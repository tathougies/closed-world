{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.ClosedWorld.Types where

import Control.Applicative
import Control.Monad.State

import Data.Typeable
import Data.Foldable
import Data.Monoid
import Data.Maybe
import qualified Data.IntMap as IM

import GHC.Types

import Unsafe.Coerce

import Debug.Trace

data ReifiedDict (c :: Constraint) where
  ReifiedDict :: c => ReifiedDict c
data SomeReifiedDict where
  SomeReifiedDict :: ReifiedDict c -> SomeReifiedDict

newtype Universe
  = Universe { lookupInstance' :: forall a. Universe -> TypeRep -> (forall c. ReifiedDict c -> a) -> Maybe a }

lookupInstance :: forall (c :: Constraint) a. Typeable c => Universe -> (c => a) -> Maybe a
lookupInstance u@(Universe lookup) f =
  lookup u (typeRep (Proxy @c)) f'
  where
    f' :: forall c'. ReifiedDict c' -> a
    f' r = case unsafeCoerce r :: ReifiedDict c of
             ReifiedDict -> f

-- | Inefficient monoidal Universe combination
instance Monoid Universe where
  mempty = Universe (\_ _ _ -> Nothing)
  mappend (Universe a) (Universe b) =
    Universe (\u t f -> a u t f <|> b u t f)

class Instantiable (a :: k) where
  instance__ :: Universe

instance (Typeable c, c) => Instantiable (c :: Constraint) where
  instance__ =  Universe fn
    where
      fn :: forall c' a. Universe -> TypeRep -> (forall c'. ReifiedDict c' -> a) -> Maybe a
      fn u req f
        | req == typeRep (Proxy @c) =
            Just (f (ReifiedDict @c))
        | otherwise = Nothing

instance_ :: forall c. (Typeable c, c) => Universe
instance_ = instance__ @Constraint @c

instanceP :: forall c. (Typeable c, c) => Proxy c -> Universe
instanceP _ = instance_ @c

mkShowListDict :: ReifiedDict (Show c) -> ReifiedDict (Show [c])
mkShowListDict ReifiedDict = ReifiedDict
mkShowMaybeDict :: ReifiedDict (Show c) -> ReifiedDict (Show (Maybe c))
mkShowMaybeDict ReifiedDict = ReifiedDict


data Head (k :: k') where
  HeadTyCon :: TyCon -> Head k
  HeadVar   :: Int   -> Head k
  HeadTyApp :: Head (a -> b) -> Head a -> Head b

deriving instance Show (Head a)

_Show :: Head (* -> Constraint)
_Show = HeadTyCon (typeRepTyCon (typeRep (Proxy @Show)))
_Foldable, _Functor :: Head ((* -> *) -> Constraint)
_Foldable = HeadTyCon (typeRepTyCon (typeRep (Proxy @Foldable)))
_Functor = HeadTyCon (typeRepTyCon (typeRep (Proxy @Functor)))

toHead :: forall (c :: k). Typeable c => Proxy c -> Head k
toHead p = HeadTyCon (typeRepTyCon (typeRep p))

list_ :: Head (* -> *)
list_ = HeadTyCon (typeRepTyCon (typeRep (Proxy @[])))
pair_ :: Head (* -> * -> *)
pair_ = HeadTyCon (typeRepTyCon (typeRep (Proxy @(,))))

ty :: forall a. Typeable a => Head *
ty = HeadTyCon (typeRepTyCon (typeRep (Proxy @a)))

(-$) :: Head (a -> b) -> Head a -> Head b
(-$) = HeadTyApp

matchHead :: Head k -> TypeRep -> Maybe (IM.IntMap TypeRep)
matchHead head_ ty = evalStateT (matchHead' head_ ty >> get) mempty
  where
    matchHead' :: forall k'. Head k' -> TypeRep -> StateT (IM.IntMap TypeRep) Maybe ()
    matchHead' (HeadTyCon con) tyRep
      | tyRep == mkTyConApp con [] = pure ()
      | otherwise = lift Nothing
    matchHead' (HeadTyApp f a) tyRep =
      do (tyCon, xs@(_:_)) <- pure $ splitTyConApp tyRep
         let asRep = init xs
             aRep = last xs
         matchHead' a aRep
         matchHead' f (mkTyConApp tyCon asRep)
    matchHead' (HeadVar x) tyRep =
      do binding <- gets (IM.lookup x)
         case binding of
           Nothing -> modify (IM.insert x tyRep)
           Just alreadyBound
             | alreadyBound == tyRep -> pure ()
             | otherwise -> lift Nothing

headToTyRep :: IM.IntMap TypeRep -> Head k -> Maybe TypeRep
headToTyRep _  (HeadTyCon ty) = Just (mkTyConApp ty [])
headToTyRep vs (HeadVar v) = IM.lookup v vs
headToTyRep vs (HeadTyApp a b) =
  do a' <- headToTyRep vs a
     b' <- headToTyRep vs b
     let (tyCon, as) = splitTyConApp a'
     pure (mkTyConApp tyCon (as ++ [b']))

tyRepToHead :: TypeRep -> Head (k :: k')
tyRepToHead r =
  case splitTyConApp r of
    (tyCon, []) -> HeadTyCon tyCon
    (tyCon, xs) ->
      let a = last xs
          as = init xs
      in unsafeCoerce $ HeadTyApp (tyRepToHead (mkTyConApp tyCon as)) (tyRepToHead a)

class InstanceForallable head mkConstraints | head -> mkConstraints where
  instantiable' :: Int -> head -> (IM.IntMap TypeRep -> mkConstraints)
                -> ([SomeReifiedDict] -> SomeReifiedDict) -> Universe
instance InstanceForallable (Head a) [Head Constraint] where
  instantiable' curVar head mkConstraints mkDict =
    Universe mkInst
    where
      mkInst :: forall a'. Universe -> TypeRep -> (forall c'. ReifiedDict c' -> a') -> Maybe a'
      mkInst u@(Universe lookup) cRep val =
        do vars <- matchHead head cRep
           guard (all (flip IM.member vars) [0..curVar - 1])

           cs <- mapM (headToTyRep vars) (mkConstraints vars)
           dicts <- mapM (\cRep -> lookup u cRep SomeReifiedDict) cs

           case mkDict dicts of
             SomeReifiedDict c ->
               Just (val c)

instance InstanceForallable head mkConstraint =>
  InstanceForallable (Head k -> head) (Head k -> mkConstraint) where
  instantiable' curVar head mkConstraints mkDict =
    instantiable' (curVar + 1) (head (HeadVar curVar)) (\v -> mkConstraints v (tyRepToHead (fromJust (IM.lookup curVar v)))) mkDict

forall_ :: (Head k -> Head a) -> (Head k -> [Head Constraint])
        -> ([SomeReifiedDict] -> SomeReifiedDict) -> Universe
forall_ f mkCs mkDict = instantiable' 0 f (\_ -> mkCs) mkDict

forall' :: (forall a. Proxy (a :: *) -> b) -> b
forall' f = f Proxy
forallK' :: forall k b. (forall (a :: k). Proxy a -> b) -> b
forallK' f = f Proxy

withHead :: forall cs a. Typeable cs => Universe -> a -> (cs => a) -> a
withHead univ onNothing onConstraint =
  fromMaybe onNothing $
  lookupInstance @cs univ onConstraint

-- | Check if type of kind * had the form 'f a'
withHead1 :: forall (cs :: (k -> *) -> Constraint) r a' a. (Typeable cs, Typeable a, Typeable a') => Proxy cs -> Universe -> a -> r -> (forall f. cs f => f a' -> r) -> r
withHead1 _ u@(Universe lookup) a onNothing onConstraint =
  fromMaybe onNothing $
  do (tyCon, tyArgs@(_:_)) <- pure $ splitTyConApp (typeRep (Proxy @a))
     let tyArgs' = init tyArgs
         a'Rep = last tyArgs
         fRep = mkTyConApp tyCon tyArgs'

         (csCon, csArgs) = splitTyConApp (typeRep (Proxy @cs))
         csfRep = mkTyConApp csCon (csArgs ++ [fRep])
     guard (a'Rep == typeRep (Proxy @a'))
     lookup u csfRep $ \(r :: ReifiedDict csf) ->
       forallK' $ \(Proxy :: Proxy (f :: k -> *)) ->
       case unsafeCoerce r :: ReifiedDict (cs (f :: k -> *)) of
         ReifiedDict -> onConstraint @f (unsafeCoerce a)

data MyDynamic where
  MyDynamic :: Typeable a => a -> MyDynamic

strList :: Universe -> [MyDynamic] -> [String]
strList u = fmap (\(MyDynamic (a :: a)) -> withHead @(Show a) u ("(no show instance found for " ++ show (typeOf a) ++ ")") $ show a)

addToList :: Universe -> [MyDynamic] -> [Int]
addToList u = concatMap (\(MyDynamic (a :: a)) -> withHead1 (Proxy @Foldable) u a [] toList)
