{-# LANGUAGE TemplateHaskell #-}

module Data.ClosedWorld.TH where

import Data.ClosedWorld.Types
import Data.Proxy
import Data.Monoid
import qualified Data.Set as S

import Control.Monad
import Control.Lens
import Control.Lens.Plated
import Control.Monad.IO.Class

import Language.Haskell.TH

import Unsafe.Coerce

--instance Plated Type where
--  plate = gplate

collectVars :: Type -> S.Set Name
collectVars t = t ^. cosmos . to (\x ->
                                    case x of
                                      VarT n -> S.singleton n
                                      _ -> mempty)

mkHead :: Type -> ExpQ
mkHead (AppT f x) =
  infixE (Just $ mkHead f) [e|(-$)|] (Just $ mkHead x)
mkHead ListT = [e| list_ |]
mkHead t@(TupleT _) = appE [e| toHead |] (sigE [e| Proxy |] (appT ([t| Proxy |]) (pure t)))
mkHead (VarT n) = varE n
mkHead t@(ConT _) = appE [e| toHead |] (sigE [e| Proxy |] (appT ([t| Proxy |]) (pure t)))
mkHead _ = tupE []

introduceAll :: [Name] -> ExpQ -> ExpQ
introduceAll vars body =
  foldr (\var body -> appE [e| forall' |] $
                      lamE [sigP [p| Proxy |]
                             (appT [t| Proxy |] (varT var))]
                           body) body vars

coerceAll :: [(Name, Type)]  -> ExpQ -> ExpQ
coerceAll superclasses body =
  foldr (\(superclassDict, superclass) body ->
            caseE (sigE (appE [e| unsafeCoerce |] (varE superclassDict))
                        (appT [t| ReifiedDict |] (pure superclass)))
                  [match [p| ReifiedDict |] (normalB body) []])
        body superclasses

mkUniverse :: Q [Dec] -> Q Exp
mkUniverse mkDs =
  do ds <- mkDs
     proxy <- [e| Proxy |]
     proxyT <- [t| Proxy |]
     instanceP_ <- [e| instanceP |]
     instantiable'_ <- [e| instantiable' |]

     let ds' =  [ (foldMap collectVars h <> collectVars x, h, x)
                | (InstanceD Nothing h x _) <- ds]
         emptyInstances = [ x | (vars, _, x) <- ds', S.null vars]
         headInstances =  [ d | d@(vars, _, _) <- ds', not (S.null vars) ]

         instanceFuncs = [ AppE instanceP_
                                (SigE proxy
                                      (AppT proxyT x))
                         | x <- emptyInstances ]

     instantiable <- forM headInstances $
                     \(vars, superclasses, head_) ->
                       do superclassDictNames <- forM superclasses $ \_ -> newName "r"
                          appE (appE (appE [e| instantiable' 0 |]
                                      (lamE (map varP (S.toList vars)) (mkHead head_)))
                                (lamE (wildP:map varP (S.toList vars)) (listE (map mkHead superclasses))))
                               (lamE [listP (map (conP 'SomeReifiedDict . pure . varP) superclassDictNames)]
                                     (introduceAll (S.toList vars) $
                                      coerceAll (zip superclassDictNames superclasses) $
                                      appE [e| SomeReifiedDict |]
                                           (sigE [e| ReifiedDict |]
                                                 (appT [t| ReifiedDict |]
                                                       (pure head_)))))

--     reportWarning $ "FOund instances with head " ++ show instantiable ++ " " ++ show headInstances
--     forM_ instantiable $ \i ->
--       reportWarning (pprint i)
     pure (AppE (VarE (mkName "mconcat"))
                (ListE (instanceFuncs ++ instantiable)))

getInstances :: Name -> Q [Dec]
getInstances typ = do
  ClassI _ instances <- reify typ
  return instances

allInstances :: Name -> Q Exp
allInstances nm =
 do i <- getInstances nm
    mapM (reportWarning . pprint) i
--    [e| mempty |]
    mkUniverse (getInstances nm)
