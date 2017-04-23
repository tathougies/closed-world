{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Various instances from the 'base' package
module Data.ClosedWorld.Base where

import Data.ClosedWorld.Types
import Data.ClosedWorld.TH

import Data.Int
import Data.Word

showInstances :: Universe
showInstances =
  $(mkUniverse
    [d| instance Show Int
        instance Show Int8
        instance Show Int16
        instance Show Int32
        instance Show Int64
        instance Show Char

        instance Show Word
        instance Show Word8
        instance Show Word16
        instance Show Word32
        instance Show Word64

        instance Show Double
        instance Show Float

        instance Show a => Show [a]

        instance Show ()
        instance (Show a, Show b) => Show (a, b)
        instance (Show a, Show b, Show c) => Show (a, b, c)
        instance (Show a, Show b, Show c, Show d) => Show (a, b, c, d)
        instance (Show a, Show b, Show c, Show d, Show e) => Show (a, b, c, d, e) |])

foldableInstances :: Universe
foldableInstances =
  $(mkUniverse
     [d| instance Foldable []
         instance Foldable ((,) a)
         instance Foldable Maybe
         instance Foldable (Either a) |])
