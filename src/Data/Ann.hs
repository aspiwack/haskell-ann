{-# LANGUAGE DerivingVia #-}

module Data.Ann
  ( Ann,
    project,
    extract,
    unsafeExtract,
  )
where

import Data.Functor.Identity

newtype Ann a = Squash a
  deriving
    (Functor, Applicative, Monad)
    via Identity
  deriving
    (Semigroup, Monoid, Read, Show)
    via (Identity a)

instance Eq (Ann a) where
  _ == _ = True

instance Ord (Ann a) where
  _ <= _ = True
  compare _ _ = EQ

unsafeExtract :: Ann a -> a
unsafeExtract (Squash a) = a

extract :: Ann a -> IO a
extract = return . unsafeExtract

project :: a -> Ann a
project = Squash
