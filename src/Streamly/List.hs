{-# LANGUAGE CPP                        #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE UndecidableInstances       #-} -- XXX
{-# LANGUAGE ViewPatterns               #-}

-- |
-- Module      : Streamly.List
-- Copyright   : (c) 2018 Composewell Technologies
--
-- License     : BSD3
-- Maintainer  : harendra.kumar@gmail.com
-- Stability   : experimental
-- Portability : GHC
--
-- Lists are just a special case of monadic streams. The stream type @SerialT
-- Identity a@ can be used as a replacement for @[a]@.  The 'List' type in this
-- module is just a newtype wrapper around @SerialT Identity@ for better type
-- inference when using the 'OverloadedLists' GHC extension. @List a@ provides
-- better performance compared to @[a]@. Standard list, string and list
-- comprehension syntax can be used with the 'List' type by enabling
-- 'OverloadedLists', 'OverloadedStrings' and 'MonadComprehensions' GHC
-- extensions.  If you want to replace streamly lists with standard lists, all
-- you need to do is import these definitions:
--
-- @
-- type List = []
-- pattern Nil <- [] where Nil = []
-- pattern Cons x xs = x : xs
-- infixr 5 `Cons`
-- {-\# COMPLETE Cons, Nil #-}
-- @
--
-- Other than that there would be a slight difference in the 'Show' and
-- 'Read' strings.
--
-- Since 'List' is a @newtype@ wrapper on a serial stream, it can be converted
-- to stream types using 'coerce' without incurring any cost.  Functions
-- working on stream types can be coerced to work on the 'List' type. However,
-- for convenience, this module provides combinators that work directly on the
-- 'List' type.
--
--
-- @
-- coerce $ S.map (+ 1) (1 \`Cons\` Nil)
-- @
--
-- 'Data.Foldable.toList' from 'Foldable' and 'GHC.Exts.toList' and
-- 'GHC.Exts.fromList' from 'IsList' can also be used to convert to and from
-- standard lists.
--
-- See <src/docs/streamly-vs-lists.md> for more details and
-- <src/test/PureStreams.hs> for comprehensive usage examples.
--
module Streamly.List
    (
#if __GLASGOW_HASKELL__ >= 800
    List (.., Nil, Cons)
#else
    List (..)
    , pattern Nil
    , pattern Cons
#endif
    , ZipList (..)
    , fromZipList
    , toZipList
    )
where

import Control.Arrow (second)
import Control.DeepSeq (NFData(..), NFData1(..))
import Data.Coerce (coerce)
import Data.Functor.Identity (Identity, runIdentity)
import Data.Semigroup (Semigroup(..))
import GHC.Exts (IsList(..), IsString(..))

import Streamly.Streams.Serial (SerialT(..))
import Streamly.Streams.Zip (ZipSerialM(..))

import qualified Streamly.Streams.Prelude as P
import qualified Streamly.Streams.StreamK as K

-- We implement list as a newtype instead of a type synonym to make type
-- inference easier when using -XOverloadedLists and -XOverloadedStrings. When
-- using a stream type the programmer needs to specify the Monad otherwise the
-- type remains ambiguous.
--
-- | @List a@ is a replacement for @[a]@.
--
-- @since 0.5.3
newtype List a = List (SerialT Identity a)
    deriving (Show, Read, Eq, Ord, NFData, NFData1
             , Semigroup, Monoid, Functor, Foldable
             , Applicative, Traversable, Monad)

instance (a ~ Char) => IsString (List a) where
    {-# INLINE fromString #-}
    fromString = List . P.fromList

toSerial :: List a -> SerialT Identity a
toSerial = coerce

-- GHC versions 8.0 and below cannot derive IsList
instance IsList (List a) where
    type (Item (List a)) = a
    {-# INLINE fromList #-}
    fromList = List . P.fromList
    {-# INLINE toList #-}
    toList = runIdentity .  P.toList . toSerial

------------------------------------------------------------------------------
-- Patterns
------------------------------------------------------------------------------

-- | An empty list constructor and pattern that matches an empty 'List'.
-- Corresponds to '[]' for Haskell lists.
--
-- @since 0.5.3
pattern Nil :: forall a. List a
pattern Nil <- (runIdentity . K.null . (id :: SerialT Identity a -> SerialT Identity a) . coerce -> True) where
    Nil = List K.nil

infixr 5 `Cons`

-- | A list constructor and pattern that deconstructs a 'List' into its head
-- and tail. Corresponds to ':' for Haskell lists.
--
-- @since 0.5.3
pattern Cons :: a -> List a -> List a
pattern Cons x xs <-
    (fmap (second List) . runIdentity . K.uncons . coerce
        -> Just (x, xs)) where
            Cons x xs = List $ K.cons x (coerce xs)

#if __GLASGOW_HASKELL__ >= 802
{-# COMPLETE Nil, Cons #-}
#endif

------------------------------------------------------------------------------
-- ZipList
------------------------------------------------------------------------------

-- | Just like 'List' except that it has a zipping 'Applicative' instance
-- and no 'Monad' instance.
--
-- @since 0.5.3
newtype ZipList a = ZipList (ZipSerialM Identity a)
    deriving (Show, Read, Eq, Ord, NFData, NFData1
             , Semigroup, Monoid, Functor, Foldable
             , Applicative, Traversable)

instance (a ~ Char) => IsString (ZipList a) where
    {-# INLINE fromString #-}
    fromString = ZipList . P.fromList

toZipSerial :: ZipList a -> ZipSerialM Identity a
toZipSerial = coerce

-- GHC versions 8.0 and below cannot derive IsList
instance IsList (ZipList a) where
    type (Item (ZipList a)) = a
    {-# INLINE fromList #-}
    fromList = ZipList . P.fromList
    {-# INLINE toList #-}
    toList = runIdentity . P.toList . toZipSerial

-- | Convert a 'ZipList' to a regular 'List'
--
-- @since 0.5.3
fromZipList :: ZipList a -> List a
fromZipList = coerce

-- | Convert a regular 'List' to a 'ZipList'
--
-- @since 0.5.3
toZipList :: List a -> ZipList a
toZipList = coerce
