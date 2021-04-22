-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE QuantifiedConstraints #-}

module Name (Name, RawName (..), Tag, Env (..), envLookup,
             BinderP (..), BinderListP (..), getRawSourceName, fromRawSourceName,
             SourceNS, SourceName, pattern SourceBinder, pattern SourceName,
             Ext (..), (@>), (<.>), (<>>),
             withFresh, binderAnn, EnvFrag, (@@>),
             extendScope, emptyEnvFrag, Scope, AlphaEq (..),
             EmptyNest, NameSet, HasNames (..), BindsNames (..),
             liftNames, lowerNames, envAsScope,
             binderName, Abs (..), Nest (..), toNest, getRawName,
             NameHint, binderListBinders, withTempScope,
             freeNames, fmapNames, foldMapNames,
             unitScope, unitName, voidScope, voidEnv) where

import Control.Monad.Identity
import Control.Monad.Writer.Strict
import qualified Data.Map.Strict as M
import qualified Data.Set        as S
import Data.String
import qualified Data.Text as T
import Unsafe.Coerce

import HigherKinded

type Tag = T.Text
data RawName = RawName Tag Int
               deriving (Show, Eq, Ord)

data Name n = UnsafeMakeName RawName
              deriving (Show, Eq, Ord)

data BinderP (ann :: * -> *) (n :: *) (l :: *) where
   UnsafeMakeBinder :: RawName -> ann n -> BinderP ann n l
   Ignore           :: ann n -> BinderP ann n n

instance (Show (ann n), Show n, Show l) => Show (BinderP ann n l)

data Ext n l = UnsafeMakeExt

-- `Env i a` is isomorphic to `Name i -> a`, but it can be extended with new
-- names efficiently.
data Env i a where
  Env :: Scope i -> EnvFrag n i a -> (Name n -> a) -> Env i a

-- `EnvFrag i' i a` is isomorphic to `Name i' -> (Either i a)`, but it can be
-- composed efficiently.
data EnvFrag i i' a = UnsafeMakeEnvFrag (M.Map RawName a)

data Scope n = UnsafeMakeScope (S.Set RawName)

emptyEnvFrag :: EnvFrag n n a
emptyEnvFrag = UnsafeMakeEnvFrag mempty

extendScope :: Scope n -> EnvFrag n n' a -> Scope n'
extendScope (UnsafeMakeScope scope) (UnsafeMakeEnvFrag frag) =
  UnsafeMakeScope $ scope <> M.keysSet frag

infixr 7 @>

(@>) :: BinderP ann i i' -> a -> EnvFrag i i' a
(@>) b x = case b of
  Ignore _ -> emptyEnvFrag
  UnsafeMakeBinder name _ -> UnsafeMakeEnvFrag $ M.singleton name x

infixl 5 <>>
(<>>) :: Env n a -> EnvFrag n n' a -> Env n' a
(<>>) (Env scope ef f) ef' = Env (extendScope scope ef') (ef <.> ef') f

infixl 3 <.>
(<.>) :: EnvFrag n n' a -> EnvFrag n' n'' a -> EnvFrag n n'' a
(<.>) (UnsafeMakeEnvFrag m1) (UnsafeMakeEnvFrag m2) = UnsafeMakeEnvFrag $ m2 <> m1

withFresh :: ann n -> Scope n
          -> (forall l. Ext n l -> BinderP ann n l -> Name l -> a) -> a
withFresh ann (UnsafeMakeScope scope) cont =
  cont UnsafeMakeExt (UnsafeMakeBinder freshName ann) (UnsafeMakeName freshName)
  where freshName = freshRawName "v" scope

freshRawName :: Tag -> S.Set RawName -> RawName
freshRawName tag usedNames = RawName tag nextNum
  where
    nextNum = case S.lookupLT (RawName tag bigInt) usedNames of
                Just (RawName tag' i)
                  | tag' /= tag -> 0
                  | i < bigInt  -> i + 1
                  | otherwise   -> error "Ran out of numbers!"
                Nothing -> 0
    bigInt = (10::Int) ^ (9::Int)  -- TODO: consider a real sentinel value

binderAnn :: BinderP ann n l -> ann n
binderAnn (Ignore ann) = ann
binderAnn (UnsafeMakeBinder _ ann) = ann

binderName :: BinderP ann n l -> Maybe (Name l)
binderName (Ignore _) = Nothing
binderName (UnsafeMakeBinder name _) = Just $ UnsafeMakeName name

envFragLookup :: EnvFrag n l a -> Name l -> Either (Name n) a
envFragLookup (UnsafeMakeEnvFrag m) (UnsafeMakeName name) =
  case M.lookup name m of
    Just x -> Right x
    Nothing -> Left $ UnsafeMakeName name

_liftName :: Ext n l -> Name n -> Name l
_liftName _ = unsafeCoerceNames

-- useful for printing etc
getRawName :: Name n -> RawName
getRawName (UnsafeMakeName name) = name

-- slightly safer than raw `unsafeCoerce` because it requires `HasNames`
unsafeCoerceNames :: HasNames e => e i -> e o
unsafeCoerceNames = unsafeCoerce

-- === free variable traversal ===

data MonadicEnv m i a where
  MonadicEnv :: EnvFrag n i a -> (Name n -> m a) -> MonadicEnv m i a

-- XXX: In addition to the methods, a `HasNames` instance is also used as a
-- proof that the `n` parameter is truly phantom, so that it doesn't affect the
-- runtime representation and can be cast arbitrarily by `unsafeCastNames`.
-- It should therefore satisfy:
--   traverseFreeNames scope (pure . liftName ext) x = unsafeCoerceNames x
--   (see implementation of `liftNames :: HasNames e => Ext n l -> e n -> e l`)
class HasNames (e :: * -> *) where
  traverseFreeNames
    :: Monad m
    => Scope o
    -> MonadicEnv m i (Name o)
    -> e i
    -> m (e o)

class BindsNames (b :: * -> * -> *) where
  traverseFreeNamesBinders
    :: Monad m
    => Scope o
    -> MonadicEnv m i (Name o)
    -> b i i'
    -> (forall o'. Scope o' -> MonadicEnv m i' (Name o') -> b o o' -> m a)
    -> m a

class HasNames e => AlphaEq (e :: * -> *) where
  alphaEq :: Scope n -> e n -> e n -> Bool

liftNames :: HasNames e => Ext n l -> e n -> e l
-- This is the reference implementation. `unsafeCoerce` is an optimization, and
-- should behave the same, up to alpha renaming.
--   liftNames _ x = fmapFreeNames scope (pure . liftName ext) x
liftNames _ x = unsafeCoerceNames x

-- Makes a temporary scope by querying the free variables of an expression. We
-- should try to avoid using this, since we normally have the actual scope
-- available and we can avoid the work of traversing the expression.
withTempScope :: HasNames e => e n
              -> (forall l. Ext l n -> Scope l -> e l -> a) -> a
withTempScope e cont =
  let freeRawNames = foldMapNames (S.singleton . getRawName) e
  in cont UnsafeMakeExt (UnsafeMakeScope freeRawNames) (unsafeCoerceNames e)

-- === convenience utilities using safe API ===

infixr 7 @@>

(@@>) :: Nest (BinderP ann) i i' -> [a] -> EnvFrag i i' a
(@@>) Empty [] = emptyEnvFrag
(@@>) (Nest b rest) (x:xs) = b@>x <.> (rest@@>xs)
(@@>) _ _ = error "length mismatch"

data Abs (binder :: * -> * -> *) (body :: * -> *) (n :: *) where
  Abs :: binder n l -> body l -> Abs binder body n

data Nest (binder :: * -> * -> * ) (n :: *) (l :: *) where
 Nest  :: binder n h -> Nest binder h i -> Nest binder n i
 Empty ::                                  Nest binder n n

envLookup :: Env i a -> Name i -> a
envLookup (Env _ frag f) name = case envFragLookup frag name of
  Left name' -> f name'
  Right x -> x

type EmptyNest (binder :: * -> * -> *) = Abs (Nest binder) UnitH :: * -> *

instance Show (Abs ann body n)
instance Show (Nest ann result n)

type NameHint = RawName

data BinderListP ann n l = BinderListP (Nest (BinderP UnitH) n l) [ann n]

binderListBinders :: BinderListP ann n l -> Nest (BinderP UnitH) n l
binderListBinders (BinderListP bs _) = bs

type NameSet n = S.Set (Name n)

asMonadicEnv :: (Name n -> m a) -> MonadicEnv m n a
asMonadicEnv f = MonadicEnv emptyEnvFrag f

lowerName :: EnvFrag n l a -> Name l -> Maybe (Name n)
lowerName ef name = case envFragLookup ef name of
   Left name' -> Just name'
   Right _ -> Nothing

-- TODO: use `Except` instead of `Maybe` to provide a more informative error
lowerNames :: HasNames e => Scope n -> EnvFrag n l a -> e l -> Maybe (e n)
lowerNames scope frag expr = traverseFreeNames scope (asMonadicEnv (lowerName frag)) expr

fmapNames :: HasNames e => Scope b -> (Name a -> Name b) -> e a -> e b
fmapNames scope f xs =
  runIdentity $ traverseFreeNames scope (asMonadicEnv (pure . f)) xs

foldMapNames :: (HasNames e, Monoid a) => (Name n -> a) -> e n -> a
foldMapNames f e = execWriter $ flip (traverseFreeNames unitScope) e $
  asMonadicEnv \name -> do
    tell (f name)
    return unitName

freeNames :: HasNames e => e n -> NameSet n
freeNames e = foldMapNames S.singleton e

envAsScope :: Env n a -> Scope n
envAsScope (Env scope _ _) = scope

-- === special name spaces ===

-- Used for source names, which don't obey any invariants
data SourceNS where
type RawSourceName = Tag

type SourceName = Name SourceNS

pattern SourceBinder :: Name SourceNS -> ann SourceNS -> BinderP ann SourceNS SourceNS
pattern SourceBinder name ann <- ((\(UnsafeMakeBinder name ann) -> (SourceName name, ann)) -> (name, ann))
  where SourceBinder (UnsafeMakeName name) ann = UnsafeMakeBinder name ann

pattern SourceName :: RawName -> Name SourceNS
pattern SourceName name = UnsafeMakeName name

getRawSourceName :: Name SourceNS -> RawSourceName
getRawSourceName (UnsafeMakeName (RawName name 0)) = name
getRawSourceName (UnsafeMakeName (RawName _ _)) =
  error "nonzero counter for a source name shouldn't happen"

fromRawSourceName :: RawSourceName -> Name SourceNS
fromRawSourceName name = UnsafeMakeName (RawName name 0)

toNest :: [b SourceNS SourceNS] -> Nest b SourceNS SourceNS
toNest [] = Empty
toNest (b:bs) = Nest b $ toNest bs

-- Name space with no inhabitants
data VoidNS where

voidScope :: Scope VoidNS
voidScope = UnsafeMakeScope mempty

voidEnv :: Env VoidNS a
voidEnv = Env voidScope emptyEnvFrag \_ ->
  error "Values of type `Name VoidNS` shouldn't exist!"

-- Name space with one inhabitant
data UnitNS where

unitName :: Name UnitNS
unitName = UnsafeMakeName "TheOneName"

unitScope :: Scope UnitNS
unitScope = UnsafeMakeScope $ S.singleton (getRawName unitName)

-- === instances ===

instance HasNames Name where
  traverseFreeNames _ = monadicEnvLookup

instance (BindsNames b, HasNames e) => HasNames (Abs b e) where
  traverseFreeNames scope env (Abs b body) =
    traverseFreeNamesBinders scope env b \scope' env' b' ->
      Abs b' <$> traverseFreeNames scope' env' body

instance HasNames ann => BindsNames (BinderP ann) where
  traverseFreeNamesBinders scope env b cont = case b of
    Ignore ann -> do
      ann' <- traverseFreeNames scope env ann
      cont scope env (Ignore ann')
    UnsafeMakeBinder _ ann -> do
      ann' <- traverseFreeNames scope env ann
      withFresh ann' scope \ext b' name' -> do
        let scope' = extendScope scope (b'@>())
        let env' = flip extendMonadicEnv (b@>name') $ liftMonadicEnv ext env
        cont scope' env' b'

instance BindsNames b => BindsNames (Nest b) where
  traverseFreeNamesBinders scope env nest cont = case nest of
    Empty -> cont scope env Empty
    Nest b rest -> do
      traverseFreeNamesBinders scope env b \scope' env' b' ->
        traverseFreeNamesBinders scope' env' rest \scope'' env'' rest' ->
          cont scope'' env'' $ Nest b' rest'

monadicEnvLookup :: Monad m => MonadicEnv m i a -> Name i -> m a
monadicEnvLookup (MonadicEnv frag f) name =
  case envFragLookup frag name of
    Left name' -> f name'
    Right x -> return x

extendMonadicEnv :: MonadicEnv m i a -> EnvFrag i i' a -> MonadicEnv m i' a
extendMonadicEnv (MonadicEnv ef f) ef' = MonadicEnv (ef <.> ef') f

liftMonadicEnv :: Ext n l -> MonadicEnv m i (Name n) -> MonadicEnv m i (Name l)
liftMonadicEnv = unsafeCoerce

instance (HasNames e1, HasNames e2) => HasNames (PairH e1 e2) where
  traverseFreeNames scope env (PairH x y) =
    PairH <$> traverseFreeNames scope env x <*> traverseFreeNames scope env y

instance (Traversable f, HasNames e) => HasNames (H f e)

instance IsString RawName where
  fromString s = RawName (fromString s) 0
