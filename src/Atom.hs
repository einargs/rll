module Atom where

import Language.Haskell.TH (Name)
import Control.Monad.State (MonadState(..), StateT, runStateT, modify', get, put)
import Control.Monad.Trans.Class (MonadTrans)
import qualified Data.Map as M
import Data.Typeable (Typeable)
import Data.Dynamic (fromDynamic, Dynamic, toDyn)
import Data.STRef (modifySTRef')
import Control.Monad.ST.Trans.Internal (liftST)
import Control.Monad.Trans (lift)
import Control.Monad.ST.Trans (STT, runSTT, STRef, readSTRef, writeSTRef, newSTRef)

-- | Holds a name and the default value for that name.
data Atom a = Atom Name a

type AtomCtx s = M.Map Name (STRef s Dynamic)

type AtomS s m a = StateT (AtomCtx s) (STT s m) a

newtype AtomT m a = MkAtomT { unAtomT :: forall s. AtomS s m a }

unwrapDynError :: a
unwrapDynError = error "Should be impossible. No way to introduce value of bad type to an atom."

addAtom :: (Monad m, Typeable a) => Name -> a -> AtomCtx s -> AtomS s m ()
addAtom n val ctx = do
  ref <- lift $ newSTRef $ toDyn val
  put $ M.insert n ref ctx

-- | Underlying function we use to implement all the actual shit.
readAtomIn :: (Monad m, Typeable a) => Atom a -> AtomS s m a
readAtomIn (Atom n def) = do
  ctx <- get
  case ctx M.!? n of
    Nothing -> pure def
    Just ref -> lift (readSTRef ref) >>= \dyn -> case fromDynamic dyn of
      Nothing -> unwrapDynError
      Just v -> pure v

writeAtomIn :: (Monad m, Typeable a) => Atom a -> a -> AtomS s m ()
writeAtomIn (Atom n _) val = do
  ctx <- get
  case ctx M.!? n of
    Nothing -> addAtom n val ctx
    Just ref -> lift $ writeSTRef ref $ toDyn val

modifyAtomIn' :: (Monad m, Typeable a) => Atom a -> (a -> a) -> AtomS s m ()
modifyAtomIn' (Atom n def) f = do
  ctx <- get
  case ctx M.!? n of
    Nothing -> addAtom n (f def) ctx
    Just ref -> lift $ liftST $ modifySTRef' ref g
  where g dyn = toDyn $ case fromDynamic dyn of
          Nothing -> unwrapDynError
          Just v -> f v

-- |
withAtomIn :: (Monad m, Typeable a) => Atom a -> a -> AtomS s m a -> AtomS s m a
withAtomIn (Atom n _) val act = do
  ctx <- get
  addAtom n val ctx
  out <- act
  put ctx
  pure out

-- withAtom
-- modifyAtom'
