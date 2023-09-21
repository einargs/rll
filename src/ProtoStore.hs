module ProtoStore (liftIO, memoize, runTask, Task) where

import Data.Text (Text)
import Data.HashMap.Strict qualified as M
import Data.Hashable (Hashable(..))
import Data.Dynamic (Dynamic, Typeable, toDyn, fromDynamic)
import Control.Monad.Reader (ReaderT, MonadReader(..), runReaderT)
import Control.Monad.IO.Class (MonadIO(..))
import Data.IORef (IORef, newIORef, readIORef, atomicModifyIORef')

newtype TaskCtx = TaskCtx
  { memoMap :: IORef (M.HashMap Int Dynamic)
  }

newtype Task a = MkTask { unTask :: ReaderT TaskCtx IO a }
  deriving newtype (Functor, Applicative, Monad, MonadReader TaskCtx, MonadIO)

runTask :: Typeable b => Task b -> IO b
runTask (MkTask m) = do
  ref <- newIORef M.empty
  let ctx = TaskCtx ref
  runReaderT m ctx

class Memoizable b where
  memoize' :: Int -> b -> b

instance Typeable b => Memoizable (Task b) where
  memoize' i calcVal = do
    ctx <- ask
    map <- liftIO $ readIORef ctx.memoMap
    case map M.!? i of
      Just dyn -> case fromDynamic dyn of
        Just val -> pure val
        Nothing -> error "wrong type somehow"
      Nothing -> do
        val <- calcVal
        liftIO $ atomicModifyIORef' ctx.memoMap $ (,()) . M.insert i (toDyn val)
        pure val

instance (Hashable a, Memoizable b) => Memoizable (a -> b) where
  memoize' i fn val = memoize' (i `hashWithSalt` val) (fn val)

memoize :: forall b. (Memoizable b) => Text -> b -> b
memoize text = memoize' $ hash text
