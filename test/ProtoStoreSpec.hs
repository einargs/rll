module ProtoStoreSpec where

import ProtoStore
import Test.Hspec

testMemo :: String -> Task Int
testMemo = memoize "testMemo" \str -> do
  liftIO $ putStrLn str
  pure $ length str

spec :: Spec
spec = do
  describe "prototype store" do
    it "can memoize adding stuff" do
      runTask do
        _ <- testMemo "hello"
        _ <- testMemo "hello"
        pure ()
