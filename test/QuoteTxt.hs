{-# LANGUAGE TemplateHaskell, QuasiQuotes #-}
module QuoteTxt (txt) where

import Data.Text (pack)
import qualified Language.Haskell.TH.Syntax as S
import qualified Language.Haskell.TH.Quote as Q

txt :: Q.QuasiQuoter
txt = Q.QuasiQuoter f fail fail fail where
  f str = do
    p <- [|pack|]
    pure $ S.AppE p $ S.LitE $ S.StringL str
