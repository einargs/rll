{-# LANGUAGE TemplateHaskell, QuasiQuotes #-}
module QuoteTxt (txt, currentFilePath) where

import Data.Text (pack)
import Language.Haskell.TH
import qualified Language.Haskell.TH.Syntax as S
import qualified Language.Haskell.TH.Quote as Q

txt :: Q.QuasiQuoter
txt = Q.QuasiQuoter f fail fail fail where
  f str = do
    p <- [|pack|]
    pure $ S.AppE p $ S.LitE $ S.StringL str


currentFilePath :: Q Exp
currentFilePath = do
  Loc{loc_filename} <- location
  stringE loc_filename
