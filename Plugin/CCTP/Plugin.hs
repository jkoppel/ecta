{-# LANGUAGE RecordWildCards #-}
module CCTP.Plugin (plugin) where

import GhcPlugins
import TcHoleErrors
import TcHoleFitTypes
import TcRnTypes
import Constraint

import CCTP.Utils

import Application.TermSearch.Dataset
import Application.TermSearch.Type
import Application.TermSearch.TermSearch
import Data.ECTA
import Data.ECTA.Term

import qualified Data.Map as Map
import Data.Text (pack, unpack, Text)
import Data.Maybe (fromMaybe)
import Data.Tuple (swap)

plugin :: Plugin
plugin =
  defaultPlugin
    { holeFitPlugin = \_ ->
        Just $
          fromPureHFPlugin
            ( HoleFitPlugin
                { candPlugin = \_ c -> return [],
                  fitPlugin = \h _ -> ectaPlugin h
                }
            )
    }


pAnyFunc :: Node
pAnyFunc = Node (map ($ 0) hoogleComps)



invGroupMapping :: Map.Map Text Text
invGroupMapping = Map.fromList $ map swap $ Map.toList groupMapping

invSubstTerm :: Term -> Term
invSubstTerm (Term (Symbol sym) ts) =
  Term (Symbol $ fromMaybe sym (Map.lookup sym invGroupMapping)) (map invSubstTerm ts)

toPrint :: Term -> Term
toPrint (Term (Symbol s) [ta,rt]) | unpack s == "filter" = invSubstTerm rt
toPrint t = invSubstTerm t

ectaPlugin :: TypedHole -> TcM [HoleFit]
ectaPlugin TyH{..} | Just hole <- tyHCt,
                     ty <- ctPred hole = do
      case ghcTypeToSkeleton ty of
         Just t | resNode <- typeToFta t -> do
             --liftIO $ putStrLn $ "looking for type: `" ++ show t ++ "`"
             let res = getAllTerms $ refold $ reduceFully $ filterType pAnyFunc resNode
             return $ map (RawHoleFit . text . show  . toPrint) res
         _ ->  do liftIO $ putStrLn $  "Could not skeleton `" ++ showSDocUnsafe (ppr ty) ++"`"
                  return []
