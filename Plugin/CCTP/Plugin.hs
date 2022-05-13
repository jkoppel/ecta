{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}
module CCTP.Plugin (plugin) where

import GhcPlugins hiding ((<>))
import TcHoleErrors
import TcHoleFitTypes
import TcRnTypes
import Constraint

import CCTP.Utils

import Application.TermSearch.Dataset
import Application.TermSearch.Type
import Application.TermSearch.TermSearch hiding (allConstructors, generalize)
import Data.ECTA
import Data.ECTA.Term

import qualified Data.Map as Map
import Data.Text (pack, unpack, Text)
import Data.Maybe (fromMaybe, mapMaybe, isJust, fromJust)
import Data.Tuple (swap)
import Data.List (sortOn, groupBy, nub, nubBy, (\\))
import Data.Function (on)
import qualified Data.Monoid as M
import MonadUtils (concatMapM)
import TcRnMonad (writeTcRef, newTcRef, readTcRef, mapMaybeM, getTopEnv)
import TcEnv (tcLookupId, tcLookupIdMaybe, tcLookup)
import qualified Data.Bifunctor as Bi
import TcRnDriver (tcRnGetInfo)
import GHC (ClsInst)
import InstEnv (ClsInst(ClsInst, is_tvs, is_cls_nm, is_tys), is_dfun)
import Language.Dot.Pretty (renderDot)
import ConLike (ConLike(RealDataCon))
import Data.ECTA.Paths (Path, mkEqConstraints)
import Application.TermSearch.Utils
import Data.Containers.ListUtils (nubOrd)
import Debug.Trace
import Data.Either (partitionEithers)


plugin :: Plugin
plugin =
  defaultPlugin
    { holeFitPlugin = \opts ->
        Just $
          HoleFitPluginR {
            hfPluginInit = newTcRef [],
            hfPluginRun = \ref ->
                  ( HoleFitPlugin
                   { candPlugin = \_ c -> writeTcRef ref c >> return [],
                     fitPlugin = \h _ -> readTcRef ref >>= ectaPlugin opts h
                                  }
                              ),
            hfPluginStop = const (return ())
          }
    }


pAnyFunc :: Node
pAnyFunc = Node (map ($ 1) hoogleComps)

candsToComps :: [HoleFitCandidate] -> TcM [((Either Text Text, TypeSkeleton), [Type])]
candsToComps = mapMaybeM (fmap (fmap extract) . candToTN)
  where candToTN :: HoleFitCandidate -> TcM (Maybe (Either Text Text, (TypeSkeleton, [Type])))
        candToTN cand = fmap (fmap (nm,) . (>>= typeToSkeleton)) (c2t cand)
          where nm = (case cand of
                      IdHFCand _ -> Left
                      _ -> Right) $ pack $ occNameString $ occName cand
                c2t cand =
                  case cand of
                    IdHFCand id -> return $ Just $ idType id
                    NameHFCand nm -> tcTyThingTypeMaybe <$> tcLookup nm
                    GreHFCand GRE{..} -> tcTyThingTypeMaybe  <$> tcLookup gre_name
        extract (a, (b,c)) = ((a,b), c)
        tcTyThingTypeMaybe :: TcTyThing -> Maybe Type
        tcTyThingTypeMaybe (ATcId tttid _) = Just $ idType tttid
        tcTyThingTypeMaybe (AGlobal (AnId ttid)) =Just $ idType ttid
        tcTyThingTypeMaybe (AGlobal (ATyCon ttid)) | t <- mkTyConApp ttid [],
                                                    (tcReturnsConstraintKind . tcTypeKind) t
                                                    = Just t
        tcTyThingTypeMaybe (AGlobal (AConLike (RealDataCon con))) = Just $ idType $ dataConWorkId con
        tcTyThingTypeMaybe _ =  Nothing


instToTerm :: ClsInst -> Maybe (Text, TypeSkeleton)
instToTerm ClsInst{..} | -- length is_tvs <= 1, -- uncomment if you want explosion!
                        Just (tyskel,args) <- typeToSkeleton $ idType is_dfun
                        = Just (toDictStr $ clsstr <> tystr, tyskel )
  where clsstr =  pack $  showSDocUnsafe $ ppr is_cls_nm
        tystr = pack $ showSDocUnsafe $ ppr is_tys
instToTerm _ = Nothing

toDictStr :: Text -> Text
toDictStr t = spToUnderscore $ "<@" <> t <> "@>"

spToUnderscore :: Text -> Text
spToUnderscore = pack . sp . unpack
  where sp (' ':str) = '_':sp str
        sp (s:str) = s:sp str
        sp [] = []

ectaPlugin :: [CommandLineOption] -> TypedHole -> [HoleFitCandidate] -> TcM [HoleFit]
ectaPlugin opts TyH{..} scope  | Just hole <- tyHCt,
                                 ty <- ctPred hole = do
      (fun_comps, scons) <- fmap (nubBy eqType . concat) . unzip <$> candsToComps scope
      let (local_comps, global_comps) = partitionEithers $ map to_e fun_comps
          to_e (Left t,ts) = Left (t,ts)
          to_e (Right t, ts) = Right (t,ts)
      -- The constraints are there and added to the graph... but we have to
      -- be more precise when we add them to the machine. Any time a
      -- function requires a constraint to hold for one of it's variables,
      -- we have to add a path equality to the ECTA.
      let constraints = filter (tcReturnsConstraintKind . tcTypeKind) scons
      let givens = concatMap (map idType . ic_given) tyHImplics
          g2c g = fmap (toDictStr (pack $ showSDocUnsafe $ ppr g),)
                      $ fmap fst $ typeToSkeleton g
          given_comps = mapMaybe g2c givens
      hsc_env <- getTopEnv
      instance_comps <- mapMaybe instToTerm . concat <$>
                             mapMaybeM (fmap (fmap (\(_,_,c,_,_) -> c) . snd)
                                       . liftIO  . tcRnGetInfo hsc_env . getName
                                       . tyConAppTyCon) constraints
      let local_scope_comps = local_comps ++ given_comps
          global_scope_comps = global_comps ++ instance_comps
          scope_comps = local_scope_comps ++ global_scope_comps
      let (scopeNode, anyArg, argNodes, skels, groups) =
            let argNodes = ngnodes local_scope_comps
                addSyms st tt = map (Bi.bimap (Symbol . st) (tt . typeToFta))
                gnodes = addSyms id (generalize global_scope_comps)
                ngnodes = addSyms id id
                anyArg = Node $ map (\(s,t) -> Edge s [t]) $ 
                        (gnodes global_scope_comps) ++ argNodes
                scopeNode = anyArg
                skels = Map.fromList $ scope_comps
                groups = Map.fromList $ map (\(t,_) -> (t,[t])) scope_comps
            in (scopeNode, anyArg, argNodes, skels, groups)
      case typeToSkeleton ty of
         Just (t, cons) | resNode <- typeToFta t -> do
             let res = getAllTerms $ refold $ reduceFully $ filterType scopeNode resNode
             ppterms <- concatMapM (prettyMatch skels groups . prettyTerm ) res
             let even_more_terms =
                  map (pp . prettyTerm) $
                    concatMap (getAllTerms . refold . reduceFully . flip filterType resNode )
                              (rtkUpToKAtLeast1 argNodes scope_comps anyArg True 7)
             return $ map (RawHoleFit . text . unpack) $ ppterms  ++ even_more_terms
         _ ->  do liftIO $ putStrLn $  "Could not skeleton `" ++ showSDocUnsafe (ppr ty) ++"`"
                  return []


-- TODO:
-- 1. I think we need to add type applications, i.e. [] @a or similar, let's see.
