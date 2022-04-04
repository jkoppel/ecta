{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE  OverloadedStrings #-}
module CCTP.Utils where

-- These will be ruined by GHC 9.0+ due to the reorganization
-- These will be ruined by GHC 9.0+ due to the reorganization
import GhcPlugins hiding ((<>))
import TcRnTypes

import Application.TermSearch.Dataset
import Application.TermSearch.Type
import GhcPlugins hiding ((<>))
import Type
import Data.Text (pack, Text, unpack)
import Data.Maybe (mapMaybe, isJust, fromJust)

import Data.Map (Map)
import qualified Data.Map as Map

import GHC.IO.Unsafe
import Data.IORef
import TcRnMonad (newUnique, getTopEnv, getLocalRdrEnv, getGlobalRdrEnv)
import TcEnv (tcLookupTyCon)
import Data.Char (isAlpha)
import Data.ECTA (Node (Node), mkEdge)
import Data.ECTA.Term
import Application.TermSearch.Utils (theArrowNode, arrowType, var1, var2, var3, var4)
import Data.ECTA (union)
import Data.ECTA.Paths (getPath, mkEqConstraints, path)
import Debug.Trace (traceShow)

 -- The old "global variable" trick, as we are creating new type variables
 -- from scratch, but we want all 'a's to refer to the same variabel, etc.
tyVarMap :: IORef (Map Text TyVar)
{-# NOINLINE tyVarMap #-}
tyVarMap = unsafePerformIO (newIORef Map.empty)

skeletonToType :: TypeSkeleton -> TcM (Maybe Type)
skeletonToType (TVar t) = Just <$>
     do tm <- liftIO $ readIORef tyVarMap
        case tm Map.!? t of
            Just tv -> return $ mkTyVarTy tv
            _ -> do
                unq <- newUnique
                let nm = mkSystemName unq $ mkOccName tvName (unpack t)
                    ntv = mkTyVar nm liftedTypeKind
                liftIO $ modifyIORef tyVarMap (Map.insert t ntv)
                return $ mkTyVarTy ntv
skeletonToType (TFun arg ret) =
     do argty <- skeletonToType arg
        retty <- skeletonToType ret
        case (argty, retty) of
            (Just a, Just r) -> return (Just (mkVisFunTy a r))
            _ -> return Nothing
        -- This will be mkVisFunTyMany in 9.0+
skeletonToType (TCons con sk) =
    do args <- mapM skeletonToType sk
       let occn = mkOccName tcName (unpack con)
       lcl_env <- getLocalRdrEnv
       gbl_env <- getGlobalRdrEnv
       let conName = case lookupLocalRdrOcc lcl_env occn of
                        Just res -> Just res
                        _ -> case lookupGlobalRdrEnv gbl_env occn of
                          -- Note: does not account for shadowing
                          (GRE{..}:_) -> Just gre_name
                          _ -> Nothing
       case conName of
           Just n | all isJust args, argTys <- map fromJust args ->  do
               conTy <- tcLookupTyCon n
               return $ Just $ mkTyConApp conTy argTys
           _ -> return Nothing




-- | Extremely crude at the moment!!
-- Returns the typeSkeleton and any constructors (for instance lookup)
typeToSkeleton :: Type -> Maybe (TypeSkeleton, [Type])
typeToSkeleton ty | (vars@(_:_), r) <- splitForAllTys ty,
                    all valid vars
                    = typeToSkeleton r
  where
      valid :: TyCoVar -> Bool
      -- for now
      valid = (`elem` ["a", "b", "c", "d", "acc"]) . showSDocUnsafe . ppr
typeToSkeleton ty | isTyVarTy ty,
                       Just tt <- tyVarToSkeletonText ty = Just  (TVar tt, [])
typeToSkeleton ty | Just (arg, ret) <- splitFunTy_maybe ty,
                       Just (argsk, ac)<- typeToSkeleton arg,
                       Just (retsk, rc)<- typeToSkeleton ret =
    Just (TFun argsk retsk,ac)
typeToSkeleton ty | (cons, args@(_:_)) <- splitAppTys ty,
                       Just const <- typeToSkeletonText cons,
                       argsks <- mapMaybe typeToSkeleton args,
                       (aks, acs) <- unzip argsks =
    Just (TCons const aks, cons:concat acs)
typeToSkeleton ty | (cons, []) <- splitAppTys ty,
                       Just const <- typeToSkeletonText cons
    -- These are the ones we don't handle so far
    = Just (TCons const [], [])

-- TODO: Filter out lifted rep etc.
typeToSkeletonText :: Outputable a => a -> Maybe Text
typeToSkeletonText ty = Just $ pack $ showSDocUnsafe $ ppr ty

-- TODO: make sure it's one of the supported ones
tyVarToSkeletonText :: Outputable a => a -> Maybe Text
tyVarToSkeletonText ty = Just $ pack $ stripNumbers $ showSDocUnsafe $ ppr ty
  -- by default, the variables are given a number (e.g. a1).
  -- we just strip them off for now.
  where stripNumbers :: String -> String
        stripNumbers = takeWhile isAlpha


tk :: Node -> Int -> [Node]
tk _ 0 = []
tk anyArg 1 = [anyArg]
tk anyArg n = [union [mapp nl1 nl1,nl1]]
 where nl1 = union $ tk anyArg (n-1)

mapp :: Node -> Node -> Node
mapp n1 n2 = Node [
    mkEdge "app"
    [getPath (path [0,2]) n1, theArrowNode, n1, n2]
    (mkEqConstraints [
          [path [1], path [2, 0, 0]] -- it's a function
        , [path [3, 0], path [2, 0, 1]]
        , [path [0], path [2,0,2]]
        ]
    )]


pp (Term (Symbol t) []) = t
pp (Term (Symbol "app") (arg:rest)) =
    "(" <> wparifreq <> " " <> mconcat (map pp rest) <> ")"
  where parg = pp arg
        wparifreq = if length (words $ unpack parg) > 1
                    then "(" <> parg <> ")"
                    else parg


--   where Just (fta, ftb) = splitFunTy_maybe ty
--         tyStr = showSDocUnsafe $ ppr (fta, ftb)