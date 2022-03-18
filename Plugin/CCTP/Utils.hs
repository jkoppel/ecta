{-# LANGUAGE RecordWildCards #-}
module CCTP.Utils where

-- These will be ruined by GHC 9.0+ due to the reorganization
import GhcPlugins
import TcRnTypes

import Application.TermSearch.Dataset
import Application.TermSearch.Type
import GhcPlugins
import Type
import Data.Text (pack, Text, unpack)
import Data.Maybe (mapMaybe, isJust, fromJust)

import Data.Map (Map)
import qualified Data.Map as Map

import GHC.IO.Unsafe
import Data.IORef
import TcRnMonad (newUnique, getTopEnv, getLocalRdrEnv, getGlobalRdrEnv)
import TcEnv (tcLookupTyCon)

tyVarMap :: IORef (Map Text TyVar)
{-# NOINLINE tyVarMap #-}
tyVarMap = unsafePerformIO (newIORef Map.empty) -- The old "global variable" trick

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
typeToSkeleton :: Type -> Maybe TypeSkeleton
typeToSkeleton ty | isTyVarTy ty,
                       Just tt <- tyVarToSkeletonText ty = Just $ TVar tt
typeToSkeleton ty | Just (arg, ret) <- splitFunTy_maybe ty,
                       Just argsk <- typeToSkeleton arg,
                       Just retsk <- typeToSkeleton ret =
    Just $ TFun argsk retsk
typeToSkeleton ty | (cons, args) <- splitAppTys ty,
                       Just const <- typeToSkeletonText cons,
                       argsks <- mapMaybe typeToSkeleton args =
    Just $ TCons const argsks

-- TODO: Filter out lifted rep etc.
typeToSkeletonText :: Outputable a => a -> Maybe Text
typeToSkeletonText ty = Just $ pack $ showSDocUnsafe $ ppr ty

-- TODO: make sure it's one of the supported ones
tyVarToSkeletonText :: Outputable a => a -> Maybe Text
tyVarToSkeletonText ty = Just $ pack $ showSDocUnsafe $ ppr ty



--   where Just (fta, ftb) = splitFunTy_maybe ty
--         tyStr = showSDocUnsafe $ ppr (fta, ftb)