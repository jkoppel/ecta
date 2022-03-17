module CCTP.Utils where


import GhcPlugins
import Application.TermSearch.Dataset
import Application.TermSearch.Type
import GhcPlugins
import Type
import Data.Text (pack)
import Data.Maybe (mapMaybe)

-- | Extremely crude at the moment!!
ghcTypeToSkeleton :: Type -> Maybe TypeSkeleton
ghcTypeToSkeleton ty | isTyVarTy ty,
                       Just tt <- ghcTyVarToSkeletonText ty = Just $ TVar tt
ghcTypeToSkeleton ty | Just (arg, ret) <- splitFunTy_maybe ty,
                       Just argsk <- ghcTypeToSkeleton arg,
                       Just retsk <- ghcTypeToSkeleton ret =
    Just $ TFun argsk retsk
ghcTypeToSkeleton ty | (cons, args) <- splitAppTys ty,
                       Just const <- ghcTypeToSkeletonText cons,
                       argsks <- mapMaybe ghcTypeToSkeleton args =
    Just $ TCons const argsks

-- TODO: Filter out lifted rep etc.
ghcTypeToSkeletonText ty = Just $ pack $ showSDocUnsafe $ ppr ty

-- TODO: make sure it's one of the supported ones
ghcTyVarToSkeletonText ty = Just $ pack $ showSDocUnsafe $ ppr ty



--   where Just (fta, ftb) = splitFunTy_maybe ty
--         tyStr = showSDocUnsafe $ ppr (fta, ftb)