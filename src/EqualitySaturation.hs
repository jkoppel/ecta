{-# LANGUAGE OverloadedStrings #-}

module EqualitySaturation (

  ) where

import           Data.List ( (\\) )
import           Data.Text ( Text )
import qualified Data.Text as Text

import Data.ECTA
import Data.ECTA.Internal.ECTA.Type ( edgeEcs )
import Data.ECTA.Paths
import Data.ECTA.Term

----------------------------------------------------


------------------------------------------------------------
---------------------- Lambda terms ------------------------
------------------------------------------------------------

------------------
------ ECTA utilities
------------------

modEcs :: (EqConstraints -> EqConstraints) -> Edge -> Edge
modEcs f e = mkEdge (edgeSymbol e) (edgeChildren e) (f $ edgeEcs e)

nodeModEcs :: (EqConstraints -> EqConstraints) -> Node -> Node
nodeModEcs f = nodeMapChildren (modEcs f)

------------------
------ Constants
------------------

maxSupportedInt :: Int
maxSupportedInt = 5

-- Set this large enough to support the highest de Bruijn index
-- appearing in a lambda term
envSize :: Int
envSize = 4

------------------
------ Node structure
------------------

----- Env structure/location

envPath :: Path
envPath = path [0]

childPath :: Int -> Path
childPath childIdx = path [childIdx + 1]

varPath :: Int -> Path
varPath varIdx = envPath <> path [varIdx]

----- Env usage

data UseVarAt = UseVarAt { varIdx :: Int, childIdx :: Int }

data At = At

useVar :: Int -> At -> Int -> UseVarAt
useVar varIdx _ childIdx = UseVarAt varIdx childIdx

copyEnvToChild :: Int -> EqConstraints
copyEnvToChild childIdx = mkEqConstraints [[envPath, childPath childIdx <> envPath]]

copyEnvToChildren :: Int -> EqConstraints
copyEnvToChildren numChildren = foldMap copyEnvToChild [0..numChildren - 1]

withCopyEnvToChildren :: Int -> Node -> Node
withCopyEnvToChildren numChildren n = nodeMapChildren (modEcs (<> copyEnvToChildren numChildren)) n

useVarFromEnv :: UseVarAt -> Edge -> Edge
useVarFromEnv uva e = modEcs (<> mkEqConstraints [[varPath (varIdx uva), childPath (childIdx uva)]]) e

nodeUseVarFromEnv :: UseVarAt -> Node -> Node
nodeUseVarFromEnv uva n = nodeMapChildren (useVarFromEnv uva) n

withEnvPropagation :: Int -> [UseVarAt] -> Node -> Node
withEnvPropagation numChildren uvas n = nodeModEcs (<> (foldMap copyEnvToChild normalChildren))
                                                   $ foldr nodeUseVarFromEnv n uvas
  where
    varChildren = map childIdx uvas
    normalChildren = [0..numChildren - 1] \\ varChildren


----- de Bruijn index operations

copyLiftedEnvToChild :: Int -> EqConstraints
copyLiftedEnvToChild childIdx = foldMap doCopyVar [1..envSize - 1]
  where
    doCopyVar :: Int -> EqConstraints
    doCopyVar targIdx = mkEqConstraints [[varPath (targIdx - 1), childPath childIdx <> varPath (targIdx)]]

------------------
------ Node types
------------------

-- | Warning: This creates a Mu node that contains a subnode. The top-down intersection algorithm
--            we use is known to have nonterminating cases for such nodes. Fingers crossed
--            such problems will not come up.
anyNode :: Node
anyNode = createGloballyUniqueMu (\n -> union (map (Node . (:[]) . constructorToEdge n) constructors))
  where
    mkAnyEnvNode :: Node -> Node
    mkAnyEnvNode n = Node [Edge "env" $ replicate envSize n]

    constructorToEdge :: Node -> (Text, Int) -> Edge
    constructorToEdge n (nm, arity) = Edge (Symbol nm) ([mkAnyEnvNode n] <> replicate arity n)

    constructors = usedConstructors <> intConstructors
    intConstructors = map (\n -> (Text.pack $ show n, 0)) [0..maxSupportedInt]
    usedConstructors = [("lambda", 1), ("apply", 2), ("+", 2)]

anyEnv :: Node
anyEnv = Node [Edge "env" $ replicate envSize anyNode]

intNode :: Int -> Node
intNode n
  | n > maxSupportedInt = error $ "intNode: int out of range " <> show n
intNode n               = Node [Edge (Symbol $ Text.pack $ show n) [anyEnv]]

plusRaw :: Node -> Node -> Node
plusRaw n1 n2 = Node [Edge "+" [anyEnv, n1, n2]]

plus :: Node -> Node -> Node
plus n1 n2 = withCopyEnvToChildren 2 (plus n1 n2)

lambda :: Node -> Node
lambda n = Node [mkEdge "lambda" [anyEnv, n] (copyLiftedEnvToChild 0)]

applyRaw :: Node -> Node -> Node
applyRaw fn arg = Node [Edge "apply" [anyEnv, fn, arg]]

apply :: Node -> Node -> Node
apply fn arg = nodeModEcs (<> copyEnvToChild 1) $ applyRaw fn arg

------------------
------ Terms of interest
------------------

plus1 :: Node
plus1 = lambda (withEnvPropagation 2 [useVar 0 At 0] $ plusRaw anyNode (intNode 1))

compose :: Node
compose = lambda $ lambda $ lambda
                          $ withEnvPropagation 2 [useVar 2 At 0] $ applyRaw anyNode
                                                                            $ withEnvPropagation 2 [useVar 1 At 0, useVar 0 At 1]
                                                                                                 $ applyRaw anyNode anyNode

------------------------------------------------------------
------------------------ Rewriting -------------------------
------------------------------------------------------------