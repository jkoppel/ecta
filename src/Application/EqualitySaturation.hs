{-# LANGUAGE OverloadedStrings #-}

module Application.EqualitySaturation (
    At (..)
  , UseVarAt (..)
  , useVar
  , maxSupportedInt
  , nodeModEcs
  , modEcs
  , varPath
  , copyEnvToChild
  , copyEnvToChildren
  , copyLiftedEnvToChild
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

varPath :: Path -> Int -> Path
varPath ep varIdx = ep <> path [varIdx]

----- Env usage

data UseVarAt = UseVarAt { varIdx :: Int, childIdx :: Int }

data At = At

useVar :: Int -> At -> Int -> UseVarAt
useVar varIdx _ childIdx = UseVarAt varIdx childIdx

copyEnvToChild :: Path -> Int -> EqConstraints
copyEnvToChild ep childIdx = mkEqConstraints [[ep, childPath childIdx <> ep]]

copyEnvToChildren :: Path -> Int -> EqConstraints
copyEnvToChildren ep numChildren = foldMap (copyEnvToChild ep) [0..numChildren - 1]

withCopyEnvToChildren :: Path -> Int -> Node -> Node
withCopyEnvToChildren ep numChildren n = nodeMapChildren (modEcs (<> copyEnvToChildren ep numChildren)) n

useVarFromEnv :: Path -> UseVarAt -> Edge -> Edge
useVarFromEnv ep uva e = modEcs (<> mkEqConstraints [[varPath ep (varIdx uva), childPath (childIdx uva)]]) e

nodeUseVarFromEnv :: Path -> UseVarAt -> Node -> Node
nodeUseVarFromEnv ep uva n = nodeMapChildren (useVarFromEnv ep uva) n

withEnvPropagation :: Path -> Int -> [UseVarAt] -> Node -> Node
withEnvPropagation ep numChildren uvas n = nodeModEcs (<> (foldMap (copyEnvToChild ep) normalChildren))
                                                      $ foldr (nodeUseVarFromEnv ep) n uvas
  where
    varChildren = map childIdx uvas
    normalChildren = [0..numChildren - 1] \\ varChildren


----- de Bruijn index operations

copyLiftedEnvToChild :: Path -> Int -> Int -> EqConstraints
copyLiftedEnvToChild ep sz childIdx = foldMap doCopyVar [1..sz - 1]
  where
    doCopyVar :: Int -> EqConstraints
    doCopyVar targIdx = mkEqConstraints [[varPath ep (targIdx - 1), childPath childIdx <> varPath ep targIdx]]

------------------
------ Node types
------------------

-- | Warning: This creates a Mu node that contains a subnode. The top-down intersection algorithm
--            we use is known to have nonterminating cases for such nodes. Fingers crossed
--            such problems will not come up.
anyNode :: Node
anyNode = createMu (\n -> union (map (Node . (:[]) . constructorToEdge n) constructors))
  where
    mkAnyEnvNode :: Node -> Node
    mkAnyEnvNode n = Node [Edge "env" $ replicate envSize n]

    constructorToEdge :: Node -> (Text, Int) -> Edge
    constructorToEdge n (nm, arity) = Edge (Symbol nm) ([mkAnyEnvNode n] <> replicate arity n)

    constructors = usedConstructors <> intConstructors
    intConstructors = map (\n -> (Text.pack $ show n, 0)) [0..maxSupportedInt]
    usedConstructors = [("lambda", 1), ("apply", 2), ("+", 2)]

anyEnv :: Node -> Node
anyEnv tau = Node [Edge "env" $ replicate envSize tau]

intNode :: Int -> Node
intNode n
  | n > maxSupportedInt = error $ "intNode: int out of range " <> show n
intNode n               = Node [Edge (Symbol $ Text.pack $ show n) [anyEnv anyNode]]

plusRaw :: Node -> Node -> Node
plusRaw n1 n2 = Node [Edge "+" [anyEnv anyNode, n1, n2]]

plus :: Path -> Node -> Node -> Node
plus ep n1 n2 = withCopyEnvToChildren ep 2 (plus ep n1 n2)

lambda :: Path -> Node -> Node
lambda ep n = Node [mkEdge "lambda" [anyEnv anyNode, n] (copyLiftedEnvToChild ep envSize 0)]

applyRaw :: Node -> Node -> Node
applyRaw fn arg = Node [Edge "apply" [anyEnv anyNode, fn, arg]]

apply :: Path -> Node -> Node -> Node
apply ep fn arg = nodeModEcs (<> copyEnvToChild ep 1) $ applyRaw fn arg

------------------
------ Terms of interest
------------------

plus1 :: Node
plus1 = lambda envPath (withEnvPropagation envPath 2 [useVar 0 At 0] $ plusRaw anyNode (intNode 1))

compose :: Node
compose = lambda envPath 
                 $ lambda envPath 
                          $ lambda envPath
                                   $ withEnvPropagation envPath 2 [useVar 2 At 0] $ applyRaw anyNode
                                                                                             $ withEnvPropagation envPath 2 [useVar 1 At 0, useVar 0 At 1]
                                                                                                                  $ applyRaw anyNode anyNode

------------------------------------------------------------
------------------------ Rewriting -------------------------
------------------------------------------------------------