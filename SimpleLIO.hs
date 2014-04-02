{-# OPTIONS_GHC  -fno-warn-unused-binds -fno-warn-unused-matches 
  -fno-warn-name-shadowing -fno-warn-missing-signatures #-}
{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, 
    UndecidableInstances, FlexibleContexts, TypeSynonymInstances #-}

----------------------------------------------------------------------
-- Labels

class (Eq l, Show l) => Label l where
    -- Relation that dictates how information flows
    canFlowTo :: l -> l -> Bool
    lub :: l -> l -> l -- Least upper bound

data SimpleLabel = Public | Classified | TopSecret 
                   deriving (Eq, Ord, Show)

instance Label SimpleLabel where
  x `canFlowTo` y = x <= y
  lub = max

----------------------------------------------------------------------
-- Privileges

class Label l => PrivDesc l p where
  canFlowToP :: p -> l -> l -> Bool
  downgradeP :: p -> l -> l

data SimplePriv = SimplePriv SimpleLabel

instance PrivDesc SimpleLabel SimplePriv where
  canFlowToP p l1 l2 = (downgradeP p l1) `canFlowTo` l2
  downgradeP (SimplePriv priv) lbl =
    if priv >= lbl then Public
      else lbl

-- canFlowToP
-- examples

----------------------------------------------------------------------
-- the “sets of principals" label model

----------------------------------------------------------------------
-- the LIO monad

-- simplified version of the LIO monad (with no IORef! :-) and no clearance)

-- lifting IO actions into LIO — in particular, IORefs
-- examples

-- lifting concurrency primitives into LIO
-- examples

----------------------------------------------------------------------
-- Integrity
-- (for the sets-of-principals model)

----------------------------------------------------------------------
-- DC labels
-- (just give examples with pure conjunction and pure disjunction)

----------------------------------------------------------------------

main = undefined
