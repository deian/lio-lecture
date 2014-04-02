{-# OPTIONS_GHC  -fno-warn-unused-binds -fno-warn-unused-matches 
  -fno-warn-name-shadowing -fno-warn-missing-signatures #-}
{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, 
    UndecidableInstances, FlexibleContexts, TypeSynonymInstances #-}

import Data.Set (Set)
import qualified Data.Set as Set

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

-- examples

----------------------------------------------------------------------
-- Privileges

class Label l => PrivDesc l p where
  canFlowToP :: p -> l -> l -> Bool
  canFlowToP p l1 l2 = (downgradeP p l1) `canFlowTo` l2
  downgradeP :: p -> l -> l

data SimplePriv = SimplePriv SimpleLabel

instance PrivDesc SimpleLabel SimplePriv where
  downgradeP (SimplePriv priv) lbl =
    if priv >= lbl then Public
      else lbl

-- examples

{- 
~~~
*Main> canFlowToP (SimplePriv TopSecret)
                  (SimpleLabel TopSecret)
                  (SimpleLabel Public)
True

*Main> canFlowToP (SimplePriv TopSecret)
                  (SimpleLabel Classified)
                  (SimpleLabel Public)
True

*Main> canFlowToP (SimplePriv Classified)
                  (SimpleLabel TopSecret)
                  (SimpleLabel Public)
False
~~~
-}

----------------------------------------------------------------------
-- the LIO monad

newtype LIO l a = LIO { unLIO :: l -> IO (a, l) }

instance Monad (LIO l) where
  return x = LIO $ \l -> return (x,l)

  a >>= f = LIO $ \l -> do (r,l') <- unLIO a l
                           unLIO (f r) l'
                           
{- 
initCurLabel :: LIOState MilLabel
initCurLabel = 
  LIOState { lioLabel = MilLabel Public (set [])
           , lioClearance = MilLabel TopSecret (set [Crypto, Nuclear]) }

mainLIO :: LIO MilLabel String
mainLIO = do
  lc <- label (MilLabel Classified (set [Crypto])) "w00t"
  c <- unlabel lc
  lts <- label (MilLabel TopSecret (set [Crypto, Nuclear])) $ 
            c ++ ";cbc-nuke-128"
  ts <- unlabel lts
  -- label (MilLabel TopSecret (set [Nuclear])) $ "leaking...crypto: " ++ ts
  return ts

main = do
  res <- runLIO mainLIO initCurLabel 
  print res

-}

-- simplified version of the LIO monad


-- labeled values

data Labeled l t = Labeled l t

{-
label :: Label l => l -> a -> LIO l (Labeled l a)
unlabel :: (Label l) => Labeled l a -> LIO l a
unlabelP :: Priv l p => p -> Labeled l a -> LIO l a
labelOf  :: Labeled l a -> l
-}

-- lifting IO actions into LIO — in particular, IORefs
-- examples

-- lifting concurrency primitives into LIO
-- examples

----------------------------------------------------------------------
-- the “sets of principals" label model

type Principal = String

newtype SetLabel = SetLabel (Set Principal)
                   deriving (Eq, Ord, Show)

instance Label SetLabel where
  (SetLabel s1) `canFlowTo` (SetLabel s2) = s2 `Set.isSubsetOf` s1
  (SetLabel s1) `lub` (SetLabel s2) = SetLabel $ s2 `Set.union` s1


data PrincipalPriv = PrincipalPriv Principal

instance PrivDesc SetLabel PrincipalPriv where
  downgradeP (PrincipalPriv p) (SetLabel s) = SetLabel $ Set.delete p s


-- examples (maybe variants of the examples above)

{-
topSecret  = "TopSecret" /\ "Classified" /\ "Public"
classified = "Classified" /\ "Public"
public     = "Public"
-}

----------------------------------------------------------------------
-- Integrity
-- (for the sets-of-principals model)

----------------------------------------------------------------------
-- DC labels
-- (just give examples with pure conjunction and pure disjunction)

----------------------------------------------------------------------

main = undefined
