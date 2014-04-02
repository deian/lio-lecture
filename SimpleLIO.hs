{-# OPTIONS_GHC  -fno-warn-unused-binds -fno-warn-unused-matches 
  -fno-warn-name-shadowing -fno-warn-missing-signatures #-}
{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, 
    UndecidableInstances, FlexibleContexts, TypeSynonymInstances #-}

import Data.Set (Set)
import qualified Data.Set as Set
import qualified System.IO as IO

----------------------------------------------------------------------
-- Labels

-- BCP: Maybe it's not nice to have "public" here.  In general, I'd
-- argue it's a good extension, but perhaps extending LIO is not a
-- good idea here because then the students will expect to see things
-- in LIO that are not there.  Best if our SimpleLIO is a strict
-- subset.  But then I need some advice what's the best way to deal
-- with putStrLn below...

class (Eq l, Show l) => Label l where
    -- Relation that dictates how information flows
    canFlowTo :: l -> l -> Bool
    lub :: l -> l -> l -- Least upper bound
    public :: l -- the default label

data SimpleLabel = Public | Classified | TopSecret 
                   deriving (Eq, Ord, Show)

instance Label SimpleLabel where
  x `canFlowTo` y = x <= y
  lub = max
  public = Public

-- examples

----------------------------------------------------------------------
-- Privileges

-- BCP: Do we really need the distinction between privileges and
-- privilege descriptions??

class Label l => Priv l p where
  downgradeP :: p -> l -> l
  canFlowToP :: p -> l -> l -> Bool
  -- default implementation of canFlowToP
  canFlowToP p l1 l2 = (downgradeP p l1) `canFlowTo` l2

data SimplePriv = SimplePrivTCB SimpleLabel

instance Priv SimpleLabel SimplePriv where
  downgradeP (SimplePrivTCB priv) lbl =
    if priv >= lbl then Public
      else lbl

-- examples

{- 
~~~
*Main> canFlowToP (SimplePrivTCB TopSecret)
                  (SimpleLabel TopSecret)
                  (SimpleLabel Public)
True

*Main> canFlowToP (SimplePrivTCB TopSecret)
                  (SimpleLabel Classified)
                  (SimpleLabel Public)
True

*Main> canFlowToP (SimplePrivTCB Classified)
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

-- The next two functions are intended only for use by the internals
-- of the LIO library.  In a real implementation we'd use modules to
-- control their visibility.  For today, we'll just be careful where
-- we use them.
guardIO :: Label l => l -> l -> LIO l ()
guardIO lmin lmax = 
  LIO $ \l -> if lmin `canFlowTo` l && l `canFlowTo` lmax 
              then return ((),l) 
              else error "foo"

liftIO :: Label l => IO a -> LIO l a
liftIO a = LIO $ \l -> do r <- a
                          return (r,l)

-- Now we use these functions to carefully lift certain operations
-- from IO to LIO, equipping the raw IO operations with appropriate
-- information-flow policies...

putStrLn :: Label l => String -> LIO l ()
putStrLn s = do guardIO public public
                liftIO $ IO.putStrLn s
  
getLabel :: Label l => LIO l l
getLabel = LIO $ \l -> return (l,l)

-- labeled values

data Labeled l t = LabeledTCB l t

-- `label` requires value label to be above current label
label :: Label l => l -> a -> LIO l (Labeled l a)
label l x = LIO $ \l -> return (LabeledTCB l x, l)

-- `labelOf` returns the label of a labeled value
labelOf  :: Labeled l a -> l
labelOf (LabeledTCB l x) = l

-- `unlabel` raises current label to (old current label `lub` value label)
unlabel :: (Label l) => Labeled l a -> LIO l a
unlabel (LabeledTCB l' x) = LIO $ \l -> return (x, l `lub` l')

-- `unlabelP` uses privileges to raise label less
unlabelP :: Priv l p => p -> Labeled l a -> LIO l a
unlabelP p (LabeledTCB l' x) = LIO $ \l -> return (x, l `lub` downgradeP p l')

-- Examples...

-- (simple functional-programming examples where we create a secret,
-- print something to stdout, then unlabel the secret and notice that
-- we can't print any more)

----------------------------------------------------------------------

-- lifting IORefs into LIO

-- examples showing how the current label interacts with the label in
-- an LIORef

-- lifting concurrency primitives into LIO
-- examples (like the one at the end of the lecture)

-- lifting MVars into LIO
-- more examples -- e.g., maybe a password checker

----------------------------------------------------------------------
----------------------------------------------------------------------
-- the “sets of principals" label model

type Principal = String

newtype SetLabel = SetLabel (Set Principal)
                   deriving (Eq, Ord, Show)

instance Label SetLabel where
  (SetLabel s1) `canFlowTo` (SetLabel s2) = s2 `Set.isSubsetOf` s1
  (SetLabel s1) `lub` (SetLabel s2) = SetLabel $ s2 `Set.union` s1
  public = SetLabel Set.empty

data PrincipalPriv = PrincipalPrivTCB Principal

instance Priv SetLabel PrincipalPriv where
  downgradeP (PrincipalPrivTCB p) (SetLabel s) = SetLabel $ Set.delete p s


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
