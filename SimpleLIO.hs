{-# OPTIONS_GHC  -fno-warn-unused-binds -fno-warn-unused-matches 
  -fno-warn-name-shadowing -fno-warn-missing-signatures #-}
{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, 
    UndecidableInstances, FlexibleContexts, TypeSynonymInstances,
    GeneralizedNewtypeDeriving #-}

import Control.Monad (unless)
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Class (lift)
import Data.Set (Set)
import Data.IORef
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

class Label l => Priv l p where
  downgradeP :: p -> l -> l
  canFlowToP :: p -> l -> l -> Bool
  -- default implementation of canFlowToP
  canFlowToP p l1 l2 = (downgradeP p l1) `canFlowTo` l2

data SimplePriv = SimplePrivTCB SimpleLabel

-- The "TCB" here (and below) indicates that, in a real system, this
-- constructor would not be made available to untrusted user code.

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

newtype LIO l a = LIOTCB { unLIOTCB :: StateT l IO a }
                  deriving (Functor, Monad)

-- | Run an LIO action with current label set to @l@.
runLIO :: LIO l a -> l -> IO (a, l)
runLIO lioAct l = runStateT (unLIOTCB lioAct) l

getLabel :: LIO l l
getLabel = LIOTCB . StateT $ \l -> return (l, l)

setLabelTCB :: l -> LIO l ()
setLabelTCB l = LIOTCB . StateT $ \_ -> return ((), l)

raiseLabel :: Label l => l -> LIO l ()
raiseLabel l = do 
 lcur <- getLabel
 setLabelTCB $ lcur `lub` l

guardWrite :: Label l => l -> LIO l ()
guardWrite l = do 
 lcur <- getLabel
 unless (lcur `canFlowTo` l) $ fail "write not allowed"

-- (In a real implementation, we would not raise an error that halts
-- the whole program; we would throw an exception that can be caught
-- and recovered from.)

liftIOTCB :: Label l => IO a -> LIO l a
liftIOTCB = LIOTCB . lift

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

putStrLn :: Label l => String -> LIO l ()
putStrLn s = do guardWrite public
                liftIOTCB $ IO.putStrLn s
  

-- We can already have a simple example here of running a function
-- that tries to print a string with the current label set to either
-- Public or Classified (using raiseLabel to raise the label)...

----------------------------------------------------------------------
-- LIORef

data LIORef l a = LIORefTCB l (IORef a)

newLIORef :: Label l => l -> a -> LIO l (LIORef l a)
newLIORef l x = do
  guardWrite l
  ref <- liftIOTCB $ newIORef x
  return $ LIORefTCB l ref

readLIORef (LIORefTCB l ref) = do
  raiseLabel l
  liftIOTCB $ readIORef ref

writeLIORef :: Label l => LIORef l a -> a -> LIO l ()
writeLIORef (LIORefTCB l ref) x = do
  guardWrite l
  liftIOTCB $ writeIORef ref x

-- examples showing how the current label interacts with the label in
-- an LIORef  (make a secret, read it, try to print a message)

-- lifting concurrency primitives into LIO
-- examples (like the one at the end of the lecture)

-- lifting MVars into LIO
-- more examples -- e.g., maybe a password checker

----------------------------------------------------------------------
-- Labeled values

data Labeled l t = LabeledTCB l t

-- label requires value label to be above current label
label :: Label l => l -> a -> LIO l (Labeled l a)
label l x = do
  guardWrite l
  return $ LabeledTCB l x

-- `labelOf` returns the label of a labeled value
labelOf  :: Labeled l a -> l
labelOf (LabeledTCB l x) = l

-- `unlabel` raises current label to (old current label `lub` value label)
unlabel :: (Label l) => Labeled l a -> LIO l a
unlabel (LabeledTCB l x) = do
  raiseLabel l
  return x

-- `unlabelP` uses privileges to raise label less
unlabelP :: Priv l p => p -> Labeled l a -> LIO l a
unlabelP p (LabeledTCB l x) = do
  raiseLabel (downgradeP p l)
  return x

-- Examples...

-- (simple functional-programming examples where we create a secret,
-- print something to stdout, then unlabel the secret and notice that
-- we can't print any more)

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

-- | Helper function for converting a list of principals into a label
setLabel :: [Principal] -> SetLabel
setLabel = SetLabel . Set.fromList

-- examples (maybe variants of the examples in earlier sections above)

{- Encoding the 3-point label model
topSecret  = "TopSecret" /\ "Classified" /\ "Public"
classified = "Classified" /\ "Public"
public     = "Public"
-}

----------------------------------------------------------------------
-- Integrity (presented as a pure-integrity sets-of-principals model)

-- (Maybe we want to rename the SetLabel model to something like
-- Readers so that this can have the same representation but a
-- different name and a different behavior for the operations)

----------------------------------------------------------------------
-- DC labels
-- (but just give examples with pure conjunction and pure disjunction)

----------------------------------------------------------------------

main = undefined
