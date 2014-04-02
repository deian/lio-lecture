{-# OPTIONS_GHC  -fno-warn-unused-binds -fno-warn-unused-matches 
  -fno-warn-name-shadowing -fno-warn-missing-signatures #-}
{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, 
    UndecidableInstances, FlexibleContexts, TypeSynonymInstances,
    GeneralizedNewtypeDeriving #-}

import Prelude hiding (putStrLn, getLine)
import Control.Monad (unless, void)
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Class (lift)
import Control.Concurrent (forkIO)
import Control.Concurrent.MVar
import Data.Monoid
import Data.Set (Set)
import qualified Data.Set as Set
import Data.IORef
import qualified System.IO as IO

----------------------------------------------------------------------
-- Labels

class (Eq l, Show l) => Label l where
    -- | Relation that dictates how information flows
    canFlowTo :: l -> l -> Bool
    -- | Least upper bound
    lub       :: l -> l -> l

data SimpleLabel = Public | Classified | TopSecret 
                   deriving (Eq, Ord, Show)

instance Label SimpleLabel where
  x `canFlowTo` y = x <= y
  lub = max

-- examples

simpleExample0 = runSimpleExample $ return
  [ canFlowTo Public TopSecret
  , canFlowTo Classified Classified 
  , canFlowTo Classified TopSecret 
  , canFlowTo TopSecret Public
  , canFlowTo Classified Public
  , canFlowTo TopSecret Classified ]

-- [True,True,True,False,False,False]

----------------------------------------------------------------------
-- Privileges

class (Label l, Monoid p) => Priv l p where
  -- | Dowgrade the label as much as possible (to the bottom element)
  -- using the supplied privileges
  downgradeP :: p -> l -> l
  -- | Relation that dictates how information flows, taking privileges
  -- into consideration
  canFlowToP :: p -> l -> l -> Bool
  -- | Default implementation of canFlowToP
  canFlowToP p l1 l2 = (downgradeP p l1) `canFlowTo` l2

-- Above, note that privileges @p@ are expected to be monoid. This is
-- because it's useful to have a notion the empty privivilege and how
-- to combine privileges.

-- A simple privilege just wraps a label. For the SimpleLabel model
-- this corresponds to a classification: if you have the TopSecret
-- privilege you can declassify any kind of data, with Classified
-- privilege you can declassify only data at your level; with Public
-- privilege you cannot declassify anything.

data SimplePriv = SimplePrivTCB SimpleLabel

instance Monoid SimplePriv where
  mempty = SimplePrivTCB $ Public
  (SimplePrivTCB p1) `mappend` (SimplePrivTCB p2) = SimplePrivTCB $ p1 `lub` p2


-- The "TCB" here (and below) indicates that, in a real system, this
-- constructor would not be made available to untrusted user code.

instance Priv SimpleLabel SimplePriv where
  downgradeP (SimplePrivTCB priv) lbl =
    if priv >= lbl then Public
      else lbl

-- examples

simpleExample1 = runSimpleExample $ return
  [ canFlowToP (SimplePrivTCB TopSecret ) TopSecret  Public
  , canFlowToP (SimplePrivTCB TopSecret ) Classified Public
  , canFlowToP (SimplePrivTCB Classified) Classified Public
  , canFlowToP (SimplePrivTCB Classified) TopSecret  Public ]

-- [True,True,True,False]


----------------------------------------------------------------------
-- No privs

-- Below we're going to define the LIO monad. Since certain actions
-- require privileges to be permisive we define a privilege type
-- 'NoPriv' corresponding to the empty privilege, regardless of the
-- label type.
--

data NoPriv = NoPriv

instance Monoid NoPriv where
  mempty       = NoPriv
  mappend  _ _ = NoPriv

instance Label l => Priv l NoPriv where
  downgradeP _ l = l

----------------------------------------------------------------------
-- the LIO monad


-- | The LIO monad is a state monad wrapping the IO monad
newtype LIO l a = LIOTCB { unLIOTCB :: StateT l IO a }
                  deriving (Functor, Monad)

-- | Execute an LIO action with initial current label set to @l@.
runLIO :: LIO l a -> l -> IO (a, l)
runLIO lioAct l = runStateT (unLIOTCB lioAct) l

-- With this, we can now give the definition for the runSimpleExample
-- wrapper we used above:

runExample :: (Show a, PublicAction l) => LIO l a -> IO ()
runExample act = do
  (a, l) <- runLIO act publicLabel
  IO.putStrLn $ show a
  IO.putStrLn  $ "=> " ++ show l ++ " <="

runSimpleExample :: (Show a) => LIO SimpleLabel a -> IO ()
runSimpleExample = runExample

-- In general, it is useful to figure out what the current label of
-- the computation is; we're going to use this when we check where an
-- LIO computation can write.

getLabel :: LIO l l
getLabel = LIOTCB . StateT $ \l -> return (l, l)

-- Similarly, we want to modify the current labe. Different form
-- getLabel, setLabelP only sets the current label to the supplied
-- label if it is above it, taking the supplied privileges into
-- consideration.

setLabelP :: Priv l p => p -> l -> LIO l ()
setLabelP priv l = do
 lcur <- getLabel
 unless (canFlowToP priv lcur l) $ fail "insufficient privs"
 LIOTCB . StateT $ \_ -> return ((), l)

-- While setLabelP can be used to lower the current label, privileges
-- prmitting, we usually want to raise the current label to allow
-- reading more sensitive data.

raiseLabelP :: Priv l p => p -> l -> LIO l ()
raiseLabelP p l = do 
 lcur <- getLabel
 setLabelP NoPriv $ lcur `lub` (downgradeP p l)

raiseLabel :: Label l => l -> LIO l ()
raiseLabel = raiseLabelP NoPriv

-- We call 'raiseLabel l' before reading any data at level 'l', this
-- ensures that the current label always protects whatever is in
-- scope. Similarly, we want to make sure that whenever we write any
-- data that the data from the current context is not leaked. To this
-- end we use guardWrite:

guardWriteP :: Priv l p => p -> l -> LIO l ()
guardWriteP p l = do 
 lcur <- getLabel
 unless (canFlowToP p lcur l) $ fail "write not allowed"

guardWrite :: Label l => l -> LIO l ()
guardWrite = guardWriteP NoPriv

-- We call 'guardWrite l' before we write to an object labeled 'l'.
-- (In a real implementation, we would not raise an error that halts
-- the whole program; we would throw an exception that can be caught
-- and recovered from.)

-- To actually perform some effects, we want to just use the existing
-- IO library (as opposed to implementing them in a purely funtional
-- way atop LIO).

liftIOTCB :: Label l => IO a -> LIO l a
liftIOTCB = LIOTCB . lift

-- As a first example of an IO function, let's lift putStrLn. While we
-- can defined it as
--
--    putStrLn s = do guardWrite Public
--                    liftIOTCB $ IO.putStrLn s
--
-- this would not let us use putStrLn with other lbel models. So,
-- let's define a set of public LIO actions

class Label l => PublicAction l where

  -- We consider these channels as public so let's assume the
  -- existence of a puclid label.
  publicLabel :: l

  putStrLnP :: Priv l p => p -> String -> LIO l ()
  -- Default implementation
  putStrLnP p s = do guardWriteP p publicLabel
                     liftIOTCB $ IO.putStrLn s

  putStrLn :: String -> LIO l ()
  -- Default implementation
  putStrLn = putStrLnP NoPriv

  getLine :: LIO l String
  getLine = do raiseLabelP NoPriv publicLabel
               liftIOTCB $ IO.getLine
  
instance PublicAction SimpleLabel where publicLabel = Public

simpleExample2 = runSimpleExample $ putStrLn "Hello LIO world!"
-- hey!
-- ()
-- => Public <=


simpleExample3 = runSimpleExample $ do
  putStrLn "Hello LIO world!"
  raiseLabel TopSecret
  putStrLn "Edward in the house..."

-- Hello LIO world!
-- *** Exception: user error (write not allowed)

simpleExample4 = runSimpleExample $ do
  putStrLn "Hello LIO world!"
  raiseLabel TopSecret
  setLabelP (SimplePrivTCB TopSecret) Public
  putStrLn "Edward got privs..."
-- Hello LIO world!
-- Edward got privs...

simpleExample5 = runSimpleExample $ do
  let privs = SimplePrivTCB Classified
  putStrLn "Hello LIO world!"
  raiseLabel Classified
  setLabelP privs Public
  putStrLn "Bradley has some privs too..."
  raiseLabel TopSecret
  setLabelP privs Public
  putStrLn "But not as many as Edward..."
-- Hello LIO world!
-- Bradley has some privs too...
-- *** Exception: user error (insufficient privs)

----------------------------------------------------------------------
-- LIORef

data LIORef l a = LIORefTCB l (IORef a)

newLIORef :: Label l => l -> a -> LIO l (LIORef l a)
newLIORef l x = do
  guardWrite l
  ref <- liftIOTCB $ newIORef x
  return $ LIORefTCB l ref

readLIORef :: Label l => LIORef l a -> LIO l a
readLIORef (LIORefTCB l ref) = do
  raiseLabel l
  liftIOTCB $ readIORef ref

writeLIORef :: Label l => LIORef l a -> a -> LIO l ()
writeLIORef (LIORefTCB l ref) x = do
  guardWrite l
  liftIOTCB $ writeIORef ref x

simpleExample6 = runSimpleExample $ do
  alice <- newLIORef TopSecret Nothing
  -- as alice:
  do putStrLn "<alice<"
     secret <- getLine
     writeLIORef alice $ Just secret
  -- as the messenger:
  msg <- readLIORef alice
  putStrLn $ "Intercepted message: " ++ show msg
-- <alice<
-- Wouldn't you like to know.
-- *** Exception: user error (write not allowed)

simpleExample7 = runSimpleExample $ do
  alice <- newLIORef TopSecret Nothing
  bob <- newLIORef TopSecret Nothing
  -- as alice:
  do putStrLn "<alice<"
     secret <- getLine
     writeLIORef alice $ Just secret
  -- as the messenger:
  msg <- readLIORef alice
  writeLIORef bob $ msg
  -- as bob:
  do mmsg <- readLIORef alice
     case mmsg of
       Just msg -> do lcur <- getLabel
                      setLabelP (SimplePrivTCB TopSecret) Public
                      putStrLn $ ">bob> " ++ msg
                      raiseLabel lcur
       _ -> return ()
  -- as the messenger:
  putStrLn $ "Intercepted message: " ++ show msg
-- <alice<
-- Woudln't you like to know.
-- >bob> Woudln't you like to know
-- *** Exception: user error (write not allowed)


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
--
-- DS: maybe just modify the ref examples to use 
-- getLine' :: Label l => l -> LIO l (Labeled l String)

----------------------------------------------------------------------
-- lifting concurrency primitives into LIO

forkLIO :: Label l => LIO l () -> LIO l ()
forkLIO lioAct = do
  l <- getLabel
  void . liftIOTCB . forkIO $ void $ runLIO lioAct l


data LMVar l a = LMVarTCB l (MVar a)

newLMVarP :: Priv l p => p -> l -> a -> LIO l (LMVar l a)
newLMVarP p l x = do
  guardWriteP p l
  mvar <- liftIOTCB $ newMVar x
  return $ LMVarTCB l mvar

newEmptyLMVarP :: Priv l p => p -> l -> LIO l (LMVar l a)
newEmptyLMVarP p l = do
  guardWriteP p l
  mvar <- liftIOTCB $ newEmptyMVar
  return $ LMVarTCB l mvar

takeLMVarP :: Priv l p => p -> LMVar l a -> LIO l a
takeLMVarP p (LMVarTCB l mvar) = do
  raiseLabelP p l
  guardWriteP p l
  liftIOTCB $ takeMVar mvar

putLMVarP :: Priv l p => p -> LMVar l a -> a -> LIO l ()
putLMVarP p (LMVarTCB l mvar) x = do
  raiseLabelP p l
  guardWriteP p l
  liftIOTCB $ putMVar mvar x

-- examples (like the one at the end of the lecture)
-- lifting MVars into LIO
-- more examples -- e.g., maybe a password checker

simpleExample8 = runSimpleExample $ do
  alice <- newEmptyLMVarP NoPriv TopSecret
  bob <- newEmptyLMVarP NoPriv TopSecret
  -- as alice:
  forkLIO $ do putStrLn "<alice<"
               secret <- getLine
               putLMVarP NoPriv alice secret
  -- as bob:
  forkLIO $ do msg <- takeLMVarP (SimplePrivTCB TopSecret) alice
               putStrLn $ ">bob> " ++ msg
               putLMVarP NoPriv bob ""
  -- as the messenger:
  msg <- takeLMVarP NoPriv bob
  putStrLn $ "Intercepted message: " ++ show msg
-- *Main> simpleExample8
-- <alice<
-- hey
-- >bob> hey
-- *** Exception: user error (write not allowed)

----------------------------------------------------------------------
----------------------------------------------------------------------
-- the “sets of principals" label model

type Principal = String

-- SetLabel econdes a label model representing the set of principals
-- to whom data labeled as such is sensitive.
newtype SetLabel = SetLabel (Set Principal)
                   deriving (Eq, Ord, Show)

fromList :: [Principal] -> SetLabel
fromList = SetLabel . Set.fromList


instance Label SetLabel where
  -- Information can from one entitty to another only if the data
  -- becomes more secret, i.e., there are more principals to whom this
  -- data is sensitive.
  (SetLabel s1) `canFlowTo` (SetLabel s2) = s1 `Set.isSubsetOf` s2

  -- Combining data from two entities means that we have to preserve
  -- the privacy of the principals from both sets.
  (SetLabel s1) `lub` (SetLabel s2) = SetLabel $ s2 `Set.union` s2


-- | A set privilege means that we can "speak on behalf of" the
-- principals in the set, i.e., we can declassify the data of these
-- principals.
data SetPriv = SetPrivTCB SetLabel

-- Here we wrapped SetLabel as opposed to 'Set Principal' for
-- simplicity.

instance Monoid SetPriv where
  -- The empty privilege means we're not speaking on behalf of anybody
  mempty = SetPrivTCB . SetLabel $ Set.empty

  -- The combination of set privilege amounts to simply cominging the
  -- underlying set of principals
  (SetPrivTCB p1) `mappend` (SetPrivTCB p2) = SetPrivTCB $ p1 `lub` p2


-- When we downgrade a label we simply remove the privilege principals
-- from the label; by exercising this privilege, these principals are
-- saying that they no longer consider the data private.

instance Priv SetLabel SetPriv where
  downgradeP (SetPrivTCB (SetLabel p)) (SetLabel s) = SetLabel $ s Set.\\ p

instance PublicAction SetLabel where publicLabel = fromList []

runSetExample :: (Show a) => LIO SetLabel a -> IO ()
runSetExample = runExample

-- examples (maybe variants of the examples in earlier sections above)

{- Encoding the 3-point label model
topSecret  = "TopSecret" /\ "Classified" /\ "Public"
classified = "Classified" /\ "Public"
public     = "Public"
-}



setExample8 = runSetExample $ do
  secretVar <- newEmptyLMVarP NoPriv alice
  forkLIO $ do
    raiseLabel alice
    putLMVarP NoPriv secretVar "Please do not share"

  forkLIO $ do
    raiseLabel bob
    putStrLnP bobPriv "I'll wait for a message from Alice"
    secret <- takeLMVarP bobPriv secretVar
    putStrLnP bobPriv secret -- This will fail!
  where alice =  fromList ["alice"]
        bob   =  fromList ["bob"]
        bobPriv = SetPrivTCB bob



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


--- 
--- OLD STUFF
--- 

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
