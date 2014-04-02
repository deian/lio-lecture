-- A Simplified Presentation of LIO
-- By Benjamin Pierce and Deian Stefan

{-# OPTIONS_GHC -fno-warn-unused-binds -fno-warn-unused-matches 
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
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
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

simpleExample0 = 
  [ Public     `canFlowTo` TopSecret
  , Classified `canFlowTo` Classified 
  , Classified `canFlowTo` TopSecret 
  , TopSecret  `canFlowTo` Public
  , Classified `canFlowTo` Public
  , TopSecret  `canFlowTo` Classified ]
-- [True,True,True,False,False,False]

----------------------------------------------------------------------
-- Privileges

class (Label l, Show p) => Priv l p where
  -- | Dowgrade the label as much as possible (to the bottom element)
  -- using the supplied privileges
  downgradeP :: p -> l -> l
  -- | Relation that dictates how information flows, taking privileges
  -- into consideration
  canFlowToP :: p -> l -> l -> Bool
  -- | Default implementation of canFlowToP
  canFlowToP p l1 l2 = (downgradeP p l1) `canFlowTo` l2

-- A simple privilege just wraps a label. For the SimpleLabel model
-- this corresponds to a classification: if you have the TopSecret
-- privilege you can declassify any kind of data, with Classified
-- privilege you can declassify only data at your level; with Public
-- privilege you cannot declassify anything.

data SimplePriv = SimplePrivTCB SimpleLabel
  deriving Show

-- The "TCB" here (and below) indicates that, in a real system, this
-- constructor would not be made available to untrusted user code.

instance Priv SimpleLabel SimplePriv where
  downgradeP (SimplePrivTCB priv) lbl =
    if priv >= lbl then Public
      else lbl

simpleExample1 = 
  [ canFlowToP (SimplePrivTCB TopSecret ) TopSecret  Public
  , canFlowToP (SimplePrivTCB TopSecret ) Classified Public
  , canFlowToP (SimplePrivTCB Classified) Classified Public
  , canFlowToP (SimplePrivTCB Classified) TopSecret  Public ]
-- [True,True,True,False]


-- For some of the definitions accompanying the LIO monad below, it
-- will be useful to have a type of "null privileges" that can be used
-- to define unprivileged versions of privileged operations.  'NoPriv'
-- corresponding to an empty privilege, regardless of the label type.

-- BCP: It might be simpler just to define the no-privilege operations
-- directly, below, rather than taking the trouble to define NoPriv
-- (there are only a few).

data NoPriv = NoPriv
  deriving Show

instance Label l => Priv l NoPriv where
  downgradeP _ l = l

simpleExample1a = 
  [ canFlowToP NoPriv Public    TopSecret
  , canFlowToP NoPriv TopSecret Public
  , canFlowToP NoPriv TopSecret Classified ]
-- [True,False,False]

----------------------------------------------------------------------
-- The LIO monad

-- | The LIO monad is a state monad wrapping the IO monad and carrying
-- a single label as the "current state"
newtype LIO l a = LIOTCB { unLIOTCB :: StateT l IO a }
                  deriving (Functor, Monad)

-- | Execute an LIO action with initial "current label" set to l.
runLIO :: LIO l a -> l -> IO (a, l)
runLIO lioAct l = runStateT (unLIOTCB lioAct) l

-- It's convenient to define a wrapper that executes an LIO action and
-- displays its final result and final label

runExample :: (Show a, PublicAction l) => LIO l a -> IO ()
runExample act = do
  IO.hSetBuffering IO.stdout IO.LineBuffering
  (a, l) <- runLIO act publicLabel
  IO.putStrLn $ show a
  IO.putStrLn  $ "=> " ++ show l ++ " <="

runSimpleExample :: (Show a) => LIO SimpleLabel a -> IO ()
runSimpleExample = runExample

-- It's often useful to find out what the current label of the
-- computation is; we're going to use this repeatedly to check where
-- an LIO computation can write.  It's also sometimes useful in
-- user-level code.

getLabel :: LIO l l
getLabel = LIOTCB . StateT $ \l -> return (l, l)

-- We will also need to modify the current label. Unlike getLabel,
-- setLabelP only sets the current label to the supplied label if the
-- latter is above the former (taking the supplied privileges into
-- consideration).

setLabelP :: Priv l p => p -> l -> LIO l ()
setLabelP priv l = do
 lcur <- getLabel
 unless (canFlowToP priv lcur l) $ fail "insufficient privs"
 LIOTCB . StateT $ \_ -> return ((), l)

-- (In a real implementation, we would not raise an error that halts
-- the whole program; we would throw an exception that can be caught
-- and recovered from.)

-- While setLabelP can be used to lower the current label (privileges
-- permitting), the most common case is raising the current label to
-- allow reading more sensitive data.

raiseLabelP :: Priv l p => p -> l -> LIO l ()
raiseLabelP p l = do 
 lcur <- getLabel
 setLabelP NoPriv $ lcur `lub` (downgradeP p l)

raiseLabel :: Label l => l -> LIO l ()
raiseLabel = raiseLabelP NoPriv

-- We call 'raiseLabel l' before reading any data at level 'l', this
-- ensures that the current label always protects whatever is in
-- scope. Similarly, we want to make sure that whenever we write any
-- data that the data from the current context is not leaked. For this
-- we use guardWrite:

guardWriteP :: Priv l p => p -> l -> LIO l ()
guardWriteP p l = do 
 lcur <- getLabel
 unless (canFlowToP p lcur l) $ 
   fail ("write from " ++ (show lcur) ++ 
         " to " ++ (show l) ++ 
         " not allowed with privilege " ++ (show p))

guardWrite :: Label l => l -> LIO l ()
guardWrite = guardWriteP NoPriv

-- We will always call 'guardWrite l' before we write to an object
-- labeled 'l'.

-- To actually perform some effects, we just lift actions from the
-- existing IO library

liftIOTCB :: Label l => IO a -> LIO l a
liftIOTCB = LIOTCB . lift

-- As a first example, let's lift putStrLn into LIO. While we could
-- defined it as
--
--    putStrLn s = do guardWrite Public
--                    liftIOTCB $ IO.putStrLn s
--
-- this would not let us use putStrLn with the other label models that
-- we are going to define later. So, let's define a typeclass of
-- public LIO actions...

class Label l => PublicAction l where
  -- We consider channels like the standard output as public so we
  -- assume the existence of a public label.
  publicLabel :: l

  putStrLnP :: Priv l p => p -> String -> LIO l ()
  -- Default implementation
  putStrLnP p s = do guardWriteP p publicLabel
                     liftIOTCB $ IO.putStrLn s

  putStrLn :: String -> LIO l ()
  -- Default implementation
  putStrLn = putStrLnP NoPriv

  getLine :: LIO l String
  -- Default implementation
  getLine = do raiseLabelP NoPriv publicLabel
               liftIOTCB $ IO.getLine
  
-- (Note that all the operations except publicLabel have default
-- definitions.  That is, once we supply the value for the public
-- label, we get all the other ones for free.)

instance PublicAction SimpleLabel where publicLabel = Public

simpleExample2 = runSimpleExample $ putStrLn "Hello LIO world!"
-- Hello LIO world!
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

-- Besides reading and writing public external channels, we want to be
-- able to store data internally in mutable structures like databases.
-- A simple structure that illustrates the issues is a single
-- reference cell.

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
  aliceSecret <- newLIORef TopSecret ""
  -- as alice:
  do putStrLn "<alice<"
     secret <- getLine
     writeLIORef aliceSecret secret
  -- as the messenger:
  msg <- readLIORef aliceSecret
  putStrLn $ "Intercepted message: " ++ show msg
-- <alice<
-- Wouldn't you like to know.
-- *** Exception: user error (write not allowed)

-- (In the above example, the "as alice" and "as messenger" actions
-- are actually all running in the same thread.  More realistically,
-- they would actually be running in separate threads, all
-- communicating with the same database of persistent values.  We'll
-- see how to express this in just a minute.)

simpleExample7 = runSimpleExample $ do
  aliceSecret <- newLIORef TopSecret ""
  bobSecret <- newLIORef TopSecret ""
  -- as alice:
  do putStrLn "<alice<"
     secret <- getLine
     writeLIORef aliceSecret secret
  -- as the messenger:
  msg <- readLIORef aliceSecret
  writeLIORef bobSecret $ msg
  -- as bob:
  do msg <- readLIORef aliceSecret
     -- (could also use putStrLnP...)
     lcur <- getLabel
     setLabelP (SimplePrivTCB TopSecret) Public
     putStrLn $ ">bob> " ++ msg
     raiseLabel lcur
  -- as the messenger:
  putStrLn $ "Intercepted message: " ++ show msg
-- <alice<
-- Wouldn't you like to know
-- >bob> Wouldn't you like to know
-- *** Exception: user error (write not allowed)


----------------------------------------------------------------------
-- Concurrency in LIO

-- We can also lift IO's concurrency primitives (forkIO and MVars)
-- into LIO...

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

newLMVar :: Label l => l -> a -> LIO l (LMVar l a)
newLMVar = newLMVarP NoPriv

newEmptyLMVarP :: Priv l p => p -> l -> LIO l (LMVar l a)
newEmptyLMVarP p l = do
  guardWriteP p l
  mvar <- liftIOTCB $ newEmptyMVar
  return $ LMVarTCB l mvar

newEmptyLMVar :: Label l => l -> LIO l (LMVar l a)
newEmptyLMVar = newEmptyLMVarP NoPriv

takeLMVarP :: Priv l p => p -> LMVar l a -> LIO l a
takeLMVarP p (LMVarTCB l mvar) = do
  raiseLabelP p l
  guardWriteP p l
  liftIOTCB $ takeMVar mvar

takeLMVar :: Label l => LMVar l a -> LIO l a
takeLMVar = takeLMVarP NoPriv

putLMVarP :: Priv l p => p -> LMVar l a -> a -> LIO l ()
putLMVarP p (LMVarTCB l mvar) x = do
  raiseLabelP p l
  guardWriteP p l
  liftIOTCB $ putMVar mvar x

putLMVar :: Label l => LMVar l a -> a -> LIO l ()
putLMVar = putLMVarP NoPriv


simpleExample8 = runSimpleExample $ do
  aliceSecret <- newEmptyLMVar TopSecret
  bobSecret <- newEmptyLMVar TopSecret
  -- as alice:
  forkLIO $ do putStrLn "<alice<"
               secret <- getLine
               putLMVar aliceSecret secret
  -- as bob:
  forkLIO $ do msg <- takeLMVarP (SimplePrivTCB TopSecret) aliceSecret
               putStrLn $ ">bob> " ++ msg
               putLMVar bobSecret ""
  -- as the messenger:
  msg <- takeLMVar bobSecret
  putStrLn $ "Intercepted message: " ++ show msg
-- *Main> simpleExample8
-- <alice<
-- hey
-- >bob> hey
-- *** Exception: user error (write not allowed)

-- (Morally, the messenger should also be in a separate thread, but if
-- we write the example that way, this thread runs and fails, aborting
-- the whole program, before either of the other threads have a chance
-- to do anything interesting!)


----------------------------------------------------------------------
-- The "Readers" Label Model

type Principal = String

-- SetLabel is a label model representing the set of principals to
-- whom data labeled as such is sensitive.
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
data SetPriv = SetPrivTCB (Set Principal)
  deriving Show

-- To downgrade a label by a privilege, we simply remove the
-- privilege's principals from the label; by exercising this
-- privilege, these principals are saying that they no longer consider
-- the data private.

instance Priv SetLabel SetPriv where
  downgradeP (SetPrivTCB p) (SetLabel s) = 
    SetLabel $ s Set.\\ p

-- It is useful to "mint" a new privilege that let's us bypass the restrictions of
-- a label directly.  Since set labels and privileges share the same underlying
-- structure
mintSetPrivTCB :: SetLabel -> SetPriv
mintSetPrivTCB (SetLabel ps) = SetPrivTCB ps

instance PublicAction SetLabel where publicLabel = fromList []

runSetExample :: (Show a) => LIO SetLabel a -> IO ()
runSetExample = runExample

-- Alice and Bob
alice       = fromList [ "Alice" ]
bob         = fromList [ "Bob" ]
aliceAndBob = fromList [ "Alice", "Bob" ]

alicePriv = mintSetPrivTCB alice
bobPriv   = mintSetPrivTCB bob

-- Encoding the Public/Classified/TopSecret label model
topSecret  = fromList [ "TopSecret" , "Classified" , "Public" ]
classified = fromList [ "Classified" , "Public" ]
public     = fromList [ "Public" ]

setExample0 = runSetExample $ return
  [ public     `canFlowTo` topSecret
  , classified `canFlowTo` classified 
  , classified `canFlowTo` topSecret 
  , topSecret  `canFlowTo` public
  , classified `canFlowTo` public
  , topSecret  `canFlowTo` classified ]

setExample1 = runSetExample $ return
  [ canFlowToP (mintSetPrivTCB topSecret ) topSecret  public
  , canFlowToP (mintSetPrivTCB topSecret ) classified public
  , canFlowToP (mintSetPrivTCB classified) classified public
  , canFlowToP (mintSetPrivTCB classified) topSecret  public ]


setExample0' = runSetExample $ return
  [ alice       `canFlowTo` aliceAndBob
  , bob         `canFlowTo` aliceAndBob
  , aliceAndBob `canFlowTo` alice
  , aliceAndBob `canFlowTo` bob
  , alice       `canFlowTo` bob
  , bob         `canFlowTo` alice ]

setExample1' = runSetExample $ return
  [ canFlowToP bobPriv   aliceAndBob alice
  , canFlowToP alicePriv aliceAndBob bob
  , canFlowToP alicePriv alice       bob
  , canFlowToP bobPriv   bob         alice
  ]

setExample2 = runSetExample $ do
  putStrLn "Hello public world!"
  raiseLabel alice
  putStrLnP alicePriv "hey!"
  raiseLabel $ alice `lub` bob
  putStrLnP alicePriv "hey again!"
-- Hello public world!
-- Hey!
-- *** Exception: user error (insufficient privs)

setExample3 = runSetExample $ do
  putStrLn "Hello public world!"
  raiseLabel alice
  putStrLnP alicePriv "hey!"
  raiseLabel $ alice `lub` bob
  putStrLnP allPrivs "hey again!"
-- Hello public world!
-- Hey!
-- *** Exception: user error (insufficient privs)
  where allPrivs  = mintSetPrivTCB $ alice `lub` bob

setExample4 = runSetExample $ do
  secretVar <- newEmptyLMVar alice
  -- First thread:
  forkLIO $ do
    raiseLabel alice
    putLMVar secretVar "Please do not share"
  -- Second thread:
  forkLIO $ do
    raiseLabel bob
    putStrLnP bobPriv "I'll wait for a message from Alice"
    secret <- takeLMVarP bobPriv secretVar
    putStrLnP bobPriv secret -- This will fail!


----------------------------------------------------------------------
-- Labeled values

-- Up to this point, we've assumed that a thread's current label
-- applies to all of the data that that thread might ever send or
-- write.  But there are situations where a thread may handle secrets
-- without "looking at them" (i.e., without making control decisions
-- based on secret information) or where we will want to combine
-- information with different secrecy labels in the same data
-- structure.  For example, we might want to create a database (a
-- single data structure) in which we can store secrets belonging to
-- both Alice and Bob.  We want Alice to be able to read Alice's
-- secrets and Bob to be able to read Bob's secrets, but not vice
-- versa.
--
-- To this end, we introduce a new type of "labeled values" -- i.e.,
-- Haskell values carrying an information-flow label restricting their
-- use.

data Labeled l t = LabeledTCB l t

-- `label` requires the value label to be above the current label
label :: Label l => l -> a -> LIO l (Labeled l a)
label l x = do
  guardWrite l
  return $ LabeledTCB l x

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

-- `labelOf` extracts the label from a labeled value
labelOf  :: Labeled l a -> l
labelOf (LabeledTCB l x) = l

-- For example, suppose DB is a type of very simple databases holding
-- a map from principal names to labeled values (in the example,
-- databases will hold a secret for alice and a secret for bob)...

type DB l = Map Principal (Labeled l String)

updateDB :: Label l => LMVar l (DB l) -> Principal -> l -> String -> LIO l ()
updateDB db prin l s = do
  m <- takeLMVarP NoPriv db
  v <- label l s
  putLMVarP NoPriv db $ Map.insert prin v m

queryDB :: Label l => LMVar l (DB l) -> Principal -> LIO l String
queryDB db prin = do
  m <- takeLMVarP NoPriv db
  putLMVarP NoPriv db m
  case Map.lookup prin m of
    Nothing -> return ""
    Just s' -> do r <- unlabel s'
                  return r

setExample9 = runSetExample $ do
  db <- newLMVarP NoPriv public $ Map.empty
  -- First alice thread:
  forkLIO $ do
    updateDB db "alice" alice "Alice's big secret"
{-
  -- Second alice thread:
  forkLIO $ do
    s <- queryDB db "alice"
    putStrLnP alicePriv $ "Alice: " ++ s
  -- First bob thread:
  forkLIO $ do
    updateDB db "bob" bob "Bob's even bigger secret"
  -- Second bob thread:
  forkLIO $ do
    s <- queryDB db "bob"
    putStrLnP bobPriv $ "Bob: " ++ s
-}

  where alicePriv = SetPrivTCB $ Set.singleton "alice"
        bobPriv   = SetPrivTCB $ Set.singleton "bob"

----------------------------------------------------------------------
-- Integrity (presented as a pure-integrity sets-of-principals model)

-- (Maybe we want to rename the SetLabel model to something like
-- Readers so that this can have the same representation but a
-- different name and a different behavior for the operations)

-- TODO: integrity examples



----------------------------------------------------------------------
-- DC labels
-- (but just give examples with pure conjunction and pure disjunction)

-- A new version of the DB example with both secrecy and integrity?


----------------------------------------------------------------------

main = undefined
