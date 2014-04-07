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
setLabelP p l = do
 lcur <- getLabel
 unless (canFlowToP p lcur l) $ 
   fail ("setLabel from " ++ (show lcur) ++ 
         " to " ++ (show l) ++ 
         " not allowed with privilege " ++ (show p))
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
--    putStrLn :: String -> LIO SimpleLabel ()
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

newLIORefP :: Priv l p => p -> l -> a -> LIO l (LIORef l a)
newLIORefP p l x = do
  guardWriteP p l
  ref <- liftIOTCB $ newIORef x
  return $ LIORefTCB l ref

newLIORef :: Label l => l -> a -> LIO l (LIORef l a)
newLIORef = newLIORefP NoPriv

readLIORefP :: Priv l p => p -> LIORef l a -> LIO l a
readLIORefP p (LIORefTCB l ref) = do
  raiseLabelP p l
  liftIOTCB $ readIORef ref

readLIORef :: Label l => LIORef l a -> LIO l a
readLIORef = readLIORefP NoPriv

writeLIORefP :: Priv l p => p -> LIORef l a -> a -> LIO l ()
writeLIORefP p (LIORefTCB l ref) x = do
  guardWriteP p l
  liftIOTCB $ writeIORef ref x

writeLIORef :: Label l => LIORef l a -> a -> LIO l ()
writeLIORef = writeLIORefP NoPriv

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

simpleExample6a = runSimpleExample $ do
  aliceSecret <- newLIORef TopSecret ""
  -- as alice:
  putStrLn "<alice<"
  secret <- getLine
  writeLIORef aliceSecret secret
  -- as the messenger:
  -- msg <- readLIORef aliceSecret
  putStrLn $ "Intercepted message: " ++ show secret

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
  do msg <- readLIORef bobSecret
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

-- BCP: Does it work? DS: Yep, added comment where it fails
simpleExample8 = runSimpleExample $ do
  aliceSecret <- newEmptyLMVar TopSecret
  bobSecret   <- newEmptyLMVar TopSecret
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
  putStrLn $ "Intercepted message: " ++ show msg  -- This will fail!
-- *Main> simpleExample8
-- <alice<
-- hey
-- >bob> hey
-- *** Exception: user error (write not allowed)

-- (Morally, the messenger should also be in a separate thread, but if
-- we write the example that way, this thread runs and fails before
-- either of the other threads have a chance to do anything
-- interesting!)


----------------------------------------------------------------------
-- the "readers" Label Model

type Principal = String

-- SecLabel is a label model representing the set of principals to
-- whom data labeled as such is sensitive. Hence, a "secrecy label".
newtype SecLabel = SecLabel (Set Principal)
                   deriving (Eq, Ord, Show)

-- Create a label from a list of principals
secLabel :: [Principal] -> SecLabel
secLabel = SecLabel . Set.fromList

instance Label SecLabel where
  -- Information can from one entitty to another only if the data
  -- becomes more secret, i.e., there are more principals to whom this
  -- data is sensitive.
  (SecLabel s1) `canFlowTo` (SecLabel s2) = s1 `Set.isSubsetOf` s2

  -- Combining data from two entities means that we have to preserve
  -- the privacy of the principals from both sets.
  (SecLabel s1) `lub` (SecLabel s2) = SecLabel $ s1 `Set.union` s2


-- | A set privilege means that we can "speak on behalf of" the
-- principals in the set, i.e., we can declassify the data of these
-- principals.
data SecPriv = SecPrivTCB (Set Principal)
  deriving Show

-- To downgrade a label by a privilege, we simply remove the
-- privilege's principals from the label; by exercising this
-- privilege, these principals are saying that they no longer consider
-- the data private.

instance Priv SecLabel SecPriv where
  downgradeP (SecPrivTCB p) (SecLabel s) = 
    SecLabel $ s Set.\\ p

-- It is useful to "mint" a new privilege that let's us bypass the restrictions of
-- a label directly.  Since set labels and privileges share the same underlying
-- structure
mintSecPrivTCB :: SecLabel -> SecPriv
mintSecPrivTCB (SecLabel ps) = SecPrivTCB ps

instance PublicAction SecLabel where publicLabel = secLabel []

runSecExample :: (Show a) => LIO SecLabel a -> IO ()
runSecExample = runExample

-- Alice and Bob
alice       = secLabel [ "Alice" ]
bob         = secLabel [ "Bob" ]
aliceAndBob = secLabel [ "Alice", "Bob" ]

alicePriv = mintSecPrivTCB alice
bobPriv   = mintSecPrivTCB bob

-- Encoding the Public/Classified/TopSecret label model
topSecret  = secLabel [ "TopSecret" , "Classified" ]
classified = secLabel [ "Classified" ]
public     = secLabel [ ]

topSecretPriv = mintSecPrivTCB topSecret
classifiedPriv = mintSecPrivTCB classified

secExample0 = runSecExample $ return
  [ public     `canFlowTo` topSecret
  , classified `canFlowTo` classified 
  , classified `canFlowTo` topSecret 
  , topSecret  `canFlowTo` public
  , classified `canFlowTo` public
  , topSecret  `canFlowTo` classified ]

-- fix
secExample1 = runSecExample $ return
  [ canFlowToP (mintSecPrivTCB topSecret ) topSecret  public
  , canFlowToP (mintSecPrivTCB topSecret ) classified public
  , canFlowToP (mintSecPrivTCB classified) classified public
  , canFlowToP (mintSecPrivTCB classified) topSecret  public ]

secExample0' = runSecExample $ return
  [ alice       `canFlowTo` aliceAndBob
  , bob         `canFlowTo` aliceAndBob
  , aliceAndBob `canFlowTo` alice
  , aliceAndBob `canFlowTo` bob
  , alice       `canFlowTo` bob
  , bob         `canFlowTo` alice ]

secExample1' = runSecExample $ return
  [ canFlowToP bobPriv   aliceAndBob alice
  , canFlowToP alicePriv aliceAndBob bob
  , canFlowToP alicePriv alice       bob
  , canFlowToP bobPriv   bob         alice
  ]

secExample2 = runSecExample $ do
  putStrLn "Hello public world!"
  raiseLabel alice
  putStrLnP alicePriv "hey!"
  raiseLabel $ bob
  putStrLnP alicePriv "hey again!"   -- fails
-- Hello public world!
-- Hey!
-- *** Exception: user error (insufficient privs)

secExample3 = runSecExample $ do
  putStrLn "Hello public world!"
  raiseLabel alice
  putStrLnP alicePriv "hey!"
  raiseLabel $ alice `lub` bob
  putStrLnP allPrivs "hey again!"
-- Hello public world!
-- Hey!
-- *** Exception: user error (insufficient privs)
  where allPrivs  = mintSecPrivTCB $ alice `lub` bob

secExample4 = runSecExample $ do
  secretVar <- newEmptyLMVar alice
  -- First thread:
  forkLIO $ do
    raiseLabel alice
    putLMVar secretVar "Please do not share"
  -- Second thread:
  forkLIO $ do
    raiseLabel bob
    putStrLnP bobPriv "I'll wait for a message from Alice"
    secret <- takeLMVarP bobPriv secretVar  -- BCP: This succeeds, yes? DS: Yes
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

-- `label` requires the value label to be above the current label, up
-- to privileges
labelP :: Priv l p => p -> l -> a -> LIO l (Labeled l a)
labelP priv l x = do
  guardWriteP priv l
  return $ LabeledTCB l x

label :: Label l => l -> a -> LIO l (Labeled l a)
label = labelP NoPriv

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


updateDBP :: Priv l p => p -> LMVar l (DB l) -> Principal -> l -> String -> LIO l ()
updateDBP priv db prin l s = do
  v <- labelP priv l s
  m <- takeLMVarP priv db
  putLMVarP priv db $ Map.insert prin v m

updateDB :: Label l => LMVar l (DB l) -> Principal -> l -> String -> LIO l ()
updateDB = updateDBP NoPriv

queryDB :: Label l => LMVar l (DB l) -> Principal -> LIO l String
queryDB db prin = do
  m <- takeLMVarP NoPriv db
  putLMVarP NoPriv db m
  case Map.lookup prin m of
    Nothing -> return ""
    Just s' -> do r <- unlabel s'
                  return r

secExample9 = runSecExample $ do
  db <- newLMVarP NoPriv public $ Map.empty
  -- First alice thread:
  forkLIO $ do
    updateDB db "alice" alice "Alice's big secret"
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
  -- Eve thread:
  forkLIO $ do
    putStrLnP NoPriv $ "Eve: I'm about to read the secret... " 
    s <- queryDB db "alice"
    putStrLnP NoPriv $ "Eve: " ++ s      -- Fails

----------------------------------------------------------------------
-- Integrity 

-- TrustLabel is a label model representing the set of principals that
-- principals that have participated in creating this value.
-- In DCLabels terminology this is a disjunction of principals.
newtype TrustLabel = TrustLabel (Set Principal)
                     deriving (Eq, Ord, Show)

-- Create a trust label from a list of principals
trustLabel :: [Principal] -> TrustLabel
trustLabel = TrustLabel . Set.fromList

-- BCP: It's easy to get confused with integrity.  Is the right
-- intuition for DC labels "These are the principals that have
-- endorsed this value"?  Or is it better to say "The set of
-- principals that have participated in creating this value?"  The
-- former is nice because it refers to an explicit downgrading step
-- that must have happened at some point in the past (assuming that
-- the default label is high---i.e., low-integrity). 
--
-- DS: The latter is the correct one for this label model, since it's
-- a disjunctive clause. The "highest" integrity value is one endorsed
-- by a single principal (this model can't have multiple principals
-- endorsing a value).

instance Label TrustLabel where
  -- Information can flow from one entity to another only if the
  -- direction of flow is from more trustworthy to less
  -- trustworthy---i.e., there are more principals that participated
  -- in creating this data.
  --
  -- We treat the empty set as the set of all principals, i.e., data that
  -- could have been created by anybody. This is the least trustworthy
  -- label (AKA top since everything flows to it).
  (TrustLabel s1) `canFlowTo` (TrustLabel s2) =
     Set.null s2 || if Set.null s1
                      then False
                      else s1 `Set.isSubsetOf` s2

  -- Combining data from two entities means that the new data is less
  -- trustworthy and thus could contain information from either entity.
  (TrustLabel s1) `lub` (TrustLabel s2) =
     if Set.null s1 || Set.null s2
       then trustLabel []
       else TrustLabel $ s1 `Set.union` s2

-- | When the privilege corresponds to a single principal this means
-- that we can "speak on behalf of" a principal, i.e., we can endorse
-- the data of this principal.
--
-- However, when the privilege is a set of principals, this is a
-- "delegated" privilege and we can only endorse data at this level.
-- That is, the privilege is strictly less powerful than a singleton.
data TrustPriv = TrustPrivTCB (Set Principal)
  deriving Show

-- What does the trust lattice look like?
--
--                                [ ]                           (low integrity)
--                                 
--                                ...
--                                 
-- ...               [ benjamin, deian, leo, emilio, ...]     ...
--
--                                ...
--
--                     [ benjamin, deian, leo ]
--                    /            |           \
--                   /             |            \
-- ... [benjamin, deian] ... [benjamin, leo] ... [deian, leo] ...
--
--                         ...           ...
--
--        [benjamin] ...   [deian] ...  [leo] ... [emilio] ...  (high integrity)

-- The "downgrade" for trust labels simply means returning the element
-- that is closest to the bottom of the lattice given the supplied
-- privileges. Since the trust label does not have a well-defined glb
-- (greatest lower bound), this definition also only makes sense in
-- certain cases. 
--
-- (DCLabels' trust/integrity components are CNF and thus does not
-- have this problem.)

instance Priv TrustLabel TrustPriv where
  downgradeP (TrustPrivTCB p) l@(TrustLabel s) =
    if Set.null glb'
      then l
      else TrustLabel glb'
    where glb' = p `Set.intersection` s
  -- The can-flow-to-given-privileges is more straight forward. It's
  -- simply saying that information can flow from l1 to l2 if either
  -- l2 is less trust worthy or the privileges can be used "endorse"
  -- the data at level l1.
  --
  canFlowToP (TrustPrivTCB p) l1 l2 = 
    l1 `canFlowTo` l2 || TrustLabel p `canFlowTo` l2
  -- (Conceptually this is the same as l1 /\ p => l2.)

instance PublicAction TrustLabel where publicLabel = trustLabel []

runTrustExample :: (Show a) => LIO TrustLabel a -> IO ()
runTrustExample = runExample

mintTrustPrivTCB :: TrustLabel -> TrustPriv
mintTrustPrivTCB (TrustLabel ps) = TrustPrivTCB ps

-- Alice and Bob
tAlice      = trustLabel [ "Alice" ]
tBob        = trustLabel [ "Bob" ]
tAliceOrBob = trustLabel [ "Alice", "Bob" ]
tCarlaOrDan = trustLabel [ "Carla", "Dan" ]

tAlicePriv      = mintTrustPrivTCB tAlice
tBobPriv        = mintTrustPrivTCB tBob
tAliceOrBobPriv = mintTrustPrivTCB tAliceOrBob
tCarlaOrDanPriv = mintTrustPrivTCB tCarlaOrDan

-- Encoding the Public/Classified/TopSecret label model
tTopSecret  = trustLabel [ "TopSecret" ]
tClassified = trustLabel [ "TopSecret", "Classified" ]
tPublic     = trustLabel [ ] -- Alt: ["TopSecret", "Classified", "Public" ]

tTopSecretPriv  = mintTrustPrivTCB tTopSecret
tClassifiedPriv = mintTrustPrivTCB tClassified
tPublicPriv     = mintTrustPrivTCB tPublic

trustExample0 = runTrustExample $ return
  [ tPublic     `canFlowTo` tTopSecret    -- False
  , tClassified `canFlowTo` tClassified   -- True
  , tClassified `canFlowTo` tTopSecret    -- False
  , tTopSecret  `canFlowTo` tPublic       -- True
  , tClassified `canFlowTo` tPublic       -- True
  , tTopSecret  `canFlowTo` tClassified ] -- True

-- Remember we don't want low integrity data to corrupt high-integrity
-- end points. So something endorsed by a principal with the public
-- level should not affect an entity that has been endorsed by someone
-- at top-secret level.

trustExample1 = runTrustExample $ return
  [ canFlowToP (mintTrustPrivTCB tTopSecret ) tPublic tTopSecret 
  , canFlowToP (mintTrustPrivTCB tTopSecret ) tPublic tClassified
  , canFlowToP (mintTrustPrivTCB tClassified) tPublic tClassified 
  , canFlowToP (mintTrustPrivTCB tClassified) tPublic tTopSecret ]

trustExample2 = runTrustExample $ return
  [ tAlice       `canFlowTo` tAliceOrBob    -- True
  , tBob         `canFlowTo` tAliceOrBob    -- True
  , tAliceOrBob  `canFlowTo` tAlice         -- False
  , tAliceOrBob  `canFlowTo` tBob           -- False
  , tAlice       `canFlowTo` tBob           -- False
  , tBob         `canFlowTo` tAlice         -- False
  , tCarlaOrDan  `canFlowTo` tAliceOrBob ]  -- False

trustExample3 = runTrustExample $ return
  [ canFlowToP tAlicePriv      tAliceOrBob tAlice      -- True
  , canFlowToP tBobPriv        tAliceOrBob tBob        -- True
  , canFlowToP tBobPriv        tAlice      tBob        -- True
  , canFlowToP tAlicePriv      tBob        tAlice      -- True
  , canFlowToP tAlicePriv      tCarlaOrDan tAliceOrBob -- True
  , canFlowToP tAliceOrBobPriv tCarlaOrDan tAliceOrBob -- True
  , canFlowToP tCarlaOrDanPriv tCarlaOrDan tAliceOrBob -- False 
  ]

trustExample4 = runTrustExample $ do
  ref <- newLIORef tAlice "w00t"
  readLIORef ref
-- *** Exception: user error (write from TrustLabel (fromList []) to
-- TrustLabel (fromList ["Alice"]) not allowed with privilege NoPriv)

trustExample5 = runTrustExample $ do
  aliceSecret <- newLIORefP tAlicePriv tAlice ""   -- []
  bobSecret   <- newLIORefP tBobPriv tBob ""       -- []
  setLabelP tBobPriv tBob                          -- [Bob]
  writeLIORef bobSecret "hey w00t w00t"
  readLIORef aliceSecret                           -- [Alice, Bob]

trustExample6 = runTrustExample $ do
  aliceSecret <- newLIORefP tAlicePriv tAlice ""
  -- as alice:
  do putStrLn "<alice<"
     secret <- getLine
     writeLIORefP tAlicePriv aliceSecret secret
  -- as the messenger:
  msg <- readLIORef aliceSecret
  putStrLn $ "Intercepted message: " ++ show msg
  writeLIORef aliceSecret $ msg ++ " is corrupt"  -- Fails here!

-- Above, the messanger is able to intercept the message, but when it
-- tries to update the reference with a new message (as to corrupt the
-- ref content), an exception is raised.

trustExample7 = runTrustExample $ do
  sharedSecret <- newLIORefP tAlicePriv tAliceOrBob ""
  -- as alice:
  do putStrLn "<alice<"
     secret <- getLine
     writeLIORefP tAlicePriv sharedSecret secret
  -- as bbob
  do putStrLn "<bob<"
     secret <- getLine
     existing <- readLIORef sharedSecret
     writeLIORefP tBobPriv sharedSecret $ show [existing, secret]
  -- as the messenger:
  msg <- readLIORef sharedSecret
  putStrLn $ "Intercepted message: " ++ show msg
  writeLIORef sharedSecret $ msg ++ " is corrupt" -- Fails here!

----------------------------------------------------------------------
-- DC labels

-- SecLabel is not enough since we sometimes want to consider data that
-- either Alice or Bob can declassify, i.e., they both have equal
-- stake in the data. 
--
-- TrustLabel is not enough since we sometimes want to allow multiple
-- principals to endorse a piece of data.
--
-- This is where the DCLabels model comes into play. It has 2
-- components, a secrecy and an integrity component, each being a
-- propositional formula (by convention in conjunctive normal form).
-- (Conceptually SecLabel was a conjunction of principals, TrustLabel
-- was a disjunction of principals.)

newtype CNF = CNF (Set (Set Principal))
              deriving (Eq, Ord, Show)

-- When considering secrecy, cTrue means data is public.  When
-- considering integrity, cTrue means data carries no integrity
-- guarantees, i.e., it is not endorsed by anybody.
cTrue :: CNF
cTrue = CNF $ Set.empty

-- When considering secrecy, cFalse, corresponds to the most secret
-- data. In a system with a finite set of principals, this corresponds
-- to the conjunction of all the principals, i.e., the data is
-- sensitive to everybody.  For that reason, cFalse generally
-- shouldn't appear in a data label.  However, it is convenient to
-- include it as to allow a thread to arbitrarily raise its label.
--
-- When considering integrity, cFalse indicates the highest integrity
-- data. In a system with a finite set of principals, this corresponds
-- to the conjunction of all the principals, i.e., the data was
-- endorsed by everybody.
cFalse :: CNF
cFalse = CNF $ Set.singleton $ Set.empty

-- Secrecy: The first formula describes the authority required to make
-- the data public.
-- Integrity: The second formula describes the authority with which
-- immutable data was endorsed, or the authority required to modify
-- mutable data.
data DCLabel = DCLabel CNF CNF
               deriving (Eq, Ord, Show)

-- Helper constructor:
(%%) :: CNF -> CNF -> DCLabel
(%%) = DCLabel
infix 6 %%

instance Label DCLabel where
  lub (DCLabel s1 i1) (DCLabel s2 i2) = 
    DCLabel (s1 `cAnd` s2) (i1 `cOr`  i2)
  -- The join preserves the privacy of both labels: must satisfy both
  -- s1 and s2 to read data. The new data is less trustworthy, it is
  -- composed of information from either i1 or i2.

  canFlowTo (DCLabel s1 i1) (DCLabel s2 i2) = 
    s2 `cImplies` s1 && i1 `cImplies` i2
  -- Information can flow from one entity to another if the
  -- destination's security formula satisfies the source, i.e., it
  -- preserves the secrecy of the data. Dually, the source must be at
  -- least as trustworthy as the destination.

-- But now we need to define the helper functions cAnd, cOr, and
-- cImplies. First, let's define some helper functions.

-- Function that checks if the predicate holds for any element in the
-- set.
setAny :: (a -> Bool) -> Set a -> Bool
setAny prd = Set.foldr' (\a -> (prd a ||)) False

-- Function that checks if the predicate holds for all elements in the
-- set.
setAll :: (a -> Bool) -> Set a -> Bool
setAll prd = Set.foldr' (\a -> (prd a &&)) True

-- Okay, now let's define cAnd:

cAnd :: CNF -> CNF -> CNF
cAnd c (CNF ds) = Set.foldr cInsert c ds

-- cAnd simply  "inserts" every disjunctive clause from the second CNF
-- (ds) with cInsert "into" c.

cInsert :: Set Principal -> CNF -> CNF
cInsert dnew c@(CNF ds)
  | setAny (`Set.isSubsetOf` dnew) ds = c
  | otherwise = CNF $ Set.insert dnew $ Set.filter (not . (dnew `Set.isSubsetOf`)) ds

-- cInsert inserts a new disjunctive clause dnew into the CNF c if
-- there is no clause that implies this clause (and thus adding it
-- would be redundant). Indeed, when adding dnew to ds we also remove
-- any disjunctive clause that is implied by this new clause.

-- It is useful to create a CNF from a list of disjunction into a CNF:

cFromList :: [Set Principal] -> CNF
cFromList = Set.foldr cInsert cTrue . Set.fromList

cFromLists :: [[Principal]] -> CNF
cFromLists = cFromList . map Set.fromList

-- To ensure that each formula is indeed CNF, we use cInsert to
-- insert each disjunctive clause, one at a time.

-- Now, let's define the disjunction of formulas:

cOr :: CNF -> CNF -> CNF
cOr (CNF ds1) (CNF ds2) =
  cFromList $ [Set.union d1 d2 | d1 <- Set.toList ds1, d2 <- Set.toList ds2]

-- For every disjunctive clause in the first and second CNFs take the
-- disjunction. Then take the conjunction of all these intermediate
-- clauses, removing any redundant clauses.

-- Finally, let's define the implication function:

cImplies :: CNF -> CNF -> Bool
cImplies (CNF ds1) (CNF ds2) = setAll ds1Implies ds2
  where ds1Implies d = setAny (`Set.isSubsetOf` d) ds1

-- This function makes sure that for each disjunctions (ds2) in the
-- second CNF, the first formula (ds1) implies the disjuction. That
-- is, there is a disjuction in ds1 that implies the disjuction (d)
-- from ds2.


-- DCLabel privileges are expressed as a CNF of the principals whose
-- authority is being exercised. The conjunctive nature means that the
-- code can speak on behalf of multiple principals. The disjunctive
-- part means that code can "own" a delegated privilege.
data DCPriv = DCPrivTCB CNF
  deriving Show

instance Priv DCLabel DCPriv where
  downgradeP (DCPrivTCB p@(CNF ps)) (DCLabel (CNF ds) i) = 
    DCLabel s (i `cAnd` p)
    where s = CNF $ Set.filter (not . pImplies) ds
          pImplies d = setAny (`Set.isSubsetOf` d) ps
  -- For secrecy we remove any clause that is implied by the
  -- privilege; for the integrity we simply take th glb.
  -- This returns the element in the lattice that is less secret and
  -- of higher integrity. (Overall, closer to the bottom of the
  -- lattice.)


  canFlowToP (DCPrivTCB p) (DCLabel s1 i1) (DCLabel s2 i2) =
    (s2 `cAnd` p) `cImplies` s1 && (i1 `cAnd` p) `cImplies` i2
  -- Here the privilege is used to bypass the secrecy restrictions by
  -- adding the principals to the destination label. Dually, the
  -- privilege is used to endorse the source label.

instance PublicAction DCLabel where publicLabel = cTrue %% cTrue

runDCExample :: (Show a) => LIO DCLabel a -> IO ()
runDCExample = runExample

--
--

cAlice       = cFromLists [["Alice"]]
cBob         = cFromLists [["Bob"]]
cAliceAndBob = cFromLists [["Alice"],["Bob"]]
cAliceOrBob  = cFromLists [["Alice","Bob"]]
cCarlaOrDan  = cFromLists [["Carla","Dan"]]

cAlicePriv       = DCPrivTCB cAlice       
cBobPriv         = DCPrivTCB cBob         
cAliceAndBobPriv = DCPrivTCB cAliceAndBob 
cAliceOrBobPriv  = DCPrivTCB cAliceOrBob  
cCarlaOrDanPriv  = DCPrivTCB cCarlaOrDan  

-- First part, same as secExample0'
dcSecExample0 = runDCExample $ return
  [ (cAlice       %% cTrue) `canFlowTo` (cAliceAndBob %% cTrue) 
  , (cBob         %% cTrue) `canFlowTo` (cAliceAndBob %% cTrue) 
  , (cAliceAndBob %% cTrue) `canFlowTo` (cAlice       %% cTrue) 
  , (cAliceAndBob %% cTrue) `canFlowTo` (cBob         %% cTrue) 
  , (cAlice       %% cTrue) `canFlowTo` (cBob         %% cTrue) 
  , (cBob         %% cTrue) `canFlowTo` (cAlice       %% cTrue) 
  --
  , (cAliceOrBob  %% cTrue) `canFlowTo` (cAlice       %% cTrue) 
  , (cAliceOrBob  %% cTrue) `canFlowTo` (cAliceAndBob %% cTrue) 
  , (cAliceOrBob  %% cTrue) `canFlowTo` (cTrue        %% cTrue) 
  ]
  

-- First part, same as secExample1'
dcSecExample1 = runDCExample $ return
  [ canFlowToP cBobPriv   (cAliceAndBob %% cTrue) ( cAlice %% cTrue)
  , canFlowToP cAlicePriv (cAliceAndBob %% cTrue) ( cBob   %% cTrue)
  , canFlowToP cAlicePriv (cAlice       %% cTrue) ( cBob   %% cTrue)
  , canFlowToP cBobPriv   (cBob         %% cTrue) ( cAlice %% cTrue)
  --
  , canFlowToP cAlicePriv (cAliceOrBob %% cTrue)  (cTrue   %% cTrue) 
  , canFlowToP cBobPriv   (cAliceOrBob %% cTrue)  (cTrue   %% cTrue) 
  ]

-- Same as trustExample2
dcTrustExample0 = runDCExample $ return
  [ (cTrue %% cAlice     ) `canFlowTo` (cTrue %% cAliceOrBob  )   -- True
  , (cTrue %% cBob       ) `canFlowTo` (cTrue %% cAliceOrBob  )   -- True
  , (cTrue %% cAliceOrBob) `canFlowTo` (cTrue %% cAlice       )   -- False
  , (cTrue %% cAliceOrBob) `canFlowTo` (cTrue %% cBob         )   -- False
  , (cTrue %% cAlice     ) `canFlowTo` (cTrue %% cBob         )   -- False
  , (cTrue %% cBob       ) `canFlowTo` (cTrue %% cAlice       )   -- False
  , (cTrue %% cCarlaOrDan) `canFlowTo` (cTrue %% cAliceOrBob  )   -- False
  --                                                          
  , (cTrue %% cAliceAndBob) `canFlowTo` (cTrue %% cAlice      )   -- True
  , (cTrue %% cAliceAndBob) `canFlowTo` (cTrue %% cBob        )   -- True
  , (cTrue %% cAlice)       `canFlowTo` (cTrue %% cAliceAndBob)   -- False
  , (cTrue %% cBob  )       `canFlowTo` (cTrue %% cAliceAndBob)   -- False
  ]

-- First part, same as trustExample3 
dcTrustExample1 = runDCExample $ return
  [ canFlowToP cAlicePriv      (cTrue %% cAliceOrBob) (cTrue %% cAlice      ) -- True
  , canFlowToP cBobPriv        (cTrue %% cAliceOrBob) (cTrue %% cBob        ) -- True
  , canFlowToP cBobPriv        (cTrue %% cAlice     ) (cTrue %% cBob        ) -- True
  , canFlowToP cAlicePriv      (cTrue %% cBob       ) (cTrue %% cAlice      ) -- True
  , canFlowToP cAlicePriv      (cTrue %% cCarlaOrDan) (cTrue %% cAliceOrBob ) -- True
  , canFlowToP cAliceOrBobPriv (cTrue %% cCarlaOrDan) (cTrue %% cAliceOrBob ) -- True
  , canFlowToP cCarlaOrDanPriv (cTrue %% cCarlaOrDan) (cTrue %% cAliceOrBob ) -- False 
  --                                                                        
  , canFlowToP cAlicePriv       (cTrue %% cTrue     ) (cTrue %% cAlice      )  -- True
  , canFlowToP cBobPriv         (cTrue %% cTrue     ) (cTrue %% cBob        )  -- True
  , canFlowToP cAlicePriv       (cTrue %% cTrue     ) (cTrue %% cAliceOrBob )  -- True
  , canFlowToP cBobPriv         (cTrue %% cTrue     ) (cTrue %% cAliceOrBob )  -- True
  , canFlowToP cAliceAndBobPriv (cTrue %% cTrue     ) (cTrue %% cAliceAndBob)  -- True
  , canFlowToP cBobPriv         (cTrue %% cAlice    ) (cTrue %% cAliceAndBob)  -- True
  , canFlowToP cAlicePriv       (cTrue %% cBob      ) (cTrue %% cAliceAndBob)  -- True
  ]

-- Same as secExample9
dcSecExample9 = runDCExample $ do
  db <- newLMVarP NoPriv publicLabel $ Map.empty
  -- First alice thread:
  forkLIO $ do
    updateDB db "alice" (cAlice %% cTrue) "Alice's big secret"
  -- Second alice thread:
  forkLIO $ do
    s <- queryDB db "alice"
    putStrLnP cAlicePriv $ "Alice: " ++ s
  -- First bob thread:
  forkLIO $ do
    updateDB db "bob" (cBob %% cTrue) "Bob's even bigger secret"
  -- Second bob thread:
  forkLIO $ do
    s <- queryDB db "bob"
    putStrLnP cBobPriv $ "Bob: " ++ s
  -- Eve thread:
  forkLIO $ do
    putStrLnP NoPriv $ "Eve: I'm about to read the secret... " 
    s <- queryDB db "alice"
    putStrLnP NoPriv $ "Eve: " ++ s      -- Fails

dcSecExample9' = runDCExample $ do
  db <- newLMVarP NoPriv publicLabel $ Map.empty
  -- First alice thread:
  forkLIO $ do
    updateDB db "alice" (cAlice %% cTrue) "Alice's big secret"
  -- Second alice thread:
  forkLIO $ do
    s <- queryDB db "alice"
    putStrLnP cAlicePriv $ "Alice: " ++ s
  -- First bob thread:
  forkLIO $ do
    updateDB db "bob" (cBob %% cTrue) "Bob's even bigger secret"
    updateDB db "alice" (cAlice %% cTrue) "Launch at dawn"
  -- Second bob thread:
  forkLIO $ do
    s <- queryDB db "bob"
    putStrLnP cBobPriv $ "Bob: " ++ s
  -- Eve thread:
  forkLIO $ do
    putStrLnP NoPriv $ "Eve: I'm about to read the secret... " 
    s <- queryDB db "alice"
    putStrLnP NoPriv $ "Eve: " ++ s      -- Fails
  -- Third  alice thread:
  forkLIO $ do
    s <- queryDB db "alice"
    putStrLnP cAlicePriv $ "Alice: " ++ s

-- This shows that we have secrecy since Eve cannot leak the data, but
-- no integrity: Bob corrupted Alice's DB cell.

dcSecExample9'' = runDCExample $ do
  db <- newLMVarP NoPriv publicLabel $ Map.empty
  -- First alice thread:
  forkLIO $ do
    updateDBP cAlicePriv db "alice" (cAlice %% cAlice) "Alice's big secret"
  -- Second alice thread:
  forkLIO $ do
    s <- queryDB db "alice"
    putStrLnP cAlicePriv $ "Alice: " ++ s
  -- First bob thread:
  forkLIO $ do
    updateDBP cBobPriv db "bob" (cBob %% cBob) "Bob's even bigger secret"
    -- In a real app we won't be able to specify a new label:
    updateDB db "alice" (cAlice %% cAlice) "Launch at dawn" -- Fails
  -- Second bob thread:
  forkLIO $ do
    s <- queryDB db "bob"
    putStrLnP cBobPriv $ "Bob: " ++ s
  -- Eve thread:
  forkLIO $ do
    putStrLnP NoPriv $ "Eve: I'm about to read the secret... " 
    s <- queryDB db "alice"
    putStrLnP NoPriv $ "Eve: " ++ s      -- Fails
  -- Third  alice thread:
  forkLIO $ do
    s <- queryDB db "alice"
    putStrLnP cAlicePriv $ "Alice: " ++ s


-- (but just gidcve examples with pure conjunction and pure disjunction)

-- A new version of the DB example with both secrecy and integrity?

----------------------------------------------------------------------

main = undefined
