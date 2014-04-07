----------------------------------------------------------------------
----------------------------------------------------------------------
----------------------------------------------------------------------
-- OLD

{-
----------------------------------------------------------------------
-- A "Writers" label model

-- Example 7 is the interesting one here...

-- TrustLabel is a label model representing the set of principals that
-- that have participated (or might have participated) in creating
-- this value.  (In the DCLabels terminology below this is a
-- "disjunction" of principals.)
data Writers = All
             | Some (Set Principal)
             deriving (Eq, Show)

newtype TrustLabel = TrustLabel Writers
                     deriving (Eq, Show)

-- Create a trust label from a list of principals
trustLabel :: [Principal] -> TrustLabel
trustLabel = TrustLabel . Some . Set.fromList

instance Label TrustLabel where
  -- Information can flow from one place to another only if the
  -- direction of flow is from more trustworthy to less
  -- trustworthy---i.e., more principals are listed as having
  -- participated in creating the data in the target place than in the
  -- source.
  (TrustLabel s1) `canFlowTo` (TrustLabel s2) =
     case (s1,s2) of
       (_,All) -> True
       (All,_) -> False
       (Some ps1, Some ps2) -> ps1 `Set.isSubsetOf` ps2

  -- Combining data from two entities makes the new data less
  -- trustworthy (because it could contain information coming from
  -- either entity).
  (TrustLabel s1) `lub` (TrustLabel s2) =
     TrustLabel $ case (s1,s2) of 
       (_,All) -> All
       (All,_) -> All
       (Some ps1, Some ps2) -> Some (ps1 `Set.union` ps2)

-- Next, we define privileges for this label model.  
--
-- When the privilege corresponds to a single principal this, means
-- that we can "speak on behalf of" a principal, i.e., we can endorse
-- the data of this principal.
--
-- However, when the privilege is a set of principals, this is a
-- "delegated" privilege and we can only endorse data at this level.
-- That is, the privilege is strictly less powerful than a singleton.
data TrustPriv = TrustPrivTCB (Set Principal)
  deriving Show

-- What does the trust lattice look like?  (Dropping the "Some"
-- constructor, for brevity.)
--
--                                All                           (low integrity)
--                                 
--                                ...
--                                 
--              ... [ benjamin, deian, leo, emilio, ...]     ...
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
-- (DCLabels' trust/integrity components include both conjunction and
-- disjunction, and thus do not have this problem.)

instance Priv TrustLabel TrustPriv where
  downgradeP (TrustPrivTCB p) l@(TrustLabel s) =
    if glb' == All
      then l
      else TrustLabel glb'
    where glb' = case (p,s) of
                   (All,_) -> s
                   (_,All) -> p
                   (Some p', Some s') -> Some $ p' `Set.intersection` s'
  -- The can-flow-to-given-privileges relation is more
  -- straightforward. It's simply saying that information can flow
  -- from l1 to l2 if either l2 is less trustworthy or the privileges
  -- can be used "endorse" the data at level l1.
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
-- tries to update the reference with a new message (thus corrupting the
-- ref's content), an exception is raised.

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
-}

