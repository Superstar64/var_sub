{-# LANGUAGE NoMonomorphismRestriction #-}

module VarSub where

import Control.Arrow (second)
import Control.Monad.IO.Class
import Control.Monad.Trans.State.Strict
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Traversable (for)

infix 6 :=

infix 6 :<=

data FlexibleState = FlexibleState {incompleteUpperBounds :: [Type], greatestLowerRigidBound :: Maybe String} deriving (Show)

-- all upper bounds
-- a transitive closure is implied
data RigidBounds = RigidBounds {upperRigidBounds :: Set String} deriving (Show)

data Context = Context
  { problems :: [Equation],
    flexible :: Map String FlexibleState,
    rigid :: Map String RigidBounds,
    freshCounter :: Int,
    environment :: Map String Type,
    answers :: [(String, Type)]
  }
  deriving (Show)

-- flexible are flexible type variables
-- rigid are rigid type variables
-- function are of the form σ -s> τ, where `s` is the region (latent effect)
-- pointer are of the form `RGNRef s a` (alternatively `STRef s a`), where s is the region
data Type = Flexible String | Rigid String | Function Type Type Type | Pointer Type Type deriving (Show)

-- := are equality constrains, :<= are subtyping constrains
data Equation = Type := Type | Type :<= Type deriving (Show)

class Substitute e where
  substitute :: Type -> String -> e -> e

instance Substitute Type where
  substitute ex x (Flexible x') | x == x' = ex
  substitute _ _ (Flexible x) = Flexible x
  substitute _ _ (Rigid x) = Rigid x
  substitute ex x (Function e e' e'') = Function (substitute ex x e) (substitute ex x e') (substitute ex x e'')
  substitute ex x (Pointer e e') = Pointer (substitute ex x e) (substitute ex x e')

instance Substitute Equation where
  substitute ex x (e := e') = substitute ex x e := substitute ex x e'
  substitute ex x (e :<= e') = substitute ex x e :<= substitute ex x e'

instance Substitute e => Substitute [e] where
  substitute ex x es = map (substitute ex x) es

instance Substitute e => Substitute (Map k e) where
  substitute ex x es = fmap (substitute ex x) es

instance (Substitute e, Substitute e') => Substitute (e, e') where
  substitute ex x (e, e') = (substitute ex x e, substitute ex x e')

instance Substitute FlexibleState where
  substitute ex x (FlexibleState upper lower) = FlexibleState (substitute ex x upper) lower

indexFlexible' :: String -> Map String FlexibleState -> FlexibleState
indexFlexible' x = Map.findWithDefault (FlexibleState [] Nothing) x

indexFlexible :: Monad m => String -> StateT Context m FlexibleState
indexFlexible x = indexFlexible' x <$> flexible <$> get

indexRigid' :: String -> Map String RigidBounds -> RigidBounds
indexRigid' x = Map.findWithDefault (RigidBounds $ Set.singleton x) x

indexRigid :: Monad m => String -> StateT Context m RigidBounds
indexRigid x = indexRigid' x <$> rigid <$> get

rigidSubType' :: String -> String -> Map String RigidBounds -> Bool
rigidSubType' x y rigid = let RigidBounds bounds = indexRigid' x rigid in Set.member y bounds

rigidSubType :: Monad m => String -> String -> StateT Context m Bool
rigidSubType x y = rigidSubType' x y <$> rigid <$> get

rigidJoin :: String -> String -> Map String RigidBounds -> Maybe String
rigidJoin x y rigid = minimal (Set.toList upper) upper
  where
    upper = upperRigidBounds (indexRigid' x rigid) `Set.intersection` upperRigidBounds (indexRigid' y rigid)
    minimal [] candidates | [item] <- Set.toList candidates = Just item
    minimal (head : tail) candidates = minimal tail $ Set.filter (\x -> rigidSubType' x head rigid) candidates
    minimal [] _ = Nothing

reachFlexible :: Monad m => Type -> String -> StateT Context m Bool
reachFlexible (Flexible x) x' | x == x' = pure True
reachFlexible (Flexible x) x' = do
  FlexibleState children _ <- indexFlexible x
  or <$> for children (\e -> reachFlexible e x')
reachFlexible _ _ = pure False

modifyProblems :: Monad m => ([Equation] -> [Equation]) -> StateT Context m ()
modifyProblems f = modify $ \context -> context {problems = f $ problems context}

modifyFlexible :: Monad m => (Map String FlexibleState -> Map String FlexibleState) -> StateT Context m ()
modifyFlexible f = modify $ \context -> context {flexible = f $ flexible context}

modifyAnswers :: Monad m => ([(String, Type)] -> [(String, Type)]) -> StateT Context m ()
modifyAnswers f = modify $ \context -> context {answers = f $ answers context}

match :: Monad m => Type -> Type -> StateT Context m ()
match e e' = modifyProblems (e := e' :)

subtype :: Monad m => Type -> Type -> StateT Context m ()
subtype e e' = modifyProblems (e :<= e' :)

variable :: Type -> Bool
variable (Flexible _) = True
variable (Rigid _) = True
variable _ = False

constrain :: MonadFail m => Type -> Type -> StateT Context m ()
constrain (Flexible x) (Flexible x') | x == x' = pure ()
constrain (Flexible x) e | variable e = do
  b <- reachFlexible e x
  if b
    then match (Flexible x) e
    else do
      FlexibleState upper lower <- indexFlexible x
      let upper' = e : upper
      modifyFlexible (Map.insert x (FlexibleState upper' lower))
      for lower $ \x' -> subtype (Rigid x') e
      pure ()
constrain (Rigid x) (Flexible x') = do
  FlexibleState upper lower <- indexFlexible x'
  rigid <- rigid <$> get
  lower' <- case lower of
    Nothing -> pure $ x
    Just y -> do
      Just lower' <- pure $ rigidJoin x y rigid
      pure lower'
  modifyFlexible (Map.insert x' (FlexibleState upper (Just lower')))
  for upper $ \e -> subtype (Rigid lower') e
  pure ()
constrain (Rigid x) (Rigid x') = do
  True <- rigidSubType x x'
  pure ()
constrain _ _ = fail "can only constrain variables"

-- todo occurance check
unify :: MonadFail m => Type -> Type -> StateT Context m ()
unify (Flexible x) (Flexible x') | x == x' = pure ()
unify (Flexible x) e = do
  FlexibleState upper lower <- indexFlexible x
  for upper $ \e' -> subtype e e'
  for lower $ \x' -> subtype (Rigid x') e
  modifyProblems (substitute e x)
  modifyFlexible (substitute e x . Map.delete x)
  modifyAnswers (map (second $ substitute e x))
  -- if a cycle forms then it must contain `e`
  -- so if the right handside is a variable
  -- then reunify it's constraints
  case e of
    Flexible x -> do
      FlexibleState upper lower <- indexFlexible x
      for upper $ \e -> subtype (Flexible x) e
      for lower $ \x' -> subtype (Rigid x') (Flexible x)
      modifyFlexible (Map.delete x)
    _ -> pure ()
  modifyAnswers ((x, e) :)
unify e (Flexible x) = unify (Flexible x) e
unify (Rigid x) (Rigid x') | x == x' = pure ()
unify (Function e1 e2 e3) (Function e1' e2' e3') = do
  match e1 e1'
  match e2 e2'
  match e3 e3'
unify (Pointer e1 e2) (Pointer e1' e2') = do
  match e1 e1'
  match e2 e2'
unify _ _ = fail "unable to unify"

solve :: (MonadIO m, MonadFail m) => StateT Context m ()
solve = do
  context <- get
  case problems context of
    [] -> pure ()
    (e := e' : problems') -> do
      liftIO $ print (e := e')
      modifyProblems (const problems')
      unify e e'
      solve
    (e :<= e' : problems') -> do
      liftIO $ print (e :<= e')
      modifyProblems (const problems')
      constrain e e'
      solve

runWithRaw :: (MonadIO m, MonadFail m) => Map String RigidBounds -> [Equation] -> m Context
runWithRaw rigid problems = execStateT solve (Context problems mempty rigid 0 Map.empty [])

runRaw :: (MonadIO m, MonadFail m) => [Equation] -> m Context
runRaw = runWithRaw mempty

rigidSample = Map.singleton "a" $ RigidBounds $ Set.fromList ["a", "b"]

rigidSample2 = Map.fromList [("a", RigidBounds $ Set.fromList ["a", "c"]), ("b", RigidBounds $ Set.fromList ["b", "c"])]

sampleRaw1 =
  map
    (\(a, b) -> Flexible a :<= Flexible b)
    [ ("a", "b"),
      ("b", "c"),
      ("c", "a")
    ]

sampleRaw2 =
  map
    (\(a, b) -> Flexible a :<= Flexible b)
    [ ("a", "b"),
      ("b", "c"),
      ("c", "a"),
      ("d", "a"),
      ("e", "a"),
      ("f", "b"),
      ("h", "b"),
      ("a", "i"),
      ("a", "j"),
      ("b", "k"),
      ("b", "l")
    ]

-- run with rigidSample
sampleRaw3 = [Flexible "a" := Rigid "a", Flexible "b" := Rigid "b", Flexible "a" :<= Flexible "b"]

sampleRaw3' = [Flexible "a" :<= Flexible "b", Flexible "a" := Rigid "a", Flexible "b" := Rigid "b"]

-- run with rigidSample2
sampleRaw4 = [Rigid "a" :<= Flexible "x", Rigid "b" :<= Flexible "x"]

-- should error out
sampleRaw5 = [Rigid "x" :<= Flexible "a", Rigid "y" :<= Flexible "a"]

data Term
  = Variable String
  | Lambda String Term
  | LambdaAscribe String Type Term
  | Application Term Term
  | Dereference Term
  | Annotate Type Type Term
  deriving (Show)

fresh :: Monad m => StateT Context m Type
fresh = do
  i <- freshCounter <$> get
  modify $ \state -> state {freshCounter = i + 1}
  pure $ Flexible (show i)

-- type checking returns a type and an effect
typeCheck :: MonadFail m => Term -> StateT Context m (Type, Type)
typeCheck (Variable x) = do
  σ <- (Map.! x) <$> environment <$> get
  π <- fresh
  pure (σ, π)
typeCheck (Lambda x e) = do
  σ <- fresh
  typeCheck (LambdaAscribe x σ e)
typeCheck (LambdaAscribe x σ e) = do
  modify $ \state -> state {environment = Map.insert x σ $ environment state}
  (τ, π) <- typeCheck e
  modify $ \state -> state {environment = Map.delete x $ environment state}
  π' <- fresh
  pure (Function σ π τ, π')
typeCheck (Application e e') = do
  σ <- fresh
  π <- fresh
  τ <- fresh
  (v, π') <- typeCheck e
  match v (Function σ π τ)
  match π π'
  (σ', π'') <- typeCheck e'
  match σ σ'
  match π π''
  pure (τ, π)
typeCheck (Dereference e) = do
  σ <- fresh
  π <- fresh
  (v, π') <- typeCheck e
  match v (Pointer π σ)
  constrain π π'
  pure (σ, π')
typeCheck (Annotate σ π e) = do
  (σ', π') <- typeCheck e
  match σ σ'
  match π π'
  pure (σ, π)

runWith :: (MonadFail m, MonadIO m) => Map String RigidBounds -> Term -> m ((Type, Type), Context)
runWith rigid e = flip runStateT (Context [] mempty rigid 0 Map.empty []) $ do
  (σ, π) <- typeCheck e
  solve
  answers <- answers <$> get
  pure $ foldr (\(x, τ) -> substitute τ x) (σ, π) answers

run :: (MonadFail m, MonadIO m) => Term -> m ((Type, Type), Context)
run = runWith Map.empty

sample1 = Lambda "x" $ Dereference $ Variable "x"

sample2 =
  LambdaAscribe "x" (Pointer (Rigid "a") (Flexible "b")) $
    Dereference $
      Variable "x"

-- run with rigidSample
sample3 =
  LambdaAscribe "x" (Pointer (Rigid "a") (Flexible "b")) $
    Dereference $ Variable "x"

-- run with rigidSample
sample4 =
  LambdaAscribe "x" (Pointer (Rigid "a") (Flexible "b")) $
    Annotate
      (Flexible "c")
      (Rigid "b")
      $ Dereference $ Variable "x"
