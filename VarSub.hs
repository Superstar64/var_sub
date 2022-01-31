{-# LANGUAGE NoMonomorphismRestriction #-}

module VarSub where

import Control.Monad.IO.Class
import Control.Monad.Trans.State.Strict
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Traversable (for)

infix 6 :=

infix 6 :<=

data FlexibleState = FlexibleState {upperBounds :: [Type], lowerRigidBounds :: [String]} deriving (Show)

data RigidState = RigidState {upperRigidBounds :: [String]} deriving (Show)

data Context = Context
  { problems :: [Equation],
    flexible :: Map String FlexibleState,
    rigid :: Map String RigidState,
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

searchFlexible :: Monad m => String -> StateT Context m FlexibleState
searchFlexible x = Map.findWithDefault (FlexibleState [] []) x <$> flexible <$> get

searchRigid :: Monad m => String -> StateT Context m RigidState
searchRigid x = Map.findWithDefault (RigidState []) x <$> rigid <$> get

rigidSubType :: Monad m => String -> [Char] -> StateT Context m Bool
rigidSubType x y | x == y = pure True
rigidSubType x y = do
  RigidState children <- searchRigid x
  or <$> for children (\x -> rigidSubType x y)

reachFlexible :: Monad m => Type -> String -> StateT Context m Bool
reachFlexible (Flexible x) x' | x == x' = pure True
reachFlexible (Flexible x) x' = do
  FlexibleState children _ <- searchFlexible x
  or <$> for children (\e -> reachFlexible e x')
reachFlexible _ _ = pure False

modifyProblems :: Monad m => ([Equation] -> [Equation]) -> StateT Context m ()
modifyProblems f = modify $ \context -> context {problems = f $ problems context}

modifyFlexible :: Monad m => (Map String FlexibleState -> Map String FlexibleState) -> StateT Context m ()
modifyFlexible f = modify $ \context -> context {flexible = f $ flexible context}

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
      FlexibleState upper lower <- searchFlexible x
      let upper' = e : upper
      modifyFlexible (Map.insert x (FlexibleState upper' lower))
      for lower $ \x' -> subtype (Rigid x') e
      pure ()
constrain (Rigid x) (Flexible x') = do
  FlexibleState upper lower <- searchFlexible x'
  let lower' = x : lower
  modifyFlexible (Map.insert x' (FlexibleState upper lower'))
  for upper $ \e -> subtype (Rigid x) e
  pure ()
constrain (Rigid x) (Rigid x') = do
  True <- rigidSubType x x'
  pure ()
constrain _ _ = fail "can only constrain variables"

-- todo occurance check
unify :: MonadFail m => Type -> Type -> StateT Context m ()
unify (Flexible x) (Flexible x') | x == x' = pure ()
unify (Flexible x) e = do
  FlexibleState upper lower <- searchFlexible x
  for upper $ \e' -> subtype e e'
  for lower $ \x' -> subtype (Rigid x') e
  modifyProblems (substitute e x)
  -- if a cycle forms then it must contain `e`
  modifyFlexible (substitute e x . Map.delete x)
  -- so if the right handside is a variable
  -- then reunify it's constraints
  case e of
    Flexible x -> do
      FlexibleState upper lower <- searchFlexible x
      for upper $ \e -> subtype (Flexible x) e
      for lower $ \x' -> subtype (Rigid x') (Flexible x)
      modifyFlexible (Map.delete x)
    _ -> pure ()
  modify $ \state -> state {answers = (x, e) : answers state}
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

runWithRaw :: (MonadIO m, MonadFail m) => Map String RigidState -> [Equation] -> m Context
runWithRaw rigid problems = execStateT solve (Context problems mempty rigid 0 Map.empty [])

runRaw :: (MonadIO m, MonadFail m) => [Equation] -> m Context
runRaw = runWithRaw mempty

sampleRaw1 =
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

sampleRaw2 = [Flexible "a" := Rigid "a", Flexible "b" := Rigid "b", Flexible "a" :<= Flexible "b"]

sampleRaw2' = [Flexible "a" :<= Flexible "b", Flexible "a" := Rigid "a", Flexible "b" := Rigid "b"]

rigidSample = Map.singleton "a" $ RigidState ["b"]

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

runWith :: (MonadFail m, MonadIO m) => Map String RigidState -> Term -> m ((Type, Type), Context)
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
    Annotate
      (Flexible "c")
      (Rigid "b")
      $ Dereference $ Variable "x"

sample4 =
  Lambda "f" $
    Lambda "x" $
      Lambda "y" $
        Application
          (Application (Variable "f") (Dereference $ Variable "x"))
          (Dereference $ Variable "y")

sample5 =
  Lambda "f" $
    Lambda "g" $
      Lambda "x" $
        Lambda "y" $
          Application
            ( Application
                (Variable "f")
                (Application (Variable "g") $ Dereference $ Variable "x")
            )
            (Application (Variable "g") $ Dereference $ Variable "y")

sample6 =
  Lambda "f" $
    Lambda "g" $
      Lambda "x" $
        Lambda "y" $
          Application
            ( Application
                (Variable "f")
                (Dereference $ Application (Variable "g") $ Variable "x")
            )
            (Dereference $ Application (Variable "g") $ Variable "y")
