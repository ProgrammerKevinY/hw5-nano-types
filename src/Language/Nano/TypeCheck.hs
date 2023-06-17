{-# LANGUAGE FlexibleInstances, OverloadedStrings, BangPatterns #-}

module Language.Nano.TypeCheck where

import Language.Nano.Types
import Language.Nano.Parser

import qualified Data.List as L
import           Text.Printf (printf)  
import           Control.Exception (throw)

--------------------------------------------------------------------------------
typeOfFile :: FilePath -> IO Type
typeOfFile f = parseFile f >>= typeOfExpr

typeOfString :: String -> IO Type
typeOfString s = typeOfExpr (parseString s)

typeOfExpr :: Expr -> IO Type
typeOfExpr e = do
  let (!st, t) = infer initInferState preludeTypes e
  if (length (stSub st)) < 0 then throw (Error ("count Negative: " ++ show (stCnt st)))
  else return t

--------------------------------------------------------------------------------
-- Problem 1: Warm-up
--------------------------------------------------------------------------------

-- | Things that have free type variables
class HasTVars a where
  freeTVars :: a -> [TVar]

-- | Type variables of a type
instance HasTVars Type where
  freeTVars TInt = []
  freeTVars TBool = []
  freeTVars (TVar t) = [t]
  freeTVars (TList t) = freeTVars t
  freeTVars (t1 :=> t2) = L.nub (freeTVars t1 ++ freeTVars t2) 

-- | Free type variables of a poly-type (remove forall-bound vars)
instance HasTVars Poly where
  freeTVars (Mono t) = freeTVars t
  freeTVars (Forall t s) = freeTVars s L.\\ [t]

-- | Free type variables of a type environment
instance HasTVars TypeEnv where
  freeTVars gamma   = concat [freeTVars s | (x, s) <- gamma]  
  
-- | Lookup a variable in the type environment  
lookupVarType :: Id -> TypeEnv -> Poly
lookupVarType x ((y, s) : gamma)
  | x == y    = s
  | otherwise = lookupVarType x gamma
lookupVarType x [] = throw (Error ("unbound variable: " ++ x))

-- | Extend the type environment with a new biding
extendTypeEnv :: Id -> Poly -> TypeEnv -> TypeEnv
extendTypeEnv x s gamma = (x,s) : gamma  

-- | Lookup a type variable in a substitution;
--   if not present, return the variable unchanged
lookupTVar :: TVar -> Subst -> Type
lookupTVar x [] = TVar x
lookupTVar x ((y, s) : gamma) | y == x    = s
                              | otherwise = lookupTVar x gamma

-- | Remove a type variable from a substitution
removeTVar :: TVar -> Subst -> Subst
removeTVar _ []                           = []
removeTVar x ((y, s) : gamma) | y == x    = removeTVar x gamma
                              | otherwise = ((y, s) : (removeTVar x gamma))
     
-- | Things to which type substitutions can be apply
class Substitutable a where
  apply :: Subst -> a -> a
  
-- | Apply substitution to type
instance Substitutable Type where  
  apply sub TInt        = TInt
  apply sub TBool       = TBool
  apply sub (TVar t)    = lookupTVar t sub
  apply sub (TList t)   = TList (apply sub t)
  apply sub (t1 :=> t2) = (apply sub t1 :=> apply sub t2)

-- | Apply substitution to poly-type
instance Substitutable Poly where    
  apply sub (Mono t)     = Mono (apply sub t)
  apply sub (Forall t s) = Forall t (apply sub s)

-- | Apply substitution to (all poly-types in) another substitution
instance Substitutable Subst where  
  apply sub to = zip keys $ map (apply sub) vals
    where
      (keys, vals) = unzip to
      
-- | Apply substitution to a type environment
instance Substitutable TypeEnv where  
  apply sub gamma = zip keys $ map (apply sub) vals
    where
      (keys, vals) = unzip gamma
      
-- | Extend substitution with a new type assignment
extendSubst :: Subst -> TVar -> Type -> Subst
extendSubst sub a TInt        = L.nub ((a, TInt):sub)
extendSubst sub a TBool       = L.nub ((a, TBool):sub)
extendSubst sub a (TVar t)    = L.nub ((a, lookupTVar t sub):sub)
extendSubst sub a (TList t)   = L.nub ((a, TList (apply sub t)):sub)
extendSubst sub a (t1 :=> t2) = L.nub ((a, apply sub t1 :=> apply sub t2):sub)
      
--------------------------------------------------------------------------------
-- Problem 2: Unification
--------------------------------------------------------------------------------
      
-- | State of the type inference algorithm      
data InferState = InferState { 
    stSub :: Subst -- ^ current substitution
  , stCnt :: Int   -- ^ number of fresh type variables generated so far
} deriving (Eq,Show)

-- | Initial state: empty substitution; 0 type variables
initInferState = InferState [] 0

-- | Fresh type variable number n
freshTV n = TVar $ "a" ++ show n      
    
-- | Extend the current substitution of a state with a new type assignment   
extendState :: InferState -> TVar -> Type -> InferState
extendState (InferState sub n) a t = InferState (extendSubst sub a t) n
        
-- | Unify a type variable with a type; 
--   if successful return an updated state, otherwise throw an error
unifyTVar :: InferState -> TVar -> Type -> InferState
unifyTVar st a t | a == (show t)            = st
                 | a `elem` (freeTVars t) = throw ( Error ( "type error: cannot unify " ++ a ++ " and " ++ show t) )
                 | otherwise              = extendState st a t 
    
-- | Unify two types;
--   if successful return an updated state, otherwise throw an error
unify :: InferState -> Type -> Type -> InferState
unify st (TVar t1) t2 | t1 `elem` (map fst (stSub st)) = st
                      | otherwise                      = unifyTVar st t1 t2
unify st t1 (TVar t2) | t2 `elem` (map fst (stSub st)) = st
                      | otherwise                      = unifyTVar st t2 t1
unify st (t1 :=> t3) (t2 :=> t4) = unify(unify(unify(unify st t1 t2)t2 t1)t3 t4)t4 t3 
unify st t1 t2 | t1 == t2  = st
               | otherwise = throw ( Error ( "type error: cannot unify " ++ show t1 ++ " and " ++ show t2 ))

--------------------------------------------------------------------------------
-- Problem 3: Type Inference
--------------------------------------------------------------------------------    
  
infer :: InferState -> TypeEnv -> Expr -> (InferState, Type)
infer st _   (EInt _)          = (st, TInt)
infer st _   (EBool _)         = (st, TBool)
infer st gamma (EVar x)        = case lookupVarType x gamma of
                                  (Mono t)        -> (st, t)
                                  (Forall a poly) -> (st', newType)
                                    where
                                      (newCount, newType) = instantiate (stCnt st) poly
                                      st'                 = InferState (stSub (extendState st a newType)) newCount
infer st gamma (ELam x body)  = (newInferState, ((freshTV ct) :=> bodyType))
  where
    (newInferState, bodyType) = infer (InferState sub (1 + ct)) extendedTypeEnv body
    extendedTypeEnv           = extendTypeEnv x (Mono (freshTV ct)) gamma
    ct                        = stCnt st
    sub                       = stSub st
infer st gamma (EApp e1 e2)   = (newState, newType)
  where
    newType                     = apply newSub e1Output
    newSub                      = stSub (newState)
    newState                    = unify st e1Input e2Type
    (_, (e1Input :=> e1Output)) = infer st gamma e1
    (_, e2Type)                 = infer st gamma e2
infer st gamma (ELet x e1 e2)  = (e2State, newType)
  where
    newType                    = apply newSub e2Type
    newSub                     = stSub (e2State)
    (e2State, e2Type)          = infer st extendedTypeEnv e2
    extendedTypeEnv            = extendTypeEnv x (Mono e1Type) gamma
    (_, e1Type)                = infer st gamma e1
infer st gamma (EBin op e1 e2) = infer st gamma asApp
  where
    asApp = EApp (EApp opVar e1) e2
    opVar = EVar (show op)
infer st gamma (EIf c e1 e2) = infer st gamma asApp
  where
    asApp = EApp (EApp (EApp ifVar c) e1) e2
    ifVar = EVar "if"    
infer st gamma ENil = infer st gamma (EVar "[]")

-- | Generalize type variables inside a type
generalize :: TypeEnv -> Type -> Poly
generalize gamma t = helper ((freeTVars t) L.\\ polytvar (map snd gamma))
  where
    helper []                     = Mono t
    helper (x:xs)                 = Forall x (helper xs)
    polytvar []                   = []
    polytvar ((Mono (TVar x)):xs) = x:(polytvar xs)
    polytvar _                    =  throw ( Error ( "Exhaustion!" ))
    
-- | Instantiate a polymorphic type into a mono-type with fresh type variables
instantiate :: Int -> Poly -> (Int, Type)
instantiate n (Mono x)           = (n, x)
instantiate n (Forall tvar poly) = instantiate (n + 1) capType
  where
    newSubst = extendSubst [] tvar (freshTV n)
    capType  = apply newSubst poly
      
-- | Types of built-in operators and functions      
preludeTypes :: TypeEnv
preludeTypes =
  [ ("+",    Mono $ TInt :=> TInt :=> TInt)
  , ("-",    Mono $ TInt :=> TInt :=> TInt)
  , ("*",    Mono $ TInt :=> TInt :=> TInt)
  , ("/",    Mono $ TInt :=> TInt :=> TInt)
  , ("==",   Forall "a" $ Mono ((TVar "a") :=> (TVar "a") :=> TBool))
  , ("!=",   Forall "a" $ Mono ((TVar "a") :=> (TVar "a") :=> TBool))
  , ("<",    Forall "a" $ Mono ((TVar "a") :=> (TVar "a") :=> TBool))
  , ("<=",   Forall "a" $ Mono ((TVar "a") :=> (TVar "a") :=> TBool))
  , ("&&",   Mono $ TBool :=> TBool :=> TBool)
  , ("||",   Mono $ TBool :=> TBool :=> TBool)
  , ("if",   Forall "a" $ Mono (TBool :=> (TVar "a") :=> (TVar "a") :=> (TVar "a")))
  -- lists: 
  , ("[]",   Forall "a" $ Mono ((TVar "a") :=> (TList (TVar "a"))))
  , (":",    Forall "a" $ Mono ((TVar "a") :=> (TList (TVar "a")) :=> (TList (TVar "a"))))
  , ("head", Forall "a" $ Mono ((TList (TVar "a")) :=> (TVar "a")))
  , ("tail", Forall "a" $ Mono ((TList (TVar "a")) :=> (TVar "a")))
  ]