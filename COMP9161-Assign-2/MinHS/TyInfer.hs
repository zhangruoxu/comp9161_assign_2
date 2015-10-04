module MinHS.TyInfer where

import qualified MinHS.Env as E
import MinHS.Syntax
import MinHS.Subst
import MinHS.TCMonad

import Data.Monoid (Monoid (..), (<>))
import Data.Foldable (foldMap)
import Data.List (nub, union, (\\))

primOpType :: Op -> QType
primOpType Gt   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Ge   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Lt   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Le   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Eq   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Ne   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Neg  = Ty $ Base Int `Arrow` Base Int
primOpType Fst  = Forall "a" $ Forall "b" $ Ty $ (TypeVar "a" `Prod` TypeVar "b") `Arrow` TypeVar "a"
primOpType Snd  = Forall "a" $ Forall "b" $ Ty $ (TypeVar "a" `Prod` TypeVar "b") `Arrow` TypeVar "b"
primOpType _    = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Int)

constType :: Id -> Maybe QType
constType "True"  = Just $ Ty $ Base Bool
constType "False" = Just $ Ty $ Base Bool
constType "()"    = Just $ Ty $ Base Unit
constType "Pair"  = Just
                  $ Forall "a"
                  $ Forall "b"
                  $ Ty
                  $ TypeVar "a" `Arrow` (TypeVar "b" `Arrow` (TypeVar "a" `Prod` TypeVar "b"))
constType "Inl"   = Just
                  $ Forall "a"
                  $ Forall "b"
                  $ Ty
                  $ TypeVar "a" `Arrow` (TypeVar "a" `Sum` TypeVar "b")
constType "Inr"   = Just
                  $ Forall "a"
                  $ Forall "b"
                  $ Ty
                  $ TypeVar "b" `Arrow` (TypeVar "a" `Sum` TypeVar "b")
constType _       = Nothing

-- augment original Env with type env?
type Gamma = E.Env QType

initialGamma :: Gamma
initialGamma = E.empty

-- type variable?
tv :: Type -> [Id]
tv = tv'
 where
   tv' (TypeVar x) = [x]
   tv' (Prod  a b) = tv a `union` tv b
   tv' (Sum   a b) = tv a `union` tv b
   tv' (Arrow a b) = tv a `union` tv b
   tv' (Base c   ) = []

-- QType quantifier type. for all blah 
tvQ :: QType -> [Id]
tvQ (Forall x t) = filter (/= x) $ tvQ t
tvQ (Ty t) = tv t

-- nub is a function. Remove duplicate elements from a list
tvGamma :: Gamma -> [Id]
tvGamma = nub . foldMap tvQ

infer :: Program -> Either TypeError Program
infer program = do (p',tau, s) <- runTC $ inferProgram initialGamma program
                   return p'

-- remove for all qualifier
unquantify :: QType -> TC Type
{-
Normally this implementation would be possible:

unquantify (Ty t) = return t
unquantify (Forall x t) = do x' <- fresh
                             unquantify (substQType (x =:x') t)

However as our "fresh" names are not checked for collisions with names bound in the type
we avoid capture entirely by first replacing each bound
variable with a guaranteed non-colliding variable with a numeric name,
and then substituting those numeric names for our normal fresh variables
-}

unquantify = unquantify' 0 emptySubst
unquantify' :: Int -> Subst -> QType -> TC Type
unquantify' i s (Ty t) = return $ substitute s t
unquantify' i s (Forall x t) = do x' <- fresh
                                  unquantify' (i + 1)
                                              ((show i =: x') <> s)
                                              (substQType (x =:TypeVar (show i)) t)

{-
unify function. Give two types and find a substitution which make them alike.
Subst is a monoid. =: is a binary operator defined over Subst. a =:b means substitute a with b. 
(=:) :: (Id -> Type -> Subst)
<> is infix synonym for mappend of monoid
-}
unify :: Type -> Type -> TC Subst
unify t@(TypeVar t1) (TypeVar t2) 
    | t1 == t2 = return emptySubst
    | otherwise = return (t2 =: t)
unify bt1@(Base t1) bt2@(Base t2)
    | t1 == t2 = return emptySubst
    | otherwise = typeError (TypeMismatch bt1 bt2)
unify (Prod t11 t12) (Prod t21 t22) = 
    do 
    subst1 <- unify t11 t21
    subst2 <- unify (substitute subst1 t21) (substitute subst1 t22)
    return (subst1 <> subst2)
unify (Sum t11 t12) (Sum t21 t22) = 
    do
    subst1 <- unify t11 t21
    subst2 <- unify (substitute subst1 t21) (substitute subst1 t22)
    return (subst1 <> subst2)
unify (Arrow t11 t12) (Arrow t21 t22) = 
    do
    subst1 <- unify t11 t21
    subst2 <- unify (substitute subst1 t21) (substitute subst1 t22)
    return (subst1 <> subst2)
unify (TypeVar id) t
    |id `notElem` tv t = return (id =: t)
    | otherwise = typeError (OccursCheckFailed id t)
unify t (TypeVar id)
    |id `notElem` tv t = return (id =: t)
    | otherwise = typeError (OccursCheckFailed id t)

generalise :: Gamma -> Type -> QType
generalise g t = error "implement me"

inferProgram :: Gamma -> Program -> TC (Program, Type, Subst)
inferProgram env bs = error "implement me! don't forget to run the result substitution on the"
                            "entire expression using allTypes from Syntax.hs"

inferExp :: Gamma -> Exp -> TC (Exp, Type, Subst)
inferExp gamma e@(Num _) = return (e, Base Int, emptySubst)
inferExp gamma (If e e1 e2) = 
    do
    (e', tau, t) <- inferExp gamma e
    u <- unify tau (Base Bool)
    (e1', tau1, t1) <- inferExp (substGamma u (substGamma  t gamma)) e1
    (e2', tau2, t2) <- inferExp (substGamma t1 (substGamma u (substGamma t gamma))) e2
    u' <- unify (substitute t2 tau1) tau2
    return ((If e' e1' e2'), substitute u' tau2, u' <> u <> t2 <> t1 <> t)
inferExp gamma (App e1 e2) = 
    do
    (e1', tau1, t) <- inferExp gamma e1
    (e2', tau2, t') <- inferExp (substGamma t gamma) e2
    alpha <- fresh
    u <- unify (substitute t' tau1) (Arrow tau2 alpha)
    return ((App e1' e2'), substitute u alpha, u <> t' <> t)
-- inferExp g _ = error "Implement me!"
-- -- Note: this is the only case you need to handle for case expressions
-- inferExp g (Case e [Alt "Inl" [x] e1, Alt "Inr" [y] e2])
-- inferExp g (Case e _) = typeError MalformedAlternatives


