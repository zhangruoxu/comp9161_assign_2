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

-- get type variable from a type expression?
tv :: Type -> [Id]
tv = tv'
 where
   tv' (TypeVar x) = [x]
   tv' (Prod  a b) = tv a `union` tv b
   tv' (Sum   a b) = tv a `union` tv b
   tv' (Arrow a b) = tv a `union` tv b
   tv' (Base c   ) = []

-- QType type with quantifier
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
    subst2 <- unify (substitute subst1 t12) (substitute subst1 t22)
    return (subst1 <> subst2)
unify (Sum t11 t12) (Sum t21 t22) = 
    do
    subst1 <- unify t11 t21
    subst2 <- unify (substitute subst1 t12) (substitute subst1 t22)
    return (subst1 <> subst2)
unify (Arrow t11 t12) (Arrow t21 t22) = 
    do
    subst1 <- unify t11 t21
    subst2 <- unify (substitute subst1 t12) (substitute subst1 t22)
    return (subst1 <> subst2)
unify (TypeVar id) t
    |id `notElem` tv t = return (id =: t)
    | otherwise = typeError (OccursCheckFailed id t)
unify t (TypeVar id)
    |id `notElem` tv t = return (id =: t)
    | otherwise = typeError (OccursCheckFailed id t)
unify t1 t2 = typeError (TypeMismatch t1 t2)

generalise :: Gamma -> Type -> QType
generalise gamma tau = gen (tv tau \\ tvGamma gamma) tau
--generalise g t = error "implement me"

gen :: [Id] -> Type -> QType
gen [] tau = Ty tau
gen (id : ids) tau = Forall id (gen ids tau)

inferProgram :: Gamma -> Program -> TC (Program, Type, Subst)
inferProgram env bs = 
    do
    (e', tau, t) <- inferExp env (Let bs (Var "main"))
    let (Let bs' var) = allTypes (substQType t) e' in
        return (bs', tau, t)
-- inferProgram env bs = error "implement me! don't forget to run the result substitution on the"
--                            "entire expression using allTypes from Syntax.hs"

inferExp :: Gamma -> Exp -> TC (Exp, Type, Subst)
inferExp gamma e@(Num _) = return (e, Base Int, emptySubst)

inferExp gamma v@(Var id)
    | Just qt <- E.lookup gamma id = -- find id type from environment. And use fresh variable to unquantify the type
        do
        t <- unquantify qt
        return (Var id, t, emptySubst)
    | otherwise = error $ "error in Var " ++ show v
    
inferExp gamma v@(Con c)
    | Just qt <- constType c = -- Type for type constructor. Use fresh variable to unquantify them.
        do
        t <- unquantify qt
        return (Con c , t, emptySubst)
    | otherwise = error $ "error in Con " ++ show v
    
inferExp gamma (Prim op) = 
    do 
    t <- unquantify $ primOpType op -- Type for primitive operator. Use fresh variable to unquantify them.
    return (Prim op, t, emptySubst)
    
inferExp gamma (If e e1 e2) = 
    do
    (e', tau, t) <- inferExp gamma e -- Type of this expression must be boolean
    u <- unify tau (Base Bool) -- If unification cannot be found, e is not a boolean expression
    (e1', tau1, t1) <- inferExp (substGamma u (substGamma  t gamma)) e1
    (e2', tau2, t2) <- inferExp (substGamma t1 (substGamma u (substGamma t gamma))) e2
    u' <- unify (substitute t2 tau1) tau2
    return ((If e' e1' e2'), substitute u' tau2, u' <> t2 <> t1 <> u <> t)
    
inferExp gamma (App e1 e2) = 
    do
    (e1', tau1, t) <- inferExp gamma e1 -- e1 is a function, maybe a polymorphic function, which means its type contains type variables.
    (e2', tau2, t') <- inferExp (substGamma t gamma) e2 --e2 is parameter. If e1 is a polymorphic function, because of the type of e2, now it is not polymorphic
    alpha <- fresh
    u <- unify (substitute t' tau1) (Arrow tau2 alpha) -- t' contains de-polymorphism information. alpha represents return type
    return ((App e1' e2'), substitute u alpha, u <> t' <> t)
    
inferExp gamma (Case e [(Alt "Inl" [x] e1), (Alt "Inr" [y] e2)]) = 
    do
    (e', tau, t) <- inferExp gamma e
    alpha_l <- fresh
    (e1', tau_l, t1) <- inferExp (substGamma t (E.add gamma (x, Ty alpha_l))) e1
    alpha_r <- fresh
    (e2', tau_r, t2) <- inferExp (substGamma t1 (substGamma t (E.add gamma (y, Ty alpha_r)))) e2
    u <- unify (substitute t2 (substitute t1 (substitute t (Sum alpha_l alpha_r)))) (substitute t1 tau)
    u'<- unify (substitute t2 (substitute t1 tau_l)) (substitute u tau_r)
    return ((Case e' [(Alt "Inl" [x] e1'), (Alt "Inr" [y] e2')]), substitute u' (substitute u tau_r), u' <> u <> t2 <> t1 <> t)
inferExp g (Case e _) = typeError MalformedAlternatives

inferExp gamma (Letfun (Bind f _ [x] e)) = 
    do
    alpha1 <- fresh
    alpha2 <- fresh
    (e', tau, t) <- inferExp (E.add (E.add gamma (x, Ty alpha1)) (f, Ty alpha2)) e-- introduce fresh variables to represent argument type and function type
    u <- unify (substitute t alpha2) (Arrow (substitute t alpha1) tau)
    let qt = substitute u (Arrow(substitute t alpha1) tau) in
        return ((Letfun (Bind f (Just (Ty qt)) [x] e')), qt, u <> t) -- add function type
            
inferExp gamma (Let [Bind x ty ids e1] e2) = 
    do
    (e1', tau, t) <- inferExp gamma e1
    let qt = (generalise (substGamma t gamma) tau)
    (e2', tau', t') <- inferExp (E.add (substGamma t gamma) (x, qt)) e2
    return (Let [Bind x (Just qt) ids e1'] e2', tau', t' <> t)
inferExp g p = error $ show "non-exhaustive pattern in inferExp"
-- -- Note: this is the only case you need to handle for case expressions
-- inferExp g (Case e [Alt "Inl" [x] e1, Alt "Inr" [y] e2])
-- inferExp g (Case e _) = typeError MalformedAlternatives


