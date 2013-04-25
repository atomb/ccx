module TheorySignature where

open import Data.List
open import Data.Product
open import Level
open import Relation.Binary.Core

data Term (symbol : Set) : Set where
  app : symbol → List (Term symbol) → Term symbol

-- Not needed: purity is defined by leaf-of.
{-
data pure {symbol : Set} : Term symbol → Set where
  pure-app : ∀ {s} → pure (app s []) 
-}

iter : {v : Set}
     → ((v × v) → v → v) → (v → v → (v × v))
     → List (v × v) → v → v
iter subst solve [] r = r
iter subst solve ((r1 , r2) ∷ S) r3 =
  subst (solve (go r1) (go r2)) (go r3)
    where go = iter subst solve S

Set' : Set (suc (suc zero))
Set' = Set (suc zero)

record Theory : Set' where
  field
    -- The underlying theory
    Symbol : Set
    Value : Set
    equal : Term Symbol → Term Symbol → Set

    -- The properties necessary for CC(X)
    make : Term Symbol → Value
    one : Value
    leaf-of : Value → Value → Set
    subst : (Value × Value) → Value → Value
    solve : Value → Value → Value × Value

    -- The equality judgement
    judge-eq : List (Value × Value) → Value → Value → Set

    -- The axioms that the above fields must satisfy
    solve-subst       : ∀ {r1 r2}
                      → subst (solve r1 r2) r1 ≡ subst (solve r1 r2) r2
    -- meaning-eq
    judge-eq-iter     : ∀ {S r}
                      → judge-eq S (iter subst solve S r) r
    composite-leaves1 : ∀ {r p P}
                      → r ≢ subst (p , P) r
                      → leaf-of p r
    composite-leaves2 : ∀ {r p P p'}
                      → r ≢ subst (p , P) r
                      → leaf-of p' P
                      → leaf-of p' r
    composite-leaves3 : ∀ {r p P p'}
                      → r ≢ subst (p , P) r
                      → leaf-of p' r
                      → p' ≢ p 
                      → leaf-of p' (subst (p , P) r)

    -- The following isn't needed if "pure" is just defined to be the
    -- term used for the case where the set of leaves is {one}.
    {-
    pure-leaves1      : ∀ {t p}
                      → pure t
                      → leaf-of p (make t)
                      → p ≡ one
    pure-leaves2      : ∀ {t}
                      → pure t
                      → leaf-of one (make t)
    -}
