module CCX where

open import Data.List
open import Data.Product
open import Level
open import Relation.Binary.Core
open import Relation.Unary

open import TheorySignature

open Theory

KnownTerms : Theory → Set'
KnownTerms t = (Term (Symbol t)) → Set

Users : Theory → Set'
Users t = Value t → Term (Symbol t) → Set

Reps : Theory → Set
Reps t = Value t → Value t

data Equation (t : Theory) : Set where
  query : Term (Symbol t) → Term (Symbol t) → Equation t
  eq : Term (Symbol t) → Term (Symbol t) → Equation t

data _<-_ {t : Theory} : Term (Symbol t) -> Equation t -> Set where
  queryl : ∀ {tm tm'} → tm <- (query tm tm')
  queryr : ∀ {tm tm'} → tm <- (query tm' tm)
  eql : ∀ {tm tm'} → tm <- (eq tm tm')
  eqr : ∀ {tm tm'} → tm <- (eq tm' tm)

Equations : Theory → Set
Equations t = List (Equation t)

Configuration : Theory → Set'
Configuration t = KnownTerms t × Users t × Reps t × Equations t

rep-subst : (t : Theory) → Reps t → (Value t × Value t) → Reps t
rep-subst t Δ s = (λ r → subst t s (Δ r))

user-subst : (t : Theory) → Users t → (Value t × Value t) → Users t
user-subst t Γ (p , P) = (λ l → Γ l ∪ Γ p) -- TODO: leaves P

singleton : ∀ {A} → A → A → Set
singleton x = (λ y → y ≡ x)

data CongruenceClosure (t : Theory) :
     Configuration t → Configuration t → Set' where

  congr  : ∀ {p P a b Θ Γ Δ Φ Γ' Δ' Φ'} →
           a ∈ Θ →
           b ∈ Θ →
           Δ (make t a) ≢ Δ (make t b) →
           (p , P) ≡ solve t (Δ (make t a)) (Δ (make t b)) →
           -- TODO: define Γ'
           Δ' ≡ rep-subst t Δ (p , P) →
           -- TODO: define Φ'
           -----------------------------
           CongruenceClosure t
           ( Θ , Γ , Δ , ( (eq a b) ∷ Φ ) )
           ( Θ , Γ' , Δ' , Φ' ++ Φ )

  remove : ∀ {a b Θ Γ Δ Φ} →
           a ∈ Θ →
           b ∈ Θ →
           Δ (make t a) ≡ Δ (make t b) →
           -------------------------------
           CongruenceClosure t
           ( Θ , Γ , Δ , ( (eq a b) ∷ Φ ) )
           ( Θ , Γ , Δ , Φ )

  add    : ∀ {f as e Θ Γ Δ Φ Θ' Γ' Φ'} →
           (app f as <- e) →
           -- as ⊆ Θ →
           -- TODO: define Θ'
           -- TODO: define Γ'
           -- TODO: define Φ'
           Θ' ≡ Θ ∪ singleton (app f as) →
           -----------------------------
           CongruenceClosure t
           ( Θ , Γ , Δ , ( e ∷ Φ ) )
           ( Θ' , Γ' , Δ , Φ' ++ ( e ∷ Φ ) )

  query  : ∀ {a b Θ Γ Δ Φ} →
           a ∈ Θ →
           b ∈ Θ →
           Δ (make t a) ≡ Δ (make t b) →
           -------------------------------
           CongruenceClosure t
           ( Θ , Γ , Δ , ( (query a b) ∷ Φ ) )
           ( Θ , Γ , Δ , Φ )
