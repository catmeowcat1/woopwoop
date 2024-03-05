-- {-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --without-K --safe #-}
module Telescope.Base where

open import Data.Product
open import Data.Product.Properties using (Σ-≡,≡↔≡)
open import Data.Unit
open import Data.Nat hiding (_⊔_)
open import Data.Fin hiding (lift)
open import Function.Bundles
open import Level hiding (lift) renaming (zero to ℓ0; suc to ℓsuc)
open import Relation.Binary.PropositionalEquality

data Teleᵢ {ℓ} (I : Set ℓ) : Setω
levelₜ : ∀ {ℓ} {I : Set ℓ} → Teleᵢ I → Level
Σₜ : ∀ {ℓ} {I : Set ℓ} (T : Teleᵢ I) → I → Set (levelₜ T)

data Teleᵢ I where
  nil : Teleᵢ I
  con : ∀ {ℓ} (T : Teleᵢ I) (A : ∀ i → Σₜ T i → Set ℓ) → Teleᵢ I

levelₜ nil           = 0ℓ
levelₜ (con {ℓ} T A) = levelₜ T ⊔ ℓ

Σₜ nil       i = ⊤
Σₜ (con T A) i = Σ (Σₜ T i) (A i)

data _⊆_ {ℓ} {I : Set ℓ} : Teleᵢ I → Teleᵢ I → Setω
Σ⊇ : ∀ {ℓ} {I : Set ℓ} {T U : Teleᵢ I} → T ⊆ U → ∀ i → Σₜ U i → Σₜ T i

data _⊆_ {ℓ} {I} where
  bot : nil ⊆ nil
  keep : ∀ {ℓ′} {T U} {A : ∀ i → Σₜ T i → Set ℓ′} {B : ∀ i → Σₜ U i → Set ℓ′} (e : T ⊆ U) → (∀ i u → B i u ≡ A i (Σ⊇ e i u)) → con T A ⊆ con U B
  skip : ∀ {ℓ′} {T U} {A : ∀ i → Σₜ U i → Set ℓ′} (e : T ⊆ U) → T ⊆ con U A

Σ⊇ bot        i u       = tt
Σ⊇ (keep e h) i (u , a) = Σ⊇ e i u , subst (λ X → X) (h i u) a
Σ⊇ (skip e)   i (u , a) = Σ⊇ e i u

module _ {ℓᵢ} {I : Set ℓᵢ} where

  -- Πₜ constructs an n-ary dependent function over a Teleᵢscope
  Πₜ : ∀ {ℓ} (T : Teleᵢ I) → (∀ i → Σₜ T i → Set ℓ) → I → Set (levelₜ T ⊔ ℓ)
  Πₜ nil       F i = F i tt
  Πₜ (con T A) F i = Πₜ T (λ i t → (a : A i t) → F i (t , a)) i

  Σₜ-right : (T : Teleᵢ I) → I → Set (levelₜ T)
  Σₜ-right T i = aux T λ _ _ → ⊤
    where aux : ∀ {ℓ} (T : Teleᵢ I) → (∀ i → Σₜ T i → Set ℓ) → Set (levelₜ T ⊔ ℓ)
          aux nil       F = F i tt
          aux (con T A) F = aux T λ i t → Σ (A i t) λ a → F i (t , a)

  infixr 1 _$ₜ_
  _$ₜ_ : ∀ {ℓ} {T : Teleᵢ I} {X : ∀ i → Σₜ T i → Set ℓ} {i} → Πₜ T X i → (t : Σₜ T i) → X i t
  _$ₜ_ {T = nil}     f tt      = f
  _$ₜ_ {T = con T _} f (t , a) = (f $ₜ t) a

  curryₜ : ∀ {ℓ} {T : Teleᵢ I} {X : ∀ i → Σₜ T i → Set ℓ} {i} → ((t : Σₜ T i) → X i t) → Πₜ T X i
  curryₜ {T = nil}     f = f tt
  curryₜ {T = con T _} f = curryₜ {T = T} λ t a → f (t , a)

  _+ₜ_ : (T : Teleᵢ I) → Teleᵢ (Σ I (Σₜ T)) → Teleᵢ I
  +ₜ-proj₁ : ∀ {T U i} → Σₜ (T +ₜ U) i → Σₜ T i
  +ₜ-proj₂ : ∀ {T U i} (x : Σₜ (T +ₜ U) i) → Σₜ U (i , +ₜ-proj₁ x)

  T +ₜ nil     = T
  T +ₜ con U A = con (T +ₜ U) λ i x → A (i , +ₜ-proj₁ x) (+ₜ-proj₂ x)

  +ₜ-proj₁ {U = nil}     x       = x
  +ₜ-proj₁ {U = con U A} (x , a) = +ₜ-proj₁ x

  +ₜ-proj₂ {U = nil}     x       = tt
  +ₜ-proj₂ {U = con U A} (x , a) = +ₜ-proj₂ x , a

  lengthₜ : Teleᵢ I → ℕ
  lengthₜ nil       = zero
  lengthₜ (con T A) = suc (lengthₜ T)

  prefixₜ : (T : Teleᵢ I) → Fin (lengthₜ T) → Teleᵢ I
  prefixₜ (con T A) zero    = T
  prefixₜ (con T A) (suc n) = prefixₜ T n

  getₜ-ℓ : (T : Teleᵢ I) → Fin (lengthₜ T) → Level
  getₜ-ℓ (con {ℓ} T A) zero     = ℓ
  getₜ-ℓ (con T A)     (suc n)  = getₜ-ℓ T n

  getₜ-A : (T : Teleᵢ  I) (n : Fin (lengthₜ T)) (i : I) → Σₜ (prefixₜ T n) i → Set (getₜ-ℓ T n)
  getₜ-A (con T A) zero    i = A i
  getₜ-A (con T A) (suc n) i = getₜ-A T n i

  getₜ : (T : Teleᵢ  I) (n : Fin (lengthₜ T)) → Teleᵢ I
  getₜ T n = con (prefixₜ T n) (getₜ-A T n)
  
  suffixₜ : (T : Teleᵢ  I) (n : Fin (lengthₜ T)) → Teleᵢ (Σ I (Σₜ (getₜ T n)))
  splitₜ-inj : ∀ {T n} i (p : Σₜ (getₜ T n) i) → Σₜ (suffixₜ T n) (i , p) → Σₜ T i

  suffixₜ (con T A) zero    = nil
  suffixₜ (con T A) (suc n) = con (suffixₜ T n) λ where (i , p) s → A i (splitₜ-inj i p s)

  splitₜ-inj {con _ _} {zero}  i p x       = p
  splitₜ-inj {con _ _} {suc n} i p (s , a) = splitₜ-inj i p s , a

Tele : Setω
Tele = Teleᵢ ⊤

Σₜ′ : (T : Tele) → Set (levelₜ T) 
Σₜ′ T = Σₜ T tt

Famₜ : ∀ {ℓ} (T : Tele) (X : Set ℓ) → Set (levelₜ T ⊔ ℓ)
Famₜ T X = Πₜ T (λ _ _ → X) tt

Pshₜ : (T : Tele) (ℓ : Level) → Set (levelₜ T ⊔ ℓsuc ℓ)
Pshₜ T ℓ = Famₜ T (Set ℓ)

Πₜ′ : ∀ {ℓ} (T : Tele) → Pshₜ T ℓ → Set (levelₜ T ⊔ ℓ)
Πₜ′ T F =  Πₜ T (λ _ → F $ₜ_) tt

con′ : ∀ {ℓ} (T : Tele) → Pshₜ T ℓ → Tele
con′ T X = con T λ _ → X $ₜ_