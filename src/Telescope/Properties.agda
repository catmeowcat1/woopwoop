{-# OPTIONS --allow-unsolved-metas --cubical #-}
module Telescope.Properties where

open import Cubical.Foundations.Prelude
open import Data.Product hiding (Σ-syntax)
--open import Data.Product.Properties using (Σ-≡,≡↔≡)
open import Function.Bundles
--open import Relation.Binary.PropositionalEquality

open import Telescope.Base

module _ {ℓᵢ} {I : Set ℓᵢ} where

  +ₜ-inj : ∀ {T U} {i : I} (x : Σₜ T i) → Σₜ U (i , x) → Σₜ (T +ₜ U) i
  +ₜ-inj-proj₁ : ∀ {T U i} (x : Σₜ T i) (y : Σₜ U (i , x)) → x ≡ +ₜ-proj₁ (+ₜ-inj x y)
  +ₜ-inj-proj₂ : ∀ {T U i} (x : Σₜ T i) (y : Σₜ U (i , x)) → PathP (λ i → Σₜ U (_ , +ₜ-inj-proj₁ x y i)) y (+ₜ-proj₂ (+ₜ-inj x y))

  +ₜ-inj-proj : ∀ {T U i} (p : Σ[ x ∈ Σₜ T i ] (Σₜ U (i , x))) → p ≡ (+ₜ-proj₁ (uncurry +ₜ-inj p) , +ₜ-proj₂ (uncurry +ₜ-inj p))
  +ₜ-inj-proj (x , y) i = +ₜ-inj-proj₁ x y i , +ₜ-inj-proj₂ x y i

  +ₜ-inj {U = nil}     x y       = x
  +ₜ-inj {U = con _ A} x (y , a) .proj₁ = +ₜ-inj x y
  +ₜ-inj {U = con _ A} x (y , a) .proj₂ = 
    subst (λ u → A _ (proj₂ u)) (+ₜ-inj-proj (x , y)) a

  +ₜ-inj-proj₁ {U = nil}     x y       = refl
  +ₜ-inj-proj₁ {U = con _ A} x (y , a) = +ₜ-inj-proj₁ x y

  +ₜ-inj-proj₂ {U = nil}     x tt        = refl
  +ₜ-inj-proj₂ {U = con _ A} x (y , a) i .proj₁ = +ₜ-inj-proj₂ x y i
  +ₜ-inj-proj₂ {U = con _ A} x (y , a) i .proj₂ =
    subst-filler (λ u → A _ (proj₂ u)) (+ₜ-inj-proj (x , y)) a i

  ⊆-refl : {T : Tele I} → T ⊆ T
  Σ⊆-refl : {T : Tele I} (i : I) (t : Σₜ T i) → t ≡ Σ⊇ (⊆-refl {T}) i t

  ⊆-refl {nil}     = bot
  ⊆-refl {con T A} = keep (⊆-refl {T}) {!!} --λ i t → cong (A i) (Σ⊆-refl i t)

  Σ⊆-refl {nil}     i tt = refl
  Σ⊆-refl {con T A} i (t , a) = {!!} --Σ-≡,≡↔≡ .Inverse.f (Σ⊆-refl i t , subst-∘ (Σ⊆-refl i t))

  nil-initial : {T : Tele I} → nil ⊆ T
  nil-initial {nil}     = bot
  nil-initial {con T A} = skip nil-initial