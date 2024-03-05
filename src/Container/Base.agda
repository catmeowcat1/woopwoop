module Container.Base where

open import Level renaming (zero to ℓ0; suc to ℓsuc)
open import Data.Unit
open import Data.Product

open import Telescope.Base

record Container (ℓ ℓ′ : Level) (T : Tele′) : Set (ℓsuc ℓ ⊔ ℓsuc ℓ′ ⊔ levelₜ T) where
  field
    shape : Pshₜ T ℓ
    position : Pshₜ (con′ T shape) ℓ′
    next : Famₜ (con′ (con′ T shape) position) (Σₜ′ T)
open Container public


_⇒ₚ_ : ∀ {ℓ ℓ′} {T : Tele′} → Pshₜ T ℓ → Pshₜ T ℓ′ → Set (ℓ ⊔ ℓ′ ⊔ levelₜ T)
_⇒ₚ_ {T = T} X Y = Πₜ T (λ _ t → X $ₜ t → Y $ₜ t) tt

module _ {ℓ ℓ′} {T : Tele′} where

  ⟦_⟧c : ∀ {ℓ″} (C : Container ℓ ℓ′ T) → Pshₜ T ℓ″ → Pshₜ T (ℓ ⊔ ℓ′ ⊔ ℓ″)
  ⟦ C ⟧c X = curryₜ {T = T} λ t →
    Σ[ s ∈ shape C $ₜ t ] ((p : (position C $ₜ t) s) → X $ₜ ((next C $ₜ t) s p))

  c-sh : ∀ {ℓ″} {C : Container ℓ ℓ′ T} {X : Pshₜ T ℓ″} → Πₜ T (λ _ t → ⟦ C ⟧c X $ₜ t → shape C $ₜ t) tt
  c-sh = curryₜ {T = T} λ t x → {!!}

  --⟦_⟧[_]c : ∀ {ℓ″ ℓ‴} (C : Container ℓ ℓ′ T) {X : Pshₜ T ℓ″} {Y : Pshₜ T ℓ‴} → _⇒ₚ_ {T = T} X Y → _⇒ₚ_ {T = T} (⟦ C ⟧c X) (⟦ C ⟧c Y)
  --⟦ C ⟧[ f ]c = curryₜ {T = T} λ where t → {!!}