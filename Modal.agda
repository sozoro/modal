module Modal where

-- Patrick Blackburn "Modal logic as dialogical logic" (2001)

open import Agda.Primitive
open import Agda.Builtin.Size

infixr  3 _⊎_
infixr  4 _×_
infixr  6 _,_

data ⊥ : Set where

record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

open Σ public

_×_ : ∀ {a b} (A : Set a) (B : Set b) → Set (a ⊔ b)
A × B = Σ A (λ _ → B)

record Thunk {ℓ} (F : Size → Set ℓ) (i : Size) : Set ℓ where
  coinductive
  field
    force : {j : Size< i} → F j

open Thunk public

module ProfaneModalLogic {ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level} (P : Set ℓ₁) where
  infix   5 _‖_⊩_ _‖_⊮_
  infixr 10 _⇒_
  infixl 11 _∧_ _∨_
  infix  12 □ ◇ ¬

  data PROP : Set ℓ₁ where
    <_> : P → PROP
    ¬   : PROP → PROP
    _∧_ : PROP → PROP → PROP
    _∨_ : PROP → PROP → PROP
    _⇒_ : PROP → PROP → PROP
    ◇   : PROP → PROP
    □   : PROP → PROP

  ℓ₅ : Level
  ℓ₅ = ℓ₁ ⊔ lsuc ℓ₂ ⊔ lsuc ℓ₃ ⊔ lsuc ℓ₄

  record Model : Set ℓ₅ where
    field
      W : Set ℓ₂
      R : W → W → Set ℓ₃
      V : PROP → W → Set ℓ₄
  open Model

  Frame : Set ℓ₅
  Frame = Σ Model W

  mutual

    _‖_⊮_ : Frame → Size → PROP → Set ℓ₅
    _‖_⊮_ f i p = Thunk (f ‖_⊩ p) i → ⊥

    {-# NO_POSITIVITY_CHECK #-}
    data _‖_⊩_ : Frame → Size → PROP → Set ℓ₅ where
      ⊩p  : ∀ {M w p i} → V M p w
                        -----------------
                        → M , w ‖ i ⊩ p

      ⊩¬  : ∀ {f φ i}   → f ‖ i ⊮ φ
                        ---------------
                        → f ‖ i ⊩ ¬ φ

      ⊩∧  : ∀ {f φ ψ i} → f ‖ i ⊩ φ → f ‖ i ⊩ ψ
                        -------------------------
                        → f ‖ i ⊩ φ ∧ ψ

      ⊩∨₁ : ∀ {f φ ψ i} → f ‖ i ⊩ φ
                        -----------------
                        → f ‖ i ⊩ φ ∨ ψ

      ⊩∨₂ : ∀ {f φ ψ i} → f ‖ i ⊩ ψ
                        -----------------
                        → f ‖ i ⊩ φ ∨ ψ

      ⊩⇒₁ : ∀ {f φ ψ i} → f ‖ i ⊮ φ
                        -----------------
                        → f ‖ i ⊩ φ ⇒ ψ

      ⊩⇒₂ : ∀ {f φ ψ i} → f ‖ i ⊩ ψ
                        -----------------
                        → f ‖ i ⊩ φ ⇒ ψ

      ⊩◇  : ∀ {M w φ i} → Σ (W M) (λ w' → R M w w' × M , w' ‖ i ⊩ φ)
                        ----------------------------------------------
                        → M , w ‖ i ⊩ ◇ φ

      ⊩□  : ∀ {M w φ i} → ((w' : W M) → R M w w' → M , w' ‖ i ⊩ φ)
                        --------------------------------------------
                        → M , w ‖ i ⊩ □ φ

    doubleNeg : ∀ {M w φ i} {j : Size< i} → (V M (¬ φ) w → ⊥)
                → ({k : Size< j} → M , w ‖ k ⊩ φ)
                -----------------------------------
                → M , w ‖ i ⊩ ¬ (¬ φ)
    doubleNeg {M} {w} {φ} {i} {j} con x = ⊩¬ (λ t → helper (force t))
      where
        helper : M , w ‖ j ⊩ ¬ φ → ⊥
        helper (⊩p v) = con v
        helper (⊩¬ f) = f record { force = x }

open ProfaneModalLogic ⊥ public
