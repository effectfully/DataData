module DataData.Container.Core where

open import DataData.Prelude
open import DataData.Structures

infixr 0 _◃_

record Container α β : Set (lsuc (α ⊔ β)) where
  constructor _◃_
  field
    Shape    : Set α
    Position : Shape -> Set β
open Container public

⟦_⟧ᶜ : ∀ {α β γ} -> Container α β -> Set γ -> Set (α ⊔ β ⊔ γ)
⟦ Sh ◃ Pos ⟧ᶜ A = ∃ λ sh -> Pos sh -> A

Kᶜ : ∀ {α β} -> Set α -> Container α β
Kᶜ A = A ◃ const (Lift ⊥)

Iᶜ : ∀ {α β} -> Container α β
Iᶜ = Lift ⊤ ◃ const (Lift ⊤)

_⊎ᶜ_ : ∀ {α₁ α₂ β} -> Container α₁ β -> Container α₂ β -> Container (α₁ ⊔ α₂) β
(Sh₁ ◃ Pos₁) ⊎ᶜ (Sh₂ ◃ Pos₂) = Sh₁ ⊎ Sh₂ ◃ [ Pos₁ , Pos₂ ]

_×ᶜ_ : ∀ {α₁ α₂ β} -> Container α₁ β -> Container α₂ β -> Container (α₁ ⊔ α₂) β
(Sh₁ ◃ Pos₁) ×ᶜ (Sh₂ ◃ Pos₂) = Sh₁ × Sh₂ ◃ Pos₁ [> _⊎_ <] Pos₂

Σᶜ : ∀ {α β γ} -> (A : Set α) -> (A -> Container β γ) -> Container (α ⊔ β) γ
Σᶜ A F = ∃ (Shape ∘ F) ◃ uncurry (Position ∘ F)

∃ᶜ : ∀ {α β γ} {A : Set α} -> (A -> Container β γ) -> Container (α ⊔ β) γ
∃ᶜ = Σᶜ _

Πᶜ : ∀ {α β γ} -> (A : Set α) -> (A -> Container β γ) -> Container (α ⊔ β) (α ⊔ γ)
Πᶜ A F = (∀ x -> Shape (F x)) ◃ λ shape -> ∃ (Position (F _) ∘ shape)

_->ᶜ_ : ∀ {α β γ} -> Set α -> Container β γ -> Container (α ⊔ β) (α ⊔ γ)
A ->ᶜ C = Πᶜ A λ _ -> C

_∘ᶜ_ : ∀ {α₁ α₂ β₁ β₂} -> Container α₂ β₂ -> Container α₁ β₁ -> Container (α₁ ⊔ α₂ ⊔ β₂) (β₁ ⊔ β₂)
(Sh₂ ◃ Pos₂) ∘ᶜ C₁ = ∃ᶜ λ sh₂ -> Pos₂ sh₂ ->ᶜ C₁

instance
  Container-Functor : ∀ {α β γ} {C : Container α β} -> Functor {γ} ⟦ C ⟧ᶜ
  Container-Functor = record { _⟨$⟩_ = λ f -> second (f ∘_) }

  Container-VerifiedFunctor : ∀ {α β γ} {C : Container α β} -> VerifiedFunctor {γ} ⟦ C ⟧ᶜ
  Container-VerifiedFunctor = record
    { fmap-id = λ _ -> refl
    ; fmap-∘  = λ _ -> refl
    }

_∸>ᶜ_ : ∀ {α₁ α₂ β₁ β₂} -> Container α₁ β₁ -> Container α₂ β₂ -> Set (α₁ ⊔ α₂ ⊔ β₁ ⊔ β₂)
(Sh₁ ◃ Pos₁) ∸>ᶜ (Sh₂ ◃ Pos₂) = Σ (Sh₁ -> Sh₂) λ shape₂ -> ∀ sh₁ -> Pos₂ (shape₂ sh₁) -> Pos₁ sh₁

morphᶜ : ∀ {α₁ α₂ β₁ β₂} {C₁ : Container α₁ β₁} {C₂ : Container α₂ β₂}
       -> ⟦ C₁ ⟧ᶜ ∸> ⟦ C₂ ⟧ᶜ -> C₁ ∸>ᶜ C₂
morphᶜ η = proj₁ ∘ η ∘ (_, id) , proj₂ ∘ η ∘ (_, id)

-- (⟦ C₁ ⟧ᶜ A) contains `A', so to construct (⟦ C₂ ⟧ᶜ A) we need to "map back",
-- hence the contravariance in the definition of _∸>ᶜ_.
unmorphᶜ : ∀ {α₁ α₂ β₁ β₂ γ} {C₁ : Container α₁ β₁} {C₂ : Container α₂ β₂}
         -> C₁ ∸>ᶜ C₂ -> ⟦ C₁ ⟧ᶜ ∸> ⟦ C₂ ⟧ᶜ
unmorphᶜ {γ = γ} (shape₂ , position₁) {A} (sh₁ , pos₁) = shape₂ sh₁ , pos₁ ∘ position₁ sh₁ where
  constraint = Set γ ∋ A

idᵐᶜ : ∀ {α β} {C : Container α β} -> C ∸>ᶜ C
idᵐᶜ = id , λ _ pos -> pos

_∘ᵐᶜ_ : ∀ {α₁ α₂ α₃ β₁ β₂ β₃}
          {C₁ : Container α₁ β₁} {C₂ : Container α₂ β₂} {C₃ : Container α₃ β₃}
      -> C₂ ∸>ᶜ C₃ -> C₁ ∸>ᶜ C₂ -> C₁ ∸>ᶜ C₃
(shape₃ , position₂) ∘ᵐᶜ (shape₂ , position₁) =
  shape₃ ∘ shape₂ , λ sh₁ -> position₁ sh₁ ∘ position₂ (shape₂ sh₁)
