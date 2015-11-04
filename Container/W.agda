{-# OPTIONS --no-termination-check #-}

module DataData.Container.W where

open import DataData.Prelude
open import DataData.Structures
open import DataData.Container.Core

record W {α β} (C : Container α β) : Set (α ⊔ β) where
  inductive
  constructor ⟨_⟩
  field unW : ⟦ C ⟧ᶜ (W C)

Natᵂ : Set lzero
Natᵂ = W (Bool ◃ T)

zeroᵂ : Natᵂ
zeroᵂ = ⟨ false , (λ()) ⟩

sucᵂ : Natᵂ -> Natᵂ
sucᵂ n = ⟨ true , const n ⟩

paraᵂ : ∀ {α} {A : Set α} -> (Natᵂ -> A -> A) -> A -> Natᵂ -> A
paraᵂ f z ⟨ false , r ⟩ = z
paraᵂ f z ⟨ true  , r ⟩ = f (r _) (paraᵂ f z (r _))

cataᵂ : ∀ {α} {A : Set α} -> (A -> A) -> A -> Natᵂ -> A
cataᵂ = paraᵂ ∘ const

addᵂ : Natᵂ -> Natᵂ -> Natᵂ
addᵂ n m = cataᵂ sucᵂ m n

elim-Natᵂ : ∀ {π} (P : Natᵂ -> Set π) -> (∀ {n} -> P n -> P (sucᵂ n)) -> P zeroᵂ -> ∀ n -> P n
elim-Natᵂ P f z ⟨ false , r ⟩ = subst (λ r' -> P ⟨ false , r' ⟩) (ext (λ())) z
                                  where postulate ext : Extensionality _ _
elim-Natᵂ P f z ⟨ true  , r ⟩ = f (elim-Natᵂ P f z (r _))

_*ᶜ_ : ∀ {α β γ} -> Container α β -> Set γ -> Set (α ⊔ β ⊔ γ)
C *ᶜ A = W (Kᶜ A ⊎ᶜ C)

instance
  *ᶜ-Monad : ∀ {α β γ} {C : Container α β} -> Monad {γ} (C *ᶜ_)
  *ᶜ-Monad {γ = γ} {C} = record
    { pointed = record { point = λ x -> ⟨ inj₁ x , (λ{(lift())}) ⟩ }
    ; _>>=_   = _>>=ᶠ_
    } where
        _>>=ᶠ_ : {A B : Set γ} -> C *ᶜ A -> (A -> C *ᶜ B) -> C *ᶜ B
        ⟨ inj₁ x  , r ⟩ >>=ᶠ f = f x
        ⟨ inj₂ sh , r ⟩ >>=ᶠ f = ⟨ inj₂ sh , (λ pos -> r pos >>=ᶠ f) ⟩
