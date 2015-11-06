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

-- _*ˢ : ∀ {α β} -> Container α β -> Container α β
-- isoˡ : ∀ {α β γ} {A : Set γ} -> (C : Container α β) -> C *ᶜ A -> ⟦ C *ˢ ⟧ᶜ A
-- isoʳ : ∀ {α β γ} {A : Set γ} -> (C : Container α β) -> ⟦ C *ˢ ⟧ᶜ A -> C *ᶜ A

call : ∀ {α β} {C : Container α β} -> (sh : Shape C) -> C *ᶜ Position C sh
call sh = ⟨ inj₂ sh , point ⟩

-- How to read this?
Π⊥ : ∀ {α β} -> (A : Set α) -> (A -> Set β) -> Set (α ⊔ β)
Π⊥ A B = (x : A) -> (A ◃ B) *ᶜ B x

-- What does this creepy mutual recursion mean?
mutual
  gas : ∀ {α β} {A : Set α} {B : A -> Set β} -> ℕ -> Π⊥ A B -> (x : A) -> Maybe (B x)
  gas              zero   f x = nothing
  gas {A = A} {B} (suc n) f x = run (f x) where
    run : ∀ {x} -> (A ◃ B) *ᶜ B x -> Maybe (B x)
    run ⟨ inj₁ y  , r ⟩ = just y
    run ⟨ inj₂ x' , r ⟩ = gas n f x' >>= run ∘ r
