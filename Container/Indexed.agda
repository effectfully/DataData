module DataData.Container.Indexed where

open import DataData.Prelude
open import DataData.STLC.Core

infixr 0 _◃_$_

record IContainer {ι κ} (I : Set ι) (J : Set κ) α β : Set (ι ⊔ κ ⊔ lsuc (α ⊔ β)) where
  constructor _◃_$_
  field
    Shape    : J -> Set α
    Position : ∀ j -> Shape j -> Set β
    irec     : ∀ j (sh : Shape j) -> Position j sh -> I

  ⟦_⟧ᵢ : ∀ {γ} -> (I -> Set γ) -> J -> Set (α ⊔ β ⊔ γ)
  ⟦_⟧ᵢ A j = ∃ λ sh -> (p : Position j sh) -> A (irec j sh p)
open IContainer public

mapᵢ : ∀ {ι κ α β γ δ} {I : Set ι} {J : Set κ} {C : IContainer I J α β}
         {A : I -> Set γ} {B : I -> Set δ}
     -> (A ∸> B) -> ⟦ C ⟧ᵢ A ∸> ⟦ C ⟧ᵢ B
mapᵢ f = second (f ∘_)

record ITree {κ α β} {J : Set κ} (C : IContainer J J α β) (j : J) : Set (κ ⊔ α ⊔ β) where
  inductive
  constructor ⟨_⟩
  field unITree : ⟦ C ⟧ᵢ (ITree C) j

Natᴵ : Set
Natᴵ = ITree (const Bool ◃ const T $ _) tt

zeroᴵ : Natᴵ
zeroᴵ = ⟨ false , (λ()) ⟩

sucᴵ : Natᴵ -> Natᴵ
sucᴵ n = ⟨ true , const n ⟩

Vecᴵ : ∀ {α} -> Set α -> ℕ -> Set α
Vecᴵ {α} A = ITree (El ◃ Rec $ prev) where
  El : ℕ -> Set α
  El  0      = Lift ⊤
  El (suc n) = A
  Rec : ∀ n -> El n -> Set
  Rec  0      _ = ⊥
  Rec (suc n) _ = ⊤
  prev : ∀ n -> (el : El n) -> Rec n el -> ℕ
  prev  0      _ ()
  prev (suc n) _ _  = n

nilᴵ : ∀ {α} {A : Set α} -> Vecᴵ A 0
nilᴵ = ⟨ , (λ()) ⟩

consᴵ : ∀ {α n} {A : Set α} -> A -> Vecᴵ A n -> Vecᴵ A (suc n)
consᴵ x xs = ⟨ x , const xs ⟩

infix 4 _⊢ᴱ_ _⊢ᴵ_

data _⊢ᴱ_ Γ : Type -> Set where
  varᴱ : ∀ {σ} -> σ ∈ Γ -> Γ ⊢ᴱ σ
  lam  : (σ τ : Type) -> Γ ⊢ᴱ σ ⇒ τ
  app  : (σ τ : Type) -> Γ ⊢ᴱ τ

_⊢ᴵ_ : Con -> Type -> Set
_⊢ᴵ_ = curry (ITree (uncurry _⊢ᴱ_ ◃ (λ _ -> Rec) $ (λ _ -> prev))) where
  Rec : ∀ {Γ σ} -> Γ ⊢ᴱ σ -> Set
  Rec (varᴱ v)  = ⊥
  Rec (lam σ τ) = ⊤
  Rec (app σ τ) = Bool

  prev : ∀ {Γ σ} -> (t : Γ ⊢ᴱ σ) -> Rec t -> Con × Type
  prev     (varᴱ v)  ()
  prev {Γ} (lam σ τ) _  = Γ ▻ σ , τ
  prev {Γ} (app σ τ) b  = Γ , (if b then σ ⇒ τ else σ)

varᴵ : ∀ {Γ σ} -> σ ∈ Γ -> Γ ⊢ᴵ σ
varᴵ v = ⟨ varᴱ v , (λ()) ⟩

ƛᴵ : ∀ {σ τ Γ} -> Γ ▻ σ ⊢ᴵ τ -> Γ ⊢ᴵ σ ⇒ τ
ƛᴵ {σ} {τ} b = ⟨ lam σ τ , const b ⟩

_·ᴵ_ : ∀ {σ τ Γ} -> Γ ⊢ᴵ σ ⇒ τ -> Γ ⊢ᴵ σ -> Γ ⊢ᴵ τ
_·ᴵ_ {σ} {τ} f x = ⟨ app σ τ , f <∨> x ⟩
