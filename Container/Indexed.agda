module DataData.Container.Indexed where

open import DataData.Prelude
open import DataData.STLC.Core

infixr 0 _◃_$_

record IContainer {ι κ} (I : Set ι) (J : Set κ) α β : Set (ι ⊔ κ ⊔ lsuc (α ⊔ β)) where
  constructor _◃_$_
  field
    Shape    : J -> Set α
    Position : ∀ j -> Shape j -> Set β
    index    : ∀ j (sh : Shape j) -> Position j sh -> I

  ⟦_⟧ᵢ : ∀ {γ} -> (I -> Set γ) -> J -> Set (α ⊔ β ⊔ γ)
  ⟦_⟧ᵢ A j = ∃ λ sh -> ∀ pos -> A (index j sh pos)

  Elᵢ : ∀ {γ} -> (I -> Set γ) -> J -> Set (α ⊔ β ⊔ γ)
  Elᵢ A j = ∃ λ sh -> ∃ λ pos -> A (index j sh pos)
open IContainer public

elᵢ : ∀ {ι κ α β γ} {I : Set ι} {J : Set κ} {j}
    -> (C : IContainer I J α β)
    -> (A : I -> Set γ)
    -> (c : ⟦ C ⟧ᵢ A j)
    -> Position C j (proj₁ c)
    -> Elᵢ C A j
elᵢ C A (sh , el) pos = sh , pos , el pos

mapᵢ : ∀ {ι κ α β γ δ} {I : Set ι} {J : Set κ} {C : IContainer I J α β}
         {A : I -> Set γ} {B : I -> Set δ}
     -> (A ∸> B) -> ⟦ C ⟧ᵢ A ∸> ⟦ C ⟧ᵢ B
mapᵢ f = second (f ∘_)

Everywhere : ∀ {ι κ α β γ} {I : Set ι} {J : Set κ}
           -> (C : IContainer I J α β)
           -> (A : I -> Set γ)
           -> IContainer (Σ I A) (Σ J (⟦ C ⟧ᵢ A)) lzero β
Everywhere (Sh ◃ Pos $ ind) A = (λ   _                  -> ⊤                      )
                              ◃ (λ{ (j , sh , el) _     -> Pos j sh              })
                              $ (λ{ (j , sh , el) _ pos -> ind j sh pos , el pos })

allTrivial : ∀ {ι κ α β γ} {I : Set ι} {J : Set κ}
           -> (C : IContainer I J α β)
           -> (A : I -> Set γ)
           -> ∀ {j} -> ⟦ Everywhere C A ⟧ᵢ (λ _ -> ⊤) j
allTrivial C A = _ , _

-- Somewhere : ∀ {ι κ α β γ} {I : Set ι} {J : Set κ}
--           -> (C : IContainer I J α β)
--           -> (A : I -> Set γ)
--           -> IContainer (Σ I A) (Σ J (⟦ C ⟧ᵢ A)) β lzero
-- Somewhere (Sh ◃ Pos $ ind) A = (λ{ (j , sh , el)       -> Pos j sh              })
--                              ◃ (λ{  _            _     -> ⊤                     })
--                              $ (λ{ (j , sh , el) pos _ -> ind j sh pos , el pos })

Somewhere : ∀ {ι κ α β γ} {I : Set ι} {J : Set κ}
          -> (C : IContainer I J α β)
          -> (A : I -> Set γ)
          -> IContainer (Σ I A) (Σ J (Elᵢ C A)) lzero lzero
Somewhere (Sh ◃ Pos $ ind) A = (λ _   -> ⊤)
                             ◃ (λ _ _ -> ⊤)
                             $ (λ{ (j , sh , pos , x) _ _ -> ind j sh pos , x })

noMagic : ∀ {ι κ α β γ} {I : Set ι} {J : Set κ}
        -> (C : IContainer I J α β)
        -> (A : I -> Set γ)
        -> ∀ {j} -> ¬ ⟦ Somewhere C A ⟧ᵢ (λ _ -> ⊥) j
noMagic C A (_ , flip) = flip _

lookupᵢ : ∀ {ι κ α β γ π ρ} {I : Set ι} {J : Set κ} {A : I -> Set γ}
            {P : Σ I A -> Set π} {Q : Σ I A -> Set ρ} {C : IContainer I J α β} {j pos}
        -> ⟦ Everywhere C A ⟧ᵢ  P             j
        -> ⟦ Somewhere  C A ⟧ᵢ  Q            (, elᵢ C A (proj₂ j) pos)
        -> ⟦ Somewhere  C A ⟧ᵢ (_×_ ∘ P ˢ Q) (, elᵢ C A (proj₂ j) pos)
lookupᵢ (_ , pr₁) (_ , pr₂) = _ , λ _ -> pr₁ _ , pr₂ _

record ITree {κ α β} {J : Set κ} (C : IContainer J J α β) (j : J) : Set (κ ⊔ α ⊔ β) where
  inductive
  constructor ⟨_⟩
  field unITree : ⟦ C ⟧ᵢ (ITree C) j

{-# TERMINATING #-}
elim-ITree : ∀ {κ α β π} {J : Set κ} {C : IContainer J J α β} {j : J}
           -> (P : Σ J (ITree C) -> Set π)
           -> (⟦ Everywhere C (ITree C) ⟧ᵢ P ∸> P ∘ second ⟨_⟩)
           -> (t : ITree C j)
           -> P (j , t)
elim-ITree P n ⟨ sh , el ⟩ = n (_ , elim-ITree P n ∘ el)

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
