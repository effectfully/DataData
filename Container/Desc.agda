module DataData.Container.Desc where

open import DataData.Prelude
open import DataData.Container.Indexed

infixr 6 _<&>_
infixr 5 _<|>_

data Desc {ι} (I : Set ι) α : Set (ι ⊔ lsuc α) where
  var   : I -> Desc I α
  κ     : Set α -> Desc I α
  σ π   : (A : Set α) -> (A -> Desc I α) -> Desc I α
  _<&>_ : Desc I α -> Desc I α -> Desc I α

κ₀ : ∀ {ι α} {I : Set ι} -> Set -> Desc I α
κ₀ = κ ∘ Lift

σ₀ : ∀ {ι α} {I : Set ι} -> (A : Set) -> (A -> Desc I α) -> Desc I α
σ₀ A f = σ (Lift A) (f ∘ lower)

_<|>_ : ∀ {ι α} {I : Set ι} -> Desc I α -> Desc I α -> Desc I α
d₁ <|> d₂ = σ₀ Bool (d₁ <∨> d₂)

⟦_⟧ᴰ : ∀ {ι α} {I : Set ι} -> Desc I α -> (I -> Set α) -> Set α
⟦ var i     ⟧ᴰ A = A i
⟦ κ A       ⟧ᴰ _ = A
⟦ σ _ f     ⟧ᴰ A = ∃ λ x -> ⟦ f x ⟧ᴰ A
⟦ π _ f     ⟧ᴰ A = ∀   x -> ⟦ f x ⟧ᴰ A
⟦ d₁ <&> d₂ ⟧ᴰ A = ⟦ d₁ ⟧ᴰ A × ⟦ d₂ ⟧ᴰ A

IContainer-Desc : ∀ {ι κ α} {I : Set ι} {J : Set κ} -> IContainer I J α α -> J -> Desc I α
IContainer-Desc (Sh ◃ Pos $ ind) j = σ (Sh j) λ sh -> π (Pos j sh) λ pos -> var (ind j sh pos)

Shapeᴰ : ∀ {ι α} {I : Set ι} -> Desc I α -> Set α
Shapeᴰ d = ⟦ d ⟧ᴰ (λ _ -> Lift ⊤)

Positionᴰ : ∀ {ι α} {I : Set ι} -> (d : Desc I α) -> Shapeᴰ d -> Set α
Positionᴰ (var i)      _          = Lift ⊤
Positionᴰ (κ A)        x          = Lift ⊥
Positionᴰ (σ A f)     (x , sh)    = Positionᴰ (f x) sh
Positionᴰ (π A f)      g          = ∃ λ x -> Positionᴰ (f x) (g x)
Positionᴰ (d₁ <&> d₂) (sh₁ , sh₂) = Positionᴰ d₁ sh₁ ⊎ Positionᴰ d₂ sh₂

indexᴰ : ∀ {ι α} {I : Set ι} -> (d : Desc I α) -> (sh : Shapeᴰ d) -> Positionᴰ d sh -> I
indexᴰ (var i)      _           _         = i
indexᴰ (κ A)        x          (lift ())
indexᴰ (σ A f)     (x , sh)     pos       = indexᴰ (f x)  sh   pos
indexᴰ (π A f)      g          (x , pos)  = indexᴰ (f x) (g x) pos
indexᴰ (d₁ <&> d₂) (sh₁ , sh₂) (inj₁ pos) = indexᴰ d₁ sh₁ pos
indexᴰ (d₁ <&> d₂) (sh₁ , sh₂) (inj₂ pos) = indexᴰ d₂ sh₂ pos

Desc-IContainer : ∀ {ι κ α} {I : Set ι} {J : Set κ} -> (J -> Desc I α) -> IContainer I J α α
Desc-IContainer f = Shapeᴰ ∘ f ◃ Positionᴰ ∘ f $ indexᴰ ∘ f

VecD : ∀ {α} -> Set α -> ℕ -> Desc ℕ α
VecD A n = κ₀ (n ≡ 0) <|> σ₀ ℕ λ m -> κ A <&> κ₀ (n ≡ suc m) <&> var m

VecD′ : ∀ {α} -> Set α -> ℕ -> Desc ℕ α
VecD′ A  0      = κ₀ ⊤
VecD′ A (suc n) = κ A <&> var n

record Data {ι α} {I : Set ι} (f : I -> Desc I α) (i : I) : Set α where
  inductive
  constructor ⟨_⟩
  field unData : ⟦ f i ⟧ᴰ (Data f)

Vecᴰ : ∀ {α} -> Set α -> ℕ -> Set α
Vecᴰ = Data ∘ VecD

nilᴰ : ∀ {α} {A : Set α} -> Vecᴰ A 0
nilᴰ = ⟨ lift true , lift refl ⟩

consᴰ : ∀ {α n} {A : Set α} -> A -> Vecᴰ A n -> Vecᴰ A (suc n)
consᴰ x xs = ⟨ lift false , _ , x , lift refl , xs ⟩

Descᴾ : ∀ α -> Set (lsuc α)
Descᴾ = Desc ⊤

Dataᴾ : ∀ {α} -> Descᴾ α -> Set α
Dataᴾ d = Data (const d) _

DescD : ∀ {ι} -> Set ι -> ∀ α -> Descᴾ (ι ⊔ lsuc α)
DescD {ι} I α =
      κ (Lift {ℓ = lsuc α} I)
  <|> κ (Lift {ℓ = ι} (Set α))
  <|> σ (Lift {ℓ = ι} (Set α)) (λ A -> π (Lift {ℓ = lsuc α ⊔ ι} (lower A)) (const (var _)))
  <|> σ (Lift {ℓ = ι} (Set α)) (λ A -> π (Lift {ℓ = lsuc α ⊔ ι} (lower A)) (const (var _)))
  <|> var _ <&> var _

Descᴰ : ∀ {ι} -> Set ι -> ∀ α -> Set (ι ⊔ lsuc α)
Descᴰ I α = Dataᴾ (DescD I α)

{-# TERMINATING #-}
desc : ∀ {ι α} {I : Set ι} -> Descᴰ I α -> Desc I α
desc ⟨ lift true  ,                                        lift i     ⟩ = var i
desc ⟨ lift false , lift true  ,                           lift A     ⟩ = κ A
desc ⟨ lift false , lift false , lift true  ,              lift A , f ⟩ = σ A (desc ∘ f ∘ lift)
desc ⟨ lift false , lift false , lift false , lift true  , lift A , f ⟩ = π A (desc ∘ f ∘ lift)
desc ⟨ lift false , lift false , lift false , lift false , d₁ , d₂    ⟩ = desc d₁ <&> desc d₂

-- TODO: add some examples.
Everywhereᴰ : ∀ {ι α} {I : Set ι} {A : I -> Set α} -> (d : Desc I α) -> ⟦ d ⟧ᴰ A -> Desc (Σ I A) α
Everywhereᴰ (var i)      x        = var (i , x)
Everywhereᴰ (κ A)        _        = κ₀ ⊤
Everywhereᴰ (σ A f)     (x , d)   = Everywhereᴰ (f x) d
Everywhereᴰ (π A f)      g        = π A λ x -> Everywhereᴰ (f x) (g x)
Everywhereᴰ (d₁ <&> d₂) (x₁ , x₂) = Everywhereᴰ d₁ x₁ <&> Everywhereᴰ d₂ x₂

Somewhereᴰ : ∀ {ι α} {I : Set ι} {A : I -> Set α} -> (d : Desc I α) -> ⟦ d ⟧ᴰ A -> Desc (Σ I A) α
Somewhereᴰ (var i)      x        = var (i , x)
Somewhereᴰ (κ A)        _        = κ₀ ⊥
Somewhereᴰ (σ A f)     (x , d)   = Somewhereᴰ (f x) d
Somewhereᴰ (π A f)      g        = π A λ x -> Somewhereᴰ (f x) (g x)
Somewhereᴰ (d₁ <&> d₂) (x₁ , x₂) = Somewhereᴰ d₁ x₁ <|> Somewhereᴰ d₂ x₂

{-# TERMINATING #-}
elim-Data : ∀ {ι α} {I : Set ι} {f : I -> Desc I α} {i}
          -> (P : Σ I (Data f) -> Set α)
          -> (∀ {i} {ds : ⟦ f i ⟧ᴰ (Data f)} -> ⟦ Everywhereᴰ (f i) ds ⟧ᴰ P -> P (i , ⟨ ds ⟩))
          -> (d : Data f i)
          -> P (i , d)
elim-Data {f = f} P r ⟨ ds ⟩ = r (go (f _) ds) where
  go : ∀ d -> (ds : ⟦ d ⟧ᴰ (Data f)) -> ⟦ Everywhereᴰ d ds ⟧ᴰ P
  go (var i)      d          = elim-Data P r d
  go (κ A)        x          = _
  go (σ A f)     (x , ds)    = go (f x) ds
  go (π A f)      g          = λ x -> go (f x) (g x)
  go (d₁ <&> d₂) (ds₁ , ds₂) = go d₁ ds₁ , go d₂ ds₂
