open import Level renaming (suc to lsuc)
open import Function
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Unit.Base
open import Data.Nat.Base hiding (_⊔_)
open import Data.Sum     as S
open import Data.Product as P
open import Data.Vec     as V hiding ([_]; _>>=_)

record Constᵣ {α β} {B : Set β} (A : Set α) (y : B) : Set α where
  constructor Const
  field unConst : A
open Constᵣ public

record _∘ᵣ_ {α β γ} {A : Set α} {B : A -> Set β} (C : ∀ {x} -> B x -> Set γ) (f : ∀ x -> B x) x : Set γ where
  constructor Comp
  field unComp : C (f x)
open _∘ᵣ_ public

data Inverse {α β} {A : Set α} {B : A -> Set β} (f : ∀ x -> B x) : ∀ x -> B x -> Set (α ⊔ β) where
  beta : ∀ {x} -> Inverse f x (f x)

syntax Inverse f x y = f ⁻¹ y ≈ x

record Functor {α β} (F : Set α -> Set β) : Set (lsuc (α ⊔ β)) where
  infixl 5 _⟨$⟩_
  infixr 6 _⟨∘⟩_

  field
    _⟨$⟩_ : ∀ {A B} -> (A -> B) -> F A -> F B

  _⟨∘⟩_ : ∀ {ι} {I : Set ι} {A B} -> (A -> B) -> (I -> F A) -> I -> F B
  (g ⟨∘⟩ f) x = g ⟨$⟩ f x
open Functor {{...}} public

record Pointed {α β} (F : Set α -> Set β) : Set (lsuc (α ⊔ β))  where
  field
    point : ∀ {A} -> A -> F A
open Pointed {{...}} public

record Applicative {α β} (F : Set α -> Set β) : Set (lsuc (α ⊔ β)) where
  infixl 5 _⟨*⟩_

  field
    pointed : Pointed F
    _⟨*⟩_   : ∀ {A B} -> F (A -> B) -> F A -> F B
open Applicative {{...}} public renaming (pointed to pointedₐ)

module _ {α β} {F : Set α -> Set β} {{Ψ : Applicative F}} where
  instance
    Applicative<:Pointed : Pointed F
    Applicative<:Pointed = pointedₐ

    Applicative<:Functor : Functor F
    Applicative<:Functor = record { _⟨$⟩_ = _⟨*⟩_ ∘ point }

  liftA₂ : ∀ {A B C} -> (A -> B -> C) -> F A -> F B -> F C
  liftA₂ f x y = f ⟨$⟩ x ⟨*⟩ y

record Monad {α β} (M : Set α -> Set β) : Set (lsuc (α ⊔ β)) where
  infixl 2 _>>=_

  field
    pointed : Pointed M
    _>>=_   : ∀ {A B} -> M A -> (A -> M B) -> M B
open Monad {{...}} public renaming (pointed to pointedₘ)

module _ {α β} {M : Set α -> Set β} {{Ψ : Monad M}} where
  instance
    Monad<:Applicative : Applicative M
    Monad<:Applicative = record
      { pointed = pointedₘ
      ; _⟨*⟩_   = λ mf mx -> mf >>= λ f -> mx >>= point {{pointedₘ}} ∘ f
      }

instance
  id-Applicative : ∀ {α} -> Applicative {α} id
  id-Applicative = record
    { pointed = record { point = id }
    ; _⟨*⟩_   = _$_
    }

  ∘-Applicative : ∀ {α β γ} {G : Set β -> Set γ} {F : Set α -> Set β}
                    {{Φ : Applicative G}} {{Ψ : Applicative F}} -> Applicative (G ∘ᵣ F)
  ∘-Applicative {{Φ}} {{Ψ}} = record
    { pointed = record { point = Comp ∘ point ∘ point }
    ; _⟨*⟩_   = λ ⟨⟨f⟩⟩ ⟨⟨x⟩⟩ -> Comp (_⟨*⟩_ ⟨$⟩ unComp ⟨⟨f⟩⟩ ⟨*⟩ unComp ⟨⟨x⟩⟩)
    }

  ×-Applicative : ∀ {α β γ} {F : Set α -> Set β} {G : Set α -> Set γ}
                    {{Ψ : Applicative F}} {{Φ : Applicative G}} -> Applicative (_×_ ∘ F ˢ G)
  ×-Applicative = record
    { pointed = record { point = < point , point > } 
    ; _⟨*⟩_   = P.zip _⟨*⟩_ _⟨*⟩_
    }

  →-Applicative : ∀ {α β} {A : Set α} -> Applicative {β} λ B -> A -> B
  →-Applicative = record
    { pointed = record { point = const }
    ; _⟨*⟩_   = _ˢ_
    }

  Vec-Applicative : ∀ {α n} -> Applicative {α} (flip Vec n)
  Vec-Applicative = record
    { pointed = record { point = replicate }
    ; _⟨*⟩_   = zipWith _$_
    }

  Lift-Applicative : ∀ {α β} -> Applicative (Lift {α} {β}) 
  Lift-Applicative = record
    { pointed = record { point = lift }
    ; _⟨*⟩_   = λ ⟨f⟩ ⟨x⟩ -> lift (lower ⟨f⟩ (lower ⟨x⟩))
    }

module Vec-Monad where
  _>>=ᵥ_ : ∀ {α β n} {A : Set α} {B : Set β} -> Vec A n -> (A -> Vec B n) -> Vec B n
  []       >>=ᵥ f = []
  (x ∷ xs) >>=ᵥ f = head (f x) ∷ (xs >>=ᵥ (tail ∘ f))

  Vec-Monad : ∀ {α n}-> Monad {α} (flip Vec n)
  Vec-Monad = record
    { pointed = record { point = replicate }
    ; _>>=_   = _>>=ᵥ_
    }

  agree : ∀ {α n} {A B : Set α} (fs : Vec (A -> B) n) (xs : Vec A n)
        -> fs ⟨*⟩ xs ≡ _⟨*⟩_ {{Monad<:Applicative {{Vec-Monad}}}} fs xs
  agree  []       []      = refl
  agree (f ∷ fs) (x ∷ xs) = cong (f x ∷_) (agree fs xs)

record Monoid {α} (A : Set α) : Set α where
  infixl 4 _∙_

  field
    ε   : A
    _∙_ : A -> A -> A
open Monoid {{...}} public

module _ {α} {A : Set α} {{M : Monoid A}} where
  instance
    Monoid<:Applicative : ∀ {α} -> Applicative {α} (Constᵣ A)
    Monoid<:Applicative = record
      { pointed = record { point = Const ∘ const ε }
      ; _⟨*⟩_   = λ x y -> Const (unConst x ∙ unConst y)
      }

    Lift-Monoid : ∀ {β} -> Monoid (Lift {ℓ = β} A)
    Lift-Monoid = record
      { ε   = lift ε
      ; _∙_ = λ ⟨x⟩ ⟨y⟩ -> lift (lower ⟨x⟩ ∙ lower ⟨y⟩)
      }

record Sumᵣ : Set where
  constructor Sum
  field unSum : ℕ
open Sumᵣ public

instance
  Sum-Monoid : Monoid Sumᵣ
  Sum-Monoid = record
    { ε   = Sum 0
    ; _∙_ = λ n m -> Sum (unSum n + unSum m)
    }

-- Not so universe polymorphic due to the Setω stuff.
-- I don't want to add `γ' to the type signature of `Foldable',
-- because it likely will break instance search.
record Foldable {α β} (F : Set α -> Set β) : Set (lsuc (α ⊔ β)) where
  field
    foldMap : ∀ {A B} {{M : Monoid {α} B}} -> (A -> B) -> F A -> B
open Foldable {{...}} public

instance
  Lift-Foldable : ∀ {α β} -> Foldable (Lift {α} {β})
  Lift-Foldable = record { foldMap = _∘ lower }

record Traversable {α} (F : Set α -> Set α) : Set (lsuc α) where
  field
    traverse : ∀ {G A B} {{Ψ : Applicative G}} -> (A -> G B) -> F A -> G (F B)
open Traversable {{...}} public

module _ {α} {F : Set α -> Set α} {{Ψ : Traversable F}} where
  Traversable<:Functor : Functor F
  Traversable<:Functor = record { _⟨$⟩_ = traverse }

  instance
    Traversable<:Foldable : Foldable F
    Traversable<:Foldable = record { foldMap = λ f -> unConst ∘ traverse {B = Lift ⊤} (Const ∘ f) }

id-Traversable : ∀ {α} -> Traversable {α} id
id-Traversable = record { traverse = _$_ }

instance
  ∘-Traversable : ∀ {α} {G : Set α -> Set α} {F : Set α -> Set α}
                    {{Φ : Traversable G}} {{Ψ : Traversable F}} -> Traversable (G ∘ᵣ F)
  ∘-Traversable = record { traverse = λ f -> Comp ⟨∘⟩ traverse (traverse f) ∘ unComp }

  Vec-Traversable : ∀ {α n} -> Traversable {α} (flip Vec n)
  Vec-Traversable = record { traverse = λ {G} f -> foldr (G ∘ Vec _) (liftA₂ _∷_ ∘ f) (point []) }

transpose : ∀ {α n m} {A : Set α} -> Vec (Vec A m) n -> Vec (Vec A n) m
transpose = traverse id

infix 0 _/_
record Normal α : Set (lsuc α) where
  constructor _/_
  field
    Shape : Set α
    size  : Shape -> ℕ

  ⟦_⟧ₙ : ∀ {β} -> Set β -> Set (α ⊔ β)
  ⟦_⟧ₙ A = ∃ λ sh -> Vec A (size sh)
open Normal public

module _ {α} {{F : Normal α}} where
  -- Makes instance search ambiguous somehow. Wrap extension in a record?
  -- instance
    Normal<:Traversable-⟦⟧ : ∀ {β} -> Traversable {α ⊔ β} ⟦ F ⟧ₙ
    Normal<:Traversable-⟦⟧ = record { traverse = λ{ f (sh , v) -> ,_ ⟨$⟩ traverse f v } }

ListN : Normal _
ListN = ℕ / id

VecN : ℕ -> Normal _
VecN n = ⊤ / const n

Kₙ : ∀ {α} -> Set α -> Normal _
Kₙ A = A / const 0

_⊎ₙ_ : ∀ {α β} -> Normal α -> Normal β -> Normal (α ⊔ β)
(Sh₁ / s₁) ⊎ₙ (Sh₂ / s₂) = Sh₁ ⊎ Sh₂ / [ s₁ , s₂ ]

_×ₙ_ : ∀ {α β} -> Normal α -> Normal β -> Normal (α ⊔ β)
(Sh₁ / s₁) ×ₙ (Sh₂ / s₂) = Sh₁ × Sh₂ / uncurry _+_ ∘ P.map s₁ s₂

injₙ : ∀ {α} {A : Set α} {F₁ F₂ : Normal α} -> ⟦ F₁ ⟧ₙ A ⊎ ⟦ F₂ ⟧ₙ A -> ⟦ F₁ ⊎ₙ F₂ ⟧ₙ A
injₙ (inj₁ (sh₁ , v₁)) = inj₁ sh₁ , v₁
injₙ (inj₂ (sh₂ , v₂)) = inj₂ sh₂ , v₂

pairₙ : ∀ {α} {A : Set α} {F₁ F₂ : Normal α} -> ⟦ F₁ ⟧ₙ A × ⟦ F₂ ⟧ₙ A -> ⟦ F₁ ×ₙ F₂ ⟧ₙ A
pairₙ ((sh₁ , v₁) , (sh₂ , v₂)) = (sh₁ , sh₂) , (v₁ ++ v₂)

uninjₙ : ∀ {α} {A : Set α} {F₁ F₂ : Normal α} -> ⟦ F₁ ⊎ₙ F₂ ⟧ₙ A -> ⟦ F₁ ⟧ₙ A ⊎ ⟦ F₂ ⟧ₙ A
uninjₙ (inj₁ sh , v₁) = inj₁ (sh , v₁)
uninjₙ (inj₂ sh , v₂) = inj₂ (sh , v₂)

-- We need to pass `F₁' explicitly because of pattern matching in _++_.
unpairₙ : ∀ {α} {A : Set α} (F₁ {F₂} : Normal α) -> ⟦ F₁ ×ₙ F₂ ⟧ₙ A -> ⟦ F₁ ⟧ₙ A × ⟦ F₂ ⟧ₙ A
unpairₙ F₁ ((sh₁ , sh₂) , v₁₂) = case splitAt (size F₁ sh₁) v₁₂ of λ { (v₁ , v₂ , _) -> (sh₁ , v₁) , (sh₂ , v₂) }

injₙ-surj : ∀ {α} {A : Set α} {F₁ F₂ : Normal α} -> (p : ⟦ F₁ ⊎ₙ F₂ ⟧ₙ A) -> injₙ ⁻¹ p ≈ uninjₙ p
injₙ-surj (inj₁ sh , v₁) = beta
injₙ-surj (inj₂ sh , v₂) = beta

unpairₙ-surj : ∀ {α} {A : Set α} (F₁ {F₂} : Normal α) -> (p : ⟦ F₁ ×ₙ F₂ ⟧ₙ A) -> pairₙ ⁻¹ p ≈ unpairₙ F₁ p
unpairₙ-surj F₁ ((sh₁ , sh₂) , v₁₂) with splitAt (size F₁ sh₁) v₁₂
... | v₁ , v₂ , p rewrite p = beta

instance
  ListN-Monoid : ∀ {α} {A : Set α} -> Monoid (⟦ ListN ⟧ₙ A)
  ListN-Monoid = record
    { ε   = , []
    ; _∙_ = P.zip _+_ _++_
    }

-- `F₂' is not used  in the second argument of _/_ at all.
_∘ₙ_ : ∀ {α β} -> Normal α -> Normal β -> Normal (α ⊔ β)
F₂ ∘ₙ (Sh₁ / s₁) = ⟦ F₂ ⟧ₙ Sh₁ / unSum ∘ lower ∘ foldMap (lift ∘ Sum ∘ s₁) ∘ proj₂

sizeₜ : ∀ {α A} {F : Set α -> Set α} {{Ψ : Foldable F}} -> F A -> ℕ
sizeₜ = unSum ∘ lower ∘ foldMap (lift ∘ Sum ∘ const 1)

-- `Foldable' is enough.
Foldable<:Normal : ∀ {α} {F : Set α -> Set α} {{Ψ : Foldable F}} -> Normal _
Foldable<:Normal {F = F} = F (Lift ⊤) / sizeₜ

-- Seems not nice to use `traverse' instead of `fmap'.
-- But making Traverse<:Functor an instance would introduce ambiguity.
shapeₜ : ∀ {α A} {F : Set α -> Set α} {{Ψ : Traversable F}} -> F A -> F (Lift ⊤)
shapeₜ = traverse (const _)

contentsₜ : ∀ {α A} {F : Set α -> Set α} {{Ψ : Foldable F}} -> F A -> ⟦ ListN ⟧ₙ A
contentsₜ = foldMap (λ x -> , x ∷ [])
