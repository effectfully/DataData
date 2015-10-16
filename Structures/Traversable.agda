module DataData.Structures.Traversable where

open import DataData.Prelude

record Constᵣ {α β} {B : Set β} (A : Set α) (y : B) : Set α where
  constructor Const
  field unConst : A
open Constᵣ public

record _∘ᵣ_ {α β γ} {A : Set α} {B : A -> Set β}
            (C : ∀ {x} -> B x -> Set γ) (f : ∀ x -> B x) x : Set γ where
  constructor Comp
  field unComp : C (f x)
open _∘ᵣ_ public

data Inverse {α β} {A : Set α} {B : A -> Set β} (f : ∀ x -> B x) : ∀ x -> B x -> Set (α ⊔ β) where
  beta : ∀ {x} -> Inverse f x (f x)

syntax Inverse f x y = f ⁻¹ y ≈ x

record Functor {α β} (F : Set α -> Set β) : Set (lsuc α ⊔ β) where
  infixl 5 _⟨$⟩_
  infixr 6 _⟨∘⟩_

  field
    _⟨$⟩_ : ∀ {A B} -> (A -> B) -> F A -> F B

  fmap = _⟨$⟩_

  _⟨∘⟩_ : ∀ {ι} {I : Set ι} {A B} -> (A -> B) -> (I -> F A) -> I -> F B
  (g ⟨∘⟩ f) x = g ⟨$⟩ f x
open Functor {{...}} public

record Pointed {α β} (F : Set α -> Set β) : Set (lsuc α ⊔ β)  where
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

record Monad {α β} (M : Set α -> Set β) : Set (lsuc α ⊔ β) where
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
    ; _⟨*⟩_   = λ f x -> Comp (_⟨*⟩_ ⟨$⟩ unComp f ⟨*⟩ unComp x)
    }

  ×-Applicative : ∀ {α β γ} {F : Set α -> Set β} {G : Set α -> Set γ}
                    {{Ψ : Applicative F}} {{Φ : Applicative G}} -> Applicative (_×_ ∘ F ˢ G)
  ×-Applicative = record
    { pointed = record { point = < point , point > } 
    ; _⟨*⟩_   = zip _⟨*⟩_ _⟨*⟩_
    }

  →-Applicative : ∀ {α β} {A : Set α} -> Applicative {β} λ B -> A -> B
  →-Applicative = record
    { pointed = record { point = const }
    ; _⟨*⟩_   = _ˢ_
    }

  Vec-Applicative : ∀ {α n} -> Applicative {α} (flip Vec n)
  Vec-Applicative = record
    { pointed = record { point = replicate }
    ; _⟨*⟩_   = _⊛_
    }

  Lift-Applicative : ∀ {α β} -> Applicative (Lift {α} {β}) 
  Lift-Applicative = record
    { pointed = record { point = lift }
    ; _⟨*⟩_   = λ f x -> lift (lower f (lower x))
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
  infixl 5 _∙_

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
      ; _∙_ = λ x y -> lift (lower x ∙ lower y)
      }

record Sumᵣ α : Set α where
  constructor Sum
  field unSum : ℕ
open Sumᵣ public

instance
  Sum-Monoid : ∀ {α} -> Monoid (Sumᵣ α)
  Sum-Monoid = record
    { ε   = Sum 0
    ; _∙_ = λ n m -> Sum (unSum n + unSum m)
    }

-- -- Not so universe polymorphic due to the Setω stuff.
-- -- I don't want to add `γ' to the type signature of `Foldable',
-- -- because it likely will break instance search.
-- record Foldable {α β} (F : Set α -> Set β) : Set (lsuc α ⊔ β) where
--   field
--     foldMap : ∀ {A B} {{M : Monoid {α} B}} -> (A -> B) -> F A -> B
-- open Foldable {{...}} public

-- instance
--   Lift-Foldable : ∀ {α β} -> Foldable (Lift {α} {β})
--   Lift-Foldable = record { foldMap = _∘ lower }

record Traversable {α} (F : Set α -> Set α) : Set (lsuc α) where
  field
    traverse : ∀ {G A B} {{Ψ : Applicative G}} -> (A -> G B) -> F A -> G (F B)
open Traversable {{...}} public

module _ {α} {F : Set α -> Set α} {{Ψ : Traversable F}} where
  Traversable<:Functor : Functor F
  Traversable<:Functor = record { _⟨$⟩_ = traverse }

  -- instance
  --   Traversable<:Foldable : Foldable F
  --   Traversable<:Foldable = record { foldMap = λ f -> unConst ∘ traverse {B = ─} (Const ∘ f) }

module _ α {β} {F : Set (α ⊔ β) -> Set (α ⊔ β)} {{Ψ : Traversable F}} where
  foldMapᵤ : ∀ {A} {B : Set β} {{M : Monoid B}} -> (A -> B) -> F A -> B
  foldMapᵤ f = lower {ℓ = α} ∘ unConst ∘ traverse {B = ─} (Const ∘ lift ∘ f)

module _ {α} where
  foldMap = foldMapᵤ α {α}

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
