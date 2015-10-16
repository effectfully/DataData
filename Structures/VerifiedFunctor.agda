module DataData.Structures.VerifiedFunctor where

open import DataData.Prelude
open import DataData.Structures.Traversable
open import DataData.Structures.Normal

record VerifiedMonoid {α} (A : Set α) {{M : Monoid A}} : Set α where
  field
    idˡ   : {x : A}     -> ε ∙ x ≡ x
    idʳ   : {x : A}     -> x ∙ ε ≡ x
    assoc : {x y z : A} -> (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)

Sum-VerifiedMonoid : VerifiedMonoid Sumᵣ
Sum-VerifiedMonoid = record
  { idˡ   = refl
  ; idʳ   = λ {x} -> cong Sum (proj₂ CS.+-identity (unSum x))
  ; assoc = λ {x y z} -> cong Sum (CS.+-assoc (unSum x) (unSum y) (unSum z))
  }

ListN-VerifiedMonoid : ∀ {α} {A : Set α} -> VerifiedMonoid (⟦ ListN ⟧ₙ A)
ListN-VerifiedMonoid = record
  { idˡ   = refl
  ; idʳ   = icong (Vec _) ,_ (proj₂ CS.+-identity _) ++-[]
  ; assoc = λ{ {n , xs} -> icong (Vec _) ,_ (CS.+-assoc n _ _) (++-assoc xs) }
  }

record MonoidHom {α β} (A : Set α) (B : Set β) {{M : Monoid A}} {{N : Monoid B}}
                 (f : A -> B) : Set (α ⊔ β) where
  field
    resp-ε : f ε ≡ ε
    resp-∙ : ∀ {x y} -> f (x ∙ y) ≡ f x ∙ f y
open MonoidHom {{...}} public

proj₁-Hom : ∀ {α} {A : Set α} -> MonoidHom (⟦ ListN ⟧ₙ A) Sumᵣ (Sum ∘ proj₁)
proj₁-Hom = record
  { resp-ε = refl
  ; resp-∙ = refl
  }

record VerifiedFunctor {α β} (F : Set α -> Set β) {{Ψ : Functor F}} : Set (lsuc α ⊔ β) where
  field
    fmap-id : ∀ {A} -> fmap {{Ψ}} (id {A = A}) ≗ id
    fmap-∘  : ∀ {A B C} {g : B -> C} {f : A -> B} -> fmap {{Ψ}} g ∘ fmap f ≗ fmap (g ∘ f)

Vec-VerifiedFunctor : ∀ {α n} -> VerifiedFunctor {α} (flip Vec n)
Vec-VerifiedFunctor = record
  { fmap-id = map-id
  ; fmap-∘  = sym ∘ map-∘ _ _
  }
