module DataData.Structures.VerifiedTraversable where

open import DataData.Prelude
open import DataData.Structures.Traversable
open import DataData.Structures.Normal
open import DataData.Structures.VerifiedFunctor

module _ {α β} (F : Set α -> Set β) {{Ψ : Applicative F}} where
  infixl 5 _⟨⋆⟩_
  _⟨⋆⟩_ = _⟨*⟩_ {{Ψ}}

  record VerifiedApplicative : Set (lsuc α ⊔ β) where
    field
      aid   : ∀ {A} {x : F A}            -> point id ⟨⋆⟩ x      ≡ x
      ahom  : ∀ {A B x} {f : A -> B}     -> point f ⟨⋆⟩ point x ≡ point (f x)
      aint  : ∀ {A B x} {f : F (A -> B)} -> f ⟨⋆⟩ point x       ≡ point (_$ x) ⟨⋆⟩ f
      acomp : ∀ {A B C x} {g : F (B -> C)} {f : F (A -> B)}
            -> point _∘′_ ⟨⋆⟩ g ⟨⋆⟩ f ⟨⋆⟩ x ≡ g ⟨⋆⟩ (f ⟨⋆⟩ x)
  open VerifiedApplicative {{...}} public

  VerifiedApplicative<:VerifiedFunctor : {{Ψᵥ : VerifiedApplicative}} -> VerifiedFunctor F
  VerifiedApplicative<:VerifiedFunctor = record
    { fmap-id = λ _ -> aid
    ; fmap-∘  = λ {_ _ _ g f} x ->
        begin
          point g ⟨⋆⟩ (point f ⟨⋆⟩ x)              ←⟨ acomp                                      ⟩
          point _∘′_ ⟨⋆⟩ point g ⟨⋆⟩ point f ⟨⋆⟩ x →⟨ cong (λ ⟨h⟩ -> ⟨h⟩ ⟨⋆⟩ point f ⟨⋆⟩ x) ahom ⟩
          point (g ∘′_) ⟨⋆⟩ point f ⟨⋆⟩ x          →⟨ cong (_⟨⋆⟩ x) ahom                         ⟩
          point (g ∘′ f) ⟨⋆⟩ x
        ∎
    }

_∸>_ : ∀ {α β γ} -> (Set α -> Set β) -> (Set α -> Set γ) -> Set (lsuc α ⊔ β ⊔ γ)
F ∸> G = ∀ {A} -> F A -> G A 

record ApplicativeHom {α β γ} (F : Set α -> Set β) (G : Set α -> Set γ)
                      {{Ψ : Applicative F}} {{Φ : Applicative G}}
                      (η : F ∸> G) : Set (lsuc α ⊔ β ⊔ γ) where
  field
    resp-point : ∀ {A} {x : A} -> η (point x) ≡ point x
    resp-⊛     : ∀ {A B x} {f : F (A -> B)} -> η (f ⟨*⟩ x) ≡ η f ⟨*⟩ η x

MonoidHom<:ApplicativeHom : ∀ {α β γ} {A : Set α} {B : Set β} {M : Monoid A} {N : Monoid B}
                              {f : A -> B} {{MH : MonoidHom A B f}}
                          -> ApplicativeHom {γ} (Constᵣ A) (Constᵣ B) (Const ∘ f ∘ unConst)
MonoidHom<:ApplicativeHom {A = A} = record
  { resp-point = cong Const (resp-ε {A = A})
  ; resp-⊛     = cong Const (resp-∙ {A = A})
  }

module _ {α β γ} {F : Set α -> Set β} {G : Set α -> Set γ}
         {{Ψ : Applicative F}} {{Φ : Applicative G}} (η : F ∸> G) where

  ap : ∀ {A B} -> F (A -> B) ⊎ G (A -> B) -> F A ⊎ G A -> F B ⊎ G B
  ap (inj₁ f) (inj₁ x) = inj₁ (f   ⟨*⟩   x)
  ap (inj₁ f) (inj₂ x) = inj₂ (η f ⟨*⟩   x)
  ap (inj₂ f) (inj₁ x) = inj₂ (f   ⟨*⟩ η x)
  ap (inj₂ f) (inj₂ x) = inj₂ (f   ⟨*⟩   x)

  homSum : Applicative (_⊎_ ∘ F ˢ G)
  homSum = record
    { pointed = record { point = inj₁ ∘ point }
    ; _⟨*⟩_   = ap
    }
