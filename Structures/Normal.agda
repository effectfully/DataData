module DataData.Structures.Normal where

open import DataData.Prelude
open import DataData.Structures.Traversable

infix 0 _/_
record Normal α : Set (lsuc α) where
  constructor _/_
  field
    Shape : Set α
    size  : Shape -> ℕ

  -- Should I call this "extension"? It's more like "flatten and extend".
  ⟦_⟧ₙ : ∀ {β} -> Set β -> Set (α ⊔ β)
  ⟦_⟧ₙ A = ∃ λ sh -> Vec A (size sh)
open Normal public

module _ {α} {{F : Normal α}} where
  -- Makes instance search ambiguous somehow. Wrap extension in a record?
  -- instance
    Normal<:Traversable-⟦⟧ : ∀ {β} -> Traversable {α ⊔ β} ⟦ F ⟧ₙ
    Normal<:Traversable-⟦⟧ = record { traverse = λ{ f (sh , v) -> ,_ ⟨$⟩ traverse f v } }

-- []; () ∷ []; () ∷ () ∷ []; ...
ListN : Normal _
ListN = ℕ / id

-- For any `n' there is only one shape of type (Vec () n).
VecN : ℕ -> Normal _
VecN n = ⊤ / const n

Kₙ : ∀ {α} -> Set α -> Normal _
Kₙ A = A / const 0

_⊎ₙ_ : ∀ {α β} -> Normal α -> Normal β -> Normal (α ⊔ β)
(Sh₁ / s₁) ⊎ₙ (Sh₂ / s₂) = Sh₁ ⊎ Sh₂ / [ s₁ , s₂ ]

_×ₙ_ : ∀ {α β} -> Normal α -> Normal β -> Normal (α ⊔ β)
(Sh₁ / s₁) ×ₙ (Sh₂ / s₂) = Sh₁ × Sh₂ / uncurry _+_ ∘ pmap s₁ s₂

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
unpairₙ F₁ ((sh₁ , sh₂) , v₁₂) = case splitAt (size F₁ sh₁) v₁₂ of
  λ{ (v₁ , v₂ , _) -> (sh₁ , v₁) , (sh₂ , v₂) }

injₙ-surj : ∀ {α} {A : Set α} {F₁ F₂ : Normal α} -> (p : ⟦ F₁ ⊎ₙ F₂ ⟧ₙ A) -> injₙ ⁻¹ p ≈ uninjₙ p
injₙ-surj (inj₁ sh , v₁) = beta
injₙ-surj (inj₂ sh , v₂) = beta

unpairₙ-surj : ∀ {α} {A : Set α} (F₁ {F₂} : Normal α)
             -> (p : ⟦ F₁ ×ₙ F₂ ⟧ₙ A) -> pairₙ ⁻¹ p ≈ unpairₙ F₁ p
unpairₙ-surj F₁ ((sh₁ , sh₂) , v₁₂) with splitAt (size F₁ sh₁) v₁₂
... | v₁ , v₂ , p rewrite p = beta

instance
  ListN-Monoid : ∀ {α} {A : Set α} -> Monoid (⟦ ListN ⟧ₙ A)
  ListN-Monoid = record
    { ε   = , []
    ; _∙_ = zip _+_ _++_
    }

-- `F₂' is not used in the second argument of _/_ at all.
_∘ₙ_ : ∀ {α β} -> Normal α -> Normal β -> Normal (α ⊔ β)
F₂ ∘ₙ (Sh₁ / s₁) = ⟦ F₂ ⟧ₙ Sh₁ / unSum ∘ foldMap (Sum ∘ s₁) ∘ proj₂

sizeₜ : ∀ {α A} {F : Set α -> Set α} {{Ψ : Traversable F}} -> F A -> ℕ
sizeₜ = unSum ∘ foldMap (Sum ∘ const 1)

-- Extension of a `Traversable' is `Traversable'.
instance
  -- `Traversable' is enough.
  Traversable<:Normal : ∀ {α} {F : Set α -> Set α} {{Ψ : Traversable F}} -> Normal α
  Traversable<:Normal {F = F} = F (Lift ⊤) / sizeₜ

-- Seems not nice to use `traverse' instead of `fmap'.
-- But making `Traverse<:Functor' an instance would introduce ambiguity.
shapeₜ : ∀ {α A} {F : Set α -> Set α} {{Ψ : Traversable F}} -> F A -> F (Lift ⊤)
shapeₜ = traverse (const _)

contentsₜ : ∀ {α A} {F : Set α -> Set α} {{Ψ : Traversable F}} -> F A -> ⟦ ListN ⟧ₙ A
contentsₜ = foldMap (λ x -> , x ∷ [])

-- fromTraversable : ∀ {α A} {F : Set α -> Set α} {{Ψ : Traversable F}}
--                 -> F A -> ⟦ Traversable<:Normal ⟧ₙ A
-- fromTraversable x = shapeₜ x , {!proj₂ (contentsₜ x)!}

-- Reads somewhat backwards: `F₂' extended with references to `F₁'.
_->ₙ_ : ∀ {α β} -> Normal α -> Normal β -> Set (α ⊔ β)
F₁ ->ₙ F₂ = ∀ sh₁ -> ⟦ F₂ ⟧ₙ (Fin (size F₁ sh₁))

⟨_⟩_∸>ₙ_ : ∀ {α β} ι -> Normal α -> Normal β -> Set (lsuc ι ⊔ α ⊔ β)
⟨ ι ⟩ F₁ ∸>ₙ F₂ = {I : Set ι} -> ⟦ F₁ ⟧ₙ I -> ⟦ F₂ ⟧ₙ I

-- (⟦ F₂ ⟧ₙ _) contains references to `F₁', (⟦ F₁ ⟧ I) contains `I' => (⟦ F₂ ⟧ I) contains `I'.
morphₙ : ∀ {α β} {F₁ : Normal α} {F₂ : Normal β} -> F₁ ->ₙ F₂ -> (∀ {ι} -> ⟨ ι ⟩ F₁ ∸>ₙ F₂)
morphₙ m (sh₁ , v₁) = pmap id (vmap (flip lookup v₁)) (m sh₁)

unmorphₙ : ∀ {α β} {F₁ : Normal α} {F₂ : Normal β} -> (∀ {ι} -> ⟨ ι ⟩ F₁ ∸>ₙ F₂) -> F₁ ->ₙ F₂
unmorphₙ m sh₁ = m (sh₁ , allFin _)

_⊗_ : ∀ {α β} -> Normal α -> Normal β -> Normal (α ⊔ β)
(Sh₁ / s₁) ⊗ (Sh₂ / s₂) = Sh₁ × Sh₂ / uncurry _*_ ∘ pmap s₁ s₂

swapₙ : ∀ {α β} {F₁ : Normal α} {F₂ : Normal β} -> (F₁ ⊗ F₂) ->ₙ (F₂ ⊗ F₁)
swapₙ {F₁ = F₁} {F₂ = F₂} (sh₁ , sh₂) rewrite CS.*-comm (size F₁ sh₁) (size F₂ sh₂)
                                            = (sh₂ , sh₁) , allFin _

-- dropₙ : ∀ {α β} {F₁ : Normal α} {F₂ : Normal β} -> (F₁ ⊗ F₂) ->ₙ (F₁ ∘ₙ F₂)
-- dropₙ (sh₁ , sh₂) = (sh₁ , replicate sh₂) , {!!}
