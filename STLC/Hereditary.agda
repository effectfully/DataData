module DataData.STLC.Hereditary where

open import DataData.Prelude
open import DataData.STLC.Core
open import DataData.STLC.Jigger

infixr 5 _◁_
infix  4 _⊨_ _⊨*_
infixl 8 _∸_

-- Looks weird. We represent variables as (app v Ø).
-- What if we add the `var' constructor in _⊨_,
-- make `app' receive only functions and make spines non-empty?
-- Perhaps we will just introduce boilerplate.
mutual
  data _⊨_ Γ : Type -> Set where
    lam : ∀ {σ τ} -> Γ ▻ σ ⊨ τ -> Γ ⊨ σ ⇒ τ
    -- E.g. having (v : σ ⇒ τ ⇒ ⋆ ∈ Γ) (x : Γ ⊨ σ) (y : Γ ⊨ τ): app v (x ◁ y ◁ Ø).
    -- In (app v s) the type of `v' always ends with `⋆'.
    app : ∀ {σ} -> σ ∈ Γ -> Γ ⊨* σ -> Γ ⊨ ⋆

  data _⊨*_ Γ : Type -> Set where
    Ø   : Γ ⊨* ⋆
    _◁_ : ∀ {σ τ} -> Γ ⊨ σ -> Γ ⊨* τ -> Γ ⊨* σ ⇒ τ

mutual
  renⁿᶠ : ∀ {Γ Δ σ} -> Ren Γ Δ -> Γ ⊨ σ -> Δ ⊨ σ
  renⁿᶠ r (lam n)   = lam (renⁿᶠ (keepʳ r) n)
  renⁿᶠ r (app v s) = app (r v) (ren* r s)

  ren* : ∀ {Γ Δ σ} -> Ren Γ Δ -> Γ ⊨* σ -> Δ ⊨* σ
  ren* r  Ø      = Ø
  ren* r (n ◁ s) = renⁿᶠ r n ◁ ren* r s

-- Remove a type from a context.
_∸_ : ∀ {σ} Γ -> σ ∈ Γ -> Con
(Γ ▻ σ) ∸ vz   = Γ
(Γ ▻ τ) ∸ vs v = Γ ∸ v ▻ τ

-- Let (Δ ≡ Γ ∸ v) so (w : τ ∈ Δ). We extend `Δ' to get `Γ',
-- and `v' points to somewhere in this extended context.
-- If `v' is after `w', then `w' remains the same.
-- If `v' is inserted before or in the place of `w', then shift `w' by one.
-- So `v' and (thin v w) are always distinct, hence the `diff' case in `Eqᵥ' below.
thin : ∀ {Γ σ τ} -> (v : σ ∈ Γ) -> τ ∈ Γ ∸ v -> τ ∈ Γ
thin  vz     w     = vs w
thin (vs v)  vz    = vz
thin (vs v) (vs w) = vs (thin v w)

data Eqᵥ {Γ σ} (v : σ ∈ Γ) : ∀ {τ} -> τ ∈ Γ -> Set where
  same : Eqᵥ v v
  diff : ∀ {τ} -> (w : τ ∈ Γ ∸ v) -> Eqᵥ v (thin v w)

-- The (suc <$> thick v w) part.
wkᵉ : ∀ {Γ σ τ ν} {v : σ ∈ Γ} {w : τ ∈ Γ} -> Eqᵥ v w -> Eqᵥ (vs {τ = ν} v) (vs {τ = ν} w)
wkᵉ  same    = same
wkᵉ (diff w) = diff (vs w)

_≟ᵥ_ : ∀ {Γ σ τ} -> (v : σ ∈ Γ) -> (w : τ ∈ Γ) -> Eqᵥ v w
vz   ≟ᵥ vz   = same
vz   ≟ᵥ vs w = diff w
vs v ≟ᵥ vz   = diff vz
vs v ≟ᵥ vs w = wkᵉ (v ≟ᵥ w)

mutual
  -- Substitute `v' for `n', which doesn't contain `v', in `m',
  -- which can contain `v', such that the result doesn't contain `v'.
  ⟨_↦_⟩ : ∀ {Γ σ τ} -> (v : σ ∈ Γ) -> Γ ∸ v ⊨ σ -> Γ ⊨ τ -> Γ ∸ v ⊨ τ
  ⟨ v ↦ n ⟩ (lam b  ) = lam (⟨ vs v ↦ renⁿᶠ vs n ⟩ b)
  ⟨ v ↦ n ⟩ (app w s) with ⟨ v ↦ n ⟩* s -- Apply the substitution recursively.
  ... | s' with w | v ≟ᵥ w
  ... | ._ | same    = app* n s' -- The domino effect.
  ... | ._ | diff w' = app w' s' -- `w'' is `w' after the context was cut.

  ⟨_↦_⟩* : ∀ {Γ σ τ} -> (v : σ ∈ Γ) -> Γ ∸ v ⊨ σ -> Γ ⊨* τ -> Γ ∸ v ⊨* τ
  ⟨ v ↦ n ⟩*  Ø      = Ø
  ⟨ v ↦ n ⟩* (m ◁ s) = ⟨ v ↦ n ⟩ m ◁ ⟨ v ↦ n ⟩* s

  app* : ∀ {Γ σ} -> Γ ⊨ σ -> Γ ⊨* σ -> Γ ⊨ ⋆
  app* n  Ø      = n
  app* f (m ◁ s) = app* (app₁ f m) s

  -- If a term in normal form has functional type, then it's a lambda
  -- (because applications receive whole spines), and we can substitute.
  app₁ : ∀ {Γ σ τ} -> Γ ⊨ σ ⇒ τ -> Γ ⊨ σ -> Γ ⊨ τ
  app₁ (lam b) n = ⟨ vz ↦ n ⟩ b

-- Differs from Conor's version.
-- It's easy to derive this mechanically:
-- we need to prepend some lambdas and hence to shift the original variable;
-- we need to apply this shifted variable to η-expanded (vz) (vs vz) (vs vs vz)...
-- in reverse order; applying and shifting is (λ Δ -> app (skip Δ v)),
-- which has this type: (∀ Δ -> Γ <>< Δ ⊨* σ -> Γ <>< Δ ⊨ ⋆);
-- then we write `η*' with the expected type signature and everything just fits.
mutual
  η : ∀ {σ Γ} -> σ ∈ Γ -> Γ ⊨ σ
  η v = η* (λ Δ -> app (skipʳ Δ v))

  η* : ∀ {σ Γ} -> (∀ Δ -> Γ <>< Δ ⊨* σ -> Γ <>< Δ ⊨ ⋆) -> Γ ⊨ σ
  η* {⋆}     c = c ε Ø
  η* {σ ⇒ τ} c = lam (η* (λ Δ s -> c (Δ ▻ σ) (η (skipʳ Δ vz) ◁ s)))

norm : ∀ {Γ σ} -> Γ ⊢ σ -> Γ ⊨ σ
norm (var v) = η v
norm (ƛ b  ) = lam (norm b)
norm (f · x) = app₁ (norm f) (norm x)

private
  try₁ : ε ⊨ ((⋆ ⇒ ⋆) ⇒ (⋆ ⇒ ⋆)) ⇒ (⋆ ⇒ ⋆) ⇒ (⋆ ⇒ ⋆)
  try₁ = norm (1 # λ x → x)

  church₂ : ∀ {σ} -> ε ⊢ ((σ ⇒ σ) ⇒ σ ⇒ σ)
  church₂ = 2 # λ f x → f · (f · x)

  try₂ : ε ⊨ (⋆ ⇒ ⋆) ⇒ (⋆ ⇒ ⋆)
  try₂ = norm (church₂ · church₂ · church₂)
