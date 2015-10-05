module DataData.STLC.NbE where

open import DataData.Prelude
open import DataData.STLC.Basic
open import DataData.STLC.Jigger
open import DataData.STLC.Hereditary hiding (norm)

infix 4 _↦_

data Stop Γ τ : Set where
  var : τ ∈ Γ -> Stop Γ τ
  app : ∀ {σ} -> Stop Γ (σ ⇒ τ) -> Γ ⊨ σ -> Stop Γ τ

renˢ : ∀ {Γ Δ τ} -> Ren Γ Δ -> Stop Γ τ -> Stop Δ τ
renˢ r (var v)   = var (r v)
renˢ r (app f n) = app (renˢ r f) (renⁿᶠ r n)

-- Fully apply partially applied `Stop'.
appˢ* : ∀ {Γ τ} -> Stop Γ τ -> Γ ⊨* τ -> Γ ⊨ ⋆
appˢ* (var v)   s = app v s
appˢ* (app f n) s = appˢ* f (n ◁ s)

mutual
  Val : Con -> Type -> Set
  Val Γ τ = Go Γ τ ⊎ Stop Γ τ

  Kripke : Con -> Type -> Type -> Set
  Kripke Γ σ τ = ∀ {Δ} -> Ren Γ Δ -> Val Δ σ -> Val Δ τ

  Go : Con -> Type -> Set
  Go Γ  ⋆      = ⊥
  Go Γ (σ ⇒ τ) = Kripke Γ σ τ

renᵏ : ∀ {Γ Δ σ τ} -> Ren Γ Δ -> Kripke Γ σ τ -> Kripke Δ σ τ
renᵏ r₁ k r₂ = k (r₂ ∘ r₁)

renᵍ : ∀ {τ Γ Δ} -> Ren Γ Δ -> Go Γ τ -> Go Δ τ
renᵍ {⋆}     r ()
renᵍ {_ ⇒ _} r k  = renᵏ r k

renᵛ : ∀ {Γ Δ τ} -> Ren Γ Δ -> Val Γ τ -> Val Δ τ
renᵛ r = smap (renᵍ r) (renˢ r)

ηˢ : ∀ {Γ τ} -> Stop Γ τ -> Γ ⊨ τ
ηˢ s = η* (λ Δ -> appˢ* (renˢ (skip Δ) s))

readback : ∀ {τ Γ} -> Val Γ τ -> Γ ⊨ τ
readback         (inj₂ s ) = ηˢ s
readback {⋆}     (inj₁ ())
readback {τ ⇒ ν} (inj₁ k ) = lam (readback (k vs (inj₂ (var vz))))

apply : ∀ {Γ σ τ} -> Val Γ (σ ⇒ τ) -> Val Γ σ -> Val Γ τ
apply (inj₁ k) x = k id x
apply (inj₂ f) x = inj₂ (app f (readback x))

data _↦_ : Con -> Con -> Set where
  Ø   : ∀ {Γ}     -> ε ↦ Γ
  _▷_ : ∀ {Γ Δ σ} -> Γ ↦ Δ -> Val Δ σ -> Γ ▻ σ ↦ Δ

lookupᵉ : ∀ {Γ Δ σ} -> σ ∈ Γ -> Γ ↦ Δ -> Val Δ σ
lookupᵉ  vz    (ρ ▷ x) = x
lookupᵉ (vs v) (ρ ▷ x) = lookupᵉ v ρ

renᵉ : ∀ {Γ Δ Ξ} -> Ren Δ Ξ -> Γ ↦ Δ -> Γ ↦ Ξ
renᵉ r  Ø      = Ø
renᵉ r (ρ ▷ x) = renᵉ r ρ ▷ renᵛ r x

idᵉ : ∀ {Γ} -> Γ ↦ Γ
idᵉ {ε}     = Ø
idᵉ {Γ ▻ σ} = renᵉ vs idᵉ ▷ inj₂ (var vz)

⟦_⟧ : ∀ {Γ Δ τ} -> Γ ⊢ τ -> Γ ↦ Δ -> Val Δ τ
⟦ var v ⟧ ρ = lookupᵉ v ρ
⟦ ƛ b   ⟧ ρ = inj₁ (λ r x -> ⟦ b ⟧ (renᵉ r ρ ▷ x))
⟦ f · x ⟧ ρ = apply (⟦ f ⟧ ρ) (⟦ x ⟧ ρ)

norm : ∀ {Γ τ} -> Γ ⊢ τ -> Γ ⊨ τ
norm t = readback (⟦ t ⟧ idᵉ)

private
  try₁ : ε ⊨ ((⋆ ⇒ ⋆) ⇒ (⋆ ⇒ ⋆)) ⇒ (⋆ ⇒ ⋆) ⇒ (⋆ ⇒ ⋆)
  try₁ = norm (1 # λ x → x)

  church₂ : ∀ {σ} -> ε ⊢ ((σ ⇒ σ) ⇒ σ ⇒ σ)
  church₂ = 2 # λ f x → f · (f · x)

  try₂ : ε ⊨ (⋆ ⇒ ⋆) ⇒ (⋆ ⇒ ⋆)
  try₂ = norm (church₂ · church₂ · church₂)
