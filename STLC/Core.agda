module DataData.STLC.Core where

open import DataData.Prelude

infixl 10 _%
_% = _∘_

infixl 5 _▻_ _▻▻_ _<><_
infixr 5 _⇒_
infix  4 _∈_ _⊢_
infixl 4 _·_
infixl 9 _[_]

data Type : Set where
  ⋆   : Type
  _⇒_ : Type -> Type -> Type

data Con : Set where
  ε   : Con
  _▻_ : Con -> Type -> Con

data _∈_ σ : Con -> Set where
  vz : ∀ {Γ}   -> σ ∈ Γ ▻ σ
  vs : ∀ {Γ τ} -> σ ∈ Γ     -> σ ∈ Γ ▻ τ 

data _⊢_ Γ : Type -> Set where
  var : ∀ {σ}   -> σ ∈ Γ     -> Γ ⊢ σ
  ƛ_  : ∀ {σ τ} -> Γ ▻ σ ⊢ τ -> Γ ⊢ σ ⇒ τ
  _·_ : ∀ {σ τ} -> Γ ⊢ σ ⇒ τ -> Γ ⊢ σ     -> Γ ⊢ τ

_▻▻_ : Con -> Con -> Con
Γ ▻▻  ε      = Γ
Γ ▻▻ (Δ ▻ τ) = Γ ▻▻ Δ ▻ τ

_<><_ : Con -> Con -> Con
Γ <><  ε      = Γ
Γ <>< (Δ ▻ τ) = Γ ▻ τ <>< Δ

Ren : Con -> Con -> Set
Ren Γ Δ = ∀ {σ} -> σ ∈ Γ -> σ ∈ Δ

Sub : Con -> Con -> Set
Sub Γ Δ = ∀ {σ} -> σ ∈ Γ -> Δ ⊢ σ

Ren⁺ : Con -> Con -> Set
Ren⁺ Γ Δ = ∀ Ξ -> Ren (Γ <>< Ξ) (Δ <>< Ξ)

Sub⁺ : Con -> Con -> Set
Sub⁺ Γ Δ = ∀ Ξ -> Sub (Γ <>< Ξ) (Δ <>< Ξ)

_[_] : ∀ {Γ Δ σ} -> Γ ⊢ σ -> Sub⁺ Γ Δ -> Δ ⊢ σ
(var v) [ θ ] = θ ε v
(ƛ b  ) [ θ ] = ƛ (b [ θ ∘ (_▻ _) ])
(f · x) [ θ ] = f [ θ ] · x [ θ ]

-- When going under a lambda shift by one all variables except for the bound one.
keepʳ : ∀ {Γ Δ σ} -> Ren Γ Δ -> Ren (Γ ▻ σ) (Δ ▻ σ)
keepʳ r  vz    = vz
keepʳ r (vs v) = vs (r v)

keepʳ⁺ : ∀ {Γ Δ} -> Ren Γ Δ -> Ren⁺ Γ Δ
keepʳ⁺ r  ε      = r
keepʳ⁺ r (Ξ ▻ ν) = keepʳ⁺ (keepʳ r) Ξ

keepˢ : ∀ {Γ Δ σ} -> Sub Γ Δ -> Sub (Γ ▻ σ) (Δ ▻ σ)
keepˢ s  vz    = var vz
keepˢ s (vs v) = s v [ (λ Ξ -> var ∘ keepʳ⁺ vs Ξ) ]

keepˢ⁺ : ∀ {Γ Δ} -> Sub Γ Δ -> Sub⁺ Γ Δ
keepˢ⁺ s  ε      = s
keepˢ⁺ s (Ξ ▻ ν) = keepˢ⁺ (keepˢ s) Ξ

skipʳ : ∀ {Γ} Δ -> Ren Γ (Γ <>< Δ)
skipʳ  ε      v = v
skipʳ (Δ ▻ σ) v = skipʳ Δ (vs v)

wkᵛ : ∀ {Γ Δ} -> Ren Γ (Δ ▻▻ Γ)
wkᵛ  vz    = vz
wkᵛ (vs v) = vs (wkᵛ v)

wk : ∀ {Γ Δ σ} -> Γ ⊢ σ -> Δ ▻▻ Γ ⊢ σ
wk (var v) = var (wkᵛ v)
wk (ƛ b  ) = ƛ (wk b)
wk (f · x) = wk f · wk x

ren : ∀ {Γ Δ σ} -> Ren Γ Δ -> Γ ⊢ σ -> Δ ⊢ σ
ren r (var v) = var (r v)
ren r (ƛ b  ) = ƛ (ren (keepʳ r) b)
ren r (f · x) = ren r f · ren r x
