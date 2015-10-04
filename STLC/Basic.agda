module DataData.STLC.Basic where

open import DataData.Prelude

infixl 5 _▻_ _<><_
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

Ren : Con -> Con -> Set
Ren Γ Δ = ∀ {σ} -> σ ∈ Γ -> σ ∈ Δ

Sub : Con -> Con -> Set
Sub Γ Δ = ∀ {σ} -> σ ∈ Γ -> Δ ⊢ σ

infixl 5 _▻▻_

_▻▻_ : Con -> Con -> Con
Γ ▻▻  ε      = Γ
Γ ▻▻ (Δ ▻ τ) = Γ ▻▻ Δ ▻ τ

_<><_ : Con -> Con -> Con
Γ <><  ε      = Γ
Γ <>< (Δ ▻ τ) = Γ ▻ τ <>< Δ

Ren⁺ : Con -> Con -> Set
Ren⁺ Γ Δ = ∀ Ξ -> Ren (Γ <>< Ξ) (Δ <>< Ξ)

Sub⁺ : Con -> Con -> Set
Sub⁺ Γ Δ = ∀ Ξ -> Sub (Γ <>< Ξ) (Δ <>< Ξ)

_[_] : ∀ {Γ Δ σ} -> Γ ⊢ σ -> Sub⁺ Γ Δ -> Δ ⊢ σ
(var v) [ θ ] = θ ε v
(ƛ b  ) [ θ ] = ƛ (b [ θ ∘ (_▻ _) ])
(f · x) [ θ ] = f [ θ ] · x [ θ ]

wkr : ∀ {Γ Δ σ} -> Ren Γ Δ -> Ren (Γ ▻ σ) (Δ ▻ σ)
wkr r  vz    = vz
wkr r (vs v) = vs (r v)

ren⁺ : ∀ {Γ Δ} -> Ren Γ Δ -> Sub⁺ Γ Δ
ren⁺ r  ε      = var ∘ r
ren⁺ r (Ξ ▻ ν) = ren⁺ (wkr r) Ξ

wks : ∀ {Γ Δ σ} -> Sub Γ Δ -> Sub (Γ ▻ σ) (Δ ▻ σ)
wks s  vz    = var vz
wks s (vs v) = s v [ ren⁺ vs ]

sub⁺ : ∀ {Γ Δ} -> Sub Γ Δ -> Sub⁺ Γ Δ
sub⁺ s  ε      = s
sub⁺ s (Ξ ▻ ν) = sub⁺ (wks s) Ξ
