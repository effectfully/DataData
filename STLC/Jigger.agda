module DataData.STLC.Jigger where

open import DataData.Prelude
open import DataData.STLC.Basic

instance
  irefl : ∀ {α} {A : Set α} {x : A} -> x ≡ x
  irefl = refl

infixl 5 _<>>_
infixr 5 _⇒ⁿ_
infix  9 _#_

_<>>_ : Con -> Con -> Con
ε       <>> Δ = Δ
(Γ ▻ σ) <>> Δ = Γ <>> (Δ ▻ σ)

chips-chips : ∀ Γ Δ -> Γ <>> Δ <>> ε ≡ Δ <>> Γ
chips-chips  ε      Δ = refl
chips-chips (Γ ▻ σ) Δ = chips-chips Γ (Δ ▻ σ)

unchips : ∀ Γ Δ -> Γ <>> ε ≡ Δ <>> ε -> Γ ≡ Δ
unchips Γ Δ p =
  begin
    Γ             ←⟨ chips-chips Γ ε ⟩
    Γ <>> ε <>> ε →⟨ cong (_<>> ε) p ⟩
    Δ <>> ε <>> ε →⟨ chips-chips Δ ε ⟩
    Δ
  ∎

lem : ∀ Γ Δ Ξ -> Δ <>> ε ≡ Γ <>> Ξ -> Γ <>< Ξ ≡ Δ
lem Γ Δ  ε      p = unchips Γ Δ (sym p)
lem Γ Δ (Ξ ▻ ν) p = lem (Γ ▻ ν) Δ Ξ p

CoN : ℕ -> Set
CoN  0      = ⊤
CoN (suc n) = CoN n × Type

_⇒ⁿ_ : ∀ {n} -> CoN n -> Type -> Type
_⇒ⁿ_ {0}      _      τ = τ
_⇒ⁿ_ {suc n} (Γ , σ) τ = σ ⇒ Γ ⇒ⁿ τ

Bound : Con -> Type -> Set
Bound Γ σ = ∀ {Δ Ξ} {{_ : Δ <>> ε ≡ Γ <>> (Ξ ▻ σ)}} -> Δ ⊢ σ

Bind : ∀ {n} -> Con -> CoN n -> Type -> Set
Bind {0}     Γ  _      σ = Γ ⊢ σ
Bind {suc n} Γ (Δ , τ) σ = Bound Γ τ -> Bind (Γ ▻ τ) Δ σ

_#_ : ∀ n {Γ} {Δ : CoN n} {σ} -> Bind Γ Δ σ -> Γ ⊢ Δ ⇒ⁿ σ
_#_  0                  b = b
_#_ (suc n) {Γ} {Δ , τ} b = ƛ (n # b (λ {Δ' Ξ} {{p}} -> subst (_⊢ τ) (lem Γ Δ' (Ξ ▻ τ) p) (var (skip Ξ vz))))

private
  A : ε ⊢ ((⋆ ⇒ ⋆) ⇒ ⋆ ⇒ ⋆)
  A = 2 # λ f x → f · x
