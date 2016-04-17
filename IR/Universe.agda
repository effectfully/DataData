module DataData.IR.Universe where

open import DataData.Prelude
open import DataData.Container.Indexed

mutual
  data Uᴴ {n} (U : Fin n -> Set) : Set where
    u   : Fin n -> Uᴴ U
    nat : Uᴴ U
    pi  : (a : Uᴴ U) -> (⟦ a ⟧ᴴ -> Uᴴ U) -> Uᴴ U

  ⟦_⟧ᴴ : ∀ {n U} -> Uᴴ {n} U -> Set
  ⟦_⟧ᴴ {U = U} (u i)    = U i
  ⟦_⟧ᴴ          nat     = ℕ
  ⟦_⟧ᴴ         (pi a f) = (x : ⟦ a ⟧ᴴ) -> ⟦ f x ⟧ᴴ

injectFromℕ : ∀ {m} n -> Fin (suc (n + m))
injectFromℕ  0      = fromℕ _
injectFromℕ (suc n) = inject₁ (injectFromℕ n)

mutual
  Predᴴ : ∀ {n} -> Fin n -> Set
  Predᴴ {suc n}  zero   = Setᴴ n
  Predᴴ         (suc i) = Predᴴ i

  Setᴴ : ℕ -> Set
  Setᴴ n = Uᴴ {n} Predᴴ

u′ : ∀ {m} n -> Setᴴ (suc (n + m))
u′ n = u (injectFromℕ n)

to-subst : ∀ {α β} {A : Set α} {x y : A}
         -> (B : A -> Set β) -> (f : ∀ x -> B x) -> (p : x ≡ y) -> subst B p (f x) ≡ f y
to-subst A f refl = refl

postulate
  ext : ∀ {α β} -> Extensionality α β

-- Or (⟦ ⇑ a ⟧ᴴ ≡ ⟦ a ⟧ᴴ).
mutual
  ⇑ : ∀ {n} -> Setᴴ n -> Setᴴ (suc n)
  ⇑ (u i)    = u (suc i)
  ⇑  nat     = nat
  ⇑ (pi a f) = pi (⇑ a) λ x -> ⇑ (f (uncoe a x))

  uncoe : ∀ {n} -> (a : Setᴴ n) -> ⟦ ⇑ a ⟧ᴴ -> ⟦ a ⟧ᴴ
  uncoe (u i)    s = s
  uncoe  nat     n = n
  uncoe (pi a f) h = λ x -> uncoe (f x)
    (subst (λ x -> ⟦ ⇑ (f x) ⟧ᴴ) (uncoe-coe a x)
                                        (h (coe a x)))

  coe : ∀ {n} -> (a : Setᴴ n) -> ⟦ a ⟧ᴴ -> ⟦ ⇑ a ⟧ᴴ
  coe (u i)    s = s
  coe  nat     n = n
  coe (pi a f) h = λ x -> coe (f (uncoe a x)) (h (uncoe a x))

  uncoe-coe : ∀ {n} -> (a : Setᴴ n) -> (x : ⟦ a ⟧ᴴ) -> uncoe a (coe a x) ≡ x
  uncoe-coe (u i)    s = refl
  uncoe-coe  nat     n = refl
  uncoe-coe (pi a f) h = ext λ x ->
    trans (cong (uncoe (f x))
                (to-subst (λ x -> ⟦ ⇑ (f x) ⟧ᴴ)
                          (λ x -> coe (f x) (h x))
                          (uncoe-coe a x)))
          (uncoe-coe (f x) (h x))

private
  ex₀ : Setᴴ 0
  ex₀ = nat

  ex₁ : Setᴴ 1
  ex₁ = nat

  ex₂ : Setᴴ 1
  ex₂ = pi (u′ 0) λ a -> ⇑ a
  
  ex₃ : Setᴴ 3
  ex₃ = pi (u′ 0) λ a -> ⇑ (⇑ (⇑ a))

  ex₄ : Setᴴ 3
  ex₄ = pi (u′ 1) λ a -> ⇑ (⇑ a)

  ex₅ : Setᴴ 3
  ex₅ = pi (u′ 2) λ a -> ⇑ a
