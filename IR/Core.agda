module DataData.IR.Core where

open import DataData.Prelude

module _ {α} {A : Set α} (_≟_ : Decidable (_≡_ {A = A})) where
  mutual
    data FreshList : Set α where
      []ᶠ  : FreshList
      _∷ᶠ_ : ∀ x xs {_ : T (fresh? x xs)} -> FreshList

    fresh? : A -> FreshList -> Bool
    fresh? y  []ᶠ      = true
    fresh? y (x ∷ᶠ xs) = ⌊ x ≟ y ⌋ ∧ fresh? y xs

data Recʳ : Set₁ where
  ⟨⟩ʳ  : Recʳ
  _,ʳ_ : (A : Set) -> (A -> Recʳ) -> Recʳ

⟦_⟧ʳ : Recʳ -> Set
⟦ ⟨⟩ʳ    ⟧ʳ = ⊤
⟦ A ,ʳ F ⟧ʳ = ∃ λ x -> ⟦ F x ⟧ʳ

Sizeʳ : ∀ {R} -> ⟦ R ⟧ʳ -> ℕ
Sizeʳ {⟨⟩ʳ}     _      = 0
Sizeʳ {A ,ʳ F} (x , r) = suc (Sizeʳ r)

typeʳ : ∀ {R} -> (r : ⟦ R ⟧ʳ) -> Fin (Sizeʳ r) -> Set
typeʳ {⟨⟩ʳ}     _       ()
typeʳ {A ,ʳ F} (x , r)  zero   = A
typeʳ {A ,ʳ F} (x , r) (suc i) = typeʳ r i

valʳ : ∀ {R} -> (r : ⟦ R ⟧ʳ) -> (i : Fin (Sizeʳ r)) -> typeʳ r i
valʳ {⟨⟩ʳ}     _       ()
valʳ {A ,ʳ F} (x , r)  zero   = x
valʳ {A ,ʳ F} (x , r) (suc i) = valʳ r i

mutual
  data Recˡ : Set₁ where
    ⟨⟩ˡ  : Recˡ
    _,ˡ_ : ∀ R -> (⟦ R ⟧ˡ -> Set) -> Recˡ

  ⟦_⟧ˡ : Recˡ -> Set
  ⟦ ⟨⟩ˡ    ⟧ˡ = ⊤
  ⟦ A ,ˡ F ⟧ˡ = ∃ F

Sizeˡ : Recˡ -> ℕ
Sizeˡ  ⟨⟩ˡ     = 0
Sizeˡ (R ,ˡ F) = suc (Sizeˡ R)

typeˡ : ∀ {R} -> Fin (Sizeˡ R) -> (r : ⟦ R ⟧ˡ) -> Set
typeˡ {⟨⟩ˡ}     ()      _
typeˡ {R ,ˡ F}  zero   (r , x) = F r
typeˡ {R ,ˡ F} (suc i) (r , x) = typeˡ i r

valˡ : ∀ {R} -> (i : Fin (Sizeˡ R)) -> (r : ⟦ R ⟧ˡ) -> typeˡ i r
valˡ {⟨⟩ˡ}     ()      _
valˡ {R ,ˡ F}  zero   (r , x) = x
valˡ {R ,ˡ F} (suc i) (r , x) = valˡ i r

Truncˡ : ∀ R -> Fin (Sizeˡ R) -> Recˡ
Truncˡ  ⟨⟩ˡ      ()
Truncˡ (R ,ˡ F)  zero   = R
Truncˡ (R ,ˡ F) (suc i) = Truncˡ R i

truncˡ : ∀ {R} -> (i : Fin (Sizeˡ R)) -> ⟦ R ⟧ˡ -> ⟦ Truncˡ R i ⟧ˡ
truncˡ {⟨⟩ˡ}     ()      _
truncˡ {R ,ˡ F}  zero   (r , x) = r
truncˡ {R ,ˡ F} (suc i) (r , x) = truncˡ i r
