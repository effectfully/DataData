module DataData.Container.MuDesc where

open import DataData.Prelude

infixr 6 _<&>_

data Desc {ι} (I : Set ι) : Set (lsuc ι) where
  var   : I -> Desc I
  κ     : Set ι -> Desc I
  σ π   : {A : Set ι} -> (A -> Desc I) -> Desc I
  _<&>_ : Desc I -> Desc I -> Desc I
  μ     : {J : Set ι} -> (J -> Desc (I ⊎ J)) -> J -> Desc I

mutual
  ⟦_⟧ᴰ : ∀ {ι} {I : Set ι} -> Desc I -> (I -> Set ι) -> Set ι
  ⟦ var i     ⟧ᴰ A = A i
  ⟦ κ A       ⟧ᴰ _ = A
  ⟦ σ f       ⟧ᴰ A = ∃ λ x -> ⟦ f x ⟧ᴰ A
  ⟦ π f       ⟧ᴰ A = ∀   x -> ⟦ f x ⟧ᴰ A
  ⟦ d₁ <&> d₂ ⟧ᴰ A = ⟦ d₁ ⟧ᴰ A × ⟦ d₂ ⟧ᴰ A
  ⟦ μ f j     ⟧ᴰ A = Data f A j

  record Data {ι} {I J : Set ι} (f : J -> Desc (I ⊎ J)) (A : I -> Set ι) (j : J) : Set ι where
    inductive
    constructor ⟨_⟩
    field unData : ⟦ f j ⟧ᴰ [ A , Data f A ]
