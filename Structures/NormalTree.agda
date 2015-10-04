module DataData.Structures.NormalTree where

open import DataData.Prelude
open import DataData.Structures.Normal

-- Should it be called `Rose'?
data Tree {α} (F : Normal α) : Set α where
  ⟨_⟩ : ⟦ F ⟧ₙ (Tree F) -> Tree F

⟨⟩-inj : ∀ {α} {F : Normal α} {p₁ p₂ : ⟦ F ⟧ₙ (Tree F)} -> ⟨ p₁ ⟩ ≡ ⟨ p₂ ⟩ -> p₁ ≡ p₂
⟨⟩-inj refl = refl 

NatT : Normal lzero
NatT = Bool / (if_then 0 else 1)

zeroT : Tree NatT
zeroT = ⟨ true , [] ⟩

sucT : Tree NatT -> Tree NatT
sucT n = ⟨ false , n ∷ [] ⟩

elim-NatT : ∀ {π} -> (P : Tree NatT -> Set π) -> (∀ {n} -> P n -> P (sucT n)) -> P zeroT -> ∀ n -> P n
elim-NatT P f z ⟨ true  , []     ⟩ = z
elim-NatT P f z ⟨ false , n ∷ [] ⟩ = f (elim-NatT P f z n)

elim-Tree : ∀ {α π} {F : Normal α} {P : Tree F -> Set π}
          -> (∀ sh -> (ts : Vec (Tree F) (size F sh)) -> All P ts -> P ⟨ sh , ts ⟩) -> ∀ t -> P t
elim-Tree {P = P} f ⟨ sh , ts ⟩ = f sh ts (map-elim-Tree ts) where
  map-elim-Tree : ∀ {n} -> (ts : Vec _ n) -> All P ts
  map-elim-Tree  []      = []ₐ
  map-elim-Tree (t ∷ ts) = elim-Tree f t ∷ₐ map-elim-Tree ts

eq-by : ∀ {α} {F : Normal α} -> Decidable (_≡_ {A = Shape F}) -> Decidable (_≡_ {A = Tree F})
eq-by {F = F} eq ⟨ sh₁ , ts₁ ⟩ ⟨ sh₂ , ts₂ ⟩ =
  dcong ⟨_⟩ ⟨⟩-inj (idcong (Vec _ ∘ size F) ,_ ,-inj (eq _ _) (fold-eq _ _)) where
    fold-eq : ∀ {n} -> Decidable (_≡_ {A = Vec (Tree F) n})
    fold-eq  []         []        = yes refl
    fold-eq (t₁ ∷ ts₁) (t₂ ∷ ts₂) = dcong₂ _∷_ ∷-inj (eq-by eq t₁ t₂) (fold-eq ts₁ ts₂)
