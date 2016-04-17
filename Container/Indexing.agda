module DataData.Container.Indexing where

open import DataData.Prelude
open import DataData.Container.Desc

infix 4 [_]_!_ _!!_

idesc : ∀ {ι α} {I : Set ι} -> Desc I α -> Desc I α
idesc (var v)     = κ (Lift ⊤)
idesc (κ A)       = κ (Lift ⊥)
idesc (σ A B)     = π A (λ x -> idesc (B x))
idesc (π A B)     = σ A (λ x -> idesc (B x))
idesc (d₁ <&> d₂) = idesc d₁ <|> idesc d₂

index : ∀ {ι α} {I : Set ι} {A B : I -> Set α}
      -> (d : Desc I α) -> ⟦ d ⟧ᴰ A -> ⟦ idesc d ⟧ᴰ B -> I
index (var v)      x       i               = v
index (κ A)        x      (lift())
index (σ A B)     (x , y)  f               = index (B x) y (f x)
index (π A B)      f      (x , i)          = index (B x) (f x) i
index (d₁ <&> d₂) (x , y) (lift true  , i) = index d₁ x i
index (d₁ <&> d₂) (x , y) (lift false , i) = index d₂ y i

[_]_!_ : ∀ {ι α} {I : Set ι} {A B : I -> Set α}
       -> (d : Desc I α) -> (x : ⟦ d ⟧ᴰ A) -> (i : ⟦ idesc d ⟧ᴰ B) -> A (index d x i)
[ var v     ] x     ! i              = x
[ κ A       ] x     ! lift()
[ σ A B     ] x , y ! f              = [ B x ] y   ! f x
[ π A B     ] f     ! x , i          = [ B x ] f x ! i
[ d₁ <&> d₂ ] x , y ! lift true  , i = [ d₁  ] x   ! i
[ d₁ <&> d₂ ] x , y ! lift false , i = [ d₂  ] y   ! i
