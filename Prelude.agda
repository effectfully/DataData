module DataData.Prelude where              

open import Level renaming (zero to lzero; suc to lsuc)                                        public
open import Function hiding (_⟨_⟩_)                                                            public
open import Relation.Nullary                                                                   public
open import Relation.Binary hiding (_⇒_)                                                       public
open import Relation.Binary.PropositionalEquality hiding ([_])                                 public
open import Relation.Binary.HeterogeneousEquality using (_≅_; ≅-to-≡) renaming (refl to hrefl) public
open import Data.Empty                                                                         public
open import Data.Unit.Base using (⊤)                                                           public
open import Data.Bool.Base                                                                     public
open import Data.Nat.Base hiding (_⊔_; _∸_)                                                    public
open import Data.Fin using (Fin)                                                               public
open import Data.Sum     renaming (map to smap)                                                public
open import Data.Product renaming (map to pmap)                                                public
open import Data.Vec     renaming (map to vmap) hiding ([_]; zip; _>>=_; _∈_; module _∈_)      public
open import Data.Vec.Properties                                                                public
open ≡-Reasoning                                                                               public

open import Algebra using (module CommutativeSemiring)
open import Data.Nat.Properties
module CS = CommutativeSemiring commutativeSemiring

infixr 2 _→⟨_⟩_ _←⟨_⟩_
infix  7 _[>_<]_

_→⟨_⟩_ : ∀ {α} {A : Set α} {y z} -> (x : A) -> x ≡ y -> y IsRelatedTo z -> x IsRelatedTo z
x →⟨ x≡y ⟩ y-irt-z = x ≡⟨     x≡y ⟩ y-irt-z

_←⟨_⟩_ : ∀ {α} {A : Set α} {y z} -> (x : A) -> y ≡ x -> y IsRelatedTo z -> x IsRelatedTo z
x ←⟨ y≡x ⟩ y-irt-z = x →⟨ sym y≡x ⟩ y-irt-z

─ : ∀ {α} -> Set α
─ = Lift ⊤

_∸>_ : ∀ {α β γ} -> (Set α -> Set β) -> (Set α -> Set γ) -> Set (lsuc α ⊔ β ⊔ γ)
F ∸> G = ∀ {A} -> F A -> G A

data All {α π} {A : Set α} (P : A -> Set π) : ∀ {n} -> Vec A n -> Set π where
  []ₐ  : All P []
  _∷ₐ_ : ∀ {n x} {xs : Vec A n} -> P x -> All P xs -> All P (x ∷ xs)

first : ∀ {α β γ} {A : Set α} {B : Set β} {C : A -> Set γ}
      -> (∀ x -> C x) -> (p : A × B) -> C (proj₁ p) × B
first f (x , y) = f x , y

second : ∀ {α β γ} {A : Set α} {B : A -> Set β} {C : A -> Set γ}
       -> (∀ {x} -> B x -> C x) -> Σ A B -> Σ A C
second g (x , y) = x , g y

_[>_<]_ : ∀ {α β γ δ ε} {A : Set α} {B : A -> Set β}
            {C : A -> Set γ} {D : ∀ {x} -> B x -> Set δ}
            {E : ∀ {x} {y : B x} -> C x -> D y -> Set ε}
        -> (f : ∀ x -> C x)
        -> (∀ {x y} -> (c : C x) -> (d : D y) -> E c d)
        -> (g : ∀ {x} -> (y : B x) -> D y)
        -> (p : Σ A B)
        -> E (f (proj₁ p)) (g (proj₂ p))
(f [> h <] g) (x , y) = h (f x) (g y)

icong : ∀ {ι α β} {I : Set ι} {B : Set β} {i j : I}
          (A : I -> Set α) {x : A i} {y : A j}
      -> (f : ∀ {k} -> A k -> B) -> i ≡ j -> x ≅ y -> f x ≡ f y
icong A f refl hrefl = refl

hicong : ∀ {ι α β} {I : Set ι} {i j : I}
           (A : I -> Set α) {B : ∀ {k} -> A k -> Set β} {x : A i} {y : A j}
       -> (f : ∀ {k} -> (x : A k) -> B x) -> i ≡ j -> x ≅ y -> f x ≅ f y
hicong A f refl hrefl = hrefl

delim : ∀ {α β} {A : Set α} {B : Dec A -> Set β}
      -> (∀ x -> B (yes x)) -> (∀ c -> B (no c)) -> (d : Dec A) -> B d
delim f g (yes x) = f x
delim f g (no  c) = g c

drec : ∀ {α β} {A : Set α} {B : Set β} -> (A -> B) -> (¬ A -> B) -> Dec A -> B
drec = delim

dmap : ∀ {α β} {A : Set α} {B : Set β} -> (A -> B) -> (¬ A -> ¬ B) -> Dec A -> Dec B
dmap f g = drec (yes ∘ f) (no ∘ g)

dcong : ∀ {α β} {A : Set α} {B : Set β} {x y}
      -> (f : A -> B)
      -> (∀ {x y} -> f x ≡ f y -> x ≡ y)
      -> Dec (x ≡ y)
      -> Dec (f x ≡ f y)
dcong f inj = dmap (cong f) (_∘ inj)

dcong₂ : ∀ {α β γ} {A : Set α} {B : Set β} {C : Set γ} {x y v w}
       -> (f : A -> B -> C)
       -> (∀ {x y} -> f x v ≡ f y w -> x ≡ y × v ≡ w)
       -> Dec (x ≡ y)
       -> Dec (v ≡ w)
       -> Dec (f x v ≡ f y w)
dcong₂ f inj d₁ d₂ = drec (λ p₁ -> dmap (λ p₂ -> cong₂ f p₁ p₂) (λ c -> c ∘ proj₂ ∘ inj) d₂)
                          (λ c  -> no (c ∘ proj₁ ∘ inj))
                           d₁

idcong : ∀ {ι α β} {I : Set ι}
           (A : I -> Set α) {B : Set β} {i j} {x : A i} {y : A j}
       -> (f : ∀ {k} -> A k -> B)
       -> (f x ≡ f y -> i ≡ j × x ≅ y)
       -> Dec (i ≡ j)
       -> ({p : i ≡ j} -> Dec (subst A p x ≡ y))
       -> Dec (f x ≡ f y)
idcong A f inj d₁ d₂ with d₁
... | yes p₁ rewrite p₁ = dmap (cong f) (λ c -> c ∘ ≅-to-≡ ∘ proj₂ ∘ inj) (d₂ {refl})
... | no  c  = no (c ∘ proj₁ ∘ inj)

,-inj : ∀ {α β} {A : Set α} {B : A -> Set β} {x₁ x₂ : A} {y₁ : B x₁} {y₂ : B x₂}
      -> (x₁ , y₁) ≡ (x₂ , y₂) -> x₁ ≡ x₂ × y₁ ≅ y₂
,-inj refl = refl , hrefl

∷-inj : ∀ {α n} {A : Set α} {x₁ x₂} {xs₁ xs₂ : Vec A n} -> x₁ ∷ xs₁ ≡ x₂ ∷ xs₂ -> x₁ ≡ x₂ × xs₁ ≡ xs₂
∷-inj refl = refl , refl

++-[] : ∀ {α n} {A : Set α} {xs : Vec A n} -> xs ++ [] ≅ xs
++-[] {xs = []    } = hrefl
++-[] {xs = x ∷ xs} = hicong (Vec _) (x ∷_) (proj₂ CS.+-identity _) ++-[]
      
++-assoc : ∀ {n m p α} {A : Set α} (xs : Vec A n) {ys : Vec A m} {zs : Vec A p}
         -> (xs ++ ys) ++ zs ≅ xs ++ (ys ++ zs)
++-assoc          []      = hrefl
++-assoc {suc n} (x ∷ xs) = hicong (Vec _) (x ∷_) (CS.+-assoc n _ _) (++-assoc xs)
