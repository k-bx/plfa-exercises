module quantifiers where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_)
open import isomorphisms using (_≃_; extensionality)

∀-elim : ∀ {A : Set} {B : A → Set}
  → (L : ∀ (x : A) → B x)
  → (M : A)
    -----------------
  → B M
∀-elim L M = L M

-- Exercise ∀-distrib-× (recommended)

-- Show that universals distribute over conjunction:

∀-distrib-× : ∀ {A : Set} {B C : A → Set} →
  (∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)
∀-distrib-× =
  record
    { to = λ{x → ⟨ (λ x₁ → proj₁ (x x₁)) , (λ x₁ → proj₂ (x x₁)) ⟩}
    ; from = λ{ ⟨ fst , snd ⟩ x₁ → ⟨ fst x₁ , snd x₁ ⟩}
    ; from∘to = λ{x → refl}
    ; to∘from = λ{ ⟨ fst , snd ⟩ → refl}
    }

-- Compare this with the result (→-distrib-×) in Chapter Connectives.

-- Exercise ⊎∀-implies-∀⊎

-- Show that a disjunction of universals implies a universal of disjunctions:

⊎∀-implies-∀⊎ : ∀ {A : Set} {B C : A → Set} →
  (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x)  →  ∀ (x : A) → B x ⊎ C x
⊎∀-implies-∀⊎ (_⊎_.inj₁ xb) = λ x → _⊎_.inj₁ (xb x)
⊎∀-implies-∀⊎ (_⊎_.inj₂ xc) = λ x → _⊎_.inj₂ (xc x)

-- Does the converse hold? If so, prove; if not, explain why.

-- -- Not holds, don't know which branch before we split on x
-- ∀⊎-implies-⊎∀ : ∀ {A : Set} {B C : A → Set} →
--   (∀ (x : A) → B x ⊎ C x) → (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x)
-- ∀⊎-implies-⊎∀ f = proj₁ (λ x → f x)

-- Exercise ∀-×

-- Consider the following type.

data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri

elim-Tri : ∀ { B : Tri → Set }
  → B aa → B bb → B cc → (t : Tri) → B t
elim-Tri a b c aa = a
elim-Tri a b c bb = b
elim-Tri a b c cc = c

η-Tri :
  (y : Tri) → elim-Tri aa bb cc y ≡ y
η-Tri =
  λ{ aa → refl -- elim-Tri aa bb cc aa
   ; bb → refl -- elim-Tri aa bb cc bb
   ; cc → refl -- elim-Tri aa bb cc cc
   }

uniq-Tri₁ : ∀ { B : Tri → Set }
  → (x : ∀ (z : Tri) → B z)
  → (y : Tri)
  → elim-Tri {B} (x aa) (x bb) (x cc) y ≡ x y
uniq-Tri₁ =
  λ{ x aa → refl -- elim-Tri (x aa) (x bb) (x cc) aa
   ; x bb → refl -- elim-Tri (x aa) (x bb) (x cc) bb
   ; x cc → refl -- elim-Tri (x aa) (x bb) (x cc) cc
   }

-- Let B be a type indexed by Tri, that is B : Tri → Set. Show that ∀ (x : Tri) → B x is isomorphic to B aa × B bb × B cc.

open import isomorphisms using (extensionality)

postulate
  ∀-extensionality :
    ∀ {A : Set} {B : A → Set} (f g : ∀ (x : A) → B x)
    → (∀ (x : A) → (f x ≡ g x))
    → f ≡ g

-- from https://github.com/chirsz-ever/plfa-code/blob/ee7fe50737d7129ee4ac3cdf98f964ce77ece8ed/src/plfa-code/Quantifiers.agda#L49
∀-×₂ : {B : Tri → Set} → (∀ (x : Tri) → B x) ≃ (B aa × B bb × B cc)
∀-×₂ {B} =
  record
  { to      = to′
  ; from    = from′
  ; from∘to = λ f → ∀-extensionality (from′ ⟨ f aa , ⟨ f bb , f cc ⟩ ⟩) f
                                     λ{aa → refl; bb → refl; cc → refl}
  ; to∘from = λ xx → refl
  }
  where
  to′ : (∀ (x : Tri) → B x) → (B aa × B bb × B cc)
  to′ f = ⟨ f aa , ⟨ f bb , f cc ⟩ ⟩
  from′ : (B aa × B bb × B cc) → (∀ (x : Tri) → B x)
  from′ xx aa = proj₁ xx
  from′ xx bb = proj₁ (proj₂ xx)
  from′ xx cc = proj₂ (proj₂ xx)

∀-× : {B : Tri → Set} → (∀ (x : Tri) → B x) ≃ (B aa × B bb × B cc)
∀-× {B} =
  record
    { to = to′
    ; from = from′
    ; from∘to = from∘to′
    ; to∘from = λ{y → refl}
    }
  where
    to′ : ((x : Tri) → B x) → B aa × B bb × B cc
    to′ = λ x → ⟨ x aa , ⟨ x bb , x cc ⟩ ⟩
    from′ : B aa × B bb × B cc → (x : Tri) → B x
    from′ = λ{ x aa → proj₁ x ; x bb → proj₁ (proj₂ x) ; x cc → proj₂ (proj₂ x)}
    from∘to′ : (x : (x₁ : Tri) → B x₁) → from′ ⟨ x aa , ⟨ x bb , x cc ⟩ ⟩ ≡ x
    from∘to′ =
      λ f →
      let v = from′ ⟨ f aa , ⟨ f bb , f cc ⟩ ⟩
      in ∀-extensionality v f λ{ aa → refl ; bb → refl ; cc → refl}

-- failed attempt
ex₁ : ∀ {B : Tri → Set} → (∀ (x : Tri) → B x) ≃ B aa × B bb × B cc
ex₁ =
  record
    { to = λ x → ⟨ x aa , ⟨ x bb , x cc ⟩ ⟩
    ; from = λ x → elim-Tri (proj₁ x) (proj₁ (proj₂ x)) (proj₂ (proj₂ x))
    ; from∘to = λ x → let v = λ y → uniq-Tri₁ x y in {!∀-extensionality !}
         -- let v = λ y → uniq-Tri₁ x y ? -- extensionality v
                -- let v = λ y → uniq-Tri₁ x y
                -- in ? -- {!extensionality v!}
    ; to∘from = λ y → refl
    }

data Σ (A : Set) (B : A → Set) : Set where
  ⟨_,_⟩ : (x : A) → B x → Σ A B

Σ-syntax = Σ
infix 2 Σ-syntax
syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

∃ : ∀ {A : Set} (B : A → Set) → Set
∃ {A} B = Σ A B

∃-syntax = ∃
syntax ∃-syntax (λ x → B) = ∃[ x ] B

∃-elim : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C)
  → ∃[ x ] B x
    ---------------
  → C
∃-elim f ⟨ x , y ⟩ = f x y

∀∃-currying : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C) ≃ (∃[ x ] B x → C)
∀∃-currying =
  record
    { to      =  λ{ f → λ{ ⟨ x , y ⟩ → f x y }}
    ; from    =  λ{ g → λ{ x → λ{ y → g ⟨ x , y ⟩ }}}
    ; from∘to =  λ{ f → refl }
    ; to∘from =  λ{ g → extensionality λ{ ⟨ x , y ⟩ → refl }}
    }

-- Exercise ∃-distrib-⊎ (recommended)

-- Show that existentials distribute over disjunction:

-- ∃-distrib-⊎ : ∀ {A : Set} {B C : A → Set} →
--   ∃[ x ] (B x ⊎ C x) ≃ (∃[ x ] B x) ⊎ (∃[ x ] C x)
-- ∃-distrib-⊎ =
--   record
--     { to = {!!}
--     ; from = {!!}
--     ; from∘to = {!!}
--     ; to∘from = {!!}
--     }

-- Exercise ∃×-implies-×∃

-- Show that an existential of conjunctions implies a conjunction of existentials:

-- postulate
--   ∃×-implies-×∃ : ∀ {A : Set} {B C : A → Set} →
--     ∃[ x ] (B x × C x) → (∃[ x ] B x) × (∃[ x ] C x)

-- Does the converse hold? If so, prove; if not, explain why.
-- Exercise ∃-⊎

-- Let Tri and B be as in Exercise ∀-×. Show that ∃[ x ] B x is isomorphic to B aa ⊎ B bb ⊎ B cc.

data even : ℕ → Set
data odd  : ℕ → Set

data even where

  even-zero : even zero

  even-suc : ∀ {n : ℕ}
    → odd n
      ------------
    → even (suc n)

data odd where
  odd-suc : ∀ {n : ℕ}
    → even n
      -----------
    → odd (suc n)

even-∃ : ∀ {n : ℕ} → even n → ∃[ m ] (    m * 2 ≡ n)
odd-∃  : ∀ {n : ℕ} →  odd n → ∃[ m ] (1 + m * 2 ≡ n)

even-∃ even-zero                       =  ⟨ zero , refl ⟩
even-∃ (even-suc o) with odd-∃ o
...                    | ⟨ m , refl ⟩  =  ⟨ suc m , refl ⟩

odd-∃  (odd-suc e)  with even-∃ e
...                    | ⟨ m , refl ⟩  =  ⟨ m , refl ⟩

∃-even : ∀ {n : ℕ} → ∃[ m ] (    m * 2 ≡ n) → even n
∃-odd  : ∀ {n : ℕ} → ∃[ m ] (1 + m * 2 ≡ n) →  odd n

∃-even ⟨  zero , refl ⟩  =  even-zero
∃-even ⟨ suc m , refl ⟩  =  even-suc (∃-odd ⟨ m , refl ⟩)

∃-odd  ⟨     m , refl ⟩  =  odd-suc (∃-even ⟨ m , refl ⟩)

-- Exercise ∃-even-odd

-- How do the proofs become more difficult if we replace m * 2 and 1 + m * 2 by 2 * m and 2 * m + 1? Rewrite the proofs of ∃-even and ∃-odd when restated in this way.

-- -- Your code goes here

-- Exercise ∃-|-≤

-- Show that y ≤ z holds if and only if there exists a x such that x + y ≡ z.

-- -- Your code goes here

¬∃≃∀¬ : ∀ {A : Set} {B : A → Set}
  → (¬ ∃[ x ] B x) ≃ ∀ x → ¬ B x
¬∃≃∀¬ =
  record
    { to      =  λ{ ¬∃xy x y → ¬∃xy ⟨ x , y ⟩ }
    ; from    =  λ{ ∀¬xy ⟨ x , y ⟩ → ∀¬xy x y }
    ; from∘to =  λ{ ¬∃xy → extensionality λ{ ⟨ x , y ⟩ → refl } }
    ; to∘from =  λ{ ∀¬xy → refl }
    }

-- Exercise ∃¬-implies-¬∀ (recommended)

-- Show that existential of a negation implies negation of a universal:

-- postulate
--   ∃¬-implies-¬∀ : ∀ {A : Set} {B : A → Set}
--     → ∃[ x ] (¬ B x)
--       --------------
--     → ¬ (∀ x → B x)

-- Does the converse hold? If so, prove; if not, explain why.
-- Exercise Bin-isomorphism (stretch)

-- Recall that Exercises Bin, Bin-laws, and Bin-predicates define a datatype of bitstrings representing natural numbers:

-- data Bin : Set where
--   nil : Bin
--   x0_ : Bin → Bin
--   x1_ : Bin → Bin

-- And ask you to define the following functions and predicates:

-- to   : ℕ → Bin
-- from : Bin → ℕ
-- Can  : Bin → Set

-- And to establish the following properties:

-- from (to n) ≡ n

-- ----------
-- Can (to n)

-- Can x
-- ---------------
-- to (from x) ≡ x

-- Using the above, establish that there is an isomorphism between ℕ and ∃[ x ](Can x).

-- -- Your code goes here
