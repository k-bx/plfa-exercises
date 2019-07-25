module negation where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_)
open import isomorphisms using (_≃_; extensionality)

¬_ : Set → Set
¬ A = A → ⊥

¬-elim : ∀ {A : Set}
  → ¬ A
  → A
    ---
  → ⊥
¬-elim ¬x x = ¬x x

infix 3 ¬_

¬¬-intro : ∀ {A : Set}
  → A
    -----
  → ¬ ¬ A
¬¬-intro x  =  λ{¬x → ¬x x}

¬¬-intro′ : ∀ {A : Set}
  → A
    -----
  → ¬ ¬ A
¬¬-intro′ x ¬x = ¬x x

¬¬¬-elim : ∀ {A : Set}
  → ¬ ¬ ¬ A
    -------
  → ¬ A
¬¬¬-elim ¬¬¬x  =  λ x → ¬¬¬x (¬¬-intro x)

contraposition : ∀ {A B : Set}
  → (A → B)
    -----------
  → (¬ B → ¬ A)
contraposition f ¬y x = ¬y (f x)

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y  =  ¬ (x ≡ y)

_ : 1 ≢ 2
_ = λ()

peano : ∀ {m : ℕ} → zero ≢ suc m
peano = λ()

id : ⊥ → ⊥
id x = x

id′ : ⊥ → ⊥
id′ ()

id≡id′ : id ≡ id′
id≡id′ = extensionality (λ())

assimilation : ∀ {A : Set} (¬x ¬x′ : ¬ A) → ¬x ≡ ¬x′
assimilation ¬x ¬x′ = extensionality (λ x → ⊥-elim (¬x x))

-- Exercise <-irreflexive (recommended)

-- Using negation, show that strict inequality is irreflexive, that is, n < n holds for no n.

infix 4 _<_

data _<_ : ℕ → ℕ → Set where

  z<s : ∀ {n : ℕ}
      ------------
    → zero < suc n

  s<s : ∀ {m n : ℕ}
    → m < n
      -------------
    → suc m < suc n

-- <-cong : ∀ {n : ℕ}
--   → (n < n)

open import Function using (_∘_)

<-irreflexive : ∀ {n : ℕ}
  → ((n < n) → ⊥)
<-irreflexive (s<s m<m) = <-irreflexive m<m

-- Exercise trichotomy

-- Show that strict inequality satisfies trichotomy, that is, for any naturals m and n exactly one of the following holds:

--     m < n
--     m ≡ n
--     m > n

-- Here “exactly one” means that not only one of the three must hold, but that when one holds the negation of the other two must also hold.

data _>_ (m n : ℕ) : Set where
  mk-> : n < m → m > n

open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong)

>≡<-trechotomy₁ : ∀ {m n : ℕ}
  → m < n
  → (¬ m ≡ n × ¬ m > n)
>≡<-trechotomy₁ z<s = (λ{ ()}) , λ{ (mk-> ())}
>≡<-trechotomy₁ (s<s m<n) =
  let e₁ = ( λ{ refl → proj₂ (>≡<-trechotomy₁ m<n) (mk-> m<n)})
      e₂ = λ{ (mk-> (s<s x)) → proj₂ (>≡<-trechotomy₁ m<n) (mk-> x)}
  in e₁ , e₂

-- Exercise ⊎-dual-× (recommended)

-- Show that conjunction, disjunction, and negation are related by a
-- version of De Morgan’s Law.
-- This result is an easy consequence of something we’ve proved previously.

η-→ : ∀ {A B : Set} (f : A → B) → (λ (x : A) → f x) ≡ f
η-→ f = refl

case-⊎ : ∀ {A B C : Set}
  → (A → C)
  → (B → C)
  → A ⊎ B
    -----------
  → C
case-⊎ f g (inj₁ x) = f x
case-⊎ f g (inj₂ y) = g y

⊎-dual-×--from : ∀ {A B : Set}
  → ¬ A × ¬ B → ¬ (A ⊎ B)
⊎-dual-×--from (¬A , ¬B) =
  case-⊎ ¬A ¬B

⊎-dual-×--to : ∀ {A B : Set}
  → ¬ (A ⊎ B) → ¬ A × ¬ B
⊎-dual-×--to = λ{¬A⊎B → (¬A⊎B ∘ inj₁) , ¬A⊎B ∘ inj₂}

uniq-⊎ : ∀ {A B C : Set} (h : A ⊎ B → C) (w : A ⊎ B) →
  case-⊎ (h ∘ inj₁) (h ∘ inj₂) w ≡ h w
uniq-⊎ h (inj₁ x) = refl
uniq-⊎ h (inj₂ y) = refl

⊎-dual-×--from∘to : ∀ {A B : Set}
  → (x : ¬ (A ⊎ B)) → ⊎-dual-×--from (⊎-dual-×--to x) ≡ x
⊎-dual-×--from∘to {A} {B} ¬A⊎B
  rewrite η-→ (⊎-dual-×--to {A} {B})
  = extensionality (λ (w : A ⊎ B) → uniq-⊎ ¬A⊎B w)

⊎-dual-× : ∀ {A B : Set}
  → ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)
⊎-dual-× {A} {B} =
  record
    { to = ⊎-dual-×--to
    ; from = ⊎-dual-×--from
    ; from∘to = ⊎-dual-×--from∘to
    ; to∘from = λ{ (fst , snd) → refl}
    }

-- Do we also have the following?

-- ¬ (A × B) ≃ (¬ A) ⊎ (¬ B)

-- If so, prove; if not, can you give a relation weaker than isomorphism that relates the two sides?

postulate
  em : ∀ {A : Set} → A ⊎ ¬ A

em-irrefutable : ∀ {A : Set} → ¬ ¬ (A ⊎ ¬ A)
em-irrefutable = λ k → k (inj₂ (λ x → k (inj₁ x)))


-- Exercise Classical (stretch)

-- Consider the following principles:

--     Excluded Middle: A ⊎ ¬ A, for all A
--     Double Negation Elimination: ¬ ¬ A → A, for all A
--     Peirce’s Law: ((A → B) → A) → A, for all A and B.
--     Implication as disjunction: (A → B) → ¬ A ⊎ B, for all A and B.
--     De Morgan: ¬ (¬ A × ¬ B) → A ⊎ B, for all A and B.

-- Show that each of these implies all the others.

-- -- Your code goes here

-- Exercise Stable (stretch)

-- Say that a formula is stable if double negation elimination holds for it:

-- Stable : Set → Set
-- Stable A = ¬ ¬ A → A

-- Show that any negated formula is stable, and that the conjunction of two stable formulas is stable.

-- -- Your code goes here
