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

-- -- Your code goes here

-- Exercise trichotomy

-- Show that strict inequality satisfies trichotomy, that is, for any naturals m and n exactly one of the following holds:

--     m < n
--     m ≡ n
--     m > n

-- Here “exactly one” means that not only one of the three must hold, but that when one holds the negation of the other two must also hold.

-- -- Your code goes here

-- Exercise ⊎-dual-× (recommended)

-- Show that conjunction, disjunction, and negation are related by a version of De Morgan’s Law.

-- ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)

-- This result is an easy consequence of something we’ve proved previously.

-- -- Your code goes here

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
