module induction where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)

+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p =
  begin
    (zero + n) + p
  ≡⟨⟩
    n + p
  ≡⟨⟩
   zero + (n + p)
  ∎
+-assoc (suc m) n p =
  begin
    (suc m + n) + p
  ≡⟨⟩
    suc (m + n) + p
  ≡⟨⟩
    suc ((m + n) + p)
  ≡⟨ cong suc (+-assoc m n p) ⟩
    suc (m + (n + p))
  ≡⟨⟩
    suc m + (n + p)
  ∎

+-assoc-2 : ∀ (n p : ℕ) → (2 + n) + p ≡ 2 + (n + p)
+-assoc-2 n p =
  begin
    (2 + n) + p
  ≡⟨⟩
    suc (1 + n) + p
  ≡⟨⟩
    suc ((1 + n) + p)
  ≡⟨ cong suc (+-assoc-1 n p) ⟩
    suc (1 + (n + p))
  ≡⟨⟩
    2 + (n + p)
  ∎
  where
  +-assoc-1 : ∀ (n p : ℕ) → (1 + n) + p ≡ 1 + (n + p)
  +-assoc-1 n p =
    begin
      (1 + n) + p
    ≡⟨⟩
      suc (0 + n) + p
    ≡⟨⟩
      suc ((0 + n) + p)
    ≡⟨ cong suc (+-assoc-0 n p) ⟩
      suc (0 + (n + p))
    ≡⟨⟩
      1 + (n + p)
    ∎
    where
    +-assoc-0 : ∀ (n p : ℕ) → (0 + n) + p ≡ 0 + (n + p)
    +-assoc-0 n p =
      begin
        (0 + n) + p
      ≡⟨⟩
        n + p
      ≡⟨⟩
        0 + (n + p)
      ∎

+-identityʳ : ∀ (m : ℕ) → m + zero ≡ m
+-identityʳ zero =
  begin
    zero + zero
  ≡⟨⟩
    zero
  ∎
+-identityʳ (suc m) =
  begin
    suc m + zero
  ≡⟨⟩
    suc (m + zero)
  ≡⟨ cong suc (+-identityʳ m) ⟩
    suc m
  ∎

+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n =
  begin
    zero + suc n
  ≡⟨⟩
    suc n
  ≡⟨⟩
    suc (zero + n)
  ∎
+-suc (suc m) n =
  begin
    suc m + suc n
  ≡⟨⟩
    suc (m + suc n)
  ≡⟨ cong suc (+-suc m n) ⟩
    suc (suc (m + n))
  ≡⟨⟩
    suc (suc m + n)
  ∎

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero =
  begin
    m + zero
  ≡⟨ +-identityʳ m ⟩
    m
  ≡⟨⟩
    zero + m
  ∎
+-comm m (suc n) =
  begin
    m + suc n
  ≡⟨ +-suc m n ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ≡⟨⟩
    suc n + m
  ∎

+-rearrange : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange m n p q =
  begin
    (m + n) + (p + q)
  ≡⟨ +-assoc m n (p + q) ⟩
    m + (n + (p + q))
  ≡⟨ cong (m +_) (sym (+-assoc n p q)) ⟩
    m + ((n + p) + q)
  ≡⟨ sym (+-assoc m (n + p) q) ⟩
    (m + (n + p)) + q
  ∎

+-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc′ zero    n p                          =  refl
+-assoc′ (suc m) n p  rewrite +-assoc′ m n p  =  refl

+-identity′ : ∀ (n : ℕ) → n + zero ≡ n
+-identity′ zero = refl
+-identity′ (suc n) rewrite +-identity′ n = refl

+-suc′ : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc′ zero n = refl
+-suc′ (suc m) n rewrite +-suc′ m n = refl

+-comm′ : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm′ m zero rewrite +-identity′ m = refl
+-comm′ m (suc n) rewrite +-suc′ m n | +-comm′ m n = refl

--
-- Exercise +-swap (recommended)
-- Show
-- 
-- m + (n + p) ≡ n + (m + p)
-- for all naturals m, n, and p. No induction is needed, just apply the previous results which show addition is associative and commutative.
--
+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap m n p rewrite +-comm′ m (n + p) | +-comm′ m p | +-assoc′ n p m = refl

--
-- Exercise *-distrib-+ (recommended)
--
-- Show multiplication distributes over addition, that is,
--
-- (m + n) * p ≡ m * p + n * p
--
-- for all naturals m, n, and p.
--
-- p₁ : zero ≡ zero
-- p₁ = refl

*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ zero n p = refl
*-distrib-+ (suc m) zero p rewrite +-comm m 0 | +-comm (p + (m * p)) 0 = refl
*-distrib-+ (suc m) (suc n) p
  rewrite +-comm m (suc n)
  | +-comm n m
  | *-distrib-+ m n p
  | +-swap p (m * p) (n * p)
  | +-assoc p (m * p) (p + n * p)
  = refl

-- _∸_ : ℕ → ℕ → ℕ
-- m     ∸ zero   =  m
-- zero  ∸ suc n  =  zero
-- suc m ∸ suc n  =  m ∸ n

unsuceq : ∀ (m n : ℕ) → suc m ≡ suc n → m ≡ n
unsuceq m n = λ x → cong (_∸ 1) x

+-striphead : ∀ (p m n : ℕ) → (p + m ≡ p + n) → (m ≡ n)
+-striphead p m n x = {!!}

*-zero-zero : ∀ (n : ℕ) → n * zero ≡ zero
*-zero-zero zero = refl
*-zero-zero (suc n) rewrite *-zero-zero n = refl

*-identityʳ : ∀ (n : ℕ) → n * 1 ≡ n
*-identityʳ zero = refl
*-identityʳ (suc n) rewrite *-identityʳ n = refl

*-suc1 : ∀ (m n : ℕ) → m * suc n ≡ m + m * n
*-suc1 zero n = refl
*-suc1 (suc m) zero rewrite *-zero-zero m
  | +-identityʳ m
  | *-identityʳ m = refl
*-suc1 (suc m) (suc n)
  rewrite
    -- sym (+-suc n (m * suc (suc n)))
  *-suc1 m (suc n)
  | +-suc m (n + m * suc n)
  | sym (+-assoc n m (m * suc n))
  | +-comm n m
  | +-assoc m n (m * suc n)
  = refl

*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm zero n rewrite *-zero-zero n = refl
*-comm (suc m) zero rewrite *-zero-zero (suc m) = refl
*-comm (suc m) (suc n)
  rewrite *-suc1 m n
  | *-suc1 n m
  | *-comm m n
  | sym (+-assoc n m (n * m))
  | +-comm n m
  | +-assoc m n (n * m)
  = refl

--
-- Exercise 0∸n≡0
-- Show
-- zero ∸ n ≡ zero
--
-- for all naturals n. Did your proof require induction?
--
exMonus : ∀ (n : ℕ) → 0 ∸ n ≡ 0
exMonus zero = refl
exMonus (suc n) = refl
