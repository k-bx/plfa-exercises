module naturals where

--
-- * Chapter code
--

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ
-- {-# BUILTIN NATURAL ℕ #-}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

_ : (suc (suc zero)) + (suc (suc (suc zero))) ≡ suc (suc (suc (suc (suc zero))))
_ =
  begin
    (suc (suc zero)) + (suc (suc (suc zero)))
  ≡⟨⟩    -- inductive case
    suc ((suc zero) + (suc (suc (suc zero))))
  ≡⟨⟩    -- inductive case
    suc (suc (zero + (suc (suc (suc zero)))))
  ≡⟨⟩    -- base case
    suc (suc (suc (suc (suc zero))))
  ∎

_*_ : ℕ → ℕ → ℕ
zero    * n  =  zero
(suc m) * n  =  n + (m * n)

--
-- Exercise _^_ (recommended)
-- Define exponentiation, which is given by the following equations:
--
-- Check that 3 ^ 4 is 81.
--

_^_ : ℕ → ℕ → ℕ
m ^ zero = suc zero
m ^ (suc n) = m * (m ^ n)

eighty_one : ℕ
eighty_one = (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

_ : (suc (suc (suc zero))) ^ (suc (suc (suc (suc zero)))) ≡ eighty_one
_ = refl

_∸_ : ℕ → ℕ → ℕ
m     ∸ zero   =  m
zero  ∸ suc n  =  zero
suc m ∸ suc n  =  m ∸ n

--
-- Exercise ∸-examples (recommended)
-- Compute 5 ∸ 3 and 3 ∸ 5, writing out your reasoning as a chain of equations.
--
_ =
  begin
    (suc (suc (suc (suc (suc zero))))) ∸ (suc (suc (suc zero)))
  ≡⟨⟩
    (suc (suc (suc (suc zero)))) ∸ (suc (suc zero))
  ≡⟨⟩
    (suc (suc (suc zero))) ∸ (suc zero)
  ≡⟨⟩
    (suc (suc zero)) ∸ zero
  ≡⟨⟩
    (suc (suc zero))
  ∎
