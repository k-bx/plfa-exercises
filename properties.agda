open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂)
open import Data.String using (String; _≟_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product
  using (_×_; proj₁; proj₂; ∃; ∃-syntax)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Function using (_∘_)
open import isomorphisms
open import lambda

V¬—→ : ∀ {M N}
  → Value M
    ----------
  → ¬ (M —→ N)
V¬—→ V-ƛ        ()
V¬—→ V-zero     ()
V¬—→ (V-suc VM) (ξ-suc M—→N) = V¬—→ VM M—→N

—→¬V : ∀ {M N}
  → M —→ N
    ---------
  → ¬ Value M
—→¬V M—→N VM  =  V¬—→ VM M—→N

infix  4 Canonical_⦂_

data Canonical_⦂_ : Term → Type → Set where

  C-ƛ : ∀ {x A N B}
    → ∅ , x ⦂ A ⊢ N ⦂ B
      -----------------------------
    → Canonical (ƛ x ⇒ N) ⦂ (A ⇒ B)

  C-zero :
      --------------------
      Canonical `zero ⦂ `ℕ

  C-suc : ∀ {V}
    → Canonical V ⦂ `ℕ
      ---------------------
    → Canonical `suc V ⦂ `ℕ

canonical : ∀ {V A}
  → ∅ ⊢ V ⦂ A
  → Value V
    -----------
  → Canonical V ⦂ A
canonical (⊢` ())          ()
canonical (⊢ƛ ⊢N)          V-ƛ         =  C-ƛ ⊢N
canonical (⊢L · ⊢M)        ()
canonical ⊢zero            V-zero      =  C-zero
canonical (⊢suc ⊢V)        (V-suc VV)  =  C-suc (canonical ⊢V VV)
canonical (⊢case ⊢L ⊢M ⊢N) ()
canonical (⊢μ ⊢M)          ()

value : ∀ {M A}
  → Canonical M ⦂ A
    ----------------
  → Value M
value (C-ƛ ⊢N)    =  V-ƛ
value C-zero      =  V-zero
value (C-suc CM)  =  V-suc (value CM)

typed : ∀ {M A}
  → Canonical M ⦂ A
    ---------------
  → ∅ ⊢ M ⦂ A
typed (C-ƛ ⊢N)    =  ⊢ƛ ⊢N
typed C-zero      =  ⊢zero
typed (C-suc CM)  =  ⊢suc (typed CM)
