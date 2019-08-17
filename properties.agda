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

data Progress (M : Term) : Set where

  step : ∀ {N}
    → M —→ N
      ----------
    → Progress M

  done :
      Value M
      ----------
    → Progress M

progress : ∀ {M A}
  → ∅ ⊢ M ⦂ A
    ----------
  → Progress M
progress (⊢` ())
progress (⊢ƛ ⊢N)                            =  done V-ƛ
progress (⊢L · ⊢M) with progress ⊢L
... | step L—→L′                            =  step (ξ-·₁ L—→L′)
... | done VL with progress ⊢M
...   | step M—→M′                          =  step (ξ-·₂ VL M—→M′)
...   | done VM with canonical ⊢L VL
...     | C-ƛ _                             =  step (β-ƛ VM)
progress ⊢zero                              =  done V-zero
progress (⊢suc ⊢M) with progress ⊢M
...  | step M—→M′                           =  step (ξ-suc M—→M′)
...  | done VM                              =  done (V-suc VM)
progress (⊢case ⊢L ⊢M ⊢N) with progress ⊢L
... | step L—→L′                            =  step (ξ-case L—→L′)
... | done VL with canonical ⊢L VL
...   | C-zero                              =  step β-zero
...   | C-suc CL                            =  step (β-suc (value CL))
progress (⊢μ ⊢M)                            =  step β-μ

postulate
  progress′ : ∀ M {A} → ∅ ⊢ M ⦂ A → Value M ⊎ ∃[ N ](M —→ N)

-- Exercise Progress-≃

-- Show that Progress M is isomorphic to Value M ⊎ ∃[ N ](M —→ N).

-- Exercise progress′

-- Write out the proof of progress′ in full, and compare it to the proof of progress above.

-- Exercise value?

-- Combine progress and —→¬V to write a program that decides whether a well-typed term is a value:

-- postulate
--   value? : ∀ {A M} → ∅ ⊢ M ⦂ A → Dec (Value M)

ext : ∀ {Γ Δ}
  → (∀ {x A}     →         Γ ∋ x ⦂ A →         Δ ∋ x ⦂ A)
    -----------------------------------------------------
  → (∀ {x y A B} → Γ , y ⦂ B ∋ x ⦂ A → Δ , y ⦂ B ∋ x ⦂ A)
ext ρ Z           =  Z
ext ρ (S x≢y ∋x)  =  S x≢y (ρ ∋x)

rename : ∀ {Γ Δ}
  → (∀ {x A} → Γ ∋ x ⦂ A → Δ ∋ x ⦂ A)
    ----------------------------------
  → (∀ {M A} → Γ ⊢ M ⦂ A → Δ ⊢ M ⦂ A)
rename ρ (⊢` ∋w)           =  ⊢` (ρ ∋w)
rename ρ (⊢ƛ ⊢N)           =  ⊢ƛ (rename (ext ρ) ⊢N)
rename ρ (⊢L · ⊢M)         =  (rename ρ ⊢L) · (rename ρ ⊢M)
rename ρ ⊢zero             =  ⊢zero
rename ρ (⊢suc ⊢M)         =  ⊢suc (rename ρ ⊢M)
rename ρ (⊢case ⊢L ⊢M ⊢N)  =  ⊢case (rename ρ ⊢L) (rename ρ ⊢M) (rename (ext ρ) ⊢N)
rename ρ (⊢μ ⊢M)           =  ⊢μ (rename (ext ρ) ⊢M)

weaken : ∀ {Γ M A}
  → ∅ ⊢ M ⦂ A
    ----------
  → Γ ⊢ M ⦂ A
weaken {Γ} ⊢M = rename ρ ⊢M
  where
  ρ : ∀ {z C}
    → ∅ ∋ z ⦂ C
      ---------
    → Γ ∋ z ⦂ C
  ρ ()

drop : ∀ {Γ x M A B C}
  → Γ , x ⦂ A , x ⦂ B ⊢ M ⦂ C
    --------------------------
  → Γ , x ⦂ B ⊢ M ⦂ C
drop {Γ} {x} {M} {A} {B} {C} ⊢M = rename ρ ⊢M
  where
  ρ : ∀ {z C}
    → Γ , x ⦂ A , x ⦂ B ∋ z ⦂ C
      -------------------------
    → Γ , x ⦂ B ∋ z ⦂ C
  ρ Z                 =  Z
  ρ (S x≢x Z)         =  ⊥-elim (x≢x refl)
  ρ (S z≢x (S _ ∋z))  =  S z≢x ∋z

swap : ∀ {Γ x y M A B C}
  → x ≢ y
  → Γ , y ⦂ B , x ⦂ A ⊢ M ⦂ C
    --------------------------
  → Γ , x ⦂ A , y ⦂ B ⊢ M ⦂ C
swap {Γ} {x} {y} {M} {A} {B} {C} x≢y ⊢M = rename ρ ⊢M
  where
  ρ : ∀ {z C}
    → Γ , y ⦂ B , x ⦂ A ∋ z ⦂ C
      --------------------------
    → Γ , x ⦂ A , y ⦂ B ∋ z ⦂ C
  ρ Z                   =  S x≢y Z
  ρ (S y≢x Z)           =  Z
  ρ (S z≢x (S z≢y ∋z))  =  S z≢y (S z≢x ∋z)

subst : ∀ {Γ x N V A B}
  → ∅ ⊢ V ⦂ A
  → Γ , x ⦂ A ⊢ N ⦂ B
    --------------------
  → Γ ⊢ N [ x := V ] ⦂ B
subst {x = y} ⊢V (⊢` {x = x} Z) with x ≟ y
... | yes _           =  weaken ⊢V
... | no  x≢y         =  ⊥-elim (x≢y refl)
subst {x = y} ⊢V (⊢` {x = x} (S x≢y ∋x)) with x ≟ y
... | yes refl        =  ⊥-elim (x≢y refl)
... | no  _           =  ⊢` ∋x
subst {x = y} ⊢V (⊢ƛ {x = x} ⊢N) with x ≟ y
... | yes refl        =  ⊢ƛ (drop ⊢N)
... | no  x≢y         =  ⊢ƛ (subst ⊢V (swap x≢y ⊢N))
subst ⊢V (⊢L · ⊢M)    =  (subst ⊢V ⊢L) · (subst ⊢V ⊢M)
subst ⊢V ⊢zero        =  ⊢zero
subst ⊢V (⊢suc ⊢M)    =  ⊢suc (subst ⊢V ⊢M)
subst {x = y} ⊢V (⊢case {x = x} ⊢L ⊢M ⊢N) with x ≟ y
... | yes refl        =  ⊢case (subst ⊢V ⊢L) (subst ⊢V ⊢M) (drop ⊢N)
... | no  x≢y         =  ⊢case (subst ⊢V ⊢L) (subst ⊢V ⊢M) (subst ⊢V (swap x≢y ⊢N))
subst {x = y} ⊢V (⊢μ {x = x} ⊢M) with x ≟ y
... | yes refl        =  ⊢μ (drop ⊢M)
... | no  x≢y         =  ⊢μ (subst ⊢V (swap x≢y ⊢M))

-- Exercise subst′ (stretch)

-- Rewrite subst to work with the modified definition _[_:=_]′ from the exercise in the previous chapter. As before, this should factor dealing with bound variables into a single function, defined by mutual recursion with the proof that substitution preserves types.

preserve : ∀ {M N A}
  → ∅ ⊢ M ⦂ A
  → M —→ N
    ----------
  → ∅ ⊢ N ⦂ A
preserve (⊢` ())
preserve (⊢ƛ ⊢N)                 ()
preserve (⊢L · ⊢M)               (ξ-·₁ L—→L′)     =  (preserve ⊢L L—→L′) · ⊢M
preserve (⊢L · ⊢M)               (ξ-·₂ VL M—→M′)  =  ⊢L · (preserve ⊢M M—→M′)
preserve ((⊢ƛ ⊢N) · ⊢V)          (β-ƛ VV)         =  subst ⊢V ⊢N
preserve ⊢zero                   ()
preserve (⊢suc ⊢M)               (ξ-suc M—→M′)    =  ⊢suc (preserve ⊢M M—→M′)
preserve (⊢case ⊢L ⊢M ⊢N)        (ξ-case L—→L′)   =  ⊢case (preserve ⊢L L—→L′) ⊢M ⊢N
preserve (⊢case ⊢zero ⊢M ⊢N)     β-zero           =  ⊢M
preserve (⊢case (⊢suc ⊢V) ⊢M ⊢N) (β-suc VV)       =  subst ⊢V ⊢N
preserve (⊢μ ⊢M)                 (β-μ)            =  subst (⊢μ ⊢M) ⊢M

data Gas : Set where
  gas : ℕ → Gas

data Finished (N : Term) : Set where

  done :
      Value N
      ----------
    → Finished N

  out-of-gas :
      ----------
      Finished N

data Steps (L : Term) : Set where

  steps : ∀ {N}
    → L —↠ N
    → Finished N
      ----------
    → Steps L

eval : ∀ {L A}
  → Gas
  → ∅ ⊢ L ⦂ A
    ---------
  → Steps L
eval {L} (gas zero)    ⊢L                             =  steps (L ∎) out-of-gas
eval {L} (gas (suc m)) ⊢L with progress ⊢L
... | done VL                                         =  steps (L ∎) (done VL)
... | step L—→M with eval (gas m) (preserve ⊢L L—→M)
...    | steps M—↠N fin                               =  steps (L —→⟨ L—→M ⟩ M—↠N) fin

⊢sucμ : ∅ ⊢ μ "x" ⇒ `suc ` "x" ⦂ `ℕ
⊢sucμ = ⊢μ (⊢suc (⊢` ∋x))
  where
  ∋x = Z

_ : eval (gas 3) ⊢sucμ ≡
  steps
   (μ "x" ⇒ `suc ` "x"
   —→⟨ β-μ ⟩
    `suc (μ "x" ⇒ `suc ` "x")
   —→⟨ ξ-suc β-μ ⟩
    `suc (`suc (μ "x" ⇒ `suc ` "x"))
   —→⟨ ξ-suc (ξ-suc β-μ) ⟩
    `suc (`suc (`suc (μ "x" ⇒ `suc ` "x")))
   ∎)
   out-of-gas
_ = refl

_ : eval (gas 100) (⊢twoᶜ · ⊢sucᶜ · ⊢zero) ≡
  steps
   ((ƛ "s" ⇒ (ƛ "z" ⇒ ` "s" · (` "s" · ` "z"))) · (ƛ "n" ⇒ `suc ` "n")
   · `zero
   —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
    (ƛ "z" ⇒ (ƛ "n" ⇒ `suc ` "n") · ((ƛ "n" ⇒ `suc ` "n") · ` "z")) ·
     `zero
   —→⟨ β-ƛ V-zero ⟩
    (ƛ "n" ⇒ `suc ` "n") · ((ƛ "n" ⇒ `suc ` "n") · `zero)
   —→⟨ ξ-·₂ V-ƛ (β-ƛ V-zero) ⟩
    (ƛ "n" ⇒ `suc ` "n") · `suc `zero
   —→⟨ β-ƛ (V-suc V-zero) ⟩
    `suc (`suc `zero)
   ∎)
   (done (V-suc (V-suc V-zero)))
_ = refl

-- Exercise mul-eval (recommended)

-- Using the evaluator, confirm that two times two is four.

⊢2*2 : ∅ ⊢ mul · two · two ⦂ `ℕ
⊢2*2 = ⊢mul · ⊢two · ⊢two

-- _ : eval (gas 100) (eval (gas 100) ⊢2*2) ≡ (expand via C-c C-n)

-- Exercise: progress-preservation

-- Without peeking at their statements above, write down the progress and preservation theorems for the simply typed lambda-calculus.

-- Exercise subject_expansion

-- We say that M reduces to N if M —→ N, but we can also describe the same situation by saying that N expands to M. The preservation property is sometimes called subject reduction. Its opposite is subject expansion, which holds if M —→ N and ∅ ⊢ N ⦂ A imply ∅ ⊢ M ⦂ A. Find two counter-examples to subject expansion, one with case expressions and one not involving case expressions.

Normal : Term → Set
Normal M  =  ∀ {N} → ¬ (M —→ N)

Stuck : Term → Set
Stuck M  =  Normal M × ¬ Value M

-- Exercise stuck

-- Give an example of an ill-typed term that does get stuck.

-- -- Your code goes here
-- Exercise unstuck (recommended)

-- Provide proofs of the three postulates, unstuck, preserves, and wttdgs above.

unstuck : ∀ {M A}
  → ∅ ⊢ M ⦂ A
    -----------
  → ¬ (Stuck M)
unstuck v ⟨ NormalLM , ¬ValueLM ⟩ with progress v
... | step M—→N = NormalLM M—→N
... | done ValueM = ¬ValueLM ValueM

preserves : ∀ {M N A}
  → ∅ ⊢ M ⦂ A
  → M —↠ N
    ---------
  → ∅ ⊢ N ⦂ A
preserves ∅⊢M⦂A (M ∎) = ∅⊢M⦂A
preserves ∅⊢L⦂A (L —→⟨ L—→M ⟩ M—↠N) = preserves (preserve ∅⊢L⦂A L—→M) M—↠N

wttdgs : ∀ {M N A}
  → ∅ ⊢ M ⦂ A
  → M —↠ N
    -----------
  → ¬ (Stuck N)
wttdgs ∅⊢M⦂A M—↠N = unstuck (preserves ∅⊢M⦂A M—↠N)

cong₄ : ∀ {A B C D E : Set} (f : A → B → C → D → E)
  {s w : A} {t x : B} {u y : C} {v z : D}
  → s ≡ w → t ≡ x → u ≡ y → v ≡ z → f s t u v ≡ f w x y z
cong₄ f refl refl refl refl = refl

det : ∀ {M M′ M″}
  → (M —→ M′)
  → (M —→ M″)
    --------
  → M′ ≡ M″
det (ξ-·₁ L—→L′)   (ξ-·₁ L—→L″)     =  cong₂ _·_ (det L—→L′ L—→L″) refl
det (ξ-·₁ L—→L′)   (ξ-·₂ VL M—→M″)  =  ⊥-elim (V¬—→ VL L—→L′)
det (ξ-·₁ L—→L′)   (β-ƛ _)          =  ⊥-elim (V¬—→ V-ƛ L—→L′)
det (ξ-·₂ VL _)    (ξ-·₁ L—→L″)     =  ⊥-elim (V¬—→ VL L—→L″)
det (ξ-·₂ _ M—→M′) (ξ-·₂ _ M—→M″)   =  cong₂ _·_ refl (det M—→M′ M—→M″)
det (ξ-·₂ _ M—→M′) (β-ƛ VM)         =  ⊥-elim (V¬—→ VM M—→M′)
det (β-ƛ _)        (ξ-·₁ L—→L″)     =  ⊥-elim (V¬—→ V-ƛ L—→L″)
det (β-ƛ VM)       (ξ-·₂ _ M—→M″)   =  ⊥-elim (V¬—→ VM M—→M″)
det (β-ƛ _)        (β-ƛ _)          =  refl
det (ξ-suc M—→M′)  (ξ-suc M—→M″)    =  cong `suc_ (det M—→M′ M—→M″)
det (ξ-case L—→L′) (ξ-case L—→L″)   =  cong₄ case_[zero⇒_|suc_⇒_]
                                         (det L—→L′ L—→L″) refl refl refl
det (ξ-case L—→L′) β-zero           =  ⊥-elim (V¬—→ V-zero L—→L′)
det (ξ-case L—→L′) (β-suc VL)       =  ⊥-elim (V¬—→ (V-suc VL) L—→L′)
det β-zero         (ξ-case M—→M″)   =  ⊥-elim (V¬—→ V-zero M—→M″)
det β-zero         β-zero           =  refl
det (β-suc VL)     (ξ-case L—→L″)   =  ⊥-elim (V¬—→ (V-suc VL) L—→L″)
det (β-suc _)      (β-suc _)        =  refl
det β-μ            β-μ              =  refl

-- Quiz

-- Suppose we add a new term zap with the following reduction rule

-- -------- β-zap
-- M —→ zap
-- and the following typing rule:

-- ----------- ⊢zap
-- Γ ⊢ zap ⦂ A
-- Which of the following properties remain true in the presence of these rules? For each property, write either “remains true” or “becomes false.” If a property becomes false, give a counterexample:

-- Determinism of step

-- Progress

-- Preservation

-- Quiz

-- Suppose instead that we add a new term foo with the following reduction rules:

-- ------------------ β-foo₁
-- (λ x ⇒ ` x) —→ foo

-- ----------- β-foo₂
-- foo —→ zero
-- Which of the following properties remain true in the presence of this rule? For each one, write either “remains true” or else “becomes false.” If a property becomes false, give a counterexample:

-- Determinism of step

-- Progress

-- Preservation

-- Quiz

-- Suppose instead that we remove the rule ξ·₁ from the step relation. Which of the following properties remain true in the absence of this rule? For each one, write either “remains true” or else “becomes false.” If a property becomes false, give a counterexample:

-- Determinism of step

-- Progress

-- Preservation

-- Quiz

-- We can enumerate all the computable function from naturals to naturals, by writing out all programs of type `ℕ ⇒ `ℕ in lexical order. Write fᵢ for the i‘th function in this list.

-- Say we add a typing rule that applies the above enumeration to interpret a natural as a function from naturals to naturals:

-- Γ ⊢ L ⦂ `ℕ
-- Γ ⊢ M ⦂ `ℕ
-- -------------- _·ℕ_
-- Γ ⊢ L · M ⦂ `ℕ
-- And that we add the corresponding reduction rule:

-- fᵢ(m) —→ n
-- ---------- δ
-- i · m —→ n
-- Which of the following properties remain true in the presence of this rule? For each one, write either “remains true” or else “becomes false.” If a property becomes false, give a counterexample:

-- Determinism of step

-- Progress

-- Preservation

-- Are all properties preserved in this case? Are there any other alterations we would wish to make to the system?

