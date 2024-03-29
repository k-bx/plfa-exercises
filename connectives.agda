module connectives where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)
open import Function using (_∘_)
open import isomorphisms using (_≃_; _≲_; extensionality)
open isomorphisms.≃-Reasoning

data _×_ (A B : Set) : Set where

  ⟨_,_⟩ :
      A
    → B
      -----
    → A × B

proj₁ : ∀ {A B : Set}
  → A × B
    -----
  → A
proj₁ ⟨ x , y ⟩ = x

proj₂ : ∀ {A B : Set}
  → A × B
    -----
  → B
proj₂ ⟨ x , y ⟩ = y

η-× : ∀ {A B : Set} (w : A × B) → ⟨ proj₁ w , proj₂ w ⟩ ≡ w
η-× ⟨ x , y ⟩ = refl

infixr 2 _×_

×-comm : ∀ {A B : Set} → A × B ≃ B × A
×-comm =
  record
    { to       =  λ{ ⟨ x , y ⟩ → ⟨ y , x ⟩ }
    ; from     =  λ{ ⟨ y , x ⟩ → ⟨ x , y ⟩ }
    ; from∘to  =  λ{ ⟨ x , y ⟩ → refl }
    ; to∘from  =  λ{ ⟨ y , x ⟩ → refl }
    }

×-assoc : ∀ {A B C : Set} → (A × B) × C ≃ A × (B × C)
×-assoc =
  record
    { to      = λ{ ⟨ ⟨ x , y ⟩ , z ⟩ → ⟨ x , ⟨ y , z ⟩ ⟩ }
    ; from    = λ{ ⟨ x , ⟨ y , z ⟩ ⟩ → ⟨ ⟨ x , y ⟩ , z ⟩ }
    ; from∘to = λ{ ⟨ ⟨ x , y ⟩ , z ⟩ → refl }
    ; to∘from = λ{ ⟨ x , ⟨ y , z ⟩ ⟩ → refl }
    }

-- Exercise ⇔≃× (recommended)
-- Show that A ⇔ B as defined earlier is isomorphic to (A → B) × (B → A).

open import isomorphisms

⇔≃× : ∀ {A B : Set}
  → A ⇔ B ≃ (A → B) × (B → A)
⇔≃× =
  record
    { to = λ z → ⟨ _⇔_.to z , _⇔_.from z ⟩
    ; from = λ {⟨ x , y ⟩ → record { to = x ; from = y }}
    ; from∘to = λ x → refl
    ; to∘from = λ {⟨ x , y ⟩ → refl}
    }

data ⊤ : Set where

  tt :
    --
    ⊤

η-⊤ : ∀ (w : ⊤) → tt ≡ w
η-⊤ tt = refl

⊤-count : ⊤ → ℕ
⊤-count tt = 1

⊤-identityˡ : ∀ {A : Set} → ⊤ × A ≃ A
⊤-identityˡ =
  record
    { to      = λ{ ⟨ tt , x ⟩ → x }
    ; from    = λ{ x → ⟨ tt , x ⟩ }
    ; from∘to = λ{ ⟨ tt , x ⟩ → refl }
    ; to∘from = λ{ x → refl }
    }

⊤-identityʳ : ∀ {A : Set} → (A × ⊤) ≃ A
⊤-identityʳ {A} =
  ≃-begin
    (A × ⊤)
  ≃⟨ ×-comm ⟩
    (⊤ × A)
  ≃⟨ ⊤-identityˡ ⟩
    A
  ≃-∎

data _⊎_ (A B : Set) : Set where

  inj₁ :
      A
      -----
    → A ⊎ B

  inj₂ :
      B
      -----
    → A ⊎ B

case-⊎ : ∀ {A B C : Set}
  → (A → C)
  → (B → C)
  → A ⊎ B
    -----------
  → C
case-⊎ f g (inj₁ x) = f x
case-⊎ f g (inj₂ y) = g y

η-⊎ : ∀ {A B : Set} (w : A ⊎ B) → case-⊎ inj₁ inj₂ w ≡ w
η-⊎ (inj₁ x) = refl
η-⊎ (inj₂ y) = refl

uniq-⊎ : ∀ {A B C : Set} (h : A ⊎ B → C) (w : A ⊎ B) →
  case-⊎ (h ∘ inj₁) (h ∘ inj₂) w ≡ h w
uniq-⊎ h (inj₁ x) = refl
uniq-⊎ h (inj₂ y) = refl

infix 1 _⊎_


-- Exercise ⊎-comm (recommended)
-- Show sum is commutative up to isomorphism.

⊎-comm : ∀ {A B : Set}
  → A ⊎ B ≃ B ⊎ A
⊎-comm =
  record
    { to = λ{ (inj₁ x) → inj₂ x ; (inj₂ x) → inj₁ x}
    ; from = λ{ (inj₁ x) → inj₂ x ; (inj₂ x) → inj₁ x}
    ; from∘to = λ{ (inj₁ x) → refl ; (inj₂ x) → refl}
    ; to∘from = λ{ (inj₁ x) → refl ; (inj₂ x) → refl}
    }

-- Exercise ⊎-assoc
-- Show sum is associative up to isomorphism.

⊎-assoc : ∀ {A B C : Set}
  → (A ⊎ B) ⊎ C ≃ A ⊎ (B ⊎ C)
⊎-assoc =
  record
    { to = λ{ (inj₁ (inj₁ x)) → inj₁ x ; (inj₁ (inj₂ x)) → inj₂ (inj₁ x) ; (inj₂ x) → inj₂ (inj₂ x)}
    ; from = λ{ (inj₁ x) → inj₁ (inj₁ x) ; (inj₂ (inj₁ x)) → inj₁ (inj₂ x) ; (inj₂ (inj₂ x)) → inj₂ x}
    ; from∘to = λ{ (inj₁ (inj₁ x)) → refl ; (inj₁ (inj₂ x)) → refl ; (inj₂ x) → refl}
    ; to∘from = λ{ (inj₁ x) → refl ; (inj₂ (inj₁ x)) → refl ; (inj₂ (inj₂ x)) → refl}
    }

data ⊥ : Set where
  -- no clauses!

⊥-elim : ∀ {A : Set}
  → ⊥
    --
  → A
⊥-elim ()

uniq-⊥ : ∀ {C : Set} (h : ⊥ → C) (w : ⊥) → ⊥-elim w ≡ h w
uniq-⊥ h ()

⊥-count : ⊥ → ℕ
⊥-count ()

-- Exercise ⊥-identityˡ (recommended)
-- Show empty is the left identity of sums up to isomorphism.

⊥-identityˡ : ∀ { A : Set }
  → ⊥ ⊎ A ≃ A
⊥-identityˡ =
  record
    { to = λ{ (inj₂ x) → x}
    ; from = λ{ x → inj₂ x}
    ; from∘to = λ{ (inj₂ x) → refl}
    ; to∘from = λ{y → refl}
    }

-- Exercise ⊥-identityʳ
-- Show empty is the right identity of sums up to isomorphism.

⊥-identityʳ : ∀ { A : Set }
  → A ⊎ ⊥ ≃ A
⊥-identityʳ =
  record
    { to = λ{ (inj₁ x) → x}
    ; from = inj₁
    ; from∘to = λ{ (inj₁ x) → refl}
    ; to∘from = λ{y → refl}
    }

→-elim : ∀ {A B : Set}
  → (A → B)
  → A
    -------
  → B
→-elim L M = L M

η-→ : ∀ {A B : Set} (f : A → B) → (λ (x : A) → f x) ≡ f
η-→ f = refl

currying : ∀ {A B C : Set} → (A → B → C) ≃ (A × B → C)
currying =
  record
    { to      =  λ{ f → λ{ ⟨ x , y ⟩ → f x y }}
    ; from    =  λ{ g → λ{ x → λ{ y → g ⟨ x , y ⟩ }}}
    ; from∘to =  λ{ f → refl }
    ; to∘from =  λ{ g → extensionality λ{ ⟨ x , y ⟩ → refl }}
    }

→-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B → C) ≃ ((A → C) × (B → C))
→-distrib-⊎ =
  record
    { to      = λ{ f → ⟨ f ∘ inj₁ , f ∘ inj₂ ⟩ }
    ; from    = λ{ ⟨ g , h ⟩ → λ{ (inj₁ x) → g x ; (inj₂ y) → h y } }
    ; from∘to = λ{ f → extensionality λ{ (inj₁ x) → refl ; (inj₂ y) → refl } }
    ; to∘from = λ{ ⟨ g , h ⟩ → refl }
    }

→-distrib-× : ∀ {A B C : Set} → (A → B × C) ≃ (A → B) × (A → C)
→-distrib-× =
  record
    { to      = λ{ f → ⟨ proj₁ ∘ f , proj₂ ∘ f ⟩ }
    ; from    = λ{ ⟨ g , h ⟩ → λ x → ⟨ g x , h x ⟩ }
    ; from∘to = λ{ f → extensionality λ{ x → η-× (f x) } }
    ; to∘from = λ{ ⟨ g , h ⟩ → refl }
    }


×-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B) × C ≃ (A × C) ⊎ (B × C)
×-distrib-⊎ =
  record
    { to      = λ{ ⟨ inj₁ x , z ⟩ → (inj₁ ⟨ x , z ⟩)
                 ; ⟨ inj₂ y , z ⟩ → (inj₂ ⟨ y , z ⟩)
                 }
    ; from    = λ{ (inj₁ ⟨ x , z ⟩) → ⟨ inj₁ x , z ⟩
                 ; (inj₂ ⟨ y , z ⟩) → ⟨ inj₂ y , z ⟩
                 }
    ; from∘to = λ{ ⟨ inj₁ x , z ⟩ → refl
                 ; ⟨ inj₂ y , z ⟩ → refl
                 }
    ; to∘from = λ{ (inj₁ ⟨ x , z ⟩) → refl
                 ; (inj₂ ⟨ y , z ⟩) → refl
                 }
    }

⊎-distrib-× : ∀ {A B C : Set} → (A × B) ⊎ C ≲ (A ⊎ C) × (B ⊎ C)
⊎-distrib-× =
  record
    { to      = λ{ (inj₁ ⟨ x , y ⟩) → ⟨ inj₁ x , inj₁ y ⟩
                 ; (inj₂ z)         → ⟨ inj₂ z , inj₂ z ⟩
                 }
    ; from    = λ{ ⟨ inj₁ x , inj₁ y ⟩ → (inj₁ ⟨ x , y ⟩)
                 ; ⟨ inj₁ x , inj₂ z ⟩ → (inj₂ z)
                 ; ⟨ inj₂ z , _      ⟩ → (inj₂ z)
                 }
    ; from∘to = λ{ (inj₁ ⟨ x , y ⟩) → refl
                 ; (inj₂ z)         → refl
                 }
    }

-- Exercise ⊎-weak-× (recommended)

-- Show that the following property holds:

⊎-weak-× : ∀ {A B C : Set} → (A ⊎ B) × C → A ⊎ (B × C)
⊎-weak-× = λ{ ⟨ inj₁ x , x₁ ⟩ → inj₁ x ; ⟨ inj₂ x , x₁ ⟩ → inj₂ ⟨ x , x₁ ⟩}

-- This is called a weak distributive law. Give the corresponding distributive law, and explain how it relates to the weak version.

⊎-× : ∀ {A B C : Set} → (A ⊎ B) × C → (A × C) ⊎ (B × C)
⊎-× = λ{ ⟨ inj₁ x , x₁ ⟩ → inj₁ ⟨ x , x₁ ⟩ ; ⟨ inj₂ x , x₁ ⟩ → inj₂ ⟨ x , x₁ ⟩}

-- Exercise ⊎×-implies-×⊎

-- Show that a disjunct of conjuncts implies a conjunct of disjuncts:

⊎×-implies-×⊎ : ∀ {A B C D : Set} → (A × B) ⊎ (C × D) → (A ⊎ C) × (B ⊎ D)
⊎×-implies-×⊎ = λ{ (inj₁ ⟨ x , x₁ ⟩) → ⟨ inj₁ x , inj₁ x₁ ⟩ ; (inj₂ ⟨ x , x₁ ⟩) → ⟨ inj₂ x , inj₂ x₁ ⟩}

-- Does the converse hold? If so, prove; if not, give a counterexample.

×⊎-implies-⊎× : ∀ {A B C D : Set} → (A ⊎ C) × (B ⊎ D) → (A × B) ⊎ (C × D)
×⊎-implies-⊎× =
  λ{ ⟨ inj₁ x , inj₁ x₁ ⟩ → inj₁ ⟨ x , x₁ ⟩
   ; ⟨ inj₁ x , inj₂ x₁ ⟩ → {!!} -- this is impossible
   ; ⟨ inj₂ x , inj₁ x₁ ⟩ → {!!} -- this is impossible
   ; ⟨ inj₂ x , inj₂ x₁ ⟩ → inj₂ ⟨ x , x₁ ⟩}
