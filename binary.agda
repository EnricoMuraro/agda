import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (x O) = x I
inc (x I) = (inc x) O

to : ℕ → Bin
to zero = ⟨⟩
to (suc x) = inc (to x)

from : Bin → ℕ
from ⟨⟩ = zero
from (x O) = (from x) * 2
from (x I) = suc ((from x) * 2)



infix 5 _+′_
_+′_ : Bin → Bin → Bin
⟨⟩ +′ n = n
m +′ ⟨⟩ = m
(m O) +′ (n O) = (m +′ n) O
(m O) +′ (n I) = (m +′ n) I
(m I) +′ (n O) = (m +′ n) I
(m I) +′ (n I) = inc (m +′ n) O


_ : ⟨⟩ I +′ (⟨⟩) ≡ ⟨⟩ I
_ = refl

_ : (⟨⟩ I I O I) +′ (⟨⟩ I I) ≡ (⟨⟩ I O O O O)
_ = refl

_*′_ : Bin → Bin → Bin
⟨⟩ *′ n = ⟨⟩
(m O) *′ n = (m *′ n) O
(m I) *′ n = n +′ ((m *′ n) O)

_ : (⟨⟩ I I I) *′ (⟨⟩ I O I O I) ≡ (⟨⟩ I O O I O O I I)
_ = refl

_ : (⟨⟩) *′ (⟨⟩ I I) ≡ ⟨⟩
_ = refl

_ : (⟨⟩ I I) *′ (⟨⟩) ≡ ⟨⟩ O O --you need the right number of zeros
_ = refl


postulate
  ⟨⟩-identity : ⟨⟩ O ≡ ⟨⟩ --I found it useful, but is it bad practice?

+-identityᵣ : ∀ (b : Bin) → b +′ ⟨⟩ ≡ b
+-identityᵣ ⟨⟩ = refl
+-identityᵣ (b O) = refl
+-identityᵣ (b I) = refl

*-identity : ∀ (b : Bin) → b *′ ⟨⟩ ≡ ⟨⟩
*-identity ⟨⟩ = refl
*-identity (b O) rewrite *-identity b = ⟨⟩-identity
*-identity (b I) rewrite *-identity b = ⟨⟩-identity

*-distr : ∀ (m n p : Bin) → (m +′ n) *′ p ≡ (m *′ p) +′ (n *′ p)
*-distr ⟨⟩ n p = refl
*-distr (m O) n p = {!!}
*-distr (m I) n p = {!!}

*-assoc : ∀ (m n p : Bin) → (m *′ n) *′ p ≡ m *′ (n *′ p)
*-assoc ⟨⟩ n p = refl
*-assoc (m O) n p = cong _O (*-assoc m n p)
*-assoc (m I) n p rewrite *-distr n ((m *′ n) O) p | *-assoc m n p = refl


inc-assoc : ∀ (m n : Bin) → (inc m) +′ n ≡ inc (m +′ n)
inc-assoc ⟨⟩ ⟨⟩ = refl
inc-assoc ⟨⟩ (n O) = refl
inc-assoc ⟨⟩ (n I) = refl
inc-assoc (m O) ⟨⟩ = refl
inc-assoc (m O) (n O) = refl
inc-assoc (m O) (n I) = refl
inc-assoc (m I) ⟨⟩ = refl
inc-assoc (m I) (n O) = cong _O (inc-assoc m n)
inc-assoc (m I) (n I) = cong _I (inc-assoc m n)

inc-assocᵣ : ∀ (m n : Bin) → m +′ (inc n) ≡ inc (m +′ n)
inc-assocᵣ ⟨⟩ ⟨⟩ = refl
inc-assocᵣ ⟨⟩ (n O) = refl
inc-assocᵣ ⟨⟩ (n I) = refl
inc-assocᵣ (m O) ⟨⟩ = cong _I (+-identityᵣ m)
inc-assocᵣ (m O) (n O) = refl
inc-assocᵣ (m O) (n I) = cong _O (inc-assocᵣ m n)
inc-assocᵣ (m I) ⟨⟩ = cong _O (cong inc (+-identityᵣ m))
inc-assocᵣ (m I) (n O) = refl
inc-assocᵣ (m I) (n I) = cong _I (inc-assocᵣ m n)


+-assoc : ∀ (m n p : Bin) → (m +′ n) +′ p ≡ m +′ (n +′ p)
+-assoc ⟨⟩ n p = refl
+-assoc (m O) ⟨⟩ p = refl
+-assoc (m O) (n O) ⟨⟩ = refl
+-assoc (m O) (n O) (p O) = cong _O (+-assoc m n p)
+-assoc (m O) (n O) (p I) = cong _I (+-assoc m n p)
+-assoc (m O) (n I) ⟨⟩ = refl
+-assoc (m O) (n I) (p O) = cong _I (+-assoc m n p)
+-assoc (m O) (n I) (p I) =
  begin
    (inc ((m +′ n) +′ p) O)
  ≡⟨ cong _O (cong inc (+-assoc m n p)) ⟩
    (inc (m +′ (n +′ p)) O)
  ≡⟨ cong _O (sym (inc-assocᵣ m (n +′ p))) ⟩
    ((m +′ inc (n +′ p)) O)
  ∎
+-assoc (m I) ⟨⟩ p = refl
+-assoc (m I) (n O) ⟨⟩ = refl
+-assoc (m I) (n O) (p O) = cong _I (+-assoc m n p)
+-assoc (m I) (n O) (p I) = cong _O (cong inc (+-assoc m n p))
+-assoc (m I) (n I) ⟨⟩ = refl
+-assoc (m I) (n I) (p O) =
  begin
    ((inc (m +′ n) +′ p) O)
  ≡⟨ cong _O (inc-assoc (m +′ n) p) ⟩
    (inc ((m +′ n) +′ p) O)
  ≡⟨ cong _O (cong inc (+-assoc m n p)) ⟩
    (inc (m +′ (n +′ p)) O)
  ∎
+-assoc (m I) (n I) (p I) =
  begin
    ((inc (m +′ n) +′ p) I)
  ≡⟨ cong _I (inc-assoc (m +′ n) p) ⟩
    (inc ((m +′ n) +′ p) I)
  ≡⟨ cong _I (cong inc (+-assoc m n p)) ⟩
    (inc (m +′ (n +′ p)) I)
  ≡⟨ cong _I (sym (inc-assocᵣ m (n +′ p))) ⟩
    ((m +′ inc (n +′ p)) I)
  ∎


+-comm : ∀ (m n : Bin) → m +′ n ≡ n +′ m
+-comm ⟨⟩ n = sym (+-identityᵣ n)
+-comm (m O) ⟨⟩ = refl
+-comm (m O) (n O) = cong _O (+-comm m n)
+-comm (m O) (n I) = cong _I (+-comm m n)
+-comm (m I) ⟨⟩ = refl
+-comm (m I) (n O) = cong _I (+-comm m n)
+-comm (m I) (n I) = cong _O (cong inc (+-comm m n))


*-comm : ∀ (m n : Bin) → m *′ n ≡ n *′ m
*-comm ⟨⟩ n = sym (*-identity n)
*-comm (m O) n = {!!}
*-comm (m I) n = {!!}

data _≤_ : Bin → Bin → Set where
  z≤n : ∀ {n : Bin} → ⟨⟩ ≤ n
  s≤s : ∀ {m n : Bin} → m ≤ n → inc m ≤ inc n

infix 4 _≤_

_ : ⟨⟩ I  ≤ ⟨⟩ I I
_ = s≤s {⟨⟩} {((⟨⟩ I) O)} (z≤n)
-- gives an error if the numbers are not explicitly given.
-- it might be because the same number can have any amount of leading zeros
-- so the representation of the number isn't unique?



data _<_ : Bin → Bin → Set where
  z<s : ∀ {n : Bin} → ⟨⟩ < inc n
  s<s : ∀ {m n : Bin} → m < n → inc m < inc n

infix 4 _<_

_ : ⟨⟩ I < ⟨⟩ I I
_ = s<s {⟨⟩} {⟨⟩ I O} (z<s {⟨⟩ I})
