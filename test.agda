import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

module test where

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

_+_ : ℕ → ℕ → ℕ
zero + n = n
(suc m) + n = suc (m + n)


_ : 2 + 3 ≡ 5
_ =
  begin
    2 + 3
  ≡⟨⟩
    (suc (suc zero)) + (suc (suc (suc zero)))
  ≡⟨⟩
    suc ((suc zero) + (suc (suc (suc zero))))
  ≡⟨⟩
    suc (suc (zero + (suc (suc (suc zero)))))
  ≡⟨⟩
    suc (suc (suc (suc (suc zero))))
  ≡⟨⟩
    5
  ∎


_*_ : ℕ → ℕ → ℕ
zero * m = zero
suc n * m = (n * m) + m

{-# BUILTIN NATPLUS _+_ #-}


data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin


inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (x O) = x I
inc (x I) = (inc x) O

_ : inc (⟨⟩ O O I I) ≡ ⟨⟩ O I O O
_ = refl

_ : inc (⟨⟩ I) ≡ ⟨⟩ I O
_ = refl

to : ℕ → Bin
to zero = ⟨⟩ O
to (suc x) = inc (to x)


from : Bin → ℕ
from ⟨⟩ = 0
from (x O) = (from x) * 2
from (x I) = ((from x) * 2) + 1

_ : (from (⟨⟩ I I O I)) ≡ 13
_ = refl


_ : (to 2) ≡ (⟨⟩ I O)
_ =
  begin
    to 2
  ≡⟨⟩
    to (suc 1)
  ≡⟨⟩
    inc (to 1)
  ≡⟨⟩
    inc (inc (to zero))
  ≡⟨⟩
    inc (inc (⟨⟩ O))
  ≡⟨⟩
    inc (⟨⟩ I)
  ≡⟨⟩
    ⟨⟩ I O
  ∎

_ : (to 12) ≡ (⟨⟩ I I O O)
_ = refl
    

