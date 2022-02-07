module induction where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; _≢_)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)

open import Function
open import Data.Product using (Σ; _,_)

+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p = refl
+-assoc (suc m) n p = cong suc (+-assoc m n p)

+-identityʳ : ∀ (m : ℕ) → m + zero ≡ m
+-identityʳ zero = refl
+-identityʳ (suc m) = cong suc (+-identityʳ m)

+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n = refl
+-suc (suc m) n = cong suc (+-suc m n)

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero = +-identityʳ m
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
to zero = ⟨⟩
to (suc x) = inc (to x)


from : Bin → ℕ
from ⟨⟩ = zero
from (x O) = (from x) * 2
from (x I) = suc ((from x) * 2)

lemma : ∀ (n : ℕ) → (suc n) * 2 ≡ suc (suc (n * 2))
lemma zero = refl
lemma (suc n) = refl

binlaw : ∀ (b : Bin) →  from (inc b) ≡ suc (from b)
binlaw ⟨⟩ = refl
binlaw (b O) = refl
binlaw (b I) =
  begin
    from (inc (b I))
  ≡⟨⟩
    from ((inc b) O)
  ≡⟨⟩
    (from (inc b)) * 2
  ≡⟨ cong (λ x → x * 2 ) (binlaw b) ⟩
    (suc (from b)) * 2
  ≡⟨⟩
    suc (suc ((from b) * 2))
  ≡⟨⟩
    suc (from (b I))
  ∎


binlaw′ : ∀ (n : ℕ) → from (to n) ≡ n
binlaw′ zero = refl
binlaw′ (suc n) =
  begin
    from (to (suc n))
  ≡⟨⟩
    from (inc (to n))
  ≡⟨ binlaw (to n) ⟩
    suc (from (to n))
  ≡⟨ cong suc (binlaw′ n) ⟩
    suc n
  ∎
    

binlaw″ : Σ Bin (λ x → to (from x) ≢ x )
binlaw″ = (⟨⟩ O O I) , λ()
    
  
