import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-comm; +-identityʳ)

data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n : ℕ} → zero ≤ n
  s≤s : ∀ {m n : ℕ} → m ≤ n → suc m ≤ suc n


_ : 2 ≤ 4
_ = s≤s (s≤s z≤n)

infix 4 _≤_

≤-refl : ∀ {n : ℕ} → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl

≤-trans : ∀ {m n p : ℕ} → m ≤ n → n ≤ p → m ≤ p
≤-trans z≤n n≤p = z≤n
≤-trans (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans m≤n n≤p)

≤-antisym : ∀ {m n : ℕ} → m ≤ n → n ≤ m → m ≡ n
≤-antisym z≤n z≤n = refl
≤-antisym (s≤s m≤n) (s≤s n≤m) = cong suc (≤-antisym m≤n n≤m)


data Total (m n : ℕ) : Set where
  forward : m ≤ n → Total m n
  flipped : n ≤ m → Total m n

≤-total : ∀ (m n : ℕ) → Total m n
≤-total zero n = forward z≤n
≤-total (suc m) zero = flipped z≤n
≤-total (suc m) (suc n) with ≤-total m n
...                          | forward m≤n = forward (s≤s m≤n)
...                          | flipped n≤m = flipped (s≤s n≤m)


infix 4 _<_

data _<_ : ℕ → ℕ → Set where
  z<s : ∀ {n : ℕ} → zero < suc n
  s<s : ∀ {m n : ℕ} → m < n → suc m < suc n


<-trans : ∀ {m n p : ℕ} → m < n → n < p → m < p
<-trans z<s (s<s n<p) = z<s
<-trans (s<s m<n) (s<s n<p) = s<s (<-trans m<n n<p)

data Trichotomy (m n : ℕ) : Set where
  less : m < n → Trichotomy m n
  equal : m ≡ n → Trichotomy m n
  greater : n < m → Trichotomy m n

<-trichotomy : ∀ (m n : ℕ) → Trichotomy m n
<-trichotomy zero zero = equal refl
<-trichotomy zero (suc n) = less z<s
<-trichotomy (suc m) zero = greater z<s
<-trichotomy (suc m) (suc n) with <-trichotomy m n
...                              | less m<n = less (s<s m<n)
...                              | equal m≡n = equal (cong suc m≡n)
...                              | greater n<m = greater (s<s n<m)

≤-iff-< : ∀ {m n : ℕ} → suc m ≤ n → m < n
≤-iff-< (s≤s z≤n) = z<s
≤-iff-< (s≤s (s≤s m≤n)) = s<s (≤-iff-< ((s≤s m≤n)))


data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (x O) = x I
inc (x I) = (inc x) O

to : ℕ → Bin
to zero = ⟨⟩ O
to (suc x) = inc (to x)

from : Bin → ℕ
from ⟨⟩ = 0
from (x O) = (from x) * 2
from (x I) = ((from x) * 2) + 1



data One : Bin → Set where
  isOne :  One (⟨⟩ I)
  
  

