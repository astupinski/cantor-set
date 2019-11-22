module cantor where

open import Basics002 --reals, real postulates, power set, union/intersection


postulate
  _≤ᴿ_ : ℝ → ℝ → Set
  _<ᴿ_ : ℝ → ℝ → Set


--data types

interval : Set
interval = ℝ ∧ ℝ

zero-one : interval
zero-one = ⟨ 𝕣 0 , 𝕣 1 ⟩


interval-set : interval → ℘ ℝ
interval-set ⟨ lb , ub ⟩ = 𝓅 (λ x → lb <ᴿ x ∧ x <ᴿ ub)

_ : map (λ x → x + 5) [ 1 , 2 , 3 ] ≡ [ 6 , 7 , 8 ]
_ = ↯

mapᴾ : (ℝ → ℝ) → ℘ ℝ → ℘ ℝ
mapᴾ f (𝓅 φ) = 𝓅 λ x₀ → φ x₀


--cantor set declaration

C₀ : ℘ ℝ
C₀ = interval-set ⟨ 𝕣 0 , 𝕣 1 ⟩

C₁ : ℘ ℝ
C₁ = mapᴾ (λ x → x /ʳ 𝕣 3) C₀ ⊍ mapᴾ (λ x → (x /ʳ 𝕣 3) +ʳ (𝕣 2 /ʳ 𝕣 3)) C₀

C : ℕ → ℘ ℝ
C Z = C₀
C (S n) =
  let Cₙ₋₁ = C n
  in mapᴾ (λ x → x /ʳ 𝕣 3) Cₙ₋₁ ⊍ mapᴾ (λ x → (x /ʳ 𝕣 3) +ʳ (𝕣 2 /ʳ 𝕣 3)) Cₙ₋₁

--element in cantor set

in-cantor : ℝ → Set
in-cantor r = ∀ n → r ∈ C n

--cantor set has measure zero (length zero)
--C(infinity) = lim(n-> inf) (2/3)^n = 0
--length zero : has no intervals
--to prove C (cantor set) has length zero, show that the length of the complement of C relative to [0,1] is 1
--at the n step, we are removing 2^(n-1) intervals, all of which are of length 1/3^n
--the sum of the length of all intervals removed is:
--sum(2^(n-1)*(1/3^n) = 1


--cantor set is uncountable/has infinite amount of point
--(set is countable -- 1-1 correspondence with natural number)
--(measure 0 = if the sum of the lengths of intervals enclosing all the points can be made arbitrarily small)
--(cardinal number is larger than that of the set of all natural numbers)
--to show cantor set is uncountable, construct a function f from the Cantor set C to the closed interval [0,1] that is surjective
--consider the point in C in terms of base 3
--we have that for any x = 0.a1a2..a3 in [0,1], x in C, iff an in {0,2} for all n in ℕ
--construct function F: C → [0,1] which replaces all the 2s and 1s and interprets sequence as a binary representation of a real number.
-- f( sum(ak*3^-k) )
--for any number y in [0,1], its binary representation can be translated into a ternary representation of a number x in C by replacing
--all the 1s by 2s, so the range of f is [0,1]. thus, the cardinality of C is greater than or equal to the cardinality of [0,1], which
--means that C is uncountable 















-- data ℘ (A : Set) : Set where
--   --constructor 𝓅
--   --field φ : A → Set

--data set (A : Set) : Set where
--  ℘ : set A
--  _∷_ : A → set A → set A

--{A : Set} → A → A
--℘ A = A

--data set-of-reals (A : Set) : ℝ → Set where
 -- ℘ : set-of-reals A Z
 -- _∷_ : ∀ {x} → A → set-of-reals A x → set-of-reals A (S x) 

--an interval defines a set of reals.

-- data interval (A : Set) (x,y : ℝ) : ℘ A → ℘ A where
-- --:= { z | x < z < y }

-- data interval : Set where
--   ❪_,_❫ : ℝ → ℝ → interval
-- 
-- record interval-2 : Set where
--   constructor ❪_,_❫
--   field
--     lb : ℝ
--     ub : ℝ

-- data _∪_ (A : Set) : ℘ A → ℘ A → ℘ A where
-- --_∪_ : ℘ A → ℘ A → ℘ A
-- --X ∪ Y = (λ x → X x ∨ Y x)

--for intersection you use ∧

--now you can use ∪ and ℘ to define the nth cantor approximation

--real-set = ℝ → Set
  --             ^^^
    --           prop

-- --defn: cantor set is a set of 2^n intervals (each of length 3^(-n))
-- data cantor-set (A : set-of-reals) : A → A where

--X : ℘ A
--X = { x | φ(x) }
          --^
--          characteristic function
  --        classically φ : A → 𝔹
    --      less-classically we want φ : A → prop