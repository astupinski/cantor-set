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



--cantor set is uncountable/has infinite amount of point
--(set is countable -- 1-1 correspondence with natural number)
--(measure 0 = if the sum of the lengths of intervals enclosing all the points can be made arbitrarily small)
--(cardinal number is larger than that of the set of all natural numbers)















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
