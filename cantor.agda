module cantor where

import Basics002

data ℘ (A : Set) : Set where
  --constructor 𝓅
  --field φ : A → Set

--data set (A : Set) : Set where
--  ℘ : set A
--  _∷_ : A → set A → set A

--{A : Set} → A → A
--℘ A = A

data set-of-reals (A : Set) : Basics002.ℝ → Set where
 -- ℘ : set-of-reals A Z
 -- _∷_ : ∀ {x} → A → set-of-reals A x → set-of-reals A (S x) 

--an interval defines a set of reals.

data interval (A : Set) (x,y : Basics002.ℝ) : ℘ A → ℘ A where
--:= { z | x < z < y }

data _∪_ (A : Set) : ℘ A → ℘ A → ℘ A where
--_∪_ : ℘ A → ℘ A → ℘ A
--X ∪ Y = (λ x → X x ∨ Y x)

--for intersection you use ∧

--now you can use ∪ and ℘ to define the nth cantor approximation

--real-set = ℝ → Set
  --             ^^^
    --           prop

--defn: cantor set is a set of 2^n intervals (each of length 3^(-n))
data cantor-set (A : set-of-reals) : A → A where

--X : ℘ A
--X = { x | φ(x) }
          --^
--          characteristic function
  --        classically φ : A → 𝔹
    --      less-classically we want φ : A → prop
