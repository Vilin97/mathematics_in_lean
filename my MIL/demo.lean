-- define the cone
-- sum of λ₁ * a₁ + ... + λₘ * aₘ
-- aᵢ are vectors, λᵢ are non-negative numbers

-- pieces:
-- 1. how to do a finite sum?
-- 2. how to define a sequnce of numbers λ₁ ... λₘ?
-- 3. how to define a vector?
-- 4. How to make a nonnegative number?
-- 5. scalar-vector mulplication

-- 1. Finite sums
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

open Finset
open BigOperators
variable (s : Finset ℕ) (f : ℕ → ℕ)

#check ∑ x in s, f x

variables (n : ℕ)
#check Fin n
#check ∑ x in range n, x
example (x : Fin n) : x ∈ (Set.univ : Set (Fin n)) := trivial
#check (Set.univ : Set (Fin n))

variable (n : ℕ) (g : Fin n → ℕ) (h : Fin 2 → ℕ) [NeZero n]
#check ∑ x in (univ : Finset (Fin n)), g x
#check ∑ x in range n, g x
#check ∑ x in range 2, h x

variable (i : Fin n) (j : range n) [NeZero n]
-- variable (i : Fin 2) (j : range 2)
#check i=j

-- 2. sequnce of numbers?
variables (a : Fin 4 → ℕ)

#check a 5

-- 3. vector?
#check EuclideanSpace ℝ (Fin 3)

-- 4. nonegative number
#check NNReal

-- define a cone
noncomputable section
def cone (s : Fin n → NNReal) (v : Fin n → EuclideanSpace ℝ (Fin d)) [NeZero n] := ∑ i in range n, s i • v i
