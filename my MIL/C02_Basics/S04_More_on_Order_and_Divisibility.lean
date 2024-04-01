import MIL.Common
import Mathlib.Data.Real.Basic

namespace C02S04

section
variable (a b c d : ℝ)

#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

example : min a b = min b a := by
  apply le_antisymm
  · apply le_min
    · apply min_le_right
    apply min_le_left
  · show min b a ≤ min a b
    apply le_min
    · apply min_le_right
    apply min_le_left

example : min a b = min b a := by
  have h : ∀ x y : ℝ, min x y ≤ min y x := by
    intro x y
    apply le_min
    apply min_le_right
    apply min_le_left
  apply le_antisymm
  apply h
  apply h

example : min a b = min b a := by
  apply le_antisymm
  repeat
    apply le_min
    apply min_le_right
    apply min_le_left

example : max a b = max b a := by
  apply ge_antisymm
  repeat
    apply max_le
    . apply le_max_right
    . apply le_max_left


example : min (min a b) c = min a (min b c) := by
  sorry
theorem aux : min a b + c ≤ min (a + c) (b + c) := by
  sorry
example : min a b + c = min (a + c) (b + c) := by
  apply le_antisymm
  . apply aux
  -- . rw [← add_neg_cancel_right (min (a+c) (b+c)) (-c)]
  have : min (a + c) (b + c) -c ≤ min a b := by
    apply le_min
    -- apply sub_left_le_of_le_add
    -- rw [add_comm c a]
    -- exact min_le_left (a + c) (b + c)
    have : min (a + c) (b + c) ≤ a + c := min_le_left (a + c) (b + c)
    linarith
    have : min (a + c) (b + c) ≤ b + c := min_le_right (a + c) (b + c)
    linarith
  linarith

#check (abs_add : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)

example : |a| - |b| ≤ |a - b| := by
  nth_rw 1 [← sub_add_cancel a b]
  linarith [abs_add (a-b) b]
end

section
variable (w x y z : ℕ)

example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
  dvd_trans h₀ h₁

example : x ∣ y * x * z := by
  apply dvd_mul_of_dvd_left
  apply dvd_mul_left

example : x ∣ x ^ 2 := by
  apply dvd_mul_left

example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
  apply dvd_add
  apply dvd_add
  . rw [← mul_assoc]
    rw [mul_comm y x]
    rw [mul_assoc]
    exact dvd_mul_right x (y*z)
  . apply dvd_mul_left
  . rw [pow_two]
    apply dvd_trans h (dvd_mul_left w w)
end

section
variable (m n : ℕ)

#check (Nat.gcd_zero_right n : Nat.gcd n 0 = n)
#check (Nat.gcd_zero_left n : Nat.gcd 0 n = n)
#check (Nat.lcm_zero_right n : Nat.lcm n 0 = 0)
#check (Nat.lcm_zero_left n : Nat.lcm 0 n = 0)

example : Nat.gcd m n = Nat.gcd n m := by
  sorry
end
