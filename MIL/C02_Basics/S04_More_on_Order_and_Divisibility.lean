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
  · show min a b ≤ min b a
    apply le_min
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
  apply le_antisymm
  · show max a b ≤ max b a
    apply max_le
    · apply le_max_right
    apply le_max_left


  · show max b a ≤ max a b
    apply max_le
    · apply le_max_right
    apply le_max_left

example : min (min a b) c = min a (min b c) := by
  exact min_assoc a b c

#check add_neg_cancel_right
theorem aux : min a b + c ≤ min (a + c) (b + c) := by
  have h₁ : min a b + c≤ a + c := by
    have h₂ : min a b ≤ a := by apply min_le_left
    linarith
  have h₃ : min a b + c ≤ b + c := by
    have h₄ : min a b ≤ b := by apply min_le_right
    linarith
  apply le_min
  exact h₁
  exact h₃

example : min a b + c = min (a + c) (b + c) := by
  apply le_antisymm
  · apply aux

  have h₂ : min (a+c) (b+c) ≤ min a b + c := by
    have h₁ : min (a+c) (b+c)+ - c ≤ min (a+c+-c) (b+c+-c) := by exact aux (a+c) (b+c) (-c)
    repeat rw [add_neg_cancel_right] at h₁
    linarith
  exact h₂



#check (abs_add_le : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)
#check add_sub_cancel_right
#check sub_add_cancel


example : |a| - |b| ≤ |a - b| := by
  have h₁ : |a-b+b| ≤ |a-b| + |b| := by exact abs_add_le (a-b) b

  rw [sub_add_cancel] at h₁
  linarith


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
  have h₁ : x ∣ y * (x*z) := by
    have h₂ : x ∣ x*z := by apply dvd_mul_right
    nth_rw 2 [mul_comm]
    rw [← mul_assoc]
    apply dvd_mul_left
  have h₃ : x ∣ x^2 := by apply dvd_mul_left
  have h₄ : x ∣ w^2 := by
    rw [pow_two]
    apply dvd_mul_of_dvd_left
    exact h
  have h₅: x ∣ y * (x * z) + x ^ 2 := by
    apply dvd_add h₁
    exact h₃
  have h₆: x ∣ y * (x * z) + x ^ 2 + w ^ 2:= by
    apply dvd_add h₅
    exact h₄
  exact h₆

#check dvd_add


end

section
variable (m n : ℕ)

#check (Nat.gcd_zero_right n : Nat.gcd n 0 = n)
#check (Nat.gcd_zero_left n : Nat.gcd 0 n = n)
#check (Nat.lcm_zero_right n : Nat.lcm n 0 = 0)
#check (Nat.lcm_zero_left n : Nat.lcm 0 n = 0)

example : Nat.gcd m n = Nat.gcd n m := by
  apply Nat.dvd_antisymm
  repeat
    apply Nat.dvd_gcd
    apply Nat.gcd_dvd_right
    apply Nat.gcd_dvd_left

end

#check dvd_antisymm
#check dvd_trans
#check gcd_dvd_left
