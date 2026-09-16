import Mathlib.Analysis.SpecialFunctions.Log.Basic
import MIL.Common

variable (a b c d e : ℝ)
open Real

#check (le_refl : ∀ a : ℝ, a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)

section
variable (h : a ≤ b) (h' : b ≤ c)

#check (le_refl : ∀ a : Real, a ≤ a)
#check (le_refl a : a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
#check (le_trans h : b ≤ c → a ≤ c)
#check (le_trans h h' : a ≤ c)

end

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  apply le_trans -- the two goals are to show ∃y ∈ ℝ s.t. x ≤ y ≤ z
  · apply h₀
  · apply h₁

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  apply le_trans h₀
  apply h₁

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z :=
  le_trans h₀ h₁

example (x : ℝ) : x ≤ x := by
  apply le_refl

example (x : ℝ) : x ≤ x :=
  le_refl x

#check (le_refl : ∀ a, a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
#check (lt_of_le_of_lt : a ≤ b → b < c → a < c)
#check (lt_of_lt_of_le : a < b → b ≤ c → a < c)
#check (lt_trans : a < b → b < c → a < c)

-- Try this.
example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  have h₄: a < c := by
    apply lt_of_le_of_lt h₀ h₁
  have h₅: a < d := by
    apply lt_of_lt_of_le h₄ h₂
  apply lt_trans h₅ h₃

example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  linarith

section

example (h : 2 * a ≤ 3 * b) (h' : 1 ≤ a) (h'' : d = 2) : d + a ≤ 5 * b := by
  linarith

end

example (h : 1 ≤ a) (h' : b ≤ c) : 2 + a + exp b ≤ 3 * a + exp c := by
  linarith [exp_le_exp.mpr h']

#check (exp_le_exp : exp a ≤ exp b ↔ a ≤ b)
#check (exp_lt_exp : exp a < exp b ↔ a < b)
#check (log_le_log : 0 < a → a ≤ b → log a ≤ log b)
#check (log_lt_log : 0 < a → a < b → log a < log b)
#check (add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d)
#check (add_le_add_right : a ≤ b → ∀ c, c + a ≤ c + b)
#check (add_le_add_left : a ≤ b → ∀ c, a + c ≤ b + c)
#check (add_lt_add_of_le_of_lt : a ≤ b → c < d → a + c < b + d)
#check (add_lt_add_of_lt_of_le : a < b → c ≤ d → a + c < b + d)
#check (add_lt_add_right : a < b → ∀ c, c + a < c + b)
#check (add_lt_add_left : a < b → ∀ c, a + c < b + c)
#check (add_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a + b)
#check (add_pos : 0 < a → 0 < b → 0 < a + b)
#check (add_pos_of_pos_of_nonneg : 0 < a → 0 ≤ b → 0 < a + b)
#check (exp_pos : ∀ a, 0 < exp a)
#check add_le_add_right

example (h : a ≤ b) : exp a ≤ exp b := by
  rw [exp_le_exp]
  exact h

example (h₀ : a ≤ b) (h₁ : c < d) : a + exp c + e < b + exp d + e := by
  apply add_lt_add_of_lt_of_le
  · apply add_lt_add_of_le_of_lt h₀
    apply exp_lt_exp.2 h₁
  apply le_refl

example (h₀ : d ≤ e) : c + exp (a + d) ≤ c + exp (a + e) := by
  have h₁ : a + d ≤ a + e := by
    apply add_le_add_right h₀
  have h₂ : exp (a+d) ≤ exp (a+e) := by
    apply exp_le_exp.mpr h₁
  apply add_le_add_right h₂


example : (0 : ℝ) < 1 := by
  linarith


example (h : a ≤ b) : log (1 + exp a) ≤ log (1 + exp b) := by
  have h₀ : 0 < 1 + exp a := by
    have h₁: 0 < exp a := by
      apply exp_pos
    linarith
  have h₂ : 1 + exp a ≤ 1 + exp b := by
    apply exp_le_exp.2 at h
    linarith
  apply log_le_log h₀ h₂

example : 0 ≤ a ^ 2 := by

  exact sq_nonneg a


example (h : a ≤ b) : c - exp b ≤ c - exp a := by
  apply exp_le_exp.2 at h
  linarith
  /-
  have h₁ : c ≤ c := by linarith
  have h₂ : exp a ≤ exp b := by
    apply exp_le_exp.2 h
  apply tsub_le_tsub h₁ h₂
  -/

example : 2*a*b ≤ a^2 + b^2 := by
  have h : 0 ≤ a^2 - 2*a*b + b^2
  calc
    a^2 - 2*a*b + b^2 = (a - b)^2 := by ring
    _ ≥ 0 := by apply pow_two_nonneg

  calc
    2*a*b = 2*a*b + 0 := by ring
    _ ≤ 2*a*b + (a^2 - 2*a*b + b^2) := add_le_add (le_refl _) h
    _ = a^2 + b^2 := by ring

example : 2*a*b ≤ a^2 + b^2 := by
  have h : 0 ≤ a^2 - 2*a*b + b^2
  calc
    a^2 - 2*a*b + b^2 = (a - b)^2 := by ring
    _ ≥ 0 := by apply pow_two_nonneg
  linarith

example : |a*b| ≤ (a^2 + b^2)/2 := by
  have h₁ : 0 ≤ a^2 - 2*a*b + b^2
  calc
    a^2 - 2*a*b + b^2 = (a-b)^2 := by ring
    _ ≥ 0 := by apply pow_two_nonneg
  have h₃ : a*b ≤ (a^2 + b^2)/2 := by linarith
  have h₂ : 0 ≤ a^2 + 2*a*b + b^2
  calc
    a^2 + 2*a*b + b^2 = (a+b)^2 := by ring
    _ ≥ 0 := by apply pow_two_nonneg
  have h₄ : -(a*b) ≤ (a^2 + b^2)/2 := by linarith

  apply abs_le'.mpr
  constructor
  exact h₃
  exact h₄

#check abs_le'.mpr
