import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S05

section

variable {x y : ℝ}

example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  left
  linarith [pow_two_nonneg x]

example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  --practise
  left
  have j : x ^2 ≥ 0 := pow_two_nonneg x
  linarith

example (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
  right
  linarith [pow_two_nonneg x]

example (h : y > 0) : y > 0 ∨ y < -1 :=
  Or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
  Or.inr h

example : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro h; left; exact h
  · rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  case inl h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  case inr h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  next h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  next h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  match le_or_gt 0 y with
    | Or.inl h =>
      rw [abs_of_nonneg h]
      intro h; left; exact h
    | Or.inr h =>
      rw [abs_of_neg h]
      intro h; right; exact h

namespace MyAbs

theorem le_abs_self (x : ℝ) : x ≤ |x| := by
  cases le_or_gt 0 x
  case inl h =>
    rw [abs_of_nonneg h]
  case inr h =>
    have k : |x| ≥ 0 := abs_nonneg x
    linarith

theorem neg_le_abs (x : ℝ) : -x ≤ |x| := by
  rcases le_or_gt 0 x with h | g
  · have k : -x ≤ 0 := by linarith
    have j : |x| ≥ 0 := abs_nonneg x
    linarith
  · rw [abs_of_neg g]

theorem abs_add_le (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  cases le_or_gt 0 (x+y)
  case inl h =>
    rw [abs_of_nonneg h]
    linarith [le_abs_self x, le_abs_self y]
  case inr h =>
    rw [abs_of_neg h]
    linarith [neg_le_abs x, neg_le_abs y]


theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by
  constructor
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro g
    left
    exact g
  · rw [abs_of_neg h]
    intro g;right;exact g
  intro g
  rcases g with g | g
  · have h : y ≤ |y| := le_abs_self y
    linarith
  · have h : -y ≤ |y| := neg_le_abs y
    linarith


theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
  sorry

end MyAbs

end

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  · right; exact xgt

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]
    apply dvd_mul_right
  · rw [mul_comm, mul_assoc]
    apply dvd_mul_right

example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  rcases h with ⟨x, y, rfl | rfl⟩ <;> linarith [sq_nonneg x, sq_nonneg y]

example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have h' : x ^ 2 - 1 = 0 := by rw [h, sub_self]
  have g : (x + 1) * (x - 1) = 0 := by rw [← h']; ring
  apply eq_zero_or_eq_zero_of_mul_eq_zero at g
  rcases g with j | j
  · right;linarith
  · left;linarith

example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have h' : x ^ 2 - y^2 = 0 := by rw [h, sub_self]
  have g : (x + y) * (x - y) = 0 := by rw [← h']; ring
  apply eq_zero_or_eq_zero_of_mul_eq_zero at g
  rcases g with j | j
  · right;linarith
  · left;linarith

section
variable {R : Type*} [CommRing R] [IsDomain R]
variable (x y : R)

example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have h' : x ^ 2 - 1 = 0 := by rw [h, sub_self]
  have g : (x + 1) * (x - 1) = 0 := by rw [← h']; ring
  apply eq_zero_or_eq_zero_of_mul_eq_zero at g
  rcases g with j | j
  · right
    exact eq_neg_iff_add_eq_zero.mpr j
  · left
    exact eq_of_sub_eq_zero j

example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have h' : x ^ 2 - y^2 = 0 := by rw [h, sub_self]
  have g : (x + y) * (x - y) = 0 := by rw [← h']; ring
  apply eq_zero_or_eq_zero_of_mul_eq_zero at g
  rcases g with j | j
  · right; exact eq_neg_iff_add_eq_zero.mpr j
  · left; exact eq_of_sub_eq_zero j

end

example (P : Prop) : ¬¬P → P := by
  intro h
  cases em P
  · assumption
  · contradiction

example (P : Prop) : ¬¬P → P := by
  intro h
  by_cases h' : P
  · assumption
  contradiction

example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  constructor
  by_cases h' : Q
  · intro g
    right
    assumption
  · intro g
    contrapose! g
    exact g
  · intro g h
    contrapose! g
    constructor
    assumption;assumption
