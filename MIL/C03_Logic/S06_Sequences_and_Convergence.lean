import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S06

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

example : (fun x y : ℝ ↦ (x + y) ^ 2) = fun x y : ℝ ↦ x ^ 2 + 2 * x * y + y ^ 2 := by
  ext a b
  ring

example (a b : ℝ) : |a| = |a - b + b| := by
  congr
  ring

example {a : ℝ} (h : 1 < a) : a < a * a := by
  convert (mul_lt_mul_iff_left₀ _).2 h
  · rw [one_mul]
  exact lt_trans zero_lt_one h

theorem convergesTo_const (a : ℝ) : ConvergesTo (fun _x : ℕ ↦ a) a := by
  intro ε εpos
  use 0
  intro n nge
  rw [sub_self, abs_zero]
  apply εpos

theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  intro ε εpos
  dsimp -- this line is not needed but cleans up the goal a bit.
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  have ksa : ∀ n ≥ max Ns Nt, |s n - a| < ε / 2 := by
    intro k kl
    have ks : k ≥ Ns := le_of_max_le_left kl
    apply hs k
    exact ks
  have ksb : ∀ n ≥ max Ns Nt, |t n - b| < ε / 2 := by
    intro k kl
    have ks : k ≥ Nt := le_of_max_le_right kl
    apply ht k
    exact ks
  intro g gl
  have kag : |s g - a| < ε / 2 := ksa g gl
  have kbg : |t g - b| < ε / 2 := ksb g gl
  have sum: |s g - a| + |t g - b| < ε := by linarith
  have tri: |(s g - a) + (t g - b)| ≤  |s g - a| + |t g - b| := by exact abs_add_le (s g - a) (t g - b)
  have fin₀ : |s g - a + (t g - b)| < ε := by linarith
  have fin₁: |s g + t g - (a+b)| = |s g - a + (t g - b)| := by congr;linarith
  rw [fin₁]
  congr


theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  · convert convergesTo_const 0
    · rw [h]
      ring
    rw [h]
    ring
  have acpos : 0 < |c| := abs_pos.mpr h
  rw [ConvergesTo];rw [ConvergesTo] at cs
  intro g gl
  have gc : (g / |c|) > 0 := div_pos gl acpos
  have ks : ∃ N, ∀ n ≥ N, |s n - a| < g / |c| := cs (g / |c|) gc
  rcases ks with ⟨m, ml⟩
  use m
  intro b j
  have pr : |s b - a| < g / |c| := ml b j
  rw [lt_div_iff₀' acpos] at pr
  rw [← abs_mul] at pr
  rw [mul_sub] at pr
  exact pr

theorem exists_abs_le_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, h⟩
  use N, |a| + 1
  intro g k
  have j : |s g - a| < 1 := h g k
  have m :|s g| - |a| ≤ |s g - a| := abs_sub_abs_le_abs_sub (s g) a
  linarith

theorem aux {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  rcases ct _ pos₀ with ⟨N₁, h₁⟩
  use (max N₁ N₀)
  intro g l
  have tg : |t g| < ε / B := by simpa using h₁ g (le_of_max_le_left l)
  norm_num
  rw [← mul_div_cancel₀ ε (ne_of_gt Bpos)]
  exact mul_lt_mul'' (h₀ g (le_of_max_le_right l)) tg (abs_nonneg (s g)) (abs_nonneg (t g))



theorem convergesTo_mul {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n * t n) (a * b) := by
  have h₁ : ConvergesTo (fun n ↦ s n * (t n + -b)) 0 := by
    apply aux cs
    convert convergesTo_add ct (convergesTo_const (-b))
    ring
  have := convergesTo_add h₁ (convergesTo_mul_const b cs)
  convert convergesTo_add h₁ (convergesTo_mul_const b cs) using 1
  · ext; ring
  ring

theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
  by_contra abne
  have : |a - b| > 0 := by

    have ambnz : a - b ≠ 0 := by
      by_contra
      have aeqb : a=b := by linarith
      contradiction
    have mod_n : |a-b| ≥ 0 := abs_nonneg (a-b)
    rcases eq_or_lt_of_le mod_n with h | h
    · have k : a-b=0 := abs_eq_zero.mp (Eq.symm h)
      contradiction
    · exact h
  let ε := |a - b| / 2
  have εpos : ε > 0 := by
    change |a - b| / 2 > 0
    linarith
  rcases sa ε εpos with ⟨Na, hNa⟩
  rcases sb ε εpos with ⟨Nb, hNb⟩
  let N := max Na Nb
  have absa : |s N - a| < ε := hNa N (le_of_max_le_left (le_refl N))
  have absb : |s N - b| < ε := hNb N (le_of_max_le_right (le_refl N))
  have : |a - b| < |a - b| := by
    change |s N - a| < |a - b| / 2 at absa
    change |s N - b| < |a - b| / 2 at absb
    have k : |s N - a| + |s N - b| < |a-b| := by
      linarith
    rw [← abs_neg (s N - a)] at k
    simp at k
    have j : |a - s N + (s N - b)| ≤ |a - s N| + |s N - b|:= abs_add_le (a - s N) (s N - b)
    simp at j
    linarith
  exact lt_irrefl _ this

section
variable {α : Type*} [LinearOrder α]

def ConvergesTo' (s : α → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

end
