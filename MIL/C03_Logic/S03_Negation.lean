import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S03

section
variable (a b : ℝ)

example (h : a < b) : ¬b < a := by
  intro h'
  have : a < a := lt_trans h h'
  apply lt_irrefl a this

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a

def FnHasLb (f : ℝ → ℝ) :=
  ∃ a, FnLb f a

variable (f : ℝ → ℝ)

example (h : ∀ a, ∃ x, f x > a) : ¬FnHasUb f := by
  intro fnub
  rcases fnub with ⟨a, fnuba⟩
  rcases h a with ⟨x, hx⟩
  have : f x ≤ a := fnuba x
  linarith

example (h : ∀ a, ∃ x, f x < a) : ¬FnHasLb f := by
  intro fnlb
  rcases fnlb with ⟨a, ha⟩
  rcases h a with ⟨b,hb⟩
  have: f b ≥  a := ha b
  have k : a < f b := by linarith
  have g : f b < f b := lt_trans hb k
  apply lt_irrefl (f b) g





example : ¬FnHasUb fun x ↦ x := by
  intro h
  rcases h with ⟨a,b⟩
  have k: (a+1) ≤  (a) := b (a+1); linarith




#check (not_le_of_gt : a > b → ¬a ≤ b)
#check (not_lt_of_ge : a ≥ b → ¬a < b)
#check (lt_of_not_ge : ¬a ≥ b → a < b)
#check (le_of_not_gt : ¬a > b → a ≤ b)

example (h : Monotone f) (h' : f a < f b) : a < b := by
  apply not_le_of_gt at h'
  apply lt_of_not_ge
  intro g
  have: f b ≤ f a := h g
  linarith


example (h : a ≤ b) (h' : f b < f a) : ¬Monotone f := by
  intro g
  have: f a ≤ f b := g h
  linarith

example : ¬∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b}, f a ≤ f b → a ≤ b := by
  intro h
  let f := fun x : ℝ ↦ (0 : ℝ)
  have monof : Monotone f := by
    intro a b aleb
    have fa: f a = 0 := by linarith
    have fb: f b = 0 := by linarith
    linarith
  have h' : f 1 ≤ f 0 := le_refl _
  have: (1:ℝ)  ≤ 0 := h monof h'
  linarith

example (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
  apply le_of_not_gt
  intro g
  have g' : x/2 < x := by linarith
  have l: x/2 > 0 := by linarith
  have k : x < x/2 := h (x/2) l
  have j: x/2 < x/2 := lt_trans g' k
  apply lt_irrefl (x/2) j


end

section
variable {α : Type*} (P : α → Prop) (Q : Prop)

example (h : ¬∃ x, P x) : ∀ x, ¬P x := by
  intro g k
  have j : ∃ x, P x := ⟨g, k⟩
  exact h j



example (h : ∀ x, ¬P x) : ¬∃ x, P x := by
  intro g
  rcases g with ⟨a, ga⟩
  have k: ¬P a := h a
  exact k ga

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra h'
  apply h
  intro x
  show P x
  by_contra h''
  exact h' ⟨x, h''⟩

example (h : ∃ x, ¬P x) : ¬∀ x, P x := by
  intro g
  rcases h with ⟨a, pa⟩
  have con: P a := g a
  exact pa con

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra h'
  apply h
  intro x
  show P x
  by_contra h''
  exact h' ⟨x, h''⟩

example (h : ¬¬Q) : Q := by
  by_contra h'
  exact h h'

example (h : Q) : ¬¬Q := by
  intro g
  exact g h

end

section
variable (f : ℝ → ℝ)

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  intro g
  by_contra h'
  apply h
  show ∃ a, FnUb f a
  have k: FnUb f g := by
    push Not at h'
    exact h'
  use g


example (h : ¬∀ a, ∃ x, f x > a) : FnHasUb f := by
  push Not at h
  exact h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  dsimp only [FnHasUb, FnUb] at h
  push Not at h
  exact h

example (h : ¬Monotone f) : ∃ x y, x ≤ y ∧ f y < f x := by
  dsimp only [Monotone] at h
  push Not at h
  exact h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  contrapose! h
  exact h

example (x : ℝ) (h : ∀ ε > 0, x ≤ ε) : x ≤ 0 := by
  contrapose! h
  use x / 2
  constructor <;> linarith

end

section
variable (a : ℕ)

example (h : 0 < 0) : a > 37 := by
  exfalso
  apply lt_irrefl 0 h

example (h : 0 < 0) : a > 37 :=
  absurd h (lt_irrefl 0)

example (h : 0 < 0) : a > 37 := by
  have h' : ¬0 < 0 := lt_irrefl 0
  contradiction

end
