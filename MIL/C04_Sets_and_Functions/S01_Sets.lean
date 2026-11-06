import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Prime.Basic
import MIL.Common

section
variable {α : Type*}
variable (s t u : Set α)
open Set

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  rw [subset_def, inter_def, inter_def]
  rw [subset_def] at h
  simp only [mem_setOf]
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  simp only [subset_def, mem_inter_iff] at *
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  intro x xsu
  exact ⟨h xsu.1, xsu.2⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
  fun _x ⟨xs, xu⟩ ↦ ⟨h xs, xu⟩

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  intro x hx
  have xs : x ∈ s := hx.1
  have xtu : x ∈ t ∪ u := hx.2
  rcases xtu with xt | xu
  · left
    show x ∈ s ∩ t
    exact ⟨xs, xt⟩
  · right
    show x ∈ s ∩ u
    exact ⟨xs, xu⟩

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  rintro x ⟨xs, xt | xu⟩
  · left; exact ⟨xs, xt⟩
  · right; exact ⟨xs, xu⟩

example : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  rintro x (⟨xs,ts⟩ | ⟨ys,zs⟩)
  exact ⟨xs,mem_union_left u ts⟩
  exact ⟨ys,mem_union_right t zs⟩



example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  intro x xstu
  have xs : x ∈ s := xstu.1.1
  have xnt : x ∉ t := xstu.1.2
  have xnu : x ∉ u := xstu.2
  constructor
  · exact xs
  intro xtu
  -- x ∈ t ∨ x ∈ u
  rcases xtu with xt | xu
  · show False; exact xnt xt
  · show False; exact xnu xu

example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  rintro x ⟨⟨xs, xnt⟩, xnu⟩
  use xs
  rintro (xt | xu) <;> contradiction

example : s \ (t ∪ u) ⊆ (s \ t) \ u := by
  rintro x ⟨xs, xn⟩
  simp
  constructor
  constructor
  exact xs
  contrapose! xn
  exact mem_union_left u xn
  contrapose! xn
  exact mem_union_right t xn
example : s ∩ t = t ∩ s := by
  ext x
  simp only [mem_inter_iff]
  constructor
  · rintro ⟨xs, xt⟩; exact ⟨xt, xs⟩
  · rintro ⟨xt, xs⟩; exact ⟨xs, xt⟩

example : s ∩ t = t ∩ s :=
  Set.ext fun _x ↦ ⟨fun ⟨xs, xt⟩ ↦ ⟨xt, xs⟩, fun ⟨xt, xs⟩ ↦ ⟨xs, xt⟩⟩

example : s ∩ t = t ∩ s := by ext x; simp [and_comm]

example : s ∩ t = t ∩ s := by
  apply Subset.antisymm
  · rintro x ⟨xs, xt⟩; exact ⟨xt, xs⟩
  · rintro x ⟨xt, xs⟩; exact ⟨xs, xt⟩

example : s ∩ t = t ∩ s :=
  Subset.antisymm (fun _x ⟨xs, xt⟩ ↦ ⟨xt, xs⟩) (fun _x ⟨xt, xs⟩ ↦ ⟨xs, xt⟩)
example : s ∩ (s ∪ t) = s := by
  ext x
  simp only [mem_inter_iff]
  constructor
  · rintro ⟨xs,xt⟩
    exact xs
  · intro g
    constructor; exact g
    exact mem_union_left t g



example : s ∪ s ∩ t = s := by
  ext x
  constructor
  · intro g
    rcases g with xs | xt; exact xs
    simp only [mem_inter_iff] at xt
    exact xt.1
  · intro g
    simp only [mem_union]
    exact Or.symm (Or.inr g)


  --simp only [mem_inter_iff]

example : s \ t ∪ t = s ∪ t := by
  ext x
  constructor
  · intro g
    rcases g with xst | xt
    · have xs : x ∈ s := xst.1
      exact mem_union_left t xs
    · exact mem_union_right s xt
  · intro g
    rcases g with xs | xt
    · by_cases h : x ∈ t
      · exact mem_union_right (s \ t) h
      · have xst : x ∈ s \ t := mem_diff_of_mem xs h
        exact mem_union_left t xst
    · exact mem_union_right (s \ t ) xt




example : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
  ext x
  constructor
  · intro g
    rcases g with xst | xts
    · have xs : x ∈ s := xst.1
      have xnt : x ∉ t := xst.2
      constructor
      · exact mem_union_left t xs
      · intro h
        exact xnt h.2
    · have xt : x ∈ t := xts.1
      have xns : x ∉ s := xts.2
      constructor
      · exact mem_union_right s xt
      · intro h
        exact xns h.1
  · intro g
    rcases g with ⟨xst, xnst⟩
    rcases xst with xs | xt
    · have xnt : x ∉ t := by
        intro xt
        exact xnst ⟨xs, xt⟩
      have xst : x ∈ s \ t := mem_diff_of_mem xs xnt
      exact mem_union_left (t \ s) xst
    · have xns : x ∉ s := by
        intro xs
        exact xnst ⟨xs, xt⟩
      have xts : x ∈ t \ s := mem_diff_of_mem xt xns
      exact mem_union_right (s \ t) xts

def evens : Set ℕ :=
  { n | Even n }

def odds : Set ℕ :=
  { n | ¬Even n }

example : evens ∪ odds = univ := by
  rw [evens, odds]
  ext n
  simp [-Nat.not_even_iff_odd]
  apply Classical.em

example (x : ℕ) (h : x ∈ (∅ : Set ℕ)) : False :=
  h

example (x : ℕ) : x ∈ (univ : Set ℕ) :=
  trivial

example : { n | Nat.Prime n } ∩ { n | n > 2 } ⊆ { n | ¬Even n } := by
  intro n g
  simp at g
  have ⟨np, n2⟩ := g
  rcases Nat.Prime.eq_two_or_odd np with ntwo | nodd
  · contrapose! ntwo
    exact Ne.symm (Nat.ne_of_lt n2)
  · exact Nat.not_even_iff.mpr nodd

#print Prime

#print Nat.Prime

example (n : ℕ) : Prime n ↔ Nat.Prime n :=
  Nat.prime_iff.symm

example (n : ℕ) (h : Prime n) : Nat.Prime n := by
  rw [Nat.prime_iff]
  exact h

example (n : ℕ) (h : Prime n) : Nat.Prime n := by
  rwa [Nat.prime_iff]

end

section

variable (s t : Set ℕ)

example (h₀ : ∀ x ∈ s, ¬Even x) (h₁ : ∀ x ∈ s, Prime x) : ∀ x ∈ s, ¬Even x ∧ Prime x := by
  intro x xs
  constructor
  · apply h₀ x xs
  apply h₁ x xs

example (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ s, Prime x := by
  rcases h with ⟨x, xs, _, prime_x⟩
  use x, xs

section
variable (ssubt : s ⊆ t)

example (h₀ : ∀ x ∈ t, ¬Even x) (h₁ : ∀ x ∈ t, Prime x) : ∀ x ∈ s, ¬Even x ∧ Prime x := by
  intro x xs
  have xt : x∈ t := ssubt xs
  constructor
  · apply h₀ x xt
  apply h₁ x xt

example (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ t, Prime x := by
  rcases h with ⟨x,xs,_,px⟩
  use x, ssubt xs

end

end

section
variable {α I : Type*}
variable (A B : I → Set α)
variable (s : Set α)

open Set

example : (s ∩ ⋃ i, A i) = ⋃ i, A i ∩ s := by
  ext x
  simp only [mem_inter_iff, mem_iUnion]
  constructor
  · rintro ⟨xs, ⟨i, xAi⟩⟩
    exact ⟨i, xAi, xs⟩
  rintro ⟨i, xAi, xs⟩
  exact ⟨xs, ⟨i, xAi⟩⟩

example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ ⋂ i, B i := by
  ext x
  simp only [mem_inter_iff, mem_iInter]
  constructor
  · intro h
    constructor
    · intro i
      exact (h i).1
    intro i
    exact (h i).2
  rintro ⟨h1, h2⟩ i
  constructor
  · exact h1 i
  exact h2 i


example : (s ∪ ⋂ i, A i) = ⋂ i, A i ∪ s := by
  ext x
  simp only [mem_iInter, mem_union]
  constructor
  · intro h
    · intro y
      by_cases g : x∈ s
      · exact Or.inr g
      have k : ∀ (i : I), x ∈ A i := Or.resolve_left h g
      exact Or.inl (k y)
  · intro g
    by_cases h : x ∈ s
    exact Or.inl h
    right
    intro i
    exact Or.resolve_right (g i) h


def primes : Set ℕ :=
  { x | Nat.Prime x }

example : (⋃ p ∈ primes, { x | p ^ 2 ∣ x }) = { x | ∃ p ∈ primes, p ^ 2 ∣ x } :=by
  ext
  rw [mem_iUnion₂]
  simp

example : (⋃ p ∈ primes, { x | p ^ 2 ∣ x }) = { x | ∃ p ∈ primes, p ^ 2 ∣ x } := by
  ext
  simp

example : (⋂ p ∈ primes, { x | ¬p ∣ x }) ⊆ { x | x = 1 } := by
  intro x
  contrapose!
  simp
  apply Nat.exists_prime_and_dvd

example : (⋃ p ∈ primes, { x | x ≤ p }) = univ := by
  apply eq_univ_of_forall
  intro x
  simp [primes]
  obtain ⟨p, hxp, hp⟩ := Nat.exists_infinite_primes x
  exact ⟨p, hp, hxp⟩

end

section

open Set

variable {α : Type*} (s : Set (Set α))

example : ⋃₀ s = ⋃ t ∈ s, t := by
  ext x
  rw [mem_iUnion₂]
  simp

example : ⋂₀ s = ⋂ t ∈ s, t := by
  ext x
  rw [mem_iInter₂]
  rfl

end
