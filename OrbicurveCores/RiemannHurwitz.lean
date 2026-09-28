/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import Mathlib

/-!
# The Riemann–Hurwitz step of [CanLift] Prop. 2.7

In the proof of [CanLift] Prop. 2.7, the core `Z` of a non-arithmetic once-punctured elliptic
curve `Y` receives a map `Ȳ → Z̄^crs ≅ ℙ¹` of degree `d`, with the same ramification index `eᵢ` at
all points over the `i`-th branch point. Riemann–Hurwitz `0 = -2d + Σ (d/eᵢ)(eᵢ - 1)` gives
`Σ (1 - 1/eᵢ) = 2`, whose solutions in integers `eᵢ ≥ 2` are

  `(2,2,2,2)`, `(2,3,6)`, `(2,4,4)`, `(3,3,3)`

(`riemannHurwitz_solutions`). In the first case the core is the hemi-elliptic quotient; the
other three make `Y` a cover of an arithmetic triangle group.
-/

namespace OrbicurveCores

/-- Three branch points: `1/a + 1/b + 1/c = 1` with `2 ≤ a ≤ b ≤ c`. -/
lemma rh_three {a b c : ℕ} (ha : 2 ≤ a) (hab : a ≤ b) (hbc : b ≤ c)
    (h : (1 - 1 / (a : ℚ)) + (1 - 1 / (b : ℚ)) + (1 - 1 / (c : ℚ)) = 2) :
    (a, b, c) = (2, 3, 6) ∨ (a, b, c) = (2, 4, 4) ∨ (a, b, c) = (3, 3, 3) := by
  have hb : 2 ≤ b := ha.trans hab
  have hc : 2 ≤ c := hb.trans hbc
  have ha' : (a : ℚ) ≠ 0 := by positivity
  have hb' : (b : ℚ) ≠ 0 := by positivity
  have hc' : (c : ℚ) ≠ 0 := by positivity
  have h' : (b : ℚ) * c + a * c + a * b = a * b * c := by
    field_simp at h; linarith
  have h'' : b * c + a * c + a * b = a * b * c := by exact_mod_cast h'
  have ha3 : a ≤ 3 := by
    by_contra hh
    have : a * b * c ≥ 4 * b * c := by
      have := Nat.mul_le_mul_right (b * c) (show 4 ≤ a by lia); nlinarith
    nlinarith [Nat.mul_le_mul hab hbc, Nat.mul_le_mul_left c hab]
  have hb4 : b ≤ 4 := by
    interval_cases a <;> nlinarith
  have hc6 : c ≤ 6 := by
    interval_cases a <;> interval_cases b <;> nlinarith
  interval_cases a <;> interval_cases b <;> interval_cases c <;> simp_all

/-- The solutions of `Σ (1 - 1/eᵢ) = 2` with all `eᵢ ≥ 2`, as sorted lists. -/
theorem riemannHurwitz_solutions (l : List ℕ) (hl : l.Pairwise (· ≤ ·)) (h2 : ∀ e ∈ l, 2 ≤ e)
    (hsum : (l.map fun e : ℕ ↦ (1 - 1 / (e : ℚ))).sum = 2) :
    l = [2, 2, 2, 2] ∨ l = [2, 3, 6] ∨ l = [2, 4, 4] ∨ l = [3, 3, 3] := by
  have hterm : ∀ e ∈ l, (1 / 2 : ℚ) ≤ 1 - 1 / (e : ℚ) ∧ 1 - 1 / (e : ℚ) < 1 := by
    intro e he
    have : (2 : ℚ) ≤ e := by exact_mod_cast h2 e he
    have hpos : (0 : ℚ) < 1 / e := by positivity
    refine ⟨?_, by linarith⟩
    have : 1 / (e : ℚ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) this
    linarith
  have hge : ∀ t : List ℕ, (∀ e ∈ t, 2 ≤ e) →
      (t.length : ℚ) / 2 ≤ (t.map fun e : ℕ ↦ (1 - 1 / (e : ℚ))).sum := by
    intro t ht
    induction t with
    | nil => simp
    | cons x t ih =>
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      have hx : (2 : ℚ) ≤ x := by exact_mod_cast ht x (by simp)
      have : 1 / (x : ℚ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hx
      have := ih (fun e he ↦ ht e (by simp [he]))
      push_cast; linarith
  match l, hl, h2, hsum, hterm with
  | [], _, _, hs, _ => simp at hs
  | [a], _, _, hs, ht =>
    have := (ht a (by simp)).2
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at hs
    linarith
  | [a, b], _, _, hs, ht =>
    have := (ht a (by simp)).2; have := (ht b (by simp)).2
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at hs
    linarith
  | [a, b, c], hl, h2, hs, _ =>
    simp only [List.pairwise_cons, List.mem_cons, forall_eq_or_imp, List.not_mem_nil,
      List.Pairwise.nil] at hl
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at hs
    have := rh_three (h2 a (by simp)) hl.1.1 hl.2.1.1 (by linarith)
    rcases this with h | h | h <;> simp only [Prod.mk.injEq] at h <;>
      obtain ⟨rfl, rfl, rfl⟩ := h <;> simp
  | [a, b, c, d], _, h2, hs, ht =>
    have e : ∀ e ∈ [a, b, c, d], 1 - 1 / (e : ℚ) = 1 / 2 := by
      intro e he
      have h1 := (ht e he).1
      have hsum' : (1 - 1 / (a : ℚ)) + (1 - 1 / (b : ℚ)) + (1 - 1 / (c : ℚ)) +
          (1 - 1 / (d : ℚ)) = 2 := by simpa [add_assoc] using hs
      have := (ht a (by simp)).1; have := (ht b (by simp)).1
      have := (ht c (by simp)).1; have := (ht d (by simp)).1
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl <;> linarith
    have two : ∀ e ∈ [a, b, c, d], e = 2 := by
      intro x hx
      have h1 := e x hx
      have hx0 : (x : ℚ) ≠ 0 := by have := h2 x hx; positivity
      have : (x : ℚ) = 2 := by field_simp at h1; linarith
      exact_mod_cast this
    simp [two a (by simp), two b (by simp), two c (by simp), two d (by simp)]
  | a :: b :: c :: d :: e :: t, _, h2, hs, _ =>
    have := hge _ h2
    rw [hs] at this
    simp at this
    have : (5 : ℚ) ≤ t.length + 1 + 1 + 1 + 1 + 1 := by
      have : (0 : ℚ) ≤ t.length := by positivity
      linarith
    linarith

end OrbicurveCores
