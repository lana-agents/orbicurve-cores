/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.ArithTraces
import OrbicurveCores.Markov

/-!
# Takeuchi's classification of arithmetic `(1;∞)`-groups (necessity)

Let `A, B ∈ SL(2, ℝ)` with `tr [A, B] = -2`, so that `Γ = ⟨A, B⟩` is (the preimage in `SL(2, ℝ)`
of) a Fuchsian group of signature `(1;∞)`: the fundamental group of a once-punctured torus, with
the commutator going around the puncture. If `Γ` is arithmetic, then some generating pair
`(A', B')` of `Γ` (obtained from `(A, B)` by Nielsen moves) has squared trace triple

  `(tr² A', tr² B', tr² A'B') ∈ {(9,9,9), (8,8,16), (5,20,25), (6,12,18)}`,

that is, trace triple `(3,3,3)`, `(2√2,2√2,4)`, `(√5,2√5,5)` or `(√6,2√3,3√2)` up to signs.
This is the "only if" half of K. Takeuchi, *Arithmetic Fuchsian groups with signature (1;e)*,
J. Math. Soc. Japan 35 (1983), Thm. 4.1(i), for `e = ∞`. Together with Fricke's theorem that the
trace triple determines the group up to conjugacy, it gives the four arithmetic once-punctured
tori of [CanLift] Prop. 2.7 and [EstIUT] Prop. 2.1.

## Proof

* `OrbicurveCores.IsArithmeticSL.sq_tr_int`: all `tr² γ`, `γ ∈ Γ`, are integers.
* Fricke: `x² + y² + z² = xyz` for `(x, y, z) = (tr A, tr B, tr AB)`.
* Nielsen moves `(A, B) ↦ (B, A)`, `(B, (AB)⁻¹)`, `(A⁻¹, B)` generate the same group and act on
  trace triples by permutations and Vieta flips `z ↦ xy - z`.
* Descent on `x² + y² + z² ∈ ℕ` reaches a reduced triple, which is classified by
  `OrbicurveCores.Markov.reduced_classification`.

The degenerate trace triple `(0, 0, 0)` on the Fricke surface belongs to a quotient of the
quaternion group of order 8 (every element has order dividing 4). It is excluded because an
arithmetic group contains elements of infinite order (`IsArithmeticSL.exists_pow_four_ne_one`).
-/

open Matrix Matrix.SpecialLinearGroup Subgroup
open scoped MatrixGroups

namespace OrbicurveCores

/-- The trace triple `(x, y, z)` is *realised* in `Γ` if `Γ = ⟨A, B⟩` with `tr A = x`,
`tr B = y`, `tr AB = z`. -/
def Realizes (Γ : Subgroup SL(2, ℝ)) (x y z : ℝ) : Prop :=
  ∃ A B : SL(2, ℝ), Subgroup.closure {A, B} = Γ ∧ tr A = x ∧ tr B = y ∧ tr (A * B) = z

/-- The four squared trace triples of Takeuchi's arithmetic `(1;∞)`-groups. -/
def TakeuchiSq (x y z : ℝ) : Prop :=
  (x ^ 2 = 9 ∧ y ^ 2 = 9 ∧ z ^ 2 = 9) ∨ (x ^ 2 = 8 ∧ y ^ 2 = 8 ∧ z ^ 2 = 16) ∨
    (x ^ 2 = 5 ∧ y ^ 2 = 20 ∧ z ^ 2 = 25) ∨ (x ^ 2 = 6 ∧ y ^ 2 = 12 ∧ z ^ 2 = 18)

namespace Realizes

variable {Γ : Subgroup SL(2, ℝ)} {x y z : ℝ}

lemma mem {A B : SL(2, ℝ)} (h : Subgroup.closure {A, B} = Γ) : A ∈ Γ ∧ B ∈ Γ := by
  subst h
  exact ⟨subset_closure (by simp), subset_closure (by simp)⟩

/-- The Nielsen move `(A, B) ↦ (B, A)`. -/
lemma swap (h : Realizes Γ x y z) : Realizes Γ y x z := by
  obtain ⟨A, B, hcl, hx, hy, hz⟩ := h
  exact ⟨B, A, by rw [Set.pair_comm]; exact hcl, hy, hx, by rw [tr_mul_comm]; exact hz⟩

/-- The Nielsen move `(A, B) ↦ (B, (AB)⁻¹)`. -/
lemma cycle (h : Realizes Γ x y z) : Realizes Γ y z x := by
  obtain ⟨A, B, hcl, hx, hy, hz⟩ := h
  refine ⟨B, (A * B)⁻¹, ?_, hy, by rw [tr_inv, hz], ?_⟩
  · rw [← hcl]
    have hA : A ∈ Subgroup.closure {A, B} := subset_closure (by simp)
    have hB : B ∈ Subgroup.closure {A, B} := subset_closure (by simp)
    have hB' : B ∈ Subgroup.closure {B, (A * B)⁻¹} := subset_closure (by simp)
    have hAB' : (A * B)⁻¹ ∈ Subgroup.closure {B, (A * B)⁻¹} := subset_closure (by simp)
    apply le_antisymm
    · rw [closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      exact ⟨hB, inv_mem (mul_mem hA hB)⟩
    · rw [closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      refine ⟨?_, hB'⟩
      simpa [mul_assoc] using mul_mem (inv_mem hAB') (inv_mem hB')
  · rw [_root_.mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul, tr_inv, hx]

/-- The Nielsen move `(A, B) ↦ (A⁻¹, B)`: the Vieta flip `z ↦ xy - z`. -/
lemma flip (h : Realizes Γ x y z) : Realizes Γ x y (x * y - z) := by
  obtain ⟨A, B, hcl, hx, hy, hz⟩ := h
  refine ⟨A⁻¹, B, ?_, by rw [tr_inv, hx], hy, by rw [tr_inv_mul, hx, hy, hz]⟩
  rw [← hcl]
  have hA : A ∈ Subgroup.closure {A, B} := subset_closure (by simp)
  have hB : B ∈ Subgroup.closure {A, B} := subset_closure (by simp)
  have hA' : A⁻¹ ∈ Subgroup.closure {A⁻¹, B} := subset_closure (by simp)
  have hB' : B ∈ Subgroup.closure {A⁻¹, B} := subset_closure (by simp)
  apply le_antisymm
  · rw [closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨inv_mem hA, hB⟩
  · rw [closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨by simpa using inv_mem hA', hB'⟩

/-- Squared traces of a realised triple are integers if all squared traces in `Γ` are. -/
lemma sq_int (hint : ∀ γ ∈ Γ, ∃ m : ℤ, tr γ ^ 2 = m) (h : Realizes Γ x y z) :
    (∃ X : ℤ, x ^ 2 = X) ∧ (∃ Y : ℤ, y ^ 2 = Y) ∧ (∃ Z : ℤ, z ^ 2 = Z) := by
  obtain ⟨A, B, hcl, rfl, rfl, rfl⟩ := h
  obtain ⟨hA, hB⟩ := mem hcl
  exact ⟨hint A hA, hint B hB, hint _ (mul_mem hA hB)⟩

end Realizes

/-- The classification step for a sorted reduced triple. -/
private lemma takeuchiSq_of_sorted {a b c : ℝ} {X Y Z : ℤ} (ha : a ^ 2 = X) (hb : b ^ 2 = Y)
    (hc : c ^ 2 = Z) (hrel : a ^ 2 + b ^ 2 + c ^ 2 = a * b * c) (hpos : 0 < a ^ 2)
    (hab : a ^ 2 ≤ b ^ 2) (hbc : b ^ 2 ≤ c ^ 2) (hred : 2 * (a * b * c) ≤ a ^ 2 * b ^ 2) :
    TakeuchiSq a b c := by
  have hX : (0 : ℝ) < X := ha ▸ hpos
  have hXY : (X : ℝ) ≤ Y := ha ▸ hb ▸ hab
  have hYZ : (Y : ℝ) ≤ Z := hb ▸ hc ▸ hbc
  have hrel' : ((X + Y + Z : ℤ) : ℝ) ^ 2 = ((X * Y * Z : ℤ) : ℝ) := by
    push_cast
    rw [← ha, ← hb, ← hc, hrel]
    ring
  have hred' : ((2 * (X + Y + Z) : ℤ) : ℝ) ≤ ((X * Y : ℤ) : ℝ) := by
    push_cast
    rw [← ha, ← hb, ← hc, hrel]
    linarith
  have := Markov.reduced_classification (by exact_mod_cast hX) (by exact_mod_cast hXY)
    (by exact_mod_cast hYZ) (by exact_mod_cast hrel') (by exact_mod_cast hred')
  unfold Markov.IsTakeuchiTriple at this
  unfold TakeuchiSq
  rw [ha, hb, hc]
  rcases this with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;>
    subst h1 h2 h3 <;> norm_num

/-- **Nielsen descent.** In a group all of whose squared traces are integral, every realised
triple on the Fricke surface `x² + y² + z² = xyz` (other than `0`) can be moved by Nielsen moves
to one of Takeuchi's four triples. -/
theorem exists_takeuchiSq {Γ : Subgroup SL(2, ℝ)} (hint : ∀ γ ∈ Γ, ∃ m : ℤ, tr γ ^ 2 = m)
    (N : ℕ) : ∀ x y z : ℝ, Realizes Γ x y z → x ^ 2 + y ^ 2 + z ^ 2 = x * y * z →
      x ^ 2 + y ^ 2 + z ^ 2 ≤ N → 0 < x ^ 2 + y ^ 2 + z ^ 2 →
      ∃ x' y' z', Realizes Γ x' y' z' ∧ x' ^ 2 + y' ^ 2 + z' ^ 2 = x' * y' * z' ∧
        TakeuchiSq x' y' z' := by
  induction N with
  | zero =>
    intro x y z _ _ hN hpos
    push_cast at hN
    linarith
  | succ N ih =>
    intro x y z hr hrel hN hpos
    obtain ⟨⟨X, hX⟩, ⟨Y, hY⟩, ⟨Z, hZ⟩⟩ := hr.sq_int hint
    -- all coordinates are nonzero
    have hx : 0 < x ^ 2 := by
      rcases (sq_nonneg x).lt_or_eq with h | h
      · exact h
      · have hx0 : x = 0 := by nlinarith
        subst hx0
        nlinarith [sq_nonneg y, sq_nonneg z]
    have hy : 0 < y ^ 2 := by
      rcases (sq_nonneg y).lt_or_eq with h | h
      · exact h
      · have hy0 : y = 0 := by nlinarith
        subst hy0
        nlinarith [sq_nonneg x, sq_nonneg z]
    have hz : 0 < z ^ 2 := by
      rcases (sq_nonneg z).lt_or_eq with h | h
      · exact h
      · have hz0 : z = 0 := by nlinarith
        subst hz0
        nlinarith [sq_nonneg x, sq_nonneg y]
    -- a Vieta flip that decreases the sum of squares
    have descend : ∀ a b c : ℝ, Realizes Γ a b c →
        a ^ 2 + b ^ 2 + c ^ 2 = a * b * c → a ^ 2 + b ^ 2 + c ^ 2 = x ^ 2 + y ^ 2 + z ^ 2 →
        a ^ 2 * b ^ 2 < 2 * (a * b * c) →
        ∃ x' y' z', Realizes Γ x' y' z' ∧ x' ^ 2 + y' ^ 2 + z' ^ 2 = x' * y' * z' ∧
        TakeuchiSq x' y' z' := by
      intro a b c habc hrel' hsum hlt
      have hr' := habc.flip
      obtain ⟨⟨X', hX'⟩, ⟨Y', hY'⟩, ⟨Z', hZ'⟩⟩ := hr'.sq_int hint
      obtain ⟨⟨X'', hX''⟩, ⟨Y'', hY''⟩, ⟨Z'', hZ''⟩⟩ := habc.sq_int hint
      have hnew : (a * b - c) ^ 2 = a ^ 2 * b ^ 2 - 2 * (a * b * c) + c ^ 2 := by ring
      have hrel'' : a ^ 2 + b ^ 2 + (a * b - c) ^ 2 = a * b * (a * b - c) := by
        linear_combination hrel'
      have hlt' : a ^ 2 + b ^ 2 + (a * b - c) ^ 2 < a ^ 2 + b ^ 2 + c ^ 2 := by
        rw [hnew]; linarith
      -- integrality of the two sums
      have hint1 : ((X' + Y' + Z' : ℤ) : ℝ) < ((X'' + Y'' + Z'' : ℤ) : ℝ) := by
        push_cast; rw [← hX', ← hY', ← hZ', ← hX'', ← hY'', ← hZ'']; exact hlt'
      have hint1' : X' + Y' + Z' + 1 ≤ X'' + Y'' + Z'' := by exact_mod_cast hint1
      have hle : a ^ 2 + b ^ 2 + (a * b - c) ^ 2 ≤ N := by
        have h1 : ((X' + Y' + Z' + 1 : ℤ) : ℝ) ≤ ((X'' + Y'' + Z'' : ℤ) : ℝ) := by
          exact_mod_cast hint1'
        push_cast at h1
        rw [← hX', ← hY', ← hZ', ← hX'', ← hY'', ← hZ'', hsum] at h1
        push_cast at hN
        linarith
      have hpos' : 0 < a ^ 2 + b ^ 2 + (a * b - c) ^ 2 := by
        have : 0 < a ^ 2 := by
          rcases (sq_nonneg a).lt_or_eq with h | h
          · exact h
          · have ha0 : a = 0 := by nlinarith
            subst ha0
            nlinarith [sq_nonneg b, sq_nonneg c]
        positivity
      exact ih _ _ _ hr' hrel'' hle hpos'
    by_cases h1 : x ^ 2 * y ^ 2 < 2 * (x * y * z)
    · exact descend x y z hr hrel rfl h1
    by_cases h2 : y ^ 2 * z ^ 2 < 2 * (y * z * x)
    · exact descend y z x hr.cycle (by linear_combination hrel) (by ring) h2
    by_cases h3 : z ^ 2 * x ^ 2 < 2 * (z * x * y)
    · exact descend z x y hr.cycle.cycle (by linear_combination hrel) (by ring) h3
    -- reduced triple: sort and classify
    push Not at h1 h2 h3
    rcases le_total (x ^ 2) (y ^ 2) with hxy | hxy <;>
    rcases le_total (y ^ 2) (z ^ 2) with hyz | hyz <;>
    rcases le_total (x ^ 2) (z ^ 2) with hxz | hxz
    · exact ⟨x, y, z, hr, hrel, takeuchiSq_of_sorted hX hY hZ hrel hx hxy hyz h1⟩
    · exact ⟨x, y, z, hr, hrel, takeuchiSq_of_sorted hX hY hZ hrel hx hxy hyz h1⟩
    · exact ⟨x, z, y, hr.swap.cycle, by linear_combination hrel,
        takeuchiSq_of_sorted hX hZ hY (by linear_combination hrel)
        hx hxz hyz (by linarith)⟩
    · exact ⟨z, x, y, hr.cycle.cycle, by linear_combination hrel,
        takeuchiSq_of_sorted hZ hX hY
        (by linear_combination hrel) hz hxz hxy (by linarith)⟩
    · exact ⟨y, x, z, hr.swap, by linear_combination hrel,
        takeuchiSq_of_sorted hY hX hZ (by linear_combination hrel)
        hy hxy hxz (by linarith)⟩
    · exact ⟨y, z, x, hr.cycle, by linear_combination hrel,
        takeuchiSq_of_sorted hY hZ hX (by linear_combination hrel)
        hy hyz hxz (by linarith)⟩
    · exact ⟨z, y, x, hr.swap.cycle.cycle, by linear_combination hrel,
        takeuchiSq_of_sorted hZ hY hX
        (by linear_combination hrel) hz hyz hxy (by linarith)⟩
    · exact ⟨z, y, x, hr.swap.cycle.cycle, by linear_combination hrel,
        takeuchiSq_of_sorted hZ hY hX
        (by linear_combination hrel) hz hyz hxy (by linarith)⟩

lemma sq_eq_neg_one_of_tr_eq_zero {A : SL(2, ℝ)} (h : tr A = 0) : A * A = -1 := by
  ext1
  rw [Matrix.SpecialLinearGroup.coe_mul, sq_eq, h, zero_smul, zero_sub,
    Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one]

/-- If `tr A = tr B = tr AB = 0`, every element of `⟨A, B⟩` has order dividing `4`
(`⟨A, B⟩` is a quotient of the quaternion group). -/
lemma pow_four_eq_one_of_tr_zero {A B : SL(2, ℝ)} (hA : tr A = 0) (hB : tr B = 0)
    (hAB : tr (A * B) = 0) {γ : SL(2, ℝ)} (hγ : γ ∈ Subgroup.closure {A, B}) : γ ^ 4 = 1 := by
  have hAA := sq_eq_neg_one_of_tr_eq_zero hA
  have hBB := sq_eq_neg_one_of_tr_eq_zero hB
  have hABAB := sq_eq_neg_one_of_tr_eq_zero hAB
  have h1 : A⁻¹ = -A := by
    rw [inv_eq_of_mul_eq_one_right]; rw [mul_neg, hAA, neg_neg]
  have h2 : B⁻¹ = -B := by
    rw [inv_eq_of_mul_eq_one_right]; rw [mul_neg, hBB, neg_neg]
  have hBA : B * A = -(A * B) := by
    have h3 : B * A * B = A := by
      have : A * (B * A * B) = -1 := by simpa [mul_assoc] using hABAB
      calc B * A * B = A⁻¹ * (A * (B * A * B)) := by group
        _ = A := by rw [this, h1]; simp
    calc B * A = B * A * B * B⁻¹ := by group
      _ = -(A * B) := by rw [h3, h2, mul_neg]
  have hBAX : ∀ X : SL(2, ℝ), B * (A * X) = -(A * (B * X)) := by
    intro X; rw [← mul_assoc, hBA, neg_mul, mul_assoc]
  have hAAX : ∀ X : SL(2, ℝ), A * (A * X) = -X := by
    intro X; rw [← mul_assoc, hAA, neg_one_mul]
  have hBBX : ∀ X : SL(2, ℝ), B * (B * X) = -X := by
    intro X; rw [← mul_assoc, hBB, neg_one_mul]
  let Q : Set SL(2, ℝ) := {1, -1, A, -A, B, -B, A * B, -(A * B)}
  have hQ : ∀ x ∈ Q, x ^ 4 = 1 := by
    intro x hx
    simp only [Q, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [pow_succ, mul_assoc, hBAX, hAA, hBB]
  apply hQ
  induction hγ using Subgroup.closure_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl <;> simp [Q]
  | one => simp [Q]
  | mul x y _ _ hx hy =>
    simp only [Q, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy ⊢
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [mul_assoc, hAAX, hBAX, hAA, hBB, hBA]
  | inv x _ hx =>
    simp only [Q, Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [h1, h2, hBA]

/-- An arithmetic subgroup of `SL(2, ℝ)` contains an element of infinite order (a conjugate of a
power of `T = [[1, 1], [0, 1]]`), in particular one with `γ⁴ ≠ 1`. -/
lemma IsArithmeticSL.exists_pow_four_ne_one {Γ : Subgroup SL(2, ℝ)} (hΓ : IsArithmeticSL Γ) :
    ∃ γ ∈ Γ, γ ^ 4 ≠ 1 := by
  obtain ⟨g, hΓ'⟩ := hΓ
  obtain ⟨n, hn, -, hmem⟩ := exists_pow_mem_of_relIndex_ne_zero hΓ'.is_commensurable.1
    (⟨ModularGroup.T, rfl⟩ : mapGL ℝ ModularGroup.T ∈ 𝒮ℒ)
  have h := (Subgroup.mem_inf.mp hmem).1
  rw [mem_pointwise_smul_iff_inv_smul_mem] at h
  simp only [← ConjAct.toConjAct_inv, ConjAct.toConjAct_smul, inv_inv] at h
  obtain ⟨γ, hγ, hγeq⟩ := Subgroup.mem_map.mp h
  refine ⟨γ, hγ, fun h4 ↦ ?_⟩
  have e : g⁻¹ * (mapGL ℝ ModularGroup.T) ^ (4 * n) * g = 1 := by
    have : toGL (γ ^ 4) = 1 := by rw [h4, map_one]
    have hc : ∀ (x : GL (Fin 2) ℝ) (k : ℕ), (g⁻¹ * x * g) ^ k = g⁻¹ * x ^ k * g := by
      intro x k
      simpa using conj_pow (a := g⁻¹) (b := x) (i := k)
    rw [map_pow, hγeq, hc, ← pow_mul, mul_comm n 4] at this
    exact this
  have e2 : (mapGL ℝ ModularGroup.T) ^ (4 * n) = 1 := by
    have := congrArg (fun x ↦ g * x * g⁻¹) e
    simpa [mul_assoc] using this
  have e3 := congrArg (fun x : GL (Fin 2) ℝ ↦ (x : Matrix (Fin 2) (Fin 2) ℝ) 0 1) e2
  rw [← map_pow] at e3
  simp only [mapGL_T_pow, Units.val_one] at e3
  simp at e3
  lia

/-- **Takeuchi's diophantine reduction.** A `(1;∞)`-group `⟨A, B⟩` with `tr A ≠ 0` all of whose
squared traces are integers has a Nielsen-equivalent generating pair (again with
`tr [A', B'] = -2`) whose squared trace triple is `(9,9,9)`, `(8,8,16)`, `(5,20,25)` or
`(6,12,18)`. -/
theorem takeuchi_one_infty_of_int {A B : SL(2, ℝ)} (hcomm : tr (A * B * A⁻¹ * B⁻¹) = -2)
    (hA : tr A ≠ 0) (hint : ∀ γ ∈ Subgroup.closure {A, B}, ∃ m : ℤ, tr γ ^ 2 = m) :
    ∃ A' B' : SL(2, ℝ), Subgroup.closure {A', B'} = Subgroup.closure {A, B} ∧
      tr (A' * B' * A'⁻¹ * B'⁻¹) = -2 ∧ TakeuchiSq (tr A') (tr B') (tr (A' * B')) := by
  have hrel := (tr_commutator_eq_neg_two_iff A B).mp hcomm
  have hr : Realizes (Subgroup.closure {A, B}) (tr A) (tr B) (tr (A * B)) :=
    ⟨A, B, rfl, rfl, rfl, rfl⟩
  obtain ⟨N, hN⟩ := exists_nat_ge (tr A ^ 2 + tr B ^ 2 + tr (A * B) ^ 2)
  have hpos : 0 < tr A ^ 2 + tr B ^ 2 + tr (A * B) ^ 2 := by positivity
  obtain ⟨x, y, z, ⟨A', B', hcl, rfl, rfl, rfl⟩, hrel', hT⟩ :=
    exists_takeuchiSq hint N _ _ _ hr hrel hN hpos
  exact ⟨A', B', hcl, (tr_commutator_eq_neg_two_iff A' B').mpr hrel', hT⟩

/-- **Takeuchi's theorem for `(1;∞)`-groups (necessity).** Let `A, B ∈ SL(2, ℝ)` with
parabolic commutator, `tr [A, B] = -2`. If `⟨A, B⟩` is arithmetic (conjugate to a group
commensurable with `SL(2, ℤ)`), then `⟨A, B⟩ = ⟨A', B'⟩` for a Nielsen-equivalent pair (again
with `tr [A', B'] = -2`) whose squared trace triple is `(9,9,9)`, `(8,8,16)`, `(5,20,25)` or
`(6,12,18)`. -/
theorem takeuchi_one_infty {A B : SL(2, ℝ)} (hcomm : tr (A * B * A⁻¹ * B⁻¹) = -2)
    (harith : IsArithmeticSL (Subgroup.closure {A, B})) :
    ∃ A' B' : SL(2, ℝ), Subgroup.closure {A', B'} = Subgroup.closure {A, B} ∧
      tr (A' * B' * A'⁻¹ * B'⁻¹) = -2 ∧ TakeuchiSq (tr A') (tr B') (tr (A' * B')) := by
  have hint : ∀ γ ∈ Subgroup.closure {A, B}, ∃ m : ℤ, tr γ ^ 2 = m :=
    fun γ hγ ↦ harith.sq_tr_int hγ
  have hrel := (tr_commutator_eq_neg_two_iff A B).mp hcomm
  -- the degenerate triple `(0, 0, 0)` gives a quotient of the quaternion group, not arithmetic
  have hA : tr A ≠ 0 := by
    intro h0
    rw [h0] at hrel
    have hy : tr B = 0 := by nlinarith [sq_nonneg (tr B), sq_nonneg (tr (A * B))]
    have hz : tr (A * B) = 0 := by nlinarith [sq_nonneg (tr B), sq_nonneg (tr (A * B))]
    obtain ⟨γ, hγ, h4⟩ := harith.exists_pow_four_ne_one
    exact h4 (pow_four_eq_one_of_tr_zero h0 hy hz hγ)
  exact takeuchi_one_infty_of_int hcomm hA hint

end OrbicurveCores
