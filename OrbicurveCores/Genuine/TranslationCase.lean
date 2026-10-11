/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.Genuine.CommIndex

/-!
# R3d: the translation case

Let `Γ = ⟨A₀, B₀⟩` be a once-punctured torus group in Fricke normal form (traces `x, y, z > 0`,
`x² + y² + z² = xyz`, triangle inequalities) which admits a core, and `Δ = Comm(Γ)`. By R3c the
translations in `Δ` are `(1/m) ℤ`. We show that `m ≥ 2` is impossible (`translationCase`).

The argument is elementary (no hyperbolic area):

* `Δ` is discrete (finite index over `Γ`), so the **sharp Shimizu lemma** (`one_le_abs_shimizu`,
  from weak Shimizu and the iteration `g ↦ g u_s g⁻¹`, which squares `c s`) gives `|c| ≥ m` for
  every element of `Δ` with lower-left entry `c ≠ 0`. The involutions `ι`, `A₀ ι`, `B₀ ι ∈ Γ⁺` have
  lower-left entries `z`, `y`, `x` and trace `0`, so `x, y, z ≥ m`. As `min (x, y, z) < 4`
  (`markov_min_lt_four`), `m ≤ 3`.
* `Γ` has no elliptic elements (an elliptic element fixes a point of `ℍ`, so it has finite order
  by proper discontinuity, and `Γ` is free); hence an element of `Γ⁺` with `|tr| < 2` has trace `0`
  (`tr_eq_zero_of_mem_nHemi`).
* Every `δ ∈ Δ` has a power `δ ^ j ∈ Γ⁺` with `1 ≤ j ≤ m` (`exists_pow_mem_nHemi`), since
  `Δ = Γ · {± u_{k/m}}` (R3c).
* For `w ∈ {x, y, z}` with `w < 2m`, the element `δ = e_w u_{1/m}` (`e_w` the involution with
  lower-left entry `w`) has trace `t = w/m ∈ (0, 2)`, and `tr δ ^ j ∈ {0} ∪ {|τ| ≥ 2}` for some
  `j ≤ m ≤ 3`. This gives `t² = 2` (`m = 2`), resp. `t ∈ {1, √2, √3}` (`m = 3`).
* Then the trace triple is `(2√2, 2√2, 4)` resp. `(3, 3, 3)` up to order (`markov_case_two`,
  `markov_case_three`), so `Γ` is one of Takeuchi's arithmetic groups and admits no core.
-/

open Matrix UpperHalfPlane Filter Topology
open Subgroup.Commensurable (commensurator)
open scoped MatrixGroups

namespace OrbicurveCores.Fuchsian

/-! ### Discreteness of the commensurator and the sharp Shimizu lemma -/

/-- If `Γ` is discrete and has finite index in its commensurator, the commensurator is discrete. -/
lemma discreteTopology_commensurator {Γ : Subgroup SL(2, ℝ)} [DiscreteTopology Γ]
    (hcore : AdmitsCore Γ) : DiscreteTopology (commensurator Γ) := by
  haveI : Γ.IsFiniteRelIndex (commensurator Γ) := ⟨hcore⟩
  exact (Subgroup.discreteTopology_iff_of_isFiniteRelIndex
    (fun _ h ↦ le_commensurator Γ h)).mp inferInstance

/-- **Sharp Shimizu lemma.** If a discrete `Δ` contains `uU s`, `s ≠ 0`, then every `g ∈ Δ` with
lower-left entry `c ≠ 0` satisfies `|c s| ≥ 1`. -/
theorem one_le_abs_shimizu {Δ : Subgroup SL(2, ℝ)} [DiscreteTopology Δ] {s : ℝ} (hs : s ≠ 0)
    (hu : SL2R.uU s ∈ Δ) {g : SL(2, ℝ)} (hg : g ∈ Δ) (hc : g 1 0 ≠ 0) : 1 ≤ |g 1 0 * s| := by
  obtain ⟨ε, hε, hb⟩ := exists_lowerLeft_bound hs hu
  by_contra hlt
  push Not at hlt
  set q := |g 1 0 * s| with hqdef
  have hq0 : 0 < q := abs_pos.mpr (mul_ne_zero hc hs)
  let G : ℕ → SL(2, ℝ) := fun n ↦ Nat.rec g (fun _ h ↦ h * SL2R.uU s * h⁻¹) n
  have hG : ∀ n, G n ∈ Δ ∧ G n 1 0 ≠ 0 ∧ |G n 1 0 * s| ≤ q ^ (n + 1) := by
    intro n
    induction n with
    | zero => exact ⟨hg, hc, by simp [G, hqdef]⟩
    | succ n ih =>
      obtain ⟨h1, h2, h3⟩ := ih
      have e : G (n + 1) = G n * SL2R.uU s * (G n)⁻¹ := rfl
      have hc' : G (n + 1) 1 0 = -s * G n 1 0 ^ 2 := by rw [e]; exact conj_uU_lowerLeft _ _
      refine ⟨by rw [e]; exact mul_mem (mul_mem h1 hu) (inv_mem h1), ?_, ?_⟩
      · rw [hc']; exact mul_ne_zero (neg_ne_zero.mpr hs) (pow_ne_zero 2 h2)
      · rw [hc']
        have e2 : |-s * G n 1 0 ^ 2 * s| = |G n 1 0 * s| * |G n 1 0 * s| := by
          rw [show -s * G n 1 0 ^ 2 * s = -((G n 1 0 * s) * (G n 1 0 * s)) by ring, abs_neg,
            abs_mul]
        have hle : |G n 1 0 * s| ≤ q := h3.trans ((pow_le_pow_of_le_one hq0.le hlt.le
          (by omega : 1 ≤ n + 1)).trans_eq (pow_one q))
        rw [e2, pow_succ]
        exact mul_le_mul h3 hle (abs_nonneg _) (pow_nonneg hq0.le _)
  have hs2 : 0 < ε * s ^ 2 := by positivity
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hs2 hlt
  obtain ⟨-, h2, h3⟩ := hG n
  have hbn := hb _ (hG n).1 h2
  have hle1 : |G n 1 0 * s| ≤ 1 := h3.trans (pow_le_one₀ hq0.le hlt.le)
  have hsq : (G n 1 0 * s) ^ 2 ≤ q ^ (n + 1) := by
    rw [← sq_abs]
    nlinarith [abs_nonneg (G n 1 0 * s)]
  have hqn : q ^ (n + 1) ≤ q ^ n := pow_le_pow_of_le_one hq0.le hlt.le (by omega)
  have : ε * s ^ 2 ≤ (G n 1 0 * s) ^ 2 := by
    rw [mul_pow]; exact mul_le_mul_of_nonneg_right hbn (sq_nonneg s)
  linarith

/-! ### Elliptic elements -/

/-- An element of a discrete subgroup with `|tr| < 2` fixes a point of `ℍ`, hence has finite
order (proper discontinuity). -/
lemma isOfFinOrder_of_abs_tr_lt {Δ : Subgroup SL(2, ℝ)} [DiscreteTopology Δ] {γ : SL(2, ℝ)}
    (hγ : γ ∈ Δ) (ht : |tr γ| < 2) : IsOfFinOrder γ := by
  set G : GL (Fin 2) ℝ := Matrix.SpecialLinearGroup.mapGL ℝ γ with hGdef
  have hdet : (G : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by simp [G]
  have hpos : 0 < G.val.det := by rw [hdet]; exact one_pos
  have hell : G.IsElliptic := by
    change (G : Matrix (Fin 2) (Fin 2) ℝ).discr < 0
    rw [Matrix.discr_fin_two, hdet]
    have htr : (G : Matrix (Fin 2) (Fin 2) ℝ).trace = tr γ := by simp [G, tr]
    rw [htr]
    obtain ⟨h1, h2⟩ := abs_lt.mp ht
    nlinarith
  set p := fixedPt G hell
  have hp : γ • p = p := (gl_smul_eq_self_iff_eq_fixedPt hpos hell).mpr rfl
  have hfin := ProperlyDiscontinuousSMul.finite_disjoint_inter_image (Γ := Δ)
    (isCompact_singleton (x := p)) (isCompact_singleton (x := p))
  by_contra hno
  have hinj := injective_pow_iff_not_isOfFinOrder.mpr hno
  have hpow : ∀ n : ℕ, (γ ^ n) • p = p := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, mul_smul, hp, ih]
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ ↦ (⟨γ ^ n, pow_mem hγ n⟩ : Δ))
    (fun a b h ↦ hinj (congrArg Subtype.val h)) (fun n ↦ ?_) hfin
  exact ⟨p, ⟨p, rfl, hpow n⟩, rfl⟩

lemma tr_mul_self' (A : SL(2, ℝ)) : tr (A * A) = tr A ^ 2 - 2 := by
  have := tr_mul_mul_self A 1
  simp only [mul_one, tr_one] at this
  rw [this]; ring

lemma tr_mul_mul_self' (A : SL(2, ℝ)) : tr (A * (A * A)) = tr A ^ 3 - 3 * tr A := by
  rw [tr_mul_mul_self, tr_mul_self']; ring

/-! ### Numerics for Markov-type triples -/

lemma markov_min_aux {x y z : ℝ} (hx : 4 ≤ x) (hy : 4 ≤ y) (hxz : x ≤ z) (hyz : y ≤ z)
    (h3 : z < x + y) (hrel : x ^ 2 + y ^ 2 + z ^ 2 = x * y * z) : False := by
  have hvieta : z * (x * y - z) = x ^ 2 + y ^ 2 := by linarith
  have h4 : 4 ≤ (x - 2) * (y - 2) := by nlinarith
  rcases le_or_gt z (x * y - z) with h | h
  · -- `z` is the smaller root
    have ha : 0 ≤ (y - z) * (y - (x * y - z)) := mul_nonneg_of_nonpos_of_nonpos (by linarith)
      (by linarith)
    have hb : 0 ≤ (x - z) * (x - (x * y - z)) := mul_nonneg_of_nonpos_of_nonpos (by linarith)
      (by linarith)
    have ha' : (x - 2) * y ^ 2 ≤ x ^ 2 := by nlinarith
    have hb' : (y - 2) * x ^ 2 ≤ y ^ 2 := by nlinarith
    have hxy : 0 < x ^ 2 * y ^ 2 := by positivity
    have : (x - 2) * (y - 2) * (x ^ 2 * y ^ 2) ≤ 1 * (x ^ 2 * y ^ 2) := by
      have hx2 : 0 ≤ x - 2 := by linarith
      have hy2 : 0 ≤ y - 2 := by linarith
      calc (x - 2) * (y - 2) * (x ^ 2 * y ^ 2) = ((x - 2) * y ^ 2) * ((y - 2) * x ^ 2) := by ring
        _ ≤ x ^ 2 * y ^ 2 := mul_le_mul ha' hb' (by positivity) (by positivity)
        _ = 1 * (x ^ 2 * y ^ 2) := by ring
    have := le_of_mul_le_mul_right this hxy
    linarith
  · nlinarith

/-- `min (x, y, z) < 4` for a Markov-type triple with the triangle inequalities. -/
lemma markov_min_lt_four {x y z : ℝ} (h1 : x < y + z) (h2 : y < x + z) (h3 : z < x + y)
    (hrel : x ^ 2 + y ^ 2 + z ^ 2 = x * y * z) : x < 4 ∨ y < 4 ∨ z < 4 := by
  by_contra h
  push Not at h
  obtain ⟨hx, hy, hz⟩ := h
  rcases le_total x z with hxz | hzx <;> rcases le_total y z with hyz | hzy <;>
    rcases le_total x y with hxy | hyx
  all_goals first
    | exact markov_min_aux hx hy hxz hyz h3 hrel
    | exact markov_min_aux hx hz hxy (by linarith) h2 (by linarith)
    | exact markov_min_aux hy hz hyx (by linarith) h1 (by linarith)

/-- `(3, b, c)` with `b, c ≥ 3` and the triangle inequality is `(3, 3, 3)`. -/
lemma markov_three {b c : ℝ} (hb : 3 ≤ b) (hc : 3 ≤ c) (h1 : b < 3 + c) (h2 : c < 3 + b)
    (hrel : 3 ^ 2 + b ^ 2 + c ^ 2 = 3 * b * c) : b = 3 ∧ c = 3 := by
  have e : (b - c) ^ 2 = 3 * (b - 3) + 3 * (c - 3) + (b - 3) * (c - 3) := by linarith
  have hp : 0 ≤ (b - 3) * (c - 3) := mul_nonneg (by linarith) (by linarith)
  have key : ∀ b c : ℝ, 3 ≤ b → 3 ≤ c → b ≤ c → c < 3 + b →
      (b - c) ^ 2 = 3 * (b - 3) + 3 * (c - 3) + (b - 3) * (c - 3) → b = 3 ∧ c = 3 := by
    intro b c hb hc h h2 e
    have hdd : (c - b) * (c - b) ≤ 3 * (c - b) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    have hp : 0 ≤ (b - 3) * (c - 3) := mul_nonneg (by linarith) (by linarith)
    have hb3 : b = 3 := by nlinarith
    subst hb3
    have : (c - 3) * (c - 3 - 3) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h' | h'
    · exact ⟨rfl, by linarith⟩
    · exact absurd h2 (by linarith)
  rcases le_total b c with h | h
  · exact key b c hb hc h h2 e
  · have := key c b hc hb h h1 (by linarith)
    exact ⟨this.2, this.1⟩

/-- `(2√2, b, c)` with `b, c ≥ 4` violates the triangle inequality. -/
lemma markov_two_aux {a b c : ℝ} (ha0 : 0 < a) (ha : a ^ 2 = 8) (hb : 4 ≤ b) (hc : 4 ≤ c)
    (hbc : b ≤ c) (h2 : c < a + b) (hrel : a ^ 2 + b ^ 2 + c ^ 2 = a * b * c) : False := by
  have ha1 : 2.828 < a := by nlinarith
  have ha2 : a < 2.829 := by nlinarith
  set d := c - b with hd
  have hd0 : 0 ≤ d := by linarith
  have e : d ^ 2 = (a - 2) * (b * c) - 8 := by rw [hd]; nlinarith
  have hbc' : 16 + 4 * d ≤ b * c := by rw [hd]; nlinarith
  have : (a - 2) * (16 + 4 * d) ≤ (a - 2) * (b * c) := mul_le_mul_of_nonneg_left hbc' (by linarith)
  nlinarith

lemma markov_case_two {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h1 : x < y + z)
    (h2 : y < x + z) (h3 : z < x + y) (hrel : x ^ 2 + y ^ 2 + z ^ 2 = x * y * z)
    (hX : 4 ≤ x ∨ x ^ 2 = 8) (hY : 4 ≤ y ∨ y ^ 2 = 8) (hZ : 4 ≤ z ∨ z ^ 2 = 8) :
    (x ^ 2 = 8 ∧ y ^ 2 = 8 ∧ z ^ 2 = 16) ∨ (y ^ 2 = 8 ∧ z ^ 2 = 8 ∧ x ^ 2 = 16) ∨
      (z ^ 2 = 8 ∧ x ^ 2 = 8 ∧ y ^ 2 = 16) := by
  -- one coordinate `2√2`, the other two `≥ 4`
  have one : ∀ a b c : ℝ, 0 < a → a ^ 2 = 8 → 4 ≤ b → 4 ≤ c → b < a + c → c < a + b →
      a ^ 2 + b ^ 2 + c ^ 2 = a * b * c → False := by
    intro a b c ha haa hb hc hb' hc' hr
    rcases le_total b c with h | h
    · exact markov_two_aux ha haa hb hc h hc' hr
    · exact markov_two_aux ha haa hc hb h hb' (by linarith)
  -- two coordinates `2√2`
  have two : ∀ a b c : ℝ, 0 < a → 0 < b → a ^ 2 = 8 → b ^ 2 = 8 →
      a ^ 2 + b ^ 2 + c ^ 2 = a * b * c → c ^ 2 = 16 := by
    intro a b c ha hb haa hbb hr
    have hab : a * b = 8 := by nlinarith [mul_pos ha hb]
    have : (c - 4) ^ 2 = 0 := by nlinarith
    have hc : c = 4 := by nlinarith
    rw [hc]; norm_num
  rcases hX with hX | hX <;> rcases hY with hY | hY <;> rcases hZ with hZ | hZ
  · rcases markov_min_lt_four h1 h2 h3 hrel with h | h | h <;> linarith
  · exact absurd (one z x y hz hZ hX hY (by linarith) (by linarith) (by linarith)) id
  · exact absurd (one y x z hy hY hX hZ (by linarith) (by linarith) (by linarith)) id
  · exact Or.inr (Or.inl ⟨hY, hZ, two y z x hy hz hY hZ (by linarith)⟩)
  · exact absurd (one x y z hx hX hY hZ h2 h3 hrel) id
  · exact Or.inr (Or.inr ⟨hZ, hX, two z x y hz hx hZ hX (by linarith)⟩)
  · exact Or.inl ⟨hX, hY, two x y z hx hy hX hY hrel⟩
  · exfalso
    have hxy : x = y := by nlinarith
    have hxz : x = z := by nlinarith
    subst hxy hxz
    nlinarith

lemma eq_three_of_lt_four {w : ℝ} (hw0 : 0 < w) (hw : w < 4)
    (h : 6 ≤ w ∨ w = 3 ∨ w ^ 2 = 18 ∨ w ^ 2 = 27) : w = 3 := by
  rcases h with h | h | h | h
  · linarith
  · exact h
  · nlinarith
  · nlinarith

lemma markov_case_three {x y z : ℝ} (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z) (h1 : x < y + z)
    (h2 : y < x + z) (h3 : z < x + y) (hrel : x ^ 2 + y ^ 2 + z ^ 2 = x * y * z)
    (hX : 6 ≤ x ∨ x = 3 ∨ x ^ 2 = 18 ∨ x ^ 2 = 27) (hY : 6 ≤ y ∨ y = 3 ∨ y ^ 2 = 18 ∨ y ^ 2 = 27)
    (hZ : 6 ≤ z ∨ z = 3 ∨ z ^ 2 = 18 ∨ z ^ 2 = 27) : x = 3 ∧ y = 3 ∧ z = 3 := by
  rcases markov_min_lt_four h1 h2 h3 hrel with h | h | h
  · have hx3 := eq_three_of_lt_four (by linarith) h hX
    subst hx3
    have := markov_three hy hz (by linarith) (by linarith) hrel
    exact ⟨rfl, this⟩
  · have hy3 := eq_three_of_lt_four (by linarith) h hY
    subst hy3
    have := markov_three hx hz (by linarith) (by linarith) (by linarith)
    exact ⟨this.1, rfl, this.2⟩
  · have hz3 := eq_three_of_lt_four (by linarith) h hZ
    subst hz3
    have := markov_three hx hy (by linarith) (by linarith) (by linarith)
    exact ⟨this.1, this.2, rfl⟩

/-- Traces of powers of an elliptic element with trace in `(0, 2)`: if `tr δ ^ j ∈ {0} ∪ {|τ| ≥ 2}`
with `1 ≤ j ≤ 3`, then `j = 2`, `tr δ = √2` or `j = 3`, `tr δ ∈ {1, √3}`. -/
lemma tr_pow_cases {δ : SL(2, ℝ)} (h0 : 0 < tr δ) (h2 : tr δ < 2) {j : ℕ} (hj : 0 < j)
    (hj3 : j ≤ 3) (h : tr (δ ^ j) = 0 ∨ 2 ≤ |tr (δ ^ j)|) :
    (j = 2 ∧ tr δ ^ 2 = 2) ∨ (j = 3 ∧ (tr δ = 1 ∨ tr δ ^ 2 = 3)) := by
  interval_cases j
  · rw [pow_one] at h
    rcases h with h | h
    · linarith
    · rw [abs_of_pos h0] at h; linarith
  · rw [pow_two, tr_mul_self'] at h
    left; refine ⟨rfl, ?_⟩
    rcases h with h | h
    · linarith
    · rcases le_abs'.mp h with h' | h' <;> nlinarith
  · rw [pow_succ, pow_two, mul_assoc, tr_mul_mul_self'] at h
    right; refine ⟨rfl, ?_⟩
    rcases h with h | h
    · right
      have : tr δ * (tr δ ^ 2 - 3) = 0 := by linarith
      rcases mul_eq_zero.mp this with h' | h'
      · linarith
      · linarith
    · left
      rcases le_abs'.mp h with h' | h'
      · have : (tr δ - 1) ^ 2 * (tr δ + 2) ≤ 0 := by nlinarith
        have h5 : (tr δ - 1) ^ 2 = 0 := by
          by_contra hne
          have := mul_pos (lt_of_le_of_ne (sq_nonneg _) (Ne.symm hne)) (by linarith : 0 < tr δ + 2)
          linarith
        nlinarith [pow_eq_zero_iff (n := 2) (a := tr δ - 1) two_ne_zero |>.mp h5]
      · nlinarith [mul_pos (sub_pos.2 h2) (by positivity : (0 : ℝ) < (tr δ + 1) ^ 2)]

lemma tr_mul_uU (g : SL(2, ℝ)) (s : ℝ) : tr (g * SL2R.uU s) = tr g + g 1 0 * s := by
  simp [tr_def, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]; ring

section normal

variable {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
  (hrel : x ^ 2 + y ^ 2 + z ^ 2 = x * y * z)

include hx hy in
/-- `Γ₀` has no elliptic elements: `|tr γ| ≥ 2` for `γ ∈ Γ₀`. -/
lemma two_le_abs_tr_of_mem {γ : SL(2, ℝ)} (hγ : γ ∈ Subgroup.closure {nA hz hrel, nB hz hrel}) :
    2 ≤ |tr γ| := by
  haveI := discreteTopology_normal hx hy hz hrel
  by_contra ht
  push Not at ht
  obtain ⟨n, hn, hpow⟩ := (isOfFinOrder_of_abs_tr_lt hγ ht).exists_pow_eq_one
  rw [← range_lift_normal] at hγ
  obtain ⟨w, rfl⟩ := hγ
  have hw : w ^ n = 1 ^ n :=
    injective_lift_normal hx hy hz hrel (by rw [map_pow, hpow, one_pow, map_one])
  have hw1 : w = 1 := IsMulTorsionFree.pow_left_injective hn.ne' hw
  rw [hw1, map_one, tr_one] at ht
  norm_num at ht

include hx hy in
/-- An element of `Γ⁺` with `|tr| < 2` has trace `0`. -/
lemma tr_eq_zero_of_mem_nHemi {γ : SL(2, ℝ)} (hγ : γ ∈ nHemi hz hrel) (ht : |tr γ| < 2) :
    tr γ = 0 := by
  set Γ := Subgroup.closure {nA hz hrel, nB hz hrel}
  have hpm : ∀ g ∈ pmGroup Γ, 2 ≤ |tr g| := by
    rintro g (h | h)
    · exact two_le_abs_tr_of_mem hx hy hz hrel h
    · have := two_le_abs_tr_of_mem hx hy hz hrel h
      rwa [tr_neg, abs_neg] at this
  rcases hγ with h | h
  · exact absurd (hpm γ h) (not_le.mpr ht)
  · set ι := nI hz
    have hconj : ∀ g ∈ Γ, ι⁻¹ * g * ι⁻¹⁻¹ ∈ Γ := fun g hg ↦ by
      rw [inv_inv]; exact nI_inv_conj_mem hz hrel hg
    have hii : ι⁻¹ * ι⁻¹ = -1 := by
      rw [nI_inv, neg_mul_neg, nI_mul_self]
    have e : γ * γ = (γ * ι) * (ι⁻¹ * (γ * ι) * ι⁻¹⁻¹) * (ι⁻¹ * ι⁻¹) := by group
    have hsq : γ * γ ∈ pmGroup Γ := by
      rw [e, hii]
      exact mul_mem (mul_mem h (conj_mem_pmGroup hconj h)) (neg_one_mem_pmGroup Γ)
    have h2 := hpm _ hsq
    rw [tr_mul_self'] at h2
    obtain ⟨ha, hb⟩ := abs_lt.mp ht
    rcases le_abs'.mp h2 with h' | h'
    · nlinarith
    · nlinarith

include hx hy in
/-- **Pigeonhole.** If the translations of `Δ = Comm(Γ₀)` are `(1/m) ℤ`, then every `δ ∈ Δ` has a
power `δ ^ j ∈ Γ⁺` with `1 ≤ j ≤ m`. -/
lemma exists_pow_mem_nHemi (h1 : x < y + z) (h2 : y < x + z) (h3 : z < x + y)
    (hcore : AdmitsCore (Subgroup.closure {nA hz hrel, nB hz hrel})) {m : ℕ} (hm : 0 < m)
    (hS : transl (commensurator (Subgroup.closure {nA hz hrel, nB hz hrel})) =
      AddSubgroup.zmultiples (1 / (m : ℝ)))
    {δ : SL(2, ℝ)} (hδ : δ ∈ commensurator (Subgroup.closure {nA hz hrel, nB hz hrel})) :
    ∃ j : ℕ, 0 < j ∧ j ≤ m ∧ δ ^ j ∈ nHemi hz hrel := by
  set Γ := Subgroup.closure {nA hz hrel, nB hz hrel}
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hZ : ∀ q : ℤ, SL2R.uU q ∈ nHemi hz hrel := by
    intro q
    have : ((q : ℝ)) = q • (1 : ℝ) := by simp [zsmul_eq_mul]
    rw [this]
    exact zsmul_mem (show (1 : ℝ) ∈ transl (nHemi hz hrel) from uU_one_mem_nHemi hz hrel) q
  have key : ∀ δ' ∈ commensurator Γ, ∃ r : Fin m,
      δ' * SL2R.uU (-((r : ℕ) : ℝ) / m) ∈ nHemi hz hrel := by
    intro δ' hδ'
    obtain ⟨γ, hγ, s, hs, hγδ⟩ := exists_mul_eq_uU hx hy hz hrel h1 h2 h3 hcore hδ'
    have hsZ : s ∈ AddSubgroup.zmultiples (1 / (m : ℝ)) := hS ▸ hs
    obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hsZ
    have hmZ : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
    have hr0 : 0 ≤ n % (m : ℤ) := Int.emod_nonneg _ hmZ
    have hrm : n % (m : ℤ) < m := Int.emod_lt_of_pos _ (by exact_mod_cast hm)
    refine ⟨⟨(n % (m : ℤ)).toNat, by omega⟩, ?_⟩
    have hcast : (((n % (m : ℤ)).toNat : ℕ) : ℝ) = ((n % (m : ℤ) : ℤ) : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hr0]
    have hdiv : n • (1 / (m : ℝ)) + -((n % (m : ℤ) : ℤ) : ℝ) / m = ((n / (m : ℤ) : ℤ) : ℝ) := by
      have := Int.emod_add_mul_ediv n m
      rw [zsmul_eq_mul]
      field_simp
      have h' : (n : ℝ) = ((n % (m : ℤ) : ℤ) : ℝ) + m * ((n / (m : ℤ) : ℤ) : ℝ) := by
        exact_mod_cast this.symm
      rw [h']; ring
    have hδ'' : δ' = γ⁻¹ * (γ * δ') := by group
    rw [hcast]
    rcases hγδ with e | e
    · rw [hδ'', e, mul_assoc, ← SL2R.uU_add, hdiv]
      exact mul_mem (inv_mem (le_nHemi hz hrel hγ)) (hZ _)
    · rw [hδ'', e, mul_assoc, neg_mul, ← SL2R.uU_add, hdiv]
      exact mul_mem (inv_mem (le_nHemi hz hrel hγ))
        (by simpa using mul_mem (neg_one_mem_nHemi hz hrel) (hZ _))
  choose f hf using fun k : Fin (m + 1) ↦ key (δ ^ (k : ℕ)) (pow_mem hδ _)
  obtain ⟨a, b, hab, hfab⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simp)
  have hmem : ∀ a b : Fin (m + 1), a < b → f a = f b → ∃ j : ℕ, 0 < j ∧ j ≤ m ∧
      δ ^ j ∈ nHemi hz hrel := by
    intro a b hlt he
    refine ⟨(b : ℕ) - a, by omega, by omega, ?_⟩
    have := mul_mem (hf b) (inv_mem (hf a))
    rw [he] at this
    have e : δ ^ (b : ℕ) * SL2R.uU (-((f b : ℕ) : ℝ) / m) *
        (δ ^ (a : ℕ) * SL2R.uU (-((f b : ℕ) : ℝ) / m))⁻¹ = δ ^ ((b : ℕ) - a) := by
      rw [_root_.mul_inv_rev, mul_assoc, mul_inv_cancel_left, ← pow_sub _ (by omega : (a : ℕ) ≤ b)]
    rwa [e] at this
  rcases lt_or_gt_of_ne hab with h | h
  · exact hmem a b h hfab
  · exact hmem b a h hfab.symm

lemma nI_entries : (nI hz) 1 0 = z ∧ tr (nI hz) = 0 := by
  constructor <;> simp [tr_def, coe_nI]

lemma nA_mul_nI_entries : (nA hz hrel * nI hz) 1 0 = y ∧ tr (nA hz hrel * nI hz) = 0 := by
  have hz0 : z ≠ 0 := hz.ne'
  constructor
  · simp [Matrix.SpecialLinearGroup.coe_mul, coe_nA, coe_nI, Matrix.mul_apply, Fin.sum_univ_two]
    field_simp
  · simp [tr_def, Matrix.SpecialLinearGroup.coe_mul, coe_nA, coe_nI, Matrix.mul_apply,
      Fin.sum_univ_two]
    field_simp
    ring

lemma nB_mul_nI_entries : (nB hz hrel * nI hz) 1 0 = x ∧ tr (nB hz hrel * nI hz) = 0 := by
  have hz0 : z ≠ 0 := hz.ne'
  constructor
  · simp [Matrix.SpecialLinearGroup.coe_mul, coe_nB, coe_nI, Matrix.mul_apply, Fin.sum_univ_two]
    field_simp
  · simp [tr_def, Matrix.SpecialLinearGroup.coe_mul, coe_nB, coe_nI, Matrix.mul_apply,
      Fin.sum_univ_two]
    field_simp
    ring

include hx hy in
/-- The normal-form groups with squared trace triples `(8, 8, 16)` (in some order) or `(9, 9, 9)`
are Takeuchi's arithmetic groups, which admit no core. -/
lemma not_admitsCore_of_sq (hT : (x ^ 2 = 8 ∧ y ^ 2 = 8 ∧ z ^ 2 = 16) ∨
      (y ^ 2 = 8 ∧ z ^ 2 = 8 ∧ x ^ 2 = 16) ∨ (z ^ 2 = 8 ∧ x ^ 2 = 8 ∧ y ^ 2 = 16) ∨
      (x ^ 2 = 9 ∧ y ^ 2 = 9 ∧ z ^ 2 = 9)) :
    ¬ AdmitsCore (Subgroup.closure {nA hz hrel, nB hz hrel}) := by
  set A := nA hz hrel
  set B := nB hz hrel
  have hA : A ∈ Subgroup.closure {A, B} := Subgroup.subset_closure (by simp)
  have hB : B ∈ Subgroup.closure {A, B} := Subgroup.subset_closure (by simp)
  have tA : tr A = x := tr_nA hz hrel
  have tB : tr B = y := tr_nB hz hrel
  have tAB : tr (A * B) = z := tr_nAnB hz hrel
  have tBA : tr (B * A) = z := by rw [tr_mul_comm]; exact tAB
  have hcomm : tr (A * B * A⁻¹ * B⁻¹) = -2 := by
    rw [tr_commutator_eq_neg_two_iff, tA, tB, tAB]; exact hrel
  have key : ∀ A' B' : SL(2, ℝ), Subgroup.closure {A', B'} = Subgroup.closure {A, B} →
      tr A' ^ 2 + tr B' ^ 2 + tr (A' * B') ^ 2 = tr A' * tr B' * tr (A' * B') →
      TakeuchiSq (tr A') (tr B') (tr (A' * B')) → ¬ AdmitsCore (Subgroup.closure {A, B}) :=
    fun A' B' hcl hr hT' ↦ not_admitsCore_of_isTakeuchiConj hcomm
      ⟨A', B', hcl, exists_conj_of_takeuchiSq ((tr_commutator_eq_neg_two_iff A' B').mpr hr) hT'⟩
  rcases hT with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · refine key A B rfl (by rw [tA, tB, tAB]; exact hrel) ?_
    rw [tA, tB, tAB]; exact Or.inr (Or.inl ⟨h1, h2, h3⟩)
  · have hcl : Subgroup.closure {B, B * A} = Subgroup.closure {A, B} := by
      apply le_antisymm
      · rw [Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
        exact ⟨hB, mul_mem hB hA⟩
      · have hB' : B ∈ Subgroup.closure {B, B * A} := Subgroup.subset_closure (by simp)
        have hBA : B * A ∈ Subgroup.closure {B, B * A} := Subgroup.subset_closure (by simp)
        rw [Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
        exact ⟨by simpa using mul_mem (inv_mem hB') hBA, hB'⟩
    have t3 : tr (B * (B * A)) = y * z - x := by rw [tr_mul_mul_self, tB, tBA, tA]
    refine key B (B * A) hcl (by rw [tB, tBA, t3]; linear_combination hrel) ?_
    rw [tB, tBA, t3]
    refine Or.inr (Or.inl ⟨h1, h2, ?_⟩)
    have hyz : y * z = 8 := by nlinarith [mul_pos hy hz]
    have hx4 : x = 4 := by nlinarith
    rw [hyz, hx4]; norm_num
  · have hcl : Subgroup.closure {A, A * B} = Subgroup.closure {A, B} := by
      apply le_antisymm
      · rw [Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
        exact ⟨hA, mul_mem hA hB⟩
      · have hA' : A ∈ Subgroup.closure {A, A * B} := Subgroup.subset_closure (by simp)
        have hAB : A * B ∈ Subgroup.closure {A, A * B} := Subgroup.subset_closure (by simp)
        rw [Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
        exact ⟨hA', by simpa using mul_mem (inv_mem hA') hAB⟩
    have t3 : tr (A * (A * B)) = x * z - y := by rw [tr_mul_mul_self, tA, tAB, tB]
    refine key A (A * B) hcl (by rw [tA, tAB, t3]; linear_combination hrel) ?_
    rw [tA, tAB, t3]
    refine Or.inr (Or.inl ⟨h2, h1, ?_⟩)
    have hxz : x * z = 8 := by nlinarith [mul_pos hx hz]
    have hy4 : y = 4 := by nlinarith
    rw [hxz, hy4]; norm_num
  · refine key A B rfl (by rw [tA, tB, tAB]; exact hrel) ?_
    rw [tA, tB, tAB]; exact Or.inl ⟨h1, h2, h3⟩

end normal

end OrbicurveCores.Fuchsian

namespace OrbicurveCores

open Fuchsian

/-- **R3d.** A normal-form once-punctured torus group whose commensurator contains a translation
`z ↦ z + 1/m₀`, `m₀ ≥ 2`, admits no core. -/
theorem translationCase : TranslationCase := by
  intro x y z hx hy hz hrel h1 h2 h3 m₀ hm₀ hmem hcore
  set Γ := Subgroup.closure {nA hz hrel, nB hz hrel}
  haveI := discreteTopology_normal hx hy hz hrel
  haveI := discreteTopology_commensurator hcore
  obtain ⟨m, hm, hS⟩ := exists_transl_commensurator hx hy hz hrel hcore
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  -- `m ≥ 2`, since `1/m₀ ∉ ℤ`
  have hm2 : 2 ≤ m := by
    by_contra hlt
    have hm1 : m = 1 := by omega
    have h' : (1 / (m₀ : ℝ)) ∈ transl (commensurator Γ) := hmem
    rw [hS, hm1] at h'
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp h'
    have hm₀R : (2 : ℝ) ≤ m₀ := by exact_mod_cast hm₀
    have hk' : (k : ℝ) = 1 / m₀ := by simpa [zsmul_eq_mul] using hk
    have hk0 : (0 : ℝ) < k := by rw [hk']; positivity
    have hk1 : (k : ℝ) < 1 := by
      rw [hk', div_lt_one (by linarith)]; linarith
    have : (0 : ℤ) < k := by exact_mod_cast hk0
    have : k < (1 : ℤ) := by exact_mod_cast hk1
    omega
  have hu : SL2R.uU (1 / m) ∈ commensurator Γ := by
    change (1 / (m : ℝ)) ∈ transl (commensurator Γ)
    rw [hS]; exact AddSubgroup.mem_zmultiples _
  have hΔ : ∀ e ∈ nHemi hz hrel, e ∈ commensurator Γ := fun e he ↦
    nHemi_le_commensurator hz hrel he
  have hAm : nA hz hrel * nI hz ∈ nHemi hz hrel :=
    mul_mem (le_nHemi hz hrel (Subgroup.subset_closure (by simp))) (nI_mem_nHemi hz hrel)
  have hBm : nB hz hrel * nI hz ∈ nHemi hz hrel :=
    mul_mem (le_nHemi hz hrel (Subgroup.subset_closure (by simp))) (nI_mem_nHemi hz hrel)
  -- Shimizu: `w ≥ m` for the lower-left entries `w` of the three involutions
  have shim : ∀ e ∈ nHemi hz hrel, ∀ w : ℝ, 0 < w → e 1 0 = w → (m : ℝ) ≤ w := by
    intro e he w hw hew
    have := one_le_abs_shimizu (one_div_pos.mpr hmR).ne' hu (hΔ e he) (by rw [hew]; exact hw.ne')
    rw [hew, abs_of_pos (by positivity), mul_one_div, le_div_iff₀ hmR, one_mul] at this
    exact this
  have hzm := shim _ (nI_mem_nHemi hz hrel) z hz (nI_entries hz).1
  have hym := shim _ hAm y hy (nA_mul_nI_entries hz hrel).1
  have hxm := shim _ hBm x hx (nB_mul_nI_entries hz hrel).1
  have hm3 : m ≤ 3 := by
    have : (m : ℝ) < 4 := by
      rcases markov_min_lt_four h1 h2 h3 hrel with h | h | h <;> linarith
    have : m < 4 := by exact_mod_cast this
    omega
  -- the elliptic elements `e_w u_{1/m}`
  have ell : ∀ e ∈ nHemi hz hrel, tr e = 0 → ∀ w : ℝ, 0 < w → e 1 0 = w → w < 2 * m →
      ∃ j : ℕ, 0 < j ∧ j ≤ m ∧
        ((j = 2 ∧ (w / m) ^ 2 = 2) ∨ (j = 3 ∧ (w / m = 1 ∨ (w / m) ^ 2 = 3))) := by
    intro e he htr w hw hew hw2
    set δ := e * SL2R.uU (1 / m)
    have hδ : δ ∈ commensurator Γ := mul_mem (hΔ e he) hu
    have htδ : tr δ = w / m := by
      rw [tr_mul_uU, htr, hew]; ring
    obtain ⟨j, hj0, hjm, hj⟩ := exists_pow_mem_nHemi hx hy hz hrel h1 h2 h3 hcore hm hS hδ
    have hcases : tr (δ ^ j) = 0 ∨ 2 ≤ |tr (δ ^ j)| := by
      by_cases hlt : |tr (δ ^ j)| < 2
      · exact Or.inl (tr_eq_zero_of_mem_nHemi hx hy hz hrel hj hlt)
      · exact Or.inr (not_lt.mp hlt)
    have h0 : 0 < tr δ := by rw [htδ]; positivity
    have h2' : tr δ < 2 := by rw [htδ, div_lt_iff₀ hmR]; linarith
    refine ⟨j, hj0, hjm, ?_⟩
    rw [← htδ]
    exact tr_pow_cases h0 h2' hj0 (hjm.trans hm3) hcases
  have eZ := ell _ (nI_mem_nHemi hz hrel) (nI_entries hz).2 z hz (nI_entries hz).1
  have eY := ell _ hAm (nA_mul_nI_entries hz hrel).2 y hy (nA_mul_nI_entries hz hrel).1
  have eX := ell _ hBm (nB_mul_nI_entries hz hrel).2 x hx (nB_mul_nI_entries hz hrel).1
  refine not_admitsCore_of_sq hx hy hz hrel ?_ hcore
  have hm23 : m = 2 ∨ m = 3 := by omega
  rcases hm23 with hm' | hm'
  · -- `m = 2`: every coordinate is `≥ 4` or `2√2`
    subst hm'
    have red : ∀ w : ℝ, 0 < w → (w < 2 * ((2 : ℕ) : ℝ) → ∃ j : ℕ, 0 < j ∧ j ≤ 2 ∧
        ((j = 2 ∧ (w / ((2 : ℕ) : ℝ)) ^ 2 = 2) ∨
          (j = 3 ∧ (w / ((2 : ℕ) : ℝ) = 1 ∨ (w / ((2 : ℕ) : ℝ)) ^ 2 = 3)))) →
        4 ≤ w ∨ w ^ 2 = 8 := by
      intro w hw h
      by_cases h4 : 4 ≤ w
      · exact Or.inl h4
      · obtain ⟨j, -, hj2, hj⟩ := h (by push_cast; linarith)
        rcases hj with ⟨-, hj⟩ | ⟨rfl, -⟩
        · right; push_cast at hj; nlinarith
        · omega
    have := markov_case_two hx hy hz h1 h2 h3 hrel (red x hx eX) (red y hy eY) (red z hz eZ)
    rcases this with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
  · -- `m = 3`: every coordinate is `≥ 6` or `3`, `3√2`, `3√3`; so `(3, 3, 3)`
    subst hm'
    have red : ∀ w : ℝ, 0 < w → (w < 2 * ((3 : ℕ) : ℝ) → ∃ j : ℕ, 0 < j ∧ j ≤ 3 ∧
        ((j = 2 ∧ (w / ((3 : ℕ) : ℝ)) ^ 2 = 2) ∨
          (j = 3 ∧ (w / ((3 : ℕ) : ℝ) = 1 ∨ (w / ((3 : ℕ) : ℝ)) ^ 2 = 3)))) →
        6 ≤ w ∨ w = 3 ∨ w ^ 2 = 18 ∨ w ^ 2 = 27 := by
      intro w hw h
      by_cases h6 : 6 ≤ w
      · exact Or.inl h6
      · obtain ⟨j, -, -, hj⟩ := h (by push_cast; linarith)
        push_cast at hj
        rcases hj with ⟨-, hj⟩ | ⟨-, hj | hj⟩
        · right; right; left; field_simp at hj; linarith
        · right; left; field_simp at hj; linarith
        · right; right; right; field_simp at hj; linarith
    push_cast at hxm hym hzm
    have := markov_case_three hxm hym hzm h1 h2 h3 hrel (red x hx eX) (red y hy eY)
      (red z hz eZ)
    obtain ⟨rfl, rfl, rfl⟩ := this
    norm_num

/-- **R3** (unconditional): a once-punctured torus group with a core has index `4` in its
commensurator, `Comm(Γ) = ⟨Γ, ι⟩`. -/
theorem commIndexFour : CommIndexFour := commIndexFour_of_translationCase translationCase

end OrbicurveCores
