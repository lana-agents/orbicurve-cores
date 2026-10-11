/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import OrbicurveCores.Genuine.Involution
import OrbicurveCores.M2.GoodLattice

/-!
# R3b: the cusp structure of a once-punctured torus group

Let `Γ ⊆ SL(2, ℝ)` be discrete and contain a translation `uU l = [[1, l], [0, 1]]`, `l ≠ 0`.

* `transl H`: the additive group `{s | uU s ∈ H}` of translations of a subgroup `H`;
* `exists_transl_bound`: the translations of a discrete group are bounded away from `0`;
* `exists_lowerLeft_bound` (**weak Shimizu**): the nonzero lower-left entries `c` of elements of
  `Γ` satisfy `c² ≥ ε` for some `ε > 0` (from the bottom-row bound `exists_bottom_row_bound`,
  after translating the bottom row `(c, d)` to `(c, d + k l c)` with `|d + k l c| ≤ |l c|`);
* `lowerRight_eq_one_or_neg_one`: an upper triangular element of `Γ` has diagonal `±1`.

For the Fricke normal form group `Γ₀ = ⟨A₀, B₀⟩` (with the triangle inequalities):

* `exists_mem_lowerLeft_eq_zero` (**one cusp**): if `g uU t g⁻¹ ∈ Γ₀` with `t ≠ 0`, then
  `γ g` fixes `∞` for some `γ ∈ Γ₀`. Push the points `g (i n)` into the fundamental strip with
  `γₙ ∈ Γ₀`; for `h = γₙ g` the height bound `Im (h (i n)) ≥ η` forces `c_h² ≤ 1 / (η n)`, while
  `h uU t h⁻¹ ∈ Γ₀` has lower-left entry `-t c_h²`, so weak Shimizu gives `c_h = 0` for large `n`.
-/

open Matrix UpperHalfPlane Filter Topology
open scoped MatrixGroups

namespace OrbicurveCores.Fuchsian

/-! ### Translations -/

lemma uU_neg (s : ℝ) : SL2R.uU (-s) = (SL2R.uU s)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← SL2R.uU_add, neg_add_cancel, SL2R.uU_zero])

lemma uU_pow_eq (t : ℝ) (n : ℕ) : SL2R.uU t ^ n = SL2R.uU (n * t) := by
  induction n with
  | zero => simp [SL2R.uU_zero]
  | succ n ih => rw [pow_succ, ih, ← SL2R.uU_add]; push_cast; ring_nf

/-- The additive group of translations `{s | uU s ∈ H}` of a subgroup `H ≤ SL(2, ℝ)`. -/
def transl (H : Subgroup SL(2, ℝ)) : AddSubgroup ℝ where
  carrier := {s | SL2R.uU s ∈ H}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, SL2R.uU_add]; exact mul_mem ha hb
  zero_mem' := by simp [SL2R.uU_zero]
  neg_mem' {s} hs := by
    simp only [Set.mem_setOf_eq, uU_neg]; exact inv_mem hs

lemma mem_transl {H : Subgroup SL(2, ℝ)} {s : ℝ} : s ∈ transl H ↔ SL2R.uU s ∈ H := Iff.rfl

lemma transl_mono {H K : Subgroup SL(2, ℝ)} (h : H ≤ K) : transl H ≤ transl K :=
  fun _ hs ↦ h hs

lemma uU_injective {s t : ℝ} (h : SL2R.uU s = SL2R.uU t) : s = t := by
  simpa using congrArg (fun g : SL(2, ℝ) ↦ g 0 1) h

/-- The translations of a discrete subgroup are bounded away from `0`. -/
lemma exists_transl_bound (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ] :
    ∃ ε > 0, ∀ s, SL2R.uU s ∈ Γ → |s| < ε → s = 0 := by
  obtain ⟨U, hU, h⟩ := exists_nhds_of_discrete Γ
  have hpre : SL2R.uU ⁻¹' U ∈ 𝓝 (0 : ℝ) :=
    SL2R.continuous_uU.continuousAt.preimage_mem_nhds (by rwa [SL2R.uU_zero])
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hpre
  refine ⟨ε, hε, fun s hs hsε ↦ ?_⟩
  have h1 := h _ hs (hball (by simpa [Real.dist_eq] using hsε))
  rw [← SL2R.uU_zero] at h1
  exact uU_injective h1

/-! ### Weak Shimizu -/

/-- **Weak Shimizu lemma.** If a discrete `Γ` contains a translation `uU l`, `l ≠ 0`, then the
nonzero lower-left entries of elements of `Γ` are bounded away from `0`. -/
theorem exists_lowerLeft_bound {Γ : Subgroup SL(2, ℝ)} [DiscreteTopology Γ] {l : ℝ} (hl : l ≠ 0)
    (hlΓ : SL2R.uU l ∈ Γ) : ∃ ε > 0, ∀ q ∈ Γ, q 1 0 ≠ 0 → ε ≤ q 1 0 ^ 2 := by
  obtain ⟨δ, hδ, hb⟩ := M2.exists_bottom_row_bound hlΓ hl (SL2R.coe_uU l)
  refine ⟨δ / (1 + l ^ 2), by positivity, fun q hq hc ↦ ?_⟩
  set c := q 1 0 with hcdef
  set d := q 1 1 with hddef
  set r : ℝ := -d / (c * l)
  set k : ℤ := ⌊r⌋
  have hk : SL2R.uU (k * l) ∈ Γ := by
    have : ((k : ℝ) * l) = k • l := by simp [zsmul_eq_mul]
    rw [this]; exact zsmul_mem (show l ∈ transl Γ from hlΓ) k
  have hbd := hb _ (mul_mem hq hk)
  have e10 : (q * SL2R.uU (k * l)) 1 0 = c := by
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hcdef]
  have e11 : (q * SL2R.uU (k * l)) 1 1 = c * (k * l) + d := by
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hcdef, hddef]
  rw [e10, e11] at hbd
  have hfl := Int.floor_le r
  have hfl2 := Int.lt_floor_add_one r
  have hcl : c * l ≠ 0 := mul_ne_zero hc hl
  have e : c * (k * l) + d = c * l * (k - r) := by
    simp only [r]; field_simp; ring
  rw [e] at hbd
  have hsq : (c * l * (k - r)) ^ 2 ≤ (c * l) ^ 2 := by
    rw [mul_pow]
    have : (k - r) ^ 2 ≤ 1 := by nlinarith
    nlinarith [sq_nonneg (c * l)]
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-! ### Upper triangular elements -/

lemma upper_pow {v : SL(2, ℝ)} (hv : v 1 0 = 0) (n : ℕ) :
    (v ^ n) 1 0 = 0 ∧ (v ^ n) 1 1 = v 1 1 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    simp only [pow_succ, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    rw [h1, h2, hv]
    constructor <;> ring

lemma det_upper {v : SL(2, ℝ)} (hv : v 1 0 = 0) : v 0 0 * v 1 1 = 1 := by
  have h := v.det_coe
  rw [det_fin_two, hv] at h
  linarith

/-- An upper triangular element of a discrete group containing a translation has diagonal
entries `±1`. -/
theorem lowerRight_eq_one_or_neg_one {Γ : Subgroup SL(2, ℝ)} [DiscreteTopology Γ] {l : ℝ}
    (hl : l ≠ 0) (hlΓ : SL2R.uU l ∈ Γ) {v : SL(2, ℝ)} (hv : v ∈ Γ) (hv10 : v 1 0 = 0) :
    v 1 1 = 1 ∨ v 1 1 = -1 := by
  obtain ⟨δ, hδ, hb⟩ := M2.exists_bottom_row_bound hlΓ hl (SL2R.coe_uU l)
  have hdet := det_upper hv10
  have key : ∀ w ∈ Γ, w 1 0 = 0 → ¬ w 1 1 ^ 2 < 1 := by
    intro w hw hw10 hlt
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hδ hlt
    have h1 := hb _ (pow_mem hw n)
    rw [(upper_pow hw10 n).1, (upper_pow hw10 n).2] at h1
    rw [← pow_mul, mul_comm, pow_mul] at hn
    linarith [sq_nonneg (0 : ℝ)]
  have hinv10 : v⁻¹ 1 0 = 0 := by
    simp [Matrix.SpecialLinearGroup.coe_inv, adjugate_fin_two, hv10]
  have hinv11 : v⁻¹ 1 1 = v 0 0 := by
    simp [Matrix.SpecialLinearGroup.coe_inv, adjugate_fin_two]
  have h1 := key v hv hv10
  have h2 := key _ (inv_mem hv) hinv10
  rw [hinv11] at h2
  push Not at h1 h2
  have h3 : v 1 1 ^ 2 = 1 := by
    by_contra hne
    have hgt : 1 < v 1 1 ^ 2 := lt_of_le_of_ne h1 (Ne.symm hne)
    have : (v 0 0 * v 1 1) ^ 2 = 1 := by rw [hdet]; norm_num
    rw [mul_pow] at this
    nlinarith
  exact mul_self_eq_one_iff.mp (by rw [← sq]; exact h3)

/-! ### The normal form: one cusp -/

section normal

variable {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
  (hrel : x ^ 2 + y ^ 2 + z ^ 2 = x * y * z)

/-- `u₄ = K² ∈ Γ₀` (the square of the commutator `K = -u₂`). -/
lemma uU_four_mem : SL2R.uU 4 ∈ Subgroup.closure {nA hz hrel, nB hz hrel} := by
  have hA : nA hz hrel ∈ Subgroup.closure {nA hz hrel, nB hz hrel} :=
    Subgroup.subset_closure (by simp)
  have hB : nB hz hrel ∈ Subgroup.closure {nA hz hrel, nB hz hrel} :=
    Subgroup.subset_closure (by simp)
  set K := nA hz hrel * nB hz hrel * (nA hz hrel)⁻¹ * (nB hz hrel)⁻¹
  have hK : K ∈ Subgroup.closure {nA hz hrel, nB hz hrel} :=
    mul_mem (mul_mem (mul_mem hA hB) (inv_mem hA)) (inv_mem hB)
  have e : SL2R.uU 4 = K * K := by
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_commutator_n hz hrel]
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]; norm_num
  rw [e]; exact mul_mem hK hK

/-- The lower-left entry of a conjugate of a translation. -/
lemma conj_uU_lowerLeft (h : SL(2, ℝ)) (t : ℝ) :
    (h * SL2R.uU t * h⁻¹) 1 0 = -t * h 1 0 ^ 2 := by
  have e := M2.conj_translation h⁻¹ (SL2R.uU t) (SL2R.coe_uU t)
  rw [inv_inv] at e
  rw [e]
  simp [Matrix.SpecialLinearGroup.coe_inv, adjugate_fin_two]

/-- The point `i n` of the upper half plane. -/
noncomputable def iN (n : ℕ) (hn : 0 < n) : ℍ :=
  ⟨(n : ℂ) * Complex.I, by simpa using hn⟩

include hx hy in
/-- **One cusp.** If `g uU t g⁻¹ ∈ Γ₀` for some `t ≠ 0`, then some `γ g` (`γ ∈ Γ₀`) fixes `∞`. -/
theorem exists_mem_lowerLeft_eq_zero (h1 : x < y + z) (h2 : y < x + z) (h3 : z < x + y)
    {g : SL(2, ℝ)} {t : ℝ} (ht : t ≠ 0)
    (hg : g * SL2R.uU t * g⁻¹ ∈ Subgroup.closure {nA hz hrel, nB hz hrel}) :
    ∃ γ ∈ Subgroup.closure {nA hz hrel, nB hz hrel}, (γ * g) 1 0 = 0 := by
  set Γ := Subgroup.closure {nA hz hrel, nB hz hrel}
  haveI := discreteTopology_normal hx hy hz hrel
  obtain ⟨ε, hε, hS⟩ := exists_lowerLeft_bound (by norm_num : (4 : ℝ) ≠ 0) (uU_four_mem hz hrel)
  obtain ⟨η, hη, hcov⟩ := exists_strip_cover_normal hz hrel hx hy h1 h2 h3
  obtain ⟨n, hn⟩ := exists_nat_gt (t ^ 2 / (η ^ 2 * ε))
  have hn0 : 0 < n := by
    have : 0 ≤ t ^ 2 / (η ^ 2 * ε) := by positivity
    exact_mod_cast this.trans_lt hn
  obtain ⟨γ, hγ, hγw⟩ := hcov (g • iN n hn0)
  refine ⟨γ, hγ, ?_⟩
  set h := γ * g
  by_contra hc
  -- the height bound
  have him : η ≤ (h • iN n hn0).im := by rw [mul_smul]; exact hγw.2
  rw [im_smul_SL] at him
  have hnorm : Complex.normSq (h 1 0 * ((iN n hn0 : ℍ) : ℂ) + h 1 1) =
      h 1 1 ^ 2 + h 1 0 ^ 2 * n ^ 2 := by
    simp [iN, Complex.normSq_apply]; ring
  have hiN : (iN n hn0).im = n := by simp [iN, UpperHalfPlane.im]
  rw [hnorm, hiN] at him
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn0
  have hpos : 0 < h 1 1 ^ 2 + h 1 0 ^ 2 * n ^ 2 := by
    have : 0 < h 1 0 ^ 2 := by positivity
    positivity
  rw [le_div_iff₀ hpos] at him
  have hb : η * h 1 0 ^ 2 * n ≤ 1 := by
    nlinarith [sq_nonneg (h 1 1), sq_nonneg (h 1 0)]
  -- the conjugated translation
  have hq : h * SL2R.uU t * h⁻¹ ∈ Γ := by
    have e : h * SL2R.uU t * h⁻¹ = γ * (g * SL2R.uU t * g⁻¹) * γ⁻¹ := by
      simp only [h]; group
    rw [e]; exact mul_mem (mul_mem hγ hg) (inv_mem hγ)
  have hq10 := conj_uU_lowerLeft h t
  have hne : (h * SL2R.uU t * h⁻¹) 1 0 ≠ 0 := by
    rw [hq10]; exact mul_ne_zero (neg_ne_zero.mpr ht) (pow_ne_zero 2 hc)
  have hεq := hS _ hq hne
  rw [hq10] at hεq
  -- `ε ≤ t² c⁴` and `η c² n ≤ 1` contradict the choice of `n`
  rw [div_lt_iff₀ (by positivity)] at hn
  set u := h 1 0 ^ 2
  have hu : 0 ≤ u := sq_nonneg _
  have e1 : (-t * u) ^ 2 = t ^ 2 * u ^ 2 := by ring
  rw [e1] at hεq
  have hb2 : (η * u * n) ^ 2 ≤ 1 := by
    have : 0 ≤ η * u * n := by positivity
    nlinarith
  have : ε * η ^ 2 * n ^ 2 ≤ t ^ 2 := by
    calc ε * η ^ 2 * n ^ 2 ≤ t ^ 2 * u ^ 2 * η ^ 2 * n ^ 2 := by gcongr
      _ = t ^ 2 * (η * u * n) ^ 2 := by ring
      _ ≤ t ^ 2 * 1 := by gcongr
      _ = t ^ 2 := mul_one _
  have hnn : (n : ℝ) ≤ n ^ 2 := by nlinarith
  nlinarith [mul_pos hε (pow_pos hη 2)]

end normal

end OrbicurveCores.Fuchsian
