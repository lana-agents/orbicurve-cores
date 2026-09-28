/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.M2.Unipotent
import OrbicurveCores.M2.PadicUnbounded
import OrbicurveCores.M2.Rational
import OrbicurveCores.ForMathlib.ComplexEmbedding
import OrbicurveCores.Fuchsian.Commensurator
import OrbicurveCores.Classification

/-!
# M2: the finish

For a once-punctured torus group `Γ` in Fricke normal form with dense commensurator:

* over `ℂ`: for every ring embedding `σ : ℝ → ℂ`, the action `g ↦ σ(g)` of the commensurator
  on `ℙ¹(ℂ)` extends continuously (superrigidity), which forces `σ(x²) = x²` and likewise for
  `y²`, `z²` (`complex_rigidity`). Hence `x², y², z² ∈ ℚ`.
-/

open MeasureTheory Filter Set Topology OnePoint OnePoint.Proj
open scoped MatrixGroups Pointwise
open Subgroup.Commensurable (commensurator)

namespace OrbicurveCores.M2

section general

variable {k : Type*} [NontriviallyNormedField k] [DecidableEq k]

/-- `SL(2, ℝ) → GL(2, k)` through a ring hom `σ : ℝ → k`. -/
noncomputable def slMap (σ : ℝ →+* k) (g : SL(2, ℝ)) : GL (Fin 2) k :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero ((g : Matrix (Fin 2) (Fin 2) ℝ).map σ) (by
    rw [show (g : Matrix (Fin 2) (Fin 2) ℝ).map σ = σ.mapMatrix g from rfl, ← RingHom.map_det,
      g.2, map_one]
    exact one_ne_zero)

omit [DecidableEq k] in
lemma coe_slMap (σ : ℝ →+* k) (g : SL(2, ℝ)) :
    (slMap σ g : Matrix (Fin 2) (Fin 2) k) = (g : Matrix (Fin 2) (Fin 2) ℝ).map σ := rfl

omit [DecidableEq k] in
lemma slMap_mul (σ : ℝ →+* k) (g h : SL(2, ℝ)) : slMap σ (g * h) = slMap σ g * slMap σ h := by
  ext1
  simp only [coe_slMap, Matrix.SpecialLinearGroup.coe_mul, Units.val_mul]
  exact Matrix.map_mul

lemma actsOn_slMap (σ : ℝ →+* k) (Γ : Subgroup SL(2, ℝ)) : ActsOn Γ (slMap σ) :=
  fun g _ h _ y ↦ by rw [slMap_mul, mul_smul]

variable {Γ : Subgroup SL(2, ℝ)} {a : SL(2, ℝ) → GL (Fin 2) k}

lemma ActsOn.smul_pow (hact : ActsOn Γ a) {g : SL(2, ℝ)} (hg : g ∈ Γ) (n : ℕ)
    (y : OnePoint k) : a (g ^ n) • y = (fun z ↦ a g • z)^[n] y := by
  induction n generalizing y with
  | zero => simp [hact.one]
  | succ n ih =>
    rw [pow_succ', hact _ hg _ (pow_mem hg n), ih, Function.iterate_succ_apply']

variable [CharZero k]

omit [CharZero k] in
lemma transl_iterate (b : k) (n : ℕ) (y : OnePoint k) :
    (fun z ↦ transl b • z)^[n] y = transl (n * b) • y := by
  induction n generalizing y with
  | zero =>
    simp only [Function.iterate_zero, id_eq, Nat.cast_zero, zero_mul]
    induction y using OnePoint.rec with
    | infty => rw [transl_smul_infty]
    | coe z => rw [transl_smul_coe, add_zero]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    induction y using OnePoint.rec with
    | infty => simp [transl_smul_infty]
    | coe z => simp only [transl_smul_coe, OnePoint.coe_eq_coe]; push_cast; ring

omit [CharZero k] in
lemma transl_fixed {b : k} (hb : b ≠ 0) {y : OnePoint k} (h : transl b • y = y) : y = ∞ := by
  induction y using OnePoint.rec with
  | infty => rfl
  | coe z =>
    rw [transl_smul_coe, OnePoint.coe_eq_coe] at h
    exact absurd (by linear_combination h : b = 0) hb

/-- **Non-elementarity.** If `a(K)` is the translation by `2` and `a(A) ∞ ≠ ∞`, no finite-index
subgroup of `Γ ∋ K, A` has a fixed point. -/
theorem nonElem_of (hact : ActsOn Γ a) {K A : SL(2, ℝ)} (hK : K ∈ Γ) (hA : A ∈ Γ)
    (hKt : ∀ y : OnePoint k, a K • y = transl (2 : k) • y)
    (hAinf : a A • (∞ : OnePoint k) ≠ ∞) : NonElem Γ a := by
  intro Γ'' hle hfi y
  by_contra hall
  push Not at hall
  have hpow : ∀ n : ℕ, 0 < n → ∀ y : OnePoint k, a (K ^ n) • y = y → y = ∞ := by
    intro n hn y hy
    rw [hact.smul_pow hK, show (fun z ↦ a K • z) = fun z ↦ transl (2 : k) • z from funext hKt,
      transl_iterate] at hy
    exact transl_fixed (mul_ne_zero (Nat.cast_ne_zero.2 hn.ne') two_ne_zero) hy
  obtain ⟨m, hm, -, hmem⟩ := Subgroup.exists_pow_mem_of_relIndex_ne_zero hfi hK
  have hy : y = ∞ := hpow m hm y (hall _ (Subgroup.mem_inf.1 hmem).1)
  subst hy
  have hAK : A * K * A⁻¹ ∈ Γ := mul_mem (mul_mem hA hK) (inv_mem hA)
  obtain ⟨m', hm', -, hmem'⟩ := Subgroup.exists_pow_mem_of_relIndex_ne_zero hfi hAK
  have h1 := hall _ (Subgroup.mem_inf.1 hmem').1
  rw [conj_pow, hact _ (mul_mem hA (pow_mem hK m')) _ (inv_mem hA),
    hact _ hA _ (pow_mem hK m')] at h1
  set w := a A⁻¹ • (∞ : OnePoint k)
  have hw : a A • w = ∞ := by
    simp only [w]; rw [← hact _ hA _ (inv_mem hA), mul_inv_cancel, hact.one]
  have hKw : a (K ^ m') • w = w := by
    rw [← hw] at h1
    exact (smul_left_cancel_iff (a A)).1 h1
  have := hpow m' hm' w hKw
  rw [this] at hw
  exact hAinf hw

end general

lemma neg_one_mem_commensurator (Γ : Subgroup SL(2, ℝ)) : (-1 : SL(2, ℝ)) ∈ commensurator Γ := by
  rw [Subgroup.Commensurable.commensurator_mem_iff]
  have : ConjAct.toConjAct (-1 : SL(2, ℝ)) • Γ = Γ := by
    ext g
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def]
    simp
  rw [this]

section normalForm

open Fuchsian

variable {x y z : ℝ} (hz : 0 < z) (hrel : x ^ 2 + y ^ 2 + z ^ 2 = x * y * z)

/-- The parabolic commutator of the normal form. -/
noncomputable def commK : SL(2, ℝ) := nA hz hrel * nB hz hrel * (nA hz hrel)⁻¹ * (nB hz hrel)⁻¹

lemma commK_mem : commK hz hrel ∈ Subgroup.closure {nA hz hrel, nB hz hrel} := by
  have hA : nA hz hrel ∈ Subgroup.closure {nA hz hrel, nB hz hrel} :=
    Subgroup.subset_closure (by simp)
  have hB : nB hz hrel ∈ Subgroup.closure {nA hz hrel, nB hz hrel} :=
    Subgroup.subset_closure (by simp)
  exact mul_mem (mul_mem (mul_mem hA hB) (inv_mem hA)) (inv_mem hB)

lemma coe_commK : (commK hz hrel : Matrix (Fin 2) (Fin 2) ℝ) = !![-1, -2; 0, -1] :=
  coe_commutator_n hz hrel

lemma uU_two_eq : SL2R.uU 2 = -1 * commK hz hrel := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_commK]
  fin_cases i <;> fin_cases j <;> simp [SL2R.uU]

variable {k : Type*} [NontriviallyNormedField k] [DecidableEq k] [CharZero k]

lemma slMap_commK (σ : ℝ →+* k) (y : OnePoint k) :
    slMap σ (commK hz hrel) • y = transl (2 : k) • y := by
  rw [gl_smul_eq_mob, gl_smul_eq_mob, coe_slMap, coe_commK]
  have : (!![-1, -2; 0, -1] : Matrix (Fin 2) (Fin 2) ℝ).map σ =
      (-1 : k) • ((transl (2 : k) : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [transl, map_ofNat]
  rw [this, mob_smul_matrix (neg_ne_zero.2 one_ne_zero)]

omit [CharZero k] in
lemma slMap_uU_two (σ : ℝ →+* k) (y : OnePoint k) :
    slMap σ (SL2R.uU 2) • y = transl (2 : k) • y := by
  rw [gl_smul_eq_mob, gl_smul_eq_mob, coe_slMap]
  congr 1
  ext i j; fin_cases i <;> fin_cases j <;> simp [transl, SL2R.uU, map_ofNat]

lemma slMap_neg_one (σ : ℝ →+* k) (y : OnePoint k) : slMap σ (-1) • y = y := by
  rw [gl_smul_eq_mob, coe_slMap]
  have : ((-1 : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ).map σ = (-1 : k) • 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [this, mob_smul_matrix (neg_ne_zero.2 one_ne_zero), mob_one]

omit [CharZero k] in
lemma slMap_nA_infty (σ : ℝ →+* k) (hx : x ≠ 0) :
    slMap σ (nA hz hrel) • (∞ : OnePoint k) ≠ ∞ := by
  rw [Ne, smul_infty_eq_self_iff, coe_slMap, coe_nA]
  simp only [Matrix.map_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
    Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one]
  intro h
  exact hx (σ.injective (by rw [h, map_zero]))

end normalForm

section complexStep

open Fuchsian

variable {x y z : ℝ} (hz : 0 < z) (hrel : x ^ 2 + y ^ 2 + z ^ 2 = x * y * z)

lemma tendsto_coe_infty_of_norm {f : ℕ → ℂ} (hf : Tendsto (fun n ↦ ‖f n‖) atTop atTop) :
    Tendsto (fun n ↦ (f n : OnePoint ℂ)) atTop (𝓝 ∞) := by
  intro U hU
  obtain ⟨R, -, hR⟩ := exists_norm_ge_mem hU
  exact (hf.eventually_ge_atTop R).mono fun n hn ↦ hR _ hn

/-- Over `ℂ`, `σ(Γ)` is unbounded: `Kⁿ(0, 1, ∞) = (2n, 2n + 1, ∞) → (∞, ∞, ∞)`. -/
lemma unbounded_complex [DecidableEq ℂ] (σ : ℝ →+* ℂ) :
    Unbounded (Subgroup.closure {nA hz hrel, nB hz hrel}) (slMap σ) := by
  refine ⟨fun n ↦ commK hz hrel ^ n, fun n ↦ pow_mem (commK_mem hz hrel) n, (∞, ∞, ∞),
    fun h ↦ h.1 rfl, ?_⟩
  have hact := actsOn_slMap σ (Subgroup.closure {nA hz hrel, nB hz hrel})
  have e : ∀ (n : ℕ) (w : OnePoint ℂ), slMap σ (commK hz hrel ^ n) • w =
      transl ((n : ℂ) * 2) • w := by
    intro n w
    rw [hact.smul_pow (commK_mem hz hrel),
      show (fun v ↦ slMap σ (commK hz hrel) • v) = fun v ↦ transl (2 : ℂ) • v from
        funext (slMap_commK hz hrel σ), transl_iterate]
  have hn : ∀ c : ℂ, Tendsto (fun n : ℕ ↦ ‖c + (n : ℂ) * 2‖) atTop atTop := by
    intro c
    refine tendsto_atTop_mono (fun n ↦ ?_) (tendsto_atTop_add_const_right _ (-‖c‖)
      (tendsto_natCast_atTop_atTop.atTop_mul_const (show (0 : ℝ) < 2 by norm_num)))
    calc (n : ℝ) * 2 + -‖c‖ = ‖(n : ℂ) * 2‖ - ‖c‖ := by
          rw [norm_mul, Complex.norm_natCast, Complex.norm_two]; ring
      _ ≤ ‖c + (n : ℂ) * 2‖ := by
          have := norm_sub_norm_le ((n : ℂ) * 2) (-c)
          rw [norm_neg, sub_neg_eq_add, add_comm] at this
          exact this
  simp only [smul3, e₃, e, transl_smul_coe, transl_smul_infty]
  exact (tendsto_coe_infty_of_norm (hn 0)).prodMk_nhds
    ((tendsto_coe_infty_of_norm (hn 1)).prodMk_nhds tendsto_const_nhds)

/-- **The complex step.** If the commensurator of a normal-form group is dense, then every ring
embedding `σ : ℝ → ℂ` fixes `x², y², z²`. -/
theorem sq_fixed_of_dense (hx : 0 < x) (hy : 0 < y) (h1 : x < y + z) (h2 : y < x + z)
    (h3 : z < x + y)
    (hdense : Dense (commensurator (Subgroup.closure {nA hz hrel, nB hz hrel}) : Set SL(2, ℝ)))
    (σ : ℝ →+* ℂ) :
    σ x ^ 2 = (x : ℂ) ^ 2 ∧ σ y ^ 2 = (y : ℂ) ^ 2 ∧ σ z ^ 2 = (z : ℂ) ^ 2 := by
  classical
  set Γ := Subgroup.closure {nA hz hrel, nB hz hrel}
  set Δ := commensurator Γ
  have hA : nA hz hrel ∈ Γ := Subgroup.subset_closure (by simp)
  have hB : nB hz hrel ∈ Γ := Subgroup.subset_closure (by simp)
  obtain ⟨Φ, hΦ, hext, hcont⟩ := commensurator_superrigidity (k := ℂ)
    (goodLattice_normal hz hrel hx hy h1 h2 h3) (le_commensurator Γ) le_rfl hdense
    (actsOn_slMap σ Δ)
    (nonElem_of (actsOn_slMap σ Γ) (commK_mem hz hrel) hA (slMap_commK hz hrel σ)
      (slMap_nA_infty hz hrel σ hx.ne'))
    (unbounded_complex hz hrel σ)
  have hU2 : SL2R.uU 2 ∈ Δ := by
    rw [uU_two_eq hz hrel]
    exact mul_mem (neg_one_mem_commensurator Γ) (le_commensurator Γ (commK_mem hz hrel))
  have htr : UnipotentRigidity.IsTransl Φ 2 2 := fun w ↦ by
    rw [hext _ hU2, slMap_uU_two]
  have hneg : ∀ w : OnePoint ℂ, Φ (-1) • w = w := fun w ↦ by
    rw [hext _ (neg_one_mem_commensurator Γ), slMap_neg_one]
  have hmob : ∀ γ ∈ Γ, ∀ w : OnePoint ℂ,
      Φ γ • w = OnePoint.Proj.mob ((γ : Matrix (Fin 2) (Fin 2) ℝ).map σ) w := by
    intro γ hγ w
    rw [hext _ (le_commensurator Γ hγ), gl_smul_eq_mob, coe_slMap]
  have hAB : nA hz hrel * nB hz hrel ∈ Γ := mul_mem hA hB
  have rA := complex_rigidity hΦ hcont htr hneg σ (hmob _ hA)
    (by rw [coe_nA]; simpa using hx.ne')
  have rB := complex_rigidity hΦ hcont htr hneg σ (hmob _ hB)
    (by rw [coe_nB]; simpa using hy.ne')
  have rAB := complex_rigidity hΦ hcont htr hneg σ (hmob _ hAB)
    (by rw [coe_nAnB]; simpa using hz.ne')
  rw [coe_nA] at rA
  rw [coe_nB] at rB
  rw [coe_nAnB] at rAB
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_zero,
    Matrix.empty_val', Matrix.cons_val_fin_one, map_neg, neg_sq, Complex.ofReal_neg] at rA rB rAB
  exact ⟨rA, rB, rAB⟩

/-- Consequently `x², y², z²` are rational. -/
theorem sq_rat_of_dense (hx : 0 < x) (hy : 0 < y) (h1 : x < y + z) (h2 : y < x + z)
    (h3 : z < x + y)
    (hdense : Dense (commensurator (Subgroup.closure {nA hz hrel, nB hz hrel}) : Set SL(2, ℝ))) :
    x ^ 2 ∈ Set.range ((↑) : ℚ → ℝ) ∧ y ^ 2 ∈ Set.range ((↑) : ℚ → ℝ) ∧
      z ^ 2 ∈ Set.range ((↑) : ℚ → ℝ) := by
  have key : ∀ w : ℝ, (∀ σ : ℝ →+* ℂ, σ w ^ 2 = (w : ℂ) ^ 2) →
      w ^ 2 ∈ Set.range ((↑) : ℚ → ℝ) := by
    intro w hw
    by_contra hno
    obtain ⟨σ, hσ⟩ := exists_ringHom_real_complex_ne hno
    apply hσ
    rw [map_pow, hw σ, Complex.ofReal_pow]
  exact ⟨key x fun σ ↦ (sq_fixed_of_dense hz hrel hx hy h1 h2 h3 hdense σ).1,
    key y fun σ ↦ (sq_fixed_of_dense hz hrel hx hy h1 h2 h3 hdense σ).2.1,
    key z fun σ ↦ (sq_fixed_of_dense hz hrel hx hy h1 h2 h3 hdense σ).2.2⟩

end complexStep


/-! ### The `p`-adic step -/

/-- A rational number which is `p`-integral for every prime `p` is an integer. -/
lemma exists_int_of_padicNorm_le_one {q : ℚ} (h : ∀ p : ℕ, p.Prime → padicNorm p q ≤ 1) :
    ∃ m : ℤ, q = m := by
  by_cases hden : q.den = 1
  · exact ⟨q.num, (Rat.coe_int_num_of_den_eq_one hden).symm⟩
  exfalso
  set p := q.den.minFac
  have hp : p.Prime := Nat.minFac_prime hden
  haveI : Fact p.Prime := ⟨hp⟩
  have hpd : p ∣ q.den := Nat.minFac_dvd _
  have hq0 : q ≠ 0 := fun h0 ↦ hden (by rw [h0]; rfl)
  have hnum : padicValInt p q.num = 0 := by
    refine padicValInt.eq_zero_of_not_dvd fun hdvd ↦ ?_
    have h1 : p ∣ q.num.natAbs := Int.natCast_dvd.1 hdvd
    have := Nat.dvd_gcd h1 hpd
    rw [q.reduced] at this
    exact hp.one_lt.ne' (Nat.dvd_one.1 this)
  have hden1 : 1 ≤ padicValNat p q.den := one_le_padicValNat_of_dvd q.den_nz hpd
  have hle := h p hp
  rw [padicNorm, if_neg hq0, padicValRat_def, hnum] at hle
  push_cast at hle
  rw [zero_sub, neg_neg] at hle
  have : (1 : ℚ) < (p : ℚ) ^ padicValRat p (q.den : ℚ) := by
    rw [padicValRat.of_nat]
    exact one_lt_zpow₀ (by exact_mod_cast hp.one_lt) (by omega)
  exact absurd hle (not_le.2 this)

namespace IsRatMul

variable {g : SL(2, ℝ)}

/-- A chosen scalar for a rational multiple. -/
noncomputable def scal (h : IsRatMul g) : ℝ := h.choose

/-- A chosen rational matrix for a rational multiple. -/
noncomputable def rep (h : IsRatMul g) : Matrix (Fin 2) (Fin 2) ℚ := h.choose_spec.2.choose

lemma scal_ne_zero (h : IsRatMul g) : h.scal ≠ 0 := h.choose_spec.1

lemma spec (h : IsRatMul g) :
    (g : Matrix (Fin 2) (Fin 2) ℝ) = h.scal • h.rep.map ((↑) : ℚ → ℝ) :=
  h.choose_spec.2.choose_spec

lemma det_ne_zero_of {c : ℝ} {R : Matrix (Fin 2) (Fin 2) ℚ}
    (hR : (g : Matrix (Fin 2) (Fin 2) ℝ) = c • R.map ((↑) : ℚ → ℝ)) : R.det ≠ 0 := by
  intro h0
  have := g.2
  rw [hR, Matrix.det_smul, show R.map ((↑) : ℚ → ℝ) = (Rat.castHom ℝ).mapMatrix R from rfl,
    ← RingHom.map_det, h0, map_zero, mul_zero] at this
  exact zero_ne_one this

/-- Rational representatives are unique up to a rational scalar. -/
lemma rep_unique (h : IsRatMul g) {c : ℝ} (hc : c ≠ 0) {R : Matrix (Fin 2) (Fin 2) ℚ}
    (hR : (g : Matrix (Fin 2) (Fin 2) ℝ) = c • R.map ((↑) : ℚ → ℝ)) :
    ∃ μ : ℚ, μ ≠ 0 ∧ R = μ • h.rep := by
  classical
  have hrep0 : h.rep ≠ 0 := fun h0 ↦ det_ne_zero_of h.spec (by rw [h0, Matrix.det_zero])
  obtain ⟨i, j, hij⟩ : ∃ i j, h.rep i j ≠ 0 := by
    by_contra hno; push Not at hno; exact hrep0 (by ext i j; exact hno i j)
  have e : ∀ a b, c * (R a b : ℝ) = h.scal * (h.rep a b : ℝ) := by
    intro a b
    have := congrFun (congrFun (hR.symm.trans h.spec) a) b
    simpa using this
  set μ : ℚ := R i j / h.rep i j
  have hμ : (μ : ℝ) = h.scal / c := by
    simp only [μ, Rat.cast_div]
    have := e i j
    have hij' : (h.rep i j : ℝ) ≠ 0 := by exact_mod_cast hij
    field_simp
    linear_combination this
  refine ⟨μ, ?_, ?_⟩
  · intro h0
    rw [h0, Rat.cast_zero] at hμ
    exact h.scal_ne_zero (by field_simp at hμ; linarith [hμ])
  · ext a b
    have := e a b
    have : (R a b : ℝ) = (μ : ℝ) * h.rep a b := by
      rw [hμ]; field_simp; linear_combination this
    simpa using (by exact_mod_cast this : R a b = μ * h.rep a b)

end IsRatMul

section padicAction

variable (p : ℕ) [Fact p.Prime] [DecidableEq ℚ_[p]]

/-- The `p`-adic action of a rationally represented element (`1` otherwise). -/
noncomputable def aP (g : SL(2, ℝ)) : GL (Fin 2) ℚ_[p] := by
  classical
  exact if h : IsRatMul g then
    Matrix.GeneralLinearGroup.mkOfDetNeZero (h.rep.map ((↑) : ℚ → ℚ_[p])) (by
      rw [show h.rep.map ((↑) : ℚ → ℚ_[p]) = (Rat.castHom ℚ_[p]).mapMatrix h.rep from rfl,
        ← RingHom.map_det]
      exact (map_ne_zero _).2 (IsRatMul.det_ne_zero_of h.spec))
    else 1

variable {p}

lemma aP_smul {g : SL(2, ℝ)} (h : IsRatMul g) {c : ℝ} (hc : c ≠ 0)
    {R : Matrix (Fin 2) (Fin 2) ℚ} (hR : (g : Matrix (Fin 2) (Fin 2) ℝ) = c • R.map ((↑) : ℚ → ℝ))
    (y : OnePoint ℚ_[p]) : aP p g • y = OnePoint.Proj.mob (R.map ((↑) : ℚ → ℚ_[p])) y := by
  obtain ⟨μ, hμ, rfl⟩ := h.rep_unique hc hR
  simp only [aP, dif_pos h]
  rw [gl_smul_eq_mob]
  change OnePoint.Proj.mob (h.rep.map ((↑) : ℚ → ℚ_[p])) y = _
  rw [show (μ • h.rep).map ((↑) : ℚ → ℚ_[p]) = (μ : ℚ_[p]) • h.rep.map ((↑) : ℚ → ℚ_[p]) by
    ext i j; simp, mob_smul_matrix (by exact_mod_cast hμ)]

lemma actsOn_aP {Δ : Subgroup SL(2, ℝ)} (hΔ : ∀ δ ∈ Δ, IsRatMul δ) : ActsOn Δ (aP p) := by
  intro g hg h hh y
  have hg' := hΔ g hg
  have hh' := hΔ h hh
  have hgh : ((g * h : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
      (hg'.scal * hh'.scal) • (hg'.rep * hh'.rep).map ((↑) : ℚ → ℝ) := by
    rw [Matrix.SpecialLinearGroup.coe_mul, hg'.spec, hh'.spec, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul]
    congr 1
    exact (Matrix.map_mul (L := hg'.rep) (M := hh'.rep) (f := Rat.castHom ℝ)).symm
  rw [aP_smul (hΔ _ (mul_mem hg hh)) (mul_ne_zero hg'.scal_ne_zero hh'.scal_ne_zero) hgh,
    aP_smul hg' hg'.scal_ne_zero hg'.spec, aP_smul hh' hh'.scal_ne_zero hh'.spec,
    show (hg'.rep * hh'.rep).map ((↑) : ℚ → ℚ_[p]) =
      hg'.rep.map (↑) * hh'.rep.map (↑) from Matrix.map_mul (f := Rat.castHom ℚ_[p]), mob_mul]
  · rw [show hh'.rep.map ((↑) : ℚ → ℚ_[p]) = (Rat.castHom ℚ_[p]).mapMatrix hh'.rep from rfl,
      ← RingHom.map_det]
    exact (map_ne_zero _).2 (IsRatMul.det_ne_zero_of hh'.spec)

end padicAction

lemma mob_infty_ne_infty {k : Type*} [Field k] [DecidableEq k] {M : Matrix (Fin 2) (Fin 2) k}
    (h : M 1 0 ≠ 0) : OnePoint.Proj.mob M (∞ : OnePoint k) ≠ ∞ := by
  simp [OnePoint.Proj.mob, OnePoint.Proj.mv, OnePoint.Proj.proj, h]

section padicStep

open Fuchsian

variable {x y z : ℝ} (hz : 0 < z) (hrel : x ^ 2 + y ^ 2 + z ^ 2 = x * y * z)
  {X Y Z : ℚ} (hX : x ^ 2 = X) (hY : y ^ 2 = Y) (hZ : z ^ 2 = Z)

/-- For an element of the normal-form group, `tr(γ)² = tr(R)²/det(R)` for its rational
representative `R`. -/
lemma trace_sq_eq {γ : SL(2, ℝ)} (h : IsRatMul γ) :
    (γ : Matrix (Fin 2) (Fin 2) ℝ).trace ^ 2 = ((h.rep.trace ^ 2 / h.rep.det : ℚ) : ℝ) := by
  have hdet := γ.2
  rw [h.spec, Matrix.det_smul] at hdet
  rw [h.spec, Matrix.trace_smul, smul_eq_mul]
  have e1 : (h.rep.map ((↑) : ℚ → ℝ)).trace = ((h.rep.trace : ℚ) : ℝ) := by
    simp [Matrix.trace_fin_two]
  have e2 : (h.rep.map ((↑) : ℚ → ℝ)).det = ((h.rep.det : ℚ) : ℝ) := by
    rw [show h.rep.map ((↑) : ℚ → ℝ) = (Rat.castHom ℝ).mapMatrix h.rep from rfl,
      ← RingHom.map_det]; rfl
  rw [e1]
  rw [e2] at hdet
  have hd : ((h.rep.det : ℚ) : ℝ) ≠ 0 := by exact_mod_cast IsRatMul.det_ne_zero_of h.spec
  rw [Rat.cast_div, Rat.cast_pow]
  field_simp
  simp only [Fintype.card_fin] at hdet
  linear_combination ((h.rep.trace : ℚ) : ℝ) ^ 2 * hdet

include hX hY hZ in
/-- **The `p`-adic step.** With `x², y², z² ∈ ℚ` and a dense commensurator, every squared trace
of the normal-form group is `p`-integral. -/
theorem padicNorm_trace_sq_le_one (hx : 0 < x) (hy : 0 < y) (h1 : x < y + z) (h2 : y < x + z)
    (h3 : z < x + y)
    (hdense : Dense (commensurator (Subgroup.closure {nA hz hrel, nB hz hrel}) : Set SL(2, ℝ)))
    (p : ℕ) [Fact p.Prime] {γ : SL(2, ℝ)}
    (hγ : γ ∈ Subgroup.closure {nA hz hrel, nB hz hrel}) (hγ' : IsRatMul γ) :
    padicNorm p (hγ'.rep.trace ^ 2 / hγ'.rep.det) ≤ 1 := by
  classical
  letI : MeasurableSpace ℚ_[p] := borel _
  haveI : BorelSpace ℚ_[p] := ⟨rfl⟩
  by_contra hlt
  push Not at hlt
  set Γ := Subgroup.closure {nA hz hrel, nB hz hrel}
  set Δ := commensurator Γ
  have hΔ : ∀ δ ∈ Δ, IsRatMul δ := fun δ hδ ↦ isRatMul_of_mem_commensurator hz hrel hX hY hZ hδ
  have hact : ActsOn Δ (aP p) := actsOn_aP hΔ
  have hactΓ : ActsOn Γ (aP p) := hact.mono (le_commensurator Γ)
  have hA : nA hz hrel ∈ Γ := Subgroup.subset_closure (by simp)
  -- `aP(K)` is the translation by `2`
  have hK : ∀ w : OnePoint ℚ_[p], aP p (commK hz hrel) • w = transl (2 : ℚ_[p]) • w := by
    intro w
    have hrep : ((commK hz hrel : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
        (1 : ℝ) • (!![-1, -2; 0, -1] : Matrix (Fin 2) (Fin 2) ℚ).map ((↑) : ℚ → ℝ) := by
      rw [coe_commK, one_smul]; ext i j; fin_cases i <;> fin_cases j <;> simp
    rw [aP_smul (hΔ _ (le_commensurator Γ (commK_mem hz hrel))) one_ne_zero hrep,
      gl_smul_eq_mob]
    have : (!![-1, -2; 0, -1] : Matrix (Fin 2) (Fin 2) ℚ).map ((↑) : ℚ → ℚ_[p]) =
        (-1 : ℚ_[p]) •
          ((transl (2 : ℚ_[p]) : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [transl]
    rw [this, mob_smul_matrix (neg_ne_zero.2 one_ne_zero)]
  have hAinf : aP p (nA hz hrel) • (∞ : OnePoint ℚ_[p]) ≠ ∞ := by
    have hA' := hΔ _ (le_commensurator Γ hA)
    rw [aP_smul hA' hA'.scal_ne_zero hA'.spec]
    refine mob_infty_ne_infty ?_
    have e := congrFun (congrFun hA'.spec 1) 0
    rw [coe_nA] at e
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_zero,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.smul_apply, Matrix.map_apply,
      smul_eq_mul] at e
    intro h0
    have : (hA'.rep 1 0 : ℝ) = 0 := by
      simp only [Matrix.map_apply] at h0; exact_mod_cast h0
    rw [this, mul_zero] at e
    exact hx.ne' e
  have hne := nonElem_of hactΓ (commK_mem hz hrel) hA hK hAinf
  -- unboundedness from the non-integral trace
  have hunb : Unbounded Γ (aP p) := by
    have hcoe : ((aP p γ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) =
        hγ'.rep.map ((↑) : ℚ → ℚ_[p]) := by
      simp only [aP, dif_pos hγ']
      rfl
    have hnorm : ‖((aP p γ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]).det‖ <
        ‖((aP p γ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]).trace‖ ^ 2 := by
      have et : (hγ'.rep.map ((↑) : ℚ → ℚ_[p])).trace = ((hγ'.rep.trace : ℚ) : ℚ_[p]) := by
        simp [Matrix.trace_fin_two]
      rw [hcoe, et, show hγ'.rep.map ((↑) : ℚ → ℚ_[p]) = (Rat.castHom ℚ_[p]).mapMatrix hγ'.rep
        from rfl, ← RingHom.map_det]
      simp only [Rat.coe_castHom, Padic.eq_padicNorm]
      have hd : hγ'.rep.det ≠ 0 := IsRatMul.det_ne_zero_of hγ'.spec
      rw [padicNorm.div, sq, padicNorm.mul] at hlt
      have hdpos : 0 < padicNorm p hγ'.rep.det :=
        lt_of_le_of_ne (padicNorm.nonneg _)
          (Ne.symm fun h0 ↦ hd (padicNorm.zero_of_padicNorm_eq_zero h0))
      rw [one_lt_div hdpos] at hlt
      exact_mod_cast (by rw [sq]; exact hlt :
        padicNorm p hγ'.rep.det < padicNorm p hγ'.rep.trace ^ 2)
    obtain ⟨τ, hτ, hlim⟩ := Padic.exists_degenerate_limit (aP p γ) hnorm
    refine ⟨fun n ↦ γ ^ n, fun n ↦ pow_mem hγ n, τ, hτ, ?_⟩
    have e : ∀ n : ℕ, smul3 (aP p (γ ^ n)) e₃ = smul3 (aP p γ ^ n) e₃ := by
      intro n
      simp only [smul3, hactΓ.smul_pow hγ, smul_iterate]
    simp_rw [e]
    exact hlim
  obtain ⟨Φ, hΦ, hext, hcont⟩ := commensurator_superrigidity (k := ℚ_[p])
    (goodLattice_normal hz hrel hx hy h1 h2 h3) (le_commensurator Γ) le_rfl hdense hact hne hunb
  have hU2 : SL2R.uU 2 ∈ Δ := by
    rw [uU_two_eq hz hrel]
    exact mul_mem (neg_one_mem_commensurator Γ) (le_commensurator Γ (commK_mem hz hrel))
  have htr : UnipotentRigidity.IsTransl Φ 2 2 := fun w ↦ by
    have hrep : ((SL2R.uU 2 : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
        (1 : ℝ) • (!![1, 2; 0, 1] : Matrix (Fin 2) (Fin 2) ℚ).map ((↑) : ℚ → ℝ) := by
      rw [one_smul]; ext i j; fin_cases i <;> fin_cases j <;> simp [SL2R.uU]
    rw [hext _ hU2, aP_smul (hΔ _ hU2) one_ne_zero hrep, gl_smul_eq_mob]
    congr 1
    ext i j; fin_cases i <;> fin_cases j <;> simp [transl]
  exact padic_contradiction hΦ hcont htr

end padicStep

/-! ### Assembly -/

section assembly

open Fuchsian

/-- **Integrality.** For a normal-form group with dense commensurator, all squared traces are
integers. -/
theorem trace_sq_int_of_dense {x y z : ℝ} (hz : 0 < z) (hrel : x ^ 2 + y ^ 2 + z ^ 2 = x * y * z)
    (hx : 0 < x) (hy : 0 < y) (h1 : x < y + z) (h2 : y < x + z) (h3 : z < x + y)
    (hdense : Dense (commensurator (Subgroup.closure {nA hz hrel, nB hz hrel}) : Set SL(2, ℝ))) :
    ∀ γ ∈ Subgroup.closure {nA hz hrel, nB hz hrel}, ∃ m : ℤ, tr γ ^ 2 = m := by
  obtain ⟨⟨X, hX⟩, ⟨Y, hY⟩, ⟨Z, hZ⟩⟩ := sq_rat_of_dense hz hrel hx hy h1 h2 h3 hdense
  intro γ hγ
  have hγ' := isRatMul_of_mem hz hrel hX.symm hY.symm hZ.symm hγ
  obtain ⟨m, hm⟩ := exists_int_of_padicNorm_le_one (q := hγ'.rep.trace ^ 2 / hγ'.rep.det)
    fun p hp ↦ by
      haveI : Fact p.Prime := ⟨hp⟩
      exact padicNorm_trace_sq_le_one hz hrel hX.symm hY.symm hZ.symm hx hy h1 h2 h3 hdense p hγ
        hγ'
  refine ⟨m, ?_⟩
  rw [tr, trace_sq_eq hγ', hm]
  push_cast; rfl

/-- The elements of `⟨A, B⟩` are, up to sign, elements of `⟨±A, ±B⟩`. -/
lemma mem_or_neg_mem_of_signs {A B A'' B'' : SL(2, ℝ)} (hA : A'' ∈ ({A, -A} : Set SL(2, ℝ)))
    (hB : B'' ∈ ({B, -B} : Set SL(2, ℝ))) {γ : SL(2, ℝ)} (hγ : γ ∈ Subgroup.closure {A, B}) :
    γ ∈ Subgroup.closure {A'', B''} ∨ -γ ∈ Subgroup.closure {A'', B''} := by
  set H'' := Subgroup.closure {A'', B''}
  have hA'' : A'' ∈ H'' := Subgroup.subset_closure (by simp)
  have hB'' : B'' ∈ H'' := Subgroup.subset_closure (by simp)
  induction hγ using Subgroup.closure_induction with
  | mem g hg =>
    rcases hg with rfl | hg
    · rcases hA with rfl | rfl
      · exact Or.inl hA''
      · right; simpa using hA''
    · rw [Set.mem_singleton_iff] at hg; subst hg
      rcases hB with rfl | rfl
      · exact Or.inl hB''
      · right; simpa using hB''
  | one => exact Or.inl (one_mem _)
  | mul g h _ _ hg hh =>
    rcases hg with hg | hg <;> rcases hh with hh | hh
    · exact Or.inl (mul_mem hg hh)
    · right; simpa using mul_mem hg hh
    · right; simpa using mul_mem hg hh
    · left; simpa using mul_mem hg hh
  | inv g _ hg =>
    rcases hg with hg | hg
    · exact Or.inl (inv_mem hg)
    · right; simpa using inv_mem hg

/-- **Margulis' commensurator theorem for once-punctured torus groups** (the input
`MargulisDenseOneInfty`): a dense commensurator forces arithmeticity. -/
theorem margulisDenseOneInfty : MargulisDenseOneInfty := by
  intro A B hcomm hA hdense
  obtain ⟨x, y, z, hx, hy, hz, hrel, ⟨t1, t2, t3⟩, A', B', hcl, A'', hA'', B'', hB'', g, hgA,
    hgB⟩ := exists_normal_form hcomm hA
  set H := Subgroup.closure {A, B}
  set H'' := Subgroup.closure {A'', B''}
  set Γ₀ := Subgroup.closure {nA hz hrel, nB hz hrel}
  -- signs
  have hcomm'' : Subgroup.Commensurable H'' H := by
    have hc := commensurable_signs hA'' hB''
    rw [hcl] at hc
    have hinj := Matrix.SpecialLinearGroup.toGL_injective (n := Fin 2) (R := ℝ)
    exact ⟨by simpa [Subgroup.relIndex_map_map_of_injective _ _ hinj] using hc.1,
      by simpa [Subgroup.relIndex_map_map_of_injective _ _ hinj] using hc.2⟩
  have hcommeq : commensurator H'' = commensurator H := Subgroup.Commensurable.eq hcomm''
  -- conjugation
  set P : Matrix (Fin 2) (Fin 2) ℝ := g.1
  have hP : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
  set φ := SL2R.conjMat P hP
  have hφA : φ A'' = nA hz hrel := by
    apply Subtype.ext
    rw [SL2R.coe_conjMat]
    have := congrArg Units.val hgA
    simpa [P, Matrix.coe_units_inv] using this
  have hφB : φ B'' = nB hz hrel := by
    apply Subtype.ext
    rw [SL2R.coe_conjMat]
    have := congrArg Units.val hgB
    simpa [P, Matrix.coe_units_inv] using this
  have hΓ₀ : Γ₀ = H''.map φ := by
    rw [MonoidHom.map_closure, Set.image_pair, hφA, hφB]
  have hφinj : Function.Injective φ := (SL2R.conjHomeo P hP).injective
  have hφsurj : Function.Surjective φ := (SL2R.conjHomeo P hP).surjective
  have hcommΓ₀ : (commensurator Γ₀ : Set SL(2, ℝ)) = φ '' (commensurator H'' : Set SL(2, ℝ)) := by
    ext w
    obtain ⟨v, rfl⟩ := hφsurj w
    rw [hΓ₀, SetLike.mem_coe, mem_commensurator_map_iff hφinj, Set.mem_image]
    constructor
    · intro hv; exact ⟨v, hv, rfl⟩
    · rintro ⟨u, hu, huv⟩; rwa [← hφinj huv]
  have hdense₀ : Dense (commensurator Γ₀ : Set SL(2, ℝ)) := by
    rw [hcommΓ₀, hcommeq]
    exact (SL2R.conjHomeo P hP).surjective.denseRange.dense_image
      (SL2R.conjHomeo P hP).continuous hdense
  have hint₀ := trace_sq_int_of_dense hz hrel hx hy t1 t2 t3 hdense₀
  -- back to `⟨A, B⟩`
  have hint : ∀ γ ∈ H, ∃ m : ℤ, tr γ ^ 2 = m := by
    intro γ hγ
    have hγ' : γ ∈ Subgroup.closure {A', B'} := hcl ▸ hγ
    have key : ∀ δ ∈ H'', ∃ m : ℤ, tr δ ^ 2 = m := by
      intro δ hδ
      have hφδ : φ δ ∈ Γ₀ := by rw [hΓ₀]; exact Subgroup.mem_map_of_mem φ hδ
      obtain ⟨m, hm⟩ := hint₀ (φ δ) hφδ
      exact ⟨m, by rw [← hm, SL2R.tr_conjMat]⟩
    rcases mem_or_neg_mem_of_signs hA'' hB'' hγ' with h | h
    · exact key γ h
    · obtain ⟨m, hm⟩ := key _ h
      exact ⟨m, by rw [← hm, tr_neg, neg_sq]⟩
  obtain ⟨A₁, B₁, hcl₁, hc₁, hT₁⟩ := takeuchi_one_infty_of_int hcomm hA hint
  exact (isArithmeticSL_iff_isTakeuchiConj hcomm).2
    ⟨A₁, B₁, hcl₁, exists_conj_of_takeuchiSq hc₁ hT₁⟩

end assembly

end OrbicurveCores.M2
