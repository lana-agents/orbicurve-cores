/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.M2.Superrigidity
import OrbicurveCores.Fuchsian.DenseSubgroup

/-!
# M2, part E: unipotent rigidity

Let `Φ : SL(2, ℝ) → PGL(2, k)` be a homomorphism (as an action on `ℙ¹(k)`), `k` of
characteristic `0`, with `Φ(u₂)` the translation `y ↦ y + 2`.

* `root_of_translation`: the only Möbius `m`-th root of `y ↦ y + 2` is `y ↦ y + 2/m`.
* `smul_uU_rat`: hence `Φ(u_q)` is translation by `q` for every rational `q`.
* `padic_contradiction`: over `ℚ_p` this is incompatible with continuity of `g ↦ Φ(g) 0`,
  since `2/pʲ → 0` in `ℝ` but not in `ℚ_p`.
-/

open Filter Topology Set OnePoint OnePoint.Proj
open scoped MatrixGroups

namespace OrbicurveCores.M2

variable {k : Type*} [Field k] [DecidableEq k]

/-- The translation `y ↦ y + b` of `ℙ¹(k)`. -/
def transl (b : k) : GL (Fin 2) k :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, b; 0, 1] (by simp [Matrix.det_fin_two])

lemma transl_smul_coe (b y : k) : transl b • (y : OnePoint k) = ((y + b : k) : OnePoint k) := by
  rw [smul_some_eq_ite]
  simp [transl, add_comm]

lemma transl_smul_infty (b : k) : transl b • (∞ : OnePoint k) = ∞ := by
  rw [smul_infty_eq_self_iff]
  simp [transl]

variable [CharZero k]

/-- **Möbius roots of a translation.** -/
theorem root_of_translation (g : GL (Fin 2) k) {m : ℕ} (hm : 0 < m)
    (h : ∀ y : OnePoint k, (fun z ↦ g • z)^[m] y = transl (2 : k) • y) (y : OnePoint k) :
    g • y = transl (2 / (m : k)) • y := by
  set f : OnePoint k → OnePoint k := fun z ↦ g • z
  -- `f` commutes with the translation, hence fixes `∞`
  have hT : ∀ z, transl (2 : k) • f z = f (transl (2 : k) • z) := by
    intro z
    rw [← h, ← h, ← Function.iterate_succ_apply' f m z, Function.iterate_succ_apply]
  have hfix : ∀ z : k, transl (2 : k) • (z : OnePoint k) ≠ z := by
    intro z hz
    rw [transl_smul_coe, OnePoint.coe_eq_coe] at hz
    have : (2 : k) = 0 := by linear_combination hz
    exact two_ne_zero this
  have hinf : f ∞ = ∞ := by
    have := hT ∞
    rw [transl_smul_infty] at this
    induction h' : f ∞ using OnePoint.rec with
    | infty => rfl
    | coe z => rw [h'] at this; exact absurd this (hfix z)
  have hg10 : g 1 0 = 0 := smul_infty_eq_self_iff.1 hinf
  have hg11 : g 1 1 ≠ 0 := by
    intro h0
    have := g.det_ne_zero
    rw [Matrix.det_fin_two, hg10, h0] at this
    simp at this
  set a := g 0 0 / g 1 1
  set b := g 0 1 / g 1 1
  have hf : ∀ z : k, f z = ((a * z + b : k) : OnePoint k) := by
    intro z
    simp only [f]
    rw [smul_some_eq_ite]
    simp only [hg10, zero_mul, zero_add, hg11, ↓reduceIte, a, b]
    congr 1
    field_simp
  -- iterates
  have hiter : ∀ n : ℕ, ∀ z : k, f^[n] z =
      ((a ^ n * z + b * ∑ i ∈ Finset.range n, a ^ i : k) : OnePoint k) := by
    intro n
    induction n with
    | zero => intro z; simp
    | succ n ih =>
      intro z
      rw [Function.iterate_succ_apply', ih, hf, geom_sum_succ]
      congr 1
      ring
  have e0 := h ((0 : k) : OnePoint k)
  have e1 := h ((1 : k) : OnePoint k)
  rw [hiter, transl_smul_coe, OnePoint.coe_eq_coe] at e0 e1
  set S := ∑ i ∈ Finset.range m, a ^ i
  have ha : a = 1 := by
    by_contra ha
    set y₀ := b / (1 - a)
    have h1a : (1 : k) - a ≠ 0 := sub_ne_zero.2 (Ne.symm ha)
    have hfix0 : f y₀ = y₀ := by
      rw [hf, OnePoint.coe_eq_coe]
      simp only [y₀]; field_simp; ring
    have hit : f^[m] y₀ = y₀ := Function.iterate_fixed hfix0 m
    rw [h] at hit
    exact hfix y₀ hit
  have hS : S = m := by simp [S, ha]
  have hb : b = 2 / m := by
    rw [hS] at e0
    have hm' : (m : k) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
    field_simp
    linear_combination e0
  induction y using OnePoint.rec with
  | infty => rw [transl_smul_infty]; exact hinf
  | coe z => rw [show g • (z : OnePoint k) = f z from rfl, hf, transl_smul_coe, ha, hb, one_mul]

namespace UnipotentRigidity

open SL2R

variable {Φ : SL(2, ℝ) → GL (Fin 2) k}
  (hΦ : ∀ g h : SL(2, ℝ), ∀ y : OnePoint k, Φ (g * h) • y = Φ g • Φ h • y)
include hΦ

omit [CharZero k] in
lemma smul_one' (y : OnePoint k) : Φ 1 • y = y := by
  have := hΦ 1 1 y
  rw [mul_one] at this
  exact ((smul_left_cancel_iff (Φ 1)).1 this).symm

omit [CharZero k] in
lemma smul_pow (g : SL(2, ℝ)) (n : ℕ) (y : OnePoint k) :
    Φ (g ^ n) • y = (fun z ↦ Φ g • z)^[n] y := by
  induction n generalizing y with
  | zero => simp [smul_one' hΦ]
  | succ n ih => rw [pow_succ', hΦ, ih, Function.iterate_succ_apply']

omit [CharZero k] hΦ in
lemma transl_add (s t : k) (y : OnePoint k) : transl (s + t) • y = transl s • transl t • y := by
  induction y using OnePoint.rec with
  | infty => simp [transl_smul_infty]
  | coe z => simp only [transl_smul_coe]; congr 1; ring

omit [CharZero k] hΦ in
lemma uU_pow (t : ℝ) (n : ℕ) : uU t ^ n = uU (n * t) := by
  induction n with
  | zero => ext i j; fin_cases i <;> fin_cases j <;> simp [uU]
  | succ n ih => rw [pow_succ, ih, ← uU_add]; congr 1; push_cast; ring

/-- The property "`Φ(u_t)` is translation by `t`". -/
def IsTransl (Φ : SL(2, ℝ) → GL (Fin 2) k) (t : ℝ) (b : k) : Prop :=
  ∀ y : OnePoint k, Φ (uU t) • y = transl b • y

/-- **Unipotent rigidity.** If `Φ(u₂)` is translation by `2`, then `Φ(u_q)` is translation by `q`
for every rational `q`. -/
theorem smul_uU_rat (h2 : IsTransl Φ 2 2) (q : ℚ) : IsTransl Φ q q := by
  -- `1/d`
  have hd : ∀ d : ℕ, 0 < d → IsTransl Φ (1 / d) (1 / d) := by
    intro d hd0 y
    have hm : 0 < 2 * d := by omega
    have := root_of_translation (k := k) (Φ (uU (1 / d))) hm (fun z ↦ by
      rw [← smul_pow hΦ, uU_pow, ← h2 z]
      congr 3
      push_cast
      field_simp) y
    rw [this]
    congr 2
    push_cast
    field_simp
  -- additivity and negation
  have hadd : ∀ s t (b c : k), IsTransl Φ s b → IsTransl Φ t c → IsTransl Φ (s + t) (b + c) := by
    intro s t b c hs ht y
    rw [uU_add, hΦ, ht, hs, transl_add]
  have hneg : ∀ t (b : k), IsTransl Φ t b → IsTransl Φ (-t) (-b) := by
    intro t b ht y
    have e : ∀ z : OnePoint k, Φ (uU (-t)) • Φ (uU t) • z = z := by
      intro z
      rw [← hΦ, ← uU_add, neg_add_cancel, show uU 0 = 1 by ext i j; fin_cases i <;>
        fin_cases j <;> simp [uU], smul_one' hΦ]
    have := e (transl (-b) • y)
    rw [ht, ← transl_add, add_neg_cancel] at this
    rw [← this]
    congr 1
    induction y using OnePoint.rec with
    | infty => simp [transl_smul_infty]
    | coe z => simp [transl_smul_coe]
  have hnat : ∀ d : ℕ, 0 < d → ∀ n : ℕ, IsTransl Φ (n * (1 / d)) (n * (1 / d)) := by
    intro d hd0 n
    induction n with
    | zero =>
      intro y
      simp only [Nat.cast_zero, zero_mul]
      rw [show uU 0 = 1 by ext i j; fin_cases i <;> fin_cases j <;> simp [uU], smul_one' hΦ]
      induction y using OnePoint.rec with
      | infty => simp [transl_smul_infty]
      | coe z => simp [transl_smul_coe]
    | succ n ih =>
      have := hadd _ _ _ _ ih (hd d hd0)
      convert this using 2 <;> push_cast <;> ring
  have hint : ∀ n : ℤ, IsTransl Φ (n * (1 / q.den)) (n * (1 / q.den)) := by
    intro n
    obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
    · exact_mod_cast hnat q.den q.den_pos m
    · have := hneg _ _ (hnat q.den q.den_pos m)
      convert this using 2 <;> push_cast <;> ring
  have := hint q.num
  convert this using 2
  · rw [Rat.cast_def]; ring
  · rw [Rat.cast_def]; ring

end UnipotentRigidity

lemma tendsto_uU_zero {t : ℕ → ℝ} (ht : Tendsto t atTop (𝓝 0)) :
    Tendsto (fun j ↦ SL2R.uU (t j)) atTop (𝓝 1) := by
  have := (SL2R.continuous_uU.tendsto 0).comp ht
  rwa [show SL2R.uU 0 = 1 by ext i j; fin_cases i <;> fin_cases j <;> simp [SL2R.uU]] at this

open UnipotentRigidity in
/-- **No continuous extension over `ℚ_p`.** A homomorphism `SL(2, ℝ) → PGL(2, ℚ_p)` with
`Φ(u₂)` the translation by `2` cannot have `g ↦ Φ(g) y` continuous. -/
theorem padic_contradiction {p : ℕ} [Fact p.Prime] [DecidableEq ℚ_[p]]
    {Φ : SL(2, ℝ) → GL (Fin 2) ℚ_[p]}
    (hΦ : ∀ g h : SL(2, ℝ), ∀ y : OnePoint ℚ_[p], Φ (g * h) • y = Φ g • Φ h • y)
    (hcont : ∀ y : OnePoint ℚ_[p], Continuous fun g ↦ Φ g • y) (h2 : IsTransl Φ 2 2) :
    False := by
  set q : ℕ → ℚ := fun j ↦ 2 / (p : ℚ) ^ j
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hq : Tendsto (fun j ↦ ((q j : ℚ) : ℝ)) atTop (𝓝 0) := by
    simp only [q, Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow, Rat.cast_natCast]
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (p : ℝ)⁻¹) (by positivity)
      (inv_lt_one_of_one_lt₀ hp)).const_mul 2
    simpa [div_eq_mul_inv, inv_pow] using this
  have hlim := ((hcont ((0 : ℚ_[p]) : OnePoint ℚ_[p])).tendsto 1).comp (tendsto_uU_zero hq)
  simp only [Function.comp_def, smul_one' hΦ] at hlim
  have e : ∀ j, Φ (SL2R.uU ((q j : ℚ) : ℝ)) • ((0 : ℚ_[p]) : OnePoint ℚ_[p]) =
      (((q j : ℚ) : ℚ_[p]) : OnePoint ℚ_[p]) := by
    intro j
    rw [smul_uU_rat hΦ h2 (q j), transl_smul_coe, zero_add]
  simp only [e] at hlim
  have hlim' : Tendsto (fun j ↦ ((q j : ℚ) : ℚ_[p])) atTop (𝓝 0) :=
    (OnePoint.isOpenEmbedding_coe (X := ℚ_[p])).isInducing.tendsto_nhds_iff.2 hlim
  have hn := (continuous_norm.tendsto _).comp hlim'
  simp only [Function.comp_def, norm_zero] at hn
  have h2p : (0 : ℝ) < ‖(2 : ℚ_[p])‖ := norm_pos_iff.2 two_ne_zero
  obtain ⟨j, hj⟩ := (hn.eventually (gt_mem_nhds h2p)).exists
  apply lt_irrefl ‖(2 : ℚ_[p])‖
  calc ‖(2 : ℚ_[p])‖ ≤ ‖(((q j : ℚ) : ℚ_[p]))‖ := by
        simp only [q, Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow, Rat.cast_natCast, norm_div,
          norm_pow, Padic.norm_p]
        rw [inv_pow, div_inv_eq_mul]
        exact le_mul_of_one_le_right (norm_nonneg _) (one_le_pow₀ hp.le)
    _ < ‖(2 : ℚ_[p])‖ := hj

/-! ### The complex case -/

section complex

open UnipotentRigidity

variable [DecidableEq ℂ]

/-- Upper and lower unipotent matrices over `ℂ`. -/
def TU (t : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![1, t; 0, 1]
def TL (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; s, 1]

omit [DecidableEq ℂ] in
lemma det_TU (t : ℂ) : (TU t).det = 1 := by simp [TU, Matrix.det_fin_two]
omit [DecidableEq ℂ] in
lemma det_TL (s : ℂ) : (TL s).det = 1 := by simp [TL, Matrix.det_fin_two]

omit [DecidableEq ℂ] in
lemma conj_TU {G : Matrix (Fin 2) (Fin 2) ℂ} (hG10 : G 1 0 ≠ 0)
    (hdetG : G 0 0 * G 1 1 - G 0 1 * G 1 0 = 1) (t : ℂ) :
    G * TU t * G.adjugate =
      TU (G 0 0 / G 1 0) * TL (-(G 1 0) ^ 2 * t) * TU (-(G 0 0 / G 1 0)) := by
  rw [Matrix.eta_fin_two G, Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · simp [TU, TL]; field_simp; linear_combination hdetG
  · simp [TU, TL]; field_simp; ring
  · simp [TU, TL]; ring
  · simp [TU, TL]; field_simp; linear_combination hdetG

lemma transl_smul_eq_mob (b : ℂ) (y : OnePoint ℂ) : transl b • y = OnePoint.Proj.mob (TU b) y := by
  rw [gl_smul_eq_mob]; rfl

set_option linter.flexible false in
lemma continuous_transl_smul (y : OnePoint ℂ) : Continuous fun t : ℝ ↦ transl (t : ℂ) • y := by
  simp_rw [transl_smul_eq_mob]
  refine continuous_iff_continuousAt.2 fun t ↦ ?_
  have hM : Continuous fun t : ℝ ↦ TU (t : ℂ) := by
    refine continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
    fin_cases i <;> fin_cases j <;> simp only [TU] <;> simp <;> fun_prop
  exact (continuousAt_mob_param hM.continuousAt (by rw [det_TU]; exact one_ne_zero) y).comp
    (f := fun t : ℝ ↦ (t, y)) (by fun_prop)

variable {Φ : SL(2, ℝ) → GL (Fin 2) ℂ}
  (hΦ : ∀ g h : SL(2, ℝ), ∀ y : OnePoint ℂ, Φ (g * h) • y = Φ g • Φ h • y)
  (hcont : ∀ y : OnePoint ℂ, Continuous fun g ↦ Φ g • y) (h2 : IsTransl Φ 2 2)
include hΦ hcont h2

/-- Over `ℂ`, `Φ(u_t)` is translation by `t` for every real `t`. -/
theorem smul_uU_real (t : ℝ) (y : OnePoint ℂ) : Φ (SL2R.uU t) • y = transl (t : ℂ) • y := by
  have h1 : Continuous fun t : ℝ ↦ Φ (SL2R.uU t) • y := (hcont y).comp SL2R.continuous_uU
  have h2' : Continuous fun t : ℝ ↦ transl (t : ℂ) • y := continuous_transl_smul y
  have := h1.ext_on Rat.denseRange_cast h2' (by
    rintro _ ⟨q, rfl⟩
    have := smul_uU_rat hΦ h2 q y
    simpa using this)
  exact congrFun this t

omit hcont h2 in
lemma smul_inv_of_mob {γ : SL(2, ℝ)} {G : Matrix (Fin 2) (Fin 2) ℂ} (hG : G.det ≠ 0)
    (hγ : ∀ y, Φ γ • y = OnePoint.Proj.mob G y) (y : OnePoint ℂ) :
    Φ γ⁻¹ • y = OnePoint.Proj.mob G.adjugate y := by
  have e : Φ γ⁻¹ • Φ γ • (OnePoint.Proj.mob G.adjugate y) = OnePoint.Proj.mob G.adjugate y := by
    rw [← hΦ, inv_mul_cancel, smul_one' hΦ]
  rwa [hγ, mob_mul_adjugate hG] at e

set_option linter.flexible false in
/-- **Complex rigidity.** If `Φ` is a continuous extension over `ℂ` of an action that agrees
with `σ` (an arbitrary ring embedding `ℝ → ℂ`) on some `γ` with `γ₁₀ ≠ 0`, and `Φ(-1) = 1`,
then `σ(γ₁₀)² = γ₁₀²`. -/
theorem complex_rigidity (hneg : ∀ y : OnePoint ℂ, Φ (-1) • y = y) (σ : ℝ →+* ℂ)
    {γ : SL(2, ℝ)}
    (hγ : ∀ y, Φ γ • y = OnePoint.Proj.mob ((γ : Matrix (Fin 2) (Fin 2) ℝ).map σ) y)
    (hr : γ 1 0 ≠ 0) : σ (γ 1 0) ^ 2 = ((γ 1 0 : ℝ) : ℂ) ^ 2 := by
  set r := γ 1 0
  set ξ := γ 0 0 / r
  set G : Matrix (Fin 2) (Fin 2) ℂ := (γ : Matrix (Fin 2) (Fin 2) ℝ).map σ
  have hdetγ : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.2; rw [Matrix.det_fin_two] at this; exact this
  have hG : G.det = 1 := by
    change (σ.mapMatrix (γ : Matrix (Fin 2) (Fin 2) ℝ)).det = 1
    rw [← RingHom.map_det, γ.2, map_one]
  have hGne : G.det ≠ 0 := by rw [hG]; exact one_ne_zero
  have hσr : σ r ≠ 0 := by
    intro h; apply hr; exact σ.injective (by rw [h, map_zero])
  -- `u_L(-1) = u(-ξ) γ u(1/r²) γ⁻¹ u(ξ)`
  have hid : SL2R.uL (-1) = SL2R.uU (-ξ) * γ * SL2R.uU (1 / r ^ 2) * γ⁻¹ * SL2R.uU ξ := by
    have hm : (γ : Matrix (Fin 2) (Fin 2) ℝ) = !![γ 0 0, γ 0 1; γ 1 0, γ 1 1] :=
      Matrix.eta_fin_two _
    ext i j
    simp only [SL2R.uL, SL2R.uU, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    rw [hm]
    simp only [Matrix.mul_fin_two]
    have hr' : (γ : Matrix (Fin 2) (Fin 2) ℝ) 1 0 ≠ 0 := hr
    fin_cases i <;> fin_cases j <;> simp [ξ, r] <;> field_simp <;>
      first
        | ring1
        | linear_combination hdetγ
        | linear_combination -hdetγ
        | linear_combination (γ 0 0) * hdetγ
        | linear_combination -(γ 0 0) * hdetγ
        | linear_combination (γ 1 1) * hdetγ
        | linear_combination -(γ 1 1) * hdetγ
        | linear_combination (γ 1 0) * hdetγ
        | linear_combination -(γ 1 0) * hdetγ
  -- matrix identities over `ℂ`
  have hTU : ∀ a b : ℂ, TU a * TU b = TU (a + b) := by
    intro a b; ext i j; fin_cases i <;> fin_cases j <;> simp [TU]; ring
  have hconj : ∀ t : ℂ, G * TU t * G.adjugate =
      TU (G 0 0 / G 1 0) * TL (-(G 1 0) ^ 2 * t) * TU (-(G 0 0 / G 1 0)) := fun t ↦
    conj_TU (by simpa [G] using hσr) (by rw [← Matrix.det_fin_two]; exact hG) t
  have hG10 : G 1 0 = σ r := rfl
  have hG00 : G 0 0 = σ (γ 0 0) := rfl
  set d : ℂ := G 0 0 / G 1 0 - (ξ : ℂ)
  set b : ℂ := -(G 1 0) ^ 2 * ((1 / r ^ 2 : ℝ) : ℂ)
  have hTUdet : ∀ a : ℂ, (TU a).det ≠ 0 := fun a ↦ by rw [det_TU]; exact one_ne_zero
  have hTLdet : ∀ a : ℂ, (TL a).det ≠ 0 := fun a ↦ by rw [det_TL]; exact one_ne_zero
  have hadj : G.adjugate.det ≠ 0 := by rw [Matrix.det_adjugate]; simpa using hGne
  have hU : ∀ (t : ℝ) (y : OnePoint ℂ), Φ (SL2R.uU t) • y = OnePoint.Proj.mob (TU t) y :=
    fun t y ↦ by rw [smul_uU_real hΦ hcont h2, transl_smul_eq_mob]
  -- `Φ(u_L(-1))`
  obtain ⟨M₁, hM₁def⟩ : ∃ M, M = TU (-(ξ : ℂ)) * G * TU ((1 / r ^ 2 : ℝ) : ℂ) * G.adjugate *
      TU (ξ : ℂ) := ⟨_, rfl⟩
  have hL : ∀ y, Φ (SL2R.uL (-1)) • y = OnePoint.Proj.mob M₁ y := by
    intro y
    rw [hid, hΦ, hΦ, hΦ, hΦ, hU, hγ, hU, smul_inv_of_mob hΦ hGne hγ, hU, hM₁def]
    rw [mob_mul (hTUdet _), mob_mul hadj, mob_mul (hTUdet _), mob_mul hGne]
    push_cast
    rfl
  have hM₁ : M₁ = TU d * TL b * TU (-d) := by
    simp only [hM₁def, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc G, ← Matrix.mul_assoc (G * TU _), hconj]
    simp only [← Matrix.mul_assoc, hTU]
    simp only [Matrix.mul_assoc, hTU]
    simp only [d, b]
    congr 2 <;> ring
  -- the Weyl element
  set W := SL2R.uU 1 * SL2R.uL (-1) * SL2R.uU 1
  have hW : W * W = -1 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [W, SL2R.uU, SL2R.uL]
  have hM1det : M₁.det ≠ 0 := by
    rw [hM₁, Matrix.det_mul, Matrix.det_mul, det_TU, det_TL, det_TU]; norm_num
  obtain ⟨N, hNdef⟩ : ∃ N, N = TU 1 * M₁ * TU 1 := ⟨_, rfl⟩
  have hN : ∀ y, Φ W • y = OnePoint.Proj.mob N y := by
    intro y
    simp only [W]
    rw [hΦ, hΦ, hU, hL, hU, hNdef, mob_mul (hTUdet 1), mob_mul hM1det]
    push_cast
    rfl
  have hNdet : N.det ≠ 0 := by
    rw [hNdef, hM₁, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul,
      det_TU, det_TL, det_TU, det_TU]; norm_num
  have hNN : ∀ y, OnePoint.Proj.mob (N * N) y = y := by
    intro y
    rw [mob_mul hNdet, ← hN, ← hN, ← hΦ, hW, hneg]
  have hsc := scalar_of_three_fixed (x := ((0 : ℂ) : OnePoint ℂ)) (y := ((1 : ℂ) : OnePoint ℂ))
    (z := ∞) (by rw [Matrix.det_mul]; exact mul_ne_zero hNdet hNdet) (by simp) (by simp)
    (by simp) (hNN _) (hNN _) (hNN _)
  have h10 := congrFun (congrFun hsc 1) 0
  simp only [Matrix.smul_apply, Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide),
    smul_zero] at h10
  have hNe : N = TU (1 + d) * TL b * TU (1 - d) := by
    simp only [hNdef, hM₁, ← Matrix.mul_assoc, hTU]
    simp only [Matrix.mul_assoc, hTU]
    congr 2; ring
  rw [hNe] at h10
  simp [TU, TL] at h10
  have hb : b ≠ 0 := by
    simp only [b]
    refine mul_ne_zero (neg_ne_zero.2 (pow_ne_zero _ (by rw [hG10]; exact hσr))) ?_
    exact_mod_cast (one_div_ne_zero (pow_ne_zero 2 hr))
  have hb' : b = -1 := by
    have : b * (2 + 2 * b) = 0 := by linear_combination h10
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hb
    · linear_combination h / 2
  simp only [b, hG10] at hb'
  have hr2 : ((r : ℝ) : ℂ) ^ 2 ≠ 0 := by exact_mod_cast pow_ne_zero 2 hr
  push_cast at hb'
  rw [neg_mul, neg_inj, one_div, ← div_eq_mul_inv, div_eq_one_iff_eq hr2] at hb'
  exact hb'

end complex

end OrbicurveCores.M2
