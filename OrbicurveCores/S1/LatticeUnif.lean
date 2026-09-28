/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.S1.Arith
import OrbicurveCores.S1.Rational
import OrbicurveCores.Classification

/-!
# From a Belyi certificate to a Takeuchi uniformisation

For an elliptic curve `W : y² = f(x)` over `ℂ` (`a₁ = a₃ = 0`) and a Belyi certificate
`RatCert f N D H K R c`, the uniformising group of `W ∖ O` is Takeuchi (`exists_takeuchi`).

* `uniformizes_unif`: oka's uniformisation `ψ : ℍ → ℂ ∖ Λ` of the lattice curve `E_τ ≅ W` gives
  `Uniformizes W A B` for the edge pairings `A, B` of `ψ` (the argument of
  `Uniformization.uniformization_oncePunctured`, keeping track of `ψ`);
* `mem_twoTorsionX_iff`: the `x`-coordinates `u⁻² (℘(v) − r)` of the `2`-torsion are the roots of
  `f`;
* `exists_takeuchi`: `F(u) = G(u⁻² (℘(u/2) − r))` is a `2Λ`-periodic orbifold covering of the
  `j`-line (`EllOrbStatement`), so the squared traces are integral (`int_sq_traces`) and the group
  is Takeuchi.
-/

open Complex Metric Set Filter Topology Uniformization Uniformization.Generators
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups

namespace OrbicurveCores.S1

variable (τ₀ : ℍ) (C : WeierstrassCurve.VariableChange ℂ)

/-- The coordinate change from the lattice curve `E_τ₀` to `C • E_τ₀`. -/
noncomputable def vcT (P : ℂ × ℂ) : ℂ × ℂ :=
  ((C.u : ℂ)⁻¹ ^ 2 * (P.1 - C.r), (C.u : ℂ)⁻¹ ^ 3 * (P.2 - C.s * (P.1 - C.r) - C.t))

lemma vcT_equation_iff (X Y : ℂ) :
    (C • Heights.latticeWeierstrassCurve τ₀).toAffine.Equation (vcT C (X, Y)).1 (vcT C (X, Y)).2 ↔
      (Heights.latticeWeierstrassCurve τ₀).toAffine.Equation X Y := by
  have hu : (C.u : ℂ) ≠ 0 := C.u.ne_zero
  rw [WeierstrassCurve.variableChange_equation_iff]
  have e1 : (C.u : ℂ) ^ 2 * ((C.u : ℂ)⁻¹ ^ 2 * (X - C.r)) + C.r = X := by field_simp; ring
  have e2 : (C.u : ℂ) ^ 3 * ((C.u : ℂ)⁻¹ ^ 3 * (Y - C.s * (X - C.r) - C.t)) +
      (C.u : ℂ) ^ 2 * C.s * ((C.u : ℂ)⁻¹ ^ 2 * (X - C.r)) + C.t = Y := by
    field_simp; ring
  simp only [vcT]; rw [e1, e2]

lemma vcT_injective : Function.Injective (vcT C) := by
  have hu : (C.u : ℂ) ≠ 0 := C.u.ne_zero
  rintro ⟨X, Y⟩ ⟨X', Y'⟩ h
  simp only [vcT, Prod.mk.injEq] at h
  have hX : X = X' := by
    have := h.1; field_simp at this; linear_combination this
  subst hX
  have := h.2; field_simp at this
  exact Prod.ext rfl (by linear_combination this)

/-- **The uniformisation of `C • E_τ₀` by the edge pairings of oka's `ψ`.** -/
theorem uniformizes_unif :
    Uniformizes (C • Heights.latticeWeierstrassCurve τ₀) (A (unifOf (Lt τ₀)))
      (B (unifOf (Lt τ₀))) := by
  set U := unifOf (Lt τ₀)
  have hu : (C.u : ℂ) ≠ 0 := C.u.ne_zero
  set W := C • Heights.latticeWeierstrassCurve τ₀
  set π : ℂ → ℂ × ℂ := fun z ↦ vcT C (wpt τ₀ (U.Ψ z))
  have hΨ : ∀ z : ℍ, U.Ψ z ∉ (Lt τ₀).lattice := fun z ↦ U.notMem z z.im_pos
  refine ⟨π, ?_, ?_, ?_, ?_⟩
  · -- holomorphic with nonvanishing derivative
    intro z
    have hz : 0 < (z : ℂ).im := z.im_pos
    have hΨd : HasDerivAt U.Ψ (deriv U.Ψ z) z :=
      (U.differentiableOn.differentiableAt (isOpen_upper.mem_nhds hz)).hasDerivAt
    set w := U.Ψ z
    have hw := hΨ z
    set u : ℂ := (C.u : ℂ)
    set r := C.r; set s := C.s; set t := C.t
    have h1 : HasDerivAt (fun z ↦ u⁻¹ ^ 2 * ((Lt τ₀).weierstrassP (U.Ψ z) - r))
        (u⁻¹ ^ 2 * ((Lt τ₀).derivWeierstrassP w * deriv U.Ψ z)) z :=
      (((hasDerivAt_wp τ₀ hw).comp _ hΨd).sub_const r).const_mul _
    have h2 : HasDerivAt (fun z ↦ u⁻¹ ^ 3 * ((Lt τ₀).derivWeierstrassP (U.Ψ z) / 2 -
        s * ((Lt τ₀).weierstrassP (U.Ψ z) - r) - t))
        (u⁻¹ ^ 3 * (deriv (Lt τ₀).derivWeierstrassP w * deriv U.Ψ z / 2 -
          s * ((Lt τ₀).derivWeierstrassP w * deriv U.Ψ z))) z :=
      (((((hasDerivAt_wp' τ₀ hw).comp _ hΨd).div_const 2).sub
        ((((hasDerivAt_wp τ₀ hw).comp _ hΨd).sub_const r).const_mul s)).sub_const t).const_mul _
    have hπ : HasDerivAt π (u⁻¹ ^ 2 * ((Lt τ₀).derivWeierstrassP w * deriv U.Ψ z),
        u⁻¹ ^ 3 * (deriv (Lt τ₀).derivWeierstrassP w * deriv U.Ψ z / 2 -
          s * ((Lt τ₀).derivWeierstrassP w * deriv U.Ψ z))) z := h1.prodMk h2
    refine ⟨hπ.differentiableAt, ?_⟩
    rw [hπ.deriv]
    intro h0
    simp only [Prod.mk_eq_zero] at h0
    obtain ⟨h01, h02⟩ := h0
    have hd := U.deriv_ne_zero z hz
    have hu2 : u⁻¹ ^ 2 ≠ 0 := by simp [hu, u]
    have hu3 : u⁻¹ ^ 3 ≠ 0 := by simp [hu, u]
    have hp1 : (Lt τ₀).derivWeierstrassP w = 0 := by
      rcases mul_eq_zero.mp h01 with h | h
      · exact absurd h hu2
      · rcases mul_eq_zero.mp h with h | h
        · exact h
        · exact absurd h hd
    rw [hp1] at h02
    have : deriv (Lt τ₀).derivWeierstrassP w = 0 := by
      rcases mul_eq_zero.mp h02 with h | h
      · exact absurd h hu3
      · simp only [zero_mul, mul_zero, sub_zero, div_eq_zero_iff, mul_eq_zero] at h
        rcases h with (h | h) | h
        · exact h
        · exact absurd h hd
        · norm_num at h
    exact not_deriv_deriv_eq_zero τ₀ hw hp1 this
  · -- points of `W`
    intro z
    exact (vcT_equation_iff τ₀ C _ _).mpr (wpt_equation τ₀ (hΨ z))
  · -- onto the affine points
    intro x y hxy
    set X := (C.u : ℂ) ^ 2 * x + C.r
    set Y := (C.u : ℂ) ^ 3 * y + (C.u : ℂ) ^ 2 * C.s * x + C.t
    have hTXY : vcT C (X, Y) = (x, y) := by
      simp only [vcT, X, Y, Prod.mk.injEq]
      constructor <;> field_simp <;> ring
    have hE : (Heights.latticeWeierstrassCurve τ₀).toAffine.Equation X Y := by
      rw [← vcT_equation_iff τ₀ C, hTXY]; exact hxy
    obtain ⟨z₀, hz₀, hwz⟩ := exists_wpt_eq τ₀ hE
    obtain ⟨z, hz⟩ := U.surj z₀ hz₀
    exact ⟨z, by simp only [π]; rw [hz, hwz, hTXY]⟩
  · -- the fibres are the orbits of `⟨A, B⟩`
    intro z w
    have key : π z = π w ↔ U.ψ w - U.ψ z ∈ (Lt τ₀).lattice := by
      constructor
      · intro h
        exact (wpt_eq_iff τ₀ (hΨ w) (hΨ z)).mp (vcT_injective C h.symm)
      · intro h
        simp only [π]
        rw [(wpt_eq_iff τ₀ (hΨ z) (hΨ w)).mpr (by
          have := neg_mem h; rwa [neg_sub] at this)]
    rw [key]
    have hHAB : ∀ g ∈ H U, ∃ h ∈ Subgroup.closure {A U, B U}, ∀ σ : ℍ, h • σ = g • σ := by
      intro g hg
      induction hg using Subgroup.closure_induction with
      | mem g hg =>
        simp only [mem_insert_iff, mem_singleton_iff] at hg
        rcases hg with rfl | rfl | rfl
        · exact ⟨A U, Subgroup.subset_closure (by simp), fun σ ↦ rfl⟩
        · exact ⟨B U, Subgroup.subset_closure (by simp), fun σ ↦ rfl⟩
        · exact ⟨1, one_mem _, fun σ ↦ by rw [one_smul, neg_one_smul']⟩
      | one => exact ⟨1, one_mem _, fun σ ↦ rfl⟩
      | mul g₁ g₂ _ _ ih₁ ih₂ =>
        obtain ⟨h₁, hh₁, e₁⟩ := ih₁
        obtain ⟨h₂, hh₂, e₂⟩ := ih₂
        exact ⟨h₁ * h₂, mul_mem hh₁ hh₂, fun σ ↦ by rw [mul_smul, mul_smul, e₂, e₁]⟩
      | inv g _ ih =>
        obtain ⟨h, hh, e⟩ := ih
        refine ⟨h⁻¹, inv_mem hh, fun σ ↦ ?_⟩
        have := e (g⁻¹ • σ)
        rw [smul_inv_smul] at this
        rw [inv_smul_eq_iff, this]
    have hABΓ : Subgroup.closure {A U, B U} ≤ U.deckGroup := by
      rw [Subgroup.closure_le]
      intro g hg
      simp only [mem_insert_iff, mem_singleton_iff] at hg
      rcases hg with rfl | rfl
      exacts [A_mem U, B_mem U]
    constructor
    · intro h
      obtain ⟨g, hg, hgz⟩ := U.exists_mem_deckGroup h
      obtain ⟨h', hh', e⟩ := hHAB g (deckGroup_le U hg)
      exact ⟨h', hh', by rw [e, hgz]⟩
    · rintro ⟨γ, hγ, rfl⟩
      exact U.smul_mem_iff (hABΓ hγ) z

lemma tr_commutator_unif :
    tr (A (unifOf (Lt τ₀)) * B (unifOf (Lt τ₀)) * (A (unifOf (Lt τ₀)))⁻¹ *
      (B (unifOf (Lt τ₀)))⁻¹) = -2 := by
  set U := unifOf (Lt τ₀)
  change Matrix.trace _ = _
  rw [← trSL_eq_trace, show A U * B U * (A U)⁻¹ * (B U)⁻¹ =
    (A U * B U) * ((A U)⁻¹ * (B U)⁻¹) by group, trSL_mul_comm, ← Peripheral.trace_Cm U,
    Peripheral.Cm]
  congr 1; group

lemma tr_A_unif_ne_zero : tr (A (unifOf (Lt τ₀))) ≠ 0 := by
  change Matrix.trace _ ≠ 0
  rw [← trSL_eq_trace]; exact Peripheral.trSL_A_ne_zero _

end OrbicurveCores.S1
