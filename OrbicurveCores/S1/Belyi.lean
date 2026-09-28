/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.S1.LatticeUnif
import OrbicurveCores.S1.EllOrb
import OrbicurveCores.S1.OrbLift

/-!
# A Belyi certificate makes the uniformising group Takeuchi

`exists_takeuchi`: if the elliptic curve `W : y² = f(x)` over `ℂ` carries a Belyi certificate
`RatCert f N D H K R c`, then `W ∖ O` is uniformised by a Takeuchi group.
-/

open Complex Metric Set Filter Topology Uniformization Uniformization.Generators
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups

namespace OrbicurveCores.S1

/-- The `2`-torsion `x`-coordinates of `C • E_τ₀` (with `a₁ = a₃ = 0`) are the roots of its
cubic. -/
lemma mem_twoTorsionX_iff (τ₀ : ℍ) (C : WeierstrassCurve.VariableChange ℂ)
    (h1 : (C • Heights.latticeWeierstrassCurve τ₀).a₁ = 0)
    (h3 : (C • Heights.latticeWeierstrassCurve τ₀).a₃ = 0) (x : ℂ) :
    x ∈ twoTorsionX τ₀ ((C.u : ℂ)⁻¹ ^ 2) (-(C.u : ℂ)⁻¹ ^ 2 * C.r) ↔
      (C • Heights.latticeWeierstrassCurve τ₀).toAffine.Equation x 0 := by
  have hu : (C.u : ℂ) ≠ 0 := C.u.ne_zero
  have hs : C.s = 0 := by
    simp only [WeierstrassCurve.variableChange_a₁, Heights.latticeWeierstrassCurve_a₁,
      zero_add, mul_eq_zero, Units.ne_zero, false_or] at h1
    simpa using h1
  have ht : C.t = 0 := by
    simp only [WeierstrassCurve.variableChange_a₃, Heights.latticeWeierstrassCurve_a₃,
      Heights.latticeWeierstrassCurve_a₁, mul_zero, zero_add, add_zero, mul_eq_zero,
      pow_eq_zero_iff, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      Units.ne_zero, false_or] at h3
    simpa using h3
  set L := Heights.periodPairOfUpperHalfPlane τ₀
  constructor
  · rintro ⟨v, ⟨hv2, hv⟩, rfl⟩
    have hd : L.derivWeierstrassP v = 0 := by
      have h2 : v = -v + (2 • v) := by rw [two_nsmul]; ring
      have := L.derivWeierstrassP_add_coe (-v) ⟨2 • v, hv2⟩
      rw [← h2, L.derivWeierstrassP_neg] at this
      linear_combination this / 2
    have hE := (vcT_equation_iff τ₀ C (L.weierstrassP v) (L.derivWeierstrassP v / 2)).mpr
      (wpt_equation τ₀ hv)
    simp only [vcT, hd, hs, ht, zero_div, zero_mul, sub_zero, mul_zero] at hE
    convert hE using 1
    ring
  · intro hx
    set X₀ := (C.u : ℂ) ^ 2 * x + C.r
    have hTX : vcT C (X₀, 0) = (x, 0) := by
      simp only [vcT, X₀, hs, ht, Prod.mk.injEq]
      constructor
      · field_simp; ring
      · ring
    have hE : (Heights.latticeWeierstrassCurve τ₀).toAffine.Equation X₀ 0 := by
      rw [← vcT_equation_iff τ₀ C, hTX]; exact hx
    obtain ⟨z, hz, hwz⟩ := exists_wpt_eq τ₀ hE
    simp only [wpt, Prod.mk.injEq] at hwz
    have hd : L.derivWeierstrassP z = 0 := by linear_combination 2 * hwz.2
    refine ⟨z, ⟨?_, hz⟩, ?_⟩
    · rw [two_nsmul]; exact add_self_mem_of_derivWeierstrassP_eq_zero L hz hd
    · change (C.u : ℂ)⁻¹ ^ 2 * L.weierstrassP z + -(C.u : ℂ)⁻¹ ^ 2 * C.r = x
      rw [hwz.1]; simp only [X₀]; field_simp; ring

/-- **A Belyi certificate makes the uniformising group Takeuchi.** -/
theorem exists_takeuchi (hJ : JOrbStatement) {f N D H K R : Polynomial ℂ} {c : ℂ}
    (hc : RatCert f N D H K R c) (W : WeierstrassCurve ℂ) [W.IsElliptic] (h1 : W.a₁ = 0)
    (h3 : W.a₃ = 0) (hf : ∀ x, f.eval x = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) :
    ∃ A B : SL(2, ℝ), Uniformizes W A B ∧ IsTakeuchiConj A B := by
  obtain ⟨τ₀, hτ₀⟩ := Heights.modularJ_surjective W.j
  obtain ⟨C, rfl⟩ := WeierstrassCurve.exists_variableChange_of_j_eq
    (Heights.latticeWeierstrassCurve τ₀) W (by rw [Heights.latticeWeierstrassCurve_j, hτ₀])
  set W := C • Heights.latticeWeierstrassCurve τ₀
  set a : ℂ := (C.u : ℂ)⁻¹ ^ 2
  set r : ℂ := -(C.u : ℂ)⁻¹ ^ 2 * C.r
  have ha : a ≠ 0 := by simp [a, C.u.ne_zero]
  have hZ : twoTorsionX τ₀ a r = {x | f.eval x = 0} := by
    ext x
    rw [mem_twoTorsionX_iff τ₀ C h1 h3, WeierstrassCurve.Affine.equation_iff, mem_setOf_eq,
      hf, h1, h3]
    constructor <;> intro h <;> linear_combination -h
  obtain ⟨hFo, hFl⟩ := ellOrbStatement τ₀ a r hc.G ha (by rw [hZ]; exact hc.differentiableOn)
    (fun x hx ↦ hc.hasLocalForm (by rw [hZ] at hx; exact hx))
    (fun w ↦ (hc.finite_fiber w).subset fun x ⟨hx, hGx⟩ ↦ ⟨by rw [hZ] at hx; exact hx, hGx⟩)
    (fun w ↦ by
      obtain ⟨x, hx, hGx⟩ := hc.surj w
      exact ⟨x, by rw [hZ]; exact hx, hGx⟩)
    (fun z hz ↦ hc.tendsto_nhdsNE (by rw [hZ] at hz; exact hz)) hc.tendsto_cobounded
  have hFp : ∀ u, ∀ l ∈ (Heights.periodPairOfUpperHalfPlane τ₀).lattice,
      hc.G (ellX τ₀ a r (u + 2 * l)) = hc.G (ellX τ₀ a r u) := by
    intro u l hl
    simp only [ellX]
    rw [show (u + 2 * l) / 2 = u / 2 + l by ring,
      (Heights.periodPairOfUpperHalfPlane τ₀).weierstrassP_add_coe (u / 2) ⟨l, hl⟩]
  have hint := int_sq_traces orbLiftStatement hJ τ₀ hFo hFl hFp
  obtain ⟨A', B', hcl, hc', hT⟩ :=
    takeuchi_one_infty_of_int (tr_commutator_unif τ₀) (tr_A_unif_ne_zero τ₀) hint
  obtain ⟨i, A'', hA'', B'', hB'', g, hgA, hgB⟩ := exists_conj_of_takeuchiSq hc' hT
  exact ⟨_, _, uniformizes_unif τ₀ C, A', B', hcl, i, A'', hA'', B'', hB'', g, hgA, hgB⟩

end OrbicurveCores.S1
