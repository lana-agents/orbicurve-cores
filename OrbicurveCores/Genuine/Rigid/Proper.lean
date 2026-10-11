/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.Genuine.Rigid.Basic

/-!
# U2c6: properness of the uniformisation modulo `Γ`

For a uniformisation `π : ℍ → E(ℂ) ∖ 0` with group `Γ`:

* `UnifProps.exists_dist_lt_imp`: `π` maps every neighbourhood of `z` onto a neighbourhood of
  `π z` in the affine curve (the curve is locally a graph over `x` or over `y`, and `π₁`, resp.
  `π₂`, has nonzero derivative there);
* `UnifProps.exists_isCompact`: the points `z` with `‖π z‖ ≤ R` lie in `Γ · C` for a compact
  `C ⊆ ℍ`.
-/

open Complex Metric Set Filter Topology UpperHalfPlane
open scoped MatrixGroups

namespace OrbicurveCores.Rigid

variable {E : WeierstrassCurve ℂ} {A B : SL(2, ℝ)} {π : ℂ → ℂ × ℂ}

/-- A holomorphic function with nonzero derivative at `z ∈ ℍ` has, for every neighbourhood `N` of
`z`, a local section with values in `N` along which a given function continuous at `z` stays
close to its value at `z`. -/
lemma exists_section_nhds {f g : ℂ → ℂ} {z : ℍ} (hf : AnalyticAt ℂ f z) (hd : deriv f z ≠ 0)
    {N : Set ℍ} (hN : N ∈ 𝓝 z) (hg : ContinuousAt g z) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ t, dist t (f z) < δ → ∃ w ∈ N, f w = t ∧ dist (g w) (g z) < η := by
  obtain ⟨ε, hε, s, hsc, hsf, hs0⟩ := Uniformization.exists_localSection hf.hasStrictDerivAt hd
  have hsa : ContinuousAt s (f z) := hsc.continuousAt (isOpen_ball.mem_nhds (mem_ball_self hε))
  have hN' : ((↑) : ℍ → ℂ) '' N ∈ 𝓝 (z : ℂ) := by
    rw [← isOpenEmbedding_coe.map_nhds_eq z]; exact image_mem_map hN
  have hg' : g ⁻¹' ball (g z) η ∈ 𝓝 (z : ℂ) := hg.preimage_mem_nhds (ball_mem_nhds _ hη)
  have h := hsa.preimage_mem_nhds (by rw [hs0]; exact inter_mem hN' hg')
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (inter_mem h (ball_mem_nhds _ hε))
  refine ⟨δ, hδ, fun t ht ↦ ?_⟩
  obtain ⟨⟨⟨w, hwN, hws⟩, hgw⟩, htε⟩ := hball ht
  refine ⟨w, hwN, ?_, ?_⟩
  · rw [hws]; exact hsf t htε
  · rw [hws]; exact hgw

lemma UnifProps.analyticAt_fst (hπ : UnifProps E A B π) (z : ℍ) :
    AnalyticAt ℂ (fun w ↦ (π w).1) z :=
  DifferentiableOn.analyticAt (s := {w : ℂ | 0 < w.im})
    (fun w hw ↦ ((hπ.diff ⟨w, hw⟩).1.fst).differentiableWithinAt)
    ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds z.im_pos)

lemma UnifProps.analyticAt_snd (hπ : UnifProps E A B π) (z : ℍ) :
    AnalyticAt ℂ (fun w ↦ (π w).2) z :=
  DifferentiableOn.analyticAt (s := {w : ℂ | 0 < w.im})
    (fun w hw ↦ ((hπ.diff ⟨w, hw⟩).1.snd).differentiableWithinAt)
    ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds z.im_pos)

lemma UnifProps.deriv_eq (hπ : UnifProps E A B π) (z : ℍ) :
    deriv π z = (deriv (fun w ↦ (π w).1) z, deriv (fun w ↦ (π w).2) z) := by
  have hd := (hπ.diff z).1.hasDerivAt
  have hfst : HasDerivAt (fun w ↦ (π w).1) (deriv π z).1 z :=
    (ContinuousLinearMap.fst ℂ ℂ ℂ).hasFDerivAt.comp_hasDerivAt _ hd
  have hsnd : HasDerivAt (fun w ↦ (π w).2) (deriv π z).2 z :=
    (ContinuousLinearMap.snd ℂ ℂ ℂ).hasFDerivAt.comp_hasDerivAt _ hd
  rw [hfst.deriv, hsnd.deriv]

/-- Differentiating the Weierstrass equation along `π`: `W_Y y' + W_X x' = 0`. -/
lemma UnifProps.deriv_relation (hπ : UnifProps E A B π) (z : ℍ) :
    (2 * (π z).2 + E.a₁ * (π z).1 + E.a₃) * deriv (fun w ↦ (π w).2) z +
      (E.a₁ * (π z).2 - (3 * (π z).1 ^ 2 + 2 * E.a₂ * (π z).1 + E.a₄)) *
        deriv (fun w ↦ (π w).1) z = 0 := by
  set X := fun w ↦ (π w).1
  set Y := fun w ↦ (π w).2
  have hX := (hπ.analyticAt_fst z).differentiableAt.hasDerivAt
  have hY := (hπ.analyticAt_snd z).differentiableAt.hasDerivAt
  set G : ℂ → ℂ := fun w ↦ Y w ^ 2 + E.a₁ * X w * Y w + E.a₃ * Y w -
    (X w ^ 3 + E.a₂ * X w ^ 2 + E.a₄ * X w + E.a₆)
  have hG : HasDerivAt G ((2 * Y z + E.a₁ * X z + E.a₃) * deriv Y z +
      (E.a₁ * Y z - (3 * X z ^ 2 + 2 * E.a₂ * X z + E.a₄)) * deriv X z) z := by
    have := ((((hY.pow 2).add ((hX.const_mul E.a₁).mul hY)).add (hY.const_mul E.a₃)).sub
      ((((hX.pow 3).add ((hX.pow 2).const_mul E.a₂)).add (hX.const_mul E.a₄)).add_const E.a₆))
    refine this.congr_deriv ?_
    ring
  have h0 : G =ᶠ[𝓝 (z : ℂ)] fun _ ↦ 0 := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds z.im_pos] with w hw
    have := hπ.eqn ⟨w, hw⟩
    rw [WeierstrassCurve.Affine.equation_iff'] at this
    exact this
  have := hG.deriv.symm.trans (h0.deriv_eq.trans (deriv_const _ _))
  exact this

/-- **`π` is open onto the curve**: points of the affine curve close to `π z` are images of
points of any given neighbourhood of `z`. -/
lemma UnifProps.exists_dist_lt_imp [E.IsElliptic] (hπ : UnifProps E A B π) (z : ℍ) {N : Set ℍ}
    (hN : N ∈ 𝓝 z) : ∃ ε > 0, ∀ x y : ℂ, E.toAffine.Equation x y →
      dist (x, y) (π z) < ε → ∃ w ∈ N, π w = (x, y) := by
  set x₀ := (π z).1
  set y₀ := (π z).2
  have hns := (WeierstrassCurve.Affine.equation_iff_nonsingular (W := E.toAffine)).mp (hπ.eqn z)
  rw [WeierstrassCurve.Affine.nonsingular_iff'] at hns
  have hrel := hπ.deriv_relation z
  have hd0 := (hπ.diff z).2
  rw [hπ.deriv_eq z] at hd0
  have hXc : ContinuousAt (fun w ↦ (π w).1) z := (hπ.analyticAt_fst z).continuousAt
  have hYc : ContinuousAt (fun w ↦ (π w).2) z := (hπ.analyticAt_snd z).continuousAt
  by_cases hWY : 2 * y₀ + E.a₁ * x₀ + E.a₃ = 0
  · -- the curve is a graph over `y`; `π₂` has nonzero derivative
    have hWX : E.a₁ * y₀ - (3 * x₀ ^ 2 + 2 * E.a₂ * x₀ + E.a₄) ≠ 0 := by
      rcases hns.2 with h | h
      · exact h
      · exact absurd hWY h
    have hY' : deriv (fun w ↦ (π w).2) z ≠ 0 := by
      intro h
      apply hd0
      rw [hWY, h, zero_mul, zero_add, mul_eq_zero] at hrel
      rw [h, hrel.resolve_left hWX]; rfl
    set Φ : ℂ × ℂ × ℂ → ℂ := fun q ↦ q.1 ^ 2 + q.1 * q.2.1 + q.2.1 ^ 2 + E.a₂ * (q.1 + q.2.1) +
      E.a₄ - E.a₁ * q.2.2
    have hΦc : Continuous Φ := by fun_prop
    have hΦ0 : Φ (x₀, x₀, y₀) ≠ 0 := by
      intro h; apply hWX; simp only [Φ] at h; linear_combination -h
    obtain ⟨η, hη, hηΦ⟩ := Metric.eventually_nhds_iff.mp
      (hΦc.continuousAt.eventually_ne hΦ0)
    obtain ⟨δ, hδ, hsec⟩ := exists_section_nhds (hπ.analyticAt_snd z) hY' hN hXc hη
    refine ⟨min δ η, lt_min hδ hη, fun x y hxy hdist ↦ ?_⟩
    rw [Prod.dist_eq, max_lt_iff] at hdist
    obtain ⟨w, hwN, hwy, hwx⟩ := hsec y (hdist.2.trans_le (min_le_left _ _))
    refine ⟨w, hwN, Prod.ext ?_ hwy⟩
    have hw := hπ.eqn w
    rw [WeierstrassCurve.Affine.equation_iff] at hw hxy
    have hΦw : Φ (x, (π w).1, y) ≠ 0 := by
      apply hηΦ
      rw [Prod.dist_eq, Prod.dist_eq, max_lt_iff, max_lt_iff]
      exact ⟨hdist.1.trans_le (min_le_right _ _), hwx, hdist.2.trans_le (min_le_right _ _)⟩
    have key : (x - (π w).1) * Φ (x, (π w).1, y) = 0 := by
      simp only [Φ]; rw [hwy] at hw; linear_combination hw - hxy
    exact (sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_right hΦw)).symm
  · -- the curve is a graph over `x`; `π₁` has nonzero derivative
    have hX' : deriv (fun w ↦ (π w).1) z ≠ 0 := by
      intro h
      apply hd0
      rw [h, mul_zero, add_zero, mul_eq_zero] at hrel
      rw [h, hrel.resolve_left hWY]; rfl
    set Φ : ℂ × ℂ × ℂ → ℂ := fun q ↦ q.1 + q.2.1 + E.a₁ * q.2.2 + E.a₃
    have hΦc : Continuous Φ := by fun_prop
    have hΦ0 : Φ (y₀, y₀, x₀) ≠ 0 := by
      intro h; apply hWY; simp only [Φ] at h; linear_combination h
    obtain ⟨η, hη, hηΦ⟩ := Metric.eventually_nhds_iff.mp
      (hΦc.continuousAt.eventually_ne hΦ0)
    obtain ⟨δ, hδ, hsec⟩ := exists_section_nhds (hπ.analyticAt_fst z) hX' hN hYc hη
    refine ⟨min δ η, lt_min hδ hη, fun x y hxy hdist ↦ ?_⟩
    rw [Prod.dist_eq, max_lt_iff] at hdist
    obtain ⟨w, hwN, hwx, hwy⟩ := hsec x (hdist.1.trans_le (min_le_left _ _))
    refine ⟨w, hwN, Prod.ext hwx ?_⟩
    have hw := hπ.eqn w
    rw [WeierstrassCurve.Affine.equation_iff] at hw hxy
    have hΦw : Φ (y, (π w).2, x) ≠ 0 := by
      apply hηΦ
      rw [Prod.dist_eq, Prod.dist_eq, max_lt_iff, max_lt_iff]
      exact ⟨hdist.2.trans_le (min_le_right _ _), hwy, hdist.1.trans_le (min_le_right _ _)⟩
    have key : (y - (π w).2) * Φ (y, (π w).2, x) = 0 := by
      simp only [Φ]; rw [hwx] at hw; linear_combination hxy - hw
    exact (sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_right hΦw)).symm

/-- **Properness of `π` modulo `Γ`**: the points where `π` is bounded lie in `Γ · C` for a
compact `C ⊆ ℍ`. -/
theorem UnifProps.exists_isCompact [E.IsElliptic] (hπ : UnifProps E A B π) (R : ℝ) :
    ∃ C : Set ℍ, IsCompact C ∧ ∀ z : ℍ, ‖π z‖ ≤ R →
      ∃ γ ∈ Subgroup.closure {A, B}, γ • z ∈ C := by
  set K : Set (ℂ × ℂ) := {P | ‖P‖ ≤ R ∧ E.toAffine.Equation P.1 P.2}
  have hKc : IsCompact K := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · have hK : K = {P | ‖P‖ ≤ R} ∩ {P | E.toAffine.Equation P.1 P.2} := rfl
      rw [hK]
      refine (isClosed_le continuous_norm continuous_const).inter ?_
      have : {P : ℂ × ℂ | E.toAffine.Equation P.1 P.2} = {P | P.2 ^ 2 + E.a₁ * P.1 * P.2 +
          E.a₃ * P.2 = P.1 ^ 3 + E.a₂ * P.1 ^ 2 + E.a₄ * P.1 + E.a₆} := by
        ext P; exact WeierstrassCurve.Affine.equation_iff _ _
      rw [this]
      exact isClosed_eq (by fun_prop) (by fun_prop)
    · exact (Metric.isBounded_closedBall (x := (0 : ℂ × ℂ)) (r := R)).subset
        fun P hP ↦ by rw [mem_closedBall, dist_zero_right]; exact hP.1
  have hP : ∀ P ∈ K, ∃ z : ℍ, π z = P := fun P hP ↦ hπ.surj P.1 P.2 hP.2
  choose! zP hzP using hP
  have hloc : ∀ z : ℍ, ∃ N ∈ 𝓝 z, IsCompact N := fun z ↦ by
    obtain ⟨s, hs, hsz⟩ := exists_compact_mem_nhds z; exact ⟨s, hsz, hs⟩
  choose N hN hNc using hloc
  have hε : ∀ P ∈ K, ∃ ε > 0, ∀ x y : ℂ, E.toAffine.Equation x y →
      dist (x, y) (π (zP P)) < ε → ∃ w ∈ N (zP P), π w = (x, y) :=
    fun P _ ↦ hπ.exists_dist_lt_imp (zP P) (hN (zP P))
  choose! ε hεpos hεN using hε
  obtain ⟨t, htK, hcov⟩ := hKc.elim_nhds_subcover (fun P ↦ ball P (ε P))
    fun P hP ↦ ball_mem_nhds P (hεpos P hP)
  refine ⟨⋃ P ∈ t, N (zP P), t.isCompact_biUnion fun P _ ↦ hNc _, fun z hz ↦ ?_⟩
  have hzK : π z ∈ K := ⟨hz, hπ.eqn z⟩
  obtain ⟨P, hPt, hzP'⟩ := mem_iUnion₂.mp (hcov hzK)
  have hPK := htK P hPt
  rw [mem_ball] at hzP'
  obtain ⟨w, hwN, hw⟩ := hεN P hPK (π z).1 (π z).2 (hπ.eqn z) (by rwa [hzP P hPK])
  obtain ⟨γ, hγ, rfl⟩ := (hπ.fib z w).mp hw.symm
  exact ⟨γ, hγ, mem_iUnion₂.mpr ⟨P, hPt, hwN⟩⟩

end OrbicurveCores.Rigid
