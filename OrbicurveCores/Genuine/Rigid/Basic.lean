/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.Genuine.CommIndex
import OrbicurveCores.S1.Mobius

/-!
# U2c6: the uniformisation `π : ℍ → E(ℂ) ∖ 0` as a quotient map

Let `(A, B)` uniformise `E ∖ 0` (`Uniformizes E A B`) via `π`, and `Γ = ⟨A, B⟩`. This file proves
the topological facts about `π` and `Γ` used by the analytic half of U2:

* `UnifProps`: the properties of `π` packaged in `Uniformizes`;
* `neg_one_notMem_closure`: `-1 ∉ Γ`;
* `UnifProps.exists_injOn`: `π` is locally injective (its derivative does not vanish);
* `UnifProps.eq_one_of_smul_eq`: `Γ` acts freely on `ℍ`;
* `UnifProps.exists_nhds_unique`: proper discontinuity: for `a, b ∈ ℍ` there are neighbourhoods
  `N_a, N_b` and `γ` such that only `γ` can map a point of `N_a` into `N_b`.
-/

open Complex Metric Set Filter Topology UpperHalfPlane Matrix
open OrbicurveCores.Fuchsian
open scoped MatrixGroups

namespace OrbicurveCores.Rigid

/-- **`-1 ∉ Γ`** for a once-punctured torus group `Γ = ⟨A, B⟩`. -/
lemma neg_one_notMem_closure {A B : SL(2, ℝ)} (hcomm : tr (A * B * A⁻¹ * B⁻¹) = -2)
    (hA : tr A ≠ 0) : (-1 : SL(2, ℝ)) ∉ Subgroup.closure {A, B} := by
  obtain ⟨x, y, z, hx, hy, hz, hrel, -, A', B', hcl, A₁, hA₁, B₁, hB₁, g, hgA,
    hgB⟩ := exists_normal_form hcomm hA
  rw [← hcl]
  set H₁ := Subgroup.closure {A₁, B₁}
  set P : Matrix (Fin 2) (Fin 2) ℝ := g.1
  have hP : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
  set φ := SL2R.conjMat P hP
  have hφA : φ A₁ = nA hz hrel := by
    apply Subtype.ext
    rw [SL2R.coe_conjMat]
    have := congrArg Units.val hgA
    simpa [P, Matrix.coe_units_inv] using this
  have hφB : φ B₁ = nB hz hrel := by
    apply Subtype.ext
    rw [SL2R.coe_conjMat]
    have := congrArg Units.val hgB
    simpa [P, Matrix.coe_units_inv] using this
  have hΓ₀ : Subgroup.closure {nA hz hrel, nB hz hrel} = H₁.map φ := by
    rw [MonoidHom.map_closure, Set.image_pair, hφA, hφB]
  have hφneg : φ (-1) = -1 := by
    apply Subtype.ext
    rw [SL2R.coe_conjMat]
    simp [Matrix.SpecialLinearGroup.coe_neg, mul_nonsing_inv _ hP]
  have hneg₁ : (-1 : SL(2, ℝ)) ∉ H₁ := fun h ↦ by
    have := Subgroup.mem_map_of_mem φ h
    rw [← hΓ₀, hφneg] at this
    exact neg_one_notMem hx hy hz hrel this
  have hinj₁ : Function.Injective (FreeGroup.lift ![A₁, B₁]) := by
    have hcomp : φ.comp (FreeGroup.lift ![A₁, B₁]) = FreeGroup.lift (ppF hz hrel) := by
      refine FreeGroup.ext_hom _ _ fun i ↦ ?_
      fin_cases i <;> simp [ppF, hφA, hφB]
    have := injective_lift_normal hx hy hz hrel
    rw [← hcomp, MonoidHom.coe_comp] at this
    exact this.of_comp
  have hA' : A' ∈ ({A₁, -A₁} : Set SL(2, ℝ)) := by rcases hA₁ with rfl | rfl <;> simp
  have hB' : B' ∈ ({B₁, -B₁} : Set SL(2, ℝ)) := by rcases hB₁ with rfl | rfl <;> simp
  exact neg_one_notMem_signs hA' hB' hinj₁ hneg₁

/-- The properties of a uniformisation `π : ℍ → E(ℂ) ∖ 0` with group `⟨A, B⟩`
(the content of `Uniformizes E A B`). -/
structure UnifProps (E : WeierstrassCurve ℂ) (A B : SL(2, ℝ)) (π : ℂ → ℂ × ℂ) : Prop where
  diff : ∀ z : ℍ, DifferentiableAt ℂ π z ∧ deriv π z ≠ 0
  eqn : ∀ z : ℍ, E.toAffine.Equation (π z).1 (π z).2
  surj : ∀ x y : ℂ, E.toAffine.Equation x y → ∃ z : ℍ, π z = (x, y)
  fib : ∀ z w : ℍ, π z = π w ↔ ∃ γ ∈ Subgroup.closure {A, B}, γ • z = w

lemma uniformizes_iff {E : WeierstrassCurve ℂ} {A B : SL(2, ℝ)} :
    Uniformizes E A B ↔ ∃ π, UnifProps E A B π :=
  ⟨fun ⟨π, h1, h2, h3, h4⟩ ↦ ⟨π, h1, h2, h3, h4⟩, fun ⟨π, h⟩ ↦ ⟨π, h.1, h.2, h.3, h.4⟩⟩

/-- A holomorphic function with nonzero derivative is locally injective. -/
lemma exists_injOn_of_analyticAt {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z)
    (hd : deriv f z ≠ 0) : ∃ U ∈ 𝓝 z, InjOn f U := by
  have hs := (hf.hasStrictDerivAt).hasStrictFDerivAt_equiv hd
  exact ⟨_, (hs.toOpenPartialHomeomorph f).open_source.mem_nhds
    hs.mem_toOpenPartialHomeomorph_source, (hs.toOpenPartialHomeomorph f).injOn⟩

/-- A Möbius transformation fixing every point of a nonempty open subset of `ℍ` is `±1`. -/
lemma eq_one_or_neg_one_of_eqOn {g : SL(2, ℝ)} {V : Set ℍ} (hV : IsOpen V) (hne : V.Nonempty)
    (h : ∀ w ∈ V, g • w = w) : g = 1 ∨ g = -1 := by
  have hid : Uniformization.HolomorphicH (id : ℍ → ℍ) := by
    unfold Uniformization.HolomorphicH
    refine (differentiableOn_id).congr fun z hz ↦ ?_
    simp [ofComplex_apply_of_im_pos hz]
  have := S1.eq_of_eqOn_open (S1.holomorphicH_smul g) hid hV hne h
  exact Uniformization.Unif.eq_one_or_neg_one_of_forall fun σ ↦ congrFun this σ

variable {E : WeierstrassCurve ℂ} {A B : SL(2, ℝ)} {π : ℂ → ℂ × ℂ}

lemma UnifProps.differentiableOn (hπ : UnifProps E A B π) :
    DifferentiableOn ℂ π {z : ℂ | 0 < z.im} := fun z hz ↦
  (hπ.diff ⟨z, hz⟩).1.differentiableWithinAt

lemma UnifProps.continuousOn (hπ : UnifProps E A B π) : ContinuousOn π {z : ℂ | 0 < z.im} :=
  hπ.differentiableOn.continuousOn

lemma UnifProps.continuous_comp (hπ : UnifProps E A B π) :
    Continuous fun z : ℍ ↦ π z :=
  hπ.continuousOn.comp_continuous UpperHalfPlane.continuous_coe fun z ↦ z.im_pos

/-- `π` is locally injective. -/
lemma UnifProps.exists_injOn (hπ : UnifProps E A B π) (z : ℍ) :
    ∃ U ∈ 𝓝 (z : ℂ), InjOn π U := by
  obtain ⟨hd, hd0⟩ := hπ.diff z
  have hopen : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const continuous_im
  have h1 : DifferentiableOn ℂ (fun w ↦ (π w).1) {w : ℂ | 0 < w.im} :=
    fun w hw ↦ ((hπ.diff ⟨w, hw⟩).1.fst).differentiableWithinAt
  have h2 : DifferentiableOn ℂ (fun w ↦ (π w).2) {w : ℂ | 0 < w.im} :=
    fun w hw ↦ ((hπ.diff ⟨w, hw⟩).1.snd).differentiableWithinAt
  have hz : (z : ℂ) ∈ {w : ℂ | 0 < w.im} := z.im_pos
  have hfst : HasDerivAt (fun w ↦ (π w).1) (deriv π z).1 z :=
    (ContinuousLinearMap.fst ℂ ℂ ℂ).hasFDerivAt.comp_hasDerivAt _ hd.hasDerivAt
  have hsnd : HasDerivAt (fun w ↦ (π w).2) (deriv π z).2 z :=
    (ContinuousLinearMap.snd ℂ ℂ ℂ).hasFDerivAt.comp_hasDerivAt _ hd.hasDerivAt
  by_cases h : (deriv π z).1 = 0
  · have h' : (deriv π z).2 ≠ 0 := fun h' ↦ hd0 (Prod.ext h h')
    rw [← hsnd.deriv] at h'
    obtain ⟨U, hU, hinj⟩ := exists_injOn_of_analyticAt (h2.analyticAt (hopen.mem_nhds hz)) h'
    exact ⟨U, hU, fun a ha b hb hab ↦ hinj ha hb (congrArg Prod.snd hab)⟩
  · rw [← hfst.deriv] at h
    obtain ⟨U, hU, hinj⟩ := exists_injOn_of_analyticAt (h1.analyticAt (hopen.mem_nhds hz)) h
    exact ⟨U, hU, fun a ha b hb hab ↦ hinj ha hb (congrArg Prod.fst hab)⟩

lemma continuous_smul_H (g : SL(2, ℝ)) : Continuous fun w : ℍ ↦ g • w :=
  S1.continuous_of_holomorphicH (S1.holomorphicH_smul g)

/-- `π`-fibres are `Γ`-orbits, `π` is locally injective, so near `z` every `γ ∈ Γ` fixing `z`
fixes every point. -/
lemma UnifProps.eq_one_of_smul_eq (hπ : UnifProps E A B π) (hcomm : tr (A * B * A⁻¹ * B⁻¹) = -2)
    (hA : tr A ≠ 0) {γ : SL(2, ℝ)} (hγ : γ ∈ Subgroup.closure {A, B}) {z : ℍ}
    (hz : γ • z = z) : γ = 1 := by
  obtain ⟨U, hU, hinj⟩ := hπ.exists_injOn z
  have hc : Continuous fun w : ℍ ↦ (w : ℂ) := UpperHalfPlane.continuous_coe
  set V : Set ℍ := interior ((fun w : ℍ ↦ (w : ℂ)) ⁻¹' U ∩
    (fun w : ℍ ↦ ((γ • w : ℍ) : ℂ)) ⁻¹' U)
  have hzV : z ∈ V := by
    refine mem_interior_iff_mem_nhds.mpr (inter_mem (hc.continuousAt.preimage_mem_nhds hU) ?_)
    refine (hc.comp (continuous_smul_H γ)).continuousAt.preimage_mem_nhds ?_
    simpa only [Function.comp_apply, hz] using hU
  have hfix : ∀ w ∈ V, γ • w = w := fun w hw ↦ by
    have hw' := interior_subset hw
    have h := (hπ.fib w (γ • w)).mpr ⟨γ, hγ, rfl⟩
    exact UpperHalfPlane.ext (hinj hw'.2 hw'.1 h.symm)
  rcases eq_one_or_neg_one_of_eqOn isOpen_interior ⟨z, hzV⟩ hfix with h | h
  · exact h
  · exact absurd (h ▸ hγ) (neg_one_notMem_closure hcomm hA)

/-- **Proper discontinuity.** For `a, b ∈ ℍ` there are neighbourhoods `N_a, N_b` and `γ ∈ SL(2, ℝ)`
such that every `δ ∈ Γ` mapping a point of `N_a` into `N_b` is `γ`. -/
lemma UnifProps.exists_nhds_unique (hπ : UnifProps E A B π)
    (hcomm : tr (A * B * A⁻¹ * B⁻¹) = -2) (hA : tr A ≠ 0) (a b : ℍ) :
    ∃ Na ∈ 𝓝 a, ∃ Nb ∈ 𝓝 b, ∃ γ : SL(2, ℝ), ∀ δ ∈ Subgroup.closure {A, B}, ∀ w ∈ Na,
      δ • w ∈ Nb → δ = γ := by
  have hpc := hπ.continuous_comp
  by_cases hab : π a = π b
  · obtain ⟨γ₀, hγ₀, rfl⟩ := (hπ.fib a b).mp hab
    obtain ⟨U, hU, hinj⟩ := hπ.exists_injOn a
    have hc : Continuous fun w : ℍ ↦ (w : ℂ) := UpperHalfPlane.continuous_coe
    have hUa : (fun w : ℍ ↦ (w : ℂ)) ⁻¹' U ∈ 𝓝 a := hc.continuousAt.preimage_mem_nhds hU
    refine ⟨_, hUa, (fun w ↦ γ₀⁻¹ • w) ⁻¹' ((fun w : ℍ ↦ (w : ℂ)) ⁻¹' U), ?_, γ₀,
      fun δ hδ w hw hδw ↦ ?_⟩
    · refine (continuous_smul_H γ₀⁻¹).continuousAt.preimage_mem_nhds ?_
      simpa [smul_smul] using hUa
    have h1 : γ₀⁻¹ * δ ∈ Subgroup.closure {A, B} := mul_mem (inv_mem hγ₀) hδ
    have h2 : (γ₀⁻¹ * δ) • w = w := by
      have hfib := (hπ.fib w ((γ₀⁻¹ * δ) • w)).mpr ⟨_, h1, rfl⟩
      apply UpperHalfPlane.ext
      refine hinj ?_ hw hfib.symm
      simpa [mul_smul] using hδw
    have := hπ.eq_one_of_smul_eq hcomm hA h1 h2
    rw [inv_mul_eq_one] at this
    exact this.symm
  · obtain ⟨Ua, Ub, hUa, hUb, hau, hbu, hdisj⟩ := t2_separation hab
    refine ⟨_, hpc.continuousAt.preimage_mem_nhds (hUa.mem_nhds hau), _,
      hpc.continuousAt.preimage_mem_nhds (hUb.mem_nhds hbu), 1, fun δ hδ w hw hδw ↦ ?_⟩
    have hfib := (hπ.fib w (δ • w)).mpr ⟨δ, hδ, rfl⟩
    exact absurd (hfib ▸ hδw : π w ∈ Ub) (Set.disjoint_left.mp hdisj hw)

end OrbicurveCores.Rigid
