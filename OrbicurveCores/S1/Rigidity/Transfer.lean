/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.S1.Rigidity.Lift

/-!
# Rigidity, step 3: two lifts with the same fibres give homothetic lattices

Let `σ : ℍ → ℂ ∖ Λ` and `σ' : ℍ → ℂ ∖ Λ'` be holomorphic lifts (`IsLatticeLift`) with the same
fibre relation mod the lattices (`SameFibres`). Then `σ z ↦ σ' z` descends to a bijection
`Φ : ℂ / Λ → ℂ / Λ'` fixing `0` (`transfer`). It is continuous off `0` because `σ` has local
holomorphic sections, and at `0` because its inverse is continuous off `0` and `ℂ / Λ'` is compact.
Its lift `β : ℂ → ℂ` through `ℂ → ℂ / Λ'` is holomorphic off `Λ` and continuous, hence entire; its
derivative is `Λ`-periodic, hence constant (Liouville). So `β x = a x` and `a Λ = Λ'`.
-/

open Complex Metric Set Filter Topology Function
open UpperHalfPlane hiding I

namespace OrbicurveCores.S1.Rigidity

local notation "mk" => Heights.latticeQuotientMk

lemma isDiscrete_lattice (τ : ℍ) : IsDiscrete ((Lt τ).lattice : Set ℂ) :=
  isDiscrete_iff_discreteTopology.mpr (inferInstanceAs (DiscreteTopology (Lt τ).lattice))

lemma mk_eq_mk_iff (τ : ℍ) {a b : ℂ} : mk τ a = mk τ b ↔ a - b ∈ (Lt τ).lattice := by
  change ((a : Heights.LatticeQuotient τ) = b) ↔ _
  rw [QuotientAddGroup.eq, show -a + b = -(a - b) by ring]
  exact neg_mem_iff

lemma mk_zero (τ : ℍ) : mk τ 0 = 0 := map_zero (QuotientAddGroup.mk' _)

lemma mk_eq_zero_iff (τ : ℍ) {a : ℂ} : mk τ a = 0 ↔ a ∈ (Lt τ).lattice := by
  rw [← mk_zero τ, mk_eq_mk_iff, sub_zero]

lemma isOpen_upper' : IsOpen {z : ℂ | 0 < z.im} :=
  isOpen_lt continuous_const Complex.continuous_im

variable {τ τ' : ℍ} {σ σ' : ℂ → ℂ}

lemma IsLatticeLift.hasStrictDerivAt (hσ : IsLatticeLift τ σ) {z : ℂ} (hz : 0 < z.im) :
    HasStrictDerivAt σ (deriv σ z) z :=
  (Uniformization.analyticAt_of_differentiableOn
    (fun w hw ↦ (hσ.differentiableAt w hw).differentiableWithinAt)
    (isOpen_upper'.mem_nhds hz)).hasStrictDerivAt

lemma IsLatticeLift.continuousOn (hσ : IsLatticeLift τ σ) :
    ContinuousOn σ {z : ℂ | 0 < z.im} :=
  fun z hz ↦ (hσ.differentiableAt z hz).continuousAt.continuousWithinAt

/-- Local holomorphic sections of `σ` modulo `Λ` near every point of `ℂ ∖ Λ`. -/
lemma IsLatticeLift.exists_chart (hσ : IsLatticeLift τ σ) {x₀ : ℂ}
    (hx₀ : x₀ ∉ (Lt τ).lattice) :
    ∃ δ > 0, ∃ s : ℂ → ℂ, ContinuousOn s (ball x₀ δ) ∧ ∀ y ∈ ball x₀ δ,
      0 < (s y).im ∧ σ (s y) - y ∈ (Lt τ).lattice ∧ DifferentiableAt ℂ s y := by
  obtain ⟨z₀, hz₀, hl⟩ := hσ.exists_sub_mem x₀ hx₀
  obtain ⟨ε, hε, s₀, hs₀c, hs₀, hs₀z⟩ :=
    Uniformization.exists_localSection (hσ.hasStrictDerivAt hz₀) (hσ.deriv_ne_zero z₀ hz₀)
  have hup : s₀ ⁻¹' {z : ℂ | 0 < z.im} ∈ 𝓝 (σ z₀) :=
    (hs₀c.continuousAt (ball_mem_nhds _ hε)).preimage_mem_nhds
      (by rw [hs₀z]; exact isOpen_upper'.mem_nhds hz₀)
  obtain ⟨δ₁, hδ₁, hball⟩ := Metric.mem_nhds_iff.mp hup
  have hmap : ∀ y ∈ ball x₀ (min ε δ₁), y + (σ z₀ - x₀) ∈ ball (σ z₀) (min ε δ₁) := by
    intro y hy
    rw [mem_ball, dist_eq_norm] at hy ⊢
    rwa [show y + (σ z₀ - x₀) - σ z₀ = y - x₀ by ring]
  have hsub : ball (σ z₀) (min ε δ₁) ⊆ ball (σ z₀) ε := ball_subset_ball (min_le_left _ _)
  refine ⟨min ε δ₁, lt_min hε hδ₁, fun y ↦ s₀ (y + (σ z₀ - x₀)), ?_, fun y hy ↦ ?_⟩
  · exact hs₀c.comp (continuousOn_id.add continuousOn_const) fun y hy ↦ hsub (hmap y hy)
  · have hw := hmap y hy
    have hwε := hsub hw
    have him : 0 < (s₀ (y + (σ z₀ - x₀))).im :=
      hball (ball_subset_ball (min_le_right _ _) hw)
    refine ⟨him, ?_, ?_⟩
    · rw [hs₀ _ hwε, show y + (σ z₀ - x₀) - y = σ z₀ - x₀ by ring]
      exact hl
    · have hd : DifferentiableAt ℂ s₀ (y + (σ z₀ - x₀)) :=
        Uniformization.differentiableAt_of_comp_eq (hσ.hasStrictDerivAt him)
          (hσ.deriv_ne_zero _ him) (hs₀c.continuousAt (isOpen_ball.mem_nhds hwε))
          (g := id) (by
            filter_upwards [isOpen_ball.mem_nhds hwε] with v hv
            exact hs₀ v hv) differentiableAt_id
      exact hd.comp y (differentiableAt_id.add_const _)

/-- `σ` and `σ'` have the same fibres modulo their lattices. -/
def SameFibres (τ τ' : ℍ) (σ σ' : ℂ → ℂ) : Prop :=
  ∀ z w : ℂ, 0 < z.im → 0 < w.im →
    (σ z - σ w ∈ (Lt τ).lattice ↔ σ' z - σ' w ∈ (Lt τ').lattice)

lemma SameFibres.symm (h : SameFibres τ τ' σ σ') : SameFibres τ' τ σ' σ :=
  fun z w hz hw ↦ (h z w hz hw).symm

/-- The induced map `ℂ / Λ → ℂ / Λ'`, `σ z ↦ σ' z`, `0 ↦ 0`. -/
noncomputable def transfer (τ τ' : ℍ) (σ σ' : ℂ → ℂ) (q : Heights.LatticeQuotient τ) :
    Heights.LatticeQuotient τ' := by
  classical
  exact if h : ∃ z : ℂ, 0 < z.im ∧ mk τ (σ z) = q then mk τ' (σ' h.choose) else 0

lemma transfer_mk_apply (hrel : SameFibres τ τ' σ σ') {z : ℂ} (hz : 0 < z.im) :
    transfer τ τ' σ σ' (mk τ (σ z)) = mk τ' (σ' z) := by
  have h : ∃ w : ℂ, 0 < w.im ∧ mk τ (σ w) = mk τ (σ z) := ⟨z, hz, rfl⟩
  rw [transfer, dif_pos h, mk_eq_mk_iff]
  obtain ⟨hw, hwz⟩ := h.choose_spec
  exact (hrel _ _ hw hz).mp ((mk_eq_mk_iff τ).mp hwz)

lemma transfer_mk_of_mem (hσ : IsLatticeLift τ σ) {x : ℂ} (hx : x ∈ (Lt τ).lattice) :
    transfer τ τ' σ σ' (mk τ x) = 0 := by
  rw [transfer, dif_neg]
  rintro ⟨z, hz, h⟩
  rw [(mk_eq_zero_iff τ).mpr hx, mk_eq_zero_iff] at h
  exact hσ.notMem z hz h

lemma transfer_transfer (hσ : IsLatticeLift τ σ) (hσ' : IsLatticeLift τ' σ')
    (hrel : SameFibres τ τ' σ σ') (q : Heights.LatticeQuotient τ) :
    transfer τ' τ σ' σ (transfer τ τ' σ σ' q) = q := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective _ q
  change transfer τ' τ σ' σ (transfer τ τ' σ σ' (mk τ x)) = mk τ x
  by_cases hx : x ∈ (Lt τ).lattice
  · rw [transfer_mk_of_mem hσ hx, ← mk_zero τ', transfer_mk_of_mem hσ' (zero_mem _),
      (mk_eq_zero_iff τ).mpr hx]
  · obtain ⟨z, hz, hzx⟩ := hσ.exists_sub_mem x hx
    rw [← (mk_eq_mk_iff τ).mpr hzx, transfer_mk_apply hrel hz, transfer_mk_apply hrel.symm hz]

lemma continuousAt_transfer_mk (hσ : IsLatticeLift τ σ) (hσ' : IsLatticeLift τ' σ')
    (hrel : SameFibres τ τ' σ σ') {x₀ : ℂ} (hx₀ : x₀ ∉ (Lt τ).lattice) :
    ContinuousAt (transfer τ τ' σ σ') (mk τ x₀) := by
  obtain ⟨δ, hδ, s, hsc, hs⟩ := hσ.exists_chart hx₀
  have heq : (fun y ↦ mk τ' (σ' (s y))) =ᶠ[𝓝 x₀] transfer τ τ' σ σ' ∘ mk τ := by
    filter_upwards [ball_mem_nhds x₀ hδ] with y hy
    obtain ⟨him, hmem, -⟩ := hs y hy
    rw [comp_apply, ← (mk_eq_mk_iff τ).mpr hmem, transfer_mk_apply hrel him]
  have hc : ContinuousAt (fun y ↦ mk τ' (σ' (s y))) x₀ :=
    (Heights.continuous_latticeQuotientMk τ').continuousAt.comp
      ((hσ'.differentiableAt _ (hs x₀ (mem_ball_self hδ)).1).continuousAt.comp
        (hsc.continuousAt (ball_mem_nhds x₀ hδ)))
  rw [ContinuousAt, Heights.latticeQuotient_nhds_mk, tendsto_map'_iff]
  exact hc.congr heq

/-- A bijection of compact Hausdorff spaces whose inverse is continuous away from `f x₀` is
continuous at `x₀`. -/
lemma continuousAt_of_inverse {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [CompactSpace Y] {f : X → Y} {g : Y → X} (hgf : ∀ x, g (f x) = x)
    (hfg : ∀ y, f (g y) = y) {x₀ : X} (hg : ∀ y, y ≠ f x₀ → ContinuousAt g y) :
    ContinuousAt f x₀ := by
  rw [ContinuousAt, _root_.tendsto_nhds]
  intro N hN hx₀N
  have hK : IsCompact Nᶜ := hN.isClosed_compl.isCompact
  have hgK : IsCompact (g '' Nᶜ) := hK.image_of_continuousOn fun y hy ↦
    (hg y fun h ↦ hy (h ▸ hx₀N)).continuousWithinAt
  have hx₀K : x₀ ∉ g '' Nᶜ := by
    rintro ⟨y, hy, hyx⟩
    exact hy (by rw [← hfg y, hyx]; exact hx₀N)
  filter_upwards [hgK.isClosed.isOpen_compl.mem_nhds hx₀K] with x hx
  by_contra hfx
  exact hx ⟨f x, hfx, hgf x⟩

lemma continuous_transfer (hσ : IsLatticeLift τ σ) (hσ' : IsLatticeLift τ' σ')
    (hrel : SameFibres τ τ' σ σ') : Continuous (transfer τ τ' σ σ') := by
  rw [continuous_iff_continuousAt]
  intro q
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective _ q
  change ContinuousAt _ (mk τ x)
  by_cases hx : x ∈ (Lt τ).lattice
  · refine continuousAt_of_inverse (transfer_transfer hσ hσ' hrel)
      (transfer_transfer hσ' hσ hrel.symm) fun y hy ↦ ?_
    obtain ⟨x', rfl⟩ := QuotientAddGroup.mk'_surjective _ y
    have hx' : x' ∉ (Lt τ').lattice := fun h ↦ hy (by
      change mk τ' x' = _
      rw [transfer_mk_of_mem hσ hx, (mk_eq_zero_iff τ').mpr h])
    exact continuousAt_transfer_mk hσ' hσ hrel.symm hx'
  · exact continuousAt_transfer_mk hσ hσ' hrel hx

/-- The lift of `transfer` to `ℂ` is linear. -/
lemma exists_linear (hσ : IsLatticeLift τ σ) (hσ' : IsLatticeLift τ' σ')
    (hrel : SameFibres τ τ' σ σ') :
    ∃ a : ℂ, ∀ x, mk τ' (a * x) = transfer τ τ' σ σ' (mk τ x) := by
  have hT := continuous_transfer hσ hσ' hrel
  obtain ⟨β, hβc, hβ, hβ0⟩ := (Heights.isCoveringMap_latticeQuotientMk τ').isCoveringMapOn
    |>.exists_lift_of_convex convex_univ
      (hT.comp (Heights.continuous_latticeQuotientMk τ)).continuousOn (mapsTo_univ _ _)
      (a₀ := 0) (mem_univ _) (e₀ := 0)
      (by rw [comp_apply, mk_zero, transfer_mk_of_mem hσ (zero_mem _)])
  have hβc' : Continuous β := continuousOn_univ.mp hβc
  have hβ' : ∀ x, mk τ' (β x) = transfer τ τ' σ σ' (mk τ x) := fun x ↦ hβ x (mem_univ _)
  -- `β` is holomorphic off `Λ`
  have hdiff : ∀ x₀ ∉ (Lt τ).lattice, DifferentiableAt ℂ β x₀ := by
    intro x₀ hx₀
    obtain ⟨δ, hδ, s, hsc, hs⟩ := hσ.exists_chart hx₀
    have hFc : ContinuousOn (fun y ↦ β y - σ' (s y)) (ball x₀ δ) :=
      hβc'.continuousOn.sub (hσ'.continuousOn.comp hsc fun y hy ↦ (hs y hy).1)
    have hFm : MapsTo (fun y ↦ β y - σ' (s y)) (ball x₀ δ) (Lt τ').lattice := by
      intro y hy
      obtain ⟨him, hmem, -⟩ := hs y hy
      change β y - σ' (s y) ∈ (Lt τ').lattice
      rw [← mk_eq_mk_iff, hβ', ← (mk_eq_mk_iff τ).mpr hmem,
        transfer_mk_apply hrel him]
    have heq : (fun y ↦ σ' (s y) + (β x₀ - σ' (s x₀))) =ᶠ[𝓝 x₀] β := by
      filter_upwards [ball_mem_nhds x₀ hδ] with y hy
      have := (isPreconnected_ball).constant_of_mapsTo (isDiscrete_lattice τ') hFc hFm hy
        (mem_ball_self hδ)
      rw [← this]
      ring
    obtain ⟨him, -, hsd⟩ := hs x₀ (mem_ball_self hδ)
    exact (((hσ'.differentiableAt _ him).comp x₀ hsd).add_const _).congr_of_eventuallyEq
      heq.symm
  -- removable singularities: `β` is entire
  have hβd : Differentiable ℂ β := by
    intro c
    by_cases hc : c ∈ (Lt τ).lattice
    · have hS := (Lt τ).compl_lattice_sdiff_singleton_mem_nhds c
      have : DifferentiableOn ℂ β ((↑(Lt τ).lattice \ {c})ᶜ) := by
        refine (Complex.differentiableOn_compl_singleton_and_continuousAt_iff hS).mp
          ⟨fun y hy ↦ (hdiff y fun h ↦ hy.1 ⟨h, hy.2⟩).differentiableWithinAt,
            hβc'.continuousAt⟩
      exact this.differentiableAt hS
    · exact hdiff c hc
  -- equivariance
  have hper : ∀ l ∈ (Lt τ).lattice, ∀ x, β (x + l) = β x + (β l - β 0) := by
    intro l hl x
    have hFm : MapsTo (fun y ↦ β (y + l) - β y) univ (Lt τ').lattice := by
      intro y _
      change β (y + l) - β y ∈ (Lt τ').lattice
      rw [← mk_eq_mk_iff, hβ', hβ',
        (mk_eq_mk_iff τ).mpr (by rwa [add_sub_cancel_left])]
    have : β (x + l) - β x = β (0 + l) - β 0 :=
      isPreconnected_univ.constant_of_mapsTo (isDiscrete_lattice τ')
        ((hβc'.comp (continuous_id.add continuous_const)).sub hβc').continuousOn hFm
        (mem_univ x) (mem_univ 0)
    rw [zero_add] at this
    rw [← this]
    ring
  have hderiv_per : ∀ z w, w ∈ (Lt τ).lattice → deriv β (z + w) = deriv β z := by
    intro z w hw
    have h1 : (fun y ↦ β (y + w)) = fun y ↦ β y + (β w - β 0) := funext (hper w hw)
    have h2 := congrArg (fun f ↦ deriv f z) h1
    simpa only [deriv_comp_add_const, deriv_add_const] using h2
  have hdd : Differentiable ℂ (deriv β) :=
    differentiableOn_univ.mp (hβd.differentiableOn.deriv isOpen_univ)
  have hbdd := IsZLattice.isCompact_range_of_periodic (Lt τ).lattice (deriv β) hdd.continuous
    hderiv_per
  have hconst : ∀ x, deriv β x = deriv β 0 := fun x ↦
    hdd.apply_eq_apply_of_bounded hbdd.isBounded x 0
  refine ⟨deriv β 0, fun x ↦ ?_⟩
  have hG : Differentiable ℂ (fun y ↦ β y - deriv β 0 * y) :=
    hβd.sub (differentiable_id.const_mul _)
  have hG' : ∀ y, deriv (fun y ↦ β y - deriv β 0 * y) y = 0 := by
    intro y
    have hD : HasDerivAt (fun y ↦ β y - deriv β 0 * y) (deriv β y - deriv β 0 * 1) y :=
      (hβd y).hasDerivAt.sub ((hasDerivAt_id y).const_mul (deriv β 0))
    rw [hD.deriv, hconst y, mul_one, sub_self]
  have := is_const_of_deriv_eq_zero hG hG' x 0
  simp only [mul_zero, sub_zero, hβ0] at this
  rw [← hβ', show β x = deriv β 0 * x by linear_combination this]

/-- **Two lifts with the same fibres give homothetic lattices.** -/
theorem exists_homothety (hσ : IsLatticeLift τ σ) (hσ' : IsLatticeLift τ' σ')
    (hrel : SameFibres τ τ' σ σ') :
    ∃ a : ℂ, a ≠ 0 ∧ ∀ x, x ∈ (Lt τ).lattice ↔ a * x ∈ (Lt τ').lattice := by
  obtain ⟨a, ha⟩ := exists_linear hσ hσ' hrel
  obtain ⟨a', ha'⟩ := exists_linear hσ' hσ hrel.symm
  have hcomp : ∀ x, mk τ (a' * (a * x)) = mk τ x := fun x ↦ by
    rw [ha', ha, transfer_transfer hσ hσ' hrel]
  have hFm : MapsTo (fun x : ℂ ↦ (a' * a - 1) * x) univ (Lt τ).lattice := by
    intro x _
    change (a' * a - 1) * x ∈ (Lt τ).lattice
    rw [show (a' * a - 1) * x = a' * (a * x) - x by ring]
    exact (mk_eq_mk_iff τ).mp (hcomp x)
  have h1 : (a' * a - 1) * 1 = (a' * a - 1) * 0 :=
    isPreconnected_univ.constant_of_mapsTo (isDiscrete_lattice τ)
      (continuous_const.mul continuous_id).continuousOn hFm (mem_univ 1) (mem_univ 0)
  rw [mul_one, mul_zero, sub_eq_zero] at h1
  refine ⟨a, fun h ↦ by simp [h] at h1, fun x ↦ ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩⟩
  · rw [← mk_eq_zero_iff, ha, transfer_mk_of_mem hσ hx]
  · rw [← mk_eq_zero_iff, ← hcomp, ha', transfer_mk_of_mem hσ' hx]

end OrbicurveCores.S1.Rigidity
