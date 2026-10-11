/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import OrbicurveCores.Genuine.Rigid.OrbCover
import OrbicurveCores.S1.OrbLift

/-!
# U2c8 (first part): orbifold lifting with a prescribed value, and Möbius comparison

* `exists_orbLift_through`: S1's orbifold lifting from `ℍ`, with a prescribed value `h z₀ = y₀`;
* `eqOn_of_lift`: two lifts agreeing at a point where the covering has nonzero derivative agree;
* `exists_mobius_of_orbCover`: two orbifold coverings `p, q : ℍ → ℂ` with the same signature
  differ by a Möbius transformation: `q ∘ m = p`, with `m z₀ = w₀` for prescribed generic points
  `z₀, w₀` with `p z₀ = q w₀`.
-/

open Complex Metric Set Filter Function UpperHalfPlane
open scoped MatrixGroups Topology
open OrbicurveCores.S1 (upper HasLocalForm IsOrbCover OrbChart IsLocLift jet germs)

namespace OrbicurveCores.Rigid

variable {p f : ℂ → ℂ} {Y : Set ℂ} {e : ℂ → ℕ}

/-- A local lift through a prescribed point of the fibre. -/
lemma exists_locLift_through (he : ∀ w, 0 < e w) (hp : IsOrbCover p Y e)
    (hf : ∀ z ∈ upper, HasLocalForm f z (e (f z))) {z₀ y₀ : ℂ} (hz₀ : z₀ ∈ upper) (hy₀ : y₀ ∈ Y)
    (hpy : p y₀ = f z₀) :
    ∃ r > (0 : ℝ), ∃ H : ℂ → ℂ, DifferentiableOn ℂ H (ball z₀ r) ∧
      (∀ z ∈ ball z₀ r, H z ∈ Y ∧ p (H z) = f z) ∧ H z₀ = y₀ := by
  set w := f z₀
  set n := e w
  have hn : 0 < n := he w
  obtain ⟨-, ρ, hρ, ι, U, u, v, -, hchart, hcov⟩ := hp w
  obtain ⟨g, hga, hg0, -, hfg⟩ := hf z₀ hz₀
  have hgs : ∀ᶠ z in 𝓝 z₀, g z ∈ ball (0 : ℂ) ρ :=
    hga.continuousAt.eventually_mem (isOpen_ball.mem_nhds (by simpa [hg0] using hρ))
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp
    ((hga.eventually_analyticAt.and hgs).and hfg)
  obtain ⟨i, hi⟩ := hcov y₀ hy₀ (by rw [hpy]; exact mem_ball_self (pow_pos hρ n))
  have hc := (hchart i).2
  refine ⟨r, hr, fun z ↦ v i (g z), fun z hz ↦ ?_, fun z hz ↦ ?_, ?_⟩
  · have hvd : DifferentiableAt ℂ (v i) (g z) :=
      hc.differentiableOn_v.differentiableAt (isOpen_ball.mem_nhds (hball z hz).1.2)
    exact (hvd.comp z (hball z hz).1.1.differentiableAt).differentiableWithinAt
  · have hU : v i (g z) ∈ U i := hc.mapsTo_v (hball z hz).1.2
    refine ⟨(hchart i).1 hU, ?_⟩
    rw [hc.eq_pow _ hU, hc.u_v _ (hball z hz).1.2, (hball z hz).2]
  · have h1 := hc.eq_pow _ hi
    rw [hpy] at h1
    have h2 : u i y₀ = 0 := pow_eq_zero_iff hn.ne' |>.mp (add_eq_left.mp h1.symm)
    simp only [hg0]
    rw [← h2, hc.v_u _ hi]

/-- **Orbifold lifting with a prescribed value.** -/
theorem exists_orbLift_through (he : ∀ w, 0 < e w) (hp : IsOrbCover p Y e)
    (hf : ∀ z ∈ upper, HasLocalForm f z (e (f z))) {z₀ y₀ : ℂ} (hz₀ : z₀ ∈ upper) (hy₀ : y₀ ∈ Y)
    (hpy : p y₀ = f z₀) :
    ∃ h : ℂ → ℂ, DifferentiableOn ℂ h upper ∧ MapsTo h upper Y ∧ (∀ z ∈ upper, p (h z) = f z) ∧
      h z₀ = y₀ := by
  have hcov := S1.germs_isCoveringMapOn he hp hf
  obtain ⟨r₀, hr₀, H₀, hH₀d, hH₀, hH₀z⟩ := exists_locLift_through he hp hf hz₀ hy₀ hpy
  have hS₀ : jet H₀ z₀ ∈ germs p f Y := ⟨hz₀, H₀, S1.isLocLift_of isOpen_ball hH₀d hH₀
    (mem_ball_self hr₀), rfl⟩
  obtain ⟨σ, hσc, hσ, hσz₀⟩ := hcov.exists_lift_of_convex (convex_halfSpace_im_gt 0)
    (g := fun z ↦ z) continuousOn_id (fun _ hz ↦ hz) hz₀ (e₀ := ⟨jet H₀ z₀, hS₀⟩) rfl
  refine ⟨fun z ↦ (σ z).1.2.1, ?_, ?_, ?_, ?_⟩
  rotate_left
  · intro z hz
    obtain ⟨-, h₀, hl, hj⟩ := (σ z).2
    rw [hσ z hz] at hl hj
    have : (σ z).1.2.1 = h₀ z := (congrArg (fun q : ℂ × ℂ × ℂ ↦ q.2.1) hj).symm
    change (σ z).1.2.1 ∈ Y
    rw [this]
    exact hl.self_of_nhds.2.1
  · intro z hz
    obtain ⟨-, h₀, hl, hj⟩ := (σ z).2
    rw [hσ z hz] at hl hj
    have : (σ z).1.2.1 = h₀ z := (congrArg (fun q : ℂ × ℂ × ℂ ↦ q.2.1) hj).symm
    change p (σ z).1.2.1 = f z
    rw [this]
    exact hl.self_of_nhds.2.2
  · simp only [hσz₀, jet, hH₀z]
  intro z hz
  obtain ⟨r, hr, -, -, hloc⟩ := S1.local_germs he hp hf hz
  have hzb : (σ z).1.1 ∈ ball z r := by rw [hσ z hz]; exact mem_ball_self hr
  obtain ⟨H, hd, hS, hqH⟩ := hloc (σ z).1 (σ z).2 hzb
  obtain ⟨s, hs, hsH, hsq⟩ := S1.exists_section hd isOpen_ball hS (σ z) hzb hqH
  rw [hσ z hz] at hsq
  obtain ⟨W, hW, hWinj⟩ := S1.germs_locallyInjective he hp hf (σ z)
  have hσz : ContinuousAt σ z := hσc.continuousAt (S1.isOpen_upper.mem_nhds hz)
  have hsz : ContinuousAt s z := hs.continuousAt (isOpen_ball.mem_nhds (mem_ball_self hr))
  have h1 : ∀ᶠ x in 𝓝 z, σ x ∈ W := hσz.preimage_mem_nhds hW
  have h2 : ∀ᶠ x in 𝓝 z, s x ∈ W := hsz.preimage_mem_nhds (by rw [hsq]; exact hW)
  have heq : (fun x ↦ (σ x).1.2.1) =ᶠ[𝓝 z] H := by
    filter_upwards [h1, h2, S1.isOpen_upper.mem_nhds hz,
      isOpen_ball.mem_nhds (mem_ball_self hr)] with x hx1 hx2 hxu hxb
    have hσs : σ x = s x := hWinj hx1 hx2 (by
      change (σ x).1.1 = (s x).1.1
      rw [hσ x hxu, hsH x hxb]
      rfl)
    rw [hσs, hsH x hxb]
    rfl
  exact ((hd.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hr))).congr_of_eventuallyEq
    heq).differentiableWithinAt

/-- **Uniqueness of lifts** at a point where the covering has nonzero derivative. -/
lemma eqOn_of_lift {h₁ h₂ : ℂ → ℂ} (hd₁ : DifferentiableOn ℂ h₁ upper)
    (hd₂ : DifferentiableOn ℂ h₂ upper) (hp : ∀ z ∈ upper, p (h₁ z) = p (h₂ z)) {z₀ : ℂ}
    (hz₀ : z₀ ∈ upper) (h₀ : h₁ z₀ = h₂ z₀) (hpa : AnalyticAt ℂ p (h₁ z₀))
    (hpd : deriv p (h₁ z₀) ≠ 0) : EqOn h₁ h₂ upper := by
  obtain ⟨V, hV, hinj⟩ := exists_injOn_of_analyticAt hpa hpd
  have hU := S1.isOpen_upper
  have hc₁ : ContinuousAt h₁ z₀ := (hd₁.differentiableAt (hU.mem_nhds hz₀)).continuousAt
  have hc₂ : ContinuousAt h₂ z₀ := (hd₂.differentiableAt (hU.mem_nhds hz₀)).continuousAt
  have hev : h₁ =ᶠ[𝓝 z₀] h₂ := by
    filter_upwards [hc₁.preimage_mem_nhds hV, hc₂.preimage_mem_nhds (h₀ ▸ hV),
      hU.mem_nhds hz₀] with z hz1 hz2 hz3
    exact hinj hz1 hz2 (hp z hz3)
  exact (hd₁.analyticOnNhd hU).eqOn_of_preconnected_of_eventuallyEq (hd₂.analyticOnNhd hU)
    (convex_halfSpace_im_gt 0).isPreconnected hz₀ hev

/-- A local normal form of order `1` has nonzero derivative. -/
lemma deriv_ne_zero_of_hasLocalForm_one {F : ℂ → ℂ} {z : ℂ} (h : HasLocalForm F z 1) :
    deriv F z ≠ 0 := by
  obtain ⟨g, hg, -, hgd, hev⟩ := h
  have : F =ᶠ[𝓝 z] fun y ↦ F z + g y := by
    filter_upwards [hev] with y hy; rw [hy, pow_one]
  rw [this.deriv_eq, deriv_const_add]
  exact hgd

/-- The holomorphic self-map of `ℍ` induced by a holomorphic `h : ℂ → ℂ` preserving `upper`. -/
noncomputable def toH (h : ℂ → ℂ) (hh : MapsTo h upper upper) : ℍ → ℍ :=
  fun z ↦ ⟨h z, hh z.im_pos⟩

lemma holomorphicH_toH {h : ℂ → ℂ} (hd : DifferentiableOn ℂ h upper) (hh : MapsTo h upper upper) :
    Uniformization.HolomorphicH (toH h hh) := by
  unfold Uniformization.HolomorphicH
  refine hd.congr fun z hz ↦ ?_
  simp [toH, ofComplex_apply_of_im_pos hz]

/-- **Two orbifold coverings of `ℂ` from `ℍ` with the same signature differ by a Möbius
transformation**, which can be chosen to map a prescribed generic point `z₀` to a prescribed
`w₀` in the corresponding fibre. -/
theorem exists_mobius_of_orbCover {p q : ℂ → ℂ} (he : ∀ w, 0 < e w)
    (hp : IsOrbCover p upper e) (hq : IsOrbCover q upper e)
    (hqd : DifferentiableOn ℂ q upper) (hploc : ∀ z ∈ upper, HasLocalForm p z (e (p z)))
    (hqloc : ∀ z ∈ upper, HasLocalForm q z (e (q z))) {z₀ w₀ : ℂ} (hz₀ : z₀ ∈ upper)
    (hw₀ : w₀ ∈ upper) (hpq : q w₀ = p z₀) (hgen : e (p z₀) = 1) :
    ∃ m : SL(2, ℝ), (∀ y ∈ upper, q (mob m y) = p y) ∧ mob m z₀ = w₀ := by
  obtain ⟨g, hgd, hgm, hgq, hg0⟩ := exists_orbLift_through he hq hploc hz₀ hw₀ hpq
  obtain ⟨g', hg'd, hg'm, hg'p, hg'0⟩ := exists_orbLift_through he hp hqloc hw₀ hz₀ hpq.symm
  -- `g ∘ g'` is a lift of `q` through `q` fixing `w₀`, hence the identity
  have hid : EqOn (g ∘ g') id upper := by
    refine eqOn_of_lift (p := q) (hgd.comp hg'd hg'm) differentiableOn_id
      (fun z hz ↦ by simp only [comp_apply, id, hgq _ (hg'm hz), hg'p z hz]) hw₀
      (by simp only [comp_apply, hg'0, hg0, id]) ?_ ?_
    · simp only [comp_apply, hg'0, hg0]
      exact (hqd.analyticOnNhd S1.isOpen_upper) w₀ hw₀
    · simp only [comp_apply, hg'0, hg0]
      have := hqloc w₀ hw₀
      rw [hpq, hgen] at this
      exact deriv_ne_zero_of_hasLocalForm_one this
  obtain ⟨m', hm'⟩ := S1.exists_SL2R_eq_of_leftInverse (holomorphicH_toH hg'd hg'm)
    (holomorphicH_toH hgd hgm) fun τ ↦ UpperHalfPlane.ext (hid τ.im_pos)
  have hg' : ∀ y ∈ upper, g' y = mob m' y := fun y hy ↦ by
    have := congrArg ((↑) : ℍ → ℂ) (hm' ⟨y, hy⟩)
    rw [mob, ofComplex_apply_of_im_pos hy]
    exact this
  have hg : ∀ y ∈ upper, g y = mob m'⁻¹ y := fun y hy ↦ by
    have h1 := hid (mob_mem m'⁻¹ y)
    simp only [comp_apply, id, hg' _ (mob_mem _ _), mob_mob_inv _ hy] at h1
    exact h1
  refine ⟨m'⁻¹, fun y hy ↦ ?_, ?_⟩
  · rw [← hg y hy, hgq y hy]
  · rw [← hg z₀ hz₀, hg0]

end OrbicurveCores.Rigid
