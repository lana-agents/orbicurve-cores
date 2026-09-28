/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.S1.LocalForm

/-!
# S1: pulling back an orbifold covering of the `x`-line along `u ↦ x(u / 2)`

We prove `EllOrbStatement`: if `G` is an orbifold covering of `ℂ` on the complement of the
`2`-torsion `x`-coordinates `Z` (holomorphic, local normal forms, finite fibres, surjective, poles
at `Z` and at `∞`), then `F = G ∘ ellX` is an orbifold covering on `ℂ ∖ Λ`.

The map `q = ellX τ a r : u ↦ a ℘(u / 2) + r` is holomorphic with nonvanishing derivative on
`ℂ ∖ Λ`, maps `ℂ ∖ Λ` onto `ℂ ∖ Z`, and its fibres are the orbits of `u ↦ ± u + 2 μ` (`μ ∈ Λ`).
The charts of `F` over a small disc about `w` are the translates `± U + 2 μ` of charts `U`
obtained by the inverse function theorem from the local normal forms of `G` at the finitely many
points of `G⁻¹(w) ∖ Z`; properness of `G` (`exists_dist_lt_imp_mem`) shows they exhaust
`F⁻¹(ball w (ρ ^ n))`.
-/

open Complex Metric Set Filter Topology Function Bornology

namespace OrbicurveCores.S1

local notation "𝓛" => Heights.periodPairOfUpperHalfPlane

/-! ### General lemmas -/

/-- **Inverse function theorem, chart form.** A function `φ` analytic with nonvanishing derivative
on an open set `O ∋ u₀`, `φ u₀ = 0`, maps an open `E ⊆ O` containing `u₀` injectively (with left
inverse `ψ`) and has a holomorphic section `ψ` over a disc `ball 0 ρ₀` with values in `E`. -/
theorem exists_chart {φ : ℂ → ℂ} {O : Set ℂ} {u₀ : ℂ} (hO : IsOpen O) (hu₀ : u₀ ∈ O)
    (han : ∀ y ∈ O, AnalyticAt ℂ φ y) (hd : ∀ y ∈ O, deriv φ y ≠ 0) (h0 : φ u₀ = 0) :
    ∃ ρ₀ > (0 : ℝ), ∃ (E : Set ℂ) (ψ : ℂ → ℂ), IsOpen E ∧ E ⊆ O ∧ u₀ ∈ E ∧
      MapsTo ψ (ball 0 ρ₀) E ∧ (∀ y ∈ E, ψ (φ y) = y) ∧ (∀ t ∈ ball (0 : ℂ) ρ₀, φ (ψ t) = t) ∧
      DifferentiableOn ℂ ψ (ball 0 ρ₀) := by
  have hs : HasStrictDerivAt φ (deriv φ u₀) u₀ := (han u₀ hu₀).hasStrictDerivAt
  have hs' := hs.hasStrictFDerivAt_equiv (hd u₀ hu₀)
  set e := hs'.toOpenPartialHomeomorph φ
  have he : ∀ y, e y = φ y := fun y ↦ rfl
  have hsrc : u₀ ∈ e.source := hs'.mem_toOpenPartialHomeomorph_source
  have hT : IsOpen (e.target ∩ e.symm ⁻¹' O) :=
    e.continuousOn_symm.isOpen_inter_preimage e.open_target hO
  have h1 : e u₀ = 0 := by rw [he, h0]
  have h0T : (0 : ℂ) ∈ e.target ∩ e.symm ⁻¹' O := by
    refine ⟨h1 ▸ e.map_source hsrc, ?_⟩
    rw [mem_preimage, ← h1, e.left_inv hsrc]; exact hu₀
  obtain ⟨ρ₀, hρ₀, hball⟩ := Metric.isOpen_iff.mp hT 0 h0T
  refine ⟨ρ₀, hρ₀, e.source ∩ O, e.symm, e.open_source.inter hO, inter_subset_right,
    ⟨hsrc, hu₀⟩, fun t ht ↦ ⟨e.map_target (hball ht).1, (hball ht).2⟩,
    fun y hy ↦ e.left_inv hy.1, fun t ht ↦ e.right_inv (hball ht).1, ?_⟩
  intro t ht
  have htT := hball ht
  have hO' : e.symm t ∈ O := htT.2
  have hsymm := e.hasStrictDerivAt_symm htT.1 (hd _ hO') (han _ hO').hasStrictDerivAt
  exact (HasStrictDerivAt.hasDerivAt hsymm).differentiableAt.differentiableWithinAt

/-- **Properness.** If `G` is continuous off `Z`, tends to `∞` at the points of `Z` and at `∞`, and
the solutions of `G x = w` off `Z` lie in the open set `M`, then all `x ∉ Z` with `G x` close
enough to `w` lie in `M`. -/
theorem exists_dist_lt_imp_mem {G : ℂ → ℂ} {Z M : Set ℂ} {w : ℂ} (hM : IsOpen M)
    (hcont : ContinuousOn G Zᶜ) (hfib : ∀ x ∉ Z, G x = w → x ∈ M)
    (hpole : ∀ z ∈ Z, Tendsto G (𝓝[≠] z) (cobounded ℂ))
    (hinf : Tendsto G (cobounded ℂ) (cobounded ℂ)) :
    ∃ δ > (0 : ℝ), ∀ x ∉ Z, dist (G x) w < δ → x ∈ M := by
  by_contra hcon
  push Not at hcon
  set l := comap G (𝓝 w) ⊓ 𝓟 (Zᶜ ∩ Mᶜ)
  haveI hl : l.NeBot := by
    refine ((nhds_basis_ball.comap G).inf_principal _).neBot_iff.mpr ?_
    intro δ hδ
    obtain ⟨x, hxZ, hxd, hxM⟩ := hcon δ hδ
    exact ⟨x, hxd, hxZ, hxM⟩
  have hGl : Tendsto G l (𝓝 w) := tendsto_comap.mono_left inf_le_left
  have hb : IsBounded (G ⁻¹' ball w 1) := by
    rw [isBounded_def, ← preimage_compl]
    exact hinf (isBounded_def.mp isBounded_ball)
  have hK : IsCompact (closure (G ⁻¹' ball w 1)) :=
    isCompact_of_isClosed_isBounded isClosed_closure hb.closure
  have hlK : l ≤ 𝓟 (closure (G ⁻¹' ball w 1)) := by
    rw [le_principal_iff]
    exact mem_of_superset (hGl (ball_mem_nhds w one_pos)) subset_closure
  obtain ⟨x, -, hx⟩ := hK hlK
  haveI : (𝓝 x ⊓ l).NeBot := hx
  have hZM : Zᶜ ∩ Mᶜ ∈ 𝓝 x ⊓ l := mem_inf_of_right (mem_inf_of_right (mem_principal_self _))
  by_cases hxZ : x ∈ Z
  · have hle : 𝓝 x ⊓ l ≤ 𝓝[≠] x := by
      refine le_inf inf_le_left (le_principal_iff.mpr (mem_of_superset hZM ?_))
      rintro y ⟨hy, -⟩ rfl
      exact hy hxZ
    exact ((hpole x hxZ).mono_left hle).not_tendsto (disjoint_cobounded_nhds w)
      (hGl.mono_left inf_le_right)
  · have hle : 𝓝 x ⊓ l ≤ 𝓝[Zᶜ] x :=
      le_inf inf_le_left (le_principal_iff.mpr (mem_of_superset hZM inter_subset_left))
    have hGx : G x = w :=
      tendsto_nhds_unique ((hcont x hxZ).tendsto.mono_left hle) (hGl.mono_left inf_le_right)
    have hMx : M ∩ (Zᶜ ∩ Mᶜ) ∈ 𝓝 x ⊓ l :=
      inter_mem (mem_inf_of_left (hM.mem_nhds (hfib x hxZ hGx))) hZM
    obtain ⟨y, hy1, -, hy2⟩ := Filter.nonempty_of_mem hMx
    exact hy2 hy1

/-! ### The Weierstrass function -/

theorem half_notMem (L : PeriodPair) {u : ℂ} (hu : u ∉ L.lattice) : u / 2 ∉ L.lattice :=
  fun h ↦ hu (by simpa only [add_halves] using L.lattice.add_mem h h)

theorem add_self_mem_of_derivWeierstrassP_eq_zero (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice)
    (h : L.derivWeierstrassP z = 0) : z + z ∈ L.lattice := by
  have hz' : -z ∉ L.lattice := by rwa [neg_mem_iff]
  have := (Heights.weierstrassP_deriv_eq_iff_sub_mem L z (-z) hz hz').mp
    ⟨(L.weierstrassP_neg z).symm, by rw [L.derivWeierstrassP_neg, h, neg_zero]⟩
  rwa [sub_neg_eq_add] at this

/-- The sign `±1` attached to a boolean. -/
def sgn : Bool → ℂ
  | true => 1
  | false => -1

theorem sgn_mul_self (b : Bool) : sgn b * sgn b = 1 := by
  cases b <;> norm_num [sgn]

theorem sgn_mul_mem {L : PeriodPair} (b : Bool) {z : ℂ} (hz : z ∈ L.lattice) :
    sgn b * z ∈ L.lattice := by
  cases b
  · rw [sgn, neg_one_mul]; exact neg_mem hz
  · rw [sgn, one_mul]; exact hz

variable {τ : UpperHalfPlane} {a r : ℂ}

theorem analyticAt_ellX {u : ℂ} (hu : u ∉ (𝓛 τ).lattice) : AnalyticAt ℂ (ellX τ a r) u := by
  have h := (𝓛 τ).analyticOnNhd_weierstrassP (u / 2) (half_notMem _ hu)
  have h2 : AnalyticAt ℂ (fun u : ℂ ↦ u / 2) u := analyticAt_id.div_const
  exact (analyticAt_const.mul
    (AnalyticAt.comp (g := (𝓛 τ).weierstrassP) (f := fun u : ℂ ↦ u / 2) h h2)).add analyticAt_const

theorem hasDerivAt_ellX {u : ℂ} (hu : u ∉ (𝓛 τ).lattice) :
    HasDerivAt (ellX τ a r) (a * ((𝓛 τ).derivWeierstrassP (u / 2) * (1 / 2))) u := by
  have h := Uniformization.hasDerivAt_wp τ (half_notMem _ hu)
  have h2 : HasDerivAt (fun u : ℂ ↦ u / 2) (1 / 2) u := (hasDerivAt_id' u).div_const 2
  exact ((h.comp u h2).const_mul a).add_const r

theorem deriv_ellX_ne_zero (ha : a ≠ 0) {u : ℂ} (hu : u ∉ (𝓛 τ).lattice) :
    deriv (ellX τ a r) u ≠ 0 := by
  rw [(hasDerivAt_ellX hu).deriv]
  refine mul_ne_zero ha (mul_ne_zero (fun h0 ↦ hu ?_) (by norm_num))
  have := add_self_mem_of_derivWeierstrassP_eq_zero _ (half_notMem _ hu) h0
  rwa [add_halves] at this

theorem ellX_notMem_twoTorsionX (ha : a ≠ 0) {u : ℂ} (hu : u ∉ (𝓛 τ).lattice) :
    ellX τ a r u ∉ twoTorsionX τ a r := by
  rintro ⟨v, ⟨hv2, hv⟩, hq⟩
  simp only [ellX, add_left_inj] at hq
  have hp := mul_left_cancel₀ ha hq
  have hv2' : v + v ∈ (𝓛 τ).lattice := by rwa [two_nsmul] at hv2
  rcases (Heights.weierstrassP_eq_iff_sub_mem_or_add_mem _ v (u / 2) hv
    (half_notMem _ hu)).mp hp with h | h
  · apply hu
    have := sub_mem (sub_mem hv2' h) h
    convert this using 1; ring
  · apply hu
    have := sub_mem (add_mem h h) hv2'
    convert this using 1; ring

theorem exists_ellX_eq (ha : a ≠ 0) {x : ℂ} (hx : x ∉ twoTorsionX τ a r) :
    ∃ u ∉ (𝓛 τ).lattice, ellX τ a r u = x := by
  obtain ⟨v, hv, hpv⟩ := Heights.exists_notMem_lattice_weierstrassP_eq (𝓛 τ) ((x - r) / a)
  have hq : a * (𝓛 τ).weierstrassP v + r = x := by
    rw [hpv, mul_div_cancel₀ _ ha, sub_add_cancel]
  refine ⟨2 * v, fun h ↦ hx ⟨v, ⟨by rwa [two_nsmul, ← two_mul], hv⟩, hq⟩, ?_⟩
  simp only [ellX, mul_div_cancel_left₀ v two_ne_zero]
  exact hq

theorem ellX_eq_or (ha : a ≠ 0) {u u' : ℂ} (hu : u ∉ (𝓛 τ).lattice) (hu' : u' ∉ (𝓛 τ).lattice)
    (h : ellX τ a r u' = ellX τ a r u) :
    ∃ μ ∈ (𝓛 τ).lattice, u' = u + 2 * μ ∨ u' = -u + 2 * μ := by
  simp only [ellX, add_left_inj] at h
  rcases (Heights.weierstrassP_eq_iff_sub_mem_or_add_mem _ (u' / 2) (u / 2) (half_notMem _ hu')
    (half_notMem _ hu)).mp (mul_left_cancel₀ ha h) with h' | h'
  · exact ⟨_, h', Or.inl (by ring)⟩
  · exact ⟨_, h', Or.inr (by ring)⟩

theorem ellX_sgn (b : Bool) {μ : ℂ} (hμ : μ ∈ (𝓛 τ).lattice) (y : ℂ) :
    ellX τ a r (sgn b * (y - 2 * μ)) = ellX τ a r y := by
  simp only [ellX]
  have e : sgn b * (y - 2 * μ) / 2 = sgn b * (y / 2 - μ) := by ring
  have hsub := (𝓛 τ).weierstrassP_sub_coe (y / 2) ⟨μ, hμ⟩
  rw [e]
  cases b
  · rw [sgn, neg_one_mul, PeriodPair.weierstrassP_neg, hsub]
  · rw [sgn, one_mul, hsub]

/-! ### Charts at a point of the fibre -/

/-- Chart data of `G ∘ ellX` at a point `u₀` over a solution `x ∉ Z` of `G x = w`: an open `E`
around `u₀` on which `g ∘ ellX` is a biholomorphism onto `ball 0 ρ₀` with inverse `ψ`, and an open
neighbourhood `M` of `x` covered by `ellX '' E` on which `G = w + g ^ n`. -/
theorem exists_pointData {G : ℂ → ℂ} {w x : ℂ} {n : ℕ} {B : Set ℂ} (ha : a ≠ 0)
    (hx : x ∉ twoTorsionX τ a r) (hGx : G x = w) (hloc : HasLocalForm G x n)
    (hB : IsOpen B) (hxB : x ∈ B) :
    ∃ ρ₀ > (0 : ℝ), ∃ (g ψ : ℂ → ℂ) (E M : Set ℂ), IsOpen E ∧ E ⊆ ((𝓛 τ).lattice : Set ℂ)ᶜ ∧
      ContinuousOn (fun y ↦ g (ellX τ a r y)) E ∧
      (∀ y ∈ E, ellX τ a r y ∈ B ∧ G (ellX τ a r y) = w + g (ellX τ a r y) ^ n) ∧
      MapsTo ψ (ball 0 ρ₀) E ∧ (∀ y ∈ E, ψ (g (ellX τ a r y)) = y) ∧
      (∀ t ∈ ball (0 : ℂ) ρ₀, g (ellX τ a r (ψ t)) = t) ∧ DifferentiableOn ℂ ψ (ball 0 ρ₀) ∧
      IsOpen M ∧ x ∈ M ∧ ∀ x' ∈ M, G x' = w + g x' ^ n ∧ ∃ y ∈ E, ellX τ a r y = x' := by
  obtain ⟨u₀, hu₀, hqu₀⟩ := exists_ellX_eq (r := r) ha hx
  obtain ⟨g, hg, hg0, hgd, hev⟩ := hloc
  rw [hGx] at hev
  obtain ⟨N, hNev, hNo, hxN⟩ := _root_.eventually_nhds_iff.mp hev
  have hq : AnalyticAt ℂ (ellX τ a r) u₀ := analyticAt_ellX hu₀
  have hqd0 : deriv (ellX τ a r) u₀ ≠ 0 := deriv_ellX_ne_zero ha hu₀
  set φ := fun y ↦ g ((ellX τ a r) y)
  have hgq : AnalyticAt ℂ g ((ellX τ a r) u₀) := by rw [hqu₀]; exact hg
  have hφ : AnalyticAt ℂ φ u₀ := hgq.comp hq
  have hφd : deriv φ u₀ ≠ 0 := by
    rw [show φ = g ∘ (ellX τ a r) from rfl,
      deriv_comp _ hgq.differentiableAt hq.differentiableAt, hqu₀]
    exact mul_ne_zero hgd hqd0
  have h4 : ∀ᶠ y in 𝓝 u₀, (ellX τ a r) y ∈ B ∩ N := by
    refine hq.continuousAt.tendsto.eventually ?_
    rw [hqu₀]
    exact (hB.inter hNo).mem_nhds ⟨hxB, hxN⟩
  have hev2 : ∀ᶠ y in 𝓝 u₀,
      y ∉ (𝓛 τ).lattice ∧ AnalyticAt ℂ φ y ∧ deriv φ y ≠ 0 ∧ (ellX τ a r) y ∈ B ∩ N :=
    Filter.Eventually.and ((𝓛 τ).isClosed_lattice.isOpen_compl.mem_nhds hu₀)
      (hφ.eventually_analyticAt.and ((hφ.deriv.continuousAt.eventually_ne hφd).and h4))
  obtain ⟨O, hOP, hOo, hu₀O⟩ := _root_.eventually_nhds_iff.mp hev2
  obtain ⟨ρ₀, hρ₀, E, ψ, hEo, hEO, hu₀E, hψ, hψφ, hφψ, hψd⟩ :=
    exists_chart hOo hu₀O (fun y hy ↦ (hOP y hy).2.1) (fun y hy ↦ (hOP y hy).2.2.1)
      (by simp only [φ, hqu₀, hg0])
  obtain ⟨ε, hε, s, hsc, hsq, hs0⟩ := Uniformization.exists_localSection hq.hasStrictDerivAt hqd0
  rw [hqu₀] at hsc hsq hs0
  refine ⟨ρ₀, hρ₀, g, ψ, E, ball x ε ∩ s ⁻¹' E ∩ N, hEo, fun y hy ↦ (hOP y (hEO hy)).1,
    fun y hy ↦ (hOP y (hEO hy)).2.1.continuousAt.continuousWithinAt, fun y hy ↦ ?_, hψ, hψφ,
    hφψ, hψd, (hsc.isOpen_inter_preimage isOpen_ball hEo).inter hNo,
    ⟨⟨mem_ball_self hε, by rw [mem_preimage, hs0]; exact hu₀E⟩, hxN⟩,
    fun x' hx' ↦ ⟨hNev x' hx'.2, s x', hx'.1.2, hsq x' hx'.1.1⟩⟩
  have hy' := (hOP y (hEO hy)).2.2.2
  exact ⟨hy'.1, hNev _ hy'.2⟩

/-! ### The main theorem -/

theorem ellOrbStatement : EllOrbStatement := by
  intro τ a r G ha hdiff hloc hfin hsurj hpole hinf
  set Z := twoTorsionX τ a r
  refine ⟨fun w ↦ ⟨?_, ?_⟩, fun u hu ↦ ?_⟩
  · obtain ⟨x, hx, rfl⟩ := hsurj w
    obtain ⟨u, hu, hqu⟩ := exists_ellX_eq (r := r) ha hx
    exact ⟨u, hu, by change G (ellX τ a r u) = G _; rw [hqu]⟩
  swap
  · exact HasLocalForm.comp (hloc _ (ellX_notMem_twoTorsionX ha hu)) (analyticAt_ellX hu)
      (deriv_ellX_ne_zero ha hu)
  -- the charts over a disc about `w`
  set n := sig w
  have hn : n ≠ 0 := (sig_pos w).ne'
  set S := {x | x ∉ Z ∧ G x = w}
  haveI : Finite S := (hfin w).to_subtype
  obtain ⟨B, hB, hBd⟩ := (hfin w).t2_separation
  have hloc' : ∀ x : S, HasLocalForm G x n := fun x ↦ by
    have := hloc x.1 x.2.1; rwa [x.2.2] at this
  choose ρ₀ hρ₀ g ψ E M hEo hEΛ hEc hEq hψ hψφ hφψ hψd hMo hxM hM using
    fun x : S ↦ exists_pointData (r := r) ha x.2.1 x.2.2 (hloc' x) (hB x).2 (hB x).1
  obtain ⟨δ, hδ, hδM⟩ := exists_dist_lt_imp_mem (isOpen_iUnion hMo) hdiff.continuousOn
    (fun x hx hGx ↦ mem_iUnion.mpr ⟨⟨x, hx, hGx⟩, hxM _⟩) hpole hinf
  have hev : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), 0 < ρ ∧ ρ ^ n < δ ∧ ∀ x : S, ρ ≤ ρ₀ x := by
    refine Filter.Eventually.and (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0)
      (Filter.Eventually.and ?_ ?_)
    · have : Tendsto (fun ρ : ℝ ↦ ρ ^ n) (𝓝 0) (𝓝 0) := by
        simpa only [zero_pow hn] using (continuous_pow n).tendsto (0 : ℝ)
      exact nhdsWithin_le_nhds (this.eventually (gt_mem_nhds hδ))
    · exact Filter.eventually_all.mpr fun x ↦ nhdsWithin_le_nhds (Iic_mem_nhds (hρ₀ x))
  obtain ⟨ρ, hρ, hρn, hρρ⟩ := hev.exists
  set ι := S × (𝓛 τ).lattice × Bool
  set σ : ι → ℂ → ℂ := fun i y ↦ sgn i.2.2 * (y - 2 * i.2.1)
  set W : S → Set ℂ := fun x ↦ E x ∩ (fun y ↦ g x ((ellX τ a r) y)) ⁻¹' ball 0 ρ
  have h2μ : ∀ i : ι, 2 * (i.2.1 : ℂ) ∈ (𝓛 τ).lattice := fun i ↦ by
    rw [two_mul]; exact add_mem i.2.1.2 i.2.1.2
  have hσq : ∀ i y, (ellX τ a r) (σ i y) = (ellX τ a r) y := fun i y ↦ ellX_sgn _ i.2.1.2 y
  have hσv : ∀ (i : ι) (t : ℂ), σ i (sgn i.2.2 * t + 2 * i.2.1) = t := fun i t ↦ by
    simp only [σ, add_sub_cancel_right, ← mul_assoc, sgn_mul_self, one_mul]
  have hvσ : ∀ (i : ι) (y : ℂ), sgn i.2.2 * σ i y + 2 * i.2.1 = y := fun i y ↦ by
    simp only [σ, ← mul_assoc, sgn_mul_self, one_mul, sub_add_cancel]
  have hUΛ : ∀ (i : ι) y, σ i y ∈ W i.1 → y ∉ (𝓛 τ).lattice := fun i y hy hyΛ ↦
    hEΛ i.1 hy.1 (sgn_mul_mem _ (sub_mem hyΛ (h2μ i)))
  refine ⟨ρ, hρ, ι, fun i ↦ σ i ⁻¹' W i.1, fun i y ↦ g i.1 ((ellX τ a r) (σ i y)),
    fun i t ↦ sgn i.2.2 * ψ i.1 t + 2 * i.2.1, ?_, fun i ↦ ⟨fun y hy ↦ hUΛ i y hy, ?_⟩, ?_⟩
  · -- disjointness
    rintro ⟨x, μ, b⟩ ⟨x', μ', b'⟩ hij
    refine Set.disjoint_left.mpr fun y hy hy' ↦ hij ?_
    have hyB : (ellX τ a r) y ∈ B x := hσq (x, μ, b) y ▸ (hEq x _ hy.1).1
    have hyB' : (ellX τ a r) y ∈ B x' := hσq (x', μ', b') y ▸ (hEq x' _ hy'.1).1
    have hxx : x = x' := by
      by_contra hne
      exact Set.disjoint_left.mp (hBd x.2 x'.2 (Subtype.coe_ne_coe.mpr hne)) hyB hyB'
    subst hxx
    have haa : σ (x, μ, b) y = σ (x, μ', b') y := by
      rw [← hψφ x _ hy.1, ← hψφ x _ hy'.1, hσq, hσq]
    have hyΛ := hUΛ _ y hy
    simp only [σ] at haa
    simp only [sgn] at haa
    cases b <;> cases b'
    · have hμ : (μ : ℂ) = μ' := by linear_combination haa / 2
      rw [Subtype.ext hμ]
    · exfalso; apply hyΛ
      have : y = μ + μ' := by linear_combination -haa / 2
      rw [this]; exact add_mem μ.2 μ'.2
    · exfalso; apply hyΛ
      have : y = μ + μ' := by linear_combination haa / 2
      rw [this]; exact add_mem μ.2 μ'.2
    · have hμ : (μ : ℂ) = μ' := by linear_combination -haa / 2
      rw [Subtype.ext hμ]
  · -- the chart
    have hball : ball (0 : ℂ) ρ ⊆ ball 0 (ρ₀ i.1) := ball_subset_ball (hρρ i.1)
    refine ⟨((hEc i.1).isOpen_inter_preimage (hEo i.1) isOpen_ball).preimage
      (continuous_const.mul (continuous_id.sub continuous_const)), fun y hy ↦ hy.2,
      fun t ht ↦ ?_, fun y hy ↦ ?_, fun t ht ↦ ?_,
      (((hψd i.1).mono hball).const_mul _).add_const _, fun y hy ↦ ?_⟩
    · change σ i _ ∈ W i.1
      rw [hσv]
      refine ⟨hψ i.1 (hball ht), ?_⟩
      change g i.1 ((ellX τ a r) (ψ i.1 t)) ∈ ball 0 ρ
      rw [hφψ i.1 t (hball ht)]; exact ht
    · change sgn i.2.2 * ψ i.1 (g i.1 ((ellX τ a r) (σ i y))) + 2 * i.2.1 = y
      rw [hψφ i.1 _ hy.1, hvσ]
    · change g i.1 ((ellX τ a r) (σ i (sgn i.2.2 * ψ i.1 t + 2 * i.2.1))) = t
      rw [hσv, hφψ i.1 t (hball ht)]
    · have := (hEq i.1 _ hy.1).2
      change _ = w + g i.1 (ellX τ a r (σ i y)) ^ n
      rwa [hσq] at this ⊢
  · -- exhaustion
    intro y hy hFy
    have hqy : (ellX τ a r) y ∉ Z := ellX_notMem_twoTorsionX ha hy
    have hFy' : dist (G ((ellX τ a r) y)) w < ρ ^ n := hFy
    obtain ⟨x, hxM'⟩ := mem_iUnion.mp (hδM ((ellX τ a r) y) hqy (lt_trans hFy' hρn))
    obtain ⟨hGx', a', ha'E, hqa'⟩ := hM x ((ellX τ a r) y) hxM'
    have hga : g x ((ellX τ a r) y) ∈ ball 0 ρ := by
      rw [mem_ball, dist_zero_right]
      rw [hGx', dist_eq_norm, add_sub_cancel_left, norm_pow] at hFy'
      exact (pow_lt_pow_iff_left₀ (norm_nonneg _) hρ.le hn).mp hFy'
    obtain ⟨μ, hμ, h | h⟩ := ellX_eq_or ha (hEΛ x ha'E) hy hqa'.symm
    · refine ⟨(x, ⟨μ, hμ⟩, true), ?_, ?_⟩
      · change sgn true * (y - 2 * μ) ∈ E x
        rw [h, sgn, one_mul, add_sub_cancel_right]; exact ha'E
      · change g x ((ellX τ a r) (σ (x, ⟨μ, hμ⟩, true) y)) ∈ ball 0 ρ
        rw [hσq]; exact hga
    · refine ⟨(x, ⟨μ, hμ⟩, false), ?_, ?_⟩
      · change sgn false * (y - 2 * μ) ∈ E x
        rw [h, sgn, add_sub_cancel_right, neg_one_mul, neg_neg]; exact ha'E
      · change g x ((ellX τ a r) (σ (x, ⟨μ, hμ⟩, false) y)) ∈ ball 0 ρ
        rw [hσq]; exact hga

end OrbicurveCores.S1
