/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.Genuine.Rigid.Proper
import OrbicurveCores.S1.EllOrb

/-!
# U2c7: an orbifold covering criterion on `ℍ`

Let `π : ℍ → E(ℂ) ∖ 0` uniformise with group `Γ`, and `Γ' ≤ Γ`. A holomorphic `Γ'`-invariant
`F : ℍ → ℂ` which has local normal forms of order `e (F z)` at every `z` and is proper modulo
`Γ'` (bounded values only on `Γ' · C`, `C` compact) is an orbifold covering of `ℂ` in the sense of
S1 (`isOrbCover_of`). The charts over a disc about `w` are the `Γ'`-translates of charts at
representatives of the finitely many `Γ'`-orbits in `F⁻¹(w)`; they are disjoint by the proper
discontinuity of `Γ` (`UnifProps.exists_nhds_unique`), and they exhaust `F⁻¹(disc)` by
properness.

* `mob g`: the Möbius action of `g ∈ SL(2, ℝ)` on `ℂ` (through `ofComplex`);
* `exists_eq_of_proper`: such an `F` takes every value;
* `isOrbCover_of`: the criterion.
-/

open Complex Metric Set Filter UpperHalfPlane
open scoped MatrixGroups Topology
open OrbicurveCores.S1 (upper HasLocalForm IsOrbCover OrbChart)

namespace OrbicurveCores.Rigid

/-- The Möbius action of `g ∈ SL(2, ℝ)` on `ℂ`, through `ofComplex : ℂ → ℍ`. -/
noncomputable def mob (g : SL(2, ℝ)) (y : ℂ) : ℂ := ((g • ofComplex y : ℍ) : ℂ)

lemma mob_mem (g : SL(2, ℝ)) (y : ℂ) : mob g y ∈ upper := (g • ofComplex y).im_pos

lemma mob_coe (g : SL(2, ℝ)) (z : ℍ) : mob g z = ((g • z : ℍ) : ℂ) := by
  simp [mob, ofComplex_apply]

lemma ofComplex_mob (g : SL(2, ℝ)) (y : ℂ) : ofComplex (mob g y) = g • ofComplex y :=
  ofComplex_apply _

lemma mob_mul (g h : SL(2, ℝ)) (y : ℂ) : mob (g * h) y = mob g (mob h y) := by
  simp only [mob, ofComplex_apply, mul_smul]

lemma mob_one {y : ℂ} (hy : y ∈ upper) : mob 1 y = y := by
  simp [mob, ofComplex_apply_of_im_pos hy]

lemma mob_inv_mob (g : SL(2, ℝ)) {y : ℂ} (hy : y ∈ upper) : mob g⁻¹ (mob g y) = y := by
  rw [← mob_mul, inv_mul_cancel, mob_one hy]

lemma mob_mob_inv (g : SL(2, ℝ)) {y : ℂ} (hy : y ∈ upper) : mob g (mob g⁻¹ y) = y := by
  rw [← mob_mul, mul_inv_cancel, mob_one hy]

lemma differentiableOn_mob (g : SL(2, ℝ)) : DifferentiableOn ℂ (mob g) upper :=
  S1.holomorphicH_smul g

lemma continuousOn_mob (g : SL(2, ℝ)) : ContinuousOn (mob g) upper :=
  (differentiableOn_mob g).continuousOn

lemma coe_image_mem_nhds {z : ℍ} {N : Set ℍ} (hN : N ∈ 𝓝 z) :
    ((↑) : ℍ → ℂ) '' N ∈ 𝓝 (z : ℂ) := by
  rw [← isOpenEmbedding_coe.map_nhds_eq z]; exact image_mem_map hN

lemma isOpen_coe_image {N : Set ℍ} (hN : IsOpen N) : IsOpen (((↑) : ℍ → ℂ) '' N) :=
  isOpenEmbedding_coe.isOpenMap _ hN

/-- A function with a local normal form at `z` is not constant near `z`. -/
lemma ne_eventually_of_hasLocalForm {F : ℂ → ℂ} {z : ℂ} {n : ℕ} (hn : 0 < n)
    (h : HasLocalForm F z n) : ∀ᶠ y in 𝓝[≠] z, F y ≠ F z := by
  obtain ⟨g, hg, hg0, hgd, hev⟩ := h
  have hne : ∀ᶠ y in 𝓝[≠] z, g y ≠ 0 := by
    rcases hg.eventually_eq_zero_or_eventually_ne_zero with h0 | h0
    · have h0' : g =ᶠ[𝓝 z] fun _ ↦ (0 : ℂ) := h0
      exact absurd (h0'.deriv_eq.trans (deriv_const _ _)) hgd
    · exact h0
  filter_upwards [hne, nhdsWithin_le_nhds hev] with y hy1 hy2
  rw [hy2]
  intro h
  exact hy1 (pow_eq_zero_iff hn.ne' |>.mp (add_eq_left.mp h))

variable {E : WeierstrassCurve ℂ} {A B : SL(2, ℝ)} {π : ℂ → ℂ × ℂ}

/-- **Surjectivity.** A holomorphic function on `ℍ` with local normal forms which is proper
modulo a group leaving it invariant takes every value. -/
lemma exists_eq_of_proper {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F upper) {e : ℂ → ℕ}
    (he : ∀ w, 0 < e w) (hloc : ∀ z ∈ upper, HasLocalForm F z (e (F z))) {Γ' : Subgroup SL(2, ℝ)}
    (hinv : ∀ γ ∈ Γ', ∀ y ∈ upper, F (mob γ y) = F y)
    (hprop : ∀ R : ℝ, ∃ C : Set ℍ, IsCompact C ∧ ∀ z : ℍ, ‖F z‖ ≤ R → ∃ γ ∈ Γ', γ • z ∈ C)
    (w : ℂ) : ∃ y ∈ upper, F y = w := by
  have hU : IsOpen upper := S1.isOpen_upper
  have han : AnalyticOnNhd ℂ F upper := hF.analyticOnNhd hU
  have hIu : (Complex.I : ℂ) ∈ upper := by simp [upper]
  have hopen : IsOpen (F '' upper) := by
    rcases han.is_constant_or_isOpen (convex_halfSpace_im_gt 0).isPreconnected with ⟨c, hc⟩ | h
    · exfalso
      have h1 := ne_eventually_of_hasLocalForm (he _) (hloc Complex.I hIu)
      have h2 : ∀ᶠ y in 𝓝[≠] (Complex.I : ℂ), F y = F Complex.I := by
        filter_upwards [nhdsWithin_le_nhds (hU.mem_nhds hIu)] with y hy
        rw [hc y hy, hc Complex.I hIu]
      obtain ⟨y, hy1, hy2⟩ := (h1.and h2).exists
      exact hy1 hy2
    · exact h upper subset_rfl hU
  have hclosed : IsClosed (F '' upper) := by
    refine isClosed_of_closure_subset fun v hv ↦ ?_
    obtain ⟨C, hC, hCp⟩ := hprop (‖v‖ + 1)
    set C' : Set ℂ := ((↑) : ℍ → ℂ) '' C
    have hC'c : IsCompact C' := hC.image UpperHalfPlane.continuous_coe
    have hC'u : C' ⊆ upper := by rintro _ ⟨c, -, rfl⟩; exact c.im_pos
    have hS : IsCompact (F '' C') := hC'c.image_of_continuousOn (hF.continuousOn.mono hC'u)
    have hsub : F '' upper ∩ ball v 1 ⊆ F '' C' := by
      rintro _ ⟨⟨y, hy, rfl⟩, hyv⟩
      have hR : ‖F y‖ ≤ ‖v‖ + 1 := by
        have := norm_le_norm_add_norm_sub' (F y) v
        rw [mem_ball, dist_eq_norm] at hyv
        linarith
      have hR' : ‖F (⟨y, hy⟩ : ℍ)‖ ≤ ‖v‖ + 1 := hR
      obtain ⟨γ, hγ, hγC⟩ := hCp ⟨y, hy⟩ hR'
      refine ⟨_, ⟨_, hγC, rfl⟩, ?_⟩
      have := hinv γ hγ y hy
      rw [mob, ofComplex_apply_of_im_pos hy] at this
      exact this
    have hv' : v ∈ closure (F '' upper ∩ ball v 1) := by
      rw [mem_closure_iff_nhds] at hv ⊢
      intro t ht
      obtain ⟨x, hx1, hx2⟩ := hv (t ∩ ball v 1) (inter_mem ht (ball_mem_nhds v one_pos))
      exact ⟨x, hx1.1, hx2, hx1.2⟩
    obtain ⟨y, hy, hyv⟩ := closure_minimal hsub hS.isClosed hv'
    exact ⟨y, hC'u hy, hyv⟩
  have hne : (F '' upper).Nonempty := ⟨_, Complex.I, hIu, rfl⟩
  have := (IsClopen.eq_univ ⟨hclosed, hopen⟩ hne)
  obtain ⟨y, hy, hyw⟩ := (this ▸ mem_univ w : w ∈ F '' upper)
  exact ⟨y, hy, hyw⟩

/-- Separation of two points of `ℍ` in distinct `Γ'`-orbits (or of a point from its
nontrivial translates). -/
lemma UnifProps.exists_sep (hπ : UnifProps E A B π) (hcomm : tr (A * B * A⁻¹ * B⁻¹) = -2)
    (hA : tr A ≠ 0) {Γ' : Subgroup SL(2, ℝ)} (hΓ' : Γ' ≤ Subgroup.closure {A, B}) (r r' : ℍ)
    (hrr : ∀ δ ∈ Γ', δ • r = r' → r = r' ∧ δ = 1) :
    ∃ N1 ∈ 𝓝 r, ∃ N2 ∈ 𝓝 r', ∀ δ ∈ Γ', ∀ a ∈ N1, δ • a ∈ N2 → r = r' ∧ δ = 1 := by
  obtain ⟨Na, hNa, Nb, hNb, γ, hγ⟩ := hπ.exists_nhds_unique hcomm hA r r'
  by_cases hg : γ ∈ Γ' ∧ γ • r = r'
  · refine ⟨Na, hNa, Nb, hNb, fun δ hδ a ha hδa ↦ ?_⟩
    obtain rfl := hγ δ (hΓ' hδ) a ha hδa
    exact hrr δ hδ hg.2
  · by_cases hgΓ : γ ∈ Γ'
    · have hne : γ • r ≠ r' := fun h ↦ hg ⟨hgΓ, h⟩
      obtain ⟨U, V, hU, hV, hrU, hrV, hUV⟩ := t2_separation hne
      refine ⟨Na ∩ (fun a ↦ γ • a) ⁻¹' U, inter_mem hNa
        ((continuous_smul_H γ).continuousAt.preimage_mem_nhds (hU.mem_nhds hrU)), Nb ∩ V,
        inter_mem hNb (hV.mem_nhds hrV), fun δ hδ a ha hδa ↦ ?_⟩
      obtain rfl := hγ δ (hΓ' hδ) a ha.1 hδa.1
      exact absurd hδa.2 (Set.disjoint_left.mp hUV ha.2)
    · refine ⟨Na, hNa, Nb, hNb, fun δ hδ a ha hδa ↦ ?_⟩
      obtain rfl := hγ δ (hΓ' hδ) a ha hδa
      exact absurd hδ hgΓ

/-- Separating neighbourhoods for a finite set of points in pairwise distinct `Γ'`-orbits. -/
lemma UnifProps.exists_sep_finset (hπ : UnifProps E A B π)
    (hcomm : tr (A * B * A⁻¹ * B⁻¹) = -2) (hA : tr A ≠ 0) {Γ' : Subgroup SL(2, ℝ)}
    (hΓ' : Γ' ≤ Subgroup.closure {A, B}) (T : Finset ℍ)
    (hT : ∀ r ∈ T, ∀ r' ∈ T, ∀ δ ∈ Γ', δ • r = r' → r = r' ∧ δ = 1) :
    ∃ M : T → Set ℍ, (∀ r, IsOpen (M r) ∧ (r : ℍ) ∈ M r) ∧
      ∀ r r' : T, ∀ δ ∈ Γ', ∀ a ∈ M r, δ • a ∈ M r' → r = r' ∧ δ = 1 := by
  have h := fun p : T × T ↦ hπ.exists_sep hcomm hA hΓ' p.1 p.2 (hT _ p.1.2 _ p.2.2)
  choose N1 hN1 N2 hN2 hN using h
  refine ⟨fun r ↦ interior (⋂ r' : T, N1 (r, r') ∩ N2 (r', r)), fun r ↦ ⟨isOpen_interior,
    mem_interior_iff_mem_nhds.mpr (Filter.iInter_mem.mpr fun r' ↦
      inter_mem (hN1 (r, r')) (hN2 (r', r)))⟩, fun r r' δ hδ a ha hδa ↦ ?_⟩
  have h1 := (mem_iInter.mp (interior_subset ha) r').1
  have h2 := (mem_iInter.mp (interior_subset hδa) r).2
  obtain ⟨h3, h4⟩ := hN (r, r') δ hδ a h1 h2
  exact ⟨Subtype.ext h3, h4⟩

/-- **U2c7. Orbifold covering criterion.** -/
theorem UnifProps.isOrbCover_of (hπ : UnifProps E A B π) (hcomm : tr (A * B * A⁻¹ * B⁻¹) = -2)
    (hA : tr A ≠ 0) {Γ' : Subgroup SL(2, ℝ)} (hΓ' : Γ' ≤ Subgroup.closure {A, B}) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F upper) {e : ℂ → ℕ} (he : ∀ w, 0 < e w)
    (hinv : ∀ γ ∈ Γ', ∀ y ∈ upper, F (mob γ y) = F y)
    (hloc : ∀ z ∈ upper, HasLocalForm F z (e (F z)))
    (hprop : ∀ R : ℝ, ∃ C : Set ℍ, IsCompact C ∧ ∀ z : ℍ, ‖F z‖ ≤ R → ∃ γ ∈ Γ', γ • z ∈ C) :
    IsOrbCover F upper e := by
  intro w
  refine ⟨exists_eq_of_proper hF he hloc hinv hprop w, ?_⟩
  set n := e w
  have hn : 0 < n := he w
  have hFc : Continuous fun c : ℍ ↦ F c :=
    hF.continuousOn.comp_continuous UpperHalfPlane.continuous_coe fun c ↦ c.im_pos
  have hinvH : ∀ γ ∈ Γ', ∀ c : ℍ, F ((γ • c : ℍ) : ℂ) = F c := fun γ hγ c ↦ by
    rw [← mob_coe]; exact hinv γ hγ c c.im_pos
  obtain ⟨C, hC, hCp⟩ := hprop (‖w‖ + 1)
  -- the fibre over `w` in `C` is finite
  set S : Set ℍ := {c | c ∈ C ∧ F c = w}
  have hSc : IsCompact S := hC.inter_right (isClosed_eq hFc continuous_const)
  have hSd : IsDiscrete S := by
    rw [isDiscrete_iff_forall_mem_exists_isOpen]
    rintro c ⟨hcC, hcw⟩
    have h1 := ne_eventually_of_hasLocalForm (he _) (hloc c c.im_pos)
    rw [hcw, eventually_nhdsWithin_iff] at h1
    obtain ⟨U, hU, hUo, hcU⟩ := _root_.eventually_nhds_iff.mp h1
    refine ⟨((↑) : ℍ → ℂ) ⁻¹' U, hUo.preimage UpperHalfPlane.continuous_coe, ?_⟩
    ext c'
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, S, mem_setOf_eq]
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · obtain ⟨h1, -, h3⟩ := h
      by_contra hne
      exact hU _ h1 (fun h ↦ hne (UpperHalfPlane.ext h)) h3
    · subst h; exact ⟨hcU, hcC, hcw⟩
  have hSf : S.Finite := hSc.finite hSd
  -- a minimal set of representatives of the `Γ'`-orbits in `S`
  set cov : Finset ℍ → Prop := fun T ↦ ∀ c ∈ S, ∃ r ∈ T, ∃ γ ∈ Γ', γ • r = c
  have hcovS : cov hSf.toFinset := fun c hc ↦ ⟨c, hSf.mem_toFinset.mpr hc, 1, one_mem _,
    one_smul _ _⟩
  classical
  obtain ⟨T, hT, hTmin⟩ := Finset.exists_min_image
    (hSf.toFinset.powerset.filter cov) Finset.card ⟨_, Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr subset_rfl, hcovS⟩⟩
  obtain ⟨hTS, hTcov⟩ := Finset.mem_filter.mp hT
  rw [Finset.mem_powerset] at hTS
  have hTS' : ∀ r ∈ T, r ∈ S := fun r hr ↦ hSf.mem_toFinset.mp (hTS hr)
  have hTsep : ∀ r ∈ T, ∀ r' ∈ T, ∀ δ ∈ Γ', δ • r = r' → r = r' ∧ δ = 1 := by
    intro r hr r' hr' δ hδ hδr
    have hrr : r = r' := by
      by_contra hne
      have hcov' : cov (T.erase r') := by
        intro c hc
        obtain ⟨r'', hr'', γ, hγ, rfl⟩ := hTcov c hc
        by_cases h : r'' = r'
        · subst h
          exact ⟨r, Finset.mem_erase.mpr ⟨hne, hr⟩, γ * δ, mul_mem hγ hδ, by rw [mul_smul, hδr]⟩
        · exact ⟨r'', Finset.mem_erase.mpr ⟨h, hr''⟩, γ, hγ, rfl⟩
      have := hTmin _ (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr
        ((Finset.erase_subset _ _).trans hTS), hcov'⟩)
      have h2 := Finset.card_erase_lt_of_mem hr'
      omega
    subst hrr
    exact ⟨rfl, hπ.eq_one_of_smul_eq hcomm hA (hΓ' hδ) hδr⟩
  obtain ⟨M, hMo, hMsep⟩ := hπ.exists_sep_finset hcomm hA hΓ' T hTsep
  -- charts at the representatives
  have hchart : ∀ r : T, ∃ (g : ℂ → ℂ) (ρ₀ : ℝ) (Er : Set ℂ) (ψ : ℂ → ℂ), 0 < ρ₀ ∧
      IsOpen Er ∧ (r : ℂ) ∈ Er ∧ Er ⊆ ((↑) : ℍ → ℂ) '' M r ∧ (∀ y ∈ Er, F y = w + g y ^ n) ∧
      ContinuousOn g Er ∧ MapsTo ψ (ball 0 ρ₀) Er ∧ (∀ y ∈ Er, ψ (g y) = y) ∧
      (∀ t ∈ ball (0 : ℂ) ρ₀, g (ψ t) = t) ∧ DifferentiableOn ℂ ψ (ball 0 ρ₀) := by
    intro r
    have hrw : F (r : ℂ) = w := (hTS' r r.2).2
    obtain ⟨g, hg, hg0, hgd, hev⟩ := hloc r (r : ℍ).im_pos
    rw [hrw] at hev
    have hev2 : ∀ᶠ y in 𝓝 ((r : ℍ) : ℂ), (AnalyticAt ℂ g y ∧ deriv g y ≠ 0) ∧
        (F y = w + g y ^ n ∧ y ∈ ((↑) : ℍ → ℂ) '' M r) :=
      (hg.eventually_analyticAt.and (hg.deriv.continuousAt.eventually_ne hgd)).and
        (hev.and ((isOpen_coe_image (hMo r).1).mem_nhds ⟨r, (hMo r).2, rfl⟩))
    obtain ⟨O, hOP, hOo, hrO⟩ := _root_.eventually_nhds_iff.mp hev2
    obtain ⟨ρ₀, hρ₀, Er, ψ, hEo, hEO, hrE, hψ, hψg, hgψ, hψd⟩ :=
      S1.exists_chart hOo hrO (fun y hy ↦ (hOP y hy).1.1) (fun y hy ↦ (hOP y hy).1.2) hg0
    exact ⟨g, ρ₀, Er, ψ, hρ₀, hEo, hrE, fun y hy ↦ (hOP y (hEO hy)).2.2,
      fun y hy ↦ (hOP y (hEO hy)).2.1,
      fun y hy ↦ (hOP y (hEO hy)).1.1.continuousAt.continuousWithinAt, hψ, hψg, hgψ, hψd⟩
  choose g ρ₀ Er ψ hρ₀ hEo hrE hEM hEF hgc hψ hψg hgψ hψd using hchart
  have hEu : ∀ r y, y ∈ Er r → y ∈ upper := fun r y hy ↦ by
    obtain ⟨c, -, rfl⟩ := hEM r hy; exact c.im_pos
  -- properness: points of `C` with `F` close to `w` lie in translates of the charts
  set O : Set ℍ := ⋃ r : T, ⋃ γ ∈ Γ', (fun c ↦ γ • c) '' (((↑) : ℍ → ℂ) ⁻¹' Er r)
  have hOo : IsOpen O := by
    refine isOpen_iUnion fun r ↦ isOpen_biUnion fun γ _ ↦ ?_
    have : (fun c : ℍ ↦ γ • c) '' (((↑) : ℍ → ℂ) ⁻¹' Er r) =
        (fun c ↦ γ⁻¹ • c) ⁻¹' (((↑) : ℍ → ℂ) ⁻¹' Er r) := by
      ext c; simp only [mem_image, mem_preimage]
      exact ⟨fun ⟨a, ha, h⟩ ↦ by rw [← h, inv_smul_smul]; exact ha,
        fun h ↦ ⟨_, h, smul_inv_smul _ _⟩⟩
    rw [this]
    exact ((hEo r).preimage UpperHalfPlane.continuous_coe).preimage (continuous_smul_H _)
  have hSO : S ⊆ O := by
    intro c hc
    obtain ⟨r, hr, γ, hγ, rfl⟩ := hTcov c hc
    exact mem_iUnion.mpr ⟨⟨r, hr⟩, mem_iUnion₂.mpr ⟨γ, hγ, r, hrE ⟨r, hr⟩, rfl⟩⟩
  obtain ⟨δ₀, hδ₀, hδ₀O⟩ : ∃ δ₀ > (0 : ℝ), ∀ c ∈ C, ‖F c - w‖ < δ₀ → c ∈ O := by
    have hK : IsCompact (C \ O) := hC.diff hOo
    rcases (C \ O).eq_empty_or_nonempty with h | h
    · refine ⟨1, one_pos, fun c hc _ ↦ ?_⟩
      by_contra hcO
      exact (h ▸ (⟨hc, hcO⟩ : c ∈ C \ O) : c ∈ (∅ : Set ℍ))
    · obtain ⟨c₀, hc₀, hmin⟩ := hK.exists_isMinOn h
        ((hFc.sub continuous_const).norm.continuousOn)
      refine ⟨‖F c₀ - w‖, ?_, fun c hc hcw ↦ ?_⟩
      · refine norm_pos_iff.mpr (sub_ne_zero.mpr fun h ↦ hc₀.2 (hSO ⟨hc₀.1, h⟩))
      · by_contra hcO
        exact absurd (hmin ⟨hc, hcO⟩) (not_le.mpr hcw)
  -- the radius
  obtain ⟨ρ, hρ, hρn, hρρ⟩ : ∃ ρ > (0 : ℝ), ρ ^ n < min δ₀ 1 ∧ ∀ r, ρ ≤ ρ₀ r := by
    have hev : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), 0 < ρ ∧ ρ ^ n < min δ₀ 1 ∧ ∀ r, ρ ≤ ρ₀ r := by
      refine Filter.Eventually.and (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0)
        (Filter.Eventually.and ?_ ?_)
      · have : Tendsto (fun ρ : ℝ ↦ ρ ^ n) (𝓝 0) (𝓝 0) := by
          simpa only [zero_pow hn.ne'] using (continuous_pow n).tendsto (0 : ℝ)
        exact nhdsWithin_le_nhds (this.eventually (gt_mem_nhds (lt_min hδ₀ one_pos)))
      · exact Filter.eventually_all.mpr fun r ↦ nhdsWithin_le_nhds (Iic_mem_nhds (hρ₀ r))
    obtain ⟨ρ, h1, h2, h3⟩ := hev.exists
    exact ⟨ρ, h1, h2, h3⟩
  -- the charts
  set ι := T × Γ'
  set U : ι → Set ℂ := fun i ↦ {y | y ∈ upper ∧ mob (i.2 : SL(2, ℝ))⁻¹ y ∈ Er i.1 ∧
    g i.1 (mob (i.2 : SL(2, ℝ))⁻¹ y) ∈ ball 0 ρ}
  set u : ι → ℂ → ℂ := fun i y ↦ g i.1 (mob (i.2 : SL(2, ℝ))⁻¹ y)
  set v : ι → ℂ → ℂ := fun i t ↦ mob i.2 (ψ i.1 t)
  refine ⟨ρ, hρ, ι, U, u, v, ?_, fun i ↦ ⟨fun y hy ↦ hy.1, ?_⟩, ?_⟩
  · -- disjointness
    rintro ⟨r, γ⟩ ⟨r', γ'⟩ hij
    refine Set.disjoint_left.mpr fun y hy hy' ↦ hij ?_
    obtain ⟨a, haM, ha⟩ := hEM r hy.2.1
    obtain ⟨b, hbM, hb⟩ := hEM r' hy'.2.1
    have hδ : (γ' : SL(2, ℝ))⁻¹ * γ ∈ Γ' := mul_mem (inv_mem γ'.2) γ.2
    have hab : ((γ' : SL(2, ℝ))⁻¹ * γ) • a = b := by
      apply UpperHalfPlane.ext
      have ha' : (a : ℂ) = mob (γ : SL(2, ℝ))⁻¹ y := ha
      have hb' : (b : ℂ) = mob (γ' : SL(2, ℝ))⁻¹ y := hb
      rw [← mob_coe, ha', ← mob_mul, mul_assoc, mul_inv_cancel, mul_one, hb']
    obtain ⟨rfl, h2⟩ := hMsep r r' _ hδ a haM (hab ▸ hbM)
    rw [inv_mul_eq_one] at h2
    rw [Subtype.ext h2]
  · -- the chart
    obtain ⟨r, γ⟩ := i
    have hball : ball (0 : ℂ) ρ ⊆ ball 0 (ρ₀ r) := ball_subset_ball (hρρ r)
    refine ⟨?_, fun y hy ↦ hy.2.2, fun t ht ↦ ?_, fun y hy ↦ ?_, fun t ht ↦ ?_, ?_,
      fun y hy ↦ ?_⟩
    · have h1 : ContinuousOn (mob (γ : SL(2, ℝ))⁻¹) upper := continuousOn_mob _
      have h2 := h1.isOpen_inter_preimage S1.isOpen_upper (hEo r)
      have h3 : ContinuousOn (fun y ↦ g r (mob (γ : SL(2, ℝ))⁻¹ y))
          (upper ∩ mob (γ : SL(2, ℝ))⁻¹ ⁻¹' Er r) :=
        (hgc r).comp (h1.mono inter_subset_left) fun y hy ↦ hy.2
      have h4 := h3.isOpen_inter_preimage h2 (isOpen_ball (x := (0 : ℂ)) (ε := ρ))
      convert h4 using 1
      ext y; simp only [U, mem_setOf_eq, mem_inter_iff, mem_preimage, and_assoc]
    · have hψt := hψ r (hball ht)
      have hu : ψ r t ∈ upper := hEu r _ hψt
      refine ⟨mob_mem _ _, ?_, ?_⟩
      · simp only [v]; rw [mob_inv_mob _ hu]; exact hψt
      · simp only [v]; rw [mob_inv_mob _ hu, hgψ r t (hball ht)]; exact ht
    · simp only [u, v]
      rw [hψg r _ hy.2.1, mob_mob_inv _ hy.1]
    · simp only [u, v]
      rw [mob_inv_mob _ (hEu r _ (hψ r (hball ht))), hgψ r t (hball ht)]
    · intro t ht
      have hψt := hψ r (hball ht)
      exact ((differentiableOn_mob _).comp ((hψd r).mono hball) fun t ht ↦
        hEu r _ (hψ r (hball ht))) t ht
    · have h1 := hinv _ (inv_mem γ.2) y hy.1
      rw [← h1, hEF r _ hy.2.1]
  · -- exhaustion
    intro y hy hFy
    rw [mem_ball, dist_eq_norm] at hFy
    have hR : ‖F (⟨y, hy⟩ : ℍ)‖ ≤ ‖w‖ + 1 := by
      have := norm_le_norm_add_norm_sub' (F y) w
      have : ‖F y - w‖ < 1 := hFy.trans_le (hρn.le.trans (min_le_right _ _))
      change ‖F y‖ ≤ _
      linarith
    obtain ⟨γ₁, hγ₁, hγ₁C⟩ := hCp ⟨y, hy⟩ hR
    have hF1 : F ((γ₁ • (⟨y, hy⟩ : ℍ) : ℍ) : ℂ) = F y := hinvH γ₁ hγ₁ ⟨y, hy⟩
    have hO := hδ₀O _ hγ₁C (by rw [hF1]; exact hFy.trans_le (hρn.le.trans (min_le_left _ _)))
    obtain ⟨r, hr⟩ := mem_iUnion.mp hO
    obtain ⟨γ, hγ, a, haE, hγa⟩ := mem_iUnion₂.mp hr
    set δ : SL(2, ℝ) := γ₁⁻¹ * γ
    have hδ : δ ∈ Γ' := mul_mem (inv_mem hγ₁) hγ
    have hy' : mob δ⁻¹ y = a := by
      have h1 : (y : ℂ) = mob δ a := by
        rw [mob_coe]; simp only [δ, mul_smul, hγa, inv_smul_smul]
      rw [h1, mob_inv_mob _ a.im_pos]
    refine ⟨(r, ⟨δ, hδ⟩), hy, ?_, ?_⟩
    · change mob δ⁻¹ y ∈ Er r; rw [hy']; exact haE
    · change g r (mob δ⁻¹ y) ∈ ball 0 ρ
      rw [hy', mem_ball, dist_zero_right]
      have h1 := hEF r a haE
      have h2 : F a = F y := by rw [← hy']; exact hinv _ (inv_mem hδ) y hy
      rw [h2] at h1
      rw [h1, add_sub_cancel_left, norm_pow] at hFy
      exact (pow_lt_pow_iff_left₀ (norm_nonneg _) hρ.le hn.ne').mp hFy

end OrbicurveCores.Rigid
