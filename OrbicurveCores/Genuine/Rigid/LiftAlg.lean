/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.Genuine.Rigid.Fibre
import OrbicurveCores.Genuine.Rigid.Roots
import Oka.Uniformization.CoveringLift

/-!
# U2c4: lifting holomorphic families of points through unramified extensions

Let `R → S` be as in `Fibre.lean` (finite, unramified, of finite type over `ℂ`), and let
`z ↦ ev z` be a holomorphic family of points of `R` on an open set `U ⊆ ℂ`.

* `eq_of_mem_fib_of_eval`: points over the same point with the same simple value of a separating
  `θ` are equal (since `P'(θ) S ⊆ R[θ]`);
* `exists_local_branches`: near every `z₀ ∈ U` the points of `S` over `ev z` are given by `n`
  holomorphic branches, separated by the values of `θ`;
* `exists_lift`: if `U` is convex, the family lifts to a holomorphic family of points of `S`
  (the pairs `(z, point over ev z)` form a covering of `U`);
* `eqOn_of_lift`: two continuous lifts agreeing at one point agree.
-/

open Polynomial Set Filter Metric
open scoped Topology

namespace OrbicurveCores.Rigid

section

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra ℂ R] [Algebra ℂ S] [Algebra R S]
  [IsScalarTower ℂ R S] [IsDedekindDomain R] [IsDedekindDomain S] [Algebra.FiniteType ℂ S]
  [Algebra.IsIntegral R S] [Module.Finite R S] [FaithfulSMul R S]

omit [Algebra.FiniteType ℂ S] in
/-- Points over the same point with the same value of `θ`, at which `P'` does not vanish, are
equal. -/
lemma eq_of_mem_fib_of_eval (hunr : ∀ q : Ideal S, q.IsMaximal → q.ramificationIdx R = 1)
    {θ : S} (hdeg : (minpoly R θ).natDegree = Module.finrank R S) {χ₁ : R →ₐ[ℂ] ℂ}
    {ψ ψ' : S →ₐ[ℂ] ℂ} (hψ : ψ ∈ Fib S χ₁) (hψ' : ψ' ∈ Fib S χ₁) (heq : ψ θ = ψ' θ)
    (hd : ((minpoly R θ).map (χ₁ : R →+* ℂ)).derivative.eval (ψ θ) ≠ 0) : ψ = ψ' := by
  set d := aeval θ (derivative (minpoly R θ))
  have hdψ : ψ d = ((minpoly R θ).map (χ₁ : R →+* ℂ)).derivative.eval (ψ θ) := by
    rw [derivative_map, eval_map_of_mem_fib hψ]
  have hdψ' : ψ' d = ((minpoly R θ).map (χ₁ : R →+* ℂ)).derivative.eval (ψ θ) := by
    rw [derivative_map, heq, eval_map_of_mem_fib hψ']
  ext a
  obtain ⟨q, hq⟩ : ∃ q : R[X], aeval θ q = d * a := by
    have := derivative_mul_mem_adjoin hunr hdeg a
    rw [Algebra.adjoin_singleton_eq_range_aeval] at this
    exact this
  have h1 : ψ d * ψ a = ψ' d * ψ' a := by
    rw [← map_mul, ← map_mul, ← hq, ← eval_map_of_mem_fib hψ, ← eval_map_of_mem_fib hψ', heq]
  rw [hdψ, hdψ'] at h1
  exact mul_left_cancel₀ hd h1

variable {U : Set ℂ} {ev : ℂ → (R →ₐ[ℂ] ℂ)}

omit [Algebra.FiniteType ℂ S] [IsDedekindDomain R] in
lemma differentiableOn_eval_map (hev : ∀ r, DifferentiableOn ℂ (fun z ↦ ev z r) U) (q : R[X])
    {s : ℂ → ℂ} (hs : DifferentiableOn ℂ s U) :
    DifferentiableOn ℂ (fun z ↦ (q.map (ev z : R →+* ℂ)).eval (s z)) U := by
  have : (fun z ↦ (q.map (ev z : R →+* ℂ)).eval (s z)) =
      fun z ↦ ∑ k ∈ Finset.range (q.natDegree + 1), ev z (q.coeff k) * s z ^ k := by
    funext z
    rw [eval_map, eval₂_eq_sum_range]
    rfl
  rw [this]
  exact DifferentiableOn.fun_sum fun k _ ↦ (hev _).mul (hs.pow k)

/-- **Local branches.** Near `z₀ ∈ U`, the points over `ev z` are `n` holomorphic branches
`b χ`, indexed by the points `χ` over `ev z₀`, and separated by the values of `θ`. -/
theorem exists_local_branches (hunr : ∀ q : Ideal S, q.IsMaximal → q.ramificationIdx R = 1)
    (hU : IsOpen U) (hev : ∀ r, DifferentiableOn ℂ (fun z ↦ ev z r) U) {z₀ : ℂ} (hz₀ : z₀ ∈ U) :
    ∃ θ : S, ∃ ε > (0 : ℝ), ∃ V ⊆ U, IsOpen V ∧ IsPreconnected V ∧ z₀ ∈ V ∧
      ∃ b : (S →ₐ[ℂ] ℂ) → ℂ → (S →ₐ[ℂ] ℂ),
        (∀ χ ∈ Fib S (ev z₀), b χ z₀ = χ) ∧
        (∀ χ ∈ Fib S (ev z₀), ∀ z ∈ V, b χ z ∈ Fib S (ev z) ∧ ‖b χ z θ - χ θ‖ < ε) ∧
        (∀ χ ∈ Fib S (ev z₀), ∀ a, DifferentiableOn ℂ (fun z ↦ b χ z a) V) ∧
        (∀ z ∈ V, ∀ ψ ∈ Fib S (ev z), ∃ χ ∈ Fib S (ev z₀), ψ = b χ z) ∧
        (∀ χ ∈ Fib S (ev z₀), ∀ χ' ∈ Fib S (ev z₀), ∀ w : ℂ, ‖w - χ θ‖ < ε →
          ‖w - χ' θ‖ < ε → χ = χ') := by
  classical
  obtain ⟨θ, hθ⟩ := exists_separating (S := S) (ev z₀)
  obtain ⟨hdeg, hsimple⟩ := minpoly_of_separating hunr (ev z₀) hθ
  set P := minpoly R θ
  set n := Module.finrank R S
  have hPm : P.Monic := minpoly.monic (Algebra.IsIntegral.isIntegral θ)
  set Q : ℂ → ℂ[X] := fun z ↦ P.map (ev z : R →+* ℂ)
  have hQm : ∀ z, (Q z).Monic := fun z ↦ hPm.map _
  have hQn : ∀ z, (Q z).natDegree = n := fun z ↦ by rw [hPm.natDegree_map, hdeg]
  have hQd : ∀ k, DifferentiableOn ℂ (fun z ↦ (Q z).coeff k) U := fun k ↦ by
    simp only [Q, coeff_map]; exact hev _
  set F := Fib S (ev z₀)
  haveI : Finite F := (finite_fib (S := S) (ev z₀)).to_subtype
  haveI := Fintype.ofFinite F
  have hroot : ∀ z, ∀ ψ ∈ Fib S (ev z), (Q z).IsRoot (ψ θ) := fun z ψ hψ ↦ by
    rw [IsRoot, eval_map_of_mem_fib hψ, minpoly.aeval, map_zero]
  -- root branches at the points over `ev z₀`
  have hbr : ∀ χ : F, ∃ V ⊆ U, IsOpen V ∧ z₀ ∈ V ∧ ∃ ε > (0 : ℝ), ∃ s : ℂ → ℂ,
      DifferentiableOn ℂ s V ∧ s z₀ = χ.1 θ ∧ ∀ z ∈ V, (Q z).IsRoot (s z) ∧
        ‖s z - χ.1 θ‖ < ε ∧ ∀ σ, (Q z).IsRoot σ → ‖σ - χ.1 θ‖ < ε → σ = s z := fun χ ↦
    exists_root_branch (N := n) hU (fun z ↦ (hQn z).le) hQm hQn hQd hz₀ (hroot z₀ χ.1 χ.2)
      (hsimple χ.1 χ.2)
  choose V hVU hVo hz₀V ε₀ hε₀ s hsd hs0 hs using hbr
  -- the radius `ε`
  obtain ⟨ε, hε, hεle, hεsep⟩ : ∃ ε > (0 : ℝ), (∀ χ : F, ε ≤ ε₀ χ) ∧
      ∀ χ χ' : F, χ ≠ χ' → 2 * ε ≤ ‖χ.1 θ - χ'.1 θ‖ := by
    have h : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (∀ χ : F, ε ≤ ε₀ χ) ∧
        ∀ χ χ' : F, χ ≠ χ' → 2 * ε ≤ ‖χ.1 θ - χ'.1 θ‖ := by
      refine (Filter.eventually_all.mpr fun χ ↦ nhdsWithin_le_nhds (Iic_mem_nhds (hε₀ χ))).and
        (Filter.eventually_all.mpr fun χ ↦ Filter.eventually_all.mpr fun χ' ↦ ?_)
      by_cases hne : χ = χ'
      · exact Eventually.of_forall fun _ h ↦ absurd hne h
      have hpos : 0 < ‖χ.1 θ - χ'.1 θ‖ := norm_pos_iff.mpr (sub_ne_zero.mpr fun h ↦
        hne (Subtype.ext (hθ χ.2 χ'.2 h)))
      have ht : Tendsto (fun ε : ℝ ↦ 2 * ε) (𝓝[>] 0) (𝓝 0) :=
        ((continuous_const_mul (2 : ℝ)).tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds
      filter_upwards [ht.eventually (eventually_le_nhds hpos)] with ε hε _ using hε
    obtain ⟨ε, ⟨h1, h2⟩, h3⟩ := (h.and self_mem_nhdsWithin).exists
    exact ⟨ε, h3, h1, h2⟩
  -- the neighbourhood `V`
  have hcontd : ∀ χ : F, ContinuousAt (fun z ↦ (Q z).derivative.eval (s χ z)) z₀ := fun χ ↦ by
    have := differentiableOn_eval_map (fun r ↦ (hev r).mono (hVU χ)) (derivative P) (hsd χ)
    simp only [← derivative_map] at this
    exact (this.continuousOn.continuousAt ((hVo χ).mem_nhds (hz₀V χ)))
  have hevV : ∀ᶠ z in 𝓝 z₀, z ∈ U ∧ ∀ χ : F, z ∈ V χ ∧ ‖s χ z - χ.1 θ‖ < ε ∧
      (Q z).derivative.eval (s χ z) ≠ 0 := by
    refine (hU.eventually_mem hz₀).and (Filter.eventually_all.mpr fun χ ↦ ?_)
    refine ((hVo χ).eventually_mem (hz₀V χ)).and (Filter.Eventually.and ?_ ?_)
    · have hc : ContinuousAt (s χ) z₀ :=
        ((hsd χ).continuousOn.continuousAt ((hVo χ).mem_nhds (hz₀V χ)))
      have := hc.tendsto.sub_const (χ.1 θ)
      rw [hs0, sub_self] at this
      exact (tendsto_norm_zero.comp this).eventually (gt_mem_nhds hε)
    · refine (hcontd χ).eventually_ne ?_
      simp only [hs0]
      exact hsimple χ.1 χ.2
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hevV
  set W := ball z₀ r
  -- every point over `ev z`, `z ∈ W`, has `θ`-value some `s χ z`
  have hval : ∀ z ∈ W, ∀ ψ ∈ Fib S (ev z), ∃ χ : F, ψ θ = s χ z := by
    intro z hz ψ hψ
    by_contra hno
    push Not at hno
    -- `Q z` would have `n + 1` distinct roots
    have hinj : Set.InjOn (fun χ : F ↦ s χ z) univ := by
      intro χ _ χ' _ h
      by_contra hne
      have h1 := (hball z hz).2 χ
      have h2 := (hball z hz).2 χ'
      have := hεsep χ χ' hne
      have : ‖χ.1 θ - χ'.1 θ‖ ≤ ‖s χ z - χ.1 θ‖ + ‖s χ' z - χ'.1 θ‖ := by
        rw [show χ.1 θ - χ'.1 θ = -(s χ z - χ.1 θ) + (s χ' z - χ'.1 θ) + (s χ z - s χ' z) by
          ring]
        simp only [h, sub_self, add_zero]
        exact (norm_add_le _ _).trans (by rw [norm_neg])
      linarith [h1.2.1, h2.2.1]
    set T : Finset ℂ := insert (ψ θ) (Finset.univ.image fun χ : F ↦ s χ z)
    have hTsub : T ⊆ (Q z).roots.toFinset := by
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact Multiset.mem_toFinset.mpr ((mem_roots (hQm z).ne_zero).mpr (hroot z ψ hψ))
      · obtain ⟨χ, -, rfl⟩ := Finset.mem_image.mp hw
        exact Multiset.mem_toFinset.mpr ((mem_roots (hQm z).ne_zero).mpr
          (hs χ z ((hball z hz).2 χ).1).1)
    have hTcard : T.card = n + 1 := by
      rw [Finset.card_insert_of_notMem (by simpa using fun χ ↦ (hno χ).symm),
        Finset.card_image_of_injOn (fun χ _ χ' _ h ↦ hinj trivial trivial h),
        Finset.card_univ, ← Nat.card_eq_fintype_card, card_fib hunr]
    have := (Finset.card_le_card hTsub).trans ((Multiset.toFinset_card_le _).trans
      (card_roots' (Q z)))
    rw [hTcard, hQn] at this
    omega
  -- the points with `θ`-value `s χ z`
  have huniq : ∀ z ∈ W, ∀ χ : F, ∀ ψ ∈ Fib S (ev z), ∀ ψ' ∈ Fib S (ev z), ψ θ = s χ z →
      ψ' θ = s χ z → ψ = ψ' := fun z hz χ ψ hψ ψ' hψ' h h' ↦
    eq_of_mem_fib_of_eval hunr hdeg hψ hψ' (h.trans h'.symm) (by
      rw [h]; exact ((hball z hz).2 χ).2.2)
  have hW : ∀ z ∈ W, ∀ χ : F, ∃ ψ ∈ Fib S (ev z), ψ θ = s χ z := by
    intro z hz χ
    haveI : Finite (Fib S (ev z)) := (finite_fib (S := S) (ev z)).to_subtype
    choose c hc using fun ψ : Fib S (ev z) ↦ hval z hz ψ.1 ψ.2
    have hcinj : Function.Injective c := by
      intro ψ ψ' h
      exact Subtype.ext (huniq z hz (c ψ) ψ.1 ψ.2 ψ'.1 ψ'.2 (hc ψ) (by rw [hc ψ', h]))
    have hcard : Nat.card F ≤ Nat.card (Fib S (ev z)) := by
      rw [card_fib hunr, card_fib hunr]
    obtain ⟨ψ, hψ⟩ := (hcinj.bijective_of_nat_card_le hcard).2 χ
    exact ⟨ψ.1, ψ.2, hψ ▸ hc ψ⟩
  -- the branches
  set b : (S →ₐ[ℂ] ℂ) → ℂ → (S →ₐ[ℂ] ℂ) := fun χ z ↦
    if h : χ ∈ F ∧ z ∈ W then Classical.choose (hW z h.2 ⟨χ, h.1⟩) else χ
  have hb : ∀ χ : F, ∀ z ∈ W, b χ z ∈ Fib S (ev z) ∧ b χ z θ = s χ z := fun χ z hz ↦ by
    have h : χ.1 ∈ F ∧ z ∈ W := ⟨χ.2, hz⟩
    simp only [b, dif_pos h]
    exact Classical.choose_spec (hW z h.2 ⟨χ.1, h.1⟩)
  have hz₀W : z₀ ∈ W := mem_ball_self hr
  have hWU : W ⊆ U := fun z hz ↦ (hball z hz).1
  have hWV : ∀ χ : F, W ⊆ V χ := fun χ z hz ↦ ((hball z hz).2 χ).1
  refine ⟨θ, ε, hε, W, hWU, isOpen_ball, (convex_ball z₀ r).isPreconnected, hz₀W, b,
    fun χ hχ ↦ ?_, fun χ hχ z hz ↦ ?_, fun χ hχ a ↦ ?_, fun z hz ψ hψ ↦ ?_,
    fun χ hχ χ' hχ' w hw hw' ↦ ?_⟩
  · have h := hb ⟨χ, hχ⟩ z₀ hz₀W
    exact huniq z₀ hz₀W ⟨χ, hχ⟩ _ h.1 χ hχ h.2 (hs0 ⟨χ, hχ⟩).symm
  · have h := hb ⟨χ, hχ⟩ z hz
    exact ⟨h.1, by rw [h.2]; exact ((hball z hz).2 ⟨χ, hχ⟩).2.1⟩
  · -- `b χ z a = q(s χ z) / P'(s χ z)` where `P'(θ) a = q(θ)`
    obtain ⟨q, hq⟩ : ∃ q : R[X], aeval θ q = aeval θ (derivative P) * a := by
      have := derivative_mul_mem_adjoin hunr hdeg a
      rw [Algebra.adjoin_singleton_eq_range_aeval] at this
      exact this
    have hev' : ∀ r, DifferentiableOn ℂ (fun z ↦ ev z r) W := fun r ↦ (hev r).mono hWU
    have hsW : DifferentiableOn ℂ (s ⟨χ, hχ⟩) W := (hsd _).mono (hWV _)
    have hnum := differentiableOn_eval_map hev' q hsW
    have hden := differentiableOn_eval_map hev' (derivative P) hsW
    refine (hnum.div hden fun z hz ↦ ?_).congr fun z hz ↦ ?_
    · rw [← derivative_map]; exact ((hball z hz).2 ⟨χ, hχ⟩).2.2
    · obtain ⟨h1, h2⟩ := hb ⟨χ, hχ⟩ z hz
      have hd : ((P.map (ev z : R →+* ℂ)).derivative).eval (s ⟨χ, hχ⟩ z) ≠ 0 :=
        ((hball z hz).2 ⟨χ, hχ⟩).2.2
      have e1 : b χ z (aeval θ (derivative P)) =
          ((derivative P).map (ev z : R →+* ℂ)).eval (s ⟨χ, hχ⟩ z) := by
        rw [← h2, eval_map_of_mem_fib h1]
      have e2 : b χ z (aeval θ q) = (q.map (ev z : R →+* ℂ)).eval (s ⟨χ, hχ⟩ z) := by
        rw [← h2, eval_map_of_mem_fib h1]
      rw [hq, map_mul, e1] at e2
      have hd' : ((derivative P).map (ev z : R →+* ℂ)).eval (s ⟨χ, hχ⟩ z) ≠ 0 := by
        rw [← derivative_map]; exact hd
      change b χ z a = (q.map (ev z : R →+* ℂ)).eval (s ⟨χ, hχ⟩ z) /
        ((derivative P).map (ev z : R →+* ℂ)).eval (s ⟨χ, hχ⟩ z)
      rw [eq_div_iff hd', ← e2, mul_comm]
  · obtain ⟨χ, hχ⟩ := hval z hz ψ hψ
    have h := hb χ z hz
    exact ⟨χ.1, χ.2, huniq z hz χ ψ hψ _ h.1 hχ h.2⟩
  · by_contra hne
    have := hεsep ⟨χ, hχ⟩ ⟨χ', hχ'⟩ fun h ↦ hne (congrArg Subtype.val h)
    have h3 : ‖χ θ - χ' θ‖ ≤ ‖w - χ θ‖ + ‖w - χ' θ‖ := by
      rw [show χ θ - χ' θ = -(w - χ θ) + (w - χ' θ) by ring]
      exact (norm_add_le _ _).trans (by rw [norm_neg])
    simp only at this
    linarith
end

end OrbicurveCores.Rigid
