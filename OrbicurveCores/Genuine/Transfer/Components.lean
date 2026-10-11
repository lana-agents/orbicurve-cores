/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Quotient.Noetherian

/-!
# T2d: rings all of whose local rings are DVRs

Let `T` be a Noetherian ring whose localizations at maximal ideals are discrete valuation rings
(`LocallyDVR T`; e.g. `K ⊗_k A` for a Dedekind domain `A` of finite type over `k`, char `0`).
Then:

* `T` is reduced (`LocallyDVR.isReduced`);
* a minimal prime `𝔭 ⊆ M` is the kernel of `T → T_M` (`minimal_eq_ker`), so distinct minimal
  primes are comaximal (`LocallyDVR.sup_eq_top`) and `T → ∏ T/𝔭` is surjective;
* every component `T/𝔭` is a Dedekind domain which is not a field
  (`LocallyDVR.isDedekindDomain_quotient`), with `(T/𝔭)_{M/𝔭} ≅ T_M`.
-/

open IsLocalRing

namespace OrbicurveCores.Transfer

/-- All localizations at maximal ideals are discrete valuation rings. -/
def LocallyDVR (T : Type*) [CommRing T] : Prop :=
  ∀ (M : Ideal T) [M.IsMaximal], ∃ _ : IsDomain (Localization.AtPrime M),
    IsDiscreteValuationRing (Localization.AtPrime M)

variable {T : Type*} [CommRing T]

lemma LocallyDVR.isReduced (h : LocallyDVR T) : IsReduced T :=
  isReduced_ofLocalizationMaximal T fun M hM ↦ by
    obtain ⟨_, _⟩ := h M
    infer_instance

/-- A minimal prime contained in `M` is the kernel of `T → T_M` when `T_M` is a domain. -/
lemma minimal_eq_ker {𝔭 M : Ideal T} (h𝔭 : 𝔭 ∈ minimalPrimes T) [M.IsPrime] (hle : 𝔭 ≤ M)
    [IsDomain (Localization.AtPrime M)] :
    𝔭 = RingHom.ker (algebraMap T (Localization.AtPrime M)) := by
  have hp : 𝔭.IsPrime := h𝔭.1.1
  have hker_le : RingHom.ker (algebraMap T (Localization.AtPrime M)) ≤ 𝔭 := by
    intro x hx
    obtain ⟨⟨s, hs⟩, hsx⟩ := (IsLocalization.map_eq_zero_iff M.primeCompl _ x).mp hx
    have hs𝔭 : s ∉ 𝔭 := fun h ↦ hs (hle h)
    have : s * x ∈ 𝔭 := by
      change s * x = 0 at hsx
      rw [hsx]; exact 𝔭.zero_mem
    exact (hp.mem_or_mem this).resolve_left hs𝔭
  have hprime : (RingHom.ker (algebraMap T (Localization.AtPrime M))).IsPrime :=
    RingHom.ker_isPrime _
  exact le_antisymm (h𝔭.2 ⟨hprime, bot_le⟩ hker_le) hker_le

/-- Distinct minimal primes are comaximal. -/
lemma LocallyDVR.sup_eq_top (h : LocallyDVR T) {𝔭 𝔮 : Ideal T} (h𝔭 : 𝔭 ∈ minimalPrimes T)
    (h𝔮 : 𝔮 ∈ minimalPrimes T) (hne : 𝔭 ≠ 𝔮) : 𝔭 ⊔ 𝔮 = ⊤ := by
  by_contra hne'
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne'
  obtain ⟨_, _⟩ := h M
  exact hne ((minimal_eq_ker h𝔭 (le_sup_left.trans hle)).trans
    (minimal_eq_ker h𝔮 (le_sup_right.trans hle)).symm)

section Quotient

variable {𝔭 : Ideal T} (h𝔭 : 𝔭 ∈ minimalPrimes T) (P : Ideal (T ⧸ 𝔭)) [P.IsMaximal]
  [IsDomain (Localization.AtPrime (P.comap (Ideal.Quotient.mk 𝔭)))]

omit [P.IsMaximal] in
lemma le_comap_mk : 𝔭 ≤ P.comap (Ideal.Quotient.mk 𝔭) := fun x hx ↦ by
  rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]; exact P.zero_mem

/-- The map `T/𝔭 → T_M` (`M = P ∩ T`) for a minimal prime `𝔭`, when `T_M` is a domain. -/
noncomputable def quotToLoc :
    T ⧸ 𝔭 →+* Localization.AtPrime (P.comap (Ideal.Quotient.mk 𝔭)) :=
  Ideal.Quotient.lift 𝔭 (algebraMap T _) fun x hx ↦ by
    rw [minimal_eq_ker h𝔭 (le_comap_mk P)] at hx; exact hx

lemma quotToLoc_mk (x : T) : quotToLoc h𝔭 P (Ideal.Quotient.mk 𝔭 x) = algebraMap T _ x := rfl

lemma quotToLoc_injective : Function.Injective (quotToLoc h𝔭 P) := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [quotToLoc_mk] at hy
  rw [Ideal.Quotient.eq_zero_iff_mem, minimal_eq_ker h𝔭 (le_comap_mk P)]
  exact hy

/-- `T_M` is the localization of `T/𝔭` at `P = M/𝔭`. -/
lemma isLocalization_quotToLoc :
    letI := (quotToLoc h𝔭 P).toAlgebra
    IsLocalization P.primeCompl (Localization.AtPrime (P.comap (Ideal.Quotient.mk 𝔭))) := by
  letI := (quotToLoc h𝔭 P).toAlgebra
  set M := P.comap (Ideal.Quotient.mk 𝔭)
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact (IsLocalization.AtPrime.isUnit_to_map_iff _ M x).mpr hy
  · intro z
    obtain ⟨⟨x, ⟨s, hs⟩⟩, rfl⟩ := IsLocalization.mk'_surjective M.primeCompl z
    refine ⟨⟨Ideal.Quotient.mk 𝔭 x, ⟨Ideal.Quotient.mk 𝔭 s, hs⟩⟩, ?_⟩
    change _ * quotToLoc h𝔭 P _ = quotToLoc h𝔭 P _
    rw [quotToLoc_mk, quotToLoc_mk]
    exact IsLocalization.mk'_spec _ _ _
  · intro x y hxy
    exact ⟨1, by rw [quotToLoc_injective h𝔭 P hxy]⟩

end Quotient

/-- **Components are Dedekind**: for a Noetherian `T` all of whose local rings at maximal
ideals are DVRs, and a minimal prime `𝔭`, `T/𝔭` is a Dedekind domain. -/
theorem LocallyDVR.isDedekindDomain_quotient [IsNoetherianRing T] (h : LocallyDVR T)
    {𝔭 : Ideal T} (h𝔭 : 𝔭 ∈ minimalPrimes T) : IsDedekindDomain (T ⧸ 𝔭) := by
  have : 𝔭.IsPrime := h𝔭.1.1
  have : IsNoetherianRing (T ⧸ 𝔭) := Ideal.Quotient.isNoetherianRing 𝔭
  have : IsDedekindDomainDvr (T ⧸ 𝔭) := by
    refine { is_dvr_at_nonzero_prime := fun P hP0 hP ↦ ?_ }
    obtain ⟨P', hP', hPP'⟩ := Ideal.exists_le_maximal P hP.ne_top
    set M := P'.comap (Ideal.Quotient.mk 𝔭)
    have : M.IsMaximal := Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
    obtain ⟨_, _⟩ := h M
    letI := (quotToLoc h𝔭 P').toAlgebra
    have hloc := isLocalization_quotToLoc h𝔭 P'
    -- `P = P'`
    set Q := P.comap (Ideal.Quotient.mk 𝔭)
    have hQ : Q.IsPrime := Ideal.comap_isPrime _ _
    have hdisj : Disjoint (M.primeCompl : Set T) Q := by
      rw [Set.disjoint_left]
      intro x hx hxQ
      exact hx (hPP' hxQ)
    have hmp := IsLocalization.isPrime_of_isPrime_disjoint M.primeCompl
      (Localization.AtPrime M) Q hQ hdisj
    have hcm := IsLocalization.under_map_of_isPrime_disjoint M.primeCompl
      (Localization.AtPrime M) hQ hdisj
    have hne : Q.map (algebraMap T (Localization.AtPrime M)) ≠ ⊥ := by
      intro h0
      apply hP0
      have hQ𝔭 : Q ≤ 𝔭 := by
        intro x hx
        have hk := minimal_eq_ker h𝔭 (le_comap_mk P')
        have h2 : x ∈ RingHom.ker (algebraMap T (Localization.AtPrime M)) := by
          have : x ∈ (Q.map (algebraMap T (Localization.AtPrime M))).under T := hcm.symm ▸ hx
          rw [h0] at this
          simpa [Ideal.under] using this
        exact (SetLike.ext_iff.mp hk x).mpr h2
      rw [eq_bot_iff]
      intro y hy
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (hQ𝔭 hy)
    have huniq := ((IsDiscreteValuationRing.iff_pid_with_one_nonzero_prime
      (Localization.AtPrime M)).mp inferInstance).2
    have hmax : Q.map (algebraMap T (Localization.AtPrime M)) =
        maximalIdeal (Localization.AtPrime M) :=
      huniq.unique ⟨hne, hmp⟩ ⟨IsDiscreteValuationRing.not_a_field _, inferInstance⟩
    have hQM : Q = M := by
      rw [← hcm, hmax, Localization.AtPrime.under_maximalIdeal]
    have hPeq : P = P' := Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective hQM
    subst hPeq
    let e := IsLocalization.algEquiv P.primeCompl (Localization.AtPrime P)
      (Localization.AtPrime M)
    have : IsDomain (Localization.AtPrime P) :=
      Function.Injective.isDomain (e.toRingEquiv.toRingHom) e.injective
    exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e.symm
  infer_instance

/-- Components are not fields. -/
theorem LocallyDVR.not_isField_quotient (h : LocallyDVR T) {𝔭 : Ideal T}
    (h𝔭 : 𝔭 ∈ minimalPrimes T) : ¬ IsField (T ⧸ 𝔭) := by
  intro hF
  have hmax : 𝔭.IsMaximal := Ideal.Quotient.maximal_of_isField 𝔭 hF
  obtain ⟨_, _⟩ := h 𝔭
  apply IsDiscreteValuationRing.not_a_field (Localization.AtPrime 𝔭)
  rw [← Localization.AtPrime.map_eq_maximalIdeal, eq_bot_iff, Ideal.map_le_iff_le_comap]
  intro x hx
  have hk := minimal_eq_ker h𝔭 (le_refl 𝔭)
  have : x ∈ RingHom.ker (algebraMap T (Localization.AtPrime 𝔭)) := (SetLike.ext_iff.mp hk x).mp hx
  simpa using this

end OrbicurveCores.Transfer
