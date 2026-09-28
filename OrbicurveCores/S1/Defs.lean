/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import Oka.Uniformization.OncePunctured
import OrbicurveCores.Uniformization

/-!
# S1: definitions and interfaces

S1 identifies the once-punctured elliptic curves uniformised by Takeuchi's four groups. The
certificate route (Blueprint §2.3c): for each of four explicit curves `C` over `ℚ` there is a
rational function `G` of the `x`-coordinate of `C`, with poles exactly at the `2`-torsion, such that
`F(u) = G(x(u / 2))` is an *orbifold covering* of the `j`-line: over `0 = j(ρ)` it is ramified to
order exactly `3`, over `1728 = j(i)` to order exactly `2`, and it is unramified elsewhere. Lifting
`F ∘ ψ` through `j` (and `j` through `F`) gives a Möbius `h` with `h Γ^{(2)} h⁻¹ ⊆ PSL₂(ℤ)`, so the
uniformising group of `C ∖ O` has integral squared traces and is Takeuchi.

This file fixes the analytic vocabulary:

* `sig`: the orbifold signature of the `j`-line;
* `HasLocalForm f z n`: `f = f z + g ^ n` near `z`, with `g` a local coordinate at `z`;
* `OrbChart`, `IsOrbCover p Y e`: `p : Y → ℂ` is an orbifold covering with signature `e`.
-/

open Complex Metric Set Filter Topology Function

namespace OrbicurveCores.S1

/-- The orbifold signature of the `j`-line: branching order `3` over `0 = j(ρ)`, `2` over
`1728 = j(i)`, and `1` elsewhere. -/
noncomputable def sig (w : ℂ) : ℕ := if w = 0 then 3 else if w = 1728 then 2 else 1

lemma sig_pos (w : ℂ) : 0 < sig w := by
  unfold sig; split_ifs <;> norm_num

/-- `f` has a local normal form of order `n` at `z`: near `z`, `f = f z + g ^ n` for a local
coordinate `g` at `z` (analytic, `g z = 0`, `g' z ≠ 0`). -/
def HasLocalForm (f : ℂ → ℂ) (z : ℂ) (n : ℕ) : Prop :=
  ∃ g : ℂ → ℂ, AnalyticAt ℂ g z ∧ g z = 0 ∧ deriv g z ≠ 0 ∧ ∀ᶠ z' in 𝓝 z, f z' = f z + g z' ^ n

/-- An orbifold chart of `p` over the disc `ball w (ρ ^ n)`: `u` maps the open set `U` bijectively
onto `ball 0 ρ`, with holomorphic inverse `v`, and `p = w + u ^ n` on `U`. -/
structure OrbChart (p : ℂ → ℂ) (w : ℂ) (n : ℕ) (ρ : ℝ) (U : Set ℂ) (u v : ℂ → ℂ) : Prop where
  isOpen : IsOpen U
  mapsTo_u : MapsTo u U (ball 0 ρ)
  mapsTo_v : MapsTo v (ball 0 ρ) U
  v_u : ∀ y ∈ U, v (u y) = y
  u_v : ∀ t ∈ ball (0 : ℂ) ρ, u (v t) = t
  differentiableOn_v : DifferentiableOn ℂ v (ball 0 ρ)
  eq_pow : ∀ y ∈ U, p y = w + u y ^ n

/-- `p : Y → ℂ` is an **orbifold covering** of `ℂ` with signature `e`: every value is attained on
`Y`, and for every `w` there is `ρ > 0` such that the part of `Y` over `ball w (ρ ^ e w)` is a
disjoint union of orbifold charts. -/
def IsOrbCover (p : ℂ → ℂ) (Y : Set ℂ) (e : ℂ → ℕ) : Prop :=
  ∀ w : ℂ, (∃ y ∈ Y, p y = w) ∧ ∃ ρ > (0 : ℝ), ∃ (ι : Type) (U : ι → Set ℂ) (u v : ι → ℂ → ℂ),
    Pairwise (Disjoint on U) ∧ (∀ i, U i ⊆ Y ∧ OrbChart p w (e w) ρ (U i) (u i) (v i)) ∧
      ∀ y ∈ Y, p y ∈ ball w (ρ ^ e w) → ∃ i, y ∈ U i

/-- The upper half-plane as a subset of `ℂ`. -/
abbrev upper : Set ℂ := {z : ℂ | 0 < z.im}

/-! ### Interfaces (proved in the files of `S1/`) -/

/-- **Orbifold lifting** from the upper half-plane: a holomorphic `f` on `ℍ` whose local
ramification matches the signature of an orbifold covering `p` lifts through `p`. -/
def OrbLiftStatement : Prop :=
  ∀ (p f : ℂ → ℂ) (Y : Set ℂ) (e : ℂ → ℕ), (∀ w, 0 < e w) → IsOrbCover p Y e →
    DifferentiableOn ℂ f upper → (∀ z ∈ upper, HasLocalForm f z (e (f z))) →
    ∃ h : ℂ → ℂ, DifferentiableOn ℂ h upper ∧ MapsTo h upper Y ∧ ∀ z ∈ upper, p (h z) = f z

/-- The modular `j`-function is an orbifold covering of `ℂ` with signature `sig`, and has local
normal form of order `sig (j z)` at every point. -/
def JOrbStatement : Prop :=
  IsOrbCover Uniformization.jC upper sig ∧
    ∀ z ∈ upper, HasLocalForm Uniformization.jC z (sig (Uniformization.jC z))

/-- The `x`-coordinate `a ℘(u / 2) + r` of `C` along `ℂ / Λ`, halved: its critical points and poles
are exactly the lattice `Λ`, so `u ↦ G (ellX τ a r u)` is unramified over the `x`-line off `Λ`. -/
noncomputable def ellX (τ : UpperHalfPlane) (a r : ℂ) (u : ℂ) : ℂ :=
  a * (Heights.periodPairOfUpperHalfPlane τ).weierstrassP (u / 2) + r

/-- The `x`-coordinates `a ℘(v) + r` of the nonzero `2`-torsion points of `ℂ / Λ`. -/
def twoTorsionX (τ : UpperHalfPlane) (a r : ℂ) : Set ℂ :=
  (fun v ↦ a * (Heights.periodPairOfUpperHalfPlane τ).weierstrassP v + r) ''
    {v | 2 • v ∈ (Heights.periodPairOfUpperHalfPlane τ).lattice ∧
      v ∉ (Heights.periodPairOfUpperHalfPlane τ).lattice}

/-- **Pulling back an orbifold covering of the `x`-line.** If `G` is holomorphic off the
`2`-torsion `x`-coordinates `Z`, has poles at `Z` and at `∞`, finite fibres, attains every value,
and has local normal forms of order `sig (G x)`, then `F = G ∘ ellX` is an orbifold covering on
`ℂ ∖ Λ` with local normal forms of order `sig (F u)`. -/
def EllOrbStatement : Prop :=
  ∀ (τ : UpperHalfPlane) (a r : ℂ) (G : ℂ → ℂ), a ≠ 0 →
    DifferentiableOn ℂ G (twoTorsionX τ a r)ᶜ →
    (∀ x ∉ twoTorsionX τ a r, HasLocalForm G x (sig (G x))) →
    (∀ w, {x | x ∉ twoTorsionX τ a r ∧ G x = w}.Finite) →
    (∀ w, ∃ x ∉ twoTorsionX τ a r, G x = w) →
    (∀ z ∈ twoTorsionX τ a r, Tendsto G (𝓝[≠] z) (Bornology.cobounded ℂ)) →
    Tendsto G (Bornology.cobounded ℂ) (Bornology.cobounded ℂ) →
    IsOrbCover (fun u ↦ G (ellX τ a r u))
        ((Heights.periodPairOfUpperHalfPlane τ).lattice : Set ℂ)ᶜ sig ∧
      ∀ u ∉ (Heights.periodPairOfUpperHalfPlane τ).lattice,
        HasLocalForm (fun u ↦ G (ellX τ a r u)) u (sig (G (ellX τ a r u)))

open scoped MatrixGroups in
/-- **Rigidity (uniqueness of the uniformised curve).** Two once-punctured elliptic curves
uniformised by the same pair `A, B` (so by the same group acting on `ℍ`) have the same
`j`-invariant. -/
def RigidityStatement : Prop :=
  ∀ (W W' : WeierstrassCurve ℂ) [W.IsElliptic] [W'.IsElliptic] (A B : SL(2, ℝ)),
    Uniformizes W A B → Uniformizes W' A B → W.j = W'.j

end OrbicurveCores.S1
