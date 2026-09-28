# Blueprint: [CanLift] Proposition 2.7 / [EstIUT] Proposition 2.1

Status legend: **[done]** proved in Lean here (no `sorry`/axioms), **[stated]** precise Lean
statement present but not proved, **[missing]** needs substantial new theory. The status column is
updated as work lands on branch `wp-canlift27`.

## 0. Sources (local copies in `references/`, gitignored, not committed)

| Key | Reference |
|---|---|
| [CanLift] | S. Mochizuki, *The absolute anabelian geometry of canonical curves*, Doc. Math. Extra Vol. Kato (2003). §2: Def. 2.1, Rem. 2.1.1–2.1.2, Prop. 2.3, Def. 2.6, **Prop. 2.7**. |
| [Corr] | S. Mochizuki, *Correspondences on hyperbolic curves*, J. Pure Appl. Algebra 131 (1998). §2 (Margulis, Takeuchi), §3 (hyperbolic core), Lemma 4.1. |
| [EstIUT] | Mochizuki–Fesenko–Hoshi–Minamide–Porowski, *Explicit estimates in IUT*, Kodai Math. J. 45 (2022). **Prop. 2.1** lists the four `j`-invariants. |
| [Sijs] | J. Sijsling, *Canonical models of arithmetic (1;∞)-curves*, Contemp. Math. 722 (2019), arXiv:1707.01158. Table 1 (trace triples), Table 4 (curves and `j`). |
| [Take2] | K. Takeuchi, *Arithmetic Fuchsian groups with signature (1;e)*, J. Math. Soc. Japan 35 (1983), Thm. 4.1(i). |
| [Take1] | K. Takeuchi, *Arithmetic triangle groups*, J. Math. Soc. Japan 29 (1977). |
| [Take75] | K. Takeuchi, *A characterization of arithmetic Fuchsian groups*, J. Math. Soc. Japan 27 (1975). |
| [Marg] | G. A. Margulis, *Discrete subgroups of semisimple Lie groups*, Ch. IX, Thm. (B) (p. 337, Thm. 27). |
| [Zim] | R. Zimmer, *Ergodic theory and semisimple groups*, Ch. 6 (Thm. 6.2.5, commensurator superrigidity). |
| [BM] | M. Burger, S. Mozes, *CAT(−1)-spaces, divergence groups and their commensurators*, JAMS 9 (1996). |
| [MR] | C. Maclachlan, A. Reid, *The arithmetic of hyperbolic 3-manifolds*, GTM 219, §8.3–8.4 (trace characterisation), §10.3. |

## 1. The statement

### 1.1 What the literature actually says

* [CanLift] Prop. 2.7 (k algebraically closed, char 0): for a *punctured hemi-elliptic* orbicurve
  `X = (E ∖ 0)/±1`: if `X` is non-arithmetic then `X` is a core; there are precisely 4 arithmetic
  such `X`, namely those of [Take2] Thm. 4.1(i). Its proof: non-arithmetic ⇒ a core `Z` exists
  ([Corr] §3, using Margulis); Riemann–Hurwitz for `E → Z^crs` forces the ramification type
  `(2,2,2,2)`, `(2,3,6)`, `(2,4,4)` or `(3,3,3)`; the last three make `Y` a cover of an
  arithmetic triangle group `(2,3,∞)`, `(2,4,∞)`, `(3,3,∞)` [Take1].
* [EstIUT] Prop. 2.1 (any field `F` of char 0): if `E ∖ 0` fails to admit an `F`-core, then
  `j(E) ∈ { 2¹⁴·31³/5³ = 488095744/125, 2²·73³/3⁴ = 1556068/81, 1728, 0 }`.
  Proof: [Sijs] Table 4 + [Sijs] Lemma 1.1.1 + [CanLift] Prop. 2.7.

The target of this repository is the [EstIUT] form (it is what IUT uses):

> **Theorem (CanLift 2.7 / EstIUT 2.1).** `k` a field of characteristic 0, `E/k` an elliptic
> curve, `X = E ∖ {0}`. If `X` does not admit a `k`-core then
> `j(E) ∈ {0, 1728, 2¹⁴·31³/5³, 2²·73³/3⁴}`.

The four values, with their groups ([Sijs] Tables 1, 4):

| case | trace triple `(tr α, tr β, tr αβ)` | `(x²,y²,z²)` | model | LMFDB | `j` |
|---|---|---|---|---|---|
| I | `(√5, 2√5, 5)` | `(5,20,25)` | `y² = x³ − 44x² − 16x` | 20.a1 | `2¹⁴·31³/5³` |
| II | `(√6, 2√3, 3√2)` | `(6,12,18)` | `y² = x³ − 4x² − 384x − 2304` | 24.a3 | `2²·73³/3⁴` |
| III | `(2√2, 2√2, 4)` | `(8,8,16)` | `y² = x(x² − 256)` | 32.a4 | `1728` |
| IV | `(3, 3, 3)` | `(9,9,9)` | `y² = x³ − 1728` | 36.a3 | `0` |

(The `j`-invariants of the four Weierstrass models are checked in Lean: `OrbicurveCores/JValues.lean`.
The same four values were found independently by the π₁ agent for `iut`'s `excJ`, also from
[Sijs] Table 4, LMFDB 36.a3, 32.a4, 20.a1, 24.a3.)

### 1.2 The notion of core

Mochizuki ([CanLift] Def. 2.1, Rem. 2.1.1): `Loc_k(X)` = generically scheme-like algebraic stacks
admitting a finite étale map to `X` (morphisms: finite étale `k`-morphisms, not necessarily over
`X`); `\overline{Loc}_k(X)` adds finite étale stack quotients; `X` *admits a `k`-core* iff
`\overline{Loc}_k(X)` has a terminal object. By [CanLift] Prop. 2.3(i),(ii) this depends only on
`X_{\bar k}` and is invariant under extension of algebraically closed fields.

Mathlib has schemes but no algebraic stacks, and the sibling definitions (`lana-agents/pi1`
branch `wp-orbicurve-pi1`, `iut` branch `wp-genuine-pi1`) did not exist when this was written
(in `iut` main, `HasCore` is still an abstract field of `EtalePi1Theory`). We therefore use the
following stack-free characterisation, which is a theorem over `ℂ` and is what we formalise:

* An **étale self-correspondence** of `X/k` is a pair of finite étale `k̄`-morphisms
  `α, β : C → X_{k̄}` from an irreducible `k̄`-scheme `C`. Its **support** is the image of the
  generic point of `C` in `X_{k̄} ×_{k̄} X_{k̄}` (the generic point of the irreducible curve
  `(α,β)(C) ⊆ X × X`).
* `AdmitsCore X :⇔` the set of supports of étale self-correspondences is **finite**.

Justification (over `ℂ`, `X = Γ\ℍ`): supports ↔ double cosets `ΓδΓ`, `δ ∈ Comm(Γ)`, and
`[Comm(Γ):Γ] = Σ_{ΓδΓ} [Γ : Γ ∩ δ⁻¹Γδ]` = Σ over supports of `deg(pr₁)`. Hence finitely many
supports ⇔ `[Comm(Γ):Γ] < ∞` ⇔ (by [Corr] §3 and [CanLift] Rem. 2.1.2) a core exists (the core is
`[Comm(Γ)\ℍ]`). Over an arbitrary algebraically closed `k` of char 0 reduce to `ℂ` by
[CanLift] Prop. 2.3(ii) / [Corr] Lemma 4.1. Reconciliation with the sibling `HasCore` is a
lemma to be proved once that definition exists (§4, R1).

The group-theoretic core notion used in the formal development:
`OrbicurveCores.AdmitsCore Γ :⇔ Γ.relIndex (commensurator Γ) ≠ 0` (finite index in its
commensurator, taken inside `SL(2, ℝ)`; the commensurator in `GL(2, ℝ)` would contain all scalars).
The scheme-level notion is `OrbicurveCores.OncePuncturedAdmitsCore` in `Statement.lean`
(finitely many supports of étale self-correspondences of `E_{k̄} ∖ {0}`). Only characteristic 0
is targeted: in characteristic `p` Mochizuki's cores fail to exist for every affine curve.

## 2. The proof, as a chain of lemmas

Notation: `Γ ⊆ SL(2,ℝ)` generated by `A, B` with `tr[A,B] = −2` (a (1;∞)-group, the preimage of
`π₁(X(ℂ))` under uniformisation), `x = tr A`, `y = tr B`, `z = tr AB`.

| # | Statement | Source | Status |
|---|---|---|---|
| A1 | Fricke: `tr[A,B] = x²+y²+z²−xyz−2`; so `tr[A,B] = −2 ⇔ x²+y²+z² = xyz`. Also `tr Aⁿ = Vₙ(tr A)` for monic `Vₙ ∈ ℤ[X]` | classical | **[done]** `Fricke.lean` (`tr_commutator`, `tr_pow`, `lucas_monic`) |
| A2 | Nielsen moves `(A,B) ↦ (B,A), (B,(AB)⁻¹), (A⁻¹,B)` preserve `⟨A,B⟩` and act on trace triples by permutations and Vieta flips `z ↦ xy − z` | classical | **[done]** `Takeuchi.lean` (`Realizes.swap/cycle/flip`) |
| A3 | Diophantine core of [Take2]: a reduced positive solution of `(X+Y+Z)² = XYZ`, `X ≤ Y ≤ Z`, `2(X+Y+Z) ≤ XY`, is `(9,9,9)`, `(8,8,16)`, `(5,20,25)` or `(6,12,18)` | [Take2] §3–4 | **[done]** `Markov.lean` (`reduced_classification`) |
| A4 | `Comm_{GL₂(ℝ)}(SL₂(ℤ)) ⊆ ℝ^×·GL₂(ℚ)`: all products `(g⁻¹)ᵢₐ gᵦⱼ` are rational; so `tr g · tr g⁻¹ ∈ ℚ` | classical | **[done]** `ArithTraces.lean` (`mul_mem_rat_of_mem_commensurator`, `tr_mul_tr_inv_mem_rat`) |
| A5 | If `Γ ⊆ SL₂(ℝ)` is arithmetic (some `GL₂(ℝ)`-conjugate is commensurable with `SL₂(ℤ)`, via Mathlib's `Subgroup.IsArithmetic`) then `tr(γ)² ∈ ℤ` for all `γ ∈ Γ` | [Take75], [MR] 8.3 | **[done]** `ArithTraces.lean` (`IsArithmeticSL.sq_tr_int`) |
| A6 | **Takeuchi (1;∞), necessity**: an arithmetic `⟨A,B⟩` with `tr[A,B] = −2` has a Nielsen-equivalent generating pair with `tr[A',B'] = −2` whose squared trace triple is one of the four. The degenerate triple `(0,0,0)` (a quaternion quotient) is excluded because arithmetic groups contain elements of infinite order | [Take2] Thm 4.1(i) (⇒) | **[done]** `Takeuchi.lean` (`takeuchi_one_infty`) |
| A6' | Fricke rigidity: an irreducible pair with hyperbolic `A` is determined by `(x,y,z)` up to `GL₂(ℝ)`-conjugacy. Four explicit pairs (table in `FourGroups.lean`). So arithmetic (1;∞)-groups are, up to Nielsen moves, signs and conjugacy, one of the four | [Sijs] Lemma 1.1.1 | **[done]** `FrickeRigidity.lean` (`exists_conj_of_tr_eq`), `FourGroups.lean` (`takeuchi_one_infty_conj`) |
| A7 | Arithmetic ⇒ no core: `[Comm(Γ):Γ] = ∞`, witnessed by a conjugate of `diag(√2, 1/√2)` none of whose powers lies in `Γ` (squared trace `2ⁿ+2+2⁻ⁿ ∉ ℤ`) | classical | **[done]** `Core.lean` (`IsArithmeticSL.not_admitsCore`) |
| A8 | Sharpness: each of the four explicit groups is arithmetic, hence admits no core. So Takeuchi's theorem holds as an iff, and (modulo Margulis) `¬AdmitsCore ⇔ IsTakeuchiConj` | [Take2] Thm 4.1(i) (⇐), [Sijs] Table 3 | **[done]** `Sharpness.lean`, `SharpnessData.lean` (certified coset enumeration, `decide`), `Classification.lean` (`isArithmeticSL_iff_isTakeuchiConj`, `not_admitsCore_iff_isTakeuchiConj`) |
| L | **Once-punctured torus groups have finite covolume**: real Nielsen descent to a triple satisfying the triangle inequalities (each step decreases `Σ|·|` by `≥ 2`), sign normalisation, Fricke rigidity to the normal form `A₀ = [[x−y/z, x/z²],[x, y/z]]`, `B₀ = [[y−x/z, −y/z²],[−y, x/z]]` (commutator `z ↦ z+2`), and a Ford-type covering criterion. Seven explicit isometric discs cover `[−1,1]`; the shrunk-disc reduction terminates without discreteness; the strip above height `η` has area `2/η` | Fricke; Ford | **[done]** `Fuchsian/FordCover.lean`, `Fuchsian/OneInftyLattice.lean` (`oneInftyFiniteCovolume`) |
| L' | **Once-punctured torus groups are free and discrete.** Ping-pong for the ideal quadrilateral with vertices `A₀⁻¹∞, 0, B₀⁻¹∞, ∞`, whose opposite sides are paired by the Fricke normal form generators: every nontrivial reduced word moves its interior off itself | Fricke, Poincaré | **[done]** `Fuchsian/PingPong.lean` (`injective_lift_normal`, `discreteTopology_normal`, `oneInfty_discrete`) |
| M1 | Dichotomy: `[Comm(Γ):Γ] = ∞` ⇒ `Comm(Γ)` dense. (a) A packing/covering volume bound: a discrete overgroup of a finite-covolume group contains it with finite index. (b) Elementary density criterion replacing the Lie algebra argument: a subgroup containing hyperbolic `A` and `B` with `tr[A,B] ≠ 2`, `tr B ≠ 0`, in which `1` is not isolated, is dense (rescale near-identity elements by powers of `A` to get full unipotent one-parameter groups) | [Greenberg 1974], [Zim] | **[done]** `Fuchsian/Covolume.lean` (`relIndex_ne_zero_of_discrete`), `Fuchsian/DenseSubgroup.lean`, `Fuchsian/DenseCriterion.lean`, `Fuchsian/Commensurator.lean` (`commensurator_dense`) |
| M2 | **Margulis** for non-uniform lattices of `SL₂(ℝ)`, standard form: dense commensurator ⇒ arithmetic | [Marg] IX, [Zim] 6.2.5, [BM] | **[stated]** as `MargulisDenseOneInfty` (`Fuchsian/Commensurator.lean`); `MargulisOneInfty` is derived from it (`margulisOneInfty_of_margulisDense`) |
| U1 | Uniformisation: `X(ℂ) ≅ Γ\ℍ` for a (1;∞)-group `Γ`, well defined up to conjugacy | Koebe; or Fricke–Teichmüller for `M_{1,1}` | **[missing]** |
| U2 | Algebraic ↔ analytic correspondences: `OncePuncturedAdmitsCore W ⇔ AdmitsCore Γ` (Riemann existence from `lana-agents/oka`, [CanLift] Prop 2.3 / [Corr] Lemma 4.1 to pass `k ⊆ k̄ ↪ ℂ`) | [Corr] §3–4 | **[missing]** |
| S1 | The four groups uniformise the four curves of §1.1 (`j` = 0, 1728 via automorphisms of order 6, 4; cases I, II via the Belyi maps of [Sijs] Lemmas 2.2.3, 2.2.9 and hauptmoduln of `Γ₀(5)`, `Γ₀(6)`) | [Sijs] §2–3 | **[missing]** (the `j`-invariants of the four models are **[done]**, `JValues.lean`) |
| F | Assembly | | group level: **[done]** conditionally only on `MargulisDenseOneInfty` (Margulis' theorem as usually stated), used only for "no core ⇒ one of the four" (`GroupMain.lean`, `canLift27_group_iff`); algebraic statement: **[stated]** (`Statement.lean`, `CanLift27`) |

### 2.1 Proof of A3 (as formalised)

Put `X = x², Y = y², Z = z², W = xyz`. Then `W² = XYZ` and (Markov-type relation)
`X + Y + Z = W`. The Vieta move `z ↦ xy − z` acts by `(X,Y,Z,W) ↦ (X, Y, XY − 2W + Z, XY − W)`.
If `W ≠ 0` then `W > 0` and `X,Y,Z > 0`; a triple with `X ≤ Y ≤ Z` is *reduced* if `4Z ≤ XY`
(i.e. `z ≤ xy − z`); otherwise the move strictly decreases `Z`, so descent on `X+Y+Z` terminates.
For a reduced triple: from `Y ≤ Z` and `Z` the smaller root of `t² − (xy)t + X + Y`, one gets
`Y(X − 4)² ≤ ...`, concretely `Y·(x−2) ≤ X` hence `4 < X ≤ 9`, `Y ≤ 21`, `Z ≤ XY/4`, and a finite
search leaves exactly the four listed triples.

### 2.2 Proof of A4–A5

`g ∈ Comm(SL₂(ℤ))` ⇒ `Γ' = SL₂(ℤ) ∩ g⁻¹SL₂(ℤ)g` has finite index `m`, so `u = [[1,m!],[0,1]]`,
`l = [[1,0],[m!,1]] ∈ Γ'` (pigeonhole on powers), and `g u g⁻¹, g l g⁻¹ ∈ SL₂(ℤ)`. Writing these out,
all products `g_{ij} g_{kl} / det g` are rational, so `g = λ·M` with `M ∈ M₂(ℚ)`.
For `γ` in an arithmetic `Γ = h Γ₀ h⁻¹` (`Γ₀` commensurable with `SL₂(ℤ)`): `γ₀ = h⁻¹γh ∈ Comm(SL₂ℤ)`
so `tr(γ₀)²/det γ₀ ∈ ℚ`; and `γ₀ᵐ ∈ SL₂(ℤ)` for some `m ≥ 1`, so the eigenvalues of
`γ₀/√det` are algebraic integers, hence `tr(γ)²/det γ` is a rational algebraic integer, i.e. in `ℤ`.

### 2.3 What is needed for M1–M2 (the shortest genuine route found)

**Is there a Margulis-free proof?** We looked for one and found none; below is why the obvious
candidates fail.

* *Cusp-set arguments* cannot work on their own: Long–Reid (*Pseudomodular surfaces*, Crelle 552,
  2002) construct **non-arithmetic once-punctured torus groups whose cusp set is exactly `ℙ¹(ℚ)`**.
  The cusp set therefore does not detect arithmeticity, even in the (1;∞) case.
* *Useful elementary reduction (valid, recorded for later)*: since a (1;∞)-group has one cusp
  orbit, `Comm(Γ) = Γ·Comm(Γ)_∞` and `Γ\Comm(Γ) ≅ Γ_∞\Comm(Γ)_∞`. So "no core" ⇔ infinitely many
  affine maps `z ↦ az + b` (necessarily `a ∈ ℚ_{>0}`) commensurate `Γ`. Horoball heights give
  more rigidity (the ratio `a·h(δ⁻¹c)/h(c)` takes finitely many values). We found no way to reach
  trace integrality from this without the superrigidity input.
* *Trace-field route* (the standard one, [MR] §8.3, [Take75]): `Comm(Γ) ⊆ PGL(A)` for the invariant
  quaternion algebra `A/kΓ`. If `Γ` is not arithmetic, then for some place `v` of `kΓ`
  (non-archimedean: a non-integral trace or `kΓ` transcendental; archimedean: `σ ≠ id` with
  `σ(Γ⁽²⁾)` unbounded) `Γ` is unbounded in `PGL(A_v)`, and `ρ_v : Comm(Γ) → PGL(A_v)` is defined.
  The missing step is always **commensurator superrigidity**: when `Comm(Γ)` is dense, `ρ_v`
  extends continuously to `SL₂(ℝ)`. That is impossible for non-archimedean `v` (connected group to
  a totally disconnected one while `Γ` embeds) and for `σ ≠ id`. For the non-uniform (1;∞) case
  the endgame is short: a unipotent (the commutator) rules out `kΓ ≠ ℚ`, and integrality at all
  primes gives `x², y², z², xyz ∈ ℤ`, so A3 applies.
* So the shortest rigorous route to M2 in our case is **commensurator superrigidity for lattices
  in `SL₂(ℝ)` with targets `PGL₂` over a local field (equivalently, isometries of a tree or of
  `ℍ²`)**: [Zim] Ch. 6 (Furstenberg boundary map `S¹ → Prob(ℙ¹(k_v))` via amenability of the
  Borel `P`; Moore/Howe–Moore ergodicity of `Γ` on `S¹`; proximality ⇒ point-valued; uniqueness ⇒
  `Comm(Γ)`-equivariance; density ⇒ the boundary map is a.e. rational ⇒ extension) or the CAT(−1)
  version [BM] (Patterson–Sullivan measures). Needed Mathlib infrastructure that does not exist:
  amenable groups / Markov–Kakutani for measure spaces, Howe–Moore for `SL₂(ℝ)`, measurable
  boundary theory, Bruhat–Tits tree of `PGL₂(K_v)`, and places of finitely generated fields.
  Rough size: 25–45k lines of Lean. M1 (dichotomy) about 3–6k more, done by hand for `SL₂(ℝ)`:
  a Lie-algebra argument plus Zariski density of a (1;∞) group, where `A, B, [A,B]` generate `M₂(ℝ)`.

### 2.3a Interface for U1 (uniformisation), to be proved in `lana-agents/oka` branch `wp-uniformization`

The group-level results here (`canLift27_group_iff`, `oneInftyFiniteCovolume`, `oneInfty_discrete`)
need from U1 exactly the following. It is stated without Riemann-surface infrastructure: a
holomorphic immersion of `ℍ` onto the affine Weierstrass curve, whose fibres are the orbits of a
once-punctured torus group.

```lean
/-- **U1: uniformisation of once-punctured elliptic curves.** -/
theorem uniformization_oncePunctured (W : WeierstrassCurve ℂ) [W.IsElliptic] :
    ∃ (A B : SL(2, ℝ)) (π : ℂ → ℂ × ℂ),
      tr (A * B * A⁻¹ * B⁻¹) = -2 ∧ tr A ≠ 0 ∧
      -- `π` is holomorphic on `ℍ` with injective differential (an immersion)
      (∀ z : ℍ, DifferentiableAt ℂ π z ∧ deriv π z ≠ 0) ∧
      -- `π` maps `ℍ` onto the affine curve `E(ℂ) ∖ {O}`
      (∀ z : ℍ, W.toAffine.Equation (π z).1 (π z).2) ∧
      (∀ x y : ℂ, W.toAffine.Equation x y → ∃ z : ℍ, π z = (x, y)) ∧
      -- the fibres of `π` are exactly the orbits of `Γ = ⟨A, B⟩`
      (∀ z w : ℍ, π z = π w ↔ ∃ γ ∈ Subgroup.closure {A, B}, γ • z = w)
```

Here `tr` is `OrbicurveCores.tr` (the trace of an element of `SL(2, ℝ)`), `ℍ` is Mathlib's
`UpperHalfPlane`, and `γ • z` is Mathlib's `SL(2, ℝ)`-action. The data are unique up to
`GL(2, ℝ)`-conjugation and signs of `A, B`, by lifting to the universal cover. Uniqueness is not
needed from the U1 agent; it follows from the fibre condition by covering theory, which U2 does
here. U2 will use this map together with Riemann existence (`oka`) to translate finite étale
covers and correspondences of `E ∖ O` into finite-index subgroups and commensurator elements
of `Γ`.

### 2.3b Blueprint for M2 (Margulis for once-punctured torus groups)

**Target.** `MargulisDenseOneInfty`: for a `(1;∞)`-group `Γ = ⟨A, B⟩` with dense commensurator
`Δ`, `Γ` is arithmetic. By `takeuchi_one_infty` and sharpness it suffices to show
`tr(γ)² ∈ ℤ` for all `γ ∈ Γ`. We may assume `Γ` is in Fricke normal form. It is then a free,
discrete lattice with explicit fundamental domains (`OneInftyLattice.lean`, `PingPong.lean`).

**Route** (Margulis / Zimmer Ch. 6 / D. W. Morris's notes "The commensurability criterion for
arithmeticity (after Margulis)", specialised to `G = SL₂(ℝ)`, `P` = upper triangular):

* **C7 (algebra).**
  * `F = ℚ(x, y, z)` contains the entries of `Γ`, and `F' = ℚ(x², y², z², xyz)` contains all
    `tr(γ)²`.
  * Every `δ ∈ Δ` is a real multiple of a matrix in `GL₂(F)`, since the `F`-span of any
    finite-index subgroup of `Γ` is `M₂(F)` (as in A4). This gives `ρ : Δ → PGL₂(F)`.
  * *(a) `F' = ℚ`.* For every field embedding `σ : F → ℂ`, `σ ∘ ρ : Δ → PGL₂(ℂ)` has unbounded
    image of `Γ`: `σ` fixes the rational unipotent `K² = T₄`. So by superrigidity (C5) it
    extends to a continuous `Φ_σ : SL₂(ℝ) → PGL₂(ℂ)`. By C6, `σ` is the identity on `F'`, hence
    `F' = ℚ`. This covers the transcendental case too.
  * *(b) Integrality.* For each prime `𝔭` of the number field `F`, `ρ_𝔭 : Δ → PGL₂(F_𝔭)`. If
    `ρ_𝔭(Γ)` were unbounded, superrigidity would give a continuous map from the connected
    `SL₂(ℝ)` to the totally disconnected `PGL₂(F_𝔭)`, which is trivial; impossible. So `Γ` is
    `𝔭`-bounded for all `𝔭`, hence `tr(γ)² ∈ ℚ ∩ ℤ̄ = ℤ`.
* **C5 (commensurator superrigidity).**
  * Setting: `Γ ≤ SL₂(ℝ)` a lattice, `Δ ⊇ Γ` a dense subgroup of `Comm(Γ)`,
    `k ∈ {ℂ, finite extensions of ℚ_p}`, and `ρ : Δ → PGL₂(k)` with `ρ(Γ)` unbounded and
    irreducible (no invariant point or pair of points in `ℙ¹(k)`).
  * Conclusion: `ρ` extends to a continuous homomorphism `SL₂(ℝ) → PGL₂(k)`.
  * Proof via a `Γ`-equivariant measurable `ψ : ℙ¹(ℝ) → ℙ¹(k)` (C2 + C3), uniqueness of such
    maps for finite-index subgroups (C1 + C4), hence `Δ`-equivariance. Then all `G`-translates of
    `ψ` lie in one `PGL₂(k)`-orbit (tameness of `PGL₂(k)` acting on measurable maps), giving a
    measurable, hence continuous, homomorphism extending `ρ`.
* **C1 (ergodicity).** A lattice acts ergodically on `ℙ¹(ℝ)` and on `ℙ¹(ℝ) × ℙ¹(ℝ)` (Lebesgue
  class). This is Moore's theorem via the Mautner phenomenon on `L²(Γ \ G)`; finite covolume is
  `oneInftyFiniteCovolume`.
* **C2 (Furstenberg lemma).**
  * Statement: there is a `Γ`-equivariant measurable `ψ : ℙ¹(ℝ) → Prob(ℙ¹(k))`, obtained from a
    fixed point of the amenable `P = AN` acting on the compact convex set of `Γ`-equivariant
    measurable maps `G → Prob(ℙ¹(k))`.
  * That set is realised as measures on (fundamental domain) × `ℙ¹(k)` with fixed first
    marginal, compact by Prokhorov (Mathlib).
  * Needs Markov–Kakutani for commuting affine maps, which is not in Mathlib.
* **C3 (tameness).** `PGL₂(k)` acting on `Prob(ℙ¹(k))`: orbits are locally closed, and the
  stabiliser of a measure is compact or fixes a point or a pair of points (explicit Cartan
  decomposition and proximality for `PGL₂` over local fields). Irreducibility and unboundedness
  of `ρ(Γ)` then upgrade `ψ` to a point map.
* **C4 (ergodicity vs. tameness).** A measurable equivariant map from an ergodic action to a tame
  (countably separated) action is essentially constant modulo the group.
* **C6 (continuous homomorphisms).** A continuous homomorphism `SL₂(ℝ) → PGL₂(K)` is trivial for
  `K` totally disconnected. For `K = ℂ`, the continuous class function `g ↦ tr(Φ g)²/det(Φ g)`
  agrees with `σ ∘ tr²` on the dense `Δ`, which forces `σ = id` on `F'`. The planned route is
  one-parameter subgroups and Lie-algebra homomorphisms.

**Estimate.**

| part | lines |
|---|---|
| C1 | 4–6k |
| C2 | 5–8k |
| C3 | 3–5k |
| C4 | 1–2k |
| C5 assembly | 2–3k |
| C6 | 2–4k |
| C7 | 2–4k |
| **total** | **about 20–30k** |

**Already available.** Discreteness, finite covolume, the explicit fundamental domains, M1, and
the finish (`takeuchi_one_infty`, sharpness).

### 2.4 What is needed for U1, U2, S1

* U1: Mathlib has `ℍ`, the `SL₂(ℝ)` action, the modular group and `j` (and `lana-agents/heights`
  has lattice uniformisation of elliptic curves and surjectivity of `j`). It has **no**
  uniformisation theorem and no Fuchsian group theory beyond `SL₂(ℤ)` (cusps, arithmetic subgroups
  via `Subgroup.IsArithmetic`, `DedekindEta`). Two routes: (a) the uniformisation theorem for
  hyperbolic Riemann surfaces (Perron/Green's function), about 15–30k lines; (b) Fricke space of
  once-punctured tori `{x²+y²+z²=xyz, x,y,z>2}`, the conformal compactification map to `M_{1,1}`,
  and surjectivity by invariance of domain plus properness, about 10–20k lines. Both are large.
* U2: `lana-agents/oka` proves Riemann existence (`Oka.Analytification.RET`); still needed are the
  comparison of covering spaces of `Γ\ℍ` with subgroups of `Γ`, compact Riemann surfaces vs
  algebraic curves for the correspondences, and the Lefschetz principle ([CanLift] 2.3(ii),
  [Corr] 4.1: rigidity of finite étale maps between hyperbolic curves) to move between `k`, `k̄`
  and `ℂ`. Several thousand lines, depending on how much `oka` supplies.
* S1: cases III and IV follow from automorphisms (a (1;∞)-group normal in the triangle group
  `(2,4,∞)`, resp. `(2,3,∞) = PSL₂(ℤ)`, with cyclic quotient of order 4, resp. 6, fixing the cusp
  ⇒ `Aut(E,0) ⊇ μ₄`, resp. `μ₆` ⇒ `j = 1728`, resp. `0`). Cases I and II need explicit
  modular-function computations with hauptmoduln of `Γ₀(5)` and `Γ₀(6)` (Mathlib has
  `DedekindEta`, but no dimension formulas or Sturm bounds for level `N`), or verification of
  [Sijs]'s Belyi maps via monodromy. Hard, computer-assisted in the source.

### 2.5 Sharpness (A8)

For cases I–III the words of even length in `Aᵢ, Bᵢ` (for II: even in each letter) are integral
matrices up to an explicit scalar. `Γᵢ ∩ SL₂(ℤ)` has finite index in `SL₂(ℤ)` because of a cover
certificate: a Schreier transversal (12, 24, 12, 6 cosets of `±(Γᵢ ∩ SL₂ℤ)`, as in [Sijs] Table 3,
doubled here to absorb signs), with a word for every transversal element and every generator
`S^{±1}, T^{±1}`. It has finite index in `Γᵢ` because of a transversal certificate by parity
classes. The certificates were found by the Python scripts in `scripts/`: coset enumeration,
using greedy reduction in `Γᵢ` as the membership oracle. They are checked in Lean by `decide` on
quadruples of integers.

## 3. Estimate

The genuinely formalisable-now layer is A1–A8 plus the conditional assembly. It is done (see
the table). The remaining pieces M1, M2, U1, U2 and S1 are each research-scale formalisation
projects:

| piece | new infrastructure | estimate (Lean lines) |
|---|---|---|
| M1 dichotomy | done (about 1.2k lines, including the finite-covolume proof L) | — |
| M2 Margulis (non-uniform, `SL₂(ℝ)`) | amenability, ergodicity, boundary maps, trees, valuations | 25–45k |
| U1 uniformisation of `E ∖ 0` | uniformisation theorem or Fricke-space route | 10–30k |
| U2 algebraic ↔ analytic cores | covering theory + `oka` + Lefschetz principle | 5–15k |
| S1 identification of the four curves | automorphisms (III, IV); hauptmoduln or Belyi (I, II) | 5–15k |

Total: roughly 50–110k lines, which is comparable to the whole `oka` repository.

## 4. Reconciliation items

* R1 (partly done): `lana-agents/pi1` branch `wp-orbicurve-pi1` (pinned at `1f39d5b` as a Lake
  dependency) defines genuine `k`-cores for affine orbicurves (`AffOrbicurve.IsCoreOf`,
  `IsArithmetic`: coarse Dedekind ring plus stabiliser orders, [CanLift] Def. 2.1). It also
  defines `punctured E`, `hemi E`, `excJ`, and the statement `AffOrbicurve.CanLift27` (core =
  hemi-elliptic quotient for non-exceptional `j`). `Reconcile.lean` proves
  `exceptionalJ = excJ` and that pi1's `CanLift27` implies the [EstIUT] form
  `CanLift27Genuine` stated with genuine cores. Still open: the equivalence of
  `IsArithmetic (punctured E)` with `¬ OncePuncturedAdmitsCore` (§1.2). Over `ℂ` both are
  `[Comm(Γ):Γ] = ∞`, which needs U1–U2.
* R2: `iut`'s `EtalePi1Theory.excJ` / `hasCore_oncePunctured` should be instantiated with the
  four values of §1.1 (a finite set of rationals), and [EstIUT] 2.1 should be cited for them.
* R3: the stronger pi1 form (the core **is** `(E∖0)/±1`) additionally needs the Riemann–Hurwitz
  step of [CanLift] 2.7: the ramification types `(2,2,2,2), (2,3,6), (2,4,4), (3,3,3)` for
  `E → Z^crs`, together with arithmeticity of the triangle groups `(2,3,∞), (2,4,∞), (3,3,∞)`.
  At the group level this is: `Comm(Γ)` for non-arithmetic `Γ` is the `(0;2,2,2,∞)` group
  `⟨Γ, ι⟩`. The numerical Riemann–Hurwitz enumeration is **[done]** (`RiemannHurwitz.lean`,
  `riemannHurwitz_solutions`).
