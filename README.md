# orbicurve-cores

Once-punctured elliptic curves failing to admit a core.

## Goals

Formalise Proposition 2.7 of Mochizuki, *The Absolute Anabelian Geometry of Canonical Curves* (<https://www.kurims.kyoto-u.ac.jp/~motizuki/Canonical%20Liftings.pdf>):

> If the once-punctured elliptic curve associated to `E_F` fails to admit an "`F`-core", then there are only four possibilities for the `j`-invariant of `E_F`.

The four exceptional values `{0, 1728, 2¹⁴·31³/5³, 2²·73³/3⁴}` are `OrbicurveCores.exceptionalJ`
(`JValues.lean`, checked against Sijsling's models). They agree with pi1's `AffOrbicurve.excJ`
(`exceptionalJ_eq_excJ`).

## Status (`main`)

**[CanLift] Prop. 2.7 is proved, unconditionally, over every field of characteristic `0`**,
with the genuine `k`-cores of `lana-agents/pi1` ([CanLift] Def. 2.1):

* `OrbicurveCores.U2.canLift27C : OrbicurveCores.CanLift27C` (`U2/Assembly.lean`): for an elliptic
  curve `E / ℂ` whose `j` is not exceptional, the hemi-elliptic quotient `(E ∖ {0}) / {±1}`
  (`AffOrbicurve.hemi E`) is the `ℂ`-core of `E ∖ {0}` (`AffOrbicurve.IsCoreOf`);
* `OrbicurveCores.canLift27 : AffOrbicurve.CanLift27.{u}` and
  `OrbicurveCores.canLift27Genuine : OrbicurveCores.CanLift27Genuine.{u}` (`Genuine/Final.lean`):
  the same over every field `k : Type u` of characteristic `0`, in every universe, and the
  [EstIUT] Prop. 2.1 form (a `k`-arithmetic `E ∖ {0}` has exceptional `j`). They come from
  `U2.canLift27C` by the transfer `hemiCoreTransfer` (`Genuine/Transfer/`).

Evidence: no `sorry` in any `.lean` file (`git grep`), no `axiom` declarations or
`native_decide`, and `#print axioms` (against the build at this revision inside `iut`) reports
only `propext`, `Classical.choice`, `Quot.sound` for `U2.canLift27C`,
`canLift27_group_unconditional`, `M2.margulisDenseOneInfty`, `s1NonExceptional`, `uniformization`
and `isArithmeticSL_iff_isTakeuchiConj`. This includes the `oka` and `pi1` dependencies. The same
holds (checked in this repository's build) for `canLift27Genuine`, `canLift27`, `hemiCoreTransfer`,
`Alt.canLift27C`, `Alt.canLift27Genuine`, `commIndexFour` and `Abhyankar.abhyankar`.

The proof, in the blueprint's labels (see `Blueprint.md` for sources and the lemma DAG):

* **Fuchsian groups (A1–A8, L, M1).** Takeuchi's classification of arithmetic `(1;∞)`-groups
  (`takeuchi_one_infty`, `takeuchi_one_infty_conj`): Fricke identities, trace integrality,
  Nielsen descent, the Diophantine lemma and Fricke rigidity up to `GL(2,ℝ)`-conjugacy;
  arithmetic groups admit no core (`IsArithmeticSL.not_admitsCore`); sharpness by certified coset
  enumeration (`isArithmeticSL_iff_isTakeuchiConj`); once-punctured torus groups are free,
  discrete lattices (`oneInftyFiniteCovolume`, `oneInfty_discrete`); infinite index in the
  commensurator forces a dense commensurator (`commensurator_dense`).
* **Margulis (M2).** The commensurator theorem for once-punctured torus groups,
  `M2.margulisDenseOneInfty`, via commensurator superrigidity into `PGL₂(ℂ)` and `PGL₂(ℚ_p)`
  (`M2.commensurator_superrigidity`): Moore double ergodicity, the Furstenberg boundary map, point
  maps, extension to a continuous homomorphism, unipotent rigidity.
* **Group-level CanLift 2.7.** `canLift27_group_unconditional`: a `(1;∞)`-group admits no core
  iff it is one of Takeuchi's four groups (`not_admitsCore_iff_isTakeuchiConj` + Margulis).
* **U1 (uniformisation).** `uniformization`: `E ∖ {0}` over `ℂ` is `ℍ / ⟨A, B⟩` with
  `tr [A, B] = -2`, restating `Uniformization.uniformization_oncePunctured` from `lana-agents/oka`;
  `exists_uniformization_core_iff` combines it with the group-level result.
* **S1 (which curves the four groups uniformise).** `S1.exceptional_of_takeuchi`,
  `S1.not_takeuchi_of_nonExceptional`, packaged as `s1NonExceptional : S1NonExceptional`, using
  Belyi certificates for the four model curves (`S1/Certificates.lean`), orbifold lifting and
  rigidity.
* **U2 (algebraic ↔ analytic).** Theorem G (`U2.theoremG`): for finite étale `Z → E ∖ {0}` and
  `Z → Y` over `ℂ` (non-exceptional `j`), the pullback of `x` comes from `ℂ[Y]`, via the Galois
  closure of the cover, automorphisms lying in the commensurator (`U2.mobius_mem_commensurator`,
  `U2.fixes_xP`) and oka's R3 (`U2.r3`). Uniqueness of the map to the hemi-elliptic curve:
  `U2.hemi_poly_unique` (fibre count + Riemann–Hurwitz).
* **Transfer to arbitrary fields** (`Genuine/Transfer/`, [CanLift] Prop. 2.3 and the Lefschetz
  principle). `hemiCoreTransfer : CanLift27C → AffOrbicurve.CanLift27.{u}`: the data of a
  violation over `k` (finitely many elements of coordinate rings) are spread out to a subfield
  `k₀ ⊆ ℂ` with `k₀ : Type`; base change to `ℂ` splits into components that are affine
  orbicurves (DVR criterion, reduced fibres, ramification indices); the core property over `ℂ` is
  pulled back along `k₀ → ℂ` and `k₀ → k` (`isCoreOf_hemi_of`: descent of `x` plus rigidity).
  pi1's `AffOrbicurve.canLift27_of_complex` (Lefschetz principle via countable algebraically
  closed subfields) proves the same for fields in `Type` (`CanLift27.{0}`); `iut` uses that.

**Alternative proofs and generic lemmas** (developed independently on the branch `wp-canlift27`
and ported here; see `Blueprint.md` §2.6):

* **R3 by elementary group theory**: `commIndexFour : CommIndexFour` (`Genuine/Involution.lean`,
  `Genuine/CuspStructure.lean`, `Genuine/CommIndex.lean`, `Genuine/TranslationCase.lean`): a
  once-punctured torus group admitting a core has index `4` in its commensurator. Sharp Shimizu
  lemma, absence of elliptic elements, pigeonhole and Markov-type numerics reduce the translation
  case to Takeuchi's groups. The main proof uses oka's analytic R3 (`U2.r3`) instead.
* **U2 by rigidity and Abhyankar's lemma**: `Alt.canLift27C : CanLift27C` (`Genuine/AltU2.lean`)
  proves [CanLift] 2.7 over `ℂ` from `commIndexFour`, the analytic rigidity half
  `Alt.u2Rigidity` (`Genuine/Rigid/`: lifts of the uniformisation to finite étale covers as
  holomorphic families of points, orbifold covering criterion, deck group `= Comm(Γ)`), and the
  descent half `Alt.u2Descent` (`Genuine.hemiDescends_of`, `Abhyankar.compositumSeparates`). It
  does not use `U2.r3`, oka's `le_pmDeck_or` or `U2.theoremG`. `Alt.canLift27Genuine` is
  `CanLift27Genuine` along this route.
* **Abhyankar's lemma** (`ForMathlib/Abhyankar/`, generic commutative algebra): for a Dedekind
  domain `B` of finite type over `ℂ` with fraction field `K` and finite `K ⊆ F₁, F₂ ⊆ K̄`, if all
  primes of `F₁` and `F₂` over `y` have the same ramification index, then `F₁ ⊔ F₂` is unramified
  over `F₁` at the primes over `y` (`Abhyankar.abhyankar`); with ramification in towers and
  composita, Kummer steps, and fibres of unramified extensions (`Abhyankar.card_fib`,
  `Abhyankar.exists_separating`).

## Dependencies

* Mathlib `v4.32.0`;
* `lana-agents/pi1` (pinned `2c1e2f0`): affine orbicurves, finite étale morphisms and genuine
  `k`-cores (`AffOrbicurve.IsCoreOf`, `AffOrbicurve.IsArithmetic`, `punctured`, `hemi`, `excJ`);
* `lana-agents/oka` (pinned `75dcdc3`, branch `wp-u2`): uniformisation of `E ∖ {0}` (U1), R3 and
  finite étale algebras over holomorphic functions on `ℍ`. `oka` pins `lana-agents/heights` at
  `3539e2a`.

No Θ-data or `iut` dependency.

## Use in `iut`

`lana-agents/iut` pins this repository at `61616dc` (`main`). `Iut/Anabelian/CanLift.lean`
proves `Iut.Anabelian.canLift27 : AffOrbicurve.CanLift27.{0}` (CanLift 2.7 over every field of
characteristic `0`) as `AffOrbicurve.canLift27_of_complex OrbicurveCores.U2.canLift27C` (with `pi1` at `7647d28`), and
from it `Iut.Anabelian.hasCore_oncePunctured`: the once-punctured elliptic curves of the model
orbicurves have the core `X/{±1}` unless `j(E)` is exceptional.

## Layout

Lean 4 project pinned to `leanprover/lean4:v4.32.0` with Mathlib at `v4.32.0`.
Library sources live under `OrbicurveCores/`, and every file must be imported from
the root module `OrbicurveCores.lean`.

```bash
lake exe cache get                       # fetch the Mathlib build cache
lake build                               # build the library
lake exe mk_all --lib OrbicurveCores --git   # regenerate the root module after adding files
```

## Validation

`.orchestra/` tells the agent harness how to prepare the environment and how to
check that a change is complete:

* `before.sh` warms the Mathlib build cache before work starts.
* `validation.sh` checks the worktree is clean, that every `.lean` file is
  imported (`mk_all --check`), and that everything builds with warnings as
  errors (`lake build --wfail`).

Run it locally with `bash .orchestra/validation.sh`.

## Tracker

Work is tracked in taxis: [#10](https://taxis.lana.merten.dev/issues/10)

License: Apache 2.0 (see LICENSE)
