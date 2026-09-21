/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.RPnTopClassAlphaPower
import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.RPnCohomologyRingBridge
import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.ModTwoDegreeComparison
import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.ConstructRPAlpha

/-!
# Conditional odd-map cohomological comparison

Assembles the reusable implication from explicit RP cohomology generator, cup-power,
transfer/naturality, and mod-two degree data to odd integer degree. These conditional interfaces
are used by later assembly modules; the stable public theorem is the unconditional endpoint in
`SphereOddDegree.Final`.
-/

noncomputable section

open CategoryTheory

namespace SphereOddDegree

/-! ## 1. Element-level double-cover naturality (genuine) -/

/-- **Element-level naturality square of the double cover** at degree `k`.
Applying the morphism identity `inducedOnRP_pullback_naturality` to a cohomology
class `a ∈ Hᵏ(RPⁿ; F₂)` gives

```text
proj^*(fbar^* a) = f^*(proj^* a) in Hᵏ(Sⁿ; F₂).
```
-/
theorem inducedOnRP_pullback_naturality_apply {n : ℕ} (f : C(Sphere n, Sphere n))
    (hf : IsOddMap f) (k : ℕ) (a : rpCohomology n k) :
    projPullback n k (inducedOnRPPullback f hf k a)
      = spherePullback f k (projPullback n k a) := by
  have h := inducedOnRP_pullback_naturality f hf k
  have happ := congrArg (fun φ : rpCohomology n k ⟶ sphereCohomology n k => φ a) h
  simpa only [ModuleCat.comp_apply] using happ

/-- **`f^*` fixes the pulled-back top class.** If the descended odd map `fbar`
fixes a top class `a ∈ Hⁿ(RPⁿ; F₂)` (`fbar^* a = a`), then the sphere self-map
`f` fixes its image `proj^* a ∈ Hⁿ(Sⁿ; F₂)` under the double-cover pullback:

```text
f^*(proj^* a) = proj^* a.
```

This is the genuine, unconditional cohomological core of the comparison: it is
the push of `fbar^*(αⁿ) = αⁿ` across the double-cover naturality square. -/
theorem spherePullback_fixes_projPullback {n : ℕ} (f : C(Sphere n, Sphere n))
    (hf : IsOddMap f) (a : rpCohomology n n)
    (ha : inducedOnRPPullback f hf n a = a) :
    spherePullback f n (projPullback n n a) = projPullback n n a := by
  have h := inducedOnRP_pullback_naturality_apply f hf n a
  rw [ha] at h
  exact h.symm

/-! ## 2. Conditional top-class / degree comparison -/

/-- **Conditional mod-2 degree comparison from the top class.**

Given a top class `a ∈ Hⁿ(RPⁿ; F₂)` that is fixed by the descended odd map
(`fbar^* a = a`) and whose double-cover image `proj^* a` is a nonzero element of
`Hⁿ(Sⁿ; F₂)`, the *only* remaining input is the **top-class / degree comparison**
`hcmp`: that `f^*` fixing the nonzero sphere top class forces
`degree f ≡ 1 (mod 2)`. Under that input the mod-2 degree is `1`.

The genuine work — pushing `fbar^* a = a` to `f^*(proj^* a) = proj^* a` via the
double-cover naturality square — is done by `spherePullback_fixes_projPullback`;
`hcmp` then consumes that fact. -/
theorem oddMap_degree_mod_two_eq_one_of_top_class_comparison {n : ℕ}
    (e : SphereTopHomologyIso n) (f : C(Sphere n, Sphere n)) (hf : IsOddMap f)
    (a : rpCohomology n n)
    (hfix : inducedOnRPPullback f hf n a = a)
    (hne : projPullback n n a ≠ 0)
    (hcmp : spherePullback f n (projPullback n n a) = projPullback n n a →
            projPullback n n a ≠ 0 → (degreeOfIso e f : ZMod 2) = 1) :
    (degreeOfIso e f : ZMod 2) = 1 :=
  hcmp (spherePullback_fixes_projPullback f hf a hfix) hne

/-- **Conditional oddness of the degree from the top class.** The `Odd` phrasing
of `oddMap_degree_mod_two_eq_one_of_top_class_comparison`, obtained through the
parity bridge `degreeOfIso_intCast_zmodTwo_eq_one_iff_odd`. -/
theorem oddMap_degree_odd_of_top_class_comparison {n : ℕ}
    (e : SphereTopHomologyIso n) (f : C(Sphere n, Sphere n)) (hf : IsOddMap f)
    (a : rpCohomology n n)
    (hfix : inducedOnRPPullback f hf n a = a)
    (hne : projPullback n n a ≠ 0)
    (hcmp : spherePullback f n (projPullback n n a) = projPullback n n a →
            projPullback n n a ≠ 0 → (degreeOfIso e f : ZMod 2) = 1) :
    Odd (degreeOfIso e f) :=
  (degreeOfIso_intCast_zmodTwo_eq_one_iff_odd e f).mp
    (oddMap_degree_mod_two_eq_one_of_top_class_comparison e f hf a hfix hne hcmp)

/-! ## 3. Conditional final theorem from the full cohomological chain -/

/-- **Conditional final odd-map degree theorem from the full cohomological
chain.** This is the assembled conditional version of

```text
f odd ⇒ Odd (degree f),
```

with the cohomological inputs as explicit hypotheses. Concretely:

* `alpha` — the degree-one class `α ∈ H¹(RPⁿ; F₂)`;
* `alphaPow` — the top class `αⁿ ∈ Hⁿ(RPⁿ; F₂)`;
* `hα_fixed` — `fbar^*(α) = α`, the action of the descended odd map on `α`;
* `hpow` — pullback preserves powers, `fbar^*(α)=α ⇒ fbar^*(αⁿ)=αⁿ`;
* `hne` — `proj^* αⁿ ≠ 0`, the nonvanishing of the top class on the sphere;
* `hcmp` — the top-class / degree comparison.

The internal step `fbar^*(αⁿ)=αⁿ ⇒ f^*(proj^* αⁿ)=proj^* αⁿ` follows from
`spherePullback_fixes_projPullback`, and the parity bridge yields the final oddness statement. -/
theorem oddMap_degree_odd_of_cohomological_inputs {n : ℕ}
    (e : SphereTopHomologyIso n) (f : C(Sphere n, Sphere n)) (hf : IsOddMap f)
    (alpha : rpCohomology n 1) (alphaPow : rpCohomology n n)
    (hα_fixed : inducedOnRPPullback f hf 1 alpha = alpha)
    (hpow : inducedOnRPPullback f hf 1 alpha = alpha →
            inducedOnRPPullback f hf n alphaPow = alphaPow)
    (hne : projPullback n n alphaPow ≠ 0)
    (hcmp : spherePullback f n (projPullback n n alphaPow) = projPullback n n alphaPow →
            projPullback n n alphaPow ≠ 0 → (degreeOfIso e f : ZMod 2) = 1) :
    Odd (degreeOfIso e f) :=
  oddMap_degree_odd_of_top_class_comparison e f hf alphaPow (hpow hα_fixed) hne hcmp

/-! ## 3b. Conditional final theorem from the single ring-bridge hypothesis -/

/-- **Conditional final odd-map degree theorem from the single ring-bridge
hypothesis.** This is the same conclusion as
`oddMap_degree_odd_of_cohomological_inputs`, but with the four separate RPⁿ-side
inputs (`alpha`, `alphaPow`, `hpow`, and the RPⁿ-level nonvanishing `αⁿ ≠ 0`)
replaced by the **single** model-side ring-bridge hypothesis
`Φ : RPnCohomologyToModelHom n` (`RPnCohomologyRingBridge.lean`).

Given the bridge `Φ`:

* the degree-one class is `α := Φ.alpha ∈ H¹(RPⁿ; F₂)`;
* the top class is its `n`-th cup power `αⁿ := cupPowZMod2 Φ.alpha n ∈ Hⁿ(RPⁿ; F₂)`;
* the step `fbar^*(α) = α ⇒ fbar^*(αⁿ) = αⁿ` is discharged automatically by the
 proved cohomology-level cup-power naturality
 (`rpAlpha_power_top_fixed_ne_zero`), and `αⁿ ≠ 0` is supplied by the bridge as
 well, so neither needs to be assumed separately.

The only remaining inputs are the genuinely sphere and degree side ones: the action
hypothesis `hα_fixed` (`fbar^*(α) = α`, gated on the degree-one UCT identifying
`α`), the sphere nonvanishing `hne`, and the top-class/degree comparison `hcmp`.
Thus the RPⁿ top-class story is reduced to the one explicit input `Φ`. -/
theorem oddMap_degree_odd_of_ringBridge {n : ℕ}
    (e : SphereTopHomologyIso n) (f : C(Sphere n, Sphere n)) (hf : IsOddMap f)
    (Φ : RPnCohomologyToModelHom n)
    (hα_fixed : (inducedOnRPPullback f hf 1).hom Φ.alpha = Φ.alpha)
    (hne : projPullback n n (cupPowZMod2 Φ.alpha n) ≠ 0)
    (hcmp : spherePullback f n (projPullback n n (cupPowZMod2 Φ.alpha n))
              = projPullback n n (cupPowZMod2 Φ.alpha n) →
            projPullback n n (cupPowZMod2 Φ.alpha n) ≠ 0 →
            (degreeOfIso e f : ZMod 2) = 1) :
    Odd (degreeOfIso e f) := by
  obtain ⟨hfix, _hnz⟩ := rpAlpha_power_top_fixed_ne_zero Φ f hf hα_fixed
  exact oddMap_degree_odd_of_top_class_comparison e f hf (cupPowZMod2 Φ.alpha n) hfix hne hcmp

/-! ## 3c. The single required input, packaged as one named comparison

Everything above keeps the genuine *topological* coefficient-reduction / top-class
comparison as a per-call hypothesis `hcmp`. We now isolate it once and for all as a
single named predicate `ModTwoTopClassComparison e`, uniform over **all** sphere
self-maps and **all** nonzero top `F₂`-classes. The final odd-map theorem then
follows from this one input together with the *proved* unconditional ingredients
(the double-cover naturality core `spherePullback_fixes_projPullback` and the
parity bridge `degreeOfIso_intCast_zmodTwo_eq_one_iff_odd`), with **no extra
parity assumptions**. This is the exact form of the required input. -/

/-- **The mod-two top-class / degree comparison.** This interface packages the
coefficient-reduction statement consumed by the conditional assembly. Relative to a chosen identification
`e : SphereTopHomologyIso n` (which fixes the integer degree `degreeOfIso e`), it
asserts: whenever a self-map `f` of `Sⁿ` **fixes a nonzero top class**
`c ∈ Hⁿ(Sⁿ; F₂)` (`f^* c = c`, `c ≠ 0`), its integer degree is **odd mod 2**
(`(degree f : ZMod 2) = 1`).

It states that the action on a nonzero top mod-two cohomology class determines
the parity of the integer degree. Downstream coefficient-reduction modules
construct this comparison. -/
def ModTwoTopClassComparison {n : ℕ} (e : SphereTopHomologyIso n) : Prop :=
  ∀ (f : C(Sphere n, Sphere n)) (c : sphereCohomology n n),
    spherePullback f n c = c → c ≠ 0 → (degreeOfIso e f : ZMod 2) = 1

/-! ### Reduction of the comparison to the top `F₂`-homology scalar action

The comparison `ModTwoTopClassComparison e` is here reduced — fully formalized,
using only the library's *proved* universal-coefficient machinery over `F₂`
(`kroneckerMap_naturality_apply` and `kroneckerMap_injective`) — to the single,
precise statement that the `F₂` pushforward on the top homology `Hₙ(Sⁿ; F₂)` acts
as the scalar `(degree f mod 2)`. This isolates the exact homological scalar statement from which the comparison
follows. -/

/-- **The top `F₂`-homology scalar action.** Relative to a chosen integral
identification `e : SphereTopHomologyIso n`, this asserts that the `F₂` homology
pushforward `f_* : Hₙ(Sⁿ; F₂) → Hₙ(Sⁿ; F₂)` of every self-map `f` acts as the
scalar `(degreeOfIso e f : ZMod 2)`.

Mathematically this is the conjunction of (i) `Hₙ(Sⁿ; F₂)` being one-dimensional
over `F₂` (so `f_*` is a scalar) and (ii) that scalar being the mod-`2` reduction
of the integer degree (coefficient-change compatibility `Hₙ(-;ℤ)⊗F₂ → Hₙ(-;F₂)`).
Downstream sphere-homology and coefficient-reduction modules prove this scalar
action for the canonical orientation. -/
def ModTwoTopHomologyScalar {n : ℕ} (e : SphereTopHomologyIso n) : Prop :=
  ∀ (f : C(Sphere n, Sphere n)) (z : homologyZMod2 (TopCat.of (Sphere n)) n),
    (homologyPushZMod2 (TopCat.ofHom f) n).hom z = (degreeOfIso e f : ZMod 2) • z

/-- **The comparison follows from the top `F₂`-homology scalar action.** This is a
proved, formalized reduction: it derives `ModTwoTopClassComparison e` from
`ModTwoTopHomologyScalar e` using only the library's proved `F₂` universal
coefficient theorem (the Kronecker classifier's naturality and injectivity).

Given a self-map `f` fixing a nonzero top class `c ∈ Hⁿ(Sⁿ; F₂)`, the Kronecker
functional `ψ = ⟨c, ·⟩` is nonzero (injectivity) and `f_*`-invariant (naturality
plus `f^* c = c`); the scalar hypothesis turns invariance into `ψ z = d · ψ z`
for `d = degree f mod 2`, and since some `ψ z = 1` in `F₂` we get `d = 1`. -/
theorem modTwoTopClassComparison_of_topHomologyScalar {n : ℕ}
    (e : SphereTopHomologyIso n) (h : ModTwoTopHomologyScalar e) :
    ModTwoTopClassComparison e := by
  intro f c hfix hc
  set X : TopCat := TopCat.of (Sphere n) with hX
  set ψ := (kroneckerMap X n).hom c with hψ
  have hψne : ψ ≠ 0 := by
    intro hcontra
    apply hc
    have hinj := kroneckerMap_injective (TopCat.of (Sphere n)) n
    exact hinj (hcontra.trans (map_zero (kroneckerMap (TopCat.of (Sphere n)) n).hom).symm)
  have hnat := kroneckerMap_naturality_apply (TopCat.ofHom f) n c
  have hfix' : (cohPullback (TopCat.ofHom f) n).hom c = c := hfix
  rw [hfix'] at hnat
  set d : ZMod 2 := (degreeOfIso e f : ZMod 2) with hd
  have key : ∀ z, ψ z = d * ψ z := by
    intro z
    have h1 : ψ z = ψ ((homologyPushZMod2 (TopCat.ofHom f) n).hom z) := by
      have := DFunLike.congr_fun hnat z
      simpa [LinearMap.comp_apply] using this
    rw [h f z, map_smul, smul_eq_mul] at h1
    exact h1
  obtain ⟨z, hz⟩ := DFunLike.ne_iff.mp hψne
  rw [LinearMap.zero_apply] at hz
  have hw1 : ψ z = 1 := by
    rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) (ψ z) with h0 | h0
    · exact absurd h0 hz
    · exact h0
  have hk := key z
  rw [hw1, mul_one] at hk
  exact hk.symm

/-- **Final odd-map degree theorem from the single packaged comparison.** Given
the one named input `ModTwoTopClassComparison e`, every odd self-map `f` of `Sⁿ`
that (via a fixed nonzero RPⁿ top class `a`) fixes the nonzero sphere top class
has **odd** integer degree. The proof uses only the proved unconditional core
`spherePullback_fixes_projPullback` and the proved parity bridge — there is **no
extra parity assumption**, exactly as required by the acceptance criterion. -/
theorem oddMap_degree_odd_of_modTwoTopClassComparison {n : ℕ}
    (e : SphereTopHomologyIso n) (hcmp : ModTwoTopClassComparison e)
    (f : C(Sphere n, Sphere n)) (hf : IsOddMap f) (a : rpCohomology n n)
    (hfix : inducedOnRPPullback f hf n a = a)
    (hne : projPullback n n a ≠ 0) :
    Odd (degreeOfIso e f) :=
  (degreeOfIso_intCast_zmodTwo_eq_one_iff_odd e f).mp
    (hcmp f (projPullback n n a)
      (spherePullback_fixes_projPullback f hf a hfix) hne)

/-- **Final odd-map degree theorem from the single comparison + the single ring
bridge.** Combines the two reductions: the RPⁿ top-class story is reduced to one
ring bridge `Φ : RPnCohomologyToModelHom n`, and the sphere/degree story to the
one comparison `ModTwoTopClassComparison e`. The only remaining sphere-side
hypotheses are the genuine action input `hα_fixed` (`fbar^*(α) = α`) and the
sphere nonvanishing `hne`; all parity reasoning is discharged. -/
theorem oddMap_degree_odd_of_ringBridge_of_modTwoTopClassComparison {n : ℕ}
    (e : SphereTopHomologyIso n) (hcmp : ModTwoTopClassComparison e)
    (f : C(Sphere n, Sphere n)) (hf : IsOddMap f)
    (Φ : RPnCohomologyToModelHom n)
    (hα_fixed : (inducedOnRPPullback f hf 1).hom Φ.alpha = Φ.alpha)
    (hne : projPullback n n (cupPowZMod2 Φ.alpha n) ≠ 0) :
    Odd (degreeOfIso e f) := by
  obtain ⟨hfix, _hnz⟩ := rpAlpha_power_top_fixed_ne_zero Φ f hf hα_fixed
  exact oddMap_degree_odd_of_modTwoTopClassComparison e hcmp f hf
    (cupPowZMod2 Φ.alpha n) hfix hne

/-! ## 3d. conditional near-final assembly: three named blockers, no vacuous hypothesis

The theorems in §3b/§3c route the sphere-side nonvanishing through `projPullback`
(`proj^*`). That route is degenerate: for `n ≥ 1` one has `proj^* α = 0` in
`H¹(RPⁿ; F₂)`, hence `proj^*(αⁿ) = 0`, so the hypothesis `proj^* (αⁿ) ≠ 0` is
unsatisfiable and the genuine comparison really proceeds through the double-cover
*transfer*, not `proj^*`. The assembly below avoids that degenerate route
entirely: it depends on exactly three honest named blockers and no vacuous or
redundant hypothesis. -/

/-- **Odd self-maps fix a nonzero top `F₂`-class.** This packages the genuine
content of the RPⁿ / double-cover descent half of the argument: every odd
self-map `f` of `Sⁿ` fixes some nonzero class `c ∈ Hⁿ(Sⁿ; F₂)`
(`f^* c = c`, `c ≠ 0`).

Mathematically this holds because `f` descends to `fbar : RPⁿ → RPⁿ`, which acts
as the identity on the one-dimensional top group `Hⁿ(RPⁿ; F₂) = ⟨αⁿ⟩` (the unique
nonzero element is fixed by any ring map), and the double-cover *transfer*
homomorphism transports this to the nonzero sphere top class. This property is packaged as an explicit named input corresponding to the `F₂` transfer/Gysin
sequence of the double cover `Sⁿ → RPⁿ`. It is
**not** the degenerate `proj^*` route (`proj^*(αⁿ) = 0` for `n ≥ 1`). -/
def OddMapFixesTopClass (n : ℕ) : Prop :=
  ∀ f : C(Sphere n, Sphere n), IsOddMap f →
    ∃ c : sphereCohomology n n, c ≠ 0 ∧ spherePullback f n c = c

/- Internal conditional version. The public theorem is
`SphereOddDegree.odd_degree_of_odd_sphere_self_map` in `Final/OddDegreeTheorem.lean`
(re-exported through `SphereOddDegree.Final`); it discharges Branch 1 (`e`)
unconditionally and factors through this lemma. -/
/-- **The conditional near-final odd-map degree theorem.**

```text
f odd ⇒ Odd (degree f),
```

assembled from exactly the three remaining named topological blockers — and with
**no vacuous or redundant hypothesis** (in particular it does *not* route through
the degenerate `proj^*` avatar, for which `proj^*(αⁿ) = 0` when `n ≥ 1`):

* `e : SphereTopHomologyIso n` — the integral top-homology identification
 `Hₙ(Sⁿ; ℤ) ≅ ℤ` that pins the integer degree `degreeOfIso e`; blocker branch
 *sphere top homology* (`SphereTopHomologyReduction.lean`);
* `hcmp : ModTwoTopClassComparison e` — a self-map fixing a nonzero top
 `F₂`-class has odd integer degree; blocker branch *mod-two degree comparison*
 (the `F₂`-coefficient transfer/reduction, `ModTwoDegreeComparison.lean`);
* `htop : OddMapFixesTopClass n` — an odd self-map fixes a nonzero top
 `F₂`-class; blocker branch *RPⁿ / double-cover descent* (the descended map acts
 trivially on `Hⁿ(RPⁿ; F₂)`, transported by the transfer).

Every other ingredient is the library's *proved, unconditional* machinery: the
parity bridge `degreeOfIso_intCast_zmodTwo_eq_one_iff_odd`. The oddness
hypothesis `hf` is used genuinely (it feeds `htop` to produce the fixed nonzero
top class). Supplying genuine terms for `e`, `hcmp`, `htop` specializes this to
the unconditional final theorem with no change of proof. -/
theorem oddMap_degree_odd_final {n : ℕ}
    (e : SphereTopHomologyIso n) (hcmp : ModTwoTopClassComparison e)
    (htop : OddMapFixesTopClass n)
    (f : C(Sphere n, Sphere n)) (hf : IsOddMap f) :
    Odd (degreeOfIso e f) := by
  obtain ⟨c, hc, hfix⟩ := htop f hf
  exact (degreeOfIso_intCast_zmodTwo_eq_one_iff_odd e f).mp (hcmp f c hfix hc)

/-! ## 3e. Discharging the `fbar^*(α) = α` hypothesis via the constructed `rpAlpha`

The theorems in §3–§3d keep the action of the descended odd map on the degree-one
class as an explicit hypothesis `hα_fixed : fbar^*(α) = α`. Using the genuine
class `rpAlpha n m` (`ConstructRPAlpha.lean`) built from a monodromy functional
`m : MonodromyFunctional n` (the degree-one homology functional interface), this
hypothesis is proved by `inducedOnRPPullback_rpAlpha`,
and — via the cohomology-level cup-power naturality — so is its consequence on the
top power. The theorems below are the §3/§3c assemblies with the `hα_fixed`
hypothesis removed. -/

/-- **§3 assembly with `fbar^*(α) = α` discharged.** Same conclusion as
`oddMap_degree_odd_of_cohomological_inputs`, but with the action hypothesis
`hα_fixed` removed: it is supplied by `inducedOnRPPullback_rpAlpha` for the genuine
class `α := rpAlpha n m`. The only RPⁿ-side datum now needed is the monodromy
functional `m` (the degree-one Hurewicz input). -/
theorem oddMap_degree_odd_of_cohomological_inputs_rpAlpha {n : ℕ}
    (e : SphereTopHomologyIso n) (m : MonodromyFunctional n)
    (f : C(Sphere n, Sphere n)) (hf : IsOddMap f)
    (alphaPow : rpCohomology n n)
    (hpow : inducedOnRPPullback f hf 1 (rpAlpha n m) = rpAlpha n m →
            inducedOnRPPullback f hf n alphaPow = alphaPow)
    (hne : projPullback n n alphaPow ≠ 0)
    (hcmp : spherePullback f n (projPullback n n alphaPow) = projPullback n n alphaPow →
            projPullback n n alphaPow ≠ 0 → (degreeOfIso e f : ZMod 2) = 1) :
    Odd (degreeOfIso e f) :=
  oddMap_degree_odd_of_cohomological_inputs e f hf (rpAlpha n m) alphaPow
    (inducedOnRPPullback_rpAlpha n m f hf) hpow hne hcmp

/-- **Top-class assembly with both `fbar^*(α) = α` and the power step discharged.**
Taking the top class to be the `n`-th cup power `(rpAlpha n m)ⁿ`, both the action
hypothesis `fbar^*(α) = α` (via `inducedOnRPPullback_rpAlpha`) and its power
consequence `fbar^*(αⁿ) = αⁿ` (via `inducedOnRP_cohPullback_cupPow_fixed`) are
proved. The only remaining inputs are the genuine sphere/degree-side ones
(`e`, `hne`, `hcmp`) and the single monodromy functional `m`. -/
theorem oddMap_degree_odd_of_monodromyFunctional {n : ℕ}
    (e : SphereTopHomologyIso n) (m : MonodromyFunctional n)
    (f : C(Sphere n, Sphere n)) (hf : IsOddMap f)
    (hne : projPullback n n (cupPowZMod2 (rpAlpha n m) n) ≠ 0)
    (hcmp : spherePullback f n (projPullback n n (cupPowZMod2 (rpAlpha n m) n))
              = projPullback n n (cupPowZMod2 (rpAlpha n m) n) →
            projPullback n n (cupPowZMod2 (rpAlpha n m) n) ≠ 0 →
            (degreeOfIso e f : ZMod 2) = 1) :
    Odd (degreeOfIso e f) := by
  have hfix1 := inducedOnRPPullback_rpAlpha n m f hf
  have hfixn : inducedOnRPPullback f hf n (cupPowZMod2 (rpAlpha n m) n)
      = cupPowZMod2 (rpAlpha n m) n :=
    inducedOnRP_cohPullback_cupPow_fixed f hf (rpAlpha n m) hfix1 n
  exact oddMap_degree_odd_of_top_class_comparison e f hf (cupPowZMod2 (rpAlpha n m) n)
    hfixn hne hcmp

/-! ## 4. Sanity specializations (genuine) -/

/-- Sanity check: for the identity map every top class is fixed, so the
naturality core fires trivially — `f^*` fixes `proj^*` of any top class. -/
theorem spherePullback_fixes_projPullback_id {n : ℕ} (a : rpCohomology n n) :
    spherePullback (ContinuousMap.id (Sphere n)) n (projPullback n n a)
      = projPullback n n a :=
  spherePullback_fixes_projPullback (ContinuousMap.id (Sphere n)) (isOddMap_id n) a
    (by rw [inducedOnRPPullback_id]; rfl)

/-- Sanity check: for the antipodal map (which descends to the identity on
`RPⁿ`) every top class is fixed, so `(antipodal)^*` fixes `proj^*` of any top
class. -/
theorem spherePullback_fixes_projPullback_antipodal {n : ℕ} (a : rpCohomology n n) :
    spherePullback (antipodal n) n (projPullback n n a) = projPullback n n a :=
  spherePullback_fixes_projPullback (antipodal n) (isOddMap_antipodal n) a
    (by rw [inducedOnRPPullback_antipodal]; rfl)

end SphereOddDegree
