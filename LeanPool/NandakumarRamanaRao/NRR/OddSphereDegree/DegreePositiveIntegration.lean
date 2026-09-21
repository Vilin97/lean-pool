/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.UnconditionalDegree
import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.FinalOddMapComparison
import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.DegreeHomotopyInvariance

/-!
# Positive-dimensional degree from bundled sphere orientations

Packages the conditional degree API through `SphereOrientationPos`, so all
positive dimensions share one coherent family of top-homology orientations.
It derives identity, composition, homotopy invariance, and conditional odd-map
results from that bundle. Later sphere-homology modules construct the
unconditional orientation used by the public final theorem.
-/
noncomputable section

open CategoryTheory AlgebraicTopology

namespace SphereOddDegree

/-! ## Positive-dimensional degree -/

/-- The integer **positive-dimensional degree** of a self-map
`f : C(Sphere n, Sphere n)` (`n ≥ 1`), read off a positive top-homology
orientation `o : SphereOrientationPos`.

This is `degreeOfIso` of `Degree.lean` evaluated at the orientation's chosen
identification `o.iso n hn : Hₙ(Sⁿ; ℤ) ≅ ℤ`; in particular it carries no free
per-dimension `SphereTopHomologyIso n` argument — only the bundled `o`. -/
def degreePos (o : SphereOrientationPos) {n : ℕ} (hn : 1 ≤ n)
    (f : C(Sphere n, Sphere n)) : ℤ :=
  degreeOfIso (o.iso n hn) f

/-- **Compatibility with the conditional API.** `degreePos` is the conditional
`degreeOfIso` at the orientation's chosen identification. -/
theorem degreePos_eq_degreeOfIso (o : SphereOrientationPos) {n : ℕ} (hn : 1 ≤ n)
    (f : C(Sphere n, Sphere n)) :
    degreePos o hn f = degreeOfIso (o.iso n hn) f := rfl

/-- **Agreement with `SphereOrientationPos.degree`.** -/
theorem degreePos_eq_orientation_degree (o : SphereOrientationPos) {n : ℕ}
    (hn : 1 ≤ n) (f : C(Sphere n, Sphere n)) :
    degreePos o hn f = o.degree hn f := rfl

/-- The degree of the identity map is `1`. -/
@[simp]
theorem degreePos_id (o : SphereOrientationPos) {n : ℕ} (hn : 1 ≤ n) :
    degreePos o hn (ContinuousMap.id (Sphere n)) = 1 :=
  degreeOfIso_id (o.iso n hn)

/-- The degree is multiplicative: `degree (g ∘ f) = degree g * degree f`. -/
theorem degreePos_comp (o : SphereOrientationPos) {n : ℕ} (hn : 1 ≤ n)
    (f g : C(Sphere n, Sphere n)) :
    degreePos o hn (g.comp f) = degreePos o hn g * degreePos o hn f :=
  degreeOfIso_comp (o.iso n hn) f g

/-- **Choice independence.** Any two positive orientations assign the same degree:
the integer is read off the intrinsic endomorphism ring, independent of the chosen
identification. -/
theorem degreePos_well_defined (o o' : SphereOrientationPos) {n : ℕ} (hn : 1 ≤ n)
    (f : C(Sphere n, Sphere n)) :
    degreePos o hn f = degreePos o' hn f :=
  degreeOfIso_well_defined (o.iso n hn) (o'.iso n hn) f

/-- **Homotopy invariance of the positive degree — unconditional.** Homotopic
self-maps of `Sphere n` (`n ≥ 1`) have equal degree. No prism hypothesis is
needed: `singularPrismOperator` is a theorem. -/
theorem degreePos_homotopy (o : SphereOrientationPos) {n : ℕ} (hn : 1 ≤ n)
    {f g : C(Sphere n, Sphere n)} (h : ContinuousMap.Homotopic f g) :
    degreePos o hn f = degreePos o hn g :=
  degreeOfIso_eq_of_homotopic_unconditional (o.iso n hn) h

/-- **Homotopy-class invariant.** Self-maps of different positive degree are not
homotopic. -/
theorem not_homotopic_of_degreePos_ne (o : SphereOrientationPos) {n : ℕ}
    (hn : 1 ≤ n) {f g : C(Sphere n, Sphere n)}
    (h : degreePos o hn f ≠ degreePos o hn g) :
    ¬ ContinuousMap.Homotopic f g :=
  fun hh => h (degreePos_homotopy o hn hh)

/-! ## Standard wrappers for the positive degree -/

/-- The degree of a one-point map is `0` (`n ≥ 1`). -/
theorem degreePos_const (o : SphereOrientationPos) {n : ℕ} (hn : 1 ≤ n)
    (c : Sphere n) :
    degreePos o hn (ContinuousMap.const (Sphere n) c) = 0 :=
  degreeOfIso_const (o.iso n hn) (by omega) c

/-- The degree of a self-homeomorphism is `±1`. -/
theorem degreePos_homeomorph_eq_one_or_neg_one (o : SphereOrientationPos) {n : ℕ}
    (hn : 1 ≤ n) (h : Sphere n ≃ₜ Sphere n) :
    degreePos o hn (h : C(Sphere n, Sphere n)) = 1
      ∨ degreePos o hn (h : C(Sphere n, Sphere n)) = -1 :=
  degreeOfIso_homeomorph_eq_one_or_neg_one (o.iso n hn) h

/-- The degree of a self-homeomorphism is odd. -/
theorem odd_degreePos_homeomorph (o : SphereOrientationPos) {n : ℕ} (hn : 1 ≤ n)
    (h : Sphere n ≃ₜ Sphere n) :
    Odd (degreePos o hn (h : C(Sphere n, Sphere n))) :=
  odd_degreeOfIso_homeomorph (o.iso n hn) h

/-- The degree of the antipodal map is `±1`. -/
theorem degreePos_antipodal_eq_one_or_neg_one (o : SphereOrientationPos) {n : ℕ}
    (hn : 1 ≤ n) :
    degreePos o hn (antipodal n) = 1 ∨ degreePos o hn (antipodal n) = -1 :=
  degreeOfIso_antipodal_eq_one_or_neg_one (o.iso n hn)

/-- The degree of the antipodal map is odd. -/
theorem odd_degreePos_antipodal (o : SphereOrientationPos) {n : ℕ} (hn : 1 ≤ n) :
    Odd (degreePos o hn (antipodal n)) :=
  odd_degreeOfIso_antipodal (o.iso n hn)

/-- **Mod-2 comparison.** The reduction of the degree to `ZMod 2` is `1` iff the
degree is odd. -/
theorem degreePos_intCast_zmodTwo_eq_one_iff_odd (o : SphereOrientationPos) {n : ℕ}
    (hn : 1 ≤ n) (f : C(Sphere n, Sphere n)) :
    ((degreePos o hn f : ZMod 2) = 1) ↔ Odd (degreePos o hn f) :=
  degreeOfIso_intCast_zmodTwo_eq_one_iff_odd (o.iso n hn) f

/-! ## The final odd-map theorem, with the free `SphereTopHomologyIso n` removed -/

/-- **Final odd-map degree theorem through a positive orientation.**

This is `oddMap_degree_odd_final` with the free `e : SphereTopHomologyIso n`
argument replaced by a bundled positive orientation `o : SphereOrientationPos`
together with `hn : 1 ≤ n`. Given the two remaining named topological inputs

* `hcmp : ModTwoTopClassComparison (o.iso n hn)` — a self-map fixing a nonzero top
 `F₂`-class has odd integer degree;
* `htop : OddMapFixesTopClass n` — an odd self-map fixes a nonzero top `F₂`-class,

every odd self-map `f` of `Sⁿ` (`n ≥ 1`) has **odd** `degreePos`. For `1 ≤ n`
the statement no longer carries a free `SphereTopHomologyIso n`. -/
theorem oddMap_degreePos_odd_final (o : SphereOrientationPos) {n : ℕ} (hn : 1 ≤ n)
    (hcmp : ModTwoTopClassComparison (o.iso n hn)) (htop : OddMapFixesTopClass n)
    (f : C(Sphere n, Sphere n)) (hf : IsOddMap f) :
    Odd (degreePos o hn f) :=
  oddMap_degree_odd_final (o.iso n hn) hcmp htop f hf

/-- **Final odd-map theorem through a positive orientation and a monodromy
functional.** This is `oddMap_degree_odd_of_monodromyFunctional` with the free
`SphereTopHomologyIso n` replaced by a bundled positive orientation; the action
hypothesis `fbar^*(α) = α` and its top-power consequence are discharged via the
constructed class `rpAlpha n m`. The remaining inputs are the orientation `o`,
the monodromy functional `m`, and the sphere-side comparison data. -/
theorem oddMap_degreePos_odd_of_monodromyFunctional (o : SphereOrientationPos)
    {n : ℕ} (hn : 1 ≤ n) (m : MonodromyFunctional n)
    (f : C(Sphere n, Sphere n)) (hf : IsOddMap f)
    (hne : projPullback n n (cupPowZMod2 (rpAlpha n m) n) ≠ 0)
    (hcmp : spherePullback f n (projPullback n n (cupPowZMod2 (rpAlpha n m) n))
              = projPullback n n (cupPowZMod2 (rpAlpha n m) n) →
            projPullback n n (cupPowZMod2 (rpAlpha n m) n) ≠ 0 →
            (degreePos o hn f : ZMod 2) = 1) :
    Odd (degreePos o hn f) :=
  oddMap_degree_odd_of_monodromyFunctional (o.iso n hn) m f hf hne hcmp

end SphereOddDegree
