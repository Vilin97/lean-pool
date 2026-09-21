/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.ModTwoDegreeComparison
import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.SphereTopHomologyReduction

/-!
# Bundled sphere degree setup

Packages positive-dimensional sphere orientation data and a singular prism operator into
`SphereDegreeSetup`, then exposes degree, composition, homeomorphism, antipodal, and homotopy
invariance APIs from that setup. Unconditional instances of both fields are constructed later
and re-exported through `SphereOddDegree.Final`.
-/

noncomputable section

open CategoryTheory AlgebraicTopology

namespace SphereOddDegree

/-! ## The single compact setup structure -/

/-- A **sphere-degree setup** bundling the two inputs used by the integral degree theory of sphere
self-maps.

* `orientation : SphereOrientationPos` — a choice of top-homology identification
 `Hₙ(Sⁿ; ℤ) ≅ ℤ` in every dimension `n ≥ 1`, represented by a
 `SphereSuspensionTower`.
* `prism : SingularPrismOperator` — the algebraic prism operator underlying
 homotopy invariance of singular homology.

Bundling both means a downstream consumer assumes **one** hypothesis rather than
several, and every degree theorem — including homotopy invariance — is
unconditional relative to a `SphereDegreeSetup`. The fields are supplied by the final assembly modules. -/
structure SphereDegreeSetup where
  /-- The positive top-homology orientation `Hₙ(Sⁿ; ℤ) ≅ ℤ` (`n ≥ 1`). -/
  orientation : SphereOrientationPos
  /-- The algebraic prism operator for homotopy invariance of singular homology. -/
  prism : SingularPrismOperator

namespace SphereDegreeSetup

variable (S : SphereDegreeSetup)

/-! ## The degree on the library sphere model `Sphere n` -/

/-- The integer **degree** of a self-map `f : C(Sphere n, Sphere n)` (`n ≥ 1`),
read off the setup's top-homology orientation. Honest and unconditional *given*
the setup `S`. -/
def degree {n : ℕ} (hn : 1 ≤ n) (f : C(Sphere n, Sphere n)) : ℤ :=
  S.orientation.degree hn f

/-- **Compatibility with the conditional API.** The setup degree is the conditional
`degreeOfIso` of `Degree.lean` at the setup's chosen identification. -/
theorem degree_eq_degreeOfIso {n : ℕ} (hn : 1 ≤ n) (f : C(Sphere n, Sphere n)) :
    S.degree hn f = degreeOfIso (S.orientation.iso n hn) f := rfl

/-- The degree of the identity map is `1`. -/
@[simp]
theorem degree_id {n : ℕ} (hn : 1 ≤ n) :
    S.degree hn (ContinuousMap.id (Sphere n)) = 1 :=
  S.orientation.degree_id hn

/-- The degree is multiplicative: `degree (g ∘ f) = degree g * degree f`. -/
theorem degree_comp {n : ℕ} (hn : 1 ≤ n) (f g : C(Sphere n, Sphere n)) :
    S.degree hn (g.comp f) = S.degree hn g * S.degree hn f :=
  S.orientation.degree_comp hn f g

/-- **Choice independence.** Any two setups assign the same degree (the integer is
read off the intrinsic endomorphism ring, independent of the chosen
identification). -/
theorem degree_well_defined (S' : SphereDegreeSetup) {n : ℕ} (hn : 1 ≤ n)
    (f : C(Sphere n, Sphere n)) : S.degree hn f = S'.degree hn f :=
  S.orientation.degree_well_defined S'.orientation hn f

/-- **Homotopy invariance — unconditional given the setup.** Homotopic self-maps of
`Sphere n` (`n ≥ 1`) have equal degree. Unlike the conditional API, no separate
prism hypothesis is needed: the prism is part of `S`. -/
theorem degree_homotopy {n : ℕ} (hn : 1 ≤ n)
    {f g : C(Sphere n, Sphere n)} (h : ContinuousMap.Homotopic f g) :
    S.degree hn f = S.degree hn g :=
  S.orientation.degree_eq_of_homotopic S.prism hn h

/-- **Homotopy-class invariant.** Self-maps of different degree are not homotopic.
No separate prism hypothesis — it is part of `S`. -/
theorem not_homotopic_of_degree_ne {n : ℕ} (hn : 1 ≤ n)
    {f g : C(Sphere n, Sphere n)} (h : S.degree hn f ≠ S.degree hn g) :
    ¬ ContinuousMap.Homotopic f g :=
  fun hh => h (S.degree_homotopy hn hh)

/-! ## The degree on the categorical sphere `TopCat.sphere n` -/

/-- The integer **degree of a `TopCat.sphere n` self-morphism** `g`, read off the
setup's orientation. the library-sphere degree is its value on the model
transport (`degree_eq_degreeTopCat`). -/
def degreeTopCat {n : ℕ} (hn : 1 ≤ n)
    (g : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n) : ℤ :=
  degreeOfIsoTop (S.orientation.iso n hn) g

/-- The `TopCat`-degree of the identity morphism is `1`. -/
@[simp]
theorem degreeTopCat_id {n : ℕ} (hn : 1 ≤ n) :
    S.degreeTopCat hn (𝟙 (TopCat.sphere.{0} n)) = 1 :=
  degreeOfIsoTop_id (S.orientation.iso n hn)

/-- The `TopCat`-degree is multiplicative under categorical composition (the
factors reverse, as for `degreeOfIsoTop_comp`). -/
theorem degreeTopCat_comp {n : ℕ} (hn : 1 ≤ n)
    (g h : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n) :
    S.degreeTopCat hn (g ≫ h) = S.degreeTopCat hn h * S.degreeTopCat hn g :=
  degreeOfIsoTop_comp (S.orientation.iso n hn) g h

/-- **Homotopy invariance of the `TopCat`-degree — unconditional given the setup.**
Self-morphisms with homotopic underlying maps have equal `TopCat`-degree. -/
theorem degreeTopCat_homotopy {n : ℕ} (hn : 1 ≤ n)
    {g h : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n}
    (H : ContinuousMap.Homotopic g.hom h.hom) :
    S.degreeTopCat hn g = S.degreeTopCat hn h :=
  degreeOfIsoTop_eq_of_homotopic S.prism (S.orientation.iso n hn) H

/-- **Model compatibility.** the library-sphere degree of `f` is the
`TopCat`-degree of its model transport `toTopCatSphereSelfMap f`. -/
theorem degree_eq_degreeTopCat {n : ℕ} (hn : 1 ≤ n) (f : C(Sphere n, Sphere n)) :
    S.degree hn f = S.degreeTopCat hn (toTopCatSphereSelfMap f) := rfl

/-! ## Standard degree wrappers, under the single setup -/

/-- The degree of a one-point map is `0` (`n ≥ 1`). -/
theorem degree_const {n : ℕ} (hn : 1 ≤ n) (c : Sphere n) :
    S.degree hn (ContinuousMap.const (Sphere n) c) = 0 :=
  degreeOfIso_const (S.orientation.iso n hn) (by omega) c

/-- The degree of a self-homeomorphism is `±1`. -/
theorem degree_homeomorph_eq_one_or_neg_one {n : ℕ} (hn : 1 ≤ n)
    (h : Sphere n ≃ₜ Sphere n) :
    S.degree hn (h : C(Sphere n, Sphere n)) = 1
      ∨ S.degree hn (h : C(Sphere n, Sphere n)) = -1 :=
  degreeOfIso_homeomorph_eq_one_or_neg_one (S.orientation.iso n hn) h

/-- The degree of a self-homeomorphism is odd. -/
theorem odd_degree_homeomorph {n : ℕ} (hn : 1 ≤ n) (h : Sphere n ≃ₜ Sphere n) :
    Odd (S.degree hn (h : C(Sphere n, Sphere n))) :=
  odd_degreeOfIso_homeomorph (S.orientation.iso n hn) h

/-- The degree of the antipodal map is `±1`. -/
theorem degree_antipodal_eq_one_or_neg_one {n : ℕ} (hn : 1 ≤ n) :
    S.degree hn (antipodal n) = 1 ∨ S.degree hn (antipodal n) = -1 :=
  degreeOfIso_antipodal_eq_one_or_neg_one (S.orientation.iso n hn)

/-- The degree of the antipodal map is odd. -/
theorem odd_degree_antipodal {n : ℕ} (hn : 1 ≤ n) :
    Odd (S.degree hn (antipodal n)) :=
  odd_degreeOfIso_antipodal (S.orientation.iso n hn)

/-- **Conditional antipodal value.** Given the orientation-sign datum
`DegreeEqAmbientDet` (degree of the antipodal map = its ambient determinant), the
antipodal degree is `(-1)^(n+1)`. -/
theorem degree_antipodal_eq_neg_one_pow_of_eq_det {n : ℕ} (hn : 1 ≤ n)
    (h : DegreeEqAmbientDet (S.orientation.iso n hn)) :
    S.degree hn (antipodal n) = (-1) ^ (n + 1) :=
  degreeOfIso_antipodal_eq_neg_one_pow_of_eq_det (S.orientation.iso n hn) h

/-- **Mod-2 comparison.** The reduction of the degree to `ZMod 2` is `1` iff the
degree is odd. -/
theorem degree_intCast_zmodTwo_eq_one_iff_odd {n : ℕ} (hn : 1 ≤ n)
    (f : C(Sphere n, Sphere n)) :
    ((S.degree hn f : ZMod 2) = 1) ↔ Odd (S.degree hn f) :=
  degreeOfIso_intCast_zmodTwo_eq_one_iff_odd (S.orientation.iso n hn) f

/-- **The mod-2 degree of the antipodal map is `1`.** -/
theorem degree_antipodal_intCast_zmodTwo_eq_one {n : ℕ} (hn : 1 ≤ n) :
    ((S.degree hn (antipodal n) : ZMod 2)) = 1 :=
  degreeOfIso_antipodal_intCast_zmodTwo_eq_one (S.orientation.iso n hn)

end SphereDegreeSetup

/-! ## Assembling a degree setup -/

/-- A `SphereSuspensionTower` and a `SingularPrismOperator` assemble a full
`SphereDegreeSetup`. -/
def SphereSuspensionTower.degreeSetup (T : SphereSuspensionTower)
    (prism : SingularPrismOperator) : SphereDegreeSetup where
  orientation := T.orientation
  prism := prism

@[simp]
theorem SphereSuspensionTower.degreeSetup_orientation (T : SphereSuspensionTower)
    (prism : SingularPrismOperator) :
    (T.degreeSetup prism).orientation = T.orientation := rfl

end SphereOddDegree
