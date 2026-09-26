/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.DegreeAPIStrengthening

/-!
# Degree functoriality and homotopy invariance (consolidation layer)

This file consolidates the **standard degree API** — identity, composition,
homotopy invariance, and the homotopy-class–distinguishing application form —
into the strongest formalized statements the library supports today.

The degree API is parameterized by a top-homology identification
`Hₙ(Sⁿ; ℤ) ≅ ℤ` (a term of `SphereTopHomologyIso n` for `n ≥ 1`). Homotopy invariance
is conditional on the required algebraic prism operator
(`SingularPrismOperator`), exactly as in `HomotopyInvariance.lean`.

What is added here, building only on `Degree.lean`, `SphereTopHomology.lean`,
`DegreeAPIStrengthening.lean` and `HomotopyInvariance.lean`:

* **`TopCat.sphere`-native homotopy invariance.** `degreeOfIsoTop_eq_of_homotopic`
 (conditional on the prism operator): homotopic self-morphisms of
 `TopCat.sphere n` have equal `TopCat`-degree.
* **Degree as a monoid homomorphism + power law.** `degreeMonoidHomTop`, the
 multiplicative `End (TopCat.sphere n) →* ℤ` underlying `degreeOfIsoTop`, with
 `degreeMonoidHomTop_apply` and the power law `degreeOfIsoTop_pow`
 (`degree (gᵏ) = (degree g)ᵏ`).
* **Homotopy-class invariant (the application form).** The contrapositives of
 homotopy invariance: maps of different degree are *not* homotopic
 (`not_homotopic_of_degreeOfIso_ne`, `not_homotopic_of_degreeOfIsoTop_ne`, and
 the oriented `SphereOrientation.not_homotopic_of_degree_ne`). This is the exact
 shape the final odd-map theorem consumes.
* **Oriented `TopCat` degree.** `SphereOrientation.degreeTop` with `degreeTop_id`,
 `degreeTop_comp`, `degreeTop_eq_of_homotopic`, and the compatibility
 `degreeTop_toTopCatSphereSelfMap` identifying it with the raw `Sphere n` degree.

Every statement is conditional only on the explicit identification `e` (resp. a
`SphereOrientation`) and, for homotopy invariance, on `SingularPrismOperator` —
the honest set of hypotheses. None of them is a disguised unconditional theorem.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicTopology

namespace SphereOddDegree

/-! ## `TopCat.sphere`-native homotopy invariance -/

/-- **Conditional homotopy invariance of the `TopCat`-degree.**

Assuming the prism operator, two self-morphisms `g, h` of `TopCat.sphere n` whose
underlying continuous maps are homotopic have equal `TopCat`-degree (relative to
any chosen identification `e : Hₙ(Sⁿ; ℤ) ≅ ℤ`). -/
theorem degreeOfIsoTop_eq_of_homotopic (prism : SingularPrismOperator) {n : ℕ}
    (e : SphereTopHomologyIso n)
    {g h : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n}
    (H : ContinuousMap.Homotopic g.hom h.hom) :
    degreeOfIsoTop e g = degreeOfIsoTop e h := by
  unfold degreeOfIsoTop
  rw [singularHomologyMap_eq_of_homotopic prism H n]

/-! ## Degree as a monoid homomorphism and the power law -/

/-- The **multiplicative degree homomorphism** `End (TopCat.sphere n) →* ℤ`
underlying `degreeOfIsoTop`: it sends the identity to `1` and respects the monoid
product of `End (TopCat.sphere n)` (categorical composition). This is the
functorial composite of `Functor.mapEnd` for the homology functor with the scalar
ring homomorphism `degreeRingHomOfIso`. -/
def degreeMonoidHomTop {n : ℕ} (e : SphereTopHomologyIso n) :
    End (TopCat.sphere.{0} n) →* ℤ :=
  (degreeRingHomOfIso _ e).toMonoidHom.comp
    ((singularHomologyℤ n).mapEnd (TopCat.sphere.{0} n))

/-- `degreeMonoidHomTop` computes the `TopCat`-degree. -/
@[simp]
theorem degreeMonoidHomTop_apply {n : ℕ} (e : SphereTopHomologyIso n)
    (g : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n) :
    degreeMonoidHomTop e g = degreeOfIsoTop e g := rfl

/-- **Power law.** The `TopCat`-degree of a `k`-fold self-composite is the `k`-th
power of the degree: `degree (gᵏ) = (degree g)ᵏ` (powers in the endomorphism
monoid `End (TopCat.sphere n)`). -/
theorem degreeOfIsoTop_pow {n : ℕ} (e : SphereTopHomologyIso n)
    (g : End (TopCat.sphere.{0} n)) (k : ℕ) :
    degreeOfIsoTop e (g ^ k) = (degreeOfIsoTop e g) ^ k := by
  rw [← degreeMonoidHomTop_apply, map_pow, degreeMonoidHomTop_apply]

/-! ## Homotopy-class invariant (the application form)

The contrapositives of homotopy invariance: a degree mismatch obstructs a
homotopy. This is the shape the final odd-map / Borsuk–Ulam–style argument
consumes — a degree invariant distinguishing homotopy classes of self-maps. -/

/-- **Maps of different degree are not homotopic** (raw `C(Sphere n, Sphere n)`
form, conditional on the prism operator). -/
theorem not_homotopic_of_degreeOfIso_ne (prism : SingularPrismOperator) {n : ℕ}
    (e : SphereTopHomologyIso n) {f g : C(Sphere n, Sphere n)}
    (h : degreeOfIso e f ≠ degreeOfIso e g) :
    ¬ ContinuousMap.Homotopic f g :=
  fun hh => h (degreeOfIso_eq_of_homotopic prism e hh)

/-- **Maps of different degree are not homotopic** (`TopCat.sphere n` form,
conditional on the prism operator). -/
theorem not_homotopic_of_degreeOfIsoTop_ne (prism : SingularPrismOperator) {n : ℕ}
    (e : SphereTopHomologyIso n)
    {g h : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n}
    (hne : degreeOfIsoTop e g ≠ degreeOfIsoTop e h) :
    ¬ ContinuousMap.Homotopic g.hom h.hom :=
  fun hh => hne (degreeOfIsoTop_eq_of_homotopic prism e hh)

/-! ## Oriented `TopCat` degree

The bundled-orientation analogue of `degreeOfIsoTop`, repackaging the same
identity / composition / homotopy-invariance facts on a `SphereOrientation`. -/

namespace SphereOrientation

variable (o : SphereOrientation)

/-- The oriented `TopCat`-degree of a self-morphism of `TopCat.sphere n`, read off
the supplied identification `o.iso n`. -/
def degreeTop {n : ℕ} (g : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n) : ℤ :=
  degreeOfIsoTop (o.iso n) g

/-- The oriented `TopCat`-degree of the identity is `1`. -/
@[simp]
theorem degreeTop_id (n : ℕ) : o.degreeTop (𝟙 (TopCat.sphere.{0} n)) = 1 :=
  degreeOfIsoTop_id (o.iso n)

/-- The oriented `TopCat`-degree is multiplicative under categorical composition
(the factors reverse, as for `degreeOfIsoTop_comp`). -/
theorem degreeTop_comp {n : ℕ}
    (g h : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n) :
    o.degreeTop (g ≫ h) = o.degreeTop h * o.degreeTop g :=
  degreeOfIsoTop_comp (o.iso n) g h

/-- **Compatibility.** The oriented raw `Sphere n` degree is the oriented
`TopCat`-degree of the model transport. -/
theorem degreeTop_toTopCatSphereSelfMap {n : ℕ} (f : C(Sphere n, Sphere n)) :
    o.degree f = o.degreeTop (toTopCatSphereSelfMap f) := rfl

/-- **Oriented homotopy invariance of the `TopCat`-degree** (conditional on the
prism operator). -/
theorem degreeTop_eq_of_homotopic (prism : SingularPrismOperator) {n : ℕ}
    {g h : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n}
    (H : ContinuousMap.Homotopic g.hom h.hom) :
    o.degreeTop g = o.degreeTop h :=
  degreeOfIsoTop_eq_of_homotopic prism (o.iso n) H

/-- **Oriented homotopy-class invariant.** Self-maps of different oriented degree
are not homotopic (conditional on the prism operator). -/
theorem not_homotopic_of_degree_ne (prism : SingularPrismOperator) {n : ℕ}
    {f g : C(Sphere n, Sphere n)} (h : o.degree f ≠ o.degree g) :
    ¬ ContinuousMap.Homotopic f g :=
  fun hh => h (o.degree_eq_of_homotopic prism hh)

end SphereOrientation

end SphereOddDegree
