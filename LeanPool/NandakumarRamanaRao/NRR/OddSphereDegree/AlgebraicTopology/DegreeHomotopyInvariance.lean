/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.Degree
public import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.SingularHomologyHomotopyInvariance

/-!
# Homotopy invariance of the topological degree — unconditional

Now that the singular prism operator is a theorem (`singularPrismOperator`,
established in `SingularHomologyHomotopyInvariance.lean` from the backported
algebraic prism and the library cylinder), the homotopy-invariance wrappers of
`Degree.lean` — which were stated conditionally on `SingularPrismOperator` — are
**unconditional**.
-/

@[expose] public section

open CategoryTheory AlgebraicTopology

namespace SphereOddDegree

/-- **Homotopy invariance of the induced top-homology endomorphism (unconditional).**
Homotopic self-maps `f, g : C(Sphere n, Sphere n)` induce the same endomorphism of
`Hₙ(TopCat.sphere n; ℤ)`. -/
theorem inducedOnTopHomology_eq_of_homotopic_unconditional
    {n : ℕ} {f g : C(Sphere n, Sphere n)} (h : ContinuousMap.Homotopic f g) :
    inducedOnTopHomology f = inducedOnTopHomology g :=
  inducedOnTopHomology_eq_of_homotopic singularPrismOperator h

/-- **Homotopy invariance of the degree (unconditional).**
Homotopic self-maps of `Sphere n` have equal degree relative to any chosen
identification `e : Hₙ(Sⁿ; ℤ) ≅ ℤ`. -/
theorem degreeOfIso_eq_of_homotopic_unconditional
    {n : ℕ} (e : (singularHomologyℤ n).obj (TopCat.sphere.{0} n) ≅ ModuleCat.of ℤ ℤ)
    {f g : C(Sphere n, Sphere n)} (h : ContinuousMap.Homotopic f g) :
    degreeOfIso e f = degreeOfIso e g :=
  degreeOfIso_eq_of_homotopic singularPrismOperator e h

end SphereOddDegree
