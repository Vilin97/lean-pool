/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.Degree
import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.RPnLowDimensional

/-!
# Sphere top homology and degree interfaces

Defines the integral top-homology objects for spheres, orientation packages, and degree relative
to a selected top-homology isomorphism. Positive-dimensional unconditional instances are built
from the Mayer--Vietoris suspension computation and re-exported by the final API.
-/

open CategoryTheory AlgebraicTopology

noncomputable section

namespace SphereOddDegree

/-! ## Top-homology abbreviations over `TopCat.sphere n` -/

/-- `Hₖ(Sⁿ; ℤ)`: the `k`-th integral singular homology of Mathlib's categorical
sphere object `TopCat.sphere n`. -/
noncomputable abbrev sphereHomologyℤ (k n : ℕ) : ModuleCat.{0} ℤ :=
  (singularHomologyℤ k).obj (TopCat.sphere.{0} n)

/-- The **top** homology `Hₙ(Sⁿ; ℤ)` — the group that should be `≅ ℤ` and that the
topological degree reads. -/
noncomputable abbrev sphereTopHomologyℤ (n : ℕ) : ModuleCat.{0} ℤ :=
  sphereHomologyℤ n n

/-! ## Model bridge: `TopCat.sphere n` vs. the raw `Sphere n` model -/

/-- **Model bridge on homology.** The integral singular homology of the
categorical sphere `TopCat.sphere n` is isomorphic to that of the library's raw
subtype model `Sphere n`, by applying the homology functor to the bridge
isomorphism `topCatSphereIso` (`TopCatBridge.lean`). -/
noncomputable def sphereModelHomologyIso (k n : ℕ) :
    sphereHomologyℤ k n ≅ (singularHomologyℤ k).obj (TopCat.of (Sphere n)) :=
  (singularHomologyℤ k).mapIso (topCatSphereIso n)

/-! ## Genuine low-dimensional case: `n = 0`

`Sphere 0` is the unit sphere in `ℝ¹`, i.e. the two-point set `{±e}`. It is finite
(at most two points by `sphere_zero_eq_or_neg`), hence discrete and totally
disconnected; the bridge homeomorphism transports this to `TopCat.sphere 0`. -/

/-- `Sphere 0` is finite: every point equals a fixed `p` or its antipode `-p`
(`sphere_zero_eq_or_neg`), so it is the image of `Bool`. -/
instance instFiniteSphereZero : Finite (Sphere 0) := by
  have p : Sphere 0 := ⟨EuclideanSpace.single 0 1, by norm_num [EuclideanSpace.norm_eq]⟩
  apply Finite.of_surjective (fun b : Bool => if b then p else -p)
  intro y
  rcases sphere_zero_eq_or_neg y p with h | h
  · exact ⟨true, by simp [h]⟩
  · exact ⟨false, by simp [h]⟩

/-- `TopCat.sphere 0` is totally disconnected: it is homeomorphic (via
`topCatSphereHomeomorph`) to the finite, hence discrete, two-point set
`Sphere 0`. -/
instance instTotallyDisconnectedTopCatSphereZero :
    TotallyDisconnectedSpace (TopCat.sphere.{0} 0 : Type) :=
  (topCatSphereHomeomorph 0).symm.totallyDisconnectedSpace

/-- **Genuine low-dimensional homology of `S⁰`.** For `k ≠ 0`,
`Hₖ(S⁰; ℤ) = 0`, since `S⁰` is totally disconnected. (The `k = 0` value is
`H₀(S⁰; ℤ) ≅ ℤ²`, which is *not* `ℤ`; the degree theory therefore concerns
`n ≥ 1`.) -/
theorem sphere0_singularHomologyℤ_isZero (k : ℕ) (hk : k ≠ 0) :
    Limits.IsZero (sphereHomologyℤ k 0) :=
  AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
    (ModuleCat ℤ) k (ModuleCat.of ℤ ℤ) (TopCat.sphere.{0} 0) hk

/-! ## Conditional isomorphism wrappers -/

/-- The **type of top-homology identifications** `Hₙ(Sⁿ; ℤ) ≅ ℤ` (over
`TopCat.sphere n`). A term of this type selects an orientation in dimension `n`. -/
abbrev SphereTopHomologyIso (n : ℕ) : Type :=
  sphereTopHomologyℤ n ≅ ModuleCat.of ℤ ℤ

/-- Transport an identification `Hₙ(Sⁿ) ≅ ℤ` from the raw `Sphere n` model to the
categorical `TopCat.sphere n` model, through the homology model bridge. -/
def sphereTopHomologyIsoOfModelIso {n : ℕ}
    (e : (singularHomologyℤ n).obj (TopCat.of (Sphere n)) ≅ ModuleCat.of ℤ ℤ) :
    SphereTopHomologyIso n :=
  (sphereModelHomologyIso n n).trans e

/-- Transport an identification `Hₙ(Sⁿ) ≅ ℤ` from the categorical
`TopCat.sphere n` model to the raw `Sphere n` model, through the homology model
bridge. -/
def modelIsoOfSphereTopHomologyIso {n : ℕ} (e : SphereTopHomologyIso n) :
    (singularHomologyℤ n).obj (TopCat.of (Sphere n)) ≅ ModuleCat.of ℤ ℤ :=
  (sphereModelHomologyIso n n).symm.trans e

/-! ## Bundled orientation ⇒ unconditional degree

`SphereOrientation` bundles a choice of `Hₙ(Sⁿ; ℤ) ≅ ℤ` in every dimension and packages the
degree of `Degree.lean` relative to that orientation data. -/

/-- A choice of top-homology identification `Hₙ(Sⁿ; ℤ) ≅ ℤ` in every dimension.
This structure provides the orientation data used by the degree API. -/
structure SphereOrientation where
  /-- The identification `Hₙ(Sⁿ; ℤ) ≅ ℤ` in dimension `n`. -/
  iso : ∀ n, SphereTopHomologyIso n

namespace SphereOrientation

variable (o : SphereOrientation)

/-- The integer **degree** of a self-map of `Sphere n`, read off the supplied
top-homology identification `o.iso n`. Honest and unconditional once a
`SphereOrientation` is provided. -/
def degree {n : ℕ} (f : C(Sphere n, Sphere n)) : ℤ :=
  degreeOfIso (o.iso n) f

/-- The degree of the identity map is `1`. -/
@[simp]
theorem degree_id (n : ℕ) : o.degree (ContinuousMap.id (Sphere n)) = 1 :=
  degreeOfIso_id (o.iso n)

/-- The degree is multiplicative: `degree (g ∘ f) = degree g * degree f`. -/
theorem degree_comp {n : ℕ} (f g : C(Sphere n, Sphere n)) :
    o.degree (g.comp f) = o.degree g * o.degree f :=
  degreeOfIso_comp (o.iso n) f g

/-- **Choice independence.** Any two orientations assign the same degree, since the
relative degree is independent of the chosen identification. -/
theorem degree_well_defined (o' : SphereOrientation) {n : ℕ}
    (f : C(Sphere n, Sphere n)) : o.degree f = o'.degree f :=
  degreeOfIso_well_defined (o.iso n) (o'.iso n) f

/-- **Homotopy invariance of the degree** (conditional on the prism operator).
Homotopic self-maps of `Sphere n` have equal degree. -/
theorem degree_eq_of_homotopic (prism : SingularPrismOperator) {n : ℕ}
    {f g : C(Sphere n, Sphere n)} (h : ContinuousMap.Homotopic f g) :
    o.degree f = o.degree g :=
  degreeOfIso_eq_of_homotopic prism (o.iso n) h

end SphereOrientation

end SphereOddDegree
