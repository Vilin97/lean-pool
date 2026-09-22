/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.TopCatBridge
import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.SingularHomologyFunctorAPI
import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.HomotopyInvariance
import Mathlib.LinearAlgebra.Determinant

/-!
# Topological degree relative to a sphere orientation

Defines the transport from the project sphere model to `TopCat.sphere`, the
induced endomorphism on top singular homology, and the integer scalar obtained
after choosing an isomorphism from top homology to `ℤ`. The resulting
`degreeOfIso` API includes identity, composition, and independence of the
chosen orientation isomorphism. Unconditional orientation data is supplied by
later sphere-homology modules.
-/
noncomputable section

open CategoryTheory

namespace SphereOddDegree

/-! ## Orientation of the ambient antipodal map

The orientation/determinant facts about the ambient linear map `x ↦ -x` on
`ℝ^(n+1)`. The bundled antipodal self-map `antipodal n` is the restriction of
this ambient map to the unit sphere, and its determinant `(-1)^(n+1)` is the
orientation sign that the topological degree `degree (antipodal n)` must
reproduce. These facts are degree/orientation support — not point-set foundation
— so they live here rather than in `Antipodal.lean`. -/

/-- The ambient antipodal map `x ↦ -x` on `ℝ^(n+1)`, as a linear endomorphism,
equals scalar multiplication by `-1`. This is the linear-algebra shadow of the
bundled `antipodal n` self-map (which is its restriction to the unit sphere). -/
theorem ambientNeg_eq_neg_one_smul (n : ℕ) :
    (-LinearMap.id :
        EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
      = (-1 : ℝ) • LinearMap.id := by
  simp

/-- The determinant of the ambient antipodal linear map `x ↦ -x` on `ℝ^(n+1)`
is `(-1)^(n+1)`.

This is the ambient orientation calculation used by the later theorem
`degree (antipodal n) = (-1)^(n+1)`: the antipodal map is the restriction to the
sphere of this linear map, and its determinant gives the expected degree sign. -/
theorem det_ambientNeg (n : ℕ) :
    LinearMap.det
        (-LinearMap.id :
          EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
      = (-1) ^ (n + 1) := by
  rw [ambientNeg_eq_neg_one_smul, LinearMap.det_smul]
  simp [finrank_euclideanSpace]

/-! ## Model transport of self-maps to `TopCat.sphere n` -/

/-- Transport a continuous self-map of the raw sphere model `Sphere n` to a
self-morphism of Mathlib's categorical sphere `TopCat.sphere n`, by conjugating
with the bridge isomorphism `topCatSphereIso`. -/
def toTopCatSphereSelfMap {n : ℕ} (f : C(Sphere n, Sphere n)) :
    TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n :=
  (topCatSphereIso n).hom ≫ TopCat.ofHom f ≫ (topCatSphereIso n).inv

/-- The transport sends the identity self-map to the identity morphism. -/
@[simp]
theorem toTopCatSphereSelfMap_id (n : ℕ) :
    toTopCatSphereSelfMap (ContinuousMap.id (Sphere n)) = 𝟙 _ :=
  TopCat.hom_ext_iff.mpr rfl

/-- The transport is functorial: it turns composition of continuous maps into
composition of `TopCat` morphisms (in the same order). -/
theorem toTopCatSphereSelfMap_comp {n : ℕ} (f g : C(Sphere n, Sphere n)) :
    toTopCatSphereSelfMap (g.comp f)
      = toTopCatSphereSelfMap f ≫ toTopCatSphereSelfMap g := by
  unfold toTopCatSphereSelfMap
  simp [TopCat.ofHom_comp]

/-! ## Induced endomorphism of top singular homology -/

/-- The endomorphism of `Hₙ(TopCat.sphere n; ℤ)` induced by a continuous self-map
of `Sphere n`, through the model transport and the integral singular homology
functor. -/
def inducedOnTopHomology {n : ℕ} (f : C(Sphere n, Sphere n)) :
    End ((singularHomologyℤ n).obj (TopCat.sphere.{0} n)) :=
  (singularHomologyℤ n).map (toTopCatSphereSelfMap f)

/-- The induced endomorphism of the identity is the identity. -/
@[simp]
theorem inducedOnTopHomology_id (n : ℕ) :
    inducedOnTopHomology (ContinuousMap.id (Sphere n)) = 𝟙 _ := by
  dsimp [inducedOnTopHomology]
  rw [toTopCatSphereSelfMap_id]
  exact (singularHomologyℤ n).map_id _

/-- Functoriality of the induced endomorphism, in categorical composition form. -/
theorem inducedOnTopHomology_comp {n : ℕ} (f g : C(Sphere n, Sphere n)) :
    inducedOnTopHomology (g.comp f)
      = inducedOnTopHomology f ≫ inducedOnTopHomology g := by
  simp [inducedOnTopHomology, toTopCatSphereSelfMap_comp]

/-- Functoriality of the induced endomorphism, in `End`-monoid product form.
Note that in `End X` the product `a * b` is `b ≫ a`, so the order reverses. -/
theorem inducedOnTopHomology_comp_mul {n : ℕ} (f g : C(Sphere n, Sphere n)) :
    inducedOnTopHomology (g.comp f)
      = inducedOnTopHomology g * inducedOnTopHomology f := by
  rw [inducedOnTopHomology_comp, End.mul_def]

/-! ## The ℤ-endomorphism scalar API -/

/-- Evaluation at `1` as a ring homomorphism `(ℤ →ₗ[ℤ] ℤ) →+* ℤ`. This packages
"multiplication by an integer on `ℤ`": a ℤ-linear endomorphism of `ℤ` is exactly
multiplication by its value at `1`, and this assignment is a ring homomorphism
(`map_one` gives the identity ↦ `1`, `map_mul` gives composition ↦ product). -/
def evalAtOneℤ : (ℤ →ₗ[ℤ] ℤ) →+* ℤ where
  toFun f := f 1
  map_one' := rfl
  map_mul' f g := by
    change (f.comp g) 1 = f 1 * g 1
    simp [LinearMap.comp_apply]
  map_zero' := rfl
  map_add' _ _ := rfl

/-- A ℤ-linear endomorphism of `ℤ` acts by multiplication by its value at `1`. -/
theorem endℤ_acts_by_evalAtOne (f : ℤ →ₗ[ℤ] ℤ) (x : ℤ) : f x = evalAtOneℤ f * x := by
  have h_linear : f x = x • f 1 := by rw [← map_smul, smul_eq_mul, mul_one]
  exact h_linear.trans (by rw [mul_comm]; rfl)

/-- Evaluation at `1` is a bijection of `(ℤ →ₗ[ℤ] ℤ)` onto `ℤ`. -/
theorem evalAtOneℤ_bijective : Function.Bijective evalAtOneℤ := by
  constructor
  · intro f g hfg
    exact LinearMap.ext fun x => by
      rw [endℤ_acts_by_evalAtOne f x, endℤ_acts_by_evalAtOne g x, hfg]
  · intro x
    exact ⟨x • LinearMap.id, by simp [evalAtOneℤ]⟩

/-! ## Scalar extraction from `End` of a rank-one `ℤ`-module -/

/-- Given an isomorphism `e : M ≅ ℤ` of `ℤ`-modules, the ring homomorphism
`End M →+* ℤ` extracting the integer scalar by which an endomorphism acts:
conjugate `End M` into `End ℤ = (ℤ →ₗ[ℤ] ℤ)` and evaluate at `1`. -/
def degreeRingHomOfIso (M : ModuleCat.{0} ℤ) (e : M ≅ ModuleCat.of ℤ ℤ) :
    End M →+* ℤ :=
  evalAtOneℤ.comp <|
    ((LinearEquiv.conjRingEquiv e.toLinearEquiv).toRingHom).comp
      (ModuleCat.endRingEquiv M).toRingHom

/-- `degreeRingHomOfIso` is in fact a ring isomorphism `End M ≃+* ℤ`: every
component (the endomorphism-ring equivalence, the conjugation, and evaluation at
`1`) is a bijection. -/
def degreeRingEquivOfIso (M : ModuleCat.{0} ℤ) (e : M ≅ ModuleCat.of ℤ ℤ) :
    End M ≃+* ℤ :=
  ((ModuleCat.endRingEquiv M).trans (LinearEquiv.conjRingEquiv e.toLinearEquiv)).trans
    (RingEquiv.ofBijective evalAtOneℤ evalAtOneℤ_bijective)

/-- The ring equivalence `degreeRingEquivOfIso` acts as `degreeRingHomOfIso` on elements. -/
@[simp]
theorem degreeRingEquivOfIso_apply (M : ModuleCat.{0} ℤ)
    (e : M ≅ ModuleCat.of ℤ ℤ) (a : End M) :
    degreeRingEquivOfIso M e a = degreeRingHomOfIso M e a := rfl

/-! ## The conditional degree relative to a chosen identification `Hₙ(Sⁿ) ≅ ℤ` -/

/-- The integer **degree of `f` relative to a chosen isomorphism**
`e : Hₙ(Sⁿ; ℤ) ≅ ℤ`. Later modules supply a canonical positive-dimensional
isomorphism and expose an unconditional orientation-based degree. -/
def degreeOfIso {n : ℕ}
    (e : (singularHomologyℤ n).obj (TopCat.sphere.{0} n) ≅ ModuleCat.of ℤ ℤ)
    (f : C(Sphere n, Sphere n)) : ℤ :=
  degreeRingHomOfIso _ e (inducedOnTopHomology f)

/-- The degree of the identity map is `1`. -/
@[simp]
theorem degreeOfIso_id {n : ℕ}
    (e : (singularHomologyℤ n).obj (TopCat.sphere.{0} n) ≅ ModuleCat.of ℤ ℤ) :
    degreeOfIso e (ContinuousMap.id (Sphere n)) = 1 := by
  rw [degreeOfIso, inducedOnTopHomology_id]
  exact map_one _

/-- The degree is multiplicative under composition:
`degree (g ∘ f) = degree g * degree f`. -/
theorem degreeOfIso_comp {n : ℕ}
    (e : (singularHomologyℤ n).obj (TopCat.sphere.{0} n) ≅ ModuleCat.of ℤ ℤ)
    (f g : C(Sphere n, Sphere n)) :
    degreeOfIso e (g.comp f) = degreeOfIso e g * degreeOfIso e f := by
  unfold degreeOfIso
  rw [← RingHom.map_mul, inducedOnTopHomology_comp_mul]

/-- **Choice independence.** The relative degree does not depend on the chosen
identification `e : Hₙ(Sⁿ; ℤ) ≅ ℤ`: any two choices give the same integer. This is
because every component of `degreeRingHomOfIso` is a ring isomorphism, so the
extracted scalar is read off the intrinsic ring `End M`, and any two ring
homomorphisms `ℤ →+* ℤ` agree. -/
theorem degreeOfIso_well_defined {n : ℕ}
    (e e' : (singularHomologyℤ n).obj (TopCat.sphere.{0} n) ≅ ModuleCat.of ℤ ℤ)
    (f : C(Sphere n, Sphere n)) :
    degreeOfIso e f = degreeOfIso e' f := by
  have key :
      (degreeRingEquivOfIso _ e).toRingHom.comp (degreeRingEquivOfIso _ e').symm.toRingHom
        = RingHom.id ℤ := Subsingleton.elim _ _
  have h := RingHom.ext_iff.mp key (degreeRingEquivOfIso _ e' (inducedOnTopHomology f))
  rw [RingHom.comp_apply, RingHom.id_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.coe_toRingHom,
    RingEquiv.symm_apply_apply, degreeRingEquivOfIso_apply,
    degreeRingEquivOfIso_apply] at h
  exact h

/-! ## Homotopy invariance of the degree (conditional on the prism operator)

These wrappers feed the conditional homotopy-invariance theorem
(`singularHomologyMap_eq_of_homotopic`, `HomotopyInvariance.lean`) into the
degree layer. They are stated conditionally on the required prism operator
`SingularPrismOperator` — there is
Once the algebraic prism is constructed, every statement here becomes
unconditional with no further change. -/

/-- The model transport of a self-map of `Sphere n` is conjugate, on underlying
spaces, to the original continuous map: homotopic self-maps `f, g` transport to
`TopCat.sphere n` self-morphisms whose underlying continuous maps are homotopic.

This is `ContinuousMap.Homotopic.comp` applied to the conjugation by the bridge
isomorphism `topCatSphereIso`. -/
theorem toTopCatSphereSelfMap_hom_homotopic {n : ℕ} {f g : C(Sphere n, Sphere n)}
    (h : ContinuousMap.Homotopic f g) :
    ContinuousMap.Homotopic (toTopCatSphereSelfMap f).hom (toTopCatSphereSelfMap g).hom := by
  have e : ∀ k : C(Sphere n, Sphere n),
      (toTopCatSphereSelfMap k).hom
        = ((topCatSphereIso n).inv.hom).comp
            (k.comp ((topCatSphereIso n).hom.hom)) := by
    intro k
    simp [toTopCatSphereSelfMap, TopCat.hom_comp, ContinuousMap.comp_assoc]
  rw [e f, e g]
  exact (ContinuousMap.Homotopic.refl _).comp
    (h.comp (ContinuousMap.Homotopic.refl _))

/-- **Conditional homotopy invariance of the induced top-homology endomorphism.**

Assuming the prism operator, homotopic self-maps `f, g : C(Sphere n, Sphere n)`
induce the *same* endomorphism of `Hₙ(TopCat.sphere n; ℤ)`. -/
theorem inducedOnTopHomology_eq_of_homotopic
    (prism : SingularPrismOperator) {n : ℕ} {f g : C(Sphere n, Sphere n)}
    (h : ContinuousMap.Homotopic f g) :
    inducedOnTopHomology f = inducedOnTopHomology g :=
  singularHomologyMap_eq_of_homotopic prism (toTopCatSphereSelfMap_hom_homotopic h) n

/-- **Conditional homotopy invariance of the degree.**

Assuming the prism operator, homotopic self-maps of `Sphere n` have equal degree
(relative to any chosen identification `e : Hₙ(Sⁿ; ℤ) ≅ ℤ`). This is the form the
sphere-degree theory consumes: the integer degree is a homotopy invariant. -/
theorem degreeOfIso_eq_of_homotopic
    (prism : SingularPrismOperator) {n : ℕ}
    (e : (singularHomologyℤ n).obj (TopCat.sphere.{0} n) ≅ ModuleCat.of ℤ ℤ)
    {f g : C(Sphere n, Sphere n)} (h : ContinuousMap.Homotopic f g) :
    degreeOfIso e f = degreeOfIso e g := by
  unfold degreeOfIso
  rw [inducedOnTopHomology_eq_of_homotopic prism h]

end SphereOddDegree
