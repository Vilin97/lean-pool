/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.Basic
public import Mathlib.Topology.Category.TopCat.Sphere

/-!
# Bridge between `Sphere n` and `TopCat.sphere n`

The project uses the concrete metric-sphere subtype for antipodal actions and
quotients, while Mathlib's algebraic-topology APIs use `TopCat.sphere n`. This
module proves that the two models differ only by `ULift`, packages the resulting
homeomorphism and categorical isomorphism, and transports continuous maps
between the models with identity and composition laws.
-/

@[expose] public section
noncomputable section

open CategoryTheory

namespace SphereOddDegree

/-- The carrier type of `TopCat.sphere n` is *definitionally* `ULift (Sphere n)`:
the ambient space and the metric-sphere subtype agree exactly, and the only
difference is the universe-lifting `ULift` wrapper used by the `TopCat` object. -/
theorem topCatSphere_carrier_eq (n : ℕ) :
    (TopCat.sphere.{u} n : Type u) = ULift.{u, 0} (Sphere n) :=
  rfl

/-- `TopCat.sphere n` is homeomorphic to the raw subtype model `Sphere n`.
The homeomorphism is simply the universe-lift equivalence `Homeomorph.ulift`,
witnessing that the two models differ only by a `ULift` wrapper. -/
noncomputable def topCatSphereHomeomorph (n : ℕ) :
    (TopCat.sphere.{u} n : Type u) ≃ₜ Sphere n :=
  Homeomorph.ulift

/-- `TopCat.sphere n` is isomorphic, as an object of `TopCat`, to the raw subtype
model `Sphere n` packaged with `TopCat.of`. This is the categorical packaging of
`topCatSphereHomeomorph` through `TopCat.isoOfHomeo`; like the homeomorphism it
carries no mathematical content beyond the universe-lifting `ULift` wrapper.

Use this to transport `TopCat`-phrased algebraic-topology constructions (e.g.
categorical (co)homology of `TopCat.sphere n`) onto the library's working model
`Sphere n`. -/
noncomputable def topCatSphereIso (n : ℕ) :
    TopCat.sphere.{0} n ≅ TopCat.of (Sphere n) :=
  TopCat.isoOfHomeo (topCatSphereHomeomorph n)

/-! ## Coercion simp lemmas

The homeomorphism `topCatSphereHomeomorph` and the categorical isomorphism
`topCatSphereIso` are both the universe-`ULift` wrapper, so their underlying maps
are `ULift.down` (forward) and `ULift.up` (backward). These `rfl` lemmas expose
that to `simp`, letting downstream proofs evaluate the bridge maps on points. -/

/-- The forward homeomorphism `TopCat.sphere n → Sphere n` is `ULift.down`. -/
@[simp]
theorem topCatSphereHomeomorph_apply {n : ℕ} (x : (TopCat.sphere.{u} n : Type u)) :
    topCatSphereHomeomorph n x = x.down := rfl

/-- The inverse homeomorphism `Sphere n → TopCat.sphere n` is `ULift.up`. -/
@[simp]
theorem topCatSphereHomeomorph_symm_apply {n : ℕ} (y : Sphere n) :
    (topCatSphereHomeomorph n).symm y = (ULift.up y : (TopCat.sphere.{u} n : Type u)) :=
  rfl

/-- The `hom` component of `topCatSphereIso` acts by `ULift.down`. -/
@[simp]
theorem topCatSphereIso_hom_apply {n : ℕ} (x : (TopCat.sphere.{0} n : Type)) :
    (topCatSphereIso n).hom x = x.down := rfl

/-- The `inv` component of `topCatSphereIso` acts by `ULift.up`. -/
@[simp]
theorem topCatSphereIso_inv_apply {n : ℕ} (y : Sphere n) :
    (topCatSphereIso n).inv y = (ULift.up y : (TopCat.sphere.{0} n : Type)) := rfl

/-- The `hom` of `topCatSphereIso` is `TopCat.ofHom` of the bundled homeomorphism
(viewed as a continuous map). This identifies the categorical isomorphism with
the homeomorphism at the level of `TopCat` morphisms. -/
theorem topCatSphereIso_hom_eq {n : ℕ} :
    (topCatSphereIso n).hom
      = TopCat.ofHom (X := TopCat.sphere.{0} n) (Y := TopCat.of (Sphere n))
          (topCatSphereHomeomorph n : C((TopCat.sphere.{0} n : Type), Sphere n)) :=
  rfl

/-- The `inv` of `topCatSphereIso` is `TopCat.ofHom` of the inverse homeomorphism
(viewed as a continuous map). -/
theorem topCatSphereIso_inv_eq {n : ℕ} :
    (topCatSphereIso n).inv
      = TopCat.ofHom (X := TopCat.of (Sphere n)) (Y := TopCat.sphere.{0} n)
          ((topCatSphereHomeomorph n).symm : C(Sphere n, (TopCat.sphere.{0} n : Type))) :=
  rfl

/-! ## Model transport of continuous maps to `TopCat.sphere`

Transport a continuous map between the raw sphere models into a `TopCat`
morphism between the categorical sphere objects, by conjugating with
`topCatSphereIso`. This is the general (possibly dimension-changing) form of the
self-map transport used by the degree layer, and it is the basic input for
feeding sphere maps to a `TopCat`-phrased (co)homology functor. It is functorial
(`toTopCatSphereMap_id`, `toTopCatSphereMap_comp`) and is conjugate to the
original map through the homeomorphisms
(`topCatSphereHomeomorph_toTopCatSphereMap`). -/

/-- Transport a continuous map `Sphere n → Sphere m` to a morphism of the
categorical sphere objects `TopCat.sphere n ⟶ TopCat.sphere m`, by conjugating
with the bridge isomorphism `topCatSphereIso`. -/
noncomputable def toTopCatSphereMap {n m : ℕ} (f : C(Sphere n, Sphere m)) :
    TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} m :=
  (topCatSphereIso n).hom ≫ TopCat.ofHom f ≫ (topCatSphereIso m).inv

/-- The transported morphism evaluates as `f` on the underlying points (modulo
the `ULift` wrapper): it sends `ULift.up x ↦ ULift.up (f x)`. -/
@[simp]
theorem toTopCatSphereMap_apply {n m : ℕ} (f : C(Sphere n, Sphere m))
    (x : (TopCat.sphere.{0} n : Type)) :
    (toTopCatSphereMap f) x = ULift.up (f x.down) := rfl

/-- The transport sends the identity continuous map to the identity morphism. -/
@[simp]
theorem toTopCatSphereMap_id (n : ℕ) :
    toTopCatSphereMap (ContinuousMap.id (Sphere n)) = 𝟙 _ :=
  TopCat.hom_ext_iff.mpr rfl

/-- The transport is functorial: it turns composition of continuous maps into
composition of `TopCat` morphisms (in the same order). -/
theorem toTopCatSphereMap_comp {n m k : ℕ} (f : C(Sphere n, Sphere m))
    (g : C(Sphere m, Sphere k)) :
    toTopCatSphereMap (g.comp f)
      = toTopCatSphereMap f ≫ toTopCatSphereMap g := by
  unfold toTopCatSphereMap
  simp [TopCat.ofHom_comp]

/-- Naturality of the transport with respect to the homeomorphism bridge: the
transported morphism is conjugate to `f` through `topCatSphereHomeomorph`.
This is the compatibility lemma a (co)homology functor consumes when comparing
the induced map of `toTopCatSphereMap f` with that of `f`. -/
theorem topCatSphereHomeomorph_toTopCatSphereMap {n m : ℕ} (f : C(Sphere n, Sphere m))
    (x : (TopCat.sphere.{0} n : Type)) :
    topCatSphereHomeomorph m ((toTopCatSphereMap f) x)
      = f (topCatSphereHomeomorph n x) := rfl

end SphereOddDegree
