/-
Copyright (c) 2026 Arthur Freitas Ramos et al. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
import Mathlib.GroupTheory.CoprodI
import Mathlib.GroupTheory.DoubleCoset
import Mathlib.GroupTheory.FreeGroup.NielsenSchreier
import Mathlib.Algebra.Group.ULift
import LeanPool.Kurosh.KuroshTheorem

/-!
# Inclusion-preserving Kurosh decomposition

This statement bridge expresses the decomposition using subgroups of `H`
and their actual inclusion homomorphisms. It adapts the upstream Palomar
statement and proves it from the Bass–Serre development.

Adapted for Lean Pool from Arthur742Ramos/KuroshSubgroupTheorem,
commit `911707126c8b9bb0c764bf853008fe1053c0aad9`: imports, API compatibility,
and proof organization were revised.
-/

noncomputable section

universe u v

namespace GraphCoveringTheory.KuroshStatement

/-- The group free product expressed using Mathlib's indexed monoid coproduct. -/
abbrev FreeProduct {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] := Monoid.CoprodI G

/-- The canonical inclusion of an indexed factor into the free product. -/
def factorInclusion {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (i : ι) : G i →* FreeProduct G :=
  Monoid.CoprodI.of

/-- The image of a subgroup under conjugation by `g`. -/
def conjugateSubgroup {P : Type u} [Group P] (K : Subgroup P) (g : P) : Subgroup P :=
  K.map (MulAut.conj g)

/-- Intersect `H` with the conjugate of an indexed free factor. -/
def intersectionFactor {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) (i : ι)
    (g : FreeProduct G) : Subgroup (FreeProduct G) :=
  H ⊓ conjugateSubgroup (MonoidHom.range (factorInclusion G i)) g

/-- Regard the conjugate-factor intersection as a subgroup of `H`. -/
def intersectionFactorInH {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) (i : ι)
    (g : FreeProduct G) : Subgroup H :=
  (intersectionFactor G H i g).comap H.subtype

/-- The subgroup factors and a free group, lifted to a common universe. -/
def Component {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {J : Type (max u v)} (A : J → Subgroup H) (X : Type (max u v)) :
    (J ⊕ PUnit.{1}) → Type (max (u + 1) (v + 1)) :=
  Sum.elim
    (fun j => ULift.{max (u + 1) (v + 1)} (A j))
    (fun _ => ULift.{max (u + 1) (v + 1)} (FreeGroup X))

instance componentGroup {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {J : Type (max u v)} (A : J → Subgroup H) (X : Type (max u v))
    (q : J ⊕ PUnit.{1}) : Group (Component G H A X q) := by
  cases q using Sum.casesOn with
  | inl j =>
      change Group (ULift.{max (u + 1) (v + 1)} (A j))
      infer_instance
  | inr q =>
      change Group (ULift.{max (u + 1) (v + 1)} (FreeGroup X))
      infer_instance

/-- The free product of the specified subgroup factors and the free group. -/
abbrev Product {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {J : Type (max u v)} (A : J → Subgroup H) (X : Type (max u v)) :=
  Monoid.CoprodI (Component G H A X)

/-! The canonical maps from the displayed factors into `H`. -/

/-- Use actual subgroup inclusions on factors and the specified homomorphism on the free part. -/
def ComponentHom {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {J : Type (max u v)} (A : J → Subgroup H) (X : Type (max u v))
    (freePartMap : ULift.{max (u + 1) (v + 1)} (FreeGroup X) →* H) :
    ∀ q : J ⊕ PUnit.{1}, Component G H A X q →* H
  | Sum.inl j => by
      change ULift.{max (u + 1) (v + 1)} (A j) →* H
      exact
        { toFun := fun x => x.down.1
          map_one' := by simp
          map_mul' := by intro x y; simp }
  | Sum.inr _ => freePartMap

/-! The homomorphism induced by the actual factor inclusions. -/

/-- The free-product homomorphism induced by the subgroup inclusions and free-part map. -/
def inducedHom {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {J : Type (max u v)} (A : J → Subgroup H) (X : Type (max u v))
    (freePartMap : ULift.{max (u + 1) (v + 1)} (FreeGroup X) →* H) :
    Product G H A X →* H :=
  Monoid.CoprodI.lift (ComponentHom G H A X freePartMap)

/-! The checked proof of the Kurosh Palomar statement. -/

theorem kurosh_decomposition_with_inclusions {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :
    ∃ (J : Type (max u v)) (X : Type (max u v)) (A : J → Subgroup H),
      (∀ j, ∃ i : ι, ∃ g : FreeProduct G,
        A j = intersectionFactorInH G H i g) ∧
      ∃ (freePartMap : ULift.{max (u + 1) (v + 1)} (FreeGroup X) →* H),
        ∃ (decomposition : Product G H A X ≃* H),
          decomposition.toMonoidHom = inducedHom G H A X freePartMap := by
  let J := GraphCoveringTheory.Kurosh.KuroshActiveVertexIndex G H
  let X := IsFreeGroup.Generators (GraphCoveringTheory.Kurosh.KuroshFreePart G H)
  let A : J → Subgroup H := fun j =>
    GraphCoveringTheory.Kurosh.treeVertexStabilizer G H j.1
  have hfactor : ∀ j, ∃ i : ι, ∃ g : FreeProduct G,
      A j = intersectionFactorInH G H i g := by
    intro j
    rcases GraphCoveringTheory.Kurosh.kurosh_factor_is_conjugate_intersection
      G H j with ⟨i, g, h⟩
    refine ⟨i, g, ?_⟩
    simpa [A, intersectionFactorInH, intersectionFactor, conjugateSubgroup,
      factorInclusion, GraphCoveringTheory.Kurosh.intersectionFactorInH,
      GraphCoveringTheory.Kurosh.intersectionFactor,
      GraphCoveringTheory.Kurosh.conjugateSubgroup,
      GraphCoveringTheory.Kurosh.factorInclusion] using h
  let freeEquiv :
      ULift.{max (u + 1) (v + 1)} (FreeGroup X) ≃*
        ULift.{max (u + 1) (v + 1)} (GraphCoveringTheory.Kurosh.KuroshFreePart G H) :=
    (MulEquiv.ulift : ULift.{max (u + 1) (v + 1)} (FreeGroup X) ≃* FreeGroup X).trans
      (IsFreeGroup.toFreeGroup
        (GraphCoveringTheory.Kurosh.KuroshFreePart G H)).symm |>.trans
      (MulEquiv.ulift :
        ULift.{max (u + 1) (v + 1)} (GraphCoveringTheory.Kurosh.KuroshFreePart G H) ≃*
          GraphCoveringTheory.Kurosh.KuroshFreePart G H).symm
  let componentEquiv : ∀ q : J ⊕ PUnit.{1},
      Component G H A X q ≃*
        GraphCoveringTheory.Kurosh.KuroshActiveComponent G H q
    | Sum.inl j => by
        change ULift.{max (u + 1) (v + 1)} (A j) ≃*
          ULift.{max (u + 1) (v + 1)}
            (GraphCoveringTheory.Kurosh.treeVertexStabilizer G H j.1)
        exact MulEquiv.refl _
    | Sum.inr q => by
        change ULift.{max (u + 1) (v + 1)} (FreeGroup X) ≃*
          ULift.{max (u + 1) (v + 1)}
            (GraphCoveringTheory.Kurosh.KuroshFreePart G H)
        exact freeEquiv
  let forward : Product G H A X →*
      GraphCoveringTheory.Kurosh.KuroshActiveProduct G H :=
    Monoid.CoprodI.lift (fun q =>
      (Monoid.CoprodI.of :
        GraphCoveringTheory.Kurosh.KuroshActiveComponent G H q →*
          GraphCoveringTheory.Kurosh.KuroshActiveProduct G H).comp
        (componentEquiv q).toMonoidHom)
  let backward : GraphCoveringTheory.Kurosh.KuroshActiveProduct G H →*
      Product G H A X :=
    Monoid.CoprodI.lift (fun q =>
      (Monoid.CoprodI.of : Component G H A X q →* Product G H A X).comp
        (componentEquiv q).symm.toMonoidHom)
  have hforward : backward.comp forward = MonoidHom.id (Product G H A X) := by
    apply Monoid.CoprodI.ext_hom
    intro q
    apply MonoidHom.ext
    intro x
    change Monoid.CoprodI.of
        ((componentEquiv q).symm ((componentEquiv q) x)) =
      Monoid.CoprodI.of x
    rw [MulEquiv.symm_apply_apply]
  have hbackward : forward.comp backward =
      MonoidHom.id (GraphCoveringTheory.Kurosh.KuroshActiveProduct G H) := by
    apply Monoid.CoprodI.ext_hom
    intro q
    apply MonoidHom.ext
    intro x
    change Monoid.CoprodI.of
        ((componentEquiv q) ((componentEquiv q).symm x)) =
      Monoid.CoprodI.of x
    rw [MulEquiv.apply_symm_apply]
  let productEquiv : Product G H A X ≃*
      GraphCoveringTheory.Kurosh.KuroshActiveProduct G H :=
    { toFun := forward
      invFun := backward
      left_inv := by
        intro z
        exact congrArg (fun f : Product G H A X →* Product G H A X => f z)
          hforward
      right_inv := by
        intro z
        exact congrArg
          (fun f : GraphCoveringTheory.Kurosh.KuroshActiveProduct G H →*
            GraphCoveringTheory.Kurosh.KuroshActiveProduct G H => f z) hbackward
      map_mul' := forward.map_mul }
  let activeEquiv := GraphCoveringTheory.Kurosh.kuroshActiveEquivH G H
  let freePartMap :
      ULift.{max (u + 1) (v + 1)} (FreeGroup X) →* H :=
    activeEquiv.toMonoidHom.comp
      ((Monoid.CoprodI.of :
        GraphCoveringTheory.Kurosh.KuroshActiveComponent G H
            (Sum.inr PUnit.unit) →*
          GraphCoveringTheory.Kurosh.KuroshActiveProduct G H).comp
        (componentEquiv (Sum.inr PUnit.unit)).toMonoidHom)
  let decomposition : Product G H A X ≃* H :=
    productEquiv.trans activeEquiv
  have hdecomposition :
      decomposition.toMonoidHom = inducedHom G H A X freePartMap := by
    apply Monoid.CoprodI.ext_hom
    intro q
    apply MonoidHom.ext
    intro x
    cases q using Sum.casesOn with
    | inl j =>
        change activeEquiv
            ((Monoid.CoprodI.of :
              @GraphCoveringTheory.Kurosh.KuroshActiveComponent.{u, v, 0} ι G _ H
                  (Sum.inl j) →*
                GraphCoveringTheory.Kurosh.KuroshActiveProduct G H)
              ((componentEquiv (Sum.inl j)) x)) = x.down.1
        change activeEquiv
            (Monoid.CoprodI.of
              (show @GraphCoveringTheory.Kurosh.KuroshActiveComponent.{u, v, 0}
                  ι G _ H
                  (Sum.inl j) from ULift.up x.down)) = x.down.1
        change GraphCoveringTheory.Kurosh.treeKuroshProductMulEquivH G H
            (GraphCoveringTheory.Kurosh.activeProductToTree G H
              (Monoid.CoprodI.of
                (show @GraphCoveringTheory.Kurosh.KuroshActiveComponent.{u, v, 0}
                    ι G _ H
                    (Sum.inl j) from ULift.up x.down))) = x.down.1
        change GraphCoveringTheory.Kurosh.treeKuroshProductMulEquivH G H
            ((Monoid.CoprodI.lift
              (GraphCoveringTheory.Kurosh.activeComponentToTree G H))
              (Monoid.CoprodI.of
                (show @GraphCoveringTheory.Kurosh.KuroshActiveComponent.{u, v, 0}
                    ι G _ H
                    (Sum.inl j) from ULift.up x.down))) = x.down.1
        rw [Monoid.CoprodI.lift_of]
        change GraphCoveringTheory.Kurosh.treeKuroshProductMulEquivH G H
            (Monoid.CoprodI.of
              (show @GraphCoveringTheory.Kurosh.TreeKuroshComponent.{u, v, 0}
                  ι G _ H
                  (Sum.inl j.1) from ULift.up x.down)) = x.down.1
        exact @GraphCoveringTheory.Kurosh.treeKuroshProductToH_vertex.{u, v, 0}
          ι G _ H j.1 x.down
    | inr q =>
        change activeEquiv
            ((Monoid.CoprodI.of :
              @GraphCoveringTheory.Kurosh.KuroshActiveComponent.{u, v, 0} ι G _ H
                  (Sum.inr q) →*
                GraphCoveringTheory.Kurosh.KuroshActiveProduct G H)
              ((componentEquiv (Sum.inr q)) x)) = freePartMap x
        rfl
  exact ⟨J, X, A, hfactor, freePartMap, decomposition, hdecomposition⟩

end GraphCoveringTheory.KuroshStatement
