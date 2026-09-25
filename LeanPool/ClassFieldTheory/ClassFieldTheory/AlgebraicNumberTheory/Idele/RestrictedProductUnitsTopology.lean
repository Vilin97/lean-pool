/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
public import Mathlib.Topology.Algebra.RestrictedProduct.Units
/-!
# Topology on units of a restricted product

For the cofinite restricted product, Mathlib's algebraic `unitsEquiv`
is a topological group equivalence when each distinguished local submonoid
is open. The units on the left carry their graph topology; the right side
has the restricted-product topology of the local unit groups.
-/

@[expose] public section

open Filter
open scoped RestrictedProduct

noncomputable section

namespace RestrictedProduct

universe u v w

variable {ι : Type u} {R : ι → Type v}
  [∀ i, Monoid (R i)] [∀ i, TopologicalSpace (R i)]
variable {S : ι → Type w}
  [∀ i, SetLike (S i) (R i)] [∀ i, SubmonoidClass (S i) (R i)]
variable {B : ∀ i, S i}

private def inclusionMonoidHom {𝓕 𝓖 : Filter ι} (h : 𝓕 ≤ 𝓖) :
    (Πʳ i, [R i, B i]_[𝓖]) →* (Πʳ i, [R i, B i]_[𝓕]) where
  toFun := inclusion R (fun i => (B i : Set (R i))) h
  map_one' := rfl
  map_mul' _ _ := rfl

/-- At a principal filter, the algebraic equivalence of units is already a
topological group equivalence; no openness assumption is needed. -/
private noncomputable def unitsEquivPrincipal (T : Set ι) :
    (Πʳ i, [R i, B i]_[𝓟 T])ˣ ≃ₜ*
      (Πʳ i, [(R i)ˣ, (Submonoid.ofClass (B i)).units]_[𝓟 T]) := by
  let e := unitsEquiv (B := B) (𝓕 := 𝓟 T) R
  refine { toMulEquiv := e, continuous_toFun := ?_, continuous_invFun := ?_ }
  · apply (isEmbedding_coe_of_principal
      (R := fun i => (R i)ˣ)
      (A := fun i => ((Submonoid.ofClass (B i)).units : Set (R i)ˣ))).continuous_iff.mpr
    have hmap : Continuous
        (Units.map (coeMonoidHom (B := B) (𝓕 := 𝓟 T))) :=
      (continuous_coe (R := R) (A := fun i => (B i : Set (R i)))).units_map _
    have h : Continuous (fun x : (Πʳ i, [R i, B i]_[𝓟 T])ˣ =>
        ContinuousMulEquiv.piUnits
          (Units.map (coeMonoidHom (B := B) (𝓕 := 𝓟 T)) x)) :=
      ContinuousMulEquiv.piUnits.continuous.comp hmap
    refine h.congr ?_
    intro x
    funext i
    rfl
  · have hCoe : Topology.IsEmbedding
        (coeMonoidHom (B := B) (𝓕 := 𝓟 T) :
          (Πʳ i, [R i, B i]_[𝓟 T]) →* Π i, R i) :=
      isEmbedding_coe_of_principal
    have hEmbedding : Topology.IsEmbedding
        (Units.map (coeMonoidHom (B := B) (𝓕 := 𝓟 T))) :=
      hCoe.units_map
    apply hEmbedding.continuous_iff.mpr
    have h : Continuous (fun y :
        (Πʳ i, [(R i)ˣ, (Submonoid.ofClass (B i)).units]_[𝓟 T]) =>
        ContinuousMulEquiv.piUnits.symm (y : Π i, (R i)ˣ)) :=
      ContinuousMulEquiv.piUnits.symm.continuous.comp continuous_coe
    refine h.congr ?_
    intro y
    apply Units.ext
    funext i
    rfl

/-- The principal-stage inclusion of ring restricted products induces an
open embedding of their unit groups when the distinguished submonoids are open. -/
private theorem isOpenEmbedding_units_inclusion
    (hBopen : ∀ i, IsOpen (B i : Set (R i)))
    {T : Set ι} (hT : cofinite ≤ 𝓟 T) :
    Topology.IsOpenEmbedding (Units.map (inclusionMonoidHom (B := B) hT)) := by
  have hRing : Topology.IsOpenEmbedding
      (inclusion R (fun i => (B i : Set (R i))) hT) :=
    isOpenEmbedding_inclusion_principal hBopen hT
  exact Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    (hRing.continuous.units_map _)
    (Units.map_injective hRing.injective)
    (Units.isOpenMap_map hRing.injective hRing.isOpenMap)

/-- For open distinguished local submonoids, Mathlib's restricted-product
unit equivalence is an equivalence of topological groups. -/
noncomputable def unitsContinuousMulEquiv
    (hBopen : ∀ i, IsOpen (B i : Set (R i))) :
    (Πʳ i, [R i, B i])ˣ ≃ₜ*
      (Πʳ i, [(R i)ˣ, (Submonoid.ofClass (B i)).units]) := by
  let e := unitsEquiv (B := B) (𝓕 := cofinite) R
  refine { toMulEquiv := e, continuous_toFun := ?_, continuous_invFun := ?_ }
  · rw [continuous_iff_continuousAt]
    intro x
    let T : Set ι := {i | e x i ∈ (Submonoid.ofClass (B i)).units}
    have hT : cofinite ≤ 𝓟 T := le_principal_iff.mpr (e x).2
    let y : Πʳ i, [(R i)ˣ, (Submonoid.ofClass (B i)).units]_[𝓟 T] :=
      ⟨(e x).1, fun i hi => hi⟩
    let x' : (Πʳ i, [R i, B i]_[𝓟 T])ˣ :=
      (unitsEquivPrincipal (B := B) T).symm y
    have hx : Units.map (inclusionMonoidHom (B := B) hT) x' = x := by
      apply Units.ext
      apply RestrictedProduct.ext
      intro i
      rfl
    have hLocal : Continuous (fun z : (Πʳ i, [R i, B i]_[𝓟 T])ˣ =>
        e (Units.map (inclusionMonoidHom (B := B) hT) z)) := by
      have h := (continuous_inclusion (R := fun i => (R i)ˣ)
        (A := fun i => ((Submonoid.ofClass (B i)).units : Set (R i)ˣ)) hT).comp
          (unitsEquivPrincipal (B := B) T).continuous
      refine h.congr ?_
      intro z
      apply RestrictedProduct.ext
      intro i
      rfl
    rw [← hx]
    exact (isOpenEmbedding_units_inclusion (B := B) hBopen hT).continuousAt_iff.mp
      hLocal.continuousAt
  · apply (continuous_dom (R := fun i => (R i)ˣ)
      (A := fun i => ((Submonoid.ofClass (B i)).units : Set (R i)ˣ))).mpr
    intro T hT
    have h : Continuous (fun y :
        (Πʳ i, [(R i)ˣ, (Submonoid.ofClass (B i)).units]_[𝓟 T]) =>
        Units.map (inclusionMonoidHom (B := B) hT)
          ((unitsEquivPrincipal (B := B) T).symm y)) :=
      ((continuous_inclusion (R := R)
        (A := fun i => (B i : Set (R i))) hT).units_map _).comp
          (unitsEquivPrincipal (B := B) T).symm.continuous
    refine h.congr ?_
    intro y
    apply Units.ext
    apply RestrictedProduct.ext
    intro i
    rfl

end RestrictedProduct
