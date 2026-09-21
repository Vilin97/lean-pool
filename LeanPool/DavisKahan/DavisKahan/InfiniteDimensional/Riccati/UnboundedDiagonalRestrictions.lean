/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.Riccati.UnboundedCoordinateRestrictions
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.AbstractSpectrum

/-!
# Coordinate restrictions of a reduced unbounded direct-sum operator

A partial map reducing the first coordinate summand induces partial maps on
both coordinates, and its direct sum has the same operator domain and action as
the original reduced map.  The final result is stated as an identity-unitary
equivalence so that both directions of domain transport remain explicit.

Density and closedness of the coordinate restrictions are separate theorems
rather than fields, matching the canonical `LinearPMap` representation: the
restriction itself is defined without either hypothesis, and each property is
inherited from the corresponding property of the ambient map.
-/

namespace TauCeti
namespace DavisKahanExt

open DavisKahan.Foundation

open scoped InnerProductSpace
open Filter Topology

variable {E0 : Type*} [NormedAddCommGroup E0] [InnerProductSpace ℂ E0]
  [CompleteSpace E0]
variable {E1 : Type*} [NormedAddCommGroup E1] [InnerProductSpace ℂ E1]
  [CompleteSpace E1]

/-- The first coordinate restriction of a partial map on the direct sum.  No
reduction hypothesis is needed to *define* it; reduction is what makes it agree
with the ambient action, which is the content of the theorems below. -/
noncomputable def coordinateRestriction0
    (D : DirectSumPMap (E0 := E0) (E1 := E1)) : E0 →ₗ.[ℂ] E0 where
  domain := coordinateRestrictionDomain0 D
  toFun := coordinateRestrictionMap0 D

/-- The second coordinate restriction of a partial map on the direct sum. -/
noncomputable def coordinateRestriction1
    (D : DirectSumPMap (E0 := E0) (E1 := E1)) : E1 →ₗ.[ℂ] E1 where
  domain := coordinateRestrictionDomain1 D
  toFun := coordinateRestrictionMap1 D

omit [CompleteSpace E0] [CompleteSpace E1] in
/-- The domain of the first coordinate restriction is `coordinateRestrictionDomain0 D`. -/
@[simp] theorem coordinateRestriction0_domain
    (D : DirectSumPMap (E0 := E0) (E1 := E1)) :
    (coordinateRestriction0 D).domain = coordinateRestrictionDomain0 D := rfl

omit [CompleteSpace E0] [CompleteSpace E1] in
/-- The domain of the second coordinate restriction is `coordinateRestrictionDomain1 D`. -/
@[simp] theorem coordinateRestriction1_domain
    (D : DirectSumPMap (E0 := E0) (E1 := E1)) :
    (coordinateRestriction1 D).domain = coordinateRestrictionDomain1 D := rfl

omit [CompleteSpace E0] [CompleteSpace E1] in
/-- The first coordinate restriction acts by `coordinateRestrictionMap0`. -/
@[simp] theorem coordinateRestriction0_apply
    (D : DirectSumPMap (E0 := E0) (E1 := E1))
    (u : (coordinateRestriction0 D).domain) :
    coordinateRestriction0 D u = coordinateRestrictionMap0 D u := rfl

omit [CompleteSpace E0] [CompleteSpace E1] in
/-- `coordinateRestriction0_apply` composed with `coordinateRestrictionMap0_apply`, in one step.

Both steps individually are `rfl`, but chaining them under `simp` does not work: the first
lemma's argument is typed `(coordinateRestriction0 D).domain` and the second's
`coordinateRestrictionDomain0 D`, and those are equal only definitionally -- `simp` matches at
`instances` transparency and will not cross the gap.  This states the composite directly so
one rewrite does the whole job. -/
@[simp] theorem coordinateRestriction0_apply'
    (D : DirectSumPMap (E0 := E0) (E1 := E1))
    (u : (coordinateRestriction0 D).domain) :
    coordinateRestriction0 D u =
      WithLp.fst (D (coordinateRestrictionDomain0ToOriginal D u)) := rfl

omit [CompleteSpace E0] [CompleteSpace E1] in
/-- The second coordinate restriction acts by `coordinateRestrictionMap1`. -/
@[simp] theorem coordinateRestriction1_apply
    (D : DirectSumPMap (E0 := E0) (E1 := E1))
    (v : (coordinateRestriction1 D).domain) :
    coordinateRestriction1 D v = coordinateRestrictionMap1 D v := rfl

omit [CompleteSpace E0] [CompleteSpace E1] in
/-- The composite of `coordinateRestriction1_apply` and `coordinateRestrictionMap1_apply`; see
`coordinateRestriction0_apply'` for why the one-step form is needed. -/
@[simp] theorem coordinateRestriction1_apply'
    (D : DirectSumPMap (E0 := E0) (E1 := E1))
    (v : (coordinateRestriction1 D).domain) :
    coordinateRestriction1 D v =
      WithLp.snd (D (coordinateRestrictionDomain1ToOriginal D v)) := rfl

/-- A reducing dense domain restricts to a dense first-coordinate domain. -/
theorem coordinateRestriction0_dense
    (D : DirectSumPMap (E0 := E0) (E1 := E1))
    (hdense : Dense (D.domain : Set (DirectSumSpace (E0 := E0) (E1 := E1))))
    (hred : TauCeti.LinearPMap.ReducesSubspace D
      (unboundedBlockGraph (0 : E0 →L[ℂ] E1))) :
    Dense ((coordinateRestriction0 D).domain : Set E0) := by
  rw [dense_iff_closure_eq]
  ext u
  simp only [Set.mem_univ, iff_true]
  have hu0 :
      blockCoordinate0 (𝕜 := ℂ) (E0 := E0) (E1 := E1) u ∈
        closure (D.domain : Set (DirectSumSpace (E0 := E0) (E1 := E1))) := by
    rw [hdense.closure_eq]
    trivial
  obtain ⟨s, hs, hs_lim⟩ := mem_closure_iff_seq_limit.mp hu0
  refine mem_closure_iff_seq_limit.mpr
    ⟨fun n => WithLp.fst (s n), ?_, ?_⟩
  · intro n
    change blockCoordinate0 (𝕜 := ℂ) (E0 := E0) (E1 := E1)
        (WithLp.fst (s n)) ∈ D.domain
    let x : D.domain := ⟨s n, hs n⟩
    have hx := hred.1 x
    change (unboundedBlockGraph (0 : E0 →L[ℂ] E1)).starProjection
        (s n) ∈ D.domain at hx
    rw [zeroUnboundedGraph_starProjection_apply] at hx
    exact hx
  · have hlim :=
      ((WithLp.fstL 2 ℂ E0 E1).continuous.tendsto
        (blockCoordinate0 (𝕜 := ℂ) (E0 := E0) (E1 := E1) u)).comp hs_lim
    change Filter.Tendsto (fun n => WithLp.fst (s n)) Filter.atTop
      (nhds (WithLp.fst
        (blockCoordinate0 (𝕜 := ℂ) (E0 := E0) (E1 := E1) u))) at hlim
    simpa using hlim

/-- A reducing dense domain restricts to a dense second-coordinate domain. -/
theorem coordinateRestriction1_dense
    (D : DirectSumPMap (E0 := E0) (E1 := E1))
    (hdense : Dense (D.domain : Set (DirectSumSpace (E0 := E0) (E1 := E1))))
    (hred : TauCeti.LinearPMap.ReducesSubspace D
      (unboundedBlockGraph (0 : E0 →L[ℂ] E1))) :
    Dense ((coordinateRestriction1 D).domain : Set E1) := by
  rw [dense_iff_closure_eq]
  ext v
  simp only [Set.mem_univ, iff_true]
  have hv1 :
      blockCoordinate1 (𝕜 := ℂ) (E0 := E0) (E1 := E1) v ∈
        closure (D.domain : Set (DirectSumSpace (E0 := E0) (E1 := E1))) := by
    rw [hdense.closure_eq]
    trivial
  obtain ⟨s, hs, hs_lim⟩ := mem_closure_iff_seq_limit.mp hv1
  refine mem_closure_iff_seq_limit.mpr
    ⟨fun n => WithLp.snd (s n), ?_, ?_⟩
  · intro n
    change blockCoordinate1 (𝕜 := ℂ) (E0 := E0) (E1 := E1)
        (WithLp.snd (s n)) ∈ D.domain
    let x : D.domain := ⟨s n, hs n⟩
    have hx := hred.2.1 x
    change (unboundedBlockGraph (0 : E0 →L[ℂ] E1))ᗮ.starProjection
        (s n) ∈ D.domain at hx
    rw [zeroUnboundedGraph_orthogonalProjection_apply] at hx
    exact hx
  · have hlim :=
      ((WithLp.sndL 2 ℂ E0 E1).continuous.tendsto
        (blockCoordinate1 (𝕜 := ℂ) (E0 := E0) (E1 := E1) v)).comp hs_lim
    change Filter.Tendsto (fun n => WithLp.snd (s n)) Filter.atTop
      (nhds (WithLp.snd
        (blockCoordinate1 (𝕜 := ℂ) (E0 := E0) (E1 := E1) v))) at hlim
    simpa using hlim

/-- A reducing closed graph restricts to a closed first-coordinate graph. -/
theorem coordinateRestriction0_closedGraph
    (D : DirectSumPMap (E0 := E0) (E1 := E1))
    (hclosed : IsClosed (Set.range fun x : D.domain =>
      ((x : DirectSumSpace (E0 := E0) (E1 := E1)), D x)))
    (hred : TauCeti.LinearPMap.ReducesSubspace D
      (unboundedBlockGraph (0 : E0 →L[ℂ] E1))) :
    IsClosed (Set.range fun u : (coordinateRestriction0 D).domain =>
      ((u : E0), coordinateRestriction0 D u)) := by
  let coords : E0 × E0 →
      DirectSumSpace (E0 := E0) (E1 := E1) ×
        DirectSumSpace (E0 := E0) (E1 := E1) :=
    fun p =>
      (blockCoordinate0 (𝕜 := ℂ) (E0 := E0) (E1 := E1) p.1,
       blockCoordinate0 (𝕜 := ℂ) (E0 := E0) (E1 := E1) p.2)
  have hcoords : Continuous coords := by
    fun_prop
  rw [show Set.range (fun u : (coordinateRestriction0 D).domain =>
      ((u : E0), coordinateRestriction0 D u)) =
      coords ⁻¹' (Set.range fun x : D.domain =>
        (((x : D.domain) : DirectSumSpace (E0 := E0) (E1 := E1)), D x)) by
    ext p
    constructor
    · rintro ⟨u, rfl⟩
      refine ⟨coordinateRestrictionDomain0ToOriginal D u, ?_⟩
      apply Prod.ext
      · rfl
      · exact coordinateRestriction0_action_eq D hred u
    · rintro ⟨x, hx⟩
      have hfst :
          ((x : D.domain) : DirectSumSpace (E0 := E0) (E1 := E1)) =
            blockCoordinate0 (𝕜 := ℂ) (E0 := E0) (E1 := E1) p.1 :=
        congrArg Prod.fst hx
      have hsnd :
          D x = blockCoordinate0 (𝕜 := ℂ) (E0 := E0) (E1 := E1) p.2 :=
        congrArg Prod.snd hx
      have hp1 : p.1 ∈ coordinateRestrictionDomain0 D := by
        change blockCoordinate0 (𝕜 := ℂ) (E0 := E0) (E1 := E1) p.1 ∈ D.domain
        rw [← hfst]
        exact x.property
      let u : coordinateRestrictionDomain0 D := ⟨p.1, hp1⟩
      have hux : coordinateRestrictionDomain0ToOriginal D u = x := by
        apply Subtype.ext
        exact hfst.symm
      refine ⟨u, Prod.ext rfl ?_⟩
      have hact := coordinateRestriction0_action_eq D hred u
      rw [hux, hsnd] at hact
      have hcoord := congrArg WithLp.fst hact
      -- `simp` cannot bridge the two spellings of the restriction domain; `exact` checks the
      -- (definitional) equality directly.
      exact hcoord.symm]
  exact hclosed.preimage hcoords

/-- A reducing closed graph restricts to a closed second-coordinate graph. -/
theorem coordinateRestriction1_closedGraph
    (D : DirectSumPMap (E0 := E0) (E1 := E1))
    (hclosed : IsClosed (Set.range fun x : D.domain =>
      ((x : DirectSumSpace (E0 := E0) (E1 := E1)), D x)))
    (hred : TauCeti.LinearPMap.ReducesSubspace D
      (unboundedBlockGraph (0 : E0 →L[ℂ] E1))) :
    IsClosed (Set.range fun v : (coordinateRestriction1 D).domain =>
      ((v : E1), coordinateRestriction1 D v)) := by
  let coords : E1 × E1 →
      DirectSumSpace (E0 := E0) (E1 := E1) ×
        DirectSumSpace (E0 := E0) (E1 := E1) :=
    fun p =>
      (blockCoordinate1 (𝕜 := ℂ) (E0 := E0) (E1 := E1) p.1,
       blockCoordinate1 (𝕜 := ℂ) (E0 := E0) (E1 := E1) p.2)
  have hcoords : Continuous coords := by
    fun_prop
  rw [show Set.range (fun v : (coordinateRestriction1 D).domain =>
      ((v : E1), coordinateRestriction1 D v)) =
      coords ⁻¹' (Set.range fun x : D.domain =>
        (((x : D.domain) : DirectSumSpace (E0 := E0) (E1 := E1)), D x)) by
    ext p
    constructor
    · rintro ⟨v, rfl⟩
      refine ⟨coordinateRestrictionDomain1ToOriginal D v, ?_⟩
      apply Prod.ext
      · rfl
      · exact coordinateRestriction1_action_eq D hred v
    · rintro ⟨x, hx⟩
      have hfst :
          ((x : D.domain) : DirectSumSpace (E0 := E0) (E1 := E1)) =
            blockCoordinate1 (𝕜 := ℂ) (E0 := E0) (E1 := E1) p.1 :=
        congrArg Prod.fst hx
      have hsnd :
          D x = blockCoordinate1 (𝕜 := ℂ) (E0 := E0) (E1 := E1) p.2 :=
        congrArg Prod.snd hx
      have hp1 : p.1 ∈ coordinateRestrictionDomain1 D := by
        change blockCoordinate1 (𝕜 := ℂ) (E0 := E0) (E1 := E1) p.1 ∈ D.domain
        rw [← hfst]
        exact x.property
      let v : coordinateRestrictionDomain1 D := ⟨p.1, hp1⟩
      have hvx : coordinateRestrictionDomain1ToOriginal D v = x := by
        apply Subtype.ext
        exact hfst.symm
      refine ⟨v, Prod.ext rfl ?_⟩
      have hact := coordinateRestriction1_action_eq D hred v
      rw [hvx, hsnd] at hact
      have hcoord := congrArg WithLp.snd hact
      -- `simp` cannot bridge the two spellings of the restriction domain; `exact` checks the
      -- (definitional) equality directly.
      exact hcoord.symm]
  exact hclosed.preimage hcoords

/-- The explicit direct sum of the two coordinate restrictions. -/
noncomputable def reducedCoordinateDirectSum
    (D : DirectSumPMap (E0 := E0) (E1 := E1)) :
    DirectSumPMap (E0 := E0) (E1 := E1) :=
  TauCeti.LinearPMap.directSum (coordinateRestriction0 D) (coordinateRestriction1 D)

/-- Reassembling the two coordinate restrictions of a reducing operator recovers its domain. -/
@[simp] theorem mem_reducedCoordinateDirectSum_domain_iff
    (D : DirectSumPMap (E0 := E0) (E1 := E1))
    (hred : TauCeti.LinearPMap.ReducesSubspace D
      (unboundedBlockGraph (0 : E0 →L[ℂ] E1)))
    (z : DirectSumSpace (E0 := E0) (E1 := E1)) :
    z ∈ (reducedCoordinateDirectSum D).domain ↔ z ∈ D.domain := by
  change z ∈ (TauCeti.LinearPMap.directSum
      (coordinateRestriction0 D) (coordinateRestriction1 D)).domain ↔ z ∈ D.domain
  rw [TauCeti.LinearPMap.directSum_domain, TauCeti.LinearPMap.mem_directSumDomain_iff]
  change (WithLp.fst z ∈ coordinateRestrictionDomain0 D ∧
      WithLp.snd z ∈ coordinateRestrictionDomain1 D) ↔ z ∈ D.domain
  exact (mem_domain_iff_coordinateRestrictionDomains D hred z).symm

/-- The explicit coordinate direct sum has exactly the same action as the
original reduced map after transporting the common domain witness. -/
theorem reducedCoordinateDirectSum_action
    (D : DirectSumPMap (E0 := E0) (E1 := E1))
    (hred : TauCeti.LinearPMap.ReducesSubspace D
      (unboundedBlockGraph (0 : E0 →L[ℂ] E1)))
    (z : (reducedCoordinateDirectSum D).domain) :
    reducedCoordinateDirectSum D z =
      D ⟨(z : DirectSumSpace (E0 := E0) (E1 := E1)),
          (mem_reducedCoordinateDirectSum_domain_iff D hred z).mp z.property⟩ := by
  let A0 := coordinateRestriction0 D
  let A1 := coordinateRestriction1 D
  let u : coordinateRestrictionDomain0 D :=
    TauCeti.LinearPMap.directSumDomainFst A0 A1 z
  let v : coordinateRestrictionDomain1 D :=
    TauCeti.LinearPMap.directSumDomainSnd A0 A1 z
  let zD : D.domain :=
    ⟨(z : DirectSumSpace (E0 := E0) (E1 := E1)),
      (mem_reducedCoordinateDirectSum_domain_iff D hred z).mp z.property⟩
  have hzsplit : zD =
      coordinateRestrictionDomain0ToOriginal D u +
        coordinateRestrictionDomain1ToOriginal D v := by
    apply Subtype.ext
    exact (blockCoordinate0_add_blockCoordinate1 (𝕜 := ℂ)
      (z : DirectSumSpace (E0 := E0) (E1 := E1))).symm
  have hDsplit : D zD =
      blockCoordinate0 (𝕜 := ℂ) (E0 := E0) (E1 := E1)
          (coordinateRestrictionMap0 D u) +
        blockCoordinate1 (𝕜 := ℂ) (E0 := E0) (E1 := E1)
          (coordinateRestrictionMap1 D v) := by
    calc
      D zD = D (coordinateRestrictionDomain0ToOriginal D u +
            coordinateRestrictionDomain1ToOriginal D v) :=
        congrArg D.toFun hzsplit
      _ = D (coordinateRestrictionDomain0ToOriginal D u) +
          D (coordinateRestrictionDomain1ToOriginal D v) :=
        LinearPMap.map_add D _ _
      _ = _ := by
        rw [coordinateRestriction0_action_eq D hred u,
          coordinateRestriction1_action_eq D hred v]
  have hsum := blockCoordinate0_add_blockCoordinate1 (𝕜 := ℂ)
    (reducedCoordinateDirectSum D z)
  change blockCoordinate0 (𝕜 := ℂ) (E0 := E0) (E1 := E1)
      (coordinateRestrictionMap0 D u) +
    blockCoordinate1 (𝕜 := ℂ) (E0 := E0) (E1 := E1)
      (coordinateRestrictionMap1 D v) =
    reducedCoordinateDirectSum D z at hsum
  exact hsum.symm.trans hDsplit.symm

/-- The coordinate direct sum and the original reduced map are equivalent
through the identity, with both domain directions and actions explicit. -/
theorem reducedCoordinateDirectSum_unitaryEquivalent
    (D : DirectSumPMap (E0 := E0) (E1 := E1))
    (hred : TauCeti.LinearPMap.ReducesSubspace D
      (unboundedBlockGraph (0 : E0 →L[ℂ] E1))) :
    TauCeti.LinearPMap.UnitaryEquivalent
      (reducedCoordinateDirectSum D) D
      (ContinuousLinearMap.id ℂ _)
      (ContinuousLinearMap.id ℂ _) := by
  have hid : TauCeti.LinearPMap.IsUnitaryOperator
      (ContinuousLinearMap.id ℂ (DirectSumSpace (E0 := E0) (E1 := E1))) := by
    constructor
    · intro x
      rfl
    · intro y
      exact ⟨y, rfl⟩
  refine ⟨hid, hid, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · let hWdom : ∀ x : (reducedCoordinateDirectSum D).domain,
        (ContinuousLinearMap.id ℂ _) (x : DirectSumSpace (E0 := E0) (E1 := E1)) ∈
          D.domain := fun x =>
      (mem_reducedCoordinateDirectSum_domain_iff D hred x).mp x.property
    refine ⟨hWdom, ?_⟩
    let hWinvdom : ∀ y : D.domain,
        (ContinuousLinearMap.id ℂ _) (y : DirectSumSpace (E0 := E0) (E1 := E1)) ∈
          (reducedCoordinateDirectSum D).domain := fun y =>
      (mem_reducedCoordinateDirectSum_domain_iff D hred y).mpr y.property
    refine ⟨hWinvdom, ?_, ?_⟩
    · intro x
      change D ⟨(x : DirectSumSpace (E0 := E0) (E1 := E1)), hWdom x⟩ =
        reducedCoordinateDirectSum D x
      exact (reducedCoordinateDirectSum_action D hred x).symm
    · intro y
      change reducedCoordinateDirectSum D
          ⟨(y : DirectSumSpace (E0 := E0) (E1 := E1)), hWinvdom y⟩ = D y
      have h := reducedCoordinateDirectSum_action D hred
        ⟨(y : DirectSumSpace (E0 := E0) (E1 := E1)), hWinvdom y⟩
      simpa using h

/-- The first coordinate restriction of the graph-rotated unbounded block
core. -/
noncomputable def unboundedBlockDiagonalRestriction0
    (H : UnboundedBlockData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    (X : E0 →L[ℂ] E1) : E0 →ₗ.[ℂ] E0 :=
  coordinateRestriction0 (unboundedBlockDiagonalCore H X)

/-- The second coordinate restriction of the graph-rotated unbounded block
core. -/
noncomputable def unboundedBlockDiagonalRestriction1
    (H : UnboundedBlockData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    (X : E0 →L[ℂ] E1) : E1 →ₗ.[ℂ] E1 :=
  coordinateRestriction1 (unboundedBlockDiagonalCore H X)

/-- The graph-rotated block core is exactly represented, up to identity
transport of the common domain, by the direct sum of its two coordinate
restrictions. -/
theorem unboundedBlockDiagonalCore_coordinateDirectSum
    (H : UnboundedBlockData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    (X : E0 →L[ℂ] E1)
    (hred : TauCeti.LinearPMap.ReducesSubspace
      (unboundedBlockOperatorCore H) (unboundedBlockGraph X)) :
    TauCeti.LinearPMap.UnitaryEquivalent
      (TauCeti.LinearPMap.directSum
        (unboundedBlockDiagonalRestriction0 H X)
        (unboundedBlockDiagonalRestriction1 H X))
      (unboundedBlockDiagonalCore H X)
      (ContinuousLinearMap.id ℂ _)
      (ContinuousLinearMap.id ℂ _) :=
  reducedCoordinateDirectSum_unitaryEquivalent
    (unboundedBlockDiagonalCore H X)
    (unboundedBlockDiagonalCore_reduces_zeroGraph H X hred)

end DavisKahanExt
end TauCeti
