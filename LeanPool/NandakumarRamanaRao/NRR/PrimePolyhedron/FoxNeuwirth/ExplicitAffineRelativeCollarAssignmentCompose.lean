/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.ExplicitAffineRelativeCollarCompose
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.ExplicitAffineRelativeCollarStokes
/-!
# Assignment composition for endpoint-identified relative affine collars

The geometric composition of two collars is already available in
`ExplicitAffineRelativeCollarCompose`.  This file supplies the corresponding assignment layer.

An assignment is most conveniently built from an equivariant vector value on global vertices.
For a composed collar, the value on each half is inherited from the corresponding component.
The only additional hypothesis is literal agreement at every geometric seam vertex.  Under that
hypothesis the two local definitions descend through equality of combined geometric vertices.

The resulting combined assignment reconstructs the original component assignments on every local
cell.  Consequently any cellwise property stated only in terms of `localVertexMap`, in particular
origin avoidance, is transported without a new geometric proof.
-/

namespace NRR
namespace FoxNeuwirthOrderComplex
namespace EquivariantPrismStableRelativeBoundary
namespace ExplicitAffineRelativeCollarAssignmentCompose

open ExplicitAffineRelativeCollar
open ExplicitAffineRelativeCollar.Parameters
open ExplicitAffineRelativeCollar.Polynomials
open ExplicitAffineRelativeCollarCompose
open AffinePositiveRayBoundary
open AffinePositiveRayBoundary.VertexMap

variable {p N₀ Nmid N₁ M₀ M₁ L₀ L₁ : Nat}
variable {hp : Nat.Prime p}

/-- Construct a scalar quotient assignment from an equivariant vector value on global vertices. -/
noncomputable def assignmentOfEquivariantVector
    {A B M L : Nat}
    (C : RelativeAffineCellSystem hp A B M L)
    (V : GlobalVertex hp C → Fin p → Real)
    (hV : ∀ (g : PrimeSymmetry p) (x : GlobalVertex hp C),
      V (g • x) = g • V x) : Assignment hp C :=
  fun q => Quotient.liftOn q (fun s : ScalarSite hp C => V s.1 s.2) (by
    intro a b hab
    obtain ⟨g, rfl⟩ : ∃ g : PrimeSymmetry p, g • b = a := hab
    have h := congrFun (hV g b.1) (g • b.2)
    simpa [PrimeSymmetry.smul_coordinate_apply, PrimeSymmetry.smul_label] using h)

/-- The assignment reconstructed from an equivariant vector has the prescribed vector value. -/
@[simp] theorem vectorValue_assignmentOfEquivariantVector
    {A B M L : Nat}
    (C : RelativeAffineCellSystem hp A B M L)
    (V : GlobalVertex hp C → Fin p → Real)
    (hV : ∀ (g : PrimeSymmetry p) (x : GlobalVertex hp C),
      V (g • x) = g • V x)
    (x : GlobalVertex hp C) :
    vectorValue hp C (assignmentOfEquivariantVector C V hV) x = V x := by
  rfl

variable
    (C : RelativeAffineCellSystem hp N₀ Nmid M₀ L₀)
    (D : RelativeAffineCellSystem hp Nmid N₁ M₁ L₁)

/-- A local vertex occurrence from the left collar, embedded in the combined cover. -/
def leftCoverVertex
    (s : CoverVertexSlot hp C) :
    CoverVertexSlot hp (combinedCells C D) :=
  (s.1, (Sum.inl s.2.1, s.2.2))

/-- A local vertex occurrence from the right collar, embedded in the combined cover. -/
def rightCoverVertex
    (s : CoverVertexSlot hp D) :
    CoverVertexSlot hp (combinedCells C D) :=
  (s.1, (Sum.inr s.2.1, s.2.2))

@[simp] theorem coverPoint_leftCoverVertex
    (s : CoverVertexSlot hp C) :
    coverPoint hp (combinedCells C D) (leftCoverVertex C D s) =
      leftPoint (coverPoint hp C s) := by
  simp [leftCoverVertex, coverPoint, RelativeAffineCellSystem.slotPoint,
    combinedCells]

@[simp] theorem coverPoint_rightCoverVertex
    (s : CoverVertexSlot hp D) :
    coverPoint hp (combinedCells C D) (rightCoverVertex C D s) =
      rightPoint (coverPoint hp D s) := by
  simp [rightCoverVertex, coverPoint, RelativeAffineCellSystem.slotPoint,
    combinedCells]

/-- Seam compatibility for two vector assignments.  It is stated directly on geometric cover
occurrences so it applies before either component is embedded into the combined quotient. -/
def SeamCompatible
    (VC : GlobalVertex hp C → Fin p → Real)
    (VD : GlobalVertex hp D → Fin p → Real) : Prop :=
  ∀ (a : CoverVertexSlot hp C) (b : CoverVertexSlot hp D),
    leftPoint (coverPoint hp C a) = rightPoint (coverPoint hp D b) →
      VC (Quotient.mk _ a) = VD (Quotient.mk _ b)

/-- Piecewise vector value on decorated local occurrences of the combined collar. -/
noncomputable def combinedCoverVector
    (VC : GlobalVertex hp C → Fin p → Real)
    (VD : GlobalVertex hp D → Fin p → Real) :
    CoverVertexSlot hp (combinedCells C D) → Fin p → Real
  | (g, (Sum.inl q, i)) => VC (Quotient.mk _ (g, (q, i)))
  | (g, (Sum.inr q, i)) => VD (Quotient.mk _ (g, (q, i)))

/-- Component compatibility and seam compatibility make the piecewise vector depend only on the
combined geometric vertex. -/
theorem combinedCoverVector_eq_of_coverPoint_eq
    (VC : GlobalVertex hp C → Fin p → Real)
    (VD : GlobalVertex hp D → Fin p → Real)
    (hseam : SeamCompatible C D VC VD)
    {a b : CoverVertexSlot hp (combinedCells C D)}
    (hab : coverPoint hp (combinedCells C D) a =
      coverPoint hp (combinedCells C D) b) :
    combinedCoverVector C D VC VD a = combinedCoverVector C D VC VD b := by
  rcases a with ⟨ga, ⟨qa, ia⟩⟩
  rcases b with ⟨gb, ⟨qb, ib⟩⟩
  cases qa with
  | inl qa =>
      cases qb with
      | inl qb =>
          apply congrArg VC
          apply Quotient.sound
          apply leftPoint_injective
          change coverPoint hp (combinedCells C D)
              (leftCoverVertex C D (ga, (qa, ia))) =
            coverPoint hp (combinedCells C D)
              (leftCoverVertex C D (gb, (qb, ib))) at hab
          rw [coverPoint_leftCoverVertex, coverPoint_leftCoverVertex] at hab
          exact hab
      | inr qb =>
          apply hseam (ga, (qa, ia)) (gb, (qb, ib))
          change coverPoint hp (combinedCells C D)
              (leftCoverVertex C D (ga, (qa, ia))) =
            coverPoint hp (combinedCells C D)
              (rightCoverVertex C D (gb, (qb, ib))) at hab
          rw [coverPoint_leftCoverVertex, coverPoint_rightCoverVertex] at hab
          exact hab
  | inr qa =>
      cases qb with
      | inl qb =>
          apply (hseam (gb, (qb, ib)) (ga, (qa, ia)) ?_).symm
          change coverPoint hp (combinedCells C D)
              (rightCoverVertex C D (ga, (qa, ia))) =
            coverPoint hp (combinedCells C D)
              (leftCoverVertex C D (gb, (qb, ib))) at hab
          rw [coverPoint_rightCoverVertex, coverPoint_leftCoverVertex] at hab
          exact hab.symm
      | inr qb =>
          apply congrArg VD
          apply Quotient.sound
          apply rightPoint_injective
          change coverPoint hp (combinedCells C D)
              (rightCoverVertex C D (ga, (qa, ia))) =
            coverPoint hp (combinedCells C D)
              (rightCoverVertex C D (gb, (qb, ib))) at hab
          rw [coverPoint_rightCoverVertex, coverPoint_rightCoverVertex] at hab
          exact hab

/-- Global combined vector obtained by descent from the piecewise cover value. -/
noncomputable def combinedGlobalVector
    (VC : GlobalVertex hp C → Fin p → Real)
    (VD : GlobalVertex hp D → Fin p → Real)
    (hseam : SeamCompatible C D VC VD) :
    GlobalVertex hp (combinedCells C D) → Fin p → Real :=
  Quotient.lift (combinedCoverVector C D VC VD) (by
    intro a b hab
    exact combinedCoverVector_eq_of_coverPoint_eq C D VC VD hseam hab)

@[simp] theorem combinedGlobalVector_left
    (VC : GlobalVertex hp C → Fin p → Real)
    (VD : GlobalVertex hp D → Fin p → Real)
    (hseam : SeamCompatible C D VC VD)
    (s : CoverVertexSlot hp C) :
    combinedGlobalVector C D VC VD hseam
        (Quotient.mk _ (leftCoverVertex C D s)) =
      VC (Quotient.mk _ s) := by
  rfl

@[simp] theorem combinedGlobalVector_right
    (VC : GlobalVertex hp C → Fin p → Real)
    (VD : GlobalVertex hp D → Fin p → Real)
    (hseam : SeamCompatible C D VC VD)
    (s : CoverVertexSlot hp D) :
    combinedGlobalVector C D VC VD hseam
        (Quotient.mk _ (rightCoverVertex C D s)) =
      VD (Quotient.mk _ s) := by
  rfl

/-- Equivariance of both component vector values is inherited by the combined vector. -/
theorem combinedGlobalVector_smul
    (VC : GlobalVertex hp C → Fin p → Real)
    (VD : GlobalVertex hp D → Fin p → Real)
    (hC : ∀ (g : PrimeSymmetry p) (x : GlobalVertex hp C),
      VC (g • x) = g • VC x)
    (hD : ∀ (g : PrimeSymmetry p) (x : GlobalVertex hp D),
      VD (g • x) = g • VD x)
    (hseam : SeamCompatible C D VC VD)
    (g : PrimeSymmetry p)
    (x : GlobalVertex hp (combinedCells C D)) :
    combinedGlobalVector C D VC VD hseam (g • x) =
      g • combinedGlobalVector C D VC VD hseam x := by
  refine Quotient.inductionOn x ?_
  rintro ⟨h, ⟨q, i⟩⟩
  cases q with
  | inl q =>
      change VC (Quotient.mk _ (g * h, (q, i))) =
        g • VC (Quotient.mk _ (h, (q, i)))
      have hact :
          g • (Quotient.mk _ (h, (q, i)) : GlobalVertex hp C) =
            Quotient.mk _ (g * h, (q, i)) := by
        change Quotient.map (actCoverVertex hp C g) _ (Quotient.mk _ (h, (q, i))) = _
        rfl
      rw [← hact]
      exact hC g (Quotient.mk _ (h, (q, i)))
  | inr q =>
      change VD (Quotient.mk _ (g * h, (q, i))) =
        g • VD (Quotient.mk _ (h, (q, i)))
      have hact :
          g • (Quotient.mk _ (h, (q, i)) : GlobalVertex hp D) =
            Quotient.mk _ (g * h, (q, i)) := by
        change Quotient.map (actCoverVertex hp D g) _ (Quotient.mk _ (h, (q, i))) = _
        rfl
      rw [← hact]
      exact hD g (Quotient.mk _ (h, (q, i)))

/-- Compose two assignments whose vector values agree on every combined seam vertex. -/
noncomputable def combinedAssignment
    (a : Assignment hp C)
    (b : Assignment hp D)
    (hseam : SeamCompatible C D (vectorValue hp C a) (vectorValue hp D b)) :
    Assignment hp (combinedCells C D) :=
  assignmentOfEquivariantVector (combinedCells C D)
    (combinedGlobalVector C D (vectorValue hp C a) (vectorValue hp D b) hseam)
    (combinedGlobalVector_smul C D
      (vectorValue hp C a) (vectorValue hp D b)
      (vectorValue_smul hp C a) (vectorValue_smul hp D b) hseam)

/-- Local values on a left cell are reconstructed literally from the left assignment. -/
theorem localVertexMap_combinedAssignment_left
    (a : Assignment hp C)
    (b : Assignment hp D)
    (hseam : SeamCompatible C D (vectorValue hp C a) (vectorValue hp D b))
    (q : C.Cell) :
    localVertexMap hp (combinedCells C D) (combinedAssignment C D a b hseam) (Sum.inl q) =
      localVertexMap hp C a q := rfl

/-- Local values on a right cell are reconstructed literally from the right assignment. -/
theorem localVertexMap_combinedAssignment_right
    (a : Assignment hp C)
    (b : Assignment hp D)
    (hseam : SeamCompatible C D (vectorValue hp C a) (vectorValue hp D b))
    (q : D.Cell) :
    localVertexMap hp (combinedCells C D) (combinedAssignment C D a b hseam) (Sum.inr q) =
      localVertexMap hp D b q := rfl


/-- On a left local slot, the combined assignment reconstructs the left component vector. -/
@[simp] theorem vectorValue_combinedAssignment_left_sample
    (a : Assignment hp C)
    (b : Assignment hp D)
    (hseam : SeamCompatible C D (vectorValue hp C a) (vectorValue hp D b))
    (s : C.VertexSlot) :
    vectorValue hp (combinedCells C D) (combinedAssignment C D a b hseam)
        (sampleVertex hp (combinedCells C D) (Sum.inl s.1, s.2)) =
      vectorValue hp C a (sampleVertex hp C s) := by
  rfl

/-- On a right local slot, the combined assignment reconstructs the right component vector. -/
@[simp] theorem vectorValue_combinedAssignment_right_sample
    (a : Assignment hp C)
    (b : Assignment hp D)
    (hseam : SeamCompatible C D (vectorValue hp C a) (vectorValue hp D b))
    (s : D.VertexSlot) :
    vectorValue hp (combinedCells C D) (combinedAssignment C D a b hseam)
        (sampleVertex hp (combinedCells C D) (Sum.inr s.1, s.2)) =
      vectorValue hp D b (sampleVertex hp D s) := by
  rfl


/-- A lower-boundary value formula on the left component is preserved by composition. -/
theorem combinedAssignment_lowerFixed
    (a : Assignment hp C)
    (b : Assignment hp D)
    (hseam : SeamCompatible C D (vectorValue hp C a) (vectorValue hp D b))
    (G : Realization p → Fin p → Real)
    (hleft : ∀ s : C.VertexSlot,
      (C.slotPoint s).time.1 = 0 →
        vectorValue hp C a (sampleVertex hp C s) = G (C.slotPoint s).spatial) :
    ∀ s : (combinedCells C D).VertexSlot,
      ((combinedCells C D).slotPoint s).time.1 = 0 →
        vectorValue hp (combinedCells C D) (combinedAssignment C D a b hseam)
            (sampleVertex hp (combinedCells C D) s) =
          G ((combinedCells C D).slotPoint s).spatial := by
  rintro ⟨q, i⟩ htime
  cases q with
  | inl q =>
      have hcomponent : (C.vertex q i).time.1 = 0 := by
        change (C.vertex q i).time.1 / 2 = 0 at htime
        linarith
      change vectorValue hp C a (sampleVertex hp C (q, i)) =
        G (C.slotPoint (q, i)).spatial
      exact hleft (q, i) hcomponent
  | inr q =>
      have hnonneg := (D.vertex q i).time.2.1
      change (1 + (D.vertex q i).time.1) / 2 = 0 at htime
      exfalso
      linarith

/-- An upper-boundary value formula on the right component is preserved by composition. -/
theorem combinedAssignment_upperFixed
    (a : Assignment hp C)
    (b : Assignment hp D)
    (hseam : SeamCompatible C D (vectorValue hp C a) (vectorValue hp D b))
    (G : Realization p → Fin p → Real)
    (hright : ∀ s : D.VertexSlot,
      (D.slotPoint s).time.1 = 1 →
        vectorValue hp D b (sampleVertex hp D s) = G (D.slotPoint s).spatial) :
    ∀ s : (combinedCells C D).VertexSlot,
      ((combinedCells C D).slotPoint s).time.1 = 1 →
        vectorValue hp (combinedCells C D) (combinedAssignment C D a b hseam)
            (sampleVertex hp (combinedCells C D) s) =
          G ((combinedCells C D).slotPoint s).spatial := by
  rintro ⟨q, i⟩ htime
  cases q with
  | inl q =>
      have hle := (C.vertex q i).time.2.2
      change (C.vertex q i).time.1 / 2 = 1 at htime
      exfalso
      linarith
  | inr q =>
      have hcomponent : (D.vertex q i).time.1 = 1 := by
        change (1 + (D.vertex q i).time.1) / 2 = 1 at htime
        linarith
      change vectorValue hp D b (sampleVertex hp D (q, i)) =
        G (D.slotPoint (q, i)).spatial
      exact hright (q, i) hcomponent

/-- Composition preserves the external horizontal endpoint values.  Only the lower values of the
left assignment and the upper values of the right assignment are needed; the common seam is
handled separately by `SeamCompatible`. -/
theorem combinedAssignment_horizontalVertexFixed
    {F₀ F₁ : RefinedAffineMap.ContinuousCoordinateMap p}
    (A₀ : RefinedAffineMap.StableRegularApproximation hp F₀)
    (A₁ : RefinedAffineMap.StableRegularApproximation hp F₁)
    (EC : EndpointIdentifiedRelativeAffineCollar hp
      A₀.toRegularApproximation.level Nmid M₀ L₀)
    (ED : EndpointIdentifiedRelativeAffineCollar hp
      Nmid A₁.toRegularApproximation.level M₁ L₁)
    (a : Assignment hp EC.cells)
    (b : Assignment hp ED.cells)
    (hseam : SeamCompatible EC.cells ED.cells
      (vectorValue hp EC.cells a) (vectorValue hp ED.cells b))
    (hlower : ∀ s : EC.cells.VertexSlot,
      (EC.cells.slotPoint s).time.1 = 0 →
        vectorValue hp EC.cells a (sampleVertex hp EC.cells s) =
          A₀.toRegularApproximation.map (EC.cells.slotPoint s).spatial)
    (hupper : ∀ s : ED.cells.VertexSlot,
      (ED.cells.slotPoint s).time.1 = 1 →
        vectorValue hp ED.cells b (sampleVertex hp ED.cells s) =
          A₁.toRegularApproximation.map (ED.cells.slotPoint s).spatial) :
    HorizontalVertexFixed hp A₀ A₁ (endpointIdentifiedCollar EC ED)
      (combinedAssignment EC.cells ED.cells a b hseam) := by
  constructor
  · rintro ⟨q, i⟩ htime
    cases q with
    | inl q =>
        have hcomponent : (EC.cells.vertex q i).time.1 = 0 := by
          change (EC.cells.vertex q i).time.1 / 2 = 0 at htime
          linarith
        change vectorValue hp EC.cells a (sampleVertex hp EC.cells (q, i)) =
          A₀.toRegularApproximation.map (EC.cells.slotPoint (q, i)).spatial
        exact hlower (q, i) hcomponent
    | inr q =>
        have hnonneg := (ED.cells.vertex q i).time.2.1
        change (1 + (ED.cells.vertex q i).time.1) / 2 = 0 at htime
        exfalso
        linarith
  · rintro ⟨q, i⟩ htime
    cases q with
    | inl q =>
        have hle := (EC.cells.vertex q i).time.2.2
        change (EC.cells.vertex q i).time.1 / 2 = 1 at htime
        exfalso
        linarith
    | inr q =>
        have hcomponent : (ED.cells.vertex q i).time.1 = 1 := by
          change (1 + (ED.cells.vertex q i).time.1) / 2 = 1 at htime
          linarith
        change vectorValue hp ED.cells b (sampleVertex hp ED.cells (q, i)) =
          A₁.toRegularApproximation.map (ED.cells.slotPoint (q, i)).spatial
        exact hupper (q, i) hcomponent

/-- Cellwise origin avoidance is preserved under assignment composition. -/
theorem combinedAssignment_avoidsOrigin
    (a : Assignment hp C)
    (b : Assignment hp D)
    (hseam : SeamCompatible C D (vectorValue hp C a) (vectorValue hp D b))
    (hC : ∀ q : C.Cell, AvoidsOrigin (localVertexMap hp C a q))
    (hD : ∀ q : D.Cell, AvoidsOrigin (localVertexMap hp D b q)) :
    ∀ q : (combinedCells C D).Cell,
      AvoidsOrigin
        (localVertexMap hp (combinedCells C D) (combinedAssignment C D a b hseam) q) := by
  intro q
  cases q with
  | inl q => simpa [localVertexMap_combinedAssignment_left] using hC q
  | inr q => simpa [localVertexMap_combinedAssignment_right] using hD q

end ExplicitAffineRelativeCollarAssignmentCompose
end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR
