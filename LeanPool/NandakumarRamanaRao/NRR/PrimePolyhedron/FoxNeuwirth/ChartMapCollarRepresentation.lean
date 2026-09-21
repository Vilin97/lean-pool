/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.CompatibleRefinedChartHomotopyPrism
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.ExplicitAffineRelativeCollarAssignmentReverse
/-!
# Chart-map representations of relative-collar assignments

A collar assignment represents a compatible chart map when every decorated local vertex value is
the chart-map value at the represented spatial point.  This invariant is independent of the time
coordinate.  It therefore passes through collar composition and interval reversal, and two
assignments representing the same chart map agree automatically on a composition seam.
-/

namespace NRR
namespace FoxNeuwirthOrderComplex
namespace EquivariantPrismStableRelativeBoundary
namespace ChartMapCollarRepresentation

open RefinedAffineMap
open ExplicitAffineRelativeCollar
open ExplicitAffineRelativeCollar.Parameters
open ExplicitAffineRelativeCollarCompose
open ExplicitAffineRelativeCollarReverse
open ExplicitAffineRelativeCollarAssignmentCompose
open ExplicitAffineRelativeCollarAssignmentReverse
open CompatibleRefinedChartHomotopy

variable {p N A B M L : Nat}
variable {hp : Nat.Prime p}

/-- Every decorated local occurrence is evaluated through one chart of `K` at the represented
spatial point. -/
def Represents
    (C : RelativeAffineCellSystem hp A B M L)
    (K : ChartMap hp N)
    (V : GlobalVertex hp C → Fin p → Real) : Prop :=
  ∀ s : CoverVertexSlot hp C,
    ∃ (q : TopCell hp N) (w : StandardSimplex (p - 1)),
      (coverPoint hp C s).spatial =
          s.1 • RefinedAffineMap.chart hp N q (StandardSimplex.toDelta w) ∧
      V (Quotient.mk _ s) = s.1 • K.value q w


/-- Boundary-restricted version of `Represents`. -/
def RepresentsAtTime
    (C : RelativeAffineCellSystem hp A B M L)
    (K : ChartMap hp N)
    (V : GlobalVertex hp C → Fin p → Real)
    (t : Real) : Prop :=
  ∀ s : CoverVertexSlot hp C,
    (coverPoint hp C s).time.1 = t →
      ∃ (q : TopCell hp N) (w : StandardSimplex (p - 1)),
        (coverPoint hp C s).spatial =
            s.1 • RefinedAffineMap.chart hp N q (StandardSimplex.toDelta w) ∧
        V (Quotient.mk _ s) = s.1 • K.value q w

/-- An unrestricted representation restricts to either horizontal boundary. -/
theorem Represents.atTime
    {C : RelativeAffineCellSystem hp A B M L}
    {K : ChartMap hp N}
    {V : GlobalVertex hp C → Fin p → Real}
    (h : Represents C K V) (t : Real) :
    RepresentsAtTime C K V t := by
  intro s hs
  exact h s

/-- Two represented assignments for the same chart map agree whenever their geometric spatial
points agree. -/
theorem value_eq_of_spatial_eq
    {A₀ B₀ M₀ L₀ A₁ B₁ M₁ L₁ : Nat}
    (C : RelativeAffineCellSystem hp A₀ B₀ M₀ L₀)
    (D : RelativeAffineCellSystem hp A₁ B₁ M₁ L₁)
    (K : ChartMap hp N)
    (VC : GlobalVertex hp C → Fin p → Real)
    (VD : GlobalVertex hp D → Fin p → Real)
    (hC : Represents C K VC) (hD : Represents D K VD)
    (a : CoverVertexSlot hp C) (b : CoverVertexSlot hp D)
    (hab : (coverPoint hp C a).spatial = (coverPoint hp D b).spatial) :
    VC (Quotient.mk _ a) = VD (Quotient.mk _ b) := by
  obtain ⟨qa, wa, hpa, hva⟩ := hC a
  obtain ⟨qb, wb, hpb, hvb⟩ := hD b
  rw [hva, hvb]
  apply K.decorated_compatible a.1 b.1 qa qb wa wb
  rw [← hpa, ← hpb]
  exact hab

/-- Representation by one chart map supplies the seam condition required by collar composition. -/
theorem seamCompatible
    {A₀ B₀ M₀ L₀ B₁ M₁ L₁ : Nat}
    (C : RelativeAffineCellSystem hp A₀ B₀ M₀ L₀)
    (D : RelativeAffineCellSystem hp B₀ B₁ M₁ L₁)
    (K : ChartMap hp N)
    (VC : GlobalVertex hp C → Fin p → Real)
    (VD : GlobalVertex hp D → Fin p → Real)
    (hC : Represents C K VC) (hD : Represents D K VD) :
    SeamCompatible C D VC VD := by
  intro a b hab
  apply value_eq_of_spatial_eq C D K VC VD hC hD a b
  have h := congrArg EquivariantPrismVertexParameters.CylinderPoint.spatial hab
  simpa [leftPoint, rightPoint] using h


/-- Upper and lower boundary representations by the same chart map supply a composition seam. -/
theorem seamCompatible_of_boundary
    {A₀ B₀ M₀ L₀ B₁ M₁ L₁ : Nat}
    (C : RelativeAffineCellSystem hp A₀ B₀ M₀ L₀)
    (D : RelativeAffineCellSystem hp B₀ B₁ M₁ L₁)
    (K : ChartMap hp N)
    (VC : GlobalVertex hp C → Fin p → Real)
    (VD : GlobalVertex hp D → Fin p → Real)
    (hC : RepresentsAtTime C K VC 1)
    (hD : RepresentsAtTime D K VD 0) :
    SeamCompatible C D VC VD := by
  intro a b hab
  have hta : (coverPoint hp C a).time.1 = 1 := by
    have h := congrArg (fun z : EquivariantPrismVertexParameters.CylinderPoint p => z.time.1) hab
    have hb0 := (coverPoint hp D b).time.2.1
    change (coverPoint hp C a).time.1 / 2 =
      (1 + (coverPoint hp D b).time.1) / 2 at h
    have hale := (coverPoint hp C a).time.2.2
    linarith
  have htb : (coverPoint hp D b).time.1 = 0 := by
    have h := congrArg (fun z : EquivariantPrismVertexParameters.CylinderPoint p => z.time.1) hab
    have ha1 := (coverPoint hp C a).time.2.2
    change (coverPoint hp C a).time.1 / 2 =
      (1 + (coverPoint hp D b).time.1) / 2 at h
    have hb0 := (coverPoint hp D b).time.2.1
    linarith
  obtain ⟨qa, wa, hpa, hva⟩ := hC a hta
  obtain ⟨qb, wb, hpb, hvb⟩ := hD b htb
  rw [hva, hvb]
  apply K.decorated_compatible a.1 b.1 qa qb wa wb
  have hsp := congrArg EquivariantPrismVertexParameters.CylinderPoint.spatial hab
  rw [← hpa, ← hpb]
  simpa [leftPoint, rightPoint] using hsp

/-- Composition of represented vector assignments represents the same chart map. -/
theorem combinedGlobalVector_represents
    {N₀ Nmid N₁ M₀ M₁ L₀ L₁ : Nat}
    (C : RelativeAffineCellSystem hp N₀ Nmid M₀ L₀)
    (D : RelativeAffineCellSystem hp Nmid N₁ M₁ L₁)
    (K : ChartMap hp N)
    (VC : GlobalVertex hp C → Fin p → Real)
    (VD : GlobalVertex hp D → Fin p → Real)
    (hC : Represents C K VC) (hD : Represents D K VD) :
    Represents (combinedCells C D) K
      (combinedGlobalVector C D VC VD
        (seamCompatible C D K VC VD hC hD)) := by
  rintro ⟨g, ⟨q, i⟩⟩
  cases q with
  | inl q =>
      obtain ⟨r, w, hpnt, hval⟩ := hC (g, (q, i))
      refine ⟨r, w, ?_, ?_⟩
      · change (coverPoint hp C (g, (q, i))).spatial = _
        exact hpnt
      · change VC (Quotient.mk _ (g, (q, i))) = _
        exact hval
  | inr q =>
      obtain ⟨r, w, hpnt, hval⟩ := hD (g, (q, i))
      refine ⟨r, w, ?_, ?_⟩
      · change (coverPoint hp D (g, (q, i))).spatial = _
        exact hpnt
      · change VD (Quotient.mk _ (g, (q, i))) = _
        exact hval

/-- The combined assignment of two represented assignments again represents the same chart map. -/
theorem combinedAssignment_represents
    {N₀ Nmid N₁ M₀ M₁ L₀ L₁ : Nat}
    (C : RelativeAffineCellSystem hp N₀ Nmid M₀ L₀)
    (D : RelativeAffineCellSystem hp Nmid N₁ M₁ L₁)
    (K : ChartMap hp N)
    (a : Assignment hp C) (b : Assignment hp D)
    (ha : Represents C K (vectorValue hp C a))
    (hb : Represents D K (vectorValue hp D b)) :
    Represents (combinedCells C D) K
      (vectorValue hp (combinedCells C D)
        (combinedAssignment C D a b
          (seamCompatible C D K (vectorValue hp C a) (vectorValue hp D b) ha hb))) := by
  change Represents (combinedCells C D) K
    (combinedGlobalVector C D (vectorValue hp C a) (vectorValue hp D b)
      (seamCompatible C D K (vectorValue hp C a) (vectorValue hp D b) ha hb))
  exact combinedGlobalVector_represents C D K
    (vectorValue hp C a) (vectorValue hp D b) ha hb


/-- The upper boundary of a composed assignment is represented by the right component's upper
boundary representation. -/
theorem combinedAssignment_upper_represents_right
    {N₀ Nmid N₁ M₀ M₁ L₀ L₁ : Nat}
    (C : RelativeAffineCellSystem hp N₀ Nmid M₀ L₀)
    (D : RelativeAffineCellSystem hp Nmid N₁ M₁ L₁)
    (K : ChartMap hp N)
    (a : Assignment hp C) (b : Assignment hp D)
    (hseam : SeamCompatible C D (vectorValue hp C a) (vectorValue hp D b))
    (hb : RepresentsAtTime D K (vectorValue hp D b) 1) :
    RepresentsAtTime (combinedCells C D) K
      (vectorValue hp (combinedCells C D)
        (combinedAssignment C D a b hseam)) 1 := by
  rintro ⟨g, ⟨q, i⟩⟩ htime
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
      obtain ⟨r, w, hpnt, hval⟩ := hb (g, (q, i)) hcomponent
      refine ⟨r, w, ?_, ?_⟩
      · change (coverPoint hp D (g, (q, i))).spatial = _
        exact hpnt
      · change vectorValue hp D b (Quotient.mk _ (g, (q, i))) = _
        exact hval

/-- The lower boundary of a composed assignment is represented by the left component's lower
boundary representation. -/
theorem combinedAssignment_lower_represents_left
    {N₀ Nmid N₁ M₀ M₁ L₀ L₁ : Nat}
    (C : RelativeAffineCellSystem hp N₀ Nmid M₀ L₀)
    (D : RelativeAffineCellSystem hp Nmid N₁ M₁ L₁)
    (K : ChartMap hp N)
    (a : Assignment hp C) (b : Assignment hp D)
    (hseam : SeamCompatible C D (vectorValue hp C a) (vectorValue hp D b))
    (ha : RepresentsAtTime C K (vectorValue hp C a) 0) :
    RepresentsAtTime (combinedCells C D) K
      (vectorValue hp (combinedCells C D)
        (combinedAssignment C D a b hseam)) 0 := by
  rintro ⟨g, ⟨q, i⟩⟩ htime
  cases q with
  | inl q =>
      have hcomponent : (C.vertex q i).time.1 = 0 := by
        change (C.vertex q i).time.1 / 2 = 0 at htime
        linarith
      obtain ⟨r, w, hpnt, hval⟩ := ha (g, (q, i)) hcomponent
      refine ⟨r, w, ?_, ?_⟩
      · change (coverPoint hp C (g, (q, i))).spatial = _
        exact hpnt
      · change vectorValue hp C a (Quotient.mk _ (g, (q, i))) = _
        exact hval
  | inr q =>
      have hnonneg := (D.vertex q i).time.2.1
      change (1 + (D.vertex q i).time.1) / 2 = 0 at htime
      exfalso
      linarith

/-- Reversal preserves representation because reflection fixes the spatial coordinate. -/
theorem reverseGlobalVector_represents
    (C : RelativeAffineCellSystem hp A B M L)
    (K : ChartMap hp N) (a : Assignment hp C)
    (ha : Represents C K (vectorValue hp C a)) :
    Represents (reverseCells C) K (reverseGlobalVector C a) := by
  rintro ⟨g, ⟨r, i⟩⟩
  obtain ⟨q, w, hpnt, hval⟩ := ha (g, (r, i))
  refine ⟨q, w, ?_, ?_⟩
  · change (coverPoint hp C (g, (r, i))).spatial = _
    exact hpnt
  · change vectorValue hp C a (Quotient.mk _ (g, (r, i))) = _
    exact hval

/-- Reversed assignments represent the same chart map. -/
theorem reverseAssignment_represents
    (C : RelativeAffineCellSystem hp A B M L)
    (K : ChartMap hp N) (a : Assignment hp C)
    (ha : Represents C K (vectorValue hp C a)) :
    Represents (reverseCells C) K
      (vectorValue hp (reverseCells C) (reverseAssignment C a)) := by
  change Represents (reverseCells C) K (reverseGlobalVector C a)
  exact reverseGlobalVector_represents C K a ha

open SphereOddDegree
open SphereOddDegree.AffineBarycentricSubdivision
open SubdivisionPrismCharts
open CompatibleRefinedChartHomotopyPrism

/-- When the lower endpoint of a chart homotopy is a refinement of a base chart map, the complete
lower prism boundary represents that base map. -/
theorem lower_boundary_represents_base
    (hp : Nat.Prime p) {N0 d : Nat}
    (K : ChartMap hp N0) {K1 : ChartMap hp (N0 + d)}
    (J : ChartHomotopy hp (N0 + d) (K.refine d) K1)
    (L : Nat) :
    RepresentsAtTime
      (RelativeCollarMiddlePrism.cellSystem hp (N0 + d) L) K
      (vectorValue hp (RelativeCollarMiddlePrism.cellSystem hp (N0 + d) L)
        (CompatibleRefinedChartHomotopyPrism.assignment hp J L)) 0 := by
  intro s hs
  let w : StandardSimplex (p - 1) :=
    (staircasePoint hp s.2.1.1.2
      (StandardSimplex.ofDelta
        (affineCompMap p L s.2.1.2
          (stdSimplex.vertex (S := Real) s.2.2)))).1
  let q0 : TopCell hp N0 := ancestorTopCell hp N0 d s.2.1.1.1
  let w0 : StandardSimplex (p - 1) := ancestorWeight N0 d s.2.1.1.1 w
  refine ⟨q0, w0, ?_, ?_⟩
  · simp [q0, w0, w, coverPoint, RelativeAffineCellSystem.slotPoint,
      RelativeCollarMiddlePrism.cellSystem, RelativeCollarMiddlePrism.vertex,
      SubdivisionPrismCharts.vertex,
      SubdivisionPrismCharts.chart, EquivariantPrismVertexParameters.CylinderPoint.ofProd,
      chart_eq_ancestor]
  · have hlocal := CompatibleRefinedChartHomotopyPrism.lower_boundary_value hp J L s.2 (by
      simpa [coverPoint, RelativeAffineCellSystem.slotPoint] using hs)
    have hlocal' :
        CompatibleRefinedChartHomotopyPrism.localVector hp J L s.2 =
          (K.refine d).value s.2.1.1.1 w := hlocal
    change s.1 • _ = s.1 • K.value q0 w0
    rw [hlocal']
    rfl

/-- When the upper endpoint is a refinement of a base chart map, the complete upper prism
boundary represents that base map. -/
theorem upper_boundary_represents_base
    (hp : Nat.Prime p) {N0 d : Nat}
    (K : ChartMap hp N0) {K0 : ChartMap hp (N0 + d)}
    (J : ChartHomotopy hp (N0 + d) K0 (K.refine d))
    (L : Nat) :
    RepresentsAtTime
      (RelativeCollarMiddlePrism.cellSystem hp (N0 + d) L) K
      (vectorValue hp (RelativeCollarMiddlePrism.cellSystem hp (N0 + d) L)
        (CompatibleRefinedChartHomotopyPrism.assignment hp J L)) 1 := by
  intro s hs
  let w : StandardSimplex (p - 1) :=
    (staircasePoint hp s.2.1.1.2
      (StandardSimplex.ofDelta
        (affineCompMap p L s.2.1.2
          (stdSimplex.vertex (S := Real) s.2.2)))).1
  let q0 : TopCell hp N0 := ancestorTopCell hp N0 d s.2.1.1.1
  let w0 : StandardSimplex (p - 1) := ancestorWeight N0 d s.2.1.1.1 w
  refine ⟨q0, w0, ?_, ?_⟩
  · simp [q0, w0, w, coverPoint, RelativeAffineCellSystem.slotPoint,
      RelativeCollarMiddlePrism.cellSystem, RelativeCollarMiddlePrism.vertex,
      SubdivisionPrismCharts.vertex,
      SubdivisionPrismCharts.chart, EquivariantPrismVertexParameters.CylinderPoint.ofProd,
      chart_eq_ancestor]
  · have hlocal := CompatibleRefinedChartHomotopyPrism.upper_boundary_value hp J L s.2 (by
      simpa [coverPoint, RelativeAffineCellSystem.slotPoint] using hs)
    have hlocal' :
        CompatibleRefinedChartHomotopyPrism.localVector hp J L s.2 =
          (K.refine d).value s.2.1.1.1 w := hlocal
    change s.1 • _ = s.1 • K.value q0 w0
    rw [hlocal']
    rfl


end ChartMapCollarRepresentation
end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR
