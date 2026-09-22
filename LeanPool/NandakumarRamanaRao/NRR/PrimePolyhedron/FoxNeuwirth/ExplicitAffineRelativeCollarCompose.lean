/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.FiniteSimplex
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.ExplicitAffineRelativeCollarReverse
/-!
# Composition of endpoint-identified relative affine collars

Two collars with a common intermediate endpoint are placed in the lower and upper half of the
realization cylinder.  Their cell families are joined by disjoint union.  The quotient-facet
relation then identifies the two copies of every intermediate endpoint facet.  The upper boundary
pairing of the first collar and lower boundary pairing of the second collar are the same refined
Fox--Neuwirth chain, hence cancel pointwise after regrouping by combined quotient facets.
-/

namespace NRR
namespace FoxNeuwirthOrderComplex
namespace EquivariantPrismStableRelativeBoundary
namespace ExplicitAffineRelativeCollarCompose

open scoped BigOperators
open ExplicitAffineRelativeCollar
open EquivariantPrismVertexParameters
open RefinedAffineMap

variable {p N₀ Nmid N₁ M₀ M₁ L₀ L₁ : Nat}
variable {hp : Nat.Prime p}

/-- Two cylinder points agree when their spatial and interval coordinates agree. -/
theorem cylinderPoint_ext {z w : CylinderPoint p}
    (hs : z.spatial = w.spatial) (ht : (z.time : Real) = (w.time : Real)) : z = w := by
  obtain ⟨zs, zt⟩ := z
  obtain ⟨ws, wt⟩ := w
  simp only at hs ht
  subst hs
  simp only [CylinderPoint.mk.injEq, true_and]
  exact Subtype.ext ht

/-- Place a cylinder point in the lower half-cylinder. -/
noncomputable def leftPoint (z : CylinderPoint p) : CylinderPoint p :=
  ⟨z.spatial, ⟨z.time.1 / 2, by constructor <;> linarith [z.time.2.1, z.time.2.2]⟩⟩

/-- Place a cylinder point in the upper half-cylinder. -/
noncomputable def rightPoint (z : CylinderPoint p) : CylinderPoint p :=
  ⟨z.spatial, ⟨(1 + z.time.1) / 2, by constructor <;> linarith [z.time.2.1, z.time.2.2]⟩⟩

@[simp] theorem leftPoint_spatial (z : CylinderPoint p) :
    (leftPoint z).spatial = z.spatial := rfl

@[simp] theorem rightPoint_spatial (z : CylinderPoint p) :
    (rightPoint z).spatial = z.spatial := rfl

@[simp] theorem leftPoint_time (z : CylinderPoint p) :
    (leftPoint z).time.1 = z.time.1 / 2 := rfl

@[simp] theorem rightPoint_time (z : CylinderPoint p) :
    (rightPoint z).time.1 = (1 + z.time.1) / 2 := rfl

@[simp] theorem leftPoint_smul (g : PrimeSymmetry p) (z : CylinderPoint p) :
    leftPoint (g • z) = g • leftPoint z := rfl

@[simp] theorem rightPoint_smul (g : PrimeSymmetry p) (z : CylinderPoint p) :
    rightPoint (g • z) = g • rightPoint z := rfl

/-- Both half-cylinder embeddings are injective. -/
theorem leftPoint_injective : Function.Injective (@leftPoint p) := by
  intro x y h
  refine cylinderPoint_ext ?_ ?_
  · have hspatial := congrArg CylinderPoint.spatial h
    exact hspatial
  · have ht := congrArg (fun z : CylinderPoint p => z.time.1) h
    simp only [leftPoint_time] at ht
    linarith

/-- Both half-cylinder embeddings are injective. -/
theorem rightPoint_injective : Function.Injective (@rightPoint p) := by
  intro x y h
  refine cylinderPoint_ext ?_ ?_
  · have hspatial := congrArg CylinderPoint.spatial h
    exact hspatial
  · have ht := congrArg (fun z : CylinderPoint p => z.time.1) h
    simp only [rightPoint_time] at ht
    linarith

/-- Common interface point at time `1/2`. -/
noncomputable def middlePoint (x : Realization p) : CylinderPoint p :=
  ⟨x, ⟨1 / 2, by norm_num⟩⟩

@[simp] theorem left_upper_eq_middle (x : Realization p) :
    leftPoint (upperCylinderPoint x) = middlePoint x := by
  refine cylinderPoint_ext rfl ?_
  simp [leftPoint, upperCylinderPoint, middlePoint]

@[simp] theorem right_lower_eq_middle (x : Realization p) :
    rightPoint (lowerCylinderPoint x) = middlePoint x := by
  refine cylinderPoint_ext rfl ?_
  simp [rightPoint, lowerCylinderPoint, middlePoint]

@[simp] theorem left_lower_eq_lower (x : Realization p) :
    leftPoint (lowerCylinderPoint x) = lowerCylinderPoint x := by
  refine cylinderPoint_ext rfl ?_
  simp [leftPoint, lowerCylinderPoint]

@[simp] theorem right_upper_eq_upper (x : Realization p) :
    rightPoint (upperCylinderPoint x) = upperCylinderPoint x := by
  refine cylinderPoint_ext rfl ?_
  simp [rightPoint, upperCylinderPoint]

/-- Combined affine cell system. -/
noncomputable def combinedCells
    (C : RelativeAffineCellSystem hp N₀ Nmid M₀ L₀)
    (D : RelativeAffineCellSystem hp Nmid N₁ M₁ L₁) :
    RelativeAffineCellSystem hp N₀ N₁ (max M₀ M₁) (L₀ + L₁ + 1) where
  lower_le_common := le_trans C.lower_le_common (Nat.le_max_left _ _)
  upper_le_common := le_trans D.upper_le_common (Nat.le_max_right _ _)
  Cell := C.Cell ⊕ D.Cell
  cell_nonempty := C.cell_nonempty.map Sum.inl
  instCellFintype := inferInstance
  instCellDecidableEq := inferInstance
  coefficient
    | Sum.inl q => C.coefficient q
    | Sum.inr q => D.coefficient q
  vertex q i := match q with
    | Sum.inl r => leftPoint (C.vertex r i)
    | Sum.inr r => rightPoint (D.vertex r i)
  chart q w := match q with
    | Sum.inl r => leftPoint (C.chart r w)
    | Sum.inr r => rightPoint (D.chart r w)
  chart_vertex := by
    intro q i
    cases q with
    | inl q => simp [C.chart_vertex]
    | inr q => simp [D.chart_vertex]
  chart_spatial_affine := by
    intro q w c
    cases q with
    | inl q => simpa using C.chart_spatial_affine q w c
    | inr q => simpa using D.chart_spatial_affine q w c
  chart_time_affine := by
    intro q w
    cases q with
    | inl q =>
        change ((leftPoint (C.chart q w)).time : Real) =
          ∑ i : Fin (p + 1), w i * ((leftPoint (C.vertex q i)).time : Real)
        simp only [leftPoint_time]
        rw [C.chart_time_affine, Finset.sum_div]
        exact Finset.sum_congr rfl (fun i _ => by ring)
    | inr q =>
        change ((rightPoint (D.chart q w)).time : Real) =
          ∑ i : Fin (p + 1), w i * ((rightPoint (D.vertex q i)).time : Real)
        simp only [rightPoint_time]
        rw [D.chart_time_affine]
        have hw : ∑ i : Fin (p + 1), w i * ((1 + (D.vertex q i).time.1) / 2) =
            ((∑ i : Fin (p + 1), (w : Fin (p + 1) → Real) i) +
              ∑ i : Fin (p + 1), w i * (D.vertex q i).time.1) / 2 := by
          rw [← Finset.sum_add_distrib, Finset.sum_div]
          exact Finset.sum_congr rfl (fun i _ => by ring)
        rw [hw, SphereOddDegree.FiniteSimplex.sum_eq_one]
  chart_injective := by
    intro q
    cases q with
    | inl q =>
        intro x y h
        exact C.chart_injective q (leftPoint_injective h)
    | inr q =>
        intro x y h
        exact D.chart_injective q (rightPoint_injective h)
  vertex_injective := by
    intro q
    cases q with
    | inl q =>
        intro i j h
        exact C.vertex_injective q (leftPoint_injective h)
    | inr q =>
        intro i j h
        exact D.vertex_injective q (rightPoint_injective h)
  vertex_orbit_injective := by
    intro q g i j h
    cases q with
    | inl q =>
        apply C.vertex_orbit_injective q g i j
        apply leftPoint_injective
        simpa using h
    | inr q =>
        apply D.vertex_orbit_injective q g i j
        apply rightPoint_injective
        simpa using h

namespace Combined

variable
    (C : RelativeAffineCellSystem hp N₀ Nmid M₀ L₀)
    (D : RelativeAffineCellSystem hp Nmid N₁ M₁ L₁)

/-- Embed a left local facet occurrence into the combined cell family. -/
def leftOccurrence (o : C.FacetOccurrence) : (combinedCells C D).FacetOccurrence :=
  (Sum.inl o.1, o.2)

/-- Embed a right local facet occurrence into the combined cell family. -/
def rightOccurrence (o : D.FacetOccurrence) : (combinedCells C D).FacetOccurrence :=
  (Sum.inr o.1, o.2)

@[simp] theorem left_facetSignature (o : C.FacetOccurrence) :
    (combinedCells C D).facetSignature (leftOccurrence C D o) =
      fun i => leftPoint (C.facetSignature o i) := rfl

@[simp] theorem right_facetSignature (o : D.FacetOccurrence) :
    (combinedCells C D).facetSignature (rightOccurrence C D o) =
      fun i => rightPoint (D.facetSignature o i) := rfl

/-- Push a left quotient facet into the combined quotient. -/
noncomputable def leftFacet (s : C.Facet) : (combinedCells C D).Facet :=
  Quotient.map (leftOccurrence C D) (by
    intro a b hab
    rcases hab with ⟨g, hg⟩
    exact ⟨g, by funext i; simpa using congrArg leftPoint (congrFun hg i)⟩) s

/-- Push a right quotient facet into the combined quotient. -/
noncomputable def rightFacet (s : D.Facet) : (combinedCells C D).Facet :=
  Quotient.map (rightOccurrence C D) (by
    intro a b hab
    rcases hab with ⟨g, hg⟩
    exact ⟨g, by funext i; simpa using congrArg rightPoint (congrFun hg i)⟩) s

@[simp] theorem leftFacet_facetClass (o : C.FacetOccurrence) :
    leftFacet C D (C.facetClass o) =
      (combinedCells C D).facetClass (leftOccurrence C D o) := rfl

@[simp] theorem rightFacet_facetClass (o : D.FacetOccurrence) :
    rightFacet C D (D.facetClass o) =
      (combinedCells C D).facetClass (rightOccurrence C D o) := rfl

/-- The left quotient-facet embedding is injective. -/
theorem leftFacet_injective : Function.Injective (leftFacet C D) := by
  intro a b
  refine Quotient.inductionOn₂ (motive := fun x y =>
    leftFacet C D x = leftFacet C D y → x = y) a b (fun a b h => ?_)
  apply Quotient.sound
  rcases Quotient.exact h with ⟨g, hg⟩
  refine ⟨g, ?_⟩
  funext i
  apply leftPoint_injective
  simpa using congrFun hg i

/-- The right quotient-facet embedding is injective. -/
theorem rightFacet_injective : Function.Injective (rightFacet C D) := by
  intro a b
  refine Quotient.inductionOn₂ (motive := fun x y =>
    rightFacet C D x = rightFacet C D y → x = y) a b (fun a b h => ?_)
  apply Quotient.sound
  rcases Quotient.exact h with ⟨g, hg⟩
  refine ⟨g, ?_⟩
  funext i
  apply rightPoint_injective
  simpa using congrFun hg i

/-- Kronecker weight for the image of one combined quotient facet. -/
noncomputable def leftIndicator
    (s : (combinedCells C D).Facet) (t : C.Facet) : ZMod p :=
  if leftFacet C D t = s then 1 else 0

/-- Kronecker weight for the right image. -/
noncomputable def rightIndicator
    (s : (combinedCells C D).Facet) (t : D.Facet) : ZMod p :=
  if rightFacet C D t = s then 1 else 0

/-- Generic finite regrouping of occurrence weights by quotient-facet incidence. -/
theorem occurrencePairing_eq_facetPairing
    {A B E T : Nat}
    (K : RelativeAffineCellSystem hp A B E T)
    (W : K.Facet → ZMod p) :
    (∑ o : K.FacetOccurrence,
      K.coefficient o.1 * RelativeAffineCellSystem.alternatingSign o.2 * W (K.facetClass o)) =
      ∑ s : K.Facet, K.facetIncidence s * W s := by
  classical
  unfold RelativeAffineCellSystem.facetIncidence
  calc
    (∑ o : K.FacetOccurrence,
      K.coefficient o.1 * RelativeAffineCellSystem.alternatingSign o.2 * W (K.facetClass o)) =
      ∑ o : K.FacetOccurrence,
        ∑ s : K.Facet,
          if K.facetClass o = s then
            (K.coefficient o.1 * RelativeAffineCellSystem.alternatingSign o.2) * W s else 0 := by
      apply Finset.sum_congr rfl
      intro o ho
      rw [Finset.sum_ite_eq]
      simp
    _ = ∑ s : K.Facet,
        ∑ o : K.FacetOccurrence,
          if K.facetClass o = s then
            (K.coefficient o.1 * RelativeAffineCellSystem.alternatingSign o.2) * W s else 0 := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro o ho
      split_ifs <;> ring

/-- Split a finite sum over combined facet occurrences into its two components. -/
theorem sum_combinedOccurrence (f : (combinedCells C D).FacetOccurrence → ZMod p) :
    (∑ o, f o) =
      (∑ o : C.FacetOccurrence, f (leftOccurrence C D o)) +
        ∑ o : D.FacetOccurrence, f (rightOccurrence C D o) := by
  classical
  have h1 : (∑ o, f o) = ∑ c : C.Cell ⊕ D.Cell, ∑ k : Fin (p + 1), f (c, k) := by
    exact Fintype.sum_prod_type f
  have h2 : (∑ c : C.Cell ⊕ D.Cell, ∑ k : Fin (p + 1), f (c, k)) =
      (∑ c : C.Cell, ∑ k : Fin (p + 1), f (Sum.inl c, k)) +
        ∑ c : D.Cell, ∑ k : Fin (p + 1), f (Sum.inr c, k) :=
    Fintype.sum_sum_type _
  have h3 : (∑ c : C.Cell, ∑ k : Fin (p + 1), f (Sum.inl c, k)) =
      ∑ o : C.FacetOccurrence, f (leftOccurrence C D o) := by
    exact (Fintype.sum_prod_type (fun o : C.FacetOccurrence => f (leftOccurrence C D o))).symm
  have h4 : (∑ c : D.Cell, ∑ k : Fin (p + 1), f (Sum.inr c, k)) =
      ∑ o : D.FacetOccurrence, f (rightOccurrence C D o) := by
    exact (Fintype.sum_prod_type (fun o : D.FacetOccurrence => f (rightOccurrence C D o))).symm
  rw [h1, h2, h3, h4]

/-- Combined pointwise incidence is the sum of the two pushed-forward incidence pairings. -/
theorem combined_facetIncidence
    (s : (combinedCells C D).Facet) :
    (combinedCells C D).facetIncidence s =
      (∑ t : C.Facet, C.facetIncidence t * leftIndicator C D s t) +
      (∑ t : D.Facet, D.facetIncidence t * rightIndicator C D s t) := by
  classical
  have hleft := occurrencePairing_eq_facetPairing
    (hp := hp) C (leftIndicator C D s)
  have hright := occurrencePairing_eq_facetPairing
    (hp := hp) D (rightIndicator C D s)
  rw [← hleft, ← hright]
  unfold RelativeAffineCellSystem.facetIncidence
  rw [sum_combinedOccurrence]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro o ho
    simp [leftIndicator, leftOccurrence, combinedCells,  mul_one]
    change
      (if (combinedCells C D).facetClass (Sum.inl o.1, o.2) = s then
          C.coefficient o.1 * RelativeAffineCellSystem.alternatingSign o.2 else 0) =
        C.coefficient o.1 * RelativeAffineCellSystem.alternatingSign o.2 *
          (if (combinedCells C D).facetClass (Sum.inl o.1, o.2) = s then 1 else 0)
    split_ifs <;> simp
  · apply Finset.sum_congr rfl
    intro o ho
    simp [rightIndicator, rightOccurrence, combinedCells,  mul_one]
    change
      (if (combinedCells C D).facetClass (Sum.inr o.1, o.2) = s then
          D.coefficient o.1 * RelativeAffineCellSystem.alternatingSign o.2 else 0) =
        D.coefficient o.1 * RelativeAffineCellSystem.alternatingSign o.2 *
          (if (combinedCells C D).facetClass (Sum.inr o.1, o.2) = s then 1 else 0)
    split_ifs <;> simp

end Combined

variable
    (C : EndpointIdentifiedRelativeAffineCollar hp N₀ Nmid M₀ L₀)
    (D : EndpointIdentifiedRelativeAffineCollar hp Nmid N₁ M₁ L₁)

/-- The two copies of every common endpoint facet define the same combined quotient facet. -/
theorem internalFacet_eq (q : TopCell hp Nmid) :
    Combined.leftFacet C.cells D.cells (C.upperFacet q) =
      Combined.rightFacet C.cells D.cells (D.lowerFacet q) := by
  obtain ⟨oc, hoc⟩ := Quotient.exists_rep (C.upperFacet q)
  obtain ⟨od, hod⟩ := Quotient.exists_rep (D.lowerFacet q)
  rw [← hoc, ← hod]
  apply Quotient.sound
  obtain ⟨gc, hgc⟩ := C.upperFacetOccurrenceVertex_eq q oc hoc
  obtain ⟨gd, hgd⟩ := D.lowerFacetOccurrenceVertex_eq q od hod
  refine ⟨gd * gc⁻¹, ?_⟩
  funext i
  simp only [Combined.left_facetSignature, Combined.right_facetSignature]
  rw [hgc i, hgd i]
  simp [mul_smul]

/-- External lower coefficient of the composed collar. -/
noncomputable def lowerBoundaryCoefficient
    (s : (combinedCells C.cells D.cells).Facet) : ZMod p :=
  ∑ q : TopCell hp N₀,
    RefinedAffineMap.coefficient hp N₀ q *
      Combined.leftIndicator C.cells D.cells s (C.lowerFacet q)

/-- External upper coefficient of the composed collar. -/
noncomputable def upperBoundaryCoefficient
    (s : (combinedCells C.cells D.cells).Facet) : ZMod p :=
  ∑ q : TopCell hp N₁,
    RefinedAffineMap.coefficient hp N₁ q *
      Combined.rightIndicator C.cells D.cells s (D.upperFacet q)

/-- The common endpoint contributions of the two component collars cancel pointwise. -/
theorem internalPairings_eq
    (s : (combinedCells C.cells D.cells).Facet) :
    (∑ t : C.cells.Facet,
      C.upperBoundaryCoefficient t *
        Combined.leftIndicator C.cells D.cells s t) =
    (∑ t : D.cells.Facet,
      D.lowerBoundaryCoefficient t *
        Combined.rightIndicator C.cells D.cells s t) := by
  rw [C.upperBoundaryPairing_eq, D.lowerBoundaryPairing_eq]
  apply Finset.sum_congr rfl
  intro q hq
  simp only [Combined.leftIndicator, Combined.rightIndicator, internalFacet_eq C D q]

/-- Pointwise boundary formula for the composed collar. -/
theorem incidence_eq_boundary
    (s : (combinedCells C.cells D.cells).Facet) :
    (combinedCells C.cells D.cells).facetIncidence s =
      upperBoundaryCoefficient C D s - lowerBoundaryCoefficient C D s := by
  rw [Combined.combined_facetIncidence]
  simp_rw [C.incidence_eq_boundary, D.incidence_eq_boundary]
  simp only [sub_mul]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  rw [internalPairings_eq C D]
  rw [C.lowerBoundaryPairing_eq, D.upperBoundaryPairing_eq]
  unfold upperBoundaryCoefficient lowerBoundaryCoefficient
  ring

/-- Canonical lower endpoint facets are lower horizontal in the combined cylinder. -/
theorem lowerFacet_isLower (q : TopCell hp N₀) :
    (combinedCells C.cells D.cells).IsLowerFacet
      (Combined.leftFacet C.cells D.cells (C.lowerFacet q)) := by
  obtain ⟨o, ho⟩ := Quotient.exists_rep (C.lowerFacet q)
  rw [← ho]
  change (combinedCells C.cells D.cells).IsLowerFacetOccurrence
    (Combined.leftOccurrence C.cells D.cells o)
  intro i
  have h := C.lowerFacet_isLower q
  rw [← ho] at h
  simp only [Combined.left_facetSignature, leftPoint_time]
  simp [h i]

/-- Canonical upper endpoint facets are upper horizontal in the combined cylinder. -/
theorem upperFacet_isUpper (q : TopCell hp N₁) :
    (combinedCells C.cells D.cells).IsUpperFacet
      (Combined.rightFacet C.cells D.cells (D.upperFacet q)) := by
  obtain ⟨o, ho⟩ := Quotient.exists_rep (D.upperFacet q)
  rw [← ho]
  change (combinedCells C.cells D.cells).IsUpperFacetOccurrence
    (Combined.rightOccurrence C.cells D.cells o)
  intro i
  have h := D.upperFacet_isUpper q
  rw [← ho] at h
  simp only [Combined.right_facetSignature, rightPoint_time]
  rw [h i]
  norm_num

/-- External lower coefficients vanish away from the lower horizontal boundary. -/
theorem lowerBoundaryCoefficient_zero_of_not_lower
    (s : (combinedCells C.cells D.cells).Facet)
    (hs : ¬ (combinedCells C.cells D.cells).IsLowerFacet s) :
    lowerBoundaryCoefficient C D s = 0 := by
  classical
  unfold lowerBoundaryCoefficient
  apply Finset.sum_eq_zero
  intro q hq
  have hne : Combined.leftFacet C.cells D.cells (C.lowerFacet q) ≠ s := by
    intro h
    apply hs
    rw [← h]
    exact lowerFacet_isLower C D q
  simp [Combined.leftIndicator, hne]

/-- External upper coefficients vanish away from the upper horizontal boundary. -/
theorem upperBoundaryCoefficient_zero_of_not_upper
    (s : (combinedCells C.cells D.cells).Facet)
    (hs : ¬ (combinedCells C.cells D.cells).IsUpperFacet s) :
    upperBoundaryCoefficient C D s = 0 := by
  classical
  unfold upperBoundaryCoefficient
  apply Finset.sum_eq_zero
  intro q hq
  have hne : Combined.rightFacet C.cells D.cells (D.upperFacet q) ≠ s := by
    intro h
    apply hs
    rw [← h]
    exact upperFacet_isUpper C D q
  simp [Combined.rightIndicator, hne]

/-- Every lower-horizontal combined quotient facet comes from the external lower boundary. -/
theorem lowerFacet_exhaustive
    (s : (combinedCells C.cells D.cells).Facet)
    (hs : (combinedCells C.cells D.cells).IsLowerFacet s) :
    ∃ q : TopCell hp N₀,
      Combined.leftFacet C.cells D.cells (C.lowerFacet q) = s := by
  refine Quotient.inductionOn s (fun o ho => ?_) hs
  rcases o with ⟨cell, k⟩
  cases cell with
  | inl cell =>
      let oc : C.cells.FacetOccurrence := (cell, k)
      have hc : C.cells.IsLowerFacetOccurrence oc := by
        intro i
        have hi := ho i
        change (C.cells.facetSignature oc i).time.1 / 2 = 0 at hi
        linarith
      have hcq : C.cells.IsLowerFacet (C.cells.facetClass oc) := hc
      obtain ⟨q, hq⟩ := C.lowerFacet_exhaustive _ hcq
      refine ⟨q, ?_⟩
      rw [hq]
      rfl
  | inr cell =>
      let i : Fin p := ⟨0, hp.pos⟩
      have hi := ho i
      have hnonneg := (D.cells.facetSignature (cell, k) i).time.2.1
      change (1 + (D.cells.facetSignature (cell, k) i).time.1) / 2 = 0 at hi
      linarith

/-- Every upper-horizontal combined quotient facet comes from the external upper boundary. -/
theorem upperFacet_exhaustive
    (s : (combinedCells C.cells D.cells).Facet)
    (hs : (combinedCells C.cells D.cells).IsUpperFacet s) :
    ∃ q : TopCell hp N₁,
      Combined.rightFacet C.cells D.cells (D.upperFacet q) = s := by
  refine Quotient.inductionOn s (fun o ho => ?_) hs
  rcases o with ⟨cell, k⟩
  cases cell with
  | inl cell =>
      let i : Fin p := ⟨0, hp.pos⟩
      have hi := ho i
      have hle := (C.cells.facetSignature (cell, k) i).time.2.2
      change (C.cells.facetSignature (cell, k) i).time.1 / 2 = 1 at hi
      linarith
  | inr cell =>
      let od : D.cells.FacetOccurrence := (cell, k)
      have hd : D.cells.IsUpperFacetOccurrence od := by
        intro i
        have hi := ho i
        change (1 + (D.cells.facetSignature od i).time.1) / 2 = 1 at hi
        linarith
      have hdq : D.cells.IsUpperFacet (D.cells.facetClass od) := hd
      obtain ⟨q, hq⟩ := D.upperFacet_exhaustive _ hdq
      refine ⟨q, ?_⟩
      rw [hq]
      rfl

/-- Chain-level lower endpoint identity for the composed collar. -/
theorem lowerBoundaryPairing_eq
    (W : (combinedCells C.cells D.cells).Facet → ZMod p) :
    (∑ s : (combinedCells C.cells D.cells).Facet,
      lowerBoundaryCoefficient C D s * W s) =
      ∑ q : TopCell hp N₀,
        RefinedAffineMap.coefficient hp N₀ q *
          W (Combined.leftFacet C.cells D.cells (C.lowerFacet q)) := by
  classical
  unfold lowerBoundaryCoefficient
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  simp only [Combined.leftIndicator, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp

/-- Chain-level upper endpoint identity for the composed collar. -/
theorem upperBoundaryPairing_eq
    (W : (combinedCells C.cells D.cells).Facet → ZMod p) :
    (∑ s : (combinedCells C.cells D.cells).Facet,
      upperBoundaryCoefficient C D s * W s) =
      ∑ q : TopCell hp N₁,
        RefinedAffineMap.coefficient hp N₁ q *
          W (Combined.rightFacet C.cells D.cells (D.upperFacet q)) := by
  classical
  unfold upperBoundaryCoefficient
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  simp only [Combined.rightIndicator, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp

/-- Representatives of external lower facets have the prescribed level-`N₀` geometry. -/
theorem lowerFacetOccurrenceVertex_eq
    (q : TopCell hp N₀)
    (o : (combinedCells C.cells D.cells).FacetOccurrence)
    (ho : (combinedCells C.cells D.cells).facetClass o =
      Combined.leftFacet C.cells D.cells (C.lowerFacet q)) :
    ∃ g : PrimeSymmetry p, ∀ i,
      (combinedCells C.cells D.cells).facetSignature o i =
        g • lowerCylinderPoint (RefinedAffineMap.vertex hp N₀ q
          (Fin.cast (Nat.sub_add_cancel hp.pos).symm i)) := by
  rcases o with ⟨cell, k⟩
  cases cell with
  | inl cell =>
      let oc : C.cells.FacetOccurrence := (cell, k)
      have hc : C.cells.facetClass oc = C.lowerFacet q := by
        apply Combined.leftFacet_injective C.cells D.cells
        simpa [oc, Combined.leftOccurrence] using ho
      obtain ⟨g, hg⟩ := C.lowerFacetOccurrenceVertex_eq q oc hc
      refine ⟨g, ?_⟩
      intro i
      simpa [oc, combinedCells, Combined.leftOccurrence,
        ExplicitAffineRelativeCollar.RelativeAffineCellSystem.facetSignature] using
        congrArg leftPoint (hg i)
  | inr cell =>
      have hlower : (combinedCells C.cells D.cells).IsLowerFacet
          ((combinedCells C.cells D.cells).facetClass (Sum.inr cell, k)) := by
        rw [ho]
        exact lowerFacet_isLower C D q
      change (combinedCells C.cells D.cells).IsLowerFacetOccurrence
        (Sum.inr cell, k) at hlower
      let i : Fin p := ⟨0, hp.pos⟩
      have hi := hlower i
      have hnonneg := (D.cells.facetSignature (cell, k) i).time.2.1
      change (1 + (D.cells.facetSignature (cell, k) i).time.1) / 2 = 0 at hi
      exfalso
      linarith

/-- Representatives of external upper facets have the prescribed level-`N₁` geometry. -/
theorem upperFacetOccurrenceVertex_eq
    (q : TopCell hp N₁)
    (o : (combinedCells C.cells D.cells).FacetOccurrence)
    (ho : (combinedCells C.cells D.cells).facetClass o =
      Combined.rightFacet C.cells D.cells (D.upperFacet q)) :
    ∃ g : PrimeSymmetry p, ∀ i,
      (combinedCells C.cells D.cells).facetSignature o i =
        g • upperCylinderPoint (RefinedAffineMap.vertex hp N₁ q
          (Fin.cast (Nat.sub_add_cancel hp.pos).symm i)) := by
  rcases o with ⟨cell, k⟩
  cases cell with
  | inl cell =>
      have hupper : (combinedCells C.cells D.cells).IsUpperFacet
          ((combinedCells C.cells D.cells).facetClass (Sum.inl cell, k)) := by
        rw [ho]
        exact upperFacet_isUpper C D q
      change (combinedCells C.cells D.cells).IsUpperFacetOccurrence
        (Sum.inl cell, k) at hupper
      let i : Fin p := ⟨0, hp.pos⟩
      have hi := hupper i
      have hle := (C.cells.facetSignature (cell, k) i).time.2.2
      change (C.cells.facetSignature (cell, k) i).time.1 / 2 = 1 at hi
      exfalso
      linarith
  | inr cell =>
      let od : D.cells.FacetOccurrence := (cell, k)
      have hd : D.cells.facetClass od = D.upperFacet q := by
        apply Combined.rightFacet_injective C.cells D.cells
        simpa [od, Combined.rightOccurrence] using ho
      obtain ⟨g, hg⟩ := D.upperFacetOccurrenceVertex_eq q od hd
      refine ⟨g, ?_⟩
      intro i
      simpa [od, combinedCells, Combined.rightOccurrence,
        ExplicitAffineRelativeCollar.RelativeAffineCellSystem.facetSignature] using
        congrArg rightPoint (hg i)

/-- Pointwise composed relative collar. -/
noncomputable def relativeCollar :
    FoxNeuwirthRelativeAffineCollar hp N₀ N₁ (max M₀ M₁) (L₀ + L₁ + 1) where
  cells := combinedCells C.cells D.cells
  lowerBoundaryCoefficient := lowerBoundaryCoefficient C D
  upperBoundaryCoefficient := upperBoundaryCoefficient C D
  lower_zero_of_not_lower := lowerBoundaryCoefficient_zero_of_not_lower C D
  upper_zero_of_not_upper := upperBoundaryCoefficient_zero_of_not_upper C D
  incidence_eq_boundary := incidence_eq_boundary C D

/-- Composition of endpoint-identified relative affine collars. -/
noncomputable def endpointIdentifiedCollar :
    EndpointIdentifiedRelativeAffineCollar hp N₀ N₁ (max M₀ M₁) (L₀ + L₁ + 1) where
  toFoxNeuwirthRelativeAffineCollar := relativeCollar C D
  lowerFacet q := Combined.leftFacet C.cells D.cells (C.lowerFacet q)
  upperFacet q := Combined.rightFacet C.cells D.cells (D.upperFacet q)
  lowerFacet_isLower := lowerFacet_isLower C D
  upperFacet_isUpper := upperFacet_isUpper C D
  lowerFacet_exhaustive := lowerFacet_exhaustive C D
  upperFacet_exhaustive := upperFacet_exhaustive C D
  lowerBoundaryPairing_eq := lowerBoundaryPairing_eq C D
  upperBoundaryPairing_eq := upperBoundaryPairing_eq C D
  lowerFacetOccurrenceVertex_eq := lowerFacetOccurrenceVertex_eq C D
  upperFacetOccurrenceVertex_eq := upperFacetOccurrenceVertex_eq C D

end ExplicitAffineRelativeCollarCompose
end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR
