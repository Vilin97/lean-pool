/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.FiniteSimplex
public import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.ExplicitAffineRelativeCollarReverse
/-!
# Cell system for composing relative affine collars

Two collars with a common intermediate endpoint are placed in the lower and upper half of the
realization cylinder.  Their cell families are joined by disjoint union.  The quotient-facet
relation then identifies the two copies of every intermediate endpoint facet.  The upper boundary
pairing of the first collar and lower boundary pairing of the second collar are the same refined
Fox--Neuwirth chain, hence cancel pointwise after regrouping by combined quotient facets.
-/

@[expose] public section

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
    simp [leftIndicator, leftOccurrence, combinedCells]
    change
      (if (combinedCells C D).facetClass (Sum.inl o.1, o.2) = s then
          C.coefficient o.1 * RelativeAffineCellSystem.alternatingSign o.2 else 0) =
        C.coefficient o.1 * RelativeAffineCellSystem.alternatingSign o.2 *
          (if (combinedCells C D).facetClass (Sum.inl o.1, o.2) = s then 1 else 0)
    split_ifs <;> simp
  · apply Finset.sum_congr rfl
    intro o ho
    simp [rightIndicator, rightOccurrence, combinedCells]
    change
      (if (combinedCells C D).facetClass (Sum.inr o.1, o.2) = s then
          D.coefficient o.1 * RelativeAffineCellSystem.alternatingSign o.2 else 0) =
        D.coefficient o.1 * RelativeAffineCellSystem.alternatingSign o.2 *
          (if (combinedCells C D).facetClass (Sum.inr o.1, o.2) = s then 1 else 0)
    split_ifs <;> simp

end Combined

end ExplicitAffineRelativeCollarCompose
end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR
