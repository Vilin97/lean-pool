/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.CuspFibre.CuspPositiveRetraction
public import LeanPool.HopfProblem.Elliptic.Core1
import all LeanPool.HopfProblem.HomologyTheory.SingularMayerVietoris
import all LeanPool.HopfProblem.Foundations.TriangleRegularBaseFundamentalGroup
import all LeanPool.HopfProblem.Toric.ToricSpace1
import all LeanPool.HopfProblem.Toric.ToricSpace2
import all LeanPool.HopfProblem.CuspFibre.CuspPositiveRetraction
import all LeanPool.HopfProblem.HomologyTheory.FirstHurewicz3
import all LeanPool.HopfProblem.Elliptic.Core1

/-!
# Hopf problem: toric · cusp honeycomb hexagon

Supporting definitions and proofs for this stage of the six-sphere construction.
-/


open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

noncomputable section

namespace Mathoverflow1973

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

private def CuspHoneycombPositive.positiveCell (v : Fin 2 → ℤ) :
    Set CuspPositiveRetraction.PositiveCentralFibre :=
  {q | (q.1 : ToricSpace.Space) ∈ ToricSpace.rayDivisor v}

private theorem
    CuspHoneycombPositive.positiveCell_isClosed (v : Fin 2 → ℤ) : IsClosed (positiveCell v) :=
  (ToricSpace.rayDivisor_isClosed v).preimage (continuous_subtype_val.comp continuous_subtype_val)

private theorem CuspHoneycombPositive.positiveCells_locallyFinite : LocallyFinite positiveCell :=
  ToricSpace.rayDivisors_locallyFinite.preimage_continuous
    (continuous_subtype_val.comp continuous_subtype_val)

private theorem CuspHoneycombPositive.iUnion_positiveCell :
    (⋃ v : Fin 2 → ℤ, positiveCell v) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro q
  have hq : (q.1 : ToricSpace.Space) ∈ ToricSpace.time ⁻¹' {0} := q.2
  rw [ToricSpace.central_fibre_eq_rayDivisors] at hq
  obtain ⟨v, hv⟩ := Set.mem_iUnion.mp hq
  exact Set.mem_iUnion.mpr ⟨v, hv⟩

private def CuspHoneycombPositive.positiveCellComponentHomeomorph (v : Fin 2 → ℤ) :
    positiveCell v ≃ₜ CuspHoneycombHexagon.PositiveComponent v
    where
  toFun q := ⟨⟨q.1.1.1, q.2⟩, q.1.1.2⟩
  invFun x := ⟨⟨⟨x.1.1, x.2⟩, ToricSpace.time_eq_zero_of_mem_rayDivisor x.1.2⟩, x.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val

private abbrev CuspHoneycombPositive.positiveCellZeroHomeomorph :
    positiveCell 0 ≃ₜ CuspHoneycombHexagon.PositiveE0 :=
  positiveCellComponentHomeomorph 0

private theorem CuspHoneycombPositive.positiveCentralTranslate_mem_positiveCell
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (u v : Fin 2 → ℤ)
    (q : CuspPositiveRetraction.PositiveCentralFibre) :
    CuspCollapse.positiveCentralTranslate C₀ u q ∈ positiveCell v ↔
      q ∈ positiveCell (v - ToricSpace.cuspVector u) :=
  ToricSpace.twistedTranslate_mem_rayDivisor (CuspPositive.positiveTwist C₀) u v
    (q.1 : ToricSpace.Space)

private def CuspHoneycombPositive.positiveE0CellHomeomorph (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) : CuspHoneycombHexagon.PositiveE0 ≃ₜ positiveCell v :=
  positiveCellZeroHomeomorph.symm.trans
    ((CuspCollapse.positiveCentralHomeomorph C₀ (-ToricSpace.cuspVector v)).subtype
      (fun q =>
        by
        change
          q ∈ positiveCell 0 ↔
            CuspCollapse.positiveCentralTranslate C₀ (-ToricSpace.cuspVector v) q ∈ positiveCell v
        rw [positiveCentralTranslate_mem_positiveCell, ToricSpace.cuspVector_neg,
          ToricSpace.cuspVector_cuspVector, neg_neg, sub_self]))

private def
    CuspHoneycombHexagon.orientedCoordinates (i : Fin 6) (z : ToricCharts.CoordinateSpace 2) :
    ToricCharts.CoordinateSpace 2 :=
  if i = 1 ∨ i = 2 ∨ i = 3 then ![z 1, z 0] else z

@[simp]
private theorem CuspHoneycombHexagon.orientedCoordinates_involutive (i : Fin 6)
    (z : ToricCharts.CoordinateSpace 2) : orientedCoordinates i (orientedCoordinates i z) = z := by
  by_cases hi : i = 1 ∨ i = 2 ∨ i = 3
  · funext j
    fin_cases j <;> simp [orientedCoordinates, hi]
  · simp [orientedCoordinates, hi]

private theorem CuspHoneycombHexagon.orientedCoordinates_continuous (i : Fin 6) :
    Continuous (orientedCoordinates i) := by
  unfold orientedCoordinates
  split_ifs
  · apply continuous_pi
    intro j
    fin_cases j
    · exact continuous_apply 1
    · exact continuous_apply 0
  · exact continuous_id

private def CuspHoneycombHexagon.orientedHomeomorph (i : Fin 6) :
    ToricCharts.CoordinateSpace 2 ≃ₜ ToricCharts.CoordinateSpace 2
    where
  toFun := orientedCoordinates i
  invFun := orientedCoordinates i
  left_inv := orientedCoordinates_involutive i
  right_inv := orientedCoordinates_involutive i
  continuous_toFun := orientedCoordinates_continuous i
  continuous_invFun := orientedCoordinates_continuous i

private def CuspHoneycombHexagon.firstCoordinate : Fin 6 → Fin 3 :=
  ![1, 2, 2, 1, 0, 0]

private def CuspHoneycombHexagon.secondCoordinate : Fin 6 → Fin 3 :=
  ![2, 1, 0, 0, 1, 2]

private theorem CuspHoneycombHexagon.firstCoordinate_vertex (i : Fin 6) :
    (ToricComponent.zeroTriangle i).vertex (firstCoordinate i) = ToricComponent.hexagonRay i := by
  fin_cases i <;> decide

private theorem CuspHoneycombHexagon.secondCoordinate_vertex (i : Fin 6) :
    (ToricComponent.zeroTriangle i).vertex (secondCoordinate i) =
      ToricComponent.hexagonRay (i + 1) := by fin_cases i <;> decide

private theorem CuspHoneycombHexagon.coordinates_exhaustive (i : Fin 6) (j : Fin 3) :
    j = ToricComponent.zeroCoordinate i ∨ j = firstCoordinate i ∨ j = secondCoordinate i := by
  fin_cases i <;> fin_cases j <;> decide

private def CuspHoneycombHexagon.liftCoordinates (i : Fin 6) (z : ToricCharts.CoordinateSpace 2) :
    ToricCharts.CoordinateSpace 3 :=
  ToricComponent.insertZero (ToricComponent.zeroCoordinate i) (orientedCoordinates i z)

@[simp]
private theorem CuspHoneycombHexagon.liftCoordinates_zero (i : Fin 6)
    (z : ToricCharts.CoordinateSpace 2) :
    liftCoordinates i z (ToricComponent.zeroCoordinate i) = 0 :=
  ToricComponent.insertZero_at _ _

@[simp]
private theorem CuspHoneycombHexagon.liftCoordinates_first (i : Fin 6)
    (z : ToricCharts.CoordinateSpace 2) : liftCoordinates i z (firstCoordinate i) = z 0 := by
  fin_cases i <;> rfl

@[simp]
private theorem CuspHoneycombHexagon.liftCoordinates_second (i : Fin 6)
    (z : ToricCharts.CoordinateSpace 2) : liftCoordinates i z (secondCoordinate i) = z 1 := by
  fin_cases i <;> rfl

private theorem CuspHoneycombHexagon.liftCoordinates_table (i : Fin 6)
    (z : ToricCharts.CoordinateSpace 2) :
    liftCoordinates i z =
      ![![0, z 0, z 1], ![0, z 1, z 0], ![z 1, 0, z 0], ![z 1, z 0, 0], ![z 0, z 1, 0],
          ![z 0, 0, z 1] ]
        i := by fin_cases i <;> ext j <;> fin_cases j <;> rfl

private theorem CuspHoneycombHexagon.liftCoordinates_vector (i : Fin 6) (a b : ℂ) :
    liftCoordinates i ![a, b] =
      ![![0, a, b], ![0, b, a], ![b, 0, a], ![b, a, 0], ![a, b, 0], ![a, 0, b] ] i :=
  liftCoordinates_table i ![a, b]

private def CuspHoneycombHexagon.chartPoint (i : Fin 6) (z : ToricCharts.CoordinateSpace 2) :
    ToricSpace.rayDivisor 0 :=
  ToricComponent.affineInclusion (ToricComponent.zeroChart i) (orientedCoordinates i z)

@[simp]
private theorem
    CuspHoneycombHexagon.chartPoint_coe (i : Fin 6) (z : ToricCharts.CoordinateSpace 2) :
    (chartPoint i z : ToricSpace.Space) =
      ToricSpace.inclusion (ToricComponent.zeroTriangle i) (liftCoordinates i z) :=
  rfl

private theorem CuspHoneycombHexagon.chartPoint_openEmbedding (i : Fin 6) :
    Topology.IsOpenEmbedding (chartPoint i) :=
  (ToricComponent.affineInclusion_openEmbedding (ToricComponent.zeroChart i)).comp
    (orientedHomeomorph i).isOpenEmbedding

private theorem CuspHoneycombHexagon.chartPoint_injective (i : Fin 6) :
    Function.Injective (chartPoint i) :=
  (chartPoint_openEmbedding i).injective

private theorem
    CuspHoneycombHexagon.chartPoint_continuous (i : Fin 6) : Continuous (chartPoint i) :=
  (chartPoint_openEmbedding i).continuous

private theorem CuspHoneycombHexagon.chartPoint_jointly_surjective (x : ToricSpace.rayDivisor 0) :
    ∃ i z, chartPoint i z = x := by
  obtain ⟨c, z, hz⟩ := ToricComponent.affineInclusion_jointly_surjective x
  obtain ⟨i, rfl⟩ := ToricComponent.zeroChart_surjective c
  refine ⟨i, orientedCoordinates i z, ?_⟩
  change
    ToricComponent.affineInclusion (ToricComponent.zeroChart i)
        (orientedCoordinates i (orientedCoordinates i z)) =
      x
  rw [orientedCoordinates_involutive]
  exact hz

private theorem CuspHoneycombHexagon.chartPoint_eq_iff (i j : Fin 6)
    (z w : ToricCharts.CoordinateSpace 2) :
    chartPoint i z = chartPoint j w ↔
      liftCoordinates i z ∈
          (ToricFan.Triangle.chartChange (ToricComponent.zeroTriangle i)
              (ToricComponent.zeroTriangle j)).source ∧
        ToricFan.Triangle.chartChange (ToricComponent.zeroTriangle i)
            (ToricComponent.zeroTriangle j) (liftCoordinates i z) =
          liftCoordinates j w := by
  rw [Subtype.ext_iff, chartPoint_coe, chartPoint_coe, ToricSpace.inclusion_eq_iff]

private theorem CuspHoneycombHexagon.chartPoint_mem_rayDivisor_iff (i k : Fin 6)
    (z : ToricCharts.CoordinateSpace 2) :
    (chartPoint i z : ToricSpace.Space) ∈ ToricSpace.rayDivisor (ToricComponent.hexagonRay k) ↔
      (k = i ∧ z 0 = 0) ∨ (k = i + 1 ∧ z 1 = 0) := by
  rw [chartPoint_coe, ToricSpace.mem_rayDivisor_inclusion]
  constructor
  · rintro ⟨j, hj, hv⟩
    rcases coordinates_exhaustive i j with rfl | rfl | rfl
    · exact
        (ToricComponent.hexagonRay_ne_zero k
            ((ToricComponent.zeroTriangle_vertex i).symm.trans hv).symm).elim
    · exact
        Or.inl
          ⟨(ToricComponent.hexagonRay_injective ((firstCoordinate_vertex i).symm.trans hv)).symm,
            by simpa only [liftCoordinates_first] using hj⟩
    · exact
        Or.inr
          ⟨(ToricComponent.hexagonRay_injective ((secondCoordinate_vertex i).symm.trans hv)).symm,
            by simpa only [liftCoordinates_second] using hj⟩
  · rintro (⟨hki, hz⟩ | ⟨hki, hz⟩)
    · subst k
      exact ⟨firstCoordinate i, (liftCoordinates_first i z).trans hz, firstCoordinate_vertex i⟩
    · subst k
      exact ⟨secondCoordinate i, (liftCoordinates_second i z).trans hz, secondCoordinate_vertex i⟩

private def CuspHoneycombHexagon.nextTransitionMatrix : Fin 6 → Matrix (Fin 3) (Fin 3) ℤ :=
  ![!![1, 1, 0; 0, -1, 0; 0, 1, 1], !![0, 0, -1; 1, 0, 1; 0, 1, 1],
    !![0, 0, -1; 1, 0, 1; 0, 1, 1], !![1, 1, 0; 0, -1, 0; 0, 1, 1],
    !![1, 1, 0; 1, 0, 1; -1, 0, 0], !![1, 1, 0; 1, 0, 1; -1, 0, 0] ]

private theorem CuspHoneycombHexagon.transition_next (i : Fin 6) :
    ToricFan.Triangle.transition (ToricComponent.zeroTriangle i)
        (ToricComponent.zeroTriangle (i + 1)) =
      nextTransitionMatrix i := by fin_cases i <;> decide

private theorem CuspHoneycombHexagon.next_source_iff (i : Fin 6) (a b : ℂ) :
    liftCoordinates i ![a, b] ∈
        (ToricFan.Triangle.chartChange (ToricComponent.zeroTriangle i)
            (ToricComponent.zeroTriangle (i + 1))).source ↔
      a ≠ 0 := by
  rw [ToricFan.Triangle.chartChange_source, transition_next, liftCoordinates_vector]
  fin_cases i <;>
    norm_num [ToricCharts.domain, nextTransitionMatrix, Fin.forall_fin_succ, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail]

private theorem CuspHoneycombHexagon.next_transition (i : Fin 6) (a b : ℂ) :
    ToricFan.Triangle.chartChange (ToricComponent.zeroTriangle i)
        (ToricComponent.zeroTriangle (i + 1)) (liftCoordinates i ![a, b]) =
      liftCoordinates (i + 1) ![a * b, a⁻¹] := by
  change ToricCharts.monomial (ToricFan.Triangle.transition _ _) _ = _
  rw [transition_next, liftCoordinates_vector, liftCoordinates_vector]
  fin_cases i <;> ext j <;> fin_cases j <;>
    norm_num [ToricCharts.monomial, nextTransitionMatrix, Fin.prod_univ_succ, Fin.add_def,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead,
      Matrix.vecTail, mul_comm]

private theorem CuspHoneycombHexagon.chartPoint_next (i : Fin 6) (a b : ℂ) (ha : a ≠ 0) :
    chartPoint (i + 1) ![a * b, a⁻¹] = chartPoint i ![a, b] := by
  symm
  exact
    (chartPoint_eq_iff i (i + 1) ![a, b] ![a * b, a⁻¹]).mpr
      ⟨(next_source_iff i a b).mpr ha, next_transition i a b⟩

private theorem CuspHoneycombHexagon.chartPoint_eq_next_iff (i : Fin 6) (a b c d : ℂ) :
    chartPoint i ![a, b] = chartPoint (i + 1) ![c, d] ↔ a ≠ 0 ∧ c = a * b ∧ d = a⁻¹ := by
  constructor
  · intro he
    have ha := (next_source_iff i a b).mp ((chartPoint_eq_iff i (i + 1) _ _).mp he).1
    have hw : ![c, d] = ![a * b, a⁻¹] :=
      chartPoint_injective (i + 1) (he.symm.trans (chartPoint_next i a b ha).symm)
    exact ⟨ha, congrFun hw 0, congrFun hw 1⟩
  · rintro ⟨ha, rfl, rfl⟩
    exact (chartPoint_next i a b ha).symm

private theorem CuspHoneycombHexagon.chartPoint_eq_nonadjacent_nonzero {i j : Fin 6}
    {z w : ToricCharts.CoordinateSpace 2} (hji : j ≠ i) (hnext : j ≠ i + 1) (hprev : i ≠ j + 1)
    (he : chartPoint i z = chartPoint j w) : z 0 ≠ 0 ∧ z 1 ≠ 0 := by
  have hcoe : (chartPoint i z : ToricSpace.Space) = (chartPoint j w : ToricSpace.Space) :=
    congrArg Subtype.val he
  constructor
  · intro hz
    have hm :
      (chartPoint j w : ToricSpace.Space) ∈ ToricSpace.rayDivisor (ToricComponent.hexagonRay i) :=
      by
      rw [← hcoe]
      exact (chartPoint_mem_rayDivisor_iff i i z).mpr (Or.inl ⟨rfl, hz⟩)
    rcases (chartPoint_mem_rayDivisor_iff j i w).mp hm with ⟨hi, _⟩ | ⟨hi, _⟩
    · exact hji hi.symm
    · exact hprev hi
  · intro hz
    have hm :
      (chartPoint j w : ToricSpace.Space) ∈
        ToricSpace.rayDivisor (ToricComponent.hexagonRay (i + 1)) := by
      rw [← hcoe]
      exact (chartPoint_mem_rayDivisor_iff i (i + 1) z).mpr (Or.inr ⟨rfl, hz⟩)
    rcases (chartPoint_mem_rayDivisor_iff j (i + 1) w).mp hm with ⟨hi, _⟩ | ⟨hi, _⟩
    · exact hnext hi.symm
    · exact hji (add_right_cancel hi).symm

private def CuspHoneycombHexagon.previousTransitionMatrix : Fin 6 → Matrix (Fin 3) (Fin 3) ℤ :=
  ![!![0, 0, -1; 1, 0, 1; 0, 1, 1], !![1, 1, 0; 0, -1, 0; 0, 1, 1],
    !![1, 1, 0; 1, 0, 1; -1, 0, 0], !![1, 1, 0; 1, 0, 1; -1, 0, 0],
    !![1, 1, 0; 0, -1, 0; 0, 1, 1], !![0, 0, -1; 1, 0, 1; 0, 1, 1] ]

private theorem CuspHoneycombHexagon.transition_previous (i : Fin 6) :
    ToricFan.Triangle.transition (ToricComponent.zeroTriangle i)
        (ToricComponent.zeroTriangle (i + 5)) =
      previousTransitionMatrix i := by fin_cases i <;> decide

private theorem CuspHoneycombHexagon.previous_source_iff (i : Fin 6) (a b : ℂ) :
    liftCoordinates i ![a, b] ∈
        (ToricFan.Triangle.chartChange (ToricComponent.zeroTriangle i)
            (ToricComponent.zeroTriangle (i + 5))).source ↔
      b ≠ 0 := by
  rw [ToricFan.Triangle.chartChange_source, transition_previous, liftCoordinates_vector]
  fin_cases i <;>
    norm_num [ToricCharts.domain, previousTransitionMatrix, Fin.forall_fin_succ,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead,
      Matrix.vecTail]

private theorem CuspHoneycombHexagon.previous_transition (i : Fin 6) (a b : ℂ) :
    ToricFan.Triangle.chartChange (ToricComponent.zeroTriangle i)
        (ToricComponent.zeroTriangle (i + 5)) (liftCoordinates i ![a, b]) =
      liftCoordinates (i + 5) ![b⁻¹, a * b] := by
  change ToricCharts.monomial (ToricFan.Triangle.transition _ _) _ = _
  rw [transition_previous, liftCoordinates_vector, liftCoordinates_vector]
  fin_cases i <;> ext j <;> fin_cases j <;>
      norm_num [ToricCharts.monomial, previousTransitionMatrix, Fin.prod_univ_succ, Fin.add_def,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead,
        Matrix.vecTail, mul_comm] <;>
    rfl

private theorem CuspHoneycombHexagon.chartPoint_previous (i : Fin 6) (a b : ℂ) (hb : b ≠ 0) :
    chartPoint (i + 5) ![b⁻¹, a * b] = chartPoint i ![a, b] := by
  symm
  exact
    (chartPoint_eq_iff i (i + 5) ![a, b] ![b⁻¹, a * b]).mpr
      ⟨(previous_source_iff i a b).mpr hb, previous_transition i a b⟩

private theorem CuspHoneycombHexagon.chartPoint_eq_previous_iff (i : Fin 6) (a b c d : ℂ) :
    chartPoint i ![a, b] = chartPoint (i + 5) ![c, d] ↔ b ≠ 0 ∧ c = b⁻¹ ∧ d = a * b := by
  constructor
  · intro he
    have hb := (previous_source_iff i a b).mp ((chartPoint_eq_iff i (i + 5) _ _).mp he).1
    have hw : ![c, d] = ![b⁻¹, a * b] :=
      chartPoint_injective (i + 5) (he.symm.trans (chartPoint_previous i a b hb).symm)
    exact ⟨hb, congrFun hw 0, congrFun hw 1⟩
  · rintro ⟨hb, rfl, rfl⟩
    exact (chartPoint_previous i a b hb).symm

private theorem CuspHoneycombHexagon.chartPoint_offset_two (i : Fin 6) (a b : ℂ) (ha : a ≠ 0)
    (hb : b ≠ 0) : chartPoint (i + 2) ![b, (a * b)⁻¹] = chartPoint i ![a, b] := by
  have hi : (i + 1) + 1 = i + 2 := by rw [add_assoc]; rfl
  have hm : a * b * a⁻¹ = b := by rw [mul_right_comm, mul_inv_cancel₀ ha, one_mul]
  simpa only [hi, hm] using
    (chartPoint_next (i + 1) (a * b) a⁻¹ (mul_ne_zero ha hb)).trans (chartPoint_next i a b ha)

private theorem CuspHoneycombHexagon.chartPoint_offset_three (i : Fin 6) (a b : ℂ) (ha : a ≠ 0)
    (hb : b ≠ 0) : chartPoint (i + 3) ![a⁻¹, b⁻¹] = chartPoint i ![a, b] := by
  have hi : (i + 2) + 1 = i + 3 := by rw [add_assoc]; rfl
  have hm : b * (a * b)⁻¹ = a⁻¹ := by simp [mul_inv_rev, hb]
  simpa only [hi, hm] using
    (chartPoint_next (i + 2) b (a * b)⁻¹ hb).trans (chartPoint_offset_two i a b ha hb)

private theorem CuspHoneycombHexagon.chartPoint_offset_four (i : Fin 6) (a b : ℂ) (ha : a ≠ 0)
    (hb : b ≠ 0) : chartPoint (i + 4) ![(a * b)⁻¹, a] = chartPoint i ![a, b] := by
  have hi : (i + 3) + 1 = i + 4 := by rw [add_assoc]; rfl
  have hm : a⁻¹ * b⁻¹ = (a * b)⁻¹ := by simp [mul_inv_rev, mul_comm]
  simpa only [hi, hm, inv_inv] using
    (chartPoint_next (i + 3) a⁻¹ b⁻¹ (inv_ne_zero ha)).trans (chartPoint_offset_three i a b ha hb)

private theorem CuspHoneycombHexagon.chartPoint_eq_offset_two_iff (i : Fin 6) (a b c d : ℂ) :
    chartPoint i ![a, b] = chartPoint (i + 2) ![c, d] ↔ a ≠ 0 ∧ b ≠ 0 ∧ c = b ∧ d = (a * b)⁻¹ := by
  constructor
  · intro he
    obtain ⟨ha, hb⟩ :=
      chartPoint_eq_nonadjacent_nonzero (by fin_cases i <;> decide : i + 2 ≠ i)
        (by fin_cases i <;> decide : i + 2 ≠ i + 1) (by fin_cases i <;> decide : i ≠ (i + 2) + 1)
        he
    have hw : ![c, d] = ![b, (a * b)⁻¹] :=
      chartPoint_injective (i + 2) (he.symm.trans (chartPoint_offset_two i a b ha hb).symm)
    exact ⟨ha, hb, congrFun hw 0, congrFun hw 1⟩
  · rintro ⟨ha, hb, hc, hd⟩
    subst c d
    exact (chartPoint_offset_two i a b ha hb).symm

private theorem CuspHoneycombHexagon.chartPoint_eq_offset_three_iff (i : Fin 6) (a b c d : ℂ) :
    chartPoint i ![a, b] = chartPoint (i + 3) ![c, d] ↔ a ≠ 0 ∧ b ≠ 0 ∧ c = a⁻¹ ∧ d = b⁻¹ := by
  constructor
  · intro he
    obtain ⟨ha, hb⟩ :=
      chartPoint_eq_nonadjacent_nonzero (by fin_cases i <;> decide : i + 3 ≠ i)
        (by fin_cases i <;> decide : i + 3 ≠ i + 1) (by fin_cases i <;> decide : i ≠ (i + 3) + 1)
        he
    have hw : ![c, d] = ![a⁻¹, b⁻¹] :=
      chartPoint_injective (i + 3) (he.symm.trans (chartPoint_offset_three i a b ha hb).symm)
    exact ⟨ha, hb, congrFun hw 0, congrFun hw 1⟩
  · rintro ⟨ha, hb, hc, hd⟩
    subst c d
    exact (chartPoint_offset_three i a b ha hb).symm

private theorem CuspHoneycombHexagon.chartPoint_eq_offset_four_iff (i : Fin 6) (a b c d : ℂ) :
    chartPoint i ![a, b] = chartPoint (i + 4) ![c, d] ↔ a ≠ 0 ∧ b ≠ 0 ∧ c = (a * b)⁻¹ ∧ d = a := by
  constructor
  · intro he
    obtain ⟨ha, hb⟩ :=
      chartPoint_eq_nonadjacent_nonzero (by fin_cases i <;> decide : i + 4 ≠ i)
        (by fin_cases i <;> decide : i + 4 ≠ i + 1) (by fin_cases i <;> decide : i ≠ (i + 4) + 1)
        he
    have hw : ![c, d] = ![(a * b)⁻¹, a] :=
      chartPoint_injective (i + 4) (he.symm.trans (chartPoint_offset_four i a b ha hb).symm)
    exact ⟨ha, hb, congrFun hw 0, congrFun hw 1⟩
  · rintro ⟨ha, hb, hc, hd⟩
    subst c d
    exact (chartPoint_offset_four i a b ha hb).symm

private theorem CuspHoneycombHexagon.unitSquare_mul_eq_one_iff {a b : ℝ} (ha : a ∈ Set.Icc 0 1)
    (hb : b ∈ Set.Icc 0 1) : a * b = 1 ↔ a = 1 ∧ b = 1 := by
  constructor
  · intro h
    have hab : a * b ≤ a := mul_le_of_le_one_right ha.1 hb.2
    have hba : a * b ≤ b := mul_le_of_le_one_left hb.1 ha.2
    rw [h] at hab hba
    exact ⟨le_antisymm ha.2 hab, le_antisymm hb.2 hba⟩
  · rintro ⟨rfl, rfl⟩
    exact one_mul 1

private theorem CuspHoneycombHexagon.unitSquare_inv_iff {a b : ℝ} (ha : a ∈ Set.Icc 0 1)
    (hb : b ∈ Set.Icc 0 1) : ((a : ℂ) ≠ 0 ∧ (b : ℂ) = (a : ℂ)⁻¹) ↔ a = 1 ∧ b = 1 := by
  constructor
  · rintro ⟨ha0, hbInv⟩
    have hC : (a : ℂ) * (b : ℂ) = 1 := by rw [hbInv, mul_inv_cancel₀ ha0]
    apply (unitSquare_mul_eq_one_iff ha hb).mp
    exact_mod_cast hC
  · rintro ⟨rfl, rfl⟩
    simp

private theorem CuspHoneycombHexagon.unitSquare_inv_mul_iff {a b c : ℝ} (ha : a ∈ Set.Icc 0 1)
    (hb : b ∈ Set.Icc 0 1) (hc : c ∈ Set.Icc 0 1) :
    ((a : ℂ) ≠ 0 ∧ (b : ℂ) ≠ 0 ∧ (c : ℂ) = ((a : ℂ) * (b : ℂ))⁻¹) ↔ a = 1 ∧ b = 1 ∧ c = 1 := by
  constructor
  · rintro ⟨ha0, hb0, hcInv⟩
    have hab : a * b ∈ Set.Icc 0 1 :=
      ⟨mul_nonneg ha.1 hb.1, (mul_le_of_le_one_right ha.1 hb.2).trans ha.2⟩
    have hmul : a * b = 1 ∧ c = 1 :=
      (unitSquare_inv_iff hab hc).mp
        ⟨by simpa only [Complex.ofReal_mul] using mul_ne_zero ha0 hb0, by
          simpa only [Complex.ofReal_mul] using hcInv⟩
    obtain ⟨ha1, hb1⟩ := (unitSquare_mul_eq_one_iff ha hb).mp hmul.1
    exact ⟨ha1, hb1, hmul.2⟩
  · rintro ⟨rfl, rfl, rfl⟩
    simp

private theorem
    CuspHoneycombHexagon.unitSquare_transition_one_iff {a b c d : ℝ} (ha : a ∈ Set.Icc 0 1)
    (hd : d ∈ Set.Icc 0 1) :
    ((a : ℂ) ≠ 0 ∧ (c : ℂ) = (a : ℂ) * (b : ℂ) ∧ (d : ℂ) = (a : ℂ)⁻¹) ↔ a = 1 ∧ c = b ∧ d = 1 := by
  constructor
  · rintro ⟨ha0, hc, hdInv⟩
    obtain ⟨ha1, hd1⟩ := (unitSquare_inv_iff ha hd).mp ⟨ha0, hdInv⟩
    refine ⟨ha1, ?_, hd1⟩
    exact_mod_cast (show (c : ℂ) = (b : ℂ) by simpa [ha1] using hc)
  · rintro ⟨rfl, rfl, rfl⟩
    simp

private theorem
    CuspHoneycombHexagon.unitSquare_transition_two_iff {a b c d : ℝ} (ha : a ∈ Set.Icc 0 1)
    (hb : b ∈ Set.Icc 0 1) (hd : d ∈ Set.Icc 0 1) :
    ((a : ℂ) ≠ 0 ∧ (b : ℂ) ≠ 0 ∧ (c : ℂ) = (b : ℂ) ∧ (d : ℂ) = ((a : ℂ) * (b : ℂ))⁻¹) ↔
      a = 1 ∧ b = 1 ∧ c = 1 ∧ d = 1 := by
  constructor
  · rintro ⟨ha0, hb0, hc, hdInv⟩
    obtain ⟨ha1, hb1, hd1⟩ := (unitSquare_inv_mul_iff ha hb hd).mp ⟨ha0, hb0, hdInv⟩
    refine ⟨ha1, hb1, ?_, hd1⟩
    exact_mod_cast (show (c : ℂ) = 1 by simpa [hb1] using hc)
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    simp

private theorem
    CuspHoneycombHexagon.unitSquare_transition_three_iff {a b c d : ℝ} (ha : a ∈ Set.Icc 0 1)
    (hb : b ∈ Set.Icc 0 1) (hc : c ∈ Set.Icc 0 1) (hd : d ∈ Set.Icc 0 1) :
    ((a : ℂ) ≠ 0 ∧ (b : ℂ) ≠ 0 ∧ (c : ℂ) = (a : ℂ)⁻¹ ∧ (d : ℂ) = (b : ℂ)⁻¹) ↔
      a = 1 ∧ b = 1 ∧ c = 1 ∧ d = 1 := by
  constructor
  · rintro ⟨ha0, hb0, hcInv, hdInv⟩
    obtain ⟨ha1, hc1⟩ := (unitSquare_inv_iff ha hc).mp ⟨ha0, hcInv⟩
    obtain ⟨hb1, hd1⟩ := (unitSquare_inv_iff hb hd).mp ⟨hb0, hdInv⟩
    exact ⟨ha1, hb1, hc1, hd1⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    simp

private theorem
    CuspHoneycombHexagon.unitSquare_transition_four_iff {a b c d : ℝ} (ha : a ∈ Set.Icc 0 1)
    (hb : b ∈ Set.Icc 0 1) (hc : c ∈ Set.Icc 0 1) :
    ((a : ℂ) ≠ 0 ∧ (b : ℂ) ≠ 0 ∧ (c : ℂ) = ((a : ℂ) * (b : ℂ))⁻¹ ∧ (d : ℂ) = (a : ℂ)) ↔
      a = 1 ∧ b = 1 ∧ c = 1 ∧ d = 1 := by
  constructor
  · rintro ⟨ha0, hb0, hcInv, hd⟩
    obtain ⟨ha1, hb1, hc1⟩ := (unitSquare_inv_mul_iff ha hb hc).mp ⟨ha0, hb0, hcInv⟩
    refine ⟨ha1, hb1, hc1, ?_⟩
    exact_mod_cast (show (d : ℂ) = 1 by simpa [ha1] using hd)
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    simp

private theorem
    CuspHoneycombHexagon.unitSquare_transition_five_iff {a b c d : ℝ} (hb : b ∈ Set.Icc 0 1)
    (hc : c ∈ Set.Icc 0 1) :
    ((b : ℂ) ≠ 0 ∧ (c : ℂ) = (b : ℂ)⁻¹ ∧ (d : ℂ) = (a : ℂ) * (b : ℂ)) ↔ b = 1 ∧ c = 1 ∧ d = a := by
  constructor
  · rintro ⟨hb0, hcInv, hd⟩
    obtain ⟨hb1, hc1⟩ := (unitSquare_inv_iff hb hc).mp ⟨hb0, hcInv⟩
    refine ⟨hb1, hc1, ?_⟩
    exact_mod_cast (show (d : ℂ) = (a : ℂ) by simpa [hb1] using hd)
  · rintro ⟨rfl, rfl, rfl⟩
    simp

private theorem CuspHoneycombHexagon.squareComplexCoordinates_vector (p : Square) :
    (fun k : Fin 2 => (p.1 k : ℂ)) = ![(p.1 0 : ℂ), (p.1 1 : ℂ)] := by
  ext k
  fin_cases k <;> rfl

private theorem CuspHoneycombHexagon.squareComplexCoordinates_injective :
    Function.Injective (fun p : Square => fun k : Fin 2 => (p.1 k : ℂ)) := by
  intro p q h
  apply Subtype.ext
  funext k
  exact Complex.ofReal_injective (congrFun h k)

private theorem CuspHoneycombHexagon.chartPoint_square_eq_iff (i j : Fin 6) (p q : Square) :
    chartPoint i (fun k => (p.1 k : ℂ)) = chartPoint j (fun k => (q.1 k : ℂ)) ↔
      SquareRel i j p q := by
  obtain ⟨k, rfl⟩ : ∃ k : Fin 6, j = i + k := ⟨j - i, by rw [add_comm i (j - i), sub_add_cancel]⟩
  fin_cases k
  · change
      chartPoint i (fun k => (p.1 k : ℂ)) = chartPoint (i + 0) (fun k => (q.1 k : ℂ)) ↔
        SquareRel i (i + 0) p q
    rw [add_zero, squareRel_self]
    exact ((chartPoint_injective i).comp squareComplexCoordinates_injective).eq_iff
  · change
      chartPoint i (fun k => (p.1 k : ℂ)) = chartPoint (i + 1) (fun k => (q.1 k : ℂ)) ↔
        SquareRel i (i + 1) p q
    rw [squareComplexCoordinates_vector p, squareComplexCoordinates_vector q,
      chartPoint_eq_next_iff, squareRel_next]
    simpa only [and_assoc, and_comm, and_left_comm] using
      (unitSquare_transition_one_iff (a := p.1 0) (b := p.1 1) (c := q.1 0) (d := q.1 1) (p.2 0)
        (q.2 1))
  · change
      chartPoint i (fun k => (p.1 k : ℂ)) = chartPoint (i + 2) (fun k => (q.1 k : ℂ)) ↔
        SquareRel i (i + 2) p q
    rw [squareComplexCoordinates_vector p, squareComplexCoordinates_vector q,
      chartPoint_eq_offset_two_iff, squareRel_add_two]
    simpa only [Fin.forall_fin_two, and_assoc] using
      (unitSquare_transition_two_iff (a := p.1 0) (b := p.1 1) (c := q.1 0) (d := q.1 1) (p.2 0)
        (p.2 1) (q.2 1))
  · change
      chartPoint i (fun k => (p.1 k : ℂ)) = chartPoint (i + 3) (fun k => (q.1 k : ℂ)) ↔
        SquareRel i (i + 3) p q
    rw [squareComplexCoordinates_vector p, squareComplexCoordinates_vector q,
      chartPoint_eq_offset_three_iff, squareRel_add_three]
    simpa only [Fin.forall_fin_two, and_assoc] using
      (unitSquare_transition_three_iff (a := p.1 0) (b := p.1 1) (c := q.1 0) (d := q.1 1) (p.2 0)
        (p.2 1) (q.2 0) (q.2 1))
  · change
      chartPoint i (fun k => (p.1 k : ℂ)) = chartPoint (i + 4) (fun k => (q.1 k : ℂ)) ↔
        SquareRel i (i + 4) p q
    rw [squareComplexCoordinates_vector p, squareComplexCoordinates_vector q,
      chartPoint_eq_offset_four_iff, squareRel_add_four]
    simpa only [Fin.forall_fin_two, and_assoc] using
      (unitSquare_transition_four_iff (a := p.1 0) (b := p.1 1) (c := q.1 0) (d := q.1 1) (p.2 0)
        (p.2 1) (q.2 0))
  · change
      chartPoint i (fun k => (p.1 k : ℂ)) = chartPoint (i + 5) (fun k => (q.1 k : ℂ)) ↔
        SquareRel i (i + 5) p q
    rw [squareComplexCoordinates_vector p, squareComplexCoordinates_vector q,
      chartPoint_eq_previous_iff, squareRel_prev]
    exact unitSquare_transition_five_iff (p.2 1) (q.2 0)

private def CuspQuotient.componentBoundary (v : Fin 2 → ℤ) : Set (ToricSpace.rayDivisor 0) :=
  {x | (x : ToricSpace.Space) ∈ ToricSpace.rayDivisor v}

private def CuspHoneycombHexagon.orientedSquare (i : Fin 6) (p : Square) : Square :=
  if i = 1 ∨ i = 2 ∨ i = 3 then ⟨![p.1 1, p.1 0], by intro k; fin_cases k <;> exact p.2 _⟩ else p

@[simp]
private theorem CuspHoneycombHexagon.orientedSquare_involutive (i : Fin 6) (p : Square) :
    orientedSquare i (orientedSquare i p) = p := by
  by_cases hi : i = 1 ∨ i = 2 ∨ i = 3
  · apply Subtype.ext
    funext k
    fin_cases k <;> simp [orientedSquare, hi]
  · simp [orientedSquare, hi]

private theorem CuspHoneycombHexagon.orientedCoordinates_square (i : Fin 6) (p : Square) :
    orientedCoordinates i (fun k => (p.1 k : ℂ)) = fun k => ((orientedSquare i p).1 k : ℂ) := by
  by_cases hi : i = 1 ∨ i = 2 ∨ i = 3
  · funext k
    fin_cases k <;> simp [orientedSquare, orientedCoordinates, hi]
  · simp [orientedSquare, orientedCoordinates, hi]

private def CuspHoneycombHexagon.squarePoint (i : Fin 6) (p : Square) : PositiveE0 :=
  ⟨chartPoint i (fun k => (p.1 k : ℂ)),
    by
    apply (affineInclusion_mem_positive_iff (ToricComponent.zeroChart i) _).mpr
    rw [orientedCoordinates_square]
    exact ⟨(orientedSquare i p).1, fun k => ((orientedSquare i p).2 k).1, rfl⟩⟩

@[simp]
private theorem CuspHoneycombHexagon.squarePoint_coe (i : Fin 6) (p : Square) :
    (squarePoint i p : ToricSpace.rayDivisor 0) = chartPoint i (fun k => (p.1 k : ℂ)) :=
  rfl

private theorem
    CuspHoneycombHexagon.squarePoint_continuous (i : Fin 6) : Continuous (squarePoint i) := by
  have h : Continuous (fun p : Square => fun k => (p.1 k : ℂ)) :=
    continuous_pi fun k =>
      Complex.continuous_ofReal.comp ((continuous_apply k).comp continuous_subtype_val)
  exact ((chartPoint_continuous i).comp h).subtype_mk _

private theorem CuspHoneycombHexagon.squarePoint_eq_iff (i j : Fin 6) (p q : Square) :
    squarePoint i p = squarePoint j q ↔ SquareRel i j p q := by
  rw [← chartPoint_square_eq_iff]
  exact Subtype.ext_iff

private theorem CuspHoneycombHexagon.squarePoint_jointly_surjective (x : PositiveE0) :
    ∃ (i : Fin 6) (p : Square), squarePoint i p = x := by
  obtain ⟨i, r, hr, he⟩ := positiveE0_bounded_chart x
  let p : Square := ⟨r.1, fun k => ⟨r.2 k, hr k⟩⟩
  refine ⟨i, orientedSquare i p, Subtype.ext ?_⟩
  change
    ToricComponent.affineInclusion (ToricComponent.zeroChart i)
        (orientedCoordinates i (fun k => ((orientedSquare i p).1 k : ℂ))) =
      x.1
  rw [orientedCoordinates_square, orientedSquare_involutive]
  exact congrArg Subtype.val he

private abbrev CuspHoneycombHexagon.TileSpace :=
  Fin 6 × Square

private def CuspHoneycombHexagon.squareProjection (p : TileSpace) : PositiveE0 :=
  squarePoint p.1 p.2

private theorem CuspHoneycombHexagon.squareProjection_continuous : Continuous squareProjection :=
  continuous_prod_of_discrete_left.mpr squarePoint_continuous

private theorem
    CuspHoneycombHexagon.squareProjection_surjective : Function.Surjective squareProjection :=
  by
  intro x
  obtain ⟨i, p, hp⟩ := squarePoint_jointly_surjective x
  exact ⟨(i, p), hp⟩

private def CuspHoneycombHexagon.positiveBoundary (k : Fin 6) : Set PositiveE0 :=
  Subtype.val ⁻¹' CuspQuotient.componentBoundary (ToricComponent.hexagonRay k)

private theorem
    CuspHoneycombHexagon.squarePoint_mem_positiveBoundary_iff (i k : Fin 6) (p : Square) :
    squarePoint i p ∈ positiveBoundary k ↔ (k = i ∧ p.1 0 = 0) ∨ (k = i + 1 ∧ p.1 1 = 0) := by
  change
    (chartPoint i (fun j => (p.1 j : ℂ)) : ToricSpace.Space) ∈
        ToricSpace.rayDivisor (ToricComponent.hexagonRay k) ↔
      _
  rw [chartPoint_mem_rayDivisor_iff]
  simp

private def CuspHoneycombHexagon.polygonProjection (p : TileSpace) : Hexagon :=
  ⟨tile p.1 p.2, tile_mem_hexagon p.1 p.2⟩

private theorem CuspHoneycombHexagon.polygonProjection_continuous : Continuous polygonProjection :=
  (continuous_prod_of_discrete_left.mpr tile_continuous).subtype_mk _

private theorem CuspHoneycombHexagon.polygonProjection_surjective :
    Function.Surjective polygonProjection := by
  intro x
  obtain ⟨i, p, hp⟩ := tile_jointly_surjective x
  exact ⟨(i, p), Subtype.ext hp⟩

private theorem
    CuspHoneycombHexagon.squareProjection_eq_iff_polygonProjection_eq (a b : TileSpace) :
    squareProjection a = squareProjection b ↔ polygonProjection a = polygonProjection b := by
  change squarePoint a.1 a.2 = squarePoint b.1 b.2 ↔ _
  rw [squarePoint_eq_iff, Subtype.ext_iff]
  exact (tile_eq_iff a.1 b.1 a.2 b.2).symm

private def CuspHoneycombHexagon.positiveE0HexagonHomeomorph : PositiveE0 ≃ₜ Hexagon :=
  CommonFibres.homeomorph squareProjection polygonProjection squareProjection_surjective
    squareProjection_continuous polygonProjection_continuous polygonProjection_surjective
    squareProjection_eq_iff_polygonProjection_eq

@[simp]
private theorem
    CuspHoneycombHexagon.positiveE0HexagonHomeomorph_squarePoint (i : Fin 6) (p : Square) :
    (positiveE0HexagonHomeomorph (squarePoint i p) : Plane) = tile i p := by
  exact
    congrArg Subtype.val
      (CommonFibres.homeomorph_apply squareProjection polygonProjection
        squareProjection_surjective squareProjection_continuous polygonProjection_continuous
        polygonProjection_surjective squareProjection_eq_iff_polygonProjection_eq (i, p))

private theorem CuspHoneycombHexagon.positiveE0HexagonHomeomorph_cornerZero (i : Fin 6) :
    (positiveE0HexagonHomeomorph (squarePoint i cornerZero) : Plane) = vertex i := by simp

private theorem CuspHoneycombHexagon.squarePoint_cornerZero_coe (i : Fin 6) :
    ((squarePoint i cornerZero : ToricSpace.rayDivisor 0) : ToricSpace.Space) =
      ToricSpace.inclusion (ToricComponent.zeroTriangle i) 0 := by
  rw [squarePoint_coe, chartPoint_coe]
  congr 1
  ext k
  rcases coordinates_exhaustive i k with rfl | rfl | rfl <;> simp [cornerZero]

private theorem CuspHoneycombHexagon.squarePoint_cornerZero_mem_positiveBoundary_iff (i k : Fin 6) :
    squarePoint i cornerZero ∈ positiveBoundary k ↔ k = i ∨ k = i + 1 := by
  rw [squarePoint_mem_positiveBoundary_iff]
  simp [cornerZero]

private theorem CuspHoneycombHexagon.positiveE0HexagonHomeomorph_mem_side_iff (x : PositiveE0)
    (k : Fin 6) : (positiveE0HexagonHomeomorph x : Plane) ∈ side k ↔ x ∈ positiveBoundary k := by
  obtain ⟨i, p, rfl⟩ := squarePoint_jointly_surjective x
  rw [positiveE0HexagonHomeomorph_squarePoint, tile_mem_side_iff,
    squarePoint_mem_positiveBoundary_iff]

private theorem CuspHoneycombHexagon.positiveE0HexagonHomeomorph_mem_boundary_iff (x : PositiveE0) :
    (positiveE0HexagonHomeomorph x : Plane) ∈ ⋃ k, side k ↔ x ∈ ⋃ k, positiveBoundary k := by
  simp only [Set.mem_iUnion]
  exact exists_congr (fun k => positiveE0HexagonHomeomorph_mem_side_iff x k)

private def CuspHoneycombHexagon.positiveBoundaryHexagonHomeomorph (k : Fin 6) :
    positiveBoundary k ≃ₜ side k
    where
  toFun
    x :=
    ⟨(positiveE0HexagonHomeomorph x.1 : Plane),
      (positiveE0HexagonHomeomorph_mem_side_iff x.1 k).mpr x.2⟩
  invFun
    y :=
    ⟨positiveE0HexagonHomeomorph.symm ⟨y.1, y.2.1⟩,
      by
      apply (positiveE0HexagonHomeomorph_mem_side_iff _ k).mp
      simpa only [Homeomorph.apply_symm_apply] using y.2⟩
  left_inv x := Subtype.ext (positiveE0HexagonHomeomorph.symm_apply_apply x.1)
  right_inv
    y := by
    apply Subtype.ext
    change
      (positiveE0HexagonHomeomorph (positiveE0HexagonHomeomorph.symm ⟨y.1, y.2.1⟩) : Plane) = y.1
    rw [Homeomorph.apply_symm_apply]
  continuous_toFun :=
    (continuous_subtype_val.comp
          (positiveE0HexagonHomeomorph.continuous.comp continuous_subtype_val)).subtype_mk
      _
  continuous_invFun :=
    (positiveE0HexagonHomeomorph.symm.continuous.comp
          (continuous_subtype_val.subtype_mk _)).subtype_mk
      _

private theorem CuspHoneycombHexagon.sideFunctional_continuous (k : Fin 6) :
    Continuous (sideFunctional k) := by fin_cases k <;> unfold sideFunctional <;> fun_prop

private theorem CuspHoneycombHexagon.sideFunctional_add (k : Fin 6) (x y : Plane) :
    sideFunctional k (x + y) = sideFunctional k x + sideFunctional k y := by
  fin_cases k <;> simp [sideFunctional] <;> ring

private theorem CuspHoneycombHexagon.sideFunctional_smul (k : Fin 6) (a : ℝ) (x : Plane) :
    sideFunctional k (a • x) = a * sideFunctional k x := by
  fin_cases k <;> simp [sideFunctional] <;> ring

private theorem CuspHoneycombHexagon.mem_hexagon_iff_sideFunctional_le (x : Plane) :
    x ∈ Hexagon ↔ ∀ k : Fin 6, sideFunctional k x ≤ 1 := by
  constructor
  · rintro ⟨hx, hy, hxy⟩ k
    have hx' := abs_le.mp hx
    have hy' := abs_le.mp hy
    have hxy' := abs_le.mp hxy
    fin_cases k
    · exact hx'.2
    · exact hxy'.2
    · exact hy'.2
    · change -x 0 ≤ 1
      linarith [hx'.1]
    · change -x 0 - x 1 ≤ 1
      linarith [hxy'.1]
    · change -x 1 ≤ 1
      linarith [hy'.1]
  · intro h
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    have h3 := h 3
    have h4 := h 4
    have h5 := h 5
    simp only [sideFunctional_zero, sideFunctional_one, sideFunctional_two, sideFunctional_three,
      sideFunctional_four, sideFunctional_five] at h0 h1 h2 h3 h4 h5
    exact
      ⟨abs_le.mpr ⟨by linarith, h0⟩, abs_le.mpr ⟨by linarith, h2⟩, abs_le.mpr ⟨by linarith, h1⟩⟩

private theorem CuspHoneycombHexagon.hexagon_convex : Convex ℝ Hexagon := by
  intro x hx y hy a b ha hb hab
  apply (mem_hexagon_iff_sideFunctional_le _).mpr
  intro k
  rw [sideFunctional_add, sideFunctional_smul, sideFunctional_smul]
  calc
    a * sideFunctional k x + b * sideFunctional k y ≤ a * 1 + b * 1 :=
      add_le_add (mul_le_mul_of_nonneg_left ((mem_hexagon_iff_sideFunctional_le x).mp hx k) ha)
        (mul_le_mul_of_nonneg_left ((mem_hexagon_iff_sideFunctional_le y).mp hy k) hb)
    _ = 1 := by simpa only [mul_one] using hab

private theorem CuspHoneycombHexagon.hexagon_isClosed : IsClosed Hexagon := by
  have he : Hexagon = ⋂ k : Fin 6, {x | sideFunctional k x ≤ 1} := by
    ext x
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, mem_hexagon_iff_sideFunctional_le]
  rw [he]
  exact isClosed_iInter fun k => isClosed_le (sideFunctional_continuous k) continuous_const

private theorem CuspHoneycombHexagon.hexagon_subset_closedBall :
    Hexagon ⊆ Metric.closedBall (0 : Plane) 1 := by
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num)).mpr
  intro i
  fin_cases i
  · exact hx.1
  · exact hx.2.1

private theorem CuspHoneycombHexagon.hexagon_isCompact : IsCompact Hexagon :=
  (ProperSpace.isCompact_closedBall (0 : Plane) 1).of_isClosed_subset hexagon_isClosed
    hexagon_subset_closedBall

private theorem CuspHoneycombHexagon.hexagon_isBounded : Bornology.IsBounded Hexagon :=
  hexagon_isCompact.isBounded

private theorem CuspHoneycombHexagon.ball_half_subset_hexagon :
    Metric.ball (0 : Plane) (1 / 2) ⊆ Hexagon := by
  intro x hx
  have hn : ‖x‖ < 1 / 2 := by simpa only [Metric.mem_ball, dist_zero_right] using hx
  have h0 : |x 0| ≤ ‖x‖ := norm_le_pi_norm x 0
  have h1 : |x 1| ≤ ‖x‖ := norm_le_pi_norm x 1
  have hsum := abs_add_le (x 0) (x 1)
  exact ⟨by linarith, by linarith, by linarith⟩

private theorem CuspHoneycombHexagon.hexagon_mem_nhds_zero : Hexagon ∈ 𝓝 (0 : Plane) :=
  Filter.mem_of_superset (Metric.ball_mem_nhds _ (by norm_num)) ball_half_subset_hexagon

private theorem CuspHoneycombHexagon.zero_mem_interior_hexagon : (0 : Plane) ∈ interior Hexagon :=
  mem_interior_iff_mem_nhds.mpr hexagon_mem_nhds_zero

private theorem CuspHoneycombHexagon.hexagon_interior_nonempty : (interior Hexagon).Nonempty :=
  ⟨0, zero_mem_interior_hexagon⟩

private theorem CuspHoneycombHexagon.mem_interior_hexagon_iff (x : Plane) :
    x ∈ interior Hexagon ↔ ∀ k : Fin 6, sideFunctional k x < 1 := by
  constructor
  · intro hx k
    have hle := (mem_hexagon_iff_sideFunctional_le x).mp (interior_subset hx) k
    apply lt_of_le_of_ne hle
    intro heq
    have hopen : IsOpen ((fun a : ℝ => a • x) ⁻¹' interior Hexagon) :=
      isOpen_interior.preimage (continuous_id.smul continuous_const)
    have hone : (1 : ℝ) ∈ (fun a : ℝ => a • x) ⁻¹' interior Hexagon := by
      simpa only [Set.mem_preimage, one_smul] using hx
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hopen 1 hone
    have ha : (1 + δ / 2) • x ∈ interior Hexagon :=
      hball
        (by
          change Dist.dist (1 + δ / 2) (1 : ℝ) < δ
          rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos (half_pos hδ)]
          exact half_lt_self hδ)
    have hb := (mem_hexagon_iff_sideFunctional_le _).mp (interior_subset ha) k
    rw [sideFunctional_smul, heq, mul_one] at hb
    linarith
  · intro hx
    let U : Set Plane := ⋂ k : Fin 6, {y | sideFunctional k y < 1}
    have hU : IsOpen U :=
      isOpen_iInter_of_finite fun k => isOpen_lt (sideFunctional_continuous k) continuous_const
    have hxU : x ∈ U := Set.mem_iInter.mpr hx
    have hUK : U ⊆ Hexagon := by
      intro y hy
      apply (mem_hexagon_iff_sideFunctional_le y).mpr
      intro k
      exact (Set.mem_iInter.mp hy k).le
    exact mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (hU.mem_nhds hxU) hUK)

private theorem CuspHoneycombHexagon.frontier_hexagon : frontier Hexagon = ⋃ k : Fin 6, side k := by
  ext x
  rw [frontier, hexagon_isClosed.closure_eq, Set.mem_sdiff, mem_interior_hexagon_iff,
    Set.mem_iUnion]
  constructor
  · rintro ⟨hx, hn⟩
    push Not at hn
    obtain ⟨k, hk⟩ := hn
    exact ⟨k, hx, le_antisymm ((mem_hexagon_iff_sideFunctional_le x).mp hx k) hk⟩
  · rintro ⟨k, hx, hk⟩
    exact ⟨hx, fun h => (h k).ne hk⟩

private abbrev CuspHoneycombRadial.UnitSphere (E : Type*) [NormedAddCommGroup E] :=
  Metric.sphere (0 : E) (1 : ℝ)

private theorem CuspHoneycombRadial.unitSphere_norm {E : Type*} [NormedAddCommGroup E]
    (x : UnitSphere E) : ‖(x : E)‖ = 1 :=
  mem_sphere_zero_iff_norm.mp x.2

private theorem CuspHoneycombRadial.unitSphere_ne_zero {E : Type*} [NormedAddCommGroup E]
    (x : UnitSphere E) : (x : E) ≠ 0 :=
  norm_ne_zero_iff.mp (by rw [unitSphere_norm]; exact one_ne_zero)

private def CuspHoneycombRadial.direction {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : { x : E // x ≠ 0 }) : UnitSphere E :=
  ⟨NormedSpace.normalize x.1, mem_sphere_zero_iff_norm.mpr (NormedSpace.norm_normalize x.2)⟩

private theorem CuspHoneycombRadial.direction_continuous {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] : Continuous (direction (E := E)) := by
  apply Continuous.subtype_mk
  exact
    (continuous_subtype_val.norm.inv₀
          (fun x : { x : E // x ≠ 0 } => norm_ne_zero_iff.mpr x.2)).smul
      continuous_subtype_val

private theorem CuspHoneycombRadial.norm_smul_direction {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (x : { x : E // x ≠ 0 }) : ‖x.1‖ • (direction x : E) = x.1 :=
  NormedSpace.norm_smul_normalize x.1

private theorem
    CuspHoneycombRadial.direction_sphere {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : UnitSphere E) (hx : (x : E) ≠ 0) : direction ⟨(x : E), hx⟩ = x :=
  Subtype.ext (NormedSpace.normalize_eq_self_of_norm_eq_one (unitSphere_norm x))

private def CuspHoneycombRadial.radialOffZero_mo1973_11510 {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (e : UnitSphere E ≃ₜ UnitSphere E) (x : { x : E // x ≠ 0 }) : E :=
  ‖x.1‖ • (e (direction x) : E)

private theorem CuspHoneycombRadial.radialOffZero_continuous_mo1973_11511 {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (e : UnitSphere E ≃ₜ UnitSphere E) :
    Continuous (radialOffZero_mo1973_11510 e) :=
  continuous_subtype_val.norm.smul
    (continuous_subtype_val.comp (e.continuous.comp direction_continuous))

private def CuspHoneycombRadial.radialMap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : UnitSphere E ≃ₜ UnitSphere E) (x : E) : E := by
  classical exact if hx : x = 0 then 0 else radialOffZero_mo1973_11510 e ⟨x, hx⟩

@[simp]
private theorem
    CuspHoneycombRadial.radialMap_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : UnitSphere E ≃ₜ UnitSphere E) : radialMap e (0 : E) = 0 := by simp [radialMap]

private theorem CuspHoneycombRadial.radialMap_apply_of_ne_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (e : UnitSphere E ≃ₜ UnitSphere E) {x : E} (hx : x ≠ 0) :
    radialMap e x = ‖x‖ • (e (direction ⟨x, hx⟩) : E) := by
  simp only [radialMap, dite_eq_right hx, radialOffZero_mo1973_11510]

@[simp]
private theorem
    CuspHoneycombRadial.radialMap_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : UnitSphere E ≃ₜ UnitSphere E) (x : E) : ‖radialMap e x‖ = ‖x‖ := by
  by_cases hx : x = 0
  · simp only [hx, radialMap_zero]
  · rw [radialMap_apply_of_ne_zero e hx, norm_smul, norm_norm, unitSphere_norm, mul_one]

@[simp]
private theorem CuspHoneycombRadial.radialMap_eq_zero_iff {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (e : UnitSphere E ≃ₜ UnitSphere E) (x : E) : radialMap e x = 0 ↔ x = 0 := by
  constructor
  · intro h
    apply norm_eq_zero.mp
    rw [← radialMap_norm e x, h, norm_zero]
  · rintro rfl
    exact radialMap_zero e

private theorem
    CuspHoneycombRadial.radialMap_ne_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : UnitSphere E ≃ₜ UnitSphere E) {x : E} (hx : x ≠ 0) : radialMap e x ≠ 0 := fun h =>
  hx ((radialMap_eq_zero_iff e x).mp h)

private theorem CuspHoneycombRadial.direction_radialMap {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (e : UnitSphere E ≃ₜ UnitSphere E) {x : E} (hx : x ≠ 0) :
    direction ⟨radialMap e x, radialMap_ne_zero e hx⟩ = e (direction ⟨x, hx⟩) := by
  apply Subtype.ext
  change ‖radialMap e x‖⁻¹ • radialMap e x = (e (direction ⟨x, hx⟩) : E)
  rw [radialMap_norm, radialMap_apply_of_ne_zero e hx, smul_smul,
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx), one_smul]

private theorem
    CuspHoneycombRadial.radialMap_sphere {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : UnitSphere E ≃ₜ UnitSphere E) (x : UnitSphere E) : radialMap e (x : E) = (e x : E) := by
  rw [radialMap_apply_of_ne_zero e (unitSphere_ne_zero x), unitSphere_norm, direction_sphere,
    one_smul]

private theorem
    CuspHoneycombRadial.radialMap_symm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : UnitSphere E ≃ₜ UnitSphere E) (x : E) : radialMap e.symm (radialMap e x) = x := by
  by_cases hx : x = 0
  · simp only [hx, radialMap_zero]
  · rw [radialMap_apply_of_ne_zero e.symm (radialMap_ne_zero e hx), radialMap_norm,
      direction_radialMap e hx, e.symm_apply_apply]
    exact norm_smul_direction ⟨x, hx⟩

private theorem CuspHoneycombRadial.radialMap_continuousAt_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (e : UnitSphere E ≃ₜ UnitSphere E) : ContinuousAt (radialMap e) (0 : E) := by
  change Filter.Tendsto (radialMap e) (𝓝 (0 : E)) (𝓝 (radialMap e 0))
  rw [radialMap_zero]
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have h : Filter.Tendsto (fun x : E => ‖x‖) (𝓝 (0 : E)) (𝓝 (0 : ℝ)) := by
    simpa only [norm_zero] using (continuous_norm.tendsto (0 : E))
  simpa only [radialMap_norm] using h

private theorem
    CuspHoneycombRadial.radialMap_continuousOn_nonzero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (e : UnitSphere E ≃ₜ UnitSphere E) :
    ContinuousOn (radialMap e) {x : E | x ≠ 0} := by
  rw [continuousOn_iff_continuous_domRestrict]
  exact
    (radialOffZero_continuous_mo1973_11511 e).congr
      (fun x : { x : E // x ≠ 0 } => (radialMap_apply_of_ne_zero e x.2).symm)

private theorem CuspHoneycombRadial.radialMap_continuous {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (e : UnitSphere E ≃ₜ UnitSphere E) : Continuous (radialMap e) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    exact radialMap_continuousAt_zero e
  · exact
      (radialMap_continuousOn_nonzero e).continuousAt
        ((isOpen_ne_fun continuous_id continuous_const).mem_nhds hx)

private def
    CuspHoneycombRadial.radialHomeomorph {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : UnitSphere E ≃ₜ UnitSphere E) : E ≃ₜ E
    where
  toFun := radialMap e
  invFun := radialMap e.symm
  left_inv := radialMap_symm e
  right_inv := radialMap_symm e.symm
  continuous_toFun := radialMap_continuous e
  continuous_invFun := radialMap_continuous e.symm

@[simp]
private theorem CuspHoneycombRadial.radialHomeomorph_norm {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (e : UnitSphere E ≃ₜ UnitSphere E) (x : E) : ‖radialHomeomorph e x‖ = ‖x‖ :=
  radialMap_norm e x

private theorem CuspHoneycombRadial.radialHomeomorph_sphere {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (e : UnitSphere E ≃ₜ UnitSphere E) (x : UnitSphere E) :
    radialHomeomorph e (x : E) = (e x : E) :=
  radialMap_sphere e x

private theorem CuspHoneycombRadial.homeomorph_mem_image_iff_mo1973_11532 {E : Type*}
    [NormedAddCommGroup E] (H : E ≃ₜ E) {S T : Set E} (hST : H '' S = T) (x : E) :
    x ∈ S ↔ H x ∈ T := by
  rw [← hST]
  exact H.injective.mem_set_image.symm

private theorem CuspHoneycombRadial.homeomorph_image_eq_of_mem_iff_mo1973_11533 {E : Type*}
    [NormedAddCommGroup E] (F : E ≃ₜ E) {K : Set E} (hmem : ∀ x, F x ∈ K ↔ x ∈ K) : F '' K = K := by
  apply Set.Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact (hmem x).mpr hx
  · intro y hy
    refine ⟨F.symm y, ?_, F.apply_symm_apply y⟩
    apply (hmem (F.symm y)).mp
    rwa [F.apply_symm_apply]

public
theorem CuspHoneycombRadial.exists_homeomorph_extending_frontier {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Set E} (hconv : Convex ℝ K)
    (hclosed : IsClosed K) (hbounded : Bornology.IsBounded K) (hne : (interior K).Nonempty)
    (e : frontier K ≃ₜ frontier K) :
    ∃ F : E ≃ₜ E, F '' K = K ∧ ∀ x : frontier K, F (x : E) = (e x : E) := by
  obtain ⟨H, _hinterior, hclosure, hfrontier⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall hconv hne hbounded
  have hK : H '' K = Metric.closedBall (0 : E) 1 := by
    simpa only [hclosed.closure_eq] using hclosure
  let HB : frontier K ≃ₜ UnitSphere E :=
    H.subtype (homeomorph_mem_image_iff_mo1973_11532 H hfrontier)
  let eS : UnitSphere E ≃ₜ UnitSphere E := HB.symm.trans (e.trans HB)
  let F : E ≃ₜ E := H.trans ((radialHomeomorph eS).trans H.symm)
  have hmemF (x : E) : F x ∈ K ↔ x ∈ K := by
    rw [homeomorph_mem_image_iff_mo1973_11532 H hK (F x),
      homeomorph_mem_image_iff_mo1973_11532 H hK x]
    change
      H (H.symm (radialHomeomorph eS (H x))) ∈ Metric.closedBall (0 : E) 1 ↔
        H x ∈ Metric.closedBall (0 : E) 1
    rw [H.apply_symm_apply]
    simp only [Metric.mem_closedBall, dist_zero_right, radialHomeomorph_norm]
  refine ⟨F, homeomorph_image_eq_of_mem_iff_mo1973_11533 F hmemF, ?_⟩
  intro x
  change H.symm (radialHomeomorph eS (HB x : E)) = (e x : E)
  rw [radialHomeomorph_sphere]
  change H.symm (HB (e (HB.symm (HB x))) : E) = (e x : E)
  rw [HB.symm_apply_apply]
  exact H.symm_apply_apply (e x : E)

private def
    CuspHoneycombRadial.boundaryExtension {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} (hconv : Convex ℝ K) (hclosed : IsClosed K) (hbounded : Bornology.IsBounded K)
    (hne : (interior K).Nonempty) (e : frontier K ≃ₜ frontier K) : E ≃ₜ E :=
  (exists_homeomorph_extending_frontier hconv hclosed hbounded hne e).choose

private theorem CuspHoneycombRadial.boundaryExtension_image {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {K : Set E} (hconv : Convex ℝ K) (hclosed : IsClosed K)
    (hbounded : Bornology.IsBounded K) (hne : (interior K).Nonempty)
    (e : frontier K ≃ₜ frontier K) : boundaryExtension hconv hclosed hbounded hne e '' K = K :=
  (exists_homeomorph_extending_frontier hconv hclosed hbounded hne e).choose_spec.1

private theorem CuspHoneycombRadial.boundaryExtension_frontier {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {K : Set E} (hconv : Convex ℝ K) (hclosed : IsClosed K)
    (hbounded : Bornology.IsBounded K) (hne : (interior K).Nonempty)
    (e : frontier K ≃ₜ frontier K) (x : frontier K) :
    boundaryExtension hconv hclosed hbounded hne e (x : E) = (e x : E) :=
  (exists_homeomorph_extending_frontier hconv hclosed hbounded hne e).choose_spec.2 x

private def
    CuspHoneycombRadial.boundarySetExtension {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} (hconv : Convex ℝ K) (hclosed : IsClosed K) (hbounded : Bornology.IsBounded K)
    (hne : (interior K).Nonempty) (e : frontier K ≃ₜ frontier K) : K ≃ₜ K :=
  (boundaryExtension hconv hclosed hbounded hne e).subtype
    (homeomorph_mem_image_iff_mo1973_11532 _
      (boundaryExtension_image hconv hclosed hbounded hne e))

private theorem CuspHoneycombRadial.boundarySetExtension_frontier {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {K : Set E} (hconv : Convex ℝ K) (hclosed : IsClosed K)
    (hbounded : Bornology.IsBounded K) (hne : (interior K).Nonempty)
    (e : frontier K ≃ₜ frontier K) (x : frontier K) :
    (boundarySetExtension hconv hclosed hbounded hne e ⟨(x : E), hclosed.frontier_subset x.2⟩ :
        E) =
      (e x : E) :=
  boundaryExtension_frontier hconv hclosed hbounded hne e x

private abbrev CuspHoneycombHexagon.PositiveE0Boundary :=
  (⋃ k : Fin 6, positiveBoundary k)

private def CuspHoneycombHexagon.positiveE0BoundaryHexagonHomeomorph :
    PositiveE0Boundary ≃ₜ frontier Hexagon
    where
  toFun
    x :=
    ⟨(positiveE0HexagonHomeomorph x.1 : Plane),
      by
      rw [frontier_hexagon]
      exact (positiveE0HexagonHomeomorph_mem_boundary_iff x.1).mpr x.2⟩
  invFun
    y :=
    ⟨positiveE0HexagonHomeomorph.symm ⟨y.1, hexagon_isClosed.frontier_subset y.2⟩,
      by
      apply (positiveE0HexagonHomeomorph_mem_boundary_iff _).mp
      simpa only [Homeomorph.apply_symm_apply, ← frontier_hexagon] using y.2⟩
  left_inv x := Subtype.ext (positiveE0HexagonHomeomorph.symm_apply_apply x.1)
  right_inv
    y := by
    apply Subtype.ext
    change
      (positiveE0HexagonHomeomorph
            (positiveE0HexagonHomeomorph.symm ⟨y.1, hexagon_isClosed.frontier_subset y.2⟩) :
          Plane) =
        y.1
    rw [Homeomorph.apply_symm_apply]
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact
      continuous_subtype_val.comp
        (positiveE0HexagonHomeomorph.continuous.comp continuous_subtype_val)
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact positiveE0HexagonHomeomorph.symm.continuous.comp (continuous_subtype_val.subtype_mk _)

@[simp]
private theorem
    CuspHoneycombHexagon.positiveE0BoundaryHexagonHomeomorph_coe (x : PositiveE0Boundary) :
    (positiveE0BoundaryHexagonHomeomorph x : Plane) = (positiveE0HexagonHomeomorph x.1 : Plane) :=
  rfl

private def
    CuspHoneycombHexagon.polygonBoundaryConjugate (b : PositiveE0Boundary ≃ₜ PositiveE0Boundary) :
    frontier Hexagon ≃ₜ frontier Hexagon :=
  positiveE0BoundaryHexagonHomeomorph.symm.trans (b.trans positiveE0BoundaryHexagonHomeomorph)

@[simp]
private theorem CuspHoneycombHexagon.polygonBoundaryConjugate_apply
    (b : PositiveE0Boundary ≃ₜ PositiveE0Boundary) (x : PositiveE0Boundary) :
    polygonBoundaryConjugate b (positiveE0BoundaryHexagonHomeomorph x) =
      positiveE0BoundaryHexagonHomeomorph (b x) := by
  change
    positiveE0BoundaryHexagonHomeomorph
        (b (positiveE0BoundaryHexagonHomeomorph.symm (positiveE0BoundaryHexagonHomeomorph x))) =
      _
  rw [Homeomorph.symm_apply_apply]

private def CuspHoneycombHexagon.positiveE0BoundaryExtension
    (b : PositiveE0Boundary ≃ₜ PositiveE0Boundary) : PositiveE0 ≃ₜ PositiveE0 :=
  positiveE0HexagonHomeomorph.trans
    ((CuspHoneycombRadial.boundarySetExtension hexagon_convex hexagon_isClosed hexagon_isBounded
          hexagon_interior_nonempty (polygonBoundaryConjugate b)).trans
      positiveE0HexagonHomeomorph.symm)

private theorem CuspHoneycombHexagon.positiveE0BoundaryExtension_boundary
    (b : PositiveE0Boundary ≃ₜ PositiveE0Boundary) (x : PositiveE0Boundary) :
    positiveE0BoundaryExtension b (x : PositiveE0) = (b x : PositiveE0) := by
  apply positiveE0HexagonHomeomorph.injective
  change
    positiveE0HexagonHomeomorph
        (positiveE0HexagonHomeomorph.symm
          (CuspHoneycombRadial.boundarySetExtension hexagon_convex hexagon_isClosed
            hexagon_isBounded hexagon_interior_nonempty (polygonBoundaryConjugate b)
            (positiveE0HexagonHomeomorph x.1))) =
      _
  rw [Homeomorph.apply_symm_apply]
  apply Subtype.ext
  have h :=
    CuspHoneycombRadial.boundarySetExtension_frontier hexagon_convex hexagon_isClosed
      hexagon_isBounded hexagon_interior_nonempty (polygonBoundaryConjugate b)
      (positiveE0BoundaryHexagonHomeomorph x)
  simpa only [polygonBoundaryConjugate_apply, positiveE0BoundaryHexagonHomeomorph_coe] using h

private def
    CuspHoneycombHexagon.positiveBoundaryArc (k : Fin 6) : unitInterval ≃ₜ positiveBoundary k :=
  (sideIntervalHomeomorph k).trans (positiveBoundaryHexagonHomeomorph k).symm

@[simp]
private theorem CuspHoneycombHexagon.positiveBoundaryArc_hexagon (k : Fin 6) (t : unitInterval) :
    (positiveE0HexagonHomeomorph (positiveBoundaryArc k t).1 : Plane) =
      (1 - (t : ℝ)) • vertex (k - 1) + (t : ℝ) • vertex k := by
  change
    (positiveBoundaryHexagonHomeomorph k
          ((positiveBoundaryHexagonHomeomorph k).symm (sideIntervalHomeomorph k t)) :
        Plane) =
      _
  rw [Homeomorph.apply_symm_apply]
  exact sideIntervalHomeomorph_apply k t

@[simp]
private theorem CuspHoneycombHexagon.positiveBoundaryArc_zero (k : Fin 6) :
    (positiveBoundaryArc k 0).1 = squarePoint (k - 1) cornerZero := by
  apply positiveE0HexagonHomeomorph.injective
  apply Subtype.ext
  rw [positiveBoundaryArc_hexagon, positiveE0HexagonHomeomorph_cornerZero]
  simp

@[simp]
private theorem CuspHoneycombHexagon.positiveBoundaryArc_one (k : Fin 6) :
    (positiveBoundaryArc k 1).1 = squarePoint k cornerZero := by
  apply positiveE0HexagonHomeomorph.injective
  apply Subtype.ext
  rw [positiveBoundaryArc_hexagon, positiveE0HexagonHomeomorph_cornerZero]
  simp

private theorem CuspHoneycombHexagon.positiveBoundaryArc_zero_coe (k : Fin 6) :
    (((positiveBoundaryArc k 0).1 : ToricSpace.rayDivisor 0) : ToricSpace.Space) =
      ToricSpace.inclusion (ToricComponent.zeroTriangle (k - 1)) 0 := by
  rw [positiveBoundaryArc_zero, squarePoint_cornerZero_coe]

private theorem CuspHoneycombHexagon.positiveBoundaryArc_one_coe (k : Fin 6) :
    (((positiveBoundaryArc k 1).1 : ToricSpace.rayDivisor 0) : ToricSpace.Space) =
      ToricSpace.inclusion (ToricComponent.zeroTriangle k) 0 := by
  rw [positiveBoundaryArc_one, squarePoint_cornerZero_coe]

private theorem CuspHoneycombHexagon.positiveBoundaryArc_next_endpoint (k : Fin 6) :
    (positiveBoundaryArc k 1).1 = (positiveBoundaryArc (k + 1) 0).1 := by
  rw [positiveBoundaryArc_one, positiveBoundaryArc_zero, add_sub_cancel_right]

private theorem CuspHoneycombHexagon.positiveBoundary_inter_next (k : Fin 6) :
    positiveBoundary k ∩ positiveBoundary (k + 1) = {squarePoint k cornerZero} := by
  ext x
  constructor
  · intro hx
    have hy : (positiveE0HexagonHomeomorph x : Plane) ∈ side k ∩ side (k + 1) :=
      ⟨(positiveE0HexagonHomeomorph_mem_side_iff x k).mpr hx.1,
        (positiveE0HexagonHomeomorph_mem_side_iff x (k + 1)).mpr hx.2⟩
    rw [side_inter_next, Set.mem_singleton_iff] at hy
    change x = squarePoint k cornerZero
    apply positiveE0HexagonHomeomorph.injective
    apply Subtype.ext
    exact hy.trans (positiveE0HexagonHomeomorph_cornerZero k).symm
  · intro hx
    have hx' : x = squarePoint k cornerZero := hx
    subst x
    exact
      ⟨(squarePoint_cornerZero_mem_positiveBoundary_iff k k).mpr (Or.inl rfl),
        (squarePoint_cornerZero_mem_positiveBoundary_iff k (k + 1)).mpr (Or.inr rfl)⟩

private theorem
    CuspHoneycombHexagon.positiveBoundary_disjoint_nonadjacent {i j : Fin 6} (hij : i ≠ j)
    (hnext : j ≠ i + 1) (hprev : i ≠ j + 1) :
    Disjoint (positiveBoundary i) (positiveBoundary j) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact
    Set.disjoint_left.mp (side_disjoint_nonadjacent hij hnext hprev)
      ((positiveE0HexagonHomeomorph_mem_side_iff x i).mpr hx)
      ((positiveE0HexagonHomeomorph_mem_side_iff x j).mpr hy)

private def CuspHoneycombHexagon.boundaryArcInclusion (k : Fin 6) (x : positiveBoundary k) :
    (⋃ j : Fin 6, positiveBoundary j) :=
  ⟨x.1, Set.mem_iUnion.mpr ⟨k, x.2⟩⟩

private theorem CuspHoneycombHexagon.boundaryArcInclusion_continuous (k : Fin 6) :
    Continuous (boundaryArcInclusion k) :=
  continuous_subtype_val.subtype_mk _

private def CuspHoneycombHexagon.boundaryArcProjection
    (P : ∀ k : Fin 6, unitInterval ≃ₜ positiveBoundary k) (p : Fin 6 × unitInterval) :
    (⋃ j : Fin 6, positiveBoundary j) :=
  boundaryArcInclusion p.1 (P p.1 p.2)

private theorem CuspHoneycombHexagon.boundaryArcProjection_continuous
    (P : ∀ k : Fin 6, unitInterval ≃ₜ positiveBoundary k) :
    Continuous (boundaryArcProjection P) :=
  continuous_prod_of_discrete_left.mpr
    (fun k => (boundaryArcInclusion_continuous k).comp (P k).continuous)

private theorem CuspHoneycombHexagon.boundaryArcProjection_surjective
    (P : ∀ k : Fin 6, unitInterval ≃ₜ positiveBoundary k) :
    Function.Surjective (boundaryArcProjection P) := by
  intro x
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp x.2
  obtain ⟨t, ht⟩ := (P k).surjective ⟨x.1, hk⟩
  refine ⟨(k, t), ?_⟩
  apply Subtype.ext
  change (P k t).1 = x.1
  exact congrArg (fun y : positiveBoundary k => y.1) ht

private theorem CuspHoneycombHexagon.boundaryArcFamily_eq_self_iff
    (P : ∀ k : Fin 6, unitInterval ≃ₜ positiveBoundary k) (i : Fin 6) (t u : unitInterval) :
    (P i t).1 = (P i u).1 ↔ t = u := by
  constructor
  · intro h
    exact (P i).injective (Subtype.ext h)
  · rintro rfl
    rfl

private theorem CuspHoneycombHexagon.boundaryArcFamily_eq_next_iff
    (P : ∀ k : Fin 6, unitInterval ≃ₜ positiveBoundary k)
    (hP0 : ∀ k, (P k 0).1 = (positiveBoundaryArc k 0).1)
    (hP1 : ∀ k, (P k 1).1 = (positiveBoundaryArc k 1).1) (i : Fin 6) (t u : unitInterval) :
    (P i t).1 = (P (i + 1) u).1 ↔ t = 1 ∧ u = 0 := by
  constructor
  · intro h
    have hm : (P i t).1 ∈ positiveBoundary i ∩ positiveBoundary (i + 1) := by
      refine ⟨(P i t).2, ?_⟩
      rw [h]
      exact (P (i + 1) u).2
    have hx : (P i t).1 = squarePoint i cornerZero := by
      simpa only [positiveBoundary_inter_next, Set.mem_singleton_iff] using hm
    constructor
    · apply (P i).injective
      apply Subtype.ext
      rw [hP1 i, positiveBoundaryArc_one]
      exact hx
    · apply (P (i + 1)).injective
      apply Subtype.ext
      rw [hP0 (i + 1), positiveBoundaryArc_zero, add_sub_cancel_right]
      exact h.symm.trans hx
  · rintro ⟨rfl, rfl⟩
    rw [hP1 i, hP0 (i + 1)]
    exact positiveBoundaryArc_next_endpoint i

private theorem CuspHoneycombHexagon.boundaryArcFamily_ne_nonadjacent
    (P : ∀ k : Fin 6, unitInterval ≃ₜ positiveBoundary k) {i j : Fin 6} (hij : i ≠ j)
    (hnext : j ≠ i + 1) (hprev : i ≠ j + 1) (t u : unitInterval) : (P i t).1 ≠ (P j u).1 := by
  intro h
  apply Set.disjoint_left.mp (positiveBoundary_disjoint_nonadjacent hij hnext hprev) (P i t).2
  rw [h]
  exact (P j u).2

private theorem CuspHoneycombHexagon.boundaryArcFamilies_sameFibres
    (P Q : ∀ k : Fin 6, unitInterval ≃ₜ positiveBoundary k)
    (hP0 : ∀ k, (P k 0).1 = (positiveBoundaryArc k 0).1)
    (hP1 : ∀ k, (P k 1).1 = (positiveBoundaryArc k 1).1)
    (hQ0 : ∀ k, (Q k 0).1 = (positiveBoundaryArc k 0).1)
    (hQ1 : ∀ k, (Q k 1).1 = (positiveBoundaryArc k 1).1) (i j : Fin 6) (t u : unitInterval) :
    (P i t).1 = (P j u).1 ↔ (Q i t).1 = (Q j u).1 := by
  by_cases hij : i = j
  · subst j
    rw [boundaryArcFamily_eq_self_iff, boundaryArcFamily_eq_self_iff]
  by_cases hnext : j = i + 1
  · subst j
    rw [boundaryArcFamily_eq_next_iff P hP0 hP1, boundaryArcFamily_eq_next_iff Q hQ0 hQ1]
  by_cases hprev : i = j + 1
  · subst i
    rw [eq_comm (a := (P (j + 1) t).1), eq_comm (a := (Q (j + 1) t).1),
      boundaryArcFamily_eq_next_iff P hP0 hP1, boundaryArcFamily_eq_next_iff Q hQ0 hQ1]
  exact
    iff_of_false (boundaryArcFamily_ne_nonadjacent P hij hnext hprev t u)
      (boundaryArcFamily_ne_nonadjacent Q hij hnext hprev t u)

private theorem CuspHoneycombHexagon.boundaryArcProjection_sameFibres
    (P Q : ∀ k : Fin 6, unitInterval ≃ₜ positiveBoundary k)
    (hP0 : ∀ k, (P k 0).1 = (positiveBoundaryArc k 0).1)
    (hP1 : ∀ k, (P k 1).1 = (positiveBoundaryArc k 1).1)
    (hQ0 : ∀ k, (Q k 0).1 = (positiveBoundaryArc k 0).1)
    (hQ1 : ∀ k, (Q k 1).1 = (positiveBoundaryArc k 1).1) (a b : Fin 6 × unitInterval) :
    boundaryArcProjection P a = boundaryArcProjection P b ↔
      boundaryArcProjection Q a = boundaryArcProjection Q b := by
  have h := boundaryArcFamilies_sameFibres P Q hP0 hP1 hQ0 hQ1 a.1 b.1 a.2 b.2
  constructor
  · intro hab
    apply Subtype.ext
    exact h.mp (congrArg Subtype.val hab)
  · intro hab
    apply Subtype.ext
    exact h.mpr (congrArg Subtype.val hab)

private def CuspHoneycombHexagon.boundaryGluingHomeomorph
    (P : ∀ k : Fin 6, unitInterval ≃ₜ positiveBoundary k)
    (hP0 : ∀ k, (P k 0).1 = (positiveBoundaryArc k 0).1)
    (hP1 : ∀ k, (P k 1).1 = (positiveBoundaryArc k 1).1) :
    (⋃ k : Fin 6, positiveBoundary k) ≃ₜ (⋃ k : Fin 6, positiveBoundary k) :=
  CommonFibres.homeomorph (boundaryArcProjection positiveBoundaryArc) (boundaryArcProjection P)
    (boundaryArcProjection_surjective positiveBoundaryArc)
    (boundaryArcProjection_continuous positiveBoundaryArc) (boundaryArcProjection_continuous P)
    (boundaryArcProjection_surjective P)
    (boundaryArcProjection_sameFibres positiveBoundaryArc P (fun _ => rfl) (fun _ => rfl) hP0 hP1)

@[simp]
private theorem CuspHoneycombHexagon.boundaryGluingHomeomorph_apply
    (P : ∀ k : Fin 6, unitInterval ≃ₜ positiveBoundary k)
    (hP0 : ∀ k, (P k 0).1 = (positiveBoundaryArc k 0).1)
    (hP1 : ∀ k, (P k 1).1 = (positiveBoundaryArc k 1).1) (k : Fin 6) (t : unitInterval) :
    boundaryGluingHomeomorph P hP0 hP1 (boundaryArcInclusion k (positiveBoundaryArc k t)) =
      boundaryArcInclusion k (P k t) :=
  CommonFibres.homeomorph_apply (boundaryArcProjection positiveBoundaryArc)
    (boundaryArcProjection P) (boundaryArcProjection_surjective positiveBoundaryArc)
    (boundaryArcProjection_continuous positiveBoundaryArc) (boundaryArcProjection_continuous P)
    (boundaryArcProjection_surjective P)
    (boundaryArcProjection_sameFibres positiveBoundaryArc P (fun _ => rfl) (fun _ => rfl) hP0 hP1)
    (k, t)

private noncomputable def
    CuspHoneycombHexagon.oppositePositiveBoundaryMap (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) (x : positiveBoundary k) : positiveBoundary (k + 3) :=
  ⟨⟨⟨ToricSpace.twistedTranslate (CuspPositive.positiveTwist C₀)
          (ToricSpace.cuspVector (ToricComponent.hexagonRay k)) (x.1.1 : ToricSpace.Space),
        by
        rw [ToricSpace.twistedTranslate_mem_rayDivisor, ToricSpace.cuspVector_cuspVector]
        simp only [zero_sub, neg_neg]
        exact x.2⟩,
      CuspPositive.twistedTranslate_positiveTwist_preserves_positivePart C₀
        (ToricSpace.cuspVector (ToricComponent.hexagonRay k)) x.1.2⟩,
    by
    change
      ToricSpace.twistedTranslate (CuspPositive.positiveTwist C₀)
          (ToricSpace.cuspVector (ToricComponent.hexagonRay k)) (x.1.1 : ToricSpace.Space) ∈
        ToricSpace.rayDivisor (ToricComponent.hexagonRay (k + 3))
    rw [ToricComponent.hexagonRay_opposite, ToricSpace.twistedTranslate_mem_rayDivisor,
      ToricSpace.cuspVector_cuspVector, sub_self]
    exact x.1.1.2⟩

private noncomputable def CuspHoneycombHexagon.oppositePositiveBoundaryInv_mo1973_11577
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 6) (y : positiveBoundary (k + 3)) :
    positiveBoundary k :=
  ⟨⟨⟨ToricSpace.twistedTranslate (CuspPositive.positiveTwist C₀)
          (-ToricSpace.cuspVector (ToricComponent.hexagonRay k)) (y.1.1 : ToricSpace.Space),
        by
        rw [ToricSpace.twistedTranslate_mem_rayDivisor, ToricSpace.cuspVector_neg,
          ToricSpace.cuspVector_cuspVector, neg_neg, zero_sub, ←
          ToricComponent.hexagonRay_opposite]
        exact y.2⟩,
      CuspPositive.twistedTranslate_positiveTwist_preserves_positivePart C₀
        (-ToricSpace.cuspVector (ToricComponent.hexagonRay k)) y.1.2⟩,
    by
    change
      ToricSpace.twistedTranslate (CuspPositive.positiveTwist C₀)
          (-ToricSpace.cuspVector (ToricComponent.hexagonRay k)) (y.1.1 : ToricSpace.Space) ∈
        ToricSpace.rayDivisor (ToricComponent.hexagonRay k)
    rw [ToricSpace.twistedTranslate_mem_rayDivisor, ToricSpace.cuspVector_neg,
      ToricSpace.cuspVector_cuspVector, neg_neg, sub_self]
    exact y.1.1.2⟩

private noncomputable def CuspHoneycombHexagon.oppositePositiveBoundaryHomeomorph
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 6) : positiveBoundary k ≃ₜ positiveBoundary (k + 3)
    where
  toFun := oppositePositiveBoundaryMap C₀ k
  invFun := oppositePositiveBoundaryInv_mo1973_11577 C₀ k
  left_inv
    x := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    change
      ToricSpace.twistedTranslate (CuspPositive.positiveTwist C₀)
          (-ToricSpace.cuspVector (ToricComponent.hexagonRay k))
          (ToricSpace.twistedTranslate (CuspPositive.positiveTwist C₀)
            (ToricSpace.cuspVector (ToricComponent.hexagonRay k)) (x.1.1 : ToricSpace.Space)) =
        (x.1.1 : ToricSpace.Space)
    rw [ToricSpace.twistedTranslate_add, neg_add_cancel, ToricSpace.twistedTranslate_zero]
  right_inv
    y := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    change
      ToricSpace.twistedTranslate (CuspPositive.positiveTwist C₀)
          (ToricSpace.cuspVector (ToricComponent.hexagonRay k))
          (ToricSpace.twistedTranslate (CuspPositive.positiveTwist C₀)
            (-ToricSpace.cuspVector (ToricComponent.hexagonRay k)) (y.1.1 : ToricSpace.Space)) =
        (y.1.1 : ToricSpace.Space)
    rw [ToricSpace.twistedTranslate_add, add_neg_cancel, ToricSpace.twistedTranslate_zero]
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact
      (ToricSpace.centralTranslationHomeomorph (CuspPositive.positiveTwist C₀)
            (ToricSpace.cuspVector (ToricComponent.hexagonRay k))).continuous.comp
        (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_subtype_val))
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact
      (ToricSpace.centralTranslationHomeomorph (CuspPositive.positiveTwist C₀)
            (-ToricSpace.cuspVector (ToricComponent.hexagonRay k))).continuous.comp
        (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_subtype_val))

private theorem CuspHoneycombHexagon.oppositePositiveBoundaryHomeomorph_coe
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 6) (x : positiveBoundary k) :
    ((oppositePositiveBoundaryHomeomorph C₀ k x).1.1 : ToricSpace.Space) =
      ToricSpace.twistedTranslate (CuspPositive.positiveTwist C₀)
        (ToricSpace.cuspVector (ToricComponent.hexagonRay k)) (x.1.1 : ToricSpace.Space) :=
  rfl

private theorem CuspHoneycombHexagon.zeroTriangle_shift_opposite_previous (k : Fin 6) :
    (ToricComponent.zeroTriangle (k - 1)).shift (-ToricComponent.hexagonRay k) =
      ToricComponent.zeroTriangle (k + 3) := by fin_cases k <;> decide

private theorem CuspHoneycombHexagon.zeroTriangle_shift_opposite_current (k : Fin 6) :
    (ToricComponent.zeroTriangle k).shift (-ToricComponent.hexagonRay k) =
      ToricComponent.zeroTriangle (k + 2) := by fin_cases k <;> decide

private theorem CuspHoneycombHexagon.opposite_twistedTranslate_origin_previous
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 6) :
    ToricSpace.twistedTranslate C (ToricSpace.cuspVector (ToricComponent.hexagonRay k))
        (ToricSpace.inclusion (ToricComponent.zeroTriangle (k - 1)) 0) =
      ToricSpace.inclusion (ToricComponent.zeroTriangle (k + 3)) 0 := by
  rw [ToricSpace.twistedTranslate_origin, ToricSpace.cuspVector_cuspVector,
    zeroTriangle_shift_opposite_previous]

private theorem CuspHoneycombHexagon.opposite_twistedTranslate_origin_current
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 6) :
    ToricSpace.twistedTranslate C (ToricSpace.cuspVector (ToricComponent.hexagonRay k))
        (ToricSpace.inclusion (ToricComponent.zeroTriangle k) 0) =
      ToricSpace.inclusion (ToricComponent.zeroTriangle (k + 2)) 0 := by
  rw [ToricSpace.twistedTranslate_origin, ToricSpace.cuspVector_cuspVector,
    zeroTriangle_shift_opposite_current]

private noncomputable def
    CuspHoneycombHexagon.reversedOppositeBoundaryArc (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) : unitInterval ≃ₜ positiveBoundary (k + 3) :=
  unitInterval.symmHomeomorph.trans
    ((positiveBoundaryArc k).trans (oppositePositiveBoundaryHomeomorph C₀ k))

private theorem
    CuspHoneycombHexagon.reversedOppositeBoundaryArc_zero (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) : reversedOppositeBoundaryArc C₀ k 0 = positiveBoundaryArc (k + 3) 0 := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  change
    ((oppositePositiveBoundaryHomeomorph C₀ k (positiveBoundaryArc k (unitInterval.symm 0))).1.1 :
        ToricSpace.Space) =
      ((positiveBoundaryArc (k + 3) 0).1.1 : ToricSpace.Space)
  rw [unitInterval.symm_zero, oppositePositiveBoundaryHomeomorph_coe, positiveBoundaryArc_one_coe,
    opposite_twistedTranslate_origin_current, positiveBoundaryArc_zero_coe]
  have hi : (k + 3) - 1 = k + 2 := by fin_cases k <;> decide
  rw [hi]

private theorem CuspHoneycombHexagon.reversedOppositeBoundaryArc_one (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) : reversedOppositeBoundaryArc C₀ k 1 = positiveBoundaryArc (k + 3) 1 := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  change
    ((oppositePositiveBoundaryHomeomorph C₀ k (positiveBoundaryArc k (unitInterval.symm 1))).1.1 :
        ToricSpace.Space) =
      ((positiveBoundaryArc (k + 3) 1).1.1 : ToricSpace.Space)
  rw [unitInterval.symm_one, oppositePositiveBoundaryHomeomorph_coe, positiveBoundaryArc_zero_coe,
    opposite_twistedTranslate_origin_previous, positiveBoundaryArc_one_coe]

private noncomputable def
    CuspHoneycombHexagon.compatibleBoundaryArc (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    (k : Fin 6) → unitInterval ≃ₜ positiveBoundary k :=
  Fin.cases (positiveBoundaryArc 0)
    (Fin.cases (positiveBoundaryArc 1)
      (Fin.cases (positiveBoundaryArc 2)
        (Fin.cases (reversedOppositeBoundaryArc C₀ 0)
          (Fin.cases (reversedOppositeBoundaryArc C₀ 1)
            (Fin.cases (reversedOppositeBoundaryArc C₀ 2) (fun i => Fin.elim0 i))))))

private theorem CuspHoneycombHexagon.compatibleBoundaryArc_zero (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) : compatibleBoundaryArc C₀ k 0 = positiveBoundaryArc k 0 := by
  fin_cases k
  · rfl
  · rfl
  · rfl
  · exact reversedOppositeBoundaryArc_zero C₀ 0
  · exact reversedOppositeBoundaryArc_zero C₀ 1
  · exact reversedOppositeBoundaryArc_zero C₀ 2

private theorem CuspHoneycombHexagon.compatibleBoundaryArc_one (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) : compatibleBoundaryArc C₀ k 1 = positiveBoundaryArc k 1 := by
  fin_cases k
  · rfl
  · rfl
  · rfl
  · exact reversedOppositeBoundaryArc_one C₀ 0
  · exact reversedOppositeBoundaryArc_one C₀ 1
  · exact reversedOppositeBoundaryArc_one C₀ 2

private theorem
    CuspHoneycombHexagon.compatibleBoundaryArc_zero_point (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) : (compatibleBoundaryArc C₀ k 0).1 = squarePoint (k - 1) cornerZero := by
  rw [compatibleBoundaryArc_zero, positiveBoundaryArc_zero]

private theorem CuspHoneycombHexagon.compatibleBoundaryArc_one_point (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) : (compatibleBoundaryArc C₀ k 1).1 = squarePoint k cornerZero := by
  rw [compatibleBoundaryArc_one, positiveBoundaryArc_one]

private theorem CuspHoneycombHexagon.oppositePositiveBoundaryHomeomorph_twice_coe
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 6) (x : positiveBoundary k) :
    ((oppositePositiveBoundaryHomeomorph C₀ (k + 3)
              (oppositePositiveBoundaryHomeomorph C₀ k x)).1.1 :
        ToricSpace.Space) =
      (x.1.1 : ToricSpace.Space) := by
  rw [oppositePositiveBoundaryHomeomorph_coe, oppositePositiveBoundaryHomeomorph_coe,
    ToricComponent.hexagonRay_opposite, ToricSpace.cuspVector_neg,
    ToricSpace.twistedTranslate_add, neg_add_cancel, ToricSpace.twistedTranslate_zero]

private theorem CuspHoneycombHexagon.compatibleBoundaryArc_opposite (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) (t : unitInterval) :
    compatibleBoundaryArc C₀ (k + 3) (unitInterval.symm t) =
      oppositePositiveBoundaryHomeomorph C₀ k (compatibleBoundaryArc C₀ k t) := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  fin_cases k
  · change
      ((oppositePositiveBoundaryHomeomorph C₀ 0
                (positiveBoundaryArc 0 (unitInterval.symm (unitInterval.symm t)))).1.1 :
          ToricSpace.Space) =
        ((oppositePositiveBoundaryHomeomorph C₀ 0 (positiveBoundaryArc 0 t)).1.1 :
          ToricSpace.Space)
    rw [unitInterval.symm_symm]
  · change
      ((oppositePositiveBoundaryHomeomorph C₀ 1
                (positiveBoundaryArc 1 (unitInterval.symm (unitInterval.symm t)))).1.1 :
          ToricSpace.Space) =
        ((oppositePositiveBoundaryHomeomorph C₀ 1 (positiveBoundaryArc 1 t)).1.1 :
          ToricSpace.Space)
    rw [unitInterval.symm_symm]
  · change
      ((oppositePositiveBoundaryHomeomorph C₀ 2
                (positiveBoundaryArc 2 (unitInterval.symm (unitInterval.symm t)))).1.1 :
          ToricSpace.Space) =
        ((oppositePositiveBoundaryHomeomorph C₀ 2 (positiveBoundaryArc 2 t)).1.1 :
          ToricSpace.Space)
    rw [unitInterval.symm_symm]
  · exact
      (oppositePositiveBoundaryHomeomorph_twice_coe C₀ 0
          (positiveBoundaryArc 0 (unitInterval.symm t))).symm
  · exact
      (oppositePositiveBoundaryHomeomorph_twice_coe C₀ 1
          (positiveBoundaryArc 1 (unitInterval.symm t))).symm
  · exact
      (oppositePositiveBoundaryHomeomorph_twice_coe C₀ 2
          (positiveBoundaryArc 2 (unitInterval.symm t))).symm

private theorem
    CuspHoneycombHexagon.compatibleBoundaryArc_opposite_coe (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) (t : unitInterval) :
    ((compatibleBoundaryArc C₀ (k + 3) (unitInterval.symm t)).1.1 : ToricSpace.Space) =
      ToricSpace.twistedTranslate (CuspPositive.positiveTwist C₀)
        (ToricSpace.cuspVector (ToricComponent.hexagonRay k))
        ((compatibleBoundaryArc C₀ k t).1.1 : ToricSpace.Space) := by
  rw [compatibleBoundaryArc_opposite, oppositePositiveBoundaryHomeomorph_coe]

private def CuspHoneycombHexagon.compatibleBoundaryHomeomorph (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    PositiveE0Boundary ≃ₜ PositiveE0Boundary :=
  boundaryGluingHomeomorph (compatibleBoundaryArc C₀)
    (fun k => congrArg Subtype.val (compatibleBoundaryArc_zero C₀ k))
    (fun k => congrArg Subtype.val (compatibleBoundaryArc_one C₀ k))

private theorem
    CuspHoneycombHexagon.compatibleBoundaryHomeomorph_arc (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) (t : unitInterval) :
    compatibleBoundaryHomeomorph C₀ (boundaryArcInclusion k (positiveBoundaryArc k t)) =
      boundaryArcInclusion k (compatibleBoundaryArc C₀ k t) :=
  boundaryGluingHomeomorph_apply _ _ _ k t

private def CuspHoneycombHexagon.compatibleComponentHomeomorph (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    PositiveE0 ≃ₜ PositiveE0 :=
  positiveE0BoundaryExtension (compatibleBoundaryHomeomorph C₀)

private theorem
    CuspHoneycombHexagon.compatibleComponentHomeomorph_arc (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) (t : unitInterval) :
    compatibleComponentHomeomorph C₀ (positiveBoundaryArc k t).1 =
      (compatibleBoundaryArc C₀ k t).1 := by
  exact
    (positiveE0BoundaryExtension_boundary (compatibleBoundaryHomeomorph C₀)
          (boundaryArcInclusion k (positiveBoundaryArc k t))).trans
      (congrArg Subtype.val (compatibleBoundaryHomeomorph_arc C₀ k t))

private theorem CuspHoneycombHexagon.compatibleComponentHomeomorph_mem_boundary_iff
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (x : PositiveE0) (k : Fin 6) :
    compatibleComponentHomeomorph C₀ x ∈ positiveBoundary k ↔ x ∈ positiveBoundary k := by
  constructor
  · intro hx
    obtain ⟨t, ht⟩ :=
      (compatibleBoundaryArc C₀ k).surjective ⟨compatibleComponentHomeomorph C₀ x, hx⟩
    have he : (positiveBoundaryArc k t).1 = x := by
      apply (compatibleComponentHomeomorph C₀).injective
      rw [compatibleComponentHomeomorph_arc]
      exact congrArg Subtype.val ht
    rw [← he]
    exact (positiveBoundaryArc k t).2
  · intro hx
    obtain ⟨t, ht⟩ := (positiveBoundaryArc k).surjective ⟨x, hx⟩
    have he : (positiveBoundaryArc k t).1 = x := congrArg Subtype.val ht
    rw [← he, compatibleComponentHomeomorph_arc]
    exact (compatibleBoundaryArc C₀ k t).2

private def CuspHoneycombHexagon.compatibleHexagonHomeomorph (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    Hexagon ≃ₜ PositiveE0 :=
  positiveE0HexagonHomeomorph.symm.trans (compatibleComponentHomeomorph C₀)

private theorem CuspHoneycombHexagon.compatibleHexagonHomeomorph_sideInterval
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 6) (t : unitInterval) :
    compatibleHexagonHomeomorph C₀
        ⟨(sideIntervalHomeomorph k t : Plane), (sideIntervalHomeomorph k t).2.1⟩ =
      (compatibleBoundaryArc C₀ k t).1 :=
  compatibleComponentHomeomorph_arc C₀ k t

private theorem CuspHoneycombHexagon.compatibleHexagonHomeomorph_mem_boundary_iff
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (x : Hexagon) (k : Fin 6) :
    compatibleHexagonHomeomorph C₀ x ∈ positiveBoundary k ↔ (x : Plane) ∈ side k := by
  change
    compatibleComponentHomeomorph C₀ (positiveE0HexagonHomeomorph.symm x) ∈ positiveBoundary k ↔ _
  rw [compatibleComponentHomeomorph_mem_boundary_iff]
  exact
    (positiveE0HexagonHomeomorph_mem_side_iff (positiveE0HexagonHomeomorph.symm x) k).symm.trans
      (by rw [Homeomorph.apply_symm_apply])

private def CuspHoneycombHexagon.compatibleCellHomeomorph (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    CuspHoneycombTiling.baseCell ≃ₜ PositiveE0 :=
  CuspHoneycombTiling.standardHexagonDualHomeomorph.symm.trans (compatibleHexagonHomeomorph C₀)

private theorem
    CuspHoneycombHexagon.compatibleCellHomeomorph_sideInterval (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) (t : unitInterval) :
    compatibleCellHomeomorph C₀
        (CuspHoneycombTiling.standardHexagonDualHomeomorph
          ⟨(sideIntervalHomeomorph k t : Plane), (sideIntervalHomeomorph k t).2.1⟩) =
      (compatibleBoundaryArc C₀ k t).1 := by
  change
    compatibleHexagonHomeomorph C₀
        (CuspHoneycombTiling.standardHexagonDualHomeomorph.symm
          (CuspHoneycombTiling.standardHexagonDualHomeomorph _)) =
      _
  rw [Homeomorph.symm_apply_apply]
  exact compatibleHexagonHomeomorph_sideInterval C₀ k t

private theorem CuspHoneycombHexagon.compatibleCellHomeomorph_mem_boundary_iff
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (x : CuspHoneycombTiling.baseCell) (k : Fin 6) :
    compatibleCellHomeomorph C₀ x ∈ positiveBoundary k ↔
      (x : Plane) ∈ CuspHoneycombTiling.cell (ToricComponent.hexagonRay k) := by
  change
    compatibleHexagonHomeomorph C₀ (CuspHoneycombTiling.standardHexagonDualHomeomorph.symm x) ∈
        positiveBoundary k ↔
      _
  rw [compatibleHexagonHomeomorph_mem_boundary_iff]
  have h :=
    CuspHoneycombTiling.standardHexagonDualHomeomorph_mem_cell_iff_side k
      (CuspHoneycombTiling.standardHexagonDualHomeomorph.symm x)
  simpa only [Homeomorph.apply_symm_apply] using h.symm

private theorem ToricFan.areAdjacent_iff_hexagonRay (v w : Fin 2 → ℤ) :
    AreAdjacent v w ↔ ∃ k : Fin 6, w - v = ToricComponent.hexagonRay k := by
  have hedges : ∀ i : Fin 3, ∃ k : Fin 6, edgeDirection i = ToricComponent.hexagonRay k := by
    intro i
    fin_cases i <;> decide
  have hrays :
    ∀ k : Fin 6,
      ∃ i : Fin 3,
        ToricComponent.hexagonRay k = edgeDirection i ∨
          ToricComponent.hexagonRay k = -edgeDirection i := by
    intro k
    fin_cases k <;> decide
  constructor
  · rintro ⟨i, hi | hi⟩
    · obtain ⟨k, hk⟩ := hedges i
      exact ⟨k, hi.trans hk⟩
    · obtain ⟨k, hk⟩ := hedges i
      refine ⟨k + 3, hi.trans ?_⟩
      rw [hk, ToricComponent.hexagonRay_opposite]
  · rintro ⟨k, hk⟩
    obtain ⟨i, hi | hi⟩ := hrays k
    · exact ⟨i, Or.inl (hk.trans hi)⟩
    · exact ⟨i, Or.inr (hk.trans hi)⟩

private theorem CuspHoneycombTiling.baseCell_inter_cell_nonempty_iff_hexagonRay
    (v : CuspHoneycombTiling.Lattice) :
    (baseCell ∩ cell v).Nonempty ↔ v = 0 ∨ ∃ k : Fin 6, v = ToricComponent.hexagonRay k := by
  rw [baseCell_inter_cell_nonempty_iff]
  simp [ToricComponent.hexagonRay, Fin.exists_fin_succ, or_assoc, or_left_comm, or_comm]

private theorem CuspHoneycombTiling.cell_inter_cell_nonempty_iff_adjacent
    (v w : CuspHoneycombTiling.Lattice) :
    (cell v ∩ cell w).Nonempty ↔ v = w ∨ ToricFan.AreAdjacent v w := by
  rw [cell_inter_cell_nonempty_iff_baseCell, baseCell_inter_cell_nonempty_iff_hexagonRay, ←
    ToricFan.areAdjacent_iff_hexagonRay, sub_eq_zero]
  exact or_congr eq_comm Iff.rfl

private theorem CuspHoneycombHexagon.compatibleCellHomeomorph_mem_rayDivisor_iff
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (x : CuspHoneycombTiling.baseCell) (v : Fin 2 → ℤ) :
    ((compatibleCellHomeomorph C₀ x).1 : ToricSpace.Space) ∈ ToricSpace.rayDivisor v ↔
      (x : Plane) ∈ CuspHoneycombTiling.cell v := by
  by_cases hv : v = 0
  · subst v
    exact
      iff_of_true (compatibleCellHomeomorph C₀ x).1.2
        (by simpa only [CuspHoneycombTiling.cell_zero] using x.2)
  constructor
  · intro hx
    have hmeet : (ToricSpace.rayDivisor 0 ∩ ToricSpace.rayDivisor v).Nonempty :=
      ⟨((compatibleCellHomeomorph C₀ x).1 : ToricSpace.Space),
        (compatibleCellHomeomorph C₀ x).1.2, hx⟩
    have hadj : ToricFan.AreAdjacent 0 v :=
      (ToricSpace.rayDivisor_inter_nonempty_iff 0 v (fun h => hv h.symm)).mp hmeet
    obtain ⟨k, hk⟩ := (ToricFan.areAdjacent_iff_hexagonRay 0 v).mp hadj
    have hvk : v = ToricComponent.hexagonRay k := by simpa only [sub_zero] using hk
    subst v
    change compatibleCellHomeomorph C₀ x ∈ positiveBoundary k at hx
    exact (compatibleCellHomeomorph_mem_boundary_iff C₀ x k).mp hx
  · intro hx
    have hmeet : (CuspHoneycombTiling.baseCell ∩ CuspHoneycombTiling.cell v).Nonempty :=
      ⟨(x : Plane), x.2, hx⟩
    rcases (CuspHoneycombTiling.baseCell_inter_cell_nonempty_iff_hexagonRay v).mp hmeet with
      hzero | ⟨k, hk⟩
    · exact (hv hzero).elim
    · subst v
      exact (compatibleCellHomeomorph_mem_boundary_iff C₀ x k).mpr hx

private theorem
    CuspHoneycombHexagon.compatibleCellHomeomorph_opposite (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) (x : CuspHoneycombTiling.baseCell)
    (hx : (x : Plane) ∈ CuspHoneycombTiling.cell (ToricComponent.hexagonRay k)) :
    ((compatibleCellHomeomorph C₀
            ⟨(x : Plane) - CuspHoneycombTiling.latticePoint (ToricComponent.hexagonRay k),
              hx⟩).1 :
        ToricSpace.Space) =
      ToricSpace.twistedTranslate (CuspPositive.positiveTwist C₀)
        (ToricSpace.cuspVector (ToricComponent.hexagonRay k))
        ((compatibleCellHomeomorph C₀ x).1 : ToricSpace.Space) := by
  let y : Hexagon := CuspHoneycombTiling.standardHexagonDualHomeomorph.symm x
  have hy : (y : Plane) ∈ side k := by
    apply (CuspHoneycombTiling.standardHexagonDualHomeomorph_mem_cell_iff_side k y).mp
    simpa only [y, Homeomorph.apply_symm_apply] using hx
  obtain ⟨t, ht⟩ := (sideIntervalHomeomorph k).surjective ⟨y, hy⟩
  have hxt :
    CuspHoneycombTiling.standardHexagonDualHomeomorph
        ⟨(sideIntervalHomeomorph k t : Plane), (sideIntervalHomeomorph k t).2.1⟩ =
      x := by
    have hyt :
      (⟨(sideIntervalHomeomorph k t : Plane), (sideIntervalHomeomorph k t).2.1⟩ : Hexagon) = y :=
      Subtype.ext (congrArg (fun z : side k => (z : Plane)) ht)
    rw [hyt]
    exact CuspHoneycombTiling.standardHexagonDualHomeomorph.apply_symm_apply x
  have hshift :
    CuspHoneycombTiling.standardHexagonDualHomeomorph
        ⟨(sideIntervalHomeomorph (k + 3) (unitInterval.symm t) : Plane),
          (sideIntervalHomeomorph (k + 3) (unitInterval.symm t)).2.1⟩ =
      ⟨(x : Plane) - CuspHoneycombTiling.latticePoint (ToricComponent.hexagonRay k), hx⟩ := by
    apply Subtype.ext
    change
      CuspHoneycombTiling.dualStandardPlaneHomeomorph.symm
          (sideIntervalHomeomorph (k + 3) (unitInterval.symm t) : Plane) =
        (x : Plane) - CuspHoneycombTiling.latticePoint (ToricComponent.hexagonRay k)
    rw [CuspHoneycombTiling.dual_sideInterval_opposite]
    exact
      congrArg
        (fun z : CuspHoneycombTiling.baseCell =>
          (z : Plane) - CuspHoneycombTiling.latticePoint (ToricComponent.hexagonRay k))
        hxt
  rw [← hshift, compatibleCellHomeomorph_sideInterval, ← hxt,
    compatibleCellHomeomorph_sideInterval]
  exact compatibleBoundaryArc_opposite_coe C₀ k t

private def CuspHoneycomb.cellHomeomorph (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (v : (CuspHoneycombTiling.Lattice)) :
    CuspHoneycombTiling.cell v ≃ₜ CuspHoneycombPositive.positiveCell v :=
  (CuspHoneycombTiling.cellTranslationHomeomorph v).symm.trans
    ((CuspHoneycombHexagon.compatibleCellHomeomorph C₀).trans
      (CuspHoneycombPositive.positiveE0CellHomeomorph C₀ v))

@[simp]
private theorem CuspHoneycomb.cellHomeomorph_coe (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (v : (CuspHoneycombTiling.Lattice)) (x : CuspHoneycombTiling.cell v) :
    ((cellHomeomorph C₀ v x).1.1 : ToricSpace.Space) =
      ToricSpace.twistedTranslate (CuspPositive.positiveTwist C₀) (-ToricSpace.cuspVector v)
        ((CuspHoneycombHexagon.compatibleCellHomeomorph C₀
              ((CuspHoneycombTiling.cellTranslationHomeomorph v).symm x)).1 :
          ToricSpace.Space) :=
  rfl

private theorem CuspHoneycomb.cellHomeomorph_mem_positiveCell_iff (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (v w : (CuspHoneycombTiling.Lattice)) (x : CuspHoneycombTiling.cell v) :
    (cellHomeomorph C₀ v x : CuspPositiveRetraction.PositiveCentralFibre) ∈
        CuspHoneycombPositive.positiveCell w ↔
      (x : (CuspHoneycombTiling.Plane)) ∈ CuspHoneycombTiling.cell w := by
  change ((cellHomeomorph C₀ v x).1.1 : ToricSpace.Space) ∈ ToricSpace.rayDivisor w ↔ _
  rw [cellHomeomorph_coe, ToricSpace.twistedTranslate_mem_rayDivisor, ToricSpace.cuspVector_neg,
    ToricSpace.cuspVector_cuspVector, neg_neg,
    CuspHoneycombHexagon.compatibleCellHomeomorph_mem_rayDivisor_iff]
  change
    (x : (CuspHoneycombTiling.Plane)) - CuspHoneycombTiling.latticePoint v ∈
        CuspHoneycombTiling.cell (w - v) ↔
      _
  rw [CuspHoneycombTiling.sub_latticePoint_mem_cell_iff]
  have he : v + (w - v) = w := by abel
  rw [he]

private theorem CuspHoneycomb.cellHomeomorph_compatible (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (v w : (CuspHoneycombTiling.Lattice)) (x : CuspHoneycombTiling.cell v)
    (y : CuspHoneycombTiling.cell w)
    (hxy : (x : (CuspHoneycombTiling.Plane)) = (y : (CuspHoneycombTiling.Plane))) :
    (cellHomeomorph C₀ v x : CuspPositiveRetraction.PositiveCentralFibre) =
      (cellHomeomorph C₀ w y : CuspPositiveRetraction.PositiveCentralFibre) := by
  have hxw : (x : (CuspHoneycombTiling.Plane)) ∈ CuspHoneycombTiling.cell w := by
    rw [hxy]
    exact y.2
  have hnonempty : (CuspHoneycombTiling.cell v ∩ CuspHoneycombTiling.cell w).Nonempty :=
    ⟨x, x.2, hxw⟩
  rcases (CuspHoneycombTiling.cell_inter_cell_nonempty_iff_adjacent v w).mp hnonempty with rfl |
    hadj
  · have he : x = y := Subtype.ext hxy
    rw [he]
  obtain ⟨k, hk⟩ := (ToricFan.areAdjacent_iff_hexagonRay v w).mp hadj
  have hw : w = v + ToricComponent.hexagonRay k := (sub_eq_iff_eq_add.mp hk).trans (add_comm _ _)
  let a : CuspHoneycombTiling.baseCell := (CuspHoneycombTiling.cellTranslationHomeomorph v).symm x
  let b : CuspHoneycombTiling.baseCell := (CuspHoneycombTiling.cellTranslationHomeomorph w).symm y
  have ha :
    (a : (CuspHoneycombTiling.Plane)) ∈ CuspHoneycombTiling.cell (ToricComponent.hexagonRay k) := by
    change
      (x : (CuspHoneycombTiling.Plane)) - CuspHoneycombTiling.latticePoint v ∈
        CuspHoneycombTiling.cell (ToricComponent.hexagonRay k)
    apply
      (CuspHoneycombTiling.sub_latticePoint_mem_cell_iff v (ToricComponent.hexagonRay k) x).mpr
    simpa only [← hw] using hxw
  have hb :
    b =
      ⟨(a : (CuspHoneycombTiling.Plane)) -
          CuspHoneycombTiling.latticePoint (ToricComponent.hexagonRay k),
        ha⟩ := by
    apply Subtype.ext
    change
      (y : (CuspHoneycombTiling.Plane)) - CuspHoneycombTiling.latticePoint w =
        ((x : (CuspHoneycombTiling.Plane)) - CuspHoneycombTiling.latticePoint v) -
          CuspHoneycombTiling.latticePoint (ToricComponent.hexagonRay k)
    rw [← hxy, hw, CuspHoneycombTiling.latticePoint_add]
    abel
  apply Subtype.ext
  apply Subtype.ext
  rw [cellHomeomorph_coe, cellHomeomorph_coe]
  change
    ToricSpace.twistedTranslate (CuspPositive.positiveTwist C₀) (-ToricSpace.cuspVector v)
        ((CuspHoneycombHexagon.compatibleCellHomeomorph C₀ a).1 : ToricSpace.Space) =
      ToricSpace.twistedTranslate (CuspPositive.positiveTwist C₀) (-ToricSpace.cuspVector w)
        ((CuspHoneycombHexagon.compatibleCellHomeomorph C₀ b).1 : ToricSpace.Space)
  rw [hb, CuspHoneycombHexagon.compatibleCellHomeomorph_opposite C₀ k a ha,
    ToricSpace.twistedTranslate_add]
  have hu :
    -ToricSpace.cuspVector w + ToricSpace.cuspVector (ToricComponent.hexagonRay k) =
      -ToricSpace.cuspVector v := by
    rw [hw, ToricSpace.cuspVector_add]
    abel
  rw [hu]

private theorem CuspHoneycomb.cellHomeomorph_eq_iff (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (v w : (CuspHoneycombTiling.Lattice)) (x : CuspHoneycombTiling.cell v)
    (y : CuspHoneycombTiling.cell w) :
    (cellHomeomorph C₀ v x : CuspPositiveRetraction.PositiveCentralFibre) =
        (cellHomeomorph C₀ w y : CuspPositiveRetraction.PositiveCentralFibre) ↔
      (x : (CuspHoneycombTiling.Plane)) = (y : (CuspHoneycombTiling.Plane)) := by
  constructor
  · intro h
    have hxw : (x : (CuspHoneycombTiling.Plane)) ∈ CuspHoneycombTiling.cell w :=
      (cellHomeomorph_mem_positiveCell_iff C₀ v w x).mp
        (by
          rw [h]
          exact (cellHomeomorph C₀ w y).2)
    have hcomp := cellHomeomorph_compatible C₀ v w x ⟨x, hxw⟩ rfl
    have he : cellHomeomorph C₀ w ⟨x, hxw⟩ = cellHomeomorph C₀ w y :=
      Subtype.ext (hcomp.symm.trans h)
    exact congrArg Subtype.val ((cellHomeomorph C₀ w).injective he)
  · exact cellHomeomorph_compatible C₀ v w x y

private def CuspHoneycombClosedCover.projection {ι X : Type*} (A : ι → Set X) (p : Σ i, A i) : X :=
  p.2.1

private theorem CuspHoneycombClosedCover.projection_continuous {ι X : Type*} [TopologicalSpace X]
    (A : ι → Set X) : Continuous (projection A) :=
  continuous_sigma_iff.mpr fun _ => continuous_subtype_val

private theorem CuspHoneycombClosedCover.projection_surjective {ι X : Type*} {A : ι → Set X}
    (hcover : ⋃ i, A i = Set.univ) : Function.Surjective (projection A) := by
  intro x
  have hx : x ∈ ⋃ i, A i := by rw [hcover]; trivial
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  exact ⟨⟨i, x, hi⟩, rfl⟩

private theorem CuspHoneycombClosedCover.projection_isClosedMap {ι X : Type*} [TopologicalSpace X]
    {A : ι → Set X} (hclosed : ∀ i, IsClosed (A i)) (hloc : LocallyFinite A) :
    IsClosedMap (projection A) := by
  intro S hS
  let F : ι → Set X := fun i => (Subtype.val : A i → X) '' ((fun x : A i => Sigma.mk i x) ⁻¹' S)
  have hFclosed (i : ι) : IsClosed (F i) :=
    (hclosed i).isClosedMap_subtype_val _ (hS.preimage continuous_sigmaMk)
  have hFsub (i : ι) : F i ⊆ A i := by
    rintro x ⟨a, _, rfl⟩
    exact a.2
  have heq : projection A '' S = ⋃ i, F i := by
    ext x
    constructor
    · rintro ⟨⟨i, a⟩, ha, rfl⟩
      exact Set.mem_iUnion.mpr ⟨i, a, ha, rfl⟩
    · intro hx
      obtain ⟨i, a, ha, rfl⟩ := Set.mem_iUnion.mp hx
      exact ⟨⟨i, a⟩, ha, rfl⟩
  rw [heq]
  exact (hloc.subset hFsub).isClosed_iUnion hFclosed

private theorem CuspHoneycombClosedCover.projection_isQuotientMap {ι X : Type*} [TopologicalSpace X]
    {A : ι → Set X} (hcover : ⋃ i, A i = Set.univ) (hclosed : ∀ i, IsClosed (A i))
    (hloc : LocallyFinite A) : Topology.IsQuotientMap (projection A) :=
  (projection_isClosedMap hclosed hloc).isQuotientMap (projection_continuous A)
    (projection_surjective hcover)

private def CuspHoneycombClosedCover.quotientHomeomorph {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {Z : Type*} [TopologicalSpace Z] (f : Z → X) (g : Z → Y)
    (hf : Topology.IsQuotientMap f) (hg : Topology.IsQuotientMap g)
    (hfg : ∀ a b, f a = f b ↔ g a = g b) : X ≃ₜ Y
    where
  toFun := CuspHoneycombHexagon.CommonFibres.descend f g hf.surjective
  invFun := CuspHoneycombHexagon.CommonFibres.descend g f hg.surjective
  left_inv
    x := by
    obtain ⟨a, rfl⟩ := hf.surjective x
    rw [CuspHoneycombHexagon.CommonFibres.descend_apply f g hf.surjective
        (fun a b => (hfg a b).mp),
      CuspHoneycombHexagon.CommonFibres.descend_apply g f hg.surjective
        (fun a b => (hfg a b).mpr)]
  right_inv
    y := by
    obtain ⟨a, rfl⟩ := hg.surjective y
    rw [CuspHoneycombHexagon.CommonFibres.descend_apply g f hg.surjective
        (fun a b => (hfg a b).mpr),
      CuspHoneycombHexagon.CommonFibres.descend_apply f g hf.surjective (fun a b => (hfg a b).mp)]
  continuous_toFun :=
    CuspHoneycombHexagon.CommonFibres.descend_continuous f g hf.surjective hf hg.continuous
      (fun a b => (hfg a b).mp)
  continuous_invFun :=
    CuspHoneycombHexagon.CommonFibres.descend_continuous g f hg.surjective hg hf.continuous
      (fun a b => (hfg a b).mpr)

private theorem CuspHoneycombClosedCover.quotientHomeomorph_apply {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {Z : Type*} [TopologicalSpace Z] (f : Z → X) (g : Z → Y)
    (hf : Topology.IsQuotientMap f) (hg : Topology.IsQuotientMap g)
    (hfg : ∀ a b, f a = f b ↔ g a = g b) (a : Z) : quotientHomeomorph f g hf hg hfg (f a) = g a :=
  CuspHoneycombHexagon.CommonFibres.descend_apply f g hf.surjective (fun a b => (hfg a b).mp) a

private def CuspHoneycombClosedCover.sigmaHomeomorph {ι X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (A : ι → Set X) (B : ι → Set Y) (e : ∀ i, A i ≃ₜ B i) :
    (Σ i, A i) ≃ₜ (Σ i, B i) where
  toFun p := ⟨p.1, e p.1 p.2⟩
  invFun p := ⟨p.1, (e p.1).symm p.2⟩
  left_inv := by rintro ⟨i, a⟩; simp
  right_inv := by rintro ⟨i, b⟩; simp
  continuous_toFun := continuous_sigma_iff.mpr fun i => continuous_sigmaMk.comp (e i).continuous
  continuous_invFun :=
    continuous_sigma_iff.mpr fun i => continuous_sigmaMk.comp (e i).symm.continuous

private def
    CuspHoneycombClosedCover.homeomorph {ι X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (A : ι → Set X) (B : ι → Set Y) (e : ∀ i, A i ≃ₜ B i) (hAcov : ⋃ i, A i = Set.univ)
    (hAcl : ∀ i, IsClosed (A i)) (hAloc : LocallyFinite A) (hBcov : ⋃ i, B i = Set.univ)
    (hBcl : ∀ i, IsClosed (B i)) (hBloc : LocallyFinite B)
    (hglue : ∀ i j (x : A i) (y : A j), (x : X) = (y : X) ↔ (e i x : Y) = (e j y : Y)) : X ≃ₜ Y :=
  quotientHomeomorph (projection A) (projection B ∘ sigmaHomeomorph A B e)
    (projection_isQuotientMap hAcov hAcl hAloc)
    ((projection_isQuotientMap hBcov hBcl hBloc).comp (sigmaHomeomorph A B e).isQuotientMap)
    (fun a b => hglue a.1 b.1 a.2 b.2)

private theorem CuspHoneycombClosedCover.homeomorph_apply {ι X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (A : ι → Set X) (B : ι → Set Y) (e : ∀ i, A i ≃ₜ B i)
    (hAcov : ⋃ i, A i = Set.univ) (hAcl : ∀ i, IsClosed (A i)) (hAloc : LocallyFinite A)
    (hBcov : ⋃ i, B i = Set.univ) (hBcl : ∀ i, IsClosed (B i)) (hBloc : LocallyFinite B)
    (hglue : ∀ i j (x : A i) (y : A j), (x : X) = (y : X) ↔ (e i x : Y) = (e j y : Y)) (i : ι)
    (x : A i) : homeomorph A B e hAcov hAcl hAloc hBcov hBcl hBloc hglue (x : X) = (e i x : Y) :=
  quotientHomeomorph_apply _ _ _ _ _ (⟨i, x⟩ : Σ i, A i)

private def CuspHoneycomb.honeycombHomeomorph (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    (CuspHoneycombTiling.Plane) ≃ₜ CuspPositiveRetraction.PositiveCentralFibre :=
  CuspHoneycombClosedCover.homeomorph CuspHoneycombTiling.cell CuspHoneycombPositive.positiveCell
    (cellHomeomorph C₀) CuspHoneycombTiling.iUnion_cell CuspHoneycombTiling.cell_isClosed
    CuspHoneycombTiling.cell_locallyFinite CuspHoneycombPositive.iUnion_positiveCell
    CuspHoneycombPositive.positiveCell_isClosed CuspHoneycombPositive.positiveCells_locallyFinite
    (fun v w x y => (cellHomeomorph_eq_iff C₀ v w x y).symm)

private theorem CuspHoneycomb.honeycombHomeomorph_cell (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (v : (CuspHoneycombTiling.Lattice)) (x : CuspHoneycombTiling.cell v) :
    honeycombHomeomorph C₀ (x : (CuspHoneycombTiling.Plane)) =
      (cellHomeomorph C₀ v x : CuspPositiveRetraction.PositiveCentralFibre) :=
  CuspHoneycombClosedCover.homeomorph_apply CuspHoneycombTiling.cell
    CuspHoneycombPositive.positiveCell (cellHomeomorph C₀) CuspHoneycombTiling.iUnion_cell
    CuspHoneycombTiling.cell_isClosed CuspHoneycombTiling.cell_locallyFinite
    CuspHoneycombPositive.iUnion_positiveCell CuspHoneycombPositive.positiveCell_isClosed
    CuspHoneycombPositive.positiveCells_locallyFinite
    (fun v w x y => (cellHomeomorph_eq_iff C₀ v w x y).symm) v x

private theorem CuspHoneycomb.honeycombHomeomorph_cell_coe (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (v : (CuspHoneycombTiling.Lattice)) (x : CuspHoneycombTiling.cell v) :
    ((honeycombHomeomorph C₀ (x : (CuspHoneycombTiling.Plane))).1 : ToricSpace.Space) =
      ToricSpace.twistedTranslate (CuspPositive.positiveTwist C₀) (-ToricSpace.cuspVector v)
        ((CuspHoneycombHexagon.compatibleCellHomeomorph C₀
              ((CuspHoneycombTiling.cellTranslationHomeomorph v).symm x)).1 :
          ToricSpace.Space) := by rw [honeycombHomeomorph_cell, cellHomeomorph_coe]

private theorem
    CuspHoneycomb.honeycombHomeomorph_mem_positiveCell_iff (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (v : (CuspHoneycombTiling.Lattice)) (x : (CuspHoneycombTiling.Plane)) :
    honeycombHomeomorph C₀ x ∈ CuspHoneycombPositive.positiveCell v ↔
      x ∈ CuspHoneycombTiling.cell v := by
  obtain ⟨w, hw⟩ := CuspHoneycombTiling.exists_mem_cell x
  rw [honeycombHomeomorph_cell C₀ w ⟨x, hw⟩]
  exact cellHomeomorph_mem_positiveCell_iff C₀ w v ⟨x, hw⟩

private theorem CuspHoneycomb.cellHomeomorph_translate (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (u v : (CuspHoneycombTiling.Lattice)) (x : CuspHoneycombTiling.cell v) :
    (cellHomeomorph C₀ (v + ToricSpace.cuspVector u)
          (CuspHoneycombTiling.cellShiftHomeomorph v (ToricSpace.cuspVector u) x) :
        CuspPositiveRetraction.PositiveCentralFibre) =
      CuspCollapse.positiveCentralTranslate C₀ u (cellHomeomorph C₀ v x) := by
  have hnorm :
    (CuspHoneycombTiling.cellTranslationHomeomorph (v + ToricSpace.cuspVector u)).symm
        (CuspHoneycombTiling.cellShiftHomeomorph v (ToricSpace.cuspVector u) x) =
      (CuspHoneycombTiling.cellTranslationHomeomorph v).symm x := by
    apply Subtype.ext
    change
      ((x : (CuspHoneycombTiling.Plane)) +
            CuspHoneycombTiling.latticePoint (ToricSpace.cuspVector u)) -
          CuspHoneycombTiling.latticePoint (v + ToricSpace.cuspVector u) =
        (x : (CuspHoneycombTiling.Plane)) - CuspHoneycombTiling.latticePoint v
    rw [CuspHoneycombTiling.latticePoint_add]
    abel
  have hu : -ToricSpace.cuspVector (v + ToricSpace.cuspVector u) = u + -ToricSpace.cuspVector v :=
    by
    rw [ToricSpace.cuspVector_add, ToricSpace.cuspVector_cuspVector]
    abel
  apply Subtype.ext
  apply Subtype.ext
  simp only [cellHomeomorph_coe, CuspCollapse.positiveCentralTranslate_coe, hnorm]
  rw [ToricSpace.twistedTranslate_add, hu]

private theorem CuspHoneycomb.honeycombHomeomorph_equivariant (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (u : (CuspHoneycombTiling.Lattice)) (x : (CuspHoneycombTiling.Plane)) :
    honeycombHomeomorph C₀ (x + CuspHoneycombTiling.latticePoint (ToricSpace.cuspVector u)) =
      CuspCollapse.positiveCentralTranslate C₀ u (honeycombHomeomorph C₀ x) := by
  obtain ⟨v, hx⟩ := CuspHoneycombTiling.exists_mem_cell x
  let a : CuspHoneycombTiling.cell v := ⟨x, hx⟩
  have ha : (a : (CuspHoneycombTiling.Plane)) = x := rfl
  have hshift :=
    honeycombHomeomorph_cell C₀ (v + ToricSpace.cuspVector u)
      (CuspHoneycombTiling.cellShiftHomeomorph v (ToricSpace.cuspVector u) a)
  have hbase :=
    congrArg (CuspCollapse.positiveCentralTranslate C₀ u) (honeycombHomeomorph_cell C₀ v a).symm
  simpa only [CuspHoneycombTiling.cellShiftHomeomorph_coe, ha] using
    hshift.trans ((cellHomeomorph_translate C₀ u v a).trans hbase)

private theorem CuspHoneycomb.honeycombHomeomorph_add_latticePoint (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (v : (CuspHoneycombTiling.Lattice)) (x : (CuspHoneycombTiling.Plane)) :
    honeycombHomeomorph C₀ (x + CuspHoneycombTiling.latticePoint v) =
      CuspCollapse.positiveCentralTranslate C₀ (-ToricSpace.cuspVector v)
        (honeycombHomeomorph C₀ x) := by
  simpa only [ToricSpace.cuspVector_neg, ToricSpace.cuspVector_cuspVector, neg_neg] using
    honeycombHomeomorph_equivariant C₀ (-ToricSpace.cuspVector v) x

private theorem CuspHoneycomb.honeycombHomeomorph_symm_equivariant (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (u : (CuspHoneycombTiling.Lattice)) (q : CuspPositiveRetraction.PositiveCentralFibre) :
    (honeycombHomeomorph C₀).symm (CuspCollapse.positiveCentralTranslate C₀ u q) =
      (honeycombHomeomorph C₀).symm q +
        CuspHoneycombTiling.latticePoint (ToricSpace.cuspVector u) := by
  apply (honeycombHomeomorph C₀).injective
  rw [Homeomorph.apply_symm_apply, honeycombHomeomorph_equivariant, Homeomorph.apply_symm_apply]

private theorem CuspHoneycomb.standardHexagonDualHomeomorph_vertex_coe (i : Fin 6) :
    (CuspHoneycombTiling.standardHexagonDualHomeomorph
          ⟨CuspHoneycombHexagon.vertex i, (CuspHoneycombHexagon.vertex_mem_side_self i).1⟩ :
        (CuspHoneycombTiling.Plane)) =
      CuspHoneycombTiling.triangleBarycenter (ToricComponent.zeroTriangle i) :=
  CuspHoneycombTiling.dual_standard_vertex i

private theorem CuspHoneycomb.compatibleCellHomeomorph_vertex (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (i : Fin 6) :
    CuspHoneycombHexagon.compatibleCellHomeomorph C₀
        (CuspHoneycombTiling.standardHexagonDualHomeomorph
          ⟨CuspHoneycombHexagon.vertex i, (CuspHoneycombHexagon.vertex_mem_side_self i).1⟩) =
      CuspHoneycombHexagon.squarePoint i CuspHoneycombHexagon.cornerZero := by
  simpa only [CuspHoneycombHexagon.sideIntervalHomeomorph_one,
    CuspHoneycombHexagon.compatibleBoundaryArc_one_point] using
    CuspHoneycombHexagon.compatibleCellHomeomorph_sideInterval C₀ i 1

private theorem CuspHoneycomb.triangleBarycenter_zeroTriangle_mem_baseCell (i : Fin 6) :
    CuspHoneycombTiling.triangleBarycenter (ToricComponent.zeroTriangle i) ∈
      CuspHoneycombTiling.baseCell := by
  rw [← standardHexagonDualHomeomorph_vertex_coe i]
  exact
    (CuspHoneycombTiling.standardHexagonDualHomeomorph
        ⟨CuspHoneycombHexagon.vertex i, (CuspHoneycombHexagon.vertex_mem_side_self i).1⟩).2

private theorem
    CuspHoneycomb.compatibleCellHomeomorph_triangleBarycenter (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (i : Fin 6) :
    CuspHoneycombHexagon.compatibleCellHomeomorph C₀
        ⟨CuspHoneycombTiling.triangleBarycenter (ToricComponent.zeroTriangle i),
          triangleBarycenter_zeroTriangle_mem_baseCell i⟩ =
      CuspHoneycombHexagon.squarePoint i CuspHoneycombHexagon.cornerZero := by
  have hi :
    (⟨CuspHoneycombTiling.triangleBarycenter (ToricComponent.zeroTriangle i),
          triangleBarycenter_zeroTriangle_mem_baseCell i⟩ :
        CuspHoneycombTiling.baseCell) =
      CuspHoneycombTiling.standardHexagonDualHomeomorph
        ⟨CuspHoneycombHexagon.vertex i, (CuspHoneycombHexagon.vertex_mem_side_self i).1⟩ := by
    apply Subtype.ext
    exact (standardHexagonDualHomeomorph_vertex_coe i).symm
  rw [hi, compatibleCellHomeomorph_vertex]

private theorem CuspHoneycomb.compatibleCellHomeomorph_triangleBarycenter_coe
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (i : Fin 6) :
    ((CuspHoneycombHexagon.compatibleCellHomeomorph C₀
            ⟨CuspHoneycombTiling.triangleBarycenter (ToricComponent.zeroTriangle i),
              triangleBarycenter_zeroTriangle_mem_baseCell i⟩).1 :
        ToricSpace.Space) =
      ToricSpace.inclusion (ToricComponent.zeroTriangle i) 0 := by
  rw [compatibleCellHomeomorph_triangleBarycenter,
    CuspHoneycombHexagon.squarePoint_cornerZero_coe]

private theorem CuspHoneycomb.honeycombHomeomorph_zeroTriangleBarycenter_coe
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (i : Fin 6) :
    ((honeycombHomeomorph C₀
            (CuspHoneycombTiling.triangleBarycenter (ToricComponent.zeroTriangle i))).1 :
        ToricSpace.Space) =
      ToricSpace.inclusion (ToricComponent.zeroTriangle i) 0 := by
  let a : CuspHoneycombTiling.baseCell :=
    ⟨CuspHoneycombTiling.triangleBarycenter (ToricComponent.zeroTriangle i),
      triangleBarycenter_zeroTriangle_mem_baseCell i⟩
  let x : CuspHoneycombTiling.cell 0 := CuspHoneycombTiling.cellTranslationHomeomorph 0 a
  have hx :
    (x : (CuspHoneycombTiling.Plane)) =
      CuspHoneycombTiling.triangleBarycenter (ToricComponent.zeroTriangle i) := by
    change
      (a : (CuspHoneycombTiling.Plane)) + CuspHoneycombTiling.latticePoint 0 =
        CuspHoneycombTiling.triangleBarycenter (ToricComponent.zeroTriangle i)
    rw [CuspHoneycombTiling.latticePoint_zero, add_zero]
  have hnorm : (CuspHoneycombTiling.cellTranslationHomeomorph 0).symm x = a :=
    (CuspHoneycombTiling.cellTranslationHomeomorph 0).symm_apply_apply a
  have h := honeycombHomeomorph_cell_coe C₀ 0 x
  rw [hx, hnorm, ToricSpace.cuspVector_zero, neg_zero, ToricSpace.twistedTranslate_zero] at h
  exact h.trans (compatibleCellHomeomorph_triangleBarycenter_coe C₀ i)

private theorem CuspHoneycomb.triangle_eq_zeroTriangle_shift (s : ToricFan.Triangle) :
    ∃ i : Fin 6,
      ∃ v : (CuspHoneycombTiling.Lattice), s = (ToricComponent.zeroTriangle i).shift v := by
  rcases s with ⟨a, b, u⟩
  cases u
  · refine ⟨0, ![a, b], ?_⟩
    ext <;> simp [ToricComponent.zeroTriangle, ToricFan.Triangle.shift]
  · refine ⟨1, ![a + 1, b], ?_⟩
    ext <;> simp [ToricComponent.zeroTriangle, ToricFan.Triangle.shift]

private theorem
    CuspHoneycomb.honeycombHomeomorph_triangleBarycenter_coe (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (s : ToricFan.Triangle) :
    ((honeycombHomeomorph C₀ (CuspHoneycombTiling.triangleBarycenter s)).1 : ToricSpace.Space) =
      ToricSpace.inclusion s 0 := by
  obtain ⟨i, v, rfl⟩ := triangle_eq_zeroTriangle_shift s
  rw [CuspHoneycombTiling.triangleBarycenter_shift, honeycombHomeomorph_add_latticePoint,
    CuspCollapse.positiveCentralTranslate_coe, honeycombHomeomorph_zeroTriangleBarycenter_coe,
    ToricSpace.twistedTranslate_origin, ToricSpace.cuspVector_neg,
    ToricSpace.cuspVector_cuspVector, neg_neg]

private abbrev CuspHoneycomb.PhasePlane :=
  ToricSpace.CompactFibreTorus × (CuspHoneycombTiling.Plane)

private def CuspHoneycomb.phaseCoordinatesHomeomorph (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    PhasePlane ≃ₜ CuspCollapse.PhasePositiveSpace :=
  (Homeomorph.refl ToricSpace.CompactFibreTorus).prodCongr (honeycombHomeomorph C₀)

private def CuspHoneycomb.honeycombPolarMap (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    PhasePlane → CuspRetraction.CentralFibre :=
  CuspCollapse.centralPolarMap ∘ phaseCoordinatesHomeomorph C₀

private theorem CuspHoneycomb.honeycombPolarMap_surjective (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    Function.Surjective (honeycombPolarMap C₀) :=
  CuspCollapse.centralPolarMap_surjective.comp (phaseCoordinatesHomeomorph C₀).surjective

private def CuspHoneycomb.honeycombDeckMap (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ)
    (p : PhasePlane) : PhasePlane :=
  (CuspCollapse.deckFibrePhase C₀ v * p.1,
    p.2 + CuspHoneycombTiling.latticePoint (ToricSpace.cuspVector v))

private def
    CuspHoneycomb.honeycombCollapseMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) :
    PhasePlane → CuspRetraction.QuotientCentralFibre C ε :=
  CuspCollapse.centralCollapseMap C ε hε ∘ phaseCoordinatesHomeomorph (C 0)

private theorem
    CuspHoneycomb.honeycombCollapseMap_continuous (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) : Continuous (honeycombCollapseMap C ε hε) :=
  (CuspCollapse.centralCollapseMap_continuous C ε hε).comp
    (phaseCoordinatesHomeomorph (C 0)).continuous

private theorem
    CuspHoneycomb.honeycombCollapseMap_surjective (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) : Function.Surjective (honeycombCollapseMap C ε hε) :=
  (CuspCollapse.centralCollapseMap_surjective C ε hε).comp
    (phaseCoordinatesHomeomorph (C 0)).surjective

private theorem CuspHoneycomb.honeycombCollapseMap_isQuotientMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε)) :
    Topology.IsQuotientMap (honeycombCollapseMap C ε hε) :=
  (CuspCollapse.centralCollapseMap_isQuotientMap C ε hε hC).comp
    (phaseCoordinatesHomeomorph (C 0)).isQuotientMap

private def
    CuspHoneycomb.honeycombCollapseRelation (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (p q : PhasePlane) :
    Prop :=
  ∃ v : Fin 2 → ℤ,
    p.2 = q.2 + CuspHoneycombTiling.latticePoint (ToricSpace.cuspVector v) ∧
      p.1⁻¹ * (CuspCollapse.deckFibrePhase C₀ v * q.1) ∈
        MulAction.stabilizer ToricSpace.CompactFibreTorus
          ((honeycombHomeomorph C₀ p.2).1 : ToricSpace.Space)

private theorem CuspHoneycomb.honeycombCollapseMap_eq_iff (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (p q : PhasePlane) :
    honeycombCollapseMap C ε hε p = honeycombCollapseMap C ε hε q ↔
      honeycombCollapseRelation (C 0) p q := by
  change
    CuspCollapse.centralCollapseMap C ε hε (phaseCoordinatesHomeomorph (C 0) p) =
        CuspCollapse.centralCollapseMap C ε hε (phaseCoordinatesHomeomorph (C 0) q) ↔
      _
  rw [CuspCollapse.centralCollapseMap_eq_iff]
  unfold CuspCollapse.centralCollapseRelation honeycombCollapseRelation
  apply exists_congr
  intro v
  change
    honeycombHomeomorph (C 0) p.2 =
          CuspCollapse.positiveCentralTranslate (C 0) v (honeycombHomeomorph (C 0) q.2) ∧
        _ ↔
      _
  rw [← honeycombHomeomorph_equivariant, (honeycombHomeomorph (C 0)).injective.eq_iff]
  rfl

private def
    ToricCharts.coordinateExp {d : ℕ} (z : CoordinateSpace d) : CoordinateSpace d := fun j =>
  Complex.exp (z j)

private theorem ToricCharts.coordinateExp_continuous {d : ℕ} : Continuous (@coordinateExp d) :=
  continuous_pi fun j => Complex.continuous_exp.comp (continuous_apply j)

private theorem ToricCharts.range_coordinateExp {d : ℕ} :
    Set.range (@coordinateExp d) = (torus : Set (CoordinateSpace d)) := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩ j
    exact Complex.exp_ne_zero (w j)
  · intro hz
    refine ⟨fun j => Complex.log (z j), ?_⟩
    funext j
    exact Complex.exp_log (hz j)

private theorem CuspQuotient.affineTube_isOpen (ε : ℝ) : IsOpen (affineTube ε) :=
  isOpen_lt ToricFan.Triangle.time_holomorphic.continuous.norm continuous_const

private theorem CuspQuotient.affineTube_isSimplyConnected {ε : ℝ} (hε : 0 < ε) :
    IsSimplyConnected (affineTube ε) := by
  let :=
    (affineTube_starConvex ε).contractibleSpace
      (show (affineTube ε).Nonempty from
        ⟨0, by simpa [affineTube, ToricFan.Triangle.time] using hε⟩)
  exact SimplyConnectedSpace.ofContractible _

private def CuspQuotient.logarithmicTube (ε : ℝ) : Set (ToricCharts.CoordinateSpace 3) :=
  {z | (z 0 + z 1 + z 2).re < Real.log ε}

private theorem CuspQuotient.logarithmicTube_convex (ε : ℝ) : Convex ℝ (logarithmicTube ε) := by
  apply convex_halfSpace_lt
  constructor
  · intro z w
    simp only [Pi.add_apply, Complex.add_re]
    ring
  · intro r z
    simp only [Pi.smul_apply, Complex.add_re, Complex.smul_re, smul_eq_mul]
    ring

private theorem CuspQuotient.logarithmicTube_nonempty (ε : ℝ) : (logarithmicTube ε).Nonempty := by
  refine ⟨![((Real.log ε - 1 : ℝ) : ℂ), 0, 0], ?_⟩
  simp [logarithmicTube]

private theorem CuspQuotient.norm_time_coordinateExp (z : ToricCharts.CoordinateSpace 3) :
    ‖ToricFan.Triangle.time (ToricCharts.coordinateExp z)‖ = Real.exp (z 0 + z 1 + z 2).re := by
  simp only [ToricFan.Triangle.time, ToricCharts.coordinateExp, ← Complex.exp_add,
    Complex.norm_exp]

private theorem CuspQuotient.coordinateExp_mem_affineTube_iff {ε : ℝ} (hε : 0 < ε)
    (z : ToricCharts.CoordinateSpace 3) :
    ToricCharts.coordinateExp z ∈ affineTube ε ↔ z ∈ logarithmicTube ε := by
  change
    ‖ToricFan.Triangle.time (ToricCharts.coordinateExp z)‖ < ε ↔ (z 0 + z 1 + z 2).re < Real.log ε
  rw [norm_time_coordinateExp]
  exact (Real.lt_log_iff_exp_lt hε).symm

private theorem CuspQuotient.coordinateExp_image_logarithmicTube {ε : ℝ} (hε : 0 < ε) :
    ToricCharts.coordinateExp '' logarithmicTube ε = ToricCharts.torus ∩ affineTube ε := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨fun j => Complex.exp_ne_zero _, (coordinateExp_mem_affineTube_iff hε w).mpr hw⟩
  · rintro ⟨hzT, hz⟩
    obtain ⟨w, rfl⟩ := ToricCharts.range_coordinateExp.symm ▸ hzT
    exact ⟨w, (coordinateExp_mem_affineTube_iff hε w).mp hz, rfl⟩

private theorem CuspQuotient.torus_inter_affineTube_isPathConnected {ε : ℝ} (hε : 0 < ε) :
    IsPathConnected (ToricCharts.torus ∩ affineTube ε) := by
  rw [← coordinateExp_image_logarithmicTube hε]
  exact
    ((logarithmicTube_convex ε).isPathConnected (logarithmicTube_nonempty ε)).image
      ToricCharts.coordinateExp_continuous

private theorem CuspQuotient.domain_inter_affineTube_isPathConnected (A : Matrix (Fin 3) (Fin 3) ℤ)
    {ε : ℝ} (hε : 0 < ε) : IsPathConnected (ToricCharts.domain A ∩ affineTube ε) := by
  apply
    ((ToricCharts.domain_open A).inter (affineTube_isOpen ε)).isConnected_iff_isPathConnected.mp
  apply (torus_inter_affineTube_isPathConnected hε).isConnected.subset_closure
  · exact fun _ hz => ⟨ToricCharts.torus_subset_domain A hz.1, hz.2⟩
  · intro z hz
    simpa only [Set.inter_comm] using
      (ToricCharts.torus_dense.open_subset_closure_inter (affineTube_isOpen ε) hz.2)

private theorem CuspQuotient.inclusion_affineTube_subset (s : ToricFan.Triangle) (ε : ℝ) :
    ToricSpace.inclusion s '' affineTube ε ⊆
      (ToricSpace.tubeOpen (disc ε) : Set ToricSpace.Space) := by
  rw [tube_eq_union]
  exact Set.subset_iUnion (fun t => ToricSpace.inclusion t '' affineTube ε) s

private theorem CuspQuotient.inclusion_affineTube_isOpen (s : ToricFan.Triangle) (ε : ℝ) :
    IsOpen (ToricSpace.inclusion s '' affineTube ε) :=
  (ToricSpace.inclusion_openEmbedding s).isOpenMap _ (affineTube_isOpen ε)

private theorem CuspQuotient.inclusion_affineTube_isSimplyConnected (s : ToricFan.Triangle) {ε : ℝ}
    (hε : 0 < ε) : IsSimplyConnected (ToricSpace.inclusion s '' affineTube ε) :=
  (ToricSpace.inclusion_openEmbedding s).isEmbedding.isSimplyConnected_image.mpr
    (affineTube_isSimplyConnected hε)

private theorem CuspQuotient.inclusion_affineTubes_inter (s t : ToricFan.Triangle) (ε : ℝ) :
    (ToricSpace.inclusion s '' affineTube ε) ∩ (ToricSpace.inclusion t '' affineTube ε) =
      ToricSpace.inclusion s ''
        (ToricCharts.domain (ToricFan.Triangle.transition s t) ∩ affineTube ε) := by
  ext x
  constructor
  · rintro ⟨⟨z, hz, rfl⟩, ⟨w, _, hw⟩⟩
    refine ⟨z, ⟨?_, hz⟩, rfl⟩
    simpa only [ToricFan.Triangle.chartChange_source] using
      ((ToricSpace.inclusion_eq_iff s t z w).mp hw.symm).1
  · rintro ⟨z, ⟨hzD, hz⟩, rfl⟩
    have hzS : z ∈ (ToricFan.Triangle.chartChange s t).source := by
      simpa only [ToricFan.Triangle.chartChange_source] using hzD
    refine ⟨⟨z, hz, rfl⟩, ToricFan.Triangle.chartChange s t z, ?_, ?_⟩
    · change ‖ToricFan.Triangle.time (ToricFan.Triangle.chartChange s t z)‖ < ε
      have he :
        ToricFan.Triangle.time (ToricFan.Triangle.chartChange s t z) = ToricFan.Triangle.time z :=
        ToricFan.Triangle.chartChange_preserves_time s t hzS
      rw [he]
      exact hz
    · exact ((ToricSpace.inclusion_eq_iff s t z _).mpr ⟨hzS, rfl⟩).symm

private theorem
    CuspQuotient.inclusion_affineTubes_inter_isPathConnected (s t : ToricFan.Triangle) {ε : ℝ}
    (hε : 0 < ε) :
    IsPathConnected
      ((ToricSpace.inclusion s '' affineTube ε) ∩ (ToricSpace.inclusion t '' affineTube ε)) := by
  rw [inclusion_affineTubes_inter]
  exact
    (domain_inter_affineTube_isPathConnected (ToricFan.Triangle.transition s t) hε).image
      (ToricSpace.inclusion_openEmbedding s).continuous

private def CuspQuotient.affineTubeChart (ε : ℝ) (s : ToricFan.Triangle) :
    Set (ToricSpace.Tube (disc ε)) :=
  Subtype.val ⁻¹' (ToricSpace.inclusion s '' affineTube ε)

private theorem CuspQuotient.affineTubeChart_isOpen (ε : ℝ) (s : ToricFan.Triangle) :
    IsOpen (affineTubeChart ε s) :=
  (inclusion_affineTube_isOpen s ε).preimage continuous_subtype_val

private theorem CuspQuotient.affineTubeChart_isSimplyConnected {ε : ℝ} (hε : 0 < ε)
    (s : ToricFan.Triangle) : IsSimplyConnected (affineTubeChart ε s) := by
  apply Topology.IsEmbedding.subtypeVal.isSimplyConnected_image.mp
  have he :
    (Subtype.val : ToricSpace.Tube (disc ε) → ToricSpace.Space) '' affineTubeChart ε s =
      ToricSpace.inclusion s '' affineTube ε := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, inclusion_affineTube_subset s ε hx⟩, hx, rfl⟩
  rw [he]
  exact inclusion_affineTube_isSimplyConnected s hε

private theorem CuspQuotient.affineTubeCharts_inter_isPathConnected {ε : ℝ} (hε : 0 < ε)
    (s t : ToricFan.Triangle) : IsPathConnected (affineTubeChart ε s ∩ affineTubeChart ε t) := by
  change
    IsPathConnected
      ((Subtype.val : ToricSpace.Tube (disc ε) → ToricSpace.Space) ⁻¹'
        ((ToricSpace.inclusion s '' affineTube ε) ∩ (ToricSpace.inclusion t '' affineTube ε)))
  exact
    (inclusion_affineTubes_inter_isPathConnected s t hε).preimage_coe
      (Set.inter_subset_left.trans (inclusion_affineTube_subset s ε))

private theorem CuspQuotient.affineTubeCharts_cover (ε : ℝ) :
    ⋃ s : ToricFan.Triangle, affineTubeChart ε s = Set.univ := by
  unfold affineTubeChart
  rw [← Set.preimage_iUnion, ← tube_eq_union]
  ext x
  simp

private theorem CuspQuotient.tube_simplyConnected {ε : ℝ} (hε : 0 < ε) :
    SimplyConnectedSpace (ToricSpace.Tube (disc ε)) := by
  obtain ⟨x, hx⟩ := tube_charts_common_point hε
  have hxTube : x ∈ (ToricSpace.tubeOpen (disc ε) : Set ToricSpace.Space) :=
    inclusion_affineTube_subset ToricSpace.referenceTriangle ε
      (Set.mem_iInter.mp hx ToricSpace.referenceTriangle)
  exact
    simplyConnectedSpace_of_open_cover (affineTubeChart ε) (affineTubeChart_isOpen ε)
      (affineTubeCharts_cover ε) (affineTubeChart_isSimplyConnected hε) ⟨x, hxTube⟩
      (fun s => Set.mem_iInter.mp hx s) (affineTubeCharts_inter_isPathConnected hε)

private theorem CuspQuotient.quotient_pathConnected (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) : PathConnectedSpace (QuotientSpace C ε) := by
  let : SimplyConnectedSpace (ToricSpace.Tube (disc ε)) := tube_simplyConnected hε
  have hq : Function.Surjective (quotientMap C ε) := Quotient.mk_surjective
  exact hq.pathConnectedSpace (quotientMap_continuous C ε)

private def
    CuspQuotient.fundamentalGroupEquivAt (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (e : ToricSpace.Tube (disc ε)) :
    FundamentalGroup (QuotientSpace C ε) (quotientMap C ε e) ≃* LatticeGroup := by
  let := ToricSpace.tubeAction C (disc ε)
  let := tube_simplyConnected hε
  let hq := quotientMap_covering C ε hε hε1 hC hR
  exact (hq.fundamentalGroupEquiv ⟨e, rfl⟩).trans MulOpposite.opMulEquiv.symm

private def
    CuspQuotient.fundamentalGroupEquiv (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (x : QuotientSpace C ε) :
    FundamentalGroup (QuotientSpace C ε) x ≃* LatticeGroup := by
  let := ToricSpace.tubeAction C (disc ε)
  let := tube_simplyConnected hε
  let hq := quotientMap_covering C ε hε hε1 hC hR
  let e : quotientMap C ε ⁻¹' { x } := ⟨(hq.surjective x).choose, (hq.surjective x).choose_spec⟩
  exact (hq.fundamentalGroupEquiv e).trans MulOpposite.opMulEquiv.symm

private theorem
    CuspQuotient.fundamentalGroupEquivAt_monodromy (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (e : ToricSpace.Tube (disc ε))
    (γ : FundamentalGroup (QuotientSpace C ε) (quotientMap C ε e)) :
    letI := ToricSpace.tubeAction C (disc ε)
    ToricSpace.tubeTranslate C (disc ε) (fundamentalGroupEquivAt C ε hε hε1 hC hR e γ).toAdd e =
      ((quotientMap_covering C ε hε hε1 hC hR).isCoveringMap.monodromy γ ⟨e, rfl⟩ :
        ToricSpace.Tube (disc ε)) := by
  let := ToricSpace.tubeAction C (disc ε)
  let := tube_simplyConnected hε
  exact (quotientMap_covering C ε hε hε1 hC hR).unop_fundamentalGroupToMulOpposite_smul

private def CuspQuotient.singularH1Equiv (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (x : QuotientSpace C ε) :
    FirstHurewicz.SingularH1 (QuotientSpace C ε) ≃ₗ[ℤ] (Fin 2 → ℤ) := by
  let := quotient_pathConnected C ε hε
  exact FirstHurewicz.singularH1EquivOfPi1 x (fundamentalGroupEquiv C ε hε hε1 hC hR x)

private def ToricSpace.fibreCoordinatePhase (s : ToricFan.Triangle) (u : CompactFibreTorus) :
    CompactTorus := fun i =>
  ⟨factors s (compactTorusUnits (compactFibrePhase u)) i,
    mem_sphere_zero_iff_norm.mpr (norm_factors_compactTorusUnits s (compactFibrePhase u) i)⟩

@[simp]
private theorem ToricSpace.fibreCoordinatePhase_coe (s : ToricFan.Triangle) (u : CompactFibreTorus)
    (i : Fin 3) :
    (fibreCoordinatePhase s u i : ℂ) = factors s (compactTorusUnits (compactFibrePhase u)) i :=
  rfl

private theorem
    ToricSpace.fibreCoordinatePhase_prod (s : ToricFan.Triangle) (u : CompactFibreTorus) :
    ∏ i, fibreCoordinatePhase s u i = 1 := by
  apply Circle.ext
  change Circle.coeHom (∏ i, fibreCoordinatePhase s u i) = (1 : ℂ)
  rw [map_prod]
  change (∏ i, factors s (compactTorusUnits (compactFibrePhase u)) i) = 1
  simpa [compactFibrePhase, Fin.prod_univ_succ, ToricFan.Triangle.time, mul_assoc] using
    time_factors s (compactTorusUnits (compactFibrePhase u))

private theorem ToricSpace.monomial_rays_fibreCoordinatePhase (s : ToricFan.Triangle)
    (u : CompactFibreTorus) :
    ToricCharts.monomial s.rays (fun i => (fibreCoordinatePhase s u i : ℂ)) = fun i =>
      (compactFibrePhase u i : ℂ) :=
  monomial_rays_factors s (compactTorusUnits (compactFibrePhase u))

private theorem ToricSpace.compactFibreAction_inclusion_eq_self_iff_coordinatePhase
    (u : CompactFibreTorus) (s : ToricFan.Triangle) (z : ToricCharts.CoordinateSpace 3) :
    compactFibreAction u (ToricSpace.inclusion s z) = ToricSpace.inclusion s z ↔
      ∀ i, z i ≠ 0 → fibreCoordinatePhase s u i = 1 := by
  rw [compactFibreAction_eq_compact, compactTorusAction_inclusion_eq_self_iff]
  simp only [← fibreCoordinatePhase_coe, Circle.coe_eq_one]

private theorem ToricSpace.compactFibrePhase_vertexDifference (s : ToricFan.Triangle) (j k : Fin 3)
    (a : Circle) :
    compactFibrePhase (fun i => a ^ (s.vertex k i - s.vertex j i)) =
      rayCompactPhase (s.vertex j) a⁻¹ * rayCompactPhase (s.vertex k) a := by
  funext i
  fin_cases i <;> simp [compactFibrePhase, rayCompactPhase, zpow_sub, mul_comm]

private theorem ToricSpace.factors_vertexDifferencePhase (s : ToricFan.Triangle) (j k : Fin 3)
    (a : Circle) :
    factors s (fibreMultiplier (compactFibreUnits (fun i => a ^ (s.vertex k i - s.vertex j i)))) =
      (fun i => if i = j then (a : ℂ)⁻¹ else 1) * (fun i => if i = k then (a : ℂ) else 1) := by
  rw [← compactTorusUnits_compactFibrePhase, compactFibrePhase_vertexDifference, map_mul,
    factors_mul, factors_rayCompactPhase_vertex, factors_rayCompactPhase_vertex]
  rfl

private theorem ToricSpace.compactFibreAction_inclusion_eq_self_iff_of_at_most_one_zero
    (u : CompactFibreTorus) (s : ToricFan.Triangle) (z : ToricCharts.CoordinateSpace 3)
    (j : Fin 3) (hz : ∀ i, i ≠ j → z i ≠ 0) :
    compactFibreAction u (ToricSpace.inclusion s z) = ToricSpace.inclusion s z ↔ u = 1 := by
  constructor
  · intro h
    have hf := (compactFibreAction_inclusion_eq_self_iff_coordinatePhase u s z).mp h
    have hrest (i : Fin 3) (hij : i ≠ j) : fibreCoordinatePhase s u i = 1 := hf i (hz i hij)
    have hp : (∏ i, fibreCoordinatePhase s u i) = fibreCoordinatePhase s u j :=
      Finset.prod_eq_single j (fun i _ hij => hrest i hij) (by simp)
    have hj : fibreCoordinatePhase s u j = 1 := hp.symm.trans (fibreCoordinatePhase_prod s u)
    have hall : fibreCoordinatePhase s u = 1 := by
      funext i
      by_cases hij : i = j
      · simpa only [hij, Pi.one_apply] using hj
      · exact hrest i hij
    have hr := monomial_rays_fibreCoordinatePhase s u
    have hc : (fun i => (fibreCoordinatePhase s u i : ℂ)) = 1 := by
      rw [hall]
      rfl
    rw [hc, ToricCharts.monomial_ones] at hr
    funext i
    apply Circle.ext
    have hi := congrFun hr i.castSucc
    fin_cases i <;> simpa [compactFibrePhase] using hi.symm
  · rintro rfl
    exact compactFibreAction_one _

private theorem
    ToricSpace.compactFibreAction_inclusion_eq_self_iff_of_two_zero (u : CompactFibreTorus)
    (s : ToricFan.Triangle) (z : ToricCharts.CoordinateSpace 3) (j k : Fin 3) (hjk : j ≠ k)
    (hzj : z j = 0) (hzk : z k = 0) (hz : ∀ i, i ≠ j → i ≠ k → z i ≠ 0) :
    compactFibreAction u (ToricSpace.inclusion s z) = ToricSpace.inclusion s z ↔
      ∃ a : Circle, ∀ i : Fin 2, u i = a ^ (s.vertex k i - s.vertex j i) := by
  constructor
  · intro h
    have hf := (compactFibreAction_inclusion_eq_self_iff_coordinatePhase u s z).mp h
    have hrest (i : Fin 3) (hij : i ≠ j) (hik : i ≠ k) : fibreCoordinatePhase s u i = 1 :=
      hf i (hz i hij hik)
    have hp : fibreCoordinatePhase s u j * fibreCoordinatePhase s u k = 1 := by
      calc
        fibreCoordinatePhase s u j * fibreCoordinatePhase s u k =
            ∏ i ∈ ({ j, k } : Finset (Fin 3)), fibreCoordinatePhase s u i :=
          (Finset.prod_pair hjk).symm
        _ = ∏ i, fibreCoordinatePhase s u i := by
          apply Finset.prod_subset (Finset.subset_univ _)
          intro i _ hi
          have hi' : i ≠ j ∧ i ≠ k := by simpa using hi
          exact hrest i hi'.1 hi'.2
        _ = 1 := fibreCoordinatePhase_prod s u
    have hj : fibreCoordinatePhase s u j = (fibreCoordinatePhase s u k)⁻¹ :=
      eq_inv_iff_mul_eq_one.mpr hp
    let a := fibreCoordinatePhase s u k
    have hc :
      (fun i => (fibreCoordinatePhase s u i : ℂ)) =
        (fun i => if i = j then (a : ℂ)⁻¹ else 1) * (fun i => if i = k then (a : ℂ) else 1) := by
      funext i
      by_cases hij : i = j
      · subst i
        simp [hj, hjk, a]
      · by_cases hik : i = k
        · subst i
          simp [hjk.symm, a]
        · simp [hij, hik, hrest i hij hik]
    have hr := monomial_rays_fibreCoordinatePhase s u
    rw [hc, ToricCharts.monomial_mul, monomial_single_coordinate_phase,
      monomial_single_coordinate_phase] at hr
    refine ⟨a, ?_⟩
    intro i
    apply Circle.ext
    have hi := congrFun hr i.castSucc
    have hphase : compactFibrePhase u i.castSucc = u i := by fin_cases i <;> rfl
    rw [hphase] at hi
    change (u i : ℂ) = (a : ℂ) ^ (s.vertex k i - s.vertex j i)
    rw [ToricFan.Triangle.vertex, ToricFan.Triangle.vertex, zpow_sub₀ a.coe_ne_zero,
      div_eq_mul_inv]
    simpa only [Pi.mul_apply, inv_zpow, mul_comm] using hi.symm
  · rintro ⟨a, ha⟩
    have hu : u = fun i => a ^ (s.vertex k i - s.vertex j i) := funext ha
    rw [compactFibreAction, torusAction_inclusion_eq_self_iff, hu]
    intro i hi
    have hij : i ≠ j := fun hij => hi (hij ▸ hzj)
    have hik : i ≠ k := fun hik => hi (hik ▸ hzk)
    rw [factors_vertexDifferencePhase]
    simp [hij, hik]

@[simp]
private theorem ToricSpace.compactFibreAction_inclusion_zero (u : CompactFibreTorus)
    (s : ToricFan.Triangle) :
    compactFibreAction u (ToricSpace.inclusion s 0) = ToricSpace.inclusion s 0 := by
  rw [compactFibreAction, torusAction_inclusion_eq_self_iff]
  intro i hi
  exact (hi rfl).elim

private def ToricSpace.edgeCompactPhase (d : Fin 2 → ℤ) : Circle →* CompactFibreTorus
    where
  toFun a i := a ^ d i
  map_one' := by
    funext i
    exact one_zpow (d i)
  map_mul' a
    b := by
    funext i
    exact mul_zpow a b (d i)

private def ToricSpace.edgeCircle (d : Fin 2 → ℤ) : Subgroup CompactFibreTorus :=
  (edgeCompactPhase d).range

private theorem ToricSpace.mem_edgeCircle_iff (d : Fin 2 → ℤ) (u : CompactFibreTorus) :
    u ∈ edgeCircle d ↔ ∃ a : Circle, ∀ i : Fin 2, u i = a ^ d i := by
  change (∃ a : Circle, edgeCompactPhase d a = u) ↔ _
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, fun i => (congrFun ha i).symm⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, funext fun i => (ha i).symm⟩

private theorem ToricSpace.edgeCompactPhase_continuous (d : Fin 2 → ℤ) :
    Continuous (edgeCompactPhase d) := by
  apply continuous_pi
  intro i
  exact continuous_id.zpow (d i)

private theorem
    ToricSpace.compactFibre_stabilizer_eq_bot_of_at_most_one_zero (s : ToricFan.Triangle)
    (z : ToricCharts.CoordinateSpace 3) (j : Fin 3) (hz : ∀ i, i ≠ j → z i ≠ 0) :
    MulAction.stabilizer CompactFibreTorus (ToricSpace.inclusion s z) = ⊥ := by
  ext u
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_bot]
  exact compactFibreAction_inclusion_eq_self_iff_of_at_most_one_zero u s z j hz

private theorem ToricSpace.compactFibre_stabilizer_eq_edgeCircle_of_two_zero (s : ToricFan.Triangle)
    (z : ToricCharts.CoordinateSpace 3) (j k : Fin 3) (hjk : j ≠ k) (hzj : z j = 0)
    (hzk : z k = 0) (hz : ∀ i, i ≠ j → i ≠ k → z i ≠ 0) :
    MulAction.stabilizer CompactFibreTorus (ToricSpace.inclusion s z) =
      edgeCircle (s.vertex k - s.vertex j) := by
  ext u
  rw [MulAction.mem_stabilizer_iff, mem_edgeCircle_iff]
  exact compactFibreAction_inclusion_eq_self_iff_of_two_zero u s z j k hjk hzj hzk hz

private theorem ToricSpace.compactFibre_stabilizer_inclusion_zero (s : ToricFan.Triangle) :
    MulAction.stabilizer CompactFibreTorus (ToricSpace.inclusion s 0) = ⊤ := by
  ext u
  rw [MulAction.mem_stabilizer_iff]
  exact ⟨fun _ => Subgroup.mem_top u, fun _ => compactFibreAction_inclusion_zero u s⟩

private theorem CuspHoneycomb.honeycombHomeomorph_branchVertices (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (y : (CuspHoneycombTiling.Plane)) :
    ToricSpace.branchVertices ((honeycombHomeomorph C₀ y).1 : ToricSpace.Space) =
      {v : (CuspHoneycombTiling.Lattice) | y ∈ CuspHoneycombTiling.cell v} := by
  ext v
  exact honeycombHomeomorph_mem_positiveCell_iff C₀ v y

private theorem CuspHoneycomb.honeycombHomeomorph_branchCount (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (y : (CuspHoneycombTiling.Plane)) :
    ToricSpace.branchCount ((honeycombHomeomorph C₀ y).1 : ToricSpace.Space) =
      {v : (CuspHoneycombTiling.Lattice) | y ∈ CuspHoneycombTiling.cell v}.ncard := by
  rw [← ToricSpace.branchVertices_ncard, honeycombHomeomorph_branchVertices]

private theorem CuspHoneycombTiling.frontier_baseCell :
    frontier baseCell = ⋃ k : Fin 6, baseCell ∩ cell (ToricComponent.hexagonRay k) := by
  have hpre : dualStandardPlaneHomeomorph ⁻¹' CuspHoneycombHexagon.Hexagon = baseCell :=
    Set.ext dualStandardPlaneHomeomorph_mem_hexagon
  calc
    frontier baseCell = dualStandardPlaneHomeomorph ⁻¹' frontier CuspHoneycombHexagon.Hexagon := by
      rw [dualStandardPlaneHomeomorph.preimage_frontier, hpre]
    _ = ⋃ k : Fin 6, dualStandardPlaneHomeomorph ⁻¹' CuspHoneycombHexagon.side k := by
      rw [CuspHoneycombHexagon.frontier_hexagon, Set.preimage_iUnion]
    _ = ⋃ k : Fin 6, baseCell ∩ cell (ToricComponent.hexagonRay k) := by
      apply Set.iUnion_congr
      intro k
      rw [← dual_image_side, Homeomorph.image_eq_preimage_symm, Homeomorph.symm_symm]

private theorem CuspHoneycombTiling.mem_frontier_baseCell_iff (y : Plane) :
    y ∈ frontier baseCell ↔
      y ∈ baseCell ∧ ∃ v : CuspHoneycombTiling.Lattice, v ≠ 0 ∧ y ∈ cell v := by
  rw [frontier_baseCell, Set.mem_iUnion]
  constructor
  · rintro ⟨k, hy, hv⟩
    refine ⟨hy, ToricComponent.hexagonRay k, ?_, hv⟩
    fin_cases k <;> decide
  · rintro ⟨hy, v, hv, hyv⟩
    rcases (baseCell_inter_cell_nonempty_iff_hexagonRay v).mp ⟨y, hy, hyv⟩ with hz | ⟨k, rfl⟩
    · exact (hv hz).elim
    · exact ⟨k, hy, hyv⟩

private theorem CuspHoneycombTiling.mem_interior_baseCell_iff (y : Plane) :
    y ∈ interior baseCell ↔ ∀ v : CuspHoneycombTiling.Lattice, y ∈ cell v ↔ v = 0 := by
  constructor
  · intro hy v
    constructor
    · intro hyv
      by_contra hv
      have hf := (mem_frontier_baseCell_iff y).mpr ⟨interior_subset hy, v, hv, hyv⟩
      exact ((mem_interior_iff_notMem_frontier (interior_subset hy)).mp hy) hf
    · rintro rfl
      simpa only [cell_zero] using interior_subset hy
  · intro hy
    have hbase : y ∈ baseCell := by simpa only [cell_zero] using (hy 0).mpr rfl
    apply (mem_interior_iff_notMem_frontier hbase).mpr
    intro hf
    obtain ⟨_, v, hv, hyv⟩ := (mem_frontier_baseCell_iff y).mp hf
    exact hv ((hy v).mp hyv)

private theorem
    CuspHoneycombTiling.mem_interior_cell_iff (v : CuspHoneycombTiling.Lattice) (y : Plane) :
    y ∈ interior (cell v) ↔ ∀ w : CuspHoneycombTiling.Lattice, y ∈ cell w ↔ w = v := by
  have hpre : (Homeomorph.subRight (latticePoint v)) ⁻¹' baseCell = cell v := rfl
  have hint : y ∈ interior (cell v) ↔ y - latticePoint v ∈ interior baseCell := by
    rw [← hpre, ← Homeomorph.preimage_interior]
    rfl
  rw [hint, mem_interior_baseCell_iff]
  constructor
  · intro hy w
    have h := hy (w - v)
    rw [sub_latticePoint_mem_cell_iff, add_comm v (w - v), sub_add_cancel] at h
    exact h.trans sub_eq_zero
  · intro hy w
    rw [sub_latticePoint_mem_cell_iff, hy, add_eq_left]

private theorem CuspHoneycombTiling.containingCells_eq_singleton_iff (y : Plane)
    (v : CuspHoneycombTiling.Lattice) :
    {w : CuspHoneycombTiling.Lattice | y ∈ cell w} = { v } ↔ y ∈ interior (cell v) := by
  rw [mem_interior_cell_iff]
  exact Set.ext_iff

private theorem CuspHoneycombTiling.containingCells_ncard_eq_one_iff (y : Plane) :
    {v : CuspHoneycombTiling.Lattice | y ∈ cell v}.ncard = 1 ↔
      ∃ v : CuspHoneycombTiling.Lattice, y ∈ interior (cell v) := by
  rw [Set.ncard_eq_one]
  exact exists_congr fun v => containingCells_eq_singleton_iff y v

private theorem
    CuspHoneycomb.honeycombHomeomorph_branchCount_eq_one_iff (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (y : CuspHoneycombTiling.Plane) :
    ToricSpace.branchCount ((honeycombHomeomorph C₀ y).1 : ToricSpace.Space) = 1 ↔
      ∃ v : CuspHoneycombTiling.Lattice, y ∈ interior (CuspHoneycombTiling.cell v) := by
  rw [honeycombHomeomorph_branchCount, CuspHoneycombTiling.containingCells_ncard_eq_one_iff]

private theorem ToricSpace.compactFibre_stabilizer_eq_bot_of_branchVertices_singleton (x : Space)
    (v : Fin 2 → ℤ) (hx : branchVertices x = { v }) :
    MulAction.stabilizer CompactFibreTorus x = ⊥ := by
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  have hv : ToricSpace.inclusion s z ∈ rayDivisor v := by
    change v ∈ branchVertices (ToricSpace.inclusion s z)
    rw [hx]
    exact Set.mem_singleton v
  obtain ⟨j, _, hjv⟩ := (mem_rayDivisor_inclusion v s z).mp hv
  apply compactFibre_stabilizer_eq_bot_of_at_most_one_zero s z j
  intro i hij hzi
  have hi : s.vertex i ∈ branchVertices (ToricSpace.inclusion s z) :=
    (mem_rayDivisor_vertex s i z).mpr hzi
  have hiv : s.vertex i = v := by simpa only [hx, Set.mem_singleton_iff] using hi
  exact hij (s.vertex_injective (hiv.trans hjv.symm))

private theorem CuspHoneycomb.honeycombHomeomorph_stabilizer_eq_bot (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (y : (CuspHoneycombTiling.Plane)) (v : (CuspHoneycombTiling.Lattice))
    (hcells : {u : (CuspHoneycombTiling.Lattice) | y ∈ CuspHoneycombTiling.cell u} = { v }) :
    MulAction.stabilizer ToricSpace.CompactFibreTorus
        ((honeycombHomeomorph C₀ y).1 : ToricSpace.Space) =
      ⊥ :=
  ToricSpace.compactFibre_stabilizer_eq_bot_of_branchVertices_singleton _ v
    ((honeycombHomeomorph_branchVertices C₀ y).trans hcells)

private theorem CuspHoneycomb.honeycombHomeomorph_stabilizer_eq_bot_of_mem_interior
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (y : (CuspHoneycombTiling.Plane))
    (v : (CuspHoneycombTiling.Lattice)) (hy : y ∈ interior (CuspHoneycombTiling.cell v)) :
    MulAction.stabilizer ToricSpace.CompactFibreTorus
        ((honeycombHomeomorph C₀ y).1 : ToricSpace.Space) =
      ⊥ :=
  honeycombHomeomorph_stabilizer_eq_bot C₀ y v
    ((CuspHoneycombTiling.containingCells_eq_singleton_iff y v).mpr hy)

private theorem CuspHoneycomb.honeycombHomeomorph_stabilizer_triangleBarycenter
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (s : ToricFan.Triangle) :
    MulAction.stabilizer ToricSpace.CompactFibreTorus
        ((honeycombHomeomorph C₀ (CuspHoneycombTiling.triangleBarycenter s)).1 :
          ToricSpace.Space) =
      ⊤ := by
  rw [honeycombHomeomorph_triangleBarycenter_coe]
  exact ToricSpace.compactFibre_stabilizer_inclusion_zero s

end Mathoverflow1973

end
