/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
import LeanPool.ConnesRigidity.Paper.Section4.ChartDetectorMeasure

/-!
Concrete §4 A-coordinate detector transport and invariant-measure bound for
Zhou's dual kernel. Paper: §4.
-/

namespace Connes
namespace PaperAChartDetectorMeasure

open MeasureTheory
open Construction
open Construction.PaperKernel
open PaperDualTopology
open PaperDualHaar
open BinaryPontryaginDual
open PaperFiniteCharts
open PaperChartDetector
open PaperChartOrbits
open PaperChartMeasure
open PaperChartDetectorMeasure

noncomputable section

/- The concrete field, kernel, polynomial module, and compact dual types. Paper: §4.
-/
/--
The `k` construction used in the Connes rigidity formalization.
-/
abbrev k := Construction.k
/--
The `D` construction used in the Connes rigidity formalization.
-/
abbrev D := PaperKernel.D
/--
The `A` construction used in the Connes rigidity formalization.
-/
abbrev A := Construction.A
/--
The `CharacterSpace` construction used in the Connes rigidity formalization.
-/
abbrev CharacterSpace := PaperDualTopology.CharacterSpace

/-- The A-coordinate embedding into the first kernel summand. Paper: §4.
-/
def aCoordinateEmbedding (v : OpenAIPort.SymplecticIndex) :
    A →ₗ[k] D where
  toFun a := (a ⊗ₜ[k] LinearMap.proj v, 0)
  map_add' a b := by
    apply Prod.ext
    · rw [TensorProduct.add_tmul]
      rfl
    · simp
  map_smul' r a := by
    apply Prod.ext
    · rw [TensorProduct.smul_tmul]
      simp
    · simp

/-- The character's A-coordinate linear functional at one finite dual index. Paper: §4.
-/
def aChartLinear (χ : CharacterSpace)
    (v : OpenAIPort.SymplecticIndex) : A →ₗ[k] k :=
  (BinaryPontryaginDual.characterLinear (M := D)
    (Additive.toMul χ)).comp (aCoordinateEmbedding v)

/-- The finite polynomial-chart evaluation of an A-coordinate functional. Paper: §4.
-/
def aChartEvaluation (χ : CharacterSpace)
    (v : OpenAIPort.SymplecticIndex) (N : ℕ) (s : Fin 3)
    (x : PaperFiniteCharts.CoeffIndex N → k) : k :=
  aChartLinear χ v
    (PaperFiniteCharts.chartPoint N
      (PaperChartDetector.chartIndexOfCoefficients N s x))

/-- The affine coefficient data witnessing the chart evaluation is quadratic. Paper: §4.
-/
def aChartQuadraticData (χ : CharacterSpace)
    (v : OpenAIPort.SymplecticIndex) (N : ℕ) (s : Fin 3) :
    BooleanPolynomial.QuadraticData (PaperFiniteCharts.CoeffIndex N) :=
  { constantTerm := aChartLinear χ v (PaperFiniteCharts.basisVector s)
    linear := fun i => aChartLinear χ v
      (PaperFiniteCharts.coefficientVector N s i)
    quadratic := fun _ _ => 0 }

/-- The finite A-chart evaluation agrees with its coefficient data. Paper: §4. -/
theorem aChartEvaluation_eq_quadraticData_eval (χ : CharacterSpace)
    (v : OpenAIPort.SymplecticIndex) (N : ℕ) (s : Fin 3)
    (x : PaperFiniteCharts.CoeffIndex N → k) :
    (aChartQuadraticData χ v N s).eval x = aChartEvaluation χ v N s x := by
  dsimp [aChartEvaluation, aChartQuadraticData,
    BooleanPolynomial.QuadraticData.eval]
  rw [PaperChartDetector.chartPoint_ofCoefficients_eq_sum]
  simp only [map_add, map_sum, map_smul, smul_eq_mul]
  simp
  simp only [mul_comm]

/- Every finite A-chart evaluation has the paper's quadratic form. Paper: §4. -/
theorem aChartEvaluation_isQuadratic (χ : CharacterSpace)
    (v : OpenAIPort.SymplecticIndex) (N : ℕ) (s : Fin 3) :
    BooleanPolynomial.IsQuadratic (aChartEvaluation χ v N s) := by
  exact ⟨aChartQuadraticData χ v N s,
    aChartEvaluation_eq_quadraticData_eval χ v N s⟩

/- The finite index type for one A-coordinate chart level. Paper: §4.
-/
/--
The `AChartEvalIndex` construction used in the Connes rigidity formalization.
-/
abbrev AChartEvalIndex (N : ℕ) :=
  PaperChartDetector.ChartEvalIndex N

/-- The value of an A-coordinate functional on an evaluation index. Paper: §4.
-/
def aChartEvalValue (χ : CharacterSpace)
    (v : OpenAIPort.SymplecticIndex) (N : ℕ)
    (i : AChartEvalIndex N) : k :=
  aChartEvaluation χ v N i.1 i.2

/-- The nonzero support of one finite A-coordinate evaluation. Paper: §4.
-/
def aChartEvalSupport (χ : CharacterSpace)
    (v : OpenAIPort.SymplecticIndex) (N : ℕ) :
    Finset (AChartEvalIndex N) := by
  classical
  exact Finset.univ.filter
    (fun i => aChartEvalValue χ v N i ≠ 0)

/-- The finite A-chart support satisfies the twelve-detector bound. Paper: §4. -/
theorem aChart_support_card_bound (χ : CharacterSpace)
    (v : OpenAIPort.SymplecticIndex) (N : ℕ)
    (hactive : (aChartEvalSupport χ v N).Nonempty) :
    Fintype.card (AChartEvalIndex N) ≤
      12 * (aChartEvalSupport χ v N).card := by
  classical
  obtain ⟨⟨s, x⟩, hx⟩ := hactive
  have hPx : aChartEvaluation χ v N s ≠ 0 := by
    have hx' : aChartEvaluation χ v N s x ≠ 0 := by
      simpa [aChartEvalSupport, aChartEvalValue] using
        (Finset.mem_filter.mp hx).2
    intro hzero
    exact hx' (congrFun hzero x)
  have hquartic := PaperChartDetector.quadratic_support_card_bound
    (aChartEvaluation χ v N s)
    (aChartEvaluation_isQuadratic χ v N s) hPx
  let S := BooleanPolynomial.supportOn (aChartEvaluation χ v N s)
  have hsubset :
      (S.image (fun y => (s, y))) ⊆ aChartEvalSupport χ v N := by
    intro i hi
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hi
    have hy' : aChartEvaluation χ v N s y ≠ 0 := by
      exact (Finset.mem_filter.mp hy).2
    change (s, y) ∈ Finset.univ.filter
      (fun i => aChartEvalValue χ v N i ≠ 0)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy'⟩
  have hinj : Function.Injective
      (fun y : PaperFiniteCharts.CoeffIndex N → k => (s, y)) := by
    intro y z h
    exact congrArg Prod.snd h
  have hScard : S.card ≤ (aChartEvalSupport χ v N).card := by
    rw [← Finset.card_image_of_injective _ hinj]
    exact Finset.card_le_card hsubset
  have hcardIndex : Fintype.card (AChartEvalIndex N) =
      3 * Fintype.card (PaperFiniteCharts.CoeffIndex N → k) := by
    simp [AChartEvalIndex, PaperChartDetector.ChartEvalIndex]
  rw [hcardIndex]
  calc
    3 * Fintype.card (PaperFiniteCharts.CoeffIndex N → k) ≤
        3 * (4 * S.card) := Nat.mul_le_mul_left 3 hquartic
    _ = 12 * S.card := by omega
    _ ≤ 12 * (aChartEvalSupport χ v N).card :=
      Nat.mul_le_mul_left 12 hScard

/- The detector set for one A-coordinate chart point. Paper: §4.
-/
/--
The `aDetector` construction used in the Connes rigidity formalization.
-/
def aDetector (v : OpenAIPort.SymplecticIndex) (a : A) :
    Set CharacterSpace :=
  linearDetector (aCoordinateEmbedding v a)

/-- A-coordinate detector membership is its binary linear value. Paper: §4. -/
theorem mem_aDetector_iff (χ : CharacterSpace)
    (v : OpenAIPort.SymplecticIndex) (a : A) :
    χ ∈ aDetector v a ↔ aChartLinear χ v a = 1 := by
  rfl

/- The A-coordinate chart point indexed by evaluation coefficients. Paper: §4.
-/
/--
The `aChartPoint` construction used in the Connes rigidity formalization.
-/
def aChartPoint (N : ℕ) (i : AChartEvalIndex N) : A :=
  PaperFiniteCharts.chartPoint N
    (PaperChartDetector.chartIndexOfCoefficients N i.1 i.2)

/-- The active A-coordinate detector support at one finite level. Paper: §4.
-/
def aDetectorSupport (χ : CharacterSpace)
    (v : OpenAIPort.SymplecticIndex) (N : ℕ) :
    Finset (AChartEvalIndex N) := by
  classical
  exact Finset.univ.filter
    (fun i => χ ∈ aDetector v (aChartPoint N i))

/-- A-coordinate detector support matches chart-evaluation support. Paper: §4. -/
theorem aDetectorSupport_mem_iff (χ : CharacterSpace)
    (v : OpenAIPort.SymplecticIndex) (N : ℕ)
    (i : AChartEvalIndex N) :
    i ∈ aDetectorSupport χ v N ↔
      i ∈ aChartEvalSupport χ v N := by
  have hbool (z : k) : z ≠ 0 ↔ z = 1 := by
    constructor
    · exact BooleanPolynomial.eq_one_of_ne_zero z
    · intro hz
      rw [hz]
      exact one_ne_zero
  simp only [aDetectorSupport, aChartEvalSupport, Finset.mem_filter,
    Finset.mem_univ, true_and]
  rw [mem_aDetector_iff]
  rw [hbool]
  rfl

/- Reindexing preserves the active A-coordinate support cardinality. Paper: §4. -/
theorem aDetectorSupport_card_eq (χ : CharacterSpace)
    (v : OpenAIPort.SymplecticIndex) (N : ℕ) :
    (aDetectorSupport χ v N).card =
      (aChartEvalSupport χ v N).card := by
  have heq : aDetectorSupport χ v N = aChartEvalSupport χ v N := by
    ext i
    exact aDetectorSupport_mem_iff χ v N i
  rw [heq]

/- The active A-coordinate support satisfies the twelve-detector bound. Paper: §4. -/
theorem aDetectorSupport_card_bound (χ : CharacterSpace)
    (v : OpenAIPort.SymplecticIndex) (N : ℕ)
    (hactive : (aDetectorSupport χ v N).Nonempty) :
    Fintype.card (AChartEvalIndex N) ≤
      12 * (aDetectorSupport χ v N).card := by
  have hactiveEval : (aChartEvalSupport χ v N).Nonempty := by
    obtain ⟨i, hi⟩ := hactive
    exact ⟨i, (aDetectorSupport_mem_iff χ v N i).mp hi⟩
  calc
    Fintype.card (AChartEvalIndex N) ≤
        12 * (aChartEvalSupport χ v N).card :=
      aChart_support_card_bound χ v N hactiveEval
    _ = 12 * (aDetectorSupport χ v N).card := by
      rw [aDetectorSupport_card_eq]

/- The first action transports every A-chart point detector to the base detector. Paper: §4. -/
theorem paperThetaOne_A_inverse_transport
    (g : SpecialLinear.SL3) (a : A)
    (v : OpenAIPort.SymplecticIndex)
    (he : PaperKernel.sl3AAction g (PaperFiniteCharts.basisVector 0) = a) :
    Multiplicative.toAdd
        (paperThetaOneAddAction (g, 1)⁻¹)
        (a ⊗ₜ[k] LinearMap.proj v, 0) =
      (PaperFiniteCharts.basisVector 0 ⊗ₜ[k]
        LinearMap.proj v, 0) := by
  rw [paperThetaOneAddAction_apply]
  have hinvPair :
      ((g, (1 : PaperKernel.Q))⁻¹ : (PaperChartDetectorMeasure.H : Type)) =
        (g⁻¹, 1) := by
    -- Expose the componentwise inverse hidden by the group-carrier abbreviation.
    change (g⁻¹, (1 : PaperKernel.Q)⁻¹) = (g⁻¹, 1)
    rw [inv_one]
  rw [hinvPair, PaperKernel.paperThetaOneLinear_apply]
  apply Prod.ext
  · change PaperKernel.avStarAction g⁻¹ (1 : PaperKernel.Q)
      (a ⊗ₜ[k] LinearMap.proj v) =
        PaperFiniteCharts.basisVector 0 ⊗ₜ[k]
          LinearMap.proj v
    have hinv : PaperKernel.sl3AAction g⁻¹ a =
        PaperFiniteCharts.basisVector 0 := by
      rw [← he]
      simp
    have hs : (PaperKernel.sl3AAction g).symm a =
        PaperFiniteCharts.basisVector 0 := by
      change PaperKernel.sl3AAction g⁻¹ a = _
      exact hinv
    simp [PaperKernel.avStarAction,
      hs]
  · change PaperKernel.sl3CAction g⁻¹ (0 : PaperKernel.C) = 0
    exact (PaperKernel.sl3CAction g⁻¹).map_zero

/- All finite A-coordinate chart detectors have the base detector mass. Paper: §4. -/
theorem aChartDetector_measure_eq_base
    (μ : ProbabilityMeasure CharacterSpace)
    (hinv : IsInvariantPaperSL3SpectralMeasure μ)
    (v : OpenAIPort.SymplecticIndex) (N : ℕ)
    (i : PaperFiniteCharts.ChartIndex N) :
    (μ : Measure CharacterSpace)
        (aDetector v (PaperFiniteCharts.chartPoint N i)) =
      (μ : Measure CharacterSpace)
        (aDetector v (PaperFiniteCharts.basisVector 0)) := by
  rcases i with ⟨s, f, h⟩
  obtain ⟨g, hg⟩ := PaperChartOrbits.chartPoint_in_orbit N s f h
  exact detector_measure_eq_of_sl3_invariant μ hinv g
    (aCoordinateEmbedding v (PaperFiniteCharts.basisVector 0))
    (aCoordinateEmbedding v (PaperFiniteCharts.chartPoint N (s, f, h)))
    (by
      exact paperThetaOne_A_inverse_transport g
        (PaperFiniteCharts.chartPoint N (s, f, h)) v hg)

/- The active A-coordinate support in the original chart indexing. Paper: §4.
-/
/--
The `aChartDetectorSupport` construction used in the Connes rigidity formalization.
-/
def aChartDetectorSupport (χ : CharacterSpace)
    (v : OpenAIPort.SymplecticIndex) (N : ℕ) :
    Finset (PaperFiniteCharts.ChartIndex N) := by
  classical
  exact Finset.univ.filter
    (fun i => χ ∈ aDetector v (PaperFiniteCharts.chartPoint N i))

/-- Original chart detectors correspond to evaluation supports. Paper: §4. -/
theorem aChartDetectorSupport_mem_iff (χ : CharacterSpace)
    (v : OpenAIPort.SymplecticIndex) (N : ℕ)
    (i : PaperFiniteCharts.ChartIndex N) :
    i ∈ aChartDetectorSupport χ v N ↔
      PaperChartDetectorMeasure.chartEvalIndexEquiv N i ∈
        aChartEvalSupport χ v N := by
  have hbool (z : k) : z ≠ 0 ↔ z = 1 := by
    constructor
    · exact BooleanPolynomial.eq_one_of_ne_zero z
    · intro hz
      rw [hz]
      exact one_ne_zero
  simp only [aChartDetectorSupport, aChartEvalSupport, Finset.mem_filter,
    Finset.mem_univ, true_and]
  rw [mem_aDetector_iff, ← hbool]
  simp only [aChartEvalValue, aChartEvaluation,
    PaperChartDetectorMeasure.chartIndexOfCoefficients_equiv,
    PaperFiniteCharts.chartPoint]

/- Reindexing preserves the original A-chart detector support cardinality. Paper: §4. -/
theorem aChartDetectorSupport_card_eq (χ : CharacterSpace)
    (v : OpenAIPort.SymplecticIndex) (N : ℕ) :
    (aChartDetectorSupport χ v N).card =
      (aChartEvalSupport χ v N).card := by
  apply Finset.card_equiv (PaperChartDetectorMeasure.chartEvalIndexEquiv N)
  intro i
  exact aChartDetectorSupport_mem_iff χ v N i

/- The original A-chart detector support satisfies the twelve-detector bound. Paper: §4. -/
theorem aChartDetectorSupport_card_bound (χ : CharacterSpace)
    (v : OpenAIPort.SymplecticIndex) (N : ℕ)
    (hactive : (aChartDetectorSupport χ v N).Nonempty) :
    Fintype.card (PaperFiniteCharts.ChartIndex N) ≤
      12 * (aChartDetectorSupport χ v N).card := by
  have hactiveEval : (aChartEvalSupport χ v N).Nonempty := by
    obtain ⟨i, hi⟩ := hactive
    exact ⟨PaperChartDetectorMeasure.chartEvalIndexEquiv N i,
      (aChartDetectorSupport_mem_iff χ v N i).mp hi⟩
  have hcard := aChart_support_card_bound χ v N hactiveEval
  have hindex : Fintype.card (PaperFiniteCharts.ChartIndex N) =
      Fintype.card (AChartEvalIndex N) := by
    exact Fintype.card_congr (PaperChartDetectorMeasure.chartEvalIndexEquiv N)
  calc
    Fintype.card (PaperFiniteCharts.ChartIndex N) =
        Fintype.card (AChartEvalIndex N) := hindex
    _ ≤ 12 * (aChartEvalSupport χ v N).card := hcard
    _ = 12 * (aChartDetectorSupport χ v N).card := by
      rw [aChartDetectorSupport_card_eq]

/- The finite union of A-coordinate chart detectors. Paper: §4.
-/
/--
The `aDetectorUnion` construction used in the Connes rigidity formalization.
-/
def aDetectorUnion (v : OpenAIPort.SymplecticIndex) (N : ℕ) :
    Set CharacterSpace :=
  ⋃ i : PaperFiniteCharts.ChartIndex N,
    aDetector v (PaperFiniteCharts.chartPoint N i)

/-- Each finite A-coordinate detector union is measurable. Paper: §4. -/
theorem measurableSet_aDetectorUnion
    (v : OpenAIPort.SymplecticIndex) (N : ℕ) :
    MeasurableSet (aDetectorUnion v N) := by
  exact MeasurableSet.iUnion (fun i =>
    measurableSet_linearDetector
      (PaperFiniteCharts.chartPoint N i ⊗ₜ[k]
        LinearMap.proj v, 0))

/- Each finite A-coordinate detector union has the paper's measure bound. Paper: §4. -/
theorem aDetectorUnion_measure_le_twelve
    (μ : ProbabilityMeasure CharacterSpace)
    (hinv : IsInvariantPaperSL3SpectralMeasure μ)
    (v : OpenAIPort.SymplecticIndex) (N : ℕ) :
    (μ : Measure CharacterSpace) (aDetectorUnion v N) ≤
      12 * (μ : Measure CharacterSpace)
        (aDetector v (PaperFiniteCharts.basisVector 0)) := by
  let _ : Nonempty (PaperFiniteCharts.ChartIndex N) := inferInstance
  apply finite_detector_measure_bound μ
    (fun i : PaperFiniteCharts.ChartIndex N =>
      aDetector v (PaperFiniteCharts.chartPoint N i))
    ((μ : Measure CharacterSpace)
      (aDetector v (PaperFiniteCharts.basisVector 0)))
  · intro i
    exact measurableSet_linearDetector
      (PaperFiniteCharts.chartPoint N i ⊗ₜ[k]
        LinearMap.proj v, 0)
  · intro χ hχ
    have hactive : (aChartDetectorSupport χ v N).Nonempty := by
      rcases Set.mem_iUnion.mp hχ with ⟨i, hi⟩
      exact ⟨i, by
        simp only [aChartDetectorSupport, Finset.mem_filter,
          Finset.mem_univ, true_and]
        exact hi⟩
    have hcard := aChartDetectorSupport_card_bound χ v N hactive
    let _ : DecidablePred (fun i : PaperFiniteCharts.ChartIndex N =>
        χ ∈ aDetector v (PaperFiniteCharts.chartPoint N i)) :=
      Classical.decPred _
    let _ : Fintype {i : PaperFiniteCharts.ChartIndex N //
        χ ∈ aDetector v (PaperFiniteCharts.chartPoint N i)} := Fintype.ofFinite _
    have hsubcard :
        Nat.card {i : PaperFiniteCharts.ChartIndex N //
            χ ∈ aDetector v (PaperFiniteCharts.chartPoint N i)} =
          (aChartDetectorSupport χ v N).card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      simp [aChartDetectorSupport]
    simpa only [hsubcard] using hcard
  · intro i
    exact aChartDetector_measure_eq_base μ hinv v N i

/- Extending polynomial coefficients preserves an A-chart point. Paper: §4. -/
theorem aChartPoint_extend {N M : ℕ} (hNM : N ≤ M)
    (i : PaperFiniteCharts.ChartIndex N) :
    PaperFiniteCharts.chartPoint M
        (i.1, PaperFiniteCharts.extendCoefficients hNM i.2.1,
          PaperFiniteCharts.extendCoefficients hNM i.2.2) =
      PaperFiniteCharts.chartPoint N i := by
  simp [PaperFiniteCharts.chartPoint, PaperFiniteCharts.chartVector,
    PaperFiniteCharts.ofFn_extendCoefficients hNM i.2.1,
    PaperFiniteCharts.ofFn_extendCoefficients hNM i.2.2]

/- The finite A-coordinate detector unions are monotone. Paper: §4. -/
theorem aDetectorUnion_mono {N M : ℕ} (hNM : N ≤ M)
    (v : OpenAIPort.SymplecticIndex) :
    aDetectorUnion v N ⊆ aDetectorUnion v M := by
  intro χ hχ
  change χ ∈ ⋃ i : PaperFiniteCharts.ChartIndex N,
    aDetector v (PaperFiniteCharts.chartPoint N i) at hχ
  rcases Set.mem_iUnion.mp hχ with ⟨i, hi⟩
  let j : PaperFiniteCharts.ChartIndex M :=
    (i.1, PaperFiniteCharts.extendCoefficients hNM i.2.1,
      PaperFiniteCharts.extendCoefficients hNM i.2.2)
  refine Set.mem_iUnion.mpr ⟨j, ?_⟩
  rw [aChartPoint_extend hNM i]
  exact hi

/- The finite span generated by A-chart points. Paper: §4.
-/
/--
The `aChartSubmodule` construction used in the Connes rigidity formalization.
-/
def aChartSubmodule (N : ℕ) : Submodule k A :=
  Submodule.span k (Set.range (PaperFiniteCharts.chartPoint N))

/-- The retraction sends each finite square span into the A-chart span. Paper: §2 and §4. -/
theorem delta_mem_aChartSubmodule {N : ℕ} {c : PaperKernel.C}
    (hc : c ∈ PaperFiniteCharts.chartSubmodule N) :
    PaperKernel.delta c ∈ aChartSubmodule N := by
  induction hc using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rw [show PaperKernel.delta (PaperFiniteCharts.chartSquare N i) =
          PaperFiniteCharts.chartPoint N i by
        exact PaperKernel.delta_diagonal _]
      exact Submodule.subset_span ⟨i, rfl⟩
  | zero => simp [aChartSubmodule]
  | add x y hx hy ihx ihy =>
      simpa only [map_add] using (aChartSubmodule N).add_mem ihx ihy
  | smul r x hx ih =>
      simpa only [map_smul] using (aChartSubmodule N).smul_mem r ih

/- Every polynomial-module vector lies in some finite A-chart span. Paper: §4. -/
theorem aChartVector_mem_some_chart (a : A) :
    ∃ N, a ∈ aChartSubmodule N := by
  obtain ⟨N, hN⟩ := PaperChartSpan.diagonal_mem_some_chart a
  refine ⟨N, ?_⟩
  have h := delta_mem_aChartSubmodule (N := N) (c := PaperKernel.diagonal a) hN
  simpa only [PaperKernel.delta_diagonal] using h

/- The nonzero locus of one A-coordinate functional. Paper: §4.
-/
/--
The `aNonzeroLocus` construction used in the Connes rigidity formalization.
-/
def aNonzeroLocus (v : OpenAIPort.SymplecticIndex) :
    Set CharacterSpace :=
  {χ : CharacterSpace | aChartLinear χ v ≠ 0}

/- The finite A-coordinate detector unions exhaust the nonzero locus. Paper: §4. -/
theorem iUnion_aDetectorUnion_eq_aNonzeroLocus
    (v : OpenAIPort.SymplecticIndex) :
    (⋃ N : ℕ, aDetectorUnion v N) = aNonzeroLocus v := by
  ext χ
  change χ ∈ ⋃ N : ℕ, aDetectorUnion v N ↔
    aChartLinear χ v ≠ 0
  constructor
  · intro hχ
    rcases Set.mem_iUnion.mp hχ with ⟨N, hN⟩
    change χ ∈ ⋃ i : PaperFiniteCharts.ChartIndex N,
      aDetector v (PaperFiniteCharts.chartPoint N i) at hN
    rcases Set.mem_iUnion.mp hN with ⟨i, hi⟩
    have hone : aChartLinear χ v
        (PaperFiniteCharts.chartPoint N i) = 1 :=
      (mem_aDetector_iff χ v _).mp hi
    intro hzero
    have hzero' := congrArg
      (fun f : A →ₗ[k] k => f (PaperFiniteCharts.chartPoint N i)) hzero
    have h01 : (0 : k) = 1 := by
      simp [hone] at hzero'
    exact one_ne_zero h01.symm
  · intro hχ
    have hnonzero : ∃ a : A, aChartLinear χ v a ≠ 0 := by
      by_contra h
      apply hχ
      apply LinearMap.ext
      intro a
      exact Classical.byContradiction (fun hne => h ⟨a, hne⟩)
    obtain ⟨a, ha⟩ := hnonzero
    obtain ⟨N, haN⟩ := aChartVector_mem_some_chart a
    have hactive : ∃ i : PaperFiniteCharts.ChartIndex N,
        aChartLinear χ v (PaperFiniteCharts.chartPoint N i) ≠ 0 := by
      by_contra h
      apply ha
      have hker : aChartSubmodule N ≤ LinearMap.ker (aChartLinear χ v) := by
        apply Submodule.span_le.mpr
        rintro _ ⟨i, rfl⟩
        exact Classical.byContradiction (fun hne => h ⟨i, hne⟩)
      exact hker haN
    obtain ⟨i, hi⟩ := hactive
    refine Set.mem_iUnion.mpr ⟨N, ?_⟩
    change χ ∈ ⋃ i : PaperFiniteCharts.ChartIndex N,
      aDetector v (PaperFiniteCharts.chartPoint N i)
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    exact (mem_aDetector_iff χ v _).mpr
      (BooleanPolynomial.eq_one_of_ne_zero _ hi)

/- The exhausted A-coordinate nonzero locus has the twelve-detector bound. Paper: §4. -/
theorem aNonzeroLocus_measureReal_le_twelve
    (μ : ProbabilityMeasure CharacterSpace)
    (hinv : IsInvariantPaperSL3SpectralMeasure μ)
    (v : OpenAIPort.SymplecticIndex) :
    (μ : Measure CharacterSpace).real (aNonzeroLocus v) ≤
      12 * (μ : Measure CharacterSpace).real
        (aDetector v (PaperFiniteCharts.basisVector 0)) := by
  have hbound : ∀ N, (μ : Measure CharacterSpace).real
      (aDetectorUnion v N) ≤
        12 * (μ : Measure CharacterSpace).real
          (aDetector v (PaperFiniteCharts.basisVector 0)) := by
    intro N
    have hfinite : (12 : ENNReal) *
        (μ : Measure CharacterSpace)
          (aDetector v (PaperFiniteCharts.basisVector 0)) ≠ ⊤ := by
      exact ENNReal.mul_ne_top ENNReal.ofNat_ne_top
        (measure_ne_top (μ : Measure CharacterSpace) _)
    have hle := aDetectorUnion_measure_le_twelve μ hinv v N
    have hreal :=
      (ENNReal.toReal_le_toReal
        (measure_ne_top (μ : Measure CharacterSpace) _) hfinite).2 hle
    simpa only [measureReal_def, ENNReal.toReal_mul,
      ENNReal.toReal_ofNat] using hreal
  have h := measureReal_iUnion_le_of_monotone
    (μ : Measure CharacterSpace) (aDetectorUnion v)
    (fun _ _ hNM => aDetectorUnion_mono hNM v) hbound
  rw [iUnion_aDetectorUnion_eq_aNonzeroLocus] at h
  exact h

end
end PaperAChartDetectorMeasure
end Connes
