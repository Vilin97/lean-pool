/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
import LeanPool.ConnesRigidity.Paper.Section4.ChartMeasure
import LeanPool.ConnesRigidity.Paper.Section4.ChartSpan
import LeanPool.ConnesRigidity.Paper.Section4.ChartOrbits
import LeanPool.ConnesRigidity.Construction.PaperActionInstances
import LeanPool.ConnesRigidity.Foundation.OperatorAlgebra.SpectralDetection

/-!
Concrete §4 chart detector transport and the invariant-measure bound for
Zhou's dual kernel. Paper: §4.
-/

namespace Connes
namespace PaperChartDetectorMeasure

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

open PaperChartOrbits
open PaperChartMeasure

noncomputable section

/--
The `k` construction used in the Connes rigidity formalization.
-/
abbrev k := Construction.k
/--
The `D` construction used in the Connes rigidity formalization.
-/
abbrev D := PaperKernel.D
/--
The `H` construction used in the Connes rigidity formalization.
-/
abbrev H := Construction.actingGroup
/--
The `C` construction used in the Connes rigidity formalization.
-/
abbrev C := PaperKernel.C
/--
The `CharacterSpace` construction used in the Connes rigidity formalization.
-/
abbrev CharacterSpace := PaperDualTopology.CharacterSpace

/- The first paper kernel action in the additive dual model. Paper: §4.
-/
/--
The `paperThetaOneAddAction` construction used in the Connes rigidity formalization.
-/
def paperThetaOneAddAction : H →* Multiplicative (AddAut D) :=
  (MulAutMultiplicative D).toMonoidHom.comp
    PaperKernel.paperThetaOneHom

/-- Pointwise form of the first Zhou action in the additive model. -/
@[simp] theorem paperThetaOneAddAction_apply (h : H) (d : D) :
    Multiplicative.toAdd (paperThetaOneAddAction h) d =
      PaperKernel.paperThetaOneLinear h d := rfl

/-- The second paper kernel action reserved for the companion detector. Paper: §4.
-/
def paperThetaTwoAddAction : H →* Multiplicative (AddAut D) :=
  (MulAutMultiplicative D).toMonoidHom.comp
    PaperKernel.paperThetaTwoHom

/-- Pointwise form of the second Zhou action in the additive model. -/
@[simp] theorem paperThetaTwoAddAction_apply (h : H) (d : D) :
    Multiplicative.toAdd (paperThetaTwoAddAction h) d =
      PaperKernel.paperThetaTwoLinearHom h d := rfl

/-- In Zhou's detector corollary only the SL₃ subgroup is used. Paper: §4.
-/
def IsInvariantPaperSL3SpectralMeasure
    (μ : ProbabilityMeasure CharacterSpace) : Prop :=
  ∀ g : SpecialLinear.SL3,
    (μ : Measure CharacterSpace).map
      (paperDualCharacterAction paperThetaOneAddAction (g, 1)) = μ

/-- Full acting-group invariance implies the SL₃ invariance needed by §4. Paper: §4. -/
theorem IsInvariantPaperSL3SpectralMeasure.of_full
    (μ : ProbabilityMeasure CharacterSpace)
    (hinv : IsInvariantPaperSpectralMeasure paperThetaOneAddAction μ) :
    IsInvariantPaperSL3SpectralMeasure μ := by
  intro g
  exact hinv (g, 1)

/- The inverse first action transports every chart square to the base square. Paper: §4. -/
lemma paperThetaOne_inverse_transport (g : SpecialLinear.SL3) (e : C)
    (he : PaperKernel.sl3CAction g (PaperKernel.diagonal
      (PaperFiniteCharts.basisVector 0)) = e) :
    Multiplicative.toAdd (paperThetaOneAddAction (g, 1)⁻¹)
        (0, e) = (0, PaperKernel.diagonal (PaperFiniteCharts.basisVector 0)) := by
  apply Prod.ext
  · change PaperKernel.avStarAction g⁻¹ (1 : PaperKernel.Q)
        (0 : PaperKernel.AVStar) = 0
    simp [PaperKernel.avStarAction]
  · have hinv : PaperKernel.sl3CAction g⁻¹ e =
        PaperKernel.diagonal (PaperFiniteCharts.basisVector 0) := by
      rw [← he]
      have h := congrArg (fun f : PaperKernel.C →ₗ[Construction.k] PaperKernel.C =>
        f (PaperKernel.diagonal (PaperFiniteCharts.basisVector 0)))
        (PaperKernel.sl3CAction_inv_comp g)
      simpa only [LinearMap.comp_apply, LinearMap.id_apply] using h
    simpa [paperThetaOneAddAction, PaperKernel.paperThetaOneHom,
      PaperKernel.paperThetaOneLinearHom,
      PaperKernel.paperThetaOneLinear, PaperKernel.avStarAction, hinv]

/- The C-coordinate of a character in the paper's dual splitting. Paper: §4.
-/
/--
The `chartLinear` construction used in the Connes rigidity formalization.
-/
def chartLinear (χ : CharacterSpace) : C →ₗ[k] k :=
  (PaperDualHaar.characterCoordinatesEquiv χ).2

/-- The detector set associated with one C-coordinate. Paper: §4.
-/
def chartDetector (c : C) : Set CharacterSpace :=
  linearDetector (0, c)

/-- The C-coordinate agrees with direct character evaluation. Paper: §4. -/
theorem chartLinear_eval (χ : CharacterSpace) (c : C) :
    chartLinear χ c =
      BinaryPontryaginDual.characterLinear (M := D)
        (Additive.toMul χ) (0, c) := by
  exact PaperDualTopology.character_second_eval χ c

/- Detector membership is characterized by the coordinate value. Paper: §4. -/
theorem mem_chartDetector_iff (χ : CharacterSpace) (c : C) :
    χ ∈ chartDetector c ↔ chartLinear χ c = 1 := by
  change BinaryPontryaginDual.characterLinear (M := D)
      (Additive.toMul χ) (0, c) = 1 ↔ _
  rw [← chartLinear_eval]

/- Detector transport using only the SL₃ invariance present in Zhou §4. -/
theorem detector_measure_eq_of_sl3_invariant
    (μ : ProbabilityMeasure CharacterSpace)
    (hinv : IsInvariantPaperSL3SpectralMeasure μ)
    (g : SpecialLinear.SL3) (d e : D)
    (he : Multiplicative.toAdd
      (paperThetaOneAddAction (g, 1)⁻¹) e = d) :
    (μ : Measure CharacterSpace) (linearDetector e) =
      (μ : Measure CharacterSpace) (linearDetector d) := by
  have hmeas : Measurable
      (paperDualCharacterAction paperThetaOneAddAction (g, 1)) := by
    exact (PaperDualAutomorphism.dualCharacterEquiv_continuous
      (Multiplicative.toAdd
        (paperThetaOneAddAction (g, 1)))).measurable
  calc
    (μ : Measure CharacterSpace) (linearDetector e) =
        (Measure.map
          (paperDualCharacterAction paperThetaOneAddAction (g, 1)) μ)
          (linearDetector e) := by rw [hinv g]
    _ = (μ : Measure CharacterSpace)
        (paperDualCharacterAction paperThetaOneAddAction (g, 1) ⁻¹'
          linearDetector e) := by
      rw [Measure.map_apply hmeas (measurableSet_linearDetector e)]
    _ = (μ : Measure CharacterSpace) (linearDetector d) := by
      rw [paperDualCharacterAction_preimage_linearDetector
        paperThetaOneAddAction (g, 1) d e he]

/- All finite chart-square detectors share the base detector mass. Paper: §4. -/
theorem chartSquareDetector_measure_eq_base
    (μ : ProbabilityMeasure CharacterSpace)
    (hinv : IsInvariantPaperSL3SpectralMeasure μ)
    (N : ℕ) (i : ChartIndex N) :
    (μ : Measure CharacterSpace) (chartDetector (chartSquare N i)) =
      (μ : Measure CharacterSpace)
        (chartDetector (PaperKernel.diagonal (basisVector 0))) := by
  rcases i with ⟨s, f, h⟩
  obtain ⟨g, hg⟩ := chartSquare_in_orbit N s f h
  exact detector_measure_eq_of_sl3_invariant μ hinv g
    (0, PaperKernel.diagonal (basisVector 0))
    (0, chartSquare N (s, f, h))
    (paperThetaOne_inverse_transport g (chartSquare N (s, f, h)) hg)

/- The chart and evaluation parameterizations have the same finite index set. Paper: §4.
-/
/--
The `chartEvalIndexEquiv` construction used in the Connes rigidity formalization.
-/
def chartEvalIndexEquiv (N : ℕ) : ChartIndex N ≃ ChartEvalIndex N where
  toFun i := (i.1, fun x => Sum.elim i.2.1 i.2.2 x)
  invFun j := (j.1, (fun x => j.2 (Sum.inl x)), (fun x => j.2 (Sum.inr x)))
  left_inv i := by
    rcases i with ⟨s, f, h⟩
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · funext x
        rfl
      · funext x
        rfl
  right_inv j := by
    rcases j with ⟨s, x⟩
    apply Prod.ext
    · rfl
    · funext z
      cases z with
      | inl i => rfl
      | inr i => rfl

/-- Evaluation indices recover the original chart coefficients. Paper: §4. -/
theorem chartIndexOfCoefficients_equiv (N : ℕ) (i : ChartIndex N) :
    chartIndexOfCoefficients N (chartEvalIndexEquiv N i).1
        (chartEvalIndexEquiv N i).2 = i := by
  rcases i with ⟨s, f, h⟩
  apply Prod.ext
  · rfl
  · apply Prod.ext <;> funext x <;> rfl

/- Evaluation of a reindexed chart is the corresponding detector coordinate. Paper: §4. -/
theorem chartEvalValue_of_chartIndex (χ : CharacterSpace)
    (N : ℕ) (i : ChartIndex N) :
    chartEvalValue (chartLinear χ) N (chartEvalIndexEquiv N i) =
      chartLinear χ (chartSquare N i) := by
  simp [chartEvalValue, chartEvaluation,
    chartIndexOfCoefficients_equiv, chartSquare]

/- The active finite chart indices for one character. Paper: §4.
-/
/--
The `chartDetectorSupport` construction used in the Connes rigidity formalization.
-/
def chartDetectorSupport (χ : CharacterSpace) (N : ℕ) :
    Finset (ChartIndex N) := by
  classical
  exact Finset.univ.filter
    (fun i => χ ∈ chartDetector (chartSquare N i))

/-- Active detector indices correspond exactly to nonzero chart evaluations. Paper: §4. -/
theorem chartDetectorSupport_mem_iff (χ : CharacterSpace)
    (N : ℕ) (i : ChartIndex N) :
    i ∈ chartDetectorSupport χ N ↔
      chartEvalIndexEquiv N i ∈ chartEvalSupport (chartLinear χ) N := by
  classical
  have hbool (z : k) : z ≠ 0 ↔ z = 1 := by
    constructor
    · exact BooleanPolynomial.eq_one_of_ne_zero z
    · intro hz
      rw [hz]
      exact one_ne_zero
  change (i ∈ (Finset.univ.filter
      (fun j => χ ∈ chartDetector (chartSquare N j)))) ↔
    (chartEvalIndexEquiv N i ∈ (Finset.univ.filter
      (fun j => chartEvalValue (chartLinear χ) N j ≠ 0)))
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [mem_chartDetector_iff, chartEvalValue_of_chartIndex, hbool]

/- Reindexing preserves the cardinality of the active chart family. Paper: §4. -/
theorem chartDetectorSupport_card_eq (χ : CharacterSpace) (N : ℕ) :
    (chartDetectorSupport χ N).card =
      (chartEvalSupport (chartLinear χ) N).card := by
  apply Finset.card_equiv (chartEvalIndexEquiv N)
  intro i
  exact chartDetectorSupport_mem_iff χ N i

/- A finite detector family with the §4 pointwise cardinal bound has union
mass at most twelve times a common detector mass. Paper: §4. -/
theorem finite_detector_measure_bound
    {α I : Type*} [MeasurableSpace α] [Fintype I] [Nonempty I]
    (μ : Measure α) (family : I → Set α) (b : ENNReal)
    (hmeas : ∀ i, MeasurableSet (family i))
    (hcount : ∀ x, x ∈ ⋃ i, family i →
      Fintype.card I ≤
        12 * Nat.card {i : I // x ∈ family i})
    (hunif : ∀ i, μ (family i) = b) :
    μ (⋃ i, family i) ≤ 12 * b := by
  classical
  let U : Set α := ⋃ i, family i
  have hU : MeasurableSet U := MeasurableSet.iUnion hmeas
  have hsum (x : α) :
      ∑ i : I, (family i).indicator (1 : α → ENNReal) x =
        (Nat.card {i : I // x ∈ family i} : ENNReal) := by
    let _ : Fintype {i : I // x ∈ family i} := Fintype.ofFinite _
    have hcard : Fintype.card {i : I // x ∈ family i} =
        ∑ i : I, if x ∈ family i then 1 else 0 := by
      calc
        Fintype.card {i : I // x ∈ family i} =
            (Finset.univ.filter (fun i : I => x ∈ family i)).card := by
              rw [Fintype.card_subtype]
        _ = ∑ i : I, if x ∈ family i then 1 else 0 := by
              rw [Finset.card_eq_sum_ones]
              simp only [Finset.sum_filter]
    rw [Nat.card_eq_fintype_card]
    simpa only [Set.indicator, Pi.one_apply, Nat.cast_sum, Nat.cast_ite,
      Nat.cast_one, Nat.cast_zero] using
      (congrArg (fun n : ℕ => (n : ENNReal)) hcard).symm
  have hpoint (x : α) :
      (Fintype.card I : ENNReal) * U.indicator (1 : α → ENNReal) x ≤
      12 * ∑ i : I, (family i).indicator (1 : α → ENNReal) x := by
    by_cases hx : x ∈ U
    · rw [Set.indicator_of_mem hx, hsum]
      have hc : (Fintype.card I : ENNReal) ≤
          12 * (Nat.card {i : I // x ∈ family i} : ENNReal) := by
        exact_mod_cast hcount x hx
      simpa only [Pi.one_apply, mul_one] using hc
    · simp [Set.indicator, hx]
  have hlin := lintegral_mono (μ := μ) hpoint
  have hleft :
      ∫⁻ x, (Fintype.card I : ENNReal) * U.indicator
          (1 : α → ENNReal) x ∂μ =
        (Fintype.card I : ENNReal) * μ U := by
    rw [lintegral_const_mul _ (measurable_one.indicator hU)]
    rw [lintegral_indicator_one hU]
  have hright :
      ∫⁻ x, 12 * ∑ i : I, (family i).indicator
          (1 : α → ENNReal) x ∂μ =
        12 * ((Fintype.card I : ENNReal) * b) := by
    rw [lintegral_const_mul _
      (Finset.measurable_fun_sum _ fun _ _ =>
        measurable_one.indicator (hmeas _))]
    rw [lintegral_finsetSum _ fun _ _ =>
      measurable_one.indicator (hmeas _)]
    simp_rw [lintegral_indicator_one (hmeas _)]
    simp [hunif]
  rw [hleft, hright] at hlin
  have hm : (0 : ENNReal) < Fintype.card I := by
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance)
  apply (ENNReal.mul_le_mul_iff_left hm.ne' (by simp)).mp
  simpa [mul_assoc, mul_comm, mul_left_comm] using hlin

/- The abstract chart support bound becomes a cardinal bound for detector
fibers in the concrete dual model. Paper: §4. -/
theorem chartDetectorSupport_card_bound
    (χ : CharacterSpace) (N : ℕ)
    (hactive : (chartDetectorSupport χ N).Nonempty) :
    Fintype.card (ChartIndex N) ≤
      12 * (chartDetectorSupport χ N).card := by
  have hactiveEval : (chartEvalSupport (chartLinear χ) N).Nonempty := by
    obtain ⟨i, hi⟩ := hactive
    exact ⟨chartEvalIndexEquiv N i,
      (chartDetectorSupport_mem_iff χ N i).mp hi⟩
  have hquartic := PaperChartDetector.chart_support_card_bound
    (chartLinear χ) N hactiveEval
  have hcard : Fintype.card (ChartIndex N) =
      Fintype.card (ChartEvalIndex N) :=
    Fintype.card_congr (chartEvalIndexEquiv N)
  calc
    Fintype.card (ChartIndex N) = Fintype.card (ChartEvalIndex N) := hcard
    _ ≤ 12 * (chartEvalSupport (chartLinear χ) N).card := hquartic
    _ = 12 * (chartDetectorSupport χ N).card := by
      rw [chartDetectorSupport_card_eq]

/- The finite union of all chart-square detectors at one level. Paper: §4.
-/
/--
The `chartDetectorUnion` construction used in the Connes rigidity formalization.
-/
def chartDetectorUnion (N : ℕ) : Set CharacterSpace :=
  ⋃ i : ChartIndex N, chartDetector (chartSquare N i)

/-- Extending polynomial coefficients preserves the represented chart square. Paper: §4. -/
theorem chartSquare_extend {N M : ℕ} (hNM : N ≤ M) (i : ChartIndex N) :
    chartSquare M
        (i.1, extendCoefficients hNM i.2.1,
          extendCoefficients hNM i.2.2) =
      chartSquare N i := by
  simp [chartSquare, chartPoint, chartVector,
    ofFn_extendCoefficients hNM i.2.1,
    ofFn_extendCoefficients hNM i.2.2]

/- The finite detector unions form the monotone exhaustion used in §4. Paper: §4. -/
theorem chartDetectorUnion_mono {N M : ℕ} (hNM : N ≤ M) :
    chartDetectorUnion N ⊆ chartDetectorUnion M := by
  intro χ hχ
  change χ ∈ ⋃ i : ChartIndex N, chartDetector (chartSquare N i) at hχ
  rcases Set.mem_iUnion.mp hχ with ⟨i, hi⟩
  let j : ChartIndex M :=
    (i.1, extendCoefficients hNM i.2.1,
      extendCoefficients hNM i.2.2)
  refine Set.mem_iUnion.mpr ⟨j, ?_⟩
  rw [chartSquare_extend hNM i]
  exact hi

/- The locus detected by some finite chart level. Paper: §4.
-/
/--
The `chartNonzeroLocus` construction used in the Connes rigidity formalization.
-/
def chartNonzeroLocus : Set CharacterSpace :=
  {χ : CharacterSpace | chartLinear χ ≠ 0}

/- The chart unions exhaust the characters with nonzero C-coordinate. Paper: §4. -/
theorem iUnion_chartDetectorUnion_eq_chartNonzeroLocus :
    (⋃ N : ℕ, chartDetectorUnion N) =
      chartNonzeroLocus := by
  ext χ
  change χ ∈ ⋃ N : ℕ, chartDetectorUnion N ↔
    chartLinear χ ≠ 0
  constructor
  · intro hχ
    rcases Set.mem_iUnion.mp hχ with ⟨N, hN⟩
    change χ ∈ ⋃ i : ChartIndex N, chartDetector (chartSquare N i) at hN
    rcases Set.mem_iUnion.mp hN with ⟨i, hi⟩
    have hone : chartLinear χ (chartSquare N i) = 1 :=
      (mem_chartDetector_iff χ (chartSquare N i)).mp hi
    intro hzero
    have hzero' := congrArg
      (fun f : C →ₗ[k] k => f (chartSquare N i)) hzero
    have h01 : (0 : k) = 1 := by
      simp [hone] at hzero'
    exact one_ne_zero h01.symm
  · intro hχ
    have hnonzero : ∃ c : C, chartLinear χ c ≠ 0 := by
      by_contra h
      apply hχ
      ext c
      exact Classical.byContradiction (fun hne => h ⟨c, hne⟩)
    obtain ⟨c, hc⟩ := hnonzero
    obtain ⟨N, hcN⟩ :=
      PaperChartSpan.diagonal_mem_chart_some_level c
    have hactive : ∃ i : ChartIndex N,
        chartLinear χ (chartSquare N i) ≠ 0 := by
      by_contra h
      apply hc
      have hker : chartSubmodule N ≤ LinearMap.ker (chartLinear χ) := by
        apply Submodule.span_le.mpr
        rintro _ ⟨i, rfl⟩
        exact Classical.byContradiction (fun hne => h ⟨i, hne⟩)
      exact hker hcN
    obtain ⟨i, hi⟩ := hactive
    refine Set.mem_iUnion.mpr ⟨N, ?_⟩
    change χ ∈ ⋃ i : ChartIndex N, chartDetector (chartSquare N i)
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    exact (mem_chartDetector_iff χ (chartSquare N i)).mpr
      (BooleanPolynomial.eq_one_of_ne_zero _ hi)

/- Each finite chart detector union is measurable. Paper: §4. -/
theorem measurableSet_chartDetectorUnion (N : ℕ) :
    MeasurableSet (chartDetectorUnion N) := by
  exact MeasurableSet.iUnion (fun i =>
    measurableSet_linearDetector (0, chartSquare N i))

/- The finite §4 chart detector union has mass controlled by its base
detector. Paper: §4. -/
theorem chartDetectorUnion_measure_le_twelve
    (μ : ProbabilityMeasure CharacterSpace)
    (hinv : IsInvariantPaperSL3SpectralMeasure μ)
    (N : ℕ) :
    (μ : Measure CharacterSpace) (chartDetectorUnion N) ≤
      12 * (μ : Measure CharacterSpace)
        (chartDetector (PaperKernel.diagonal (basisVector 0))) := by
  let _ : Nonempty (ChartIndex N) := inferInstance
  apply finite_detector_measure_bound μ
    (fun i : ChartIndex N => chartDetector (chartSquare N i))
    ((μ : Measure CharacterSpace)
      (chartDetector (PaperKernel.diagonal (basisVector 0))))
  · intro i
    exact measurableSet_linearDetector (0, chartSquare N i)
  · intro χ hχ
    have hactive : (chartDetectorSupport χ N).Nonempty := by
      rcases Set.mem_iUnion.mp hχ with ⟨i, hi⟩
      exact ⟨i, by
        simp only [chartDetectorSupport, Finset.mem_filter, Finset.mem_univ,
          true_and]
        exact hi⟩
    have hcard := chartDetectorSupport_card_bound χ N hactive
    let _ : DecidablePred (fun i : ChartIndex N =>
        χ ∈ chartDetector (chartSquare N i)) := Classical.decPred _
    let _ : Fintype {i : ChartIndex N //
        χ ∈ chartDetector (chartSquare N i)} := Fintype.ofFinite _
    have hsubcard :
        Nat.card {i : ChartIndex N //
            χ ∈ chartDetector (chartSquare N i)} =
          (chartDetectorSupport χ N).card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      simp [chartDetectorSupport]
    simpa only [hsubcard] using hcard
  · intro i
    exact chartSquareDetector_measure_eq_base μ hinv N i

/- The exhausted nonzero C-coordinate locus obeys the same mass bound. Paper: §4. -/
theorem chartNonzeroLocus_measureReal_le_twelve
    (μ : ProbabilityMeasure CharacterSpace)
    (hinv : IsInvariantPaperSL3SpectralMeasure μ) :
    (μ : Measure CharacterSpace).real chartNonzeroLocus ≤
      12 * (μ : Measure CharacterSpace).real
        (chartDetector (PaperKernel.diagonal (basisVector 0))) := by
  have hbound : ∀ N, (μ : Measure CharacterSpace).real
      (chartDetectorUnion N) ≤
        12 * (μ : Measure CharacterSpace).real
          (chartDetector (PaperKernel.diagonal (basisVector 0))) := by
    intro N
    have hfinite : (12 : ENNReal) *
        (μ : Measure CharacterSpace)
          (chartDetector (PaperKernel.diagonal (basisVector 0))) ≠ ⊤ := by
      exact ENNReal.mul_ne_top ENNReal.ofNat_ne_top
        (measure_ne_top (μ : Measure CharacterSpace) _)
    have hle := chartDetectorUnion_measure_le_twelve μ hinv N
    have hreal :=
      (ENNReal.toReal_le_toReal
        (measure_ne_top (μ : Measure CharacterSpace) _) hfinite).2 hle
    simpa only [measureReal_def, ENNReal.toReal_mul,
      ENNReal.toReal_ofNat] using hreal
  have h := measureReal_iUnion_le_of_monotone
    (μ : Measure CharacterSpace) chartDetectorUnion
    (fun _ _ hNM => chartDetectorUnion_mono hNM) hbound
  rw [iUnion_chartDetectorUnion_eq_chartNonzeroLocus] at h
  exact h

end
end PaperChartDetectorMeasure
end Connes
