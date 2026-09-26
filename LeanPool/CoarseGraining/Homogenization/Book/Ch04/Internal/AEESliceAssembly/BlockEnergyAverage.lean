/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Internal.FixedCompetitorEnergyMeasurability
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.HilbertMinimizationMeasurability
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MuOperator.AEEOperator

/-! # Block Energy Average -/

@[expose] public section

namespace Homogenization

open scoped ENNReal
open scoped Topology
open Filter

/-!
# AEE quantitative slice assembly

## Audit tag (Ch4 rebuild contract `CH04_REBUILD_SURFACE_2026-05-16.md`)

**Internal claim:** the probability-facing replacement of the pointwise
quantitative-slice handoff. Re-routes the block-energy-average
measurability of `Internal/FixedCompetitorEnergyMeasurability` through the
a.e.-elliptic slice predicate `AEEQuantitativeEllipticSlice`, so the
local-test σ-algebra lane only needs a.e. quantitative ellipticity
information rather than a pointwise total cover.

**Consumed by:** `AEESliceAssembly/MuFamily.lean`, then
`Theorems/Mu.lean :: aemeasurable_Mu_cubeSet` and the AEE-slice
specialization
`aemeasurable_Mu_cubeSet_of_measurable_aeeQuantitativeSlice`.

Downstream developments should consume this through high-level
measurability bridges (e.g. `HasMeasurableMuFamily`) rather than threading
AEE-slice predicates through deterministic estimates.

If the single-claim summary above grows into three or more distinct
claims, split or refactor per the rebuild contract.
-/

theorem AEEQuantitativeEllipticSlice.ae_toHilbertMatrixL2_mem_quantitativeEllipticHilbertMatSet
    {d : ℕ} {U : Set (Vec d)} {k : ℕ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}) :
    ∀ᵐ x ∂ volumeMeasureOn U,
      AEEQuantitativeEllipticSlice.toHilbertMatrixL2 a x ∈
        quantitativeEllipticHilbertMatSet d k := by
  filter_upwards
      [AEEQuantitativeEllipticSlice.coeFn_toHilbertMatrixL2 a,
       MeasureTheory.ae_restrict_mem a.2.1,
       a.2.2.2]
    with x hcoeff hxU hxEll
  rw [hcoeff]
  simpa [quantitativeEllipticHilbertMatSet, restrictCoeffField, hxU] using hxEll

theorem AEEQuantitativeEllipticSlice.ae_fullBlockCoeffEntry_toHilbertMatrixL2_eq
    {d : ℕ} {U : Set (Vec d)} {k : ℕ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a})
    (α β : BlockCoord d) :
    (fun x => toFullBlockMat (blockCoeffField a.1 x) α β)
      =ᵐ[volumeMeasureOn U]
        fun x =>
          toFullBlockMat
            (blockMatrixOfCoeff
              (AEEQuantitativeEllipticSlice.toHilbertMatrixL2 a x).toMat) α β := by
  filter_upwards
      [AEEQuantitativeEllipticSlice.coeFn_toHilbertMatrixL2 a,
       MeasureTheory.ae_restrict_mem a.2.1]
    with x hcoeff hxU
  rw [hcoeff]
  simp [blockCoeffField, restrictCoeffField, hxU]

theorem AEEQuantitativeEllipticSlice.weightedFullBlockCoeffEntryIntegral_eq_hilbertMatrixL2
    {d : ℕ} {U : Set (Vec d)} {k : ℕ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a})
    (w : Vec d → ℝ) (α β : BlockCoord d) :
    ∫ x in U, w x * toFullBlockMat (blockCoeffField a.1 x) α β ∂MeasureTheory.volume =
      ∫ x,
        w x *
          toFullBlockMat
            (blockMatrixOfCoeff
              (AEEQuantitativeEllipticSlice.toHilbertMatrixL2 a x).toMat) α β
          ∂volumeMeasureOn U := by
  unfold volumeMeasureOn
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards
      [AEEQuantitativeEllipticSlice.ae_fullBlockCoeffEntry_toHilbertMatrixL2_eq a α β]
    with x hx
  rw [hx]

theorem AEEQuantitativeEllipticSlice.measurable_l2WeightedFullBlockCoeffEntryIntegral_of_lipschitzExtension
    {d : ℕ} {U : Set (Vec d)} {k : ℕ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hToL2 :
      @Measurable {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}
        (MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U))
        (AEEQuantitativeEllipticSlice.localMeasurableSpace U k) (borel _)
        AEEQuantitativeEllipticSlice.toHilbertMatrixL2)
    {w : Vec d → ℝ} (hw : MemScalarL2 U w) (α β : BlockCoord d)
    {K : NNReal} {Q : HilbertMat d → ℝ} (hQ : LipschitzWith K Q)
    (hQ_eq :
      ∀ A ∈ quantitativeEllipticHilbertMatSet d k,
        Q A = toFullBlockMat (blockMatrixOfCoeff A.toMat) α β) :
    @Measurable {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}
      ℝ (AEEQuantitativeEllipticSlice.localMeasurableSpace U k) (borel ℝ)
      (fun a =>
        ∫ x in U,
          w x * toFullBlockMat (blockCoeffField a.1 x) α β ∂MeasureTheory.volume) := by
  rw [show
      (fun a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a} =>
        ∫ x in U,
          w x * toFullBlockMat (blockCoeffField a.1 x) α β ∂MeasureTheory.volume) =
        fun a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a} =>
          ∫ x,
            w x * Q (AEEQuantitativeEllipticSlice.toHilbertMatrixL2 a x)
              ∂volumeMeasureOn U by
        funext a
        calc
          ∫ x in U, w x * toFullBlockMat (blockCoeffField a.1 x) α β
              ∂MeasureTheory.volume =
            ∫ x,
              w x *
                toFullBlockMat
                  (blockMatrixOfCoeff
                    (AEEQuantitativeEllipticSlice.toHilbertMatrixL2 a x).toMat) α β
                ∂volumeMeasureOn U :=
            AEEQuantitativeEllipticSlice.weightedFullBlockCoeffEntryIntegral_eq_hilbertMatrixL2
              a w α β
          _ =
            ∫ x,
              w x * Q (AEEQuantitativeEllipticSlice.toHilbertMatrixL2 a x)
                ∂volumeMeasureOn U := by
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards
                [AEEQuantitativeEllipticSlice.ae_toHilbertMatrixL2_mem_quantitativeEllipticHilbertMatSet
                  a]
              with x hx
            rw [hQ_eq _ hx]]
  exact measurable_l2WeightedHilbertMatrixLipschitzIntegral hToL2 hw hQ

theorem AEEQuantitativeEllipticSlice.measurable_l2WeightedFullBlockCoeffEntryIntegral_of_lipschitzOn
    {d : ℕ} {U : Set (Vec d)} {k : ℕ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hToL2 :
      @Measurable {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}
        (MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U))
        (AEEQuantitativeEllipticSlice.localMeasurableSpace U k) (borel _)
        AEEQuantitativeEllipticSlice.toHilbertMatrixL2)
    {w : Vec d → ℝ} (hw : MemScalarL2 U w) (α β : BlockCoord d)
    {K : NNReal}
    (hLip :
      LipschitzOnWith K
        (fun A : HilbertMat d => toFullBlockMat (blockMatrixOfCoeff A.toMat) α β)
        (quantitativeEllipticHilbertMatSet d k)) :
    @Measurable {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}
      ℝ (AEEQuantitativeEllipticSlice.localMeasurableSpace U k) (borel ℝ)
      (fun a =>
        ∫ x in U,
          w x * toFullBlockMat (blockCoeffField a.1 x) α β ∂MeasureTheory.volume) := by
  obtain ⟨Q, hQ_lip, hQ_eq_on⟩ := hLip.extend_real
  refine
    AEEQuantitativeEllipticSlice.measurable_l2WeightedFullBlockCoeffEntryIntegral_of_lipschitzExtension
      hToL2 hw α β hQ_lip ?_
  intro A hA
  exact (hQ_eq_on hA).symm

theorem AEEQuantitativeEllipticSlice.measurable_l2WeightedFullBlockCoeffEntryIntegral
    {d : ℕ} {U : Set (Vec d)} {k : ℕ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hToL2 :
      @Measurable {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}
        (MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U))
        (AEEQuantitativeEllipticSlice.localMeasurableSpace U k) (borel _)
        AEEQuantitativeEllipticSlice.toHilbertMatrixL2)
    {w : Vec d → ℝ} (hw : MemScalarL2 U w) (α β : BlockCoord d) :
    @Measurable {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}
      ℝ (AEEQuantitativeEllipticSlice.localMeasurableSpace U k) (borel ℝ)
      (fun a =>
        ∫ x in U,
          w x * toFullBlockMat (blockCoeffField a.1 x) α β ∂MeasureTheory.volume) := by
  exact
    AEEQuantitativeEllipticSlice.measurable_l2WeightedFullBlockCoeffEntryIntegral_of_lipschitzOn
      hToL2 hw α β
      (lipschitzOnWith_fullBlockCoeffEntry_hilbertMat_quantitative α β)

theorem AEEQuantitativeEllipticSlice.integrable_weightedFullBlockCoeffEntry_of_integrable
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {k : ℕ} {w : Vec d → ℝ} (hSlice : AEEQuantitativeEllipticSlice U k a)
    (hw : MeasureTheory.Integrable w (volumeMeasureOn U)) (α β : BlockCoord d) :
    MeasureTheory.Integrable
      (fun x => w x * toFullBlockMat (blockCoeffField a x) α β)
      (volumeMeasureOn U) := by
  classical
  let coeff : Vec d → ℝ := fun x => toFullBlockMat (blockCoeffField a x) α β
  let aSub : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a} := ⟨a, hSlice⟩
  have hcoeff_ae : AEMeasurable coeff (volumeMeasureOn U) := by
    have htarget :
        AEMeasurable
          (fun x : Vec d =>
            toFullBlockMat
              (blockMatrixOfCoeff
                (AEEQuantitativeEllipticSlice.toHilbertMatrixL2 aSub x).toMat) α β)
          (volumeMeasureOn U) :=
      (measurable_fullBlockCoeffEntry_hilbertMat α β).comp_aemeasurable
        (MeasureTheory.Lp.aestronglyMeasurable
          (AEEQuantitativeEllipticSlice.toHilbertMatrixL2 aSub)).aemeasurable
    exact htarget.congr
      (AEEQuantitativeEllipticSlice.ae_fullBlockCoeffEntry_toHilbertMatrixL2_eq
        aSub α β).symm
  have hbound :
      ∀ᵐ x ∂ volumeMeasureOn U,
        ‖coeff x‖ ≤ Real.sqrt (blockMatrixOfCoeffNormSqBound ((k + 1 : ℝ)⁻¹) (k + 1 : ℝ)) := by
    filter_upwards [hSlice.ae_isEllipticMatrix] with x hxEll
    simpa [coeff, blockCoeffField, Real.norm_eq_abs] using
      abs_toFullBlockMat_blockMatrixOfCoeff_entry_le_of_isEllipticMatrix
        (A := a x) hxEll α β
  simpa [coeff] using hw.mul_bdd hcoeff_ae.aestronglyMeasurable hbound

theorem AEEQuantitativeEllipticSlice.measurable_integrableWeightedFullBlockCoeffEntryIntegral_of_measurable
    {d : ℕ} {U : Set (Vec d)} {k : ℕ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hToL2 :
      @Measurable {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}
        (MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U))
        (AEEQuantitativeEllipticSlice.localMeasurableSpace U k) (borel _)
        AEEQuantitativeEllipticSlice.toHilbertMatrixL2)
    {w : Vec d → ℝ} (hw_meas : Measurable w)
    (hw_int : MeasureTheory.Integrable w (volumeMeasureOn U)) (α β : BlockCoord d) :
    @Measurable {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}
      ℝ (AEEQuantitativeEllipticSlice.localMeasurableSpace U k) (borel ℝ)
      (fun a =>
        ∫ x in U,
          w x * toFullBlockMat (blockCoeffField a.1 x) α β ∂MeasureTheory.volume) := by
  classical
  let μ := volumeMeasureOn U
  let C : ℝ :=
    Real.sqrt (blockMatrixOfCoeffNormSqBound ((k + 1 : ℝ)⁻¹) (k + 1 : ℝ))
  let s : ℕ → Vec d → ℝ :=
    fun n => MeasureTheory.SimpleFunc.approxOn w hw_meas (Set.range w ∪ {0}) 0 (by simp) n
  have hs_L2 : ∀ n, MemScalarL2 U (s n) := by
    intro n
    simpa [MemScalarL2, μ, s] using
      (MeasureTheory.SimpleFunc.memLp_of_isFiniteMeasure
        (MeasureTheory.SimpleFunc.approxOn w hw_meas (Set.range w ∪ {0}) 0 (by simp) n)
        (2 : ℝ≥0∞) (volumeMeasureOn U))
  have hs_meas :
      ∀ n,
        @Measurable {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}
          ℝ (AEEQuantitativeEllipticSlice.localMeasurableSpace U k) (borel ℝ)
          (fun a =>
            ∫ x in U,
              s n x * toFullBlockMat (blockCoeffField a.1 x) α β
                ∂MeasureTheory.volume) := by
    intro n
    exact
      AEEQuantitativeEllipticSlice.measurable_l2WeightedFullBlockCoeffEntryIntegral
        hToL2 (hs_L2 n) α β
  have hs_tendsto :
      Filter.Tendsto
        (fun n : ℕ =>
          fun a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a} =>
            ∫ x in U,
              s n x * toFullBlockMat (blockCoeffField a.1 x) α β
                ∂MeasureTheory.volume)
        atTop
        (𝓝
          fun a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a} =>
            ∫ x in U,
              w x * toFullBlockMat (blockCoeffField a.1 x) α β
                ∂MeasureTheory.volume) := by
    rw [tendsto_pi_nhds]
    intro a
    have hprod_int :
        MeasureTheory.Integrable
          (fun x => w x * toFullBlockMat (blockCoeffField a.1 x) α β) μ := by
      simpa [μ] using
        a.2.integrable_weightedFullBlockCoeffEntry_of_integrable hw_int α β
    have hs_prod_int :
        ∀ n,
          MeasureTheory.Integrable
            (fun x => s n x * toFullBlockMat (blockCoeffField a.1 x) α β) μ := by
      intro n
      have hs_int :
          MeasureTheory.Integrable (s n) μ := by
        simpa [s, μ] using
          (MeasureTheory.SimpleFunc.integrable_of_isFiniteMeasure
            (MeasureTheory.SimpleFunc.approxOn w hw_meas (Set.range w ∪ {0}) 0 (by simp) n))
      simpa [μ] using
        a.2.integrable_weightedFullBlockCoeffEntry_of_integrable hs_int α β
    have hcoeff_bound :
        ∀ᵐ x ∂ μ,
          ‖toFullBlockMat (blockCoeffField a.1 x) α β‖ ≤ C := by
      filter_upwards [a.2.2.2] with x hxEll
      simpa [μ, C, blockCoeffField, Real.norm_eq_abs] using
        abs_toFullBlockMat_blockMatrixOfCoeff_entry_le_of_isEllipticMatrix
          (A := a.1 x) hxEll α β
    have hbound :
        ∀ n,
          ∀ᵐ x ∂ μ,
            ‖s n x * toFullBlockMat (blockCoeffField a.1 x) α β‖ ≤
              (2 * C) * ‖w x‖ := by
      intro n
      filter_upwards [hcoeff_bound] with x hxcoeff
      have hsx :
          ‖s n x‖ ≤ ‖w x‖ + ‖w x‖ := by
        simpa [s] using
          MeasureTheory.SimpleFunc.norm_approxOn_zero_le hw_meas
            (s := Set.range w ∪ {0}) (by simp) x n
      have hmul_nonneg : 0 ≤ ‖w x‖ + ‖w x‖ := by positivity
      have hcoeff_nonneg : 0 ≤ ‖toFullBlockMat (blockCoeffField a.1 x) α β‖ := by
        positivity
      calc
        ‖s n x * toFullBlockMat (blockCoeffField a.1 x) α β‖
            = ‖s n x‖ * ‖toFullBlockMat (blockCoeffField a.1 x) α β‖ := by
              exact norm_mul _ _
        _ ≤ (‖w x‖ + ‖w x‖) * C := by
              exact mul_le_mul hsx hxcoeff hcoeff_nonneg hmul_nonneg
        _ = (2 * C) * ‖w x‖ := by ring
    have hbound_int :
        MeasureTheory.Integrable (fun x => (2 * C) * ‖w x‖) μ := by
      simpa [mul_assoc] using hw_int.norm.const_mul (2 * C)
    have hlim :
        ∀ᵐ x ∂ μ,
          Tendsto
            (fun n : ℕ =>
              s n x * toFullBlockMat (blockCoeffField a.1 x) α β)
            atTop
            (𝓝 (w x * toFullBlockMat (blockCoeffField a.1 x) α β)) := by
      refine Filter.Eventually.of_forall ?_
      intro x
      exact
        (MeasureTheory.SimpleFunc.tendsto_approxOn hw_meas
            (s := Set.range w ∪ {0}) (y₀ := 0) (by simp)
            (x := x) (subset_closure (Or.inl ⟨x, rfl⟩))).mul tendsto_const_nhds
    simpa [MeasureTheory.IntegrableOn, volumeMeasureOn, μ, s] using
      MeasureTheory.tendsto_integral_of_dominated_convergence
        (μ := μ) (G := ℝ)
        (F := fun n x =>
          s n x * toFullBlockMat (blockCoeffField a.1 x) α β)
        (f := fun x =>
          w x * toFullBlockMat (blockCoeffField a.1 x) α β)
        (fun x => (2 * C) * ‖w x‖)
        (fun n => (hs_prod_int n).aestronglyMeasurable)
        hbound_int hbound hlim
  let : MeasurableSpace {a : CoeffField d // AEEQuantitativeEllipticSlice U k a} :=
    AEEQuantitativeEllipticSlice.localMeasurableSpace U k
  exact measurable_of_tendsto_metrizable hs_meas hs_tendsto

theorem AEEQuantitativeEllipticSlice.measurable_integrableWeightedFullBlockCoeffEntryIntegral
    {d : ℕ} {U : Set (Vec d)} {k : ℕ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hToL2 :
      @Measurable {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}
        (MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U))
        (AEEQuantitativeEllipticSlice.localMeasurableSpace U k) (borel _)
        AEEQuantitativeEllipticSlice.toHilbertMatrixL2)
    {w : Vec d → ℝ}
    (hw : MeasureTheory.Integrable w (volumeMeasureOn U)) (α β : BlockCoord d) :
    @Measurable {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}
      ℝ (AEEQuantitativeEllipticSlice.localMeasurableSpace U k) (borel ℝ)
      (fun a =>
        ∫ x in U,
          w x * toFullBlockMat (blockCoeffField a.1 x) α β ∂MeasureTheory.volume) := by
  classical
  let w' : Vec d → ℝ := hw.aestronglyMeasurable.mk w
  have hw'_meas : Measurable w' := by
    simpa [w'] using hw.aestronglyMeasurable.measurable_mk
  have hw'_int : MeasureTheory.Integrable w' (volumeMeasureOn U) := by
    exact hw.congr hw.aestronglyMeasurable.ae_eq_mk
  have hmeas' :
      @Measurable {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}
        ℝ (AEEQuantitativeEllipticSlice.localMeasurableSpace U k) (borel ℝ)
        (fun a =>
          ∫ x in U,
            w' x * toFullBlockMat (blockCoeffField a.1 x) α β
              ∂MeasureTheory.volume) :=
    AEEQuantitativeEllipticSlice.measurable_integrableWeightedFullBlockCoeffEntryIntegral_of_measurable
        hToL2 hw'_meas hw'_int α β
  rw [show
      (fun a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a} =>
        ∫ x in U,
          w x * toFullBlockMat (blockCoeffField a.1 x) α β ∂MeasureTheory.volume) =
        fun a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a} =>
          ∫ x in U,
            w' x * toFullBlockMat (blockCoeffField a.1 x) α β
              ∂MeasureTheory.volume by
        funext a
        apply MeasureTheory.integral_congr_ae
        filter_upwards [hw.aestronglyMeasurable.ae_eq_mk] with x hx
        rw [hx]]
  exact hmeas'

theorem AEEQuantitativeEllipticSlice.integrableOn_weightedFullBlockCoeffEntry_of_memBlockL2
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {k : ℕ} {X : BlockState d} (hSlice : AEEQuantitativeEllipticSlice U k a)
    (hX : MemBlockL2 U X.eval) (α β : BlockCoord d) :
    MeasureTheory.IntegrableOn
      (fun x =>
        blockEnergyEntryWeight X α β x *
          toFullBlockMat (blockCoeffField a x) α β)
      U := by
  simpa [MeasureTheory.IntegrableOn, volumeMeasureOn] using
    hSlice.integrable_weightedFullBlockCoeffEntry_of_integrable
      (integrable_blockEnergyEntryWeight_of_memBlockL2 hX α β) α β

theorem AEEQuantitativeEllipticSlice.integrableOn_pairingWeightedFullBlockCoeffEntry_of_memBlockL2
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {k : ℕ} {X Y : BlockState d} (hSlice : AEEQuantitativeEllipticSlice U k a)
    (hX : MemBlockL2 U X.eval) (hY : MemBlockL2 U Y.eval) (α β : BlockCoord d) :
    MeasureTheory.IntegrableOn
      (fun x =>
        blockPairingEntryWeight X Y α β x *
          toFullBlockMat (blockCoeffField a x) α β)
      U := by
  simpa [MeasureTheory.IntegrableOn, volumeMeasureOn] using
    hSlice.integrable_weightedFullBlockCoeffEntry_of_integrable
      (integrable_blockPairingEntryWeight_of_memBlockL2 hX hY α β) α β

theorem measurable_blockEnergyAverage_aeeQuantitativeSlice
    {d : ℕ} {U : Set (Vec d)} {k : ℕ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hToL2 :
      @Measurable {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}
        (MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U))
        (AEEQuantitativeEllipticSlice.localMeasurableSpace U k) (borel _)
        AEEQuantitativeEllipticSlice.toHilbertMatrixL2)
    (X : BlockState d) (hX : MemBlockL2 U X.eval) :
    @Measurable {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}
      ℝ (AEEQuantitativeEllipticSlice.localMeasurableSpace U k) (borel ℝ)
      (fun a => blockEnergyAverage U a.1 X) := by
  let : MeasurableSpace {a : CoeffField d // AEEQuantitativeEllipticSlice U k a} :=
    AEEQuantitativeEllipticSlice.localMeasurableSpace U k
  exact measurable_blockEnergyAverage_comp_of_measurable_weightedFullBlockCoeffEntryIntegrals
    (A := fun a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a} => a.1)
    (X := X)
    (fun a α β =>
      a.2.integrableOn_weightedFullBlockCoeffEntry_of_memBlockL2 hX α β)
    (fun α β =>
      AEEQuantitativeEllipticSlice.measurable_integrableWeightedFullBlockCoeffEntryIntegral
        hToL2 (integrable_blockEnergyEntryWeight_of_memBlockL2 hX α β) α β)

theorem measurable_blockPairingAverage_aeeQuantitativeSlice
    {d : ℕ} {U : Set (Vec d)} {k : ℕ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hToL2 :
      @Measurable {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}
        (MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U))
        (AEEQuantitativeEllipticSlice.localMeasurableSpace U k) (borel _)
        AEEQuantitativeEllipticSlice.toHilbertMatrixL2)
    (X Y : BlockState d) (hX : MemBlockL2 U X.eval) (hY : MemBlockL2 U Y.eval) :
    @Measurable {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}
      ℝ (AEEQuantitativeEllipticSlice.localMeasurableSpace U k) (borel ℝ)
      (fun a => blockPairingAverage U a.1 X Y) := by
  let : MeasurableSpace {a : CoeffField d // AEEQuantitativeEllipticSlice U k a} :=
    AEEQuantitativeEllipticSlice.localMeasurableSpace U k
  exact measurable_blockPairingAverage_comp_of_measurable_weightedFullBlockCoeffEntryIntegrals
    (A := fun a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a} => a.1)
    (X := X) (Y := Y)
    (fun a α β =>
      a.2.integrableOn_pairingWeightedFullBlockCoeffEntry_of_memBlockL2 hX hY α β)
    (fun α β =>
      AEEQuantitativeEllipticSlice.measurable_integrableWeightedFullBlockCoeffEntryIntegral
        hToL2 (integrable_blockPairingEntryWeight_of_memBlockL2 hX hY α β) α β)

/-- Canonical AEE cube-slice measurability of the Hilbert bilinear form on two
dense-generator correction probes. -/
theorem measurable_energyBilin_canonicalAEEMuGenerator_aeeQuantitativeSlice_cubeSet
    {d : ℕ} (Q : TriadicCube d) (k : ℕ)
    (Y Z : canonicalMuBlockCorrectionGeneratorSubmodule (cubeSet Q)) :
    @Measurable {a : CoeffField d // AEEQuantitativeEllipticSlice (cubeSet Q) k a}
      ℝ (AEEQuantitativeEllipticSlice.localMeasurableSpace (cubeSet Q) k) (borel ℝ)
      (fun a =>
        ((canonicalAEEMuOperatorSystemData Q k a).toMuHilbertRealization).energyBilin
          (canonicalMuCorrectionGeneratorEmbedding (cubeSet Q) Y)
          (canonicalMuCorrectionGeneratorEmbedding (cubeSet Q) Z)) := by
  let Xstate : BlockState d :=
    canonicalMuGeneratorAffineField (U := cubeSet Q) (0 : BlockVec d) Z
  let Ystate : BlockState d :=
    canonicalMuGeneratorAffineField (U := cubeSet Q) (0 : BlockVec d) Y
  have hRewrite :
      (fun a : {a : CoeffField d // AEEQuantitativeEllipticSlice (cubeSet Q) k a} =>
        ((canonicalAEEMuOperatorSystemData Q k a).toMuHilbertRealization).energyBilin
          (canonicalMuCorrectionGeneratorEmbedding (cubeSet Q) Y)
          (canonicalMuCorrectionGeneratorEmbedding (cubeSet Q) Z)) =
        fun a => blockPairingAverage (cubeSet Q) a.1 Xstate Ystate := by
    funext a
    simpa [Xstate, Ystate] using
      canonicalAEEMuOperatorSystemData_energyBilin_generator_eq_blockPairingAverage
        Q k a Y Z
  rw [hRewrite]
  exact
    measurable_blockPairingAverage_aeeQuantitativeSlice
      (measurable_toHilbertMatrixL2_aeeQuantitativeEllipticSlice_cubeSet Q k)
      Xstate Ystate
      (canonicalMuGeneratorAffineField_memBlockL2 (U := cubeSet Q) (0 : BlockVec d) Z)
      (canonicalMuGeneratorAffineField_memBlockL2 (U := cubeSet Q) (0 : BlockVec d) Y)

/-- Canonical AEE cube-slice measurability of the Hilbert bilinear form on a
constant affine shift and one dense-generator correction probe. -/
theorem measurable_energyBilin_const_canonicalAEEMuGenerator_aeeQuantitativeSlice_cubeSet
    {d : ℕ} (Q : TriadicCube d) (k : ℕ) (P : BlockVec d)
    (Y : canonicalMuBlockCorrectionGeneratorSubmodule (cubeSet Q)) :
    @Measurable {a : CoeffField d // AEEQuantitativeEllipticSlice (cubeSet Q) k a}
      ℝ (AEEQuantitativeEllipticSlice.localMeasurableSpace (cubeSet Q) k) (borel ℝ)
      (fun a =>
        ((canonicalAEEMuOperatorSystemData Q k a).toMuHilbertRealization).energyBilin
          (((canonicalAEEMuOperatorSystemData Q k a).toMuHilbertRealization).constantField P)
          (canonicalMuCorrectionGeneratorEmbedding (cubeSet Q) Y)) := by
  let Xstate : BlockState d :=
    canonicalMuGeneratorAffineField (U := cubeSet Q) (0 : BlockVec d) Y
  let Ystate : BlockState d :=
    canonicalMuGeneratorAffineField
      (U := cubeSet Q) P (0 : canonicalMuBlockCorrectionGeneratorSubmodule (cubeSet Q))
  have hRewrite :
      (fun a : {a : CoeffField d // AEEQuantitativeEllipticSlice (cubeSet Q) k a} =>
        ((canonicalAEEMuOperatorSystemData Q k a).toMuHilbertRealization).energyBilin
          (((canonicalAEEMuOperatorSystemData Q k a).toMuHilbertRealization).constantField P)
          (canonicalMuCorrectionGeneratorEmbedding (cubeSet Q) Y)) =
        fun a => blockPairingAverage (cubeSet Q) a.1 Xstate Ystate := by
    funext a
    simpa [Xstate, Ystate] using
      canonicalAEEMuOperatorSystemData_energyBilin_const_generator_eq_blockPairingAverage
        Q k a P Y
  rw [hRewrite]
  exact
    measurable_blockPairingAverage_aeeQuantitativeSlice
      (measurable_toHilbertMatrixL2_aeeQuantitativeEllipticSlice_cubeSet Q k)
      Xstate Ystate
      (canonicalMuGeneratorAffineField_memBlockL2 (U := cubeSet Q) (0 : BlockVec d) Y)
      (canonicalMuGeneratorAffineField_memBlockL2
        (U := cubeSet Q) P (0 : canonicalMuBlockCorrectionGeneratorSubmodule (cubeSet Q)))

/-- Canonical AEE cube-slice measurability of the Hilbert bilinear form on a
fixed block-`L²` test and one affine dense-generator probe. This is the
internal scalar-response source for measuring operator-image averages of the
selected doubled-`Mu` minimizer against deterministic tests. -/
theorem measurable_energyBilin_fixed_canonicalMuGeneratorAffineField_aeeQuantitativeSlice_cubeSet
    {d : ℕ} (Q : TriadicCube d) (k : ℕ) (P : BlockVec d)
    (Y : BlockState d) (hY : MemBlockL2 (cubeSet Q) Y.eval)
    (Z : canonicalMuBlockCorrectionGeneratorSubmodule (cubeSet Q)) :
    @Measurable {a : CoeffField d // AEEQuantitativeEllipticSlice (cubeSet Q) k a}
      ℝ (AEEQuantitativeEllipticSlice.localMeasurableSpace (cubeSet Q) k) (borel ℝ)
      (fun a =>
        ((canonicalAEEMuOperatorSystemData Q k a).toMuHilbertRealization).energyBilin
          (toHilbertBlockL2OfBlockField (U := cubeSet Q) hY)
          (blockVecToHilbertBlockL2Const (U := cubeSet Q) P +
            canonicalMuCorrectionGeneratorEmbedding (cubeSet Q) Z)) := by
  let Xstate : BlockState d :=
    canonicalMuGeneratorAffineField (U := cubeSet Q) P Z
  have hX : MemBlockL2 (cubeSet Q) Xstate.eval := by
    simpa [Xstate] using
      canonicalMuGeneratorAffineField_memBlockL2 (U := cubeSet Q) P Z
  have hRewrite :
      (fun a : {a : CoeffField d // AEEQuantitativeEllipticSlice (cubeSet Q) k a} =>
        ((canonicalAEEMuOperatorSystemData Q k a).toMuHilbertRealization).energyBilin
          (toHilbertBlockL2OfBlockField (U := cubeSet Q) hY)
          (blockVecToHilbertBlockL2Const (U := cubeSet Q) P +
            canonicalMuCorrectionGeneratorEmbedding (cubeSet Q) Z)) =
        fun a => blockPairingAverage (cubeSet Q) a.1 Xstate Y := by
    funext a
    let U : Set (Vec d) := cubeSet Q
    let system : AEEMuOperatorSystemData U a.1 := canonicalAEEMuOperatorSystemData Q k a
    have hX_hilbert :
        toHilbertBlockL2OfBlockField (U := U)
            (by simpa [U, Xstate] using hX) =
          blockVecToHilbertBlockL2Const (U := U) P +
            canonicalMuCorrectionGeneratorEmbedding U Z := by
      simpa [U, Xstate] using
        canonicalMuGeneratorAffineField_hilbert_eq_const_add (U := cubeSet Q) P Z
    calc
      ((canonicalAEEMuOperatorSystemData Q k a).toMuHilbertRealization).energyBilin
          (toHilbertBlockL2OfBlockField (U := cubeSet Q) hY)
          (blockVecToHilbertBlockL2Const (U := cubeSet Q) P +
            canonicalMuCorrectionGeneratorEmbedding (cubeSet Q) Z)
          =
        energyBilinOfOperator system.toMuOperatorRealization.operator
          (toHilbertBlockL2OfBlockField (U := U) (by simpa [U] using hY))
          (toHilbertBlockL2OfBlockField (U := U) (by simpa [U, Xstate] using hX)) := by
            simp [U, system, AEEMuOperatorSystemData.toMuHilbertRealization,
              MuOperatorRealization.toMuHilbertRealization, MuHilbertRealization.ofOperator,
              hX_hilbert]
      _ = blockPairingAverage U a.1 Xstate Y := by
            exact
              system.toMuOperatorRealization.energyBilin_eq_blockPairingAverage_of_blockState
                (X := Xstate) (Y := Y)
                (by simpa [U, Xstate] using hX) (by simpa [U] using hY)
  rw [hRewrite]
  exact
    measurable_blockPairingAverage_aeeQuantitativeSlice
      (measurable_toHilbertMatrixL2_aeeQuantitativeEllipticSlice_cubeSet Q k)
      Xstate Y hX hY

/-- Canonical AEE cube-slice measurability of every finite Galerkin affine
minimizer built from dense-generator correction probes. -/
theorem measurable_galerkinAffineMinimizer_canonicalAEEMuGenerator_aeeQuantitativeSlice_cubeSet
    {d : ℕ} (Q : TriadicCube d) (k : ℕ) (P : BlockVec d) {n : ℕ}
    (e : Fin n → canonicalMuBlockCorrectionGeneratorSubmodule (cubeSet Q)) :
    @Measurable {a : CoeffField d // AEEQuantitativeEllipticSlice (cubeSet Q) k a}
      (HilbertBlockL2 (cubeSet Q))
      (AEEQuantitativeEllipticSlice.localMeasurableSpace (cubeSet Q) k) (borel _)
      (fun a =>
        galerkinAffineMinimizer
          (((canonicalAEEMuOperatorSystemData Q k a).toMuHilbertRealization).energyBilin)
          (((canonicalAEEMuOperatorSystemData Q k a).toMuHilbertRealization).constantField P)
          (fun i =>
            (canonicalMuCorrectionGeneratorEmbedding (cubeSet Q) (e i) :
              HilbertBlockL2 (cubeSet Q)))) := by
  classical
  let : MeasurableSpace {a : CoeffField d // AEEQuantitativeEllipticSlice (cubeSet Q) k a} :=
    AEEQuantitativeEllipticSlice.localMeasurableSpace (cubeSet Q) k
  let : MeasurableSpace (HilbertBlockL2 (cubeSet Q)) := borel _
  let : BorelSpace (HilbertBlockL2 (cubeSet Q)) := ⟨rfl⟩
  let B :
      {a : CoeffField d // AEEQuantitativeEllipticSlice (cubeSet Q) k a} →
        HilbertBlockL2 (cubeSet Q) →L[ℝ] HilbertBlockL2 (cubeSet Q) →L[ℝ] ℝ :=
    fun a => ((canonicalAEEMuOperatorSystemData Q k a).toMuHilbertRealization).energyBilin
  let x :
      {a : CoeffField d // AEEQuantitativeEllipticSlice (cubeSet Q) k a} →
        HilbertBlockL2 (cubeSet Q) :=
    fun a => ((canonicalAEEMuOperatorSystemData Q k a).toMuHilbertRealization).constantField P
  let ebasis : Fin n → HilbertBlockL2 (cubeSet Q) :=
    fun i => canonicalMuCorrectionGeneratorEmbedding (cubeSet Q) (e i)
  have hx : @Measurable
      {a : CoeffField d // AEEQuantitativeEllipticSlice (cubeSet Q) k a}
      (HilbertBlockL2 (cubeSet Q))
      (AEEQuantitativeEllipticSlice.localMeasurableSpace (cubeSet Q) k) (borel _) x := by
    change @Measurable
      {a : CoeffField d // AEEQuantitativeEllipticSlice (cubeSet Q) k a}
      (HilbertBlockL2 (cubeSet Q))
      (AEEQuantitativeEllipticSlice.localMeasurableSpace (cubeSet Q) k) (borel _)
      (fun _ => blockVecToHilbertBlockL2Const (U := cubeSet Q) P)
    exact measurable_const
  have hB : ∀ i j : Fin n, @Measurable
      {a : CoeffField d // AEEQuantitativeEllipticSlice (cubeSet Q) k a}
      ℝ (AEEQuantitativeEllipticSlice.localMeasurableSpace (cubeSet Q) k) (borel ℝ)
      (fun a => B a (ebasis j) (ebasis i)) := by
    intro i j
    simpa [B, ebasis] using
      measurable_energyBilin_canonicalAEEMuGenerator_aeeQuantitativeSlice_cubeSet
        Q k (e j) (e i)
  have hBx : ∀ i : Fin n, @Measurable
      {a : CoeffField d // AEEQuantitativeEllipticSlice (cubeSet Q) k a}
      ℝ (AEEQuantitativeEllipticSlice.localMeasurableSpace (cubeSet Q) k) (borel ℝ)
      (fun a => B a (x a) (ebasis i)) := by
    intro i
    simpa [B, x, ebasis] using
      measurable_energyBilin_const_canonicalAEEMuGenerator_aeeQuantitativeSlice_cubeSet
        Q k P (e i)
  have hCoeff : Measurable fun a => galerkinCoeff (B a) (x a) ebasis :=
    measurable_galerkinCoeff hB hBx
  have hCorr : Measurable fun a => galerkinCorrection (B a) (x a) ebasis := by
    have hAssemble :
        Continuous fun c : Fin n → ℝ => ∑ j : Fin n, c j • ebasis j := by
      fun_prop
    change Measurable ((fun c : Fin n → ℝ => ∑ j : Fin n, c j • ebasis j) ∘
      fun a => galerkinCoeff (B a) (x a) ebasis)
    exact hAssemble.measurable.comp hCoeff
  have hTranslate :
      Measurable fun y : HilbertBlockL2 (cubeSet Q) =>
        blockVecToHilbertBlockL2Const (U := cubeSet Q) P + y :=
    (continuous_const.add continuous_id).measurable
  simpa [B, x, ebasis, galerkinAffineMinimizer] using! hTranslate.comp hCorr

/-- Slice-local strong measurability of the selected canonical doubled-`Mu`
Hilbert minimizer, once the canonical finite Galerkin approximants satisfy the
deterministic energy-comparison convergence hypotheses. -/
theorem stronglyMeasurable_canonicalAEEMuHilbertMinimizer_aeeQuantitativeSlice_cubeSet_of_galerkin_energy
    {d : ℕ} (Q : TriadicCube d) (k : ℕ) (P : BlockVec d)
    (e : (m : ℕ) → Fin m → canonicalMuBlockCorrectionGeneratorSubmodule (cubeSet Q))
    (v :
      {a : CoeffField d // AEEQuantitativeEllipticSlice (cubeSet Q) k a} →
        ℕ → HilbertBlockL2 (cubeSet Q))
    (hv_mem :
      ∀ a m,
        let H := ((canonicalAEEMuOperatorSystemData Q k a).toMuHilbertRealization)
        v a m - H.constantField P ∈
          (canonicalAEEMuCorrectionSpaceData Q).correctionSpace)
    (hEnergy :
      ∀ a m,
        let H := ((canonicalAEEMuOperatorSystemData Q k a).toMuHilbertRealization)
        quadraticEnergy H.energyBilin
            (galerkinAffineMinimizer H.energyBilin (H.constantField P)
              (fun i =>
                (canonicalMuCorrectionGeneratorEmbedding (cubeSet Q) (e m i) :
                  HilbertBlockL2 (cubeSet Q)))) ≤
          quadraticEnergy H.energyBilin (v a m))
    (hv_tendsto :
      ∀ a,
        let H := ((canonicalAEEMuOperatorSystemData Q k a).toMuHilbertRealization)
        Tendsto (fun m : ℕ => v a m) atTop
          (𝓝 (affineMinimizerMap
            (canonicalAEEMuCorrectionSpaceData Q).correctionSpace
            H.energyBilin H.energyCoercive (H.constantField P)))) :
    letI : MeasurableSpace
      {a : CoeffField d // AEEQuantitativeEllipticSlice (cubeSet Q) k a} :=
        AEEQuantitativeEllipticSlice.localMeasurableSpace (cubeSet Q) k
    MeasureTheory.StronglyMeasurable
      (fun a : {a : CoeffField d // AEEQuantitativeEllipticSlice (cubeSet Q) k a} =>
        let H := ((canonicalAEEMuOperatorSystemData Q k a).toMuHilbertRealization)
        affineMinimizerMap
          (canonicalAEEMuCorrectionSpaceData Q).correctionSpace
          H.energyBilin H.energyCoercive (H.constantField P)) := by
  classical
  let : MeasurableSpace {a : CoeffField d // AEEQuantitativeEllipticSlice (cubeSet Q) k a} :=
    AEEQuantitativeEllipticSlice.localMeasurableSpace (cubeSet Q) k
  let : MeasurableSpace (HilbertBlockL2 (cubeSet Q)) := borel _
  let K : ClosedSubmodule ℝ (HilbertBlockL2 (cubeSet Q)) :=
    (canonicalAEEMuCorrectionSpaceData Q).correctionSpace
  let B :
      {a : CoeffField d // AEEQuantitativeEllipticSlice (cubeSet Q) k a} →
        HilbertBlockL2 (cubeSet Q) →L[ℝ] HilbertBlockL2 (cubeSet Q) →L[ℝ] ℝ :=
    fun a => ((canonicalAEEMuOperatorSystemData Q k a).toMuHilbertRealization).energyBilin
  let hB :
      ∀ a, IsCoercive (B a) :=
    fun a => ((canonicalAEEMuOperatorSystemData Q k a).toMuHilbertRealization).energyCoercive
  let x :
      {a : CoeffField d // AEEQuantitativeEllipticSlice (cubeSet Q) k a} →
        HilbertBlockL2 (cubeSet Q) :=
    fun a => ((canonicalAEEMuOperatorSystemData Q k a).toMuHilbertRealization).constantField P
  let ebasis : (m : ℕ) → Fin m → HilbertBlockL2 (cubeSet Q) :=
    fun m i => canonicalMuCorrectionGeneratorEmbedding (cubeSet Q) (e m i)
  have hx : MeasureTheory.StronglyMeasurable x := by
    change MeasureTheory.StronglyMeasurable
      (fun _ : {a : CoeffField d // AEEQuantitativeEllipticSlice (cubeSet Q) k a} =>
        blockVecToHilbertBlockL2Const (U := cubeSet Q) P)
    exact MeasureTheory.stronglyMeasurable_const
  have hsymm : ∀ a, ∀ X Y : HilbertBlockL2 (cubeSet Q), B a X Y = B a Y X := by
    intro a
    exact ((canonicalAEEMuOperatorSystemData Q k a).toMuHilbertRealization).energySymm
  have hB_meas :
      ∀ m, ∀ i j : Fin m, Measurable fun a => B a (ebasis m j) (ebasis m i) := by
    intro m i j
    simpa [B, ebasis] using
      measurable_energyBilin_canonicalAEEMuGenerator_aeeQuantitativeSlice_cubeSet
        Q k (e m j) (e m i)
  have hBx_meas :
      ∀ m, ∀ i : Fin m, Measurable fun a => B a (x a) (ebasis m i) := by
    intro m i
    simpa [B, x, ebasis] using
      measurable_energyBilin_const_canonicalAEEMuGenerator_aeeQuantitativeSlice_cubeSet
        Q k P (e m i)
  have hGalerkin_mem :
      ∀ a m, galerkinAffineMinimizer (B a) (x a) (ebasis m) - x a ∈ K := by
    intro a m
    have hcorr : galerkinCorrection (B a) (x a) (ebasis m) ∈ K := by
      unfold galerkinCorrection
      refine K.toSubmodule.sum_mem ?_
      intro i _hi
      refine K.toSubmodule.smul_mem _ ?_
      exact (canonicalMuCorrectionGeneratorEmbedding (cubeSet Q) (e m i)).2
    have hdiff :
        galerkinAffineMinimizer (B a) (x a) (ebasis m) - x a =
          galerkinCorrection (B a) (x a) (ebasis m) := by
      simp [galerkinAffineMinimizer]
    rw [hdiff]
    exact hcorr
  have hv_mem' : ∀ a m, v a m - x a ∈ K := by
    intro a m
    simpa [K, x] using hv_mem a m
  have hEnergy' :
      ∀ a m,
        quadraticEnergy (B a) (galerkinAffineMinimizer (B a) (x a) (ebasis m)) ≤
          quadraticEnergy (B a) (v a m) := by
    intro a m
    simpa [B, x, ebasis] using hEnergy a m
  have hv_tendsto' :
      ∀ a,
        Tendsto (fun m : ℕ => v a m) atTop
          (𝓝 (affineMinimizerMap K (B a) (hB a) (x a))) := by
    intro a
    simpa [K, B, hB, x] using hv_tendsto a
  simpa [K, B, hB, x] using
    stronglyMeasurable_of_galerkin_energy_approximants
      (K := K)
      (hB := hB)
      hsymm hx hB_meas hBx_meas hGalerkin_mem hv_mem' hEnergy'
      hv_tendsto'

theorem measurable_subtype_mk_aeeQuantitativeSlice_of_isLocalSigmaMeasurableOn
    {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} {U : Set (Vec d)} {k : ℕ}
    (A : Ω → CoeffField d) (hA : IsPointwiseLocalSigmaMeasurableOn A U)
    (hSlice : ∀ ω : Ω, AEEQuantitativeEllipticSlice U k (A ω)) :
    @Measurable Ω {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}
      _ (AEEQuantitativeEllipticSlice.localMeasurableSpace U k)
      (fun ω => ⟨A ω, hSlice ω⟩) := by
  let As : Ω → {a : CoeffField d // AEEQuantitativeEllipticSlice U k a} :=
    fun ω => ⟨A ω, hSlice ω⟩
  change @Measurable Ω {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}
    _ (AEEQuantitativeEllipticSlice.localMeasurableSpace U k) As
  apply Measurable.of_comap_le
  unfold AEEQuantitativeEllipticSlice.localMeasurableSpace
  rw [MeasurableSpace.comap_comp]
  simpa [As, IsPointwiseLocalSigmaMeasurableOn, Function.comp] using! hA.comap_le

theorem measurable_blockEnergyAverage_comp_aeeQuantitativeSlice
    {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} {U : Set (Vec d)} {k : ℕ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hToL2 :
      @Measurable {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}
        (MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U))
        (AEEQuantitativeEllipticSlice.localMeasurableSpace U k) (borel _)
        AEEQuantitativeEllipticSlice.toHilbertMatrixL2)
    (A : Ω → CoeffField d) (hA : IsPointwiseLocalSigmaMeasurableOn A U)
    (hSlice : ∀ ω : Ω, AEEQuantitativeEllipticSlice U k (A ω))
    (X : BlockState d) (hX : MemBlockL2 U X.eval) :
    Measurable fun ω => blockEnergyAverage U (A ω) X := by
  let As : Ω → {a : CoeffField d // AEEQuantitativeEllipticSlice U k a} :=
    fun ω => ⟨A ω, hSlice ω⟩
  have hAs :
      @Measurable Ω {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}
        _ (AEEQuantitativeEllipticSlice.localMeasurableSpace U k) As :=
    measurable_subtype_mk_aeeQuantitativeSlice_of_isLocalSigmaMeasurableOn A hA hSlice
  have hEnergy :
      @Measurable {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}
        ℝ (AEEQuantitativeEllipticSlice.localMeasurableSpace U k) (borel ℝ)
        (fun a => blockEnergyAverage U a.1 X) :=
    measurable_blockEnergyAverage_aeeQuantitativeSlice hToL2 X hX
  change Measurable ((fun a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a} =>
    blockEnergyAverage U a.1 X) ∘ As)
  exact hEnergy.comp hAs

theorem measurable_blockPairingAverage_comp_aeeQuantitativeSlice
    {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} {U : Set (Vec d)} {k : ℕ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hToL2 :
      @Measurable {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}
        (MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U))
        (AEEQuantitativeEllipticSlice.localMeasurableSpace U k) (borel _)
        AEEQuantitativeEllipticSlice.toHilbertMatrixL2)
    (A : Ω → CoeffField d) (hA : IsPointwiseLocalSigmaMeasurableOn A U)
    (hSlice : ∀ ω : Ω, AEEQuantitativeEllipticSlice U k (A ω))
    (X Y : BlockState d) (hX : MemBlockL2 U X.eval) (hY : MemBlockL2 U Y.eval) :
    Measurable fun ω => blockPairingAverage U (A ω) X Y := by
  let As : Ω → {a : CoeffField d // AEEQuantitativeEllipticSlice U k a} :=
    fun ω => ⟨A ω, hSlice ω⟩
  have hAs :
      @Measurable Ω {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}
        _ (AEEQuantitativeEllipticSlice.localMeasurableSpace U k) As :=
    measurable_subtype_mk_aeeQuantitativeSlice_of_isLocalSigmaMeasurableOn A hA hSlice
  have hPair :
      @Measurable {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}
        ℝ (AEEQuantitativeEllipticSlice.localMeasurableSpace U k) (borel ℝ)
        (fun a => blockPairingAverage U a.1 X Y) :=
    measurable_blockPairingAverage_aeeQuantitativeSlice hToL2 X Y hX hY
  change Measurable ((fun a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a} =>
    blockPairingAverage U a.1 X Y) ∘ As)
  exact hPair.comp hAs

theorem measurable_blockEnergyAverage_comp_countable_aeeQuantitativeSlice_cover
    {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hToL2 :
      ∀ k : ℕ,
        @Measurable {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}
          (MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U))
          (AEEQuantitativeEllipticSlice.localMeasurableSpace U k) (borel _)
          AEEQuantitativeEllipticSlice.toHilbertMatrixL2)
    (A : Ω → CoeffField d) (hA : IsPointwiseLocalSigmaMeasurableOn A U)
    (t : ℕ → Set Ω) (ht : ∀ k : ℕ, MeasurableSet (t k))
    (hcover : ⋃ k : ℕ, t k = Set.univ)
    (hSlice : ∀ k : ℕ, ∀ ω : Ω, ω ∈ t k →
      AEEQuantitativeEllipticSlice U k (A ω))
    (X : BlockState d) (hX : MemBlockL2 U X.eval) :
    Measurable fun ω => blockEnergyAverage U (A ω) X := by
  classical
  let f : (k : ℕ) → t k → ℝ :=
    fun k ω => blockEnergyAverage U (A ω.1) X
  have hfm : ∀ k : ℕ, Measurable (f k) := by
    intro k
    have hA_sub : IsPointwiseLocalSigmaMeasurableOn (fun ω : t k => A ω.1) U := by
      simpa [IsPointwiseLocalSigmaMeasurableOn, Function.comp] using!
        hA.comp measurable_subtype_coe
    have hSlice_sub :
        ∀ ω : t k,
          AEEQuantitativeEllipticSlice U k ((fun ω : t k => A ω.1) ω) := by
      intro ω
      exact hSlice k ω.1 ω.2
    exact measurable_blockEnergyAverage_comp_aeeQuantitativeSlice
      (hToL2 k) (fun ω : t k => A ω.1) hA_sub hSlice_sub X hX
  have hagree :
      ∀ (i j : ℕ) (ω : Ω) (hωi : ω ∈ t i) (hωj : ω ∈ t j),
        f i ⟨ω, hωi⟩ = f j ⟨ω, hωj⟩ := by
    intro i j ω hωi hωj
    rfl
  have hLift : Measurable (Set.liftCover t f hagree hcover) :=
    measurable_liftCover t ht f hfm hagree hcover
  have hEq : Set.liftCover t f hagree hcover =
      (fun ω => blockEnergyAverage U (A ω) X) := by
    funext ω
    obtain ⟨k, hωk⟩ : ∃ k : ℕ, ω ∈ t k := by
      have hω_cover : ω ∈ ⋃ k : ℕ, t k := by
        rw [hcover]
        exact Set.mem_univ ω
      exact Set.mem_iUnion.mp hω_cover
    rw [Set.liftCover_of_mem (S := t) (f := f) (hf := hagree) (hS := hcover) hωk]
  simpa [hEq] using hLift

theorem aemeasurable_blockEnergyAverage_comp_countable_aeeQuantitativeSlice_cover
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    {d : ℕ} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hToL2 :
      ∀ k : ℕ,
        @Measurable {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}
          (MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U))
          (AEEQuantitativeEllipticSlice.localMeasurableSpace U k) (borel _)
          AEEQuantitativeEllipticSlice.toHilbertMatrixL2)
    (A : Ω → CoeffField d) (hA : IsPointwiseLocalSigmaMeasurableOn A U)
    (t : ℕ → Set Ω) (ht : ∀ k : ℕ, MeasurableSet (t k))
    (hcover_ae : ∀ᵐ ω ∂μ, ω ∈ ⋃ k : ℕ, t k)
    (hSlice : ∀ k : ℕ, ∀ ω : Ω, ω ∈ t k →
      AEEQuantitativeEllipticSlice U k (A ω))
    (X : BlockState d) (hX : MemBlockL2 U X.eval) :
    AEMeasurable (fun ω => blockEnergyAverage U (A ω) X) μ := by
  classical
  let S : Set Ω := ⋃ k : ℕ, t k
  let cover : Option ℕ → Set Ω
    | none => Sᶜ
    | some k => t k
  let f : (i : Option ℕ) → cover i → ℝ
    | none, _ => 0
    | some k, ω => blockEnergyAverage U (A ω.1) X
  have hcover_meas : ∀ i : Option ℕ, MeasurableSet (cover i) := by
    intro i
    cases i with
    | none => exact (MeasurableSet.iUnion ht).compl
    | some k => exact ht k
  have hfm : ∀ i : Option ℕ, Measurable (f i) := by
    intro i
    cases i with
    | none => exact measurable_const
    | some k =>
        have hA_sub : IsPointwiseLocalSigmaMeasurableOn (fun ω : cover (some k) => A ω.1) U := by
          simpa [IsPointwiseLocalSigmaMeasurableOn, Function.comp, cover] using!
            hA.comp measurable_subtype_coe
        have hSlice_sub :
            ∀ ω : cover (some k),
              AEEQuantitativeEllipticSlice U k ((fun ω : cover (some k) => A ω.1) ω) := by
          intro ω
          have hω : ω.1 ∈ t k := by
            simp [cover] at ω
            exact ω.2
          exact hSlice k ω.1 hω
        simpa [f, cover] using
          measurable_blockEnergyAverage_comp_aeeQuantitativeSlice
            (hToL2 k) (fun ω : cover (some k) => A ω.1) hA_sub hSlice_sub X hX
  have hagree :
      ∀ (i j : Option ℕ) (ω : Ω) (hωi : ω ∈ cover i) (hωj : ω ∈ cover j),
        f i ⟨ω, hωi⟩ = f j ⟨ω, hωj⟩ := by
    intro i j ω hωi hωj
    cases i with
    | none =>
        cases j with
        | none => rfl
        | some k =>
            exfalso
            have hωS : ω ∈ S := Set.mem_iUnion.mpr ⟨k, by simpa [cover] using hωj⟩
            have hω_notS : ω ∉ S := by simpa [cover] using hωi
            exact hω_notS hωS
    | some k =>
        cases j with
        | none =>
            exfalso
            have hωS : ω ∈ S := Set.mem_iUnion.mpr ⟨k, by simpa [cover] using hωi⟩
            have hω_notS : ω ∉ S := by simpa [cover] using hωj
            exact hω_notS hωS
        | some _ => rfl
  have hcover : ⋃ i : Option ℕ, cover i = Set.univ := by
    ext ω
    constructor
    · intro _hω
      exact Set.mem_univ ω
    · intro _hω
      by_cases hωS : ω ∈ S
      · obtain ⟨k, hωk⟩ := Set.mem_iUnion.mp hωS
        exact Set.mem_iUnion.mpr ⟨some k, by simpa [cover] using hωk⟩
      · exact Set.mem_iUnion.mpr ⟨none, by simpa [cover] using hωS⟩
  have hLift : Measurable (Set.liftCover cover f hagree hcover) :=
    measurable_liftCover cover hcover_meas f hfm hagree hcover
  have hEq :
      (fun ω => blockEnergyAverage U (A ω) X) =ᵐ[μ]
        Set.liftCover cover f hagree hcover := by
    filter_upwards [hcover_ae] with ω hωS
    obtain ⟨k, hωk⟩ := Set.mem_iUnion.mp hωS
    rw [Set.liftCover_of_mem
      (S := cover) (f := f) (hf := hagree) (hS := hcover) (i := some k)
      (by simpa [cover] using hωk)]
  exact hLift.aemeasurable.congr hEq.symm

theorem measurable_blockEnergyAverage_comp_aeeQuantitativeSlice_sets
    {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hToL2 :
      ∀ k : ℕ,
        @Measurable {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}
          (MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U))
          (AEEQuantitativeEllipticSlice.localMeasurableSpace U k) (borel _)
          AEEQuantitativeEllipticSlice.toHilbertMatrixL2)
    (A : Ω → CoeffField d) (hA : IsPointwiseLocalSigmaMeasurableOn A U)
    (hSliceMeas :
      ∀ k : ℕ, MeasurableSet {ω : Ω | AEEQuantitativeEllipticSlice U k (A ω)})
    (hcover : ∀ ω : Ω, ∃ k : ℕ, AEEQuantitativeEllipticSlice U k (A ω))
    (X : BlockState d) (hX : MemBlockL2 U X.eval) :
    Measurable fun ω => blockEnergyAverage U (A ω) X := by
  classical
  let t : ℕ → Set Ω := fun k => {ω : Ω | AEEQuantitativeEllipticSlice U k (A ω)}
  have ht : ∀ k : ℕ, MeasurableSet (t k) := hSliceMeas
  have hcover_set : ⋃ k : ℕ, t k = Set.univ := by
    ext ω
    constructor
    · intro _hω
      exact Set.mem_univ ω
    · intro _hω
      exact Set.mem_iUnion.mpr (hcover ω)
  exact measurable_blockEnergyAverage_comp_countable_aeeQuantitativeSlice_cover
    hToL2 A hA t ht hcover_set (fun k ω hω => hω) X hX

theorem aemeasurable_blockEnergyAverage_comp_aeeQuantitativeSlice_sets
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    {d : ℕ} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hToL2 :
      ∀ k : ℕ,
        @Measurable {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}
          (MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U))
          (AEEQuantitativeEllipticSlice.localMeasurableSpace U k) (borel _)
          AEEQuantitativeEllipticSlice.toHilbertMatrixL2)
    (A : Ω → CoeffField d) (hA : IsPointwiseLocalSigmaMeasurableOn A U)
    (hSliceMeas :
      ∀ k : ℕ, MeasurableSet {ω : Ω | AEEQuantitativeEllipticSlice U k (A ω)})
    (hcover_ae : ∀ᵐ ω ∂μ, ∃ k : ℕ, AEEQuantitativeEllipticSlice U k (A ω))
    (X : BlockState d) (hX : MemBlockL2 U X.eval) :
    AEMeasurable (fun ω => blockEnergyAverage U (A ω) X) μ := by
  classical
  let t : ℕ → Set Ω := fun k => {ω : Ω | AEEQuantitativeEllipticSlice U k (A ω)}
  have ht : ∀ k : ℕ, MeasurableSet (t k) := hSliceMeas
  have hcover_set_ae : ∀ᵐ ω ∂μ, ω ∈ ⋃ k : ℕ, t k := by
    filter_upwards [hcover_ae] with ω hω
    exact Set.mem_iUnion.mpr hω
  exact aemeasurable_blockEnergyAverage_comp_countable_aeeQuantitativeSlice_cover
    μ hToL2 A hA t ht hcover_set_ae (fun k ω hω => hω) X hX

theorem aemeasurable_blockEnergyAverage_comp_aeeQuantitativeSlice_sets_of_isOpen_volume_ne_top
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    {d : ℕ} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hUopen : IsOpen U) (hUfinite : MeasureTheory.volume U ≠ ⊤)
    (A : Ω → CoeffField d) (hA : IsPointwiseLocalSigmaMeasurableOn A U)
    (hSliceMeas :
      ∀ k : ℕ, MeasurableSet {ω : Ω | AEEQuantitativeEllipticSlice U k (A ω)})
    (hcover_ae : ∀ᵐ ω ∂μ, ∃ k : ℕ, AEEQuantitativeEllipticSlice U k (A ω))
    (X : BlockState d) (hX : MemBlockL2 U X.eval) :
    AEMeasurable (fun ω => blockEnergyAverage U (A ω) X) μ := by
  exact aemeasurable_blockEnergyAverage_comp_aeeQuantitativeSlice_sets μ
    (fun _k => measurable_toHilbertMatrixL2_aee_of_isOpen_volume_ne_top hUopen hUfinite)
    A hA hSliceMeas hcover_ae X hX
end Homogenization
