/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MuQuadratic
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MuOperator.CoeffOperator
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MuRecovery.CorrectionSpaceEnergy
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Internal.CoarseObservableMeasurability.Mu
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Internal.FixedCompetitorEnergyMeasurability.LipschitzBounds
import LeanPool.CoarseGraining.Homogenization.Probability.LocalEllipticitySlices
import LeanPool.CoarseGraining.Homogenization.Probability.LocalObservable
import LeanPool.CoarseGraining.Homogenization.Probability.RandomFieldMeasurability
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Function.UniformIntegrable

/-! # Integrals -/

namespace Homogenization

open scoped Manifold
open scoped ENNReal
open scoped Topology
open Filter

/-!
# Audit tag (Ch4 rebuild contract `CH04_REBUILD_SURFACE_2026-05-16.md`)

**Internal claim:** integrability and a.e. membership of `toHilbertMatrixL2`
in the quantitative-elliptic Hilbert-matrix set, plus the Bochner-integral
algebra needed to take the Lipschitz scalar atoms from `LipschitzBounds.lean`
and turn them into measurable energy-functional integrals on quantitative
slices.

**Consumed by (within `Internal/FixedCompetitorEnergyMeasurability/`):**
`BlockEnergyAverage.lean`. Upstream chain continues to
`Theorems/Mu.lean :: aemeasurable_Mu_cubeSet`.

If the single-claim summary above grows into three or more distinct
claims, split or refactor per the rebuild contract.
-/

theorem QuantitativeEllipticSlice.ae_toHilbertMatrixL2_mem_quantitativeEllipticHilbertMatSet
    {d : ℕ} {U : Set (Vec d)} {k : ℕ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (a : {a : CoeffField d // QuantitativeEllipticSlice U k a}) :
    ∀ᵐ x ∂ volumeMeasureOn U,
      QuantitativeEllipticSlice.toHilbertMatrixL2 a x ∈
        quantitativeEllipticHilbertMatSet d k := by
  have hmem : ∀ᵐ x ∂ volumeMeasureOn U, x ∈ U := by
    exact
      (MeasureTheory.ae_restrict_iff' (measurableSet_of_isEllipticFieldOn a.2)).2
        (Filter.Eventually.of_forall fun x hx => hx)
  filter_upwards [QuantitativeEllipticSlice.coeFn_toHilbertMatrixL2 a, hmem] with x hcoeff hx
  rw [hcoeff]
  simpa [quantitativeEllipticHilbertMatSet, restrictCoeffField, hx] using a.2.2 x hx

theorem IsPointwiseLocalSigmaMeasurableOn.measurable_entryTestObservable
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {A : Ω → CoeffField d} {U : Set (Vec d)}
    (hA : IsPointwiseLocalSigmaMeasurableOn A U) (i j : Fin d) {φ : Vec d → ℝ}
    (hφ_cont : ContDiff ℝ (⊤ : ℕ∞) φ) (hφ_compact : HasCompactSupport φ)
    (hφ_support : tsupport φ ⊆ U) :
    Measurable fun ω => ∫ x, A ω x i j * φ x ∂MeasureTheory.volume := by
  exact (measurable_entryTestObservable_localSigma
    (U := U) i j hφ_cont hφ_compact hφ_support).comp hA

theorem measurable_blockEnergyDensity_eval {d : ℕ} (X : BlockState d) (x : Vec d) :
    Measurable fun a : CoeffField d => blockEnergyDensity a X x := by
  have hFull :
      Measurable fun a : CoeffField d =>
        toFullBlockMat (blockCoeffField a x) :=
    measurable_toFullBlockMat_blockCoeffField (d := d) (measurable_coeffField_eval (d := d) x)
  have hQuad :
      Measurable
        (fun a : CoeffField d =>
          (1 / 2 : ℝ) *
            blockVecDot (X.eval x)
              (blockMatVecMul (ofFullBlockMat (toFullBlockMat (blockCoeffField a x)))
                (X.eval x))) :=
    measurable_half_blockVecDot_blockMatVecMul_of_measurable_fullBlockMat
      (d := d) hFull (X.eval x)
  simpa [blockEnergyDensity] using hQuad

theorem blockEnergyDensity_eq_sum_fullBlockMat_entries {d : ℕ}
    (a : CoeffField d) (X : BlockState d) (x : Vec d) :
    blockEnergyDensity a X x =
      (1 / 2 : ℝ) *
        ∑ α, ∑ β,
          toFullBlockVec (X.eval x) α *
            toFullBlockVec (X.eval x) β *
              toFullBlockMat (blockCoeffField a x) α β := by
  rw [blockEnergyDensity, blockVecDot_blockMatVecMul_eq_toLinearMap₂',
    Matrix.toLinearMap₂'_apply]
  simp [smul_eq_mul, mul_assoc, mul_left_comm]

theorem memScalarL2_fullBlockCoord_of_memBlockL2 {d : ℕ} {U : Set (Vec d)}
    {F : Vec d → BlockVec d} (hF : MemBlockL2 U F) (α : BlockCoord d) :
    MemScalarL2 U (fun x => toFullBlockVec (F x) α) := by
  cases α with
  | inl i =>
      simpa [toFullBlockVec] using
        memScalarL2_coord_of_memVectorL2 (memVectorL2_fst_of_memBlockL2 hF) i
  | inr i =>
      simpa [toFullBlockVec] using
        memScalarL2_coord_of_memVectorL2 (memVectorL2_snd_of_memBlockL2 hF) i

theorem integrableOn_fullBlockCoord_mul_of_memBlockL2 {d : ℕ} {U : Set (Vec d)}
    {F : Vec d → BlockVec d} (hF : MemBlockL2 U F) (α β : BlockCoord d) :
    MeasureTheory.IntegrableOn
      (fun x => toFullBlockVec (F x) α * toFullBlockVec (F x) β) U := by
  simpa [MeasureTheory.IntegrableOn, volumeMeasureOn] using!
    (memScalarL2_fullBlockCoord_of_memBlockL2 hF α).integrable_mul
      (memScalarL2_fullBlockCoord_of_memBlockL2 hF β)

private theorem vecNormSq_single_one {d : ℕ} (i : Fin d) :
    vecNormSq (Pi.single i 1 : Vec d) = 1 := by
  rw [vecNormSq, vecDot, Finset.sum_eq_single i]
  · simp
  · intro k _ hki
    simp [Pi.single_eq_of_ne hki]
  · simp

private theorem blockVecDot_blockBasis_self {d : ℕ} (α : BlockCoord d) :
    blockVecDot (blockBasis α) (blockBasis α) = 1 := by
  cases α with
  | inl i =>
      change vecNormSq (Pi.single i 1 : Vec d) + vecNormSq (0 : Vec d) = 1
      rw [vecNormSq_single_one]
      simp [vecNormSq, vecDot]
  | inr i =>
      change vecNormSq (0 : Vec d) + vecNormSq (Pi.single i 1 : Vec d) = 1
      rw [vecNormSq_single_one]
      simp [vecNormSq, vecDot]

theorem abs_toFullBlockMat_blockMatrixOfCoeff_entry_le_of_isEllipticMatrix
    {d : ℕ} {A : Mat d} {lam Lam : ℝ} (hA : IsEllipticMatrix lam Lam A)
    (α β : BlockCoord d) :
    |toFullBlockMat (blockMatrixOfCoeff A) α β| ≤
      Real.sqrt (blockMatrixOfCoeffNormSqBound lam Lam) := by
  let B : BlockMat d := blockMatrixOfCoeff A
  let eα : BlockVec d := blockBasis α
  let eβ : BlockVec d := blockBasis β
  have hentry :
      blockVecDot eα (blockMatVecMul B eβ) =
        toFullBlockMat (blockMatrixOfCoeff A) α β := by
    simpa [B, eα, eβ, toFullBlockMat, blockMatEntry] using
      blockBasis_pairing B α β
  have hbasisα : blockVecDot eα eα = 1 := by
    simpa [eα] using blockVecDot_blockBasis_self α
  have hbasisβ : blockVecDot eβ eβ = 1 := by
    simpa [eβ] using blockVecDot_blockBasis_self β
  have hsq :
      (toFullBlockMat (blockMatrixOfCoeff A) α β) ^ 2 ≤
        blockVecDot eα eα * blockVecDot (blockMatVecMul B eβ) (blockMatVecMul B eβ) := by
    calc
      (toFullBlockMat (blockMatrixOfCoeff A) α β) ^ 2
          = (blockVecDot eα (blockMatVecMul B eβ)) ^ 2 := by rw [hentry]
      _ ≤ blockVecDot eα eα * blockVecDot (blockMatVecMul B eβ) (blockMatVecMul B eβ) :=
        sq_blockVecDot_le_blockVecDot_mul_blockVecDot eα (blockMatVecMul B eβ)
  have himage :
      blockVecDot (blockMatVecMul B eβ) (blockMatVecMul B eβ) ≤
        blockMatrixOfCoeffNormSqBound lam Lam := by
    have h := blockMatrixOfCoeff_image_bound_of_isEllipticMatrix hA eβ
    simpa [B, hbasisβ] using h
  have hsq' :
      (toFullBlockMat (blockMatrixOfCoeff A) α β) ^ 2 ≤
        blockMatrixOfCoeffNormSqBound lam Lam := by
    rw [hbasisα] at hsq
    nlinarith
  have hbound_nonneg : 0 ≤ blockMatrixOfCoeffNormSqBound lam Lam :=
    blockMatrixOfCoeffNormSqBound_nonneg lam Lam
  have habs_sq :
      |toFullBlockMat (blockMatrixOfCoeff A) α β| ^ 2 ≤
        blockMatrixOfCoeffNormSqBound lam Lam := by
    simpa [sq_abs] using hsq'
  have hsqrt_nonneg : 0 ≤ Real.sqrt (blockMatrixOfCoeffNormSqBound lam Lam) := by
    exact Real.sqrt_nonneg _
  have habs_nonneg : 0 ≤ |toFullBlockMat (blockMatrixOfCoeff A) α β| := by
    exact abs_nonneg _
  nlinarith [habs_sq, Real.sq_sqrt hbound_nonneg, hsqrt_nonneg, habs_nonneg,
    sq_nonneg (Real.sqrt (blockMatrixOfCoeffNormSqBound lam Lam) -
      |toFullBlockMat (blockMatrixOfCoeff A) α β|)]

theorem abs_fullBlockCoeffEntry_hilbertMat_le_of_mem_quantitativeEllipticHilbertMatSet
    {d : ℕ} {k : ℕ} {A : HilbertMat d}
    (hA : A ∈ quantitativeEllipticHilbertMatSet d k) (α β : BlockCoord d) :
    |toFullBlockMat (blockMatrixOfCoeff A.toMat) α β| ≤
      Real.sqrt (blockMatrixOfCoeffNormSqBound ((k + 1 : ℝ)⁻¹) (k + 1 : ℝ)) :=
  abs_toFullBlockMat_blockMatrixOfCoeff_entry_le_of_isEllipticMatrix hA α β

theorem QuantitativeEllipticSlice.ae_fullBlockCoeffEntry_toHilbertMatrixL2_eq
    {d : ℕ} {U : Set (Vec d)} {k : ℕ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (a : {a : CoeffField d // QuantitativeEllipticSlice U k a})
    (α β : BlockCoord d) :
    (fun x => toFullBlockMat (blockCoeffField a.1 x) α β)
      =ᵐ[volumeMeasureOn U]
        fun x =>
          toFullBlockMat
            (blockMatrixOfCoeff (QuantitativeEllipticSlice.toHilbertMatrixL2 a x).toMat)
            α β := by
  have hmem : ∀ᵐ x ∂ volumeMeasureOn U, x ∈ U := by
    exact
      (MeasureTheory.ae_restrict_iff' (measurableSet_of_isEllipticFieldOn a.2)).2
        (Filter.Eventually.of_forall fun x hx => hx)
  filter_upwards [QuantitativeEllipticSlice.coeFn_toHilbertMatrixL2 a, hmem] with x hcoeff hx
  rw [hcoeff]
  simp [blockCoeffField, restrictCoeffField, hx]

theorem QuantitativeEllipticSlice.ae_abs_fullBlockCoeffEntry_toHilbertMatrixL2_le
    {d : ℕ} {U : Set (Vec d)} {k : ℕ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (a : {a : CoeffField d // QuantitativeEllipticSlice U k a})
    (α β : BlockCoord d) :
    ∀ᵐ x ∂ volumeMeasureOn U,
      |toFullBlockMat
          (blockMatrixOfCoeff (QuantitativeEllipticSlice.toHilbertMatrixL2 a x).toMat) α β| ≤
        Real.sqrt (blockMatrixOfCoeffNormSqBound ((k + 1 : ℝ)⁻¹) (k + 1 : ℝ)) := by
  filter_upwards
      [QuantitativeEllipticSlice.ae_toHilbertMatrixL2_mem_quantitativeEllipticHilbertMatSet a]
    with x hx
  exact abs_fullBlockCoeffEntry_hilbertMat_le_of_mem_quantitativeEllipticHilbertMatSet hx α β

theorem QuantitativeEllipticSlice.weightedFullBlockCoeffEntryIntegral_eq_hilbertMatrixL2
    {d : ℕ} {U : Set (Vec d)} {k : ℕ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (a : {a : CoeffField d // QuantitativeEllipticSlice U k a})
    (w : Vec d → ℝ) (α β : BlockCoord d) :
    ∫ x in U, w x * toFullBlockMat (blockCoeffField a.1 x) α β ∂MeasureTheory.volume =
      ∫ x,
        w x *
          toFullBlockMat
            (blockMatrixOfCoeff (QuantitativeEllipticSlice.toHilbertMatrixL2 a x).toMat)
            α β ∂volumeMeasureOn U := by
  unfold volumeMeasureOn
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards
      [QuantitativeEllipticSlice.ae_fullBlockCoeffEntry_toHilbertMatrixL2_eq a α β]
    with x hx
  rw [hx]

private theorem LipschitzWith.sub_const_right_real
    {E : Type*} [PseudoMetricSpace E] {K : NNReal} {Q : E → ℝ}
    (hQ : LipschitzWith K Q) (c : ℝ) :
    LipschitzWith K (fun A => Q A - c) := by
  refine LipschitzWith.of_dist_le_mul ?_
  intro A B
  simpa [dist_sub_right] using hQ.dist_le_mul A B

private theorem lipschitzHilbertMatrixL2Pairing_eq_integral
    {d : ℕ} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {w : Vec d → ℝ} (hw : MemScalarL2 U w)
    {K : NNReal} {Q : HilbertMat d → ℝ} (hQ : LipschitzWith K Q)
    (F : MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U)) :
    inner ℝ (toScalarL2 hw)
        ((LipschitzWith.sub_const_right_real hQ (Q (0 : HilbertMat d))).compLp (by simp) F +
          MeasureTheory.Lp.const 2 (volumeMeasureOn U) (Q (0 : HilbertMat d))) =
      ∫ x, w x * Q (F x) ∂volumeMeasureOn U := by
  let Q0 : HilbertMat d → ℝ := fun A => Q A - Q (0 : HilbertMat d)
  let hQ0 : LipschitzWith K Q0 :=
    LipschitzWith.sub_const_right_real hQ (Q (0 : HilbertMat d))
  have hQ0_zero : Q0 0 = 0 := by simp [Q0]
  rw [MeasureTheory.L2.inner_def]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards
      [coeFn_toScalarL2 hw,
       LipschitzWith.coeFn_compLp hQ0 hQ0_zero F,
       MeasureTheory.Lp.coeFn_add
        (hQ0.compLp hQ0_zero F)
        (MeasureTheory.Lp.const 2 (volumeMeasureOn U) (Q (0 : HilbertMat d))),
       MeasureTheory.Lp.coeFn_const
        (μ := volumeMeasureOn U) (p := 2) (Q (0 : HilbertMat d))]
    with x hweight hcomp hadd hconst
  rw [hweight, hadd]
  change inner ℝ (w x)
      ((hQ0.compLp hQ0_zero F : ScalarL2 U) x +
        (MeasureTheory.Lp.const 2 (volumeMeasureOn U) (Q (0 : HilbertMat d)) :
          ScalarL2 U) x) =
    w x * Q (F x)
  rw [hcomp, hconst]
  simp [Q0]
  ring

/-- If a scalar observable of a Hilbert-matrix value has a global Lipschitz
extension, then its `L²`-weighted integral is measurable as a function of the
`L²` Hilbert-matrix field.  This is the Nemytskii/pairing bridge used before
the final `L¹` weight approximation. -/
theorem measurable_l2WeightedHilbertMatrixLipschitzIntegral
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {d : ℕ} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {F : Ω → MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U)}
    (hF :
      @Measurable Ω (MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U))
        mΩ (borel _) F)
    {w : Vec d → ℝ} (hw : MemScalarL2 U w)
    {K : NNReal} {Q : HilbertMat d → ℝ} (hQ : LipschitzWith K Q) :
    @Measurable Ω ℝ mΩ (borel ℝ)
      (fun ω => ∫ x, w x * Q (F ω x) ∂volumeMeasureOn U) := by
  let H := MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U)
  let : MeasurableSpace Ω := mΩ
  let : MeasurableSpace H := borel H
  have : BorelSpace H := ⟨rfl⟩
  let hQ0 : LipschitzWith K (fun A : HilbertMat d => Q A - Q (0 : HilbertMat d)) :=
    LipschitzWith.sub_const_right_real hQ (Q (0 : HilbertMat d))
  let G : MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U) → ScalarL2 U :=
    fun F => hQ0.compLp (by simp) F +
      MeasureTheory.Lp.const 2 (volumeMeasureOn U) (Q (0 : HilbertMat d))
  have hG_cont : Continuous G := by
    have hcomp :
        Continuous
          (hQ0.compLp (by simp) :
            MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U) → ScalarL2 U) :=
      hQ0.continuous_compLp (by simp)
    simpa [G] using! hcomp.add continuous_const
  have hpair_cont :
      Continuous fun F : MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U) =>
        inner ℝ (toScalarL2 hw) (G F) :=
    continuous_const.inner hG_cont
  rw [show
      (fun ω => ∫ x, w x * Q (F ω x) ∂volumeMeasureOn U) =
        fun ω => inner ℝ (toScalarL2 hw) (G (F ω)) by
        funext ω
        exact (lipschitzHilbertMatrixL2Pairing_eq_integral hw hQ (F ω)).symm]
  exact hpair_cont.measurable.comp hF

/-- Slice-level version of the Lipschitz-extension bridge for a full-block
coefficient entry.  The agreement hypothesis keeps the theorem independent of
the later finite-dimensional extension construction. -/
theorem QuantitativeEllipticSlice.measurable_l2WeightedFullBlockCoeffEntryIntegral_of_lipschitzExtension
    {d : ℕ} {U : Set (Vec d)} {k : ℕ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hToL2 :
      @Measurable {a : CoeffField d // QuantitativeEllipticSlice U k a}
        (MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U))
        (QuantitativeEllipticSlice.localMeasurableSpace U k) (borel _)
        QuantitativeEllipticSlice.toHilbertMatrixL2)
    {w : Vec d → ℝ} (hw : MemScalarL2 U w) (α β : BlockCoord d)
    {K : NNReal} {Q : HilbertMat d → ℝ} (hQ : LipschitzWith K Q)
    (hQ_eq :
      ∀ A ∈ quantitativeEllipticHilbertMatSet d k,
        Q A = toFullBlockMat (blockMatrixOfCoeff A.toMat) α β) :
    @Measurable {a : CoeffField d // QuantitativeEllipticSlice U k a}
      ℝ (QuantitativeEllipticSlice.localMeasurableSpace U k) (borel ℝ)
      (fun a =>
        ∫ x in U,
          w x * toFullBlockMat (blockCoeffField a.1 x) α β ∂MeasureTheory.volume) := by
  rw [show
      (fun a : {a : CoeffField d // QuantitativeEllipticSlice U k a} =>
        ∫ x in U,
          w x * toFullBlockMat (blockCoeffField a.1 x) α β ∂MeasureTheory.volume) =
        fun a : {a : CoeffField d // QuantitativeEllipticSlice U k a} =>
          ∫ x,
            w x * Q (QuantitativeEllipticSlice.toHilbertMatrixL2 a x)
              ∂volumeMeasureOn U by
        funext a
        calc
          ∫ x in U, w x * toFullBlockMat (blockCoeffField a.1 x) α β
              ∂MeasureTheory.volume =
            ∫ x,
              w x *
                toFullBlockMat
                  (blockMatrixOfCoeff
                    (QuantitativeEllipticSlice.toHilbertMatrixL2 a x).toMat) α β
                ∂volumeMeasureOn U :=
            QuantitativeEllipticSlice.weightedFullBlockCoeffEntryIntegral_eq_hilbertMatrixL2
              a w α β
          _ =
            ∫ x,
              w x * Q (QuantitativeEllipticSlice.toHilbertMatrixL2 a x)
                ∂volumeMeasureOn U := by
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards
                [QuantitativeEllipticSlice.ae_toHilbertMatrixL2_mem_quantitativeEllipticHilbertMatSet
                  a]
              with x hx
            rw [hQ_eq _ hx]]
  exact measurable_l2WeightedHilbertMatrixLipschitzIntegral hToL2 hw hQ

/-- Open finite-measure wrapper for the `L²`-weighted full-block entry bridge.
The only remaining external input is the finite-dimensional Lipschitz extension
of the entry observable. -/
theorem QuantitativeEllipticSlice.measurable_l2WeightedFullBlockCoeffEntryIntegral_of_isOpen_volume_ne_top_of_lipschitzExtension
    {d : ℕ} {U : Set (Vec d)} {k : ℕ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hUopen : IsOpen U) (hUfinite : MeasureTheory.volume U ≠ ⊤)
    {w : Vec d → ℝ} (hw : MemScalarL2 U w) (α β : BlockCoord d)
    {K : NNReal} {Q : HilbertMat d → ℝ} (hQ : LipschitzWith K Q)
    (hQ_eq :
      ∀ A ∈ quantitativeEllipticHilbertMatSet d k,
        Q A = toFullBlockMat (blockMatrixOfCoeff A.toMat) α β) :
    @Measurable {a : CoeffField d // QuantitativeEllipticSlice U k a}
      ℝ (QuantitativeEllipticSlice.localMeasurableSpace U k) (borel ℝ)
      (fun a =>
        ∫ x in U,
          w x * toFullBlockMat (blockCoeffField a.1 x) α β ∂MeasureTheory.volume) := by
  exact
    QuantitativeEllipticSlice.measurable_l2WeightedFullBlockCoeffEntryIntegral_of_lipschitzExtension
      (measurable_toHilbertMatrixL2_of_isOpen_volume_ne_top hUopen hUfinite)
      hw α β hQ hQ_eq

/-- If the finite-dimensional full-block entry is Lipschitz on the
quantitative elliptic value set, then the `L²`-weighted entry integral is
measurable on the slice.  The global Lipschitz extension is supplied by
`LipschitzOnWith.extend_real`. -/
theorem QuantitativeEllipticSlice.measurable_l2WeightedFullBlockCoeffEntryIntegral_of_lipschitzOn
    {d : ℕ} {U : Set (Vec d)} {k : ℕ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hToL2 :
      @Measurable {a : CoeffField d // QuantitativeEllipticSlice U k a}
        (MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U))
        (QuantitativeEllipticSlice.localMeasurableSpace U k) (borel _)
        QuantitativeEllipticSlice.toHilbertMatrixL2)
    {w : Vec d → ℝ} (hw : MemScalarL2 U w) (α β : BlockCoord d)
    {K : NNReal}
    (hLip :
      LipschitzOnWith K
        (fun A : HilbertMat d => toFullBlockMat (blockMatrixOfCoeff A.toMat) α β)
        (quantitativeEllipticHilbertMatSet d k)) :
    @Measurable {a : CoeffField d // QuantitativeEllipticSlice U k a}
      ℝ (QuantitativeEllipticSlice.localMeasurableSpace U k) (borel ℝ)
      (fun a =>
        ∫ x in U,
          w x * toFullBlockMat (blockCoeffField a.1 x) α β ∂MeasureTheory.volume) := by
  obtain ⟨Q, hQ_lip, hQ_eq_on⟩ := hLip.extend_real
  refine
    QuantitativeEllipticSlice.measurable_l2WeightedFullBlockCoeffEntryIntegral_of_lipschitzExtension
      hToL2 hw α β hQ_lip ?_
  intro A hA
  exact (hQ_eq_on hA).symm

/-- Open finite-measure wrapper for the Lipschitz-on-value-set version. -/
theorem QuantitativeEllipticSlice.measurable_l2WeightedFullBlockCoeffEntryIntegral_of_isOpen_volume_ne_top_of_lipschitzOn
    {d : ℕ} {U : Set (Vec d)} {k : ℕ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hUopen : IsOpen U) (hUfinite : MeasureTheory.volume U ≠ ⊤)
    {w : Vec d → ℝ} (hw : MemScalarL2 U w) (α β : BlockCoord d)
    {K : NNReal}
    (hLip :
      LipschitzOnWith K
        (fun A : HilbertMat d => toFullBlockMat (blockMatrixOfCoeff A.toMat) α β)
        (quantitativeEllipticHilbertMatSet d k)) :
    @Measurable {a : CoeffField d // QuantitativeEllipticSlice U k a}
      ℝ (QuantitativeEllipticSlice.localMeasurableSpace U k) (borel ℝ)
      (fun a =>
        ∫ x in U,
          w x * toFullBlockMat (blockCoeffField a.1 x) α β ∂MeasureTheory.volume) := by
  exact
    QuantitativeEllipticSlice.measurable_l2WeightedFullBlockCoeffEntryIntegral_of_lipschitzOn
      (measurable_toHilbertMatrixL2_of_isOpen_volume_ne_top hUopen hUfinite)
      hw α β hLip

/-- Slice-level `L²`-weighted full-block entry measurability with the
finite-dimensional quantitative Lipschitz estimate supplied internally. -/
theorem QuantitativeEllipticSlice.measurable_l2WeightedFullBlockCoeffEntryIntegral
    {d : ℕ} {U : Set (Vec d)} {k : ℕ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hToL2 :
      @Measurable {a : CoeffField d // QuantitativeEllipticSlice U k a}
        (MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U))
        (QuantitativeEllipticSlice.localMeasurableSpace U k) (borel _)
        QuantitativeEllipticSlice.toHilbertMatrixL2)
    {w : Vec d → ℝ} (hw : MemScalarL2 U w) (α β : BlockCoord d) :
    @Measurable {a : CoeffField d // QuantitativeEllipticSlice U k a}
      ℝ (QuantitativeEllipticSlice.localMeasurableSpace U k) (borel ℝ)
      (fun a =>
        ∫ x in U,
          w x * toFullBlockMat (blockCoeffField a.1 x) α β ∂MeasureTheory.volume) := by
  exact
    QuantitativeEllipticSlice.measurable_l2WeightedFullBlockCoeffEntryIntegral_of_lipschitzOn
      hToL2 hw α β
      (lipschitzOnWith_fullBlockCoeffEntry_hilbertMat_quantitative α β)

/-- Open finite-measure wrapper for the fully internal `L²`-weighted
full-block entry measurability theorem. -/
theorem QuantitativeEllipticSlice.measurable_l2WeightedFullBlockCoeffEntryIntegral_of_isOpen_volume_ne_top
    {d : ℕ} {U : Set (Vec d)} {k : ℕ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hUopen : IsOpen U) (hUfinite : MeasureTheory.volume U ≠ ⊤)
    {w : Vec d → ℝ} (hw : MemScalarL2 U w) (α β : BlockCoord d) :
    @Measurable {a : CoeffField d // QuantitativeEllipticSlice U k a}
      ℝ (QuantitativeEllipticSlice.localMeasurableSpace U k) (borel ℝ)
      (fun a =>
        ∫ x in U,
          w x * toFullBlockMat (blockCoeffField a.1 x) α β ∂MeasureTheory.volume) := by
  exact
    QuantitativeEllipticSlice.measurable_l2WeightedFullBlockCoeffEntryIntegral
      (measurable_toHilbertMatrixL2_of_isOpen_volume_ne_top hUopen hUfinite)
      hw α β

theorem abs_toFullBlockMat_blockCoeffField_entry_le_of_isEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U a) {x : Vec d} (hx : x ∈ U)
    (α β : BlockCoord d) :
    |toFullBlockMat (blockCoeffField a x) α β| ≤
      Real.sqrt (blockMatrixOfCoeffNormSqBound lam Lam) := by
  simpa [blockCoeffField] using
    abs_toFullBlockMat_blockMatrixOfCoeff_entry_le_of_isEllipticMatrix
      (A := a x) (hEll.2 x hx) α β

theorem QuantitativeEllipticSlice.integrable_weightedFullBlockCoeffEntry_of_integrable
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    {k : ℕ} {w : Vec d → ℝ} (hSlice : QuantitativeEllipticSlice U k a)
    (hw : MeasureTheory.Integrable w (volumeMeasureOn U)) (α β : BlockCoord d) :
    MeasureTheory.Integrable
      (fun x => w x * toFullBlockMat (blockCoeffField a x) α β)
      (volumeMeasureOn U) := by
  classical
  let coeff : Vec d → ℝ := fun x => toFullBlockMat (blockCoeffField a x) α β
  let aExt : Vec d → Fin d → Fin d → ℝ := fun x i j => if x ∈ U then a x i j else 0
  have haExt : Measurable aExt := by
    simpa [aExt] using hSlice.1
  have hblock :
      Measurable (fun x γ δ =>
        toFullBlockMat (blockMatrixOfCoeff (aExt x)) γ δ) :=
    measurable_toFullBlockMat_blockCoeffField haExt
  have hcoeffExt :
      Measurable (fun x => toFullBlockMat (blockMatrixOfCoeff (aExt x)) α β) :=
    measurable_pi_iff.1 (measurable_pi_iff.1 hblock α) β
  have hmem : ∀ᵐ x ∂ volumeMeasureOn U, x ∈ U := by
    exact
      (MeasureTheory.ae_restrict_iff' (measurableSet_of_isEllipticFieldOn hSlice)).2
        (Filter.Eventually.of_forall fun x hx => hx)
  have hcoeff_ae : AEMeasurable coeff (volumeMeasureOn U) := by
    refine (Measurable.aemeasurable hcoeffExt).congr ?_
    filter_upwards [hmem] with x hx
    simp [coeff, aExt, blockCoeffField, hx]
  have hbound :
      ∀ᵐ x ∂ volumeMeasureOn U,
        ‖coeff x‖ ≤ Real.sqrt (blockMatrixOfCoeffNormSqBound ((k + 1 : ℝ)⁻¹) (k + 1 : ℝ)) := by
    filter_upwards [hmem] with x hx
    simpa [coeff, Real.norm_eq_abs] using
      abs_toFullBlockMat_blockCoeffField_entry_le_of_isEllipticFieldOn hSlice hx α β
  simpa [coeff] using hw.mul_bdd hcoeff_ae.aestronglyMeasurable hbound

/-- `L¹` deterministic weights are enough for slice-level full-block entry
measurability, provided the weight is represented by an honest measurable
function.  The proof approximates the weight by simple functions, uses the
already-proved `L²` theorem for each approximant, and passes to the limit by
the uniform quantitative ellipticity bound on the slice. -/
theorem QuantitativeEllipticSlice.measurable_integrableWeightedFullBlockCoeffEntryIntegral_of_measurable
    {d : ℕ} {U : Set (Vec d)} {k : ℕ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hToL2 :
      @Measurable {a : CoeffField d // QuantitativeEllipticSlice U k a}
        (MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U))
        (QuantitativeEllipticSlice.localMeasurableSpace U k) (borel _)
        QuantitativeEllipticSlice.toHilbertMatrixL2)
    {w : Vec d → ℝ} (hw_meas : Measurable w)
    (hw_int : MeasureTheory.Integrable w (volumeMeasureOn U)) (α β : BlockCoord d) :
    @Measurable {a : CoeffField d // QuantitativeEllipticSlice U k a}
      ℝ (QuantitativeEllipticSlice.localMeasurableSpace U k) (borel ℝ)
      (fun a =>
        ∫ x in U,
          w x * toFullBlockMat (blockCoeffField a.1 x) α β ∂MeasureTheory.volume) := by
  classical
  let μ := volumeMeasureOn U
  let C : ℝ :=
    Real.sqrt (blockMatrixOfCoeffNormSqBound ((k + 1 : ℝ)⁻¹) (k + 1 : ℝ))
  let s : ℕ → Vec d → ℝ :=
    fun n => MeasureTheory.SimpleFunc.approxOn w hw_meas (Set.range w ∪ {0}) 0 (by simp) n
  have hC_nonneg : 0 ≤ C := by
    exact Real.sqrt_nonneg _
  have hs_L2 : ∀ n, MemScalarL2 U (s n) := by
    intro n
    simpa [MemScalarL2, μ, s] using
      (MeasureTheory.SimpleFunc.memLp_of_isFiniteMeasure
        (MeasureTheory.SimpleFunc.approxOn w hw_meas (Set.range w ∪ {0}) 0 (by simp) n)
        (2 : ℝ≥0∞) (volumeMeasureOn U))
  have hs_meas :
      ∀ n,
        @Measurable {a : CoeffField d // QuantitativeEllipticSlice U k a}
          ℝ (QuantitativeEllipticSlice.localMeasurableSpace U k) (borel ℝ)
          (fun a =>
            ∫ x in U,
              s n x * toFullBlockMat (blockCoeffField a.1 x) α β
                ∂MeasureTheory.volume) := by
    intro n
    exact
      QuantitativeEllipticSlice.measurable_l2WeightedFullBlockCoeffEntryIntegral
        hToL2 (hs_L2 n) α β
  have hs_tendsto :
      Filter.Tendsto
        (fun n : ℕ =>
          fun a : {a : CoeffField d // QuantitativeEllipticSlice U k a} =>
            ∫ x in U,
              s n x * toFullBlockMat (blockCoeffField a.1 x) α β
                ∂MeasureTheory.volume)
        atTop
        (𝓝
          fun a : {a : CoeffField d // QuantitativeEllipticSlice U k a} =>
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
      have hmem : ∀ᵐ x ∂ μ, x ∈ U := by
        simpa [μ] using
          (MeasureTheory.ae_restrict_iff'
              (measurableSet_of_isEllipticFieldOn a.2)).2
            (Filter.Eventually.of_forall fun x hx => hx)
      filter_upwards [hmem] with x hx
      simpa [μ, C, Real.norm_eq_abs] using
        abs_toFullBlockMat_blockCoeffField_entry_le_of_isEllipticFieldOn a.2 hx α β
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
  let : MeasurableSpace {a : CoeffField d // QuantitativeEllipticSlice U k a} :=
    QuantitativeEllipticSlice.localMeasurableSpace U k
  exact measurable_of_tendsto_metrizable hs_meas hs_tendsto

/-- `L¹` deterministic weights are enough for slice-level full-block entry
measurability.  This wrapper removes the need for callers to choose a
measurable representative of an integrable weight. -/
theorem QuantitativeEllipticSlice.measurable_integrableWeightedFullBlockCoeffEntryIntegral
    {d : ℕ} {U : Set (Vec d)} {k : ℕ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hToL2 :
      @Measurable {a : CoeffField d // QuantitativeEllipticSlice U k a}
        (MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U))
        (QuantitativeEllipticSlice.localMeasurableSpace U k) (borel _)
        QuantitativeEllipticSlice.toHilbertMatrixL2)
    {w : Vec d → ℝ}
    (hw : MeasureTheory.Integrable w (volumeMeasureOn U)) (α β : BlockCoord d) :
    @Measurable {a : CoeffField d // QuantitativeEllipticSlice U k a}
      ℝ (QuantitativeEllipticSlice.localMeasurableSpace U k) (borel ℝ)
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
      @Measurable {a : CoeffField d // QuantitativeEllipticSlice U k a}
        ℝ (QuantitativeEllipticSlice.localMeasurableSpace U k) (borel ℝ)
        (fun a =>
          ∫ x in U,
            w' x * toFullBlockMat (blockCoeffField a.1 x) α β
              ∂MeasureTheory.volume) :=
    QuantitativeEllipticSlice.measurable_integrableWeightedFullBlockCoeffEntryIntegral_of_measurable
        hToL2 hw'_meas hw'_int α β
  rw [show
      (fun a : {a : CoeffField d // QuantitativeEllipticSlice U k a} =>
        ∫ x in U,
          w x * toFullBlockMat (blockCoeffField a.1 x) α β ∂MeasureTheory.volume) =
        fun a : {a : CoeffField d // QuantitativeEllipticSlice U k a} =>
          ∫ x in U,
            w' x * toFullBlockMat (blockCoeffField a.1 x) α β
              ∂MeasureTheory.volume by
        funext a
        apply MeasureTheory.integral_congr_ae
        filter_upwards [hw.aestronglyMeasurable.ae_eq_mk] with x hx
        rw [hx]]
  exact hmeas'

/-- Open finite-measure wrapper for the `L¹`-weighted full-block entry
measurability theorem. -/
theorem QuantitativeEllipticSlice.measurable_integrableWeightedFullBlockCoeffEntryIntegral_of_isOpen_volume_ne_top
    {d : ℕ} {U : Set (Vec d)} {k : ℕ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hUopen : IsOpen U) (hUfinite : MeasureTheory.volume U ≠ ⊤)
    {w : Vec d → ℝ}
    (hw : MeasureTheory.Integrable w (volumeMeasureOn U)) (α β : BlockCoord d) :
    @Measurable {a : CoeffField d // QuantitativeEllipticSlice U k a}
      ℝ (QuantitativeEllipticSlice.localMeasurableSpace U k) (borel ℝ)
      (fun a =>
        ∫ x in U,
          w x * toFullBlockMat (blockCoeffField a.1 x) α β ∂MeasureTheory.volume) := by
  exact
    QuantitativeEllipticSlice.measurable_integrableWeightedFullBlockCoeffEntryIntegral
      (measurable_toHilbertMatrixL2_of_isOpen_volume_ne_top hUopen hUfinite)
      hw α β

theorem QuantitativeEllipticSlice.blockEnergyDensity_integrableOn_of_memBlockL2
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {k : ℕ} {X : BlockState d} (hSlice : QuantitativeEllipticSlice U k a)
    (hX : MemBlockL2 U X.eval) :
    MeasureTheory.IntegrableOn (blockEnergyDensity a X) U :=
  blockEnergyDensity_integrableOn_of_memBlockL2_of_isEllipticFieldOn
    (U := U) (a := a) (lam := ((k + 1 : ℝ)⁻¹)) (Lam := (k + 1 : ℝ)) hX hSlice

noncomputable def blockEnergyEntryWeight {d : ℕ} (X : BlockState d)
    (α β : BlockCoord d) (x : Vec d) : ℝ :=
  (1 / 2 : ℝ) * (toFullBlockVec (X.eval x) α * toFullBlockVec (X.eval x) β)

noncomputable def blockPairingEntryWeight {d : ℕ} (X Y : BlockState d)
    (α β : BlockCoord d) (x : Vec d) : ℝ :=
  toFullBlockVec (X.eval x) α * toFullBlockVec (Y.eval x) β

theorem integrable_blockEnergyEntryWeight_of_memBlockL2 {d : ℕ} {U : Set (Vec d)}
    {X : BlockState d} (hX : MemBlockL2 U X.eval) (α β : BlockCoord d) :
    MeasureTheory.Integrable (blockEnergyEntryWeight X α β) (volumeMeasureOn U) := by
  have hcoord :
      MeasureTheory.Integrable
        (fun x => toFullBlockVec (X.eval x) α * toFullBlockVec (X.eval x) β)
      (volumeMeasureOn U) := by
    simpa [MeasureTheory.IntegrableOn, volumeMeasureOn] using
      integrableOn_fullBlockCoord_mul_of_memBlockL2 hX α β
  change MeasureTheory.Integrable
    (fun x => (1 / 2 : ℝ) *
      (toFullBlockVec (X.eval x) α * toFullBlockVec (X.eval x) β))
    (volumeMeasureOn U)
  exact hcoord.const_mul (1 / 2 : ℝ)

theorem integrable_blockPairingEntryWeight_of_memBlockL2 {d : ℕ} {U : Set (Vec d)}
    {X Y : BlockState d} (hX : MemBlockL2 U X.eval) (hY : MemBlockL2 U Y.eval)
    (α β : BlockCoord d) :
    MeasureTheory.Integrable (blockPairingEntryWeight X Y α β) (volumeMeasureOn U) := by
  simpa [blockPairingEntryWeight, MeasureTheory.IntegrableOn, volumeMeasureOn] using!
    (memScalarL2_fullBlockCoord_of_memBlockL2 hX α).integrable_mul
      (memScalarL2_fullBlockCoord_of_memBlockL2 hY β)

theorem QuantitativeEllipticSlice.integrableOn_weightedFullBlockCoeffEntry_of_memBlockL2
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    {k : ℕ} {X : BlockState d} (hSlice : QuantitativeEllipticSlice U k a)
    (hX : MemBlockL2 U X.eval) (α β : BlockCoord d) :
    MeasureTheory.IntegrableOn
      (fun x =>
        blockEnergyEntryWeight X α β x *
          toFullBlockMat (blockCoeffField a x) α β)
      U := by
  classical
  let coeff : Vec d → ℝ := fun x => toFullBlockMat (blockCoeffField a x) α β
  let aExt : Vec d → Fin d → Fin d → ℝ := fun x i j => if x ∈ U then a x i j else 0
  have haExt : Measurable aExt := by
    simpa [aExt] using hSlice.1
  have hblock :
      Measurable (fun x γ δ =>
        toFullBlockMat (blockMatrixOfCoeff (aExt x)) γ δ) :=
    measurable_toFullBlockMat_blockCoeffField haExt
  have hcoeffExt :
      Measurable (fun x => toFullBlockMat (blockMatrixOfCoeff (aExt x)) α β) :=
    measurable_pi_iff.1 (measurable_pi_iff.1 hblock α) β
  have hmem : ∀ᵐ x ∂ volumeMeasureOn U, x ∈ U := by
    exact
      (MeasureTheory.ae_restrict_iff' (measurableSet_of_isEllipticFieldOn hSlice)).2
        (Filter.Eventually.of_forall fun x hx => hx)
  have hcoeff_ae : AEMeasurable coeff (volumeMeasureOn U) := by
    refine (Measurable.aemeasurable hcoeffExt).congr ?_
    filter_upwards [hmem] with x hx
    simp [coeff, aExt, blockCoeffField, hx]
  have hbound :
      ∀ᵐ x ∂ volumeMeasureOn U,
        ‖coeff x‖ ≤ Real.sqrt (blockMatrixOfCoeffNormSqBound ((k + 1 : ℝ)⁻¹) (k + 1 : ℝ)) := by
    filter_upwards [hmem] with x hx
    simpa [coeff, Real.norm_eq_abs] using
      abs_toFullBlockMat_blockCoeffField_entry_le_of_isEllipticFieldOn hSlice hx α β
  have hweight := integrable_blockEnergyEntryWeight_of_memBlockL2 (U := U) hX α β
  have hprod :
      MeasureTheory.Integrable
        (fun x => blockEnergyEntryWeight X α β x * coeff x) (volumeMeasureOn U) :=
    hweight.mul_bdd hcoeff_ae.aestronglyMeasurable hbound
  simpa [MeasureTheory.IntegrableOn, volumeMeasureOn, coeff] using hprod

theorem blockEnergyDensity_eq_sum_entryWeights {d : ℕ}
    (a : CoeffField d) (X : BlockState d) (x : Vec d) :
    blockEnergyDensity a X x =
      ∑ α, ∑ β,
        blockEnergyEntryWeight X α β x * toFullBlockMat (blockCoeffField a x) α β := by
  rw [blockEnergyDensity_eq_sum_fullBlockMat_entries]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro α _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro β _
  simp [blockEnergyEntryWeight]
  ring_nf

theorem blockPairingIntegrand_eq_sum_entryWeights {d : ℕ}
    (a : CoeffField d) (X Y : BlockState d) (x : Vec d) :
    blockPairingIntegrand a X Y x =
      ∑ α, ∑ β,
        blockPairingEntryWeight X Y α β x * toFullBlockMat (blockCoeffField a x) α β := by
  rw [blockPairingIntegrand, blockVecDot_blockMatVecMul_eq_toLinearMap₂',
    Matrix.toLinearMap₂'_apply]
  simp [blockPairingEntryWeight, mul_assoc]

theorem blockEnergyAverage_eq_sum_weightedFullBlockCoeffEntryIntegrals {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) (X : BlockState d)
    (hInt :
      ∀ α β : BlockCoord d,
        MeasureTheory.IntegrableOn
          (fun x =>
            blockEnergyEntryWeight X α β x * toFullBlockMat (blockCoeffField a x) α β)
          U) :
    blockEnergyAverage U a X =
      (MeasureTheory.volume U).toReal⁻¹ *
        ∑ α, ∑ β,
          ∫ x in U,
            blockEnergyEntryWeight X α β x *
              toFullBlockMat (blockCoeffField a x) α β ∂MeasureTheory.volume := by
  unfold blockEnergyAverage volumeAverage
  rw [show
      blockEnergyDensity a X =
        fun x =>
          ∑ α, ∑ β,
            blockEnergyEntryWeight X α β x * toFullBlockMat (blockCoeffField a x) α β by
        funext x
        exact blockEnergyDensity_eq_sum_entryWeights a X x]
  rw [MeasureTheory.integral_finsetSum]
  · congr 1
    apply Finset.sum_congr rfl
    intro α _
    rw [MeasureTheory.integral_finsetSum]
    intro β _
    simpa [MeasureTheory.IntegrableOn] using hInt α β
  · intro α _
    exact MeasureTheory.integrable_finsetSum
      Finset.univ
      (fun β _ => by
        simpa [MeasureTheory.IntegrableOn] using hInt α β)

theorem blockPairingAverage_eq_sum_weightedFullBlockCoeffEntryIntegrals {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) (X Y : BlockState d)
    (hInt :
      ∀ α β : BlockCoord d,
        MeasureTheory.IntegrableOn
          (fun x =>
            blockPairingEntryWeight X Y α β x * toFullBlockMat (blockCoeffField a x) α β)
          U) :
    blockPairingAverage U a X Y =
      (MeasureTheory.volume U).toReal⁻¹ *
        ∑ α, ∑ β,
          ∫ x in U,
            blockPairingEntryWeight X Y α β x *
              toFullBlockMat (blockCoeffField a x) α β ∂MeasureTheory.volume := by
  unfold blockPairingAverage volumeAverage
  rw [show
      blockPairingIntegrand a X Y =
        fun x =>
          ∑ α, ∑ β,
            blockPairingEntryWeight X Y α β x * toFullBlockMat (blockCoeffField a x) α β by
        funext x
        exact blockPairingIntegrand_eq_sum_entryWeights a X Y x]
  rw [MeasureTheory.integral_finsetSum]
  · congr 1
    apply Finset.sum_congr rfl
    intro α _
    rw [MeasureTheory.integral_finsetSum]
    intro β _
    simpa [MeasureTheory.IntegrableOn] using hInt α β
  · intro α _
    exact MeasureTheory.integrable_finsetSum
      Finset.univ
      (fun β _ => by
        simpa [MeasureTheory.IntegrableOn] using hInt α β)

theorem measurable_blockEnergyAverage_of_measurable_weightedFullBlockCoeffEntryIntegrals
    {d : ℕ} {U : Set (Vec d)} (X : BlockState d)
    (hInt :
      ∀ a : CoeffField d, ∀ α β : BlockCoord d,
        MeasureTheory.IntegrableOn
          (fun x =>
            blockEnergyEntryWeight X α β x * toFullBlockMat (blockCoeffField a x) α β)
          U)
    (hMeas :
      ∀ α β : BlockCoord d,
        Measurable fun a : CoeffField d =>
          ∫ x in U,
            blockEnergyEntryWeight X α β x *
              toFullBlockMat (blockCoeffField a x) α β ∂MeasureTheory.volume) :
    Measurable fun a : CoeffField d => blockEnergyAverage U a X := by
  rw [show
      (fun a : CoeffField d => blockEnergyAverage U a X) =
        fun a : CoeffField d =>
          (MeasureTheory.volume U).toReal⁻¹ *
            ∑ α, ∑ β,
              ∫ x in U,
                blockEnergyEntryWeight X α β x *
                  toFullBlockMat (blockCoeffField a x) α β ∂MeasureTheory.volume by
        funext a
        exact blockEnergyAverage_eq_sum_weightedFullBlockCoeffEntryIntegrals U a X (hInt a)]
  exact measurable_const.mul
    (Finset.measurable_sum Finset.univ fun α _ =>
      Finset.measurable_sum Finset.univ fun β _ => hMeas α β)

theorem measurable_blockPairingAverage_of_measurable_weightedFullBlockCoeffEntryIntegrals
    {d : ℕ} {U : Set (Vec d)} (X Y : BlockState d)
    (hInt :
      ∀ a : CoeffField d, ∀ α β : BlockCoord d,
        MeasureTheory.IntegrableOn
          (fun x =>
            blockPairingEntryWeight X Y α β x * toFullBlockMat (blockCoeffField a x) α β)
          U)
    (hMeas :
      ∀ α β : BlockCoord d,
        Measurable fun a : CoeffField d =>
          ∫ x in U,
            blockPairingEntryWeight X Y α β x *
              toFullBlockMat (blockCoeffField a x) α β ∂MeasureTheory.volume) :
    Measurable fun a : CoeffField d => blockPairingAverage U a X Y := by
  rw [show
      (fun a : CoeffField d => blockPairingAverage U a X Y) =
        fun a : CoeffField d =>
          (MeasureTheory.volume U).toReal⁻¹ *
            ∑ α, ∑ β,
              ∫ x in U,
                blockPairingEntryWeight X Y α β x *
                  toFullBlockMat (blockCoeffField a x) α β ∂MeasureTheory.volume by
        funext a
        exact blockPairingAverage_eq_sum_weightedFullBlockCoeffEntryIntegrals U a X Y
          (hInt a)]
  exact measurable_const.mul
    (Finset.measurable_sum Finset.univ fun α _ =>
      Finset.measurable_sum Finset.univ fun β _ => hMeas α β)

theorem measurable_blockEnergyAverage_comp_of_measurable_weightedFullBlockCoeffEntryIntegrals
    {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} {U : Set (Vec d)} (A : Ω → CoeffField d) (X : BlockState d)
    (hInt :
      ∀ ω : Ω, ∀ α β : BlockCoord d,
        MeasureTheory.IntegrableOn
          (fun x =>
            blockEnergyEntryWeight X α β x * toFullBlockMat (blockCoeffField (A ω) x) α β)
          U)
    (hMeas :
      ∀ α β : BlockCoord d,
        Measurable fun ω : Ω =>
          ∫ x in U,
            blockEnergyEntryWeight X α β x *
              toFullBlockMat (blockCoeffField (A ω) x) α β ∂MeasureTheory.volume) :
    Measurable fun ω : Ω => blockEnergyAverage U (A ω) X := by
  rw [show
      (fun ω : Ω => blockEnergyAverage U (A ω) X) =
        fun ω : Ω =>
          (MeasureTheory.volume U).toReal⁻¹ *
            ∑ α, ∑ β,
              ∫ x in U,
                blockEnergyEntryWeight X α β x *
                  toFullBlockMat (blockCoeffField (A ω) x) α β ∂MeasureTheory.volume by
        funext ω
        exact blockEnergyAverage_eq_sum_weightedFullBlockCoeffEntryIntegrals U (A ω) X
          (hInt ω)]
  exact measurable_const.mul
    (Finset.measurable_sum Finset.univ fun α _ =>
      Finset.measurable_sum Finset.univ fun β _ => hMeas α β)

theorem measurable_blockPairingAverage_comp_of_measurable_weightedFullBlockCoeffEntryIntegrals
    {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} {U : Set (Vec d)} (A : Ω → CoeffField d) (X Y : BlockState d)
    (hInt :
      ∀ ω : Ω, ∀ α β : BlockCoord d,
        MeasureTheory.IntegrableOn
          (fun x =>
            blockPairingEntryWeight X Y α β x *
              toFullBlockMat (blockCoeffField (A ω) x) α β)
          U)
    (hMeas :
      ∀ α β : BlockCoord d,
        Measurable fun ω : Ω =>
          ∫ x in U,
            blockPairingEntryWeight X Y α β x *
              toFullBlockMat (blockCoeffField (A ω) x) α β ∂MeasureTheory.volume) :
    Measurable fun ω : Ω => blockPairingAverage U (A ω) X Y := by
  rw [show
      (fun ω : Ω => blockPairingAverage U (A ω) X Y) =
        fun ω : Ω =>
          (MeasureTheory.volume U).toReal⁻¹ *
            ∑ α, ∑ β,
              ∫ x in U,
                blockPairingEntryWeight X Y α β x *
                  toFullBlockMat (blockCoeffField (A ω) x) α β ∂MeasureTheory.volume by
        funext ω
        exact blockPairingAverage_eq_sum_weightedFullBlockCoeffEntryIntegrals U (A ω) X Y
          (hInt ω)]
  exact measurable_const.mul
    (Finset.measurable_sum Finset.univ fun α _ =>
      Finset.measurable_sum Finset.univ fun β _ => hMeas α β)

theorem measurable_blockEnergyAverage_quantitativeSlice_of_measurable_weightedFullBlockCoeffEntryIntegrals
    {d : ℕ} {U : Set (Vec d)} {k : ℕ} (X : BlockState d)
    (hX : MemBlockL2 U X.eval)
    (hMeas :
      ∀ α β : BlockCoord d,
        Measurable fun a : {a : CoeffField d // QuantitativeEllipticSlice U k a} =>
          ∫ x in U,
            blockEnergyEntryWeight X α β x *
              toFullBlockMat (blockCoeffField a.1 x) α β ∂MeasureTheory.volume) :
    Measurable fun a : {a : CoeffField d // QuantitativeEllipticSlice U k a} =>
      blockEnergyAverage U a.1 X := by
  exact measurable_blockEnergyAverage_comp_of_measurable_weightedFullBlockCoeffEntryIntegrals
    (A := fun a : {a : CoeffField d // QuantitativeEllipticSlice U k a} => a.1)
    (X := X)
    (fun a α β =>
      a.2.integrableOn_weightedFullBlockCoeffEntry_of_memBlockL2 hX α β)
    hMeas

/-- Fixed-competitor energy averages are measurable on a quantitative elliptic
slice once the slice has the note-facing measurable `L²` realization. -/
theorem measurable_blockEnergyAverage_quantitativeSlice
    {d : ℕ} {U : Set (Vec d)} {k : ℕ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hToL2 :
      @Measurable {a : CoeffField d // QuantitativeEllipticSlice U k a}
        (MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U))
        (QuantitativeEllipticSlice.localMeasurableSpace U k) (borel _)
        QuantitativeEllipticSlice.toHilbertMatrixL2)
    (X : BlockState d) (hX : MemBlockL2 U X.eval) :
    @Measurable {a : CoeffField d // QuantitativeEllipticSlice U k a}
      ℝ (QuantitativeEllipticSlice.localMeasurableSpace U k) (borel ℝ)
      (fun a => blockEnergyAverage U a.1 X) := by
  let : MeasurableSpace {a : CoeffField d // QuantitativeEllipticSlice U k a} :=
    QuantitativeEllipticSlice.localMeasurableSpace U k
  exact measurable_blockEnergyAverage_comp_of_measurable_weightedFullBlockCoeffEntryIntegrals
    (A := fun a : {a : CoeffField d // QuantitativeEllipticSlice U k a} => a.1)
    (X := X)
    (fun a α β =>
      a.2.integrableOn_weightedFullBlockCoeffEntry_of_memBlockL2 hX α β)
    (fun α β =>
      QuantitativeEllipticSlice.measurable_integrableWeightedFullBlockCoeffEntryIntegral
        hToL2 (integrable_blockEnergyEntryWeight_of_memBlockL2 hX α β) α β)

end Homogenization
