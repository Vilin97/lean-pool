/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MuQuadratic
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MuOperator.CoeffOperator
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MuRecovery.CorrectionSpaceEnergy
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Internal.CoarseObservableMeasurability.Mu
import LeanPool.CoarseGraining.Homogenization.Probability.LocalEllipticitySlices
import LeanPool.CoarseGraining.Homogenization.Probability.LocalObservable
import LeanPool.CoarseGraining.Homogenization.Probability.RandomFieldMeasurability
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Function.UniformIntegrable

/-! # Measurability -/

namespace Homogenization

open scoped Manifold
open scoped ENNReal
open scoped Topology
open Filter

/-!
# Fixed-competitor energy measurability, first atoms

## Audit tag (Ch4 rebuild contract `CH04_REBUILD_SURFACE_2026-05-16.md`)

**Internal claim:** the `PointwiseLocalSigma`-measurable scalar atoms (single-vector
dot products, single-coordinate matrix-vector products, etc.) used as the
local-σ-measurable building blocks for fixed-competitor energy observables.
First layer of the internal `HasMeasurableMuFamily` cleanup.

**Consumed by (within `Internal/FixedCompetitorEnergyMeasurability/`):**
`LipschitzBounds.lean`, which lifts these atoms to Borel-measurable
fixed-coefficient maps; ultimately reaches the public
`Theorems/Mu.lean :: aemeasurable_Mu_cubeSet` via the chain
`Measurability → LipschitzBounds → Integrals → BlockEnergyAverage →
MuObservable → AEESliceAssembly/MuFamily`.

If the single-claim summary above grows into three or more distinct
claims, split or refactor per the rebuild contract.
-/

theorem vecDot_single_matVecMul_single {d : ℕ} (A : Mat d) (i j : Fin d) :
    vecDot (Pi.single i 1 : Vec d) (matVecMul A (Pi.single j 1)) = A i j := by
  rw [vecDot, Finset.sum_eq_single i]
  · rw [matVecMul, Finset.sum_eq_single j]
    · simp
    · intro k _ hkj
      simp [Pi.single_eq_of_ne hkj]
    · simp
  · intro k _ hki
    simp [Pi.single_eq_of_ne hki]
  · simp

theorem localTestObservable_single_single_eq_integral_entry {d : ℕ}
    (i j : Fin d) (φ : Vec d → ℝ) :
    localTestObservable (Pi.single j 1 : Vec d) (Pi.single i 1 : Vec d) φ =
      fun a : CoeffField d => ∫ x, a x i j * φ x ∂MeasureTheory.volume := by
  funext a
  unfold localTestObservable
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    simp [vecDot_single_matVecMul_single]

theorem measurable_entryTestObservable_localSigma {d : ℕ} {U : Set (Vec d)}
    (i j : Fin d) {φ : Vec d → ℝ} (hφ_cont : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ) (hφ_support : tsupport φ ⊆ U) :
    @Measurable (CoeffField d) ℝ (PointwiseLocalSigma U) (borel ℝ)
      (fun a : CoeffField d => ∫ x, a x i j * φ x ∂MeasureTheory.volume) := by
  rw [← localTestObservable_single_single_eq_integral_entry i j φ]
  exact measurable_localTestObservable_localSigma
    (U := U) (Pi.single j 1 : Vec d) (Pi.single i 1 : Vec d)
    hφ_cont hφ_compact hφ_support

theorem setIntegral_entry_mul_eq_integral_of_tsupport_subset {d : ℕ}
    {U : Set (Vec d)} (a : CoeffField d) (i j : Fin d) {φ : Vec d → ℝ}
    (hφ_support : tsupport φ ⊆ U) :
    ∫ x in U, a x i j * φ x ∂MeasureTheory.volume =
      ∫ x, a x i j * φ x ∂MeasureTheory.volume := by
  apply MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have hx_notin : x ∉ tsupport φ := fun hx' => hx (hφ_support hx')
  simp [image_eq_zero_of_notMem_tsupport hx_notin]

theorem measurable_entryTestObservable_setIntegral_localSigma {d : ℕ} {U : Set (Vec d)}
    (i j : Fin d) {φ : Vec d → ℝ} (hφ_cont : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ) (hφ_support : tsupport φ ⊆ U) :
    @Measurable (CoeffField d) ℝ (PointwiseLocalSigma U) (borel ℝ)
      (fun a : CoeffField d => ∫ x in U, a x i j * φ x ∂MeasureTheory.volume) := by
  rw [show
      (fun a : CoeffField d => ∫ x in U, a x i j * φ x ∂MeasureTheory.volume) =
        fun a : CoeffField d => ∫ x, a x i j * φ x ∂MeasureTheory.volume by
          funext a
          exact setIntegral_entry_mul_eq_integral_of_tsupport_subset a i j hφ_support]
  exact measurable_entryTestObservable_localSigma
    (U := U) i j hφ_cont hφ_compact hφ_support

theorem measurable_inner_toScalarL2_matrixL2Entry_toMatrixL2_localMeasurableSpace
    {d : ℕ} {U : Set (Vec d)} {k : ℕ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (i j : Fin d) {φ : Vec d → ℝ} (hφL2 : MemScalarL2 U φ)
    (hφ_cont : ContDiff ℝ (⊤ : ℕ∞) φ) (hφ_compact : HasCompactSupport φ)
    (hφ_support : tsupport φ ⊆ U) :
    @Measurable {a : CoeffField d // QuantitativeEllipticSlice U k a}
      ℝ (QuantitativeEllipticSlice.localMeasurableSpace U k) (borel ℝ)
      (fun a =>
        inner ℝ (toScalarL2 hφL2)
          (QuantitativeEllipticSlice.matrixL2Entry (U := U) i j
            (QuantitativeEllipticSlice.toMatrixL2 a))) := by
  rw [show
      (fun a : {a : CoeffField d // QuantitativeEllipticSlice U k a} =>
        inner ℝ (toScalarL2 hφL2)
          (QuantitativeEllipticSlice.matrixL2Entry (U := U) i j
            (QuantitativeEllipticSlice.toMatrixL2 a))) =
        fun a : {a : CoeffField d // QuantitativeEllipticSlice U k a} =>
          ∫ x in U, a.1 x i j * φ x ∂MeasureTheory.volume by
        funext a
        calc
          inner ℝ (toScalarL2 hφL2)
              (QuantitativeEllipticSlice.matrixL2Entry (U := U) i j
                (QuantitativeEllipticSlice.toMatrixL2 a))
              = ∫ x in U, φ x * a.1 x i j ∂MeasureTheory.volume :=
            QuantitativeEllipticSlice.inner_toScalarL2_matrixL2Entry_toMatrixL2_eq_setIntegral
              hφL2 i j a
          _ = ∫ x in U, a.1 x i j * φ x ∂MeasureTheory.volume := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with x
            ring]
  exact (measurable_entryTestObservable_setIntegral_localSigma
    (U := U) i j hφ_cont hφ_compact hφ_support).comp
      QuantitativeEllipticSlice.measurable_val_localMeasurableSpace

theorem measurable_inner_toScalarL2_hilbertMatrixL2Entry_toHilbertMatrixL2_localMeasurableSpace
    {d : ℕ} {U : Set (Vec d)} {k : ℕ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (i j : Fin d) {φ : Vec d → ℝ} (hφL2 : MemScalarL2 U φ)
    (hφ_cont : ContDiff ℝ (⊤ : ℕ∞) φ) (hφ_compact : HasCompactSupport φ)
    (hφ_support : tsupport φ ⊆ U) :
    @Measurable {a : CoeffField d // QuantitativeEllipticSlice U k a}
      ℝ (QuantitativeEllipticSlice.localMeasurableSpace U k) (borel ℝ)
      (fun a =>
        inner ℝ (toScalarL2 hφL2)
          (QuantitativeEllipticSlice.hilbertMatrixL2Entry (U := U) i j
            (QuantitativeEllipticSlice.toHilbertMatrixL2 a))) := by
  rw [show
      (fun a : {a : CoeffField d // QuantitativeEllipticSlice U k a} =>
        inner ℝ (toScalarL2 hφL2)
          (QuantitativeEllipticSlice.hilbertMatrixL2Entry (U := U) i j
            (QuantitativeEllipticSlice.toHilbertMatrixL2 a))) =
        fun a : {a : CoeffField d // QuantitativeEllipticSlice U k a} =>
          ∫ x in U, a.1 x i j * φ x ∂MeasureTheory.volume by
        funext a
        calc
          inner ℝ (toScalarL2 hφL2)
              (QuantitativeEllipticSlice.hilbertMatrixL2Entry (U := U) i j
                (QuantitativeEllipticSlice.toHilbertMatrixL2 a))
              = ∫ x in U, φ x * a.1 x i j ∂MeasureTheory.volume :=
            QuantitativeEllipticSlice.inner_toScalarL2_hilbertMatrixL2Entry_toHilbertMatrixL2_eq_setIntegral
              hφL2 i j a
          _ = ∫ x in U, a.1 x i j * φ x ∂MeasureTheory.volume := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with x
            ring]
  exact (measurable_entryTestObservable_setIntegral_localSigma
    (U := U) i j hφ_cont hφ_compact hφ_support).comp
      QuantitativeEllipticSlice.measurable_val_localMeasurableSpace

theorem measurable_inner_hilbertMatrixSmoothProbe_toHilbertMatrixL2_localMeasurableSpace
    {d : ℕ} {U : Set (Vec d)} {k : ℕ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] {g : Vec d → HilbertMat d}
    (hgL2 : MeasureTheory.MemLp g 2 (volumeMeasureOn U))
    (hg_cont : ContDiff ℝ (⊤ : ℕ∞) g) (hg_compact : HasCompactSupport g)
    (hg_support : tsupport g ⊆ U) :
    @Measurable {a : CoeffField d // QuantitativeEllipticSlice U k a}
      ℝ (QuantitativeEllipticSlice.localMeasurableSpace U k) (borel ℝ)
      (fun a => inner ℝ (hgL2.toLp g) (QuantitativeEllipticSlice.toHilbertMatrixL2 a)) := by
  rw [show
      (fun a : {a : CoeffField d // QuantitativeEllipticSlice U k a} =>
        inner ℝ (hgL2.toLp g) (QuantitativeEllipticSlice.toHilbertMatrixL2 a)) =
        fun a : {a : CoeffField d // QuantitativeEllipticSlice U k a} =>
          ∑ i : Fin d, ∑ j : Fin d,
            inner ℝ (toScalarL2
                (QuantitativeEllipticSlice.memScalarL2_hilbertMatrix_entry_of_memLp
                  (U := U) hgL2 i j))
              (QuantitativeEllipticSlice.hilbertMatrixL2Entry (U := U) i j
                (QuantitativeEllipticSlice.toHilbertMatrixL2 a)) by
      funext a
      exact QuantitativeEllipticSlice.inner_hilbertMatrixL2_eq_sum_entry_inner hgL2
        (QuantitativeEllipticSlice.toHilbertMatrixL2 a)]
  refine Finset.measurable_sum _ ?_
  intro i _
  refine Finset.measurable_sum _ ?_
  intro j _
  let gij : Vec d → ℝ := fun x => HilbertMat.entryL i j (g x)
  have hgijL2 : MemScalarL2 U gij := by
    simpa [gij] using
      QuantitativeEllipticSlice.memScalarL2_hilbertMatrix_entry_of_memLp (U := U) hgL2 i j
  have hgij_cont : ContDiff ℝ (⊤ : ℕ∞) gij := by
    simpa [gij, Function.comp_def] using
      (ContDiff.continuousLinearMap_comp (HilbertMat.entryL i j) hg_cont)
  have hgij_compact : HasCompactSupport gij := by
    simpa [gij, Function.comp_def] using
      hg_compact.comp_left (by simp : HilbertMat.entryL i j (0 : HilbertMat d) = 0)
  have hgij_support : tsupport gij ⊆ U := by
    have hsubset : tsupport gij ⊆ tsupport g := by
      simpa [gij, Function.comp_def] using
        (tsupport_comp_subset
          (by simp : HilbertMat.entryL i j (0 : HilbertMat d) = 0) g)
    exact hsubset.trans hg_support
  simpa [gij, hgijL2] using
    measurable_inner_toScalarL2_hilbertMatrixL2Entry_toHilbertMatrixL2_localMeasurableSpace
      (U := U) i j hgijL2 hgij_cont hgij_compact hgij_support

theorem measurable_toHilbertMatrixL2_of_dense_smoothProbeSequence
    {d : ℕ} {U : Set (Vec d)} {k : ℕ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (u : ℕ → MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U))
    (hu : DenseRange u)
    (hSmooth : ∀ n : ℕ, ∃ g : Vec d → HilbertMat d,
      ∃ hgL2 : MeasureTheory.MemLp g 2 (volumeMeasureOn U),
        u n = hgL2.toLp g ∧ ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g ∧
          tsupport g ⊆ U) :
    @Measurable {a : CoeffField d // QuantitativeEllipticSlice U k a}
      (MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U))
      (QuantitativeEllipticSlice.localMeasurableSpace U k) (borel _)
      QuantitativeEllipticSlice.toHilbertMatrixL2 := by
  refine QuantitativeEllipticSlice.measurable_toHilbertMatrixL2_of_dense_inner u hu ?_
  intro n
  rcases hSmooth n with ⟨g, hgL2, hEq, hg_cont, hg_compact, hg_support⟩
  rw [hEq]
  exact measurable_inner_hilbertMatrixSmoothProbe_toHilbertMatrixL2_localMeasurableSpace
    (U := U) hgL2 hg_cont hg_compact hg_support

/-- Mathlib's global smooth compact-support density, converted to the exact `toLp`
representative shape used by the probability bookkeeping.

The later local argument still has to push these probes inside `U`; this lemma isolates the
ambient density input from that boundary-cutoff step. -/
theorem dense_smoothCompactHilbertMatrixL2
    {d : ℕ} {U : Set (Vec d)} :
    Dense {f : MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U) |
      ∃ g : Vec d → HilbertMat d,
      ∃ hgL2 : MeasureTheory.MemLp g 2 (volumeMeasureOn U),
        f = hgL2.toLp g ∧ ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g} := by
  have : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
  have hDenseAE :=
    MeasureTheory.Lp.dense_hasCompactSupport_contDiff
      (E := Vec d) (F := HilbertMat d) (μ := volumeMeasureOn U)
      (p := (2 : ENNReal)) ENNReal.ofNat_ne_top
  refine hDenseAE.mono ?_
  intro f hf
  rcases hf with ⟨g, hfg, hg_compact, hg_cont⟩
  let hgL2 : MeasureTheory.MemLp g 2 (volumeMeasureOn U) :=
    (MeasureTheory.Lp.memLp f).ae_eq hfg
  refine ⟨g, hgL2, ?_, by simpa using hg_cont, hg_compact⟩
  calc
    f = (MeasureTheory.Lp.memLp f).toLp (fun x => f x) :=
      (MeasureTheory.Lp.toLp_coeFn f (MeasureTheory.Lp.memLp f)).symm
    _ = hgL2.toLp g :=
      MeasureTheory.MemLp.toLp_congr (MeasureTheory.Lp.memLp f) hgL2 hfg

private theorem hilbertMat_norm_sub_smul_le_norm {d : ℕ}
    (c : ℝ) (h0 : 0 ≤ c) (h1 : c ≤ 1) (v : HilbertMat d) :
    ‖v - c • v‖ ≤ ‖v‖ := by
  calc
    ‖v - c • v‖ = ‖(1 - c) • v‖ := by
      congr 1
      simp [sub_smul]
    _ = ‖(1 - c : ℝ)‖ * ‖v‖ := norm_smul (1 - c) v
    _ ≤ 1 * ‖v‖ := by
      gcongr
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      linarith
    _ = ‖v‖ := by simp

/-- Localize a smooth `L²` matrix field to an open finite-measure set without
changing it much in `L²`.  This is the analytic cutoff step that turns
Mathlib's ambient compactly supported smooth density into the note-facing
`tsupport ⊆ U` probe class. -/
theorem exists_contDiff_hilbertMatrixL2_tsupport_subset_eLpNorm_sub_le
    {d : ℕ} {U : Set (Vec d)} (hUopen : IsOpen U)
    (hUfinite : MeasureTheory.volume U ≠ ⊤)
    {g : Vec d → HilbertMat d} (hgL2 : MeasureTheory.MemLp g 2 (volumeMeasureOn U))
    (hg_cont : ContDiff ℝ (⊤ : ℕ∞) g) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : Vec d → HilbertMat d,
      ∃ _hφL2 : MeasureTheory.MemLp φ 2 (volumeMeasureOn U),
        MeasureTheory.eLpNorm (g - φ) 2 (volumeMeasureOn U) ≤ ENNReal.ofReal ε ∧
        ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U := by
  obtain ⟨δ, hδpos, hδ⟩ :=
    hgL2.eLpNorm_indicator_le (p := (2 : ENNReal)) (by norm_num)
      ENNReal.ofNat_ne_top hε
  obtain ⟨K, hKU, hK_compact, hK_closed, hμK⟩ :=
    hUopen.measurableSet.exists_isCompact_isClosed_sdiff_lt (μ := MeasureTheory.volume)
      hUfinite ((ENNReal.ofReal_pos.mpr hδpos).ne')
  rcases exists_compact_closed_between hK_compact hUopen hKU with
    ⟨L, hL_compact, hL_closed, hKL, hLU⟩
  rcases exists_contMDiffMap_one_nhds_of_subset_interior (n := ⊤)
      (I := 𝓘(ℝ, Vec d)) hK_closed hKL with
    ⟨η, hη_one, hη_zero, hη_range⟩
  let φ : Vec d → HilbertMat d := fun x => η x • g x
  have hη_cont : ContDiff ℝ (⊤ : ℕ∞) η := η.contMDiff.contDiff
  have hφ_cont : ContDiff ℝ (⊤ : ℕ∞) φ := by
    simpa only [φ] using! hη_cont.smul hg_cont
  have hφ_support : Function.support φ ⊆ L := by
    intro x hx
    by_contra hxL
    have hz : η x = 0 := hη_zero x hxL
    exact hx (by simp [φ, hz])
  have hφ_compact : HasCompactSupport φ :=
    HasCompactSupport.of_support_subset_isCompact hL_compact hφ_support
  have hφ_tsupport : tsupport φ ⊆ U := by
    have hφ_tsupport_L : tsupport φ ⊆ L := by
      simpa [tsupport] using closure_minimal hφ_support hL_closed
    exact hφ_tsupport_L.trans hLU
  have hφL2 : MeasureTheory.MemLp φ 2 (volumeMeasureOn U) :=
    hφ_cont.continuous.memLp_of_hasCompactSupport hφ_compact
  refine ⟨φ, hφL2, ?_, hφ_cont, hφ_compact, hφ_tsupport⟩
  have hμsmall : volumeMeasureOn U (U \ K) ≤ ENNReal.ofReal δ := by
    unfold volumeMeasureOn
    rw [MeasureTheory.Measure.restrict_apply (hUopen.measurableSet.diff hK_closed.measurableSet)]
    simpa [Set.inter_eq_self_of_subset_left (Set.sdiff_subset : U \ K ⊆ U)] using hμK.le
  have hindicator := hδ (U \ K) (hUopen.measurableSet.diff hK_closed.measurableSet) hμsmall
  calc
    MeasureTheory.eLpNorm (g - φ) 2 (volumeMeasureOn U)
        ≤ MeasureTheory.eLpNorm ((U \ K).indicator g) 2 (volumeMeasureOn U) := by
          refine MeasureTheory.eLpNorm_mono_ae ?_
          have hmem : ∀ᵐ x ∂ volumeMeasureOn U, x ∈ U := by
            simpa [volumeMeasureOn] using MeasureTheory.ae_restrict_mem hUopen.measurableSet
          filter_upwards [hmem] with x hxU
          by_cases hxK : x ∈ K
          · have hφx : φ x = g x := by
              have hηx : η x = 1 := hη_one.self_of_nhdsSet x hxK
              simp [φ, hηx]
            simp [hφx, hxK]
          · have hxDiff : x ∈ U \ K := ⟨hxU, hxK⟩
            rw [Set.indicator_of_mem hxDiff]
            have hη01 := hη_range x
            exact hilbertMat_norm_sub_smul_le_norm (d := d) (η x) hη01.1 hη01.2 (g x)
    _ ≤ ENNReal.ofReal ε := hindicator

/-- Smooth compactly supported `HilbertMat` probes with support contained in an
open finite-measure set are dense in `L²(U; HilbertMat d)`. -/
theorem dense_smoothCompactSupportHilbertMatrixL2_tsupport_subset
    {d : ℕ} {U : Set (Vec d)} (hUopen : IsOpen U)
    (hUfinite : MeasureTheory.volume U ≠ ⊤) :
    Dense {f : MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U) |
      ∃ g : Vec d → HilbertMat d,
      ∃ hgL2 : MeasureTheory.MemLp g 2 (volumeMeasureOn U),
        f = hgL2.toLp g ∧ ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g ∧
          tsupport g ⊆ U} := by
  have : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
  intro f
  refine (mem_closure_iff_nhds_basis Metric.nhds_basis_closedBall).2 fun ε hε => ?_
  have hε2 : 0 < ε / 2 := by positivity
  obtain ⟨g, hg_compact, hg_cont, hg_err⟩ :=
    MeasureTheory.MemLp.exist_eLpNorm_sub_le
      (μ := volumeMeasureOn U) (p := (2 : ENNReal))
      ENNReal.ofNat_ne_top (by norm_num : (1 : ENNReal) ≤ 2)
      (MeasureTheory.Lp.memLp f) hε2
  have hgL2 : MeasureTheory.MemLp g 2 (volumeMeasureOn U) :=
    hg_cont.continuous.memLp_of_hasCompactSupport hg_compact
  obtain ⟨φ, hφL2, hφ_err, hφ_cont, hφ_compact, hφ_support⟩ :=
    exists_contDiff_hilbertMatrixL2_tsupport_subset_eLpNorm_sub_le
      hUopen hUfinite hgL2 hg_cont hε2
  refine ⟨hφL2.toLp φ, ?_, ?_⟩
  · exact ⟨φ, hφL2, rfl, hφ_cont, hφ_compact, hφ_support⟩
  · have hnorm :
        MeasureTheory.eLpNorm (fun x => f x - hφL2.toLp φ x) 2 (volumeMeasureOn U) ≤
          ENNReal.ofReal ε := by
      calc
        MeasureTheory.eLpNorm (fun x => f x - hφL2.toLp φ x) 2 (volumeMeasureOn U)
            = MeasureTheory.eLpNorm ((fun x => f x) - φ) 2 (volumeMeasureOn U) := by
              apply MeasureTheory.eLpNorm_congr_ae
              filter_upwards [hφL2.coeFn_toLp] with x hx
              simp [Pi.sub_apply, hx]
        _ = MeasureTheory.eLpNorm (((fun x => f x) - g) + (g - φ)) 2
              (volumeMeasureOn U) := by
              congr 1
              funext x
              simp [Pi.sub_apply]
        _ ≤ MeasureTheory.eLpNorm ((fun x => f x) - g) 2 (volumeMeasureOn U) +
              MeasureTheory.eLpNorm (g - φ) 2 (volumeMeasureOn U) := by
              refine MeasureTheory.eLpNorm_add_le ?_ ?_ (by norm_num : (1 : ENNReal) ≤ 2)
              · exact (MeasureTheory.Lp.aestronglyMeasurable f).sub hgL2.aestronglyMeasurable
              · exact hgL2.aestronglyMeasurable.sub hφL2.aestronglyMeasurable
        _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := add_le_add hg_err hφ_err
        _ = ENNReal.ofReal ε := by
              rw [← ENNReal.ofReal_add hε2.le hε2.le, add_halves]
    rw [Metric.mem_closedBall, dist_comm, MeasureTheory.Lp.dist_def]
    exact ENNReal.toReal_le_of_le_ofReal
      (a := MeasureTheory.eLpNorm (fun x => f x - hφL2.toLp φ x) 2 (volumeMeasureOn U))
      (b := ε) hε.le hnorm

theorem exists_dense_smoothProbeSequence_of_dense_smoothProbeSet
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hDense : Dense {f : MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U) |
      ∃ g : Vec d → HilbertMat d,
      ∃ hgL2 : MeasureTheory.MemLp g 2 (volumeMeasureOn U),
        f = hgL2.toLp g ∧ ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g ∧
          tsupport g ⊆ U}) :
    ∃ u : ℕ → MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U),
      DenseRange u ∧
        ∀ n : ℕ, ∃ g : Vec d → HilbertMat d,
          ∃ hgL2 : MeasureTheory.MemLp g 2 (volumeMeasureOn U),
            u n = hgL2.toLp g ∧ ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g ∧
              tsupport g ⊆ U := by
  have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨ENNReal.ofNat_ne_top⟩
  let H := MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U)
  let S : Set H := {f : H |
      ∃ g : Vec d → HilbertMat d,
      ∃ hgL2 : MeasureTheory.MemLp g 2 (volumeMeasureOn U),
        f = hgL2.toLp g ∧ ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g ∧
          tsupport g ⊆ U}
  have hDenseS : Dense S := by
    simpa [S, H] using hDense
  have hS_nonempty : S.Nonempty := by
    rcases hDenseS.inter_open_nonempty Set.univ isOpen_univ
        (Set.univ_nonempty : (Set.univ : Set H).Nonempty) with
      ⟨x, _, hxS⟩
    exact ⟨x, hxS⟩
  have : Nonempty S := hS_nonempty.to_subtype
  rcases TopologicalSpace.exists_dense_seq S with ⟨v, hv⟩
  refine ⟨fun n => (v n : H), ?_, ?_⟩
  · exact hDenseS.denseRange_val.comp hv continuous_subtype_val
  · intro n
    simpa [S, H] using (v n).2

theorem measurable_toHilbertMatrixL2_of_dense_smoothProbeSet
    {d : ℕ} {U : Set (Vec d)} {k : ℕ} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hDense : Dense {f : MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U) |
      ∃ g : Vec d → HilbertMat d,
      ∃ hgL2 : MeasureTheory.MemLp g 2 (volumeMeasureOn U),
        f = hgL2.toLp g ∧ ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g ∧
          tsupport g ⊆ U}) :
    @Measurable {a : CoeffField d // QuantitativeEllipticSlice U k a}
      (MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U))
      (QuantitativeEllipticSlice.localMeasurableSpace U k) (borel _)
      QuantitativeEllipticSlice.toHilbertMatrixL2 := by
  rcases exists_dense_smoothProbeSequence_of_dense_smoothProbeSet (U := U) hDense with
    ⟨u, hu, hSmooth⟩
  exact measurable_toHilbertMatrixL2_of_dense_smoothProbeSequence (U := U) u hu hSmooth

/-- On an open finite-measure domain, the quantitative-slice coefficient field
as an `L²` Hilbert-matrix object is measurable for the local sigma algebra. -/
theorem measurable_toHilbertMatrixL2_of_isOpen_volume_ne_top
    {d : ℕ} {U : Set (Vec d)} {k : ℕ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hUopen : IsOpen U) (hUfinite : MeasureTheory.volume U ≠ ⊤) :
    @Measurable {a : CoeffField d // QuantitativeEllipticSlice U k a}
      (MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U))
      (QuantitativeEllipticSlice.localMeasurableSpace U k) (borel _)
      QuantitativeEllipticSlice.toHilbertMatrixL2 := by
  exact measurable_toHilbertMatrixL2_of_dense_smoothProbeSet (U := U)
    (dense_smoothCompactSupportHilbertMatrixL2_tsupport_subset hUopen hUfinite)

theorem measurable_inner_toScalarL2_hilbertMatrixL2Entry_toHilbertMatrixL2_essentialLocalMeasurableSpace
    {d : ℕ} {U : Set (Vec d)} {k : ℕ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (i j : Fin d) {φ : Vec d → ℝ} (hφL2 : MemScalarL2 U φ)
    (hφ_cont : ContDiff ℝ (⊤ : ℕ∞) φ) (hφ_compact : HasCompactSupport φ)
    (hφ_support : tsupport φ ⊆ U) :
    @Measurable {a : CoeffField d // EssentialQuantitativeEllipticSlice U k a}
      ℝ (EssentialQuantitativeEllipticSlice.localMeasurableSpace U k) (borel ℝ)
      (fun a =>
        inner ℝ (toScalarL2 hφL2)
          (QuantitativeEllipticSlice.hilbertMatrixL2Entry (U := U) i j
            (EssentialQuantitativeEllipticSlice.toHilbertMatrixL2 a))) := by
  rw [show
      (fun a : {a : CoeffField d // EssentialQuantitativeEllipticSlice U k a} =>
        inner ℝ (toScalarL2 hφL2)
          (QuantitativeEllipticSlice.hilbertMatrixL2Entry (U := U) i j
            (EssentialQuantitativeEllipticSlice.toHilbertMatrixL2 a))) =
        fun a : {a : CoeffField d // EssentialQuantitativeEllipticSlice U k a} =>
          ∫ x in U, a.1 x i j * φ x ∂MeasureTheory.volume by
        funext a
        calc
          inner ℝ (toScalarL2 hφL2)
              (QuantitativeEllipticSlice.hilbertMatrixL2Entry (U := U) i j
                (EssentialQuantitativeEllipticSlice.toHilbertMatrixL2 a))
              = ∫ x, φ x * EssentialQuantitativeEllipticSlice.toHilbertMatrixL2 a x i j
                  ∂volumeMeasureOn U :=
            QuantitativeEllipticSlice.inner_toScalarL2_hilbertMatrixL2Entry_eq_integral
              hφL2 i j (EssentialQuantitativeEllipticSlice.toHilbertMatrixL2 a)
          _ = ∫ x, φ x * restrictCoeffField U a.1 x i j ∂volumeMeasureOn U := by
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards [EssentialQuantitativeEllipticSlice.coeFn_toHilbertMatrixL2 a]
              with x hx
            rw [hx]
          _ = ∫ x in U, φ x * a.1 x i j ∂MeasureTheory.volume := by
            unfold volumeMeasureOn
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards [MeasureTheory.ae_restrict_mem a.2.1] with x hxU
            simp [restrictCoeffField, hxU]
          _ = ∫ x in U, a.1 x i j * φ x ∂MeasureTheory.volume := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with x
            ring]
  exact (measurable_entryTestObservable_setIntegral_localSigma
    (U := U) i j hφ_cont hφ_compact hφ_support).comp
      EssentialQuantitativeEllipticSlice.measurable_val_localMeasurableSpace

theorem measurable_inner_hilbertMatrixSmoothProbe_toHilbertMatrixL2_essentialLocalMeasurableSpace
    {d : ℕ} {U : Set (Vec d)} {k : ℕ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] {g : Vec d → HilbertMat d}
    (hgL2 : MeasureTheory.MemLp g 2 (volumeMeasureOn U))
    (hg_cont : ContDiff ℝ (⊤ : ℕ∞) g) (hg_compact : HasCompactSupport g)
    (hg_support : tsupport g ⊆ U) :
    @Measurable {a : CoeffField d // EssentialQuantitativeEllipticSlice U k a}
      ℝ (EssentialQuantitativeEllipticSlice.localMeasurableSpace U k) (borel ℝ)
      (fun a => inner ℝ (hgL2.toLp g)
        (EssentialQuantitativeEllipticSlice.toHilbertMatrixL2 a)) := by
  rw [show
      (fun a : {a : CoeffField d // EssentialQuantitativeEllipticSlice U k a} =>
        inner ℝ (hgL2.toLp g) (EssentialQuantitativeEllipticSlice.toHilbertMatrixL2 a)) =
        fun a : {a : CoeffField d // EssentialQuantitativeEllipticSlice U k a} =>
          ∑ i : Fin d, ∑ j : Fin d,
            inner ℝ (toScalarL2
                (QuantitativeEllipticSlice.memScalarL2_hilbertMatrix_entry_of_memLp
                  (U := U) hgL2 i j))
              (QuantitativeEllipticSlice.hilbertMatrixL2Entry (U := U) i j
                (EssentialQuantitativeEllipticSlice.toHilbertMatrixL2 a)) by
      funext a
      exact QuantitativeEllipticSlice.inner_hilbertMatrixL2_eq_sum_entry_inner hgL2
        (EssentialQuantitativeEllipticSlice.toHilbertMatrixL2 a)]
  refine Finset.measurable_sum _ ?_
  intro i _
  refine Finset.measurable_sum _ ?_
  intro j _
  let gij : Vec d → ℝ := fun x => HilbertMat.entryL i j (g x)
  have hgijL2 : MemScalarL2 U gij := by
    simpa [gij] using
      QuantitativeEllipticSlice.memScalarL2_hilbertMatrix_entry_of_memLp (U := U) hgL2 i j
  have hgij_cont : ContDiff ℝ (⊤ : ℕ∞) gij := by
    simpa [gij, Function.comp_def] using
      (ContDiff.continuousLinearMap_comp (HilbertMat.entryL i j) hg_cont)
  have hgij_compact : HasCompactSupport gij := by
    simpa [gij, Function.comp_def] using
      hg_compact.comp_left (by simp : HilbertMat.entryL i j (0 : HilbertMat d) = 0)
  have hgij_support : tsupport gij ⊆ U := by
    have hsubset : tsupport gij ⊆ tsupport g := by
      simpa [gij, Function.comp_def] using
        (tsupport_comp_subset
          (by simp : HilbertMat.entryL i j (0 : HilbertMat d) = 0) g)
    exact hsubset.trans hg_support
  simpa [gij, hgijL2] using
    measurable_inner_toScalarL2_hilbertMatrixL2Entry_toHilbertMatrixL2_essentialLocalMeasurableSpace
      (U := U) i j hgijL2 hgij_cont hgij_compact hgij_support

theorem measurable_toHilbertMatrixL2_essential_of_dense_smoothProbeSequence
    {d : ℕ} {U : Set (Vec d)} {k : ℕ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (u : ℕ → MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U))
    (hu : DenseRange u)
    (hSmooth : ∀ n : ℕ, ∃ g : Vec d → HilbertMat d,
      ∃ hgL2 : MeasureTheory.MemLp g 2 (volumeMeasureOn U),
        u n = hgL2.toLp g ∧ ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g ∧
          tsupport g ⊆ U) :
    @Measurable {a : CoeffField d // EssentialQuantitativeEllipticSlice U k a}
      (MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U))
      (EssentialQuantitativeEllipticSlice.localMeasurableSpace U k) (borel _)
      EssentialQuantitativeEllipticSlice.toHilbertMatrixL2 := by
  have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨ENNReal.ofNat_ne_top⟩
  let H := MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U)
  let : MeasurableSpace H := borel H
  have : BorelSpace H := ⟨rfl⟩
  refine
    @measurable_of_measurable_inner_denseRange_polish
      {a : CoeffField d // EssentialQuantitativeEllipticSlice U k a} H
      (EssentialQuantitativeEllipticSlice.localMeasurableSpace U k) _ _ _ _ _
      u hu
      (F := EssentialQuantitativeEllipticSlice.toHilbertMatrixL2) ?_
  intro n
  rcases hSmooth n with ⟨g, hgL2, hEq, hg_cont, hg_compact, hg_support⟩
  rw [hEq]
  exact measurable_inner_hilbertMatrixSmoothProbe_toHilbertMatrixL2_essentialLocalMeasurableSpace
    (U := U) hgL2 hg_cont hg_compact hg_support

theorem measurable_toHilbertMatrixL2_essential_of_dense_smoothProbeSet
    {d : ℕ} {U : Set (Vec d)} {k : ℕ} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hDense : Dense {f : MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U) |
      ∃ g : Vec d → HilbertMat d,
      ∃ hgL2 : MeasureTheory.MemLp g 2 (volumeMeasureOn U),
        f = hgL2.toLp g ∧ ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g ∧
          tsupport g ⊆ U}) :
    @Measurable {a : CoeffField d // EssentialQuantitativeEllipticSlice U k a}
      (MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U))
      (EssentialQuantitativeEllipticSlice.localMeasurableSpace U k) (borel _)
      EssentialQuantitativeEllipticSlice.toHilbertMatrixL2 := by
  rcases exists_dense_smoothProbeSequence_of_dense_smoothProbeSet (U := U) hDense with
    ⟨u, hu, hSmooth⟩
  exact measurable_toHilbertMatrixL2_essential_of_dense_smoothProbeSequence (U := U) u hu hSmooth

/-- On an open finite-measure domain, the essential quantitative-slice
coefficient field as an `L²` Hilbert-matrix object is measurable for the local
sigma algebra. -/
theorem measurable_toHilbertMatrixL2_essential_of_isOpen_volume_ne_top
    {d : ℕ} {U : Set (Vec d)} {k : ℕ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hUopen : IsOpen U) (hUfinite : MeasureTheory.volume U ≠ ⊤) :
    @Measurable {a : CoeffField d // EssentialQuantitativeEllipticSlice U k a}
      (MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U))
      (EssentialQuantitativeEllipticSlice.localMeasurableSpace U k) (borel _)
      EssentialQuantitativeEllipticSlice.toHilbertMatrixL2 := by
  exact measurable_toHilbertMatrixL2_essential_of_dense_smoothProbeSet (U := U)
    (dense_smoothCompactSupportHilbertMatrixL2_tsupport_subset hUopen hUfinite)

/-- Smooth probes supported in the open core of a triadic cube are dense for the
half-open cube, because the two restricted volume measures agree. -/
theorem dense_smoothCompactSupportHilbertMatrixL2_tsupport_subset_cubeSet
    {d : ℕ} (Q : TriadicCube d) :
    Dense {f : MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn (cubeSet Q)) |
      ∃ g : Vec d → HilbertMat d,
      ∃ hgL2 : MeasureTheory.MemLp g 2 (volumeMeasureOn (cubeSet Q)),
        f = hgL2.toLp g ∧ ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g ∧
          tsupport g ⊆ cubeSet Q} := by
  have hMeasure : volumeMeasureOn (cubeSet Q) = volumeMeasureOn (openCubeSet Q) := by
    simpa [volumeMeasureOn] using volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q
  rw [hMeasure]
  refine
    (dense_smoothCompactSupportHilbertMatrixL2_tsupport_subset
      (d := d) (U := openCubeSet Q) (isOpen_openCubeSet Q)
      (ne_of_lt (volume_openCubeSet_lt_top Q))).mono ?_
  intro f hf
  rcases hf with ⟨g, hgL2, hfg, hg_cont, hg_compact, hg_support⟩
  exact
    ⟨g, hgL2, hfg, hg_cont, hg_compact,
      hg_support.trans (openCubeSet_subset_cubeSet Q)⟩

/-- On a half-open triadic cube, the essential quantitative-slice coefficient
field as an `L²` Hilbert-matrix object is measurable for the local sigma
algebra. -/
theorem measurable_toHilbertMatrixL2_essentialQuantitativeEllipticSlice_cubeSet
    {d : ℕ} (Q : TriadicCube d) (k : ℕ)
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn (cubeSet Q))] :
    @Measurable {a : CoeffField d // EssentialQuantitativeEllipticSlice (cubeSet Q) k a}
      (MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn (cubeSet Q)))
      (EssentialQuantitativeEllipticSlice.localMeasurableSpace (cubeSet Q) k) (borel _)
      EssentialQuantitativeEllipticSlice.toHilbertMatrixL2 :=
  measurable_toHilbertMatrixL2_essential_of_dense_smoothProbeSet (U := cubeSet Q)
    (dense_smoothCompactSupportHilbertMatrixL2_tsupport_subset_cubeSet Q)

/-- Smooth-probe coordinate pairings of the AEE `L²` coefficient realization
are local-test measurable. -/
theorem measurable_inner_toScalarL2_hilbertMatrixL2Entry_toHilbertMatrixL2_aeeLocalMeasurableSpace
    {d : ℕ} {U : Set (Vec d)} {k : ℕ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (i j : Fin d) {φ : Vec d → ℝ} (hφL2 : MemScalarL2 U φ)
    (hφ_cont : ContDiff ℝ (⊤ : ℕ∞) φ) (hφ_compact : HasCompactSupport φ)
    (hφ_support : tsupport φ ⊆ U) :
    @Measurable {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}
      ℝ (AEEQuantitativeEllipticSlice.localMeasurableSpace U k) (borel ℝ)
      (fun a =>
        inner ℝ (toScalarL2 hφL2)
          (QuantitativeEllipticSlice.hilbertMatrixL2Entry (U := U) i j
            (AEEQuantitativeEllipticSlice.toHilbertMatrixL2 a))) := by
  rw [show
      (fun a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a} =>
        inner ℝ (toScalarL2 hφL2)
          (QuantitativeEllipticSlice.hilbertMatrixL2Entry (U := U) i j
            (AEEQuantitativeEllipticSlice.toHilbertMatrixL2 a))) =
        fun a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a} =>
          ∫ x in U, a.1 x i j * φ x ∂MeasureTheory.volume by
        funext a
        calc
          inner ℝ (toScalarL2 hφL2)
              (QuantitativeEllipticSlice.hilbertMatrixL2Entry (U := U) i j
                (AEEQuantitativeEllipticSlice.toHilbertMatrixL2 a))
              = ∫ x, φ x * AEEQuantitativeEllipticSlice.toHilbertMatrixL2 a x i j
                  ∂volumeMeasureOn U :=
            QuantitativeEllipticSlice.inner_toScalarL2_hilbertMatrixL2Entry_eq_integral
              hφL2 i j (AEEQuantitativeEllipticSlice.toHilbertMatrixL2 a)
          _ = ∫ x, φ x * restrictCoeffField U a.1 x i j ∂volumeMeasureOn U := by
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards [AEEQuantitativeEllipticSlice.coeFn_toHilbertMatrixL2 a]
              with x hx
            rw [hx]
          _ = ∫ x in U, φ x * a.1 x i j ∂MeasureTheory.volume := by
            unfold volumeMeasureOn
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards [MeasureTheory.ae_restrict_mem a.2.measurableSet] with x hxU
            simp [restrictCoeffField, hxU]
          _ = ∫ x in U, a.1 x i j * φ x ∂MeasureTheory.volume := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with x
            ring]
  exact (measurable_entryTestObservable_setIntegral_localSigma
    (U := U) i j hφ_cont hφ_compact hφ_support).comp
      AEEQuantitativeEllipticSlice.measurable_val_localMeasurableSpace

theorem measurable_inner_hilbertMatrixSmoothProbe_toHilbertMatrixL2_aeeLocalMeasurableSpace
    {d : ℕ} {U : Set (Vec d)} {k : ℕ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] {g : Vec d → HilbertMat d}
    (hgL2 : MeasureTheory.MemLp g 2 (volumeMeasureOn U))
    (hg_cont : ContDiff ℝ (⊤ : ℕ∞) g) (hg_compact : HasCompactSupport g)
    (hg_support : tsupport g ⊆ U) :
    @Measurable {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}
      ℝ (AEEQuantitativeEllipticSlice.localMeasurableSpace U k) (borel ℝ)
      (fun a => inner ℝ (hgL2.toLp g)
        (AEEQuantitativeEllipticSlice.toHilbertMatrixL2 a)) := by
  rw [show
      (fun a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a} =>
        inner ℝ (hgL2.toLp g) (AEEQuantitativeEllipticSlice.toHilbertMatrixL2 a)) =
        fun a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a} =>
          ∑ i : Fin d, ∑ j : Fin d,
            inner ℝ (toScalarL2
                (QuantitativeEllipticSlice.memScalarL2_hilbertMatrix_entry_of_memLp
                  (U := U) hgL2 i j))
              (QuantitativeEllipticSlice.hilbertMatrixL2Entry (U := U) i j
                (AEEQuantitativeEllipticSlice.toHilbertMatrixL2 a)) by
      funext a
      exact QuantitativeEllipticSlice.inner_hilbertMatrixL2_eq_sum_entry_inner hgL2
        (AEEQuantitativeEllipticSlice.toHilbertMatrixL2 a)]
  refine Finset.measurable_sum _ ?_
  intro i _
  refine Finset.measurable_sum _ ?_
  intro j _
  let gij : Vec d → ℝ := fun x => HilbertMat.entryL i j (g x)
  have hgijL2 : MemScalarL2 U gij := by
    simpa [gij] using
      QuantitativeEllipticSlice.memScalarL2_hilbertMatrix_entry_of_memLp (U := U) hgL2 i j
  have hgij_cont : ContDiff ℝ (⊤ : ℕ∞) gij := by
    simpa [gij, Function.comp_def] using
      (ContDiff.continuousLinearMap_comp (HilbertMat.entryL i j) hg_cont)
  have hgij_compact : HasCompactSupport gij := by
    simpa [gij, Function.comp_def] using
      hg_compact.comp_left (by simp : HilbertMat.entryL i j (0 : HilbertMat d) = 0)
  have hgij_support : tsupport gij ⊆ U := by
    have hsubset : tsupport gij ⊆ tsupport g := by
      simpa [gij, Function.comp_def] using
        (tsupport_comp_subset
          (by simp : HilbertMat.entryL i j (0 : HilbertMat d) = 0) g)
    exact hsubset.trans hg_support
  simpa [gij, hgijL2] using
    measurable_inner_toScalarL2_hilbertMatrixL2Entry_toHilbertMatrixL2_aeeLocalMeasurableSpace
      (U := U) i j hgijL2 hgij_cont hgij_compact hgij_support

theorem measurable_toHilbertMatrixL2_aee_of_dense_smoothProbeSequence
    {d : ℕ} {U : Set (Vec d)} {k : ℕ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (u : ℕ → MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U))
    (hu : DenseRange u)
    (hSmooth : ∀ n : ℕ, ∃ g : Vec d → HilbertMat d,
      ∃ hgL2 : MeasureTheory.MemLp g 2 (volumeMeasureOn U),
        u n = hgL2.toLp g ∧ ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g ∧
          tsupport g ⊆ U) :
    @Measurable {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}
      (MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U))
      (AEEQuantitativeEllipticSlice.localMeasurableSpace U k) (borel _)
      AEEQuantitativeEllipticSlice.toHilbertMatrixL2 := by
  have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨ENNReal.ofNat_ne_top⟩
  let H := MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U)
  let : MeasurableSpace H := borel H
  have : BorelSpace H := ⟨rfl⟩
  refine
    @measurable_of_measurable_inner_denseRange_polish
      {a : CoeffField d // AEEQuantitativeEllipticSlice U k a} H
      (AEEQuantitativeEllipticSlice.localMeasurableSpace U k) _ _ _ _ _
      u hu
      (F := AEEQuantitativeEllipticSlice.toHilbertMatrixL2) ?_
  intro n
  rcases hSmooth n with ⟨g, hgL2, hEq, hg_cont, hg_compact, hg_support⟩
  rw [hEq]
  exact measurable_inner_hilbertMatrixSmoothProbe_toHilbertMatrixL2_aeeLocalMeasurableSpace
    (U := U) hgL2 hg_cont hg_compact hg_support

theorem measurable_toHilbertMatrixL2_aee_of_dense_smoothProbeSet
    {d : ℕ} {U : Set (Vec d)} {k : ℕ} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hDense : Dense {f : MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U) |
      ∃ g : Vec d → HilbertMat d,
      ∃ hgL2 : MeasureTheory.MemLp g 2 (volumeMeasureOn U),
        f = hgL2.toLp g ∧ ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g ∧
          tsupport g ⊆ U}) :
    @Measurable {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}
      (MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U))
      (AEEQuantitativeEllipticSlice.localMeasurableSpace U k) (borel _)
      AEEQuantitativeEllipticSlice.toHilbertMatrixL2 := by
  rcases exists_dense_smoothProbeSequence_of_dense_smoothProbeSet (U := U) hDense with
    ⟨u, hu, hSmooth⟩
  exact measurable_toHilbertMatrixL2_aee_of_dense_smoothProbeSequence (U := U) u hu hSmooth

/-- On an open finite-measure domain, the AEE quantitative-slice coefficient
field as an `L²` Hilbert-matrix object is measurable for the local sigma
algebra. -/
theorem measurable_toHilbertMatrixL2_aee_of_isOpen_volume_ne_top
    {d : ℕ} {U : Set (Vec d)} {k : ℕ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hUopen : IsOpen U) (hUfinite : MeasureTheory.volume U ≠ ⊤) :
    @Measurable {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}
      (MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U))
      (AEEQuantitativeEllipticSlice.localMeasurableSpace U k) (borel _)
      AEEQuantitativeEllipticSlice.toHilbertMatrixL2 := by
  exact measurable_toHilbertMatrixL2_aee_of_dense_smoothProbeSet (U := U)
    (dense_smoothCompactSupportHilbertMatrixL2_tsupport_subset hUopen hUfinite)

/-- On a half-open triadic cube, the AEE quantitative-slice coefficient field
as an `L²` Hilbert-matrix object is measurable for the local sigma algebra. -/
theorem measurable_toHilbertMatrixL2_aeeQuantitativeEllipticSlice_cubeSet
    {d : ℕ} (Q : TriadicCube d) (k : ℕ)
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn (cubeSet Q))] :
    @Measurable {a : CoeffField d // AEEQuantitativeEllipticSlice (cubeSet Q) k a}
      (MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn (cubeSet Q)))
      (AEEQuantitativeEllipticSlice.localMeasurableSpace (cubeSet Q) k) (borel _)
      AEEQuantitativeEllipticSlice.toHilbertMatrixL2 :=
  measurable_toHilbertMatrixL2_aee_of_dense_smoothProbeSet (U := cubeSet Q)
    (dense_smoothCompactSupportHilbertMatrixL2_tsupport_subset_cubeSet Q)

end Homogenization
