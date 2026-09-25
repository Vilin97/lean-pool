/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Internal.AEESliceAssembly.MuFamily
public import LeanPool.CoarseGraining.Homogenization.Probability.RegCoeffField.SliceMeasurability
public import LeanPool.CoarseGraining.Homogenization.Probability.RegCoeffField.RestrictionBridge

/-! # Carrier Mu Family -/

@[expose] public section

namespace Homogenization

open MeasureTheory
open scoped ENNReal
open scoped Topology
open Filter

/-!
# Carrier `Mu` measurability (Packet P5 centrepiece)

This file re-aims the raw AEE-slice `Mu` measurability spine onto the honest
carrier `RegCoeffField d`.  The raw spine (`AEESliceAssembly/MuFamily.lean`,
`BlockEnergyAverage.lean`, `FixedCompetitorEnergyMeasurability/**`) proves
measurability of the coarse-grained energy `Mu` on the raw slice subtype for the
**fine** local σ-algebra `AEEQuantitativeEllipticSlice.localMeasurableSpace`,
which is a `comap` of the powerset-fine `PointwiseLocalSigma`.  The carrier redesign needs
`Mu` measurable for the honest **entry-test** local σ-algebra `LocalSigmaR`
(P4b), and the carrier's `toFun` does **not** reflect fine local events into
`LocalSigmaR` (pointwise evaluations are not entry-test measurable — the Rao
obstruction), so the fine spine cannot be reused as a black box.

The honest route re-derived here:

* every measurability step of the raw spine factors through the `L²` coefficient
  realization `toHilbertMatrixL2` (the block-energy averages and hence `Mu` are
  Borel functions of it); the raw building blocks
  (`measurable_l2WeightedHilbertMatrixLipschitzIntegral`,
  `measurable_blockEnergyAverage_comp_of_measurable_weightedFullBlockCoeffEntryIntegrals`,
  `measurable_Mu_comp_of_measurable_blockEnergyAverage_affineField_denseSeq`) are
  **domain-generic**, taking the `L²` realization's measurability as an input;
* the one genuinely new fact is that the `L²` realization of a carrier field is
  `LocalSigmaR`-measurable — proved by the dense-probe inner-product criterion,
  whose inner products are exactly the localized entry-test generators
  `entryTestR` of the carrier (`measurable_entryTestR_localSigmaR`), not the fine
  pointwise data.

The result `measurable_Mu_comp_aeeSlice_of_measurable_entryTest` is the generic
engine consumed by `Theorems/Mu.lean`.

Reference: the paper (Armstrong–Kuusi–Loher, to appear).
-/

noncomputable section

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {d : ℕ} {U : Set (Vec d)} {k : ℕ}

/-- The raw AEE-slice element attached to a carrier source. -/
private def rawSlice (A : Ω → RegCoeffField d)
    (hSlice : ∀ ω, AEEQuantitativeEllipticSlice U k (A ω).toFun) (ω : Ω) :
    {a : CoeffField d // AEEQuantitativeEllipticSlice U k a} :=
  ⟨(A ω).toFun, hSlice ω⟩

section CarrierToL2

variable [IsFiniteMeasure (volumeMeasureOn U)]
  {A : Ω → RegCoeffField d}
  {hSlice : ∀ ω, AEEQuantitativeEllipticSlice U k (A ω).toFun}
  (hU : MeasurableSet U)
  (hEntry : ∀ (i j : Fin d) {φ : Vec d → ℝ}, ContDiff ℝ (⊤ : ℕ∞) φ →
    HasCompactSupport φ → tsupport φ ⊆ U →
    @Measurable Ω ℝ mΩ _ (fun ω => entryTestR i j φ (A ω)))

include hU hEntry

/-- Scalar-entry inner product of the carrier `L²` realization against a smooth,
compactly supported scalar probe supported in `U` is a localized entry-test
generator of the carrier field, hence `mΩ`-measurable. -/
theorem measurable_inner_toScalarL2_hilbertMatrixL2Entry_carrier
    (i j : Fin d) {φ : Vec d → ℝ} (hφL2 : MemScalarL2 U φ)
    (hφ_cont : ContDiff ℝ (⊤ : ℕ∞) φ) (hφ_compact : HasCompactSupport φ)
    (hφ_support : tsupport φ ⊆ U) :
    @Measurable Ω ℝ mΩ _
      (fun ω =>
        inner ℝ (toScalarL2 hφL2)
          (QuantitativeEllipticSlice.hilbertMatrixL2Entry (U := U) i j
            (AEEQuantitativeEllipticSlice.toHilbertMatrixL2 (rawSlice A hSlice ω)))) := by
  have hsuppφ : Function.support φ ⊆ U :=
    (Function.support_subset_iff.2 (fun x hx => subset_tsupport φ hx)).trans hφ_support
  have hEq :
      (fun ω =>
        inner ℝ (toScalarL2 hφL2)
          (QuantitativeEllipticSlice.hilbertMatrixL2Entry (U := U) i j
            (AEEQuantitativeEllipticSlice.toHilbertMatrixL2 (rawSlice A hSlice ω))))
        = fun ω => entryTestR i j φ (A ω) := by
    funext ω
    have hInner :
        inner ℝ (toScalarL2 hφL2)
            (QuantitativeEllipticSlice.hilbertMatrixL2Entry (U := U) i j
              (AEEQuantitativeEllipticSlice.toHilbertMatrixL2 (rawSlice A hSlice ω)))
          = ∫ x in U, φ x * (A ω).toFun x i j ∂MeasureTheory.volume := by
      calc
        inner ℝ (toScalarL2 hφL2)
            (QuantitativeEllipticSlice.hilbertMatrixL2Entry (U := U) i j
              (AEEQuantitativeEllipticSlice.toHilbertMatrixL2 (rawSlice A hSlice ω)))
            = ∫ x, φ x *
                AEEQuantitativeEllipticSlice.toHilbertMatrixL2 (rawSlice A hSlice ω) x i j
                ∂volumeMeasureOn U :=
          QuantitativeEllipticSlice.inner_toScalarL2_hilbertMatrixL2Entry_eq_integral
            hφL2 i j (AEEQuantitativeEllipticSlice.toHilbertMatrixL2 (rawSlice A hSlice ω))
        _ = ∫ x, φ x * restrictCoeffField U (rawSlice A hSlice ω).1 x i j
              ∂volumeMeasureOn U := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards
              [AEEQuantitativeEllipticSlice.coeFn_toHilbertMatrixL2 (rawSlice A hSlice ω)]
            with x hx
          rw [hx]
        _ = ∫ x in U, φ x * (A ω).toFun x i j ∂MeasureTheory.volume := by
          unfold volumeMeasureOn
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards [MeasureTheory.ae_restrict_mem (rawSlice A hSlice ω).2.measurableSet]
            with x hxU
          simp [restrictCoeffField, hxU, rawSlice]
    calc
      inner ℝ (toScalarL2 hφL2)
          (QuantitativeEllipticSlice.hilbertMatrixL2Entry (U := U) i j
            (AEEQuantitativeEllipticSlice.toHilbertMatrixL2 (rawSlice A hSlice ω))) =
          ∫ x in U, φ x * (A ω).toFun x i j ∂MeasureTheory.volume := hInner
      _ = entryTestR i j φ (A ω) :=
        (entryTestR_eq_setIntegral_of_support hU i j hsuppφ (A ω)).symm
  rw [hEq]
  exact hEntry i j hφ_cont hφ_compact hφ_support

/-- Smooth `HilbertMat`-valued probe inner product of the carrier `L²`
realization is `mΩ`-measurable: it decomposes into a finite sum of localized
scalar entry-test generators of the carrier field. -/
theorem measurable_inner_hilbertMatrixSmoothProbe_toHilbertMatrixL2_carrier
    {g : Vec d → HilbertMat d} (hgL2 : MeasureTheory.MemLp g 2 (volumeMeasureOn U))
    (hg_cont : ContDiff ℝ (⊤ : ℕ∞) g) (hg_compact : HasCompactSupport g)
    (hg_support : tsupport g ⊆ U) :
    @Measurable Ω ℝ mΩ _
      (fun ω =>
        inner ℝ (hgL2.toLp g)
          (AEEQuantitativeEllipticSlice.toHilbertMatrixL2 (rawSlice A hSlice ω))) := by
  have hEq :
      (fun ω =>
        inner ℝ (hgL2.toLp g)
          (AEEQuantitativeEllipticSlice.toHilbertMatrixL2 (rawSlice A hSlice ω)))
        = fun ω =>
          ∑ i : Fin d, ∑ j : Fin d,
            inner ℝ (toScalarL2
                (QuantitativeEllipticSlice.memScalarL2_hilbertMatrix_entry_of_memLp
                  (U := U) hgL2 i j))
              (QuantitativeEllipticSlice.hilbertMatrixL2Entry (U := U) i j
                (AEEQuantitativeEllipticSlice.toHilbertMatrixL2 (rawSlice A hSlice ω))) := by
    funext ω
    exact QuantitativeEllipticSlice.inner_hilbertMatrixL2_eq_sum_entry_inner hgL2
      (AEEQuantitativeEllipticSlice.toHilbertMatrixL2 (rawSlice A hSlice ω))
  rw [hEq]
  refine Finset.measurable_sum _ (fun i _ => Finset.measurable_sum _ (fun j _ => ?_))
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
    measurable_inner_toScalarL2_hilbertMatrixL2Entry_carrier
      (mΩ := mΩ) hU hEntry i j hgijL2 hgij_cont hgij_compact hgij_support

/-- **The carrier `L²` coefficient realization is `mΩ`-measurable.**  Proved by
the dense smooth-probe inner-product criterion; each inner product is a finite
sum of localized entry-test generators of the carrier field. -/
theorem measurable_toHilbertMatrixL2_carrier
    (hUopen : IsOpen U) (hUfinite : MeasureTheory.volume U ≠ ⊤) :
    @Measurable Ω (MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U)) mΩ (borel _)
      (fun ω => AEEQuantitativeEllipticSlice.toHilbertMatrixL2 (rawSlice A hSlice ω)) := by
  have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨ENNReal.ofNat_ne_top⟩
  let : MeasurableSpace (MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U)) := borel _
  have : BorelSpace (MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U)) := ⟨rfl⟩
  obtain ⟨u, hu, hSmooth⟩ :=
    exists_dense_smoothProbeSequence_of_dense_smoothProbeSet (U := U)
      (dense_smoothCompactSupportHilbertMatrixL2_tsupport_subset hUopen hUfinite)
  refine measurable_of_measurable_inner_denseRange_polish u hu (fun n => ?_)
  rcases hSmooth n with ⟨g, hgL2, hEqn, hg_cont, hg_compact, hg_support⟩
  rw [hEqn]
  exact measurable_inner_hilbertMatrixSmoothProbe_toHilbertMatrixL2_carrier
    (mΩ := mΩ) hU hEntry hgL2 hg_cont hg_compact hg_support

end CarrierToL2

/-! ## Block-energy averages and `Mu` from the carrier `L²` realization

These lemmas take the carrier `L²` realization's measurability `hF` (produced by
`measurable_toHilbertMatrixL2_carrier`) and thread the domain-generic raw
block-energy → `Mu` spine.  The weighted-integral atoms mirror
`BlockEnergyAverage.lean`, replacing the subtype `L²` realization with `hF`. -/

section CarrierBlockEnergy

variable [IsFiniteMeasure (volumeMeasureOn U)]
  {A : Ω → RegCoeffField d}
  {hSlice : ∀ ω, AEEQuantitativeEllipticSlice U k (A ω).toFun}
  (hF : @Measurable Ω (MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U)) mΩ (borel _)
    (fun ω => AEEQuantitativeEllipticSlice.toHilbertMatrixL2 (rawSlice A hSlice ω)))

include hF

/-- Carrier version of the `L²`-weighted full-block coefficient-entry integral
measurability, for an `L²` weight. -/
theorem measurable_l2WeightedFullBlockCoeffEntry_carrier
    {w : Vec d → ℝ} (hw : MemScalarL2 U w) (α β : BlockCoord d) :
    @Measurable Ω ℝ mΩ _
      (fun ω =>
        ∫ x in U, w x * toFullBlockMat (blockCoeffField (A ω).toFun x) α β
          ∂MeasureTheory.volume) := by
  obtain ⟨Q', hQ_lip, hQ_eq_on⟩ :=
    (lipschitzOnWith_fullBlockCoeffEntry_hilbertMat_quantitative
      (d := d) (k := k) α β).extend_real
  have hrw :
      (fun ω =>
        ∫ x in U, w x * toFullBlockMat (blockCoeffField (A ω).toFun x) α β
          ∂MeasureTheory.volume)
        = fun ω =>
          ∫ x, w x *
            Q' (AEEQuantitativeEllipticSlice.toHilbertMatrixL2 (rawSlice A hSlice ω) x)
            ∂volumeMeasureOn U := by
    funext ω
    calc
      ∫ x in U, w x * toFullBlockMat (blockCoeffField (A ω).toFun x) α β
          ∂MeasureTheory.volume
          = ∫ x, w x *
              toFullBlockMat
                (blockMatrixOfCoeff
                  (AEEQuantitativeEllipticSlice.toHilbertMatrixL2 (rawSlice A hSlice ω) x).toMat)
                α β
              ∂volumeMeasureOn U :=
        AEEQuantitativeEllipticSlice.weightedFullBlockCoeffEntryIntegral_eq_hilbertMatrixL2
          (rawSlice A hSlice ω) w α β
      _ = ∫ x, w x *
            Q' (AEEQuantitativeEllipticSlice.toHilbertMatrixL2 (rawSlice A hSlice ω) x)
            ∂volumeMeasureOn U := by
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards
            [AEEQuantitativeEllipticSlice.ae_toHilbertMatrixL2_mem_quantitativeEllipticHilbertMatSet
              (rawSlice A hSlice ω)]
          with x hx
        have h :
            toFullBlockMat
                (blockMatrixOfCoeff
                  (AEEQuantitativeEllipticSlice.toHilbertMatrixL2 (rawSlice A hSlice ω) x).toMat)
                α β
              = Q' (AEEQuantitativeEllipticSlice.toHilbertMatrixL2 (rawSlice A hSlice ω) x) :=
          hQ_eq_on hx
        rw [h]
  rw [hrw]
  exact measurable_l2WeightedHilbertMatrixLipschitzIntegral hF hw hQ_lip

/-- Carrier version of the `L²`-weighted full-block coefficient-entry integral
measurability, for an integrable weight (`L²` weights are dense; simple-function
approximation upgrades the previous lemma). -/
theorem measurable_integrableWeightedFullBlockCoeffEntry_carrier_of_measurable
    {w : Vec d → ℝ} (hw_meas : Measurable w)
    (hw_int : MeasureTheory.Integrable w (volumeMeasureOn U)) (α β : BlockCoord d) :
    @Measurable Ω ℝ mΩ _
      (fun ω =>
        ∫ x in U, w x * toFullBlockMat (blockCoeffField (A ω).toFun x) α β
          ∂MeasureTheory.volume) := by
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
      ∀ n, @Measurable Ω ℝ mΩ _
        (fun ω =>
          ∫ x in U, s n x * toFullBlockMat (blockCoeffField (A ω).toFun x) α β
            ∂MeasureTheory.volume) :=
    fun n => measurable_l2WeightedFullBlockCoeffEntry_carrier hF (hs_L2 n) α β
  have hs_tendsto :
      Filter.Tendsto
        (fun n : ℕ => fun ω : Ω =>
          ∫ x in U, s n x * toFullBlockMat (blockCoeffField (A ω).toFun x) α β
            ∂MeasureTheory.volume)
        atTop
        (𝓝 fun ω : Ω =>
          ∫ x in U, w x * toFullBlockMat (blockCoeffField (A ω).toFun x) α β
            ∂MeasureTheory.volume) := by
    rw [tendsto_pi_nhds]
    intro ω
    have hprod_int :
        MeasureTheory.Integrable
          (fun x => w x * toFullBlockMat (blockCoeffField (A ω).toFun x) α β) μ := by
      simpa [μ] using
        (hSlice ω).integrable_weightedFullBlockCoeffEntry_of_integrable hw_int α β
    have hs_prod_int :
        ∀ n, MeasureTheory.Integrable
            (fun x => s n x * toFullBlockMat (blockCoeffField (A ω).toFun x) α β) μ := by
      intro n
      have hs_int : MeasureTheory.Integrable (s n) μ := by
        simpa [s, μ] using
          (MeasureTheory.SimpleFunc.integrable_of_isFiniteMeasure
            (MeasureTheory.SimpleFunc.approxOn w hw_meas (Set.range w ∪ {0}) 0 (by simp) n))
      simpa [μ] using
        (hSlice ω).integrable_weightedFullBlockCoeffEntry_of_integrable hs_int α β
    have hcoeff_bound :
        ∀ᵐ x ∂ μ, ‖toFullBlockMat (blockCoeffField (A ω).toFun x) α β‖ ≤ C := by
      filter_upwards [(hSlice ω).ae_isEllipticMatrix] with x hxEll
      simpa [μ, C, blockCoeffField, Real.norm_eq_abs] using
        abs_toFullBlockMat_blockMatrixOfCoeff_entry_le_of_isEllipticMatrix
          (A := (A ω).toFun x) hxEll α β
    have hbound :
        ∀ n, ∀ᵐ x ∂ μ,
          ‖s n x * toFullBlockMat (blockCoeffField (A ω).toFun x) α β‖ ≤ (2 * C) * ‖w x‖ := by
      intro n
      filter_upwards [hcoeff_bound] with x hxcoeff
      have hsx : ‖s n x‖ ≤ ‖w x‖ + ‖w x‖ := by
        simpa [s] using
          MeasureTheory.SimpleFunc.norm_approxOn_zero_le hw_meas
            (s := Set.range w ∪ {0}) (by simp) x n
      have hmul_nonneg : 0 ≤ ‖w x‖ + ‖w x‖ := by positivity
      have hcoeff_nonneg :
          0 ≤ ‖toFullBlockMat (blockCoeffField (A ω).toFun x) α β‖ := by positivity
      calc
        ‖s n x * toFullBlockMat (blockCoeffField (A ω).toFun x) α β‖
            = ‖s n x‖ * ‖toFullBlockMat (blockCoeffField (A ω).toFun x) α β‖ := norm_mul _ _
        _ ≤ (‖w x‖ + ‖w x‖) * C := mul_le_mul hsx hxcoeff hcoeff_nonneg hmul_nonneg
        _ = (2 * C) * ‖w x‖ := by ring
    have hbound_int : MeasureTheory.Integrable (fun x => (2 * C) * ‖w x‖) μ := by
      simpa [mul_assoc] using hw_int.norm.const_mul (2 * C)
    have hlim :
        ∀ᵐ x ∂ μ,
          Tendsto (fun n : ℕ => s n x * toFullBlockMat (blockCoeffField (A ω).toFun x) α β)
            atTop (𝓝 (w x * toFullBlockMat (blockCoeffField (A ω).toFun x) α β)) := by
      refine Filter.Eventually.of_forall (fun x => ?_)
      exact
        (MeasureTheory.SimpleFunc.tendsto_approxOn hw_meas
            (s := Set.range w ∪ {0}) (y₀ := 0) (by simp)
            (x := x) (subset_closure (Or.inl ⟨x, rfl⟩))).mul tendsto_const_nhds
    simpa [MeasureTheory.IntegrableOn, volumeMeasureOn, μ, s] using
      MeasureTheory.tendsto_integral_of_dominated_convergence
        (μ := μ) (G := ℝ)
        (F := fun n x => s n x * toFullBlockMat (blockCoeffField (A ω).toFun x) α β)
        (f := fun x => w x * toFullBlockMat (blockCoeffField (A ω).toFun x) α β)
        (fun x => (2 * C) * ‖w x‖)
        (fun n => (hs_prod_int n).aestronglyMeasurable) hbound_int hbound hlim
  exact measurable_of_tendsto_metrizable hs_meas hs_tendsto

/-- Carrier version, for a general integrable weight (drop the measurability of
`w` by passing to a measurable representative). -/
theorem measurable_integrableWeightedFullBlockCoeffEntry_carrier
    {w : Vec d → ℝ} (hw : MeasureTheory.Integrable w (volumeMeasureOn U)) (α β : BlockCoord d) :
    @Measurable Ω ℝ mΩ _
      (fun ω =>
        ∫ x in U, w x * toFullBlockMat (blockCoeffField (A ω).toFun x) α β
          ∂MeasureTheory.volume) := by
  classical
  let w' : Vec d → ℝ := hw.aestronglyMeasurable.mk w
  have hw'_meas : Measurable w' := by
    simpa [w'] using hw.aestronglyMeasurable.measurable_mk
  have hw'_int : MeasureTheory.Integrable w' (volumeMeasureOn U) :=
    hw.congr hw.aestronglyMeasurable.ae_eq_mk
  have hmeas' :
      @Measurable Ω ℝ mΩ _
        (fun ω =>
          ∫ x in U, w' x * toFullBlockMat (blockCoeffField (A ω).toFun x) α β
            ∂MeasureTheory.volume) :=
    measurable_integrableWeightedFullBlockCoeffEntry_carrier_of_measurable hF hw'_meas hw'_int α β
  have hrw :
      (fun ω =>
        ∫ x in U, w x * toFullBlockMat (blockCoeffField (A ω).toFun x) α β
          ∂MeasureTheory.volume)
        = fun ω =>
          ∫ x in U, w' x * toFullBlockMat (blockCoeffField (A ω).toFun x) α β
            ∂MeasureTheory.volume := by
    funext ω
    apply MeasureTheory.integral_congr_ae
    filter_upwards [hw.aestronglyMeasurable.ae_eq_mk] with x hx
    rw [hx]
  rw [hrw]; exact hmeas'

/-- Carrier block-energy average measurability from `hF`. -/
theorem measurable_blockEnergyAverage_carrier (X : BlockState d) (hX : MemBlockL2 U X.eval) :
    @Measurable Ω ℝ mΩ _ (fun ω => blockEnergyAverage U (A ω).toFun X) :=
  measurable_blockEnergyAverage_comp_of_measurable_weightedFullBlockCoeffEntryIntegrals
    (A := fun ω => (A ω).toFun) (X := X)
    (fun ω α β =>
      (hSlice ω).integrableOn_weightedFullBlockCoeffEntry_of_memBlockL2 hX α β)
    (fun α β =>
      measurable_integrableWeightedFullBlockCoeffEntry_carrier hF
        (integrable_blockEnergyEntryWeight_of_memBlockL2 hX α β) α β)

end CarrierBlockEnergy

/-! ## The generic engine -/

section CarrierEngine

variable (Q : TriadicCube d) {A : Ω → RegCoeffField d}
  (hSlice : ∀ ω, AEEQuantitativeEllipticSlice (cubeSet Q) k (A ω).toFun)

include hSlice

/-- **Carrier `L²` realization measurability on a triadic cube.**  The half-open
cube is not open, so density of smooth probes is imported from the open core (the
two restricted volume measures agree). -/
theorem measurable_toHilbertMatrixL2_carrier_cubeSet
    (hEntry : ∀ (i j : Fin d) {φ : Vec d → ℝ}, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ cubeSet Q →
      @Measurable Ω ℝ mΩ _ (fun ω => entryTestR i j φ (A ω))) :
    @Measurable Ω (MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn (cubeSet Q))) mΩ (borel _)
      (fun ω =>
        AEEQuantitativeEllipticSlice.toHilbertMatrixL2
          (rawSlice (U := cubeSet Q) (k := k) A hSlice ω)) := by
  have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨ENNReal.ofNat_ne_top⟩
  let : MeasurableSpace (MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn (cubeSet Q))) :=
    borel _
  have : BorelSpace (MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn (cubeSet Q))) := ⟨rfl⟩
  obtain ⟨u, hu, hSmooth⟩ :=
    exists_dense_smoothProbeSequence_of_dense_smoothProbeSet (U := cubeSet Q)
      (dense_smoothCompactSupportHilbertMatrixL2_tsupport_subset_cubeSet Q)
  refine measurable_of_measurable_inner_denseRange_polish u hu (fun n => ?_)
  rcases hSmooth n with ⟨g, hgL2, hEqn, hg_cont, hg_compact, hg_support⟩
  rw [hEqn]
  exact measurable_inner_hilbertMatrixSmoothProbe_toHilbertMatrixL2_carrier
    (mΩ := mΩ) (measurableSet_cubeSet Q) hEntry hgL2 hg_cont hg_compact hg_support

/-- **The generic carrier `Mu` measurability engine.**  Given a carrier source
`A` landing a.e.-elliptically in the AEE quantitative `k`-slice of a triadic cube,
whose localized entry-test generators are `mΩ`-measurable, the coarse-grained
energy `ω ↦ Mu (cubeSet Q) P (A ω).toFun` is `mΩ`-measurable.  This is the P5
carrier re-aim of the raw `Mu`-slice measurability spine. -/
theorem measurable_Mu_comp_aeeSlice_of_measurable_entryTest
    (hEntry : ∀ (i j : Fin d) {φ : Vec d → ℝ}, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ cubeSet Q →
      @Measurable Ω ℝ mΩ _ (fun ω => entryTestR i j φ (A ω)))
    (P : BlockVec d) :
    @Measurable Ω ℝ mΩ _ (fun ω => Mu (cubeSet Q) P (A ω).toFun) := by
  have hF := measurable_toHilbertMatrixL2_carrier_cubeSet Q hSlice hEntry
  have hRewrite :
      (fun ω => Mu (cubeSet Q) P (A ω).toFun)
        = fun ω =>
          ⨅ n : ℕ,
            blockEnergyAverage (cubeSet Q) (A ω).toFun
              (canonicalMuGeneratorAffineField (U := cubeSet Q) P
                (TopologicalSpace.denseSeq
                  (canonicalMuBlockCorrectionGeneratorSubmodule (cubeSet Q)) n)) := by
    funext ω
    exact mu_eq_iInf_blockEnergyAverage_canonicalAEEMuGenerator Q k (rawSlice A hSlice ω) P
  rw [hRewrite]
  refine Measurable.iInf (fun n => ?_)
  exact measurable_blockEnergyAverage_carrier hF
    (canonicalMuGeneratorAffineField (U := cubeSet Q) P
      (TopologicalSpace.denseSeq
        (canonicalMuBlockCorrectionGeneratorSubmodule (cubeSet Q)) n))
    (canonicalMuGeneratorAffineField_memBlockL2 (U := cubeSet Q) P
      (TopologicalSpace.denseSeq
        (canonicalMuBlockCorrectionGeneratorSubmodule (cubeSet Q)) n))

end CarrierEngine

end

end Homogenization
