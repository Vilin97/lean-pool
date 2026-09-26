/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.AxisCubeHarmonicGain
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.ClosedBallNormalizedL2
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.LocalComparisonBridges
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.LocalScaledDatumEnergy
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.LocalWeightedTailRestrict
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.OneBallTailAlgebra
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.StoppingEnergyTransfer

/-! # One Stopping Ball Comparison -/

@[expose] public section

namespace Homogenization

open scoped ENNReal

noncomputable section

namespace CubeCalderonZygmund

open Filter MeasureTheory Set

/-!
# The one-stopping-ball comparison estimate

This is the local, genuinely PDE-derived step in the cube good-`lambda`
argument.  At an exact stopping radius it constructs the zero-trace harmonic
replacement on the comparison parent, applies the finite-exponent harmonic
gain on its triadic descendant, and then applies the weighted comparison-tail
inequality.  No harmonic comparison or tail estimate is an input hypothesis.

The datum in the stopping energy is `sigma0⁻¹ • hilbertifyVecField H`.  This
normalization is essential: it makes every constant below independent of the
ellipticity scale, while the final source norm has exactly the expected
`sigma0⁻¹` factor.
-/

/-- The coefficient produced by the one-ball comparison.  The first summand
comes from the harmonic `L^q` gain on `B_(5r)`, the second from the
zero-trace correction energy on its comparison parent.  In the final tail
bound it multiplies the factored quantity
`(M / 2)^(2-q) + eps^2`; keeping this source-facing factor separate is what
allows the later good-`lambda` parameter choice. -/
def oneStoppingBallCoefficient {d : ℕ} {q : FiniteLpExponent} (depth : ℕ)
    (G : INTERNAL.HarmonicEuclideanGradientGain d q depth) : ℝ≥0∞ :=
  4 * (5 : ℝ≥0∞) ^ d *
      (2 * (G.fixedValue * (d : ℝ≥0∞))) ^ q.exponent.toReal +
    12 * ENNReal.ofReal ((5 * (3 : ℝ) ^ depth) ^ d)

/-- The coefficient is finite; hence it may safely be used in the later
weighted layer-cake integration without an implicit extended-real exception. -/
theorem oneStoppingBallCoefficient_ne_top {d : ℕ} {q : FiniteLpExponent}
    {depth : ℕ} (G : INTERNAL.HarmonicEuclideanGradientGain d q depth) :
    oneStoppingBallCoefficient depth G ≠ ∞ := by
  unfold oneStoppingBallCoefficient
  rw [ENNReal.add_ne_top]
  constructor
  · apply ENNReal.mul_ne_top
    · apply ENNReal.mul_ne_top
      · norm_num
      · exact ENNReal.pow_ne_top (by norm_num)
    · exact ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg
        (ENNReal.mul_ne_top (by norm_num) (axisCube_harmonicEuclideanGradientGain_coefficient_ne_top G))
  · apply ENNReal.mul_ne_top
    · norm_num
    · exact ENNReal.ofReal_ne_top

/-- The exact stopping identity and the last-exit bound control both fields on
the *actual* harmonic-comparison parent.  This is deliberately stated before
the PDE comparison: it is the point at which the conservative radius cutoff
is converted into the sharp parent-radius input required by the local
replacement. -/
theorem stoppingComparisonParent_eLpNorm_two_bounds_of_stop_lastExit
    {d : ℕ} [NeZero d] {F G : Type*} [NormedAddCommGroup F]
    [NormedAddCommGroup G] (f : Vec d → F) (g : Vec d → G)
    {eps level r R : ℝ} (heps : 0 < eps) (hr : 0 < r) (depth : ℕ)
    (hcutoff : r ≤ R / (10 * (3 : ℝ) ^ depth))
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) (x : Vec d)
    (hlast : ∀ s ∈ Icc r R, goodLambdaCombinedEnergy f g eps x s ≤ level) :
    eLpNorm f 2
        (axisCubeNormalizedMeasure (stoppingComparisonParentCorner x r depth)
          (stoppingComparisonParentSide r depth)) ≤ ENNReal.ofReal level ∧
      eLpNorm g 2
        (axisCubeNormalizedMeasure (stoppingComparisonParentCorner x r depth)
          (stoppingComparisonParentSide r depth)) ≤ ENNReal.ofReal (eps * level) := by
  let parentRadius : ℝ := stoppingComparisonParentMultiplier depth * r
  have hrnonneg : 0 ≤ r := hr.le
  have hparent_mem : parentRadius ∈ Icc r R := by
    simpa only [parentRadius, stoppingComparisonParentMultiplier] using!
      (stoppingComparisonParentRadius_mem_Icc_of_le hrnonneg depth hcutoff)
  have hparent_energy : goodLambdaCombinedEnergy f g eps x parentRadius ≤ level :=
    hlast parentRadius hparent_mem
  obtain ⟨hf_energy, hg_energy⟩ :=
    closedBallL2Energy_sqrt_bounds_of_goodLambdaCombinedEnergy_le f g heps
      (mul_pos (by
        simp only [stoppingComparisonParentMultiplier]
        positivity) hr) x hparent_energy
  constructor
  · rw [stoppingComparisonParent_eLpNorm_two_eq_ofReal_sqrt_closedBallL2Energy
      x hr depth f (hf.restrict _)]
    exact ENNReal.ofReal_le_ofReal hf_energy
  · rw [stoppingComparisonParent_eLpNorm_two_eq_ofReal_sqrt_closedBallL2Energy
      x hr depth g (hg.restrict _)]
    exact ENNReal.ofReal_le_ofReal hg_energy

/-- The PDE part of the one-ball argument.  The zero-trace correction and its
harmonic remainder are constructed internally; the returned bounds are the
two inputs needed by the weighted-tail step. -/
theorem exists_stoppingComparison_harmonic_remainder
    {d : ℕ} [NeZero d] {q : FiniteLpExponent} {depth : ℕ}
    (G : INTERNAL.HarmonicEuclideanGradientGain d q depth)
    (x : Vec d) {r R sigma0 eps level : ℝ}
    (hr : 0 < r) (hsigma0 : 0 < sigma0) (heps : 0 < eps) (heps_one : eps ≤ 1)
    (hcutoff : r ≤ R / (10 * (3 : ℝ) ^ depth))
    (f : Vec d → HilbertVec d) (H : Vec d → Vec d)
    (hf : MemLp f 2 volume) (hH : MemLp (hilbertifyVecField H) 2 volume)
    (u : H1Function
      (axisCube (stoppingComparisonParentCorner x r depth)
        (stoppingComparisonParentSide r depth)))
    (hfu : f =ᵐ[volume.restrict
      (axisCube (stoppingComparisonParentCorner x r depth)
        (stoppingComparisonParentSide r depth))] hilbertifyVecField u.grad)
    (hweak : ∀ phi : Vec d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) phi → HasCompactSupport phi →
      tsupport phi ⊆ axisCube (stoppingComparisonParentCorner x r depth)
        (stoppingComparisonParentSide r depth) →
      sigma0 * ∫ y in axisCube (stoppingComparisonParentCorner x r depth)
          (stoppingComparisonParentSide r depth),
        vecDot (u.grad y) (euclideanGradient phi y) ∂volume =
          -∫ y in axisCube (stoppingComparisonParentCorner x r depth)
            (stoppingComparisonParentSide r depth),
            vecDot (H y) (euclideanGradient phi y) ∂volume)
    (hlast : ∀ s ∈ Icc r R,
      goodLambdaCombinedEnergy f (sigma0⁻¹ • hilbertifyVecField H) eps x s ≤ level) :
    ∃ w : H10Function
        (axisCube (stoppingComparisonParentCorner x r depth)
          (stoppingComparisonParentSide r depth)),
      WeakPoissonEquationOn
        (axisCube (stoppingComparisonParentCorner x r depth)
          (stoppingComparisonParentSide r depth))
        (u - w.toH1Function) 0 ∧
      eLpNorm (hilbertifyVecField w.toH1Function.grad) 2
        (axisCubeNormalizedMeasure (stoppingComparisonParentCorner x r depth)
          (stoppingComparisonParentSide r depth)) ≤ ENNReal.ofReal (eps * level) ∧
      MemLp (hilbertifyVecField (u - w.toH1Function).grad) q.exponent
        (axisCubeNormalizedMeasure
          (axisCubeConcentricDepthCorner (stoppingComparisonParentCorner x r depth)
            (stoppingComparisonParentSide r depth) depth)
          (axisCubeConcentricDepthSide (stoppingComparisonParentSide r depth) depth)) ∧
      eLpNorm (hilbertifyVecField (u - w.toH1Function).grad) q.exponent
        (axisCubeNormalizedMeasure
          (axisCubeConcentricDepthCorner (stoppingComparisonParentCorner x r depth)
            (stoppingComparisonParentSide r depth) depth)
          (axisCubeConcentricDepthSide (stoppingComparisonParentSide r depth) depth)) ≤
        (2 * (G.fixedValue * (d : ℝ≥0∞))) * ENNReal.ofReal level := by
  let U : Set (Vec d) := axisCube (stoppingComparisonParentCorner x r depth)
    (stoppingComparisonParentSide r depth)
  have hL : 0 < stoppingComparisonParentSide r depth := by
    simp only [stoppingComparisonParentSide, stoppingAxisCubeSide,
      stoppingComparisonParentMultiplier]
    positivity
  have hscale_ne_top : ENNReal.ofReal ((stoppingComparisonParentSide r depth) ^ d)⁻¹ ≠ ∞ := by
    exact ENNReal.ofReal_ne_top
  have hfU : MemLp f 2 (axisCubeNormalizedMeasure
      (stoppingComparisonParentCorner x r depth) (stoppingComparisonParentSide r depth)) := by
    rw [axisCubeNormalizedMeasure_eq_smul_volume_restrict _ _ hL]
    exact (hf.restrict U).smul_measure hscale_ne_top
  have hfuU : f =ᵐ[axisCubeNormalizedMeasure
      (stoppingComparisonParentCorner x r depth) (stoppingComparisonParentSide r depth)]
      hilbertifyVecField u.grad := by
    rw [axisCubeNormalizedMeasure_eq_smul_volume_restrict _ _ hL]
    exact Measure.smul_absolutelyContinuous.ae_eq (by simpa only [U] using hfu)
  have huU : MemLp (hilbertifyVecField u.grad) 2
      (axisCubeNormalizedMeasure (stoppingComparisonParentCorner x r depth)
        (stoppingComparisonParentSide r depth)) :=
    (memLp_congr_ae hfuU).mp hfU
  have hHU : MemVectorL2 U H :=
    memVectorL2_of_memLp_hilbertifyVecField hH
  obtain ⟨w, _hw, hwHarm, hwenergy⟩ :=
    exists_local_harmonic_replacement_axisCube
      (stoppingComparisonParentCorner x r depth) hL hsigma0 u hHU (by
        simpa only [U] using hweak)
  have hparent := stoppingComparisonParent_eLpNorm_two_bounds_of_stop_lastExit
    f (sigma0⁻¹ • hilbertifyVecField H) heps hr depth hcutoff hf
      (hH.const_smul sigma0⁻¹) x hlast
  have hwbound : eLpNorm (hilbertifyVecField w.toH1Function.grad) 2
      (axisCubeNormalizedMeasure (stoppingComparisonParentCorner x r depth)
        (stoppingComparisonParentSide r depth)) ≤ ENNReal.ofReal (eps * level) := by
    calc
      eLpNorm (hilbertifyVecField w.toH1Function.grad) 2
          (axisCubeNormalizedMeasure (stoppingComparisonParentCorner x r depth)
            (stoppingComparisonParentSide r depth)) ≤
          eLpNorm (sigma0⁻¹ • hilbertifyVecField H) 2
            (axisCubeNormalizedMeasure (stoppingComparisonParentCorner x r depth)
              (stoppingComparisonParentSide r depth)) :=
        axisCubeNormalized_eLpNorm_harmonicCorrection_le_scaledDatum
          (stoppingComparisonParentCorner x r depth) hL hsigma0 w.toH1Function hHU hwenergy
      _ ≤ ENNReal.ofReal (eps * level) := hparent.2
  have hvGain := axisCube_harmonicEuclideanGradientGain G
    (stoppingComparisonParentCorner x r depth) (stoppingComparisonParentSide r depth)
      hL (u - w.toH1Function) hwHarm
  refine ⟨w, hwHarm, hwbound, ?_, ?_⟩
  · simpa only [hilbertifyVecField] using! hvGain.1
  · have hvfield : hilbertifyVecField (u - w.toH1Function).grad =
        hilbertifyVecField u.grad + (-hilbertifyVecField w.toH1Function.grad) := by
      funext y
      change HilbertVec.ofVec ((u - w.toH1Function).grad y) =
        HilbertVec.ofVec (u.grad y) + -HilbertVec.ofVec (w.toH1Function.grad y)
      rw [H1Function.sub_grad]
      exact (HilbertVec.continuousLinearEquivVec d).symm.map_sub _ _
    change MemLp (hilbertifyVecField (u - w.toH1Function).grad) q.exponent _ ∧
      eLpNorm (hilbertifyVecField (u - w.toH1Function).grad) q.exponent _ ≤ _ at hvGain
    calc
      eLpNorm (hilbertifyVecField (u - w.toH1Function).grad) q.exponent
          (axisCubeNormalizedMeasure
            (axisCubeConcentricDepthCorner (stoppingComparisonParentCorner x r depth)
              (stoppingComparisonParentSide r depth) depth)
            (axisCubeConcentricDepthSide (stoppingComparisonParentSide r depth) depth)) ≤
          (G.fixedValue * (d : ℝ≥0∞)) *
            eLpNorm (hilbertifyVecField (u - w.toH1Function).grad) 2
              (axisCubeNormalizedMeasure (stoppingComparisonParentCorner x r depth)
                (stoppingComparisonParentSide r depth)) := hvGain.2
      _ = (G.fixedValue * (d : ℝ≥0∞)) *
            eLpNorm (hilbertifyVecField u.grad +
              (-hilbertifyVecField w.toH1Function.grad)) 2
              (axisCubeNormalizedMeasure (stoppingComparisonParentCorner x r depth)
                (stoppingComparisonParentSide r depth)) := by rw [hvfield]
      _ ≤ (G.fixedValue * (d : ℝ≥0∞)) *
            (eLpNorm (hilbertifyVecField u.grad) 2
              (axisCubeNormalizedMeasure (stoppingComparisonParentCorner x r depth)
                (stoppingComparisonParentSide r depth)) +
              eLpNorm (-hilbertifyVecField w.toH1Function.grad) 2
                (axisCubeNormalizedMeasure (stoppingComparisonParentCorner x r depth)
                  (stoppingComparisonParentSide r depth))) := by
            gcongr
            exact axisCubeNormalized_eLpNorm_two_add_le
              (stoppingComparisonParentCorner x r depth)
              (stoppingComparisonParentSide r depth) huU.aestronglyMeasurable
              (by
                rw [axisCubeNormalizedMeasure_eq_smul_volume_restrict _ _ hL]
                exact (memHilbertVectorL2_hilbertifyVecField
                  w.toH1Function.grad_memVectorL2).smul_measure hscale_ne_top |>.neg.aestronglyMeasurable)
      _ ≤ (G.fixedValue * (d : ℝ≥0∞)) *
            (ENNReal.ofReal level + ENNReal.ofReal (eps * level)) := by
            gcongr
            · exact (eLpNorm_congr_ae hfuU).symm ▸ hparent.1
            · simpa only [eLpNorm_neg] using hwbound
      _ ≤ (2 * (G.fixedValue * (d : ℝ≥0∞))) * ENNReal.ofReal level := by
            rw [ENNReal.ofReal_mul heps.le]
            exact oneBall_harmonicGain_scale_le_two
              (A := G.fixedValue * (d : ℝ≥0∞)) (L := ENNReal.ofReal level)
              (e := ENNReal.ofReal eps) (by
                rw [ENNReal.ofReal_le_one]
                exact heps_one)

end CubeCalderonZygmund

end

end Homogenization
