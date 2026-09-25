/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Probability.RegCoeffField.SliceMeasurability
public import LeanPool.CoarseGraining.Homogenization.Probability.RegCoeffField.SmoothSigma
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Smooth-local measurability of quantitative ellipticity slices

For compact rational balls in an open cube, smooth cutoffs supported in the
cube approximate the ball indicator.  Dominated convergence then transfers the
ball-average presentation of the quantitative ellipticity slice to the smooth
local sigma algebra.
-/

@[expose] public section

namespace Homogenization

open MeasureTheory Metric Filter Topology
open scoped Manifold

noncomputable section

variable {d : ℕ}

private theorem exists_smooth_cutoff_seq {U B : Set (Vec d)}
    (hUopen : IsOpen U) (hBcpt : IsCompact B) (hBU : B ⊆ U) :
    ∃ K : Set (Vec d), ∃ ψ : ℕ → Vec d → ℝ,
      IsCompact K ∧ K ⊆ U ∧
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (ψ n) ∧ HasCompactSupport (ψ n) ∧
        tsupport (ψ n) ⊆ U ∧ Function.support (ψ n) ⊆ K ∧
          ∀ x, ψ n x ∈ Set.Icc 0 1) ∧
      ∀ x, Tendsto (fun n => ψ n x) atTop
        (𝓝 (Set.indicator B (fun _ => (1 : ℝ)) x)) := by
  classical
  obtain ⟨ε, hεpos, hεU⟩ := hBcpt.exists_cthickening_subset_open hUopen hBU
  let δ : ℕ → ℝ := fun n => ε / (n + 1)
  have hδpos : ∀ n, 0 < δ n := fun n => by
    dsimp [δ]
    positivity
  have hδle : ∀ n, δ n ≤ ε := fun n => by
    dsimp [δ]
    have hn : 1 ≤ (n : ℝ) + 1 := by
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
      linarith
    calc
      ε / ((n : ℝ) + 1) ≤ ε / 1 := by
        exact div_le_div_of_nonneg_left hεpos.le (by positivity) hn
      _ = ε := by rw [div_one]
  have hBint : ∀ n, B ⊆ interior (cthickening (δ n) B) := fun n =>
    (self_subset_thickening (hδpos n) B).trans
      (thickening_subset_interior_cthickening (δ n) B)
  choose ψ hψone hψzero hψrange using fun n =>
    exists_contMDiffMap_one_nhds_of_subset_interior (I := 𝓘(ℝ, Vec d)) (n := (⊤ : ℕ∞))
      hBcpt.isClosed (hBint n)
  let ψ' : ℕ → Vec d → ℝ := fun n => ψ n
  let K : Set (Vec d) := cthickening ε B
  refine ⟨K, ψ', hBcpt.cthickening, hεU, ?_, ?_⟩
  · intro n
    have hTsub : cthickening (δ n) B ⊆ K :=
      cthickening_mono (hδle n) B
    have hsupp : Function.support (ψ' n) ⊆ cthickening (δ n) B := by
      intro x hx
      by_contra hxT
      exact hx (hψzero n x hxT)
    have hcompact : HasCompactSupport (ψ' n) :=
      HasCompactSupport.of_support_subset_isCompact (hBcpt.cthickening) hsupp
    have htsupp : tsupport (ψ' n) ⊆ U := by
      have htsuppT : tsupport (ψ' n) ⊆ cthickening (δ n) B := by
        simpa [tsupport] using closure_minimal hsupp isClosed_cthickening
      exact htsuppT.trans (hTsub.trans hεU)
    exact ⟨(ψ n).contMDiff.contDiff, hcompact, htsupp, hsupp.trans hTsub, hψrange n⟩
  · intro x
    by_cases hx : x ∈ B
    · have hone : ∀ n, ψ' n x = 1 := fun n =>
        hψone n |>.self_of_nhdsSet x hx
      rw [show Set.indicator B (fun _ => (1 : ℝ)) x = 1 by simp [hx]]
      simp_rw [hone]
      exact tendsto_const_nhds
    · have hxcl : x ∉ closure B := by simpa [hBcpt.isClosed.closure_eq] using hx
      obtain ⟨ρ, ⟨hρpos, hρlt⟩⟩ :=
        Metric.exists_real_pos_lt_infEDist_of_notMem_closure hxcl
      have hδtend : Tendsto δ atTop (𝓝 0) := by
        simpa only [δ, div_eq_mul_inv, one_mul, mul_zero] using
          (tendsto_const_nhds.mul tendsto_one_div_add_atTop_nhds_zero_nat :
            Tendsto (fun n : ℕ => ε * (1 / ((n : ℝ) + 1))) atTop (𝓝 (ε * 0)))
      have hsmall : ∀ᶠ n in atTop, δ n < ρ := by
        rw [Metric.tendsto_nhds] at hδtend
        specialize hδtend ρ hρpos
        filter_upwards [hδtend] with n hn
        simpa only [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (hδpos n).le] using hn
      rw [show Set.indicator B (fun _ => (1 : ℝ)) x = 0 by simp [hx]]
      rcases (eventually_atTop.1 hsmall) with ⟨N, hN⟩
      apply tendsto_atTop_of_eventually_const (i₀ := N)
      intro n hn
      apply hψzero n x
      intro hxt
      rw [mem_cthickening_iff] at hxt
      have hδρ : ENNReal.ofReal (δ n) < ENNReal.ofReal ρ :=
        ENNReal.ofReal_lt_ofReal_iff hρpos |>.mpr (hN n hn)
      exact (not_le_of_gt (hδρ.trans hρlt)) hxt

private theorem exists_smooth_entryTestR_approximation {U B : Set (Vec d)}
    (hUopen : IsOpen U) (hBcpt : IsCompact B) (hBU : B ⊆ U) :
    ∃ ψ : ℕ → Vec d → ℝ,
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (ψ n) ∧ HasCompactSupport (ψ n) ∧
        tsupport (ψ n) ⊆ U) ∧
      ∀ (i j : Fin d) (a : RegCoeffField d),
        Tendsto (fun n => entryTestR i j (ψ n) a) atTop
          (𝓝 (entryTestR i j (Set.indicator B (fun _ => (1 : ℝ))) a)) := by
  obtain ⟨K, ψ, hKcpt, hKU, hψ, hlim⟩ :=
    exists_smooth_cutoff_seq hUopen hBcpt hBU
  refine ⟨ψ, fun n => ⟨(hψ n).1, (hψ n).2.1, (hψ n).2.2.1⟩, ?_⟩
  intro i j a
  have hbound_integrable : Integrable (K.indicator fun x => |a x i j|) volume := by
    rw [integrable_indicator_iff hKcpt.measurableSet]
    simpa only [Real.norm_eq_abs] using!
      ((a.entry_locInt i j).integrableOn_isCompact hKcpt).norm
  have hF_measurable : ∀ n, AEStronglyMeasurable (fun x => a x i j * ψ n x) volume := by
    intro n
    exact ((a.entry_measurable i j).mul (hψ n).1.continuous.measurable).aestronglyMeasurable
  have hF_bound : ∀ n, ∀ᵐ x ∂volume,
      ‖a x i j * ψ n x‖ ≤ K.indicator (fun x => |a x i j|) x := by
    intro n
    filter_upwards with x
    by_cases hxK : x ∈ K
    · rw [Set.indicator_of_mem hxK, norm_mul, Real.norm_eq_abs]
      have hψ01 := (hψ n).2.2.2.2 x
      rw [Real.norm_eq_abs, abs_of_nonneg hψ01.1]
      exact mul_le_of_le_one_right (abs_nonneg _) hψ01.2
    · rw [Set.indicator_of_notMem hxK]
      have hxSupp : x ∉ Function.support (ψ n) := fun hx => hxK ((hψ n).2.2.2.1 hx)
      have hzero : ψ n x = 0 := by
        simpa only [Function.mem_support, not_not] using hxSupp
      simp [hzero]
  have hF_lim : ∀ᵐ x ∂volume,
      Tendsto (fun n => a x i j * ψ n x) atTop
        (𝓝 (a x i j * Set.indicator B (fun _ => (1 : ℝ)) x)) :=
    Filter.Eventually.of_forall fun x => tendsto_const_nhds.mul (hlim x)
  simpa only [entryTestR] using
    tendsto_integral_of_dominated_convergence (K.indicator fun x => |a x i j|)
      hF_measurable hbound_integrable hF_bound hF_lim

private theorem measurable_entryTestR_smoothLocalSigmaR {U : Set (Vec d)}
    (i j : Fin d) {φ : Vec d → ℝ} (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ) (hφ_support : tsupport φ ⊆ U) :
    @Measurable (RegCoeffField d) ℝ (SmoothLocalSigmaR U) _ (entryTestR i j φ) := by
  intro t ht
  exact MeasurableSpace.measurableSet_generateFrom
    ⟨i, j, φ, hφ_smooth, hφ_compact, hφ_support, t, ht, rfl⟩

private theorem measurable_avgMat_smoothLocalSigmaR {U B : Set (Vec d)}
    (hUopen : IsOpen U) (hBcpt : IsCompact B) (hBU : B ⊆ U) :
    @Measurable (RegCoeffField d) (Mat d) (SmoothLocalSigmaR U) _ (avgMat B) := by
  let : MeasurableSpace (RegCoeffField d) := SmoothLocalSigmaR U
  obtain ⟨ψ, hψ, hlim⟩ := exists_smooth_entryTestR_approximation hUopen hBcpt hBU
  refine @measurable_matrix_of_entries d (RegCoeffField d) (SmoothLocalSigmaR U) (avgMat B) ?_
  intro i j
  have hmeas : ∀ n, @Measurable (RegCoeffField d) ℝ (SmoothLocalSigmaR U) _
      (entryTestR i j (ψ n)) := fun n =>
    measurable_entryTestR_smoothLocalSigmaR i j (hψ n).1 (hψ n).2.1 (hψ n).2.2
  have htend : Tendsto (fun n => entryTestR i j (ψ n)) atTop
      (𝓝 (entryTestR i j (Set.indicator B (fun _ => (1 : ℝ)))) ) := by
    rw [tendsto_pi_nhds]
    intro a
    exact hlim i j a
  have hindicator : @Measurable (RegCoeffField d) ℝ (SmoothLocalSigmaR U) _
      (entryTestR i j (Set.indicator B (fun _ => (1 : ℝ)))) :=
    measurable_of_tendsto_metrizable hmeas htend
  have heq : (fun a : RegCoeffField d => avgMat B a i j)
      = fun a => (volume B).toReal⁻¹ • entryTestR i j (Set.indicator B (fun _ => (1 : ℝ))) a := by
    funext a
    exact avgMat_entry_eq_smul_entryTestR i j B hBcpt.measurableSet a
  rw [heq]
  exact hindicator.const_smul ((volume B).toReal⁻¹)

private theorem measurableSet_slicePart_smoothLocalSigmaR {U : Set (Vec d)}
    (hUopen : IsOpen U) (lam Lam : ℝ) :
    MeasurableSet[SmoothLocalSigmaR U] (slicePart U lam Lam) := by
  refine MeasurableSet.iInter (fun q => ?_)
  refine MeasurableSet.iInter (fun r => ?_)
  refine MeasurableSet.iInter (fun hpos => ?_)
  refine MeasurableSet.iInter (fun hsub => ?_)
  have hBcpt : IsCompact (closedBall (ratPt q) (r : ℝ)) := isCompact_closedBall _ _
  have hpre :
      {a : RegCoeffField d | IsEllipticMatrix lam Lam (avgMat (closedBall (ratPt q) (r : ℝ)) a)}
        = (avgMat (closedBall (ratPt q) (r : ℝ))) ⁻¹' {A : Mat d | IsEllipticMatrix lam Lam A} :=
    rfl
  rw [hpre]
  exact (measurable_avgMat_smoothLocalSigmaR hUopen hBcpt hsub)
    measurableSet_isEllipticMatrix

/-- The AEE quantitative ellipticity slice of a triadic cube is measurable for
the smooth support-local integral sigma algebra. -/
theorem measurableSet_smoothLocalSigmaR_aeeSlice (Q : TriadicCube d) (k : ℕ) :
    MeasurableSet[SmoothLocalSigmaR (cubeSet Q)]
      {a : RegCoeffField d | AEEQuantitativeEllipticSlice (cubeSet Q) k a.toFun} := by
  set lam : ℝ := (k + 1 : ℝ)⁻¹
  set Lam : ℝ := (k + 1 : ℝ)
  have hEvent :
      {a : RegCoeffField d | AEEQuantitativeEllipticSlice (cubeSet Q) k a.toFun}
        = {a : RegCoeffField d |
            ∀ᵐ x ∂(volume.restrict (openCubeSet Q)), IsEllipticMatrix lam Lam (a x)} := by
    ext a
    simp only [Set.mem_ofPred_eq]
    rw [aeeQuantitativeEllipticSlice_carrier_iff (cubeSet Q) (measurableSet_cubeSet Q) k a]
    show (∀ᵐ x ∂(volume.restrict (cubeSet Q)), IsEllipticMatrix lam Lam (a x)) ↔ _
    exact ae_restrict_cubeSet_iff
  rw [hEvent, setOf_aeRestrict_isEllipticMatrix_eq_slicePart (isOpen_openCubeSet Q) lam Lam]
  exact smoothLocalSigmaR_mono (openCubeSet_subset_cubeSet Q) _
    (measurableSet_slicePart_smoothLocalSigmaR (isOpen_openCubeSet Q) lam Lam)

end

end Homogenization
