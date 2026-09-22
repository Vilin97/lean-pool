/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.IntegralLpSeminorm
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.TestSubmodule

/-! # Cutoff Tail -/

namespace Homogenization

open scoped ENNReal Manifold

noncomputable section

private theorem norm_sub_mul_self_le_norm_of_nonneg_of_le_one
    (c v : ℝ) (h0 : 0 ≤ c) (h1 : c ≤ 1) :
    ‖v - c * v‖ ≤ ‖v‖ := by
  calc
    ‖v - c * v‖ = ‖(1 - c) * v‖ := by ring_nf
    _ = ‖(1 - c : ℝ)‖ * ‖v‖ := norm_mul _ _
    _ ≤ 1 * ‖v‖ := by
      gcongr
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      linarith
    _ = ‖v‖ := by simp

private theorem euclideanCoordDeriv_mul_of_contDiff
    {d : ℕ} {φ ψ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (i : Fin d) (x : Vec d) :
    euclideanCoordDeriv i (fun y => φ y * ψ y) x =
      φ x * euclideanCoordDeriv i ψ x + euclideanCoordDeriv i φ x * ψ x := by
  unfold euclideanCoordDeriv
  have hφ_diff : DifferentiableAt ℝ φ x := hφ.differentiable (by simp) x
  have hψ_diff : DifferentiableAt ℝ ψ x := hψ.differentiable (by simp) x
  rw [show (fun y => φ y * ψ y) = φ * ψ by rfl, fderiv_mul hφ_diff hψ_diff]
  simp [smul_eq_mul, mul_comm]

/-- If smooth cutoffs are bounded between `0` and `1` and are eventually equal
to `1` on every compact subset of an open finite-measure domain, then cutting
an `L²` function by them converges back to the original function in `L²`.

This is the measure-regularity part of the cube boundary approximation
argument.  The cube geometry only has to prove the eventual-`1` hypothesis for
the canonical inner cutoffs. -/
theorem tendsto_integralLpSeminorm_sub_mul_of_eventually_eq_one_on_compacts
    {d : ℕ} {U : Set (Vec d)} {g : Vec d → ℝ} {η : ℕ → Vec d → ℝ}
    (hUopen : IsOpen U) (hUfinite : MeasureTheory.volume U ≠ ⊤)
    (hg : MemScalarL2 U g)
    (hη_nonneg : ∀ n x, 0 ≤ η n x)
    (hη_le_one : ∀ n x, η n x ≤ 1)
    (hη_eventually_one :
      ∀ K : Set (Vec d), IsCompact K → K ⊆ U →
        ∀ᶠ n in Filter.atTop, ∀ x ∈ K, η n x = 1) :
    Filter.Tendsto
      (fun n =>
        Gagliardo.integralLpSeminorm (fun x => g x - η n x * g x) 2 (volumeMeasureOn U))
      Filter.atTop (nhds 0) := by
  refine ENNReal.tendsto_nhds_zero.2 ?_
  intro ε hε
  by_cases hε_top : ε = ⊤
  · filter_upwards with n
    rw [hε_top]
    exact le_top
  · have hε_real_pos : 0 < ε.toReal / 2 := by
      have hε_ne_zero : ε ≠ 0 := ne_of_gt hε
      have hε_toReal_pos : 0 < ε.toReal :=
        ENNReal.toReal_pos hε_ne_zero hε_top
      positivity
    obtain ⟨δ, hδpos, hδ⟩ :=
      hg.eLpNorm_indicator_le (p := (2 : ENNReal)) (by norm_num)
        ENNReal.ofNat_ne_top (ENNReal.ofReal_pos.mpr hε_real_pos)
    obtain ⟨K, hKU, hK_compact, hK_closed, hμK⟩ :=
      hUopen.measurableSet.exists_isCompact_isClosed_sdiff_lt
        (μ := MeasureTheory.volume) hUfinite
        hδpos.ne'
    have hsmall : volumeMeasureOn U (U \ K) ≤ δ := by
      unfold volumeMeasureOn
      rw [MeasureTheory.Measure.restrict_apply
        (hUopen.measurableSet.diff hK_closed.measurableSet)]
      simpa [Set.inter_eq_self_of_subset_left (Set.sdiff_subset : U \ K ⊆ U)]
        using hμK.le
    have htail :=
      hδ (U \ K) (hUopen.measurableSet.diff hK_closed.measurableSet) hsmall
    have hε_bound : ENNReal.ofReal (ε.toReal / 2) ≤ ε := by
      have hhalf_le : ε.toReal / 2 ≤ ε.toReal := by
        linarith [(ENNReal.toReal_nonneg : 0 ≤ ε.toReal)]
      exact (ENNReal.ofReal_le_iff_le_toReal hε_top).2 hhalf_le
    filter_upwards [hη_eventually_one K hK_compact hKU] with n hn
    calc
      Gagliardo.integralLpSeminorm (fun x => g x - η n x * g x) 2 (volumeMeasureOn U)
          ≤ Gagliardo.integralLpSeminorm ((U \ K).indicator g) 2 (volumeMeasureOn U) := by
            simp only [Gagliardo.integralLpSeminorm,
              show (2 : ℝ≥0∞) ≠ 0 by norm_num, show (2 : ℝ≥0∞) ≠ ∞ by norm_num,
              if_false, ENNReal.toReal_ofNat]
            apply MeasureTheory.eLpNorm'_mono_ae (by norm_num)
            have hmem : ∀ᵐ x ∂ volumeMeasureOn U, x ∈ U := by
              simpa [volumeMeasureOn] using
                MeasureTheory.ae_restrict_mem hUopen.measurableSet
            filter_upwards [hmem] with x hxU
            by_cases hxK : x ∈ K
            · have hηx : η n x = 1 := hn x hxK
              simp [hηx, hxK]
            · have hxDiff : x ∈ U \ K := ⟨hxU, hxK⟩
              rw [Set.indicator_of_mem hxDiff]
              exact
                norm_sub_mul_self_le_norm_of_nonneg_of_le_one
                  (η n x) (g x) (hη_nonneg n x) (hη_le_one n x)
      _ ≤ MeasureTheory.eLpNorm ((U \ K).indicator g) 2 (volumeMeasureOn U) :=
        Gagliardo.integralLpSeminorm_le_eLpNorm _ _ _
      _ ≤ ENNReal.ofReal (ε.toReal / 2) := htail
      _ ≤ ε := hε_bound


/-- Measurable cutoffs satisfy the same convergence statement for Mathlib’s norm. -/
theorem tendsto_eLpNorm_sub_mul_of_eventually_eq_one_on_compacts
    {d : ℕ} {U : Set (Vec d)} {g : Vec d → ℝ} {η : ℕ → Vec d → ℝ}
    (hUopen : IsOpen U) (hUfinite : MeasureTheory.volume U ≠ ⊤)
    (hg : MemScalarL2 U g)
    (hη_nonneg : ∀ n x, 0 ≤ η n x)
    (hη_le_one : ∀ n x, η n x ≤ 1)
    (hη_eventually_one :
      ∀ K : Set (Vec d), IsCompact K → K ⊆ U →
        ∀ᶠ n in Filter.atTop, ∀ x ∈ K, η n x = 1)
    (hη : ∀ n, MeasureTheory.AEStronglyMeasurable (η n) (volumeMeasureOn U)) :
    Filter.Tendsto
      (fun n =>
        MeasureTheory.eLpNorm (fun x => g x - η n x * g x) 2 (volumeMeasureOn U))
      Filter.atTop (nhds 0) := by
  have hraw := tendsto_integralLpSeminorm_sub_mul_of_eventually_eq_one_on_compacts
    hUopen hUfinite hg hη_nonneg hη_le_one hη_eventually_one
  have heq : (fun n => Gagliardo.integralLpSeminorm
      (fun x => g x - η n x * g x) 2 (volumeMeasureOn U)) =
      (fun n => MeasureTheory.eLpNorm
        (fun x => g x - η n x * g x) 2 (volumeMeasureOn U)) := by
    funext n
    exact Gagliardo.integralLpSeminorm_eq_eLpNorm _ _ _
      (hg.aestronglyMeasurable.sub ((hη n).mul hg.aestronglyMeasurable))
  rwa [heq] at hraw

/-- A compact subset of an open triadic cube is contained in a strictly smaller
concentric closed cube. -/
theorem IsCompact.exists_lt_one_subset_scaledClosedCubeSet_of_subset_openCubeSet
    {d : ℕ} {Q : TriadicCube d} {K : Set (Vec d)}
    (hK : IsCompact K) (hKU : K ⊆ openCubeSet Q) :
    ∃ ρ : ℝ, ρ < 1 ∧ K ⊆ scaledClosedCubeSet Q ρ := by
  by_cases hKempty : K = ∅
  · refine ⟨0, zero_lt_one, ?_⟩
    simp [hKempty]
  · have hKne : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hKempty
    let imageDist : Set ℝ := (fun x : Vec d => dist x (cubeCenter Q)) '' K
    have hDistCont : Continuous fun x : Vec d => dist x (cubeCenter Q) :=
      continuous_id.dist continuous_const
    let M : ℝ :=
      Classical.choose
        ((hK.image hDistCont).exists_isGreatest
          (by
            rcases hKne with ⟨x, hx⟩
            exact ⟨dist x (cubeCenter Q), ⟨x, hx, rfl⟩⟩))
    have hM_mem : M ∈ imageDist :=
      (Classical.choose_spec
        ((hK.image hDistCont).exists_isGreatest
          (by
            rcases hKne with ⟨x, hx⟩
            exact ⟨dist x (cubeCenter Q), ⟨x, hx, rfl⟩⟩))).1
    have hM_ge : ∀ y ∈ imageDist, y ≤ M :=
      (Classical.choose_spec
        ((hK.image hDistCont).exists_isGreatest
          (by
            rcases hKne with ⟨x, hx⟩
            exact ⟨dist x (cubeCenter Q), ⟨x, hx, rfl⟩⟩))).2
    rcases hM_mem with ⟨x₀, hx₀K, hx₀M⟩
    have hM_nonneg : 0 ≤ M := by
      rw [← hx₀M]
      exact dist_nonneg
    have hM_lt : M < cubeRadius Q := by
      have hx₀_open : x₀ ∈ Metric.ball (cubeCenter Q) (cubeRadius Q) := by
        simpa [ball_cubeCenter_eq_openCubeSet] using hKU hx₀K
      have hx₀_dist : dist x₀ (cubeCenter Q) < cubeRadius Q := by
        simpa [Metric.mem_ball, dist_comm] using hx₀_open
      simpa [← hx₀M] using hx₀_dist
    refine ⟨M / cubeRadius Q, ?_, ?_⟩
    · have hrad : 0 < cubeRadius Q := cubeRadius_pos Q
      rw [div_lt_one hrad]
      exact hM_lt
    · intro x hxK i
      have hxM : dist x (cubeCenter Q) ≤ M :=
        hM_ge (dist x (cubeCenter Q)) ⟨x, hxK, rfl⟩
      have hcoord : dist (x i) (cubeCenter Q i) ≤ M :=
        (dist_pi_le_iff hM_nonneg).1 hxM i
      have hscale : M / cubeRadius Q * cubeRadius Q = M := by
        field_simp [(ne_of_gt (cubeRadius_pos Q))]
      simpa [scaledClosedCubeSet, Real.dist_eq, abs_sub_comm, hscale] using hcoord

/-- If inner radii tend to `1`, they eventually contain any compact subset of
the open cube. -/
theorem eventually_subset_scaledClosedCubeSet_of_tendsto_one
    {d : ℕ} {Q : TriadicCube d} {K : Set (Vec d)} {ρ : ℕ → ℝ}
    (hρ : Filter.Tendsto ρ Filter.atTop (nhds 1))
    (hK : IsCompact K) (hKU : K ⊆ openCubeSet Q) :
    ∀ᶠ n in Filter.atTop, K ⊆ scaledClosedCubeSet Q (ρ n) := by
  rcases IsCompact.exists_lt_one_subset_scaledClosedCubeSet_of_subset_openCubeSet hK hKU with
    ⟨σ, hσ_lt_one, hKσ⟩
  have hσ_eventually : ∀ᶠ n in Filter.atTop, σ < ρ n :=
    hρ.eventually (isOpen_Ioi.mem_nhds hσ_lt_one)
  filter_upwards [hσ_eventually] with n hn x hx
  exact scaledClosedCubeSet_mono Q (le_of_lt hn) (hKσ hx)

namespace QuantitativeCubeCutoff

/-- Quantitative cube cutoffs whose inner radius tends to one are eventually
identically `1` on each compact subset of the open cube. -/
theorem eventually_eq_one_on_compacts_of_tendsto_inner
    {d : ℕ} {Q : TriadicCube d} {ρ₁ ρ₂ : ℕ → ℝ}
    (η : ∀ n, QuantitativeCubeCutoff Q (ρ₁ n) (ρ₂ n))
    (hρ₁ : Filter.Tendsto ρ₁ Filter.atTop (nhds 1))
    (K : Set (Vec d)) (hK : IsCompact K) (hKU : K ⊆ openCubeSet Q) :
    ∀ᶠ n in Filter.atTop, ∀ x ∈ K, η n x = 1 := by
  filter_upwards
    [eventually_subset_scaledClosedCubeSet_of_tendsto_one
      (Q := Q) (K := K) hρ₁ hK hKU] with n hn x hx
  exact (η n).eq_one_on_inner x (hn hx)

/-- Cutting an `L²` function by quantitative cube cutoffs whose inner radii
tend to one converges back to the function in `L²(openCubeSet Q)`. -/
theorem tendsto_eLpNorm_sub_mul_of_tendsto_inner
    {d : ℕ} {Q : TriadicCube d} {g : Vec d → ℝ} {ρ₁ ρ₂ : ℕ → ℝ}
    (η : ∀ n, QuantitativeCubeCutoff Q (ρ₁ n) (ρ₂ n))
    (hρ₁ : Filter.Tendsto ρ₁ Filter.atTop (nhds 1))
    (hg : MemScalarL2 (openCubeSet Q) g) :
    Filter.Tendsto
      (fun n =>
        MeasureTheory.eLpNorm (fun x => g x - η n x * g x) 2
          (volumeMeasureOn (openCubeSet Q)))
      Filter.atTop (nhds 0) := by
  exact
    tendsto_eLpNorm_sub_mul_of_eventually_eq_one_on_compacts
      (U := openCubeSet Q) (g := g) (η := fun n x => η n x)
      (isOpen_openCubeSet Q) (volume_openCubeSet_lt_top Q).ne hg
      (fun n x => (η n).nonneg x)
      (fun n x => (η n).le_one x)
      (eventually_eq_one_on_compacts_of_tendsto_inner η hρ₁)
      (fun n => (η n).smooth.continuous.aestronglyMeasurable)

end QuantitativeCubeCutoff

namespace QuantitativeCubeCutoff

/-- Product-rule derivative convergence for cutoff tests, with the genuinely
hard face term isolated as the boundary-error hypothesis. -/
theorem tendsto_eLpNorm_euclideanCoordDeriv_mul_sub_of_tendsto_inner_of_boundary_error
    {d : ℕ} {Q : TriadicCube d} {ψ : Vec d → ℝ} {ρ₁ ρ₂ : ℕ → ℝ}
    (η : ∀ n, QuantitativeCubeCutoff Q (ρ₁ n) (ρ₂ n))
    (hρ₁ : Filter.Tendsto ρ₁ Filter.atTop (nhds 1))
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_compact : HasCompactSupport ψ) (i : Fin d)
    (hboundary :
      Filter.Tendsto
        (fun n =>
          MeasureTheory.eLpNorm
            (fun x => euclideanCoordDeriv i (η n : Vec d → ℝ) x * ψ x) 2
            (volumeMeasureOn (openCubeSet Q)))
        Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n =>
        MeasureTheory.eLpNorm
          (fun x =>
            euclideanCoordDeriv i (fun y => η n y * ψ y) x -
              euclideanCoordDeriv i ψ x)
          2 (volumeMeasureOn (openCubeSet Q)))
      Filter.atTop (nhds 0) := by
  let U : Set (Vec d) := openCubeSet Q
  let Dψ : Vec d → ℝ := euclideanCoordDeriv i ψ
  let B : ℕ → Vec d → ℝ := fun n x =>
    euclideanCoordDeriv i (η n : Vec d → ℝ) x * ψ x
  have hDψ_mem : MemScalarL2 U Dψ := by
    simpa [U, Dψ, MemScalarL2, volumeMeasureOn] using
      ((contDiff_euclideanCoordDeriv hψ i).continuous.memLp_of_hasCompactSupport
        (hasCompactSupport_euclideanCoordDeriv hψ_compact i)).restrict U
  have hηDψ_mem : ∀ n, MemScalarL2 U (fun x => η n x * Dψ x) := by
    intro n
    have hcont :
        Continuous (fun x => η n x * Dψ x) :=
      (η n).smooth.continuous.mul (contDiff_euclideanCoordDeriv hψ i).continuous
    have hcomp :
        HasCompactSupport (fun x => η n x * Dψ x) := by
      simpa [Dψ] using! ((η n).hasCompactSupport.mul_right :
        HasCompactSupport (fun x => (η n : Vec d → ℝ) x * euclideanCoordDeriv i ψ x))
    simpa [U, MemScalarL2, volumeMeasureOn] using
      (hcont.memLp_of_hasCompactSupport hcomp).restrict U
  have hB_mem : ∀ n, MemScalarL2 U (B n) := by
    intro n
    have hDη_cont :
        Continuous (fun x => euclideanCoordDeriv i (η n : Vec d → ℝ) x) :=
      (contDiff_euclideanCoordDeriv (η n).smooth i).continuous
    have hcont : Continuous (B n) := by
      simpa [B] using! hDη_cont.mul hψ.continuous
    have hDη_comp :
        HasCompactSupport (fun x => euclideanCoordDeriv i (η n : Vec d → ℝ) x) :=
      hasCompactSupport_euclideanCoordDeriv (η n).hasCompactSupport i
    have hcomp : HasCompactSupport (B n) := by
      simpa [B] using! (hDη_comp.mul_right :
        HasCompactSupport
          (fun x => euclideanCoordDeriv i (η n : Vec d → ℝ) x * ψ x))
    simpa [U, MemScalarL2, volumeMeasureOn] using
      (hcont.memLp_of_hasCompactSupport hcomp).restrict U
  have htail :
      Filter.Tendsto
        (fun n =>
          MeasureTheory.eLpNorm (fun x => Dψ x - η n x * Dψ x) 2
            (volumeMeasureOn U))
        Filter.atTop (nhds 0) :=
    tendsto_eLpNorm_sub_mul_of_tendsto_inner η hρ₁ hDψ_mem
  have hbound :
      ∀ n,
        MeasureTheory.eLpNorm
            (fun x =>
              euclideanCoordDeriv i (fun y => η n y * ψ y) x -
                euclideanCoordDeriv i ψ x)
            2 (volumeMeasureOn U) ≤
          MeasureTheory.eLpNorm (fun x => Dψ x - η n x * Dψ x) 2
              (volumeMeasureOn U) +
            MeasureTheory.eLpNorm (B n) 2 (volumeMeasureOn U) := by
    intro n
    have hfun :
        (fun x =>
            euclideanCoordDeriv i (fun y => η n y * ψ y) x -
              euclideanCoordDeriv i ψ x) =
          fun x => -(Dψ x - η n x * Dψ x) + B n x := by
      funext x
      rw [euclideanCoordDeriv_mul_of_contDiff (η n).smooth hψ i x]
      simp [Dψ, B]
      ring
    rw [hfun]
    calc
      MeasureTheory.eLpNorm (fun x => -(Dψ x - η n x * Dψ x) + B n x)
          2 (volumeMeasureOn U)
          ≤ MeasureTheory.eLpNorm (fun x => -(Dψ x - η n x * Dψ x)) 2
                (volumeMeasureOn U) +
              MeasureTheory.eLpNorm (B n) 2 (volumeMeasureOn U) := by
            exact MeasureTheory.eLpNorm_add_le (by norm_num : (1 : ENNReal) ≤ 2)
      _ = MeasureTheory.eLpNorm (fun x => Dψ x - η n x * Dψ x) 2
                (volumeMeasureOn U) +
              MeasureTheory.eLpNorm (B n) 2 (volumeMeasureOn U) := by
            have hneg :
                MeasureTheory.eLpNorm (fun x => -(Dψ x - η n x * Dψ x)) 2
                    (volumeMeasureOn U) =
                  MeasureTheory.eLpNorm (fun x => Dψ x - η n x * Dψ x) 2
                    (volumeMeasureOn U) := by
              change
                MeasureTheory.eLpNorm (-(fun x => Dψ x - η n x * Dψ x)) 2
                    (volumeMeasureOn U) =
                  MeasureTheory.eLpNorm (fun x => Dψ x - η n x * Dψ x) 2
                    (volumeMeasureOn U)
              exact
                MeasureTheory.eLpNorm_neg
                  (fun x => Dψ x - η n x * Dψ x)
                  (2 : ENNReal) (volumeMeasureOn U)
            rw [hneg]
  have hsum :
      Filter.Tendsto
        (fun n =>
          MeasureTheory.eLpNorm (fun x => Dψ x - η n x * Dψ x) 2
              (volumeMeasureOn U) +
            MeasureTheory.eLpNorm (B n) 2 (volumeMeasureOn U))
        Filter.atTop (nhds 0) := by
    have hboundary' :
        Filter.Tendsto
          (fun n => MeasureTheory.eLpNorm (B n) 2 (volumeMeasureOn U))
          Filter.atTop (nhds 0) := by
      simpa [B, U] using hboundary
    simpa using htail.add hboundary'
  refine Filter.Tendsto.squeeze tendsto_const_nhds hsum (fun n => ?_) hbound
  exact bot_le

end QuantitativeCubeCutoff

end

end Homogenization
