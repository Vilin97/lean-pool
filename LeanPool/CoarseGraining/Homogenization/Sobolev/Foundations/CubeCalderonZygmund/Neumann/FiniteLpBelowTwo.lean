/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.Neumann.EnergyDuality
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.Neumann.FiniteLpAboveTwo
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.FiniteLpBelowTwo

/-!
# Below-two Neumann cube Calderón--Zygmund estimate

This file proves the adjoint-duality branch for a supplied mean-zero Neumann
solution with only `L^p` datum, then combines it with the energy and good-`λ`
branches to cover every finite exponent.
-/

namespace Homogenization

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace CubeCalderonZygmund

private theorem centeredCube_memLp_hilbertMeanZeroGradient_two
    {d : ℕ} {m : ℤ}
    (u : H1MeanZeroFunction (openCubeSet (originCube d m))) :
    MemLp (hilbertifyVecField u.toH1Function.grad) 2
      (centeredCubeDomain d m).normalizedVolume := by
  rw [show (centeredCubeDomain d m).normalizedVolume =
      ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹) •
        volume.restrict (openCubeSet (originCube d m)) by
    change (cubeBoundedMeasurableDomain (originCube d m)).normalizedVolume = _
    rw [cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
      normalizedCubeMeasure, cubeMeasure,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]]
  exact (memHilbertVectorL2_hilbertifyVecField
    u.toH1Function.grad_memVectorL2).smul_measure ENNReal.ofReal_ne_top

/-- The below-two supplied-solution Neumann CZ estimate with `L^p`-only datum. -/
theorem centeredCubeH1MeanZeroNeumannDivergence_cz_lpData_of_lt_two
    (d : ℕ) [NeZero d] (q : FiniteLpExponent)
    (hq : q.exponent.toReal < 2) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ (m : ℤ) (sigma0 : ℝ)
      (h : CubeEuclideanLpField (originCube d m) q)
      (u : H1MeanZeroFunction (openCubeSet (originCube d m))), 0 < sigma0 →
      IsMeanZeroNeumannRhsWeakSolution
        (fun _ : Vec d ↦ scalarMatrix (d := d) sigma0)
        (openCubeSet (originCube d m)) u (fun x ↦ -h.toField x) →
      (centeredCubeDomain d m).normalizedEuclideanLpENorm q.exponent
        u.toH1Function.grad ≤ C * (ENNReal.ofReal sigma0)⁻¹ *
          (centeredCubeDomain d m).normalizedEuclideanLpENorm q.exponent
            h.toField := by
  obtain ⟨C, hCtop, hC⟩ := centeredCubeH1MeanZeroNeumannDivergence_cz_of_two_lt d
    q.conjugate (INTERNAL.conjugate_toReal_gt_two_of_lt_two q hq)
  refine ⟨C, hCtop, ?_⟩
  intro m sigma0 h u hsigma0 hsolution
  let μ : Measure (Vec d) := (centeredCubeDomain d m).normalizedVolume
  let F : Vec d → HilbertVec d := hilbertifyVecField u.toH1Function.grad
  let H : Vec d → HilbertVec d := hilbertifyVecField h.toField
  let : ENNReal.HolderConjugate q.exponent q.conjugate.exponent := q.holderConjugate
  have hqreal : 1 < q.exponent.toReal := by
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal (by norm_num) q.lt_top.ne).mpr q.one_lt
  have hFtwo : MemLp F 2 μ := by
    simpa only [F, μ] using centeredCube_memLp_hilbertMeanZeroGradient_two u
  have hHq : MemLp H q.exponent μ := by
    simpa only [H, μ, centeredCubeDomain,
      cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
      hilbertifyVecField] using! h.euclideanMemLp
  have hFmeas : AEStronglyMeasurable F μ := hFtwo.aestronglyMeasurable
  let A : ℝ≥0∞ := C * (ENNReal.ofReal sigma0)⁻¹ * eLpNorm H q.exponent μ
  have hmain : eLpNorm F q.exponent μ ≤ A := by
    rw [← ENNReal.ofReal_toReal q.lt_top.ne]
    apply INTERNAL.eLpNorm_le_of_truncated_cross_bound hqreal hFmeas
    intro n
    let Gfield := INTERNAL.cubeRadialTruncationL2LpField
      (originCube d m) q u.toH1Function.grad
      (by
        simpa only [volumeMeasureOn, hilbertifyVecField] using!
          (memHilbertVectorL2_hilbertifyVecField
            u.toH1Function.grad_memVectorL2).aestronglyMeasurable) n
    let G : Vec d → Vec d := Gfield.toField
    have hGtwo : MemVectorL2 (openCubeSet (originCube d m)) G := by
      simpa only [G, Gfield] using INTERNAL.cubeRadialTruncation_memVectorL2
        (originCube d m) q u.toH1Function.grad
        (by
          simpa only [volumeMeasureOn, hilbertifyVecField] using!
            (memHilbertVectorL2_hilbertifyVecField
              u.toH1Function.grad_memVectorL2).aestronglyMeasurable) n
    let v := centeredCubeMeanZeroScalarDivergenceSolution m hsigma0 G hGtwo
    have hk : Integrable (fun x => vecDot (u.toH1Function.grad x) (G x)) μ := by
      simpa only [μ] using INTERNAL.centeredCube_integrable_vecDot_of_memVectorL2 m
        u.toH1Function.grad_memVectorL2 hGtwo
    have hk0 : 0 ≤ᵐ[μ] fun x => vecDot (u.toH1Function.grad x) (G x) := by
      filter_upwards with x
      change 0 ≤ vecDot (u.toH1Function.grad x)
        (INTERNAL.vectorRadialTruncation q.exponent.toReal n u.toH1Function.grad x)
      rw [vecDot_comm, INTERNAL.vecDot_vectorRadialTruncation_self hqreal]
      split_ifs with hx
      · exact Real.rpow_nonneg (euclideanNorm_nonneg _) _
      · exact le_rfl
    have hpoint : ∀ᵐ x ∂μ, ENNReal.ofReal
        (vecDot (u.toH1Function.grad x) (G x)) =
          INTERNAL.truncatedMoment q.exponent.toReal n F x := by
      filter_upwards with x
      simpa only [F, G, Gfield] using!
        INTERNAL.ofReal_vecDot_vectorRadialTruncation_eq_truncatedMoment
          hqreal n u.toH1Function.grad x
    have hJ : (∫⁻ x, INTERNAL.truncatedMoment q.exponent.toReal n F x ∂μ) =
        ENNReal.ofReal (∫ x, vecDot (u.toH1Function.grad x) (G x) ∂μ) :=
      INTERNAL.lintegral_truncatedMoment_eq_ofReal_integral hk hk0 hpoint
    refine ⟨?_, ?_⟩
    · rw [hJ]
      exact ENNReal.ofReal_ne_top
    have hvsolution : IsMeanZeroNeumannRhsWeakSolution
        (fun _ : Vec d ↦ scalarMatrix (d := d) sigma0)
        (openCubeSet (originCube d m)) v (fun x ↦ -Gfield.toField x) := by
      simpa only [v, G] using
        centeredCubeMeanZeroScalarDivergenceSolution_isWeakSolution
          m hsigma0 G hGtwo
    have hvbound := hC m sigma0 Gfield v hsigma0 hvsolution
    have hGq : MemLp (hilbertifyVecField G) q.conjugate.exponent μ := by
      simpa only [μ, G, Gfield, centeredCubeDomain,
        cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
        hilbertifyVecField] using! Gfield.euclideanMemLp
    have hVtwo : MemLp (hilbertifyVecField v.toH1Function.grad) 2 μ := by
      simpa only [v, μ] using centeredCube_memLp_hilbertMeanZeroGradient_two v
    have hVbound : eLpNorm (hilbertifyVecField v.toH1Function.grad)
        q.conjugate.exponent μ ≤ C * (ENNReal.ofReal sigma0)⁻¹ *
          eLpNorm (hilbertifyVecField G) q.conjugate.exponent μ := by
      simpa only [BoundedMeasurableDomain.normalizedEuclideanLpENorm,
        BoundedMeasurableDomain.normalizedLpENorm, euclideanNorm_eq_norm_ofVec,
        eLpNorm_norm, μ, v, G, Gfield, hilbertifyVecField] using! hvbound
    have hVq : MemLp (hilbertifyVecField v.toH1Function.grad)
        q.conjugate.exponent μ := by
      refine ⟨hVtwo.aestronglyMeasurable, ?_⟩
      apply lt_of_le_of_lt hVbound
      apply ENNReal.mul_lt_top
      · exact (ENNReal.mul_ne_top hCtop.ne
          (ENNReal.inv_ne_top.mpr (ne_of_gt (ENNReal.ofReal_pos.mpr hsigma0)))).lt_top
      · exact hGq.eLpNorm_lt_top
    have hcross :=
      centeredCubeMeanZeroScalarDivergenceSolution_normalized_cross_pairing
        m hsigma0 u h.toField G hsolution hGtwo
    have hholder := INTERNAL.abs_integral_vecDot_le_eLpNorm_toReal_mul
      (F := h.toField) (G := v.toH1Function.grad) hHq hVq
    have hGmoment : (eLpNorm (hilbertifyVecField G) q.conjugate.exponent μ) ^
        q.conjugate.exponent.toReal =
          ∫⁻ x, INTERNAL.truncatedMoment q.exponent.toReal n F x ∂μ := by
      simpa only [μ, F, G, Gfield, hilbertifyVecField] using!
        INTERNAL.eLpNorm_hilbertRadialTruncation_rpow_conjugate_eq_truncatedMoment q n F
    have hreal : q.exponent.toReal.HolderConjugate q.conjugate.exponent.toReal :=
      ENNReal.HolderConjugate.toReal hqreal
    have hexp : (q.conjugate.exponent.toReal)⁻¹ = 1 - q.exponent.toReal⁻¹ := by
      have hsum := hreal.one_div_add_one_div
      rw [one_div] at hsum
      norm_num at hsum
      linarith
    have hGnorm : eLpNorm (hilbertifyVecField G) q.conjugate.exponent μ =
        (∫⁻ x, INTERNAL.truncatedMoment q.exponent.toReal n F x ∂μ) ^
          (1 - q.exponent.toReal⁻¹) := by
      have hr0 : q.conjugate.exponent.toReal ≠ 0 := by
        exact ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans q.conjugate.one_lt))
          q.conjugate.lt_top.ne |>.ne'
      calc
        eLpNorm (hilbertifyVecField G) q.conjugate.exponent μ =
            (eLpNorm (hilbertifyVecField G) q.conjugate.exponent μ ^
              q.conjugate.exponent.toReal) ^ (q.conjugate.exponent.toReal)⁻¹ := by
              rw [← ENNReal.rpow_mul, mul_inv_cancel₀ hr0, ENNReal.rpow_one]
        _ = (∫⁻ x, INTERNAL.truncatedMoment q.exponent.toReal n F x ∂μ) ^
            (q.conjugate.exponent.toReal)⁻¹ := by rw [hGmoment]
        _ = _ := by rw [hexp]
    calc
      ∫⁻ x, INTERNAL.truncatedMoment q.exponent.toReal n F x ∂μ =
          ENNReal.ofReal (∫ x, vecDot (u.toH1Function.grad x) (G x) ∂μ) := hJ
      _ = ENNReal.ofReal
          (∫ x, vecDot (h.toField x) (v.toH1Function.grad x) ∂μ) := by
            rw [hcross]
      _ ≤ ENNReal.ofReal
          |∫ x, vecDot (h.toField x) (v.toH1Function.grad x) ∂μ| :=
        ENNReal.ofReal_le_ofReal (le_abs_self _)
      _ ≤ ENNReal.ofReal ((eLpNorm H q.exponent μ).toReal *
          (eLpNorm (hilbertifyVecField v.toH1Function.grad)
            q.conjugate.exponent μ).toReal) := ENNReal.ofReal_le_ofReal hholder
      _ = eLpNorm H q.exponent μ *
          eLpNorm (hilbertifyVecField v.toH1Function.grad)
            q.conjugate.exponent μ := by
          rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
            ENNReal.ofReal_toReal hHq.eLpNorm_lt_top.ne,
            ENNReal.ofReal_toReal hVq.eLpNorm_lt_top.ne]
      _ ≤ eLpNorm H q.exponent μ *
          (C * (ENNReal.ofReal sigma0)⁻¹ *
            eLpNorm (hilbertifyVecField G) q.conjugate.exponent μ) := by
          gcongr
      _ = A * (∫⁻ x, INTERNAL.truncatedMoment q.exponent.toReal n F x ∂μ) ^
          (1 - q.exponent.toReal⁻¹) := by
          rw [hGnorm]
          dsimp only [A]
          ac_rfl
  simpa only [BoundedMeasurableDomain.normalizedEuclideanLpENorm,
    BoundedMeasurableDomain.normalizedLpENorm, euclideanNorm_eq_norm_ofVec,
    eLpNorm_norm, F, H, μ, A] using! hmain

/-- The supplied-solution centered-cube Neumann Calderón--Zygmund estimate for
every finite exponent and an `L^p` datum.  No auxiliary `L²` hypothesis is
exposed. -/
theorem centeredCubeH1MeanZeroNeumannDivergence_cz_lpData
    (d : ℕ) [NeZero d] (q : FiniteLpExponent) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ (m : ℤ) (sigma0 : ℝ)
      (h : CubeEuclideanLpField (originCube d m) q)
      (u : H1MeanZeroFunction (openCubeSet (originCube d m))), 0 < sigma0 →
      IsMeanZeroNeumannRhsWeakSolution
        (fun _ : Vec d ↦ scalarMatrix (d := d) sigma0)
        (openCubeSet (originCube d m)) u (fun x ↦ -h.toField x) →
      (centeredCubeDomain d m).normalizedEuclideanLpENorm q.exponent
        u.toH1Function.grad ≤ C * (ENNReal.ofReal sigma0)⁻¹ *
          (centeredCubeDomain d m).normalizedEuclideanLpENorm q.exponent
            h.toField := by
  by_cases hlt : q.exponent.toReal < 2
  · exact centeredCubeH1MeanZeroNeumannDivergence_cz_lpData_of_lt_two d q hlt
  by_cases hgt : 2 < q.exponent.toReal
  · obtain ⟨C, hCtop, hC⟩ :=
      centeredCubeH1MeanZeroNeumannDivergence_cz_of_two_lt d q hgt
    refine ⟨C, hCtop, ?_⟩
    intro m sigma0 h u hsigma0 hsolution
    have htwo_le : (2 : ℝ≥0∞) ≤ q.exponent := by
      apply (ENNReal.toReal_le_toReal (by norm_num) q.lt_top.ne).mp
      simpa only [ENNReal.toReal_ofNat] using hgt.le
    let hL2Lp : CubeEuclideanL2LpField (originCube d m) q :=
      { toCubeEuclideanLpField := h
        euclideanMemL2 := h.euclideanMemLp.mono_exponent htwo_le }
    simpa only [hL2Lp] using hC m sigma0 hL2Lp u hsigma0 hsolution
  have hreal : q.exponent.toReal = 2 :=
    le_antisymm (le_of_not_gt hgt) (le_of_not_gt hlt)
  have hexp : q.exponent = 2 := by
    apply (ENNReal.toReal_eq_toReal_iff' q.lt_top.ne (by norm_num)).mp
    simpa only [ENNReal.toReal_ofNat] using hreal
  have hq : q = FiniteLpExponent.two := by
    cases q
    simp only [FiniteLpExponent.two] at hexp ⊢
    cases hexp
    rfl
  subst q
  refine ⟨1, by norm_num, ?_⟩
  intro m sigma0 h u hsigma0 hsolution
  simpa only [one_mul] using
    centeredCubeH1MeanZeroScalarDivergence_cz_two m sigma0 h u hsigma0 hsolution

end CubeCalderonZygmund

end
end Homogenization
