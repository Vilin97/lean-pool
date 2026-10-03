/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.HmPairingPrefix
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.ScalarQuadraticL2
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.LeadingErrorHEuclid
public import Mathlib.MeasureTheory.Integral.Prod

/-! Fubini converts a spacetime scalar L² bound into the time-L² datum of
the spatial slice norm used by the pairing prefix estimates. -/

@[expose] public section

noncomputable section

open MeasureTheory Set Homogenization

namespace AVenhance.Infra.Section4

/-- On the open time-space cell, the spacetime square integral is the time
integral of the spatial `L²` energy. Consequently its bound supplies the
time-L² data for the prefix Cauchy estimates. -/
theorem hm_time_slice_l2_data_of_spacetime_square
    {G : ℝ → Vec 2 → ℝ} {Q : ℝ}
    (hGsqInt : Integrable
      (fun z : ℝ × Vec 2 => G z.1 z.2 ^ 2)
      (volume.restrict AVenhance.timeCube))
    (hGsqBound : ∫ z in AVenhance.timeCube, G z.1 z.2 ^ 2 ≤ Q ^ 2) :
    MemLp (fun t => Real.sqrt (AVenhance.l2NormSq (G t))) 2
        (volume.restrict (Set.Ioc (0 : ℝ) 1)) ∧
      (∫ t in Set.Ioc (0 : ℝ) 1,
        (Real.sqrt (AVenhance.l2NormSq (G t))) ^ 2 ≤ Q ^ 2) ∧
      Integrable (fun t => Real.sqrt (AVenhance.l2NormSq (G t)))
        (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  let μ : Measure ℝ := volume.restrict (Set.Ioo (0 : ℝ) 1)
  let ν : Measure (Vec 2) := volume.restrict AVenhance.unitCube
  have htime : μ = volume.restrict (Set.Ioc (0 : ℝ) 1) := by
    dsimp [μ]
    exact Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Ioc
  have hprod : μ.prod ν =
      (volume : Measure (ℝ × Vec 2)).restrict AVenhance.timeCube := by
    dsimp [μ, ν]
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod ℝ (Vec 2)]
    rfl
  have hGprod : Integrable (fun z : ℝ × Vec 2 => G z.1 z.2 ^ 2) (μ.prod ν) := by
    rw [hprod]
    exact hGsqInt
  have hFubini := MeasureTheory.integral_prod
    (fun z : ℝ × Vec 2 => G z.1 z.2 ^ 2) hGprod
  have hinner : (fun t : ℝ =>
      ∫ x, G t x ^ 2 ∂ν) = fun t => AVenhance.l2NormSq (G t) := by
    funext t
    rfl
  have hglobal :
      (∫ z in AVenhance.timeCube, G z.1 z.2 ^ 2) =
        ∫ t in Set.Ioc (0 : ℝ) 1, AVenhance.l2NormSq (G t) := by
    calc
      _ = ∫ z, G z.1 z.2 ^ 2 ∂(μ.prod ν) := by rw [hprod]
      _ = ∫ t, (∫ x, G t x ^ 2 ∂ν) ∂μ := hFubini
      _ = ∫ t, AVenhance.l2NormSq (G t) ∂μ := by rw [hinner]
      _ = ∫ t in Set.Ioc (0 : ℝ) 1, AVenhance.l2NormSq (G t) := by
        rw [htime]
  have hEnergyInt : Integrable
      (fun t => AVenhance.l2NormSq (G t))
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    rw [← htime, ← hinner]
    exact hGprod.integral_prod_left
  have hEnergy :
      (∫ t in Set.Ioc (0 : ℝ) 1, AVenhance.l2NormSq (G t)) ≤ Q ^ 2 := by
    calc
      _ = ∫ z in AVenhance.timeCube, G z.1 z.2 ^ 2 := hglobal.symm
      _ ≤ Q ^ 2 := hGsqBound
  have hNormMeas : AEStronglyMeasurable
      (fun t => Real.sqrt (AVenhance.l2NormSq (G t)))
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    have hEnergyMeas := hEnergyInt.aemeasurable
    exact hEnergyMeas.sqrt.aestronglyMeasurable
  exact hm_time_slice_l2_data_of_spatial_energy hNormMeas hEnergyInt hEnergy

/-- A spacetime scalar `eLpNorm` estimate supplies the full time-slice
`L²` datum, with the same amplitude. Measurability is the only separate
input; in the source it follows from the coefficient and gradient
entry measurability. -/
theorem hm_time_slice_l2_data_of_spacetime_eLpNorm
    {G : ℝ → Vec 2 → ℝ} {Q : ℝ}
    (hGmeas : AEStronglyMeasurable
      (fun z : ℝ × Vec 2 => G z.1 z.2)
      (volume.restrict AVenhance.timeCube))
    (hQ : 0 ≤ Q)
    (hGbound : eLpNorm (fun z : ℝ × Vec 2 => G z.1 z.2) 2
      (volume.restrict AVenhance.timeCube) ≤ ENNReal.ofReal Q) :
    MemLp (fun t => Real.sqrt (AVenhance.l2NormSq (G t))) 2
        (volume.restrict (Set.Ioc (0 : ℝ) 1)) ∧
      (∫ t in Set.Ioc (0 : ℝ) 1,
        (Real.sqrt (AVenhance.l2NormSq (G t))) ^ 2 ≤ Q ^ 2) ∧
      Integrable (fun t => Real.sqrt (AVenhance.l2NormSq (G t)))
        (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  have hGsqInt : Integrable
      (fun z : ℝ × Vec 2 => G z.1 z.2 ^ 2)
      (volume.restrict AVenhance.timeCube) := by
    have hmem : MemLp (fun z : ℝ × Vec 2 => G z.1 z.2) 2
        (volume.restrict AVenhance.timeCube) := hGbound.trans_lt (by finiteness)
    exact hmem.integrable_sq
  have hGsqBound := amnr_scalar_square_le_of_eLpNorm_two
    hGmeas hQ hGbound
  exact hm_time_slice_l2_data_of_spacetime_square hGsqInt hGsqBound

/-- A vector-valued spacetime `L²` bound gives time-slice data for its
Euclidean spatial energy. `Vec 2` carries the Pi sup norm in `eLpNorm`, so
the conversion to `vecNormSq` costs the explicit factor `√2`. -/
theorem hm_vector_time_slice_l2_data_of_spacetime_eLpNorm
    {V : ℝ → Vec 2 → Vec 2} {Q : ℝ}
    (hVmeas : AEStronglyMeasurable
      (fun z : ℝ × Vec 2 => V z.1 z.2)
      (volume.restrict AVenhance.timeCube))
    (hVmagMeas : AEStronglyMeasurable
      (fun z : ℝ × Vec 2 => Real.sqrt (vecNormSq (V z.1 z.2)))
      (volume.restrict AVenhance.timeCube))
    (hQ : 0 ≤ Q)
    (hVbound : eLpNorm (fun z : ℝ × Vec 2 => V z.1 z.2) 2
      (volume.restrict AVenhance.timeCube) ≤ ENNReal.ofReal Q) :
    MemLp (fun t => Real.sqrt (AVenhance.gradNormSq (V t))) 2
        (volume.restrict (Set.Ioc (0 : ℝ) 1)) ∧
      (∫ t in Set.Ioc (0 : ℝ) 1,
        (Real.sqrt (AVenhance.gradNormSq (V t))) ^ 2 ≤
          (Real.sqrt 2 * Q) ^ 2) ∧
      Integrable (fun t => Real.sqrt (AVenhance.gradNormSq (V t)))
        (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  let G : ℝ → Vec 2 → ℝ := fun t x => Real.sqrt (vecNormSq (V t x))
  let μ : Measure (ℝ × Vec 2) := volume.restrict AVenhance.timeCube
  have hpoint (z : ℝ × Vec 2) : G z.1 z.2 ≤ Real.sqrt 2 * ‖V z.1 z.2‖ := by
    calc
      G z.1 z.2 ≤ Real.sqrt (2 * ‖V z.1 z.2‖ ^ 2) :=
        Real.sqrt_le_sqrt (by
          simpa [G] using
            (AVenhance.Infra.Section5.RelativeError.vecNormSq_two_le (V z.1 z.2)))
      _ = Real.sqrt 2 * ‖V z.1 z.2‖ := by
        rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (norm_nonneg _)]
  have hGbound : eLpNorm (fun z : ℝ × Vec 2 => G z.1 z.2) 2 μ ≤
      ENNReal.ofReal (Real.sqrt 2 * Q) := by
    have hmono := eLpNorm_mono_ae (by simpa only [G, μ] using hVmagMeas)
      (Filter.Eventually.of_forall fun z => by
        calc
          ‖G z.1 z.2‖ = G z.1 z.2 := by
            rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
          _ ≤ Real.sqrt 2 * ‖V z.1 z.2‖ := hpoint z
          _ = ‖Real.sqrt 2 • ‖V z.1 z.2‖‖ := by
            rw [norm_smul]
            rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 2)]
            rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (V z.1 z.2))]) (p := 2)
    calc
      _ ≤ eLpNorm (fun z : ℝ × Vec 2 => Real.sqrt 2 • ‖V z.1 z.2‖) 2 μ := by
        exact hmono
      _ = ‖Real.sqrt 2‖ₑ * eLpNorm (fun z : ℝ × Vec 2 => ‖V z.1 z.2‖) 2 μ :=
        eLpNorm_const_smul (Real.sqrt 2) (fun z : ℝ × Vec 2 => ‖V z.1 z.2‖) 2 μ
      _ = ENNReal.ofReal (Real.sqrt 2) *
          eLpNorm (fun z : ℝ × Vec 2 => V z.1 z.2) 2 μ := by
        rw [eLpNorm_norm _ (by simpa only [μ] using hVmeas)]
        rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (Real.sqrt_nonneg 2)]
      _ ≤ ENNReal.ofReal (Real.sqrt 2) * ENNReal.ofReal Q :=
        mul_le_mul_of_nonneg_left hVbound (by positivity)
      _ = ENNReal.ofReal (Real.sqrt 2 * Q) := by
        rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  have hData := hm_time_slice_l2_data_of_spacetime_eLpNorm
    (G := G) (Q := Real.sqrt 2 * Q)
    (by simpa only [G, μ] using hVmagMeas)
    (mul_nonneg (Real.sqrt_nonneg _) hQ) hGbound
  have hEnergy (t : ℝ) : AVenhance.l2NormSq (G t) =
      AVenhance.gradNormSq (V t) := by
    unfold AVenhance.l2NormSq AVenhance.gradNormSq G
    apply integral_congr_ae
    filter_upwards with x
    exact Real.sq_sqrt (vecNormSq_nonneg (V t x))
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hEnergy] using hData.1
  · simpa only [hEnergy] using hData.2.1
  · simpa only [hEnergy] using hData.2.2

end AVenhance.Infra.Section4

end
