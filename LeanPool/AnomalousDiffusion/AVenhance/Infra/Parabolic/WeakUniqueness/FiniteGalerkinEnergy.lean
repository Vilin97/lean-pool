/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.WeakUniqueness.ModePath
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.WeakUniqueness.FiniteEnergy
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.GalerkinModeCalculus
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.ODE.Linear.Basic

/-!
# Energy identity for finite Fourier coefficients of weak solutions

Each real Fourier coefficient satisfies a scalar integral equation. Applying the finite-path
energy identity coefficientwise and summing gives the exact energy identity for every Fourier
cutoff.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open Homogenization

namespace AVenhance.Infra.Parabolic.WeakUniqueness

open AVenhance.Infra.Parabolic.FourierGalerkin

/-- The finite vector of real Fourier coefficients of a weak path at time `t`. -/
def weakFourierCoefficientPath (N : ℕ) (u : ℝ → Vec 2 → ℝ) (t : ℝ) :
    Coefficients (RealFourierDimension N) :=
  WithLp.toLp 2 (fun i => weakModePairing u
    (realFourierModeAmbient N ((realFourierIndexEquivFin N).symm i)) t)

theorem FiniteGalerkinEnergy.weakFourierMode_smooth (N : ℕ) (i : Fin (RealFourierDimension N)) :
    ContDiff ℝ (⊤ : ℕ∞)
      (realFourierModeAmbient N ((realFourierIndexEquivFin N).symm i)) :=
  (realFourierModeAmbient_contDiff N ((realFourierIndexEquivFin N).symm i)).of_le
    (by simp)

theorem FiniteGalerkinEnergy.weakFourierMode_periodic (N : ℕ) (i : Fin (RealFourierDimension N)) :
    AVenhance.IsZ2Periodic
      (realFourierModeAmbient N ((realFourierIndexEquivFin N).symm i)) :=
  realFourierModeAmbient_periodic N ((realFourierIndexEquivFin N).symm i)

/-- Coefficientwise integration by parts in time gives the exact energy balance for the finite
real Fourier projection of a weak solution. -/
theorem weak_solution_finite_fourier_energy_identity
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {f : Vec 2 → ℝ}
    {u : ℝ → Vec 2 → ℝ} {D : ℝ → Vec 2 → Vec 2}
    (hu : AVenhance.IsWeakSolutionGrad b κ f u D)
    (hf : MemL2On AVenhance.unitCube f)
    (N : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖weakFourierCoefficientPath N u t‖ ^ 2 +
      ∫ s in (0 : ℝ)..t,
        2 * ∑ i : Fin (RealFourierDimension N),
          weakModePairing u
              (realFourierModeAmbient N ((realFourierIndexEquivFin N).symm i)) s *
            weakModeForcing b κ D
              (realFourierModeAmbient N ((realFourierIndexEquivFin N).symm i)) s =
      ‖weakFourierCoefficientPath N u 0‖ ^ 2 := by
  classical
  let c : Fin (RealFourierDimension N) → ℝ → ℝ := fun i s =>
    weakModePairing u
      (realFourierModeAmbient N ((realFourierIndexEquivFin N).symm i)) s
  let q : Fin (RealFourierDimension N) → ℝ → ℝ := fun i s =>
    weakModeForcing b κ D
      (realFourierModeAmbient N ((realFourierIndexEquivFin N).symm i)) s
  have hccont (i : Fin (RealFourierDimension N)) :
      ContinuousOn (c i) (Set.Icc (0 : ℝ) 1) := by
    dsimp [c, weakModePairing]
    exact hu.2.2.2.2.2.2.1
      (realFourierModeAmbient N ((realFourierIndexEquivFin N).symm i))
      (FiniteGalerkinEnergy.weakFourierMode_smooth N i)
          (FiniteGalerkinEnergy.weakFourierMode_periodic N i)
  have hqint (i : Fin (RealFourierDimension N)) :
      IntervalIntegrable (q i) volume 0 1 := by
    dsimp [q]
    exact weak_solution_mode_forcing_intervalIntegrable hu
        (FiniteGalerkinEnergy.weakFourierMode_smooth N i)
  have hqintT (i : Fin (RealFourierDimension N)) :
      IntervalIntegrable (q i) volume 0 t := by
    have hsubset : uIcc (0 : ℝ) t ⊆ uIcc 0 1 := by
      rw [uIcc_of_le ht.1, uIcc_of_le (by norm_num)]
      intro s hs
      exact ⟨hs.1, hs.2.trans ht.2⟩
    exact (hqint i).mono_set hsubset
  have hmodePath (i : Fin (RealFourierDimension N)) :
      ∀ s ∈ Set.Icc (0 : ℝ) t,
        c i s = c i 0 + ∫ r in (0 : ℝ)..s, -q i r := by
    intro s hs
    have hs01 : s ∈ Set.Icc (0 : ℝ) 1 := ⟨hs.1, hs.2.trans ht.2⟩
    have hpath := weak_solution_mode_integral_path hu hf
      (FiniteGalerkinEnergy.weakFourierMode_smooth N i)
          (FiniteGalerkinEnergy.weakFourierMode_periodic N i) s hs01
    dsimp [c, q, weakModePairing, weakModeForcing] at hpath ⊢
    have hinit := weak_solution_mode_integral_path hu hf
      (FiniteGalerkinEnergy.weakFourierMode_smooth N i)
          (FiniteGalerkinEnergy.weakFourierMode_periodic N i) 0
      ⟨le_rfl, by norm_num⟩
    have hinit' : (∫ x in AVenhance.unitCube,
        f x * realFourierModeAmbient N ((realFourierIndexEquivFin N).symm i) x) =
        c i 0 := by
      simpa [c, weakModePairing] using hinit.symm
    rw [hinit'] at hpath
    rw [intervalIntegral.integral_neg]
    exact hpath
  have hmodeEnergy (i : Fin (RealFourierDimension N)) :
      ∫ s in (0 : ℝ)..t, 2 * c i s * q i s = c i 0 ^ 2 - c i t ^ 2 := by
    let y : ℝ → ℝ := c i
    let q₀ : ℝ → ℝ := q i
    have hy : AVenhance.Infra.ODE.IsLinearIntegralSolution
        (fun _ : ℝ => (0 : ℝ →L[ℝ] ℝ)) (fun s => -q₀ s) (y 0) 0 t y := by
      intro s hs
      have h := hmodePath i s hs
      dsimp [AVenhance.Infra.ODE.IsLinearIntegralSolution,
        AVenhance.Infra.ODE.linearRhs, y, q₀]
      simpa [integral_neg] using h
    have henergy := integral_path_energy_identity (hab := ht.1) hy (hqintT i)
    calc
      ∫ s in (0 : ℝ)..t, 2 * c i s * q i s =
          ∫ s in (0 : ℝ)..t, 2 * (c i s * q i s) := by
        apply intervalIntegral.integral_congr
        intro s hs
        ring
      _ = 2 * ∫ s in (0 : ℝ)..t, q i s * c i s := by
        rw [intervalIntegral.integral_const_mul]
        congr 1
        apply intervalIntegral.integral_congr
        intro s hs
        ring
      _ = c i 0 ^ 2 - c i t ^ 2 := by simpa [y, q₀] using henergy
  have hmodeEnergySum :
      ∑ i : Fin (RealFourierDimension N),
        ∫ s in (0 : ℝ)..t, 2 * c i s * q i s =
      ∑ i : Fin (RealFourierDimension N), (c i 0 ^ 2 - c i t ^ 2) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hmodeEnergy i
  have hproducts (i : Fin (RealFourierDimension N)) :
      IntervalIntegrable (fun s => 2 * c i s * q i s) volume 0 t := by
    have hqT : IntervalIntegrable (q i) volume 0 t := hqintT i
    have hcT : ContinuousOn (c i) (uIcc (0 : ℝ) t) := by
      apply (hccont i).mono
      intro s hs
      rw [uIcc_of_le ht.1] at hs
      exact ⟨hs.1, hs.2.trans ht.2⟩
    have hprod := hqT.mul_continuousOn hcT
    convert hprod.const_mul 2 using 1
    funext s
    ring
  have hsumIntegral :
      ∫ s in (0 : ℝ)..t, 2 * ∑ i : Fin (RealFourierDimension N), c i s * q i s =
        ∑ i : Fin (RealFourierDimension N),
          ∫ s in (0 : ℝ)..t, 2 * c i s * q i s := by
    rw [show (fun s => 2 * ∑ i : Fin (RealFourierDimension N), c i s * q i s) =
        fun s => ∑ i : Fin (RealFourierDimension N), 2 * c i s * q i s by
      funext s
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring]
    exact intervalIntegral.integral_finsetSum (fun i hi => hproducts i)
  have hnorm (s : ℝ) : ‖weakFourierCoefficientPath N u s‖ ^ 2 =
      ∑ i : Fin (RealFourierDimension N), c i s ^ 2 := by
    calc
      ‖weakFourierCoefficientPath N u s‖ ^ 2 =
          inner ℝ (weakFourierCoefficientPath N u s)
            (weakFourierCoefficientPath N u s) :=
        (real_inner_self_eq_norm_sq _).symm
      _ = ∑ i : Fin (RealFourierDimension N), c i s * c i s := by
        rw [weakFourierCoefficientPath, PiLp.inner_apply]
        simp [c, weakModePairing, pow_two]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        exact (pow_two (c i s)).symm
  rw [hnorm t, hnorm 0, hsumIntegral, hmodeEnergySum]
  simp only [Finset.sum_sub_distrib]
  ring

end AVenhance.Infra.Parabolic.WeakUniqueness

end
