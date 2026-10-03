/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.ForcedEnergyModes

/-!
# Finite Fourier energy balance for a forced weak path

If every smooth periodic Fourier coefficient of a path satisfies an integral equation with
integrable forcing, the finite Fourier projection satisfies the corresponding exact energy balance.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open Homogenization
open scoped Topology

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance.Infra.Parabolic.FourierGalerkin
open AVenhance.Infra.Parabolic.WeakUniqueness

/-- The first seven regularity clauses of a weak solution together with the mode-path form of the
forced weak equation `∂ₜu − κΔu = −G − div F`, `u(0) = f`. -/
structure ForcedModePath (κ : ℝ) (f : Vec 2 → ℝ) (u : ℝ → Vec 2 → ℝ)
    (Du : ℝ → Vec 2 → Vec 2) (G : ℝ × Vec 2 → ℝ) (F : ℝ × Vec 2 → Vec 2) : Prop where
  slice_mem : ∀ t ∈ Set.Icc (0 : ℝ) 1, MemL2On AVenhance.unitCube (u t)
  memLp : MemLp (fun p : ℝ × Vec 2 => u p.1 p.2) 2 (volume.restrict AVenhance.timeCube)
  grad_memLp : ∀ i : Fin 2,
    MemLp (fun p : ℝ × Vec 2 => Du p.1 p.2 i) 2 (volume.restrict AVenhance.timeCube)
  G_memLp : MemLp G 2 (volume.restrict AVenhance.timeCube)
  F_memLp : ∀ i : Fin 2, MemLp (fun p => F p i) 2 (volume.restrict AVenhance.timeCube)
  weak_cont : ∀ ψ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → AVenhance.IsZ2Periodic ψ →
    ContinuousOn (fun t => ∫ x in AVenhance.unitCube, u t x * ψ x) (Set.Icc (0 : ℝ) 1)
  path : ∀ ψ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → AVenhance.IsZ2Periodic ψ →
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∫ x in AVenhance.unitCube, u t x * ψ x =
        (∫ x in AVenhance.unitCube, f x * ψ x) -
          ∫ s in (0 : ℝ)..t, forcedModeForcing κ Du G F ψ s

/-- The real Fourier mode with finite index `i`. -/
def forcedMode (N : ℕ) (i : Fin (RealFourierDimension N)) : Vec 2 → ℝ :=
  realFourierModeAmbient N ((realFourierIndexEquivFin N).symm i)

theorem forcedMode_smooth (N : ℕ) (i : Fin (RealFourierDimension N)) :
    ContDiff ℝ (⊤ : ℕ∞) (forcedMode N i) :=
  (realFourierModeAmbient_contDiff N ((realFourierIndexEquivFin N).symm i)).of_le
    (by simp)

theorem forcedMode_periodic (N : ℕ) (i : Fin (RealFourierDimension N)) :
    AVenhance.IsZ2Periodic (forcedMode N i) :=
  realFourierModeAmbient_periodic N ((realFourierIndexEquivFin N).symm i)

/-- Coefficientwise energy balance for the finite Fourier projection of a forced path. -/
theorem forced_finite_fourier_energy
    {κ : ℝ} {f : Vec 2 → ℝ} {u : ℝ → Vec 2 → ℝ} {Du : ℝ → Vec 2 → Vec 2}
    {G : ℝ × Vec 2 → ℝ} {F : ℝ × Vec 2 → Vec 2}
    (h : ForcedModePath κ f u Du G F) (N : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖weakFourierCoefficientPath N u t‖ ^ 2 +
      ∫ s in (0 : ℝ)..t,
        2 * ∑ i : Fin (RealFourierDimension N),
          weakModePairing u (forcedMode N i) s *
            forcedModeForcing κ Du G F (forcedMode N i) s =
      ‖weakFourierCoefficientPath N u 0‖ ^ 2 := by
  classical
  let c : Fin (RealFourierDimension N) → ℝ → ℝ := fun i s =>
    weakModePairing u (forcedMode N i) s
  let q : Fin (RealFourierDimension N) → ℝ → ℝ := fun i s =>
    forcedModeForcing κ Du G F (forcedMode N i) s
  have hccont (i : Fin (RealFourierDimension N)) :
      ContinuousOn (c i) (Set.Icc (0 : ℝ) 1) :=
    h.weak_cont _ (forcedMode_smooth N i) (forcedMode_periodic N i)
  have hqint (i : Fin (RealFourierDimension N)) :
      IntervalIntegrable (q i) volume 0 1 :=
    forcedModeForcing_intervalIntegrable h.grad_memLp h.G_memLp h.F_memLp
      (forcedMode_smooth N i)
  have hsubset : uIcc (0 : ℝ) t ⊆ uIcc 0 1 := by
    rw [uIcc_of_le ht.1, uIcc_of_le (by norm_num)]
    intro s hs
    exact ⟨hs.1, hs.2.trans ht.2⟩
  have hqintT (i : Fin (RealFourierDimension N)) :
      IntervalIntegrable (q i) volume 0 t := (hqint i).mono_set hsubset
  have hzeroPath (i : Fin (RealFourierDimension N)) :
      c i 0 = ∫ x in AVenhance.unitCube, f x * forcedMode N i x := by
    have := h.path _ (forcedMode_smooth N i) (forcedMode_periodic N i) 0
      ⟨le_rfl, by norm_num⟩
    simpa [c, weakModePairing] using this
  have hmodePath (i : Fin (RealFourierDimension N)) :
      ∀ s ∈ Set.Icc (0 : ℝ) t,
        c i s = c i 0 + ∫ r in (0 : ℝ)..s, -q i r := by
    intro s hs
    have hs01 : s ∈ Set.Icc (0 : ℝ) 1 := ⟨hs.1, hs.2.trans ht.2⟩
    have hpath := h.path _ (forcedMode_smooth N i) (forcedMode_periodic N i) s hs01
    rw [intervalIntegral.integral_neg, hzeroPath i]
    simpa [c, q, weakModePairing, sub_eq_add_neg] using hpath
  have hmodeEnergy (i : Fin (RealFourierDimension N)) :
      ∫ s in (0 : ℝ)..t, 2 * c i s * q i s = c i 0 ^ 2 - c i t ^ 2 := by
    let y : ℝ → ℝ := c i
    let q₀ : ℝ → ℝ := q i
    have hy : AVenhance.Infra.ODE.IsLinearIntegralSolution
        (fun _ : ℝ => (0 : ℝ →L[ℝ] ℝ)) (fun s => -q₀ s) (y 0) 0 t y := by
      intro s hs
      have h' := hmodePath i s hs
      dsimp [AVenhance.Infra.ODE.IsLinearIntegralSolution,
        AVenhance.Infra.ODE.linearRhs, y, q₀]
      simpa [integral_neg] using h'
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
      ∑ i : Fin (RealFourierDimension N), ∫ s in (0 : ℝ)..t, 2 * c i s * q i s =
      ∑ i : Fin (RealFourierDimension N), (c i 0 ^ 2 - c i t ^ 2) :=
    Finset.sum_congr rfl fun i _ => hmodeEnergy i
  have hproducts (i : Fin (RealFourierDimension N)) :
      IntervalIntegrable (fun s => 2 * c i s * q i s) volume 0 t := by
    have hcT : ContinuousOn (c i) (uIcc (0 : ℝ) t) := by
      apply (hccont i).mono
      intro s hs
      rw [uIcc_of_le ht.1] at hs
      exact ⟨hs.1, hs.2.trans ht.2⟩
    have hprod := (hqintT i).mul_continuousOn hcT
    convert hprod.const_mul 2 using 1
    funext s
    ring
  have hsumIntegral :
      ∫ s in (0 : ℝ)..t, 2 * ∑ i : Fin (RealFourierDimension N), c i s * q i s =
        ∑ i : Fin (RealFourierDimension N), ∫ s in (0 : ℝ)..t, 2 * c i s * q i s := by
    rw [show (fun s => 2 * ∑ i : Fin (RealFourierDimension N), c i s * q i s) =
        fun s => ∑ i : Fin (RealFourierDimension N), 2 * c i s * q i s by
      funext s
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring]
    exact intervalIntegral.integral_finsetSum (fun i _ => hproducts i)
  have hnorm (s : ℝ) : ‖weakFourierCoefficientPath N u s‖ ^ 2 =
      ∑ i : Fin (RealFourierDimension N), c i s ^ 2 := by
    calc
      ‖weakFourierCoefficientPath N u s‖ ^ 2 =
          inner ℝ (weakFourierCoefficientPath N u s) (weakFourierCoefficientPath N u s) :=
        (real_inner_self_eq_norm_sq _).symm
      _ = ∑ i : Fin (RealFourierDimension N), c i s * c i s := by
        rw [weakFourierCoefficientPath, PiLp.inner_apply]
        simp [c, weakModePairing, forcedMode, pow_two]
      _ = _ := Finset.sum_congr rfl fun i _ => (pow_two (c i s)).symm
  have hgoal : ∫ s in (0 : ℝ)..t,
        2 * ∑ i : Fin (RealFourierDimension N),
          weakModePairing u (forcedMode N i) s *
            forcedModeForcing κ Du G F (forcedMode N i) s =
      ∫ s in (0 : ℝ)..t, 2 * ∑ i : Fin (RealFourierDimension N), c i s * q i s := rfl
  rw [hnorm t, hnorm 0, hgoal, hsumIntegral, hmodeEnergySum]
  simp only [Finset.sum_sub_distrib]
  ring

end AVenhance.Infra.Section5.RelativeError

end
