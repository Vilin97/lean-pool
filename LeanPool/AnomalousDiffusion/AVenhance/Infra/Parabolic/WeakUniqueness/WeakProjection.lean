/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Heat.WeakFourier
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.Density
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.GalerkinModeCalculus
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.WeakUniqueness.FiniteGalerkinEnergy

/-!
# Fourier projection of periodic weak gradients

The weak-gradient Fourier multiplier identifies the derivative of each real Fourier
projection with the real Fourier projection of the weak gradient. This gives the slice-wise
`H¹` convergence needed in the weak energy passage.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Homogenization

namespace AVenhance.Infra.Parabolic.WeakUniqueness

open AVenhance.Infra.Parabolic.FourierGalerkin

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance weakProjectionMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance weakProjectionMeasureIsAddHaar :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance weakProjectionProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance weakProjectionProbability : IsProbabilityMeasure
    (volume : Measure Torus) := inferInstance
open AVenhance.Infra.Classical

theorem WeakProjection.weakProjection_mFourierCoeff_congr_ae {f g : Torus → ℂ}
    (hfg : f =ᵐ[volume] g) (k : Fin 2 → ℤ) :
    UnitAddTorus.mFourierCoeff f k = UnitAddTorus.mFourierCoeff g k := by
  unfold UnitAddTorus.mFourierCoeff
  apply integral_congr_ae
  filter_upwards [hfg] with x hx
  simp [hx]

theorem WeakProjection.weakProjection_frozenCellToTorus_coeff {f : Vec 2 → ℝ}
    (hf : MemL2On AVenhance.unitCube f) (k : Fin 2 → ℤ) :
    UnitAddTorus.mFourierCoeff
        (fun x : Torus =>
          AVenhance.Infra.Torus.periodicToTorus (fun y => (f y : ℂ)) x) k =
      UnitAddTorus.mFourierCoeff (AVenhance.Infra.Heat.frozenCellToTorusL2 hf) k := by
  apply WeakProjection.weakProjection_mFourierCoeff_congr_ae
  filter_upwards [AVenhance.Infra.Heat.memLp_frozenCellTransfer hf |>.coeFn_toLp]
    with x hx
  simpa [AVenhance.Infra.Heat.frozenCellToTorusL2] using hx.symm

theorem weakProjection_realCellToTorus_memLp {f : Vec 2 → ℝ}
    (hf : MemL2On AVenhance.unitCube f) :
    MemLp (AVenhance.Infra.Torus.periodicToTorus f) 2 volume := by
  have hcell : MemLp f 2
      (volume.restrict (AVenhance.Infra.Torus.unitCell 2)) := by
    rw [Measure.restrict_congr_set
      AVenhance.Infra.Torus.unitCell_ae_eq_unitCube]
    exact hf
  let Cell := {x : Vec 2 // x ∈ AVenhance.Infra.Torus.unitCell 2}
  let μCell : Measure Cell := volume.comap (Subtype.val : Cell → Vec 2)
  have hmpSub : MeasurePreserving (Subtype.val : Cell → Vec 2) μCell
      (volume.restrict (AVenhance.Infra.Torus.unitCell 2)) := by
    refine ⟨measurable_subtype_coe, ?_⟩
    rw [map_comap_subtype_coe (AVenhance.Infra.Torus.measurableSet_unitCell 2) volume]
  have hsub : MemLp (fun x : Cell => f x.1) 2 μCell := by
    exact hcell.comp_measurePreserving hmpSub
  have hmp := UnitAddTorus.measurePreserving_equivPiIoc
    (fun _ : Fin 2 => (0 : ℝ))
  have htorus := hsub.comp_measurePreserving hmp
  have heq : AVenhance.Infra.Torus.periodicToTorus f =
      fun y => (fun x : Cell => f x.1)
        (UnitAddTorus.measurableEquivPiIoc (fun _ : Fin 2 => (0 : ℝ)) y) := by
    funext y
    rfl
  rw [heq]
  exact htorus

theorem WeakProjection.weakProjection_realFourierMultiplier
    {u : Vec 2 → ℝ} {Du : Vec 2 → Vec 2}
    (h : AVenhance.IsPeriodicH1With u Du) (i : Fin 2) (k : Fin 2 → ℤ) :
    UnitAddTorus.mFourierCoeff
        (fun x : Torus =>
          AVenhance.Infra.Torus.periodicToTorus (fun y => (Du y i : ℂ)) x) k =
      (2 * Real.pi * Complex.I * (k i : ℂ)) *
        UnitAddTorus.mFourierCoeff
          (fun x : Torus =>
            AVenhance.Infra.Torus.periodicToTorus (fun y => (u y : ℂ)) x) k := by
  rw [WeakProjection.weakProjection_frozenCellToTorus_coeff (h.2.2.2.1 i) k,
    WeakProjection.weakProjection_frozenCellToTorus_coeff h.2.2.1 k]
  exact AVenhance.Infra.Heat.mFourierCoeff_frozenPeriodicH1GradientL2 h i k

/-- The finite real Fourier derivative coefficients of a periodic `H¹` value are exactly
the real Fourier coefficients of the corresponding weak-gradient component. -/
theorem weakGradient_realFourierProjectionCoefficients
    {u : Vec 2 → ℝ} {Du : Vec 2 → Vec 2}
    (h : AVenhance.IsPeriodicH1With u Du) (N : ℕ) (i : Fin 2) :
    realFourierModeDerivativeCoefficients N
        (modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
          (AVenhance.Infra.Torus.periodicToTorus u)) i =
      modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
        (AVenhance.Infra.Torus.periodicToTorus (fun x => Du x i)) := by
  classical
  let f : Torus → ℝ := AVenhance.Infra.Torus.periodicToTorus u
  let g : Torus → ℝ :=
    AVenhance.Infra.Torus.periodicToTorus (fun x => Du x i)
  have hfmem : MemLp f 2 volume := by
    simpa [f] using weakProjection_realCellToTorus_memLp h.2.2.1
  have hgmem : MemLp g 2 volume := by
    simpa [g] using weakProjection_realCellToTorus_memLp (h.2.2.2.1 i)
  have hfint : Integrable f volume := hfmem.integrable (by norm_num)
  have hgint : Integrable g volume := hgmem.integrable (by norm_num)
  have hFourier : ∀ k : Fin 2 → ℤ,
      UnitAddTorus.mFourierCoeff (fun x => (g x : ℂ)) k =
        (2 * Real.pi * Complex.I * (k i : ℂ)) *
          UnitAddTorus.mFourierCoeff (fun x => (f x : ℂ)) k := by
    intro k
    simpa only [f, g, AVenhance.Infra.Torus.periodicToTorus] using
      WeakProjection.weakProjection_realFourierMultiplier h i k
  ext j
  let a := (realFourierIndexEquivFin N).symm j
  have hj : realFourierIndexEquivFin N a = j := by
    dsimp [a]
    exact (realFourierIndexEquivFin N).apply_symm_apply j
  simp only [realFourierModeDerivativeCoefficients, PiLp.toLp_apply,
    modeProjectionCoefficients, PiLp.toLp_apply]
  rw [← hj]
  simp only [Equiv.symm_apply_apply]
  change
    (∫ x : Torus, f x *
      realFourierModeFin N
        (realFourierIndexEquivFin N (realFourierModeIndexSwap a)) x) *
        realFourierModeDerivativeScale (realFourierModeIndexSwap a) i =
      ∫ x : Torus, g x * realFourierModeFin N (realFourierIndexEquivFin N a) x
  cases a with
  | none =>
      have hmean : ∫ x : Torus, g x = 0 := by
        have hzero := hFourier (0 : Fin 2 → ℤ)
        rw [mFourierCoeff_real_zero_integral hgint,
          mFourierCoeff_real_zero_integral hfint] at hzero
        simpa using congrArg Complex.re hzero
      change
        modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N) f
            (realFourierIndexEquivFin N none) *
          realFourierModeDerivativeScale none i =
        modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N) g
          (realFourierIndexEquivFin N none)
      rw [realFourierModeFin_projectionCoefficient_const N hfint,
        realFourierModeFin_projectionCoefficient_const N hgint]
      simp [realFourierModeDerivativeScale, hmean]
  | some q =>
      rcases q with ⟨p, hsine⟩
      cases hsine with
      | false =>
          change
            modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N) f
                (realFourierIndexEquivFin N (some (p, true))) *
              realFourierModeDerivativeScale (some (p, true)) i =
            modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N) g
              (realFourierIndexEquivFin N (some (p, false)))
          rw [realFourierModeFin_projectionCoefficient_sin N hfint p,
            realFourierModeFin_projectionCoefficient_cos N hgint p,
            hFourier (representativeFrequency p)]
          simp [realFourierModeDerivativeScale, Complex.mul_re, Complex.mul_im]
          ring
      | true =>
          change
            modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N) f
                (realFourierIndexEquivFin N (some (p, false))) *
              realFourierModeDerivativeScale (some (p, false)) i =
            modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N) g
              (realFourierIndexEquivFin N (some (p, true)))
          rw [realFourierModeFin_projectionCoefficient_cos N hfint p,
            realFourierModeFin_projectionCoefficient_sin N hgint p,
            hFourier (representativeFrequency p)]
          simp [realFourierModeDerivativeScale, Complex.mul_re, Complex.mul_im]
          ring

end AVenhance.Infra.Parabolic.WeakUniqueness

end
