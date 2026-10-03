/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.WeakUniqueness.WeakProjectionConvergence

/-!
# Lemma U: cell coefficients of real Fourier modes

For a periodic function `f` on the unit cell, `cellCoeff M f a = ∫_cell f ψ_a` is its coefficient
against the real mode `ψ_a` of the cutoff `M`.  This file records Bessel's inequality in this
form, the multiplier identity for gradients of periodic `H¹` functions, and the resulting
`Σ_a λ_a c_a² ≤ ‖Df‖²`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Homogenization
open AVenhance.Infra.Parabolic.FourierGalerkin
open AVenhance.Infra.Parabolic.WeakUniqueness
open AVenhance.Infra.Classical

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance lemmaUMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance lemmaUMeasureIsAddHaar :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance lemmaUProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance lemmaUProbability : IsProbabilityMeasure
    (volume : Measure Torus) := inferInstance

namespace AVenhance.Infra.FullTheorem.LemmaU

/-- The cell coefficient of a function against the real mode `a` at cutoff `M`. -/
def cellCoeff (M : ℕ) (f : Vec 2 → ℝ) (a : RealFourierIndex M) : ℝ :=
  ∫ x in AVenhance.unitCube, f x * realFourierModeAmbient M a x

/-- The Laplace eigenvalue `4π²|k|²` of the real mode `a`. -/
def modeLam (M : ℕ) (a : RealFourierIndex M) : ℝ :=
  ∑ i : Fin 2, realFourierModeDerivativeScale a i ^ 2

theorem modeLam_nonneg (M : ℕ) (a : RealFourierIndex M) : 0 ≤ modeLam M a :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem modeCoeff_torus (M : ℕ) (f : Vec 2 → ℝ) (a : RealFourierIndex M) :
    modeProjectionCoefficients (RealFourierDimension M) (realFourierModeFin M)
      (AVenhance.Infra.Torus.periodicToTorus f) (realFourierIndexEquivFin M a) =
      cellCoeff M f a := by
  simp only [modeProjectionCoefficients, PiLp.toLp_apply]
  rw [realFourierModeFin_eq_periodicToTorus]
  simp only [Equiv.symm_apply_apply]
  change (∫ x : Torus, AVenhance.Infra.Torus.periodicToTorus
      (fun y => f y * realFourierModeAmbient M a y) x) = _
  rw [AVenhance.Infra.Torus.integral_periodicToTorus_eq_unitCell,
    AVenhance.Infra.Torus.integral_unitCell_eq_unitCube]
  rfl

/-- Bessel's inequality for the cell coefficients. -/
theorem cellCoeff_bessel (M : ℕ) {f : Vec 2 → ℝ} (hf : MemL2On AVenhance.unitCube f) :
    ∑ a, cellCoeff M f a ^ 2 ≤ AVenhance.l2NormSq f := by
  have hmem := weakProjection_realCellToTorus_memLp hf
  have h1 := realFourierModeFin_projectionCoefficients_norm_le M hmem
  have h2 := weakProjection_scalarTransfer_normSq hf
  have hnorm : ‖modeProjectionCoefficients (RealFourierDimension M) (realFourierModeFin M)
      (AVenhance.Infra.Torus.periodicToTorus f)‖ ^ 2 =
      ∑ a, cellCoeff M f a ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Real.norm_eq_abs, sq_abs]
    rw [← Equiv.sum_comp (realFourierIndexEquivFin M)]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [← modeCoeff_torus M f a]
  rw [← hnorm, ← h2]
  exact pow_le_pow_left₀ (norm_nonneg _) h1 2

theorem spaceGrad_mode (M : ℕ) (a : RealFourierIndex M) (i : Fin 2) (x : Vec 2) :
    AVenhance.spaceGrad (realFourierModeAmbient M a) x i =
      realFourierModeDerivativeScale a i *
        realFourierModeAmbient M (realFourierModeIndexSwap a) x := by
  rw [spaceGrad_realFourierModeAmbient]
  cases a with
  | none => simp [realFourierModeDerivativeScale]
  | some q =>
      rcases q with ⟨p, sine⟩
      cases sine <;> simp [realFourierModeDerivativeScale]

/-- The Fourier multiplier identity for the coefficients of a weak gradient. -/
theorem cellCoeff_grad {u : Vec 2 → ℝ} {Du : Vec 2 → Vec 2}
    (hH : AVenhance.IsPeriodicH1With u Du) (M : ℕ) (i : Fin 2) (a : RealFourierIndex M) :
    cellCoeff M (fun x => Du x i) a =
      cellCoeff M u (realFourierModeIndexSwap a) *
        realFourierModeDerivativeScale (realFourierModeIndexSwap a) i := by
  have h := weakGradient_realFourierProjectionCoefficients hH M i
  have h2 := congrArg (fun v => v.ofLp (realFourierIndexEquivFin M a)) h
  simp only [realFourierModeDerivativeCoefficients, PiLp.toLp_apply,
    Equiv.symm_apply_apply] at h2
  rw [modeCoeff_torus M (fun x => Du x i) a, modeCoeff_torus M u _] at h2
  exact h2.symm

theorem swap_sum {M : ℕ} (F : RealFourierIndex M → ℝ) :
    ∑ a, F (realFourierModeIndexSwap a) = ∑ a, F a :=
  Equiv.sum_comp (Function.Involutive.toPerm realFourierModeIndexSwap
    realFourierModeIndexSwap_involutive) F

theorem gradNormSq_eq_sum (Du : Vec 2 → Vec 2) (hD : Homogenization.GradMemL2On AVenhance.unitCube
    Du) :
    AVenhance.gradNormSq Du = ∑ i : Fin 2, AVenhance.l2NormSq (fun x => Du x i) := by
  unfold AVenhance.gradNormSq AVenhance.l2NormSq
  have : (fun x => vecNormSq (Du x)) = fun x => ∑ i : Fin 2, Du x i ^ 2 := by
    funext x
    simp [Homogenization.vecNormSq, Homogenization.vecDot, sq]
  rw [this, integral_finsetSum]
  intro i _
  have := weak_product_integrable_cell (hD i) (hD i)
  simpa [sq] using this

/-- `Σ λ_a c_a² ≤ ‖Du‖²` for a periodic `H¹` function. -/
theorem modeLam_sum_le {u : Vec 2 → ℝ} {Du : Vec 2 → Vec 2}
    (hH : AVenhance.IsPeriodicH1With u Du) (M : ℕ) :
    ∑ a, modeLam M a * cellCoeff M u a ^ 2 ≤ AVenhance.gradNormSq Du := by
  rw [gradNormSq_eq_sum Du hH.2.2.2.1]
  have hcomp : ∀ i : Fin 2, ∑ a, (realFourierModeDerivativeScale a i * cellCoeff M u a) ^ 2 ≤
      AVenhance.l2NormSq (fun x => Du x i) := by
    intro i
    have hb := cellCoeff_bessel M (hH.2.2.2.1 i)
    have : ∑ a, cellCoeff M (fun x => Du x i) a ^ 2 =
        ∑ a, (realFourierModeDerivativeScale a i * cellCoeff M u a) ^ 2 := by
      have e : ∀ a, cellCoeff M (fun x => Du x i) a ^ 2 =
          (fun b => (realFourierModeDerivativeScale b i * cellCoeff M u b) ^ 2)
            (realFourierModeIndexSwap a) := by
        intro a
        simp only [cellCoeff_grad hH M i a]
        ring
      rw [Finset.sum_congr rfl (fun a _ => e a)]
      exact swap_sum (fun b => (realFourierModeDerivativeScale b i * cellCoeff M u b) ^ 2)
    rw [← this]
    exact hb
  calc ∑ a, modeLam M a * cellCoeff M u a ^ 2
      = ∑ i : Fin 2, ∑ a, (realFourierModeDerivativeScale a i * cellCoeff M u a) ^ 2 := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        simp only [modeLam, Finset.sum_mul]
        exact Finset.sum_congr rfl (fun i _ => by ring)
    _ ≤ ∑ i : Fin 2, AVenhance.l2NormSq (fun x => Du x i) :=
        Finset.sum_le_sum (fun i _ => hcomp i)

/-- The diffusion pairing with a mode is the eigenvalue times the coefficient. -/
theorem vecDot_gradMode {u : Vec 2 → ℝ} {Du : Vec 2 → Vec 2}
    (hH : AVenhance.IsPeriodicH1With u Du) (M : ℕ) (a : RealFourierIndex M) :
    ∫ x in AVenhance.unitCube,
        Homogenization.vecDot (Du x) (AVenhance.spaceGrad (realFourierModeAmbient M a) x) =
      modeLam M a * cellCoeff M u a := by
  have hψ : ∀ b : RealFourierIndex M, MemL2On AVenhance.unitCube (realFourierModeAmbient M b) :=
    fun b => weak_continuous_memL2On (realFourierModeAmbient_contDiff M b).continuous
  have hterm : ∀ i : Fin 2, ∫ x in AVenhance.unitCube,
      Du x i * AVenhance.spaceGrad (realFourierModeAmbient M a) x i =
      realFourierModeDerivativeScale a i ^ 2 * cellCoeff M u a := by
    intro i
    have e : ∀ x, Du x i * AVenhance.spaceGrad (realFourierModeAmbient M a) x i =
        realFourierModeDerivativeScale a i *
          (Du x i * realFourierModeAmbient M (realFourierModeIndexSwap a) x) := by
      intro x; rw [spaceGrad_mode]; ring
    simp_rw [e]
    rw [integral_const_mul]
    have hc := cellCoeff_grad hH M i (realFourierModeIndexSwap a)
    rw [realFourierModeIndexSwap_involutive] at hc
    change realFourierModeDerivativeScale a i * cellCoeff M (fun x => Du x i)
      (realFourierModeIndexSwap a) = _
    rw [hc]
    ring
  have hint : ∀ i ∈ (Finset.univ : Finset (Fin 2)), Integrable
      (fun x => Du x i * AVenhance.spaceGrad (realFourierModeAmbient M a) x i)
      (volume.restrict AVenhance.unitCube) := by
    intro i _
    refine weak_product_integrable_cell (hH.2.2.2.1 i) ?_
    have hc : Continuous (fun x : Vec 2 => AVenhance.spaceGrad (realFourierModeAmbient M a) x i) :=
      ((realFourierModeAmbient_contDiff M a).continuous_fderiv (by simp)).clm_apply
        continuous_const
    exact weak_continuous_memL2On hc
  have : (fun x => Homogenization.vecDot (Du x) (AVenhance.spaceGrad (realFourierModeAmbient M a)
      x)) =
      fun x => ∑ i : Fin 2, Du x i * AVenhance.spaceGrad (realFourierModeAmbient M a) x i := rfl
  rw [this, integral_finsetSum _ hint]
  simp_rw [hterm]
  simp [modeLam]
  ring

end AVenhance.Infra.FullTheorem.LemmaU

end
