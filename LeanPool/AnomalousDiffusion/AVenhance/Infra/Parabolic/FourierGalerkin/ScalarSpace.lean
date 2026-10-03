/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.ProjectionCoefficients
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Scalar spatial `L²` synthesis for the real Fourier frame

The orthonormal scalar Fourier modes synthesize an isometric copy of the finite coefficient
space inside scalar torus `L²`. This is the common state space for the cutoff paths and the
coefficient energy estimate.
-/

@[expose] public section

noncomputable section

open MeasureTheory

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance scalarSpaceMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance scalarSpaceMeasureIsAddHaarUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance scalarSpaceProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace AVenhance.Infra.Parabolic.FourierGalerkin

/-- Scalar-valued spatial `L²` on the unit torus. -/
abbrev ScalarTorusL2 := Lp ℝ 2 (volume : Measure Torus)

/-- Every real Fourier mode belongs to scalar spatial `L²`. -/
theorem realFourierModeFin_memLp (N : ℕ) (i : Fin (RealFourierDimension N)) :
    MemLp (realFourierModeFin N i) 2 (volume : Measure Torus) := by
  have hcont := realFourierModeFin_continuous N i
  have hint : Integrable (fun x : Torus => realFourierModeFin N i x ^ 2) volume := by
    exact (hcont.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  exact (memLp_two_iff_integrable_sq hcont.aestronglyMeasurable).2 hint

/-- The class of one normalized real cutoff mode in scalar `L²`. -/
noncomputable def realFourierModeL2 (N : ℕ) (i : Fin (RealFourierDimension N)) :
    ScalarTorusL2 :=
  (realFourierModeFin_memLp N i).toLp (realFourierModeFin N i)

/-- Synthesis of a finite real coefficient vector as a scalar torus `L²` function. -/
noncomputable def realFourierScalarMap (N : ℕ) :
    Coefficients (RealFourierDimension N) →L[ℝ] ScalarTorusL2 :=
  ∑ i : Fin (RealFourierDimension N),
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (RealFourierDimension N) => ℝ) i).smulRight
      (realFourierModeL2 N i)

@[simp]
theorem realFourierScalarMap_apply (N : ℕ)
    (c : Coefficients (RealFourierDimension N)) :
    realFourierScalarMap N c =
      ∑ i : Fin (RealFourierDimension N), (c i) • realFourierModeL2 N i := by
  simp [realFourierScalarMap, PiLp.proj_apply]

/-- The scalar cutoff modes remain orthonormal in their `L²` classes. -/
theorem realFourierModeL2_inner (N : ℕ) (i j : Fin (RealFourierDimension N)) :
    inner ℝ (realFourierModeL2 N i) (realFourierModeL2 N j) =
      if i = j then 1 else 0 := by
  rw [MeasureTheory.L2.inner_def]
  calc
    _ = ∫ x : Torus, realFourierModeFin N i x * realFourierModeFin N j x := by
      apply integral_congr_ae
      filter_upwards [(realFourierModeFin_memLp N i).coeFn_toLp,
        (realFourierModeFin_memLp N j).coeFn_toLp] with x hi hj
      simp [realFourierModeL2, hi, hj]
      ring
    _ = _ := realFourierModeFin_orthonormal N i j

theorem ScalarSpace.finiteModeSynthesis_inner {n : ℕ}
    (v : Fin n → ScalarTorusL2)
    (horth : ∀ i j, inner ℝ (v i) (v j) = if i = j then 1 else 0)
    (c d : Coefficients n) :
    inner ℝ (∑ i : Fin n, (c i) • v i) (∑ j : Fin n, (d j) • v j) =
      inner ℝ c d := by
  classical
  rw [sum_inner]
  simp_rw [inner_sum, inner_smul_left, inner_smul_right, horth]
  simp [PiLp.inner_apply, mul_comm]

theorem ScalarSpace.finiteModeSynthesis_norm {n : ℕ}
    (v : Fin n → ScalarTorusL2)
    (horth : ∀ i j, inner ℝ (v i) (v j) = if i = j then 1 else 0)
    (c : Coefficients n) :
    ‖∑ i : Fin n, (c i) • v i‖ = ‖c‖ := by
  have hinner := ScalarSpace.finiteModeSynthesis_inner v horth c c
  have hleft := real_inner_self_eq_norm_sq (∑ i : Fin n, (c i) • v i)
  have hright := real_inner_self_eq_norm_sq c
  rw [hinner] at hleft
  nlinarith [hleft, hright, norm_nonneg (∑ i : Fin n, (c i) • v i), norm_nonneg c]

/-- The coefficient vector of an orthogonal projection onto a finite orthonormal family is
contractive. -/
noncomputable def orthonormalProjectionCoefficients {n : ℕ}
    (v : Fin n → ScalarTorusL2) (x : ScalarTorusL2) : Coefficients n :=
  WithLp.toLp 2 (fun i => inner ℝ x (v i))

theorem orthonormalProjectionCoefficients_norm_le {n : ℕ}
    (v : Fin n → ScalarTorusL2)
    (horth : ∀ i j, inner ℝ (v i) (v j) = if i = j then 1 else 0)
    (x : ScalarTorusL2) :
    ‖orthonormalProjectionCoefficients v x‖ ≤ ‖x‖ := by
  let c := orthonormalProjectionCoefficients v x
  let s : ScalarTorusL2 := ∑ i : Fin n, (c i) • v i
  have hc (i : Fin n) : c i = inner ℝ x (v i) := by
    simp [c, orthonormalProjectionCoefficients]
  have hxs : inner ℝ (x - s) s = 0 := by
    rw [inner_sub_left]
    have hfirst : inner ℝ x s = ∑ i : Fin n, (c i) ^ 2 := by
      rw [show s = ∑ i : Fin n, (c i) • v i by rfl, inner_sum]
      simp_rw [inner_smul_right, hc]
      simp [pow_two]
    have hsecond : inner ℝ s s = ∑ i : Fin n, (c i) ^ 2 := by
      have h := ScalarSpace.finiteModeSynthesis_inner v horth c c
      calc
        inner ℝ s s = inner ℝ c c := by simpa [s] using h
        _ = ∑ i : Fin n, (c i) ^ 2 := by
          rw [PiLp.inner_apply]
          simp [pow_two]
    rw [hfirst, hsecond]
    ring
  have hp := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (x - s) s hxs
  have hpyth : ‖x‖ ^ 2 = ‖x - s‖ ^ 2 + ‖s‖ ^ 2 := by
    have hx : ‖x‖ * ‖x‖ = ‖x - s‖ * ‖x - s‖ + ‖s‖ * ‖s‖ := by
      simpa [sub_add_cancel] using hp
    nlinarith
  have hs := ScalarSpace.finiteModeSynthesis_norm v horth c
  have hle : ‖c‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [← hs]
    nlinarith [hpyth, sq_nonneg ‖x - s‖]
  exact (sq_le_sq₀ (norm_nonneg c) (norm_nonneg x)).mp hle

/-- Synthesis by an orthonormal real Fourier frame is an isometry. -/
theorem realFourierScalarMap_norm (N : ℕ)
    (c : Coefficients (RealFourierDimension N)) :
    ‖realFourierScalarMap N c‖ = ‖c‖ := by
  have hinner := ScalarSpace.finiteModeSynthesis_inner (realFourierModeL2 N)
    (realFourierModeL2_inner N) c c
  have hinner' : inner ℝ (realFourierScalarMap N c) (realFourierScalarMap N c) =
      inner ℝ c c := by
    simpa only [realFourierScalarMap_apply] using hinner
  have hleft := real_inner_self_eq_norm_sq (realFourierScalarMap N c)
  have hright := real_inner_self_eq_norm_sq c
  rw [hinner'] at hleft
  nlinarith [hleft, hright, norm_nonneg (realFourierScalarMap N c), norm_nonneg c]

/-- Synthesis preserves the coefficient-space pairing, including against a different test vector.
This identity is the interface used to test the finite ODE by an arbitrary Fourier mode. -/
theorem realFourierScalarMap_inner (N : ℕ)
    (c d : Coefficients (RealFourierDimension N)) :
    inner ℝ (realFourierScalarMap N c) (realFourierScalarMap N d) = inner ℝ c d := by
  have hinner := ScalarSpace.finiteModeSynthesis_inner (realFourierModeL2 N)
    (realFourierModeL2_inner N) c d
  simpa only [realFourierScalarMap_apply] using hinner

/-- The finite Fourier projection coefficients of any torus `L²` datum are contractive. -/
theorem realFourierModeFin_projectionCoefficients_norm_le (N : ℕ)
    {f : Torus → ℝ} (hf : MemLp f 2 (volume : Measure Torus)) :
    ‖modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N) f‖ ≤
      ‖hf.toLp f‖ := by
  have hcoeff :
      modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N) f =
        orthonormalProjectionCoefficients (realFourierModeL2 N) (hf.toLp f) := by
    ext i
    change (∫ x : Torus, f x * realFourierModeFin N i x) =
      inner ℝ (hf.toLp f) (realFourierModeL2 N i)
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp, (realFourierModeFin_memLp N i).coeFn_toLp]
      with x hx hi
    simp [realFourierModeL2, hx, hi, mul_comm]
  rw [hcoeff]
  exact orthonormalProjectionCoefficients_norm_le (realFourierModeL2 N)
    (realFourierModeL2_inner N) (hf.toLp f)

end AVenhance.Infra.Parabolic.FourierGalerkin

end
