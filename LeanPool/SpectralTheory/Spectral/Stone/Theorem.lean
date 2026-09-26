/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
module

public import LeanPool.SpectralTheory.Spectral.Stone.SelfAdjoint
public import LeanPool.SpectralTheory.Spectral.Spectral.Existence


/-!
# Stone's theorem: unitary groups from self-adjoint generators

This file constructs a strongly continuous unitary group from a self-adjoint
operator's spectral functional calculus applied to the phase function
`t ↦ exp(i t r)`, and shows it generates the original operator, completing
Stone's theorem in the direction from self-adjoint operators to unitary
groups.
-/

public section

open MeasureTheory Filter

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- The complex unit phase at time `t` and spectral coordinate `r`. -/
noncomputable def stonePhase (t r : ℝ) : ℂ :=
  Complex.exp (Complex.I * (t : ℂ) * (r : ℂ))

theorem stonePhase_measurable (t : ℝ) : Measurable (stonePhase t) := by
  unfold stonePhase
  fun_prop

theorem stonePhase_norm (t r : ℝ) : ‖stonePhase t r‖ = 1 := by
  rw [stonePhase, mul_assoc, ← Complex.ofReal_mul]
  exact Complex.norm_exp_I_mul_ofReal (t * r)

private theorem stonePhase_zero (r : ℝ) : stonePhase 0 r = 1 := by
  rw [stonePhase, Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero]

private theorem stonePhase_add (s t r : ℝ) :
    stonePhase (s + t) r = stonePhase s r * stonePhase t r := by
  rw [stonePhase, stonePhase, stonePhase, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem stonePhase_bounded (t : ℝ) : ∀ r, ‖stonePhase t r‖ ≤ 1 :=
  fun r => (stonePhase_norm t r).le

private theorem PVM.integral_const_mul_local (E_pvm : PVM E)
    (c : ℂ) (f : ℝ → ℂ) (hf : Measurable f)
    (hbddf : ∃ C, ∀ r, ‖f r‖ ≤ C)
    (hbddMul : ∃ C, ∀ r, ‖c * f r‖ ≤ C) :
    E_pvm.integral (fun r => c * f r) (measurable_const.mul hf) hbddMul =
      c • E_pvm.integral f hf hbddf := by
  let fc : ℝ → ℂ := fun _ => c
  have hfc : Measurable fc := measurable_const
  have hbddc : ∃ C, ∀ r, ‖fc r‖ ≤ C := ⟨‖c‖, fun _ => le_refl _⟩
  have hfun : (fun r => c * f r) = fc * f := by
    funext r
    rfl
  calc
    E_pvm.integral (fun r => c * f r) (measurable_const.mul hf) hbddMul =
        E_pvm.integral (fc * f) (hfc.mul hf) hbddMul :=
      E_pvm.integral_congr hfun _ _ _ _
    _ = E_pvm.integral fc hfc hbddc * E_pvm.integral f hf hbddf :=
      E_pvm.integral_mul fc f hfc hf hbddc hbddf hbddMul
    _ = c • E_pvm.integral f hf hbddf := by
      rw [show E_pvm.integral fc hfc hbddc = c • 1 by
        exact E_pvm.integral_const c, smul_mul_assoc, one_mul]

/-- The bounded evolution operator obtained by integrating the unit phase against a PVM. -/
noncomputable def spectralEvolution (E_pvm : PVM E) (t : ℝ) : E →L[ℂ] E :=
  E_pvm.integral (stonePhase t) (by exact stonePhase_measurable t)
    (by exact ⟨1, stonePhase_bounded t⟩)

private theorem spectralEvolution_zero (E_pvm : PVM E) :
    spectralEvolution E_pvm 0 = 1 := by
  change E_pvm.integral (stonePhase 0) (stonePhase_measurable 0)
    ⟨1, stonePhase_bounded 0⟩ = 1
  have hfun : stonePhase 0 = fun _ : ℝ => (1 : ℂ) := by
    funext r
    exact stonePhase_zero r
  calc
    E_pvm.integral (stonePhase 0) (stonePhase_measurable 0)
        ⟨1, stonePhase_bounded 0⟩ =
      E_pvm.integral (fun _ : ℝ => (1 : ℂ)) measurable_const
        ⟨1, fun _ => by rw [norm_one]⟩ :=
      E_pvm.integral_congr hfun _ _ _ _
    _ = 1 := E_pvm.integral_one

private theorem spectralEvolution_add (E_pvm : PVM E) (s t : ℝ) :
    spectralEvolution E_pvm (s + t) =
      spectralEvolution E_pvm s * spectralEvolution E_pvm t := by
  have hfun : stonePhase (s + t) = stonePhase s * stonePhase t := by
    funext r
    exact stonePhase_add s t r
  have hbddMul : ∀ r, ‖(stonePhase s * stonePhase t) r‖ ≤ 1 := by
    intro r
    change ‖stonePhase s r * stonePhase t r‖ ≤ 1
    rw [norm_mul, stonePhase_norm, stonePhase_norm, one_mul]
  change E_pvm.integral (stonePhase (s + t)) (stonePhase_measurable (s + t))
      ⟨1, stonePhase_bounded (s + t)⟩ =
    E_pvm.integral (stonePhase s) (stonePhase_measurable s) ⟨1, stonePhase_bounded s⟩ *
      E_pvm.integral (stonePhase t) (by exact stonePhase_measurable t)
    (by exact ⟨1, stonePhase_bounded t⟩)
  calc
    E_pvm.integral (stonePhase (s + t)) (stonePhase_measurable (s + t))
        ⟨1, stonePhase_bounded (s + t)⟩ =
      E_pvm.integral (stonePhase s * stonePhase t)
        ((stonePhase_measurable s).mul (stonePhase_measurable t)) ⟨1, hbddMul⟩ :=
      E_pvm.integral_congr hfun _ _ _ _
    _ = E_pvm.integral (stonePhase s) (stonePhase_measurable s)
          ⟨1, stonePhase_bounded s⟩ *
        E_pvm.integral (stonePhase t) (stonePhase_measurable t)
          ⟨1, stonePhase_bounded t⟩ :=
      E_pvm.integral_mul (stonePhase s) (stonePhase t)
        (stonePhase_measurable s) (stonePhase_measurable t)
        ⟨1, stonePhase_bounded s⟩ ⟨1, stonePhase_bounded t⟩ ⟨1, hbddMul⟩

private theorem spectralEvolution_norm (E_pvm : PVM E) (t : ℝ) (x : E) :
    ‖spectralEvolution E_pvm t x‖ = ‖x‖ := by
  have hL2 := E_pvm.ofReal_norm_sq_integral
    (stonePhase t) (stonePhase_measurable t) ⟨1, stonePhase_bounded t⟩ x
  change ENNReal.ofReal (‖spectralEvolution E_pvm t x‖ ^ 2) =
    (∫⁻ r, ‖stonePhase t r‖₊ ^ 2 ∂(E_pvm.scalarMeasure x)) at hL2
  have hright :
      (∫⁻ r, ‖stonePhase t r‖₊ ^ 2 ∂(E_pvm.scalarMeasure x)) =
        ENNReal.ofReal (‖x‖ ^ 2) := by
    change (∫⁻ r, ‖stonePhase t r‖ₑ ^ 2 ∂(E_pvm.scalarMeasure x)) = _
    have henorm (r : ℝ) : ‖stonePhase t r‖ₑ = 1 := by
      rw [enorm_eq_nnnorm]
      exact congrArg (fun z : NNReal => (z : ENNReal))
        (Subtype.ext (stonePhase_norm t r))
    simp_rw [henorm, one_pow]
    rw [lintegral_one, E_pvm.scalarMeasure_univ x]
  rw [hright] at hL2
  have hsquare : ‖spectralEvolution E_pvm t x‖ ^ 2 = ‖x‖ ^ 2 := by
    exact (ENNReal.ofReal_eq_ofReal_iff
      (sq_nonneg ‖spectralEvolution E_pvm t x‖) (sq_nonneg ‖x‖)).mp hL2
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsquare

private theorem spectralEvolution_surjective (E_pvm : PVM E) (t : ℝ) :
    Function.Surjective (spectralEvolution E_pvm t) := by
  intro y
  refine ⟨spectralEvolution E_pvm (-t) y, ?_⟩
  have hmul : spectralEvolution E_pvm t * spectralEvolution E_pvm (-t) = 1 := by
    rw [← spectralEvolution_add, add_neg_cancel, spectralEvolution_zero]
  change (spectralEvolution E_pvm t * spectralEvolution E_pvm (-t)) y = y
  rw [hmul, one_apply_eq_self]

private theorem spectralEvolution_unitary (E_pvm : PVM E) (t : ℝ) :
    spectralEvolution E_pvm t ∈ unitary (E →L[ℂ] E) := by
  let f : E →ₗᵢ[ℂ] E := LinearIsometry.mk (spectralEvolution E_pvm t).toLinearMap
    (spectralEvolution_norm E_pvm t)
  let e : E ≃ₗᵢ[ℂ] E := LinearIsometryEquiv.ofSurjective f
    (spectralEvolution_surjective E_pvm t)
  let u : unitary (E →L[ℂ] E) := Unitary.linearIsometryEquiv.symm e
  have hueq : (u : E →L[ℂ] E) = spectralEvolution E_pvm t := by
    ext x
    change e x = spectralEvolution E_pvm t x
    change f x = spectralEvolution E_pvm t x
    rfl
  rw [← hueq]
  exact u.property

private theorem stonePhase_continuous_left (r : ℝ) :
    Continuous (fun t : ℝ => stonePhase t r) := by
  unfold stonePhase
  fun_prop

private theorem stonePhase_sub_bounded (s t : ℝ) :
    ∀ r, ‖stonePhase t r - stonePhase s r‖ ≤ 2 := by
  intro r
  calc
    ‖stonePhase t r - stonePhase s r‖ ≤
        ‖stonePhase t r‖ + ‖stonePhase s r‖ := norm_sub_le _ _
    _ = 2 := by rw [stonePhase_norm, stonePhase_norm]; norm_num

private theorem spectralEvolution_sub (E_pvm : PVM E) (t s : ℝ) :
    spectralEvolution E_pvm t - spectralEvolution E_pvm s =
      E_pvm.integral (stonePhase t - stonePhase s)
        ((stonePhase_measurable t).sub (stonePhase_measurable s))
        ⟨2, stonePhase_sub_bounded s t⟩ := by
  change E_pvm.integral (stonePhase t) (stonePhase_measurable t)
      ⟨1, stonePhase_bounded t⟩ -
    E_pvm.integral (stonePhase s) (stonePhase_measurable s)
      ⟨1, stonePhase_bounded s⟩ = _
  exact (E_pvm.integral_sub (stonePhase t) (stonePhase s)
    (stonePhase_measurable t) (stonePhase_measurable s)
    ⟨1, stonePhase_bounded t⟩ ⟨1, stonePhase_bounded s⟩
    ⟨2, stonePhase_sub_bounded s t⟩).symm

private theorem phaseDifference_lintegral_tendsto_zero
    (E_pvm : PVM E) (x : E) (s : ℝ) :
    Tendsto
      (fun t : ℝ => ∫⁻ r,
        (↑(‖stonePhase t r - stonePhase s r‖₊ ^ 2) : ENNReal)
          ∂(E_pvm.scalarMeasure x))
      (nhds s) (nhds 0) := by
  have h := tendsto_lintegral_filter_of_dominated_convergence
    (μ := E_pvm.scalarMeasure x)
    (l := nhds s)
    (F := fun t r => (↑(‖stonePhase t r - stonePhase s r‖₊ ^ 2) : ENNReal))
    (f := fun _ => 0) (fun _ => (4 : ENNReal))
    (Filter.Eventually.of_forall fun t =>
      ((((stonePhase_measurable t).sub
        (stonePhase_measurable s)).nnnorm.pow_const 2).coe_nnreal_ennreal))
    (Filter.Eventually.of_forall fun t => ae_of_all _ fun r => by
      change ‖stonePhase t r - stonePhase s r‖ₑ ^ 2 ≤ (4 : ENNReal)
      calc
        ‖stonePhase t r - stonePhase s r‖ₑ ^ 2 =
            ENNReal.ofReal (‖stonePhase t r - stonePhase s r‖ ^ 2) := by
          rw [ENNReal.ofReal_pow (norm_nonneg _) 2, ofReal_norm]
        _ ≤ ENNReal.ofReal (2 ^ 2) := ENNReal.ofReal_le_ofReal
          ((sq_le_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)).2
            (stonePhase_sub_bounded s t r))
        _ = 4 := by norm_num)
    (by
      rw [lintegral_const]
      exact ENNReal.mul_ne_top (by norm_num)
        (E_pvm.scalarMeasure_lt_top x Set.univ).ne)
    (ae_of_all _ fun r => by
      have hcont : Continuous (fun t : ℝ =>
          (↑(‖stonePhase t r - stonePhase s r‖₊ ^ 2) : ENNReal)) := by
        have hdiff : Continuous
            (fun t : ℝ => stonePhase t r - stonePhase s r) :=
          (stonePhase_continuous_left r).sub continuous_const
        have hnnorm : Continuous
            (fun t : ℝ => ‖stonePhase t r - stonePhase s r‖₊) := hdiff.nnnorm
        exact ENNReal.continuous_coe.comp (hnnorm.pow 2)
      have htend : Tendsto
          (fun t : ℝ => (↑(‖stonePhase t r - stonePhase s r‖₊ ^ 2) : ENNReal))
          (nhds s)
          (nhds (↑(‖stonePhase s r - stonePhase s r‖₊ ^ 2) : ENNReal)) :=
        hcont.continuousAt
      simpa only [sub_self, nnnorm_zero,
        zero_pow (by norm_num : (2 : ℕ) ≠ 0), ENNReal.coe_zero]
        using htend)
  simpa only [lintegral_zero] using h

private theorem spectralEvolution_stronglyContinuous (E_pvm : PVM E) (x : E) :
    Continuous (fun t => spectralEvolution E_pvm t x) := by
  rw [continuous_iff_continuousAt]
  intro s
  change Tendsto (fun t => spectralEvolution E_pvm t x) (nhds s)
    (nhds (spectralEvolution E_pvm s x))
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hIntegral := phaseDifference_lintegral_tendsto_zero E_pvm x s
  have hthreshold : 0 < ENNReal.ofReal (ε ^ 2) :=
    ENNReal.ofReal_pos.2 (sq_pos_of_pos hε)
  filter_upwards [hIntegral.eventually (gt_mem_nhds hthreshold)] with t ht
  rw [dist_eq_norm]
  have hop := spectralEvolution_sub E_pvm t s
  have happ := congrArg (fun T : E →L[ℂ] E => T x) hop
  change spectralEvolution E_pvm t x - spectralEvolution E_pvm s x =
    E_pvm.integral (stonePhase t - stonePhase s)
      ((stonePhase_measurable t).sub (stonePhase_measurable s))
      ⟨2, stonePhase_sub_bounded s t⟩ x at happ
  have hL2 := E_pvm.ofReal_norm_sq_integral
    (stonePhase t - stonePhase s)
    ((stonePhase_measurable t).sub (stonePhase_measurable s))
    ⟨2, stonePhase_sub_bounded s t⟩ x
  have hofReal :
      ENNReal.ofReal
          (‖spectralEvolution E_pvm t x - spectralEvolution E_pvm s x‖ ^ 2) <
        ENNReal.ofReal (ε ^ 2) := by
    rw [happ, hL2]
    exact ht
  have hsquare :
      ‖spectralEvolution E_pvm t x - spectralEvolution E_pvm s x‖ ^ 2 < ε ^ 2 :=
    (ENNReal.ofReal_lt_ofReal_iff (sq_pos_of_pos hε)).1 hofReal
  exact (sq_lt_sq₀ (norm_nonneg _) hε.le).1 hsquare

/-- The strongly continuous unitary group assembled from spectral evolution operators. -/
noncomputable def spectralUnitaryGroup (E_pvm : PVM E) :
    StrongContUnitary E where
  toFun := spectralEvolution E_pvm
  isUnitary := by exact spectralEvolution_unitary E_pvm
  zero := by exact spectralEvolution_zero E_pvm
  add := by exact spectralEvolution_add E_pvm
  stronglyContinuous := by exact spectralEvolution_stronglyContinuous E_pvm

private noncomputable def stoneQuotient (t r : ℝ) : ℂ :=
  (Complex.I * (t : ℂ))⁻¹ * (stonePhase t r - stonePhase 0 r)

private theorem stonePhase_hasDerivAt_zero (r : ℝ) :
    HasDerivAt (fun t : ℝ => stonePhase t r) (Complex.I * (r : ℂ)) 0 := by
  have harg : HasDerivAt
      (fun t : ℝ => Complex.I * (t : ℂ) * (r : ℂ))
      (Complex.I * (r : ℂ)) 0 := by
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one, mul_one] using
      (Complex.ofRealCLM.hasDerivAt.const_mul Complex.I).mul_const (r : ℂ)
  unfold stonePhase
  simpa only [Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero, one_mul]
    using harg.cexp

private theorem stoneQuotient_tendsto (r : ℝ) :
    Tendsto (fun t : ℝ => stoneQuotient t r)
      (nhdsWithin 0 {0}ᶜ) (nhds (r : ℂ)) := by
  have hslope := (stonePhase_hasDerivAt_zero r).tendsto_slope_zero
  have hconst : Tendsto (fun _t : ℝ => (-Complex.I : ℂ))
      (nhdsWithin 0 {0}ᶜ) (nhds (-Complex.I)) := tendsto_const_nhds
  have hscaled := hconst.mul hslope
  convert hscaled using 1
  · funext t
    rw [stoneQuotient, zero_add, Complex.real_smul, Complex.ofReal_inv,
      mul_inv_rev, Complex.inv_I]
    ring
  · congr 1
    rw [neg_mul, ← mul_assoc, Complex.I_mul_I, neg_mul, one_mul, neg_neg]

private theorem stoneQuotient_measurable (t : ℝ) : Measurable (stoneQuotient t) := by
  unfold stoneQuotient
  exact measurable_const.mul
    ((stonePhase_measurable t).sub (stonePhase_measurable 0))

private theorem stoneQuotient_bounded (t : ℝ) :
    ∀ r, ‖stoneQuotient t r‖ ≤ ‖(Complex.I * (t : ℂ))⁻¹‖ * 2 := by
  intro r
  rw [stoneQuotient, norm_mul]
  exact mul_le_mul_of_nonneg_left (stonePhase_sub_bounded 0 t r) (norm_nonneg _)

private theorem integral_stoneQuotient (E_pvm : PVM E) (t : ℝ) :
    E_pvm.integral (stoneQuotient t) (stoneQuotient_measurable t)
        ⟨‖(Complex.I * (t : ℂ))⁻¹‖ * 2, stoneQuotient_bounded t⟩ =
      (Complex.I * (t : ℂ))⁻¹ •
        (spectralEvolution E_pvm t - spectralEvolution E_pvm 0) := by
  let c : ℂ := (Complex.I * (t : ℂ))⁻¹
  let f : ℝ → ℂ := stonePhase t - stonePhase 0
  have hf : Measurable f := (stonePhase_measurable t).sub (stonePhase_measurable 0)
  have hbddf : ∃ C, ∀ r, ‖f r‖ ≤ C := ⟨2, stonePhase_sub_bounded 0 t⟩
  have hbddMul : ∃ C, ∀ r, ‖c * f r‖ ≤ C :=
    ⟨‖(Complex.I * (t : ℂ))⁻¹‖ * 2, stoneQuotient_bounded t⟩
  have hfun : stoneQuotient t = fun r => c * f r := by
    funext r
    rfl
  calc
    E_pvm.integral (stoneQuotient t) (stoneQuotient_measurable t) hbddMul =
        E_pvm.integral (fun r => c * f r) (measurable_const.mul hf) hbddMul :=
      E_pvm.integral_congr hfun _ _ _ _
    _ = c • E_pvm.integral f hf hbddf :=
      E_pvm.integral_const_mul_local c f hf hbddf hbddMul
    _ = c • (spectralEvolution E_pvm t - spectralEvolution E_pvm 0) := by
      rw [spectralEvolution_sub]

private theorem spectralDifferenceQuotient_eq_integral
    (E_pvm : PVM E) (t : ℝ) (x : E) :
    (Complex.I * (t : ℂ))⁻¹ • (spectralEvolution E_pvm t x - x) =
      E_pvm.integral (stoneQuotient t) (stoneQuotient_measurable t)
        ⟨‖(Complex.I * (t : ℂ))⁻¹‖ * 2, stoneQuotient_bounded t⟩ x := by
  rw [integral_stoneQuotient]
  rw [smul_apply, sub_apply, spectralEvolution_zero, one_apply_eq_self]

private theorem stoneQuotient_norm_le (t r : ℝ) (ht : t ≠ 0) :
    ‖stoneQuotient t r‖ ≤ ‖r‖ := by
  have hnum : ‖stonePhase t r - stonePhase 0 r‖ ≤ ‖t * r‖ := by
    rw [stonePhase_zero]
    change ‖Complex.exp (Complex.I * (t : ℂ) * (r : ℂ)) - 1‖ ≤ ‖t * r‖
    rw [mul_assoc, ← Complex.ofReal_mul]
    exact Real.norm_exp_I_mul_ofReal_sub_one_le
  rw [stoneQuotient, norm_mul]
  calc
    ‖(Complex.I * (t : ℂ))⁻¹‖ * ‖stonePhase t r - stonePhase 0 r‖ ≤
        ‖(Complex.I * (t : ℂ))⁻¹‖ * ‖t * r‖ :=
      mul_le_mul_of_nonneg_left hnum (norm_nonneg _)
    _ = ‖r‖ := by
      rw [norm_inv, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, norm_mul,
        ← mul_assoc, inv_mul_cancel₀ (norm_ne_zero_iff.mpr ht), one_mul]

private theorem quotientDifference_lintegral_tendsto_zero
    (E_pvm : PVM E)
    (x : (E_pvm.unboundedIntegral ((↑) : ℝ → ℂ)
      Complex.continuous_ofReal.measurable).domain) :
    Tendsto
      (fun t : ℝ => ∫⁻ r,
        (↑(‖stoneQuotient t r - (r : ℂ)‖₊ ^ 2) : ENNReal)
          ∂(E_pvm.scalarMeasure (x : E)))
      (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
  have hcoordMeas : Measurable
      (fun r : ℝ => (↑(‖(r : ℂ)‖₊ ^ 2) : ENNReal)) :=
    ((Complex.continuous_ofReal.measurable.nnnorm.pow_const 2).coe_nnreal_ennreal)
  have h := tendsto_lintegral_filter_of_dominated_convergence
    (μ := E_pvm.scalarMeasure (x : E))
    (l := nhdsWithin 0 {0}ᶜ)
    (F := fun t r => (↑(‖stoneQuotient t r - (r : ℂ)‖₊ ^ 2) : ENNReal))
    (f := fun _ => 0)
    (fun r => 4 * (↑(‖(r : ℂ)‖₊ ^ 2) : ENNReal))
    (Filter.Eventually.of_forall fun t =>
      (((stoneQuotient_measurable t).sub
        Complex.continuous_ofReal.measurable).nnnorm.pow_const 2).coe_nnreal_ennreal)
    (by
      filter_upwards [self_mem_nhdsWithin] with t ht
      apply ae_of_all
      intro r
      have ht0 : t ≠ 0 := ht
      have hnorm : ‖stoneQuotient t r - (r : ℂ)‖ ≤ 2 * ‖r‖ := by
        calc
          ‖stoneQuotient t r - (r : ℂ)‖ ≤
              ‖stoneQuotient t r‖ + ‖(r : ℂ)‖ := norm_sub_le _ _
          _ ≤ ‖r‖ + ‖r‖ := add_le_add (stoneQuotient_norm_le t r ht0)
            (Complex.norm_real r).le
          _ = 2 * ‖r‖ := by ring
      change ‖stoneQuotient t r - (r : ℂ)‖ₑ ^ 2 ≤
        4 * (↑(‖(r : ℂ)‖₊ ^ 2) : ENNReal)
      calc
        ‖stoneQuotient t r - (r : ℂ)‖ₑ ^ 2 =
            ENNReal.ofReal (‖stoneQuotient t r - (r : ℂ)‖ ^ 2) := by
          rw [ENNReal.ofReal_pow (norm_nonneg _) 2, ofReal_norm]
        _ ≤ ENNReal.ofReal ((2 * ‖r‖) ^ 2) := ENNReal.ofReal_le_ofReal
          ((sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by norm_num) (norm_nonneg _))).2 hnorm)
        _ = 4 * (↑(‖(r : ℂ)‖₊ ^ 2) : ENNReal) := by
          rw [mul_pow, ENNReal.ofReal_mul (sq_nonneg (2 : ℝ)),
            ENNReal.ofReal_pow (norm_nonneg r) 2, Complex.nnnorm_real,
            ENNReal.coe_pow, ← enorm_eq_nnnorm, ← ofReal_norm]
          norm_num)
    (by
      rw [lintegral_const_mul 4 hcoordMeas]
      exact ENNReal.mul_ne_top (by norm_num) x.property.ne)
    (ae_of_all _ fun r => by
      have hconstR : Tendsto (fun _t : ℝ => (r : ℂ)) (nhdsWithin 0 {0}ᶜ)
          (nhds (r : ℂ)) := tendsto_const_nhds
      have hsub := (stoneQuotient_tendsto r).sub hconstR
      have hreal := ENNReal.tendsto_ofReal (hsub.norm.pow 2)
      convert hreal using 1
      · funext t
        rw [ENNReal.ofReal_pow (norm_nonneg _) 2, ofReal_norm,
          enorm_eq_nnnorm, ENNReal.coe_pow]
      · rw [sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
          ENNReal.ofReal_zero])
  simpa only [lintegral_zero] using h

private theorem spectralDifferenceQuotient_tendsto
    (E_pvm : PVM E)
    (x : (E_pvm.unboundedIntegral ((↑) : ℝ → ℂ)
      Complex.continuous_ofReal.measurable).domain) :
    Tendsto
      (fun t : ℝ => (Complex.I * (t : ℂ))⁻¹ •
        (spectralEvolution E_pvm t (x : E) - (x : E)))
      (nhdsWithin 0 {0}ᶜ)
      (nhds (E_pvm.unboundedIntegral ((↑) : ℝ → ℂ)
        Complex.continuous_ofReal.measurable x)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hIntegral := quotientDifference_lintegral_tendsto_zero E_pvm x
  have hthreshold : 0 < ENNReal.ofReal (ε ^ 2) :=
    ENNReal.ofReal_pos.2 (sq_pos_of_pos hε)
  filter_upwards [hIntegral.eventually (gt_mem_nhds hthreshold)] with t ht
  rw [dist_eq_norm]
  have hL2 := E_pvm.ofReal_norm_sq_integral_sub_unboundedIntegral
    (stoneQuotient t) (stoneQuotient_measurable t)
    ⟨‖(Complex.I * (t : ℂ))⁻¹‖ * 2, stoneQuotient_bounded t⟩
    ((↑) : ℝ → ℂ) Complex.continuous_ofReal.measurable x
  have hofReal :
      ENNReal.ofReal
          (‖(Complex.I * (t : ℂ))⁻¹ •
            (spectralEvolution E_pvm t (x : E) - (x : E)) -
              E_pvm.unboundedIntegral ((↑) : ℝ → ℂ)
                Complex.continuous_ofReal.measurable x‖ ^ 2) <
        ENNReal.ofReal (ε ^ 2) := by
    rw [spectralDifferenceQuotient_eq_integral]
    exact hL2.trans_lt (by simpa only [ENNReal.coe_pow] using ht)
  have hsquare :
      ‖(Complex.I * (t : ℂ))⁻¹ •
          (spectralEvolution E_pvm t (x : E) - (x : E)) -
        E_pvm.unboundedIntegral ((↑) : ℝ → ℂ)
          Complex.continuous_ofReal.measurable x‖ ^ 2 < ε ^ 2 :=
    (ENNReal.ofReal_lt_ofReal_iff (sq_pos_of_pos hε)).1 hofReal
  exact (sq_lt_sq₀ (norm_nonneg _) hε.le).1 hsquare

private theorem coordinateOperator_le_phaseGenerator (E_pvm : PVM E) :
    E_pvm.unboundedIntegral ((↑) : ℝ → ℂ)
        Complex.continuous_ofReal.measurable ≤
      (spectralUnitaryGroup E_pvm).generator := by
  let A := E_pvm.unboundedIntegral ((↑) : ℝ → ℂ)
    Complex.continuous_ofReal.measurable
  let U := spectralUnitaryGroup E_pvm
  have hdomain : A.domain ≤ U.generator.domain := by
    intro x hx
    apply (U.mem_generator_domain_iff x).2
    let xA : A.domain := ⟨x, hx⟩
    refine ⟨A xA, ?_⟩
    exact spectralDifferenceQuotient_tendsto E_pvm xA
  refine ⟨hdomain, ?_⟩
  intro x y hxy
  have hcoord := spectralDifferenceQuotient_tendsto E_pvm x
  have hgenerator := U.tendsto_generator y
  change Tendsto
    (fun t : ℝ => (Complex.I * (t : ℂ))⁻¹ •
      (spectralEvolution E_pvm t (y : E) - (y : E)))
    (nhdsWithin 0 {0}ᶜ) (nhds (U.generator y)) at hgenerator
  rw [← hxy] at hgenerator
  exact tendsto_nhds_unique hcoord hgenerator

private noncomputable def quotientTime (n : ℕ) : ℝ :=
  1 / ((n : ℝ) + 1)

private theorem quotientTime_tendsto :
    Tendsto quotientTime atTop (nhdsWithin 0 {0}ᶜ) := by
  apply tendsto_nhdsWithin_iff.2
  refine ⟨tendsto_one_div_add_atTop_nhds_zero_nat, ?_⟩
  apply Filter.Eventually.of_forall
  intro n
  change quotientTime n ≠ 0
  unfold quotientTime
  positivity

private theorem phaseGenerator_coordinate_integrable (E_pvm : PVM E)
    (x : (spectralUnitaryGroup E_pvm).generator.domain) :
    ∫⁻ r, ‖(r : ℂ)‖₊ ^ 2 ∂(E_pvm.scalarMeasure (x : E)) < ⊤ := by
  let U := spectralUnitaryGroup E_pvm
  let q : ℕ → ℝ → ℂ := fun n => stoneQuotient (quotientTime n)
  let L : ENNReal := ENNReal.ofReal (‖U.generator x‖ ^ 2)
  have hquotient : Tendsto
      (fun n => (Complex.I * (quotientTime n : ℂ))⁻¹ •
        (spectralEvolution E_pvm (quotientTime n) (x : E) - (x : E)))
      atTop (nhds (U.generator x)) := by
    have hgenerator := U.tendsto_generator x
    change Tendsto
      (fun t : ℝ => (Complex.I * (t : ℂ))⁻¹ •
        (spectralEvolution E_pvm t (x : E) - (x : E)))
      (nhdsWithin 0 {0}ᶜ) (nhds (U.generator x)) at hgenerator
    exact hgenerator.comp quotientTime_tendsto
  have hnorm : Tendsto
      (fun n => ENNReal.ofReal
        (‖(Complex.I * (quotientTime n : ℂ))⁻¹ •
          (spectralEvolution E_pvm (quotientTime n) (x : E) - (x : E))‖ ^ 2))
      atTop (nhds L) := by
    exact ENNReal.tendsto_ofReal (hquotient.norm.pow 2)
  have hintegrals : Tendsto
      (fun n => ∫⁻ r, (↑(‖q n r‖₊ ^ 2) : ENNReal)
        ∂(E_pvm.scalarMeasure (x : E)))
      atTop (nhds L) := by
    apply hnorm.congr'
    apply Filter.Eventually.of_forall
    intro n
    have hL2 := E_pvm.ofReal_norm_sq_integral
      (stoneQuotient (quotientTime n))
      (stoneQuotient_measurable (quotientTime n))
      ⟨‖(Complex.I * (quotientTime n : ℂ))⁻¹‖ * 2,
        stoneQuotient_bounded (quotientTime n)⟩ (x : E)
    rw [← spectralDifferenceQuotient_eq_integral] at hL2
    simpa only [q, ENNReal.coe_pow] using hL2
  have hpointwise : ∀ r, Tendsto
      (fun n => (↑(‖q n r‖₊ ^ 2) : ENNReal)) atTop
      (nhds (↑(‖(r : ℂ)‖₊ ^ 2) : ENNReal)) := by
    intro r
    have hq := (stoneQuotient_tendsto r).comp quotientTime_tendsto
    have hreal := ENNReal.tendsto_ofReal (hq.norm.pow 2)
    convert hreal using 1
    · funext n
      rw [ENNReal.ofReal_pow (norm_nonneg _) 2, ofReal_norm,
        enorm_eq_nnnorm, ENNReal.coe_pow]
      rfl
    · rw [ENNReal.ofReal_pow (norm_nonneg _) 2, ofReal_norm,
        enorm_eq_nnnorm, ENNReal.coe_pow]
  calc
    ∫⁻ r, ‖(r : ℂ)‖₊ ^ 2 ∂(E_pvm.scalarMeasure (x : E)) =
        ∫⁻ r, liminf (fun n => (↑(‖q n r‖₊ ^ 2) : ENNReal)) atTop
          ∂(E_pvm.scalarMeasure (x : E)) := by
      apply lintegral_congr
      intro r
      exact (hpointwise r).liminf_eq.symm
    _ ≤ liminf
        (fun n => ∫⁻ r, (↑(‖q n r‖₊ ^ 2) : ENNReal)
          ∂(E_pvm.scalarMeasure (x : E))) atTop := by
      apply lintegral_liminf_le
      intro n
      exact Measurable.coe_nnreal_ennreal
        ((stoneQuotient_measurable (quotientTime n)).nnnorm.pow_const 2)
    _ = L := hintegrals.liminf_eq
    _ < ⊤ := ENNReal.ofReal_lt_top

private theorem phaseGenerator_domain_le_coordinateOperator (E_pvm : PVM E) :
    (spectralUnitaryGroup E_pvm).generator.domain ≤
      (E_pvm.unboundedIntegral ((↑) : ℝ → ℂ)
        Complex.continuous_ofReal.measurable).domain := by
  intro x hx
  rw [E_pvm.mem_domain_unboundedIntegral]
  exact phaseGenerator_coordinate_integrable E_pvm ⟨x, hx⟩

private theorem spectralUnitaryGroup_generator (E_pvm : PVM E) :
    (spectralUnitaryGroup E_pvm).generator =
      E_pvm.unboundedIntegral ((↑) : ℝ → ℂ)
        Complex.continuous_ofReal.measurable := by
  have hle := coordinateOperator_le_phaseGenerator E_pvm
  have hdomain :
      (E_pvm.unboundedIntegral ((↑) : ℝ → ℂ)
          Complex.continuous_ofReal.measurable).domain =
        (spectralUnitaryGroup E_pvm).generator.domain :=
    le_antisymm hle.1 (phaseGenerator_domain_le_coordinateOperator E_pvm)
  exact (LinearPMap.eq_of_le_of_domain_eq hle hdomain).symm

/-- The unitary group obtained by integrating the phases `exp (i t r)` against a PVM. -/
noncomputable def PVM.phaseUnitaryGroup (E_pvm : PVM E) : StrongContUnitary E :=
  spectralUnitaryGroup E_pvm

/-- The generator of the phase unitary group is integration against the real coordinate. -/
theorem PVM.phaseUnitaryGroup_generator (E_pvm : PVM E) :
    E_pvm.phaseUnitaryGroup.generator =
      E_pvm.unboundedIntegral ((↑) : ℝ → ℂ)
        Complex.continuous_ofReal.measurable := by
  simpa only [PVM.phaseUnitaryGroup] using spectralUnitaryGroup_generator E_pvm

/-- A self-adjoint operator generates a strongly continuous one-parameter unitary group. -/
noncomputable def selfAdjointGeneratesUnitaryGroup
    (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) :
    StrongContUnitary E :=
  (Classical.choose (spectral_theorem_existence A hA)).phaseUnitaryGroup

/-- The phase unitary group constructed from a self-adjoint operator has generator `A`. -/
theorem selfAdjoint_generates_unitary_group_generator
    (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) :
    (selfAdjointGeneratesUnitaryGroup A hA).generator = A := by
  unfold selfAdjointGeneratesUnitaryGroup
  rw [PVM.phaseUnitaryGroup_generator]
  exact Classical.choose_spec (spectral_theorem_existence A hA)
