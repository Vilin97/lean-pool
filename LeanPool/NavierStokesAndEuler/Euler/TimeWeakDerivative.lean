/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TerminalTimePrimitive
public import Mathlib.Analysis.InnerProductSpace.Calculus

@[expose] public section

/-!
# Recovering actual time derivatives from the zero-endpoint weak identity

The terminal primitive is an explicit integral of an L² equivalence class.
Integration by parts and the kernel of its initial trace identify the strong
momentum representative used by the mean and transverse variational inverses.
-/

noncomputable section

namespace EulerTimeWeakDerivative

open MeasureTheory Set InnerProductSpace EulerTimeLp EulerTerminalTimePrimitive
  EulerVolterraConvolution
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
/-- Taking norms preserves absolute continuity by the reverse triangle inequality. -/
theorem absolutelyContinuous_norm {a b : ℝ} {f : ℝ → E}
    (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun t => ‖f t‖) a b := by
  apply squeeze_zero (fun _ => Finset.sum_nonneg (fun _ _ => dist_nonneg)) ?_ hf
  intro I
  apply Finset.sum_le_sum
  intro i _
  simpa only [dist_eq_norm] using dist_norm_norm_le (f (I.2 i).1) (f (I.2 i).2)

/-- Real inner products of absolutely continuous Hilbert-valued paths are
absolutely continuous; polarization reduces this to scalar products. -/
theorem absolutelyContinuous_inner {a b : ℝ} {f g : ℝ → E}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : AbsolutelyContinuousOnInterval g a b) :
    AbsolutelyContinuousOnInterval (fun t => ⟪f t, g t⟫_ℝ) a b := by
  have hfn : AbsolutelyContinuousOnInterval (fun t => ‖f t‖) a b :=
    absolutelyContinuous_norm hf
  have hgn : AbsolutelyContinuousOnInterval (fun t => ‖g t‖) a b :=
    absolutelyContinuous_norm hg
  have hsum : AbsolutelyContinuousOnInterval (fun t => ‖f t + g t‖) a b :=
    absolutelyContinuous_norm (hf.add hg)
  have he : (fun t => ⟪f t, g t⟫_ℝ) =
      (fun t => (1 / 2 : ℝ) *
        (‖f t + g t‖ * ‖f t + g t‖ - ‖f t‖ * ‖f t‖ - ‖g t‖ * ‖g t‖)) := by
    funext t
    rw [real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two]
    ring
  rw [he]
  exact (((hsum.mul hsum).sub (hfn.mul hfn)).sub (hgn.mul hgn)).const_mul (1 / 2)

variable [CompleteSpace E]

/-- Exact integration by parts for the genuine L² terminal primitives. -/
theorem primitive_inner_identity (T : ℝ) (hT : 0 ≤ T) (f v : TimeLp T E) :
    ⟪primitiveTimeLp T hT f, v⟫_ℝ + ⟪f, primitiveTimeLp T hT v⟫_ℝ =
      -⟪initialTrace T hT f, initialTrace T hT v⟫_ℝ := by
  let φ : ℝ → ℝ := fun t => ⟪realPrimitive T f t, realPrimitive T v t⟫_ℝ
  have hφ : AbsolutelyContinuousOnInterval φ 0 T :=
    absolutelyContinuous_inner (realPrimitive_absolutelyContinuous T f)
      (realPrimitive_absolutelyContinuous T v)
  have hftc : (∫ t, deriv φ t ∂timeMeasure T) = φ T - φ 0 := by
    change (∫ t in Icc (0 : ℝ) T, deriv φ t) = _
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT]
    exact hφ.integral_deriv_eq_sub
  calc
    ⟪primitiveTimeLp T hT f, v⟫_ℝ + ⟪f, primitiveTimeLp T hT v⟫_ℝ =
        ∫ t, ⟪(primitiveTimeLp T hT f : ℝ → E) t, v t⟫_ℝ +
          ⟪f t, (primitiveTimeLp T hT v : ℝ → E) t⟫_ℝ ∂timeMeasure T := by
      rw [L2.inner_def, L2.inner_def]
      exact (integral_add (L2.integrable_inner (primitiveTimeLp T hT f) v)
        (L2.integrable_inner f (primitiveTimeLp T hT v))).symm
    _ = ∫ t, deriv φ t ∂timeMeasure T := by
      apply integral_congr_ae
      filter_upwards [primitiveTimeLp_ae T hT f, primitiveTimeLp_ae T hT v,
        realPrimitive_hasDerivAt_ae T f, realPrimitive_hasDerivAt_ae T v]
        with t hf hv hdf hdv
      rw [hf, hv]
      exact (hdf.inner ℝ hdv).deriv.symm
    _ = -⟪initialTrace T hT f, initialTrace T hT v⟫_ℝ := by
      rw [hftc]
      change ⟪realPrimitive T f T, realPrimitive T v T⟫_ℝ -
          ⟪realPrimitive T f 0, realPrimitive T v 0⟫_ℝ = _
      rw [realPrimitive_terminal, realPrimitive_terminal, inner_zero_left, zero_sub]
      rfl

/-- Zero-endpoint tests remove the boundary term in primitive integration by parts. -/
theorem primitive_inner_zero_trace (T : ℝ) (hT : 0 ≤ T) (f v : TimeLp T E)
    (hv : initialTrace T hT v = 0) :
    ⟪primitiveTimeLp T hT f, v⟫_ℝ = -⟪f, primitiveTimeLp T hT v⟫_ℝ := by
  have h := primitive_inner_identity T hT f v
  rw [hv, inner_zero_right, neg_zero] at h
  linarith

/-- An actual constant time field, embedded in Bochner L². -/
def constantField (T : ℝ) (hT : 0 ≤ T) (c : E) : TimeLp T E :=
  pathLp T hT (ContinuousMap.const (Icc (0 : ℝ) T) c)

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- The Bochner constant has its literal pointwise representative almost everywhere. -/
theorem constantField_ae (T : ℝ) (hT : 0 ≤ T) (c : E) :
    (constantField T hT c : ℝ → E) =ᵐ[timeMeasure T] fun _ => c :=
  pathLp_ae T hT (ContinuousMap.const (Icc (0 : ℝ) T) c)

omit [CompleteSpace E] in
/-- The trace of the primitive is minus the Bochner integral of the derivative. -/
theorem initialTrace_eq_neg_integral (T : ℝ) (hT : 0 ≤ T) (u : TimeLp T E) :
    initialTrace T hT u = -(∫ t, u t ∂timeMeasure T) := by
  rw [initialTrace_eq_integral, intervalIntegral.integral_of_le hT]
  congr 1
  exact (integral_Icc_eq_integral_Ioc (f := fun t => u t)).symm

/-- Constant fields pair only with the initial trace of a terminal primitive. -/
theorem constantField_inner (T : ℝ) (hT : 0 ≤ T) (c : E) (v : TimeLp T E) :
    ⟪constantField T hT c, v⟫_ℝ = -⟪c, initialTrace T hT v⟫_ℝ := by
  calc
    ⟪constantField T hT c, v⟫_ℝ = ∫ t, ⟪c, v t⟫_ℝ ∂timeMeasure T := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [constantField_ae T hT c] with t ht
      rw [ht]
    _ = ⟪c, ∫ t, v t ∂timeMeasure T⟫_ℝ :=
      (innerSL ℝ c).integral_comp_comm ((Lp.memLp v).integrable (by norm_num))
    _ = -⟪c, initialTrace T hT v⟫_ℝ := by
      rw [initialTrace_eq_neg_integral, inner_neg_right, neg_neg]

/-- The initial trace of a constant derivative is its value times minus the length. -/
theorem initialTrace_constantField (T : ℝ) (hT : 0 ≤ T) (c : E) :
    initialTrace T hT (constantField T hT c) = (-T) • c := by
  rw [initialTrace_eq_neg_integral]
  rw [integral_congr_ae (constantField_ae T hT c), integral_const]
  simp only [Measure.real_def, timeMeasure, Measure.restrict_apply_univ, Real.volume_Icc,
    sub_zero, ENNReal.toReal_ofReal hT, neg_smul]

/-- Orthogonality to all zero-trace derivatives forces an actual constant L² field. -/
theorem exists_constant_of_zero_trace_orthogonal (T : ℝ) (hT : 0 < T) (r : TimeLp T E)
    (hr : ∀ v : TimeLp T E, initialTrace T hT.le v = 0 → ⟪r, v⟫_ℝ = 0) :
    ∃ c : E, r = constantField T hT.le c := by
  let c : E := (-T)⁻¹ • initialTrace T hT.le r
  let v := r - constantField T hT.le c
  have hc : initialTrace T hT.le (constantField T hT.le c) = initialTrace T hT.le r := by
    rw [initialTrace_constantField]
    dsimp only [c]
    rw [smul_smul, mul_inv_cancel₀ (neg_ne_zero.mpr hT.ne'), one_smul]
  have hv : initialTrace T hT.le v = 0 := by
    simp only [v, map_sub, hc, sub_self]
  have hcv : ⟪constantField T hT.le c, v⟫_ℝ = 0 := by
    rw [constantField_inner, hv, inner_zero_right, neg_zero]
  have hzero : v = 0 := by
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    change ⟪r - constantField T hT.le c, v⟫_ℝ = 0
    rw [inner_sub_left, hr v hv, hcv, sub_zero]
  exact ⟨c, sub_eq_zero.mp hzero⟩

/-- The zero-endpoint weak derivative identity constructs an actual momentum
representative: a terminal primitive plus a constant. -/
theorem weak_derivative_eq_primitive_add_constant (T : ℝ) (hT : 0 < T)
    (p h : TimeLp T E)
    (hweak : ∀ v : TimeLp T E, initialTrace T hT.le v = 0 →
      ⟪p, v⟫_ℝ = -⟪h, primitiveTimeLp T hT.le v⟫_ℝ) :
    ∃ c : E, p = primitiveTimeLp T hT.le h + constantField T hT.le c := by
  obtain ⟨c, hc⟩ := exists_constant_of_zero_trace_orthogonal T hT
    (p - primitiveTimeLp T hT.le h) (by
      intro v hv
      rw [inner_sub_left, hweak v hv, primitive_inner_zero_trace T hT.le h v hv, sub_self])
  refine ⟨c, ?_⟩
  rw [← hc]
  abel

/-- The weak identity supplies a genuine absolutely continuous representative
whose almost-everywhere derivative is the prescribed momentum forcing. -/
theorem exists_ac_representative_of_weak (T : ℝ) (hT : 0 < T)
    (p h : TimeLp T E)
    (hweak : ∀ v : TimeLp T E, initialTrace T hT.le v = 0 →
      ⟪p, v⟫_ℝ = -⟪h, primitiveTimeLp T hT.le v⟫_ℝ) :
    ∃ η : ℝ → E,
      AbsolutelyContinuousOnInterval η 0 T ∧
      (p : ℝ → E) =ᵐ[timeMeasure T] η ∧
      ∀ᵐ t ∂timeMeasure T, HasDerivAt η (h t) t := by
  obtain ⟨c, hc⟩ := weak_derivative_eq_primitive_add_constant T hT p h hweak
  refine ⟨fun t => realPrimitive T h t + c, ?_, ?_, ?_⟩
  · exact (realPrimitive_absolutelyContinuous T h).add
      ((LipschitzWith.const c).lipschitzOnWith.absolutelyContinuousOnInterval)
  · rw [hc]
    filter_upwards [Lp.coeFn_add (primitiveTimeLp T hT.le h) (constantField T hT.le c),
      primitiveTimeLp_ae T hT.le h, constantField_ae T hT.le c] with t ha hp hconst
    simpa only [Pi.add_apply, hp, hconst] using ha
  · filter_upwards [realPrimitive_hasDerivAt_ae T h] with t ht
    exact ht.add_const c

end EulerTimeWeakDerivative
