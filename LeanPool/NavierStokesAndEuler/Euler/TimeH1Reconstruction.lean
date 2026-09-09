/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TimeH1PointwiseBounds
public import LeanPool.NavierStokesAndEuler.Euler.TimeWeakDerivative
public import LeanPool.NavierStokesAndEuler.Euler.TimeLpCoefficientGevrey

@[expose] public section

/-!
# A bounded reconstruction of genuine time-H¹ fields

The pair of L² fields `(p,q)` determines a continuous path by
`mean(p) - mean(Jq) + Jq`. For an actual absolutely continuous representative
of `p` with derivative `q`, this is that representative. Thus parameter
derivatives and all-order bounds pass through one fixed bounded linear map.
-/

noncomputable section

open scoped ContDiff

namespace EulerTimeH1Reconstruction

open Set MeasureTheory ContinuousLinearMap EulerTimeLp EulerTerminalTimePrimitive
  EulerTimeWeakDerivative EulerTimeH1PointwiseBounds EulerTimeLpCoefficientGevrey
  EulerOperatorGevreyCalculus EulerGevrey

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The actual time average, expressed using the terminal primitive's initial trace. -/
def mean (T : ℝ) (hT : 0 ≤ T) : TimeLp T E →L[ℝ] E :=
  (-T)⁻¹ • initialTrace T hT

/-- The constant part of the reconstruction. -/
def valuePart (T : ℝ) (hT : 0 ≤ T) : TimeLp T E →L[ℝ] C(Icc (0 : ℝ) T, E) :=
  (ContinuousLinearMap.const ℝ (Icc (0 : ℝ) T)).comp (mean T hT)

/-- The mean-zero primitive part of the reconstruction. -/
def derivativePart (T : ℝ) (hT : 0 ≤ T) : TimeLp T E →L[ℝ] C(Icc (0 : ℝ) T, E) :=
  terminalPrimitive T hT - (valuePart T hT).comp (primitiveTimeLp T hT)

/-- One fixed bounded linear map from the value/derivative pair to its continuous representative. -/
def reconstruction (T : ℝ) (hT : 0 ≤ T) :
    (TimeLp T E × TimeLp T E) →L[ℝ] C(Icc (0 : ℝ) T, E) :=
  (valuePart T hT).comp (fst ℝ (TimeLp T E) (TimeLp T E)) +
    (derivativePart T hT).comp (snd ℝ (TimeLp T E) (TimeLp T E))

omit [CompleteSpace E] in
/-- The reconstruction is the literal average plus mean-zero terminal primitive. -/
theorem reconstruction_apply (T : ℝ) (hT : 0 ≤ T) (p q : TimeLp T E)
    (t : Icc (0 : ℝ) T) :
    reconstruction T hT (p,q) t =
      mean T hT p + (terminalPrimitive T hT q t - mean T hT (primitiveTimeLp T hT q)) := rfl

/-- Constant fields have their actual value as time average. -/
theorem mean_constantField (T : ℝ) (hT : 0 < T) (v : E) :
    mean T hT.le (constantField T hT.le v) = v := by
  change (-T)⁻¹ • initialTrace T hT.le (constantField T hT.le v) = v
  rw [initialTrace_constantField, smul_smul, inv_mul_cancel₀ (neg_ne_zero.mpr hT.ne'), one_smul]

omit [CompleteSpace E] in
/-- The mean has the expected inverse-square-root time bound. -/
theorem mean_norm_le (T : ℝ) (hT : 0 ≤ T) (p : TimeLp T E) :
    ‖mean T hT p‖ ≤ (T⁻¹ * Real.sqrt T) * ‖p‖ := by
  have htrace : ‖initialTrace T hT p‖ ≤ Real.sqrt T * ‖p‖ :=
    ((initialTrace (E := E) T hT).le_opNorm p).trans
      (mul_le_mul_of_nonneg_right (initialTrace_norm_le (E := E) T hT) (norm_nonneg p))
  change ‖(-T)⁻¹ • initialTrace T hT p‖ ≤ _
  rw [norm_smul, norm_inv, norm_neg, Real.norm_of_nonneg hT]
  exact (mul_le_mul_of_nonneg_left htrace (inv_nonneg.mpr hT)).trans_eq (mul_assoc _ _ _).symm

omit [CompleteSpace E] in
/-- Uniform time evaluation is controlled by the actual L² value and derivative. -/
theorem reconstruction_norm_le (T : ℝ) (hT : 0 < T) (p q : TimeLp T E) :
    ‖reconstruction T hT.le (p,q)‖ ≤
      (T⁻¹ * Real.sqrt T) * ‖p‖ + (2 * Real.sqrt T) * ‖q‖ := by
  have hJ : ‖primitiveTimeLp T hT.le q‖ ≤ T*‖q‖ :=
    ((primitiveTimeLp (E := E) T hT.le).le_opNorm q).trans
      (mul_le_mul_of_nonneg_right (primitive_norm_le_time (E := E) T hT.le) (norm_nonneg q))
  have hmJ : ‖mean T hT.le (primitiveTimeLp T hT.le q)‖ ≤ Real.sqrt T * ‖q‖ := by
    apply (mean_norm_le T hT.le _).trans
    have he : (T⁻¹ * Real.sqrt T) * (T*‖q‖) = Real.sqrt T * ‖q‖ := by
      field_simp
    exact (mul_le_mul_of_nonneg_left hJ (by positivity)).trans_eq he
  apply (ContinuousMap.norm_le _ (by positivity)).2
  intro t
  have hterm : ‖terminalPrimitive T hT.le q t‖ ≤ Real.sqrt T * ‖q‖ :=
    ((terminalPrimitive T hT.le q).norm_coe_le_norm t).trans
      (((terminalPrimitive (E := E) T hT.le).le_opNorm q).trans
        (mul_le_mul_of_nonneg_right (terminalPrimitive_norm_le (E := E) T hT.le) (norm_nonneg q)))
  rw [reconstruction_apply]
  exact (norm_add_le _ _).trans ((add_le_add (mean_norm_le T hT.le p)
    ((norm_sub_le _ _).trans (add_le_add hterm hmJ))).trans_eq (by ring))

omit [CompleteSpace E] in
/-- The constant reconstruction component has the sharp polynomial trace cost. -/
theorem valuePart_norm_le (T : ℝ) (hT : 0 < T) :
    ‖valuePart (E := E) T hT.le‖ ≤ T⁻¹ * Real.sqrt T := by
  apply opNorm_le_bound _ (by positivity)
  intro p
  have h := reconstruction_norm_le T hT p 0
  simpa only [reconstruction, comp_apply, add_apply, coe_fst', coe_snd',
    map_zero, add_zero, norm_zero, mul_zero] using h

omit [CompleteSpace E] in
/-- The mean-zero primitive reconstruction has only a square-root time cost. -/
theorem derivativePart_norm_le (T : ℝ) (hT : 0 < T) :
    ‖derivativePart (E := E) T hT.le‖ ≤ 2 * Real.sqrt T := by
  apply opNorm_le_bound _ (by positivity)
  intro q
  have h := reconstruction_norm_le T hT 0 q
  simpa only [reconstruction, comp_apply, add_apply, coe_fst', coe_snd',
    map_zero, zero_add, norm_zero, mul_zero] using h

/-- The reconstructed path equals every genuine AC representative with the specified derivative. -/
theorem reconstruction_eq_path (T : ℝ) (hT : 0 < T) (p q : TimeLp T E) (η : ℝ → E)
    (hη : AbsolutelyContinuousOnInterval η 0 T)
    (hp : (p : ℝ → E) =ᵐ[timeMeasure T] η)
    (hq : ∀ᵐ t ∂timeMeasure T, HasDerivAt η (q t) t)
    (t : Icc (0 : ℝ) T) :
    reconstruction T hT.le (p,q) t = η t := by
  have hpEq : p = primitiveTimeLp T hT.le q + constantField T hT.le (η T) := by
    apply Lp.ext
    filter_upwards [hp, primitiveTimeLp_ae T hT.le q,
      constantField_ae T hT.le (η T),
      Lp.coeFn_add (primitiveTimeLp T hT.le q) (constantField T hT.le (η T)),
      ae_restrict_mem measurableSet_Icc] with s hps hJs hcs hs hsmem
    change p s = (primitiveTimeLp T hT.le q + constantField T hT.le (η T)) s
    rw [hps, hs, Pi.add_apply, hJs, hcs]
    exact eq_primitive_add_terminal T hT.le q η hη hq s hsmem
  have hm : mean T hT.le p = mean T hT.le (primitiveTimeLp T hT.le q) + η T := by
    rw [hpEq, map_add, mean_constantField T hT]
  rw [reconstruction_apply, hm]
  have he := eq_primitive_add_terminal T hT.le q η hη hq t t.property
  change mean T hT.le (primitiveTimeLp T hT.le q) + η T +
    (realPrimitive T q t - mean T hT.le (primitiveTimeLp T hT.le q)) = η t
  rw [he]
  abel

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

omit [CompleteSpace E] in
/-- Smooth parameter dependence passes through the fixed H¹ reconstruction. -/
theorem reconstruction_contDiff (T : ℝ) (hT : 0 ≤ T)
    (p q : P → TimeLp T E) {n : ℕ∞ω} (hp : ContDiff ℝ n p) (hq : ContDiff ℝ n q) :
    ContDiff ℝ n (fun x => reconstruction T hT (p x,q x)) := by
  exact ((valuePart (E := E) T hT).contDiff.comp hp).add
    ((derivativePart (E := E) T hT).contDiff.comp hq)

omit [CompleteSpace E] in
/-- Every actual parameter derivative has the uniform time-trace estimate;
the trace costs a fixed polynomial multiplier, independent of the order. -/
theorem reconstruction_gevrey (T : ℝ) (hT : 0 < T)
    (p q : P → TimeLp T E) (hp : ContDiff ℝ ∞ p) (hq : ContDiff ℝ ∞ q)
    (R C D : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C) (hD : 0 ≤ D) (d : ℕ)
    (hbp : ∀ n x, ‖iteratedFDeriv ℝ n p x‖ ≤ C*majorant R d n)
    (hbq : ∀ n x, ‖iteratedFDeriv ℝ n q x‖ ≤ D*majorant R d n)
    (n : ℕ) (x : P) :
    ‖iteratedFDeriv ℝ n (fun y => reconstruction T hT.le (p y,q y)) x‖ ≤
      ((T⁻¹*Real.sqrt T)*C + (2*Real.sqrt T)*D) * majorant R d n := by
  have hvalue (k : ℕ) (y : P) :
      ‖iteratedFDeriv ℝ k (fun z => valuePart T hT.le (p z)) y‖ ≤
      ((T⁻¹*Real.sqrt T)*C) * majorant R d k := by
    exact (linear_bound (valuePart (E := E) T hT.le) p hp R C d hbp k y).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (valuePart_norm_le (E := E) T hT) hC)
        (majorant_nonneg R hR d k))
  have hderivative (k : ℕ) (y : P) :
      ‖iteratedFDeriv ℝ k (fun z => derivativePart T hT.le (q z)) y‖ ≤
      ((2*Real.sqrt T)*D) * majorant R d k := by
    exact (linear_bound (derivativePart (E := E) T hT.le) q hq R D d hbq k y).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (derivativePart_norm_le (E := E) T hT) hD)
        (majorant_nonneg R hR d k))
  exact add_bound (fun z => valuePart T hT.le (p z)) (fun z => derivativePart T hT.le (q z))
    ((valuePart (E := E) T hT.le).contDiff.comp hp)
    ((derivativePart (E := E) T hT.le).contDiff.comp hq)
    R ((T⁻¹*Real.sqrt T)*C) ((2*Real.sqrt T)*D) d hvalue hderivative n x

end EulerTimeH1Reconstruction
