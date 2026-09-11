/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.MeanFixedSpaceInverse
import LeanPool.NavierStokesAndEuler.Euler.MeanFixedCoefficientRegularity
import LeanPool.NavierStokesAndEuler.Euler.OperatorGevreyCalculus
import LeanPool.NavierStokesAndEuler.Euler.TimeLpCoefficientGevrey
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder
import Mathlib.Analysis.Calculus.ContDiff.Operations
public import LeanPool.NavierStokesAndEuler.Euler.MeanVariationalOperator
public import LeanPool.NavierStokesAndEuler.Euler.HilbertCoerciveTransport
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.Gevrey
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import LeanPool.NavierStokesAndEuler.Euler.TransverseGramInverse

/-!
# Quantitative genuine coefficient calculus for the fixed mean inverse

The actual fixed operator has a polynomial amplitude depending on the time
interval and coefficient bounds. The factorial radius and derivative shift
are preserved by the coefficient-to-time-operator constructions.
-/

section

/-!
# Polynomial factorial bounds for the full mean variational form

All quantities are actual iterated Fréchet derivatives. The initial trace
operator contributes through its proved operator norm, just as the time
primitive does. The estimates keep the coefficient amplitudes outside the
factorial radius.
-/

@[expose] public section

noncomputable section

namespace EulerMeanFormGevrey

open ContinuousLinearMap InnerProductSpace EulerGevrey EulerMeanVariationalOperator
  EulerHilbertCoerciveTransport EulerOperatorGevreyCalculus EulerTransverseGramInverse
  EulerTransverseVariationalInverse
open scoped ContDiff

variable {P V W X : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

variable (J : W →L[ℝ] W) (R : W →L[ℝ] X)
  (H : P → W →L[ℝ] W) (C : P → X →L[ℝ] X)

/-- The full physical form is a smooth polynomial in its genuine coefficient operators. -/
theorem meanOperator_contDiff {n : ℕ∞ω} (hH : ContDiff ℝ n H) (hC : ContDiff ℝ n C) :
    ContDiff ℝ n (fun p => meanOperator J R (H p) (C p)) :=
  (contDiff_const.sub (contDiff_const.clm_comp (hH.clm_comp contDiff_const))).add
    (contDiff_const.clm_comp (hC.clm_comp contDiff_const))

/-- A polynomial amplitude for the original kinetic, potential, and boundary form. -/
def baseAmplitude (CH CC : ℝ) : ℝ := 1+‖J‖^2*CH+‖R‖^2*CC

omit [CompleteSpace W] [CompleteSpace X] in
theorem baseAmplitude_nonneg (CH CC : ℝ) (hCH : 0 ≤ CH) (hCC : 0 ≤ CC) :
    0 ≤ baseAmplitude J R CH CC := by unfold baseAmplitude; positivity

/-- The actual physical mean operator has the stated all-order factorial bound. -/
theorem meanOperator_bound (hH : ContDiff ℝ ∞ H) (hC : ContDiff ℝ ∞ C)
    (r CH CC : ℝ) (hr : 0 ≤ r) (hCH : 0 ≤ CH) (hCC : 0 ≤ CC)
    (hHb : ∀ n x, ‖iteratedFDeriv ℝ n H x‖ ≤ CH * majorant r 0 n)
    (hCb : ∀ n x, ‖iteratedFDeriv ℝ n C x‖ ≤ CC * majorant r 0 n)
    (n : ℕ) (x : P) :
    ‖iteratedFDeriv ℝ n (fun p => meanOperator J R (H p) (C p)) x‖ ≤
      baseAmplitude J R CH CC * majorant r 0 n := by
  have hHJ := clm_comp_const_right_bound H J hH r CH hr hCH 0 hHb
  have hJHJ : ∀ k y,
      ‖iteratedFDeriv ℝ k (fun p => J.adjoint.comp ((H p).comp J)) y‖ ≤
        (‖J‖^2*CH) * majorant r 0 k := by
    intro k y
    have h := clm_comp_const_left_bound J.adjoint (fun p => (H p).comp J)
      (hH.clm_comp contDiff_const) r (‖J‖*CH) hr (mul_nonneg (norm_nonneg _) hCH) 0 hHJ k y
    simpa only [LinearIsometryEquiv.norm_map, pow_two, mul_assoc] using h
  have hCR := clm_comp_const_right_bound C R hC r CC hr hCC 0 hCb
  have hRCR : ∀ k y,
      ‖iteratedFDeriv ℝ k (fun p => R.adjoint.comp ((C p).comp R)) y‖ ≤
        (‖R‖^2*CC) * majorant r 0 k := by
    intro k y
    have h := clm_comp_const_left_bound R.adjoint (fun p => (C p).comp R)
      (hC.clm_comp contDiff_const) r (‖R‖*CC) hr (mul_nonneg (norm_nonneg _) hCC) 0 hCR k y
    simpa only [LinearIsometryEquiv.norm_map, pow_two, mul_assoc] using h
  have hId := const_bound (P := P) (ContinuousLinearMap.id ℝ W) r 1 hr (norm_id_le :
      ‖ContinuousLinearMap.id ℝ W‖ ≤ 1)
  have hsub := sub_bound (fun _ : P => ContinuousLinearMap.id ℝ W)
    (fun p => J.adjoint.comp ((H p).comp J)) contDiff_const
    (contDiff_const.clm_comp (hH.clm_comp contDiff_const)) r 1 (‖J‖^2*CH) 0 hId hJHJ
  exact add_bound
    (fun p => ContinuousLinearMap.id ℝ W-J.adjoint.comp ((H p).comp J))
    (fun p => R.adjoint.comp ((C p).comp R))
    (contDiff_const.sub (contDiff_const.clm_comp (hH.clm_comp contDiff_const)))
    (contDiff_const.clm_comp (hC.clm_comp contDiff_const))
    r (1+‖J‖^2*CH) (‖R‖^2*CC) 0 hsub hRCR n x

variable (D : P → V →L[ℝ] W)

/-- Pullback by the genuine coordinate derivative preserves coefficient regularity. -/
theorem pullbackMeanOperator_contDiff {n : ℕ∞ω}
    (hD : ContDiff ℝ n D) (hH : ContDiff ℝ n H) (hC : ContDiff ℝ n C) :
    ContDiff ℝ n (fun p => transportedOperator (D p) (meanOperator J R (H p) (C p))) :=
  ((realAdjoint (U := V) (E := W)).contDiff.comp hD).clm_comp
    ((meanOperator_contDiff J R H C hH hC).clm_comp hD)

/-- The full actual fixed-space mean operator obeys a polynomial factorial bound. -/
theorem pullbackMeanOperator_bound
    (hD : ContDiff ℝ ∞ D) (hH : ContDiff ℝ ∞ H) (hC : ContDiff ℝ ∞ C)
    (r CD CH CC : ℝ) (hr : 0 ≤ r) (hCD : 0 ≤ CD) (hCH : 0 ≤ CH) (hCC : 0 ≤ CC)
    (hDb : ∀ n x, ‖iteratedFDeriv ℝ n D x‖ ≤ CD * majorant r 0 n)
    (hHb : ∀ n x, ‖iteratedFDeriv ℝ n H x‖ ≤ CH * majorant r 0 n)
    (hCb : ∀ n x, ‖iteratedFDeriv ℝ n C x‖ ≤ CC * majorant r 0 n)
    (n : ℕ) (x : P) :
    ‖iteratedFDeriv ℝ n (fun p => transportedOperator (D p) (meanOperator J R (H p) (C p))) x‖ ≤
      (9*CD^2*baseAmplitude J R CH CC) * majorant r 0 n := by
  have hB := meanOperator_contDiff J R H C hH hC
  have hBb := meanOperator_bound J R H C hH hC r CH CC hr hCH hCC hHb hCb
  have hB0 := baseAmplitude_nonneg J R CH CC hCH hCC
  have hBD : ∀ k y,
      ‖iteratedFDeriv ℝ k (fun p => (meanOperator J R (H p) (C p)).comp (D p)) y‖ ≤
        (3*baseAmplitude J R CH CC*CD) * majorant r 0 k := by
    intro k y
    simpa only [Nat.zero_add] using clm_comp_bound
      (fun p => meanOperator J R (H p) (C p)) D hB hD r (baseAmplitude J R CH CC) CD
      hr hB0 hCD 0 0 hBb hDb k y
  have hDa := (realAdjoint (U := V) (E := W)).contDiff.comp hD
  have hDab := adjoint_bound D hD r CD hr hCD 0 hDb
  have h := clm_comp_bound (fun p => (D p).adjoint)
    (fun p => (meanOperator J R (H p) (C p)).comp (D p)) hDa (hB.clm_comp hD)
    r CD (3*baseAmplitude J R CH CC*CD) hr hCD (by positivity) 0 0 hDab hBD n x
  calc
    _ ≤ (3*CD*(3*baseAmplitude J R CH CC*CD)) * majorant r 0 n := by
      simpa only [transportedOperator, Nat.zero_add] using h
    _ = _ := by ring

/-- The genuine forcing pullback has the matching factorial shift. -/
theorem pullbackMeanForcing_bound (f : P → W) (hD : ContDiff ℝ ∞ D) (hf : ContDiff ℝ ∞ f)
    (r CD CF : ℝ) (hr : 0 ≤ r) (hCD : 0 ≤ CD) (hCF : 0 ≤ CF) (d : ℕ)
    (hDb : ∀ n x, ‖iteratedFDeriv ℝ n D x‖ ≤ CD * majorant r 0 n)
    (hfb : ∀ n x, ‖iteratedFDeriv ℝ n f x‖ ≤ CF * majorant r d n)
    (n : ℕ) (x : P) :
    ‖iteratedFDeriv ℝ n (fun p => -((J.comp (D p)).adjoint (f p))) x‖ ≤
      (3*(‖J‖*CD)*CF) * majorant r d n := by
  have hK : ContDiff ℝ ∞ (fun p => J.comp (D p)) :=
    (show ContDiff ℝ ∞ (fun _ : P => J) from contDiff_const).clm_comp hD
  have hKb := clm_comp_const_left_bound J D hD r CD hr hCD 0 hDb
  have hKa := (realAdjoint (U := V) (E := W)).contDiff.comp hK
  have hKab := adjoint_bound (fun p => J.comp (D p)) hK r (‖J‖*CD) hr
    (mul_nonneg (norm_nonneg _) hCD) 0 hKb
  have happ : ∀ k y,
      ‖iteratedFDeriv ℝ k (fun p => (J.comp (D p)).adjoint (f p)) y‖ ≤
        (3*(‖J‖*CD)*CF) * majorant r d k := by
    intro k y
    simpa only [Nat.zero_add] using clm_apply_bound
      (fun p => (J.comp (D p)).adjoint) f hKa hf r (‖J‖*CD) CF hr
      (mul_nonneg (norm_nonneg _) hCD) hCF 0 d hKab hfb k y
  exact neg_bound (fun p => (J.comp (D p)).adjoint (f p)) r (3*(‖J‖*CD)*CF) d happ n x

end EulerMeanFormGevrey

end
end

end

@[expose] public section

noncomputable section

namespace EulerMeanFixedCoefficientGevrey

open Set ContinuousLinearMap EulerTimeLp EulerTerminalTimePrimitive EulerMeanSolenoidal
  EulerMeanVariationalInverse EulerMeanFixedSpaceInverse EulerMeanFixedCoefficientRegularity
  EulerTimeLpCoefficientMap EulerTimeLpCoefficientGevrey EulerOperatorGevreyCalculus
  EulerMeanFormGevrey EulerGevrey EulerVolterraConvolution
open scoped ContDiff

/-- Cache the standard `NormedAddCommGroup solenoidalSpace` instance to shorten typeclass
synthesis. -/
local instance instMeanFixedCoefficientGevrey1 : NormedAddCommGroup solenoidalSpace := inferInstance
/-- Cache the standard `InnerProductSpace ℝ solenoidalSpace` instance to shorten typeclass
synthesis. -/
local instance instMeanFixedCoefficientGevrey2 : InnerProductSpace ℝ solenoidalSpace :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup (solenoidalSpace →L[ℝ] L2)` instance to shorten
typeclass synthesis. -/
local instance instMeanFixedCoefficientGevrey3 : NormedAddCommGroup (solenoidalSpace →L[ℝ] L2) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (solenoidalSpace →L[ℝ] L2)` instance to shorten typeclass
synthesis. -/
local instance instMeanFixedCoefficientGevrey4 : NormedSpace ℝ (solenoidalSpace →L[ℝ] L2) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)` instance to shorten
typeclass synthesis. -/
local instance instMeanFixedCoefficientGevrey5 (T : ℝ) : NormedAddCommGroup C(Icc (0 : ℝ) T, L2
    →L[ℝ] L2) := inferInstance
/-- Cache the standard `NormedSpace ℝ C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)` instance to shorten
typeclass synthesis. -/
local instance instMeanFixedCoefficientGevrey6 (T : ℝ) : NormedSpace ℝ C(Icc (0 : ℝ) T, L2 →L[ℝ]
    L2) := inferInstance
/-- Cache the standard `NormedAddCommGroup C(Icc (0 : ℝ) T, solenoidalSpace →L[ℝ] L2)` instance
to shorten typeclass synthesis. -/
local instance instMeanFixedCoefficientGevrey7 (T : ℝ) : NormedAddCommGroup C(Icc (0 : ℝ) T,
    solenoidalSpace →L[ℝ] L2) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ C(Icc (0 : ℝ) T, solenoidalSpace →L[ℝ] L2)` instance to
shorten typeclass synthesis. -/
local instance instMeanFixedCoefficientGevrey8 (T : ℝ) : NormedSpace ℝ C(Icc (0 : ℝ) T,
    solenoidalSpace →L[ℝ] L2) :=
    inferInstance

private theorem scalar_bound {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (a : ℝ) (f : P → E) (hf : ContDiff ℝ ∞ f)
    (r C : ℝ) (d : ℕ) (hb : ∀ n x, ‖iteratedFDeriv ℝ n f x‖ ≤ C * majorant r d n)
    (n : ℕ) (x : P) :
    ‖iteratedFDeriv ℝ n (fun p => a • f p) x‖ ≤ (|a| *C)*majorant r d n := by
  calc
    _ = |a| *‖iteratedFDeriv ℝ n f x‖ := by
      rw [iteratedFDeriv_const_smul_apply' (hf.contDiffAt.of_le (by
          simp)), norm_smul, Real.norm_eq_abs]
    _ ≤ |a| *(C*majorant r d n) := mul_le_mul_of_nonneg_left (hb n x) (abs_nonneg a)
    _ = _ := by ring

/-- The sharp terminal time bounds control the norm factors in the actual physical form. -/
theorem baseAmplitude_time_bound (T : ℝ) (hT : 0 ≤ T) (CH CC : ℝ)
    (hCH : 0 ≤ CH) (hCC : 0 ≤ CC) :
    baseAmplitude (primitiveTimeLp (E := L2) T hT) (initialTrace (E := L2) T hT) CH CC ≤
      1+(T^2/2)*CH+T*CC := by
  have hJ := (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg (T^2/2))).2
    (primitiveTimeLp_norm_le (E := L2) T hT)
  have hR := (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg T)).2
    (initialTrace_norm_le (E := L2) T hT)
  have hJ := hJ.trans_eq (Real.sq_sqrt (by positivity : 0 ≤ T^2/2))
  have hR := hR.trans_eq (Real.sq_sqrt hT)
  exact add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_right hJ hCH))
    (mul_le_mul_of_nonneg_right hR hCC)

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  (T : ℝ) (hT : 0 ≤ T)
  (F F₁ H : P → C(Icc (0 : ℝ) T, L2 →L[ℝ] L2))
  (M0 A : P → L2 →L[ℝ] L2) (L : ℝ)

/-- Restriction to the actual solenoidal space does not enlarge any factorial bound. -/
theorem solenoidalFrame_bound (hF : ContDiff ℝ ∞ F)
    (r C : ℝ) (hr : 0 ≤ r) (hC : 0 ≤ C) (d : ℕ)
    (hb : ∀ n x, ‖iteratedFDeriv ℝ n F x‖ ≤ C * majorant r d n) (n : ℕ) (x : P) :
    ‖iteratedFDeriv ℝ n (fun p => solenoidalFrame T (F p)) x‖ ≤ C*majorant r d n :=
  contraction_bound (P := P) (E := C(Icc (0 : ℝ) T, L2 →L[ℝ] L2))
    (F := C(Icc (0 : ℝ) T, solenoidalSpace →L[ℝ] L2))
    (framePathRestriction T) (framePathRestriction_norm T) F hF r C hr hC d hb n x

/-- The genuine fixed derivative map has only polynomial time cost. -/
theorem fixedMeanDerivative_bound (hF : ContDiff ℝ ∞ F) (hF₁ : ContDiff ℝ ∞ F₁)
    (r CF CF₁ : ℝ) (hr : 0 ≤ r) (hCF : 0 ≤ CF) (hCF₁ : 0 ≤ CF₁) (d : ℕ)
    (hFb : ∀ n x, ‖iteratedFDeriv ℝ n F x‖ ≤ CF * majorant r d n)
    (hF₁b : ∀ n x, ‖iteratedFDeriv ℝ n F₁ x‖ ≤ CF₁ * majorant r d n)
    (n : ℕ) (x : P) :
    ‖iteratedFDeriv ℝ n (fun p => fixedMeanDerivative T hT (F p) (F₁ p)) x‖ ≤
      (T*CF₁+CF)*majorant r d n :=
  productDerivative_bound T hT (fun p => solenoidalFrame T (F p))
    (fun p => solenoidalFrame T (F₁ p)) (contDiff_solenoidalFrame T F hF)
    (contDiff_solenoidalFrame T F₁ hF₁) r CF CF₁ hr hCF hCF₁ d
    (solenoidalFrame_bound T F hF r CF hr hCF d hFb)
    (solenoidalFrame_bound T F₁ hF₁ r CF₁ hr hCF₁ d hF₁b) n x

/-- A fully explicit polynomial amplitude for actual derivatives of the entire fixed mean operator.
-/
theorem fixedMeanOperator_bound
    (hF : ContDiff ℝ ∞ F) (hF₁ : ContDiff ℝ ∞ F₁) (hH : ContDiff ℝ ∞ H)
    (hM0 : ContDiff ℝ ∞ M0) (hA : ContDiff ℝ ∞ A)
    (r CF CF₁ CH CM CA : ℝ) (hr : 0 ≤ r) (hCF : 0 ≤ CF) (hCF₁ : 0 ≤ CF₁)
    (hCH : 0 ≤ CH) (hCM : 0 ≤ CM) (hCA : 0 ≤ CA)
    (hFb : ∀ n x, ‖iteratedFDeriv ℝ n F x‖ ≤ CF * majorant r 0 n)
    (hF₁b : ∀ n x, ‖iteratedFDeriv ℝ n F₁ x‖ ≤ CF₁ * majorant r 0 n)
    (hHb : ∀ n x, ‖iteratedFDeriv ℝ n H x‖ ≤ CH * majorant r 0 n)
    (hMb : ∀ n x, ‖iteratedFDeriv ℝ n M0 x‖ ≤ CM * majorant r 0 n)
    (hAb : ∀ n x, ‖iteratedFDeriv ℝ n A x‖ ≤ CA * majorant r 0 n)
    (n : ℕ) (x : P) :
    ‖iteratedFDeriv ℝ n (fun p => fixedMeanOperator T hT (F p) (F₁ p) (H p) (M0 p) (A p) L) x‖ ≤
      (9*(T*CF₁+CF)^2*(1+(T^2/2)*CH+T*(CM+|L| *CA))) * majorant r 0 n := by
  have hD := contDiff_fixedMeanDerivative T hT F F₁ hF hF₁
  have hDb := fixedMeanDerivative_bound T hT F F₁ hF hF₁ r CF CF₁ hr hCF hCF₁ 0 hFb hF₁b
  have hHC := contDiff_timeMultiplier T hT H hH
  have hHCb := timeMultiplier_bound T hT H hH r CH hr hCH 0 hHb
  have hC : ContDiff ℝ ∞ (fun p => M0 p+L • A p) := hM0.add (hA.const_smul L)
  have hCb := add_bound M0 (fun p => L • A p) hM0 (hA.const_smul L) r CM (|L| *CA) 0
    hMb (scalar_bound L A hA r CA 0 hAb)
  have hD0 : 0 ≤ T*CF₁+CF := add_nonneg (mul_nonneg hT hCF₁) hCF
  have hC0 : 0 ≤ CM+|L| *CA := add_nonneg hCM (mul_nonneg (abs_nonneg L) hCA)
  have hb := pullbackMeanOperator_bound
    (primitiveTimeLp (E := L2) T hT) (initialTrace (E := L2) T hT)
    (fun p => timeMultiplier T hT (H p)) (fun p => M0 p+L • A p)
    (fun p => fixedMeanDerivative T hT (F p) (F₁ p)) hD hHC hC
    r (T*CF₁+CF) CH (CM+|L| *CA) hr hD0 hCH hC0 hDb hHCb hCb n x
  have hb' : ‖iteratedFDeriv ℝ n
      (fun p => fixedMeanOperator T hT (F p) (F₁ p) (H p) (M0 p) (A p) L) x‖ ≤
      (9*(T*CF₁+CF)^2*baseAmplitude (primitiveTimeLp (E := L2) T hT)
        (initialTrace (E := L2) T hT) CH (CM+|L| *CA))*majorant r 0 n := hb
  exact hb'.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (baseAmplitude_time_bound T hT CH (CM+|L| *CA) hCH hC0) (by
        positivity))
    (majorant_nonneg r hr 0 n))

/-- The actual force pullback preserves the forcing shift and has explicit polynomial amplitude. -/
theorem fixedMeanForcing_bound (f : P → TimeLp T L2)
    (hF : ContDiff ℝ ∞ F) (hF₁ : ContDiff ℝ ∞ F₁) (hf : ContDiff ℝ ∞ f)
    (r CF CF₁ Cf : ℝ) (hr : 0 ≤ r) (hCF : 0 ≤ CF) (hCF₁ : 0 ≤ CF₁) (hCf : 0 ≤ Cf) (d : ℕ)
    (hFb : ∀ n x, ‖iteratedFDeriv ℝ n F x‖ ≤ CF * majorant r 0 n)
    (hF₁b : ∀ n x, ‖iteratedFDeriv ℝ n F₁ x‖ ≤ CF₁ * majorant r 0 n)
    (hfb : ∀ n x, ‖iteratedFDeriv ℝ n f x‖ ≤ Cf * majorant r d n)
    (n : ℕ) (x : P) :
    ‖iteratedFDeriv ℝ n (fun p => -(fixedMeanPrimitive T hT (F p) (F₁ p)).adjoint (f p)) x‖ ≤
      (3*(T*(T*CF₁+CF))*Cf)*majorant r d n := by
  have hD0 : 0 ≤ T*CF₁+CF := add_nonneg (mul_nonneg hT hCF₁) hCF
  have hb := pullbackMeanForcing_bound (primitiveTimeLp (E := L2) T hT)
    (fun p => fixedMeanDerivative T hT (F p) (F₁ p)) f
    (contDiff_fixedMeanDerivative T hT F F₁ hF hF₁) hf r (T*CF₁+CF) Cf hr hD0 hCf d
    (fixedMeanDerivative_bound T hT F F₁ hF hF₁ r CF CF₁ hr hCF hCF₁ 0 hFb hF₁b) hfb n x
  exact hb.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (primitive_norm_le_time (E := L2) T hT) hD0) (by norm_num)) hCf)
    (majorant_nonneg r hr d n))

end EulerMeanFixedCoefficientGevrey
