/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanVariationalOperator
public import LeanPool.NavierStokesAndEuler.Euler.HilbertCoerciveTransport
public import LeanPool.NavierStokesAndEuler.Euler.OperatorGevreyCalculus

@[expose] public section

/-!
# Polynomial factorial bounds for the full mean variational form

All quantities are actual iterated Fréchet derivatives. The initial trace
operator contributes through its proved operator norm, just as the time
primitive does. The estimates keep the coefficient amplitudes outside the
factorial radius.
-/

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
