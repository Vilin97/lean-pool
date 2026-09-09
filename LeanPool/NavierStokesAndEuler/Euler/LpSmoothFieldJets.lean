/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.LpSmoothField
public import LeanPool.NavierStokesAndEuler.Euler.LpMultilinearBundling
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder

/-! Exact identification of ordinary spatial derivatives with all translation jets in L². -/

@[expose] public section


noncomputable section


namespace EulerLpTranslation.SmoothL2Field

open MeasureTheory EulerSmoothLimit EulerLpDerivative Filter
open scoped ContDiff Topology

universe u

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem jetLp_ae (A : SmoothL2Field V) (n : ℕ) :
    A.jetLp n =ᵐ[volume] iteratedFDeriv ℝ n A.field := (A.integrable n).coeFn_toLp

private theorem iteratedFDeriv_translation_ae_aux (n : ℕ) :
    ∀ (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V] (A : SmoothL2Field V)
      (a : Space) (v : Fin n → Space),
      iteratedFDeriv ℝ n (fun b : Space => translation b A.toLp) a v =ᵐ[volume]
        fun x => iteratedFDeriv ℝ n A.field (x+a) v := by
  induction n with
  | zero =>
    intro V _ _ A a v
    simp only [iteratedFDeriv_zero_apply]
    filter_upwards [translation_ae a A.toLp,
      (measurePreserving_add_right (volume : Measure Space) a).quasiMeasurePreserving.ae
        A.toLp_ae] with x ht hf
    exact ht.trans hf
  | succ n ih =>
    intro V _ _ A a v
    have he : iteratedFDeriv ℝ (n+1) (fun b : Space => translation b A.toLp) a v =
        derivativeMap volume
          (iteratedFDeriv ℝ n (fun b : Space => translation b A.derivative.toLp) a (Fin.init v))
          (v (Fin.last n)) := by
      rw [iteratedFDeriv_succ_apply_right, A.translation_fderiv]
      change (iteratedFDeriv ℝ n
        ((derivativeBundling (P := Space) (V := V) volume) ∘
          fun b : Space => translation b A.derivative.toLp) a (Fin.init v)) (v (Fin.last n)) = _
      rw [(derivativeBundling (P := Space) (V := V) volume).iteratedFDeriv_comp_left
        (A.derivative.translation_contDiff.contDiffAt (x := a)) (by simp)]
      rfl
    rw [he]
    filter_upwards [derivativeMap_ae volume
      (iteratedFDeriv ℝ n (fun b : Space => translation b A.derivative.toLp) a (Fin.init v))
      (v (Fin.last n)), ih (Space →L[ℝ] V) A.derivative a (Fin.init v)] with x hm hi
    rw [hm, hi]
    exact (iteratedFDeriv_succ_apply_right (f := A.field) (x := x+a) v).symm

theorem iteratedFDeriv_translation_ae (A : SmoothL2Field V) (n : ℕ)
    (a : Space) (v : Fin n → Space) :
    iteratedFDeriv ℝ n (fun b : Space => translation b A.toLp) a v =ᵐ[volume]
      fun x => iteratedFDeriv ℝ n A.field (x+a) v :=
  iteratedFDeriv_translation_ae_aux n V A a v

/-- The entire parameter derivative tensor is a bounded linear image of the actual spatial L²
tensor. -/
theorem iteratedFDeriv_translation_eq (A : SmoothL2Field V) (n : ℕ) (a : Space) :
    iteratedFDeriv ℝ n (fun b : Space => translation b A.toLp) a =
      multilinearBundling (P := Space) (V := V) volume n (translation a (A.jetLp n)) := by
  apply ContinuousMultilinearMap.ext
  intro v
  apply Lp.ext
  filter_upwards [A.iteratedFDeriv_translation_ae n a v,
    multilinearBundling_ae volume n (translation a (A.jetLp n)) v,
    translation_ae a (A.jetLp n),
    (measurePreserving_add_right (volume : Measure Space) a).quasiMeasurePreserving.ae
      (A.jetLp_ae n)] with x hd hm ht hj
  rw [hd, hm, ht, hj]

end EulerLpTranslation.SmoothL2Field
