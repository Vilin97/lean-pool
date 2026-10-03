/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.RecursionIncrement
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FaaDiBruno.TransportODEApplications

/-! The Section 2 induction bound controls all positive spatial seminorms of
the stream velocity. -/

@[expose] public section

open Homogenization MeasureTheory
open scoped ContDiff

noncomputable section

namespace AVenhance.Infra.Construction

open AVenhance.FaaDiBruno

theorem AppB2FieldBounds.derivativeSup_postCLM_le
    {n : ℕ} {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : F →L[ℝ] G) (f : Vec 2 → F) (hf : ContDiff ℝ n f)
    (hL : ‖L‖ ≤ 1) :
    derivativeSup n (fun x => L (f x)) ≤ derivativeSup n f := by
  classical
  have hpartial (I : Fin n → Fin 2) (x : Vec 2) :
      orderedPartial n (fun y => L (f y)) x I = L (orderedPartial n f x I) := by
    let z : VecOne 2 := WithLp.toLp 1 x
    have hcomp := L.iteratedFDeriv_comp_left (f := liftVecOne f)
      (contDiff_liftVecOne hf).contDiffAt (i := n) le_rfl (x := z)
    have hcomp' :
        iteratedFDeriv ℝ n (liftVecOne (fun y => L (f y))) z =
          L.compContinuousMultilinearMap (iteratedFDeriv ℝ n (liftVecOne f) z) := by
      simpa [liftVecOne, Function.comp_def, z] using hcomp
    have heval := congrArg
      (fun D => D (fun j => coordinateVectorOne 2 (I j))) hcomp'
    simpa [orderedPartial, z] using heval
  unfold derivativeSup
  refine iSup_le fun I => ?_
  calc
    partialSup n (fun x => L (f x)) I ≤ partialSup n f I := by
      unfold partialSup
      apply eLpNormEssSup_mono_enorm_ae
      filter_upwards with x
      rw [hpartial I x]
      have hnorm : ‖L (orderedPartial n f x I)‖ ≤
          ‖orderedPartial n f x I‖ := by
        calc
          ‖L (orderedPartial n f x I)‖ ≤
              ‖L‖ * ‖orderedPartial n f x I‖ := L.le_opNorm _
          _ ≤ 1 * ‖orderedPartial n f x I‖ :=
            mul_le_mul_of_nonneg_right hL (norm_nonneg _)
          _ = ‖orderedPartial n f x I‖ := by ring
      simpa [Real.enorm_eq_ofReal_abs] using ENNReal.ofReal_le_ofReal hnorm
    _ ≤ derivativeSup n f := le_iSup_of_le I le_rfl

/-- Embed a scalar into the first coordinate of the stream vector. -/
noncomputable def AppB2FieldBounds.scalarStreamEmbedding : ℝ →L[ℝ] Vec 2 :=
  ContinuousLinearMap.toSpanSingleton ℝ (Homogenization.basisVec 0)

theorem AppB2FieldBounds.scalarStreamEmbedding_norm_le : ‖AppB2FieldBounds.scalarStreamEmbedding‖
    ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro r
  calc
    ‖AppB2FieldBounds.scalarStreamEmbedding r‖ = ‖r‖ := by
      change ‖r • Homogenization.basisVec 0‖ = ‖r‖
      rw [norm_smul]
      simp [Homogenization.basisVec, Pi.norm_single]
    _ ≤ 1 * ‖r‖ := by norm_num

/-- Extract the rotated stream gradient from the first row of a flow matrix. -/
noncomputable def AppB2FieldBounds.streamGradientExtraction :
    FlowMatrix →L[ℝ] Vec 2 :=
  ContinuousLinearMap.mk
    { toFun := fun A => ![-A 0 1, A 0 0]
      map_add' := by
        intro A B
        ext i
        fin_cases i
        · simp [add_comm]
        · simp
      map_smul' := by
        intro c A
        ext i
        fin_cases i <;> simp [smul_eq_mul] }
    (by fun_prop)

theorem AppB2FieldBounds.streamGradientExtraction_norm_le (A : FlowMatrix) :
    ‖AppB2FieldBounds.streamGradientExtraction A‖ ≤ ‖A‖ := by
  rw [pi_norm_le_iff_of_nonempty]
  intro i
  fin_cases i
  · calc
      ‖-A 0 1‖ = ‖A 0 1‖ := norm_neg _
      _ ≤ ‖A 0‖ := norm_le_pi_norm _ _
      _ ≤ ‖A‖ := norm_le_pi_norm _ _
  · calc
      ‖A 0 0‖ ≤ ‖A 0‖ := norm_le_pi_norm _ _
      _ ≤ ‖A‖ := norm_le_pi_norm _ _

theorem AppB2FieldBounds.streamGradientExtraction_opNorm_le :
    ‖AppB2FieldBounds.streamGradientExtraction‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro A
  calc
    ‖AppB2FieldBounds.streamGradientExtraction A‖ ≤ ‖A‖ :=
        AppB2FieldBounds.streamGradientExtraction_norm_le A
    _ = 1 * ‖A‖ := by ring

theorem AppB2FieldBounds.streamVel_eq_extractedGradient
    (φ : ℝ → Vec 2 → ℝ) (hφsmooth : ContDiff ℝ ∞ (Function.uncurry φ))
    (t : ℝ) :
    streamVel φ t = fun x => AppB2FieldBounds.streamGradientExtraction
      (spatialGradientMatrix (fun y => AppB2FieldBounds.scalarStreamEmbedding (φ t y)) x) := by
  funext x
  rw [streamVel_eq_timeIncrementRotate]
  have hφslice : ContDiff ℝ 1 (φ t) := by
    have hmap : ContDiff ℝ 1 (fun y : Vec 2 => (t, y)) := by fun_prop
    exact (hφsmooth.of_le (by norm_num)).comp hmap
  have hcomp := AppB2FieldBounds.scalarStreamEmbedding.hasFDerivAt.comp x
    (hφslice.differentiable (by norm_num) x).hasFDerivAt
  have hderiv : fderiv ℝ (fun y => AppB2FieldBounds.scalarStreamEmbedding (φ t y)) x =
      AppB2FieldBounds.scalarStreamEmbedding.comp (fderiv ℝ (φ t) x) := by
    simpa only [Function.comp_def] using hcomp.fderiv
  unfold spatialGradientMatrix
  rw [hderiv]
  ext i
  fin_cases i <;>
    simp [AppB2FieldBounds.streamGradientExtraction, AppB2FieldBounds.scalarStreamEmbedding,
        timeIncrementRotate,
      ContinuousLinearMap.comp_apply, Homogenization.basisVec, coordinateVector]

theorem streamVel_derivativeSup_le_next
    (φ : ℝ → Vec 2 → ℝ) (hφ : ContDiff ℝ ∞ (Function.uncurry φ))
    (t : ℝ) (n : ℕ) :
    derivativeSup n (streamVel φ t) ≤ derivativeSup (n + 1) (φ t) := by
  let F : Vec 2 → Vec 2 := fun x => AppB2FieldBounds.scalarStreamEmbedding (φ t x)
  have hslice : ContDiff ℝ ∞ (φ t) := by
    have hmap : ContDiff ℝ ∞ (fun x : Vec 2 => (t, x)) := by fun_prop
    exact hφ.comp hmap
  have hF : ContDiff ℝ ∞ F := by
    exact AppB2FieldBounds.scalarStreamEmbedding.contDiff.comp hslice
  have hFderiv : ContDiff ℝ ∞ (fun x : Vec 2 => fderiv ℝ F x) :=
    hF.fderiv_right (by simp)
  have hgradient : ContDiff ℝ ∞ (spatialGradientMatrix F) := by
    unfold spatialGradientMatrix
    apply contDiff_pi.2
    intro i
    apply contDiff_pi.2
    intro j
    have hcolumn : ContDiff ℝ ∞
        (fun x : Vec 2 => fderiv ℝ F x (coordinateVector 2 j)) :=
      hFderiv.clm_apply contDiff_const
    exact (contDiff_apply ℝ ℝ i).comp hcolumn
  rw [AppB2FieldBounds.streamVel_eq_extractedGradient φ hφ t]
  calc
    derivativeSup n
        (fun x => AppB2FieldBounds.streamGradientExtraction (spatialGradientMatrix F x)) ≤
        derivativeSup n (spatialGradientMatrix F) :=
      AppB2FieldBounds.derivativeSup_postCLM_le AppB2FieldBounds.streamGradientExtraction
          (spatialGradientMatrix F)
        (hgradient.of_le (by simp)) AppB2FieldBounds.streamGradientExtraction_opNorm_le
    _ ≤ derivativeSup (n + 1) F :=
      AVenhance.FaaDiBruno.spatialGradientMatrix_derivativeSup_le F hF n
    _ = derivativeSup (n + 1)
          (fun x => AppB2FieldBounds.scalarStreamEmbedding (φ t x)) := rfl
    _ ≤ derivativeSup (n + 1) (φ t) :=
      AppB2FieldBounds.derivativeSup_postCLM_le AppB2FieldBounds.scalarStreamEmbedding (φ t)
        (hslice.of_le (by simp)) AppB2FieldBounds.scalarStreamEmbedding_norm_le

theorem streamVel_snorm_le_from_induction
    (φ : ℝ → Vec 2 → ℝ) (hφ : ContDiff ℝ ∞ (Function.uncurry φ))
    (t : ℝ) (n : ℕ) {R M : ℝ} (hR : 0 < R) (hM : 0 < M)
    (hprev : snorm (φ t) (n + 1) R ≤ ENNReal.ofReal
      (M * R⁻¹ ^ 2 * (((n : ℝ) + 3) ^ 2 / ((n : ℝ) + 2) ^ 3))) :
    snorm (streamVel φ t) n R ≤ ENNReal.ofReal (M / R) := by
  have hDprev := derivativeSup_le_of_snorm_le (φ t) hR hprev
  have hDprev' : derivativeSup (n + 1) (φ t) ≤
      ENNReal.ofReal
        (M * R⁻¹ ^ 2 * (((n : ℝ) + 3) ^ 2 / ((n : ℝ) + 2) ^ 3) *
          (n + 1).factorial * R ^ (n + 1) / ((n : ℝ) + 2) ^ 2) := by
    have hden : (((n + 1 : ℕ) : ℝ) + 1) ^ 2 = ((n : ℝ) + 2) ^ 2 := by
      push_cast
      ring
    have hDprev'' := hDprev
    rw [hden] at hDprev''
    exact hDprev''
  have hDvel := streamVel_derivativeSup_le_next φ hφ t n
  have hpoly : ((n : ℝ) + 1) ^ 3 * ((n : ℝ) + 3) ^ 2 ≤
      ((n : ℝ) + 2) ^ 5 := by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith [sq_nonneg ((n : ℝ) + 2), sq_nonneg ((n : ℝ) + 3)]
  have hderiv : derivativeSup n (streamVel φ t) ≤ ENNReal.ofReal
      ((M / R) * n.factorial * R ^ n / ((n : ℝ) + 1) ^ 2) := by
    calc
      derivativeSup n (streamVel φ t) ≤ derivativeSup (n + 1) (φ t) := hDvel
      _ ≤ ENNReal.ofReal
          (M * R⁻¹ ^ 2 * (((n : ℝ) + 3) ^ 2 / ((n : ℝ) + 2) ^ 3) *
            (n + 1).factorial * R ^ (n + 1) / ((n : ℝ) + 2) ^ 2) := by
          exact hDprev'
      _ ≤ ENNReal.ofReal
          ((M / R) * n.factorial * R ^ n / ((n : ℝ) + 1) ^ 2) := by
          apply ENNReal.ofReal_le_ofReal
          have hRn : R ^ (n + 1) = R ^ n * R := by rw [pow_succ]
          rw [hRn, Nat.factorial_succ]
          have hRpos : 0 < R := hR
          have hMpos : 0 < M := hM
          have hpolyFac :
              ((n : ℝ) + 1) ^ 3 * ((n : ℝ) + 3) ^ 2 *
                  (n.factorial : ℝ) ≤
                ((n : ℝ) + 2) ^ 5 * (n.factorial : ℝ) :=
            mul_le_mul_of_nonneg_right hpoly (by positivity)
          push_cast
          field_simp [hRpos.ne']
          nlinarith [hpolyFac]
  have hderiv' : derivativeSup n (streamVel φ t) ≤ ENNReal.ofReal
      ((M / R) * R ^ n * n.factorial / ((n : ℝ) + 1) ^ 2) := by
    convert hderiv using 1
    congr 1
    ring
  exact snorm_le_of_derivativeSup_le (streamVel φ t) hR hderiv'

theorem section2_streamVel_snorm_bound
    {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : IsStreamSeq I Φ) {R M : ℕ → ℝ} {m n : ℕ}
    (hprev : Section2StreamInductionHypothesis (Φ := Φ) R M m)
    (hn : 1 ≤ n) (hR : 0 < R m) (hM : 0 < M m) (t : ℝ) :
    snorm (streamVel (Φ m) t) n (R m) ≤ ENNReal.ofReal (M m / R m) := by
  have hsource0 : snorm (Φ m t) (n + 1) (R m) ≤ ENNReal.ofReal
      (M m * (R m)⁻¹ ^ 2 * (((n : ℝ) + 1 + 2) ^ 2 / ((n : ℝ) + 1 + 1) ^ 3)) := by
    simpa only [Section2StreamInductionHypothesis, Nat.cast_add, Nat.cast_one] using
      hprev t (n + 1) (by omega)
  have hsource : snorm (Φ m t) (n + 1) (R m) ≤ ENNReal.ofReal
      (M m * (R m)⁻¹ ^ 2 * (((n : ℝ) + 3) ^ 2 / ((n : ℝ) + 2) ^ 3)) := by
    convert hsource0 using 1
    congr 1
    ring
  exact streamVel_snorm_le_from_induction (Φ m)
    (streamSeq_isAdmissible hseq m).1 t n hR hM hsource

end AVenhance.Infra.Construction

end
