/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketLiftedCurl

@[expose] public section

/-!
The curl Piola identity on the actual periodic cylinder.  The Jacobian acts
only on the three label variables.  Its derivative cancels in the lifted
curl by symmetry of the genuine second derivative; the angular component
passes through unchanged.  This supplies an actual element of the closed
lifted divergence-free L² space from a compact smooth packet potential.
-/

noncomputable section


namespace EulerPacketPiola

open MeasureTheory InnerProductSpace EulerSmoothLimit EulerMeanBoundary
  EulerLiftedGradientSpace EulerMetricTransport EulerTransportDerivatives
  EulerLiftedWeakDerivative EulerTransverseGramInverse
open scoped ContDiff

private local instance : NormedAddCommGroup (Space →L[ℝ] Space) := inferInstance
private local instance : NormedSpace ℝ (Space →L[ℝ] Space) := inferInstance

theorem realAdjoint_apply (A : Space →L[ℝ] Space) :
    realAdjoint A = A.adjoint := rfl

def coveringCurl (κ : ℝ) (m : Space) (q : LiftTangent → Space)
    (z : LiftTangent) : Space :=
  curlMatrix ((fderiv ℝ q z).comp (EulerGraphPullback.liftedDirection κ m))

def coveringPullbackCovector (Ξ : Space → Space) (q : LiftTangent → Space)
    (z : LiftTangent) : Space :=
  (fderiv ℝ Ξ z.1).adjoint (q z)

/-- Cancellation of the actual Hessian in all constant lifted directions. -/
theorem coveringCurl_pullback (κ : ℝ) (m : Space) (Ξ : Space → Space)
    (q : LiftTangent → Space) (hΞ : ContDiff ℝ 2 Ξ) (z : LiftTangent)
    (hq : DifferentiableAt ℝ q z) :
    coveringCurl κ m (coveringPullbackCovector Ξ q) z =
      curlMatrix ((fderiv ℝ Ξ z.1).adjoint.comp
        ((fderiv ℝ q z).comp (EulerGraphPullback.liftedDirection κ m))) := by
  have hD : DifferentiableAt ℝ (fderiv ℝ Ξ) z.1 :=
    ((hΞ.fderiv_right (m := 1) le_rfl).differentiable one_ne_zero).differentiableAt
  have hX : HasFDerivAt (fun w : LiftTangent => fderiv ℝ Ξ w.1)
      ((fderiv ℝ (fderiv ℝ Ξ) z.1).comp (ContinuousLinearMap.fst ℝ Space ℝ)) z :=
    hD.hasFDerivAt.comp z hasFDerivAt_fst
  have hA : HasFDerivAt (fun w : LiftTangent => (fderiv ℝ Ξ w.1).adjoint)
      ((realAdjoint (U := Space) (E := Space)).comp
        ((fderiv ℝ (fderiv ℝ Ξ) z.1).comp (ContinuousLinearMap.fst ℝ Space ℝ))) z :=
    (realAdjoint (U := Space) (E := Space)).hasFDerivAt.comp z hX
  have hp := hA.clm_apply hq.hasFDerivAt
  have hzero : curlMatrix
      ((((realAdjoint (U := Space) (E := Space)).comp
        ((fderiv ℝ (fderiv ℝ Ξ) z.1).comp (ContinuousLinearMap.fst ℝ Space ℝ))).flip (q z)).comp
          (EulerGraphPullback.liftedDirection κ m)) = 0 := by
    ext i
    simp only [curlMatrix, WithLp.ofLp_toLp, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply, EulerGraphPullback.liftedDirection_apply,
      ContinuousLinearMap.coe_fst', realAdjoint_apply, PiLp.zero_apply]
    change
      ((fderiv ℝ (fderiv ℝ Ξ) z.1 (κ • EuclideanSpace.single (i + 1) 1)).adjoint (q z)) (i + 2) -
      ((fderiv ℝ (fderiv ℝ Ξ) z.1 (κ • EuclideanSpace.single (i + 2) 1)).adjoint (q z)) (i + 1) = 0
    rw [adjoint_apply_coordinate, adjoint_apply_coordinate]
    simp only [map_smul, smul_apply, real_inner_smul_left]
    have hs := ((hΞ.contDiffAt (x := z.1)).isSymmSndFDerivAt (n := 2) (by simp)).eq
      (EuclideanSpace.single (i + 1) 1) (EuclideanSpace.single (i + 2) 1)
    rw [hs, sub_self]
  change curlMatrix ((fderiv ℝ (fun w : LiftTangent => (fderiv ℝ Ξ w.1).adjoint (q w)) z).comp
      (EulerGraphPullback.liftedDirection κ m)) = _
  rw [hp.fderiv, ContinuousLinearMap.add_comp, curlMatrix_add, hzero, add_zero]
  rfl

/-- Unit determinant transforms the full slow-plus-angular curl by the inverse Jacobian. -/
theorem covering_piola_curl (κ : ℝ) (m : Space) (Ξ : Space → Space)
    (q : LiftTangent → Space) (hΞ : ContDiff ℝ 2 Ξ) (z : LiftTangent)
    (F : Space ≃L[ℝ] Space) (hF : fderiv ℝ Ξ z.1 = F.toContinuousLinearMap)
    (hdet : (operatorMatrix F.toContinuousLinearMap).det = 1)
    (hq : DifferentiableAt ℝ q z) :
    F.symm (curlMatrix ((fderiv ℝ q z).comp
      ((EulerGraphPullback.liftedDirection κ m).comp F.symm.toContinuousLinearMap))) =
      coveringCurl κ m (coveringPullbackCovector Ξ q) z := by
  rw [coveringCurl_pullback κ m Ξ q hΞ z hq, hF]
  exact (curlMatrix_piola F hdet
    ((fderiv ℝ q z).comp (EulerGraphPullback.liftedDirection κ m))).symm

variable (period : ℝ)

def liftedPullbackCovector (Ξ : Space → Space) (Q : LiftDomain period → Space)
    (x : LiftDomain period) : Space :=
  (fderiv ℝ Ξ x.1).adjoint (Q x)

def transformedLiftedCurl (κ : ℝ) (m : Space)
    (F : Space → Space ≃L[ℝ] Space) (Q : LiftDomain period → Space)
    (x : LiftDomain period) : Space :=
  curlMatrix ((fieldFDeriv period Q x).comp
    ((EulerGraphPullback.liftedDirection κ m).comp (F x.1).symm.toContinuousLinearMap))

/-- The actual local chart of the pulled-back potential. -/
theorem localFieldLift_pullbackCovector (Ξ : Space → Space)
    (Q : LiftDomain period → Space) (x : LiftDomain period) :
    localFieldLift period (liftedPullbackCovector period Ξ Q) x =
      coveringPullbackCovector (fun y => Ξ (x.1 + y)) (localFieldLift period Q x) := by
  funext z
  simp only [localFieldLift, liftedPullbackCovector, coveringPullbackCovector,
    fderiv_comp_add_left]

/-- The Piola curl identity for the periodic packet, with the actual scaled lifted directions. -/
theorem lifted_piola_curl (κ : ℝ) (m : Space) (Ξ : Space → Space)
    (Q : LiftDomain period → Space) (hΞ : ContDiff ℝ 2 Ξ)
    (F : Space → Space ≃L[ℝ] Space)
    (hF : ∀ y, fderiv ℝ Ξ y = (F y).toContinuousLinearMap)
    (hdet : ∀ y, (operatorMatrix (F y).toContinuousLinearMap).det = 1)
    (hQ : ∀ x, ContDiff ℝ ∞ (localFieldLift period Q x)) (x : LiftDomain period) :
    (F x.1).symm (transformedLiftedCurl period κ m F Q x) =
      liftedCurl period κ m (liftedPullbackCovector period Ξ Q) x := by
  have hshift : ContDiff ℝ 2 (fun y => Ξ (x.1 + y)) :=
    hΞ.comp (contDiff_const.add contDiff_id)
  have hF0 : fderiv ℝ (fun y => Ξ (x.1 + y)) (0 : LiftTangent).1 =
      (F x.1).toContinuousLinearMap := by
    simpa only [fderiv_comp_add_left, Prod.fst_zero, add_zero] using hF x.1
  have he := covering_piola_curl κ m (fun y => Ξ (x.1 + y))
    (localFieldLift period Q x) hshift 0 (F x.1) hF0 (hdet x.1)
    (((hQ x).differentiable (by simp)).differentiableAt)
  simpa only [transformedLiftedCurl, liftedCurl, fieldFDeriv, coveringCurl,
    ← localFieldLift_pullbackCovector period Ξ Q x] using he

theorem liftedPullbackCovector_smooth (Ξ : Space → Space)
    (Q : LiftDomain period → Space) (hΞ : ContDiff ℝ ∞ Ξ)
    (hQ : ∀ x, ContDiff ℝ ∞ (localFieldLift period Q x)) (x : LiftDomain period) :
    ContDiff ℝ ∞ (localFieldLift period (liftedPullbackCovector period Ξ Q) x) := by
  change ContDiff ℝ ∞ (fun z : LiftTangent =>
    (fderiv ℝ Ξ (x.1 + z.1)).adjoint (localFieldLift period Q x z))
  exact ((realAdjoint (U := Space) (E := Space)).contDiff.comp
    ((hΞ.fderiv_right (m := ∞) (by simp)).comp
      (contDiff_const.add contDiff_fst))).clm_apply (hQ x)

theorem liftedPullbackCovector_compact (Ξ : Space → Space)
    (Q : LiftDomain period → Space) (hc : HasCompactSupport Q) :
    HasCompactSupport (liftedPullbackCovector period Ξ Q) := by
  apply hc.mono
  intro x hx
  contrapose! hx
  simp only [Function.mem_support, not_not] at hx ⊢
  simp only [liftedPullbackCovector, hx, map_zero]

/-- Actual pointwise lifted divergence vanishes for the transformed packet curl. -/
theorem lifted_divergence_piola_curl (κ : ℝ) (m : Space) (Ξ : Space → Space)
    (Q : LiftDomain period → Space) (hΞ : ContDiff ℝ ∞ Ξ)
    (F : Space → Space ≃L[ℝ] Space)
    (hF : ∀ y, fderiv ℝ Ξ y = (F y).toContinuousLinearMap)
    (hdet : ∀ y, (operatorMatrix (F y).toContinuousLinearMap).det = 1)
    (hQ : ∀ x, ContDiff ℝ ∞ (localFieldLift period Q x)) (x : LiftDomain period) :
    (∑ i : Fin 3, (fieldDerivative period (coordinateDirection κ m i)
      (fun y => (F y.1).symm (transformedLiftedCurl period κ m F Q y)) x) i) = 0 := by
  have he : (fun y => (F y.1).symm (transformedLiftedCurl period κ m F Q y)) =
      liftedCurl period κ m (liftedPullbackCovector period Ξ Q) :=
    funext fun y => lifted_piola_curl period κ m Ξ Q (hΞ.of_le (by simp)) F hF hdet hQ y
  rw [he]
  exact lifted_divergence_curl period κ m _ (liftedPullbackCovector_smooth period Ξ Q hΞ hQ) x

variable [Fact (0 < period)]

/-- A genuine Bochner L² realization of the pulled-back packet curl. -/
def piolaLiftedCurlLp (κ : ℝ) (m : Space) (Ξ : Space → Space)
    (Q : LiftDomain period → Space) (hΞ : ContDiff ℝ ∞ Ξ)
    (hc : HasCompactSupport Q) (hQ : ∀ x, ContDiff ℝ ∞ (localFieldLift period Q x)) :
    LiftL2 period :=
  liftedCurlLp period κ m (liftedPullbackCovector period Ξ Q)
    (liftedPullbackCovector_compact period Ξ Q hc)
    (liftedPullbackCovector_smooth period Ξ Q hΞ hQ)

theorem piolaLiftedCurlLp_ae (κ : ℝ) (m : Space) (Ξ : Space → Space)
    (Q : LiftDomain period → Space) (hΞ : ContDiff ℝ ∞ Ξ)
    (hc : HasCompactSupport Q) (hQ : ∀ x, ContDiff ℝ ∞ (localFieldLift period Q x))
    (F : Space → Space ≃L[ℝ] Space)
    (hF : ∀ y, fderiv ℝ Ξ y = (F y).toContinuousLinearMap)
    (hdet : ∀ y, (operatorMatrix (F y).toContinuousLinearMap).det = 1) :
    (piolaLiftedCurlLp period κ m Ξ Q hΞ hc hQ : LiftDomain period → Space) =ᵐ[liftMeasure period]
      (fun x => (F x.1).symm (transformedLiftedCurl period κ m F Q x)) := by
  filter_upwards [liftedCurlLp_ae period κ m (liftedPullbackCovector period Ξ Q)
    (liftedPullbackCovector_compact period Ξ Q hc)
    (liftedPullbackCovector_smooth period Ξ Q hΞ hQ)] with x hx
  exact hx.trans (lifted_piola_curl period κ m Ξ Q (hΞ.of_le (by simp)) F hF hdet hQ x).symm

/-- The pulled-back packet satisfies the exact closed constraint used by correction assembly. -/
theorem piolaLiftedCurlLp_mem (κ : ℝ) (m : Space) (Ξ : Space → Space)
    (Q : LiftDomain period → Space) (hΞ : ContDiff ℝ ∞ Ξ)
    (hc : HasCompactSupport Q) (hQ : ∀ x, ContDiff ℝ ∞ (localFieldLift period Q x)) :
    piolaLiftedCurlLp period κ m Ξ Q hΞ hc hQ ∈ divergenceFreeSpace period κ m :=
  liftedCurlLp_mem period κ m (liftedPullbackCovector period Ξ Q)
    (liftedPullbackCovector_compact period Ξ Q hc)
    (liftedPullbackCovector_smooth period Ξ Q hΞ hQ)

end EulerPacketPiola
