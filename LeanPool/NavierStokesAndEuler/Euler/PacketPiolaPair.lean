/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketLiftedPiola
public import LeanPool.NavierStokesAndEuler.Euler.PacketAngularPotential

@[expose] public section

/-!
The exact fast/slow splitting of the packet curl.  The angular term is the
ordinary cross product with `F⁻ᵀ m₀`; the angular primitive then produces the
literal pair `A + κ C`.  Its weighted pullback is realized in the actual
lifted divergence-free L² space.
-/

noncomputable section


namespace EulerPacketPiola

open MeasureTheory InnerProductSpace EulerSmoothLimit EulerMeanBoundary
  EulerLiftedGradientSpace EulerMetricTransport EulerTransportDerivatives
  EulerLiftedWeakDerivative EulerPacketCrossProduct EulerPacketAngularPotential
open scoped ContDiff

theorem curlMatrix_rankOne (a b : Space) :
    curlMatrix (rankOne ℝ a b) = cross b a := by
  ext i
  fin_cases i <;>
    simp [curlMatrix, rankOne_apply, EuclideanSpace.inner_single_right,
      cross, cross_apply]

/-- The actual four-dimensional derivative splits into its slow and angular parts. -/
theorem curl_lifted_split (κ : ℝ) (m : Space) (L : LiftTangent →L[ℝ] Space)
    (G : Space →L[ℝ] Space) :
    curlMatrix (L.comp ((EulerGraphPullback.liftedDirection κ m).comp G)) =
      κ • curlMatrix (L.comp ((ContinuousLinearMap.inl ℝ Space ℝ).comp G)) +
        cross (G.adjoint m) (L (0, 1)) := by
  have he : L.comp ((EulerGraphPullback.liftedDirection κ m).comp G) =
      κ • (L.comp ((ContinuousLinearMap.inl ℝ Space ℝ).comp G)) +
        rankOne ℝ (L (0, 1)) (G.adjoint m) := by
    apply ContinuousLinearMap.ext
    intro v
    change L (κ • G v, ⟪m, G v⟫_ℝ) =
      κ • L (G v, 0) + ⟪G.adjoint m, v⟫_ℝ • L (0, 1)
    rw [G.adjoint_inner_left]
    have hv : (κ • G v, ⟪m, G v⟫_ℝ) =
        κ • (G v, (0 : ℝ)) + ⟪m, G v⟫_ℝ • ((0 : Space), (1 : ℝ)) := by
      ext <;> simp
    rw [hv, map_add, map_smul, map_smul]
  rw [he, curlMatrix_add, curlMatrix_smul, curlMatrix_rankOne]

def coveringSlowCurl (G : Space →L[ℝ] Space) (q : LiftTangent → Space)
    (z : LiftTangent) : Space :=
  curlMatrix ((fderiv ℝ q z).comp ((ContinuousLinearMap.inl ℝ Space ℝ).comp G))

/-- The same angular primitive as in the source, at each ordinary label. -/
def coveringPotential (P : ℝ) (m : Space → Space) (A : LiftTangent → Space)
    (z : LiftTangent) : Space :=
  potential P (m z.1) (fun θ => A (z.1, θ)) z.2

/-- The derivative in the angle direction is proved from the actual primitive. -/
theorem coveringPotential_angle_derivative (P : ℝ) (m : Space → Space)
    (A : LiftTangent → Space) (z : LiftTangent)
    (hA : Continuous (fun θ => A (z.1, θ)))
    (hq : DifferentiableAt ℝ (coveringPotential P m A) z) :
    fderiv ℝ (coveringPotential P m A) z (0, 1) =
      potentialMultiplier (m z.1) (A z) := by
  have hline : HasDerivAt (fun θ => coveringPotential P m A (z.1, θ))
      (fderiv ℝ (coveringPotential P m A) z (0, 1)) z.2 :=
    by
      have hh : HasFDerivAt (coveringPotential P m A)
          (fderiv ℝ (coveringPotential P m A) z) (z.1, z.2) := hq.hasFDerivAt
      simpa only [Function.comp_def, id_eq] using hh.comp_hasDerivAt z.2
        ((hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2))
  exact hline.unique (potential_hasDerivAt P (m z.1) (fun θ => A (z.1, θ)) hA z.2)

/-- A literal source pair is a Piola curl for the actual constructed angular primitive. -/
theorem coveringPotential_pair_piola (P κ : ℝ) (m₀ : Space) (Ξ : Space → Space)
    (A : LiftTangent → Space) (hΞ : ContDiff ℝ 2 Ξ)
    (F : Space → Space ≃L[ℝ] Space) (z : LiftTangent)
    (hF : fderiv ℝ Ξ z.1 = (F z.1).toContinuousLinearMap)
    (hdet : (operatorMatrix (F z.1).toContinuousLinearMap).det = 1)
    (hm : (F z.1).symm.toContinuousLinearMap.adjoint m₀ ≠ 0)
    (htan : ⟪(F z.1).symm.toContinuousLinearMap.adjoint m₀, A z⟫_ℝ = 0)
    (hA : Continuous (fun θ => A (z.1, θ)))
    (hq : DifferentiableAt ℝ
      (coveringPotential P (fun y => (F y).symm.toContinuousLinearMap.adjoint m₀) A) z) :
    (F z.1).symm (A z + κ • coveringSlowCurl (F z.1).symm.toContinuousLinearMap
      (coveringPotential P (fun y => (F y).symm.toContinuousLinearMap.adjoint m₀) A) z) =
      coveringCurl κ m₀ (coveringPullbackCovector Ξ
        (coveringPotential P (fun y => (F y).symm.toContinuousLinearMap.adjoint m₀) A)) z := by
  have hp := covering_piola_curl κ m₀ Ξ _ hΞ z (F z.1) hF hdet hq
  rw [curl_lifted_split, coveringPotential_angle_derivative P _ A z hA hq,
    cross_potentialMultiplier _ _ hm htan] at hp
  simpa only [coveringSlowCurl, add_comm] using hp

variable (period : ℝ)

def liftedSlowCurl (F : Space → Space ≃L[ℝ] Space) (Q : LiftDomain period → Space)
    (x : LiftDomain period) : Space :=
  curlMatrix ((fieldFDeriv period Q x).comp
    ((ContinuousLinearMap.inl ℝ Space ℝ).comp (F x.1).symm.toContinuousLinearMap))

theorem transformedLiftedCurl_split (κ : ℝ) (m₀ : Space)
    (F : Space → Space ≃L[ℝ] Space) (Q : LiftDomain period → Space)
    (x : LiftDomain period) :
    transformedLiftedCurl period κ m₀ F Q x =
      κ • liftedSlowCurl period F Q x +
        cross ((F x.1).symm.toContinuousLinearMap.adjoint m₀)
          (fieldDerivative period (0, 1) Q x) :=
  curl_lifted_split κ m₀ (fieldFDeriv period Q x) (F x.1).symm.toContinuousLinearMap

/-- Only the actual angular derivative formula for Q is needed to identify the source pair. -/
theorem lifted_pair_piola (κ : ℝ) (m₀ : Space) (Ξ : Space → Space)
    (A Q : LiftDomain period → Space) (hΞ : ContDiff ℝ 2 Ξ)
    (F : Space → Space ≃L[ℝ] Space)
    (hF : ∀ y, fderiv ℝ Ξ y = (F y).toContinuousLinearMap)
    (hdet : ∀ y, (operatorMatrix (F y).toContinuousLinearMap).det = 1)
    (hQ : ∀ x, ContDiff ℝ ∞ (localFieldLift period Q x)) (x : LiftDomain period)
    (hm : (F x.1).symm.toContinuousLinearMap.adjoint m₀ ≠ 0)
    (htan : ⟪(F x.1).symm.toContinuousLinearMap.adjoint m₀, A x⟫_ℝ = 0)
    (hangle : fieldDerivative period (0, 1) Q x =
      potentialMultiplier ((F x.1).symm.toContinuousLinearMap.adjoint m₀) (A x)) :
    (F x.1).symm (A x + κ • liftedSlowCurl period F Q x) =
      liftedCurl period κ m₀ (liftedPullbackCovector period Ξ Q) x := by
  have hp := lifted_piola_curl period κ m₀ Ξ Q hΞ F hF hdet hQ x
  rw [transformedLiftedCurl_split, hangle, cross_potentialMultiplier _ _ hm htan] at hp
  simpa only [add_comm] using hp

/-- The exact powers in source (13), without discarding the terminal corrector. -/
theorem weighted_lifted_pair_piola (κ : ℝ) (m₀ : Space) (Ξ : Space → Space)
    (A Q : LiftDomain period → Space) (hΞ : ContDiff ℝ 2 Ξ)
    (F : Space → Space ≃L[ℝ] Space)
    (hF : ∀ y, fderiv ℝ Ξ y = (F y).toContinuousLinearMap)
    (hdet : ∀ y, (operatorMatrix (F y).toContinuousLinearMap).det = 1)
    (hQ : ∀ x, ContDiff ℝ ∞ (localFieldLift period Q x)) (x : LiftDomain period)
    (hm : (F x.1).symm.toContinuousLinearMap.adjoint m₀ ≠ 0)
    (htan : ⟪(F x.1).symm.toContinuousLinearMap.adjoint m₀, A x⟫_ℝ = 0)
    (hangle : fieldDerivative period (0, 1) Q x =
      potentialMultiplier ((F x.1).symm.toContinuousLinearMap.adjoint m₀) (A x)) (p : ℕ) :
    (F x.1).symm (κ ^ p • A x + κ ^ (p + 1) • liftedSlowCurl period F Q x) =
      κ ^ p • liftedCurl period κ m₀ (liftedPullbackCovector period Ξ Q) x := by
  have he : κ ^ p • A x + κ ^ (p + 1) • liftedSlowCurl period F Q x =
      κ ^ p • (A x + κ • liftedSlowCurl period F Q x) := by
    rw [smul_add, smul_smul, pow_succ]
  rw [he, map_smul, lifted_pair_piola period κ m₀ Ξ A Q hΞ F hF hdet hQ x hm htan hangle]

variable [Fact (0 < period)]

def piolaPairLp (κ : ℝ) (m₀ : Space) (Ξ : Space → Space)
    (Q : LiftDomain period → Space) (hΞ : ContDiff ℝ ∞ Ξ)
    (hc : HasCompactSupport Q) (hQ : ∀ x, ContDiff ℝ ∞ (localFieldLift period Q x)) (p : ℕ) :
    LiftL2 period := κ ^ p • piolaLiftedCurlLp period κ m₀ Ξ Q hΞ hc hQ

theorem piolaPairLp_mem (κ : ℝ) (m₀ : Space) (Ξ : Space → Space)
    (Q : LiftDomain period → Space) (hΞ : ContDiff ℝ ∞ Ξ)
    (hc : HasCompactSupport Q) (hQ : ∀ x, ContDiff ℝ ∞ (localFieldLift period Q x)) (p : ℕ) :
    piolaPairLp period κ m₀ Ξ Q hΞ hc hQ p ∈ divergenceFreeSpace period κ m₀ :=
  (divergenceFreeSpace period κ m₀).smul_mem (κ ^ p)
    (piolaLiftedCurlLp_mem period κ m₀ Ξ Q hΞ hc hQ)

theorem piolaPairLp_ae (κ : ℝ) (m₀ : Space) (Ξ : Space → Space)
    (A Q : LiftDomain period → Space) (hΞ : ContDiff ℝ ∞ Ξ)
    (hc : HasCompactSupport Q) (hQ : ∀ x, ContDiff ℝ ∞ (localFieldLift period Q x))
    (F : Space → Space ≃L[ℝ] Space)
    (hF : ∀ y, fderiv ℝ Ξ y = (F y).toContinuousLinearMap)
    (hdet : ∀ y, (operatorMatrix (F y).toContinuousLinearMap).det = 1)
    (hm : ∀ x, (F x).symm.toContinuousLinearMap.adjoint m₀ ≠ 0)
    (htan : ∀ x, ⟪(F x.1).symm.toContinuousLinearMap.adjoint m₀, A x⟫_ℝ = 0)
    (hangle : ∀ x, fieldDerivative period (0, 1) Q x =
      potentialMultiplier ((F x.1).symm.toContinuousLinearMap.adjoint m₀) (A x)) (p : ℕ) :
    (piolaPairLp period κ m₀ Ξ Q hΞ hc hQ p : LiftDomain period → Space) =ᵐ[liftMeasure period]
      fun x => (F x.1).symm (κ ^ p • A x + κ ^ (p + 1) • liftedSlowCurl period F Q x) := by
  filter_upwards [Lp.coeFn_smul (κ ^ p) (piolaLiftedCurlLp period κ m₀ Ξ Q hΞ hc hQ),
    liftedCurlLp_ae period κ m₀ (liftedPullbackCovector period Ξ Q)
      (liftedPullbackCovector_compact period Ξ Q hc)
      (liftedPullbackCovector_smooth period Ξ Q hΞ hQ)] with x hs hx
  calc
    piolaPairLp period κ m₀ Ξ Q hΞ hc hQ p x =
        κ ^ p • piolaLiftedCurlLp period κ m₀ Ξ Q hΞ hc hQ x := hs
    _ = κ ^ p • liftedCurl period κ m₀ (liftedPullbackCovector period Ξ Q) x :=
      congrArg (fun v : Space => κ ^ p • v) hx
    _ = (F x.1).symm (κ ^ p • A x + κ ^ (p + 1) • liftedSlowCurl period F Q x) :=
      (weighted_lifted_pair_piola period κ m₀ Ξ A Q (hΞ.of_le (by simp)) F hF hdet hQ x
        (hm x.1) (htan x) (hangle x) p).symm

end EulerPacketPiola
