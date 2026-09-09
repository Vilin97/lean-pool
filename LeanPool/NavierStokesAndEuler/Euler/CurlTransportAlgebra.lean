/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanVectorIdentities
public import LeanPool.NavierStokesAndEuler.Euler.MeanScalarProductDerivatives

@[expose] public section

/-! The ordinary curl identity for the Euler convection term on ℝ³. -/

noncomputable section

namespace EulerComparatorCurlTransport

open InnerProductSpace EulerSmoothLimit EulerVectorCalculus EulerMeanCutoffCurl
  EulerMeanHarmonic EulerMeanVectorIdentities EulerMeanBoundary
open scoped ContDiff

theorem fderiv_apply_coordinate_sum (f : Space → Space) (hf : ContDiff ℝ ∞ f)
    (x v : Space) (i : Fin 3) :
    (fderiv ℝ f x v) i =
      ∑ j : Fin 3, v j * partialDerivative (fun y => f y i) j x := by
  rw [← fderiv_coordinate f x (hf.differentiable (by simp)).differentiableAt i v]
  have hre : ∑ j : Fin 3, v j • (EuclideanSpace.single j 1 : Space) = v := by
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr v
  calc
    _ = fderiv ℝ (fun y => f y i) x
        (∑ j : Fin 3, v j • EuclideanSpace.single j 1) :=
      congrArg (fderiv ℝ (fun y => f y i) x) hre.symm
    _ = _ := by simp only [map_sum, map_smul, smul_eq_mul, partialDerivative]

/-- Curl of the material convection term, including the compressible correction. -/
theorem vectorCurl_convection (u : Space → Space) (hu : ContDiff ℝ ∞ u) (x : Space) :
    vectorCurl (fun y => fderiv ℝ u y (u y)) x =
      fderiv ℝ (vectorCurl u) x (u x) - fderiv ℝ u x (vectorCurl u x) +
        divergence u x • vectorCurl u x := by
  have hc (i : Fin 3) : ContDiff ℝ ∞ (fun y => u y i) := (contDiff_piLp 2).mp hu i
  have hp (i j : Fin 3) : ContDiff ℝ ∞ (partialDerivative (fun y => u y i) j) :=
    contDiff_partialDerivative _ (hc i) j
  have hconv (i : Fin 3) :
      (fun y => (fderiv ℝ u y (u y)) i) =
        fun y => ∑ j : Fin 3, u y j * partialDerivative (fun z => u z i) j y := by
    funext y
    exact fderiv_apply_coordinate_sum u hu y (u y) i
  have hconvpart (i k : Fin 3) :
      partialDerivative (fun y => (fderiv ℝ u y (u y)) i) k x =
        ∑ j : Fin 3,
          (partialDerivative (fun y => u y i) j x *
            partialDerivative (fun y => u y j) k x +
          u x j * partialDerivative (partialDerivative (fun y => u y i) j) k x) := by
    rw [hconv i, partialDerivative_sum _ (fun j => (hc j).mul (hp i j))]
    apply Finset.sum_congr rfl
    intro j _
    exact EulerMeanHarmonic.partialDerivative_mul
      ((hc j).differentiable (by simp)).differentiableAt
      ((hp i j).differentiable (by simp)).differentiableAt k
  have hcurlpart (i k : Fin 3) :
      partialDerivative (fun y => vectorCurl u y i) k x =
        partialDerivative (partialDerivative (fun y => u y (i+2)) (i+1)) k x -
        partialDerivative (partialDerivative (fun y => u y (i+1)) (i+2)) k x := by
    simp only [vectorCurl, curl_apply]
    exact EulerMeanVectorIdentities.partialDerivative_sub _ _ (hp _ _) (hp _ _) k x
  have hcomm01 (a : Fin 3) :
      partialDerivative (partialDerivative (fun y => u y a) 0) 1 x =
        partialDerivative (partialDerivative (fun y => u y a) 1) 0 x :=
    partialDerivative_comm _ ((hc a).of_le (by simp)) 0 1 x
  have hcomm02 (a : Fin 3) :
      partialDerivative (partialDerivative (fun y => u y a) 0) 2 x =
        partialDerivative (partialDerivative (fun y => u y a) 2) 0 x :=
    partialDerivative_comm _ ((hc a).of_le (by simp)) 0 2 x
  have hcomm12 (a : Fin 3) :
      partialDerivative (partialDerivative (fun y => u y a) 1) 2 x =
        partialDerivative (partialDerivative (fun y => u y a) 2) 1 x :=
    partialDerivative_comm _ ((hc a).of_le (by simp)) 1 2 x
  ext i
  simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  rw [fderiv_apply_coordinate_sum (vectorCurl u) (vectorCurl_smooth u hu) x (u x) i,
    fderiv_apply_coordinate_sum u hu x (vectorCurl u x) i]
  simp only [hcurlpart, divergence_coordinate_sum u hu]
  conv_lhs => simp only [vectorCurl, curl_apply]
  rw [hconvpart, hconvpart]
  simp only [vectorCurl, curl_apply]
  fin_cases i <;>
    norm_num [Fin.sum_univ_three, Fin.add_def] <;>
    simp only [show (⟨2, by decide⟩ : Fin 3) = 2 from rfl] <;>
    simp only [hcomm01, hcomm02, hcomm12] <;> ring!

/-- The form of curl transport used for incompressible Euler. -/
theorem vectorCurl_convection_of_divergence_zero (u : Space → Space)
    (hu : ContDiff ℝ ∞ u) (x : Space) (hdiv : divergence u x = 0) :
    vectorCurl (fun y => fderiv ℝ u y (u y)) x =
      fderiv ℝ (vectorCurl u) x (u x) - fderiv ℝ u x (vectorCurl u x) := by
  simpa only [hdiv, zero_smul, add_zero] using vectorCurl_convection u hu x

/-- Ordinary gradients have zero ordinary curl. -/
theorem vectorCurl_gradient_zero (p : Space → ℝ) (hp : ContDiff ℝ ∞ p) (x : Space) :
    vectorCurl (gradient p) x = 0 := by
  ext i
  simp only [vectorCurl, curl_apply, gradient_coordinate, PiLp.zero_apply]
  exact sub_eq_zero.mpr (partialDerivative_comm p (hp.of_le (by simp)) (i+2) (i+1) x)

theorem vectorCurl_neg (f : Space → Space) (hf : Differentiable ℝ f) :
    vectorCurl (-f) = -vectorCurl f := by
  simpa only [neg_one_smul] using vectorCurl_smul (-1) f hf

theorem vectorCurl_sub (f g : Space → Space)
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    vectorCurl (f-g) = vectorCurl f - vectorCurl g := by
  rw [sub_eq_add_neg, vectorCurl_add f (-g) hf hg.neg, vectorCurl_neg g hg,
    sub_eq_add_neg]

/-- Taking curl removes pressure and gives the Euler vorticity right-hand side. -/
theorem vectorCurl_euler_rhs (u : Space → Space) (p : Space → ℝ)
    (hu : ContDiff ℝ ∞ u) (hp : ContDiff ℝ ∞ p) (x : Space)
    (hdiv : divergence u x = 0) :
    vectorCurl (fun y => -fderiv ℝ u y (u y) - gradient p y) x =
      fderiv ℝ u x (vectorCurl u x) - fderiv ℝ (vectorCurl u) x (u x) := by
  have hc : Differentiable ℝ (fun y => fderiv ℝ u y (u y)) :=
    ((hu.fderiv_right (m := ∞) (by simp)).clm_apply hu).differentiable (by simp)
  have hpg : Differentiable ℝ (gradient p) :=
    (EulerMeanSolenoidal.contDiff_gradient hp).differentiable (by simp)
  change vectorCurl (-(fun y => fderiv ℝ u y (u y)) - gradient p) x = _
  rw [vectorCurl_sub _ _ hc.neg hpg, vectorCurl_neg _ hc]
  simp only [Pi.sub_apply, Pi.neg_apply, vectorCurl_gradient_zero p hp x,
    vectorCurl_convection_of_divergence_zero u hu x hdiv, sub_zero, neg_sub]

end EulerComparatorCurlTransport
