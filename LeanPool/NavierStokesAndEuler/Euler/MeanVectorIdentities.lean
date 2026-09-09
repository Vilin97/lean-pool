/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanCurlTensor
public import LeanPool.NavierStokesAndEuler.Euler.MeanHarmonicDerivatives

@[expose] public section

/-! Ordinary smooth vector-calculus identities with the canonical Mathlib Laplacian. -/

noncomputable section

namespace EulerMeanVectorIdentities

open MeasureTheory InnerProductSpace Laplacian EulerSmoothLimit EulerVectorCalculus
  EulerMeanSolenoidal EulerMeanCutoffCurl EulerMeanGradientTest EulerMeanHarmonic
open scoped ContDiff

def vectorPartial (f : Space → Space) (i : Fin 3) (x : Space) : Space :=
  fderiv ℝ f x (EuclideanSpace.single i 1)

theorem vectorPartial_smooth (f : Space → Space) (hf : ContDiff ℝ ∞ f) (i : Fin 3) :
    ContDiff ℝ ∞ (vectorPartial f i) :=
  (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem vectorPartial_compact (f : Space → Space) (hc : HasCompactSupport f) (i : Fin 3) :
    HasCompactSupport (vectorPartial f i) := hc.fderiv_apply ℝ (EuclideanSpace.single i 1)

theorem vectorPartial_apply (f : Space → Space) (hf : ContDiff ℝ ∞ f)
    (i j : Fin 3) (x : Space) :
    vectorPartial f i x j = partialDerivative (fun y => f y j) i x :=
  (fderiv_coordinate f x ((hf.differentiable (by simp)).differentiableAt)
    j (EuclideanSpace.single i 1)).symm

theorem vector_laplacian_coordinate (f : Space → Space) (hf : ContDiff ℝ ∞ f)
    (x : Space) (i : Fin 3) :
    (Δ f x) i = Δ (fun y => f y i) x := by
  have h2 : ContDiffAt ℝ 2 f x := (hf.of_le (by simp)).contDiffAt
  exact (h2.laplacian_CLM_comp_left (l := EuclideanSpace.proj i)).symm

theorem vector_laplacian_eq_sum (f : Space → Space) (hf : ContDiff ℝ ∞ f) :
    Δ f = fun x => ∑ i : Fin 3, vectorPartial (vectorPartial f i) i x := by
  funext x
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis f (EuclideanSpace.basisFun (Fin 3) ℝ)]
  apply Finset.sum_congr rfl
  intro i _
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp)).differentiableAt
  simp only [EuclideanSpace.basisFun_apply, iteratedFDeriv_two_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, vectorPartial]
  change _ = (fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.single i 1)) x)
    (EuclideanSpace.single i 1)
  rw [fderiv_clm_apply hdf (differentiableAt_const _)]
  simp

theorem vector_laplacian_smooth (f : Space → Space) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (Δ f) := by
  rw [vector_laplacian_eq_sum f hf]
  exact ContDiff.sum (fun i _ => vectorPartial_smooth _ (vectorPartial_smooth f hf i) i)

theorem vector_laplacian_compact (f : Space → Space) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) : HasCompactSupport (Δ f) := by
  rw [vector_laplacian_eq_sum f hf]
  simp only [Fin.sum_univ_three]
  exact ((vectorPartial_compact _ (vectorPartial_compact f hc 0) 0).add
    (vectorPartial_compact _ (vectorPartial_compact f hc 1) 1)).add
    (vectorPartial_compact _ (vectorPartial_compact f hc 2) 2)

theorem vectorCurl_smooth (f : Space → Space) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (vectorCurl f) := contDiff_curl _ ((contDiff_piLp 2).mp hf)

theorem vectorCurl_support (f : Space → Space) : tsupport (vectorCurl f) ⊆ tsupport f :=
  tsupport_curl_subset _ _ (isClosed_tsupport f)
    (fun i => tsupport_comp_subset (g := fun v : Space => v i) rfl f)

theorem vectorCurl_compact (f : Space → Space) (hc : HasCompactSupport f) :
    HasCompactSupport (vectorCurl f) := hc.of_isClosed_subset
      (isClosed_tsupport _) (vectorCurl_support f)

def curlTest (f : Test) : Test :=
  ⟨vectorCurl (f : Space → Space), vectorCurl_smooth f f.smooth, vectorCurl_compact f f.compact⟩

def laplacianTest (f : Test) : Test :=
  ⟨Δ (f : Space → Space), vector_laplacian_smooth f f.smooth,
    vector_laplacian_compact f f.smooth f.compact⟩

theorem divergence_coordinate_sum (f : Space → Space) (hf : ContDiff ℝ ∞ f) :
    divergence f = fun x => ∑ i : Fin 3, partialDerivative (fun y => f y i) i x := by
  funext x
  rw [divergence_eq_coordinate_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact (fderiv_coordinate f x ((hf.differentiable (by simp)).differentiableAt)
    i (EuclideanSpace.single i 1)).symm

theorem divergence_smooth (f : Space → Space) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (divergence f) := by
  rw [divergence_coordinate_sum f hf]
  exact ContDiff.sum (fun i _ => contDiff_partialDerivative _ ((contDiff_piLp 2).mp hf i) i)

theorem partialDerivative_sub (f g : Space → ℝ) (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (i : Fin 3) (x : Space) :
    partialDerivative (fun y => f y - g y) i x = partialDerivative f i x - partialDerivative g i x
      := by
  unfold partialDerivative
  rw [fderiv_fun_sub ((hf.differentiable (by simp)).differentiableAt)
    ((hg.differentiable (by simp)).differentiableAt)]
  rfl

/-- The classical curl-curl identity, with genuine Fréchet derivatives and canonical Laplacian. -/
theorem vectorCurl_vectorCurl (f : Space → Space) (hf : ContDiff ℝ ∞ f) :
    vectorCurl (vectorCurl f) = gradient (divergence f) - Δ f := by
  have hc (i : Fin 3) : ContDiff ℝ ∞ (fun y => f y i) := (contDiff_piLp 2).mp hf i
  have hsub (a b c d e : Fin 3) (x : Space) :
      partialDerivative (fun y => partialDerivative (fun z => f z a) b y -
        partialDerivative (fun z => f z c) d y) e x =
      partialDerivative (partialDerivative (fun z => f z a) b) e x -
        partialDerivative (partialDerivative (fun z => f z c) d) e x :=
    partialDerivative_sub _ _ (contDiff_partialDerivative _ (hc a) b)
      (contDiff_partialDerivative _ (hc c) d) e x
  have hcomm (a i j : Fin 3) (x : Space) :
      partialDerivative (partialDerivative (fun z => f z a) i) j x =
        partialDerivative (partialDerivative (fun z => f z a) j) i x :=
    partialDerivative_comm _ ((hc a).of_le (by simp)) i j x
  funext x
  let d (a i j : Fin 3) := partialDerivative (partialDerivative (fun z => f z a) i) j x
  ext i
  simp only [Pi.sub_apply, PiLp.sub_apply, gradient_coordinate, vector_laplacian_coordinate f hf,
    divergence_coordinate_sum f hf,
    partialDerivative_sum _ (fun j => contDiff_partialDerivative _ (hc j) j),
    laplacian_eq_coordinate_sum _ (hc i), vectorCurl, curl_apply, hsub]
  fin_cases i
  · norm_num [Fin.sum_univ_three, Fin.add_def]
    change d 1 0 1 - d 0 1 1 - (d 0 2 2 - d 2 0 2) =
      d 0 0 0 + d 1 1 0 + d 2 2 0 - (d 0 0 0 + d 0 1 1 + d 0 2 2)
    have h₁ : d 1 0 1 = d 1 1 0 := hcomm 1 0 1 x
    have h₂ : d 2 0 2 = d 2 2 0 := hcomm 2 0 2 x
    linarith
  · norm_num [Fin.sum_univ_three, Fin.add_def]
    change d 2 1 2 - d 1 2 2 - (d 1 0 0 - d 0 1 0) =
      d 0 0 1 + d 1 1 1 + d 2 2 1 - (d 1 0 0 + d 1 1 1 + d 1 2 2)
    have h₁ : d 0 1 0 = d 0 0 1 := hcomm 0 1 0 x
    have h₂ : d 2 1 2 = d 2 2 1 := hcomm 2 1 2 x
    linarith
  · norm_num [Fin.sum_univ_three, Fin.add_def]
    change d 0 2 0 - d 2 0 0 - (d 2 1 1 - d 1 2 1) =
      d 0 0 2 + d 1 1 2 + d 2 2 2 - (d 2 0 0 + d 2 1 1 + d 2 2 2)
    have h₁ : d 0 2 0 = d 0 0 2 := hcomm 0 2 0 x
    have h₂ : d 1 2 1 = d 1 1 2 := hcomm 1 2 1 x
    linarith

theorem divergence_compact (f : Space → Space) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) : HasCompactSupport (divergence f) := by
  rw [divergence_coordinate_sum f hf]
  have hpart (i : Fin 3) : HasCompactSupport (partialDerivative (fun y => f y i) i) :=
    (hc.comp_left (g := fun v : Space => v i) rfl).fderiv_apply ℝ (EuclideanSpace.single i 1)
  simp only [Fin.sum_univ_three]
  change HasCompactSupport (partialDerivative (fun y => f y 0) 0 +
    partialDerivative (fun y => f y 1) 1 + partialDerivative (fun y => f y 2) 2)
  exact ((hpart 0).add (hpart 1)).add (hpart 2)

/-- The ordinary curl commutes with the canonical vector-valued Laplacian. -/
theorem laplacian_vectorCurl (f : Space → Space) (hf : ContDiff ℝ ∞ f) :
    Δ (vectorCurl f) = vectorCurl (Δ f) := by
  have hc (i : Fin 3) : ContDiff ℝ ∞ (fun y => f y i) := (contDiff_piLp 2).mp hf i
  have heq (i : Fin 3) : (fun y => (Δ f y) i) = Δ (fun y => f y i) :=
    funext fun y => vector_laplacian_coordinate f hf y i
  funext x
  ext i
  rw [vector_laplacian_coordinate _ (vectorCurl_smooth f hf)]
  change Δ (partialDerivative (fun y => f y (i+2)) (i+1) -
      partialDerivative (fun y => f y (i+1)) (i+2)) x =
    partialDerivative (fun y => (Δ f y) (i+2)) (i+1) x -
      partialDerivative (fun y => (Δ f y) (i+1)) (i+2) x
  rw [((contDiff_partialDerivative _ (hc (i+2)) (i+1)).of_le (by simp)).contDiffAt.laplacian_sub
    ((contDiff_partialDerivative _ (hc (i+1)) (i+2)).of_le (by simp)).contDiffAt]
  simp only [laplacian_partialDerivative _ (hc _), heq]

end EulerMeanVectorIdentities
