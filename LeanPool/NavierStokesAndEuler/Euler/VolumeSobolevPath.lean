/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.VolumeSobolevComposition
public import LeanPool.NavierStokesAndEuler.Euler.LpPointwiseMultiplier

@[expose] public section

/-! Strong Sobolev continuity under genuine varying volume-preserving
maps. Faà di Bruno gives actual derivative tensors, and dominated
convergence handles the bounded, pointwise continuous coefficients. -/

noncomputable section

namespace EulerVolumeSobolevPath

open MeasureTheory Filter EulerMetricTransport EulerLiftedGradientSpace
  EulerLpPointwiseMultiplier
open scoped Topology ContDiff

abbrev Tensor (n : ℕ) := Vector3 [×n]→L[ℝ] Vector3

private local instance (n : ℕ) : NormedAddCommGroup (Tensor n) := inferInstance
private local instance (n : ℕ) : NormedSpace ℝ (Tensor n) := inferInstance
private local instance (a b : ℕ) : NormedAddCommGroup (Tensor a →L[ℝ] Tensor b) := inferInstance
private local instance (a b : ℕ) : NormedSpace ℝ (Tensor a →L[ℝ] Tensor b) := inferInstance
private local instance (a b : ℕ) : SecondCountableTopologyEither Vector3 (Tensor a →L[ℝ] Tensor b)
  :=
  ⟨Or.inl inferInstance⟩

variable {K : Type*} [TopologicalSpace K]
  (Y : C(K,C(Vector3,Vector3))) (hmp : ∀ t, MeasurePreserving (Y t) volume volume)
  (u : ∀ i : ℕ, C(K,Lp (Tensor i) 2 (volume : Measure Vector3)))

def pulledJetPath (i : ℕ) : C(K,Lp (Tensor i) 2 (volume : Measure Vector3)) where
  toFun t := Lp.compMeasurePreserving (Y t) (hmp t) (u i t)
  continuous_toFun := (u i).continuous.compMeasurePreservingLp Y.continuous hmp (by norm_num)

theorem pulledJetPath_ae (g : K → Vector3 → Vector3)
    (hu : ∀ i t, (u i t : Vector3 → Tensor i) =ᵐ[volume] iteratedFDeriv ℝ i (g t))
    (i : ℕ) (t : K) :
    (pulledJetPath Y hmp u i t : Vector3 → Tensor i) =ᵐ[volume]
      fun x => iteratedFDeriv ℝ i (g t) (Y t x) :=
  (Lp.coeFn_compMeasurePreserving (u i t) (hmp t)).trans
    ((hmp t).quasiMeasurePreserving.ae_eq_comp (hu i t))

variable {n : ℕ}

def partitionCoefficient (c : OrderedFinpartition n) (t : K) (x : Vector3) :
    Tensor c.length →L[ℝ] Tensor n :=
  (c.compAlongOrderedFinpartitionL ℝ Vector3 Vector3 Vector3).flipMultilinear
    (fun i => iteratedFDeriv ℝ (c.partSize i) (Y t) x)

theorem partitionCoefficient_apply (c : OrderedFinpartition n) (t : K) (x : Vector3)
    (v : Tensor c.length) :
    partitionCoefficient Y c t x v = c.compAlongOrderedFinpartition v
      (fun i => iteratedFDeriv ℝ (c.partSize i) (Y t) x) := rfl

def partitionBound (D : ℝ) (c : OrderedFinpartition n) : ℝ :=
  ∏ i : Fin c.length, D^(c.partSize i)

variable (D : ℝ) (hD : 0 ≤ D)
  (hJ : ∀ i, 1 ≤ i → i ≤ n →
    Continuous (fun z : K × Vector3 => iteratedFDeriv ℝ i (Y z.1) z.2))
  (hB : ∀ i, 1 ≤ i → i ≤ n → ∀ t x, ‖iteratedFDeriv ℝ i (Y t) x‖ ≤ D^i)

include hJ in
theorem partitionCoefficient_continuous (c : OrderedFinpartition n) :
    Continuous (Function.uncurry (partitionCoefficient Y c)) := by
  exact (c.compAlongOrderedFinpartitionL ℝ Vector3 Vector3 Vector3).flipMultilinear.cont.comp
    (continuous_pi (fun i => hJ (c.partSize i) (c.partSize_pos i) (c.partSize_le i)))

include hD hB in
theorem partitionCoefficient_bound (c : OrderedFinpartition n) (t : K) (x : Vector3) :
    ‖partitionCoefficient Y c t x‖ ≤ partitionBound D c := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Finset.prod_nonneg (fun i _ => pow_nonneg hD _))
  intro v
  rw [partitionCoefficient_apply]
  calc
    _ ≤ ‖v‖ * ∏ i, ‖iteratedFDeriv ℝ (c.partSize i) (Y t) x‖ :=
      c.norm_compAlongOrderedFinpartition_le _ _
    _ ≤ ‖v‖ * partitionBound D c := mul_le_mul_of_nonneg_left
      (Finset.prod_le_prod (fun _ _ => norm_nonneg _)
        (fun i _ => hB (c.partSize i) (c.partSize_pos i) (c.partSize_le i) t x)) (norm_nonneg _)
    _ = _ := mul_comm _ _

variable [FirstCountableTopology K]

def partitionPath (c : OrderedFinpartition n) :
    C(K,Lp (Tensor n) 2 (volume : Measure Vector3)) where
  toFun t := operator volume (partitionCoefficient Y c t)
    ((partitionCoefficient_continuous Y hJ c).uncurry_left t).aestronglyMeasurable
    (partitionBound D c) (partitionCoefficient_bound Y D hD hB c t) (pulledJetPath Y hmp u c.length
      t)
  continuous_toFun := operator_path_continuous volume (partitionBound D c) (partitionCoefficient Y
    c)
    (fun t => ((partitionCoefficient_continuous Y hJ c).uncurry_left t).aestronglyMeasurable)
    (fun _ => (partitionCoefficient_continuous Y hJ c).comp (continuous_id.prodMk continuous_const))
    (partitionCoefficient_bound Y D hD hB c) _ (pulledJetPath Y hmp u c.length).continuous

theorem partitionPath_ae (g : K → Vector3 → Vector3)
    (hu : ∀ i t, (u i t : Vector3 → Tensor i) =ᵐ[volume] iteratedFDeriv ℝ i (g t))
    (c : OrderedFinpartition n) (t : K) :
    (partitionPath Y hmp u D hD hJ hB c t : Vector3 → Tensor n) =ᵐ[volume]
      fun x => c.compAlongOrderedFinpartition (iteratedFDeriv ℝ c.length (g t) (Y t x))
        (fun i => iteratedFDeriv ℝ (c.partSize i) (Y t) x) := by
  have h := operator_ae volume (partitionCoefficient Y c t)
    ((partitionCoefficient_continuous Y hJ c).uncurry_left t).aestronglyMeasurable
    (partitionBound D c) (partitionCoefficient_bound Y D hD hB c t) (pulledJetPath Y hmp u c.length
      t)
  filter_upwards [h,pulledJetPath_ae Y hmp u g hu c.length t] with x hx hy
  exact hx.trans (by rw [hy,partitionCoefficient_apply])

def tensorPath : C(K,Lp (Tensor n) 2 (volume : Measure Vector3)) :=
  ∑ c : OrderedFinpartition n, partitionPath Y hmp u D hD hJ hB c

theorem tensorPath_ae (g : K → Vector3 → Vector3)
    (hg : ∀ t, ContDiff ℝ ∞ (g t)) (hY : ∀ t, ContDiff ℝ ∞ (Y t))
    (hu : ∀ i t, (u i t : Vector3 → Tensor i) =ᵐ[volume] iteratedFDeriv ℝ i (g t)) (t : K) :
    (tensorPath Y hmp u D hD hJ hB t : Vector3 → Tensor n) =ᵐ[volume]
      iteratedFDeriv ℝ n (g t ∘ Y t) := by
  have hterms : ∀ᵐ x ∂volume, ∀ c : OrderedFinpartition n,
      (partitionPath Y hmp u D hD hJ hB c t) x =
      c.compAlongOrderedFinpartition (iteratedFDeriv ℝ c.length (g t) (Y t x))
        (fun i => iteratedFDeriv ℝ (c.partSize i) (Y t) x) :=
    ae_all_iff.mpr (fun c => partitionPath_ae Y hmp u D hD hJ hB g hu c t)
  have hsum := Lp.coeFn_finsetSum Finset.univ (fun c : OrderedFinpartition n =>
    partitionPath Y hmp u D hD hJ hB c t)
  filter_upwards [hterms,hsum] with x hx hs
  simp only [tensorPath,ContinuousMap.sum_apply]
  rw [hs]
  simp only [Finset.sum_apply]
  rw [iteratedFDeriv_comp (i := n) ((hg t).contDiffAt.of_le (show (n : ℕ∞ω) ≤ ∞ by simp))
    ((hY t).contDiffAt.of_le (show (n : ℕ∞ω) ≤ ∞ by simp)) le_rfl]
  simp only [FormalMultilinearSeries.taylorComp,FormalMultilinearSeries.compAlongOrderedFinpartition,
    ftaylorSeries]
  exact Finset.sum_congr rfl (fun c _ => hx c)

end EulerVolumeSobolevPath
