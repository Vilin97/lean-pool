/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.VolumeSobolevPath

@[expose] public section

/-! Actual all-order field towers retain their spatial Sobolev regularity
after a smooth volume-preserving change of coordinates. -/

noncomputable section

namespace EulerVolumeSobolevPath

open MeasureTheory EulerVolumeSobolevComposition EulerMetricTransport EulerLiftedGradientSpace
open scoped ContDiff

variable {K : Type*} [TopologicalSpace K] [FirstCountableTopology K]
  (Y : C(K,C(Vector3,Vector3))) (hmp : ∀ t, MeasurePreserving (Y t) volume volume)
  (u : ∀ i : ℕ, C(K,Lp (Tensor i) 2 (volume : Measure Vector3))) {n : ℕ}
  (D : ℝ) (hD : 0 ≤ D)
  (hJ : ∀ i, 1 ≤ i → i ≤ n →
    Continuous (fun z : K × Vector3 => iteratedFDeriv ℝ i (Y z.1) z.2))
  (hB : ∀ i, 1 ≤ i → i ≤ n → ∀ t x, ‖iteratedFDeriv ℝ i (Y t) x‖ ≤ D^i)

theorem tensorPath_norm_le (g : K → Vector3 → Vector3)
    (hg : ∀ t, ContDiff ℝ ∞ (g t)) (hY : ∀ t, ContDiff ℝ ∞ (Y t))
    (hu : ∀ i t, (u i t : Vector3 → Tensor i) =ᵐ[volume] iteratedFDeriv ℝ i (g t)) (t : K) :
    ‖tensorPath Y hmp u D hD hJ hB t‖ ≤
      ((n.factorial : ℝ)*D^n)*∑ i : Fin (n+1), ‖u i.val t‖ := by
  have hLp : ∀ i, i ≤ n → MemLp (iteratedFDeriv ℝ i (g t)) 2 volume :=
    fun i _ => (memLp_congr_ae (hu i t)).mp (Lp.memLp (u i t))
  let V := compositionTensorLp (Y t) (g t) (hY t) (hg t) n D hD
    (fun i h1 hi => hB i h1 hi t) (hmp t) hLp
  have he : tensorPath Y hmp u D hD hJ hB t = V := by
    apply Lp.ext
    exact (tensorPath_ae Y hmp u D hD hJ hB g hg hY hu t).trans
      (compositionTensor_memLp (Y t) (g t) (hY t) (hg t) n D hD
        (fun i h1 hi => hB i h1 hi t) (hmp t) hLp).coeFn_toLp.symm
  rw [he]
  calc
    ‖V‖ ≤ ((n.factorial : ℝ)*D^n)*∑ i : Fin (n+1),
        (eLpNorm (iteratedFDeriv ℝ i.val (g t)) 2 volume).toReal :=
      compositionTensorLp_norm_le (Y t) (g t) (hY t) (hg t) n D hD
        (fun i h1 hi => hB i h1 hi t) (hmp t) hLp
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [Lp.norm_def,eLpNorm_congr_ae (hu i.val t)]

end EulerVolumeSobolevPath

namespace EulerAllOrderCorrectionData.FieldTower

open Set MeasureTheory EulerMetricTransport EulerCylinderPhysicalTensor EulerCylinderSobolevSpace
  EulerLiftedGradientSpace
open scoped ContDiff

variable {P T : ℝ} [Fact (0 < P)] (A : EulerAllOrderCorrectionData.FieldTower P T)
  (k : ℝ) (m : Vector3)
  (Y : C(Icc (0 : ℝ) T,C(Vector3,Vector3)))
  (hmp : ∀ t, MeasurePreserving (Y t) volume volume)
  (n : ℕ) (D : ℝ) (hD : 0 ≤ D)
  (hJ : ∀ i, 1 ≤ i → i ≤ n →
    Continuous (fun z : Icc (0 : ℝ) T × Vector3 => iteratedFDeriv ℝ i (Y z.1) z.2))
  (hB : ∀ i, 1 ≤ i → i ≤ n → ∀ t x, ‖iteratedFDeriv ℝ i (Y t) x‖ ≤ D^i)

def volumePointField (t : Icc (0 : ℝ) T) : Vector3 → Vector3 :=
  A.physicalPointField k m t ∘ Y t

def volumeTensorPath : C(Icc (0 : ℝ) T,
    Lp (Vector3 [×n]→L[ℝ] Vector3) 2 (volume : Measure Vector3)) :=
  EulerVolumeSobolevPath.tensorPath Y hmp (fun i => A.physicalTensorPath k m i) D hD hJ hB

theorem volumePointField_smooth (hY : ∀ t, ContDiff ℝ ∞ (Y t)) (t : Icc (0 : ℝ) T) :
    ContDiff ℝ ∞ (A.volumePointField k m Y t) :=
  (A.physicalPointField_smooth k m t).comp (hY t)

theorem volumeTensorPath_ae (hY : ∀ t, ContDiff ℝ ∞ (Y t)) (t : Icc (0 : ℝ) T) :
    (A.volumeTensorPath k m Y hmp n D hD hJ hB t : Vector3 → (Vector3 [×n]→L[ℝ] Vector3)) =ᵐ[volume]
      iteratedFDeriv ℝ n (A.volumePointField k m Y t) :=
  EulerVolumeSobolevPath.tensorPath_ae Y hmp (fun i => A.physicalTensorPath k m i) D hD hJ hB
    (A.physicalPointField k m) (A.physicalPointField_smooth k m) hY
    (A.physicalTensorPath_ae k m) t

theorem volumeTensorPath_norm_le (hY : ∀ t, ContDiff ℝ ∞ (Y t)) (t : Icc (0 : ℝ) T) :
    ‖A.volumeTensorPath k m Y hmp n D hD hJ hB t‖ ≤
      ((n.factorial : ℝ)*D^n)*∑ i : Fin (n+1),
        frequencyFactor k m^i.val*(4 : ℝ)^i.val*Real.sqrt (2/P+2*P)*‖A.realization (i.val+1) t‖ :=
          by
  have h := EulerVolumeSobolevPath.tensorPath_norm_le Y hmp (fun i => A.physicalTensorPath k m i)
    D hD hJ hB (A.physicalPointField k m) (A.physicalPointField_smooth k m) hY
    (A.physicalTensorPath_ae k m) t
  exact h.trans (mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (fun i _ => A.physicalTensorValue_norm_le k m i.val t)) (by positivity))

end EulerAllOrderCorrectionData.FieldTower
