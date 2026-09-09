/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketPrimaryHomogeneity
public import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevScaling
public import LeanPool.NavierStokesAndEuler.Euler.ElapsedTimePathWeight

@[expose] public section

/-! Unit-data estimates extend to arbitrary actual terminal amplitudes at the same radius. -/

noncomputable section

namespace EulerTransversePacketProvider

open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace EulerLpCylinderTranslation
  EulerLpCylinderPaths EulerContinuousTimeWeight EulerParameterWordGevrey EulerGevrey
open scoped ContDiff

variable {P : ℝ} [Fact (0 < P)]
  {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {D : Data U} {ι : Type*} [Fintype ι]

theorem initial_amplitude_bound
    (S : InitialData P D → C(Icc (0 : ℝ) D.T,CylinderL2 P V))
    (hs : ∀ Y, ContDiff ℝ ∞ (fun a => pathTranslate P a (S Y)))
    (hm : ∀ Y Z (a : ℝ), Z.value = a • Y.value → S Z = a • S Y)
    (g : C(Icc (0 : ℝ) D.T,ℝ)) (hg : ∀ t, 0 < g t)
    (directions : ι → LiftTangent) (q : ℕ) (R C : ℝ) (d e : ℕ)
    (hunit : ∀ Y : InitialData P D,
      (∀ n, block directions q (fun a => translate P a (Y.value : CylinderL2 P U)) n 0 ≤ majorant R
        d n) →
      ∀ n, block directions q (fun a => pathTranslate P a (normalize g hg (S Y))) n 0 ≤ C*majorant
        R e n)
    (Y : InitialData P D) (A : ℝ) (hA : 0 ≤ A)
    (hb : ∀ n, block directions q (fun a => translate P a (Y.value : CylinderL2 P U)) n 0 ≤
      A*majorant R d n)
    (n : ℕ) :
    block directions q (fun a => pathTranslate P a (normalize g hg (S Y))) n 0 ≤
      (C*A)*majorant R e n := by
  by_cases hz : A = 0
  · have hv := value_zero_of_block_zero_bound directions q
      (fun a => translate P a (Y.value : CylinderL2 P U)) 0
      (by simpa only [hz,zero_mul] using hb 0)
    rw [translate_zero] at hv
    have hy : Y.value = 0 := Subtype.ext hv
    have hS : S Y = 0 := by
      have he := hm Y Y 0 (hy.trans (zero_smul ℝ Y.value).symm)
      simpa only [zero_smul] using he
    simp only [hS,map_zero,block_zero_function,hz,mul_zero,zero_mul,le_refl]
  · have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hz)
    let Z := Y.smul A⁻¹
    have hZ (j : ℕ) : block directions q
        (fun a => translate P a (Z.value : CylinderL2 P U)) j 0 ≤ majorant R d j := by
      have he : (fun a => translate P a (Z.value : CylinderL2 P U)) =
          fun a => A⁻¹ • translate P a (Y.value : CylinderL2 P U) := by
        funext a
        exact (translate P a).map_smul A⁻¹ (Y.value : CylinderL2 P U)
      rw [he]
      simpa only [one_mul] using block_normalize_bound directions q
        (fun a => translate P a (Y.value : CylinderL2 P U)) Y.orbit
        A hApos R 1 d j 0 (by simpa only [one_mul] using hb j)
    have hrestore : S Y = A • S Z := by
      rw [hm Y Z A⁻¹ rfl,smul_smul,mul_inv_cancel₀ hz,one_smul]
    have hsZ : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a (normalize g hg (S Z))) := by
      have he : (fun a : LiftTangent => pathTranslate P a (normalize g hg (S Z))) =
          fun a => normalize g hg (pathTranslate P a (S Z)) := by
        funext a
        apply ContinuousMap.ext
        intro t
        exact (translate P a).map_smul (g t)⁻¹ (S Z t)
      rw [he]
      exact (normalize (E := CylinderL2 P V) g hg).contDiff.comp (hs Z)
    have hr := block_restore_bound directions q
      (fun a => pathTranslate P a (normalize g hg (S Z)))
      (fun a => pathTranslate P a (normalize g hg (S Y)))
      hsZ A hA
      (fun a => by rw [hrestore,map_smul,map_smul]) R C e n 0 (hunit Z hZ n)
    exact hr.trans_eq (by ring)

end EulerTransversePacketProvider
