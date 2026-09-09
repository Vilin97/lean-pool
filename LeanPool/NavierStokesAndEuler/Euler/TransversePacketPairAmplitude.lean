/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketHistory
import LeanPool.NavierStokesAndEuler.Euler.ElapsedTimePathWeight
import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevScaling
import LeanPool.NavierStokesAndEuler.Euler.TransversePacketHomogeneity
import LeanPool.NavierStokesAndEuler.Euler.TransversePacketPrimaryHomogeneity

/-! Homogeneity restores a common arbitrary envelope for genuine forcing
and initial data, without adding either envelope to the radius guards. -/

@[expose] public section


noncomputable section

namespace EulerTransversePacketProvider

open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace EulerLpCylinderTranslation
  EulerLpCylinderPaths EulerPacketProfileRecursion EulerContinuousTimeWeight
  EulerParameterWordGevrey EulerGevrey
open scoped ContDiff

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  {D : Data U} {ι : Type*} [Fintype ι]

theorem pair_amplitude_bound
    (S : ∀ {r : VectorField}, Forcing P D r → InitialData P D → C(Icc (0 : ℝ) D.T, LiftL2 P))
    (hs : ∀ {r} (G : Forcing P D r) (I : InitialData P D),
      ContDiff ℝ ∞ (fun a => pathTranslate P a (S G I)))
    (hm : ∀ {r r'} (G : Forcing P D r) (H : Forcing P D r') (I J : InitialData P D) (a : ℝ),
      H.path = a • G.path → J.value = a • I.value → S H J = a • S G I)
    (g : C(Icc (0 : ℝ) D.T, ℝ)) (hg : ∀ t, 0 < g t)
    (directions : ι → LiftTangent) (q : ℕ) (R C : ℝ) (d e : ℕ)
    (hunit : ∀ {r} (G : Forcing P D r) (I : InitialData P D),
      (∀ n, block directions q (fun a => pathTranslate P a
        (normalize g hg (HistoryData.forcingPath G))) n 0 ≤ majorant R d n) →
      (∀ n, block directions q (fun a => translate P a (I.value : CylinderL2 P U)) n 0 ≤ majorant R
          d n) →
      ∀ n, block directions q (fun a => pathTranslate P a (normalize g hg (S G I))) n 0 ≤
          C * majorant R e n)
    {r : VectorField} (G : Forcing P D r) (I : InitialData P D) (A : ℝ) (hA : 0 ≤ A)
    (hb : ∀ n, block directions q (fun a => pathTranslate P a
      (normalize g hg (HistoryData.forcingPath G))) n 0 ≤ A * majorant R d n)
    (hi : ∀ n, block directions q (fun a => translate P a (I.value : CylinderL2 P U)) n 0 ≤
        A * majorant R d n)
    (n : ℕ) :
    block directions q (fun a => pathTranslate P a (normalize g hg (S G I))) n 0 ≤
      (C*A)*majorant R e n := by
  by_cases hz : A = 0
  · have hf := value_zero_of_block_zero_bound directions q
      (fun a => pathTranslate P a (normalize g hg (HistoryData.forcingPath G))) 0
      (by simpa only [hz,zero_mul] using hb 0)
    have ht : pathTranslate P 0 (normalize g hg (HistoryData.forcingPath G)) =
        normalize g hg (HistoryData.forcingPath G) := by
      apply ContinuousMap.ext
      intro t
      exact translate_zero P _
    rw [ht] at hf
    have hfull : HistoryData.forcingPath G = 0 := by
      have he := congrArg (weight g) hf
      rw [weight_normalize,map_zero] at he
      exact he
    have hp : G.path = 0 := by
      have he := congrArg (projectPath P D.support D.support_measurable) hfull
      rw [project_include,map_zero] at he
      exact he
    have hinitial := value_zero_of_block_zero_bound directions q
      (fun a => translate P a (I.value : CylinderL2 P U)) 0
      (by simpa only [hz,zero_mul] using hi 0)
    rw [translate_zero] at hinitial
    have hv : I.value = 0 := Subtype.ext hinitial
    have hS : S G I = 0 := by
      have he := hm G G I I 0 (hp.trans (zero_smul ℝ G.path).symm)
        (hv.trans (zero_smul ℝ I.value).symm)
      simpa only [zero_smul] using he
    simp only [hS,map_zero,block_zero_function,hz,mul_zero,zero_mul,le_refl]
  · have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hz)
    let H := G.smul A⁻¹
    let J := I.smul A⁻¹
    have hinput : HistoryData.forcingPath H = A⁻¹ • HistoryData.forcingPath G := by
      change includePath P D.support D.support_measurable (A⁻¹ • G.path) = _
      rw [map_smul]
    have hH (j : ℕ) : block directions q (fun a => pathTranslate P a
        (normalize g hg (HistoryData.forcingPath H))) j 0 ≤ majorant R d j := by
      have he : (fun a => pathTranslate P a (normalize g hg (HistoryData.forcingPath H))) =
          fun a => A⁻¹ • pathTranslate P a (normalize g hg (HistoryData.forcingPath G)) := by
        funext a
        rw [hinput,map_smul,map_smul]
      rw [he]
      simpa only [one_mul] using block_normalize_bound directions q
        (fun a => pathTranslate P a (normalize g hg (HistoryData.forcingPath G)))
        (normalize_orbit_contDiff P g hg _ G.path_orbit) A hApos R 1 d j 0
        (by simpa only [one_mul] using hb j)
    have hJ (j : ℕ) : block directions q
        (fun a => translate P a (J.value : CylinderL2 P U)) j 0 ≤ majorant R d j := by
      have he : (fun a => translate P a (J.value : CylinderL2 P U)) =
          fun a => A⁻¹ • translate P a (I.value : CylinderL2 P U) := by
        funext a
        change translate P a (A⁻¹ • (I.value : CylinderL2 P U)) = _
        rw [map_smul]
      rw [he]
      simpa only [one_mul] using block_normalize_bound directions q
        (fun a => translate P a (I.value : CylinderL2 P U)) I.orbit A hApos R 1 d j 0
        (by simpa only [one_mul] using hi j)
    have hrestore : S G I = A • S H J := by
      rw [hm G H I J A⁻¹ rfl rfl,smul_smul,mul_inv_cancel₀ hz,one_smul]
    exact (block_restore_bound directions q
      (fun a => pathTranslate P a (normalize g hg (S H J)))
      (fun a => pathTranslate P a (normalize g hg (S G I)))
      (normalize_orbit_contDiff P g hg (S H J) (hs H J)) A hA
      (fun a => by rw [hrestore,map_smul,map_smul]) R C e n 0
      (hunit H J hH hJ n)).trans_eq (by ring)

end EulerTransversePacketProvider
