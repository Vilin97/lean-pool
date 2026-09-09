/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketHomogeneity
public import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevScaling
public import LeanPool.NavierStokesAndEuler.Euler.ElapsedTimePathWeight

@[expose] public section

/-! Restoring arbitrary forcing amplitudes by actual scalar homogeneity. -/

noncomputable section

namespace EulerTransversePacketProvider

open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace EulerLpCylinderTranslation
  EulerLpCylinderPaths EulerPacketProfileRecursion EulerContinuousTimeWeight
  EulerParameterWordGevrey EulerGevrey
open scoped ContDiff

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  {D : Data U} {ι : Type*} [Fintype ι]

/-- A genuine homogeneous operator's unit-amplitude bound extends to every
nonnegative amplitude without changing its radius or its derivative shifts. -/
theorem amplitude_bound
    (S : ∀ {r : VectorField}, Forcing P D r → C(Icc (0 : ℝ) D.T,LiftL2 P))
    (hs : ∀ {r} (G : Forcing P D r), ContDiff ℝ ∞ (fun a => pathTranslate P a (S G)))
    (hm : ∀ {r r'} (G : Forcing P D r) (H : Forcing P D r') (a : ℝ),
      H.path = a • G.path → S H = a • S G)
    (g : C(Icc (0 : ℝ) D.T,ℝ)) (hg : ∀ t, 0 < g t)
    (directions : ι → LiftTangent) (q : ℕ) (R C : ℝ) (d e : ℕ)
    (hunit : ∀ {r} (G : Forcing P D r),
      (∀ n, block directions q (fun a => pathTranslate P a
        (normalize g hg (HistoryData.forcingPath G))) n 0 ≤ majorant R d n) →
      ∀ n, block directions q (fun a => pathTranslate P a (normalize g hg (S G))) n 0 ≤ C*majorant
        R e n)
    {r : VectorField} (G : Forcing P D r) (A : ℝ) (hA : 0 ≤ A)
    (hb : ∀ n, block directions q (fun a => pathTranslate P a
      (normalize g hg (HistoryData.forcingPath G))) n 0 ≤ A*majorant R d n)
    (n : ℕ) :
    block directions q (fun a => pathTranslate P a (normalize g hg (S G))) n 0 ≤
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
    have hS : S G = 0 := by
      have he := hm G G 0 (hp.trans (zero_smul ℝ G.path).symm)
      simpa only [zero_smul] using he
    simp only [hS,map_zero,block_zero_function,hz,mul_zero,zero_mul,le_refl]
  · have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hz)
    let H := G.smul A⁻¹
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
    have hrestore : S G = A • S H := by
      rw [hm G H A⁻¹ rfl,smul_smul,mul_inv_cancel₀ hz,one_smul]
    have hresult := block_restore_bound directions q
      (fun a => pathTranslate P a (normalize g hg (S H)))
      (fun a => pathTranslate P a (normalize g hg (S G)))
      (normalize_orbit_contDiff P g hg (S H) (hs H)) A hA
      (fun a => by rw [hrestore,map_smul,map_smul]) R C e n 0 (hunit H hH n)
    exact hresult.trans_eq (by ring)

end EulerTransversePacketProvider
