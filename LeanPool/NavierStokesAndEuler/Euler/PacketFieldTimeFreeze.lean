/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketProfileBudget
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderWeightedLinear
import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevLinear

/-! Time evaluation and constant extension preserve every genuine spatial
word bound. Restoring a time weight uses its value at that time, retaining
the source's initial alpha factor. -/

@[expose] public section


noncomputable section


open scoped ContDiff

namespace EulerContinuousTimeFreeze

variable {K E : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Freeze path, given by `(ContinuousLinearMap.const ℝ K).comp (ContinuousMap.evalCLM ℝ t)`. -/
def freezePath (t : K) : C(K,E) →L[ℝ] C(K,E) :=
  (ContinuousLinearMap.const ℝ K).comp (ContinuousMap.evalCLM ℝ t)

omit [CompactSpace K] in
@[simp] theorem freezePath_apply (t s : K) (p : C(K, E)) : freezePath t p s = p t := rfl

theorem freezePath_norm (t : K) : ‖freezePath (E := E) t‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro p
  rw [one_mul]
  apply (ContinuousMap.norm_le _ (norm_nonneg p)).2
  intro s
  exact p.norm_coe_le_norm t

end EulerContinuousTimeFreeze

namespace EulerPacketCylinderField.Field

open Set MeasureTheory EulerSmoothLimit EulerLiftedGradientSpace EulerLpCylinderTranslation
  EulerCylinderSmoothOrbit EulerCylinderSobolev EulerContinuousTimeFreeze EulerParameterWordGevrey
  EulerPacketProfileRecursion EulerContinuousTimeWeight

variable {P T : ℝ} [Fact (0 < P)] {raw : VectorField}

theorem freezePath_translate (t : Icc (0 : ℝ) T) (p : C(Icc (0 : ℝ) T, LiftL2 P))
    (a : LiftTangent) :
    pathTranslate P a (freezePath t p) = freezePath t (pathTranslate P a p) := by
  apply ContinuousMap.ext
  intro s
  rfl

/-- Freeze, constructed using `ofLifted`. -/
def freeze (G : Field P T raw) (t : Icc (0 : ℝ) T) :
    Field P T (fun z => raw (t,z.2)) :=
  ofLifted (freezePath t G.path)
    (by
      have he : (fun a : LiftTangent => pathTranslate P a (freezePath t G.path)) =
          freezePath t ∘ (fun a : LiftTangent => pathTranslate P a G.path) :=
        funext (freezePath_translate t G.path)
      rw [he]
      exact (freezePath t).contDiff.comp G.orbit)
    (fun _ => pointField P G.path G.orbit t)
    (fun _ => EulerMetricTransport.smoothField_continuous P _ (pointField_smooth P G.path G.orbit
        t))
    (fun _ => pointField_ae P G.path G.orbit t)
    (fun _ x θ => G.raw_eq t x θ)

@[simp] theorem freeze_path (G : Field P T raw) (t : Icc (0 : ℝ) T) :
    (G.freeze t).path = freezePath t G.path := rfl

theorem WordBound.freeze {G : Field P T raw} {q d : ℕ} {R A : ℝ}
    (hG : G.WordBound q R A d) (t : Icc (0 : ℝ) T) :
    (G.freeze t).WordBound q R A d := by
  intro n
  have he : (fun a : LiftTangent => pathTranslate P a (G.freeze t).path) =
      freezePath t ∘ (fun a : LiftTangent => pathTranslate P a G.path) :=
    funext (freezePath_translate t G.path)
  rw [he]
  have hb := block_comp_clm_le standardDirection q
    (freezePath (E := LiftL2 P) t)
    (fun a : LiftTangent => pathTranslate P a G.path) G.orbit n 0
  have hp : 0 ≤ block standardDirection q
      (fun a : LiftTangent => pathTranslate P a G.path) n 0 :=
    block_nonneg standardDirection q (fun a : LiftTangent => pathTranslate P a G.path) n 0
  have hn : ‖freezePath (E := LiftL2 P) t‖ ≤ 1 := freezePath_norm t
  have hm := mul_le_mul_of_nonneg_right hn hp
  rw [one_mul] at hm
  exact hb.trans (hm.trans (hG n))

theorem freeze_normalized_restore (G : Field P T raw) (hT : 0 ≤ T)
    (g : C(Icc (0 : ℝ) T, ℝ)) (hg : ∀ t, 0 < g t) (t : Icc (0 : ℝ) T) :
    (G.freeze t).path = (((G.normalized hT g hg).freeze t).smul (g t)).path := by
  apply ContinuousMap.ext
  intro s
  change G.path t = g t • ((g t)⁻¹ • G.path t)
  rw [smul_smul, mul_inv_cancel₀ (ne_of_gt (hg t)), one_smul]

theorem WordBound.freeze_normalized {G : Field P T raw} {q d : ℕ} {R A : ℝ}
    (hT : 0 ≤ T) (g : C(Icc (0 : ℝ) T, ℝ)) (hg : ∀ t, 0 < g t)
    (hG : (G.normalized hT g hg).WordBound q R A d) (t : Icc (0 : ℝ) T) :
    (G.freeze t).WordBound q R (g t*A) d := by
  have h := (hG.freeze t).smul (g t)
  rw [abs_of_pos (hg t)] at h
  exact h.of_path_eq (G.freeze t) (G.freeze_normalized_restore hT g hg t)

end EulerPacketCylinderField.Field

namespace EulerPacketCylinderField.ProfileBudget

open Set EulerPacketProfileRecursion EulerPacketTimeProfile EulerPacketShiftArithmetic

variable {P T : ℝ} [Fact (0 < P)] {hT : 0 ≤ T} {support : Set EulerSmoothLimit.Space}
  {a : Profile} {G : ProfileRegularity P T hT support a}
  {S : Scales (Icc (0 : ℝ) T)} {R : ℝ} {p : ℕ}

theorem high_freeze (hG : ProfileBudget G S R p) (t : Icc (0 : ℝ) T) :
    (G.high.freeze t).WordBound 6 R (S.high p t) (highShift p) := by
  simpa only [mul_one] using hG.high.freeze_normalized hT (S.high p) (S.high_pos p) t

theorem corrector_freeze (hG : ProfileBudget G S R p) (t : Icc (0 : ℝ) T) :
    (G.corrector.freeze t).WordBound 6 R (S.high p t) (highShift p) := by
  simpa only [mul_one] using hG.corrector.freeze_normalized hT (S.high p) (S.high_pos p) t

theorem mean_freeze (hG : ProfileBudget G S R p) (t : Icc (0 : ℝ) T) :
    (G.mean.freeze t).WordBound 6 R (S.mean p t) (meanShift p) := by
  simpa only [mul_one] using hG.mean.freeze_normalized hT (S.mean p) (S.mean_pos p) t

end EulerPacketCylinderField.ProfileBudget
