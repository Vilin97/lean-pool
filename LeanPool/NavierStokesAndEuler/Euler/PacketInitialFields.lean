/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.PacketFiniteFieldAlgebra
public import LeanPool.NavierStokesAndEuler.Euler.PacketRecursiveCancellation
public import LeanPool.NavierStokesAndEuler.Euler.PacketProfileBudget
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderWeightedLinear
import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevLinear

/-! The literal initial packet is the sum of its oscillating high part
and its angle-independent mean part. Every field below is realized by
the already constructed continuous cylinder L² paths. -/

section

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

end
end

end

@[expose] public section

noncomputable section

namespace EulerPacketInitial

open Set Finset EulerSmoothLimit EulerPacketProfileRecursion EulerPacketPointJets
  EulerPacketCylinderField EulerFiniteGrades

/-- Time slice, defined pointwise by `f (t,z.2)`. -/
def timeSlice (t : ℝ) (f : VectorField) : VectorField := fun z => f (t,z.2)

/-- High grade, given by `assemble N (fun i => timeSlice t (a i).high) (fun i => timeSlice t (a
i).corrector)`. -/
def highGrade (N : ℕ) (t : ℝ) (a : ℕ → Profile) : ℕ → VectorField :=
  assemble N (fun i => timeSlice t (a i).high) (fun i => timeSlice t (a i).corrector)

/-- Mean grade, given by `truncate N (fun i => timeSlice t (a i).mean)`. -/
def meanGrade (N : ℕ) (t : ℝ) (a : ℕ → Profile) : ℕ → VectorField :=
  truncate N (fun i => timeSlice t (a i).mean)

/-- High, given by `fieldSum (N+1) κ (highGrade N t a)`. -/
def high (N : ℕ) (κ t : ℝ) (a : ℕ → Profile) : VectorField :=
  fieldSum (N+1) κ (highGrade N t a)

/-- Mean, given by `fieldSum (N+1) κ (meanGrade N t a)`. -/
def mean (N : ℕ) (κ t : ℝ) (a : ℕ → Profile) : VectorField :=
  fieldSum (N+1) κ (meanGrade N t a)

theorem high_eq (N : ℕ) (κ t : ℝ) (a : ℕ → Profile) :
    high N κ t a = fieldSum N κ (fun i => timeSlice t (a i).high) +
      κ • fieldSum N κ (fun i => timeSlice t (a i).corrector) := by
  funext z
  have h := congrFun (evaluate_assemble N κ (fun i => timeSlice t (a i).high)
    (fun i => timeSlice t (a i).corrector)) z
  simpa only [high,highGrade,fieldSum,evaluate,Finset.sum_apply,Pi.smul_apply,Pi.add_apply] using h

theorem mean_eq (N : ℕ) (κ t : ℝ) (a : ℕ → Profile) :
    mean N κ t a = fieldSum N κ (fun i => timeSlice t (a i).mean) := by
  funext z
  have h := congrFun (evaluate_truncate_extend N (N+1) (by omega) κ
    (fun i => timeSlice t (a i).mean)) z
  simpa only [mean,meanGrade,fieldSum,evaluate,Finset.sum_apply,Pi.smul_apply] using h

theorem packet_split (N : ℕ) (κ t : ℝ) (a : ℕ → Profile) :
    timeSlice t (fieldSum (N+1) κ (assembledVelocity N a)) =
      high N κ t a + mean N κ t a := by
  rw [high_eq,mean_eq]
  funext z
  have he := congrFun (evaluate_assemble N κ (fun i => (a i).high+(a i).mean)
    (fun i => (a i).corrector)) (t,z.2)
  simpa only [timeSlice,fieldSum,evaluate,assembledVelocity,Finset.sum_apply,Pi.add_apply,
    Pi.smul_apply,smul_add,sum_add_distrib,add_assoc,add_comm,add_left_comm] using he

variable {P T : ℝ} [Fact (0 < P)] {hT : 0 ≤ T} {N : ℕ}
  {a : ℕ → Profile} {support : Set Space}

/-- High grade field, given by `Field.assembleFamily N _ _ (fun i hi => (G i hi).high.freeze t)
(fun i hi => (G i hi).corrector.freeze t) n`. -/
def highGradeField (G : ∀ i, i ≤ N → ProfileRegularity P T hT support (a i))
    (t : Icc (0 : ℝ) T) (n : ℕ) : Field P T (highGrade N t a n) :=
  Field.assembleFamily N _ _ (fun i hi => (G i hi).high.freeze t)
    (fun i hi => (G i hi).corrector.freeze t) n

/-- Mean grade field, given by `Field.truncateFamily N _ (fun i hi => (G i hi).mean.freeze t)
n`. -/
def meanGradeField (G : ∀ i, i ≤ N → ProfileRegularity P T hT support (a i))
    (t : Icc (0 : ℝ) T) (n : ℕ) : Field P T (meanGrade N t a n) :=
  Field.truncateFamily N _ (fun i hi => (G i hi).mean.freeze t) n

/-- High field, given by `Field.evaluateFamily (N+1) κ _ (highGradeField G t)`. -/
def highField (G : ∀ i, i ≤ N → ProfileRegularity P T hT support (a i))
    (t : Icc (0 : ℝ) T) (κ : ℝ) : Field P T (high N κ t a) :=
  Field.evaluateFamily (N+1) κ _ (highGradeField G t)

/-- Mean field, given by `Field.evaluateFamily (N+1) κ _ (meanGradeField G t)`. -/
def meanField (G : ∀ i, i ≤ N → ProfileRegularity P T hT support (a i))
    (t : Icc (0 : ℝ) T) (κ : ℝ) : Field P T (mean N κ t a) :=
  Field.evaluateFamily (N+1) κ _ (meanGradeField G t)

theorem high_zero_outside (G : ∀ i, i ≤ N → ProfileRegularity P T hT support (a i))
    (t : Icc (0 : ℝ) T) (κ s : ℝ) (x : Space) (hx : x ∉ support) (θ : ℝ) :
    high N κ t a (s,(x,θ)) = 0 := by
  rw [high_eq]
  change (∑ i ∈ range (N+1), κ^i • (a i).high (t,(x,θ))) +
    κ • (∑ i ∈ range (N+1), κ^i • (a i).corrector (t,(x,θ))) = 0
  have hh : (∑ i ∈ range (N+1), κ^i • (a i).high (t,(x,θ))) = 0 := by
    apply sum_eq_zero
    intro i hi
    rw [(G i (by have := mem_range.mp hi; omega)).high_zero t x hx θ,smul_zero]
  have hc : (∑ i ∈ range (N+1), κ^i • (a i).corrector (t,(x,θ))) = 0 := by
    apply sum_eq_zero
    intro i hi
    rw [(G i (by have := mem_range.mp hi; omega)).corrector_zero t x hx θ,smul_zero]
  rw [hh,hc,smul_zero,add_zero]

theorem mean_angle (G : ∀ i, i ≤ N → ProfileRegularity P T hT support (a i))
    (t : Icc (0 : ℝ) T) (κ s : ℝ) (x : Space) (θ : ℝ) :
    mean N κ t a (s,(x,θ)) = mean N κ t a (s,(x,0)) := by
  rw [mean_eq]
  change (∑ i ∈ range (N+1), κ^i • (a i).mean (t,(x,θ))) =
    ∑ i ∈ range (N+1), κ^i • (a i).mean (t,(x,0))
  apply sum_congr rfl
  intro i hi
  rw [(G i (by have := mem_range.mp hi; omega)).mean_angle t x θ]

theorem mean_zero_outside (t : ℝ) (κ s : ℝ) (a : ℕ → Profile)
    (K : Set Space)
    (hmean : ∀ i, i ≤ N → ∀ x, x ∉ K → ∀ θ, (a i).mean (t, (x, θ)) = 0)
    (x : Space) (hx : x ∉ K) (θ : ℝ) :
    mean N κ t a (s,(x,θ)) = 0 := by
  rw [mean_eq]
  change (∑ i ∈ range (N+1), κ^i • (a i).mean (t,(x,θ))) = 0
  apply sum_eq_zero
  intro i hi
  rw [hmean i (by have := mem_range.mp hi; omega) x hx θ,smul_zero]

end EulerPacketInitial
