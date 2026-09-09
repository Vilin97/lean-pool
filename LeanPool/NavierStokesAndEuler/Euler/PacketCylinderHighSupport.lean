/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderPrefixLocality
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderJetOperations

/-!
# Support of the literal recursive high forcing

Exterior pure-mean interactions are angle-independent and are removed by the
actual angular mean. The remaining terms use only the already supported
prefix high fields, correctors and physical pressure gradients.
-/

@[expose] public section


noncomputable section

namespace EulerPacketCylinderField

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerPacketPointJets
    EulerPacketProfileRecursion

variable {P T : ℝ} [Fact (0 < P)]

theorem Field.timeDerivative_zero_outside {raw raw_t : VectorField}
    (G : Field P T raw) (H : Field P T raw_t) (hT : 0 < T)
    (hd : TimeDerivative hT.le G H) (S : Set Space)
    (hs : ∀ (t : Icc (0 : ℝ) T) x, x ∉ S → ∀ θ : ℝ, raw (t,(x,θ)) = 0)
    (t : Icc (0 : ℝ) T) (x : Space) (hx : x ∉ S) (θ : ℝ) :
    raw_t (t,(x,θ)) = 0 := by
  have h₁ := G.raw_hasDerivWithinAt hT.le H hd t x θ
  have h₂ : HasDerivWithinAt (fun r => raw (r,(x,θ))) (0 : Space) (Icc (0 : ℝ) T) t :=
    (hasDerivWithinAt_const (t : ℝ) (Icc (0 : ℝ) T) (0 : Space)).congr_of_mem
      (fun r hr => hs ⟨r,hr⟩ x hx θ) t.property
  exact (h₁.derivWithin ((uniqueDiffOn_Icc hT) _ t.property)).symm.trans
    (h₂.derivWithin ((uniqueDiffOn_Icc hT) _ t.property))

variable {O : Operators} {p : ℕ} {a : ℕ → Profile}

theorem PrefixFields.knownForce_angleIndependent (F : PrefixFields P T p a)
    (C : CoefficientData P T O) (hp : 1 ≤ p) (hT : 0 < T)
    {correctorT : VectorField} (Ct : Field P T correctorT)
    (hCt : TimeDerivative hT.le (F.corrector (p - 1) (Nat.sub_one_lt_of_lt hp)) Ct)
    (S : Set Space) (hS : IsClosed S) (L : PrefixLocality T p a S)
    (hpressure : ∀ (t : Icc (0 : ℝ) T) x, x ∉ S → ∀ θ : ℝ,
      pressureGradient (a (p-1)).highPressure (t,(x,θ)) = 0)
    (t : Icc (0 : ℝ) T) (x : Space) (hx : x ∉ S) (θ : ℝ) :
    EulerPacketProfileRecursion.knownForce O p a (t,(x,θ)) =
      EulerPacketProfileRecursion.knownForce O p a (t,(x,0)) := by
  have hlin (s : ℝ) : linearPart (O.strain (t,(x,s)))
      (slicedJet O.interval (a (p-1)).corrector (t,(x,s))) = 0 := by
    change (slicedJet O.interval (a (p-1)).corrector (t,(x,s))).2 timeDirection +
      O.strain (t,(x,s)) ((a (p-1)).corrector (t,(x,s))) = 0
    rw [C.interval_eq,(F.corrector (p-1) (by omega)).slicedJet_temporal hT Ct hCt]
    rw [(F.corrector (p-1) (by omega)).timeDerivative_zero_outside Ct hT hCt S
      (L.corrector_zero (p-1) (by omega)) t x hx s,L.corrector_zero (p-1) (by omega) t x hx s,
      map_zero,add_zero]
  have hpr (s : ℝ) : slowPressure (O.inverseFrame (t,(x,s)))
      (pressureJet (a (p-1)).highPressure (t,(x,s))) = 0 := by
    change (O.inverseFrame (t,(x,s))).adjoint
      (pressureGradient (a (p-1)).highPressure (t,(x,s))) = 0
    rw [hpressure t x hx s,map_zero]
  unfold EulerPacketProfileRecursion.knownForce
  rw [hlin θ,hlin 0,hpr θ,hpr 0,F.nonlinear_angleIndependent C hp S hS L t x hx θ]

theorem PrefixFields.highForce_zero_outside (F : PrefixFields P T p a)
    (C : CoefficientData P T O) (hp : 2 ≤ p) (hT : 0 < T)
    {correctorT : VectorField} (Ct : Field P T correctorT)
    (hCt : TimeDerivative hT.le (F.corrector (p - 1) (Nat.sub_one_lt_of_lt hp)) Ct)
    (S : Set Space) (hS : IsClosed S) (L : PrefixLocality T p a S)
    (hpressure : ∀ (t : Icc (0 : ℝ) T) x, x ∉ S → ∀ θ : ℝ,
      pressureGradient (a (p-1)).highPressure (t,(x,θ)) = 0)
    (t : Icc (0 : ℝ) T) (x : Space) (hx : x ∉ S) (θ : ℝ) :
    EulerPacketProfileRecursion.highForce O p a (t,(x,θ)) = 0 := by
  have hknown := F.knownForce_angleIndependent C (by omega) hT Ct hCt S hS L hpressure t x hx
  have hmean : EulerPacketProfileRecursion.meanForce O p a (t,(x,θ)) =
      EulerPacketProfileRecursion.knownForce O p a (t,(x,θ)) := by
    unfold EulerPacketProfileRecursion.meanForce EulerPacketProfileRecursion.angleMean
    rw [C.period_eq]
    have he : (fun s : ℝ => EulerPacketProfileRecursion.knownForce O p a (t,(x,s))) =
        fun _ : ℝ => EulerPacketProfileRecursion.knownForce O p a (t,(x,0)) := funext hknown
    rw [he,intervalIntegral.integral_const,sub_zero,smul_smul,
      inv_mul_cancel₀ (ne_of_gt (Fact.out : 0 < P)),one_smul,hknown θ]
  have hfast : fastAdvection (O.normal (t,(x,θ)))
      (slicedJet O.interval (meanResult O p a).1 (t,(x,θ)))
      (slicedJet O.interval (a 1).high (t,(x,θ))) = 0 := by
    change inner ℝ (O.normal (t,(x,θ))) ((meanResult O p a).1 (t,(x,θ))) •
      (slicedJet O.interval (a 1).high (t,(x,θ))).2 angleDirection = 0
    rw [slicedJet_angle,raw_fderiv_zero_outside S hS (L.high_zero 1 (by omega)) t x hx θ,
      zero_apply,smul_zero]
  change EulerPacketProfileRecursion.knownForce O p a (t,(x,θ)) -
    EulerPacketProfileRecursion.meanForce O p a (t,(x,θ)) - _ = 0
  rw [hmean,hfast,sub_self,sub_zero]

end EulerPacketCylinderField
