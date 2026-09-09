/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderJetOperations
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderJetParity
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderKnownJets
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderTimeParity

/-! The literal recursive force preserves joint odd parity from its actual prefix data. -/

@[expose] public section


noncomputable section

namespace EulerPacketCylinderField

open Set Finset EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion EulerFiniteGrades

/-- Prefix odd data, collecting `high`, `mean`, `corrector`. -/
structure PrefixOdd (T : ℝ) (p : ℕ) (a : ℕ → Profile) : Prop where
  high : ∀ i, i < p → JointOdd T (a i).high
  mean : ∀ i, i < p → JointOdd T (a i).mean
  corrector : ∀ i, i < p → JointOdd T (a i).corrector

theorem JointOdd.convolution {T : ℝ} (M n : ℕ) (f : ℕ → ℕ → VectorField)
    (hf : ∀ i j, JointOdd T (f i j)) :
    JointOdd T (fun z => ∑ i ∈ range (M+1), ∑ j ∈ range (M+1),
      if i+j=n then f i j z else 0) := by
  intro t x θ
  rw [← sum_neg_distrib]
  apply sum_congr rfl
  intro i _
  rw [← sum_neg_distrib]
  apply sum_congr rfl
  intro j _
  by_cases h : i+j=n
  · simp only [h,ite_true,hf i j t x θ]
  · simp only [h,ite_false,neg_zero]

variable {P T : ℝ} [Fact (0 < P)] {O : Operators} {p : ℕ} {a : ℕ → Profile}

theorem PrefixOdd.knownJet_value_odd (H : PrefixOdd T p a) (hp : 1 ≤ p) (i : ℕ) :
    JointOdd T (fun z => (knownJets O p a z i).1) := by
  intro t x θ
  by_cases hi : i < p
  · by_cases hz : i = 0
    · subst i
      simp [knownJets,history,velocityJet,show (0 : ℕ) < p by omega]
    · simp only [knownJets,history,hi,ite_true,velocityJet,hz,ite_false]
      change (a i).high (t,(-x,-θ)) + (a i).mean (t,(-x,-θ)) +
        (a (i-1)).corrector (t,(-x,-θ)) =
          -((a i).high (t,(x,θ)) + (a i).mean (t,(x,θ)) + (a (i-1)).corrector (t,(x,θ)))
      rw [H.high i hi,H.mean i hi,H.corrector (i-1) (by omega),neg_add,neg_add]
  · by_cases he : i = p
    · subst i
      simpa [knownJets,history,slicedJet] using H.corrector (p-1) (by omega) t x θ
    · simp only [knownJets,history,hi,ite_false,he,Prod.fst_zero,neg_zero]

theorem PrefixFields.nonlinear_odd (F : PrefixFields P T p a) (H : PrefixOdd T p a)
    (hp : 1 ≤ p)
    (hI : ∀ (t : Icc (0 : ℝ) T) x θ, O.inverseFrame (t, (-x, -θ)) = O.inverseFrame (t, (x, θ)))
    (hN : ∀ (t : Icc (0 : ℝ) T) x θ, O.normal (t, (-x, -θ)) = O.normal (t, (x, θ))) :
    JointOdd T (fun z => nonlinearGrade (p+1) p (O.inverseFrame z) (O.normal z) (knownJets O p a
        z)) := by
  have hs (i j : ℕ) := (F.knownJet O hp j).slowAdvection_odd O.inverseFrame hI
    (H.knownJet_value_odd (O := O) hp i) (H.knownJet_value_odd (O := O) hp j)
  have ha (i j : ℕ) := (F.knownJet O hp j).fastAdvection_odd O.normal hN
    (H.knownJet_value_odd (O := O) hp i) (H.knownJet_value_odd (O := O) hp j)
  exact (JointOdd.convolution (p+1) p _ hs).add (JointOdd.convolution (p+1) (p+1) _ ha)

theorem PrefixFields.knownForce_odd (F : PrefixFields P T p a) (H : PrefixOdd T p a)
    (C : CoefficientData P T O) (hp : 1 ≤ p) (hT : 0 < T)
    {correctorT : VectorField} (Ct : Field P T correctorT)
    (hCt : TimeDerivative hT.le (F.corrector (p - 1) (Nat.sub_one_lt_of_lt hp)) Ct)
    (hpressure : JointOdd T (pressureGradient (a (p - 1)).highPressure))
    (hI : ∀ (t : Icc (0 : ℝ) T) x θ, O.inverseFrame (t, (-x, -θ)) = O.inverseFrame (t, (x, θ)))
    (hM : ∀ (t : Icc (0 : ℝ) T) x θ, O.strain (t, (-x, -θ)) = O.strain (t, (x, θ)))
    (hN : ∀ (t : Icc (0 : ℝ) T) x θ, O.normal (t, (-x, -θ)) = O.normal (t, (x, θ))) :
    JointOdd T (EulerPacketProfileRecursion.knownForce O p a) := by
  have hC := H.corrector (p-1) (by omega)
  have ht : JointOdd T correctorT :=
    (F.corrector (p-1) (by omega)).timeDerivative_odd Ct hT hCt hC
  have hL : JointOdd T (fun z => linearPart (O.strain z) (slicedJet O.interval (a (p-1)).corrector
      z)) := by
    intro t x θ
    change (slicedJet O.interval (a (p-1)).corrector (t,(-x,-θ))).2 timeDirection +
      O.strain (t,(-x,-θ)) ((a (p-1)).corrector (t,(-x,-θ))) =
        -((slicedJet O.interval (a (p-1)).corrector (t,(x,θ))).2 timeDirection +
          O.strain (t,(x,θ)) ((a (p-1)).corrector (t,(x,θ))))
    simp only [C.interval_eq,(F.corrector (p-1) (by omega)).slicedJet_temporal hT Ct hCt,
      ht t x θ,hM t x θ,hC t x θ,map_neg,neg_add]
  have hQ : JointOdd T (fun z => slowPressure (O.inverseFrame z) (pressureJet (a
      (p-1)).highPressure z)) := by
    intro t x θ
    change (O.inverseFrame (t,(-x,-θ))).adjoint (pressureGradient (a (p-1)).highPressure
        (t,(-x,-θ))) =
      -((O.inverseFrame (t,(x,θ))).adjoint (pressureGradient (a (p-1)).highPressure (t,(x,θ))))
    rw [hI,hpressure,map_neg]
  exact ((hL.add hQ).add (F.nonlinear_odd H hp hI hN)).neg

end EulerPacketCylinderField
