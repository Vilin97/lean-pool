/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderSpatialInvariance
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderCoefficientData

@[expose] public section

/-! Compact high profiles and angle-independent means make the exterior nonlinear forcing constant
  in angle. -/

noncomputable section

namespace EulerPacketCylinderField

open Set Finset EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion EulerFiniteGrades

structure PrefixLocality (T : ℝ) (p : ℕ) (a : ℕ → Profile) (S : Set Space) : Prop where
  high_zero : ∀ i, i < p → ∀ (t : Icc (0 : ℝ) T) x, x ∉ S → ∀ θ : ℝ,
    (a i).high (t,(x,θ)) = 0
  corrector_zero : ∀ i, i < p → ∀ (t : Icc (0 : ℝ) T) x, x ∉ S → ∀ θ : ℝ,
    (a i).corrector (t,(x,θ)) = 0
  mean_angle : ∀ i, i < p → ∀ (t : Icc (0 : ℝ) T) x θ,
    (a i).mean (t,(x,θ)) = (a i).mean (t,(x,0))

variable {P T : ℝ} [Fact (0 < P)] {O : Operators} {p : ℕ} {a : ℕ → Profile}

theorem PrefixFields.knownJet_angleIndependent (F : PrefixFields P T p a) (O : Operators)
    (hp : 1 ≤ p) (S : Set Space) (hS : IsClosed S) (L : PrefixLocality T p a S)
    (t : Icc (0 : ℝ) T) (x : Space) (hx : x ∉ S) (i : ℕ) :
    AngleIndependentJet (fun θ => knownJets O p a (t,(x,θ)) i) := by
  classical
  by_cases hi : i < p
  · by_cases hz : i = 0
    · subst i
      simpa only [knownJets,history,hi,ite_true,velocityJet] using AngleIndependentJet.zero
    · have ha := slicedJet_angleIndependent_of_support O.interval S hS (L.high_zero i hi) t x hx
      have hb := (F.mean i hi).slicedJet_angleIndependent O.interval (L.mean_angle i hi) t x
      have hc := slicedJet_angleIndependent_of_support O.interval S hS
        (L.corrector_zero (i-1) (by omega)) t x hx
      simpa only [knownJets,history,hi,ite_true,velocityJet,hz,ite_false] using (ha.add hb).add hc
  · by_cases he : i = p
    · subst i
      simpa only [knownJets,history,hi,ite_false,ite_true] using
        slicedJet_angleIndependent_of_support O.interval S hS
          (L.corrector_zero (p-1) (by omega)) t x hx
    · simpa only [knownJets,history,hi,ite_false,he] using AngleIndependentJet.zero

theorem AngleIndependentJet.slowAdvection {J K : ℝ → VectorJet}
    (hJ : AngleIndependentJet J) (hK : AngleIndependentJet K)
    (A : ℝ → Space →L[ℝ] Space) (hA : ∀ θ, A θ = A 0) (θ : ℝ) :
    EulerPacketPointJets.slowAdvection (A θ) (J θ) (K θ) =
      EulerPacketPointJets.slowAdvection (A 0) (J 0) (K 0) := by
  change (K θ).2 (spatialInjection (A θ (J θ).1)) = (K 0).2 (spatialInjection (A 0 (J 0).1))
  rw [hA θ,hJ.value θ,hK.spatial θ]

theorem AngleIndependentJet.fastAdvection_zero {K : ℝ → VectorJet}
    (hK : AngleIndependentJet K) (m : Space) (J : VectorJet) (θ : ℝ) :
    EulerPacketPointJets.fastAdvection m J (K θ) = 0 := by
  change inner ℝ m J.1 • (K θ).2 angleDirection = 0
  rw [hK.angular θ,smul_zero]

theorem PrefixFields.nonlinear_angleIndependent (F : PrefixFields P T p a)
    (C : CoefficientData P T O) (hp : 1 ≤ p) (S : Set Space) (hS : IsClosed S)
    (L : PrefixLocality T p a S) (t : Icc (0 : ℝ) T) (x : Space) (hx : x ∉ S) (θ : ℝ) :
    nonlinearGrade (p+1) p (O.inverseFrame (t,(x,θ))) (O.normal (t,(x,θ)))
        (knownJets O p a (t,(x,θ))) =
      nonlinearGrade (p+1) p (O.inverseFrame (t,(x,0))) (O.normal (t,(x,0)))
        (knownJets O p a (t,(x,0))) := by
  have hJ := F.knownJet_angleIndependent O hp S hS L t x hx
  have hA : ∀ θ, O.inverseFrame (t,(x,θ)) = O.inverseFrame (t,(x,0)) := by
    intro s
    rw [C.inverse.raw_eq,C.inverse.raw_eq]
  have hs (i j : ℕ) := (hJ i).slowAdvection (hJ j) (fun s => O.inverseFrame (t,(x,s))) hA θ
  have hf (i j : ℕ) : fastAdvection (O.normal (t,(x,θ)))
      (knownJets O p a (t,(x,θ)) i) (knownJets O p a (t,(x,θ)) j) =
      fastAdvection (O.normal (t,(x,0)))
        (knownJets O p a (t,(x,0)) i) (knownJets O p a (t,(x,0)) j) := by
    rw [(hJ j).fastAdvection_zero,(hJ j).fastAdvection_zero]
  unfold nonlinearGrade convolution
  apply congrArg₂ (·+·)
  · apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    split_ifs
    · exact hs i j
    · rfl
  · apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    split_ifs
    · exact hf i j
    · rfl

end EulerPacketCylinderField
