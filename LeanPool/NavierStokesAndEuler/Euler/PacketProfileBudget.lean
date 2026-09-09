/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketProfileRegularity
public import LeanPool.NavierStokesAndEuler.Euler.PacketKnownPieceBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderTimeUnique

@[expose] public section

/-! The actual field estimates needed to close the recursive packet construction. -/

noncomputable section

namespace EulerPacketCylinderField

open Set EulerSmoothLimit EulerPacketProfileRecursion EulerPacketTimeProfile
  EulerPacketShiftArithmetic

variable {P T : ℝ} [Fact (0 < P)] {hT : 0 ≤ T} {support : Set Space} {a : Profile}

structure ProfileBudget (G : ProfileRegularity P T hT support a)
    (S : Scales (Icc (0 : ℝ) T)) (R : ℝ) (p : ℕ) : Prop where
  high : (G.high.normalized hT (S.high p) (S.high_pos p)).WordBound 6 R 1 (highShift p)
  highDerivative : (G.highDerivative.normalized hT (S.high p) (S.high_pos p)).WordBound 6 R 1
    (highShift p)
  mean : (G.mean.normalized hT (S.mean p) (S.mean_pos p)).WordBound 6 R 1 (meanShift p)
  meanDerivative : (G.meanDerivative.normalized hT (S.mean p) (S.mean_pos p)).WordBound 6 R 1
    (meanShift p)
  corrector : (G.corrector.normalized hT (S.high p) (S.high_pos p)).WordBound 6 R 1 (highShift p)
  correctorDerivative : (G.correctorDerivative.normalized hT (S.high p) (S.high_pos p)).WordBound 6
    R 1
    (highShift p)
  pressure : (G.pressure.normalized hT (S.high p) (S.high_pos p)).WordBound 6 R 1 (highShift p)

theorem Field.normalized_wordBound_congr {raw : VectorField}
    (A : Field P T raw) (hT : 0 ≤ T)
    (g k : C(Icc (0 : ℝ) T,ℝ)) (hg : ∀ t, 0 < g t) (hk : ∀ t, 0 < k t)
    (he : g = k) (q d : ℕ) (R C : ℝ)
    (hb : (A.normalized hT k hk).WordBound q R C d) :
    (A.normalized hT g hg).WordBound q R C d := by
  subst k
  exact hb

namespace ProfileBudget

variable {S : Scales (Icc (0 : ℝ) T)} {R : ℝ}

theorem prefixBound {p : ℕ} {a : ℕ → Profile}
    (G : ∀ i, i < p → ProfileRegularity P T hT support (a i))
    (hG : ∀ i (hi : i < p), ProfileBudget (G i hi) S R i) :
    PrefixBound (ProfileRegularity.prefixFields G) hT S R where
  high i hi _ := (hG i hi).high
  mean i hi _ := (hG i hi).mean
  corrector i hi _ := (hG i hi).corrector

theorem transfer {p : ℕ} {support' : Set Space} (hTpos : 0 < T)
    {G : ProfileRegularity P T hT support a} (hG : ProfileBudget G S R p)
    (H : ProfileRegularity P T hT support' a) : ProfileBudget H S R p where
  high := hG.high.normalized_of_raw_eq H.high hT (S.high p) (S.high_pos p) (fun _ _ _ => rfl)
  mean := hG.mean.normalized_of_raw_eq H.mean hT (S.mean p) (S.mean_pos p) (fun _ _ _ => rfl)
  corrector := hG.corrector.normalized_of_raw_eq H.corrector hT (S.high p) (S.high_pos p) (fun _ _
    _ => rfl)
  pressure := hG.pressure.normalized_of_raw_eq H.pressure hT (S.high p) (S.high_pos p) (fun _ _ _
    => rfl)
  highDerivative := hG.highDerivative.normalized_of_raw_eq H.highDerivative hT (S.high p)
    (S.high_pos p)
    (TimeDerivative.raw_eq (hT := hTpos) H.high_time G.high_time)
  meanDerivative := hG.meanDerivative.normalized_of_raw_eq H.meanDerivative hT (S.mean p)
    (S.mean_pos p)
    (TimeDerivative.raw_eq (hT := hTpos) H.mean_time G.mean_time)
  correctorDerivative := hG.correctorDerivative.normalized_of_raw_eq H.correctorDerivative hT
    (S.high p)
    (S.high_pos p) (TimeDerivative.raw_eq (hT := hTpos) H.corrector_time G.corrector_time)

end ProfileBudget
end EulerPacketCylinderField
