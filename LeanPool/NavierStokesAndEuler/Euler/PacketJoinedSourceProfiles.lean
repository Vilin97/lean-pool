/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketJoinedSourceOperators
public import LeanPool.NavierStokesAndEuler.Euler.PacketJoinedProfilesParity

@[expose] public section

/-!
Actual source profiles for the complete high inverse. The primary datum is a
genuine profile with its path/time witnesses; every later forcing is proved
admissible and every later profile is constructed by the two source inverses.
-/

noncomputable section

namespace EulerPacketCylinderField

open Set EulerSmoothLimit EulerPacketProfileRecursion

variable (P : ℝ) [Fact (0 < P)] (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : EulerTransversePacketProvider.Data U) (hT : M.T = D.T)
  (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : EulerTransversePacketProvider.HistoryData (D.initial τ hτ hτT.le))
  (primary : Profile) (hprimary : ProfileRegularity P M.T M.T_pos.le D.support primary)

def joinedSourceProfiles : ℕ → Profile :=
  profiles (joinedSourceOperators P M D τ hτ hτT B) primary

def joinedSourceProfileWitness (p : ℕ) :
    ProfileRegularity P M.T M.T_pos.le D.support (joinedSourceProfiles P M D τ hτ hτT B primary p)
      :=
  joinedProfileWitness M D hT τ hτ hτT B (joinedSourceCoefficientData P M D τ hτ hτT B hT)
    rfl rfl rfl primary hprimary p

def joinedSource_meanForcing (p : ℕ) (hp : 2 ≤ p) :
    EulerMeanPacketProvider.Forcing M
      (meanForce (joinedSourceOperators P M D τ hτ hτT B) p
        (joinedSourceProfiles P M D τ hτ hτT B primary)) :=
  joined_profiles_meanForcing M D hT τ hτ hτT B (joinedSourceCoefficientData P M D τ hτ hτT B hT)
    rfl rfl rfl primary hprimary p hp

def joinedSource_highForcing (p : ℕ) (hp : 2 ≤ p) :
    EulerTransversePacketProvider.Forcing P D
      (highForce (joinedSourceOperators P M D τ hτ hτT B) p
        (joinedSourceProfiles P M D τ hτ hτT B primary)) :=
  joined_profiles_highForcing M D hT τ hτ hτT B (joinedSourceCoefficientData P M D τ hτ hτT B hT)
    rfl rfl rfl primary hprimary p hp

theorem joinedSourceCoefficientEven
    (hF : ∀ t x, D.F.field t (-x) = D.F.field t x)
    (hM : ∀ t x, D.M.field t (-x) = D.M.field t x) :
    CoefficientEven M.T (joinedSourceOperators P M D τ hτ hτT B) where
  inverse t x _ := D.inverse_even hF (D.clamp t) x
  strain t x _ := hM (D.clamp t) x
  normal t x _ := D.normal_even hF (D.clamp t) x

include hT hprimary in
theorem joinedSourceProfiles_parity
    (eM : EulerMeanPacketProvider.EvenData M)
    (hSym : ∀ x, -x ∈ D.support ↔ x ∈ D.support)
    (hF : ∀ t x, D.F.field t (-x) = D.F.field t x)
    (hDM : ∀ t x, D.M.field t (-x) = D.M.field t x)
    (hBH : ∀ t x, B.H.field t (-x) = B.H.field t x)
    (hprimaryParity : ProfileParity M.T primary) (p : ℕ) :
    ProfileParity M.T (joinedSourceProfiles P M D τ hτ hτT B primary p) :=
  joined_profiles_parity M D hT τ hτ hτT B (joinedSourceCoefficientData P M D τ hτ hτT B hT)
    rfl rfl rfl (joinedSourceCoefficientEven P M D τ hτ hτT B hF hDM) eM
    hSym hF hDM hBH primary hprimary hprimaryParity p

end EulerPacketCylinderField
