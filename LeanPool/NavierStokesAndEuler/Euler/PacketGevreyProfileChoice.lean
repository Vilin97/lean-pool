/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketBudgetTimeChange

/-! One positive growth profile and one scalar amplitude determine all grade profiles. -/

@[expose] public section


noncomputable section

namespace EulerPacketCylinderField

open Set

theorem timeProfileChange_smul {T T' : ℝ} (g : C(Icc (0 : ℝ) T, ℝ)) (h : T = T') (c : ℝ) :
    timeProfileChange (c • g) h = c • timeProfileChange g h := by
  subst T'
  rfl

end EulerPacketCylinderField

namespace EulerPacketTimeProfile.Scales

open Set EulerPacketCylinderField

theorem high_eq_smul_growth {K : Type*} [TopologicalSpace K] (S : Scales K) (p : ℕ) :
    S.high p = meanScale S.H0 p • S.growth := by
  apply ContinuousMap.ext
  intro t
  change S.growth t*meanScale S.H0 p = meanScale S.H0 p*S.growth t
  exact mul_comm _ _

theorem high_timeProfile_eq {T T' : ℝ} (S : Scales (Icc (0 : ℝ) T))
    (h : T = T') (g : C(Icc (0 : ℝ) T', ℝ)) (α : ℝ)
    (hgrowth : timeProfileChange S.growth h = α • g) (p : ℕ) :
    timeProfileChange (S.high p) h = (α*meanScale S.H0 p) • g := by
  rw [high_eq_smul_growth,timeProfileChange_smul,hgrowth,smul_smul,mul_comm]

/-- Of time profile, given by `ofGrowth (α • timeProfileChange g h) (fun t => mul_pos hα
(timeProfileChange_pos g hg h t))`. -/
def ofTimeProfile {T T' : ℝ} (g : C(Icc (0 : ℝ) T, ℝ)) (hg : ∀ t, 0 < g t)
    (h : T = T') (α : ℝ) (hα : 0 < α) : Scales (Icc (0 : ℝ) T') :=
  ofGrowth (α • timeProfileChange g h)
    (fun t => mul_pos hα (timeProfileChange_pos g hg h t))

theorem ofTimeProfile_growth {T T' : ℝ} (g : C(Icc (0 : ℝ) T, ℝ)) (hg : ∀ t, 0 < g t)
    (h : T = T') (α : ℝ) (hα : 0 < α) :
    timeProfileChange (ofTimeProfile g hg h α hα).growth h.symm = α • g := by
  change timeProfileChange (α • timeProfileChange g h) h.symm = α • g
  rw [timeProfileChange_smul,timeProfileChange_roundtrip]

theorem ofTimeProfile_high {T T' : ℝ} (g : C(Icc (0 : ℝ) T, ℝ)) (hg : ∀ t, 0 < g t)
    (h : T = T') (α : ℝ) (hα : 0 < α) (p : ℕ) :
    timeProfileChange ((ofTimeProfile g hg h α hα).high p) h.symm =
      (α*meanScale (ofTimeProfile g hg h α hα).H0 p) • g :=
  high_timeProfile_eq (ofTimeProfile g hg h α hα) h.symm g α
    (ofTimeProfile_growth g hg h α hα) p

theorem gradeFactor_pos {K : Type*} [TopologicalSpace K] (S : Scales K)
    (α : ℝ) (hα : 0 < α) (p : ℕ) : 0 < α*meanScale S.H0 p :=
  mul_pos hα (meanScale_pos S.H0 S.H0_pos p)

end EulerPacketTimeProfile.Scales
