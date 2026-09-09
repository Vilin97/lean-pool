/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketProfileBudget

@[expose] public section

/-! Time-endpoint equality transports the actual path norm and its profile without changing any
  bound. -/

noncomputable section

namespace EulerPacketCylinderField

open Set EulerPacketProfileRecursion EulerPacketTimeProfile

def timeProfileChange {T T' : ℝ} (g : C(Icc (0 : ℝ) T,ℝ)) (h : T = T') :
    C(Icc (0 : ℝ) T',ℝ) := h ▸ g

theorem timeProfileChange_pos {T T' : ℝ} (g : C(Icc (0 : ℝ) T,ℝ)) (hg : ∀ t, 0 < g t)
    (h : T = T') (t : Icc (0 : ℝ) T') : 0 < timeProfileChange g h t := by
  subst T'
  exact hg t

@[simp] theorem timeProfileChange_roundtrip {T T' : ℝ} (g : C(Icc (0 : ℝ) T,ℝ)) (h : T = T') :
    timeProfileChange (timeProfileChange g h) h.symm = g := by
  subst T'
  rfl

namespace Field

variable {P T T' : ℝ} [Fact (0 < P)] {raw : VectorField} {G : Field P T raw}
  {q d : ℕ} {R A : ℝ}

theorem WordBound.changeTime (hG : G.WordBound q R A d) (h : T = T') :
    (G.changeTime h).WordBound q R A d := by
  subst T'
  exact hG

theorem WordBound.normalized_profile_eq {hT : 0 ≤ T}
    {g : C(Icc (0 : ℝ) T,ℝ)} {hg : ∀ t, 0 < g t}
    (hG : (G.normalized hT g hg).WordBound q R A d)
    (g' : C(Icc (0 : ℝ) T,ℝ)) (hg' : ∀ t, 0 < g' t) (he : g = g') :
    (G.normalized hT g' hg').WordBound q R A d := by
  subst g'
  exact hG

theorem WordBound.normalized_changeTime (hT : 0 ≤ T)
    (g : C(Icc (0 : ℝ) T,ℝ)) (hg : ∀ t, 0 < g t)
    (hG : (G.normalized hT g hg).WordBound q R A d)
    (h : T = T') (hT' : 0 ≤ T')
    (g' : C(Icc (0 : ℝ) T',ℝ)) (hg' : ∀ t, 0 < g' t) (he : timeProfileChange g h = g') :
    ((G.changeTime h).normalized hT' g' hg').WordBound q R A d := by
  subst T'
  change g = g' at he
  subst g'
  exact hG

end Field
end EulerPacketCylinderField

namespace EulerPacketTimeProfile.Scales

open Set EulerPacketCylinderField

def changeTime {T T' : ℝ} (S : Scales (Icc (0 : ℝ) T)) (h : T = T') :
    Scales (Icc (0 : ℝ) T') := h ▸ S

@[simp] theorem high_changeTime {T T' : ℝ} (S : Scales (Icc (0 : ℝ) T)) (h : T = T') (p : ℕ) :
    (S.changeTime h).high p = timeProfileChange (S.high p) h := by
  subst T'
  rfl

@[simp] theorem mean_changeTime {T T' : ℝ} (S : Scales (Icc (0 : ℝ) T)) (h : T = T') (p : ℕ) :
    (S.changeTime h).mean p = timeProfileChange (S.mean p) h := by
  subst T'
  rfl

@[simp] theorem changeTime_roundtrip {T T' : ℝ} (S : Scales (Icc (0 : ℝ) T)) (h : T = T') :
    (S.changeTime h).changeTime h.symm = S := by
  subst T'
  rfl

end EulerPacketTimeProfile.Scales
