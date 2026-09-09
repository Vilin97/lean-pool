/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketSourceData
public import LeanPool.NavierStokesAndEuler.Euler.PhysicalChildParent
public import LeanPool.NavierStokesAndEuler.Euler.PacketParentLabelBudgets

@[expose] public section

/-! The literal physical-label bounds feed the source coefficient factory.
The constructed child inherits this interface from its proved three-field
estimate; frame and coefficient identifications are not extra hypotheses. -/

noncomputable section

namespace EulerParentPacketFrames

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients EulerLpTranslation
  EulerPacketParentLabelBounds EulerMeanClassicalWordBounds EulerPacketCofactor
  EulerPacketPiola EulerGraphInvariantFlow

structure LabelData (G : Parent) where
  K : ℝ
  K_one : 1 ≤ K
  displacement : Icc (0 : ℝ) G.T → SmoothL2Field Space
  velocity : Icc (0 : ℝ) G.T → SmoothL2Field Space
  acceleration : Icc (0 : ℝ) G.T → SmoothL2Field Space
  displacement_match : ∀ t x, (displacement t).field x=G.displacement.field t x
  velocity_match : ∀ t x, (velocity t).field x=G.velocity.field t x
  acceleration_match : ∀ t x, (acceleration t).field x=G.acceleration.field t x
  displacement_bound : ∀ t, HasLabelBound K (displacement t)
  velocity_bound : ∀ t, HasLabelBound K (velocity t)
  acceleration_bound : ∀ t, HasLabelBound K (acceleration t)

namespace LabelData

variable {G : Parent} (L : LabelData G)

theorem frame_match (t : Icc (0 : ℝ) G.T) (x : Space) :
    G.frame.field t x=ContinuousLinearMap.id ℝ Space+fderiv ℝ (L.displacement t).field (G.ell • x)
      := by
  rw [G.frame_apply,← funext (L.displacement_match t)]

theorem first_match (t : Icc (0 : ℝ) G.T) (x : Space) :
    G.first.field t x=fderiv ℝ (L.velocity t).field (G.ell • x) := by
  rw [G.first_apply,← funext (L.velocity_match t)]

theorem second_match (t : Icc (0 : ℝ) G.T) (x : Space) :
    G.second.field t x=fderiv ℝ (L.acceleration t).field (G.ell • x) := by
  rw [G.second_apply,← funext (L.acceleration_match t)]

def normalBudget {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    (m : Space) (hm : ‖m‖=1) (R : U ≃ₗᵢ[ℝ] EulerTransverseFrameCoordinates.referencePlane m)
    (S : Set Space) (hS : IsCompact S) (q : ℕ) :
    EulerTransversePacketJoin.NormalBudget (G.transverseData m hm R S hS) q
      (EulerPacketParentNormalBudget.radius (coefficientRadius L.K)
        (frameAmplitude L.K) (gradientAmplitude L.K)) :=
  EulerPacketParentLabelBudgets.normalBudget (G.transverseData m hm R S hS) q
    L.displacement L.velocity G.ell L.K G.ell_pos.le G.ell_le_one (zero_le_one.trans L.K_one)
    L.displacement_bound L.velocity_bound L.frame_match L.first_match G.frame_det

def meanBudget (H : LowBounds G) (q : ℕ) (Ti : ℝ) (hT : G.T ≤ 1) (hTi : G.T⁻¹ ≤ Ti) :
    EulerMeanPacketProvider.Budget (G.meanData H) q
      (EulerPacketParentMeanBudget.radius q G.T Ti (coefficientRadius L.K)
        (frameAmplitude L.K) (gradientAmplitude L.K) (gradientAmplitude L.K) H.L) :=
  EulerPacketParentLabelBudgets.meanBudget (G.meanData H) q
    L.displacement L.velocity L.acceleration Ti L.K hT hTi (zero_le_one.trans L.K_one)
    L.displacement_bound L.velocity_bound L.acceleration_bound
    L.frame_match L.first_match L.second_match G.frame_det

theorem block_nonneg (A : SmoothL2Field Space) (n : ℕ) :
    0 ≤ classicalBlockSize EulerPacketParentLabelBounds.direction 6 A.toLp A.translation_contDiff n
      := by
  unfold classicalBlockSize classicalBaseSize
  positivity

variable {P : ℝ} [Fact (0 < P)] (B : EulerPhysicalGraphFlowBounds.Data P G.T)
  (k : ℝ) (m : Space) (hgraph : ∀ t z, graphConstraint k m (B.A.field t z)=0)
  (nextEll : ℝ) (hnext : 0 < nextEll) (hnext1 : nextEll ≤ 1)
  (E : Icc (0 : ℝ) G.T → EulerChildParticleFieldBounds.Data)
  (hD : ∀ t, (E t).parentDisplacement=L.displacement t)
  (hV : ∀ t, (E t).parentVelocity=L.velocity t)
  (hW : ∀ t, (E t).parentAcceleration=L.acceleration t)
  (hd : ∀ t, (E t).displacement=B.displacementField k m G.ell G.ell_pos t)
  (hv : ∀ t, (E t).velocity=B.velocityField k m G.ell G.ell_pos t)
  (hw : ∀ t, (E t).acceleration=B.accelerationFieldL2 k m G.ell G.ell_pos t)

def child (K : ℝ) (hK : 1 ≤ K)
    (hb : ∀ t n,
      classicalBlockSize direction 6 (E t).childDisplacement.toLp (E
        t).childDisplacement.translation_contDiff n+
      classicalBlockSize direction 6 (E t).childVelocity.toLp (E
        t).childVelocity.translation_contDiff n+
      classicalBlockSize direction 6 (E t).childAcceleration.toLp (E
        t).childAcceleration.translation_contDiff n ≤
        K^(n+1)*(n.factorial : ℝ)^2) :
    LabelData (G.child B k m hgraph nextEll hnext hnext1) := by
  have hmatch := G.child_fields_match B k m hgraph nextEll hnext hnext1 E
    (fun t x => by rw [hD]; exact L.displacement_match t x)
    (fun t x => by rw [hV]; exact L.velocity_match t x)
    (fun t x => by rw [hW]; exact L.acceleration_match t x) hd hv hw
  exact {
    K := K
    K_one := hK
    displacement := fun t => (E t).childDisplacement
    velocity := fun t => (E t).childVelocity
    acceleration := fun t => (E t).childAcceleration
    displacement_match := fun t x => (hmatch t x).1
    velocity_match := fun t x => (hmatch t x).2.1
    acceleration_match := fun t x => (hmatch t x).2.2
    displacement_bound := fun t n => by
      have h1 := block_nonneg (E t).childVelocity n
      have h2 := block_nonneg (E t).childAcceleration n
      linarith [hb t n]
    velocity_bound := fun t n => by
      have h1 := block_nonneg (E t).childDisplacement n
      have h2 := block_nonneg (E t).childAcceleration n
      linarith [hb t n]
    acceleration_bound := fun t n => by
      have h1 := block_nonneg (E t).childDisplacement n
      have h2 := block_nonneg (E t).childVelocity n
      linarith [hb t n] }

end LabelData
end EulerParentPacketFrames
