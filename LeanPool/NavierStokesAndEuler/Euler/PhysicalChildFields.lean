/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ChildParticleFieldBounds
public import LeanPool.NavierStokesAndEuler.Euler.PhysicalGraphFlowBounds

/-! Applying the child composition estimate to the actual physical
graph flow. The input fields are the concrete displacement, velocity and
acceleration constructed from the periodic corrected packet. -/

@[expose] public section


noncomputable section

namespace EulerPhysicalChildFields

open Set MeasureTheory EulerSmoothLimit EulerLiftedGradientSpace EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerPacketParentLabelBounds EulerGevrey
  EulerSmoothBanachFlow EulerSmoothFlowGevrey EulerGraphInvariantFlow
open scoped ContDiff

variable {P T : ℝ} [Fact (0 < P)] (G : EulerPhysicalGraphFlowBounds.Data P T)
  (k : ℝ) (m : Vector3) (hgraph : ∀ t z, graphConstraint k m (G.A.field t z) = 0)
  (ell : ℝ) (hell : 0 < ell)
  (D V W : Icc (0 : ℝ) T → SmoothL2Field Space)
  (K : ℝ) (hK : 1 ≤ K)
  (hD : ∀ t, HasLabelBound K (D t)) (hV : ∀ t, HasLabelBound K (V t)) (hW : ∀ t, HasLabelBound K (W
      t))
  (M R : ℝ) (hM : 1 ≤ M) (hR : 1 ≤ R)
  (hd : ∀ t, (G.displacementField k m ell hell t).HasJetBound M R)
  (hv : ∀ t, (G.velocityField k m ell hell t).HasJetBound M R)
  (hw : ∀ t, (G.accelerationFieldL2 k m ell hell t).HasJetBound M R)
  (hds : ∀ t, HasSupBound (G.displacementField k m ell hell t).field M R)
  (hvs : ∀ t, HasSupBound (G.velocityField k m ell hell t).field M R)

include hgraph in
theorem inner_eq_forward (t : Icc (0 : ℝ) T) :
    (fun x => x+(G.displacementField k m ell hell t).field x) =
      (flowData T G.time_nonneg (physicalCoefficient k m T G.A ell)).forward t := by
  funext x
  rw [G.displacementField_eq k m hgraph,displacement_eq]
  abel

/-- Data, bundling `parentDisplacement`, `parentVelocity`, `parentAcceleration`, `K` and the
required compatibility proofs. -/
def data (t : Icc (0 : ℝ) T) : EulerChildParticleFieldBounds.Data where
  parentDisplacement := D t
  parentVelocity := V t
  parentAcceleration := W t
  K := K
  K_one := hK
  parentDisplacement_bound := hD t
  parentVelocity_bound := hV t
  parentAcceleration_bound := hW t
  displacement := G.displacementField k m ell hell t
  velocity := G.velocityField k m ell hell t
  acceleration := G.accelerationFieldL2 k m ell hell t
  amp := M
  rad := R
  amp_one := hM
  rad_one := hR
  displacement_bound := hd t
  velocity_bound := hv t
  acceleration_bound := hw t
  displacement_sup := hds t
  velocity_sup := hvs t
  volume_preserving := by
    rw [inner_eq_forward G k m hgraph ell hell t]
    exact physical_forward_measurePreserving k m T G.time_nonneg G.A hgraph G.divergence ell
        hell.ne' t

include hgraph hK hD hV hW hM hR hd hv hw hds hvs in
theorem data_inner (t : Icc (0 : ℝ) T) :
    (data G k m hgraph ell hell D V W K hK hD hV hW M R hM hR hd hv hw hds hvs t).inner =
      (flowData T G.time_nonneg (physicalCoefficient k m T G.A ell)).forward t :=
  inner_eq_forward G k m hgraph ell hell t

omit G k m hgraph ell hell D V W K hK hD hV hW M R hM hR hd hv hw hds hvs in
/-- Child amplitude, given by
`K+M+9*((embeddingCost*K)*K)*M+9*(((embeddingCost*K)*K)*(4*K))*M^2`. -/
def childAmplitude (K M : ℝ) : ℝ :=
  K+M+9*((embeddingCost*K)*K)*M+9*(((embeddingCost*K)*K)*(4*K))*M^2

omit G k m hgraph ell hell D V W K hK hD hV hW M R hM hR hd hv hw hds hvs in
/-- Child radius, given by `(1+R)*((1+M)*(16*K)+2)+R`. -/
def childRadius (K M R : ℝ) : ℝ := (1+R)*((1+M)*(16*K)+2)+R

include hgraph hK hD hV hW hM hR hd hv hw hds hvs in
theorem fields_jet_bound (t : Icc (0 : ℝ) T) :
    let E := data G k m hgraph ell hell D V W K hK hD hV hW M R hM hR hd hv hw hds hvs t
    E.childDisplacement.HasJetBound (childAmplitude K M) (childRadius K M R) ∧
    E.childVelocity.HasJetBound (childAmplitude K M) (childRadius K M R) ∧
    E.childAcceleration.HasJetBound (childAmplitude K M) (childRadius K M R) := by
  let E := data G k m hgraph ell hell D V W K hK hD hV hW M R hM hR hd hv hw hds hvs t
  exact ⟨E.childDisplacement_bound,E.childVelocity_bound,E.childAcceleration_bound⟩

include hgraph hK hD hV hW hM hR hd hv hw hds hvs in
theorem fields_label_bound (J : ℝ)
    (ha : EulerParameterWordGevrey.sobolevCoefficientAmplitude (Fin 3) 6
      (childRadius K M R) (childAmplitude K M) ≤ J)
    (hr : EulerParameterWordGevrey.sobolevCoefficientRadius (Fin 3) (childRadius K M R) ≤ J)
    (t : Icc (0 : ℝ) T) :
    let E := data G k m hgraph ell hell D V W K hK hD hV hW M R hM hR hd hv hw hds hvs t
    HasLabelBound J E.childDisplacement ∧ HasLabelBound J E.childVelocity ∧ HasLabelBound J
        E.childAcceleration :=
  (data G k m hgraph ell hell D V W K hK hD hV hW M R hM hR hd hv hw hds hvs t).child_label_bounds
      J ha hr

end EulerPhysicalChildFields
