/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SmoothL2ClassicalBounds
public import LeanPool.NavierStokesAndEuler.Euler.SmoothL2GevreyCalculus

@[expose] public section

/-! The actual three fields in the chain rule for X(t,Y(t,a)) have
Gevrey L² bounds. The parent is controlled by its physical-label H⁶
norm, and Y preserves volume. The new radius is linear in the inner
radius, with only polynomial dependence on the parent and amplitudes. -/

noncomputable section

namespace EulerChildParticleFieldBounds

open MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerPacketParentLabelBounds EulerGevrey
open scoped ContDiff

structure Data where
  parentDisplacement : SmoothL2Field Space
  parentVelocity : SmoothL2Field Space
  parentAcceleration : SmoothL2Field Space
  K : ℝ
  K_one : 1 ≤ K
  parentDisplacement_bound : HasLabelBound K parentDisplacement
  parentVelocity_bound : HasLabelBound K parentVelocity
  parentAcceleration_bound : HasLabelBound K parentAcceleration
  displacement : SmoothL2Field Space
  velocity : SmoothL2Field Space
  acceleration : SmoothL2Field Space
  amp : ℝ
  rad : ℝ
  amp_one : 1 ≤ amp
  rad_one : 1 ≤ rad
  displacement_bound : displacement.HasJetBound amp rad
  velocity_bound : velocity.HasJetBound amp rad
  acceleration_bound : acceleration.HasJetBound amp rad
  displacement_sup : HasSupBound displacement.field amp rad
  velocity_sup : HasSupBound velocity.field amp rad
  volume_preserving : MeasurePreserving (fun x => x+displacement.field x) volume volume

namespace Data

variable (G : Data)

def inner (x : Space) : Space := x+G.displacement.field x
def compositionRadius (s : ℝ) : ℝ := (1+G.rad)*((1+G.amp)*s+2)
def radius : ℝ := G.compositionRadius (16*G.K)+G.rad
def firstAmplitude : ℝ := (embeddingCost*G.K)*G.K
def secondAmplitude : ℝ := G.firstAmplitude*(4*G.K)
def amplitude : ℝ := G.K+G.amp+9*G.firstAmplitude*G.amp+9*G.secondAmplitude*G.amp^2

theorem K_nonneg : 0 ≤ G.K := le_trans zero_le_one G.K_one
theorem amp_nonneg : 0 ≤ G.amp := le_trans zero_le_one G.amp_one
theorem rad_nonneg : 0 ≤ G.rad := le_trans zero_le_one G.rad_one
theorem compositionRadius_nonneg (s : ℝ) (hs : 0 ≤ s) : 0 ≤ G.compositionRadius s := by
  have := G.amp_nonneg
  have := G.rad_nonneg
  unfold compositionRadius
  positivity
theorem radius_nonneg : 0 ≤ G.radius :=
  add_nonneg (G.compositionRadius_nonneg _ (mul_nonneg (by norm_num) G.K_nonneg)) G.rad_nonneg
theorem rad_le_radius : G.rad ≤ G.radius :=
  le_add_of_nonneg_left (G.compositionRadius_nonneg _ (mul_nonneg (by norm_num) G.K_nonneg))
theorem firstAmplitude_nonneg : 0 ≤ G.firstAmplitude :=
  mul_nonneg (mul_nonneg embeddingCost_nonneg G.K_nonneg) G.K_nonneg
theorem secondAmplitude_nonneg : 0 ≤ G.secondAmplitude :=
  mul_nonneg G.firstAmplitude_nonneg (mul_nonneg (by norm_num) G.K_nonneg)
theorem amplitude_nonneg : 0 ≤ G.amplitude := by
  have := G.K_nonneg
  have := G.amp_nonneg
  have := G.firstAmplitude_nonneg
  have := G.secondAmplitude_nonneg
  unfold amplitude
  positivity

theorem compositionRadius_le_radius (s : ℝ) (hs : s ≤ 16*G.K) : G.compositionRadius s ≤ G.radius :=
  by
  calc
    G.compositionRadius s ≤ G.compositionRadius (16*G.K) := by
      unfold compositionRadius
      exact mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left hs (add_nonneg zero_le_one G.amp_nonneg)) (le_refl
          (2 : ℝ)))
        (add_nonneg zero_le_one G.rad_nonneg)
    _ ≤ G.radius := le_add_of_nonneg_right G.rad_nonneg

theorem inner_smooth : ContDiff ℝ ∞ G.inner := contDiff_id.add G.displacement.smooth
theorem inner_positive (n : ℕ) (hn : 0 < n) (x : Space) :
    ‖iteratedFDeriv ℝ n G.inner x‖ ≤ (1+G.amp)*(1+G.rad)^n*(n.factorial : ℝ)^2 :=
  positive_id_add_bound G.displacement.field G.displacement.smooth G.amp G.rad
    G.amp_nonneg G.rad_nonneg G.displacement_sup n hn x

def parentComposed (U : SmoothL2Field Space) (hU : HasLabelBound G.K U) : SmoothL2Field Space :=
  composeField G.inner G.inner_smooth G.volume_preserving (1+G.amp) (1+G.rad)
    (by linarith [G.amp_nonneg]) (by linarith [G.rad_nonneg]) G.inner_positive
    U G.K G.K G.K_nonneg G.K_nonneg (hasJetBound_of_labelBound U G.K hU)

theorem parentComposed_bound (U : SmoothL2Field Space) (hU : HasLabelBound G.K U) :
    (G.parentComposed U hU).HasJetBound G.K G.radius := by
  have h := composeField_bound G.inner G.inner_smooth G.volume_preserving (1+G.amp) (1+G.rad)
    (by linarith [G.amp_nonneg]) (by linarith [G.rad_nonneg]) G.inner_positive
    U G.K G.K G.K_nonneg G.K_nonneg (hasJetBound_of_labelBound U G.K hU)
  exact h.mono G.K_nonneg (G.compositionRadius_nonneg G.K G.K_nonneg) le_rfl
    (G.compositionRadius_le_radius G.K (by nlinarith [G.K_nonneg]))

def firstCoefficient (U : SmoothL2Field Space) (x : Space) : Space →L[ℝ] Space :=
  fderiv ℝ U.field (G.inner x)
def secondCoefficient (U : SmoothL2Field Space) (x : Space) : Space →L[ℝ] Space →L[ℝ] Space :=
  fderiv ℝ (fderiv ℝ U.field) (G.inner x)

theorem firstCoefficient_smooth (U : SmoothL2Field Space) : ContDiff ℝ ∞ (G.firstCoefficient U) :=
  (U.smooth.fderiv_right (m := ∞) (by simp)).comp G.inner_smooth
theorem secondCoefficient_smooth (U : SmoothL2Field Space) : ContDiff ℝ ∞ (G.secondCoefficient U) :=
  ((U.smooth.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)).comp G.inner_smooth

theorem firstCoefficient_bound (U : SmoothL2Field Space) (hU : HasLabelBound G.K U) :
    HasSupBound (G.firstCoefficient U) G.firstAmplitude G.radius := by
  have hu : HasSupBound U.field (embeddingCost*G.K) G.K := sup_bound_of_labelBound U G.K hU
  have hd := hu.derivative (mul_nonneg embeddingCost_nonneg G.K_nonneg) G.K_nonneg
  have hc := hd.comp G.inner_smooth (U.smooth.fderiv_right (m := ∞) (by simp))
    G.firstAmplitude_nonneg (by linarith [G.amp_nonneg]) (by linarith [G.rad_nonneg])
    (mul_nonneg (by norm_num) G.K_nonneg) G.inner_positive
  exact hc.mono G.firstAmplitude_nonneg (G.compositionRadius_nonneg _ (by nlinarith [G.K_nonneg]))
    le_rfl (G.compositionRadius_le_radius (4*G.K) (by nlinarith [G.K_nonneg]))

theorem secondCoefficient_bound (U : SmoothL2Field Space) (hU : HasLabelBound G.K U) :
    HasSupBound (G.secondCoefficient U) G.secondAmplitude G.radius := by
  have hu : HasSupBound U.field (embeddingCost*G.K) G.K := sup_bound_of_labelBound U G.K hU
  have hd := (hu.derivative (mul_nonneg embeddingCost_nonneg G.K_nonneg) G.K_nonneg).derivative
    G.firstAmplitude_nonneg (mul_nonneg (by norm_num) G.K_nonneg)
  have hc := hd.comp G.inner_smooth
    ((U.smooth.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp))
    G.secondAmplitude_nonneg (by linarith [G.amp_nonneg]) (by linarith [G.rad_nonneg])
    (by nlinarith [G.K_nonneg]) G.inner_positive
  have he : (4 : ℝ)*(4*G.K)=16*G.K := by ring
  rw [he] at hc
  exact hc.mono G.secondAmplitude_nonneg (G.compositionRadius_nonneg _ (by nlinarith [G.K_nonneg]))
    le_rfl (G.compositionRadius_le_radius (16*G.K) le_rfl)

theorem velocity_bound_radius : G.velocity.HasJetBound G.amp G.radius :=
  G.velocity_bound.mono G.amp_nonneg G.rad_nonneg le_rfl G.rad_le_radius
theorem acceleration_bound_radius : G.acceleration.HasJetBound G.amp G.radius :=
  G.acceleration_bound.mono G.amp_nonneg G.rad_nonneg le_rfl G.rad_le_radius
theorem displacement_bound_radius : G.displacement.HasJetBound G.amp G.radius :=
  G.displacement_bound.mono G.amp_nonneg G.rad_nonneg le_rfl G.rad_le_radius
theorem velocity_sup_radius : HasSupBound G.velocity.field G.amp G.radius :=
  G.velocity_sup.mono G.amp_nonneg G.rad_nonneg le_rfl G.rad_le_radius

def firstTerm (U : SmoothL2Field Space) (hU : HasLabelBound G.K U) : SmoothL2Field Space :=
  productField (G.firstCoefficient U) (G.firstCoefficient_smooth U) G.velocity
    G.firstAmplitude G.amp G.radius G.firstAmplitude_nonneg G.amp_nonneg G.radius_nonneg
    (G.firstCoefficient_bound U hU) G.velocity_bound_radius

theorem firstTerm_bound (U : SmoothL2Field Space) (hU : HasLabelBound G.K U) :
    (G.firstTerm U hU).HasJetBound (3*G.firstAmplitude*G.amp) G.radius :=
  productField_bound (G.firstCoefficient U) (G.firstCoefficient_smooth U) G.velocity
    G.firstAmplitude G.amp G.radius G.firstAmplitude_nonneg G.amp_nonneg G.radius_nonneg
    (G.firstCoefficient_bound U hU) G.velocity_bound_radius

def quadraticCoefficient (x : Space) : Space →L[ℝ] Space :=
  G.secondCoefficient G.parentDisplacement x (G.velocity.field x)

theorem quadraticCoefficient_smooth : ContDiff ℝ ∞ G.quadraticCoefficient :=
  (G.secondCoefficient_smooth G.parentDisplacement).clm_apply G.velocity.smooth

theorem quadraticCoefficient_bound :
    HasSupBound G.quadraticCoefficient (3*G.secondAmplitude*G.amp) G.radius :=
  (G.secondCoefficient_bound G.parentDisplacement G.parentDisplacement_bound).apply
    G.velocity_sup_radius
    (G.secondCoefficient_smooth G.parentDisplacement) G.velocity.smooth G.secondAmplitude_nonneg
    G.amp_nonneg G.radius_nonneg

def quadraticTerm : SmoothL2Field Space :=
  productField G.quadraticCoefficient G.quadraticCoefficient_smooth G.velocity
    (3*G.secondAmplitude*G.amp) G.amp G.radius
    (mul_nonneg (mul_nonneg (by norm_num) G.secondAmplitude_nonneg) G.amp_nonneg) G.amp_nonneg
      G.radius_nonneg
    G.quadraticCoefficient_bound G.velocity_bound_radius

theorem quadraticTerm_bound :
    G.quadraticTerm.HasJetBound (9*G.secondAmplitude*G.amp^2) G.radius := by
  have h := productField_bound G.quadraticCoefficient G.quadraticCoefficient_smooth G.velocity
    (3*G.secondAmplitude*G.amp) G.amp G.radius
    (mul_nonneg (mul_nonneg (by norm_num) G.secondAmplitude_nonneg) G.amp_nonneg) G.amp_nonneg
      G.radius_nonneg
    G.quadraticCoefficient_bound G.velocity_bound_radius
  have he : 3*(3*G.secondAmplitude*G.amp)*G.amp = 9*G.secondAmplitude*G.amp^2 := by ring
  rw [he] at h
  exact h

def accelerationTerm : SmoothL2Field Space :=
  productField (G.firstCoefficient G.parentDisplacement) (G.firstCoefficient_smooth
    G.parentDisplacement)
    G.acceleration G.firstAmplitude G.amp G.radius G.firstAmplitude_nonneg G.amp_nonneg
      G.radius_nonneg
    (G.firstCoefficient_bound G.parentDisplacement G.parentDisplacement_bound)
      G.acceleration_bound_radius

theorem accelerationTerm_bound :
    G.accelerationTerm.HasJetBound (3*G.firstAmplitude*G.amp) G.radius :=
  productField_bound (G.firstCoefficient G.parentDisplacement) (G.firstCoefficient_smooth
    G.parentDisplacement)
    G.acceleration G.firstAmplitude G.amp G.radius G.firstAmplitude_nonneg G.amp_nonneg
      G.radius_nonneg
    (G.firstCoefficient_bound G.parentDisplacement G.parentDisplacement_bound)
      G.acceleration_bound_radius

def childDisplacement : SmoothL2Field Space :=
  addField (G.parentComposed G.parentDisplacement G.parentDisplacement_bound) G.displacement
def childVelocity : SmoothL2Field Space :=
  addField (addField (G.parentComposed G.parentVelocity G.parentVelocity_bound) G.velocity)
    (G.firstTerm G.parentDisplacement G.parentDisplacement_bound)
def childAcceleration : SmoothL2Field Space :=
  addField (addField (addField (addField (addField
    (G.parentComposed G.parentAcceleration G.parentAcceleration_bound)
    (G.firstTerm G.parentVelocity G.parentVelocity_bound))
    (G.firstTerm G.parentVelocity G.parentVelocity_bound)) G.quadraticTerm) G.acceleration)
      G.accelerationTerm

theorem childDisplacement_bound : G.childDisplacement.HasJetBound G.amplitude G.radius := by
  have h := (G.parentComposed_bound G.parentDisplacement G.parentDisplacement_bound).add
    G.displacement_bound_radius
  apply h.mono (add_nonneg G.K_nonneg G.amp_nonneg) G.radius_nonneg _ le_rfl
  have h₁ := mul_nonneg G.firstAmplitude_nonneg G.amp_nonneg
  have h₂ := mul_nonneg G.secondAmplitude_nonneg (sq_nonneg G.amp)
  unfold amplitude
  nlinarith

theorem childVelocity_bound : G.childVelocity.HasJetBound G.amplitude G.radius := by
  have h := ((G.parentComposed_bound G.parentVelocity G.parentVelocity_bound).add
    G.velocity_bound_radius).add
    (G.firstTerm_bound G.parentDisplacement G.parentDisplacement_bound)
  have h₁ := mul_nonneg G.firstAmplitude_nonneg G.amp_nonneg
  have h₂ := mul_nonneg G.secondAmplitude_nonneg (sq_nonneg G.amp)
  apply h.mono (by nlinarith [G.K_nonneg,G.amp_nonneg]) G.radius_nonneg _ le_rfl
  unfold amplitude
  nlinarith

theorem childAcceleration_bound : G.childAcceleration.HasJetBound G.amplitude G.radius := by
  have h := (((((G.parentComposed_bound G.parentAcceleration G.parentAcceleration_bound).add
    (G.firstTerm_bound G.parentVelocity G.parentVelocity_bound)).add
    (G.firstTerm_bound G.parentVelocity G.parentVelocity_bound)).add G.quadraticTerm_bound).add
    G.acceleration_bound_radius).add G.accelerationTerm_bound
  have he : G.K+3*G.firstAmplitude*G.amp+3*G.firstAmplitude*G.amp+
      9*G.secondAmplitude*G.amp^2+G.amp+3*G.firstAmplitude*G.amp = G.amplitude := by
    unfold amplitude
    ring
  rw [he] at h
  exact h

theorem childDisplacement_apply (x : Space) :
    G.childDisplacement.field x = G.parentDisplacement.field (G.inner x)+G.displacement.field x :=
      rfl

theorem childVelocity_apply (x : Space) :
    G.childVelocity.field x = G.parentVelocity.field (G.inner x)+G.velocity.field x+
      fderiv ℝ G.parentDisplacement.field (G.inner x) (G.velocity.field x) := rfl

theorem childAcceleration_apply (x : Space) :
    G.childAcceleration.field x = G.parentAcceleration.field (G.inner x)+
      fderiv ℝ G.parentVelocity.field (G.inner x) (G.velocity.field x)+
      fderiv ℝ G.parentVelocity.field (G.inner x) (G.velocity.field x)+
      fderiv ℝ (fderiv ℝ G.parentDisplacement.field) (G.inner x) (G.velocity.field x)
        (G.velocity.field x)+
      G.acceleration.field x+fderiv ℝ G.parentDisplacement.field (G.inner x) (G.acceleration.field
        x) := rfl

theorem child_label_bounds (K : ℝ)
    (ha : EulerParameterWordGevrey.sobolevCoefficientAmplitude (Fin 3) 6 G.radius G.amplitude ≤ K)
    (hr : EulerParameterWordGevrey.sobolevCoefficientRadius (Fin 3) G.radius ≤ K) :
    HasLabelBound K G.childDisplacement ∧ HasLabelBound K G.childVelocity ∧ HasLabelBound K
      G.childAcceleration :=
  ⟨hasLabelBound_of_jet_bound _ _ _ K G.amplitude_nonneg G.radius_nonneg G.childDisplacement_bound
    ha hr,
   hasLabelBound_of_jet_bound _ _ _ K G.amplitude_nonneg G.radius_nonneg G.childVelocity_bound ha
     hr,
   hasLabelBound_of_jet_bound _ _ _ K G.amplitude_nonneg G.radius_nonneg G.childAcceleration_bound
     ha hr⟩

end Data
end EulerChildParticleFieldBounds
