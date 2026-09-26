/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.WeakGradientGluingTFixedSelection

/-! # Space-time pressure pairing for an identified slice field

Integrability of the same selected field on the inner carrier upgrades its
slice weak derivative identity to the full-space test-function pairing.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Heat

noncomputable section
namespace CKN.Core.Step4

/-- An integrable slice derivative satisfies the space-time pairing for every
test function compactly supported in its product carrier. -/
theorem pressure_pairing_of_integrable_slice_derivative
    {B : Set Vec3} {J : Set ℝ} {p D : ParabolicPoint → ℝ} (i : Fin 3)
    (hp : IntegrableOn p (B ×ˢ J) volume) (hD : IntegrableOn D (B ×ˢ J) volume)
    (hweak : ∀ᵐ s ∂volume.restrict J,
      HasWeakPartialDerivOn B i (fun x => p (x, s)) (fun x => D (x, s)))
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ B ×ˢ J) :
    (∫ z : ParabolicPoint, p z * spatialPartial ψ i z) =
      -(∫ z : ParabolicPoint, D z * ψ z) := by
  have hsp := spatialPartial_contDiff hψ i
  have hspts : tsupport (fun z : Vec3 × ℝ => spatialPartial ψ i z) ⊆ tsupport ψ := by
    apply closure_minimal
    · intro z hz
      by_contra hnot
      exact hz (spatialPartial_zero_of_not_mem_tsupport_public hψ hnot i)
    · exact isClosed_tsupport ψ
  have hspc : HasCompactSupport (fun z : Vec3 × ℝ => spatialPartial ψ i z) :=
    hψc.isCompact.of_isClosed_subset (isClosed_tsupport _) hspts
  have hleft : IntegrableOn (fun z : Vec3 × ℝ => p z * spatialPartial ψ i z) (B ×ˢ J) volume := by
    obtain ⟨C, hC⟩ := hspc.exists_bound_of_continuous hsp.continuous
    exact hp.mul_bdd hsp.continuous.measurable.aestronglyMeasurable
      (Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using hC z)
  have hright : IntegrableOn (fun z : Vec3 × ℝ => D z * ψ z) (B ×ˢ J) volume := by
    obtain ⟨C, hC⟩ := hψc.exists_bound_of_continuous hψ.continuous
    exact hD.mul_bdd hψ.continuous.measurable.aestronglyMeasurable
      (Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using hC z)
  have hiter : (∫ s in J, ∫ x in B, p (x, s) * spatialPartial ψ i (x, s)) =
      -(∫ s in J, ∫ x in B, D (x, s) * ψ (x, s)) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [hweak] with s hs
    obtain ⟨hsm, hc, hsup⟩ := slice_testFunction hψ hψc hψs s
    exact hs _ hsm hc hsup
  have hprod := setIntegral_prod_eq_of_iterated hleft hright hiter
  have hl : (∫ z : Vec3 × ℝ, p z * spatialPartial ψ i z) =
      ∫ z in B ×ˢ J, p z * spatialPartial ψ i z := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    rw [spatialPartial_zero_of_not_mem_tsupport_public hψ (fun h => hz (hψs h)) i, mul_zero]
  have hr : (∫ z : Vec3 × ℝ, D z * ψ z) = ∫ z in B ×ˢ J, D z * ψ z := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    rw [image_eq_zero_of_notMem_tsupport (fun h => hz (hψs h)), mul_zero]
  change (∫ z : Vec3 × ℝ, p z * spatialPartial ψ i z) = -(∫ z : Vec3 × ℝ, D z * ψ z)
  rw [hl, hr]
  exact hprod

/-- The inner symmetric metric ball is the exact spatial-time product used
by the selected weak pressure derivative. -/
theorem inner_pressure_ball_eq_product (z₀ : ParabolicPoint) (R : ℝ) :
    Metric.ball z₀ (R / 2) = vec3Ball z₀.1 (R / 2) ×ˢ
      Ioo (z₀.2 - R ^ 2 / 4) (z₀.2 + R ^ 2 / 4) := by
  rw [metricBall_eq_parabolicBall, show (R / 2) ^ 2 = R ^ 2 / 4 by ring]

end CKN.Core.Step4
