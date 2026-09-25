/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradient
public import LeanPool.CaffarelliKohnNirenberg.Setting.Energy.Calculus
public import LeanPool.CaffarelliKohnNirenberg.Setting.ScalingInvarianceTests

/-!
# Pressure Gradient Origin Clause Pairing

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section
namespace CKN.Core.Step4

/-! # The origin clause as a full-space pairing

Clause `(OC)` of the paper is stated as an iterated pairing, first in space and
then in time, against a smooth compactly supported test function carried by a
product box `B' ×ˢ J`.  The transfer lemmas downstream consume it instead as a
single integral over the whole space-time carrier.

This file bridges the two shapes.  Because the test function is supported in the
box, the spatial gradient of the test function is supported there as well, so
both integrands vanish outside `B' ×ˢ J`.  Fubini on the product box, applied to
the two integrable products, therefore identifies the box integral with the
iterated one, and the box may be replaced by the whole carrier without changing
either side. -/

/-- **Full-space form of the origin clause.**

If the iterated space-time pairing identity
`∫_J ∫_{B'} p ∂ᵢψ = -∫_J ∫_{B'} D ψ` holds for a smooth compactly supported
`ψ` carried by the box `B' ×ˢ J`, with `p` and `D` integrable on that box, then
the same identity holds as a single integral over the whole carrier: the box may
be replaced by all of space-time on both sides.

The support hypothesis is what makes the replacement legitimate: `ψ` vanishes
off the box, and so does its spatial derivative `∂ᵢψ`, since the latter is
supported inside the support of `ψ`. -/
theorem originClause_spacetime_pairing_of_iterated
    {B' : Set Vec3} {J : Set ℝ} {p D : ParabolicPoint → ℝ}
    {ψ : Vec3 × ℝ → ℝ} {i : Fin 3}
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ)
    (hsupp : tsupport ψ ⊆ B' ×ˢ J)
    (hp : IntegrableOn p (B' ×ˢ J) volume)
    (hD : IntegrableOn D (B' ×ˢ J) volume)
    (hiter : (∫ t in J, ∫ x in B', p (x, t) * spatialPartial ψ i (x, t)) =
      -∫ t in J, ∫ x in B', D (x, t) * ψ (x, t)) :
    (∫ z : ParabolicPoint, p z * spatialPartial ψ i z) =
      -(∫ z : ParabolicPoint, D z * ψ z) := by
  have hsp : ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => spatialPartial ψ i z) :=
    spatialPartial_contDiff hψ.1 i
  have hspc : HasCompactSupport (fun z : Vec3 × ℝ => spatialPartial ψ i z) := by
    apply HasCompactSupport.of_support_subset_isCompact hψ.2.1.isCompact
    intro z hz
    by_contra hnot
    apply hz
    exact spatialPartial_zero_of_not_mem_tsupport_public hψ.1 hnot i
  have hspts : tsupport (fun z : Vec3 × ℝ => spatialPartial ψ i z) ⊆ tsupport ψ := by
    apply closure_minimal
    · intro z hz
      by_contra hnot
      apply hz
      exact spatialPartial_zero_of_not_mem_tsupport_public hψ.1 hnot i
    · exact isClosed_tsupport ψ
  have hleft : IntegrableOn
      (fun z : ParabolicPoint => p z * spatialPartial ψ i z) (B' ×ˢ J) volume := by
    obtain ⟨C, hC⟩ := hspc.exists_bound_of_continuous hsp.continuous
    have hmul := hp.mul_bdd hsp.continuous.measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by
        simpa only [Real.norm_eq_abs] using hC z)
    simpa only [IntegrableOn] using hmul
  have hright : IntegrableOn
      (fun z : ParabolicPoint => D z * ψ z) (B' ×ˢ J) volume := by
    obtain ⟨C, hC⟩ := hψ.2.1.exists_bound_of_continuous hψ.1.continuous
    have hmul := hD.mul_bdd hψ.1.continuous.measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by
        simpa only [Real.norm_eq_abs] using hC z)
    simpa only [IntegrableOn] using hmul
  have hprod := setIntegral_prod_eq_of_iterated hleft hright hiter
  have hleft_full : (∫ z : Vec3 × ℝ, p z * spatialPartial ψ i z) =
      ∫ z in B' ×ˢ J, p z * spatialPartial ψ i z := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    rw [image_eq_zero_of_notMem_tsupport (f := fun y : Vec3 × ℝ => spatialPartial ψ i y)
      (fun hzt => hz (hsupp (hspts hzt)))]
    simp
  have hright_full : (∫ z : Vec3 × ℝ, D z * ψ z) =
      ∫ z in B' ×ˢ J, D z * ψ z := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    rw [image_eq_zero_of_notMem_tsupport (f := ψ) (fun hzt => hz (hsupp hzt))]
    simp
  change (∫ z : Vec3 × ℝ, p z * spatialPartial ψ i z) =
    -(∫ z : Vec3 × ℝ, D z * ψ z)
  rw [hleft_full, hright_full]
  exact hprod

end CKN.Core.Step4
