/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.Biholomorphic
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.CartanUniqueness
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.Circular
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.IdentityPrinciple

/-!
# Rigidity of biholomorphic maps

Equality of first jets and circular-domain linearity follow from Cartan's uniqueness theorem.
The independent analytic step uses Cauchy's derivative formula to show that a
rotation-equivariant holomorphic map is linear. Equality is asserted on the source, not for
arbitrary ambient representatives outside it. Reference: [Scheidemann][Scheidemann2005] (2005),
Section 3.3.

## Main results

`IsBiholomorphic.eqOn_of_value_fderiv_eq` is rigidity from equality of 1-jets.
`IsBiholomorphic.exists_linearEquiv_of_circular` is linearity of a biholomorphism of circular
domains fixing the origin. `eqOn_fderiv_of_circle_equivariant` is the analytic step that a
rotation-equivariant holomorphic map is linear.

## References

* [V. Scheidemann, *Introduction to Complex Analysis in Several Variables*][Scheidemann2005]
-/

public section

open Set Filter Metric
open scoped Topology

namespace SeveralComplexVariables

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]

omit [FiniteDimensional ℂ F] in
/-- Two biholomorphisms with the same source and target are determined by their value and derivative
at one point of a bounded connected source. Depends on Cartan uniqueness; boundedness of the
target is unnecessary. -/
theorem IsBiholomorphic.eqOn_of_value_fderiv_eq
    {e e' : OpenPartialHomeomorph E F} (he : IsBiholomorphic e) (he' : IsBiholomorphic e')
    (hs : e'.source = e.source) (ht : e'.target = e.target)
    (hc : IsPreconnected e.source) (hb : Bornology.IsBounded e.source)
    {a : E} (ha : a ∈ e.source) (hv : e' a = e a)
    (hd : fderiv ℂ e' a = fderiv ℂ e a) : EqOn e' e e.source := by
  let := FiniteDimensional.complete ℂ E
  have hmem : MapsTo e' e.source e.target := by
    intro x hx
    rw [← ht]
    exact e'.map_source (hs ▸ hx)
  have hd' : DifferentiableOn ℂ e' e.source := hs ▸ he'.1
  have hcomp : DifferentiableOn ℂ (e.symm ∘ e') e.source := he.2.comp hd' hmem
  have hder : fderiv ℂ (e.symm ∘ e') a = ContinuousLinearMap.id ℂ E := by
    rw [fderiv_comp a (he.symm.differentiableAt (hmem ha))
      ((hd' a ha).differentiableAt (e.open_source.mem_nhds ha)), hv, hd]
    exact he.fderiv_symm_comp ha
  have hid := eqOn_id_of_mapsTo_of_fderiv_eq_id e.open_source hc hb
    (hcomp.analyticOnNhd_of_finiteDimensional e.open_source)
    (fun x hx => e.symm.map_source (hmem hx)) ha
    (by simp [hv, e.left_inv ha]) hder
  intro x hx
  have h := congrArg e (hid hx)
  simpa only [Function.comp_apply, e.right_inv (hmem hx), id_eq] using h

omit [FiniteDimensional ℂ F] in
/-- A holomorphic map commuting with complex rotations agrees with its derivative at zero on a
preconnected neighborhood of zero. Cauchy's derivative formula on scalar slices proves local
equality, and the identity theorem propagates it. -/
theorem eqOn_fderiv_of_circle_equivariant [CompleteSpace F] {U : Set E} (ho : IsOpen U)
    (hc : IsPreconnected U) (hzero : (0 : E) ∈ U) {f : E → F}
    (hf : DifferentiableOn ℂ f U)
    (hrot : ∀ z ∈ U, ∀ c : ℂ, ‖c‖ = 1 → f (c • z) = c • f z) :
    EqOn f (fderiv ℂ f 0) U := by
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp (ho.mem_nhds hzero)
  apply hf.eqOn_of_preconnected_of_eqOn ho hc (fderiv ℂ f 0).differentiable.differentiableOn
    isOpen_ball ⟨0, mem_ball_self hr⟩ hsub
  intro z hz
  have hcz (c : ℂ) (hc : c ∈ closedBall 0 1) : c • z ∈ U := by
    apply hsub
    rw [mem_ball, dist_zero_right] at hz ⊢
    rw [mem_closedBall, dist_zero_right] at hc
    exact (norm_smul c z).le.trans_lt
      ((mul_le_mul_of_nonneg_right hc (norm_nonneg z)).trans_lt (by simpa using hz))
  have hd : DifferentiableOn ℂ (fun c : ℂ => f (c • z)) (closedBall 0 1) := by
    intro c hc
    exact ((hf (c • z) (hcz c hc)).differentiableAt
      (ho.mem_nhds (hcz c hc))).comp c (differentiableAt_id.smul_const z)
      |>.differentiableWithinAt
  have hd' : DifferentiableOn ℂ (fun c : ℂ => c • f z) (closedBall 0 1) :=
    (differentiable_id.smul_const (f z)).differentiableOn
  have heq := circleIntegral.integral_congr (c := 0) (show (0 : ℝ) ≤ 1 by norm_num)
    (f := fun c : ℂ => (1 / (c - 0) ^ 2) • f (c • z))
    (g := fun c : ℂ => (1 / (c - 0) ^ 2) • (c • f z))
    (fun c hc => by dsimp only; rw [hrot z (hsub hz) c (by simpa using hc)])
  rw [hd.deriv_eq_smul_circleIntegral (by norm_num),
    hd'.deriv_eq_smul_circleIntegral (by norm_num)] at heq
  have hdf : HasDerivAt (fun c : ℂ => f (c • z)) (fderiv ℂ f 0 z) 0 := by
    have hpre : HasFDerivAt f (fderiv ℂ f 0) ((0 : ℂ) • z) := by
      simpa using ((hf 0 hzero).differentiableAt (ho.mem_nhds hzero)).hasFDerivAt
    simpa [Function.comp_def] using hpre.comp_hasDerivAt 0 ((hasDerivAt_id (0 : ℂ)).smul_const z)
  have hlin : HasDerivAt (fun c : ℂ => c • f z) (f z) 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).smul_const (f z)
  rw [hdf.deriv, hlin.deriv] at heq
  exact (smul_right_injective F Complex.two_pi_I_ne_zero heq).symm

omit [FiniteDimensional ℂ F] in
/-- Origin-preserving biholomorphisms of circular domains commute with rotations. This follows from
Cartan uniqueness on the bounded source; boundedness of the target is unnecessary. -/
theorem IsBiholomorphic.map_smul_of_circular
    {e : OpenPartialHomeomorph E F} (he : IsBiholomorphic e)
    (hc : IsPreconnected e.source) (hb : Bornology.IsBounded e.source)
    (hrot : IsCircular e.source) (hrot' : IsCircular e.target)
    (hzero : (0 : E) ∈ e.source) (hfix : e 0 = 0)
    {z : E} (hz : z ∈ e.source) {c : ℂ} (hc1 : ‖c‖ = 1) :
    e (c • z) = c • e z := by
  let := FiniteDimensional.complete ℂ E
  have hcn : c ≠ 0 := norm_ne_zero_iff.mp (by rw [hc1]; norm_num)
  have hci : ‖c⁻¹‖ = 1 := by simp [hc1]
  have hi0 : e.symm 0 = 0 := by simpa [hfix] using e.left_inv hzero
  let g : E → E := fun x => e.symm (c⁻¹ • e (c • x))
  have hmem : MapsTo (fun x => c⁻¹ • e (c • x)) e.source e.target :=
    fun x hx => hrot'.smul_mem (e.map_source (hrot.smul_mem hx hc1)) hci
  have hdiff : DifferentiableOn ℂ g e.source :=
    he.2.comp ((he.1.comp (differentiable_id.const_smul c).differentiableOn
      (fun x hx => hrot.smul_mem hx hc1)).const_smul c⁻¹) hmem
  have hinner : HasFDerivAt (fun x => c⁻¹ • e (c • x)) (fderiv ℂ e 0) 0 := by
    have hd : HasFDerivAt e (fderiv ℂ e 0) (c • (0 : E)) := by
      simpa using (he.differentiableAt hzero).hasFDerivAt
    convert (hd.comp 0 ((hasFDerivAt_id (𝕜 := ℂ) (0 : E)).const_smul c)).const_smul c⁻¹ using 1
    · simp only [Function.comp_def, Pi.smul_def]
    · ext x
      simp [hcn]
  have hd : HasFDerivAt g (ContinuousLinearMap.id ℂ E) 0 := by
    have hinv : HasFDerivAt e.symm (fderiv ℂ e.symm (e 0)) (c⁻¹ • e (c • (0 : E))) := by
      simpa [hfix] using (he.symm.differentiableAt (e.map_source hzero)).hasFDerivAt
    simpa [g, Function.comp_def, he.fderiv_symm_comp hzero] using hinv.comp 0 hinner
  have hid := eqOn_id_of_mapsTo_of_fderiv_eq_id e.open_source hc hb
    (hdiff.analyticOnNhd_of_finiteDimensional e.open_source)
    (fun x hx => e.symm.map_source (hmem hx)) hzero
    (by simp [g, hfix, hi0]) hd.fderiv
  have heq : c⁻¹ • e (c • z) = e z := by
    simpa only [g, e.right_inv (hmem hz), id_eq] using congrArg e (hid hz)
  simpa [hcn] using congrArg (fun y : F => c • y) heq

/-- An origin-preserving biholomorphism between circular domains with bounded source agrees with an
invertible complex-linear map. Cartan uniqueness gives rotation equivariance, and Cauchy's
derivative formula eliminates the nonlinear terms. Zero-dimensional spaces are included;
membership of zero supplies nonemptiness. -/
theorem IsBiholomorphic.exists_linearEquiv_of_circular
    {e : OpenPartialHomeomorph E F} (he : IsBiholomorphic e)
    (hc : IsPreconnected e.source) (hb : Bornology.IsBounded e.source)
    (hrot : IsCircular e.source)
    (hrot' : IsCircular e.target) (hzero : (0 : E) ∈ e.source) (hfix : e 0 = 0) :
      ∃ L : E ≃L[ℂ] F, EqOn e L e.source := by
  let := FiniteDimensional.complete ℂ F
  obtain ⟨L, hL⟩ := he.isInvertible_fderiv hzero
  refine ⟨L, ?_⟩
  have h := eqOn_fderiv_of_circle_equivariant e.open_source hc hzero he.1
    (fun z hz c hc1 => he.map_smul_of_circular hc hb hrot hrot' hzero hfix hz hc1)
  intro x hx
  change e x = L.toContinuousLinearMap x
  rw [hL]
  exact h hx

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
