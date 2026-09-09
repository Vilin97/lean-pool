/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransverseForwardRegularity
public import LeanPool.NavierStokesAndEuler.Euler.ContinuousGramGevrey
public import LeanPool.NavierStokesAndEuler.Euler.GevreyFixedShift

@[expose] public section

/-!
# Actual coefficient bounds for the transverse forward equation

The Gram inverse is genuinely constructed and differentiated. Its one fixed
factorial shift is absorbed into a coefficient radius enlargement. The source
generator and projected forcing coefficients then have shift-zero bounds by
actual composition, with explicit polynomial amplitudes.
-/

noncomputable section


namespace EulerTransverseForwardCoefficientGevrey

open Set ContinuousLinearMap EulerGevrey EulerOperatorGevreyCalculus
  EulerContinuousPathCalculus EulerContinuousPathComposition EulerContinuousGramPath
  EulerContinuousGramGevrey EulerTimeLpGramGevrey EulerTransverseGramPath
  EulerTransverseForwardInverse EulerTransverseForwardRegularity
open scoped ContDiff

theorem inverseRadius_bounds (c C Rc R : ℝ) (hc : 0 < c) (hRc : 0 ≤ Rc)
    (hR : 2*gramCost c C 1*(Rc+1) ≤ R) : 0 ≤ R ∧ Rc ≤ 4*R := by
  have hi : 0 ≤ c⁻¹ := inv_nonneg.mpr hc.le
  have hcost : 1 ≤ gramCost c C 1 := by
    unfold gramCost
    nlinarith [sq_nonneg C]
  have hp : 0 ≤ (gramCost c C 1-1)*(Rc+1) :=
    mul_nonneg (sub_nonneg.mpr hcost) (by linarith)
  constructor <;> nlinarith

variable {P V E : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (T : ℝ) (Q Q₁ : P → C(Icc (0 : ℝ) T,V →L[ℝ] E))
  (c : ℝ) (hc : 0 < c) (hQ : ∀ x t v, c*‖v‖^2 ≤ ‖Q x t v‖^2)
  (hQr : ContDiff ℝ ∞ Q) (hQ₁r : ContDiff ℝ ∞ Q₁)
  (Rc C₀ C₁ Ri : ℝ) (hRc : 0 ≤ Rc) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
  (hRi : 2*gramCost c C₀ 1*(Rc+1) ≤ Ri)
  (hbQ : ∀ n x, ‖iteratedFDeriv ℝ n Q x‖ ≤ C₀*majorant Rc 0 n)
  (hbQ₁ : ∀ n x, ‖iteratedFDeriv ℝ n Q₁ x‖ ≤ C₁*majorant Rc 0 n)

private local instance : NormedAddCommGroup (V →L[ℝ] V) := inferInstance
private local instance : NormedSpace ℝ (V →L[ℝ] V) := inferInstance
private local instance : NormedAddCommGroup C(Icc (0 : ℝ) T,V →L[ℝ] V) := inferInstance
private local instance : NormedSpace ℝ C(Icc (0 : ℝ) T,V →L[ℝ] V) := inferInstance
private local instance : NormedAddCommGroup C(Icc (0 : ℝ) T,V →L[ℝ] E) := inferInstance
private local instance : NormedSpace ℝ C(Icc (0 : ℝ) T,V →L[ℝ] E) := inferInstance
private local instance : NormedAddCommGroup C(Icc (0 : ℝ) T,E →L[ℝ] V) := inferInstance
private local instance : NormedSpace ℝ C(Icc (0 : ℝ) T,E →L[ℝ] V) := inferInstance

include hQr hRc hC₀ hRi hbQ in
/-- The genuine inverse becomes a shift-zero coefficient at radius `4 Ri`. -/
theorem inversePath_coefficient_bound (n : ℕ) (x : P) :
    ‖iteratedFDeriv ℝ n (fun y => gramInversePath T (Q y) c hc (hQ y)) x‖ ≤
      Ri*majorant (4*Ri) 0 n := by
  exact (inversePath_gevrey T Q c hc hQ hQr Rc C₀ hRc hC₀ hbQ Ri hRi n x).trans
    (majorant_one_le_radius_four Ri (inverseRadius_bounds c C₀ Rc Ri hc hRc hRi).1 n)

include hQr hRc hC₀ hRi hbQ in
/-- The actual left inverse `K⁻¹ Q*` has a polynomial multiplier amplitude. -/
theorem frameLeftInversePath_bound (n : ℕ) (x : P) :
    ‖iteratedFDeriv ℝ n (fun y => frameLeftInversePath T (Q y) c hc (hQ y)) x‖ ≤
      (3*Ri*C₀)*majorant (4*Ri) 0 n := by
  obtain ⟨hi,hbase⟩ := inverseRadius_bounds c C₀ Rc Ri hc hRc hRi
  have hrad : 0 ≤ 4*Ri := by positivity
  have hbQ' (j : ℕ) (y : P) : ‖iteratedFDeriv ℝ j Q y‖ ≤ C₀*majorant (4*Ri) 0 j :=
    (hbQ j y).trans (mul_le_mul_of_nonneg_left (majorant_radius_mono Rc (4*Ri) hRc hbase 0 j) hC₀)
  have hbAdj := EulerContinuousPathComposition.adjoint_bound Q hQr (4*Ri) C₀ hrad hC₀ 0 hbQ'
  have h := compose_bound (fun y => gramInversePath T (Q y) c hc (hQ y))
    (fun y => adjointMap (Q y)) (gramInversePath_contDiff T c hc Q hQ hQr)
    (contDiff_adjoint Q hQr) (4*Ri) Ri C₀ hrad hi hC₀ 0 0
    (inversePath_coefficient_bound T Q c hc hQ hQr Rc C₀ Ri hRc hC₀ hRi hbQ) hbAdj n x
  simp only [Nat.add_zero] at h
  convert h using 1
  all_goals rfl

include hQr hQ₁r hRc hC₀ hC₁ hRi hbQ hbQ₁ in
/-- The ordinary generator in (12) has actual shift-zero coefficient bounds. -/
theorem generator_bound (n : ℕ) (x : P) :
    ‖iteratedFDeriv ℝ n (fun y => generator T (Q y) (Q₁ y) c hc (hQ y)) x‖ ≤
      (18*Ri*C₀*C₁)*majorant (4*Ri) 0 n := by
  obtain ⟨hi,hbase⟩ := inverseRadius_bounds c C₀ Rc Ri hc hRc hRi
  have hrad : 0 ≤ 4*Ri := by positivity
  have hbQ₁' (j : ℕ) (y : P) : ‖iteratedFDeriv ℝ j Q₁ y‖ ≤ C₁*majorant (4*Ri) 0 j :=
    (hbQ₁ j y).trans (mul_le_mul_of_nonneg_left (majorant_radius_mono Rc (4*Ri) hRc hbase 0 j) hC₁)
  let S := fun y => compose (frameLeftInversePath T (Q y) c hc (hQ y)) (Q₁ y)
  have hSr : ContDiff ℝ ∞ S := contDiff_compose _ Q₁
    (frameLeftInversePath_contDiff T Q c hc hQ hQr) hQ₁r
  have hSb : ‖iteratedFDeriv ℝ n S x‖ ≤ (3*(3*Ri*C₀)*C₁)*majorant (4*Ri) 0 n := by
    exact compose_bound (fun y => frameLeftInversePath T (Q y) c hc (hQ y)) Q₁
      (frameLeftInversePath_contDiff T Q c hc hQ hQr) hQ₁r (4*Ri) (3*Ri*C₀) C₁
      hrad (by positivity) hC₁ 0 0
      (frameLeftInversePath_bound T Q c hc hQ hQr Rc C₀ Ri hRc hC₀ hRi hbQ) hbQ₁' n x
  change ‖iteratedFDeriv ℝ n (fun y => (-2 : ℝ) • S y) x‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply' (hSr.contDiffAt.of_le (by simp)), norm_smul]
  norm_num only [norm_neg, Real.norm_ofNat]
  exact (mul_le_mul_of_nonneg_left hSb (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring)

include hQr hRc hC₀ hRi hbQ in
/-- Multiplication by the actual projected-forcing coefficient preserves the
input factorial shift, with a polynomial amplitude. -/
theorem projected_forcing_bound (f : P → C(Icc (0 : ℝ) T,E)) (hf : ContDiff ℝ ∞ f)
    (R D : ℝ) (hR : 4*Ri ≤ R) (hD : 0 ≤ D) (d : ℕ)
    (hbf : ∀ n x, ‖iteratedFDeriv ℝ n f x‖ ≤ D*majorant R d n) (n : ℕ) (x : P) :
    ‖iteratedFDeriv ℝ n (fun y => forcingOperator T (Q y) c hc (hQ y) (f y)) x‖ ≤
      (9*Ri*C₀*D)*majorant R d n := by
  have hi := (inverseRadius_bounds c C₀ Rc Ri hc hRc hRi).1
  have hrad : 0 ≤ 4*Ri := by positivity
  have hR0 : 0 ≤ R := hrad.trans hR
  have hbL (j : ℕ) (y : P) :
      ‖iteratedFDeriv ℝ j (fun z => frameLeftInversePath T (Q z) c hc (hQ z)) y‖ ≤
        (3*Ri*C₀)*majorant R 0 j :=
    (frameLeftInversePath_bound T Q c hc hQ hQr Rc C₀ Ri hRc hC₀ hRi hbQ j y).trans
      (mul_le_mul_of_nonneg_left (majorant_radius_mono (4*Ri) R hrad hR 0 j) (by positivity))
  have h := apply_bound (fun y => frameLeftInversePath T (Q y) c hc (hQ y)) f
    (frameLeftInversePath_contDiff T Q c hc hQ hQr) hf R (3*Ri*C₀) D hR0 (by positivity) hD 0 d hbL
      hbf n x
  have he : 3*(3*Ri*C₀)*D = 9*Ri*C₀*D := by ring
  simp only [Nat.zero_add, he] at h
  convert h using 1
  all_goals rfl

end EulerTransverseForwardCoefficientGevrey
