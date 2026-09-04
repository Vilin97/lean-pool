/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
import LeanPool.Feige.TransferTestFunctions
import LeanPool.Feige.TransferProbability

/-!
# Measure-level transfer Stein identities

This file lifts the fixed-`y` identities to an arbitrary law for `Y`.
The outer integrability assumptions are stated explicitly, making the
result usable independently of how the law of `Y` is presented.
-/

open MeasureTheory Real Set

namespace Feige

namespace TransferStein

open TransferTestFunctions

/-- Real-valued conditional lower-tail transfer integrand `u`. -/
noncomputable def uTailIntegrand (d z : ℝ) : ℝ :=
  if 0 ≤ z then exp (-z / d) else 0

/-- Real-valued conditional upper-tail transfer integrand `v`. -/
noncomputable def vTailIntegrand (c z : ℝ) : ℝ :=
  if z < 0 then exp (z / c) else 0

/-- The formal derivative of `φ`, multiplied by `d`, is the conditional
`u` integrand away from the sole boundary point zero. -/
theorem d_mul_transferPhiDeriv
    {d z : ℝ} (hd : 0 < d) (hz : z ≠ 0) :
    d * transferPhiDeriv d z = uTailIntegrand d z := by
  rcases lt_or_gt_of_ne hz with hz | hz
  · rw [transferPhiDeriv, ite_eq_right (not_lt_of_ge hz.le),
      uTailIntegrand, ite_eq_right (not_le.mpr hz)]
    simp
  · rw [transferPhiDeriv, ite_eq_left hz, uTailIntegrand, ite_eq_left hz.le]
    field_simp [hd.ne']

/-- The `ψ` derivative identity has no boundary discrepancy. -/
theorem c_mul_transferPsiDeriv
    {c z : ℝ} (hc : 0 < c) :
    c * transferPsiDeriv c z = vTailIntegrand c z := by
  by_cases hz : z < 0
  · rw [transferPsiDeriv, ite_eq_left hz, vTailIntegrand, ite_eq_left hz]
    field_simp [hc.ne']
  · rw [transferPsiDeriv, ite_eq_right hz, vTailIntegrand, ite_eq_right hz]
    simp

/-- Integral bridge from the analytic `φ'` quantity to the conditional
tail formula.  Atomlessness at zero is precisely the boundary condition
needed to pass between `z ≥ 0` in the tail event and `z > 0` in the a.e.
derivative. -/
theorem d_mul_integral_transferPhiDeriv
    (ν : Measure ℝ) {d : ℝ}
    (hd : 0 < d) (hzero : ν {0} = 0) :
    d * ∫ z, transferPhiDeriv d z ∂ν =
      ∫ z, uTailIntegrand d z ∂ν := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  have hae : ∀ᵐ z ∂ν, z ≠ 0 := by
    rw [ae_iff]
    simpa only [not_not, ofPred_eq_eq_singleton] using hzero
  filter_upwards [hae] with z hz
  exact d_mul_transferPhiDeriv hd hz

/-- Integral bridge from the analytic `ψ'` quantity to the conditional
left-tail formula. -/
theorem c_mul_integral_transferPsiDeriv
    (ν : Measure ℝ) {c : ℝ} (hc : 0 < c) :
    c * ∫ z, transferPsiDeriv c z ∂ν =
      ∫ z, vTailIntegrand c z ∂ν := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => c_mul_transferPsiDeriv hc

/-- The positive `φ` expectation conditional on `Y = y`. -/
noncomputable def phiPlus (d a y : ℝ) : ℝ :=
  ∫ e : ℝ in Ioi 0, transferPhi d (y + a * e) * exp (-e)

/-- The negative `φ` expectation conditional on `Y = y`. -/
noncomputable def phiMinus (d b y : ℝ) : ℝ :=
  ∫ e : ℝ in Ioi 0, transferPhi d (y - b * e) * exp (-e)

/-- The positive derivative expectation conditional on `Y = y`. -/
noncomputable def phiDerivPlus (d a y : ℝ) : ℝ :=
  ∫ e : ℝ in Ioi 0,
    a * transferPhiDeriv d (y + a * e) * exp (-e)

/-- The negative derivative expectation conditional on `Y = y`. -/
noncomputable def phiDerivMinus (d b y : ℝ) : ℝ :=
  ∫ e : ℝ in Ioi 0,
    b * transferPhiDeriv d (y - b * e) * exp (-e)

/-- The two-sided exponential Stein identity for `φ`, averaged over an
arbitrary measure `μ`.

The four hypotheses are exactly those needed to distribute the outer
Bochner integral over subtraction and addition.
-/
theorem integral_phi_two_sided
    (μ : Measure ℝ) {d a b : ℝ}
    (hd : 0 < d) (ha : 0 < a) (hb : 0 < b)
    (hPlus : Integrable (phiPlus d a) μ)
    (hMinus : Integrable (phiMinus d b) μ)
    (hDerivPlus : Integrable (phiDerivPlus d a) μ)
    (hDerivMinus : Integrable (phiDerivMinus d b) μ) :
    (∫ y, phiPlus d a y ∂μ) - (∫ y, phiMinus d b y ∂μ) =
      (∫ y, phiDerivPlus d a y ∂μ) +
        ∫ y, phiDerivMinus d b y ∂μ := by
  rw [← integral_sub hPlus hMinus, ← integral_add hDerivPlus hDerivMinus]
  apply integral_congr_ae
  filter_upwards with y
  exact transferPhi_stein_fixed_two_sided hd ha hb

/-- Product-measure/Fubini form of the averaged `φ` identity. -/
theorem integral_phi_two_sided_prod
    (μ : Measure ℝ) [SFinite μ] {d a b : ℝ}
    (hd : 0 < d) (ha : 0 < a) (hb : 0 < b)
    (hPlus : Integrable
      (fun p : ℝ × ℝ => transferPhi d (p.1 + a * p.2) * exp (-p.2))
      (μ.prod (volume.restrict (Ioi 0))))
    (hMinus : Integrable
      (fun p : ℝ × ℝ => transferPhi d (p.1 - b * p.2) * exp (-p.2))
      (μ.prod (volume.restrict (Ioi 0))))
    (hDerivPlus : Integrable
      (fun p : ℝ × ℝ =>
        a * transferPhiDeriv d (p.1 + a * p.2) * exp (-p.2))
      (μ.prod (volume.restrict (Ioi 0))))
    (hDerivMinus : Integrable
      (fun p : ℝ × ℝ =>
        b * transferPhiDeriv d (p.1 - b * p.2) * exp (-p.2))
      (μ.prod (volume.restrict (Ioi 0)))) :
    (∫ p : ℝ × ℝ,
        transferPhi d (p.1 + a * p.2) * exp (-p.2)
          ∂μ.prod (volume.restrict (Ioi 0))) -
      (∫ p : ℝ × ℝ,
        transferPhi d (p.1 - b * p.2) * exp (-p.2)
          ∂μ.prod (volume.restrict (Ioi 0))) =
    (∫ p : ℝ × ℝ,
        a * transferPhiDeriv d (p.1 + a * p.2) * exp (-p.2)
          ∂μ.prod (volume.restrict (Ioi 0))) +
      ∫ p : ℝ × ℝ,
        b * transferPhiDeriv d (p.1 - b * p.2) * exp (-p.2)
          ∂μ.prod (volume.restrict (Ioi 0)) := by
  have hOuterPlus : Integrable (phiPlus d a) μ := by
    change Integrable
      (fun x => ∫ y in Ioi 0, transferPhi d (x + a * y) * exp (-y)) μ
    exact hPlus.integral_prod_left
  have hOuterMinus : Integrable (phiMinus d b) μ := by
    change Integrable
      (fun x => ∫ y in Ioi 0, transferPhi d (x - b * y) * exp (-y)) μ
    exact hMinus.integral_prod_left
  have hOuterDerivPlus : Integrable (phiDerivPlus d a) μ := by
    change Integrable
      (fun x => ∫ y in Ioi 0,
        a * transferPhiDeriv d (x + a * y) * exp (-y)) μ
    exact hDerivPlus.integral_prod_left
  have hOuterDerivMinus : Integrable (phiDerivMinus d b) μ := by
    change Integrable
      (fun x => ∫ y in Ioi 0,
        b * transferPhiDeriv d (x - b * y) * exp (-y)) μ
    exact hDerivMinus.integral_prod_left
  have hiter := integral_phi_two_sided μ hd ha hb
    hOuterPlus hOuterMinus hOuterDerivPlus hOuterDerivMinus
  rw [integral_prod _ hPlus, integral_prod _ hMinus,
    integral_prod _ hDerivPlus, integral_prod _ hDerivMinus]
  simpa [phiPlus, phiMinus, phiDerivPlus, phiDerivMinus] using hiter

/-- The positive `ψ` expectation conditional on `Y = y`. -/
noncomputable def psiPlus (c a y : ℝ) : ℝ :=
  ∫ e : ℝ in Ioi 0, transferPsi c (y + a * e) * exp (-e)

/-- The negative `ψ` expectation conditional on `Y = y`. -/
noncomputable def psiMinus (c b y : ℝ) : ℝ :=
  ∫ e : ℝ in Ioi 0, transferPsi c (y - b * e) * exp (-e)

/-- The positive derivative expectation conditional on `Y = y`. -/
noncomputable def psiDerivPlus (c a y : ℝ) : ℝ :=
  ∫ e : ℝ in Ioi 0,
    a * transferPsiDeriv c (y + a * e) * exp (-e)

/-- The negative derivative expectation conditional on `Y = y`. -/
noncomputable def psiDerivMinus (c b y : ℝ) : ℝ :=
  ∫ e : ℝ in Ioi 0,
    b * transferPsiDeriv c (y - b * e) * exp (-e)

/-- The two-sided exponential Stein identity for `ψ`, averaged over an
arbitrary measure `μ`. -/
theorem integral_psi_two_sided
    (μ : Measure ℝ) {c a b : ℝ}
    (hc : 0 < c) (ha : 0 < a) (hb : 0 < b)
    (hPlus : Integrable (psiPlus c a) μ)
    (hMinus : Integrable (psiMinus c b) μ)
    (hDerivPlus : Integrable (psiDerivPlus c a) μ)
    (hDerivMinus : Integrable (psiDerivMinus c b) μ) :
    (∫ y, psiPlus c a y ∂μ) - (∫ y, psiMinus c b y ∂μ) =
      (∫ y, psiDerivPlus c a y ∂μ) +
        ∫ y, psiDerivMinus c b y ∂μ := by
  rw [← integral_sub hPlus hMinus, ← integral_add hDerivPlus hDerivMinus]
  apply integral_congr_ae
  filter_upwards with y
  exact transferPsi_stein_fixed_two_sided hc ha hb

/-- Product-measure/Fubini form of the averaged `ψ` identity. -/
theorem integral_psi_two_sided_prod
    (μ : Measure ℝ) [SFinite μ] {c a b : ℝ}
    (hc : 0 < c) (ha : 0 < a) (hb : 0 < b)
    (hPlus : Integrable
      (fun p : ℝ × ℝ => transferPsi c (p.1 + a * p.2) * exp (-p.2))
      (μ.prod (volume.restrict (Ioi 0))))
    (hMinus : Integrable
      (fun p : ℝ × ℝ => transferPsi c (p.1 - b * p.2) * exp (-p.2))
      (μ.prod (volume.restrict (Ioi 0))))
    (hDerivPlus : Integrable
      (fun p : ℝ × ℝ =>
        a * transferPsiDeriv c (p.1 + a * p.2) * exp (-p.2))
      (μ.prod (volume.restrict (Ioi 0))))
    (hDerivMinus : Integrable
      (fun p : ℝ × ℝ =>
        b * transferPsiDeriv c (p.1 - b * p.2) * exp (-p.2))
      (μ.prod (volume.restrict (Ioi 0)))) :
    (∫ p : ℝ × ℝ,
        transferPsi c (p.1 + a * p.2) * exp (-p.2)
          ∂μ.prod (volume.restrict (Ioi 0))) -
      (∫ p : ℝ × ℝ,
        transferPsi c (p.1 - b * p.2) * exp (-p.2)
          ∂μ.prod (volume.restrict (Ioi 0))) =
    (∫ p : ℝ × ℝ,
        a * transferPsiDeriv c (p.1 + a * p.2) * exp (-p.2)
          ∂μ.prod (volume.restrict (Ioi 0))) +
      ∫ p : ℝ × ℝ,
        b * transferPsiDeriv c (p.1 - b * p.2) * exp (-p.2)
          ∂μ.prod (volume.restrict (Ioi 0)) := by
  have hOuterPlus : Integrable (psiPlus c a) μ := by
    change Integrable
      (fun x => ∫ y in Ioi 0, transferPsi c (x + a * y) * exp (-y)) μ
    exact hPlus.integral_prod_left
  have hOuterMinus : Integrable (psiMinus c b) μ := by
    change Integrable
      (fun x => ∫ y in Ioi 0, transferPsi c (x - b * y) * exp (-y)) μ
    exact hMinus.integral_prod_left
  have hOuterDerivPlus : Integrable (psiDerivPlus c a) μ := by
    change Integrable
      (fun x => ∫ y in Ioi 0,
        a * transferPsiDeriv c (x + a * y) * exp (-y)) μ
    exact hDerivPlus.integral_prod_left
  have hOuterDerivMinus : Integrable (psiDerivMinus c b) μ := by
    change Integrable
      (fun x => ∫ y in Ioi 0,
        b * transferPsiDeriv c (x - b * y) * exp (-y)) μ
    exact hDerivMinus.integral_prod_left
  have hiter := integral_psi_two_sided μ hc ha hb
    hOuterPlus hOuterMinus hOuterDerivPlus hOuterDerivMinus
  rw [integral_prod _ hPlus, integral_prod _ hMinus,
    integral_prod _ hDerivPlus, integral_prod _ hDerivMinus]
  simpa [psiPlus, psiMinus, psiDerivPlus, psiDerivMinus] using hiter

section Equation23

/-- Analytic `A₊ = E φ(Z₊)`. -/
noncomputable def APlus (μ : Measure ℝ) (d a : ℝ) : ℝ :=
  ∫ y, phiPlus d a y ∂μ

/-- Analytic `A₋ = E φ(Z₋)`. -/
noncomputable def AMinus (μ : Measure ℝ) (d b : ℝ) : ℝ :=
  ∫ y, phiMinus d b y ∂μ

/-- Analytic `B₊ = E ψ(Z₊)`. -/
noncomputable def BPlus (μ : Measure ℝ) (c a : ℝ) : ℝ :=
  ∫ y, psiPlus c a y ∂μ

/-- Analytic `B₋ = E ψ(Z₋)`. -/
noncomputable def BMinus (μ : Measure ℝ) (c b : ℝ) : ℝ :=
  ∫ y, psiMinus c b y ∂μ

/-- `u₊`, normalized as `d` times the `φ'` expectation.  Since
`phiDerivPlus` includes the affine chain-rule factor `a`, it is divided
out here. -/
noncomputable def uPlus (μ : Measure ℝ) (d a : ℝ) : ℝ :=
  (d / a) * ∫ y, phiDerivPlus d a y ∂μ

/-- Analytic `u₋`. -/
noncomputable def uMinus (μ : Measure ℝ) (d b : ℝ) : ℝ :=
  (d / b) * ∫ y, phiDerivMinus d b y ∂μ

/-- `v₊`, normalized as `c` times the `ψ'` expectation. -/
noncomputable def vPlus (μ : Measure ℝ) (c a : ℝ) : ℝ :=
  (c / a) * ∫ y, psiDerivPlus c a y ∂μ

/-- Analytic `v₋`. -/
noncomputable def vMinus (μ : Measure ℝ) (c b : ℝ) : ℝ :=
  (c / b) * ∫ y, psiDerivMinus c b y ∂μ

/-- The lower-test Stein identity for the analytic quantities above. -/
theorem equation23_A
    (μ : Measure ℝ) {d a b : ℝ}
    (hd : 0 < d) (ha : 0 < a) (hb : 0 < b)
    (hPlus : Integrable (phiPlus d a) μ)
    (hMinus : Integrable (phiMinus d b) μ)
    (hDerivPlus : Integrable (phiDerivPlus d a) μ)
    (hDerivMinus : Integrable (phiDerivMinus d b) μ) :
    d * (APlus μ d a - AMinus μ d b) =
      a * uPlus μ d a + b * uMinus μ d b := by
  have h := integral_phi_two_sided μ hd ha hb
    hPlus hMinus hDerivPlus hDerivMinus
  unfold APlus AMinus uPlus uMinus
  have hda : a * (d / a) = d := by field_simp
  have hdb : b * (d / b) = d := by field_simp
  rw [← mul_assoc, hda, ← mul_assoc, hdb]
  linear_combination d * h

/-- The upper-test Stein identity for the analytic quantities above. -/
theorem equation23_B
    (μ : Measure ℝ) {c a b : ℝ}
    (hc : 0 < c) (ha : 0 < a) (hb : 0 < b)
    (hPlus : Integrable (psiPlus c a) μ)
    (hMinus : Integrable (psiMinus c b) μ)
    (hDerivPlus : Integrable (psiDerivPlus c a) μ)
    (hDerivMinus : Integrable (psiDerivMinus c b) μ) :
    c * (BPlus μ c a - BMinus μ c b) =
      a * vPlus μ c a + b * vMinus μ c b := by
  have h := integral_psi_two_sided μ hc ha hb
    hPlus hMinus hDerivPlus hDerivMinus
  unfold BPlus BMinus vPlus vMinus
  have hca : a * (c / a) = c := by field_simp
  have hcb : b * (c / b) = c := by field_simp
  rw [← mul_assoc, hca, ← mul_assoc, hcb]
  linear_combination c * h

end Equation23

end TransferStein

end Feige
