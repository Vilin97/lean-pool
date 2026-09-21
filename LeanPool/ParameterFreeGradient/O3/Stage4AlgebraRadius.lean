/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.O3.BelowTwo
import LeanPool.ParameterFreeGradient.O3.Stage2RouteC

/-!
# Stage 4: exact weight algebra, barycentric identity, and radius bridge

This module isolates the source-exact algebraic parts of the accepted
estimate-sequence proof.  In particular, it keeps the exceptional first
weight separate from the stationary recurrence and proves the radius of the
regularized minimizer from its minimizing property and the actual `sInf`
definition of the distance to the minimizer set.
-/

namespace O3

/-- The source increment `a_(k+1) = A_(k+1) - A_k`, including the exceptional
first step. -/
noncomputable def belowWeightIncrement (M tau : ℝ) (k : ℕ) : ℝ :=
  belowWeight M tau (k + 1) - belowWeight M tau k

@[simp] theorem belowWeightIncrement_zero (M tau : ℝ) :
    belowWeightIncrement M tau 0 = 1 / M := by
  simp [belowWeightIncrement]

/-- With the source increment, `A_+ = A_k + a_(k+1)` is definitionally the
next weight. -/
theorem belowWeight_add_increment (M tau : ℝ) (k : ℕ) :
    belowWeight M tau k + belowWeightIncrement M tau k =
      belowWeight M tau (k + 1) := by
  unfold belowWeightIncrement
  ring

/-- For the stationary part of the recurrence, the source increment is
exactly `tau * A_(k+1)`. -/
theorem belowWeightIncrement_eq_tau_mul {M tau : ℝ} (htau : tau ≠ 1)
    {k : ℕ} (hk : 1 ≤ k) :
    belowWeightIncrement M tau k = tau * belowWeight M tau (k + 1) := by
  rw [belowWeightIncrement, belowWeight_succ hk]
  have hden : 1 - tau ≠ 0 := sub_ne_zero.mpr (Ne.symm htau)
  field_simp [hden]
  ring

/-- Equivalent multiplicative form of the later weight recurrence. -/
theorem belowWeight_eq_one_sub_tau_mul_succ {M tau : ℝ} (htau : tau ≠ 1)
    {k : ℕ} (hk : 1 ≤ k) :
    belowWeight M tau k =
      (1 - tau) * belowWeight M tau (k + 1) := by
  rw [belowWeight_succ hk]
  have hden : 1 - tau ≠ 0 := sub_ne_zero.mpr (Ne.symm htau)
  field_simp [hden]

/-- The first-step coefficient is exactly one.  This theorem deliberately
does not route through the later stationary recurrence. -/
theorem belowFirstCoefficient {M tau : ℝ} (hM : M ≠ 0) :
    M * (belowWeightIncrement M tau 0) ^ 2 / belowWeight M tau 1 = 1 := by
  simp only [belowWeightIncrement_zero, belowWeight_one]
  field_simp [hM]

/-- First-step equality with the source strong-convexity modulus
`beta_0 = 1 + lambda * sigma * A_0`. -/
theorem belowFirstCoefficient_eq_betaZero {M tau lambda sigma : ℝ}
    (hM : M ≠ 0) :
    M * (belowWeightIncrement M tau 0) ^ 2 / belowWeight M tau 1 =
      1 + lambda * sigma * belowWeight M tau 0 := by
  rw [belowFirstCoefficient hM]
  simp

/-- Exact later-step coefficient cancellation from the source tau equation. -/
theorem belowLaterCoefficient {M lambda sigma : ℝ}
    (hM : 0 < M) (hlambda : 0 < lambda) (hsigma : 0 < sigma)
    {k : ℕ} (hk : 1 ≤ k) :
    M * (belowWeightIncrement M (belowTau M lambda sigma) k) ^ 2 /
        belowWeight M (belowTau M lambda sigma) (k + 1) =
      lambda * sigma * belowWeight M (belowTau M lambda sigma) k := by
  let tau := belowTau M lambda sigma
  have htau_lt : tau < 1 := belowTau_lt_one hM hlambda hsigma
  have htau_ne : tau ≠ 1 := ne_of_lt htau_lt
  have hApos : 0 < belowWeight M tau (k + 1) :=
    belowWeight_pos hM htau_lt (by omega)
  change M * (belowWeightIncrement M tau k) ^ 2 /
      belowWeight M tau (k + 1) =
    lambda * sigma * belowWeight M tau k
  rw [belowWeightIncrement_eq_tau_mul htau_ne hk]
  have hrec := belowWeight_eq_one_sub_tau_mul_succ
    (M := M) (tau := tau) htau_ne hk
  have heq : M * tau ^ 2 = lambda * sigma * (1 - tau) :=
    belowTau_equation hM hlambda hsigma
  calc
    M * (tau * belowWeight M tau (k + 1)) ^ 2 /
          belowWeight M tau (k + 1) =
        (M * tau ^ 2) * belowWeight M tau (k + 1) := by
          field_simp [hApos.ne']
    _ = (lambda * sigma * (1 - tau)) *
          belowWeight M tau (k + 1) := by rw [heq]
    _ = lambda * sigma * belowWeight M tau k := by rw [hrec]; ring

/-- Hence the later potential coefficient is nonpositive against
`beta_k = 1 + lambda * sigma * A_k`. -/
theorem belowLaterCoefficient_le_beta {M lambda sigma : ℝ}
    (hM : 0 < M) (hlambda : 0 < lambda) (hsigma : 0 < sigma)
    {k : ℕ} (hk : 1 ≤ k) :
    M * (belowWeightIncrement M (belowTau M lambda sigma) k) ^ 2 /
        belowWeight M (belowTau M lambda sigma) (k + 1) ≤
      1 + lambda * sigma * belowWeight M (belowTau M lambda sigma) k := by
  rw [belowLaterCoefficient hM hlambda hsigma hk]
  linarith

/-- Scalar-weighted barycenter used for both `y_k` and `x_(k+1)^a`. -/
noncomputable def belowBarycenter {d : ℕ} (A a : ℝ)
    (x v : Point d) : Point d :=
  (A + a)⁻¹ • (A • x + a • v)

/-- The exact vector identity used in the one-step potential estimate. -/
theorem belowBarycenter_sub {d : ℕ} {A a : ℝ}
    (hAa : A + a ≠ 0) (x v vnext : Point d) :
    belowBarycenter A a x vnext - belowBarycenter A a x v =
      (a / (A + a)) • (vnext - v) := by
  funext i
  simp only [belowBarycenter, Pi.sub_apply, Pi.smul_apply, Pi.add_apply,
    smul_eq_mul, div_eq_mul_inv]
  field_simp [hAa]
  ring

/-- The exact composite objective `Phi = f + lambda * psi_x0`. -/
noncomputable def belowPhi {d : ℕ} (p lambda : ℝ)
    (f : Point d → ℝ) (x0 x : Point d) : ℝ :=
  f x + lambda * quadraticRegularizer p x0 x

/-- A genuine minimizer of the regularized objective lies no farther from the
center than the `sInf` distance to the original minimizer set.  This avoids
assuming that the `sInf` itself is attained. -/
theorem belowRegularizedMinimizer_radius {d : ℕ} {p lambda : ℝ}
    (hlambda : 0 < lambda)
    {f : Point d → ℝ} {x0 xlambda : Point d}
    (hmin_nonempty : (MinimizerSet f).Nonempty)
    (hxlambda : ∀ z, belowPhi p lambda f x0 xlambda ≤
      belowPhi p lambda f x0 z) :
    lpNorm p (xlambda - x0) ≤ minimizerDistance p f x0 := by
  let distances : Set ℝ :=
    (fun x : Point d ↦ lpNorm p (x - x0)) '' MinimizerSet f
  have hdistances : distances.Nonempty := hmin_nonempty.image _
  change lpNorm p (xlambda - x0) ≤ sInf distances
  apply le_csInf hdistances
  intro r hr
  rcases hr with ⟨xstar, hxstar, rfl⟩
  have hfstar : f xstar ≤ f xlambda := hxstar xlambda
  have hphi := hxlambda xstar
  have hleft : 0 ≤ lpNorm p (xlambda - x0) := lpNorm_nonneg _ _
  have hright : 0 ≤ lpNorm p (xstar - x0) := lpNorm_nonneg _ _
  unfold belowPhi quadraticRegularizer at hphi
  have hsquares : (lpNorm p (xlambda - x0)) ^ (2 : ℕ) ≤
      (lpNorm p (xstar - x0)) ^ (2 : ℕ) := by
    nlinarith
  nlinarith

/-- The source distance to a nonempty minimizer set is nonnegative. -/
theorem minimizerDistance_nonneg_of_nonempty {d : ℕ} {p : ℝ}
    {f : Point d → ℝ} {x0 : Point d}
    (hmin_nonempty : (MinimizerSet f).Nonempty) :
    0 ≤ minimizerDistance p f x0 := by
  let distances : Set ℝ :=
    (fun x : Point d ↦ lpNorm p (x - x0)) '' MinimizerSet f
  have hdistances : distances.Nonempty := hmin_nonempty.image _
  change 0 ≤ sInf distances
  apply le_csInf hdistances
  intro r hr
  rcases hr with ⟨x, _, rfl⟩
  exact lpNorm_nonneg _ _

/-- Radius comparison gives the exact regularizer budget appearing in the
final source gap bound. -/
theorem belowRegularizer_le_radius_budget {d : ℕ} {p sigma D R : ℝ}
    (hsigma : 0 < sigma) (hR : 0 ≤ R) (hDR : R ≤ D)
    {x0 x : Point d} (hxR : lpNorm p (x - x0) ≤ R) :
    (1 / sigma) * quadraticRegularizer p x0 x ≤ D ^ 2 / (2 * sigma) := by
  have hx0 : 0 ≤ lpNorm p (x - x0) := lpNorm_nonneg _ _
  have hD : 0 ≤ D := hR.trans hDR
  unfold quadraticRegularizer
  have hsquare : (lpNorm p (x - x0)) ^ (2 : ℕ) ≤ D ^ 2 := by
    nlinarith
  have hsigma_ne : sigma ≠ 0 := hsigma.ne'
  field_simp [hsigma_ne]
  nlinarith

/-- Combined version of the source radius argument and regularizer budget,
still using the actual regularized minimizer property rather than a supplied
radius certificate. -/
theorem belowRegularizedMinimizer_budget {d : ℕ} {p lambda sigma D : ℝ}
    (hlambda : 0 < lambda) (hsigma : 0 < sigma)
    {f : Point d → ℝ} {x0 xlambda : Point d}
    (hmin_nonempty : (MinimizerSet f).Nonempty)
    (hxlambda : ∀ z, belowPhi p lambda f x0 xlambda ≤
      belowPhi p lambda f x0 z)
    (hDR : minimizerDistance p f x0 ≤ D) :
    (1 / sigma) * quadraticRegularizer p x0 xlambda ≤
      D ^ 2 / (2 * sigma) := by
  apply belowRegularizer_le_radius_budget hsigma
    (minimizerDistance_nonneg_of_nonempty hmin_nonempty) hDR
  exact belowRegularizedMinimizer_radius hlambda hmin_nonempty hxlambda

/-- Pure final division step from the potential invariant and evaluation at
the regularized minimizer. -/
theorem belowPotential_to_gap {A sigma D phiXa phiXlambda psiStar h : ℝ}
    (hA : 0 < A) (hsigma : 0 < sigma)
    (hinvariant : A * phiXa ≤ psiStar)
    (hevaluation : psiStar ≤ h + A * phiXlambda)
    (hh : h ≤ D ^ 2 / (2 * sigma)) :
    phiXa - phiXlambda ≤ D ^ 2 / (2 * sigma * A) := by
  have hden : 0 < 2 * sigma * A := mul_pos (mul_pos (by norm_num) hsigma) hA
  have hcombined : A * (phiXa - phiXlambda) ≤ h := by
    linarith
  have hbudget : A * (phiXa - phiXlambda) ≤ D ^ 2 / (2 * sigma) :=
    hcombined.trans hh
  have hscale : 0 ≤ 2 * sigma := by positivity
  have hmul := mul_le_mul_of_nonneg_left hbudget hscale
  rw [le_div_iff₀ hden]
  have hsigma_ne : 2 * sigma ≠ 0 := ne_of_gt (by positivity)
  calc
    (phiXa - phiXlambda) * (2 * sigma * A) =
        (2 * sigma) * (A * (phiXa - phiXlambda)) := by ring
    _ ≤ (2 * sigma) * (D ^ 2 / (2 * sigma)) := hmul
    _ = D ^ 2 := by field_simp [hsigma_ne]

end O3
