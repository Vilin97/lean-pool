/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Fourier.AddCircle
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.Subharmonic

/-!
# Harmonic polynomial majorants and the submean inequality

Real parts of complex polynomials in `(z - a) / r` are harmonic and approximate every continuous
function on the circle of radius `r` about `a` uniformly, by density of trigonometric
polynomials. Consequently a continuous function satisfies the submean inequality on a closed
disc as soon as it lies below the center value of every such harmonic polynomial that dominates
it on the boundary circle.

Combined with the maximum principle on discs, this gives the submean inequality on every closed
disc in the domain for continuous subharmonic functions, whose definition only asks for the
inequality on small circles.

References: [Fritzsche–Grauert][FritzscheGrauert2002] (2002), Chapter II, Section 2;
[Ransford][Ransford1995] (1995), Chapter 2.

## Main results

* `le_circleAverage_of_forall_polynomial_majorant`: **Harmonic-majorant criterion.** A function
  continuous on a circle whose center value is dominated by the center value of every harmonic
  polynomial majorant on the circle satisfies the submean inequality.
* `SubharmonicOn.le_circleAverage_of_continuousOn`: **Submean inequality on closed discs.** A
  continuous subharmonic function satisfies the submean inequality on every closed disc contained in
  its domain.

## References

* [K. Fritzsche and H. Grauert, *From Holomorphic Functions to Complex
  Manifolds*][FritzscheGrauert2002]
* [T. Ransford, *Potential Theory in the Complex Plane*][Ransford1995]
-/

public section

open Filter Metric Set Real
open scoped Topology

namespace SeveralComplexVariables

/-- Every trigonometric polynomial is the sum of a polynomial and a conjugated polynomial in the
circle variable. -/
theorem exists_polynomial_of_mem_span_fourier (ψ : C(AddCircle (2 * π), ℂ))
    (hψ : ψ ∈ Submodule.span ℂ (Set.range (fourier (T := 2 * π)))) :
    ∃ Q₁ Q₂ : Polynomial ℂ, ∀ x : AddCircle (2 * π),
      ψ x = Q₁.eval ((AddCircle.toCircle x : Circle) : ℂ) +
        (starRingEnd ℂ) (Q₂.eval ((AddCircle.toCircle x : Circle) : ℂ)) := by
  induction hψ using Submodule.span_induction with
  | mem ψ hψ =>
    obtain ⟨n, rfl⟩ := hψ
    rcases le_or_gt 0 n with hn | hn
    · refine ⟨Polynomial.X ^ n.toNat, 0, fun x => ?_⟩
      simp only [fourier_apply, AddCircle.toCircle_zsmul, Circle.coe_zpow, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_zero, map_zero, add_zero]
      rw [← zpow_natCast, Int.toNat_of_nonneg hn]
    · set m := (-n).toNat with hmdef
      refine ⟨0, Polynomial.X ^ m, fun x => ?_⟩
      simp only [fourier_apply, AddCircle.toCircle_zsmul, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_zero, zero_add]
      have hm : (n : ℤ) = -(m : ℤ) := by
        rw [hmdef, Int.toNat_of_nonneg (neg_nonneg.mpr hn.le), neg_neg]
      rw [hm, zpow_neg, zpow_natCast, Circle.coe_inv_eq_conj, Circle.coe_pow]
  | zero => exact ⟨0, 0, fun x => by simp⟩
  | add ψ₁ ψ₂ _ _ ih₁ ih₂ =>
    obtain ⟨Q₁, Q₂, h₁⟩ := ih₁
    obtain ⟨Q₃, Q₄, h₂⟩ := ih₂
    refine ⟨Q₁ + Q₃, Q₂ + Q₄, fun x => ?_⟩
    simp only [ContinuousMap.add_apply, h₁, h₂, Polynomial.eval_add, map_add]
    ring
  | smul c ψ _ ih =>
    obtain ⟨Q₁, Q₂, h⟩ := ih
    refine ⟨Polynomial.C c * Q₁, Polynomial.C ((starRingEnd ℂ) c) * Q₂, fun x => ?_⟩
    simp only [ContinuousMap.smul_apply, smul_eq_mul, h, Polynomial.eval_mul, Polynomial.eval_C,
      map_mul, Complex.conj_conj]
    ring

/-- Continuous functions on a circle are uniformly approximated by real parts of polynomials in the
normalized circle variable. -/
theorem exists_polynomial_re_approx {v : ℂ → ℝ} {a : ℂ} {r : ℝ} (hr : 0 < r)
    (hv : ContinuousOn v (sphere a r)) {ε : ℝ} (hε : 0 < ε) :
    ∃ Q : Polynomial ℂ, ∀ z ∈ sphere a r, |v z - (Q.eval ((z - a) / r)).re| < ε := by
  have hpos : (0 : ℝ) < 2 * π := Real.two_pi_pos
  have : Fact (0 < 2 * π) := ⟨hpos⟩
  let e : AddCircle (2 * π) → ℂ := fun x => a + r * (AddCircle.toCircle x : ℂ)
  have he_cont : Continuous e := by
    have := continuous_subtype_val.comp (AddCircle.continuous_toCircle (T := 2 * π))
    fun_prop
  have he_mem : ∀ x, e x ∈ sphere a r := fun x => by
    simp [e, abs_of_pos hr]
  let φ : C(AddCircle (2 * π), ℂ) :=
    ⟨fun x => (v (e x) : ℂ), Complex.continuous_ofReal.comp (hv.comp_continuous he_cont he_mem)⟩
  have hφ : φ ∈ closure ((Submodule.span ℂ (Set.range (fourier (T := 2 * π)))) : Set _) := by
    rw [← Submodule.topologicalClosure_coe, span_fourier_closure_eq_top]
    trivial
  obtain ⟨ψ, hψ, hdist⟩ := Metric.mem_closure_iff.mp hφ ε hε
  obtain ⟨Q₁, Q₂, hQ⟩ := exists_polynomial_of_mem_span_fourier ψ hψ
  refine ⟨Q₁ + Q₂, fun z hz => ?_⟩
  -- a parameter for the point `z`
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, circleMap a r θ = z := by
    have : z ∈ Set.range (circleMap a r) := by rw [range_circleMap, abs_of_pos hr]; exact hz
    exact this
  set x : AddCircle (2 * π) := (θ : AddCircle (2 * π)) with hx
  have hex : e x = z := by
    rw [← hθ]
    simp only [e, hx, AddCircle.toCircle_apply_mk, Circle.coe_exp, circleMap]
    congr 3
    field_simp
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hz' : (z - a) / r = (AddCircle.toCircle x : ℂ) := by
    rw [← hex]
    simp only [e]
    rw [add_sub_cancel_left, mul_div_cancel_left₀ _ hr']
  have hre : (ψ x).re = ((Q₁ + Q₂).eval ((z - a) / r)).re := by
    rw [hQ x, hz', Polynomial.eval_add, Complex.add_re, Complex.add_re, Complex.conj_re]
  have h1 : v z = (φ x).re := by simp [φ, hex]
  rw [h1, ← hre]
  have := (ContinuousMap.dist_lt_iff hε).mp hdist x
  rw [dist_eq_norm] at this
  calc |(φ x).re - (ψ x).re| = |(φ x - ψ x).re| := by rw [Complex.sub_re]
    _ ≤ ‖φ x - ψ x‖ := Complex.abs_re_le_norm _
    _ < ε := this

/-- The real part of a polynomial in the normalized circle variable has circle average equal to its
value at the center. -/
theorem circleAverage_re_polynomial (Q : Polynomial ℂ) (a : ℂ) {r : ℝ} (hr : 0 < r) :
    circleAverage (fun z => (Q.eval ((z - a) / r)).re) a r = (Q.eval 0).re := by
  have hd : Differentiable ℂ fun z : ℂ => Q.eval ((z - a) / r) :=
    Q.differentiable.comp (by fun_prop)
  have hcl : DiffContOnCl ℂ (fun z : ℂ => Q.eval ((z - a) / r)) (ball a |r|) :=
    hd.diffContOnCl
  have hint : CircleIntegrable (fun z : ℂ => Q.eval ((z - a) / r)) a r :=
    hd.continuous.continuousOn.circleIntegrable hr.le
  have := Complex.reCLM.circleAverage_comp_comm (f := fun z : ℂ => Q.eval ((z - a) / r))
    (c := a) (R := r) hint
  simp only [Function.comp_def, Complex.reCLM_apply] at this
  rw [this, hcl.circleAverage]
  simp

/-- **Harmonic-majorant criterion.** A function continuous on a circle whose center value is
dominated by the center value of every harmonic polynomial majorant on the circle satisfies
the submean inequality. -/
theorem le_circleAverage_of_forall_polynomial_majorant {v : ℂ → ℝ} {a : ℂ} {r : ℝ} (hr : 0 < r)
    (hv : ContinuousOn v (sphere a r))
    (h : ∀ Q : Polynomial ℂ, (∀ z ∈ sphere a r, v z ≤ (Q.eval ((z - a) / r)).re) →
      v a ≤ (Q.eval 0).re) :
    v a ≤ circleAverage v a r := by
  have hint : CircleIntegrable v a r := hv.circleIntegrable hr.le
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨Q, hQ⟩ := exists_polynomial_re_approx hr hv (half_pos hε)
  have hQre : ∀ z, ((Q + Polynomial.C (ε / 2 : ℂ)).eval ((z - a) / r)).re =
      (Q.eval ((z - a) / r)).re + ε / 2 := fun z => by
    simp [Polynomial.eval_add]
  have hmaj : ∀ z ∈ sphere a r, v z ≤ ((Q + Polynomial.C (ε / 2 : ℂ)).eval ((z - a) / r)).re := by
    intro z hz
    rw [hQre]
    linarith [(abs_lt.mp (hQ z hz)).2]
  have h1 := h _ hmaj
  rw [Polynomial.eval_add, Polynomial.eval_C, Complex.add_re] at h1
  have hcont : ContinuousOn (fun z => (Q.eval ((z - a) / r)).re) (sphere a r) :=
    (Complex.continuous_re.comp (Q.differentiable.comp (by fun_prop)).continuous).continuousOn
  have h2 : circleAverage (fun z => (Q.eval ((z - a) / r)).re) a r ≤
      circleAverage (fun z => v z + ε / 2) a r := by
    refine circleAverage_mono (hcont.circleIntegrable hr.le)
      (hint.add (circleIntegrable_const _ a r)) fun z hz => ?_
    have := (abs_lt.mp (hQ z (by simpa [abs_of_pos hr] using hz))).1
    linarith
  rw [circleAverage_re_polynomial Q a hr] at h2
  rw [circleAverage_fun_add hint (circleIntegrable_const _ a r), circleAverage_const] at h2
  have h3 : ((ε / 2 : ℂ)).re = ε / 2 := by simp
  linarith

/-- **Submean inequality on closed discs.** A continuous subharmonic function satisfies the
submean inequality on every closed disc contained in its domain. -/
theorem SubharmonicOn.le_circleAverage_of_continuousOn {u : ℂ → ℝ} {U : Set ℂ}
    (hu : SubharmonicOn u U) (hc : ContinuousOn u U) {a : ℂ} {r : ℝ} (hr : 0 < r)
    (hsub : closedBall a r ⊆ U) : u a ≤ circleAverage u a r := by
  refine le_circleAverage_of_forall_polynomial_majorant hr
    (hc.mono (sphere_subset_closedBall.trans hsub)) fun Q hQ => ?_
  have hQan : AnalyticOnNhd ℂ (fun z : ℂ => Q.eval ((z - a) / r)) (ball a r) :=
    fun z _ => (Q.differentiable.comp (by fun_prop)).analyticAt z
  have hw : SubharmonicOn (fun z => u z + -(Q.eval ((z - a) / r)).re) (ball a r) :=
    (hu.mono (ball_subset_closedBall.trans hsub)).add
      (AnalyticOnNhd.subharmonicOn_neg_re hQan)
  have husc : UpperSemicontinuousOn (fun z => u z + -(Q.eval ((z - a) / r)).re)
      (closedBall a r) :=
    ((hc.mono hsub).add (Complex.continuous_re.comp
      (Q.differentiable.comp (by fun_prop)).continuous).continuousOn.neg).upperSemicontinuousOn
  have := hw.le_of_le_sphere hr husc (M := 0) (fun z hz => by linarith [hQ z hz]) a
    (mem_closedBall_self hr.le)
  have h0 : ((a - a) / r) = 0 := by simp
  rw [h0] at this
  linarith

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
