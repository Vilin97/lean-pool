/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.CarlsonFunctions.Carlson.R.ZeroParameter
public import LeanPool.CarlsonFunctions.Carlson.R.Relations
public import LeanPool.CarlsonFunctions.Dirichlet.Average.ContinuedRelations
public import LeanPool.CarlsonFunctions.Carlson.R.EulerTransform

/-!
# Reduction of integral Dirichlet parameters

This is the first reduction in Carlson's Section 8.5. A parameter `-N` can
be removed, leaving at most `N + 1` functions of one fewer variable. Their
exponents are `t, t-1, ..., t-N`; the coefficients are polynomials in the
removed node. All remaining parameters and the exponent are unrestricted.

The lowering relation 8.5(1) is also proved in a form without division, valid
at every complex parameter and for coincident nodes as well.

Euler's transformation supplies the complementary terminating case: a polynomial
in reciprocal nodes times powers. For integral parameters this is an explicit
rational expression.

This reduction does not yet classify all integral or half-integral parameter
configurations in terms of elementary functions.
-/

open Complex Polynomial ProbabilityTheory
@[expose] public noncomputable section
namespace DirichletTransform
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- A nonpositive integral parameter can be removed with polynomial coefficients,
uniformly in the nodes. This is the raising-and-deletion step in Theorems 8.5-1
and 8.5-3, on the entire regularized parameter domain. -/
theorem exists_polynomial_regCarlsonRContinued_option_neg_nat (N : ℕ) (t : ℂ)
    {b : Option ι → ℂ} (hb : b none = -(N : ℂ)) :
    ∃ p : Fin (N + 1) → ℂ[X], ∀ (z : Option ι → ℂ) (hz : z ∈ carlsonRVariableDomain),
      regCarlsonRContinued t z hz b =
        ∑ j, (p j).eval (z none) *
          regCarlsonRContinued (t - (j : ℕ)) (z ∘ some)
            (fun i => hz (some i)) (b ∘ some) := by
  induction N generalizing t b with
  | zero =>
    refine ⟨fun _ => 1, fun z hz => ?_⟩
    simpa using regCarlsonRContinued_option_zero t (by simpa using hb) hz
  | succ N ih =>
    let : DecidableEq (Option ι) := Classical.decEq _
    let b' := addDirichletUnit b none
    have hb' : b' none = -(N : ℂ) := by
      simp only [b', addDirichletUnit, Function.update_self, hb, Nat.cast_succ]
      ring
    have hsome : b' ∘ some = b ∘ some := by
      ext i
      simp [b', addDirichletUnit]
    obtain ⟨p, hp⟩ := ih t hb'
    obtain ⟨q, hq⟩ := ih (t - 1) hb'
    let c : ℂ := ∑ i, b i
    let p₀ : Fin (N + 2) → ℂ[X] := Fin.snoc p 0
    let q₀ : Fin (N + 2) → ℂ[X] := Fin.cons 0 q
    refine ⟨fun j => C (c + t) * p₀ j - C t * X * q₀ j, ?_⟩
    intro z hz
    have hp' := hp z hz
    have hq' := hq z hz
    rw [hsome] at hp' hq'
    have hraise := regCarlsonRContinued_eq_addDirichletUnit t b hz none
    change regCarlsonRContinued t z hz b =
      (c + t) * regCarlsonRContinued t z hz b' -
        t * z none * regCarlsonRContinued (t - 1) z hz b' at hraise
    rw [hraise, hp', hq']
    simp only [p₀, q₀, eval_sub, eval_mul, eval_C, eval_X, sub_mul, Finset.sum_sub_distrib]
    congr 1
    · conv_rhs => rw [Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, eval_zero,
        mul_zero, zero_mul, add_zero, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    · conv_rhs => rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, Fin.val_succ, eval_zero,
        mul_zero, zero_mul, zero_add, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [show t - ((j : ℕ) + 1 : ℕ) = t - 1 - (j : ℕ) by push_cast; ring]
      ring

/-- Explicit removal of the parameter `-1`, the first nontrivial case of the
finite reduction in Section 8.5. No division or node-distinctness is required. -/
theorem regCarlsonRContinued_option_neg_one (t : ℂ)
    {b : Option ι → ℂ} (hb : b none = -1)
    {z : Option ι → ℂ} (hz : z ∈ carlsonRVariableDomain) :
    regCarlsonRContinued t z hz b =
      ((∑ i, b i) + t) *
        regCarlsonRContinued t (z ∘ some) (fun i => hz (some i)) (b ∘ some) -
      t * z none *
        regCarlsonRContinued (t - 1) (z ∘ some) (fun i => hz (some i)) (b ∘ some) := by
  let : DecidableEq (Option ι) := Classical.decEq _
  have hzero : addDirichletUnit b none none = 0 := by simp [addDirichletUnit, hb]
  have hsome : addDirichletUnit b none ∘ some = b ∘ some := by
    ext i
    simp [addDirichletUnit]
  rw [regCarlsonRContinued_eq_addDirichletUnit t b hz none,
    regCarlsonRContinued_option_zero t hzero hz,
    regCarlsonRContinued_option_zero (t - 1) hzero hz, hsome]

omit [Nonempty ι] in
open scoped Classical in
/-- Carlson's lowering relation 8.5(1), in pole-free regularized form. It is
valid even at `a = 1` and coincident nodes, though solving for the left-hand
function then requires the usual nonvanishing hypotheses. -/
theorem regCarlsonRContinued_lower (a : ℂ) (b : ι → ℂ)
    {z : ι → ℂ} (hz : z ∈ carlsonRVariableDomain) (i j : ι) :
    (a - 1) * (z i - z j) * regCarlsonRContinued (-a) z hz b =
      regCarlsonRContinued (1 - a) z hz (b - Pi.single i 1) -
        regCarlsonRContinued (1 - a) z hz (b - Pi.single j 1) := by
  have hf : AnalyticOnNhd ℂ (fun w : ℂ => w ^ (1 - a)) carlsonRightHalfPlane := by
    intro w hw
    rw [analyticAt_iff_eventually_differentiableAt]
    filter_upwards [isOpen_slitPlane.eventually_mem
      (carlsonRightHalfPlane_subset_slitPlane hw)] with v hv
    exact differentiableAt_id.cpow_const hv
  have hD : IsRegCarlsonContinuation (deriv (fun w : ℂ => w ^ (1 - a))) z
      (fun c => (1 - a) * regCarlsonRContinued (-a) z hz c) := by
    refine ⟨analyticOnNhd_const.mul (analyticOnNhd_regCarlsonRContinued (-a) hz), ?_⟩
    intro c hc
    dsimp only
    rw [regCarlsonRContinued_eq_integral (-a) hz hc]
    rw [regCarlsonRIntegral, ← regCarlsonDirichletAverage_const_mul]
    apply regDirichletIntegral_congr
    intro u hu
    dsimp only
    rw [Complex.deriv_cpow_const (carlsonAffineForm_mem_slitPlane hz hu)]
    congr 2
    ring
  have h := IsRegCarlsonContinuation.tangent_sub convex_carlsonRightHalfPlane hf
    (Set.range_subset_iff.mpr hz) (isRegCarlsonRContinuation_continued (1 - a) hz) hD b i j
  linear_combination -h

omit [Nonempty ι] in
/-- If the complementary exponent is a nonpositive integer, Euler's
transformation reduces the function to a polynomial in reciprocal nodes times
complex powers. This is the second terminating case used in Section 8.5. -/
theorem regCarlsonRContinued_neg_sum_sub_nat (N : ℕ) (b : ι → ℂ)
    {z : ι → ℂ} (hz : z ∈ carlsonRVariableDomain) :
    regCarlsonRContinued (-(∑ i, b i) - N) z hz b =
      (∏ i, z i ^ (-b i)) * regCarlsonR N (fun i => (z i)⁻¹) b := by
  rw [regCarlsonRContinued_euler,
    show -(∑ i, b i) - (-(∑ i, b i) - N) = (N : ℂ) by ring,
    regCarlsonRContinued_natCast]

omit [Nonempty ι] in
/-- For integral Dirichlet parameters the complementary terminating case is
explicitly rational in the nodes: integer powers times a polynomial in their
reciprocals. Negative and zero Dirichlet parameters are allowed. -/
theorem regCarlsonRContinued_neg_sum_sub_nat_int (N : ℕ) (m : ι → ℤ)
    {z : ι → ℂ} (hz : z ∈ carlsonRVariableDomain) :
    regCarlsonRContinued (-(∑ i, (m i : ℂ)) - N) z hz (fun i => m i) =
      (∏ i, z i ^ (-m i)) * regCarlsonR N (fun i => (z i)⁻¹) (fun i => m i) := by
  rw [regCarlsonRContinued_neg_sum_sub_nat]
  simp only [← Int.cast_neg, cpow_intCast]

end DirichletTransform
end
