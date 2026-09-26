/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.Reinhardt

/-!
# Domains of absolute convergence of multivariable power series

For coefficients indexed by Mathlib's finitely supported multi-indices, the absolute convergence
set records summability of the norms of the individual monomial terms. Its interior is the
convergence domain, following [Boas][Boas2013] (2013), Sections 2.1--2.2. Boundary convergence
is deliberately not included in the definition of the domain.

The absolute-convergence set and its interior are complete Reinhardt and logarithmically convex.
The proofs apply to normed-group-valued coefficients; a complex Banach target is needed only to
deduce summability of the actual vector-valued terms. Convexity follows by comparing terms at
logarithmic interpolates with arithmetic averages, using convexity of exp.

The existence converse is proved in `SeveralComplexVariables.PowerSeriesConvergence`. Empty
coordinate index types are included; nonemptiness is required of a prescribed domain, but a
general series may have empty convergence domain.

## Main definitions

* `powerSeriesAbsConvergenceSet`: The absolute-convergence set of a power series centred at zero.
* `powerSeriesConvergenceDomain`: The convergence domain is the interior of the absolute-convergence
  set.

## Main results

* `isOpen_powerSeriesConvergenceDomain`: A power-series convergence domain is open by definition,
  and may be empty.
* `isCompleteReinhardt_powerSeriesConvergenceDomain`: The convergence domain is complete Reinhardt,
  including at coordinate hyperplanes.
* `isLogarithmicallyConvex_powerSeriesConvergenceDomain`: The interior of the absolute-convergence
  set is logarithmically convex.
* `isPathConnected_powerSeriesConvergenceDomain`: A nonempty convergence domain is path connected.

## References

* [H. P. Boas, *Lecture Notes on Several Complex Variables*][Boas2013]
-/

public noncomputable section

open Set
open scoped BigOperators

namespace SeveralComplexVariables

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]

/-- The absolute-convergence set of a power series centred at zero. The product records the norm of
the monomial, so no scalar action or completeness of the coefficient space is needed. -/
@[expose] def powerSeriesAbsConvergenceSet (c : MvPowerSeries ι E) : Set (ι → ℂ) :=
  {z | Summable (fun m : ι →₀ ℕ => ‖c m‖ * ∏ i, ‖z i‖ ^ m i)}

/-- The convergence domain is the interior of the absolute-convergence set. -/
@[expose] def powerSeriesConvergenceDomain (c : MvPowerSeries ι E) : Set (ι → ℂ) :=
  interior (powerSeriesAbsConvergenceSet c)

/-- For complex normed coefficients the defining summability condition is exactly absolute
convergence of the vector-valued monomial terms. -/
theorem mem_powerSeriesAbsConvergenceSet_iff [NormedSpace ℂ E]
    {c : MvPowerSeries ι E} {z : ι → ℂ} :
    z ∈ powerSeriesAbsConvergenceSet c ↔
      Summable (fun m : ι →₀ ℕ => ‖(∏ i, z i ^ m i) • c m‖) := by
  simp [powerSeriesAbsConvergenceSet, norm_smul, norm_prod, norm_pow, mul_comm]

/-- Every formal series converges absolutely at zero, since only its constant term survives. This
does not assert that its convergence domain is nonempty. -/
theorem zero_mem_powerSeriesAbsConvergenceSet (c : MvPowerSeries ι E) :
    0 ∈ powerSeriesAbsConvergenceSet c := by
  classical
  apply summable_of_ne_finset_zero (s := {0})
  intro m hm
  have hm0 : m ≠ 0 := by simpa using hm
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hm0
  have hterm : ‖(0 : ι → ℂ) i‖ ^ m i = 0 := by
    simpa using (zero_pow hi : (0 : ℝ) ^ m i = 0)
  rw [Finset.prod_eq_zero (Finset.mem_univ i) hterm, mul_zero]

/-- A power-series convergence domain is open by definition, and may be empty. -/
theorem isOpen_powerSeriesConvergenceDomain (c : MvPowerSeries ι E) :
    IsOpen (powerSeriesConvergenceDomain c) := isOpen_interior

/-- Membership of the convergence domain implies absolute convergence. -/
theorem powerSeriesConvergenceDomain_subset (c : MvPowerSeries ι E) :
    powerSeriesConvergenceDomain c ⊆ powerSeriesAbsConvergenceSet c := interior_subset

/-- Decreasing coordinate moduli preserves absolute convergence. -/
theorem isCompleteReinhardt_powerSeriesAbsConvergenceSet (c : MvPowerSeries ι E) :
    IsCompleteReinhardt (powerSeriesAbsConvergenceSet c) := by
  intro z hz w hw
  apply hz.of_nonneg_of_le
  · intro m
    positivity
  · intro m
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact Finset.prod_le_prod₀ (fun i _ => by positivity)
      (fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hw i) _)

/-- The convergence domain is complete Reinhardt, including at coordinate hyperplanes. -/
theorem isCompleteReinhardt_powerSeriesConvergenceDomain (c : MvPowerSeries ι E) :
    IsCompleteReinhardt (powerSeriesConvergenceDomain c) :=
  (isCompleteReinhardt_powerSeriesAbsConvergenceSet c).interior

/-- A power-series convergence domain has independent coordinate rotation symmetry. -/
theorem isReinhardt_powerSeriesConvergenceDomain (c : MvPowerSeries ι E) :
    IsReinhardt (powerSeriesConvergenceDomain c) :=
  (isCompleteReinhardt_powerSeriesConvergenceDomain c).isReinhardt

/-- A nonempty convergence domain is path connected. -/
theorem isPathConnected_powerSeriesConvergenceDomain (c : MvPowerSeries ι E)
    (hne : (powerSeriesConvergenceDomain c).Nonempty) :
    IsPathConnected (powerSeriesConvergenceDomain c) :=
  (isCompleteReinhardt_powerSeriesConvergenceDomain c).isPathConnected hne

/-- In logarithmic coordinates the modulus of a monomial is an exponential of a linear form. -/
theorem prod_norm_exp_pow (x : ι → ℝ) (m : ι →₀ ℕ) :
    (∏ i, ‖(Real.exp (x i) : ℂ)‖ ^ m i) = Real.exp (∑ i, (m i : ℝ) * x i) := by
  simp [Real.exp_sum, Real.exp_nat_mul]

/-- Absolute convergence has a convex logarithmic image, by termwise convexity of exp and comparison
of nonnegative series. -/
theorem isLogarithmicallyConvex_powerSeriesAbsConvergenceSet (c : MvPowerSeries ι E) :
    IsLogarithmicallyConvex (powerSeriesAbsConvergenceSet c) := by
  intro x hx y hy a b ha hb hab
  change Summable (fun m : ι →₀ ℕ =>
    ‖c m‖ * ∏ i, ‖(Real.exp ((a • x + b • y) i) : ℂ)‖ ^ m i)
  have hx' : Summable (fun m : ι →₀ ℕ => ‖c m‖ * Real.exp (∑ i, (m i : ℝ) * x i)) := by
    simpa only [logarithmicImage, mem_ofPred_eq, powerSeriesAbsConvergenceSet,
      prod_norm_exp_pow] using hx
  have hy' : Summable (fun m : ι →₀ ℕ => ‖c m‖ * Real.exp (∑ i, (m i : ℝ) * y i)) := by
    simpa only [logarithmicImage, mem_ofPred_eq, powerSeriesAbsConvergenceSet,
      prod_norm_exp_pow] using hy
  apply ((hx'.mul_left a).add (hy'.mul_left b)).of_nonneg_of_le
  · intro m
    positivity
  · intro m
    rw [prod_norm_exp_pow]
    have heq : (∑ i, (m i : ℝ) * (a • x + b • y) i) =
        a * (∑ i, (m i : ℝ) * x i) + b * (∑ i, (m i : ℝ) * y i) := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add,
        Finset.sum_add_distrib, Finset.mul_sum]
      congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> ring
    rw [heq]
    have h := mul_le_mul_of_nonneg_left
      (convexOn_exp.2 (mem_univ (∑ i, (m i : ℝ) * x i))
        (mem_univ (∑ i, (m i : ℝ) * y i)) ha hb hab) (norm_nonneg (c m))
    simpa only [smul_eq_mul, mul_add, mul_left_comm] using h

/-- The interior of the absolute-convergence set is logarithmically convex. -/
theorem isLogarithmicallyConvex_powerSeriesConvergenceDomain (c : MvPowerSeries ι E) :
    IsLogarithmicallyConvex (powerSeriesConvergenceDomain c) :=
  (isLogarithmicallyConvex_powerSeriesAbsConvergenceSet c).interior
    (isCompleteReinhardt_powerSeriesAbsConvergenceSet c)

/-- Absolute convergence implies summability of the vector-valued monomial terms in a complex Banach
space. -/
theorem summable_powerSeriesTerms [NormedSpace ℂ E] [CompleteSpace E]
    {c : MvPowerSeries ι E} {z : ι → ℂ} (hz : z ∈ powerSeriesAbsConvergenceSet c) :
    Summable (fun m : ι →₀ ℕ => (∏ i, z i ^ m i) • c m) := by
  apply hz.of_norm_bounded
  intro m
  simp [norm_smul, norm_prod, norm_pow, mul_comm]

/-- The zero series has the whole coordinate space as its convergence domain. -/
@[simp] theorem powerSeriesConvergenceDomain_zero :
    powerSeriesConvergenceDomain (0 : MvPowerSeries ι E) = univ := by
  have hz (m : ι →₀ ℕ) : (0 : MvPowerSeries ι E) m = 0 := rfl
  simp [powerSeriesConvergenceDomain, powerSeriesAbsConvergenceSet, hz]

/-- With no coordinates, every series has the whole singleton coordinate space as its convergence
domain. -/
theorem powerSeriesConvergenceDomain_of_isEmpty [IsEmpty ι] (c : MvPowerSeries ι E) :
    powerSeriesConvergenceDomain c = univ := by
  have h : powerSeriesAbsConvergenceSet c = univ := by
    apply Set.eq_univ_of_forall
    intro z
    exact Summable.of_finite
  simp [powerSeriesConvergenceDomain, h]

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
