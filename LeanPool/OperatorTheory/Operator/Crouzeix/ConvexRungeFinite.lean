/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
/-
# Finite exterior-kernel sums on convex compact sets

This file synchronizes the exterior Cauchy-kernel approximants from
`ConvexRunge`: every finite complex linear combination of such kernels is a
compact-uniform limit of a single sequence of complex polynomials.  This is
the finite-quadrature closure step used in constructive Runge arguments.
-/
import LeanPool.OperatorTheory.Operator.Crouzeix.ConvexRunge
import Mathlib.Topology.Algebra.IsUniformGroup.Basic

open Complex Filter Set
open scoped Topology

private theorem tendstoUniformlyOn_finset_sum
    {ι : Type*} {s : Finset ι} {K : Set ℂ}
    (F : s → ℕ → ℂ → ℂ) (g : s → ℂ → ℂ)
    (hF : ∀ i : s, TendstoUniformlyOn (F i) (g i) atTop K) :
    TendstoUniformlyOn
      (fun n z => ∑ i : s, F i n z)
      (fun z => ∑ i : s, g i z) atTop K := by
  classical
  have hsum : ∀ t : Finset s,
      TendstoUniformlyOn
        (fun n z => ∑ i ∈ t, F i n z)
        (fun z => ∑ i ∈ t, g i z) atTop K := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
        have hzero : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0) :=
          tendsto_const_nhds
        simpa only [Finset.sum_empty] using
          hzero.tendstoUniformlyOn_const K
    | @insert i t hi hind =>
        simp_rw [Finset.sum_insert hi]
        change TendstoUniformlyOn
          (F i + fun n z => ∑ i ∈ t, F i n z)
          (g i + fun z => ∑ i ∈ t, g i z) atTop K
        exact (hF i).add hind
  simpa only [Finset.sum_filter, Finset.mem_univ, ↓reduceIte] using
    hsum Finset.univ

/-- A finite complex linear combination of Cauchy kernels with poles outside
a compact convex planar set is a compact-uniform limit of polynomials. -/
theorem exists_polynomial_tendstoUniformlyOn_sum_mul_inv_sub_of_isCompact_convex
    {ι : Type*} (s : Finset ι) (coeff pole : ι → ℂ)
    (K : Set ℂ) (hK : IsCompact K) (hconvex : Convex ℝ K)
    (hpole : ∀ i ∈ s, pole i ∉ K) :
    ∃ q : ℕ → Polynomial ℂ,
      TendstoUniformlyOn
        (fun n z => Polynomial.eval z (q n))
        (fun z => ∑ i ∈ s, coeff i * (pole i - z)⁻¹) atTop K := by
  classical
  have hexists : ∀ i : s, ∃ q : ℕ → Polynomial ℂ,
      TendstoUniformlyOn
        (fun n z => Polynomial.eval z (q n))
        (fun z => (pole i - z)⁻¹) atTop K := by
    intro i
    exact exists_polynomial_tendstoUniformlyOn_inv_sub_of_isCompact_convex
      K hK hconvex (hpole i i.property)
  choose q hq using hexists
  let Q : ℕ → Polynomial ℂ := fun n =>
    ∑ i : s, Polynomial.C (coeff i) * q i n
  have hweighted (i : s) : TendstoUniformlyOn
      (fun n z => coeff i * Polynomial.eval z (q i n))
      (fun z => coeff i * (pole i - z)⁻¹) atTop K := by
    let L : ℂ →L[ℂ] ℂ := ContinuousLinearMap.mul ℂ ℂ (coeff i)
    have hL := L.uniformContinuous.comp_tendstoUniformlyOn (hq i)
    change TendstoUniformlyOn
      (fun n z => L (Polynomial.eval z (q i n)))
      (fun z => L ((pole i - z)⁻¹)) atTop K at hL
    simpa only [L, ContinuousLinearMap.mul_apply'] using hL
  have hsum := tendstoUniformlyOn_finset_sum
    (fun i n z => coeff i * Polynomial.eval z (q i n))
    (fun i z => coeff i * (pole i - z)⁻¹) hweighted
  refine ⟨Q, ?_⟩
  have htarget (z : ℂ) :
      (∑ i : s, coeff i * (pole i - z)⁻¹) =
        ∑ i ∈ s, coeff i * (pole i - z)⁻¹ := by
    exact Finset.sum_attach s (fun i => coeff i * (pole i - z)⁻¹)
  have hsum_target := hsum.congr_right (fun z _hz => htarget z)
  apply hsum_target.congr
  filter_upwards [] with n
  intro z _hz
  dsimp only [Q]
  rw [Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Polynomial.eval_mul, Polynomial.eval_C]

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
