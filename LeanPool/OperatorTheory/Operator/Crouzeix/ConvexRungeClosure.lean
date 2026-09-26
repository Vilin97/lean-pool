/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
module


public import LeanPool.OperatorTheory.Operator.Crouzeix.ConvexRungeFinite
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# Closure of convex Runge kernel approximations

Finite Cauchy-kernel quadrature approximations naturally produce a sequence
of functions, each of which is itself a compact-uniform polynomial limit.
This file diagonalizes those iterated limits.  Combined with finite exterior
Cauchy-kernel approximation, it turns uniform approximation by quadrature
sums into uniform approximation by one polynomial sequence.
-/

@[expose] public section

open Filter Polynomial Set
open scoped Topology

/-- A uniform limit of uniform polynomial limits admits one polynomial approximating sequence. -/
theorem exists_polynomial_tendstoUniformlyOn_of_iterated_limits
    (K : Set ℂ) (f : ℂ → ℂ) (g : ℕ → ℂ → ℂ)
    (hg : TendstoUniformlyOn g f atTop K)
    (hpoly : ∀ n, ∃ q : ℕ → Polynomial ℂ,
      TendstoUniformlyOn (fun j z => Polynomial.eval z (q j))
        (g n) atTop K) :
    ∃ q : ℕ → Polynomial ℂ,
      TendstoUniformlyOn (fun n z => Polynomial.eval z (q n))
        f atTop K := by
  choose q hq using hpoly
  have hevent : ∀ n : ℕ, ∀ᶠ j in atTop,
      ∀ z ∈ K, dist (g n z) (Polynomial.eval z (q n j)) <
        1 / ((n : ℝ) + 1) := by
    intro n
    apply (Metric.tendstoUniformlyOn_iff.mp (hq n))
    positivity
  choose N hN using fun n => eventually_atTop.1 (hevent n)
  refine ⟨fun n => q n (N n), ?_⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hg_event : ∀ᶠ n in atTop,
      ∀ z ∈ K, dist (f z) (g n z) < ε / 2 :=
    (Metric.tendstoUniformlyOn_iff.mp hg) (ε / 2) (by positivity)
  have hrate : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hrate_event : ∀ᶠ (n : ℕ) in atTop,
      1 / ((n : ℝ) + 1) < ε / 2 :=
    hrate.eventually (gt_mem_nhds (by positivity))
  filter_upwards [hg_event, hrate_event] with n hgn hn z hz
  calc
    dist (f z) (Polynomial.eval z (q n (N n))) ≤
        dist (f z) (g n z) +
          dist (g n z) (Polynomial.eval z (q n (N n))) :=
      dist_triangle _ _ _
    _ < ε / 2 + ε / 2 :=
      add_lt_add (hgn z hz) ((hN n (N n) le_rfl z hz).trans hn)
    _ = ε := by ring

/-- A compact-uniform limit of finite exterior Cauchy-kernel sums on a compact
convex planar set is itself a compact-uniform limit of polynomials. -/
theorem exists_polynomial_tendstoUniformlyOn_of_tendstoUniformlyOn_cauchyKernel_finset
    (K : Set ℂ) (hK : IsCompact K) (hconvex : Convex ℝ K)
    (poles : ℕ → Finset ℂ) (coeff : ℕ → ℂ → ℂ)
    (hpoles : ∀ n ζ, ζ ∈ poles n → ζ ∉ K) {f : ℂ → ℂ}
    (hlim : TendstoUniformlyOn
      (fun n z ↦ ∑ ζ ∈ poles n, coeff n ζ * (ζ - z)⁻¹)
      f atTop K) :
    ∃ q : ℕ → Polynomial ℂ,
      TendstoUniformlyOn (fun n z ↦ Polynomial.eval z (q n))
        f atTop K := by
  classical
  apply exists_polynomial_tendstoUniformlyOn_of_iterated_limits K f
    (fun n z ↦ ∑ ζ ∈ poles n, coeff n ζ * (ζ - z)⁻¹) hlim
  intro n
  exact
    exists_polynomial_tendstoUniformlyOn_sum_mul_inv_sub_of_isCompact_convex
      (poles n) (coeff n) id K hK hconvex (hpoles n)

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
