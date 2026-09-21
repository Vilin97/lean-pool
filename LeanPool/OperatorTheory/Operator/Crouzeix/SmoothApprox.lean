/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
/-
# Smooth Jordan domains containing compact planar sets

This file supplies the first kernel-checked part of L4.2b.  It packages the
geometric data needed to integrate around the boundary of a smooth strictly
convex planar domain and proves that every compact set in `ℂ` is contained in
such a domain: take a sufficiently large open disk.

The stronger approximation needed by the full Crouzeix--Palencia argument --
a nested sequence of smooth domains whose intersection is the original compact
convex set -- is not asserted here.  In particular, the enclosing-disk theorem
must not be mistaken for that remaining planar approximation result.

The imports have separate roles: `Strict` supplies strict convexity of open
convex sets, `Ball.Pointwise` identifies closures of metric thickenings,
`RCLike.Real` identifies the frontier of a complex ball, and `CircleIntegral`
supplies the smooth regular circle parametrization API.
-/
import Mathlib.Analysis.Convex.Strict
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.MeasureTheory.Integral.CircleIntegral

open Complex Metric Set
open scoped ContDiff

/-- A smooth Jordan domain, represented by a `2π`-periodic regular boundary
parametrization.  Injectivity is imposed on the half-open fundamental interval
`[0, 2π)`, so the periodic identification of its two endpoints is the only
allowed repetition there. -/
structure SmoothJordanDomain where
  carrier : Set ℂ
  isOpen_carrier : IsOpen carrier
  strictConvex_carrier : StrictConvex ℝ carrier
  boundaryParam : ℝ → ℂ
  boundaryParam_periodic : Function.Periodic boundaryParam (2 * Real.pi)
  boundaryParam_contDiff : ContDiff ℝ ∞ boundaryParam
  boundaryParam_range : Set.range boundaryParam = frontier carrier
  boundaryParam_injOn : Set.InjOn boundaryParam (Set.Ico 0 (2 * Real.pi))
  boundaryParam_regular : ∀ t, deriv boundaryParam t ≠ 0

/-- A positive-radius open disk, with `circleMap` as its smooth Jordan boundary. -/
noncomputable def SmoothJordanDomain.ball (c : ℂ) (R : ℝ) (hR : 0 < R) :
    SmoothJordanDomain where
  carrier := Metric.ball c R
  isOpen_carrier := Metric.isOpen_ball
  strictConvex_carrier := (convex_ball c R).strictConvex_of_isOpen Metric.isOpen_ball
  boundaryParam := circleMap c R
  boundaryParam_periodic := periodic_circleMap c R
  boundaryParam_contDiff := contDiff_circleMap c R
  boundaryParam_range := by
    rw [range_circleMap, abs_of_pos hR, frontier_ball c hR.ne']
  boundaryParam_injOn := by
    apply injOn_circleMap_of_abs_sub_le' hR.ne'
    simp only [sub_zero]
    exact le_rfl
  boundaryParam_regular := fun _ => deriv_circleMap_ne_zero hR.ne'

/-- Every compact subset of `ℂ` lies in a smooth strictly convex Jordan domain.

This is the one-domain existence result consumed by the initial auxiliary
operator construction.  It does not provide the nested exhaustion whose
intersection is `K`. -/
theorem exists_smoothJordanDomain_superset_of_isCompact (K : Set ℂ) (hK : IsCompact K) :
    ∃ Ω : SmoothJordanDomain, K ⊆ Ω.carrier := by
  obtain ⟨R, hR, hsub⟩ := hK.isBounded.subset_ball_lt 0 0
  exact ⟨SmoothJordanDomain.ball 0 R hR, hsub⟩

/-- The positive radii `1, 1/2, 1/3, ...` used for the explicit thickening
approximation. -/
noncomputable def smoothApproxRadius (n : ℕ) : ℝ := 1 / (n + 1 : ℝ)

/-- The `n`th open metric thickening of `K`, at radius `1 / (n + 1)`. -/
noncomputable def convexThickeningApprox (K : Set ℂ) (n : ℕ) : Set ℂ :=
  Metric.thickening (smoothApproxRadius n) K

private theorem smoothApproxRadius_pos (n : ℕ) : 0 < smoothApproxRadius n := by
  unfold smoothApproxRadius
  positivity

/-- The closure of each later open thickening is contained in the preceding
open thickening.  Thus the explicit metric approximation has strict adjacent
nesting, not merely antitonicity. -/
theorem closure_convexThickeningApprox_succ_subset (K : Set ℂ) (n : ℕ) :
    closure (convexThickeningApprox K (n + 1)) ⊆
      convexThickeningApprox K n := by
  unfold convexThickeningApprox
  apply (Metric.closure_thickening_subset_cthickening
    (smoothApproxRadius (n + 1)) K).trans
  apply Metric.cthickening_subset_thickening'
  · exact smoothApproxRadius_pos n
  · unfold smoothApproxRadius
    exact Nat.one_div_lt_one_div (Nat.lt_succ_self n)

private theorem iInter_convexThickeningApprox (K : Set ℂ) (hK : IsClosed K) :
    (⋂ n, convexThickeningApprox K n) = K := by
  let radii : Set ℝ := Set.range smoothApproxRadius
  have hradii_pos : radii ⊆ Set.Ioi 0 := by
    rintro _ ⟨n, rfl⟩
    exact smoothApproxRadius_pos n
  have hradii_small : ∀ ε, 0 < ε → (radii ∩ Set.Ioc 0 ε).Nonempty := by
    intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    refine ⟨smoothApproxRadius n, ⟨⟨n, rfl⟩, ?_⟩⟩
    exact ⟨smoothApproxRadius_pos n, hn.le⟩
  have hclosure := Metric.closure_eq_iInter_thickening' K radii hradii_pos hradii_small
  rw [hK.closure_eq] at hclosure
  calc
    (⋂ n, convexThickeningApprox K n) =
        ⋂ δ ∈ radii, Metric.thickening δ K := by
      ext x
      simp only [Set.mem_iInter, convexThickeningApprox]
      constructor
      · intro hx δ hδ
        obtain ⟨n, rfl⟩ := hδ
        exact hx n
      · intro hx n
        exact hx (smoothApproxRadius n) ⟨n, rfl⟩
    _ = K := hclosure.symm

/-- A compact convex planar set is the exact intersection of an explicit
sequence of open strictly convex supersets.

This discharges the containment, convexity, openness, and intersection parts
of L4.2b.  The remaining gap is to replace or perturb these thickenings so
that every frontier has a smooth regular Jordan parametrization. -/
theorem convexThickeningApprox_spec (K : Set ℂ) (hcompact : IsCompact K)
    (hconvex : Convex ℝ K) :
    (∀ n, K ⊆ convexThickeningApprox K n ∧
      IsOpen (convexThickeningApprox K n) ∧
      StrictConvex ℝ (convexThickeningApprox K n)) ∧
      (⋂ n, convexThickeningApprox K n) = K := by
  constructor
  · intro n
    refine ⟨Metric.self_subset_thickening (smoothApproxRadius_pos n) K,
      Metric.isOpen_thickening, ?_⟩
    exact (hconvex.thickening (smoothApproxRadius n)).strictConvex_of_isOpen
      Metric.isOpen_thickening
  · exact iInter_convexThickeningApprox K hcompact.isClosed

/-- A sequence of smooth strictly convex Jordan domains that contains `K` at
every stage and has intersection exactly `K`.  Existence of this structure for
an arbitrary compact convex planar set is the remaining geometric content of
L4.2b. -/
structure SmoothConvexApproximation (K : Set ℂ) where
  domain : ℕ → SmoothJordanDomain
  subset_domain : ∀ n, K ⊆ (domain n).carrier
  iInter_domain : (⋂ n, (domain n).carrier) = K

/-- Closed disks admit a complete smooth convex approximation: enlarge the
radius by `1 / (n + 1)` and use the standard circle parametrization at every
stage.  This is the fully verified model case for the general L4.2b package. -/
noncomputable def smoothClosedBallApproximation (c : ℂ) (R : ℝ) (hR : 0 ≤ R) :
    SmoothConvexApproximation (Metric.closedBall c R) where
  domain n := SmoothJordanDomain.ball c (smoothApproxRadius n + R)
    (add_pos_of_pos_of_nonneg (smoothApproxRadius_pos n) hR)
  subset_domain n := by
    change Metric.closedBall c R ⊆ Metric.ball c (smoothApproxRadius n + R)
    apply Metric.closedBall_subset_ball
    linarith [smoothApproxRadius_pos n]
  iInter_domain := by
    have heq : ∀ n,
        (SmoothJordanDomain.ball c (smoothApproxRadius n + R)
          (add_pos_of_pos_of_nonneg (smoothApproxRadius_pos n) hR)).carrier =
          convexThickeningApprox (Metric.closedBall c R) n := by
      intro n
      change Metric.ball c (smoothApproxRadius n + R) =
        Metric.thickening (smoothApproxRadius n) (Metric.closedBall c R)
      exact (thickening_closedBall (smoothApproxRadius_pos n) hR c).symm
    simp_rw [heq]
    exact iInter_convexThickeningApprox _ Metric.isClosed_closedBall

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
