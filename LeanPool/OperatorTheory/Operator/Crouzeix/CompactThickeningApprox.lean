/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

import LeanPool.OperatorTheory.Operator.Crouzeix.SmoothApprox

/-!
# Compact metric-thickening approximations

The open thickenings in `SmoothApprox.lean` supply the convex domains used by
the analytic argument.  At the same radii, their closed metric thickenings
form a decreasing compact exhaustion and contain the corresponding domain
frontiers.  These are the compact control sets used by the limiting Palencia
assembly.

## Main declarations

* `compactThickeningApprox` -- the closed thickening at radius `1 / (n + 1)`.
* `compactThickeningApprox_infinite` -- every stage over a nonempty set is
  infinite.
* `compactThickeningApprox_spec` -- antitonicity, compactness, nonemptiness,
  and exact intersection of the compact exhaustion.
* `frontier_convexThickeningApprox_subset_compactThickeningApprox` -- the
  open-stage frontier lies in the compact control set at the same radius.
-/

open Metric Set

private theorem smoothApproxRadius_pos_compact (n : ℕ) : 0 < smoothApproxRadius n := by
  unfold smoothApproxRadius
  positivity

private theorem smoothApproxRadius_antitone : Antitone smoothApproxRadius := by
  intro m n hmn
  unfold smoothApproxRadius
  apply one_div_le_one_div_of_le
  · positivity
  · exact_mod_cast Nat.add_le_add_right hmn 1

/-- The closed metric thickening of `K` at radius `1 / (n + 1)`. -/
noncomputable def compactThickeningApprox (K : Set ℂ) (n : ℕ) : Set ℂ :=
  Metric.cthickening (smoothApproxRadius n) K

/-- A closed thickening of a nonempty planar set at the positive approximation
radius contains a nondegenerate closed disk, hence is infinite. -/
theorem compactThickeningApprox_infinite (K : Set ℂ) (n : ℕ)
    (hnonempty : K.Nonempty) : (compactThickeningApprox K n).Infinite := by
  obtain ⟨z, hz⟩ := hnonempty
  have hball : (Metric.closedBall z (smoothApproxRadius n)).Infinite := by
    have hopen : (Metric.ball z (smoothApproxRadius n)).Infinite := by
      apply Set.Infinite.of_accPt
      exact Metric.isOpen_ball.preperfect z
        (Metric.mem_ball_self (smoothApproxRadius_pos_compact n))
    exact hopen.mono Metric.ball_subset_closedBall
  apply hball.mono
  unfold compactThickeningApprox
  exact Metric.closedBall_subset_cthickening hz _

/-- Closed thickenings of a nonempty compact planar set form an antitone
sequence of nonempty compact sets whose intersection is exactly the set. -/
theorem compactThickeningApprox_spec (K : Set ℂ) (hcompact : IsCompact K)
    (hnonempty : K.Nonempty) :
    Antitone (compactThickeningApprox K) ∧
      (∀ n, IsCompact (compactThickeningApprox K n)) ∧
      (∀ n, (compactThickeningApprox K n).Nonempty) ∧
      (⋂ n, compactThickeningApprox K n) = K := by
  have hanti : Antitone (compactThickeningApprox K) := by
    intro m n hmn
    exact Metric.cthickening_mono (smoothApproxRadius_antitone hmn) K
  have hstageCompact : ∀ n, IsCompact (compactThickeningApprox K n) :=
    fun _ ↦ hcompact.cthickening
  have hstageNonempty : ∀ n, (compactThickeningApprox K n).Nonempty :=
    fun n ↦ hnonempty.mono
      (Metric.self_subset_cthickening (E := K) (δ := smoothApproxRadius n))
  let radii : Set ℝ := Set.range smoothApproxRadius
  have hradii_small : ∀ ε, 0 < ε → (radii ∩ Set.Ioc 0 ε).Nonempty := by
    intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    refine ⟨smoothApproxRadius n, ⟨⟨n, rfl⟩, ?_⟩⟩
    exact ⟨smoothApproxRadius_pos_compact n, hn.le⟩
  have hclosure := Metric.closure_eq_iInter_cthickening' K radii hradii_small
  rw [hcompact.isClosed.closure_eq] at hclosure
  refine ⟨hanti, hstageCompact, hstageNonempty, ?_⟩
  calc
    (⋂ n, compactThickeningApprox K n) =
        ⋂ δ ∈ radii, Metric.cthickening δ K := by
      ext x
      simp only [Set.mem_iInter, compactThickeningApprox]
      constructor
      · intro hx δ hδ
        obtain ⟨n, rfl⟩ := hδ
        exact hx n
      · intro hx n
        exact hx (smoothApproxRadius n) ⟨n, rfl⟩
    _ = K := hclosure.symm

/-- The frontier of the open thickening at stage `n` lies in the closed
thickening at the same radius. -/
theorem frontier_convexThickeningApprox_subset_compactThickeningApprox
    (K : Set ℂ) (n : ℕ) :
    frontier (convexThickeningApprox K n) ⊆ compactThickeningApprox K n := by
  exact frontier_subset_closure.trans
    (Metric.closure_thickening_subset_cthickening (smoothApproxRadius n) K)

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
