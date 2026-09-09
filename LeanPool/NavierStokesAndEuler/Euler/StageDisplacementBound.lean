/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Confinement by summable changes of particle labels

The packet construction composes particle maps as `Xₙ₊₁ = Xₙ ∘ Yₙ`.
Bounding the displacement of this composition costs the sum of the two
displacements, without a derivative bound on `Xₙ`. Consequently summable
changes of labels confine the images of every fixed initial ball uniformly
over all stages, including when the velocity gradients are unbounded.

The horizon predicate permits the time intervals to shrink with the stage.
The hypotheses below are explicit: this file does not yet assert their
instantiation for the packet choices made by the development.
-/

@[expose] public section


namespace Euler.ComparatorBridge

open Finset Set

variable {E : Type*} [NormedAddCommGroup E]

theorem displacement_comp_le (X Y : E → E) {M δ : ℝ}
    (hX : ∀ x, ‖X x - x‖ ≤ M) (hY : ∀ x, ‖Y x - x‖ ≤ δ) (x : E) :
    ‖X (Y x) - x‖ ≤ M + δ := by
  calc
    ‖X (Y x) - x‖ = ‖(X (Y x) - Y x) + (Y x - x)‖ := by
      rw [sub_add_sub_cancel]
    _ ≤ ‖X (Y x) - Y x‖ + ‖Y x - x‖ := norm_add_le _ _
    _ ≤ M + δ := add_le_add (hX _) (hY _)

omit [NormedAddCommGroup E] in
/-- A transported quantity that starts supported in `K` remains supported in
the region containing its transported labels. Only preservation of zero is
needed; the transported quantity need not be constant along trajectories. -/
theorem support_subset_of_transport {F : Type*} [Zero F]
    (X Y : E → E) (w₀ w : E → F) {K L : Set E}
    (hright : ∀ x, X (Y x) = x) (hmap : MapsTo X K L)
    (hinitial : Function.support w₀ ⊆ K)
    (htransport : ∀ a, w₀ a = 0 → w (X a) = 0) :
    Function.support w ⊆ L := by
  classical
  intro x hx
  by_contra houtside
  have ha : Y x ∉ K := fun hy => houtside (hright x ▸ hmap hy)
  have hzero : w₀ (Y x) = 0 := by
    by_contra hne
    exact ha (hinitial (Function.mem_support.mpr hne))
  have h := htransport (Y x) hzero
  rw [hright x] at h
  exact (Function.mem_support.mp hx) h

variable {Time : Type*} (H : ℕ → Time → Prop)
  (X Y : ℕ → Time → E → E) (M : ℝ) (δ : ℕ → ℝ)
  (hbase : ∀ t, H 0 t → ∀ x, ‖X 0 t x - x‖ ≤ M)
  (hnest : ∀ n t, H (n + 1) t → H n t)
  (hstep : ∀ n t, H (n + 1) t → ∀ x, X (n + 1) t x = X n t (Y n t x))
  (hsmall : ∀ n t, H (n + 1) t → ∀ x, ‖Y n t x - x‖ ≤ δ n)

include hbase hnest hstep hsmall in
theorem stage_displacement_le_partial_sum (n : ℕ) (t : Time) (ht : H n t) (x : E) :
    ‖X n t x - x‖ ≤ M + ∑ i ∈ range n, δ i := by
  induction n generalizing x with
  | zero => simpa using hbase t ht x
  | succ n ih =>
    rw [hstep n t ht, sum_range_succ, ← add_assoc]
    exact displacement_comp_le (X n t) (Y n t)
      (fun y => ih (hnest n t ht) y) (hsmall n t ht) x

include hbase hnest hstep hsmall in
theorem stage_displacement_le_of_partial_sums {C : ℝ}
    (hC : ∀ n, ∑ i ∈ range n, δ i ≤ C)
    (n : ℕ) (t : Time) (ht : H n t) (x : E) :
    ‖X n t x - x‖ ≤ M + C := by
  exact (stage_displacement_le_partial_sum H X Y M δ hbase hnest hstep hsmall n t ht x).trans
    (add_le_add le_rfl (hC n))

include hbase hnest hstep hsmall in
theorem stage_mapsTo_closedBall_of_partial_sums {C : ℝ}
    (hC : ∀ n, ∑ i ∈ range n, δ i ≤ C)
    (R : ℝ) (n : ℕ) (t : Time) (ht : H n t) :
    MapsTo (X n t) (Metric.closedBall 0 R) (Metric.closedBall 0 (R + M + C)) := by
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right] at hx ⊢
  calc
    ‖X n t x‖ = ‖x + (X n t x - x)‖ := by rw [add_comm x, sub_add_cancel]
    _ ≤ ‖x‖ + ‖X n t x - x‖ := norm_add_le _ _
    _ ≤ R + (M + C) := add_le_add hx
      (stage_displacement_le_of_partial_sums H X Y M δ hbase hnest hstep hsmall hC n t ht x)
    _ = R + M + C := (add_assoc _ _ _).symm

include hbase hnest hstep hsmall in
theorem stage_displacement_le_tsum (hδ : Summable δ) (hδ0 : ∀ n, 0 ≤ δ n)
    (n : ℕ) (t : Time) (ht : H n t) (x : E) :
    ‖X n t x - x‖ ≤ M + ∑' i, δ i := by
  exact (stage_displacement_le_partial_sum H X Y M δ hbase hnest hstep hsmall n t ht x).trans
    (add_le_add le_rfl (hδ.sum_le_tsum (range n) (fun i _ => hδ0 i)))

include hbase hnest hstep hsmall in
theorem stage_mapsTo_closedBall (hδ : Summable δ) (hδ0 : ∀ n, 0 ≤ δ n)
    (R : ℝ) (n : ℕ) (t : Time) (ht : H n t) :
    MapsTo (X n t) (Metric.closedBall 0 R) (Metric.closedBall 0 (R + M + ∑' i, δ i)) := by
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right] at hx ⊢
  calc
    ‖X n t x‖ = ‖x + (X n t x - x)‖ := by rw [add_comm x, sub_add_cancel]
    _ ≤ ‖x‖ + ‖X n t x - x‖ := norm_add_le _ _
    _ ≤ R + (M + ∑' i, δ i) := add_le_add hx
      (stage_displacement_le_tsum H X Y M δ hbase hnest hstep hsmall hδ hδ0 n t ht x)
    _ = R + M + ∑' i, δ i := (add_assoc _ _ _).symm

end Euler.ComparatorBridge
