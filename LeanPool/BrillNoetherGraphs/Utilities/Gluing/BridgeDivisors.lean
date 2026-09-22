/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Gluing.BridgeGraph

/-!
# Divisors and firing scripts on a bridge graph

Divisors and firing scripts on either factor extend by zero to the graph formed
by joining the factors with a bridge. A script which is one on the left factor
and zero on the right records the elementary chip transfer across the bridge.
-/

open Finset

namespace MarkedGraphs

open Utilities

universe u v

/-- Extend a divisor on the left factor by zero on the right factor. -/
def liftLeftDivisor (G : CFGraph.{u}) (H : CFGraph.{v})
    (x : G.V) (y : H.V) (D : CFDiv G) :
    CFDiv (bridgeGraph G H x y) :=
  Sum.elim D (fun _ => 0)

/-- Extend a divisor on the right factor by zero on the left factor. -/
def liftRightDivisor (G : CFGraph.{u}) (H : CFGraph.{v})
    (x : G.V) (y : H.V) (D : CFDiv H) :
    CFDiv (bridgeGraph G H x y) :=
  Sum.elim (fun _ => 0) D

@[simp] theorem liftLeftDivisor_inl
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D : CFDiv G) (a : G.V) :
    liftLeftDivisor G H x y D (Sum.inl a) = D a := rfl

@[simp] theorem liftLeftDivisor_inr
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D : CFDiv G) (b : H.V) :
    liftLeftDivisor G H x y D (Sum.inr b) = 0 := rfl

@[simp] theorem liftRightDivisor_inl
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D : CFDiv H) (a : G.V) :
    liftRightDivisor G H x y D (Sum.inl a) = 0 := rfl

@[simp] theorem liftRightDivisor_inr
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D : CFDiv H) (b : H.V) :
    liftRightDivisor G H x y D (Sum.inr b) = D b := rfl
/-- Zero extension from the left preserves divisor degree. -/
@[simp] theorem deg_liftLeftDivisor
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D : CFDiv G) :
    deg (liftLeftDivisor G H x y D) = deg D := by
  change (∑ z : Sum G.V H.V, liftLeftDivisor G H x y D z) =
    ∑ a : G.V, D a
  rw [Fintype.sum_sum_type]
  simp
/-- Zero extension from the right preserves divisor degree. -/
@[simp] theorem deg_liftRightDivisor
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D : CFDiv H) :
    deg (liftRightDivisor G H x y D) = deg D := by
  change (∑ z : Sum G.V H.V, liftRightDivisor G H x y D z) =
    ∑ b : H.V, D b
  rw [Fintype.sum_sum_type]
  simp

/-- Zero extension from the left is effective exactly when the original
divisor is effective. -/
@[simp] theorem effective_liftLeftDivisor_iff
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D : CFDiv G) :
    effective (liftLeftDivisor G H x y D) ↔ effective D := by
  constructor
  · intro h a
    exact h (Sum.inl a)
  · intro h z
    cases z with
    | inl a => exact h a
    | inr b => simp

/-- Zero extension from the right is effective exactly when the original
divisor is effective. -/
@[simp] theorem effective_liftRightDivisor_iff
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D : CFDiv H) :
    effective (liftRightDivisor G H x y D) ↔ effective D := by
  constructor
  · intro h b
    exact h (Sum.inr b)
  · intro h z
    cases z with
    | inl a => simp
    | inr b => exact h b

/-- Extend a firing script on the left factor by zero on the right. -/
def liftLeftScript (G : CFGraph.{u}) (H : CFGraph.{v})
    (x : G.V) (y : H.V) (σ : firing_script G) :
    firing_script (bridgeGraph G H x y) :=
  Sum.elim σ (fun _ => 0)

/-- Extend a firing script on the right factor by zero on the left. -/
def liftRightScript (G : CFGraph.{u}) (H : CFGraph.{v})
    (x : G.V) (y : H.V) (σ : firing_script H) :
    firing_script (bridgeGraph G H x y) :=
  Sum.elim (fun _ => 0) σ

@[simp] theorem liftLeftScript_inl
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (σ : firing_script G) (a : G.V) :
    liftLeftScript G H x y σ (Sum.inl a) = σ a := rfl

@[simp] theorem liftLeftScript_inr
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (σ : firing_script G) (b : H.V) :
    liftLeftScript G H x y σ (Sum.inr b) = 0 := rfl

@[simp] theorem liftRightScript_inl
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (σ : firing_script H) (a : G.V) :
    liftRightScript G H x y σ (Sum.inl a) = 0 := rfl

@[simp] theorem liftRightScript_inr
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (σ : firing_script H) (b : H.V) :
    liftRightScript G H x y σ (Sum.inr b) = σ b := rfl

/-- Extend a left-factor script constantly across the right factor, using its
value at the bridge endpoint. This introduces no firing across the bridge. -/
def extendLeftScript (G : CFGraph.{u}) (H : CFGraph.{v})
    (x : G.V) (y : H.V) (σ : firing_script G) :
    firing_script (bridgeGraph G H x y) :=
  Sum.elim σ (fun _ => σ x)

/-- Extend a right-factor script constantly across the left factor, using its
value at the bridge endpoint. This introduces no firing across the bridge. -/
def extendRightScript (G : CFGraph.{u}) (H : CFGraph.{v})
    (x : G.V) (y : H.V) (σ : firing_script H) :
    firing_script (bridgeGraph G H x y) :=
  Sum.elim (fun _ => σ y) σ

@[simp] theorem extendLeftScript_inl
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (σ : firing_script G) (a : G.V) :
    extendLeftScript G H x y σ (Sum.inl a) = σ a := rfl

@[simp] theorem extendLeftScript_inr
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (σ : firing_script G) (b : H.V) :
    extendLeftScript G H x y σ (Sum.inr b) = σ x := rfl

@[simp] theorem extendRightScript_inl
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (σ : firing_script H) (a : G.V) :
    extendRightScript G H x y σ (Sum.inl a) = σ y := rfl

@[simp] theorem extendRightScript_inr
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (σ : firing_script H) (b : H.V) :
    extendRightScript G H x y σ (Sum.inr b) = σ b := rfl
/-- Endpoint-constant extension carries a principal divisor from the left
factor to its zero extension on the bridge graph. -/
theorem prin_extendLeftScript
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (σ : firing_script G) :
    prin (bridgeGraph G H x y) (extendLeftScript G H x y σ) =
      liftLeftDivisor G H x y (prin G σ) := by
  funext z
  cases z with
  | inl a =>
      change
        (∑ z : Sum G.V H.V,
          (extendLeftScript G H x y σ z - σ a) *
            (num_edges (bridgeGraph G H x y) (Sum.inl a) z : ℤ)) =
          (prin G σ) a
      rw [Fintype.sum_sum_type]
      simp only [extendLeftScript_inl, extendLeftScript_inr,
        num_edges_bridgeGraph_inl, num_edges_bridgeGraph_inl_inr]
      change
        (∑ p : G.V, (σ p - σ a) * (num_edges G a p : ℤ)) +
            ∑ q : H.V,
              (σ x - σ a) *
                (((if a = x ∧ q = y then 1 else 0) : ℕ) : ℤ) =
          ∑ p : G.V, (σ p - σ a) * (num_edges G a p : ℤ)
      by_cases ha : a = x
      · subst a
        simp
      · simp [ha]
  | inr b =>
      change
        (∑ z : Sum G.V H.V,
          (extendLeftScript G H x y σ z - σ x) *
            (num_edges (bridgeGraph G H x y) (Sum.inr b) z : ℤ)) = 0
      rw [Fintype.sum_sum_type]
      have hCross (a : G.V) :
          num_edges (bridgeGraph G H x y) (Sum.inr b) (Sum.inl a) =
            if a = x ∧ b = y then 1 else 0 := by
        rw [num_edges_symmetric]
        exact num_edges_bridgeGraph_inl_inr G H x y a b
      simp_rw [extendLeftScript_inl, extendLeftScript_inr, hCross,
        num_edges_bridgeGraph_inr]
      simp
      apply Finset.sum_eq_zero
      intro a _ha
      by_cases h : a = x ∧ b = y
      · rcases h with ⟨rfl, _⟩
        simp
      · simp [h]
/-- Endpoint-constant extension carries a principal divisor from the right
factor to its zero extension on the bridge graph. -/
theorem prin_extendRightScript
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (σ : firing_script H) :
    prin (bridgeGraph G H x y) (extendRightScript G H x y σ) =
      liftRightDivisor G H x y (prin H σ) := by
  funext z
  cases z with
  | inl a =>
      change
        (∑ z : Sum G.V H.V,
          (extendRightScript G H x y σ z - σ y) *
            (num_edges (bridgeGraph G H x y) (Sum.inl a) z : ℤ)) = 0
      rw [Fintype.sum_sum_type]
      simp_rw [extendRightScript_inl, extendRightScript_inr,
        num_edges_bridgeGraph_inl, num_edges_bridgeGraph_inl_inr]
      simp
      apply Finset.sum_eq_zero
      intro b _hb
      by_cases h : a = x ∧ b = y
      · rcases h with ⟨_, rfl⟩
        simp
      · simp [h]
  | inr b =>
      change
        (∑ z : Sum G.V H.V,
          (extendRightScript G H x y σ z - σ b) *
            (num_edges (bridgeGraph G H x y) (Sum.inr b) z : ℤ)) =
          (prin H σ) b
      rw [Fintype.sum_sum_type]
      have hCross (a : G.V) :
          num_edges (bridgeGraph G H x y) (Sum.inr b) (Sum.inl a) =
            if a = x ∧ b = y then 1 else 0 := by
        rw [num_edges_symmetric]
        exact num_edges_bridgeGraph_inl_inr G H x y a b
      simp_rw [extendRightScript_inl, extendRightScript_inr, hCross,
        num_edges_bridgeGraph_inr]
      change
        (∑ p : G.V,
          (σ y - σ b) *
            (((if p = x ∧ b = y then 1 else 0) : ℕ) : ℤ)) +
            ∑ q : H.V, (σ q - σ b) * (num_edges H b q : ℤ) =
          ∑ q : H.V, (σ q - σ b) * (num_edges H b q : ℤ)
      by_cases hb : b = y
      · subst b
        simp
      · simp [hb]
/-- Linear equivalence on the left factor remains linear equivalence after
zero extension to the bridge graph. -/
theorem linear_equiv_liftLeftDivisor
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    {D E : CFDiv G} (hDE : linear_equiv G D E) :
    linear_equiv (bridgeGraph G H x y)
      (liftLeftDivisor G H x y D) (liftLeftDivisor G H x y E) := by
  unfold linear_equiv at hDE ⊢
  obtain ⟨σ, hσ⟩ := (principal_iff_eq_prin G (E - D)).mp hDE
  apply (principal_iff_eq_prin (bridgeGraph G H x y)
    (liftLeftDivisor G H x y E - liftLeftDivisor G H x y D)).mpr
  refine ⟨extendLeftScript G H x y σ, ?_⟩
  rw [prin_extendLeftScript]
  funext z
  cases z with
  | inl a => simpa using congrFun hσ a
  | inr b => simp
/-- Linear equivalence on the right factor remains linear equivalence after
zero extension to the bridge graph. -/
theorem linear_equiv_liftRightDivisor
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    {D E : CFDiv H} (hDE : linear_equiv H D E) :
    linear_equiv (bridgeGraph G H x y)
      (liftRightDivisor G H x y D) (liftRightDivisor G H x y E) := by
  unfold linear_equiv at hDE ⊢
  obtain ⟨σ, hσ⟩ := (principal_iff_eq_prin H (E - D)).mp hDE
  apply (principal_iff_eq_prin (bridgeGraph G H x y)
    (liftRightDivisor G H x y E - liftRightDivisor G H x y D)).mpr
  refine ⟨extendRightScript G H x y σ, ?_⟩
  rw [prin_extendRightScript]
  funext z
  cases z with
  | inl a => simp
  | inr b => simpa using congrFun hσ b

/-- Winnability on the left factor is preserved by zero extension. -/
theorem winnable_liftLeftDivisor
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    {D : CFDiv G} (hD : winnable G D) :
    winnable (bridgeGraph G H x y) (liftLeftDivisor G H x y D) := by
  obtain ⟨E, hEEffective, hDE⟩ := hD
  exact ⟨liftLeftDivisor G H x y E,
    (effective_liftLeftDivisor_iff G H x y E).mpr hEEffective,
    linear_equiv_liftLeftDivisor G H x y hDE⟩

/-- Winnability on the right factor is preserved by zero extension. -/
theorem winnable_liftRightDivisor
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    {D : CFDiv H} (hD : winnable H D) :
    winnable (bridgeGraph G H x y) (liftRightDivisor G H x y D) := by
  obtain ⟨E, hEEffective, hDE⟩ := hD
  exact ⟨liftRightDivisor G H x y E,
    (effective_liftRightDivisor_iff G H x y E).mpr hEEffective,
    linear_equiv_liftRightDivisor G H x y hDE⟩

/-- The firing script which is one on the left factor and zero on the right. -/
def leftSideIndicator (G : CFGraph.{u}) (H : CFGraph.{v})
    (x : G.V) (y : H.V) : firing_script (bridgeGraph G H x y) :=
  liftLeftScript G H x y (fun _ => 1)

@[simp] theorem leftSideIndicator_inl
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (a : G.V) :
    leftSideIndicator G H x y (Sum.inl a) = 1 := rfl

@[simp] theorem leftSideIndicator_inr
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (b : H.V) :
    leftSideIndicator G H x y (Sum.inr b) = 0 := rfl
/-- With the library's negative-Laplacian sign convention, firing the left
side once moves one chip from the left endpoint to the right endpoint. -/
theorem prin_leftSideIndicator
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V) :
    prin (bridgeGraph G H x y) (leftSideIndicator G H x y) =
      one_chip (Sum.inr y) - one_chip (Sum.inl x) := by
  funext z
  cases z with
  | inl a =>
      change
        (∑ z : Sum G.V H.V,
          (leftSideIndicator G H x y z -
              leftSideIndicator G H x y (Sum.inl a)) *
            (num_edges (bridgeGraph G H x y) (Sum.inl a) z : ℤ)) =
          (one_chip (G := bridgeGraph G H x y) (Sum.inr y)) (Sum.inl a) -
            (one_chip (G := bridgeGraph G H x y) (Sum.inl x)) (Sum.inl a)
      rw [Fintype.sum_sum_type]
      simp [one_chip]
      by_cases ha : a = x
      · subst a
        simp
      · simp [ha]
  | inr b =>
      change
        (∑ z : Sum G.V H.V,
          (leftSideIndicator G H x y z -
              leftSideIndicator G H x y (Sum.inr b)) *
            (num_edges (bridgeGraph G H x y) (Sum.inr b) z : ℤ)) =
          (one_chip (G := bridgeGraph G H x y) (Sum.inr y)) (Sum.inr b) -
            (one_chip (G := bridgeGraph G H x y) (Sum.inl x)) (Sum.inr b)
      rw [Fintype.sum_sum_type]
      have hCross (a : G.V) :
          num_edges (bridgeGraph G H x y) (Sum.inr b) (Sum.inl a) =
            if a = x ∧ b = y then 1 else 0 := by
        rw [num_edges_symmetric]
        exact num_edges_bridgeGraph_inl_inr G H x y a b
      simp_rw [hCross]
      simp [one_chip]
      by_cases hb : b = y
      · subst b
        simp
        have hFilter :
            Finset.univ.filter (fun a : G.V => a = x) = {x} := by
          ext a
          simp
        rw [hFilter]
        simp
      · simp [hb]

end MarkedGraphs
