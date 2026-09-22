/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Gluing.BridgeDivisors
import LeanPool.BrillNoetherGraphs.Utilities.Gluing.VertexWedge

/-!
# Contracting a separating bridge

Contracting the bridge in `bridgeGraph G H x y` gives the vertex wedge
`vertexWedge G H x y`.  This file proves the divisor-theoretic statement
behind that observation: merging the two bridge-endpoint coefficients
preserves degree, linear equivalence, winnability, and every rank condition.

The proofs are entirely at the level of divisors and firing scripts.  In
particular, no graph isomorphism or connectivity hypothesis is needed.

The declarations remain in the established `MarkedGraphs` namespace for API
compatibility.
-/

open Finset

namespace Utilities

open MarkedGraphs

universe u v

/-- Contract the bridge endpoints, using the left endpoint as the vertex of
the resulting wedge. -/
def contractBridgeVertex (G : CFGraph.{u}) (H : CFGraph.{v})
    (x : G.V) (y : H.V) :
    (bridgeGraph G H x y).V → (vertexWedge G H x y).V :=
  Sum.elim Sum.inl (wedgeRightVertex G H x y)

@[simp] theorem contractBridgeVertex_inl
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V) (a : G.V) :
    contractBridgeVertex G H x y (Sum.inl a) = Sum.inl a := rfl
@[simp] theorem contractBridgeVertex_inr_marked
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V) :
    contractBridgeVertex G H x y (Sum.inr y) = Sum.inl x := by
  simp [contractBridgeVertex]
@[simp] theorem contractBridgeVertex_inr_unmarked
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (b : H.V) (hb : b ≠ y) :
    contractBridgeVertex G H x y (Sum.inr b) = Sum.inr ⟨b, hb⟩ := by
  simp [contractBridgeVertex, hb]

/-- Push a divisor through bridge contraction.  The coefficients at the two
bridge endpoints are added; every other coefficient is unchanged. -/
def bridgePushforwardHom (G : CFGraph.{u}) (H : CFGraph.{v})
    (x : G.V) (y : H.V) :
    CFDiv (bridgeGraph G H x y) →+ CFDiv (vertexWedge G H x y) where
  toFun D := Sum.elim
    (fun a => D (Sum.inl a) + if a = x then D (Sum.inr y) else 0)
    (fun b => D (Sum.inr b.1))
  map_zero' := by
    funext z
    cases z with
    | inl a =>
        change (0 : ℤ) + (if a = x then 0 else 0) = 0
        by_cases ha : a = x
        · simp [ha]
        · simp [ha]
    | inr b => rfl
  map_add' D E := by
    funext z
    cases z with
    | inl a =>
        change
          (D (Sum.inl a) + E (Sum.inl a)) +
              (if a = x then D (Sum.inr y) + E (Sum.inr y) else 0) =
            (D (Sum.inl a) + if a = x then D (Sum.inr y) else 0) +
              (E (Sum.inl a) + if a = x then E (Sum.inr y) else 0)
        by_cases ha : a = x
        · simp [ha]
          abel
        · simp [ha]
    | inr b => rfl

/-- Divisor pushforward along contraction of the separating bridge. -/
abbrev bridgePushforward (G : CFGraph.{u}) (H : CFGraph.{v})
    (x : G.V) (y : H.V) := bridgePushforwardHom G H x y

@[simp] theorem bridgePushforward_inl
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D : CFDiv (bridgeGraph G H x y)) (a : G.V) :
    bridgePushforward G H x y D (Sum.inl a) =
      D (Sum.inl a) + if a = x then D (Sum.inr y) else 0 := rfl

@[simp] theorem bridgePushforward_inr
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D : CFDiv (bridgeGraph G H x y)) (b : { b : H.V // b ≠ y }) :
    bridgePushforward G H x y D (Sum.inr b) = D (Sum.inr b.1) := rfl

/-- The canonical lift puts the coefficient of the common wedge vertex at
the left bridge endpoint and puts zero at the right bridge endpoint. -/
def bridgeCanonicalLiftHom (G : CFGraph.{u}) (H : CFGraph.{v})
    (x : G.V) (y : H.V) :
    CFDiv (vertexWedge G H x y) →+ CFDiv (bridgeGraph G H x y) where
  toFun D := Sum.elim
    (fun a => D (Sum.inl a))
    (fun b => if hb : b = y then 0 else D (Sum.inr ⟨b, hb⟩))
  map_zero' := by
    funext z
    cases z with
    | inl a => rfl
    | inr b =>
        change (if hb : b = y then (0 : ℤ) else 0) = 0
        by_cases hb : b = y
        · simp [hb]
        · simp [hb]
  map_add' D E := by
    funext z
    cases z with
    | inl a => rfl
    | inr b =>
        change
          (if hb : b = y then 0
            else D (Sum.inr ⟨b, hb⟩) + E (Sum.inr ⟨b, hb⟩)) =
          (if hb : b = y then 0 else D (Sum.inr ⟨b, hb⟩)) +
            (if hb : b = y then 0 else E (Sum.inr ⟨b, hb⟩))
        by_cases hb : b = y
        · simp [hb]
        · simp [hb]

/-- Canonical lift of a wedge divisor across the contracted bridge. -/
abbrev bridgeCanonicalLift (G : CFGraph.{u}) (H : CFGraph.{v})
    (x : G.V) (y : H.V) := bridgeCanonicalLiftHom G H x y

@[simp] theorem bridgeCanonicalLift_inl
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D : CFDiv (vertexWedge G H x y)) (a : G.V) :
    bridgeCanonicalLift G H x y D (Sum.inl a) = D (Sum.inl a) := rfl
@[simp] theorem bridgeCanonicalLift_inr_marked
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D : CFDiv (vertexWedge G H x y)) :
    bridgeCanonicalLift G H x y D (Sum.inr y) = 0 := by
  simp [bridgeCanonicalLiftHom]
@[simp] theorem bridgeCanonicalLift_inr_unmarked
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D : CFDiv (vertexWedge G H x y)) (b : H.V) (hb : b ≠ y) :
    bridgeCanonicalLift G H x y D (Sum.inr b) = D (Sum.inr ⟨b, hb⟩) := by
  simp [bridgeCanonicalLiftHom, hb]

@[simp] theorem bridgePushforward_canonicalLift
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D : CFDiv (vertexWedge G H x y)) :
    bridgePushforward G H x y (bridgeCanonicalLift G H x y D) = D := by
  funext z
  cases z with
  | inl a =>
      by_cases ha : a = x
      · simp [ha]
      · simp [ha]
  | inr b => simp [b.2]
/-- Bridge contraction preserves divisor degree. -/
@[simp] theorem deg_bridgePushforward
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D : CFDiv (bridgeGraph G H x y)) :
    deg (bridgePushforward G H x y D) = deg D := by
  classical
  change
    (∑ z : Sum G.V { b : H.V // b ≠ y },
      bridgePushforward G H x y D z) =
    ∑ z : Sum G.V H.V, D z
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [bridgePushforward_inl, bridgePushforward_inr]
  rw [sum_add_distrib]
  have hMarked : (∑ a : G.V, if a = x then D (Sum.inr y) else 0) =
      D (Sum.inr y) := by simp
  rw [hMarked]
  have hSplit := sum_unmarked_add_marked H y (fun b => D (Sum.inr b))
  linarith

/-- The canonical lift also preserves degree. -/
@[simp] theorem deg_bridgeCanonicalLift
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D : CFDiv (vertexWedge G H x y)) :
    deg (bridgeCanonicalLift G H x y D) = deg D := by
  have h := deg_bridgePushforward G H x y (bridgeCanonicalLift G H x y D)
  simpa using h.symm

/-- Pushforward takes effective divisors to effective divisors. -/
theorem effective_bridgePushforward
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    {D : CFDiv (bridgeGraph G H x y)} (hD : effective D) :
    effective (bridgePushforward G H x y D) := by
  intro z
  cases z with
  | inl a =>
      by_cases ha : a = x
      · subst a
        simpa using add_nonneg (hD (Sum.inl x)) (hD (Sum.inr y))
      · simpa [ha] using hD (Sum.inl a)
  | inr b => simpa using hD (Sum.inr b.1)

/-- A wedge divisor is effective exactly when its canonical lift is. -/
@[simp] theorem effective_bridgeCanonicalLift_iff
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D : CFDiv (vertexWedge G H x y)) :
    effective (bridgeCanonicalLift G H x y D) ↔ effective D := by
  constructor
  · intro hD z
    cases z with
    | inl a => simpa using hD (Sum.inl a)
    | inr b => simpa [b.2] using hD (Sum.inr b.1)
  · intro hD z
    cases z with
    | inl a => simpa using hD (Sum.inl a)
    | inr b =>
        by_cases hb : b = y
        · simp [hb]
        · simpa [hb] using hD (Sum.inr ⟨b, hb⟩)

/-- Restrict a firing script on the bridge graph to the left factor. -/
def restrictLeftBridgeScript (G : CFGraph.{u}) (H : CFGraph.{v})
    (x : G.V) (y : H.V)
    (σ : firing_script (bridgeGraph G H x y)) : firing_script G :=
  fun a => σ (Sum.inl a)

/-- Restrict a firing script on the bridge graph to the right factor. -/
def restrictRightBridgeScript (G : CFGraph.{u}) (H : CFGraph.{v})
    (x : G.V) (y : H.V)
    (σ : firing_script (bridgeGraph G H x y)) : firing_script H :=
  fun b => σ (Sum.inr b)

@[simp] theorem restrictLeftBridgeScript_apply
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (σ : firing_script (bridgeGraph G H x y)) (a : G.V) :
    restrictLeftBridgeScript G H x y σ a = σ (Sum.inl a) := rfl

@[simp] theorem restrictRightBridgeScript_apply
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (σ : firing_script (bridgeGraph G H x y)) (b : H.V) :
    restrictRightBridgeScript G H x y σ b = σ (Sum.inr b) := rfl

/-- After bridge contraction, normalize the right restriction of a firing
script by a constant so that its value at `y` agrees with the left value at
`x`, then glue the two restrictions. -/
def contractBridgeScript (G : CFGraph.{u}) (H : CFGraph.{v})
    (x : G.V) (y : H.V)
    (σ : firing_script (bridgeGraph G H x y)) :
    firing_script (vertexWedge G H x y) :=
  let σG := restrictLeftBridgeScript G H x y σ
  let σH := restrictRightBridgeScript G H x y σ
  let c := σ (Sum.inl x) - σ (Sum.inr y)
  wedgeScript G H x y σG (shiftScript H σH c) (by
    dsimp [σG, σH, c, restrictLeftBridgeScript, restrictRightBridgeScript,
      shiftScript]
    ring)

/-- Every bridge script is, up to a constant, the sum of its endpoint-constant
factor extensions and a multiple of the left-side indicator. -/
theorem bridge_script_decomposition
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (σ : firing_script (bridgeGraph G H x y)) :
    extendLeftScript G H x y (restrictLeftBridgeScript G H x y σ) +
        extendRightScript G H x y (restrictRightBridgeScript G H x y σ) +
        @SMul.smul ℤ (firing_script (bridgeGraph G H x y)) inferInstance
          (σ (Sum.inl x) - σ (Sum.inr y)) (leftSideIndicator G H x y) =
      shiftScript (bridgeGraph G H x y) σ (σ (Sum.inl x)) := by
  funext z
  cases z with
  | inl a =>
      change
        σ (Sum.inl a) + σ (Sum.inr y) +
            (σ (Sum.inl x) - σ (Sum.inr y)) • (1 : ℤ) =
          σ (Sum.inl a) + σ (Sum.inl x)
      rw [Int.zsmul_eq_mul]
      ring
  | inr b =>
      change
        σ (Sum.inl x) + σ (Sum.inr b) +
            (σ (Sum.inl x) - σ (Sum.inr y)) • (0 : ℤ) =
          σ (Sum.inr b) + σ (Sum.inl x)
      simp
      ring

/-- Principal divisors on a bridge split into factor-principal parts plus the
single elementary transfer across the bridge. -/
theorem prin_bridge_decomposition
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (σ : firing_script (bridgeGraph G H x y)) :
    prin (bridgeGraph G H x y) σ =
      liftLeftDivisor G H x y
          (prin G (restrictLeftBridgeScript G H x y σ)) +
        liftRightDivisor G H x y
          (prin H (restrictRightBridgeScript G H x y σ)) +
        @SMul.smul ℤ (CFDiv (bridgeGraph G H x y)) inferInstance
          (σ (Sum.inl x) - σ (Sum.inr y))
          (one_chip (G := bridgeGraph G H x y) (Sum.inr y) -
            one_chip (G := bridgeGraph G H x y) (Sum.inl x)) := by
  have hScale :
      prin (bridgeGraph G H x y)
          (@SMul.smul ℤ (firing_script (bridgeGraph G H x y)) inferInstance
            (σ (Sum.inl x) - σ (Sum.inr y))
            (leftSideIndicator G H x y)) =
        @SMul.smul ℤ (CFDiv (bridgeGraph G H x y)) inferInstance
          (σ (Sum.inl x) - σ (Sum.inr y))
          (prin (bridgeGraph G H x y) (leftSideIndicator G H x y)) :=
    AddMonoidHom.map_zsmul (prin (bridgeGraph G H x y))
      (σ (Sum.inl x) - σ (Sum.inr y)) (leftSideIndicator G H x y)
  calc
    prin (bridgeGraph G H x y) σ =
        prin (bridgeGraph G H x y)
          (shiftScript (bridgeGraph G H x y) σ (σ (Sum.inl x))) := by simp
    _ = prin (bridgeGraph G H x y)
          (extendLeftScript G H x y (restrictLeftBridgeScript G H x y σ) +
            extendRightScript G H x y (restrictRightBridgeScript G H x y σ) +
            @SMul.smul ℤ (firing_script (bridgeGraph G H x y)) inferInstance
              (σ (Sum.inl x) - σ (Sum.inr y))
              (leftSideIndicator G H x y)) := by
          rw [bridge_script_decomposition G H x y σ]
    _ = _ := by
      rw [map_add, map_add, hScale, prin_extendLeftScript,
        prin_extendRightScript, prin_leftSideIndicator]

/-- Pushing a zero-extended left divisor through bridge contraction gives its
literal left lift to the wedge. -/
@[simp] theorem bridgePushforward_liftLeftDivisor
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D : CFDiv G) :
    bridgePushforward G H x y (liftLeftDivisor G H x y D) =
      wedgeLiftLeftDivisor G H x y D := by
  funext z
  cases z with
  | inl a => simp
  | inr b => simp

/-- Pushing a zero-extended right divisor through bridge contraction gives its
right lift to the wedge. -/
@[simp] theorem bridgePushforward_liftRightDivisor
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D : CFDiv H) :
    bridgePushforward G H x y (liftRightDivisor G H x y D) =
      wedgeLiftRightDivisor G H x y D := by
  funext z
  cases z with
  | inl a =>
      by_cases ha : a = x
      · simp [ha]
      · simp [ha]
  | inr b => simp

/-- The elementary bridge transfer disappears when its two endpoints are
identified. -/
@[simp] theorem bridgePushforward_endpoint_difference
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V) :
    bridgePushforward G H x y
        (one_chip (G := bridgeGraph G H x y) (Sum.inr y) -
          one_chip (G := bridgeGraph G H x y) (Sum.inl x)) = 0 := by
  funext z
  cases z with
  | inl a =>
      change
        ((if Sum.inl a = Sum.inr y then 1 else 0) -
            if Sum.inl a = Sum.inl x then 1 else 0) +
            (if a = x then
              (if Sum.inr y = Sum.inr y then 1 else 0) -
                if Sum.inr y = Sum.inl x then 1 else 0
              else 0) = (0 : ℤ)
      by_cases ha : a = x
      · subst a
        simp
      · simp [ha]
  | inr b =>
      change
        (if Sum.inr b.1 = Sum.inr y then 1 else 0) -
          (if Sum.inr b.1 = Sum.inl x then 1 else 0) = (0 : ℤ)
      simp [b.2]
/-- The two one-sided wedge lifts add to `wedgeAddDivisor`. -/
theorem wedgeLiftLeft_add_wedgeLiftRight
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D : CFDiv G) (E : CFDiv H) :
    wedgeLiftLeftDivisor G H x y D + wedgeLiftRightDivisor G H x y E =
      wedgeAddDivisor G H x y D E := by
  funext z
  cases z with
  | inl a =>
      by_cases ha : a = x
      · simp [ha]
      · simp [ha]
  | inr b => simp

/-- The contracted firing script has exactly the two factor-principal parts. -/
theorem prin_contractBridgeScript
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (σ : firing_script (bridgeGraph G H x y)) :
    prin (vertexWedge G H x y) (contractBridgeScript G H x y σ) =
      wedgeAddDivisor G H x y
        (prin G (restrictLeftBridgeScript G H x y σ))
        (prin H (restrictRightBridgeScript G H x y σ)) := by
  unfold contractBridgeScript
  rw [prin_wedgeScript, prin_shiftScript]

/-- Bridge contraction sends every principal divisor to a principal divisor,
with an explicit contracted firing script. -/
theorem bridgePushforward_prin
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (σ : firing_script (bridgeGraph G H x y)) :
    bridgePushforward G H x y (prin (bridgeGraph G H x y) σ) =
      prin (vertexWedge G H x y) (contractBridgeScript G H x y σ) := by
  have hScale :
      bridgePushforward G H x y
          (@SMul.smul ℤ (CFDiv (bridgeGraph G H x y)) inferInstance
            (σ (Sum.inl x) - σ (Sum.inr y))
            (one_chip (G := bridgeGraph G H x y) (Sum.inr y) -
              one_chip (G := bridgeGraph G H x y) (Sum.inl x))) =
        @SMul.smul ℤ (CFDiv (vertexWedge G H x y)) inferInstance
          (σ (Sum.inl x) - σ (Sum.inr y))
          (bridgePushforward G H x y
            (one_chip (G := bridgeGraph G H x y) (Sum.inr y) -
              one_chip (G := bridgeGraph G H x y) (Sum.inl x))) :=
    AddMonoidHom.map_zsmul (bridgePushforward G H x y)
      (σ (Sum.inl x) - σ (Sum.inr y))
      (one_chip (G := bridgeGraph G H x y) (Sum.inr y) -
        one_chip (G := bridgeGraph G H x y) (Sum.inl x))
  have hZero :
      @SMul.smul ℤ (CFDiv (vertexWedge G H x y)) inferInstance
          (σ (Sum.inl x) - σ (Sum.inr y)) 0 = 0 := by
    exact smul_zero (σ (Sum.inl x) - σ (Sum.inr y))
  rw [prin_bridge_decomposition, map_add, map_add, hScale,
    bridgePushforward_liftLeftDivisor, bridgePushforward_liftRightDivisor,
    bridgePushforward_endpoint_difference, hZero, add_zero,
    wedgeLiftLeft_add_wedgeLiftRight, prin_contractBridgeScript]
/-- Every divisor on the bridge graph is linearly equivalent to the canonical
lift of its contraction.  The sole correction is a transfer across the
bridge, witnessed by `leftSideIndicator`. -/
theorem linear_equiv_bridgeCanonicalLift_pushforward
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D : CFDiv (bridgeGraph G H x y)) :
    linear_equiv (bridgeGraph G H x y) D
      (bridgeCanonicalLift G H x y (bridgePushforward G H x y D)) := by
  unfold linear_equiv
  apply (principal_iff_eq_prin (bridgeGraph G H x y)
    (bridgeCanonicalLift G H x y (bridgePushforward G H x y D) - D)).mpr
  let n : ℤ := -D (Sum.inr y)
  let τ : firing_script (bridgeGraph G H x y) :=
    @SMul.smul ℤ (firing_script (bridgeGraph G H x y)) inferInstance n
      (leftSideIndicator G H x y)
  refine ⟨τ, ?_⟩
  have hScale :
      prin (bridgeGraph G H x y) τ =
        @SMul.smul ℤ (CFDiv (bridgeGraph G H x y)) inferInstance n
          (prin (bridgeGraph G H x y) (leftSideIndicator G H x y)) := by
    exact AddMonoidHom.map_zsmul (prin (bridgeGraph G H x y)) n
      (leftSideIndicator G H x y)
  rw [hScale, prin_leftSideIndicator]
  have hScaleApply (z : (bridgeGraph G H x y).V) :
      (@SMul.smul ℤ (CFDiv (bridgeGraph G H x y)) inferInstance n
        (one_chip (G := bridgeGraph G H x y) (Sum.inr y) -
          one_chip (G := bridgeGraph G H x y) (Sum.inl x))) z =
        n • ((one_chip (G := bridgeGraph G H x y) (Sum.inr y) -
          one_chip (G := bridgeGraph G H x y) (Sum.inl x)) z) := by
    rfl
  funext z
  cases z with
  | inl a =>
      rw [hScaleApply]
      by_cases ha : a = x
      · subst a
        simp [n, one_chip]
      · have hax : (Sum.inl a : Sum G.V H.V) ≠ Sum.inl x :=
          fun h => ha (Sum.inl.inj h)
        simp [n, one_chip, ha]
  | inr b =>
      rw [hScaleApply]
      by_cases hb : b = y
      · subst b
        simp [n, one_chip]
      · have hby : (Sum.inr b : Sum G.V H.V) ≠ Sum.inr y :=
          fun h => hb (Sum.inr.inj h)
        simp [n, one_chip, hb]

/-- Linear equivalence descends through bridge contraction. -/
theorem linear_equiv_bridgePushforward
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    {D E : CFDiv (bridgeGraph G H x y)}
    (hDE : linear_equiv (bridgeGraph G H x y) D E) :
    linear_equiv (vertexWedge G H x y)
      (bridgePushforward G H x y D) (bridgePushforward G H x y E) := by
  unfold linear_equiv at hDE ⊢
  obtain ⟨σ, hσ⟩ :=
    (principal_iff_eq_prin (bridgeGraph G H x y) (E - D)).mp hDE
  apply (principal_iff_eq_prin (vertexWedge G H x y)
    (bridgePushforward G H x y E - bridgePushforward G H x y D)).mpr
  refine ⟨contractBridgeScript G H x y σ, ?_⟩
  rw [← bridgePushforward_prin, ← hσ, map_sub]

/-- Pull a firing script on the wedge back to the bridge graph, assigning the
common wedge value to both bridge endpoints. -/
def expandWedgeScript (G : CFGraph.{u}) (H : CFGraph.{v})
    (x : G.V) (y : H.V)
    (σ : firing_script (vertexWedge G H x y)) :
    firing_script (bridgeGraph G H x y) :=
  Sum.elim (fun a => σ (Sum.inl a))
    (fun b => σ (wedgeRightVertex G H x y b))

@[simp] theorem expandWedgeScript_inl
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (σ : firing_script (vertexWedge G H x y)) (a : G.V) :
    expandWedgeScript G H x y σ (Sum.inl a) = σ (Sum.inl a) := rfl

@[simp] theorem expandWedgeScript_inr
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (σ : firing_script (vertexWedge G H x y)) (b : H.V) :
    expandWedgeScript G H x y σ (Sum.inr b) =
      σ (wedgeRightVertex G H x y b) := rfl

/-- Contracting an endpoint-compatible lifted script recovers the original
wedge script literally. -/
@[simp] theorem contractBridgeScript_expandWedgeScript
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (σ : firing_script (vertexWedge G H x y)) :
    contractBridgeScript G H x y (expandWedgeScript G H x y σ) = σ := by
  funext z
  cases z with
  | inl a =>
      simp [contractBridgeScript, restrictLeftBridgeScript]
  | inr b =>
      simp [contractBridgeScript, restrictRightBridgeScript, shiftScript, b.2]

/-- A canonical lift of a principal wedge divisor is principal on the bridge
graph. -/
theorem principal_bridgeCanonicalLift_prin
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (σ : firing_script (vertexWedge G H x y)) :
    bridgeCanonicalLift G H x y (prin (vertexWedge G H x y) σ) ∈
      principal_divisors (bridgeGraph G H x y) := by
  let τ := expandWedgeScript G H x y σ
  have hZeroPrin :
      linear_equiv (bridgeGraph G H x y) 0
        (prin (bridgeGraph G H x y) τ) := by
    unfold linear_equiv
    apply (principal_iff_eq_prin (bridgeGraph G H x y)
      (prin (bridgeGraph G H x y) τ - 0)).mpr
    exact ⟨τ, by simp⟩
  have hCanonical := linear_equiv_bridgeCanonicalLift_pushforward G H x y
    (prin (bridgeGraph G H x y) τ)
  have hTrans := linear_equiv.trans hZeroPrin hCanonical
  have hPush :
      bridgePushforward G H x y (prin (bridgeGraph G H x y) τ) =
        prin (vertexWedge G H x y) σ := by
    rw [bridgePushforward_prin]
    simp [τ]
  rw [hPush] at hTrans
  unfold linear_equiv at hTrans
  simpa using hTrans

/-- Canonical lift preserves linear equivalence from the wedge to the bridge. -/
theorem linear_equiv_bridgeCanonicalLift
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    {D E : CFDiv (vertexWedge G H x y)}
    (hDE : linear_equiv (vertexWedge G H x y) D E) :
    linear_equiv (bridgeGraph G H x y)
      (bridgeCanonicalLift G H x y D) (bridgeCanonicalLift G H x y E) := by
  unfold linear_equiv at hDE ⊢
  obtain ⟨σ, hσ⟩ :=
    (principal_iff_eq_prin (vertexWedge G H x y) (E - D)).mp hDE
  rw [← map_sub, hσ]
  exact principal_bridgeCanonicalLift_prin G H x y σ

/-- Linear equivalence on the bridge graph is exactly linear equivalence of
the contracted divisors. -/
theorem linear_equiv_bridge_iff_pushforward
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D E : CFDiv (bridgeGraph G H x y)) :
    linear_equiv (bridgeGraph G H x y) D E ↔
      linear_equiv (vertexWedge G H x y)
        (bridgePushforward G H x y D) (bridgePushforward G H x y E) := by
  constructor
  · exact linear_equiv_bridgePushforward G H x y
  · intro hDE
    exact linear_equiv.trans
      (linear_equiv_bridgeCanonicalLift_pushforward G H x y D)
      (linear_equiv.trans
        (linear_equiv_bridgeCanonicalLift G H x y hDE)
        (linear_equiv.symm
          (linear_equiv_bridgeCanonicalLift_pushforward G H x y E)))

/-- Winnability is invariant under contraction of a separating bridge. -/
theorem winnable_bridge_iff_pushforward
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D : CFDiv (bridgeGraph G H x y)) :
    winnable (bridgeGraph G H x y) D ↔
      winnable (vertexWedge G H x y) (bridgePushforward G H x y D) := by
  constructor
  · rintro ⟨E, hEEffective, hDE⟩
    exact ⟨bridgePushforward G H x y E,
      effective_bridgePushforward G H x y hEEffective,
      linear_equiv_bridgePushforward G H x y hDE⟩
  · rintro ⟨E, hEEffective, hDE⟩
    refine ⟨bridgeCanonicalLift G H x y E,
      (effective_bridgeCanonicalLift_iff G H x y E).mpr hEEffective, ?_⟩
    exact linear_equiv.trans
      (linear_equiv_bridgeCanonicalLift_pushforward G H x y D)
      (linear_equiv_bridgeCanonicalLift G H x y hDE)

/-- Every rank inequality is invariant under contraction of a separating
bridge. -/
theorem rank_geq_bridge_iff_pushforward
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D : CFDiv (bridgeGraph G H x y)) (k : ℤ) :
    rank_geq (bridgeGraph G H x y) D k ↔
      rank_geq (vertexWedge G H x y) (bridgePushforward G H x y D) k := by
  constructor
  · intro hRank E hE
    have hLiftE :
        bridgeCanonicalLift G H x y E ∈
          eff_of_degree (bridgeGraph G H x y) k := by
      exact ⟨(effective_bridgeCanonicalLift_iff G H x y E).mpr hE.1,
        by simpa using hE.2⟩
    have hWin := hRank (bridgeCanonicalLift G H x y E) hLiftE
    have hPushWin :=
      (winnable_bridge_iff_pushforward G H x y
        (D - bridgeCanonicalLift G H x y E)).mp hWin
    simpa only [map_sub, bridgePushforward_canonicalLift] using hPushWin
  · intro hRank E hE
    have hPushE :
        bridgePushforward G H x y E ∈
          eff_of_degree (vertexWedge G H x y) k := by
      exact ⟨effective_bridgePushforward G H x y hE.1,
        by simpa using hE.2⟩
    have hWin := hRank (bridgePushforward G H x y E) hPushE
    apply (winnable_bridge_iff_pushforward G H x y (D - E)).mpr
    simpa only [map_sub] using hWin

/-- Baker--Norine rank itself is unchanged by contracting a separating
bridge. -/
@[simp] theorem rank_bridgePushforward
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D : CFDiv (bridgeGraph G H x y)) :
    rank (vertexWedge G H x y) (bridgePushforward G H x y D) =
      rank (bridgeGraph G H x y) D := by
  apply le_antisymm
  · apply (rank_geq_iff (bridgeGraph G H x y) D
      (rank (vertexWedge G H x y) (bridgePushforward G H x y D))).mp
    apply (rank_geq_bridge_iff_pushforward G H x y D _).mpr
    exact (rank_geq_iff (vertexWedge G H x y) (bridgePushforward G H x y D)
      (rank (vertexWedge G H x y) (bridgePushforward G H x y D))).mpr le_rfl
  · apply (rank_geq_iff (vertexWedge G H x y) (bridgePushforward G H x y D)
      (rank (bridgeGraph G H x y) D)).mp
    apply (rank_geq_bridge_iff_pushforward G H x y D _).mp
    exact (rank_geq_iff (bridgeGraph G H x y) D
      (rank (bridgeGraph G H x y) D)).mpr le_rfl

/-- Brill--Noether existence is invariant under contraction of a separating
bridge. -/
theorem BNExists_bridge_iff_vertexWedge
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (r d : ℤ) :
    BNExists (bridgeGraph G H x y) r d ↔
      BNExists (vertexWedge G H x y) r d := by
  constructor
  · rintro ⟨D, hDegree, hRank⟩
    refine ⟨bridgePushforward G H x y D, by simpa using hDegree, ?_⟩
    simpa using hRank
  · rintro ⟨D, hDegree, hRank⟩
    refine ⟨bridgeCanonicalLift G H x y D, by simpa using hDegree, ?_⟩
    have hRankEq := rank_bridgePushforward G H x y
      (bridgeCanonicalLift G H x y D)
    have hRankEq' :
        rank (vertexWedge G H x y) D =
          rank (bridgeGraph G H x y) (bridgeCanonicalLift G H x y D) := by
      simpa only [bridgePushforward_canonicalLift] using hRankEq
    rw [← hRankEq']
    exact hRank

end Utilities
