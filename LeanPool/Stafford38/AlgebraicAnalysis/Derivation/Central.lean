/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Tactic

/-!
# Centrality and inner derivations

This file contains the noncommutative derivation facts used by the
algebraic-analysis stages.  Mathlib's `Derivation` is specialized to
commutative coefficient rings, so the Leibniz and innerness predicates are
recorded directly for additive maps on arbitrary rings.

The fraction-presentation lemma is deliberately stated with all hypotheses
visible.  It does not assert that a particular localization has those
properties.
-/

namespace AlgebraicAnalysis.NoncommutativeDerivation

variable {E : Type*} [Ring E] [Nontrivial E]

/-- Leibniz rule for an additive derivation of a possibly noncommutative ring. -/
def IsDerivation (d : E →+ E) : Prop :=
  ∀ a b : E, d (a * b) = a * d b + d a * b

/-- An additive derivation is inner when it is a commutator with one element. -/
def IsInnerDerivation (d : E →+ E) : Prop :=
  ∃ e : E, ∀ y : E, d y = e * y - y * e
theorem not_isInnerDerivation_of_central
    (d : E →+ E) (x : E)
    (hxcentral : ∀ y : E, x * y = y * x) (hdx : d x = 1) :
    ¬ IsInnerDerivation d := by
  intro hinner
  obtain ⟨e, he⟩ := hinner
  have h := he x
  rw [hdx, hxcentral e] at h
  simp at h

omit [Nontrivial E] in
/-- Commutation with a set propagates through the subring it generates. -/
theorem commute_of_mem_subring_closure
    (x : E) (G : Set E) (hG : ∀ g ∈ G, Commute x g) :
    ∀ y : E, y ∈ Subring.closure G → Commute x y := by
  intro y hy
  induction hy using Subring.closure_induction with
  | mem z hz => exact hG z hz
  | zero => exact Commute.zero_right x
  | one => exact Commute.one_right x
  | add a b ha hb hca hcb => exact hca.add_right hcb
  | neg a ha hca => exact hca.neg_right
  | mul a b ha hb hca hcb => exact hca.mul_right hcb

omit [Nontrivial E] in
/--
A central element of a source ring remains central in a target ring when
every target element has a right-fraction presentation and every denominator
maps to a unit.  No commutativity of either ring is assumed.
-/
theorem commute_map_of_right_fraction_representation
    {R : Type*} [Ring R]
    (ι : R →+* E) (x : R)
    (hcentral : ∀ y : R, Commute x y)
    (hunit : ∀ s : R, IsUnit (ι s))
    (hrep : ∀ z : E, ∃ c s : R, z * ι s = ι c) :
    ∀ z : E, Commute (ι x) z := by
  intro z
  obtain ⟨c, s, hs⟩ := hrep z
  apply (hunit s).mul_right_cancel
  calc
    (ι x * z) * ι s = ι x * (z * ι s) := by rw [mul_assoc]
    _ = ι x * ι c := by rw [hs]
    _ = ι (x * c) := by rw [ι.map_mul]
    _ = ι (c * x) := by rw [(hcentral c).eq]
    _ = ι c * ι x := by rw [ι.map_mul]
    _ = (z * ι s) * ι x := by rw [hs]
    _ = (z * ι x) * ι s := by
      rw [mul_assoc, mul_assoc, ((hcentral s).map ι).eq]

/--
A derivation that sends a central coordinate to `1` cannot be inner.  This is
the form consumed by differential-Ore stage arguments.
-/
theorem not_inner_of_central_coordinate
    (d : E →+ E) (_hd : IsDerivation d) (x : E)
    (hxcentral : ∀ y : E, Commute x y) (hdx : d x = 1) :
    ¬ IsInnerDerivation d :=
  not_isInnerDerivation_of_central d x (fun y => (hxcentral y).eq) hdx


end AlgebraicAnalysis.NoncommutativeDerivation
