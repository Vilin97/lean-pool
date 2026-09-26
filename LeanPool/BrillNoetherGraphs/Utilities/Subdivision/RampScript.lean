/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.SlopeScript

/-!
# Ramp firing scripts on positive subdivisions

A ramp is constant, then affine with slope `-1`, `0`, or `1` on a bounded
window of each edge slot, then constant again.  This is the generic positive-
length infrastructure behind the readable genus-four pencil proofs.
-/

@[expose] public section

namespace Utilities.Certificate.SubdivisionRamp

open Utilities
open Utilities.Certificate
open Utilities.Certificate.SubdivisionGraph
open Finset

variable {n p : ℕ}

/-- Two divisors on a subdivision agree when they agree on core and interior
vertices separately. -/
theorem divisor_ext {spec : SubdivisionGraph.Spec n p}
    {D E : CFDiv spec.graph}
    (hcore : ∀ v : Fin n, D (spec.coreVertex v) = E (spec.coreVertex v))
    (hint : ∀ (edge : Fin p) (offset : Fin (spec.length edge - 1)),
      D (spec.interiorVertex edge offset) =
        E (spec.interiorVertex edge offset)) :
    D = E := by
  funext vertex
  rcases vertex with u | ⟨edge, offset⟩
  · exact hcore u
  · exact hint edge offset

/-- A strictly interior path position is its corresponding interior vertex. -/
theorem pathVertex_interior (spec : SubdivisionGraph.Spec n p)
    (edge : Fin p) (k : ℕ) (hk0 : 0 < k) (hk : k < spec.length edge) :
    spec.pathVertex edge ⟨k, by omega⟩ =
      spec.interiorVertex edge ⟨k - 1, by omega⟩ := by
  unfold SubdivisionGraph.Spec.pathVertex
  rw [dite_eq_right (by omega : ¬ k = 0),
    dite_eq_right (by omega : ¬ k = spec.length edge)]

/-- Distinct interior vertices are distinguished by slot and offset. -/
theorem interiorVertex_eq_iff (spec : SubdivisionGraph.Spec n p)
    (e e' : Fin p) (off : Fin (spec.length e - 1))
    (off' : Fin (spec.length e' - 1)) :
    spec.interiorVertex e off = spec.interiorVertex e' off' ↔
      e = e' ∧ off.val = off'.val := by
  constructor
  · intro h
    have hs : (⟨e, off⟩ : Σ edge : Fin p, Fin (spec.length edge - 1)) =
        ⟨e', off'⟩ := Sum.inr.inj h
    exact ⟨congrArg Sigma.fst hs,
      congrArg (fun s : (Σ edge : Fin p, Fin (spec.length edge - 1)) =>
        s.2.val) hs⟩
  · rintro ⟨rfl, hv⟩
    have hoff : off = off' := Fin.ext hv
    rw [hoff]

/-- A core vertex cannot be an interior vertex. -/
theorem coreVertex_ne_interiorVertex (spec : SubdivisionGraph.Spec n p)
    (v : Fin n) (e : Fin p) (off : Fin (spec.length e - 1)) :
    spec.coreVertex v ≠ spec.interiorVertex e off := by
  simp [SubdivisionGraph.Spec.coreVertex, SubdivisionGraph.Spec.interiorVertex]

/-- Path values of a ramp script. -/
def rampValue (spec : SubdivisionGraph.Spec n p) (pot : Fin n → ℤ)
    (sgn : Fin p → ℤ) (lo : Fin p → ℕ) (t : ℕ) : Fin p → ℕ → ℤ :=
  fun edge k =>
    pot (spec.core.tail edge) +
      sgn edge * ((min (k - lo edge) t : ℕ) : ℤ)

/-- The ramp firing script. -/
def rampScript (spec : SubdivisionGraph.Spec n p) (pot : Fin n → ℤ)
    (sgn : Fin p → ℤ) (lo : Fin p → ℕ) (t : ℕ) :
    firingScript spec.graph :=
  spec.slotValueScript pot (rampValue spec pot sgn lo t)

/-- Unit-step slopes of a ramp script. -/
def rampSlope (sgn : Fin p → ℤ) (lo : Fin p → ℕ) (t : ℕ) :
    Fin p → ℕ → ℤ :=
  fun edge k => if lo edge ≤ k ∧ k < lo edge + t then sgn edge else 0

/-- Consistency of ramp data with the endpoint potentials and edge lengths. -/
structure RampData (spec : SubdivisionGraph.Spec n p) (pot : Fin n → ℤ)
    (sgn : Fin p → ℤ) (lo : Fin p → ℕ) (t : ℕ) : Prop where
  potential : ∀ edge : Fin p,
    pot (spec.core.head edge) =
      pot (spec.core.tail edge) + sgn edge * (t : ℤ)
  window : ∀ edge : Fin p, lo edge + t ≤ spec.length edge ∨ sgn edge = 0

variable {spec : SubdivisionGraph.Spec n p} {pot : Fin n → ℤ}
  {sgn : Fin p → ℤ} {lo : Fin p → ℕ} {t : ℕ}

theorem rampCompatible (h : RampData spec pot sgn lo t) :
    spec.SlotValueCompatible pot (rampValue spec pot sgn lo t) := by
  constructor
  · intro edge
    simp [rampValue]
  · intro edge
    have hp := h.potential edge
    rcases h.window edge with hw | hw
    · have hmin : min (spec.length edge - lo edge) t = t := by omega
      simp only [rampValue, hmin, hp]
    · simp only [rampValue, hp, hw]
      ring

theorem isStepSlope_ramp (h : RampData spec pot sgn lo t) :
    spec.IsStepSlope (rampScript spec pot sgn lo t) (rampSlope sgn lo t) := by
  intro edge offset
  rw [rampScript, spec.slotValueScript_stepRight (rampCompatible h),
    spec.slotValueScript_stepLeft (rampCompatible h)]
  simp only [rampValue, rampSlope]
  by_cases hw : lo edge ≤ offset.val ∧ offset.val < lo edge + t
  · rw [ite_eq_left hw]
    obtain ⟨hw1, hw2⟩ := hw
    have h1 : min (offset.val + 1 - lo edge) t =
        (offset.val - lo edge) + 1 := by omega
    have h2 : min (offset.val - lo edge) t = offset.val - lo edge := by omega
    rw [h1, h2]
    push_cast
    try ring
  · rw [ite_eq_right hw]
    have h1 : min (offset.val + 1 - lo edge) t =
        min (offset.val - lo edge) t := by
      simp only [not_and_or, not_le, not_lt] at hw
      omega
    rw [h1]
    try ring

theorem prin_ramp_coreVertex (h : RampData spec pot sgn lo t) (v : Fin n) :
    prin spec.graph (rampScript spec pot sgn lo t) (spec.coreVertex v) =
      ∑ edge : Fin p,
        ((if spec.core.tail edge = v then rampSlope sgn lo t edge 0 else 0) +
          (if spec.core.head edge = v then
            -rampSlope sgn lo t edge (spec.length edge - 1) else 0)) :=
  spec.prin_coreVertex_eq_endpointSum (isStepSlope_ramp h) v

theorem prin_ramp_interiorVertex (h : RampData spec pot sgn lo t)
    (edge : Fin p) (offset : Fin (spec.length edge - 1)) :
    prin spec.graph (rampScript spec pot sgn lo t)
        (spec.interiorVertex edge offset) =
      rampSlope sgn lo t edge (offset.val + 1) -
        rampSlope sgn lo t edge offset.val :=
  spec.prin_interiorVertex_eq_slopeDifference (isStepSlope_ramp h) edge offset

theorem rampSlope_zero (sgn : Fin p → ℤ) (lo : Fin p → ℕ) (t : ℕ)
    (edge : Fin p) :
    rampSlope sgn lo t edge 0 =
      if lo edge = 0 ∧ 0 < t then sgn edge else 0 := by
  simp only [rampSlope]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem rampSlope_last (h : RampData spec pot sgn lo t) (edge : Fin p) :
    rampSlope sgn lo t edge (spec.length edge - 1) =
      if lo edge + t = spec.length edge ∧ 0 < t then sgn edge else 0 := by
  have hpos := spec.length_pos edge
  rcases h.window edge with hw | hw
  · simp only [rampSlope]
    split_ifs <;> first | rfl | (exfalso; omega)
  · simp only [rampSlope, hw]
    split_ifs <;> rfl

theorem rampSlope_zero_t (sgn : Fin p → ℤ) (lo : Fin p → ℕ)
    (edge : Fin p) (k : ℕ) : rampSlope sgn lo 0 edge k = 0 := by
  simp only [rampSlope]
  rw [ite_eq_right (show ¬ (lo edge ≤ k ∧ k < lo edge + 0) by omega)]

/-- Divergence of a ramp along one slot. -/
theorem rampSlope_diff (sgn : Fin p → ℤ) (lo : Fin p → ℕ) (t : ℕ)
    (edge : Fin p) (k : ℕ) (hk : 0 < k) :
    rampSlope sgn lo t edge k - rampSlope sgn lo t edge (k - 1) =
      (if k = lo edge ∧ 0 < t then sgn edge else 0) -
        (if k = lo edge + t ∧ 0 < t then sgn edge else 0) := by
  rcases Nat.eq_zero_or_pos t with ht | ht
  · subst ht
    rw [rampSlope_zero_t, rampSlope_zero_t,
      ite_eq_right (show ¬ (k = lo edge ∧ 0 < 0) by omega),
      ite_eq_right (show ¬ (k = lo edge + 0 ∧ 0 < 0) by omega)]
    try ring
  · simp only [rampSlope]
    by_cases h1 : lo edge ≤ k ∧ k < lo edge + t
    · rw [ite_eq_left h1]
      by_cases h2 : lo edge ≤ k - 1 ∧ k - 1 < lo edge + t
      · rw [ite_eq_left h2, ite_eq_right (show ¬ (k = lo edge ∧ 0 < t) by omega),
          ite_eq_right (show ¬ (k = lo edge + t ∧ 0 < t) by omega)]
        try ring
      · rw [ite_eq_right h2, ite_eq_left (show k = lo edge ∧ 0 < t by omega),
          ite_eq_right (show ¬ (k = lo edge + t ∧ 0 < t) by omega)]
        try ring
    · rw [ite_eq_right h1]
      by_cases h2 : lo edge ≤ k - 1 ∧ k - 1 < lo edge + t
      · rw [ite_eq_left h2, ite_eq_right (show ¬ (k = lo edge ∧ 0 < t) by omega),
          ite_eq_left (show k = lo edge + t ∧ 0 < t by omega)]
        try ring
      · rw [ite_eq_right h2,
          ite_eq_right (show ¬ (k = lo edge ∧ 0 < t) by omega),
          ite_eq_right (show ¬ (k = lo edge + t ∧ 0 < t) by omega)]
        try ring

end Utilities.Certificate.SubdivisionRamp
