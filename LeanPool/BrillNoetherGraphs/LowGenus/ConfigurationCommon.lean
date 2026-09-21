/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.DegenerateInterpolation

/-!
# The base layer shared by every Atanasov--Ranganathan configuration

Every AR configuration on a genus-five core interpolates a potential that is
a negative constant on one contracted core class and zero elsewhere, and then
reads off what each original core slot contributes at each contracted class.
Three groups of facts are common to all of them and depend on no row and on
no particular configuration:

* the six one-slot ramp lemmas, which say what the first and last slope of a
  truncated ramp is (`firstStep_neg_eq_neg_one`, `lastStep_pos_eq_one`,
  `firstStep_full_eq_one`, `lastStep_neg_full_eq_neg_one`,
  `firstStep_pos_nonneg`, `lastStep_neg_nonpos`);
* the one-class potential `centerPotential` together with its
  rep-invariance and its value on a singleton class;
* the endpoint bookkeeping `endpointContribution` and `endpointPair`,
  including the fact that a slot with zero rise contributes nothing.

These used to live in `GenusFiveRow11`, where they were first written, which
forced `ConfigurationThree` and `ConfigurationTwo` to import a row.  They are
collected here so that the configuration files depend on no row at all, and
`GenusFiveRow11` can itself be a `ConfigTwo` instantiation.

## Core size

Everything here is generic in the core size `(n, p)`: `n` vertices and `p`
slots.  The genus-five programme instantiates it at `(8, 12)` and the
genus-six critical pencil at `(10, 15)`; because `n` and `p` are implicit and
inferred from the `DegSpec`, no genus-five call site had to change when this
file stopped being genus-five specific.
-/

namespace AtanasovRanganathan.ConfigurationCommon

open Utilities

open Certificate
open Certificate.ExplicitPotential
open Certificate.DegenerateSpec
open Certificate.DegenerateSpec.DegSpec

variable {n p : ℕ}

/-! ### The one-slot ramp lemmas -/

/-- The first slope of a truncated negative ramp consumes one chip. -/
theorem firstStep_neg_eq_neg_one {L k : ℕ} (hk : 0 < k) (hkL : k ≤ L) :
    SubdivisionArithmetic.step L (-(k : ℤ)) 0 = -1 := by
  rw [SubdivisionArithmetic.step_neg_eq_ite hk hkL]
  simp [hk]

/-- The last slope of a positive ramp consumes one chip at its head. -/
theorem lastStep_pos_eq_one {L k : ℕ} (hk : 0 < k) (hkL : k ≤ L) :
    SubdivisionArithmetic.step L (k : ℤ) (L - 1) = 1 := by
  have hL : 0 < L := lt_of_lt_of_le hk hkL
  rw [SubdivisionArithmetic.lastStep_eq_neg_ediv_neg (k : ℤ) hL]
  change -SubdivisionArithmetic.quotient L (-(k : ℤ)) = 1
  rw [SubdivisionArithmetic.quotient_neg_eq_neg_one hk hkL]
  norm_num

/-- A ramp whose height equals the whole arm delivers one chip at its tail. -/
theorem firstStep_full_eq_one {L : ℕ} (hL : 0 < L) :
    SubdivisionArithmetic.step L (L : ℤ) 0 = 1 := by
  rw [SubdivisionArithmetic.firstStep_eq_quotient (L : ℤ) hL]
  simp [SubdivisionArithmetic.quotient, hL.ne']

/-- A reversed full-arm ramp delivers one chip at its head. -/
theorem lastStep_neg_full_eq_neg_one {L : ℕ} (hL : 0 < L) :
    SubdivisionArithmetic.step L (-(L : ℤ)) (L - 1) = -1 := by
  rw [SubdivisionArithmetic.step_neg_eq_ite hL le_rfl]
  simp [hL]

theorem firstStep_pos_nonneg {L k : ℕ} (hL : 0 < L) :
    0 ≤ SubdivisionArithmetic.step L (k : ℤ) 0 := by
  apply SubdivisionArithmetic.lower_le_step_of_mul_le (k : ℤ) 0 hL
  simp

theorem lastStep_neg_nonpos {L k : ℕ} (hk : 0 < k) (hkL : k ≤ L) :
    SubdivisionArithmetic.step L (-(k : ℤ)) (L - 1) ≤ 0 := by
  rw [SubdivisionArithmetic.step_neg_eq_ite hk hkL]
  split_ifs <;> omega

/-! ### The one-class potential -/

/-- Negative height on one contracted class and zero on all other classes. -/
def centerPotential (d : DegSpec n p) (center : Fin n) (height : ℕ)
    (v : Fin n) : ℤ :=
  if d.rep v = d.rep center then -(height : ℤ) else 0

theorem centerPotential_repInvariant (d : DegSpec n p)
    (center : Fin n) (height : ℕ) :
    d.RepInvariant (centerPotential d center height) := by
  intro v
  simp only [centerPotential, d.rep_idem]

theorem centerPotential_eq_of_singleton
    (d : DegSpec n p) (center : Fin n) (height : ℕ)
    (hSingleton : ∀ v : Fin n, d.rep v = d.rep center ↔ v = center)
    (v : Fin n) :
    centerPotential d center height v =
      if v = center then -(height : ℤ) else 0 := by
  simp only [centerPotential]
  rw [if_congr (hSingleton v) rfl rfl]

/-! ### Endpoint bookkeeping -/

/-- The per-source-core endpoint contribution used by the class-sum formula. -/
def endpointContribution (d : DegSpec n p) (potential : Fin n → ℤ)
    (v : Fin n) : ℤ :=
  ∑ e : Fin p,
    ((if d.core.tail e = v then
        SubdivisionArithmetic.step (d.length e) (d.coreRise potential e) 0
      else 0) +
    (if d.core.head e = v then
        -SubdivisionArithmetic.step (d.length e) (d.coreRise potential e)
          (d.length e - 1)
      else 0))

/-- The two endpoint terms contributed by one original core slot to one
contracted core class.  Keeping them paired is essential on a closed face:
when a zero slot is contracted, its two artificial endpoint terms cancel. -/
def endpointPair (d : DegSpec n p) (potential : Fin n → ℤ)
    (e : Fin p) (r : Fin n) : ℤ :=
  (if d.rep (d.core.tail e) = d.rep r then
      SubdivisionArithmetic.step (d.length e) (d.coreRise potential e) 0
    else 0) +
  (if d.rep (d.core.head e) = d.rep r then
      -SubdivisionArithmetic.step (d.length e) (d.coreRise potential e)
        (d.length e - 1)
    else 0)

theorem zero_rise_endpoint_pair (d : DegSpec n p) (e : Fin p) (r : Fin n) :
    (if d.rep (d.core.tail e) = d.rep r then
        SubdivisionArithmetic.step (d.length e) 0 0 else 0) +
      (if d.rep (d.core.head e) = d.rep r then
        -SubdivisionArithmetic.step (d.length e) 0 (d.length e - 1)
        else 0) = 0 := by
  rcases Nat.eq_zero_or_pos (d.length e) with hZero | hPos
  · have hRep := d.rep_zero e hZero
    rw [hZero, hRep]
    by_cases h : d.rep (d.core.head e) = d.rep r <;> simp [h]
  · have hFirst := SubdivisionArithmetic.step_zero_of_lt
      (L := d.length e) (i := 0) hPos
    have hLast := SubdivisionArithmetic.step_zero_of_lt
      (L := d.length e) (i := d.length e - 1) (by omega)
    rw [hFirst, hLast]
    simp

theorem endpointPair_eq_zero_of_rise_eq_zero
    (d : DegSpec n p) (potential : Fin n → ℤ) (e : Fin p) (r : Fin n)
    (hRise : d.coreRise potential e = 0) :
    endpointPair d potential e r = 0 := by
  simp only [endpointPair, hRise]
  exact zero_rise_endpoint_pair d e r

/-! ### Redistributing chips inside contracted classes

A chip may be delivered to a vertex of the target's class other than the
target itself, and a collapsed arm may put its chip in the centre's class.
Both are handled by moving weight *within* a class, which leaves every class
sum -- hence the divisor -- unchanged. -/

def indicatorWeight (vertex source : Fin n) : ℤ :=
  if vertex = source then 1 else 0

def transferWeight (source target vertex : Fin n) : ℤ :=
  indicatorWeight vertex target - indicatorWeight vertex source

theorem sum_transferWeight_eq_zero
    (d : DegSpec n p) {source target : Fin n}
    (hRep : d.rep source = d.rep target) (r : Fin n) :
    ∑ v ∈ Finset.univ.filter (fun v : Fin n => d.rep v = d.rep r),
      transferWeight source target v = 0 := by
  classical
  have hMem : d.rep source = d.rep r ↔ d.rep target = d.rep r := by
    rw [hRep]
  simp [transferWeight, indicatorWeight, hMem]

theorem sum_indicatorWeight_class
    (d : DegSpec n p) (source r : Fin n) :
    ∑ v ∈ Finset.univ.filter (fun v : Fin n => d.rep v = d.rep r),
        indicatorWeight v source =
      if d.rep source = d.rep r then 1 else 0 := by
  classical
  simp [indicatorWeight]

/-! ### Endpoint accounting on the contracted face -/

/-- Endpoint contribution with the artificial endpoints of a zero slot
suppressed.  Those two terms cancel after passing to a contracted class. -/
def positiveEndpointContribution (d : DegSpec n p)
    (potential : Fin n → ℤ) (v : Fin n) : ℤ :=
  ∑ e : Fin p,
    if d.length e = 0 then 0 else
      ((if d.core.tail e = v then
          SubdivisionArithmetic.step (d.length e) (d.coreRise potential e) 0
        else 0) +
      (if d.core.head e = v then
          -SubdivisionArithmetic.step (d.length e) (d.coreRise potential e)
            (d.length e - 1)
        else 0))

theorem positiveEndpointContribution_classSum_eq
    (d : DegSpec n p) (potential : Fin n → ℤ)
    (hInv : d.RepInvariant potential) (r : Fin n) :
    ∑ v ∈ Finset.univ.filter (fun v : Fin n => d.rep v = d.rep r),
        positiveEndpointContribution d potential v =
      prin d.graph (d.interpolatedScript potential) (d.coreVertex r) := by
  classical
  rw [d.prin_interpolatedScript_coreVertex_eq_endpointSum hInv]
  unfold positiveEndpointContribution
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _he
  by_cases hZero : d.length e = 0
  · have hRep := d.rep_zero e hZero
    have hRise : d.coreRise potential e = 0 := by
      unfold DegSpec.coreRise
      rw [← hInv (d.core.tail e), ← hInv (d.core.head e), hRep]
      omega
    simp only [hZero, if_true, Finset.sum_const_zero]
    rw [hRep]
    by_cases h : d.rep (d.core.head e) = d.rep r <;>
      simp [h, hRise]
  · simp only [hZero, if_false, Finset.sum_add_distrib]
    by_cases hTail : d.rep (d.core.tail e) = d.rep r <;>
      by_cases hHead : d.rep (d.core.head e) = d.rep r <;>
      simp [hTail, hHead]

end AtanasovRanganathan.ConfigurationCommon
