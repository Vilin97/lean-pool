/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.DegenerateSlopeScript
import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.SubdivisionCoreSupport
import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.TwoPoleSubdivision
import LeanPool.BrillNoetherGraphs.Utilities.Foundations.ConvexIntegerRounding
import LeanPool.BrillNoetherGraphs.Utilities.Foundations.CommonOffsetRounding
import LeanPool.BrillNoetherGraphs.Utilities.Foundations.ScriptClamping
import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.ContractionForestCensusGeneral
import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.DegenerateSeparator
import LeanPool.BrillNoetherGraphs.Utilities.Foundations.RankOne

/-!
# Transferring a script by comparing path endpoint slopes

A source subdivision replaces every vanishing slot by one unit edge.
After summing over contraction classes those edges cancel. On surviving
slots, increasing the outgoing endpoint contributions preserves effectivity.
This isolates the graph bookkeeping from the integer rounding argument.
-/

namespace Utilities.Certificate.DiscreteSpecialization

open Finset ExplicitPotential SubdivisionGraph DegenerateSpec
open Utilities.Subdivision.SubdivisionCoreSupport
open TwoPoleSubdivision

variable {n p : ℕ}

/-- The source endpoint sum, regrouped by target contraction classes. -/
theorem source_prin_classSum (d : DegSpec n p) (s : Spec n p)
    (hCore : s.core = d.core) (f : firing_script s.graph) (r : Fin n) :
    (∑ v ∈ univ.filter (fun v : Fin n => d.rep v = d.rep r),
      prin s.graph f (s.coreVertex v)) =
    ∑ e : Fin p,
      ((if d.rep (d.core.tail e) = d.rep r then
          pathValue s f e 1 - pathValue s f e 0 else 0) +
        (if d.rep (d.core.head e) = d.rep r then
          -(pathValue s f e (s.length e - 1 + 1) -
            pathValue s f e (s.length e - 1)) else 0)) := by
  simp_rw [s.prin_coreVertex_eq_endpointSum (pathValue_slope s f), hCore]
  rw [sum_add_distrib, d.sum_tail_class, d.sum_head_class, ← sum_add_distrib]
  apply sum_congr rfl
  intro v _
  exact sum_add_distrib

/-- Only endpoint comparisons and interior convexity are needed to transfer
effectivity. Both scripts are actual functions on their respective graphs. -/
theorem effective_of_endpoint_comparison (d : DegSpec n p) (s : Spec n p)
    (hCore : s.core = d.core)
    (hZero : ∀ e, d.length e = 0 → s.length e = 1)
    (weight : Fin n → ℤ) (f : firing_script s.graph)
    (hf : effective (coreDivisor s weight + prin s.graph f))
    (g : firing_script d.graph) (slope : Fin p → ℕ → ℤ)
    (hg : d.IsStepSlope g slope)
    (hTail : ∀ e, 0 < d.length e →
      pathValue s f e 1 - pathValue s f e 0 ≤ slope e 0)
    (hHead : ∀ e, 0 < d.length e →
      slope e (d.length e - 1) ≤
        pathValue s f e (s.length e - 1 + 1) -
          pathValue s f e (s.length e - 1))
    (hInterior : ∀ e (k : Fin (d.length e - 1)),
      slope e k.val ≤ slope e (k.val + 1)) :
    effective (d.coreClassDivisor weight + prin d.graph g) := by
  classical
  have hCoreLe (r : Fin n) :
      (∑ v ∈ univ.filter (fun v : Fin n => d.rep v = d.rep r),
        prin s.graph f (s.coreVertex v)) ≤ prin d.graph g (d.coreVertex r) := by
    rw [source_prin_classSum d s hCore f r,
      d.prin_coreVertex_eq_endpointSum hg]
    apply sum_le_sum
    intro e _
    by_cases he : d.length e = 0
    · rw [he, hZero e he]
      simp only [Nat.sub_self, Nat.zero_add, Nat.zero_sub]
      rw [d.rep_zero e he]
      split_ifs <;> omega
    · have hp : 0 < d.length e := Nat.pos_of_ne_zero he
      have ht := hTail e hp
      have hh := hHead e hp
      split_ifs <;> omega
  intro z
  rcases z with c | ⟨e, k⟩
  · have hSum := sum_nonneg fun v
        (_ : v ∈ univ.filter (fun v : Fin n => d.rep v = d.rep c.val)) =>
      hf (s.coreVertex v)
    simp only [Pi.add_apply, coreDivisor_coreVertex, sum_add_distrib] at hSum
    have hLe := hCoreLe c.val
    have hc : d.coreVertex c.val = Sum.inl c := by
      apply congrArg Sum.inl
      exact Subtype.ext c.property
    rw [hc] at hLe
    simp only [Pi.add_apply, DegSpec.coreClassDivisor]
    rw [c.property] at hSum hLe
    omega
  · change 0 ≤ 0 + prin d.graph g (d.interiorVertex e k)
    rw [d.prin_interiorVertex_eq_slopeDifference hg]
    have := hInterior e k
    omega

end Utilities.Certificate.DiscreteSpecialization

/-!
# Rounded firing scripts on a contracted subdivision

An effective translate of a core-supported divisor makes the source script
convex along every slot. Sample its values every `N` steps and use one common
rounding offset. If the rounded core values agree on contraction classes,
they define a script on the target graph. Convex block estimates then give
the endpoint comparisons and interior convexity needed to retain effectivity.
-/

namespace Utilities.Certificate.DiscreteSpecialization

open SubdivisionGraph DegenerateSpec TwoPoleSubdivision
open Utilities.Subdivision.SubdivisionCoreSupport
open Utilities.CommonOffsetRounding

variable {n p : ℕ}

/-- A winning script for a core-supported divisor has nondecreasing unit
slopes along every slot, since there are no prescribed interior chips. -/
theorem winning_path_slopes_mono (s : Spec n p) (weight : Fin n → ℤ)
    (f : firing_script s.graph)
    (hf : effective (coreDivisor s weight + prin s.graph f)) (e : Fin p) :
    ∀ a b : ℕ, a ≤ b → b < s.length e →
      ConvexIntegerRounding.slope (pathValue s f e) a ≤
        ConvexIntegerRounding.slope (pathValue s f e) b := by
  apply ConvexIntegerRounding.slopes_mono_of_adjacent
  intro i hi
  let vertex : Fin (s.length e - 1) := ⟨i, by omega⟩
  have h := hf (s.interiorVertex e vertex)
  change 0 ≤ 0 + prin s.graph f (s.interiorVertex e vertex) at h
  rw [s.prin_interiorVertex_eq_slopeDifference (pathValue_slope s f)] at h
  change 0 ≤ 0 +
    (ConvexIntegerRounding.slope (pathValue s f e) (i + 1) -
      ConvexIntegerRounding.slope (pathValue s f e) i) at h
  omega

/-- Common-offset rounding transfers an effective translate to the target
subdivision once its rounded core values are constant on contracted classes.
No nonnegativity assumption on the initial core weights is needed. -/
theorem rounded_script_effective (d : DegSpec n p) (s : Spec n p)
    (hCore : s.core = d.core) (N : ℕ) (hN : 0 < N)
    (hZero : ∀ e, d.length e = 0 → s.length e = 1)
    (hPos : ∀ e, 0 < d.length e → s.length e = N * d.length e)
    (weight : Fin n → ℤ) (f : firing_script s.graph)
    (hf : effective (coreDivisor s weight + prin s.graph f)) (k : Fin N)
    (hConst : ∀ u v : Fin n, d.rep u = d.rep v →
      round N k (f (s.coreVertex u)) = round N k (f (s.coreVertex v))) :
    ∃ g : firing_script d.graph,
      effective (d.coreClassDivisor weight + prin d.graph g) := by
  let potential : Fin n → ℤ := fun v => round N k (f (s.coreVertex v))
  let values : Fin p → ℕ → ℤ := fun e j =>
    round N k (pathValue s f e (N * j))
  have hRep (v : Fin n) : potential v = potential (d.rep v) := by
    apply hConst v (d.rep v)
    rw [d.rep_idem]
  have hCompatible : d.SlotValueCompatible potential values := by
    constructor
    · intro e
      simp only [values, Nat.mul_zero, pathValue_zero, hCore]
      exact hRep (d.core.tail e)
    · intro e
      by_cases he : d.length e = 0
      · simp only [values, he, Nat.mul_zero, pathValue_zero, hCore]
        exact (hConst (d.core.tail e) (d.core.head e) (d.rep_zero e he)).trans
          (hRep (d.core.head e))
      · have hp : 0 < d.length e := Nat.pos_of_ne_zero he
        simp only [values, ← hPos e hp, pathValue_length, hCore]
        exact hRep (d.core.head e)
  let coarseSlope : Fin p → ℕ → ℤ := fun e j => values e (j + 1) - values e j
  refine ⟨d.slotValueScript potential values, ?_⟩
  apply effective_of_endpoint_comparison d s hCore hZero weight f hf
    (d.slotValueScript potential values) coarseSlope
    (d.isStepSlope_slotValueScript hCompatible)
  · intro e hp
    have hBlock : N * (0 + 1) ≤ s.length e := by
      rw [hPos e hp]
      exact Nat.mul_le_mul_left N hp
    have h := ConvexIntegerRounding.rounded_block_slope_bounds N hN k
      (pathValue s f e) (s.length e) (winning_path_slopes_mono s weight f hf e)
      0 hBlock
    simpa only [coarseSlope, values, ConvexIntegerRounding.slope,
      Nat.mul_zero, Nat.zero_add] using h.1
  · intro e hp
    have hEnd : N * (d.length e - 1 + 1) = s.length e := by
      rw [Nat.sub_add_cancel hp, hPos e hp]
    have h := ConvexIntegerRounding.rounded_block_slope_bounds N hN k
      (pathValue s f e) (s.length e) (winning_path_slopes_mono s weight f hf e)
      (d.length e - 1) hEnd.le
    simpa only [coarseSlope, values, ConvexIntegerRounding.slope, hEnd] using h.2
  · intro e j
    have hp : 0 < d.length e := by have := j.isLt; omega
    have hTwo : N * (j.val + 2) ≤ s.length e := by
      rw [hPos e hp]
      exact Nat.mul_le_mul_left N (by have := j.isLt; omega)
    have h := ConvexIntegerRounding.rounded_slopes_nondecreasing N hN k
      (pathValue s f e) (s.length e) (winning_path_slopes_mono s weight f hf e)
      j.val hTwo
    simpa only [coarseSlope, values, ConvexIntegerRounding.slope] using h

end Utilities.Certificate.DiscreteSpecialization

/-!
# Finite specialization by a common rounding offset

Stretch surviving lengths by `N` and replace vanishing slots by unit edges.
When `N` exceeds the degree bound times the number of vanishing slots,
integer rounding turns a winning core-supported script into a winning
script on the contracted graph. No metric graph or limiting argument enters.
-/

namespace Utilities.Certificate.DiscreteSpecialization

open Finset ExplicitPotential SubdivisionGraph DegenerateSpec
open ContractionForestCensusGeneral
open Utilities.Subdivision.SubdivisionCoreSupport
open TwoPoleSubdivision
open Utilities.CommonOffsetRounding

variable {n p : ℕ}

/-- The positive graph used to prove a specified contraction face. -/
def stretch (d : DegSpec n p) (N : ℕ) (hN : 0 < N)
    (hLoopless : ∀ e, d.core.tail e ≠ d.core.head e) : Spec n p where
  core := d.core
  length e := if d.length e = 0 then 1 else N * d.length e
  core_nonempty := d.core_nonempty
  core_loopless := hLoopless
  length_pos e := by
    split_ifs with h
    · omega
    · exact Nat.mul_pos hN (Nat.pos_of_ne_zero h)

@[simp] theorem stretch_core (d : DegSpec n p) (N : ℕ) (hN : 0 < N)
    (hLoopless : ∀ e, d.core.tail e ≠ d.core.head e) :
    (stretch d N hN hLoopless).core = d.core := rfl

theorem stretch_length_zero (d : DegSpec n p) (N : ℕ) (hN : 0 < N)
    (hLoopless : ∀ e, d.core.tail e ≠ d.core.head e) (e : Fin p)
    (he : d.length e = 0) : (stretch d N hN hLoopless).length e = 1 := by
  simp [stretch, he]

theorem stretch_length_pos (d : DegSpec n p) (N : ℕ) (hN : 0 < N)
    (hLoopless : ∀ e, d.core.tail e ≠ d.core.head e) (e : Fin p)
    (he : 0 < d.length e) :
    (stretch d N hN hLoopless).length e = N * d.length e := by
  simp [stretch, he.ne']

/-- Equality on zero-slot endpoints propagates through the actual contraction
relation. A bare cardinality condition on the representative map would not
be enough here. -/
theorem constant_on_classes (d : DegSpec n p)
    (hRep : ∀ u v, d.rep u = d.rep v →
      ReachIn d.core (univ.filter (fun e => d.length e = 0)) u v)
    (potential : Fin n → ℤ)
    (hZero : ∀ e, d.length e = 0 →
      potential (d.core.tail e) = potential (d.core.head e)) :
    ∀ u v, d.rep u = d.rep v → potential u = potential v := by
  intro u v huv
  have h := hRep u v huv
  clear huv
  induction h with
  | refl => rfl
  | @tail b c _ hbc ih =>
    obtain ⟨e, he, hcase⟩ := hbc
    have hz : d.length e = 0 := by
      have hm := (mem_edgeList _ e).mp he
      simpa using hm
    rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ih.trans (hZero e hz)
    · exact ih.trans (hZero e hz).symm

/-- A winning script has a common rounding offset that agrees throughout
each contracted component. The degree bound may use any effective majorant
of its signed starting divisor. -/
theorem exists_descending_offset (d : DegSpec n p) (N : ℕ) (hN : 0 < N)
    (hLoopless : ∀ e, d.core.tail e ≠ d.core.head e)
    (hRep : ∀ u v, d.rep u = d.rep v →
      ReachIn d.core (univ.filter (fun e => d.length e = 0)) u v)
    (weight majorant : Fin n → ℤ)
    (hMajorant : ∀ v, 0 ≤ majorant v) (hLe : ∀ v, weight v ≤ majorant v)
    (hBudget : ((univ.filter (fun e => d.length e = 0)).card : ℤ) *
      (∑ v, majorant v) < (N : ℤ))
    (f : firing_script (stretch d N hN hLoopless).graph)
    (hf : effective (coreDivisor (stretch d N hN hLoopless) weight +
      prin (stretch d N hN hLoopless).graph f)) :
    ∃ k : Fin N, ∀ u v, d.rep u = d.rep v →
      round N k (f ((stretch d N hN hLoopless).coreVertex u)) =
        round N k (f ((stretch d N hN hLoopless).coreVertex v)) := by
  classical
  let s := stretch d N hN hLoopless
  let F := univ.filter (fun e : Fin p => d.length e = 0)
  have hDivLe : ∀ v, coreDivisor s weight v ≤ coreDivisor s majorant v := by
    intro v
    cases v with
    | inl v => exact hLe v
    | inr _ => rfl
  have hSlope (e : Fin p) (he : e ∈ F) :
      |f (s.coreVertex (d.core.tail e)) - f (s.coreVertex (d.core.head e))| ≤
        ∑ v, majorant v := by
    have hz : d.length e = 0 := (mem_filter.mp he).2
    have hEdge : 0 < num_edges s.graph (s.coreVertex (d.core.tail e))
        (s.coreVertex (d.core.head e)) := by
      have hh := s.unitStep_num_edges_pos e ⟨0, s.length_pos e⟩
      simpa [Spec.stepLeft, Spec.stepRight, s, stretch, hz] using hh
    have hh := Utilities.abs_script_sub_le_deg_of_le
      (coreDivisor_effective s majorant hMajorant) hDivLe hf hEdge
    simpa only [deg_coreDivisor] using hh
  have hTotal :
      (∑ e ∈ F, |f (s.coreVertex (d.core.tail e)) -
        f (s.coreVertex (d.core.head e))|) < (N : ℤ) := by
    calc
      _ ≤ ∑ _e ∈ F, (∑ v, majorant v) := sum_le_sum hSlope
      _ = (F.card : ℤ) * (∑ v, majorant v) := by simp
      _ < (N : ℤ) := hBudget
  obtain ⟨k, hk⟩ := exists_common_offset N hN F
    (fun e => f (s.coreVertex (d.core.tail e)))
    (fun e => f (s.coreVertex (d.core.head e))) hTotal
  refine ⟨k, constant_on_classes d hRep
    (fun v => round N k (f (s.coreVertex v))) ?_⟩
  intro e he
  exact hk e (by simp [F, he])

/-- Quantitative discrete specialization of a core-supported winning script.
The graph is stretched only once; the offset depends on the script. -/
theorem winning_script_coreClassDivisor_of_stretch
    (d : DegSpec n p) (N : ℕ) (hN : 0 < N)
    (hLoopless : ∀ e, d.core.tail e ≠ d.core.head e)
    (hRep : ∀ u v, d.rep u = d.rep v →
      ReachIn d.core (univ.filter (fun e => d.length e = 0)) u v)
    (weight majorant : Fin n → ℤ)
    (hMajorant : ∀ v, 0 ≤ majorant v) (hLe : ∀ v, weight v ≤ majorant v)
    (hBudget : ((univ.filter (fun e => d.length e = 0)).card : ℤ) *
      (∑ v, majorant v) < (N : ℤ))
    (f : firing_script (stretch d N hN hLoopless).graph)
    (hf : effective (coreDivisor (stretch d N hN hLoopless) weight +
      prin (stretch d N hN hLoopless).graph f)) :
    ∃ g : firing_script d.graph, effective (d.coreClassDivisor weight + prin d.graph g) := by
  obtain ⟨k, hk⟩ := exists_descending_offset d N hN hLoopless hRep
    weight majorant hMajorant hLe hBudget f hf
  exact rounded_script_effective d (stretch d N hN hLoopless) rfl N hN
    (stretch_length_zero d N hN hLoopless)
    (stretch_length_pos d N hN hLoopless) weight f hf k hk

/-- Winnability descends from one sufficiently stretched positive instance.
The signed source weights may have any effective pointwise majorant. -/
theorem winnable_coreClassDivisor_of_stretch
    (d : DegSpec n p) (N : ℕ) (hN : 0 < N)
    (hLoopless : ∀ e, d.core.tail e ≠ d.core.head e)
    (hRep : ∀ u v, d.rep u = d.rep v →
      ReachIn d.core (univ.filter (fun e => d.length e = 0)) u v)
    (weight majorant : Fin n → ℤ)
    (hMajorant : ∀ v, 0 ≤ majorant v) (hLe : ∀ v, weight v ≤ majorant v)
    (hBudget : ((univ.filter (fun e => d.length e = 0)).card : ℤ) *
      (∑ v, majorant v) < (N : ℤ))
    (hWin : winnable (stretch d N hN hLoopless).graph
      (coreDivisor (stretch d N hN hLoopless) weight)) :
    winnable d.graph (d.coreClassDivisor weight) := by
  let s := stretch d N hN hLoopless
  obtain ⟨W, hW, hEquiv⟩ := hWin
  obtain ⟨f, hf⟩ := (principal_iff_eq_prin s.graph _).mp hEquiv
  have hWinning : effective (coreDivisor s weight + prin s.graph f) := by
    have hEq : coreDivisor s weight + prin s.graph f = W := by
      rw [← hf]
      abel
    rwa [hEq]
  obtain ⟨g, hg⟩ := winning_script_coreClassDivisor_of_stretch d N hN hLoopless
    hRep weight majorant hMajorant hLe hBudget f hWinning
  refine ⟨d.coreClassDivisor weight + prin d.graph g, hg, ?_⟩
  apply (principal_iff_eq_prin d.graph _).mpr
  exact ⟨g, by abel⟩

end Utilities.Certificate.DiscreteSpecialization

/-!
# Closing a fixed rank-one divisor over contraction faces

A nonnegative core weight with rank at least one on every positive integer
subdivision keeps rank at least one after the zero-length slots contract.
For each demanded core chip, finite specialization uses the original weight
as its effective majorant. The existing closed-face separator supplies the
remaining subdivision-interior rank tests.
-/

namespace Utilities.Certificate.DiscreteSpecialization

open Finset ExplicitPotential SubdivisionGraph DegenerateSpec
open ContractionForestCensusGeneral
open Utilities.Subdivision.SubdivisionCoreSupport

variable {n p : ℕ}

/-- Subtract one chip at a named original core vertex. -/
def subChipWeight (weight : Fin n → ℤ) (anchor v : Fin n) : ℤ :=
  weight v - if v = anchor then 1 else 0

/-- Subtracting a named core chip commutes with positive subdivision. -/
theorem coreDivisor_subChipWeight (s : Spec n p)
    (weight : Fin n → ℤ) (anchor : Fin n) :
    coreDivisor s (subChipWeight weight anchor) =
      coreDivisor s weight - one_chip (s.coreVertex anchor) := by
  funext x
  rcases x with v | interior
  · simp [coreDivisor, subChipWeight, one_chip, Spec.coreVertex]
  · simp [coreDivisor, one_chip, Spec.coreVertex]

/-- A single named chip pushes to a single chip on its contracted class,
even when other original vertices belong to that class. -/
theorem coreClassDivisor_subChipWeight (d : DegSpec n p)
    (weight : Fin n → ℤ) (anchor : Fin n) :
    d.coreClassDivisor (subChipWeight weight anchor) =
      d.coreClassDivisor weight - one_chip (d.coreVertex anchor) := by
  classical
  funext x
  rcases x with c | interior
  · simp [DegSpec.coreClassDivisor, subChipWeight, Finset.sum_sub_distrib,
      one_chip, DegSpec.coreVertex, Subtype.ext_iff, eq_comm]
  · simp [DegSpec.coreClassDivisor, one_chip, DegSpec.coreVertex]

/-- A core-supported rank-one divisor on one sufficiently stretched graph
already gives rank one after contraction. Its weights need not belong to a
single family that works on every positive subdivision. -/
theorem rank_ge_one_coreClassDivisor_of_stretch
    (d : DegSpec n p) (N : ℕ) (hN : 0 < N)
    (hConnected : d.core.Connected)
    (hLoopless : ∀ e, d.core.tail e ≠ d.core.head e)
    (hRep : ∀ u v, d.rep u = d.rep v →
      ReachIn d.core (univ.filter (fun e => d.length e = 0)) u v)
    (weight : Fin n → ℤ) (hWeight : ∀ v, 0 ≤ weight v)
    (hBudget : ((univ.filter (fun e => d.length e = 0)).card : ℤ) *
      (∑ v, weight v) < (N : ℤ))
    (hRank : rank (stretch d N hN hLoopless).graph
      (coreDivisor (stretch d N hN hLoopless) weight) ≥ 1) :
    rank d.graph (d.coreClassDivisor weight) ≥ 1 := by
  let s := stretch d N hN hLoopless
  apply d.rank_ge_one_of_reaches_coreVertices hConnected
  intro anchor
  have hWin : winnable s.graph (coreDivisor s (subChipWeight weight anchor)) := by
    rw [coreDivisor_subChipWeight]
    exact (rank_ge_one_iff_winnable_sub_one_chip _ _).mp hRank (s.coreVertex anchor)
  have hLe : ∀ v, subChipWeight weight anchor v ≤ weight v := by
    intro v
    unfold subChipWeight
    split_ifs <;> omega
  have hTransferred := winnable_coreClassDivisor_of_stretch d N hN hLoopless hRep
    (subChipWeight weight anchor) weight hWeight hLe hBudget hWin
  change winnable d.graph (d.coreClassDivisor weight - one_chip (d.coreVertex anchor))
  simpa only [coreClassDivisor_subChipWeight] using hTransferred

/-- Fixed nonnegative core weights that have rank one on every positive
subdivision retain rank one on any actual closed contraction face. -/
theorem rank_ge_one_coreClassDivisor_of_positive
    (d : DegSpec n p) (hConnected : d.core.Connected)
    (hLoopless : ∀ e, d.core.tail e ≠ d.core.head e)
    (hRep : ∀ u v, d.rep u = d.rep v →
      ReachIn d.core (univ.filter (fun e => d.length e = 0)) u v)
    (weight : Fin n → ℤ) (hWeight : ∀ v, 0 ≤ weight v)
    (hPositive : ∀ s : Spec n p, s.core = d.core →
      rank s.graph (coreDivisor s weight) ≥ 1) :
    rank d.graph (d.coreClassDivisor weight) ≥ 1 := by
  classical
  let F := univ.filter (fun e : Fin p => d.length e = 0)
  let degree : ℤ := ∑ v : Fin n, weight v
  have hDegree : 0 ≤ degree := Finset.sum_nonneg (fun v _ => hWeight v)
  let N : ℕ := degree.toNat * F.card + 1
  have hN : 0 < N := by dsimp [N]; omega
  have hBudget : (F.card : ℤ) * degree < (N : ℤ) := by
    have hCast : (degree.toNat : ℤ) = degree := Int.toNat_of_nonneg hDegree
    have hNcast : (N : ℤ) = degree * (F.card : ℤ) + 1 := by
      simp only [N, Nat.cast_add, Nat.cast_mul, Nat.cast_one, hCast]
    rw [hNcast]
    nlinarith
  exact rank_ge_one_coreClassDivisor_of_stretch d N hN hConnected hLoopless hRep
    weight hWeight hBudget (hPositive _ rfl)

end Utilities.Certificate.DiscreteSpecialization
