/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.StableCollarRelativeSubdivisionExact
import Mathlib.Topology.UniformSpace.HeineCantor
/-!
# Zero-free endpoint bridges for stable regular approximations

A stable regular approximation stores a finite family of refined vertex samples and a zero-free
straight-line comparison between the original map and their affine interpolation on every refined
top simplex.  For the relative collar we need a genuine global endpoint map whose values at those
refined vertices are exactly the stored samples.

The construction below does not attempt to glue the local affine formulas globally.  Instead it
uses a finite, localized correction of the original map.

* Include every prime translate of every refined endpoint vertex in a finite sample family.
* Around each sample point, the straight segment from the original map to the approximation's
  global sampling map remains zero-free on a sufficiently small ball.
* A finite continuous bump is one at every sample point and supported in the union of those safe
  balls.
* Averaging the bump over the prime group makes it invariant without changing its value on the
  invariant sample family or enlarging its support outside the safe locus.
* Blending the original map with the sampling map by this invariant bump gives a continuous,
  equivariant, zero-free global map.  It agrees exactly with the approximation at every refined
  vertex, and the straight line from the original map to the blended map is zero-free.

Thus every `StableRegularApproximation` canonically determines the
`ZeroFreeEndpointInterpolant` required by the exact relative-collar interface.
-/

namespace NRR

open scoped BigOperators
open FoxNeuwirthOrderComplex

namespace FoxNeuwirthOrderComplex
namespace EquivariantPrismStableRelativeBoundary
namespace StableEndpointBridges

open EquivariantCoordinateHomotopy
open RefinedAffineMap
open StableCollarRelativeSubdivisionExact

variable {p : Nat}

/-- Pointwise straight-segment safety between two coordinate maps. -/
def SegmentSafe
    (F G : ContinuousCoordinateMap p) (x : Realization p) : Prop :=
  ∀ t : Set.Icc (0 : Real) 1,
    (1 - t.1) • F x + t.1 • G x ≠ 0

/-- The jointly continuous straight-segment evaluation map. -/
noncomputable def segmentFamily
    (F G : ContinuousCoordinateMap p) :
    C(Realization p × Set.Icc (0 : Real) 1, Fin p → Real) where
  toFun z := (1 - z.2.1) • F z.1 + z.2.1 • G z.1
  continuous_toFun := by fun_prop

/-- A safe segment at one point has a positive norm margin, uniformly in the segment parameter. -/
theorem exists_positive_segment_margin_at
    (F G : ContinuousCoordinateMap p) (x : Realization p)
    (hsafe : SegmentSafe F G x) :
    ∃ m : Real, 0 < m ∧ ∀ t : Set.Icc (0 : Real) 1,
      m ≤ ‖(1 - t.1) • F x + t.1 • G x‖ := by
  have hcont : Continuous (fun t : Set.Icc (0 : Real) 1 =>
      ‖(1 - t.1) • F x + t.1 • G x‖) := by
    fun_prop
  obtain ⟨t0, ht0⟩ :=
    IsCompact.exists_isMinOn
      (isCompact_univ : IsCompact (Set.univ : Set (Set.Icc (0 : Real) 1)))
      ⟨⟨0, by norm_num⟩, Set.mem_univ _⟩ hcont.continuousOn
  refine ⟨‖(1 - t0.1) • F x + t0.1 • G x‖,
    norm_pos_iff.mpr (hsafe t0), ?_⟩
  intro t
  exact ht0.2 (Set.mem_univ t)

/-- Segment safety persists on a metric neighborhood of a safe point. -/
theorem exists_segmentSafe_ball
    (F G : ContinuousCoordinateMap p) (x : Realization p)
    (hsafe : SegmentSafe F G x) :
    ∃ r : Real, 0 < r ∧
      ∀ y : Realization p, y ∈ Metric.ball x r → SegmentSafe F G y := by
  obtain ⟨m, hm0, hm⟩ := exists_positive_segment_margin_at F G x hsafe
  have huc : UniformContinuous (segmentFamily F G) :=
    CompactSpace.uniformContinuous_of_continuous (segmentFamily F G).continuous
  obtain ⟨r, hr0, hr⟩ :=
    (Metric.uniformContinuous_iff.1 huc) m hm0
  refine ⟨r, hr0, ?_⟩
  intro y hy t
  have hprod : dist (y, t) (x, t) < r := by
    simpa [Prod.dist_eq] using hy
  have hclose := hr hprod
  intro hzero
  have hnorm :
      ‖(1 - t.1) • F x + t.1 • G x‖ < m := by
    have hd := hclose
    rw [dist_comm, dist_eq_norm] at hd
    have hseg : segmentFamily F G (y, t) = 0 := hzero
    rw [hseg, sub_zero] at hd
    exact hd
  exact (not_lt_of_ge (hm t)) hnorm

/-- One finite index for every prime translate of every refined endpoint vertex. -/
abbrev SampleIndex (hp : Nat.Prime p) (N : Nat) :=
  PrimeSymmetry p × (TopCell hp N × Fin (p - 1 + 1))

/-- Spatial point represented by a sample index. -/
noncomputable def samplePoint
    (hp : Nat.Prime p) (N : Nat) (z : SampleIndex hp N) : Realization p :=
  z.1 • vertex hp N z.2.1 z.2.2

/-- Left multiplication on the group coordinate realizes the prime action on sample points. -/
@[simp] theorem samplePoint_mul
    (hp : Nat.Prime p) (N : Nat)
    (h : PrimeSymmetry p) (z : SampleIndex hp N) :
    samplePoint hp N (h * z.1, z.2) = h • samplePoint hp N z := by
  simp [samplePoint, mul_smul]

/-- Segment safety is transported by prime equivariance. -/
theorem segmentSafe_smul
    (hp : Nat.Prime p)
    (F G : ContinuousCoordinateMap p)
    (hF : IsEquivariantCoordinateMap p F)
    (hG : IsEquivariantCoordinateMap p G)
    {x : Realization p} (hx : SegmentSafe F G x)
    (g : PrimeSymmetry p) :
    SegmentSafe F G (g • x) := by
  intro t
  rw [hF g x, hG g x]
  intro hzero
  apply hx t
  funext j
  have h := congrFun hzero ((PrimeSymmetry.toPerm p g) j)
  simpa [PrimeSymmetry.smul_coordinate_apply, Pi.add_apply, Pi.smul_apply] using h

/-- Segment safety is equivalent along a prime orbit. -/
theorem segmentSafe_smul_iff
    (hp : Nat.Prime p)
    (F G : ContinuousCoordinateMap p)
    (hF : IsEquivariantCoordinateMap p F)
    (hG : IsEquivariantCoordinateMap p G)
    (x : Realization p) (g : PrimeSymmetry p) :
    SegmentSafe F G (g • x) ↔ SegmentSafe F G x := by
  constructor
  · intro h
    have := segmentSafe_smul hp F G hF hG h g⁻¹
    simpa [smul_smul] using this
  · intro h
    exact segmentSafe_smul hp F G hF hG h g

/-- The stored simplexwise straight-line condition is safe at every refined vertex. -/
theorem segmentSafe_refinedVertex
    (hp : Nat.Prime p) (F : ZeroFreeMap hp)
    (A : StableRegularApproximation hp F.map)
    (q : TopCell hp A.toRegularApproximation.level) (i : Fin (p - 1 + 1)) :
    SegmentSafe F.map A.toRegularApproximation.map
      (vertex hp A.toRegularApproximation.level q i) := by
  intro t
  have h := A.toRegularApproximation.zeroFreeStraightLine q
    (StandardSimplex.ofDelta (stdSimplex.vertex (S := Real) i)) t
  have hchart : chart hp A.toRegularApproximation.level q
      (StandardSimplex.toDelta
        (StandardSimplex.ofDelta (stdSimplex.vertex (S := Real) i))) =
      vertex hp A.toRegularApproximation.level q i := by
    rw [StandardSimplex.toDelta_ofDelta]
    rfl
  have hvalue : value hp A.toRegularApproximation.level
      A.toRegularApproximation.map q
      (StandardSimplex.ofDelta (stdSimplex.vertex (S := Real) i)) =
      A.toRegularApproximation.map
        (vertex hp A.toRegularApproximation.level q i) := by
    funext j
    simp [value, vertexValue, StandardSimplex.ofDelta, stdSimplex.vertex,
      Pi.single_apply, ite_mul, Finset.sum_ite_eq']
  rw [hchart, hvalue] at h
  exact h

/-- Every translated endpoint sample has a safe segment to the approximation's sampling map. -/
theorem segmentSafe_samplePoint
    (hp : Nat.Prime p) (F : ZeroFreeMap hp)
    (A : StableRegularApproximation hp F.map)
    (z : SampleIndex hp A.toRegularApproximation.level) :
    SegmentSafe F.map A.toRegularApproximation.map
      (samplePoint hp A.toRegularApproximation.level z) := by
  apply segmentSafe_smul hp F.map A.toRegularApproximation.map
    F.equivariant A.toRegularApproximation.equivariant
  exact segmentSafe_refinedVertex hp F A z.2.1 z.2.2

/-- A chosen positive radius on which one sample's full segment remains safe. -/
noncomputable def sampleRadius
    (hp : Nat.Prime p) (F : ZeroFreeMap hp)
    (A : StableRegularApproximation hp F.map)
    (z : SampleIndex hp A.toRegularApproximation.level) : Real :=
  Classical.choose (exists_segmentSafe_ball
    F.map A.toRegularApproximation.map
    (samplePoint hp A.toRegularApproximation.level z)
    (segmentSafe_samplePoint hp F A z))

@[simp] theorem sampleRadius_pos
    (hp : Nat.Prime p) (F : ZeroFreeMap hp)
    (A : StableRegularApproximation hp F.map)
    (z : SampleIndex hp A.toRegularApproximation.level) :
    0 < sampleRadius hp F A z :=
  (Classical.choose_spec (exists_segmentSafe_ball
    F.map A.toRegularApproximation.map
    (samplePoint hp A.toRegularApproximation.level z)
    (segmentSafe_samplePoint hp F A z))).1

/-- The chosen ball around a sample lies in the pointwise safe locus. -/
theorem segmentSafe_of_mem_sampleBall
    (hp : Nat.Prime p) (F : ZeroFreeMap hp)
    (A : StableRegularApproximation hp F.map)
    (z : SampleIndex hp A.toRegularApproximation.level)
    (x : Realization p)
    (hx : x ∈ Metric.ball
      (samplePoint hp A.toRegularApproximation.level z)
      (sampleRadius hp F A z)) :
    SegmentSafe F.map A.toRegularApproximation.map x :=
  (Classical.choose_spec (exists_segmentSafe_ball
    F.map A.toRegularApproximation.map
    (samplePoint hp A.toRegularApproximation.level z)
    (segmentSafe_samplePoint hp F A z))).2 x hx

/-- Continuous radial bump supported in one chosen safe ball. -/
noncomputable def sampleBump
    (hp : Nat.Prime p) (F : ZeroFreeMap hp)
    (A : StableRegularApproximation hp F.map)
    (z : SampleIndex hp A.toRegularApproximation.level)
    (x : Realization p) : Real :=
  max 0 (1 - dist x (samplePoint hp A.toRegularApproximation.level z) /
    sampleRadius hp F A z)

@[simp] theorem sampleBump_self
    (hp : Nat.Prime p) (F : ZeroFreeMap hp)
    (A : StableRegularApproximation hp F.map)
    (z : SampleIndex hp A.toRegularApproximation.level) :
    sampleBump hp F A z
      (samplePoint hp A.toRegularApproximation.level z) = 1 := by
  simp [sampleBump]

theorem sampleBump_nonneg
    (hp : Nat.Prime p) (F : ZeroFreeMap hp)
    (A : StableRegularApproximation hp F.map)
    (z : SampleIndex hp A.toRegularApproximation.level)
    (x : Realization p) :
    0 ≤ sampleBump hp F A z x := by
  exact le_max_left _ _

theorem sampleBump_le_one
    (hp : Nat.Prime p) (F : ZeroFreeMap hp)
    (A : StableRegularApproximation hp F.map)
    (z : SampleIndex hp A.toRegularApproximation.level)
    (x : Realization p) :
    sampleBump hp F A z x ≤ 1 := by
  unfold sampleBump
  apply max_le
  · exact zero_le_one
  · have hdiv : 0 ≤ dist x (samplePoint hp A.toRegularApproximation.level z) /
        sampleRadius hp F A z :=
      div_nonneg dist_nonneg (le_of_lt (sampleRadius_pos hp F A z))
    linarith

theorem continuous_sampleBump
    (hp : Nat.Prime p) (F : ZeroFreeMap hp)
    (A : StableRegularApproximation hp F.map)
    (z : SampleIndex hp A.toRegularApproximation.level) :
    Continuous (sampleBump hp F A z) := by
  unfold sampleBump
  fun_prop

/-- A positive sample bump certifies membership in its safe ball. -/
theorem mem_sampleBall_of_sampleBump_pos
    (hp : Nat.Prime p) (F : ZeroFreeMap hp)
    (A : StableRegularApproximation hp F.map)
    (z : SampleIndex hp A.toRegularApproximation.level)
    (x : Realization p)
    (hx : 0 < sampleBump hp F A z x) :
    x ∈ Metric.ball
      (samplePoint hp A.toRegularApproximation.level z)
      (sampleRadius hp F A z) := by
  unfold sampleBump at hx
  have hright : 0 < 1 - dist x (samplePoint hp A.toRegularApproximation.level z) /
      sampleRadius hp F A z := by
    rcases lt_max_iff.mp hx with h | h
    · exact (lt_irrefl 0 h).elim
    · exact h
  rw [Metric.mem_ball]
  have hr := sampleRadius_pos hp F A z
  have hdiv : dist x (samplePoint hp A.toRegularApproximation.level z) /
      sampleRadius hp F A z < 1 := by linarith
  exact (div_lt_one hr).mp hdiv

/-- Unsymmetrized finite bump: one on every endpoint sample and supported in the union of safe
sample balls. -/
noncomputable def rawBridgeWeight
    (hp : Nat.Prime p) (F : ZeroFreeMap hp)
    (A : StableRegularApproximation hp F.map)
    (x : Realization p) : Real :=
  min 1 (∑ z : SampleIndex hp A.toRegularApproximation.level,
    sampleBump hp F A z x)

theorem continuous_rawBridgeWeight
    (hp : Nat.Prime p) (F : ZeroFreeMap hp)
    (A : StableRegularApproximation hp F.map) :
    Continuous (rawBridgeWeight hp F A) := by
  unfold rawBridgeWeight
  exact continuous_const.min
    (continuous_finsetSum _ fun z _ => continuous_sampleBump hp F A z)

theorem rawBridgeWeight_nonneg
    (hp : Nat.Prime p) (F : ZeroFreeMap hp)
    (A : StableRegularApproximation hp F.map)
    (x : Realization p) :
    0 ≤ rawBridgeWeight hp F A x := by
  unfold rawBridgeWeight
  apply le_min zero_le_one
  exact Finset.sum_nonneg fun z _ => sampleBump_nonneg hp F A z x

theorem rawBridgeWeight_le_one
    (hp : Nat.Prime p) (F : ZeroFreeMap hp)
    (A : StableRegularApproximation hp F.map)
    (x : Realization p) :
    rawBridgeWeight hp F A x ≤ 1 := by
  exact min_le_left _ _

@[simp] theorem rawBridgeWeight_sample
    (hp : Nat.Prime p) (F : ZeroFreeMap hp)
    (A : StableRegularApproximation hp F.map)
    (z0 : SampleIndex hp A.toRegularApproximation.level) :
    rawBridgeWeight hp F A
      (samplePoint hp A.toRegularApproximation.level z0) = 1 := by
  unfold rawBridgeWeight
  have h0 := Finset.single_le_sum
    (f := fun z : SampleIndex hp A.toRegularApproximation.level =>
      sampleBump hp F A z (samplePoint hp A.toRegularApproximation.level z0))
    (fun z _ => sampleBump_nonneg hp F A z _) (Finset.mem_univ z0)
  have h1 : sampleBump hp F A z0
        (samplePoint hp A.toRegularApproximation.level z0) ≤
      ∑ z : SampleIndex hp A.toRegularApproximation.level,
        sampleBump hp F A z
          (samplePoint hp A.toRegularApproximation.level z0) := h0
  rw [sampleBump_self] at h1
  exact min_eq_left h1

/-- Positivity of the raw bump implies full pointwise segment safety. -/
theorem segmentSafe_of_rawBridgeWeight_pos
    (hp : Nat.Prime p) (F : ZeroFreeMap hp)
    (A : StableRegularApproximation hp F.map)
    (x : Realization p)
    (hx : 0 < rawBridgeWeight hp F A x) :
    SegmentSafe F.map A.toRegularApproximation.map x := by
  have hsum : 0 < ∑ z : SampleIndex hp A.toRegularApproximation.level,
      sampleBump hp F A z x := by
    unfold rawBridgeWeight at hx
    exact lt_of_lt_of_le hx (min_le_right _ _)
  by_contra hnone
  have hall : ∀ z : SampleIndex hp A.toRegularApproximation.level,
      sampleBump hp F A z x = 0 := by
    intro z
    apply le_antisymm
    · apply not_lt.mp
      intro hz
      apply hnone
      exact segmentSafe_of_mem_sampleBall hp F A z x
        (mem_sampleBall_of_sampleBump_pos hp F A z x hz)
    · exact sampleBump_nonneg hp F A z x
  simp [hall] at hsum

/-- Prime-invariant average of the raw bridge weight. -/
noncomputable def bridgeWeight
    (hp : Nat.Prime p) (F : ZeroFreeMap hp)
    (A : StableRegularApproximation hp F.map)
    (x : Realization p) : Real :=
  ((Fintype.card (PrimeSymmetry p) : Real)⁻¹) *
    ∑ g : PrimeSymmetry p, rawBridgeWeight hp F A (g • x)

theorem continuous_bridgeWeight
    (hp : Nat.Prime p) (F : ZeroFreeMap hp)
    (A : StableRegularApproximation hp F.map) :
    Continuous (bridgeWeight hp F A) := by
  unfold bridgeWeight
  exact continuous_const.mul
    (continuous_finsetSum _ fun g _ =>
      (continuous_rawBridgeWeight hp F A).comp (Realization.continuous_smul p g))

theorem bridgeWeight_nonneg
    (hp : Nat.Prime p) (F : ZeroFreeMap hp)
    (A : StableRegularApproximation hp F.map)
    (x : Realization p) :
    0 ≤ bridgeWeight hp F A x := by
  unfold bridgeWeight
  exact mul_nonneg (inv_nonneg.mpr (by positivity))
    (Finset.sum_nonneg fun g _ => rawBridgeWeight_nonneg hp F A (g • x))

theorem bridgeWeight_le_one
    (hp : Nat.Prime p) (F : ZeroFreeMap hp)
    (A : StableRegularApproximation hp F.map)
    (x : Realization p) :
    bridgeWeight hp F A x ≤ 1 := by
  have hn_nat : 0 < Fintype.card (PrimeSymmetry p) := Fintype.card_pos
  have hn : (0 : Real) < (Fintype.card (PrimeSymmetry p) : Real) := by
    exact_mod_cast hn_nat
  have hsum :
      (∑ g : PrimeSymmetry p, rawBridgeWeight hp F A (g • x)) ≤
        (Fintype.card (PrimeSymmetry p) : Real) := by
    calc
      (∑ g : PrimeSymmetry p, rawBridgeWeight hp F A (g • x))
          ≤ ∑ _g : PrimeSymmetry p, (1 : Real) :=
        Finset.sum_le_sum fun g _ => rawBridgeWeight_le_one hp F A (g • x)
      _ = (Fintype.card (PrimeSymmetry p) : Real) := by simp
  unfold bridgeWeight
  rw [inv_mul_le_iff₀ hn]
  simpa using hsum

/-- The averaged bridge weight is prime-invariant. -/
@[simp] theorem bridgeWeight_smul
    (hp : Nat.Prime p) (F : ZeroFreeMap hp)
    (A : StableRegularApproximation hp F.map)
    (h : PrimeSymmetry p) (x : Realization p) :
    bridgeWeight hp F A (h • x) = bridgeWeight hp F A x := by
  classical
  unfold bridgeWeight
  congr 1
  refine Fintype.sum_equiv (Equiv.mulRight h) _ _ ?_
  intro g
  simp [mul_smul]

/-- The averaged weight remains one on every translated refined endpoint vertex. -/
@[simp] theorem bridgeWeight_sample
    (hp : Nat.Prime p) (F : ZeroFreeMap hp)
    (A : StableRegularApproximation hp F.map)
    (z : SampleIndex hp A.toRegularApproximation.level) :
    bridgeWeight hp F A
      (samplePoint hp A.toRegularApproximation.level z) = 1 := by
  classical
  unfold bridgeWeight
  have hcard : (Fintype.card (PrimeSymmetry p) : Real) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hterm : ∀ g : PrimeSymmetry p,
      rawBridgeWeight hp F A
        (g • samplePoint hp A.toRegularApproximation.level z) = 1 := by
    intro g
    rw [← samplePoint_mul hp A.toRegularApproximation.level g z]
    exact rawBridgeWeight_sample hp F A (g * z.1, z.2)
  simp_rw [hterm]
  simp [hcard]

/-- A positive averaged weight still lies in the full safe locus. -/
theorem segmentSafe_of_bridgeWeight_pos
    (hp : Nat.Prime p) (F : ZeroFreeMap hp)
    (A : StableRegularApproximation hp F.map)
    (x : Realization p)
    (hx : 0 < bridgeWeight hp F A x) :
    SegmentSafe F.map A.toRegularApproximation.map x := by
  have hsum : 0 < ∑ g : PrimeSymmetry p,
      rawBridgeWeight hp F A (g • x) := by
    unfold bridgeWeight at hx
    have hcard_nat : 0 < Fintype.card (PrimeSymmetry p) := Fintype.card_pos
    have hcard : 0 < (Fintype.card (PrimeSymmetry p) : Real) := by
      exact_mod_cast hcard_nat
    have hinv : 0 < ((Fintype.card (PrimeSymmetry p) : Real)⁻¹) :=
      inv_pos.mpr hcard
    rcases (mul_pos_iff.mp hx) with hpos | hneg
    · exact hpos.2
    · exact (not_lt_of_ge (le_of_lt hinv) hneg.1).elim
  by_contra hnone
  have hall : ∀ g : PrimeSymmetry p,
      rawBridgeWeight hp F A (g • x) = 0 := by
    intro g
    apply le_antisymm
    · apply not_lt.mp
      intro hg
      apply hnone
      exact (segmentSafe_smul_iff hp F.map A.toRegularApproximation.map
        F.equivariant A.toRegularApproximation.equivariant x g).mp
        (segmentSafe_of_rawBridgeWeight_pos hp F A (g • x) hg)
    · exact rawBridgeWeight_nonneg hp F A (g • x)
  simp [hall] at hsum

/-- Global localized endpoint map.  It agrees with the approximation's sampling map at every
refined endpoint vertex, but returns to the original map away from the finite safe neighborhood. -/
noncomputable def bridgedMap
    (hp : Nat.Prime p) (F : ZeroFreeMap hp)
    (A : StableRegularApproximation hp F.map) : ZeroFreeMap hp where
  map := {
    toFun := fun x =>
      (1 - bridgeWeight hp F A x) • F.map x +
        bridgeWeight hp F A x • A.toRegularApproximation.map x
    continuous_toFun := by
      exact ((continuous_const.sub (continuous_bridgeWeight hp F A)).smul
        F.map.continuous).add
        ((continuous_bridgeWeight hp F A).smul
          A.toRegularApproximation.map.continuous)
  }
  equivariant := by
    intro g x
    change (1 - bridgeWeight hp F A (g • x)) • F.map (g • x) +
        bridgeWeight hp F A (g • x) • A.toRegularApproximation.map (g • x) =
      g • ((1 - bridgeWeight hp F A x) • F.map x +
        bridgeWeight hp F A x • A.toRegularApproximation.map x)
    rw [bridgeWeight_smul hp F A g x,
      F.equivariant g x, A.toRegularApproximation.equivariant g x]
    funext i
    simp only [PrimeSymmetry.smul_coordinate_apply, Pi.add_apply, Pi.smul_apply]
  zeroFree := by
    intro x
    by_cases hzero : bridgeWeight hp F A x = 0
    · simpa [hzero] using F.zeroFree x
    · have hpos : 0 < bridgeWeight hp F A x :=
        lt_of_le_of_ne (bridgeWeight_nonneg hp F A x) (Ne.symm hzero)
      exact segmentSafe_of_bridgeWeight_pos hp F A x hpos
        ⟨bridgeWeight hp F A x,
          bridgeWeight_nonneg hp F A x,
          bridgeWeight_le_one hp F A x⟩

/-- The bridged map has exactly the stored approximation value at every translated refined vertex. -/
@[simp] theorem bridgedMap_sample
    (hp : Nat.Prime p) (F : ZeroFreeMap hp)
    (A : StableRegularApproximation hp F.map)
    (z : SampleIndex hp A.toRegularApproximation.level) :
    (bridgedMap hp F A).map
      (samplePoint hp A.toRegularApproximation.level z) =
      A.toRegularApproximation.map
        (samplePoint hp A.toRegularApproximation.level z) := by
  simp [bridgedMap]

/-- In particular, every canonical refined vertex is fixed to the stored endpoint sample. -/
@[simp] theorem bridgedMap_refinedVertex
    (hp : Nat.Prime p) (F : ZeroFreeMap hp)
    (A : StableRegularApproximation hp F.map)
    (q : TopCell hp A.toRegularApproximation.level) (i : Fin (p - 1 + 1)) :
    (bridgedMap hp F A).map
      (vertex hp A.toRegularApproximation.level q i) =
      A.toRegularApproximation.map
        (vertex hp A.toRegularApproximation.level q i) := by
  simpa [samplePoint] using
    bridgedMap_sample hp F A
      ((1 : PrimeSymmetry p), (q, i))

/-- The straight line from the original map to the localized bridged map is zero-free. -/
theorem bridgedMap_zeroFreeStraightLine
    (hp : Nat.Prime p) (F : ZeroFreeMap hp)
    (A : StableRegularApproximation hp F.map) :
    ∀ x (t : Set.Icc (0 : Real) 1),
      (1 - t.1) • F.map x + t.1 • (bridgedMap hp F A).map x ≠ 0 := by
  intro x t
  by_cases hb : bridgeWeight hp F A x = 0
  · have hmap : (bridgedMap hp F A).map x = F.map x := by
      show (1 - bridgeWeight hp F A x) • F.map x +
        bridgeWeight hp F A x • A.toRegularApproximation.map x = F.map x
      rw [hb]
      module
    rw [hmap]
    have hcol : (1 - t.1) • F.map x + t.1 • F.map x = F.map x := by module
    rw [hcol]
    exact F.zeroFree x
  · have hbpos : 0 < bridgeWeight hp F A x :=
      lt_of_le_of_ne (bridgeWeight_nonneg hp F A x) (Ne.symm hb)
    have hsafe := segmentSafe_of_bridgeWeight_pos hp F A x hbpos
    let u : Set.Icc (0 : Real) 1 :=
      ⟨t.1 * bridgeWeight hp F A x, by
        constructor
        · exact mul_nonneg t.2.1 (bridgeWeight_nonneg hp F A x)
        · exact mul_le_one₀ t.2.2 (bridgeWeight_nonneg hp F A x)
            (bridgeWeight_le_one hp F A x)⟩
    have heq :
        (1 - t.1) • F.map x + t.1 • (bridgedMap hp F A).map x =
          (1 - u.1) • F.map x + u.1 • A.toRegularApproximation.map x := by
      show (1 - t.1) • F.map x +
          t.1 • ((1 - bridgeWeight hp F A x) • F.map x +
            bridgeWeight hp F A x • A.toRegularApproximation.map x) =
        (1 - t.1 * bridgeWeight hp F A x) • F.map x +
          (t.1 * bridgeWeight hp F A x) • A.toRegularApproximation.map x
      module
    rw [heq]
    exact hsafe u

/-- Every stable regular approximation supplies the global zero-free endpoint interpolant required
by the exact relative-collar construction. -/
noncomputable def endpointInterpolant
    (hp : Nat.Prime p) (F : ZeroFreeMap hp)
    (A : StableRegularApproximation hp F.map) :
    ZeroFreeEndpointInterpolant hp F where
  map := bridgedMap hp F A
  zeroFreeStraightLine := bridgedMap_zeroFreeStraightLine hp F A

/-- The endpoint interpolant has exactly the approximation's refined vertex samples. -/
@[simp] theorem endpointInterpolant_refinedVertex
    (hp : Nat.Prime p) (F : ZeroFreeMap hp)
    (A : StableRegularApproximation hp F.map)
    (q : TopCell hp A.toRegularApproximation.level) (i : Fin (p - 1 + 1)) :
    (endpointInterpolant hp F A).map.map
      (vertex hp A.toRegularApproximation.level q i) =
      A.toRegularApproximation.map
        (vertex hp A.toRegularApproximation.level q i) :=
  bridgedMap_refinedVertex hp F A q i

/-- Simultaneous lower and upper endpoint bridges. -/
noncomputable def endpointBridgePair
    (hp : Nat.Prime p)
    (F₀ F₁ : ZeroFreeMap hp)
    (A₀ : StableRegularApproximation hp F₀.map)
    (A₁ : StableRegularApproximation hp F₁.map) :
    ZeroFreeEndpointInterpolant hp F₀ × ZeroFreeEndpointInterpolant hp F₁ :=
  (endpointInterpolant hp F₀ A₀, endpointInterpolant hp F₁ A₁)

end StableEndpointBridges
end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR
