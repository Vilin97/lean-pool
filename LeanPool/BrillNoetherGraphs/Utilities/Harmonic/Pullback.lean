/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Harmonic.Basic

/-!
# Rank and transmission transport along harmonic pullback

The rank-one fibre argument is only the first consequence of a harmonic map.
Whenever pullback preserves principal divisors, it does not decrease the rank
of *any* target divisor.  The proof pushes an arbitrary effective rank test to
the target, wins there, and observes that pulling the pushed test back
dominates the original source test.

This file also records the marked consequence at the natural level of
generality.  If the two marked one-chip divisors are exact pullbacks, every ASP
transmission row pulls back.  An additional effective source divisor may be
added, so the degree can be adjusted independently; only the final
transmission-degree equation remains to be supplied.
-/

@[expose] public section

namespace MarkedGraphs

open Utilities
open Finset

namespace IndexedHarmonicData

variable {G H : CFGraph}

/-- Push a divisor forward by summing its coefficients over target fibres. -/
def pushforward (f : IndexedHarmonicData G H) (D : CFDiv G) : CFDiv H :=
  fun z => ∑ x : G.V, if f.vertexMap x = z then D x else 0

/-- Pushforward preserves total degree. -/
theorem deg_pushforward (f : IndexedHarmonicData G H) (D : CFDiv G) :
    deg (f.pushforward D) = deg D := by
  classical
  change (∑ z : H.V, ∑ x : G.V,
    if f.vertexMap x = z then D x else 0) = ∑ x : G.V, D x
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp

/-- Pushforward preserves effectivity. -/
theorem pushforward_effective (f : IndexedHarmonicData G H) {D : CFDiv G}
    (hD : effective D) :
    effective (f.pushforward D) := by
  intro z
  unfold pushforward
  exact Finset.sum_nonneg fun x _ => by
    split
    · exact hD x
    · exact le_rfl

/-- Pullback preserves effectivity. -/
theorem pullback_effective (f : IndexedHarmonicData G H) {A : CFDiv H}
    (hA : effective A) :
    effective (f.pullback A) := by
  intro x
  unfold pullback
  exact mul_nonneg (Int.natCast_nonneg _) (hA (f.vertexMap x))

/-- Pullback is additive. -/
theorem pullback_add (f : IndexedHarmonicData G H) (A B : CFDiv H) :
    f.pullback (A + B) = f.pullback A + f.pullback B := by
  funext x
  simp [pullback, mul_add]

/-- Pullback commutes with integral scalar multiplication. -/
theorem pullback_zsmul (f : IndexedHarmonicData G H) (a : ℤ) (A : CFDiv H) :
    f.pullback (a • A) = a • f.pullback A := by
  funext x
  simp [pullback]
  ring

/-- For an effective divisor, pulling its pushforward back dominates it.

The local degree is positive, and the fibre sum at `x` contains the summand
at `x`; these are exactly the two inequalities used in the proof. -/
theorem pullback_pushforward_sub_effective
    (f : IndexedHarmonicData G H) {D : CFDiv G} (hD : effective D) :
    effective (f.pullback (f.pushforward D) - D) := by
  classical
  intro x
  let S : ℤ := ∑ y : G.V,
    if f.vertexMap y = f.vertexMap x then D y else 0
  have hSummandNonneg (y : G.V) :
      0 ≤ if f.vertexMap y = f.vertexMap x then D y else 0 := by
    split
    · exact hD y
    · exact le_rfl
  have hSNonneg : 0 ≤ S := by
    exact Finset.sum_nonneg fun y _ => hSummandNonneg y
  have hDxLeS : D x ≤ S := by
    have hSingle := Finset.single_le_sum
      (s := (Finset.univ : Finset G.V))
      (f := fun y : G.V =>
        if f.vertexMap y = f.vertexMap x then D y else 0)
      (fun y _ => hSummandNonneg y) (Finset.mem_univ x)
    simpa [S] using hSingle
  have hDegreeOne : (1 : ℤ) ≤ (f.localDegree x : ℤ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr (f.localDegree_pos x))
  change 0 ≤ (f.localDegree x : ℤ) * S - D x
  nlinarith

/-- Winnability transports along any pullback compatible with principal
divisors. -/
theorem winnable_pullback
    (f : IndexedHarmonicData G H)
    (hPullback : f.PullbackPrincipalCompatible)
    {A : CFDiv H} (hA : winnable H A) :
    winnable G (f.pullback A) := by
  obtain ⟨B, hBEffective, hAB⟩ := hA
  exact ⟨f.pullback B, f.pullback_effective hBEffective,
    hPullback A B hAB⟩

/-- Harmonic pullback does not decrease Baker--Norine rank. -/
theorem rank_pullback_ge
    (f : IndexedHarmonicData G H)
    (hPullback : f.PullbackPrincipalCompatible) (A : CFDiv H) :
    rank G (f.pullback A) ≥ rank H A := by
  apply (rank_geq_iff G (f.pullback A) (rank H A)).mp
  intro D hD
  have hPushEffective : effective (f.pushforward D) :=
    f.pushforward_effective hD.1
  have hPushDegree : deg (f.pushforward D) = rank H A := by
    rw [f.deg_pushforward, hD.2]
  have hTarget : winnable H (A - f.pushforward D) :=
    ((rank_geq_iff H A (rank H A)).mpr le_rfl)
      (f.pushforward D) ⟨hPushEffective, hPushDegree⟩
  have hPulled : winnable G (f.pullback (A - f.pushforward D)) :=
    f.winnable_pullback hPullback hTarget
  have hExcessEffective : effective (f.pullback (f.pushforward D) - D) :=
    f.pullback_pushforward_sub_effective hD.1
  have hSum := winnable_add_winnable G
    (f.pullback (A - f.pushforward D))
    (f.pullback (f.pushforward D) - D)
    hPulled (winnable_of_effective G _ hExcessEffective)
  convert hSum using 1
  rw [f.pullback_sub]
  abel

/-- A source mark is an exact unramified singleton pullback of a target mark.
The equation is the precise condition needed by the marked rank formulas and
is often cheaper to check than separately spelling singleton and local-degree
conditions. -/
def PullsBackMark (f : IndexedHarmonicData G H) (u : G.V) (p : H.V) : Prop :=
  f.pullback (oneChip p) = oneChip u

/-- Marked twists commute with pullback at two exact marked fibres. -/
theorem pullback_markedTwist
    (f : IndexedHarmonicData G H) {u v : G.V} {p q : H.V}
    (hu : f.PullsBackMark u p) (hv : f.PullsBackMark v q)
    (A : CFDiv H) (a b : ℤ) :
    f.pullback (A + a • oneChip p - b • oneChip q) =
      f.pullback A + a • oneChip u - b • oneChip v := by
  rw [f.pullback_sub, f.pullback_add, f.pullback_zsmul,
    f.pullback_zsmul, hu, hv]

/-- Every individual ASP transmission inequality transports through harmonic
pullback at exact marked fibres. -/
theorem transmissionInequality_pullback
    (f : IndexedHarmonicData G H)
    (hPullback : f.PullbackPrincipalCompatible)
    {u v : G.V} {p q : H.V}
    (hu : f.PullsBackMark u p) (hv : f.PullsBackMark v q)
    (τ : AspPerm) (A : CFDiv H) (a b : ℤ)
    (hRow : TransmissionInequality H p q τ A a b) :
    TransmissionInequality G u v τ (f.pullback A) a b := by
  unfold TransmissionInequality at hRow ⊢
  rw [← f.pullback_markedTwist hu hv A a b]
  exact le_trans hRow
    (f.rank_pullback_ge hPullback
      (A + a • oneChip p - b • oneChip q))

/-- Adding an effective correction after pullback still preserves every
marked transmission row. -/
theorem transmissionInequality_pullback_add_effective
    (f : IndexedHarmonicData G H)
    (hPullback : f.PullbackPrincipalCompatible)
    {u v : G.V} {p q : H.V}
    (hu : f.PullsBackMark u p) (hv : f.PullsBackMark v q)
    (τ : AspPerm) (A : CFDiv H) (E : CFDiv G) (a b : ℤ)
    (hE : effective E)
    (hRow : TransmissionInequality H p q τ A a b) :
    TransmissionInequality G u v τ (f.pullback A + E) a b := by
  unfold TransmissionInequality at hRow ⊢
  have hBase := f.transmissionInequality_pullback hPullback hu hv
    τ A a b hRow
  unfold TransmissionInequality at hBase
  have hAdd := rank_add_effective_ge G
    (f.pullback A + a • oneChip u - b • oneChip v)
    E hE (τ.s (a + 1) b - 1) hBase
  convert hAdd using 1
  abel_nf

/-- Restricted arbitrary-ASP transmission profiles pull back row by row. -/
theorem satisfiesTransmissionOn_pullback
    (f : IndexedHarmonicData G H)
    (hPullback : f.PullbackPrincipalCompatible)
    {u v : G.V} {p q : H.V}
    (hu : f.PullsBackMark u p) (hv : f.PullsBackMark v q)
    (τ : AspPerm) (A : CFDiv H) (S : Set (ℤ × ℤ))
    (hA : SatisfiesTransmissionOn H p q τ A S) :
    SatisfiesTransmissionOn G u v τ (f.pullback A) S := by
  intro row hRow
  exact f.transmissionInequality_pullback hPullback hu hv
    τ A row.1 row.2 (hA row hRow)

/-- Full arbitrary-ASP transmission pulls back once the resulting divisor has
the source graph's required transmission degree. -/
theorem satisfiesTransmission_pullback
    (f : IndexedHarmonicData G H)
    (hPullback : f.PullbackPrincipalCompatible)
    {u v : G.V} {p q : H.V}
    (hu : f.PullsBackMark u p) (hv : f.PullsBackMark v q)
    (τ : AspPerm) (A : CFDiv H)
    (hA : SatisfiesTransmission H p q τ A)
    (hDegree : deg (f.pullback A) = (genus G : ℤ) + τ.χ) :
    SatisfiesTransmission G u v τ (f.pullback A) := by
  refine ⟨hDegree, ?_⟩
  intro a b
  exact f.transmissionInequality_pullback hPullback hu hv
    τ A a b (hA.2 a b)

/-- An effective source correction may adjust the pullback degree without
spoiling any arbitrary-ASP transmission row. -/
theorem satisfiesTransmission_pullback_add_effective
    (f : IndexedHarmonicData G H)
    (hPullback : f.PullbackPrincipalCompatible)
    {u v : G.V} {p q : H.V}
    (hu : f.PullsBackMark u p) (hv : f.PullsBackMark v q)
    (τ : AspPerm) (A : CFDiv H) (E : CFDiv G)
    (hA : SatisfiesTransmission H p q τ A) (hE : effective E)
    (hDegree : deg (f.pullback A + E) = (genus G : ℤ) + τ.χ) :
    SatisfiesTransmission G u v τ (f.pullback A + E) := by
  refine ⟨hDegree, ?_⟩
  intro a b
  exact f.transmissionInequality_pullback_add_effective hPullback hu hv
    τ A E a b hE (hA.2 a b)

/-- Existence form of effective-corrected marked harmonic pullback. -/
theorem transmissionExists_of_pullback_add_effective
    (f : IndexedHarmonicData G H)
    (hPullback : f.PullbackPrincipalCompatible)
    {u v : G.V} {p q : H.V}
    (hu : f.PullsBackMark u p) (hv : f.PullsBackMark v q)
    (τ : AspPerm) (A : CFDiv H) (E : CFDiv G)
    (hA : SatisfiesTransmission H p q τ A) (hE : effective E)
    (hDegree : deg (f.pullback A + E) = (genus G : ℤ) + τ.χ) :
    TransmissionExists G u v τ :=
  ⟨f.pullback A + E,
    f.satisfiesTransmission_pullback_add_effective hPullback hu hv
      τ A E hA hE hDegree⟩

/-- Row-wise comparison data for transporting a transmission divisor through
a harmonic map.  Unlike `PullsBackMark`, this permits ramified or nonsingleton
marked fibres: for each row, the source twist need only be the corresponding
target pullback plus an effective correction. -/
def HarmonicTransmissionProfile
    (f : IndexedHarmonicData G H) (u v : G.V) (p q : H.V)
    (τ : AspPerm) (A : CFDiv H) (D : CFDiv G) : Prop :=
  deg D = (genus G : ℤ) + τ.χ ∧
    ∀ a b : ℤ, ∃ E : CFDiv G, effective E ∧
      D + a • oneChip u - b • oneChip v =
        f.pullback (A + a • oneChip p - b • oneChip q) + E

/-- A harmonic transmission profile and a target transmission witness give a
source witness for the same arbitrary ASP permutation. -/
theorem satisfiesTransmission_of_harmonicProfile
    (f : IndexedHarmonicData G H)
    (hPullback : f.PullbackPrincipalCompatible)
    (u v : G.V) (p q : H.V) (τ : AspPerm)
    (A : CFDiv H) (D : CFDiv G)
    (hTarget : SatisfiesTransmission H p q τ A)
    (hProfile : f.HarmonicTransmissionProfile u v p q τ A D) :
    SatisfiesTransmission G u v τ D := by
  refine ⟨hProfile.1, ?_⟩
  intro a b
  obtain ⟨E, hEEffective, hRowEq⟩ := hProfile.2 a b
  have hTargetRow := hTarget.2 a b
  unfold TransmissionInequality at hTargetRow ⊢
  rw [hRowEq]
  exact rank_add_effective_ge G _ E hEEffective _
    (le_trans hTargetRow
      (f.rank_pullback_ge hPullback
        (A + a • oneChip p - b • oneChip q)))

/-- Existence wrapper for an arbitrary-ASP harmonic transmission profile. -/
theorem transmissionExists_of_harmonicProfile
    (f : IndexedHarmonicData G H)
    (hPullback : f.PullbackPrincipalCompatible)
    (u v : G.V) (p q : H.V) (τ : AspPerm)
    (A : CFDiv H) (D : CFDiv G)
    (hTarget : SatisfiesTransmission H p q τ A)
    (hProfile : f.HarmonicTransmissionProfile u v p q τ A D) :
    TransmissionExists G u v τ :=
  ⟨D, f.satisfiesTransmission_of_harmonicProfile hPullback
    u v p q τ A D hTarget hProfile⟩

end IndexedHarmonicData

end MarkedGraphs
