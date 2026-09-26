/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.ClosedRowProof.RichLeafDivisor
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.ClosedRowProof.RichChipPlacement
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.ClosedRowProof.RichW5Aggregation

/-! # Rich Leaf Assembly -/

@[expose] public section

open MarkedGraphs.Certificate
open Utilities.Certificate
open Utilities.Subdivision.ClosedRowProof

theorem finRange_map_sum {p : ℕ} (f : Fin p → ℤ) :
    (List.map f (List.finRange p)).sum = ∑ e : Fin p, f e := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [Fin.sum_univ_succ]
    simp only [List.finRange_succ, List.map_cons, List.sum_cons, List.map_map]
    change f 0 + (List.map (fun e => f e.succ) (List.finRange p)).sum = _
    rw [ih (fun e => f e.succ)]

theorem foldl_finRange_add {p : ℕ} (f : Fin p → ℤ) :
    (List.finRange p).foldl (fun z e => z + f e) 0 = ∑ e : Fin p, f e := by
  have h : ∀ (xs : List (Fin p)) (z : ℤ),
      xs.foldl (fun z e => z + f e) z = z + (xs.map f).sum := by
    intro xs
    induction xs with
    | nil => simp
    | cons e es ih =>
      intro z
      simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih]
      omega
  rw [h]
  rw [zero_add, finRange_map_sum]

namespace Utilities.Subdivision.ClosedRowProof.RichWitness

open Utilities
open Utilities.Certificate.ContractionForestCensusGeneral
variable {n p : ℕ}

theorem selectedBlock_intervalLength (d : Utilities.Certificate.DegenerateSpec.DegSpec n p)
    (w : RichWitness) (core : ExplicitPotential.Core n p) (Γ : Context)
    (x : List ℤ) (hW1 : w.w1Checks core Γ = true)
    (hx : Γ.Holds x) (hCoord : ∀ e : Fin p, eval (coordForm e.val) x = d.length e)
    (a : Fin n) (e : Fin p) (k : ℕ) (hk : k < d.length e) :
    let b := w.richBlockEnds d core Γ x hW1 hx hCoord a e
    ↑(b.endAt (b.blockAt k) - b.startAt (b.blockAt k)) =
      w.blockLengthValue x a.val e.val (b.blockAt k) := by
  dsimp only
  let b := w.richBlockEnds d core Γ x hW1 hx hCoord a e
  let i := b.blockAt k
  have hcover := b.covers k hk
  have hi : i < (w.blockList a.val e.val).length := by
    have hi' : i < b.ends.length := b.blockAt_lt_length k hk
    simpa [b, i] using hi'
  have hLengths : ∀ t < (w.blockList a.val e.val).length,
      0 ≤ w.blockLengthValue x a.val e.val t := fun t ht =>
    w.blockLength_nonneg_of_w1Checks core Γ x hW1 hx a e t ht
  have hLeft : 0 ≤ w.pointValue x a.val e.val i :=
    w.pointValue_nonneg_of_lengths x a.val e.val
      (w.blockList a.val e.val).length i hLengths (by omega)
  have hRight : 0 ≤ w.pointValue x a.val e.val (i + 1) :=
    w.pointValue_nonneg_of_lengths x a.val e.val
      (w.blockList a.val e.val).length (i + 1) hLengths (by omega)
  have hEnd : b.endAt i = (w.pointValue x a.val e.val (i + 1)).toNat := by
    simpa [b, i] using w.richBlockEnds_endAt d core Γ x hW1 hx hCoord a e i hi
  have hStart : b.startAt i = (w.pointValue x a.val e.val i).toNat := by
    by_cases hiz : i = 0
    · simp [FiniteBlockEnds.startAt, hiz, pointValue_zero]
    · rw [FiniteBlockEnds.startAt, ite_eq_right hiz]
      have hp : i - 1 < (w.blockList a.val e.val).length := by omega
      have hprev := w.richBlockEnds_endAt d core Γ x hW1 hx hCoord a e (i - 1) hp
      simpa [b, show i - 1 + 1 = i by omega] using hprev
  change ↑(b.endAt i - b.startAt i) = w.blockLengthValue x a.val e.val i
  rw [hEnd, hStart]
  have hdiff := w.pointValue_succ_sub x a.val e.val i
  have hlenNonneg := hLengths i hi
  have hNatLe : (w.pointValue x a.val e.val i).toNat ≤
      (w.pointValue x a.val e.val (i + 1)).toNat :=
    Int.toNat_le_toNat (by omega)
  rw [Nat.cast_sub hNatLe]
  simp only [Int.toNat_of_nonneg hRight, Int.toNat_of_nonneg hLeft]
  exact hdiff
theorem rich_blockSlope_bounds (d : Utilities.Certificate.DegenerateSpec.DegSpec n p)
    (w : RichWitness) (core : ExplicitPotential.Core n p) (Γ : Context)
    (x : List ℤ) (hW1 : w.w1Checks core Γ = true) (hW2 : w.w2Checks core Γ = true)
    (hx : Γ.Holds x) (ℓ : Fin p → ℕ)
    (hCoord : ∀ e : Fin p, eval (coordForm e.val) x = ℓ e)
    (hn : 0 < n) (hForest : IsForest core (zeroSet ℓ))
    (hNotLoopy : ¬ IsLoopy core (zeroSet ℓ)) (a : Fin n)
    (e : Fin p) (k : ℕ) (hk : k < d.length e)
    (hd : d = censusSpec core hn ℓ hForest hNotLoopy) :
    let data := w.richCensusPiecewiseData core Γ x hW1 hW2 hx ℓ hCoord hn
      hForest hNotLoopy a
    (w.block a.val e.val (data.blockAt e k)).lo ≤
      Utilities.Certificate.DegenerateSpec.DegSpec.blockSlope data.blockAt data.blockEnd
        data.blockRise e k ∧
    Utilities.Certificate.DegenerateSpec.DegSpec.blockSlope data.blockAt data.blockEnd
      data.blockRise e k ≤
      (w.block a.val e.val (data.blockAt e k)).hi := by
  subst d
  dsimp only
  let d := censusSpec core hn ℓ hForest hNotLoopy
  let data := w.richCensusPiecewiseData core Γ x hW1 hW2 hx ℓ hCoord hn
      hForest hNotLoopy a
  let i := data.blockAt e k
  have hiData : i = (w.richBlockEnds d core Γ x hW1 hx hCoord a e).blockAt k := rfl
  have hi : i < (w.blockList a.val e.val).length := by
    have := (w.richBlockEnds d core Γ x hW1 hx hCoord a e).blockAt_lt_length k hk
    rw [richBlockEnds_length d w core Γ x hW1 hx hCoord a e] at this
    simpa [i, data, richCensusPiecewiseData,
      Utilities.Certificate.DegenerateSpec.DegSpec.decodePiecewiseData, d] using! this
  obtain ⟨hLoReceipt, hHiReceipt⟩ := w.blockBounds_of_w2Checks core Γ hW2 a e i hi
  have hLo := w.blockLower_bound_of_receipt Γ x hx a.val e.val i hLoReceipt
  have hHi := w.blockUpper_bound_of_receipt Γ x hx a.val e.val i hHiReceipt
  have hInterval := w.selectedBlock_intervalLength d core Γ x hW1 hx hCoord a e k hk
  have hIntervalData :
      ↑(data.blockEnd e (data.blockAt e k) -
        Utilities.Certificate.DegenerateSpec.DegSpec.blockStart data.blockEnd e (data.blockAt e k))
          =
        w.blockLengthValue x a.val e.val (data.blockAt e k) := by
    simpa [data, richCensusPiecewiseData,
      Utilities.Certificate.DegenerateSpec.DegSpec.decodePiecewiseData,
      Utilities.Certificate.DegenerateSpec.DegSpec.blockStart, FiniteBlockEnds.startAt, d] using
        hInterval
  constructor
  · apply Utilities.Certificate.DegenerateSpec.DegSpec.lower_le_blockSlope_of_mul_le e k _ hk
    rw [hIntervalData]
    change (w.block a.val e.val (data.blockAt e k)).lo *
      w.blockLengthValue x a.val e.val (data.blockAt e k) ≤
        eval (w.block a.val e.val (data.blockAt e k)).rise x
    simpa [i] using hLo
  · apply Utilities.Certificate.DegenerateSpec.DegSpec.blockSlope_le_upper_of_le_mul e k _ hk
    rw [hIntervalData]
    change eval (w.block a.val e.val (data.blockAt e k)).rise x ≤
      (w.block a.val e.val (data.blockAt e k)).hi *
        w.blockLengthValue x a.val e.val (data.blockAt e k)
    simpa [i] using hHi

theorem rawChipMassAt_selectorChange (d : Utilities.Certificate.DegenerateSpec.DegSpec n p)
    (w : RichWitness) (core : ExplicitPotential.Core n p) (Γ : Context)
    (x : List ℤ) (hW1 : w.w1Checks core Γ = true) (hW3 : w.w3Checks core = true)
    (hx : Γ.Holds x) (hCoord : ∀ e : Fin p, eval (coordForm e.val) x = d.length e)
    (a : Fin n) (e : Fin p) (o : Fin (d.length e - 1))
    (hChange :
      (w.richBlockEnds d core Γ x hW1 hx hCoord a e).blockAt o.val <
        (w.richBlockEnds d core Γ x hW1 hx hCoord a e).blockAt (o.val + 1)) :
    w.rawChipMassAt x e.val (o.val + 1) =
      w4ChipSum (fun t => w.chipAt a.val e.val t)
        ((w.richBlockEnds d core Γ x hW1 hx hCoord a e).blockAt o.val + 1)
        ((w.richBlockEnds d core Γ x hW1 hx hCoord a e).blockAt (o.val + 1)) := by
  let b := w.richBlockEnds d core Γ x hW1 hx hCoord a e
  let i := b.blockAt o.val + 1
  let j := b.blockAt (o.val + 1)
  have hI : 1 ≤ i := by omega
  have hIJ : i ≤ j := by simpa [i, j, b] using hChange
  have hLen : o.val + 1 < d.length e := by omega
  have hLengths : ∀ t < (w.blockList a.val e.val).length,
      0 ≤ w.blockLengthValue x a.val e.val t := fun t ht =>
    w.blockLength_nonneg_of_w1Checks core Γ x hW1 hx a e t ht
  have hPointNonneg : ∀ t ≤ (w.blockList a.val e.val).length,
      0 ≤ w.pointValue x a.val e.val t := fun t ht =>
    w.pointValue_nonneg_of_lengths x a.val e.val
      (w.blockList a.val e.val).length t hLengths ht
  have hrun : ∀ t, i ≤ t → t ≤ j →
      w.pointValue x a.val e.val t = (o.val + 1 : ℕ) := by
    intro t hit htj
    have htpos : 0 < t := by omega
    have htblock : t - 1 < (w.blockList a.val e.val).length := by
      have hjlt := b.blockAt_lt_length (o.val + 1) hLen
      simpa [b] using (show t - 1 < b.ends.length by
        rw [w.richBlockEnds_length d core Γ x hW1 hx hCoord a e] at hjlt ⊢
        omega)
    have hend : b.endAt (t - 1) = o.val + 1 :=
      b.endAt_eq_succ_of_selector_lt o.val (b.blockAt o.val)
        (b.blockAt (o.val + 1)) (t - 1) hLen rfl rfl hChange (by omega) (by omega)
    have hp := w.richBlockEnds_endAt d core Γ x hW1 hx hCoord a e (t - 1) htblock
    rw [show t - 1 + 1 = t by omega] at hp
    have hnat : (w.pointValue x a.val e.val t).toNat = o.val + 1 := by
      rw [← hp]
      exact hend
    have hnn := hPointNonneg t (by
      have := b.blockAt_lt_length (o.val + 1) hLen; simp [j] at htj; omega)
    omega
  have hbelow : ∀ t, 1 ≤ t → t < i →
      w.pointValue x a.val e.val t ≠ (o.val + 1 : ℕ) := by
    intro t ht1 hti heq
    have htblock : t - 1 < (w.blockList a.val e.val).length := by
      have hiOld := b.blockAt_lt_length o.val (by omega : o.val < d.length e)
      rw [w.richBlockEnds_length d core Γ x hW1 hx hCoord a e] at hiOld
      omega
    have hp := w.richBlockEnds_endAt d core Γ x hW1 hx hCoord a e (t - 1) htblock
    rw [show t - 1 + 1 = t by omega, heq] at hp
    have hendle := b.endAt_le_of_lt_blockAt o.val (t - 1) (by omega : o.val < d.length e)
      (by change t < b.blockAt o.val + 1 at hti; omega)
    rw [hp] at hendle
    omega
  have habove : ∀ t, j < t → t ≤ (w.blockList a.val e.val).length - 1 →
      w.pointValue x a.val e.val t ≠ (o.val + 1 : ℕ) := by
    intro t hjt htlen heq
    have htblock : t - 1 < (w.blockList a.val e.val).length := by omega
    have hp := w.richBlockEnds_endAt d core Γ x hW1 hx hCoord a e (t - 1) htblock
    rw [show t - 1 + 1 = t by omega, heq] at hp
    have hlive := b.blockAt_spec (o.val + 1) hLen
    have hmono := b.endAt_mono (show b.blockAt (o.val + 1) ≤ t - 1 by
      simpa [j] using (show j ≤ t - 1 by omega))
    rw [hp] at hmono
    omega
  exact w.rawChipMassAt_eq_w4ChipSum core hW3 x a e i j (o.val + 1)
    hI hIJ hrun hbelow habove

theorem rawChipMassAt_eq_zero_of_sameSelector (d : Utilities.Certificate.DegenerateSpec.DegSpec n p)
    (w : RichWitness) (core : ExplicitPotential.Core n p) (Γ : Context)
    (x : List ℤ) (hW1 : w.w1Checks core Γ = true) (hW3 : w.w3Checks core = true)
    (hx : Γ.Holds x) (hCoord : ∀ e : Fin p, eval (coordForm e.val) x = d.length e)
    (a : Fin n) (e : Fin p) (o : Fin (d.length e - 1))
    (hSame :
      (w.richBlockEnds d core Γ x hW1 hx hCoord a e).blockAt o.val =
        (w.richBlockEnds d core Γ x hW1 hx hCoord a e).blockAt (o.val + 1)) :
    w.rawChipMassAt x e.val (o.val + 1) = 0 := by
  classical
  let b := w.richBlockEnds d core Γ x hW1 hx hCoord a e
  unfold rawChipMassAt
  have hmap : w.chips.map (fun chip =>
      if chip.1 == e.val && eval chip.2.1 x == (o.val + 1) then chip.2.2 else 0) =
      w.chips.map (fun _ => 0) := by
    apply List.map_congr_left
    intro chip hchip
    by_cases hs : chip.1 = e.val
    · obtain ⟨i, hi, hval⟩ := w.chip_pointValue_eq_of_w3Checks core hW3 a hchip x
      rw [hs] at hi hval
      have hne : eval chip.2.1 x ≠ (o.val + 1 : ℕ) := by
        intro heval
        have hpval : w.pointValue x a.val e.val (i + 1) = (o.val + 1 : ℕ) := by
          rw [← hval]
          exact heval
        have hend : b.endAt i = o.val + 1 := by
          have hi' : i < (w.blockList a.val e.val).length := by omega
          have hp := w.richBlockEnds_endAt d core Γ x hW1 hx hCoord a e i hi'
          rw [hp, hpval]
          simp
        have hOldLe : b.blockAt o.val ≤ i := by
          by_contra hnot
          have hendle := b.endAt_le_of_lt_blockAt o.val i
            (by omega : o.val < d.length e) (by omega)
          rw [hend] at hendle
          omega
        have hNewGt : i < b.blockAt (o.val + 1) :=
          b.lt_blockAt_of_endAt_le (o.val + 1) i (by omega) (by omega)
        have : b.blockAt o.val < b.blockAt (o.val + 1) := lt_of_le_of_lt hOldLe hNewGt
        have hs' : b.blockAt o.val = b.blockAt (o.val + 1) := by simpa [b] using hSame
        exact (lt_irrefl _ (hs' ▸ this))
      have hb : (eval chip.2.1 x == (o.val + 1 : ℤ)) = false := by
        simp only [beq_eq_false_iff_ne]
        exact hne
      simp [hs, hb]
    · simp [hs]
  rw [hmap]
  simp

theorem blockList_length_eq_one_of_coord_eq_zero (w : RichWitness)
    (core : ExplicitPotential.Core n p) (Γ : Context) (x : List ℤ)
    (hW1 : w.w1Checks core Γ = true) (hW3 : w.w3Checks core = true)
    (hx : Γ.Holds x) (a : Fin n) (e : Fin p)
    (hcoord : eval (coordForm e.val) x = 0) :
    (w.blockList a.val e.val).length = 1 := by
  let k := (w.blockList a.val e.val).length
  let α := (w.plan a.val).headSlack.getD e.val 0
  let ω := (w.plan a.val).tailSlack.getD e.val 0
  have hLength : ∀ j < k, 0 ≤ w.blockLengthValue x a.val e.val j := fun j hj =>
    w.blockLength_nonneg_of_w1Checks core Γ x hW1 hx a e j (by simpa [k] using hj)
  have hLast : w.pointValue x a.val e.val k = 0 := by
    rw [w.pointValue_last_eq_coord_of_w1Checks core Γ x hW1 a e]
    exact hcoord
  have hAllZero : ∀ i ≤ k, w.pointValue x a.val e.val i = 0 := by
    intro i hi
    have hnonneg := w.pointValue_nonneg_of_lengths x a.val e.val k i hLength hi
    have hle := w.pointValue_le_of_lengths_last x a.val e.val k 0 i hLength hLast hi
    omega
  obtain ⟨sT, hsTα, hsTle, -, hsTmax, -⟩ :=
    w.exists_tail_collapse core Γ x hW1 hW3 hx a e
  have hsT : sT = k - 1 := by
    apply Nat.le_antisymm hsTle
    by_contra hnot
    exact hsTmax (k - 1) (by omega) le_rfl (hAllZero _ (by omega))
  obtain ⟨sH, hsHω, hsHle, -, hsHlow, -⟩ :=
    w.exists_head_collapse core Γ x hW1 hW3 hx a e
  have hsH : sH = k - 1 := by
    apply Nat.le_antisymm hsHle
    by_contra hnot
    exact hsHlow 1 (by omega) (by omega)
      (by simpa [hcoord] using hAllZero 1 (by omega))
  have hW1' := hW1
  simp only [w1Checks, ExplicitPotential.allFin_eq_true_iff,
    Bool.and_eq_true] at hW1'
  have hdiscipline : α + ω + 1 ≤ k := by
    exact decide_eq_true_eq.mp (by simpa [α, ω, k] using (hW1' a e).1.1.1.1.2)
  have hk : k = 1 := by
    have hsTα' : sT ≤ α := by simpa [α] using hsTα
    have hsHω' : sH ≤ ω := by simpa [ω] using hsHω
    rw [hsT] at hsTα'
    rw [hsH] at hsHω'
    omega
  simpa [k] using hk

theorem tail_blockAt_eq_collapse (d : Utilities.Certificate.DegenerateSpec.DegSpec n p)
    (w : RichWitness) (core : ExplicitPotential.Core n p) (Γ : Context) (x : List ℤ)
    (hW1 : w.w1Checks core Γ = true) (hx : Γ.Holds x)
    (hCoord : ∀ e : Fin p, eval (coordForm e.val) x = d.length e)
    (a : Fin n) (e : Fin p) (hpos : 0 < d.length e) (s : ℕ)
    (hs : s ≤ (w.blockList a.val e.val).length - 1)
    (hzero : w.pointValue x a.val e.val s = 0)
    (hmax : ∀ i, s < i → i ≤ (w.blockList a.val e.val).length - 1 →
      w.pointValue x a.val e.val i ≠ 0) :
    (w.richBlockEnds d core Γ x hW1 hx hCoord a e).blockAt 0 = s := by
  let b := w.richBlockEnds d core Γ x hW1 hx hCoord a e
  have hslt : s < (w.blockList a.val e.val).length := by
    have hnonempty := b.nonempty
    rw [w.richBlockEnds_length d core Γ x hW1 hx hCoord a e] at hnonempty
    omega
  have hstart : b.startAt s = 0 := by
    by_cases hz : s = 0
    · simp [FiniteBlockEnds.startAt, hz]
    · rw [FiniteBlockEnds.startAt, ite_eq_right hz]
      have hp := w.richBlockEnds_endAt d core Γ x hW1 hx hCoord a e (s - 1) (by omega)
      rw [show s - 1 + 1 = s by omega, hzero] at hp
      simpa [b] using hp
  have hendpos : 0 < b.endAt s := by
    have hp := w.richBlockEnds_endAt d core Γ x hW1 hx hCoord a e s hslt
    by_cases hlast : s = (w.blockList a.val e.val).length - 1
    · have hlastval := w.pointValue_last_eq_coord_of_w1Checks core Γ x hW1 a e
      have hsuc : s + 1 = (w.blockList a.val e.val).length := by omega
      rw [hp, hsuc, hlastval, hCoord e]
      simp [hpos]
    · have hne := hmax (s + 1) (by omega) (by omega)
      have hLengths : ∀ t < (w.blockList a.val e.val).length,
          0 ≤ w.blockLengthValue x a.val e.val t := fun t ht =>
        w.blockLength_nonneg_of_w1Checks core Γ x hW1 hx a e t ht
      have hnn := w.pointValue_nonneg_of_lengths x a.val e.val
        (w.blockList a.val e.val).length (s + 1) hLengths (by omega)
      rw [hp]
      omega
  exact b.ownsInterval s 0 (by rw [hstart]) hendpos

theorem head_blockAt_eq_collapse (d : Utilities.Certificate.DegenerateSpec.DegSpec n p)
    (w : RichWitness) (core : ExplicitPotential.Core n p) (Γ : Context) (x : List ℤ)
    (hW1 : w.w1Checks core Γ = true) (hx : Γ.Holds x)
    (hCoord : ∀ e : Fin p, eval (coordForm e.val) x = d.length e)
    (a : Fin n) (e : Fin p) (hpos : 0 < d.length e) (s : ℕ)
    (hs : s ≤ (w.blockList a.val e.val).length - 1)
    (hhead : w.pointValue x a.val e.val ((w.blockList a.val e.val).length - s) =
      eval (coordForm e.val) x)
    (hlow : ∀ i, 1 ≤ i → i < (w.blockList a.val e.val).length - s →
      w.pointValue x a.val e.val i ≠ eval (coordForm e.val) x) :
    (w.richBlockEnds d core Γ x hW1 hx hCoord a e).blockAt (d.length e - 1) =
      (w.blockList a.val e.val).length - 1 - s := by
  let b := w.richBlockEnds d core Γ x hW1 hx hCoord a e
  let t := (w.blockList a.val e.val).length - 1 - s
  have htlt : t < (w.blockList a.val e.val).length := by
    have hnonempty := b.nonempty
    rw [w.richBlockEnds_length d core Γ x hW1 hx hCoord a e] at hnonempty
    omega
  have hend : b.endAt t = d.length e := by
    have hp := w.richBlockEnds_endAt d core Γ x hW1 hx hCoord a e t htlt
    have ht1 : t + 1 = (w.blockList a.val e.val).length - s := by omega
    rw [hp, ht1, hhead, hCoord e]
    simp
  have hstartlt : b.startAt t < d.length e := by
    by_cases ht0 : t = 0
    · simp [FiniteBlockEnds.startAt, ht0, hpos]
    · rw [FiniteBlockEnds.startAt, ite_eq_right ht0]
      have hp := w.richBlockEnds_endAt d core Γ x hW1 hx hCoord a e (t - 1) (by omega)
      have hidx : t - 1 + 1 = t := by omega
      rw [hp, hidx]
      have hneq := hlow t (by omega) (by dsimp [t]; omega)
      have hLengths : ∀ q < (w.blockList a.val e.val).length,
          0 ≤ w.blockLengthValue x a.val e.val q := fun q hq =>
        w.blockLength_nonneg_of_w1Checks core Γ x hW1 hx a e q hq
      have hlast : w.pointValue x a.val e.val (w.blockList a.val e.val).length =
          d.length e := by
        rw [w.pointValue_last_eq_coord_of_w1Checks core Γ x hW1 a e, hCoord e]
      have hle := w.pointValue_le_of_lengths_last x a.val e.val
        (w.blockList a.val e.val).length (d.length e) t hLengths hlast (by
          dsimp [t]; omega)
      have hnn := w.pointValue_nonneg_of_lengths x a.val e.val
        (w.blockList a.val e.val).length t hLengths (by dsimp [t]; omega)
      rw [Int.toNat_lt hnn]
      simpa [hCoord e] using lt_of_le_of_ne hle (by simpa [hCoord e] using hneq)
  apply b.ownsInterval t (d.length e - 1)
  · omega
  · rw [hend]
    omega

private theorem sum_class_indicator (d : Utilities.Certificate.DegenerateSpec.DegSpec n p)
    (u r : Fin n) (z : ℤ) :
    ∑ v ∈ Finset.univ.filter (fun v : Fin n => d.rep v = d.rep r),
      (if u.val == v.val then z else 0) =
      if d.rep u = d.rep r then z else 0 := by
  classical
  by_cases hmem : u ∈ Finset.univ.filter (fun v : Fin n => d.rep v = d.rep r)
  · rw [ite_eq_left (by simpa using (Finset.mem_filter.mp hmem).2)]
    rw [Finset.sum_eq_single u]
    · simp
    · intro b hb hbu
      have hval : u.val ≠ b.val := fun h => hbu (Fin.ext h.symm)
      simp [hval]
    · exact fun h => (h hmem).elim
  · rw [ite_eq_right]
    · apply Finset.sum_eq_zero
      intro b hb
      have hval : u.val ≠ b.val := by
        intro h
        have hbu : b = u := Fin.ext h.symm
        subst b
        exact hmem hb
      simp [hval]
    · simpa using hmem

private theorem sum_class_indicator_rev (d : Utilities.Certificate.DegenerateSpec.DegSpec n p)
    (u r : Fin n) (z : ℤ) :
    ∑ v ∈ Finset.univ.filter (fun v : Fin n => d.rep v = d.rep r),
      (if v.val == u.val then z else 0) =
      if d.rep u = d.rep r then z else 0 := by
  classical
  by_cases hmem : u ∈ Finset.univ.filter (fun v : Fin n => d.rep v = d.rep r)
  · rw [ite_eq_left (by simpa using (Finset.mem_filter.mp hmem).2)]
    rw [Finset.sum_eq_single u]
    · simp
    · intro b hb hbu
      have hval : b.val ≠ u.val := fun h => hbu (Fin.ext h)
      simp [hval]
    · exact fun h => (h hmem).elim
  · rw [ite_eq_right]
    · apply Finset.sum_eq_zero
      intro b hb
      have hval : b.val ≠ u.val := by
        intro h
        have hbu : b = u := Fin.ext h
        subst b
        exact hmem hb
      simp [hval]
    · simpa using hmem

theorem classSum_w5ActualResidual_eq (d : Utilities.Certificate.DegenerateSpec.DegSpec n p)
    (w : RichWitness) (core : ExplicitPotential.Core n p) (mult : ℤ) (a : Fin n)
    (tail head : Fin p → ℤ) (r : Fin n) :
    ∑ v ∈ Finset.univ.filter (fun v : Fin n => d.rep v = d.rep r),
        w.w5ActualResidual core mult a tail head v =
      (∑ v ∈ Finset.univ.filter (fun v : Fin n => d.rep v = d.rep r),
        w.divisorCore.getD v.val 0) -
      (if d.rep a = d.rep r then mult else 0) +
      ∑ e : Fin p,
        ((if d.rep (core.tail e) = d.rep r then tail e else 0) +
          (if d.rep (core.head e) = d.rep r then head e else 0)) := by
  classical
  simp only [w5ActualResidual]
  have hFold : ∀ v : Fin n,
      (List.finRange p).foldl (fun z e => z +
        (if (core.tail e).val == v.val then tail e else 0) +
        (if (core.head e).val == v.val then head e else 0)) 0 =
      ∑ e : Fin p, ((if (core.tail e).val == v.val then tail e else 0) +
        (if (core.head e).val == v.val then head e else 0)) := by
    intro v
    simpa only [add_assoc] using foldl_finRange_add (fun e : Fin p =>
      (if (core.tail e).val == v.val then tail e else 0) +
        (if (core.head e).val == v.val then head e else 0))
  simp_rw [hFold]
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_sub_distrib]
    congr 1
    exact sum_class_indicator_rev d a r mult
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Finset.sum_add_distrib]
    congr 1
    · exact sum_class_indicator d (core.tail e) r (tail e)
    · exact sum_class_indicator d (core.head e) r (head e)

end Utilities.Subdivision.ClosedRowProof.RichWitness

namespace Utilities.Subdivision.ClosedRowProof.RichWitness
open Utilities
open Utilities.Certificate.ContractionForestCensusGeneral
variable {m n p : ℕ}

/-- The decoded census script realizes at least the certified endpoint contributions,
including the case where the entire slot contracts to length zero. -/
private theorem richCensusEndpoint_bounds
    (core : ExplicitPotential.Core n p) (w : RichWitness) (Γ : Context) (hn : 0 < n)
    (x : List ℤ) (hx : Γ.Holds x)
    (hW1 : w.w1Checks core Γ = true) (hW2 : w.w2Checks core Γ = true)
    (hW3 : w.w3Checks core = true) (ℓ : Fin p → ℕ)
    (hCoord : ∀ e : Fin p, eval (coordForm e.val) x = (ℓ e : ℤ))
    (hForest : IsForest core (zeroSet ℓ)) (hNotLoopy : ¬ IsLoopy core (zeroSet ℓ))
    (anchor : Fin n) :
    let d := censusSpec core hn ℓ hForest hNotLoopy
    let data := w.richCensusPiecewiseData core Γ x hW1 hW2 hx ℓ hCoord hn
      hForest hNotLoopy anchor
    let tail : Fin p → ℤ := fun e =>
      if d.length e = 0 then (w.block anchor.val e.val 0).lo
      else w.rawChipMassAt x e.val 0 +
        Utilities.Certificate.DegenerateSpec.DegSpec.blockSlope data.blockAt data.blockEnd
          data.blockRise e 0
    let head : Fin p → ℤ := fun e =>
      if d.length e = 0 then -(w.block anchor.val e.val 0).hi
      else w.rawChipMassAt x e.val (d.length e) -
        Utilities.Certificate.DegenerateSpec.DegSpec.blockSlope data.blockAt data.blockEnd
          data.blockRise e
          (d.length e - 1)
    (∀ e, w.tailContribution anchor.val e.val ≤ tail e) ∧
      (∀ e, w.headContribution anchor.val e.val ≤ head e) := by
  classical
  let d := censusSpec core hn ℓ hForest hNotLoopy
  let data := w.richCensusPiecewiseData core Γ x hW1 hW2 hx ℓ hCoord hn
    hForest hNotLoopy anchor
  let tail : Fin p → ℤ := fun e =>
    if d.length e = 0 then (w.block anchor.val e.val 0).lo
    else w.rawChipMassAt x e.val 0 +
      Utilities.Certificate.DegenerateSpec.DegSpec.blockSlope data.blockAt data.blockEnd
        data.blockRise e 0
  let head : Fin p → ℤ := fun e =>
    if d.length e = 0 then -(w.block anchor.val e.val 0).hi
    else w.rawChipMassAt x e.val (d.length e) -
      Utilities.Certificate.DegenerateSpec.DegSpec.blockSlope data.blockAt data.blockEnd
        data.blockRise e
        (d.length e - 1)
  change (∀ e, w.tailContribution anchor.val e.val ≤ tail e) ∧
      (∀ e, w.headContribution anchor.val e.val ≤ head e)
  have hTail : ∀ e, w.tailContribution anchor.val e.val ≤ tail e := by
    intro e
    by_cases hz : d.length e = 0
    · have hzL : ℓ e = 0 := by
        change ℓ e = 0 at hz
        exact hz
      have hcoord0 : eval (coordForm e.val) x = 0 := by rw [hCoord e, hzL]; rfl
      have hk := w.blockList_length_eq_one_of_coord_eq_zero core Γ x hW1 hW3 hx
        anchor e hcoord0
      obtain ⟨s, hs, -, -, hle⟩ :=
        w.exists_tailContribution_le core Γ x hW1 hW3 hx anchor e
      have hs0 : s = 0 := by omega
      have hmass := w.rawChipMassAt_eq_zero_of_coord_eq_zero core Γ x hn hW1 hW3 hx
        e hcoord0 0
      simp [tail, hz, hs0, hmass] at hle ⊢
      exact hle
    · obtain ⟨s, hs, hzero, hmax, hle⟩ :=
        w.exists_tailContribution_le core Γ x hW1 hW3 hx anchor e
      have hsel := w.tail_blockAt_eq_collapse d core Γ x hW1 hx hCoord anchor e
        (Nat.pos_of_ne_zero hz) s hs hzero hmax
      have hslope := (w.rich_blockSlope_bounds d core Γ x hW1 hW2 hx ℓ hCoord hn
        hForest hNotLoopy anchor e 0 (Nat.pos_of_ne_zero hz) rfl).1
      have hselData : data.blockAt e 0 = s := by
        change (w.richBlockEnds d core Γ x hW1 hx hCoord anchor e).blockAt 0 = s
        exact hsel
      rw [hselData] at hslope
      change (w.block anchor.val e.val s).lo ≤
        Utilities.Certificate.DegenerateSpec.DegSpec.blockSlope data.blockAt data.blockEnd
          data.blockRise e 0
        at hslope
      dsimp only [tail]
      rw [ite_eq_right hz]
      omega
  have hHead : ∀ e, w.headContribution anchor.val e.val ≤ head e := by
    intro e
    by_cases hz : d.length e = 0
    · have hzL : ℓ e = 0 := by
        change ℓ e = 0 at hz
        exact hz
      have hcoord0 : eval (coordForm e.val) x = 0 := by rw [hCoord e, hzL]; rfl
      have hk := w.blockList_length_eq_one_of_coord_eq_zero core Γ x hW1 hW3 hx
        anchor e hcoord0
      obtain ⟨s, hs, -, -, hle⟩ :=
        w.exists_headContribution_le core Γ x hW1 hW3 hx anchor e
      have hs0 : s = 0 := by omega
      have hmass := w.rawChipMassAt_eq_zero_of_coord_eq_zero core Γ x hn hW1 hW3 hx
        e hcoord0 (eval (coordForm e.val) x)
      rw [hmass] at hle
      simp [head, hz, hs0, hk] at hle ⊢
      exact hle
    · obtain ⟨s, hs, hhead, hlow, hle⟩ :=
        w.exists_headContribution_le core Γ x hW1 hW3 hx anchor e
      have hsel := w.head_blockAt_eq_collapse d core Γ x hW1 hx hCoord anchor e
        (Nat.pos_of_ne_zero hz) s hs hhead hlow
      have hslope := (w.rich_blockSlope_bounds d core Γ x hW1 hW2 hx ℓ hCoord hn
        hForest hNotLoopy anchor e (d.length e - 1) (by omega) rfl).2
      have hselData : data.blockAt e (d.length e - 1) =
          (w.blockList anchor.val e.val).length - 1 - s := by
        change (w.richBlockEnds d core Γ x hW1 hx hCoord anchor e).blockAt
          (d.length e - 1) = _
        exact hsel
      rw [hselData] at hslope
      change Utilities.Certificate.DegenerateSpec.DegSpec.blockSlope data.blockAt data.blockEnd
          data.blockRise e (d.length e - 1) ≤
        (w.block anchor.val e.val ((w.blockList anchor.val e.val).length - 1 - s)).hi
        at hslope
      have hcoordD : eval (coordForm e.val) x = (d.length e : ℤ) := by
        exact hCoord e
      rw [hcoordD] at hle
      dsimp only [head]
      rw [ite_eq_right hz]
      omega
  exact ⟨hTail, hHead⟩

/-- **The rich leaf's script reaches its plan's vertex, at any multiplicity.**

The body of this lemma used to sit inline inside `richLeaf_sound`, specialised
to one chip.  It is stated for `mult` chips because a legged rich leaf needs
exactly the same argument at the doubled anchor: `mult = 1` is a rank anchor,
`mult = m` is the `(comp x …)` plan certifying `D − m·1_x` winnable.  Nothing
in the argument cared how many chips were withdrawn — only that W5 stays
nonnegative after withdrawing them, which is the `hW5m` hypothesis. -/
theorem richDivisor_winnable_sub_smul (core : ExplicitPotential.Core n p)
    (w : RichWitness) (Γ : Context) (hn : 0 < n)
    (x : List ℤ) (hx : Γ.Holds x)
    (hW1 : w.w1Checks core Γ = true) (hW2 : w.w2Checks core Γ = true)
    (hW3 : w.w3Checks core = true) (hW4 : w.w4Checks core Γ = true)
    (ℓ : Fin p → ℕ) (hCoord : ∀ e : Fin p, eval (coordForm e.val) x = (ℓ e : ℤ))
    (hForest : IsForest core (zeroSet ℓ))
    (hNotLoopy : ¬ IsLoopy core (zeroSet ℓ))
    (fallback : Fin n) (mult : ℤ) (anchor : Fin n)
    (hW5m : ∀ v : Fin n, 0 ≤ w.w5MultResidual core mult anchor.val v.val) :
    winnable (censusSpec core hn ℓ hForest hNotLoopy).graph
      (w.richDivisor (censusSpec core hn ℓ hForest hNotLoopy) fallback x -
        mult • oneChip
          ((censusSpec core hn ℓ hForest hNotLoopy).coreVertex anchor)) := by
  classical
  set d := censusSpec core hn ℓ hForest hNotLoopy with hd
  have hCore : d.core = core := rfl
  let data := w.richCensusPiecewiseData core Γ x hW1 hW2 hx ℓ hCoord hn
    hForest hNotLoopy anchor
  let script := w.richCensusPiecewiseScript core Γ x hW1 hW2 hx ℓ hCoord hn
    hForest hNotLoopy anchor
  have hInv := w.repInvariant_of_w1w2_census core Γ x hW1 hW2 hx anchor hn ℓ
    hCoord hForest hNotLoopy
  let tail : Fin p → ℤ := fun e =>
    if d.length e = 0 then (w.block anchor.val e.val 0).lo
    else w.rawChipMassAt x e.val 0 +
      Utilities.Certificate.DegenerateSpec.DegSpec.blockSlope data.blockAt data.blockEnd
        data.blockRise e 0
  let head : Fin p → ℤ := fun e =>
    if d.length e = 0 then -(w.block anchor.val e.val 0).hi
    else w.rawChipMassAt x e.val (d.length e) -
      Utilities.Certificate.DegenerateSpec.DegSpec.blockSlope data.blockAt data.blockEnd
        data.blockRise e
        (d.length e - 1)
  have hEndpointBounds := richCensusEndpoint_bounds core w Γ hn x hx hW1 hW2 hW3
    ℓ hCoord hForest hNotLoopy anchor
  change (∀ e, w.tailContribution anchor.val e.val ≤ tail e) ∧
    (∀ e, w.headContribution anchor.val e.val ≤ head e) at hEndpointBounds
  obtain ⟨hTail, hHead⟩ := hEndpointBounds
  refine ⟨w.richDivisor d fallback x - mult • oneChip (d.coreVertex anchor) +
    prin d.graph script, ?_, ?_⟩
  · intro vertex
    rcases vertex with c | interior
    · have hInl : (Sum.inl c : d.Vertex) = d.coreVertex c.val :=
        (congrArg Sum.inl (Subtype.ext c.property)).symm
      rw [hInl]
      have hChip : (mult • oneChip (G := d.graph) (d.coreVertex anchor))
          (d.coreVertex c.val) =
          (if d.rep anchor = d.rep c.val then mult else 0) := by
        unfold oneChip
        rw [Pi.smul_apply]
        by_cases hr : d.rep anchor = d.rep c.val
        · rw [ite_eq_left ((d.coreVertex_eq_iff c.val anchor).mpr hr.symm), ite_eq_left hr]
          simp
        · rw [ite_eq_right (fun heq => hr (((d.coreVertex_eq_iff c.val anchor).mp heq).symm)),
            ite_eq_right hr]
          simp
      have hPrin : prin d.graph script (d.coreVertex c.val) =
          ∑ e : Fin p,
            ((if d.rep (d.core.tail e) = d.rep c.val then
                Utilities.Certificate.DegenerateSpec.DegSpec.blockSlope data.blockAt data.blockEnd
                  data.blockRise e 0 else 0) +
              (if d.rep (d.core.head e) = d.rep c.val then
                -Utilities.Certificate.DegenerateSpec.DegSpec.blockSlope data.blockAt data.blockEnd
                  data.blockRise e (d.length e - 1) else 0)) := by
        simpa [script, data, richCensusPiecewiseScript] using
          (d.prin_piecewiseScript_coreVertex hInv c.val)
      have hActual := w.w5ActualResidual_class_nonneg d core mult anchor hW5m tail head
        hTail hHead c.val
      rw [w.classSum_w5ActualResidual_eq d core mult anchor tail head c.val] at hActual
      rw [← hCore] at hActual
      have hEndpoint : ∀ e : Fin p,
          ((if d.rep (d.core.tail e) = d.rep c.val then tail e else 0) +
            (if d.rep (d.core.head e) = d.rep c.val then head e else 0)) ≤
          ((if d.rep (d.core.tail e) = d.rep c.val then
              w.rawChipMassAt x e.val 0 else 0) +
            (if d.rep (d.core.head e) = d.rep c.val then
              headMassAdj d w x e else 0)) +
          ((if d.rep (d.core.tail e) = d.rep c.val then
              Utilities.Certificate.DegenerateSpec.DegSpec.blockSlope data.blockAt data.blockEnd
                data.blockRise e 0 else 0) +
            (if d.rep (d.core.head e) = d.rep c.val then
              -Utilities.Certificate.DegenerateSpec.DegSpec.blockSlope data.blockAt data.blockEnd
                data.blockRise e (d.length e - 1) else 0)) := by
        intro e
        by_cases hz : d.length e = 0
        · have hzL : ℓ e = 0 := by
            change ℓ e = 0 at hz
            exact hz
          have hcoord0 : eval (coordForm e.val) x = 0 := by rw [hCoord e, hzL]; rfl
          have hk := w.blockList_length_eq_one_of_coord_eq_zero core Γ x hW1 hW3 hx
            anchor e hcoord0
          have hmass0 := w.rawChipMassAt_eq_zero_of_coord_eq_zero core Γ x hn
            hW1 hW3 hx e hcoord0 0
          have hRep : d.rep (d.core.tail e) = d.rep (d.core.head e) :=
            d.rep_zero e hz
          have hW2' := hW2
          simp only [w2Checks, ExplicitPotential.allFin_eq_true_iff,
            List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hW2'
          have hlohi : (w.block anchor.val e.val 0).lo ≤
              (w.block anchor.val e.val 0).hi := by
            exact ((hW2' anchor e).1 0 (by simp [hk])).1.1
          simp only [tail, head, hz, ite_eq_left, headMassAdj, hmass0]
          by_cases hclass : d.rep (d.core.tail e) = d.rep c.val
          · have hclassH : d.rep (d.core.head e) = d.rep c.val := by
              rw [← hRep]
              exact hclass
            rw [ite_eq_left hclass, ite_eq_left hclassH]
            simp
            omega
          · have hclassH : d.rep (d.core.head e) ≠ d.rep c.val := by
              rwa [← hRep]
            rw [ite_eq_right hclass, ite_eq_right hclassH]
            omega
        · by_cases ht : d.rep (d.core.tail e) = d.rep c.val
          all_goals
            by_cases hh : d.rep (d.core.head e) = d.rep c.val
            all_goals
              simp [tail, head, hz, headMassAdj, ht, hh]
            all_goals omega
      have hEndpointSum :
          (∑ e : Fin p,
            ((if d.rep (d.core.tail e) = d.rep c.val then tail e else 0) +
              (if d.rep (d.core.head e) = d.rep c.val then head e else 0))) ≤
          (∑ e : Fin p,
            (((if d.rep (d.core.tail e) = d.rep c.val then
                w.rawChipMassAt x e.val 0 else 0) +
              (if d.rep (d.core.head e) = d.rep c.val then
                headMassAdj d w x e else 0)) +
            ((if d.rep (d.core.tail e) = d.rep c.val then
                Utilities.Certificate.DegenerateSpec.DegSpec.blockSlope data.blockAt data.blockEnd
                  data.blockRise e 0 else 0) +
              (if d.rep (d.core.head e) = d.rep c.val then
                -Utilities.Certificate.DegenerateSpec.DegSpec.blockSlope data.blockAt data.blockEnd
                  data.blockRise e (d.length e - 1) else 0)))) :=
        Finset.sum_le_sum fun e _ => hEndpoint e
      simp only [ge_iff_le, Pi.add_apply, Pi.sub_apply]
      unfold richDivisor
      rw [Pi.add_apply, w.richCoreDivisor_coreVertex d c.val,
        w.rawChipDivisor_coreVertex_eq d core Γ x hW1 hW3 hx hCoord anchor fallback
          c.val, hChip, hPrin]
      rw [Finset.sum_add_distrib] at hEndpointSum
      rw [Finset.sum_add_distrib] at hEndpointSum
      rw [Finset.sum_add_distrib] at hActual
      omega
    · rcases interior with ⟨e, o⟩
      simp only [ge_iff_le, Pi.add_apply, Pi.sub_apply]
      have hChip : (mult • oneChip (G := d.graph) (d.coreVertex anchor))
          (d.interiorVertex e o) = 0 := by
        unfold oneChip
        rw [Pi.smul_apply, ite_eq_right]
        · simp
        · exact fun h => interiorVertex_ne_coreVertex d e o anchor h
      unfold richDivisor
      rw [Pi.add_apply]
      change 0 ≤ w.richCoreDivisor d (d.interiorVertex e o) +
        w.rawChipDivisor d (evaluatedChipVertex d fallback x) (d.interiorVertex e o) -
        (mult • oneChip (G := d.graph) (d.coreVertex anchor)) (d.interiorVertex e o) +
        prin d.graph script (d.interiorVertex e o)
      rw [w.richCoreDivisor_interiorVertex d e o,
        w.rawChipDivisor_interiorVertex_eq_rawChipMassAt d core Γ x hW1 hW3 hx
          hCoord anchor fallback e o, hChip]
      have hPrin : prin d.graph script (d.interiorVertex e o) =
          Utilities.Certificate.DegenerateSpec.DegSpec.blockSlope data.blockAt data.blockEnd
            data.blockRise
              e (o.val + 1) -
            Utilities.Certificate.DegenerateSpec.DegSpec.blockSlope data.blockAt data.blockEnd
              data.blockRise
              e o.val := by
        simpa [script, data, richCensusPiecewiseScript] using
          (d.prin_piecewiseScript_interiorVertex hInv e o)
      rw [hPrin]
      let b := w.richBlockEnds d core Γ x hW1 hx hCoord anchor e
      have hmono : b.blockAt o.val ≤ b.blockAt (o.val + 1) :=
        b.blockAt_mono (by omega) (by omega) (by omega)
      by_cases hSame : b.blockAt (o.val + 1) = b.blockAt o.val
      · have hRaw := w.rawChipMassAt_eq_zero_of_sameSelector d core Γ x hW1 hW3 hx
            hCoord anchor e o (by simpa [b] using hSame.symm)
        rw [hRaw, zero_add, sub_zero]
        have hSameData : data.blockAt e (o.val + 1) = data.blockAt e o.val := by
          change b.blockAt (o.val + 1) = b.blockAt o.val
          exact hSame
        have hnonneg := d.prin_piecewiseScript_interiorVertex_nonneg_of_sameBlock
          hInv e o hSameData
        rw [d.prin_piecewiseScript_interiorVertex hInv e o] at hnonneg
        omega
      · have hChange : b.blockAt o.val < b.blockAt (o.val + 1) := by omega
        have hIncoming := (w.rich_blockSlope_bounds d core Γ x hW1 hW2 hx ℓ hCoord
          hn hForest hNotLoopy anchor e o.val (by omega) rfl).2
        have hOutgoing := (w.rich_blockSlope_bounds d core Γ x hW1 hW2 hx ℓ hCoord
          hn hForest hNotLoopy anchor e (o.val + 1) (by omega) rfl).1
        have hW4actual := w.w4_actual_nonneg_of_rich_selector_change d core Γ x hW1
          hW4 hx hCoord anchor e o (by simpa [b] using hChange)
          (Utilities.Certificate.DegenerateSpec.DegSpec.blockSlope data.blockAt data.blockEnd
            data.blockRise
            e o.val)
          (Utilities.Certificate.DegenerateSpec.DegSpec.blockSlope data.blockAt data.blockEnd
            data.blockRise
            e (o.val + 1))
          (by simpa [data, richCensusPiecewiseData,
            Utilities.Certificate.DegenerateSpec.DegSpec.decodePiecewiseData, b] using hIncoming)
          (by simpa [data, richCensusPiecewiseData,
            Utilities.Certificate.DegenerateSpec.DegSpec.decodePiecewiseData, b] using hOutgoing)
        have hRaw := w.rawChipMassAt_selectorChange d core Γ x hW1 hW3 hx hCoord
          anchor e o (by simpa [b] using hChange)
        rw [hRaw]
        unfold w4Actual at hW4actual
        omega
  · exact StrongSeparator.linearEquiv_add_prin
      (w.richDivisor d fallback x - mult • oneChip (d.coreVertex anchor)) script


theorem richLeaf_sound (core : ExplicitPotential.Core n p) (w : RichWitness)
    (Γ : Context) (degree : ℤ) (hp : p ≤ m) (hn : 0 < n)
    (hchk : w.richLeafChecks m core Γ degree = true)
    (point : Fin m → ℤ) (hΓ : Γ.Holds (List.ofFn point))
    (ℓ : Fin p → ℕ) (hlen : ∀ e : Fin p, (ℓ e : ℤ) = point (Fin.castLE hp e))
    (hForest : IsForest core (zeroSet ℓ))
    (hNotLoopy : ¬ IsLoopy core (zeroSet ℓ)) :
    BNExists (censusSpec core hn ℓ hForest hNotLoopy).graph 1 degree := by
  classical
  simp only [richLeafChecks, Bool.and_eq_true, decide_eq_true_eq,
    ExplicitPotential.allFin_eq_true_iff] at hchk
  obtain ⟨hpre, hDegree⟩ := hchk
  obtain ⟨hpre, hSlot⟩ := hpre
  obtain ⟨hpre, hW5⟩ := hpre
  obtain ⟨hpre, hW4⟩ := hpre
  obtain ⟨hpre, hW3⟩ := hpre
  obtain ⟨hpre, hW2⟩ := hpre
  obtain ⟨hpre, hW1⟩ := hpre
  obtain ⟨hpre, hLength⟩ := hpre
  obtain ⟨hLoopless, hConnected⟩ := hpre
  let x := List.ofFn point
  have hx : Γ.Holds x := hΓ
  have hCoord : ∀ e : Fin p, eval (coordForm e.val) x = ℓ e := by
    intro e
    have heval := eval_coordForm_ofFn point (Fin.castLE hp e)
    simpa [x] using heval.trans (hlen e).symm
  let d := censusSpec core hn ℓ hForest hNotLoopy
  have hCore : d.core = core := rfl
  let fallback : Fin n := ⟨0, hn⟩
  refine ⟨w.richDivisor d fallback x, ?_, ?_⟩
  · exact w.deg_richDivisor_eq_declared d fallback x hLength hDegree
  · apply StrongSeparator.rank_ge_one_of_strongSeparatorCertificate
      (Utilities.Certificate.DegenerateSpec.DegSpec.graph_connected_of_coreConnected d
        ((ExplicitPotential.Core.connectedCheck_eq_true_iff core).mp hConnected))
      (ExplicitPotential.CertificateData.degenerateCoreVertices_nonempty d)
      (Utilities.Certificate.DegenerateSpec.DegSpec.strongSeparatorCertificate d)
    intro coreVertex hCoreVertex
    obtain ⟨anchor, -, rfl⟩ := Finset.mem_image.mp hCoreVertex
    have hW5m : ∀ v : Fin n, 0 ≤ w.w5MultResidual core 1 anchor.val v.val :=
      fun v => w.w5Residual_nonneg_of_w5Checks core hW5 anchor v
    have := w.richDivisor_winnable_sub_smul core Γ hn x hx hW1 hW2 hW3 hW4 ℓ
      hCoord hForest hNotLoopy fallback 1 anchor hW5m
    simpa [Utilities.Certificate.StrongSeparator.Reaches,
      one_smul] using this

end Utilities.Subdivision.ClosedRowProof.RichWitness
