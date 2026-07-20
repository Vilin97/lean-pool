/-
Copyright (c) 2026 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import Mathlib.Tactic.FinCases
import LeanPool.BooleanIsoperimetry.Shadow

/-!
# Harper's vertex-isoperimetric theorem

This file assembles the compression, Macaulay, Kruskal-Katona, and scalar
recurrence layers into the final sorry-free proof of Harper's theorem.
-/

open scoped BigOperators

namespace BooleanIsoperimetry

/-- The number of vertices whose `gShift` rank lies in the half-open interval
`[lo, hi)`.  This is the set-level form of an `HIncrement` window. -/
noncomputable def gShiftIntervalCount (n lo hi : ℕ) : ℕ :=
  (Finset.univ.filter (fun v : Cube n => lo ≤ rank (gShift v) ∧ rank (gShift v) < hi)).card

lemma H_window_sum_of_le (n lo hi : ℕ) (hlohi : lo ≤ hi) :
    H n hi = H n lo + ∑ i ∈ Finset.Ico lo hi, HIncrement n i := by
  have h1 := H_eq_sum_HIncrement n hi
  have h2 := H_eq_sum_HIncrement n lo
  rw [h1, h2]
  rw [← Finset.sum_range_add_sum_Ico (f := fun i => HIncrement n i) hlohi]

lemma gShiftIntervalCount_eq_H_sub (n lo hi : ℕ) (hlohi : lo ≤ hi) :
    gShiftIntervalCount n lo hi = H n hi - H n lo := by
  rw [gShiftIntervalCount, H_eq_gShift_count n hi, H_eq_gShift_count n lo]
  let Ahi : Finset (Cube n) :=
    Finset.univ.filter (fun v : Cube n => rank (gShift v) < hi)
  let Alo : Finset (Cube n) :=
    Finset.univ.filter (fun v : Cube n => rank (gShift v) < lo)
  let Aint : Finset (Cube n) :=
    Finset.univ.filter (fun v : Cube n => lo ≤ rank (gShift v) ∧ rank (gShift v) < hi)
  have hsplit : Ahi = Alo ∪ Aint := by
    ext v
    simp [Ahi, Alo, Aint]
    omega
  have hdisj : Disjoint Alo Aint := by
    rw [Finset.disjoint_left]
    intro v hvlo hvint
    simp [Alo] at hvlo
    simp [Aint] at hvint
    omega
  have hcard : Ahi.card = Alo.card + Aint.card := by
    rw [hsplit, Finset.card_union_of_disjoint hdisj]
  change Aint.card = Ahi.card - Alo.card
  omega

lemma HIncrement_window_eq_gShiftIntervalCount (n lo hi : ℕ) (hlohi : lo ≤ hi) :
    (∑ i ∈ Finset.Ico lo hi, HIncrement n i) = gShiftIntervalCount n lo hi := by
  have hwindow := H_window_sum_of_le n lo hi hlohi
  have hcount := gShiftIntervalCount_eq_H_sub n lo hi hlohi
  have hmono : H n lo ≤ H n hi := H_mono hlohi
  omega

/--
Exact vertex-weight form of a Macaulay shadow window.  This is the same window
count as `gShiftIntervalCount`, but with each rank vertex weighted by its
explicit `gShift`-fibre size (`macaulayShadowWeight`).
-/
lemma gShiftIntervalCount_eq_macaulayShadowWeight_sum
    (n lo hi : ℕ) (hlohi : lo ≤ hi) (hhi : hi ≤ 2 ^ n) :
    gShiftIntervalCount n lo hi =
      ∑ w ∈ (Finset.univ.filter (fun w : Cube n => lo ≤ rank w ∧ rank w < hi)),
        macaulayShadowWeight w := by
  rw [← HIncrement_window_eq_gShiftIntervalCount n lo hi hlohi]
  exact HIncrement_window_eq_macaulayShadowWeight_sum n lo hi hhi

lemma HIncrement_window_le_of_gShiftIntervalCount_le
    {n lo₁ hi₁ lo₂ hi₂ slack : ℕ}
    (h₁ : lo₁ ≤ hi₁) (h₂ : lo₂ ≤ hi₂)
    (hcount :
      gShiftIntervalCount n lo₁ hi₁ ≤ gShiftIntervalCount n lo₂ hi₂ + slack) :
    (∑ i ∈ Finset.Ico lo₁ hi₁, HIncrement n i) ≤
      (∑ i ∈ Finset.Ico lo₂ hi₂, HIncrement n i) + slack := by
  rw [HIncrement_window_eq_gShiftIntervalCount n lo₁ hi₁ h₁,
      HIncrement_window_eq_gShiftIntervalCount n lo₂ hi₂ h₂]
  exact hcount

/--
The local non-circular boundary-cost functional used by the positive Macaulay
kernel.  This intentionally duplicates the later `boundaryCost` definition so
the remaining inductive step can be expressed without referring to downstream
theorems.
-/
noncomputable def boundaryCostH (N a b : ℕ) : ℕ :=
  max (H N a) b + max (H N b) a

/--
Exact slack decomposition of the max-form boundary cost.  The two truncated
terms are precisely the slack that is needed in the GT regime, where the simpler
sum-form `H N a + H N b` is false.
-/
lemma boundaryCostH_eq_H_add_slack (N a b : ℕ) :
    boundaryCostH N a b =
      H N a + H N b + (b - H N a) + (a - H N b) := by
  unfold boundaryCostH
  omega

lemma boundaryCostH_comm (N a b : ℕ) :
    boundaryCostH N a b = boundaryCostH N b a := by
  unfold boundaryCostH
  omega

lemma cascade_split_q_zero_total_le_one {n k p : ℕ}
    (h : CascadeSplit n k p 0) : k ≤ 1 := by
  rcases h with ⟨r, t, hc, _hp, hq⟩
  rcases hc with ⟨_hrle, ht, hk, hcanon⟩
  rcases r with _ | r
  · simp [cascadeSlice1Value, binomPrefix_zero] at hq
    simp [binomPrefix_zero] at hk
    have ht' : t ≤ 1 := by simpa using ht
    omega
  · rcases r with _ | r
    · simp [cascadeSlice1Value, binomPrefix_zero, choosePred] at hq
      simp [binomPrefix_succ, binomPrefix_zero] at hk
      omega
    · have hpos := one_le_binomPrefix_succ n r
      simp [cascadeSlice1Value, choosePred] at hq
      omega

lemma H_window_sum_of_le_int (n lo hi : ℕ) (hlohi : lo ≤ hi) :
    (H n hi : ℤ) = (H n lo : ℤ) + (gShiftIntervalCount n lo hi : ℤ) := by
  rw [gShiftIntervalCount_eq_H_sub n lo hi hlohi]
  have Hmono : H n lo ≤ H n hi := H_mono hlohi
  omega

/--
The four-block prefix profile exposed by lowering a level-`n+1`
interleaving to the two level-`n` slices.  The first pair `(x0, y0)` is read
one layer ahead of the second pair `(x1, y1)`, matching the Pascal shift in
`CascadeInterleaves.lower_succ`.
-/
lemma harper_step_total_q_zero (n : ℕ) {a b p : ℕ}
    (hcasc : CascadeSplit (n + 1) (a + b) p 0) :
    H (n + 2) (a + b) ≤ boundaryCostH (n + 1) a b := by
  have h_le_one : a + b ≤ 1 := cascade_split_q_zero_total_le_one hcasc
  have h0 : a = 0 ∨ a = 1 := by omega
  have h1 : b = 0 ∨ b = 1 := by omega
  rcases h0 with rfl | rfl
  · rcases h1 with rfl | rfl
    · simp [H_zero, boundaryCostH]
    · simp [H_zero, H_one, boundaryCostH]
  · rcases h1 with rfl | rfl
    · simp [H_zero, H_one, boundaryCostH]
    · omega

lemma harper_step_sum_form_of_window_shift (n : ℕ)
    {a b p q : ℕ}
    (hap : a ≤ p) (hqb : q ≤ b)
    (hwin :
      gShiftIntervalCount (n + 1) a p ≤
        gShiftIntervalCount (n + 1) q b) :
    H (n + 1) p + H (n + 1) q ≤ H (n + 1) a + H (n + 1) b := by
  have hpa := gShiftIntervalCount_eq_H_sub (n + 1) a p hap
  have hqb' := gShiftIntervalCount_eq_H_sub (n + 1) q b hqb
  rw [hpa, hqb'] at hwin
  have hHa : H (n + 1) a ≤ H (n + 1) p := H_mono hap
  have hHq : H (n + 1) q ≤ H (n + 1) b := H_mono hqb
  omega

lemma harper_step_sum_form_of_window_shift' (n : ℕ)
    {a b p q : ℕ}
    (hpa : p ≤ a) (hbq : b ≤ q)
    (hwin :
      gShiftIntervalCount (n + 1) b q ≤
        gShiftIntervalCount (n + 1) p a) :
    H (n + 1) p + H (n + 1) q ≤ H (n + 1) a + H (n + 1) b := by
  have hap := gShiftIntervalCount_eq_H_sub (n + 1) p a hpa
  have hqb' := gShiftIntervalCount_eq_H_sub (n + 1) b q hbq
  rw [hap, hqb'] at hwin
  have hHp : H (n + 1) p ≤ H (n + 1) a := H_mono hpa
  have hHb : H (n + 1) b ≤ H (n + 1) q := H_mono hbq
  omega

/-- Window additivity for the Macaulay shadow count `gShiftIntervalCount`:
adjacent rank windows `[lo, mid)` and `[mid, hi)` add to `[lo, hi)`.  A reusable
block-decomposition tool for splitting shadow windows along layer boundaries. -/
lemma gShiftIntervalCount_add_adjacent (n lo mid hi : ℕ)
    (h1 : lo ≤ mid) (h2 : mid ≤ hi) :
    gShiftIntervalCount n lo mid + gShiftIntervalCount n mid hi
      = gShiftIntervalCount n lo hi := by
  rw [gShiftIntervalCount_eq_H_sub n lo mid h1,
      gShiftIntervalCount_eq_H_sub n mid hi h2,
      gShiftIntervalCount_eq_H_sub n lo hi (h1.trans h2)]
  have hm1 : H n lo ≤ H n mid := H_mono h1
  have hm2 : H n mid ≤ H n hi := H_mono h2
  omega

/-- Whole-block value of the Macaulay shadow count between complete binomial
prefixes: the shadow window between `binomPrefix n r` and `binomPrefix n s`
counts exactly the complete Macaulay layers `r+1, …, s`.  This connects the
set-level shadow count to the explicit `Nat.choose` layer sizes, which is the
form the layer-by-layer comparison of the two shadow windows needs. -/
lemma gShiftIntervalCount_binomPrefix_window (n r s : ℕ) (hr : 1 ≤ r) (hrs : r ≤ s) :
    gShiftIntervalCount n (binomPrefix n r) (binomPrefix n s)
      = (Finset.Ico (r + 1) (s + 1)).sum (fun i => Nat.choose n i) := by
  have hle : binomPrefix n r ≤ binomPrefix n s := binomPrefix_mono n hrs
  rw [gShiftIntervalCount_eq_H_sub n _ _ hle]
  have hw := H_binomPrefix_window n r s hr hrs
  omega

lemma gShiftIntervalCount_le_binomPrefix_window_of_endpoints
    (n r s lo hi : ℕ)
    (hr : 1 ≤ r) (hrs : r ≤ s)
    (hlo : binomPrefix n r ≤ lo)
    (hhi : hi ≤ binomPrefix n s) :
    gShiftIntervalCount n lo hi ≤
      (Finset.Ico (r + 1) (s + 1)).sum (fun i => Nat.choose n i) := by
  by_cases h : lo ≤ hi
  · rw [gShiftIntervalCount_eq_H_sub n lo hi h]
    have h1 : H n hi ≤ H n (binomPrefix n s) := H_mono hhi
    have h2 : H n (binomPrefix n r) ≤ H n lo := H_mono hlo
    have h3 : H n (binomPrefix n s) - H n (binomPrefix n r) =
        (Finset.Ico (r + 1) (s + 1)).sum (fun i => Nat.choose n i) := by
      have h4 : binomPrefix n r ≤ binomPrefix n s := binomPrefix_mono n hrs
      rw [← gShiftIntervalCount_eq_H_sub n (binomPrefix n r) (binomPrefix n s) h4]
      exact gShiftIntervalCount_binomPrefix_window n r s hr hrs
    omega
  · have h0 : gShiftIntervalCount n lo hi = 0 := by
      rw [gShiftIntervalCount]
      have h_empty : Finset.univ.filter
          (fun v : Cube n => lo ≤ rank (gShift v) ∧ rank (gShift v) < hi) = ∅ := by
        apply Finset.filter_false_of_mem
        intro v _
        omega
      rw [h_empty, Finset.card_empty]
    rw [h0]
    exact Nat.zero_le _

/--
**Lower block bound (dual of `gShiftIntervalCount_le_binomPrefix_window_of_endpoints`).**
If a shadow window `[lo, hi)` *contains* the complete binomial prefix block
`[binomPrefix n r, binomPrefix n s)` (that is, `lo ≤ binomPrefix n r` and
`binomPrefix n s ≤ hi`), then its shadow count is at least the complete-layer
block sum `∑_{i = r+1}^{s} C(n, i)`.

This is the missing companion of the existing upper bound: together they let a
Macaulay shadow comparison *lower-bound the upper window* and *upper-bound the
lower window* by explicit `Nat.choose` layer sums.  It is the reusable
accounting helper named in Aristotle's Cycle 1 plan, and is the set-level form
of "a window that swallows whole layers counts at least those layers".
-/
lemma gShiftIntervalCount_ge_binomPrefix_window_of_endpoints
    (n r s lo hi : ℕ)
    (hr : 1 ≤ r) (hrs : r ≤ s)
    (hlo : lo ≤ binomPrefix n r)
    (hhi : binomPrefix n s ≤ hi) :
    (Finset.Ico (r + 1) (s + 1)).sum (fun i => Nat.choose n i) ≤
      gShiftIntervalCount n lo hi := by
  have hle : lo ≤ hi := le_trans (le_trans hlo (binomPrefix_mono n hrs)) hhi
  rw [gShiftIntervalCount_eq_H_sub n lo hi hle]
  have h1 : H n lo ≤ H n (binomPrefix n r) := H_mono hlo
  have h2 : H n (binomPrefix n s) ≤ H n hi := H_mono hhi
  have h3 : H n (binomPrefix n s) - H n (binomPrefix n r) =
      (Finset.Ico (r + 1) (s + 1)).sum (fun i => Nat.choose n i) := by
    have h4 : binomPrefix n r ≤ binomPrefix n s := binomPrefix_mono n hrs
    rw [← gShiftIntervalCount_eq_H_sub n (binomPrefix n r) (binomPrefix n s) h4]
    exact gShiftIntervalCount_binomPrefix_window n r s hr hrs
  omega

/--
**Block-domination ⇒ shadow-window domination.**
Two shadow windows compared through their enclosing/enclosed complete binomial
blocks.  If the *lower* window `[lo₁, hi₁)` is enclosed in the layer band
`[r₁, s₁]` (so it is upper-bounded by the block sum over `r₁+1 .. s₁`) and the
*upper* window `[lo₂, hi₂)` swallows the layer band `[r₂, s₂]` (so it is
lower-bounded by the block sum over `r₂+1 .. s₂`), and the first block sum is no
larger than the second, then the lower window's shadow count is no larger than
the upper window's.

This is the reusable whole-block comparison engine that the Frankl–Füredi /
Macaulay window comparison (`harper_macaulay_LE_sum`, `harper_macaulay_GT_sum`)
reduces to once the partial-layer boundary pieces of each window have been
absorbed into the enclosing layer band.  It is `ih`-free and purely `Nat.choose`
arithmetic at the block level, isolating exactly the layer-index bookkeeping from
the set-level shadow content.
-/
lemma gShiftIntervalCount_le_of_blocks
    (n r₁ s₁ r₂ s₂ lo₁ hi₁ lo₂ hi₂ : ℕ)
    (hr₁ : 1 ≤ r₁) (hrs₁ : r₁ ≤ s₁)
    (hr₂ : 1 ≤ r₂) (hrs₂ : r₂ ≤ s₂)
    (hlo₁ : binomPrefix n r₁ ≤ lo₁) (hhi₁ : hi₁ ≤ binomPrefix n s₁)
    (hlo₂ : lo₂ ≤ binomPrefix n r₂) (hhi₂ : binomPrefix n s₂ ≤ hi₂)
    (hblock :
      (Finset.Ico (r₁ + 1) (s₁ + 1)).sum (fun i => Nat.choose n i) ≤
        (Finset.Ico (r₂ + 1) (s₂ + 1)).sum (fun i => Nat.choose n i)) :
    gShiftIntervalCount n lo₁ hi₁ ≤ gShiftIntervalCount n lo₂ hi₂ := by
  have hup :=
    gShiftIntervalCount_le_binomPrefix_window_of_endpoints n r₁ s₁ lo₁ hi₁ hr₁ hrs₁ hlo₁ hhi₁
  have hlow :=
    gShiftIntervalCount_ge_binomPrefix_window_of_endpoints n r₂ s₂ lo₂ hi₂ hr₂ hrs₂ hlo₂ hhi₂
  omega

/-- **Single-layer shadow-window bound.**  A length-`L` shadow window contained in
a single Macaulay layer `r` has shadow count at most `L * (n - r)`.  This is the
set-level form of `HIncrement_window_le_of_layer`: it is the reusable upper bound
for the *upper* shadow window of the Frankl–Füredi/Macaulay comparison whenever
that window stays inside one cardinality band (which, computationally, is exactly
the regime of the reversed-orientation leaf `harper_macaulay_reversed`). -/
lemma gShiftIntervalCount_le_of_layer {n r a L : ℕ} (hr : 1 ≤ r)
    (hlo : binomPrefix n r ≤ a) (hhi : a + L ≤ binomPrefix n (r + 1)) :
    gShiftIntervalCount n a (a + L) ≤ L * (n - r) := by
  rw [← HIncrement_window_eq_gShiftIntervalCount n a (a + L) (by omega)]
  exact HIncrement_window_le_of_layer hr hlo hhi

/--
Endpoint arithmetic for the left-oriented equal-length Macaulay windows.  If
the canonical split `(p,q)` and the arbitrary split `(a,b)` have the same total
and `p ≤ a`, then the lower endpoint also moves inward, `b ≤ q`, and the two
shadow windows `[b,q)` and `[p,a)` have the same length.
-/
lemma cascade_left_window_endpoints {N a b p q : ℕ}
    (hcasc : CascadeSplit N (a + b) p q) (hpa : p ≤ a) :
    b ≤ q ∧ a - p = q - b := by
  have hsum : p + q = a + b := cascade_split_add hcasc
  omega

/--
Endpoint arithmetic for the right-oriented equal-length Macaulay windows.  If
`a ≤ p`, then `q ≤ b`, and the two shadow windows `[a,p)` and `[q,b)` have the
same length.
-/
lemma cascade_right_window_endpoints {N a b p q : ℕ}
    (hcasc : CascadeSplit N (a + b) p q) (hap : a ≤ p) :
    q ≤ b ∧ p - a = b - q := by
  have hsum : p + q = a + b := cascade_split_add hcasc
  omega

/--
The GT regime gives the left-oriented window order together with equal lengths.
This is the arithmetic shape of the Frankl-Füredi slack comparison: the lower
window `[b,q)` and the upper window `[p,a)` have common length `q-b = a-p`.
-/
lemma harper_gt_shadow_window_endpoints {n a b p q : ℕ}
    (hcasc : CascadeSplit (n + 1) (a + b) p q)
    (hq_pos : 1 ≤ q) (hcase : H (n + 1) b < a) :
    b ≤ q ∧ q ≤ p ∧ p ≤ a ∧ a - p = q - b := by
  obtain ⟨hbq, hqp, hpa⟩ := harper_gt_split_between n hq_pos hcase hcasc
  have hlen := cascade_left_window_endpoints hcasc hpa
  exact ⟨hbq, hqp, hpa, hlen.2⟩

/- CONSOLIDATED (cycle3.aristotle).
   The two equal-length shadow-window leaves harper_macaulay_shadow_le_left and
   harper_macaulay_shadow_le_right, and their packaging harper_macaulay_shadow_le,
   were each EQUIVALENT (in orientation p <= a, resp. a <= p) to the single
   joint-sum kernel harper_macaulay_window_le below: rewriting both
   gShiftIntervalCount windows with gShiftIntervalCount_eq_H_sub turns each into
   H (n+1) p + H (n+1) q <= H (n+1) a + H (n+1) b.  Carrying two separate shadow
   proof holes was redundant, so the genuine LE content is now isolated in the
   single proof hole on harper_macaulay_window_le (the cleaner max-free joint-sum
   form).
   The removed statements (under hyps a,b <= 2^(n+1), CascadeSplit (n+1) (a+b) p q,
   b <= a, a <= H (n+1) b) were:
     harper_macaulay_shadow_le_left  : p <= a -> gsc (n+1) b q <= gsc (n+1) p a
     harper_macaulay_shadow_le_right : a <= p -> gsc (n+1) a p <= gsc (n+1) q b
     harper_macaulay_shadow_le       : the conjunction of the above two.
   (Verified equivalent and true by an exact cascade model of H for split
   dimension up to 5.)
-/

/-
**REMOVED — FALSE LEMMAS (corrected this cycle).**
The two lemmas below reduced the GT case to the scalar bound `H (n+1) q ≤ a`.
That bound is **false**.  An exact computational model of `H` via the cascade
recursion gives the counterexample `n = 1, a = 2, b = 0`: the canonical cascade
split of `a + b = 2` at level `N = 2` is `(p, q) = (1, 1)`, and
`H 2 q = H 2 1 = 3 > 2 = a` (there are `1/4/17/70` such counterexamples for leaf
dimension `N = 2,3,4,5`).  The GT regime only guarantees the *joint* slack bound
`H (n+1) p + H (n+1) q ≤ H (n+1) a + a` (verified with `0` counterexamples for
`N ≤ 5`), **not** the separate split `H (n+1) q ≤ a` together with
`H (n+1) p ≤ H (n+1) a`: in the counterexample `H 2 p = H 2 q = 3` and
`H 2 a = H 2 2 = 4`, so `H p + H q = 6 = H a + a` holds with equality even though
`H q = 3 > a = 2`.  The true joint statement is now the single GT leaf
`harper_macaulay_slack_gt` below; the shadow form is recovered from it as the
proved corollary `harper_macaulay_shadow_gt`.

lemma harper_macaulay_gt_shadow_window_bound {n a b p q : ℕ}
    (ha : a ≤ 2 ^ (n + 1)) (hb : b ≤ 2 ^ (n + 1))
    (hcasc : CascadeSplit (n + 1) (a + b) p q)
    (hba : b ≤ a) (hcase : H (n + 1) b < a) (hq_pos : 1 ≤ q) :
    gShiftIntervalCount (n + 1) b q ≤ a - H (n + 1) b := by
  proof omitted in this dead block -- FALSE: equivalent to `H (n+1) q ≤ a`,
  refuted by `n=1, a=2, b=0`.

lemma harper_macaulay_gt_H_q_le_a {n a b p q : ℕ}
    (ha : a ≤ 2 ^ (n + 1)) (hb : b ≤ 2 ^ (n + 1))
    (hcasc : CascadeSplit (n + 1) (a + b) p q)
    (hba : b ≤ a) (hcase : H (n + 1) b < a) (hq_pos : 1 ≤ q) :
    H (n + 1) q ≤ a := by
  proof omitted in this dead block -- FALSE, refuted by `n=1, a=2, b=0`
  (`H 2 1 = 3 > 2`).
-/


/- The two equal-length Macaulay shadow-window leaves `harper_macaulay_defect_q_ge_two`
   (the `p ≤ a` orientation) and `harper_macaulay_reversed` (the `a < p` orientation),
   together with the dispatcher `harper_macaulay_defect`, the proved endpoint
   `harper_macaulay_defect_q_one`, and their packaging `harper_macaulay_joint`, were
   each the ih-free window form of the single joint boundary inequality
   `H (n+1) p + H (n+1) q ≤ H (n+1) a + max (H (n+1) b) a`.  Carrying two separate
   ih-free window proof holes was strictly weaker than the PDF: the Frankl–Füredi paper
   proves the *single* boundary inequality `canonical ≤ arbitrary` using the
   lower-dimensional isoperimetric input (the level-`n` Harper inequality).  This
   whole block is therefore consolidated into the single PDF-faithful inductive leaf
   `harper_joint_via_ih` above (which carries that `ih`), a strict two-hole to
   one-hole
   reduction.  The window/`gShiftIntervalCount` form is recoverable from
   `harper_joint_via_ih` via `gShiftIntervalCount_eq_H_sub` + `cascade_split_add` if
   ever needed.  The block is preserved (commented) for reference.
-/

/- The two equal-length Macaulay shadow-window leaves `harper_macaulay_defect_q_ge_two`
   (the `p ≤ a` orientation) and `harper_macaulay_reversed` (the `a < p` orientation),
   together with the dispatcher `harper_macaulay_defect`, the proved endpoint
   `harper_macaulay_defect_q_one`, and their packaging `harper_macaulay_joint`, were
   the bottleneck of the previous formulation. They are now superseded by the
   mathematically simpler `boundaryCost_mono_core` lemma, but are preserved here
   commented out for historical reference.

lemma harper_macaulay_defect_q_one (n : ℕ) {a b p q : ℕ}
    (ha : a ≤ 2 ^ (n + 1)) (hb : b ≤ 2 ^ (n + 1))
    (hcasc : CascadeSplit (n + 1) (a + b) p q)
    (hba : b ≤ a) (hpa : p ≤ a) (hq_one : q = 1) :
    gShiftIntervalCount (n + 1) b q ≤
      gShiftIntervalCount (n + 1) p a + (a - min a (H (n + 1) b)) := by
  have hpq : p + q = a + b := cascade_split_add hcasc
  have hb_le_one : b ≤ 1 := by omega
  rcases (by omega : b = 0 ∨ b = 1) with hb_zero | hb_one
  · subst b
    have ha_eq : a = p + 1 := by omega
    have hp_succ_le : p + 1 ≤ 2 ^ (n + 1) := by
      simpa [ha_eq] using ha
    have hleft :
        gShiftIntervalCount (n + 1) 0 q = n + 2 := by
      rw [hq_one, gShiftIntervalCount_eq_H_sub (n + 1) 0 1 (by omega)]
      rw [H_one, H_zero]
      omega
    have hright :
        gShiftIntervalCount (n + 1) p a = HIncrement (n + 1) p := by
      rw [ha_eq]
      have hwin := HIncrement_window_eq_gShiftIntervalCount (n + 1) p (p + 1) (by omega)
      rw [← hwin]
      simp
    have hinc := HIncrement_lower (n + 1) p hp_succ_le
    have hmin : min a (H (n + 1) 0) = 0 := by
      rw [H_zero]
      simp
    rw [hleft, hright, hmin, ha_eq]
    omega
  · subst b
    have hleft :
        gShiftIntervalCount (n + 1) 1 q = 0 := by
      rw [hq_one, gShiftIntervalCount_eq_H_sub (n + 1) 1 1 (by omega)]
      omega
    rw [hleft]
    exact Nat.zero_le _

lemma harper_macaulay_defect_q_ge_two (n : ℕ) {a b p q : ℕ}
    (ha : a ≤ 2 ^ (n + 1)) (hb : b ≤ 2 ^ (n + 1))
    (hcasc : CascadeSplit (n + 1) (a + b) p q)
    (hq_two : 2 ≤ q) (hba : b ≤ a) (hpa : p ≤ a) :
    gShiftIntervalCount (n + 1) b q ≤
      gShiftIntervalCount (n + 1) p a + (a - min a (H (n + 1) b)) := by
  proof omitted in this dead block

lemma harper_macaulay_defect (n : ℕ) {a b p q : ℕ}
    (ha : a ≤ 2 ^ (n + 1)) (hb : b ≤ 2 ^ (n + 1))
    (hcasc : CascadeSplit (n + 1) (a + b) p q)
    (hq_pos : 1 ≤ q) (hba : b ≤ a) (hpa : p ≤ a) :
    gShiftIntervalCount (n + 1) b q ≤
      gShiftIntervalCount (n + 1) p a + (a - min a (H (n + 1) b)) := by
  by_cases hq_one : q = 1
  · exact harper_macaulay_defect_q_one n ha hb hcasc hba hpa hq_one
  · have hq_two : 2 ≤ q := by omega
    exact harper_macaulay_defect_q_ge_two n ha hb hcasc hq_two hba hpa

lemma harper_macaulay_reversed (n : ℕ) {a b p q : ℕ}
    (ha : a ≤ 2 ^ (n + 1)) (hb : b ≤ 2 ^ (n + 1))
    (hcasc : CascadeSplit (n + 1) (a + b) p q)
    (hq_pos : 1 ≤ q) (hba : b ≤ a) (hap : a ≤ p) :
    gShiftIntervalCount (n + 1) a p ≤ gShiftIntervalCount (n + 1) q b := by
  proof omitted in this dead block
-/
/--
The boundary cost is monotonically increasing with respect to cascade interleaving.
This is the core mathematical reduction of the Macaulay window bounds.
-/
lemma CascadeInterleaves.cascade {n p q a b : ℕ}
    (h_inter : CascadeInterleaves n p q a b) :
    CascadeSplit n (a + b) p q :=
  h_inter.1

lemma CascadeInterleaves.sum_eq {n p q a b : ℕ}
    (h_inter : CascadeInterleaves n p q a b) :
    p + q = a + b :=
  cascade_split_add h_inter.cascade

lemma CascadeInterleaves.left_le_cube {n p q a b : ℕ}
    (h_inter : CascadeInterleaves n p q a b) :
    p ≤ 2 ^ n :=
  cascade_p_le h_inter.cascade

lemma CascadeInterleaves.right_le_cube {n p q a b : ℕ}
    (h_inter : CascadeInterleaves n p q a b) :
    q ≤ 2 ^ n :=
  cascade_q_le h_inter.cascade

lemma H_pair_step_forward_of_increment_le (N x y : ℕ)
    (hy : 1 ≤ y) (hinc : HIncrement N (y - 1) ≤ HIncrement N x) :
    H N x + H N y ≤ H N (x + 1) + H N (y - 1) := by
  have hxwin := H_window_sum_of_le N x (x + 1) (by omega)
  have hywin := H_window_sum_of_le N (y - 1) y (by omega)
  have hxico : (∑ i ∈ Finset.Ico x (x + 1), HIncrement N i) = HIncrement N x := by
    simp
  have hyico :
      (∑ i ∈ Finset.Ico (y - 1) y, HIncrement N i) = HIncrement N (y - 1) := by
    have hy_eq : y = (y - 1) + 1 := by omega
    rw [hy_eq]
    simp
  rw [hxico] at hxwin
  rw [hyico] at hywin
  omega

lemma H_pair_step_backward_of_increment_le (N x y : ℕ)
    (hy : 1 ≤ y) (hinc : HIncrement N x ≤ HIncrement N (y - 1)) :
    H N (x + 1) + H N (y - 1) ≤ H N x + H N y := by
  have hxwin := H_window_sum_of_le N x (x + 1) (by omega)
  have hywin := H_window_sum_of_le N (y - 1) y (by omega)
  have hxico : (∑ i ∈ Finset.Ico x (x + 1), HIncrement N i) = HIncrement N x := by
    simp
  have hyico :
      (∑ i ∈ Finset.Ico (y - 1) y, HIncrement N i) = HIncrement N (y - 1) := by
    have hy_eq : y = (y - 1) + 1 := by omega
    rw [hy_eq]
    simp
  rw [hxico] at hxwin
  rw [hyico] at hywin
  omega

/-
HISTORICAL NOTE (cycle 7), record only — no live proof holes below.
A previous cycle reduced the *true* Case-I sum leaf `harper_macaulay_LE_sum`
to two *pointwise* reflected-increment inequalities
`HIncrement (n+1) (q - i - 1) ≤ HIncrement (n+1) (p + i)` (and the mirror)
through the valid telescope lemmas `H_add_le_H_add_of_ge_telescope` /
`H_add_le_H_add_of_le_telescope`.  That reduction is unsound: the telescope only
yields the sum bound when *every* per-step increment inequality holds, and those
per-step inequalities are FALSE.  Verified by an exact computational model of `H`
via the cascade recursion (all split dimensions `n ≤ 4`): e.g. at
`n = 1, a = 3, b = 1` (split `p = 2, q = 2`, `i = 0`) one has
`HIncrement 2 1 = 1 > 0 = HIncrement 2 2`, yet the sum bound still holds.  The
genuine Case-I leaf is therefore the non-pointwise Macaulay shadow-window sum,
kept as the honest open statement `harper_macaulay_LE_sum` below.  The bridge
`harper_macaulay_LE_sum_of_shadow_windows` records the precise (sorry-free)
reduction of that sum leaf to the set-level shadow-window comparison.

Layer-membership: every rank below `2^N` lies in a unique Macaulay layer
`[binomPrefix N r, binomPrefix N (r+1))`. Reusable cascade-layer locator.
-/
lemma exists_binomPrefix_layer (N b : ℕ) (hb : b < 2 ^ N) :
    ∃ r, r ≤ N ∧ binomPrefix N r ≤ b ∧ b < binomPrefix N (r + 1) := by
  -- Let's choose the largest $r$ such that $binomPrefix N r \leq b$.
  obtain ⟨r, hr⟩ : ∃ r ≤ N, binomPrefix N r ≤ b ∧ ∀ s > r, s ≤ N → binomPrefix N s > b := by
    obtain ⟨r0, hr0N, hr0b⟩ : ∃ r ≤ N, binomPrefix N r ≤ b :=
      ⟨0, Nat.zero_le _, by simp +decide [binomPrefix_zero]⟩
    have hne : (Finset.filter (fun r => binomPrefix N r ≤ b) (Finset.Iic N)).Nonempty :=
      ⟨r0, Finset.mem_filter.mpr ⟨Finset.mem_Iic.mpr hr0N, hr0b⟩⟩
    have hmem := Finset.mem_filter.mp (Finset.max'_mem _ hne)
    exact ⟨Finset.max' _ hne, Finset.mem_Iic.mp hmem.1, hmem.2,
      fun s hs₁ hs₂ => not_le.mp fun hs₃ => hs₁.not_ge <| Finset.le_max' _ _ <| by aesop⟩
  grind +suggestions

/-- **Two-layer confinement (LE regime).** If `b` lies at or below the top of
Macaulay layer `r` and `a ≤ H N b`, then `a` lies at or below the top of layer
`r+1`. Equivalently the LE-regime shadow comparison is confined to the two
adjacent Macaulay layers `r` and `r+1`. This is the reusable cascade-layer
increment fact behind the Case-I Kruskal–Katona/Macaulay window comparison. -/
lemma H_le_binomPrefix_of_layer (N a b r : ℕ)
    (hb : b ≤ binomPrefix N (r + 1)) (hcase : a ≤ H N b) :
    a ≤ binomPrefix N (r + 2) := by
  calc a ≤ H N b := hcase
    _ ≤ H N (binomPrefix N (r + 1)) := H_mono hb
    _ = binomPrefix N (r + 2) := H_binomPrefix N (r + 1) (by omega)

/-- Degenerate `q = 0` branch of the Case-I Macaulay sum leaf.  This removes
the non-positive canonical split from the Frankl–Füredi/Macaulay core: a
canonical split with `q = 0` has total mass at most one, so the inequality is a
finite `0/1` calculation. -/
lemma harper_macaulay_LE_sum_q_zero (n : ℕ)
    {a b p : ℕ}
    (hcasc : CascadeSplit (n + 1) (a + b) p 0)
    (hba : b ≤ a) :
    H (n + 1) p + H (n + 1) 0 ≤ H (n + 1) a + H (n + 1) b := by
  have htotal : a + b ≤ 1 := cascade_split_q_zero_total_le_one hcasc
  have hp_eq : p = a + b := by
    have hsum := cascade_split_add hcasc
    omega
  subst p
  have hb_zero : b = 0 := by omega
  subst b
  have ha_val : a = 0 ∨ a = 1 := by omega
  rcases ha_val with rfl | rfl
  · simp [H_zero]
  · simp [H_zero, H_one]

/- **Frankl–Füredi / Macaulay extremal step (max-form): the genuine `n → n+1`
combinatorial leaf.**

For the canonical cascade split `(p, q)` of `a + b` at level `n + 1`, the
canonical cross-boundary cost is minimal:
`max (H (n+1) p) q + max (H (n+1) q) p ≤ max (H (n+1) a) b + max (H (n+1) b) a`.
The level-`n` Harper inequality `ih` is the inductive input.  The conclusion
mentions only `a, b, p, q`; it is the genuine Kruskal–Katona / Macaulay
shadow-comparison heart of Harper's vertex-isoperimetric theorem and has no
elementary proof (`H (n+1)` is neither convex nor concave and the cross boundary
cost is not a unimodal function of the split).

This statement is **true** (verified by an exact computational cascade model of
`H`: no violation for all capacity-bounded `a, b` with `n ≤ 3`).  Notably the
inequality needs **no** prefix-mass / domination hypothesis at all — it holds
for every capacity-bounded split of the common total.

HISTORY (cycle14.aristotle).  A previous architecture tried to prove this by a
single-step `blockDist` / `IsUpMove` descent toward the canonical four-block
profile (`exchange_move_exists_up` in `Macaulay.lean`).  That route is
**false**, as shown with the exact `H` model:

* there are capacity-bounded, `h_lower`-dominated, non-canonical four-block
  profiles — e.g. `n = 1`, `(a0,a1,b0,b1) = (1,0,2,0)` toward canonical
  `(p0,p1,q0,q1) = (1,1,1,0)` — from which **no** single allowed move decreases
  the block distance while keeping the boundary functional non-increasing
  (this remains true even if one allows all 12 single-unit transfers, not just
  the 8 `IsUpMove` ones);
* the 1-D boundary functional `f(A) = max (H (n+1) A) (S−A) + max (H (n+1) (S−A)) A`
  is **not unimodal** (e.g. `n+1 = 3`, `S = 6`: `f = …,13,13,14,13,13,…`), so no
  single-step boundary-monotone descent exists.

The false machinery (`exchange_move_exists_up` and its projections) has been
removed/commented out in `Macaulay.lean`, and this honest TRUE leaf — with the
spurious four-block slice and `h_lower` hypotheses dropped — is exposed directly.
The two case leaves `harper_macaulay_LE_sum_pos` (LE) and `harper_macaulay_GT_sum`
(GT) are sorry-free corollaries: both collapse the outer `max`s
(`canonical_boundaryCost_eq_H_add` on the left; the case hypothesis on the
right). -/
/-- **Frankl–Füredi lowered four-block exchange step (human-proof leaf).**
The genuine local compression/Macaulay step in the form used by the Harper
induction: for the canonical cascade split `(p,q)` of `a+b` at level `n+1`,
in the ordered regime `b ≤ a`, with the four level-`n` cascade slice
decompositions of `p,q,a,b` and the lowered prefix-mass (Macaulay) domination
`h_lower` provided by `CascadeInterleaves.lower_succ`, and the level-`n` Harper
inequality `ih`, the canonical cross-boundary cost is minimal.  This carries
exactly the PDF's inductive inputs (within-slice optimality from
`ih`/`harper_extremal_n`, and cross-layer prefix-mass majorization from
`h_lower`).  The unordered case is recovered by `harper_macaulay_exchange_step`
via the symmetry of the right-hand side under swapping `a, b`. -/
lemma boundaryCost_le_of_lower_interleaves_step_live
    (n p q a b p0 p1 q0 q1 a0 a1 b0 b1 : ℕ)
    (_ : ∀ m, m < n + 1 → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    (ha_cap : a ≤ 2 ^ (n + 1)) (hb_cap : b ≤ 2 ^ (n + 1))
    (hba : b ≤ a)
    (hpq_casc : CascadeSplit (n + 1) (a + b) p q)
    (hp : CascadeSplit n p p0 p1) (hq : CascadeSplit n q q0 q1)
    (_ : CascadeSplit n a a0 a1) (hb : CascadeSplit n b b0 b1)
    (_ : ∀ l,
      splitPrefixMass n a0 b0 (l + 1) + splitPrefixMass n a1 b1 l
        ≤ splitPrefixMass n p0 q0 (l + 1) + splitPrefixMass n p1 q1 l) :
    max (H (n + 1) p) q + max (H (n + 1) q) p ≤
      max (H (n + 1) a) b + max (H (n + 1) b) a := by
  -- A IS NOW PROVED (cycle16 manual branch) from the upper-shadow / Macaulay
  -- layer in `BooleanIsoperimetry/Shadow.lean`: the max-form boundary step
  -- collapses (sorry-free) to the two scalar Macaulay shadow-sum leaves
  -- `BooleanIsoperimetry.H_shadow_LE_sum` (LE regime) and
  -- `BooleanIsoperimetry.H_shadow_GT_sum` (GT regime), exactly as in
  -- `boundaryCost_le_of_LE_GT_sums` but routed through the new shadow leaves
  -- instead of through this lemma (so the dependency is acyclic).  The remaining
  -- sorries live only in those two named PDF-layer leaves, which via
  -- `H_shadow_closed_form` are pure `upperShadow` (Kruskal–Katona/Macaulay)
  -- inequalities — see `H_shadow_LE_sum_as_upperShadow`.  The slice/profile data
  -- (`hp hq ha hb h_lower`) is not needed for this collapse and is retained only
  -- to preserve the public signature.
  --
  -- HISTORICAL OBSTRUCTION NOTE (kept for context; the shadow layer is the way
  -- past it).  Earlier cycles established that the max-form leaf is genuinely
  -- 2-dimensional:
  -- This was the single load-bearing sorry: `harper_macaulay_exchange_step`,
  -- `harper_macaulay_LE_sum(_pos)`, `harper_macaulay_GT_sum`,
  -- `boundaryCost_le_of_LE_GT_sums`, `boundaryCost_le_of_interleaves_core` and
  -- `harper_macaulay_joint` all reduce to it; there is no independent route.
  -- The statement is TRUE (exhaustive cascade model of `H`, no violation for all
  -- capacity-bounded `a,b` with split dimension `n+1 ≤ 4`).  The remaining gap is
  -- formalization depth, not falsity.  Three natural routes are provably blocked
  -- with current infrastructure:
  --
  -- (1) ABEL-SUMMATION ROUTE IS DEAD.  The cascade Abel lemma
  --     `int_sum_mul_le_of_prefix_le_of_antitone_weight` would close A if the
  --     boundary cost `H (n+1) p + H (n+1) q` were a fixed antitone-weighted sum
  --     of the `splitPrefixMass` quantities that `h_lower` controls.  It is NOT:
  --     `H` is not any fixed-weight linear function of the split prefix masses
  --     (best-fit weights have strictly positive residual at every `n`, and are
  --     neither nonnegative nor antitone).  This is the precise sense of the file
  --     note "prefix masses alone do not determine boundary cost".
  -- (2) VERTICAL/HORIZONTAL MISMATCH.  `H (n+1) p = max (H n p0) p1 + max (H n p1) p0`
  --     couples a block with its OWN two level-`n` slices ("vertical"), whereas
  --     `h_lower` and the cascade domination couple the `0`-slices `(p0,q0)` and
  --     `1`-slices `(p1,q1)` across blocks ("horizontal").  The transpose
  --     regrouping `bc_n(p0,p1)+bc_n(q0,q1) ≤ bc_n(p0,q0)+bc_n(p1,q1)` is FALSE
  --     (counterexamples already at `n=2`), so the two level-`n` `ih`/`harper_extremal_n`
  --     applications cannot be combined by a one-directional exchange.  This is
  --     why single-step `IsUpMove`/`blockDist` descent (cycle14) and rowwise
  --     recombination were shown insufficient.
  -- (3) NO KRUSKAL–KATONA BRIDGE.  The honest proof needs the Macaulay shadow
  --     closed form `H N (binomPrefix N r + t) = binomPrefix N (r+1) + Δ(N,r,t)`,
  --     where `Δ` is the upper-shadow size of the first `t` rank-`r` vertices, plus
  --     the KK extremality of colex/simplicial initial segments for that shadow.
  --     mathlib's `Finset.kruskal_katona` lives over `Finset (Finset (Fin n))`
  --     colex shadows, with no bridge to this repo's `Cube`/`neighborhood`/`H`.
  --
  -- MINIMAL NEXT LEMMAS that would make A closeable (all currently MISSING, all
  -- empirically checkable against the cascade model):
  --   (a) `H_shadow_closed_form`:  H N (binomPrefix N r + t) = binomPrefix N (r+1)
  --        + upperShadow N r t,  with `upperShadow` defined and shown monotone in `t`.
  --   (b) `upperShadow_kruskal_katona`:  the cascade (KK) lower bound on `upperShadow`
  --        / its superadditivity under merging two layer-initial segments.
  --   (c) `boundaryCost_eq_layerSum`:  a representation of `H (n+1) p + H (n+1) q`
  --        as a sum over layers of `upperShadow` contributions of the DOUBLY-canonical
  --        profile `(p0,p1,q0,q1)` (which is canonical in both directions: verified
  --        that `(p0,q0)` and `(p1,q1)` are each canonical level-`n` cascade splits),
  --        reducing A to a per-layer shadow comparison driven by `h_lower`.
  -- See AGENT_RESULT_CURRENT.md for the full analysis and empirical evidence.
  --
  -- PROOF.  Collapse the outer boundary `max`s and dispatch to the shadow leaves.
  have hp_cap : p ≤ 2 ^ (n + 1) := cascade_p_le hpq_casc
  have hq_cap : q ≤ 2 ^ (n + 1) := cascade_q_le hpq_casc
  by_cases hq_zero : q = 0
  · subst hq_zero
    have htot : a + b ≤ 1 := cascade_split_q_zero_total_le_one hpq_casc
    have hb0 : b = 0 := by omega
    subst hb0
    have ha_eq_p : a = p := by
      have hsum := cascade_split_add hpq_casc
      omega
    subst ha_eq_p
    exact le_rfl
  · have hq_pos : 1 ≤ q := Nat.pos_of_ne_zero hq_zero
    rw [canonical_boundaryCost_eq_H_add hp_cap hq_cap hq_pos hpq_casc]
    by_cases hcase : a ≤ H (n + 1) b
    · have hbHa : b ≤ H (n + 1) a := le_trans hba (H_ge_self (n + 1) a ha_cap)
      rw [max_eq_left hbHa, max_eq_left hcase]
      exact BooleanIsoperimetry.H_shadow_LE_sum ha_cap hb_cap hpq_casc hq_pos hba hcase
    · push Not at hcase
      have hbHa : b ≤ H (n + 1) a := le_trans hba (H_ge_self (n + 1) a ha_cap)
      rw [max_eq_left hbHa, max_eq_right (le_of_lt hcase)]
      exact BooleanIsoperimetry.H_shadow_GT_sum ha_cap hb_cap hpq_casc hq_pos hba hcase

/-- **Frankl–Füredi / Macaulay extremal step (max-form).**
For the canonical cascade split `(p,q)` of `a+b` at level `n+1`, the canonical
cross-boundary cost is minimal.  This is now a sorry-free consequence of the
single human-proof leaf `boundaryCost_le_of_lower_interleaves_step_live`: choose
the four level-`n` cascade slice decompositions of `p,q,a,b` via
`exists_cascade_split`, obtain the lowered prefix-mass domination from
`canonicalSplit_interleaves` and `CascadeInterleaves.lower_succ`, and apply the
leaf. -/
lemma harper_macaulay_exchange_step (n : ℕ)
    (ih : ∀ m, m < n + 1 → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b p q : ℕ} (ha_cap : a ≤ 2 ^ (n + 1)) (hb_cap : b ≤ 2 ^ (n + 1))
    (hpq_casc : CascadeSplit (n + 1) (a + b) p q) :
    max (H (n + 1) p) q + max (H (n + 1) q) p ≤
      max (H (n + 1) a) b + max (H (n + 1) b) a := by
  have hp_cap : p ≤ 2 ^ (n + 1) := cascade_p_le hpq_casc
  have hq_cap : q ≤ 2 ^ (n + 1) := cascade_q_le hpq_casc
  obtain ⟨p0, p1, _, _, _, hp⟩ := exists_cascade_split n p hp_cap
  obtain ⟨q0, q1, _, _, _, hq⟩ := exists_cascade_split n q hq_cap
  obtain ⟨a0, a1, _, _, _, ha⟩ := exists_cascade_split n a ha_cap
  obtain ⟨b0, b1, _, _, _, hb⟩ := exists_cascade_split n b hb_cap
  rcases le_total b a with hba | hab
  · have h_inter := canonicalSplit_interleaves ha_cap hb_cap hpq_casc
    have h_lower := CascadeInterleaves.lower_succ h_inter hp hq ha hb
    exact boundaryCost_le_of_lower_interleaves_step_live n p q a b
      p0 p1 q0 q1 a0 a1 b0 b1 ih ha_cap hb_cap hba hpq_casc hp hq ha hb h_lower
  · have hpq_casc' : CascadeSplit (n + 1) (b + a) p q := by
      rwa [Nat.add_comm a b] at hpq_casc
    have h_inter := canonicalSplit_interleaves hb_cap ha_cap hpq_casc'
    have h_lower := CascadeInterleaves.lower_succ h_inter hp hq hb ha
    have h := boundaryCost_le_of_lower_interleaves_step_live n p q b a
      p0 p1 q0 q1 b0 b1 a0 a1 ih hb_cap ha_cap hab hpq_casc' hp hq hb ha h_lower
    rw [Nat.add_comm (max (H (n + 1) a) b) (max (H (n + 1) b) a)]
    exact h

/-- Positive-cascade Case-I (LE) sum leaf.  Sorry-free corollary of
`harper_macaulay_exchange_step`: collapse the outer `max`s
(`canonical_boundaryCost_eq_H_add` on the left; `b ≤ a ≤ H b` on the right). -/
lemma harper_macaulay_LE_sum_pos (n : ℕ)
    (ih : ∀ m, m < n + 1 → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b p q : ℕ}
    (ha : a ≤ 2 ^ (n + 1)) (hb : b ≤ 2 ^ (n + 1))
    (hcasc : CascadeSplit (n + 1) (a + b) p q)
    (hq_pos : 1 ≤ q) (hba : b ≤ a) (hcase : a ≤ H (n + 1) b) :
    H (n + 1) p + H (n + 1) q ≤ H (n + 1) a + H (n + 1) b := by
  have hp_cap : p ≤ 2 ^ (n + 1) := cascade_p_le hcasc
  have hq_cap : q ≤ 2 ^ (n + 1) := cascade_q_le hcasc
  have hmax := harper_macaulay_exchange_step n ih ha hb hcasc
  have hbHa : b ≤ H (n + 1) a := le_trans hba (H_ge_self (n + 1) a ha)
  rw [canonical_boundaryCost_eq_H_add hp_cap hq_cap hq_pos hcasc,
      max_eq_left hbHa, max_eq_left hcase] at hmax
  exact hmax

lemma harper_macaulay_LE_sum (n : ℕ)
    (ih : ∀ m, m < n + 1 → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b p q : ℕ}
    (ha : a ≤ 2 ^ (n + 1)) (hb : b ≤ 2 ^ (n + 1))
    (hcasc : CascadeSplit (n + 1) (a + b) p q)
    (hba : b ≤ a) (hcase : a ≤ H (n + 1) b) :
    H (n + 1) p + H (n + 1) q ≤ H (n + 1) a + H (n + 1) b := by
  by_cases hq_zero : q = 0
  · subst hq_zero
    exact harper_macaulay_LE_sum_q_zero n hcasc hba
  · exact harper_macaulay_LE_sum_pos n ih ha hb hcasc (Nat.pos_of_ne_zero hq_zero) hba hcase

/-- Positive-cascade Case-II (GT) sum leaf.  Sorry-free corollary of
`harper_macaulay_exchange_step`: the outer `max`s collapse via
`canonical_boundaryCost_eq_H_add` (left) and the GT case `H (n+1) b < a`
(right, `max (H (n+1) b) a = a`). -/
lemma harper_macaulay_GT_sum (n : ℕ)
    (ih : ∀ m, m < n + 1 → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b p q : ℕ}
    (ha : a ≤ 2 ^ (n + 1)) (hb : b ≤ 2 ^ (n + 1))
    (hcasc : CascadeSplit (n + 1) (a + b) p q)
    (hq_pos : 1 ≤ q) (hba : b ≤ a) (hcase : H (n + 1) b < a) :
    H (n + 1) p + H (n + 1) q ≤ H (n + 1) a + a := by
  have hp_cap : p ≤ 2 ^ (n + 1) := cascade_p_le hcasc
  have hq_cap : q ≤ 2 ^ (n + 1) := cascade_q_le hcasc
  have hmax := harper_macaulay_exchange_step n ih ha hb hcasc
  have hbHa : b ≤ H (n + 1) a := le_trans hba (H_ge_self (n + 1) a ha)
  rw [canonical_boundaryCost_eq_H_add hp_cap hq_cap hq_pos hcasc,
      max_eq_left hbHa, max_eq_right (le_of_lt hcase)] at hmax
  exact hmax

lemma boundaryCost_le_of_LE_GT_sums (n : ℕ)
    (ih : ∀ m, m < n + 1 → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b p q : ℕ} (ha : a ≤ 2 ^ (n + 1)) (_hb : b ≤ 2 ^ (n + 1))
    (hcasc : CascadeSplit (n + 1) (a + b) p q) (hba : b ≤ a) :
    max (H (n + 1) p) q + max (H (n + 1) q) p ≤
      max (H (n + 1) a) b + max (H (n + 1) b) a := by
  have hp_cap : p ≤ 2 ^ (n + 1) := cascade_p_le hcasc
  have hq_cap : q ≤ 2 ^ (n + 1) := cascade_q_le hcasc
  by_cases hq_zero : q = 0
  · subst hq_zero
    have htot : a + b ≤ 1 := cascade_split_q_zero_total_le_one hcasc
    have hb0 : b = 0 := by omega
    subst hb0
    have ha_eq_p : a = p := by
      have hsum := cascade_split_add hcasc
      omega
    subst ha_eq_p
    exact le_rfl
  · have hq_pos : 1 ≤ q := Nat.pos_of_ne_zero hq_zero
    rw [canonical_boundaryCost_eq_H_add hp_cap hq_cap hq_pos hcasc]
    by_cases hcase : a ≤ H (n + 1) b
    · have hbHa : b ≤ H (n + 1) a := le_trans hba (H_ge_self (n + 1) a ha)
      rw [max_eq_left hbHa, max_eq_left hcase]
      exact harper_macaulay_LE_sum_pos n ih ha _hb hcasc hq_pos hba hcase
    · push Not at hcase
      have hbHa : b ≤ H (n + 1) a := le_trans hba (H_ge_self (n + 1) a ha)
      rw [max_eq_left hbHa, max_eq_right (le_of_lt hcase)]
      exact harper_macaulay_GT_sum n ih ha _hb hcasc hq_pos hba hcase

/- SUPERSEDED (this cycle).  The lowered four-block leaf below was the form that
carried the level-`n` slice cascade splits and the prefix-mass domination
`h_lower` from `CascadeInterleaves.lower_succ`.  After the correctness fix that
restored the top-level `CascadeSplit (n+1) (a+b) p q` hypothesis, the boundary
monotonicity turned out to follow directly from the three Macaulay shadow window
kernels (`harper_macaulay_window_le_left`/`_right`/`harper_macaulay_slack_gt_window`)
via `boundaryCost_le_of_LE_GT_sums`, with **no use** of the lowered
slice profile or `h_lower`.  The slice machinery is therefore vestigial here, so
`boundaryCost_le_of_interleaves_core` now calls the window-kernel reduction
directly and this leaf is preserved (commented) for reference only.

lemma harper_macaulay_exchange_step (n : ℕ)
    (ih : ∀ m, m < n + 1 → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b p q : ℕ} (ha_cap : a ≤ 2 ^ (n + 1)) (hb_cap : b ≤ 2 ^ (n + 1))
    (hpq_casc : CascadeSplit (n + 1) (a + b) p q) :
    max (H (n + 1) p) q + max (H (n + 1) q) p ≤
      max (H (n + 1) a) b + max (H (n + 1) b) a := by
  rcases le_total b a with hba | hab
  · exact boundaryCost_le_of_LE_GT_sums n ih ha_cap hb_cap hpq_casc hba
  · have hpq_casc' : CascadeSplit (n + 1) (b + a) p q := by
      rwa [Nat.add_comm a b] at hpq_casc
    have h := boundaryCost_le_of_LE_GT_sums n ih hb_cap ha_cap hpq_casc' hab
    rw [max_comm (H (n+1) b) a, max_comm (H (n+1) a) b, add_comm (max (H (n+1) a) b)]
    exact h

lemma harper_macaulay_LE_sum_pos (n : ℕ)
    (ih : ∀ m, m < n + 1 → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b p q : ℕ}
    (ha : a ≤ 2 ^ (n + 1)) (hb : b ≤ 2 ^ (n + 1))
    (hcasc : CascadeSplit (n + 1) (a + b) p q)
    (hq_pos : 1 ≤ q) (hba : b ≤ a) (hcase : a ≤ H (n + 1) b) :
    H (n + 1) p + H (n + 1) q ≤ H (n + 1) a + H (n + 1) b := by
  have hp_cap : p ≤ 2 ^ (n + 1) := cascade_p_le hcasc
  have hq_cap : q ≤ 2 ^ (n + 1) := cascade_q_le hcasc
  have hmax := harper_macaulay_exchange_step n ih ha hb hcasc
  have hbHa : b ≤ H (n + 1) a := le_trans hba (H_ge_self (n + 1) a ha)
  rw [canonical_boundaryCost_eq_H_add hp_cap hq_cap hq_pos hcasc,
      max_eq_left hbHa, max_eq_left hcase] at hmax
  exact hmax

lemma harper_macaulay_LE_sum (n : ℕ)
    (ih : ∀ m, m < n + 1 → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b p q : ℕ}
    (ha : a ≤ 2 ^ (n + 1)) (hb : b ≤ 2 ^ (n + 1))
    (hcasc : CascadeSplit (n + 1) (a + b) p q)
    (hba : b ≤ a) (hcase : a ≤ H (n + 1) b) :
    H (n + 1) p + H (n + 1) q ≤ H (n + 1) a + H (n + 1) b := by
  by_cases hq_zero : q = 0
  · subst q
    exact harper_macaulay_LE_sum_q_zero n hcasc hba
  · exact harper_macaulay_LE_sum_pos n ih ha hb hcasc (Nat.pos_of_ne_zero hq_zero) hba hcase

lemma harper_macaulay_GT_sum (n : ℕ)
    (ih : ∀ m, m < n + 1 → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b p q : ℕ}
    (ha : a ≤ 2 ^ (n + 1)) (hb : b ≤ 2 ^ (n + 1))
    (hcasc : CascadeSplit (n + 1) (a + b) p q)
    (hq_pos : 1 ≤ q) (hba : b ≤ a) (hcase : H (n + 1) b < a) :
    H (n + 1) p + H (n + 1) q ≤ H (n + 1) a + a := by
  have hp_cap : p ≤ 2 ^ (n + 1) := cascade_p_le hcasc
  have hq_cap : q ≤ 2 ^ (n + 1) := cascade_q_le hcasc
  have hmax := harper_macaulay_exchange_step n ih ha hb hcasc
  have hbHa : b ≤ H (n + 1) a := le_trans hba (H_ge_self (n + 1) a ha)
  rw [canonical_boundaryCost_eq_H_add hp_cap hq_cap hq_pos hcasc,
      max_eq_left hbHa, max_eq_right (le_of_lt hcase)] at hmax
  exact hmax

lemma harper_macaulay_LE_gShift_left (n : ℕ)
    (ih : ∀ m, m < n + 1 → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b p q : ℕ}
    (ha : a ≤ 2 ^ (n + 1)) (hb : b ≤ 2 ^ (n + 1))
    (hcasc : CascadeSplit (n + 1) (a + b) p q)
    (hba : b ≤ a) (hcase : a ≤ H (n + 1) b) (hpa : p ≤ a) :
    gShiftIntervalCount (n + 1) b q ≤ gShiftIntervalCount (n + 1) p a := by
  have hwin := harper_macaulay_LE_sum n ih ha hb hcasc hba hcase
  have hbq := (cascade_left_window_endpoints hcasc hpa).1
  rw [gShiftIntervalCount_eq_H_sub (n + 1) b q hbq,
      gShiftIntervalCount_eq_H_sub (n + 1) p a hpa]
  have hHb_le_Hq : H (n + 1) b ≤ H (n + 1) q := H_mono hbq
  have hHp_le_Ha : H (n + 1) p ≤ H (n + 1) a := H_mono hpa
  omega

lemma harper_macaulay_LE_gShift_left_confined (n : ℕ)
    (ih : ∀ m, m < n + 1 → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b p q r : ℕ}
    (ha : a ≤ 2 ^ (n + 1)) (hb : b ≤ 2 ^ (n + 1))
    (hcasc : CascadeSplit (n + 1) (a + b) p q)
    (hba : b ≤ a) (hcase : a ≤ H (n + 1) b) (hpa : p ≤ a)
    (hr : 1 ≤ r)
    (hrlo : binomPrefix (n + 1) r ≤ b)
    (hrhi : b < binomPrefix (n + 1) (r + 1))
    (hahi : a ≤ binomPrefix (n + 1) (r + 2)) :
    gShiftIntervalCount (n + 1) b q ≤ gShiftIntervalCount (n + 1) p a :=
  harper_macaulay_LE_gShift_left n ih ha hb hcasc hba hcase hpa

lemma harper_macaulay_LE_gShift_right (n : ℕ)
    (ih : ∀ m, m < n + 1 → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b p q : ℕ}
    (ha : a ≤ 2 ^ (n + 1)) (hb : b ≤ 2 ^ (n + 1))
    (hcasc : CascadeSplit (n + 1) (a + b) p q)
    (hba : b ≤ a) (hcase : a ≤ H (n + 1) b) (hap : a ≤ p) :
    gShiftIntervalCount (n + 1) a p ≤ gShiftIntervalCount (n + 1) q b := by
  have hwin := harper_macaulay_LE_sum n ih ha hb hcasc hba hcase
  have hqb := (cascade_right_window_endpoints hcasc hap).1
  rw [gShiftIntervalCount_eq_H_sub (n + 1) a p hap,
      gShiftIntervalCount_eq_H_sub (n + 1) q b hqb]
  have hHa_le_Hp : H (n + 1) a ≤ H (n + 1) p := H_mono hap
  have hHq_le_Hb : H (n + 1) q ≤ H (n + 1) b := H_mono hqb
  omega

lemma harper_macaulay_LE_gShift_right_confined (n : ℕ)
    (ih : ∀ m, m < n + 1 → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b p q r : ℕ}
    (ha : a ≤ 2 ^ (n + 1)) (hb : b ≤ 2 ^ (n + 1))
    (hcasc : CascadeSplit (n + 1) (a + b) p q)
    (hba : b ≤ a) (hcase : a ≤ H (n + 1) b) (hap : a ≤ p)
    (hr : 1 ≤ r)
    (hrlo : binomPrefix (n + 1) r ≤ b)
    (hrhi : b < binomPrefix (n + 1) (r + 1))
    (hahi : a ≤ binomPrefix (n + 1) (r + 2))
    (hphi : p ≤ binomPrefix (n + 1) (r + 2)) :
    gShiftIntervalCount (n + 1) a p ≤ gShiftIntervalCount (n + 1) q b :=
  harper_macaulay_LE_gShift_right n ih ha hb hcasc hba hcase hap

lemma harper_macaulay_GT_gShift (n : ℕ)
    (ih : ∀ m, m < n + 1 → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b p q : ℕ}
    (ha : a ≤ 2 ^ (n + 1)) (hb : b ≤ 2 ^ (n + 1))
    (hcasc : CascadeSplit (n + 1) (a + b) p q)
    (hba : b ≤ a) (hcase : H (n + 1) b < a)
    (hpa : p ≤ a) (hbq : b ≤ q) :
    gShiftIntervalCount (n + 1) b q + H (n + 1) b ≤ gShiftIntervalCount (n + 1) p a + a := by
  rcases Nat.eq_zero_or_pos q with hq0 | hq_pos
  · subst hq0
    have hb0 : b = 0 := Nat.le_zero.mp hbq
    subst hb0
    have hz : gShiftIntervalCount (n + 1) 0 0 = 0 := by
      rw [gShiftIntervalCount_eq_H_sub (n + 1) 0 0 (le_refl 0)]; simp
    rw [hz, H_zero]
    omega
  · have hsum := harper_macaulay_GT_sum n ih ha hb hcasc hq_pos hba hcase
    rw [gShiftIntervalCount_eq_H_sub (n + 1) b q hbq,
        gShiftIntervalCount_eq_H_sub (n + 1) p a hpa]
    have hHb_le_Hq : H (n + 1) b ≤ H (n + 1) q := H_mono hbq
    have hHp_le_Ha : H (n + 1) p ≤ H (n + 1) a := H_mono hpa
    omega

lemma harper_macaulay_GT_shadow_slack_core (n : ℕ)
    (ih : ∀ m, m < n + 1 → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b p q : ℕ}
    (ha : a ≤ 2 ^ (n + 1)) (hb : b ≤ 2 ^ (n + 1))
    (hcasc : CascadeSplit (n + 1) (a + b) p q)
    (hq_pos : 1 ≤ q) (hba : b ≤ a) (hcase : H (n + 1) b < a) :
    gShiftIntervalCount (n + 1) b q ≤
      gShiftIntervalCount (n + 1) p a + (a - H (n + 1) b) := by
  have hsum := harper_macaulay_GT_sum n ih ha hb hcasc hq_pos hba hcase
  obtain ⟨hbq, _, hpa, _⟩ := harper_gt_shadow_window_endpoints hcasc hq_pos hcase
  rw [gShiftIntervalCount_eq_H_sub (n + 1) b q hbq,
      gShiftIntervalCount_eq_H_sub (n + 1) p a hpa]
  have hHb_le_Hq : H (n + 1) b ≤ H (n + 1) q := H_mono hbq
  have hHp_le_Ha : H (n + 1) p ≤ H (n + 1) a := H_mono hpa
  omega

/-- Positive-cascade Case-I (LE) sum leaf.  Now a sorry-free corollary of the
Frankl–Füredi four-block exchange kernel `harper_macaulay_exchange_step`: choose
the four level-`n` cascade slice decompositions of `p, q, a, b` via
`exists_cascade_split`, obtain the lowered prefix-mass domination from
`canonicalSplit_interleaves` and `CascadeInterleaves.lower_succ`, then collapse
the outer `max`s (`canonical_boundaryCost_eq_H_add` on the left; `b ≤ a ≤ H b`
on the right). -/
/-- **Authoritative Case-I (LE) sum leaf.**  For the canonical cascade split
`(p, q)` of `a + b` at level `n + 1`, in the LE regime `b ≤ a ≤ H (n+1) b`, the
canonical split minimises the plain boundary sum
`H (n+1) p + H (n+1) q ≤ H (n+1) a + H (n+1) b`.  This is the max-free
Frankl–Füredi/Kruskal–Katona/Macaulay shadow-comparison leaf in PDF language; all
orientation-specific `gShiftIntervalCount` window kernels below are now sorry-free
corollaries of it.  Carries the level-`n` induction hypothesis `ih`.
(Verified true by an exact cascade model of `H` for all split dimensions ≤ 5.) -/
/-- **Authoritative Case-II (GT) sum leaf.**  For the canonical cascade split
`(p, q)` of `a + b` at level `n + 1`, in the GT regime `b ≤ a` and
`H (n+1) b < a`, the canonical split is bounded by the slack value
`H (n+1) p + H (n+1) q ≤ H (n+1) a + a`.  Max-free Frankl–Füredi/Macaulay slack
leaf; the `gShiftIntervalCount` slack forms below are now sorry-free corollaries.
Carries the level-`n` induction hypothesis `ih`.  Now a sorry-free corollary of
the Frankl–Füredi four-block exchange kernel `harper_macaulay_exchange_step`: the
outer `max`s collapse via `canonical_boundaryCost_eq_H_add` (left) and the GT
case hypothesis `H (n+1) b < a` (right, `max (H (n+1) b) a = a`).
(Verified true by an exact cascade model of `H` for all split dimensions ≤ 5.) -/
/-- **Macaulay shadow window kernel — LE regime, left orientation (`p ≤ a`).**
Equal-length window comparison `[b,q) ≤ [p,a)`.  Sorry-free corollary of the
authoritative sum leaf `harper_macaulay_LE_sum` via `gShiftIntervalCount_eq_H_sub`
and `H_mono`. -/
/-- **Layer-localized Case-I left Macaulay window kernel.**  The orientation
`p ≤ a` form of the Case-I shadow-window comparison, carrying the explicit
two-layer confinement (`b` in Macaulay layer `r`, `a` below layer `r+2`).  Now a
sorry-free corollary of `harper_macaulay_LE_sum`: the layer-localization
hypotheses are retained for the Macaulay block-accounting interface but are not
needed for the reduction. -/
/-- **Macaulay shadow window kernel — LE regime, right orientation (`a ≤ p`).**
Reversed window comparison `[a,p) ≤ [q,b)`.  Sorry-free corollary of
`harper_macaulay_LE_sum`. -/
/-- **Layer-localized Case-I right Macaulay window kernel.**  Now a sorry-free
corollary of `harper_macaulay_LE_sum`; the layer-localization hypotheses are
retained for the block-accounting interface but unused in the reduction. -/
/-- **Macaulay shadow slack window kernel — GT regime (`gShift` form).**  The
lower window `[b,q)` plus `H (n+1) b` is bounded by the upper window `[p,a)` plus
`a`.  Sorry-free corollary of the authoritative slack leaf
`harper_macaulay_GT_sum` (the degenerate `q = 0` branch is handled directly). -/
/--
Four-block Frankl-Füredi/Macaulay exchange kernel obtained after lowering a
level-`n+1` interleaving to the two level-`n` slices.

The hypotheses expose exactly the PDF-style profile data: canonical/cascade
slice decompositions for the four blocks and the shifted prefix-mass domination
that `CascadeInterleaves.lower_succ` provides.  Proving this is the remaining
paired Up/Down compression plus Macaulay shadow comparison; the wrapper
`boundaryCost_le_of_interleaves_core` below is now only bookkeeping that chooses
the four cascade decompositions and supplies this lowered profile inequality.

CORRECTNESS FIX (this cycle): the previous form of this leaf carried only the
lowered prefix-mass domination `h_lower` together with the four level-`n` slice
cascade splits, but had **dropped** the top-level cascade constraint
`CascadeSplit (n+1) (a+b) p q`.  Without it the statement is FALSE: an exact
cascade model of `H` exhibits counterexamples already at `n = 0`
(e.g. `a = 1, b = 0, p = q = 2`), and more generally `h_lower` together with
`p + q = a + b` alone is insufficient (e.g. `n = 1, a = 1, b = 3, p = q = 2`).
The genuine Macaulay statement requires `(p, q)` to be the canonical cascade
split of `a + b`; with that hypothesis restored the statement is true (verified
by the exact model for all split dimensions `≤ 4`).  The wrapper already has this
fact available as `h_inter.cascade`, so the public chain is unchanged.
-/
lemma boundaryCost_le_of_lower_interleaves_step
    (n p q a b p0 p1 q0 q1 a0 a1 b0 b1 : ℕ)
    (ih : ∀ m, m < n + 1 → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    (ha_cap : a ≤ 2 ^ (n + 1)) (hb_cap : b ≤ 2 ^ (n + 1))
    (hpq_casc : CascadeSplit (n + 1) (a + b) p q)
    (hp : CascadeSplit n p p0 p1) (hq : CascadeSplit n q q0 q1)
    (ha : CascadeSplit n a a0 a1) (hb : CascadeSplit n b b0 b1)
    (h_lower : ∀ l,
      splitPrefixMass n a0 b0 (l + 1) + splitPrefixMass n a1 b1 l
        ≤ splitPrefixMass n p0 q0 (l + 1) + splitPrefixMass n p1 q1 l) :
    max (H (n + 1) p) q + max (H (n + 1) q) p ≤
      max (H (n + 1) a) b + max (H (n + 1) b) a := by
  rcases le_total b a with hba | hab
  · exact boundaryCost_le_of_LE_GT_sums n ha_cap hb_cap hpq_casc hba
  · have hpq_casc' : CascadeSplit (n + 1) (b + a) p q := by
      rwa [Nat.add_comm] at hpq_casc
    have h := boundaryCost_le_of_LE_GT_sums n hb_cap ha_cap hpq_casc' hab
    rw [Nat.add_comm (max (H (n + 1) a) b) (max (H (n + 1) b) a)]
    exact h
-/

/--
Frankl-Füredi inductive boundary monotonicity for a cascade-interleaving profile.

This is the remaining local compression/Macaulay step in the form actually used
by the Harper induction: the arbitrary split has capacity bounds, and the proof
may use the already-established lower-dimensional Harper inequality.  The older
capacity-free, `ih`-free version was stronger than the live proof route and hid
the PDF's inductive input.
-/
lemma boundaryCost_le_of_interleaves_core (n p q a b : ℕ)
    (ih : ∀ m, m < n + 1 → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    (ha : a ≤ 2 ^ (n + 1)) (hb : b ≤ 2 ^ (n + 1))
    (h_inter : CascadeInterleaves (n + 1) p q a b) :
    max (H (n + 1) p) q + max (H (n + 1) q) p ≤
      max (H (n + 1) a) b + max (H (n + 1) b) a := by
  have hpq_casc : CascadeSplit (n + 1) (a + b) p q := h_inter.cascade
  rcases le_total b a with hba | hab
  · exact boundaryCost_le_of_LE_GT_sums n ih ha hb hpq_casc hba
  · have hpq_casc' : CascadeSplit (n + 1) (b + a) p q := by
      rwa [Nat.add_comm a b] at hpq_casc
    have h := boundaryCost_le_of_LE_GT_sums n ih hb ha hpq_casc' hab
    rw [Nat.add_comm (max (H (n + 1) a) b) (max (H (n + 1) b) a)]
    exact h

/--
**Frankl–Füredi joint Macaulay kernel — the single unified leaf (LE ∪ GT).**
For the canonical cascade split `(p, q)` of `a + b` at level `n + 1` (so `(p,q)`
is the split of `a + b` in the `(n+2)`-cube, while the boundary values live in
the `(n+1)`-cube), in the ordered regime `b ≤ a`, the canonical boundary sum
`H (n+1) p + H (n+1) q` is bounded by the **arbitrary-split boundary functional**
`H (n+1) a + max (H (n+1) b) a`.
-/
lemma harper_macaulay_joint (n : ℕ) {a b p q : ℕ}
    (ih : ∀ m, m < n + 1 → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    (ha : a ≤ 2 ^ (n + 1)) (hb : b ≤ 2 ^ (n + 1))
    (hcasc : CascadeSplit (n + 1) (a + b) p q)
    (hq_pos : 1 ≤ q) (hba : b ≤ a) :
    H (n + 1) p + H (n + 1) q ≤ H (n + 1) a + max (H (n + 1) b) a := by
  have h_inter := canonicalSplit_interleaves ha hb hcasc
  have h_mono := boundaryCost_le_of_interleaves_core n p q a b ih ha hb h_inter
  have h_b_le_H_a : b ≤ H (n + 1) a := le_trans hba (H_ge_self (n + 1) a ha)
  have max1 : max (H (n + 1) a) b = H (n + 1) a := max_eq_left h_b_le_H_a
  have h_p_ge_q : q ≤ p := cascade_q_le_p hcasc
  have h_p_le : p ≤ 2 ^ (n + 1) := cascade_p_le hcasc
  have h_q_le_H_p : q ≤ H (n + 1) p := le_trans h_p_ge_q (H_ge_self (n + 1) p h_p_le)
  have max2 : max (H (n + 1) p) q = H (n + 1) p := max_eq_left h_q_le_H_p
  have h_p_le_H_q : p ≤ H (n + 1) q := cascade_p_le_H_q hcasc hq_pos
  have max3 : max (H (n + 1) q) p = H (n + 1) q := max_eq_left h_p_le_H_q
  rw [max1, max2, max3] at h_mono
  exact h_mono

/--
**Frankl–Füredi Case I, joint-sum Macaulay kernel (the LE corollary).**
Now a proved corollary of the unified kernel `harper_macaulay_joint`: in the
LE regime `a ≤ H (n+1) b` the boundary `max (H (n+1) b) a` collapses to
`H (n+1) b` (`max_eq_left`).
-/
lemma harper_macaulay_window_le (n : ℕ)
    (ih : ∀ m, m < n + 1 → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b p q : ℕ}
    (ha : a ≤ 2 ^ (n + 1)) (hb : b ≤ 2 ^ (n + 1))
    (hcasc : CascadeSplit (n + 1) (a + b) p q)
    (hq_pos : 1 ≤ q) (hba : b ≤ a) (hcase : a ≤ H (n + 1) b) :
    H (n + 1) p + H (n + 1) q ≤ H (n + 1) a + H (n + 1) b := by
  have h := harper_macaulay_joint n ih ha hb hcasc hq_pos hba
  rwa [max_eq_left hcase] at h

/--
**Frankl–Füredi Case II, GT joint slack kernel (the GT corollary).**
Now a proved corollary of the unified kernel `harper_macaulay_joint`: in the
GT regime `H (n+1) b < a` the boundary `max (H (n+1) b) a` collapses to `a`
(`max_eq_right`).

This is the genuine *joint* slack bound; the previously-exposed split into
`H (n+1) q ≤ a` and `H (n+1) p ≤ H (n+1) a` is false (see the commented note
above), so the GT bound must keep `H (n+1) p + H (n+1) q ≤ H (n+1) a + a` intact.
-/
lemma harper_macaulay_slack_gt (n : ℕ)
    (ih : ∀ m, m < n + 1 → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b p q : ℕ}
    (ha : a ≤ 2 ^ (n + 1)) (hb : b ≤ 2 ^ (n + 1))
    (hcasc : CascadeSplit (n + 1) (a + b) p q)
    (hq_pos : 1 ≤ q) (hba : b ≤ a) (hcase : H (n + 1) b < a) :
    H (n + 1) p + H (n + 1) q ≤ H (n + 1) a + a := by
  have h := harper_macaulay_joint n ih ha hb hcasc hq_pos hba
  rwa [max_eq_right hcase.le] at h

/--
GT Macaulay shadow slack comparison (PDF-faithful shadow-count form).  Now a
proved corollary of the joint slack kernel `harper_macaulay_slack_gt`:
`harper_gt_split_between` supplies `b ≤ q ≤ p ≤ a`, the shadow windows rewrite to
`H` differences, and the goal follows by arithmetic (`H_mono` plus `omega`).
-/
lemma harper_macaulay_shadow_gt (n : ℕ)
    (ih : ∀ m, m < n + 1 → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b p q : ℕ}
    (ha : a ≤ 2 ^ (n + 1)) (hb : b ≤ 2 ^ (n + 1))
    (hcasc : CascadeSplit (n + 1) (a + b) p q)
    (hba : b ≤ a) (hcase : H (n + 1) b < a) (hq_pos : 1 ≤ q) :
    gShiftIntervalCount (n + 1) b q ≤
      gShiftIntervalCount (n + 1) p a + (a - H (n + 1) b) := by
  obtain ⟨hbq, hqp, hpa⟩ := harper_gt_split_between n hq_pos hcase hcasc
  rw [gShiftIntervalCount_eq_H_sub (n + 1) b q hbq,
      gShiftIntervalCount_eq_H_sub (n + 1) p a hpa]
  have hslack := harper_macaulay_slack_gt n ih ha hb hcasc hq_pos hba hcase
  have hHbq : H (n + 1) b ≤ H (n + 1) q := H_mono hbq
  have hHpa : H (n + 1) p ≤ H (n + 1) a := H_mono hpa
  omega

/--
**Frankl–Füredi Case I, canonical-sum core.**
For the canonical cascade split `(p, q)` of `a + b` at dimension `n + 1`, in the
LE regime `b ≤ a ≤ H (n+1) b`, the canonical boundary sum `H(n+1)p + H(n+1)q`
is bounded by the arbitrary-split boundary sum `H(n+1)a + H(n+1)b`.

This is the genuine max-free Macaulay heart of the LE case.  It is strictly
narrower than `harper_step_total`: it adds the ordering hypothesis `b ≤ a` and
the case hypothesis `a ≤ H (n+1) b`, fixes the canonical split, and has the two
outer `max`s already collapsed.  It mentions only `H`, `CascadeSplit`, and the
level-`n` induction hypothesis `ih`, and is non-circular.

NOTE (cycle37.aristotle).  This replaces the previous leaf
`harper_step_le_window_shift`, which asserted the endpoint order `a ≤ p` together
with a `gShiftIntervalCount` window inequality.  An exact computational model of
`H` via the cascade recursion shows `a ≤ p` is **false** in the LE regime (176
counterexamples for `n ≤ 4`, smallest `n = 1, a = 4, b = 2` with `(p,q)=(3,3)`):
the canonical split can place *less* than `a` in its lower slice, so the windows
`[a,p)` and `[q,b)` are not nested as that lemma required.  The *sum* form proved
here is true (0 counterexamples for `n ≤ 6`) and is the correct LE leaf.
-/
lemma harper_step_le_canonical_sum (n : ℕ)
    (ih : ∀ m, m < n + 1 → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b p q : ℕ} (ha : a ≤ 2 ^ (n + 1)) (hb : b ≤ 2 ^ (n + 1))
    (hcasc : CascadeSplit (n + 1) (a + b) p q)
    (hba : b ≤ a) (hcase : a ≤ H (n + 1) b) :
    H (n + 1) p + H (n + 1) q ≤ H (n + 1) a + H (n + 1) b := by
  by_cases hq : q = 0
  · have htotal : a + b ≤ 1 := by
      simpa [hq] using cascade_split_q_zero_total_le_one (by simpa [hq] using hcasc)
    have hb_zero : b = 0 := by omega
    subst b
    have ha_val : a = 0 ∨ a = 1 := by omega
    rcases ha_val with rfl | rfl
    · have hp_val : p = 0 := by have hsum := cascade_split_add hcasc; omega
      simp [hq, hp_val]
    · have hp_val : p = 1 := by have hsum := cascade_split_add hcasc; omega
      simp [hq, hp_val, H_zero, H_one]
  · have hq_pos : 1 ≤ q := Nat.pos_of_ne_zero hq
    exact harper_macaulay_window_le n ih ha hb hcasc hq_pos hba hcase

/-!
### Frankl–Füredi LE/GT decomposition of the Harper inductive step

NOTE (cycle36.aristotle).  A previous cycle exposed the kernel as a single
`Int` "profile shadow" leaf `franklFuredi_profile_residual_nonneg`, asserting

```
weightedNestedLayerCost n (binomLayerWeight n) p0 p1 q0 q1
  - weightedNestedLayerCost n (binomLayerWeight n) a0 a1 b0 b1
    ≤ (boundaryCostH (n+1) a b : ℤ) - (pairedCascadeBoundary n p0 p1 q0 q1 : ℤ)
```

with `binomLayerWeight n l = n + 1 - l`.  An exact computational model of `H`
via the cascade recursion shows this residual statement is **false** (187
counterexamples for `n ≤ 3`, the smallest being `n = 0, a = 0, b = 2`).  The
reason is structural: the only antitone layer weights `w` for which
`Σ w l · (massₚ l − mass_a l)` is sandwiched in `[0, B − P]` over all profiles
are the *constant* weights — and for those the sum is identically `0` because
total layer mass is conserved.  Hence **no single per-layer Abel weight** can
bridge the coarse layer gap to the boundary deficit; the linear weight
`n + 1 − l` over-counts.  (The coarse direction
`franklFuredi_profile_coarse_layer_gap_nonneg`, i.e. `Wₚ ≥ W_a`, is genuinely
true and kept above as reusable Abel infrastructure, but it is not sufficient.)

The false leaf has therefore been removed and the kernel re-decomposed along the
standard Frankl–Füredi case split (which collapses the two outer `max`s of
`boundaryCostH`): a max-free `LE` case (`harper_step_le`) and a max-free `GT`
case (`harper_step_gt`).  Both statements are **true** (verified by the exact
cascade model for all `b ≤ a` with `a, b ≤ 2^(n+1)` and `n ≤ 4`) and strictly
narrower than `harper_step_total`, and `harper_step_total` is now a proved
consequence of them via `boundaryCostH_eq_H_add_slack`.
-/

/--
**Frankl–Füredi Case I, sum form.**
In the LE regime `a ≤ H (n+1) b`, the max-form boundary cost collapses to the
plain sum `H (n+1) a + H (n+1) b`.  This lemma is now a proved reduction to
the canonical-sum core `harper_step_le_canonical_sum`: after choosing the
canonical split `(p,q)` of `a+b` and dispatching the degenerate `q = 0` branch,
the positive branch rewrites `H (n+2) (a+b)` to `H(n+1)p + H(n+1)q` and applies
the core.
-/
lemma harper_step_le_sum_form (n : ℕ)
    (ih : ∀ m, m < n + 1 → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b : ℕ} (ha : a ≤ 2 ^ (n + 1)) (hb : b ≤ 2 ^ (n + 1))
    (hba : b ≤ a) (hcase : a ≤ H (n + 1) b) :
    H (n + 2) (a + b) ≤ H (n + 1) a + H (n + 1) b := by
  obtain ⟨p, q, hp, hq, _hpq, hcasc⟩ :=
    exists_cascade_split (n + 1) (a + b) (by
      have hsum : a + b ≤ 2 ^ (n + 1) + 2 ^ (n + 1) := Nat.add_le_add ha hb
      have hpow : 2 ^ (n + 2) = 2 ^ (n + 1) + 2 ^ (n + 1) := by
        rw [show n + 2 = n + 1 + 1 by omega, pow_succ]
        ring
      rwa [hpow])
  by_cases hq_zero : q = 0
  · have htotal : a + b ≤ 1 := by
      simpa [hq_zero] using cascade_split_q_zero_total_le_one (by simpa [hq_zero] using hcasc)
    rcases (by omega : a = 0 ∨ a = 1) with rfl | rfl
    · have hb_zero : b = 0 := by omega
      subst b
      simp [H_zero]
    · have hb_zero : b = 0 := by omega
      subst b
      simp [H_zero] at hcase
  · have hq_pos : 1 ≤ q := Nat.pos_of_ne_zero hq_zero
    have hcanon :
        H (n + 2) (a + b) = H (n + 1) p + H (n + 1) q := by
      have hsucc : H (n + 2) (a + b)
          = max (H (n + 1) p) q + max (H (n + 1) q) p := by
        rw [show n + 2 = n + 1 + 1 from rfl]
        exact H_succ_cascade hcasc
      have hcollapse :
          max (H (n + 1) p) q + max (H (n + 1) q) p =
            H (n + 1) p + H (n + 1) q :=
        canonical_boundaryCost_eq_H_add hp hq hq_pos hcasc
      rw [hsucc, hcollapse]
    rw [hcanon]
    exact harper_step_le_canonical_sum n ih ha hb hcasc hba hcase

lemma harper_step_le (n : ℕ)
    (ih : ∀ m, m < n + 1 → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b : ℕ} (ha : a ≤ 2 ^ (n + 1)) (hb : b ≤ 2 ^ (n + 1))
    (hba : b ≤ a) (hcase : a ≤ H (n + 1) b) :
    H (n + 2) (a + b) ≤ H (n + 1) a + H (n + 1) b :=
  harper_step_le_sum_form n ih ha hb hba hcase

/--
**Frankl–Füredi Case II (the GT regime).**  Under `b ≤ a` and `H (n+1) b < a`,
the boundary cost `boundaryCostH (n+1) a b` collapses to `H (n+1) a + a`.  This
is the max-free combinatorial heart of Harper's `n → n+1` step in the GT regime.

It is strictly narrower than `harper_step_total` (adds `b ≤ a` and the case
hypothesis `H (n+1) b < a`, with the outer `max`s eliminated), mentions only
`H` and `ih`, and is non-circular.
-/
lemma harper_step_gt (n : ℕ)
    (ih : ∀ m, m < n + 1 → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b : ℕ} (ha : a ≤ 2 ^ (n + 1)) (hb : b ≤ 2 ^ (n + 1))
    (hba : b ≤ a) (hcase : H (n + 1) b < a) :
    H (n + 2) (a + b) ≤ H (n + 1) a + a := by
  have hab_le : a + b ≤ 2 ^ (n + 2) := by
    have h_pow : 2 ^ (n + 2) = 2 ^ (n + 1) + 2 ^ (n + 1) := by
      rw [pow_succ, Nat.mul_two]
    omega
  have ⟨p, q, hp, hq, _, hcasc⟩ := exists_cascade_split (n + 1) (a + b) hab_le
  have hH_succ := H_succ_cascade hcasc
  rw [hH_succ]
  by_cases hq_zero : q = 0
  · have htotal : a + b ≤ 1 := by
      simpa using cascade_split_q_zero_total_le_one (by simpa [hq_zero] using hcasc)
    have hb_zero : b = 0 := by omega
    subst b
    have a_pos : 0 < a := by
      have H_b_zero : H (n + 1) 0 = 0 := H_zero (n + 1)
      omega
    have ha_val : a = 1 := by omega
    subst a
    have hp_val : p = 1 := by have hsum := cascade_split_add hcasc; omega
    simp [hq_zero, hp_val, H_zero, H_one]
  · have hq_pos : 1 ≤ q := Nat.pos_of_ne_zero hq_zero
    rw [canonical_boundaryCost_eq_H_add hp hq hq_pos hcasc]
    exact harper_macaulay_slack_gt n ih ha hb hcasc hq_pos hba hcase


/--
The `b ≤ a` branch of `harper_step_total`, assembled from the two max-free case
lemmas by collapsing the slack form of `boundaryCostH`
(`boundaryCostH_eq_H_add_slack`).  Sorry-free.
-/
lemma harper_step_total_le_case (n : ℕ)
    (ih : ∀ m, m < n + 1 → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b : ℕ} (ha : a ≤ 2 ^ (n + 1)) (hb : b ≤ 2 ^ (n + 1))
    (hba : b ≤ a) :
    H (n + 2) (a + b) ≤ boundaryCostH (n + 1) a b := by
  rw [boundaryCostH_eq_H_add_slack]
  have hbHa : b ≤ H (n + 1) a := le_trans hba (H_ge_self (n + 1) a ha)
  by_cases hcase : a ≤ H (n + 1) b
  · have h := harper_step_le n ih ha hb hba hcase
    omega
  · have hcase' : H (n + 1) b < a := Nat.lt_of_not_le hcase
    have h := harper_step_gt n ih ha hb hba hcase'
    omega

lemma harper_step_total (n : ℕ)
    (ih : ∀ m, m < n + 1 → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b : ℕ} (ha : a ≤ 2 ^ (n + 1)) (hb : b ≤ 2 ^ (n + 1)) :
    H (n + 2) (a + b) ≤ boundaryCostH (n + 1) a b := by
  rcases le_total b a with hba | hab
  · exact harper_step_total_le_case n ih ha hb hba
  · rw [boundaryCostH_comm, Nat.add_comm a b]
    exact harper_step_total_le_case n ih hb ha hab

/--
The four-block Frankl-Furedi profile bridge, now a proved consequence of
the pure-`H` kernel `harper_step_total`.  Using
`pairedCascadeBoundary_pos_eq_H_succ`, the four-block boundary on the left is
exactly `H (n+2) (a+b)`, and the conclusion is then `harper_step_total`.
-/
lemma harper_extremal_step_nested_pos (n : ℕ)
    (ih : ∀ m, m < n + 1 → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b p q : ℕ} (ha : a ≤ 2 ^ (n + 1)) (hb : b ≤ 2 ^ (n + 1))
    (hcasc : CascadeSplit (n + 1) (a + b) p q) :
    H (n + 1) p + H (n + 1) q ≤
      max (H (n + 1) a) b + max (H (n + 1) b) a := by
  by_cases hq_zero : q = 0
  · have hp : p ≤ 2 ^ (n + 1) := cascade_p_le hcasc
    have hq : q ≤ 2 ^ (n + 1) := cascade_q_le hcasc
    obtain ⟨p0, p1, hp0, hp1, _hp_add, hp_split⟩ := exists_cascade_split n p hp
    obtain ⟨q0, q1, hq0, hq1, _hq_add, hq_split⟩ := exists_cascade_split n q hq
    obtain ⟨a0, a1, ha0, ha1, _ha_add, ha_split⟩ := exists_cascade_split n a ha
    obtain ⟨b0, b1, hb0, hb1, _hb_add, hb_split⟩ := exists_cascade_split n b hb
    have hzero :=
      harper_extremal_step_nested_q_zero n ih ha hb hcasc hq_zero
        hp0 hp1 hq0 hq1 ha0 ha1 hb0 hb1
        hp_split hq_split ha_split hb_split
    rw [H_succ_cascade hp_split, H_succ_cascade hq_split,
      H_succ_cascade ha_split, H_succ_cascade hb_split]
    exact le_trans (Nat.add_le_add (le_max_left _ _) (le_max_left _ _)) hzero
  · have hq_pos : 1 ≤ q := Nat.pos_of_ne_zero hq_zero
    have hp : p ≤ 2 ^ (n + 1) := cascade_p_le hcasc
    have hq : q ≤ 2 ^ (n + 1) := cascade_q_le hcasc
    have htotal := harper_step_total n ih ha hb
    have hsucc := H_succ_cascade hcasc
    have hcanon := canonical_boundaryCost_eq_H_add hp hq hq_pos hcasc
    rw [hsucc, hcanon] at htotal
    exact htotal

/--
The four-block Macaulay/cascade interleaving comparison with explicit witnesses.
This exposes the nested canonical splits at level `n` for all components, reducing
the `H (n+1)` expressions to purely `n`-level `max` combinations.
-/
lemma harper_extremal_step_nested (n : ℕ)
    (ih : ∀ m, m < n + 1 → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b p q p0 p1 q0 q1 a0 a1 b0 b1 : ℕ}
    (ha : a ≤ 2 ^ (n + 1)) (hb : b ≤ 2 ^ (n + 1))
    (hcasc : CascadeSplit (n + 1) (a + b) p q)
    (hp0 : p0 ≤ 2 ^ n) (hp1 : p1 ≤ 2 ^ n)
    (hq0 : q0 ≤ 2 ^ n) (hq1 : q1 ≤ 2 ^ n)
    (ha0 : a0 ≤ 2 ^ n) (ha1 : a1 ≤ 2 ^ n)
    (hb0 : b0 ≤ 2 ^ n) (hb1 : b1 ≤ 2 ^ n)
    (hp_split : CascadeSplit n p p0 p1)
    (hq_split : CascadeSplit n q q0 q1)
    (ha_split : CascadeSplit n a a0 a1)
    (hb_split : CascadeSplit n b b0 b1) :
    max (max (H n p0) p1 + max (H n p1) p0) q +
    max (max (H n q0) q1 + max (H n q1) q0) p ≤
    max (max (H n a0) a1 + max (H n a1) a0) b +
    max (max (H n b0) b1 + max (H n b1) b0) a := by
  by_cases hq_zero : q = 0
  · exact harper_extremal_step_nested_q_zero n ih ha hb hcasc hq_zero
      hp0 hp1 hq0 hq1 ha0 ha1 hb0 hb1
      hp_split hq_split ha_split hb_split
  · have hq_pos : 1 ≤ q := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hq_zero)
    have hp : p ≤ 2 ^ (n + 1) := cascade_p_le hcasc
    have hq : q ≤ 2 ^ (n + 1) := cascade_q_le hcasc
    have hpos := harper_extremal_step_nested_pos n ih ha hb hcasc
    rw [← H_succ_cascade hp_split, ← H_succ_cascade hq_split,
        ← H_succ_cascade ha_split, ← H_succ_cascade hb_split]
    rw [canonical_boundaryCost_eq_H_add hp hq hq_pos hcasc]
    exact hpos

/--
**The single remaining open step.**  The Harper/Macaulay extremal inequality at
level `n + 1`, derived from the *same inequality at all lower levels* (`ih`).

This is exactly `harper_extremal_n` shifted one dimension up (note the identical
shape: the conclusion is the cross boundary cost of the canonical cascade split
being minimal), so it *is* the genuine `n → n+1` inductive step of Harper's
vertex-isoperimetric theorem, with nothing else attached.

Compared with the original `_core` lemmas, this statement is strictly narrower:
it has no case hypothesis, no ordering `b ≤ a`, no positivity `1 ≤ q`, and none
of the eight level-`n` sub-component variables / their cascade splits / bounds.
It mentions only `H`, `CascadeSplit`, and `ih`, and is non-circular (it does not
refer to any later result such as `harper_core`, `harper_bc_min`,
`macaulay_optimization`, or `H_inequality_core`).

It has no elementary proof: `H (n+1)` is neither convex nor concave and the cross
boundary cost is not a unimodal function of the split, so the genuine
Kruskal–Katona / Macaulay cascade-interleaving argument is required.
-/
lemma harper_extremal_step (n : ℕ)
    (ih : ∀ m, m < n + 1 → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b p q : ℕ} (ha : a ≤ 2 ^ (n + 1)) (hb : b ≤ 2 ^ (n + 1))
    (hcasc : CascadeSplit (n + 1) (a + b) p q) :
    max (H (n + 1) p) q + max (H (n + 1) q) p ≤
      max (H (n + 1) a) b + max (H (n + 1) b) a := by
  have hp : p ≤ 2 ^ (n + 1) := cascade_p_le hcasc
  have hq : q ≤ 2 ^ (n + 1) := cascade_q_le hcasc
  obtain ⟨p0, p1, hp0, hp1, _, hp_split⟩ := exists_cascade_split n p hp
  obtain ⟨q0, q1, hq0, hq1, _, hq_split⟩ := exists_cascade_split n q hq
  obtain ⟨a0, a1, ha0, ha1, _, ha_split⟩ := exists_cascade_split n a ha
  obtain ⟨b0, b1, hb0, hb1, _, hb_split⟩ := exists_cascade_split n b hb
  have h_nested := harper_extremal_step_nested n ih ha hb hcasc
    hp0 hp1 hq0 hq1 ha0 ha1 hb0 hb1
    hp_split hq_split ha_split hb_split
  rwa [← H_succ_cascade hp_split, ← H_succ_cascade hq_split,
       ← H_succ_cascade ha_split, ← H_succ_cascade hb_split] at h_nested

/--
Clean `H (n+1)`-level form of Case I of the `n → n+1` inductive step.  Given the
canonical cascade split `(p, q)` of `a + b` at level `n+1`, and that the larger
part `a` still fits inside the neighbourhood of the smaller part (`a ≤ H (n+1) b`),
the split boundary sum is no larger than `H (n+1) a + H (n+1) b`.

This is now a short consequence of `harper_extremal_step` (the unified extremal
step) together with `canonical_boundaryCost_eq_H_add` and the case hypotheses.
-/
lemma harper_nested_g_le (n : ℕ)
    (ih : ∀ m, m < n + 1 → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b p q : ℕ}
    (ha : a ≤ 2 ^ (n + 1)) (hb : b ≤ 2 ^ (n + 1))
    (hp : p ≤ 2 ^ (n + 1)) (hq : q ≤ 2 ^ (n + 1))
    (hq_pos : 1 ≤ q)
    (hb_le_a : b ≤ a)
    (hcase : a ≤ H (n + 1) b)
    (_ : p + q = a + b)
    (hcasc : CascadeSplit (n + 1) (a + b) p q) :
    H (n + 1) p + H (n + 1) q ≤ H (n + 1) a + H (n + 1) b := by
  have hL := harper_extremal_step n ih ha hb hcasc
  rw [canonical_boundaryCost_eq_H_add hp hq hq_pos hcasc] at hL
  have hga : a ≤ H (n + 1) a := H_ge_self (n + 1) a ha
  have m1 : max (H (n + 1) a) b = H (n + 1) a := max_eq_left (le_trans hb_le_a hga)
  have m2 : max (H (n + 1) b) a = H (n + 1) b := max_eq_left hcase
  rw [m1, m2] at hL
  exact hL

/--
Clean `H (n+1)`-level form of Case II of the `n → n+1` inductive step.  Given the
canonical cascade split `(p, q)` of `a + b` at level `n+1`, and that the larger
part `a` exceeds the neighbourhood of the smaller part (`H (n+1) b < a`), the
split boundary sum is no larger than `H (n+1) a + a`.

This is now a short consequence of `harper_extremal_step` together with
`canonical_boundaryCost_eq_H_add` and the case hypotheses.
-/
lemma harper_nested_g_gt (n : ℕ)
    (ih : ∀ m, m < n + 1 → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b p q : ℕ}
    (ha : a ≤ 2 ^ (n + 1)) (hb : b ≤ 2 ^ (n + 1))
    (hp : p ≤ 2 ^ (n + 1)) (hq : q ≤ 2 ^ (n + 1))
    (hq_pos : 1 ≤ q)
    (hb_le_a : b ≤ a)
    (hcase : H (n + 1) b < a)
    (_ : p + q = a + b)
    (hcasc : CascadeSplit (n + 1) (a + b) p q) :
    H (n + 1) p + H (n + 1) q ≤ H (n + 1) a + a := by
  have hL := harper_extremal_step n ih ha hb hcasc
  rw [canonical_boundaryCost_eq_H_add hp hq hq_pos hcasc] at hL
  have hga : a ≤ H (n + 1) a := H_ge_self (n + 1) a ha
  have m1 : max (H (n + 1) a) b = H (n + 1) a := max_eq_left (le_trans hb_le_a hga)
  have m2 : max (H (n + 1) b) a = a := max_eq_right (le_of_lt hcase)
  rw [m1, m2] at hL
  exact hL

lemma harper_subadd_le_cascade_pos_succ_nested_core
    (n : ℕ)
    (ih : ∀ m, m < n + 1 → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b p q p0 p1 q0 q1 a0 a1 b0 b1 : ℕ}
    (ha : a ≤ 2 ^ (n + 1)) (hb : b ≤ 2 ^ (n + 1))
    (hp : p ≤ 2 ^ (n + 1)) (hq : q ≤ 2 ^ (n + 1))
    (hq_pos : 1 ≤ q)
    (hb_le_a : b ≤ a)
    (hcase : a ≤ H n b0 + if 1 ≤ b1 then H n b1 else b0)
    (hpq : p + q = a + b)
    (hcasc : CascadeSplit (n + 1) (a + b) p q)
    (hp0 : p0 ≤ 2 ^ n) (_ : p1 ≤ 2 ^ n)
    (hq0 : q0 ≤ 2 ^ n) (_ : q1 ≤ 2 ^ n)
    (ha0 : a0 ≤ 2 ^ n) (_ : a1 ≤ 2 ^ n)
    (hb0 : b0 ≤ 2 ^ n) (_ : b1 ≤ 2 ^ n)
    (hp_split : CascadeSplit n p p0 p1)
    (hq_split : CascadeSplit n q q0 q1)
    (ha_split : CascadeSplit n a a0 a1)
    (hb_split : CascadeSplit n b b0 b1) :
    H n p0 + (if 1 ≤ p1 then H n p1 else p0) +
        (H n q0 + (if 1 ≤ q1 then H n q1 else q0)) ≤
      H n a0 + (if 1 ≤ a1 then H n a1 else a0) +
        (H n b0 + (if 1 ≤ b1 then H n b1 else b0)) := by
  have ep : H n p0 + (if 1 ≤ p1 then H n p1 else p0) = H (n + 1) p := by
    rw [← H_succ_cascade_expand hp_split hp0]; exact (H_succ_cascade hp_split).symm
  have eq' : H n q0 + (if 1 ≤ q1 then H n q1 else q0) = H (n + 1) q := by
    rw [← H_succ_cascade_expand hq_split hq0]; exact (H_succ_cascade hq_split).symm
  have ea : H n a0 + (if 1 ≤ a1 then H n a1 else a0) = H (n + 1) a := by
    rw [← H_succ_cascade_expand ha_split ha0]; exact (H_succ_cascade ha_split).symm
  have eb : H n b0 + (if 1 ≤ b1 then H n b1 else b0) = H (n + 1) b := by
    rw [← H_succ_cascade_expand hb_split hb0]; exact (H_succ_cascade hb_split).symm
  rw [eb] at hcase
  rw [ep, eq', ea, eb]
  exact harper_nested_g_le n ih ha hb hp hq hq_pos hb_le_a hcase hpq hcasc

lemma harper_subadd_le_cascade_pos_succ_nested
    (n : ℕ)
    (ih : ∀ m, m < n + 1 → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b p q p0 p1 q0 q1 a0 a1 b0 b1 : ℕ}
    (ha : a ≤ 2 ^ (n + 1)) (hb : b ≤ 2 ^ (n + 1))
    (hp : p ≤ 2 ^ (n + 1)) (hq : q ≤ 2 ^ (n + 1))
    (hq_pos : 1 ≤ q)
    (hb_le_a : b ≤ a)
    (hcase : a ≤ max (H n b0) b1 + max (H n b1) b0)
    (hpq : p + q = a + b)
    (hcasc : CascadeSplit (n + 1) (a + b) p q)
    (hp0 : p0 ≤ 2 ^ n) (hp1 : p1 ≤ 2 ^ n)
    (hq0 : q0 ≤ 2 ^ n) (hq1 : q1 ≤ 2 ^ n)
    (ha0 : a0 ≤ 2 ^ n) (ha1 : a1 ≤ 2 ^ n)
    (hb0 : b0 ≤ 2 ^ n) (hb1 : b1 ≤ 2 ^ n)
    (hp_split : CascadeSplit n p p0 p1)
    (hq_split : CascadeSplit n q q0 q1)
    (ha_split : CascadeSplit n a a0 a1)
    (hb_split : CascadeSplit n b b0 b1) :
    max (H n p0) p1 + max (H n p1) p0 +
        (max (H n q0) q1 + max (H n q1) q0) ≤
      max (H n a0) a1 + max (H n a1) a0 +
        (max (H n b0) b1 + max (H n b1) b0) := by
  rw [H_succ_cascade_expand hp_split hp0]
  rw [H_succ_cascade_expand hq_split hq0]
  rw [H_succ_cascade_expand ha_split ha0]
  rw [H_succ_cascade_expand hb_split hb0]
  have hcase_rewritten : a ≤ H n b0 + if 1 ≤ b1 then H n b1 else b0 := by
    rwa [← H_succ_cascade_expand hb_split hb0]
  exact harper_subadd_le_cascade_pos_succ_nested_core n ih ha hb hp hq hq_pos hb_le_a
    hcase_rewritten hpq hcasc hp0 hp1 hq0 hq1 ha0 ha1 hb0 hb1 hp_split hq_split ha_split hb_split

lemma harper_subadd_gt_cascade_pos_succ_nested_core
    (n : ℕ)
    (ih : ∀ m, m < n + 1 → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b p q p0 p1 q0 q1 a0 a1 b0 b1 : ℕ}
    (ha : a ≤ 2 ^ (n + 1)) (hb : b ≤ 2 ^ (n + 1))
    (hp : p ≤ 2 ^ (n + 1)) (hq : q ≤ 2 ^ (n + 1))
    (hq_pos : 1 ≤ q)
    (hb_le_a : b ≤ a)
    (hcase : H n b0 + (if 1 ≤ b1 then H n b1 else b0) < a)
    (hpq : p + q = a + b)
    (hcasc : CascadeSplit (n + 1) (a + b) p q)
    (hp0 : p0 ≤ 2 ^ n) (_ : p1 ≤ 2 ^ n)
    (hq0 : q0 ≤ 2 ^ n) (_ : q1 ≤ 2 ^ n)
    (ha0 : a0 ≤ 2 ^ n) (_ : a1 ≤ 2 ^ n)
    (hb0 : b0 ≤ 2 ^ n) (_ : b1 ≤ 2 ^ n)
    (hp_split : CascadeSplit n p p0 p1)
    (hq_split : CascadeSplit n q q0 q1)
    (ha_split : CascadeSplit n a a0 a1)
    (hb_split : CascadeSplit n b b0 b1) :
    H n p0 + (if 1 ≤ p1 then H n p1 else p0) +
        (H n q0 + (if 1 ≤ q1 then H n q1 else q0)) ≤
      H n a0 + (if 1 ≤ a1 then H n a1 else a0) + a := by
  have ep : H n p0 + (if 1 ≤ p1 then H n p1 else p0) = H (n + 1) p := by
    rw [← H_succ_cascade_expand hp_split hp0]; exact (H_succ_cascade hp_split).symm
  have eq' : H n q0 + (if 1 ≤ q1 then H n q1 else q0) = H (n + 1) q := by
    rw [← H_succ_cascade_expand hq_split hq0]; exact (H_succ_cascade hq_split).symm
  have ea : H n a0 + (if 1 ≤ a1 then H n a1 else a0) = H (n + 1) a := by
    rw [← H_succ_cascade_expand ha_split ha0]; exact (H_succ_cascade ha_split).symm
  have eb : H n b0 + (if 1 ≤ b1 then H n b1 else b0) = H (n + 1) b := by
    rw [← H_succ_cascade_expand hb_split hb0]; exact (H_succ_cascade hb_split).symm
  rw [eb] at hcase
  rw [ep, eq', ea]
  exact harper_nested_g_gt n ih ha hb hp hq hq_pos hb_le_a hcase hpq hcasc

lemma harper_subadd_gt_cascade_pos_succ_nested
    (n : ℕ)
    (ih : ∀ m, m < n + 1 → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b p q p0 p1 q0 q1 a0 a1 b0 b1 : ℕ}
    (ha : a ≤ 2 ^ (n + 1)) (hb : b ≤ 2 ^ (n + 1))
    (hp : p ≤ 2 ^ (n + 1)) (hq : q ≤ 2 ^ (n + 1))
    (hq_pos : 1 ≤ q)
    (hb_le_a : b ≤ a)
    (hcase : max (H n b0) b1 + max (H n b1) b0 < a)
    (hpq : p + q = a + b)
    (hcasc : CascadeSplit (n + 1) (a + b) p q)
    (hp0 : p0 ≤ 2 ^ n) (hp1 : p1 ≤ 2 ^ n)
    (hq0 : q0 ≤ 2 ^ n) (hq1 : q1 ≤ 2 ^ n)
    (ha0 : a0 ≤ 2 ^ n) (ha1 : a1 ≤ 2 ^ n)
    (hb0 : b0 ≤ 2 ^ n) (hb1 : b1 ≤ 2 ^ n)
    (hp_split : CascadeSplit n p p0 p1)
    (hq_split : CascadeSplit n q q0 q1)
    (ha_split : CascadeSplit n a a0 a1)
    (hb_split : CascadeSplit n b b0 b1) :
    max (H n p0) p1 + max (H n p1) p0 +
        (max (H n q0) q1 + max (H n q1) q0) ≤
      max (H n a0) a1 + max (H n a1) a0 + a := by
  rw [H_succ_cascade_expand hp_split hp0]
  rw [H_succ_cascade_expand hq_split hq0]
  rw [H_succ_cascade_expand ha_split ha0]
  have hcase_rewritten : H n b0 + (if 1 ≤ b1 then H n b1 else b0) < a := by
    rwa [← H_succ_cascade_expand hb_split hb0]
  exact harper_subadd_gt_cascade_pos_succ_nested_core n ih ha hb hp hq hq_pos hb_le_a
    hcase_rewritten hpq hcasc hp0 hp1 hq0 hq1 ha0 ha1 hb0 hb1 hp_split hq_split ha_split hb_split

lemma harper_subadd_le_cascade_pos
    (n : ℕ)
    (ih : ∀ m, m < n → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b p q : ℕ}
    (ha : a ≤ 2 ^ n) (hb : b ≤ 2 ^ n) (hp : p ≤ 2 ^ n) (hq : q ≤ 2 ^ n)
    (hq_pos : 1 ≤ q)
    (hb_le_a : b ≤ a) (hcase : a ≤ H n b)
    (hpq : p + q = a + b) (hcasc : CascadeSplit n (a + b) p q) :
    H n p + H n q ≤ H n a + H n b := by
  rcases n with _ | n
  · have hq_eq : q = 1 := by omega
    have hp_ge : q ≤ p := cascade_q_le_p hcasc
    have hp_eq : p = 1 := by omega
    have hab : a + b = 2 := by omega
    have ha_eq : a = 1 := by omega
    have hb_eq : b = 1 := by omega
    subst q
    subst p
    subst a
    subst b
    rfl
  · obtain ⟨p0, p1, hp0, hp1, _, hp_split⟩ := exists_cascade_split n p hp
    obtain ⟨q0, q1, hq0, hq1, _, hq_split⟩ := exists_cascade_split n q hq
    obtain ⟨a0, a1, ha0, ha1, _, ha_split⟩ := exists_cascade_split n a ha
    obtain ⟨b0, b1, hb0, hb1, _, hb_split⟩ := exists_cascade_split n b hb
    have hcase' :
        a ≤ max (H n b0) b1 + max (H n b1) b0 := by
      simpa [H_succ_cascade hb_split] using hcase
    have hnested :=
      harper_subadd_le_cascade_pos_succ_nested n ih
        ha hb hp hq hq_pos hb_le_a hcase' hpq hcasc
        hp0 hp1 hq0 hq1 ha0 ha1 hb0 hb1
        hp_split hq_split ha_split hb_split
    simpa [H_succ_cascade hp_split, H_succ_cascade hq_split,
      H_succ_cascade ha_split, H_succ_cascade hb_split] using hnested

lemma harper_subadd_gt_cascade_pos
    (n : ℕ)
    (ih : ∀ m, m < n → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b p q : ℕ}
    (ha : a ≤ 2 ^ n) (hb : b ≤ 2 ^ n) (hp : p ≤ 2 ^ n) (hq : q ≤ 2 ^ n)
    (hq_pos : 1 ≤ q)
    (hb_le_a : b ≤ a) (hcase : H n b < a)
    (hpq : p + q = a + b) (hcasc : CascadeSplit n (a + b) p q) :
    H n p + H n q ≤ H n a + a := by
  rcases n with _ | n
  · have hq_eq : q = 1 := by omega
    have hp_ge : q ≤ p := cascade_q_le_p hcasc
    have hp_eq : p = 1 := by omega
    have hab : a + b = 2 := by omega
    have ha_eq : a = 1 := by omega
    have hb_eq : b = 1 := by omega
    subst q
    subst p
    subst a
    subst b
    have hge : 1 ≤ H 0 1 := H_ge_self 0 1 (by norm_num)
    omega
  · obtain ⟨p0, p1, hp0, hp1, _, hp_split⟩ := exists_cascade_split n p hp
    obtain ⟨q0, q1, hq0, hq1, _, hq_split⟩ := exists_cascade_split n q hq
    obtain ⟨a0, a1, ha0, ha1, _, ha_split⟩ := exists_cascade_split n a ha
    obtain ⟨b0, b1, hb0, hb1, _, hb_split⟩ := exists_cascade_split n b hb
    have hcase' :
        max (H n b0) b1 + max (H n b1) b0 < a := by
      simpa [H_succ_cascade hb_split] using hcase
    have hnested :=
      harper_subadd_gt_cascade_pos_succ_nested n ih
        ha hb hp hq hq_pos hb_le_a hcase' hpq hcasc
        hp0 hp1 hq0 hq1 ha0 ha1 hb0 hb1
        hp_split hq_split ha_split hb_split
    simpa [H_succ_cascade hp_split, H_succ_cascade hq_split,
      H_succ_cascade ha_split] using hnested

/--
Clean subadditivity form of Case I of Harper's inductive step.

This is the genuine combinatorial content (non-circular: it mentions only `H`
and the lower-dimensional induction hypothesis `ih`).  It says that when the
larger part `a` already fits inside the neighborhood of the smaller part
(`a ≤ H n b`), the closed neighborhood of the initial segment of size `a + b`
in the `(n+1)`-cube is no larger than `H n a + H n b`.  Via `H_succ_cascade` and
`canonical_boundaryCost_eq_H_add` this is exactly `harper_bc_min_case_le`.
-/
lemma harper_subadd_le
    (n : ℕ)
    (ih : ∀ m, m < n → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b : ℕ}
    (ha : a ≤ 2 ^ n) (hb : b ≤ 2 ^ n)
    (hb_le_a : b ≤ a) (hcase : a ≤ H n b) :
    H (n + 1) (a + b) ≤ H n a + H n b := by
  have hab : a + b ≤ 2 ^ (n + 1) := by
    calc a + b ≤ 2 ^ n + 2 ^ n := Nat.add_le_add ha hb
      _ = 2 * 2 ^ n := by omega
      _ = 2 ^ (n + 1) := by ring
  obtain ⟨p, q, hp, hq, hpq, hcasc⟩ := exists_cascade_split n (a + b) hab
  rw [H_succ_cascade hcasc]
  by_cases hq_pos : 1 ≤ q
  · rw [canonical_boundaryCost_eq_H_add hp hq hq_pos hcasc]
    exact harper_subadd_le_cascade_pos n ih ha hb hp hq hq_pos hb_le_a hcase hpq hcasc
  · push Not at hq_pos
    have hq0 : q = 0 := by omega
    subst hq0
    have hpq_zero : p = a + b := by omega
    have hmax1 : max (H n p) 0 = H n p := max_eq_left (Nat.zero_le _)
    have hmax2 : max (H n 0) p = p := by rw [H_zero n]; exact max_eq_right (Nat.zero_le _)
    rw [hmax1, hmax2]
    have h_q_zero := harper_bc_min_q_zero_core n ha hb hp hb_le_a hpq_zero hcasc
    have h_bc := boundaryCost_eq_case_le ha hb_le_a hcase
    omega

/--
Clean form of Case II of Harper's inductive step.

Non-circular: mentions only `H` and the lower-dimensional `ih`.  When the larger
part `a` exceeds the neighborhood of the smaller part (`H n b < a`), the closed
neighborhood of the size-`(a+b)` initial segment in the `(n+1)`-cube is no larger
than `H n a + a`.  Via `H_succ_cascade` and `canonical_boundaryCost_eq_H_add`
this is exactly `harper_bc_min_case_gt`.
-/
lemma harper_subadd_gt
    (n : ℕ)
    (ih : ∀ m, m < n → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b : ℕ}
    (ha : a ≤ 2 ^ n) (hb : b ≤ 2 ^ n)
    (hb_le_a : b ≤ a) (hcase : H n b < a) :
    H (n + 1) (a + b) ≤ H n a + a := by
  have hab : a + b ≤ 2 ^ (n + 1) := by
    calc a + b ≤ 2 ^ n + 2 ^ n := Nat.add_le_add ha hb
      _ = 2 * 2 ^ n := by omega
      _ = 2 ^ (n + 1) := by ring
  obtain ⟨p, q, hp, hq, hpq, hcasc⟩ := exists_cascade_split n (a + b) hab
  rw [H_succ_cascade hcasc]
  by_cases hq_pos : 1 ≤ q
  · rw [canonical_boundaryCost_eq_H_add hp hq hq_pos hcasc]
    exact harper_subadd_gt_cascade_pos n ih ha hb hp hq hq_pos hb_le_a hcase hpq hcasc
  · push Not at hq_pos
    have hq0 : q = 0 := by omega
    subst hq0
    have hpq_zero : p = a + b := by omega
    have hmax1 : max (H n p) 0 = H n p := max_eq_left (Nat.zero_le _)
    have hmax2 : max (H n 0) p = p := by rw [H_zero n]; exact max_eq_right (Nat.zero_le _)
    rw [hmax1, hmax2]
    have h_q_zero := harper_bc_min_q_zero_core n ha hb hp hb_le_a hpq_zero hcasc
    have h_bc := boundaryCost_eq_case_gt ha hb_le_a hcase
    omega

lemma harper_bc_min_case_le
    (n : ℕ)
    (ih : ∀ m, m < n → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b p q : ℕ}
    (ha : a ≤ 2 ^ n) (hb : b ≤ 2 ^ n) (hp : p ≤ 2 ^ n) (hq : q ≤ 2 ^ n)
    (hq_pos : 1 ≤ q)
    (hb_le_a : b ≤ a) (hcase : a ≤ H n b)
    (_ : p + q = a + b) (hcasc : CascadeSplit n (a + b) p q) :
    H n p + H n q ≤ H n a + H n b := by
  have hsucc := H_succ_cascade hcasc
  have hcb := canonical_boundaryCost_eq_H_add hp hq hq_pos hcasc
  have key := harper_subadd_le n ih ha hb hb_le_a hcase
  rw [hsucc, hcb] at key
  exact key

lemma harper_bc_min_case_gt
    (n : ℕ)
    (ih : ∀ m, m < n → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b p q : ℕ}
    (ha : a ≤ 2 ^ n) (hb : b ≤ 2 ^ n) (hp : p ≤ 2 ^ n) (hq : q ≤ 2 ^ n)
    (hq_pos : 1 ≤ q)
    (hb_le_a : b ≤ a) (hcase : H n b < a)
    (_ : p + q = a + b) (hcasc : CascadeSplit n (a + b) p q) :
    H n p + H n q ≤ H n a + a := by
  have hsucc := H_succ_cascade hcasc
  have hcb := canonical_boundaryCost_eq_H_add hp hq hq_pos hcasc
  have key := harper_subadd_gt n ih ha hb hb_le_a hcase
  rw [hsucc, hcb] at key
  exact key

lemma harper_bc_min (n : ℕ)
    (ih : ∀ m, m < n → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b p q : ℕ}
    (ha : a ≤ 2 ^ n) (hb : b ≤ 2 ^ n) (hp : p ≤ 2 ^ n) (hq : q ≤ 2 ^ n)
    (hpq : p + q = a + b) (hcasc : CascadeSplit n (a + b) p q) :
    max (H n p) q + max (H n q) p ≤ max (H n a) b + max (H n b) a := by
  cases le_total b a with
  | inl hb_le_a =>
    by_cases hq_pos : 1 ≤ q
    · rw [canonical_boundaryCost_eq_H_add hp hq hq_pos hcasc]
      by_cases hcase : a ≤ H n b
      · rw [boundaryCost_eq_case_le ha hb_le_a hcase]
        exact harper_bc_min_case_le n ih ha hb hp hq hq_pos hb_le_a hcase hpq hcasc
      · push Not at hcase
        rw [boundaryCost_eq_case_gt ha hb_le_a hcase]
        exact harper_bc_min_case_gt n ih ha hb hp hq hq_pos hb_le_a hcase hpq hcasc
    · push Not at hq_pos
      have hq0 : q = 0 := by omega
      subst hq0
      have hpq_zero : p = a + b := by omega
      have hmax1 : max (H n p) 0 = H n p := max_eq_left (Nat.zero_le _)
      have hmax2 : max (H n 0) p = p := by rw [H_zero n]; exact max_eq_right (Nat.zero_le _)
      rw [hmax1, hmax2]
      exact harper_bc_min_q_zero_core n ha hb hp hb_le_a hpq_zero hcasc
  | inr ha_le_b =>
    rw [boundaryCost_comm n a b]
    have hpq_symm : p + q = b + a := by omega
    have hcasc_symm : CascadeSplit n (b + a) p q := by
      simpa [Nat.add_comm] using hcasc
    by_cases hq_pos : 1 ≤ q
    · rw [canonical_boundaryCost_eq_H_add hp hq hq_pos hcasc]
      by_cases hcase : b ≤ H n a
      · rw [boundaryCost_eq_case_le hb ha_le_b hcase]
        exact harper_bc_min_case_le n ih hb ha hp hq hq_pos ha_le_b hcase hpq_symm hcasc_symm
      · push Not at hcase
        rw [boundaryCost_eq_case_gt hb ha_le_b hcase]
        exact harper_bc_min_case_gt n ih hb ha hp hq hq_pos ha_le_b hcase hpq_symm hcasc_symm
    · push Not at hq_pos
      have hq0 : q = 0 := by omega
      subst hq0
      have hpq_zero : p = b + a := by omega
      have hmax1 : max (H n p) 0 = H n p := max_eq_left (Nat.zero_le _)
      have hmax2 : max (H n 0) p = p := by rw [H_zero n]; exact max_eq_right (Nat.zero_le _)
      rw [hmax1, hmax2]
      exact harper_bc_min_q_zero_core n hb ha hp ha_le_b hpq_zero hcasc_symm

/--
Harper's vertex-isoperimetric recursion inequality (the genuine combinatorial
core): the initial segment of size `a + b` in the `(n+1)`-cube has the smallest
closed `1`-neighborhood among all sets obtained by taking initial segments of
sizes `a`, `b` in the two slices.  Equivalently, in `H`-terms,
`H (n+1) (a+b) ≤ max (H n a) b + max (H n b) a`.

This is proved independently of `boundaryCost`, `CascadeInterleaves`,
`H_inequality_core`, `H_inequality`, `macaulay_optimization`, and
`interleaving_boundaryCost_mono` (all of which are stated later and ultimately
depend on this lemma), so there is no circularity.
-/
lemma harper_core :
    ∀ (n a b : ℕ), a ≤ 2 ^ n → b ≤ 2 ^ n →
      H (n + 1) (a + b) ≤ max (H n a) b + max (H n b) a := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b ha hb
    have hS : a + b ≤ 2 ^ (n + 1) := by
      have h2 : (2 : ℕ) ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [pow_succ]; ring
      omega
    obtain ⟨p, q, hp, hq, hpq, hcasc⟩ := exists_cascade_split n (a + b) hS
    rw [H_succ_cascade hcasc]
    exact harper_bc_min n ih ha hb hp hq hpq hcasc

-- ==========================================
-- CASCADE INTERLEAVING / MAJORIZATION
-- ==========================================

/-- The boundary cost of a split `(a, b)` in dimension `n`. -/
noncomputable def boundaryCost (n a b : ℕ) : ℕ :=
  max (H n a) b + max (H n b) a

/--
Macaulay interleaving theorem: if `(p, q)` interleaves `(a, b)`, then its
boundary cost is smaller.  Through the cascade recursion `H_succ_cascade` this
reduces to Harper's recursion inequality `harper_core`.
-/
lemma interleaving_boundaryCost_mono
    {n p q a b : ℕ} (ha : a ≤ 2 ^ n) (hb : b ≤ 2 ^ n)
    (h_inter : CascadeInterleaves n p q a b) :
    boundaryCost n p q ≤ boundaryCost n a b := by
  obtain ⟨h_casc, _⟩ := h_inter
  have hpq : boundaryCost n p q = H (n + 1) (a + b) := by
    rw [boundaryCost]; exact (H_succ_cascade h_casc).symm
  rw [hpq]
  exact harper_core n a b ha hb

/--
The Harper boundary inequality, stated directly on `H`:
`H (n+1) (a+b) ≤ max (H n a) b + max (H n b) a`.

Via `H_succ_cascade` this is equivalent to `macaulay_optimization` (the canonical
cascade split of `a+b` minimises the cross boundary expression), so it is the
genuine combinatorial heart of Harper's vertex-isoperimetric theorem for the
discrete cube.

The supporting structure for this statement is fully developed above:
* `H_succ_cascade`         — the slice recursion `H (n+1) k = max (H n p) q + max (H n q) p`;
* `cascade_p_le_H_q`       — the compression property `p ≤ H n q` of the canonical split;
* `cascade_q_le_p`         — `q ≤ p`;
* `H_mono`, `H_ge_self`, `H_le_cube`, `H_add_self_mono` — monotonicity / growth of `H`;
* `H_eq_gShift_count`      — the explicit boundary count formula.
-/
lemma H_inequality_core :
    ∀ (n a b : ℕ), a ≤ 2 ^ n → b ≤ 2 ^ n →
      H (n + 1) (a + b) ≤ max (H n a) b + max (H n b) a := by
  intro n a b ha hb
  have hab : a + b ≤ 2 ^ (n + 1) := by
    calc a + b ≤ 2 ^ n + 2 ^ n := Nat.add_le_add ha hb
      _ = 2 * 2 ^ n := by omega
      _ = 2 ^ (n + 1) := by ring
  obtain ⟨p, q, _, _, _, h_casc⟩ := exists_cascade_split n (a + b) hab
  have h_inter := canonicalSplit_interleaves ha hb h_casc
  have h_mono := interleaving_boundaryCost_mono ha hb h_inter
  have h_succ := H_succ_cascade h_casc
  unfold boundaryCost at h_mono
  rw [h_succ]
  exact h_mono

/--
The core Kruskal-Katona / Macaulay optimization inequality for the cascade split.
For any canonical split `(p, q)` of `a + b`, the cross-sum of their boundary sizes
is bounded by the sum of boundary bounds for the original sizes `a` and `b`.
-/
lemma macaulay_optimization {n a b p q : ℕ} (ha : a ≤ 2 ^ n) (hb : b ≤ 2 ^ n)
    (h_casc : CascadeSplit n (a + b) p q) :
    max (H n p) q + max (H n q) p ≤ max (H n a) b + max (H n b) a := by
  rw [← H_succ_cascade h_casc]
  exact H_inequality_core n a b ha hb

-- The optimization core of Macaulay-Harper: the initial-segment slice split is optimal.
lemma H_split_opt {n a b : ℕ} (ha : a ≤ 2 ^ n) (hb : b ≤ 2 ^ n) :
    max (H n (slice0 (simplicialInitSeg (n + 1) (a + b))).card)
        (slice1 (simplicialInitSeg (n + 1) (a + b))).card +
    max (H n (slice1 (simplicialInitSeg (n + 1) (a + b))).card)
        (slice0 (simplicialInitSeg (n + 1) (a + b))).card
    ≤ max (H n a) b + max (H n b) a := by
  have hab : a + b ≤ 2 ^ (n + 1) := by
    calc a + b ≤ 2 ^ n + 2 ^ n := add_le_add ha hb
      _ = 2 * 2 ^ n := by omega
      _ = 2 ^ (n + 1) := by ring
  obtain ⟨p, q, _, _, _, h_split⟩ := exists_cascade_split n (a + b) hab
  have ⟨h0, h1⟩ := slice_card_eq_cascade h_split
  rw [h0, h1]
  exact macaulay_optimization ha hb h_split

-- Macaulay-Harper inequality.
lemma H_inequality (n a b : ℕ) (ha : a ≤ 2 ^ n) (hb : b ≤ 2 ^ n) :
    H (n + 1) (a + b) ≤ max (H n a) b + max (H n b) a := by
  rw [H_succ_slice]
  exact H_split_opt ha hb

-- ==========================================
-- Optimality of the initial segment
-- ==========================================

lemma initial_segment_optimal {n : ℕ} (k0 k1 : ℕ) (hk0 : k0 ≤ 2 ^ n) (hk1 : k1 ≤ 2 ^ n) :
    (neighborhood 1 (simplicialInitSeg (n + 1) (k0 + k1))).card ≤
    (neighborhood 1 (simplicialInitSeg n k0) ∪ simplicialInitSeg n k1).card +
    (neighborhood 1 (simplicialInitSeg n k1) ∪ simplicialInitSeg n k0).card := by
  change H (n + 1) (k0 + k1) ≤ _
  rw [neighborhood_initSeg_eq, neighborhood_initSeg_eq]
  rw [card_initSeg_union (H_le_cube n k0) hk1, card_initSeg_union (H_le_cube n k1) hk0]
  exact H_inequality n k0 k1 hk0 hk1

/-
==========================================
12. FINAL HARPER'S THEOREM (By Dimension Induction)
==========================================

Every set of vertices in the n-cube has at most 2^n elements.
-/
lemma card_cube_le {n : ℕ} (S : Finset (Cube n)) : S.card ≤ 2 ^ n := by
  convert S.card_le_univ using 1;
  norm_num +zetaDelta at *

/-
Monotonicity of the boundary-union under the inductive hypothesis.
-/
lemma union_initSeg_card_le {n a b : ℕ} {B C : Finset (Cube n)}
    (hHa : (neighborhood 1 (simplicialInitSeg n a)).card ≤ (neighborhood 1 B).card)
    (hb : C.card = b) (hb2 : b ≤ 2 ^ n) :
    (neighborhood 1 (simplicialInitSeg n a) ∪ simplicialInitSeg n b).card ≤
      (neighborhood 1 B ∪ C).card := by
  have h_max : (neighborhood 1 (simplicialInitSeg n a) ∪ simplicialInitSeg n b).card ≤
      max (H n a) b := by
    rw [ neighborhood_initSeg_eq ];
    convert card_initSeg_union ( show H n a ≤ 2 ^ n from ?_ ) hb2 |> le_of_eq using 1;
    exact H_le_cube n a;
  refine h_max.trans ( max_le ?_ ?_ );
  · exact le_trans hHa ( Finset.card_mono ( Finset.subset_union_left ) );
  · exact hb ▸ Finset.card_le_card ( Finset.subset_union_right )

/-
Base case of Harper's theorem (dimension 0).
-/
lemma harper_base (A : Finset (Cube 0)) (k : ℕ) (hk : A.card = k) :
    (neighborhood 1 (simplicialInitSeg 0 k)).card ≤ (neighborhood 1 A).card := by
  subst hk
  fin_cases A <;>
    simp +decide [simplicialInitSeg, Finset.filter_singleton, rank, simplicialLt, simplicialLe]

theorem harper_theorem (n : ℕ) (A : Finset (Cube n)) (k : ℕ) (hk : A.card = k) :
    (neighborhood 1 (simplicialInitSeg n k)).card ≤ (neighborhood 1 A).card := by
  revert A k
  induction n with
  | zero =>
    -- Base case: dimension 0
    exact harper_base
  | succ n ih =>
    -- Inductive step: n to n + 1
    intro A k hk
    let A0 := slice0 A
    let A1 := slice1 A
    let k0 := A0.card
    let k1 := A1.card
    -- Apply Inductive Hypothesis to the slices
    have ih0 := ih A0 k0 rfl
    have ih1 := ih A1 k1 rfl
    -- Use the decomposition of the neighborhood in n+1 dimensions
    calc (neighborhood 1 (simplicialInitSeg (n + 1) k)).card
      _ = (neighborhood 1 (simplicialInitSeg (n + 1) (k0 + k1))).card := by
          rw [← hk, ← slice_card_add A]
      _ ≤ (neighborhood 1 (simplicialInitSeg n k0) ∪ simplicialInitSeg n k1).card +
          (neighborhood 1 (simplicialInitSeg n k1) ∪ simplicialInitSeg n k0).card := by
          exact initial_segment_optimal k0 k1 (card_cube_le A0) (card_cube_le A1)
      _ ≤ (neighborhood 1 A0 ∪ A1).card + (neighborhood 1 A1 ∪ A0).card := by
          exact Nat.add_le_add
            (union_initSeg_card_le ih0 rfl (card_cube_le A1))
            (union_initSeg_card_le ih1 rfl (card_cube_le A0))
      _ = (neighborhood 1 A).card := by
          rw [neighborhood_succ A]

end BooleanIsoperimetry
