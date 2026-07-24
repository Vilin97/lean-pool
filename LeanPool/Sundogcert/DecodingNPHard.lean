/-
Copyright (c) 2026 Humiliati. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Humiliati
-/

import Mathlib.Data.Matrix.Mul
import Mathlib.InformationTheory.Hamming
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import LeanPool.Sundogcert.Certificate

/-!
  Sundogcert/DecodingNPHard.lean — the DEDUCTIVE CORE of NP-hardness of SYNDROME DECODING
  over GF(2), via the reduction from EXACT-COVER-BY-3-SETS (EC3S / X3C).
  (Lean 4 / mathlib v4.30.0.  Berlekamp–McEliece–van Tilborg route.)

  WHAT THIS FILE PROVES (the deductive core — MILESTONES 1 AND 2 BOTH DONE):
    * the reduction is laid out exactly as designed: an EC3S instance `(c : Fin s → Finset X)`
      becomes a parity-check matrix `Hmat c` over `ZMod 2` with target syndrome `allOnes`, and a
      bounded-weight decoding question `Decodes c q`.
    * the KEY CONNECTION (`connection`): for the indicator error `eOf T`, the syndrome
      `Hmat c *ᵥ eOf T` is the mod-2 cast of the cover count — so "syndrome = allOnes" is exactly
      "every point is covered an ODD number of times".  An exact cover (count = 1) is odd.
    * the DOUBLE-COUNT (`incidence_double_count`): `∑ i∈T, (c i).card = ∑ x, coverCount c T x`,
      which with `hc` (each 3-set has card 3) and `hX` (|X| = 3q) pins `T.card = q`.
    * `reduction_forward` (PROVED): an exact cover yields a weight-`≤ q` decoding witness.
    * `reduction_backward` (PROVED, MILESTONE 2): a weight-`≤ q` decoding witness MUST be a 0/1
      exact-cover indicator.  Over `ZMod 2` the error is 0/1, so its support `T` has `eOf T = e`
      and `|T| ≤ q`; "syndrome = allOnes" forces every cover count ODD hence `≥ 1`, and the
      double-count `∑ coverCount = 3|T| ≥ |X| = 3q` pins `|T| = q`; equal sums with the pointwise
      `≥ 1` bound force every cover count `= 1` — an exact cover.
    * `reduction_iff` (UNCONDITIONAL): the full `X3C c ↔ Decodes c q`, both directions now
      machine-checked (`⟨reduction_forward, reduction_backward⟩`) — NO hypothesis, NO `sorry`,
      NO `axiom`.  The reduction's correctness is FULLY proved; only the COMPLEXITY WRAPPING
      remains the named imported wall (below).

  WIRE-IN TO THE CERTIFICATE.  `Decodes c q` is EXACTLY the decision form of
  `Sundog.Certificate.CertWall.minCosetWeight (Hmat c) allOnes ≤ q` — we use the EXISTENTIAL
  form (∃ e, Hmat *ᵥ e = allOnes ∧ hammingNorm e ≤ q) rather than `minCosetWeight ≤ q` to dodge
  the `sInf`-of-empty-coset pitfall (`safe_iff_minCosetWeight_le` in CertWall is the bridge when
  the coset is nonempty).  So this reduction LANDS on the certificate's imported hardness wall:
  CertWall's `minCosetWeight` is the very quantity an EC3S→decoding reduction makes NP-hard.

  THE IMPORTED WALL (named, NOT proved — mathlib has no complexity framework):
    * the NP complexity class itself;
    * poly-time-ness of this reduction (it is visibly local, but "polynomial" is unformalized);
    * EC3S's own NP-hardness (Karp 1972).
  STANDING LIMIT.  With milestone 2 done, this proves "decoding is NP-hard CONDITIONAL on P≠NP" —
  hardness is never absolute, and this limit is UNCHANGED by completing the backward direction.
  What IS proved (now in full) is that bounded-weight GF(2) decoding is exactly as hard as a
  canonical NP-hard problem (EC3S): the reduction correctness `X3C c ↔ Decodes c q` is fully
  machine-checked; only the complexity wrapping above stays imported.

  CORRECTNESS NOTE (a wrong reduction is the failure mode).  Decoding is over GF(2), so
  `H *ᵥ e` is a MOD-2 (XOR) sum.  EC3S is the right source problem because GF(2) is the natural
  operation for COVERING (odd-cover) — unlike subset-sum, which needs integer carries and is WRONG
  over GF(2).  The connection lemma makes the odd-cover ⇔ syndrome=allOnes equivalence explicit.
-/

open Matrix Finset

namespace Sundog.DecodingNPHard

variable {X : Type*} [Fintype X] [DecidableEq X]
variable {s : ℕ} (c : Fin s → Finset X) (q : ℕ)

/-! ### The reduction's definitions. -/

/-- `coverCount c T x` — how many SELECTED 3-sets (indices in `T`) contain the point `x`. -/
def coverCount (T : Finset (Fin s)) (x : X) : ℕ :=
  (T.filter (fun i => x ∈ c i)).card

/-- `T` is an **exact cover**: every point is covered by exactly one selected set. -/
def IsExactCover (T : Finset (Fin s)) : Prop := ∀ x : X, coverCount c T x = 1

/-- **EC3S / X3C**: an exact cover exists.  (The source NP-hard problem; Karp 1972.) -/
def X3C : Prop := ∃ T : Finset (Fin s), IsExactCover c T

/-- The parity-check matrix of the reduction: column `i` is the GF(2) indicator of the 3-set
    `c i`.  Rows are points of `X`, columns are the `s` sets. -/
def Hmat : Matrix X (Fin s) (ZMod 2) := Matrix.of (fun x i => if x ∈ c i then 1 else 0)

/-- The all-ones target syndrome — "cover every point". -/
def allOnes : X → ZMod 2 := Function.const X 1

/-- **The decoding question** (decision form of `minCosetWeight (Hmat c) allOnes ≤ q`): is there a
    GF(2) error pattern `e` of weight `≤ q` whose syndrome is the all-ones vector?  Existential
    form, NOT `minCosetWeight ≤ q`, to dodge the `sInf`-of-empty-coset pitfall. -/
def Decodes : Prop :=
  ∃ e : Fin s → ZMod 2, Hmat c *ᵥ e = allOnes ∧ hammingNorm e ≤ q

/-- The 0/1 indicator error pattern of a selection `T` (a column-selection of `Hmat`). -/
def eOf (T : Finset (Fin s)) : Fin s → ZMod 2 :=
  fun i => if i ∈ T then 1 else 0

/-! ### The KEY CONNECTION — syndrome of `eOf T` is the mod-2 cast of the cover count. -/

omit [Fintype X] in
/-- For each point `x`, the syndrome coordinate `(Hmat c *ᵥ eOf T) x` equals the mod-2 cast of
    `coverCount c T x`: each selected set containing `x` contributes a `1`, all summed in `ZMod 2`,
    so the parity of the cover count is exactly the syndrome bit. -/
theorem syndrome_eq_coverCount_cast (T : Finset (Fin s)) (x : X) :
    (Hmat c *ᵥ eOf T) x = ((coverCount c T x : ℕ) : ZMod 2) := by
  unfold Hmat eOf coverCount
  -- `(M *ᵥ v) x = ∑ i, M x i * v i`.
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
  -- RHS: cast of `#(T.filter (x ∈ c i))` = `∑ i ∈ T, ite (x ∈ c i) 1 0`.
  rw [card_filter]
  push_cast
  -- LHS: `∑ i, ite(x∈c i) 1 0 * ite(i∈T) 1 0`; fold to `∑ i, ite(i∈T) (ite(x∈c i) 1 0) 0`.
  rw [show (∑ i, (if x ∈ c i then (1 : ZMod 2) else 0) * (if i ∈ T then 1 else 0))
        = ∑ i, (if i ∈ T then (if x ∈ c i then (1 : ZMod 2) else 0) else 0) from
      Finset.sum_congr rfl (fun i _ => by by_cases h : i ∈ T <;> simp [h])]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

omit [Fintype X] [DecidableEq X] in
/-- The Hamming weight of the indicator error equals the size of the selection. -/
theorem hammingNorm_eOf (T : Finset (Fin s)) : hammingNorm (eOf T) = T.card := by
  unfold hammingNorm eOf
  -- the support `{i | (if i ∈ T then 1 else 0) ≠ 0}` is exactly `T`.
  have hset : (Finset.univ.filter (fun i => (if i ∈ T then (1 : ZMod 2) else 0) ≠ 0)) = T := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hiT : i ∈ T <;> simp [hiT]
  rw [hset]

omit [Fintype X] in
/-- An EXACT cover makes the syndrome the all-ones vector: count `1` is odd, so its mod-2 cast is
    `1` at every point. -/
theorem syndrome_eOf_eq_allOnes (T : Finset (Fin s)) (hT : IsExactCover c T) :
    Hmat c *ᵥ eOf T = allOnes := by
  funext x
  rw [syndrome_eq_coverCount_cast, hT x]
  simp only [allOnes, Function.const_apply, Nat.cast_one]

/-! ### The DOUBLE-COUNT — incidence count, two ways. -/

/-- **Incidence double-count.**  Summing set-sizes over selected sets equals summing cover-counts
    over points: both count the incidence pairs `(i, x)` with `i ∈ T` and `x ∈ c i`.  Proved by
    `Finset.sum_comm` after writing each card as a sum of `0/1` indicators. -/
theorem incidence_double_count (T : Finset (Fin s)) :
    (∑ i ∈ T, (c i).card) = ∑ x : X, coverCount c T x := by
  unfold coverCount
  -- LHS: `#(c i) = ∑ x, ite (x ∈ c i) 1 0` via `filter_univ_mem` + `card_filter`.
  have hL : ∀ i, (c i).card = ∑ x : X, ite (x ∈ c i) 1 0 := by
    intro i
    conv_lhs => rw [← Finset.filter_univ_mem (c i)]
    rw [card_filter]
  -- RHS: `#(T.filter (x ∈ c i)) = ∑ i∈T, ite (x ∈ c i) 1 0` via `card_filter`.
  simp only [hL, card_filter]
  -- both sides are `∑ ∑ ite (x ∈ c i) 1 0`; swap the order.
  exact Finset.sum_comm

/-- With each 3-set of card `3`, an exact cover of an `X` of size `3q` selects exactly `q` sets.
    `3 * T.card = ∑ i∈T, 3 = ∑ i∈T, (c i).card = ∑ x, coverCount = ∑ x, 1 = |X| = 3q`. -/
theorem exactCover_card_eq (hc : ∀ i, (c i).card = 3) (hX : Fintype.card X = 3 * q)
    (T : Finset (Fin s)) (hT : IsExactCover c T) : T.card = q := by
  have hsum : (∑ i ∈ T, (c i).card) = 3 * T.card := by
    rw [Finset.sum_congr rfl (fun i _ => hc i), Finset.sum_const, smul_eq_mul]
    ring
  have hcov : (∑ x : X, coverCount c T x) = Fintype.card X := by
    rw [Finset.sum_congr rfl (fun x _ => hT x), Finset.sum_const, smul_eq_mul,
      mul_one, Finset.card_univ]
  rw [incidence_double_count, hcov, hX] at hsum
  omega

/-! ### THE THEOREMS. -/

/-- **FORWARD (PROVED).**  An EC3S exact cover yields a bounded-weight GF(2) decoding witness:
    the column-selection `eOf T` has syndrome `allOnes` (connection lemma) and weight
    `T.card = q ≤ q` (double-count). -/
theorem reduction_forward (hc : ∀ i, (c i).card = 3) (hX : Fintype.card X = 3 * q)
    (h : X3C c) : Decodes c q := by
  obtain ⟨T, hT⟩ := h
  refine ⟨eOf T, syndrome_eOf_eq_allOnes c T hT, ?_⟩
  rw [hammingNorm_eOf, exactCover_card_eq c q hc hX T hT]

/-- **BACKWARD (PROVED, MILESTONE 2).**  A bounded-weight GF(2) decoding witness MUST be a 0/1
    exact-cover indicator.  Over `ZMod 2` every coordinate of `e` is `0` or `1`, so for its support
    `T := {i | e i ≠ 0}` we have `e = eOf T` and `|T| = hammingNorm e ≤ q`.  "Syndrome = allOnes"
    casts each cover count to `1` in `ZMod 2`, forcing it ODD hence `≥ 1`; the double-count plus
    `hc` gives `∑ coverCount = 3|T|`, and pointwise `≥ 1` summed gives `∑ coverCount ≥ |X| = 3q`,
    pinning `|T| = q`.  Finally equal sums against the pointwise `≥ 1` bound force every cover count
    to be EXACTLY `1` — an exact cover. -/
theorem reduction_backward (hc : ∀ i, (c i).card = 3) (hX : Fintype.card X = 3 * q)
    (h : Decodes c q) : X3C c := by
  obtain ⟨e, hsyn, hwt⟩ := h
  classical
  -- (A) the support T, and e = eOf T (over ZMod 2 every coord is 0 or 1):
  set T : Finset (Fin s) := Finset.univ.filter (fun i => e i ≠ 0) with hTdef
  have hz : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  have he : e = eOf T := by
    funext i; unfold eOf
    by_cases hi : e i = 0
    · simp [hi, hTdef]
    · have h1 : e i = 1 := (hz (e i)).resolve_left hi
      simp [h1, hTdef]
  -- (B) |T| ≤ q via hammingNorm:
  have hTle : T.card ≤ q := by rw [← hammingNorm_eOf T, ← he]; exact hwt
  -- (C) each cover count is ≥ 1 (syndrome bit 1 ⟹ count odd ⟹ nonzero):
  have hge1 : ∀ x : X, 1 ≤ coverCount c T x := by
    intro x
    have hcast : ((coverCount c T x : ℕ) : ZMod 2) = 1 := by
      rw [← syndrome_eq_coverCount_cast c T x, ← he, hsyn]; rfl
    rcases Nat.eq_zero_or_pos (coverCount c T x) with h0 | hpos
    · exfalso; rw [h0, Nat.cast_zero] at hcast; exact (by decide : (0 : ZMod 2) ≠ 1) hcast
    · exact hpos
  -- (D) double-count + hc ⟹ ∑ coverCount = 3 * |T|:
  have hsum : (∑ x : X, coverCount c T x) = 3 * T.card := by
    rw [← incidence_double_count c T]
    rw [Finset.sum_congr rfl (fun i _ => hc i), Finset.sum_const, smul_eq_mul]; ring
  -- (E) pointwise ≥ 1 ⟹ ∑ coverCount ≥ |X| = 3q ⟹ |T| ≥ q ⟹ |T| = q:
  have hlow : Fintype.card X ≤ ∑ x : X, coverCount c T x := by
    have hone : (∑ _x : X, (1 : ℕ)) ≤ ∑ x : X, coverCount c T x :=
      Finset.sum_le_sum (fun x _ => hge1 x)
    simpa [Finset.sum_const, Finset.card_univ] using hone
  have hTcard : T.card = q := by rw [hsum, hX] at hlow; omega
  -- (F) equal sums + pointwise ≥ ⟹ pointwise = 1 (the exact cover):
  refine ⟨T, fun x => ?_⟩
  have hsumEq : (∑ _x : X, (1 : ℕ)) = ∑ x : X, coverCount c T x := by
    rw [Finset.sum_const, Finset.card_univ, hX, hsum, hTcard]; ring
  have hpt := (Finset.sum_eq_sum_iff_of_le (fun x _ => hge1 x)).mp hsumEq
  exact (hpt x (Finset.mem_univ x)).symm

/-- **THE REDUCTION IFF** (UNCONDITIONAL).  Both directions are now machine-checked: forward is the
    PROVED `reduction_forward`, backward is the PROVED `reduction_backward` (milestone 2).  This is
    the full EC3S ⇔ bounded-weight-GF(2)-decoding equivalence — the reduction's correctness, NO
    hypothesis, NO `sorry`, NO `axiom` — landing on CertWall's `minCosetWeight` imported wall.  Only
    the COMPLEXITY WRAPPING (NP class, poly-time-ness, EC3S's own NP-hardness, Karp 1972) stays the
    named imported wall; the standing limit (NP-hard CONDITIONAL on P≠NP) is unchanged. -/
theorem reduction_iff (hc : ∀ i, (c i).card = 3) (hX : Fintype.card X = 3 * q) :
    X3C c ↔ Decodes c q :=
  ⟨reduction_forward c q hc hX, reduction_backward c q hc hX⟩

/-! ### Axiom audit on the two headline theorems (expect propext/Classical.choice/Quot.sound). -/


end Sundog.DecodingNPHard
