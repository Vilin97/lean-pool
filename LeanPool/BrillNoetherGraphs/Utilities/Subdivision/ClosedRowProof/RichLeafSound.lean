/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.ClosedRowProof.RichLeafChecks
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.DegeneratePiecewiseInterpolation
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.DegenerateAffinePositionMultiBreak
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.PiecewiseBlockDecoder

/-!
# Semantic bridge ingredients for rich row-proof leaves

This module deliberately does not yet add a `PTree` constructor.  It records
the pointwise arithmetic facts which turn the executable W1--W5 receipts into
closed-face data.  Keeping these facts independent of the tree is useful: a
rich leaf is evaluated at a single integral point before its block endpoints
are decoded into a `DegSpec.PiecewiseData` and its chips into a weighted
divisor.

The remaining assembly is not a matter of weakening the checker.  It needs a
finite-list decoder which supplies `PiecewiseData.covers`,
`PiecewiseData.ownsInterval`, and `PiecewiseData.balance`, together with the
two residual comparison lemmas documented at the end of this file.
-/

@[expose] public section

namespace Utilities.Subdivision.ClosedRowProof

open Utilities

open MarkedGraphs.Certificate
open Utilities.Certificate
open Utilities.Certificate.ContractionForestCensusGeneral

namespace RichWitness

variable {m n p : ℕ}

/-- Evaluation of a named point.  This is kept as an integer: W1 first proves
nonnegativity, after which the lowerer may take `toNat` to obtain a path
offset. -/
def pointValue (w : RichWitness) (x : List ℤ) (a e i : ℕ) : ℤ :=
  eval (w.point a e i) x

/-- Evaluation of a declared block length. -/
def blockLengthValue (w : RichWitness) (x : List ℤ) (a e i : ℕ) : ℤ :=
  eval (w.blockLength a e i) x

@[simp] theorem pointValue_zero (w : RichWitness) (x : List ℤ) (a e : ℕ) :
    w.pointValue x a e 0 = 0 := by
  simp [pointValue, point]

theorem blockLengthValue_eq (w : RichWitness) (x : List ℤ) (a e i : ℕ) :
    w.blockLengthValue x a e i =
      eval (w.block a e i).endForm x - w.pointValue x a e i := by
  simp only [blockLengthValue, blockLength, eval_subForm, pointValue]

/-- Consecutive named points differ by the length of the intervening block.
This is the arithmetic form of the RPF convention that point `i + 1` is the
right endpoint of block `i`. -/
theorem pointValue_succ_sub (w : RichWitness) (x : List ℤ) (a e i : ℕ) :
    w.pointValue x a e (i + 1) - w.pointValue x a e i =
      w.blockLengthValue x a e i := by
  rw [blockLengthValue_eq]
  simp only [pointValue, point]
  rw [ite_eq_right (Nat.succ_ne_zero _)]
  rfl

/-- W1 monotonicity receipts make the evaluated named points weakly ordered.
The index bounds are explicit because a rich block list is only constrained
on its declared finite prefix. -/
theorem pointValue_mono_of_lengths (w : RichWitness) (x : List ℤ) (a e k : ℕ)
    (hLength : ∀ i < k, 0 ≤ w.blockLengthValue x a e i) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ k) :
    w.pointValue x a e i ≤ w.pointValue x a e j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hjle ih =>
      have hjk : j < k := by omega
      have hStep := w.pointValue_succ_sub x a e j
      have hNonneg := hLength j hjk
      have hNext : w.pointValue x a e j ≤ w.pointValue x a e (j + 1) := by
        omega
      exact (ih (by omega)).trans hNext

/-- Every named point through the final endpoint is nonnegative.  This is the
integer fact needed before W1 endpoints can be decoded with `Int.toNat`. -/
theorem pointValue_nonneg_of_lengths (w : RichWitness) (x : List ℤ) (a e k i : ℕ)
    (hLength : ∀ j < k, 0 ≤ w.blockLengthValue x a e j) (hi : i ≤ k) :
    0 ≤ w.pointValue x a e i := by
  have hZero := w.pointValue_zero x a e
  rw [← hZero]
  exact w.pointValue_mono_of_lengths x a e k hLength (Nat.zero_le _) hi

/-- W1's final endpoint equality bounds every named point by the slot length. -/
theorem pointValue_le_of_lengths_last (w : RichWitness) (x : List ℤ)
    (a e k L i : ℕ) (hLength : ∀ j < k, 0 ≤ w.blockLengthValue x a e j)
    (hLast : w.pointValue x a e k = L) (hi : i ≤ k) :
    w.pointValue x a e i ≤ L := by
  rw [← hLast]
  exact w.pointValue_mono_of_lengths x a e k hLength hi le_rfl

/-- A positive evaluated named point separates all earlier named points from
the tail.  This is the arithmetic W1 bridge used to bound a collapsed prefix. -/
theorem pointValue_eq_zero_lt_of_pointValue_pos (w : RichWitness)
    (x : List ℤ) (a e k i s : ℕ)
    (hLength : ∀ j < k, 0 ≤ w.blockLengthValue x a e j)
    (hi : i ≤ k) (hZero : w.pointValue x a e i = 0)
    (hPos : 0 < w.pointValue x a e s) : i < s := by
  by_contra hNot
  have hSI : s ≤ i := Nat.le_of_not_gt hNot
  have hMono := w.pointValue_mono_of_lengths x a e k hLength hSI hi
  rw [hZero] at hMono
  omega

/-- The head-side counterpart: a named point strictly before the slot length
separates every later point at the head. -/
theorem lt_of_pointValue_eq_length_of_pointValue_lt (w : RichWitness)
    (x : List ℤ) (a e k L i s : ℕ)
    (hLength : ∀ j < k, 0 ≤ w.blockLengthValue x a e j)
    (hs : s ≤ k) (hLengthValue : w.pointValue x a e i = L)
    (hLt : w.pointValue x a e s < L) : s < i := by
  by_contra hNot
  have hIS : i ≤ s := Nat.le_of_not_gt hNot
  have hMono := w.pointValue_mono_of_lengths x a e k hLength hIS hs
  rw [hLengthValue] at hMono
  omega

/-- A strict W1 separation receipt is genuinely strict at every integral
point satisfying its context. -/
theorem positiveCheck_sound {c : Cert} {Γ : Context} {f : Form}
    (hcheck : positiveCheck c Γ f = true) {x : List ℤ} (hx : Γ.Holds x) :
    0 < eval f x := by
  have h := Cert.check_sound hcheck hx
  rw [eval_subForm] at h
  have hone : eval ([1] : Form) x = 1 := by simp [eval, dot]
  rw [hone] at h
  omega

/-! ## W3 shape facts

The physical chip decoder needs only the two structural consequences of W3:
every raw slot index is genuine, and for every anchor a chip is syntactically
one of that slot's named interior endpoints.  The latter becomes an equality
of evaluated positions through `eval_eq_of_formEq`. -/

theorem slot_lt_of_w3Checks (w : RichWitness) (core : ExplicitPotential.Core n p)
    (hW3 : w.w3Checks core = true) {chip : ℕ × Form × ℤ} (hchip : chip ∈ w.chips) :
    chip.1 < p := by
  simp only [w3Checks, Bool.and_eq_true] at hW3
  exact decide_eq_true_eq.mp (List.all_eq_true.mp hW3.1 chip hchip)

theorem chip_named_of_w3Checks (w : RichWitness) (core : ExplicitPotential.Core n p)
    (hW3 : w.w3Checks core = true) (a : Fin n) {chip : ℕ × Form × ℤ}
    (hchip : chip ∈ w.chips) :
    ∃ i < (w.blockList a.val chip.1).length - 1,
      formEq chip.2.1 (w.point a.val chip.1 (i + 1)) = true := by
  have hW3' := hW3
  simp only [w3Checks, Bool.and_eq_true] at hW3'
  have hSlots : w.chips.all (fun c => decide (c.1 < p)) = true := by
    exact hW3'.left
  have hAll : ExplicitPotential.allFin (fun a : Fin n => ExplicitPotential.allFin fun e : Fin p =>
      w.chips.all (fun c =>
        if c.1 == e.val then
          (List.range ((w.blockList a.val e.val).length - 1)).any
            (fun i => formEq c.2.1 (w.point a.val e.val (i + 1)))
        else true)) = true := by
    exact hW3'.right
  have hSlot : chip.1 < p := decide_eq_true_eq.mp (List.all_eq_true.mp hSlots chip hchip)
  let e : Fin p := ⟨chip.1, hSlot⟩
  have hForA := (ExplicitPotential.allFin_eq_true_iff _).mp hAll a
  have hForAE := (ExplicitPotential.allFin_eq_true_iff _).mp hForA e
  have hAny := (List.all_eq_true.mp hForAE chip hchip)
  rw [ite_eq_left (by simp [e])] at hAny
  rcases List.any_eq_true.mp hAny with ⟨i, hi, hform⟩
  exact ⟨i, List.mem_range.mp hi, hform⟩

/-- W3's syntactic named-point witness has the expected geometric meaning at
every parameter point: the raw form evaluates to that named endpoint. -/
theorem chip_pointValue_eq_of_w3Checks (w : RichWitness)
    (core : ExplicitPotential.Core n p) (hW3 : w.w3Checks core = true)
    (a : Fin n) {chip : ℕ × Form × ℤ} (hchip : chip ∈ w.chips)
    (x : List ℤ) :
    ∃ i < (w.blockList a.val chip.1).length - 1,
      eval chip.2.1 x = w.pointValue x a.val chip.1 (i + 1) := by
  rcases w.chip_named_of_w3Checks core hW3 a hchip with ⟨i, hi, hform⟩
  exact ⟨i, hi, eval_eq_of_formEq hform x⟩

theorem blockLength_nonneg_of_w1Checks (w : RichWitness)
    (core : ExplicitPotential.Core n p) (Γ : Context) (x : List ℤ)
    (hW1 : w.w1Checks core Γ = true) (hx : Γ.Holds x)
    (a : Fin n) (e : Fin p) (i : ℕ)
    (hi : i < (w.blockList a.val e.val).length) :
    0 ≤ w.blockLengthValue x a.val e.val i := by
  simp only [w1Checks, ExplicitPotential.allFin_eq_true_iff, Bool.and_eq_true,
    decide_eq_true_eq, List.all_eq_true] at hW1
  have hMono : (w.blockReceipt a.val e.val i).monotone.check Γ
      (w.blockLength a.val e.val i) = true :=
    (hW1 a e).1.1.1.2 i (List.mem_range.mpr hi)
  exact Cert.check_sound hMono hx

/-- W1's final named endpoint is the coordinate form for its slot. -/
theorem pointValue_last_eq_coord_of_w1Checks (w : RichWitness)
    (core : ExplicitPotential.Core n p) (Γ : Context) (x : List ℤ)
    (hW1 : w.w1Checks core Γ = true) (a : Fin n) (e : Fin p) :
    w.pointValue x a.val e.val (w.blockList a.val e.val).length =
      eval (coordForm e.val) x := by
  simp only [w1Checks, ExplicitPotential.allFin_eq_true_iff, Bool.and_eq_true,
    decide_eq_true_eq, List.all_eq_true] at hW1
  have hNonempty : 0 < (w.blockList a.val e.val).length :=
    (hW1 a e).1.1.1.1.1
  have hForm : formEq
      (w.block a.val e.val ((w.blockList a.val e.val).length - 1)).endForm
      (coordForm e.val) = true :=
    (hW1 a e).1.1.2
  rw [show w.pointValue x a.val e.val (w.blockList a.val e.val).length =
      eval (w.block a.val e.val ((w.blockList a.val e.val).length - 1)).endForm x by
    simp [pointValue, point, Nat.ne_of_gt hNonempty]]
  exact eval_eq_of_formEq hForm x

/-- W1's monotonicity certificate says precisely that the evaluated block
length is nonnegative.  This is the local fact used to order the decoded block
ends. -/
theorem blockLength_nonneg_of_receipt (w : RichWitness) (Γ : Context)
    (x : List ℤ) (hx : Γ.Holds x) (a e i : ℕ)
    (hcheck : (w.blockReceipt a e i).monotone.check Γ (w.blockLength a e i) = true) :
    0 ≤ w.blockLengthValue x a e i := by
  exact Cert.check_sound hcheck hx

/-- The lower W2 receipt gives the numerical lower endpoint-slope bound for
one decoded block. -/
theorem blockLower_bound_of_receipt (w : RichWitness) (Γ : Context)
    (x : List ℤ) (hx : Γ.Holds x) (a e i : ℕ)
    (hcheck : (w.blockReceipt a e i).lower.check Γ
      (subForm (w.block a e i).rise
        (smulForm (w.block a e i).lo (w.blockLength a e i))) = true) :
    (w.block a e i).lo * w.blockLengthValue x a e i ≤
      eval (w.block a e i).rise x := by
  have h := Cert.check_sound hcheck hx
  rw [eval_subForm, eval_smulForm] at h
  change (w.block a e i).lo * eval (w.blockLength a e i) x ≤ _
  exact sub_nonneg.mp h

/-- The upper W2 receipt gives the numerical upper endpoint-slope bound for
one decoded block. -/
theorem blockUpper_bound_of_receipt (w : RichWitness) (Γ : Context)
    (x : List ℤ) (hx : Γ.Holds x) (a e i : ℕ)
    (hcheck : (w.blockReceipt a e i).upper.check Γ
      (subForm (smulForm (w.block a e i).hi (w.blockLength a e i))
        (w.block a e i).rise) = true) :
    eval (w.block a e i).rise x ≤
      (w.block a e i).hi * w.blockLengthValue x a e i := by
  have h := Cert.check_sound hcheck hx
  rw [eval_subForm, eval_smulForm] at h
  change _ ≤ (w.block a e i).hi * eval (w.blockLength a e i) x
  exact sub_nonneg.mp h

/-- A zero-length block has zero declared rise.  This is the W2 fact which
allows repeated finite endpoints to be discarded by canonical interpolation
without changing the total potential change. -/
theorem blockRise_eq_zero_of_bounds (w : RichWitness) (Γ : Context)
    (x : List ℤ) (hx : Γ.Holds x) (a e i : ℕ)
    (hLower : (w.blockReceipt a e i).lower.check Γ
      (subForm (w.block a e i).rise
        (smulForm (w.block a e i).lo (w.blockLength a e i))) = true)
    (hUpper : (w.blockReceipt a e i).upper.check Γ
      (subForm (smulForm (w.block a e i).hi (w.blockLength a e i))
        (w.block a e i).rise) = true)
    (hEmpty : w.blockLengthValue x a e i = 0) :
    eval (w.block a e i).rise x = 0 := by
  have hLo := w.blockLower_bound_of_receipt Γ x hx a e i hLower
  have hHi := w.blockUpper_bound_of_receipt Γ x hx a e i hUpper
  rw [hEmpty] at hLo hHi
  omega

/-- Extract the two numerical W2 receipts for a declared block. -/
theorem blockBounds_of_w2Checks (w : RichWitness)
    (core : ExplicitPotential.Core n p) (Γ : Context)
    (hW2 : w.w2Checks core Γ = true) (a : Fin n) (e : Fin p) (i : ℕ)
    (hi : i < (w.blockList a.val e.val).length) :
    (w.blockReceipt a.val e.val i).lower.check Γ
      (subForm (w.block a.val e.val i).rise
        (smulForm (w.block a.val e.val i).lo (w.blockLength a.val e.val i))) = true ∧
    (w.blockReceipt a.val e.val i).upper.check Γ
      (subForm (smulForm (w.block a.val e.val i).hi (w.blockLength a.val e.val i))
        (w.block a.val e.val i).rise) = true := by
  simp only [w2Checks, ExplicitPotential.allFin_eq_true_iff, Bool.and_eq_true,
    decide_eq_true_eq, List.all_eq_true] at hW2
  exact ⟨((hW2 a e).1 i (List.mem_range.mpr hi)).1.2,
    ((hW2 a e).1 i (List.mem_range.mpr hi)).2⟩

theorem blockRise_eq_zero_of_w2Checks (w : RichWitness)
    (core : ExplicitPotential.Core n p) (Γ : Context) (x : List ℤ)
    (hW2 : w.w2Checks core Γ = true) (hx : Γ.Holds x)
    (a : Fin n) (e : Fin p) (i : ℕ)
    (hi : i < (w.blockList a.val e.val).length)
    (hEmpty : w.blockLengthValue x a.val e.val i = 0) :
    eval (w.block a.val e.val i).rise x = 0 := by
  rcases w.blockBounds_of_w2Checks core Γ hW2 a e i hi with ⟨hLower, hUpper⟩
  exact w.blockRise_eq_zero_of_bounds Γ x hx a.val e.val i hLower hUpper hEmpty

/-- Evaluation commutes with an accumulated list of affine-form additions. -/
theorem eval_foldl_addForm (forms : List Form) (initial : Form) (x : List ℤ) :
    eval (forms.foldl addForm initial) x =
      eval initial x + (forms.map fun form => eval form x).sum := by
  induction forms generalizing initial with
  | nil => simp [eval]
  | cons form forms ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih, eval_addForm]
      ring

/-- Indexed version of `eval_foldl_addForm`, matching the RPF representation
where a finite list of block indices selects the forms to add. -/
theorem eval_foldl_addForm_index {α : Type} (indices : List α) (form : α → Form)
    (initial : Form) (x : List ℤ) :
    eval (indices.foldl (fun z i => addForm z (form i)) initial) x =
      eval initial x + (indices.map fun i => eval (form i) x).sum := by
  induction indices generalizing initial with
  | nil => simp [eval]
  | cons index indices ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih, eval_addForm]
      ring

/-- The ordered finite list `range k` computes the same additive sum as the
finite-set presentation used by the piecewise interpolation interface. -/
theorem foldl_range_eq_finset_sum (f : ℕ → ℤ) (k : ℕ) :
    (List.range k).foldl (fun z i => z + f i) 0 = ∑ i ∈ Finset.range k, f i := by
  induction k with
  | zero => simp
  | succ k ih =>
      simp only [List.range_succ, List.foldl_append, List.foldl_cons,
        List.foldl_nil, ih, Finset.sum_range_succ]

/-- W2 closure, evaluated at a point, is the finite sum of all declared block
rises.  This is the arithmetic input to `piecewise_balance_of_total_rises`. -/
theorem totalRises_eq_potentialDifference_of_w2Checks (w : RichWitness)
    (core : ExplicitPotential.Core n p) (Γ : Context) (x : List ℤ)
    (hW2 : w.w2Checks core Γ = true) (a : Fin n) (e : Fin p) :
    ∑ i ∈ Finset.range (w.blockList a.val e.val).length,
      eval (w.block a.val e.val i).rise x =
        eval (w.pot a.val (core.head e).val) x -
          eval (w.pot a.val (core.tail e).val) x := by
  simp only [w2Checks, ExplicitPotential.allFin_eq_true_iff, Bool.and_eq_true,
    decide_eq_true_eq, List.all_eq_true] at hW2
  have hForm := (hW2 a e).2
  have hEval := eval_eq_of_formEq hForm x
  rw [eval_subForm] at hEval
  have hFold :
      eval ((List.range (w.blockList a.val e.val).length).foldl
        (fun z i => addForm z (w.block a.val e.val i).rise) []) x =
        ∑ i ∈ Finset.range (w.blockList a.val e.val).length,
          eval (w.block a.val e.val i).rise x := by
    rw [eval_foldl_addForm_index]
    simp only [eval, dot, zero_add]
    rw [List.sum_eq_foldl, List.foldl_map]
    exact foldl_range_eq_finset_sum
      (fun i => eval (w.block a.val e.val i).rise x)
      (w.blockList a.val e.val).length
  rw [← hFold]
  exact hEval

/-- On a zero-length slot, W1 collapses every block and W2 makes every rise
zero; consequently the evaluated anchor potential agrees across the slot. -/
theorem potential_eq_of_zeroLength_of_w1w2 (w : RichWitness)
    (core : ExplicitPotential.Core n p) (Γ : Context) (x : List ℤ)
    (hW1 : w.w1Checks core Γ = true) (hW2 : w.w2Checks core Γ = true)
    (hx : Γ.Holds x) (a : Fin n) (e : Fin p)
    (hZero : eval (coordForm e.val) x = 0) :
    eval (w.pot a.val (core.head e).val) x =
      eval (w.pot a.val (core.tail e).val) x := by
  have hW1' := hW1
  simp only [w1Checks, ExplicitPotential.allFin_eq_true_iff, Bool.and_eq_true,
    decide_eq_true_eq, List.all_eq_true] at hW1'
  let k := (w.blockList a.val e.val).length
  have hNonempty : 0 < k := (hW1' a e).1.1.1.1.1
  have hLengths : ∀ i < k, 0 ≤ w.blockLengthValue x a.val e.val i := by
    intro i hi
    exact w.blockLength_nonneg_of_w1Checks core Γ x hW1 hx a e i (by simpa [k] using hi)
  have hLast : w.pointValue x a.val e.val k = 0 := by
    rw [show k = (w.blockList a.val e.val).length by rfl,
      w.pointValue_last_eq_coord_of_w1Checks core Γ x hW1 a e, hZero]
  have hEmpty : ∀ i < k, w.blockLengthValue x a.val e.val i = 0 := by
    intro i hi
    have hLeft := w.pointValue_nonneg_of_lengths x a.val e.val k i hLengths (by omega)
    have hRight := w.pointValue_le_of_lengths_last x a.val e.val k 0 (i + 1)
      hLengths hLast (by omega)
    have hDiff := w.pointValue_succ_sub x a.val e.val i
    have hLen := hLengths i hi
    omega
  have hRise : ∀ i < k, eval (w.block a.val e.val i).rise x = 0 := by
    intro i hi
    exact w.blockRise_eq_zero_of_w2Checks core Γ x hW2 hx a e i
      (by simpa [k] using hi) (hEmpty i hi)
  have hSum : ∑ i ∈ Finset.range k, eval (w.block a.val e.val i).rise x = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    exact hRise i (Finset.mem_range.mp hi)
  have hTotal := w.totalRises_eq_potentialDifference_of_w2Checks core Γ x hW2 a e
  rw [show (w.blockList a.val e.val).length = k by rfl, hSum] at hTotal
  omega

/-- Equality along every edge of a contracted set transports along the census
reachability relation.  This is the small graph-theoretic bridge from the
zero-slot lemma to `DegSpec.RepInvariant`. -/
theorem value_eq_of_reachIn (core : ExplicitPotential.Core n p)
    (F : Finset (Fin p)) (value : Fin n → ℤ)
    (hEdge : ∀ e : Fin p, e ∈ F → value (core.tail e) = value (core.head e))
    {u v : Fin n} (hReach : ReachIn core F u v) : value u = value v := by
  unfold ReachIn ReachInList at hReach
  induction hReach with
  | refl => rfl
  | tail _ hStep ih =>
      rcases hStep with ⟨e, he, hEnds⟩
      have hEq : value (core.tail e) = value (core.head e) :=
        hEdge e ((mem_edgeList F e).mp he)
      rcases hEnds with ⟨hTail, hHead⟩ | ⟨hHead, hTail⟩
      · subst hTail
        subst hHead
        exact ih.trans hEq
      · subst hHead
        subst hTail
        exact ih.trans hEq.symm

/-- The evaluated potential of a rich anchor is invariant on every contraction
class of the census face. -/
theorem repInvariant_of_w1w2_census (w : RichWitness)
    (core : ExplicitPotential.Core n p) (Γ : Context) (x : List ℤ)
    (hW1 : w.w1Checks core Γ = true) (hW2 : w.w2Checks core Γ = true)
    (hx : Γ.Holds x) (a : Fin n) (hn : 0 < n) (ℓ : Fin p → ℕ)
    (hCoord : ∀ e : Fin p, eval (coordForm e.val) x = ℓ e)
    (hForest : IsForest core (zeroSet ℓ))
    (hNotLoopy : ¬ IsLoopy core (zeroSet ℓ)) :
    (censusSpec core hn ℓ hForest hNotLoopy).RepInvariant
      (fun v => eval (w.pot a.val v.val) x) := by
  intro v
  change eval (w.pot a.val (compFold core (zeroSet ℓ) v).val) x =
    eval (w.pot a.val v.val) x
  symm
  apply value_eq_of_reachIn core (zeroSet ℓ) (fun v => eval (w.pot a.val v.val) x)
  · intro e he
    have hZero : eval (coordForm e.val) x = 0 := by
      rw [hCoord e]
      simpa [zeroSet] using he
    exact (w.potential_eq_of_zeroLength_of_w1w2 core Γ x hW1 hW2 hx a e hZero).symm
  · exact reachIn_self_compFold core (zeroSet ℓ) v

/-! ## W4: collapsed boundary runs

At a named interior vertex the only possible negative contribution of the
piecewise script is the jump from the last slope before a run of coincident
named endpoints to the first slope after it.  The checker deliberately uses
the lower bound of the outgoing block and the upper bound of the incoming
block, so its integer residual is a lower bound for the actual coefficient.

The lemmas in this section are phrased without a subdivision graph.  This is
intentional: decoding named forms into a closed-face vertex is the only
graph-specific part of the eventual proof, while the W4 arithmetic is exactly
the calculation below.  In particular repeated endpoints (zero-length
blocks) need no special case: they simply enlarge the run.
-/

/-- The chip sum used by W4, written in the same `List.range`/`foldl` form as
the executable checker. -/
def w4ChipSum (chip : ℕ → ℤ) (i j : ℕ) : ℤ :=
  (List.range (j + 1 - i)).foldl (fun z t => z + chip (i + t)) 0

/-- This is definitionally the chip portion of the executable W4 residual.
Keeping the bridge explicit avoids a later proof depending on the particular
implementation of `w4Residual`. -/
theorem w4Residual_eq_chipSum (w : RichWitness) (a e i j : ℕ) :
    w.w4Residual a e i j =
      w4ChipSum (fun t => w.chipAt a e t) i j +
        (w.block a e j).lo - (w.block a e (i - 1)).hi := rfl

/-- The actual coefficient at a collapsed named-endpoint run: chips on the
run plus outgoing slope minus incoming slope. -/
def w4Actual (chip : ℕ → ℤ) (incoming outgoing : ℤ) (i j : ℕ) : ℤ :=
  w4ChipSum chip i j + outgoing - incoming

/-- The numerical residual checked by W4 is a lower bound for the actual
coefficient whenever W2 bounds the two bordering slopes. -/
theorem w4Residual_le_actual (chip lo hi : ℕ → ℤ)
    (incoming outgoing : ℤ) (i j : ℕ)
    (hIncoming : incoming ≤ hi (i - 1)) (hOutgoing : lo j ≤ outgoing) :
    w4ChipSum chip i j + lo j - hi (i - 1) ≤
      w4Actual chip incoming outgoing i j := by
  unfold w4Actual
  omega

/-- A strict W4 separation receipt rules out the only situation in which its
corresponding run has to be tested: all named endpoints of that run decoding
to the same closed-face vertex. -/
theorem w4_not_collapsed_of_strict_separation {left right : ℤ}
    (hsep : 0 < right - left) : left ≠ right := by
  intro h
  subst right
  omega

/-- The local W4 soundness step.  If the endpoints collapse, the strict
separation alternative is impossible, hence a nonnegative checked residual
remains; W2 then promotes it to nonnegativity of the actual divisor
coefficient. -/
theorem w4_actual_nonneg_of_checked (chip lo hi : ℕ → ℤ)
    (incoming outgoing left right : ℤ) (i j : ℕ)
    (hIncoming : incoming ≤ hi (i - 1)) (hOutgoing : lo j ≤ outgoing)
    (hChecked : 0 ≤ w4ChipSum chip i j + lo j - hi (i - 1) ∨
      0 < right - left)
    (hCollapsed : left = right) :
    0 ≤ w4Actual chip incoming outgoing i j := by
  rcases hChecked with hResidual | hSep
  · exact hResidual.trans (w4Residual_le_actual chip lo hi incoming outgoing i j
      hIncoming hOutgoing)
  · exact False.elim (w4_not_collapsed_of_strict_separation hSep hCollapsed)

/-- Extract one of the two W4 alternatives for an admissible interior run.
The executable checker enumerates the run by `q = i - 1` and `r = j - i`;
this lemma exposes the geometric indices directly, so the closed-face proof
can feed a collapsed run to `w4_actual_nonneg_of_checked`. -/
theorem w4_checked_or_separated_of_w4Checks (w : RichWitness)
    (core : ExplicitPotential.Core n p) (Γ : Context) (x : List ℤ)
    (hW4 : w.w4Checks core Γ = true) (hx : Γ.Holds x)
    (a : Fin n) (e : Fin p) (i j : ℕ)
    (hI : 1 ≤ i)
    (hJ : j ≤ (w.blockList a.val e.val).length - 1)
    (hIJ : i ≤ j)
    (hNotTail : w.pointValue x a.val e.val i ≠ 0)
    (hNotHead : w.pointValue x a.val e.val j ≠ eval (coordForm e.val) x) :
    0 ≤ w.w4Residual a.val e.val i j ∨
      0 < w.pointValue x a.val e.val j - w.pointValue x a.val e.val i := by
  simp only [w4Checks, ExplicitPotential.allFin_eq_true_iff] at hW4
  let k := (w.blockList a.val e.val).length
  have hOuter := hW4 a e
  have hq : i - 1 < k - 1 := by
    dsimp [k]
    omega
  have hInnerAll : (List.range (k - i)).all (fun r =>
      let j := i + r
      if w.tailConfined a.val e.val i || w.headConfined a.val e.val j then true
      else if 0 ≤ w.w4Residual a.val e.val i j then true
      else if i == j then false
      else positiveCheck (w.separationReceipt a.val e.val i j) Γ
        (subForm (w.point a.val e.val j) (w.point a.val e.val i))) = true := by
    have hqEntry := List.all_eq_true.mp hOuter (i - 1) (List.mem_range.mpr hq)
    change (List.range (k - ((i - 1) + 1))).all (fun r =>
      let j := (i - 1) + 1 + r
      if w.tailConfined a.val e.val ((i - 1) + 1) ||
          w.headConfined a.val e.val j then true
      else if 0 ≤ w.w4Residual a.val e.val ((i - 1) + 1) j then true
      else if ((i - 1) + 1) == j then false
      else positiveCheck (w.separationReceipt a.val e.val ((i - 1) + 1) j) Γ
        (subForm (w.point a.val e.val j)
          (w.point a.val e.val ((i - 1) + 1)))) = true at hqEntry
    convert hqEntry using 1
    all_goals simp only [k, show i - 1 + 1 = i by omega]
  have hr : j - i < k - i := by
    dsimp [k]
    omega
  have hEntry := List.all_eq_true.mp hInnerAll (j - i) (List.mem_range.mpr hr)
  have hIndex : i + (j - i) = j := by omega
  simp only [hIndex] at hEntry
  -- Neither endpoint-confinement exemption applies at an interior collapse.
  have hTailFalse : w.tailConfined a.val e.val i = false := by
    by_contra hc
    have hEq : formEq (w.point a.val e.val i) [] = true := by
      simpa [tailConfined] using hc
    refine hNotTail ?_
    show eval (w.point a.val e.val i) x = 0
    rw [eval_eq_of_formEq hEq x, eval_nil]
  have hHeadFalse : w.headConfined a.val e.val j = false := by
    by_contra hc
    have hEq : formEq (w.point a.val e.val j) (coordForm e.val) = true := by
      simpa [headConfined] using hc
    exact hNotHead (eval_eq_of_formEq hEq x)
  rw [hTailFalse, hHeadFalse, Bool.or_self, ite_eq_right (by simp)] at hEntry
  by_cases hResidual : 0 ≤ w.w4Residual a.val e.val i j
  · exact Or.inl hResidual
  · rw [ite_eq_right hResidual] at hEntry
    by_cases hEq : i == j
    · rw [ite_eq_left hEq] at hEntry
      contradiction
    · rw [ite_eq_right hEq] at hEntry
      exact Or.inr (by
        simpa [pointValue, eval_subForm] using (positiveCheck_sound hEntry hx))

/-- The finite endpoint list decoded from an evaluated rich slot.  Its entry
`i` is named point `i + 1`, so it is the end of block `i`. -/
def endpointValues (w : RichWitness) (x : List ℤ) (a e k : ℕ) : List ℕ :=
  (List.range k).map fun i => (w.pointValue x a e (i + 1)).toNat

@[simp] theorem endpointValues_length (w : RichWitness) (x : List ℤ) (a e k : ℕ) :
    (w.endpointValues x a e k).length = k := by
  simp [endpointValues]

theorem endpointValues_getD (w : RichWitness) (x : List ℤ) (a e k L i : ℕ)
    (hi : i < k) :
    (w.endpointValues x a e k).getD i L = (w.pointValue x a e (i + 1)).toNat := by
  rw [List.getD_eq_getElem _ _ (by simpa [endpointValues] using hi)]
  simp [endpointValues]

/-- W1's nonempty, monotone endpoint data decodes to the finite selector
required by canonical piecewise interpolation.  The input `hLast` is the
evaluated W1 final-end equality; all block lengths are integral and the
nonnegative receipts make the `Int.toNat` conversion exact. -/
def finiteBlockEndsOfW1 (w : RichWitness) (x : List ℤ) (a e k L : ℕ)
    (hNonempty : 0 < k)
    (hLast : w.pointValue x a e k = L)
    (hLength : ∀ i < k, 0 ≤ w.blockLengthValue x a e i) :
    FiniteBlockEnds L :=
  FiniteBlockEnds.ofOrderedLast (w.endpointValues x a e k) (by
    simp [endpointValues, hNonempty]) (by
    rw [w.endpointValues_length]
    rw [w.endpointValues_getD x a e k L (k - 1) (by omega)]
    rw [show k - 1 + 1 = k by omega, hLast]
    simp) (by
    intro i
    by_cases hi : i < k
    · by_cases hlast : i + 1 = k
      · have hiLast : i = k - 1 := by omega
        rw [hiLast, w.endpointValues_getD x a e k L (k - 1) (by omega)]
        rw [show k - 1 + 1 = k by omega, hLast]
        rw [List.getD_eq_default _ _ (by simp [endpointValues])]
        simp
      · have hiNext : i + 1 < k := by omega
        have hdiff : w.pointValue x a e (i + 2) - w.pointValue x a e (i + 1) =
            w.blockLengthValue x a e (i + 1) := by
          simpa [Nat.add_assoc] using w.pointValue_succ_sub x a e (i + 1)
        have hnonneg := hLength (i + 1) hiNext
        have hmono : w.pointValue x a e (i + 1) ≤ w.pointValue x a e (i + 2) := by
          omega
        rw [w.endpointValues_getD x a e k L i hi,
          w.endpointValues_getD x a e k L (i + 1) hiNext]
        exact Int.toNat_le_toNat hmono
    · have hik : k ≤ i := Nat.le_of_not_gt hi
      have hnext : k ≤ i + 1 := by omega
      rw [List.getD_eq_default _ _ (by simpa [endpointValues] using hik),
        List.getD_eq_default _ _ (by simpa [endpointValues] using hnext)])

/-- The finite endpoint selector decoded from an accepted rich W1 block list
on a concrete closed face. -/
noncomputable def richBlockEnds
    (d : Utilities.Certificate.DegenerateSpec.DegSpec n p)
    (w : RichWitness) (core : ExplicitPotential.Core n p) (Γ : Context)
    (x : List ℤ) (hW1 : w.w1Checks core Γ = true) (hx : Γ.Holds x)
    (hCoord : ∀ e : Fin p, eval (coordForm e.val) x = d.length e)
    (a : Fin n) (e : Fin p) : FiniteBlockEnds (d.length e) :=
  w.finiteBlockEndsOfW1 x a.val e.val (w.blockList a.val e.val).length (d.length e)
    (by
      have h := hW1
      simp only [w1Checks, ExplicitPotential.allFin_eq_true_iff, Bool.and_eq_true,
        decide_eq_true_eq, List.all_eq_true] at h
      exact (h a e).1.1.1.1.1)
    (by
      rw [w.pointValue_last_eq_coord_of_w1Checks core Γ x hW1 a e, hCoord e])
    (by
      intro i hi
      exact w.blockLength_nonneg_of_w1Checks core Γ x hW1 hx a e i hi)

/-- On an actual rich block, the finite decoder's endpoint is exactly the
evaluated named right endpoint.  Keeping this lookup lemma separate makes
the W2 empty-block bridge below independent of the proof fields stored in
`FiniteBlockEnds.ofOrderedLast`. -/
theorem richBlockEnds_endAt
    (d : Utilities.Certificate.DegenerateSpec.DegSpec n p)
    (w : RichWitness) (core : ExplicitPotential.Core n p) (Γ : Context)
    (x : List ℤ) (hW1 : w.w1Checks core Γ = true) (hx : Γ.Holds x)
    (hCoord : ∀ e : Fin p, eval (coordForm e.val) x = d.length e)
    (a : Fin n) (e : Fin p) (i : ℕ)
    (hi : i < (w.blockList a.val e.val).length) :
    (w.richBlockEnds d core Γ x hW1 hx hCoord a e).endAt i =
      (w.pointValue x a.val e.val (i + 1)).toNat := by
  unfold richBlockEnds finiteBlockEndsOfW1 FiniteBlockEnds.endAt
  exact w.endpointValues_getD x a.val e.val
    (w.blockList a.val e.val).length (d.length e) i hi

@[simp] theorem richBlockEnds_length
    (d : Utilities.Certificate.DegenerateSpec.DegSpec n p)
    (w : RichWitness) (core : ExplicitPotential.Core n p) (Γ : Context)
    (x : List ℤ) (hW1 : w.w1Checks core Γ = true) (hx : Γ.Holds x)
    (hCoord : ∀ e : Fin p, eval (coordForm e.val) x = d.length e)
    (a : Fin n) (e : Fin p) :
    (w.richBlockEnds d core Γ x hW1 hx hCoord a e).ends.length =
      (w.blockList a.val e.val).length := by
  unfold richBlockEnds finiteBlockEndsOfW1
  exact w.endpointValues_length x a.val e.val (w.blockList a.val e.val).length

/-- Beyond a declared rich block list, the fail-closed default block has zero
rise, so it contributes nothing to the interpolation sum. -/
theorem eval_block_rise_eq_zero_of_not_lt (w : RichWitness) (x : List ℤ)
    (a e i : ℕ) (hi : ¬ i < (w.blockList a e).length) :
    eval (w.block a e i).rise x = 0 := by
  unfold block
  rw [List.getD_eq_default _ _ (Nat.le_of_not_gt hi)]
  simp [Block.dflt, eval]

/-- If an actual decoded rich block has an empty finite interval, then W1
makes its evaluated length zero and W2 forces its declared rise to vanish.
This is the exact bridge needed by `PiecewiseData.empty_rise`: repeated
finite endpoints are harmless even when their RPF block records remain in
the list. -/
theorem blockRise_eq_zero_of_richBlockEnds_empty
    (d : Utilities.Certificate.DegenerateSpec.DegSpec n p)
    (w : RichWitness) (core : ExplicitPotential.Core n p) (Γ : Context)
    (x : List ℤ) (hW1 : w.w1Checks core Γ = true) (hW2 : w.w2Checks core Γ = true)
    (hx : Γ.Holds x) (hCoord : ∀ e : Fin p, eval (coordForm e.val) x = d.length e)
    (a : Fin n) (e : Fin p) (i : ℕ)
    (hi : i < (w.blockList a.val e.val).length)
    (hEmpty : (w.richBlockEnds d core Γ x hW1 hx hCoord a e).endAt i ≤
      (w.richBlockEnds d core Γ x hW1 hx hCoord a e).startAt i) :
    eval (w.block a.val e.val i).rise x = 0 := by
  let k := (w.blockList a.val e.val).length
  have hLengths : ∀ j < k, 0 ≤ w.blockLengthValue x a.val e.val j := by
    intro j hj
    exact w.blockLength_nonneg_of_w1Checks core Γ x hW1 hx a e j (by simpa [k] using hj)
  have hLenZero : w.blockLengthValue x a.val e.val i = 0 := by
    by_cases hZero : i = 0
    · subst i
      have hEnd : (w.pointValue x a.val e.val 1).toNat ≤ 0 := by
        simp only [FiniteBlockEnds.startAt, ite_eq_left] at hEmpty
        rw [w.richBlockEnds_endAt d core Γ x hW1 hx hCoord a e 0 hi] at hEmpty
        exact hEmpty
      have hPointNonneg : 0 ≤ w.pointValue x a.val e.val 1 :=
        w.pointValue_nonneg_of_lengths x a.val e.val k 1 hLengths (by omega)
      have hPointZero : w.pointValue x a.val e.val 1 = 0 := by
        have hNatZero : (w.pointValue x a.val e.val 1).toNat = 0 := by omega
        omega
      have hDiff := w.pointValue_succ_sub x a.val e.val 0
      rw [pointValue_zero, hPointZero] at hDiff
      omega
    · have hPred : i - 1 < k := by omega
      have hEnd : (w.pointValue x a.val e.val (i + 1)).toNat ≤
          (w.pointValue x a.val e.val i).toNat := by
        rw [FiniteBlockEnds.startAt, ite_eq_right hZero] at hEmpty
        rw [w.richBlockEnds_endAt d core Γ x hW1 hx hCoord a e i (by simpa [k] using hi),
          w.richBlockEnds_endAt d core Γ x hW1 hx hCoord a e (i - 1) (by
            simpa [k] using hPred)] at hEmpty
        simpa [show i - 1 + 1 = i by omega] using hEmpty
      have hPointMono : w.pointValue x a.val e.val i ≤
          w.pointValue x a.val e.val (i + 1) :=
        w.pointValue_mono_of_lengths x a.val e.val k hLengths (by omega) (by omega)
      have hPointI : 0 ≤ w.pointValue x a.val e.val i :=
        w.pointValue_nonneg_of_lengths x a.val e.val k i hLengths (by omega)
      have hPointSucc : 0 ≤ w.pointValue x a.val e.val (i + 1) :=
        w.pointValue_nonneg_of_lengths x a.val e.val k (i + 1) hLengths (by omega)
      have hNatMono : (w.pointValue x a.val e.val i).toNat ≤
          (w.pointValue x a.val e.val (i + 1)).toNat := Int.toNat_le_toNat hPointMono
      have hNatEq : (w.pointValue x a.val e.val i).toNat =
          (w.pointValue x a.val e.val (i + 1)).toNat := Nat.le_antisymm hNatMono hEnd
      have hPointEq : w.pointValue x a.val e.val i =
          w.pointValue x a.val e.val (i + 1) := by omega
      have hDiff := w.pointValue_succ_sub x a.val e.val i
      omega
  exact w.blockRise_eq_zero_of_w2Checks core Γ x hW2 hx a e i (by simpa [k] using hi) hLenZero

/-- Once W2 has made every collapsed block's rise zero, its closure equality
is exactly the balance field required by `PiecewiseData`.  This is independent
of the RPF list encoding and is the final arithmetic conversion used by the
rich-leaf decoder. -/
theorem piecewise_balance_of_total_rises {n p : ℕ}
    (d : Utilities.Certificate.DegenerateSpec.DegSpec n p)
    (potential : Fin n → ℤ)
    (blocks : (e : Fin p) → FiniteBlockEnds (d.length e))
    (rises : Fin p → ℕ → ℤ)
    (hEmpty : ∀ e i, (blocks e).endAt i ≤ (blocks e).startAt i → rises e i = 0)
    (hTotal : ∀ e : Fin p,
      potential (d.core.head e) = potential (d.core.tail e) +
        ∑ i ∈ Finset.range (blocks e).ends.length, rises e i) :
    ∀ e : Fin p,
      potential (d.core.head e) = potential (d.core.tail e) +
        ∑ k ∈ Finset.range (d.length e),
          Utilities.Certificate.DegenerateSpec.DegSpec.blockSlope
            (fun e k => (blocks e).blockAt k)
            (fun e k => (blocks e).endAt k) rises e k := by
  intro e
  rw [hTotal e]
  congr 1
  symm
  exact (blocks e).sum_selected_steps_eq_total_rises (rises e) (hEmpty e)

/-- The canonical piecewise interpolation data for one rich anchor on the
census face selected by the current length vector. -/
noncomputable def richCensusPiecewiseData (w : RichWitness)
    (core : ExplicitPotential.Core n p) (Γ : Context) (x : List ℤ)
    (hW1 : w.w1Checks core Γ = true) (hW2 : w.w2Checks core Γ = true)
    (hx : Γ.Holds x) (ℓ : Fin p → ℕ)
    (hCoord : ∀ e : Fin p, eval (coordForm e.val) x = ℓ e)
    (hn : 0 < n) (hForest : IsForest core (zeroSet ℓ))
    (hNotLoopy : ¬ IsLoopy core (zeroSet ℓ)) (a : Fin n) :
    (censusSpec core hn ℓ hForest hNotLoopy).PiecewiseData
      (fun v => eval (w.pot a.val v.val) x) :=
  (censusSpec core hn ℓ hForest hNotLoopy).decodePiecewiseData
    (fun v => eval (w.pot a.val v.val) x)
    (fun e => w.richBlockEnds (censusSpec core hn ℓ hForest hNotLoopy)
      core Γ x hW1 hx hCoord a e)
    (fun e i => eval (w.block a.val e.val i).rise x)
    (by
      apply piecewise_balance_of_total_rises (censusSpec core hn ℓ hForest hNotLoopy)
        (fun v => eval (w.pot a.val v.val) x)
        (fun e => w.richBlockEnds (censusSpec core hn ℓ hForest hNotLoopy)
          core Γ x hW1 hx hCoord a e)
        (fun e i => eval (w.block a.val e.val i).rise x)
      · intro e i hEmpty
        by_cases hi : i < (w.blockList a.val e.val).length
        · exact w.blockRise_eq_zero_of_richBlockEnds_empty
            (censusSpec core hn ℓ hForest hNotLoopy) core Γ x hW1 hW2 hx hCoord
            a e i hi hEmpty
        · exact w.eval_block_rise_eq_zero_of_not_lt x a.val e.val i hi
      · intro e
        have hTotal := w.totalRises_eq_potentialDifference_of_w2Checks core Γ x hW2 a e
        rw [← w.richBlockEnds_length (censusSpec core hn ℓ hForest hNotLoopy)
          core Γ x hW1 hx hCoord a e] at hTotal
        change eval (w.pot a.val (core.head e).val) x =
          eval (w.pot a.val (core.tail e).val) x +
            ∑ i ∈ Finset.range
              (w.richBlockEnds (censusSpec core hn ℓ hForest hNotLoopy)
                core Γ x hW1 hx hCoord a e).ends.length,
              eval (w.block a.val e.val i).rise x
        omega)

/-- The firing script denoted by the decoded rich block data. -/
noncomputable def richCensusPiecewiseScript (w : RichWitness)
    (core : ExplicitPotential.Core n p) (Γ : Context) (x : List ℤ)
    (hW1 : w.w1Checks core Γ = true) (hW2 : w.w2Checks core Γ = true)
    (hx : Γ.Holds x) (ℓ : Fin p → ℕ)
    (hCoord : ∀ e : Fin p, eval (coordForm e.val) x = ℓ e)
    (hn : 0 < n) (hForest : IsForest core (zeroSet ℓ))
    (hNotLoopy : ¬ IsLoopy core (zeroSet ℓ)) (a : Fin n) :
    firingScript (censusSpec core hn ℓ hForest hNotLoopy).graph :=
  (censusSpec core hn ℓ hForest hNotLoopy).piecewiseScript
    (w.richCensusPiecewiseData core Γ x hW1 hW2 hx ℓ hCoord hn hForest hNotLoopy a)

/-- The rich script's unit slopes are precisely its selected canonical block
slopes; this is the entry point for the W4 interior coefficient calculation. -/
theorem richCensus_isStepSlope (w : RichWitness)
    (core : ExplicitPotential.Core n p) (Γ : Context) (x : List ℤ)
    (hW1 : w.w1Checks core Γ = true) (hW2 : w.w2Checks core Γ = true)
    (hx : Γ.Holds x) (ℓ : Fin p → ℕ)
    (hCoord : ∀ e : Fin p, eval (coordForm e.val) x = ℓ e)
    (hn : 0 < n) (hForest : IsForest core (zeroSet ℓ))
    (hNotLoopy : ¬ IsLoopy core (zeroSet ℓ)) (a : Fin n) :
    (censusSpec core hn ℓ hForest hNotLoopy).IsStepSlope
      (w.richCensusPiecewiseScript core Γ x hW1 hW2 hx ℓ hCoord hn hForest hNotLoopy a)
      (fun e k => Utilities.Certificate.DegenerateSpec.DegSpec.blockSlope
        (w.richCensusPiecewiseData core Γ x hW1 hW2 hx ℓ hCoord hn hForest hNotLoopy a).blockAt
        (w.richCensusPiecewiseData core Γ x hW1 hW2 hx ℓ hCoord hn hForest hNotLoopy a).blockEnd
        (w.richCensusPiecewiseData core Γ x hW1 hW2 hx ℓ hCoord hn hForest hNotLoopy a).blockRise e
          k) := by
  unfold richCensusPiecewiseScript
  exact (censusSpec core hn ℓ hForest hNotLoopy).isStepSlope_piecewiseScript
    (w.repInvariant_of_w1w2_census core Γ x hW1 hW2 hx a hn ℓ hCoord hForest hNotLoopy)

/-! ## W4: selector changes on a rich closed face

The finite selector sees a forward jump precisely when a consecutive run of
named endpoints has collapsed to the intervening subdivision vertex.  The
two lemmas below isolate that geometric fact from the subsequent chip-divisor
accounting.  Their indices agree with the checker: if the old selected block
is `i`, then its named right endpoint is `i + 1`, while the new block is `j`.
-/

/-- A forward change of the decoded rich block selector identifies the two
named forms at the ends of the collapsed run.  This is the geometric premise
which rules out W4's strict-separation alternative. -/
theorem pointValue_eq_of_rich_selector_change
    (d : Utilities.Certificate.DegenerateSpec.DegSpec n p)
    (w : RichWitness) (core : ExplicitPotential.Core n p) (Γ : Context)
    (x : List ℤ) (hW1 : w.w1Checks core Γ = true) (hx : Γ.Holds x)
    (hCoord : ∀ e : Fin p, eval (coordForm e.val) x = d.length e)
    (a : Fin n) (e : Fin p) (offset : Fin (d.length e - 1))
    (hChange :
      (w.richBlockEnds d core Γ x hW1 hx hCoord a e).blockAt offset.val <
        (w.richBlockEnds d core Γ x hW1 hx hCoord a e).blockAt (offset.val + 1)) :
    w.pointValue x a.val e.val
        ((w.richBlockEnds d core Γ x hW1 hx hCoord a e).blockAt offset.val + 1) =
      w.pointValue x a.val e.val
        ((w.richBlockEnds d core Γ x hW1 hx hCoord a e).blockAt (offset.val + 1)) := by
  let b := w.richBlockEnds d core Γ x hW1 hx hCoord a e
  let i := b.blockAt offset.val
  let j := b.blockAt (offset.val + 1)
  have hOffset : offset.val + 1 < d.length e := by
    omega
  have hRunLeft : b.endAt i = offset.val + 1 := by
    exact b.endAt_eq_succ_of_selector_lt offset.val i j i hOffset rfl rfl
      (by simpa [i, j] using hChange) (by omega) (by omega)
  have hRunRight : b.endAt (j - 1) = offset.val + 1 := by
    have hIJ : i < j := by simpa [i, j] using hChange
    have hIle : i ≤ j - 1 := by omega
    have hlt : j - 1 < j := by omega
    exact b.endAt_eq_succ_of_selector_lt offset.val i j (j - 1) hOffset rfl rfl
      hIJ hIle hlt
  have hIlt : i < (w.blockList a.val e.val).length := by
    have hI : i < b.ends.length := b.blockAt_lt_length offset.val (by omega)
    have hLength : b.ends.length = (w.blockList a.val e.val).length := by
      unfold b
      exact w.richBlockEnds_length d core Γ x hW1 hx hCoord a e
    rw [hLength] at hI
    exact hI
  have hJlt : j - 1 < (w.blockList a.val e.val).length := by
    have hJ : j < b.ends.length := b.blockAt_lt_length (offset.val + 1) hOffset
    rw [w.richBlockEnds_length d core Γ x hW1 hx hCoord a e] at hJ
    omega
  have hIend : (w.pointValue x a.val e.val (i + 1)).toNat = offset.val + 1 := by
    rw [← w.richBlockEnds_endAt d core Γ x hW1 hx hCoord a e i (by
      simpa [b, i] using hIlt)]
    change b.endAt i = offset.val + 1
    exact hRunLeft
  have hJend : (w.pointValue x a.val e.val j).toNat = offset.val + 1 := by
    have hIndex : j - 1 + 1 = j := by
      have : 0 < j := lt_of_le_of_lt (Nat.zero_le i)
        (by simpa [i, j] using hChange)
      omega
    rw [← hIndex]
    rw [← w.richBlockEnds_endAt d core Γ x hW1 hx hCoord a e (j - 1) (by
      simpa [b, j] using hJlt)]
    simpa [b, j] using hRunRight
  have hLengths : ∀ t < (w.blockList a.val e.val).length,
      0 ≤ w.blockLengthValue x a.val e.val t := by
    intro t ht
    exact w.blockLength_nonneg_of_w1Checks core Γ x hW1 hx a e t ht
  have hLeftNonneg : 0 ≤ w.pointValue x a.val e.val (i + 1) :=
    w.pointValue_nonneg_of_lengths x a.val e.val
      (w.blockList a.val e.val).length (i + 1) hLengths (by omega)
  have hRightNonneg : 0 ≤ w.pointValue x a.val e.val j :=
    w.pointValue_nonneg_of_lengths x a.val e.val
      (w.blockList a.val e.val).length j hLengths (by omega)
  have hNatEq : (w.pointValue x a.val e.val (i + 1)).toNat =
      (w.pointValue x a.val e.val j).toNat := hIend.trans hJend.symm
  change w.pointValue x a.val e.val (i + 1) = w.pointValue x a.val e.val j
  omega

/-- W4 promotes its checked residual to the actual slope-jump coefficient at
a forward rich-selector change, once W2 has supplied the bordering slope
bounds.  The caller supplies the two bounds so this lemma can be used with
the canonical script as well as any extensionally equal slope presentation. -/
theorem w4_actual_nonneg_of_rich_selector_change
    (d : Utilities.Certificate.DegenerateSpec.DegSpec n p)
    (w : RichWitness) (core : ExplicitPotential.Core n p) (Γ : Context)
    (x : List ℤ) (hW1 : w.w1Checks core Γ = true)
    (hW4 : w.w4Checks core Γ = true) (hx : Γ.Holds x)
    (hCoord : ∀ e : Fin p, eval (coordForm e.val) x = d.length e)
    (a : Fin n) (e : Fin p) (offset : Fin (d.length e - 1))
    (hChange :
      (w.richBlockEnds d core Γ x hW1 hx hCoord a e).blockAt offset.val <
        (w.richBlockEnds d core Γ x hW1 hx hCoord a e).blockAt (offset.val + 1))
    (incoming outgoing : ℤ)
    (hIncoming : incoming ≤ (w.block a.val e.val
      ((w.richBlockEnds d core Γ x hW1 hx hCoord a e).blockAt offset.val)).hi)
    (hOutgoing : (w.block a.val e.val
      ((w.richBlockEnds d core Γ x hW1 hx hCoord a e).blockAt (offset.val + 1))).lo ≤ outgoing) :
    0 ≤ w4Actual (fun t => w.chipAt a.val e.val t) incoming outgoing
      ((w.richBlockEnds d core Γ x hW1 hx hCoord a e).blockAt offset.val + 1)
      ((w.richBlockEnds d core Γ x hW1 hx hCoord a e).blockAt (offset.val + 1)) := by
  let b := w.richBlockEnds d core Γ x hW1 hx hCoord a e
  let i := b.blockAt offset.val
  let j := b.blockAt (offset.val + 1)
  have hCollapsed : w.pointValue x a.val e.val (i + 1) =
      w.pointValue x a.val e.val j := by
    simpa [b, i, j] using w.pointValue_eq_of_rich_selector_change d core Γ x hW1 hx
      hCoord a e offset hChange
  -- The collapsed run sits at the strictly interior offset `offset + 1`, so
  -- neither of W4's endpoint exemptions applies.
  have hLenPos : offset.val + 1 < d.length e := by omega
  have hIlt : i < (w.blockList a.val e.val).length := by
    have hI : i < b.ends.length := b.blockAt_lt_length offset.val (by omega)
    rwa [w.richBlockEnds_length d core Γ x hW1 hx hCoord a e] at hI
  have hJlt : j < (w.blockList a.val e.val).length := by
    have hJ : j < b.ends.length := b.blockAt_lt_length (offset.val + 1) hLenPos
    rwa [w.richBlockEnds_length d core Γ x hW1 hx hCoord a e] at hJ
  have hLengths : ∀ t < (w.blockList a.val e.val).length,
      0 ≤ w.blockLengthValue x a.val e.val t := fun t ht =>
    w.blockLength_nonneg_of_w1Checks core Γ x hW1 hx a e t ht
  have hIend : (w.pointValue x a.val e.val (i + 1)).toNat = offset.val + 1 := by
    rw [← w.richBlockEnds_endAt d core Γ x hW1 hx hCoord a e i hIlt]
    exact b.endAt_eq_succ_of_selector_lt offset.val i j i hLenPos rfl rfl
      (by simpa [i, j] using hChange) (by omega) (by omega)
  have hIvalue : w.pointValue x a.val e.val (i + 1) = (offset.val + 1 : ℕ) := by
    have hnn : 0 ≤ w.pointValue x a.val e.val (i + 1) :=
      w.pointValue_nonneg_of_lengths x a.val e.val
        (w.blockList a.val e.val).length (i + 1) hLengths (by omega)
    omega
  have hNotTail : w.pointValue x a.val e.val (i + 1) ≠ 0 := by
    rw [hIvalue]; omega
  have hNotHead : w.pointValue x a.val e.val j ≠ eval (coordForm e.val) x := by
    rw [← hCollapsed, hIvalue, hCoord e]
    omega
  have hCheck := w.w4_checked_or_separated_of_w4Checks core Γ x hW4 hx a e
    (i + 1) j (by omega) (by omega)
    (by simpa [i, j] using (show i + 1 ≤ j by
      have h : i < j := by simpa [i, j] using hChange
      omega))
    hNotTail hNotHead
  rw [w4Residual_eq_chipSum] at hCheck
  exact w4_actual_nonneg_of_checked (fun t => w.chipAt a.val e.val t)
    (fun t => (w.block a.val e.val t).lo) (fun t => (w.block a.val e.val t).hi)
    incoming outgoing (w.pointValue x a.val e.val (i + 1))
    (w.pointValue x a.val e.val j) (i + 1) j
    (by simpa [i] using hIncoming) (by simpa [j] using hOutgoing)
    hCheck hCollapsed

/-! ## W5: finite endpoint minima

The checker stores a conservative endpoint contribution as a finite minimum.
The geometric part of the closed-face proof supplies a particular prefix (or
suffix) length; this lemma is the deliberately small arithmetic bridge from
that selected candidate to the stored minimum. -/

theorem minOver_le_candidate (f : ℕ → ℤ) (bound s : ℕ) (hs : s ≤ bound) :
    minOver f bound ≤ f s := by
  induction bound generalizing s with
  | zero =>
      have : s = 0 := by omega
      subst s
      simp [minOver]
  | succ bound ih =>
      by_cases hlast : s = bound + 1
      · subst s
        rw [show minOver f (bound + 1) = min (minOver f bound) (f (bound + 1)) by
          simp only [minOver, List.range_succ, List.foldl_append, List.foldl_cons,
            List.foldl_nil]]
        exact min_le_right _ _
      · have hs' : s ≤ bound := by omega
        have hih := ih s hs'
        have hstep : minOver f (bound + 1) ≤ minOver f bound := by
          rw [show minOver f (bound + 1) = min (minOver f bound) (f (bound + 1)) by
            simp only [minOver, List.range_succ, List.foldl_append, List.foldl_cons,
              List.foldl_nil]]
          exact min_le_left _ _
        exact hstep.trans hih

theorem tailContribution_le_candidate (w : RichWitness) (a e s : ℕ)
    (hs : s ≤ (w.plan a).headSlack.getD e 0) :
    w.tailContribution a e ≤ w.tailCandidate a e s :=
  minOver_le_candidate _ _ _ hs

theorem headContribution_le_candidate (w : RichWitness) (a e s : ℕ)
    (hs : s ≤ (w.plan a).tailSlack.getD e 0) :
    w.headContribution a e ≤ w.headCandidate a e s :=
  minOver_le_candidate _ _ _ hs

/-!
## Required next bridge lemmas

The following are the exact nontrivial obligations left before a theorem
`richLeafChecks_sound` can be assembled.

* `decode_piecewise`: from the W1 monotonicity/final-end facts and the W2
  receipts at `x`, construct `d.PiecewiseData potential`.  Its proof requires
  a finite monotone-list selector (first block end strictly above a surviving
  step) and a telescoping lemma saying that the canonical `step`s over a
  block sum to its declared rise.  The latter is not currently exported by
  `SubdivisionArithmetic`.

* `w4_boundary_effective`: identify a change of decoded block at an interior
  offset with a maximal run of named endpoints which evaluate to that offset.
  The W4 residual is the chip sum on this run plus the lower bound on the
  outgoing first slope minus the upper bound on the incoming last slope.
  `DegSpec.prin_piecewiseScript_interiorVertex_nonneg_of_sameBlock` already
  handles the complementary (non-boundary) case.

* `w5_core_effective`: after a prefix/suffix of named points collapses into a
  core class, compare the actual first/last selected slopes and all chips
  which decode to that class with `tailContribution`/`headContribution`.
  `w5Checks` then proves each uncontracted core summand nonnegative; summing
  it over a representative class and using
  `DegSpec.prin_piecewiseScript_coreVertex` proves the quotient-core case.

  **Current formal interface obstruction.**  `RichWitness.chips` is still a
  raw `List (Nat × Form × Int)`, whereas the closed-face library's only
  chipwise divisor API is `Closed.WeightedChip.divisorOf`, which accepts
  bounded `Code`s from an `ExplicitPotential.Certificate`.  A rich leaf has
  neither of those objects.  Consequently the library has no definition for
  the rich chip divisor on `d.graph`, nor a coefficient theorem saying that
  chips which decode to the tail/head are exactly the C-faithful
  first-matched `chipPrefix`/suffix sums.  W3 is enough to prove the needed
  bounds *after* such a decoder exists, but cannot state that comparison.
  The necessary next artifact is a row-local decoder from the raw rich chips
  and evaluated named endpoints to `CFDiv d.graph`, with core/interior
  coefficient formulae.  The checker now assigns a chip to its first matching
  named interior endpoint, matching `rpfcheck.c`; the decoder theorem must
  preserve that convention when zero-length blocks duplicate endpoint forms.

The last two lemmas must use `Closed.WeightedChip.divisorOf` (or an equivalent
row-local decoder), because a named point may become either endpoint on a
closed face.  Treating every declared chip as an interior vertex would be
incorrect when a block collapses.
-/

end RichWitness

end Utilities.Subdivision.ClosedRowProof
