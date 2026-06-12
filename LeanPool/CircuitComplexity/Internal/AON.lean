/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import LeanPool.CircuitComplexity.AON.Defs

/-! # Internal: AND/OR/NOT Completeness Proof

This internal module proves functional completeness of `Basis.unboundedAON`
via DNF (disjunctive normal form) construction. The basis definitions are
in `Circ.AON.Defs`; this module is re-exported through `Circ.AON`.
-/

namespace CircuitComplexity


/-- Indicator circuit: outputs `true` iff the input equals `s`.

A single N-input AND gate where input `i` is wired to primary input `i`,
negated when `s i = false`. No internal gates needed. -/
def AONIndicator {N : Nat} [NeZero N] (s : BitString N) :
    Circuit Basis.unboundedAON N 1 0 where
  gates i := i.elim0
  outputs _ :=
    { op := .and, fanIn := N, arityOk := trivial,
      inputs := fun j => ⟨j.val, by omega⟩,
      negated := fun j => !(s j) }
  acyclic i := i.elim0

/-- DNF circuit computing an arbitrary `f : BitString N → Bool`.

For each of the `2^N` possible inputs `s` (decoded via `Nat.testBit`),
internal gate `i` is the indicator AND for `s` when `f s = true`, or a
trivially-false 0-input OR otherwise. The single output OR gate disjoins
all internal gates. -/
private def AONFor.mkGate {N : Nat} (f : BitString N → Bool) (i : Fin (2 ^ N)) :
    Gate Basis.unboundedAON (N + 2 ^ N) :=
  if f (fun j => i.val.testBit j.val) then
    { op := .and, fanIn := N, arityOk := trivial,
      inputs := fun j => (j.castAdd (2 ^ N)),
      negated := fun j => !(i.val.testBit j.val) }
  else
    { op := .or, fanIn := 0, arityOk := trivial,
      inputs := Fin.elim0,
      negated := Fin.elim0 }

private lemma AONFor.mkGate_acyclic {N : Nat} (f : BitString N → Bool)
    (i : Fin (2 ^ N)) (k : Fin (AONFor.mkGate f i).fanIn) :
    ((AONFor.mkGate f i).inputs k).val < N + i.val := by
  revert k; unfold mkGate
  cases f (fun j => i.val.testBit j.val)
  · intro k; exact Fin.elim0 k
  · intro k; exact Nat.lt_of_lt_of_le k.isLt (Nat.le_add_right N _)

/-- Single-output DNF circuit computing `f : BitString N → Bool`.

For each of the `2^N` possible inputs `s`, internal gate `i` is the
indicator AND for `s` when `f s = true`, or a trivially-false 0-input
OR otherwise. The single output OR gate disjoins all internal gates. -/
def AONFor {N : Nat} [NeZero N] (f : BitString N → Bool) :
    Circuit Basis.unboundedAON N 1 (2 ^ N) where
  gates := AONFor.mkGate f
  outputs _ :=
    { op := .or, fanIn := 2 ^ N, arityOk := trivial,
      inputs := fun j => (j.natAdd N),
      negated := fun _ => false }
  acyclic := AONFor.mkGate_acyclic f

private lemma AONFor_wireValue_gate {N : Nat} [NeZero N] (f : BitString N → Bool)
    (x : BitString N) (i : Fin (2 ^ N)) :
    (AONFor f).wireValue x (Fin.natAdd N i) =
      (AONFor.mkGate f i).eval ((AONFor f).wireValue x) := by
  have hge : ¬ ((Fin.natAdd N i).val < N) := by simp [Fin.natAdd]
  rw [Circuit.wireValue_ge _ _ _ hge]
  congr 1; simp only [AONFor]; congr 1
  exact Fin.ext (by simp [Fin.natAdd])

@[simp] private lemma AONFor_outputs {N : Nat} [NeZero N] (f : BitString N → Bool) (j : Fin 1) :
    (AONFor f).outputs j =
      { op := .or, fanIn := 2 ^ N, arityOk := trivial,
        inputs := Fin.natAdd N, negated := fun _ => false } := rfl

@[simp] private lemma AONFor_gates {N : Nat} [NeZero N] (f : BitString N → Bool) :
    (AONFor f).gates = AONFor.mkGate f := rfl

/-! ## Helper lemmas for AONFor correctness -/

private lemma foldl_bor_eq_true (n : Nat) (g : Fin n → Bool) :
    (Fin.foldl n (fun acc i => acc || g i) false = true) ↔ (∃ i : Fin n, g i = true) := by
  induction n with
  | zero => simp [Fin.foldl_zero]
  | succ n ih =>
    rw [Fin.foldl_succ_last]
    constructor
    · intro h
      rw [Bool.or_eq_true] at h
      cases h with
      | inl h => rw [ih] at h; obtain ⟨j, hj⟩ := h; exact ⟨j.castSucc, hj⟩
      | inr h => exact ⟨Fin.last n, h⟩
    · intro ⟨i, hi⟩
      rw [Bool.or_eq_true]
      rcases Fin.lastCases (motive := fun i => (∃ j : Fin n, i = j.castSucc) ∨ i = Fin.last n)
        (Or.inr rfl) (fun j => Or.inl ⟨j, rfl⟩) i with ⟨j, rfl⟩ | rfl
      · left; rw [ih]; exact ⟨j, hi⟩
      · right; exact hi

private lemma foldl_band_eq_true (n : Nat) (g : Fin n → Bool) :
    (Fin.foldl n (fun acc i => acc && g i) true = true) ↔ (∀ i : Fin n, g i = true) := by
  induction n with
  | zero => simp [Fin.foldl_zero]
  | succ n ih =>
    rw [Fin.foldl_succ_last]; constructor
    · intro h; rw [Bool.and_eq_true] at h; obtain ⟨h1, h2⟩ := h
      rw [ih] at h1; intro i; exact Fin.lastCases h2 (fun j => h1 j) i
    · intro h; rw [Bool.and_eq_true]
      exact ⟨(ih _).mpr (fun j => h j.castSucc), h (Fin.last n)⟩

private lemma AONFor_wireValue_input {N : Nat} [NeZero N] (f : BitString N → Bool)
    (x : BitString N) (j : Fin N) :
    (AONFor f).wireValue x (j.castAdd (2 ^ N)) = x j := by
  have h : (j.castAdd (2 ^ N)).val < N := by simp [Fin.val_castAdd]
  rw [Circuit.wireValue_lt _ _ _ h]
  congr 1

private lemma xor_not_eq_true_iff (a b : Bool) : ((!b).xor a = true) ↔ (a = b) := by
  cases a <;> cases b <;> simp

private lemma mkGate_true {N : Nat} (f : BitString N → Bool) (i : Fin (2 ^ N))
    (hfi : f (fun j => i.val.testBit j.val) = true) :
    AONFor.mkGate f i =
      { op := .and, fanIn := N, arityOk := trivial,
        inputs := fun j => (j.castAdd (2 ^ N)),
        negated := fun j => !(i.val.testBit j.val) } := by
  unfold AONFor.mkGate; simp [hfi]

private lemma mkGate_eval_false {N : Nat} (f : BitString N → Bool) (i : Fin (2 ^ N))
    (wv : BitString (N + 2 ^ N))
    (hfi : f (fun j => i.val.testBit j.val) = false) :
    (AONFor.mkGate f i).eval wv = false := by
  unfold AONFor.mkGate Gate.eval
  simp [hfi, Basis.unboundedAON, AONOp.eval, Fin.foldl_zero]

private lemma mkGate_eval_true_iff {N : Nat} (f : BitString N → Bool) (i : Fin (2 ^ N))
    (wv : BitString (N + 2 ^ N))
    (hfi : f (fun j => i.val.testBit j.val) = true) :
    (AONFor.mkGate f i).eval wv = true ↔
      ∀ j : Fin N, wv (j.castAdd (2 ^ N)) = (i.val.testBit j.val) := by
  rw [mkGate_true f i hfi]
  simp only [Gate.eval, Basis.unboundedAON, AONOp.eval]
  rw [foldl_band_eq_true]
  exact ⟨fun h j => (xor_not_eq_true_iff _ _).mp (h j),
         fun h j => (xor_not_eq_true_iff _ _).mpr (h j)⟩

private lemma exists_testBit_encode (N : Nat) (x : BitString N) :
    ∃ m : Fin (2 ^ N), ∀ j : Fin N, m.val.testBit j.val = x j := by
  induction N with
  | zero => exact ⟨⟨0, Nat.one_pos⟩, fun j => j.elim0⟩
  | succ n ih =>
    obtain ⟨m', hm'⟩ := ih (fun j => x j.castSucc)
    have hm'_bound : m'.val < 2 ^ n := m'.isLt
    refine ⟨⟨m'.val ||| (if x (Fin.last n) then 2 ^ n else 0),
            Nat.or_lt_two_pow (by omega) (by split <;> omega)⟩, ?_⟩
    intro j; simp only
    rw [Nat.testBit_or]
    exact Fin.lastCases
      (by
        simp only [Fin.val_last]
        rw [Nat.testBit_lt_two_pow hm'_bound]
        simp only [Bool.false_or]
        split <;> rename_i h
        · simp [Nat.testBit_two_pow_self, h]
        · simp [Nat.zero_testBit]
          cases hx : x (Fin.last n) <;> simp_all)
      (fun k => by
        simp only [Fin.val_castSucc]
        rw [hm' k]
        split
        · rw [Nat.testBit_two_pow]; simp [Nat.ne_of_gt k.isLt]
        · simp [Nat.zero_testBit])
      j

/-- The single-output DNF circuit correctly computes `f`. -/
theorem AONFor_is_Correct {N : Nat} [NeZero N] (f : BitString N → Bool) :
    (fun (x : BitString 1) => x 0) ∘ (AONFor f).eval = f := by
  funext x
  simp only [Function.comp, Circuit.eval, AONFor_outputs, Gate.eval,
    Basis.unboundedAON, Bool.false_xor, AONOp.eval]
  have key : ∀ i : Fin (2^N), (AONFor f).wireValue x (Fin.natAdd N i) =
      (AONFor.mkGate f i).eval ((AONFor f).wireValue x) := AONFor_wireValue_gate f x
  conv_lhs => arg 2; ext acc i; erw [key i]
  -- Goal: Fin.foldl (2^N) (fun acc i => acc || (mkGate f i).eval (wireValue x)) false = f x
  have h_iff : (Fin.foldl (2 ^ N)
      (fun acc i => acc || (AONFor.mkGate f i).eval ((AONFor f).wireValue x))
      false = true) ↔ (f x = true) := by
    rw [foldl_bor_eq_true]
    constructor
    · -- Some gate fires → f x = true
      rintro ⟨i, hi⟩
      by_cases hfi : f (fun j => i.val.testBit j.val) = true
      · rw [mkGate_eval_true_iff f i _ hfi] at hi
        have hxeq : ∀ j : Fin N, x j = i.val.testBit j.val := by
          intro j; rw [← AONFor_wireValue_input f x j]; exact hi j
        have : f x = f (fun j => i.val.testBit j.val) := congr_arg f (funext hxeq)
        rw [this]; exact hfi
      · have hfi' : f (fun j => i.val.testBit j.val) = false := by
          cases h : f (fun j => i.val.testBit j.val) <;> simp_all
        exact absurd (mkGate_eval_false f i _ hfi' ▸ hi) Bool.false_ne_true
    · -- f x = true → some gate fires
      intro hfx
      obtain ⟨m, hm⟩ := exists_testBit_encode N x
      refine ⟨m, ?_⟩
      have hfm : f (fun j => m.val.testBit j.val) = true := by
        convert hfx using 1; congr 1; funext j; exact hm j
      rw [mkGate_eval_true_iff f m _ hfm]
      intro j; rw [AONFor_wireValue_input f x j]; exact (hm j).symm
  -- Close by Bool case analysis using the ↔
  cases hfx : f x <;>
    cases hfold : Fin.foldl (2 ^ N) (fun acc i =>
      acc || (AONFor.mkGate f i).eval ((AONFor f).wireValue x)) false <;>
    simp_all

/-! ## Multi-output DNF circuit: AONForM -/

/-- Internal gate for the multi-output DNF circuit.
Gate `idx` encodes output bit `j = idx / 2^N` and indicator index `i = idx % 2^N`.
If `f(bitstring i)[j] = true`, it's an AND indicator gate; otherwise a trivially-false OR gate. -/
private def AONForM_j {N M : Nat} (idx : Fin (M * 2 ^ N)) : Fin M :=
  ⟨idx.val / 2 ^ N, Nat.div_lt_of_lt_mul (Nat.mul_comm M (2^N) ▸ idx.isLt)⟩

private def AONForM_i {N : Nat} {M : Nat} (idx : Fin (M * 2 ^ N)) : Fin (2 ^ N) :=
  ⟨idx.val % 2 ^ N, Nat.mod_lt _ (Nat.two_pow_pos N)⟩

private def AONForM_mkGate {N M : Nat} (f : BitString N → BitString M) (idx : Fin (M * 2 ^ N)) :
    Gate Basis.unboundedAON (N + M * 2 ^ N) :=
  if f (fun k => (AONForM_i idx).val.testBit k.val) (AONForM_j idx) then
    { op := .and, fanIn := N, arityOk := trivial,
      inputs := fun k => ⟨k.val, by omega⟩,
      negated := fun k => !((AONForM_i idx).val.testBit k.val) }
  else
    { op := .or, fanIn := 0, arityOk := trivial,
      inputs := Fin.elim0,
      negated := Fin.elim0 }

private lemma AONForM_mkGate_acyclic {N M : Nat} (f : BitString N → BitString M)
    (idx : Fin (M * 2 ^ N)) (k : Fin (AONForM_mkGate f idx).fanIn) :
    ((AONForM_mkGate f idx).inputs k).val < N + idx.val := by
  revert k; unfold AONForM_mkGate
  cases f (fun k => (AONForM_i idx).val.testBit k.val) (AONForM_j idx)
  · intro k; exact Fin.elim0 k
  · intro k; simp; omega

private lemma AONForM_output_bound {N M : Nat} (j : Fin M) (k : Fin (2 ^ N)) :
    N + j.val * 2 ^ N + k.val < N + M * 2 ^ N := by
  have hk := k.isLt
  suffices h : j.val * 2 ^ N + k.val < M * 2 ^ N by omega
  calc j.val * 2 ^ N + k.val
      < j.val * 2 ^ N + 2 ^ N := by omega
    _ = (j.val + 1) * 2 ^ N := by rw [Nat.add_mul]; simp
    _ ≤ M * 2 ^ N := Nat.mul_le_mul_right _ (by omega)

/-- Multi-output DNF circuit computing `f : BitString N → BitString M`.

For each output bit `j` and each of the `2^N` possible inputs, there is
an indicator AND gate (or a trivially-false gate). Each output OR gate
disjoins the `2^N` gates for its output bit. -/
def AONForM {N M : Nat} [NeZero N] [NeZero M] (f : BitString N → BitString M) :
    Circuit Basis.unboundedAON N M (M * 2 ^ N) where
  gates := AONForM_mkGate f
  outputs j :=
    { op := .or, fanIn := 2 ^ N, arityOk := trivial,
      inputs := fun k => ⟨N + j.val * 2 ^ N + k.val, AONForM_output_bound j k⟩,
      negated := fun _ => false }
  acyclic := AONForM_mkGate_acyclic f

private lemma AONForM_wireValue_input {N M : Nat} [NeZero N] [NeZero M]
    (f : BitString N → BitString M) (x : BitString N) (k : Fin N) :
    (AONForM f).wireValue x ⟨k.val, by omega⟩ = x k := by
  have h : (⟨k.val, by omega⟩ : Fin (N + M * 2 ^ N)).val < N := k.isLt
  rw [Circuit.wireValue_lt _ _ _ h]

private lemma AONForM_wireValue_gate {N M : Nat} [NeZero N] [NeZero M]
    (f : BitString N → BitString M) (x : BitString N) (idx : Fin (M * 2 ^ N)) :
    (AONForM f).wireValue x ⟨N + idx.val, by omega⟩ =
      (AONForM_mkGate f idx).eval ((AONForM f).wireValue x) := by
  have hge : ¬ ((⟨N + idx.val, by omega⟩ : Fin (N + M * 2 ^ N)).val < N) := by simp
  rw [Circuit.wireValue_ge _ _ _ hge]
  congr 1; simp only [AONForM]; congr 1; exact Fin.ext (by simp)

private lemma AONForM_mkGate_eval_false {N M : Nat}
    (f : BitString N → BitString M) (idx : Fin (M * 2 ^ N))
    (wv : BitString (N + M * 2 ^ N))
    (hfi : f (fun k => (AONForM_i idx).val.testBit k.val) (AONForM_j idx) = false) :
    (AONForM_mkGate f idx).eval wv = false := by
  unfold AONForM_mkGate Gate.eval
  simp [hfi, Basis.unboundedAON, AONOp.eval, Fin.foldl_zero]

private lemma AONForM_mkGate_eval_true_iff {N M : Nat}
    (f : BitString N → BitString M) (idx : Fin (M * 2 ^ N))
    (wv : BitString (N + M * 2 ^ N))
    (hfi : f (fun k => (AONForM_i idx).val.testBit k.val) (AONForM_j idx) = true) :
    (AONForM_mkGate f idx).eval wv = true ↔
      ∀ k : Fin N, wv ⟨k.val, by omega⟩ = ((AONForM_i idx).val.testBit k.val) := by
  have hmk : AONForM_mkGate f idx =
    { op := .and, fanIn := N, arityOk := trivial,
      inputs := fun k => ⟨k.val, by omega⟩,
      negated := fun k => !((AONForM_i idx).val.testBit k.val) } := by
    unfold AONForM_mkGate; simp [hfi]
  rw [hmk]; simp only [Gate.eval, Basis.unboundedAON, AONOp.eval]
  rw [foldl_band_eq_true]
  exact ⟨fun h k => (xor_not_eq_true_iff _ _).mp (h k),
         fun h k => (xor_not_eq_true_iff _ _).mpr (h k)⟩

-- Helper: relate index `j * 2^N + k` to `AONForM_i` and `AONForM_j`
private lemma AONForM_i_of_add {N M : Nat} (j : Fin M) (k : Fin (2 ^ N))
    (h : j.val * 2 ^ N + k.val < M * 2 ^ N) :
    AONForM_i (⟨j.val * 2 ^ N + k.val, h⟩ : Fin (M * 2 ^ N)) = k := by
  ext; simp [AONForM_i, Nat.mod_eq_of_lt k.isLt]

private lemma AONForM_j_of_add {N M : Nat} (j : Fin M) (k : Fin (2 ^ N))
    (h : j.val * 2 ^ N + k.val < M * 2 ^ N) :
    AONForM_j (⟨j.val * 2 ^ N + k.val, h⟩ : Fin (M * 2 ^ N)) = j := by
  ext; simp only [AONForM_j, Fin.val_mk]
  rw [show j.val * 2^N + k.val = k.val + 2^N * j.val from by rw [Nat.mul_comm j.val]; omega]
  rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos N), Nat.div_eq_of_lt k.isLt]; simp

-- The idx corresponding to output j and indicator k
private def AONForM_idx {N M : Nat} (j : Fin M) (k : Fin (2 ^ N)) :
    Fin (M * 2 ^ N) :=
  ⟨j.val * 2 ^ N + k.val, by
    have := AONForM_output_bound (N := N) j k; omega⟩

private lemma AONForM_idx_i {N M : Nat} (j : Fin M) (k : Fin (2 ^ N)) :
    AONForM_i (AONForM_idx j k) = k :=
  AONForM_i_of_add j k _

private lemma AONForM_idx_j {N M : Nat} (j : Fin M) (k : Fin (2 ^ N)) :
    AONForM_j (AONForM_idx j k) = j :=
  AONForM_j_of_add j k _

/-- The multi-output DNF circuit correctly computes `f`. -/
theorem AONForM_is_Correct {N M : Nat} [NeZero N] [NeZero M]
    (f : BitString N → BitString M) :
    (AONForM f).eval = f := by
  funext x j
  -- Unfold eval to get the output gate evaluation
  change ((AONForM f).outputs j).eval ((AONForM f).wireValue x) = f x j
  simp only [AONForM, Gate.eval, Basis.unboundedAON, Bool.false_xor, AONOp.eval]
  -- Now the goal involves Fin.foldl over wireValues at output wires
  -- We need to connect wireValue to mkGate eval
  have key : ∀ k : Fin (2^N),
    (AONForM f).wireValue x ⟨N + j.val * 2 ^ N + k.val, AONForM_output_bound j k⟩ =
    (AONForM_mkGate f (AONForM_idx j k)).eval ((AONForM f).wireValue x) := by
    intro k
    have h := AONForM_wireValue_gate f x (AONForM_idx j k)
    simp only [AONForM_idx] at h
    simp only [Nat.add_assoc] at h ⊢
    exact h
  -- Rewrite the foldl body
  suffices hsuff : Fin.foldl (2 ^ N) (fun acc k =>
    acc || (AONForM_mkGate f (AONForM_idx j k)).eval ((AONForM f).wireValue x)) false = f x j by
    convert hsuff using 2
    ext acc k
    congr 1; exact key k
  -- Now prove the suffices
  have h_iff : (Fin.foldl (2 ^ N) (fun acc k =>
    acc || (AONForM_mkGate f (AONForM_idx j k)).eval ((AONForM f).wireValue x)) false = true) ↔
    (f x j = true) := by
    rw [foldl_bor_eq_true]
    constructor
    · -- Some gate fires → f x j = true
      rintro ⟨k, hk⟩
      -- Use AONForM_idx_i and AONForM_idx_j to simplify
      have hi : AONForM_i (AONForM_idx j k) = k := AONForM_idx_i j k
      have hj' : AONForM_j (AONForM_idx j k) = j := AONForM_idx_j j k
      by_cases hfk : f (fun p => (AONForM_i (AONForM_idx j k)).val.testBit p.val)
        (AONForM_j (AONForM_idx j k)) = true
      · rw [AONForM_mkGate_eval_true_iff f _ _ hfk] at hk
        rw [hi, hj'] at hfk
        have hxeq : ∀ p : Fin N, x p = k.val.testBit p.val := by
          intro p; rw [← AONForM_wireValue_input f x p]
          rw [hi] at hk; exact hk p
        have : f x j = f (fun p => k.val.testBit p.val) j := congr_arg (· j)
          (congr_arg f (funext hxeq))
        rw [this]; exact hfk
      · have hfk' : f (fun p => (AONForM_i (AONForM_idx j k)).val.testBit p.val)
            (AONForM_j (AONForM_idx j k)) = false := by
          cases h : f (fun p => (AONForM_i (AONForM_idx j k)).val.testBit p.val)
            (AONForM_j (AONForM_idx j k)) <;> simp_all
        exact absurd (AONForM_mkGate_eval_false f _ _ hfk' ▸ hk) Bool.false_ne_true
    · -- f x j = true → some gate fires
      intro hfx
      obtain ⟨m, hm⟩ := exists_testBit_encode N x
      refine ⟨m, ?_⟩
      have hfm : f (fun p => (AONForM_i (AONForM_idx j m)).val.testBit p.val)
        (AONForM_j (AONForM_idx j m)) = true := by
        rw [AONForM_idx_i, AONForM_idx_j]
        convert hfx using 1; congr 1; funext p; exact hm p
      rw [AONForM_mkGate_eval_true_iff f _ _ hfm]
      intro p; rw [AONForM_wireValue_input f x p]
      rw [AONForM_idx_i]; exact (hm p).symm
  -- Close by Bool case analysis
  cases hfx : f x j <;>
    cases hfold : Fin.foldl (2 ^ N) (fun acc k =>
      acc || (AONForM_mkGate f (AONForM_idx j k)).eval ((AONForM f).wireValue x)) false <;>
    simp_all

instance : CompleteBasis Basis.unboundedAON where
  complete f := ⟨_, AONForM f, AONForM_is_Correct f⟩

end CircuitComplexity
