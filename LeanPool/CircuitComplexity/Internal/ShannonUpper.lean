/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import LeanPool.CircuitComplexity.AON.Defs
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Positivity

/-! # Internal: Shannon Upper Bound Construction

The Shannon (1949) upper bound: every Boolean function on `N` variables
can be computed by a fan-in-2 AND/OR circuit of size at most `C * 2^N / N`,
for a fixed constant `C` and all sufficiently large `N`.

This is the full-column-library variant (C = 18). The tighter
`(1 + o(1)) · 2^N / N` bound due to Lupanov (1958) uses column grouping
and is not yet formalized.

## Construction

Split `N` inputs into `k = ⌊log₂ N⌋ - 1` address variables and
`q = N - k` data variables. Decompose any `f : {0,1}^N → {0,1}` as
`f(a,y) = ⋁ᵧ [mintermᵧ(data) ∧ colᵧ(addr)]` where `colᵧ(a) = f(a,y)`.

Build shared minterm trees for both variable groups, a pattern library
for column functions, AND/OR combining layers. Total ≤ `18 · 2^N / N`
gates for `N ≥ 16`.
-/

namespace CircuitComplexity


namespace ShannonUpper

/-! ## Parameters -/

/-- Number of address variables: `⌊log₂ N⌋ - 1`. -/
def addrBits (N : Nat) : Nat := Nat.log 2 N - 1

/-- Number of data variables: `N - addrBits N`. -/
def dataBits (N : Nat) : Nat := N - addrBits N

/-! ## Gate Construction Helpers -/

/-- Build a fan-in-2 gate bundled with an acyclicity proof. -/
private def mkGate2' (op : AONOp) {W : Nat} (w₀ w₁ : Fin W) (n₀ n₁ : Bool)
    (bound : Nat) (hw₀ : w₀.val < bound) (hw₁ : w₁.val < bound) :
    { g : Gate Basis.andOr2 W // ∀ k : Fin g.fanIn, (g.inputs k).val < bound } :=
  ⟨{ op := op, fanIn := 2, arityOk := rfl,
     inputs := fun i => if i.val = 0 then w₀ else w₁,
     negated := fun i => if i.val = 0 then n₀ else n₁ },
   fun k => by dsimp; split_ifs <;> assumption⟩

/-- Remap a wire from c₂'s space into the combined space. -/
private def remap₂ (N G₁ G₂ : Nat) (w : Fin (N + G₂)) : Fin (N + (G₁ + G₂ + 2)) :=
  if h : w.val < N then ⟨w.val, by omega⟩
  else ⟨w.val + G₁ + 1, by have := w.isLt; omega⟩

private lemma remap₂_val_lt (N G₁ G₂ : Nat) (w : Fin (N + G₂))
    (bound : Nat) (hb : G₁ + 1 ≤ bound) (hw : w.val < N + (bound - G₁ - 1)) :
    (remap₂ N G₁ G₂ w).val < N + bound := by
  unfold remap₂; split_ifs <;> dsimp <;> omega

private def gw (idx : Nat) {W : Nat} (g : Gate Basis.andOr2 W)
    (_ : idx < 2 := by omega) : Fin W :=
  g.inputs ⟨idx, by rw [andOr2_fanIn]; omega⟩
private def gn (idx : Nat) {W : Nat} (g : Gate Basis.andOr2 W)
    (_ : idx < 2 := by omega) : Bool :=
  g.negated ⟨idx, by rw [andOr2_fanIn]; omega⟩

/-! ## Binary Circuit Composition -/

/-- Gate + acyclicity proof for the binary composition, bundled as a subtype. -/
private def binopGWP {N G₁ G₂ : Nat} [NeZero N]
    (c₁ : Circuit Basis.andOr2 N 1 G₁) (c₂ : Circuit Basis.andOr2 N 1 G₂)
    (i : Fin (G₁ + G₂ + 2)) :
    { g : Gate Basis.andOr2 (N + (G₁ + G₂ + 2)) //
      ∀ k : Fin g.fanIn, (g.inputs k).val < N + i.val } :=
  if h₁ : i.val < G₁ then
    let g := c₁.gates ⟨i.val, h₁⟩
    mkGate2' g.op ⟨(gw 0 g).val, by omega⟩ ⟨(gw 1 g).val, by omega⟩ (gn 0 g) (gn 1 g)
      (N + i.val)
      (show (gw 0 g).val < _ from c₁.acyclic ⟨_, h₁⟩ ⟨0, by rw [andOr2_fanIn]; omega⟩)
      (show (gw 1 g).val < _ from c₁.acyclic ⟨_, h₁⟩ ⟨1, by rw [andOr2_fanIn]; omega⟩)
  else if h₂ : i.val = G₁ then
    let g := c₁.outputs 0
    mkGate2' g.op ⟨(gw 0 g).val, by omega⟩ ⟨(gw 1 g).val, by omega⟩ (gn 0 g) (gn 1 g)
      (N + i.val)
      (show (gw 0 g).val < _ by have := (gw 0 g).isLt; omega)
      (show (gw 1 g).val < _ by have := (gw 1 g).isLt; omega)
  else if h₃ : i.val < G₁ + 1 + G₂ then
    let g := c₂.gates ⟨i.val - G₁ - 1, by omega⟩
    mkGate2' g.op (remap₂ N G₁ G₂ (gw 0 g)) (remap₂ N G₁ G₂ (gw 1 g)) (gn 0 g) (gn 1 g)
      (N + i.val)
      (remap₂_val_lt N G₁ G₂ (gw 0 g) i.val (by omega)
        (c₂.acyclic ⟨i.val-G₁-1, by omega⟩ ⟨0, by rw [andOr2_fanIn]; omega⟩))
      (remap₂_val_lt N G₁ G₂ (gw 1 g) i.val (by omega)
        (c₂.acyclic ⟨i.val-G₁-1, by omega⟩ ⟨1, by rw [andOr2_fanIn]; omega⟩))
  else
    let g := c₂.outputs 0
    mkGate2' g.op (remap₂ N G₁ G₂ (gw 0 g)) (remap₂ N G₁ G₂ (gw 1 g)) (gn 0 g) (gn 1 g)
      (N + i.val)
      (remap₂_val_lt N G₁ G₂ (gw 0 g) i.val (by omega)
        (show (gw 0 g).val < _ by have := (gw 0 g).isLt; omega))
      (remap₂_val_lt N G₁ G₂ (gw 1 g) i.val (by omega)
        (show (gw 1 g).val < _ by have := (gw 1 g).isLt; omega))

/-- Compose two circuits with a binary AND/OR. -/
def binopCircuit (op : AONOp) {N G₁ G₂ : Nat} [NeZero N]
    (c₁ : Circuit Basis.andOr2 N 1 G₁) (c₂ : Circuit Basis.andOr2 N 1 G₂) :
    Circuit Basis.andOr2 N 1 (G₁ + G₂ + 2) where
  gates i := (binopGWP c₁ c₂ i).val
  outputs _ :=
    { op := op, fanIn := 2, arityOk := rfl,
      inputs := fun j => if j.val = 0 then ⟨N + G₁, by omega⟩ else ⟨N + G₁ + G₂ + 1, by omega⟩,
      negated := fun _ => false }
  acyclic i k := (binopGWP c₁ c₂ i).property k

private theorem mkGate2'_eval (o : AONOp) {W : Nat} (w₀ w₁ : Fin W) (n₀ n₁ : Bool)
    (b : Nat) (h₀ : w₀.val < b) (h₁ : w₁.val < b)
    (wv : BitString W) :
    (mkGate2' o w₀ w₁ n₀ n₁ b h₀ h₁).val.eval wv =
    match o with
    | .and => (n₀ ^^ wv w₀) && (n₁ ^^ wv w₁)
    | .or => (n₀ ^^ wv w₀) || (n₁ ^^ wv w₁) := by
  simp only [mkGate2', Gate.eval, Basis.andOr2]
  cases o <;> simp [AONOp.eval, Fin.foldl_succ_last, Fin.foldl_zero]

private theorem andOr2_gate_eval_two_inputs {W : Nat}
    (g : Gate Basis.andOr2 W) (wv : BitString W) :
    g.eval wv =
    match g.op with
    | .and => (gn 0 g ^^ wv (gw 0 g)) && (gn 1 g ^^ wv (gw 1 g))
    | .or => (gn 0 g ^^ wv (gw 0 g)) || (gn 1 g ^^ wv (gw 1 g)) := by
  have hf := andOr2_fanIn g
  simp only [Gate.eval, Basis.andOr2, gw, gn]
  cases g.op <;> simp_all [AONOp.eval, Fin.foldl_succ_last, Fin.foldl_zero, Fin.cast]

private theorem binop_wireValue_c₁ {N G₁ G₂ : Nat} [NeZero N]
    (op : AONOp)
    (c₁ : Circuit Basis.andOr2 N 1 G₁) (c₂ : Circuit Basis.andOr2 N 1 G₂)
    (x : BitString N) (w : Fin (N + G₁))
    (hw : w.val < N + G₁) :
    (binopCircuit op c₁ c₂).wireValue x ⟨w.val, by omega⟩ = c₁.wireValue x w := by
  have key : ∀ n : Nat, ∀ (hn₁ : n < N + (G₁ + G₂ + 2)) (hn₂ : n < N + G₁),
      (binopCircuit op c₁ c₂).wireValue x ⟨n, hn₁⟩ = c₁.wireValue x ⟨n, hn₂⟩ := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn₁ hn₂
      by_cases hlt : n < N
      · rw [Circuit.wireValue_lt _ _ ⟨n, hn₁⟩ (show (⟨n, hn₁⟩ : Fin _).val < N from hlt),
             Circuit.wireValue_lt _ _ ⟨n, hn₂⟩ (show (⟨n, hn₂⟩ : Fin _).val < N from hlt)]
      · rw [Circuit.wireValue_ge _ _ _ hlt, Circuit.wireValue_ge _ _ _ hlt]
        have hg : n - N < G₁ := by omega
        -- binopGWP takes first branch since n - N < G₁
        -- Change goal to use binopGWP
        change (binopGWP c₁ c₂ ⟨n - N, _⟩).val.eval _ = _
        -- Unfold binopGWP for the first branch
        simp only [binopGWP, dif_pos hg]
        rw [mkGate2'_eval, andOr2_gate_eval_two_inputs]
        have hacyc0 : (gw 0 (c₁.gates ⟨n - N, hg⟩)).val < n := by
          have := c₁.acyclic ⟨_, hg⟩ ⟨0, by rw [andOr2_fanIn]; omega⟩; simp [gw] at this ⊢; omega
        have hacyc1 : (gw 1 (c₁.gates ⟨n - N, hg⟩)).val < n := by
          have := c₁.acyclic ⟨_, hg⟩ ⟨1, by rw [andOr2_fanIn]; omega⟩; simp [gw] at this ⊢; omega
        cases (c₁.gates ⟨n - N, hg⟩).op <;> simp only <;> congr 1 <;> congr 1
        · exact ih _ hacyc0 (by omega) (by omega)
        · exact ih _ hacyc1 (by omega) (by omega)
        · exact ih _ hacyc0 (by omega) (by omega)
        · exact ih _ hacyc1 (by omega) (by omega)
  have := key w.val (by omega) hw
  convert this using 2

private theorem binop_wireValue_c₂ {N G₁ G₂ : Nat} [NeZero N]
    (op : AONOp)
    (c₁ : Circuit Basis.andOr2 N 1 G₁) (c₂ : Circuit Basis.andOr2 N 1 G₂)
    (x : BitString N) (w : Fin (N + G₂)) :
    (binopCircuit op c₁ c₂).wireValue x (remap₂ N G₁ G₂ w) = c₂.wireValue x w := by
  have key : ∀ n : Nat, ∀ (hn : n < N + G₂),
      (binopCircuit op c₁ c₂).wireValue x (remap₂ N G₁ G₂ ⟨n, hn⟩) =
        c₂.wireValue x ⟨n, hn⟩ := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn
      by_cases hlt : n < N
      · -- Input wire: remap₂ preserves it
        simp only [remap₂, dif_pos hlt]
        rw [Circuit.wireValue_lt _ _ _ hlt, Circuit.wireValue_lt _ _ _ hlt]
      · -- Gate wire: remap₂ shifts by G₁ + 1
        simp only [remap₂, dif_neg hlt]
        have hge : ¬(n + G₁ + 1 < N) := by omega
        rw [Circuit.wireValue_ge _ _ _ hge, Circuit.wireValue_ge _ _ _ hlt]
        have hg₂ : n - N < G₂ := by omega
        have hidx : n + G₁ + 1 - N = n - N + G₁ + 1 := by omega
        -- Change to binopGWP form
        change (binopGWP c₁ c₂ ⟨n + G₁ + 1 - N, _⟩).val.eval _ = _
        -- Unfold binopGWP for the third branch
        have hb1 : ¬(n + G₁ + 1 - N < G₁) := by omega
        have hb2 : ¬(n + G₁ + 1 - N = G₁) := by omega
        have hb3 : n + G₁ + 1 - N < G₁ + 1 + G₂ := by omega
        simp only [binopGWP, dif_neg hb1, dif_neg hb2, dif_pos hb3]
        rw [mkGate2'_eval, andOr2_gate_eval_two_inputs]
        -- Simplify gate index
        have : (⟨n + G₁ + 1 - N - G₁ - 1, by omega⟩ : Fin G₂) = ⟨n - N, hg₂⟩ := by
          ext; simp; omega
        simp only [this]
        have hacyc0 : (gw 0 (c₂.gates ⟨n - N, hg₂⟩)).val < n := by
          have := c₂.acyclic ⟨_, hg₂⟩ ⟨0, by rw [andOr2_fanIn]; omega⟩; simp [gw] at this ⊢; omega
        have hacyc1 : (gw 1 (c₂.gates ⟨n - N, hg₂⟩)).val < n := by
          have := c₂.acyclic ⟨_, hg₂⟩ ⟨1, by rw [andOr2_fanIn]; omega⟩; simp [gw] at this ⊢; omega
        cases (c₂.gates ⟨n - N, hg₂⟩).op <;> simp only <;> congr 1 <;> congr 1
        · exact ih _ hacyc0 (by omega)
        · exact ih _ hacyc1 (by omega)
        · exact ih _ hacyc0 (by omega)
        · exact ih _ hacyc1 (by omega)
  exact key w.val w.isLt

/-- `binopCircuit` correctly computes the OR of two circuits' outputs.

    The output gate of `binopCircuit` applies OR to wires `N + G₁` and
    `N + G₁ + G₂ + 1`, which replicate the output gates of c₁ and c₂.
    The proof shows that wire values in the combined circuit agree with
    wire values in the original circuits (via `binop_wireValue_c₁` and
    `binop_wireValue_c₂`), then combines. -/
theorem binopCircuit_or_correct {N G₁ G₂ : Nat} [NeZero N]
    (c₁ : Circuit Basis.andOr2 N 1 G₁) (c₂ : Circuit Basis.andOr2 N 1 G₂)
    (f₁ f₂ : BitString N → Bool)
    (hf₁ : (fun x => (c₁.eval x) 0) = f₁)
    (hf₂ : (fun x => (c₂.eval x) 0) = f₂) :
    (fun x => ((binopCircuit AONOp.or c₁ c₂).eval x) 0) =
    fun x => f₁ x || f₂ x := by
  funext x
  simp only [← hf₁, ← hf₂, Circuit.eval]
  set cb := binopCircuit AONOp.or c₁ c₂
  -- Wire N + G₁ corresponds to c₁'s output gate (gate G₁ in combined circuit)
  have hw1 : cb.wireValue x ⟨N + G₁, by omega⟩ =
      (c₁.outputs 0).eval (c₁.wireValue x) := by
    rw [Circuit.wireValue_ge _ _ _ (show ¬(N + G₁ < N) by omega)]
    change (binopGWP c₁ c₂ ⟨_, _⟩).val.eval _ = _
    have hfin : (⟨N + G₁ - N, (by omega : N + G₁ - N < G₁ + G₂ + 2)⟩ : Fin (G₁ + G₂ + 2)) =
        ⟨G₁, by omega⟩ := Fin.ext (show N + G₁ - N = G₁ by omega)
    rw [hfin]
    simp only [binopGWP, show ¬(G₁ < G₁) from Nat.lt_irrefl G₁, dite_false, dite_true]
    rw [mkGate2'_eval, andOr2_gate_eval_two_inputs]
    cases (c₁.outputs 0).op <;> simp only <;> congr 1 <;> congr 1
    all_goals (apply binop_wireValue_c₁; exact (gw _ (c₁.outputs 0)).isLt)
  -- Wire N + G₁ + G₂ + 1 corresponds to c₂'s output gate
  have hw2 : cb.wireValue x ⟨N + G₁ + G₂ + 1, by omega⟩ =
      (c₂.outputs 0).eval (c₂.wireValue x) := by
    rw [Circuit.wireValue_ge _ _ _ (show ¬(N + G₁ + G₂ + 1 < N) by omega)]
    change (binopGWP c₁ c₂ ⟨_, _⟩).val.eval _ = _
    have hfin :
      (⟨N + G₁ + G₂ + 1 - N, (by omega : N + G₁ + G₂ + 1 - N < G₁ + G₂ + 2)⟩ : Fin (G₁ + G₂ + 2)) =
        ⟨G₁ + G₂ + 1, by omega⟩ := Fin.ext (show N + G₁ + G₂ + 1 - N = G₁ + G₂ + 1 by omega)
    rw [hfin]
    simp only [binopGWP,
      show ¬(G₁ + G₂ + 1 < G₁) by omega,
      show ¬(G₁ + G₂ + 1 = G₁) by omega,
      show ¬(G₁ + G₂ + 1 < G₁ + 1 + G₂) by omega,
      dite_false]
    rw [mkGate2'_eval, andOr2_gate_eval_two_inputs]
    cases (c₂.outputs 0).op <;> simp only <;> congr 1 <;> congr 1
    all_goals (apply binop_wireValue_c₂)
  -- The output gate of cb applies OR to these two wires
  change (cb.outputs 0).eval (cb.wireValue x) = _
  rw [andOr2_gate_eval_two_inputs (g := cb.outputs 0)]
  -- The output gate has op = .or, negated = false, inputs 0 = N+G₁, inputs 1 = N+G₁+G₂+1
  have hcb_op : (cb.outputs 0).op = AONOp.or := rfl
  have hcb_gn0 : gn 0 (cb.outputs 0) = false := rfl
  have hcb_gn1 : gn 1 (cb.outputs 0) = false := rfl
  have hcb_gw0 : gw 0 (cb.outputs 0) = ⟨N + G₁, by omega⟩ := by
    simp [gw, cb, binopCircuit]
  have hcb_gw1 : gw 1 (cb.outputs 0) = ⟨N + G₁ + G₂ + 1, by omega⟩ := by
    simp [gw, cb, binopCircuit]
  rw [hcb_op, hcb_gn0, hcb_gn1, hcb_gw0, hcb_gw1, Bool.false_xor, Bool.false_xor]
  exact congr_arg₂ (· || ·) hw1 hw2

/-! ## Arithmetic -/

/-! ### Nat.log helpers -/

private theorem log_ge_one (N : Nat) (hN : 16 ≤ N) : 1 ≤ Nat.log 2 N :=
  Nat.le_log_of_pow_le (by omega) (by omega)

private theorem log_lt_N (N : Nat) (hN : 16 ≤ N) : Nat.log 2 N < N :=
  Nat.log_lt_of_lt_pow (by omega) (@Nat.lt_pow_self N 2 (by omega))

theorem addrBits_ge_three (N : Nat) (hN : 16 ≤ N) : 3 ≤ addrBits N := by
  unfold addrBits
  have := Nat.le_log_of_pow_le (by omega : 1 < 2) (show 2 ^ 4 ≤ N by omega)
  omega

theorem dataBits_pos (N : Nat) (hN : 16 ≤ N) : 0 < dataBits N := by
  unfold dataBits addrBits; have := log_lt_N N hN; omega

theorem dataBits_ge_two (N : Nat) (hN : 16 ≤ N) : 2 ≤ dataBits N := by
  unfold dataBits addrBits
  have : Nat.log 2 N < N := log_lt_N N hN
  have : 4 ≤ Nat.log 2 N := Nat.le_log_of_pow_le (by omega) (by omega)
  omega

/-! ### Key identities -/

private theorem addr_le_N (N : Nat) (hN : 16 ≤ N) : addrBits N ≤ N := by
  unfold addrBits; have := log_lt_N N hN; omega

private theorem addr_data_sum (N : Nat) (hN : 16 ≤ N) :
    dataBits N + addrBits N = N := by
  unfold dataBits; have := addr_le_N N hN; omega

private theorem pow_split (N : Nat) (hN : 16 ≤ N) :
    2 ^ dataBits N * 2 ^ addrBits N = 2 ^ N := by
  rw [← Nat.pow_add]; congr 1; exact addr_data_sum N hN

private theorem two_mul_pow_addr_le (N : Nat) (hN : 16 ≤ N) :
    2 * 2 ^ addrBits N ≤ N := by
  unfold addrBits
  have hlog := log_ge_one N hN
  have : 2 * 2 ^ (Nat.log 2 N - 1) = 2 ^ Nat.log 2 N := by
    conv_rhs => rw [show Nat.log 2 N = (Nat.log 2 N - 1) + 1 from by omega]
    rw [Nat.pow_succ]; ring
  rw [this]; exact Nat.pow_log_le_self 2 (by omega)

private theorem n_lt_four_pow_addr (N : Nat) (hN : 16 ≤ N) :
    N < 4 * 2 ^ addrBits N := by
  unfold addrBits
  have hlog := log_ge_one N hN
  have : 4 * 2 ^ (Nat.log 2 N - 1) = 2 ^ (Nat.log 2 N + 1) := by
    conv_rhs => rw [show Nat.log 2 N + 1 = (Nat.log 2 N - 1) + 2 from by omega]
    rw [Nat.pow_add]; omega
  rw [this]; exact Nat.lt_pow_succ_log_self (by omega) N

/-! ### N² ≤ 2^N for N ≥ 16 -/

private theorem two_n_plus_one_le (N : Nat) (hN : 4 ≤ N) : 2 * N + 1 ≤ 2 ^ N := by
  induction N with
  | zero => omega
  | succ n ih =>
    cases Nat.lt_or_ge n 4 with
    | inl h => interval_cases n <;> omega
    | inr h =>
      have := ih (by omega)
      have := @Nat.lt_pow_self n 2 (by omega)
      have : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by ring
      omega

private theorem sq_le_pow (N : Nat) (hN : 16 ≤ N) : N * N ≤ 2 ^ N := by
  induction N with
  | zero => omega
  | succ n ih =>
    cases Nat.lt_or_ge n 16 with
    | inl h => interval_cases n <;> omega
    | inr h =>
      have := ih (by omega)
      have := two_n_plus_one_le n (by omega)
      have hsq : (n + 1) * (n + 1) = n * n + 2 * n + 1 := by ring
      have : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by ring
      omega

/-! ### Term-by-term bounds -/

private theorem term1 (N : Nat) (hN : 16 ≤ N) :
    4 * 2 ^ dataBits N * N ≤ 16 * 2 ^ N := by
  have hlt := n_lt_four_pow_addr N hN
  have hsplit := pow_split N hN
  have : 4 * 2 ^ dataBits N * N ≤ 4 * 2 ^ dataBits N * (4 * 2 ^ addrBits N) :=
    Nat.mul_le_mul_left _ (by omega)
  nlinarith [this, hsplit]

private theorem term2 (N : Nat) (hN : 16 ≤ N) :
    2 * 2 ^ addrBits N * N ≤ 2 ^ N := by
  calc 2 * 2 ^ addrBits N * N
      ≤ N * N := by apply Nat.mul_le_mul_right; exact two_mul_pow_addr_le N hN
    _ ≤ 2 ^ N := sq_le_pow N hN

private theorem pow_ge_four_mul (k : Nat) (hk : 4 ≤ k) : 4 * k ≤ 2 ^ k := by
  induction k with
  | zero => omega
  | succ n ih =>
    cases Nat.lt_or_ge n 4 with
    | inl h => interval_cases n <;> omega
    | inr h =>
      have := ih (by omega)
      have := @Nat.lt_pow_self n 2 (by omega)
      have : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by ring
      omega

private theorem log_le_quarter (N : Nat) (hN : 16 ≤ N) : 4 * Nat.log 2 N ≤ N := by
  have hlog4 : 4 ≤ Nat.log 2 N := Nat.le_log_of_pow_le (by omega) (by omega)
  calc 4 * Nat.log 2 N
      ≤ 2 ^ Nat.log 2 N := pow_ge_four_mul (Nat.log 2 N) hlog4
    _ ≤ N := Nat.pow_log_le_self 2 (by omega)

private theorem pow_addr_plus_addr_le (N : Nat) (hN : 16 ≤ N) :
    2 ^ addrBits N + addrBits N + (Nat.log 2 N + 1) ≤ N := by
  unfold addrBits
  have hlog1 : 1 ≤ Nat.log 2 N := Nat.le_log_of_pow_le (by omega) (by omega)
  have : 2 * 2 ^ (Nat.log 2 N - 1) = 2 ^ Nat.log 2 N := by
    conv_rhs => rw [show Nat.log 2 N = (Nat.log 2 N - 1) + 1 from by omega]
    rw [Nat.pow_succ]; ring
  have : 2 * 2 ^ (Nat.log 2 N - 1) ≤ N := by
    rw [this]; exact Nat.pow_log_le_self 2 (by omega)
  have := log_le_quarter N hN
  omega

private theorem term3 (N : Nat) (hN : 16 ≤ N) :
    2 ^ (2 ^ addrBits N + addrBits N) * N ≤ 2 ^ N := by
  have hkey := pow_addr_plus_addr_le N hN
  have hsub : Nat.log 2 N + 1 ≤ N - (2 ^ addrBits N + addrBits N) := by omega
  have hN_lt : N < 2 ^ (N - (2 ^ addrBits N + addrBits N)) :=
    calc N < 2 ^ (Nat.log 2 N + 1) := Nat.lt_pow_succ_log_self (by omega) N
      _ ≤ 2 ^ (N - (2 ^ addrBits N + addrBits N)) := Nat.pow_le_pow_right (by omega) hsub
  have hsplit : 2 ^ (2 ^ addrBits N + addrBits N) *
      2 ^ (N - (2 ^ addrBits N + addrBits N)) = 2 ^ N := by
    rw [← Nat.pow_add]; congr 1; omega
  have : 2 ^ (2 ^ addrBits N + addrBits N) * N ≤
      2 ^ (2 ^ addrBits N + addrBits N) * 2 ^ (N - (2 ^ addrBits N + addrBits N)) :=
    Nat.mul_le_mul_left _ (by omega)
  omega

theorem shannon_arithmetic (N : Nat) (hN : 16 ≤ N) :
    (4 * 2 ^ dataBits N + 2 * 2 ^ addrBits N +
      2 ^ (2 ^ addrBits N + addrBits N)) * N ≤ 18 * 2 ^ N := by
  have h1 := term1 N hN
  have h2 := term2 N hN
  have h3 := term3 N hN
  nlinarith

theorem shannon_size_le (N : Nat) (hN : 16 ≤ N) (G : Nat)
    (hG : G + 1 ≤ 4 * 2 ^ dataBits N + 2 * 2 ^ addrBits N +
            2 ^ (2 ^ addrBits N + addrBits N)) :
    G + 1 ≤ 18 * 2 ^ N / N := by
  have hNpos : 0 < N := by omega
  apply (Nat.le_div_iff_mul_le hNpos).mpr
  calc (G + 1) * N
      ≤ (4 * 2 ^ dataBits N + 2 * 2 ^ addrBits N +
          2 ^ (2 ^ addrBits N + addrBits N)) * N := by
        apply Nat.mul_le_mul_right; exact hG
    _ ≤ 18 * 2 ^ N := shannon_arithmetic N hN

/-! ## Circuit Construction -/

/-! ### Gate construction helper -/

private def mkG (W : Nat) (op : AONOp) (w0 w1 : Nat) (n0 n1 : Bool)
    (hw0 : w0 < W) (hw1 : w1 < W)
    (bound : Nat) (hb0 : w0 < bound) (hb1 : w1 < bound) :
    { g : Gate Basis.andOr2 W // ∀ j : Fin g.fanIn, (g.inputs j).val < bound } :=
  ⟨{ op := op, fanIn := 2, arityOk := rfl,
     inputs := fun j => if j.val = 0 then ⟨w0, hw0⟩ else ⟨w1, hw1⟩,
     negated := fun j => if j.val = 0 then n0 else n1 },
   fun j => by dsimp; split_ifs <;> assumption⟩

/-! ### Circuit layout -/

/-- Total gate count of the Shannon upper-bound circuit construction. -/
def szSections (kk qq : Nat) : Nat :=
  1 + (2^(qq+1) - 4) + (2^(kk+1) - 4) + 2^(2^kk) * (2^kk - 1) + 2^qq + (2^qq - 1)

lemma szSections_pos (kk qq : Nat) : 0 < szSections kk qq := by
  unfold szSections; positivity

/-! ### Section offsets (not private so they can be unfolded after `set`) -/

/-- Cumulative gate offset after Section C of the construction. -/
def oC (qq : Nat) : Nat := 1 + (2 ^ (qq + 1) - 4)
/-- Cumulative gate offset after Section D of the construction. -/
def oD (kk qq : Nat) : Nat := oC qq + (2 ^ (kk + 1) - 4)
/-- Cumulative gate offset after Section E of the construction. -/
def oE (kk qq : Nat) : Nat := oD kk qq + 2 ^ (2 ^ kk) * (2 ^ kk - 1)
/-- Cumulative gate offset after Section F of the construction. -/
def oF (kk qq : Nat) : Nat := oE kk qq + 2 ^ qq

/-! ### Power-of-2 helpers -/

private lemma pow_ge_4 (n : Nat) (hn : 2 ≤ n) : 4 ≤ 2 ^ n := by
  have : (4 : Nat) = 2 ^ 2 := by norm_num
  rw [this]; exact Nat.pow_le_pow_right (by omega) hn

private lemma pow_double (n : Nat) : 2 ^ (n + 1) = 2 * 2 ^ n := by ring

/-! ### Minterm tree level -/

/-- The level (depth from the root) of node `j` in the selection tree. -/
def treeLevel (j : Nat) : Nat := Nat.log 2 (j + 4) - 1

lemma treeLevel_ge_two (j : Nat) (hj : 4 ≤ j) : 2 ≤ treeLevel j := by
  unfold treeLevel
  have : 3 ≤ Nat.log 2 (j + 4) := Nat.le_log_of_pow_le (by omega) (by omega)
  omega

lemma treeLevel_lt (j n : Nat) (hj : j < 2 ^ (n + 1) - 4) (hn : 2 ≤ n) :
    treeLevel j < n := by
  unfold treeLevel
  have : j + 4 < 2^(n+1) := by have := pow_ge_4 (n+1) (by omega); omega
  have : Nat.log 2 (j + 4) < n + 1 := Nat.log_lt_of_lt_pow (by omega) this
  omega

/-- The index of the first node at level `l` of the selection tree. -/
def treeBase (l : Nat) : Nat := 2 ^ (l + 1) - 4
/-- The position of node `j` within its level of the selection tree. -/
def treePos (j l : Nat) : Nat := j - treeBase l
/-- The index of the parent of a node at level `l`, position `m`. -/
def treeParentIdx (l m : Nat) : Nat := treeBase (l-1) + (m % 2 ^ l)

lemma treeBase_le_of_level (j : Nat) (hj : 4 ≤ j) :
    treeBase (treeLevel j) ≤ j := by
  unfold treeBase treeLevel
  have h8 : 8 ≤ j + 4 := by omega
  have h3 : 3 ≤ Nat.log 2 (j + 4) := Nat.le_log_of_pow_le (by omega) (by omega)
  have hlog_sub : Nat.log 2 (j + 4) - 1 + 1 = Nat.log 2 (j + 4) := by omega
  -- 2^(log₂(j+4)) ≤ j + 4
  have hpow_le : 2 ^ Nat.log 2 (j + 4) ≤ j + 4 := Nat.pow_log_le_self 2 (by omega)
  rw [hlog_sub]; omega

lemma treeParentIdx_lt_j (l m j : Nat) (hl : 2 ≤ l)
    (hm : m = treePos j l) (hbase : treeBase l ≤ j) :
    treeParentIdx l m < j := by
  unfold treeParentIdx treeBase treePos at *
  have h4l : 4 ≤ 2 ^ l := pow_ge_4 l hl
  have hlm1 : l - 1 + 1 = l := by omega
  have hpow_eq : 2 ^ (l - 1 + 1) = 2 ^ l := by rw [hlm1]
  have hmod : m % 2 ^ l < 2 ^ l := Nat.mod_lt _ (by positivity)
  have h2l : 2 ^ l ≤ 2 ^ (l + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  subst hm
  rw [hpow_eq]
  omega

private lemma treeLevel_parent (l m : Nat) (hl : 2 ≤ l) :
    treeLevel (treeParentIdx l m) = l - 1 := by
  unfold treeLevel treeParentIdx treeBase
  have h4l : 4 ≤ 2 ^ l := pow_ge_4 l hl
  have hmod : m % 2 ^ l < 2 ^ l := Nat.mod_lt _ (by positivity)
  have hlm1 : l - 1 + 1 = l := by omega
  have harg : 2 ^ (l - 1 + 1) - 4 + m % 2 ^ l + 4 = 2 ^ l + m % 2 ^ l := by
    rw [hlm1]; omega
  rw [harg]
  suffices Nat.log 2 (2 ^ l + m % 2 ^ l) = l by omega
  apply le_antisymm
  · exact Nat.lt_succ_iff.mp (Nat.log_lt_of_lt_pow (by omega)
      (show 2 ^ l + m % 2 ^ l < 2 ^ (l + 1) by have := pow_double l; omega))
  · exact Nat.le_log_of_pow_le (by omega) (by omega)

private lemma treePos_parent (l m : Nat) (_hl : 2 ≤ l) :
    treePos (treeParentIdx l m) (l - 1) = m % 2 ^ l := by
  unfold treePos treeParentIdx
  omega

/-! ### Column pattern encoding -/

/-- Encode a column of truth-table bits as a natural number. -/
noncomputable def encodeCol (k : Nat) (col : Fin (2 ^ k) → Bool) : Nat :=
  Finset.sum (Finset.univ : Finset (Fin (2^k)))
    fun j => if col j then 2^j.val else 0

private lemma sum_pow_two_lt (n : Nat) :
    Finset.sum Finset.univ (fun j : Fin n => (2 : Nat) ^ j.val) < 2 ^ n := by
  rw [Fin.sum_univ_eq_sum_range]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    calc Finset.sum (Finset.range n) (fun j => 2 ^ j) + 2 ^ n
        < 2 ^ n + 2 ^ n := by omega
      _ = 2 ^ (n + 1) := by ring

theorem encodeCol_lt (k : Nat) (col : Fin (2 ^ k) → Bool) :
    encodeCol k col < 2^(2^k) := by
  unfold encodeCol
  calc Finset.sum Finset.univ (fun j : Fin (2^k) => if col j then 2 ^ j.val else 0)
      ≤ Finset.sum Finset.univ (fun j : Fin (2^k) => 2 ^ j.val) := by
        apply Finset.sum_le_sum; intro j _; split_ifs <;> simp
    _ < 2 ^ (2^k) := sum_pow_two_lt (2^k)

/-- The Boolean function selecting the addressed column of `f`. The hypothesis
`hkq : k + q = N` records that the address and data bits partition the inputs. -/
noncomputable def colFun (N : Nat) (f : BitString N → Bool)
    (k q : Nat) (hkq : k + q = N) (y : Fin (2 ^ q)) : Fin (2 ^ k) → Bool :=
  let _hkq := hkq
  fun a => f (fun idx =>
    if _ : idx.val < k then Nat.testBit a.val idx.val
    else Nat.testBit y.val (idx.val - k))

/-- The pattern index of the addressed column of `f`. -/
noncomputable def colPatIdx (N : Nat) (f : BitString N → Bool)
    (k q : Nat) (hkq : k + q = N) (y : Fin (2 ^ q)) : Nat :=
  encodeCol k (colFun N f k q hkq y)

theorem colPatIdx_lt (N : Nat) (f : BitString N → Bool)
    (k q : Nat) (hkq : k + q = N) (y : Fin (2 ^ q)) :
    colPatIdx N f k q hkq y < 2^(2^k) :=
  encodeCol_lt k (colFun N f k q hkq y)

/-- Bound on conditional-power sum over Fin. -/
private lemma sum_cond_pow_fin_lt (k : Nat) (b : BitString k) :
    Finset.sum (Finset.univ : Finset (Fin k))
      (fun j => if b j then 2^j.val else 0) < 2^k :=
  calc _ ≤ Finset.sum Finset.univ (fun j : Fin k => 2^j.val) := by
        apply Finset.sum_le_sum; intro j _; split_ifs <;> simp
    _ < 2^k := sum_pow_two_lt k

/-- testBit of a conditional-power sum over Fin k recovers the bit. -/
private theorem testBit_sum_cond_pow_fin (k : Nat) (b : BitString k) (i : Nat) (hi : i < k) :
    Nat.testBit (Finset.sum (Finset.univ : Finset (Fin k))
      (fun j => if b j then 2^j.val else 0)) i = b ⟨i, hi⟩ := by
  -- Prove by induction on k using a helper with ∀ quantifiers
  suffices h : ∀ (kk : Nat) (bb : BitString kk) (ii : Nat) (hii : ii < kk),
    Nat.testBit (Finset.sum (Finset.univ : Finset (Fin kk))
      (fun j => if bb j then 2^j.val else 0)) ii = bb ⟨ii, hii⟩ from h k b i hi
  intro kk
  induction kk with
  | zero => intro _ ii hii; omega
  | succ n ih =>
    intro bb ii hii
    rw [Fin.sum_univ_castSucc]
    have hcast : ∀ j : Fin n,
      (if bb (Fin.castSucc j) then 2 ^ (Fin.castSucc j).val else 0) =
      (if bb (Fin.castSucc j) then 2 ^ j.val else 0) := by
      intro j; simp [Fin.val_castSucc]
    simp_rw [hcast]
    set S := Finset.sum Finset.univ
      (fun j : Fin n => if bb (Fin.castSucc j) then 2^j.val else 0)
    have hS_lt : S < 2^n := sum_cond_pow_fin_lt n (fun j => bb (Fin.castSucc j))
    by_cases hi_n : ii < n
    · -- ii < n: the last term (power 2^n) doesn't affect testBit at position ii
      by_cases hbn : bb (Fin.last n)
      · simp only [hbn, ite_true, Fin.val_last]
        rw [Nat.add_comm, Nat.testBit_two_pow_add_gt (by omega)]
        exact ih (fun j => bb (Fin.castSucc j)) ii hi_n
      · simp only [hbn, Fin.val_last]
        exact ih (fun j => bb (Fin.castSucc j)) ii hi_n
    · -- ii = n
      have hii_eq : ii = n := by omega
      subst hii_eq
      have hlast_eq : (Fin.last ii : Fin (ii + 1)) = ⟨ii, hii⟩ := by ext; simp [Fin.val_last]
      by_cases hbn : bb (Fin.last ii)
      · simp only [hbn, ite_true, Fin.val_last]
        rw [Nat.add_comm, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hS_lt, Bool.not_false]
        rw [hlast_eq] at hbn; exact hbn.symm
      · simp only [hbn, ite_false, Fin.val_last, Nat.add_zero, Bool.false_eq_true]
        rw [Nat.testBit_lt_two_pow hS_lt]
        rw [hlast_eq] at hbn
        exact (Bool.eq_false_iff.mpr hbn).symm

private theorem addrDataSum (N : Nat) (hN : 16 ≤ N) :
    addrBits N + dataBits N = N := by
  have := addr_data_sum N hN; omega

/-! ### Shannon gate array -/

private noncomputable def shannonGateArray (N : Nat) [NeZero N]
    (f : BitString N → Bool) (hN : 16 ≤ N) :
    (i : Fin (szSections (addrBits N) (dataBits N))) →
    { g : Gate Basis.andOr2 (N + szSections (addrBits N) (dataBits N)) //
      ∀ j : Fin g.fanIn, (g.inputs j).val < N + i.val } := by
  -- Abbreviations: we use `let` not `set` to keep definitions transparent
  let k := addrBits N
  let q := dataBits N
  let W := N + szSections k q
  let G := szSections k q
  have hkq : k + q = N := by change addrBits N + dataBits N = N; have := addr_data_sum N hN; omega
  have hk3 : 3 ≤ k := addrBits_ge_three N hN
  have hq2 : 2 ≤ q := dataBits_ge_two N hN
  have h4q : 4 ≤ 2^q := pow_ge_4 q (by omega)
  have h4k : 4 ≤ 2^k := pow_ge_4 k (by omega)
  have h4q1 : 4 ≤ 2^(q+1) := pow_ge_4 (q+1) (by omega)
  have h4k1 : 4 ≤ 2^(k+1) := pow_ge_4 (k+1) (by omega)
  have h2q1 : 2^(q+1) = 2 * 2^q := pow_double q
  have h2k1 : 2^(k+1) = 2 * 2^k := pow_double k
  have hW_pos : 0 < W := by change 0 < N + szSections k q; unfold szSections; positivity
  have hG_eq : G = oF k q + (2^q - 1) := by
    change szSections k q = oF k q + (2^q - 1)
    unfold szSections oF oE oD oC; omega
  intro i
  -- ──── Section A: constFalse (gate 0) ────
  if hiA : i.val = 0 then
    exact mkG W .and 0 0 false true (by omega) (by omega) (N + i.val) (by omega) (by omega)
  -- ──── Section B: data minterm tree ────
  else if hiB : i.val < oC q then
    let j := i.val - 1
    have hjB : j < 2^(q+1) - 4 := by unfold oC at hiB; omega
    if hjL1 : j < 4 then
      -- Level 1: AND(input[k], input[k+1])
      exact mkG W .and k (k+1) (!Nat.testBit j 0) (!Nat.testBit j 1)
        (by omega) (by omega) (N + i.val) (by omega) (by omega)
    else
      let l := treeLevel j
      let m := treePos j l
      have hl2 : 2 ≤ l := treeLevel_ge_two j (by omega)
      have hlq : l < q := treeLevel_lt j q hjB hq2
      -- Parent wire: N + 1 + treeParentIdx l m (gate in data tree)
      let pw := N + 1 + treeParentIdx l m
      let vw := k + l
      have hbase : treeBase l ≤ j := treeBase_le_of_level j (by omega)
      have hpi_lt : treeParentIdx l m < j := treeParentIdx_lt_j l m j hl2 rfl hbase
      have hpw_b : pw < N + i.val := by
        change N + 1 + treeParentIdx l m < N + i.val; omega
      have hvw_b : vw < N + i.val := by change k + l < N + i.val; omega
      -- For W bounds, chain: treeParentIdx < j = i.val - 1 < i.val < G → in W
      have hi_lt : i.val < szSections k q := i.isLt
      have hpw_W : pw < W := by
        change N + 1 + treeParentIdx l m < N + szSections k q; omega
      have hvw_W : vw < W := by change k + l < N + szSections k q; omega
      exact mkG W .and pw vw false (!Nat.testBit m l) hpw_W hvw_W (N + i.val) hpw_b hvw_b
  -- ──── Section C: address minterm tree ────
  else if hiC : i.val < oD k q then
    let j := i.val - oC q
    have hi_lt : i.val < szSections k q := i.isLt
    have hjC : j < 2^(k+1) - 4 := by
      change i.val - oC q < 2^(k+1) - 4
      have : i.val < oC q + (2^(k+1) - 4) := by unfold oD at hiC; exact hiC
      unfold oC at this ⊢; omega
    if hjL1 : j < 4 then
      exact mkG W .and 0 1 (!Nat.testBit j 0) (!Nat.testBit j 1)
        (by omega) (by omega) (N + i.val) (by omega) (by omega)
    else
      let l := treeLevel j
      let m := treePos j l
      have hl2 : 2 ≤ l := treeLevel_ge_two j (by omega)
      have hlk : l < k := treeLevel_lt j k hjC (by omega)
      let pw := N + oC q + treeParentIdx l m
      let vw := l
      have hbase : treeBase l ≤ j := treeBase_le_of_level j (by omega)
      have hpi_lt : treeParentIdx l m < j := treeParentIdx_lt_j l m j hl2 rfl hbase
      -- j < 2^(k+1) - 4, and oC q + (2^(k+1) - 4) ≤ G
      have hj_lt_G : oC q + j < G := by
        change oC q + j < szSections k q
        unfold szSections oC; omega
      have hpw_b : pw < N + i.val := by
        change N + oC q + treeParentIdx l m < N + i.val; omega
      have hvw_b : vw < N + i.val := by change l < N + i.val; omega
      have hpw_W : pw < W := by
        change N + oC q + treeParentIdx l m < N + szSections k q; omega
      have hvw_W : vw < W := by change l < N + szSections k q; omega
      exact mkG W .and pw vw false (!Nat.testBit m l) hpw_W hvw_W (N + i.val) hpw_b hvw_b
  -- ──── Section D: column library ────
  else if hiD : i.val < oE k q then
    -- Block p, position r. Block size = 2^k - 1.
    -- Linear OR chain: gate 0 ORs select(0) with select(1),
    -- gate r≥1 ORs prev with select(r+1).
    -- select(a) = addrMinterm_a if testBit(p, a) else constFalse
    let j := i.val - oD k q
    have hjD : j < 2^(2^k) * (2^k - 1) := by
      change i.val - oD k q < 2^(2^k) * (2^k - 1)
      have : i.val < oD k q + 2^(2^k) * (2^k - 1) := by unfold oE at hiD; exact hiD
      omega
    let blkSz := 2^k - 1
    have hblk_pos : 0 < blkSz := by omega
    let p := j / blkSz
    let r := j % blkSz
    have hr_lt : r < blkSz := Nat.mod_lt j hblk_pos
    -- Address minterm wire for index a: N + oC q + (2^k - 4) + a
    let amw (a : Nat) : Nat := N + oC q + (2^k - 4) + a
    let cfw : Nat := N  -- constFalse wire
    -- Simplify: r + 1 regardless of r = 0 check
    let selIdx (pos : Nat) : Nat :=
      if Nat.testBit p pos then amw pos else cfw
    let w0 : Nat := if r = 0 then selIdx 0 else N + oD k q + p * blkSz + (r - 1)
    let w1 : Nat := selIdx (r + 1)
    -- Bound proofs: all referenced wires are before the current gate
    -- Address minterms are in section C (before D)
    -- constFalse is gate 0 (before everything)
    -- previous gate in same block is at index < i
    have hamw_lt (a : Nat) (ha : a < 2^k) : amw a < N + i.val := by
      change N + oC q + (2^k - 4) + a < N + i.val
      have : oC q + (2^k - 4) + a < oD k q := by unfold oD oC; omega
      omega
    have hi_lt : i.val < szSections k q := i.isLt
    have hamw_W (a : Nat) (ha : a < 2^k) : amw a < W := by
      change N + oC q + (2^k - 4) + a < N + szSections k q
      unfold szSections oC; omega
    have hcfw_lt : cfw < N + i.val := by change N < N + i.val; omega
    have hcfw_W : cfw < W := by change N < N + szSections k q; omega
    -- selIdx bound helper
    have hsel_lt (pos : Nat) (hpos : pos < 2^k) : selIdx pos < N + i.val := by
      change (if Nat.testBit p pos then amw pos else cfw) < N + i.val
      split_ifs
      · exact hamw_lt pos hpos
      · exact hcfw_lt
    have hsel_W (pos : Nat) (hpos : pos < 2^k) : selIdx pos < W := by
      change (if Nat.testBit p pos then amw pos else cfw) < W
      split_ifs
      · exact hamw_W pos hpos
      · exact hcfw_W
    have hi_eq : oD k q + j = i.val := by omega
    have hpbr_j : blkSz * p + r = j := by
      change blkSz * (j / blkSz) + j % blkSz = j; exact Nat.div_add_mod j blkSz
    have hpbr : oD k q + p * blkSz + r = i.val := by nlinarith [mul_comm blkSz p]
    have hw0_lt : w0 < W := by
      change (if r = 0 then selIdx 0 else N + oD k q + p * blkSz + (r - 1)) < W
      split_ifs with hr0
      · exact hsel_W 0 (by omega)
      · have hi_lt := i.isLt; omega
    have hw1_lt : w1 < W := hsel_W (r + 1) (by omega)
    have hb0 : w0 < N + i.val := by
      change (if r = 0 then selIdx 0 else N + oD k q + p * blkSz + (r - 1)) < N + i.val
      split_ifs with hr0
      · exact hsel_lt 0 (by omega)
      · omega
    have hb1 : w1 < N + i.val := hsel_lt (r + 1) (by omega)
    exact mkG W .or w0 w1 false false hw0_lt hw1_lt (N + i.val) hb0 hb1
  -- ──── Section E: AND layer ────
  else if hiE : i.val < oF k q then
    let y := i.val - oE k q
    have hy : y < 2^q := by
      change i.val - oE k q < 2^q
      have : i.val < oE k q + 2^q := by unfold oF at hiE; exact hiE
      omega
    -- Data minterm: N + 1 + (2^q - 4) + y
    let dmw := N + 1 + (2^q - 4) + y
    -- Column library output for row y
    let p := colPatIdx N f k q hkq ⟨y, hy⟩
    have hp : p < 2^(2^k) := colPatIdx_lt N f k q hkq ⟨y, hy⟩
    let cw := N + oD k q + p * (2^k - 1) + (2^k - 2)
    -- dmw is in section B, which is before section E (where i lives)
    have hdmw_in_B : 1 + (2^q - 4) + y < oC q := by unfold oC; omega
    have hdmw_b : dmw < N + i.val := by
      change N + 1 + (2^q - 4) + y < N + i.val
      have : oC q ≤ oD k q := by unfold oD; omega
      have : oD k q ≤ oE k q := by unfold oE; omega
      omega
    have hdmw_W : dmw < W := by
      change N + 1 + (2^q - 4) + y < N + szSections k q
      unfold szSections at *; omega
    -- cw is the last gate of column block p (in section D, before section E)
    have hcw_in_D : p * (2^k - 1) + (2^k - 2) < 2^(2^k) * (2^k - 1) := by
      have hmul : (p + 1) * (2^k - 1) ≤ 2^(2^k) * (2^k - 1) :=
        Nat.mul_le_mul_right _ (by omega)
      have hexp : p * (2^k - 1) + (2^k - 1) = (p + 1) * (2^k - 1) := by ring
      omega
    have hcw_b : cw < N + i.val := by
      change N + oD k q + p * (2^k - 1) + (2^k - 2) < N + i.val
      have hoE_le : oE k q ≤ i.val := by omega
      -- oE k q = oD k q + 2^(2^k) * (2^k - 1), and our wire < oE, so < i.val
      have : oD k q + p * (2^k - 1) + (2^k - 2) < oE k q := by
        unfold oE; omega
      omega
    have hcw_W : cw < W := by
      change N + oD k q + p * (2^k - 1) + (2^k - 2) < N + szSections k q
      have hi_lt := i.isLt; omega
    exact mkG W .and dmw cw false false hdmw_W hcw_W (N + i.val) hdmw_b hcw_b
  -- ──── Section F: OR chain ────
  else
    let r := i.val - oF k q
    have hiF : oF k q ≤ i.val := by omega
    have hr : r < 2^q - 1 := by
      change i.val - oF k q < 2^q - 1
      have : i.val < oF k q + (2^q - 1) := by rw [← hG_eq]; exact i.isLt
      omega
    let w0 : Nat := if r = 0 then N + oE k q else N + oF k q + (r - 1)
    let w1 : Nat := N + oE k q + (r + 1)
    -- oE < oF ≤ i.val, and oE + (r+1) < oE + 2^q = oF ≤ i.val
    have hoEF : oE k q < oF k q := by unfold oF; omega
    have hsz_eq : szSections k q = oF k q + (2^q - 1) := hG_eq
    have hw0_lt : w0 < W := by
      change (if r = 0 then N + oE k q else N + oF k q + (r - 1)) < N + szSections k q
      split_ifs
      · omega
      · omega
    have hw1_lt : w1 < W := by
      change N + oE k q + (r + 1) < N + szSections k q
      unfold oF at hsz_eq; omega
    have hb0 : w0 < N + i.val := by
      change (if r = 0 then N + oE k q else N + oF k q + (r - 1)) < N + i.val
      split_ifs with hr0
      · omega
      · omega
    have hb1 : w1 < N + i.val := by
      change N + oE k q + (r + 1) < N + i.val
      unfold oF at hiF; omega
    exact mkG W .or w0 w1 false false hw0_lt hw1_lt (N + i.val) hb0 hb1

private theorem lastWire_is_orChain_last (N : Nat) (hN : 16 ≤ N) :
    N + szSections (addrBits N) (dataBits N) - 1 =
    N + oF (addrBits N) (dataBits N) + (2 ^ dataBits N - 2) := by
  have hq2 : 2 ≤ dataBits N := dataBits_ge_two N hN
  have h4q : 4 ≤ 2 ^ dataBits N := pow_ge_4 (dataBits N) hq2
  unfold szSections oF oE oD oC; omega

private noncomputable def shannonCircuit (N : Nat) [NeZero N]
    (f : BitString N → Bool) (hN : 16 ≤ N) :
    Circuit Basis.andOr2 N 1 (szSections (addrBits N) (dataBits N)) where
  gates i := (shannonGateArray N f hN i).val
  outputs _ :=
    let lastWire := N + szSections (addrBits N) (dataBits N) - 1
    { op := .or, fanIn := 2, arityOk := rfl,
      inputs := fun _ => ⟨lastWire, by have := szSections_pos (addrBits N) (dataBits N); omega⟩,
      negated := fun _ => false }
  acyclic i k := (shannonGateArray N f hN i).property k

/-! ### Correctness -/

/-! #### colFun reconstruction lemma -/

/-- Shift the data bits of x to form a q-bit function. -/
private def shiftedBits (N k q : Nat) (hkq : k + q = N) (x : BitString N) :
    BitString q :=
  fun j => x ⟨k + j.val, by have := j.isLt; omega⟩

/-- colFun at the actual bit-vector address/data values equals f(x). -/
private theorem colFun_at_actual_bits (N : Nat) [NeZero N]
    (f : BitString N → Bool) (x : BitString N)
    (k q : Nat) (hkq : k + q = N) :
    let addr : BitString k := fun j => x ⟨j.val, by have := j.isLt; omega⟩
    let data := shiftedBits N k q hkq x
    let aSum := Finset.sum (Finset.univ : Finset (Fin k))
      (fun j => if addr j then 2^j.val else 0)
    let dSum := Finset.sum (Finset.univ : Finset (Fin q))
      (fun j => if data j then 2^j.val else 0)
    colFun N f k q hkq
      ⟨dSum, sum_cond_pow_fin_lt q data⟩
      ⟨aSum, sum_cond_pow_fin_lt k addr⟩ = f x := by
  simp only
  unfold colFun shiftedBits
  dsimp only
  congr 1
  funext ⟨idx, hidx⟩
  dsimp only
  split_ifs with h
  · exact testBit_sum_cond_pow_fin k _ idx h
  · have hq_bound : idx - k < q := by omega
    rw [testBit_sum_cond_pow_fin q _ (idx - k) hq_bound]
    dsimp only
    congr 1; ext; simp; omega

/-! #### Circuit correctness -/

/-- The semantic value of each AND-layer wire (Section E). -/
private noncomputable def andLayerSem (N : Nat)
    (f : BitString N → Bool) (hN : 16 ≤ N) (x : BitString N)
    (y : Nat) (hy : y < 2 ^ dataBits N) : Bool :=
  let k := addrBits N
  let q := dataBits N
  let hkq := addrDataSum N hN
  let data := shiftedBits N k q hkq x
  let dVal := Finset.sum (Finset.univ : Finset (Fin q))
    (fun j => if data j then 2^j.val else 0)
  let addr : BitString k := fun j => x ⟨j.val, by have := j.isLt; omega⟩
  let aVal := Finset.sum (Finset.univ : Finset (Fin k))
    (fun j => if addr j then 2^j.val else 0)
  (y == dVal) && colFun N f k q hkq ⟨y, hy⟩
    ⟨aVal, sum_cond_pow_fin_lt k addr⟩

/-- Foldl of OR over a list where all elements are false gives false. -/
private theorem foldl_or_all_false {n : Nat} {P : Nat → Bool}
    (hP : ∀ y, y < n → P y = false) :
    (List.range n).foldl (fun acc y => acc || P y) false = false := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [ih (fun y hy => hP y (by omega))]
    rw [hP m (by omega)]; rfl

/-- A list foldl of OR where each non-matching term is false produces the
    value at the matching position. -/
private theorem foldl_or_unique_true {n : Nat} {P : Nat → Bool}
    (target : Nat) (htarget : target < n)
    (hP : ∀ y, y < n → y ≠ target → P y = false) :
    (List.range n).foldl (fun acc y => acc || P y) false = P target := by
  induction n with
  | zero => omega
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    by_cases htm : target < m
    · -- target < m: result after first m was already P target
      rw [ih htm (fun y hy hne => hP y (by omega) hne)]
      rw [hP m (by omega) (by omega)]
      simp [Bool.or_false]
    · -- target = m
      have htm_eq : target = m := by omega
      subst htm_eq
      -- All terms before target are false, so foldl gives false
      rw [foldl_or_all_false (fun y hy => hP y (by omega) (by omega))]
      simp [Bool.false_or]

/-- The data sum: encode the data bits of x as a natural number. -/
private noncomputable def dataSum (N : Nat) (hN : 16 ≤ N) (x : BitString N) : Nat :=
  Finset.sum (Finset.univ : Finset (Fin (dataBits N)))
    (fun j => if shiftedBits N (addrBits N) (dataBits N) (addrDataSum N hN) x j
              then 2^j.val else 0)

private theorem dataSum_lt (N : Nat) (hN : 16 ≤ N) (x : BitString N) :
    dataSum N hN x < 2 ^ dataBits N :=
  sum_cond_pow_fin_lt (dataBits N) (shiftedBits N (addrBits N) (dataBits N) (addrDataSum N hN) x)

/-- andLayerSem at y is false when y ≠ dataSum. -/
private theorem andLayerSem_ne (N : Nat) [NeZero N]
    (f : BitString N → Bool) (hN : 16 ≤ N) (x : BitString N)
    (y : Nat) (hy : y < 2 ^ dataBits N) (hne : y ≠ dataSum N hN x) :
    andLayerSem N f hN x y hy = false := by
  unfold andLayerSem dataSum at *
  simp only [beq_eq_false_iff_ne.mpr hne, Bool.false_and]

/-- andLayerSem at dataSum gives colFun at actual bits. -/
private theorem andLayerSem_eq (N : Nat) [NeZero N]
    (f : BitString N → Bool) (hN : 16 ≤ N) (x : BitString N) :
    andLayerSem N f hN x (dataSum N hN x) (dataSum_lt N hN x) = f x := by
  unfold andLayerSem dataSum
  simp only [beq_self_eq_true, Bool.true_and]
  exact colFun_at_actual_bits N f x (addrBits N) (dataBits N) (addrDataSum N hN)

private theorem or_andLayerSem_eq_f (N : Nat) [NeZero N]
    (f : BitString N → Bool) (hN : 16 ≤ N) (x : BitString N) :
    (List.range (2 ^ dataBits N)).foldl
      (fun acc y => acc || if h : y < 2 ^ dataBits N
        then andLayerSem N f hN x y h else false) false = f x := by
  -- Use foldl_or_unique_true with target = dataSum N hN x
  have hds_lt := dataSum_lt N hN x
  have hP_ne : ∀ y, y < 2 ^ dataBits N → y ≠ dataSum N hN x →
    (if h : y < 2 ^ dataBits N then andLayerSem N f hN x y h else false) = false := by
    intro y hy hne
    rw [dif_pos hy, andLayerSem_ne N f hN x y hy hne]
  have hfoldl := foldl_or_unique_true (dataSum N hN x) hds_lt hP_ne
  rw [hfoldl, dif_pos hds_lt, andLayerSem_eq N f hN x]

/-- The OR chain accumulates AND-layer semantic values.

    This is the key wire-level fact: by induction on r, the OR-chain gate
    at position r in Section F evaluates to the foldl-OR of AND-layer
    semantic values for y = 0, ..., r+1.

    The proof requires tracing wireValue through the gate array, showing:
    - The gate at index oF(k,q) + r is in Section F
    - Section F gates are OR gates with inputs pointing to:
      * For r=0: AND gates at oE+0 and oE+1
      * For r>0: previous OR-chain gate and AND gate at oE+(r+1)
    - Each AND gate at oE+y evaluates to andLayerSem (by wireValue_andLayer_sem)
    - The OR of the accumulated value and the new AND output gives
      the extended foldl

    The data tree leaf and column library output wire-value proofs
    trace wireValue through Sections B and D respectively via
    tree-level induction. -/
private theorem wireValue_dataLeaf (N : Nat) [NeZero N]
    (f : BitString N → Bool) (hN : 16 ≤ N) (x : BitString N)
    (y : Nat) (hy : y < 2 ^ dataBits N)
    (hyW : N + 1 + (2 ^ dataBits N - 4) + y <
          N + szSections (addrBits N) (dataBits N)) :
    (shannonCircuit N f hN).wireValue x
      ⟨N + 1 + (2 ^ dataBits N - 4) + y, hyW⟩ =
    (y == Finset.sum Finset.univ (fun j : Fin (dataBits N) =>
      if shiftedBits N (addrBits N) (dataBits N) (addrDataSum N hN) x j = true
      then 2 ^ j.val else 0)) := by
  have hq2 := dataBits_ge_two N hN
  have h4q := pow_ge_4 (dataBits N) hq2
  have hk3 := addrBits_ge_three N hN
  have hkq := addrDataSum N hN
  have h2q1 : 2 ^ (dataBits N + 1) = 2 * 2 ^ dataBits N := pow_double (dataBits N)
  have hsB : ∀ (j : Nat) (hj : j < 2 ^ (dataBits N + 1) - 4)
      (hjW : N + 1 + j < N + szSections (addrBits N) (dataBits N)),
      (shannonCircuit N f hN).wireValue x ⟨N + 1 + j, hjW⟩ =
      decide (∀ i : Fin (treeLevel j + 1),
        x ⟨addrBits N + i.val,
          by have := i.isLt; have := treeLevel_lt j (dataBits N) hj hq2; omega⟩ =
          Nat.testBit (treePos j (treeLevel j)) i.val) := by
    intro j
    exact Nat.strongRecOn j fun j ih => by
      intro hj hjW
      rw [Circuit.wireValue_ge _ _ _ (by change ¬(N + 1 + j < N); omega)]
      change (shannonGateArray N f hN ⟨_, _⟩).val.eval _ = _
      unfold shannonGateArray
      simp only [show N + 1 + j - N = 1 + j from by omega]
      rw [dif_neg (by omega : ¬(1 + j = 0))]
      rw [dif_pos (by unfold oC; omega : 1 + j < oC (dataBits N))]
      simp only [show 1 + j - 1 = j from by omega]
      by_cases hjL1 : j < 4
      · rw [dif_pos hjL1]
        simp only [mkG, Gate.eval, Basis.andOr2, AONOp.eval,
          Fin.foldl_succ_last, Fin.foldl_zero, Bool.true_and]
        simp only [Fin.val_last, Fin.val_castSucc, ite_true, ite_false,
          show ¬((1 : Nat) = 0) from by omega]
        rw [Circuit.wireValue_lt _ _ _ (show (⟨addrBits N, _⟩ : Fin _).val < N from by
          change addrBits N < N; have := addr_le_N N hN; omega)]
        rw [Circuit.wireValue_lt _ _ _ (show (⟨addrBits N + 1, _⟩ : Fin _).val < N from by
          change addrBits N + 1 < N; have := addr_le_N N hN; omega)]
        have htl : treeLevel j = 1 := by
          unfold treeLevel
          have h1 : Nat.log 2 (j + 4) = 2 := by
            apply le_antisymm
            · exact Nat.lt_succ_iff.mp (Nat.log_lt_of_lt_pow (by omega) (by omega))
            · exact Nat.le_log_of_pow_le (by omega) (by omega)
          omega
        have htp : treePos j 1 = j := by unfold treePos treeBase; omega
        simp only [htl, htp, Nat.testBit_zero]
        have hlq : treeLevel j < dataBits N := treeLevel_lt j (dataBits N) (by omega) hq2
        have hfin_bound : ∀ (i : Fin (treeLevel j + 1)), addrBits N + i.val < N := by
          intro i; have := i.isLt; omega
        have hfin_bound2 : ∀ (i : Fin 2), addrBits N + i.val < N := by
          intro i; have := i.isLt; omega
        have hcast : (∀ (i : Fin (treeLevel j + 1)),
            x ⟨addrBits N + i.val, hfin_bound i⟩ = j.testBit i.val) ↔
            (∀ (i : Fin 2), x ⟨addrBits N + i.val, hfin_bound2 i⟩ = j.testBit i.val) := by
          constructor
          · intro h i; exact h ⟨i.val, by rw [htl]; exact i.isLt⟩
          · intro h ⟨i, hi⟩; exact h ⟨i, by rw [htl] at hi; exact hi⟩
        rw [show decide (∀ (i : Fin (treeLevel j + 1)),
              x ⟨addrBits N + ↑i, hfin_bound i⟩ = j.testBit ↑i) =
            decide (∀ (i : Fin 2),
              x ⟨addrBits N + ↑i, hfin_bound2 i⟩ = j.testBit ↑i) from
          decide_eq_decide.mpr hcast]
        simp only [Fin.forall_fin_two, Fin.val_zero, Fin.val_one,
          show addrBits N + 0 = addrBits N from by omega, Nat.testBit_zero]
        cases x ⟨addrBits N, by omega⟩ <;> cases x ⟨addrBits N + 1, by omega⟩ <;>
          cases j.testBit 1 <;> cases (decide (j % 2 = 1)) <;> simp_all
      · rw [dif_neg hjL1]
        simp only [mkG, Gate.eval, Basis.andOr2, AONOp.eval,
          Fin.foldl_succ_last, Fin.foldl_zero, Bool.true_and]
        simp only [Fin.val_last, Fin.val_castSucc, ite_true, ite_false,
          show ¬((1 : Nat) = 0) from by omega]
        have hl2 : 2 ≤ treeLevel j := treeLevel_ge_two j (by omega)
        have hlq : treeLevel j < dataBits N := treeLevel_lt j (dataBits N) hj hq2
        have hbase : treeBase (treeLevel j) ≤ j := treeBase_le_of_level j (by omega)
        have hpi_lt : treeParentIdx (treeLevel j) (treePos j (treeLevel j)) < j :=
          treeParentIdx_lt_j _ _ j hl2 rfl hbase
        rw [Circuit.wireValue_lt _ _ _ (show (⟨addrBits N + treeLevel j, _⟩ : Fin _).val < N
          from by change addrBits N + treeLevel j < N; omega)]
        have hpar := ih (treeParentIdx (treeLevel j) (treePos j (treeLevel j)))
          hpi_lt (by omega) (by omega)
        have htlp := treeLevel_parent (treeLevel j) (treePos j (treeLevel j)) hl2
        have htlp1 : treeLevel (treeParentIdx (treeLevel j) (treePos j (treeLevel j))) + 1 =
          treeLevel j := by omega
        have htpp : treePos (treeParentIdx (treeLevel j) (treePos j (treeLevel j)))
          (treeLevel (treeParentIdx (treeLevel j) (treePos j (treeLevel j)))) =
          treePos j (treeLevel j) % 2 ^ treeLevel j := by
          rw [htlp]; exact treePos_parent (treeLevel j) (treePos j (treeLevel j)) hl2
        change ((false ^^ (shannonCircuit N f hN).wireValue x
            ⟨N + 1 + treeParentIdx (treeLevel j) (treePos j (treeLevel j)), by omega⟩) &&
          (!(treePos j (treeLevel j)).testBit (treeLevel j) ^^
            x ⟨addrBits N + treeLevel j, by omega⟩)) =
          decide (∀ (i : Fin (treeLevel j + 1)),
            x ⟨addrBits N + i.val, by have := i.isLt; omega⟩ =
            (treePos j (treeLevel j)).testBit i.val)
        rw [Bool.false_xor, hpar]
        rw [Bool.eq_iff_iff, Bool.and_eq_true]
        constructor
        · rintro ⟨h1, h2⟩
          rw [decide_eq_true_eq] at h1 ⊢
          intro i
          by_cases hil : i.val < treeLevel j
          · have h1i := h1 ⟨i.val, by rw [htlp1]; exact hil⟩
            rw [htpp, Nat.testBit_mod_two_pow] at h1i
            simp only [show decide (i.val < treeLevel j) = true from
              decide_eq_true_eq.mpr hil, Bool.true_and] at h1i
            exact Eq.mpr (by congr 1) h1i
          · have hi_eq : i.val = treeLevel j := by have := i.isLt; omega
            have h2' := (show ∀ (a b : Bool), (!b ^^ a) = true → a = b from by decide) _ _ h2
            exact Eq.mpr (by simp only [hi_eq]) h2'
        · intro h
          rw [decide_eq_true_eq] at h
          refine ⟨?_, ?_⟩
          · rw [decide_eq_true_eq]
            intro i
            rw [htpp, Nat.testBit_mod_two_pow]
            have hi : i.val < treeLevel j := by omega
            simp only [show decide (i.val < treeLevel j) = true from
              decide_eq_true_eq.mpr hi, Bool.true_and]
            exact Eq.mpr (by congr 1) (h ⟨i.val, by omega⟩)
          · exact (show ∀ (a b : Bool), a = b → (!b ^^ a) = true from by decide) _ _
              (Eq.mpr (by congr 1) (h ⟨treeLevel j, by omega⟩))
  specialize hsB (2 ^ dataBits N - 4 + y) (by omega) (by omega)
  simp only [show N + 1 + (2 ^ dataBits N - 4 + y) = N + 1 + (2 ^ dataBits N - 4) + y
    from by omega] at hsB
  rw [hsB]
  have htl_leaf : treeLevel (2 ^ dataBits N - 4 + y) = dataBits N - 1 := by
    unfold treeLevel
    have : Nat.log 2 (2 ^ dataBits N - 4 + y + 4) = dataBits N := by
      apply le_antisymm
      · exact Nat.lt_succ_iff.mp (Nat.log_lt_of_lt_pow (by omega) (by omega))
      · exact Nat.le_log_of_pow_le (by omega) (by omega)
    omega
  have htp_leaf : treePos (2 ^ dataBits N - 4 + y) (dataBits N - 1) = y := by
    unfold treePos treeBase
    have : dataBits N - 1 + 1 = dataBits N := by omega
    rw [this]; omega
  conv_lhs => rw [show treePos (2 ^ dataBits N - 4 + y)
      (treeLevel (2 ^ dataBits N - 4 + y)) = y from by rw [htl_leaf]; exact htp_leaf]
  have hFin_eq : treeLevel (2 ^ dataBits N - 4 + y) + 1 = dataBits N := by
    rw [htl_leaf]; omega
  set data := shiftedBits N (addrBits N) (dataBits N) (addrDataSum N hN) x
  set dSum := Finset.sum Finset.univ (fun j : Fin (dataBits N) =>
    if data j then 2 ^ j.val else 0)
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, beq_iff_eq]
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < dataBits N
    · rw [testBit_sum_cond_pow_fin (dataBits N) data i hi]
      exact Eq.mpr (by congr 1) (h ⟨i, by omega⟩).symm
    · have : y < 2 ^ i := lt_of_lt_of_le hy (Nat.pow_le_pow_right (by omega) (by omega))
      have : dSum < 2 ^ i := lt_of_lt_of_le
        (sum_cond_pow_fin_lt (dataBits N) data) (Nat.pow_le_pow_right (by omega) (by omega))
      rw [Nat.testBit_lt_two_pow ‹y < 2 ^ i›, Nat.testBit_lt_two_pow ‹dSum < 2 ^ i›]
  · intro h
    subst h
    intro i
    have hi : i.val < dataBits N := by omega
    rw [testBit_sum_cond_pow_fin (dataBits N) data i.val hi]
    exact Eq.mpr (by congr 1) rfl

/-- Each address-selector wire outputs `decide (a = aSum)`, where `aSum` is the
numeric value of `x`'s address bits. (Extracted from `wireValue_colOutput`.) -/
private theorem colOutput_addrLeaf (N : Nat) [NeZero N]
    (f : BitString N → Bool) (hN : 16 ≤ N) (x : BitString N) :
    ∀ (a : Nat) (_ha : a < 2 ^ addrBits N)
      (haW : N + oC (dataBits N) + (2 ^ addrBits N - 4) + a <
        N + szSections (addrBits N) (dataBits N)),
      (shannonCircuit N f hN).wireValue x
        ⟨N + oC (dataBits N) + (2 ^ addrBits N - 4) + a, haW⟩ =
      decide (a = Finset.sum Finset.univ
        (fun j : Fin (addrBits N) =>
          if x ⟨j.val, by have := j.isLt; have := addr_le_N N hN; omega⟩
          then 2 ^ j.val else 0)) := by
  intro a ha haW
  have hk3 := addrBits_ge_three N hN
  have hq2 := dataBits_ge_two N hN
  have h4k := pow_ge_4 (addrBits N) (by omega)
  have hkq := addrDataSum N hN
  set k := addrBits N
  set q := dataBits N
  set addr : BitString k := fun j => x ⟨j.val, by have := j.isLt; omega⟩
  set aSum := Finset.sum Finset.univ (fun j : Fin k => if addr j then 2 ^ j.val else 0)
  have haSum_lt : aSum < 2 ^ k := sum_cond_pow_fin_lt k addr
  have hk1 : 2 ^ (k + 1) = 2 * 2 ^ k := pow_double k
  have hsC : ∀ (j : Nat) (hj : j < 2 ^ (k + 1) - 4)
      (hjW : N + oC q + j < N + szSections k q),
      (shannonCircuit N f hN).wireValue x ⟨N + oC q + j, hjW⟩ =
      decide (∀ i : Fin (treeLevel j + 1),
        x ⟨i.val, by have := i.isLt; have := treeLevel_lt j k hj (by omega); omega⟩ =
        Nat.testBit (treePos j (treeLevel j)) i.val) := by
    intro j
    exact Nat.strongRecOn j fun j ih => by
      intro hj hjW
      rw [Circuit.wireValue_ge _ _ _ (by change ¬(N + oC q + j < N); omega)]
      change (shannonGateArray N f hN ⟨_, _⟩).val.eval _ = _
      unfold shannonGateArray
      simp only [show N + oC q + j - N = oC q + j from by omega]
      rw [dif_neg (by unfold oC; omega : ¬(oC q + j = 0))]
      rw [dif_neg (by unfold oC; omega : ¬(oC q + j < oC q))]
      rw [dif_pos (by unfold oD oC; omega : oC q + j < oD k q)]
      simp_rw [show oC q + j - oC (dataBits N) = j from by
        change oC q + j - oC q = j; omega]
      by_cases hjL1 : j < 4
      · rw [dif_pos hjL1]
        simp only [mkG, Gate.eval, Basis.andOr2, AONOp.eval,
          Fin.foldl_succ_last, Fin.foldl_zero, Bool.true_and]
        simp only [Fin.val_last, Fin.val_castSucc, ite_true, ite_false,
          show ¬((1 : Nat) = 0) from by omega]
        rw [Circuit.wireValue_lt _ _ _ (show (⟨0, _⟩ : Fin _).val < N from by
          change 0 < N; linarith [hkq, hk3])]
        rw [Circuit.wireValue_lt _ _ _ (show (⟨1, _⟩ : Fin _).val < N from by
          change 1 < N; linarith [hkq, hk3])]
        have htl : treeLevel j = 1 := by
          unfold treeLevel
          have : Nat.log 2 (j + 4) = 2 := le_antisymm
            (Nat.lt_succ_iff.mp (Nat.log_lt_of_lt_pow (by omega) (by omega)))
            (Nat.le_log_of_pow_le (by omega) (by omega))
          omega
        have htp : treePos j 1 = j := by unfold treePos treeBase; omega
        have hN2 : ∀ i : Nat, i < 2 → i < N := fun i hi => by linarith [hkq, hk3]
        have hcast : (∀ i : Fin (treeLevel j + 1),
            x ⟨i.val, by have := i.isLt; have := treeLevel_lt j k hj (by omega); omega⟩ =
            j.testBit i.val) ↔
            (∀ i : Fin 2, x ⟨i.val, hN2 i.val i.isLt⟩ = j.testBit i.val) := by
          constructor
          · intro h i; exact Eq.mpr (by congr 1) (h ⟨i.val, by rw [htl]; exact i.isLt⟩)
          · intro h ⟨i, hi⟩; exact Eq.mpr (by congr 1) (h ⟨i, by rw [htl] at hi; exact hi⟩)
        conv_rhs => rw [show treePos j (treeLevel j) = j from by rw [htl]; exact htp]
        rw [decide_eq_decide.mpr hcast] <;> [skip; exact inferInstance]
        simp only [Fin.forall_fin_two, Fin.val_zero, Fin.val_one, Nat.testBit_zero]
        cases x ⟨0, hN2 0 (by omega)⟩ <;> cases x ⟨1, hN2 1 (by omega)⟩ <;>
          cases j.testBit 1 <;> cases (decide (j % 2 = 1)) <;> simp_all
      · rw [dif_neg hjL1]
        simp only [mkG, Gate.eval, Basis.andOr2, AONOp.eval,
          Fin.foldl_succ_last, Fin.foldl_zero, Bool.true_and]
        simp only [Fin.val_last, Fin.val_castSucc, ite_true, ite_false,
          show ¬((1 : Nat) = 0) from by omega]
        have hl2 : 2 ≤ treeLevel j := treeLevel_ge_two j (by omega)
        have hlk : treeLevel j < k := treeLevel_lt j k hj (by omega)
        have hbase : treeBase (treeLevel j) ≤ j := treeBase_le_of_level j (by omega)
        have hpi_lt : treeParentIdx (treeLevel j) (treePos j (treeLevel j)) < j :=
          treeParentIdx_lt_j _ _ j hl2 rfl hbase
        simp only [Bool.false_xor]
        rw [Circuit.wireValue_lt _ _ _ (show (⟨treeLevel j, _⟩ : Fin _).val < N from by
          change treeLevel j < N; linarith [hkq, hlk])]
        have hpar := ih (treeParentIdx (treeLevel j) (treePos j (treeLevel j)))
          hpi_lt (by omega) (by omega)
        have htlp := treeLevel_parent (treeLevel j) (treePos j (treeLevel j)) hl2
        have htlp1 : treeLevel (treeParentIdx (treeLevel j) (treePos j (treeLevel j))) + 1 =
          treeLevel j := by omega
        have htpp : treePos (treeParentIdx (treeLevel j) (treePos j (treeLevel j)))
          (treeLevel (treeParentIdx (treeLevel j) (treePos j (treeLevel j)))) =
          treePos j (treeLevel j) % 2 ^ treeLevel j := by
          rw [htlp]; exact treePos_parent (treeLevel j) (treePos j (treeLevel j)) hl2
        change ((shannonCircuit N f hN).wireValue x
            ⟨N + oC (dataBits N) + treeParentIdx (treeLevel j) (treePos j (treeLevel j)),
              by linarith [hpi_lt]⟩ &&
          (!(treePos j (treeLevel j)).testBit (treeLevel j) ^^
            x ⟨treeLevel j, by linarith [hkq, hlk]⟩)) =
          decide (∀ (i : Fin (treeLevel j + 1)),
            x ⟨i.val, by have := i.isLt; linarith [hkq, hlk]⟩ =
            (treePos j (treeLevel j)).testBit i.val)
        rw [hpar]
        rw [Bool.eq_iff_iff, Bool.and_eq_true]
        constructor
        · rintro ⟨h1, h2⟩
          rw [decide_eq_true_eq] at h1 ⊢
          intro i
          by_cases hil : i.val < treeLevel j
          · have h1i := h1 ⟨i.val, by rw [htlp1]; exact hil⟩
            rw [htpp, Nat.testBit_mod_two_pow] at h1i
            simp only [show decide (i.val < treeLevel j) = true from
              decide_eq_true_eq.mpr hil, Bool.true_and] at h1i
            exact Eq.mpr (by congr 1) h1i
          · have hi_eq : i.val = treeLevel j := by have := i.isLt; omega
            exact Eq.mpr (by simp only [hi_eq])
              ((show ∀ (a b : Bool), (!b ^^ a) = true → a = b from by decide) _ _ h2)
        · intro h
          rw [decide_eq_true_eq] at h
          refine ⟨?_, ?_⟩
          · rw [decide_eq_true_eq]
            intro i
            have hi : i.val < treeLevel j := by omega
            rw [htpp, Nat.testBit_mod_two_pow]
            simp only [show decide (i.val < treeLevel j) = true from
              decide_eq_true_eq.mpr hi, Bool.true_and]
            exact Eq.mpr (by congr 1) (h ⟨i.val, by omega⟩)
          · exact (show ∀ (a b : Bool), a = b → (!b ^^ a) = true from by decide) _ _
              (Eq.mpr (by congr 1) (h ⟨treeLevel j, by omega⟩))
  specialize hsC (2 ^ k - 4 + a) (by omega)
    (by omega : N + oC q + (2 ^ k - 4 + a) < N + szSections k q)
  simp only [show N + oC q + (2 ^ k - 4 + a) = N + oC q + (2 ^ k - 4) + a from by omega] at hsC
  rw [hsC]
  conv_lhs => rw [show treePos (2 ^ k - 4 + a)
      (treeLevel (2 ^ k - 4 + a)) = a from by
    rw [show treeLevel (2 ^ k - 4 + a) = k - 1 from by
      unfold treeLevel; have : Nat.log 2 (2 ^ k - 4 + a + 4) = k := le_antisymm
        (Nat.lt_succ_iff.mp (Nat.log_lt_of_lt_pow (by omega) (by omega)))
        (Nat.le_log_of_pow_le (by omega) (by omega)); omega]
    unfold treePos treeBase; rw [show k - 1 + 1 = k from by omega]; omega]
  have hFin_eq : treeLevel (2 ^ k - 4 + a) + 1 = k := by
    have : treeLevel (2 ^ k - 4 + a) = k - 1 := by
      unfold treeLevel; have : Nat.log 2 (2 ^ k - 4 + a + 4) = k := le_antisymm
        (Nat.lt_succ_iff.mp (Nat.log_lt_of_lt_pow (by omega) (by omega)))
        (Nat.le_log_of_pow_le (by omega) (by omega)); omega
    omega
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq]
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < k
    · rw [testBit_sum_cond_pow_fin k addr i hi]
      exact Eq.mpr (by congr 1) (h ⟨i, by omega⟩).symm
    · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by omega) (by omega))),
          Nat.testBit_lt_two_pow
            (lt_of_lt_of_le haSum_lt (Nat.pow_le_pow_right (by omega) (by omega)))]
  · intro h i
    have hlt : i.val < k := by have := i.isLt; omega
    have e : aSum.testBit i.val = addr ⟨i.val, hlt⟩ :=
      testBit_sum_cond_pow_fin k addr i.val hlt
    have key : a.testBit i.val = addr ⟨i.val, hlt⟩ :=
      (congrArg (fun n => Nat.testBit n i.val) h).trans e
    exact Eq.mpr (by congr 1) key.symm

/-- The wire at index `N` (the shared constant-`false` source) outputs `false`.
(Extracted from `wireValue_colOutput`.) -/
private theorem colOutput_constFalse (N : Nat) [NeZero N]
    (f : BitString N → Bool) (hN : 16 ≤ N) (x : BitString N) :
    ∀ (hW : N < N + szSections (addrBits N) (dataBits N)),
      (shannonCircuit N f hN).wireValue x ⟨N, hW⟩ = false := by
  intro hW
  have hk3 := addrBits_ge_three N hN
  have hkq := addrDataSum N hN
  set k := addrBits N
  set q := dataBits N
  have h0N : (0 : Nat) < N := by linarith [hkq, hk3]
  rw [Circuit.wireValue_ge _ _ _ (show ¬((⟨N, hW⟩ : Fin _).val < N) from by change ¬(N < N); omega)]
  change (shannonGateArray N f hN ⟨_, _⟩).val.eval _ = _
  unfold shannonGateArray
  change (shannonGateArray N f hN ⟨N - N, by omega⟩).val.eval
    ((shannonCircuit N f hN).wireValue x) = false
  unfold shannonGateArray
  rw [dif_pos (show N - N = 0 from by omega)]
  simp only [mkG, Gate.eval, Basis.andOr2, AONOp.eval,
    Fin.foldl_succ_last, Fin.foldl_zero, Bool.true_and]
  simp only [Fin.val_last, Fin.val_castSucc, ite_true, ite_false,
    show ¬((1 : Nat) = 0) from by omega, Bool.false_xor, Bool.true_xor]
  rw [Circuit.wireValue_lt _ _ _ (show (⟨0, _⟩ : Fin _).val < N from h0N)]
  cases x ⟨0, h0N⟩ <;> rfl

private theorem wireValue_colOutput (N : Nat) [NeZero N]
    (f : BitString N → Bool) (hN : 16 ≤ N) (x : BitString N)
    (y : Nat) (hy : y < 2 ^ dataBits N)
    (hyW : N + oD (addrBits N) (dataBits N) +
      colPatIdx N f (addrBits N) (dataBits N) (addrDataSum N hN) ⟨y, hy⟩ *
        (2 ^ addrBits N - 1) + (2 ^ addrBits N - 2) <
      N + szSections (addrBits N) (dataBits N)) :
    (shannonCircuit N f hN).wireValue x
      ⟨N + oD (addrBits N) (dataBits N) +
        colPatIdx N f (addrBits N) (dataBits N) (addrDataSum N hN) ⟨y, hy⟩ *
          (2 ^ addrBits N - 1) + (2 ^ addrBits N - 2), hyW⟩ =
    colFun N f (addrBits N) (dataBits N) (addrDataSum N hN) ⟨y, hy⟩
      ⟨Finset.sum Finset.univ (fun j : Fin (addrBits N) =>
        if (x ⟨j.val, by have := j.isLt; have := addr_le_N N hN; omega⟩) = true
        then 2 ^ j.val else 0),
       sum_cond_pow_fin_lt (addrBits N) (fun j =>
        x ⟨j.val, by have := j.isLt; have := addr_le_N N hN; omega⟩)⟩ := by
  have hk3 := addrBits_ge_three N hN
  have hq2 := dataBits_ge_two N hN
  have h4k := pow_ge_4 (addrBits N) (by omega)
  have hkq := addrDataSum N hN
  set k := addrBits N
  set q := dataBits N
  set p := colPatIdx N f k q hkq ⟨y, hy⟩
  set addr : BitString k := fun j => x ⟨j.val, by have := j.isLt; omega⟩
  set aSum := Finset.sum Finset.univ (fun j : Fin k => if addr j then 2 ^ j.val else 0)
  have hp_lt : p < 2 ^ (2 ^ k) := colPatIdx_lt N f k q hkq ⟨y, hy⟩
  have haSum_lt : aSum < 2 ^ k := sum_cond_pow_fin_lt k addr
  have hblk : 0 < 2 ^ k - 1 := by omega
  have hbk : (2 : Nat) ^ addrBits N = 2 ^ k := rfl
  have addrLeaf : ∀ (a : Nat) (_ha : a < 2 ^ k)
      (haW : N + oC q + (2 ^ k - 4) + a < N + szSections k q),
      (shannonCircuit N f hN).wireValue x
        ⟨N + oC q + (2 ^ k - 4) + a, haW⟩ = decide (a = aSum) :=
    colOutput_addrLeaf N f hN x
  have constFalse_wire : ∀ (hW : N < N + szSections k q),
      (shannonCircuit N f hN).wireValue x ⟨N, hW⟩ = false :=
    colOutput_constFalse N f hN x
  have colChain : ∀ (r : Nat) (hr : r < 2 ^ k - 1)
      (hrW : N + oD k q + p * (2 ^ k - 1) + r < N + szSections k q),
      (shannonCircuit N f hN).wireValue x
        ⟨N + oD k q + p * (2 ^ k - 1) + r, hrW⟩ =
      (List.range (r + 2)).foldl
        (fun acc a => acc || (Nat.testBit p a && decide (a = aSum))) false := by
    intro r hr hrW
    have hsz_eq : szSections k q = szSections (addrBits N) (dataBits N) := rfl
    have hoC_eq : oC q = oC (dataBits N) := rfl
    have hW_bound : N + oC q + (2 ^ k - 4) + (2 ^ k) ≤ N + szSections k q := by
      have : oD k q ≤ szSections k q := by
        change oD (addrBits N) (dataBits N) ≤ szSections (addrBits N) (dataBits N)
        unfold szSections oD oC; omega
      have : oC q + (2 ^ k - 4) + 2 ^ k ≤ oD k q := by
        change oC (dataBits N) + (2 ^ (addrBits N) - 4) + 2 ^ (addrBits N) ≤
          oD (addrBits N) (dataBits N)
        unfold oD oC
        have : 2 ^ (addrBits N + 1) - 4 = (2 ^ addrBits N - 4) + 2 ^ addrBits N := by
          have := pow_double (addrBits N)
          have := pow_ge_4 (addrBits N) (show 2 ≤ addrBits N from by omega)
          omega
        linarith
      omega
    have hoE_lt : oD k q + p * (2 ^ k - 1) + (2 ^ k - 1) ≤ oE k q := by
      change oD (addrBits N) (dataBits N) +
        colPatIdx N f (addrBits N) (dataBits N) (addrDataSum N hN) ⟨y, hy⟩ *
          (2 ^ (addrBits N) - 1) + (2 ^ (addrBits N) - 1) ≤
        oE (addrBits N) (dataBits N)
      unfold oE oD
      have := Nat.mul_le_mul_right (2 ^ (addrBits N) - 1)
        (show colPatIdx N f (addrBits N) (dataBits N) (addrDataSum N hN) ⟨y, hy⟩ + 1 ≤
          2 ^ (2 ^ addrBits N) from by exact hp_lt)
      nlinarith
    have hsel_bound (pos : Nat) (hpos : pos < 2 ^ k) :
        N + oC q + (2 ^ k - 4) + pos < N + szSections k q :=
      lt_of_lt_of_le (show N + oC q + (2 ^ k - 4) + pos <
        N + oC q + (2 ^ k - 4) + 2 ^ k from by omega) hW_bound
    have selWire (pos : Nat) (hpos : pos < 2 ^ k) :
        (if Nat.testBit p pos then
          (shannonCircuit N f hN).wireValue x
            ⟨N + oC q + (2 ^ k - 4) + pos, hsel_bound pos hpos⟩
         else
          (shannonCircuit N f hN).wireValue x ⟨N, by linarith [hsel_bound pos hpos]⟩) =
        (Nat.testBit p pos && decide (pos = aSum)) := by
      split_ifs with htb
      · have h := colOutput_addrLeaf N f hN x pos hpos (hsel_bound pos hpos)
        rw [show (Nat.testBit p pos && decide (pos = aSum)) = decide (pos = aSum) from by
          simp [htb]]
        exact h
      · have h := colOutput_constFalse N f hN x (by linarith [hsel_bound pos hpos])
        rw [show (Nat.testBit p pos && decide (pos = aSum)) = false from by simp [htb]]
        exact h
    induction r with
    | zero =>
      have h_ne0 : oD k q + p * (2 ^ k - 1) ≠ 0 := by
        change oD (addrBits N) (dataBits N) + colPatIdx N f (addrBits N) (dataBits N)
          (addrDataSum N hN)
          ⟨y, hy⟩ * (2 ^ (addrBits N) - 1) ≠ 0
        unfold oD oC; omega
      have h_ge_oC : ¬(oD k q + p * (2 ^ k - 1) < oC q) := by
        simp only [show k = addrBits N from rfl, show q = dataBits N from rfl] at *
        unfold oD oC; omega
      have h_ge_oD : ¬(oD k q + p * (2 ^ k - 1) < oD k q) := by omega
      have h_lt_oE : oD k q + p * (2 ^ k - 1) < oE k q := by linarith [hoE_lt]
      rw [Circuit.wireValue_ge _ _ _ (by
        change ¬(N + oD k q + p * (2 ^ k - 1) + 0 < N); omega)]
      change (shannonGateArray N f hN ⟨_, _⟩).val.eval _ = _
      unfold shannonGateArray
      simp only [show N + oD k q + p * (2 ^ k - 1) + 0 - N =
        oD k q + p * (2 ^ k - 1) from by omega]
      rw [dif_neg h_ne0, dif_neg h_ge_oC, dif_neg h_ge_oD, dif_pos h_lt_oE]
      simp only [show addrBits N = k from rfl, show dataBits N = q from rfl]
      simp only [show oD k q + p * (2 ^ k - 1) - oD k q =
        p * (2 ^ k - 1) from by omega]
      simp_rw [show p * (2 ^ k - 1) % (2 ^ k - 1) = 0 from by
        rw [Nat.mul_comm]; exact Nat.mul_mod_right _ _]
      simp only [show p * (2 ^ k - 1) / (2 ^ k - 1) = p from Nat.mul_div_cancel p hblk]
      simp only [mkG, Gate.eval, Basis.andOr2, AONOp.eval,
        Fin.foldl_succ_last, Fin.foldl_zero, Bool.false_or]
      simp only [Fin.val_last, Fin.val_castSucc, ite_true, ite_false,
        show ¬((1 : Nat) = 0) from by omega, Bool.false_xor,
        show (0 : Nat) + 1 = 1 from by omega]
      conv_rhs => rw [show (0 : Nat) + 2 = 2 from rfl,
        show (2 : Nat) = 1 + 1 from rfl, List.range_succ,
        show (1 : Nat) = 0 + 1 from rfl, List.range_succ, List.range_zero]
      simp only [List.nil_append, List.foldl_append, List.foldl_cons, List.foldl_nil, Bool.false_or]
      congr 1 <;> split_ifs with htb
      · simp only [htb, Bool.true_and]
        exact colOutput_addrLeaf N f hN x _ (hbk ▸ (show _ < 2 ^ k by omega)) _
      · simp only [Bool.eq_false_iff.mpr htb, Bool.false_and]; exact colOutput_constFalse N f hN x _
      · simp only [htb, Bool.true_and]
        exact colOutput_addrLeaf N f hN x _ (hbk ▸ (show _ < 2 ^ k by omega)) _
      · simp only [Bool.eq_false_iff.mpr htb, Bool.false_and]; exact colOutput_constFalse N f hN x _
    | succ r' ih =>
      have h_ne0' : oD k q + p * (2 ^ k - 1) + (r' + 1) ≠ 0 := by
        change oD (addrBits N) (dataBits N) + colPatIdx N f (addrBits N) (dataBits N)
          (addrDataSum N hN)
          ⟨y, hy⟩ * (2 ^ (addrBits N) - 1) + (r' + 1) ≠ 0
        unfold oD oC; omega
      have h_ge_oC' : ¬(oD k q + p * (2 ^ k - 1) + (r' + 1) < oC q) := by
        simp only [show k = addrBits N from rfl, show q = dataBits N from rfl] at *
        unfold oD oC; omega
      have h_ge_oD' : ¬(oD k q + p * (2 ^ k - 1) + (r' + 1) < oD k q) := by omega
      have h_lt_oE' : oD k q + p * (2 ^ k - 1) + (r' + 1) < oE k q := by linarith [hoE_lt]
      rw [Circuit.wireValue_ge _ _ _ (by
        change ¬(N + oD k q + p * (2 ^ k - 1) + (r' + 1) < N); omega)]
      change (shannonGateArray N f hN ⟨_, _⟩).val.eval _ = _
      unfold shannonGateArray
      simp only [show N + oD k q + p * (2 ^ k - 1) + (r' + 1) - N =
        oD k q + p * (2 ^ k - 1) + (r' + 1) from by omega]
      rw [dif_neg h_ne0', dif_neg h_ge_oC', dif_neg h_ge_oD', dif_pos h_lt_oE']
      simp only [show addrBits N = k from rfl, show dataBits N = q from rfl]
      simp_rw [show (oD k q + p * (2 ^ k - 1) + (r' + 1) - oD k q) =
        p * (2 ^ k - 1) + (r' + 1) from by omega]
      simp only [show (p * (2 ^ k - 1) + (r' + 1)) / (2 ^ k - 1) = p from
        Nat.div_eq_of_lt_le (by omega)
          (show p * (2 ^ k - 1) + (r' + 1) < (p + 1) * (2 ^ k - 1) by nlinarith),
        show (p * (2 ^ k - 1) + (r' + 1)) % (2 ^ k - 1) = r' + 1 from by
          rw [show p * (2 ^ k - 1) + (r' + 1) = (r' + 1) + (2 ^ k - 1) * p from by ring,
              Nat.add_mul_mod_self_left]; exact Nat.mod_eq_of_lt (by omega)]
      simp only [show r' + 1 ≠ 0 from by omega, ite_false,
        show r' + 1 - 1 = r' from by omega]
      simp only [mkG, Gate.eval, Basis.andOr2, AONOp.eval,
        Fin.foldl_succ_last, Fin.foldl_zero, Bool.false_or]
      simp only [Fin.val_last, Fin.val_castSucc, ite_true, ite_false,
        show ¬((1 : Nat) = 0) from by omega, Bool.false_xor,
        show r' + 1 + 1 = r' + 2 from by omega]
      conv_rhs => rw [show r' + 2 + 1 = (r' + 1) + 2 from by omega,
        List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      congr 1
      · exact ih (by omega) (by omega)
      · split_ifs with htb2
        · simp only [htb2, Bool.true_and]
          exact colOutput_addrLeaf N f hN x _ (hbk ▸ (show _ < 2 ^ k by omega)) _
        · simp only [Bool.eq_false_iff.mpr htb2, Bool.false_and]
          exact colOutput_constFalse N f hN x _
  change (shannonCircuit N f hN).wireValue x
    ⟨N + oD k q + p * (2 ^ k - 1) + (2 ^ k - 2), by omega⟩ = _
  rw [colChain (2 ^ k - 2) (by omega) (by omega)]
  rw [show (2 ^ k - 2) + 2 = 2 ^ k from by omega]
  have hfold := foldl_or_unique_true aSum haSum_lt
    (P := fun a => Nat.testBit p a && decide (a = aSum))
    (fun a _ hne => by simp [show ¬(a = aSum) from hne])
  rw [hfold]; simp only [decide_true, Bool.and_true]
  change (colPatIdx N f k q hkq ⟨y, hy⟩).testBit aSum = _
  unfold colPatIdx
  rw [encodeCol]
  rw [testBit_sum_cond_pow_fin (2 ^ k) _ aSum haSum_lt]

/-! ### OR chain induction

    The deep wireValue unfolding through all 6 sections (required for
    wireValue_andLayer_sem) and the gate array branch analysis make this
    the most technically challenging part of the formalization. -/
private theorem wireValue_orChain_sem (N : Nat) [NeZero N]
    (f : BitString N → Bool) (hN : 16 ≤ N) (x : BitString N)
    (r : Nat) (hr : r < 2 ^ dataBits N - 1)
    (hW : N + oF (addrBits N) (dataBits N) + r <
          N + szSections (addrBits N) (dataBits N)) :
    (shannonCircuit N f hN).wireValue x
      ⟨N + oF (addrBits N) (dataBits N) + r, hW⟩ =
    (List.range (r + 2)).foldl
      (fun acc y => acc || if h : y < 2 ^ dataBits N
        then andLayerSem N f hN x y h else false) false := by
  have andLayer_sem : ∀ (y : Nat) (hy : y < 2 ^ dataBits N)
      (hyW : N + oE (addrBits N) (dataBits N) + y <
            N + szSections (addrBits N) (dataBits N)),
      (shannonCircuit N f hN).wireValue x
        ⟨N + oE (addrBits N) (dataBits N) + y, hyW⟩ =
      andLayerSem N f hN x y hy := by
    intro y hy hyW
    rw [Circuit.wireValue_ge _ _ _ (by
      change ¬(N + oE (addrBits N) (dataBits N) + y < N); omega)]
    change (shannonGateArray N f hN ⟨_, _⟩).val.eval _ = _
    unfold shannonGateArray
    simp only [show N + oE (addrBits N) (dataBits N) + y - N =
      oE (addrBits N) (dataBits N) + y from by omega]
    rw [dif_neg (by unfold oE oD oC; have := pow_ge_4 (dataBits N) (dataBits_ge_two N hN); omega :
      ¬(oE (addrBits N) (dataBits N) + y = 0))]
    rw [dif_neg (by unfold oE oD oC; omega :
      ¬(oE (addrBits N) (dataBits N) + y < oC (dataBits N)))]
    rw [dif_neg (by unfold oE oD; omega :
      ¬(oE (addrBits N) (dataBits N) + y < oD (addrBits N) (dataBits N)))]
    rw [dif_neg (by unfold oE; omega :
      ¬(oE (addrBits N) (dataBits N) + y < oE (addrBits N) (dataBits N)))]
    rw [dif_pos (by unfold oF; omega :
      oE (addrBits N) (dataBits N) + y < oF (addrBits N) (dataBits N))]
    simp only [mkG, Gate.eval, Basis.andOr2, AONOp.eval,
      Fin.foldl_succ_last, Fin.foldl_zero, Bool.true_and, ite_self, Bool.false_xor]
    simp only [Fin.val_last, Fin.val_castSucc, ite_true, ite_false,
      show ¬((1 : Nat) = 0) from by omega,
      show oE (addrBits N) (dataBits N) + y - oE (addrBits N) (dataBits N) = y from by omega]
    unfold andLayerSem
    congr 1
    · exact wireValue_dataLeaf N f hN x y hy _
    · exact wireValue_colOutput N f hN x y hy _
  have hoEF : oE (addrBits N) (dataBits N) + 2 ^ dataBits N =
      oF (addrBits N) (dataBits N) := by unfold oF; ring
  have hoFsz : oF (addrBits N) (dataBits N) + (2 ^ dataBits N - 1) =
      szSections (addrBits N) (dataBits N) := by unfold szSections oF oE oD oC; omega
  have hq2 := dataBits_ge_two N hN
  have h4q := pow_ge_4 (dataBits N) hq2
  induction r with
  | zero =>
    rw [Circuit.wireValue_ge _ _ _ (show ¬((⟨N + oF (addrBits N) (dataBits N) + 0, hW⟩ :
        Fin _).val < N) from by change ¬(N + oF (addrBits N) (dataBits N) + 0 < N); omega)]
    change (shannonGateArray N f hN ⟨_, _⟩).val.eval _ = _
    unfold shannonGateArray
    simp only [show N + oF (addrBits N) (dataBits N) + 0 - N =
      oF (addrBits N) (dataBits N) + 0 from by omega]
    rw [dif_neg (by unfold oF oE oD oC; omega : ¬(oF (addrBits N) (dataBits N) + 0 = 0))]
    rw [dif_neg (by unfold oF oE oD oC; omega :
      ¬(oF (addrBits N) (dataBits N) + 0 < oC (dataBits N)))]
    rw [dif_neg (by unfold oF oE oD; omega :
      ¬(oF (addrBits N) (dataBits N) + 0 < oD (addrBits N) (dataBits N)))]
    rw [dif_neg (by unfold oF oE; omega :
      ¬(oF (addrBits N) (dataBits N) + 0 < oE (addrBits N) (dataBits N)))]
    rw [dif_neg (by omega :
      ¬(oF (addrBits N) (dataBits N) + 0 < oF (addrBits N) (dataBits N)))]
    simp only [mkG, Gate.eval, Basis.andOr2, AONOp.eval,
      Fin.foldl_succ_last, Fin.foldl_zero, Bool.false_or, ite_self, Bool.false_xor]
    simp only [show oF (addrBits N) (dataBits N) + 0 - oF (addrBits N) (dataBits N) = 0
      from by omega, ite_true,
      Fin.val_last, Fin.val_castSucc, ite_false,
      show ¬((1 : Nat) = 0) from by omega,
      show (0 : Nat) + 1 = 1 from by omega]
    change ((shannonCircuit N f hN).wireValue x
        ⟨N + oE (addrBits N) (dataBits N) + 0, by linarith⟩ ||
      (shannonCircuit N f hN).wireValue x
        ⟨N + oE (addrBits N) (dataBits N) + 1, by linarith⟩) =
      List.foldl (fun acc y => acc || if h : y < 2 ^ dataBits N
        then andLayerSem N f hN x y h else false) false (List.range (0 + 2))
    rw [andLayer_sem 0 (by omega) (by linarith),
        andLayer_sem 1 (by omega) (by linarith)]
    simp only [show List.range (0 + 2) = [0, 1] from by decide,
      List.foldl_cons, List.foldl_nil,
      Bool.false_or, dif_pos (show 0 < 2 ^ dataBits N from by omega),
      dif_pos (show 1 < 2 ^ dataBits N from by omega)]
  | succ r' ih =>
    rw [Circuit.wireValue_ge _ _ _ (show ¬((⟨N + oF (addrBits N) (dataBits N) + (r' + 1), hW⟩ :
        Fin _).val < N) from by change ¬(N + oF (addrBits N) (dataBits N) + (r' + 1) < N); omega)]
    change (shannonGateArray N f hN ⟨_, _⟩).val.eval _ = _
    unfold shannonGateArray
    simp only [show N + oF (addrBits N) (dataBits N) + (r' + 1) - N =
      oF (addrBits N) (dataBits N) + (r' + 1) from by omega]
    rw [dif_neg (by unfold oF oE oD oC; omega :
      ¬(oF (addrBits N) (dataBits N) + (r' + 1) = 0))]
    rw [dif_neg (by unfold oF oE oD oC; omega :
      ¬(oF (addrBits N) (dataBits N) + (r' + 1) < oC (dataBits N)))]
    rw [dif_neg (by unfold oF oE oD; omega :
      ¬(oF (addrBits N) (dataBits N) + (r' + 1) < oD (addrBits N) (dataBits N)))]
    rw [dif_neg (by unfold oF oE; omega :
      ¬(oF (addrBits N) (dataBits N) + (r' + 1) < oE (addrBits N) (dataBits N)))]
    rw [dif_neg (by omega :
      ¬(oF (addrBits N) (dataBits N) + (r' + 1) < oF (addrBits N) (dataBits N)))]
    simp only [mkG, Gate.eval, Basis.andOr2, AONOp.eval,
      Fin.foldl_succ_last, Fin.foldl_zero, Bool.false_or, ite_self, Bool.false_xor]
    simp only [show oF (addrBits N) (dataBits N) + (r' + 1) -
      oF (addrBits N) (dataBits N) = r' + 1 from by omega,
      show r' + 1 ≠ 0 from by omega, ite_false,
      show r' + 1 - 1 = r' from by omega]
    have hr' : r' < 2 ^ dataBits N - 1 := by omega
    have hW' : N + oF (addrBits N) (dataBits N) + r' <
        N + szSections (addrBits N) (dataBits N) := by linarith
    simp only [Fin.val_last, Fin.val_castSucc, ite_true, ite_false,
      show ¬((1 : Nat) = 0) from by omega]
    have hih := ih hr' hW'
    simp only [show r' + 1 + 1 = r' + 2 from by omega]
    change ((shannonCircuit N f hN).wireValue x ⟨N + oF (addrBits N) (dataBits N) + r', hW'⟩ ||
         (shannonCircuit N f hN).wireValue x
           ⟨N + oE (addrBits N) (dataBits N) + (r' + 2), by linarith⟩) =
        List.foldl (fun acc y => acc || if h : y < 2 ^ dataBits N
          then andLayerSem N f hN x y h else false) false (List.range (r' + 1 + 2))
    rw [hih, andLayer_sem (r' + 2) (by omega) (by linarith)]
    rw [show r' + 1 + 2 = (r' + 2) + 1 from by omega,
        List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hr2 : r' + 2 < 2 ^ dataBits N := by omega
    rw [show andLayerSem N f hN x (r' + 2) hr2 =
      (if h : r' + 2 < 2 ^ dataBits N then andLayerSem N f hN x (r' + 2) h else false) from
      by rw [dif_pos hr2]]
    rw [Bool.or_assoc]
    simp only [show r' + 1 + 2 = r' + 2 + 1 from by omega,
      show r' + 2 = r' + 1 + 1 from by omega,
      List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      dif_pos (show r' + 2 < 2 ^ dataBits N from by omega),
      dif_pos (show r' + 1 < 2 ^ dataBits N from by omega),
      Bool.or_assoc]

private theorem lastOrChain_eq_f (N : Nat) [NeZero N]
    (f : BitString N → Bool) (hN : 16 ≤ N) (x : BitString N)
    (hW : N + oF (addrBits N) (dataBits N) + (2 ^ dataBits N - 2) <
          N + szSections (addrBits N) (dataBits N)) :
    (shannonCircuit N f hN).wireValue x
      ⟨N + oF (addrBits N) (dataBits N) + (2 ^ dataBits N - 2), hW⟩ = f x := by
  have hq2 : 2 ≤ dataBits N := dataBits_ge_two N hN
  have h4q : 4 ≤ 2 ^ dataBits N := pow_ge_4 (dataBits N) hq2
  -- Step 1: OR chain at last position = foldl of AND semantic values
  have hr : 2 ^ dataBits N - 2 < 2 ^ dataBits N - 1 := by omega
  rw [wireValue_orChain_sem N f hN x (2 ^ dataBits N - 2) hr hW]
  -- Step 2: range length (2^q - 2) + 2 = 2^q
  have hrange : (2 ^ dataBits N - 2) + 2 = 2 ^ dataBits N := by omega
  rw [hrange]
  -- Step 3: OR of all AND semantic values = f(x)
  exact or_andLayerSem_eq_f N f hN x

/-! ##### Main correctness theorem -/

/-- The last wire of the Shannon circuit evaluates to f x.

The correctness argument proceeds in two steps:
1. The last wire index = oF(k,q) + (2^q - 2)  (lastWire_is_orChain_last)
2. That wire evaluates to f(x)  (lastOrChain_eq_f) -/
private theorem shannon_lastWire_correct (N : Nat) [NeZero N]
    (f : BitString N → Bool) (hN : 16 ≤ N) (x : BitString N) :
    (shannonCircuit N f hN).wireValue x
      ⟨N + szSections (addrBits N) (dataBits N) - 1,
       by have := szSections_pos (addrBits N) (dataBits N); omega⟩ = f x := by
  -- Step 1: rewrite last wire index as oF k q + (2^q - 2)
  have hlast := lastWire_is_orChain_last N hN
  have hq2 : 2 ≤ dataBits N := dataBits_ge_two N hN
  have h4q : 4 ≤ 2 ^ dataBits N := pow_ge_4 (dataBits N) hq2
  have hW_or : N + oF (addrBits N) (dataBits N) + (2 ^ dataBits N - 2) <
    N + szSections (addrBits N) (dataBits N) := by
    unfold szSections oF oE oD oC; omega
  have hfin_eq :
    (⟨N + szSections (addrBits N) (dataBits N) - 1,
      by have := szSections_pos (addrBits N) (dataBits N); omega⟩ :
      Fin (N + szSections (addrBits N) (dataBits N))) =
    ⟨N + oF (addrBits N) (dataBits N) + (2 ^ dataBits N - 2), hW_or⟩ := by
    ext; exact hlast
  rw [hfin_eq]
  -- Step 2: that wire = f(x)
  exact lastOrChain_eq_f N f hN x hW_or

private theorem shannonCircuit_correct (N : Nat) [NeZero N]
    (f : BitString N → Bool) (hN : 16 ≤ N) (x : BitString N) :
    ((shannonCircuit N f hN).eval x) 0 = f x := by
  -- eval at output 0 = outputs-gate.eval(wireValue)
  simp only [Circuit.eval, shannonCircuit, Gate.eval, Basis.andOr2]
  rw [AONOp.eval_two_or]
  simp only [Bool.false_xor, Bool.or_self]
  exact shannon_lastWire_correct N f hN x

private theorem szSections_le_bound (N : Nat) (_hN : 16 ≤ N) :
    szSections (addrBits N) (dataBits N) + 1 ≤
      4 * 2 ^ dataBits N + 2 * 2 ^ addrBits N + 2 ^ (2 ^ addrBits N + addrBits N) := by
  unfold szSections
  have hq1 : 1 ≤ 2 ^ dataBits N := Nat.one_le_two_pow
  have hk1 : 1 ≤ 2 ^ addrBits N := Nat.one_le_two_pow
  rw [show dataBits N + 1 = (dataBits N).succ from rfl, Nat.pow_succ]
  rw [show addrBits N + 1 = (addrBits N).succ from rfl, Nat.pow_succ]
  have hlib : 2 ^ (2 ^ addrBits N) * (2 ^ addrBits N - 1) ≤
      2 ^ (2 ^ addrBits N + addrBits N) := by
    calc 2 ^ (2 ^ addrBits N) * (2 ^ addrBits N - 1)
        ≤ 2 ^ (2 ^ addrBits N) * 2 ^ addrBits N := Nat.mul_le_mul_left _ (by omega)
      _ = 2 ^ (2 ^ addrBits N + addrBits N) := by rw [← Nat.pow_add]
  omega

theorem shannon_assembly (N : Nat) [NeZero N] (hN : 16 ≤ N)
    (f : BitString N → Bool) :
    ∃ G, ∃ c : Circuit Basis.andOr2 N 1 G,
      (fun x => (c.eval x) 0) = f ∧
      G + 1 ≤ 4 * 2 ^ dataBits N + 2 * 2 ^ addrBits N +
          2 ^ (2 ^ addrBits N + addrBits N) := by
  exact ⟨szSections (addrBits N) (dataBits N),
    shannonCircuit N f hN,
    funext (shannonCircuit_correct N f hN),
    szSections_le_bound N hN⟩

/-! ## Main Theorem -/

/-- **Shannon circuit construction**: For `N ≥ 16`, every Boolean function
    has a fan-in-2 AND/OR circuit of size `≤ 18 · 2^N / N`. -/
theorem shannon_construction (N : Nat) [NeZero N] (hN : 16 ≤ N)
    (f : BitString N → Bool) :
    ∃ G, ∃ c : Circuit Basis.andOr2 N 1 G,
      (fun x => (c.eval x) 0) = f ∧ c.size ≤ 18 * 2 ^ N / N := by
  obtain ⟨G, c, heval, hG⟩ := shannon_assembly N hN f
  exact ⟨G, c, heval, by rw [Circuit.size]; exact shannon_size_le N hN G hG⟩

end ShannonUpper

end CircuitComplexity



