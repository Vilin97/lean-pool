/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import LeanPool.CircuitComplexity.NF.Defs
import LeanPool.CircuitComplexity.AON.Defs
import Mathlib.Data.Fintype.BigOperators

/-! # Internal: Normal Form Proof Machinery

This internal module contains the proof infrastructure for CNF/DNF:

* **Circuit embedding**: `CNF.toCircuit` and `DNF.toCircuit` embed normal form
  formulas as 2-level circuits over `Basis.unboundedAON`, together with
  correctness (`eval_toCircuit`) and size (`size_toCircuit`) proofs.

* **Lower bound machinery**: `DNF.flip_complexity_lb` shows that any DNF
  computing a flip-sensitive function on `N` variables needs at least `2^{N-1}`
  terms. Key lemmas include `term_mentions_all`, `full_term_unique`, and
  `card_true_of_flip_sensitive`.

The public interface re-exports the main theorems from `Circ.NF`.
-/

namespace CircuitComplexity


/-! ## Helper lemmas for toCircuit correctness -/

private lemma xor_neg_polarity_eq_eval (l : Literal N) (x : BitString N) :
    (!l.polarity).xor (x l.var) = l.eval x := by
  simp only [Literal.eval]
  cases l.polarity <;> simp

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
    rw [Fin.foldl_succ_last, Bool.and_eq_true]
    refine ⟨fun ⟨h1, h2⟩ i => Fin.lastCases h2 (fun j => (ih _).mp h1 j) i, fun h => ?_⟩
    exact ⟨(ih _).mpr (fun j => h j.castSucc), h (Fin.last n)⟩

private lemma foldl_bor_eq_list_any {α : Type} (l : List α) (p : α → Bool) :
    Fin.foldl l.length (fun acc (i : Fin l.length) => acc || p (l.get i)) false = l.any p := by
  have h_iff : (Fin.foldl l.length (fun acc i => acc || p (l.get i)) false = true) ↔
      (l.any p = true) := by
    rw [foldl_bor_eq_true, List.any_eq_true]
    refine ⟨fun ⟨i, hi⟩ => ⟨l.get i, List.get_mem l i, hi⟩, fun ⟨a, ha, hp⟩ => ?_⟩
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp ha
    exact ⟨i, hp⟩
  cases h1 : Fin.foldl l.length (fun acc i => acc || p (l.get i)) false <;>
    cases h2 : l.any p <;> simp_all

private lemma foldl_band_eq_list_all {α : Type} (l : List α) (p : α → Bool) :
    Fin.foldl l.length (fun acc (i : Fin l.length) => acc && p (l.get i)) true = l.all p := by
  have h_iff : (Fin.foldl l.length (fun acc i => acc && p (l.get i)) true = true) ↔
      (l.all p = true) := by
    rw [foldl_band_eq_true, List.all_eq_true]
    refine ⟨fun h a ha => ?_, fun h i => h (l.get i) (List.get_mem l i)⟩
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp ha
    exact h i
  cases h1 : Fin.foldl l.length (fun acc i => acc && p (l.get i)) true <;>
    cases h2 : l.all p <;> simp_all

/-! ## CNF circuit embedding -/

namespace CNF

/-- Embed a CNF formula as a 2-level AND-of-ORs circuit over `Basis.unboundedAON`.

The circuit has `φ.complexity` internal OR gates (one per clause) and a single
output AND gate. Each OR gate reads only primary input wires, with the `negated`
flag encoding literal polarity. The circuit size is `φ.complexity + 1`. -/
def toCircuit {N : Nat} [NeZero N] (φ : CNF N) :
    Circuit Basis.unboundedAON N 1 φ.complexity where
  gates i :=
    let clause := φ.clauses.get ⟨i.val, i.isLt⟩
    { op := .or
      fanIn := clause.length
      arityOk := trivial
      inputs := fun j => ⟨(clause.get j).var.val, by
        have := (clause.get j).var.isLt; omega⟩
      negated := fun j => !(clause.get j).polarity }
  outputs _ :=
    { op := .and
      fanIn := φ.complexity
      arityOk := trivial
      inputs := fun j => ⟨N + j.val, by omega⟩
      negated := fun _ => false }
  acyclic i j :=
    Nat.lt_of_lt_of_le
      ((φ.clauses.get ⟨i.val, i.isLt⟩).get ⟨j.val, j.isLt⟩).var.isLt
      (Nat.le_add_right N i.val)

private lemma wireValue_gate [NeZero N] (φ : CNF N) (x : BitString N) (i : Fin φ.complexity) :
    φ.toCircuit.wireValue x ⟨N + i.val, by omega⟩ =
      (φ.clauses.get ⟨i.val, i.isLt⟩).any (fun l => l.eval x) := by
  have hge : ¬ ((⟨N + ↑i, (by omega)⟩ : Fin (N + φ.complexity)).val < N) := by simp
  rw [Circuit.wireValue_ge _ x _ hge]
  -- Normalize gate index
  have hgi : φ.toCircuit.gates ⟨(⟨N + ↑i, (by omega)⟩ : Fin (N + φ.complexity)).val - N,
    (by omega)⟩ = φ.toCircuit.gates i := by congr 1; ext; simp
  rw [hgi]
  -- Unfold gate definition
  simp only [toCircuit, Gate.eval, Basis.unboundedAON, AONOp.eval]
  -- Handle wireValue for primary inputs + xor-negation inside foldl
  conv_lhs => arg 2; ext acc j; arg 2
              rw [Circuit.wireValue_lt _ _ _
                ((φ.clauses.get ⟨↑i, i.isLt⟩).get j).var.isLt, xor_neg_polarity_eq_eval]
  exact foldl_bor_eq_list_any (φ.clauses.get ⟨↑i, i.isLt⟩) (fun l => l.eval x)

/-- The circuit produced by `toCircuit` correctly computes the CNF formula. -/
theorem eval_toCircuit [NeZero N] (φ : CNF N) :
    (fun x => (φ.toCircuit.eval x) 0) = φ.eval := by
  funext x
  simp only [Circuit.eval, eval, toCircuit, Gate.eval, Basis.unboundedAON, Bool.false_xor,
    AONOp.eval]
  -- Convert struct-literal wireValue back to φ.toCircuit form for wireValue_gate
  change Fin.foldl φ.complexity
    (fun acc j => acc && φ.toCircuit.wireValue x ⟨N + j.val, by omega⟩) true =
    φ.clauses.all (fun clause => clause.any fun l => l.eval x)
  conv_lhs => arg 2; ext acc j; arg 2; rw [wireValue_gate φ x j]
  exact foldl_band_eq_list_all φ.clauses (fun clause => clause.any fun l => l.eval x)

/-- The circuit size of `toCircuit` is `φ.complexity + 1`. -/
theorem size_toCircuit [NeZero N] (φ : CNF N) :
    φ.toCircuit.size = φ.complexity + 1 := rfl

end CNF

/-! ## DNF circuit embedding -/

namespace DNF

/-- Embed a DNF formula as a 2-level OR-of-ANDs circuit over `Basis.unboundedAON`.

The circuit has `φ.complexity` internal AND gates (one per term) and a single
output OR gate. Each AND gate reads only primary input wires, with the `negated`
flag encoding literal polarity. The circuit size is `φ.complexity + 1`. -/
def toCircuit {N : Nat} [NeZero N] (φ : DNF N) :
    Circuit Basis.unboundedAON N 1 φ.complexity where
  gates i :=
    let term := φ.terms.get ⟨i.val, i.isLt⟩
    { op := .and
      fanIn := term.length
      arityOk := trivial
      inputs := fun j => ⟨(term.get j).var.val, by
        have := (term.get j).var.isLt; omega⟩
      negated := fun j => !(term.get j).polarity }
  outputs _ :=
    { op := .or
      fanIn := φ.complexity
      arityOk := trivial
      inputs := fun j => ⟨N + j.val, by omega⟩
      negated := fun _ => false }
  acyclic i j :=
    Nat.lt_of_lt_of_le
      ((φ.terms.get ⟨i.val, i.isLt⟩).get ⟨j.val, j.isLt⟩).var.isLt
      (Nat.le_add_right N i.val)

private lemma wireValue_gate [NeZero N] (φ : DNF N) (x : BitString N) (i : Fin φ.complexity) :
    φ.toCircuit.wireValue x ⟨N + i.val, by omega⟩ =
      (φ.terms.get ⟨i.val, i.isLt⟩).all (fun l => l.eval x) := by
  have hge : ¬ ((⟨N + ↑i, (by omega)⟩ : Fin (N + φ.complexity)).val < N) := by simp
  rw [Circuit.wireValue_ge _ x _ hge]
  -- Normalize gate index
  have hgi : φ.toCircuit.gates ⟨(⟨N + ↑i, (by omega)⟩ : Fin (N + φ.complexity)).val - N,
    (by omega)⟩ = φ.toCircuit.gates i := by congr 1; ext; simp
  rw [hgi]
  -- Unfold gate definition
  simp only [toCircuit, Gate.eval, Basis.unboundedAON, AONOp.eval]
  -- Handle wireValue for primary inputs + xor-negation inside foldl
  conv_lhs => arg 2; ext acc j; arg 2
              rw [Circuit.wireValue_lt _ _ _
                ((φ.terms.get ⟨↑i, i.isLt⟩).get j).var.isLt, xor_neg_polarity_eq_eval]
  exact foldl_band_eq_list_all (φ.terms.get ⟨↑i, i.isLt⟩) (fun l => l.eval x)

/-- The circuit produced by `toCircuit` correctly computes the DNF formula. -/
theorem eval_toCircuit [NeZero N] (φ : DNF N) :
    (fun x => (φ.toCircuit.eval x) 0) = φ.eval := by
  funext x
  simp only [Circuit.eval, eval, toCircuit, Gate.eval, Basis.unboundedAON, Bool.false_xor,
    AONOp.eval]
  -- Convert struct-literal wireValue back to φ.toCircuit form for wireValue_gate
  change Fin.foldl φ.complexity
    (fun acc j => acc || φ.toCircuit.wireValue x ⟨N + j.val, by omega⟩) false =
    φ.terms.any (fun term => term.all fun l => l.eval x)
  conv_lhs => arg 2; ext acc j; arg 2; rw [wireValue_gate φ x j]
  exact foldl_bor_eq_list_any φ.terms (fun term => term.all fun l => l.eval x)

/-- The circuit size of `toCircuit` is `φ.complexity + 1`. -/
theorem size_toCircuit [NeZero N] (φ : DNF N) :
    φ.toCircuit.size = φ.complexity + 1 := rfl

end DNF

/-! ## CNF/DNF Lower Bound for Flip-Sensitive Functions -/

/-- A literal that doesn't mention variable `i` evaluates the same when `i` is flipped. -/
private lemma Literal.eval_update_ne {l : Literal N} {i : Fin N} (hne : l.var ≠ i)
    (x : BitString N) (b : Bool) :
    l.eval (Function.update x i b) = l.eval x := by
  simp only [Literal.eval]
  rw [Function.update_of_ne hne]

/-- If a term (conjunction of literals) doesn't mention variable `i`,
then flipping `i` doesn't change whether the term is satisfied. -/
private lemma term_eval_update {term : List (Literal N)} {i : Fin N}
    (hmiss : ∀ l ∈ term, l.var ≠ i) (x : BitString N) (b : Bool) :
    term.all (fun l => l.eval (Function.update x i b)) = term.all (fun l => l.eval x) := by
  induction term with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.all_cons]
    rw [Literal.eval_update_ne (hmiss hd List.mem_cons_self) x b]
    rw [ih (fun l hl => hmiss l (List.mem_cons_of_mem _ hl))]

/-- If `φ : DNF N` computes a flip-sensitive function, every satisfiable term
mentions all N variables. -/
theorem DNF.term_mentions_all (φ : DNF N)
    (f : BitString N → Bool)
    (hcomp : ∀ x, φ.eval x = f x)
    (hflip : ∀ x (i : Fin N), f (Function.update x i (!x i)) = !f x)
    (term : List (Literal N)) (hterm : term ∈ φ.terms)
    (x : BitString N) (hsat : term.all (fun l => l.eval x) = true) :
    ∀ i : Fin N, ∃ l ∈ term, l.var = i := by
  intro i
  by_contra hmiss
  push Not at hmiss
  -- hmiss : ∀ l ∈ term, l.var ≠ i
  -- Since term misses variable i, flipping i doesn't change the term
  have hsat' : term.all (fun l => l.eval (Function.update x i (!x i))) = true := by
    rw [term_eval_update hmiss]; exact hsat
  -- Both x and (flip x i) satisfy the term, so DNF is true on both
  have hx_true : φ.eval x = true := by
    simp only [DNF.eval, List.any_eq_true]
    exact ⟨term, hterm, hsat⟩
  have hx'_true : φ.eval (Function.update x i (!x i)) = true := by
    simp only [DNF.eval, List.any_eq_true]
    exact ⟨term, hterm, hsat'⟩
  -- But f flips, so f x ≠ f (flip x i)
  have := hflip x i
  rw [← hcomp, ← hcomp, hx_true, hx'_true] at this
  simp at this

/-- If a term mentions all N variables, it is satisfied by at most one assignment. -/
theorem full_term_unique {term : List (Literal N)}
    (hfull : ∀ i : Fin N, ∃ l ∈ term, l.var = i)
    {x y : BitString N}
    (hx : term.all (fun l => l.eval x) = true)
    (hy : term.all (fun l => l.eval y) = true) :
    x = y := by
  funext i
  obtain ⟨l, hl_mem, hl_var⟩ := hfull i
  rw [List.all_eq_true] at hx hy
  have hx_l := hx l hl_mem
  have hy_l := hy l hl_mem
  simp only [Literal.eval, hl_var] at hx_l hy_l
  split at hx_l <;> split at hy_l <;> simp_all

/-- If `f` is flip-sensitive with `N ≥ 1`, its true-set has exactly `2^{N-1}` elements. -/
theorem card_true_of_flip_sensitive {N : Nat} (hN : 1 ≤ N)
    (f : BitString N → Bool)
    (hflip : ∀ x (i : Fin N), f (Function.update x i (!x i)) = !f x) :
    (Finset.univ.filter (fun x => f x = true)).card = 2 ^ (N - 1) := by
  set S_true := Finset.univ.filter (fun x => f x = true)
  set S_false := Finset.univ.filter (fun x => f x = false)
  -- The involution: flip variable 0
  have hN' : 0 < N := by omega
  set flip0 : BitString N → BitString N := fun x => Function.update x ⟨0, hN'⟩ (!x ⟨0, hN'⟩)
  -- flip0 is self-inverse
  have flip0_inv : ∀ x, flip0 (flip0 x) = x := by
    intro x; ext j; simp only [flip0]
    by_cases h : j = ⟨0, hN'⟩
    · subst h; simp
    · simp [Function.update_of_ne h]
  -- flip0 maps true-set to false-set
  have flip0_tf : ∀ x, f x = true → f (flip0 x) = false := by
    intro x hx; have := hflip x ⟨0, hN'⟩; rw [hx] at this; simpa using this
  -- Bijection from S_true to S_false
  have hcard_eq : S_true.card = S_false.card := by
    apply Finset.card_bij (fun x _ => flip0 x)
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, S_true, S_false] at hx ⊢
      exact flip0_tf x hx
    · intro a₁ h₁ a₂ h₂ heq
      have := congr_arg flip0 heq
      rwa [flip0_inv, flip0_inv] at this
    · intro b hb
      refine ⟨flip0 b, ?_, flip0_inv b⟩
      simp only [S_true, S_false, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      -- f b = false, need f (flip0 b) = true
      have h1 := hflip b ⟨0, hN'⟩
      rwa [hb, Bool.not_false] at h1
  -- |S_true| + |S_false| = 2^N
  have hcard_total : S_true.card + S_false.card = 2 ^ N := by
    have h := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun x : BitString N => f x = true)
    simp only [Finset.card_univ] at h
    rw [show Fintype.card (BitString N) = 2 ^ N from by
      rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]] at h
    convert h using 2
    simp only [S_false]
    congr 1; ext x; cases f x <;> simp
  -- 2 * S_true.card = 2^N, so S_true.card = 2^{N-1}
  have : 2 ^ N = 2 * 2 ^ (N - 1) := by
    cases N with
    | zero => omega
    | succ n => simp [Nat.pow_succ, Nat.mul_comm]
  omega

/-- If `φ : DNF N` computes a flip-sensitive function with `N ≥ 1`,
then `2^{N-1} ≤ φ.complexity`. -/
theorem DNF.flip_complexity_lb (φ : DNF N) (hN : 1 ≤ N)
    (f : BitString N → Bool)
    (hcomp : ∀ x, φ.eval x = f x)
    (hflip : ∀ x (i : Fin N), f (Function.update x i (!x i)) = !f x) :
    2 ^ (N - 1) ≤ φ.complexity := by
  -- Every true assignment is covered by some term, and each full term covers ≤ 1 assignment
  suffices h : (Finset.univ.filter (fun x : BitString N => f x = true)).card ≤ φ.complexity by
    rwa [card_true_of_flip_sensitive hN f hflip] at h
  -- For each true x, find a term that x satisfies
  have hfind : ∀ x : BitString N, f x = true →
      ∃ term ∈ φ.terms, term.all (fun l => l.eval x) = true := by
    intro x hx
    have : φ.eval x = true := by rw [hcomp]; exact hx
    simpa [DNF.eval, List.any_eq_true] using this
  -- Each satisfiable term mentions all variables (so is satisfied by ≤ 1 assignment)
  have huniq : ∀ term ∈ φ.terms, ∀ x₁ x₂ : BitString N,
      term.all (fun l => l.eval x₁) = true →
      term.all (fun l => l.eval x₂) = true →
      x₁ = x₂ := by
    intro term hterm x₁ x₂ h₁ h₂
    have hfull := DNF.term_mentions_all φ f hcomp hflip term hterm x₁ h₁
    exact full_term_unique hfull h₁ h₂
  -- Count: |true-set| ≤ |terms| by injection via findIdx
  -- Reformulate as card ≤ card
  rw [show φ.complexity = (Finset.range φ.complexity).card from
    (Finset.card_range φ.complexity).symm]
  apply Finset.card_le_card_of_injOn
    (fun x => φ.terms.findIdx (fun t => t.all (fun l => l.eval x)))
  · -- MapsTo: findIdx lands in range
    intro x hx
    simp only [Finset.coe_filter, Finset.mem_univ, Set.mem_setOf, true_and] at hx
    simp only [Finset.coe_range, Set.mem_Iio, DNF.complexity]
    rw [List.findIdx_lt_length]
    exact hfind x hx
  · -- InjOn: two true assignments with same findIdx must be equal
    intro x₁ hx₁ x₂ hx₂ heq
    simp only [Finset.coe_filter, Finset.mem_univ, Set.mem_setOf, true_and] at hx₁ hx₂
    set k := φ.terms.findIdx (fun t => t.all (fun l => l.eval x₂))
    have hlt : k < φ.terms.length := by
      rw [List.findIdx_lt_length]; exact hfind x₂ hx₂
    have sat₂ : (φ.terms[k]'hlt).all (fun l => l.eval x₂) = true :=
      List.findIdx_getElem (w := hlt)
    have hlt₁ : φ.terms.findIdx (fun t => t.all (fun l => l.eval x₁)) < φ.terms.length := by
      rw [List.findIdx_lt_length]; exact hfind x₁ hx₁
    have sat₁ : (φ.terms[φ.terms.findIdx (fun t => t.all (fun l => l.eval x₁))]'hlt₁).all
        (fun l => l.eval x₁) = true :=
      List.findIdx_getElem (w := hlt₁)
    rw [show (φ.terms[φ.terms.findIdx (fun t => t.all (fun l => l.eval x₁))]'hlt₁) =
        (φ.terms[k]'hlt) from by congr 1] at sat₁
    exact huniq _ (List.getElem_mem ..) x₁ x₂ sat₁ sat₂

end CircuitComplexity
