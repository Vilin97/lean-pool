/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Mathlib.Analysis.Convex.DoublyStochasticMatrix
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
/-!
# Shannon.Entropy.Core

Foundational definitions for the Shannon characterization development:

- finite probability distributions (`ProbDist`);
- Shannon-style condition bundle (`ShannonEntropyAxioms`);
- basic constructions used in all later phases
  (`uniformPNat`, `composeProb`, `relabelProb`).

Global roadmap (matching Shannon Appendix 2):
1. Equiprobable case: `Apos H (n * m) = Apos H n + Apos H m`, then `Apos H n = K * log n`.
2. Rational case: grouped equiprobable refinement implies
   `H p = -K * ∑ p_i log p_i` for rational probabilities.
3. Real case: floor-count rational approximants `approxProb p N` converge to `p`;
   continuity upgrades the rational formula to all real probabilities.
-/
namespace LeanPool.Shannon1948Formalization

noncomputable section
open Filter
open scoped Topology

/-- `p` has nonnegative masses that sum to one. -/
def IsProbDist {α : Type} [Fintype α] (p : α → ℝ) : Prop :=
  (∀ a, 0 ≤ p a) ∧ (∑ a, p a) = 1

/--
A probability distribution over a finite type `α`, bundled with simplex proofs.
This keeps API signatures clean (no separate `IsProbDist` assumptions everywhere).
-/
abbrev ProbDist (α : Type) [Fintype α] := {p : α → ℝ // IsProbDist p}

instance {α : Type} [Fintype α] : CoeFun (ProbDist α) (fun _ => α → ℝ) where
  coe p := p.1

lemma prob_nonneg {α : Type} [Fintype α] (p : ProbDist α) (a : α) : 0 ≤ p a :=
  p.2.1 a

lemma prob_sum_eq_one {α : Type} [Fintype α] (p : ProbDist α) : (∑ a, p a) = 1 :=
  p.2.2

lemma prob_le_one {α : Type} [Fintype α] (p : ProbDist α) (a : α) : p a ≤ 1 :=
  (prob_sum_eq_one p) ▸ Finset.single_le_sum (fun b _ => prob_nonneg p b) (Finset.mem_univ a)

/-- Uniform distribution on `Fin (n + 1)`. -/
def uniformFin (n : ℕ) : ProbDist (Fin (n + 1)) :=
  ⟨fun _ => 1 / (n + 1 : ℝ), fun _ => by positivity,
    by simp [Finset.card_univ, show (n + 1 : ℝ) ≠ 0 by exact_mod_cast Nat.succ_ne_zero n]⟩

/--
Uniform distribution on `Fin n` for positive natural `n : ℕ+`.
This avoids `n + 1` index gymnastics when formalizing Appendix 2.
-/
def uniformPNat (n : ℕ+) : ProbDist (Fin n) :=
  ⟨fun _ => 1 / (n : ℝ), fun _ => by positivity,
    by simp [Finset.card_univ, show (n : ℝ) ≠ 0 by exact_mod_cast Nat.ne_of_gt n.2]⟩

/-- Composite distribution for a two-stage random choice. -/
def composeProb
    {α : Type} [Fintype α]
    {β : α → Type} [∀ a, Fintype (β a)]
    (p : ProbDist α)
    (q : (a : α) → ProbDist (β a)) :
    ProbDist (Sigma β) :=
  ⟨fun x => p x.1 * q x.1 x.2,
    fun x => mul_nonneg (prob_nonneg p x.1) (prob_nonneg (q x.1) x.2),
    by simp_rw [Fintype.sum_sigma, ← Finset.mul_sum, prob_sum_eq_one (q _), mul_one,
        prob_sum_eq_one p]⟩

/-- Equivalence between two-stage finite outcomes and `Fin (n * m)`. -/
def sigmaConstFinEquivFinMul (n m : ℕ+) :
    Sigma (fun _ : Fin n => Fin m) ≃ Fin (n * m : ℕ+) :=
  (Equiv.sigmaEquivProdOfEquiv (fun _ : Fin n => (Equiv.refl (Fin m)))).trans
    finProdFinEquiv

/--
Relabel a distribution along an equivalence of finite types.
This is the formal "event names do not matter" transport map.
-/
def relabelProb
    {α β : Type} [Fintype α] [Fintype β]
    (e : α ≃ β)
    (p : ProbDist α) :
    ProbDist β :=
  ⟨fun b => p (e.symm b), fun b => prob_nonneg p (e.symm b),
    by simpa using (e.symm.sum_comp (fun a => p a)).trans (prob_sum_eq_one p)⟩

/--
Shannon's three conditions for a finite-choice uncertainty functional `H`.
The final theorem will show any such `H` has entropy form up to a positive scale.
-/
structure ShannonEntropyAxioms
    (H : {α : Type} → [Fintype α] → ProbDist α → ℝ) : Prop where
  /-- Continuity in probabilities (for each finite alphabet). -/
  continuous :
    ∀ {α : Type} [Fintype α], Continuous fun p : ProbDist α => H p

  /-- On uniform distributions, uncertainty is monotone in alphabet size. -/
  uniformMonotone :
    StrictMono fun n : ℕ+ => H (uniformPNat n)

  /-- Invariance under relabeling outcomes by a finite equivalence. -/
  relabelInvariant :
    ∀ {α β : Type} [Fintype α] [Fintype β]
      (e : α ≃ β)
      (p : ProbDist α),
      H (relabelProb e p) = H p

  /-- Grouping (recursivity): a two-stage choice decomposes additively. -/
  grouping :
    ∀ {α : Type} [Fintype α]
      {β : α → Type} [∀ a, Fintype (β a)]
      (p : ProbDist α)
      (q : (a : α) → ProbDist (β a)),
      H (composeProb p q) = H p + ∑ a, p a * H (q a)

/--
`A_H(n)` is Shannon's notation for uncertainty on the uniform distribution
with `n + 1` equiprobable outcomes.
-/
def A
    (H : {α : Type} → [Fintype α] → ProbDist α → ℝ)
    (n : ℕ) : ℝ :=
  H (uniformFin n)

/--
`Apos H n` is uncertainty for exactly `n` equiprobable outcomes (`n : ℕ+`).
-/
def Apos
    (H : {α : Type} → [Fintype α] → ProbDist α → ℝ)
    (n : ℕ+) : ℝ :=
  H (uniformPNat n)


end

end LeanPool.Shannon1948Formalization
