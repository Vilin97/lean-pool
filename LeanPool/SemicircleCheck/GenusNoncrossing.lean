/-
Copyright (c) 2026 Wondermonger-daydreaming. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wondermonger-daydreaming
-/

import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Data.Fin.Basic
import LeanPool.SemicircleCheck.ShiftTwoEquiv
import LeanPool.SemicircleCheck.FinRotateLemmas
import LeanPool.SemicircleCheck.RotationArithmetic

/-!
  GENUS ZERO ↔ NONCROSSING

  The combinatorial heart of the Wigner semicircle law:
  a pairing of {0, ..., 2n-1} has genus zero if and only if
  it is noncrossing. Consequently, the number of genus-zero
  pairings equals the Catalan number Cₙ.

  Key design choices:
  - `Pairing n` as a subtype (no dependent proof parameters)
  - `Equiv.Perm.numCycles` counting ALL cycles including fixed points
  - `finRotate` for the long cycle (not `cycleOf`)
  - Recursive noncrossing predicate, with a separate bridge to arc crossings
  - Three-stage proof decomposition via cycle count bound
-/

open Equiv Equiv.Perm Fintype

/-! ## 1. Total Cycle Count

Mathlib's `cycleType.card` counts only nontrivial cycles (length ≥ 2).
The genus formula needs ALL cycles, including fixed points (1-cycles).
We define `numCycles` as the sum of nontrivial cycles and fixed points.

Using `cycleType.card` alone gives wrong genera.
For γπ = (1,3,5)(2)(4)(6), cycleType.card = 1 but numCycles = 4.
The genus formula requires 4, not 1.
-/

namespace Equiv.Perm

/-- Total number of cycles of a permutation, including fixed points. -/
def numCycles {α : Type*} [Fintype α] [DecidableEq α] (σ : _root_.Equiv.Perm α) : ℕ :=
  σ.cycleType.card + card (Function.fixedPoints σ)

end Equiv.Perm


/-! ## 2. The Long Cycle

The canonical cyclic permutation on Fin (2n), sending i ↦ i + 1 mod 2n.
Mathlib provides this as `finRotate`. Key properties we need:
- It is a single (2n)-cycle for n ≥ 1.
- `isCycle_finRotate` and `cycleType_finRotate` are available.
-/

/-- The long cycle γ on Fin (2n). -/
def longCycle (n : ℕ) : Perm (Fin (2 * n)) :=
  finRotate (2 * n)

/-- For n ≥ 1, the long cycle is a single cycle of length 2n. -/
theorem longCycle_isCycle {n : ℕ} (hn : 1 ≤ n) :
    (longCycle n).IsCycle := by
  unfold longCycle
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  change (finRotate (2 * m + 2)).IsCycle
  exact isCycle_finRotate

/-! ## 3. Pairings as a Subtype

A pairing is a fixed-point-free involution. Making it a subtype
avoids carrying proof terms through every definition and theorem.
-/

/-- A permutation is a pairing if it is an involution with no fixed points. -/
def IsPairing {n : ℕ} (π : Perm (Fin (2 * n))) : Prop :=
  π ^ 2 = 1 ∧ ∀ x, π x ≠ x

/-- The type of pairings of Fin (2n). -/
def Pairing (n : ℕ) :=
  { π : Perm (Fin (2 * n)) // IsPairing π }

instance (n : ℕ) : CoeOut (Pairing n) (Perm (Fin (2 * n))) :=
  ⟨Subtype.val⟩

/-! ## 4. Genus

Genus is defined as a plain function on pairings.
For a pairing π, the composition γπ is a permutation of Fin(2n),
and its total cycle count determines the genus via:

  genus(π) = (n + 1 - numCycles(γ * π)) / 2

We prove separately that for pairings:
(a) numCycles(γ * π) ≤ n + 1, so the numerator is nonneg
(b) the numerator is always even, so division is exact
-/

/-- The genus of a pairing. -/
def Pairing.genus {n : ℕ} (p : Pairing n) : ℕ :=
  ((n + 1) - numCycles (longCycle n * p.val)) / 2

private lemma multiset_sum_ge_two_card' {s : Multiset ℕ} (h : ∀ c ∈ s, 2 ≤ c) :
    s.sum ≥ 2 * s.card := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a t ih =>
    simp only [Multiset.sum_cons, Multiset.card_cons]
    have ha := h a (Multiset.mem_cons_self a t)
    have ht := ih (fun c hc => h c (Multiset.mem_cons_of_mem hc))
    omega

/-! ### Transposition bound infrastructure

The key structural fact: multiplying a permutation by a single transposition
changes numCycles by at most 1. This is the fundamental property of the
Cayley distance on the symmetric group.

We prove this via cycle_induction_on, analyzing how swap(a,b) interacts with
the cycle decomposition of σ. The three cases are:
(1) σ = 1 (trivial)
(2) σ is a single cycle (swap splits or shortens)
(3) σ = c * d with c, d disjoint (reduce to sub-cases)
-/

/-- numCycles is bounded by the cardinality of the type. -/
private lemma numCycles_le_card {α : Type*} [Fintype α] [DecidableEq α] (σ : Perm α) :
    numCycles σ ≤ Fintype.card α := by
  unfold Equiv.Perm.numCycles
  rw [Equiv.Perm.card_fixedPoints, Equiv.Perm.sum_cycleType]
  have h_ge := @multiset_sum_ge_two_card' σ.cycleType
    (fun c hc => Equiv.Perm.two_le_of_mem_cycleType hc)
  rw [Equiv.Perm.sum_cycleType] at h_ge
  have h_supp : σ.support.card ≤ Fintype.card α :=
    (Finset.card_le_card (Finset.subset_univ _)).trans (by simp)
  omega

/-- Conjugation preserves numCycles: numCycles(τστ⁻¹) = numCycles(σ). -/
private theorem numCycles_conj {α : Type*} [Fintype α] [DecidableEq α]
    (σ τ : Perm α) : numCycles (τ * σ * τ⁻¹) = numCycles σ := by
  unfold Equiv.Perm.numCycles
  have hct : (τ * σ * τ⁻¹).cycleType = σ.cycleType := Equiv.Perm.cycleType_conj
  rw [hct]
  congr 1
  rw [Equiv.Perm.card_fixedPoints, Equiv.Perm.card_fixedPoints, hct]

/-- If numCycles σ = card α, then σ = 1 (defect zero implies identity). -/
private lemma numCycles_eq_card_imp_one {α : Type*} [Fintype α] [DecidableEq α] (σ : Perm α)
    (h : numCycles σ = Fintype.card α) : σ = 1 := by
  unfold Equiv.Perm.numCycles at h
  rw [Equiv.Perm.card_fixedPoints, Equiv.Perm.sum_cycleType] at h
  have h_ge := @multiset_sum_ge_two_card' σ.cycleType
    (fun c hc => Equiv.Perm.two_le_of_mem_cycleType hc)
  rw [Equiv.Perm.sum_cycleType] at h_ge
  have h_supp : σ.support.card ≤ Fintype.card α :=
    (Finset.card_le_card (Finset.subset_univ _)).trans (by simp)
  exact Equiv.Perm.support_eq_empty_iff.mp (Finset.card_eq_zero.mp (by omega))

/-- Swap identity: for distinct a, b, c, swap(a,c) * swap(a,b) = swap(c,b) * swap(a,c).
    This is the key conjugation identity for three-element transpositions. -/
private lemma swap_mul_swap_comm {α : Type*} [DecidableEq α] {a b c : α}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Equiv.swap a c * Equiv.swap a b = Equiv.swap c b * Equiv.swap a c := by
  ext x
  simp only [Perm.coe_mul, Function.comp_apply]
  by_cases hxa : x = a <;> by_cases hxb : x = b <;> by_cases hxc : x = c
  all_goals
    subst_vars
    simp_all [swap_apply_left, swap_apply_right, swap_apply_of_ne_of_ne, Ne.symm]

/-- Multiplying by swap(a, σ(a)) on the left always increases numCycles by 1
    when a is not a fixed point. This is the fundamental transposition-cycle lemma:
    swap(a, b) * σ makes a into a fixed point of the product (since
    (swap(a,b)*σ)(a) = swap(a,b)(b) = a), effectively "splitting off" element a
    from its cycle. In the case σ(σ(a)) = a (2-cycle), the 2-cycle becomes two
    fixed points (+1 net). In the case σ(σ(a)) ≠ a, the cycle containing a
    splits into a fixed point {a} and a shorter cycle (+1 net). -/
private theorem numCycles_swap_mul_of_apply {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Perm α) (a : α) (ha : σ a ≠ a) :
    numCycles (swap a (σ a) * σ) = numCycles σ + 1 := by
  -- Unfold numCycles and rewrite fixedPoints via support
  unfold Equiv.Perm.numCycles
  rw [Equiv.Perm.card_fixedPoints, Equiv.Perm.card_fixedPoints,
      Equiv.Perm.sum_cycleType, Equiv.Perm.sum_cycleType]
  set τ := swap a (σ a) * σ
  have ha_supp : a ∈ σ.support := Equiv.Perm.mem_support.mpr ha
  have hσ_le : σ.support.card ≤ Fintype.card α :=
    (Finset.card_le_card (Finset.subset_univ _)).trans (by simp)
  have hτ_le : τ.support.card ≤ Fintype.card α :=
    (Finset.card_le_card (Finset.subset_univ _)).trans (by simp)
  -- The cycleOf a in σ
  set c := σ.cycleOf a
  have hc_mem : c ∈ σ.cycleFactorsFinset :=
    Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr ha_supp
  have hc_cycle : c.IsCycle := σ.isCycle_cycleOf ha
  have hca : c a = σ a := Equiv.Perm.cycleOf_apply_self σ a
  have ha_ne_sa : a ≠ σ a := Ne.symm ha
  -- Useful: a ∈ c.support, c a ∈ c.support
  have ha_c_supp : a ∈ c.support := by
    rw [Equiv.Perm.mem_support, hca]; exact ha
  have hca_c_supp : c a ∈ c.support := Equiv.Perm.apply_mem_support.mpr ha_c_supp
  -- Case split on σ(σ(a)) = a
  by_cases hffa : σ (σ a) = a
  · -- CASE 1: a is in a 2-cycle
    have hcca_eq : c (c a) = a := by rw [hca, Equiv.Perm.cycleOf_apply_apply_self]; exact hffa
    have hcycle_eq : c = swap a (σ a) := by
      have := hc_cycle.eq_swap_of_apply_apply_eq_self (by rwa [hca]) hcca_eq
      rwa [hca] at this
    have hτ_eq : τ = σ * c⁻¹ := by
      have hc_sq : c * c = 1 := by rw [hcycle_eq]; simp
      have hd : Equiv.Perm.Disjoint c (σ * c⁻¹) :=
        (Equiv.Perm.disjoint_mul_inv_of_mem_cycleFactorsFinset hc_mem).symm
      change swap a (σ a) * σ = σ * c⁻¹
      calc swap a (σ a) * σ = c * σ := by rw [hcycle_eq]
        _ = c * (σ * c⁻¹ * c) := by group
        _ = c * (σ * c⁻¹) * c := by group
        _ = (σ * c⁻¹) * c * c := by rw [hd.commute.eq]
        _ = σ * c⁻¹ := by rw [mul_assoc, hc_sq, mul_one]
    have hτ_ct : τ.cycleType = σ.cycleType - c.cycleType := by
      rw [hτ_eq]; exact Equiv.Perm.cycleType_mul_inv_mem_cycleFactorsFinset_eq_sub hc_mem
    have hc_ct : c.cycleType = {2} := by
      rw [hcycle_eq]
      have : (swap a (σ a)).IsCycle := by rw [swap_comm]; exact isCycle_swap ha
      rw [this.cycleType]
      congr 1
      rw [swap_comm]; exact card_support_swap ha
    have h2_mem : 2 ∈ σ.cycleType :=
      Multiset.mem_of_le (hc_ct ▸ Equiv.Perm.cycleType_le_of_mem_cycleFactorsFinset hc_mem)
        (Multiset.mem_singleton_self 2)
    rw [hτ_ct, hc_ct, Multiset.sub_singleton, Multiset.card_erase_of_mem h2_mem]
    have hsa_supp : σ a ∈ σ.support := by
      rw [Equiv.Perm.mem_support]; intro h; rw [h] at hffa; exact ha hffa
    have hτ_support : τ.support = σ.support \ {a, σ a} := by
      ext x; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton,
                         Equiv.Perm.mem_support]
      constructor
      · intro hx
        have ⟨hxs, hxne⟩ := Equiv.Perm.mem_support_swap_mul_imp_mem_support_ne
          (Equiv.Perm.mem_support.mpr hx)
        exact ⟨Equiv.Perm.mem_support.mp hxs,
               fun h => h.elim (fun hxa => hxne hxa)
                               (fun hxsa => hx (show τ x = x from by
                                 subst hxsa
                                 simp [τ, mul_apply, hffa]))⟩
      · intro ⟨hx_supp, hx_ne⟩
        push Not at hx_ne
        change (swap a (σ a) * σ) x ≠ x
        simp only [mul_apply]
        have hσx_ne_σa : σ x ≠ σ a := fun h => hx_ne.1 (σ.injective h)
        by_cases hσx_a : σ x = a
        · rw [hσx_a, swap_apply_left]; exact Ne.symm hx_ne.2
        · rw [swap_apply_of_ne_of_ne hσx_a hσx_ne_σa]; exact hx_supp
    rw [hτ_support]
    have hpair_sub : {a, σ a} ⊆ σ.support := by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> [exact ha_supp; exact hsa_supp]
    rw [Finset.card_sdiff_of_subset hpair_sub, Finset.card_pair ha_ne_sa]
    have h1_ct : 1 ≤ σ.cycleType.card :=
      Nat.one_le_iff_ne_zero.mpr (Equiv.Perm.card_cycleType_eq_zero.not.mpr (by
        intro h; rw [h] at ha; simp at ha))
    have h2_supp : 2 ≤ σ.support.card := by
      calc 2 = ({a, σ a} : Finset α).card := (Finset.card_pair ha_ne_sa).symm
        _ ≤ σ.support.card := Finset.card_le_card hpair_sub
    have hpred : σ.cycleType.card.pred = σ.cycleType.card - 1 := rfl
    omega
  · -- CASE 2: a is in a cycle of length ≥ 3
    have hτ_support : τ.support = σ.support \ {a} :=
      Equiv.Perm.support_swap_mul_eq σ a hffa
    rw [hτ_support, Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem ha_supp]
    set rest := σ * c⁻¹
    have hrest_disjoint_c : Equiv.Perm.Disjoint c rest :=
      (Equiv.Perm.disjoint_mul_inv_of_mem_cycleFactorsFinset hc_mem).symm
    have hσ_eq : σ = rest * c := by change σ = σ * c⁻¹ * c; group
    have hcca : c (c a) ≠ a := by
      rw [hca, Equiv.Perm.cycleOf_apply_apply_self]; exact hffa
    set c' := swap a (c a) * c
    have hc'_cycle : c'.IsCycle := hc_cycle.swap_mul (by rwa [hca]) hcca
    have hc'_support : c'.support = c.support \ {a} :=
      Equiv.Perm.support_swap_mul_eq c a (by rwa [hca, Equiv.Perm.cycleOf_apply_apply_self])
    have hswap_supp : (swap a (c a)).support ≤ c.support := by
      intro x hx
      rw [Equiv.Perm.mem_support] at hx
      by_cases hxa : x = a
      · exact hxa ▸ ha_c_supp
      · by_cases hxca : x = c a
        · exact hxca ▸ hca_c_supp
        · exact absurd (swap_apply_of_ne_of_ne hxa hxca) hx
    have hswap_rest_disjoint : Equiv.Perm.Disjoint (swap a (c a)) rest :=
      hrest_disjoint_c.mono hswap_supp (le_refl _)
    have hτ_eq : τ = rest * c' := by
      change swap a (σ a) * σ = rest * c'
      conv_lhs => rw [show σ a = c a from hca.symm]
      rw [hσ_eq, ← mul_assoc, hswap_rest_disjoint.commute.eq, mul_assoc]
    have hrest_c'_disjoint : Equiv.Perm.Disjoint rest c' := by
      rw [Equiv.Perm.disjoint_iff_disjoint_support, hc'_support]
      exact Finset.disjoint_of_subset_right Finset.sdiff_subset
        hrest_disjoint_c.symm.disjoint_support
    have hτ_ct : τ.cycleType = rest.cycleType + c'.cycleType := by
      rw [hτ_eq]; exact hrest_c'_disjoint.cycleType_mul
    have hσ_ct : σ.cycleType = rest.cycleType + c.cycleType := by
      rw [hσ_eq]; exact hrest_disjoint_c.symm.cycleType_mul
    rw [hτ_ct, hσ_ct, Multiset.card_add, Multiset.card_add,
        Equiv.Perm.card_cycleType_eq_one.mpr hc'_cycle,
        Equiv.Perm.card_cycleType_eq_one.mpr hc_cycle]
    have h1 : 1 ≤ σ.support.card := Finset.one_le_card.mpr ⟨a, ha_supp⟩
    omega

/-- Multiplying by a transposition changes numCycles by at most 1.
    Proof by well-founded induction on defect(σ) = card α - numCycles σ.
    Three cases on σ(a):
    (1) σ(a) = b: direct from numCycles_swap_mul_of_apply
    (2) σ(a) = a: swap creates a non-fixed point, apply inverse argument
    (3) σ(a) ∉ {a,b}: reduce via swap identity to smaller defect -/
private lemma numCycles_swap_mul_le_aux {α : Type*} [Fintype α] [DecidableEq α]
    (k : ℕ) (a b : α) (σ : Perm α) (hk : Fintype.card α - numCycles σ ≤ k) :
    numCycles (swap a b * σ) ≤ numCycles σ + 1 := by
  induction k generalizing a b σ with
  | zero => exact (numCycles_le_card _).trans (by omega)
  | succ k ih =>
    by_cases hab : a = b
    · subst hab; rw [show swap a a = (1 : Perm α) from Equiv.swap_self a, one_mul]; omega
    · by_cases hσa_b : σ a = b
      · -- Case 1: σ(a) = b, so swap(a,b) = swap(a, σ(a))
        rw [← hσa_b]
        exact le_of_eq (numCycles_swap_mul_of_apply σ a
          (by intro h; rw [hσa_b] at h; exact hab h.symm))
      · by_cases hσa_a : σ a = a
        · -- Case 2: a is a fixed point. (swap a b * σ)(a) = b.
          -- Apply numCycles_swap_mul_of_apply to swap a b * σ at a:
          -- numCycles(swap(a,b) * swap(a,b) * σ) = numCycles(swap a b * σ) + 1
          -- i.e., numCycles σ = numCycles(swap a b * σ) + 1
          have h_app : (swap a b * σ) a = b := by simp [mul_apply, hσa_a, swap_apply_left]
          have h_ne : (swap a b * σ) a ≠ a := by rw [h_app]; exact Ne.symm hab
          have h1 := numCycles_swap_mul_of_apply (swap a b * σ) a h_ne
          conv at h1 => lhs; rw [h_app]
          rw [← mul_assoc, swap_mul_self, one_mul] at h1
          omega
        · -- Case 3: σ(a) ≠ a and σ(a) ≠ b.
          -- (swap a b * σ)(a) = σ(a), apply numCycles_swap_mul_of_apply to get:
          -- numCycles(swap(a, σ a) * swap(a,b) * σ) = numCycles(swap a b * σ) + 1
          -- Use swap identity: swap(a, σ a) * swap(a,b) = swap(σ a, b) * swap(a, σ a)
          -- So LHS = numCycles(swap(σ a, b) * (swap(a, σ a) * σ))
          -- IH on ρ = swap(a, σ a) * σ (which has defect one less):
          -- numCycles(swap(σ a, b) * ρ) ≤ numCycles(ρ) + 1 = numCycles(σ) + 2
          -- Therefore numCycles(swap a b * σ) + 1 ≤ numCycles(σ) + 2
          have h_app : (swap a b * σ) a = σ a := by
            simp [mul_apply, swap_apply_of_ne_of_ne hσa_a hσa_b]
          have h_ne : (swap a b * σ) a ≠ a := by rw [h_app]; exact hσa_a
          have h1 := numCycles_swap_mul_of_apply (swap a b * σ) a h_ne
          conv at h1 => lhs; rw [h_app]
          rw [← mul_assoc, swap_mul_swap_comm hab (Ne.symm hσa_a) (Ne.symm hσa_b),
              mul_assoc] at h1
          have h2 := numCycles_swap_mul_of_apply σ a hσa_a
          have hρ_defect : Fintype.card α - numCycles (swap a (σ a) * σ) ≤ k := by
            rw [h2]; have := numCycles_le_card σ; omega
          have h3 := ih (σ a) b (swap a (σ a) * σ) hρ_defect
          omega

/-- Multiplying by a transposition changes numCycles by at most 1.
This is the fundamental lemma for the Cayley distance theory. -/
private lemma numCycles_swap_mul_le {α : Type*} [Fintype α] [DecidableEq α]
    (a b : α) (σ : Perm α) :
    numCycles (swap a b * σ) ≤ numCycles σ + 1 :=
  numCycles_swap_mul_le_aux (Fintype.card α) a b σ (by omega)

/-- numCycles of right multiplication by swap, via conjugation invariance. -/
private lemma numCycles_mul_swap_le {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Perm α) (a b : α) :
    numCycles (σ * swap a b) ≤ numCycles σ + 1 := by
  have key : numCycles (σ * swap a b) = numCycles (swap a b * σ) := by
    have h := numCycles_conj (σ * swap a b) (swap a b)
    simp only [mul_assoc, swap_mul_self, mul_one, swap_inv] at h
    exact h.symm
  rw [key]; exact numCycles_swap_mul_le a b σ

/-- Composing with a list of swaps: numCycles grows by at most the list length. -/
private lemma numCycles_mul_swaps_le {m : ℕ} (σ : Perm (Fin m))
    (l : List (Perm (Fin m))) (hl : ∀ g ∈ l, Equiv.Perm.IsSwap g) :
    numCycles (σ * l.prod) ≤ numCycles σ + l.length := by
  induction l generalizing σ with
  | nil => simp
  | cons t l ih =>
    rw [List.prod_cons, ← mul_assoc]
    obtain ⟨a, b, _, rfl⟩ := hl t (by simp)
    have h1 := ih (σ * swap a b) (fun g hg => hl g (by simp [hg]))
    have h2 := numCycles_mul_swap_le σ a b
    simp [List.length_cons]; omega

/-- numCycles of the long cycle equals 1 for n ≥ 1. -/
private lemma numCycles_longCycle {n : ℕ} (hn : 1 ≤ n) :
    numCycles (longCycle n) = 1 := by
  unfold Equiv.Perm.numCycles longCycle
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hcyc : (finRotate (2 * (k + 1))).IsCycle := by
    change (finRotate (2 * k + 2)).IsCycle; exact isCycle_finRotate
  rw [hcyc.cycleType, Multiset.card_singleton,
      Equiv.Perm.card_fixedPoints, hcyc.cycleType, Multiset.sum_singleton]
  have hsup : (finRotate (2 * (k + 1))).support = Finset.univ := by
    change (finRotate (2 * k + 2)).support = Finset.univ; exact support_finRotate
  rw [hsup, Finset.card_univ]; omega

private lemma support_eq_univ_of_fpf {α : Type*} [Fintype α] [DecidableEq α]
    (π : Perm α) (hfpf : ∀ x, π x ≠ x) : π.support = Finset.univ := by
  ext x; simp [Equiv.Perm.mem_support, hfpf]

private lemma multiset_sum_const {s : Multiset ℕ} {k : ℕ}
    (h : ∀ c ∈ s, c = k) : s.sum = k * s.card := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.sum_cons, Multiset.card_cons]
    rw [h a (Multiset.mem_cons_self a s), ih fun c hc => h c (Multiset.mem_cons_of_mem hc)]
    ring

private lemma pairing_cycleType_all_two {n : ℕ} (p : Pairing n) :
    ∀ c ∈ p.val.cycleType, c = 2 := by
  intro c hc
  have hge := Equiv.Perm.two_le_of_mem_cycleType hc
  have hord : orderOf p.val ∣ 2 := orderOf_dvd_of_pow_eq_one p.property.1
  have := Nat.le_of_dvd (by omega) (dvd_trans (dvd_of_mem_cycleType hc) hord)
  omega

private lemma pairing_cycleType_card {n : ℕ} (p : Pairing n) :
    p.val.cycleType.card = n := by
  have hsum := Equiv.Perm.sum_cycleType p.val
  rw [support_eq_univ_of_fpf p.val p.property.2, Finset.card_univ, card_fin] at hsum
  rw [multiset_sum_const (pairing_cycleType_all_two p)] at hsum; omega

/-- A pairing on Fin(2n) can be written as a product of n swaps.
Each cycle in the pairing is a 2-cycle (swap), and there are exactly n of them. -/
private lemma pairing_swap_factorization {n : ℕ} (p : Pairing n) :
    ∃ l : List (Perm (Fin (2 * n))), l.prod = p.val ∧ l.length = n ∧
    ∀ g ∈ l, Equiv.Perm.IsSwap g := by
  -- The cycleFactorsFinset of p.val consists of n swaps
  -- We convert to a list
  have hcard := pairing_cycleType_card p
  have hall := pairing_cycleType_all_two p
  -- Each cycle factor is a swap (support.card = 2)
  have hswap : ∀ c ∈ p.val.cycleFactorsFinset, Equiv.Perm.IsSwap c := by
    intro c hc
    rw [← Equiv.Perm.card_support_eq_two]
    have hc_mem := Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc
    -- c.support.card is in p.val.cycleType
    have : c.support.card ∈ p.val.cycleType := by
      simp only [Equiv.Perm.cycleType_def, Multiset.mem_map]
      exact ⟨c, hc, rfl⟩
    exact (hall _ this).symm ▸ rfl
  -- Convert finset to list
  obtain ⟨l, hl_nodup, hl_eq⟩ := p.val.cycleFactorsFinset.exists_list_nodup_eq
  refine ⟨l, ?_, ?_, ?_⟩
  · -- l.prod = p.val
    -- The cycle factors pairwise commute (they're disjoint)
    have hpw : (l.toFinset : Set (Perm (Fin (2 * n)))).Pairwise (Function.onFun Commute id) := by
      rw [hl_eq]
      intro x hx y hy hne
      exact (Equiv.Perm.cycleFactorsFinset_pairwise_disjoint p.val hx hy hne).commute
    -- Use Finset.noncommProd_toFinset and cycleFactorsFinset_noncommProd
    have key : ∀ (s : Finset (Perm (Fin (2 * n)))) (hs : s = l.toFinset)
        (comm : Set.Pairwise (↑s) (Function.onFun Commute (id : Perm (Fin (2 * n)) → _))),
        s.noncommProd id comm = l.prod := by
      intro s hs comm
      subst hs
      exact (Finset.noncommProd_toFinset l id comm hl_nodup).trans (by simp)
    exact (key _ hl_eq.symm _).symm.trans (Equiv.Perm.cycleFactorsFinset_noncommProd _)
  · -- l.length = n
    have hlen : l.length = p.val.cycleFactorsFinset.card := by
      rw [← hl_eq]; exact (List.toFinset_card_of_nodup hl_nodup).symm
    rw [hlen]
    -- cycleFactorsFinset.card = cycleType.card = n
    rw [show p.val.cycleFactorsFinset.card = p.val.cycleType.card from by
      simp [Equiv.Perm.cycleType_def]]
    exact hcard
  · -- all elements are swaps
    intro g hg
    exact hswap g (by rw [← hl_eq]; exact List.mem_toFinset.mpr hg)

/-- For any pairing, numCycles(γπ) ≤ n + 1. -/
theorem Pairing.numCycles_le {n : ℕ} (p : Pairing n) :
    numCycles (longCycle n * p.val) ≤ n + 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- n = 0: Fin 0 is empty
    have : longCycle 0 * p.val = 1 := by ext x; exact Fin.elim0 x
    rw [this]; unfold Equiv.Perm.numCycles
    simp [Equiv.Perm.cycleType_one]
  · -- n ≥ 1
    obtain ⟨l, hl_prod, hl_len, hl_swap⟩ := pairing_swap_factorization p
    rw [← hl_prod]
    calc numCycles (longCycle n * l.prod)
        ≤ numCycles (longCycle n) + l.length := numCycles_mul_swaps_le _ l hl_swap
      _ = 1 + n := by rw [numCycles_longCycle hn, hl_len]
      _ = n + 1 := by omega

/-! ### Sign-based parity infrastructure

The parity of numCycles(γπ) matches the parity of n + 1. This follows from
the sign equation sign(γπ) = sign(γ) * sign(π) = (-1)^(n+1), combined
with sign(σ) = (-1)^(σ.support.card + σ.cycleType.card). -/

private lemma neg_one_pow_parity {a b : ℕ}
    (h : (-1 : ℤˣ) ^ a = (-1 : ℤˣ) ^ b) : a % 2 = b % 2 := by
  rw [neg_one_pow_eq_ite (n := a), neg_one_pow_eq_ite (n := b)] at h
  split_ifs at h with h1 h2 h2
  · rw [Nat.even_iff] at h1 h2; omega
  · exfalso; simp at h
  · exfalso; simp at h
  · rw [Nat.not_even_iff_odd, Nat.odd_iff] at h1 h2; omega

private lemma sign_longCycle (n : ℕ) (hn : 1 ≤ n) :
    Equiv.Perm.sign (longCycle n) = -1 := by
  unfold longCycle
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have h2k : 2 * (k + 1) = 2 * k + 2 := by ring
  conv_lhs => rw [h2k]
  rw [(@isCycle_finRotate (2 * k)).sign, support_finRotate, Finset.card_univ, card_fin]
  simp [pow_add, pow_mul]

private lemma sign_pairing {n : ℕ} (p : Pairing n) :
    Equiv.Perm.sign p.val = (-1) ^ n := by
  rw [Equiv.Perm.sign_of_cycleType, Equiv.Perm.sum_cycleType,
      support_eq_univ_of_fpf p.val p.property.2, Finset.card_univ, card_fin,
      pairing_cycleType_card p]
  simp [pow_add, pow_mul]

private theorem numCycles_parity_even {n : ℕ} (p : Pairing n) (hn : 1 ≤ n) :
    2 ∣ ((n + 1) - numCycles (longCycle n * p.val)) := by
  suffices h : ((n + 1) - numCycles (longCycle n * p.val)) % 2 = 0 from
    Nat.dvd_of_mod_eq_zero h
  set σ := longCycle n * p.val with hσ_def
  have hsign : Equiv.Perm.sign σ = (-1) ^ (n + 1) := by
    rw [hσ_def, Equiv.Perm.sign_mul, sign_longCycle n hn, sign_pairing p, ← pow_succ']
  have hct := Equiv.Perm.sign_of_cycleType σ
  rw [hsign] at hct
  have hmod := neg_one_pow_parity hct.symm
  rw [Equiv.Perm.sum_cycleType] at hmod
  have hnc_eq : numCycles σ = σ.cycleType.card + (2 * n - σ.support.card) := by
    unfold Equiv.Perm.numCycles
    rw [Equiv.Perm.card_fixedPoints, card_fin, Equiv.Perm.sum_cycleType]
  have hsupp_le : σ.support.card ≤ 2 * n :=
    calc σ.support.card ≤ Finset.univ.card := Finset.card_le_card (Finset.subset_univ _)
      _ = 2 * n := by simp [card_fin]
  have hle := p.numCycles_le
  omega

/-- For any pairing with n ≥ 1, (n + 1 - numCycles(γπ)) is even.
    False for n = 0: numCycles on Fin 0 is 0, but 2 * 0 ≠ 1. -/
theorem Pairing.genus_exact {n : ℕ} (p : Pairing n) (hn : 1 ≤ n) :
    2 * p.genus = (n + 1) - numCycles (longCycle n * p.val) := by
  unfold Pairing.genus
  exact Nat.mul_div_cancel' (numCycles_parity_even p hn)

/-! ## 5. Noncrossing Predicate (Recursive)

A noncrossing pairing is defined recursively:
- The empty pairing (n = 0) is noncrossing.
- A pairing on 2n points is noncrossing if there exists an
  adjacent pair (i, i+1 mod 2n) in the pairing whose removal
  yields a noncrossing pairing on 2(n-1) points.

"Adjacent" means: π(i) = finRotate(i), i.e., π sends some
element to its cyclic successor.

This definition is better for Lean than the "no crossing arcs"
formulation because:
1. It is structurally recursive (induction is immediate).
2. It aligns with Catalan recursion.
3. It avoids the cyclic-order normalization headaches.
-/

/-- An adjacent pair in a pairing: a point i such that π(i) = i + 1 mod 2n. -/
def Pairing.hasAdjacentAt {n : ℕ} (p : Pairing n) (i : Fin (2 * n)) : Prop :=
  p.val i = finRotate (2 * n) i

/-- Deletion of an adjacent pair: given a pairing with π(i) = i+1,
    remove the pair {i, i+1} and reindex to get a pairing on 2(n-1) points.

    This requires careful construction. The idea:
    1. Let j = finRotate(i) = i + 1 mod 2n.
    2. Define the restriction of π to Fin(2n) \ {i, j}.
    3. Identify Fin(2n) \ {i, j} with Fin(2(n-1)) via an order-preserving map.
    4. Show the resulting permutation is again a pairing.

    This is the most technically demanding definition in the file.
    It requires building the injection Fin(2n-2) ↪ Fin(2n) that
    skips i and j, and proving the conjugated permutation is
    a fixed-point-free involution. -/
noncomputable def Pairing.deleteAdjacent {n : ℕ} (p : Pairing (n + 1))
    (i : Fin (2 * (n + 1))) (h : p.hasAdjacentAt i) :
    Pairing n :=
  -- Rotate so the adjacent pair sits at coordinates (0, 1)
  let ρ : Perm (Fin (2 * (n + 1))) := (finRotate _) ^ (2 * (n + 1) - i.val)
  let p' : Perm (Fin (2 * (n + 1))) := ρ * p.val * ρ⁻¹
  -- After rotation: p'(0) = 1 and p'(1) = 0
  -- The two rotation facts: ρ sends i↦0 and (i+1)↦1
  have hρ0 : ρ i = ⟨0, by omega⟩ :=
    rotate_self_eq_zero (2 * (n + 1)) (by omega) i
  have hρ1 : ρ (finRotate _ i) = ⟨1, by omega⟩ :=
    rotate_succ_eq_one (2 * (n + 1)) i (by omega)
  -- h₀': conjugation sends 0↦1 via group theory
  have h₀' : p' ⟨0, by omega⟩ = ⟨1, by omega⟩ :=
    conjugate_sends hρ0 hρ1 h
  -- h₁': conjugation sends 1↦0 via involution
  have h₁' : p' ⟨1, by omega⟩ = ⟨0, by omega⟩ :=
    conjugate_sends_back hρ0 hρ1 p.property.1 h
  -- Contract the normalized boundary pair, then package as a pairing.
  ⟨SemicircleCore.contractZeroOne p' h₀' h₁',
    -- contractZeroOne_isPairing + conjugation preserves pairing
    by
      have hππ : p.val * p.val = 1 := by
        have := p.property.1; rwa [sq] at this
      have hinv : p' ^ 2 = 1 := by
        have : p' * p' = 1 := by
          change (ρ * p.val * ρ⁻¹) * (ρ * p.val * ρ⁻¹) = 1
          calc ρ * p.val * ρ⁻¹ * (ρ * p.val * ρ⁻¹)
              = ρ * p.val * (ρ⁻¹ * ρ) * p.val * ρ⁻¹ := by group
            _ = ρ * p.val * 1 * p.val * ρ⁻¹ := by rw [inv_mul_cancel]
            _ = ρ * (p.val * p.val) * ρ⁻¹ := by group
            _ = ρ * 1 * ρ⁻¹ := by rw [hππ]
            _ = 1 := by group
        rwa [sq]
      have hfpf : ∀ x, p' x ≠ x := by
        intro x hfix
        have hfix' : (ρ * p.val * ρ⁻¹) x = x := hfix
        simp only [mul_apply] at hfix'
        -- hfix' : ρ (p.val (ρ⁻¹ x)) = x
        -- Apply ρ⁻¹ to both sides: p.val (ρ⁻¹ x) = ρ⁻¹ x
        have : p.val (ρ⁻¹ x) = ρ⁻¹ x := by
          have := congr_arg ρ.symm hfix'
          simpa [Equiv.symm_apply_apply] using this
        exact p.property.2 (ρ⁻¹ x) this
      exact SemicircleCore.contractZeroOne_isPairing h₀' h₁' hinv hfpf⟩

/-- Recursive noncrossing predicate. -/
def Pairing.IsNoncrossing : {n : ℕ} → Pairing n → Prop
  | 0, _ => True
  | n + 1, p => ∃ i : Fin (2 * (n + 1)),
      ∃ h : p.hasAdjacentAt i, (p.deleteAdjacent i h).IsNoncrossing

/-! ## 6. The Bridge Theorem (Three Stages)

We prove the equivalence in stages:

Stage A: numCycles(γπ) ≤ n + 1 for all pairings (upper bound)
Stage B: numCycles(γπ) = n + 1 → noncrossing (equality → noncrossing)
Stage C: noncrossing → numCycles(γπ) = n + 1 (noncrossing → equality)

Then genus = 0 ↔ numCycles = n + 1 ↔ noncrossing.
-/

-- Stage A: Universal upper bound on cycle count.
-- This is Pairing.numCycles_le above.

/-- Powers of finRotate commute with finRotate (since finRotate commutes with itself). -/
private lemma longCycle_comm_rotate (n k : ℕ) :
    (finRotate (2 * n)) ^ k * finRotate (2 * n) =
    finRotate (2 * n) * (finRotate (2 * n)) ^ k := by
  rw [← pow_succ, ← pow_succ']

/-- After rotation to (0,1), the product longCycle * p' has 1 as fixed point. -/
private lemma sigma_fixedPoint_one {n : ℕ} (p' : Perm (Fin (2 * (n + 1))))
    (h₁ : p' ⟨1, by omega⟩ = ⟨0, by omega⟩) :
    (longCycle (n + 1) * p') ⟨1, by omega⟩ = ⟨1, by omega⟩ := by
  simp only [mul_apply, h₁, longCycle]
  -- finRotate sends 0 to 1: use finRotate_pow_apply' with k=1
  have h0lt : (0 : ℕ) < 2 * (n + 1) := by omega
  have := finRotate_pow_apply' h0lt 1 ⟨0, h0lt⟩
  simp only [pow_one] at this
  exact this

/-- The orbit-absorption lemma: longCycle(n+1) * q (where q fixes 0 and 1)
    has the same number of cycles as longCycle(n) * contracted, where
    contracted is obtained from p' = swap(0,1) * q via contractZeroOne.
    Elements 0 and 1 are absorbed into an existing orbit without creating
    new orbits: 0 -> 1 -> 2 in longCycle*q, extending the orbit containing 2. -/
private theorem numCycles_orbit_absorption {n : ℕ} (hn : 1 ≤ n)
    (p' : Perm (Fin (2 * (n + 1))))
    (h₀ : p' ⟨0, by omega⟩ = ⟨1, by omega⟩)
    (h₁ : p' ⟨1, by omega⟩ = ⟨0, by omega⟩)
    (_hinv : p' ^ 2 = 1)
    (_hfpf : ∀ x, p' x ≠ x) :
    let q := swap ⟨0, by omega⟩ ⟨1, by omega⟩ * p'
    numCycles (longCycle (n + 1) * q) =
      numCycles (longCycle n * (SemicircleCore.contractZeroOne p' h₀ h₁)) := by
  -- Proof via two applications of numCycles_swap_mul_of_apply and extendDomain.
  -- swap(1,2)*swap(0,1)*(longCycle(n+1)*q) = τ.extendDomain(shiftTwoEquiv n)
  -- where τ = longCycle(n) * contractZeroOne.
  -- numCycles of the extendDomain equals numCycles(τ) + 2 (two extra fixed points).
  -- Two swap applications add 2 to numCycles. So numCycles(longCycle*q) = numCycles(τ).
  intro q
  -- Helper for Fin inequality proofs: converts Fin equality to val equality
  have fin_ne : ∀ {m : ℕ} (a b : Fin m), a.val ≠ b.val → a ≠ b :=
    fun a b h hab => h (congr_arg Fin.val hab)
  set τ := longCycle n * SemicircleCore.contractZeroOne p' h₀ h₁
  set e := SemicircleCore.shiftTwoEquiv n
  -- q fixes 0 and 1
  have hq0 : q ⟨0, by omega⟩ = (⟨0, by omega⟩ : Fin (2 * (n + 1))) := by
    change (swap (⟨0, by omega⟩ : Fin (2 * (n + 1))) ⟨1, by omega⟩ * p') ⟨0, by omega⟩ = _
    rw [mul_apply, h₀, Equiv.swap_apply_right]
  have hq1 : q ⟨1, by omega⟩ = (⟨1, by omega⟩ : Fin (2 * (n + 1))) := by
    change (swap (⟨0, by omega⟩ : Fin (2 * (n + 1))) ⟨1, by omega⟩ * p') ⟨1, by omega⟩ = _
    rw [mul_apply, h₁, Equiv.swap_apply_left]
  -- longCycle at 0 and 1
  have hγ0 : longCycle (n + 1) ⟨0, by omega⟩ = (⟨1, by omega⟩ : Fin (2 * (n + 1))) := by
    unfold longCycle
    have := finRotate_pow_apply' (by omega : 0 < 2 * (n + 1)) 1 ⟨0, by omega⟩
    simp only [pow_one] at this; rw [this]; ext
    simp [Nat.mod_eq_of_lt (show 1 < 2 * (n + 1) by omega)]
  -- longCycle at 1
  have hγ1 : longCycle (n + 1) ⟨1, by omega⟩ = (⟨2, by omega⟩ : Fin (2 * (n + 1))) := by
    unfold longCycle
    have := finRotate_pow_apply' (by omega : 0 < 2 * (n + 1)) 1 ⟨1, by omega⟩
    simp only [pow_one] at this; convert this using 1
    ext; simp [Nat.mod_eq_of_lt (show 2 < 2 * (n + 1) by omega)]
  set σ := longCycle (n + 1) * q with hσ_def
  -- σ(0) = 1
  have hσ0 : σ ⟨0, by omega⟩ = (⟨1, by omega⟩ : Fin (2 * (n + 1))) := by
    simp only [hσ_def, mul_apply, hq0]; exact hγ0
  have hσ0_ne : σ ⟨0, by omega⟩ ≠ ⟨0, by omega⟩ := by
    rw [hσ0]; intro h; exact absurd (congr_arg Fin.val h) (by simp)
  -- Step 1: swap(0, σ(0)) * σ has numCycles = numCycles(σ) + 1
  have hswap1 : numCycles (swap ⟨0, by omega⟩ ⟨1, by omega⟩ * σ) = numCycles σ + 1 := by
    conv_lhs => rw [show (⟨1, by omega⟩ : Fin (2 * (n + 1))) = σ ⟨0, by omega⟩ from hσ0.symm]
    exact numCycles_swap_mul_of_apply σ ⟨0, by omega⟩ hσ0_ne
  set σ' := swap (⟨0, by omega⟩ : Fin (2 * (n + 1))) ⟨1, by omega⟩ * σ with hσ'_def
  -- σ(1) = 2
  have hσ1 : σ ⟨1, by omega⟩ = (⟨2, by omega⟩ : Fin (2 * (n + 1))) := by
    simp only [hσ_def, mul_apply, hq1]; exact hγ1
  -- σ'(1) = 2
  have hσ'1 : σ' ⟨1, by omega⟩ = (⟨2, by omega⟩ : Fin (2 * (n + 1))) := by
    simp only [hσ'_def, mul_apply, hσ1]
    exact swap_apply_of_ne_of_ne
      (by intro h; exact absurd (congr_arg Fin.val h) (by simp))
      (by intro h; exact absurd (congr_arg Fin.val h) (by simp))
  have hσ'1_ne : σ' ⟨1, by omega⟩ ≠ ⟨1, by omega⟩ := by
    rw [hσ'1]; intro h; exact absurd (congr_arg Fin.val h) (by simp)
  -- Step 2: swap(1, σ'(1)) * σ'
  have hswap2 : numCycles (swap ⟨1, by omega⟩ ⟨2, by omega⟩ * σ') = numCycles σ' + 1 := by
    conv_lhs => rw [show (⟨2, by omega⟩ : Fin (2 * (n + 1))) = σ' ⟨1, by omega⟩ from hσ'1.symm]
    exact numCycles_swap_mul_of_apply σ' ⟨1, by omega⟩ hσ'1_ne
  -- Step 3: Perm equality: swap(1,2)*swap(0,1)*(longCycle*q) = τ.extendDomain(e)
  -- Helper: for y with y.val ≥ 2, swap(1,2)(swap(0,1)(longCycle(n+1)(y))) = ⟨(y.val-1)%(2n)+2, _⟩
  have lhs_val_eq : ∀ (y : Fin (2 * (n + 1))), 2 ≤ y.val →
      (swap (⟨1, by omega⟩ : Fin (2 * (n + 1))) ⟨2, by omega⟩
        (swap (⟨0, by omega⟩ : Fin (2 * (n + 1))) ⟨1, by omega⟩
          (longCycle (n + 1) y))) =
      ⟨(y.val - 1) % (2 * n) + 2, by
        have := Nat.mod_lt (y.val - 1) (show 0 < 2 * n by omega); omega⟩ := by
    intro y hy
    have hlc_val : (longCycle (n + 1) y).val = (y.val + 1) % (2 * (n + 1)) := by
      have h := finRotate_pow_apply' (show 0 < 2 * (n + 1) by omega) 1 y
      simp only [pow_one] at h; exact congr_arg Fin.val h
    by_cases hmax : y.val = 2 * n + 1
    · have hlce : longCycle (n + 1) y = ⟨0, by omega⟩ := by
        apply Fin.ext; rw [hlc_val, hmax]; change (2 * n + 2) % (2 * (n + 1)) = 0
        change (2 * (n + 1)) % (2 * (n + 1)) = 0; exact Nat.mod_self _
      rw [hlce, Equiv.swap_apply_left, Equiv.swap_apply_left]
      apply Fin.ext; change 2 = (y.val - 1) % (2 * n) + 2
      rw [hmax, show 2 * n + 1 - 1 = 2 * n from by omega, Nat.mod_self]
    · have hlt : y.val + 1 < 2 * (n + 1) := by omega
      have hlce : longCycle (n + 1) y = ⟨y.val + 1, hlt⟩ := by
        apply Fin.ext; rw [hlc_val, Nat.mod_eq_of_lt hlt]
      rw [hlce]
      have hne0 : (⟨y.val + 1, hlt⟩ : Fin (2 * (n + 1))) ≠ ⟨0, by omega⟩ := by
        simp only [ne_eq, Fin.mk.injEq]; omega
      have hne1 : (⟨y.val + 1, hlt⟩ : Fin (2 * (n + 1))) ≠ ⟨1, by omega⟩ := by
        simp only [ne_eq, Fin.mk.injEq]; omega
      have hne2 : (⟨y.val + 1, hlt⟩ : Fin (2 * (n + 1))) ≠ ⟨2, by omega⟩ := by
        simp only [ne_eq, Fin.mk.injEq]; omega
      rw [swap_apply_of_ne_of_ne hne0 hne1, swap_apply_of_ne_of_ne hne1 hne2]
      apply Fin.ext; change y.val + 1 = (y.val - 1) % (2 * n) + 2
      rw [Nat.mod_eq_of_lt (show y.val - 1 < 2 * n by omega)]; omega
  have hperm_eq : swap (⟨1, by omega⟩ : Fin (2 * (n + 1))) ⟨2, by omega⟩ * σ' =
      τ.extendDomain e := by
    apply Equiv.Perm.ext; intro x
    simp only [mul_apply, hσ'_def, hσ_def]
    by_cases hx0 : x = ⟨0, by omega⟩
    · subst hx0
      rw [hq0, hγ0, Equiv.swap_apply_right]
      rw [show swap (⟨1, by omega⟩ : Fin (2 * (n + 1))) ⟨2, by omega⟩ ⟨0, by omega⟩
            = ⟨0, by omega⟩ from
        swap_apply_of_ne_of_ne
          (by intro h; exact absurd (congr_arg Fin.val h) (by simp))
          (by intro h; exact absurd (congr_arg Fin.val h) (by simp))]
      symm; exact Equiv.Perm.extendDomain_apply_not_subtype _ _ (by simp)
    · by_cases hx1 : x = ⟨1, by omega⟩
      · subst hx1
        rw [hq1, hγ1]
        rw [show swap (⟨0, by omega⟩ : Fin (2 * (n + 1))) ⟨1, by omega⟩
              (⟨2, by omega⟩ : Fin (2 * (n + 1))) = ⟨2, by omega⟩ from
          swap_apply_of_ne_of_ne
            (by intro h; exact absurd (congr_arg Fin.val h) (by simp))
            (by intro h; exact absurd (congr_arg Fin.val h) (by simp))]
        rw [Equiv.swap_apply_right]
        symm; exact Equiv.Perm.extendDomain_apply_not_subtype _ _ (by simp)
      · -- x.val ≥ 2
        have hxge2 : 2 ≤ x.val := by
          by_contra hlt; push Not at hlt
          have : x.val = 0 ∨ x.val = 1 := by omega
          rcases this with h | h <;> [exact hx0 (Fin.ext h); exact hx1 (Fin.ext h)]
        have hp'x_ge : 2 ≤ (p' x).val := SemicircleCore.mapsTo_remaining h₀ h₁ hxge2
        -- q(x) = p'(x) for x ≥ 2
        have hqx : q x = p' x := by
          change (swap (⟨0, by omega⟩ : Fin (2 * (n + 1))) ⟨1, by omega⟩ * p') x = p' x
          rw [mul_apply]
          refine swap_apply_of_ne_of_ne ?_ ?_
          · simp only [ne_eq, Fin.ext_iff]; omega
          · simp only [ne_eq, Fin.ext_iff]; omega
        rw [hqx, lhs_val_eq (p' x) hp'x_ge]
        -- RHS: extendDomain
        have hext_x := Equiv.Perm.extendDomain_apply_subtype τ e hxge2
        rw [hext_x]; apply Fin.ext
        -- Compute contractZeroOne val
        have hczo_val : (SemicircleCore.contractZeroOne p' h₀ h₁ (e.symm ⟨x, hxge2⟩)).val =
            (p' x).val - 2 := by
          unfold SemicircleCore.contractZeroOne
          simp only [Equiv.trans_apply]
          rw [show (SemicircleCore.shiftTwoEquiv n)
              ((SemicircleCore.shiftTwoEquiv n).symm ⟨x, hxge2⟩) = ⟨x, hxge2⟩ from
            (SemicircleCore.shiftTwoEquiv n).apply_symm_apply ⟨x, hxge2⟩]
          simp [SemicircleCore.shiftTwoEquiv]
        -- Compute τ val
        have hτ_val : (τ (e.symm ⟨x, hxge2⟩)).val = ((p' x).val - 1) % (2 * n) := by
          simp only [τ, mul_apply]
          have hlc := finRotate_pow_apply' (show 0 < 2 * n by omega) 1
            (SemicircleCore.contractZeroOne p' h₀ h₁ (e.symm ⟨x, hxge2⟩))
          simp only [pow_one] at hlc
          rw [show (longCycle n) = finRotate (2 * n) from rfl]
          rw [congr_arg Fin.val hlc, hczo_val]
          change ((p' x).val - 2 + 1) % (2 * n) = ((p' x).val - 1) % (2 * n)
          congr 1; omega
        -- e(z) coercion gives z.val + 2
        have he_coe : (↑(e (τ (e.symm ⟨x, hxge2⟩))) : Fin (2 * (n + 1))).val =
            (τ (e.symm ⟨x, hxge2⟩)).val + 2 := by
          simp [SemicircleCore.shiftTwoEquiv, e]
        rw [he_coe, hτ_val]
  -- Step 4: numCycles(extendDomain) = numCycles(τ) + 2
  have hext_nc : numCycles (τ.extendDomain e) = numCycles τ + 2 := by
    unfold Equiv.Perm.numCycles
    have hct : (τ.extendDomain e).cycleType = τ.cycleType :=
      Equiv.Perm.cycleType_extendDomain _
    have hfp_ext : card (Function.fixedPoints (τ.extendDomain e)) =
        card (Fin (2 * (n + 1))) - (τ.extendDomain e).cycleType.sum :=
      Equiv.Perm.card_fixedPoints _
    have hfp_τ : card (Function.fixedPoints τ) =
        card (Fin (2 * n)) - τ.cycleType.sum :=
      Equiv.Perm.card_fixedPoints _
    rw [hfp_ext, hfp_τ, hct]; simp only [card_fin]
    have hle : τ.cycleType.sum ≤ 2 * n := by
      rw [Equiv.Perm.sum_cycleType]
      have := τ.support.card_le_univ; simp only [card_fin] at this; exact this
    omega
  -- Step 5: Combine
  -- From hperm_eq: numCycles(swap*σ') = numCycles(τ.extendDomain e) = numCycles(τ) + 2
  -- From hswap2: numCycles(swap*σ') = numCycles(σ') + 1
  -- From hswap1: numCycles(σ') = numCycles(σ) + 1
  -- So numCycles(σ) + 2 = numCycles(τ) + 2, hence numCycles(σ) = numCycles(τ)
  rw [hperm_eq] at hswap2; rw [hswap1] at hswap2; omega

private theorem numCycles_split_normalized {n : ℕ} (hn : 1 ≤ n)
    (p' : Perm (Fin (2 * (n + 1))))
    (h₀ : p' ⟨0, by omega⟩ = ⟨1, by omega⟩)
    (h₁ : p' ⟨1, by omega⟩ = ⟨0, by omega⟩)
    (hinv : p' ^ 2 = 1)
    (hfpf : ∀ x, p' x ≠ x) :
    numCycles (longCycle (n + 1) * p') =
      numCycles (longCycle n * (SemicircleCore.contractZeroOne p' h₀ h₁)) + 1 := by
  -- Step 1: Decompose p' = swap(0,1) * q where q fixes 0 and 1
  set q := swap ⟨0, by omega⟩ ⟨1, by omega⟩ * p' with hq_def
  -- Step 2: γ * p' = swap(γ(0), γ(1)) * (γ * q) = swap(1,2) * (γ * q)
  -- via Mathlib's mul_swap_eq_swap_mul: f * swap x y = swap (f x) (f y) * f
  -- γ(0) = 1 and γ(1) = 2
  have hγ0 : longCycle (n + 1) ⟨0, by omega⟩ = (⟨1, by omega⟩ : Fin (2 * (n + 1))) := by
    unfold longCycle
    have := finRotate_pow_apply' (by omega : 0 < 2 * (n + 1)) 1 ⟨0, by omega⟩
    simp only [pow_one] at this; rw [this]; ext
    simp [Nat.mod_eq_of_lt (show 1 < 2 * (n + 1) by omega)]
  have hγ1 : longCycle (n + 1) ⟨1, by omega⟩ = (⟨2, by omega⟩ : Fin (2 * (n + 1))) := by
    unfold longCycle
    have := finRotate_pow_apply' (by omega : 0 < 2 * (n + 1)) 1 ⟨1, by omega⟩
    simp only [pow_one] at this; convert this using 1
    ext; simp [Nat.mod_eq_of_lt (show 2 < 2 * (n + 1) by omega)]
  -- γ * p' = swap(1,2) * (γ * q) via mul_swap_eq_swap_mul
  have hγp_eq : longCycle (n + 1) * p' =
      swap ⟨1, by omega⟩ ⟨2, by omega⟩ * (longCycle (n + 1) * q) := by
    have hsw : p' = swap ⟨0, by omega⟩ ⟨1, by omega⟩ * q := by
      simp [hq_def]
    rw [hsw, ← mul_assoc, Equiv.mul_swap_eq_swap_mul, hγ0, hγ1, mul_assoc]
  -- q fixes 1, and (γ*q)(1) = γ(1) = 2
  have hq1 : q ⟨1, by omega⟩ = (⟨1, by omega⟩ : Fin (2 * (n + 1))) := by
    change (swap (⟨0, by omega⟩ : Fin (2 * (n + 1))) ⟨1, by omega⟩ * p') ⟨1, by omega⟩ = _
    simp only [mul_apply, h₁]
    rfl
  have hgq1 : (longCycle (n + 1) * q) ⟨1, by omega⟩ = (⟨2, by omega⟩ : Fin (2 * (n + 1))) := by
    simp only [mul_apply, hq1]; exact hγ1
  have hgq1_ne : (longCycle (n + 1) * q) ⟨1, by omega⟩ ≠ ⟨1, by omega⟩ := by
    rw [hgq1]; simp [Fin.ext_iff, Nat.mod_eq_of_lt (show 1 < 2 * (n + 1) by omega)]
  -- Apply swap lemma + orbit absorption
  rw [hγp_eq, ← hgq1,
      numCycles_swap_mul_of_apply _ _ hgq1_ne,
      numCycles_orbit_absorption hn p' h₀ h₁ hinv hfpf]

/-- The cycle-splitting lemma: removing an adjacent pair from a
    pairing decreases numCycles(γπ) by 1. Equivalently, the pairing
    with the adjacent pair has one more cycle than the contracted one.
    Requires n ≥ 1 so the target Pairing n is on ≥ 2 elements. -/
theorem numCycles_delete_adjacent {n : ℕ} (hn : 1 ≤ n) (p : Pairing (n + 1))
    (i : Fin (2 * (n + 1))) (h : p.hasAdjacentAt i) :
    numCycles (longCycle (n + 1) * p.val) =
      numCycles (longCycle n * (p.deleteAdjacent i h).val) + 1 := by
  -- Step 1: Reduce to normalized form via conjugation
  -- Let ρ = finRotate^(2(n+1) - i.val) which rotates i to 0 and (i+1) to 1
  let ρ : Perm (Fin (2 * (n + 1))) := (finRotate _) ^ (2 * (n + 1) - i.val)
  let p' : Perm (Fin (2 * (n + 1))) := ρ * p.val * ρ⁻¹
  -- Key: ρ commutes with longCycle since ρ is a power of longCycle
  have hρ_comm : ρ * longCycle (n + 1) = longCycle (n + 1) * ρ := by
    change (finRotate (2 * (n + 1))) ^ _ * finRotate (2 * (n + 1)) =
         finRotate (2 * (n + 1)) * (finRotate (2 * (n + 1))) ^ _
    rw [← pow_succ, ← pow_succ']
  -- Therefore: ρ * (longCycle * p.val) * ρ⁻¹ = longCycle * p'
  have hconj_eq : ρ * (longCycle (n + 1) * p.val) * ρ⁻¹ = longCycle (n + 1) * p' := by
    change ρ * (longCycle (n + 1) * p.val) * ρ⁻¹ = longCycle (n + 1) * (ρ * p.val * ρ⁻¹)
    calc ρ * (longCycle (n + 1) * p.val) * ρ⁻¹
        = (ρ * longCycle (n + 1)) * p.val * ρ⁻¹ := by group
      _ = (longCycle (n + 1) * ρ) * p.val * ρ⁻¹ := by rw [hρ_comm]
      _ = longCycle (n + 1) * (ρ * p.val * ρ⁻¹) := by group
  -- Conjugation preserves numCycles
  have hconj_nc : numCycles (longCycle (n + 1) * p.val) =
      numCycles (longCycle (n + 1) * p') := by
    have : longCycle (n + 1) * p.val =
        ρ⁻¹ * (longCycle (n + 1) * p') * (ρ⁻¹)⁻¹ := by
      rw [inv_inv]
      have := hconj_eq
      calc longCycle (n + 1) * p.val
          = ρ⁻¹ * (ρ * (longCycle (n + 1) * p.val) * ρ⁻¹) * ρ := by group
        _ = ρ⁻¹ * (longCycle (n + 1) * p') * ρ := by rw [hconj_eq]
    rw [this, numCycles_conj]
  -- Step 2: Establish that p' satisfies the normalized conditions
  have hρ0 : ρ i = ⟨0, by omega⟩ :=
    rotate_self_eq_zero (2 * (n + 1)) (by omega) i
  have hρ1 : ρ (finRotate _ i) = ⟨1, by omega⟩ :=
    rotate_succ_eq_one (2 * (n + 1)) i (by omega)
  have h₀' : p' ⟨0, by omega⟩ = ⟨1, by omega⟩ :=
    conjugate_sends hρ0 hρ1 h
  have h₁' : p' ⟨1, by omega⟩ = ⟨0, by omega⟩ :=
    conjugate_sends_back hρ0 hρ1 p.property.1 h
  have hinv' : p' ^ 2 = 1 := by
    have hππ : p.val * p.val = 1 := by have := p.property.1; rwa [sq] at this
    change (ρ * p.val * ρ⁻¹) ^ 2 = 1
    rw [sq]
    calc (ρ * p.val * ρ⁻¹) * (ρ * p.val * ρ⁻¹)
        = ρ * (p.val * p.val) * ρ⁻¹ := by group
      _ = ρ * 1 * ρ⁻¹ := by rw [hππ]
      _ = 1 := by group
  have hfpf' : ∀ x, p' x ≠ x := by
    intro x hfix
    have hfix' : (ρ * p.val * ρ⁻¹) x = x := hfix
    simp only [mul_apply] at hfix'
    have : p.val (ρ⁻¹ x) = ρ⁻¹ x := by
      have := congr_arg ρ.symm hfix'
      simpa [Equiv.symm_apply_apply] using this
    exact p.property.2 (ρ⁻¹ x) this
  -- Step 3: Apply the normalized splitting lemma
  rw [hconj_nc]
  -- The deleteAdjacent construction produces exactly contractZeroOne p'
  -- by definition (it rotates to (0,1) then contracts)
  suffices hda_eq : (p.deleteAdjacent i h).val = SemicircleCore.contractZeroOne p' h₀' h₁' by
    rw [hda_eq]
    exact numCycles_split_normalized hn p' h₀' h₁' hinv' hfpf'
  -- deleteAdjacent unfolds to contractZeroOne applied to the same p'
  show (p.deleteAdjacent i h).val = SemicircleCore.contractZeroOne p' h₀' h₁'
  unfold Pairing.deleteAdjacent
  rfl

/-! ### Helpers for Stage B: fixed points imply adjacent pairs -/

/-- For any multiset where all elements are at least 2, the sum is at least 2 times the card. -/
private lemma multiset_sum_ge_two_card {s : Multiset ℕ} (h : ∀ c ∈ s, 2 ≤ c) :
    s.sum ≥ 2 * s.card := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a t ih =>
    simp only [Multiset.sum_cons, Multiset.card_cons]
    have ha := h a (Multiset.mem_cons_self a t)
    have ht := ih (fun c hc => h c (Multiset.mem_cons_of_mem hc))
    omega

/-- If numCycles(gamma * pi) = n + 2 on Fin(2*(n+1)), then gamma * pi has a fixed point.
    The proof uses: numCycles = cycleType.card + |fixedPoints|, each nontrivial cycle
    has length >= 2, so cycleType.card <= n, hence |fixedPoints| >= 2 > 0. -/
private lemma has_fixedPoint_of_maxCycles {n : ℕ} (p : Pairing (n + 1))
    (h : numCycles (longCycle (n + 1) * p.val) = n + 2) :
    ∃ x : Fin (2 * (n + 1)), (longCycle (n + 1) * p.val) x = x := by
  set σ := longCycle (n + 1) * p.val
  have hfp_card := Equiv.Perm.card_fixedPoints σ
  have hsum := Equiv.Perm.sum_cycleType σ
  have hsum_ge := multiset_sum_ge_two_card
    (fun c hc => Equiv.Perm.two_le_of_mem_cycleType hc : ∀ c ∈ σ.cycleType, 2 ≤ c)
  have hsupp_le : σ.support.card ≤ 2 * (n + 1) := by
    calc σ.support.card ≤ Finset.univ.card := Finset.card_le_card (Finset.subset_univ _)
      _ = 2 * (n + 1) := by simp [card_fin]
  unfold Equiv.Perm.numCycles at h
  rw [hfp_card, card_fin, hsum] at h
  have hfp_pos : 0 < card (Function.fixedPoints σ) := by
    rw [hfp_card, card_fin, hsum]; omega
  rw [card_pos_iff] at hfp_pos
  obtain ⟨⟨x, hx⟩⟩ := hfp_pos
  exact ⟨x, hx⟩

/-- A fixed point x of (gamma * pi) yields an adjacent pair at gamma^{-1}(x).
    If gamma(pi(x)) = x, then pi(x) = gamma^{-1}(x). By the involution property,
    pi(gamma^{-1}(x)) = x = gamma(gamma^{-1}(x)), so gamma^{-1}(x) is adjacent. -/
private lemma fixedPoint_gives_adjacent {n : ℕ} (p : Pairing (n + 1))
    (x : Fin (2 * (n + 1)))
    (hfp : (longCycle (n + 1) * p.val) x = x) :
    p.hasAdjacentAt ((longCycle (n + 1) : Perm (Fin (2 * (n + 1))))⁻¹ x) := by
  set γ : Perm (Fin (2 * (n + 1))) := longCycle (n + 1) with hγ_def
  unfold Pairing.hasAdjacentAt
  -- From hfp: γ (p.val x) = x, so p.val x = γ.symm x
  have hgpx : γ (p.val x) = x := by change (γ * p.val) x = x; exact hfp
  have h1 : p.val x = γ.symm x := by
    apply_fun γ.symm at hgpx; simp only [symm_apply_apply] at hgpx; exact hgpx
  -- p.val is an involution: p.val (p.val y) = y for all y
  have hinv : ∀ y, p.val (p.val y) = y := by
    intro y
    have hsq : p.val * p.val = 1 := by have := p.property.1; rwa [sq] at this
    exact congr_fun (congr_arg DFunLike.coe hsq) y
  -- Substituting h1: p.val (γ.symm x) = x
  have h2 : p.val (γ.symm x) = x := by rw [← h1]; exact hinv x
  -- Goal: p.val (γ⁻¹ x) = finRotate _ (γ⁻¹ x), where γ⁻¹ = γ.symm
  change p.val (γ.symm x) = finRotate (2 * (n + 1)) (γ.symm x)
  rw [h2, hγ_def, longCycle, Equiv.apply_symm_apply]

/-- Stage B: If the cycle count achieves its maximum, the pairing
    is noncrossing.

    Proof: by induction on n. The key insight is that numCycles = n+1
    forces the composition gamma*pi to have fixed points (at least 2).
    Each fixed point yields an adjacent pair via the involution property.
    After deleting that adjacent pair, the cycle-splitting lemma gives
    numCycles = n for the contracted pairing, and induction applies. -/
theorem Pairing.maxCycles_imp_noncrossing {n : ℕ} (p : Pairing n)
    (h : numCycles (longCycle n * p.val) = n + 1) :
    p.IsNoncrossing := by
  induction n with
  | zero => exact trivial
  | succ m ih =>
    -- Find a fixed point of gamma * pi, then extract an adjacent pair
    obtain ⟨x, hfp⟩ := has_fixedPoint_of_maxCycles p (by omega)
    set i := ((longCycle (m + 1) : Perm (Fin (2 * (m + 1))))⁻¹ x)
    have hadj := fixedPoint_gives_adjacent p x hfp
    cases m with
    | zero =>
      -- m = 0, n = 1: deleteAdjacent gives Pairing 0, trivially noncrossing
      exact ⟨i, hadj, trivial⟩
    | succ k =>
      -- m = k+1, n = k+2: use cycle-splitting + induction
      refine ⟨i, hadj, ih (p.deleteAdjacent i hadj) ?_⟩
      have hda := numCycles_delete_adjacent (by omega : 1 ≤ k + 1) p i hadj
      omega

/-- Stage C: Noncrossing pairings achieve maximum cycle count.

    Proof: induction on n using the recursive noncrossing definition.
    Base case (n = 1): direct computation — the unique pairing on Fin 2
    composed with the long cycle gives the identity, which has 2 cycles.
    Inductive step: if p is noncrossing, it has an adjacent pair at
    some i. Deleting this pair gives a noncrossing pairing p' on 2n
    points with numCycles(γ' * p') = n + 1 by induction. The
    cycle-splitting lemma gives numCycles(γπ) = numCycles(γ'π') + 1.

    Requires n ≥ 1: on Fin 0, numCycles = 0 ≠ 1 = 0 + 1. -/
theorem Pairing.noncrossing_imp_maxCycles {n : ℕ} (p : Pairing n)
    (hn : 1 ≤ n) (h : p.IsNoncrossing) :
    numCycles (longCycle n * p.val) = n + 1 := by
  induction n with
  | zero => omega
  | succ m ih =>
    obtain ⟨i, hi, hnc'⟩ := h
    cases m with
    | zero =>
      -- n = 1: Pairing on Fin(2*1), unique fpf involution is swap(0,1)
      -- longCycle 1 = finRotate 2 = swap(0,1), so γπ = id, numCycles = 2
      have h0 : p.val ⟨0, by omega⟩ = ⟨1, by omega⟩ := by
        have hne := p.property.2 ⟨0, by omega⟩
        have hlt := (p.val ⟨0, by omega⟩).isLt
        have hne0 : (p.val ⟨0, by omega⟩).val ≠ 0 := fun h => hne (Fin.ext h)
        exact Fin.ext (show (p.val ⟨0, by omega⟩).val = 1 by omega)
      have h1 : p.val ⟨1, by omega⟩ = ⟨0, by omega⟩ := by
        have hsq : p.val * p.val = 1 := by have := p.property.1; rwa [sq] at this
        have h2 := congr_fun (congr_arg DFunLike.coe hsq) ⟨0, by omega⟩
        simp only [mul_apply, Perm.coe_one, id_eq] at h2
        rw [h0] at h2; exact h2
      have hgp : longCycle 1 * p.val = 1 := by
        ext ⟨x, hx⟩; simp only [mul_apply, Perm.coe_one, id_eq, longCycle]
        have : x = 0 ∨ x = 1 := by omega
        rcases this with rfl | rfl
        · rw [h0]; rfl
        · rw [h1]; rfl
      rw [hgp]; simp [numCycles]
    | succ k =>
      -- n = k + 2: use cycle-splitting lemma and inductive hypothesis
      have hda := numCycles_delete_adjacent (by omega : 1 ≤ k + 1) p i hi
      have hih := ih (p.deleteAdjacent i hi) (by omega) hnc'
      omega

/-! ## 7. Main Theorem and Corollary -/

/-- **The Bridge Theorem**: genus zero ↔ noncrossing. -/
theorem Pairing.genus_zero_iff_noncrossing {n : ℕ} (p : Pairing n) :
    p.genus = 0 ↔ p.IsNoncrossing := by
  cases n with
  | zero =>
    -- n = 0: genus = (1-0)/2 = 0, IsNoncrossing = True. Both trivially true.
    simp only [Pairing.IsNoncrossing]
    constructor
    · intro _; trivial
    · intro _
      unfold Pairing.genus Equiv.Perm.numCycles longCycle
      simp [Equiv.Perm.cycleType, Function.fixedPoints]
  | succ m =>
    constructor
    · -- genus = 0 → numCycles = n+1 → noncrossing
      intro hg
      have hc : numCycles (longCycle (m + 1) * p.val) = m + 1 + 1 := by
        unfold Pairing.genus at hg
        have hle := p.numCycles_le
        have hparity := p.genus_exact (by omega)
        unfold Pairing.genus at hparity
        omega
      exact p.maxCycles_imp_noncrossing hc
    · -- noncrossing → numCycles = n+1 → genus = 0
      intro hnc
      have hc := p.noncrossing_imp_maxCycles (by omega) hnc
      unfold Pairing.genus
      rw [hc]
      simp

instance {n : ℕ} : DecidablePred (@IsPairing n) := fun _ =>
  inferInstanceAs (Decidable (_ ∧ _))

instance {n : ℕ} : Fintype (Pairing n) :=
  Subtype.fintype _

-- **Corollary**: the number of genus-zero pairings equals Cₙ.
-- This theorem conceptually belongs here (genus-counting near genus results),
-- but is proved in `SemicircleCheck.CatalanRecurrence` as `Pairing.genus_zero_count`
-- because it requires the Catalan equivalence and finitary cardinality machinery
-- defined there. CatalanRecurrence imports GenusNoncrossing, so the proof cannot
-- live in this file without creating a circular import.

/-! ## 8. Proof Dependencies and Estimated Effort

### Lemmas that need building (not in Mathlib):
1. `numCycles_eq_num_orbits` — total cycles = orbits of ⟨σ⟩-action
2. `Pairing.deleteAdjacent` — the deletion/reindexing construction
3. `numCycles_insert_adjacent` — the cycle-splitting lemma
4. `Pairing.numCycles_le` — upper bound on cycles for pairings
5. `Pairing.maxCycles_imp_noncrossing` — contrapositive via crossing→merger
6. `Pairing.noncrossing_imp_maxCycles` — induction via deletion

### What Mathlib provides:
- `finRotate` and `isCycle_finRotate` for the long cycle
- `Equiv.Perm.cycleType` for nontrivial cycle structure
- `Function.fixedPoints` and `Fintype.card` for fixed point count
- `catalan` and `catalan_succ` for Catalan numbers
- Basic `Fin` arithmetic and `Perm` algebra

### Estimated scope: 800–1500 lines of Lean 4.

### The hardest part:
The deletion/reindexing machinery (Lemma 2 above). Removing two
points from Fin(2n) and reindexing to Fin(2(n-1)) while preserving
the pairing structure requires building an explicit embedding
Fin(2n-2) ↪ Fin(2n) and conjugating the permutation through it.
This is conceptually simple but technically fiddly in dependent
type theory. It is exactly the kind of thing an autoformalization
agent (Gauss, Aristotle) handles well with human scaffolding.

### The most satisfying part:
Once the bridge theorem compiles, the connection to the semicircle
law becomes a clean chain:
  E[Tr(W^{2n})/N] → trace expansion → pairing sum → genus filter
  → genus 0 = noncrossing = Catalan → semicircle moments
Each arrow is a separate formalizable step, and this file handles
the crucial middle link.
-/
