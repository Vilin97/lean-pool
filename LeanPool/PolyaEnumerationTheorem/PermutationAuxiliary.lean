/-
Copyright (c) 2026 Luka Opravš. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luka Opravš
-/
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Tactic

/-!
# Auxiliary results on permutations
-/

universe u

variable {X : Type u}

namespace LeanPool.PolyaEnumerationTheorem

namespace CyclesOfPermutation

/-!
## Cycles of a permutation

The cycles of a permutation `f : X → X` are defined as the equivalence classes of `X` quotiented
by the equivalence relation of being in the same cycle: `x₁ ∼ x₂ ↔ ∃ k : ℤ, fᵏ x₁ = x₂`.

To avoid working with cardinalities of quotients, we introduce a lemma that enables us to work with
cardinalities of finite sets instead. For a permutation `f`, we can construct a set of
representatives of its cycles, that is, a set that contains exactly one element of `X` from every
cycle of `f`. The number of cycles of `f` is equal to the cardinality of any such set of
representatives of its cycles.
-/

/-- The number of cycles in the permutation `f`. Cycles with only a single element are also
    counted, e.g., `c[0, 1] : Equiv.Perm (Fin 3)` has two cycles. -/
abbrev numCyclesOfPerm (f : Equiv.Perm X)
    [Fintype (Quotient (Equiv.Perm.SameCycle.setoid f))] : ℕ :=
  Fintype.card (Quotient (Equiv.Perm.SameCycle.setoid f))

/-- The number of cycles of a permutation `f : X → X` is equal to the cardinality of any set of
    representatives of its cycles. That is, any set that contains exactly one element of `X` from
    every cycle of `f`. -/
lemma numCyclesOfPerm_eq_card {f : Equiv.Perm X}
    [Fintype (Quotient (Equiv.Perm.SameCycle.setoid f))] {s : Finset X}
    (h1 : ∀ x ∈ s, ∀ y ∈ s, f.SameCycle x y → x = y)
    (h2 : ∀ x : X, ∃ y ∈ s, f.SameCycle x y) : numCyclesOfPerm f = s.card := by
  rw [← Fintype.card_coe]
  apply Fintype.card_congr ⟨
    Quotient.lift (fun x ↦ ⟨(h2 x).choose, (h2 x).choose_spec.1⟩) (by
      intro a b hab
      refine Subtype.ext ?_
      apply h1 _ (h2 a).choose_spec.1 _ (h2 b).choose_spec.1
      exact Equiv.Perm.SameCycle.trans (Equiv.Perm.SameCycle.trans
        (Equiv.Perm.SameCycle.symm (h2 a).choose_spec.2) hab) (h2 b).choose_spec.2),
    fun ⟨x, _⟩ ↦ ⟦x⟧,
    by
      intro x
      rcases Quotient.mk_surjective x with ⟨y, rfl⟩
      apply Quotient.sound
      exact Equiv.Perm.SameCycle.symm (h2 y).choose_spec.2,
    by
      intro ⟨x, hx⟩
      refine Subtype.ext ?_
      exact h1 _ (h2 x).choose_spec.1 x hx (Equiv.Perm.SameCycle.symm (h2 x).choose_spec.2)⟩

end CyclesOfPermutation


namespace PowersOfPermutation

/-!
## Powers of a permutation

Repeatedly applying a permutation of a finite set on some element will eventually result in that
same element. If `fⁿ⁺¹ x = x`, then for any `k ∈ ℤ`, we have `fᵏ x = fᵐ x` for some
`m ∈ {0, ..., n}`.
-/

/-- Given a permutation on a finite type `f : X → X` and any `x : X` there exists `n : ℕ` such
    that `fⁿ⁺¹ x = x`. -/
lemma exists_perm_pow [Finite X] (f : Equiv.Perm X) (x : X) :
    ∃ n, (f ^ (n + 1)) x = x := by
  classical
  haveI : Fintype X := Fintype.ofFinite X
  by_cases hx : x ∈ f.support
  · refine ⟨(f.cycleOf x).support.card - 1, ?_⟩
    rw [Nat.sub_add_cancel (by simp [Equiv.Perm.mem_support.1 hx]),
      ← (f.isCycle_cycleOf (Equiv.Perm.mem_support.1 hx)).orderOf,
      ← f.cycleOf_pow_apply_self, pow_orderOf_eq_one, Equiv.Perm.one_apply]
  · exact ⟨0, Equiv.Perm.notMem_support.1 hx⟩

/-- Given a permutation `f` satisfying `fⁿ x = x` we can reduce `fⁿ*ᵐ⁺ʳ x` to `fʳ x`. -/
lemma perm_pow_reduce {n m r : ℕ} {f : Equiv.Perm X} {x : X} (h : (f ^ n) x = x) :
    (f ^ (m * n + r)) x = (f ^ r) x := by
  induction m with
  | zero => simp
  | succ k hk =>
    rw [add_mul, one_mul, add_assoc, add_comm n, ← add_assoc, pow_add]
    simp [h, hk]

/-- Given a permutation `f` satisfying `fⁿ⁺¹ x = x` for some `n : ℕ`, then for any `k : ℤ`,
    `fᵏ x = fᵐ x` for some `m ∈ {0, ..., n}`. -/
lemma forall_exists_lt_perm_pow_eq_perm_pow {n : ℕ} {f : Equiv.Perm X} {x : X}
    (h : (f ^ (n + 1)) x = x) :
    ∀ k : ℤ, ∃ m < n + 1, (f ^ k) x = (f ^ m) x := by
  intro k
  refine ⟨(k % (n + 1 : ℤ)).toNat, ?_, ?_⟩
  · have hp : (0 : ℤ) < n + 1 := by positivity
    have hnn : 0 ≤ k % (n + 1 : ℤ) := Int.emod_nonneg k (by linarith)
    have hlt : k % (n + 1 : ℤ) < (n + 1 : ℤ) := Int.emod_lt_of_pos k hp
    have heq : ((k % (n + 1 : ℤ)).toNat : ℤ) = k % (n + 1 : ℤ) := Int.toNat_of_nonneg hnn
    omega
  · have hp : (0 : ℤ) < n + 1 := by positivity
    have hnn : 0 ≤ k % (n + 1 : ℤ) := Int.emod_nonneg k (by linarith)
    have heq : ((k % (n + 1 : ℤ)).toNat : ℤ) = k % (n + 1 : ℤ) := Int.toNat_of_nonneg hnn
    rw [show f ^ ((k % (n + 1 : ℤ)).toNat) = f ^ (((k % (n + 1 : ℤ)).toNat : ℤ)) from
          (zpow_natCast f _).symm, heq]
    nth_rewrite 1 [show k = (n + 1 : ℤ) * (k / (n + 1 : ℤ)) + k % (n + 1 : ℤ) from
          (Int.mul_ediv_add_emod k _).symm]
    rw [zpow_add, zpow_mul]
    have hint_h : ((f : Equiv.Perm X) ^ ((n + 1) : ℤ)) x = x := by
      rw [show ((n + 1) : ℤ) = ((n + 1 : ℕ) : ℤ) from by push_cast; ring, zpow_natCast]
      exact h
    have hfix : ∀ q : ℤ, ((f ^ ((n + 1) : ℤ)) ^ q) x = x := by
      intro q
      induction q with
      | zero => simp
      | succ m hm => rw [zpow_add_one, Equiv.Perm.mul_apply, hint_h, hm]
      | pred m hm =>
        have hinv_fix : (f ^ ((n + 1) : ℤ))⁻¹ x = x :=
          Equiv.Perm.inv_eq_iff_eq.mpr hint_h.symm
        rw [zpow_sub_one, Equiv.Perm.mul_apply, hinv_fix, hm]
    have key : ∀ (q r : ℤ), ((f ^ ((n + 1) : ℤ)) ^ q) ((f ^ r) x) = (f ^ r) x := by
      intro q r
      have hcomm : (f ^ ((n + 1) : ℤ)) ^ q * f ^ r = f ^ r * (f ^ ((n + 1) : ℤ)) ^ q := by
        rw [show (f ^ ((n + 1) : ℤ)) ^ q = f ^ ((n + 1 : ℤ) * q) from (zpow_mul f _ _).symm]
        exact zpow_mul_comm _ _ _
      rw [show ((f ^ ((n + 1) : ℤ)) ^ q) ((f ^ r) x) =
            ((f ^ ((n + 1) : ℤ)) ^ q * f ^ r) x from rfl, hcomm,
        Equiv.Perm.mul_apply, hfix]
    exact key _ _

end PowersOfPermutation


namespace ContractExpand

/-!
## Contraction or expansion of a domain of a permutation

We can contract a permutation `f` on `Fin (n + 1)` by removing `n` from the domain and remapping
`f⁻¹ n ↦ f n`. We get a permutation on `Fin n`. We can expand a permutation `f` on `Fin n` by
adding `n` to the domain and defining `f n = n`. We get a permutation on `Fin (n + 1)`.
-/

variable {n : ℕ}

/-- If `n < m + 1` and `n ≠ m` then `n < m`. -/
lemma lt_of_lt_succ_of_neq {m : ℕ} (h1 : m < n + 1) (h2 : m ≠ n) : m < n := by
  omega

/-- Embed `i : Fin n` into `Fin (n + 1)` by keeping the same underlying value. -/
private def liftFin (i : Fin n) : Fin (n + 1) := ⟨i.1, Nat.lt_succ_of_lt i.2⟩

@[simp] private lemma liftFin_val (i : Fin n) : (liftFin i).1 = i.1 := rfl

private lemma liftFin_of_lt {a : Fin (n + 1)} (ha : a.1 < n) :
    liftFin (⟨a.1, ha⟩ : Fin n) = a := Fin.ext rfl

/-- For any permutation `f` of `Fin (n + 1)`, if `f i = n` for some `i < n`, then `f (f i) < n`. -/
lemma perm_perm_val_lt_of_perm_val_eq {f : Equiv.Perm (Fin (n + 1))} {i : Fin n}
    (h : (f (liftFin i)).1 = n) : (f (f (liftFin i))).1 < n := by
  by_contra hcontra
  have heq : (f (f (liftFin i))).1 = n :=
    Nat.eq_of_lt_succ_of_not_lt (f (f (liftFin i))).2 hcontra
  have h1 : f (f (liftFin i)) = f (liftFin i) := Fin.ext (heq.trans h.symm)
  have h2 : f (liftFin i) = liftFin i := f.injective h1
  have h3 : (f (liftFin i)).1 = (liftFin i).1 := by rw [h2]
  rw [h, liftFin_val] at h3
  omega

/-- The forward direction of `permContract`. -/
private def contractFwd (f : Equiv.Perm (Fin (n + 1))) (i : Fin n) : Fin n :=
  if h : (f (liftFin i)).1 = n
  then ⟨(f (f (liftFin i))).1, perm_perm_val_lt_of_perm_val_eq h⟩
  else ⟨(f (liftFin i)).1, lt_of_lt_succ_of_neq (f (liftFin i)).2 h⟩

private lemma contractFwd_pos (f : Equiv.Perm (Fin (n + 1))) (i : Fin n)
    (h : (f (liftFin i)).1 = n) :
    contractFwd f i = ⟨(f (f (liftFin i))).1, perm_perm_val_lt_of_perm_val_eq h⟩ := by
  unfold contractFwd; exact dif_pos h

private lemma contractFwd_neg (f : Equiv.Perm (Fin (n + 1))) (i : Fin n)
    (h : (f (liftFin i)).1 ≠ n) :
    contractFwd f i = ⟨(f (liftFin i)).1, lt_of_lt_succ_of_neq (f (liftFin i)).2 h⟩ := by
  unfold contractFwd; exact dif_neg h

private lemma f_inv_apply_self (f : Equiv.Perm (Fin (n + 1))) (y : Fin (n + 1)) :
    f⁻¹ (f y) = y := by
  rw [← Equiv.Perm.mul_apply, inv_mul_cancel, Equiv.Perm.one_apply]

private lemma f_apply_inv_self (f : Equiv.Perm (Fin (n + 1))) (y : Fin (n + 1)) :
    f (f⁻¹ y) = y := by
  rw [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply]

/-- A function that takes a permutation `f` of `Fin (n + 1)` and returns a permutation of `Fin n`
    that behaves exactly the same as `f` on all inputs except on `f⁻¹ n`, where it returns `f n`,
    and `n`, which is no longer a valid input. -/
def permContract (f : Equiv.Perm (Fin (n + 1))) : Equiv.Perm (Fin n) where
  toFun := contractFwd f
  invFun := contractFwd f⁻¹
  left_inv := by
    intro i
    apply Fin.ext
    by_cases h1 : (f (liftFin i)).1 = n
    · -- case h1 = true
      rw [contractFwd_pos f i h1]
      -- liftFin of ⟨(f (f (liftFin i))).1, _⟩ equals f (f (liftFin i))
      have hl : liftFin (⟨(f (f (liftFin i))).1, perm_perm_val_lt_of_perm_val_eq h1⟩ : Fin n)
          = f (f (liftFin i)) := liftFin_of_lt _
      -- Condition for contractFwd f⁻¹: (f⁻¹ (liftFin _)).1 = n?
      -- f⁻¹ (f (f (liftFin i))) = f (liftFin i). Its .1 = h1 = n.
      have h2 : (f⁻¹ (liftFin (⟨(f (f (liftFin i))).1,
          perm_perm_val_lt_of_perm_val_eq h1⟩ : Fin n))).1 = n := by
        rw [hl, f_inv_apply_self]; exact h1
      rw [contractFwd_pos f⁻¹ _ h2]
      -- Now goal: (f⁻¹ (f⁻¹ (liftFin _))).1 = i.1
      simp only
      rw [hl, f_inv_apply_self, f_inv_apply_self]
      rfl
    · -- case h1 = false
      rw [contractFwd_neg f i h1]
      -- liftFin of ⟨(f (liftFin i)).1, _⟩ equals f (liftFin i)
      have hl : liftFin (⟨(f (liftFin i)).1,
          lt_of_lt_succ_of_neq (f (liftFin i)).2 h1⟩ : Fin n) = f (liftFin i) :=
        liftFin_of_lt _
      -- Condition for contractFwd f⁻¹: (f⁻¹ (liftFin _)).1 = n?
      -- f⁻¹ (f (liftFin i)) = liftFin i. Its .1 = i.1, which is < n.
      have h2 : (f⁻¹ (liftFin (⟨(f (liftFin i)).1,
          lt_of_lt_succ_of_neq (f (liftFin i)).2 h1⟩ : Fin n))).1 ≠ n := by
        rw [hl, f_inv_apply_self, liftFin_val]
        omega
      rw [contractFwd_neg f⁻¹ _ h2]
      simp only
      rw [hl, f_inv_apply_self, liftFin_val]
  right_inv := by
    intro i
    apply Fin.ext
    by_cases h1 : (f⁻¹ (liftFin i)).1 = n
    · rw [contractFwd_pos f⁻¹ i h1]
      have hl : liftFin (⟨(f⁻¹ (f⁻¹ (liftFin i))).1,
          perm_perm_val_lt_of_perm_val_eq (f := f⁻¹) h1⟩ : Fin n) = f⁻¹ (f⁻¹ (liftFin i)) :=
        liftFin_of_lt _
      have h2 : (f (liftFin (⟨(f⁻¹ (f⁻¹ (liftFin i))).1,
          perm_perm_val_lt_of_perm_val_eq (f := f⁻¹) h1⟩ : Fin n))).1 = n := by
        rw [hl, f_apply_inv_self]; exact h1
      rw [contractFwd_pos f _ h2]
      simp only
      rw [hl, f_apply_inv_self, f_apply_inv_self]
      rfl
    · rw [contractFwd_neg f⁻¹ i h1]
      have hl : liftFin (⟨(f⁻¹ (liftFin i)).1,
          lt_of_lt_succ_of_neq (f⁻¹ (liftFin i)).2 h1⟩ : Fin n) = f⁻¹ (liftFin i) :=
        liftFin_of_lt _
      have h2 : (f (liftFin (⟨(f⁻¹ (liftFin i)).1,
          lt_of_lt_succ_of_neq (f⁻¹ (liftFin i)).2 h1⟩ : Fin n))).1 ≠ n := by
        rw [hl, f_apply_inv_self, liftFin_val]
        omega
      rw [contractFwd_neg f _ h2]
      simp only
      rw [hl, f_apply_inv_self, liftFin_val]

/-- The forward direction of `permExpand`. -/
private def expandFwd (f : Equiv.Perm (Fin n)) (i : Fin (n + 1)) : Fin (n + 1) :=
  if h : i.1 = n
  then ⟨n, Nat.lt_succ_self n⟩
  else liftFin (f ⟨i.1, lt_of_lt_succ_of_neq i.2 h⟩)

private lemma expandFwd_pos (f : Equiv.Perm (Fin n)) (i : Fin (n + 1)) (h : i.1 = n) :
    expandFwd f i = ⟨n, Nat.lt_succ_self n⟩ := by
  unfold expandFwd; exact dif_pos h

private lemma expandFwd_neg (f : Equiv.Perm (Fin n)) (i : Fin (n + 1)) (h : i.1 ≠ n) :
    expandFwd f i = liftFin (f ⟨i.1, lt_of_lt_succ_of_neq i.2 h⟩) := by
  unfold expandFwd; exact dif_neg h

private lemma f_inv_apply_self' (f : Equiv.Perm (Fin n)) (y : Fin n) : f⁻¹ (f y) = y := by
  rw [← Equiv.Perm.mul_apply, inv_mul_cancel, Equiv.Perm.one_apply]

private lemma f_apply_inv_self' (f : Equiv.Perm (Fin n)) (y : Fin n) : f (f⁻¹ y) = y := by
  rw [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply]

/-- A function that takes a permutation `f` of `Fin n` and returns a permutation of `Fin (n + 1)`
    that behaves exactly the same as `f` on all inputs except on `n`, where it returns `n`. -/
def permExpand (f : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n + 1)) where
  toFun := expandFwd f
  invFun := expandFwd f⁻¹
  left_inv := by
    intro x
    apply Fin.ext
    by_cases h1 : x.1 = n
    · -- x.1 = n
      rw [expandFwd_pos f x h1]
      -- Now compute expandFwd f⁻¹ ⟨n, _⟩
      have h2 : (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)).1 = n := rfl
      rw [expandFwd_pos f⁻¹ _ h2]
      exact h1.symm
    · rw [expandFwd_neg f x h1]
      -- expandFwd f⁻¹ (liftFin (f ⟨x.1, _⟩))
      have h2 : (liftFin (f ⟨x.1, lt_of_lt_succ_of_neq x.2 h1⟩)).1 ≠ n := by
        rw [liftFin_val]
        exact Nat.ne_of_lt (f _).2
      rw [expandFwd_neg f⁻¹ _ h2]
      rw [liftFin_val]
      -- Goal: (f⁻¹ ⟨(liftFin (f _)).1, _⟩).1 = x.1
      -- Use that ⟨(liftFin (f _)).1, _⟩ = f ⟨x.1, _⟩ via Fin.ext
      have he : (⟨(liftFin (f ⟨x.1, lt_of_lt_succ_of_neq x.2 h1⟩)).1,
          lt_of_lt_succ_of_neq (liftFin (f ⟨x.1, lt_of_lt_succ_of_neq x.2 h1⟩)).2 h2⟩ : Fin n)
          = f ⟨x.1, lt_of_lt_succ_of_neq x.2 h1⟩ := Fin.ext rfl
      rw [he, f_inv_apply_self']
  right_inv := by
    intro x
    apply Fin.ext
    by_cases h1 : x.1 = n
    · rw [expandFwd_pos f⁻¹ x h1]
      have h2 : (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)).1 = n := rfl
      rw [expandFwd_pos f _ h2]
      exact h1.symm
    · rw [expandFwd_neg f⁻¹ x h1]
      have h2 : (liftFin (f⁻¹ ⟨x.1, lt_of_lt_succ_of_neq x.2 h1⟩)).1 ≠ n := by
        rw [liftFin_val]
        exact Nat.ne_of_lt (f⁻¹ _).2
      rw [expandFwd_neg f _ h2]
      rw [liftFin_val]
      have he : (⟨(liftFin (f⁻¹ ⟨x.1, lt_of_lt_succ_of_neq x.2 h1⟩)).1,
          lt_of_lt_succ_of_neq (liftFin (f⁻¹ ⟨x.1, lt_of_lt_succ_of_neq x.2 h1⟩)).2 h2⟩ : Fin n)
          = f⁻¹ ⟨x.1, lt_of_lt_succ_of_neq x.2 h1⟩ := Fin.ext rfl
      rw [he, f_apply_inv_self']

end ContractExpand

end LeanPool.PolyaEnumerationTheorem
