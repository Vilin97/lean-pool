/-
Copyright (c) 2026 Math_XMUM. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Math_XMUM
-/
import LeanPool.Brouwer.ScarfPath
import Mathlib.Data.PNat.Basic
import Mathlib.Order.PiLex
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Sequences
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Brouwer's fixed-point theorem on a simplex

This file derives Brouwer's fixed-point theorem for a continuous self-map of the
standard simplex from Scarf's lemma. The combinatorial type `TT n l` of integer
points of the scaled simplex carries an `IndexedLOrder`; applying Scarf's lemma to
finer and finer subdivisions and passing to a convergent subsequence of the
resulting colorful points produces a fixed point.
-/

attribute [local instance] Classical.propDecidable

section
/-- A dependent product of finite, indexed by finite, is a finite. -/
instance Pi.Lex.finite {α : Type*} {β : α → Type*} [Finite α]
    [∀ a, Finite (β a)] : Finite (Πₗ a, β a) :=
        (Equiv.finite_iff toLex).1 Pi.finite

end

noncomputable section
open IndexedLOrder

variable (n l : ℕ+) (i : Fin n)

/-- The combinatorial type of integer points of the `l`-scaled `n`-simplex. -/
abbrev TT := {x : Πₗ (_ : Fin n), Fin (l+1) | ∑ i, (x i : ℕ)  = l}

instance TT.finite : Finite (TT n l) := by
  rw [Set.coe_eq_subtype]
  exact Subtype.finite

instance TT.inhabited : Inhabited (TT n l) where
  default :=
    ⟨ fun i => if i = 0 then Fin.last l else 0,  by
      simp only [TT, Set.mem_setOf_eq]
      rw [Finset.sum_eq_single (0 : Fin n)]
      · simp
      · intro b _ hb; simp [hb]
      · simp [Fin.val_last] ⟩

instance TT.funlike : FunLike (TT n l) (Fin n) (Fin (l+1)) where
  coe := fun a => a.1
  coe_injective' := Subtype.val_injective

variable {n l} in
/-- The point of the standard simplex associated to an integer point of `TT n l`. -/
def TTtostdSimplex (x : TT n l) : stdSimplex ℝ (Fin n) := ⟨fun i => x i / l, by
  rw [stdSimplex]
  constructor
  · intro;simp only[Set.coe_setOf]
    apply div_nonneg <;> simp
  · simp only [Set.coe_setOf];
    rw [<-Finset.sum_div, div_eq_one_iff_eq]
    · exact_mod_cast x.2
    · exact Iff.mpr Nat.cast_ne_zero (PNat.ne_zero l)
  ⟩

instance TT.CoestdSimplex : CoeOut (TT n l) (stdSimplex ℝ (Fin n)) where
  coe := TTtostdSimplex


variable {n l} in
/-- The strict order on `TT n l` at index `i`, comparing the `i`-th coordinate first. -/
abbrev TT.Ilt (x y : TT n l) :=
  toLex (x i, x)  < toLex (y i, y)

instance TT.IST : IsStrictTotalOrder (TT n l) (TT.Ilt i) where
  trichotomous := by
    intro a b h_ab h_ba
    unfold TT.Ilt at h_ab h_ba
    have h_eq :
        toLex (a i, a) = toLex (b i, b) :=
      le_antisymm (le_of_not_gt h_ba) (le_of_not_gt h_ab)
    have h_pair : (a i, a) = (b i, b) :=
      (EquivLike.injective (toLex : (Fin (l + 1) × TT n l) ≃
        Lex (Fin (l + 1) × TT n l))) h_eq
    exact congrArg Prod.snd h_pair
  irrefl := by
    intro a
    unfold TT.Ilt
    exact lt_irrefl _
  trans := by
    intro a b c h_ab h_bc
    unfold TT.Ilt at *
    exact lt_trans h_ab h_bc


variable {n l} in
instance TT.ILO : IndexedLOrder (Fin n) (TT n l) where
  IST := fun i => linearOrderOfSTO (TT.Ilt i)

local notation  lhs "<[" i "]" rhs => IndexedLOrder.ltAt i lhs rhs
local notation  lhs "≤[" i "]" rhs => IndexedLOrder.leAt i lhs rhs

lemma TT.Ilt_def (a b : TT n l) :
  (a <[i] b) ↔ TT.Ilt i a b := by
  rfl

lemma TT.Ilt_keyprop (a b : TT n l) :
  a i < b i → a <[i] b := by
  intro h
  change toLex (a i, a) < toLex (b i, b)
  change Prod.Lex (· < ·) (· < ·) (a i, a) (b i, b)
  exact Prod.Lex.left a b h

lemma size_bound_key (σ : Finset (TT n l)) (C : Finset (Fin n)) (h : TT.ILO.isDominant σ C)
(h2 : σ.Nonempty) :
  l < ∑ k ∈ C, (σ.image (fun x => (x k : ℕ))).min' (h2.image _) + C.card := by
  by_contra h_not
  push Not at h_not
  let m := fun k => (σ.image (fun x => (x k : ℕ))).min' (h2.image _)
  have h_sum_bound : ∑ k ∈ C, m k + C.card ≤ l := h_not
  have h_sum_plus_one : ∑ k ∈ C, (m k + 1) ≤ l := by
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_one]
    exact h_sum_bound
  have h_exists_point : ∃ M : TT n l, ∀ k ∈ C, m k + 1 ≤ M k := by
    let M' : Fin n → ℕ := fun k => if k ∈ C then m k + 1 else 0
    let S := ∑ k, M' k
    have h_S_le_l : S ≤ l := by
      simp [S, M', h_sum_plus_one]
    let R := l - S
    let M_coords : Fin n → ℕ := fun k => if k = (0 : Fin n) then M' 0 + R else M' k
    have h_M_coords_sum : ∑ k, M_coords k = l := by
      have h1 : S = M' 0 + ∑ k ∈ (Finset.univ : Finset (Fin n)).erase 0, M' k := by
        simp only [S]
        rw [← Finset.sum_insert (Finset.notMem_erase 0 Finset.univ)]
        rw [Finset.insert_erase (Finset.mem_univ 0)]
      have : ∑ k, M_coords k = M_coords 0 + ∑ k ∈ (Finset.univ : Finset (Fin n)).erase 0,
          M_coords k := by
        rw [← Finset.sum_insert (Finset.notMem_erase 0 Finset.univ)]
        rw [Finset.insert_erase (Finset.mem_univ 0)]
      rw [this]
      simp only [M_coords, if_true]
      have sum_eq : ∑ x ∈ Finset.univ.erase 0, (if x = 0 then M' 0 + R else M' x)
          = ∑ x ∈ Finset.univ.erase 0, M' x := by
        apply Finset.sum_congr rfl
        intro k hk
        simp only [if_neg (Finset.ne_of_mem_erase hk)]
      rw [sum_eq, add_comm (M' 0) R, add_assoc, ← h1]
      simp only [R]
      have hM'0_le_S : M' 0 ≤ S := by
        have : M' 0 ≤ ∑ k, M' k := Finset.single_le_sum (fun _ _ => Nat.zero_le _)
            (Finset.mem_univ 0)
        exact this
      omega
    have h_M_coords_bound : ∀ k, M_coords k ≤ l := by
      intro k
      by_cases h_is_zero : k = 0
      · simp [h_is_zero, M_coords, R]
        have hM'0_le_S : M' 0 ≤ S := by
          have : M' 0 ≤ ∑ k, M' k := Finset.single_le_sum (fun _ _ => Nat.zero_le _)
              (Finset.mem_univ 0)
          exact this
        omega
      · simp only [h_is_zero, ↓reduceIte, M_coords]
        by_cases hk_in_C : k ∈ C
        · simp only [hk_in_C, ↓reduceIte, Order.add_one_le_iff, M'];
            exact Nat.le_trans (Finset.single_le_sum (fun k _ => Nat.zero_le (m k + 1)) hk_in_C)
            h_sum_plus_one
        · simp [M', hk_in_C]
    let M_val : Fin n → Fin (l + 1) := fun k => ⟨M_coords k, Nat.lt_succ_of_le (h_M_coords_bound k)⟩
    use ⟨M_val, by simp [M_val, h_M_coords_sum]⟩
    intro k hk_in_C
    change m k + 1 ≤ (M_val k : ℕ)
    by_cases h_is_zero : k = 0
    · rw [h_is_zero] at hk_in_C ⊢
      simp [M_val, M_coords, M', hk_in_C]
    · simp [M_val, M_coords, h_is_zero, M', hk_in_C]
  obtain ⟨M, hM⟩ := h_exists_point
  have h_min_less : ∀ k ∈ C, ∃ x_min ∈ σ, ∀ x ∈ σ, x_min ≤[k] x := by
    intro k _
    letI : LinearOrder (TT n l) := IndexedLOrder.IST k
    let x_min := σ.min' h2
    use x_min
    constructor
    · exact Finset.min'_mem σ h2
    · intro x hx
      exact Finset.min'_le σ x hx
  have h_contradiction : ∀ k ∈ C, ∃ x_min ∈ σ, x_min <[k] M := by
    intro k hk_in_C
    letI : LinearOrder (TT n l) := IndexedLOrder.IST k
    let x_min := σ.min' h2
    use x_min
    constructor
    · exact Finset.min'_mem σ h2
    · apply TT.Ilt_keyprop
      have h_min_coord : (x_min k : ℕ) = (σ.image (fun x => (x k : ℕ))).min' (h2.image _) := by
        symm
        apply le_antisymm
        · apply Finset.min'_le
          apply Finset.mem_image_of_mem
          exact Finset.min'_mem σ h2
        · apply Finset.le_min'
          intro y hy
          rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
          have h_x_min_le_x : x_min ≤[k] x := Finset.min'_le σ x hx
          by_cases h_case : (x_min k : ℕ) ≤ (x k : ℕ)
          · exact h_case
          · exfalso
            push Not at h_case
            have h_x_lt_min : x <[k] x_min := by
              apply TT.Ilt_keyprop
              exact h_case
            exact not_lt.mpr h_x_min_le_x h_x_lt_min
      have h_nat_lt : (x_min k : ℕ) < (M k : ℕ) := by
        rw [h_min_coord]
        exact Nat.lt_of_succ_le (hM k hk_in_C)
      exact h_nat_lt
  have h_not_dominant : ¬ TT.ILO.isDominant σ C := by
    intro h_dom
    rcases h_dom M with ⟨k, hk, h_all⟩
    rcases h_contradiction k hk with ⟨x, hx, hlt⟩
    letI : LinearOrder (TT n l) := IndexedLOrder.IST k
    exact not_lt.mpr (h_all x hx) hlt
  exact h_not_dominant h



theorem size_bound_in (σ : Finset (TT n l)) (C : Finset (Fin n)) (h : TT.ILO.isDominant σ C) :
    ∀ x ∈ σ, ∀ y ∈ σ, ∀ i : Fin n, abs ((x i : ℤ) - (y i : ℤ)) < 2 * (n + 1)
    := by
  by_cases hσ : σ.Nonempty
  · intro x hx y hy i
    let m k := (σ.image (fun z => (z k : ℕ))).min' (hσ.image _)
    let m' i := if h_i : i ∈ C then m i else 0
    have h_le_l_sub_sum : (l : ℕ) - ∑ k ∈ C, m k < C.card := by
      have h_key : l < ∑ k ∈ C, m k + C.card := size_bound_key n l σ C h hσ
      have h_sum_le_l : ∑ k ∈ C, m k ≤ l := by
        rcases hσ with ⟨x, hx⟩
        have h_m_le : ∀ k ∈ C, m k ≤ (x k : ℕ) := fun k _ =>
          Finset.min'_le (σ.image (fun z => (z k : ℕ))) (x k : ℕ)
              (Finset.mem_image_of_mem (fun z => (z k : ℕ)) hx)
        calc
          ∑ k ∈ C, m k ≤ ∑ k ∈ C, (x k : ℕ) := Finset.sum_le_sum h_m_le
          _ ≤ ∑ k, (x k : ℕ) := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ C)
              (by simp)
          _ = l := x.2
      rw [Nat.sub_lt_iff_lt_add h_sum_le_l, add_comm]
      exact h_key
    have h_bound : ∀ z ∈ σ, (z i : ℕ) - m' i < C.card := by
      intro z hz
      by_cases hi_in_C : i ∈ C
      · simp only [Set.coe_setOf, dite_eq_ite, hi_in_C, ↓reduceIte, m']
        have h_mi_le_zi : m i ≤ (z i : ℕ) := by
          apply Finset.min'_le
          apply Finset.mem_image_of_mem
          exact hz
        have h_zi_le_sum : (z i : ℕ) ≤ ∑ k ∈ C, (z k : ℕ) :=
          Finset.single_le_sum (fun k _ => Nat.zero_le (z k : ℕ)) hi_in_C
        have h_sum_z_le_l : ∑ k ∈ C, (z k : ℕ) ≤ l := by
          calc ∑ k ∈ C, (z k : ℕ) ≤ ∑ k, (z k : ℕ) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ C) (by simp)
          _ = l := z.2
        have h_diff_bound : (z i : ℕ) - m i ≤ l - ∑ k ∈ C, m k := by
          calc
          (z i : ℕ) - m i ≤ ∑ k ∈ C, ((z k : ℕ) - m k) :=
            Finset.single_le_sum (fun k _ => Nat.zero_le ((z k : ℕ) - m k)) hi_in_C
          _ = (∑ k ∈ C, (z k : ℕ)) - (∑ k ∈ C, m k) := by
            rw [Finset.sum_tsub_distrib]
            intro k hk
            apply Finset.min'_le
            apply Finset.mem_image_of_mem
            exact hz
          _ ≤ l - ∑ k ∈ C, m k := by
            apply Nat.sub_le_sub_right
            calc
              ∑ k ∈ C, (z k : ℕ) ≤ ∑ k, (z k : ℕ)
                  := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ C) (by simp)
              _ = l := z.2
        exact lt_of_le_of_lt h_diff_bound h_le_l_sub_sum
      · simp only [Set.coe_setOf, dite_eq_ite, hi_in_C, ↓reduceIte, tsub_zero, m']
        have h_sum_le : (z i : ℕ) + ∑ k ∈ C, (z k : ℕ) ≤ l := by
          calc
            (z i : ℕ) + ∑ k ∈ C, (z k : ℕ) = ∑ k ∈ insert i C, (z k : ℕ) := by
              rw [Finset.sum_insert hi_in_C]
            _ ≤ ∑ k, (z k : ℕ) := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
                (by simp)
            _ = l := z.2
        have h_le_sub : (z i : ℕ) ≤ l - ∑ k ∈ C, (z k : ℕ) := Nat.le_sub_of_add_le h_sum_le
        have h_m_le_z : ∑ k ∈ C, m k ≤ ∑ k ∈ C, (z k : ℕ) := by
          apply Finset.sum_le_sum
          intro k hk
          apply Finset.min'_le
          apply Finset.mem_image_of_mem
          exact hz
        have h_sub_le_sub : l - ∑ k ∈ C, (z k : ℕ) ≤ l - ∑ k ∈ C, m k :=
          Nat.sub_le_sub_left h_m_le_z l
        exact lt_of_le_of_lt (h_le_sub.trans h_sub_le_sub) h_le_l_sub_sum
    have h_nonneg : ∀ z ∈ σ, 0 ≤ (z i : ℤ) - (m' i : ℤ) := by
      intro z hz
      by_cases hi_in_C : i ∈ C
      · simp only [Set.coe_setOf, dite_eq_ite, hi_in_C, ↓reduceIte, Int.sub_nonneg, Nat.cast_le, m']
        have h_min_le : m i ≤ ↑(z i) := by
          apply Finset.min'_le
          apply Finset.mem_image_of_mem
          exact hz
        exact_mod_cast h_min_le
      · simp [m', hi_in_C]
    have h_abs_lt_2_card : abs ((x i : ℤ) - (y i : ℤ)) < 2 * (C.card : ℤ) := by
      have h_bound_int : ∀ z ∈ σ, (z i : ℤ) - (m' i : ℤ) < C.card := by
        intro z hz
        have := h_bound z hz
        simp only [m'] at this ⊢
        split_ifs at this ⊢ with h_case
        · have : (z i : ℕ) - m i < C.card := this
          simp
          have h_le : m i ≤ (z i : ℕ) := by
            apply Finset.min'_le
            apply Finset.mem_image_of_mem
            exact hz
          omega
        · simp only [Int.ofNat_zero, sub_zero]
          exact Int.ofNat_lt.mpr this
      calc
        abs ((x i : ℤ) - (y i : ℤ)) = abs (((x i : ℤ) - (m' i : ℤ)) - ((y i : ℤ) - (m' i : ℤ)))
            := by rw [sub_sub_sub_cancel_right]
        _ ≤ abs ((x i : ℤ) - (m' i : ℤ)) + abs ((y i : ℤ) - (m' i : ℤ)) := abs_sub _ _
        _ = ((x i : ℤ) - (m' i : ℤ)) + ((y i : ℤ) - (m' i : ℤ)) := by
          rw [abs_of_nonneg (h_nonneg x hx), abs_of_nonneg (h_nonneg y hy)]
        _ < (C.card : ℤ) + (C.card : ℤ) := by
          apply add_lt_add (h_bound_int x hx) (h_bound_int y hy)
        _ = 2 * (C.card : ℤ) := by rw [two_mul]
    have h_card_le_n : C.card ≤ n :=
      calc
        C.card ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_card (Finset.subset_univ C)
        _ = n := by simp
    apply lt_trans h_abs_lt_2_card
    have : (2 * (C.card : ℤ)) < 2 * (n + 1 : ℤ) := by
      linarith [Int.ofNat_le.mpr h_card_le_n]
    exact this
  · intro x hx y hy i
    exfalso
    exact hσ ⟨x, hx⟩

theorem size_bound_out (σ : Finset (TT n l)) (C : Finset (Fin n)) (h : TT.ILO.isDominant σ C) :
    ∀ x ∈ σ, ∀ i ∉ C, (x i : ℤ) < n + 1
    := by
  by_cases hσ : σ.Nonempty
  · intro x hx i hi_not_C
    let m k := (σ.image (fun z => (z k : ℕ))).min' (hσ.image _)
    have h_le_l_sub_sum : l - ∑ k ∈ C, m k < C.card := by
      have h_sum_le_l : ∑ k ∈ C, m k ≤ l := by
        rcases hσ with ⟨x, hx⟩
        have h_m_le : ∀ k ∈ C, m k ≤ (x k : ℕ) := fun k _ =>
          Finset.min'_le (σ.image (fun z => (z k : ℕ))) (x k : ℕ)
              (Finset.mem_image_of_mem (fun z => (z k : ℕ)) hx)
        calc
          ∑ k ∈ C, m k ≤ ∑ k ∈ C, (x k : ℕ) := Finset.sum_le_sum h_m_le
          _ ≤ ∑ k, (x k : ℕ) := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ C)
              (by simp)
          _ = l := x.2
      rw [Nat.sub_lt_iff_lt_add h_sum_le_l, add_comm]
      exact size_bound_key n l σ C h hσ
    have h_bound : (x i : ℕ) < C.card := by
      have h_sum_le : (x i : ℕ) + ∑ k ∈ C, (x k : ℕ) ≤ l := by
        calc
          (x i : ℕ) + ∑ k ∈ C, (x k : ℕ) = ∑ k ∈ insert i C, (x k : ℕ) := by
            rw [Finset.sum_insert hi_not_C]
          _ ≤ ∑ k, (x k : ℕ) := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (by simp)
          _ = l := x.2
      have h_le_sub : (x i : ℕ) ≤ l - ∑ k ∈ C, (x k : ℕ) := Nat.le_sub_of_add_le h_sum_le
      have h_m_le_x : ∑ k ∈ C, m k ≤ ∑ k ∈ C, (x k : ℕ) := by
        apply Finset.sum_le_sum
        intro k _
        apply Finset.min'_le
        apply Finset.mem_image_of_mem
        exact hx
      have h_sub_le_sub : l - ∑ k ∈ C, (x k : ℕ) ≤ l - ∑ k ∈ C, m k :=
        Nat.sub_le_sub_left h_m_le_x l
      exact lt_of_le_of_lt (h_le_sub.trans h_sub_le_sub) h_le_l_sub_sum
    have h_card_le_n : C.card ≤ n := by
      calc
        C.card ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_card (Finset.subset_univ C)
        _ = n := by simp [Fintype.card_fin]
    have h_lt_n : (x i : ℤ) < ↑n := by
      apply lt_of_lt_of_le
      · exact Int.ofNat_lt.mpr h_bound
      · exact Int.ofNat_le.mpr h_card_le_n
    linarith
  · intro x hx
    exfalso
    exact hσ ⟨x, hx⟩

section Brouwer

--instance stdSimplex.cpt : CompactSpace ↑(stdSimplex ℝ (Fin n)) := inferInstance

variable (f : stdSimplex ℝ (Fin n) → stdSimplex ℝ (Fin n))

variable {n l}

instance stdSimplex.upidx (x y : stdSimplex ℝ (Fin n)) : Nonempty { i | x.1 i ≤ y.1 i} := by
  by_contra h
  push Not at h
  have sum_x_eq_1 := x.2.2
  have sum_y_eq_1 := y.2.2
  have sum_lt : Finset.sum Finset.univ y.1 < Finset.sum Finset.univ x.1 := by
    apply Finset.sum_lt_sum_of_nonempty
    · exact Finset.univ_nonempty
    · intro i _
      have : ¬ (x.1 i ≤ y.1 i) := by
        intro hle
        exact @IsEmpty.false _ h ⟨i, hle⟩
      exact lt_of_not_ge this
  rw [sum_y_eq_1, sum_x_eq_1] at sum_lt
  exact (lt_irrefl 1 sum_lt).elim


/-- A chosen index where `x` does not exceed `y`, for two simplex points. -/
noncomputable def stdSimplex.pick (x y : stdSimplex ℝ (Fin n))
    := Classical.choice <| stdSimplex.upidx x y



/-- The Scarf coloring induced on `TT n l` by a self-map `f` of the simplex. -/
def Fcolor (x : TT n l) : Fin n := stdSimplex.pick x (f x)

/-- A colorful room produced by Scarf lemma for the `l-th` subdivision. -/
def roomSeq (l' : ℕ) :=
  let l : PNat := ⟨l'+1,Nat.zero_lt_succ _⟩
  Classical.choice (TT.ILO.Scarf (@Fcolor n l f)).to_subtype

/-- A point of the colorful room `roomSeq`, as an integer point of `TT`. -/
def roomPointSeq (l' : ℕ) : TT n ⟨l' + 1, Nat.zero_lt_succ _⟩ :=
  (pickColorfulPoint (Finset.mem_filter.1 (roomSeq f l').2).2).1



section finiteness

-- Define subsequence function
/-- The subsequence of indices generated by iterating a step function. -/
def mkSubseq (f : ℕ → ℕ) (h : ∀ n, n < f n) : ℕ → ℕ
  | 0 => f 0
  | n+1 => f (mkSubseq f h n)

theorem exists_subseq_constant_of_finite_image {s : Finset α} (e : ℕ → α) (he : ∀ n, e n ∈ s) :
  ∃ a ∈ s, ∃ g : ℕ ↪o ℕ,  (∀ n, e (g n) = a) := by
  have range_subset : Set.range e ⊆ (s : Set α) := Set.range_subset_iff.mpr he
  have range_finite : (Set.range e).Finite := (Finset.finite_toSet s).subset range_subset
  let imgs : Finset α := Finset.filter (fun a => ¬(Set.Finite (e ⁻¹' {a}))) s
  have imgs_nonempty : imgs.Nonempty := by
    by_contra h
    simp only [Finset.not_nonempty_iff_eq_empty] at h
    have preimages_all_finite : ∀ a ∈ s, Set.Finite (e ⁻¹' {a}) := by
      intro a ha
      by_contra hnf
      have a_in_imgs : a ∈ imgs := by
        simp only [Set.not_finite, Finset.mem_filter, ha, true_and, imgs]
        exact hnf
      have : imgs ≠ ∅ := Finset.ne_empty_of_mem a_in_imgs
      contradiction
    have nat_finite : Set.Finite (Set.univ : Set ℕ) := by
      have univ_eq : Set.univ = e ⁻¹' (s : Set α) := by ext n; simp [he]
      rw [univ_eq]
      have : e ⁻¹' (s : Set α) = ⋃ a ∈ s, e ⁻¹' {a} := by
        ext n; simp [ Set.mem_preimage]
      rw [this]
      exact Set.Finite.biUnion s.finite_toSet preimages_all_finite
    exact Set.infinite_univ nat_finite
  obtain ⟨a, a_in_imgs⟩ := imgs_nonempty
  have a_in_s : a ∈ s := (Finset.mem_filter.1 a_in_imgs).1
  have a_infinite_preimage : ¬Set.Finite (e ⁻¹' {a}) := (Finset.mem_filter.1 a_in_imgs).2
  use a, a_in_s
  let preimage := e ⁻¹' {a}
  have preimage_infinite : Set.Infinite preimage := a_infinite_preimage
  have h_nonempty : preimage.Nonempty := by
    by_contra h_empty
    rw [Set.not_nonempty_iff_eq_empty] at h_empty
    rw [h_empty] at preimage_infinite
    exact Set.finite_empty.not_infinite preimage_infinite
  obtain ⟨m₀, hm₀⟩ := h_nonempty
  have h_exists_larger : ∀ k : ℕ, ∃ m ∈ preimage, k < m := by
    intro k
    by_contra h_not
    push Not at h_not
    have : preimage ⊆ {n | n ≤ k} := fun n hn => h_not n hn
    have h_finite : Set.Finite preimage := (Set.finite_le_nat k).subset this
    exact preimage_infinite h_finite
  choose f hf using h_exists_larger
  have f_lt : ∀ n : ℕ, n < f n := fun n => (hf n).2
  have f_in : ∀ n : ℕ, f n ∈ preimage := fun n => (hf n).1
  let g := mkSubseq f f_lt
  have hg_in : ∀ n, g n ∈ preimage := by
    intro n
    induction n with
    | zero => simpa only [g, mkSubseq] using f_in 0
    | succ n ih => simpa only [g, mkSubseq] using f_in (g n)
  have hg_strict : StrictMono g := by
    intro m n hmn
    induction hmn with
    | refl =>
      simp only [g, mkSubseq]
      exact f_lt (g m)
    | step hmn ih =>
      rename_i n
      simp only [g, mkSubseq]
      exact lt_trans ih (f_lt (g n))
  use OrderEmbedding.ofStrictMono g hg_strict
  intro n
  exact hg_in n

end finiteness

lemma constant_index_set_nonempty : Nonempty {(a, g) :(Finset (Fin n)) × (ℕ ↪o ℕ) | ∀ l',
    (roomSeq f (g l')).1.2 = a } := by
  obtain ⟨a, ha,g,hg⟩ := exists_subseq_constant_of_finite_image (s := Finset.univ)
    (fun x => (roomSeq f x).1.2) (by simp)
  use ⟨a,g⟩; simp [hg]


/- roomSeq ∘ gpkg.1.2 has constant value equal to gpkg.1.1-/
/-- A constant-index colorful subsequence package extracted from `roomSeq`. -/
def gpkg :=  Classical.choice <| constant_index_set_nonempty f

/-- The index subsequence selected by `gpkg`. -/
abbrev g1 := gpkg f |>.1.2


open Topology
open Filter

/- roomSeq ∘ g1 ∘ hpkg.1.2 converge to a point in stdSimplex-/

lemma dominant_coords_tend_to_zero (f : stdSimplex ℝ (Fin n) → stdSimplex ℝ (Fin n))
    (C : Finset (Fin n)) (g : ℕ ↪o ℕ) (h_const : ∀ l', (roomSeq f (g l')).1.2 = C) :
  ∀ i ∉ C, Filter.Tendsto (fun l' => ((roomPointSeq f (g l')) : stdSimplex ℝ (Fin n)).1 i)
      Filter.atTop (𝓝 0) := by
  intro i hiC
  have h_tendsto_bound : Filter.Tendsto (fun l' => ((n : ℝ) + 1) / ((g l' : ℝ) + 1))
      Filter.atTop (𝓝 0) := by
    have h_denom_tendsto : Filter.Tendsto (fun l' => (g l' : ℝ) + 1) Filter.atTop Filter.atTop := by
      have g_tendsto : Filter.Tendsto (fun l' => g l') Filter.atTop Filter.atTop := by
        apply Filter.tendsto_atTop_atTop.mpr
        intro b
        use b
        intro l' hl'
        exact le_trans hl' (StrictMono.id_le g.strictMono l')
      have cast_tendsto : Filter.Tendsto (fun l' => (g l' : ℝ)) Filter.atTop Filter.atTop :=
        Filter.Tendsto.comp tendsto_natCast_atTop_atTop g_tendsto
      exact Tendsto.atTop_add cast_tendsto (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ))
          atTop (𝓝 1))
    have : Tendsto (fun l' => ((n : ℝ) + 1) / ((g l' : ℝ) + 1)) atTop (𝓝 0) :=
      Tendsto.div_atTop tendsto_const_nhds h_denom_tendsto
    exact this
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 :
      ℝ)) atTop (𝓝 0)) h_tendsto_bound
  · intro l'
    exact ((roomPointSeq f (g l')) : stdSimplex ℝ (Fin n)).2.1 i
  · intro l'
    let l_pnat : PNat := ⟨g l' + 1, Nat.succ_pos _⟩
    let rs := roomSeq f (g l')
    let σ := rs.1.1
    let C_l := rs.1.2
    have h_C_l : C_l = C := h_const l'
    have hiC_l : i ∉ C_l := h_C_l ▸ hiC
    let x := roomPointSeq f (g l')
    let colorful_proof := (Finset.mem_filter.mp rs.2).2
    have hx_mem : x ∈ σ := (pickColorfulPoint colorful_proof).2
    have h_dom : TT.ILO.isDominant σ C_l := colorful_proof.1
    have h_bound := size_bound_out n l_pnat σ C_l h_dom x hx_mem i hiC_l
    simp only [TTtostdSimplex, Subtype.coe_mk]
    have h_eq : (↑l_pnat : ℝ) = ↑(g l') + 1 := by simp [l_pnat, PNat.mk_coe]
    rw [h_eq]
    rw [div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < ↑(g l') + 1)]
    have h_bound_real : ((x i : ℕ) : ℝ) < (↑n + 1 : ℝ) := by
      exact_mod_cast Nat.lt_succ_of_le (Int.ofNat_le.mp (Int.le_of_lt_add_one h_bound))
    exact le_of_lt h_bound_real

lemma hpkgAux :
  Nonempty {(z , h) : (stdSimplex ℝ  (Fin n)) × (ℕ → ℕ) | StrictMono h ∧ Filter.Tendsto
    ((fun l' => (roomPointSeq f (g1 f l'): stdSimplex ℝ (Fin n))) ∘ h)
    Filter.atTop (𝓝 z) } := by
  let u := fun l' : ℕ => (roomPointSeq f (g1 f l') : stdSimplex ℝ (Fin n))
  have h_compact : IsCompact (Set.univ : Set (stdSimplex ℝ (Fin n))) := isCompact_univ
  have h_in_univ : ∀ n, u n ∈ Set.univ := fun _ => Set.mem_univ _
  obtain ⟨z, hz, φ, φ_mono, h_tendsto⟩ := h_compact.tendsto_subseq h_in_univ
  use ⟨z, φ⟩
  exact ⟨φ_mono, h_tendsto⟩

/-- A convergent colorful subsequence package, with its limit point. -/
def hpkg := Classical.choice  (hpkgAux f)

/-
Use
-- StrictMono.id_le : ∀ {φ : ℕ → ℕ}, StrictMono φ → ∀ (n : ℕ), n ≤ φ n
-- OrderEmbedding.strictMono: (f : α ↪o β), StrictMono ⇑f
-/

theorem tendsto_diam_to_zero (f : stdSimplex ℝ (Fin n) → stdSimplex ℝ (Fin n)) :
  Tendsto
    (fun k =>
      Metric.diam
        ((((roomSeq f (g1 f ((hpkg f).1.2 k))).1.1.image (fun x => TTtostdSimplex x)) :
          Set (stdSimplex ℝ (Fin n)))))
    atTop (𝓝 0) := by
  let l k := g1 f ((hpkg f).1.2 k)
  let σ k := (roomSeq f (l k)).1.1
  let projected_σ k := (σ k).image (fun x => TTtostdSimplex x)
  have h_diam_bounded : ∃ (C : ℝ), ∀ k, Metric.diam ((projected_σ k : Set (stdSimplex ℝ (Fin n))))
      ≤ C / (l k + 1) := by
    use 2 * Real.sqrt (n : ℝ) * ((n : ℝ) + 1)
    intro k
    let l_pnat : PNat := ⟨l k + 1, Nat.succ_pos _⟩
    let rs := roomSeq f (l k)
    let C_k := rs.1.2
    have h_dom : TT.ILO.isDominant (σ k) C_k := (Finset.mem_filter.mp rs.2).2.1
    have h_coord_bound : ∀ x ∈ (σ k), ∀ y ∈ (σ k), ∀ i : Fin n,
        abs (((TTtostdSimplex x).1 i : ℝ) - ((TTtostdSimplex y).1 i : ℝ)) < 2 * ((n : ℝ) + 1)
            / (l k + 1) := by
      intro x hx y hy i
      have h_bound_int := size_bound_in n l_pnat (σ k) C_k h_dom x hx y hy i
      simp only [TTtostdSimplex]
      rw [← sub_div]
      rw [abs_div]
      have h_pos : (0 : ℝ) < l_pnat := by positivity
      rw [abs_of_pos h_pos]
      have h_eq : (l_pnat : ℝ) = l k + 1 := by simp [l_pnat, PNat.mk_coe]
      rw [h_eq]
      rw [div_lt_div_iff_of_pos_right (by positivity : (0 : ℝ) < l k + 1)]
      exact_mod_cast h_bound_int
    have h_dist_bound : ∀ x ∈ (σ k), ∀ y ∈ (σ k),
        dist (TTtostdSimplex x) (TTtostdSimplex y) ≤ 2 * Real.sqrt (n : ℝ) * ((n : ℝ) + 1)
            / (l k + 1) := by
      intro x hx y hy
      have h_coord_diff_le : ∀ i, |(TTtostdSimplex x).1 i - (TTtostdSimplex y).1 i| ≤ 2 * (↑n + 1)
          / (↑(l k) + 1) :=
        fun i => le_of_lt (h_coord_bound x hx y hy i)
      calc dist (TTtostdSimplex x) (TTtostdSimplex y)
        = ‖(TTtostdSimplex x).1 - (TTtostdSimplex y).1‖ := rfl
      _ ≤ 2 * (↑n + 1) / (l k + 1) := by
          rw [pi_norm_le_iff_of_nonneg (by positivity)]
          exact h_coord_diff_le
      _ ≤ 2 * Real.sqrt (n : ℝ) * ((n : ℝ) + 1) / (l k + 1) := by
          rw [div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < l k + 1)]
          have hsqrt : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
            apply Real.one_le_sqrt.mpr
            norm_cast
            exact Nat.succ_le_of_lt n.2
          calc
            2 * ((n : ℝ) + 1) = 1 * (2 * ((n : ℝ) + 1)) := by ring
            _ ≤ Real.sqrt (n : ℝ) * (2 * ((n : ℝ) + 1)) :=
              mul_le_mul_of_nonneg_right hsqrt (by positivity)
            _ = 2 * Real.sqrt (n : ℝ) * ((n : ℝ) + 1) := by ring
    apply Metric.diam_le_of_forall_dist_le (by positivity)
    intro x hx y hy
    rcases Finset.mem_image.mp hx with ⟨x', hx', rfl⟩
    rcases Finset.mem_image.mp hy with ⟨y', hy', rfl⟩
    exact h_dist_bound x' hx' y' hy'
  rcases h_diam_bounded with ⟨C, hC_bound⟩
  have h_l_tends_to_inf : Tendsto (fun k => (l k : ℝ) + 1) atTop atTop := by
    have h_l_mono : StrictMono l := (g1 f).strictMono.comp (hpkg f).2.1
    have h_l_tends_nat : Tendsto l atTop atTop := h_l_mono.tendsto_atTop
    have h_l_tends_real : Tendsto (fun k => (l k : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp h_l_tends_nat
    exact Tendsto.atTop_add h_l_tends_real tendsto_const_nhds
  have h_C_div_l_tends_to_zero : Tendsto (fun k => C / (l k + 1)) atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop h_l_tends_to_inf
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le (tendsto_const_nhds : Tendsto (fun _ => (0:ℝ))
      atTop (𝓝 0)) h_C_div_l_tends_to_zero (fun _ => Metric.diam_nonneg) hC_bound

theorem f_coords_ge_z_coords (f : stdSimplex ℝ (Fin n) → stdSimplex ℝ (Fin n)) (hf : Continuous f) :
  ∀ i ∈ (gpkg f).1.1, (f (hpkg f).1.1).1 i ≥ ((hpkg f).1.1).1 i := by
      let z := (hpkg f).1.1
      let C := (gpkg f).1.1
      let φ := (hpkg f).1.2
      have convergence_to_z : Filter.Tendsto ((fun l' => (roomPointSeq f (g1 f l'): stdSimplex ℝ
          (Fin n))) ∘ φ) Filter.atTop (𝓝 z) := by
        exact (hpkg f).2.2
      have constant_color_set : ∀ l', (roomSeq f (g1 f l')).1.2 = C := by
        exact (gpkg f).2
      intro idx h_idx_C
      have h_exists_point : ∀ l', ∃ y,
        y ∈ (roomSeq f (g1 f l')).1.1 ∧
        (let l_pnat : PNat := ⟨(g1 f) l' + 1, by simp⟩; @Fcolor n l_pnat f y) = idx := by
        intro l'
        let l_pnat : PNat := ⟨(g1 f) l' + 1, by simp⟩
        let rs := roomSeq f (g1 f l')
        let σ := rs.1.1
        let C_l := rs.1.2
        have h_C_l : C_l = C := constant_color_set l'
        let colorful_proof := (Finset.mem_filter.mp rs.2).2
        have h_image_eq : σ.image (@Fcolor n l_pnat f) = C_l := colorful_proof.2
        have h_idx_in_C_l : idx ∈ C_l := h_C_l ▸ h_idx_C
        have h_idx_in_image : idx ∈ σ.image (@Fcolor n l_pnat f) := by
          rw [h_image_eq]; exact h_idx_in_C_l
        rw [Finset.mem_image] at h_idx_in_image
        obtain ⟨y, hy_in_σ, hy_color⟩ := h_idx_in_image
        use y
      let y_seq := fun l' => TTtostdSimplex (h_exists_point l').choose
      have y_seq_spec : ∀ l',
        (h_exists_point l').choose ∈ (roomSeq f (g1 f l')).1.1 ∧
        (let l_pnat : PNat := ⟨(g1 f) l' + 1, by simp⟩;
            @Fcolor n l_pnat f (h_exists_point l').choose) = idx := by
        intro l'
        exact (h_exists_point l').choose_spec
      have h_ineq : ∀ l', (f (y_seq l')).1 idx ≥ (y_seq l').1 idx := by
        intro l'
        have h_spec := y_seq_spec l'
        simp only [PNat.mk_coe, ge_iff_le, y_seq] at h_spec ⊢
        let chosen_point := (h_exists_point l').choose
        have h_color : (let l_pnat : PNat := ⟨(g1 f) l' + 1, by simp⟩;
            @Fcolor n l_pnat f chosen_point) = idx := h_spec.2
        let l_pnat : PNat := ⟨(g1 f) l' + 1, by simp⟩
        unfold Fcolor at h_color
        have h_pick_property : ∃ h : Nonempty {i | (chosen_point : stdSimplex ℝ (Fin n)).1 i ≤ (f
            (chosen_point : stdSimplex ℝ (Fin n))).1 i},
          @Classical.choice _ h = idx := by
          rw [← h_color]
          use stdSimplex.upidx (chosen_point : stdSimplex ℝ (Fin n))
              (f (chosen_point : stdSimplex ℝ (Fin n)))
          rfl
        obtain ⟨h_nonempty, h_choice_eq⟩ := h_pick_property
        have h_mem : idx ∈ {i | (chosen_point : stdSimplex ℝ (Fin n)).1 i ≤ (f (chosen_point :
            stdSimplex ℝ (Fin n))).1 i} := by
          let choice_prop := Classical.choice h_nonempty
          have : idx = choice_prop.val := h_choice_eq.symm
          rw [this]
          exact choice_prop.property
        exact h_mem
      have y_seq_φ_converges_to_z : Filter.Tendsto (y_seq ∘ φ) Filter.atTop (𝓝 z) := by
        have h_dist_tends_to_zero : Filter.Tendsto (fun k => dist (y_seq (φ k))
            ((fun l' => (roomPointSeq f (g1 f l') : stdSimplex ℝ (Fin n))) (φ k)))
            Filter.atTop (𝓝 0) := by
          have h_bound : ∀ k, dist (y_seq (φ k)) ((roomPointSeq f (g1 f (φ k))
              : stdSimplex ℝ (Fin n))) ≤
                Metric.diam ((((roomSeq f (g1 f (φ k))).1.1.image (fun x => TTtostdSimplex x))
                    : Set (stdSimplex ℝ (Fin n)))) := by
            intro k
            apply Metric.dist_le_diam_of_mem
            · exact Set.Finite.isBounded (Finset.finite_toSet _)
            · exact Finset.mem_image_of_mem TTtostdSimplex (y_seq_spec (φ k)).1
            · exact Finset.mem_image_of_mem TTtostdSimplex (pickColorfulPoint
                ((Finset.mem_filter.1 (roomSeq f (g1 f (φ k))).2).2)).2
          have h_diam_tendsto : Tendsto (fun k => Metric.diam ((((roomSeq f (g1 f (φ
              k))).1.1.image TTtostdSimplex) : Set (stdSimplex ℝ (Fin n))))) atTop (𝓝 0) := by
            exact tendsto_diam_to_zero f
          exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_diam_tendsto
            (Eventually.of_forall (fun _ => dist_nonneg)) (Eventually.of_forall h_bound)
        rw [Metric.tendsto_nhds]
        intro ε hε
        have h1 := (Metric.tendsto_nhds.1 convergence_to_z) (ε / 2) (half_pos hε)
        have h2 := (Metric.tendsto_nhds.1 h_dist_tends_to_zero) (ε / 2) (half_pos hε)
        apply (h1.and h2).mono
        intro k ⟨hk1, hk2⟩
        calc dist (y_seq (φ k)) z
          ≤ dist (y_seq (φ k)) ((roomPointSeq f (g1 f (φ k)) : stdSimplex ℝ (Fin n)))
            + dist ((roomPointSeq f (g1 f (φ k)) : stdSimplex ℝ (Fin n))) z := dist_triangle _ _ _
        _ < ε / 2 + ε / 2 :=
          add_lt_add
            (by simp only [dist_zero_right, Real.norm_eq_abs, abs_dist] at hk2; exact hk2) hk1
        _ = ε := add_halves ε
      have f_y_seq_φ_converges_to_f_z : Filter.Tendsto (f ∘ y_seq ∘ φ) Filter.atTop (𝓝 (f z)) := by
        exact hf.continuousAt.tendsto.comp y_seq_φ_converges_to_z
      have f_y_seq_φ_coord_converges : Filter.Tendsto (fun l' => (f (y_seq (φ l'))).1 idx)
          Filter.atTop (𝓝 ((f z).1 idx)) := by
        have h_continuous : Continuous (fun x : stdSimplex ℝ (Fin n) => x.1 idx) :=
          Continuous.comp (continuous_apply idx) continuous_subtype_val
        exact h_continuous.continuousAt.tendsto.comp f_y_seq_φ_converges_to_f_z
      have y_seq_φ_coord_converges : Filter.Tendsto (fun l' => (y_seq (φ l')).1 idx)
          Filter.atTop (𝓝 (z.1 idx)) := by
        have h_continuous : Continuous (fun x : stdSimplex ℝ (Fin n) => x.1 idx) :=
          Continuous.comp (continuous_apply idx) continuous_subtype_val
        exact h_continuous.continuousAt.tendsto.comp y_seq_φ_converges_to_z
      exact le_of_tendsto_of_tendsto y_seq_φ_coord_converges f_y_seq_φ_coord_converges
          (Eventually.of_forall (fun l' => h_ineq (φ l')))

theorem Brouwer (hf : Continuous f) : ∃ x , f x = x := by
  let z := (hpkg f).1.1
  let C := (gpkg f).1.1
  let φ := (hpkg f).1.2
  use z
  have tendsto_diam_to_zero := tendsto_diam_to_zero f
  have convergence_to_z : Filter.Tendsto ((fun l' => (roomPointSeq f (g1 f l'): stdSimplex ℝ (Fin
      n))) ∘ φ) Filter.atTop (𝓝 z) :=
    (hpkg f).2.2
  have constant_color_set : ∀ l', (roomSeq f (g1 f l')).1.2 = C :=
    (gpkg f).2
  have coords_outside_C_zero : ∀ i_1 ∉ C, z.1 i_1 = 0 := by
    intro i_1 hi_not_C
    have tendsto_zero : Filter.Tendsto (fun l' => ((roomPointSeq f (g1 f l'))
        : stdSimplex ℝ (Fin n)).1 i_1) Filter.atTop (𝓝 0) :=
      dominant_coords_tend_to_zero f C (g1 f) constant_color_set i_1 hi_not_C
    have h_tendsto_coord_z : Tendsto (fun k => ((roomPointSeq f (g1 f (φ k)))
        : stdSimplex ℝ (Fin n)).1 i_1) atTop (𝓝 (z.1 i_1)) := by
      have h_continuous : Continuous (fun x : stdSimplex ℝ (Fin n) => x.1 i_1) :=
        Continuous.comp (continuous_apply i_1) continuous_subtype_val
      exact h_continuous.continuousAt.tendsto.comp convergence_to_z
    have tendsto_zero_subseq : Tendsto (fun k => ((roomPointSeq f (g1 f (φ k)))
        : stdSimplex ℝ (Fin n)).1 i_1) atTop (𝓝 0) :=
      (dominant_coords_tend_to_zero f C (g1 f)
          constant_color_set i_1 hi_not_C).comp (hpkg f).2.1.tendsto_atTop
    exact tendsto_nhds_unique h_tendsto_coord_z tendsto_zero_subseq
  have sum_coords_in_C_eq_one : ∑ i_1 ∈ C, z.1 i_1 = 1 := by
    have total_sum_eq_one : ∑ i, z.1 i = 1 := z.2.2
    have split_sum : ∑ i, z.1 i = ∑ i ∈ C, z.1 i + ∑ i ∈ Cᶜ, z.1 i :=
      (Finset.sum_add_sum_compl C (z.1)).symm
    have compl_sum_zero : ∑ i ∈ Cᶜ, z.1 i = 0 := by
      apply Finset.sum_eq_zero
      intro i_1 hi
      exact coords_outside_C_zero i_1 (Finset.mem_compl.mp hi)
    rw [split_sum, compl_sum_zero, add_zero] at total_sum_eq_one
    exact total_sum_eq_one
  have f_coords_ge_z_coords := f_coords_ge_z_coords f hf
  have sum_f_coords_ge_one : ∑ i_1 ∈ C, (f z).1 i_1 ≥ 1 := by
    calc ∑ i_1 ∈ C, (f z).1 i_1
        ≥ ∑ i_1 ∈ C, z.1 i_1 := Finset.sum_le_sum fun i_1 hi => f_coords_ge_z_coords i_1 hi
      _ = 1 := sum_coords_in_C_eq_one
  have f_coords_outside_C_zero : ∀ i_1 ∉ C, (f z).1 i_1 = 0 := by
    intro i_1 hi_not_C
    have total_sum_f : ∑ i, (f z).1 i = 1 := (f z).2.2
    have sum_f_C_eq_one : ∑ i_2 ∈ C, (f z).1 i_2 = 1 := by
      have : ∑ i_2 ∈ C, (f z).1 i_2 ≤ 1 := by
        calc ∑ i_2 ∈ C, (f z).1 i_2
          ≤ ∑ i, (f z).1 i := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ C)
              (fun i_2 _ _ => (f z).2.1 i_2)
          _ = 1 := total_sum_f
      exact le_antisymm this sum_f_coords_ge_one
    have compl_sum_zero : ∑ i_2 ∈ Cᶜ, (f z).1 i_2 = 0 := by
      have split_sum : ∑ i, (f z).1 i = ∑ i ∈ C, (f z).1 i + ∑ i ∈ Cᶜ, (f z).1 i :=
        (Finset.sum_add_sum_compl C ((f z).1)).symm
      rw [total_sum_f, sum_f_C_eq_one] at split_sum
      linarith
    have hi_in_compl : i_1 ∈ Cᶜ := Finset.mem_compl.mpr hi_not_C
    have h_nonneg : (f z).1 i_1 ≥ 0 := (f z).2.1 i_1
    have h_le_sum : (f z).1 i_1 ≤ ∑ j ∈ Cᶜ,
        (f z).1 j := Finset.single_le_sum (fun j _ => (f z).2.1 j) hi_in_compl
    rw [compl_sum_zero] at h_le_sum
    exact le_antisymm h_le_sum h_nonneg
  have f_coords_eq_z_coords : ∀ i_1 ∈ C, (f z).1 i_1 = z.1 i_1 := by
    intro i_1 hi_C
    have h_sum_f_C_eq_one : ∑ i_2 ∈ C, (f z).1 i_2 = 1 := by
      have total_sum_f : ∑ i, (f z).1 i = 1 := (f z).2.2
      have : ∑ i_2 ∈ C, (f z).1 i_2 ≤ 1 := by
        calc
          ∑ i_2 ∈ C, (f z).1 i_2 ≤ ∑ i,
              (f z).1 i := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ C)
              (fun i_2 _ _ => (f z).2.1 i_2)
          _ = 1 := total_sum_f
      exact le_antisymm this (sum_f_coords_ge_one)
    have h_sum_eq : ∑ i_2 ∈ C, (f z).1 i_2 = ∑ i_2 ∈ C, z.1 i_2 := by
      rw [h_sum_f_C_eq_one, sum_coords_in_C_eq_one]
    exact (((Finset.sum_eq_sum_iff_of_le fun i_2 hi => f_coords_ge_z_coords i_2 hi).mp
        h_sum_eq.symm) i_1 hi_C).symm
  ext i_1
  by_cases hi : i_1 ∈ C
  · exact f_coords_eq_z_coords i_1 hi
  · change (f z).1 i_1 = z.1 i_1
    rw [f_coords_outside_C_zero i_1 hi, coords_outside_C_zero i_1 hi]


end Brouwer
