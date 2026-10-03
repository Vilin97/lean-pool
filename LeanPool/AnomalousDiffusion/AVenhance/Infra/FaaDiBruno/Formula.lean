/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Analytic.Binomial
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Nat.Choose.Multinomial
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FaaDiBruno.Seminorm

/-!
# The finite-dimensional multivariate Faà di Bruno formula

Mathlib's `OrderedFinpartition` representation is the coordinate-free form of
the multivariate formula: its parts group the input derivative directions
that enter each derivative of the inner map. The paper-form sum is defined
separately below; identifying its terms with fibers of the ordered-partition
sum remains a separate combinatorial theorem.
-/

@[expose] public section

noncomputable section

namespace AVenhance.FaaDiBruno

open FormalMultilinearSeries

/-- The `n`-th derivative of a composition, expanded over ordered set
partitions of its `n` coordinate directions.  This is Mathlib's Faà di Bruno
formula, stated for arbitrary real normed spaces so it specializes to
`Vec d → Vec d` and `Vec d → ℝ`. -/
theorem multivariateFaaDiBruno
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {h : F → G} {g : E → F} {x : E} {n : ℕ}
    (hh : ContDiffAt ℝ n h (g x)) (hg : ContDiffAt ℝ n g x) :
    iteratedFDeriv ℝ n (h ∘ g) x =
      ∑ c : OrderedFinpartition n,
        (ftaylorSeries ℝ h (g x)).compAlongOrderedFinpartition
          (ftaylorSeries ℝ g x) c := by
  simpa [FormalMultilinearSeries.taylorComp] using
    (iteratedFDeriv_comp hh hg (i := n) le_rfl)

/-- A paper multi-index is a coordinatewise multiplicity vector. -/
abbrev PaperMultiIndex (d : ℕ) := Fin d → ℕ

/-- The order of a paper multi-index. -/
def paperMultiIndexSize {d : ℕ} (α : PaperMultiIndex d) : ℕ := ∑ i, α i

theorem paperMultiIndex_coord_le_size {d : ℕ} (α : PaperMultiIndex d) (i : Fin d) :
    α i ≤ paperMultiIndexSize α := by
  unfold paperMultiIndexSize
  exact Finset.single_le_sum (f := fun j : Fin d ↦ α j)
    (fun j hj ↦ Nat.zero_le _) (Finset.mem_univ i)

/-- The finite range of nonzero multi-indices of order at most `n`. -/
def PaperMultiIndexUpTo (d n : ℕ) :=
  {α : PaperMultiIndex d // 1 ≤ paperMultiIndexSize α ∧ paperMultiIndexSize α ≤ n}

namespace PaperMultiIndexUpTo

theorem finite {d n : ℕ} : Finite (PaperMultiIndexUpTo d n) := by
  classical
  let encode (α : PaperMultiIndexUpTo d n) :
      ∀ i : Fin d, Fin (n + 1) := fun i ↦
    ⟨α.1 i, Nat.lt_succ_iff.mpr
      ((paperMultiIndex_coord_le_size α.1 i).trans α.2.2)⟩
  have hinj : Function.Injective encode := by
    intro α β h
    apply Subtype.ext
    funext i
    exact congrArg Fin.val (congrFun h i)
  exact Finite.of_injective encode hinj

noncomputable instance instFinite {d n : ℕ} : Finite (PaperMultiIndexUpTo d n) := finite

noncomputable instance instFintype {d n : ℕ} : Fintype (PaperMultiIndexUpTo d n) :=
  Fintype.ofFinite _

end PaperMultiIndexUpTo

/-- Graded lexicographic order used for the strictly ordered derivative
multi-indices in the paper's partition data. -/
def paperMultiIndexLT {d : ℕ} (α β : PaperMultiIndex d) : Prop :=
  paperMultiIndexSize α < paperMultiIndexSize β ∨
    (paperMultiIndexSize α = paperMultiIndexSize β ∧
      ∃ i : Fin d, α i < β i ∧ ∀ j : Fin d, j < i → α j = β j)

/-- The finite multi-index and multiplicity data called `p_s(β, α)` in
Appendix B.1. The `ell` entries are distinct and strictly increasing in
graded lexicographic order. -/
@[ext] structure PaperPartitionData (d s : ℕ) (β α : PaperMultiIndex d) where
  /-- Multi-index multiplicities in a Faà di Bruno partition. -/
  k : Fin s → PaperMultiIndex d
  /-- Distinct derivative multi-indices ordered by graded lexicographic order. -/
  ell : Fin s → PaperMultiIndex d
  k_nonzero : ∀ j, 0 < paperMultiIndexSize (k j)
  ell_nonzero : ∀ j, 0 < paperMultiIndexSize (ell j)
  ell_strictlyOrdered : ∀ i j, i < j → paperMultiIndexLT (ell i) (ell j)
  k_sum : ∀ i, (∑ j, k j i) = α i
  beta_sum : ∀ i, (∑ j, paperMultiIndexSize (k j) * ell j i) = β i

/-- The paper's `p_s(β, α)`, with the dimension generalized according to the correction. -/
def paperPartitions {d s : ℕ} (β α : PaperMultiIndex d) :=
  PaperPartitionData d s β α

namespace PaperPartitionData

theorem k_le_alpha {d s : ℕ} {β α : PaperMultiIndex d}
    (P : paperPartitions (d := d) (s := s) β α) (j : Fin s) (i : Fin d) :
    P.k j i ≤ α i := by
  change PaperPartitionData d s β α at P
  rw [← P.k_sum i]
  exact Finset.single_le_sum (fun l hl ↦ Nat.zero_le (P.k l i)) (Finset.mem_univ j)

theorem ell_le_beta {d s : ℕ} {β α : PaperMultiIndex d}
    (P : paperPartitions (d := d) (s := s) β α) (j : Fin s) (i : Fin d) :
    P.ell j i ≤ β i := by
  change PaperPartitionData d s β α at P
  have hterm : paperMultiIndexSize (P.k j) * P.ell j i ≤
      ∑ l : Fin s, paperMultiIndexSize (P.k l) * P.ell l i :=
    Finset.single_le_sum
      (f := fun l : Fin s ↦ paperMultiIndexSize (P.k l) * P.ell l i)
      (fun l hl ↦ Nat.zero_le _) (Finset.mem_univ j)
  rw [P.beta_sum i] at hterm
  have hk : 1 ≤ paperMultiIndexSize (P.k j) := P.k_nonzero j
  calc
    P.ell j i = 1 * P.ell j i := by simp
    _ ≤ paperMultiIndexSize (P.k j) * P.ell j i :=
      Nat.mul_le_mul_right _ hk
    _ ≤ β i := hterm

theorem finite {d s : ℕ} {β α : PaperMultiIndex d} :
    Finite (paperPartitions (d := d) (s := s) β α) := by
  classical
  let encode (P : paperPartitions (d := d) (s := s) β α) :
      (Fin s → (∀ i : Fin d, Fin (α i + 1))) ×
        (Fin s → (∀ i : Fin d, Fin (β i + 1))) :=
    (fun j i ↦ ⟨P.k j i, Nat.lt_succ_iff.mpr (PaperPartitionData.k_le_alpha P j i)⟩,
      fun j i ↦ ⟨P.ell j i, Nat.lt_succ_iff.mpr (PaperPartitionData.ell_le_beta P j i)⟩)
  have hinj : Function.Injective encode := by
    intro P Q h
    apply PaperPartitionData.ext
    · funext j i
      have hh := congrArg Prod.fst h
      exact congrArg Fin.val (congrFun (congrFun hh j) i)
    · funext j i
      have hh := congrArg Prod.snd h
      exact congrArg Fin.val (congrFun (congrFun hh j) i)
  exact Finite.of_injective encode hinj

noncomputable instance instFinite {d s : ℕ} {β α : PaperMultiIndex d} :
    Finite (paperPartitions (d := d) (s := s) β α) := PaperPartitionData.finite

noncomputable instance instFintype {d s : ℕ} {β α : PaperMultiIndex d} :
    Fintype (paperPartitions (d := d) (s := s) β α) := Fintype.ofFinite _

end PaperPartitionData

open Homogenization

end AVenhance.FaaDiBruno

end
