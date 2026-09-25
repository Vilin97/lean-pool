/-
Copyright (c) 2026 Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vinicius de Oliveira Rodrigues
-/
module

/-
Copyright (c) 2026 Vinicius de Oliveira Rodrigues.
Released under Apache 2.0 license as described in the file LICENSE.
-/

public import Mathlib.SetTheory.Cardinal.Arithmetic
public import Mathlib.Topology.Baire.CompleteMetrizable
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Perfect
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Tactic

/-!
# The uniformity of the meagre ideal

The definition `nonM` below uses the usual topology on the real numbers.
In particular it does not define this cardinal by means of slaloms.

This file also proves the elementary countable-family slalom avoidance
lemma. The category comparison used in the final proof is developed in
`NonMRR.CategoryBound`; the general Bartoszyński characterization is not assumed.
-/

@[expose] public section

open Set Filter Cardinal

namespace NonMRR

universe u

/-- The least size of a nonmeagre subset of a topological space. -/
noncomputable def nonMeagreCardinal (X : Type u) [TopologicalSpace X] : Cardinal.{u} :=
  sInf {κ | ∃ s : Set X, ¬ IsMeagre s ∧ Cardinal.mk s = κ}

/-- The uniformity of the meagre ideal on the real line, as in the manuscript. -/
noncomputable def nonM : Cardinal := nonMeagreCardinal ℝ

/-- The corresponding cardinal for Baire space; no identification is postulated. -/
noncomputable def nonMBaire : Cardinal := nonMeagreCardinal (ℕ → ℕ)

theorem nonMeagreCardinal_le_mk {X : Type u} [TopologicalSpace X]
    {s : Set X} (hs : ¬ IsMeagre s) : nonMeagreCardinal X ≤ Cardinal.mk s := by
  exact csInf_le (OrderBot.bddBelow _) ⟨s, hs, rfl⟩

/-- Every set smaller than the uniformity of the meagre ideal is meagre. -/
theorem isMeagre_of_mk_lt_nonMeagreCardinal {X : Type u} [TopologicalSpace X]
    {s : Set X} (hs : Cardinal.mk s < nonMeagreCardinal X) : IsMeagre s := by
  by_contra h
  exact (not_lt_of_ge (nonMeagreCardinal_le_mk h)) hs

theorem isMeagre_of_mk_lt_nonM {s : Set ℝ} (hs : Cardinal.mk s < nonM) :
    IsMeagre s := isMeagre_of_mk_lt_nonMeagreCardinal hs

/-- In a nonempty Baire space, the defining minimum has an actual witness. -/
theorem exists_nonmeagre_minimizer (X : Type u) [TopologicalSpace X]
    [BaireSpace X] [Nonempty X] :
    ∃ s : Set X, ¬ IsMeagre s ∧ Cardinal.mk s = nonMeagreCardinal X := by
  have hne : {κ : Cardinal.{u} | ∃ s : Set X, ¬ IsMeagre s ∧ Cardinal.mk s = κ}.Nonempty :=
    ⟨Cardinal.mk (univ : Set X), univ,
      not_isMeagre_of_isOpen isOpen_univ univ_nonempty, rfl⟩
  exact csInf_mem hne

theorem nonMeagreCardinal_le_mk_space (X : Type u) [TopologicalSpace X]
    [BaireSpace X] [Nonempty X] : nonMeagreCardinal X ≤ Cardinal.mk X := by
  have h := nonMeagreCardinal_le_mk
    (not_isMeagre_of_isOpen (X := X) isOpen_univ univ_nonempty)
  simpa using h

/-- Countable sets are meagre in a perfect T₁ space. -/
theorem isMeagre_of_countable {X : Type u} [TopologicalSpace X] [T1Space X]
    [PerfectSpace X] {s : Set X} (hs : s.Countable) : IsMeagre s := by
  have hsingle : ∀ x : X, IsMeagre ({x} : Set X) := fun x => by
    apply IsNowhereDense.isMeagre
    simpa only [IsNowhereDense, isClosed_singleton.closure_eq] using interior_singleton x
  simpa only [biUnion_of_singleton] using isMeagre_biUnion hs (fun x _ => hsingle x)

/-- The real uniformity is strictly larger than the countable cardinal. -/
theorem aleph0_lt_nonM : ℵ₀ < nonM := by
  obtain ⟨s, hs, hcard⟩ := exists_nonmeagre_minimizer ℝ
  by_contra h
  have hc : Cardinal.mk s ≤ ℵ₀ := by
    rw [hcard]
    exact le_of_not_gt h
  exact hs (isMeagre_of_countable ((Cardinal.mk_le_aleph0_iff).mp hc))

/-- A countable collection of finite slaloms has a common eventual avoider.
No uniform width bound is needed for this elementary diagonal argument. -/
theorem exists_eventually_avoids_of_countable
    {Φ : Set (ℕ → Finset ℕ)} (hΦ : Φ.Countable) :
    ∃ x : ℕ → ℕ, ∀ φ ∈ Φ, ∀ᶠ n in atTop, x n ∉ φ n := by
  classical
  obtain ⟨f, hf⟩ := Set.countable_iff_exists_subset_range.mp hΦ
  let forbidden (n : ℕ) : Finset ℕ := (Finset.range (n + 1)).biUnion (fun i => f i n)
  let x (n : ℕ) : ℕ := (forbidden n).sup id + 1
  refine ⟨x, ?_⟩
  intro φ hφ
  obtain ⟨i, rfl⟩ := hf hφ
  filter_upwards [eventually_ge_atTop i] with n hn
  intro hmem
  have hin : x n ∈ forbidden n :=
    Finset.mem_biUnion.mpr ⟨i, Finset.mem_range.mpr (by omega), hmem⟩
  have hle : x n ≤ (forbidden n).sup id := Finset.le_sup (f := id) hin
  change (forbidden n).sup id + 1 ≤ (forbidden n).sup id at hle
  omega

/-- Eventual disagreement with a fixed function is a meagre condition
in Baire space. -/
theorem isMeagre_eventually_ne (x : ℕ → ℕ) :
    IsMeagre {f : ℕ → ℕ | ∀ᶠ n in atTop, f n ≠ x n} := by
  classical
  let F (N : ℕ) : Set (ℕ → ℕ) := {f | ∀ n, N ≤ n → f n ≠ x n}
  have hclosed (N : ℕ) : IsClosed (F N) := by
    have heq : F N = ⋂ n, ⋂ (_ : N ≤ n), {f : ℕ → ℕ | f n ≠ x n} := by
      ext f
      simp [F]
    rw [heq]
    apply isClosed_iInter
    intro n
    apply isClosed_iInter
    intro _
    have hc : IsClosed ((fun f : ℕ → ℕ => f n) ⁻¹' ({x n}ᶜ : Set ℕ)) :=
      IsClosed.preimage (continuous_apply n) (isClosed_discrete _)
    convert hc using 1
    rfl
  have hnowhere (N : ℕ) : IsNowhereDense (F N) := by
    rw [(hclosed N).isNowhereDense_iff]
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro f hf
    obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.mp isOpen_interior f hf
    let n : ℕ := max N (I.sup id + 1)
    have hnN : N ≤ n := le_max_left _ _
    have hnI : n ∉ I := by
      intro h
      have hle := Finset.le_sup (f := id) h
      change n ≤ I.sup id at hle
      have hgt : I.sup id + 1 ≤ n := le_max_right _ _
      omega
    have hupdated : Function.update f n (x n) ∈ interior (F N) := by
      apply hsub
      intro i hi
      have hin : i ≠ n := by rintro rfl; exact hnI hi
      simpa only [Function.update_of_ne hin] using (hu i hi).2
    have hbad := interior_subset hupdated n hnN
    simp at hbad
  have heq : {f : ℕ → ℕ | ∀ᶠ n in atTop, f n ≠ x n} = ⋃ N, F N := by
    ext f
    simp only [Set.mem_ofPred_eq, eventually_atTop, Set.mem_iUnion, F]
  rw [heq]
  exact isMeagre_iUnion (fun N => (hnowhere N).isMeagre)

/-- Every nonmeagre family in Baire space agrees infinitely often with
each prescribed function somewhere in the family. -/
theorem exists_frequently_eq_of_not_isMeagre {s : Set (ℕ → ℕ)}
    (hs : ¬ IsMeagre s) (x : ℕ → ℕ) :
    ∃ f ∈ s, ∃ᶠ n in atTop, f n = x n := by
  by_contra h
  push Not at h
  apply hs
  apply (isMeagre_eventually_ne x).mono
  intro f hf
  exact h f hf

end NonMRR

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
