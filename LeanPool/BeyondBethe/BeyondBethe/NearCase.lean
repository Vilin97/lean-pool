/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.CycleTransfer
public import LeanPool.BeyondBethe.BeyondBethe.CleanConstants
public import LeanPool.BeyondBethe.BeyondBethe.Completion
public import LeanPool.BeyondBethe.BeyondBethe.ClusterCertificate
public import LeanPool.BeyondBethe.BeyondBethe.SourceBetheUpper
public import Mathlib.Data.Finset.Sort
public import Mathlib.Tactic

/-! # Near Case -/

@[expose] public section

open scoped BigOperators

namespace BeyondBethe

/-- The actual clean two-row factors of the alternating permutation. -/
noncomputable def cleanCycleFactors
    {n : ℕ} (η : ℝ) (P : Matrix (Fin n) (Fin n) ℝ)
    (h : Equiv.Perm (Fin n)) : Finset h.cycleFactorsFinset := by
  classical
  exact Finset.univ.filter fun c ↦
    (c : Equiv.Perm (Fin n)).support.card = 2 ∧
      cycleGoodCount η P h c = 2

theorem cleanCycleFactors_card
    {n : ℕ} (η : ℝ) (P : Matrix (Fin n) (Fin n) ℝ)
    (h : Equiv.Perm (Fin n)) :
    (cleanCycleFactors η P h).card = cleanCycleCount η P h := by
  classical
  rw [cleanCycleCount]
  calc
    (cleanCycleFactors η P h).card =
        ∑ c : h.cycleFactorsFinset,
          if (c : Equiv.Perm (Fin n)).support.card = 2 ∧
              cycleGoodCount η P h c = 2 then 1 else 0 := by
      simp [cleanCycleFactors]
    _ = ∑ c : h.cycleFactorsFinset, cleanCycleIndicator η P h c := by
      apply Finset.sum_congr rfl
      intro c _
      rfl

theorem cleanCycleFactor_property
    {n : ℕ} {η : ℝ} {P : Matrix (Fin n) (Fin n) ℝ}
    {h : Equiv.Perm (Fin n)} (c : cleanCycleFactors η P h) :
    (c.1 : Equiv.Perm (Fin n)).support.card = 2 ∧
      cycleGoodCount η P h c.1 = 2 := by
  have hc := c.2
  change c.1 ∈ Finset.univ.filter (fun d : h.cycleFactorsFinset ↦
    (d : Equiv.Perm (Fin n)).support.card = 2 ∧
      cycleGoodCount η P h d = 2) at hc
  exact (Finset.mem_filter.mp hc).2

/-- The two rows of a clean factor, in the ambient linear order. -/
noncomputable def cleanCycleRow
    {n : ℕ} {η : ℝ} {P : Matrix (Fin n) (Fin n) ℝ}
    {h : Equiv.Perm (Fin n)} (c : cleanCycleFactors η P h) :
    Fin 2 → Fin n := fun k ↦
  ((c.1 : Equiv.Perm (Fin n)).support.orderIsoOfFin
    (cleanCycleFactor_property c).1 k).1

theorem cleanCycleRow_mem_support
    {n : ℕ} {η : ℝ} {P : Matrix (Fin n) (Fin n) ℝ}
    {h : Equiv.Perm (Fin n)} (c : cleanCycleFactors η P h) (k : Fin 2) :
    cleanCycleRow c k ∈ (c.1 : Equiv.Perm (Fin n)).support := by
  exact ((c.1 : Equiv.Perm (Fin n)).support.orderIsoOfFin
    (cleanCycleFactor_property c).1 k).2

theorem cleanCycleRow_injective
    {n : ℕ} {η : ℝ} {P : Matrix (Fin n) (Fin n) ℝ}
    {h : Equiv.Perm (Fin n)} (c : cleanCycleFactors η P h) :
    Function.Injective (cleanCycleRow c) := by
  intro k l hkl
  apply ((c.1 : Equiv.Perm (Fin n)).support.orderIsoOfFin
    (cleanCycleFactor_property c).1).injective
  exact Subtype.ext hkl

theorem cleanCycleRows_ne
    {n : ℕ} {η : ℝ} {P : Matrix (Fin n) (Fin n) ℝ}
    {h : Equiv.Perm (Fin n)} (c : cleanCycleFactors η P h) :
    cleanCycleRow c 0 ≠ cleanCycleRow c 1 := by
  intro hrs
  have := cleanCycleRow_injective c hrs
  norm_num at this

theorem cleanCycleRow_mem_goodRows
    {n : ℕ} {η : ℝ} {P : Matrix (Fin n) (Fin n) ℝ}
    {h : Equiv.Perm (Fin n)} (c : cleanCycleFactors η P h) (k : Fin 2) :
    cleanCycleRow c k ∈ goodRows η P := by
  have hcard := cleanCycleFactor_property c
  have hinter :
      (c.1 : Equiv.Perm (Fin n)).support ∩ goodRows η P =
        (c.1 : Equiv.Perm (Fin n)).support := by
    apply Finset.eq_of_subset_of_card_le Finset.inter_subset_left
    rw [hcard.1]
    simpa [cycleGoodCount] using hcard.2.symm.le
  have hmem := cleanCycleRow_mem_support c k
  rw [← hinter] at hmem
  exact (Finset.mem_inter.mp hmem).2

/-- On a two-row alternating component, the two perfect matchings cross:
the unordered pair of core columns is the same at both rows. -/
theorem cleanCycle_core_columns
    {n : ℕ} {f g : Equiv.Perm (Fin n)}
    {η : ℝ} {P : Matrix (Fin n) (Fin n) ℝ}
    (c : cleanCycleFactors η P (alternatingRowPerm f g)) :
    let r := cleanCycleRow c 0
    let s := cleanCycleRow c 1
    r ≠ s ∧ f r ≠ g r ∧ f r = g s ∧ g r = f s := by
  let h := alternatingRowPerm f g
  let q : Equiv.Perm (Fin n) := c.1
  let r := cleanCycleRow c 0
  let s := cleanCycleRow c 1
  have hrs : r ≠ s := cleanCycleRows_ne c
  have hrq : r ∈ q.support := cleanCycleRow_mem_support c 0
  have hsq : s ∈ q.support := cleanCycleRow_mem_support c 1
  have hpair : q.support = {r, s} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl
      · exact hrq
      · exact hsq
    · have hqcard : q.support.card = 2 := (cleanCycleFactor_property c).1
      simpa [hrs, hqcard]
  have hqr_ne : q r ≠ r := Equiv.Perm.mem_support.mp hrq
  have hqs_ne : q s ≠ s := Equiv.Perm.mem_support.mp hsq
  have hqr_mem : q r ∈ q.support := by
    rw [Equiv.Perm.mem_support]
    exact mt q.injective.eq_iff.mp hqr_ne
  have hqs_mem : q s ∈ q.support := by
    rw [Equiv.Perm.mem_support]
    exact mt q.injective.eq_iff.mp hqs_ne
  have hqr : q r = s := by
    rw [hpair] at hqr_mem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hqr_mem
    exact hqr_mem.resolve_left hqr_ne
  have hqs : q s = r := by
    rw [hpair] at hqs_mem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hqs_mem
    exact hqs_mem.resolve_right hqs_ne
  have hfactor := Equiv.Perm.mem_cycleFactorsFinset_iff.mp c.1.2
  have hhr : h r = s := by
    rw [← hfactor.2 r hrq, hqr]
  have hhs : h s = r := by
    rw [← hfactor.2 s hsq, hqs]
  have hfrgs : f r = g s := by
    have := congrArg g hhr
    simpa [h, alternatingRowPerm] using this
  have hgrfs : g r = f s := by
    have := congrArg g hhs
    simpa [h, alternatingRowPerm] using this.symm
  have hfg : f r ≠ g r := by
    intro heq
    have hfix : h r = r := (alternatingRowPerm_fixed_iff f g r).2 heq
    exact hrs (hfix.symm.trans hhr)
  exact ⟨hrs, hfg, hfrgs, hgrfs⟩

theorem twoMatching_core_mem_heavy_of_good
    {n : ℕ} {P : Matrix (Fin n) (Fin n) ℝ}
    (hP : ∀ i, IsStrictProbabilityVector (P i))
    {η : ℝ} (f g : Equiv.Perm (Fin n))
    (hheavy : ∀ i j, j ∈ heavyCoordinates η (P i) →
      j = f i ∨ j = g i)
    {i : Fin n} (hgood : IsGoodRow η (P i)) :
    f i ∈ heavyCoordinates η (P i) ∧
      g i ∈ heavyCoordinates η (P i) ∧ f i ≠ g i := by
  obtain ⟨a, b, hab, hdist⟩ := hgood
  have hcore := goodRow_witness_mem_heavyCoordinates
    (hP i).probability hab hdist
  have ha := hheavy i a hcore.1
  have hb := hheavy i b hcore.2
  rcases ha with haf | hag <;> rcases hb with hbf | hbg
  · exact False.elim (hab (haf.trans hbf.symm))
  · subst a
    subst b
    exact ⟨hcore.1, hcore.2, hab⟩
  · subst a
    subst b
    exact ⟨hcore.2, hcore.1, hab.symm⟩
  · exact False.elim (hab (hag.trans hbg.symm))

theorem univ_sdiff_coreOutside_of_ne
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {a b : ι} (hab : a ≠ b) :
    Finset.univ \ coreOutside a b = {a, b} := by
  ext j
  simp only [Finset.mem_sdiff, Finset.mem_univ, coreOutside,
    Finset.mem_filter, true_and, Finset.mem_insert, Finset.mem_singleton]
  tauto

noncomputable def encodedCoreRowTransferCost
    {n : ℕ} (f g : Equiv.Perm (Fin n))
    (P U : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : ℝ :=
  transferCostOn (Finset.univ \ coreOutside (f i) (g i)) (P i) (U i)

noncomputable def cleanCycleWeightedCost
    {n : ℕ} {η : ℝ} {P : Matrix (Fin n) (Fin n) ℝ}
    {f g : Equiv.Perm (Fin n)}
    (U : Matrix (Fin n) (Fin n) ℝ)
    (c : cleanCycleFactors η P (alternatingRowPerm f g)) : ℝ :=
  ∑ k : Fin 2, encodedCoreRowTransferCost f g P U (cleanCycleRow c k)

theorem cleanCycleWeightedCost_eq_support_sum
    {n : ℕ} {η : ℝ} {P : Matrix (Fin n) (Fin n) ℝ}
    {f g : Equiv.Perm (Fin n)}
    (U : Matrix (Fin n) (Fin n) ℝ)
    (c : cleanCycleFactors η P (alternatingRowPerm f g)) :
    cleanCycleWeightedCost U c =
      ∑ i ∈ (c.1 : Equiv.Perm (Fin n)).support,
        encodedCoreRowTransferCost f g P U i := by
  let e := (c.1 : Equiv.Perm (Fin n)).support.orderIsoOfFin
    (cleanCycleFactor_property c).1
  unfold cleanCycleWeightedCost
  calc
    (∑ k : Fin 2, encodedCoreRowTransferCost f g P U (cleanCycleRow c k)) =
        ∑ i : (c.1 : Equiv.Perm (Fin n)).support,
          encodedCoreRowTransferCost f g P U i.1 := by
      exact Equiv.sum_comp e.toEquiv
        (fun i : (c.1 : Equiv.Perm (Fin n)).support ↦
          encodedCoreRowTransferCost f g P U i.1)
    _ = ∑ i ∈ (c.1 : Equiv.Perm (Fin n)).support,
          encodedCoreRowTransferCost f g P U i := by
      simpa using Finset.sum_coe_sort
        (c.1 : Equiv.Perm (Fin n)).support
        (encodedCoreRowTransferCost f g P U)

theorem encodedCoreRowTransferCost_nonneg
    {n : ℕ} {τ : ℝ} (hτ : 0 ≤ τ)
    {P X : Matrix (Fin n) (Fin n) ℝ}
    (hP : IsDoublyStochastic P)
    (hXint : ∀ i, IsInteriorProbabilityVector (X i))
    (f g : Equiv.Perm (Fin n)) (i : Fin n) :
    0 ≤ encodedCoreRowTransferCost f g P
      (fun a b ↦ transferU τ (X a) b) i := by
  unfold encodedCoreRowTransferCost transferCostOn
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (hP.nonnegative i j)
    (log_one_div_nonneg_of_pos_le_one
      (transferU_pos (hXint i) j)
      (transferU_le_one hτ (hXint i) j))

/-- Clean factors are vertex-disjoint, so their weighted core costs are
bounded by the global core-transfer cost. -/
theorem sum_cleanCycleWeightedCost_le_coreTransferCost
    {n : ℕ} {τ η : ℝ}
    {P X : Matrix (Fin n) (Fin n) ℝ}
    (hP : IsDoublyStochastic P) (hτ : 0 ≤ τ)
    (hXint : ∀ i, IsInteriorProbabilityVector (X i))
    (f g : Equiv.Perm (Fin n)) :
    (∑ c : cleanCycleFactors η P (alternatingRowPerm f g),
        cleanCycleWeightedCost (fun i j ↦ transferU τ (X i) j) c) ≤
      coreTransferCost (fun i ↦ coreOutside (f i) (g i)) P
        (fun i j ↦ transferU τ (X i) j) := by
  let S := cleanCycleFactors η P (alternatingRowPerm f g)
  let t : (alternatingRowPerm f g).cycleFactorsFinset → Finset (Fin n) :=
    fun c ↦ (c : Equiv.Perm (Fin n)).support
  let w : Fin n → ℝ := fun i ↦ encodedCoreRowTransferCost f g P
    (fun a b ↦ transferU τ (X a) b) i
  have hpair : (↑S : Set (alternatingRowPerm f g).cycleFactorsFinset).PairwiseDisjoint t := by
    intro c hc d hd hcd
    have hcd' : (c : Equiv.Perm (Fin n)) ≠ d := by
      intro heq
      apply hcd
      exact Subtype.ext heq
    exact (alternatingRowPerm f g).cycleFactorsFinset_pairwise_disjoint
      c.2 d.2 hcd' |>.disjoint_support
  have hunion : (∑ c : S, ∑ i ∈ t c.1, w i) =
      ∑ i ∈ S.biUnion t, w i := by
    calc
      (∑ c : S, ∑ i ∈ t c.1, w i) =
          ∑ c ∈ S, ∑ i ∈ t c, w i := by
        simpa using Finset.sum_coe_sort S (fun c ↦ ∑ i ∈ t c, w i)
      _ = ∑ i ∈ S.biUnion t, w i := (Finset.sum_biUnion hpair).symm
  change (∑ c : S, cleanCycleWeightedCost
    (fun a b => transferU τ (X a) b) c) ≤ ∑ i, w i
  simp_rw [cleanCycleWeightedCost_eq_support_sum
    (fun a b => transferU τ (X a) b)]
  change (∑ c : S, ∑ i ∈ t c.1, w i) ≤ ∑ i, w i
  rw [hunion]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun i _ _ ↦ encodedCoreRowTransferCost_nonneg hτ hP hXint f g i)

theorem cleanCycle_minCost_mul_fourCore
    {n : ℕ} {τ η : ℝ}
    {P X : Matrix (Fin n) (Fin n) ℝ}
    (hP : ∀ i, IsStrictProbabilityVector (P i))
    (hτ : 0 ≤ τ)
    (hXint : ∀ i, IsInteriorProbabilityVector (X i))
    (f g : Equiv.Perm (Fin n))
    (hheavy : ∀ i j, j ∈ heavyCoordinates η (P i) →
      j = f i ∨ j = g i)
    (c : cleanCycleFactors η P (alternatingRowPerm f g)) :
    (1 / 2 - η) * fourCoreTransferCost τ X
        (cleanCycleRow c 0) (cleanCycleRow c 1)
        (f (cleanCycleRow c 0)) (g (cleanCycleRow c 0)) ≤
      cleanCycleWeightedCost (fun i j ↦ transferU τ (X i) j) c := by
  let r := cleanCycleRow c 0
  let s := cleanCycleRow c 1
  let a := f r
  let b := g r
  have hcols := cleanCycle_core_columns c
  have hrgood : IsGoodRow η (P r) := by
    simpa [goodRows] using cleanCycleRow_mem_goodRows c 0
  have hsgood : IsGoodRow η (P s) := by
    simpa [goodRows] using cleanCycleRow_mem_goodRows c 1
  have hrheavy := twoMatching_core_mem_heavy_of_good hP f g hheavy hrgood
  have hsheavy := twoMatching_core_mem_heavy_of_good hP f g hheavy hsgood
  have hra : 1 / 2 - η ≤ P r a := by
    simpa [a, heavyCoordinates] using hrheavy.1
  have hrb : 1 / 2 - η ≤ P r b := by
    simpa [b, heavyCoordinates] using hrheavy.2.1
  have hsa : 1 / 2 - η ≤ P s a := by
    have : a = g s := hcols.2.2.1
    rw [this]
    simpa [heavyCoordinates] using hsheavy.2.1
  have hsb : 1 / 2 - η ≤ P s b := by
    have : b = f s := hcols.2.2.2
    rw [this]
    simpa [heavyCoordinates] using hsheavy.1
  have hlog : ∀ i j,
      0 ≤ Real.log (1 / transferU τ (X i) j) := fun i j ↦
    log_one_div_nonneg_of_pos_le_one (transferU_pos (hXint i) j)
      (transferU_le_one hτ (hXint i) j)
  have hsaCore : coreOutside (f s) (g s) = coreOutside a b := by
    rw [hcols.2.2.2.symm, hcols.2.2.1.symm, coreOutside_comm]
  unfold cleanCycleWeightedCost
  simp only [Fin.sum_univ_two]
  rw [show cleanCycleRow c 0 = r by rfl, show cleanCycleRow c 1 = s by rfl]
  unfold encodedCoreRowTransferCost
  rw [hsaCore, univ_sdiff_coreOutside_of_ne hcols.2.1]
  simp only [transferCostOn, Finset.sum_insert,
    Finset.sum_singleton, Finset.mem_singleton, hcols.2.1, not_false_eq_true]
  rw [fourCoreTransferCost]
  nlinarith [mul_le_mul_of_nonneg_right hra (hlog r a),
    mul_le_mul_of_nonneg_right hrb (hlog r b),
    mul_le_mul_of_nonneg_right hsa (hlog s a),
    mul_le_mul_of_nonneg_right hsb (hlog s b)]

noncomputable def failedCleanCycles
    {n : ℕ} (κ τ η : ℝ)
    (P X : Matrix (Fin n) (Fin n) ℝ)
    (f g : Equiv.Perm (Fin n)) :
    Finset (cleanCycleFactors η P (alternatingRowPerm f g)) := by
  classical
  exact Finset.univ.filter fun c ↦
    κ < fourCoreTransferCost τ X
      (cleanCycleRow c 0) (cleanCycleRow c 1)
      (f (cleanCycleRow c 0)) (g (cleanCycleRow c 0))

noncomputable def successfulCleanCycles
    {n : ℕ} (κ τ η : ℝ)
    (P X : Matrix (Fin n) (Fin n) ℝ)
    (f g : Equiv.Perm (Fin n)) :
    Finset (cleanCycleFactors η P (alternatingRowPerm f g)) :=
  Finset.univ \ failedCleanCycles κ τ η P X f g

theorem cleanCycleWeightedCost_nonneg
    {n : ℕ} {τ η : ℝ}
    {P X : Matrix (Fin n) (Fin n) ℝ}
    (hP : IsDoublyStochastic P) (hτ : 0 ≤ τ)
    (hXint : ∀ i, IsInteriorProbabilityVector (X i))
    (f g : Equiv.Perm (Fin n))
    (c : cleanCycleFactors η P (alternatingRowPerm f g)) :
    0 ≤ cleanCycleWeightedCost
      (fun i j ↦ transferU τ (X i) j) c := by
  unfold cleanCycleWeightedCost
  exact Finset.sum_nonneg fun k _ ↦
    encodedCoreRowTransferCost_nonneg hτ hP hXint f g (cleanCycleRow c k)

/-- The weighted Markov step on the actual clean alternating factors. -/
theorem failedCleanCycles_count_mul_le_coreTransferCost
    {n : ℕ} {κ τ η : ℝ}
    {P X : Matrix (Fin n) (Fin n) ℝ}
    (hP : ∀ i, IsStrictProbabilityVector (P i))
    (hPds : IsDoublyStochastic P)
    (hτ : 0 ≤ τ) (hfactor : 0 ≤ 1 / 2 - η)
    (hXint : ∀ i, IsInteriorProbabilityVector (X i))
    (f g : Equiv.Perm (Fin n))
    (hheavy : ∀ i j, j ∈ heavyCoordinates η (P i) →
      j = f i ∨ j = g i) :
    ((failedCleanCycles κ τ η P X f g).card : ℝ) *
        ((1 / 2 - η) * κ) ≤
      coreTransferCost (fun i ↦ coreOutside (f i) (g i)) P
        (fun i j ↦ transferU τ (X i) j) := by
  let F := failedCleanCycles κ τ η P X f g
  let C := cleanCycleFactors η P (alternatingRowPerm f g)
  let W : C → ℝ := fun c ↦ cleanCycleWeightedCost
    (fun i j ↦ transferU τ (X i) j) c
  have hpoint : ∀ c ∈ F, (1 / 2 - η) * κ ≤ W c := by
    intro c hc
    have hfail : κ < fourCoreTransferCost τ X
        (cleanCycleRow c 0) (cleanCycleRow c 1)
        (f (cleanCycleRow c 0)) (g (cleanCycleRow c 0)) := by
      simpa [F, failedCleanCycles] using hc
    have hscaled : (1 / 2 - η) * κ ≤
        (1 / 2 - η) * fourCoreTransferCost τ X
          (cleanCycleRow c 0) (cleanCycleRow c 1)
          (f (cleanCycleRow c 0)) (g (cleanCycleRow c 0)) :=
      mul_le_mul_of_nonneg_left hfail.le hfactor
    exact hscaled.trans (cleanCycle_minCost_mul_fourCore
      hP hτ hXint f g hheavy c)
  have hfailedSum : (F.card : ℝ) * ((1 / 2 - η) * κ) ≤
      ∑ c ∈ F, W c := by
    calc
      (F.card : ℝ) * ((1 / 2 - η) * κ) =
          ∑ _c ∈ F, ((1 / 2 - η) * κ) := by simp
      _ ≤ ∑ c ∈ F, W c := Finset.sum_le_sum hpoint
  have hsubset : F ⊆ Finset.univ := Finset.subset_univ F
  have hsumAll : (∑ c ∈ F, W c) ≤ ∑ c : C, W c := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun c _ _ ↦ cleanCycleWeightedCost_nonneg hPds hτ hXint f g c)
  exact hfailedSum.trans (hsumAll.trans
    (sum_cleanCycleWeightedCost_le_coreTransferCost hPds hτ hXint f g))

theorem failedCleanCycles_count_le
    {n : ℕ} (hn : 0 < n) {κ τ η εtr : ℝ}
    {P X : Matrix (Fin n) (Fin n) ℝ}
    (hP : ∀ i, IsStrictProbabilityVector (P i))
    (hPds : IsDoublyStochastic P)
    (hτ : 0 ≤ τ) (hfactor : 0 ≤ 1 / 2 - η)
    (hmin : 0 < (1 / 2 - η) * κ)
    (hXint : ∀ i, IsInteriorProbabilityVector (X i))
    (f g : Equiv.Perm (Fin n))
    (hheavy : ∀ i j, j ∈ heavyCoordinates η (P i) →
      j = f i ∨ j = g i)
    (hcore : coreTransferCost (fun i ↦ coreOutside (f i) (g i)) P
          (fun i j ↦ transferU τ (X i) j) / n ≤
        εtr * ((1 / 2 - η) * κ)) :
    ((failedCleanCycles κ τ η P X f g).card : ℝ) ≤ εtr * n := by
  have hweighted := failedCleanCycles_count_mul_le_coreTransferCost
    (κ := κ) hP hPds hτ hfactor hXint f g hheavy
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have htotal := (div_le_iff₀ hnR).mp hcore
  exact failedPair_count_le_transferError hmin hweighted (by
    calc
      coreTransferCost (fun i ↦ coreOutside (f i) (g i)) P
          (fun i j ↦ transferU τ (X i) j) ≤
          (εtr * ((1 / 2 - η) * κ)) * n := htotal
      _ = εtr * n * ((1 / 2 - η) * κ) := by ring)

theorem successfulCleanCycles_card_add_failed
    {n : ℕ} (κ τ η : ℝ)
    (P X : Matrix (Fin n) (Fin n) ℝ)
    (f g : Equiv.Perm (Fin n)) :
    (successfulCleanCycles κ τ η P X f g).card +
    (failedCleanCycles κ τ η P X f g).card =
      cleanCycleCount η P (alternatingRowPerm f g) := by
  have hpart := Finset.card_sdiff_add_card_eq_card
    (Finset.subset_univ (failedCleanCycles κ τ η P X f g))
  simpa [successfulCleanCycles, Finset.card_univ, Fintype.card_coe,
    cleanCycleFactors_card] using hpart

/-- The exact clean-pair counting conclusion used in the near case. -/
theorem successfulCleanCycles_count_ge_threeEighths
    {n : ℕ} {κ τ η : ℝ}
    {P X : Matrix (Fin n) (Fin n) ℝ}
    (hP : ∀ i, IsStrictProbabilityVector (P i))
    (f g : Equiv.Perm (Fin n))
    (hheavy : ∀ i j, j ∈ heavyCoordinates η (P i) →
      j = f i ∨ j = g i)
    (hbad : ((badRows η P).card : ℝ) ≤ n / 128)
    (hlong : (longCycleGoodRows η P (alternatingRowPerm f g) : ℝ) ≤
      n / 16)
    (hfailed : ((failedCleanCycles κ τ η P X f g).card : ℝ) ≤
      n / 16) :
    3 * n / 8 ≤
      ((successfulCleanCycles κ τ η P X f g).card : ℝ) := by
  have haccountNat := alternating_cleanCycle_count hP f g hheavy
  have haccountCast : (n : ℝ) ≤
      2 * ((badRows η P).card : ℝ) +
        (longCycleGoodRows η P (alternatingRowPerm f g) : ℝ) +
        2 * (cleanCycleCount η P (alternatingRowPerm f g) : ℝ) := by
    exact_mod_cast haccountNat
  have haccount : (n : ℝ) - 2 * (badRows η P).card -
        longCycleGoodRows η P (alternatingRowPerm f g) ≤
      2 * cleanCycleCount η P (alternatingRowPerm f g) := by
    linarith
  have hclean := cleanPair_count_ge_fiftyNine hbad hlong haccount
  have hpartitionNat := successfulCleanCycles_card_add_failed
    κ τ η P X f g
  have hpartitionCast :
      ((successfulCleanCycles κ τ η P X f g).card : ℝ) +
          ((failedCleanCycles κ τ η P X f g).card : ℝ) =
        (cleanCycleCount η P (alternatingRowPerm f g) : ℝ) := by
    exact_mod_cast hpartitionNat
  have hpartition :
      (cleanCycleCount η P (alternatingRowPerm f g) : ℝ) -
          (failedCleanCycles κ τ η P X f g).card ≤
        (successfulCleanCycles κ τ η P X f g).card := by
    linarith
  exact successfulCleanPair_count_ge_threeEighths (Nat.cast_nonneg n)
    hclean hfailed hpartition

/-- Pointwise form: every successful clean factor receives the uniform gain
from Lemma 19. -/
theorem successfulCleanCycle_gain
    {n : ℕ} {κ₀ ξ₀ γ₀ ell ξ τ η : ℝ}
    (hgain : CleanPairGainGuarantee κ₀ ξ₀ γ₀)
    (hell : 1 ≤ ell) (hlogn : Real.log n ≤ ell * Real.log 2)
    (hξ : 0 < ξ) (hξ₀ : ξ ≤ ξ₀) (hτscale : τ = ξ / (4 * ell))
    {A P X : Matrix (Fin n) (Fin n) ℝ}
    (hA : Matrix.Positive A) (hX : IsDoublyStochastic X)
    (hXint : ∀ i, IsInteriorProbabilityVector (X i))
    {R C : Fin n → ℝ} (hKKT : HasLogKKT τ A X R C)
    (f g : Equiv.Perm (Fin n))
    (c : cleanCycleFactors η P (alternatingRowPerm f g))
    (hc : c ∈ successfulCleanCycles κ₀ τ η P X f g) :
    γ₀ ≤ Real.log
      (pairGain A X (cleanCycleRow c 0) (cleanCycleRow c 1)) := by
  let rscale : Fin n → ℝ := fun i ↦ Real.exp (R i)
  let cscale : Fin n → ℝ := fun j ↦ Real.exp (C j)
  have hmult : HasMultiplicativeKKT τ A X rscale cscale :=
    hasMultiplicativeKKT_of_logKKT hA hXint hKKT
  have hcost : fourCoreTransferCost τ X
      (cleanCycleRow c 0) (cleanCycleRow c 1)
      (f (cleanCycleRow c 0)) (g (cleanCycleRow c 0)) ≤ κ₀ := by
    have hnot : ¬ κ₀ < fourCoreTransferCost τ X
        (cleanCycleRow c 0) (cleanCycleRow c 1)
        (f (cleanCycleRow c 0)) (g (cleanCycleRow c 0)) := by
      simpa [successfulCleanCycles, failedCleanCycles] using hc
    exact le_of_not_gt hnot
  have hcols := cleanCycle_core_columns c
  exact hgain hell hlogn hξ hξ₀ hτscale hA hX hXint
    (fun i ↦ Real.exp_pos _) (fun j ↦ Real.exp_pos _) hmult
    hcols.1 hcols.2.1 hcost

/-- Summed form of the preceding pointwise gain. -/
theorem successfulCleanCycles_gain_sum
    {n : ℕ} {κ₀ ξ₀ γ₀ ell ξ τ η : ℝ}
    (hgain : CleanPairGainGuarantee κ₀ ξ₀ γ₀)
    (hell : 1 ≤ ell) (hlogn : Real.log n ≤ ell * Real.log 2)
    (hξ : 0 < ξ) (hξ₀ : ξ ≤ ξ₀) (hτscale : τ = ξ / (4 * ell))
    {A P X : Matrix (Fin n) (Fin n) ℝ}
    (hA : Matrix.Positive A) (hX : IsDoublyStochastic X)
    (hXint : ∀ i, IsInteriorProbabilityVector (X i))
    {R C : Fin n → ℝ} (hKKT : HasLogKKT τ A X R C)
    (f g : Equiv.Perm (Fin n)) :
    ((successfulCleanCycles κ₀ τ η P X f g).card : ℝ) * γ₀ ≤
      ∑ c ∈ successfulCleanCycles κ₀ τ η P X f g,
        Real.log (pairGain A X (cleanCycleRow c 0) (cleanCycleRow c 1)) := by
  have hpoint := successfulCleanCycle_gain hgain hell hlogn hξ hξ₀
    (P := P) (η := η) hτscale hA hX hXint hKKT f g
  calc
    ((successfulCleanCycles κ₀ τ η P X f g).card : ℝ) * γ₀ =
        ∑ _c ∈ successfulCleanCycles κ₀ τ η P X f g, γ₀ := by simp
    _ ≤ ∑ c ∈ successfulCleanCycles κ₀ τ η P X f g,
        Real.log (pairGain A X (cleanCycleRow c 0) (cleanCycleRow c 1)) :=
      Finset.sum_le_sum hpoint

/-- An unordered pair of distinct rows.  The ambient order gives it a
canonical orientation whenever a formula such as `pairGain` expects one. -/
abbrev RowPair (n : ℕ) := {q : Finset (Fin n) // q.card = 2}

def rowPairRow {n : ℕ} (q : RowPair n) : Fin 2 → Fin n :=
  fun k ↦ (q.1.orderIsoOfFin q.2 k).1

def IsRowMatching {n : ℕ} (M : Finset (RowPair n)) : Prop :=
  (↑M : Set (RowPair n)).PairwiseDisjoint fun q ↦ q.1

noncomputable def rowPairWeight
    {n : ℕ} (A X : Matrix (Fin n) (Fin n) ℝ) (q : RowPair n) : ℝ :=
  max 0 (Real.log (pairGain A X (rowPairRow q 0) (rowPairRow q 1)))

noncomputable def rowMatchingWeight
    {n : ℕ} (A X : Matrix (Fin n) (Fin n) ℝ)
    (M : Finset (RowPair n)) : ℝ :=
  ∑ q ∈ M, rowPairWeight A X q

noncomputable def allRowMatchings (n : ℕ) : Finset (Finset (RowPair n)) := by
  classical
  exact Finset.univ.filter IsRowMatching

theorem allRowMatchings_nonempty (n : ℕ) :
    (allRowMatchings n).Nonempty := by
  refine ⟨∅, ?_⟩
  simp [allRowMatchings, IsRowMatching]

noncomputable def maximumMatchingGain
    {n : ℕ} (A X : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  (allRowMatchings n).sup' (allRowMatchings_nonempty n)
    (rowMatchingWeight A X)

theorem rowMatchingWeight_le_maximum
    {n : ℕ} (A X : Matrix (Fin n) (Fin n) ℝ)
    {M : Finset (RowPair n)} (hM : IsRowMatching M) :
    rowMatchingWeight A X M ≤ maximumMatchingGain A X := by
  apply Finset.le_sup'
  simpa [allRowMatchings] using hM

theorem maximumMatchingGain_nonneg
    {n : ℕ} (A X : Matrix (Fin n) (Fin n) ℝ) :
    0 ≤ maximumMatchingGain A X := by
  have h := rowMatchingWeight_le_maximum A X
    (M := ∅) (by simp [IsRowMatching])
  simpa [rowMatchingWeight] using h

theorem exists_maximumRowMatching
    {n : ℕ} (A X : Matrix (Fin n) (Fin n) ℝ) :
    ∃ M : Finset (RowPair n), IsRowMatching M ∧
      rowMatchingWeight A X M = maximumMatchingGain A X := by
  let S := allRowMatchings n
  have hnonempty : S.Nonempty := allRowMatchings_nonempty n
  have hexists : ∃ M ∈ S,
      maximumMatchingGain A X ≤ rowMatchingWeight A X M := by
    rw [maximumMatchingGain]
    exact (Finset.le_sup'_iff hnonempty).mp le_rfl
  obtain ⟨M, hMS, hle⟩ := hexists
  have hM : IsRowMatching M := by
    simpa [S, allRowMatchings] using hMS
  exact ⟨M, hM, le_antisymm (rowMatchingWeight_le_maximum A X hM) hle⟩

/-- Delete the zero-weight pairs from a matching.  Since the matching weights
are positive parts of logarithmic gains, this preserves the objective and
leaves only pairs whose multiplicative gain is strictly larger than one. -/
noncomputable def positiveRowPairs
    {n : ℕ} (A X : Matrix (Fin n) (Fin n) ℝ)
    (M : Finset (RowPair n)) : Finset (RowPair n) :=
  M.filter fun q ↦ 0 < Real.log
    (pairGain A X (rowPairRow q 0) (rowPairRow q 1))

theorem positiveRowPairs_subset
    {n : ℕ} (A X : Matrix (Fin n) (Fin n) ℝ)
    (M : Finset (RowPair n)) :
    positiveRowPairs A X M ⊆ M := by
  exact Finset.filter_subset _ _

theorem positiveRowPairs_isRowMatching
    {n : ℕ} {A X : Matrix (Fin n) (Fin n) ℝ}
    {M : Finset (RowPair n)} (hM : IsRowMatching M) :
    IsRowMatching (positiveRowPairs A X M) := by
  intro q hq q' hq' hne
  exact hM (positiveRowPairs_subset A X M hq)
    (positiveRowPairs_subset A X M hq') hne

theorem positiveRowPairs_logGain_pos
    {n : ℕ} {A X : Matrix (Fin n) (Fin n) ℝ}
    {M : Finset (RowPair n)} {q : RowPair n}
    (hq : q ∈ positiveRowPairs A X M) :
    0 < Real.log (pairGain A X (rowPairRow q 0) (rowPairRow q 1)) := by
  exact (Finset.mem_filter.mp hq).2

theorem positiveRowPairs_weight_eq
    {n : ℕ} (A X : Matrix (Fin n) (Fin n) ℝ)
    (M : Finset (RowPair n)) :
    rowMatchingWeight A X (positiveRowPairs A X M) =
      rowMatchingWeight A X M := by
  rw [rowMatchingWeight, rowMatchingWeight, positiveRowPairs]
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro q hqM hqfilter
  have hpos : ¬ 0 < Real.log
      (pairGain A X (rowPairRow q 0) (rowPairRow q 1)) := by
    intro h
    exact hqfilter (Finset.mem_filter.mpr ⟨hqM, h⟩)
  have hnonpos : Real.log
      (pairGain A X (rowPairRow q 0) (rowPairRow q 1)) ≤ 0 :=
    le_of_not_gt hpos
  simp [rowPairWeight, max_eq_left hnonpos]

theorem exists_positive_maximumRowMatching
    {n : ℕ} (A X : Matrix (Fin n) (Fin n) ℝ) :
    ∃ M : Finset (RowPair n), IsRowMatching M ∧
      rowMatchingWeight A X M = maximumMatchingGain A X ∧
      ∀ q ∈ M, 0 < Real.log
        (pairGain A X (rowPairRow q 0) (rowPairRow q 1)) := by
  obtain ⟨M, hM, hmax⟩ := exists_maximumRowMatching A X
  refine ⟨positiveRowPairs A X M, positiveRowPairs_isRowMatching hM,
    (positiveRowPairs_weight_eq A X M).trans hmax, ?_⟩
  intro q hq
  exact positiveRowPairs_logGain_pos hq

noncomputable def cleanCycleRowPair
    {n : ℕ} {η : ℝ} {P : Matrix (Fin n) (Fin n) ℝ}
    {f g : Equiv.Perm (Fin n)}
    (c : cleanCycleFactors η P (alternatingRowPerm f g)) : RowPair n :=
  ⟨(c.1 : Equiv.Perm (Fin n)).support,
    (cleanCycleFactor_property c).1⟩

theorem rowPairRow_cleanCycleRowPair
    {n : ℕ} {η : ℝ} {P : Matrix (Fin n) (Fin n) ℝ}
    {f g : Equiv.Perm (Fin n)}
    (c : cleanCycleFactors η P (alternatingRowPerm f g)) (k : Fin 2) :
    rowPairRow (cleanCycleRowPair c) k = cleanCycleRow c k := by
  rfl

theorem cleanCycleRowPair_injective
    {n : ℕ} {η : ℝ} {P : Matrix (Fin n) (Fin n) ℝ}
    {f g : Equiv.Perm (Fin n)} :
    Function.Injective
      (cleanCycleRowPair :
        cleanCycleFactors η P (alternatingRowPerm f g) → RowPair n) := by
  intro c d heq
  apply Subtype.ext
  by_contra hcd
  have hcd' : (c.1 : Equiv.Perm (Fin n)) ≠ d.1 := by
    intro h
    apply hcd
    exact Subtype.ext h
  have hdisj := (alternatingRowPerm f g).cycleFactorsFinset_pairwise_disjoint
    c.1.2 d.1.2 hcd' |>.disjoint_support
  have hsupp : (c.1 : Equiv.Perm (Fin n)).support =
      (d.1 : Equiv.Perm (Fin n)).support := congrArg Subtype.val heq
  have hr := cleanCycleRow_mem_support c 0
  exact (Finset.disjoint_left.mp hdisj) hr (by rwa [← hsupp])

noncomputable def successfulRowPairs
    {n : ℕ} (κ τ η : ℝ)
    (P X : Matrix (Fin n) (Fin n) ℝ)
    (f g : Equiv.Perm (Fin n)) : Finset (RowPair n) :=
  (successfulCleanCycles κ τ η P X f g).image cleanCycleRowPair

theorem successfulRowPairs_isRowMatching
    {n : ℕ} (κ τ η : ℝ)
    (P X : Matrix (Fin n) (Fin n) ℝ)
    (f g : Equiv.Perm (Fin n)) :
    IsRowMatching (successfulRowPairs κ τ η P X f g) := by
  intro q hq q' hq' hqq'
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hq'
  have hcd : c ≠ d := by
    intro heq
    subst d
    exact hqq' rfl
  have hcd' : (c.1 : Equiv.Perm (Fin n)) ≠ d.1 := by
    intro heq
    apply hcd
    exact Subtype.ext (Subtype.ext heq)
  exact (alternatingRowPerm f g).cycleFactorsFinset_pairwise_disjoint
    c.1.2 d.1.2 hcd' |>.disjoint_support

theorem successfulRowPairs_weight_eq
    {n : ℕ} {κ τ η : ℝ}
    {A P X : Matrix (Fin n) (Fin n) ℝ}
    (f g : Equiv.Perm (Fin n))
    (hpositive : ∀ c ∈ successfulCleanCycles κ τ η P X f g,
      0 ≤ Real.log
        (pairGain A X (cleanCycleRow c 0) (cleanCycleRow c 1))) :
    rowMatchingWeight A X (successfulRowPairs κ τ η P X f g) =
      ∑ c ∈ successfulCleanCycles κ τ η P X f g,
        Real.log (pairGain A X (cleanCycleRow c 0) (cleanCycleRow c 1)) := by
  rw [rowMatchingWeight, successfulRowPairs,
    Finset.sum_image (cleanCycleRowPair_injective.injOn)]
  apply Finset.sum_congr rfl
  intro c hc
  rw [rowPairWeight, rowPairRow_cleanCycleRowPair,
    rowPairRow_cleanCycleRowPair, max_eq_right (hpositive c hc)]

/-- The computable maximum-weight matching dominates the disjoint successful
clean pairs used only in the analysis. -/
theorem maximumMatchingGain_ge_successfulCleanCycles
    {n : ℕ} {κ τ η γ : ℝ}
    {A P X : Matrix (Fin n) (Fin n) ℝ}
    (f g : Equiv.Perm (Fin n))
    (hγ : 0 ≤ γ)
    (hpoint : ∀ c ∈ successfulCleanCycles κ τ η P X f g,
      γ ≤ Real.log
        (pairGain A X (cleanCycleRow c 0) (cleanCycleRow c 1))) :
    ((successfulCleanCycles κ τ η P X f g).card : ℝ) * γ ≤
      maximumMatchingGain A X := by
  have hpositive : ∀ c ∈ successfulCleanCycles κ τ η P X f g,
      0 ≤ Real.log
        (pairGain A X (cleanCycleRow c 0) (cleanCycleRow c 1)) := by
    intro c hc
    exact hγ.trans (hpoint c hc)
  have hsum : ((successfulCleanCycles κ τ η P X f g).card : ℝ) * γ ≤
      ∑ c ∈ successfulCleanCycles κ τ η P X f g,
        Real.log (pairGain A X (cleanCycleRow c 0) (cleanCycleRow c 1)) := by
    calc
      ((successfulCleanCycles κ τ η P X f g).card : ℝ) * γ =
          ∑ _c ∈ successfulCleanCycles κ τ η P X f g, γ := by simp
      _ ≤ _ := Finset.sum_le_sum hpoint
  rw [← successfulRowPairs_weight_eq f g hpositive] at hsum
  exact hsum.trans (rowMatchingWeight_le_maximum A X
    (successfulRowPairs_isRowMatching κ τ η P X f g))

/-- Once the three exceptional sets have the advertised sizes, the clean
pair lemma and disjointness give the full near-case matching gain. -/
theorem maximumMatchingGain_ge_threeEighths_of_structuralBounds
    {n : ℕ} (hn : 0 < n)
    {κ₀ ξ₀ γ₀ ell ξ τ η : ℝ}
    (hgain : CleanPairGainGuarantee κ₀ ξ₀ γ₀)
    (hκ₀ : 0 < κ₀) (hγ₀ : 0 ≤ γ₀)
    (hell : 1 ≤ ell) (hlogn : Real.log n ≤ ell * Real.log 2)
    (hξ : 0 < ξ) (hξ₀ : ξ ≤ ξ₀) (hτscale : τ = ξ / (4 * ell))
    {A P X : Matrix (Fin n) (Fin n) ℝ}
    (hA : Matrix.Positive A)
    (hP : ∀ i, IsStrictProbabilityVector (P i))
    (hPds : IsDoublyStochastic P)
    (hX : IsDoublyStochastic X)
    (hXint : ∀ i, IsInteriorProbabilityVector (X i))
    {R C : Fin n → ℝ} (hKKT : HasLogKKT τ A X R C)
    (f g : Equiv.Perm (Fin n))
    (hheavy : ∀ i j, j ∈ heavyCoordinates η (P i) →
      j = f i ∨ j = g i)
    (hηhalf : η < 1 / 2)
    (hbad : ((badRows η P).card : ℝ) ≤ n / 128)
    (hlong : (longCycleGoodRows η P (alternatingRowPerm f g) : ℝ) ≤
      n / 16)
    (hcore : coreTransferCost (fun i ↦ coreOutside (f i) (g i)) P
          (fun i j ↦ transferU τ (X i) j) / n ≤
        (1 / 16) * ((1 / 2 - η) * κ₀)) :
    3 * γ₀ / 8 * n ≤ maximumMatchingGain A X := by
  have hellpos : 0 < ell := lt_of_lt_of_le (by norm_num) hell
  have hτ : 0 ≤ τ := by
    rw [hτscale]
    positivity
  have hfactor : 0 ≤ 1 / 2 - η := (sub_pos.mpr hηhalf).le
  have hmin : 0 < (1 / 2 - η) * κ₀ :=
    mul_pos (sub_pos.mpr hηhalf) hκ₀
  have hfailed : ((failedCleanCycles κ₀ τ η P X f g).card : ℝ) ≤ n / 16 := by
    have hf := failedCleanCycles_count_le hn hP hPds hτ
      hfactor hmin hXint f g hheavy hcore
    nlinarith
  have hsuccess := successfulCleanCycles_count_ge_threeEighths hP f g
    hheavy hbad hlong hfailed
  have hmatching := maximumMatchingGain_ge_successfulCleanCycles
    (A := A) (P := P) (X := X) (κ := κ₀) (τ := τ) (η := η)
    (γ := γ₀) f g hγ₀
    (fun c hc ↦ successfulCleanCycle_gain hgain hell hlogn hξ hξ₀
      (P := P) (η := η) hτscale hA hX hXint hKKT f g c hc)
  have hfinal := matchingGain_ge_threeEighths hγ₀ hsuccess hmatching
  nlinarith

/-- The structural content of the near case, separated from the choice of
matching algorithm.  It produces two perfect matchings whose alternating
permutation contains at least `3n/8` successful clean two-cycles. -/
theorem nearCase_successfulCleanCycles_count_ge_threeEighths
    (hrowInequality : AnariRezaeiRowInequality)
    {n : ℕ} (hn : 2 ≤ n)
    {κ₀ ell ξ τ η δ : ℝ}
    (hκ₀ : 0 < κ₀)
    (hell : 1 ≤ ell) (hlogn : Real.log n ≤ ell * Real.log 2)
    (hξ : 0 < ξ) (hτscale : τ = ξ / (4 * ell))
    (hη : 0 < η) (hηtenth : η ≤ 1 / 10)
    (hrowSmall : δ / (η / 3074) ^ 4 ≤ 1 / 128)
    (hcycleSmall : 6 / Real.log 2 *
      (δ + (1 + Real.log 2 / 2) * (δ / (η / 3074) ^ 4) +
        goodRowOmega η) ≤ 1 / 16)
    (htransferSmall :
      δ + 2 * ξ + binaryEntropy η + η +
          (1 + Real.log 2) * (δ / (η / 3074) ^ 4) ≤
        (1 / 16) * ((1 / 2 - η) * κ₀))
    {A X : Matrix (Fin n) (Fin n) ℝ}
    (hA : Matrix.Positive A)
    (hX : IsDoublyStochastic X)
    (hXint : ∀ i, IsInteriorProbabilityVector (X i))
    {R C : Fin n → ℝ} (hKKT : HasLogKKT τ A X R C)
    (hnear : betheSlack n (betheLogValue A)
      (Real.log (Matrix.permanent A)) < δ * n) :
    ∃ f g : Equiv.Perm (Fin n),
      3 * n / 8 ≤
        ((successfulCleanCycles κ₀ τ η (assignmentMarginal A) X f g).card : ℝ) := by
  have hnpos : 0 < n := by omega
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hnpos
  let P := assignmentMarginal A
  let S := betheSlack n (betheLogValue A)
    (Real.log (Matrix.permanent A))
  let D := gibbsSequentialDivergence A
  have hPds : IsDoublyStochastic P := by
    exact assignmentMarginal_doublyStochastic A
      (fun i j ↦ (hA i j).le)
      (permanent_pos_of_positive A hA).ne'
  have hPstrict : ∀ i, IsStrictProbabilityVector (P i) :=
    assignmentMarginal_strictProbabilityVector A hA
  have hseq : Real.log (Matrix.permanent A) =
      betheObjective A P + (∑ i, rowCorrection (P i)) - D := by
    exact gibbs_exact_sequential_identity A hA
  have hdecomp : S =
      betheSuboptimality (betheLogValue A) (betheObjective A P) +
        (∑ i, rowDeficit (P i)) + D :=
    slack_decomposition_rowDeficit P hseq
  have hsub0 : 0 ≤
      betheSuboptimality (betheLogValue A) (betheObjective A P) := by
    rw [betheSuboptimality]
    exact sub_nonneg.mpr
      (betheObjective_le_betheLogValue_of_positive hA hPds)
  have hrow0 : 0 ≤ ∑ i, rowDeficit (P i) :=
    Finset.sum_nonneg fun i _ ↦ hrowInequality hn (P i) (hPstrict i).1
  have hD0 : 0 ≤ D := gibbsSequentialDivergence_nonneg A hA
  have hterms := terms_le_slack_of_decomposition hsub0 hrow0 hD0 hdecomp
  have hrowSum : (∑ i, rowDeficit (P i)) ≤ S := hterms.2.1
  have hDle : D ≤ S := hterms.2.2
  have hSlt : S < δ * n := by simpa only [S] using hnear
  have hd0 : 0 < (η / 3074) ^ 4 := pow_pos (div_pos hη (by norm_num)) 4
  have hbadRaw := badRow_count_le_slack hrowInequality hn hη hPstrict hrowSum
  have hquot : S / (η / 3074) ^ 4 <
      (δ / (η / 3074) ^ 4) * n := by
    calc
      S / (η / 3074) ^ 4 < (δ * n) / (η / 3074) ^ 4 :=
        (div_lt_div_iff_of_pos_right hd0).2 hSlt
      _ = (δ / (η / 3074) ^ 4) * n := by ring
  have hbadError : ((badRows η P).card : ℝ) ≤
      (δ / (η / 3074) ^ 4) * n :=
    hbadRaw.trans hquot.le
  have hbad : ((badRows η P).card : ℝ) ≤ n / 128 := by
    have hscaled := mul_le_mul_of_nonneg_right hrowSmall (Nat.cast_nonneg n)
    nlinarith
  obtain ⟨f, g, hheavy, hrobust⟩ :=
    exists_gibbs_robust_cycle_information A hA hη.le hηtenth
  have hlongRaw := longRow_count_le_cycleError
    (n := (n : ℝ)) (D := D)
    (N := (longCycleGoodRows η P (alternatingRowPerm f g) : ℝ))
    (bad := ((badRows η P).card : ℝ))
    (δ := δ) (rowError := δ / (η / 3074) ^ 4)
    (ω := goodRowOmega η)
    (cycleError := 6 / Real.log 2 *
      (δ + (1 + Real.log 2 / 2) * (δ / (η / 3074) ^ 4) +
        goodRowOmega η))
    (Nat.cast_nonneg n) (hDle.trans_lt hSlt).le
    hbadError
    (by simpa only [P, D] using hrobust) rfl
  have hlong : (longCycleGoodRows η P (alternatingRowPerm f g) : ℝ) ≤
      n / 16 := by
    have hscaled := mul_le_mul_of_nonneg_right hcycleSmall (Nat.cast_nonneg n)
    nlinarith
  have hbudget : τ * (n * Real.log n) ≤ ξ * n :=
    regularization_budget_of_paper_scale
      (lt_of_lt_of_le (by norm_num) hell) hlogn hξ hτscale
  have hτ : 0 ≤ τ := by rw [hτscale]; positivity
  have hcoreRaw := gibbs_twoMatching_coreTransferCost_normalized_le hnpos
    A hA hτ hbudget ⟨hη.le, hηtenth.trans (by norm_num)⟩ f g hheavy
    hX hXint hKKT
  have hSnorm : S / n < δ := (div_lt_iff₀ hnR).2 hSlt
  have hbadNorm : ((badRows η P).card : ℝ) / n ≤
      δ / (η / 3074) ^ 4 := by
    exact (div_le_iff₀ hnR).2 hbadError
  have hcore : coreTransferCost (fun i ↦ coreOutside (f i) (g i)) P
          (fun i j ↦ transferU τ (X i) j) / n ≤
        (1 / 16) * ((1 / 2 - η) * κ₀) := by
    have hraw : coreTransferCost (fun i ↦ coreOutside (f i) (g i)) P
          (fun i j ↦ transferU τ (X i) j) / n ≤
        S / n + 2 * ξ + binaryEntropy η + η +
          (1 + Real.log 2) * ((badRows η P).card : ℝ) / n := by
      simpa only [P, S] using hcoreRaw
    have hbadCoeff : 0 ≤ 1 + Real.log 2 := by
      have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
      linarith
    have htail := mul_le_mul_of_nonneg_left hbadNorm hbadCoeff
    have hraw' : coreTransferCost (fun i ↦ coreOutside (f i) (g i)) P
          (fun i j ↦ transferU τ (X i) j) / n ≤
        S / n + 2 * ξ + binaryEntropy η + η +
          (1 + Real.log 2) * (((badRows η P).card : ℝ) / n) := by
      convert hraw using 1 <;> ring
    linarith
  have hfactor : 0 ≤ 1 / 2 - η :=
    (sub_pos.mpr (hηtenth.trans_lt (by norm_num))).le
  have hmin : 0 < (1 / 2 - η) * κ₀ :=
    mul_pos (sub_pos.mpr (hηtenth.trans_lt (by norm_num))) hκ₀
  have hfailed : ((failedCleanCycles κ₀ τ η P X f g).card : ℝ) ≤
      n / 16 := by
    have hf := failedCleanCycles_count_le hnpos hPstrict hPds hτ
      hfactor hmin hXint f g hheavy hcore
    nlinarith
  have hsuccess := successfulCleanCycles_count_ge_threeEighths hPstrict f g
    hheavy hbad hlong hfailed
  refine ⟨f, g, ?_⟩
  simpa only [P] using hsuccess

/-- Full structural near case for a positive matrix.  The three displayed
smallness hypotheses are exactly the row, long-cycle, and transfer choices in
the paper's completion section. -/
theorem nearCase_maximumMatchingGain_ge_threeEighths
    (hrowInequality : AnariRezaeiRowInequality)
    {n : ℕ} (hn : 2 ≤ n)
    {κ₀ ξ₀ γ₀ ell ξ τ η δ : ℝ}
    (hgain : CleanPairGainGuarantee κ₀ ξ₀ γ₀)
    (hκ₀ : 0 < κ₀) (hγ₀ : 0 ≤ γ₀)
    (hell : 1 ≤ ell) (hlogn : Real.log n ≤ ell * Real.log 2)
    (hξ : 0 < ξ) (hξ₀ : ξ ≤ ξ₀) (hτscale : τ = ξ / (4 * ell))
    (hη : 0 < η) (hηtenth : η ≤ 1 / 10)
    (hrowSmall : δ / (η / 3074) ^ 4 ≤ 1 / 128)
    (hcycleSmall : 6 / Real.log 2 *
      (δ + (1 + Real.log 2 / 2) * (δ / (η / 3074) ^ 4) +
        goodRowOmega η) ≤ 1 / 16)
    (htransferSmall :
      δ + 2 * ξ + binaryEntropy η + η +
          (1 + Real.log 2) * (δ / (η / 3074) ^ 4) ≤
        (1 / 16) * ((1 / 2 - η) * κ₀))
    {A X : Matrix (Fin n) (Fin n) ℝ}
    (hA : Matrix.Positive A)
    (hX : IsDoublyStochastic X)
    (hXint : ∀ i, IsInteriorProbabilityVector (X i))
    {R C : Fin n → ℝ} (hKKT : HasLogKKT τ A X R C)
    (hnear : betheSlack n (betheLogValue A)
      (Real.log (Matrix.permanent A)) < δ * n) :
    3 * γ₀ / 8 * n ≤ maximumMatchingGain A X := by
  obtain ⟨f, g, hsuccess⟩ :=
    nearCase_successfulCleanCycles_count_ge_threeEighths hrowInequality hn
      hκ₀ hell hlogn hξ hτscale hη hηtenth hrowSmall hcycleSmall
      htransferSmall hA hX hXint hKKT hnear
  have hmatching := maximumMatchingGain_ge_successfulCleanCycles
    (A := A) (P := assignmentMarginal A) (X := X)
    (κ := κ₀) (τ := τ) (η := η) (γ := γ₀) f g hγ₀
    (fun c hc ↦ successfulCleanCycle_gain hgain hell hlogn hξ hξ₀
      hτscale hA hX hXint hKKT f g c hc)
  have hfinal := matchingGain_ge_threeEighths hγ₀ hsuccess hmatching
  nlinarith

theorem rowPairRow_mem
    {n : ℕ} (q : RowPair n) (k : Fin 2) : rowPairRow q k ∈ q.1 := by
  exact (q.1.orderIsoOfFin q.2 k).2

theorem rowPairRow_injective
    {n : ℕ} (q : RowPair n) : Function.Injective (rowPairRow q) := by
  intro k l hkl
  apply (q.1.orderIsoOfFin q.2).injective
  exact Subtype.ext hkl

theorem rowPairRow_ne
    {n : ℕ} (q : RowPair n) : rowPairRow q 0 ≠ rowPairRow q 1 := by
  intro h
  have hk := rowPairRow_injective q h
  norm_num at hk

noncomputable def matchingRows
    {n : ℕ} (M : Finset (RowPair n)) : Finset (Fin n) :=
  M.biUnion fun q ↦ q.1

abbrev UnmatchedRow {n : ℕ} (M : Finset (RowPair n)) :=
  {i : Fin n // i ∉ matchingRows M}

abbrev MatchingCluster {n : ℕ} (M : Finset (RowPair n)) :=
  M ⊕ UnmatchedRow M

def matchingClusterSize
    {n : ℕ} {M : Finset (RowPair n)} : MatchingCluster M → ℕ
  | Sum.inl _ => 2
  | Sum.inr _ => 1

noncomputable def matchingRowMap
    {n : ℕ} (M : Finset (RowPair n)) :
    (Σ c : MatchingCluster M, Fin (matchingClusterSize c)) → Fin n
  | ⟨Sum.inl q, k⟩ => rowPairRow q.1 k
  | ⟨Sum.inr i, _⟩ => i.1

theorem matchingRowMap_bijective
    {n : ℕ} {M : Finset (RowPair n)} (hM : IsRowMatching M) :
    Function.Bijective (matchingRowMap M) := by
  constructor
  · rintro ⟨c, k⟩ ⟨d, l⟩ heq
    rcases c with q | i <;> rcases d with q' | i'
    · change Fin 2 at k l
      change rowPairRow q.1 k = rowPairRow q'.1 l at heq
      have hqq : q = q' := by
        by_contra hne
        have hne' : q.1 ≠ q'.1 := by
          intro h
          exact hne (Subtype.ext h)
        have hdisj := hM q.2 q'.2 hne'
        exact (Finset.disjoint_left.mp hdisj)
          (rowPairRow_mem q.1 k) (by rw [heq]; exact rowPairRow_mem q'.1 l)
      subst q'
      have hkl : k = l := rowPairRow_injective q.1 heq
      subst l
      rfl
    · change Fin 2 at k
      change rowPairRow q.1 k = i'.1 at heq
      have hmatched : rowPairRow q.1 k ∈ matchingRows M := by
        exact Finset.mem_biUnion.mpr ⟨q.1, q.2, rowPairRow_mem q.1 k⟩
      have : i'.1 ∈ matchingRows M := by rwa [← heq]
      exact False.elim (i'.2 this)
    · change Fin 2 at l
      change i.1 = rowPairRow q'.1 l at heq
      have hmatched : rowPairRow q'.1 l ∈ matchingRows M := by
        exact Finset.mem_biUnion.mpr ⟨q'.1, q'.2, rowPairRow_mem q'.1 l⟩
      have : i.1 ∈ matchingRows M := by rwa [heq]
      exact False.elim (i.2 this)
    · have hii : i = i' := Subtype.ext heq
      subst i'
      change Fin 1 at k l
      have hkl : k = l := Subsingleton.elim _ _
      subst l
      rfl
  · intro i
    by_cases hi : i ∈ matchingRows M
    · obtain ⟨q, hqM, hiq⟩ := Finset.mem_biUnion.mp hi
      let qM : M := ⟨q, hqM⟩
      obtain ⟨k, hk⟩ := (q.1.orderIsoOfFin q.2).surjective ⟨i, hiq⟩
      exact ⟨⟨Sum.inl qM, k⟩, by exact congrArg Subtype.val hk⟩
    · let k : Fin (matchingClusterSize (Sum.inr ⟨i, hi⟩ : MatchingCluster M)) :=
        ⟨0, by simp [matchingClusterSize]⟩
      exact ⟨⟨Sum.inr ⟨i, hi⟩, k⟩, rfl⟩

/-- The row-labeling equivalence, written with an explicit forward map so its
action on a cluster is transparent to subsequent proofs. -/
noncomputable def matchingRowsEquiv
    {n : ℕ} (M : Finset (RowPair n)) (hM : IsRowMatching M) :
    (Σ c : MatchingCluster M, Fin (matchingClusterSize c)) ≃ Fin n where
  toFun := matchingRowMap M
  invFun := Function.surjInv (matchingRowMap_bijective hM).2
  left_inv := Function.leftInverse_surjInv (matchingRowMap_bijective hM)
  right_inv := Function.rightInverse_surjInv _

@[simp] theorem matchingRowsEquiv_apply
    {n : ℕ} (M : Finset (RowPair n)) (hM : IsRowMatching M)
    (x : Σ c : MatchingCluster M, Fin (matchingClusterSize c)) :
    matchingRowsEquiv M hM x = matchingRowMap M x := rfl

/-- Convert a disjoint row matching into the singleton/pair clustering used
by the paired-certificate theorem. -/
noncomputable def rowClusteringOfMatching
    {n : ℕ} (M : Finset (RowPair n)) (hM : IsRowMatching M) :
    RowClustering n where
  Cluster := MatchingCluster M
  clusterFintype := inferInstance
  clusterDecidableEq := Classical.decEq _
  size := matchingClusterSize
  rows := matchingRowsEquiv M hM

theorem rowClusteringOfMatching_singletonPairs
    {n : ℕ} (M : Finset (RowPair n)) (hM : IsRowMatching M) :
    IsSingletonPairClustering (rowClusteringOfMatching M hM) := by
  intro c
  rcases c with q | i
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem singletonClusterRow_rowClusteringOfMatching
    {n : ℕ} (M : Finset (RowPair n)) (hM : IsRowMatching M)
    (i : UnmatchedRow M) :
    singletonClusterRow (rowClusteringOfMatching M hM) (Sum.inr i) rfl = i.1 := by
  rfl

theorem pairClusterRow_rowClusteringOfMatching
    {n : ℕ} (M : Finset (RowPair n)) (hM : IsRowMatching M)
    (q : M) (k : Fin 2) :
    pairClusterRow (rowClusteringOfMatching M hM) (Sum.inl q) rfl k =
      rowPairRow q.1 k := by
  rfl

theorem rowClusteringOfMatching_rows_pair
    {n : ℕ} (M : Finset (RowPair n)) (hM : IsRowMatching M)
    (q : M) (k : Fin 2) :
    (rowClusteringOfMatching M hM).rows ⟨Sum.inl q, k⟩ =
      rowPairRow q.1 k := by
  rfl

theorem rowClusteringOfMatching_rows_singleton
    {n : ℕ} (M : Finset (RowPair n)) (hM : IsRowMatching M)
    (i : UnmatchedRow M) (k : Fin 1) :
    (rowClusteringOfMatching M hM).rows ⟨Sum.inr i, k⟩ = i.1 := by
  have hk : k = 0 := Subsingleton.elim _ _
  subst k
  rfl

theorem pairCertificateValue_nonneg
    {n : ℕ} {A X : Matrix (Fin n) (Fin n) ℝ}
    (hA : Matrix.Nonnegative A) (hX : IsDoublyStochastic X)
    {r s : Fin n} (hrs : r ≠ s) :
    0 ≤ pairCertificateValue A X r s := by
  rw [pairCertificateValue]
  apply mul_nonneg
  · exact Finset.prod_nonneg fun j _ ↦ Real.rpow_nonneg
      (sub_nonneg.mpr (pairAlpha_le_one hX hrs j)) _
  · exact polynomialCapacity_nonneg
      (pairPolynomial_nonnegativeCoefficients (hA r) (hA s)) _

/-- Algebraic meaning of the gain ratio: a pair factor is its gain times the
two singleton factors that it replaces. -/
theorem pairCertificateValue_eq_pairGain_mul_singletons
    {n : ℕ} {A X : Matrix (Fin n) (Fin n) ℝ}
    (hcard : 2 ≤ n) (hA : Matrix.Positive A)
    (hX : IsDoublyStochastic X) (hXpos : ∀ i j, 0 < X i j)
    (r s : Fin n) :
    pairCertificateValue A X r s =
      pairGain A X r s * (singletonFactor A X r * singletonFactor A X s) := by
  have hr := singletonProductValue_eq_singletonFactor hcard hA hX hXpos r
  have hs := singletonProductValue_eq_singletonFactor hcard hA hX hXpos s
  have hden : singletonFactor A X r * singletonFactor A X s ≠ 0 :=
    mul_ne_zero (Real.exp_ne_zero _) (Real.exp_ne_zero _)
  rw [pairGain, hr, hs]
  exact (div_mul_cancel₀ _ hden).symm

theorem pairCertificateValue_eq_exp_logGain_mul_singletons
    {n : ℕ} {A X : Matrix (Fin n) (Fin n) ℝ}
    (hcard : 2 ≤ n) (hA : Matrix.Positive A)
    (hX : IsDoublyStochastic X) (hXpos : ∀ i j, 0 < X i j)
    (r s : Fin n) (hrs : r ≠ s)
    (hgain : 0 < Real.log (pairGain A X r s)) :
    pairCertificateValue A X r s =
      Real.exp (Real.log (pairGain A X r s)) *
        (singletonFactor A X r * singletonFactor A X s) := by
  have hgain0 : 0 ≤ pairGain A X r s := by
    have hr := singletonProductValue_eq_singletonFactor hcard hA hX hXpos r
    have hs := singletonProductValue_eq_singletonFactor hcard hA hX hXpos s
    have hden : 0 ≤ singletonProductValue A X r * singletonProductValue A X s := by
      rw [hr, hs]
      exact mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
    rw [pairGain]
    exact div_nonneg (pairCertificateValue_nonneg
        (fun i j ↦ (hA i j).le) hX hrs)
      hden
  have hone : 1 < pairGain A X r s := (Real.log_pos_iff hgain0).mp hgain
  rw [Real.exp_log (zero_lt_one.trans hone)]
  exact pairCertificateValue_eq_pairGain_mul_singletons hcard hA hX hXpos r s

noncomputable def matchingClusterLogGain
    {n : ℕ} (A X : Matrix (Fin n) (Fin n) ℝ)
    {M : Finset (RowPair n)} : MatchingCluster M → ℝ
  | Sum.inl q => Real.log
      (pairGain A X (rowPairRow q.1 0) (rowPairRow q.1 1))
  | Sum.inr _ => 0

theorem sum_matchingClusterLogGain_eq_rowMatchingWeight
    {n : ℕ} {A X : Matrix (Fin n) (Fin n) ℝ}
    {M : Finset (RowPair n)}
    (hpositive : ∀ q ∈ M, 0 < Real.log
      (pairGain A X (rowPairRow q 0) (rowPairRow q 1))) :
    ∑ c : MatchingCluster M, matchingClusterLogGain A X c =
      rowMatchingWeight A X M := by
  rw [Fintype.sum_sum_type]
  simp only [matchingClusterLogGain]
  have hzero : (∑ _i : UnmatchedRow M, (0 : ℝ)) = 0 := by simp
  rw [hzero, add_zero]
  calc
    (∑ q : M, Real.log
        (pairGain A X (rowPairRow q.1 0) (rowPairRow q.1 1))) =
        ∑ q ∈ M, Real.log
          (pairGain A X (rowPairRow q 0) (rowPairRow q 1)) :=
      by
        simpa using (Finset.sum_coe_sort M (fun q : RowPair n ↦
          Real.log (pairGain A X (rowPairRow q 0) (rowPairRow q 1))))
    _ = rowMatchingWeight A X M := by
      rw [rowMatchingWeight]
      apply Finset.sum_congr rfl
      intro q hq
      rw [rowPairWeight, max_eq_right (hpositive q hq).le]

theorem paperClusterFactor_rowClusteringOfMatching
    {n : ℕ} {A X : Matrix (Fin n) (Fin n) ℝ}
    {M : Finset (RowPair n)} (hM : IsRowMatching M)
    (hcard : 2 ≤ n) (hA : Matrix.Positive A)
    (hX : IsDoublyStochastic X) (hXpos : ∀ i j, 0 < X i j)
    (hpositive : ∀ q ∈ M, 0 < Real.log
      (pairGain A X (rowPairRow q 0) (rowPairRow q 1)))
    (c : MatchingCluster M) :
    paperClusterFactor A X (rowClusteringOfMatching M hM)
        (rowClusteringOfMatching_singletonPairs M hM) c =
      Real.exp (matchingClusterLogGain A X c) *
        ∏ k, singletonFactor A X
          ((rowClusteringOfMatching M hM).rows ⟨c, k⟩) := by
  rcases c with q | i
  · change pairCertificateValue A X (rowPairRow q.1 0) (rowPairRow q.1 1) = _
    rw [pairCertificateValue_eq_exp_logGain_mul_singletons hcard hA hX hXpos
      (rowPairRow q.1 0) (rowPairRow q.1 1) (rowPairRow_ne q.1)
      (hpositive q.1 q.2)]
    rw [matchingClusterLogGain]
    change Real.exp (Real.log (pairGain A X (rowPairRow q.1 0) (rowPairRow q.1 1))) *
      (singletonFactor A X (rowPairRow q.1 0) * singletonFactor A X (rowPairRow q.1 1)) =
      Real.exp (Real.log (pairGain A X (rowPairRow q.1 0) (rowPairRow q.1 1))) *
        ∏ k : Fin 2, singletonFactor A X (rowPairRow q.1 k)
    have hprod := Fin.prod_univ_two (fun k : Fin 2 ↦
      singletonFactor A X (rowPairRow q.1 k))
    exact congrArg (Real.exp
      (Real.log (pairGain A X (rowPairRow q.1 0) (rowPairRow q.1 1))) * ·)
      hprod.symm
  · change singletonFactor A X i.1 = _
    change singletonFactor A X i.1 = Real.exp 0 *
      ∏ _k : Fin 1, singletonFactor A X i.1
    simp

theorem prod_paperClusterFactor_rowClusteringOfMatching
    {n : ℕ} {A X : Matrix (Fin n) (Fin n) ℝ}
    {M : Finset (RowPair n)} (hM : IsRowMatching M)
    (hcard : 2 ≤ n) (hA : Matrix.Positive A)
    (hX : IsDoublyStochastic X) (hXpos : ∀ i j, 0 < X i j)
    (hpositive : ∀ q ∈ M, 0 < Real.log
      (pairGain A X (rowPairRow q 0) (rowPairRow q 1))) :
    (∏ c, paperClusterFactor A X (rowClusteringOfMatching M hM)
        (rowClusteringOfMatching_singletonPairs M hM) c) =
      Real.exp (betheObjective A X + rowMatchingWeight A X M) := by
  let hclusters := rowClusteringOfMatching_singletonPairs M hM
  calc
    (∏ c, paperClusterFactor A X (rowClusteringOfMatching M hM) hclusters c) =
        ∏ c, (Real.exp (matchingClusterLogGain A X c) *
          ∏ k, singletonFactor A X
            ((rowClusteringOfMatching M hM).rows ⟨c, k⟩)) := by
      apply Finset.prod_congr rfl
      intro c _
      exact paperClusterFactor_rowClusteringOfMatching hM hcard hA hX hXpos
        hpositive c
    _ = (∏ c, Real.exp (matchingClusterLogGain A X c)) *
        ∏ c, ∏ k, singletonFactor A X
          ((rowClusteringOfMatching M hM).rows ⟨c, k⟩) := by
      exact Finset.prod_mul_distrib
    _ = Real.exp (∑ c : MatchingCluster M, matchingClusterLogGain A X c) *
        ∏ s : Σ c : (rowClusteringOfMatching M hM).Cluster,
            Fin ((rowClusteringOfMatching M hM).size c),
          singletonFactor A X ((rowClusteringOfMatching M hM).rows s) := by
      rw [Real.exp_sum, ← Fintype.prod_sigma']
    _ = Real.exp (rowMatchingWeight A X M) *
        ∏ i, singletonFactor A X i := by
      rw [sum_matchingClusterLogGain_eq_rowMatchingWeight hpositive]
      exact congrArg (Real.exp (rowMatchingWeight A X M) * ·)
        (Equiv.prod_comp (rowClusteringOfMatching M hM).rows
          (singletonFactor A X))
    _ = Real.exp (rowMatchingWeight A X M) *
        Real.exp (betheObjective A X) := by
      rw [prod_singletonFactor_eq_exp_betheObjective]
    _ = Real.exp (betheObjective A X + rowMatchingWeight A X M) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- Every positive-gain row matching produces a certified lower bound. -/
theorem exp_betheObjective_add_rowMatchingWeight_le_permanent
    {n : ℕ}
    (stableCoefficient : AnariOveisGharanStableCoefficient.{0})
    {A X : Matrix (Fin n) (Fin n) ℝ}
    {M : Finset (RowPair n)} (hM : IsRowMatching M)
    (hcard : 2 ≤ n) (hA : Matrix.Positive A)
    (hX : IsDoublyStochastic X) (hXpos : ∀ i j, 0 < X i j)
    (hpositive : ∀ q ∈ M, 0 < Real.log
      (pairGain A X (rowPairRow q 0) (rowPairRow q 1))) :
    Real.exp (betheObjective A X + rowMatchingWeight A X M) ≤
      Matrix.permanent A := by
  rw [← prod_paperClusterFactor_rowClusteringOfMatching hM hcard hA hX
    hXpos hpositive]
  exact pairedLowerCertificate_for_clustering stableCoefficient
    (rowClusteringOfMatching M hM) hcard hA hX hXpos
    (rowClusteringOfMatching_singletonPairs M hM)

/-- The output based on a maximum-weight row matching remains below the
permanent.  Zero-gain edges are deleted before applying the cluster theorem. -/
theorem exp_betheObjective_add_maximumMatchingGain_le_permanent
    {n : ℕ}
    (stableCoefficient : AnariOveisGharanStableCoefficient.{0})
    {A X : Matrix (Fin n) (Fin n) ℝ}
    (hcard : 2 ≤ n) (hA : Matrix.Positive A)
    (hX : IsDoublyStochastic X) (hXpos : ∀ i j, 0 < X i j) :
    Real.exp (betheObjective A X + maximumMatchingGain A X) ≤
      Matrix.permanent A := by
  obtain ⟨M, hM, hmax, hpositive⟩ := exists_positive_maximumRowMatching A X
  rw [← hmax]
  exact exp_betheObjective_add_rowMatchingWeight_le_permanent
    stableCoefficient hM hcard hA hX hXpos hpositive

/-- Positive-matrix form of Proposition 20.  Vontobel's concavity theorem,
the sharp row inequality, and the upper Bethe bound are proved internally. -/
theorem positiveMatrix_logApproximation
    (stableCoefficient : AnariOveisGharanStableCoefficient.{0})
    {n : ℕ} (hn : 2 ≤ n)
    {κ₀ ξ₀ γ₀ ell ξ τ η δ : ℝ}
    (hgain : CleanPairGainGuarantee κ₀ ξ₀ γ₀)
    (hκ₀ : 0 < κ₀) (hγ₀ : 0 < γ₀)
    (hell : 1 ≤ ell) (hlogn : Real.log n ≤ ell * Real.log 2)
    (hξ : 0 < ξ) (hξ₀ : ξ ≤ ξ₀) (hτscale : τ = ξ / (4 * ell))
    (hη : 0 < η) (hηtenth : η ≤ 1 / 10)
    (hrowSmall : δ / (η / 3074) ^ 4 ≤ 1 / 128)
    (hcycleSmall : 6 / Real.log 2 *
      (δ + (1 + Real.log 2 / 2) * (δ / (η / 3074) ^ 4) +
        goodRowOmega η) ≤ 1 / 16)
    (htransferSmall :
      δ + 2 * ξ + binaryEntropy η + η +
          (1 + Real.log 2) * (δ / (η / 3074) ^ 4) ≤
        (1 / 16) * ((1 / 2 - η) * κ₀))
    (hξδ : ξ < δ) (hξγ : ξ < 3 * γ₀ / 8)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : Matrix.Positive A) :
    0 < epsilonPlus δ ξ γ₀ ∧
      ∃ X : Matrix (Fin n) (Fin n) ℝ,
        IsDoublyStochastic X ∧
        (∀ i, IsInteriorProbabilityVector (X i)) ∧
        Real.exp (betheObjective A X + maximumMatchingGain A X) ≤
          Matrix.permanent A ∧
        Real.log (Matrix.permanent A) -
            (betheObjective A X + maximumMatchingGain A X) ≤
          (Real.log 2 / 2 - epsilonPlus δ ξ γ₀) * n := by
  obtain ⟨X, hX, hXint, _hmax, ⟨R, C, hKKT⟩, hobjective⟩ :=
    exists_regularizedOptimizer_at_paper_scale
      (show 1 < n by omega) (lt_of_lt_of_le (by norm_num) hell)
      hlogn hξ hτscale A hA
  have hmatch := positiveMatrix_hasPerfectMatching hA
  have hlogBethe : Real.log (bethePermanent A) = betheLogValue A := by
    rw [bethePermanent, ite_eq_left hmatch, Real.log_exp]
  have hupper : Real.log (Matrix.permanent A) ≤
      Real.log (bethePermanent A) + n * (Real.log 2 / 2) := by
    rw [hlogBethe]
    exact log_permanent_le_betheLogValue_add_log_two_half hn A hA
  have hcertificate :=
    exp_betheObjective_add_maximumMatchingGain_le_permanent
      stableCoefficient hn hA hX (fun i j ↦ (hXint i).2 j |>.1)
  have hnearGain : betheSlack n (Real.log (bethePermanent A))
      (Real.log (Matrix.permanent A)) < δ * n →
      3 * γ₀ / 8 * n ≤ maximumMatchingGain A X := by
    intro hnear
    rw [hlogBethe] at hnear
    exact nearCase_maximumMatchingGain_ge_threeEighths
      anariRezaeiRowInequality hn
      hgain hκ₀ hγ₀.le hell hlogn hξ hξ₀ hτscale hη hηtenth
      hrowSmall hcycleSmall htransferSmall hA hX hXint hKKT hnear
  have hcases := completionCaseDisjunction
    (logPermanent := Real.log (Matrix.permanent A))
    (logBethe := Real.log (bethePermanent A))
    (objective := betheObjective A X)
    (gain := maximumMatchingGain A X)
    (δ := δ) (ξ := ξ) (γ := γ₀)
    hobjective (maximumMatchingGain_nonneg A X) hupper hnearGain
  have hgap := positiveDichotomy_exponent hcases
  exact ⟨epsilonPlus_pos hξδ hξγ, X, hX, hXint, hcertificate, hgap⟩

/-- The hierarchy of absolute scales used in the completion exists.  We
parameterize `δ` as a small multiple of `(η/3074)^4`; this makes the apparent
singularity in the row-error ratio disappear. -/
theorem exists_completion_scales
    {κ₀ ξ₀ γ₀ : ℝ} (hκ₀ : 0 < κ₀) (hξ₀ : 0 < ξ₀) (hγ₀ : 0 < γ₀) :
    ∃ η δ ξ : ℝ,
      0 < η ∧ η ≤ 1 / 10 ∧ 0 < δ ∧ 0 < ξ ∧ ξ ≤ ξ₀ ∧
      δ / (η / 3074) ^ 4 ≤ 1 / 128 ∧
      6 / Real.log 2 *
        (δ + (1 + Real.log 2 / 2) * (δ / (η / 3074) ^ 4) +
          goodRowOmega η) ≤ 1 / 16 ∧
      δ + 2 * ξ + binaryEntropy η + η +
          (1 + Real.log 2) * (δ / (η / 3074) ^ 4) ≤
        (1 / 16) * ((1 / 2 - η) * κ₀) ∧
      ξ < δ ∧ ξ < 3 * γ₀ / 8 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hωtarget : 0 < Real.log 2 / 384 := div_pos hlog (by norm_num)
  have hωevent : {x : ℝ | goodRowOmega x < Real.log 2 / 384} ∈ nhds 0 :=
    tendsto_goodRowOmega_zero (isOpen_Iio.mem_nhds hωtarget)
  have hHcont : ContinuousAt (fun x : ℝ ↦ binaryEntropy x + x) 0 :=
    continuous_binaryEntropy.continuousAt.add continuousAt_id
  have hHtarget : 0 < κ₀ / 256 := div_pos hκ₀ (by norm_num)
  have hHevent : {x : ℝ | binaryEntropy x + x < κ₀ / 256} ∈ nhds 0 := by
    exact hHcont.eventually (isOpen_Iio.mem_nhds (by
      simpa [binaryEntropy] using hHtarget))
  have hevent := Filter.inter_mem hωevent hHevent
  rw [Metric.mem_nhds_iff] at hevent
  obtain ⟨a, ha, hball⟩ := hevent
  let η : ℝ := min (a / 2) (1 / 20)
  have hη : 0 < η := lt_min (half_pos ha) (by norm_num)
  have hηtwenty : η ≤ 1 / 20 := min_le_right _ _
  have hηa : η < a := (min_le_left _ _).trans_lt (half_lt_self ha)
  have hηmem := hball (by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hη]
    exact hηa)
  have hωsmall : goodRowOmega η < Real.log 2 / 384 := hηmem.1
  have hHsmall : binaryEntropy η + η < κ₀ / 256 := hηmem.2
  have hηtenth : η ≤ 1 / 10 := hηtwenty.trans (by norm_num)
  have hcycleBase : 6 / Real.log 2 * goodRowOmega η < 1 / 64 := by
    have hcoef : 0 < 6 / Real.log 2 := div_pos (by norm_num) hlog
    calc
      6 / Real.log 2 * goodRowOmega η <
          6 / Real.log 2 * (Real.log 2 / 384) :=
        mul_lt_mul_of_pos_left hωsmall hcoef
      _ = 1 / 64 := by field_simp [hlog.ne'] <;> norm_num
  have hηκ : η * κ₀ ≤ (1 / 20) * κ₀ :=
    mul_le_mul_of_nonneg_right hηtwenty hκ₀.le
  have htransferBase : binaryEntropy η + η <
      (1 / 16) * ((1 / 2 - η) * κ₀) := by
    nlinarith
  let cycleMargin : ℝ := 1 / 16 - 6 / Real.log 2 * goodRowOmega η
  let transferMargin : ℝ :=
    (1 / 16) * ((1 / 2 - η) * κ₀) - (binaryEntropy η + η)
  have hcycleMargin : 0 < cycleMargin := by
    dsimp only [cycleMargin]
    linarith
  have htransferMargin : 0 < transferMargin := by
    dsimp only [transferMargin]
    linarith
  let d₀ : ℝ := (η / 3074) ^ 4
  have hd₀ : 0 < d₀ := pow_pos (div_pos hη (by norm_num)) 4
  let cycleCoefficient : ℝ :=
    6 / Real.log 2 * (d₀ + (1 + Real.log 2 / 2))
  have hcycleCoefficient : 0 < cycleCoefficient := by
    dsimp only [cycleCoefficient]
    have hc : 0 < d₀ + (1 + Real.log 2 / 2) := by positivity
    exact mul_pos (div_pos (by norm_num) hlog) hc
  let transferCoefficient : ℝ := d₀ + (1 + Real.log 2)
  have htransferCoefficient : 0 < transferCoefficient := by
    dsimp only [transferCoefficient]
    positivity
  let r : ℝ := min (1 / 128)
    (min (cycleMargin / (2 * cycleCoefficient))
      (transferMargin / (2 * transferCoefficient)))
  have hr : 0 < r := by
    dsimp only [r]
    exact lt_min (by norm_num) (lt_min
      (div_pos hcycleMargin (mul_pos (by norm_num) hcycleCoefficient))
      (div_pos htransferMargin (mul_pos (by norm_num) htransferCoefficient)))
  have hr128 : r ≤ 1 / 128 := min_le_left _ _
  have hrcycle : r ≤ cycleMargin / (2 * cycleCoefficient) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hrtransfer : r ≤ transferMargin / (2 * transferCoefficient) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hcycleExtra : cycleCoefficient * r ≤ cycleMargin / 2 := by
    calc
      cycleCoefficient * r ≤
          cycleCoefficient * (cycleMargin / (2 * cycleCoefficient)) :=
        mul_le_mul_of_nonneg_left hrcycle hcycleCoefficient.le
      _ = cycleMargin / 2 := by field_simp [hcycleCoefficient.ne']
  have htransferExtra : transferCoefficient * r ≤ transferMargin / 2 := by
    calc
      transferCoefficient * r ≤
          transferCoefficient * (transferMargin / (2 * transferCoefficient)) :=
        mul_le_mul_of_nonneg_left hrtransfer htransferCoefficient.le
      _ = transferMargin / 2 := by field_simp [htransferCoefficient.ne']
  let δ : ℝ := d₀ * r
  have hδ : 0 < δ := mul_pos hd₀ hr
  have hratio : δ / (η / 3074) ^ 4 = r := by
    change d₀ * r / d₀ = r
    exact mul_div_cancel_left₀ r hd₀.ne'
  have hcycle : 6 / Real.log 2 *
      (δ + (1 + Real.log 2 / 2) * (δ / (η / 3074) ^ 4) +
        goodRowOmega η) < 1 / 16 := by
    rw [hratio]
    have hid : 6 / Real.log 2 *
        (δ + (1 + Real.log 2 / 2) * r + goodRowOmega η) =
        6 / Real.log 2 * goodRowOmega η + cycleCoefficient * r := by
      dsimp only [δ, cycleCoefficient]
      dsimp only [d₀]
      ring
    rw [hid]
    dsimp only [cycleMargin] at hcycleExtra
    linarith
  have htransferZero :
      δ + binaryEntropy η + η +
          (1 + Real.log 2) * (δ / (η / 3074) ^ 4) <
        (1 / 16) * ((1 / 2 - η) * κ₀) := by
    rw [hratio]
    have hid : δ + binaryEntropy η + η + (1 + Real.log 2) * r =
        (binaryEntropy η + η) + transferCoefficient * r := by
      dsimp only [δ, transferCoefficient]
      ring
    rw [hid]
    dsimp only [transferMargin] at htransferExtra
    linarith
  let remaining : ℝ := (1 / 16) * ((1 / 2 - η) * κ₀) -
    (δ + binaryEntropy η + η +
      (1 + Real.log 2) * (δ / (η / 3074) ^ 4))
  have hremaining : 0 < remaining := by
    dsimp only [remaining]
    linarith
  let ξ : ℝ := min (ξ₀ / 2)
    (min (δ / 2) (min (3 * γ₀ / 16) (remaining / 4)))
  have hξ : 0 < ξ := by
    dsimp only [ξ]
    exact lt_min (half_pos hξ₀) (lt_min (half_pos hδ) (lt_min
      (div_pos (mul_pos (by norm_num) hγ₀) (by norm_num))
      (div_pos hremaining (by norm_num))))
  have hξξ₀ : ξ ≤ ξ₀ :=
    (min_le_left _ _).trans (half_le_self hξ₀.le)
  have hξδ : ξ < δ :=
    (min_le_right _ _).trans (min_le_left _ _) |>.trans_lt (half_lt_self hδ)
  have hξγ : ξ < 3 * γ₀ / 8 := by
    have hle : ξ ≤ 3 * γ₀ / 16 :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    nlinarith
  have hξremaining : ξ ≤ remaining / 4 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have htransfer :
      δ + 2 * ξ + binaryEntropy η + η +
          (1 + Real.log 2) * (δ / (η / 3074) ^ 4) ≤
        (1 / 16) * ((1 / 2 - η) * κ₀) := by
    dsimp only [remaining] at hξremaining
    nlinarith
  exact ⟨η, δ, ξ, hη, hηtenth, hδ, hξ, hξξ₀,
    by simpa [hratio] using hr128, hcycle.le, htransfer, hξδ, hξγ⟩

noncomputable def paperScaleEll (n : ℕ) : ℝ :=
  max 1 (Real.log n / Real.log 2)

theorem one_le_paperScaleEll (n : ℕ) : 1 ≤ paperScaleEll n := by
  exact le_max_left _ _

theorem log_le_paperScaleEll_mul_log_two (n : ℕ) :
    Real.log n ≤ paperScaleEll n * Real.log 2 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmax : Real.log n / Real.log 2 ≤ paperScaleEll n :=
    le_max_right _ _
  calc
    Real.log n = (Real.log n / Real.log 2) * Real.log 2 := by
      field_simp [hlog.ne']
    _ ≤ paperScaleEll n * Real.log 2 :=
      mul_le_mul_of_nonneg_right hmax hlog.le

/-- Exact positive-matrix certificate property at logarithmic improvement
`epsilon`.  This is the mathematical core of Theorem 1 before smoothing and
finite-precision evaluation. -/
def ExactPositiveCertificate (ε : ℝ) : Prop :=
  ∀ {n : ℕ}, 2 ≤ n →
    ∀ A : Matrix (Fin n) (Fin n) ℝ, Matrix.Positive A →
    ∃ X : Matrix (Fin n) (Fin n) ℝ,
      IsDoublyStochastic X ∧
      Real.exp (betheObjective A X + maximumMatchingGain A X) ≤
        Matrix.permanent A ∧
      Real.log (Matrix.permanent A) -
          (betheObjective A X + maximumMatchingGain A X) ≤
        (Real.log 2 / 2 - ε) * n

/-- Absolute positive-matrix approximation theorem, with all constants
chosen internally.  This is the mathematical core of Theorem 1 before the
standard smoothing and finite-precision wrapper. -/
theorem exists_absolute_positiveMatrix_logApproximation
    (stableCoefficient : AnariOveisGharanStableCoefficient.{0}) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ {n : ℕ}, 2 ≤ n →
      ∀ A : Matrix (Fin n) (Fin n) ℝ, Matrix.Positive A →
      ∃ X : Matrix (Fin n) (Fin n) ℝ,
        IsDoublyStochastic X ∧
        Real.exp (betheObjective A X + maximumMatchingGain A X) ≤
          Matrix.permanent A ∧
        Real.log (Matrix.permanent A) -
            (betheObjective A X + maximumMatchingGain A X) ≤
          (Real.log 2 / 2 - ε) * n := by
  obtain ⟨κq, ξq, γq, hκq, hξq, hγq, hgain⟩ :=
    exists_rational_cleanPairGain_constants
  have hκ : 0 < (κq : ℝ) := by exact_mod_cast hκq
  have hξ₀ : 0 < (ξq : ℝ) := by exact_mod_cast hξq
  have hγ : 0 < (γq : ℝ) := by exact_mod_cast hγq
  obtain ⟨η, δ, ξ, hη, hηtenth, _hδ, hξ, hξξ₀, hrowSmall,
      hcycleSmall, htransferSmall, hξδ, hξγ⟩ :=
    exists_completion_scales hκ hξ₀ hγ
  let ε := epsilonPlus δ ξ (γq : ℝ)
  have hε : 0 < ε := epsilonPlus_pos hξδ hξγ
  refine ⟨ε, hε, ?_⟩
  intro n hn A hA
  let ell := paperScaleEll n
  let τ := ξ / (4 * ell)
  have hresult := positiveMatrix_logApproximation stableCoefficient hn
    hgain hκ hγ
    (one_le_paperScaleEll n) (log_le_paperScaleEll_mul_log_two n)
    hξ hξξ₀ (show τ = ξ / (4 * ell) by rfl) hη hηtenth
    hrowSmall hcycleSmall htransferSmall hξδ hξγ A hA
  rcases hresult with ⟨hε', X, hX, _hXint, hcert, hgap⟩
  exact ⟨X, hX, hcert, by simpa only [ε] using hgap⟩

end BeyondBethe
