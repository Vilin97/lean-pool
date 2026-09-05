/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

import LeanPool.MetricCodes.Interlacing

/-!
# Highest-weight identities

Diamond relations, Lie irreducibility, and isotropic highest-weight constructions.
-/

noncomputable section MetricCodesNoncomputable

namespace MetricCodes

namespace Spherical

namespace HigherHarmonicYoung

section

open scoped BigOperators

namespace ArbitraryRowFirstAxisIntertwining

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonPathRecurrence
open MetricCodes.Spherical.HigherHarmonicYoung.GelfandTsetlin

theorem sum_powerset_erase_insert
    {α M : Type*} [DecidableEq α] [AddCommMonoid M]
    (P : Finset α) (a : α) (ha : a ∈ P) (f : Finset α → M) :
    (∑ S ∈ P.powerset, f S) =
      ∑ S ∈ (P.erase a).powerset, (f S + f (insert a S)) := by
  classical
  calc
    (∑ S ∈ P.powerset, f S) =
        ∑ S ∈ (insert a (P.erase a)).powerset, f S := by
          rw [Finset.insert_erase ha]
    _ = (∑ S ∈ (P.erase a).powerset, f S) +
          ∑ S ∈ (P.erase a).powerset, f (insert a S) := by
          rw [Finset.sum_powerset_insert (by simp only [Finset.mem_erase, ne_eq, not_true_eq_false,
                                               false_and, not_false_eq_true])]
    _ = ∑ S ∈ (P.erase a).powerset,
          (f S + f (insert a S)) := by
          rw [Finset.sum_add_distrib]

end ArbitraryRowFirstAxisIntertwining

end

section


open scoped BigOperators

namespace ArbitraryRowSameAxisDiamondGapShift

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonPathRecurrence

theorem shiftedRowGap_raiseWeight_of_ne
    {r : ℕ} (lam : Fin (r + 1) → ℕ)
    (target preceding raised : Fin (r + 1))
    (htarget : target ≠ raised) (hpreceding : preceding ≠ raised) :
    shiftedRowGap (raiseWeight lam raised) target preceding =
      shiftedRowGap lam target preceding := by
  simp only [shiftedRowGap, raiseWeight, ne_eq, hpreceding, not_false_eq_true,
    Function.update_of_ne, htarget]

theorem shiftedRowGap_raiseWeight_later
    {r : ℕ} (lam : Fin (r + 1) → ℕ)
    (target raised preceding : Fin (r + 1))
    (htarget : target < raised) (hpreceding : preceding < target) :
    shiftedRowGap (raiseWeight lam raised) target preceding =
      shiftedRowGap lam target preceding := by
  apply shiftedRowGap_raiseWeight_of_ne lam target preceding raised
  · exact ne_of_lt htarget
  · exact ne_of_lt (hpreceding.trans htarget)

theorem shiftedRowGap_raiseWeight_preceding
    {r : ℕ} (lam : Fin (r + 1) → ℕ)
    (target raised : Fin (r + 1))
    (hne : target ≠ raised) (hdom : lam target ≤ lam raised) :
    shiftedRowGap (raiseWeight lam raised) target raised =
      shiftedRowGap lam target raised + 1 := by
  have hnat : lam raised + 1 - lam target =
      (lam raised - lam target) + 1 := by omega
  simp only [shiftedRowGap, raiseWeight, Function.update_self, ne_eq, hne, not_false_eq_true,
    Function.update_of_ne, hnat, Nat.cast_add, Nat.cast_one]
  ring

theorem polarizationPathCoefficient_raiseWeight_later
    {r : ℕ} (lam : Fin (r + 1) → ℕ)
    (target raised : Fin (r + 1)) (htarget : target < raised)
    (S : Finset (Fin (r + 1))) :
    polarizationPathCoefficient (raiseWeight lam raised) target S =
      polarizationPathCoefficient lam target S := by
  classical
  unfold polarizationPathCoefficient
  congr 1
  apply Finset.prod_congr rfl
  intro preceding hpreceding
  apply shiftedRowGap_raiseWeight_later lam target raised preceding htarget
  exact (mem_precedingRows preceding target).mp
    (Finset.mem_sdiff.mp hpreceding).1

theorem arbitraryRowAxialRaise_raiseWeight_later
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (target raised : Fin (r + 1)) (htarget : target < raised)
    (k : Fin n) :
    arbitraryRowAxialRaise (raiseWeight lam raised) target k =
      arbitraryRowAxialRaise lam target k := by
  apply LinearMap.ext
  intro p
  rw [arbitraryRowAxialRaise_apply, arbitraryRowAxialRaise_apply]
  apply Finset.sum_congr rfl
  intro S _
  rw [polarizationPathCoefficient_raiseWeight_later
    lam target raised htarget S]

theorem polarizationPathCoefficient_raiseWeight_of_mem
    {r : ℕ} (lam : Fin (r + 1) → ℕ)
    (target raised : Fin (r + 1)) (htarget : target ≠ raised)
    (S : Finset (Fin (r + 1))) (hS : raised ∈ S) :
    polarizationPathCoefficient (raiseWeight lam raised) target S =
      polarizationPathCoefficient lam target S := by
  classical
  unfold polarizationPathCoefficient
  congr 1
  apply Finset.prod_congr rfl
  intro preceding hpreceding
  apply shiftedRowGap_raiseWeight_of_ne lam target preceding raised htarget
  intro heq
  subst preceding
  exact (Finset.mem_sdiff.mp hpreceding).2 hS

theorem polarizationPathCoefficient_raiseWeight_of_not_mem
    {r : ℕ} (lam : Fin (r + 1) → ℕ)
    (target raised : Fin (r + 1)) (hrow : raised < target)
    (hdom : lam target ≤ lam raised)
    (S : Finset (Fin (r + 1))) (hS : raised ∉ S) :
    polarizationPathCoefficient (raiseWeight lam raised) target S =
      polarizationPathCoefficient lam target S -
        polarizationPathCoefficient lam target (insert raised S) := by
  rw [polarizationPathCoefficient_insert
    (raiseWeight lam raised) target raised S hrow hS,
    shiftedRowGap_raiseWeight_preceding lam target raised
      (ne_of_gt hrow) hdom,
    polarizationPathCoefficient_raiseWeight_of_mem lam target raised
      (ne_of_gt hrow) (insert raised S) (Finset.mem_insert_self _ _),
    polarizationPathCoefficient_insert lam target raised S hrow hS]
  ring

end ArbitraryRowSameAxisDiamondGapShift

namespace ArbitraryRowSameAxisDiamondPathCommutator

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowFirstAxisIntertwining
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondGapShift

private def diamondPathOperator {r n : ℕ}
    (target : Fin (r + 1)) (k : Fin n)
    (S : Finset (Fin (r + 1))) :
    PolynomialSpace r n →ₗ[ℝ] PolynomialSpace r n :=
  (LinearMap.mulLeft ℝ
    (MvPolynomial.X (variableIndex (polarizationPathStart target S) k))).comp
      (lowerPolarizationPath ((S.sort (· ≤ ·)) ++ [target]))

@[simp] theorem diamondPathOperator_apply {r n : ℕ}
    (target : Fin (r + 1)) (k : Fin n)
    (S : Finset (Fin (r + 1))) (p : PolynomialSpace r n) :
    diamondPathOperator target k S p =
      MvPolynomial.X (variableIndex (polarizationPathStart target S) k) *
        lowerPolarizationPath ((S.sort (· ≤ ·)) ++ [target]) p := rfl

private def diamondOmittedRowOperator {r n : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (target raised : Fin (r + 1)) (k : Fin n) :
    PolynomialSpace r n →ₗ[ℝ] PolynomialSpace r n :=
  ∑ S ∈ ((precedingRows target).erase raised).powerset,
    polarizationPathCoefficient lam target (insert raised S) •
      diamondPathOperator target k S

@[simp] theorem diamondOmittedRowOperator_apply {r n : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (target raised : Fin (r + 1)) (k : Fin n)
    (p : PolynomialSpace r n) :
    diamondOmittedRowOperator lam target raised k p =
      ∑ S ∈ ((precedingRows target).erase raised).powerset,
        polarizationPathCoefficient lam target (insert raised S) •
          (MvPolynomial.X
            (variableIndex (polarizationPathStart target S) k) *
              lowerPolarizationPath ((S.sort (· ≤ ·)) ++ [target]) p) := by
  simp only [diamondOmittedRowOperator, LinearMap.coe_sum, LinearMap.coe_smul, Finset.sum_apply,
    Pi.smul_apply, diamondPathOperator_apply]

theorem arbitraryRowAxialRaise_raiseWeight_eq_sub_omitted
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (target raised : Fin (r + 1)) (hrow : raised < target)
    (hdom : lam target ≤ lam raised) (k : Fin n) :
    arbitraryRowAxialRaise (raiseWeight lam raised) target k =
      arbitraryRowAxialRaise lam target k -
        diamondOmittedRowOperator lam target raised k := by
  classical
  apply LinearMap.ext
  intro p
  rw [LinearMap.sub_apply, arbitraryRowAxialRaise_apply,
    arbitraryRowAxialRaise_apply, diamondOmittedRowOperator_apply]
  have hmem : raised ∈ precedingRows target :=
    (mem_precedingRows raised target).mpr hrow
  rw [sum_powerset_erase_insert (precedingRows target) raised hmem,
    sum_powerset_erase_insert (precedingRows target) raised hmem,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro S hS
  have hsub : S ⊆ (precedingRows target).erase raised :=
    Finset.mem_powerset.mp hS
  have hnot : raised ∉ S := by
    intro h
    exact (Finset.mem_erase.mp (hsub h)).1 rfl
  rw [polarizationPathCoefficient_raiseWeight_of_not_mem
    lam target raised hrow hdom S hnot,
    polarizationPathCoefficient_raiseWeight_of_mem
      lam target raised (ne_of_gt hrow)
      (insert raised S) (Finset.mem_insert_self _ _), sub_smul]
  abel

theorem arbitraryRowAxialRaise_sameAxis_diamond_iff_commutator
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (i j : Fin (r + 1)) (hij : i < j)
    (hdom : lam j ≤ lam i) (k : Fin n) :
    ((arbitraryRowAxialRaise (raiseWeight lam i) j k).comp
        (arbitraryRowAxialRaise lam i k) =
      (arbitraryRowAxialRaise (raiseWeight lam j) i k).comp
        (arbitraryRowAxialRaise lam j k)) ↔
      ((arbitraryRowAxialRaise lam j k).comp
          (arbitraryRowAxialRaise lam i k) -
        (arbitraryRowAxialRaise lam i k).comp
          (arbitraryRowAxialRaise lam j k) =
          (diamondOmittedRowOperator lam j i k).comp
            (arbitraryRowAxialRaise lam i k)) := by
  rw [arbitraryRowAxialRaise_raiseWeight_eq_sub_omitted
    lam j i hij hdom k,
    arbitraryRowAxialRaise_raiseWeight_later lam i j hij k,
    LinearMap.sub_comp]
  constructor
  · intro h
    have h' := (sub_eq_iff_eq_add).mp h
    rw [h']
    abel
  · intro h
    have h' := (sub_eq_iff_eq_add).mp h
    rw [h']
    abel

end ArbitraryRowSameAxisDiamondPathCommutator

end

section


open scoped BigOperators InnerProductSpace

namespace ArbitraryRowSameAxisDiamond

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowFirstAxisIntertwining
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonGramIdeal
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonHighest
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondPathCommutator

theorem raiseWeight_raiseWeight_comm
    {r : ℕ} (lam : Fin (r + 1) → ℕ)
    (i j : Fin (r + 1)) (hij : i ≠ j) :
    raiseWeight (raiseWeight lam i) j =
      raiseWeight (raiseWeight lam j) i := by
  funext a
  by_cases hai : a = i
  · subst a
    simp only [raiseWeight, ne_eq, Ne.symm hij, not_false_eq_true, Function.update_of_ne, hij,
      Function.update_self]
  · by_cases haj : a = j
    · subst a
      simp only [raiseWeight, ne_eq, Ne.symm hij, not_false_eq_true, Function.update_of_ne,
        Function.update_self, hij]
    · simp only [raiseWeight, ne_eq, haj, not_false_eq_true, Function.update_of_ne, hai]

end ArbitraryRowSameAxisDiamond

end

section


open scoped BigOperators InnerProductSpace

namespace ArbitraryRankInterlacingAdjacentPathExchange

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInterlacingPolynomialSeed
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankReverseInterlacingPolynomialSeed
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonGramIdeal
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamond
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungArbitraryRankAdjacentInterlacingSchedule
open MetricCodes.Spherical.HigherYoungArbitraryRankInterlacingGapSchedule
open MetricCodes.Spherical.HigherYoungArbitraryRankInterlacingLegalSchedule
open MetricCodes.Spherical.ThreeRowYoungBranching

private def DominantSameAxisDiamond (r n : ℕ) : Prop :=
  ∀ (lam : Fin (r + 1) → ℕ) (_ : Antitone lam)
    (i j : Fin (r + 1)) (_ : i < j) (k : Fin n)
    (p : PolynomialSpace r n),
    arbitraryRowAxialRaise (raiseWeight lam i) j k
        (arbitraryRowAxialRaise lam i k p) =
      arbitraryRowAxialRaise (raiseWeight lam j) i k
        (arbitraryRowAxialRaise lam j k p)

private def DominantSameAxisRowDiamond {r : ℕ} (n : ℕ)
    (row : Fin (r + 1)) : Prop :=
  ∀ (lam : Fin (r + 1) → ℕ) (_ : Antitone lam)
    (i : Fin (r + 1)) (_ : i < row) (k : Fin n)
    (p : PolynomialSpace r n),
    arbitraryRowAxialRaise (raiseWeight lam i) row k
        (arbitraryRowAxialRaise lam i k p) =
      arbitraryRowAxialRaise (raiseWeight lam row) i k
        (arbitraryRowAxialRaise lam row k p)

theorem iteratedArbitraryRowAxialRaise_move_last_of_rowDiamond
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (rows : List (Fin (r + 1))) (row : Fin (r + 1))
    (hdiamond : DominantSameAxisRowDiamond n row)
    (hrows : ∀ i ∈ rows, i < row)
    (hdom : ∀ (front : List (Fin (r + 1))),
      (∀ i, front.count i ≤ rows.count i) →
        Antitone (arbitraryRowPathWeight lam front))
    (k : Fin n) (p : PolynomialSpace r n) :
    arbitraryRowAxialRaise (arbitraryRowPathWeight lam rows) row k
        (iteratedArbitraryRowAxialRaise lam k rows p) =
      iteratedArbitraryRowAxialRaise (raiseWeight lam row) k rows
        (arbitraryRowAxialRaise lam row k p) := by
  classical
  induction rows generalizing lam p with
  | nil => rfl
  | cons i rest ih =>
      have hi : i < row := hrows i (by simp only [List.mem_cons, true_or])
      have hrest : ∀ j ∈ rest, j < row := by
        intro j hj
        exact hrows j (by simp only [List.mem_cons, hj, or_true])
      have hdom0 : Antitone lam := by
        simpa only [arbitraryRowPathWeight] using hdom [] (by simp)
      have hdomrest : ∀ (front : List (Fin (r + 1))),
          (∀ j, front.count j ≤ rest.count j) →
            Antitone
              (arbitraryRowPathWeight (raiseWeight lam i) front) := by
        intro front hfront
        have hfull : ∀ j,
            (i :: front).count j ≤ (i :: rest).count j := by
          intro j
          by_cases hij : i = j
          · subst j
            simpa only [List.count_cons_self, add_le_add_iff_right, add_le_add_iff_left] using
              Nat.add_le_add_left (hfront i) 1
          · simp only [ne_eq, hij, not_false_eq_true, List.count_cons_of_ne, hfront j]
        simpa only [arbitraryRowPathWeight] using hdom (i :: front) hfull
      change
        arbitraryRowAxialRaise
            (arbitraryRowPathWeight (raiseWeight lam i) rest) row k
          (iteratedArbitraryRowAxialRaise (raiseWeight lam i) k rest
            (arbitraryRowAxialRaise lam i k p)) =
        iteratedArbitraryRowAxialRaise
          (raiseWeight (raiseWeight lam row) i) k rest
          (arbitraryRowAxialRaise (raiseWeight lam row) i k
            (arbitraryRowAxialRaise lam row k p))
      rw [ih (lam := raiseWeight lam i)
        (p := arbitraryRowAxialRaise lam i k p) hrest hdomrest]
      rw [hdiamond lam hdom0 i hi k p]
      rw [raiseWeight_raiseWeight_comm lam i row (ne_of_lt hi)]

theorem arbitraryRowPathWeight_adjacentReverseSuffix_antitone
    {r : ℕ} {low : Fin (r + 2) → ℕ}
    {mu : Fin (r + 1) → ℕ} (hlow : Interlaces low mu)
    (row : Fin (r + 2))
    (front : List (Fin (r + 2)))
    (hfront : ∀ i,
      front.count i ≤ (adjacentReverseSuffix low mu row).count i) :
    Antitone
      (arbitraryRowPathWeight
        (arbitraryRowPathWeight (appendZeroWeight mu)
          (adjacentReversePrefix low mu row)) front) := by
  have hcount : ∀ i,
      (adjacentReversePrefix low mu row ++ front).count i ≤
        interlacingGap low mu i := by
    intro i
    have hlowcount :
        (adjacentReversePrefix low mu row ++
          adjacentReverseSuffix low mu row).count i =
            interlacingGap low mu i := by
      rw [← reverseInterlacingRowSchedule_eq_adjacentReversePrefix_append_suffix,
        reverseInterlacingRowSchedule_count]
    simp only [List.count_append] at hlowcount ⊢
    have hfronti := hfront i
    omega
  have hinterlaces := foldl_interlaces_of_count_le_gap hlow
    (adjacentReversePrefix low mu row ++ front) hcount
  rw [← arbitraryRowPathWeight_eq_foldl,
    arbitraryRowPathWeight_append] at hinterlaces
  exact hinterlaces.antitone_ambient

theorem reverseInterlacingPolynomialSeed_adjacent_raise_of_rowDiamond
    {r n : ℕ}
    {low : Fin (r + 2) → ℕ} {mu : Fin (r + 1) → ℕ}
    (hlow : Interlaces low mu) (row : Fin (r + 2))
    (hdiamond : DominantSameAxisRowDiamond (n + 1) row)
    (p : HarmonicYoungSpace (n := n) mu) :
    arbitraryRowAxialRaise low row (Fin.last n)
        (reverseInterlacingPolynomialSeed low mu p) =
      reverseInterlacingPolynomialSeed (raiseWeight low row) mu p := by
  let pref := adjacentReversePrefix low mu row
  let suff := adjacentReverseSuffix low mu row
  let theta := arbitraryRowPathWeight (appendZeroWeight mu) pref
  let z : PolynomialSpace (r + 1) (n + 1) :=
    ((terminalZeroSelectedBranchIsometry mu p :
      HarmonicYoungSpace (n := n + 1) (appendZeroWeight mu)) :
      PolynomialSpace (r + 1) (n + 1))
  have hlowpath : arbitraryRowPathWeight theta suff = low := by
    simpa only [arbitraryRowPathWeight_append] using
      arbitraryRowPathWeight_adjacentReversePrefix_append_suffix hlow row
  have hsplitlow :
      reverseInterlacingRowSchedule low mu = pref ++ suff :=
    reverseInterlacingRowSchedule_eq_adjacentReversePrefix_append_suffix
      low mu row
  have hsplithigh :
      reverseInterlacingRowSchedule (raiseWeight low row) mu =
        pref ++ row :: suff :=
    reverseInterlacingRowSchedule_raiseWeight_eq_prefix_cons_suffix hlow row
  change
    arbitraryRowAxialRaise low row (Fin.last n)
        (iteratedArbitraryRowAxialRaise (appendZeroWeight mu)
          (Fin.last n) (reverseInterlacingRowSchedule low mu) z) =
      iteratedArbitraryRowAxialRaise (appendZeroWeight mu)
          (Fin.last n)
          (reverseInterlacingRowSchedule (raiseWeight low row) mu) z
  rw [hsplitlow, hsplithigh,
    iteratedArbitraryRowAxialRaise_append,
    iteratedArbitraryRowAxialRaise_append]
  change
    arbitraryRowAxialRaise low row (Fin.last n)
      (iteratedArbitraryRowAxialRaise theta (Fin.last n) suff
        (iteratedArbitraryRowAxialRaise (appendZeroWeight mu)
          (Fin.last n) pref z)) =
      iteratedArbitraryRowAxialRaise (raiseWeight theta row)
        (Fin.last n) suff
          (arbitraryRowAxialRaise theta row (Fin.last n)
            (iteratedArbitraryRowAxialRaise (appendZeroWeight mu)
              (Fin.last n) pref z))
  rw [← hlowpath]
  apply iteratedArbitraryRowAxialRaise_move_last_of_rowDiamond
    theta suff row hdiamond
  · intro i hi
    exact lt_of_mem_adjacentReverseSuffix low mu row i hi
  · intro t ht
    exact arbitraryRowPathWeight_adjacentReverseSuffix_antitone
      hlow row t ht

theorem reverseInterlacingPolynomialSeed_adjacent_raise_of_diamond
    {r n : ℕ} (hdiamond : DominantSameAxisDiamond (r + 1) (n + 1))
    {low : Fin (r + 2) → ℕ} {mu : Fin (r + 1) → ℕ}
    (hlow : Interlaces low mu) (row : Fin (r + 2))
    (p : HarmonicYoungSpace (n := n) mu) :
    arbitraryRowAxialRaise low row (Fin.last n)
        (reverseInterlacingPolynomialSeed low mu p) =
      reverseInterlacingPolynomialSeed (raiseWeight low row) mu p := by
  exact reverseInterlacingPolynomialSeed_adjacent_raise_of_rowDiamond
    hlow row
      (fun lam hdom i hi k q => hdiamond lam hdom i row hi k q) p

end ArbitraryRankInterlacingAdjacentPathExchange

namespace AllRankGelfandTsetlinAdjacentProjectedCoefficient

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalFibreAxisTransfer
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalForwardAxisRange
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinAdjacentFibrePhase
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankGelfandTsetlinHarmonicIsometry
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInternalRowLowerGram
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInterlacingAdjacentPathExchange
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankReverseInterlacingPolynomialSeed
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowAxialAdjointGram
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowBaseAxisChannel
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonGramIdeal
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowUnconditionalBranch
open MetricCodes.Spherical.HigherRepresentationGraph

private def canonicalAdjacentProjectedRaiseCoefficient
    {r n : ℕ} (low : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (row : Fin (r + 2))
    (hlow : Interlaces low mu)
    (hhigh : Interlaces (raiseWeight low row) mu)
    (hlowGram : PositiveGelfandTsetlinFischerGram (n := n) low mu hlow)
    (hhighGram : PositiveGelfandTsetlinFischerGram
      (n := n) (raiseWeight low row) mu hhigh) : ℝ :=
  adjacentNormalizedAxisCoefficient
    (canonicalGelfandTsetlinFischerGram low mu hlow hlowGram)
    (canonicalGelfandTsetlinFischerGram
      (raiseWeight low row) mu hhigh hhighGram)
    (arbitraryRowAxialLowerScalar low row)⁻¹

theorem projectedCoordinateRaise_canonicalGelfandTsetlinFibre_eq_of_pathExchange
    {r n : ℕ} (low : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (row : Fin (r + 2))
    (hlow : Interlaces low mu)
    (hhigh : Interlaces (raiseWeight low row) mu)
    (hdom : Antitone low)
    (hlowGram : PositiveGelfandTsetlinFischerGram (n := n) low mu hlow)
    (hhighGram : PositiveGelfandTsetlinFischerGram
      (n := n) (raiseWeight low row) mu hhigh)
    (hexchange : ∀ p : HarmonicYoungSpace (n := n) mu,
      arbitraryRowAxialRaise low row (Fin.last n)
          (reverseInterlacingPolynomialSeed low mu p) -
        reverseInterlacingPolynomialSeed (raiseWeight low row) mu p ∈
        youngGramRadialIdeal (r + 1) (n + 1))
    (p : HarmonicYoungSpace (n := n) mu) :
    projectedCoordinateRaise (raiseWeight low row) low
        (sum_raiseWeight low row) row
        (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n))
        (canonicalGelfandTsetlinFibre low mu hlow hlowGram p) =
      canonicalAdjacentProjectedRaiseCoefficient
        low mu row hlow hhigh hlowGram hhighGram •
        canonicalGelfandTsetlinFibre
          (raiseWeight low row) mu hhigh hhighGram p := by
  apply canonicalGelfandTsetlinFibre_channel_apply
    low (raiseWeight low row) mu hlow hhigh hlowGram hhighGram
    (projectedCoordinateRaise (raiseWeight low row) low
      (sum_raiseWeight low row) row
      (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n)))
    (arbitraryRowAxialLowerScalar low row)⁻¹
  intro q
  simpa only [EuclideanSpace.basisFun_apply, mul_one] using
    (projectedCoordinateRaise_reverseInterlacingHarmonicBranch_eq_of_pathExchange low mu row
      hlow hhigh hdom 1
      (by simpa using hexchange) q)

theorem canonicalAdjacentProjectedRaiseCoefficient_sq
    {r n : ℕ} (low : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (row : Fin (r + 2))
    (hlow : Interlaces low mu)
    (hhigh : Interlaces (raiseWeight low row) mu)
    (hlowGram : PositiveGelfandTsetlinFischerGram (n := n) low mu hlow)
    (hhighGram : PositiveGelfandTsetlinFischerGram
      (n := n) (raiseWeight low row) mu hhigh) :
    canonicalAdjacentProjectedRaiseCoefficient
      low mu row hlow hhigh hlowGram hhighGram ^ 2 =
      (arbitraryRowAxialLowerScalar low row)⁻¹ ^ 2 *
        canonicalGelfandTsetlinFischerGram
          (raiseWeight low row) mu hhigh hhighGram /
        canonicalGelfandTsetlinFischerGram low mu hlow hlowGram := by
  unfold canonicalAdjacentProjectedRaiseCoefficient
    adjacentNormalizedAxisCoefficient
  exact canonicalFibreAxisCoefficient_sq
    (arbitraryRowAxialLowerScalar low row)⁻¹
    (canonicalGelfandTsetlinFischerGram low mu hlow hlowGram)
    (canonicalGelfandTsetlinFischerGram
      (raiseWeight low row) mu hhigh hhighGram)
    (canonicalGelfandTsetlinFischerGram_pos low mu hlow hlowGram)
    (canonicalGelfandTsetlinFischerGram_pos
      (raiseWeight low row) mu hhigh hhighGram)

theorem canonicalAdjacentProjectedRaiseCoefficient_sq_iff_fischerGram
    {r n : ℕ} (low : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (row : Fin (r + 2))
    (hlow : Interlaces low mu)
    (hhigh : Interlaces (raiseWeight low row) mu)
    (hlowGram : PositiveGelfandTsetlinFischerGram (n := n) low mu hlow)
    (hhighGram : PositiveGelfandTsetlinFischerGram
      (n := n) (raiseWeight low row) mu hhigh) :
    canonicalAdjacentProjectedRaiseCoefficient
        low mu row hlow hhigh hlowGram hhighGram ^ 2 =
      internalRowLowerGramScalar (raiseWeight low row) row *
        plusProbability (n + 1) low mu row ↔
    canonicalGelfandTsetlinFischerGram
        (raiseWeight low row) mu hhigh hhighGram =
      arbitraryRowAxialLowerScalar low row ^ 2 *
        internalRowLowerGramScalar (raiseWeight low row) row *
        canonicalGelfandTsetlinFischerGram low mu hlow hlowGram *
        plusProbability (n + 1) low mu row := by
  rw [canonicalAdjacentProjectedRaiseCoefficient_sq]
  have hgap : arbitraryRowAxialLowerScalar low row ≠ 0 :=
    (arbitraryRowAxialLowerScalar_pos low row).ne'
  have hlowpos : canonicalGelfandTsetlinFischerGram
      low mu hlow hlowGram ≠ 0 :=
    (canonicalGelfandTsetlinFischerGram_pos
      low mu hlow hlowGram).ne'
  constructor <;> intro h
  · field_simp [hgap, hlowpos] at h ⊢
    nlinarith [h]
  · field_simp [hgap, hlowpos] at h ⊢
    nlinarith [h]

theorem canonicalAdjacentProjectedRaiseCoefficient_sq_of_fischerGram
    {r n : ℕ} (low : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (row : Fin (r + 2))
    (hlow : Interlaces low mu)
    (hhigh : Interlaces (raiseWeight low row) mu)
    (hlowGram : PositiveGelfandTsetlinFischerGram (n := n) low mu hlow)
    (hhighGram : PositiveGelfandTsetlinFischerGram
      (n := n) (raiseWeight low row) mu hhigh)
    (hgram : canonicalGelfandTsetlinFischerGram
        (raiseWeight low row) mu hhigh hhighGram =
      arbitraryRowAxialLowerScalar low row ^ 2 *
        internalRowLowerGramScalar (raiseWeight low row) row *
        canonicalGelfandTsetlinFischerGram low mu hlow hlowGram *
        plusProbability (n + 1) low mu row) :
    canonicalAdjacentProjectedRaiseCoefficient
        low mu row hlow hhigh hlowGram hhighGram ^ 2 =
      internalRowLowerGramScalar (raiseWeight low row) row *
        plusProbability (n + 1) low mu row :=
  (canonicalAdjacentProjectedRaiseCoefficient_sq_iff_fischerGram
    low mu row hlow hhigh hlowGram hhighGram).2 hgram

end AllRankGelfandTsetlinAdjacentProjectedCoefficient

end

section


open scoped BigOperators

namespace ArbitraryRowSameAxisDiamondFullCommutator

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowFirstAxisIntertwining
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonPathRecurrence
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondPathCommutator

private def diamondPairResidual {r n : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (target raised : Fin (r + 1)) (k : Fin n)
    (S : Finset (Fin (r + 1))) :
    PolynomialSpace r n →ₗ[ℝ] PolynomialSpace r n :=
  let Z := arbitraryRowAxialRaise lam raised k
  let omitted := diamondPathOperator target k S
  let inserted := diamondPathOperator target k (insert raised S)
  ((inserted.comp Z - Z.comp inserted) -
    shiftedRowGap lam target raised •
      (omitted.comp Z - Z.comp omitted)) - omitted.comp Z

@[simp] theorem diamondPairResidual_apply {r n : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (target raised : Fin (r + 1)) (k : Fin n)
    (S : Finset (Fin (r + 1))) (p : PolynomialSpace r n) :
    diamondPairResidual lam target raised k S p =
      ((diamondPathOperator target k (insert raised S)
            (arbitraryRowAxialRaise lam raised k p) -
          arbitraryRowAxialRaise lam raised k
            (diamondPathOperator target k (insert raised S) p)) -
        shiftedRowGap lam target raised •
          (diamondPathOperator target k S
              (arbitraryRowAxialRaise lam raised k p) -
            arbitraryRowAxialRaise lam raised k
              (diamondPathOperator target k S p))) -
        diamondPathOperator target k S
          (arbitraryRowAxialRaise lam raised k p) := rfl

theorem arbitraryRowAxialRaise_eq_paired_paths
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (target raised : Fin (r + 1)) (hrow : raised < target)
    (k : Fin n) (p : PolynomialSpace r n) :
    arbitraryRowAxialRaise lam target k p =
      ∑ S ∈ ((precedingRows target).erase raised).powerset,
        polarizationPathCoefficient lam target (insert raised S) •
          (diamondPathOperator target k (insert raised S) p -
            shiftedRowGap lam target raised •
              diamondPathOperator target k S p) := by
  classical
  rw [arbitraryRowAxialRaise_apply,
    sum_powerset_erase_insert (precedingRows target) raised
      ((mem_precedingRows raised target).mpr hrow)]
  apply Finset.sum_congr rfl
  intro S hS
  have hsub : S ⊆ (precedingRows target).erase raised :=
    Finset.mem_powerset.mp hS
  have hnot : raised ∉ S := by
    intro h
    exact (Finset.mem_erase.mp (hsub h)).1 rfl
  rw [polarizationPathCoefficient_insert lam target raised S hrow hnot]
  simp only [diamondPathOperator_apply, smul_sub, smul_smul]
  module

theorem arbitraryRowAxialRaise_commutator_sub_omitted_eq_sum_residual
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (target raised : Fin (r + 1)) (hrow : raised < target)
    (k : Fin n) :
    ((arbitraryRowAxialRaise lam target k).comp
          (arbitraryRowAxialRaise lam raised k) -
        (arbitraryRowAxialRaise lam raised k).comp
          (arbitraryRowAxialRaise lam target k)) -
        (diamondOmittedRowOperator lam target raised k).comp
          (arbitraryRowAxialRaise lam raised k) =
      ∑ S ∈ ((precedingRows target).erase raised).powerset,
        polarizationPathCoefficient lam target (insert raised S) •
          diamondPairResidual lam target raised k S := by
  classical
  apply LinearMap.ext
  intro p
  simp only [LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.sum_apply, LinearMap.smul_apply,
    diamondPairResidual_apply]
  rw [arbitraryRowAxialRaise_eq_paired_paths lam target raised hrow k
        (arbitraryRowAxialRaise lam raised k p),
      arbitraryRowAxialRaise_eq_paired_paths lam target raised hrow k p,
      diamondOmittedRowOperator_apply]
  simp_rw [map_sum, map_smul, map_sub]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro S _
  simp only [smul_sub, smul_smul, diamondPathOperator_apply, map_smul]
  module

theorem arbitraryRowAxialRaise_commutator_iff_sum_residual_eq_zero
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (target raised : Fin (r + 1)) (hrow : raised < target)
    (k : Fin n) :
    ((arbitraryRowAxialRaise lam target k).comp
          (arbitraryRowAxialRaise lam raised k) -
        (arbitraryRowAxialRaise lam raised k).comp
          (arbitraryRowAxialRaise lam target k) =
        (diamondOmittedRowOperator lam target raised k).comp
          (arbitraryRowAxialRaise lam raised k)) ↔
      (∑ S ∈ ((precedingRows target).erase raised).powerset,
        polarizationPathCoefficient lam target (insert raised S) •
          diamondPairResidual lam target raised k S) = 0 := by
  rw [← sub_eq_zero,
    arbitraryRowAxialRaise_commutator_sub_omitted_eq_sum_residual
      lam target raised hrow k]

end ArbitraryRowSameAxisDiamondFullCommutator

namespace ArbitraryRowSameAxisDiamondGapDifference

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonPathRecurrence

theorem shiftedRowGap_sub_shiftedRowGap
    {r : ℕ} (lam : Fin (r + 1) → ℕ)
    (a i j : Fin (r + 1)) (hai : a < i) (hij : i < j)
    (hji : lam j ≤ lam i) (hia : lam i ≤ lam a) :
    shiftedRowGap lam j a - shiftedRowGap lam i a =
      shiftedRowGap lam j i + 1 := by
  have hja : lam j ≤ lam a := hji.trans hia
  have hja_index : 1 ≤ j.val - a.val := by omega
  have hia_index : 1 ≤ i.val - a.val := by omega
  have hji_index : 1 ≤ j.val - i.val := by omega
  unfold shiftedRowGap
  rw [Nat.cast_sub hja, Nat.cast_sub hia, Nat.cast_sub hji,
    Nat.cast_sub hja_index, Nat.cast_sub hia_index,
    Nat.cast_sub hji_index,
    Nat.cast_sub (by omega : a.val ≤ j.val),
    Nat.cast_sub (by omega : a.val ≤ i.val),
    Nat.cast_sub (by omega : i.val ≤ j.val)]
  norm_num
  ring

end ArbitraryRowSameAxisDiamondGapDifference

end

section


open scoped BigOperators InnerProductSpace

namespace ArbitraryRowSameAxisDiamondRootCommutator

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankLowerRowBranching
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonPathCommutator

theorem polarization_axialCoordinate_mul_lowerPolarizationPath_sub
    {r n : ℕ} (a b start : Fin (r + 1)) (k : Fin n)
    (path : List (Fin (r + 1))) (p : PolynomialSpace r n) :
    polarization r n a b
        (MvPolynomial.X (variableIndex start k) *
          lowerPolarizationPath path p) -
        MvPolynomial.X (variableIndex start k) *
          lowerPolarizationPath path (polarization r n a b p) =
      (if b = start then
        MvPolynomial.X (variableIndex a k) *
          lowerPolarizationPath path p
      else 0) +
        MvPolynomial.X (variableIndex start k) *
          upperPolarizationPathCommutator a b path p := by
  rw [polarization_mul_euler, polarization_X_euler,
    polarization_lowerPolarizationPath_commutator]
  split_ifs <;> ring

private def axialCoordinateLowerPath
    {r n : ℕ} (start : Fin (r + 1)) (k : Fin n)
    (path : List (Fin (r + 1))) :
    PolynomialSpace r n →ₗ[ℝ] PolynomialSpace r n :=
  (LinearMap.mulLeft ℝ (MvPolynomial.X (variableIndex start k))).comp
    (lowerPolarizationPath path)

@[simp] theorem axialCoordinateLowerPath_apply
    {r n : ℕ} (start : Fin (r + 1)) (k : Fin n)
    (path : List (Fin (r + 1))) (p : PolynomialSpace r n) :
    axialCoordinateLowerPath start k path p =
      MvPolynomial.X (variableIndex start k) *
        lowerPolarizationPath path p := rfl

theorem polarization_arbitraryRowAxialRaise_commutator_sum
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (row a b : Fin (r + 1)) (k : Fin n)
    (p : PolynomialSpace r n) :
    polarization r n a b (arbitraryRowAxialRaise lam row k p) -
        arbitraryRowAxialRaise lam row k (polarization r n a b p) =
      ∑ S ∈ (precedingRows row).powerset,
        polarizationPathCoefficient lam row S •
          ((if b = polarizationPathStart row S then
            MvPolynomial.X (variableIndex a k) *
              lowerPolarizationPath
                ((S.sort (· ≤ ·)) ++ [row]) p
          else 0) +
            MvPolynomial.X
                (variableIndex (polarizationPathStart row S) k) *
              upperPolarizationPathCommutator a b
                ((S.sort (· ≤ ·)) ++ [row]) p) := by
  classical
  rw [arbitraryRowAxialRaise_apply, map_sum,
    arbitraryRowAxialRaise_apply, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro S _
  rw [map_smul, ← smul_sub,
    polarization_axialCoordinate_mul_lowerPolarizationPath_sub]

end ArbitraryRowSameAxisDiamondRootCommutator

namespace ArbitraryRowSameAxisDiamondSuffixRootCommute

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonPathCommutator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondRootCommutator

theorem upperPolarizationPathCommutator_eq_zero_of_avoids
    {r n : ℕ} (a b : Fin (r + 1))
    (path : List (Fin (r + 1)))
    (ha : a ∉ path) (hb : b ∉ path) :
    upperPolarizationPathCommutator (n := n) a b path = 0 := by
  induction path with
  | nil => rfl
  | cons i rest ih =>
      cases rest with
      | nil => rfl
      | cons j tail =>
          have harest : a ∉ j :: tail := by
            intro h
            exact ha (by simp only [List.mem_cons, h, or_true])
          have hbrest : b ∉ j :: tail := by
            intro h
            exact hb (by simp only [List.mem_cons, h, or_true])
          have hbjne : b ≠ j := by
            intro h
            subst b
            exact hb (by simp only [List.mem_cons, true_or, or_true])
          have hiane : i ≠ a := by
            intro h
            subst i
            exact ha (by simp only [List.mem_cons, true_or])
          change
            (polarization r n j i).comp
                (upperPolarizationPathCommutator a b (j :: tail)) +
              (if b = j then
                (polarization r n a i).comp
                  (lowerPolarizationPath (j :: tail))
              else 0) -
              (if i = a then
                (polarization r n j b).comp
                  (lowerPolarizationPath (j :: tail))
              else 0) = 0
          rw [ih harest hbrest, ite_eq_right hbjne, ite_eq_right hiane]
          simp only [LinearMap.comp_zero, add_zero, sub_self]

theorem polarization_arbitraryRowAxialRaise_commutator_eq_zero_of_gt
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (row a b : Fin (r + 1))
    (ha : row < a) (hb : row < b) (k : Fin n)
    (p : PolynomialSpace r n) :
    polarization r n a b (arbitraryRowAxialRaise lam row k p) -
      arbitraryRowAxialRaise lam row k (polarization r n a b p) = 0 := by
  classical
  rw [polarization_arbitraryRowAxialRaise_commutator_sum]
  apply Finset.sum_eq_zero
  intro S hS
  have hsub : S ⊆ precedingRows row := Finset.mem_powerset.mp hS
  have hstart : polarizationPathStart row S ≤ row := by
    by_cases hnon : S.Nonempty
    · exact le_of_lt
        (polarizationPathStart_lt_of_nonempty row S hnon hsub)
    · have hempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnon
      subst S
      simp only [polarizationPathStart_empty, Std.le_refl]
  have hpath :
      ∀ q ∈ ((S.sort (· ≤ ·)) ++ [row]), q ≤ row := by
    intro q hq
    rcases List.mem_append.mp hq with hsorted | hlast
    · exact le_of_lt
        ((mem_precedingRows q row).mp
          (hsub ((Finset.mem_sort (· ≤ ·)).mp hsorted)))
    · have hqrow : q = row := by simpa only [List.mem_cons, List.not_mem_nil, or_false] using hlast
      subst q
      exact le_rfl
  have hnota : a ∉ ((S.sort (· ≤ ·)) ++ [row]) := by
    intro h
    exact (not_lt_of_ge (hpath a h)) ha
  have hnotb : b ∉ ((S.sort (· ≤ ·)) ++ [row]) := by
    intro h
    exact (not_lt_of_ge (hpath b h)) hb
  have hbstart : b ≠ polarizationPathStart row S :=
    ne_of_gt (lt_of_le_of_lt hstart hb)
  rw [ite_eq_right hbstart,
    upperPolarizationPathCommutator_eq_zero_of_avoids
      a b ((S.sort (· ≤ ·)) ++ [row]) hnota hnotb]
  simp only [LinearMap.zero_apply, mul_zero, add_zero, smul_zero]

theorem polarization_arbitraryRowAxialRaise_commute_of_gt
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (row a b : Fin (r + 1))
    (ha : row < a) (hb : row < b) (k : Fin n)
    (p : PolynomialSpace r n) :
    polarization r n a b (arbitraryRowAxialRaise lam row k p) =
      arbitraryRowAxialRaise lam row k (polarization r n a b p) :=
  sub_eq_zero.mp
    (polarization_arbitraryRowAxialRaise_commutator_eq_zero_of_gt
      lam row a b ha hb k p)

theorem lowerPolarizationPath_arbitraryRowAxialRaise_commute_of_gt
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (row : Fin (r + 1)) (k : Fin n)
    (path : List (Fin (r + 1)))
    (hpath : ∀ q ∈ path, row < q)
    (p : PolynomialSpace r n) :
    lowerPolarizationPath path (arbitraryRowAxialRaise lam row k p) =
      arbitraryRowAxialRaise lam row k (lowerPolarizationPath path p) := by
  induction path generalizing p with
  | nil => rfl
  | cons first rest ih =>
      cases rest with
      | nil => rfl
      | cons next tail =>
          have hfirst : row < first := hpath first (by simp only [List.mem_cons, true_or])
          have hnext : row < next := hpath next (by simp only [List.mem_cons, true_or, or_true])
          have hrest : ∀ q ∈ (next :: tail), row < q := by
            intro q hq
            exact hpath q (by simp only [List.mem_cons, hq, or_true])
          change
            polarization r n next first
                (lowerPolarizationPath (next :: tail)
                  (arbitraryRowAxialRaise lam row k p)) =
              arbitraryRowAxialRaise lam row k
                (polarization r n next first
                  (lowerPolarizationPath (next :: tail) p))
          rw [ih hrest]
          exact polarization_arbitraryRowAxialRaise_commute_of_gt
            lam row next first hnext hfirst k _

end ArbitraryRowSameAxisDiamondSuffixRootCommute

end

section


open scoped BigOperators

namespace ArbitraryRowSameAxisDiamondResidualSuffixPartition

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonPathCommutator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondPathCommutator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondFullCommutator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondRootCommutator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSuffixRootCommute

private def precedingDiamondSubset {r : ℕ}
    (pivot : Fin (r + 1)) (S : Finset (Fin (r + 1))) :
    Finset (Fin (r + 1)) := S.filter (fun a => a < pivot)

private def succeedingDiamondSubset {r : ℕ}
    (pivot : Fin (r + 1)) (S : Finset (Fin (r + 1))) :
    Finset (Fin (r + 1)) := S.filter (fun a => pivot < a)

theorem sort_eq_preceding_append_succeeding
    {r : ℕ} (pivot : Fin (r + 1))
    (S : Finset (Fin (r + 1))) (hpivot : pivot ∉ S) :
    S.sort (· ≤ ·) =
      (precedingDiamondSubset pivot S).sort (· ≤ ·) ++
        (succeedingDiamondSubset pivot S).sort (· ≤ ·) := by
  classical
  let L := precedingDiamondSubset pivot S
  let U := succeedingDiamondSubset pivot S
  let path := L.sort (· ≤ ·) ++ U.sort (· ≤ ·)
  have hnodup : path.Nodup := by
    apply List.nodup_append.mpr
    refine ⟨Finset.sort_nodup L (· ≤ ·),
      Finset.sort_nodup U (· ≤ ·), ?_⟩
    intro a ha b hb hab
    have haL : a ∈ L := (Finset.mem_sort (· ≤ ·)).mp ha
    have hbU : b ∈ U := (Finset.mem_sort (· ≤ ·)).mp hb
    have halow : a < pivot := (Finset.mem_filter.mp haL).2
    have hbhigh : pivot < b := (Finset.mem_filter.mp hbU).2
    exact (ne_of_lt (halow.trans hbhigh)) hab
  have hsorted : path.Pairwise (· ≤ ·) := by
    apply List.pairwise_append.mpr
    refine ⟨Finset.pairwise_sort L (· ≤ ·),
      Finset.pairwise_sort U (· ≤ ·), ?_⟩
    intro a ha b hb
    have haL : a ∈ L := (Finset.mem_sort (· ≤ ·)).mp ha
    have hbU : b ∈ U := (Finset.mem_sort (· ≤ ·)).mp hb
    exact le_of_lt
      ((Finset.mem_filter.mp haL).2.trans
        (Finset.mem_filter.mp hbU).2)
  have hfin : path.toFinset = S := by
    ext a
    simp only [path, List.toFinset_append,
      List.mem_toFinset, Finset.mem_union, Finset.mem_sort,
      L, U, precedingDiamondSubset, succeedingDiamondSubset,
      Finset.mem_filter]
    constructor
    · rintro (⟨ha, _⟩ | ⟨ha, _⟩)
      · exact ha
      · exact ha
    · intro ha
      have hne : a ≠ pivot := by
        intro heq
        subst a
        exact hpivot ha
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact Or.inl ⟨ha, hlt⟩
      · exact Or.inr ⟨ha, hgt⟩
  have hcanonical := (List.toFinset_sort (r := (· ≤ ·)) hnodup).mpr hsorted
  simpa only [hfin] using hcanonical

theorem sort_insert_eq_preceding_cons_succeeding
    {r : ℕ} (pivot : Fin (r + 1))
    (S : Finset (Fin (r + 1))) (hpivot : pivot ∉ S) :
    (insert pivot S).sort (· ≤ ·) =
      (precedingDiamondSubset pivot S).sort (· ≤ ·) ++
        pivot :: (succeedingDiamondSubset pivot S).sort (· ≤ ·) := by
  classical
  let L := precedingDiamondSubset pivot S
  let U := succeedingDiamondSubset pivot S
  let path := L.sort (· ≤ ·) ++ pivot :: U.sort (· ≤ ·)
  have hnodup : path.Nodup := by
    apply List.nodup_append.mpr
    refine ⟨Finset.sort_nodup L (· ≤ ·), ?_, ?_⟩
    · apply List.nodup_cons.mpr
      refine ⟨?_, Finset.sort_nodup U (· ≤ ·)⟩
      intro h
      have hU : pivot ∈ U := (Finset.mem_sort (· ≤ ·)).mp h
      exact (lt_irrefl pivot) (Finset.mem_filter.mp hU).2
    · intro a ha b hb hab
      have haL : a ∈ L := (Finset.mem_sort (· ≤ ·)).mp ha
      have halow : a < pivot := (Finset.mem_filter.mp haL).2
      rcases List.mem_cons.mp hb with hb | hb
      · rw [hb] at hab
        exact (ne_of_lt halow) hab
      · have hbU : b ∈ U := (Finset.mem_sort (· ≤ ·)).mp hb
        exact (ne_of_lt (halow.trans (Finset.mem_filter.mp hbU).2)) hab
  have hsorted : path.Pairwise (· ≤ ·) := by
    apply List.pairwise_append.mpr
    refine ⟨Finset.pairwise_sort L (· ≤ ·), ?_, ?_⟩
    · apply List.pairwise_cons.mpr
      refine ⟨?_, Finset.pairwise_sort U (· ≤ ·)⟩
      intro a ha
      exact le_of_lt (Finset.mem_filter.mp
        ((Finset.mem_sort (· ≤ ·)).mp ha)).2
    · intro a ha b hb
      have haL : a ∈ L := (Finset.mem_sort (· ≤ ·)).mp ha
      have halow : a < pivot := (Finset.mem_filter.mp haL).2
      rcases List.mem_cons.mp hb with hb | hb
      · subst b
        exact halow.le
      · exact le_of_lt
          (halow.trans (Finset.mem_filter.mp
            ((Finset.mem_sort (· ≤ ·)).mp hb)).2)
  have hfin : path.toFinset = insert pivot S := by
    ext a
    simp only [path, List.toFinset_append,
      List.mem_toFinset, Finset.mem_union, List.toFinset_cons,
      Finset.mem_insert, Finset.mem_sort,
      L, U, precedingDiamondSubset, succeedingDiamondSubset,
      Finset.mem_filter]
    constructor
    · rintro (⟨ha, _⟩ | ha | ⟨ha, _⟩)
      · exact Or.inr ha
      · exact Or.inl ha
      · exact Or.inr ha
    · rintro (rfl | ha)
      · exact Or.inr (Or.inl rfl)
      · have hne : a ≠ pivot := by
          intro heq
          subst a
          exact hpivot ha
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · exact Or.inl ⟨ha, hlt⟩
        · exact Or.inr (Or.inr ⟨ha, hgt⟩)
  have hcanonical := (List.toFinset_sort (r := (· ≤ ·)) hnodup).mpr hsorted
  simpa only [hfin] using hcanonical

private def omittedDiamondPrefix {r n : ℕ}
    (target : Fin (r + 1)) (k : Fin n)
    (S : Finset (Fin (r + 1)))
    (front : List (Fin (r + 1))) (next : Fin (r + 1)) :
    PolynomialSpace r n →ₗ[ℝ] PolynomialSpace r n :=
  axialCoordinateLowerPath
    (polarizationPathStart target S) k (front ++ [next])

private def insertedDiamondPrefix {r n : ℕ}
    (target pivot : Fin (r + 1)) (k : Fin n)
    (S : Finset (Fin (r + 1)))
    (front : List (Fin (r + 1))) (next : Fin (r + 1)) :
    PolynomialSpace r n →ₗ[ℝ] PolynomialSpace r n :=
  (axialCoordinateLowerPath
    (polarizationPathStart target (insert pivot S)) k (front ++ [pivot])).comp
      (polarization r n next pivot)

theorem diamondPathOperator_eq_omittedPrefix_comp_suffix
    {r n : ℕ} (target : Fin (r + 1)) (k : Fin n)
    (S : Finset (Fin (r + 1)))
    (front : List (Fin (r + 1)))
    (next : Fin (r + 1)) (tail : List (Fin (r + 1)))
    (hsplit : (S.sort (· ≤ ·)) ++ [target] = front ++ next :: tail) :
    diamondPathOperator target k S =
      (omittedDiamondPrefix target k S front next).comp
        (lowerPolarizationPath (next :: tail)) := by
  apply LinearMap.ext
  intro p
  simp only [diamondPathOperator_apply, omittedDiamondPrefix,
    axialCoordinateLowerPath_apply, LinearMap.comp_apply]
  rw [hsplit, lowerPolarizationPath_append_cons_apply]

theorem diamondPathOperator_eq_insertedPrefix_comp_suffix
    {r n : ℕ} (target pivot : Fin (r + 1)) (k : Fin n)
    (S : Finset (Fin (r + 1)))
    (front : List (Fin (r + 1)))
    (next : Fin (r + 1)) (tail : List (Fin (r + 1)))
    (hsplit : ((insert pivot S).sort (· ≤ ·)) ++ [target] =
      front ++ pivot :: next :: tail) :
    diamondPathOperator target k (insert pivot S) =
      (insertedDiamondPrefix target pivot k S front next).comp
        (lowerPolarizationPath (next :: tail)) := by
  apply LinearMap.ext
  intro p
  simp only [diamondPathOperator_apply, insertedDiamondPrefix,
    axialCoordinateLowerPath_apply, LinearMap.comp_apply]
  rw [hsplit,
    lowerPolarizationPath_append_cons_apply front pivot (next :: tail)]
  rfl

private def diamondPrefixResidual {r n : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (target pivot : Fin (r + 1)) (k : Fin n)
    (S : Finset (Fin (r + 1)))
    (front : List (Fin (r + 1))) (next : Fin (r + 1)) :
    PolynomialSpace r n →ₗ[ℝ] PolynomialSpace r n :=
  let Z := arbitraryRowAxialRaise lam pivot k
  let omitted := omittedDiamondPrefix target k S front next
  let inserted := insertedDiamondPrefix target pivot k S front next
  ((inserted.comp Z - Z.comp inserted) -
    shiftedRowGap lam target pivot •
      (omitted.comp Z - Z.comp omitted)) - omitted.comp Z

theorem diamondPairResidual_eq_prefix_comp_suffix
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (target pivot : Fin (r + 1)) (k : Fin n)
    (S : Finset (Fin (r + 1)))
    (front : List (Fin (r + 1)))
    (next : Fin (r + 1)) (tail : List (Fin (r + 1)))
    (homit : (S.sort (· ≤ ·)) ++ [target] = front ++ next :: tail)
    (hinsert : ((insert pivot S).sort (· ≤ ·)) ++ [target] =
      front ++ pivot :: next :: tail)
    (hnext : pivot < next)
    (htail : ∀ a ∈ tail, pivot < a) :
    diamondPairResidual lam target pivot k S =
      (diamondPrefixResidual lam target pivot k S front next).comp
        (lowerPolarizationPath (next :: tail)) := by
  let suffix : PolynomialSpace r n →ₗ[ℝ] PolynomialSpace r n :=
    lowerPolarizationPath (next :: tail)
  let Z : PolynomialSpace r n →ₗ[ℝ] PolynomialSpace r n :=
    arbitraryRowAxialRaise lam pivot k
  have hcomm : suffix.comp Z = Z.comp suffix := by
    apply LinearMap.ext
    intro p
    exact lowerPolarizationPath_arbitraryRowAxialRaise_commute_of_gt
      lam pivot k (next :: tail)
      (by
        intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hnext
        · exact htail a ha)
      p
  rw [diamondPairResidual,
    diamondPathOperator_eq_omittedPrefix_comp_suffix
      target k S front next tail homit,
    diamondPathOperator_eq_insertedPrefix_comp_suffix
      target pivot k S front next tail hinsert]
  change
    ((((insertedDiamondPrefix target pivot k S front next).comp suffix).comp Z -
      Z.comp ((insertedDiamondPrefix target pivot k S front next).comp suffix)) -
      shiftedRowGap lam target pivot •
        (((omittedDiamondPrefix target k S front next).comp suffix).comp Z -
          Z.comp ((omittedDiamondPrefix target k S front next).comp suffix))) -
        ((omittedDiamondPrefix target k S front next).comp suffix).comp Z =
      (diamondPrefixResidual lam target pivot k S front next).comp suffix
  simp only [diamondPrefixResidual, LinearMap.sub_comp,
    LinearMap.smul_comp, LinearMap.comp_assoc, hcomm]
  rfl

end ArbitraryRowSameAxisDiamondResidualSuffixPartition

namespace ArbitraryRowSameAxisDiamondSpectralPath

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonLastRoot
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonPathCommutator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondPathCommutator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondGapDifference

private def spectralPathCoeff {r : ℕ}
    (lam : Fin (r + 1) → ℕ) (pivot : Fin (r + 1))
    (t : ℝ) (S : Finset (Fin (r + 1))) : ℝ :=
  (-1 : ℝ) ^ S.card *
    ∏ a ∈ precedingRows pivot \ S, (shiftedRowGap lam pivot a + t)

private def spectralPathOperator {r n : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (pivot target : Fin (r + 1)) (k : Fin n) (t : ℝ) :
    PolynomialSpace r n →ₗ[ℝ] PolynomialSpace r n :=
  ∑ S ∈ (precedingRows pivot).powerset,
    spectralPathCoeff lam pivot t S • diamondPathOperator target k S

@[simp] theorem spectralPathOperator_apply {r n : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (pivot target : Fin (r + 1)) (k : Fin n) (t : ℝ)
    (p : PolynomialSpace r n) :
    spectralPathOperator lam pivot target k t p =
      ∑ S ∈ (precedingRows pivot).powerset,
        spectralPathCoeff lam pivot t S • diamondPathOperator target k S p := by
  simp only [spectralPathOperator, LinearMap.coe_sum, LinearMap.coe_smul, Finset.sum_apply,
    Pi.smul_apply, diamondPathOperator_apply]

@[simp] theorem spectralPathCoeff_zero {r : ℕ}
    (lam : Fin (r + 1) → ℕ) (pivot : Fin (r + 1))
    (S : Finset (Fin (r + 1))) :
    spectralPathCoeff lam pivot 0 S =
      polarizationPathCoefficient lam pivot S := by
  simp only [spectralPathCoeff, add_zero, polarizationPathCoefficient]

@[simp] theorem spectralPathOperator_self_zero {r n : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (pivot : Fin (r + 1)) (k : Fin n) :
    spectralPathOperator lam pivot pivot k 0 =
      arbitraryRowAxialRaise lam pivot k := by
  simp only [spectralPathOperator, spectralPathCoeff_zero, diamondPathOperator,
    arbitraryRowAxialRaise]

theorem spectralPathCoeff_insert {r : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (pivot a : Fin (r + 1)) (t : ℝ)
    (S : Finset (Fin (r + 1)))
    (ha : a < pivot) (haS : a ∉ S) :
    spectralPathCoeff lam pivot t S =
      -(shiftedRowGap lam pivot a + t) *
        spectralPathCoeff lam pivot t (insert a S) := by
  classical
  have hamem : a ∈ precedingRows pivot \ S := by
    simp only [Finset.mem_sdiff, mem_precedingRows, ha, haS, not_false_eq_true, and_self]
  have hprod := Finset.mul_prod_erase
    (precedingRows pivot \ S)
      (fun b => shiftedRowGap lam pivot b + t) hamem
  have hdiff : precedingRows pivot \ insert a S =
      (precedingRows pivot \ S).erase a :=
    Finset.sdiff_insert (precedingRows pivot) S a
  unfold spectralPathCoeff
  rw [Finset.card_insert_of_notMem haS, hdiff, pow_succ, ← hprod]
  ring

@[simp] theorem spectralPathOperator_zero_pivot {r n : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (target : Fin (r + 1)) (k : Fin n) (t : ℝ) :
    spectralPathOperator lam 0 target k t =
      LinearMap.mulLeft ℝ (MvPolynomial.X (variableIndex target k)) := by
  have hpre : precedingRows (0 : Fin (r + 1)) = ∅ := by
    ext a
    simp only [mem_precedingRows, not_lt_zero, Finset.notMem_empty]
  simp only [spectralPathOperator, hpre, Finset.powerset_empty, spectralPathCoeff,
    Finset.empty_sdiff, Finset.prod_empty, mul_one, diamondPathOperator, polarizationPathStart,
    Finset.sum_singleton, Finset.card_empty, pow_zero, Finset.not_nonempty_empty, ↓reduceDIte,
    Finset.sort_empty, List.nil_append, lowerPolarizationPath, LinearMap.comp_id, one_smul]

theorem shiftedRowGap_succ_eq_add_predecessor {r : ℕ}
    (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam)
    (a : Fin r) (b : Fin (r + 1)) (hb : b < a.castSucc) :
    shiftedRowGap lam a.succ b =
      shiftedRowGap lam a.castSucc b +
        shiftedRowGap lam a.succ a.castSucc + 1 := by
  have hstep : a.castSucc < a.succ := by
    change a.val < a.val + 1
    omega
  have hgap := shiftedRowGap_sub_shiftedRowGap
    lam b a.castSucc a.succ hb hstep
      (hdom hstep.le) (hdom hb.le)
  linarith

theorem spectralPathCoeff_succ_insert_predecessor {r : ℕ}
    (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam)
    (a : Fin r) (t : ℝ) (S : Finset (Fin (r + 1)))
    (hS : S ⊆ precedingRows a.castSucc) :
    spectralPathCoeff lam a.succ t (insert a.castSucc S) =
      -spectralPathCoeff lam a.castSucc
        (t + shiftedRowGap lam a.succ a.castSucc + 1) S := by
  classical
  have hnot : a.castSucc ∉ S := by
    intro ha
    exact (lt_irrefl a.castSucc)
      ((mem_precedingRows a.castSucc a.castSucc).mp (hS ha))
  have hdiff :
      precedingRows a.succ \ insert a.castSucc S =
        precedingRows a.castSucc \ S := by
    rw [precedingRows_succ a]
    ext b
    simp only [Finset.mem_sdiff, Finset.mem_insert]
    constructor
    · rintro ⟨hb | hb, hnotb⟩
      · exact False.elim (hnotb (Or.inl hb))
      · exact ⟨hb, fun h => hnotb (Or.inr h)⟩
    · rintro ⟨hb, hbS⟩
      exact ⟨Or.inr hb, by
        rintro (rfl | hb')
        · exact (lt_irrefl a.castSucc)
            ((mem_precedingRows a.castSucc a.castSucc).mp hb)
        · exact hbS hb'⟩
  have hprod :
      (∏ b ∈ precedingRows a.castSucc \ S,
        (shiftedRowGap lam a.succ b + t)) =
      ∏ b ∈ precedingRows a.castSucc \ S,
        (shiftedRowGap lam a.castSucc b +
          (t + shiftedRowGap lam a.succ a.castSucc + 1)) := by
    apply Finset.prod_congr rfl
    intro b hb
    rw [shiftedRowGap_succ_eq_add_predecessor
      lam hdom a b
        ((mem_precedingRows b a.castSucc).mp
          (Finset.mem_sdiff.mp hb).1)]
    ring
  unfold spectralPathCoeff
  rw [Finset.card_insert_of_notMem hnot, hdiff, hprod, pow_succ]
  ring

theorem spectralPathCoeff_succ_of_preceding {r : ℕ}
    (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam)
    (a : Fin r) (t : ℝ) (S : Finset (Fin (r + 1)))
    (hS : S ⊆ precedingRows a.castSucc) :
    spectralPathCoeff lam a.succ t S =
      (shiftedRowGap lam a.succ a.castSucc + t) *
        spectralPathCoeff lam a.castSucc
          (t + shiftedRowGap lam a.succ a.castSucc + 1) S := by
  have hnot : a.castSucc ∉ S := by
    intro ha
    exact (lt_irrefl a.castSucc)
      ((mem_precedingRows a.castSucc a.castSucc).mp (hS ha))
  have hstep : a.castSucc < a.succ := by
    change a.val < a.val + 1
    omega
  rw [spectralPathCoeff_insert lam a.succ a.castSucc t S hstep hnot,
    spectralPathCoeff_succ_insert_predecessor lam hdom a t S hS]
  ring

theorem diamondPathOperator_insert_predecessor {r n : ℕ}
    (a : Fin r) (target : Fin (r + 1)) (k : Fin n)
    (S : Finset (Fin (r + 1)))
    (hS : S ⊆ precedingRows a.castSucc) :
    diamondPathOperator target k (insert a.castSucc S) =
      (diamondPathOperator a.castSucc k S).comp
        (polarization r n target a.castSucc) := by
  classical
  have hstart :
      polarizationPathStart target (insert a.castSucc S) =
        polarizationPathStart a.castSucc S := by
    by_cases hnon : S.Nonempty
    · rw [polarizationPathStart,
        dite_eq_left (S.insert_nonempty a.castSucc),
        polarizationPathStart, dite_eq_left hnon,
        Finset.min'_insert a.castSucc S hnon]
      apply min_eq_right
      exact le_of_lt ((mem_precedingRows (S.min' hnon) a.castSucc).mp
        (hS (Finset.min'_mem S hnon)))
    · have hempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnon
      simp only [polarizationPathStart, hempty, insert_empty_eq, Finset.singleton_nonempty,
        ↓reduceDIte, Finset.min'_singleton, Finset.not_nonempty_empty]
  apply LinearMap.ext
  intro p
  simp only [LinearMap.comp_apply, diamondPathOperator_apply]
  rw [sort_insert_last_of_preceding a S hS, hstart]
  simp only [List.append_assoc, List.singleton_append]
  rw [lowerPolarizationPath_append_cons_apply
    (S.sort (· ≤ ·)) a.castSucc [target] p]
  rfl

theorem spectralPathOperator_succ {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam)
    (a : Fin r) (target : Fin (r + 1))
    (k : Fin n) (t : ℝ) :
    spectralPathOperator lam a.succ target k t =
      (shiftedRowGap lam a.succ a.castSucc + t) •
        spectralPathOperator lam a.castSucc target k
          (t + shiftedRowGap lam a.succ a.castSucc + 1) -
      (spectralPathOperator lam a.castSucc a.castSucc k
        (t + shiftedRowGap lam a.succ a.castSucc + 1)).comp
          (polarization r n target a.castSucc) := by
  classical
  apply LinearMap.ext
  intro p
  rw [spectralPathOperator_apply, precedingRows_succ a,
    Finset.sum_powerset_insert (by simp only [mem_precedingRows, lt_self_iff_false,
                                     not_false_eq_true])]
  have hfirst :
      (∑ S ∈ (precedingRows a.castSucc).powerset,
        spectralPathCoeff lam a.succ t S •
          diamondPathOperator target k S p) =
        (shiftedRowGap lam a.succ a.castSucc + t) •
          spectralPathOperator lam a.castSucc target k
            (t + shiftedRowGap lam a.succ a.castSucc + 1) p := by
    rw [spectralPathOperator_apply, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro S hS
    rw [spectralPathCoeff_succ_of_preceding
      lam hdom a t S (Finset.mem_powerset.mp hS), mul_smul]
  have hsecond :
      (∑ S ∈ (precedingRows a.castSucc).powerset,
        spectralPathCoeff lam a.succ t (insert a.castSucc S) •
          diamondPathOperator target k (insert a.castSucc S) p) =
        -(spectralPathOperator lam a.castSucc a.castSucc k
          (t + shiftedRowGap lam a.succ a.castSucc + 1)
            (polarization r n target a.castSucc p)) := by
    rw [spectralPathOperator_apply, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro S hS
    rw [spectralPathCoeff_succ_insert_predecessor
      lam hdom a t S (Finset.mem_powerset.mp hS),
      diamondPathOperator_insert_predecessor
        a target k S (Finset.mem_powerset.mp hS)]
    simp only [shiftedRowGap_succ_castSucc, LinearMap.coe_comp, Function.comp_apply,
      polarization_apply, map_sum, diamondPathOperator_apply, neg_smul]
  rw [hfirst, hsecond]
  simp only [shiftedRowGap_succ_castSucc, spectralPathOperator_apply, diamondPathOperator_apply,
    polarization_apply, map_sum, sub_eq_add_neg, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.neg_apply, LinearMap.comp_apply]

end ArbitraryRowSameAxisDiamondSpectralPath

namespace ArbitraryRowSameAxisDiamondSuffixCoefficientFactor

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondGapDifference
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondResidualSuffixPartition
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralPath

theorem diamondSubset_eq_preceding_union_succeeding
    {r : ℕ} (pivot : Fin (r + 1))
    (S : Finset (Fin (r + 1))) (hpivot : pivot ∉ S) :
    S = precedingDiamondSubset pivot S ∪ succeedingDiamondSubset pivot S := by
  ext a
  simp only [Finset.mem_union, precedingDiamondSubset, succeedingDiamondSubset,
    Finset.mem_filter]
  constructor
  · intro ha
    have hne : a ≠ pivot := by
      intro heq
      subst a
      exact hpivot ha
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact Or.inl ⟨ha, hlt⟩
    · exact Or.inr ⟨ha, hgt⟩
  · rintro (⟨ha, _⟩ | ⟨ha, _⟩)
    · exact ha
    · exact ha

private def diamondSucceedingRows {r : ℕ}
    (target pivot : Fin (r + 1)) : Finset (Fin (r + 1)) :=
  (precedingRows target).filter (fun a => pivot < a)

@[simp] theorem mem_diamondSucceedingRows {r : ℕ}
    (target pivot a : Fin (r + 1)) :
    a ∈ diamondSucceedingRows target pivot ↔ a < target ∧ pivot < a := by
  simp only [diamondSucceedingRows, Finset.mem_filter, mem_precedingRows]

theorem diamondOmittedRows_eq_preceding_union_succeeding
    {r : ℕ} (target pivot : Fin (r + 1)) (hpivot : pivot < target)
    (S : Finset (Fin (r + 1))) :
    precedingRows target \ insert pivot S =
      (precedingRows pivot \ precedingDiamondSubset pivot S) ∪
        (diamondSucceedingRows target pivot \
          succeedingDiamondSubset pivot S) := by
  ext a
  simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_union,
    mem_precedingRows, mem_diamondSucceedingRows,
    precedingDiamondSubset, succeedingDiamondSubset, Finset.mem_filter]
  constructor
  · rintro ⟨hatarget, hnot⟩
    have hne : a ≠ pivot := by
      intro heq
      exact hnot (Or.inl heq)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact Or.inl ⟨hlt, fun ha => hnot (Or.inr ha.1)⟩
    · exact Or.inr ⟨⟨hatarget, hgt⟩, fun ha => hnot (Or.inr ha.1)⟩
  · rintro (⟨halow, hnot⟩ | ⟨⟨hatarget, hahigh⟩, hnot⟩)
    · refine ⟨halow.trans hpivot, ?_⟩
      rintro (heq | haS)
      · exact (ne_of_lt halow) heq
      · exact hnot ⟨haS, halow⟩
    · refine ⟨hatarget, ?_⟩
      rintro (heq | haS)
      · exact (ne_of_gt hahigh) heq
      · exact hnot ⟨haS, hahigh⟩

private def upperDiamondPathCoefficient {r : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (target pivot : Fin (r + 1))
    (S : Finset (Fin (r + 1))) : ℝ :=
  (-1 : ℝ) ^ (succeedingDiamondSubset pivot S).card *
    ∏ a ∈ diamondSucceedingRows target pivot \
      succeedingDiamondSubset pivot S, shiftedRowGap lam target a

theorem shiftedRowGap_target_eq_pivot_add_spectralShift
    {r : ℕ} (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam)
    (target pivot a : Fin (r + 1))
    (hpivot : pivot < target) (ha : a < pivot) :
    shiftedRowGap lam target a =
      shiftedRowGap lam pivot a + (shiftedRowGap lam target pivot + 1) := by
  have hgap := shiftedRowGap_sub_shiftedRowGap lam a pivot target ha hpivot
    (hdom hpivot.le) (hdom ha.le)
  linarith

theorem polarizationPathCoefficient_insert_pivot_factor
    {r : ℕ} (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam)
    (target pivot : Fin (r + 1)) (hpivot : pivot < target)
    (S : Finset (Fin (r + 1))) (hS : pivot ∉ S) :
    polarizationPathCoefficient lam target (insert pivot S) =
      -upperDiamondPathCoefficient lam target pivot S *
        spectralPathCoeff lam pivot
          (shiftedRowGap lam target pivot + 1)
          (precedingDiamondSubset pivot S) := by
  classical
  let lower := precedingDiamondSubset pivot S
  let upper := succeedingDiamondSubset pivot S
  have hdisjoint : Disjoint lower upper := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    exact (not_lt_of_ge (Finset.mem_filter.mp hb).2.le)
      (Finset.mem_filter.mp ha).2
  have hcard : S.card = lower.card + upper.card := by
    rw [diamondSubset_eq_preceding_union_succeeding pivot S hS,
      Finset.card_union_of_disjoint hdisjoint]
  have hblocks :
      Disjoint (precedingRows pivot \ lower)
        (diamondSucceedingRows target pivot \ upper) := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    have halow : a < pivot :=
      (mem_precedingRows a pivot).mp (Finset.mem_sdiff.mp ha).1
    have hahigh : pivot < a :=
      (mem_diamondSucceedingRows target pivot a).mp
        (Finset.mem_sdiff.mp hb).1 |>.2
    exact (not_lt_of_ge hahigh.le) halow
  have hprod :
      (∏ a ∈ precedingRows target \ insert pivot S,
        shiftedRowGap lam target a) =
        (∏ a ∈ precedingRows pivot \ lower,
          (shiftedRowGap lam pivot a +
            (shiftedRowGap lam target pivot + 1))) *
          (∏ a ∈ diamondSucceedingRows target pivot \ upper,
            shiftedRowGap lam target a) := by
    rw [diamondOmittedRows_eq_preceding_union_succeeding
      target pivot hpivot S, Finset.prod_union hblocks]
    congr 1
    apply Finset.prod_congr rfl
    intro a ha
    exact shiftedRowGap_target_eq_pivot_add_spectralShift
      lam hdom target pivot a hpivot
        ((mem_precedingRows a pivot).mp (Finset.mem_sdiff.mp ha).1)
  unfold polarizationPathCoefficient upperDiamondPathCoefficient spectralPathCoeff
  rw [Finset.card_insert_of_notMem hS, hcard, pow_add, pow_add, hprod]
  ring

end ArbitraryRowSameAxisDiamondSuffixCoefficientFactor

end

section


open scoped BigOperators

namespace ArbitraryRowSameAxisDiamondSuffixSummation

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondFullCommutator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondPathCommutator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondResidualSuffixPartition
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondRootCommutator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralPath
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSuffixCoefficientFactor

theorem sum_powerset_disjoint_union
    {α M : Type*} [DecidableEq α] [AddCommMonoid M]
    (lower upper : Finset α) (hdisjoint : Disjoint lower upper)
    (f : Finset α → M) :
    (∑ S ∈ (lower ∪ upper).powerset, f S) =
      ∑ U ∈ upper.powerset,
        ∑ L ∈ lower.powerset, f (L ∪ U) := by
  classical
  rw [← Finset.sum_product upper.powerset lower.powerset
    (fun z => f (z.2 ∪ z.1))]
  apply Finset.sum_bij
    (fun S _ => (S ∩ upper, S ∩ lower))
  · intro S _
    simp only [Finset.mem_product, Finset.mem_powerset]
    exact ⟨Finset.inter_subset_right, Finset.inter_subset_right⟩
  · intro S hS T hT heq
    have hu : S ∩ upper = T ∩ upper := congrArg Prod.fst heq
    have hl : S ∩ lower = T ∩ lower := congrArg Prod.snd heq
    have hsubS : S ⊆ lower ∪ upper := Finset.mem_powerset.mp hS
    have hsubT : T ⊆ lower ∪ upper := Finset.mem_powerset.mp hT
    ext a
    constructor
    · intro ha
      rcases Finset.mem_union.mp (hsubS ha) with halow | haup
      · have ha' : a ∈ S ∩ lower := Finset.mem_inter.mpr ⟨ha, halow⟩
        rw [hl] at ha'
        exact (Finset.mem_inter.mp ha').1
      · have ha' : a ∈ S ∩ upper := Finset.mem_inter.mpr ⟨ha, haup⟩
        rw [hu] at ha'
        exact (Finset.mem_inter.mp ha').1
    · intro ha
      rcases Finset.mem_union.mp (hsubT ha) with halow | haup
      · have ha' : a ∈ T ∩ lower := Finset.mem_inter.mpr ⟨ha, halow⟩
        rw [← hl] at ha'
        exact (Finset.mem_inter.mp ha').1
      · have ha' : a ∈ T ∩ upper := Finset.mem_inter.mpr ⟨ha, haup⟩
        rw [← hu] at ha'
        exact (Finset.mem_inter.mp ha').1
  · rintro ⟨U, L⟩ hUL
    have hU : U ⊆ upper :=
      Finset.mem_powerset.mp (Finset.mem_product.mp hUL).1
    have hL : L ⊆ lower :=
      Finset.mem_powerset.mp (Finset.mem_product.mp hUL).2
    refine ⟨L ∪ U, Finset.mem_powerset.mpr ?_, ?_⟩
    · intro a ha
      rcases Finset.mem_union.mp ha with ha | ha
      · exact Finset.mem_union_left _ (hL ha)
      · exact Finset.mem_union_right _ (hU ha)
    · apply Prod.ext
      · change (L ∪ U) ∩ upper = U
        ext a
        simp only [Finset.mem_inter]
        constructor
        · rintro ⟨ha, haup⟩
          rcases Finset.mem_union.mp ha with halow | haU
          · exact False.elim
              ((Finset.disjoint_left.mp hdisjoint (hL halow)) haup)
          · exact haU
        · intro ha
          exact ⟨Finset.mem_union_right _ ha, hU ha⟩
      · change (L ∪ U) ∩ lower = L
        ext a
        simp only [Finset.mem_inter]
        constructor
        · rintro ⟨ha, halow⟩
          rcases Finset.mem_union.mp ha with haL | haup
          · exact haL
          · exact False.elim
              ((Finset.disjoint_left.mp hdisjoint halow) (hU haup))
        · intro ha
          exact ⟨Finset.mem_union_left _ ha, hL ha⟩
  · intro S hS
    congr 1
    ext a
    simp only [Finset.mem_union, Finset.mem_inter]
    constructor
    · intro ha
      rcases Finset.mem_union.mp ((Finset.mem_powerset.mp hS) ha) with
        halow | haup
      · exact Or.inl ⟨ha, halow⟩
      · exact Or.inr ⟨ha, haup⟩
    · rintro (⟨ha, _⟩ | ⟨ha, _⟩)
      · exact ha
      · exact ha

theorem precedingRows_erase_pivot_eq_union
    {r : ℕ} (target pivot : Fin (r + 1)) (hpivot : pivot < target) :
    (precedingRows target).erase pivot =
      precedingRows pivot ∪ diamondSucceedingRows target pivot := by
  ext a
  simp only [Finset.mem_erase, Finset.mem_union,
    mem_precedingRows, mem_diamondSucceedingRows]
  constructor
  · rintro ⟨hne, hatarget⟩
    rcases lt_or_gt_of_ne hne with hlow | hhigh
    · exact Or.inl hlow
    · exact Or.inr ⟨hatarget, hhigh⟩
  · rintro (hlow | ⟨hatarget, hhigh⟩)
    · exact ⟨ne_of_lt hlow, hlow.trans hpivot⟩
    · exact ⟨ne_of_gt hhigh, hatarget⟩

theorem precedingRows_disjoint_diamondSucceedingRows
    {r : ℕ} (target pivot : Fin (r + 1)) :
    Disjoint (precedingRows pivot)
      (diamondSucceedingRows target pivot) := by
  apply Finset.disjoint_left.mpr
  intro a ha hb
  exact (not_lt_of_ge
    ((mem_diamondSucceedingRows target pivot a).mp hb).2.le)
      ((mem_precedingRows a pivot).mp ha)

theorem precedingDiamondSubset_union
    {r : ℕ} (target pivot : Fin (r + 1))
    (L U : Finset (Fin (r + 1)))
    (hL : L ⊆ precedingRows pivot)
    (hU : U ⊆ diamondSucceedingRows target pivot) :
    precedingDiamondSubset pivot (L ∪ U) = L := by
  ext a
  simp only [precedingDiamondSubset, Finset.mem_filter, Finset.mem_union]
  constructor
  · rintro ⟨haL | haU, hlow⟩
    · exact haL
    · exact False.elim ((not_lt_of_ge
        ((mem_diamondSucceedingRows target pivot a).mp (hU haU)).2.le) hlow)
  · intro ha
    exact ⟨Or.inl ha, (mem_precedingRows a pivot).mp (hL ha)⟩

theorem succeedingDiamondSubset_union
    {r : ℕ} (target pivot : Fin (r + 1))
    (L U : Finset (Fin (r + 1)))
    (hL : L ⊆ precedingRows pivot)
    (hU : U ⊆ diamondSucceedingRows target pivot) :
    succeedingDiamondSubset pivot (L ∪ U) = U := by
  ext a
  simp only [succeedingDiamondSubset, Finset.mem_filter, Finset.mem_union]
  constructor
  · rintro ⟨haL | haU, hhigh⟩
    · exact False.elim ((not_lt_of_ge hhigh.le)
        ((mem_precedingRows a pivot).mp (hL haL)))
    · exact haU
  · intro ha
    exact ⟨Or.inr ha,
      ((mem_diamondSucceedingRows target pivot a).mp (hU ha)).2⟩

theorem pivot_not_mem_preceding_union_succeeding
    {r : ℕ} (target pivot : Fin (r + 1))
    (L U : Finset (Fin (r + 1)))
    (hL : L ⊆ precedingRows pivot)
    (hU : U ⊆ diamondSucceedingRows target pivot) :
    pivot ∉ L ∪ U := by
  intro h
  rcases Finset.mem_union.mp h with h | h
  · exact (lt_irrefl pivot)
      ((mem_precedingRows pivot pivot).mp (hL h))
  · exact (lt_irrefl pivot)
      ((mem_diamondSucceedingRows target pivot pivot).mp (hU h)).2

theorem polarizationPathCoefficient_insert_union_factor
    {r : ℕ} (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam)
    (target pivot : Fin (r + 1)) (hpivot : pivot < target)
    (L U : Finset (Fin (r + 1)))
    (hL : L ⊆ precedingRows pivot)
    (hU : U ⊆ diamondSucceedingRows target pivot) :
    polarizationPathCoefficient lam target (insert pivot (L ∪ U)) =
      -upperDiamondPathCoefficient lam target pivot U *
        spectralPathCoeff lam pivot
          (shiftedRowGap lam target pivot + 1) L := by
  rw [polarizationPathCoefficient_insert_pivot_factor
    lam hdom target pivot hpivot (L ∪ U)
      (pivot_not_mem_preceding_union_succeeding
        target pivot L U hL hU),
    precedingDiamondSubset_union target pivot L U hL hU]
  congr 2
  unfold upperDiamondPathCoefficient
  have hupper : succeedingDiamondSubset pivot (L ∪ U) = U :=
    succeedingDiamondSubset_union target pivot L U hL hU
  have hself : succeedingDiamondSubset pivot U = U := by
    ext a
    simp only [succeedingDiamondSubset, Finset.mem_filter]
    constructor
    · exact And.left
    · intro ha
      exact ⟨ha,
        ((mem_diamondSucceedingRows target pivot a).mp (hU ha)).2⟩
  rw [hupper, hself]

private def diamondUpperSuffixNext {r : ℕ}
    (target : Fin (r + 1)) (U : Finset (Fin (r + 1))) : Fin (r + 1) :=
  ((U.sort (· ≤ ·)) ++ [target]).headD target

private def diamondUpperSuffixTail {r : ℕ}
    (target : Fin (r + 1)) (U : Finset (Fin (r + 1))) :
    List (Fin (r + 1)) :=
  ((U.sort (· ≤ ·)) ++ [target]).tail

theorem upperDiamondSuffix_eq_next_cons_tail
    {r : ℕ} (target : Fin (r + 1))
    (U : Finset (Fin (r + 1))) :
    (U.sort (· ≤ ·)) ++ [target] =
      diamondUpperSuffixNext target U :: diamondUpperSuffixTail target U := by
  have hnon : (U.sort (· ≤ ·)) ++ [target] ≠ [] := by
    intro h
    have hmem : target ∈ (U.sort (· ≤ ·)) ++ [target] := by simp only [List.mem_append,
                                                              Finset.mem_sort, List.mem_cons,
                                                              List.not_mem_nil, or_false, or_true]
    rw [h] at hmem
    simp only [List.not_mem_nil] at hmem
  unfold diamondUpperSuffixNext diamondUpperSuffixTail
  cases hpath : (U.sort (· ≤ ·)) ++ [target] with
  | nil => exact False.elim (hnon hpath)
  | cons a tail => simp only [List.headD_eq_head?_getD, List.head?_cons, Option.getD_some,
                     List.tail_cons]

theorem polarizationPathStart_union_eq_lower_next
    {r : ℕ} (target pivot next : Fin (r + 1))
    (L U : Finset (Fin (r + 1))) (tail : List (Fin (r + 1)))
    (hL : L ⊆ precedingRows pivot)
    (hU : U ⊆ diamondSucceedingRows target pivot)
    (hupper : (U.sort (· ≤ ·)) ++ [target] = next :: tail) :
    polarizationPathStart target (L ∪ U) =
      polarizationPathStart next L := by
  have hnot := pivot_not_mem_preceding_union_succeeding
    target pivot L U hL hU
  rw [← sort_headD_eq_polarizationPathStart target (L ∪ U),
    sort_eq_preceding_append_succeeding pivot (L ∪ U) hnot,
    precedingDiamondSubset_union target pivot L U hL hU,
    succeedingDiamondSubset_union target pivot L U hL hU,
    ← sort_headD_eq_polarizationPathStart next L]
  cases hlower : L.sort (· ≤ ·) with
  | nil =>
      simp only [List.nil_append, List.headD_nil]
      have hhead :
          (U.sort (· ≤ ·)).headD target =
            ((U.sort (· ≤ ·)) ++ [target]).headD target := by
        cases U.sort (· ≤ ·) <;> rfl
      rw [hhead, hupper]
      rfl
  | cons a rest => simp only [List.cons_append, List.headD_eq_head?_getD, List.head?_cons,
                     Option.getD_some]

theorem polarizationPathStart_insert_union_eq_lower_pivot
    {r : ℕ} (target pivot : Fin (r + 1))
    (L U : Finset (Fin (r + 1)))
    (hL : L ⊆ precedingRows pivot)
    (hU : U ⊆ diamondSucceedingRows target pivot) :
    polarizationPathStart target (insert pivot (L ∪ U)) =
      polarizationPathStart pivot L := by
  have hnot := pivot_not_mem_preceding_union_succeeding
    target pivot L U hL hU
  rw [← sort_headD_eq_polarizationPathStart target (insert pivot (L ∪ U)),
    sort_insert_eq_preceding_cons_succeeding pivot (L ∪ U) hnot,
    precedingDiamondSubset_union target pivot L U hL hU,
    succeedingDiamondSubset_union target pivot L U hL hU,
    ← sort_headD_eq_polarizationPathStart pivot L]
  cases hlower : L.sort (· ≤ ·) <;> simp

theorem omittedDiamondPrefix_union_eq_lowerPath
    {r n : ℕ} (target pivot next : Fin (r + 1)) (k : Fin n)
    (L U : Finset (Fin (r + 1))) (tail : List (Fin (r + 1)))
    (hL : L ⊆ precedingRows pivot)
    (hU : U ⊆ diamondSucceedingRows target pivot)
    (hupper : (U.sort (· ≤ ·)) ++ [target] = next :: tail) :
    omittedDiamondPrefix target k (L ∪ U)
        (L.sort (· ≤ ·)) next =
      diamondPathOperator next k L := by
  unfold omittedDiamondPrefix diamondPathOperator axialCoordinateLowerPath
  rw [polarizationPathStart_union_eq_lower_next
    target pivot next L U tail hL hU hupper]

theorem insertedDiamondPrefix_union_eq_lowerPath_comp_root
    {r n : ℕ} (target pivot next : Fin (r + 1)) (k : Fin n)
    (L U : Finset (Fin (r + 1)))
    (hL : L ⊆ precedingRows pivot)
    (hU : U ⊆ diamondSucceedingRows target pivot) :
    insertedDiamondPrefix target pivot k (L ∪ U)
        (L.sort (· ≤ ·)) next =
      (diamondPathOperator pivot k L).comp
        (polarization r n next pivot) := by
  unfold insertedDiamondPrefix diamondPathOperator axialCoordinateLowerPath
  rw [polarizationPathStart_insert_union_eq_lower_pivot
    target pivot L U hL hU]

private def localSpectralDiamondResidual {r n : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (target pivot next : Fin (r + 1)) (k : Fin n)
    (L : Finset (Fin (r + 1))) :
    PolynomialSpace r n →ₗ[ℝ] PolynomialSpace r n :=
  let Z := arbitraryRowAxialRaise lam pivot k
  let omitted := diamondPathOperator next k L
  let inserted := (diamondPathOperator pivot k L).comp
    (polarization r n next pivot)
  ((inserted.comp Z - Z.comp inserted) -
    shiftedRowGap lam target pivot •
      (omitted.comp Z - Z.comp omitted)) - omitted.comp Z

private def spectralDiamondPrefixResidual {r n : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (target pivot next : Fin (r + 1)) (k : Fin n) :
    PolynomialSpace r n →ₗ[ℝ] PolynomialSpace r n :=
  let h := shiftedRowGap lam target pivot
  let Z := arbitraryRowAxialRaise lam pivot k
  let diagonal := spectralPathOperator lam pivot pivot k (h + 1)
  let offdiagonal := spectralPathOperator lam pivot next k (h + 1)
  (((diagonal.comp (polarization r n next pivot)).comp Z -
      Z.comp (diagonal.comp (polarization r n next pivot))) -
    h • (offdiagonal.comp Z - Z.comp offdiagonal)) -
      offdiagonal.comp Z

private def spectralDiamondResidualTransform {r n : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (target pivot next : Fin (r + 1)) (k : Fin n) :
    ((PolynomialSpace r n →ₗ[ℝ] PolynomialSpace r n) ×
      (PolynomialSpace r n →ₗ[ℝ] PolynomialSpace r n)) →ₗ[ℝ]
        (PolynomialSpace r n →ₗ[ℝ] PolynomialSpace r n) :=
  let E := PolynomialSpace r n
  let Z := arbitraryRowAxialRaise lam pivot k
  let rightRoot : (E →ₗ[ℝ] E) →ₗ[ℝ] (E →ₗ[ℝ] E) :=
    LinearMap.lcomp ℝ E (polarization r n next pivot)
  let rightZ : (E →ₗ[ℝ] E) →ₗ[ℝ] (E →ₗ[ℝ] E) :=
    LinearMap.lcomp ℝ E Z
  let leftZ : (E →ₗ[ℝ] E) →ₗ[ℝ] (E →ₗ[ℝ] E) :=
    LinearMap.compRight ℝ Z
  let comm := rightZ - leftZ
  ((comm.comp rightRoot).comp (LinearMap.fst ℝ (E →ₗ[ℝ] E) (E →ₗ[ℝ] E))) -
    (((shiftedRowGap lam target pivot • comm + rightZ)).comp
      (LinearMap.snd ℝ (E →ₗ[ℝ] E) (E →ₗ[ℝ] E)))

@[simp] theorem spectralDiamondResidualTransform_apply
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (target pivot next : Fin (r + 1)) (k : Fin n)
    (A B : PolynomialSpace r n →ₗ[ℝ] PolynomialSpace r n) :
    spectralDiamondResidualTransform lam target pivot next k (A, B) =
      ((((A.comp (polarization r n next pivot)).comp
          (arbitraryRowAxialRaise lam pivot k) -
        (arbitraryRowAxialRaise lam pivot k).comp
          (A.comp (polarization r n next pivot))) -
        shiftedRowGap lam target pivot •
          (B.comp (arbitraryRowAxialRaise lam pivot k) -
            (arbitraryRowAxialRaise lam pivot k).comp B)) -
        B.comp (arbitraryRowAxialRaise lam pivot k)) := by
  unfold spectralDiamondResidualTransform
  simp only [LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.fst_apply, LinearMap.snd_apply, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.compRight_apply]
  apply LinearMap.ext
  intro p
  simp only [LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.lcomp_apply]
  module

theorem sum_spectralLocalDiamondResidual_eq_spectralPrefix
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (target pivot next : Fin (r + 1)) (k : Fin n) :
    (∑ L ∈ (precedingRows pivot).powerset,
      spectralPathCoeff lam pivot (shiftedRowGap lam target pivot + 1) L •
        localSpectralDiamondResidual lam target pivot next k L) =
      spectralDiamondPrefixResidual lam target pivot next k := by
  let T := spectralDiamondResidualTransform lam target pivot next k
  let path (L : Finset (Fin (r + 1))) :
      (PolynomialSpace r n →ₗ[ℝ] PolynomialSpace r n) ×
        (PolynomialSpace r n →ₗ[ℝ] PolynomialSpace r n) :=
    (diamondPathOperator pivot k L, diamondPathOperator next k L)
  have hlocal (L : Finset (Fin (r + 1))) :
      T (path L) =
        localSpectralDiamondResidual lam target pivot next k L := by
    unfold T path localSpectralDiamondResidual
    exact spectralDiamondResidualTransform_apply lam target pivot next k
      (diamondPathOperator pivot k L) (diamondPathOperator next k L)
  have hsum :
      (∑ L ∈ (precedingRows pivot).powerset,
        spectralPathCoeff lam pivot (shiftedRowGap lam target pivot + 1) L •
          localSpectralDiamondResidual lam target pivot next k L) =
        T (∑ L ∈ (precedingRows pivot).powerset,
          spectralPathCoeff lam pivot (shiftedRowGap lam target pivot + 1) L •
            path L) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro L _
    rw [map_smul, hlocal]
  rw [hsum]
  have hpair :
      (∑ L ∈ (precedingRows pivot).powerset,
        spectralPathCoeff lam pivot (shiftedRowGap lam target pivot + 1) L •
          path L) =
        (spectralPathOperator lam pivot pivot k
          (shiftedRowGap lam target pivot + 1),
          spectralPathOperator lam pivot next k
            (shiftedRowGap lam target pivot + 1)) := by
    apply Prod.ext
    · simp only [Prod.smul_mk, Prod.fst_sum, spectralPathOperator, path]
    · simp only [Prod.smul_mk, Prod.snd_sum, spectralPathOperator, path]
  rw [hpair]
  unfold T spectralDiamondPrefixResidual
  exact spectralDiamondResidualTransform_apply lam target pivot next k
    (spectralPathOperator lam pivot pivot k
      (shiftedRowGap lam target pivot + 1))
    (spectralPathOperator lam pivot next k
      (shiftedRowGap lam target pivot + 1))

theorem diamondPairResidual_union_eq_local_comp_suffix
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (target pivot next : Fin (r + 1)) (hpivot : pivot < target)
    (k : Fin n) (L U : Finset (Fin (r + 1)))
    (tail : List (Fin (r + 1)))
    (hL : L ⊆ precedingRows pivot)
    (hU : U ⊆ diamondSucceedingRows target pivot)
    (hupper : (U.sort (· ≤ ·)) ++ [target] = next :: tail) :
    diamondPairResidual lam target pivot k (L ∪ U) =
      (localSpectralDiamondResidual lam target pivot next k L).comp
        (lowerPolarizationPath (next :: tail)) := by
  have hnot := pivot_not_mem_preceding_union_succeeding
    target pivot L U hL hU
  have hsorted :
      ((L ∪ U).sort (· ≤ ·)) ++ [target] =
        (L.sort (· ≤ ·)) ++ next :: tail := by
    rw [sort_eq_preceding_append_succeeding pivot (L ∪ U) hnot,
      precedingDiamondSubset_union target pivot L U hL hU,
      succeedingDiamondSubset_union target pivot L U hL hU,
      List.append_assoc, hupper]
  have hinsert :
      ((insert pivot (L ∪ U)).sort (· ≤ ·)) ++ [target] =
        (L.sort (· ≤ ·)) ++ pivot :: next :: tail := by
    rw [sort_insert_eq_preceding_cons_succeeding
      pivot (L ∪ U) hnot,
      precedingDiamondSubset_union target pivot L U hL hU,
      succeedingDiamondSubset_union target pivot L U hL hU,
      List.append_assoc]
    simp only [List.cons_append]
    rw [hupper]
  have hnext : pivot < next := by
    have hmem : next ∈ (U.sort (· ≤ ·)) ++ [target] := by
      rw [hupper]
      simp only [List.mem_cons, true_or]
    rcases List.mem_append.mp hmem with hmem | hmem
    · exact ((mem_diamondSucceedingRows target pivot next).mp
        (hU ((Finset.mem_sort (· ≤ ·)).mp hmem))).2
    · have hnexttarget : next = target := by simpa only [List.mem_cons, List.not_mem_nil,
                                               or_false] using hmem
      simpa only [hnexttarget, gt_iff_lt] using hpivot
  have htail : ∀ a ∈ tail, pivot < a := by
    intro a ha
    have hmem : a ∈ (U.sort (· ≤ ·)) ++ [target] := by
      rw [hupper]
      simp only [List.mem_cons, ha, or_true]
    rcases List.mem_append.mp hmem with hmem | hmem
    · exact ((mem_diamondSucceedingRows target pivot a).mp
        (hU ((Finset.mem_sort (· ≤ ·)).mp hmem))).2
    · have hatarget : a = target := by simpa only [List.mem_cons, List.not_mem_nil,
                                         or_false] using hmem
      simpa only [hatarget, gt_iff_lt] using hpivot
  rw [diamondPairResidual_eq_prefix_comp_suffix
    lam target pivot k (L ∪ U) (L.sort (· ≤ ·)) next tail
      hsorted hinsert hnext htail]
  unfold diamondPrefixResidual localSpectralDiamondResidual
  rw [omittedDiamondPrefix_union_eq_lowerPath
    target pivot next k L U tail hL hU hupper,
    insertedDiamondPrefix_union_eq_lowerPath_comp_root
      target pivot next k L U hL hU]

theorem sum_weightedDiamondPairResidual_eq_sum_upper_lower
    {r n : ℕ} (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam)
    (target pivot : Fin (r + 1)) (hpivot : pivot < target)
    (k : Fin n) :
    (∑ S ∈ ((precedingRows target).erase pivot).powerset,
      polarizationPathCoefficient lam target (insert pivot S) •
        diamondPairResidual lam target pivot k S) =
      -(∑ U ∈ (diamondSucceedingRows target pivot).powerset,
        upperDiamondPathCoefficient lam target pivot U •
          (∑ L ∈ (precedingRows pivot).powerset,
            spectralPathCoeff lam pivot
              (shiftedRowGap lam target pivot + 1) L •
                diamondPairResidual lam target pivot k (L ∪ U))) := by
  classical
  rw [precedingRows_erase_pivot_eq_union target pivot hpivot,
    sum_powerset_disjoint_union (precedingRows pivot)
      (diamondSucceedingRows target pivot)
      (precedingRows_disjoint_diamondSucceedingRows target pivot)]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro U hU
  have hUsub : U ⊆ diamondSucceedingRows target pivot :=
    Finset.mem_powerset.mp hU
  rw [Finset.smul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro L hL
  rw [polarizationPathCoefficient_insert_union_factor
    lam hdom target pivot hpivot L U
      (Finset.mem_powerset.mp hL) hUsub]
  module

theorem pivot_lt_diamondUpperSuffixNext
    {r : ℕ} (target pivot : Fin (r + 1)) (hpivot : pivot < target)
    (U : Finset (Fin (r + 1)))
    (hU : U ⊆ diamondSucceedingRows target pivot) :
    pivot < diamondUpperSuffixNext target U := by
  let next := diamondUpperSuffixNext target U
  have hupper := upperDiamondSuffix_eq_next_cons_tail target U
  have hmem : next ∈ (U.sort (· ≤ ·)) ++ [target] := by
    rw [hupper]
    simp only [List.mem_cons, true_or, next]
  rcases List.mem_append.mp hmem with hmem | hmem
  · exact ((mem_diamondSucceedingRows target pivot next).mp
      (hU ((Finset.mem_sort (· ≤ ·)).mp hmem))).2
  · have hnexttarget : next = target := by simpa only [List.mem_cons, List.not_mem_nil,
                                             or_false] using hmem
    simpa [next, hnexttarget] using hpivot

theorem sum_weightedDiamondPairResidual_eq_sum_spectralPrefix_suffix
    {r n : ℕ} (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam)
    (target pivot : Fin (r + 1)) (hpivot : pivot < target)
    (k : Fin n) :
    (∑ S ∈ ((precedingRows target).erase pivot).powerset,
      polarizationPathCoefficient lam target (insert pivot S) •
        diamondPairResidual lam target pivot k S) =
      -(∑ U ∈ (diamondSucceedingRows target pivot).powerset,
        upperDiamondPathCoefficient lam target pivot U •
          (spectralDiamondPrefixResidual lam target pivot
            (diamondUpperSuffixNext target U) k).comp
              (lowerPolarizationPath
                ((U.sort (· ≤ ·)) ++ [target]))) := by
  classical
  rw [sum_weightedDiamondPairResidual_eq_sum_upper_lower
    lam hdom target pivot hpivot k, neg_inj]
  apply Finset.sum_congr rfl
  intro U hU
  have hUsub : U ⊆ diamondSucceedingRows target pivot :=
    Finset.mem_powerset.mp hU
  let next := diamondUpperSuffixNext target U
  let tail := diamondUpperSuffixTail target U
  have hupper : (U.sort (· ≤ ·)) ++ [target] = next :: tail :=
    upperDiamondSuffix_eq_next_cons_tail target U
  congr 1
  rw [hupper]
  calc
    (∑ L ∈ (precedingRows pivot).powerset,
      spectralPathCoeff lam pivot (shiftedRowGap lam target pivot + 1) L •
        diamondPairResidual lam target pivot k (L ∪ U)) =
      (∑ L ∈ (precedingRows pivot).powerset,
        spectralPathCoeff lam pivot (shiftedRowGap lam target pivot + 1) L •
          localSpectralDiamondResidual lam target pivot next k L).comp
            (lowerPolarizationPath (next :: tail)) := by
      apply LinearMap.ext
      intro p
      simp only [LinearMap.sum_apply, LinearMap.smul_apply,
        LinearMap.comp_apply]
      apply Finset.sum_congr rfl
      intro L hL
      rw [diamondPairResidual_union_eq_local_comp_suffix
        lam target pivot next hpivot k L U tail
          (Finset.mem_powerset.mp hL) hUsub hupper]
      rfl
    _ = (spectralDiamondPrefixResidual lam target pivot next k).comp
          (lowerPolarizationPath (next :: tail)) := by
      rw [sum_spectralLocalDiamondResidual_eq_spectralPrefix
        lam target pivot next k]

end ArbitraryRowSameAxisDiamondSuffixSummation

end

section


open scoped BigOperators

namespace ArbitraryRowSameAxisDiamondSpectralRootTransport

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonPathCommutator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondPathCommutator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondRootCommutator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralPath

theorem upperPolarizationPathCommutator_append_pivot
    {r n : ℕ} (pivot target : Fin (r + 1)) (hpt : pivot < target)
    (front : List (Fin (r + 1))) (hnon : front ≠ [])
    (hfront : ∀ a ∈ front, a < pivot) :
    upperPolarizationPathCommutator (n := n) target pivot
        (front ++ [pivot]) =
      lowerPolarizationPath (n := n) (front ++ [target]) := by
  induction front with
  | nil => exact False.elim (hnon rfl)
  | cons first rest ih =>
      have hfirst : first < pivot := hfront first (by simp only [List.mem_cons, true_or])
      have hfirstTarget : first ≠ target :=
        ne_of_lt (hfirst.trans hpt)
      cases rest with
      | nil =>
          simp only [List.cons_append, List.nil_append, upperPolarizationPathCommutator,
            LinearMap.comp_zero, ↓reduceIte, lowerPolarizationPath, LinearMap.comp_id, zero_add,
            hfirstTarget, sub_zero]
      | cons second tail =>
          have hsecond : second < pivot := hfront second (by simp only [List.mem_cons, true_or,
                                                               or_true])
          have hpivotSecond : pivot ≠ second := ne_of_gt hsecond
          have hrest : ∀ a ∈ (second :: tail), a < pivot := by
            intro a ha
            exact hfront a (by simp only [List.mem_cons, ha, or_true])
          change
            (polarization r n second first).comp
                  (upperPolarizationPathCommutator target pivot
                    ((second :: tail) ++ [pivot])) +
                (if pivot = second then
                  (polarization r n target first).comp
                    (lowerPolarizationPath ((second :: tail) ++ [pivot]))
                else 0) -
                (if first = target then
                  (polarization r n second pivot).comp
                    (lowerPolarizationPath ((second :: tail) ++ [pivot]))
                else 0) =
              (polarization r n second first).comp
                (lowerPolarizationPath ((second :: tail) ++ [target]))
          rw [ite_eq_right hpivotSecond, ite_eq_right hfirstTarget,
            ih (by simp only [ne_eq, reduceCtorEq, not_false_eq_true]) hrest]
          simp only [List.cons_append, add_zero, sub_zero]

theorem polarization_diamondPathOperator_pivot_sub
    {r n : ℕ} (pivot target : Fin (r + 1)) (hpt : pivot < target)
    (k : Fin n) (S : Finset (Fin (r + 1)))
    (hS : S ⊆ precedingRows pivot)
    (p : PolynomialSpace r n) :
    polarization r n target pivot (diamondPathOperator pivot k S p) -
        diamondPathOperator pivot k S
          (polarization r n target pivot p) =
      diamondPathOperator target k S p := by
  classical
  by_cases hnon : S.Nonempty
  · have hstart : polarizationPathStart pivot S < pivot :=
      polarizationPathStart_lt_of_nonempty pivot S hnon hS
    have hstart_ne : pivot ≠ polarizationPathStart pivot S :=
      ne_of_gt hstart
    have hstarts : polarizationPathStart target S =
        polarizationPathStart pivot S := by
      simp only [polarizationPathStart, hnon, ↓reduceDIte]
    have hlistnon : S.sort (· ≤ ·) ≠ [] := by
      intro h
      have hempty : S = ∅ := by
        simpa only [Finset.sort_toFinset, List.toFinset_nil] using congrArg List.toFinset h
      exact hnon.ne_empty hempty
    have hlist : ∀ a ∈ S.sort (· ≤ ·), a < pivot := by
      intro a ha
      exact (mem_precedingRows a pivot).mp
        (hS ((Finset.mem_sort (· ≤ ·)).mp ha))
    rw [diamondPathOperator_apply, diamondPathOperator_apply,
      polarization_axialCoordinate_mul_lowerPolarizationPath_sub,
      ite_eq_right hstart_ne, zero_add,
      upperPolarizationPathCommutator_append_pivot
        pivot target hpt (S.sort (· ≤ ·)) hlistnon hlist]
    simp [diamondPathOperator_apply, hstarts]
  · have hempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnon
    subst S
    simp only [diamondPathOperator_apply, polarizationPathStart_empty,
      Finset.sort_empty, List.nil_append, lowerPolarizationPath,
      LinearMap.id_apply]
    rw [polarization_mul_euler, polarization_X_euler]
    simp only [↓reduceIte, polarization_apply, add_sub_cancel_right]

theorem upperPolarizationPathCommutator_later_target_eq_zero
    {r n : ℕ} (pivot rootTarget target : Fin (r + 1))
    (hroot : pivot < rootTarget) (htarget : pivot < target)
    (front : List (Fin (r + 1)))
    (hfront : ∀ a ∈ front, a < pivot) :
    upperPolarizationPathCommutator (n := n) rootTarget pivot
        (front ++ [target]) = 0 := by
  induction front with
  | nil => simp only [List.nil_append, upperPolarizationPathCommutator_singleton]
  | cons first rest ih =>
      have hfirst : first < pivot := hfront first (by simp only [List.mem_cons, true_or])
      have hfirstRoot : first ≠ rootTarget :=
        ne_of_lt (hfirst.trans hroot)
      cases rest with
      | nil =>
          have hpivotTarget : pivot ≠ target := ne_of_lt htarget
          simp only [List.cons_append, List.nil_append, upperPolarizationPathCommutator,
            LinearMap.comp_zero, hpivotTarget, ↓reduceIte, add_zero, hfirstRoot, sub_self]
      | cons second tail =>
          have hsecond : second < pivot := hfront second (by simp only [List.mem_cons, true_or,
                                                               or_true])
          have hpivotSecond : pivot ≠ second := ne_of_gt hsecond
          have hrest : ∀ a ∈ (second :: tail), a < pivot := by
            intro a ha
            exact hfront a (by simp only [List.mem_cons, ha, or_true])
          change
            (polarization r n second first).comp
                  (upperPolarizationPathCommutator rootTarget pivot
                    ((second :: tail) ++ [target])) +
                (if pivot = second then
                  (polarization r n rootTarget first).comp
                    (lowerPolarizationPath ((second :: tail) ++ [target]))
                else 0) -
                (if first = rootTarget then
                  (polarization r n second pivot).comp
                    (lowerPolarizationPath ((second :: tail) ++ [target]))
                else 0) = 0
          rw [ite_eq_right hpivotSecond, ite_eq_right hfirstRoot, ih hrest]
          simp only [LinearMap.comp_zero, add_zero, sub_self]

theorem polarization_diamondPathOperator_later_target_sub_eq_zero
    {r n : ℕ} (pivot rootTarget target : Fin (r + 1))
    (hroot : pivot < rootTarget) (htarget : pivot < target)
    (k : Fin n) (S : Finset (Fin (r + 1)))
    (hS : S ⊆ precedingRows pivot)
    (p : PolynomialSpace r n) :
    polarization r n rootTarget pivot
          (diamondPathOperator target k S p) -
        diamondPathOperator target k S
          (polarization r n rootTarget pivot p) = 0 := by
  classical
  have hstart : pivot ≠ polarizationPathStart target S := by
    by_cases hnon : S.Nonempty
    · have hbefore : polarizationPathStart target S < pivot := by
        rw [polarizationPathStart, dite_eq_left hnon]
        exact (mem_precedingRows _ pivot).mp
          (hS (Finset.min'_mem S hnon))
      exact ne_of_gt hbefore
    · have hempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnon
      simp only [hempty, polarizationPathStart_empty, ne_eq, ne_of_lt htarget, not_false_eq_true]
  have hlist : ∀ a ∈ S.sort (· ≤ ·), a < pivot := by
    intro a ha
    exact (mem_precedingRows a pivot).mp
      (hS ((Finset.mem_sort (· ≤ ·)).mp ha))
  rw [diamondPathOperator_apply, diamondPathOperator_apply,
    polarization_axialCoordinate_mul_lowerPolarizationPath_sub,
    ite_eq_right hstart,
    upperPolarizationPathCommutator_later_target_eq_zero
      pivot rootTarget target hroot htarget
      (S.sort (· ≤ ·)) hlist]
  simp only [LinearMap.zero_apply, mul_zero, add_zero]

theorem polarization_spectralPathOperator_later_target_sub_eq_zero
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (pivot rootTarget target : Fin (r + 1))
    (hroot : pivot < rootTarget) (htarget : pivot < target)
    (k : Fin n) (t : ℝ) (p : PolynomialSpace r n) :
    polarization r n rootTarget pivot
          (spectralPathOperator lam pivot target k t p) -
        spectralPathOperator lam pivot target k t
          (polarization r n rootTarget pivot p) = 0 := by
  classical
  rw [spectralPathOperator_apply, map_sum,
    spectralPathOperator_apply, ← Finset.sum_sub_distrib]
  apply Finset.sum_eq_zero
  intro S hS
  rw [map_smul, ← smul_sub,
    polarization_diamondPathOperator_later_target_sub_eq_zero
      pivot rootTarget target hroot htarget k S
      (Finset.mem_powerset.mp hS), smul_zero]

theorem polarization_comp_spectralPathOperator_later_target_commute
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (pivot rootTarget target : Fin (r + 1))
    (hroot : pivot < rootTarget) (htarget : pivot < target)
    (k : Fin n) (t : ℝ) :
    (polarization r n rootTarget pivot).comp
          (spectralPathOperator lam pivot target k t) =
        (spectralPathOperator lam pivot target k t).comp
          (polarization r n rootTarget pivot) := by
  apply LinearMap.ext
  intro p
  exact sub_eq_zero.mp
    (polarization_spectralPathOperator_later_target_sub_eq_zero
      lam pivot rootTarget target hroot htarget k t p)

theorem polarization_spectralPathOperator_self_sub
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (pivot target : Fin (r + 1)) (hpt : pivot < target)
    (k : Fin n) (t : ℝ) (p : PolynomialSpace r n) :
    polarization r n target pivot
          (spectralPathOperator lam pivot pivot k t p) -
        spectralPathOperator lam pivot pivot k t
          (polarization r n target pivot p) =
      spectralPathOperator lam pivot target k t p := by
  classical
  rw [spectralPathOperator_apply, map_sum,
    spectralPathOperator_apply, spectralPathOperator_apply,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro S hS
  rw [map_smul, ← smul_sub,
    polarization_diamondPathOperator_pivot_sub
      pivot target hpt k S (Finset.mem_powerset.mp hS)]

theorem polarization_comp_spectralPathOperator_self_sub
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (pivot target : Fin (r + 1)) (hpt : pivot < target)
    (k : Fin n) (t : ℝ) :
    (polarization r n target pivot).comp
          (spectralPathOperator lam pivot pivot k t) -
        (spectralPathOperator lam pivot pivot k t).comp
          (polarization r n target pivot) =
      spectralPathOperator lam pivot target k t := by
  apply LinearMap.ext
  intro p
  exact polarization_spectralPathOperator_self_sub
    lam pivot target hpt k t p

theorem polarization_comp_arbitraryRowAxialRaise_sub
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (pivot target : Fin (r + 1)) (hpt : pivot < target)
    (k : Fin n) :
    (polarization r n target pivot).comp
          (arbitraryRowAxialRaise lam pivot k) -
        (arbitraryRowAxialRaise lam pivot k).comp
          (polarization r n target pivot) =
      spectralPathOperator lam pivot target k 0 := by
  simpa only [spectralPathOperator_self_zero] using
    polarization_comp_spectralPathOperator_self_sub lam pivot target hpt k 0

end ArbitraryRowSameAxisDiamondSpectralRootTransport

end

section


open scoped BigOperators

namespace ArbitraryRowSameAxisDiamondUniversalPluckerCancellation

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankLowerRowBranching
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonHighest
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondFullCommutator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondGapDifference
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondPathCommutator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondResidualSuffixPartition
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralPath
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralRootTransport
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSuffixCoefficientFactor

theorem spectralBooleanPrefixResidual_eq_zero_of_rtt
    {r n : ℕ}
    (A B C D E : PolynomialSpace r n →ₗ[ℝ] PolynomialSpace r n)
    (h : ℝ)
    (hcomm : A.comp B = B.comp A)
    (hroot : E.comp B - B.comp E = D)
    (hrtt : (h + 1) • (C.comp B - B.comp C) =
      A.comp D - B.comp C) :
    (((A.comp E).comp B - B.comp (A.comp E)) -
        h • (C.comp B - B.comp C)) - C.comp B = 0 := by
  have htransport :
      (A.comp E).comp B - B.comp (A.comp E) = A.comp D := by
    calc
      (A.comp E).comp B - B.comp (A.comp E) =
          A.comp (E.comp B) - (B.comp A).comp E := by
            simp only [LinearMap.comp_assoc]
      _ = A.comp (E.comp B) - (A.comp B).comp E := by rw [hcomm]
      _ = A.comp (E.comp B - B.comp E) := by
            rw [LinearMap.comp_sub, LinearMap.comp_assoc]
      _ = A.comp D := by rw [hroot]
  rw [htransport]
  have hrelation :
      A.comp D = (h + 1) • (C.comp B - B.comp C) + B.comp C := by
    rw [hrtt]
    module
  rw [hrelation]
  module

theorem spectralPathPrefixResidual_eq_zero_of_rtt
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (pivot next : Fin (r + 1)) (hpivot : pivot < next)
    (k : Fin n) (h : ℝ)
    (hcomm :
      (spectralPathOperator lam pivot pivot k (h + 1)).comp
          (arbitraryRowAxialRaise lam pivot k) =
        (arbitraryRowAxialRaise lam pivot k).comp
          (spectralPathOperator lam pivot pivot k (h + 1)))
    (hrtt :
      (h + 1) •
          ((spectralPathOperator lam pivot next k (h + 1)).comp
              (arbitraryRowAxialRaise lam pivot k) -
            (arbitraryRowAxialRaise lam pivot k).comp
              (spectralPathOperator lam pivot next k (h + 1))) =
        (spectralPathOperator lam pivot pivot k (h + 1)).comp
            (spectralPathOperator lam pivot next k 0) -
          (arbitraryRowAxialRaise lam pivot k).comp
            (spectralPathOperator lam pivot next k (h + 1))) :
    ((((spectralPathOperator lam pivot pivot k (h + 1)).comp
            (polarization r n next pivot)).comp
          (arbitraryRowAxialRaise lam pivot k) -
        (arbitraryRowAxialRaise lam pivot k).comp
          ((spectralPathOperator lam pivot pivot k (h + 1)).comp
            (polarization r n next pivot))) -
      h •
        ((spectralPathOperator lam pivot next k (h + 1)).comp
            (arbitraryRowAxialRaise lam pivot k) -
          (arbitraryRowAxialRaise lam pivot k).comp
            (spectralPathOperator lam pivot next k (h + 1)))) -
      (spectralPathOperator lam pivot next k (h + 1)).comp
        (arbitraryRowAxialRaise lam pivot k) = 0 := by
  exact spectralBooleanPrefixResidual_eq_zero_of_rtt
    (spectralPathOperator lam pivot pivot k (h + 1))
    (arbitraryRowAxialRaise lam pivot k)
    (spectralPathOperator lam pivot next k (h + 1))
    (spectralPathOperator lam pivot next k 0)
    (polarization r n next pivot) h hcomm
    (polarization_comp_arbitraryRowAxialRaise_sub lam pivot next hpivot k)
    hrtt

end ArbitraryRowSameAxisDiamondUniversalPluckerCancellation

end

section


open scoped BigOperators

namespace ArbitraryRowSameAxisDiamondSpectralAbstractRTT

open MetricCodes.Spherical.HigherHarmonicYoung

theorem spectralStep_rtt
    {r n : ℕ}
    (A B C D E F S T : PolynomialSpace r n →ₗ[ℝ] PolynomialSpace r n)
    (x y : ℝ)
    (hAB : A * B = B * A)
    (hSB : S * B - B * S = D)
    (hTA : T * A - A * T = E)
    (hTB : T * B - B * T = F)
    (hSF : S * F = F * S)
    (hTC : T * C = C * T)
    (hTD : T * D = D * T)
    (hST : S * T = T * S)
    (hcross : (x - y) • (C * F - F * C) = E * D - F * C)
    (hCB : (x - y) • (C * B - B * C) = A * D - B * C)
    (hAF : (x - y) • (A * F - F * A) = E * B - F * A)
    (hEB : (x - y) • (E * B - B * E) = A * F - B * E) :
    (x - y) •
        ((x • C - A * S) * (y • F - B * T) -
          (y • F - B * T) * (x • C - A * S)) =
      (x • E - A * T) * (y • D - B * S) -
        (y • F - B * T) * (x • C - A * S) := by
  have hSB' : S * B = B * S + D := by
    rw [← hSB]
    noncomm_ring
  have hTA' : T * A = A * T + E := by
    rw [← hTA]
    noncomm_ring
  have hTB' : T * B = B * T + F := by
    rw [← hTB]
    noncomm_ring
  have hCBT : C * (B * T) - (B * T) * C =
      (C * B - B * C) * T := by
    calc
      C * (B * T) - (B * T) * C =
          (C * B) * T - B * (T * C) := by noncomm_ring
      _ = (C * B - B * C) * T := by
            rw [hTC]
            simp only [mul_assoc, sub_mul]
  have hASF : (A * S) * F - F * (A * S) =
      (A * F - F * A) * S := by
    calc
      (A * S) * F - F * (A * S) =
          A * (S * F) - (F * A) * S := by noncomm_ring
      _ = (A * F - F * A) * S := by
            rw [hSF]
            simp only [mul_assoc, sub_mul]
  have hASBT :
      (A * S) * (B * T) - (B * T) * (A * S) =
        (A * D) * T - (B * E) * S := by
    calc
      (A * S) * (B * T) - (B * T) * (A * S) =
          (A * (S * B)) * T - (B * (T * A)) * S := by
            noncomm_ring
      _ = (A * (B * S + D)) * T -
            (B * (A * T + E)) * S := by rw [hSB', hTA']
      _ = (A * B) * (S * T) - (B * A) * (T * S) +
            (A * D) * T - (B * E) * S := by
              simp only [mul_assoc, mul_add, add_mul]
              module
      _ = (A * D) * T - (B * E) * S := by
            rw [hAB, hST]
            module
  have hATBS :
      (A * T) * (B * S) - (B * T) * (A * S) =
        (A * F - B * E) * S := by
    calc
      (A * T) * (B * S) - (B * T) * (A * S) =
          (A * (T * B)) * S - (B * (T * A)) * S := by
            noncomm_ring
      _ = (A * (B * T + F)) * S -
            (B * (A * T + E)) * S := by rw [hTB', hTA']
      _ = ((A * B - B * A) * T + A * F - B * E) * S := by
            simp only [mul_assoc, mul_add, add_mul, sub_mul]
            module
      _ = (A * F - B * E) * S := by simp only [hAB, sub_self, zero_mul, zero_add]
  have hATD : (A * T) * D = (A * D) * T := by
    calc
      (A * T) * D = A * (T * D) := by noncomm_ring
      _ = (A * D) * T := by rw [hTD]; noncomm_ring
  have hBTC : (B * T) * C = (B * C) * T := by
    calc
      (B * T) * C = B * (T * C) := by noncomm_ring
      _ = (B * C) * T := by rw [hTC]; noncomm_ring
  have hleft :
      (x • C - A * S) * (y • F - B * T) -
          (y • F - B * T) * (x • C - A * S) =
        (x * y) • (C * F - F * C) +
          (-x • (C * B - B * C) + A * D) * T +
          (-y • (A * F - F * A) - B * E) * S := by
    calc
      (x • C - A * S) * (y • F - B * T) -
          (y • F - B * T) * (x • C - A * S) =
        (x * y) • (C * F - F * C) -
          x • (C * (B * T) - (B * T) * C) -
          y • ((A * S) * F - F * (A * S)) +
          ((A * S) * (B * T) - (B * T) * (A * S)) := by
            simp only [mul_sub, sub_mul,
              Algebra.smul_mul_assoc, Algebra.mul_smul_comm,
              smul_smul, smul_sub]
            module
      _ = (x * y) • (C * F - F * C) +
          (-x • (C * B - B * C) + A * D) * T +
          (-y • (A * F - F * A) - B * E) * S := by
            rw [hCBT, hASF, hASBT]
            simp only [add_mul, sub_mul, Algebra.smul_mul_assoc]
            module
  have hright :
      (x • E - A * T) * (y • D - B * S) -
          (y • F - B * T) * (x • C - A * S) =
        (x * y) • (E * D - F * C) +
          (-x • (E * B) + y • (F * A) + A * F - B * E) * S +
          (-y • (A * D) + x • (B * C)) * T := by
    calc
      (x • E - A * T) * (y • D - B * S) -
          (y • F - B * T) * (x • C - A * S) =
        (x * y) • (E * D - F * C) -
          x • ((E * B) * S) - y • ((A * D) * T) +
          y • ((F * A) * S) + x • ((B * C) * T) +
          ((A * T) * (B * S) - (B * T) * (A * S)) := by
            simp only [mul_sub, sub_mul,
              Algebra.smul_mul_assoc, Algebra.mul_smul_comm,
              smul_smul, smul_sub]
            rw [hATD, hBTC]
            module
      _ = (x * y) • (E * D - F * C) +
          (-x • (E * B) + y • (F * A) + A * F - B * E) * S +
          (-y • (A * D) + x • (B * C)) * T := by
            rw [hATBS]
            simp only [add_mul, sub_mul, Algebra.smul_mul_assoc]
            module
  rw [hleft, hright]
  have ht :
      (x - y) • (-x • (C * B - B * C) + A * D) =
        -y • (A * D) + x • (B * C) := by
    rw [smul_add, smul_smul]
    have hscaled := congrArg (fun Z => (-x) • Z) hCB
    simp only [smul_smul] at hscaled
    rw [mul_comm (x - y) (-x), hscaled]
    simp only [smul_sub]
    module
  have hs :
      (x - y) • (-y • (A * F - F * A) - B * E) =
        -x • (E * B) + y • (F * A) + A * F - B * E := by
    rw [smul_sub, smul_smul]
    have hscaled := congrArg (fun Z => (-y) • Z) hAF
    simp only [smul_smul] at hscaled
    rw [mul_comm (x - y) (-y), hscaled]
    calc
      -y • (E * B - F * A) - (x - y) • (B * E) =
          -x • (E * B) + y • (F * A) +
            (x - y) • (E * B - B * E) := by
              simp only [smul_sub]
              module
      _ = -x • (E * B) + y • (F * A) + A * F - B * E := by
            rw [hEB]
            module
  simp only [smul_add]
  rw [smul_comm (x - y) (x * y), hcross]
  rw [← Algebra.smul_mul_assoc, ← Algebra.smul_mul_assoc, ht, hs]
  module

end ArbitraryRowSameAxisDiamondSpectralAbstractRTT

end

section


open scoped BigOperators

namespace ArbitraryRowSameAxisDiamondSpectralRTTStep

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankLowerRowBranching
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralPath
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralRootTransport
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralAbstractRTT

theorem spectralPathOperator_succ_rtt_of
    {r n : ℕ} (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam)
    (a : Fin r) (s t : Fin (r + 1))
    (hs : a.succ ≤ s) (ht : a.succ ≤ t)
    (k : Fin n) (u v : ℝ)
    (hself : ∀ w z : ℝ,
      (spectralPathOperator lam a.castSucc a.castSucc k w).comp
          (spectralPathOperator lam a.castSucc a.castSucc k z) =
        (spectralPathOperator lam a.castSucc a.castSucc k z).comp
          (spectralPathOperator lam a.castSucc a.castSucc k w))
    (hrtt : ∀ (i j : Fin (r + 1)),
      a.castSucc ≤ i → a.castSucc ≤ j → ∀ w z : ℝ,
        (w - z) •
            ((spectralPathOperator lam a.castSucc i k w).comp
                (spectralPathOperator lam a.castSucc j k z) -
              (spectralPathOperator lam a.castSucc j k z).comp
                (spectralPathOperator lam a.castSucc i k w)) =
          (spectralPathOperator lam a.castSucc j k w).comp
              (spectralPathOperator lam a.castSucc i k z) -
            (spectralPathOperator lam a.castSucc j k z).comp
              (spectralPathOperator lam a.castSucc i k w)) :
    (u - v) •
        ((spectralPathOperator lam a.succ s k u).comp
            (spectralPathOperator lam a.succ t k v) -
          (spectralPathOperator lam a.succ t k v).comp
            (spectralPathOperator lam a.succ s k u)) =
      (spectralPathOperator lam a.succ t k u).comp
          (spectralPathOperator lam a.succ s k v) -
        (spectralPathOperator lam a.succ t k v).comp
          (spectralPathOperator lam a.succ s k u) := by
  let g : ℝ := shiftedRowGap lam a.succ a.castSucc
  let x : ℝ := g + u
  let y : ℝ := g + v
  let w : ℝ := u + g + 1
  let z : ℝ := v + g + 1
  let A := spectralPathOperator lam a.castSucc a.castSucc k w
  let B := spectralPathOperator lam a.castSucc a.castSucc k z
  let C := spectralPathOperator lam a.castSucc s k w
  let D := spectralPathOperator lam a.castSucc s k z
  let E := spectralPathOperator lam a.castSucc t k w
  let F := spectralPathOperator lam a.castSucc t k z
  let S := polarization r n s a.castSucc
  let T := polarization r n t a.castSucc
  have has : a.castSucc < s := Fin.castSucc_lt_iff_succ_le.mpr hs
  have hat : a.castSucc < t := Fin.castSucc_lt_iff_succ_le.mpr ht
  have hdelta : x - y = w - z := by
    dsimp [x, y, w, z]
    ring
  have hdelta' : x - y = u - v := by
    dsimp [x, y]
    ring
  have hAB : A * B = B * A := hself w z
  have hSB : S * B - B * S = D :=
    polarization_comp_spectralPathOperator_self_sub
      lam a.castSucc s has k z
  have hTA : T * A - A * T = E :=
    polarization_comp_spectralPathOperator_self_sub
      lam a.castSucc t hat k w
  have hTB : T * B - B * T = F :=
    polarization_comp_spectralPathOperator_self_sub
      lam a.castSucc t hat k z
  have hSF : S * F = F * S :=
    polarization_comp_spectralPathOperator_later_target_commute
      lam a.castSucc s t has hat k z
  have hTC : T * C = C * T :=
    polarization_comp_spectralPathOperator_later_target_commute
      lam a.castSucc t s hat has k w
  have hTD : T * D = D * T :=
    polarization_comp_spectralPathOperator_later_target_commute
      lam a.castSucc t s hat has k z
  have hST : S * T = T * S := by
    apply LinearMap.ext
    intro p
    change polarization r n s a.castSucc
        (polarization r n t a.castSucc p) =
      polarization r n t a.castSucc
        (polarization r n s a.castSucc p)
    rw [polarization_polarization_commutator]
    simp only [polarization_apply, map_sum, Derivation.leibniz, smul_eq_mul, MvPolynomial.pderiv_X,
      ne_eq, DeterminantVectors.variableIndex_eq_iff, ne_of_lt has, false_and, not_false_eq_true,
      Pi.single_eq_of_ne', mul_zero, add_zero, ne_of_lt hat, ↓reduceIte, sub_zero]
  have hcross : (x - y) • (C * F - F * C) = E * D - F * C := by
    rw [hdelta]
    exact hrtt s t has.le hat.le w z
  have hCB : (x - y) • (C * B - B * C) = A * D - B * C := by
    rw [hdelta]
    exact hrtt s a.castSucc has.le le_rfl w z
  have hAF : (x - y) • (A * F - F * A) = E * B - F * A := by
    rw [hdelta]
    exact hrtt a.castSucc t le_rfl hat.le w z
  have hEB : (x - y) • (E * B - B * E) = A * F - B * E := by
    rw [hdelta]
    exact hrtt t a.castSucc hat.le le_rfl w z
  have hstep := spectralStep_rtt A B C D E F S T x y
    hAB hSB hTA hTB hSF hTC hTD hST hcross hCB hAF hEB
  rw [hdelta'] at hstep
  rw [spectralPathOperator_succ lam hdom a s k u,
    spectralPathOperator_succ lam hdom a t k v,
    spectralPathOperator_succ lam hdom a t k u,
    spectralPathOperator_succ lam hdom a s k v]
  change
    (u - v) •
        ((x • C - A.comp S).comp (y • F - B.comp T) -
          (y • F - B.comp T).comp (x • C - A.comp S)) =
      (x • E - A.comp T).comp (y • D - B.comp S) -
        (y • F - B.comp T).comp (x • C - A.comp S)
  exact hstep

end ArbitraryRowSameAxisDiamondSpectralRTTStep

end

section


open scoped BigOperators

namespace ArbitraryRowSameAxisDiamondSpectralAbstractSelfCommute

open MetricCodes.Spherical.HigherHarmonicYoung

theorem spectralStep_same_target_commute
    {r n : ℕ}
    (A B C D R : PolynomialSpace r n →ₗ[ℝ] PolynomialSpace r n)
    (x y : ℝ)
    (hAB : A * B = B * A)
    (hCD : C * D = D * C)
    (hRA : R * A - A * R = C)
    (hRB : R * B - B * R = D)
    (hRC : R * C = C * R)
    (hRD : R * D = D * R)
    (hcross : (x - y) • (C * B - B * C) = A * D - B * C) :
    (x • C - A * R) * (y • D - B * R) =
      (y • D - B * R) * (x • C - A * R) := by
  have hRA' : R * A = A * R + C := by
    rw [← hRA]
    noncomm_ring
  have hRB' : R * B = B * R + D := by
    rw [← hRB]
    noncomm_ring
  have hjacobi : C * B + A * D = D * A + B * C := by
    calc
      C * B + A * D =
          (R * A - A * R) * B + A * (R * B - B * R) := by
            rw [hRA, hRB]
      _ = R * (A * B) - (A * B) * R := by
            simp only [mul_sub, sub_mul, mul_assoc]
            module
      _ = R * (B * A) - (B * A) * R := by rw [hAB]
      _ = (R * B - B * R) * A + B * (R * A - A * R) := by
            simp only [mul_sub, sub_mul, mul_assoc]
            module
      _ = D * A + B * C := by rw [hRB, hRA]
  have hcbr :
      C * (B * R) - (B * R) * C = (C * B - B * C) * R := by
    calc
      C * (B * R) - (B * R) * C =
          (C * B) * R - B * (R * C) := by noncomm_ring
      _ = (C * B - B * C) * R := by
            rw [hRC]
            simp only [sub_mul, mul_assoc]
  have hard :
      (A * R) * D - D * (A * R) = (A * D - D * A) * R := by
    calc
      (A * R) * D - D * (A * R) =
          A * (R * D) - (D * A) * R := by noncomm_ring
      _ = (A * D - D * A) * R := by
            rw [hRD]
            simp only [sub_mul, mul_assoc]
  have hroots :
      (A * R) * (B * R) - (B * R) * (A * R) =
        (A * D - B * C) * R := by
    calc
      (A * R) * (B * R) - (B * R) * (A * R) =
          (A * (R * B)) * R - (B * (R * A)) * R := by
            noncomm_ring
      _ = (A * (B * R + D)) * R -
            (B * (A * R + C)) * R := by rw [hRB', hRA']
      _ = ((A * B - B * A) * R + (A * D - B * C)) * R := by
            simp only [sub_mul, mul_add, add_mul, mul_assoc]
            module
      _ = (A * D - B * C) * R := by rw [hAB]; simp only [sub_self, zero_mul, zero_add]
  apply sub_eq_zero.mp
  calc
    (x • C - A * R) * (y • D - B * R) -
        (y • D - B * R) * (x • C - A * R) =
      (x * y) • (C * D - D * C) -
        x • (C * (B * R) - (B * R) * C) -
        y • ((A * R) * D - D * (A * R)) +
        ((A * R) * (B * R) - (B * R) * (A * R)) := by
          simp only [mul_sub, sub_mul, Algebra.smul_mul_assoc,
            Algebra.mul_smul_comm, smul_smul, smul_sub]
          module
    _ = -(x • ((C * B - B * C) * R)) -
          y • ((A * D - D * A) * R) +
          (A * D - B * C) * R := by
            rw [hCD, sub_self, smul_zero, zero_sub,
              hcbr, hard, hroots]
    _ = (-((x - y) • (C * B - B * C)) +
          (A * D - B * C)) * R := by
            have hrel : A * D - D * A = -(C * B - B * C) := by
              calc
                A * D - D * A =
                    (C * B + A * D) - (D * A + B * C) -
                      (C * B - B * C) := by module
                _ = -(C * B - B * C) := by rw [hjacobi]; module
            rw [hrel]
            apply LinearMap.ext
            intro p
            simp only [LinearMap.add_apply, LinearMap.sub_apply,
              LinearMap.neg_apply, LinearMap.smul_apply,
              Module.End.mul_apply]
            module
    _ = 0 := by rw [hcross]; simp only [neg_sub, sub_add_sub_cancel, sub_self, zero_mul]

end ArbitraryRowSameAxisDiamondSpectralAbstractSelfCommute

end

section


open scoped BigOperators

namespace ArbitraryRowSameAxisDiamondSpectralSelfCommuteStep

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralPath
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralRootTransport
open
  MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralAbstractSelfCommute

theorem spectralPathOperator_succ_same_target_commute_of
    {r n : ℕ} (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam)
    (a : Fin r) (target : Fin (r + 1))
    (htarget : a.succ ≤ target)
    (k : Fin n) (u v : ℝ)
    (hcomm : ∀ (i : Fin (r + 1)), a.castSucc ≤ i → ∀ w z : ℝ,
      (spectralPathOperator lam a.castSucc i k w).comp
          (spectralPathOperator lam a.castSucc i k z) =
        (spectralPathOperator lam a.castSucc i k z).comp
          (spectralPathOperator lam a.castSucc i k w))
    (hrtt : ∀ (i j : Fin (r + 1)),
      a.castSucc ≤ i → a.castSucc ≤ j → ∀ w z : ℝ,
        (w - z) •
            ((spectralPathOperator lam a.castSucc i k w).comp
                (spectralPathOperator lam a.castSucc j k z) -
              (spectralPathOperator lam a.castSucc j k z).comp
                (spectralPathOperator lam a.castSucc i k w)) =
          (spectralPathOperator lam a.castSucc j k w).comp
              (spectralPathOperator lam a.castSucc i k z) -
            (spectralPathOperator lam a.castSucc j k z).comp
              (spectralPathOperator lam a.castSucc i k w)) :
    (spectralPathOperator lam a.succ target k u).comp
        (spectralPathOperator lam a.succ target k v) =
      (spectralPathOperator lam a.succ target k v).comp
        (spectralPathOperator lam a.succ target k u) := by
  let g : ℝ := shiftedRowGap lam a.succ a.castSucc
  let x : ℝ := g + u
  let y : ℝ := g + v
  let w : ℝ := u + g + 1
  let z : ℝ := v + g + 1
  let A := spectralPathOperator lam a.castSucc a.castSucc k w
  let B := spectralPathOperator lam a.castSucc a.castSucc k z
  let C := spectralPathOperator lam a.castSucc target k w
  let D := spectralPathOperator lam a.castSucc target k z
  let R := polarization r n target a.castSucc
  have hpos : a.castSucc < target :=
    Fin.castSucc_lt_iff_succ_le.mpr htarget
  have hdelta : x - y = w - z := by
    dsimp [x, y, w, z]
    ring
  have hAB : A * B = B * A := hcomm a.castSucc le_rfl w z
  have hCD : C * D = D * C := hcomm target hpos.le w z
  have hRA : R * A - A * R = C :=
    polarization_comp_spectralPathOperator_self_sub
      lam a.castSucc target hpos k w
  have hRB : R * B - B * R = D :=
    polarization_comp_spectralPathOperator_self_sub
      lam a.castSucc target hpos k z
  have hRC : R * C = C * R :=
    polarization_comp_spectralPathOperator_later_target_commute
      lam a.castSucc target target hpos hpos k w
  have hRD : R * D = D * R :=
    polarization_comp_spectralPathOperator_later_target_commute
      lam a.castSucc target target hpos hpos k z
  have hcross : (x - y) • (C * B - B * C) = A * D - B * C := by
    rw [hdelta]
    exact hrtt target a.castSucc hpos.le le_rfl w z
  have hstep := spectralStep_same_target_commute A B C D R x y
    hAB hCD hRA hRB hRC hRD hcross
  rw [spectralPathOperator_succ lam hdom a target k u,
    spectralPathOperator_succ lam hdom a target k v]
  change
    (x • C - A.comp R).comp (y • D - B.comp R) =
      (y • D - B.comp R).comp (x • C - A.comp R)
  exact hstep

end ArbitraryRowSameAxisDiamondSpectralSelfCommuteStep

namespace ArbitraryRowSameAxisDiamondSpectralRTT

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankLowerRowBranching
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralPath
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralRootTransport
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralAbstractRTT
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralRTTStep
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralSelfCommuteStep

theorem spectralPathOperator_zero_pivot_rtt
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (s t : Fin (r + 1)) (k : Fin n) (u v : ℝ) :
    (u - v) •
        ((spectralPathOperator lam 0 s k u).comp
            (spectralPathOperator lam 0 t k v) -
          (spectralPathOperator lam 0 t k v).comp
            (spectralPathOperator lam 0 s k u)) =
      (spectralPathOperator lam 0 t k u).comp
          (spectralPathOperator lam 0 s k v) -
        (spectralPathOperator lam 0 t k v).comp
          (spectralPathOperator lam 0 s k u) := by
  apply LinearMap.ext
  intro p
  simp only [spectralPathOperator_zero_pivot, LinearMap.smul_apply,
    LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply]
  rw [MvPolynomial.smul_eq_C_mul]
  ring

theorem spectralPathOperator_zero_pivot_same_target_commute
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (target : Fin (r + 1)) (k : Fin n) (u v : ℝ) :
    (spectralPathOperator lam 0 target k u).comp
        (spectralPathOperator lam 0 target k v) =
      (spectralPathOperator lam 0 target k v).comp
        (spectralPathOperator lam 0 target k u) := by
  simp only [spectralPathOperator_zero_pivot]

theorem spectralPathOperator_rtt_and_same_target_commute
    {r n : ℕ} (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam)
    (pivot : Fin (r + 1)) :
    (∀ (s t : Fin (r + 1)), pivot ≤ s → pivot ≤ t →
      ∀ (k : Fin n) (u v : ℝ),
        (u - v) •
            ((spectralPathOperator lam pivot s k u).comp
                (spectralPathOperator lam pivot t k v) -
              (spectralPathOperator lam pivot t k v).comp
                (spectralPathOperator lam pivot s k u)) =
          (spectralPathOperator lam pivot t k u).comp
              (spectralPathOperator lam pivot s k v) -
            (spectralPathOperator lam pivot t k v).comp
              (spectralPathOperator lam pivot s k u)) ∧
    (∀ (target : Fin (r + 1)), pivot ≤ target →
      ∀ (k : Fin n) (u v : ℝ),
        (spectralPathOperator lam pivot target k u).comp
            (spectralPathOperator lam pivot target k v) =
          (spectralPathOperator lam pivot target k v).comp
            (spectralPathOperator lam pivot target k u)) := by
  induction pivot using Fin.induction with
  | zero =>
      constructor
      · intro s t _ _ k u v
        exact spectralPathOperator_zero_pivot_rtt lam s t k u v
      · intro target _ k u v
        exact spectralPathOperator_zero_pivot_same_target_commute
          lam target k u v
  | succ a ih =>
      rcases ih with ⟨ihrtt, ihcomm⟩
      constructor
      · intro s t hs ht k u v
        exact spectralPathOperator_succ_rtt_of lam hdom a s t hs ht k u v
          (fun w z => ihcomm a.castSucc le_rfl k w z)
          (fun i j hi hj w z => ihrtt i j hi hj k w z)
      · intro target ht k u v
        exact spectralPathOperator_succ_same_target_commute_of
          lam hdom a target ht k u v
          (fun i hi w z => ihcomm i hi k w z)
          (fun i j hi hj w z => ihrtt i j hi hj k w z)

theorem spectralPathOperator_rtt
    {r n : ℕ} (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam)
    (pivot s t : Fin (r + 1))
    (hs : pivot ≤ s) (ht : pivot ≤ t)
    (k : Fin n) (u v : ℝ) :
    (u - v) •
        ((spectralPathOperator lam pivot s k u).comp
            (spectralPathOperator lam pivot t k v) -
          (spectralPathOperator lam pivot t k v).comp
            (spectralPathOperator lam pivot s k u)) =
      (spectralPathOperator lam pivot t k u).comp
          (spectralPathOperator lam pivot s k v) -
        (spectralPathOperator lam pivot t k v).comp
          (spectralPathOperator lam pivot s k u) :=
  (spectralPathOperator_rtt_and_same_target_commute
    (n := n) lam hdom pivot).1 s t hs ht k u v

theorem spectralPathOperator_same_target_commute
    {r n : ℕ} (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam)
    (pivot target : Fin (r + 1)) (htarget : pivot ≤ target)
    (k : Fin n) (u v : ℝ) :
    (spectralPathOperator lam pivot target k u).comp
        (spectralPathOperator lam pivot target k v) =
      (spectralPathOperator lam pivot target k v).comp
        (spectralPathOperator lam pivot target k u) :=
  (spectralPathOperator_rtt_and_same_target_commute
    (n := n) lam hdom pivot).2 target htarget k u v

end ArbitraryRowSameAxisDiamondSpectralRTT

end

section


open scoped BigOperators

namespace ArbitraryRowSameAxisDiamondSpectralSuffixClosure

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondFullCommutator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondPathCommutator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralPath
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralRTT
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSuffixCoefficientFactor
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSuffixSummation
open
  MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondUniversalPluckerCancellation

theorem spectralDiamondPrefixResidual_eq_zero_of_spectral_rtt
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (target pivot next : Fin (r + 1)) (hnext : pivot < next)
    (k : Fin n)
    (hself : ∀ u v : ℝ,
      (spectralPathOperator lam pivot pivot k u).comp
          (spectralPathOperator lam pivot pivot k v) =
        (spectralPathOperator lam pivot pivot k v).comp
          (spectralPathOperator lam pivot pivot k u))
    (hrtt : ∀ (s t : Fin (r + 1)),
      pivot ≤ s → pivot ≤ t → ∀ u v : ℝ,
        (u - v) •
            ((spectralPathOperator lam pivot s k u).comp
                (spectralPathOperator lam pivot t k v) -
              (spectralPathOperator lam pivot t k v).comp
                (spectralPathOperator lam pivot s k u)) =
          (spectralPathOperator lam pivot t k u).comp
              (spectralPathOperator lam pivot s k v) -
            (spectralPathOperator lam pivot t k v).comp
              (spectralPathOperator lam pivot s k u)) :
    spectralDiamondPrefixResidual lam target pivot next k = 0 := by
  let h : ℝ := shiftedRowGap lam target pivot
  have hcomm :
      (spectralPathOperator lam pivot pivot k (h + 1)).comp
          (arbitraryRowAxialRaise lam pivot k) =
        (arbitraryRowAxialRaise lam pivot k).comp
          (spectralPathOperator lam pivot pivot k (h + 1)) := by
    simpa only [spectralPathOperator_self_zero] using hself (h + 1) 0
  have hcross :
      (h + 1) •
          ((spectralPathOperator lam pivot next k (h + 1)).comp
              (arbitraryRowAxialRaise lam pivot k) -
            (arbitraryRowAxialRaise lam pivot k).comp
              (spectralPathOperator lam pivot next k (h + 1))) =
        (spectralPathOperator lam pivot pivot k (h + 1)).comp
            (spectralPathOperator lam pivot next k 0) -
          (arbitraryRowAxialRaise lam pivot k).comp
            (spectralPathOperator lam pivot next k (h + 1)) := by
    simpa only [sub_zero, spectralPathOperator_self_zero] using
      hrtt next pivot hnext.le le_rfl (h + 1) 0
  exact spectralPathPrefixResidual_eq_zero_of_rtt
    lam pivot next hnext k h hcomm hcross

theorem sum_weightedDiamondPairResidual_eq_zero_of_spectral_rtt
    {r n : ℕ} (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam)
    (target pivot : Fin (r + 1)) (hpivot : pivot < target)
    (k : Fin n)
    (hself : ∀ u v : ℝ,
      (spectralPathOperator lam pivot pivot k u).comp
          (spectralPathOperator lam pivot pivot k v) =
        (spectralPathOperator lam pivot pivot k v).comp
          (spectralPathOperator lam pivot pivot k u))
    (hrtt : ∀ (s t : Fin (r + 1)),
      pivot ≤ s → pivot ≤ t → ∀ u v : ℝ,
        (u - v) •
            ((spectralPathOperator lam pivot s k u).comp
                (spectralPathOperator lam pivot t k v) -
              (spectralPathOperator lam pivot t k v).comp
                (spectralPathOperator lam pivot s k u)) =
          (spectralPathOperator lam pivot t k u).comp
              (spectralPathOperator lam pivot s k v) -
            (spectralPathOperator lam pivot t k v).comp
              (spectralPathOperator lam pivot s k u)) :
    (∑ S ∈ ((precedingRows target).erase pivot).powerset,
      polarizationPathCoefficient lam target (insert pivot S) •
        diamondPairResidual lam target pivot k S) = 0 := by
  rw [sum_weightedDiamondPairResidual_eq_sum_spectralPrefix_suffix
    lam hdom target pivot hpivot k]
  simp only [neg_eq_zero]
  apply Finset.sum_eq_zero
  intro U hU
  rw [spectralDiamondPrefixResidual_eq_zero_of_spectral_rtt
    lam target pivot (diamondUpperSuffixNext target U)
      (pivot_lt_diamondUpperSuffixNext target pivot hpivot U
        (Finset.mem_powerset.mp hU)) k hself hrtt]
  simp only [LinearMap.zero_comp, smul_zero]

theorem sum_weightedDiamondPairResidual_eq_zero
    {r n : ℕ} (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam)
    (target pivot : Fin (r + 1)) (hpivot : pivot < target)
    (k : Fin n) :
    (∑ S ∈ ((precedingRows target).erase pivot).powerset,
      polarizationPathCoefficient lam target (insert pivot S) •
        diamondPairResidual lam target pivot k S) = 0 := by
  apply sum_weightedDiamondPairResidual_eq_zero_of_spectral_rtt
    lam hdom target pivot hpivot k
  · intro u v
    exact spectralPathOperator_same_target_commute
      lam hdom pivot pivot le_rfl k u v
  · intro s t hs ht u v
    exact spectralPathOperator_rtt lam hdom pivot s t hs ht k u v

theorem arbitraryRowAxialRaise_sameAxis_commutator
    {r n : ℕ} (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam)
    (pivot target : Fin (r + 1)) (hpivot : pivot < target)
    (k : Fin n) :
    (arbitraryRowAxialRaise lam target k).comp
          (arbitraryRowAxialRaise lam pivot k) -
        (arbitraryRowAxialRaise lam pivot k).comp
          (arbitraryRowAxialRaise lam target k) =
      (diamondOmittedRowOperator lam target pivot k).comp
        (arbitraryRowAxialRaise lam pivot k) := by
  exact (arbitraryRowAxialRaise_commutator_iff_sum_residual_eq_zero
    lam target pivot hpivot k).mpr
      (sum_weightedDiamondPairResidual_eq_zero
        lam hdom target pivot hpivot k)

theorem arbitraryRowAxialRaise_sameAxis_diamond
    {r n : ℕ} (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam)
    (i j : Fin (r + 1)) (hij : i < j)
    (k : Fin n) (p : PolynomialSpace r n) :
    arbitraryRowAxialRaise (raiseWeight lam i) j k
        (arbitraryRowAxialRaise lam i k p) =
      arbitraryRowAxialRaise (raiseWeight lam j) i k
        (arbitraryRowAxialRaise lam j k p) := by
  apply LinearMap.congr_fun
    ((arbitraryRowAxialRaise_sameAxis_diamond_iff_commutator
      lam i j hij (hdom hij.le) k).mpr ?_) p
  exact arbitraryRowAxialRaise_sameAxis_commutator
    lam hdom i j hij k

end ArbitraryRowSameAxisDiamondSpectralSuffixClosure

end

section


open scoped BigOperators InnerProductSpace

namespace AllRankCanonicalBoxActualForward

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalBoxProjectedAxisWitness
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinAdjacentFibrePhase
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinAdjacentProjectedCoefficient
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankGelfandTsetlinHarmonicIsometry
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankHarmonicBranch
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInternalRowLowerGram
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInterlacingAdjacentPathExchange
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankReverseInterlacingPolynomialSeed
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowAxialAdjointGram
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamond
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralSuffixClosure
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonGramIdeal
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonHighest
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherHarmonicYoung.FullRankClebschProbabilities
open MetricCodes.Spherical.HigherHarmonicYoung.GelfandTsetlin
open MetricCodes.Spherical.HigherHierarchy
open MetricCodes.Spherical.HigherHierarchyActualBoxSufficiency
open MetricCodes.Spherical.HigherProjectionInstantiation
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungActualGraphAssembly
open MetricCodes.Spherical.HigherYoungAllRankActualBoxInstantiation
open MetricCodes.Spherical.HigherYoungArbitraryRowLoweringProjectedAxisWitness
open MetricCodes.Spherical.HigherYoungMovingFibres
open MetricCodes.Spherical.HigherYoungArbitraryRankInterlacingGapSchedule
open MetricCodes.Spherical.HigherYoungArbitraryRankInterlacingLegalSchedule
open MetricCodes.Spherical.ThreeRowYoungBranching
open SpherePacking.HarmonicCoordinateOperators

theorem boxAxis_succ_val_eq_basisFun (n : ℕ) :
    (boxAxis (n + 1) (by omega)).val =
      EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n) := by
  simp only [boxAxis, EuclideanSpace.basisFun_apply]

theorem dominantSameAxisDiamond_allRows (r n : ℕ) :
    DominantSameAxisDiamond r n := by
  intro lam hdom i j hij k p
  exact arbitraryRowAxialRaise_sameAxis_diamond lam hdom i j hij k p

theorem projectedCoordinateRaise_canonicalGelfandTsetlinFibre_eq_of_adjacentSignature
    {r n : ℕ} (low high : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (row : Fin (r + 2))
    (hrow : high = raiseWeight low row)
    (hlow : Interlaces low mu) (hhigh : Interlaces high mu)
    (hdom : Antitone low)
    (hlowGram : PositiveGelfandTsetlinFischerGram (n := n) low mu hlow)
    (hhighGram : PositiveGelfandTsetlinFischerGram (n := n) high mu hhigh)
    (hexchange : ∀ p : HarmonicYoungSpace (n := n) mu,
      arbitraryRowAxialRaise low row (Fin.last n)
          (reverseInterlacingPolynomialSeed low mu p) -
        reverseInterlacingPolynomialSeed high mu p ∈
        youngGramRadialIdeal (r + 1) (n + 1))
    (p : HarmonicYoungSpace (n := n) mu) :
    projectedCoordinateRaise high low
        (by rw [hrow]; exact sum_raiseWeight low row) row
        (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n))
        (canonicalGelfandTsetlinFibre low mu hlow hlowGram p) =
      adjacentNormalizedAxisCoefficient
        (canonicalGelfandTsetlinFischerGram low mu hlow hlowGram)
        (canonicalGelfandTsetlinFischerGram high mu hhigh hhighGram)
        (arbitraryRowAxialLowerScalar low row)⁻¹ •
        canonicalGelfandTsetlinFibre high mu hhigh hhighGram p := by
  subst high
  exact projectedCoordinateRaise_canonicalGelfandTsetlinFibre_eq_of_pathExchange
    low mu row hlow hhigh hdom hlowGram hhighGram hexchange p

theorem canonicalAdjacentProjectedRaiseCoefficient_sq_of_adjacentSignature
    {r n : ℕ} (low high : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (row : Fin (r + 2))
    (hrow : high = raiseWeight low row)
    (hlow : Interlaces low mu) (hhigh : Interlaces high mu)
    (hlowGram : PositiveGelfandTsetlinFischerGram (n := n) low mu hlow)
    (hhighGram : PositiveGelfandTsetlinFischerGram (n := n) high mu hhigh)
    (hgram : canonicalGelfandTsetlinFischerGram high mu hhigh hhighGram =
      arbitraryRowAxialLowerScalar low row ^ 2 *
        internalRowLowerGramScalar high row *
        canonicalGelfandTsetlinFischerGram low mu hlow hlowGram *
        plusProbability (n + 1) low mu row) :
    adjacentNormalizedAxisCoefficient
        (canonicalGelfandTsetlinFischerGram low mu hlow hlowGram)
        (canonicalGelfandTsetlinFischerGram high mu hhigh hhighGram)
        (arbitraryRowAxialLowerScalar low row)⁻¹ ^ 2 =
      internalRowLowerGramScalar high row *
        plusProbability (n + 1) low mu row := by
  subst high
  exact canonicalAdjacentProjectedRaiseCoefficient_sq_of_fischerGram
    low mu row hlow hhigh hlowGram hhighGram hgram

/-- Data encoding the canonical box forward polynomial construction. -/
structure CanonicalBoxForwardPolynomialData {r m n : ℕ}
    (a : Fin (r + 2) → ℝ) (b : Fin (r + 1) → ℝ)
    (hstable : ∀ v : RectangularVertices.Vertex (r + 1) m,
      FiniteInterlacing (n + 1)
        (RectangularVertices.signature a (n + 1) v)
        (flooredCoordinates b (n + 1)))
    (hgram : ∀ i : BoxIndex (r + 1) m,
      PositiveGelfandTsetlinFischerGram (n := n)
        (boxSignature (m := m) a (n + 1) i)
        (Weyl.flooredWeight b (n + 1))
        (boxSignature_interlaces a b hstable i))
    (low high : BoxIndex (r + 1) m) (row : Fin (r + 2))
    (hrow : boxSignature (m := m) a (n + 1) high =
      raiseWeight (boxSignature (m := m) a (n + 1) low) row) where
  path_exchange : ∀ p : HarmonicYoungSpace
      (n := n) (Weyl.flooredWeight b (n + 1)),
    arbitraryRowAxialRaise (boxSignature (m := m) a (n + 1) low)
        row (Fin.last n)
        (reverseInterlacingPolynomialSeed
          (boxSignature (m := m) a (n + 1) low)
          (Weyl.flooredWeight b (n + 1)) p) -
      reverseInterlacingPolynomialSeed
        (boxSignature (m := m) a (n + 1) high)
        (Weyl.flooredWeight b (n + 1)) p ∈
      youngGramRadialIdeal (r + 1) (n + 1)
  fischer_recurrence :
    canonicalGelfandTsetlinFischerGram
      (boxSignature (m := m) a (n + 1) high)
      (Weyl.flooredWeight b (n + 1))
      (boxSignature_interlaces a b hstable high)
      (hgram high) =
    arbitraryRowAxialLowerScalar
        (boxSignature (m := m) a (n + 1) low) row ^ 2 *
      internalRowLowerGramScalar
        (boxSignature (m := m) a (n + 1) high) row *
      canonicalGelfandTsetlinFischerGram
        (boxSignature (m := m) a (n + 1) low)
        (Weyl.flooredWeight b (n + 1))
        (boxSignature_interlaces a b hstable low)
        (hgram low) *
      plusProbability (n + 1)
        (boxSignature (m := m) a (n + 1) low)
        (Weyl.flooredWeight b (n + 1)) row

/-- The canonical box adjacent fischer recurrence used in the spherical-code argument. -/
def CanonicalBoxAdjacentFischerRecurrence {r m n : ℕ}
    (a : Fin (r + 2) → ℝ) (b : Fin (r + 1) → ℝ)
    (hstable : ∀ v : RectangularVertices.Vertex (r + 1) m,
      FiniteInterlacing (n + 1)
        (RectangularVertices.signature a (n + 1) v)
        (flooredCoordinates b (n + 1)))
    (hgram : ∀ i : BoxIndex (r + 1) m,
      PositiveGelfandTsetlinFischerGram (n := n)
        (boxSignature (m := m) a (n + 1) i)
        (Weyl.flooredWeight b (n + 1))
        (boxSignature_interlaces a b hstable i))
    (low high : BoxIndex (r + 1) m) (row : Fin (r + 2)) : Prop :=
  canonicalGelfandTsetlinFischerGram
      (boxSignature (m := m) a (n + 1) high)
      (Weyl.flooredWeight b (n + 1))
      (boxSignature_interlaces a b hstable high)
      (hgram high) =
    arbitraryRowAxialLowerScalar
        (boxSignature (m := m) a (n + 1) low) row ^ 2 *
      internalRowLowerGramScalar
        (boxSignature (m := m) a (n + 1) high) row *
      canonicalGelfandTsetlinFischerGram
        (boxSignature (m := m) a (n + 1) low)
        (Weyl.flooredWeight b (n + 1))
        (boxSignature_interlaces a b hstable low)
        (hgram low) *
      plusProbability (n + 1)
        (boxSignature (m := m) a (n + 1) low)
        (Weyl.flooredWeight b (n + 1)) row

/-- The canonical box genuine forward axis data used in the spherical-code argument. -/
def canonicalBoxGenuineForwardAxisData {r m n : ℕ}
    (a : Fin (r + 2) → ℝ) (b : Fin (r + 1) → ℝ)
    (hstable : ∀ v : RectangularVertices.Vertex (r + 1) m,
      FiniteInterlacing (n + 1)
        (RectangularVertices.signature a (n + 1) v)
        (flooredCoordinates b (n + 1)))
    (hgram : ∀ i : BoxIndex (r + 1) m,
      PositiveGelfandTsetlinFischerGram (n := n)
        (boxSignature (m := m) a (n + 1) i)
        (Weyl.flooredWeight b (n + 1))
        (boxSignature_interlaces a b hstable i))
    (low high : BoxIndex (r + 1) m) (row : Fin (r + 2))
    (hrow : boxSignature (m := m) a (n + 1) high =
      raiseWeight (boxSignature (m := m) a (n + 1) low) row)
    (D : CanonicalBoxForwardPolynomialData
      a b hstable hgram low high row hrow) :
    GenuineLoweringFibreAxisData a b
      (boxAxis (n + 1) (by omega))
      (canonicalBoxGelfandTsetlinFibre a b hstable hgram)
      low high row
      (by rw [hrow]; exact sum_raiseWeight _ row) := by
  let lowSig := boxSignature (m := m) a (n + 1) low
  let highSig := boxSignature (m := m) a (n + 1) high
  let mu := Weyl.flooredWeight b (n + 1)
  have hlow : Interlaces lowSig mu :=
    boxSignature_interlaces a b hstable low
  have hhigh : Interlaces highSig mu :=
    boxSignature_interlaces a b hstable high
  have hlowGram : PositiveGelfandTsetlinFischerGram
      (n := n) lowSig mu hlow := hgram low
  have hhighGram : PositiveGelfandTsetlinFischerGram
      (n := n) highSig mu hhigh := hgram high
  let c := adjacentNormalizedAxisCoefficient
    (canonicalGelfandTsetlinFischerGram lowSig mu hlow hlowGram)
    (canonicalGelfandTsetlinFischerGram highSig mu hhigh hhighGram)
    (arbitraryRowAxialLowerScalar lowSig row)⁻¹
  refine ⟨c, ?_, ?_⟩
  · exact canonicalAdjacentProjectedRaiseCoefficient_sq_of_adjacentSignature
      lowSig highSig mu row hrow hlow hhigh hlowGram hhighGram
      D.fischer_recurrence
  · intro p
    have hdom : Antitone lowSig := hlow.antitone_ambient
    have hpath : ∀ q : HarmonicYoungSpace (n := n) mu,
        arbitraryRowAxialRaise lowSig row (Fin.last n)
            (reverseInterlacingPolynomialSeed lowSig mu q) -
          reverseInterlacingPolynomialSeed highSig mu q ∈
            youngGramRadialIdeal (r + 1) (n + 1) := by
      intro q
      exact D.path_exchange q
    have hforward :=
      projectedCoordinateRaise_canonicalGelfandTsetlinFibre_eq_of_adjacentSignature
        lowSig highSig mu row hrow hlow hhigh hdom
        hlowGram hhighGram hpath p
    change projectedCoordinateRaise highSig lowSig
        (by
          dsimp [highSig, lowSig]
          rw [hrow]
          exact sum_raiseWeight _ row) row
        (boxAxis (n + 1) (by omega)).val
        (canonicalGelfandTsetlinFibre lowSig mu hlow hlowGram p) =
      c • canonicalGelfandTsetlinFibre highSig mu
        (boxSignature_interlaces a b hstable high) (hgram high) p
    rw [boxAxis_succ_val_eq_basisFun]
    exact hforward

theorem canonicalBoxForwardPolynomialData_pathExchange_of_diamond
    {r m n : ℕ}
    (hdiamond : DominantSameAxisDiamond (r + 1) (n + 1))
    (a : Fin (r + 2) → ℝ) (b : Fin (r + 1) → ℝ)
    (hstable : ∀ v : RectangularVertices.Vertex (r + 1) m,
      FiniteInterlacing (n + 1)
        (RectangularVertices.signature a (n + 1) v)
        (flooredCoordinates b (n + 1)))
    (low high : BoxIndex (r + 1) m) (row : Fin (r + 2))
    (hrow : boxSignature (m := m) a (n + 1) high =
      raiseWeight (boxSignature (m := m) a (n + 1) low) row)
    (p : HarmonicYoungSpace (n := n)
      (Weyl.flooredWeight b (n + 1))) :
    arbitraryRowAxialRaise (boxSignature (m := m) a (n + 1) low)
        row (Fin.last n)
        (reverseInterlacingPolynomialSeed
          (boxSignature (m := m) a (n + 1) low)
          (Weyl.flooredWeight b (n + 1)) p) -
      reverseInterlacingPolynomialSeed
        (boxSignature (m := m) a (n + 1) high)
        (Weyl.flooredWeight b (n + 1)) p ∈
      youngGramRadialIdeal (r + 1) (n + 1) := by
  rw [hrow,
    reverseInterlacingPolynomialSeed_adjacent_raise_of_diamond
      hdiamond (boxSignature_interlaces a b hstable low) row p,
    sub_self]
  exact (youngGramRadialIdeal (r + 1) (n + 1)).zero_mem

theorem canonicalBoxForwardPolynomialData_pathExchange_allRows
    {r m n : ℕ}
    (a : Fin (r + 2) → ℝ) (b : Fin (r + 1) → ℝ)
    (hstable : ∀ v : RectangularVertices.Vertex (r + 1) m,
      FiniteInterlacing (n + 1)
        (RectangularVertices.signature a (n + 1) v)
        (flooredCoordinates b (n + 1)))
    (low high : BoxIndex (r + 1) m) (row : Fin (r + 2))
    (hrow : boxSignature (m := m) a (n + 1) high =
      raiseWeight (boxSignature (m := m) a (n + 1) low) row)
    (p : HarmonicYoungSpace (n := n)
      (Weyl.flooredWeight b (n + 1))) :
    arbitraryRowAxialRaise (boxSignature (m := m) a (n + 1) low)
        row (Fin.last n)
        (reverseInterlacingPolynomialSeed
          (boxSignature (m := m) a (n + 1) low)
          (Weyl.flooredWeight b (n + 1)) p) -
      reverseInterlacingPolynomialSeed
        (boxSignature (m := m) a (n + 1) high)
        (Weyl.flooredWeight b (n + 1)) p ∈
      youngGramRadialIdeal (r + 1) (n + 1) := by
  exact canonicalBoxForwardPolynomialData_pathExchange_of_diamond
    (dominantSameAxisDiamond_allRows (r + 1) (n + 1))
    a b hstable low high row hrow p

theorem canonicalBoxForwardPolynomialData_of_recurrence
    {r m n : ℕ}
    (a : Fin (r + 2) → ℝ) (b : Fin (r + 1) → ℝ)
    (hstable : ∀ v : RectangularVertices.Vertex (r + 1) m,
      FiniteInterlacing (n + 1)
        (RectangularVertices.signature a (n + 1) v)
        (flooredCoordinates b (n + 1)))
    (hgram : ∀ i : BoxIndex (r + 1) m,
      PositiveGelfandTsetlinFischerGram (n := n)
        (boxSignature (m := m) a (n + 1) i)
        (Weyl.flooredWeight b (n + 1))
        (boxSignature_interlaces a b hstable i))
    (low high : BoxIndex (r + 1) m) (row : Fin (r + 2))
    (hrow : boxSignature (m := m) a (n + 1) high =
      raiseWeight (boxSignature (m := m) a (n + 1) low) row)
    (hrecurrence : CanonicalBoxAdjacentFischerRecurrence
      a b hstable hgram low high row) :
    CanonicalBoxForwardPolynomialData
      a b hstable hgram low high row hrow where
  path_exchange p := canonicalBoxForwardPolynomialData_pathExchange_allRows
    a b hstable low high row hrow p
  fischer_recurrence := hrecurrence

end AllRankCanonicalBoxActualForward

end

section


open scoped BigOperators

namespace BideterminantHighestLine

open MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors
open MetricCodes.Spherical.TwoRowYoungBidegreeDecomposition

/-- The source matrix used in the spherical-code argument. -/
abbrev SourceMatrix (m : ℕ) := MvPolynomial (Fin m × Fin m) ℂ

/-- The source row root used in the spherical-code argument. -/
def sourceRowRoot {m : ℕ} (i j : Fin m) :
    Derivation ℂ (SourceMatrix m) (SourceMatrix m) :=
  ∑ k : Fin m,
    (MvPolynomial.X (i, k) : SourceMatrix m) •
      (MvPolynomial.pderiv (j, k) :
        Derivation ℂ (SourceMatrix m) (SourceMatrix m))

/-- The source column root used in the spherical-code argument. -/
def sourceColumnRoot {m : ℕ} (i j : Fin m) :
    Derivation ℂ (SourceMatrix m) (SourceMatrix m) :=
  ∑ k : Fin m,
    (MvPolynomial.X (k, i) : SourceMatrix m) •
      (MvPolynomial.pderiv (k, j) :
        Derivation ℂ (SourceMatrix m) (SourceMatrix m))

@[simp] theorem sourceRowRoot_apply {m : ℕ}
    (i j : Fin m) (p : SourceMatrix m) :
    sourceRowRoot i j p =
      ∑ k : Fin m,
        MvPolynomial.X (i, k) * MvPolynomial.pderiv (j, k) p := by
  change
    (Derivation.coeFnAddMonoidHom
      (∑ k : Fin m,
        (MvPolynomial.X (i, k) : SourceMatrix m) •
          (MvPolynomial.pderiv (j, k) :
            Derivation ℂ (SourceMatrix m) (SourceMatrix m)))) p = _
  rw [map_sum, Finset.sum_apply]
  rfl

@[simp] theorem sourceColumnRoot_apply {m : ℕ}
    (i j : Fin m) (p : SourceMatrix m) :
    sourceColumnRoot i j p =
      ∑ k : Fin m,
        MvPolynomial.X (k, i) * MvPolynomial.pderiv (k, j) p := by
  change
    (Derivation.coeFnAddMonoidHom
      (∑ k : Fin m,
        (MvPolynomial.X (k, i) : SourceMatrix m) •
          (MvPolynomial.pderiv (k, j) :
            Derivation ℂ (SourceMatrix m) (SourceMatrix m)))) p = _
  rw [map_sum, Finset.sum_apply]
  rfl

/-- The source row degree used in the spherical-code argument. -/
def sourceRowDegree {m : ℕ}
    (d : Fin m × Fin m →₀ ℕ) (i : Fin m) : ℕ :=
  ∑ j : Fin m, d (i, j)

/-- The source column degree used in the spherical-code argument. -/
def sourceColumnDegree {m : ℕ}
    (d : Fin m × Fin m →₀ ℕ) (j : Fin m) : ℕ :=
  ∑ i : Fin m, d (i, j)

theorem coeff_sourceRowRoot_self {m : ℕ}
    (p : SourceMatrix m) (i : Fin m)
    (d : Fin m × Fin m →₀ ℕ) :
    (sourceRowRoot i i p).coeff d =
      sourceRowDegree d i • p.coeff d := by
  rw [sourceRowRoot_apply, MvPolynomial.coeff_sum]
  simp_rw [coeff_X_mul_pderiv]
  rw [Finset.sum_nsmul_assoc]
  rfl

theorem coeff_sourceColumnRoot_self {m : ℕ}
    (p : SourceMatrix m) (i : Fin m)
    (d : Fin m × Fin m →₀ ℕ) :
    (sourceColumnRoot i i p).coeff d =
      sourceColumnDegree d i • p.coeff d := by
  rw [sourceColumnRoot_apply, MvPolynomial.coeff_sum]
  simp_rw [coeff_X_mul_pderiv]
  rw [Finset.sum_nsmul_assoc]
  rfl

theorem sourceRowDegree_eq_of_coeff_ne_zero {m : ℕ}
    (p : SourceMatrix m) (lam : Fin m → ℕ)
    (hp : ∀ i, sourceRowRoot i i p = (lam i : ℂ) • p)
    (d : Fin m × Fin m →₀ ℕ) (hd : p.coeff d ≠ 0)
    (i : Fin m) : sourceRowDegree d i = lam i := by
  have hcoeff := congrArg (MvPolynomial.coeff d) (hp i)
  rw [coeff_sourceRowRoot_self, MvPolynomial.coeff_smul] at hcoeff
  have hmul :
      (sourceRowDegree d i : ℂ) * p.coeff d =
        (lam i : ℂ) * p.coeff d := by
    simpa only [mul_eq_mul_right_iff, Nat.cast_inj, nsmul_eq_mul, smul_eq_mul] using hcoeff
  exact_mod_cast mul_right_cancel₀ hd hmul

theorem sourceColumnDegree_eq_of_coeff_ne_zero {m : ℕ}
    (p : SourceMatrix m) (lam : Fin m → ℕ)
    (hp : ∀ i, sourceColumnRoot i i p = (lam i : ℂ) • p)
    (d : Fin m × Fin m →₀ ℕ) (hd : p.coeff d ≠ 0)
    (i : Fin m) : sourceColumnDegree d i = lam i := by
  have hcoeff := congrArg (MvPolynomial.coeff d) (hp i)
  rw [coeff_sourceColumnRoot_self, MvPolynomial.coeff_smul] at hcoeff
  have hmul :
      (sourceColumnDegree d i : ℂ) * p.coeff d =
        (lam i : ℂ) * p.coeff d := by
    simpa only [mul_eq_mul_right_iff, Nat.cast_inj, nsmul_eq_mul, smul_eq_mul] using hcoeff
  exact_mod_cast mul_right_cancel₀ hd hmul

theorem coeff_X_mul_pderiv_ne {σ : Type*}
    (p : MvPolynomial σ ℂ) (a b : σ) (hab : a ≠ b)
    (d : σ →₀ ℕ) :
    (MvPolynomial.X a * MvPolynomial.pderiv b p).coeff d =
      if d a = 0 then 0 else
        (d b + 1 : ℕ) •
          p.coeff (d - Finsupp.single a 1 + Finsupp.single b 1) := by
  classical
  rw [MvPolynomial.coeff_X_mul']
  by_cases ha : d a = 0
  · have hna : a ∉ d.support :=
      Finsupp.notMem_support_iff.mpr ha
    simp only [hna, ↓reduceIte, ha]
  · have hma : a ∈ d.support :=
      Finsupp.mem_support_iff.mpr ha
    rw [ite_eq_left hma, MvPolynomial.coeff_pderiv, ite_eq_right ha]
    have hneq : a ≠ b := hab
    have hsub :
        (d - (Finsupp.single a 1 : σ →₀ ℕ)) b = d b := by
      simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_of_ne hab.symm, tsub_zero]
    rw [hsub]
    simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one, mul_comm]

theorem sourceRowRoot_X {m : ℕ}
    (i j a b : Fin m) :
    sourceRowRoot i j (MvPolynomial.X (a, b) : SourceMatrix m) =
      if j = a then MvPolynomial.X (i, b) else 0 := by
  classical
  rw [sourceRowRoot_apply]
  by_cases h : j = a
  · subst a
    simp only [MvPolynomial.pderiv_X, Pi.single_apply, Prod.mk.injEq, true_and, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  · simp only [MvPolynomial.pderiv_X, ne_eq, Prod.mk.injEq, Ne.symm h, false_and, not_false_eq_true,
      Pi.single_eq_of_ne, mul_zero, Finset.sum_const_zero, h, ↓reduceIte]

theorem sourceColumnRoot_X {m : ℕ}
    (i j a b : Fin m) :
    sourceColumnRoot i j (MvPolynomial.X (a, b) : SourceMatrix m) =
      if j = b then MvPolynomial.X (a, i) else 0 := by
  classical
  rw [sourceColumnRoot_apply]
  by_cases h : j = b
  · subst b
    simp only [MvPolynomial.pderiv_X, Pi.single_apply, Prod.mk.injEq, and_true, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  · simp only [MvPolynomial.pderiv_X, ne_eq, Prod.mk.injEq, Ne.symm h, and_false, not_false_eq_true,
      Pi.single_eq_of_ne, mul_zero, Finset.sum_const_zero, h, ↓reduceIte]

theorem sourceRowRoot_sourceLeadingMinor_self {r : ℕ}
    (i k : Fin (r + 1)) :
    sourceRowRoot i i (sourceLeadingMinor k) =
      if i ≤ k then sourceLeadingMinor k else 0 := by
  classical
  unfold sourceLeadingMinor
  by_cases hi : i.val ≤ k.val
  · let ii : Fin (k.val + 1) := ⟨i.val, by omega⟩
    have hii : minorIndex k ii = i := Fin.ext rfl
    rw [ite_eq_left (show i ≤ k from hi), derivation_det_singleRow
      (sourceRowRoot i i)
      (Matrix.of fun a b : Fin (k.val + 1) =>
        MvPolynomial.X (minorIndex k a, minorIndex k b)) ii]
    · have hrow :
          (fun b : Fin (k.val + 1) =>
            sourceRowRoot i i
              (MvPolynomial.X (minorIndex k ii, minorIndex k b))) =
          (fun b : Fin (k.val + 1) =>
            MvPolynomial.X (minorIndex k ii, minorIndex k b)) := by
        funext b
        rw [sourceRowRoot_X, hii, ite_eq_left rfl]
      simp only [Matrix.of_apply]
      rw [hrow]
      have hrowMatrix :
          (fun b : Fin (k.val + 1) =>
            MvPolynomial.X (minorIndex k ii, minorIndex k b)) =
          (fun b => (Matrix.of fun a b : Fin (k.val + 1) =>
            (MvPolynomial.X (minorIndex k a, minorIndex k b) :
              SourceMatrix (r + 1))) ii b) := by
        funext b
        simp only [Matrix.of_apply]
      rw [hrowMatrix, Matrix.updateRow_eq_self]
    · intro a b hab
      simp only [Matrix.of_apply]
      rw [sourceRowRoot_X]
      have hne : i ≠ minorIndex k a := by
        intro heq
        apply hab
        apply Fin.ext
        have hv := congrArg Fin.val heq
        change i.val = a.val at hv
        exact hv.symm
      simp only [hne, ↓reduceIte]
  · rw [ite_eq_right (show ¬ i ≤ k from hi)]
    apply derivation_det_eq_zero
    intro a b
    simp only [Matrix.of_apply]
    rw [sourceRowRoot_X]
    have hne : i ≠ minorIndex k a := by
      intro heq
      have hv := congrArg Fin.val heq
      change i.val = a.val at hv
      have ha := a.isLt
      omega
    simp only [hne, ↓reduceIte]

theorem sourceColumnRoot_sourceLeadingMinor_self {r : ℕ}
    (i k : Fin (r + 1)) :
    sourceColumnRoot i i (sourceLeadingMinor k) =
      if i ≤ k then sourceLeadingMinor k else 0 := by
  classical
  unfold sourceLeadingMinor
  by_cases hi : i.val ≤ k.val
  · let ii : Fin (k.val + 1) := ⟨i.val, by omega⟩
    have hii : minorIndex k ii = i := Fin.ext rfl
    rw [ite_eq_left (show i ≤ k from hi), derivation_det_singleColumn
      (sourceColumnRoot i i)
      (Matrix.of fun a b : Fin (k.val + 1) =>
        MvPolynomial.X (minorIndex k a, minorIndex k b)) ii]
    · have hcol :
          (fun a : Fin (k.val + 1) =>
            sourceColumnRoot i i
              (MvPolynomial.X (minorIndex k a, minorIndex k ii))) =
          (fun a : Fin (k.val + 1) =>
            MvPolynomial.X (minorIndex k a, minorIndex k ii)) := by
        funext a
        rw [sourceColumnRoot_X, hii, ite_eq_left rfl]
      simp only [Matrix.of_apply]
      rw [hcol]
      have hcolMatrix :
          (fun a : Fin (k.val + 1) =>
            MvPolynomial.X (minorIndex k a, minorIndex k ii)) =
          (fun a => (Matrix.of fun a b : Fin (k.val + 1) =>
            (MvPolynomial.X (minorIndex k a, minorIndex k b) :
              SourceMatrix (r + 1))) a ii) := by
        funext a
        simp only [Matrix.of_apply]
      rw [hcolMatrix, Matrix.updateCol_eq_self]
    · intro a b hab
      simp only [Matrix.of_apply]
      rw [sourceColumnRoot_X]
      have hne : i ≠ minorIndex k b := by
        intro heq
        apply hab
        apply Fin.ext
        have hv := congrArg Fin.val heq
        change i.val = b.val at hv
        exact hv.symm
      simp only [hne, ↓reduceIte]
  · rw [ite_eq_right (show ¬ i ≤ k from hi)]
    apply derivation_det_eq_zero
    intro a b
    simp only [Matrix.of_apply]
    rw [sourceColumnRoot_X]
    have hne : i ≠ minorIndex k b := by
      intro heq
      have hv := congrArg Fin.val heq
      change i.val = b.val at hv
      have hb := b.isLt
      omega
    simp only [hne, ↓reduceIte]

theorem sourceRowRoot_sourceLeadingMinor_upper {r : ℕ}
    (i j : Fin (r + 1)) (hij : i < j) (k : Fin (r + 1)) :
    sourceRowRoot i j (sourceLeadingMinor k) = 0 := by
  classical
  unfold sourceLeadingMinor
  by_cases hj : j.val ≤ k.val
  · let jj : Fin (k.val + 1) := ⟨j.val, by omega⟩
    let ii : Fin (k.val + 1) := ⟨i.val, by
      have hijv : i.val < j.val := hij
      omega⟩
    have hjj : minorIndex k jj = j := Fin.ext rfl
    have hii : minorIndex k ii = i := Fin.ext rfl
    rw [derivation_det_singleRow (sourceRowRoot i j)
      (Matrix.of fun a b : Fin (k.val + 1) =>
        MvPolynomial.X (minorIndex k a, minorIndex k b)) jj]
    · have hrow :
          (fun b : Fin (k.val + 1) =>
            sourceRowRoot i j
              (MvPolynomial.X (minorIndex k jj, minorIndex k b))) =
          (fun b : Fin (k.val + 1) =>
            MvPolynomial.X (minorIndex k ii, minorIndex k b)) := by
        funext b
        rw [sourceRowRoot_X, hjj, hii, ite_eq_left rfl]
      simp only [Matrix.of_apply]
      rw [hrow]
      have hrowMatrix :
          (fun b : Fin (k.val + 1) =>
            MvPolynomial.X (minorIndex k ii, minorIndex k b)) =
          (fun b => (Matrix.of fun a b : Fin (k.val + 1) =>
            (MvPolynomial.X (minorIndex k a, minorIndex k b) :
              SourceMatrix (r + 1))) ii b) := by
        funext b
        simp only [Matrix.of_apply]
      rw [hrowMatrix]
      apply Matrix.det_updateRow_eq_zero
      intro heq
      have hv := congrArg Fin.val heq
      have hijv : i.val < j.val := hij
      change i.val = j.val at hv
      omega
    · intro a b hab
      simp only [Matrix.of_apply]
      rw [sourceRowRoot_X]
      have hne : j ≠ minorIndex k a := by
        intro heq
        apply hab
        apply Fin.ext
        have hv := congrArg Fin.val heq
        change j.val = a.val at hv
        exact hv.symm
      simp only [hne, ↓reduceIte]
  · apply derivation_det_eq_zero
    intro a b
    simp only [Matrix.of_apply]
    rw [sourceRowRoot_X]
    have hne : j ≠ minorIndex k a := by
      intro heq
      have hv := congrArg Fin.val heq
      change j.val = a.val at hv
      have ha := a.isLt
      omega
    simp only [hne, ↓reduceIte]

theorem sourceRowRoot_sourceHighestWeightPolynomial_self {r : ℕ}
    (e : Fin (r + 1) → ℕ) (i : Fin (r + 1)) :
    sourceRowRoot i i (sourceHighestWeightPolynomial e) =
      (determinantWeight e i : ℂ) • sourceHighestWeightPolynomial e := by
  classical
  unfold sourceHighestWeightPolynomial determinantWeight
  rw [Nat.cast_sum]
  apply derivation_prod_eigen (sourceRowRoot i i) Finset.univ
    (fun k : Fin (r + 1) => sourceLeadingMinor k ^ e k)
    (fun k => if i ≤ k then e k else 0)
  intro k _
  rw [(sourceRowRoot i i).leibniz_pow,
    sourceRowRoot_sourceLeadingMinor_self]
  by_cases hik : i ≤ k
  · simp only [hik, ite_true]
    cases e k with
    | zero => simp only [zero_tsub, pow_zero, smul_eq_mul, one_mul, CharP.cast_eq_zero,
                zero_smul]
    | succ m =>
        simp only [add_tsub_cancel_right, smul_eq_mul, Algebra.smul_def, eq_natCast, Nat.cast_add,
          Nat.cast_one, pow_succ, MvPolynomial.algebraMap_eq, MvPolynomial.C_add, map_natCast,
          MvPolynomial.C_1]
  · simp only [hik, ↓reduceIte, smul_eq_mul, mul_zero, nsmul_zero, CharP.cast_eq_zero, zero_smul]

theorem sourceColumnRoot_sourceHighestWeightPolynomial_self {r : ℕ}
    (e : Fin (r + 1) → ℕ) (i : Fin (r + 1)) :
    sourceColumnRoot i i (sourceHighestWeightPolynomial e) =
      (determinantWeight e i : ℂ) • sourceHighestWeightPolynomial e := by
  classical
  unfold sourceHighestWeightPolynomial determinantWeight
  rw [Nat.cast_sum]
  apply derivation_prod_eigen (sourceColumnRoot i i) Finset.univ
    (fun k : Fin (r + 1) => sourceLeadingMinor k ^ e k)
    (fun k => if i ≤ k then e k else 0)
  intro k _
  rw [(sourceColumnRoot i i).leibniz_pow,
    sourceColumnRoot_sourceLeadingMinor_self]
  by_cases hik : i ≤ k
  · simp only [hik, ite_true]
    cases e k with
    | zero => simp only [zero_tsub, pow_zero, smul_eq_mul, one_mul, CharP.cast_eq_zero,
                zero_smul]
    | succ m =>
        simp only [add_tsub_cancel_right, smul_eq_mul, Algebra.smul_def, eq_natCast, Nat.cast_add,
          Nat.cast_one, pow_succ, MvPolynomial.algebraMap_eq, MvPolynomial.C_add, map_natCast,
          MvPolynomial.C_1]
  · simp only [hik, ↓reduceIte, smul_eq_mul, mul_zero, nsmul_zero, CharP.cast_eq_zero, zero_smul]

theorem sourceRowRoot_sourceHighestWeightPolynomial_upper {r : ℕ}
    (e : Fin (r + 1) → ℕ) (i j : Fin (r + 1)) (hij : i < j) :
    sourceRowRoot i j (sourceHighestWeightPolynomial e) = 0 := by
  classical
  unfold sourceHighestWeightPolynomial
  apply derivation_prod_eq_zero
  intro k _
  rw [(sourceRowRoot i j).leibniz_pow,
    sourceRowRoot_sourceLeadingMinor_upper i j hij k]
  simp only [smul_eq_mul, mul_zero, nsmul_zero]

private def sourceDiagonalEvaluation {m : ℕ} : Fin m × Fin m → ℂ :=
  fun z => if z.1 = z.2 then 1 else 0

theorem eval_sourceLeadingMinor {r : ℕ} (k : Fin (r + 1)) :
    MvPolynomial.eval sourceDiagonalEvaluation
      (sourceLeadingMinor k) = 1 := by
  unfold sourceLeadingMinor
  rw [(MvPolynomial.eval sourceDiagonalEvaluation).map_det]
  have hmatrix :
      (fun i j : Fin (k.val + 1) =>
        MvPolynomial.eval sourceDiagonalEvaluation
          (MvPolynomial.X (minorIndex k i, minorIndex k j))) =
      (1 : Matrix (Fin (k.val + 1)) (Fin (k.val + 1)) ℂ) := by
    ext i j
    simp only [minorIndex, MvPolynomial.eval_X, sourceDiagonalEvaluation, Fin.ext_iff,
      Matrix.one_apply]
  change
    Matrix.det (fun i j : Fin (k.val + 1) =>
      MvPolynomial.eval sourceDiagonalEvaluation
        (MvPolynomial.X (minorIndex k i, minorIndex k j))) = 1
  rw [hmatrix, Matrix.det_one]

theorem eval_sourceHighestWeightPolynomial {r : ℕ}
    (e : Fin (r + 1) → ℕ) :
    MvPolynomial.eval sourceDiagonalEvaluation
      (sourceHighestWeightPolynomial e) = 1 := by
  simp only [sourceHighestWeightPolynomial, map_prod, map_pow, eval_sourceLeadingMinor, one_pow,
    Finset.prod_const_one]

end BideterminantHighestLine

end

end HigherHarmonicYoung

section


open scoped BigOperators InnerProductSpace

namespace HigherYoungTwoRowLieIrreducibility

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherYoungMixedGapLieGram

/-- The polynomial complexification used in the spherical-code argument. -/
def polynomialComplexification {r n : ℕ} :
    PolynomialSpace r n →ₗ[ℝ]
      MvPolynomial (Fin ((r + 1) * n)) ℂ where
  toFun := MvPolynomial.map Complex.ofRealHom
  map_add' p q := map_add (MvPolynomial.map Complex.ofRealHom) p q
  map_smul' c p := by
    apply MvPolynomial.ext
    intro d
    simp only [MvPolynomial.coeff_map, MvPolynomial.coeff_smul, smul_eq_mul,
      Complex.ofRealHom_eq_coe, Complex.ofReal_mul, Real.ringHom_apply, Complex.real_smul]

@[simp] theorem polynomialComplexification_apply
    {r n : ℕ} (p : PolynomialSpace r n) :
    polynomialComplexification p =
      MvPolynomial.map Complex.ofRealHom p := rfl

theorem polynomialRealPart_complexification
    {r n : ℕ} (p : PolynomialSpace r n) :
    polynomialRealPart (polynomialComplexification p) = p := by
  apply MvPolynomial.ext
  intro d
  simp only [polynomialComplexification_apply, coeff_polynomialRealPart, MvPolynomial.coeff_map,
    Complex.ofRealHom_eq_coe, Complex.ofReal_re]

theorem polynomialImaginaryPart_complexification
    {r n : ℕ} (p : PolynomialSpace r n) :
    polynomialImaginaryPart (polynomialComplexification p) = 0 := by
  apply MvPolynomial.ext
  intro d
  simp only [polynomialComplexification_apply, coeff_polynomialImaginaryPart,
    MvPolynomial.coeff_map, Complex.ofRealHom_eq_coe, Complex.ofReal_im, MvPolynomial.coeff_zero]

theorem polynomialRealPart_complex_smul {r n : ℕ} (c : ℂ)
    (p : MvPolynomial (Fin ((r + 1) * n)) ℂ) :
    polynomialRealPart (c • p) =
      c.re • polynomialRealPart p -
        c.im • polynomialImaginaryPart p := by
  apply MvPolynomial.ext
  intro d
  simp only [coeff_polynomialRealPart, MvPolynomial.coeff_smul, smul_eq_mul, Complex.mul_re,
    MvPolynomial.coeff_sub, coeff_polynomialImaginaryPart]

theorem polynomialImaginaryPart_complex_smul {r n : ℕ} (c : ℂ)
    (p : MvPolynomial (Fin ((r + 1) * n)) ℂ) :
    polynomialImaginaryPart (c • p) =
      c.re • polynomialImaginaryPart p +
        c.im • polynomialRealPart p := by
  apply MvPolynomial.ext
  intro d
  simp only [coeff_polynomialImaginaryPart, MvPolynomial.coeff_smul, smul_eq_mul, Complex.mul_im,
    MvPolynomial.coeff_add, coeff_polynomialRealPart]

/-- The polynomial complex span used in the spherical-code argument. -/
def polynomialComplexSpan {r n : ℕ}
    (W : Submodule ℝ (PolynomialSpace r n)) :
    Submodule ℂ (MvPolynomial (Fin ((r + 1) * n)) ℂ) :=
  Submodule.span ℂ (polynomialComplexification '' (W : Set (PolynomialSpace r n)))

theorem realPart_imaginaryPart_mem_of_mem_polynomialComplexSpan
    {r n : ℕ} (W : Submodule ℝ (PolynomialSpace r n))
    (z : MvPolynomial (Fin ((r + 1) * n)) ℂ)
    (hz : z ∈ polynomialComplexSpan W) :
    polynomialRealPart z ∈ W ∧ polynomialImaginaryPart z ∈ W := by
  change z ∈ Submodule.span ℂ
    (polynomialComplexification '' (W : Set (PolynomialSpace r n))) at hz
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hz
  · intro z hz
    obtain ⟨p, hp, rfl⟩ := hz
    have hreal : polynomialRealPart
        (MvPolynomial.map Complex.ofRealHom p) = p := by
      simpa only [polynomialComplexification_apply] using
        polynomialRealPart_complexification p
    have himag : polynomialImaginaryPart
        (MvPolynomial.map Complex.ofRealHom p) = 0 := by
      simpa only [polynomialComplexification_apply] using
        polynomialImaginaryPart_complexification p
    exact ⟨hreal.symm ▸ hp, himag.symm ▸ W.zero_mem⟩
  · simp only [map_zero, zero_mem, and_self]
  · intro z w _ _ ihz ihw
    rw [map_add, map_add]
    exact ⟨W.add_mem ihz.1 ihw.1,
      W.add_mem ihz.2 ihw.2⟩
  · intro c z _ ih
    rw [polynomialRealPart_complex_smul,
      polynomialImaginaryPart_complex_smul]
    exact ⟨W.sub_mem (W.smul_mem c.re ih.1)
      (W.smul_mem c.im ih.2),
      W.add_mem (W.smul_mem c.re ih.2)
        (W.smul_mem c.im ih.1)⟩

theorem polynomialComplexSpan_inf_eq_bot_of_inf_eq_bot
    {r n : ℕ}
    (W U : Submodule ℝ (PolynomialSpace r n))
    (hdisjoint : W ⊓ U = ⊥) :
    polynomialComplexSpan W ⊓ polynomialComplexSpan U = ⊥ := by
  apply bot_unique
  intro z hz
  obtain ⟨hzW, hzU⟩ := Submodule.mem_inf.mp hz
  have hW := realPart_imaginaryPart_mem_of_mem_polynomialComplexSpan W z hzW
  have hU := realPart_imaginaryPart_mem_of_mem_polynomialComplexSpan U z hzU
  have hreal : polynomialRealPart z = 0 := by
    have hmem : polynomialRealPart z ∈ W ⊓ U :=
      Submodule.mem_inf.mpr ⟨hW.1, hU.1⟩
    rw [hdisjoint] at hmem
    simpa only [Submodule.mem_bot] using hmem
  have himag : polynomialImaginaryPart z = 0 := by
    have hmem : polynomialImaginaryPart z ∈ W ⊓ U :=
      Submodule.mem_inf.mpr ⟨hW.2, hU.2⟩
    rw [hdisjoint] at hmem
    simpa only [Submodule.mem_bot] using hmem
  have hz0 : z = 0 := by
    apply MvPolynomial.ext
    intro d
    apply Complex.ext
    · simpa only [MvPolynomial.coeff_zero, Complex.zero_re, coeff_polynomialRealPart] using
        congrArg (fun p : PolynomialSpace r n => p.coeff d) hreal
    · simpa only [MvPolynomial.coeff_zero, Complex.zero_im, coeff_polynomialImaginaryPart] using
        congrArg (fun p : PolynomialSpace r n => p.coeff d) himag
  simp only [hz0, zero_mem]

theorem polynomialComplexSpan_ne_bot_of_ne_bot
    {r n : ℕ} (W : Submodule ℝ (PolynomialSpace r n))
    (hW : W ≠ ⊥) :
    polynomialComplexSpan W ≠ ⊥ := by
  obtain ⟨p, hp, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  intro hbot
  have hmem : polynomialComplexification p ∈ polynomialComplexSpan W :=
    Submodule.subset_span ⟨p, hp, rfl⟩
  rw [hbot] at hmem
  have hzero : polynomialComplexification p = 0 := by
    simpa only [polynomialComplexification_apply, Submodule.mem_bot] using hmem
  apply hp0
  calc
    p = polynomialRealPart (polynomialComplexification p) :=
      (polynomialRealPart_complexification p).symm
    _ = polynomialRealPart 0 := congrArg polynomialRealPart hzero
    _ = 0 := map_zero polynomialRealPart

theorem complexSpan_invariant
    {V Z I : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup Z] [Module ℂ Z] [Module ℝ Z]
    (e : V →ₗ[ℝ] Z)
    (R : I → V →ₗ[ℝ] V)
    (RC : I → Z →ₗ[ℂ] Z)
    (hcomm : ∀ (i : I) (v : V), RC i (e v) = e (R i v))
    (W : Submodule ℝ V)
    (hW : ∀ (i : I) (v : V), v ∈ W → R i v ∈ W)
    (i : I) (z : Z)
    (hz : z ∈ Submodule.span ℂ (e '' (W : Set V))) :
    RC i z ∈ Submodule.span ℂ (e '' (W : Set V)) := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hz
  · intro z hz
    rcases hz with ⟨v, hv, rfl⟩
    rw [hcomm]
    exact Submodule.subset_span ⟨R i v, hW i v hv, rfl⟩
  · simp only [map_zero, zero_mem]
  · intro z w _ _ ihz ihw
    rw [map_add]
    exact (Submodule.span ℂ (e '' (W : Set V))).add_mem ihz ihw
  · intro c z _ ih
    rw [map_smul]
    exact (Submodule.span ℂ (e '' (W : Set V))).smul_mem c ih

/-- The complex ambient coordinate derivation used in the spherical-code argument. -/
def complexAmbientCoordinateDerivation {r n : ℕ} (a b : Fin n) :
    Derivation ℂ (MvPolynomial (Fin ((r + 1) * n)) ℂ)
      (MvPolynomial (Fin ((r + 1) * n)) ℂ) :=
  ∑ i : Fin (r + 1),
    (MvPolynomial.X (variableIndex i a) :
      MvPolynomial (Fin ((r + 1) * n)) ℂ) •
      (MvPolynomial.pderiv (variableIndex i b) :
        Derivation ℂ (MvPolynomial (Fin ((r + 1) * n)) ℂ)
          (MvPolynomial (Fin ((r + 1) * n)) ℂ))

@[simp] theorem complexAmbientCoordinateDerivation_apply
    {r n : ℕ} (a b : Fin n)
    (p : MvPolynomial (Fin ((r + 1) * n)) ℂ) :
    complexAmbientCoordinateDerivation (r := r) a b p =
      ∑ i : Fin (r + 1),
        MvPolynomial.X (variableIndex i a) *
          MvPolynomial.pderiv (variableIndex i b) p := by
  change
    (Derivation.coeFnAddMonoidHom
      (∑ i : Fin (r + 1),
        (MvPolynomial.X (variableIndex i a) :
          MvPolynomial (Fin ((r + 1) * n)) ℂ) •
          (MvPolynomial.pderiv (variableIndex i b) :
            Derivation ℂ (MvPolynomial (Fin ((r + 1) * n)) ℂ)
              (MvPolynomial (Fin ((r + 1) * n)) ℂ)))) p = _
  rw [map_sum, Finset.sum_apply]
  rfl

theorem complexAmbientCoordinateDerivation_complexification
    {r n : ℕ} (a b : Fin n) (p : PolynomialSpace r n) :
    complexAmbientCoordinateDerivation (r := r) a b
        (polynomialComplexification p) =
      polynomialComplexification (ambientCoordinateDerivation a b p) := by
  rw [complexAmbientCoordinateDerivation_apply,
    ambientCoordinateDerivation_apply]
  change
    (∑ i : Fin (r + 1),
      MvPolynomial.X (variableIndex i a) *
        MvPolynomial.pderiv (variableIndex i b)
          (MvPolynomial.map Complex.ofRealHom p)) =
      MvPolynomial.map Complex.ofRealHom
        (∑ i : Fin (r + 1), MvPolynomial.X (variableIndex i a) *
          MvPolynomial.pderiv (variableIndex i b) p)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul, MvPolynomial.map_X, MvPolynomial.pderiv_map]

/-- The complex ambient rotation used in the spherical-code argument. -/
def complexAmbientRotation {r n : ℕ} (a b : Fin n) :
    Derivation ℂ (MvPolynomial (Fin ((r + 1) * n)) ℂ)
      (MvPolynomial (Fin ((r + 1) * n)) ℂ) :=
  complexAmbientCoordinateDerivation (r := r) a b -
    complexAmbientCoordinateDerivation (r := r) b a

theorem complexAmbientRotation_complexification
    {r n : ℕ} (a b : Fin n) (p : PolynomialSpace r n) :
    complexAmbientRotation (r := r) a b
        (polynomialComplexification p) =
      polynomialComplexification (ambientRotation a b p) := by
  change
    complexAmbientCoordinateDerivation (r := r) a b
          (polynomialComplexification p) -
        complexAmbientCoordinateDerivation (r := r) b a
          (polynomialComplexification p) =
      polynomialComplexification
        (ambientCoordinateDerivation a b p -
          ambientCoordinateDerivation b a p)
  rw [complexAmbientCoordinateDerivation_complexification,
    complexAmbientCoordinateDerivation_complexification, map_sub]

/-- The young real polynomial image used in the spherical-code argument. -/
def youngRealPolynomialImage {r n : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (W : Submodule ℝ (HarmonicYoungSpace (n := n) lam)) :
    Submodule ℝ (PolynomialSpace r n) :=
  Submodule.map (harmonicYoungSubmodule lam).subtype W

theorem youngRealPolynomialImage_le {r n : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (W : Submodule ℝ (HarmonicYoungSpace (n := n) lam)) :
    youngRealPolynomialImage lam W ≤ harmonicYoungSubmodule lam := by
  rintro _ ⟨p, _, rfl⟩
  exact p.property

theorem youngRealPolynomialImage_ne_bot_of_ne_bot {r n : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (W : Submodule ℝ (HarmonicYoungSpace (n := n) lam))
    (hW : W ≠ ⊥) : youngRealPolynomialImage lam W ≠ ⊥ := by
  obtain ⟨p, hp, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  intro hbot
  have hmem : (p : PolynomialSpace r n) ∈
      youngRealPolynomialImage lam W :=
    ⟨p, hp, rfl⟩
  rw [hbot] at hmem
  apply hp0
  apply Subtype.ext
  simpa only [ZeroMemClass.coe_zero, ZeroMemClass.coe_eq_zero, Submodule.mem_bot] using hmem

theorem youngRealPolynomialImage_inf_orthogonal_eq_bot {r n : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (W : Submodule ℝ (HarmonicYoungSpace (n := n) lam)) :
    youngRealPolynomialImage lam W ⊓
      youngRealPolynomialImage lam Wᗮ = ⊥ := by
  apply bot_unique
  intro z hz
  obtain ⟨⟨p, hp, hpz⟩, ⟨q, hq, hqz⟩⟩ :=
    Submodule.mem_inf.mp hz
  have hpq : p = q := by
    apply Subtype.ext
    exact hpz.trans hqz.symm
  have hinner := (Submodule.mem_orthogonal W q).mp hq p hp
  rw [hpq] at hinner
  have hqzero : q = 0 := by
    by_contra hne
    have hpos := real_inner_self_pos.mpr hne
    linarith
  have hzzero : z = 0 := by
    rw [← hpz, hpq, hqzero]
    rfl
  simp only [hzzero, zero_mem]

/-- The young complex polynomial span used in the spherical-code argument. -/
def youngComplexPolynomialSpan {r n : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (W : Submodule ℝ (HarmonicYoungSpace (n := n) lam)) :
    Submodule ℂ (MvPolynomial (Fin ((r + 1) * n)) ℂ) :=
  polynomialComplexSpan (youngRealPolynomialImage lam W)

/-- The full young complex polynomial span used in the spherical-code argument. -/
def fullYoungComplexPolynomialSpan {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) :
    Submodule ℂ (MvPolynomial (Fin ((r + 1) * n)) ℂ) :=
  polynomialComplexSpan (harmonicYoungSubmodule lam)

theorem youngComplexPolynomialSpan_le_full {r n : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (W : Submodule ℝ (HarmonicYoungSpace (n := n) lam)) :
    youngComplexPolynomialSpan lam W ≤
      fullYoungComplexPolynomialSpan lam := by
  apply Submodule.span_mono
  rintro _ ⟨p, hp, rfl⟩
  exact ⟨p, youngRealPolynomialImage_le lam W hp, rfl⟩

theorem youngComplexPolynomialSpan_ne_bot_of_ne_bot {r n : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (W : Submodule ℝ (HarmonicYoungSpace (n := n) lam))
    (hW : W ≠ ⊥) : youngComplexPolynomialSpan lam W ≠ ⊥ :=
  polynomialComplexSpan_ne_bot_of_ne_bot _
    (youngRealPolynomialImage_ne_bot_of_ne_bot lam W hW)

theorem youngComplexPolynomialSpan_inf_orthogonal_eq_bot {r n : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (W : Submodule ℝ (HarmonicYoungSpace (n := n) lam)) :
    youngComplexPolynomialSpan lam W ⊓
      youngComplexPolynomialSpan lam Wᗮ = ⊥ :=
  polynomialComplexSpan_inf_eq_bot_of_inf_eq_bot _ _
    (youngRealPolynomialImage_inf_orthogonal_eq_bot lam W)

/-- The root operator word used in the spherical-code argument. -/
def rootOperatorWord {K V I : Type*} [Semiring K]
    [AddCommMonoid V] [Module K V]
    (E : I → V →ₗ[K] V) : List I → V →ₗ[K] V
  | [] => LinearMap.id
  | i :: w => (rootOperatorWord E w).comp (E i)

@[simp] theorem rootOperatorWord_nil {K V I : Type*} [Semiring K]
    [AddCommMonoid V] [Module K V]
    (E : I → V →ₗ[K] V) :
    rootOperatorWord E [] = LinearMap.id := rfl

@[simp] theorem rootOperatorWord_cons_apply {K V I : Type*} [Semiring K]
    [AddCommMonoid V] [Module K V]
    (E : I → V →ₗ[K] V) (i : I) (w : List I) (v : V) :
    rootOperatorWord E (i :: w) v = rootOperatorWord E w (E i v) := rfl

end HigherYoungTwoRowLieIrreducibility

namespace HigherYoungCyclicHighestSchur

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherYoungMixedGapLieGram
open MetricCodes.Spherical.HigherYoungTwoRowLieIrreducibility

theorem commute_rootOperatorWord
    {K V I : Type*} [Semiring K]
    [AddCommMonoid V] [Module K V]
    (R : I → V →ₗ[K] V) (A : V →ₗ[K] V)
    (hcomm : ∀ i, A.comp (R i) = (R i).comp A)
    (w : List I) :
    A.comp (rootOperatorWord R w) = (rootOperatorWord R w).comp A := by
  induction w with
  | nil => simp only [rootOperatorWord, LinearMap.comp_id, LinearMap.id_comp]
  | cons i w ih =>
      change A.comp ((rootOperatorWord R w).comp (R i)) =
        ((rootOperatorWord R w).comp (R i)).comp A
      rw [← LinearMap.comp_assoc, ih, LinearMap.comp_assoc,
        hcomm i, ← LinearMap.comp_assoc]

/-- The operator word span used in the spherical-code argument. -/
def operatorWordSpan
    {K V I : Type*} [Semiring K]
    [AddCommMonoid V] [Module K V]
    (R : I → V →ₗ[K] V) (v : V) : Submodule K V :=
  Submodule.span K (Set.range (fun w : List I => rootOperatorWord R w v))

private def operatorWordPairSpan
    {K V I : Type*} [Semiring K]
    [AddCommMonoid V] [Module K V]
    (R : I → V →ₗ[K] V) (v w : V) : Submodule K V :=
  operatorWordSpan R v ⊔ operatorWordSpan R w

theorem eq_smul_id_of_cyclic_eigenpair
    {K V I : Type*} [CommRing K]
    [AddCommGroup V] [Module K V]
    (R : I → V →ₗ[K] V) (A : V →ₗ[K] V)
    (hcomm : ∀ i, A.comp (R i) = (R i).comp A)
    (v w : V) (c : K)
    (hv : A v = c • v) (hw : A w = c • w)
    (hcyclic : operatorWordPairSpan R v w = ⊤) :
    A = c • LinearMap.id := by
  let E : Submodule K V := LinearMap.ker (A - c • LinearMap.id)
  have hvE : v ∈ E := by
    change A v - c • v = 0
    rw [hv, sub_self]
  have hwE : w ∈ E := by
    change A w - c • w = 0
    rw [hw, sub_self]
  have hword : ∀ (u : V), u ∈ E → operatorWordSpan R u ≤ E := by
    intro u hu
    rw [operatorWordSpan, Submodule.span_le]
    rintro _ ⟨word, rfl⟩
    change A (rootOperatorWord R word u) -
      c • rootOperatorWord R word u = 0
    have h := LinearMap.congr_fun
      (commute_rootOperatorWord R A hcomm word) u
    change A (rootOperatorWord R word u) =
      rootOperatorWord R word (A u) at h
    have hAu : A u = c • u := sub_eq_zero.mp hu
    rw [h, hAu, map_smul, sub_self]
  have htop : E = ⊤ := by
    apply top_unique
    rw [← hcyclic]
    exact sup_le (hword v hvE) (hword w hwE)
  have hzero : A - c • LinearMap.id = 0 :=
    LinearMap.ker_eq_top.mp htop
  exact sub_eq_zero.mp hzero

theorem complex_eigenpair_im_eq_zero_of_symmetric
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (A : V →ₗ[ℝ] V) (hA : A.IsSymmetric)
    (v w : V) (a b : ℝ)
    (hv : A v = a • v - b • w)
    (hw : A w = b • v + a • w)
    (hne : v ≠ 0 ∨ w ≠ 0) : b = 0 := by
  have hsym := hA v w
  rw [hv, hw, inner_sub_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_left,
    real_inner_smul_right, real_inner_smul_right] at hsym
  have hsum : 0 < ⟪v, v⟫_ℝ + ⟪w, w⟫_ℝ := by
    rcases hne with hvne | hwne
    · exact add_pos_of_pos_of_nonneg
        (real_inner_self_pos.mpr hvne) real_inner_self_nonneg
    · exact add_pos_of_nonneg_of_pos
        real_inner_self_nonneg (real_inner_self_pos.mpr hwne)
  nlinarith

theorem symmetric_eq_smul_id_of_complex_cyclic_eigenvector
    {V I : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (R : I → V →ₗ[ℝ] V) (A : V →ₗ[ℝ] V)
    (hA : A.IsSymmetric)
    (hcomm : ∀ i, A.comp (R i) = (R i).comp A)
    (v w : V) (c : ℂ)
    (hv : A v = c.re • v - c.im • w)
    (hw : A w = c.im • v + c.re • w)
    (hne : v ≠ 0 ∨ w ≠ 0)
    (hcyclic : operatorWordPairSpan R v w = ⊤) :
    A = c.re • LinearMap.id := by
  have him : c.im = 0 :=
    complex_eigenpair_im_eq_zero_of_symmetric A hA v w
      c.re c.im hv hw hne
  apply eq_smul_id_of_cyclic_eigenpair R A hcomm v w c.re
    (by simpa only [him, zero_smul, sub_zero] using hv)
    (by simpa only [him, zero_smul, zero_add] using hw)
    hcyclic

/-- The dominant highest real vector used in the spherical-code argument. -/
def dominantHighestRealVector {r n : ℕ}
    (hn : 2 * (r + 1) ≤ n)
    (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam) :
    HarmonicYoungSpace (n := n) lam :=
  ⟨polynomialRealPart
      (dominantHighestWeightWitness hn lam hdom).polynomial,
    (dominantHighestWeightWitness hn lam hdom).realPart_mem⟩

/-- The dominant highest imaginary vector used in the spherical-code argument. -/
def dominantHighestImaginaryVector {r n : ℕ}
    (hn : 2 * (r + 1) ≤ n)
    (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam) :
    HarmonicYoungSpace (n := n) lam :=
  ⟨polynomialImaginaryPart
      (dominantHighestWeightWitness hn lam hdom).polynomial,
    (dominantHighestWeightWitness hn lam hdom).imaginaryPart_mem⟩

theorem dominantHighestRealVector_ne_zero_or_imaginary_ne_zero
    {r n : ℕ} (hn : 2 * (r + 1) ≤ n)
    (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam) :
    dominantHighestRealVector hn lam hdom ≠ 0 ∨
      dominantHighestImaginaryVector hn lam hdom ≠ 0 := by
  rcases polynomialRealPart_ne_zero_or_polynomialImaginaryPart_ne_zero
    (dominantHighestWeightWitness hn lam hdom).nonzero with hreal | himag
  · left
    intro hzero
    apply hreal
    exact congrArg Subtype.val hzero
  · right
    intro hzero
    apply himag
    exact congrArg Subtype.val hzero

/-- The dominant highest rotation word span used in the spherical-code argument. -/
def dominantHighestRotationWordSpan {r n : ℕ}
    (hn : 2 * (r + 1) ≤ n)
    (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam) :
    Submodule ℝ (HarmonicYoungSpace (n := n) lam) :=
  operatorWordPairSpan (youngRotationFamily lam)
    (dominantHighestRealVector hn lam hdom)
    (dominantHighestImaginaryVector hn lam hdom)

theorem youngSymmetricRotationIntertwiner_eq_smul_id_of_dominantCyclicHighest
    {r n : ℕ} (hn : 2 * (r + 1) ≤ n)
    (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam)
    (A : HarmonicYoungSpace (n := n) lam →ₗ[ℝ]
      HarmonicYoungSpace (n := n) lam)
    (hA : A.IsSymmetric)
    (hcomm : ∀ a b : Fin n,
      A.comp (youngAmbientRotation lam a b) =
        (youngAmbientRotation lam a b).comp A)
    (c : ℂ)
    (hreal : A (dominantHighestRealVector hn lam hdom) =
      c.re • dominantHighestRealVector hn lam hdom -
        c.im • dominantHighestImaginaryVector hn lam hdom)
    (himaginary : A (dominantHighestImaginaryVector hn lam hdom) =
      c.im • dominantHighestRealVector hn lam hdom +
        c.re • dominantHighestImaginaryVector hn lam hdom)
    (hcyclic : dominantHighestRotationWordSpan hn lam hdom = ⊤) :
    A = c.re • LinearMap.id := by
  apply symmetric_eq_smul_id_of_complex_cyclic_eigenvector
    (youngRotationFamily lam) A hA
    (fun ab => hcomm ab.1 ab.2)
    (dominantHighestRealVector hn lam hdom)
    (dominantHighestImaginaryVector hn lam hdom)
    c hreal himaginary
    (dominantHighestRealVector_ne_zero_or_imaginary_ne_zero
      hn lam hdom)
  exact hcyclic

end HigherYoungCyclicHighestSchur

end

end Spherical

end MetricCodes


namespace MetricCodes

namespace Spherical

namespace HigherHarmonicYoung

section

open scoped BigOperators InnerProductSpace TensorProduct

namespace ArbitraryRowRaisingSchurTraceGram

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowDownstreamActualChannels
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInternalRowLowerGram
open MetricCodes.Spherical.HigherHarmonicYoung.ClebschRotation
open MetricCodes.Spherical.HigherHarmonicYoung.CrossGram
open MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherYoungCyclicHighestSchur
open MetricCodes.Spherical.HigherYoungPenultimateRowProjectedLower

theorem youngClebschRaise_scalar_eq_lower_dimension_ratio
    {r n : ℕ} (high low : Fin (r + 1) → ℕ)
    (hdeg : (∑ i, high i) = (∑ i, low i) + 1)
    (row : Fin (r + 1)) (raisingGram loweringGram : ℝ)
    (hraise :
      (youngClebschRaise (n := n) high low hdeg row).adjoint.comp
          (youngClebschRaise (n := n) high low hdeg row) =
        raisingGram • LinearMap.id)
    (hlower :
      (youngClebschLower (n := n) low high hdeg row).adjoint.comp
          (youngClebschLower (n := n) low high hdeg row) =
        loweringGram • LinearMap.id)
    (hlow : 0 < Module.finrank ℝ (HarmonicYoungSpace (n := n) low)) :
    raisingGram = loweringGram *
      (Module.finrank ℝ (HarmonicYoungSpace (n := n) high) : ℝ) /
      (Module.finrank ℝ (HarmonicYoungSpace (n := n) low) : ℝ) := by
  have htrace := youngClebschRaiseLower_trace (n := n)
    high low hdeg row
  rw [hraise, hlower] at htrace
  simp only [map_smul, LinearMap.trace_id, smul_eq_mul] at htrace
  have hlowR :
      (Module.finrank ℝ (HarmonicYoungSpace (n := n) low) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hlow)
  apply (eq_div_iff hlowR).2
  simpa only using htrace

theorem youngClebschRaise_gram_rotation_intertwine
    {r n : ℕ} (high low : Fin (r + 1) → ℕ)
    (hdeg : (∑ i, high i) = (∑ i, low i) + 1)
    (row : Fin (r + 1)) (a b : Fin n) :
    ((youngClebschRaise (n := n) high low hdeg row).adjoint.comp
        (youngClebschRaise (n := n) high low hdeg row)).comp
      (youngAmbientRotation low a b) =
    (youngAmbientRotation low a b).comp
      ((youngClebschRaise (n := n) high low hdeg row).adjoint.comp
        (youngClebschRaise (n := n) high low hdeg row)) := by
  exact crossGram_intertwines_of_skew
    (youngClebschRaise (n := n) high low hdeg row)
    (youngClebschRaise (n := n) high low hdeg row)
    (youngAmbientRotation low a b)
    (youngAmbientRotation low a b)
    (tensorAmbientRotation high a b)
    (youngAmbientRotation_adjoint low a b)
    (tensorAmbientRotation_adjoint high a b)
    (youngClebschRaise_rotation_intertwine high low hdeg row a b)
    (youngClebschRaise_rotation_intertwine high low hdeg row a b)

theorem youngClebschRaise_gram_scalar_of_dominantCyclicHighest
    {r n : ℕ} (high low : Fin (r + 1) → ℕ)
    (hdeg : (∑ i, high i) = (∑ i, low i) + 1)
    (row : Fin (r + 1))
    (hn : 2 * (r + 1) ≤ n) (hdom : Antitone low)
    (c : ℂ)
    (hreal :
      ((youngClebschRaise (n := n) high low hdeg row).adjoint.comp
        (youngClebschRaise (n := n) high low hdeg row))
          (dominantHighestRealVector hn low hdom) =
        c.re • dominantHighestRealVector hn low hdom -
          c.im • dominantHighestImaginaryVector hn low hdom)
    (himaginary :
      ((youngClebschRaise (n := n) high low hdeg row).adjoint.comp
        (youngClebschRaise (n := n) high low hdeg row))
          (dominantHighestImaginaryVector hn low hdom) =
        c.im • dominantHighestRealVector hn low hdom +
          c.re • dominantHighestImaginaryVector hn low hdom)
    (hcyclic : dominantHighestRotationWordSpan hn low hdom = ⊤) :
    (youngClebschRaise (n := n) high low hdeg row).adjoint.comp
        (youngClebschRaise (n := n) high low hdeg row) =
      c.re • LinearMap.id := by
  apply youngSymmetricRotationIntertwiner_eq_smul_id_of_dominantCyclicHighest
    hn low hdom
    ((youngClebschRaise (n := n) high low hdeg row).adjoint.comp
      (youngClebschRaise (n := n) high low hdeg row))
    (LinearMap.isSymmetric_adjoint_comp_self
      (youngClebschRaise (n := n) high low hdeg row))
  · exact youngClebschRaise_gram_rotation_intertwine high low hdeg row
  · exact hreal
  · exact himaginary
  · exact hcyclic

/-- The arbitrary row raising gram scalar used in the spherical-code argument. -/
def arbitraryRowRaisingGramScalar {r n : ℕ}
    (high : Fin (r + 1) → ℕ) (row : Fin (r + 1)) : ℝ :=
  internalRowLowerGramScalar high row *
    (Module.finrank ℝ (HarmonicYoungSpace (n := n) high) : ℝ) /
    (Module.finrank ℝ
      (HarmonicYoungSpace (n := n)
        (loweredInternalYoungWeight high row)) : ℝ)

theorem youngClebschRaise_arbitrary_inner_of_dominantCyclicHighest
    {r n : ℕ} (high : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (ha : 0 < high row)
    (hn : 2 * (r + 1) ≤ n)
    (hdomhigh : Antitone high)
    (hdomlow : Antitone (loweredInternalYoungWeight high row))
    (c : ℂ)
    (hreal :
      ((youngClebschRaise (n := n) high
        (loweredInternalYoungWeight high row)
        (loweredInternalYoungWeight_sum_add_one high row ha) row).adjoint.comp
        (youngClebschRaise (n := n) high
          (loweredInternalYoungWeight high row)
          (loweredInternalYoungWeight_sum_add_one high row ha) row))
          (dominantHighestRealVector hn
            (loweredInternalYoungWeight high row) hdomlow) =
        c.re • dominantHighestRealVector hn
          (loweredInternalYoungWeight high row) hdomlow -
          c.im • dominantHighestImaginaryVector hn
            (loweredInternalYoungWeight high row) hdomlow)
    (himaginary :
      ((youngClebschRaise (n := n) high
        (loweredInternalYoungWeight high row)
        (loweredInternalYoungWeight_sum_add_one high row ha) row).adjoint.comp
        (youngClebschRaise (n := n) high
          (loweredInternalYoungWeight high row)
          (loweredInternalYoungWeight_sum_add_one high row ha) row))
          (dominantHighestImaginaryVector hn
            (loweredInternalYoungWeight high row) hdomlow) =
        c.im • dominantHighestRealVector hn
          (loweredInternalYoungWeight high row) hdomlow +
          c.re • dominantHighestImaginaryVector hn
            (loweredInternalYoungWeight high row) hdomlow)
    (hcyclic : dominantHighestRotationWordSpan hn
      (loweredInternalYoungWeight high row) hdomlow = ⊤)
    (p q : HarmonicYoungSpace (n := n)
      (loweredInternalYoungWeight high row)) :
    ⟪youngClebschRaise high (loweredInternalYoungWeight high row)
        (loweredInternalYoungWeight_sum_add_one high row ha) row p,
      youngClebschRaise high (loweredInternalYoungWeight high row)
        (loweredInternalYoungWeight_sum_add_one high row ha) row q⟫_ℝ =
      arbitraryRowRaisingGramScalar (n := n) high row * ⟪p, q⟫_ℝ := by
  let low := loweredInternalYoungWeight high row
  let hdeg := loweredInternalYoungWeight_sum_add_one high row ha
  have hscalar :
      (youngClebschRaise (n := n) high low hdeg row).adjoint.comp
          (youngClebschRaise (n := n) high low hdeg row) =
        c.re • LinearMap.id := by
    exact youngClebschRaise_gram_scalar_of_dominantCyclicHighest
      high low hdeg row hn hdomlow c hreal himaginary hcyclic
  have hlower :
      (youngClebschLower (n := n) low high hdeg row).adjoint.comp
          (youngClebschLower (n := n) low high hdeg row) =
        internalRowLowerGramScalar high row • LinearMap.id := by
    exact youngClebschLower_arbitrary_adjoint_comp_self
      high row ha hdomhigh
  have hfin : 0 < Module.finrank ℝ (HarmonicYoungSpace (n := n) low) :=
    finrank_harmonicYoung_pos_of_antitone hn low hdomlow
  have hc : c.re = arbitraryRowRaisingGramScalar (n := n) high row := by
    exact youngClebschRaise_scalar_eq_lower_dimension_ratio
      high low hdeg row c.re (internalRowLowerGramScalar high row)
      hscalar hlower hfin
  calc
    ⟪youngClebschRaise high low hdeg row p,
      youngClebschRaise high low hdeg row q⟫_ℝ =
        ⟪p, ((youngClebschRaise high low hdeg row).adjoint.comp
          (youngClebschRaise high low hdeg row)) q⟫_ℝ := by
      rw [LinearMap.comp_apply]
      exact (LinearMap.adjoint_inner_right
        (youngClebschRaise high low hdeg row) p
        (youngClebschRaise high low hdeg row q)).symm
    _ = c.re * ⟪p, q⟫_ℝ := by
      rw [hscalar]
      change ⟪p, c.re • q⟫_ℝ = c.re * ⟪p, q⟫_ℝ
      exact real_inner_smul_right p q c.re
    _ = arbitraryRowRaisingGramScalar (n := n) high row *
      ⟪p, q⟫_ℝ := by rw [hc]

end ArbitraryRowRaisingSchurTraceGram

end

section


open scoped BigOperators

namespace IsotropicAmbientHighestLine

open MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors
open MetricCodes.Spherical.HigherHarmonicYoung.BideterminantHighestLine

theorem rowDerivation_nullSubstitution_sourceRowRoot
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (i j : Fin (r + 1))
    (q : SourceMatrix (r + 1)) :
    rowDerivation i j (nullSubstitution h q) =
      nullSubstitution h (sourceRowRoot i j q) := by
  rw [← complexPolarization_eq_rowDerivation,
    complexPolarization_nullSubstitution]
  congr 1
  exact (sourceRowRoot_apply i j q).symm

theorem ambientPositiveRoot_nullSubstitution_sourceColumnRoot
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (i j : Fin (r + 1))
    (q : SourceMatrix (r + 1)) :
    ambientPositiveRoot h i j (nullSubstitution h q) =
      (2 : ℂ) • nullSubstitution h (sourceColumnRoot i j q) := by
  classical
  induction q using MvPolynomial.induction_on with
  | C c =>
      simp only [nullSubstitution, MvPolynomial.aeval_eq_bind₁, MvPolynomial.algHom_C,
        MvPolynomial.algebraMap_eq, MvPolynomial.derivation_C, map_zero, smul_zero]
  | add p q hp hq =>
      simp only [map_add, hp, hq, smul_add]
  | mul_X q z hq =>
      rcases z with ⟨a, b⟩
      rw [map_mul, (ambientPositiveRoot h i j).leibniz,
        (sourceColumnRoot i j).leibniz]
      simp only [Algebra.smul_def, map_add, map_mul,
        nullSubstitution_X]
      rw [hq]
      rw [← isotropicVariable_eq_nullRowLinearForm,
        ambientPositiveRoot_isotropicVariable,
        sourceColumnRoot_X]
      by_cases hjb : j = b
      · subst b
        simp only [Algebra.algebraMap_self, RingHom.id_apply, ↓reduceIte,
          isotropicVariable_eq_nullRowLinearForm, Algebra.smul_def, MvPolynomial.algebraMap_eq,
          sourceColumnRoot_apply, map_sum, map_mul, nullSubstitution_X]
        ring
      · simp only [Algebra.algebraMap_self, RingHom.id_apply, hjb, ↓reduceIte, mul_zero,
          isotropicVariable_eq_nullRowLinearForm, sourceColumnRoot_apply, map_sum, map_mul,
          nullSubstitution_X, Algebra.smul_def, MvPolynomial.algebraMap_eq, zero_add, map_zero]
        ring

theorem ambientCartan_nullSubstitution_sourceColumnRoot
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (i : Fin (r + 1)) (q : SourceMatrix (r + 1)) :
    ambientCartan h i (nullSubstitution h q) =
      (2 : ℂ) • nullSubstitution h (sourceColumnRoot i i q) :=
  ambientPositiveRoot_nullSubstitution_sourceColumnRoot h i i q

/-- The source matrix highest submodule used in the spherical-code argument. -/
def sourceMatrixHighestSubmodule {r : ℕ}
    (lam : Fin (r + 1) → ℕ) : Submodule ℂ (SourceMatrix (r + 1)) :=
  (⨅ i : Fin (r + 1), LinearMap.ker
    ((sourceRowRoot i i).toLinearMap -
      (lam i : ℂ) • LinearMap.id)) ⊓
  (⨅ i : Fin (r + 1), LinearMap.ker
    ((sourceColumnRoot i i).toLinearMap -
      (lam i : ℂ) • LinearMap.id)) ⊓
  (⨅ i : Fin (r + 1), ⨅ j : Fin (r + 1), ⨅ (_ : i < j),
    LinearMap.ker (sourceRowRoot i j).toLinearMap)

theorem mem_sourceMatrixHighestSubmodule {r : ℕ}
    (lam : Fin (r + 1) → ℕ) (q : SourceMatrix (r + 1)) :
    q ∈ sourceMatrixHighestSubmodule lam ↔
      (∀ i, sourceRowRoot i i q = (lam i : ℂ) • q) ∧
      (∀ i, sourceColumnRoot i i q = (lam i : ℂ) • q) ∧
      (∀ i j, i < j → sourceRowRoot i j q = 0) := by
  simp only [sourceMatrixHighestSubmodule, Submodule.mem_inf,
    Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
  aesop

/-- The ambient isotropic highest submodule used in the spherical-code argument. -/
def ambientIsotropicHighestSubmodule {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (lam : Fin (r + 1) → ℕ) :
    Submodule ℂ (MvPolynomial (Fin ((r + 1) * n)) ℂ) :=
  LinearMap.range (nullSubstitution h).toLinearMap ⊓
  (⨅ i : Fin (r + 1), LinearMap.ker
    ((rowDerivation i i).toLinearMap -
      (lam i : ℂ) • LinearMap.id)) ⊓
  (⨅ i : Fin (r + 1), LinearMap.ker
    ((ambientCartan h i).toLinearMap -
      ((2 * lam i : ℕ) : ℂ) • LinearMap.id)) ⊓
  (⨅ i : Fin (r + 1), ⨅ j : Fin (r + 1), ⨅ (_ : i < j),
    LinearMap.ker (rowDerivation i j).toLinearMap)

theorem mem_ambientIsotropicHighestSubmodule {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (lam : Fin (r + 1) → ℕ)
    (f : MvPolynomial (Fin ((r + 1) * n)) ℂ) :
    f ∈ ambientIsotropicHighestSubmodule h lam ↔
      (∃ q : SourceMatrix (r + 1), nullSubstitution h q = f) ∧
      (∀ i, rowDerivation i i f = (lam i : ℂ) • f) ∧
      (∀ i, ambientCartan h i f = ((2 * lam i : ℕ) : ℂ) • f) ∧
      (∀ i j, i < j → rowDerivation i j f = 0) := by
  simp only [ambientIsotropicHighestSubmodule, Submodule.mem_inf,
    Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero,
    LinearMap.mem_range]
  aesop

theorem sourceRowRoot_eigen_of_ambient
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (i : Fin (r + 1)) (q : SourceMatrix (r + 1)) (c : ℂ)
    (heigen : rowDerivation i i (nullSubstitution h q) =
      c • nullSubstitution h q) :
    sourceRowRoot i i q = c • q := by
  apply nullSubstitution_injective h
  rw [map_smul, ← rowDerivation_nullSubstitution_sourceRowRoot]
  exact heigen

theorem sourceColumnRoot_eigen_of_ambient
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (i : Fin (r + 1)) (q : SourceMatrix (r + 1)) (k : ℕ)
    (heigen : ambientCartan h i (nullSubstitution h q) =
      ((2 * k : ℕ) : ℂ) • nullSubstitution h q) :
    sourceColumnRoot i i q = (k : ℂ) • q := by
  rw [ambientCartan_nullSubstitution_sourceColumnRoot] at heigen
  have hcast : ((2 * k : ℕ) : ℂ) = (2 : ℂ) * (k : ℂ) := by
    norm_num
  rw [hcast, mul_smul] at heigen
  have hzero : (2 : ℂ) •
      (nullSubstitution h (sourceColumnRoot i i q) -
        (k : ℂ) • nullSubstitution h q) = 0 := by
    rw [smul_sub, heigen, sub_self]
  have hcancel :
      nullSubstitution h (sourceColumnRoot i i q) =
        (k : ℂ) • nullSubstitution h q :=
    sub_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_left (by norm_num))
  apply nullSubstitution_injective h
  rw [map_smul]
  exact hcancel

theorem ambientIsotropicHighestSubmodule_eq_map_source
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (lam : Fin (r + 1) → ℕ) :
    ambientIsotropicHighestSubmodule h lam =
      Submodule.map (nullSubstitution h).toLinearMap
        (sourceMatrixHighestSubmodule lam) := by
  apply le_antisymm
  · intro f hf
    obtain ⟨⟨q, rfl⟩, hrow, hcartan, hupper⟩ :=
      (mem_ambientIsotropicHighestSubmodule h lam f).mp hf
    refine ⟨q, (mem_sourceMatrixHighestSubmodule lam q).mpr
      ⟨?_, ?_, ?_⟩, rfl⟩
    · intro i
      exact sourceRowRoot_eigen_of_ambient h i q (lam i) (hrow i)
    · intro i
      exact sourceColumnRoot_eigen_of_ambient h i q (lam i)
        (hcartan i)
    · intro i j hij
      apply nullSubstitution_injective h
      rw [map_zero, ← rowDerivation_nullSubstitution_sourceRowRoot]
      exact hupper i j hij
  · rintro f ⟨q, hq, rfl⟩
    obtain ⟨hrow, hcol, hupper⟩ :=
      (mem_sourceMatrixHighestSubmodule lam q).mp hq
    apply (mem_ambientIsotropicHighestSubmodule h lam _).mpr
    refine ⟨⟨q, rfl⟩, ?_, ?_, ?_⟩
    · intro i
      change rowDerivation i i (nullSubstitution h q) =
        (lam i : ℂ) • nullSubstitution h q
      rw [rowDerivation_nullSubstitution_sourceRowRoot,
        hrow i, map_smul]
    · intro i
      change ambientCartan h i (nullSubstitution h q) =
        ((2 * lam i : ℕ) : ℂ) • nullSubstitution h q
      rw [ambientCartan_nullSubstitution_sourceColumnRoot,
        hcol i, map_smul, ← mul_smul]
      norm_num
    · intro i j hij
      change rowDerivation i j (nullSubstitution h q) = _
      rw [rowDerivation_nullSubstitution_sourceRowRoot,
        hupper i j hij, map_zero]

theorem finrank_ambientIsotropicHighestSubmodule_eq_source
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (lam : Fin (r + 1) → ℕ) :
    Module.finrank ℂ (ambientIsotropicHighestSubmodule h lam) =
      Module.finrank ℂ (sourceMatrixHighestSubmodule lam) := by
  rw [ambientIsotropicHighestSubmodule_eq_map_source]
  exact (Submodule.equivMapOfInjective
    (nullSubstitution h).toLinearMap
    (nullSubstitution_injective h)
    (sourceMatrixHighestSubmodule lam)).finrank_eq.symm

theorem sourceHighestWeightPolynomial_mem_sourceMatrixHighestSubmodule
    {r : ℕ} (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam) :
    sourceHighestWeightPolynomial (signatureExponent lam) ∈
      sourceMatrixHighestSubmodule lam := by
  rw [mem_sourceMatrixHighestSubmodule]
  have hsig := determinantWeight_signatureExponent lam hdom
  refine ⟨?_, ?_, ?_⟩
  · intro i
    rw [sourceRowRoot_sourceHighestWeightPolynomial_self,
      congrFun hsig i]
  · intro i
    rw [sourceColumnRoot_sourceHighestWeightPolynomial_self,
      congrFun hsig i]
  · intro i j hij
    exact sourceRowRoot_sourceHighestWeightPolynomial_upper
      (signatureExponent lam) i j hij

theorem sourceHighestWeightPolynomial_ne_zero
    {r : ℕ} (lam : Fin (r + 1) → ℕ) :
    sourceHighestWeightPolynomial (signatureExponent lam) ≠ 0 := by
  intro hzero
  have heval := eval_sourceHighestWeightPolynomial (signatureExponent lam)
  simp only [hzero, map_zero, zero_ne_one] at heval

theorem ambientIsotropicHighestSubmodule_eq_span_iff_source_finrank
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam) :
    ambientIsotropicHighestSubmodule h lam =
      Submodule.span ℂ
        {highestWeightPolynomial h (signatureExponent lam)} ↔
      Module.finrank ℂ (sourceMatrixHighestSubmodule lam) = 1 := by
  constructor
  · intro hline
    rw [← finrank_ambientIsotropicHighestSubmodule_eq_source h lam,
      hline]
    exact finrank_span_singleton
      (highestWeightPolynomial_ne_zero h (signatureExponent lam))
  · intro hdim
    rw [ambientIsotropicHighestSubmodule_eq_map_source]
    have hsource : sourceMatrixHighestSubmodule lam =
        Submodule.span ℂ
          {sourceHighestWeightPolynomial (signatureExponent lam)} :=
      eq_span_singleton_of_mem_of_finrank_eq_one hdim
        (sourceHighestWeightPolynomial_mem_sourceMatrixHighestSubmodule
          lam hdom)
        (sourceHighestWeightPolynomial_ne_zero lam)
    rw [hsource, LinearMap.map_span]
    simp only [AlgHom.toLinearMap_apply, Set.image_singleton,
      nullSubstitution_sourceHighestWeightPolynomial]

end IsotropicAmbientHighestLine

end

end HigherHarmonicYoung

section


open scoped BigOperators

namespace HigherYoungAllRankSourceHighestKernel

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors
open MetricCodes.Spherical.HigherHarmonicYoung.BideterminantHighestLine

theorem sourceColumnRoot_sourceLeadingMinor_upper {r : ℕ}
    (i j : Fin (r + 1)) (hij : i < j) (k : Fin (r + 1)) :
    sourceColumnRoot i j (sourceLeadingMinor k) = 0 := by
  classical
  unfold sourceLeadingMinor
  by_cases hj : j.val ≤ k.val
  · let jj : Fin (k.val + 1) := ⟨j.val, by omega⟩
    let ii : Fin (k.val + 1) := ⟨i.val, by
      have hijv : i.val < j.val := hij
      omega⟩
    have hjj : minorIndex k jj = j := Fin.ext rfl
    have hii : minorIndex k ii = i := Fin.ext rfl
    rw [derivation_det_singleColumn (sourceColumnRoot i j)
      (Matrix.of fun a b : Fin (k.val + 1) =>
        MvPolynomial.X (minorIndex k a, minorIndex k b)) jj]
    · have hcol :
          (fun a : Fin (k.val + 1) =>
            sourceColumnRoot i j
              (MvPolynomial.X (minorIndex k a, minorIndex k jj))) =
          (fun a : Fin (k.val + 1) =>
            MvPolynomial.X (minorIndex k a, minorIndex k ii)) := by
        funext a
        rw [sourceColumnRoot_X, hjj, hii, ite_eq_left rfl]
      simp only [Matrix.of_apply]
      rw [hcol]
      have hcolMatrix :
          (fun a : Fin (k.val + 1) =>
            MvPolynomial.X (minorIndex k a, minorIndex k ii)) =
          (fun a => (Matrix.of fun a b : Fin (k.val + 1) =>
            (MvPolynomial.X (minorIndex k a, minorIndex k b) :
              SourceMatrix (r + 1))) a ii) := by
        funext a
        simp only [Matrix.of_apply]
      rw [hcolMatrix]
      apply Matrix.det_updateCol_eq_zero
      intro heq
      have hv := congrArg Fin.val heq
      have hijv : i.val < j.val := hij
      change i.val = j.val at hv
      omega
    · intro a b hab
      simp only [Matrix.of_apply]
      rw [sourceColumnRoot_X]
      have hne : j ≠ minorIndex k b := by
        intro heq
        apply hab
        apply Fin.ext
        have hv := congrArg Fin.val heq
        change j.val = b.val at hv
        exact hv.symm
      simp only [hne, ↓reduceIte]
  · apply derivation_det_eq_zero
    intro a b
    simp only [Matrix.of_apply]
    rw [sourceColumnRoot_X]
    have hne : j ≠ minorIndex k b := by
      intro heq
      have hv := congrArg Fin.val heq
      change j.val = b.val at hv
      have hb := b.isLt
      omega
    simp only [hne, ↓reduceIte]

theorem sourceColumnRoot_sourceHighestWeightPolynomial_upper {r : ℕ}
    (e : Fin (r + 1) → ℕ)
    (i j : Fin (r + 1)) (hij : i < j) :
    sourceColumnRoot i j (sourceHighestWeightPolynomial e) = 0 := by
  classical
  unfold sourceHighestWeightPolynomial
  apply derivation_prod_eq_zero
  intro k _
  rw [(sourceColumnRoot i j).leibniz_pow,
    sourceColumnRoot_sourceLeadingMinor_upper i j hij k]
  simp only [smul_eq_mul, mul_zero, nsmul_zero]

private def sourceHighestKernel {r : ℕ} (lam : Fin (r + 1) → ℕ) :
    Submodule ℂ (SourceMatrix (r + 1)) :=
  (⨅ i : Fin (r + 1), LinearMap.ker
      ((sourceRowRoot i i).toLinearMap -
        (lam i : ℂ) • LinearMap.id)) ⊓
    (⨅ i : Fin (r + 1), LinearMap.ker
      ((sourceColumnRoot i i).toLinearMap -
        (lam i : ℂ) • LinearMap.id)) ⊓
    (⨅ i : Fin (r + 1), ⨅ j : Fin (r + 1), ⨅ (_ : i < j),
      LinearMap.ker (sourceRowRoot i j).toLinearMap) ⊓
    (⨅ i : Fin (r + 1), ⨅ j : Fin (r + 1), ⨅ (_ : i < j),
      LinearMap.ker (sourceColumnRoot i j).toLinearMap)

theorem mem_sourceHighestKernel {r : ℕ}
    (lam : Fin (r + 1) → ℕ) (q : SourceMatrix (r + 1)) :
    q ∈ sourceHighestKernel lam ↔
      (∀ i : Fin (r + 1), sourceRowRoot i i q = (lam i : ℂ) • q) ∧
      (∀ i : Fin (r + 1), sourceColumnRoot i i q = (lam i : ℂ) • q) ∧
      (∀ i j : Fin (r + 1), i < j → sourceRowRoot i j q = 0) ∧
      (∀ i j : Fin (r + 1), i < j → sourceColumnRoot i j q = 0) := by
  simp only [sourceHighestKernel, Submodule.mem_inf, Submodule.mem_iInf,
    LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero]
  aesop

theorem sourceHighestWeightPolynomial_mem_sourceHighestKernel
    {r : ℕ} (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam) :
    sourceHighestWeightPolynomial (signatureExponent lam) ∈
      sourceHighestKernel lam := by
  rw [mem_sourceHighestKernel]
  have hweight := determinantWeight_signatureExponent lam hdom
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    rw [sourceRowRoot_sourceHighestWeightPolynomial_self,
      congrFun hweight i]
  · intro i
    rw [sourceColumnRoot_sourceHighestWeightPolynomial_self,
      congrFun hweight i]
  · exact sourceRowRoot_sourceHighestWeightPolynomial_upper
      (signatureExponent lam)
  · exact sourceColumnRoot_sourceHighestWeightPolynomial_upper
      (signatureExponent lam)

end HigherYoungAllRankSourceHighestKernel

end

section


open scoped BigOperators

namespace HigherYoungAllRankSourceDiagonalBalance

open MetricCodes.Spherical.HigherHarmonicYoung.BideterminantHighestLine

private def sourceDiagonalExponent {m : ℕ} (lam : Fin m → ℕ) :
    Fin m × Fin m →₀ ℕ :=
  ∑ i : Fin m, Finsupp.single (i, i) (lam i)

@[simp] theorem sourceDiagonalExponent_apply {m : ℕ}
    (lam : Fin m → ℕ) (i j : Fin m) :
    sourceDiagonalExponent lam (i, j) =
      if i = j then lam i else 0 := by
  classical
  by_cases hij : i = j
  · subst j
    simp only [sourceDiagonalExponent, Finsupp.coe_finsetSum, Finset.sum_apply,
      Finsupp.single_apply, Prod.mk.injEq, and_self, Finset.sum_ite_eq', Finset.mem_univ,
      ↓reduceIte]
  · simp only [sourceDiagonalExponent, Finsupp.coe_finsetSum, Finset.sum_apply,
      Finsupp.single_apply, Prod.mk.injEq, hij, ↓reduceIte, Finset.sum_eq_zero_iff, Finset.mem_univ,
      ite_eq_right_iff, and_imp, forall_const, forall_eq, IsEmpty.forall_iff]

theorem rowWeightedEntry_le_columnWeightedEntry {m : ℕ}
    (d : Fin m × Fin m →₀ ℕ)
    (hbelow : ∀ i j : Fin m, j < i → d (i, j) = 0)
    (i j : Fin m) :
    i.val * d (i, j) ≤ j.val * d (i, j) := by
  by_cases hji : j < i
  · simp only [hbelow i j hji, mul_zero, Std.le_refl]
  · exact Nat.mul_le_mul_right (d (i, j))
      (show i.val ≤ j.val from Fin.le_iff_val_le_val.mp (le_of_not_gt hji))

theorem rowWeightedMass_eq_columnWeightedMass {m : ℕ}
    (lam : Fin m → ℕ) (d : Fin m × Fin m →₀ ℕ)
    (hrow : ∀ i : Fin m, sourceRowDegree d i = lam i)
    (hcolumn : ∀ i : Fin m, sourceColumnDegree d i = lam i) :
    (∑ i : Fin m, ∑ j : Fin m, i.val * d (i, j)) =
      ∑ i : Fin m, ∑ j : Fin m, j.val * d (i, j) := by
  calc
    (∑ i : Fin m, ∑ j : Fin m, i.val * d (i, j)) =
        ∑ i : Fin m, i.val * sourceRowDegree d i := by
          simp only [sourceRowDegree, Finset.mul_sum]
    _ = ∑ i : Fin m, i.val * lam i := by simp_rw [hrow]
    _ = ∑ j : Fin m, j.val * sourceColumnDegree d j := by
          simp_rw [hcolumn]
    _ = ∑ j : Fin m, ∑ i : Fin m, j.val * d (i, j) := by
          simp only [sourceColumnDegree, Finset.mul_sum]
    _ = ∑ i : Fin m, ∑ j : Fin m, j.val * d (i, j) := by
          rw [Finset.sum_comm]

theorem rowWeightedEntry_eq_columnWeightedEntry_of_balance {m : ℕ}
    (lam : Fin m → ℕ) (d : Fin m × Fin m →₀ ℕ)
    (hrow : ∀ i : Fin m, sourceRowDegree d i = lam i)
    (hcolumn : ∀ i : Fin m, sourceColumnDegree d i = lam i)
    (hbelow : ∀ i j : Fin m, j < i → d (i, j) = 0)
    (i j : Fin m) :
    i.val * d (i, j) = j.val * d (i, j) := by
  have hmass := rowWeightedMass_eq_columnWeightedMass
    lam d hrow hcolumn
  have hroweq : ∀ a : Fin m,
      (∑ b : Fin m, a.val * d (a, b)) =
        ∑ b : Fin m, b.val * d (a, b) := by
    intro a
    exact (Finset.sum_eq_sum_iff_of_le (fun b _ =>
      Finset.sum_le_sum (fun c _ =>
        rowWeightedEntry_le_columnWeightedEntry d hbelow b c))).mp
          hmass a (Finset.mem_univ a)
  exact (Finset.sum_eq_sum_iff_of_le (fun b _ =>
    rowWeightedEntry_le_columnWeightedEntry d hbelow i b)).mp
      (hroweq i) j (Finset.mem_univ j)

theorem sourceExponent_above_eq_zero_of_diagonalBalance {m : ℕ}
    (lam : Fin m → ℕ) (d : Fin m × Fin m →₀ ℕ)
    (hrow : ∀ i : Fin m, sourceRowDegree d i = lam i)
    (hcolumn : ∀ i : Fin m, sourceColumnDegree d i = lam i)
    (hbelow : ∀ i j : Fin m, j < i → d (i, j) = 0)
    (i j : Fin m) (hij : i < j) : d (i, j) = 0 := by
  by_contra hnonzero
  have hpositive : 0 < d (i, j) := Nat.pos_of_ne_zero hnonzero
  have hstrict : i.val * d (i, j) < j.val * d (i, j) :=
    Nat.mul_lt_mul_of_pos_right (show i.val < j.val from hij) hpositive
  exact (Nat.ne_of_lt hstrict)
    (rowWeightedEntry_eq_columnWeightedEntry_of_balance
      lam d hrow hcolumn hbelow i j)

theorem sourceExponent_offDiagonal_eq_zero_of_diagonalBalance {m : ℕ}
    (lam : Fin m → ℕ) (d : Fin m × Fin m →₀ ℕ)
    (hrow : ∀ i : Fin m, sourceRowDegree d i = lam i)
    (hcolumn : ∀ i : Fin m, sourceColumnDegree d i = lam i)
    (hbelow : ∀ i j : Fin m, j < i → d (i, j) = 0)
    (i j : Fin m) (hij : i ≠ j) : d (i, j) = 0 := by
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact sourceExponent_above_eq_zero_of_diagonalBalance
      lam d hrow hcolumn hbelow i j hlt
  · exact hbelow i j hgt

theorem sourceExponent_diagonal_eq_of_diagonalBalance {m : ℕ}
    (lam : Fin m → ℕ) (d : Fin m × Fin m →₀ ℕ)
    (hrow : ∀ i : Fin m, sourceRowDegree d i = lam i)
    (hcolumn : ∀ i : Fin m, sourceColumnDegree d i = lam i)
    (hbelow : ∀ i j : Fin m, j < i → d (i, j) = 0)
    (i : Fin m) : d (i, i) = lam i := by
  calc
    d (i, i) = sourceRowDegree d i := by
      unfold sourceRowDegree
      symm
      apply Finset.sum_eq_single i
      · intro j _ hji
        exact sourceExponent_offDiagonal_eq_zero_of_diagonalBalance
          lam d hrow hcolumn hbelow i j (Ne.symm hji)
      · simp only [Finset.mem_univ, not_true_eq_false, IsEmpty.forall_iff]
    _ = lam i := hrow i

theorem sourceExponent_eq_diagonal_of_upperTriangular
    {m : ℕ} (lam : Fin m → ℕ) (d : Fin m × Fin m →₀ ℕ)
    (hrow : ∀ i : Fin m, sourceRowDegree d i = lam i)
    (hcolumn : ∀ i : Fin m, sourceColumnDegree d i = lam i)
    (hbelow : ∀ i j : Fin m, j < i → d (i, j) = 0) :
    d = sourceDiagonalExponent lam := by
  ext z
  rcases z with ⟨i, j⟩
  by_cases hij : i = j
  · subst j
    simpa only [sourceDiagonalExponent_apply, ↓reduceIte] using
      sourceExponent_diagonal_eq_of_diagonalBalance lam d hrow hcolumn hbelow i
  · simp only [sourceExponent_offDiagonal_eq_zero_of_diagonalBalance lam d hrow hcolumn hbelow i
    j hij,
      sourceDiagonalExponent_apply, hij, ↓reduceIte]

end HigherYoungAllRankSourceDiagonalBalance

end

section


open scoped BigOperators

namespace HigherYoungAllRankSourceCoefficientStraightening

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors
open MetricCodes.Spherical.HigherHarmonicYoung.BideterminantHighestLine
open MetricCodes.Spherical.HigherYoungAllRankSourceHighestKernel
open MetricCodes.Spherical.HigherYoungAllRankSourceDiagonalBalance

private def belowDiagonalWeight {m : ℕ} (z : Fin m × Fin m) : ℕ :=
  z.1.val - z.2.val

/-- The below diagonal mass used in the spherical-code argument. -/
def belowDiagonalMass {m : ℕ} (d : Fin m × Fin m →₀ ℕ) : ℕ :=
  ∑ z : Fin m × Fin m, belowDiagonalWeight z * d z

theorem belowDiagonalMass_add_single {m : ℕ}
    (d : Fin m × Fin m →₀ ℕ) (z : Fin m × Fin m) (k : ℕ) :
    belowDiagonalMass (d + Finsupp.single z k) =
      belowDiagonalMass d + belowDiagonalWeight z * k := by
  classical
  unfold belowDiagonalMass
  simp_rw [Finsupp.add_apply, Finsupp.single_apply, mul_add,
    Finset.sum_add_distrib]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

theorem belowDiagonalMass_sub_single_add {m : ℕ}
    (d : Fin m × Fin m →₀ ℕ) (z : Fin m × Fin m)
    (hz : 0 < d z) :
    belowDiagonalMass (d - Finsupp.single z 1) +
        belowDiagonalWeight z = belowDiagonalMass d := by
  have heq : d - Finsupp.single z 1 + Finsupp.single z 1 = d := by
    ext w
    by_cases hw : w = z
    · subst w
      simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
        Finsupp.single_eq_same, Nat.sub_add_cancel hz]
    · simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
        Finsupp.single_eq_of_ne hw, tsub_zero, add_zero]
  have hmass := belowDiagonalMass_add_single
    (d - Finsupp.single z 1) z 1
  simpa only [mul_one, heq] using hmass.symm

private def upperRootTargetExponent {m : ℕ}
    (d : Fin m × Fin m →₀ ℕ) (i j : Fin m) :
    Fin m × Fin m →₀ ℕ :=
  d - Finsupp.single (j, i) 1 + Finsupp.single (i, i) 1

private def upperRootSourceExponent {m : ℕ}
    (d : Fin m × Fin m →₀ ℕ) (i j k : Fin m) :
    Fin m × Fin m →₀ ℕ :=
  upperRootTargetExponent d i j -
    Finsupp.single (i, k) 1 + Finsupp.single (j, k) 1

theorem upperRootSourceExponent_self {m : ℕ}
    (d : Fin m × Fin m →₀ ℕ) (i j : Fin m)
    (hij : i < j) (hpositive : 0 < d (j, i)) :
    upperRootSourceExponent d i j i = d := by
  ext z
  by_cases hji : z = (j, i)
  · subst z
    simp only [upperRootSourceExponent, upperRootTargetExponent, add_tsub_cancel_right,
      Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, Finsupp.single_eq_same,
      Nat.sub_add_cancel hpositive]
  · by_cases hii : z = (i, i)
    · subst z
      simp only [upperRootSourceExponent, upperRootTargetExponent, add_tsub_cancel_right,
        Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, ne_eq, Prod.mk.injEq,
        ne_of_lt hij, and_true, not_false_eq_true, Finsupp.single_eq_of_ne, tsub_zero, add_zero]
    · simp only [upperRootSourceExponent, upperRootTargetExponent, add_tsub_cancel_right,
        Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, Finsupp.single_eq_of_ne hji,
        tsub_zero, add_zero]

theorem upperRootTarget_coefficient_eq_zero {m : ℕ}
    (p : SourceMatrix m) (i j : Fin m) (hij : i < j)
    (d : Fin m × Fin m →₀ ℕ)
    (hhighest : sourceRowRoot i j p = 0) :
    (∑ k : Fin m,
      if upperRootTargetExponent d i j (i, k) = 0 then 0
      else (upperRootTargetExponent d i j (j, k) + 1 : ℕ) •
        p.coeff (upperRootSourceExponent d i j k)) = 0 := by
  have hcoeff := congrArg
    (MvPolynomial.coeff (upperRootTargetExponent d i j)) hhighest
  rw [sourceRowRoot_apply, MvPolynomial.coeff_sum] at hcoeff
  simp only [MvPolynomial.coeff_zero] at hcoeff
  convert hcoeff using 1
  apply Finset.sum_congr rfl
  intro k _
  exact (coeff_X_mul_pderiv_ne p (i, k) (j, k)
    (by intro heq; exact (ne_of_lt hij) (Prod.mk.inj heq).1)
    (upperRootTargetExponent d i j)).symm

theorem belowDiagonalMass_upperRootTarget_add {m : ℕ}
    (d : Fin m × Fin m →₀ ℕ) (i j : Fin m)
    (hpositive : 0 < d (j, i)) :
    belowDiagonalMass (upperRootTargetExponent d i j) +
      (j.val - i.val) = belowDiagonalMass d := by
  unfold upperRootTargetExponent
  rw [belowDiagonalMass_add_single]
  have hweight : belowDiagonalWeight (i, i) = 0 := by
    simp only [belowDiagonalWeight, tsub_self]
  rw [hweight]
  simp only [zero_mul, add_zero]
  simpa only [belowDiagonalWeight] using belowDiagonalMass_sub_single_add d (j, i) hpositive

theorem belowDiagonalMass_upperRootSource_lt {m : ℕ}
    (d : Fin m × Fin m →₀ ℕ) (i j k : Fin m)
    (hij : i < j) (hik : i < k)
    (hpositive : 0 < d (j, i))
    (htarget : 0 < upperRootTargetExponent d i j (i, k)) :
    belowDiagonalMass (upperRootSourceExponent d i j k) <
      belowDiagonalMass d := by
  let e := upperRootTargetExponent d i j
  have hremove := belowDiagonalMass_sub_single_add e (i, k) htarget
  have hzero : belowDiagonalWeight (i, k) = 0 := by
    simp only [belowDiagonalWeight]
    omega
  rw [hzero, add_zero] at hremove
  have hadd := belowDiagonalMass_add_single
    (e - Finsupp.single (i, k) 1) (j, k) 1
  have htargetmass := belowDiagonalMass_upperRootTarget_add
    d i j hpositive
  change belowDiagonalMass e + (j.val - i.val) =
    belowDiagonalMass d at htargetmass
  change belowDiagonalMass
      (e - Finsupp.single (i, k) 1 + Finsupp.single (j, k) 1) <
    belowDiagonalMass d
  rw [hadd]
  simp only [mul_one]
  rw [hremove]
  have hweight : belowDiagonalWeight (j, k) < j.val - i.val := by
    change j.val - k.val < j.val - i.val
    have hijv : i.val < j.val := hij
    have hikv : i.val < k.val := hik
    omega
  omega

@[simp] theorem upperRootTargetExponent_diagonal {m : ℕ}
    (d : Fin m × Fin m →₀ ℕ) (i j : Fin m) (hij : i < j) :
    upperRootTargetExponent d i j (i, i) = d (i, i) + 1 := by
  simp only [upperRootTargetExponent, Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
    ne_eq, Prod.mk.injEq, ne_of_lt hij, and_true, not_false_eq_true, Finsupp.single_eq_of_ne,
    tsub_zero, Finsupp.single_eq_same]

theorem upperRootTargetExponent_below_add_one {m : ℕ}
    (d : Fin m × Fin m →₀ ℕ) (i j : Fin m)
    (hij : i < j) (hpositive : 0 < d (j, i)) :
    upperRootTargetExponent d i j (j, i) + 1 = d (j, i) := by
  simp only [upperRootTargetExponent, Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
    Finsupp.single_eq_same, ne_eq, Prod.mk.injEq, ne_of_gt hij, and_true, not_false_eq_true,
    Finsupp.single_eq_of_ne, add_zero, Nat.sub_add_cancel hpositive]

theorem upperRootTargetExponent_earlierRow_of_ne {m : ℕ}
    (d : Fin m × Fin m →₀ ℕ) (i j k : Fin m)
    (hij : i < j) (hki : k ≠ i) :
    upperRootTargetExponent d i j (i, k) = d (i, k) := by
  simp only [upperRootTargetExponent, Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
    ne_eq, Prod.mk.injEq, ne_of_lt hij, hki, and_self, not_false_eq_true, Finsupp.single_eq_of_ne,
    tsub_zero, and_false, add_zero]

theorem upperRootTargetExponent_eq_zero_of_earlierColumn {m : ℕ}
    (d : Fin m × Fin m →₀ ℕ) (i j k : Fin m)
    (hij : i < j) (hki : k < i)
    (hminimal : ∀ a b : Fin m, b < i → b < a → d (a, b) = 0) :
    upperRootTargetExponent d i j (i, k) = 0 := by
  rw [upperRootTargetExponent_earlierRow_of_ne d i j k hij
    (ne_of_lt hki)]
  exact hminimal i k hki hki

theorem coeff_eq_zero_of_minimalBelowColumn
    {m : ℕ} (p : SourceMatrix m)
    (d : Fin m × Fin m →₀ ℕ) (i j : Fin m)
    (hij : i < j) (hpositive : 0 < d (j, i))
    (hminimal : ∀ a b : Fin m, b < i → b < a → d (a, b) = 0)
    (hhighest : sourceRowRoot i j p = 0)
    (hinduction : ∀ e : Fin m × Fin m →₀ ℕ,
      belowDiagonalMass e < belowDiagonalMass d → p.coeff e = 0) :
    p.coeff d = 0 := by
  classical
  have hsum := upperRootTarget_coefficient_eq_zero p i j hij d hhighest
  have hcollapse :
      (∑ k : Fin m,
        if upperRootTargetExponent d i j (i, k) = 0 then 0
        else (upperRootTargetExponent d i j (j, k) + 1 : ℕ) •
          p.coeff (upperRootSourceExponent d i j k)) =
        (d (j, i) : ℕ) • p.coeff d := by
    rw [Finset.sum_eq_single i]
    · have hii : upperRootTargetExponent d i j (i, i) ≠ 0 := by
        rw [upperRootTargetExponent_diagonal d i j hij]
        omega
      simp only [hii, ↓reduceIte,
        upperRootSourceExponent_self d i j hij hpositive,
        upperRootTargetExponent_below_add_one d i j hij hpositive]
    · intro k _ hki
      rcases (lt_or_gt_of_ne hki) with hless | hgreater
      · rw [upperRootTargetExponent_eq_zero_of_earlierColumn
          d i j k hij hless hminimal]
        simp only [↓reduceIte]
      · by_cases htarget : upperRootTargetExponent d i j (i, k) = 0
        · simp only [htarget, ↓reduceIte]
        · have hlt := belowDiagonalMass_upperRootSource_lt
            d i j k hij hgreater hpositive
            (Nat.pos_of_ne_zero htarget)
          simp only [htarget, ↓reduceIte, hinduction _ hlt, nsmul_zero]
    · simp only [Finset.mem_univ, not_true_eq_false, nsmul_eq_mul, Nat.cast_add, Nat.cast_one,
        ite_eq_left_iff, mul_eq_zero, IsEmpty.forall_iff]
  rw [hcollapse] at hsum
  have hscalar : (d (j, i) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hpositive
  simpa only [nsmul_eq_mul, mul_eq_zero, hscalar, false_or] using hsum

theorem exists_minimalBelowColumn_of_mass_pos {m : ℕ}
    (d : Fin m × Fin m →₀ ℕ)
    (hmass : 0 < belowDiagonalMass d) :
    ∃ i j : Fin m, i < j ∧ 0 < d (j, i) ∧
      ∀ a b : Fin m, b < i → b < a → d (a, b) = 0 := by
  classical
  have hterm : ∃ z : Fin m × Fin m,
      0 < belowDiagonalWeight z * d z := by
    unfold belowDiagonalMass at hmass
    obtain ⟨z, _, hz⟩ := Finset.sum_pos_iff.mp hmass
    exact ⟨z, hz⟩
  obtain ⟨⟨j, i⟩, hterm⟩ := hterm
  have hweight : 0 < belowDiagonalWeight (j, i) := by
    apply Nat.pos_of_ne_zero
    intro hz
    simp only [hz, zero_mul, lt_self_iff_false] at hterm
  have hpositive : 0 < d (j, i) := by
    apply Nat.pos_of_ne_zero
    intro hz
    simp only [hz, mul_zero, lt_self_iff_false] at hterm
  have hij : i < j := by
    change i.val < j.val
    change 0 < j.val - i.val at hweight
    omega
  let P : ℕ → Prop := fun k =>
    ∃ a b : Fin m, b.val = k ∧ b < a ∧ 0 < d (a, b)
  have hex : ∃ k : ℕ, P k :=
    ⟨i.val, j, i, rfl, hij, hpositive⟩
  obtain ⟨j', i', hi', hij', hpositive'⟩ := Nat.find_spec hex
  refine ⟨i', j', hij', hpositive', ?_⟩
  intro a b hbi hba
  by_contra hzero
  have hpos : 0 < d (a, b) := Nat.pos_of_ne_zero hzero
  have hcandidate : P b.val := ⟨a, b, rfl, hba, hpos⟩
  have hleast : Nat.find hex ≤ b.val := Nat.find_min' hex hcandidate
  have hlt : b.val < i'.val := hbi
  omega

theorem eq_zero_of_upperRoots_of_massZero_coeff
    {m : ℕ} (p : SourceMatrix m)
    (hhighest : ∀ i j : Fin m, i < j → sourceRowRoot i j p = 0)
    (hzero : ∀ d : Fin m × Fin m →₀ ℕ,
      belowDiagonalMass d = 0 → p.coeff d = 0) :
    p = 0 := by
  have hcoeff : ∀ k : ℕ, ∀ d : Fin m × Fin m →₀ ℕ,
      belowDiagonalMass d = k → p.coeff d = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro d hd
        by_cases hk : k = 0
        · apply hzero d
          omega
        · have hmass : 0 < belowDiagonalMass d := by omega
          obtain ⟨i, j, hij, hpos, hminimal⟩ :=
            exists_minimalBelowColumn_of_mass_pos d hmass
          apply coeff_eq_zero_of_minimalBelowColumn
            p d i j hij hpos hminimal (hhighest i j hij)
          intro e he
          exact ih (belowDiagonalMass e) (by omega) e rfl
  apply MvPolynomial.ext
  intro d
  simpa only [MvPolynomial.coeff_zero] using hcoeff (belowDiagonalMass d) d rfl

theorem belowDiagonal_entry_eq_zero_of_mass_eq_zero {m : ℕ}
    (d : Fin m × Fin m →₀ ℕ)
    (hmass : belowDiagonalMass d = 0)
    (i j : Fin m) (hji : j < i) : d (i, j) = 0 := by
  classical
  have hle : belowDiagonalWeight (i, j) * d (i, j) ≤
      belowDiagonalMass d := by
    unfold belowDiagonalMass
    exact Finset.single_le_sum
      (f := fun z : Fin m × Fin m => belowDiagonalWeight z * d z)
      (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ (i, j))
  rw [hmass] at hle
  have hproduct : belowDiagonalWeight (i, j) * d (i, j) = 0 := by omega
  have hweight : belowDiagonalWeight (i, j) ≠ 0 := by
    change i.val - j.val ≠ 0
    have hvals : j.val < i.val := hji
    omega
  exact (mul_eq_zero.mp hproduct).resolve_left hweight

theorem sourceHighest_eq_zero_of_diagonalCoeff_eq_zero
    {r : ℕ} (lam : Fin (r + 1) → ℕ)
    (p : SourceMatrix (r + 1))
    (hrow : ∀ i : Fin (r + 1),
      sourceRowRoot i i p = (lam i : ℂ) • p)
    (hcolumn : ∀ i : Fin (r + 1),
      sourceColumnRoot i i p = (lam i : ℂ) • p)
    (hhighest : ∀ i j : Fin (r + 1), i < j →
      sourceRowRoot i j p = 0)
    (hdiagonal : p.coeff (sourceDiagonalExponent lam) = 0) :
    p = 0 := by
  apply eq_zero_of_upperRoots_of_massZero_coeff p hhighest
  intro d hmass
  by_cases hcoeff : p.coeff d = 0
  · exact hcoeff
  · have hrowDegree : ∀ i : Fin (r + 1),
        sourceRowDegree d i = lam i := by
        intro i
        exact sourceRowDegree_eq_of_coeff_ne_zero
          p lam hrow d hcoeff i
    have hcolumnDegree : ∀ i : Fin (r + 1),
        sourceColumnDegree d i = lam i := by
        intro i
        exact sourceColumnDegree_eq_of_coeff_ne_zero
          p lam hcolumn d hcoeff i
    have hbelow : ∀ i j : Fin (r + 1), j < i → d (i, j) = 0 := by
      intro i j hji
      exact belowDiagonal_entry_eq_zero_of_mass_eq_zero d hmass i j hji
    have hdiag := sourceExponent_eq_diagonal_of_upperTriangular
      lam d hrowDegree hcolumnDegree hbelow
    exact (hcoeff (hdiag.symm ▸ hdiagonal)).elim

theorem sourceHighest_eq_of_diagonalCoeff_eq
    {r : ℕ} (lam : Fin (r + 1) → ℕ)
    (p q : SourceMatrix (r + 1))
    (hrowp : ∀ i : Fin (r + 1),
      sourceRowRoot i i p = (lam i : ℂ) • p)
    (hcolumnp : ∀ i : Fin (r + 1),
      sourceColumnRoot i i p = (lam i : ℂ) • p)
    (hhighestp : ∀ i j : Fin (r + 1), i < j →
      sourceRowRoot i j p = 0)
    (hrowq : ∀ i : Fin (r + 1),
      sourceRowRoot i i q = (lam i : ℂ) • q)
    (hcolumnq : ∀ i : Fin (r + 1),
      sourceColumnRoot i i q = (lam i : ℂ) • q)
    (hhighestq : ∀ i j : Fin (r + 1), i < j →
      sourceRowRoot i j q = 0)
    (hdiagonal : p.coeff (sourceDiagonalExponent lam) =
      q.coeff (sourceDiagonalExponent lam)) :
    p = q := by
  apply sub_eq_zero.mp
  apply sourceHighest_eq_zero_of_diagonalCoeff_eq_zero lam (p - q)
  · intro i
    rw [map_sub, hrowp i, hrowq i, smul_sub]
  · intro i
    rw [map_sub, hcolumnp i, hcolumnq i, smul_sub]
  · intro i j hij
    rw [map_sub, hhighestp i j hij, hhighestq i j hij, sub_self]
  · simp only [MvPolynomial.coeff_sub, hdiagonal, sub_self]

theorem sourceHighestWeightPolynomial_diagonal_coeff_ne_zero
    {r : ℕ} (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam) :
    (sourceHighestWeightPolynomial (signatureExponent lam)).coeff
      (sourceDiagonalExponent lam) ≠ 0 := by
  intro hzero
  have hw := (mem_sourceHighestKernel lam
    (sourceHighestWeightPolynomial (signatureExponent lam))).mp
      (sourceHighestWeightPolynomial_mem_sourceHighestKernel lam hdom)
  have hpoly := sourceHighest_eq_zero_of_diagonalCoeff_eq_zero
    lam (sourceHighestWeightPolynomial (signatureExponent lam))
    hw.1 hw.2.1 hw.2.2.1 hzero
  have heval := eval_sourceHighestWeightPolynomial (signatureExponent lam)
  simp only [hpoly, map_zero, zero_ne_one] at heval

end HigherYoungAllRankSourceCoefficientStraightening

end

section


open scoped BigOperators

namespace HigherYoungAllRankIsotropicHighestMultiplicityOne

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors
open MetricCodes.Spherical.HigherHarmonicYoung.BideterminantHighestLine
open MetricCodes.Spherical.HigherHarmonicYoung.IsotropicAmbientHighestLine
open MetricCodes.Spherical.HigherYoungAllRankSourceHighestKernel
open MetricCodes.Spherical.HigherYoungAllRankSourceCoefficientStraightening
open MetricCodes.Spherical.HigherYoungAllRankSourceDiagonalBalance

theorem sourceMatrixHighestSubmodule_eq_span
    {r : ℕ} (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam) :
    sourceMatrixHighestSubmodule lam =
      Submodule.span ℂ
        {sourceHighestWeightPolynomial (signatureExponent lam)} := by
  apply le_antisymm
  · intro p hp
    obtain ⟨hrowp, hcolumnp, hhighestp⟩ :=
      (mem_sourceMatrixHighestSubmodule lam p).mp hp
    let w := sourceHighestWeightPolynomial (signatureExponent lam)
    have hw := (mem_sourceMatrixHighestSubmodule lam w).mp
      (sourceHighestWeightPolynomial_mem_sourceMatrixHighestSubmodule
        lam hdom)
    let d := sourceDiagonalExponent lam
    have hwd : w.coeff d ≠ 0 :=
      sourceHighestWeightPolynomial_diagonal_coeff_ne_zero lam hdom
    let c : ℂ := p.coeff d / w.coeff d
    have hrow : ∀ i : Fin (r + 1),
        sourceRowRoot i i (c • w) = (lam i : ℂ) • (c • w) := by
      intro i
      rw [(sourceRowRoot i i).map_smul, hw.1 i]
      module
    have hcolumn : ∀ i : Fin (r + 1),
        sourceColumnRoot i i (c • w) = (lam i : ℂ) • (c • w) := by
      intro i
      rw [(sourceColumnRoot i i).map_smul, hw.2.1 i]
      module
    have hupper : ∀ i j : Fin (r + 1), i < j →
        sourceRowRoot i j (c • w) = 0 := by
      intro i j hij
      rw [(sourceRowRoot i j).map_smul, hw.2.2 i j hij, smul_zero]
    have hdiag : p.coeff d = (c • w).coeff d := by
      rw [MvPolynomial.coeff_smul]
      change p.coeff d = c * w.coeff d
      dsimp [c]
      field_simp
    have heq := sourceHighest_eq_of_diagonalCoeff_eq lam p (c • w)
      hrowp hcolumnp hhighestp hrow hcolumn hupper hdiag
    rw [heq]
    exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self _)
  · rw [Submodule.span_le]
    exact Set.singleton_subset_iff.mpr
      (sourceHighestWeightPolynomial_mem_sourceMatrixHighestSubmodule
        lam hdom)

theorem finrank_sourceMatrixHighestSubmodule
    {r : ℕ} (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam) :
    Module.finrank ℂ (sourceMatrixHighestSubmodule lam) = 1 := by
  rw [sourceMatrixHighestSubmodule_eq_span lam hdom]
  exact finrank_span_singleton
    (IsotropicAmbientHighestLine.sourceHighestWeightPolynomial_ne_zero lam)

theorem ambientIsotropicHighestSubmodule_eq_determinant_span
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam) :
    ambientIsotropicHighestSubmodule h lam =
      Submodule.span ℂ
        {highestWeightPolynomial h (signatureExponent lam)} :=
  (ambientIsotropicHighestSubmodule_eq_span_iff_source_finrank
    h lam hdom).mpr (finrank_sourceMatrixHighestSubmodule lam hdom)

theorem finrank_ambientIsotropicHighestSubmodule
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam) :
    Module.finrank ℂ (ambientIsotropicHighestSubmodule h lam) = 1 := by
  rw [finrank_ambientIsotropicHighestSubmodule_eq_source]
  exact finrank_sourceMatrixHighestSubmodule lam hdom

theorem ambientIsotropicHighest_eq_diagonal_smul
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam)
    {f : MvPolynomial (Fin ((r + 1) * n)) ℂ}
    (hf : f ∈ ambientIsotropicHighestSubmodule h lam) :
    f = MvPolynomial.eval diagonalEvaluation f •
      highestWeightPolynomial h (signatureExponent lam) := by
  rw [ambientIsotropicHighestSubmodule_eq_determinant_span h lam hdom] at hf
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hf
  have heval : MvPolynomial.eval diagonalEvaluation f = c := by
    rw [← hc]
    simp only [Algebra.smul_def, MvPolynomial.algebraMap_eq, map_mul, MvPolynomial.eval_C,
      eval_highestWeightPolynomial h (signatureExponent lam), mul_one]
  rw [heval]
  exact hc.symm

end HigherYoungAllRankIsotropicHighestMultiplicityOne

end

section


open scoped BigOperators InnerProductSpace

namespace HigherYoungArbitraryRankGelfandTsetlinHighestEigenpair

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors
open MetricCodes.Spherical.HigherHarmonicYoung.IsotropicAmbientHighestLine
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankGelfandTsetlinHarmonicIsometry
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungAllRankIsotropicHighestMultiplicityOne
open MetricCodes.Spherical.HigherYoungCyclicHighestSchur
open MetricCodes.Spherical.HigherYoungTwoRowLieIrreducibility

/-- The young endomorphism highest polynomial used in the spherical-code argument. -/
def youngEndomorphismHighestPolynomial
    {r n : ℕ} (hn : 2 * (r + 1) ≤ n)
    (mu : Fin (r + 1) → ℕ) (hdom : Antitone mu)
    (A : HarmonicYoungSpace (n := n) mu →ₗ[ℝ]
      HarmonicYoungSpace (n := n) mu) :
    MvPolynomial (Fin ((r + 1) * n)) ℂ :=
  polynomialComplexification
      ((A (dominantHighestRealVector hn mu hdom) :
        HarmonicYoungSpace (n := n) mu) : PolynomialSpace r n) +
    Complex.I • polynomialComplexification
      ((A (dominantHighestImaginaryVector hn mu hdom) :
        HarmonicYoungSpace (n := n) mu) : PolynomialSpace r n)

theorem polynomialRealPart_youngEndomorphismHighestPolynomial
    {r n : ℕ} (hn : 2 * (r + 1) ≤ n)
    (mu : Fin (r + 1) → ℕ) (hdom : Antitone mu)
    (A : HarmonicYoungSpace (n := n) mu →ₗ[ℝ]
      HarmonicYoungSpace (n := n) mu) :
    polynomialRealPart
        (youngEndomorphismHighestPolynomial hn mu hdom A) =
      ((A (dominantHighestRealVector hn mu hdom) :
        HarmonicYoungSpace (n := n) mu) : PolynomialSpace r n) := by
  unfold youngEndomorphismHighestPolynomial
  rw [map_add, polynomialRealPart_complex_smul,
    polynomialRealPart_complexification,
    polynomialRealPart_complexification,
    polynomialImaginaryPart_complexification]
  simp only [Complex.I_re, zero_smul, Complex.I_im, smul_zero, sub_self, add_zero]

theorem polynomialImaginaryPart_youngEndomorphismHighestPolynomial
    {r n : ℕ} (hn : 2 * (r + 1) ≤ n)
    (mu : Fin (r + 1) → ℕ) (hdom : Antitone mu)
    (A : HarmonicYoungSpace (n := n) mu →ₗ[ℝ]
      HarmonicYoungSpace (n := n) mu) :
    polynomialImaginaryPart
        (youngEndomorphismHighestPolynomial hn mu hdom A) =
      ((A (dominantHighestImaginaryVector hn mu hdom) :
        HarmonicYoungSpace (n := n) mu) : PolynomialSpace r n) := by
  unfold youngEndomorphismHighestPolynomial
  rw [map_add, polynomialImaginaryPart_complex_smul,
    polynomialImaginaryPart_complexification,
    polynomialImaginaryPart_complexification,
    polynomialRealPart_complexification]
  simp only [Complex.I_re, smul_zero, Complex.I_im, one_smul, zero_add]

theorem youngEndomorphism_dominantHighest_eigenpair
    {r n : ℕ} (hn : 2 * (r + 1) ≤ n)
    (mu : Fin (r + 1) → ℕ) (hdom : Antitone mu)
    (A : HarmonicYoungSpace (n := n) mu →ₗ[ℝ]
      HarmonicYoungSpace (n := n) mu)
    (hhighest : youngEndomorphismHighestPolynomial hn mu hdom A ∈
      ambientIsotropicHighestSubmodule hn mu) :
    ∃ c : ℂ,
      A (dominantHighestRealVector hn mu hdom) =
          c.re • dominantHighestRealVector hn mu hdom -
            c.im • dominantHighestImaginaryVector hn mu hdom ∧
        A (dominantHighestImaginaryVector hn mu hdom) =
          c.im • dominantHighestRealVector hn mu hdom +
            c.re • dominantHighestImaginaryVector hn mu hdom := by
  let f := youngEndomorphismHighestPolynomial hn mu hdom A
  let c := MvPolynomial.eval diagonalEvaluation f
  have hline : f = c • highestWeightPolynomial hn (signatureExponent mu) :=
    ambientIsotropicHighest_eq_diagonal_smul hn mu hdom hhighest
  refine ⟨c, ?_, ?_⟩
  · apply Subtype.ext
    have hreal := congrArg polynomialRealPart hline
    rw [polynomialRealPart_youngEndomorphismHighestPolynomial,
      polynomialRealPart_complex_smul] at hreal
    exact hreal
  · apply Subtype.ext
    have himag := congrArg polynomialImaginaryPart hline
    rw [polynomialImaginaryPart_youngEndomorphismHighestPolynomial,
      polynomialImaginaryPart_complex_smul] at himag
    exact himag.trans (add_comm _ _)

end HigherYoungArbitraryRankGelfandTsetlinHighestEigenpair

end

section


open scoped BigOperators InnerProductSpace TensorProduct

namespace HigherHarmonicYoung.ArbitraryRowRaiseLowerTensorTrace

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowDownstreamActualChannels
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInternalRowLowerGram
open MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors
open MetricCodes.Spherical.HigherYoungPenultimateRowProjectedLower

/-- The arbitrary row raise tensor gram scalar used in the spherical-code argument. -/
def arbitraryRowRaiseTensorGramScalar
    {r n : ℕ} (high : Fin (r + 1) → ℕ)
    (row : Fin (r + 1)) : ℝ :=
  internalRowLowerGramScalar high row *
      (Module.finrank ℝ (HarmonicYoungSpace (n := n) high) : ℝ) /
    (Module.finrank ℝ
      (HarmonicYoungSpace (n := n)
        (loweredInternalYoungWeight high row)) : ℝ)

theorem arbitraryRowRaiseTensorGramScalar_pos
    {r n : ℕ} (high : Fin (r + 1) → ℕ)
    (row : Fin (r + 1))
    (hn : 2 * (r + 1) ≤ n)
    (hrow : 0 < high row)
    (hdomhigh : Antitone high)
    (hdomlow : Antitone (loweredInternalYoungWeight high row))
    (hstrict : ∀ j : Fin (r + 1),
      j.val = row.val + 1 → high j < high row) :
    0 < arbitraryRowRaiseTensorGramScalar (n := n) high row := by
  unfold arbitraryRowRaiseTensorGramScalar
  apply div_pos
  · apply mul_pos
    · exact internalRowLowerGramScalar_pos high row hrow hstrict
    · exact_mod_cast finrank_harmonicYoung_pos_of_antitone
        hn high hdomhigh
  · exact_mod_cast finrank_harmonicYoung_pos_of_antitone
      hn (loweredInternalYoungWeight high row) hdomlow

end HigherHarmonicYoung.ArbitraryRowRaiseLowerTensorTrace

end

section


open scoped BigOperators

namespace HigherYoungAmbientCartanIsotropicEigenvalues

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors

theorem pderiv_even_conjugateIsotropicVariable {r n : ℕ}
    (h : 2 * (r + 1) ≤ n)
    (a p i j : Fin (r + 1)) :
    MvPolynomial.pderiv (variableIndex a (evenCoordinate h p))
        (conjugateIsotropicVariable h i j) =
      if a = i ∧ p = j then 1 else 0 := by
  classical
  simp [conjugateIsotropicVariable, Pi.single_apply, DeterminantVectors.variableIndex_eq_iff,
    evenCoordinate_inj,
    evenCoordinate_ne_oddCoordinate, eq_comm]

theorem pderiv_odd_conjugateIsotropicVariable {r n : ℕ}
    (h : 2 * (r + 1) ≤ n)
    (a p i j : Fin (r + 1)) :
    MvPolynomial.pderiv (variableIndex a (oddCoordinate h p))
        (conjugateIsotropicVariable h i j) =
      if a = i ∧ p = j then -MvPolynomial.C Complex.I else 0 := by
  classical
  simp only [conjugateIsotropicVariable, map_sub, MvPolynomial.pderiv_X, ne_eq,
    DeterminantVectors.variableIndex_eq_iff, eq_comm, evenCoordinate_ne_oddCoordinate, and_false,
    not_false_eq_true, Pi.single_eq_of_ne, Derivation.leibniz, Pi.single_apply, oddCoordinate_inj,
    smul_eq_mul, mul_ite, mul_one, mul_zero, MvPolynomial.derivation_C, add_zero, zero_sub]
  split_ifs <;> simp

theorem ambientCartan_conjugateIsotropicVariable {r n : ℕ}
    (h : 2 * (r + 1) ≤ n)
    (p i j : Fin (r + 1)) :
    ambientCartan h p (conjugateIsotropicVariable h i j) =
      if p = j then (-2 : ℂ) • conjugateIsotropicVariable h i j else 0 := by
  classical
  change ambientPositiveRoot h p p
    (conjugateIsotropicVariable h i j) = _
  rw [ambientPositiveRoot_apply]
  simp_rw [pderiv_even_conjugateIsotropicVariable,
    pderiv_odd_conjugateIsotropicVariable]
  by_cases hpj : p = j
  · subst j
    simp only [and_true, ↓reduceIte]
    have hterm (a : Fin (r + 1)) :
        (isotropicVariable h a p *
          ((if a = i then 1 else 0) -
            MvPolynomial.C Complex.I *
              (if a = i then -MvPolynomial.C Complex.I else 0)) -
          conjugateIsotropicVariable h a p *
          ((if a = i then 1 else 0) +
            MvPolynomial.C Complex.I *
              (if a = i then -MvPolynomial.C Complex.I else 0))) =
          if a = i then (-2 : ℂ) • conjugateIsotropicVariable h i p
          else 0 := by
      by_cases hai : a = i
      · subst a
        simp only [↓reduceIte, mul_neg, ← map_mul, Complex.I_mul_I, MvPolynomial.C_neg,
          MvPolynomial.C_1, neg_neg, sub_self, mul_zero, zero_sub, Algebra.smul_def,
          MvPolynomial.algebraMap_eq, neg_mul, neg_inj]
        rw [map_ofNat (MvPolynomial.C :
          ℂ →+* MvPolynomial (Fin ((r + 1) * n)) ℂ) 2]
        ring
      · simp only [hai, ↓reduceIte, mul_zero, sub_self, add_zero]
    simp_rw [hterm]
    simp only [neg_smul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  · simp only [hpj, and_false, ↓reduceIte, mul_zero, sub_self, add_zero, Finset.sum_const_zero]

theorem ambientCartan_X_unused {r n : ℕ}
    (h : 2 * (r + 1) ≤ n)
    (p a : Fin (r + 1)) (t : Fin n)
    (ht : 2 * (r + 1) ≤ t.val) :
    ambientCartan h p
      (MvPolynomial.X (variableIndex a t) :
        MvPolynomial (Fin ((r + 1) * n)) ℂ) = 0 := by
  classical
  change ambientPositiveRoot h p p
    (MvPolynomial.X (variableIndex a t)) = 0
  rw [ambientPositiveRoot_apply]
  apply Finset.sum_eq_zero
  intro b _
  have he : evenCoordinate h p ≠ t := by
    intro heq
    have hv := congrArg Fin.val heq
    have hp := p.isLt
    simp only [evenCoordinate_val] at hv
    omega
  have ho : oddCoordinate h p ≠ t := by
    intro heq
    have hv := congrArg Fin.val heq
    have hp := p.isLt
    simp only [oddCoordinate_val] at hv
    omega
  simp only [MvPolynomial.pderiv_X, ne_eq, DeterminantVectors.variableIndex_eq_iff, Ne.symm he,
    and_false, not_false_eq_true, Pi.single_eq_of_ne, Ne.symm ho, mul_zero, sub_self, add_zero]

/-- The total ambient cartan used in the spherical-code argument. -/
def totalAmbientCartan {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) :
    Derivation ℂ (MvPolynomial (Fin ((r + 1) * n)) ℂ)
      (MvPolynomial (Fin ((r + 1) * n)) ℂ) :=
  ∑ p : Fin (r + 1), ambientCartan h p

@[simp] theorem totalAmbientCartan_apply {r n : ℕ}
    (h : 2 * (r + 1) ≤ n)
    (f : MvPolynomial (Fin ((r + 1) * n)) ℂ) :
    totalAmbientCartan h f = ∑ p : Fin (r + 1), ambientCartan h p f := by
  change (Derivation.coeFnAddMonoidHom
    (∑ p : Fin (r + 1), ambientCartan h p)) f = _
  rw [map_sum, Finset.sum_apply]
  rfl

theorem totalAmbientCartan_isotropicVariable {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (i j : Fin (r + 1)) :
    totalAmbientCartan h (isotropicVariable h i j) =
      (2 : ℂ) • isotropicVariable h i j := by
  rw [totalAmbientCartan_apply]
  simp_rw [ambientCartan_isotropicVariable]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

theorem totalAmbientCartan_conjugateIsotropicVariable {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (i j : Fin (r + 1)) :
    totalAmbientCartan h (conjugateIsotropicVariable h i j) =
      (-2 : ℂ) • conjugateIsotropicVariable h i j := by
  rw [totalAmbientCartan_apply]
  simp_rw [ambientCartan_conjugateIsotropicVariable]
  simp only [neg_smul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

theorem totalAmbientCartan_X_unused {r n : ℕ}
    (h : 2 * (r + 1) ≤ n)
    (a : Fin (r + 1)) (t : Fin n)
    (ht : 2 * (r + 1) ≤ t.val) :
    totalAmbientCartan h
      (MvPolynomial.X (variableIndex a t) :
        MvPolynomial (Fin ((r + 1) * n)) ℂ) = 0 := by
  rw [totalAmbientCartan_apply]
  simp only [ambientCartan_X_unused h _ a t ht, Finset.sum_const_zero]

end HigherYoungAmbientCartanIsotropicEigenvalues

end

section


open scoped BigOperators

namespace HigherYoungAmbientRootRotationDecomposition

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherYoungMixedGapLieGram
open MetricCodes.Spherical.HigherYoungTwoRowLieIrreducibility

theorem complexAmbientRotation_apply {r n : ℕ} (a b : Fin n)
    (f : MvPolynomial (Fin ((r + 1) * n)) ℂ) :
    complexAmbientRotation (r := r) a b f =
      ∑ i : Fin (r + 1),
        (MvPolynomial.X (variableIndex i a) *
          MvPolynomial.pderiv (variableIndex i b) f -
          MvPolynomial.X (variableIndex i b) *
            MvPolynomial.pderiv (variableIndex i a) f) := by
  change complexAmbientCoordinateDerivation (r := r) a b f -
      complexAmbientCoordinateDerivation (r := r) b a f = _
  rw [complexAmbientCoordinateDerivation_apply,
    complexAmbientCoordinateDerivation_apply, Finset.sum_sub_distrib]

theorem complexAmbientRotation_youngComplexPolynomialSpan_mem
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (W : Submodule ℝ (HarmonicYoungSpace (n := n) lam))
    (hW : IsRotationInvariant (youngRotationFamily lam) W)
    (a b : Fin n)
    (f : MvPolynomial (Fin ((r + 1) * n)) ℂ)
    (hf : f ∈ youngComplexPolynomialSpan lam W) :
    complexAmbientRotation (r := r) a b f ∈
      youngComplexPolynomialSpan lam W := by
  apply complexSpan_invariant
    (polynomialComplexification (r := r) (n := n))
    (fun ab : Fin n × Fin n =>
      (ambientRotation (r := r) ab.1 ab.2).toLinearMap)
    (fun ab : Fin n × Fin n =>
      (complexAmbientRotation (r := r) ab.1 ab.2).toLinearMap)
    (fun ab p => complexAmbientRotation_complexification ab.1 ab.2 p)
    (youngRealPolynomialImage lam W) ?_ (a, b) f hf
  rintro ⟨c, d⟩ p ⟨q, hq, hqp⟩
  subst p
  refine ⟨youngAmbientRotation lam c d q, hW (c, d) q hq, ?_⟩
  rfl

theorem ambientPositiveRoot_eq_complexRotations {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (p q : Fin (r + 1)) :
    ambientPositiveRoot h p q =
      complexAmbientRotation (r := r) (evenCoordinate h p) (evenCoordinate h q) +
        complexAmbientRotation (r := r) (oddCoordinate h p) (oddCoordinate h q) +
        Complex.I • complexAmbientRotation (r := r)
          (oddCoordinate h p) (evenCoordinate h q) +
        Complex.I • complexAmbientRotation (r := r)
          (oddCoordinate h q) (evenCoordinate h p) := by
  apply Derivation.ext
  intro f
  change ambientPositiveRoot h p q f =
    complexAmbientRotation (r := r) (evenCoordinate h p) (evenCoordinate h q) f +
      complexAmbientRotation (r := r) (oddCoordinate h p) (oddCoordinate h q) f +
      Complex.I • complexAmbientRotation (r := r)
        (oddCoordinate h p) (evenCoordinate h q) f +
      Complex.I • complexAmbientRotation (r := r)
        (oddCoordinate h q) (evenCoordinate h p) f
  simp only [ambientPositiveRoot_apply,
    complexAmbientRotation_apply, isotropicVariable,
    conjugateIsotropicVariable, Algebra.smul_def]
  simp_rw [Finset.mul_sum]
  repeat rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  simp only [MvPolynomial.algebraMap_eq]
  have hI : (MvPolynomial.C Complex.I :
      MvPolynomial (Fin ((r + 1) * n)) ℂ) ^ 2 = -1 := by
    rw [pow_two, ← map_mul, Complex.I_mul_I, map_neg, map_one]
  ring_nf
  rw [hI]
  ring

theorem ambientPositiveRoot_youngComplexPolynomialSpan_mem
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (lam : Fin (r + 1) → ℕ)
    (W : Submodule ℝ (HarmonicYoungSpace (n := n) lam))
    (hW : IsRotationInvariant (youngRotationFamily lam) W)
    (p q : Fin (r + 1))
    (f : MvPolynomial (Fin ((r + 1) * n)) ℂ)
    (hf : f ∈ youngComplexPolynomialSpan lam W) :
    ambientPositiveRoot h p q f ∈ youngComplexPolynomialSpan lam W := by
  rw [ambientPositiveRoot_eq_complexRotations]
  change
    complexAmbientRotation (r := r)
        (evenCoordinate h p) (evenCoordinate h q) f +
      complexAmbientRotation (r := r)
        (oddCoordinate h p) (oddCoordinate h q) f +
      Complex.I • complexAmbientRotation (r := r)
        (oddCoordinate h p) (evenCoordinate h q) f +
      Complex.I • complexAmbientRotation (r := r)
        (oddCoordinate h q) (evenCoordinate h p) f ∈
      youngComplexPolynomialSpan lam W
  exact (youngComplexPolynomialSpan lam W).add_mem
    ((youngComplexPolynomialSpan lam W).add_mem
      ((youngComplexPolynomialSpan lam W).add_mem
        (complexAmbientRotation_youngComplexPolynomialSpan_mem
          lam W hW _ _ f hf)
        (complexAmbientRotation_youngComplexPolynomialSpan_mem
          lam W hW _ _ f hf))
      ((youngComplexPolynomialSpan lam W).smul_mem Complex.I
        (complexAmbientRotation_youngComplexPolynomialSpan_mem
          lam W hW _ _ f hf)))
    ((youngComplexPolynomialSpan lam W).smul_mem Complex.I
      (complexAmbientRotation_youngComplexPolynomialSpan_mem
        lam W hW _ _ f hf))

theorem ambientSumPositiveRoot_apply {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (p q : Fin (r + 1))
    (f : MvPolynomial (Fin ((r + 1) * n)) ℂ) :
    ambientSumPositiveRoot h p q f =
      ∑ a : Fin (r + 1),
        (isotropicVariable h a p *
          (MvPolynomial.pderiv (variableIndex a (evenCoordinate h q)) f +
            MvPolynomial.C Complex.I *
              MvPolynomial.pderiv (variableIndex a (oddCoordinate h q)) f) -
        isotropicVariable h a q *
          (MvPolynomial.pderiv (variableIndex a (evenCoordinate h p)) f +
            MvPolynomial.C Complex.I *
              MvPolynomial.pderiv (variableIndex a (oddCoordinate h p)) f)) := by
  change (Derivation.coeFnAddMonoidHom
    (∑ a : Fin (r + 1),
      (isotropicVariable h a p • antiholomorphicDerivative h a q -
        isotropicVariable h a q • antiholomorphicDerivative h a p))) f = _
  rw [map_sum, Finset.sum_apply]
  rfl

theorem ambientSumPositiveRoot_eq_complexRotations {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (p q : Fin (r + 1)) :
    ambientSumPositiveRoot h p q =
      complexAmbientRotation (r := r) (evenCoordinate h p) (evenCoordinate h q) -
        complexAmbientRotation (r := r) (oddCoordinate h p) (oddCoordinate h q) +
        Complex.I • complexAmbientRotation (r := r)
          (evenCoordinate h p) (oddCoordinate h q) +
        Complex.I • complexAmbientRotation (r := r)
          (oddCoordinate h p) (evenCoordinate h q) := by
  apply Derivation.ext
  intro f
  change ambientSumPositiveRoot h p q f =
    complexAmbientRotation (r := r) (evenCoordinate h p) (evenCoordinate h q) f -
      complexAmbientRotation (r := r) (oddCoordinate h p) (oddCoordinate h q) f +
      Complex.I • complexAmbientRotation (r := r)
        (evenCoordinate h p) (oddCoordinate h q) f +
      Complex.I • complexAmbientRotation (r := r)
        (oddCoordinate h p) (evenCoordinate h q) f
  simp only [ambientSumPositiveRoot_apply,
    complexAmbientRotation_apply, isotropicVariable, Algebra.smul_def]
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  repeat rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  simp only [MvPolynomial.algebraMap_eq]
  have hI : (MvPolynomial.C Complex.I :
      MvPolynomial (Fin ((r + 1) * n)) ℂ) ^ 2 = -1 := by
    rw [pow_two, ← map_mul, Complex.I_mul_I, map_neg, map_one]
  ring_nf
  rw [hI]
  ring

theorem ambientSumPositiveRoot_youngComplexPolynomialSpan_mem
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (lam : Fin (r + 1) → ℕ)
    (W : Submodule ℝ (HarmonicYoungSpace (n := n) lam))
    (hW : IsRotationInvariant (youngRotationFamily lam) W)
    (p q : Fin (r + 1))
    (f : MvPolynomial (Fin ((r + 1) * n)) ℂ)
    (hf : f ∈ youngComplexPolynomialSpan lam W) :
    ambientSumPositiveRoot h p q f ∈ youngComplexPolynomialSpan lam W := by
  rw [ambientSumPositiveRoot_eq_complexRotations]
  change
    complexAmbientRotation (r := r)
        (evenCoordinate h p) (evenCoordinate h q) f -
      complexAmbientRotation (r := r)
        (oddCoordinate h p) (oddCoordinate h q) f +
      Complex.I • complexAmbientRotation (r := r)
        (evenCoordinate h p) (oddCoordinate h q) f +
      Complex.I • complexAmbientRotation (r := r)
        (oddCoordinate h p) (evenCoordinate h q) f ∈
      youngComplexPolynomialSpan lam W
  exact (youngComplexPolynomialSpan lam W).add_mem
    ((youngComplexPolynomialSpan lam W).add_mem
      ((youngComplexPolynomialSpan lam W).sub_mem
        (complexAmbientRotation_youngComplexPolynomialSpan_mem
          lam W hW _ _ f hf)
        (complexAmbientRotation_youngComplexPolynomialSpan_mem
          lam W hW _ _ f hf))
      ((youngComplexPolynomialSpan lam W).smul_mem Complex.I
        (complexAmbientRotation_youngComplexPolynomialSpan_mem
          lam W hW _ _ f hf)))
    ((youngComplexPolynomialSpan lam W).smul_mem Complex.I
      (complexAmbientRotation_youngComplexPolynomialSpan_mem
        lam W hW _ _ f hf))

theorem ambientShortPositiveRoot_apply {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (p : Fin (r + 1)) (t : Fin n)
    (f : MvPolynomial (Fin ((r + 1) * n)) ℂ) :
    ambientShortPositiveRoot h p t f =
      ∑ a : Fin (r + 1),
        (isotropicVariable h a p * MvPolynomial.pderiv (variableIndex a t) f -
          MvPolynomial.X (variableIndex a t) *
            (MvPolynomial.pderiv (variableIndex a (evenCoordinate h p)) f +
              MvPolynomial.C Complex.I *
                MvPolynomial.pderiv (variableIndex a (oddCoordinate h p)) f)) := by
  change (Derivation.coeFnAddMonoidHom
    (∑ a : Fin (r + 1),
      (isotropicVariable h a p •
        (MvPolynomial.pderiv (variableIndex a t) :
          Derivation ℂ (MvPolynomial (Fin ((r + 1) * n)) ℂ)
            (MvPolynomial (Fin ((r + 1) * n)) ℂ)) -
        MvPolynomial.X (variableIndex a t) •
          antiholomorphicDerivative h a p))) f = _
  rw [map_sum, Finset.sum_apply]
  rfl

theorem ambientShortPositiveRoot_eq_complexRotations {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (p : Fin (r + 1)) (t : Fin n) :
    ambientShortPositiveRoot h p t =
      complexAmbientRotation (r := r) (evenCoordinate h p) t +
        Complex.I • complexAmbientRotation (r := r) (oddCoordinate h p) t := by
  apply Derivation.ext
  intro f
  change ambientShortPositiveRoot h p t f =
    complexAmbientRotation (r := r) (evenCoordinate h p) t f +
      Complex.I • complexAmbientRotation (r := r) (oddCoordinate h p) t f
  simp only [ambientShortPositiveRoot_apply,
    complexAmbientRotation_apply, isotropicVariable, Algebra.smul_def]
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  simp only [MvPolynomial.algebraMap_eq]
  ring

theorem ambientShortPositiveRoot_youngComplexPolynomialSpan_mem
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (lam : Fin (r + 1) → ℕ)
    (W : Submodule ℝ (HarmonicYoungSpace (n := n) lam))
    (hW : IsRotationInvariant (youngRotationFamily lam) W)
    (p : Fin (r + 1)) (t : Fin n)
    (f : MvPolynomial (Fin ((r + 1) * n)) ℂ)
    (hf : f ∈ youngComplexPolynomialSpan lam W) :
    ambientShortPositiveRoot h p t f ∈ youngComplexPolynomialSpan lam W := by
  rw [ambientShortPositiveRoot_eq_complexRotations]
  change
    complexAmbientRotation (r := r) (evenCoordinate h p) t f +
      Complex.I • complexAmbientRotation (r := r) (oddCoordinate h p) t f ∈
      youngComplexPolynomialSpan lam W
  exact (youngComplexPolynomialSpan lam W).add_mem
    (complexAmbientRotation_youngComplexPolynomialSpan_mem
      lam W hW _ _ f hf)
    ((youngComplexPolynomialSpan lam W).smul_mem Complex.I
      (complexAmbientRotation_youngComplexPolynomialSpan_mem
        lam W hW _ _ f hf))

theorem ambientCartan_youngComplexPolynomialSpan_mem
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (lam : Fin (r + 1) → ℕ)
    (W : Submodule ℝ (HarmonicYoungSpace (n := n) lam))
    (hW : IsRotationInvariant (youngRotationFamily lam) W)
    (p : Fin (r + 1))
    (f : MvPolynomial (Fin ((r + 1) * n)) ℂ)
    (hf : f ∈ youngComplexPolynomialSpan lam W) :
    ambientCartan h p f ∈ youngComplexPolynomialSpan lam W :=
  ambientPositiveRoot_youngComplexPolynomialSpan_mem
    h lam W hW p p f hf

end HigherYoungAmbientRootRotationDecomposition

end

namespace HigherYoungAmbientRootNilpotence

section


open scoped BigOperators
open MetricCodes.Spherical.HigherYoungTwoRowLieIrreducibility

private def weightedPolynomialFiltration {σ : Type*} (weight : σ → ℕ) (k : ℕ) :
    Submodule ℂ (MvPolynomial σ ℂ) :=
  MvPolynomial.restrictSupport ℂ
    {d : σ →₀ ℕ | Finsupp.weight weight d ≤ k}

theorem mem_weightedPolynomialFiltration {σ : Type*}
    (weight : σ → ℕ) (k : ℕ) (p : MvPolynomial σ ℂ) :
    p ∈ weightedPolynomialFiltration weight k ↔
      ∀ d : σ →₀ ℕ, p.coeff d ≠ 0 → Finsupp.weight weight d ≤ k := by
  change (∀ d ∈ p.support, d ∈ ({d : σ →₀ ℕ | Finsupp.weight weight d ≤ k} : Set (σ →₀ ℕ))) ↔ _
  simp only [MvPolynomial.mem_support_iff, ne_eq, Set.mem_ofPred_eq]

theorem monomial_mem_weightedPolynomialFiltration {σ : Type*}
    (weight : σ → ℕ) (d : σ →₀ ℕ) (c : ℂ) :
    MvPolynomial.monomial d c ∈
      weightedPolynomialFiltration weight (Finsupp.weight weight d) := by
  classical
  rw [mem_weightedPolynomialFiltration]
  intro e he
  rw [MvPolynomial.coeff_monomial] at he
  split_ifs at he with hed
  · simp [hed]
  · exact (he rfl).elim

private def strictWeightedPolynomialFiltration {σ : Type*}
    (weight : σ → ℕ) (k : ℕ) : Submodule ℂ (MvPolynomial σ ℂ) :=
  MvPolynomial.restrictSupport ℂ
    {d : σ →₀ ℕ | Finsupp.weight weight d + 1 ≤ k}

theorem mem_strictWeightedPolynomialFiltration {σ : Type*}
    (weight : σ → ℕ) (k : ℕ) (p : MvPolynomial σ ℂ) :
    p ∈ strictWeightedPolynomialFiltration weight k ↔
      ∀ d : σ →₀ ℕ, p.coeff d ≠ 0 →
        Finsupp.weight weight d + 1 ≤ k := by
  change (∀ d ∈ p.support,
    d ∈ ({d : σ →₀ ℕ | Finsupp.weight weight d + 1 ≤ k} :
      Set (σ →₀ ℕ))) ↔ _
  simp only [MvPolynomial.mem_support_iff, ne_eq, Order.add_one_le_iff, Set.mem_ofPred_eq]

theorem strictWeightedPolynomialFiltration_mono {σ : Type*}
    (weight : σ → ℕ) {k l : ℕ} (h : k ≤ l) :
    strictWeightedPolynomialFiltration weight k ≤
      strictWeightedPolynomialFiltration weight l := by
  intro p hp
  rw [mem_strictWeightedPolynomialFiltration] at hp ⊢
  exact fun d hd => (hp d hd).trans h

theorem mul_mem_strictWeightedPolynomialFiltration {σ : Type*}
    (weight : σ → ℕ) {k l : ℕ} {p q : MvPolynomial σ ℂ}
    (hp : p ∈ weightedPolynomialFiltration weight k)
    (hq : q ∈ strictWeightedPolynomialFiltration weight l) :
    p * q ∈ strictWeightedPolynomialFiltration weight (k + l) := by
  classical
  rw [mem_weightedPolynomialFiltration] at hp
  rw [mem_strictWeightedPolynomialFiltration] at hq ⊢
  intro d hd
  have hs : d ∈ (p * q).support := MvPolynomial.mem_support_iff.mpr hd
  have hsum := MvPolynomial.support_mul p q hs
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.mem_add.mp hsum
  subst d
  rw [map_add]
  have hpa := hp a (MvPolynomial.mem_support_iff.mp ha)
  have hqb := hq b (MvPolynomial.mem_support_iff.mp hb)
  omega

theorem derivation_mem_strictWeightedPolynomialFiltration
    {σ : Type*} (weight : σ → ℕ)
    (D : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ))
    (hD : ∀ i : σ, ∀ e : σ →₀ ℕ,
      (D (MvPolynomial.X i)).coeff e ≠ 0 →
        Finsupp.weight weight e + 1 ≤ weight i)
    {k : ℕ} {p : MvPolynomial σ ℂ}
    (hp : p ∈ weightedPolynomialFiltration weight k) :
    D p ∈ strictWeightedPolynomialFiltration weight k := by
  classical
  have hrepr : D = MvPolynomial.mkDerivation ℂ
      (fun i : σ => D (MvPolynomial.X i)) := by
    apply MvPolynomial.derivation_ext
    intro i
    simp only [MvPolynomial.mkDerivation_X]
  rw [p.as_sum, map_sum]
  apply Submodule.sum_mem
  intro d hd
  rw [hrepr, MvPolynomial.mkDerivation_monomial]
  apply Submodule.smul_mem
  change (∑ i ∈ d.support,
    MvPolynomial.monomial (d - Finsupp.single i 1)
      (d i : ℂ) • D (MvPolynomial.X i)) ∈
      strictWeightedPolynomialFiltration weight k
  apply Submodule.sum_mem
  intro i hi
  have hi0 : d i ≠ 0 := Finsupp.mem_support_iff.mp hi
  have hweight := Finsupp.weight_sub_single_add (w := weight) hi0
  have hsource : Finsupp.weight weight d ≤ k :=
    (mem_weightedPolynomialFiltration weight k p).mp hp d
      (MvPolynomial.mem_support_iff.mp hd)
  have hgen : D (MvPolynomial.X i) ∈
      strictWeightedPolynomialFiltration weight (weight i) :=
    (mem_strictWeightedPolynomialFiltration weight (weight i) _).mpr
      (hD i)
  have hmono := monomial_mem_weightedPolynomialFiltration
    weight (d - Finsupp.single i 1) (d i : ℂ)
  have hproduct := mul_mem_strictWeightedPolynomialFiltration
    weight hmono hgen
  have hbound : Finsupp.weight weight
      (d - Finsupp.single i 1) + weight i ≤ k := by
    omega
  apply strictWeightedPolynomialFiltration_mono weight hbound hproduct

theorem derivation_eq_zero_of_mem_weightedPolynomialFiltration_zero
    {σ : Type*} (weight : σ → ℕ)
    (D : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ))
    (hD : ∀ i : σ, ∀ e : σ →₀ ℕ,
      (D (MvPolynomial.X i)).coeff e ≠ 0 →
        Finsupp.weight weight e + 1 ≤ weight i)
    {p : MvPolynomial σ ℂ}
    (hp : p ∈ weightedPolynomialFiltration weight 0) : D p = 0 := by
  have hstrict := derivation_mem_strictWeightedPolynomialFiltration
    weight D hD hp
  apply MvPolynomial.ext
  intro d
  by_contra hd
  have h := (mem_strictWeightedPolynomialFiltration
    weight 0 (D p)).mp hstrict d hd
  omega

theorem strictWeightedPolynomialFiltration_le_weighted_pred
    {σ : Type*} (weight : σ → ℕ) (k : ℕ) :
    strictWeightedPolynomialFiltration weight (k + 1) ≤
      weightedPolynomialFiltration weight k := by
  intro p hp
  rw [mem_strictWeightedPolynomialFiltration] at hp
  rw [mem_weightedPolynomialFiltration]
  intro d hd
  have h := hp d hd
  omega

theorem derivation_mem_weightedPolynomialFiltration_succ
    {σ : Type*} (weight : σ → ℕ)
    (D : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ))
    (hD : ∀ i : σ, ∀ e : σ →₀ ℕ,
      (D (MvPolynomial.X i)).coeff e ≠ 0 →
        Finsupp.weight weight e + 1 ≤ weight i)
    {k : ℕ} {p : MvPolynomial σ ℂ}
    (hp : p ∈ weightedPolynomialFiltration weight (k + 1)) :
    D p ∈ weightedPolynomialFiltration weight k :=
  strictWeightedPolynomialFiltration_le_weighted_pred weight k
    (derivation_mem_strictWeightedPolynomialFiltration weight D hD hp)

theorem triangular_rootOperatorWord_eq_zero_of_length_gt
    {σ J : Type*} (weight : σ → ℕ)
    (D : J → Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ))
    (hD : ∀ (j : J) (i : σ) (e : σ →₀ ℕ),
      ((D j) (MvPolynomial.X i)).coeff e ≠ 0 →
        Finsupp.weight weight e + 1 ≤ weight i)
    (word : List J) {k : ℕ} {p : MvPolynomial σ ℂ}
    (hp : p ∈ weightedPolynomialFiltration weight k)
    (hlen : k < word.length) :
    rootOperatorWord (fun j => (D j).toLinearMap) word p = 0 := by
  induction word generalizing p k with
  | nil => simp only [List.length_nil, not_lt_zero] at hlen
  | cons j word ih =>
      cases k with
      | zero =>
          have hz := derivation_eq_zero_of_mem_weightedPolynomialFiltration_zero
            weight (D j) (hD j) hp
          simp only [rootOperatorWord_cons_apply, Derivation.coeFn_coe, hz, map_zero]
      | succ k =>
          change rootOperatorWord (fun j => (D j).toLinearMap) word
            (D j p) = 0
          apply ih
          · exact derivation_mem_weightedPolynomialFiltration_succ
              weight (D j) (hD j) hp
          · simp only [List.length_cons] at hlen
            omega

theorem finsupp_weight_le_degree_mul
    {σ : Type*} (weight : σ → ℕ) (bound : ℕ)
    (hweight : ∀ i : σ, weight i ≤ bound)
    (d : σ →₀ ℕ) :
    Finsupp.weight weight d ≤ d.degree * bound := by
  classical
  rw [Finsupp.weight_apply, Finsupp.degree_apply, Finsupp.sum]
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  simpa only [smul_eq_mul] using Nat.mul_le_mul_left (d i) (hweight i)

theorem homogeneous_mem_weightedPolynomialFiltration
    {σ : Type*} (weight : σ → ℕ) (bound m : ℕ)
    (hweight : ∀ i : σ, weight i ≤ bound)
    {p : MvPolynomial σ ℂ} (hp : p.IsHomogeneous m) :
    p ∈ weightedPolynomialFiltration weight (m * bound) := by
  rw [mem_weightedPolynomialFiltration]
  intro d hd
  have hdeg : d.degree = m := by
    rw [Finsupp.degree_eq_weight_one]
    exact hp hd
  simpa only [ge_iff_le, hdeg] using finsupp_weight_le_degree_mul weight bound hweight d

theorem triangular_rootOperatorWord_eq_zero_of_isHomogeneous
    {σ J : Type*} (weight : σ → ℕ) (bound : ℕ)
    (hweight : ∀ i : σ, weight i ≤ bound)
    (D : J → Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ))
    (hD : ∀ (j : J) (i : σ) (e : σ →₀ ℕ),
      ((D j) (MvPolynomial.X i)).coeff e ≠ 0 →
        Finsupp.weight weight e + 1 ≤ weight i)
    {m : ℕ} {p : MvPolynomial σ ℂ}
    (hp : p.IsHomogeneous m)
    (word : List J) (hlen : m * bound < word.length) :
    rootOperatorWord (fun j => (D j).toLinearMap) word p = 0 :=
  triangular_rootOperatorWord_eq_zero_of_length_gt weight D hD word
    (homogeneous_mem_weightedPolynomialFiltration weight bound m hweight hp) hlen

end

section


open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors

/-- The ambient pair index used in the spherical-code argument. -/
def ambientPairIndex {r n : ℕ}
    (a : Fin n) (ha : a.val < 2 * (r + 1)) : Fin (r + 1) :=
  ⟨a.val / 2, by omega⟩

@[simp] theorem ambientPairIndex_even {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (a : Fin (r + 1)) :
    ambientPairIndex (evenCoordinate h a)
      (by have := a.isLt; simp only [evenCoordinate, Order.lt_two_iff, zero_le,
                            mul_lt_mul_iff_right₀, Order.lt_add_one_iff, ge_iff_le]; omega) = a
                              := by
  apply Fin.ext
  simp only [ambientPairIndex, evenCoordinate, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    mul_div_cancel_left₀, Fin.eta]

@[simp] theorem ambientPairIndex_odd {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (a : Fin (r + 1)) :
    ambientPairIndex (oddCoordinate h a)
      (by have := a.isLt; simp only [oddCoordinate, gt_iff_lt]; omega) = a := by
  apply Fin.ext
  simp only [ambientPairIndex, oddCoordinate]
  omega

/-- The isotropic coordinate generator used in the spherical-code argument. -/
def isotropicCoordinateGenerator {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (v : Fin ((r + 1) * n)) :
    MvPolynomial (Fin ((r + 1) * n)) ℂ :=
  let a := ((finProdFinEquiv (m := r + 1) (n := n)).symm v).1
  let t := ((finProdFinEquiv (m := r + 1) (n := n)).symm v).2
  if ht : t.val < 2 * (r + 1) then
    if _he : t.val % 2 = 0 then
      isotropicVariable h a (ambientPairIndex t ht)
    else
      conjugateIsotropicVariable h a (ambientPairIndex t ht)
  else MvPolynomial.X v

@[simp] theorem isotropicCoordinateGenerator_even {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (a p : Fin (r + 1)) :
    isotropicCoordinateGenerator h
      (variableIndex a (evenCoordinate h p)) =
      isotropicVariable h a p := by
  have hcut : (evenCoordinate h p).val < 2 * (r + 1) := by
    simp only [evenCoordinate, Order.lt_two_iff, zero_le, mul_lt_mul_iff_right₀,
      Order.lt_add_one_iff]
    have := p.isLt
    omega
  simp only [isotropicCoordinateGenerator, variableIndex,
    Equiv.symm_apply_apply, dite_eq_left hcut]
  simp only [evenCoordinate_val, Nat.mul_mod_right, ↓reduceDIte, ambientPairIndex_even]

@[simp] theorem isotropicCoordinateGenerator_odd {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (a p : Fin (r + 1)) :
    isotropicCoordinateGenerator h
      (variableIndex a (oddCoordinate h p)) =
      conjugateIsotropicVariable h a p := by
  have hcut : (oddCoordinate h p).val < 2 * (r + 1) := by
    simp only [oddCoordinate]
    have := p.isLt
    omega
  simp only [isotropicCoordinateGenerator, variableIndex,
    Equiv.symm_apply_apply, dite_eq_left hcut]
  simp only [oddCoordinate_val, Nat.mul_add_mod_self_left, Nat.mod_succ, one_ne_zero, ↓reduceDIte,
    ambientPairIndex_odd]

@[simp] theorem isotropicCoordinateGenerator_unused {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (a : Fin (r + 1)) (t : Fin n)
    (ht : 2 * (r + 1) ≤ t.val) :
    isotropicCoordinateGenerator h (variableIndex a t) =
      MvPolynomial.X (variableIndex a t) := by
  simp only [isotropicCoordinateGenerator, variableIndex, Equiv.symm_apply_apply, not_lt_of_ge ht,
    ↓reduceDIte]

private def inverseIsotropicCoordinateGenerator {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (v : Fin ((r + 1) * n)) :
    MvPolynomial (Fin ((r + 1) * n)) ℂ :=
  let a := ((finProdFinEquiv (m := r + 1) (n := n)).symm v).1
  let t := ((finProdFinEquiv (m := r + 1) (n := n)).symm v).2
  if ht : t.val < 2 * (r + 1) then
    let p := ambientPairIndex t ht
    if _he : t.val % 2 = 0 then
      ((2 : ℂ)⁻¹) •
        (MvPolynomial.X (variableIndex a (evenCoordinate h p)) +
          MvPolynomial.X (variableIndex a (oddCoordinate h p)))
    else
      (-(Complex.I / 2)) •
        MvPolynomial.X (variableIndex a (evenCoordinate h p)) +
      (Complex.I / 2) •
        MvPolynomial.X (variableIndex a (oddCoordinate h p))
  else MvPolynomial.X v

@[simp] theorem inverseIsotropicCoordinateGenerator_even {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (a p : Fin (r + 1)) :
    inverseIsotropicCoordinateGenerator h
      (variableIndex a (evenCoordinate h p)) =
      ((2 : ℂ)⁻¹) •
        (MvPolynomial.X (variableIndex a (evenCoordinate h p)) +
          MvPolynomial.X (variableIndex a (oddCoordinate h p))) := by
  have hcut : (evenCoordinate h p).val < 2 * (r + 1) := by
    simp only [evenCoordinate, Order.lt_two_iff, zero_le, mul_lt_mul_iff_right₀,
      Order.lt_add_one_iff]
    have := p.isLt
    omega
  simp only [inverseIsotropicCoordinateGenerator, variableIndex,
    Equiv.symm_apply_apply, dite_eq_left hcut]
  simp only [evenCoordinate_val, Nat.mul_mod_right, ↓reduceDIte, ambientPairIndex_even, smul_add]

@[simp] theorem inverseIsotropicCoordinateGenerator_odd {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (a p : Fin (r + 1)) :
    inverseIsotropicCoordinateGenerator h
      (variableIndex a (oddCoordinate h p)) =
      (-(Complex.I / 2)) •
        MvPolynomial.X (variableIndex a (evenCoordinate h p)) +
      (Complex.I / 2) •
        MvPolynomial.X (variableIndex a (oddCoordinate h p)) := by
  have hcut : (oddCoordinate h p).val < 2 * (r + 1) := by
    simp only [oddCoordinate]
    have := p.isLt
    omega
  simp only [inverseIsotropicCoordinateGenerator, variableIndex,
    Equiv.symm_apply_apply, dite_eq_left hcut]
  simp only [oddCoordinate_val, Nat.mul_add_mod_self_left, Nat.mod_succ, one_ne_zero, ↓reduceDIte,
    ambientPairIndex_odd, neg_smul]

@[simp] theorem inverseIsotropicCoordinateGenerator_unused {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (a : Fin (r + 1)) (t : Fin n)
    (ht : 2 * (r + 1) ≤ t.val) :
    inverseIsotropicCoordinateGenerator h (variableIndex a t) =
      MvPolynomial.X (variableIndex a t) := by
  simp only [inverseIsotropicCoordinateGenerator, variableIndex, Equiv.symm_apply_apply,
    not_lt_of_ge ht, ↓reduceDIte]

private def isotropicCoordinateHom {r n : ℕ} (h : 2 * (r + 1) ≤ n) :
    MvPolynomial (Fin ((r + 1) * n)) ℂ →ₐ[ℂ]
      MvPolynomial (Fin ((r + 1) * n)) ℂ :=
  MvPolynomial.aeval (isotropicCoordinateGenerator h)

private def inverseIsotropicCoordinateHom {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) :
    MvPolynomial (Fin ((r + 1) * n)) ℂ →ₐ[ℂ]
      MvPolynomial (Fin ((r + 1) * n)) ℂ :=
  MvPolynomial.aeval (inverseIsotropicCoordinateGenerator h)

@[simp] theorem isotropicCoordinateHom_X {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (v : Fin ((r + 1) * n)) :
    isotropicCoordinateHom h (MvPolynomial.X v) =
      isotropicCoordinateGenerator h v := by
  simp only [isotropicCoordinateHom, MvPolynomial.aeval_eq_bind₁, MvPolynomial.bind₁_X_right]

@[simp] theorem inverseIsotropicCoordinateHom_X {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (v : Fin ((r + 1) * n)) :
    inverseIsotropicCoordinateHom h (MvPolynomial.X v) =
      inverseIsotropicCoordinateGenerator h v := by
  simp only [inverseIsotropicCoordinateHom, MvPolynomial.aeval_eq_bind₁, MvPolynomial.bind₁_X_right]

lemma isotropic_inverse_even_identity
    {V : Type*} [AddCommGroup V] [Module ℂ V] (x y : V) :
    ((2 : ℂ)⁻¹) • ((x + Complex.I • y) + (x - Complex.I • y)) = x := by
  module

lemma isotropic_inverse_odd_identity
    {V : Type*} [AddCommGroup V] [Module ℂ V] (x y : V) :
    (-(Complex.I / 2)) • (x + Complex.I • y) +
      (Complex.I / 2) • (x - Complex.I • y) = y := by
  rw [smul_add, smul_sub, smul_smul, smul_smul]
  have hI : (-(Complex.I / 2)) * Complex.I = (2 : ℂ)⁻¹ := by
    rw [neg_mul, div_mul_eq_mul_div, Complex.I_mul_I]
    norm_num
  have hI2 : (Complex.I / 2) * Complex.I = -((2 : ℂ)⁻¹) := by
    rw [div_mul_eq_mul_div, Complex.I_mul_I]
    norm_num
  rw [hI, hI2]
  module

lemma isotropic_forward_even_identity
    {V : Type*} [AddCommGroup V] [Module ℂ V] (x y : V) :
    ((2 : ℂ)⁻¹) • (x + y) +
      Complex.I • ((-(Complex.I / 2)) • x + (Complex.I / 2) • y) = x := by
  rw [smul_add, smul_add, smul_smul, smul_smul]
  have hI : Complex.I * (-(Complex.I / 2)) = (2 : ℂ)⁻¹ := by
    calc
      Complex.I * (-(Complex.I / 2)) = -(Complex.I * Complex.I) / 2 := by ring
      _ = (2 : ℂ)⁻¹ := by rw [Complex.I_mul_I]; norm_num
  have hI2 : Complex.I * (Complex.I / 2) = -((2 : ℂ)⁻¹) := by
    calc
      Complex.I * (Complex.I / 2) = (Complex.I * Complex.I) / 2 := by ring
      _ = -((2 : ℂ)⁻¹) := by rw [Complex.I_mul_I]; norm_num
  rw [hI, hI2]
  module

lemma isotropic_forward_odd_identity
    {V : Type*} [AddCommGroup V] [Module ℂ V] (x y : V) :
    ((2 : ℂ)⁻¹) • (x + y) -
      Complex.I • ((-(Complex.I / 2)) • x + (Complex.I / 2) • y) = y := by
  rw [smul_add, smul_add, smul_smul, smul_smul]
  have hI : Complex.I * (-(Complex.I / 2)) = (2 : ℂ)⁻¹ := by
    calc
      Complex.I * (-(Complex.I / 2)) = -(Complex.I * Complex.I) / 2 := by ring
      _ = (2 : ℂ)⁻¹ := by rw [Complex.I_mul_I]; norm_num
  have hI2 : Complex.I * (Complex.I / 2) = -((2 : ℂ)⁻¹) := by
    calc
      Complex.I * (Complex.I / 2) = (Complex.I * Complex.I) / 2 := by ring
      _ = -((2 : ℂ)⁻¹) := by rw [Complex.I_mul_I]; norm_num
  rw [hI, hI2]
  module

theorem isotropicCoordinateHom_comp_inverse {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) :
    (isotropicCoordinateHom h).comp
      (inverseIsotropicCoordinateHom h) =
        AlgHom.id ℂ (MvPolynomial (Fin ((r + 1) * n)) ℂ) := by
  apply MvPolynomial.algHom_ext
  intro v
  obtain ⟨⟨a, t⟩, rfl⟩ :=
    (finProdFinEquiv (m := r + 1) (n := n)).surjective v
  simp only [AlgHom.comp_apply, AlgHom.id_apply,
    inverseIsotropicCoordinateHom_X]
  change isotropicCoordinateHom h
      (inverseIsotropicCoordinateGenerator h (variableIndex a t)) =
      MvPolynomial.X (variableIndex a t)
  by_cases ht : t.val < 2 * (r + 1)
  · let p := ambientPairIndex t ht
    by_cases he : t.val % 2 = 0
    · have hpair : evenCoordinate h p = t := by
        apply Fin.ext
        change 2 * (t.val / 2) = t.val
        omega
      rw [← hpair, inverseIsotropicCoordinateGenerator_even]
      simp only [map_smul, map_add, isotropicCoordinateHom_X,
        isotropicCoordinateGenerator_even, isotropicCoordinateGenerator_odd]
      simpa only [isotropicVariable, MvPolynomial.C_mul', conjugateIsotropicVariable,
        add_add_sub_cancel,
        smul_add] using
        (isotropic_inverse_even_identity (V := MvPolynomial (Fin ((r + 1) * n)) ℂ)
          (MvPolynomial.X (variableIndex a (evenCoordinate h p))) (MvPolynomial.X (variableIndex
            a (oddCoordinate h p))))
    · have hpair : oddCoordinate h p = t := by
        apply Fin.ext
        change 2 * (t.val / 2) + 1 = t.val
        have hrem : t.val % 2 = 1 := by omega
        omega
      rw [← hpair, inverseIsotropicCoordinateGenerator_odd]
      simp only [map_add, map_smul, isotropicCoordinateHom_X,
        isotropicCoordinateGenerator_even, isotropicCoordinateGenerator_odd]
      simpa only [isotropicVariable, MvPolynomial.C_mul', smul_add, neg_smul,
        conjugateIsotropicVariable] using
        (isotropic_inverse_odd_identity (V := MvPolynomial (Fin ((r + 1) * n)) ℂ)
          (MvPolynomial.X (variableIndex a (evenCoordinate h p))) (MvPolynomial.X (variableIndex
            a (oddCoordinate h p))))
  · have htge : 2 * (r + 1) ≤ t.val := Nat.le_of_not_gt ht
    rw [inverseIsotropicCoordinateGenerator_unused h a t htge,
      isotropicCoordinateHom_X,
      isotropicCoordinateGenerator_unused h a t htge]

theorem inverseIsotropicCoordinateHom_comp {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) :
    (inverseIsotropicCoordinateHom h).comp
      (isotropicCoordinateHom h) =
        AlgHom.id ℂ (MvPolynomial (Fin ((r + 1) * n)) ℂ) := by
  apply MvPolynomial.algHom_ext
  intro v
  obtain ⟨⟨a, t⟩, rfl⟩ :=
    (finProdFinEquiv (m := r + 1) (n := n)).surjective v
  simp only [AlgHom.comp_apply, AlgHom.id_apply,
    isotropicCoordinateHom_X]
  change inverseIsotropicCoordinateHom h
      (isotropicCoordinateGenerator h (variableIndex a t)) =
      MvPolynomial.X (variableIndex a t)
  by_cases ht : t.val < 2 * (r + 1)
  · let p := ambientPairIndex t ht
    by_cases he : t.val % 2 = 0
    · have hpair : evenCoordinate h p = t := by
        apply Fin.ext
        change 2 * (t.val / 2) = t.val
        omega
      rw [← hpair, isotropicCoordinateGenerator_even]
      simp only [isotropicVariable, MvPolynomial.C_mul', map_add,
        map_smul, inverseIsotropicCoordinateHom_X,
        inverseIsotropicCoordinateGenerator_even,
        inverseIsotropicCoordinateGenerator_odd]
      exact isotropic_forward_even_identity
        (MvPolynomial.X (variableIndex a (evenCoordinate h p)))
        (MvPolynomial.X (variableIndex a (oddCoordinate h p)))
    · have hpair : oddCoordinate h p = t := by
        apply Fin.ext
        change 2 * (t.val / 2) + 1 = t.val
        have hrem : t.val % 2 = 1 := by omega
        omega
      rw [← hpair, isotropicCoordinateGenerator_odd]
      simp only [conjugateIsotropicVariable, MvPolynomial.C_mul', map_sub,
        map_smul, inverseIsotropicCoordinateHom_X,
        inverseIsotropicCoordinateGenerator_even,
        inverseIsotropicCoordinateGenerator_odd]
      exact isotropic_forward_odd_identity
        (MvPolynomial.X (variableIndex a (evenCoordinate h p)))
        (MvPolynomial.X (variableIndex a (oddCoordinate h p)))
  · have htge : 2 * (r + 1) ≤ t.val := Nat.le_of_not_gt ht
    rw [isotropicCoordinateGenerator_unused h a t htge,
      inverseIsotropicCoordinateHom_X,
      inverseIsotropicCoordinateGenerator_unused h a t htge]

/-- The isotropic coordinate equiv used in the spherical-code argument. -/
def isotropicCoordinateEquiv {r n : ℕ} (h : 2 * (r + 1) ≤ n) :
    MvPolynomial (Fin ((r + 1) * n)) ℂ ≃ₐ[ℂ]
      MvPolynomial (Fin ((r + 1) * n)) ℂ :=
  AlgEquiv.ofAlgHom (isotropicCoordinateHom h)
    (inverseIsotropicCoordinateHom h)
    (isotropicCoordinateHom_comp_inverse h)
    (inverseIsotropicCoordinateHom_comp h)

@[simp] theorem isotropicCoordinateEquiv_X {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (v : Fin ((r + 1) * n)) :
    isotropicCoordinateEquiv h (MvPolynomial.X v) =
      isotropicCoordinateGenerator h v :=
  isotropicCoordinateHom_X h v

theorem isotropicCoordinateEquiv_X_even {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (a p : Fin (r + 1)) :
    isotropicCoordinateEquiv h
      (MvPolynomial.X (variableIndex a (evenCoordinate h p))) =
      isotropicVariable h a p := by
  simp only [isotropicCoordinateEquiv_X, isotropicCoordinateGenerator_even]

theorem isotropicCoordinateEquiv_X_odd {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (a p : Fin (r + 1)) :
    isotropicCoordinateEquiv h
      (MvPolynomial.X (variableIndex a (oddCoordinate h p))) =
      conjugateIsotropicVariable h a p := by
  simp only [isotropicCoordinateEquiv_X, isotropicCoordinateGenerator_odd]

theorem isotropicCoordinateEquiv_X_unused {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (a : Fin (r + 1)) (t : Fin n)
    (ht : 2 * (r + 1) ≤ t.val) :
    isotropicCoordinateEquiv h (MvPolynomial.X (variableIndex a t)) =
      MvPolynomial.X (variableIndex a t) := by
  simp only [isotropicCoordinateEquiv_X, isotropicCoordinateGenerator_unused h a t ht]

end

end HigherYoungAmbientRootNilpotence

section


open scoped BigOperators

namespace HigherYoungAmbientPositiveRootGeneratorAction

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors
open MetricCodes.Spherical.HigherYoungAmbientCartanIsotropicEigenvalues
open MetricCodes.Spherical.HigherYoungAmbientRootRotationDecomposition

theorem holomorphicDerivative_conjugateIsotropicVariable
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (a p i j : Fin (r + 1)) :
    MvPolynomial.pderiv (variableIndex a (evenCoordinate h p))
        (conjugateIsotropicVariable h i j) -
      MvPolynomial.C Complex.I *
        MvPolynomial.pderiv (variableIndex a (oddCoordinate h p))
          (conjugateIsotropicVariable h i j) = 0 := by
  rw [pderiv_even_conjugateIsotropicVariable,
    pderiv_odd_conjugateIsotropicVariable]
  split_ifs with hp
  · simp only [mul_neg, ← map_mul, Complex.I_mul_I, MvPolynomial.C_neg, MvPolynomial.C_1, neg_neg,
      sub_self]
  · simp only [mul_zero, sub_self]

theorem antiholomorphicDerivative_conjugateIsotropicVariable
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (a p i j : Fin (r + 1)) :
    antiholomorphicDerivative h a p
        (conjugateIsotropicVariable h i j) =
      if a = i ∧ p = j then 2 else 0 := by
  change MvPolynomial.pderiv (variableIndex a (evenCoordinate h p))
      (conjugateIsotropicVariable h i j) +
    MvPolynomial.C Complex.I *
      MvPolynomial.pderiv (variableIndex a (oddCoordinate h p))
        (conjugateIsotropicVariable h i j) = _
  rw [pderiv_even_conjugateIsotropicVariable,
    pderiv_odd_conjugateIsotropicVariable]
  split_ifs with hp
  · simp only [mul_neg, ← map_mul, Complex.I_mul_I, MvPolynomial.C_neg, MvPolynomial.C_1, neg_neg]
    norm_num
  · simp only [mul_zero, add_zero]

theorem ambientPositiveRoot_conjugateIsotropicVariable
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (p q i j : Fin (r + 1)) :
    ambientPositiveRoot h p q (conjugateIsotropicVariable h i j) =
      if p = j then (-2 : ℂ) • conjugateIsotropicVariable h i q else 0 := by
  classical
  rw [ambientPositiveRoot_apply]
  have hfirst (a : Fin (r + 1)) :
      MvPolynomial.pderiv (variableIndex a (evenCoordinate h q))
          (conjugateIsotropicVariable h i j) -
        MvPolynomial.C Complex.I *
          MvPolynomial.pderiv (variableIndex a (oddCoordinate h q))
            (conjugateIsotropicVariable h i j) = 0 :=
    holomorphicDerivative_conjugateIsotropicVariable h a q i j
  have hsecond (a : Fin (r + 1)) :
      MvPolynomial.pderiv (variableIndex a (evenCoordinate h p))
          (conjugateIsotropicVariable h i j) +
        MvPolynomial.C Complex.I *
          MvPolynomial.pderiv (variableIndex a (oddCoordinate h p))
            (conjugateIsotropicVariable h i j) =
        if a = i ∧ p = j then 2 else 0 :=
    antiholomorphicDerivative_conjugateIsotropicVariable h a p i j
  simp_rw [hfirst, hsecond]
  by_cases hp : p = j
  · subst j
    simp only [mul_zero, and_true, mul_ite, zero_sub, Finset.sum_neg_distrib, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte, Algebra.smul_def, MvPolynomial.algebraMap_eq, MvPolynomial.C_neg,
      neg_mul, neg_inj]
    rw [map_ofNat (MvPolynomial.C :
      ℂ →+* MvPolynomial (Fin ((r + 1) * n)) ℂ) 2]
    ring
  · simp only [mul_zero, hp, and_false, ↓reduceIte, sub_self, Finset.sum_const_zero]

theorem ambientSumPositiveRoot_conjugateIsotropicVariable
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (p q i j : Fin (r + 1)) :
    ambientSumPositiveRoot h p q (conjugateIsotropicVariable h i j) =
      (if q = j then (2 : ℂ) • isotropicVariable h i p else 0) -
        (if p = j then (2 : ℂ) • isotropicVariable h i q else 0) := by
  classical
  rw [ambientSumPositiveRoot_apply]
  have hterm (a k : Fin (r + 1)) :
      MvPolynomial.pderiv (variableIndex a (evenCoordinate h k))
          (conjugateIsotropicVariable h i j) +
        MvPolynomial.C Complex.I *
          MvPolynomial.pderiv (variableIndex a (oddCoordinate h k))
            (conjugateIsotropicVariable h i j) =
        if a = i ∧ k = j then 2 else 0 :=
    antiholomorphicDerivative_conjugateIsotropicVariable h a k i j
  simp_rw [hterm]
  by_cases hp : p = j <;> by_cases hq : q = j <;>
    simp only [hp, hq, and_true, and_false, mul_ite, mul_zero,
      sub_self, Finset.sum_const_zero, ↓reduceIte, Algebra.smul_def,
      MvPolynomial.algebraMap_eq, zero_sub, Finset.sum_neg_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, neg_inj, sub_zero]
  all_goals
    rw [map_ofNat (MvPolynomial.C :
      ℂ →+* MvPolynomial (Fin ((r + 1) * n)) ℂ) 2]
    ring

end HigherYoungAmbientPositiveRootGeneratorAction

namespace HigherYoungAmbientPositiveRootUnusedGeneratorAction

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors
open MetricCodes.Spherical.HigherYoungAmbientCartanIsotropicEigenvalues
open MetricCodes.Spherical.HigherYoungAmbientRootRotationDecomposition
open MetricCodes.Spherical.HigherYoungAmbientPositiveRootGeneratorAction

theorem pderiv_even_X_unused {r n : ℕ}
    (h : 2 * (r + 1) ≤ n)
    (a p i : Fin (r + 1)) (t : Fin n)
    (ht : 2 * (r + 1) ≤ t.val) :
    MvPolynomial.pderiv (variableIndex a (evenCoordinate h p))
      (MvPolynomial.X (variableIndex i t) :
        MvPolynomial (Fin ((r + 1) * n)) ℂ) = 0 := by
  have he : evenCoordinate h p ≠ t := by
    intro heq
    have hv := congrArg Fin.val heq
    simp only [evenCoordinate_val] at hv
    have hp := p.isLt
    omega
  simp only [MvPolynomial.pderiv_X, ne_eq, DeterminantVectors.variableIndex_eq_iff, he, and_false,
    not_false_eq_true, Pi.single_eq_of_ne']

theorem pderiv_odd_X_unused {r n : ℕ}
    (h : 2 * (r + 1) ≤ n)
    (a p i : Fin (r + 1)) (t : Fin n)
    (ht : 2 * (r + 1) ≤ t.val) :
    MvPolynomial.pderiv (variableIndex a (oddCoordinate h p))
      (MvPolynomial.X (variableIndex i t) :
        MvPolynomial (Fin ((r + 1) * n)) ℂ) = 0 := by
  have ho : oddCoordinate h p ≠ t := by
    intro heq
    have hv := congrArg Fin.val heq
    simp only [oddCoordinate_val] at hv
    have hp := p.isLt
    omega
  simp only [MvPolynomial.pderiv_X, ne_eq, DeterminantVectors.variableIndex_eq_iff, ho, and_false,
    not_false_eq_true, Pi.single_eq_of_ne']

theorem pderiv_unused_conjugateIsotropicVariable {r n : ℕ}
    (h : 2 * (r + 1) ≤ n)
    (a i j : Fin (r + 1)) (t : Fin n)
    (ht : 2 * (r + 1) ≤ t.val) :
    MvPolynomial.pderiv (variableIndex a t)
      (conjugateIsotropicVariable h i j) = 0 := by
  have he : evenCoordinate h j ≠ t := by
    intro heq
    have hv := congrArg Fin.val heq
    simp only [evenCoordinate_val] at hv
    have hj := j.isLt
    omega
  have ho : oddCoordinate h j ≠ t := by
    intro heq
    have hv := congrArg Fin.val heq
    simp only [oddCoordinate_val] at hv
    have hj := j.isLt
    omega
  simp only [conjugateIsotropicVariable, map_sub, MvPolynomial.pderiv_X, ne_eq,
    DeterminantVectors.variableIndex_eq_iff, Ne.symm he, and_false, not_false_eq_true,
    Pi.single_eq_of_ne', Derivation.leibniz, Ne.symm ho, smul_eq_mul, mul_zero,
    MvPolynomial.derivation_C, add_zero, sub_self]

theorem ambientPositiveRoot_X_unused {r n : ℕ}
    (h : 2 * (r + 1) ≤ n)
    (p q i : Fin (r + 1)) (t : Fin n)
    (ht : 2 * (r + 1) ≤ t.val) :
    ambientPositiveRoot h p q
      (MvPolynomial.X (variableIndex i t) :
        MvPolynomial (Fin ((r + 1) * n)) ℂ) = 0 := by
  rw [ambientPositiveRoot_apply]
  simp_rw [pderiv_even_X_unused h _ _ i t ht,
    pderiv_odd_X_unused h _ _ i t ht]
  simp only [mul_zero, sub_self, add_zero, Finset.sum_const_zero]

theorem ambientSumPositiveRoot_X_unused {r n : ℕ}
    (h : 2 * (r + 1) ≤ n)
    (p q i : Fin (r + 1)) (t : Fin n)
    (ht : 2 * (r + 1) ≤ t.val) :
    ambientSumPositiveRoot h p q
      (MvPolynomial.X (variableIndex i t) :
        MvPolynomial (Fin ((r + 1) * n)) ℂ) = 0 := by
  rw [ambientSumPositiveRoot_apply]
  simp_rw [pderiv_even_X_unused h _ _ i t ht,
    pderiv_odd_X_unused h _ _ i t ht]
  simp only [mul_zero, add_zero, sub_self, Finset.sum_const_zero]

theorem ambientShortPositiveRoot_conjugateIsotropicVariable
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (p i j : Fin (r + 1)) (t : Fin n)
    (ht : 2 * (r + 1) ≤ t.val) :
    ambientShortPositiveRoot h p t
      (conjugateIsotropicVariable h i j) =
      if p = j then (-2 : ℂ) •
        (MvPolynomial.X (variableIndex i t) :
          MvPolynomial (Fin ((r + 1) * n)) ℂ)
      else 0 := by
  classical
  rw [ambientShortPositiveRoot_apply]
  have hplus (a : Fin (r + 1)) :
      MvPolynomial.pderiv (variableIndex a (evenCoordinate h p))
          (conjugateIsotropicVariable h i j) +
        MvPolynomial.C Complex.I *
          MvPolynomial.pderiv (variableIndex a (oddCoordinate h p))
            (conjugateIsotropicVariable h i j) =
        if a = i ∧ p = j then 2 else 0 :=
    antiholomorphicDerivative_conjugateIsotropicVariable h a p i j
  simp_rw [pderiv_unused_conjugateIsotropicVariable h _ i j t ht,
    hplus]
  by_cases hp : p = j
  · subst j
    simp only [mul_zero, and_true, mul_ite, zero_sub, Finset.sum_neg_distrib, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte, Algebra.smul_def, MvPolynomial.algebraMap_eq, MvPolynomial.C_neg,
      neg_mul, neg_inj]
    rw [map_ofNat (MvPolynomial.C :
      ℂ →+* MvPolynomial (Fin ((r + 1) * n)) ℂ) 2]
    ring
  · simp only [mul_zero, hp, and_false, ↓reduceIte, sub_self, Finset.sum_const_zero]

theorem ambientShortPositiveRoot_X_unused {r n : ℕ}
    (h : 2 * (r + 1) ≤ n)
    (p i : Fin (r + 1)) (t u : Fin n)
    (hu : 2 * (r + 1) ≤ u.val) :
    ambientShortPositiveRoot h p t
      (MvPolynomial.X (variableIndex i u) :
        MvPolynomial (Fin ((r + 1) * n)) ℂ) =
      if t = u then isotropicVariable h i p else 0 := by
  classical
  rw [ambientShortPositiveRoot_apply]
  simp_rw [pderiv_even_X_unused h _ p i u hu,
    pderiv_odd_X_unused h _ p i u hu]
  have hderiv (a : Fin (r + 1)) :
      MvPolynomial.pderiv (variableIndex a t)
        (MvPolynomial.X (variableIndex i u) :
          MvPolynomial (Fin ((r + 1) * n)) ℂ) =
        if a = i ∧ t = u then 1 else 0 := by
    simp only [MvPolynomial.pderiv_X, Pi.single_apply, DeterminantVectors.variableIndex_eq_iff,
      eq_comm]
  simp_rw [hderiv]
  by_cases htu : t = u <;> simp [htu]

end HigherYoungAmbientPositiveRootUnusedGeneratorAction

namespace HigherYoungIsotropicCoordinateHomogeneity

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors
open MetricCodes.Spherical.HigherYoungAmbientRootNilpotence

theorem inverseIsotropicCoordinateGenerator_isHomogeneous
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (v : Fin ((r + 1) * n)) :
    (inverseIsotropicCoordinateGenerator h v).IsHomogeneous 1 := by
  have hsmul (c : ℂ)
      (p : MvPolynomial (Fin ((r + 1) * n)) ℂ)
      (hp : p.IsHomogeneous 1) : (c • p).IsHomogeneous 1 := by
    rw [MvPolynomial.smul_eq_C_mul]
    exact hp.C_mul c
  unfold inverseIsotropicCoordinateGenerator
  dsimp only
  split_ifs
  · exact hsmul _ _
      ((MvPolynomial.isHomogeneous_X _ _).add
        (MvPolynomial.isHomogeneous_X _ _))
  · exact (hsmul _ _ (MvPolynomial.isHomogeneous_X _ _)).add
      (hsmul _ _ (MvPolynomial.isHomogeneous_X _ _))
  · exact MvPolynomial.isHomogeneous_X _ _

theorem isotropicCoordinateEquiv_symm_isHomogeneous
    {r n m : ℕ} (h : 2 * (r + 1) ≤ n)
    (p : MvPolynomial (Fin ((r + 1) * n)) ℂ)
    (hp : p.IsHomogeneous m) :
    ((isotropicCoordinateEquiv h).symm p).IsHomogeneous m := by
  change
    (MvPolynomial.aeval (inverseIsotropicCoordinateGenerator h) p).IsHomogeneous m
  simpa only [MvPolynomial.aeval_eq_bind₁, one_mul] using
    hp.aeval (inverseIsotropicCoordinateGenerator h)
      (inverseIsotropicCoordinateGenerator_isHomogeneous h)

end HigherYoungIsotropicCoordinateHomogeneity

end

end Spherical

end MetricCodes

end MetricCodesNoncomputable
