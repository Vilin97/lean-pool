/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyAnnularSparseTransfer
import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyPositiveSuffixThreeShift
import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceySparseUnion
import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyThreeShiftTreeInterface

/-!
# Native positive suffix closure from the one-node good estimate

This module isolates the last analytic input in the Krause--Lacey stopping
argument.  The hypothesis `HasOneNodeGoodPartPairingBound` is exactly the
estimate for the good collection at one node of one of the concrete shifted
dyadic trees.  Everything after that hypothesis is finite and deterministic:
the threshold-ten recursion, preservation of `1 / 4` sparseness, union over
disjoint roots, and the three-shift reduction.
-/

open Function MeasureTheory Set
open scoped ENNReal NNReal

namespace QuadraticCarleson
namespace KrauseLaceyNativePositiveSuffixClosure

open KrauseLaceyAnnularSparseTransfer KrauseLaceyFullDyadicSparseTransfer
open KrauseLaceyPositiveSuffixThreeShift KrauseLaceyStoppingExtraction
open KrauseLaceyStoppingRecursion
open KrauseLaceyThreeShiftGrid


noncomputable section

local instance : DecidableEq RealInterval := Classical.decEq _

private def sparseAtom (p : ℝ) (f g : ℝ → ℂ) (I : RealInterval) : ℝ≥0∞ :=
  ENNReal.ofReal (I.length * localAverage 1 f I * localAverage p g I)

theorem sparseForm_finset (p : ℝ) (f g : ℝ → ℂ)
    (S : Finset RealInterval) :
    sparseForm p f g (↑S : Set RealInterval) = ∑ I ∈ S, sparseAtom p f g I := by
  rw [sparseForm]
  exact Finset.tsum_subtype S (fun I ↦
    ENNReal.ofReal (I.length * localAverage 1 f I * localAverage p g I))

private theorem length_le_of_carrier_subset {I J : RealInterval}
    (h : I.carrier ⊆ J.carrier) : I.length ≤ J.length := by
  have he := (Ioc_subset_Ioc_iff I.left_lt_right).mp h
  dsimp [RealInterval.length]
  linarith [he.1, he.2]

private theorem interval_eq_of_mutual_carrier_subset {I J : RealInterval}
    (hIJ : I.carrier ⊆ J.carrier) (hJI : J.carrier ⊆ I.carrier) : I = J :=
  interval_eq_of_carrier_subset_of_length_le hIJ (length_le_of_carrier_subset hJI)

/- A sparse family below each pairwise-disjoint child can be attached to a
new root.  The root major subset is the actual threshold-ten stopping major
subset, so the density remains exactly `1 / 4`. -/
private theorem isSparse_insert_root_biUnion
    {S : Finset RealInterval} {f monitor : ℝ → ℂ} (I : RealInterval)
    (hf : Integrable f) (hm : Integrable monitor)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (R : RealInterval → Finset RealInterval)
    (hRsparse : ∀ K ∈ stoppingChildren S f monitor I,
      IsSparse (1 / 4) (↑(R K) : Set RealInterval))
    (hRsub : ∀ K ∈ stoppingChildren S f monitor I, ∀ J ∈ R K,
      J.carrier ⊆ K.carrier) :
    IsSparse (1 / 4)
      (↑(insert I ((stoppingChildren S f monitor I).biUnion R)) : Set RealInterval) := by
  classical
  let C := stoppingChildren S f monitor I
  let B := C.biUnion R
  have hCdisj : Set.Pairwise (↑C : Set RealInterval)
      (Disjoint on fun K : RealInterval ↦ K.carrier) :=
    stoppingChildren_pairwiseDisjoint f monitor I hlam
  have hRdisj : Set.PairwiseDisjoint (↑C : Set RealInterval) R := by
    intro K hK L hL hKL
    apply Finset.disjoint_left.mpr
    intro J hJK hJL
    have hx : J.right ∈ J.carrier := ⟨J.left_lt_right, le_rfl⟩
    exact Set.disjoint_left.mp (hCdisj hK hL hKL)
      (hRsub K hK J hJK hx) (hRsub L hL J hJL hx)
  have hIB : I ∉ B := by
    intro hI
    obtain ⟨K, hK, hIK⟩ := Finset.mem_biUnion.mp hI
    have hIKsub := hRsub K hK I hIK
    have hKIsub := (stoppingChildren_bad hK).1
    have hKI : K = I := (interval_eq_of_mutual_carrier_subset hIKsub hKIsub).symm
    exact self_not_mem_stoppingChildren S f monitor I (by simpa only [hKI] using hK)
  by_cases hC : C.Nonempty
  · let ι := {K : RealInterval // K ∈ C}
    let F : ι → Set RealInterval := fun K ↦ ↑(R K.1)
    let U : ι → Set ℝ := fun K ↦ K.1.carrier
    let _ : Nonempty ι := Set.nonempty_coe_sort.mpr (by simpa using hC)
    have hFsparse : ∀ K : ι, IsSparse (1 / 4) (F K) := fun K ↦
      hRsparse K.1 K.2
    have hFU : ∀ K : ι, ∀ J ∈ F K, J.carrier ⊆ U K := fun K J hJ ↦
      hRsub K.1 K.2 J hJ
    have hU : (Set.univ : Set ι).PairwiseDisjoint U := by
      intro K hKu L hLu hKL
      exact hCdisj K.2 L.2 (fun h ↦ hKL (Subtype.ext h))
    have hBsparse : IsSparse (1 / 4) (↑B : Set RealInterval) := by
      have hu := IsSparse.iUnion_of_disjoint_carriers F U hU hFU hFsparse
      convert hu using 1
      ext J
      constructor
      · intro hJ
        obtain ⟨K, hK, hJR⟩ := Finset.mem_biUnion.mp hJ
        exact Set.mem_iUnion_of_mem ⟨K, hK⟩ hJR
      · intro hJ
        obtain ⟨K, hJR⟩ := Set.mem_iUnion.mp hJ
        exact Finset.mem_biUnion.mpr ⟨K.1, K.2, hJR⟩
    rcases hBsparse with ⟨heta0, heta1, E, hEmeas, hEsub, hEdisj, hEmass⟩
    let Uchildren : Set ℝ := ⋃ K ∈ C, K.carrier
    let E' : {J : RealInterval // J ∈ (↑(insert I B) : Set RealInterval)} → Set ℝ :=
      fun J ↦ if hJI : J.1 = I then I.carrier \ Uchildren
        else E ⟨J.1, (Finset.mem_insert.mp J.2).resolve_left hJI⟩
    refine ⟨heta0, heta1, E', ?_, ?_, ?_, ?_⟩
    · intro J
      by_cases hJI : J.1 = I
      · simp only [E', dif_pos hJI]
        exact I.measurableSet_carrier.diff
          (Finset.measurableSet_biUnion C fun K _ ↦ K.measurableSet_carrier)
      · simp only [E', dif_neg hJI]
        exact hEmeas _
    · intro J
      by_cases hJI : J.1 = I
      · simp only [E', dif_pos hJI]
        simpa only [hJI] using (diff_subset : I.carrier \ Uchildren ⊆ I.carrier)
      · simp only [E', dif_neg hJI]
        exact hEsub _
    · intro J L hJL
      by_cases hJI : J.1 = I
      ·
        have hLI : L.1 ≠ I := fun h ↦
          hJL (Subtype.ext (hJI.trans h.symm))
        simp only [E', dif_pos hJI, dif_neg hLI]
        apply Set.disjoint_left.mpr
        intro x hxroot hxL
        have hLB : L.1 ∈ B := (Finset.mem_insert.mp L.2).resolve_left hLI
        obtain ⟨K, hK, hLK⟩ := Finset.mem_biUnion.mp hLB
        exact hxroot.2 (Set.mem_iUnion_of_mem K
          (Set.mem_iUnion_of_mem hK (hRsub K hK L.1 hLK (hEsub _ hxL))))
      · by_cases hLI : L.1 = I
        ·
          simp only [E', dif_neg hJI, dif_pos hLI]
          apply Disjoint.symm
          apply Set.disjoint_left.mpr
          intro x hxroot hxJ
          have hJB : J.1 ∈ B := (Finset.mem_insert.mp J.2).resolve_left hJI
          obtain ⟨K, hK, hJK⟩ := Finset.mem_biUnion.mp hJB
          exact hxroot.2 (Set.mem_iUnion_of_mem K
            (Set.mem_iUnion_of_mem hK (hRsub K hK J.1 hJK (hEsub _ hxJ))))
        · simp only [E', dif_neg hJI, dif_neg hLI]
          apply hEdisj
          intro h
          apply hJL
          apply Subtype.ext
          exact congrArg (fun z : {J : RealInterval // J ∈ (↑B : Set RealInterval)} ↦ z.1) h
    · intro J
      by_cases hJI : J.1 = I
      · simp only [E', dif_pos hJI]
        have hfour := stoppingMajorSubset_measure_ge_four_fifths f monitor I
          hf.integrableOn hm.integrableOn hlam
        have hquarter : (1 / 4 : ℝ) * I.length ≤
            (volume (I.carrier \ Uchildren)).toReal := by
          apply (mul_le_mul_of_nonneg_right
            (by norm_num : (1 / 4 : ℝ) ≤ 4 / 5) I.length_pos.le).trans
          simpa only [krauseLaceyStoppingMajorSubset, id_eq, C, Uchildren] using hfour
        simpa only [hJI] using hquarter
      · simp only [E', dif_neg hJI]
        exact hEmass ⟨J.1, (Finset.mem_insert.mp J.2).resolve_left hJI⟩
  · have hCempty : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hC
    simp only [C] at hCempty
    have hs := root_insert_stoppingChildren_isSparse f monitor I hf hm hlam
    simpa [B, C, hCempty, stoppingStepFamily] using hs

/-- The sole analytic interface needed by the global closure theorem.

At one node `I` of one concrete shifted dyadic tree, stop simultaneously on
the `L¹` average of `f` and the `L¹` average of `‖g‖^p`.  The hypothesis asks
only for the pairing of the surviving good collection.  Its right side is
the single sparse atom at `I`, with the paper-facing `p'` dependence.

The collection supplied to the node may be any subcollection of the ambient
complete tree contained in `I`; this closure under restriction is what makes
the finite recursion composable. -/
def HasOneNodeGoodPartPairingBound (A : ℝ) : Prop :=
  0 ≤ A ∧
    ∀ (p : ℝ), ∀ hp : 1 < p, p ≤ 2 →
      ∀ (ell₀ topScale : ℤ) (shift : Fin 3) (maxDepth : ℕ) (q₀ : ℤ)
        (S : Finset RealInterval) (I : RealInterval) (f g : L0Infinity),
        3 ≤ ell₀ →
        S ⊆ completeFiniteShiftGridTree topScale shift maxDepth q₀ →
        I ∈ completeFiniteShiftGridTree topScale shift maxDepth q₀ →
        (∀ J ∈ S, J.carrier ⊆ I.carrier) →
        (∫⁻ x, localizedTailMaximal ell₀ (finiteShiftGridScale topScale shift)
            (goodCollection S f g I) f x * ‖g x‖ₑ) ≤
          ENNReal.ofReal (A * holderConjugate p) * sparseAtom p f g I

private theorem childCollection_ssubset_of_root_mem
    {S : Finset RealInterval} {f monitor : ℝ → ℂ} {I K : RealInterval}
    (hI : I ∈ S) (hK : K ∈ stoppingChildren S f monitor I) :
    childCollection S K ⊂ S := by
  classical
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨fun J hJ ↦ (Finset.mem_filter.mp hJ).1, ?_⟩
  intro heq
  have hImem : I ∈ childCollection S K := heq.symm ▸ hI
  have hIK : I.carrier ⊆ K.carrier := (Finset.mem_filter.mp hImem).2
  have hKI : K.carrier ⊆ I.carrier := (stoppingChildren_bad hK).1
  have : K = I := (interval_eq_of_mutual_carrier_subset hIK hKI).symm
  exact self_not_mem_stoppingChildren S f monitor I (by simpa only [this] using hK)

private theorem sparseForm_insert_biUnion
    (p : ℝ) (f g : ℝ → ℂ) (I : RealInterval)
    (C : Finset RealInterval) (R : RealInterval → Finset RealInterval)
    (hRdisj : Set.PairwiseDisjoint (↑C : Set RealInterval) R)
    (hI : I ∉ C.biUnion R) :
    sparseForm p f g (↑(insert I (C.biUnion R)) : Set RealInterval) =
      sparseAtom p f g I + ∑ K ∈ C, sparseForm p f g (↑(R K) : Set RealInterval) := by
  rw [sparseForm_finset, Finset.sum_insert hI, Finset.sum_biUnion hRdisj]
  simp_rw [← sparseForm_finset]

/- The finite recursion below a node already belonging to the active
collection.  Membership of the root makes every recursive child collection
a strict sub-finset, so strong induction terminates after at most `S.card`
steps. -/
private theorem exists_recursive_sparse_bound_of_root_mem
    {A p : ℝ} (hlocal : HasOneNodeGoodPartPairingBound A)
    (hp : 1 < p) (hp2 : p < 2)
    (ell₀ topScale : ℤ) (shift : Fin 3) (maxDepth : ℕ) (q₀ : ℤ)
    (S : Finset RealInterval) (I : RealInterval) (f g : L0Infinity)
    (hell : 3 ≤ ell₀)
    (hStree : S ⊆ completeFiniteShiftGridTree topScale shift maxDepth q₀)
    (hItree : I ∈ completeFiniteShiftGridTree topScale shift maxDepth q₀)
    (hsub : ∀ J ∈ S, J.carrier ⊆ I.carrier) (hI : I ∈ S) :
    ∃ R : Finset RealInterval,
      IsSparse (1 / 4) (↑R : Set RealInterval) ∧
      (∀ J ∈ R, J.carrier ⊆ I.carrier) ∧
      (∫⁻ x, localizedTailMaximal ell₀ (finiteShiftGridScale topScale shift) S f x *
        ‖g x‖ₑ) ≤
        ENNReal.ofReal (A * holderConjugate p) * sparseForm p f g (↑R : Set RealInterval) := by
  classical
  induction S using Finset.strongInductionOn generalizing I with
  | _ S ih =>
      let monitor := g
      let C := stoppingChildren S f monitor I
      let scale := finiteShiftGridScale topScale shift
      have hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
          J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier :=
        (completeFiniteShiftGridTree_laminar topScale shift maxDepth q₀).mono hStree
      have hscale : ∀ J ∈ S, J.length = (2 : ℝ) ^ (scale J + 2) := by
        intro J hJ
        exact completeFiniteShiftGridTree_length_eq_scale topScale shift maxDepth q₀ J
          (hStree hJ)
      have hstep := finite_localized_stopping_step ell₀ scale S
        f.measurable_toFun g.measurable_toFun f.integrable g.integrable I hsub hscale hlam
      have hgood := hlocal.2 p hp hp2.le ell₀ topScale shift maxDepth q₀ S I f g
        hell hStree hItree hsub
      have hchild (K : RealInterval) (hK : K ∈ C) :
          ∃ R : Finset RealInterval,
            IsSparse (1 / 4) (↑R : Set RealInterval) ∧
            (∀ J ∈ R, J.carrier ⊆ K.carrier) ∧
            (∫⁻ x, localizedTailMaximal ell₀ scale (childCollection S K) f x * ‖g x‖ₑ) ≤
              ENNReal.ofReal (A * holderConjugate p) *
                sparseForm p f g (↑R : Set RealInterval) := by
        have hK' : K ∈ stoppingChildren S f monitor I := hK
        have hKS : K ∈ S := stoppingChildren_subset S f monitor I hK'
        apply ih (childCollection S K) (childCollection_ssubset_of_root_mem hI hK') K
        · intro J hJ
          exact hStree (Finset.mem_filter.mp hJ).1
        · exact hStree hKS
        · intro J hJ
          exact (Finset.mem_filter.mp hJ).2
        · exact Finset.mem_filter.mpr ⟨hKS, Subset.rfl⟩
      choose R hRsparse hRsub hRbound using hchild
      let R' : RealInterval → Finset RealInterval :=
        fun K => if hK : K ∈ C then R K hK else ∅
      have hRsparse' : ∀ K ∈ C, IsSparse (1 / 4) (↑(R' K) : Set RealInterval) := by
        intro K hK
        simp only [R', dif_pos hK]
        exact hRsparse K hK
      have hRsub' : ∀ K ∈ C, ∀ J ∈ R' K, J.carrier ⊆ K.carrier := by
        intro K hK
        simp only [R', dif_pos hK]
        exact hRsub K hK
      have hRbound' : ∀ K ∈ C,
          (∫⁻ x, localizedTailMaximal ell₀ scale (childCollection S K) f x * ‖g x‖ₑ) ≤
            ENNReal.ofReal (A * holderConjugate p) *
              sparseForm p f g (↑(R' K) : Set RealInterval) := by
        intro K hK
        simp only [R', dif_pos hK]
        exact hRbound K hK
      let B := C.biUnion R'
      let Rall := insert I B
      have hCdisj : Set.Pairwise (↑C : Set RealInterval)
          (Disjoint on fun K : RealInterval ↦ K.carrier) :=
        stoppingChildren_pairwiseDisjoint f monitor I hlam
      have hRdisj : Set.PairwiseDisjoint (↑C : Set RealInterval) R' := by
        intro K hK L hL hKL
        apply Finset.disjoint_left.mpr
        intro J hJK hJL
        have hx : J.right ∈ J.carrier := ⟨J.left_lt_right, le_rfl⟩
        exact Set.disjoint_left.mp (hCdisj hK hL hKL)
          (hRsub' K hK J hJK hx) (hRsub' L hL J hJL hx)
      have hIB : I ∉ B := by
        intro hIB
        obtain ⟨K, hK, hIK⟩ := Finset.mem_biUnion.mp hIB
        have hIKsub := hRsub' K hK I hIK
        have hKIsub := (stoppingChildren_bad hK).1
        have hKI : K = I := (interval_eq_of_mutual_carrier_subset hIKsub hKIsub).symm
        exact self_not_mem_stoppingChildren S f monitor I (by simpa only [hKI] using hK)
      refine ⟨Rall, ?_, ?_, ?_⟩
      · exact isSparse_insert_root_biUnion I f.integrable monitor.integrable hlam R'
          hRsparse' hRsub'
      · intro J hJ
        rcases Finset.mem_insert.mp hJ with rfl | hJB
        · exact Subset.rfl
        · obtain ⟨K, hK, hJK⟩ := Finset.mem_biUnion.mp hJB
          exact (hRsub' K hK J hJK).trans (stoppingChildren_bad hK).1
      · calc
          (∫⁻ x, localizedTailMaximal ell₀ scale S f x * ‖g x‖ₑ) ≤
              (∫⁻ x, localizedTailMaximal ell₀ scale
                (goodCollection S f monitor I) f x * ‖g x‖ₑ) +
                ∑ K ∈ C, ∫⁻ x, localizedTailMaximal ell₀ scale
                  (childCollection S K) f x * ‖g x‖ₑ := hstep.2.2.2
          _ ≤ ENNReal.ofReal (A * holderConjugate p) * sparseAtom p f g I +
                ∑ K ∈ C, ENNReal.ofReal (A * holderConjugate p) *
                  sparseForm p f g (↑(R' K) : Set RealInterval) := by
              exact add_le_add hgood (Finset.sum_le_sum fun K hK ↦ hRbound' K hK)
          _ = ENNReal.ofReal (A * holderConjugate p) *
                sparseForm p f g (↑Rall : Set RealInterval) := by
              rw [sparseForm_insert_biUnion p f g I C R' hRdisj hIB]
              rw [mul_add, Finset.mul_sum]

/- One external root step reduces immediately to the root-member recursion
on each selected child.  This is the form used for the depth-zero roots of a
three-shift forest, which need not themselves occur in the localized input
family. -/
theorem exists_recursive_sparse_bound
    {A p : ℝ} (hlocal : HasOneNodeGoodPartPairingBound A)
    (hp : 1 < p) (hp2 : p < 2)
    (ell₀ topScale : ℤ) (shift : Fin 3) (maxDepth : ℕ) (q₀ : ℤ)
    (S : Finset RealInterval) (f g : L0Infinity)
    (hell : 3 ≤ ell₀)
    (hStree : S ⊆ completeFiniteShiftGridTree topScale shift maxDepth q₀) :
    ∃ R : Finset RealInterval,
      IsSparse (1 / 4) (↑R : Set RealInterval) ∧
      (∀ J ∈ R, J.carrier ⊆
        (finiteShiftGridInterval topScale shift 0 q₀).carrier) ∧
      (∫⁻ x, localizedTailMaximal ell₀ (finiteShiftGridScale topScale shift) S f x *
        ‖g x‖ₑ) ≤
        ENNReal.ofReal (A * holderConjugate p) * sparseForm p f g (↑R : Set RealInterval) := by
  classical
  let I := finiteShiftGridInterval topScale shift 0 q₀
  let scale := finiteShiftGridScale topScale shift
  by_cases hS : S = ∅
  · refine ⟨∅, by simpa using HardyLittlewoodSparseReduction.isSparse_empty, by simp, ?_⟩
    simp [hS, localizedTailMaximal, localizedTailAction]
  have hsub : ∀ J ∈ S, J.carrier ⊆ I.carrier := by
    intro J hJ
    exact completeFiniteShiftGridTree_subset_root topScale shift maxDepth q₀ J (hStree hJ)
  have hItree : I ∈ completeFiniteShiftGridTree topScale shift maxDepth q₀ :=
    root_mem_completeFiniteShiftGridTree topScale shift maxDepth q₀
  have hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier :=
    (completeFiniteShiftGridTree_laminar topScale shift maxDepth q₀).mono hStree
  have hscale : ∀ J ∈ S, J.length = (2 : ℝ) ^ (scale J + 2) := by
    intro J hJ
    exact completeFiniteShiftGridTree_length_eq_scale topScale shift maxDepth q₀ J
      (hStree hJ)
  let monitor := g
  let C := stoppingChildren S f monitor I
  have hstep := finite_localized_stopping_step ell₀ scale S
    f.measurable_toFun g.measurable_toFun f.integrable g.integrable I hsub hscale hlam
  have hgood := hlocal.2 p hp hp2.le ell₀ topScale shift maxDepth q₀ S I f g
    hell hStree hItree hsub
  have hchild (K : RealInterval) (hK : K ∈ C) :=
    exists_recursive_sparse_bound_of_root_mem hlocal hp hp2 ell₀ topScale shift maxDepth q₀
      (childCollection S K) K f g hell
      (fun J hJ ↦ hStree (Finset.mem_filter.mp hJ).1)
      (hStree (stoppingChildren_subset S f monitor I hK))
      (fun J hJ ↦ (Finset.mem_filter.mp hJ).2)
      (Finset.mem_filter.mpr
        ⟨stoppingChildren_subset S f monitor I hK, Subset.rfl⟩)
  choose R hRsparse hRsub hRbound using hchild
  let R' : RealInterval → Finset RealInterval :=
    fun K => if hK : K ∈ C then R K hK else ∅
  have hRsparse' : ∀ K ∈ C, IsSparse (1 / 4) (↑(R' K) : Set RealInterval) := by
    intro K hK
    simp only [R', dif_pos hK]
    exact hRsparse K hK
  have hRsub' : ∀ K ∈ C, ∀ J ∈ R' K, J.carrier ⊆ K.carrier := by
    intro K hK
    simp only [R', dif_pos hK]
    exact hRsub K hK
  have hRbound' : ∀ K ∈ C,
      (∫⁻ x, localizedTailMaximal ell₀ scale (childCollection S K) f x * ‖g x‖ₑ) ≤
        ENNReal.ofReal (A * holderConjugate p) *
          sparseForm p f g (↑(R' K) : Set RealInterval) := by
    intro K hK
    simp only [R', dif_pos hK]
    exact hRbound K hK
  let B := C.biUnion R'
  let Rall := insert I B
  have hCdisj : Set.Pairwise (↑C : Set RealInterval)
      (Disjoint on fun K : RealInterval ↦ K.carrier) :=
    stoppingChildren_pairwiseDisjoint f monitor I hlam
  have hRdisj : Set.PairwiseDisjoint (↑C : Set RealInterval) R' := by
    intro K hK L hL hKL
    apply Finset.disjoint_left.mpr
    intro J hJK hJL
    have hx : J.right ∈ J.carrier := ⟨J.left_lt_right, le_rfl⟩
    exact Set.disjoint_left.mp (hCdisj hK hL hKL)
      (hRsub' K hK J hJK hx) (hRsub' L hL J hJL hx)
  have hIB : I ∉ B := by
    intro hIB
    obtain ⟨K, hK, hIK⟩ := Finset.mem_biUnion.mp hIB
    have hIKsub := hRsub' K hK I hIK
    have hKIsub := (stoppingChildren_bad hK).1
    have hKI : K = I := (interval_eq_of_mutual_carrier_subset hIKsub hKIsub).symm
    exact self_not_mem_stoppingChildren S f monitor I (by simpa only [hKI] using hK)
  refine ⟨Rall, ?_, ?_, ?_⟩
  · exact isSparse_insert_root_biUnion I f.integrable monitor.integrable hlam R'
      hRsparse' hRsub'
  · intro J hJ
    rcases Finset.mem_insert.mp hJ with rfl | hJB
    · exact Subset.rfl
    · obtain ⟨K, hK, hJK⟩ := Finset.mem_biUnion.mp hJB
      exact (hRsub' K hK J hJK).trans (stoppingChildren_bad hK).1
  · calc
      (∫⁻ x, localizedTailMaximal ell₀ scale S f x * ‖g x‖ₑ) ≤
          (∫⁻ x, localizedTailMaximal ell₀ scale
            (goodCollection S f monitor I) f x * ‖g x‖ₑ) +
            ∑ K ∈ C, ∫⁻ x, localizedTailMaximal ell₀ scale
              (childCollection S K) f x * ‖g x‖ₑ := hstep.2.2.2
      _ ≤ ENNReal.ofReal (A * holderConjugate p) * sparseAtom p f g I +
            ∑ K ∈ C, ENNReal.ofReal (A * holderConjugate p) *
              sparseForm p f g (↑(R' K) : Set RealInterval) := by
          exact add_le_add hgood (Finset.sum_le_sum fun K hK ↦ hRbound' K hK)
      _ = ENNReal.ofReal (A * holderConjugate p) *
            sparseForm p f g (↑Rall : Set RealInterval) := by
          rw [sparseForm_insert_biUnion p f g I C R' hRdisj hIB]
          rw [mul_add, Finset.mul_sum]

/- The scalar-valued test operator associated with one localized shifted
   tree.  The `toReal` coercion is harmless even before finiteness is known:
   `ENNReal.ofReal_toReal_le` is enough for every domination below. -/
noncomputable def localizedTailMaximalTestOperator
    (ell₀ : ℤ) (scale : RealInterval → ℤ) (S : Finset RealInterval) : TestOperator :=
  fun f x ↦ ((localizedTailMaximal ell₀ scale S f x).toReal : ℂ)

theorem hasSparseOnePBound_localizedTailMaximalTestOperator_of_tree
    {A p : ℝ} (hlocal : HasOneNodeGoodPartPairingBound A)
    (hp : 1 < p) (hp2 : p < 2)
    (ell₀ topScale : ℤ) (shift : Fin 3) (maxDepth : ℕ) (q₀ : ℤ)
    (S : Finset RealInterval) (hStree : S ⊆
      completeFiniteShiftGridTree topScale shift maxDepth q₀)
    (hell : 3 ≤ ell₀) :
    HasSparseOnePBound (A * holderConjugate p) p
      (localizedTailMaximalTestOperator ell₀
        (finiteShiftGridScale topScale shift) S) := by
  intro f g
  obtain ⟨R, hRsparse, hRsub, hpair⟩ := exists_recursive_sparse_bound
    hlocal hp hp2 ell₀ topScale shift maxDepth q₀ S f g hell hStree
  refine ⟨(↑R : Set RealInterval), hRsparse, ?_⟩
  let T := localizedTailMaximalTestOperator ell₀
    (finiteShiftGridScale topScale shift) S
  by_cases hi : Integrable (fun x ↦ T f x * star (g x))
  · have hnorm : ‖operatorPairing T f g‖ ≤
        ∫ x, ‖T f x * star (g x)‖ := by
      unfold operatorPairing
      exact norm_integral_le_of_norm_le hi.norm
        (Filter.Eventually.of_forall fun x ↦ le_rfl)
    have hof : ENNReal.ofReal ‖operatorPairing T f g‖ ≤
        ∫⁻ x, ‖T f x * star (g x)‖ₑ := by
      exact (ENNReal.ofReal_le_ofReal hnorm).trans_eq
        (ofReal_integral_norm_eq_lintegral_enorm hi)
    refine hof.trans (le_trans ?_ hpair)
    apply lintegral_mono
    intro x
    simp only [T, localizedTailMaximalTestOperator, norm_mul, norm_star,
      ← ofReal_norm]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg]
    exact mul_le_mul' ENNReal.ofReal_toReal_le le_rfl
  · have hzero : operatorPairing T f g = 0 := by
      unfold operatorPairing
      exact integral_undef hi
    rw [hzero, norm_zero, ENNReal.ofReal_zero]
    exact bot_le


end

end KrauseLaceyNativePositiveSuffixClosure
end QuadraticCarleson
