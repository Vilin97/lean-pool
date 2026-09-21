/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyPStoppingRecursion
import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyNativePositiveSuffixClosure

/-!
# Positive one-node interface with genuine `p`-monitor stopping

The good collection below is formed with `pStoppingMonitor g p hp`, while
the pairing remains against the original `g`.
-/

open Function MeasureTheory Set
open scoped ENNReal NNReal

namespace QuadraticCarleson
namespace KrauseLaceyPStoppingPositiveClosure

open KrauseLaceyStoppingExtraction KrauseLaceyPStoppingRecursion
open KrauseLaceyStoppingRecursion KrauseLaceyNativePositiveSuffixClosure
open KrauseLaceyThreeShiftGrid


noncomputable
section

/-- Classical decidable equality for the finite interval families used in the p-stopping
construction. -/
local instance : DecidableEq RealInterval := Classical.decEq _

/-- The contribution of one interval to the sparse form with local exponents one and `p`. -/
noncomputable def pStoppingSparseAtom (p : ℝ) (f g : ℝ → ℂ)
    (I : RealInterval) : ℝ≥0∞ :=
  ENNReal.ofReal (I.length * localAverage 1 f I * localAverage p g I)

/-- The public p-stopping atom is exactly the summand of the ambient sparse
form. This lets a recursive p-stopping witness be assembled without ever
returning to the old `L¹` monitor interface. -/
theorem sparseForm_finset_pStoppingAtom (p : ℝ) (f g : ℝ → ℂ)
    (R : Finset RealInterval) :
    sparseForm p f g (↑R : Set RealInterval) =
      ∑ I ∈ R, pStoppingSparseAtom p f g I := by
  unfold sparseForm pStoppingSparseAtom
  exact Finset.tsum_subtype R (fun I ↦
    ENNReal.ofReal (I.length * localAverage 1 f I * localAverage p g I))

private theorem pStopping_interval_eq_of_mutual_carrier_subset {I J : RealInterval}
    (hIJ : I.carrier ⊆ J.carrier) (hJI : J.carrier ⊆ I.carrier) : I = J := by
  apply interval_eq_of_carrier_subset_of_length_le hIJ
  have he := (Ioc_subset_Ioc_iff J.left_lt_right).mp hJI
  dsimp [RealInterval.length]
  linarith [he.1, he.2]

private theorem pStopping_childCollection_ssubset
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
  have hEq : K = I := (pStopping_interval_eq_of_mutual_carrier_subset hIK hKI).symm
  exact self_not_mem_stoppingChildren S f monitor I (by simpa only [hEq] using hK)

/-- The p-stopping replacement for the old interface: only the monitor,
not the testing function in the pairing, is changed. -/
def HasOneNodePStoppingGoodPartPairingBound (A : ℝ) : Prop :=
  0 ≤ A ∧ ∀ (p : ℝ), ∀ hp : 1 < p, p ≤ 2 →
    ∀ (ell₀ topScale : ℤ) (shift : Fin 3) (maxDepth : ℕ) (q₀ : ℤ)
      (S : Finset RealInterval) (I : RealInterval) (f g : L0Infinity),
      3 ≤ ell₀ →
      S ⊆ completeFiniteShiftGridTree topScale shift maxDepth q₀ →
      I ∈ completeFiniteShiftGridTree topScale shift maxDepth q₀ →
      (∀ J ∈ S, J.carrier ⊆ I.carrier) →
      (∫⁻ x, localizedTailMaximal ell₀ (finiteShiftGridScale topScale shift)
        (goodCollection S f (pStoppingMonitor g p (lt_trans zero_lt_one hp)) I) f x * ‖g x‖ₑ) ≤
        ENNReal.ofReal (A * holderConjugate p) * pStoppingSparseAtom p f g I

theorem pStopping_good_part_pairing
    {A p : ℝ} (hlocal : HasOneNodePStoppingGoodPartPairingBound A)
    (hp : 1 < p) (hp2 : p ≤ 2)
    (ell₀ topScale : ℤ) (shift : Fin 3) (maxDepth : ℕ) (q₀ : ℤ)
    (S : Finset RealInterval) (I : RealInterval) (f g : L0Infinity)
    (hell : 3 ≤ ell₀)
    (hS : S ⊆ completeFiniteShiftGridTree topScale shift maxDepth q₀)
    (hI : I ∈ completeFiniteShiftGridTree topScale shift maxDepth q₀)
    (hsub : ∀ J ∈ S, J.carrier ⊆ I.carrier) :
    (∫⁻ x, localizedTailMaximal ell₀ (finiteShiftGridScale topScale shift)
      (goodCollection S f (pStoppingMonitor g p (lt_trans zero_lt_one hp)) I) f x * ‖g x‖ₑ) ≤
      ENNReal.ofReal (A * holderConjugate p) * pStoppingSparseAtom p f g I :=
  hlocal.2 p hp hp2 ell₀ topScale shift maxDepth q₀ S I f g hell hS hI hsub

/-- One exact recursive p-stopping step with the local term closed by the
new interface. This is the induction step needed for the finite tree/forest
closure; recursive children retain the same monitor convention. -/
theorem pStopping_one_step_pairing_bound
    {A p : ℝ} (hlocal : HasOneNodePStoppingGoodPartPairingBound A)
    (hp : 1 < p) (hp2 : p ≤ 2)
    (ell₀ topScale : ℤ) (shift : Fin 3) (maxDepth : ℕ) (q₀ : ℤ)
    (S : Finset RealInterval) (I : RealInterval) (f g : L0Infinity)
    (hell : 3 ≤ ell₀)
    (hS : S ⊆ completeFiniteShiftGridTree topScale shift maxDepth q₀)
    (hI : I ∈ completeFiniteShiftGridTree topScale shift maxDepth q₀)
    (hsub : ∀ J ∈ S, J.carrier ⊆ I.carrier) :
    (∫⁻ x, localizedTailMaximal ell₀ (finiteShiftGridScale topScale shift) S f x * ‖g x‖ₑ) ≤
      ENNReal.ofReal (A * holderConjugate p) * pStoppingSparseAtom p f g I +
        ∑ K ∈ stoppingChildren S f (pStoppingMonitor g p (lt_trans zero_lt_one hp)) I,
          ∫⁻ x, localizedTailMaximal ell₀ (finiteShiftGridScale topScale shift)
            (childCollection S K) f x * ‖g x‖ₑ := by
  let scale := finiteShiftGridScale topScale shift
  have hlam := (completeFiniteShiftGridTree_laminar topScale shift maxDepth q₀).mono hS
  have hscale : ∀ J ∈ S, J.length = (2 : ℝ) ^ (scale J + 2) := by
    intro J hJ
    exact completeFiniteShiftGridTree_length_eq_scale topScale shift maxDepth q₀ J (hS hJ)
  have hstep := finite_localized_p_stopping_step ell₀ scale S g (lt_trans zero_lt_one hp)
    f.measurable_toFun f.integrable I hsub hscale hlam
  exact le_trans hstep.2.2.2 (add_le_add
    (pStopping_good_part_pairing hlocal hp hp2 ell₀ topScale shift maxDepth q₀ S I f g
      hell hS hI hsub) le_rfl)

/- A sparse family below each pairwise-disjoint p-stopping child can be
attached to the current root without losing the `1 / 4` density. -/
private theorem pStopping_isSparse_insert_root_biUnion
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
    have hKI : K = I :=
      (pStopping_interval_eq_of_mutual_carrier_subset hIKsub hKIsub).symm
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
      · simp only [E', dite_eq_left hJI]
        exact I.measurableSet_carrier.diff
          (Finset.measurableSet_biUnion C fun K _ ↦ K.measurableSet_carrier)
      · simp only [E', dite_eq_right hJI]
        exact hEmeas _
    · intro J
      by_cases hJI : J.1 = I
      · simp only [E', dite_eq_left hJI]
        simpa only [hJI] using (sdiff_subset : I.carrier \ Uchildren ⊆ I.carrier)
      · simp only [E', dite_eq_right hJI]
        exact hEsub _
    · intro J L hJL
      by_cases hJI : J.1 = I
      · have hLI : L.1 ≠ I := fun h ↦ hJL (Subtype.ext (hJI.trans h.symm))
        simp only [E', dite_eq_left hJI, dite_eq_right hLI]
        apply Set.disjoint_left.mpr
        intro x hxroot hxL
        have hLB : L.1 ∈ B := (Finset.mem_insert.mp L.2).resolve_left hLI
        obtain ⟨K, hK, hLK⟩ := Finset.mem_biUnion.mp hLB
        exact hxroot.2 (Set.mem_iUnion_of_mem K
          (Set.mem_iUnion_of_mem hK (hRsub K hK L.1 hLK (hEsub _ hxL))))
      · by_cases hLI : L.1 = I
        · simp only [E', dite_eq_right hJI, dite_eq_left hLI]
          apply Disjoint.symm
          apply Set.disjoint_left.mpr
          intro x hxroot hxJ
          have hJB : J.1 ∈ B := (Finset.mem_insert.mp J.2).resolve_left hJI
          obtain ⟨K, hK, hJK⟩ := Finset.mem_biUnion.mp hJB
          exact hxroot.2 (Set.mem_iUnion_of_mem K
            (Set.mem_iUnion_of_mem hK (hRsub K hK J.1 hJK (hEsub _ hxJ))))
        · simp only [E', dite_eq_right hJI, dite_eq_right hLI]
          apply hEdisj
          intro h
          apply hJL
          apply Subtype.ext
          exact congrArg
            (fun z : {J : RealInterval // J ∈ (↑B : Set RealInterval)} ↦ z.1) h
    · intro J
      by_cases hJI : J.1 = I
      · simp only [E', dite_eq_left hJI]
        have hfour := stoppingMajorSubset_measure_ge_four_fifths f monitor I
          hf.integrableOn hm.integrableOn hlam
        have hquarter : (1 / 4 : ℝ) * I.length ≤
            (volume (I.carrier \ Uchildren)).toReal := by
          apply (mul_le_mul_of_nonneg_right
            (by norm_num : (1 / 4 : ℝ) ≤ 4 / 5) I.length_pos.le).trans
          simpa only [krauseLaceyStoppingMajorSubset, id_eq, C, Uchildren] using hfour
        simpa only [hJI] using hquarter
      · simp only [E', dite_eq_right hJI]
        exact hEmass ⟨J.1, (Finset.mem_insert.mp J.2).resolve_left hJI⟩
  · have hCempty : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hC
    simp only [C] at hCempty
    have hs := root_insert_stoppingChildren_isSparse f monitor I hf hm hlam
    simpa [B, C, hCempty, stoppingStepFamily] using hs

private theorem pStopping_sparseForm_insert_biUnion
    (p : ℝ) (f g : ℝ → ℂ) (I : RealInterval)
    (C : Finset RealInterval) (R : RealInterval → Finset RealInterval)
    (hRdisj : Set.PairwiseDisjoint (↑C : Set RealInterval) R)
    (hI : I ∉ C.biUnion R) :
    sparseForm p f g (↑(insert I (C.biUnion R)) : Set RealInterval) =
      pStoppingSparseAtom p f g I +
        ∑ K ∈ C, sparseForm p f g (↑(R K) : Set RealInterval) := by
  rw [sparseForm_finset_pStoppingAtom, Finset.sum_insert hI,
    Finset.sum_biUnion hRdisj]
  simp_rw [← sparseForm_finset_pStoppingAtom]

/- Strong induction over the active finite collection. The auxiliary
monitor is fixed throughout the recursion, while the integrand continues to
pair with the original `g`. -/
private theorem exists_pStopping_recursive_sparse_bound_of_root_mem
    {A p : ℝ} (hlocal : HasOneNodePStoppingGoodPartPairingBound A)
    (hp : 1 < p) (hp2 : p ≤ 2)
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
      let monitor := pStoppingMonitor g p (lt_trans zero_lt_one hp)
      let C := stoppingChildren S f monitor I
      let scale := finiteShiftGridScale topScale shift
      have hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
          J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier :=
        (completeFiniteShiftGridTree_laminar topScale shift maxDepth q₀).mono hStree
      have hstep := pStopping_one_step_pairing_bound hlocal hp hp2 ell₀ topScale shift
        maxDepth q₀ S I f g hell hStree hItree hsub
      have hchild (K : RealInterval) (hK : K ∈ C) :
          ∃ R : Finset RealInterval,
            IsSparse (1 / 4) (↑R : Set RealInterval) ∧
            (∀ J ∈ R, J.carrier ⊆ K.carrier) ∧
            (∫⁻ x, localizedTailMaximal ell₀ scale (childCollection S K) f x * ‖g x‖ₑ) ≤
              ENNReal.ofReal (A * holderConjugate p) *
                sparseForm p f g (↑R : Set RealInterval) := by
        have hK' : K ∈ stoppingChildren S f monitor I := hK
        have hKS : K ∈ S := stoppingChildren_subset S f monitor I hK'
        apply ih (childCollection S K) (pStopping_childCollection_ssubset hI hK') K
        · intro J hJ
          exact hStree (Finset.mem_filter.mp hJ).1
        · exact hStree hKS
        · intro J hJ
          exact (Finset.mem_filter.mp hJ).2
        · exact Finset.mem_filter.mpr ⟨hKS, Subset.rfl⟩
      choose R hRsparse hRsub hRbound using hchild
      let R' : RealInterval → Finset RealInterval :=
        fun K ↦ if hK : K ∈ C then R K hK else ∅
      have hRsparse' : ∀ K ∈ C,
          IsSparse (1 / 4) (↑(R' K) : Set RealInterval) := by
        intro K hK
        simp only [R', dite_eq_left hK]
        exact hRsparse K hK
      have hRsub' : ∀ K ∈ C, ∀ J ∈ R' K, J.carrier ⊆ K.carrier := by
        intro K hK
        simp only [R', dite_eq_left hK]
        exact hRsub K hK
      have hRbound' : ∀ K ∈ C,
          (∫⁻ x, localizedTailMaximal ell₀ scale (childCollection S K) f x * ‖g x‖ₑ) ≤
            ENNReal.ofReal (A * holderConjugate p) *
              sparseForm p f g (↑(R' K) : Set RealInterval) := by
        intro K hK
        simp only [R', dite_eq_left hK]
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
        have hKI : K = I :=
          (pStopping_interval_eq_of_mutual_carrier_subset hIKsub hKIsub).symm
        exact self_not_mem_stoppingChildren S f monitor I
          (by simpa only [hKI] using hK)
      refine ⟨Rall, ?_, ?_, ?_⟩
      · exact pStopping_isSparse_insert_root_biUnion I f.integrable monitor.integrable
          hlam R' hRsparse' hRsub'
      · intro J hJ
        rcases Finset.mem_insert.mp hJ with rfl | hJB
        · exact Subset.rfl
        · obtain ⟨K, hK, hJK⟩ := Finset.mem_biUnion.mp hJB
          exact (hRsub' K hK J hJK).trans (stoppingChildren_bad hK).1
      · calc
          (∫⁻ x, localizedTailMaximal ell₀ scale S f x * ‖g x‖ₑ) ≤
              ENNReal.ofReal (A * holderConjugate p) * pStoppingSparseAtom p f g I +
                ∑ K ∈ C, ∫⁻ x, localizedTailMaximal ell₀ scale
                  (childCollection S K) f x * ‖g x‖ₑ := hstep
          _ ≤ ENNReal.ofReal (A * holderConjugate p) * pStoppingSparseAtom p f g I +
                ∑ K ∈ C, ENNReal.ofReal (A * holderConjugate p) *
                  sparseForm p f g (↑(R' K) : Set RealInterval) := by
              exact add_le_add le_rfl (Finset.sum_le_sum fun K hK ↦ hRbound' K hK)
          _ = ENNReal.ofReal (A * holderConjugate p) *
                sparseForm p f g (↑Rall : Set RealInterval) := by
              rw [pStopping_sparseForm_insert_biUnion p f g I C R' hRdisj hIB]
              rw [mul_add, Finset.mul_sum]

/-- Recursive p-stopping closure for one complete shifted dyadic tree. -/
theorem exists_pStopping_recursive_sparse_bound
    {A p : ℝ} (hlocal : HasOneNodePStoppingGoodPartPairingBound A)
    (hp : 1 < p) (hp2 : p ≤ 2)
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
  let monitor := pStoppingMonitor g p (lt_trans zero_lt_one hp)
  let C := stoppingChildren S f monitor I
  have hstep := pStopping_one_step_pairing_bound hlocal hp hp2 ell₀ topScale shift
    maxDepth q₀ S I f g hell hStree hItree hsub
  have hchild (K : RealInterval) (hK : K ∈ C) :=
    exists_pStopping_recursive_sparse_bound_of_root_mem hlocal hp hp2 ell₀ topScale
      shift maxDepth q₀ (childCollection S K) K f g hell
      (fun J hJ ↦ hStree (Finset.mem_filter.mp hJ).1)
      (hStree (stoppingChildren_subset S f monitor I hK))
      (fun J hJ ↦ (Finset.mem_filter.mp hJ).2)
      (Finset.mem_filter.mpr
        ⟨stoppingChildren_subset S f monitor I hK, Subset.rfl⟩)
  choose R hRsparse hRsub hRbound using hchild
  let R' : RealInterval → Finset RealInterval :=
    fun K ↦ if hK : K ∈ C then R K hK else ∅
  have hRsparse' : ∀ K ∈ C,
      IsSparse (1 / 4) (↑(R' K) : Set RealInterval) := by
    intro K hK
    simp only [R', dite_eq_left hK]
    exact hRsparse K hK
  have hRsub' : ∀ K ∈ C, ∀ J ∈ R' K, J.carrier ⊆ K.carrier := by
    intro K hK
    simp only [R', dite_eq_left hK]
    exact hRsub K hK
  have hRbound' : ∀ K ∈ C,
      (∫⁻ x, localizedTailMaximal ell₀ scale (childCollection S K) f x * ‖g x‖ₑ) ≤
        ENNReal.ofReal (A * holderConjugate p) *
          sparseForm p f g (↑(R' K) : Set RealInterval) := by
    intro K hK
    simp only [R', dite_eq_left hK]
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
    have hKI : K = I :=
      (pStopping_interval_eq_of_mutual_carrier_subset hIKsub hKIsub).symm
    exact self_not_mem_stoppingChildren S f monitor I (by simpa only [hKI] using hK)
  refine ⟨Rall, ?_, ?_, ?_⟩
  · exact pStopping_isSparse_insert_root_biUnion I f.integrable monitor.integrable
      hlam R' hRsparse' hRsub'
  · intro J hJ
    rcases Finset.mem_insert.mp hJ with rfl | hJB
    · exact Subset.rfl
    · obtain ⟨K, hK, hJK⟩ := Finset.mem_biUnion.mp hJB
      exact (hRsub' K hK J hJK).trans (stoppingChildren_bad hK).1
  · calc
      (∫⁻ x, localizedTailMaximal ell₀ scale S f x * ‖g x‖ₑ) ≤
          ENNReal.ofReal (A * holderConjugate p) * pStoppingSparseAtom p f g I +
            ∑ K ∈ C, ∫⁻ x, localizedTailMaximal ell₀ scale
              (childCollection S K) f x * ‖g x‖ₑ := hstep
      _ ≤ ENNReal.ofReal (A * holderConjugate p) * pStoppingSparseAtom p f g I +
            ∑ K ∈ C, ENNReal.ofReal (A * holderConjugate p) *
              sparseForm p f g (↑(R' K) : Set RealInterval) := by
          exact add_le_add le_rfl (Finset.sum_le_sum fun K hK ↦ hRbound' K hK)
      _ = ENNReal.ofReal (A * holderConjugate p) *
            sparseForm p f g (↑Rall : Set RealInterval) := by
          rw [pStopping_sparseForm_insert_biUnion p f g I C R' hRdisj hIB]
          rw [mul_add, Finset.mul_sum]

private def pStoppingRootSubfamily
    (topScale : ℤ) (shift : Fin 3) (maxDepth : ℕ)
    (S : Finset RealInterval) (q₀ : ℤ) : Finset RealInterval :=
  S.filter fun I ↦ I ∈ completeFiniteShiftGridTree topScale shift maxDepth q₀

private theorem pStoppingRootSubfamilies_pairwiseDisjoint
    (topScale : ℤ) (shift : Fin 3) (maxDepth : ℕ)
    (Q : Finset ℤ) (S : Finset RealInterval) :
    Set.PairwiseDisjoint (↑Q : Set ℤ)
      (pStoppingRootSubfamily topScale shift maxDepth S) := by
  classical
  intro q hq r hr hqr
  apply Finset.disjoint_left.mpr
  intro I hIq hIr
  have hIqtree := (Finset.mem_filter.mp hIq).2
  have hIrtree := (Finset.mem_filter.mp hIr).2
  have hd := completeFiniteShiftGridTree_disjoint_of_ne_root
    topScale shift maxDepth hqr hIqtree hIrtree
  obtain ⟨x, hx⟩ := I.carrier_nonempty
  exact Set.disjoint_left.mp hd hx hx

private theorem pStopping_biUnion_rootSubfamily_eq
    (topScale : ℤ) (shift : Fin 3) (maxDepth : ℕ)
    (F : Finset (ℕ × ℤ)) (S : Finset RealInterval)
    (hS : S ⊆ completeFiniteShiftGridForest topScale shift maxDepth F) :
    (finiteShiftGridRootAddresses F).biUnion
        (pStoppingRootSubfamily topScale shift maxDepth S) = S := by
  classical
  ext I
  constructor
  · intro hI
    obtain ⟨q₀, hq₀, hIq₀⟩ := Finset.mem_biUnion.mp hI
    exact (Finset.mem_filter.mp hIq₀).1
  · intro hI
    have hIF := hS hI
    change I ∈ (finiteShiftGridRootAddresses F).biUnion
      (fun q₀ ↦ completeFiniteShiftGridTree topScale shift maxDepth q₀) at hIF
    obtain ⟨q₀, hq₀, hIq₀⟩ := Finset.mem_biUnion.mp hIF
    exact Finset.mem_biUnion.mpr
      ⟨q₀, hq₀, Finset.mem_filter.mpr ⟨hI, hIq₀⟩⟩

private theorem pStopping_localizedTailMaximal_le_sum_rootSubfamilies
    (ell₀ topScale : ℤ) (shift : Fin 3) (maxDepth : ℕ)
    (Q : Finset ℤ) (S : Finset RealInterval) (f : ℝ → ℂ)
    (hunion : Q.biUnion (pStoppingRootSubfamily topScale shift maxDepth S) = S)
    (x : ℝ) :
    localizedTailMaximal ell₀ (finiteShiftGridScale topScale shift) S f x ≤
      ∑ q₀ ∈ Q, localizedTailMaximal ell₀
        (finiteShiftGridScale topScale shift)
        (pStoppingRootSubfamily topScale shift maxDepth S q₀) f x := by
  classical
  let scale := finiteShiftGridScale topScale shift
  have hdisj := pStoppingRootSubfamilies_pairwiseDisjoint topScale shift maxDepth Q S
  have haction (ell : ℤ) :
      localizedTailAction scale S f ell x =
        ∑ q₀ ∈ Q,
          localizedTailAction scale
            (pStoppingRootSubfamily topScale shift maxDepth S q₀) f ell x := by
    calc
      localizedTailAction scale S f ell x =
          localizedTailAction scale
            (Q.biUnion (pStoppingRootSubfamily topScale shift maxDepth S)) f ell x := by
        rw [hunion]
      _ = _ := by
        unfold localizedTailAction
        rw [Finset.sum_biUnion hdisj]
  apply iSup_le
  intro ell
  rw [haction ell.1]
  apply (enorm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro q₀ hq₀
  exact le_iSup
    (fun k : {k : ℤ // ell₀ ≤ k} ↦
      ‖localizedTailAction scale
        (pStoppingRootSubfamily topScale shift maxDepth S q₀) f k.1 x‖ₑ)
    ell

/-- The p-stopping tree recursion extends to any finite forest in a single
shifted grid, with the same sparse density and coefficient. -/
theorem exists_pStopping_recursive_sparse_bound_forest
    {A p : ℝ} (hlocal : HasOneNodePStoppingGoodPartPairingBound A)
    (hp : 1 < p) (hp2 : p ≤ 2)
    (ell₀ topScale : ℤ) (shift : Fin 3) (maxDepth : ℕ)
    (F : Finset (ℕ × ℤ)) (S : Finset RealInterval) (f g : L0Infinity)
    (hell : 3 ≤ ell₀)
    (hSforest : S ⊆ completeFiniteShiftGridForest topScale shift maxDepth F) :
    ∃ R : Finset RealInterval,
      IsSparse (1 / 4) (↑R : Set RealInterval) ∧
      (∫⁻ x, localizedTailMaximal ell₀
          (finiteShiftGridScale topScale shift) S f x * ‖g x‖ₑ) ≤
        ENNReal.ofReal (A * holderConjugate p) *
          sparseForm p f g (↑R : Set RealInterval) := by
  classical
  let Q := finiteShiftGridRootAddresses F
  let branch := pStoppingRootSubfamily topScale shift maxDepth S
  let scale := finiteShiftGridScale topScale shift
  have hbranchTree : ∀ q₀ ∈ Q,
      branch q₀ ⊆ completeFiniteShiftGridTree topScale shift maxDepth q₀ := by
    intro q₀ hq₀ I hI
    exact (Finset.mem_filter.mp hI).2
  have hunion : Q.biUnion branch = S :=
    pStopping_biUnion_rootSubfamily_eq topScale shift maxDepth F S hSforest
  have hroot (q₀ : ℤ) (hq₀ : q₀ ∈ Q) :=
    exists_pStopping_recursive_sparse_bound hlocal hp hp2 ell₀ topScale shift
      maxDepth q₀ (branch q₀) f g hell (hbranchTree q₀ hq₀)
  choose R hRsparse hRsub hRbound using hroot
  let R' : ℤ → Finset RealInterval :=
    fun q₀ ↦ if hq₀ : q₀ ∈ Q then R q₀ hq₀ else ∅
  have hRsparse' : ∀ q₀ ∈ Q,
      IsSparse (1 / 4) (↑(R' q₀) : Set RealInterval) := by
    intro q₀ hq₀
    simp only [R', dite_eq_left hq₀]
    exact hRsparse q₀ hq₀
  have hRsub' : ∀ q₀ ∈ Q, ∀ I ∈ R' q₀,
      I.carrier ⊆ (finiteShiftGridInterval topScale shift 0 q₀).carrier := by
    intro q₀ hq₀
    simp only [R', dite_eq_left hq₀]
    exact hRsub q₀ hq₀
  have hRbound' : ∀ q₀ ∈ Q,
      (∫⁻ x, localizedTailMaximal ell₀ scale (branch q₀) f x * ‖g x‖ₑ) ≤
        ENNReal.ofReal (A * holderConjugate p) *
          sparseForm p f g (↑(R' q₀) : Set RealInterval) := by
    intro q₀ hq₀
    simp only [R', dite_eq_left hq₀]
    exact hRbound q₀ hq₀
  have hRdisjoint : Set.PairwiseDisjoint (↑Q : Set ℤ) R' := by
    intro q₀ hq₀ q₁ hq₁ hne
    apply Finset.disjoint_left.mpr
    intro I hIq₀ hIq₁
    have hsub₀ := hRsub' q₀ hq₀ I hIq₀
    have hsub₁ := hRsub' q₁ hq₁ I hIq₁
    have hd := finiteShiftGridRootIntervals_pairwiseDisjoint topScale shift hne
    obtain ⟨x, hx⟩ := I.carrier_nonempty
    exact Set.disjoint_left.mp hd (hsub₀ hx) (hsub₁ hx)
  let Rall := Q.biUnion R'
  have hRallSparse : IsSparse (1 / 4) (↑Rall : Set RealInterval) := by
    by_cases hQ : Q.Nonempty
    · let ι := {q₀ : ℤ // q₀ ∈ Q}
      let RF : ι → Set RealInterval := fun q₀ ↦ ↑(R' q₀.1)
      let U : ι → Set ℝ := fun q₀ ↦
        (finiteShiftGridInterval topScale shift 0 q₀.1).carrier
      let _ : Nonempty ι := Set.nonempty_coe_sort.mpr (by simpa using hQ)
      have hU : (Set.univ : Set ι).PairwiseDisjoint U := by
        intro q₀ hq₀ q₁ hq₁ hne
        exact finiteShiftGridRootIntervals_pairwiseDisjoint topScale shift
          (fun h ↦ hne (Subtype.ext h))
      have hRFsub : ∀ q₀ : ι, ∀ I ∈ RF q₀, I.carrier ⊆ U q₀ := by
        intro q₀ I hI
        exact hRsub' q₀.1 q₀.2 I hI
      have hRFsparse : ∀ q₀ : ι, IsSparse (1 / 4) (RF q₀) := by
        intro q₀
        exact hRsparse' q₀.1 q₀.2
      have hu := IsSparse.iUnion_of_disjoint_carriers RF U hU hRFsub hRFsparse
      convert hu using 1
      ext I
      constructor
      · intro hI
        obtain ⟨q₀, hq₀, hIR⟩ := Finset.mem_biUnion.mp hI
        exact Set.mem_iUnion_of_mem ⟨q₀, hq₀⟩ hIR
      · intro hI
        obtain ⟨q₀, hIR⟩ := Set.mem_iUnion.mp hI
        exact Finset.mem_biUnion.mpr ⟨q₀.1, q₀.2, hIR⟩
    · have hQempty : Q = ∅ := Finset.not_nonempty_iff_eq_empty.mp hQ
      simpa [Rall, hQempty] using HardyLittlewoodSparseReduction.isSparse_empty
  have hforms : sparseForm p f g (↑Rall : Set RealInterval) =
      ∑ q₀ ∈ Q, sparseForm p f g (↑(R' q₀) : Set RealInterval) := by
    dsimp only [Rall]
    rw [sparseForm_finset_pStoppingAtom, Finset.sum_biUnion hRdisjoint]
    simp_rw [← sparseForm_finset_pStoppingAtom]
  refine ⟨Rall, hRallSparse, ?_⟩
  calc
    (∫⁻ x, localizedTailMaximal ell₀ scale S f x * ‖g x‖ₑ) ≤
        ∫⁻ x, (∑ q₀ ∈ Q, localizedTailMaximal ell₀ scale
          (branch q₀) f x) * ‖g x‖ₑ := by
      apply lintegral_mono
      intro x
      exact mul_le_mul'
        (pStopping_localizedTailMaximal_le_sum_rootSubfamilies ell₀ topScale shift
          maxDepth Q S f hunion x) le_rfl
    _ = ∑ q₀ ∈ Q,
        ∫⁻ x, localizedTailMaximal ell₀ scale (branch q₀) f x * ‖g x‖ₑ := by
      simp_rw [Finset.sum_mul]
      apply lintegral_finsetSum
      intro q₀ hq₀
      exact (measurable_localizedTailMaximal ell₀ scale (branch q₀)
        f.measurable_toFun).mul g.measurable_toFun.enorm
    _ ≤ ∑ q₀ ∈ Q, ENNReal.ofReal (A * holderConjugate p) *
        sparseForm p f g (↑(R' q₀) : Set RealInterval) := by
      exact Finset.sum_le_sum fun q₀ hq₀ ↦ hRbound' q₀ hq₀
    _ = ENNReal.ofReal (A * holderConjugate p) *
        sparseForm p f g (↑Rall : Set RealInterval) := by
      rw [hforms, Finset.mul_sum]

/-- Operator-facing form of the one-tree p-stopping closure. -/
theorem hasSparseOnePBound_localizedTailMaximalTestOperator_of_pStopping_tree
    {A p : ℝ} (hlocal : HasOneNodePStoppingGoodPartPairingBound A)
    (hp : 1 < p) (hp2 : p ≤ 2)
    (ell₀ topScale : ℤ) (shift : Fin 3) (maxDepth : ℕ) (q₀ : ℤ)
    (S : Finset RealInterval)
    (hStree : S ⊆ completeFiniteShiftGridTree topScale shift maxDepth q₀)
    (hell : 3 ≤ ell₀) :
    HasSparseOnePBound (A * holderConjugate p) p
      (localizedTailMaximalTestOperator ell₀
        (finiteShiftGridScale topScale shift) S) := by
  intro f g
  obtain ⟨R, hRsparse, hRsub, hpair⟩ := exists_pStopping_recursive_sparse_bound
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

/-- Operator-facing form of the finite-forest p-stopping closure. -/
theorem hasSparseOnePBound_localizedTailMaximalTestOperator_of_pStopping_forest
    {A p : ℝ} (hlocal : HasOneNodePStoppingGoodPartPairingBound A)
    (hp : 1 < p) (hp2 : p ≤ 2)
    (ell₀ topScale : ℤ) (shift : Fin 3) (maxDepth : ℕ)
    (F : Finset (ℕ × ℤ)) (S : Finset RealInterval)
    (hSforest : S ⊆ completeFiniteShiftGridForest topScale shift maxDepth F)
    (hell : 3 ≤ ell₀) :
    HasSparseOnePBound (A * holderConjugate p) p
      (localizedTailMaximalTestOperator ell₀
        (finiteShiftGridScale topScale shift) S) := by
  intro f g
  obtain ⟨R, hRsparse, hpair⟩ := exists_pStopping_recursive_sparse_bound_forest
    hlocal hp hp2 ell₀ topScale shift maxDepth F S f g hell hSforest
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
end KrauseLaceyPStoppingPositiveClosure
end QuadraticCarleson
