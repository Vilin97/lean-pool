/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/
module


public import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyPStoppingRecursion
public import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyNativePositiveForestClosure

/-!
# Positive one-node interface with genuine `p`-monitor stopping

The good collection below is formed with `pStoppingMonitor g p hp`, while
the pairing remains against the original `g`.
-/

@[expose] public section

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
      (↑(insert I ((stoppingChildren S f monitor I).biUnion R)) : Set RealInterval) :=
  KrauseLaceyNativePositiveSuffixClosure.isSparse_insert_root_biUnion
    I hf hm hlam R hRsparse hRsub

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
  apply KrauseLaceyNativePositiveForestClosure.exists_sparse_bound_forest_of_tree_witnesses
    ell₀ topScale shift maxDepth F S f g hSforest
  intro q₀ T hT
  exact exists_pStopping_recursive_sparse_bound hlocal hp hp2 ell₀ topScale shift
    maxDepth q₀ T f g hell hT

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
  exact (operatorPairing_localizedTailMaximalTestOperator_le ell₀
    (finiteShiftGridScale topScale shift) S f g).trans hpair

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
  exact (operatorPairing_localizedTailMaximalTestOperator_le ell₀
    (finiteShiftGridScale topScale shift) S f g).trans hpair


end
end KrauseLaceyPStoppingPositiveClosure
end QuadraticCarleson
