/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/
module


public import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyNativePositiveSuffixClosure

/-!
# Native positive sparse closure on a finite shifted forest

The one-node Krause--Lacey estimate has already been iterated down one
complete shifted tree. This module performs the next exact structural step:
split a finite forest into its depth-zero roots, apply that tree recursion on
each component, and unite the resulting sparse families. Distinct roots in
one shifted grid have disjoint carriers, so the sparsity density and analytic
constant are unchanged.
-/

@[expose] public section

open Function MeasureTheory Set
open scoped ENNReal NNReal

namespace QuadraticCarleson
namespace KrauseLaceyNativePositiveForestClosure

open KrauseLaceyNativePositiveSuffixClosure KrauseLaceyStoppingRecursion
open KrauseLaceyThreeShiftGrid


noncomputable
section

/-- Classical decidable equality for the finite interval families used in the forest
construction. -/
local instance : DecidableEq RealInterval := Classical.decEq _

private noncomputable def rootSubfamily
    (topScale : ℤ) (shift : Fin 3) (maxDepth : ℕ)
    (S : Finset RealInterval) (q₀ : ℤ) : Finset RealInterval :=
  S.filter fun I ↦ I ∈ completeFiniteShiftGridTree topScale shift maxDepth q₀

private theorem rootSubfamilies_pairwiseDisjoint
    (topScale : ℤ) (shift : Fin 3) (maxDepth : ℕ)
    (Q : Finset ℤ) (S : Finset RealInterval) :
    Set.PairwiseDisjoint (↑Q : Set ℤ)
      (rootSubfamily topScale shift maxDepth S) := by
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

private theorem biUnion_rootSubfamily_eq
    (topScale : ℤ) (shift : Fin 3) (maxDepth : ℕ)
    (F : Finset (ℕ × ℤ)) (S : Finset RealInterval)
    (hS : S ⊆ completeFiniteShiftGridForest topScale shift maxDepth F) :
    (finiteShiftGridRootAddresses F).biUnion
        (rootSubfamily topScale shift maxDepth S) = S := by
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
    apply Finset.mem_biUnion.mpr
    exact ⟨q₀, hq₀, Finset.mem_filter.mpr ⟨hI, hIq₀⟩⟩

private theorem localizedTailMaximal_le_sum_rootSubfamilies
    (ell₀ topScale : ℤ) (shift : Fin 3) (maxDepth : ℕ)
    (Q : Finset ℤ) (S : Finset RealInterval) (f : ℝ → ℂ)
    (hunion : Q.biUnion (rootSubfamily topScale shift maxDepth S) = S)
    (x : ℝ) :
    localizedTailMaximal ell₀ (finiteShiftGridScale topScale shift) S f x ≤
      ∑ q₀ ∈ Q, localizedTailMaximal ell₀
        (finiteShiftGridScale topScale shift)
        (rootSubfamily topScale shift maxDepth S q₀) f x := by
  classical
  let scale := finiteShiftGridScale topScale shift
  have hdisj := rootSubfamilies_pairwiseDisjoint topScale shift maxDepth Q S
  have haction (ell : ℤ) :
      localizedTailAction scale S f ell x =
        ∑ q₀ ∈ Q,
          localizedTailAction scale
            (rootSubfamily topScale shift maxDepth S q₀) f ell x := by
    calc
      localizedTailAction scale S f ell x =
          localizedTailAction scale
            (Q.biUnion (rootSubfamily topScale shift maxDepth S)) f ell x := by
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
        (rootSubfamily topScale shift maxDepth S q₀) f k.1 x‖ₑ)
    ell

/-- The checked one-tree recursion extends to an arbitrary finite forest in
one shifted grid. The sparse witness is the disjoint union of the rootwise
witnesses, so neither its `1 / 4` density nor its coefficient is degraded. -/
theorem exists_recursive_sparse_bound_forest
    {A p : ℝ} (hlocal : HasOneNodeGoodPartPairingBound A)
    (hp : 1 < p) (hp2 : p < 2)
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
  let branch := rootSubfamily topScale shift maxDepth S
  let scale := finiteShiftGridScale topScale shift
  have hbranchTree : ∀ q₀ ∈ Q,
      branch q₀ ⊆ completeFiniteShiftGridTree topScale shift maxDepth q₀ := by
    intro q₀ hq₀ I hI
    exact (Finset.mem_filter.mp hI).2
  have hunion : Q.biUnion branch = S := by
    exact biUnion_rootSubfamily_eq topScale shift maxDepth F S hSforest
  have hbranchDisjoint : Set.PairwiseDisjoint (↑Q : Set ℤ) branch := by
    exact rootSubfamilies_pairwiseDisjoint topScale shift maxDepth Q S
  have hroot (q₀ : ℤ) (hq₀ : q₀ ∈ Q) :=
    exists_recursive_sparse_bound hlocal hp hp2 ell₀ topScale shift maxDepth q₀
      (branch q₀) f g hell (hbranchTree q₀ hq₀)
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
    rw [sparseForm_finset, Finset.sum_biUnion hRdisjoint]
    simp_rw [← sparseForm_finset]
  refine ⟨Rall, hRallSparse, ?_⟩
  calc
    (∫⁻ x, localizedTailMaximal ell₀ scale S f x * ‖g x‖ₑ) ≤
        ∫⁻ x, (∑ q₀ ∈ Q, localizedTailMaximal ell₀ scale
          (branch q₀) f x) * ‖g x‖ₑ := by
      apply lintegral_mono
      intro x
      exact mul_le_mul'
        (localizedTailMaximal_le_sum_rootSubfamilies ell₀ topScale shift maxDepth
          Q S f hunion x) le_rfl
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

/-- Operator-facing form of the finite-forest closure. -/
theorem hasSparseOnePBound_localizedTailMaximalTestOperator_of_forest
    {A p : ℝ} (hlocal : HasOneNodeGoodPartPairingBound A)
    (hp : 1 < p) (hp2 : p < 2)
    (ell₀ topScale : ℤ) (shift : Fin 3) (maxDepth : ℕ)
    (F : Finset (ℕ × ℤ)) (S : Finset RealInterval)
    (hSforest : S ⊆ completeFiniteShiftGridForest topScale shift maxDepth F)
    (hell : 3 ≤ ell₀) :
    HasSparseOnePBound (A * holderConjugate p) p
      (localizedTailMaximalTestOperator ell₀
        (finiteShiftGridScale topScale shift) S) := by
  intro f g
  obtain ⟨R, hRsparse, hpair⟩ := exists_recursive_sparse_bound_forest
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
end KrauseLaceyNativePositiveForestClosure
end QuadraticCarleson
