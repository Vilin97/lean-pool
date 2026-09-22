/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Sol
-/
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Ideals.StandardInstances
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Instances

/-! # Ky Fan Norm -/

open TauCeti.DavisKahan.Sylvester

/-!
# Ky Fan norms inside the Davis--Kahan source norm class

The source-facing class `SymmetricNormingFunction` is quantified over coherent
normalized symmetric norms in every finite dimension.  Fan dominance gives the
forward implication

`(forall k, KF_k(A) <= KF_k(B)) -> (forall N, N(A) <= N(B))`.

For source-faithfulness we also need the converse: each positive-index Ky Fan
norm is itself one of the coherent source norms.  This module constructs that
member, proves that its canonical infinite-dimensional extension is exactly the
Ky Fan approximation gauge, and packages the resulting converse.

The construction uses the already-proved finite-dimensional rectangular Ky Fan
seminorm.  The only genuinely new coherence fact is that adjoining a zero
coordinate leaves its gauge unchanged.  We prove that by sorting the absolute
values, extending the sorting permutation by the identity on the new coordinate,
and using the existing zero-padding theorem for prefix sums.
-/

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace BigOperators ENNReal

noncomputable section

universe u v

/-- Extend a permutation of `Fin n` to `Fin (n + 1)` by fixing the new last
coordinate. -/
noncomputable def zeroPadPerm {n : ℕ} (pi : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin (n + 1)) :=
  finSumFinEquiv.symm.trans
    ((Equiv.sumCongr pi (Equiv.refl (Fin 1))).trans finSumFinEquiv)

/-- The zero-padding permutation fixes the original block. -/
@[simp]
theorem zeroPadPerm_castAdd {n : ℕ} (pi : Equiv.Perm (Fin n)) (i : Fin n) :
    zeroPadPerm pi (Fin.castAdd 1 i) = Fin.castAdd 1 (pi i) := by
  simp [zeroPadPerm]

/-- The zero-padding permutation sends the padded block past the original. -/
@[simp]
theorem zeroPadPerm_natAdd {n : ℕ} (pi : Equiv.Perm (Fin n)) (i : Fin 1) :
    zeroPadPerm pi (Fin.natAdd n i) = Fin.natAdd n i := by
  simp [zeroPadPerm]

/-- Zero-padding commutes with extending a permutation by the identity. -/
theorem zeroPadRight_comp_zeroPadPerm {n : ℕ}
    (pi : Equiv.Perm (Fin n)) (x : Fin n → ℝ) :
    FiniteVector.zeroPadRight (m := 1) x ∘ zeroPadPerm pi =
      FiniteVector.zeroPadRight (m := 1) (x ∘ pi) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [Function.comp_apply, zeroPadPerm, FiniteVector.zeroPadRight]
  · simp [Function.comp_apply, zeroPadPerm, FiniteVector.zeroPadRight]

/-- The finite square Ky Fan `k` seminorm used to build the coherent paper
norm.  For `k` larger than the dimension the extra singular values are zero. -/
noncomputable def kyFanFiniteNorm (k n : ℕ) :
    TauCeti.UnitarilyInvariantSeminorm ℂ (EuclideanSpace ℂ (Fin n)) (EuclideanSpace ℂ (Fin n)) :=
  (TauCeti.UnitarilyInvariantSeminorm.kyFan
      (𝕜 := ℂ) (E := EuclideanSpace ℂ (Fin n))
      (F := EuclideanSpace ℂ (Fin n)) k)

/-- On an antitone nonnegative vector, the finite Ky Fan gauge is literally the
corresponding prefix sum. -/
theorem kyFanFiniteNorm_gauge_of_antitone_nonneg
    (k n : ℕ) (x : Fin n → ℝ) (hxanti : Antitone x)
    (hx0 : ∀ i, 0 ≤ x i) :
    (kyFanFiniteNorm k n).gauge
        (EuclideanSpace.basisFun (Fin n) ℂ) x =
      FiniteVector.prefixSum k x := by
  let b := EuclideanSpace.basisFun (Fin n) ℂ
  change TauCeti.kyFanSum k
      (TauCeti.diagOp b x) = FiniteVector.prefixSum k x
  rcases le_total k n with hkn | hnk
  · have hprefix :
        FiniteVector.prefixSum k x =
          ∑ i : Fin k, x ⟨i, lt_of_lt_of_le i.isLt hkn⟩ := by
      unfold FiniteVector.prefixSum
      let f : ℕ → ℝ := fun m => if hm : m < n then x ⟨m, hm⟩ else 0
      calc
        ∑ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) < k), x j =
            ∑ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) < k),
              f (j : ℕ) := by
                apply Finset.sum_congr rfl
                intro j hj
                simp [f, j.isLt]
        _ = ∑ i : Fin k, f (i : ℕ) :=
          TauCeti.sum_filter_lt_eq_sum_fin hkn f
        _ = ∑ i : Fin k, x ⟨i, lt_of_lt_of_le i.isLt hkn⟩ := by
          apply Finset.sum_congr rfl
          intro i hi
          simp [f, lt_of_lt_of_le i.isLt hkn]
    rw [hprefix]
    unfold TauCeti.kyFanSum
    apply Finset.sum_congr rfl
    intro i hi
    exact TauCeti.singularValues_diagOp
      (𝕜 := ℂ) (E := EuclideanSpace ℂ (Fin n))
      finrank_euclideanSpace_fin b hxanti hx0
      ⟨i, lt_of_lt_of_le i.isLt hkn⟩
  · have hstab :=
      TauCeti.kyFanSum_eq_of_finrank_le (k := k) (by simpa using hnk) (TauCeti.diagOp b x)
    rw [hstab]
    rw [finrank_euclideanSpace_fin]
    rw [FiniteVector.prefixSum_eq_full_sum_of_le x hnk]
    unfold TauCeti.kyFanSum
    apply Finset.sum_congr rfl
    intro i hi
    exact TauCeti.singularValues_diagOp
      (𝕜 := ℂ) (E := EuclideanSpace ℂ (Fin n))
      finrank_euclideanSpace_fin b hxanti hx0 i

/-- The finite Ky Fan gauges are coherent under appending a zero coordinate. -/
theorem kyFanFiniteNorm_zeroPad (k n : ℕ) (x : Fin n → ℝ) :
    (kyFanFiniteNorm k (n + 1)).gauge
        (EuclideanSpace.basisFun (Fin (n + 1)) ℂ) (zeroPad x) =
      (kyFanFiniteNorm k n).gauge
        (EuclideanSpace.basisFun (Fin n) ℂ) x := by
  let absx : Fin n → ℝ := fun i => |x i|
  let pi : Equiv.Perm (Fin n) :=
    TauCeti.FiniteSymmetricGauge.antitoneSortPerm absx
  let y : Fin n → ℝ := absx ∘ pi
  have hyanti : Antitone y :=
    TauCeti.FiniteSymmetricGauge.antitone_comp_antitoneSortPerm absx
  have hy0 : ∀ i, 0 ≤ y i := fun i => abs_nonneg _
  have hpadyanti : Antitone (FiniteVector.zeroPadRight (m := 1) y) :=
    FiniteVector.antitone_zeroPadRight hyanti hy0
  have hpady0 : ∀ i, 0 ≤ FiniteVector.zeroPadRight (m := 1) y i :=
    FiniteVector.zeroPadRight_nonneg hy0

  have hsmall :
      (kyFanFiniteNorm k n).gauge
          (EuclideanSpace.basisFun (Fin n) ℂ) y =
        (kyFanFiniteNorm k n).gauge
          (EuclideanSpace.basisFun (Fin n) ℂ) x := by
    calc
      (kyFanFiniteNorm k n).gauge
          (EuclideanSpace.basisFun (Fin n) ℂ) y =
          (kyFanFiniteNorm k n).gauge
            (EuclideanSpace.basisFun (Fin n) ℂ) absx := by
        exact (kyFanFiniteNorm k n).gauge_perm
          (EuclideanSpace.basisFun (Fin n) ℂ) absx pi
      _ = (kyFanFiniteNorm k n).gauge
            (EuclideanSpace.basisFun (Fin n) ℂ) x := by
        exact uinGauge_abs (kyFanFiniteNorm k n)
          (EuclideanSpace.basisFun (Fin n) ℂ) x

  have habspad :
      (fun i : Fin (n + 1) => |FiniteVector.zeroPadRight (m := 1) x i|) =
        FiniteVector.zeroPadRight (m := 1) absx := by
    funext i
    unfold FiniteVector.zeroPadRight absx
    split_ifs <;> simp

  have hpermPad :
      (fun i : Fin (n + 1) => |FiniteVector.zeroPadRight (m := 1) x i|) ∘
          zeroPadPerm pi =
        FiniteVector.zeroPadRight (m := 1) y := by
    rw [habspad, zeroPadRight_comp_zeroPadPerm]

  rw [SymmetricIdeal.zeroPad_eq_zeroPadRight]
  calc
    (kyFanFiniteNorm k (n + 1)).gauge
        (EuclideanSpace.basisFun (Fin (n + 1)) ℂ)
        (FiniteVector.zeroPadRight (m := 1) x) =
      (kyFanFiniteNorm k (n + 1)).gauge
        (EuclideanSpace.basisFun (Fin (n + 1)) ℂ)
        (fun i => |FiniteVector.zeroPadRight (m := 1) x i|) := by
          exact (uinGauge_abs (kyFanFiniteNorm k (n + 1))
            (EuclideanSpace.basisFun (Fin (n + 1)) ℂ)
            (FiniteVector.zeroPadRight (m := 1) x)).symm
    _ = (kyFanFiniteNorm k (n + 1)).gauge
        (EuclideanSpace.basisFun (Fin (n + 1)) ℂ)
        (((fun i => |FiniteVector.zeroPadRight (m := 1) x i|) ∘
          zeroPadPerm pi)) := by
          exact ((kyFanFiniteNorm k (n + 1)).gauge_perm
            (EuclideanSpace.basisFun (Fin (n + 1)) ℂ)
            (fun i => |FiniteVector.zeroPadRight (m := 1) x i|)
            (zeroPadPerm pi)).symm
    _ = (kyFanFiniteNorm k (n + 1)).gauge
        (EuclideanSpace.basisFun (Fin (n + 1)) ℂ)
        (FiniteVector.zeroPadRight (m := 1) y) := by rw [hpermPad]
    _ = FiniteVector.prefixSum k (FiniteVector.zeroPadRight (m := 1) y) :=
      kyFanFiniteNorm_gauge_of_antitone_nonneg k (n + 1)
        _ hpadyanti hpady0
    _ = FiniteVector.prefixSum k y :=
      FiniteVector.prefixSum_zeroPadRight k y
    _ = (kyFanFiniteNorm k n).gauge
        (EuclideanSpace.basisFun (Fin n) ℂ) y :=
      (kyFanFiniteNorm_gauge_of_antitone_nonneg k n y hyanti hy0).symm
    _ = (kyFanFiniteNorm k n).gauge
        (EuclideanSpace.basisFun (Fin n) ℂ) x := hsmall

/-- The Ky Fan `k` norm, for positive `k`, as an actual member of the coherent
Davis--Kahan source norm class. -/
noncomputable def kyFanNormingFunction (k : ℕ) (hk : 0 < k) :
    SymmetricNormingFunction where
  finiteNorm := kyFanFiniteNorm k
  normalized := by
    rw [kyFanFiniteNorm_gauge_of_antitone_nonneg k 1]
    · rw [FiniteVector.prefixSum_eq_full_sum_of_le (fun _ : Fin 1 => (1 : ℝ))]
      · simp
      · omega
    · intro i j hij
      simp
    · intro i
      norm_num
  zero_pad := by
    intro n x
    exact kyFanFiniteNorm_zeroPad k n x

/-- The finite prefix of `kyFanNormingFunction k` is the Ky Fan gauge at the shorter
of `k` and the available prefix length. -/
theorem kyFanNormingFunction_prefixGauge
    {𝕜 : Type u} [RCLike 𝕜]
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (k : ℕ) (hk : 0 < k) (n : ℕ) (A : E →L[𝕜] F) :
    (kyFanNormingFunction k hk).prefixGauge n A =
      kyFanApproximationGauge (min k n) A := by
  rw [SymmetricNormingFunction.prefixGauge]
  unfold SymmetricNormingFunction.finiteGauge kyFanNormingFunction
  rw [kyFanFiniteNorm_gauge_of_antitone_nonneg]
  · rcases le_total k n with hkn | hnk
    · rw [min_eq_left hkn]
      unfold FiniteVector.prefixSum
      simp only [SymmetricNormingFunction.approximationPrefix]
      rw [TauCeti.sum_filter_lt_eq_sum_fin hkn
        (fun m => approximationSingularValue m A)]
      simpa only [SymmetricNormingFunction.approximationPrefix] using
        (SymmetricNormingFunction.sum_approximationPrefix k A)
    · rw [min_eq_right hnk]
      rw [FiniteVector.prefixSum_eq_full_sum_of_le _ hnk]
      exact SymmetricNormingFunction.sum_approximationPrefix n A
  · intro i j hij
    exact approximationSingularValue_antitone A (Fin.le_def.mp hij)
  · intro i
    exact approximationSingularValue_nonneg _ _

private theorem kyFanApproximationGauge_mono_length_local
    {𝕜 : Type u} [RCLike 𝕜]
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] 
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] 
    (A : E →L[𝕜] F) {m k : ℕ} (hmk : m ≤ k) :
    kyFanApproximationGauge m A ≤ kyFanApproximationGauge k A := by
  unfold kyFanApproximationGauge ContinuousLinearMap.kyFanGauge
  rw [← Finset.sum_range_add_sum_Ico
    (f := fun n => A.approximationNumber n) hmk]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun n _ =>
    A.approximationNumber_nonneg n)

/-- The canonical infinite-dimensional extension of `kyFanNormingFunction k` is
exactly the Ky Fan approximation gauge. -/
theorem kyFanNormingFunction_extendedGauge
    {𝕜 : Type u} [RCLike 𝕜]
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (k : ℕ) (hk : 0 < k) (A : E →L[𝕜] F) :
    (kyFanNormingFunction k hk).extendedGauge A =
      ENNReal.ofReal (kyFanApproximationGauge k A) := by
  apply le_antisymm
  · rw [SymmetricNormingFunction.extendedGauge]
    apply iSup_le
    intro n
    rw [kyFanNormingFunction_prefixGauge]
    exact ENNReal.ofReal_le_ofReal
      (kyFanApproximationGauge_mono_length_local A (min_le_left k n))
  · rw [SymmetricNormingFunction.extendedGauge]
    refine le_trans ?_ (le_iSup
      (fun n : ℕ => ENNReal.ofReal ((kyFanNormingFunction k hk).prefixGauge n A)) k)
    rw [kyFanNormingFunction_prefixGauge, min_self]

/-- Every bounded operator belongs to a Ky Fan source norm, since a finite Ky
Fan prefix is always finite. -/
theorem kyFanNormingFunction_mem
    {𝕜 : Type u} [RCLike 𝕜]
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (k : ℕ) (hk : 0 < k) (A : E →L[𝕜] F) :
    (kyFanNormingFunction k hk).Mem A := by
  rw [SymmetricNormingFunction.Mem, kyFanNormingFunction_extendedGauge]
  exact ENNReal.ofReal_ne_top

/-- The real-valued source gauge of `kyFanNormingFunction k` is exactly the Ky Fan
approximation gauge. -/
theorem kyFanNormingFunction_gauge
    {𝕜 : Type u} [RCLike 𝕜]
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (k : ℕ) (hk : 0 < k) (A : E →L[𝕜] F) :
    (kyFanNormingFunction k hk).gauge A = kyFanApproximationGauge k A := by
  rw [SymmetricNormingFunction.gauge, kyFanNormingFunction_extendedGauge,
    ENNReal.toReal_ofReal (kyFanApproximationGauge_nonneg k A)]

/-- **Converse Ky Fan principle for the source class.**  If every coherent
Davis--Kahan source norm of `A` is at most the corresponding norm of `B`, then
every Ky Fan prefix of `A` is at most that of `B`.

Together with `SymmetricNormingFunction.extendedGauge_le_of_all_kyFan_le`, this
shows that the universal source-norm order is exactly weak Ky Fan majorization. -/
theorem all_kyFan_le_of_every_ext_finiteGaugeendedGauge_le
    {𝕜 : Type u} [RCLike 𝕜]
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    {A B : E →L[𝕜] F}
    (h : ∀ N : SymmetricNormingFunction, N.extendedGauge A ≤ N.extendedGauge B) :
    ∀ k : ℕ, kyFanApproximationGauge k A ≤ kyFanApproximationGauge k B := by
  intro k
  by_cases hk0 : k = 0
  · subst k
    simp [kyFanApproximationGauge, ContinuousLinearMap.kyFanGauge_zero_index]
  · have hk : 0 < k := Nat.pos_of_ne_zero hk0
    have hN := h (kyFanNormingFunction k hk)
    rw [kyFanNormingFunction_extendedGauge, kyFanNormingFunction_extendedGauge] at hN
    exact (ENNReal.ofReal_le_ofReal_iff (kyFanApproximationGauge_nonneg k B)).mp hN

/-- Real-valued scaled converse, in the form most useful to source-facing
Davis--Kahan inequalities. -/
theorem all_mul_kyFan_le_of_every_symmetricNorming_gauge_le
    {𝕜 : Type u} [RCLike 𝕜]
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    {A B : E →L[𝕜] F} {c : ℝ}
    (h : ∀ N : SymmetricNormingFunction, c * N.gauge A ≤ N.gauge B) :
    ∀ k : ℕ, c * kyFanApproximationGauge k A ≤ kyFanApproximationGauge k B := by
  intro k
  by_cases hk0 : k = 0
  · subst k
    simp [kyFanApproximationGauge, ContinuousLinearMap.kyFanGauge_zero_index]
  · have hk : 0 < k := Nat.pos_of_ne_zero hk0
    simpa [kyFanNormingFunction_gauge] using h (kyFanNormingFunction k hk)

end

end ExactSinTheta
end DavisKahan
end TauCeti
