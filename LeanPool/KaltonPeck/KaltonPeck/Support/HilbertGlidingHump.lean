/-
Copyright (c) 2026 Avik Das. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Avik Das
-/
module

/-
Copyright (c) 2026 adas1236. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: adas1236
-/
public import LeanPool.KaltonPeck.KaltonPeck.Support.CgpBlockExtraction

/-!
# Hilbert-space gliding-hump arguments

This file constructs successive normalized finite-support blocks approximating vectors in
infinite-dimensional Hilbert subspaces and coordinatewise-null sequences, together with uniform
signed-average estimates.
-/

@[expose] public section


namespace KaltonPeck.Support.HilbertGlidingHump

noncomputable
section

open Coordinates Symplectic
open Filter Function
open scoped Topology

private def l2Basis (n : ℕ) : CanonicalL2 :=
  lp.single 2 n 1

private def l2Head (N : ℕ) : Submodule ℝ CanonicalL2 :=
  Submodule.span ℝ (Set.range fun i : Fin N => l2Basis i)

private instance instFiniteDimensionalL2Head (N : ℕ) :
    FiniteDimensional ℝ (l2Head N) :=
  FiniteDimensional.span_of_finite ℝ (Set.finite_range _)

private lemma mem_l2Head_orthogonal_iff (N : ℕ) (x : CanonicalL2) :
    x ∈ (l2Head N)ᗮ ↔ ∀ k < N, x k = 0 := by
  constructor
  · intro hx k hk
    have heb : l2Basis k ∈ l2Head N := by
      apply Submodule.subset_span
      exact ⟨⟨k, hk⟩, rfl⟩
    have hi := Submodule.inner_right_of_mem_orthogonal heb hx
    simpa only [l2Basis, lp.inner_single_left, RCLike.inner_apply, conj_trivial,
      mul_one] using hi
  · intro hx
    rw [Submodule.mem_orthogonal]
    intro u hu
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hu
    · rintro y ⟨i, rfl⟩
      simp only [l2Basis, lp.inner_single_left, RCLike.inner_apply, conj_trivial,
        mul_one, hx i i.isLt]
    · exact inner_zero_left _
    · intro y z _ _ hy hz
      rw [inner_add_left, hy, hz, add_zero]
    · intro c y _ hy
      rw [inner_smul_left, hy, mul_zero]

private def l2Trunc (m : ℕ) (x : CanonicalL2) : CanonicalL2 :=
  ∑ k ∈ Finset.range m, lp.single 2 k (x k)

private lemma l2Trunc_apply (m k : ℕ) (x : CanonicalL2) :
    l2Trunc m x k = if k < m then x k else 0 := by
  rw [l2Trunc]
  change
    (lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 k)
        (∑ i ∈ Finset.range m, lp.single 2 i (x i)) =
      if k < m then x k else 0
  rw [map_sum]
  simp [lp.evalCLM, lp.single_apply, Pi.single_apply]

private lemma l2Trunc_tendsto (x : CanonicalL2) :
    Tendsto (fun m => l2Trunc m x) atTop (𝓝 x) :=
  (lp.hasSum_single (p := (2 : ENNReal)) (by norm_num) x).tendsto_sum_nat

private lemma l2Norm_coe_eq_norm (x : CanonicalL2) :
    l2Norm (fun n => x n) = ‖x‖ := by
  rw [lp.norm_eq_tsum_rpow (p := (2 : ENNReal)) (by norm_num)]
  change Real.sqrt (∑' n, x n ^ 2) =
    (∑' n, |x n| ^ (2 : ℝ)) ^ (1 / (2 : ℝ))
  rw [Real.sqrt_eq_rpow]
  congr 1
  apply tsum_congr
  intro n
  calc
    x n ^ (2 : ℕ) = |x n| ^ (2 : ℕ) := (sq_abs (x n)).symm
    _ = |x n| ^ (2 : ℝ) := (Real.rpow_natCast |x n| 2).symm

/-- Every infinite-dimensional subspace of the canonical Hilbert space contains a unit vector
whose prescribed finite coordinate head vanishes. -/
theorem exists_unit_tail
    (M : Submodule ℝ CanonicalL2) (hM : ¬ FiniteDimensional ℝ M)
    (N : ℕ) :
    ∃ y : M, ‖y‖ = 1 ∧ ∀ k < N, (y : CanonicalL2) k = 0 := by
  let P : M →L[ℝ] l2Head N :=
    (l2Head N).orthogonalProjectionOnto.domRestrict M
  have hker : ¬ FiniteDimensional ℝ P.toLinearMap.ker := by
    intro hkerFinite
    let : FiniteDimensional ℝ P.toLinearMap.ker := hkerFinite
    obtain ⟨C, hcompl⟩ := P.toLinearMap.ker.exists_isCompl
    have hCinj : Function.Injective (P.toLinearMap.domRestrict C) := by
      intro x y hxy
      apply Subtype.ext
      have hxyKer : (x : M) - (y : M) ∈ P.toLinearMap.ker := by
        change P ((x : M) - (y : M)) = 0
        rw [map_sub, sub_eq_zero]
        exact hxy
      have hxyC : (x : M) - (y : M) ∈ C :=
        C.sub_mem x.property y.property
      have hzero : (x : M) - (y : M) ∈ (⊥ : Submodule ℝ M) :=
        hcompl.disjoint.le_bot ⟨hxyKer, hxyC⟩
      simpa only [Submodule.mem_bot, sub_eq_zero] using hzero
    let : FiniteDimensional ℝ C :=
      FiniteDimensional.of_injective (P.toLinearMap.domRestrict C) hCinj
    have hprod : FiniteDimensional ℝ (P.toLinearMap.ker × C) := inferInstance
    let : FiniteDimensional ℝ M :=
      @LinearEquiv.finiteDimensional ℝ (P.toLinearMap.ker × C) _ _ _
        M _ _ (Submodule.prodEquivOfIsCompl _ _ hcompl) hprod
    exact hM inferInstance
  have hkerNe : P.toLinearMap.ker ≠ ⊥ := by
    intro hbot
    apply hker
    rw [hbot]
    infer_instance
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff P.toLinearMap.ker).mp hkerNe
  let y : M := ‖x‖⁻¹ • x
  have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  refine ⟨y, ?_, ?_⟩
  · dsimp only [y]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg x),
      inv_mul_cancel₀ hxnorm.ne']
  · have hyker : P y = 0 := by
      dsimp only [y]
      rw [map_smul, show P x = 0 from hx, smul_zero]
    have hperp : (y : CanonicalL2) ∈ (l2Head N)ᗮ := by
      exact Submodule.orthogonalProjectionOnto_eq_zero_iff.mp hyker
    exact (mem_l2Head_orthogonal_iff N (y : CanonicalL2)).mp hperp

private lemma norm_sub_normalize
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (z : E) (hz : 0 < ‖z‖) :
    ‖z - ‖z‖⁻¹ • z‖ = |‖z‖ - 1| := by
  have hsub : z - ‖z‖⁻¹ • z = (1 - ‖z‖⁻¹) • z := by
    rw [sub_smul, one_smul]
  rw [hsub, norm_smul, Real.norm_eq_abs]
  calc
    |1 - ‖z‖⁻¹| * ‖z‖ = |(1 - ‖z‖⁻¹) * ‖z‖| := by
      rw [abs_mul, abs_of_nonneg (norm_nonneg z)]
    _ = |‖z‖ - 1| := by
      congr 1
      field_simp

private structure FiniteApproxBlock
    (M : Submodule ℝ CanonicalL2) (start : ℕ) (ε : ℝ) where
  stop : ℕ
  y : M
  vec : CanonicalL2
  start_lt_stop : start < stop
  norm_y : ‖y‖ = 1
  norm_vec : ‖vec‖ = 1
  support_finite : Set.Finite {k | vec k ≠ 0}
  support_nonempty : Set.Nonempty {k | vec k ≠ 0}
  support_lower : ∀ k, vec k ≠ 0 → start ≤ k
  support_upper : ∀ k, vec k ≠ 0 → k < stop
  approx : ‖(y : CanonicalL2) - vec‖ < ε

private lemma exists_finiteApproxBlock
    (M : Submodule ℝ CanonicalL2) (hM : ¬ FiniteDimensional ℝ M)
    (start : ℕ) {ε : ℝ} (hε : 0 < ε) :
    Nonempty (FiniteApproxBlock M start ε) := by
  obtain ⟨u, huNorm, huTail⟩ := exists_unit_tail M hM start
  let η : ℝ := min (1 / 4 : ℝ) (ε / 4)
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  have hηQuarter : η ≤ 1 / 4 := min_le_left _ _
  have hηEps : η ≤ ε / 4 := min_le_right _ _
  obtain ⟨N, hN⟩ :=
    Metric.tendsto_atTop.mp (l2Trunc_tendsto (u : CanonicalL2)) η hη
  let stop : ℕ := max N (start + 1)
  have hstopN : N ≤ stop := Nat.le_max_left _ _
  have hstartStop : start < stop :=
    lt_of_lt_of_le (Nat.lt_succ_self start) (Nat.le_max_right _ _)
  let z : CanonicalL2 := l2Trunc stop (u : CanonicalL2)
  have hzCloseDist : dist z (u : CanonicalL2) < η := hN stop hstopN
  have hzClose : ‖z - (u : CanonicalL2)‖ < η := by
    simpa only [dist_eq_norm] using hzCloseDist
  have hNormLower : 3 / 4 < ‖z‖ := by
    have htri : ‖(u : CanonicalL2)‖ ≤
        ‖(u : CanonicalL2) - z‖ + ‖z‖ := by
      calc
        ‖(u : CanonicalL2)‖ = ‖((u : CanonicalL2) - z) + z‖ := by
          rw [sub_add_cancel]
        _ ≤ ‖(u : CanonicalL2) - z‖ + ‖z‖ := norm_add_le _ _
    have hzCloseRev : ‖(u : CanonicalL2) - z‖ < η := by
      simpa only [norm_sub_rev] using hzClose
    have huNorm' : ‖(u : CanonicalL2)‖ = 1 := huNorm
    nlinarith
  have hzPos : 0 < ‖z‖ := lt_trans (by norm_num) hNormLower
  let v : CanonicalL2 := ‖z‖⁻¹ • z
  have hvNorm : ‖v‖ = 1 := by
    dsimp only [v]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg z),
      inv_mul_cancel₀ hzPos.ne']
  have hzNormDiff : |‖z‖ - 1| ≤ ‖z - (u : CanonicalL2)‖ := by
    have huNorm' : ‖(u : CanonicalL2)‖ = 1 := huNorm
    rw [← huNorm']
    exact abs_norm_sub_norm_le z (u : CanonicalL2)
  have hzv : ‖z - v‖ = |‖z‖ - 1| :=
    norm_sub_normalize z hzPos
  have huv : ‖(u : CanonicalL2) - v‖ < ε := by
    calc
      ‖(u : CanonicalL2) - v‖ ≤
          ‖(u : CanonicalL2) - z‖ + ‖z - v‖ := by
        simpa only [sub_add_sub_cancel] using
          norm_add_le ((u : CanonicalL2) - z) (z - v)
      _ = ‖z - (u : CanonicalL2)‖ + |‖z‖ - 1| := by
        rw [norm_sub_rev (u : CanonicalL2) z, hzv]
      _ ≤ ‖z - (u : CanonicalL2)‖ + ‖z - (u : CanonicalL2)‖ := by
        gcongr
      _ < η + η := add_lt_add hzClose hzClose
      _ ≤ ε / 4 + ε / 4 := add_le_add hηEps hηEps
      _ < ε := by linarith
  have hvToZ {k : ℕ} (hvk : v k ≠ 0) : z k ≠ 0 := by
    intro hzk
    apply hvk
    simp [v, hzk]
  have hvFinite : Set.Finite {k | v k ≠ 0} := by
    apply (Set.finite_Iio stop).subset
    intro k hk
    have hzk := hvToZ hk
    dsimp only [z] at hzk
    rw [l2Trunc_apply] at hzk
    by_contra hstop
    have hkStop : ¬ k < stop := by
      simpa only [Set.mem_Iio] using hstop
    rw [ite_eq_right hkStop] at hzk
    exact hzk rfl
  have hvNonempty : Set.Nonempty {k | v k ≠ 0} := by
    by_contra hempty
    have hvZero : v = 0 := by
      apply Subtype.ext
      funext k
      by_contra hvk
      exact hempty ⟨k, hvk⟩
    rw [hvZero, norm_zero] at hvNorm
    norm_num at hvNorm
  have hvLower : ∀ k, v k ≠ 0 → start ≤ k := by
    intro k hvk
    have hzk := hvToZ hvk
    by_contra hstart
    have hkStart : k < start := Nat.lt_of_not_ge hstart
    have huk : (u : CanonicalL2) k = 0 := huTail k hkStart
    dsimp only [z] at hzk
    rw [l2Trunc_apply, huk] at hzk
    by_cases hkStop : k < stop
    · rw [ite_eq_left hkStop] at hzk
      exact hzk rfl
    · rw [ite_eq_right hkStop] at hzk
      exact hzk rfl
  have hvUpper : ∀ k, v k ≠ 0 → k < stop := by
    intro k hvk
    have hzk := hvToZ hvk
    dsimp only [z] at hzk
    rw [l2Trunc_apply] at hzk
    by_contra hstop
    rw [ite_eq_right hstop] at hzk
    exact hzk rfl
  exact ⟨stop, u, v, hstartStop, huNorm, hvNorm, hvFinite, hvNonempty,
    hvLower, hvUpper, huv⟩

private def blockEpsilon (n : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ (n + 2)

private lemma blockEpsilon_pos (n : ℕ) : 0 < blockEpsilon n :=
  pow_pos (by norm_num) _

private lemma summable_blockEpsilon : Summable blockEpsilon := by
  have hgeom : Summable fun n : ℕ => (1 / 2 : ℝ) ^ n :=
    summable_geometric_of_norm_lt_one (by norm_num)
  apply (hgeom.mul_left ((1 / 2 : ℝ) ^ 2)).congr
  intro n
  rw [blockEpsilon, pow_add]
  ring

private noncomputable def chosenBlock
    (M : Submodule ℝ CanonicalL2) (hM : ¬ FiniteDimensional ℝ M)
    (start n : ℕ) :
    FiniteApproxBlock M start (blockEpsilon n) :=
  Classical.choice (exists_finiteApproxBlock M hM start (blockEpsilon_pos n))

private noncomputable def blockCut
    (M : Submodule ℝ CanonicalL2) (hM : ¬ FiniteDimensional ℝ M) :
    ℕ → ℕ
  | 0 => 0
  | n + 1 => (chosenBlock M hM (blockCut M hM n) n).stop

private noncomputable def blockVec
    (M : Submodule ℝ CanonicalL2) (hM : ¬ FiniteDimensional ℝ M)
    (n : ℕ) : CanonicalL2 :=
  (chosenBlock M hM (blockCut M hM n) n).vec

private noncomputable def subspaceVec
    (M : Submodule ℝ CanonicalL2) (hM : ¬ FiniteDimensional ℝ M)
    (n : ℕ) : M :=
  (chosenBlock M hM (blockCut M hM n) n).y

private noncomputable def extractedBlock
    (M : Submodule ℝ CanonicalL2) (hM : ¬ FiniteDimensional ℝ M) :
    ℕ → ℕ → ℝ :=
  fun n k => blockVec M hM n k

private lemma extractedBlock_isSuccessive
    (M : Submodule ℝ CanonicalL2) (hM : ¬ FiniteDimensional ℝ M) :
    IsSuccessiveNormalizedBlockSequence (extractedBlock M hM) := by
  constructor
  · intro n
    constructor
    · exact (chosenBlock M hM (blockCut M hM n) n).support_finite
    · exact (chosenBlock M hM (blockCut M hM n) n).support_nonempty
  constructor
  · intro n
    change l2Norm (fun k => blockVec M hM n k) = 1
    rw [l2Norm_coe_eq_norm (blockVec M hM n)]
    exact (chosenBlock M hM (blockCut M hM n) n).norm_vec
  · intro n i j hi hj
    change (chosenBlock M hM (blockCut M hM n) n).vec i ≠ 0 at hi
    change
      (chosenBlock M hM (blockCut M hM (n + 1)) (n + 1)).vec j ≠ 0 at hj
    have hi' :=
      (chosenBlock M hM (blockCut M hM n) n).support_upper i hi
    have hj' :=
      (chosenBlock M hM (blockCut M hM (n + 1)) (n + 1)).support_lower j hj
    exact lt_of_lt_of_le hi' hj'

/-- Every infinite-dimensional Hilbert subspace contains unit vectors which are summably close
to a successive normalized finite-support block sequence.
Blueprint label: `lem:hilbert-gliding-hump`. -/
theorem exists_summable_successiveBlock_approximation
    (M : Submodule ℝ CanonicalL2) (hM : ¬ FiniteDimensional ℝ M) :
    ∃ y : ℕ → M, ∃ w : ℕ → ℕ → ℝ,
      ∃ hw : IsSuccessiveNormalizedBlockSequence w,
        (∀ n, ‖y n‖ = 1) ∧
          Summable (fun n =>
            ‖(y n : CanonicalL2) -
              canonicalL2BlockEmbedding w hw (lp.single 2 n 1)‖) := by
  let y := subspaceVec M hM
  let w := extractedBlock M hM
  let hw := extractedBlock_isSuccessive M hM
  refine ⟨y, w, hw, ?_, ?_⟩
  · intro n
    exact (chosenBlock M hM (blockCut M hM n) n).norm_y
  · apply Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      (fun n => ?_) summable_blockEpsilon
    have heq :
        canonicalL2BlockEmbedding w hw (lp.single 2 n 1) =
          blockVec M hM n := by
      apply Subtype.ext
      funext k
      exact canonicalL2BlockEmbedding_single_apply w hw n k
    rw [heq]
    exact (chosenBlock M hM (blockCut M hM n) n).approx.le

private lemma l2Trunc_sequence_tendsto_zero
    (u : ℕ → CanonicalL2)
    (hu : ∀ k, Tendsto (fun n => u n k) atTop (𝓝 0))
    (m : ℕ) :
    Tendsto (fun n => l2Trunc m (u n)) atTop (𝓝 0) := by
  rw [show (0 : CanonicalL2) =
      ∑ k ∈ Finset.range m, lp.single 2 k (0 : ℝ) by simp]
  apply tendsto_finsetSum
  intro k hk
  let L : ℝ →L[ℝ] CanonicalL2 :=
    ContinuousLinearMap.toSpanSingleton ℝ (lp.single 2 k (1 : ℝ))
  have hL :
      Tendsto (fun n => L (u n k)) atTop (𝓝 (L 0)) :=
    L.continuous.continuousAt.tendsto.comp (hu k)
  convert hL using 1
  · ext n
    rw [ContinuousLinearMap.toSpanSingleton_apply]
    simp [lp.single_apply, Pi.single_apply]
  · simp [L]

private structure WeakNullBlockStep
    (u : ℕ → CanonicalL2) (start minIndex : ℕ) (ε : ℝ) where
  index : ℕ
  stop : ℕ
  vec : CanonicalL2
  minIndex_le : minIndex ≤ index
  start_lt_stop : start < stop
  norm_vec : ‖vec‖ = 1
  support_finite : Set.Finite {k | vec k ≠ 0}
  support_nonempty : Set.Nonempty {k | vec k ≠ 0}
  support_lower : ∀ k, vec k ≠ 0 → start ≤ k
  support_upper : ∀ k, vec k ≠ 0 → k < stop
  approx : ‖u index - vec‖ < ε

private theorem exists_weakNullBlockStep
    (u : ℕ → CanonicalL2) (huNorm : ∀ n, ‖u n‖ = 1)
    (hu : ∀ k, Tendsto (fun n => u n k) atTop (𝓝 0))
    (start minIndex : ℕ) {ε : ℝ} (hε : 0 < ε) :
    Nonempty (WeakNullBlockStep u start minIndex ε) := by
  let η : ℝ := min (1 / 8 : ℝ) (ε / 8)
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  have hηEps : η ≤ ε / 8 := min_le_right _ _
  have hheadTendsto :=
    (l2Trunc_sequence_tendsto_zero u hu start).norm
  rw [Metric.tendsto_atTop] at hheadTendsto
  obtain ⟨N, hN⟩ := hheadTendsto η hη
  let index := max N minIndex
  have hindexN : N ≤ index := Nat.le_max_left _ _
  have hindexMin : minIndex ≤ index := Nat.le_max_right _ _
  have hheadDist :
      dist ‖l2Trunc start (u index)‖ ‖(0 : CanonicalL2)‖ < η :=
    hN index hindexN
  have hhead : ‖l2Trunc start (u index)‖ < η := by
    simpa only [norm_zero, dist_zero_right, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _)] using hheadDist
  obtain ⟨Nstop, hNstop⟩ :=
    Metric.tendsto_atTop.mp (l2Trunc_tendsto (u index)) η hη
  let stop := max Nstop (start + 1)
  have hstopN : Nstop ≤ stop := Nat.le_max_left _ _
  have hstartStop : start < stop :=
    lt_of_lt_of_le (Nat.lt_succ_self start) (Nat.le_max_right _ _)
  have hfullDist : dist (l2Trunc stop (u index)) (u index) < η :=
    hNstop stop hstopN
  have hfull : ‖u index - l2Trunc stop (u index)‖ < η := by
    simpa only [dist_eq_norm, norm_sub_rev] using hfullDist
  let z : CanonicalL2 :=
    l2Trunc stop (u index) - l2Trunc start (u index)
  have huz : ‖u index - z‖ < η + η := by
    calc
      ‖u index - z‖ =
          ‖(u index - l2Trunc stop (u index)) +
            l2Trunc start (u index)‖ := by
        congr 1
        dsimp only [z]
        module
      _ ≤ ‖u index - l2Trunc stop (u index)‖ +
          ‖l2Trunc start (u index)‖ := norm_add_le _ _
      _ < η + η := add_lt_add hfull hhead
  have hzLower : 1 - (η + η) < ‖z‖ := by
    have htri : ‖u index‖ ≤ ‖u index - z‖ + ‖z‖ := by
      calc
        ‖u index‖ = ‖(u index - z) + z‖ := by rw [sub_add_cancel]
        _ ≤ _ := norm_add_le _ _
    rw [huNorm] at htri
    linarith
  have hηBound : η + η ≤ 1 / 4 := by
    have hη' : η ≤ 1 / 8 := min_le_left _ _
    linarith
  have hzPos : 0 < ‖z‖ := by linarith
  let v : CanonicalL2 := ‖z‖⁻¹ • z
  have hvNorm : ‖v‖ = 1 := by
    dsimp only [v]
    rw [norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_pos hzPos, inv_mul_cancel₀ hzPos.ne']
  have hzNormDiff : |‖z‖ - 1| ≤ ‖z - u index‖ := by
    rw [← huNorm index]
    exact abs_norm_sub_norm_le z (u index)
  have hzv : ‖z - v‖ = |‖z‖ - 1| :=
    norm_sub_normalize z hzPos
  have huv : ‖u index - v‖ < ε := by
    calc
      ‖u index - v‖ ≤ ‖u index - z‖ + ‖z - v‖ := by
        simpa only [sub_add_sub_cancel] using
          norm_add_le (u index - z) (z - v)
      _ ≤ ‖u index - z‖ + ‖z - u index‖ := by
        rw [hzv]
        gcongr
      _ = ‖u index - z‖ + ‖u index - z‖ := by
        rw [norm_sub_rev z (u index)]
      _ < (η + η) + (η + η) := add_lt_add huz huz
      _ ≤ ε := by linarith
  have hvToZ {k : ℕ} (hvk : v k ≠ 0) : z k ≠ 0 := by
    intro hzk
    apply hvk
    simp [v, hzk]
  have hzApply (k : ℕ) :
      z k =
        (if k < stop then u index k else 0) -
          (if k < start then u index k else 0) := by
    change
      l2Trunc stop (u index) k - l2Trunc start (u index) k =
        (if k < stop then u index k else 0) -
          (if k < start then u index k else 0)
    rw [l2Trunc_apply, l2Trunc_apply]
  have hvFinite : Set.Finite {k | v k ≠ 0} := by
    apply (Set.finite_Iio stop).subset
    intro k hk
    have hzk := hvToZ hk
    rw [hzApply] at hzk
    by_contra hstop
    have hkstop : ¬ k < stop := by
      simpa only [Set.mem_Iio] using hstop
    have hkstart : ¬ k < start :=
      fun h => hkstop (h.trans hstartStop)
    simp [hkstop, hkstart] at hzk
  have hvLower {k : ℕ} (hvk : v k ≠ 0) : start ≤ k := by
    have hzk := hvToZ hvk
    rw [hzApply] at hzk
    by_contra hstart
    have hkstart : k < start := Nat.lt_of_not_ge hstart
    have hkstop : k < stop := hkstart.trans hstartStop
    simp [hkstart, hkstop] at hzk
  have hvUpper {k : ℕ} (hvk : v k ≠ 0) : k < stop := by
    have hzk := hvToZ hvk
    rw [hzApply] at hzk
    by_contra hstop
    have hkstop : ¬ k < stop := hstop
    have hkstart : ¬ k < start :=
      fun h => hkstop (h.trans hstartStop)
    simp [hkstop, hkstart] at hzk
  have hvNonempty : Set.Nonempty {k | v k ≠ 0} := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have hvzero : v = 0 := by
      apply Subtype.ext
      funext k
      by_contra hvk
      have hk : k ∈ {k | v k ≠ 0} := hvk
      rw [h] at hk
      exact hk
    rw [hvzero, norm_zero] at hvNorm
    norm_num at hvNorm
  exact ⟨{
    index := index
    stop := stop
    vec := v
    minIndex_le := hindexMin
    start_lt_stop := hstartStop
    norm_vec := hvNorm
    support_finite := hvFinite
    support_nonempty := hvNonempty
    support_lower := fun k hk => hvLower hk
    support_upper := fun k hk => hvUpper hk
    approx := huv
  }⟩

private structure WeakNullBlockData (u : ℕ → CanonicalL2) where
  index : ℕ
  start : ℕ
  stop : ℕ
  error : ℝ
  vec : CanonicalL2
  minIndex : ℕ
  minIndex_le : minIndex ≤ index
  start_lt_stop : start < stop
  norm_vec : ‖vec‖ = 1
  support_finite : Set.Finite {k | vec k ≠ 0}
  support_nonempty : Set.Nonempty {k | vec k ≠ 0}
  support_lower : ∀ k, vec k ≠ 0 → start ≤ k
  support_upper : ∀ k, vec k ≠ 0 → k < stop
  approx : ‖u index - vec‖ < error

private noncomputable def weakNullBlockData
    (u : ℕ → CanonicalL2) (huNorm : ∀ n, ‖u n‖ = 1)
    (hu : ∀ k, Tendsto (fun n => u n k) atTop (𝓝 0))
    (start minIndex n : ℕ) :
    WeakNullBlockData u := by
  let s : WeakNullBlockStep u start minIndex (blockEpsilon n) :=
    Classical.choice
      (exists_weakNullBlockStep u huNorm hu start minIndex
        (blockEpsilon_pos n))
  exact
    { index := s.index
      start := start
      stop := s.stop
      error := blockEpsilon n
      vec := s.vec
      minIndex := minIndex
      minIndex_le := s.minIndex_le
      start_lt_stop := s.start_lt_stop
      norm_vec := s.norm_vec
      support_finite := s.support_finite
      support_nonempty := s.support_nonempty
      support_lower := s.support_lower
      support_upper := s.support_upper
      approx := s.approx }

private noncomputable def weakNullBlockState
    (u : ℕ → CanonicalL2) (huNorm : ∀ n, ‖u n‖ = 1)
    (hu : ∀ k, Tendsto (fun n => u n k) atTop (𝓝 0)) :
    ℕ → WeakNullBlockData u
  | 0 => weakNullBlockData u huNorm hu 0 0 0
  | n + 1 =>
      weakNullBlockData u huNorm hu
        (weakNullBlockState u huNorm hu n).stop
        ((weakNullBlockState u huNorm hu n).index + 1) (n + 1)

private lemma weakNullBlockState_error
    (u : ℕ → CanonicalL2) (huNorm : ∀ n, ‖u n‖ = 1)
    (hu : ∀ k, Tendsto (fun n => u n k) atTop (𝓝 0))
    (n : ℕ) :
    (weakNullBlockState u huNorm hu n).error = blockEpsilon n := by
  cases n <;> rfl

private lemma weakNullBlockState_succ_start
    (u : ℕ → CanonicalL2) (huNorm : ∀ n, ‖u n‖ = 1)
    (hu : ∀ k, Tendsto (fun n => u n k) atTop (𝓝 0))
    (n : ℕ) :
    (weakNullBlockState u huNorm hu (n + 1)).start =
      (weakNullBlockState u huNorm hu n).stop := by
  rfl

private lemma weakNullBlockState_succ_minIndex
    (u : ℕ → CanonicalL2) (huNorm : ∀ n, ‖u n‖ = 1)
    (hu : ∀ k, Tendsto (fun n => u n k) atTop (𝓝 0))
    (n : ℕ) :
    (weakNullBlockState u huNorm hu (n + 1)).minIndex =
      (weakNullBlockState u huNorm hu n).index + 1 := by
  rfl

private noncomputable def weakNullBlockIndex
    (u : ℕ → CanonicalL2) (huNorm : ∀ n, ‖u n‖ = 1)
    (hu : ∀ k, Tendsto (fun n => u n k) atTop (𝓝 0))
    (n : ℕ) : ℕ :=
  (weakNullBlockState u huNorm hu n).index

private noncomputable def weakNullBlockSequence
    (u : ℕ → CanonicalL2) (huNorm : ∀ n, ‖u n‖ = 1)
    (hu : ∀ k, Tendsto (fun n => u n k) atTop (𝓝 0)) :
    ℕ → ℕ → ℝ :=
  fun n k => (weakNullBlockState u huNorm hu n).vec k

private theorem weakNullBlockIndex_strictMono
    (u : ℕ → CanonicalL2) (huNorm : ∀ n, ‖u n‖ = 1)
    (hu : ∀ k, Tendsto (fun n => u n k) atTop (𝓝 0)) :
    StrictMono (weakNullBlockIndex u huNorm hu) := by
  apply strictMono_nat_of_lt_succ
  intro n
  change
    (weakNullBlockState u huNorm hu n).index <
      (weakNullBlockState u huNorm hu (n + 1)).index
  apply Nat.lt_of_succ_le
  have h :=
    (weakNullBlockState u huNorm hu (n + 1)).minIndex_le
  rw [weakNullBlockState_succ_minIndex u huNorm hu n] at h
  simpa only [Nat.succ_eq_add_one] using h

private theorem weakNullBlockSequence_isSuccessive
    (u : ℕ → CanonicalL2) (huNorm : ∀ n, ‖u n‖ = 1)
    (hu : ∀ k, Tendsto (fun n => u n k) atTop (𝓝 0)) :
    IsSuccessiveNormalizedBlockSequence
      (weakNullBlockSequence u huNorm hu) := by
  constructor
  · intro n
    constructor
    · exact (weakNullBlockState u huNorm hu n).support_finite
    · exact (weakNullBlockState u huNorm hu n).support_nonempty
  constructor
  · intro n
    change
      l2Norm (fun k => (weakNullBlockState u huNorm hu n).vec k) = 1
    rw [l2Norm_coe_eq_norm
      (weakNullBlockState u huNorm hu n).vec]
    exact (weakNullBlockState u huNorm hu n).norm_vec
  · intro n i j hi hj
    have hi' :=
      (weakNullBlockState u huNorm hu n).support_upper i hi
    have hj' :=
      (weakNullBlockState u huNorm hu (n + 1)).support_lower j hj
    rw [weakNullBlockState_succ_start u huNorm hu n] at hj'
    exact lt_of_lt_of_le hi' hj'

/-- Every continuous functional on the canonical Hilbert space vanishes along its standard
unit-vector basis. -/
theorem tendsto_dual_canonicalL2Basis_zero
    (f : StrongDual ℝ CanonicalL2) :
    Tendsto (fun n => f (lp.single 2 n (1 : ℝ))) atTop (𝓝 0) := by
  let x : CanonicalL2 :=
    (InnerProductSpace.toDual ℝ CanonicalL2).symm f
  have hx : Tendsto (fun n => x n) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hs :
        Summable (fun n => ‖x n‖ ^ (2 : ℝ)) :=
      (lp.memℓp x).summable (by norm_num)
    have hsq :
        Tendsto (fun n => ‖x n‖ ^ (2 : ℝ)) atTop (𝓝 0) :=
      hs.tendsto_atTop_zero
    have hsqrt :=
      (Real.continuous_sqrt.tendsto 0).comp hsq
    convert hsqrt using 1
    · ext n
      simpa [Function.comp_apply] using
        (Real.sqrt_sq_eq_abs (x n)).symm
    · simp
  have hfx :
      InnerProductSpace.toDual ℝ CanonicalL2 x = f :=
    (InnerProductSpace.toDual ℝ CanonicalL2).apply_symm_apply f
  have happ (n : ℕ) :
      f (lp.single 2 n (1 : ℝ)) = x n := by
    rw [← hfx]
    change
      InnerProductSpace.toDual ℝ CanonicalL2 x
          (lp.single 2 n (1 : ℝ)) =
        x n
    rw [InnerProductSpace.toDual_apply_apply, lp.inner_single_right]
    simp
  convert hx using 1
  ext n
  exact happ n

/-- A normalized coordinatewise-null sequence in the canonical Hilbert space has a strict
subsequence summably close to a successive normalized finite-support block sequence. -/
theorem exists_summable_successiveBlock_subsequence_approximation
    (u : ℕ → CanonicalL2) (huNorm : ∀ n, ‖u n‖ = 1)
    (hu : ∀ k, Tendsto (fun n => u n k) atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ v : ℕ → ℕ → ℝ,
        ∃ hv : IsSuccessiveNormalizedBlockSequence v,
          Summable (fun n =>
            ‖u (φ n) -
              canonicalL2BlockEmbedding v hv
                (lp.single 2 n (1 : ℝ))‖) := by
  let φ := weakNullBlockIndex u huNorm hu
  let v := weakNullBlockSequence u huNorm hu
  let hv := weakNullBlockSequence_isSuccessive u huNorm hu
  refine ⟨φ, weakNullBlockIndex_strictMono u huNorm hu, v, hv, ?_⟩
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      (fun n => ?_) summable_blockEpsilon
  have heq :
      canonicalL2BlockEmbedding v hv (lp.single 2 n (1 : ℝ)) =
        (weakNullBlockState u huNorm hu n).vec := by
    apply Subtype.ext
    funext k
    exact canonicalL2BlockEmbedding_single_apply v hv n k
  rw [heq]
  change
    ‖u (weakNullBlockState u huNorm hu n).index -
      (weakNullBlockState u huNorm hu n).vec‖ ≤ blockEpsilon n
  rw [← weakNullBlockState_error u huNorm hu n]
  exact (weakNullBlockState u huNorm hu n).approx.le

private lemma canonicalL2Single_orthonormal :
    Orthonormal ℝ (fun n : ℕ => lp.single 2 n (1 : ℝ)) := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [lp.inner_single_left]
  simp [lp.single_apply, Pi.single_apply]

/-- The block isometry intertwines every finite linear combination of standard `ℓ₂` vectors
with the corresponding combination of block vectors. -/
theorem canonicalL2BlockEmbedding_sum_single
    (w : ℕ → ℕ → ℝ) (hw : IsSuccessiveNormalizedBlockSequence w)
    (s : Finset ℕ) (c : ℕ → ℝ) :
    canonicalL2BlockEmbedding w hw
        (∑ k ∈ s, c k • lp.single 2 k (1 : ℝ)) =
      ∑ k ∈ s, c k •
        canonicalL2BlockEmbedding w hw (lp.single 2 k (1 : ℝ)) := by
  simp only [map_sum, map_smul]

/-- A finite combination of approximate block vectors is controlled by the corresponding
`ℓ₂` combination plus the weighted approximation errors. -/
theorem norm_finset_sum_le_block_plus_error
    (y : ℕ → CanonicalL2)
    (w : ℕ → ℕ → ℝ) (hw : IsSuccessiveNormalizedBlockSequence w)
    (s : Finset ℕ) (c : ℕ → ℝ) :
    ‖∑ k ∈ s, c k • y k‖ ≤
      ‖∑ k ∈ s, c k • lp.single 2 k (1 : ℝ)‖ +
        ∑ k ∈ s, |c k| *
          ‖y k -
            canonicalL2BlockEmbedding w hw (lp.single 2 k (1 : ℝ))‖ := by
  let B := canonicalL2BlockEmbedding w hw
  have hdecomp :
      (∑ k ∈ s, c k • y k) =
        (∑ k ∈ s, c k • B (lp.single 2 k (1 : ℝ))) +
          ∑ k ∈ s, c k •
            (y k - B (lp.single 2 k (1 : ℝ))) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    module
  rw [hdecomp]
  calc
    ‖(∑ k ∈ s, c k • B (lp.single 2 k (1 : ℝ))) +
        ∑ k ∈ s, c k •
          (y k - B (lp.single 2 k (1 : ℝ)))‖ ≤
        ‖∑ k ∈ s, c k • B (lp.single 2 k (1 : ℝ))‖ +
          ‖∑ k ∈ s, c k •
            (y k - B (lp.single 2 k (1 : ℝ)))‖ :=
      norm_add_le _ _
    _ = ‖∑ k ∈ s, c k • lp.single 2 k (1 : ℝ)‖ +
          ‖∑ k ∈ s, c k •
            (y k - B (lp.single 2 k (1 : ℝ)))‖ := by
      congr 1
      rw [← canonicalL2BlockEmbedding_sum_single w hw s c]
      exact canonicalL2BlockEmbedding_norm w hw _
    _ ≤ ‖∑ k ∈ s, c k • lp.single 2 k (1 : ℝ)‖ +
          ∑ k ∈ s, |c k| *
            ‖y k - B (lp.single 2 k (1 : ℝ))‖ := by
      gcongr
      simpa only [norm_smul, Real.norm_eq_abs] using
        (norm_sum_le s
          (fun k => c k •
            (y k - B (lp.single 2 k (1 : ℝ)))))

/-- A normalized signed average of distinct standard `ℓ₂` vectors has norm exactly one. -/
theorem norm_signed_average_single
    (N : ℕ) (hN : 0 < N) (σ : ℕ → ℝ)
    (hσ : ∀ k < N, |σ k| = 1) :
    ‖∑ k ∈ Finset.range N,
        (σ k / Real.sqrt (N : ℝ)) • lp.single 2 k (1 : ℝ)‖ = 1 := by
  let c : ℕ → ℝ := fun k => σ k / Real.sqrt (N : ℝ)
  let z : CanonicalL2 :=
    ∑ k ∈ Finset.range N, c k • lp.single 2 k (1 : ℝ)
  have hNreal : 0 < (N : ℝ) := by
    exact_mod_cast hN
  have hterms :
      ∀ k ∈ Finset.range N, c k ^ 2 = 1 / (N : ℝ) := by
    intro k hk
    have hσsq : σ k ^ 2 = 1 := by
      calc
        σ k ^ 2 = |σ k| ^ 2 := (sq_abs (σ k)).symm
        _ = 1 := by
          rw [hσ k (Finset.mem_range.mp hk)]
          norm_num
    dsimp only [c]
    rw [div_pow, hσsq, Real.sq_sqrt hNreal.le]
  have hsum : ∑ k ∈ Finset.range N, c k ^ 2 = 1 := by
    calc
      ∑ k ∈ Finset.range N, c k ^ 2 =
          ∑ k ∈ Finset.range N, (1 / (N : ℝ)) :=
        Finset.sum_congr rfl hterms
      _ = 1 := by simp [hN.ne']
  have hinner :=
    canonicalL2Single_orthonormal.inner_sum c c (Finset.range N)
  change inner ℝ z z = _ at hinner
  rw [real_inner_self_eq_norm_sq] at hinner
  have hzsq : ‖z‖ ^ 2 = 1 := by
    calc
      ‖z‖ ^ 2 = ∑ k ∈ Finset.range N, c k ^ 2 := by
        simpa only [starRingEnd_apply, star_trivial, pow_two] using hinner
      _ = 1 := hsum
  have hznonneg : 0 ≤ ‖z‖ := norm_nonneg z
  nlinarith

/-- The corresponding normalized signed average of exact block vectors also has norm exactly
one. -/
theorem norm_signed_average_blockEmbedding
    (w : ℕ → ℕ → ℝ) (hw : IsSuccessiveNormalizedBlockSequence w)
    (N : ℕ) (hN : 0 < N) (σ : ℕ → ℝ)
    (hσ : ∀ k < N, |σ k| = 1) :
    ‖∑ k ∈ Finset.range N,
        (σ k / Real.sqrt (N : ℝ)) •
          canonicalL2BlockEmbedding w hw (lp.single 2 k (1 : ℝ))‖ = 1 := by
  rw [← canonicalL2BlockEmbedding_sum_single]
  rw [canonicalL2BlockEmbedding_norm]
  exact norm_signed_average_single N hN σ hσ

/-- A normalized signed average of approximate block vectors has norm at most one plus the sum
of their approximation errors. -/
theorem norm_signed_average_le_one_add_error
    (y : ℕ → CanonicalL2)
    (w : ℕ → ℕ → ℝ) (hw : IsSuccessiveNormalizedBlockSequence w)
    (N : ℕ) (hN : 0 < N) (σ : ℕ → ℝ)
    (hσ : ∀ k < N, |σ k| = 1) :
    ‖∑ k ∈ Finset.range N,
        (σ k / Real.sqrt (N : ℝ)) • y k‖ ≤
      1 + ∑ k ∈ Finset.range N,
        ‖y k -
          canonicalL2BlockEmbedding w hw (lp.single 2 k (1 : ℝ))‖ := by
  have hN_one : 1 ≤ N := hN
  have hNsqrt : 1 ≤ Real.sqrt (N : ℝ) := by
    rw [Real.one_le_sqrt]
    exact_mod_cast hN_one
  calc
    ‖∑ k ∈ Finset.range N,
        (σ k / Real.sqrt (N : ℝ)) • y k‖ ≤
      ‖∑ k ∈ Finset.range N,
        (σ k / Real.sqrt (N : ℝ)) • lp.single 2 k (1 : ℝ)‖ +
        ∑ k ∈ Finset.range N,
          |σ k / Real.sqrt (N : ℝ)| *
            ‖y k -
              canonicalL2BlockEmbedding w hw
                (lp.single 2 k (1 : ℝ))‖ :=
      norm_finset_sum_le_block_plus_error y w hw (Finset.range N)
        (fun k => σ k / Real.sqrt (N : ℝ))
    _ ≤ 1 + ∑ k ∈ Finset.range N,
        ‖y k -
          canonicalL2BlockEmbedding w hw
            (lp.single 2 k (1 : ℝ))‖ := by
      rw [norm_signed_average_single N hN σ hσ]
      gcongr with k hk
      apply mul_le_of_le_one_left (norm_nonneg _)
      rw [abs_div, hσ k (Finset.mem_range.mp hk),
        abs_of_pos (lt_of_lt_of_le zero_lt_one hNsqrt)]
      exact (div_le_one (lt_of_lt_of_le zero_lt_one hNsqrt)).2 hNsqrt

/-- The signed-average estimate is uniform in the length and sign choices whenever the
approximation errors are summable. -/
theorem norm_signed_average_le_one_add_tsum_error
    (y : ℕ → CanonicalL2)
    (w : ℕ → ℕ → ℝ) (hw : IsSuccessiveNormalizedBlockSequence w)
    (hsum : Summable fun k =>
      ‖y k -
        canonicalL2BlockEmbedding w hw (lp.single 2 k (1 : ℝ))‖)
    (N : ℕ) (hN : 0 < N) (σ : ℕ → ℝ)
    (hσ : ∀ k < N, |σ k| = 1) :
    ‖∑ k ∈ Finset.range N,
        (σ k / Real.sqrt (N : ℝ)) • y k‖ ≤
      1 + ∑' k,
        ‖y k -
          canonicalL2BlockEmbedding w hw (lp.single 2 k (1 : ℝ))‖ := by
  refine (norm_signed_average_le_one_add_error y w hw N hN σ hσ).trans ?_
  gcongr
  exact hsum.sum_le_tsum (Finset.range N)
    (fun k hk => norm_nonneg _)

/-- A compact gliding-hump interface exposing the normalized vectors, exact successive blocks,
summable approximation, and their uniform signed-average bound. -/
theorem exists_successiveBlock_with_uniform_signed_average_bound
    (M : Submodule ℝ CanonicalL2) (hM : ¬ FiniteDimensional ℝ M) :
    ∃ y : ℕ → M, ∃ w : ℕ → ℕ → ℝ,
      ∃ hw : IsSuccessiveNormalizedBlockSequence w,
        (∀ n, ‖y n‖ = 1) ∧
          Summable (fun n =>
            ‖(y n : CanonicalL2) -
              canonicalL2BlockEmbedding w hw
                (lp.single 2 n (1 : ℝ))‖) ∧
          ∀ N, 0 < N → ∀ σ : ℕ → ℝ,
            (∀ k < N, |σ k| = 1) →
              ‖∑ k ∈ Finset.range N,
                  (σ k / Real.sqrt (N : ℝ)) •
                    (y k : CanonicalL2)‖ ≤
                1 + ∑' k,
                  ‖(y k : CanonicalL2) -
                    canonicalL2BlockEmbedding w hw
                      (lp.single 2 k (1 : ℝ))‖ := by
  obtain ⟨y, w, hw, hy, hsum⟩ :=
    exists_summable_successiveBlock_approximation M hM
  refine ⟨y, w, hw, hy, hsum, ?_⟩
  intro N hN σ hσ
  exact norm_signed_average_le_one_add_tsum_error
    (fun k => (y k : CanonicalL2)) w hw hsum N hN σ hσ

end

end KaltonPeck.Support.HilbertGlidingHump

/-
Upstream license notice:
MIT License

Copyright (c) 2026 Avik Das

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
