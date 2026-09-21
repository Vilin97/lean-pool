/-
Copyright (c) 2026 Avik Das. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Avik Das
-/
/-
Copyright (c) 2026 adas1236. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: adas1236
-/
import LeanPool.KaltonPeck.KaltonPeck.Support.Symplectic
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Normed.Module.Bases
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# Compact block extraction for the canonical Hilbert space

This file extracts a successive normalized finite-support block family on which an operator
that is not upper semi-Fredholm becomes compact.
-/


namespace KaltonPeck.Support.CgpBlockExtraction

noncomputable
section

open Coordinates Symplectic
open Function
open Filter
open scoped Topology

private theorem upperSemi_of_antilipschitz_orthogonal
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : E →L[ℝ] F) (H : Submodule ℝ E) [FiniteDimensional ℝ H]
    (hanti : ∃ K, AntilipschitzWith K (T.domRestrict Hᗮ)) :
    FiniteDimensional ℝ T.toLinearMap.ker ∧
      IsClosed (T.toLinearMap.range : Set F) := by
  obtain ⟨K, hK⟩ := hanti
  have hg_inj : Function.Injective (T.domRestrict Hᗮ) := hK.injective
  let p : T.toLinearMap.ker →ₗ[ℝ] H :=
    H.orthogonalProjectionOnto.toLinearMap.comp T.toLinearMap.ker.subtype
  have hp_inj : Function.Injective p := by
    intro x y hxy
    apply Subtype.ext
    have hproj : H.orthogonalProjectionOnto ((x : E) - (y : E)) = 0 := by
      rw [map_sub, sub_eq_zero]
      exact hxy
    have hperp : (x : E) - (y : E) ∈ Hᗮ :=
      H.orthogonalProjectionOnto_eq_zero_iff.mp hproj
    let z : Hᗮ := ⟨(x : E) - (y : E), hperp⟩
    have hzero : T.domRestrict Hᗮ z = 0 := by
      change T ((x : E) - (y : E)) = 0
      rw [map_sub]
      have hx : T (x : E) = 0 := x.property
      have hy : T (y : E) = 0 := y.property
      rw [hx, hy, sub_zero]
    have hz : z = 0 := hg_inj (by simpa using hzero)
    exact sub_eq_zero.mp (congrArg Subtype.val hz)
  let : FiniteDimensional ℝ T.toLinearMap.ker :=
    FiniteDimensional.of_injective p hp_inj
  have hclosed_perp :
      IsClosed (((T.domRestrict Hᗮ).toLinearMap.range : Submodule ℝ F) : Set F) :=
    hK.isClosed_range (T.domRestrict Hᗮ).uniformContinuous
  let : FiniteDimensional ℝ (Submodule.map T.toLinearMap H) := inferInstance
  have hrange :
      T.toLinearMap.range =
        (T.domRestrict Hᗮ).toLinearMap.range ⊔ Submodule.map T.toLinearMap H := by
    rw [ContinuousLinearMap.toLinearMap_domRestrict, LinearMap.range_domRestrict]
    rw [← Submodule.map_sup]
    rw [sup_comm, Submodule.sup_orthogonal_of_hasOrthogonalProjection]
    exact LinearMap.range_eq_map T.toLinearMap
  refine ⟨inferInstance, ?_⟩
  rw [hrange]
  exact Submodule.isClosed_sup_finiteDimensional _ _ hclosed_perp

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
    Filter.Tendsto (fun m => l2Trunc m x) Filter.atTop (𝓝 x) := by
  exact (lp.hasSum_single (p := (2 : ENNReal)) (by norm_num) x).tendsto_sum_nat

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

private lemma exists_small_unit_tail
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (T : CanonicalL2 →L[ℝ] X)
    (hT : ¬ (FiniteDimensional ℝ T.toLinearMap.ker ∧
      IsClosed (T.toLinearMap.range : Set X)))
    (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ x : (l2Head N)ᗮ, ‖x‖ = 1 ∧ ‖T (x : CanonicalL2)‖ < ε := by
  have hnoanti : ¬ ∃ K, AntilipschitzWith K (T.domRestrict (l2Head N)ᗮ) := by
    intro h
    exact hT (upperSemi_of_antilipschitz_orthogonal T (l2Head N) h)
  have hnolower :
      ¬ ∃ c > 0, ∀ x : (l2Head N)ᗮ,
        c * ‖x‖ ≤ ‖T.domRestrict (l2Head N)ᗮ x‖ := by
    intro h
    exact hnoanti (antilipschitzWith_iff_exists_mul_le_norm.mpr h)
  have hfail :
      ¬ ∀ x : (l2Head N)ᗮ,
        ε * ‖x‖ ≤ ‖T.domRestrict (l2Head N)ᗮ x‖ := by
    intro h
    exact hnolower ⟨ε, hε, h⟩
  push Not at hfail
  obtain ⟨x, hx⟩ := hfail
  have hxne : x ≠ 0 := by
    intro hzero
    subst x
    simp at hx
  have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hxne
  let u : (l2Head N)ᗮ := (‖x‖ : ℝ)⁻¹ • x
  refine ⟨u, ?_, ?_⟩
  · dsimp only [u]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg x),
      inv_mul_cancel₀ hxnorm.ne']
  · change ‖T ((‖x‖ : ℝ)⁻¹ • (x : CanonicalL2))‖ < ε
    rw [map_smul, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_nonneg (norm_nonneg x)]
    calc
      ‖x‖⁻¹ * ‖T (x : CanonicalL2)‖ <
          ‖x‖⁻¹ * (ε * ‖x‖) :=
        mul_lt_mul_of_pos_left hx (inv_pos.mpr hxnorm)
      _ = ε := by field_simp

private structure FiniteBlock
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (T : CanonicalL2 →L[ℝ] X) (start : ℕ) (ε : ℝ) where
  stop : ℕ
  vec : CanonicalL2
  start_lt_stop : start < stop
  norm_vec : ‖vec‖ = 1
  support_finite : Set.Finite {k | vec k ≠ 0}
  support_nonempty : Set.Nonempty {k | vec k ≠ 0}
  support_lower : ∀ k, vec k ≠ 0 → start ≤ k
  support_upper : ∀ k, vec k ≠ 0 → k < stop
  map_norm_lt : ‖T vec‖ < ε

private lemma exists_finiteBlock
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (T : CanonicalL2 →L[ℝ] X)
    (hT : ¬ (FiniteDimensional ℝ T.toLinearMap.ker ∧
      IsClosed (T.toLinearMap.range : Set X)))
    (start : ℕ) {ε : ℝ} (hε : 0 < ε) :
    Nonempty (FiniteBlock T start ε) := by
  obtain ⟨u, hu_norm, hu_small⟩ :=
    exists_small_unit_tail T hT start (show 0 < ε / 4 by positivity)
  let η : ℝ := min (1 / 2 : ℝ) (ε / (8 * (‖T‖ + 1)))
  have hTplus : 0 < ‖T‖ + 1 := by positivity
  have hden : 0 < 8 * (‖T‖ + 1) := mul_pos (by norm_num) hTplus
  have hη : 0 < η := lt_min (by norm_num) (div_pos hε hden)
  have hη_half : η ≤ 1 / 2 := min_le_left _ _
  have hη_eps : η ≤ ε / (8 * (‖T‖ + 1)) := min_le_right _ _
  obtain ⟨M, hM⟩ :=
    Metric.tendsto_atTop.mp (l2Trunc_tendsto (u : CanonicalL2)) η hη
  let m : ℕ := max M (start + 1)
  have hmM : M ≤ m := Nat.le_max_left _ _
  have hstartm : start < m :=
    lt_of_lt_of_le (Nat.lt_succ_self start) (Nat.le_max_right _ _)
  let y : CanonicalL2 := l2Trunc m (u : CanonicalL2)
  have hyclose_dist : dist y (u : CanonicalL2) < η := hM m hmM
  have hyclose : ‖y - (u : CanonicalL2)‖ < η := by
    simpa only [dist_eq_norm] using hyclose_dist
  have hyclose_rev : ‖(u : CanonicalL2) - y‖ < η := by
    simpa only [norm_sub_rev] using hyclose
  have htri : ‖(u : CanonicalL2)‖ ≤
      ‖(u : CanonicalL2) - y‖ + ‖y‖ := by
    calc
      ‖(u : CanonicalL2)‖ =
          ‖((u : CanonicalL2) - y) + y‖ := by rw [sub_add_cancel]
      _ ≤ ‖(u : CanonicalL2) - y‖ + ‖y‖ := norm_add_le _ _
  have hu_norm' : ‖(u : CanonicalL2)‖ = 1 := hu_norm
  have hy_norm_lower : 1 / 2 < ‖y‖ := by
    nlinarith
  have hy_norm_pos : 0 < ‖y‖ := lt_trans (by norm_num) hy_norm_lower
  have hprod : ‖T‖ * ‖y - (u : CanonicalL2)‖ < ε / 8 := by
    calc
      ‖T‖ * ‖y - (u : CanonicalL2)‖ ≤
          (‖T‖ + 1) * ‖y - (u : CanonicalL2)‖ := by
        exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      _ < (‖T‖ + 1) * η :=
        mul_lt_mul_of_pos_left hyclose hTplus
      _ ≤ (‖T‖ + 1) * (ε / (8 * (‖T‖ + 1))) :=
        mul_le_mul_of_nonneg_left hη_eps hTplus.le
      _ = ε / 8 := by field_simp
  have hTdiff : ‖T (y - (u : CanonicalL2))‖ < ε / 8 :=
    (T.le_opNorm _).trans_lt hprod
  have hy_decomp :
      T y = T (u : CanonicalL2) + T (y - (u : CanonicalL2)) := by
    rw [map_sub]
    abel
  have hTy : ‖T y‖ < 3 * ε / 8 := by
    rw [hy_decomp]
    calc
      ‖T (u : CanonicalL2) + T (y - (u : CanonicalL2))‖ ≤
          ‖T (u : CanonicalL2)‖ + ‖T (y - (u : CanonicalL2))‖ :=
        norm_add_le _ _
      _ < ε / 4 + ε / 8 := add_lt_add hu_small hTdiff
      _ = 3 * ε / 8 := by ring
  let v : CanonicalL2 := (‖y‖ : ℝ)⁻¹ • y
  have hv_norm : ‖v‖ = 1 := by
    dsimp only [v]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg y),
      inv_mul_cancel₀ hy_norm_pos.ne']
  have hinv_lt : (‖y‖ : ℝ)⁻¹ < 2 := by
    rw [inv_lt_iff_one_lt_mul₀ hy_norm_pos]
    nlinarith
  have hv_small : ‖T v‖ < ε := by
    dsimp only [v]
    rw [map_smul, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_nonneg (norm_nonneg y)]
    calc
      ‖y‖⁻¹ * ‖T y‖ ≤ 2 * ‖T y‖ :=
        mul_le_mul_of_nonneg_right hinv_lt.le (norm_nonneg _)
      _ < 2 * (3 * ε / 8) := mul_lt_mul_of_pos_left hTy (by norm_num)
      _ < ε := by nlinarith
  have hv_to_y {k : ℕ} (hvk : v k ≠ 0) : y k ≠ 0 := by
    intro hyk
    apply hvk
    simp [v, hyk]
  have hv_finite : Set.Finite {k | v k ≠ 0} := by
    apply (Set.finite_Iio m).subset
    intro k hk
    have hyk := hv_to_y hk
    dsimp only [y] at hyk
    rw [l2Trunc_apply] at hyk
    change k < m
    by_contra hkm
    rw [ite_eq_right hkm] at hyk
    exact hyk rfl
  have hv_nonempty : Set.Nonempty {k | v k ≠ 0} := by
    by_contra hempty
    have hvzero : v = 0 := by
      apply Subtype.ext
      funext k
      by_contra hvk
      exact hempty ⟨k, hvk⟩
    rw [hvzero, norm_zero] at hv_norm
    norm_num at hv_norm
  have hv_lower : ∀ k, v k ≠ 0 → start ≤ k := by
    intro k hvk
    have hyk := hv_to_y hvk
    by_contra hsk
    have hks : k < start := Nat.lt_of_not_ge hsk
    have huk : (u : CanonicalL2) k = 0 :=
      (mem_l2Head_orthogonal_iff start (u : CanonicalL2)).mp u.property k hks
    dsimp only [y] at hyk
    rw [l2Trunc_apply, huk] at hyk
    by_cases hkm : k < m
    · rw [ite_eq_left hkm] at hyk
      exact hyk rfl
    · rw [ite_eq_right hkm] at hyk
      exact hyk rfl
  have hv_upper : ∀ k, v k ≠ 0 → k < m := by
    intro k hvk
    have hyk := hv_to_y hvk
    dsimp only [y] at hyk
    rw [l2Trunc_apply] at hyk
    by_contra hkm
    rw [ite_eq_right hkm] at hyk
    exact hyk rfl
  exact ⟨m, v, hstartm, hv_norm, hv_finite, hv_nonempty, hv_lower,
    hv_upper, hv_small⟩

private def blockEpsilon (n : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ (n + 2)

private lemma blockEpsilon_pos (n : ℕ) : 0 < blockEpsilon n := by
  exact pow_pos (by norm_num) _

private noncomputable def chosenBlock
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (T : CanonicalL2 →L[ℝ] X)
    (hT : ¬ (FiniteDimensional ℝ T.toLinearMap.ker ∧
      IsClosed (T.toLinearMap.range : Set X)))
    (start n : ℕ) : FiniteBlock T start (blockEpsilon n) :=
  Classical.choice (exists_finiteBlock T hT start (blockEpsilon_pos n))

private noncomputable def blockCut
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (T : CanonicalL2 →L[ℝ] X)
    (hT : ¬ (FiniteDimensional ℝ T.toLinearMap.ker ∧
      IsClosed (T.toLinearMap.range : Set X))) : ℕ → ℕ
  | 0 => 0
  | n + 1 => (chosenBlock T hT (blockCut T hT n) n).stop

private noncomputable def blockVec
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (T : CanonicalL2 →L[ℝ] X)
    (hT : ¬ (FiniteDimensional ℝ T.toLinearMap.ker ∧
      IsClosed (T.toLinearMap.range : Set X)))
    (n : ℕ) : CanonicalL2 :=
  (chosenBlock T hT (blockCut T hT n) n).vec

private noncomputable def extractedBlock
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (T : CanonicalL2 →L[ℝ] X)
    (hT : ¬ (FiniteDimensional ℝ T.toLinearMap.ker ∧
      IsClosed (T.toLinearMap.range : Set X))) :
    ℕ → ℕ → ℝ :=
  fun n k => blockVec T hT n k

private lemma extractedBlock_isSuccessive
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (T : CanonicalL2 →L[ℝ] X)
    (hT : ¬ (FiniteDimensional ℝ T.toLinearMap.ker ∧
      IsClosed (T.toLinearMap.range : Set X))) :
    IsSuccessiveNormalizedBlockSequence (extractedBlock T hT) := by
  constructor
  · intro n
    constructor
    · exact (chosenBlock T hT (blockCut T hT n) n).support_finite
    · exact (chosenBlock T hT (blockCut T hT n) n).support_nonempty
  constructor
  · intro n
    change l2Norm (fun k => blockVec T hT n k) = 1
    rw [l2Norm_coe_eq_norm (blockVec T hT n)]
    exact (chosenBlock T hT (blockCut T hT n) n).norm_vec
  · intro n i j hi hj
    change (chosenBlock T hT (blockCut T hT n) n).vec i ≠ 0 at hi
    change
      (chosenBlock T hT (blockCut T hT (n + 1)) (n + 1)).vec j ≠ 0 at hj
    have hi' :=
      (chosenBlock T hT (blockCut T hT n) n).support_upper i hi
    have hj' :=
      (chosenBlock T hT (blockCut T hT (n + 1)) (n + 1)).support_lower j hj
    have hiCut : i < blockCut T hT (n + 1) := hi'
    exact lt_of_lt_of_le hiCut hj'

private lemma extractedBlock_basis_bound
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (T : CanonicalL2 →L[ℝ] X)
    (hT : ¬ (FiniteDimensional ℝ T.toLinearMap.ker ∧
      IsClosed (T.toLinearMap.range : Set X)))
    (n : ℕ) :
    let w := extractedBlock T hT
    let hw := extractedBlock_isSuccessive T hT
    ‖T (canonicalL2BlockEmbedding w hw (lp.single 2 n 1))‖ <
      blockEpsilon n := by
  let w := extractedBlock T hT
  let hw := extractedBlock_isSuccessive T hT
  change
    ‖T (canonicalL2BlockEmbedding w hw (lp.single 2 n 1))‖ <
      blockEpsilon n
  have heq :
      canonicalL2BlockEmbedding w hw (lp.single 2 n 1) =
        blockVec T hT n := by
    apply Subtype.ext
    funext k
    exact canonicalL2BlockEmbedding_single_apply w hw n k
  rw [heq]
  exact (chosenBlock T hT (blockCut T hT n) n).map_norm_lt

private lemma schauderRankOne_isCompact
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (c : StrongDual ℝ X) (y : Y) :
    IsCompactOperator (c.smulRight y) := by
  have hc : IsCompactOperator c :=
    isCompactOperator_of_locallyCompactSpace_dom c
  change IsCompactOperator
    (fun x => (ContinuousLinearMap.toSpanSingleton ℝ y) (c x))
  exact hc.clm_comp (ContinuousLinearMap.toSpanSingleton ℝ y)

/-- A bounded operator is compact when its images along a Schauder basis are summable after
weighting by the norms of the coordinate functionals.
Blueprint label: `lem:schauder-weighted-images-compact`. -/
theorem compact_of_schauderBasis_weighted
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (b : SchauderBasis ℝ X) (T : X →L[ℝ] Y)
    (hT : Summable fun n => ‖b.coord n‖ * ‖T (b n)‖) :
    IsCompactOperator T := by
  let R : ℕ → X →L[ℝ] Y :=
    fun n => (b.coord n).smulRight (T (b n))
  have hnorm (n : ℕ) :
      ‖R n‖ = ‖b.coord n‖ * ‖T (b n)‖ := by
    simp [R]
  have hR : Summable R := by
    apply Summable.of_norm
    simpa only [hnorm] using hT
  have hsum : ∑' n, R n = T := by
    apply ContinuousLinearMap.ext
    intro x
    have hRx : HasSum (fun n => R n x) ((∑' n, R n) x) :=
      hR.hasSum.map (ContinuousLinearMap.apply ℝ Y x)
        (ContinuousLinearMap.apply ℝ Y x).continuous
    have hRx' :
        HasSum (fun n => R n x) ((∑' n, R n) x)
          (SummationFilter.conditional ℕ) :=
      hRx.mono_left SummationFilter.le_atTop
    have hx := (b.expansion x).map T T.continuous
    apply hRx'.unique
    convert hx using 1
    ext n
    simp [R, map_smul]
  rw [← hsum]
  apply isCompactOperator_of_tendsto hR.hasSum.tendsto_sum_nat
  filter_upwards []
  intro n
  have hfinite (s : Finset ℕ) :
      IsCompactOperator (fun z => (∑ i ∈ s, R i) z) := by
    induction s using Finset.induction with
    | empty =>
        change IsCompactOperator (fun _ : X => (0 : Y))
        exact isCompactOperator_zero
    | @insert a s ha ih =>
        rw [Finset.sum_insert ha]
        exact (schauderRankOne_isCompact
          (b.coord a) (T (b a))).add ih
  exact hfinite (Finset.range n)

private lemma rankOne_isCompact
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (x : X) (n : ℕ) :
    IsCompactOperator (InnerProductSpace.rankOne ℝ x (l2Basis n)) := by
  have hscalar :
      IsCompactOperator (innerSL ℝ (l2Basis n) : CanonicalL2 → ℝ) := by
    exact isCompactOperator_of_locallyCompactSpace_dom (innerSL ℝ (l2Basis n))
  rw [InnerProductSpace.rankOne_def']
  exact hscalar.clm_comp (ContinuousLinearMap.toSpanSingleton ℝ x)

private theorem compact_of_summable_basis_images
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (S : CanonicalL2 →L[ℝ] X)
    (hS : Summable fun n => ‖S (l2Basis n)‖) :
    IsCompactOperator S := by
  let R : ℕ → CanonicalL2 →L[ℝ] X :=
    fun n => InnerProductSpace.rankOne ℝ (S (l2Basis n)) (l2Basis n)
  have hnorm (n : ℕ) : ‖R n‖ = ‖S (l2Basis n)‖ := by
    simp [R, l2Basis, InnerProductSpace.norm_rankOne, lp.norm_single]
  have hR : Summable R := by
    apply Summable.of_norm
    simpa only [hnorm] using hS
  have hsum : ∑' n, R n = S := by
    apply ContinuousLinearMap.ext
    intro x
    have hRx : HasSum (fun n => R n x) ((∑' n, R n) x) :=
      hR.hasSum.map (ContinuousLinearMap.apply ℝ X x)
        (ContinuousLinearMap.apply ℝ X x).continuous
    have hx :=
      (lp.hasSum_single (p := (2 : ENNReal)) (by norm_num) x).map S S.continuous
    apply hRx.unique
    convert hx using 1
    ext n
    change inner ℝ (l2Basis n) x • S (l2Basis n) =
      S (lp.single 2 n (x n))
    have hinner : inner ℝ (l2Basis n) x = x n := by
      simpa only [l2Basis, RCLike.inner_apply, conj_trivial, mul_one] using
        (lp.inner_single_left (𝕜 := ℝ) n (1 : ℝ) x)
    rw [hinner, ← map_smul]
    congr 1
    ext j
    by_cases hj : j = n <;> simp [l2Basis, lp.single_apply, hj]
  rw [← hsum]
  apply isCompactOperator_of_tendsto hR.hasSum.tendsto_sum_nat
  filter_upwards []
  intro n
  have hfinite (s : Finset ℕ) :
      IsCompactOperator (fun z => (∑ i ∈ s, R i) z) := by
    induction s using Finset.induction with
    | empty =>
        change IsCompactOperator (fun _ : CanonicalL2 => (0 : X))
        exact isCompactOperator_zero
    | @insert a s ha ih =>
        rw [Finset.sum_insert ha]
        exact (rankOne_isCompact (S (l2Basis a)) a).add ih
  exact hfinite (Finset.range n)

private lemma summable_blockEpsilon : Summable blockEpsilon := by
  have hgeom : Summable fun n : ℕ => (1 / 2 : ℝ) ^ n :=
    summable_geometric_of_norm_lt_one (by norm_num)
  apply (hgeom.mul_left ((1 / 2 : ℝ) ^ 2)).congr
  intro n
  rw [blockEpsilon, pow_add]
  ring

/-- Failure of upper semi-Fredholmness on the canonical Hilbert space yields a normalized
successive block sequence whose basis images are absolutely summable. -/
theorem exists_summable_canonicalL2Block_of_not_upperSemi
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (T : CanonicalL2 →L[ℝ] X)
    (hT : ¬ (FiniteDimensional ℝ T.toLinearMap.ker ∧
      IsClosed (T.toLinearMap.range : Set X))) :
    ∃ w : ℕ → ℕ → ℝ, ∃ hw : IsSuccessiveNormalizedBlockSequence w,
      Summable (fun n =>
        ‖T (canonicalL2BlockEmbedding w hw (lp.single 2 n 1))‖) := by
  let w := extractedBlock T hT
  let hw := extractedBlock_isSuccessive T hT
  refine ⟨w, hw, ?_⟩
  exact
    Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      (fun n => (extractedBlock_basis_bound T hT n).le)
      summable_blockEpsilon

theorem exists_compact_canonicalL2Block_of_not_upperSemi
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (T : CanonicalL2 →L[ℝ] X)
    (hT : ¬ (FiniteDimensional ℝ T.toLinearMap.ker ∧
      IsClosed (T.toLinearMap.range : Set X))) :
    ∃ w : ℕ → ℕ → ℝ, ∃ hw : IsSuccessiveNormalizedBlockSequence w,
      IsCompactOperator (T.comp (canonicalL2BlockEmbedding w hw)) := by
  obtain ⟨w, hw, hsum⟩ :=
    exists_summable_canonicalL2Block_of_not_upperSemi T hT
  refine ⟨w, hw, ?_⟩
  apply compact_of_summable_basis_images
  simpa only [l2Basis, ContinuousLinearMap.comp_apply] using hsum

end

end KaltonPeck.Support.CgpBlockExtraction

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
