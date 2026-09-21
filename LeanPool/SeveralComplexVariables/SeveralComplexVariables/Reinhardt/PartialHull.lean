/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.Reinhardt.Extension

/-!
# Completion in selected Reinhardt coordinates

The selected coordinates can decrease in modulus; the others retain their moduli. On Reinhardt
sets this is precisely coordinate contraction without a coordinate ordering. The geometric hull
works for arbitrary index types, and its openness is proved. For finite coordinates, absolute
convergence and vanishing of the relevant negative Laurent coefficients give locally uniform
convergence and an analytic sum on the hull. These coefficient-series results are independent of
the Laurent expansion theorem; extension of arbitrary holomorphic functions is deduced from that
theorem. Reference: [Scheidemann][Scheidemann2005] (2005), Corollary 2.1.15.

## Main results

`IsCompleteReinhardtIn` is completeness in a selected set of coordinates. `partialReinhardtHull`
is the corresponding hull. `exists_extension_partialReinhardtHull` extends a holomorphic
function to that hull. `hasSumLocallyUniformlyOn_laurent_partialReinhardtHull` is locally
uniform convergence of the relevant Laurent terms.

## References

* [V. Scheidemann, *Introduction to Complex Analysis in Several Variables*][Scheidemann2005]
-/

public section

open Set Filter
open scoped Topology

namespace SeveralComplexVariables

variable {ι : Type*} {U V : Set (ι → ℂ)} {I : Set ι}

/-- Reinhardt completeness restricted to a specified set of coordinates. -/
@[expose] def IsCompleteReinhardtIn (I : Set ι) (U : Set (ι → ℂ)) : Prop :=
  ∀ ⦃z⦄, z ∈ U → ∀ ⦃w⦄, (∀ i, ‖w i‖ ≤ ‖z i‖) →
    (∀ i ∉ I, ‖w i‖ = ‖z i‖) → w ∈ U

/-- The hull formed by contracting selected moduli and preserving all other moduli. -/
@[expose] def partialReinhardtHull (I : Set ι) (U : Set (ι → ℂ)) : Set (ι → ℂ) :=
  {w | ∃ z ∈ U, (∀ i, ‖w i‖ ≤ ‖z i‖) ∧ ∀ i ∉ I, ‖w i‖ = ‖z i‖}

/-- The original set is contained in its partial hull. -/
theorem subset_partialReinhardtHull : U ⊆ partialReinhardtHull I U :=
  fun z hz => ⟨z, hz, fun _ => le_rfl, fun _ _ => rfl⟩

/-- Partial completeness includes Reinhardt symmetry. -/
theorem IsCompleteReinhardtIn.isReinhardt (h : IsCompleteReinhardtIn I U) :
    IsReinhardt U := fun _ hz _ he => h hz (fun i => (he i).le) (fun i _ => he i)

/-- The partial hull has the stated partial completeness property. -/
theorem isCompleteReinhardtIn_partialReinhardtHull :
    IsCompleteReinhardtIn I (partialReinhardtHull I U) := by
  rintro z ⟨v, hv, hle, heq⟩ w hwl hwe
  exact ⟨v, hv, fun i => (hwl i).trans (hle i), fun i hi => (hwe i hi).trans (heq i hi)⟩

/-- The partial hull is the smallest partially complete Reinhardt superset. -/
theorem partialReinhardtHull_min (hUV : U ⊆ V) (hV : IsCompleteReinhardtIn I V) :
    partialReinhardtHull I U ⊆ V := by
  rintro w ⟨z, hz, hle, heq⟩
  exact hV (hUV hz) hle heq

/-- Every partial hull retains independent coordinate rotations. -/
theorem isReinhardt_partialReinhardtHull : IsReinhardt (partialReinhardtHull I U) :=
  isCompleteReinhardtIn_partialReinhardtHull.isReinhardt

/-- Partial completion is monotone in the original set. -/
theorem partialReinhardtHull_mono (hUV : U ⊆ V) :
    partialReinhardtHull I U ⊆ partialReinhardtHull I V :=
  partialReinhardtHull_min (hUV.trans subset_partialReinhardtHull)
    isCompleteReinhardtIn_partialReinhardtHull

/-- Completing twice in the same coordinates has no further effect. -/
theorem partialReinhardtHull_idem :
    partialReinhardtHull I (partialReinhardtHull I U) = partialReinhardtHull I U :=
  Subset.antisymm (partialReinhardtHull_min Subset.rfl isCompleteReinhardtIn_partialReinhardtHull)
    subset_partialReinhardtHull

/-- Completion in all coordinates recovers the existing complete Reinhardt hull. -/
theorem partialReinhardtHull_univ : partialReinhardtHull univ U = completeReinhardtHull U := by
  ext z
  simp [partialReinhardtHull, completeReinhardtHull]

/-- With no selected coordinates, a Reinhardt set is unchanged. -/
theorem partialReinhardtHull_empty (hU : IsReinhardt U) : partialReinhardtHull ∅ U = U := by
  apply Subset.antisymm ?_ subset_partialReinhardtHull
  rintro w ⟨z, hz, _, he⟩
  exact hU hz (fun i => he i (by simp))

/-- Partial hulls of open Reinhardt sets are open. A continuous modulus majorant supplies nearby
witnesses in the original open set. -/
theorem isOpen_partialReinhardtHull [Fintype ι] (ho : IsOpen U) (hR : IsReinhardt U) :
    IsOpen (partialReinhardtHull I U) := by
  classical
  rw [isOpen_iff_mem_nhds]
  rintro w ⟨z, hz, hle, heq⟩
  let v : (ι → ℂ) → (ι → ℂ) := fun x i =>
    if i ∈ I then (max ‖x i‖ ‖z i‖ : ℝ) else (‖x i‖ : ℝ)
  have hv : Continuous v := by
    apply continuous_pi
    intro i
    dsimp [v]
    split_ifs <;> fun_prop
  have hvw : v w ∈ U := by
    apply hR hz
    intro i
    by_cases hi : i ∈ I
    · simp [v, hi, max_eq_right (hle i)]
    · simp [v, hi, heq i hi]
  apply Filter.mem_of_superset (hv.continuousAt.preimage_mem_nhds (ho.mem_nhds hvw))
  intro x hx
  refine ⟨v x, hx, ?_, ?_⟩
  · intro i
    by_cases hi : i ∈ I
    · simp [v, hi, abs_of_nonneg (le_trans (norm_nonneg _) (le_max_left _ _))]
    · simp [v, hi]
  · intro i hi
    simp [v, hi]

/-- A Laurent monomial is largest at the corner selected by its exponent signs. Summing over all
corners gives a bound independent of the signs. -/
private theorem norm_laurentTerm_le_sum_corners {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F] (c : (Fin n → ℤ) → F)
    (a b : Fin n → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (m : Fin n → ℤ) (x : Fin n → ℂ)
    (hupper : ∀ i, ‖x i‖ ≤ b i)
    (hlower : c m ≠ 0 → ∀ i, m i < 0 → a i ≤ ‖x i‖) :
    ‖multivariableLaurentTerm c m x‖ ≤
      ∑ s : Finset (Fin n), ‖multivariableLaurentTerm c m
        (fun i => ((if i ∈ s then b i else a i) : ℂ))‖ := by
  classical
  by_cases hc : c m = 0
  · simp [multivariableLaurentTerm, hc]
  let s := Finset.univ.filter (fun i => 0 ≤ m i)
  have hcoord (i : Fin n) : ‖x i‖ ^ m i ≤
      ‖((if i ∈ s then b i else a i) : ℂ)‖ ^ m i := by
    by_cases hi : 0 ≤ m i
    · simpa [s, hi, abs_of_pos (hb i)] using
        zpow_le_zpow_left₀ hi (norm_nonneg _) (hupper i)
    · have hmi : m i < 0 := lt_of_not_ge hi
      have hpow := zpow_le_zpow_left₀ (neg_nonneg.mpr hmi.le) (ha i).le (hlower hc i hmi)
      have hinv := one_div_le_one_div_of_le (zpow_pos (ha i) (-m i)) hpow
      simpa [s, hi, abs_of_pos (ha i), one_div, zpow_neg] using hinv
  calc
    ‖multivariableLaurentTerm c m x‖ ≤ ‖multivariableLaurentTerm c m
        (fun i => ((if i ∈ s then b i else a i) : ℂ))‖ := by
      simp only [multivariableLaurentTerm, norm_smul, norm_prod, norm_zpow]
      exact mul_le_mul_of_nonneg_right
        (Finset.prod_le_prod₀ (fun i _ => zpow_nonneg (norm_nonneg _) _) (fun i _ => hcoord i))
        (norm_nonneg _)
    _ ≤ _ := Finset.single_le_sum
      (f := fun t : Finset (Fin n) => ‖multivariableLaurentTerm c m
        (fun i => ((if i ∈ t then b i else a i) : ℂ))‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ s)

/-- Near a point of the partial hull, choose upper and lower radii whose finitely many corners lie
in the original domain. Lower bounds are needed only in coordinates where a nonzero Laurent
coefficient has negative exponent. -/
private theorem exists_laurent_box_partialHull {n : ℕ} {I : Set (Fin n)}
    {U : Set (Fin n → ℂ)} (ho : IsOpen U) (hR : IsReinhardt U)
    {F : Type*} [Zero F] (c : (Fin n → ℤ) → F)
    (hzero : ∀ m i, (i ∈ I ∨ ∃ z ∈ U, z i = 0) → m i < 0 → c m = 0)
    {w : Fin n → ℂ} (hw : w ∈ partialReinhardtHull I U) :
    ∃ a b : Fin n → ℝ, (∀ i, 0 < a i) ∧ (∀ i, 0 < b i) ∧
      (∀ s : Finset (Fin n), (fun i => ((if i ∈ s then b i else a i) : ℂ)) ∈ U) ∧
      (∀ i, ‖w i‖ < b i) ∧ (∀ m, c m ≠ 0 → ∀ i, m i < 0 → a i < ‖w i‖) := by
  classical
  obtain ⟨z, hz, hwz, hweq⟩ := hw
  let v (s : Finset (Fin n)) (t : ℝ) : Fin n → ℂ := fun i =>
    if z i = 0 then (t : ℂ) else ((1 + (if i ∈ s then t else -t)) * ‖z i‖ : ℝ)
  have hv (s : Finset (Fin n)) : Continuous (v s) := by
    apply continuous_pi
    intro i
    dsimp [v]
    split_ifs <;> fun_prop
  have hv0 (s : Finset (Fin n)) : v s 0 ∈ U := by
    apply hR hz
    intro i
    by_cases hi : z i = 0 <;> simp [v, hi]
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ s : Finset (Fin n), v s t ∈ U :=
    eventually_all.mpr fun s => (hv s).continuousAt.preimage_mem_nhds (ho.mem_nhds (hv0 s))
  obtain ⟨δ, hδ, hδv⟩ := Metric.eventually_nhds_iff.mp hev
  let ε := min (δ / 2) (1 / 2)
  have hε : 0 < ε := lt_min (half_pos hδ) (by norm_num)
  have hεδ : ε < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
  have hε1 : ε < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hcorners := hδv (show dist ε 0 < δ by simpa [Real.dist_eq, abs_of_pos hε] using hεδ)
  let a : Fin n → ℝ := fun i => if z i = 0 then ε else (1 - ε) * ‖z i‖
  let b : Fin n → ℝ := fun i => if z i = 0 then ε else (1 + ε) * ‖z i‖
  have ha (i : Fin n) : 0 < a i := by
    dsimp [a]
    split_ifs with hi
    · exact hε
    · exact mul_pos (sub_pos.mpr hε1) (norm_pos_iff.mpr hi)
  have hb (i : Fin n) : ‖z i‖ < b i := by
    dsimp [b]
    split_ifs with hi
    · simpa [hi] using hε
    · nlinarith [norm_pos_iff.mpr hi]
  refine ⟨a, b, ha, fun i => (norm_nonneg _).trans_lt (hb i), ?_,
    fun i => (hwz i).trans_lt (hb i), ?_⟩
  · intro s
    convert hcorners s using 1
    ext i
    by_cases hi : z i = 0 <;> by_cases his : i ∈ s <;> simp [a, b, v, hi, his, sub_eq_add_neg]
  · intro m hm i hmi
    have hi : i ∉ I := fun hi => hm (hzero m i (Or.inl hi) hmi)
    have hzi : z i ≠ 0 := fun hzi => hm (hzero m i (Or.inr ⟨z, hz, hzi⟩) hmi)
    rw [hweq i hi]
    dsimp [a]
    rw [ite_eq_right hzi]
    nlinarith [norm_pos_iff.mpr hzi]

/-- An absolutely convergent Laurent series on an open Reinhardt set converges locally uniformly on
its partial hull when the relevant negative coefficients vanish. This convergence argument is
independent of Laurent expansion for functions. -/
theorem hasSumLocallyUniformlyOn_laurent_partialReinhardtHull
    {n : ℕ} {I : Set (Fin n)} {U : Set (Fin n → ℂ)}
    (ho : IsOpen U) (hR : IsReinhardt U)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (c : (Fin n → ℤ) → F)
    (hsum : ∀ z ∈ U, Summable (fun m => ‖multivariableLaurentTerm c m z‖))
    (hzero : ∀ m i, (i ∈ I ∨ ∃ z ∈ U, z i = 0) → m i < 0 → c m = 0) :
    HasSumLocallyUniformlyOn (multivariableLaurentTerm c)
      (fun z => ∑' m, multivariableLaurentTerm c m z) (partialReinhardtHull I U) := by
  classical
  apply hasSumLocallyUniformlyOn_of_of_forall_exists_nhds
  intro w hw
  obtain ⟨a, b, ha, hb, hcorners, hupper, hlower⟩ :=
    exists_laurent_box_partialHull ho hR c hzero hw
  let W : Set (Fin n → ℂ) := {x | ∀ i, ‖x i‖ < b i ∧ (a i < ‖w i‖ → a i < ‖x i‖)}
  have hW : IsOpen W := by
    simp only [W, ofPred_forall, ofPred_and]
    apply isOpen_iInter_of_finite
    intro i
    apply IsOpen.inter (isOpen_lt (continuous_apply i).norm continuous_const)
    apply isOpen_iInter_of_finite
    intro _
    exact isOpen_lt continuous_const (continuous_apply i).norm
  have hwW : w ∈ W := fun i => ⟨hupper i, fun h => h⟩
  refine ⟨W, nhdsWithin_le_nhds (hW.mem_nhds hwW), ?_⟩
  apply hasSumUniformlyOn_iff_tendstoUniformlyOn.mpr
  have hs : Summable (fun m => ∑ t : Finset (Fin n),
      ‖multivariableLaurentTerm c m (fun i => ((if i ∈ t then b i else a i) : ℂ))‖) :=
    summable_sum (fun t _ => hsum _ (hcorners t))
  apply tendstoUniformlyOn_tsum hs
  intro m x hx
  exact norm_laurentTerm_le_sum_corners c a b ha hb m x
    (fun i => (hx i).1.le) (fun hm i hmi => ((hx i).2 (hlower m hm i hmi)).le)

/-- The Laurent sum is analytic on the partial hull. A term with a negative exponent is either
identically zero or has no coordinate singularity on the hull. -/
theorem analyticOnNhd_laurentSum_partialReinhardtHull
    {n : ℕ} {I : Set (Fin n)} {U : Set (Fin n → ℂ)}
    (ho : IsOpen U) (hR : IsReinhardt U)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (c : (Fin n → ℤ) → F)
    (hsum : ∀ z ∈ U, Summable (fun m => ‖multivariableLaurentTerm c m z‖))
    (hzero : ∀ m i, (i ∈ I ∨ ∃ z ∈ U, z i = 0) → m i < 0 → c m = 0) :
    AnalyticOnNhd ℂ (fun z => ∑' m, multivariableLaurentTerm c m z)
      (partialReinhardtHull I U) := by
  apply (hasSumLocallyUniformlyOn_laurent_partialReinhardtHull ho hR c hsum hzero).analyticOnNhd_pi
    _ (isOpen_partialReinhardtHull ho hR)
  intro m w hw
  change AnalyticAt ℂ (fun z => (∏ i, z i ^ m i) • c m) w
  by_cases hm : c m = 0
  · simpa only [hm, smul_zero] using
      (analyticAt_const : AnalyticAt ℂ (fun _ : Fin n → ℂ => (0 : F)) w)
  apply AnalyticAt.smul _ analyticAt_const
  apply Finset.analyticAt_fun_prod
  intro i _
  by_cases hi : 0 ≤ m i
  · exact ((ContinuousLinearMap.proj (R := ℂ) i).analyticAt w).zpow_nonneg hi
  · apply ((ContinuousLinearMap.proj (R := ℂ) i).analyticAt w).zpow
    intro hwi
    change w i = 0 at hwi
    have hmi : m i < 0 := lt_of_not_ge hi
    by_cases hiI : i ∈ I
    · exact hm (hzero m i (Or.inl hiI) hmi)
    · obtain ⟨z, hz, _, hweq⟩ := hw
      have hzi : z i = 0 := norm_eq_zero.mp (by simpa [hwi] using (hweq i hiI).symm)
      exact hm (hzero m i (Or.inr ⟨z, hz, hzi⟩) hmi)

/-- Extension in the coordinates whose zero hyperplanes meet the connected domain. The Laurent
expansion theorem supplies the coefficients and their vanishing; the series converges locally
uniformly and is analytic on the partial hull. This deduction depends on the Laurent expansion.
No common point on the hyperplanes is required. -/
theorem exists_extension_partialReinhardtHull {n : ℕ} {I : Set (Fin n)}
    {U : Set (Fin n → ℂ)} (ho : IsOpen U) (hc : IsConnected U) (hR : IsReinhardt U)
    (hmeet : ∀ i ∈ I, ∃ z ∈ U, z i = 0)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {f : (Fin n → ℂ) → F} (hf : AnalyticOnNhd ℂ f U) :
    ∃ g, AnalyticOnNhd ℂ g (partialReinhardtHull I U) ∧ EqOn g f U := by
  obtain ⟨z₀, hz₀⟩ := hc.nonempty
  obtain ⟨r, hrU, hzr⟩ := hR.exists_strict_modulus_majorant ho hz₀
  have hr : ∀ i, (0 : ℝ) < r i := fun i => (norm_nonneg _).trans_lt (hzr i)
  obtain ⟨hsum, hnorm, hneg, _, _⟩ := multivariableLaurent_expansion ho hc.isPreconnected hR hf hr
    hrU
  let c := multivariableLaurentCoeff f (fun i => (r i : ℝ))
  have hzero : ∀ m i, (i ∈ I ∨ ∃ z ∈ U, z i = 0) → m i < 0 → c m = 0 := by
    intro m i hi hmi
    exact hneg m i (hi.elim (hmeet i) id) hmi
  exact ⟨fun z => ∑' m, multivariableLaurentTerm c m z,
    analyticOnNhd_laurentSum_partialReinhardtHull ho hR c hnorm hzero,
    fun z hz => (hsum.hasSum hz).tsum_eq⟩

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
