/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.H1.Algebra.Membership
import LeanPool.CoarseGraining.Homogenization.Sobolev.Truncation.Approx
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.Cutoff.OpenSet

/-! # Basic -/

namespace Homogenization

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal

/-!
# Positive-part truncation and compact support in `H¹`

* `exists_h1_max_sub_const`: the positive-part truncation `(u − c)₊` lies in
  `H¹(U)` with weak gradient `1_{u>c} ∇u`, via the C¹ chain rule applied to the
  one-sided approximants `GApprox c δₙ` and an `L²` limit.
* `memH10_of_compactSupport`: an `H¹` function vanishing off a compact
  `K ⊆ U` lies in `H¹₀(U)`, via a smooth cutoff `≡ 1` on `K`.

Both are stated on `IsOpenBoundedConvexDomain U`, the hypothesis the ambient
mollification tools require.
-/

/-- **Positive-part truncation.**  For `u ∈ H¹(U)` and a level `c`, the
truncation `(u − c)₊ = max (u − c) 0` is again in `H¹(U)`, with weak gradient
`1_{u > c} ∇u` almost everywhere.

Proof: apply the C¹ chain rule (`hasWeakGradientOn_comp_of_deriv_bounded`) to the
one-sided smooth approximants `GApprox c δₙ` (`δₙ = 1/(n+1)`), then pass to the
limit with the L²-limit closure keystone; the two convergences are dominated
(`tendsto_eLpNorm_two_of_tendsto_ae_of_dominated`) using `GApprox → (·−c)₊` and
`gStep → 𝟙_{·>c}` pointwise everywhere. -/
theorem exists_h1_max_sub_const {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (u : H1Function U) (c : ℝ) :
    ∃ v : H1Function U,
      v.toFun = (fun x => max (u.toFun x - c) 0) ∧
      (∀ᵐ x ∂(volumeMeasureOn U),
        v.grad x = {y | c < u.toFun y}.indicator u.grad x) := by
  have : IsFiniteMeasure (volumeMeasureOn U) :=
    hU.isBoundedDomain.isFiniteMeasure_restrict_volume
  set δ : ℕ → ℝ := fun n => 1 / (n + 1) with hδ_def
  have hδpos : ∀ n, 0 < δ n := fun n => by positivity
  have hδlim : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hgStep_abs_le : ∀ n x, |gStep c (δ n) x| ≤ 1 := fun n x => by
    rw [abs_of_nonneg (gStep_nonneg c (δ n) x)]; exact gStep_le_one c (δ n) x
  set f : Vec d → ℝ := fun x => max (u.toFun x - c) 0 with hf_def
  set Du : Vec d → Vec d := fun x => {y | c < u.toFun y}.indicator u.grad x with hDu_def
  -- Pointwise limit of the approximants at every argument.
  have hb2 : Tendsto (fun n => 2 * δ n) atTop (𝓝 0) := by
    have h := hδlim.const_mul (2 : ℝ); rwa [mul_zero] at h
  have htend_f : ∀ x, Tendsto (fun n => GApprox c (δ n) (u.toFun x)) atTop (𝓝 (f x)) := by
    intro x
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hb2
    rw [Real.norm_eq_abs, hf_def]
    exact abs_GApprox_sub_le (hδpos n) (u.toFun x)
  have hDu_eq : ∀ x i, Du x i = (if c < u.toFun x then (1:ℝ) else 0) * u.grad x i := by
    intro x i
    by_cases h : c < u.toFun x <;> simp [hDu_def, Set.indicator_apply, h]
  -- Membership of `f` and of the target gradient coordinates in `L²`.
  have hf_aesm : AEStronglyMeasurable f (volumeMeasureOn U) :=
    (((continuous_id.sub continuous_const).max continuous_const).comp_aestronglyMeasurable
      u.memL2.1)
  have hf_memL2 : MemL2On U f := by
    refine MemLp.of_le (u.memL2.sub (memLp_const c)) hf_aesm ?_
    filter_upwards with x
    simp only [hf_def, Real.norm_eq_abs, Pi.sub_apply]
    rcases le_or_gt (u.toFun x - c) 0 with h | h
    · simp only [max_eq_right h, abs_zero]; positivity
    · rw [max_eq_left h.le]
  -- The squared-gStep sequence and the `L²` membership of the target gradient.
  have hgstep_seq_aesm : ∀ (i : Fin d) n,
      AEStronglyMeasurable (fun x => gStep c (δ n) (u.toFun x) * u.grad x i) (volumeMeasureOn U) :=
    fun i n => ((gStep_continuous c (δ n)).comp_aestronglyMeasurable u.memL2.1).mul (u.gradMemL2 i).1
  have htend_g' : ∀ (i : Fin d) x,
      Tendsto (fun n => gStep c (δ n) (u.toFun x) * u.grad x i) atTop (𝓝 (Du x i)) := by
    intro i x
    have := (tendsto_gStep (c := c) hδpos hδlim (u.toFun x)).mul_const (u.grad x i)
    rwa [← hDu_eq x i] at this
  have hgi_aesm : ∀ i, AEStronglyMeasurable (fun x => Du x i) (volumeMeasureOn U) :=
    fun i => aestronglyMeasurable_of_tendsto_ae atTop (hgstep_seq_aesm i)
      (Filter.Eventually.of_forall (htend_g' i))
  have hgi_bnd : ∀ (i : Fin d) x, |(if c < u.toFun x then (1:ℝ) else 0)| ≤ 1 := by
    intro i x; split_ifs <;> simp
  have hgi_memL2 : ∀ i, MemLp (fun x => Du x i) 2 (volumeMeasureOn U) := by
    intro i
    refine MemLp.of_le (u.gradMemL2 i) (hgi_aesm i) ?_
    filter_upwards with x
    rw [hDu_eq x i]
    simp only [norm_mul, Real.norm_eq_abs]
    calc |if c < u.toFun x then (1:ℝ) else 0| * |u.grad x i|
        ≤ 1 * |u.grad x i| := mul_le_mul_of_nonneg_right (hgi_bnd i x) (abs_nonneg _)
      _ = |u.grad x i| := one_mul _
  -- Weak gradient of `f` via the chain rule and the L²-limit closure.
  have hweak : HasWeakGradientOn U f Du := by
    intro i
    set un : ℕ → Vec d → ℝ := fun n x => GApprox c (δ n) (u.toFun x) with hun_def
    set gn : ℕ → Vec d → ℝ :=
      fun n x => deriv (GApprox c (δ n)) (u.toFun x) * u.grad x i with hgn_def
    have hun_aesm : ∀ n, AEStronglyMeasurable (un n) (volumeMeasureOn U) := fun n =>
      (GApprox_contDiff_one c (δ n)).continuous.comp_aestronglyMeasurable u.memL2.1
    have hgn_eq : ∀ n, gn n = fun x => gStep c (δ n) (u.toFun x) * u.grad x i := by
      intro n; funext x; simp only [hgn_def, deriv_GApprox]
    have hgn_aesm : ∀ n, AEStronglyMeasurable (gn n) (volumeMeasureOn U) := by
      intro n; rw [hgn_eq n]; exact hgstep_seq_aesm i n
    have hweak_n : ∀ n, HasWeakPartialDerivOn U i (un n) (gn n) := fun n =>
      (hasWeakGradientOn_comp_of_deriv_bounded hU u (GApprox_contDiff_one c (δ n))
        zero_le_one (abs_deriv_GApprox_le c (δ n))) i
    have hun_memL2 : ∀ n, MemLp (un n) 2 (volumeMeasureOn U) := by
      intro n
      refine MemLp.of_le (u.memL2.sub (memLp_const c)) (hun_aesm n) ?_
      filter_upwards with x
      rw [Real.norm_eq_abs, Real.norm_eq_abs, hun_def]
      exact abs_GApprox_le c (δ n) (u.toFun x)
    have hgn_bound : ∀ n, ∀ᵐ x ∂(volumeMeasureOn U), ‖gn n x‖ ≤ ‖u.grad x i‖ := by
      intro n
      filter_upwards with x
      simp only [hgn_eq n, norm_mul, Real.norm_eq_abs]
      calc |gStep c (δ n) (u.toFun x)| * |u.grad x i|
          ≤ 1 * |u.grad x i| :=
            mul_le_mul_of_nonneg_right (hgStep_abs_le n (u.toFun x)) (abs_nonneg _)
        _ = |u.grad x i| := one_mul _
    have hgn_memL2 : ∀ n, MemLp (gn n) 2 (volumeMeasureOn U) := fun n =>
      MemLp.of_le (u.gradMemL2 i) (hgn_aesm n) (hgn_bound n)
    have hun_conv : Tendsto
        (fun n => eLpNorm (fun x => un n x - f x) 2 (volumeMeasureOn U)) atTop (𝓝 0) :=
      tendsto_eLpNorm_two_of_tendsto_ae_of_dominated hun_aesm hf_memL2
        (u.memL2.sub (memLp_const c)).norm
        (fun n => Filter.Eventually.of_forall fun x => by
          rw [hun_def, Real.norm_eq_abs, Real.norm_eq_abs]
          exact abs_GApprox_le c (δ n) (u.toFun x))
        (Filter.Eventually.of_forall htend_f)
    have hgn_conv : Tendsto
        (fun n => eLpNorm (fun x => gn n x - Du x i) 2 (volumeMeasureOn U)) atTop (𝓝 0) :=
      tendsto_eLpNorm_two_of_tendsto_ae_of_dominated hgn_aesm (hgi_memL2 i)
        (u.gradMemL2 i).norm hgn_bound
        (Filter.Eventually.of_forall fun x => by
          simpa only [hgn_eq] using htend_g' i x)
    exact hasWeakPartialDerivOn_of_tendsto_L2 hf_memL2 (hgi_memL2 i) hun_memL2 hgn_memL2
      hweak_n hun_conv hgn_conv
  exact ⟨⟨f, Du, hf_memL2, hgi_memL2, hweak⟩, rfl,
    Filter.Eventually.of_forall (fun _ => rfl)⟩

/-- **Compact support implies `H¹₀`.**  An `H¹(U)` function that vanishes off a
compact `K ⊆ U` lies in `H¹₀(U)`.

Proof: pick a smooth cutoff `χ ≡ 1` on `K` with `tsupport χ ⊆ U`; then `χ·u`
is in `H¹₀` by the library's cutoff-membership lemma, and `χ·u = u` since `u` vanishes
off `K`. -/
theorem memH10_of_compactSupport {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (u : H1Function U)
    {K : Set (Vec d)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hzero : ∀ x, x ∉ K → u.toFun x = 0) :
    MemH10 U u.toFun := by
  -- Smooth cutoff `χ ≡ 1` on `K`, `0 ≤ χ ≤ 1`, `tsupport χ ⊆ U`.
  obtain ⟨χ, hχ_smooth, _hχ_bounds, hχ_one, hχ_tsupport⟩ :=
    exists_contDiff_one_on_compact_tsupport_subset hK hKU hU.isOpen
  -- `tsupport χ` is closed and lies in the bounded set `U`, hence compact.
  have hχ_compact : HasCompactSupport χ :=
    Metric.isCompact_of_isClosed_isBounded (isClosed_tsupport χ)
      (hU.isBoundedDomain.isBounded.subset hχ_tsupport)
  -- `χ · u` is in `H¹₀(U)` by the library's cutoff-membership lemma.
  have hmem : MemH10 U (fun x => χ x * u.toFun x) :=
    memH10_mul_of_contDiff_hasCompactSupport hU hχ_smooth hχ_compact hχ_tsupport ⟨u, rfl⟩
  -- But `χ · u = u` pointwise: `χ = 1` on `K`, and `u = 0` off `K`.
  have heq : (fun x => χ x * u.toFun x) = u.toFun := by
    funext x
    by_cases hx : x ∈ K
    · rw [show χ x = 1 from by simpa using hχ_one hx, one_mul]
    · rw [hzero x hx, mul_zero]
  rwa [heq] at hmem

end Homogenization
