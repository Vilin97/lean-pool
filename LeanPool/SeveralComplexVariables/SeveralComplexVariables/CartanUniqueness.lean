/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Normed.Group.Bounded
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.Analyticity
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.Biholomorphic
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.Montel

/-!
# Cartan uniqueness on bounded domains

The theorem in this file concerns holomorphic self-maps of bounded finite-dimensional domains.
It is Cartan's uniqueness theorem from [Scheidemann][Scheidemann2005] (2005), Theorem 3.3.1,
[Jakóbczak–Jarnicki][JakobczakJarnicki2021] (2021), Theorem 2.3.2, and [Lebl][Lebl2026] (2026),
Section 1.5. It is independent of sheaves and of Cartan's theorems A and B.

The proof averages the bounded iterates and uses Montel's theorem to extract a locally uniform
limit. Derivative convergence gives identity derivative at the fixed point. Telescoping gives
invariance of the limit under the original map, so local injectivity and the identity principle
force the original map to be the identity.

## Main results

`eqOn_id_of_mapsTo_of_fderiv_eq_id` is Cartan's uniqueness theorem: a holomorphic self-map of a
bounded domain which fixes a point and has identity derivative there is the identity on the
connected component of that point.

## References

* [P. Jakóbczak and M. Jarnicki, *Lectures on Holomorphic Functions of Several Complex
  Variables*][JakobczakJarnicki2021]
* [J. Lebl, *Tasty Bits of Several Complex Variables: A Whirlwind Tour of the Subject*][Lebl2026]
* [V. Scheidemann, *Introduction to Complex Analysis in Several Variables*][Scheidemann2005]
-/

public section

open Set Filter
open scoped Topology

namespace SeveralComplexVariables

/-- **Cartan's uniqueness theorem.** A holomorphic self-map of a bounded connected open set
that fixes an interior point and has identity derivative there is the identity on the set.
Boundedness is essential; no injectivity or surjectivity of the map is assumed.
The formulation includes zero-dimensional domains. -/
theorem eqOn_id_of_mapsTo_of_fderiv_eq_id
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {U : Set E} (hU : IsOpen U) (hconn : IsPreconnected U) (hb : Bornology.IsBounded U)
    {f : E → E} (hf : AnalyticOnNhd ℂ f U) (hmaps : MapsTo f U U)
    {a : E} (ha : a ∈ U) (hfix : f a = a)
    (hderiv : fderiv ℂ f a = ContinuousLinearMap.id ℂ E) : EqOn f id U := by
  classical
  let : CompleteSpace E := FiniteDimensional.complete ℂ E
  obtain ⟨M, hM0, hM⟩ := hb.exists_pos_norm_le
  let A (n : ℕ) (z : E) : E := ((n + 1 : ℕ) : ℂ)⁻¹ •
    ∑ k ∈ Finset.range (n + 1), f^[k] z
  have hA (n : ℕ) : AnalyticOnNhd ℂ (A n) U :=
    ((DifferentiableOn.fun_sum (fun k _ => hf.differentiableOn.iterate hmaps k)).const_smul
      ((n + 1 : ℕ) : ℂ)⁻¹).analyticOnNhd_of_finiteDimensional hU
  have hAb (n : ℕ) (z : E) (hz : z ∈ U) : ‖A n z‖ ≤ M := by
    have hn : (0 : ℝ) < n + 1 := by positivity
    calc
      ‖A n z‖ = ((n : ℝ) + 1)⁻¹ * ‖∑ k ∈ Finset.range (n + 1), f^[k] z‖ := by
        dsimp only [A]
        rw [norm_smul, norm_inv, norm_natCast, Nat.cast_add, Nat.cast_one]
      _ ≤ ((n : ℝ) + 1)⁻¹ * (((n : ℝ) + 1) * M) := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hn.le)
        calc
          _ ≤ ∑ k ∈ Finset.range (n + 1), ‖f^[k] z‖ := norm_sum_le _ _
          _ ≤ ∑ _k ∈ Finset.range (n + 1), M :=
            Finset.sum_le_sum fun k _ => hM _ (hmaps.iterate k hz)
          _ = _ := by simp
      _ = M := by field_simp
  have hfd : HasFDerivAt f (ContinuousLinearMap.id ℂ E) a := by
    rw [← hderiv]
    exact (hf a ha).differentiableAt.hasFDerivAt
  have hAd (n : ℕ) : fderiv ℂ (A n) a = ContinuousLinearMap.id ℂ E := by
    have hk (k : ℕ) : HasFDerivAt f^[k] (ContinuousLinearMap.id ℂ E) a := by
      simpa only [← ContinuousLinearMap.one_def, one_pow] using hfd.iterate hfix k
    have H := (HasFDerivAt.fun_sum (u := Finset.range (n + 1)) (fun k _ => hk k)).const_smul
      ((n + 1 : ℕ) : ℂ)⁻¹
    have hn : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    simpa only [A, Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul ℂ,
      smul_smul, inv_mul_cancel₀ hn, one_smul, Pi.smul_def] using H.fderiv
  obtain ⟨g, φ, hφ, hg, hlim⟩ :=
    exists_subseq_tendstoLocallyUniformlyOn_of_uniform_bound hU hA hAb
  have hgd : fderiv ℂ g a = ContinuousLinearMap.id ℂ E := by
    have H := (hlim.fderiv_of_finiteDimensional (.of_forall fun n => hA (φ n)) hU).tendsto_at ha
    simp only [hAd] at H
    exact tendsto_nhds_unique H tendsto_const_nhds
  have htel (n : ℕ) (z : E) : A n (f z) - A n z =
      ((n + 1 : ℕ) : ℂ)⁻¹ • (f^[n + 1] z - z) := by
    dsimp only [A]
    rw [← smul_sub, ← Finset.sum_sub_distrib]
    congr 1
    simpa only [Function.iterate_succ_apply, Function.iterate_zero_apply] using
      (Finset.sum_range_sub (fun k => f^[k] z) (n + 1))
  have hzero (z : E) (hz : z ∈ U) :
      Tendsto (fun n => A n (f z) - A n z) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => ?_)
      (show Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹ * (2 * M)) atTop (𝓝 0) by
        simpa only [one_div, zero_mul] using
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const (2 * M))
    rw [htel, norm_smul, norm_inv, norm_natCast, Nat.cast_add, Nat.cast_one]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact (norm_sub_le _ _).trans (by linarith [hM _ (hmaps.iterate (n + 1) hz), hM z hz])
  have hgf (z : E) (hz : z ∈ U) : g (f z) = g z := by
    have H := (hlim.tendsto_at (hmaps hz)).sub (hlim.tendsto_at hz)
    exact sub_eq_zero.mp (tendsto_nhds_unique H ((hzero z hz).comp hφ.tendsto_atTop))
  obtain ⟨V, hV, haV, _, hinj⟩ := exists_open_injOn_of_injective_fderiv hU hg.differentiableOn ha
    (by rw [hgd]; exact Function.injective_id)
  have heq : f =ᶠ[𝓝 a] id := by
    have hpre : f ⁻¹' V ∈ 𝓝 a := (hf a ha).continuousAt.preimage_mem_nhds
      (hV.mem_nhds (by simpa only [hfix] using haV))
    filter_upwards [hU.mem_nhds ha, hV.mem_nhds haV, hpre] with z hz hzV hfzV
    exact hinj hfzV hzV (hgf z hz)
  exact hf.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_id hconn ha heq

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
