/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.RingTheory.Finiteness.Finsupp
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Analysis.Complex.Basic

/-!
# The Schwartz cospan lemma (`finiteness-and-chi`, Banach half)

Unit: finiteness-and-chi (`docs/design/finiteness-and-chi.md` §0 (D-b), §4.3, §6.1–6.2).

Pure Banach-space material, **zero project dependencies** (D6: no manifold variables at all).
This file is the make-or-break analytic core of the unit: it replaces Forster's §14.3/14.5/14.7
(finite-codimensional `ε`-contraction subspaces, iterated with Hilbert-space orthogonal
complements) by one abstract statement, the classical L. Schwartz perturbation lemma
specialized to the cospan form we need:

* `schwartz_finite_cospan`: if `u v : E →L[ℂ] F` are continuous linear maps between Banach
  spaces, `u` surjective and `v` compact, then there is a finite-dimensional `S ≤ F` with
  `F = range (u - v) + S` (span form — we never need closedness of `range (u - v)`, only
  dimensions of quotients of it, so the harder half of Schwartz's theorem is not proved here).
* `finiteDimensional_of_cospan`: the consumer form used by `Chain.lean`/`TradeBounded.lean`:
  any `P` linearly hit by `F` and killed on `range (u - v)` is finite-dimensional.
* `FiniteDimensional.of_linearMap_ker_range`: the "extension" helper (finite kernel + finite
  codomain ⇒ finite domain) reused by both all-`D` finiteness steps and the χ ledger.

The proof of `schwartz_finite_cospan` mirrors mathlib's own proof of
`ContinuousLinearMap.exists_preimage_norm_le` (`Analysis/Normed/Operator/Banach.lean`) in
texture: `Function.iterate`, `Summable.of_norm`, `summable_geometric_of_lt_one`, telescoping,
`tendsto_nhds_unique` — with an extra finite-dimensional "escape" term `s ∈ S` carried in
parallel with the approximate-preimage term `e`, since we only get a compact (not surjective)
perturbation `v` to correct for. Forster's open-mapping step 14.6(b) survives as the first line
(`u.exists_preimage_norm_le hu`); Montel-compactness of `v` enters only via
`IsCompactOperator.isCompact_closure_image_closedBall` (the forward form — the iff-lemma
`isCompactOperator_iff_isCompact_closure_image_closedBall` hits a deterministic `isDefEq`
timeout at `E →L[ℂ] F`, per the spike `scratch_finiteness.lean` §11).
-/

open Metric Function

namespace RS

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- **Schwartz's perturbation lemma**, cospan/span form: a compact perturbation `v` of a
surjective continuous linear map `u` between Banach spaces has finite-codimensional range —
every `f : F` is `u e - v e` up to a finite-dimensional correction `S`, independent of `f`. -/
theorem schwartz_finite_cospan (u v : E →L[ℂ] F) (hu : Surjective u) (hv : IsCompactOperator v) :
    ∃ S : Submodule ℂ F, FiniteDimensional ℂ S ∧ ∀ f : F, ∃ e : E, f - (u e - v e) ∈ S := by
  obtain ⟨C₀, hC₀, hpre⟩ := u.exists_preimage_norm_le hu
  set C : ℝ := max C₀ 1 with hC_def
  have hC : (0 : ℝ) < C := lt_max_of_lt_right one_pos
  have hpreC : ∀ y : F, ∃ x, u x = y ∧ ‖x‖ ≤ C * ‖y‖ := by
    intro y
    obtain ⟨x, hx, hxle⟩ := hpre y
    exact ⟨x, hx, hxle.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg y))⟩
  have hK : IsCompact (closure (v '' Metric.closedBall (0 : E) C)) :=
    hv.isCompact_closure_image_closedBall C
  obtain ⟨t, -, htf, htcov⟩ := finite_cover_balls_of_compact hK (by norm_num : (0 : ℝ) < 2⁻¹)
  set S : Submodule ℂ F := Submodule.span ℂ t with hS_def
  have hSfd : FiniteDimensional ℂ S := FiniteDimensional.span_of_finite ℂ htf
  obtain ⟨R', hR'⟩ := (htf.image (‖·‖ : F → ℝ)).bddAbove
  set R : ℝ := max R' 0 with hR_def
  have hRnn : (0 : ℝ) ≤ R := le_max_right _ _
  have hRt : ∀ y ∈ t, ‖y‖ ≤ R := fun y hy => (hR' ⟨y, hy, rfl⟩).trans (le_max_left _ _)
  -- **Single-step lemma**: every `f` is corrected to within half its norm by `u e - v e`, up
  -- to a finite-dimensional (in fact `S`-valued) error, with quantitative control on `e`/error.
  have step : ∀ f : F, ∃ (e : E) (s : F), s ∈ S ∧ ‖e‖ ≤ C * ‖f‖ ∧ ‖s‖ ≤ R * ‖f‖ ∧
      ‖f - ((u e - v e) + s)‖ ≤ 2⁻¹ * ‖f‖ := by
    intro f
    rcases eq_or_ne f 0 with rfl | hf0
    · exact ⟨0, 0, S.zero_mem, by simp, by simp, by simp⟩
    · obtain ⟨e, hue, hee⟩ := hpreC f
      have hfpos : (0 : ℝ) < ‖f‖ := norm_pos_iff.mpr hf0
      have hfC : (‖f‖ : ℂ) ≠ 0 := by exact_mod_cast hfpos.ne'
      set w : E := (‖f‖ : ℂ)⁻¹ • e with hw_def
      have hwnorm : ‖w‖ ≤ C := by
        rw [hw_def, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hfpos, inv_mul_le_iff₀ hfpos]
        calc ‖e‖ ≤ C * ‖f‖ := hee
          _ = ‖f‖ * C := mul_comm _ _
      have hmemball : v w ∈ v '' Metric.closedBall (0 : E) C :=
        ⟨w, Metric.mem_closedBall.mpr (by rw [dist_zero_right]; exact hwnorm), rfl⟩
      have hcov := htcov (subset_closure hmemball)
      simp only [Set.mem_iUnion] at hcov
      obtain ⟨y, hyt, hy⟩ := hcov
      have hew : e = (‖f‖ : ℂ) • w := by
        rw [hw_def, smul_smul, mul_inv_cancel₀ hfC, one_smul]
      have hve : v e = (‖f‖ : ℂ) • v w := by rw [hew, map_smul]
      refine ⟨e, (‖f‖ : ℂ) • y, S.smul_mem _ (Submodule.subset_span hyt), hee, ?_, ?_⟩
      · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hfpos]
        have := hRt y hyt
        nlinarith [norm_nonneg y]
      · have hcalc : f - ((u e - v e) + (‖f‖ : ℂ) • y) = (‖f‖ : ℂ) • (v w - y) := by
          rw [hue, hve, smul_sub]; abel
        rw [hcalc, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hfpos]
        have hyb : ‖v w - y‖ ≤ 2⁻¹ := by
          rw [← dist_eq_norm]; exact (Metric.mem_ball.mp hy).le
        nlinarith [hfpos.le]
  choose e s hsS he hs hrem using step
  let nextF : F → F := fun f => f - ((u (e f) - v (e f)) + s f)
  refine ⟨S, hSfd, fun f₀ => ?_⟩
  set fk : ℕ → F := fun k => nextF^[k] f₀ with hfk_def
  have hfk_succ : ∀ k, fk (k + 1) = nextF (fk k) := by
    intro k; rw [hfk_def]; exact Function.iterate_succ_apply' nextF k f₀
  have hdecay : ∀ k, ‖fk k‖ ≤ (2⁻¹ : ℝ) ^ k * ‖f₀‖ := by
    intro k
    induction k with
    | zero => simp [hfk_def]
    | succ k IH =>
      rw [hfk_succ]
      calc ‖nextF (fk k)‖ ≤ 2⁻¹ * ‖fk k‖ := hrem (fk k)
        _ ≤ 2⁻¹ * ((2⁻¹ : ℝ) ^ k * ‖f₀‖) := by gcongr
        _ = (2⁻¹ : ℝ) ^ (k + 1) * ‖f₀‖ := by ring
  have hbound_e : ∀ k, ‖e (fk k)‖ ≤ C * ‖f₀‖ * (2⁻¹ : ℝ) ^ k := by
    intro k
    calc ‖e (fk k)‖ ≤ C * ‖fk k‖ := he (fk k)
      _ ≤ C * ((2⁻¹ : ℝ) ^ k * ‖f₀‖) := by gcongr; exact hdecay k
      _ = C * ‖f₀‖ * (2⁻¹ : ℝ) ^ k := by ring
  have hbound_s : ∀ k, ‖s (fk k)‖ ≤ R * ‖f₀‖ * (2⁻¹ : ℝ) ^ k := by
    intro k
    calc ‖s (fk k)‖ ≤ R * ‖fk k‖ := hs (fk k)
      _ ≤ R * ((2⁻¹ : ℝ) ^ k * ‖f₀‖) := by gcongr; exact hdecay k
      _ = R * ‖f₀‖ * (2⁻¹ : ℝ) ^ k := by ring
  have hsum_e : Summable (fun k => e (fk k)) := Summable.of_norm
    (Summable.of_nonneg_of_le (fun k => norm_nonneg _) hbound_e
      (Summable.mul_left (C * ‖f₀‖)
        (summable_geometric_of_lt_one (r := (2⁻¹ : ℝ)) (by norm_num) (by norm_num))))
  have hsum_s : Summable (fun k => s (fk k)) := Summable.of_norm
    (Summable.of_nonneg_of_le (fun k => norm_nonneg _) hbound_s
      (Summable.mul_left (R * ‖f₀‖)
        (summable_geometric_of_lt_one (r := (2⁻¹ : ℝ)) (by norm_num) (by norm_num))))
  set a : E := ∑' k, e (fk k) with ha_def
  set σ : F := ∑' k, s (fk k) with hσ_def
  have hσS : σ ∈ S := by
    have hpartial : ∀ m, (∑ k ∈ Finset.range m, s (fk k)) ∈ S :=
      fun m => S.sum_mem (fun k _ => hsS (fk k))
    exact (S.closed_of_finiteDimensional).mem_of_tendsto
      hsum_s.hasSum.tendsto_sum_nat (Filter.Eventually.of_forall hpartial)
  have htel : ∀ m : ℕ,
      (∑ k ∈ Finset.range m, ((u (e (fk k)) - v (e (fk k))) + s (fk k))) = f₀ - fk m := by
    intro m
    induction m with
    | zero => simp [hfk_def]
    | succ m IH =>
      rw [Finset.sum_range_succ, IH, hfk_succ]
      change (f₀ - fk m) + ((u (e (fk m)) - v (e (fk m))) + s (fk m)) =
        f₀ - (fk m - ((u (e (fk m)) - v (e (fk m))) + s (fk m)))
      abel
  have hL1 : Filter.Tendsto
      (fun m => ∑ k ∈ Finset.range m, ((u (e (fk k)) - v (e (fk k))) + s (fk k)))
      Filter.atTop (nhds ((u a - v a) + σ)) := by
    have heq : ∀ m, (∑ k ∈ Finset.range m, ((u (e (fk k)) - v (e (fk k))) + s (fk k))) =
        (u (∑ k ∈ Finset.range m, e (fk k)) - v (∑ k ∈ Finset.range m, e (fk k))) +
          ∑ k ∈ Finset.range m, s (fk k) := by
      intro m
      rw [map_sum, map_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    simp only [heq]
    have h1 : Filter.Tendsto (fun m => ∑ k ∈ Finset.range m, e (fk k)) Filter.atTop (nhds a) :=
      hsum_e.hasSum.tendsto_sum_nat
    have h2 : Filter.Tendsto (fun m => u (∑ k ∈ Finset.range m, e (fk k))) Filter.atTop
        (nhds (u a)) :=
      (u.continuous.tendsto _).comp h1
    have h3 : Filter.Tendsto (fun m => v (∑ k ∈ Finset.range m, e (fk k))) Filter.atTop
        (nhds (v a)) :=
      (v.continuous.tendsto _).comp h1
    have h4 : Filter.Tendsto (fun m => ∑ k ∈ Finset.range m, s (fk k)) Filter.atTop (nhds σ) :=
      hsum_s.hasSum.tendsto_sum_nat
    exact (h2.sub h3).add h4
  have hL2 : Filter.Tendsto (fun m => f₀ - fk m) Filter.atTop (nhds (f₀ - 0)) := by
    refine Filter.Tendsto.const_sub f₀ ?_
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) hdecay ?_
    have : Filter.Tendsto (fun k : ℕ => (2⁻¹ : ℝ) ^ k) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simpa using this.mul_const ‖f₀‖
  have hlim := Filter.Tendsto.congr (fun m => (htel m)) hL1
  rw [sub_zero] at hL2
  have heq : (u a - v a) + σ = f₀ := tendsto_nhds_unique hlim hL2
  refine ⟨a, ?_⟩
  have hfin : f₀ - (u a - v a) = σ := by rw [← heq]; abel
  exact hfin ▸ hσS

/-- Consumer form: any linear target `P` that is (a) killed by `u − v` and (b) hit by all of
`F`, is finite-dimensional — the direct Schwartz-consumer shape needed for `H1Cover`. -/
theorem finiteDimensional_of_cospan {E F P : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    [AddCommGroup P] [Module ℂ P] (u v : E →L[ℂ] F) (hu : Function.Surjective u)
    (hv : IsCompactOperator v) (χ : F →ₗ[ℂ] P) (hker : ∀ e, χ (u e - v e) = 0)
    (hχ : Function.Surjective χ) : FiniteDimensional ℂ P := by
  obtain ⟨S, hSfd, hspan⟩ := schwartz_finite_cospan u v hu hv
  have htop : (⊤ : Submodule ℂ P) ≤ Submodule.map χ S := by
    intro p _
    obtain ⟨f, hf⟩ := hχ p
    obtain ⟨e, he⟩ := hspan f
    refine ⟨f - (u e - v e), he, ?_⟩
    rw [map_sub, hker e, sub_zero, hf]
  have htop' : Submodule.map χ S = ⊤ := top_le_iff.mp htop
  have : Module.Finite ℂ (Submodule.map χ S) := Module.Finite.map S χ
  have : Module.Finite ℂ (⊤ : Submodule ℂ P) := htop' ▸ this
  exact Module.Finite.equiv (Submodule.topEquiv (R := ℂ) (M := P))

/-- The extension helper: a linear map with finite-dimensional kernel and finite-dimensional
codomain has finite-dimensional domain (used by both all-`D` finiteness steps and the χ
ledger's `finiteDimensional_linSys`). -/
theorem FiniteDimensional.of_linearMap_ker_range {M N : Type*} [AddCommGroup M] [Module ℂ M]
    [AddCommGroup N] [Module ℂ N] (f : M →ₗ[ℂ] N) [FiniteDimensional ℂ (LinearMap.ker f)]
    [FiniteDimensional ℂ N] : FiniteDimensional ℂ M := by
  have : Module.Finite ℂ (M ⧸ LinearMap.ker f) :=
    Module.Finite.equiv f.quotKerEquivRange.symm
  exact Module.Finite.of_submodule_quotient (LinearMap.ker f)

end RS
