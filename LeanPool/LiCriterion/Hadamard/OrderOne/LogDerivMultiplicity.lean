/-
Copyright (c) 2026 Nicholas Bulka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Bulka
-/

import Mathlib.Topology.Algebra.InfiniteSum.Real
import LeanPool.LiCriterion.Hadamard.OrderOne.LogDeriv

/-!
Multiplicity-aware log-derivative formulas for genus‑1 canonical products.

We model multiplicity by repeating each zero index `i` exactly `m i` times via the sigma type
`Σ i, Fin (m i)`. This keeps the analytic infrastructure unchanged, and the resulting
log-derivative series carries the expected multiplicity coefficient.
-/

open Complex Filter
open scoped BigOperators

namespace Hadamard
namespace OrderOne

/-- Duplicate each index `i` exactly `m i` times. -/
abbrev WithMultiplicity (ι : Type) (m : ι → ℕ) : Type := Σ i : ι, Fin (m i)

-- The multiplicity-aware sigma summability proof is one of the expensive
-- reindexing steps in this file.
private lemma summable_inv_norm_sq_withMultiplicity_of_summable_mul_inv_norm_sq
    {ι : Type} {z : ι → ℂ} {m : ι → ℕ}
    (h : Summable (fun i : ι => (m i : ℝ) / ‖z i‖ ^ 2))
    : Summable (fun j : WithMultiplicity ι m => (1 : ℝ) / ‖z j.1‖ ^ 2) := by
  classical
  have hnonneg :
      ∀ j : WithMultiplicity ι m, 0 ≤ (1 : ℝ) / ‖z j.1‖ ^ 2 := by
    intro j
    positivity
  refine
    (summable_sigma_of_nonneg
      (f := fun j : WithMultiplicity ι m => (1 : ℝ) / ‖z j.1‖ ^ 2) hnonneg).2 ?_
  refine ⟨?_, ?_⟩
  · intro i
    exact (hasSum_fintype (fun _ : Fin (m i) => (1 : ℝ) / ‖z i‖ ^ 2)).summable
  · have hrewrite :
        (fun i : ι => ∑' _ : Fin (m i), (1 : ℝ) / ‖z i‖ ^ 2) =
          (fun i : ι => (m i : ℝ) / ‖z i‖ ^ 2) := by
      funext i
      calc
        (∑' _ : Fin (m i), (1 : ℝ) / ‖z i‖ ^ 2) =
            (m i : ℝ) * ((1 : ℝ) / ‖z i‖ ^ 2) := by
              simp [tsum_fintype, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
        _ = (m i : ℝ) / ‖z i‖ ^ 2 := by simp [div_eq_mul_inv]
    simpa [hrewrite, div_eq_mul_inv] using h

-- The `tsum_sigma'` reindexing is the remaining heartbeat hotspot.
private lemma tsum_withMultiplicity_eq_tsum_sigma
    {ι : Type} {z : ι → ℂ} {m : ι → ℕ} {x : ℂ}
    (hsumR : Summable (fun j : WithMultiplicity ι m => x / (z j.1 * (x - z j.1)))) :
    (∑' j : WithMultiplicity ι m, x / (z j.1 * (x - z j.1))) =
      ∑' i : ι, ∑' _ : Fin (m i), x / (z i * (x - z i)) := by
  simpa [WithMultiplicity] using
    (hsumR.tsum_sigma'
      (fun i =>
        (hasSum_fintype (fun _ : Fin (m i) => x / (z i * (x - z i)))).summable))

private lemma tsum_fintype_eq_mul_tsum_term
    {ι : Type} {z : ι → ℂ} {m : ι → ℕ} {x : ℂ} :
    (fun i : ι => (∑' _ : Fin (m i), x / (z i * (x - z i)))) =
      (fun i : ι => (m i : ℂ) * (x / (z i * (x - z i)))) := by
  funext i
  simp [tsum_fintype, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]

theorem logDeriv_tprod_weierstrass_E_one_eq_tsum_of_summable_mul_inv_norm_sq
    {ι : Type} {z : ι → ℂ} {m : ι → ℕ}
    (hz0 : ∀ i, z i ≠ 0)
    (h : Summable (fun i : ι => (m i : ℝ) / ‖z i‖ ^ 2))
    (x : ℂ) (hx : ∀ i, x ≠ z i) :
    logDeriv
        (fun w : ℂ => ∏' j : WithMultiplicity ι m, weierstrassE 1 (w / z j.1)) x =
      ∑' i : ι, (m i : ℂ) * (x / (z i * (x - z i))) := by
  classical
  have hz0' : ∀ j : WithMultiplicity ι m, z j.1 ≠ 0 := by
    intro j
    exact hz0 j.1
  have h' : Summable (fun j : WithMultiplicity ι m => (1 : ℝ) / ‖z j.1‖ ^ 2) :=
    summable_inv_norm_sq_withMultiplicity_of_summable_mul_inv_norm_sq (z := z) (m := m) h
  have hx' : ∀ j : WithMultiplicity ι m, x ≠ z j.1 := by
    intro j
    exact hx j.1
  have hlog :
      logDeriv (fun w : ℂ => ∏' j : WithMultiplicity ι m, weierstrassE 1 (w / z j.1)) x =
        ∑' j : WithMultiplicity ι m, x / (z j.1 * (x - z j.1)) :=
    logDeriv_tprod_weierstrass_E_one_eq_tsum_of_summable_inv_norm_sq
      (z := fun j : WithMultiplicity ι m => z j.1) hz0' h' x hx'
  have hsumR : Summable (fun j : WithMultiplicity ι m => x / (z j.1 * (x - z j.1))) := by
    have hsum_log :
        Summable (fun j : WithMultiplicity ι m =>
          logDeriv (fun w : ℂ => weierstrassE 1 (w / z j.1)) x) := by
      simpa using
        summable_logDeriv_weierstrass_E_one_div_of_summable_inv_norm_sq
          (z := fun j : WithMultiplicity ι m => z j.1) hz0' h' x hx'
    have hterm :
        (fun j : WithMultiplicity ι m =>
            logDeriv (fun w : ℂ => weierstrassE 1 (w / z j.1)) x) =
          (fun j : WithMultiplicity ι m => x / (z j.1 * (x - z j.1))) := by
      funext j
      simpa using logDeriv_weierstrass_E_one_div (a := z j.1) (x := x) (hz0 j.1) (hx j.1)
    simpa [hterm] using hsum_log
  have hSigma :=
    tsum_withMultiplicity_eq_tsum_sigma (z := z) (m := m) (x := x) hsumR
  have hInner := tsum_fintype_eq_mul_tsum_term (z := z) (m := m) (x := x)
  calc
    logDeriv (fun w : ℂ => ∏' j : WithMultiplicity ι m, weierstrassE 1 (w / z j.1)) x
        = ∑' j : WithMultiplicity ι m, x / (z j.1 * (x - z j.1)) := hlog
    _ = ∑' i : ι, ∑' _ : Fin (m i), x / (z i * (x - z i)) := hSigma
    _ = ∑' i : ι, (m i : ℂ) * (x / (z i * (x - z i))) := by
          simp only [hInner]

end OrderOne
end Hadamard
