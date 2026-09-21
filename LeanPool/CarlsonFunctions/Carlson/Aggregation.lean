/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.CarlsonFunctions.Dirichlet.Average.Aggregation
public import LeanPool.CarlsonFunctions.Carlson.R.Continuation
public import LeanPool.CarlsonFunctions.Carlson.S

/-!
# Equal-node aggregation for Carlson functions

These specializations of the general continuation theorem impose no restrictions
on the Dirichlet parameters. The `R` function retains its right-half-plane node
domain; the polynomial and `S` statements allow arbitrary complex nodes.
-/

open Complex Set
open scoped Classical
@[expose] public noncomputable section
namespace DirichletTransform
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Equal-node aggregation for the entire regularized `R` function. -/
theorem regCarlsonRContinued_aggregate {q : ι → κ} (hq : Function.Surjective q)
    (t : ℂ) {z : κ → ℂ} (hz : z ∈ carlsonRVariableDomain) (b : ι → ℂ) :
    regCarlsonRContinued t (z ∘ q) (fun i => hz (q i)) b =
      regCarlsonRContinued t z hz (stdSimplexAggregate q b) := by
  exact IsRegCarlsonContinuation.aggregate hq
    (isRegCarlsonRContinuation_continued t (fun i => hz (q i)))
    (isRegCarlsonRContinuation_continued t hz)
    ((continuous_carlsonAffineForm z).continuousOn.cpow_const
      (fun _ hu => carlsonAffineForm_mem_slitPlane hz hu)) b

/-- Equal-node aggregation for regularized `R` polynomials at every complex parameter. -/
theorem regCarlsonR_aggregate {q : ι → κ} (hq : Function.Surjective q)
    (n : ℕ) (z : κ → ℂ) (b : ι → ℂ) :
    regCarlsonR n (z ∘ q) b = regCarlsonR n z (stdSimplexAggregate q b) := by
  have h (w : ι → ℂ) : IsRegCarlsonContinuation (fun x => x ^ n) w (regCarlsonR n w) :=
    ⟨analyticOnNhd_regCarlsonR n w, fun _ hb => (regCarlsonDirichletAverage_pow n w hb).symm⟩
  have h' : IsRegCarlsonContinuation (fun x => x ^ n) z (regCarlsonR n z) :=
    ⟨analyticOnNhd_regCarlsonR n z, fun _ hb => (regCarlsonDirichletAverage_pow n z hb).symm⟩
  exact (h (z ∘ q)).aggregate hq h'
    ((continuous_carlsonAffineForm z).pow n).continuousOn b

/-- Equal-node aggregation for the entire regularized `S` function. -/
theorem regCarlsonSSeries_aggregate {q : ι → κ} (hq : Function.Surjective q)
    (z : κ → ℂ) (b : ι → ℂ) :
    regCarlsonSSeries (z ∘ q) b = regCarlsonSSeries z (stdSimplexAggregate q b) := by
  exact IsRegCarlsonContinuation.aggregate hq
    (isRegCarlsonSContinuation_series (z ∘ q)) (isRegCarlsonSContinuation_series z)
    (Complex.continuous_exp.comp (continuous_carlsonAffineForm z)).continuousOn b

end DirichletTransform
end
