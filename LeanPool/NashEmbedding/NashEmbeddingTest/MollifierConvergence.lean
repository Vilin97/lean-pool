/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wiygul
-/
module


/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Claude Fable 5 (Anthropic), Claude Opus 4.7 (Anthropic)
  — at the request of David Wiygul
-/
public import LeanPool.NashEmbedding.NashEmbedding.Sobolev.Convolution

/-!
# Sharp `mollifier_convergence` witness tests

Concrete witness checks for `mollifier_convergence` applied to a
momentum-space delta `δ_{m₀}`:
- **W1** — `δ_{m₀} ∈ H^s_*` for every `s`.
- **W2** — On a momentum-space delta, the rescaled-convolution
  distribution is a scalar multiple of `δ_{m₀}` with explicit
  coefficient `ftRn φ (ε • m₀)`.
- **W3** — `mollifier_convergence` invoked on `δ_{m₀}`.
-/

@[expose] public section

open scoped BigOperators
open NashEmbedding.Sobolev MeasureTheory

namespace MollifierConvergenceTests

noncomputable
section

variable {n : ℕ}

/-- The Kronecker-delta distribution `δ_{m₀} ∈ X_n^*`. -/
def singleMode (n : ℕ) (m₀ : Fin n → ℤ) : TrigPolyDual n :=
  seqToDual n (fun m => if m = m₀ then (1 : ℂ) else 0)

/-- **W1** — `singleMode n m₀` lies in `MemSobolevDistrib n s` for every
    `s ∈ ℝ`. The FC sequence has finite support `{m₀}`, so summability
    is trivial. -/
example (s : ℝ) (m₀ : Fin n → ℤ) :
    MemSobolevDistrib n s (singleMode n m₀) := by
  unfold MemSobolevDistrib singleMode
  rw [fourierCoeffDistrib_seqToDual]
  apply summable_of_ne_finset_zero (s := ({m₀} : Finset _))
  intro m hm
  simp at hm
  simp [hm]

/-- **W2** — On a momentum-space delta, the rescaled-convolution
    distribution is a scalar multiple of `δ_{m₀}`:
    `convDistrib (rescale φ ε) δ_{m₀} = ftRn φ (ε • m₀) • δ_{m₀}`.
    Combines Stage 6 test S logic with `ftRn_rescale`. -/
example (φ : (Fin n → ℝ) → ℂ) (hφ : Integrable φ) {ε : ℝ} (hε : 0 < ε)
    (m₀ : Fin n → ℤ) :
    convDistrib n (rescale n φ ε) (singleMode n m₀)
      = (ftRn n φ (ε • fun j => (m₀ j : ℝ))) • singleMode n m₀ := by
  have h_test_s : convDistrib n (rescale n φ ε) (singleMode n m₀)
      = ftRn n (rescale n φ ε) (fun j => (m₀ j : ℝ)) • singleMode n m₀ := by
    unfold convDistrib singleMode
    rw [fourierCoeffDistrib_seqToDual]
    rw [← seqToDual_smul]
    congr 1
    funext m
    by_cases hm : m = m₀
    · simp [hm]
    · simp [hm]
  rw [h_test_s, ftRn_rescale φ hφ hε]

/-- **W3** — `mollifier_convergence` invoked on a momentum-space delta.
    Sobolev-distance from the rescaled-convolution residual to
    `ftRn φ 0 • δ_{m₀}` tends to 0 as `ε → 0⁺`. The substantive content
    of `mollifier_convergence` on this concrete `u`: the convergence
    reduces to continuity of `ftRn φ` at `0`, weighted by
    `weight n s m₀`. -/
example {s : ℝ} (φ : (Fin n → ℝ) → ℂ) (hφ : Integrable φ)
    (m₀ : Fin n → ℤ) :
    Filter.Tendsto
      (fun ε => sobolevNormSqDistrib n s
        (convDistrib n (rescale n φ ε) (singleMode n m₀)
          - ftRn n φ 0 • singleMode n m₀))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds 0) := by
  have hmem : MemSobolevDistrib n s (singleMode n m₀) := by
    unfold MemSobolevDistrib singleMode
    rw [fourierCoeffDistrib_seqToDual]
    apply summable_of_ne_finset_zero (s := ({m₀} : Finset _))
    intro m hm
    simp at hm
    simp [hm]
  exact mollifier_convergence φ hφ hmem

end

end MollifierConvergenceTests
