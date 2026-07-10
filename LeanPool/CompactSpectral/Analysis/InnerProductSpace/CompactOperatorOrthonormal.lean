/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Cofinite
import LeanPool.CompactSpectral.Analysis.InnerProductSpace.RayleighCompact

/-!
# Compact operators on orthonormal sequences

In a (real or complex) Hilbert space, an orthonormal sequence converges to `0` in the weak
topology. As a corollary, a compact operator sends orthonormal sequences to norm-null sequences.

These lemmas are useful for iterating the Rayleigh-quotient eigenvector construction toward
compact self-adjoint spectral theory (and later, compact-resolvent arguments for unbounded
operators such as Laplace–Beltrami).

## Main results

- `CompactSpectral.tendsto_zero_weakSpace_of_orthonormal`
- `CompactSpectral.tendsto_zero_apply_of_isCompactOperator_of_orthonormal`
- `CompactSpectral.tendsto_norm_apply_of_isCompactOperator_of_orthonormal`
-/

namespace CompactSpectral

open Filter Topology Metric
open scoped Topology

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

private lemma injective_topDualPairing_flip : Function.Injective (topDualPairing 𝕜 E).flip := by
  intro x y hxy
  have h0 :
      (InnerProductSpace.toDual 𝕜 E (x - y)) x = (InnerProductSpace.toDual 𝕜 E (x - y)) y := by
    have :=
      congrArg (fun f : (E →L[𝕜] 𝕜) →ₗ[𝕜] 𝕜 => f (InnerProductSpace.toDual 𝕜 E (x - y))) hxy
    simpa [topDualPairing_apply] using this
  have hinner := h0
  rw [InnerProductSpace.toDual_apply_apply] at hinner
  rw [InnerProductSpace.toDual_apply_apply] at hinner
  have hdiff : inner 𝕜 (x - y) x - inner 𝕜 (x - y) y = 0 := by
    simp [hinner]
  have hself : inner 𝕜 (x - y) (x - y) = 0 := by
    have h :
        inner 𝕜 (x - y) (x - y) = inner 𝕜 (x - y) x - inner 𝕜 (x - y) y := by
      simpa using (inner_sub_right (𝕜 := 𝕜) (x := x - y) (y := x) (z := y))
    simp_all
  have : x - y = 0 := (inner_self_eq_zero).1 hself
  exact sub_eq_zero.mp this

/-- An orthonormal sequence converges to `0` in the weak topology (`WeakSpace`). -/
lemma tendsto_zero_weakSpace_of_orthonormal {e : ℕ → E} (he : Orthonormal 𝕜 e) :
    Tendsto (let ew : ℕ → WeakSpace 𝕜 E := fun n => e n; ew) atTop (𝓝 (0 : WeakSpace 𝕜 E)) := by
  let ew : ℕ → WeakSpace 𝕜 E := fun n => e n
  change Tendsto ew atTop (𝓝 (0 : WeakSpace 𝕜 E))
  have hinj : Function.Injective (topDualPairing 𝕜 E).flip :=
    injective_topDualPairing_flip (𝕜 := 𝕜) (E := E)
  have hiff :=
    (WeakBilin.tendsto_iff_forall_eval_tendsto (B := (topDualPairing 𝕜 E).flip) (f := ew)
      (x := (0 : WeakSpace 𝕜 E)) (l := atTop) hinj)
  refine hiff.2 ?_
  intro l
  let y : E := (InnerProductSpace.toDual 𝕜 E).symm (l : StrongDual 𝕜 E)
  have hl : ∀ x : E, l x = inner 𝕜 y x := by
    intro x
    -- Riesz representation: evaluation by `l` is inner product with the representing vector.
    exact (InnerProductSpace.toDual_symm_apply (𝕜 := 𝕜) (x := x) (y := l)).symm
  have hsq : Tendsto (fun n => ‖inner 𝕜 (e n) y‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    have hsum : Summable (fun n => ‖inner 𝕜 (e n) y‖ ^ 2) :=
      he.inner_products_summable y
    have hcof : Tendsto (fun n => ‖inner 𝕜 (e n) y‖ ^ 2) cofinite (𝓝 (0 : ℝ)) :=
      hsum.tendsto_cofinite_zero
    simpa [Nat.cofinite_eq_atTop] using hcof
  have hsqrt :
      Tendsto (fun n => Real.sqrt (‖inner 𝕜 (e n) y‖ ^ 2)) atTop (𝓝 (Real.sqrt (0 : ℝ))) :=
    (Real.continuous_sqrt.tendsto 0).comp hsq
  have hsimp : (fun n => Real.sqrt (‖inner 𝕜 (e n) y‖ ^ 2)) = fun n => ‖inner 𝕜 (e n) y‖ := by
    simp_all
  have hnorm' : Tendsto (fun n => ‖inner 𝕜 (e n) y‖) atTop (𝓝 (0 : ℝ)) := by
    simpa [hsimp, Real.sqrt_zero] using hsqrt
  have hnorm : Tendsto (fun n => ‖inner 𝕜 y (e n)‖) atTop (𝓝 (0 : ℝ)) := by
    have hsymm : (fun n => ‖inner 𝕜 y (e n)‖) = fun n => ‖inner 𝕜 (e n) y‖ := by
      funext n
      simpa using (norm_inner_symm (𝕜 := 𝕜) (x := y) (y := e n))
    simpa [hsymm] using hnorm'
  have hinner : Tendsto (fun n => inner 𝕜 y (e n)) atTop (𝓝 (0 : 𝕜)) :=
    (tendsto_zero_iff_norm_tendsto_zero).2 hnorm
  have : Tendsto (fun n => l (e n)) atTop (𝓝 (0 : 𝕜)) := by
    simpa [hl] using hinner
  have h0 : ((topDualPairing 𝕜 E).flip (0 : WeakSpace 𝕜 E)) l = 0 := by
    simp only [LinearMap.flip_apply, topDualPairing_apply]
    exact map_zero l
  simpa [ew, topDualPairing_apply, h0] using this

/-- A compact operator sends an orthonormal sequence to a strongly-null sequence. -/
lemma tendsto_zero_apply_of_isCompactOperator_of_orthonormal (T : E →L[𝕜] E)
    (hTc : IsCompactOperator (T : E → E)) {e : ℕ → E} (he : Orthonormal 𝕜 e) :
    Tendsto (fun n => T (e n)) atTop (𝓝 (0 : E)) := by
  let ew : ℕ → WeakSpace 𝕜 E := fun n => e n
  have hx_ball :
      ∀ᶠ n in atTop, ew n ∈ weakClosedBall (𝕜 := 𝕜) (E := E) (1 : ℝ) :=
    Filter.Eventually.of_forall fun n => by
      have hn : ‖e n‖ = (1 : ℝ) := by
        simpa [Orthonormal] using he.1 n
      change (e n : E) ∈ Metric.closedBall (α := E) (0 : E) (1 : ℝ)
      simp_all
  have hweak : Tendsto ew atTop (𝓝 (0 : WeakSpace 𝕜 E)) := by
    simpa [ew] using tendsto_zero_weakSpace_of_orthonormal (𝕜 := 𝕜) (E := E) he
  have hT :
      Tendsto (fun n => T (ew n : E)) atTop
        (𝓝 (T ((0 : WeakSpace 𝕜 E) : E))) :=
    CompactSelfAdjoint.tendsto_apply_of_isCompactOperator (𝕜 := 𝕜) (E := E) T hTc
      (r := (1 : ℝ)) hx_ball hweak
  rw [show (T : E → E) ((0 : WeakSpace 𝕜 E) : E) = 0 from T.map_zero] at hT
  simpa [ew] using hT

/-- A compact operator sends an orthonormal sequence to a norm-null sequence. -/
lemma tendsto_norm_apply_of_isCompactOperator_of_orthonormal (T : E →L[𝕜] E)
    (hTc : IsCompactOperator (T : E → E)) {e : ℕ → E} (he : Orthonormal 𝕜 e) :
    Tendsto (fun n => ‖T (e n)‖) atTop (𝓝 (0 : ℝ)) := by
  have hT : Tendsto (fun n => T (e n)) atTop (𝓝 (0 : E)) :=
    tendsto_zero_apply_of_isCompactOperator_of_orthonormal (𝕜 := 𝕜) (E := E) T hTc he
  simpa using hT.norm

end CompactSpectral
