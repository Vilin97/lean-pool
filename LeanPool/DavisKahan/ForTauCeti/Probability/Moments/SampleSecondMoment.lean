/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 4.8
-/

/-
Staged for Tau Ceti, roadmap topic T20.  Mathlib is not the destination
(`ForTauCeti/README.md`); what follows is where this material would have gone on
the closed Mathlib track —
uncentered sample second-moment eigenvalue concentration.

Specializes the generic random-Hermitian eigenvalue-concentration engine
(`MatrixConcentration.lean`) to the uncentered second moment
`M̂_{kl}(ω) = n⁻¹ Σᵢ Vᵢ(ω)ₖ Vᵢ(ω)ₗ` of iid random vectors, via the scalar
sample-mean second-moment identity applied to the coordinate products.

Formalized by Claude Opus 4.8 (claude-opus-4-8[1m]).
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Probability.Moments.MatrixConcentration
public import LeanPool.DavisKahan.ForTauCeti.Probability.Moments.SampleMean

/-!
# The uncentered empirical second moment

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `ForMathlib.Probability.Moments.SampleCovariance`, moved to
  `ForTauCeti` in the Wave-1 staging migration; introduced at Davis--Kahan
  commit `f9309f7`.
* Original declarations: `sampleCovariance`, `integral_sq_sampleCovariance_entry_le`,
  `isHermitian_sampleCovariance`, and the capstone eigenvalue bound.  They are spelled
  `sampleSecondMoment...` here: the definition subtracts no sample mean, so the original
  name asserted a centering the mathematics does not perform.  Statements and proofs are
  unaffected, and no alias for the original spelling is kept.
* Extraction class: **moved**.  The Wave-1 migration renamed the namespace
  `ForMathlib` to `TauCeti`, leaving statements and proofs unchanged.
* Original authors / copyright: Jon Crall, Claude Opus 4.8; Copyright (c) 2026 Kitware, Inc.;
  Apache 2.0.
* Spectra influence: **none** — this module imports only Mathlib and sibling
  `ForTauCeti` staging modules.
-/

@[expose] public section


open scoped Matrix ENNReal
open MeasureTheory ProbabilityTheory

namespace TauCeti

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The **uncentered empirical second moment** of the vectors `V₀, …, V_{n-1}` at outcome
`ω`: `M̂_{kl}(ω) = n⁻¹ Σᵢ Vᵢ(ω)ₖ Vᵢ(ω)ₗ`.

No sample mean is subtracted, so this is a second-moment matrix and **not** a covariance:
the two agree only when the coordinates are centered.  The name records that.

The centered analogue in this directory is `TauCeti.centeredScatter`
(`ForTauCeti/Probability/Moments/CenteredScatter.lean`), the *unnormalized* operator
`∑ i, (zᵢ - mean z) ⊗ (zᵢ - mean z)`.  It is centered but not averaged, so it is not a
covariance either.  "Covariance" is reserved for a centered *and* normalized definition,
which this directory does not currently provide. -/
noncomputable def sampleSecondMoment {n d : ℕ}
    (V : Fin n → Ω → EuclideanSpace ℝ (Fin d)) (ω : Ω) : Matrix (Fin d) (Fin d) ℝ :=
  fun k l => (n : ℝ)⁻¹ * ∑ i, V i ω k * V i ω l

/-- **Per-entry second-moment bound for the sample second moment.**  Applying the
scalar sample-mean second-moment identity to the coordinate products
`Yᵢ = Vᵢ(·)ₖ Vᵢ(·)ₗ`, the `(k,l)` entry of `M̂ − M` has mean-square `≤ v / n`, where
`M` is the population second moment `M_{kl} = 𝔼[V(k) V(l)]`. -/
theorem integral_sq_sampleSecondMoment_entry_le {n d : ℕ} (hn : 0 < n)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (V : Fin n → Ω → EuclideanSpace ℝ (Fin d))
    (populationSecondMoment : Matrix (Fin d) (Fin d) ℝ) (k l : Fin d)
    (hL2 : ∀ i, MemLp (fun ω => V i ω k * V i ω l) 2 P)
    (hmean : ∀ i, ∫ ω, V i ω k * V i ω l ∂P = populationSecondMoment k l)
    (hindep : Set.Pairwise (Set.univ : Set (Fin n))
      fun i j => IndepFun (fun ω => V i ω k * V i ω l) (fun ω => V j ω k * V j ω l) P)
    (hident : ∀ i, ∫ ω, ‖V i ω k * V i ω l - populationSecondMoment k l‖ ^ 2 ∂P
        = ∫ ω, ‖V ⟨0, hn⟩ ω k * V ⟨0, hn⟩ ω l - populationSecondMoment k l‖ ^ 2 ∂P)
    {v : ℝ}
    (hv : ∫ ω, ‖V ⟨0, hn⟩ ω k * V ⟨0, hn⟩ ω l - populationSecondMoment k l‖ ^ 2 ∂P ≤ v) :
    ∫ ω, (sampleSecondMoment V ω k l - populationSecondMoment k l) ^ 2 ∂P
      ≤ (n : ℝ)⁻¹ * v := by
  have key := integral_norm_sq_average_sub_of_iid P hn
    (fun i ω => V i ω k * V i ω l) (populationSecondMoment k l) hL2 hmean hindep hident
  have hrw : ∫ ω, (sampleSecondMoment V ω k l - populationSecondMoment k l) ^ 2 ∂P
      = ∫ ω, ‖(n : ℝ)⁻¹ • (∑ i, V i ω k * V i ω l) - populationSecondMoment k l‖ ^ 2 ∂P := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only [sampleSecondMoment, smul_eq_mul, Real.norm_eq_abs, sq_abs]
  rw [hrw, key]
  have hv_nonneg : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
  exact mul_le_mul_of_nonneg_left hv hv_nonneg

omit [MeasurableSpace Ω] in
/-- The uncentered second-moment matrix is symmetric (Hermitian over `ℝ`). -/
theorem isHermitian_sampleSecondMoment {n d : ℕ}
    (V : Fin n → Ω → EuclideanSpace ℝ (Fin d)) (ω : Ω) :
    (sampleSecondMoment V ω).IsHermitian := by
  ext k l
  -- states the conjugate-symmetry goal against `sampleSecondMoment`'s own
  -- entries, which is the form the `star` lemma below rewrites.
  change star (sampleSecondMoment V ω l k) = sampleSecondMoment V ω k l
  simp only [sampleSecondMoment, star_trivial]
  refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
  ring

/-- **Second-moment eigenvalue lower bound (high probability).**  Given a
per-entry mean-square bound `v` for `M̂ − M`, with `M` the population second
moment (e.g. `v = σ²/n` from `integral_sq_sampleSecondMoment_entry_le` under iid
coordinates), with probability `≥ 1 − d² v / η²` every eigenvalue of the
empirical second moment `M̂(ω)` exceeds the corresponding eigenvalue of `M` minus
`d · η`.  Taking `η = c / (2d)` keeps a population eigenvalue floored at `c`
above `c / 2` with high probability — the eigengap the DKPS `halign` route needs. -/
theorem measure_forall_sampleSecondMoment_eigenvalues₀_ge_ge {n d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (V : Fin n → Ω → EuclideanSpace ℝ (Fin d))
    (populationSecondMoment : Matrix (Fin d) (Fin d) ℝ)
    (hPopHermitian : populationSecondMoment.IsHermitian)
    (hVmeas : ∀ i (k : Fin d), Measurable fun ω => V i ω k)
    (hint : ∀ k l, Integrable
      (fun ω => (sampleSecondMoment V ω k l - populationSecondMoment k l) ^ 2) P)
    {v η : ℝ} (hη : 0 < η)
    (hmoment : ∀ k l,
      ∫ ω, (sampleSecondMoment V ω k l - populationSecondMoment k l) ^ 2 ∂P ≤ v) :
    P {ω | ∀ k : Fin (Fintype.card (Fin d)),
        hPopHermitian.eigenvalues₀ k - (d : ℝ) * η ≤
          (isHermitian_sampleSecondMoment V ω).eigenvalues₀ k}
      ≥ 1 - ENNReal.ofReal ((d : ℝ) ^ 2 * v / η ^ 2) := by
  have hmeas : ∀ k l : Fin d, Measurable fun ω => sampleSecondMoment V ω k l := by
    intro k l
    refine Measurable.const_mul ?_ _
    exact Finset.measurable_sum _ fun i _ => (hVmeas i k).mul (hVmeas i l)
  exact measure_forall_eigenvalues₀_ge_ge P (sampleSecondMoment V) populationSecondMoment
    (isHermitian_sampleSecondMoment V) hPopHermitian hmeas hint hη hmoment

end TauCeti
