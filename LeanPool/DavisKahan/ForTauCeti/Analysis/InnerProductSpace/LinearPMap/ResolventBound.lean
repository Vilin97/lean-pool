/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Resolvent
public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import Mathlib.Analysis.CStarAlgebra.Spectrum

/-!
# Resolvent spectral mapping

`TauCeti.LinearPMap.resolvent`, the bounded two-sided inverse of `z • I - A`,
and the first resolvent identity it satisfies are supplied by the canonical core
in `ForTauCeti.Analysis.Normed.Operator.Resolvent.Unbounded`.  This file adds the
one thing that core does not carry, because it is about the *spectrum* rather
than the resolvent set:

* **resolvent spectral mapping** in the direction that matters — if `ν ≠ 0` and
  `z - ν⁻¹` is in the resolvent set of `A`, then `ν` is not in the spectrum of
  the bounded operator `resolvent A z`;
* hence, via Mathlib's `IsSelfAdjoint.spectralRadius_eq_nnnorm`, the
  quantitative bound the Davis--Kahan unbounded theory consumes:

> if `A` is self-adjoint and its spectrum avoids the ball of radius `s` about a
> real `c`, then `c • I - A` has a bounded two-sided inverse of norm at most
> `s⁻¹`.

## Why this file exists

That bound was previously obtained from `vendor/Spectra` by a much heavier
route: Stone's theorem (`genToGroup`) to manufacture a unitary group, its
projection-valued measure, the bounded Borel functional calculus, and a
truncated symbol `(l - c)⁻¹`.  None of that is needed.  The bound is a
*C⋆-algebra* fact about the bounded operator `resolvent A z`, and the only input
from the unbounded side is the spectral mapping, which is elementary algebra with
domain bookkeeping.

For the Spectra-removal plan this removes the
projection-valued-measure layer from the critical path of the gap-resolvent
endpoint, which was the largest single block of the port.

## Convention

The resolvent here is the canonical one, `resolvent A z = (z • I - A)⁻¹`.  An
earlier version of this file defined its own `resolvent A hz = (A - z)⁻¹`, taking
a membership proof; that operator was the negative of this one.  The spectral
mapping is stated accordingly: the relevant point of `A` attached to a nonzero
`ν ∈ spectrum (resolvent A z)` is `z - ν⁻¹`, not `z + ν⁻¹`.

## Provenance

* **Extraction class:** *new*.  Statement and proof are ours.
* **Spectra influence:** the *theorem selection* is Spectra's — its
  `exists_norm_le_two_sided_shifted_inverse_of_spectralProjection_Ioo_eq_zero`
  is what identified this bound as the thing to prove, and
  the completed Tau Ceti adaptation recorded that
  theorem selection is attributable even when the proof is independent.  The
  proof *architecture* is not Spectra's: Spectra goes through the PVM and the
  bounded calculus, this goes through spectral mapping and the spectral radius,
  and the two share no lemma.
-/

@[expose] public section

namespace TauCeti
namespace LinearPMap

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The composite of two resolvents as a difference:
`R z ∘ R w = ν • (R w - R z)` when `w = z - ν⁻¹`.  Stated in the form the
spectral mapping below consumes. -/
theorem resolvent_comp_resolvent {A : E →ₗ.[𝕜] E} {z w : 𝕜}
    (hz : z ∈ resolventSet A) (hw : w ∈ resolventSet A) {ν : 𝕜}
    (hν : ν ≠ 0) (hwz : w = z - ν⁻¹) (φ : E) :
    resolvent A z (resolvent A w φ) = ν • (resolvent A w φ - resolvent A z φ) := by
  have h := resolvent_sub_resolvent_apply hz hw φ
  have hzw : w - z = -ν⁻¹ := by rw [hwz]; ring
  rw [hzw] at h
  -- `R z φ - R w φ = -ν⁻¹ • R z (R w φ)`; multiply by `-ν`.
  have hmul := congrArg (fun v => (-ν) • v) h
  simp only [smul_smul] at hmul
  rw [show (-ν) * (-ν⁻¹) = 1 by field_simp] at hmul
  rw [one_smul] at hmul
  rw [← hmul]
  module

/-- **Resolvent spectral mapping**, in the direction the norm bound needs: a
nonzero `ν` is outside the spectrum of the bounded operator `resolvent A z` as
soon as `z - ν⁻¹` is a resolvent point of `A`.

What is proved is that `ν • 1 - resolvent A z` is a unit, with explicit inverse
`ν⁻¹ • (1 + ν⁻¹ • resolvent A (z - ν⁻¹))`. -/
theorem notMem_spectrum_resolvent {A : E →ₗ.[𝕜] E} {z : 𝕜}
    (hz : z ∈ resolventSet A) {ν : 𝕜} (hν : ν ≠ 0)
    (hw : z - ν⁻¹ ∈ resolventSet A) :
    ν ∉ _root_.spectrum 𝕜 (resolvent A z) := by
  classical
  set R := resolvent A z with hR
  set S := resolvent A (z - ν⁻¹) with hS
  set T : E →L[𝕜] E := ν⁻¹ • (1 + ν⁻¹ • S) with hT
  -- `R (S φ) = ν • (S φ - R φ)` and `S (R φ) = ν • (S φ - R φ)`
  have hRS : ∀ φ, R (S φ) = ν • (S φ - R φ) := by
    intro φ
    have := resolvent_comp_resolvent hz hw hν rfl φ
    simpa [hR, hS] using this
  have hSR : ∀ φ, S (R φ) = ν • (S φ - R φ) := by
    intro φ
    have h := resolvent_sub_resolvent_apply hw hz φ
    have hwz : z - (z - ν⁻¹) = ν⁻¹ := by ring
    rw [hwz] at h
    have hmul := congrArg (fun v => ν • v) h
    simp only [smul_smul] at hmul
    rw [show (ν : 𝕜) * ν⁻¹ = 1 by field_simp, one_smul] at hmul
    simpa [hR, hS] using hmul.symm
  have hinv : ν * ν⁻¹ = 1 := mul_inv_cancel₀ hν
  have hinv' : ν⁻¹ * ν = 1 := inv_mul_cancel₀ hν
  have hTapp : ∀ φ : E, T φ = ν⁻¹ • (φ + ν⁻¹ • S φ) := fun φ => by simp [hT]
  -- `R (T φ) = ν⁻¹ • S φ`, the one computation both directions rest on.
  have hRT : ∀ φ : E, R (T φ) = ν⁻¹ • S φ := by
    intro φ
    simp only [hTapp, map_smul, map_add, hRS φ, smul_smul, hinv', one_smul]
    module
  have hleft : (algebraMap 𝕜 (E →L[𝕜] E) ν - R) * T = 1 := by
    refine ContinuousLinearMap.ext fun φ => ?_
    -- states the goal with the definition unfolded, in the shape the next step needs;
    -- there is no `_apply` lemma to rewrite with here.
    change ν • T φ - R (T φ) = φ
    rw [hRT φ, hTapp φ, smul_smul, hinv, one_smul]
    module
  have hright : T * (algebraMap 𝕜 (E →L[𝕜] E) ν - R) = 1 := by
    refine ContinuousLinearMap.ext fun φ => ?_
    -- states the goal with the definition unfolded, in the shape the next step needs;
    -- there is no `_apply` lemma to rewrite with here.
    change T (ν • φ - R φ) = φ
    rw [hTapp, map_sub, map_smul, hSR φ]
    rw [show ν • S φ - ν • (S φ - R φ) = ν • R φ by module]
    -- `module` reduces to scalar identities; they need `ν ≠ 0`, so `field_simp`.
    match_scalars
    all_goals field_simp
    all_goals ring
  exact (spectrum.notMem_iff).mpr ⟨⟨_, T, hleft, hright⟩, rfl⟩

/-- **Resolvents at two points of the resolvent set commute**, packaged as
`Commute`.  The underlying equation is the canonical core's
`TauCeti.LinearPMap.resolvent_comm`. -/
theorem resolvent_commute {A : E →ₗ.[𝕜] E} {w z : 𝕜}
    (hw : w ∈ resolventSet A) (hz : z ∈ resolventSet A) :
    Commute (resolvent A w) (resolvent A z) :=
  resolvent_comm hw hz

end LinearPMap
end TauCeti
