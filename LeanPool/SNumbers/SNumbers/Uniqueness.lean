/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.SNumbers.SNumbers.Approximation
public import LeanPool.SNumbers.BasicResults.SVD

/-!
# Uniqueness of `s`-numbers on Hilbert spaces (Pietsch 2.11.9)

On a pair of Hilbert spaces, **every** `s`-number sequence coincides with
the approximation numbers:

```
s S n = aₙ(S)    for every s-number sequence s and every S : H₁ →L[𝕜] H₂.
```

The upper bound `sₙ(S) ≤ aₙ(S)` holds on any Banach space and is proved in
`SNumbers.Approximation` (`sn_le_approximationNumber`). The reverse bound
`aₙ(S) ≤ sₙ(S)` is the Hilbert-space input and is where the singular value
decomposition enters.

This file is **Hilbert-space only**; the general-space comparison results
(`hₙ ≤ sₙ` and Pietsch's sandwich) that build on it live in
`SNumbers.Inequalities`.

## Proof of the lower bound

Fix a real `c` with `0 ≤ c < aₙ(S)`. The SVD provides
(`SVD.exists_scalar_factorisation`) contractions
`A : ℓ₂ⁿ⁺¹ →L[𝕜] H₁`, `B : H₂ →L[𝕜] ℓ₂ⁿ⁺¹` with

```
B ∘ S ∘ A = c • id_{ℓ₂ⁿ⁺¹}.
```

Then:

* (S5) normalisation gives `sₙ(id_{ℓ₂ⁿ⁺¹}) = 1`, and reverse homogeneity
  (`norm_smul_le_sn`) gives `c = c · sₙ(id) ≤ sₙ(c • id) = sₙ(B ∘ S ∘ A)`.
* (S3) gives `sₙ(B ∘ S ∘ A) ≤ ‖B‖ · sₙ(S) · ‖A‖ ≤ sₙ(S)` since
  `‖A‖, ‖B‖ ≤ 1`.

Hence `c ≤ sₙ(S)` for every `c < aₙ(S)`, so `aₙ(S) ≤ sₙ(S)`.

## Input

The one ingredient from outside is `SVD.exists_scalar_factorisation` (the scalar
factorisation `B ∘ S ∘ A = c • id` for `c < aₙ(S)`), whose own spectral-theory
input is `SpectralRepresentation.exists_spectral_projection`.

## Main results

* `SNumbers.le_sn_of_lt_approximationNumber` — `c ≤ sₙ(S)` for `c < aₙ(S)`.
* `SNumbers.approximationNumber_le_sn` — the lower bound `aₙ(S) ≤ sₙ(S)`.
* `SNumbers.allSNumbers_eq_on_HilbertSpace` — the coincidence
  `sₙ(S) = aₙ(S)`.
-/

@[expose] public section

universe u

open scoped Cardinal
open ContinuousLinearMap

namespace SNumbers

variable {𝕜 : Type u} [RCLike 𝕜]
variable {H₁ H₂ : Type u}
variable [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁] [CompleteSpace H₁]
variable [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂] [CompleteSpace H₂]

/-- For every real `c` with `0 ≤ c < aₙ(S)`, every `s`-number sequence
satisfies `c ≤ sₙ(S)`. This is the core of the Hilbert-space lower bound;
it consumes the SVD factorisation `B ∘ S ∘ A = c • id`. -/
theorem le_sn_of_lt_approximationNumber {s : Family 𝕜} (hs : IsSNumberSequence s)
    (S : H₁ →L[𝕜] H₂) (n : ℕ) {c : ℝ} (hc0 : 0 ≤ c)
    (hca : c < approximationNumber S n) : c ≤ s S n := by
  rcases hc0.eq_or_lt with hc | hcpos
  · -- `c = 0`: immediate from non-negativity (S1).
    rw [← hc]; exact hs.nonneg S n
  · -- `c > 0`: use the SVD factorisation.
    obtain ⟨A, B, hA, hB, hfact⟩ :=
      SVD.exists_scalar_factorisation S n hc0 hca
    have hc_ne : (c : 𝕜) ≠ 0 := by exact_mod_cast hcpos.ne'
    have hnorm : ‖(c : 𝕜)‖ = c := by rw [RCLike.norm_ofReal, abs_of_pos hcpos]
    -- (S5) normalisation on `ℓ₂ⁿ⁺¹`.
    have hid : s (ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1)))) n = 1 :=
      hs.normalised_at_id n
    -- Lower bound on `sₙ(c • id)` via reverse homogeneity.
    have hlow : c ≤ s ((c : 𝕜) •
        ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1)))) n := by
      have h := norm_smul_le_sn hs hc_ne
        (ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1)))) n
      rwa [hnorm, hid, mul_one] at h
    -- Upper bound on `sₙ(B ∘ S ∘ A)` via the (S3) ideal property.
    have hsn : 0 ≤ s S n := hs.nonneg S n
    have hupp : s (B.comp (S.comp A)) n ≤ s S n := by
      have h3 := hs.ideal A S B n
      have hb : ‖B‖ * s S n ≤ s S n := by nlinarith [hsn, hB, norm_nonneg B]
      have hba : ‖B‖ * s S n * ‖A‖ ≤ s S n := by
        nlinarith [hb, hA, mul_nonneg (norm_nonneg B) hsn, norm_nonneg A]
      linarith [h3]
    -- Combine: `c ≤ sₙ(c • id) = sₙ(B ∘ S ∘ A) ≤ sₙ(S)`.
    rw [hfact] at hupp
    linarith [hlow, hupp]

/-- **Lower bound.** On Hilbert spaces, `aₙ(S) ≤ sₙ(S)` for every
`s`-number sequence `s`. -/
theorem approximationNumber_le_sn {s : Family 𝕜} (hs : IsSNumberSequence s)
    (S : H₁ →L[𝕜] H₂) (n : ℕ) :
    approximationNumber S n ≤ s S n := by
  by_contra h
  rw [not_le] at h
  have ht0 : 0 ≤ s S n := hs.nonneg S n
  have ha0 : 0 ≤ approximationNumber S n := approximationNumber_nonneg S n
  have hc0 : 0 ≤ (s S n + approximationNumber S n) / 2 := by linarith
  have hca : (s S n + approximationNumber S n) / 2 < approximationNumber S n := by linarith
  have hkey := le_sn_of_lt_approximationNumber hs S n hc0 hca
  linarith

/-- **Uniqueness theorem (Pietsch 2.11.9).** On Hilbert spaces, every
`s`-number sequence agrees with the approximation numbers:
`sₙ(S) = aₙ(S)`.

The upper bound is `sn_le_approximationNumber` (valid on any Banach space);
the lower bound is `approximationNumber_le_sn` (Hilbert-space SVD). -/
theorem allSNumbers_eq_on_HilbertSpace {s : Family 𝕜} (hs : IsSNumberSequence s)
    (S : H₁ →L[𝕜] H₂) (n : ℕ) :
    s S n = approximationNumber S n :=
  le_antisymm (sn_le_approximationNumber hs S n) (approximationNumber_le_sn hs S n)

end SNumbers

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
