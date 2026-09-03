/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import LeanPool.ZetaZeros.Hilbert.Defs

/-!
# The zeta-side vocabulary

The zero counts, the pair-correlation apparatus, and the kernel construction of the source's
Section 3.

Every definition that also appears in `Challenge/Basic.lean` is spelled **identically** here. That
is a requirement rather than a courtesy: the comparator compares elaborated types, so a development
and a challenge that spell one notion two ways name two constants, and the pair then verifies
nothing while every other gate stays green.
-/

@[expose] public section

namespace ZetaZeros

open MeasureTheory

/-- The non-trivial zeros of the Riemann zeta function with imaginary part in `(0, T]`: the
zeros lying in the critical strip `0 < re s < 1`, as a set, so without multiplicity. -/
@[zz_tag "def_Z_T"]
noncomputable def rescale (T : ℝ) (ρ : ℂ) : ℂ :=
  Complex.I * (ρ - 1 / 2) * ((Real.log T / (2 * Real.pi) : ℝ) : ℂ)

/-- The rescaled zeros: the image of the non-trivial zeros up to height `T`. -/
@[zz_tag "def_Z_T"]
noncomputable def rescaledZeros (T : ℝ) : Set ℂ := rescale T '' nontrivialZeros T

/-- The multiplicity transported along the rescaling: the rescaling is injective, so a rescaled
point inherits the multiplicity of the zero it came from. -/
@[zz_tag "def_Z_T"]
noncomputable def rescaledMult (T : ℝ) (w : ℂ) : ℕ :=
  zeroMultiplicity (w / (Complex.I * ((Real.log T / (2 * Real.pi) : ℝ) : ℂ)) + 1 / 2)

/-- The extremal test function `cos(√2 x) / (√2 sin(1/√2))` on `[-1/2, 1/2]`, zero elsewhere. -/
@[zz_tag "def_f0"]
noncomputable def extremalTest (x : ℝ) : ℝ :=
  if |x| ≤ 1 / 2 then Real.cos (Real.sqrt 2 * x) / (Real.sqrt 2 * Real.sin (1 / Real.sqrt 2))
  else 0

/-- The self-convolution of the extremal test function. -/
@[zz_tag "def_Q0"]
noncomputable def extremalSelfConv (x : ℝ) : ℝ := ∫ t : ℝ, extremalTest t * extremalTest (x - t)

/-- `psi` is a `delta`-cutoff: smooth, even, supported in `(-1/2, 1/2)`, valued in `[0, 1]`, and
identically `1` on `|x| ≤ 1/2 - delta`. -/
@[zz_tag "def_cutoff"]
structure IsCutoff (delta : ℝ) (psi : ℝ → ℝ) : Prop where
  /-- `psi` is smooth. -/
  smooth : ContDiff ℝ (⊤ : ℕ∞) psi
  /-- `psi` vanishes off `(-1/2, 1/2)`. -/
  support : ∀ x, 1 / 2 ≤ |x| → psi x = 0
  /-- `psi` is even. -/
  even : ∀ x, psi (-x) = psi x
  /-- `psi` is non-negative. -/
  nonneg : ∀ x, 0 ≤ psi x
  /-- `psi` is at most one. -/
  le_one : ∀ x, psi x ≤ 1
  /-- `psi` is identically one on the shrunken interval. -/
  eq_one : ∀ x, |x| ≤ 1 / 2 - delta → psi x = 1

/-- The normalising constant `A_psi = ∫ psi² f₀`. -/
@[zz_tag "def_normaliser"]
noncomputable def cutoffNormaliser (psi : ℝ → ℝ) : ℝ := ∫ x : ℝ, psi x ^ 2 * extremalTest x

/-- The normalised test function `eta_psi = psi √f₀ / √A_psi`. -/
@[zz_tag "def_eta_psi"]
noncomputable def cutoffTest (psi : ℝ → ℝ) (x : ℝ) : ℝ :=
  psi x * Real.sqrt (extremalTest x) / Real.sqrt (cutoffNormaliser psi)

/-- Its square, `f_psi = eta_psi²`. -/
@[zz_tag "def_f_psi"]
noncomputable def cutoffTestSq (psi : ℝ → ℝ) : ℝ → ℝ := cutoffTest psi ^ 2

/-- Its self-convolution, `Q_psi = f_psi ⋆ f_psi`. -/
@[zz_tag "def_Q_psi"]
noncomputable def cutoffSelfConv (psi : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ t : ℝ, cutoffTestSq psi t * cutoffTestSq psi (x - t)

/-- The corrected test function `r_{psi,T} = Q_psi - Q_psi'' / (4 (log T)²)`, whose Fourier
transform carries the factor that cancels the pair-correlation weight. -/
@[zz_tag "def_r_psi_T"]
noncomputable def correctedTest (psi : ℝ → ℝ) (T : ℝ) (x : ℝ) : ℝ :=
  cutoffSelfConv psi x - iteratedDeriv 2 (cutoffSelfConv psi) x / (4 * Real.log T ^ 2)

end ZetaZeros
