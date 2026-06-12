/-
Copyright (c) 2026 Susanna Bertolini, Jaume de Dios Pont. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Susanna Bertolini, Jaume de Dios Pont
-/
import LeanPool.PhaseRetrieval.DimdPoly.Internal.Auxiliary

/-! # DimdPoly -/


open scoped BigOperators

noncomputable section

namespace DimdPolyShowcaseChallenge

/-!
# Showcase: stable phase recovery for Hermite-Fock expansions

This file is the explained, proved public version of the qualitative
fixed-dimension phase-retrieval theorem.

The public statement deliberately uses only ordinary Mathlib objects:

* a point is a vector `z : Fin d -> ℂ`;
* a finite signal is a finitely supported coefficient array
  `F : Finsupp (Fin d -> ℕ) ℂ`;
* the basis functions are written out as explicit finite products of explicit
  one-variable complex Hermite polynomials;
* `TrueHermitePoly κ F` is the finite linear combination
  `∑ α, F α * Φ κ α`;
* `TrueHermitePolys κ` is the set of all functions that arise this way;
* `TrueHermiteFunctions κ` is the Gaussian `L^2` closure of those finite
  functions;
* the stability defect is an explicit Gaussian `L^2` norm of a difference of
  measured magnitudes.

The theorem `stable_phase_retrieval` is the main qualitative statement: it keeps
the reference signal `P` finite, but allows the comparison signal `Q` to lie in
the Gaussian `L^2` closure of `TrueHermitePolys κ`.

-/

/-! ## Explicit Hermite-Fock basis -/

/--
The normalized one-variable Hermite-Fock basis polynomial.

The fixed index `k` is the Hermite level, while `n` is the coefficient index.

Lean's `Finset.range N` is the finite set `{0, ..., N - 1}`.  Thus
`Finset.range (min n k + 1)` indexes exactly `j = 0, ..., min n k`, matching
the inclusive upper limit in the paper formula.
-/
def HermitePoly (k n : ℕ) (z : ℂ) : ℂ :=
  (((Real.sqrt ((Nat.factorial n : ℝ) * (Nat.factorial k : ℝ))) : ℂ)⁻¹) *
    ∑ j ∈ Finset.range (min n k + 1),
      ((-1 : ℂ) ^ j) * (Nat.factorial j : ℂ) *
        (Nat.choose n j : ℂ) * (Nat.choose k j : ℂ) *
        z ^ (n - j) * (star z) ^ (k - j)

variable {d : ℕ}

/--
The `d`-variable basis element.

For each coordinate `q`, take the one-variable basis polynomial determined by
`κ q` and `α q`, then multiply the results over all coordinates.
-/
def Φ (κ α : Fin d -> ℕ) (z : Fin d -> ℂ) : ℂ :=
  ∏ q : Fin d, HermitePoly (κ q) (α q) (z q)

/--
The finite Hermite-Fock polynomial attached to a finite coefficient array.

This is the reader-friendly finite model: it is just a finite sum of explicit
basis polynomials with complex coefficients.
-/
def TrueHermitePoly (κ : Fin d -> ℕ)
    (F : Finsupp (Fin d -> ℕ) ℂ) : (Fin d -> ℂ) -> ℂ :=
  fun z => F.sum fun α c => c * Φ κ α z

/--
The set of all finite Hermite-Fock polynomials at level `κ`.

This is just the range of the explicit coefficient formula above.  Thus a
function `P` belongs to `TrueHermitePolys κ` exactly when it can be written
as `TrueHermitePoly κ F` for some finite coefficient array `F`.
-/
def TrueHermitePolys (κ : Fin d -> ℕ) :
    Set ((Fin d -> ℂ) -> ℂ) :=
  Set.range (TrueHermitePoly κ)


/-! ## Gaussian measure and coefficient geometry -/

/-- The real-valued Gaussian density on `Fin d -> ℂ`. -/
def gaussianDensity (z : Fin d -> ℂ) : ℝ :=
  (1 / Real.pi ^ d) * Real.exp (-Finset.sum Finset.univ fun q : Fin d => ‖z q‖ ^ 2)

/-- The product Gaussian measure on `Fin d -> ℂ`. -/
def γ : MeasureTheory.Measure (Fin d -> ℂ) :=
  MeasureTheory.volume.withDensity fun z => ENNReal.ofReal (gaussianDensity z)

/--
The Gaussian `L²` closure of finite Hermite-Fock polynomials at level `κ`.
Note that functions in L² are only defined up to almost-everywhere equality,
and come with integrability guarantees so we use `f =ᵐ[γ] P` to denote this
"equal in measure" statement.
-/
def TrueHermiteFunctions (κ : Fin d -> ℕ) :
    Set (MeasureTheory.Lp ℂ (p:=2) (γ (d := d))) :=
  closure { f | ∃ P ∈ TrueHermitePolys κ, f =ᵐ[γ] P }

/--
Stable phase retrieval for Gaussian `L²` limits of finite Hermite-Fock polynomials.

This is the main qualitative statement.  The comparison signal `Q` is an element
of the Gaussian `L²` closure of the finite Hermite-Fock polynomials.
-/
theorem stable_phase_retrieval
    (hd : 0 < d) (κ : Fin d -> ℕ)
    (P : (Fin d -> ℂ) -> ℂ) (hP : P ∈ TrueHermitePolys κ) :
    ∃ M : ℝ, 0 < M ∧
      ∀ Q ∈ TrueHermiteFunctions κ,
        ∃ θ : ℂ, ‖θ‖ = 1 ∧
          ∫ z, ‖P z - θ * Q z‖ ^ 2 ∂ γ
            ≤ M ^ 2 * ∫ z, (‖P z‖ - ‖Q z‖) ^ 2 ∂ γ := by
  have hTHP : TrueHermitePoly κ = DimdPolyLEAN.explicitEvalPkappa κ := by
    funext F z
    simp only [TrueHermitePoly, Φ, HermitePoly, DimdPolyLEAN.explicitEvalPkappa,
      DimdPolyLEAN.explicitPhi, DimdPolyLEAN.explicitPhi1D,
      DimdPolyLEAN.explicitComplexHermite]
  have hP' : P ∈ Set.range (DimdPolyLEAN.explicitEvalPkappa κ) := by
    rw [← hTHP]; exact hP
  have hγ : γ = DimdPolyLEAN.explicitGamma d := by
    simp only [γ, gaussianDensity, DimdPolyLEAN.explicitGamma,
      DimdPolyLEAN.explicitGaussianDensity, one_div]
  simp only [TrueHermiteFunctions, TrueHermitePolys, hTHP, hγ]
  exact DimdPolyLEAN.stablePhaseRetrievalExplicitLpClosure_ae (d := d) hd κ P hP'

end DimdPolyShowcaseChallenge
