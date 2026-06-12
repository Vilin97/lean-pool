/-
Copyright (c) 2026 Susanna Bertolini, Jaume de Dios Pont. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Susanna Bertolini, Jaume de Dios Pont
-/
/-
  # Definitions.lean
  Core shared definitions for the Hermite phase-retrieval scaffold.

  Scaffolding notes:
  - `Basis/first_true_level_basis.md`
  - `Reduction/circle_reduction.md`
  - `BlockDecomposition/block_decomposition.md`

  The goal of this file is only to pin down the common language of the
  development. Proofs come later.
-/
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Data.Nat.Dist
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-! # Definitions -/


open Complex MeasureTheory Real Finset
open scoped BigOperators ComplexConjugate Topology

noncomputable section

namespace HermiteLEAN

/-- The circle period used throughout the Hermite development. -/
def T : ℝ := 2 * Real.pi

lemma T_pos : 0 < T := by
  dsimp [T]
  positivity

instance : Fact (0 < T) := ⟨T_pos⟩

/-- The normalized circle used for Fourier analysis. -/
abbrev Circle := AddCircle T

/-- Positive part. -/
def posPart (x : ℝ) : ℝ := max x 0

/-- The signed modulus defect imported from the Fock-space argument. -/
def rho (w : ℂ) : ℝ := |‖(1 : ℂ) + w‖ - 1|

/-- The distinguished basis vector `Φ₀(z) = \bar z`. -/
def phi0 (z : ℂ) : ℂ := conj z

/-- The first true-level Hermite basis vector `Φₙ`.

We index from `0`, with `phi 0 = Phi_0` and for `n ≥ 1`

`phi n z = z^(n-1) * (|z|² - n) / sqrt(n!)`.
-/
def phi : ℕ → ℂ → ℂ
  | 0 => phi0
  | n + 1 =>
      fun z =>
        z ^ n *
          (((‖z‖ ^ 2 - (Nat.succ n : ℝ)) /
              Real.sqrt ((Nat.factorial (Nat.succ n) : ℕ) : ℝ)) : ℂ)

/-- The weighted inner product on `L²_γ(ℂ)`. -/
def weightedInner (F G : ℂ → ℂ) : ℂ :=
  (1 / Real.pi : ℂ) *
    ∫ z, F z * conj (G z) * (Real.exp (-‖z‖ ^ 2) : ℂ) ∂(volume : Measure ℂ)

/-- The weighted squared norm on `L²_γ(ℂ)`. -/
def weightedNormSq (F : ℂ → ℂ) : ℝ :=
  (1 / Real.pi) * ∫ z, ‖F z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) ∂(volume : Measure ℂ)

/-- The weighted norm on `L²_γ(ℂ)`. -/
def weightedNorm (F : ℂ → ℂ) : ℝ := Real.sqrt (weightedNormSq F)

/-- The pointwise modulus defect relative to a background function `F₀`. -/
def modulusDefect (F0 G : ℂ → ℂ) (z : ℂ) : ℝ := |‖F0 z + G z‖ - ‖F0 z‖|

/-- The weighted squared defect norm relative to a background function `F₀`. -/
def weightedDefectNormSq (F0 G : ℂ → ℂ) : ℝ :=
  (1 / Real.pi) *
    ∫ z, (modulusDefect F0 G z) ^ 2 * Real.exp (-‖z‖ ^ 2) ∂(volume : Measure ℂ)

/-- The weighted defect norm relative to a background function `F₀`. -/
def weightedDefectNorm (F0 G : ℂ → ℂ) : ℝ := Real.sqrt (weightedDefectNormSq F0 G)

/-- The orthogonal complement to `Φ₀`, expressed via the weighted inner product. -/
def Phi0Perp : Set (ℂ → ℂ) := {F | weightedInner F phi0 = 0}

/-- A finite orthogonal Hermite perturbation `G_a = ∑ a_n Φ_{n+1}`. -/
def hermiteSum {D : ℕ} (a : Fin D → ℂ) (z : ℂ) : ℂ :=
  ∑ n : Fin D, a n * phi (n.1 + 1) z

/-- The coefficient-side squared norm for a finite Hermite perturbation. -/
def hermiteCoeffNormSq {D : ℕ} (a : Fin D → ℂ) : ℝ :=
  ∑ n : Fin D, ‖a n‖ ^ 2

/-- The unit circle point of radius `r` and argument `t`. -/
def circlePoint (r : ℝ) (t : Circle) : ℂ := (r : ℂ) * (fourier (1 : ℤ) t : ℂ)

/-- The coefficient appearing in the circle reduction for `Φ_{n+1}`.

This formula is only intended for `r > 0`; the radius-zero case is handled
separately later on.
-/
def circleCoeff {D : ℕ} (a : Fin D → ℂ) (r : ℝ) (n : Fin D) : ℂ :=
  a n *
    ((((r ^ n.1) * (r ^ 2 - ((n.1 + 1 : ℕ) : ℝ))) /
        (r * Real.sqrt ((Nat.factorial (n.1 + 1) : ℕ) : ℝ)) : ℝ) : ℂ)

/-- The positive-frequency trigonometric polynomial on the circle attached to `G_a`. -/
def circlePolynomial {D : ℕ} (a : Fin D → ℂ) (r : ℝ) : Circle → ℂ :=
  fun t => ∑ n : Fin D, circleCoeff a r n * fourier ((n.1 + 1 : ℕ) : ℤ) t

/-- A generic positive-frequency trigonometric polynomial. -/
def positiveTrigonometricPolynomial (E : Finset ℕ) (c : ℕ → ℂ) : Circle → ℂ :=
  fun t => Finset.sum E (fun n => c n * fourier (n : ℤ) t)

/-- Consecutive positive frequencies `[N, N + L - 1]`. -/
def frequencyBand (N L : ℕ) : Finset ℕ := Finset.Icc N (N + L - 1)

/-- The circle `L²` norm squared with respect to normalized Haar measure. -/
def circleL2Sq (f : Circle → ℂ) : ℝ :=
  ∫ t, ‖f t‖ ^ 2 ∂AddCircle.haarAddCircle

/-- The circle defect against the constant `1`. -/
def circleRhoNormSq (f : Circle → ℂ) : ℝ :=
  ∫ t, (rho (f t)) ^ 2 ∂AddCircle.haarAddCircle

/-- The pointwise circle modulus defect relative to a background function `F₀`. -/
def circleModulusDefect (F0 G : Circle → ℂ) (t : Circle) : ℝ :=
  |‖F0 t + G t‖ - ‖F0 t‖|

/-- The circle squared defect norm relative to a background function `F₀`. -/
def circleDefectNormSq (F0 G : Circle → ℂ) : ℝ :=
  ∫ t, (circleModulusDefect F0 G t) ^ 2 ∂AddCircle.haarAddCircle

/-- The annulus `A_j = { z : j ≤ |z| < j + 1 }`. -/
def annulus (j : ℕ) : Set ℂ := {z | (j : ℝ) ≤ ‖z‖ ∧ ‖z‖ < ((j + 1 : ℕ) : ℝ)}

/-- The weighted squared mass of a function on annulus `A_j`. -/
def annulusIntegralSq (F : ℂ → ℂ) (j : ℕ) : ℝ :=
  (1 / Real.pi) *
    ∫ z in annulus j, ‖F z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) ∂(volume : Measure ℂ)

/-- The square block `I_ℓ = { n : ℓ² ≤ n < (ℓ + 1)² }`. -/
def squareBlock (ℓ : ℕ) : Finset ℕ := Finset.Ico (ℓ ^ 2) ((ℓ + 1) ^ 2)

/-- The block index of a positive Hermite mode. -/
def blockIndex (n : ℕ) : ℕ := Nat.sqrt n

/-- The `ℓ`-th block of a finite Hermite perturbation. -/
def blockPiece {D : ℕ} (a : Fin D → ℂ) (ℓ : ℕ) : ℂ → ℂ :=
  fun z => ∑ n : Fin D, if blockIndex (n.1 + 1) = ℓ then a n * phi (n.1 + 1) z else 0

/-- The local part `V_j` built from blocks at distance at most `M` from `j`. -/
def localPiece {D : ℕ} (a : Fin D → ℂ) (M j : ℕ) : ℂ → ℂ :=
  fun z =>
    ∑ n : Fin D,
      if Nat.dist (blockIndex (n.1 + 1)) j ≤ M then a n * phi (n.1 + 1) z else 0

/-- The distant remainder `R_j = G - V_j`. -/
def remainderPiece {D : ℕ} (a : Fin D → ℂ) (M j : ℕ) : ℂ → ℂ :=
  fun z => hermiteSum a z - localPiece a M j z

/-- The coefficient-side squared norm of one block. -/
def blockCoeffNormSq {D : ℕ} (a : Fin D → ℂ) (ℓ : ℕ) : ℝ :=
  ∑ n : Fin D, if blockIndex (n.1 + 1) = ℓ then ‖a n‖ ^ 2 else 0

/-- The formal Hermite expansion associated to a coefficient sequence. -/
def h1Series (a : ℕ → ℂ) (z : ℂ) : ℂ := ∑' n : ℕ, a n * phi n z

/-- The model space `H₁`, encoded as the closed span of the Hermite family. -/
def H1 : Set (ℂ → ℂ) :=
  ((Submodule.span ℂ (Set.range phi)).topologicalClosure : Set (ℂ → ℂ))

/-- The closed span of the higher Hermite modes `Φ₁, Φ₂, ...`. -/
def H1Orthogonal : Set (ℂ → ℂ) :=
  ((Submodule.span ℂ (Set.range fun n : ℕ => phi (n + 1))).topologicalClosure :
    Set (ℂ → ℂ))

/-- The Gaussian tail appearing in the leakage coefficient. -/
def gaussianTail (c : ℝ) (M : ℕ) : ℝ :=
  ∑' m : ℕ, Real.exp (-c * (posPart ((((m + M + 1 : ℕ) : ℝ) - 4))) ^ 2)

/-- The leakage coefficient `η_M`. -/
def etaCoeff (Cblk cblk : ℝ) (M : ℕ) : ℝ := 2 * Cblk * gaussianTail cblk M

end HermiteLEAN
