/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch04.AnnealedDefinitions
import LeanPool.CoarseGraining.Homogenization.Probability.Scalarization

/-! # Scalarization Witnesses -/

namespace Homogenization
namespace Book
namespace Ch04
namespace Internal

/-!
# Scalarization witness internals

This file contains the route-specific witness and primitive-data machinery used
to prove the public Chapter 4 scalarization theorems.  The note-facing API should
prefer direct theorem endpoints over these objects.
-/

open scoped Matrix.Norms.Elementwise

noncomputable section

/-- Witness data for scalarization of annealed matrices at scale `n`. -/
structure AnnealedScalarizationWitness {d : ℕ}
    (P : RestrictionCoeffLaw d) (n : ℤ) where
  sigma : ℝ
  sigmaStar : ℝ
  sigma_eq : annealedSigmaAtScale P n = sigma • 1
  sigmaStar_eq : annealedSigmaStarAtScale P n = sigmaStar • 1
  kappa_eq_zero : annealedKappaAtScale P n = 0

/-- Scalarization at scale `n`, packaged as a witness. -/
def HasAnnealedScalarizationAtScale {d : ℕ}
    (P : RestrictionCoeffLaw d) (n : ℤ) : Prop :=
  Nonempty (AnnealedScalarizationWitness P n)

/-- Abstract invariance data sufficient to build a scalarization witness. -/
structure AnnealedScalarizationInvarianceData {d : ℕ} [NeZero d]
    (P : RestrictionCoeffLaw d) (n : ℤ) where
  sigmaFlip : IsSignFlipInvariant (annealedSigmaAtScale P n)
  sigmaSwap : IsSwapInvariant (annealedSigmaAtScale P n)
  sigmaStarFlip : IsSignFlipInvariant (annealedSigmaStarAtScale P n)
  sigmaStarSwap : IsSwapInvariant (annealedSigmaStarAtScale P n)
  kappa_eq_zero : annealedKappaAtScale P n = 0

/-- Primitive scalarization data for the annealed `b` and
`\sigma_*^{-1}` blocks. -/
structure AnnealedScalarizationPrimitiveData {d : ℕ} [NeZero d]
    (P : RestrictionCoeffLaw d) (n : ℤ) where
  sigmaStarInvFlip : IsSignFlipInvariant (annealedSigmaStarInvAtScale P n)
  sigmaStarInvSwap : IsSwapInvariant (annealedSigmaStarInvAtScale P n)
  bFlip : IsSignFlipInvariant (annealedBAtScale P n)
  bSwap : IsSwapInvariant (annealedBAtScale P n)
  sigmaStarInvKappaMean_eq_zero : annealedSigmaStarInvKappaMeanAtScale P n = 0

/-- The scalar contrast ratio attached to a chosen scalarization witness. -/
noncomputable def annealedContrastAtScale {d : ℕ}
    {P : RestrictionCoeffLaw d} {n : ℤ}
    (w : AnnealedScalarizationWitness P n) : ℝ :=
  w.sigma * w.sigmaStar⁻¹

theorem annealedSigmaAtScale_isScalarMatrix_of_invariant {d : ℕ} [NeZero d]
    (P : RestrictionCoeffLaw d) (n : ℤ)
    (hFlip : IsSignFlipInvariant (annealedSigmaAtScale P n))
    (hSwap : IsSwapInvariant (annealedSigmaAtScale P n)) :
    IsScalarMatrix (annealedSigmaAtScale P n) :=
  isScalarMatrix_of_isSignFlipInvariant_of_isSwapInvariant hFlip hSwap

theorem annealedSigmaStarInvAtScale_isScalarMatrix_of_invariant {d : ℕ} [NeZero d]
    (P : RestrictionCoeffLaw d) (n : ℤ)
    (hFlip : IsSignFlipInvariant (annealedSigmaStarInvAtScale P n))
    (hSwap : IsSwapInvariant (annealedSigmaStarInvAtScale P n)) :
    IsScalarMatrix (annealedSigmaStarInvAtScale P n) :=
  isScalarMatrix_of_isSignFlipInvariant_of_isSwapInvariant hFlip hSwap

theorem annealedBAtScale_isScalarMatrix_of_invariant {d : ℕ} [NeZero d]
    (P : RestrictionCoeffLaw d) (n : ℤ)
    (hFlip : IsSignFlipInvariant (annealedBAtScale P n))
    (hSwap : IsSwapInvariant (annealedBAtScale P n)) :
    IsScalarMatrix (annealedBAtScale P n) :=
  isScalarMatrix_of_isSignFlipInvariant_of_isSwapInvariant hFlip hSwap

theorem annealedSigmaStarAtScale_isScalarMatrix_of_invariant {d : ℕ} [NeZero d]
    (P : RestrictionCoeffLaw d) (n : ℤ)
    (hFlip : IsSignFlipInvariant (annealedSigmaStarAtScale P n))
    (hSwap : IsSwapInvariant (annealedSigmaStarAtScale P n)) :
    IsScalarMatrix (annealedSigmaStarAtScale P n) :=
  isScalarMatrix_of_isSignFlipInvariant_of_isSwapInvariant hFlip hSwap

theorem annealedSigmaStarAtScale_isScalarMatrix_of_sigmaStarInv {d : ℕ}
    (P : RestrictionCoeffLaw d) (n : ℤ)
    (hScalar : IsScalarMatrix (annealedSigmaStarInvAtScale P n)) :
    IsScalarMatrix (annealedSigmaStarAtScale P n) := by
  simpa [annealedSigmaStarAtScale, annealedSigmaStar] using! isScalarMatrix_inv hScalar

theorem annealedKappaAtScale_eq_zero_of_sigmaStarInvKappaMean_eq_zero {d : ℕ}
    (P : RestrictionCoeffLaw d) (n : ℤ)
    (hMean : annealedSigmaStarInvKappaMeanAtScale P n = 0) :
    annealedKappaAtScale P n = 0 := by
  change annealedKappa P (cubeSet (originCube d n)) = 0
  rw [annealedKappa]
  simpa [annealedSigmaStarInvKappaMeanAtScale] using
    congrArg (fun M => annealedSigmaStar P (cubeSet (originCube d n)) * M) hMean

theorem annealedSigmaAtScale_eq_annealedBAtScale_of_sigmaStarInvKappaMean_eq_zero
    {d : ℕ} (P : RestrictionCoeffLaw d) (n : ℤ)
    (hMean : annealedSigmaStarInvKappaMeanAtScale P n = 0) :
    annealedSigmaAtScale P n = annealedBAtScale P n := by
  change annealedSigma P (cubeSet (originCube d n)) = annealedB P (cubeSet (originCube d n))
  rw [annealedSigma]
  have hKappa : annealedKappa P (cubeSet (originCube d n)) = 0 := by
    rw [annealedKappa]
    simpa [annealedSigmaStarInvKappaMeanAtScale] using
      congrArg (fun M => annealedSigmaStar P (cubeSet (originCube d n)) * M) hMean
  simp [hKappa]

theorem annealedSigmaAtScale_isScalarMatrix_of_bInvariant_of_sigmaStarInvKappaMean_eq_zero
    {d : ℕ} [NeZero d] (P : RestrictionCoeffLaw d) (n : ℤ)
    (hBFlip : IsSignFlipInvariant (annealedBAtScale P n))
    (hBSwap : IsSwapInvariant (annealedBAtScale P n))
    (hMean : annealedSigmaStarInvKappaMeanAtScale P n = 0) :
    IsScalarMatrix (annealedSigmaAtScale P n) := by
  rw [annealedSigmaAtScale_eq_annealedBAtScale_of_sigmaStarInvKappaMean_eq_zero P n hMean]
  exact annealedBAtScale_isScalarMatrix_of_invariant P n hBFlip hBSwap

/-- Build scalarization from invariant annealed `\sigma`, `\sigma_*`, and
zero coupling. -/
noncomputable def annealedScalarizationWitnessOfInvariant {d : ℕ} [NeZero d]
    (P : RestrictionCoeffLaw d) (n : ℤ)
    (hSigmaFlip : IsSignFlipInvariant (annealedSigmaAtScale P n))
    (hSigmaSwap : IsSwapInvariant (annealedSigmaAtScale P n))
    (hSigmaStarFlip : IsSignFlipInvariant (annealedSigmaStarAtScale P n))
    (hSigmaStarSwap : IsSwapInvariant (annealedSigmaStarAtScale P n))
    (hKappa : annealedKappaAtScale P n = 0) :
    AnnealedScalarizationWitness P n := by
  classical
  let hsigmaScalar :=
    annealedSigmaAtScale_isScalarMatrix_of_invariant P n hSigmaFlip hSigmaSwap
  let hsigmaStarScalar :=
    annealedSigmaStarAtScale_isScalarMatrix_of_invariant P n hSigmaStarFlip hSigmaStarSwap
  exact
    { sigma := Classical.choose hsigmaScalar
      sigmaStar := Classical.choose hsigmaStarScalar
      sigma_eq := Classical.choose_spec hsigmaScalar
      sigmaStar_eq := Classical.choose_spec hsigmaStarScalar
      kappa_eq_zero := hKappa }

theorem hasAnnealedScalarizationAtScale_of_invariant {d : ℕ} [NeZero d]
    (P : RestrictionCoeffLaw d) (n : ℤ)
    (hSigmaFlip : IsSignFlipInvariant (annealedSigmaAtScale P n))
    (hSigmaSwap : IsSwapInvariant (annealedSigmaAtScale P n))
    (hSigmaStarFlip : IsSignFlipInvariant (annealedSigmaStarAtScale P n))
    (hSigmaStarSwap : IsSwapInvariant (annealedSigmaStarAtScale P n))
    (hKappa : annealedKappaAtScale P n = 0) :
    HasAnnealedScalarizationAtScale P n :=
  ⟨annealedScalarizationWitnessOfInvariant P n
    hSigmaFlip hSigmaSwap hSigmaStarFlip hSigmaStarSwap hKappa⟩

/-- Build scalarization from primitive invariant data for `b` and
`\sigma_*^{-1}`. -/
noncomputable def annealedScalarizationWitnessOfPrimitive {d : ℕ} [NeZero d]
    (P : RestrictionCoeffLaw d) (n : ℤ)
    (hSigmaStarInvFlip : IsSignFlipInvariant (annealedSigmaStarInvAtScale P n))
    (hSigmaStarInvSwap : IsSwapInvariant (annealedSigmaStarInvAtScale P n))
    (hBFlip : IsSignFlipInvariant (annealedBAtScale P n))
    (hBSwap : IsSwapInvariant (annealedBAtScale P n))
    (hMean : annealedSigmaStarInvKappaMeanAtScale P n = 0) :
    AnnealedScalarizationWitness P n := by
  classical
  let hSigmaStarInvScalar :=
    annealedSigmaStarInvAtScale_isScalarMatrix_of_invariant P n
      hSigmaStarInvFlip hSigmaStarInvSwap
  let hSigmaStarScalar :=
    annealedSigmaStarAtScale_isScalarMatrix_of_sigmaStarInv P n hSigmaStarInvScalar
  let hSigmaScalar :=
    annealedSigmaAtScale_isScalarMatrix_of_bInvariant_of_sigmaStarInvKappaMean_eq_zero
      P n hBFlip hBSwap hMean
  exact
    { sigma := Classical.choose hSigmaScalar
      sigmaStar := Classical.choose hSigmaStarScalar
      sigma_eq := Classical.choose_spec hSigmaScalar
      sigmaStar_eq := Classical.choose_spec hSigmaStarScalar
      kappa_eq_zero :=
        annealedKappaAtScale_eq_zero_of_sigmaStarInvKappaMean_eq_zero P n hMean }

theorem hasAnnealedScalarizationAtScale_of_primitive {d : ℕ} [NeZero d]
    (P : RestrictionCoeffLaw d) (n : ℤ)
    (hSigmaStarInvFlip : IsSignFlipInvariant (annealedSigmaStarInvAtScale P n))
    (hSigmaStarInvSwap : IsSwapInvariant (annealedSigmaStarInvAtScale P n))
    (hBFlip : IsSignFlipInvariant (annealedBAtScale P n))
    (hBSwap : IsSwapInvariant (annealedBAtScale P n))
    (hMean : annealedSigmaStarInvKappaMeanAtScale P n = 0) :
    HasAnnealedScalarizationAtScale P n :=
  ⟨annealedScalarizationWitnessOfPrimitive P n
    hSigmaStarInvFlip hSigmaStarInvSwap hBFlip hBSwap hMean⟩

namespace AnnealedScalarizationInvarianceData

variable {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} {n : ℤ}

noncomputable def toWitness (h : AnnealedScalarizationInvarianceData P n) :
    AnnealedScalarizationWitness P n :=
  annealedScalarizationWitnessOfInvariant P n
    h.sigmaFlip h.sigmaSwap h.sigmaStarFlip h.sigmaStarSwap h.kappa_eq_zero

theorem hasAnnealedScalarizationAtScale (h : AnnealedScalarizationInvarianceData P n) :
    HasAnnealedScalarizationAtScale P n :=
  ⟨h.toWitness⟩

end AnnealedScalarizationInvarianceData

namespace AnnealedScalarizationPrimitiveData

variable {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} {n : ℤ}

noncomputable def toWitness (h : AnnealedScalarizationPrimitiveData P n) :
    AnnealedScalarizationWitness P n :=
  annealedScalarizationWitnessOfPrimitive P n
    h.sigmaStarInvFlip h.sigmaStarInvSwap h.bFlip h.bSwap h.sigmaStarInvKappaMean_eq_zero

theorem hasAnnealedScalarizationAtScale (h : AnnealedScalarizationPrimitiveData P n) :
    HasAnnealedScalarizationAtScale P n :=
  ⟨h.toWitness⟩

end AnnealedScalarizationPrimitiveData

end

end Internal
end Ch04
end Book
end Homogenization
