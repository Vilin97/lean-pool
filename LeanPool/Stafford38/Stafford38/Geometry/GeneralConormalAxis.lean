/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Geometry.GeneralDivisorialVisibleFrame
import LeanPool.Stafford38.Stafford38.Geometry.FiniteGradientResidueExtension

/-!
# Laurent conormal axes for arbitrary affine components

The prime-component visible frame passes through the generic finite-gradient
adapter to a Laurent equation-conormal point with the prescribed residue.
This is an algebraic witness; the comparison with smooth projective conormal
directions is a separate statement.


## References and proof context

[HTT08] Ryoshi Hotta, Kiyoshi Takeuchi, and Toshiyuki Tanisaki, *D-Modules, Perverse Sheaves,
  and Representation Theory*, Progress in Mathematics 236, Birkhäuser, 2008.
https://doi.org/10.1007/978-0-8176-4523-6

Chapters 1–2 supply characteristic-variety context. The visible-frame and finite-gradient
  construction is project mathematics, not a cited theorem from this book. See docs/literature.md.
-/

namespace Stafford38.Geometry.GeneralConormalAxis

open Stafford38.Geometry.AffineComponentCoordinateSplit
open Stafford38.Geometry.GeneralDivisorialVisibleFrame
open Stafford38.Geometry.ExactVisibleDivisorFrameInterface
open Stafford38.Geometry.CanonicalVisibleDivisorFrameProduction
open Stafford38.Geometry.FiniteGradientResidueExtension
open Stafford38.Geometry.LaurentConormalResidueExtension
open Stafford38.GeometryRetractionSpecialization

noncomputable section

universe u

theorem exists_groundConormalAxis_of_minimalPrime_unit_transcendental
    {k : Type u} [Field k] [CharZero k]
    {m : ℕ} (hm : 0 < m)
    (I : Ideal (MvPolynomial (Fin m) k)) (hI : I.IsRadical)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (hP : P.asIdeal ∈ I.minimalPrimes)
    (hunit : ∃ g : MvPolynomial (Fin m) k,
      MvPolynomial.X ⟨0, hm⟩ * g - 1 ∈ P.asIdeal)
    (htrans : Transcendental k (componentCoordinate P ⟨0, hm⟩)) :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K)
      (y : Fin m → LaurentSeries K) (xi : Fin m → PowerSeries K),
      Sum.elim y
          (fun i ↦ algebraMap (PowerSeries K) (LaurentSeries K) (xi i)) ∈
        groundEquationConormalLocus (k := k) (K := K) I ∧
      residueColumn xi =
        (fun i : Fin m ↦ if i = ⟨0, hm⟩ then 1 else 0) := by
  have hframe := hasVisibleDivisorFrame_of_normalizedCompatibleVisibleFrame P hm
    (generalDivisorialVisibleFrameExistence hm P hunit htrans)
  obtain ⟨K, hK, hAlg, ⟨W⟩⟩ :=
    exists_finiteGradientBoundaryCertificateOver_of_hasVisibleDivisorFrame
      I hI P hP hm hframe
  let := hK
  let := hAlg
  obtain ⟨y, xi, hmem, hres⟩ :=
    exists_groundConormalAxis_of_finiteGradientBoundaryCertificateOver hm I W
  exact ⟨K, hK, hAlg, y, xi, hmem, hres⟩


end
end Stafford38.Geometry.GeneralConormalAxis
