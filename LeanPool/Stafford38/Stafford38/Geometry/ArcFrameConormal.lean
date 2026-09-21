/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Geometry.AffineConormalSpan
import LeanPool.Stafford38.Stafford38.Geometry.PowerSeriesArcTangency

/-!
# From an annihilating arc frame to an affine conormal covector

The power-series arc file proves that the uniformizer and coefficient-field
residue directions are tangent to the scalar-extended equation ideal.  The
continuous-frame file separately proves that a finite independent family with
the correct tangent-dimension bound spans the tangent space.  This file joins
those two facts and records the exact local tangent-to-conormal bridge.

The result is deliberately affine and local.  It does not construct a
divisorial chart, identify an arc with a projective component, or descend a
`K[[t]]` chart to `k[[t]]`.  Those are still global production obligations for
`CanonicalAsymptoticLaurentProducer`.
-/

namespace Stafford38.Geometry.ArcFrameConormal

open Stafford38.Geometry.AffineConormalSpan
open Stafford38.Geometry.ContinuousPowerSeriesTangentFrame
open Stafford38.Geometry.PowerSeriesArcTangency

noncomputable section

universe u v

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-! ## The frame-span bridge -/

/--
An actual annihilating power-series arc makes the complete residue frame
tangent.  If that finite frame is independent and its cardinality bounds the
tangent dimension, the equation-defined tangent space is contained in its
span.

The coefficient directions are arbitrary `k`-derivations of the residue
field; no coefficient-field section of a geometric DVR is inferred here.
-/
theorem tangent_le_span_residueFrame_of_annihilatingArc
    {m : ℕ} {κ : Type v} [Fintype κ]
    (I : Ideal (MvPolynomial (Fin m) k))
    (q : Fin m → PowerSeries K)
    (D : κ → Derivation k K K)
    (hq : ∀ f ∈ I,
      MvPolynomial.eval₂ (algebraMap k (PowerSeries K)) q f = 0)
    (hindependent : LinearIndependent K (residueFrameVector q D))
    (hfinrank : Module.finrank K
        (zariskiTangentSpace
          (fun i ↦ PowerSeries.constantCoeff (q i))
          (I.map (MvPolynomial.map (algebraMap k K)))) ≤
      Fintype.card (FrameIndex κ)) :
    zariskiTangentSpace
        (fun i ↦ PowerSeries.constantCoeff (q i))
        (I.map (MvPolynomial.map (algebraMap k K))) ≤
      Submodule.span K (Set.range (residueFrameVector q D)) := by
  apply tangent_le_span_residueFrame
    (k := k) (K := K)
    (I.map (MvPolynomial.map (algebraMap k K))) q D ?_
    hindependent hfinrank
  intro j
  cases j with
  | none =>
      have hD :=
        residueDerivationVector_mem_zariskiTangentSpace_of_eval₂_eq_zero
          (k := k) (K := K) I q
            (uniformizerDerivation (k := k) (K := K)) hq
      change (fun i ↦ PowerSeries.constantCoeff
          (uniformizerDerivation (k := k) (K := K) (q i))) ∈ _
      exact hD
  | some j =>
      have hD :=
        residueDerivationVector_mem_zariskiTangentSpace_of_eval₂_eq_zero
          (k := k) (K := K) I q
            (coefficientwiseDerivation (D j)) hq
      change (fun i ↦ PowerSeries.constantCoeff
          (coefficientwiseDerivation (D j) (q i))) ∈ _
      exact hD

/-! ## The tangent-to-conormal bridge -/

/--
If a covector annihilates every residue-frame direction of an annihilating
arc, then the frame-span bridge places that covector in the affine conormal
space of the scalar-extended equation ideal.

The hypothesis is an explicit finite sum, so the theorem does not hide a
projective tangent comparison or a smoothness assertion.
-/
theorem coordinateCovector_mem_affineConormalSpace_of_annihilatingArcFrame
    {m : ℕ} {κ : Type v} [Fintype κ]
    (I : Ideal (MvPolynomial (Fin m) k))
    (q : Fin m → PowerSeries K)
    (D : κ → Derivation k K K)
    (xi : Fin m → K)
    (hq : ∀ f ∈ I,
      MvPolynomial.eval₂ (algebraMap k (PowerSeries K)) q f = 0)
    (hframe : ∀ j,
      ∑ i, xi i * residueFrameVector q D j i = 0)
    (hindependent : LinearIndependent K (residueFrameVector q D))
    (hfinrank : Module.finrank K
        (zariskiTangentSpace
          (fun i ↦ PowerSeries.constantCoeff (q i))
          (I.map (MvPolynomial.map (algebraMap k K)))) ≤
      Fintype.card (FrameIndex κ)) :
    coordinateCovector xi ∈
      affineConormalSpace
        (fun i ↦ PowerSeries.constantCoeff (q i))
        (I.map (MvPolynomial.map (algebraMap k K))) := by
  have htangent := tangent_le_span_residueFrame_of_annihilatingArc
    (k := k) (K := K) I q D hq hindependent hfinrank
  rw [affineConormalSpace, Submodule.mem_dualAnnihilator]
  intro v hv
  have hspan : ∀ w,
      w ∈ Submodule.span K (Set.range (residueFrameVector q D)) →
        coordinateCovector xi w = 0 := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
        rcases hw with ⟨j, rfl⟩
        simpa [coordinateCovector_apply] using hframe j
    | zero =>
        simp
    | add w z hw hz ihw ihz =>
        rw [map_add, ihw, ihz, add_zero]
    | smul a w hw ih =>
        rw [map_smul, ih, smul_zero]
  exact hspan v (htangent hv)


end

end Stafford38.Geometry.ArcFrameConormal
