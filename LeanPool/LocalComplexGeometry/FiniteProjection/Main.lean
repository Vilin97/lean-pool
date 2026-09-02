/-
Copyright (c) 2026 BochaoKong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BochaoKong
-/

import LeanPool.LocalComplexGeometry.FiniteProjection.PreparedQuotient
import LeanPool.LocalComplexGeometry.Geometry.FiniteProjection
import LeanPool.LocalComplexGeometry.WPTBridge.PreparedAssociate
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Finite projection for analytic hypersurface germs

This module exposes the frozen algebraic predicate and combines the prepared
quotient power basis with the genuine local proper finite-projection theorem.
-/

open Filter
open scoped Topology

namespace LocalComplexGeometry

open ClassicalComplexWPT
open WPTBridge

noncomputable section


/-- Include a lower-dimensional germ as a germ independent of the last
coordinate. -/
def baseInclusion (n : ℕ) :
    HolomorphicGerm n →+* HolomorphicGerm (n + 1) :=
  lowerDimensionalInclusion n

/-- The principal ideal of a hypersurface germ. -/
def hypersurfaceIdeal {n : ℕ} (f : HolomorphicGerm (n + 1)) :
    Ideal (HolomorphicGerm (n + 1)) :=
  Ideal.span ({f} : Set (HolomorphicGerm (n + 1)))

/-- The local ring of the hypersurface germ. -/
abbrev HypersurfaceQuotient {n : ℕ}
    (f : HolomorphicGerm (n + 1)) :=
  HolomorphicGerm (n + 1) ⧸ hypersurfaceIdeal f

/-- The base-ring map on a hypersurface quotient. -/
def hypersurfaceBaseRingHom {n : ℕ}
    (f : HolomorphicGerm (n + 1)) :
    HolomorphicGerm n →+* HypersurfaceQuotient f :=
  (Ideal.Quotient.mk (hypersurfaceIdeal f)).comp (baseInclusion n)

/-- A noncircular finite-free rank-`d` predicate with the explicit power
basis `1,w,...,w^(d-1)`. -/
def IsFiniteFreeOfRankOverBase {n : ℕ}
    (f : HolomorphicGerm (n + 1)) (d : ℕ) : Prop :=
  let q := Ideal.Quotient.mk (hypersurfaceIdeal f)
  letI : Algebra (HolomorphicGerm n) (HypersurfaceQuotient f) :=
    (hypersurfaceBaseRingHom f).toAlgebra
  ∃ b : Module.Basis (Fin d) (HolomorphicGerm n)
      (HypersurfaceQuotient f),
    ∀ i, b i = q ((lastCoordinateGerm n) ^ (i : ℕ))

/-- Associated hypersurface equations have the same principal ideal. -/
theorem hypersurfaceIdeal_eq_of_associated {n : ℕ}
    {f g : HolomorphicGerm (n + 1)} (hfg : Associated f g) :
    hypersurfaceIdeal f = hypersurfaceIdeal g := by
  ext h
  rw [hypersurfaceIdeal, hypersurfaceIdeal,
    Ideal.mem_span_singleton, Ideal.mem_span_singleton]
  exact hfg.dvd_iff_dvd_left

/-- The prepared power basis transfers across multiplication by a unit. -/
theorem isFiniteFreeOfRankOverBase_of_associated_prepared {n d : ℕ}
    (g : HolomorphicGerm (n + 1))
    (a : Fin d → Base n → ℂ) (ha : ∀ i, AnalyticAt ℂ (a i) 0)
    (ha0 : ∀ i, a i 0 = 0)
    (hassoc : Associated g (preparedPolynomialGerm a ha)) :
    IsFiniteFreeOfRankOverBase g d := by
  have hideal : hypersurfaceIdeal g = preparedPolynomialIdeal a ha := by
    calc
      hypersurfaceIdeal g = hypersurfaceIdeal (preparedPolynomialGerm a ha) :=
        hypersurfaceIdeal_eq_of_associated hassoc
      _ = preparedPolynomialIdeal a ha := rfl
  unfold IsFiniteFreeOfRankOverBase
  dsimp only
  let e : HypersurfaceQuotient g ≃ₐ[HolomorphicGerm n]
      (HolomorphicGerm (n + 1) ⧸ preparedPolynomialIdeal a ha) :=
    Ideal.quotientEquivAlgOfEq (HolomorphicGerm n) hideal
  refine ⟨(preparedQuotientBasis a ha ha0).map e.symm.toLinearEquiv, ?_⟩
  intro i
  rw [Module.Basis.map_apply, preparedQuotientBasis_apply]
  change e.symm
      (Ideal.Quotient.mk (preparedPolynomialIdeal a ha)
        (lastCoordinateGerm n ^ (i : ℕ))) =
    Ideal.Quotient.mk (hypersurfaceIdeal g)
      (lastCoordinateGerm n ^ (i : ℕ))
  simp [e]

/-- **Finite projection for a nontrivial analytic hypersurface germ.**

After an invertible complex-linear coordinate change, the hypersurface local
ring is finite free over the lower-dimensional base with power basis
`1,w,...,w^(d-1)`.  The same coordinate change admits an analytic
representative whose local zero locus projects properly and surjectively, with
finite fibers of cardinality at most `d` and explicit vertical-boundary
control.
-/
theorem hypersurface_finiteProjection_core
    {n : ℕ} {f : HolomorphicGerm (n + 1)}
    (hf_ne : f ≠ 0)
    (hf_zero : evalAtOriginHom (n + 1) f = 0) :
    ∃ (L : ComplexEuclidean (n + 1) ≃L[ℂ]
          ComplexEuclidean (n + 1))
      (d : ℕ),
      0 < d ∧
      IsFiniteFreeOfRankOverBase (coordinatePullback L f) d ∧
      ∃ F : ComplexEuclidean (n + 1) → ℂ,
        AnalyticAt ℂ F 0 ∧
        (F : FunctionGerm (n + 1)) =
          (coordinatePullback L f : FunctionGerm (n + 1)) ∧
        HasGeometricFiniteProjection F d := by
  obtain ⟨L, d, H, a, u, hd, hH, hcoord, hH0, horder, hprep⟩ :=
    exists_regularized_weierstrassPreparation_pos hf_ne hf_zero
  have hassoc : Associated (coordinatePullback L f)
      (preparedPolynomialGerm a hprep.1) :=
    coordinatePullback_associated_preparedPolynomialGerm
      L H a u hcoord hprep
  have hfinite : IsFiniteFreeOfRankOverBase (coordinatePullback L f) d :=
    isFiniteFreeOfRankOverBase_of_associated_prepared
      (coordinatePullback L f) a hprep.1 hprep.2.1 hassoc
  let F : ComplexEuclidean (n + 1) → ℂ :=
    fun x ↦ H (wptAmbientEquiv n x)
  have hF : AnalyticAt ℂ F 0 := by
    change AnalyticAt ℂ (H ∘ (wptAmbientEquiv n)) 0
    have hH' : AnalyticAt ℂ H (wptAmbientEquiv n 0) := by
      rw [map_zero]
      exact hH
    simpa using hH'.compContinuousLinearMap
      (u := (wptAmbientEquiv n :
        ComplexEuclidean (n + 1) →L[ℂ] Ambient n)) (x := 0)
  have hFcoord : (F : FunctionGerm (n + 1)) =
      (coordinatePullback L f : FunctionGerm (n + 1)) := by
    simpa only [F] using hcoord
  have hgeom : HasGeometricFiniteProjection F d := by
    simpa only [F] using
      hasGeometricFiniteProjection_of_exactOrder hd hH horder
  exact ⟨L, d, hd, hfinite, F, hF, hFcoord, hgeom⟩

end

end LocalComplexGeometry
