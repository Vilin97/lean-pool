/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Geometry.ConvexDomain
import LeanPool.CoarseGraining.Homogenization.Geometry.TriadicCubeTranslation
import LeanPool.CoarseGraining.Homogenization.Geometry.TriadicPartition
import LeanPool.CoarseGraining.Homogenization.PDE.Harmonic
import LeanPool.CoarseGraining.Homogenization.PDE.HarmonicTranslation
import LeanPool.CoarseGraining.Homogenization.Sobolev.PotentialSolenoidalOriginCubeBridge

/-!
# Harmonic functions on triadic subcubes

This file packages the general restriction theorem for `AHarmonicFunction` as a
cube-facing API.  The half-open `cubeSet` transport layer is intentionally kept
separate; on open cubes the restriction follows directly from descendant
containment and monotonicity of ellipticity.
-/

namespace Homogenization

noncomputable section

namespace AHarmonicFunction

private noncomputable def castDomain {d : ℕ} {a : CoeffField d} {U V : Set (Vec d)}
    (hUV : U = V) (u : AHarmonicFunction a U) : AHarmonicFunction a V :=
  hUV ▸ u

private noncomputable def castCoeff {d : ℕ} {a b : CoeffField d} {U : Set (Vec d)}
    (hab : a = b) (u : AHarmonicFunction a U) : AHarmonicFunction b U :=
  hab ▸ u

@[simp] theorem grad_castDomain {d : ℕ} {a : CoeffField d} {U V : Set (Vec d)}
    (hUV : U = V) (u : AHarmonicFunction a U) :
    (castDomain hUV u).toH1.grad = u.toH1.grad := by
  subst V
  rfl

@[simp] theorem grad_castCoeff {d : ℕ} {a b : CoeffField d} {U : Set (Vec d)}
    (hab : a = b) (u : AHarmonicFunction a U) :
    (castCoeff hab u).toH1.grad = u.toH1.grad := by
  subst b
  rfl

theorem isAHarmonicGradient_cubeSet_originCube_iff_openCubeSet
    {d : ℕ} [NeZero d] {n : ℤ} {a : CoeffField d} {f : Vec d → Vec d} :
    IsAHarmonicGradient a (cubeSet (originCube d n)) f ↔
      IsAHarmonicGradient a (openCubeSet (originCube d n)) f := by
  constructor
  · rintro ⟨hpot, hsol⟩
    refine ⟨isPotentialOn_openCubeSet_originCube_of_cubeSet hpot, ?_⟩
    exact isSolenoidalOn_openCubeSet_originCube_of_cubeSet hsol
  · rintro ⟨hpot, hsol⟩
    refine ⟨isPotentialOn_cubeSet_originCube_of_openCubeSet hpot, ?_⟩
    exact isSolenoidalOn_cubeSet_originCube_of_openCubeSet hsol

noncomputable def toCubeSetOriginCube {d : ℕ} [NeZero d] {n : ℤ} {a : CoeffField d}
    (u : AHarmonicFunction a (openCubeSet (originCube d n))) :
    AHarmonicFunction a (cubeSet (originCube d n)) where
  toH1 := u.toH1.toCubeSetOriginCube
  isHarmonic :=
    (isAHarmonicGradient_cubeSet_originCube_iff_openCubeSet (d := d) (n := n) (a := a)
      (f := u.toH1.grad)).2 u.isHarmonic

@[simp] theorem grad_toCubeSetOriginCube {d : ℕ} [NeZero d] {n : ℤ} {a : CoeffField d}
    (u : AHarmonicFunction a (openCubeSet (originCube d n))) :
    (u.toCubeSetOriginCube (n := n)).toH1.grad = u.toH1.grad :=
  rfl

noncomputable def toOpenCubeSetOriginCube {d : ℕ} [NeZero d] {n : ℤ} {a : CoeffField d}
    (u : AHarmonicFunction a (cubeSet (originCube d n))) :
    AHarmonicFunction a (openCubeSet (originCube d n)) where
  toH1 := u.toH1.restrict (isOpen_openCubeSet (originCube d n)) (openCubeSet_subset_cubeSet _)
  isHarmonic :=
    (isAHarmonicGradient_cubeSet_originCube_iff_openCubeSet (d := d) (n := n) (a := a)
      (f := u.toH1.grad)).1 u.isHarmonic

@[simp] theorem grad_toOpenCubeSetOriginCube {d : ℕ} [NeZero d] {n : ℤ} {a : CoeffField d}
    (u : AHarmonicFunction a (cubeSet (originCube d n))) :
    (u.toOpenCubeSetOriginCube (n := n)).toH1.grad = u.toH1.grad :=
  rfl

private noncomputable def toCubeSetOrigin {d : ℕ} [NeZero d] {a : CoeffField d}
    (Q : TriadicCube d) (u : AHarmonicFunction a (cubeSet Q)) :
    AHarmonicFunction (translateCoeffField (triadicCubeShift Q) a)
      (cubeSet (originCube d Q.scale)) := by
  let z : Vec d := triadicCubeShift Q
  let U : Set (Vec d) := cubeSet (originCube d Q.scale)
  have hcube : cubeSet Q = translateSet z U := by
    simpa [z, U] using cubeSet_eq_translateSet_originCube_of_triadicCube Q
  let uTranslated : AHarmonicFunction a (translateSet z U) := castDomain hcube u
  have hcoeff : a = translateCoeffField (-z) (translateCoeffField z a) := by
    rw [translateCoeffField_neg_add_cancel]
  let uOrigin :
      AHarmonicFunction (translateCoeffField z a) (translateSet (-z) (translateSet z U)) := by
    exact AHarmonicFunction.translate (-z) (castCoeff hcoeff uTranslated)
  have hdomain : translateSet (-z) (translateSet z U) = U := by
    simpa [sub_eq_add_neg] using (translateSet_translateSet (d := d) z (-z) U)
  exact castDomain hdomain uOrigin

private noncomputable def toOpenCubeSetOrigin {d : ℕ} [NeZero d] {a : CoeffField d}
    (Q : TriadicCube d) (u : AHarmonicFunction a (openCubeSet Q)) :
    AHarmonicFunction (translateCoeffField (triadicCubeShift Q) a)
      (openCubeSet (originCube d Q.scale)) := by
  let z : Vec d := triadicCubeShift Q
  let U : Set (Vec d) := openCubeSet (originCube d Q.scale)
  have hopen : openCubeSet Q = translateSet z U := by
    simpa [z, U] using openCubeSet_eq_translateSet_originCube_of_triadicCube Q
  let uTranslated : AHarmonicFunction a (translateSet z U) := castDomain hopen u
  have hcoeff : a = translateCoeffField (-z) (translateCoeffField z a) := by
    rw [translateCoeffField_neg_add_cancel]
  let uOrigin :
      AHarmonicFunction (translateCoeffField z a) (translateSet (-z) (translateSet z U)) := by
    exact AHarmonicFunction.translate (-z) (castCoeff hcoeff uTranslated)
  have hdomain : translateSet (-z) (translateSet z U) = U := by
    simpa [sub_eq_add_neg] using (translateSet_translateSet (d := d) z (-z) U)
  exact castDomain hdomain uOrigin

noncomputable def toOpenCubeSet {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffField d}
    (u : AHarmonicFunction a (cubeSet Q)) :
    AHarmonicFunction a (openCubeSet Q) := by
  let z : Vec d := triadicCubeShift Q
  let U : Set (Vec d) := openCubeSet (originCube d Q.scale)
  have hopen : openCubeSet Q = translateSet z U := by
    simpa [z, U] using openCubeSet_eq_translateSet_originCube_of_triadicCube Q
  let uOrigin : AHarmonicFunction (translateCoeffField z a) (cubeSet (originCube d Q.scale)) :=
    toCubeSetOrigin Q u
  let uOpenOrigin : AHarmonicFunction (translateCoeffField z a) U := by
    simpa [U] using uOrigin.toOpenCubeSetOriginCube
  let uOpen : AHarmonicFunction a (translateSet z U) :=
    AHarmonicFunction.translate z uOpenOrigin
  exact castDomain hopen.symm uOpen

noncomputable def toCubeSet {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffField d}
    (u : AHarmonicFunction a (openCubeSet Q)) :
    AHarmonicFunction a (cubeSet Q) := by
  let z : Vec d := triadicCubeShift Q
  let U : Set (Vec d) := cubeSet (originCube d Q.scale)
  have hcube : cubeSet Q = translateSet z U := by
    simpa [z, U] using cubeSet_eq_translateSet_originCube_of_triadicCube Q
  let uOrigin : AHarmonicFunction (translateCoeffField z a) (openCubeSet (originCube d Q.scale)) :=
    toOpenCubeSetOrigin Q u
  let uCubeOrigin : AHarmonicFunction (translateCoeffField z a) U := by
    simpa [U] using uOrigin.toCubeSetOriginCube
  let uCube : AHarmonicFunction a (translateSet z U) :=
    AHarmonicFunction.translate z uCubeOrigin
  exact castDomain hcube.symm uCube

/-- Restrict an `A`-harmonic function on an open triadic cube to an open
descendant cube. -/
noncomputable def restrictToOpenSubcube {d : ℕ} {a : CoeffField d} {lam Lam : ℝ}
    {Q R : TriadicCube d} {j : ℕ}
    (u : AHarmonicFunction a (openCubeSet Q))
    (hEllQ : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hR : R ∈ descendantsAtDepth Q j) :
    AHarmonicFunction a (openCubeSet R) := by
  letI : MeasureTheory.IsFiniteMeasure (volumeMeasureOn (openCubeSet R)) := by
    simpa [volumeMeasureOn] using
      (isOpenBoundedConvexDomain_openCubeSet R).isFiniteMeasure_restrict_volume
  exact u.restrictOfIsEllipticFieldOn
    (isOpen_openCubeSet Q)
    (isOpen_openCubeSet R)
    (openCubeSet_subset_of_mem_descendantsAtDepth hR)
    (hEllQ.mono (measurableSet_openCubeSet R)
      (openCubeSet_subset_of_mem_descendantsAtDepth hR))

@[simp] theorem toH1_restrictToOpenSubcube {d : ℕ} {a : CoeffField d} {lam Lam : ℝ}
    {Q R : TriadicCube d} {j : ℕ}
    (u : AHarmonicFunction a (openCubeSet Q))
    (hEllQ : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hR : R ∈ descendantsAtDepth Q j) :
    (u.restrictToOpenSubcube hEllQ hR).toH1 =
      u.toH1.restrict (isOpen_openCubeSet R)
        (openCubeSet_subset_of_mem_descendantsAtDepth hR) :=
  rfl

@[simp] theorem grad_restrictToOpenSubcube {d : ℕ} {a : CoeffField d} {lam Lam : ℝ}
    {Q R : TriadicCube d} {j : ℕ}
    (u : AHarmonicFunction a (openCubeSet Q))
    (hEllQ : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hR : R ∈ descendantsAtDepth Q j) :
    (u.restrictToOpenSubcube hEllQ hR).toH1.grad = u.toH1.grad :=
  rfl

noncomputable def restrictToSubcube {d : ℕ} [NeZero d] {a : CoeffField d} {lam Lam : ℝ}
    {Q R : TriadicCube d} {j : ℕ}
    (u : AHarmonicFunction a (cubeSet Q))
    (hEllQ : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hR : R ∈ descendantsAtDepth Q j) :
    AHarmonicFunction a (cubeSet R) := by
  let uOpen : AHarmonicFunction a (openCubeSet Q) := u.toOpenCubeSet
  have hEllOpenQ : IsEllipticFieldOn lam Lam (openCubeSet Q) a :=
    hEllQ.mono (measurableSet_openCubeSet Q) (openCubeSet_subset_cubeSet Q)
  exact (uOpen.restrictToOpenSubcube hEllOpenQ hR).toCubeSet

@[simp] theorem grad_toOpenCubeSet {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffField d}
    (u : AHarmonicFunction a (cubeSet Q)) :
    u.toOpenCubeSet.toH1.grad = u.toH1.grad := by
  funext x
  simp [toOpenCubeSet, toCubeSetOrigin, sub_eq_add_neg, add_assoc]

@[simp] theorem grad_toCubeSet {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffField d}
    (u : AHarmonicFunction a (openCubeSet Q)) :
    u.toCubeSet.toH1.grad = u.toH1.grad := by
  funext x
  simp [toCubeSet, toOpenCubeSetOrigin, sub_eq_add_neg, add_assoc]

@[simp] theorem grad_restrictToSubcube {d : ℕ} [NeZero d] {a : CoeffField d} {lam Lam : ℝ}
    {Q R : TriadicCube d} {j : ℕ}
    (u : AHarmonicFunction a (cubeSet Q))
    (hEllQ : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hR : R ∈ descendantsAtDepth Q j) :
    (u.restrictToSubcube hEllQ hR).toH1.grad = u.toH1.grad := by
  simp only [restrictToSubcube, grad_toCubeSet, grad_restrictToOpenSubcube, grad_toOpenCubeSet]

/--
Restrict a `cubeSet` harmonic function to a descendant `cubeSet` when
ellipticity is known on the parent open cube.

This is the a.e.-ellipticity-friendly variant used by Section 5.3: the
restriction proof happens on open cubes, and the result is transported back to
the half-open `cubeSet`.
-/
noncomputable def restrictToSubcubeOfOpenElliptic {d : ℕ} [NeZero d]
    {a : CoeffField d} {lam Lam : ℝ} {Q R : TriadicCube d} {j : ℕ}
    (u : AHarmonicFunction a (cubeSet Q))
    (hEllOpenQ : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hR : R ∈ descendantsAtDepth Q j) :
    AHarmonicFunction a (cubeSet R) := by
  let uOpen : AHarmonicFunction a (openCubeSet Q) := u.toOpenCubeSet
  exact (uOpen.restrictToOpenSubcube hEllOpenQ hR).toCubeSet

@[simp] theorem grad_restrictToSubcubeOfOpenElliptic {d : ℕ} [NeZero d]
    {a : CoeffField d} {lam Lam : ℝ} {Q R : TriadicCube d} {j : ℕ}
    (u : AHarmonicFunction a (cubeSet Q))
    (hEllOpenQ : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hR : R ∈ descendantsAtDepth Q j) :
    (u.restrictToSubcubeOfOpenElliptic hEllOpenQ hR).toH1.grad = u.toH1.grad := by
  simp only [restrictToSubcubeOfOpenElliptic, grad_toCubeSet, grad_restrictToOpenSubcube,
    grad_toOpenCubeSet]

end AHarmonicFunction

end

end Homogenization
