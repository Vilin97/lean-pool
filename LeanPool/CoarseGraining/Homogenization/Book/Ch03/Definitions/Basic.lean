/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch01.Definitions
public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Definitions
public import LeanPool.CoarseGraining.Homogenization.Ambient.ScalarMatrix
public import LeanPool.CoarseGraining.Homogenization.Deterministic.ConstantCoefficientDirichletBesov.StandardProjectionSharpKernel
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarsePoincareRHS.Regularity
public import LeanPool.CoarseGraining.Homogenization.Geometry.TriadicCubeTranslation

/-! # Basic Chapter 3 quantities and cube geometry -/

@[expose] public section

open scoped BigOperators ENNReal Pointwise

namespace Homogenization
namespace Book
namespace Ch03

/-!
# Chapter 3 public vocabulary

This file contains the note-facing quantities used in Chapter 3.  The
coefficient input is the Chapter 2 `TriadicCoeffFamily`, so all ellipticity and
compatibility data remain a.e.-based on open cube domains.
-/

noncomputable section

abbrev CoeffFamily (d : ℕ) :=
  Ch02.TriadicCoeffFamily d

abbrev CubeSolution {d : ℕ} (Q : TriadicCube d) (a : CoeffFamily d) :=
  Ch02.Solution (Ch02.cubeDomain Q) (a.coeffOn Q)

/-- Public regularity package for the manuscript assumption
`g ∈ H^s(Q; R^d)`, in the form consumed by the deterministic RHS development. -/
abbrev ForceBesovRegularity {d : ℕ} (Q : TriadicCube d)
    (s : ℝ) (g : Vec d → Vec d) : Prop :=
  CubeVectorBesovHRegularity Q s g

/-- The depth-`j` block-average square for a vector field on a parent cube. -/
noncomputable def negativeBesovVectorDepthAverage {d : ℕ}
    (Q : TriadicCube d) (F : Vec d → Vec d) (j : ℕ) : ℝ :=
  descendantsAverage Q j fun R => vecNormSq (cubeAverageVec R F)

/-- The note-normalized depth contribution in `3^{-s m} B^{-s}_{2,q}`.

If `R` is a depth-`j` descendant of a scale-`m` cube, the outer factor
`3^{-s m}` combines with the scale of `R` to give this `3^{-s j}` weight. -/
noncomputable def negativeBesovVectorDepthSeminorm {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (F : Vec d → Vec d) (j : ℕ) : ℝ :=
  Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
    Real.sqrt (negativeBesovVectorDepthAverage Q F j)

/-- Finite-depth vector-valued `3^{-s m} B^{-s}_{2,q}` seminorm for finite
multiscale exponent `q`. -/
noncomputable def negativeBesovVectorPartialNormFinite {d : ℕ}
    (Q : TriadicCube d) (s q : ℝ) (N : ℕ) (F : Vec d → Vec d) : ℝ :=
  Real.rpow
    (Finset.sum (Finset.range (N + 1)) fun j =>
      Real.rpow (negativeBesovVectorDepthSeminorm Q s F j) q)
    (1 / q)

/-- Public vector-valued `3^{-s m} B^{-s}_{2,q}` seminorm on a cube of scale
`m`, using Euclidean norms of the cube-averaged vector field. -/
noncomputable def scaleNormalizedNegativeBesovVectorNorm {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (q : Ch02.MultiscaleExponent)
    (F : Vec d → Vec d) : ℝ :=
  match q with
  | .finite q =>
      sSup (Set.range fun N : ℕ =>
        negativeBesovVectorPartialNormFinite Q s q N F)
  | .infinity =>
      sSup (Set.range fun j : ℕ =>
        negativeBesovVectorDepthSeminorm Q s F j)

/-- Note-normalized positive `q = 2` Besov seminorm
`3^{s m} [F]_{\underline B^s_{2,2}(Q)}` for vector fields. -/
noncomputable abbrev scaleNormalizedPositiveBesovVectorSeminormTwo {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (F : Vec d → Vec d) : ℝ :=
  cubeBesovPositiveVectorSeminormTwo Q s F

/-- Note-normalized positive `q = 2` Besov norm for vector fields.

The positive seminorms in the deterministic RHS layer are already normalized by
the parent scale.  The full norm adds the top-scale average, matching
`3^{s m} ||F||_{\underline B^s_{2,2}(Q)}`. -/
noncomputable def scaleNormalizedPositiveBesovVectorNormTwo {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (F : Vec d → Vec d) : ℝ :=
  Real.sqrt (vecNormSq (cubeAverageVec Q F)) +
    scaleNormalizedPositiveBesovVectorSeminormTwo Q s F

/-- Public vector-valued genuine dual negative Besov norm, normalized as
`3^{-s m} [F]_{\underline B^{-s}_{2,2}(Q)}`.

This is deliberately separate from `scaleNormalizedNegativeBesovVectorNorm`,
which is the concrete/circ seminorm used in the homogeneous coarse-graining
estimates. -/
noncomputable def scaleNormalizedDualNegativeBesovVectorNormTwo {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (F : Vec d → Vec d) : ℝ :=
  Real.rpow (3 : ℝ) (-s * (((Q.scale : ℤ) : ℝ))) *
    ∑ i : Fin d,
      cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞)
        (fun x => F x i)

/-- Open cube with arbitrary center and triadic scale. -/
noncomputable def openCubeAtScale {d : ℕ} (center : Vec d) (m : ℤ) : Set (Vec d) :=
  { y | ∀ i : Fin d,
      |y i - center i| < Real.rpow (3 : ℝ) (((m : ℤ) : ℝ)) / 2 }

theorem isOpen_openCubeAtScale {d : ℕ} (center : Vec d) (m : ℤ) :
    IsOpen (openCubeAtScale center m) := by
  classical
  unfold openCubeAtScale
  rw [show
      {y : Vec d | ∀ i : Fin d,
          |y i - center i| < Real.rpow (3 : ℝ) (((m : ℤ) : ℝ)) / 2} =
        ⋂ i : Fin d,
          {y : Vec d |
            |y i - center i| < Real.rpow (3 : ℝ) (((m : ℤ) : ℝ)) / 2} by
    ext y
    simp]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_Iio.preimage
      ((continuous_abs.comp ((continuous_apply i).sub continuous_const)))

theorem measurableSet_openCubeAtScale {d : ℕ} (center : Vec d) (m : ℤ) :
    MeasurableSet (openCubeAtScale center m) :=
  (isOpen_openCubeAtScale center m).measurableSet

theorem openCubeAtScale_eq_pi_Ioo {d : ℕ} (center : Vec d) (m : ℤ) :
    openCubeAtScale center m =
      Set.pi Set.univ
        (fun i : Fin d =>
          Set.Ioo
            (center i - Real.rpow (3 : ℝ) (((m : ℤ) : ℝ)) / 2)
            (center i + Real.rpow (3 : ℝ) (((m : ℤ) : ℝ)) / 2)) := by
  ext y
  constructor
  · intro hy i _
    rcases (abs_sub_lt_iff.mp (hy i)) with ⟨hleft, hright⟩
    constructor <;> linarith
  · intro hy i
    rcases hy i (by simp) with ⟨hleft, hright⟩
    exact abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩

theorem openCubeAtScale_zero_eq_openCubeSet_originCube {d : ℕ} (m : ℤ) :
    openCubeAtScale (0 : Vec d) m = openCubeSet (originCube d m) := by
  rw [openCubeAtScale_eq_pi_Ioo, openCubeSet_eq_pi_Ioo]
  simp [originCube, cubeScaleFactor]
  congr
  funext i
  congr <;> ring_nf

theorem openCubeAtScale_eq_translateSet {d : ℕ} (center : Vec d) (m : ℤ) :
    openCubeAtScale center m =
      translateSet center (openCubeAtScale (0 : Vec d) m) := by
  ext y
  rw [mem_translateSet_iff_sub_mem]
  simp [openCubeAtScale]

theorem openCubeAtScale_eq_translateSet_smul_originCube_zero {d : ℕ}
    (center : Vec d) (m : ℤ) :
    openCubeAtScale center m =
      translateSet center
        (cubeScaleFactor (originCube d m) • openCubeAtScale (0 : Vec d) 0) := by
  rw [openCubeAtScale_eq_translateSet, openCubeAtScale_zero_eq_openCubeSet_originCube,
    openCubeSet_originCube_eq_smul_originCube_zero]
  rw [← openCubeAtScale_zero_eq_openCubeSet_originCube (d := d) 0]

theorem openCubeAtScale_eq_translateSet_sub {d : ℕ}
    (z center : Vec d) (m : ℤ) :
    openCubeAtScale center m =
      translateSet z (openCubeAtScale (center - z) m) := by
  ext y
  rw [mem_translateSet_iff_sub_mem]
  constructor
  · intro hy i
    have hcoord :
        (y - z) i - (center - z) i = y i - center i := by
      simp [sub_eq_add_neg]
    rw [hcoord]
    exact hy i
  · intro hy i
    have hcoord :
        (y - z) i - (center - z) i = y i - center i := by
      simp [sub_eq_add_neg]
    rw [← hcoord]
    exact hy i

/-- The boundary patch `cu_m ∩ (x + cu_{m-1})` used in the boundary
Caccioppoli statement. -/
noncomputable def boundaryPatchSet {d : ℕ} (Q : TriadicCube d) (x : Vec d) :
    Set (Vec d) :=
  openCubeSet Q ∩ openCubeAtScale x (Q.scale - 1)

theorem boundaryPatchSet_eq_translateSet_origin {d : ℕ}
    (Q : TriadicCube d) (x : Vec d) :
    boundaryPatchSet Q x =
      translateSet (triadicCubeShift Q)
        (boundaryPatchSet (originCube d Q.scale) (x - triadicCubeShift Q)) := by
  rw [boundaryPatchSet,
    openCubeSet_eq_translateSet_originCube_of_triadicCube Q,
    openCubeAtScale_eq_translateSet_sub (triadicCubeShift Q) x (Q.scale - 1),
    ← translateSet_inter, boundaryPatchSet]
  simp [originCube]

/-- The smaller local energy patch `cu_m ∩ (x + cu_{m-2})`. -/
noncomputable def caccioppoliCoreSet {d : ℕ} (Q : TriadicCube d) (x : Vec d) :
    Set (Vec d) :=
  openCubeSet Q ∩ openCubeAtScale x (Q.scale - 2)

theorem measurableSet_caccioppoliCoreSet {d : ℕ}
    (Q : TriadicCube d) (x : Vec d) :
    MeasurableSet (caccioppoliCoreSet Q x) := by
  exact
    (measurableSet_openCubeSet Q).inter
      (measurableSet_openCubeAtScale x (Q.scale - 2))

theorem caccioppoliCoreSet_eq_translateSet_origin {d : ℕ}
    (Q : TriadicCube d) (x : Vec d) :
    caccioppoliCoreSet Q x =
      translateSet (triadicCubeShift Q)
        (caccioppoliCoreSet (originCube d Q.scale) (x - triadicCubeShift Q)) := by
  rw [caccioppoliCoreSet,
    openCubeSet_eq_translateSet_originCube_of_triadicCube Q,
    openCubeAtScale_eq_translateSet_sub (triadicCubeShift Q) x (Q.scale - 2),
    ← translateSet_inter, caccioppoliCoreSet]
  simp [originCube]

end

end Ch03
end Book
end Homogenization
