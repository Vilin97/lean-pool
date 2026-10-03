/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import Mathlib

/-!
# Independent geometric vocabulary for almost-Schur

Only Mathlib is imported. Curvature is the actual covariant-derivative
commutator, evaluated on smooth extensions and contracted in orthonormal
frames. Volume is specified by the square root of the metric Gram determinant
in charts. No Poisson, Bianchi, Bochner, or almost-Schur identity is an input.

The smooth-extension construction adapts the attributed curvature core at
12cebb809524d0cd185c6cd7bcb5b73d3562bce1; see PROVENANCE.md.
-/

@[expose] public noncomputable section
open Bundle FiberBundle Set MeasureTheory
open scoped Manifold ContDiff BigOperators

namespace AlmostSchurEntry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless] [T2Space M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I ∞ E (TangentSpace I : M → Type _)]

local notation "TM" => (TangentSpace I : M → Type _)

local instance finiteTangent (x : M) : FiniteDimensional ℝ (TM x) :=
  VectorBundle.finiteDimensional ℝ E TM x

/-- Choose a smooth cutoff supported in the tangent trivialization. -/
def extensionBump (x : M) : SmoothBumpFunction I x := by
  let t := trivializationAt E TM x
  have ht : t.baseSet ∈ nhds x :=
    t.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt E TM x)
  have hφ : ∃ φ : SmoothBumpFunction I x, True ∧ tsupport φ ⊆ t.baseSet :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := I) (c := x)).mem_iff.mp ht
  exact Classical.choose hφ

/-- Extend a tangent vector smoothly without changing it near its base point. -/
def extension (x : M) (v : TM x) : Π y : M, TM y :=
  ((extensionBump (I := I) x : M → ℝ) • FiberBundle.extend E v)

/-- R(X,Y)Z = ∇X∇YZ − ∇Y∇XZ − ∇[X,Y]Z, evaluated at x. -/
def curvature (cov : CovariantDerivative I E TM) (x : M) (u v w : TM x) : TM x :=
  let X := extension (I := I) x u
  let Y := extension (I := I) x v
  let Z := extension (I := I) x w
  cov (fun y => cov Z y (Y y)) x (X x) -
    cov (fun y => cov Z y (X y)) x (Y x) -
    cov Z x (VectorField.mlieBracket I X Y x)

/-- Ric(u,v) is the trace of w ↦ R(w,u)v. -/
def ricci (cov : CovariantDerivative I E TM) (x : M) (u v : TM x) : ℝ :=
  let b := stdOrthonormalBasis ℝ (TM x)
  ∑ i, inner ℝ (curvature cov x (b i) u v) (b i)

/-- Scalar curvature is the metric trace of Ricci. -/
def scalar (cov : CovariantDerivative I E TM) (x : M) : ℝ :=
  let b := stdOrthonormalBasis ℝ (TM x)
  ∑ i, ricci cov x (b i) (b i)

/-- Squared tensor norm of Ric − (R/n)g, not the operator norm. -/
def traceFreeRicciSq (cov : CovariantDerivative I E TM) (x : M) : ℝ :=
  let b := stdOrthonormalBasis ℝ (TM x)
  ∑ i, ∑ j, (ricci cov x (b i) (b j) -
    (scalar cov x / Module.finrank ℝ (TM x)) * inner ℝ (b i) (b j)) ^ 2

variable [MeasurableSpace M] [BorelSpace M]

/-- The defining chart formula for Riemannian volume with basis Haar normalization. -/
def isRiemannianVolume (μ : Measure M) : Prop :=
  letI : MeasurableSpace E := borel E
  letI : BorelSpace E := ⟨rfl⟩
  let b := Module.finBasis ℝ E
  ∀ (c : M) (s : Set M), MeasurableSet s → s ⊆ (extChartAt I c).source →
    μ s = ∫⁻ y in extChartAt I c '' s,
      ENNReal.ofReal (Real.sqrt (Matrix.gram ℝ (fun i =>
        (trivializationAt E TM c).symmL ℝ ((extChartAt I c).symm y) (b i))).det)
      ∂b.addHaar

/-- The ordinary integral average; μ is not assumed to be a probability measure. -/
def average (μ : Measure M) (f : M → ℝ) : ℝ :=
  (∫ x, f x ∂μ) / (μ univ).toReal

variable [Nonempty M] [LindelofSpace M] [CompactSpace M] [PreconnectedSpace M]

/-- Construct the Levi-Civita connection and Riemannian volume, then prove
the almost-Schur inequality and the Einstein equality characterization.
All auxiliary geometric objects are conclusions of the theorem. -/
def geometricStatement : Prop :=
  ∃ (cov : CovariantDerivative I E TM) (μ : Measure M),
    (@CovariantDerivative.IsMetricCompatible E _ _ H _ I M _ _ E _ _ TM _
      (fun _ => inferInstance) (fun _ => inferInstance) _ cov _ _ _ _) ∧
    cov.torsion = 0 ∧ Nonempty (cov.ContMDiffCovariantDerivative 1) ∧
    isRiemannianVolume (I := I) μ ∧ 0 < μ univ ∧ μ univ < ⊤ ∧
    ∀ (_hRic : ∀ (x : M) (v : TM x), 0 ≤ ricci cov x v v)
      (_hd : 2 < (Module.finrank ℝ E : ℝ)),
      let A := ∫ x, (scalar cov x - average μ (scalar cov)) ^ 2 ∂μ
      let B := ∫ x, traceFreeRicciSq cov x ∂μ
      let C := 4 * (Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) - 1) /
        ((Module.finrank ℝ E : ℝ) - 2) ^ 2
      A ≤ C * B ∧
        (A = C * B ↔ ∀ (x : M) (u v : TM x),
          ricci cov x u v = (scalar cov x / Module.finrank ℝ (TM x)) * inner ℝ u v)

end AlmostSchurEntry.Geometry
