/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualParticularStageControls
import LeanPool.NavierStokesAndEuler.NavierStokes.ActualInitialCoherence
public import LeanPool.NavierStokesAndEuler.NavierStokes.ParticularWaveBounds

/-!
# Native reference data from the actual common-cover state

The current state at the reference band still uses that band's common cover.
The reference Volterra geometry, on the other hand, uses the native cover.
This file changes the free auxiliary coordinate before forming the reference
source.  The change acts on the entire current residual, including its
Gaussian and alias inputs.
-/

section

/-!
# A single deck shift of the actual particular solve

Only invariance under the specified lattice vector is assumed.  Equality of
the actual anchored coefficient and forcing paths gives equality of the
Volterra solves, and a bijective copy reindexing gives the same symmetry of
the periodized velocity and pressure.
-/

@[expose] public section

noncomputable section

namespace NavierStokes.SubcoverPeriodicity

open Set Function CommonCoverSolve TorusInverse HarmonicCalculus ParticularWaveBounds
open scoped Topology BigOperators

section LinearSolve

variable {P V E : Type}
variable [NormedAddCommGroup P] [NormedSpace ℝ P]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem forcingAlong_shift (d : LinearData P V E) (g : Geometry)
    (j K : Frequency) (p : P)
    (hf : ∀ Y : Plane, d.source (p, Y + TorusAverages.latticePoint K) = d.source (p,Y))
    (Y : Plane) (s : ℝ) :
    d.forcingAlong g (j + coverIndex g.gap K) ((p, Y + TorusAverages.latticePoint K), s) =
      d.forcingAlong g j ((p,Y),s) := by
  simp only [LinearData.forcingAlong, g.coordinates_deck, g.path_deck, hf]

omit [NormedSpace ℝ P] in
omit [NormedAddCommGroup P] in
theorem forcingPath_shift (d : LinearData P V E) (g : Geometry)
    {a b : ℝ} (j K : Frequency) (p : P)
    (hf : ∀ Y : Plane, d.source (p, Y + TorusAverages.latticePoint K) = d.source (p,Y))
    (Y : Plane) :
    d.forcingPath (a := a) (b := b) g (j + coverIndex g.gap K)
        (p, Y + TorusAverages.latticePoint K) = d.forcingPath g j (p,Y) := by
  apply pathFamily_congr_slice
  intro s
  exact forcingAlong_shift d g j K p hf Y s

variable [CompleteSpace E]

omit [NormedSpace ℝ P] in
omit [NormedAddCommGroup P] in
theorem anchoredSolve_shift (d : LinearData P V E) (g : Geometry)
    {a b : ℝ} (hab : a ≤ b) (j K : Frequency) (p : P)
    (hf : ∀ Y : Plane, d.source (p, Y + TorusAverages.latticePoint K) = d.source (p,Y))
    (Y : Plane) (s : ℝ) :
    d.anchoredSolve g hab (j + coverIndex g.gap K) (p, Y + TorusAverages.latticePoint K) s =
      d.anchoredSolve g hab j (p,Y) s := by
  unfold LinearData.anchoredSolve
  rw [d.coefficientPath_deck, forcingPath_shift d g j K p hf]

omit [NormedSpace ℝ P] in
omit [NormedAddCommGroup P] in
theorem copySolve_shift (d : LinearData P V E) (g : Geometry)
    {a b : ℝ} (hab : a ≤ b) (j K : Frequency) (p : P)
    (hf : ∀ Y : Plane, d.source (p, Y + TorusAverages.latticePoint K) = d.source (p,Y))
    (Y : Plane) :
    d.copySolve g hab (j + coverIndex g.gap K) (p, Y + TorusAverages.latticePoint K) =
      d.copySolve g hab j (p,Y) := by
  unfold LinearData.copySolve
  rw [g.coordinates_deck, anchoredSolve_shift d g hab j K p hf]

end LinearSolve

section ParticularCopies

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

omit [NormedSpace ℝ P] in
omit [NormedAddCommGroup P] in
theorem copyVelocity_shift (t : TangentData P ProblemStatement.Space) (g : Geometry)
    {a b : ℝ} (hab : a ≤ b) (j K : Frequency) (p : P)
    (hf : ∀ Y : Plane, t.source (p, Y + TorusAverages.latticePoint K) = t.source (p,Y))
    (Y : Plane) :
    copyVelocity t g hab (j + coverIndex g.gap K) (p, Y + TorusAverages.latticePoint K) =
      copyVelocity t g hab j (p,Y) := by
  unfold copyVelocity
  rw [copySolve_shift t.linearData g hab j K p hf]

omit [NormedSpace ℝ P] in
omit [NormedAddCommGroup P] in
theorem copyPressure_shift (t : TangentData P ProblemStatement.Space) (g : Geometry)
    {a b : ℝ} (hab : a ≤ b) (j K : Frequency) (frequency : ℝ) (p : P)
    (hf : ∀ Y : Plane, t.source (p, Y + TorusAverages.latticePoint K) = t.source (p,Y))
    (Y : Plane) :
    copyPressure t g hab (j + coverIndex g.gap K) frequency (p, Y + TorusAverages.latticePoint K) =
      copyPressure t g hab j frequency (p,Y) := by
  simp only [copyPressure, copyPressureReal, nativePoint, g.coordinates_deck,
    copySolve_shift t.linearData g hab j K p hf Y, hf Y]

omit [NormedSpace ℝ P] in
omit [NormedAddCommGroup P] in
theorem complexCopyVelocity_shift (t : TangentData P ProblemStatement.Space)
    (f : P × Plane → ComplexVector) (g : Geometry) {a b : ℝ} (hab : a ≤ b)
    (j K : Frequency) (p : P)
    (hf : ∀ Y : Plane, f (p, Y + TorusAverages.latticePoint K) = f (p,Y)) (Y : Plane) :
    complexCopyVelocity t f g hab (j + coverIndex g.gap K) (p, Y + TorusAverages.latticePoint K) =
      complexCopyVelocity t f g hab j (p,Y) := by
  have hr : ∀ Y : Plane, (realData t f).source (p, Y + TorusAverages.latticePoint K) =
      (realData t f).source (p,Y) := fun Y => congrArg realPart (hf Y)
  have hi : ∀ Y : Plane, (imagData t f).source (p, Y + TorusAverages.latticePoint K) =
      (imagData t f).source (p,Y) := fun Y => congrArg imagPart (hf Y)
  simp only [complexCopyVelocity, copyVelocity_shift _ g hab j K p hr Y,
    copyVelocity_shift _ g hab j K p hi Y]

omit [NormedSpace ℝ P] in
omit [NormedAddCommGroup P] in
theorem complexCopyPressure_shift (t : TangentData P ProblemStatement.Space)
    (f : P × Plane → ComplexVector) (g : Geometry) {a b : ℝ} (hab : a ≤ b)
    (j K : Frequency) (frequency : ℝ) (p : P)
    (hf : ∀ Y : Plane, f (p, Y + TorusAverages.latticePoint K) = f (p,Y)) (Y : Plane) :
    complexCopyPressure t f g hab (j + coverIndex g.gap K) frequency
        (p, Y + TorusAverages.latticePoint K) =
      complexCopyPressure t f g hab j frequency (p,Y) := by
  have hr : ∀ Y : Plane, (realData t f).source (p, Y + TorusAverages.latticePoint K) =
      (realData t f).source (p,Y) := fun Y => congrArg realPart (hf Y)
  have hi : ∀ Y : Plane, (imagData t f).source (p, Y + TorusAverages.latticePoint K) =
      (imagData t f).source (p,Y) := fun Y => congrArg imagPart (hf Y)
  simp only [complexCopyPressure, copyPressure_shift _ g hab j K frequency p hr Y,
    copyPressure_shift _ g hab j K frequency p hi Y]

omit [NormedSpace ℝ P] in
omit [NormedAddCommGroup P] in
theorem complexCopyVelocity_shift_of_gap_zero (t : TangentData P ProblemStatement.Space)
    (f : P × Plane → ComplexVector) (g : Geometry) (hg : g.gap = 0)
    {a b : ℝ} (hab : a ≤ b) (j K : Frequency) (p : P)
    (hf : ∀ Y : Plane, f (p, Y + TorusAverages.latticePoint K) = f (p,Y)) (Y : Plane) :
    complexCopyVelocity t f g hab (j + K) (p, Y + TorusAverages.latticePoint K) =
      complexCopyVelocity t f g hab j (p,Y) := by
  simpa only [hg, coverIndex, Function.iterate_zero, id_eq] using
    complexCopyVelocity_shift t f g hab j K p hf Y

omit [NormedSpace ℝ P] in
omit [NormedAddCommGroup P] in
theorem complexCopyPressure_shift_of_gap_zero (t : TangentData P ProblemStatement.Space)
    (f : P × Plane → ComplexVector) (g : Geometry) (hg : g.gap = 0)
    {a b : ℝ} (hab : a ≤ b) (j K : Frequency) (frequency : ℝ) (p : P)
    (hf : ∀ Y : Plane, f (p, Y + TorusAverages.latticePoint K) = f (p,Y)) (Y : Plane) :
    complexCopyPressure t f g hab (j + K) frequency (p, Y + TorusAverages.latticePoint K) =
      complexCopyPressure t f g hab j frequency (p,Y) := by
  simpa only [hg, coverIndex, Function.iterate_zero, id_eq] using
    complexCopyPressure_shift t f g hab j K frequency p hf Y

end ParticularCopies

section PeriodizedCopies

variable {P H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Translation of the copy index is a bijection; there is no multiplicity
factor when passing from the individual solves to the common field. -/
theorem periodizedCopies_shift (g : Geometry) (κ : Plane → ℝ)
    (F : Frequency → P × Plane → H) (K : Frequency) (p : P)
    (hF : ∀ j Y, F (j + coverIndex g.gap K) (p, Y + TorusAverages.latticePoint K) = F j (p, Y))
    (Y : Plane) :
    periodizedCopies g κ F (p, Y + TorusAverages.latticePoint K) =
      periodizedCopies g κ F (p,Y) := by
  unfold periodizedCopies
  calc
    _ = ∑' j : Frequency,
        κ (g.coordinates (j + coverIndex g.gap K) (Y + TorusAverages.latticePoint K)) •
          F (j + coverIndex g.gap K) (p, Y + TorusAverages.latticePoint K) :=
      ((Equiv.addRight (coverIndex g.gap K)).tsum_eq _).symm
    _ = _ := by
      apply tsum_congr
      intro j
      rw [g.coordinates_deck, hF j Y]

end PeriodizedCopies

section CommonFields

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

omit [NormedSpace ℝ P] in
omit [NormedAddCommGroup P] in
theorem commonVelocity_shift (t : TangentData P ProblemStatement.Space)
    (f : P × Plane → ComplexVector) (g : Geometry) {a b : ℝ} (hab : a ≤ b)
    (κ : Plane → ℝ) (K : Frequency) (p : P)
    (hf : ∀ Y : Plane, f (p, Y + TorusAverages.latticePoint K) = f (p,Y)) (Y : Plane) :
    commonVelocity t f g hab κ (p, Y + TorusAverages.latticePoint K) =
      commonVelocity t f g hab κ (p,Y) :=
  periodizedCopies_shift g κ _ K p (fun j Y => complexCopyVelocity_shift t f g hab j K p hf Y) Y

omit [NormedSpace ℝ P] in
omit [NormedAddCommGroup P] in
theorem commonPressure_shift (t : TangentData P ProblemStatement.Space)
    (f : P × Plane → ComplexVector) (g : Geometry) {a b : ℝ} (hab : a ≤ b)
    (κ : Plane → ℝ) (frequency : ℝ) (K : Frequency) (p : P)
    (hf : ∀ Y : Plane, f (p, Y + TorusAverages.latticePoint K) = f (p,Y)) (Y : Plane) :
    commonPressure t f g hab κ frequency (p, Y + TorusAverages.latticePoint K) =
      commonPressure t f g hab κ frequency (p,Y) :=
  periodizedCopies_shift g κ _ K p
    (fun j Y => complexCopyPressure_shift t f g hab j K frequency p hf Y) Y

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
/-- With a compact cutoff, both fields are genuine finite sums over the
same copy set at the specified point. -/
theorem commonFields_finite_sum (t : TangentData P ProblemStatement.Space)
    (f : P × Plane → ComplexVector) (g : Geometry) {a b : ℝ} (hab : a ≤ b)
    (κ : Plane → ℝ) (hκ : HasCompactSupport κ) (frequency : ℝ) (p : P) (Y : Plane) :
    ∃ I : Finset Frequency,
      commonVelocity t f g hab κ (p,Y) =
        ∑ j ∈ I, κ (g.coordinates j Y) • complexCopyVelocity t f g hab j (p,Y) ∧
      commonPressure t f g hab κ frequency (p,Y) =
        ∑ j ∈ I, κ (g.coordinates j Y) • complexCopyPressure t f g hab j frequency (p,Y) := by
  obtain ⟨I,hI⟩ := g.finite_copy_cutoffs hκ ‖Y‖
  refine ⟨I, ?_, ?_⟩
  · unfold commonVelocity periodizedCopies
    exact tsum_eq_sum (fun j hj => by rw [hI Y le_rfl j hj, zero_smul])
  · unfold commonPressure periodizedCopies
    exact tsum_eq_sum (fun j hj => by rw [hI Y le_rfl j hj, zero_smul])

end CommonFields

/-! ## The inherited sublattice, without a unit-lattice assertion -/

/-- Periodicity on the image of the integer lattice under the d-fold
cover. The parameter is fixed throughout the statement. -/
def SubcoverPeriodicAt {P V : Type} (d : ℕ) (f : P × Plane → V) (p : P) : Prop :=
  ∀ Y : Plane, ∀ k : Frequency,
    f (p, Y + TorusAverages.latticePoint (coverIndex d k)) = f (p,Y)

/-- The actual inverse-cover pullback of a source. -/
noncomputable def inverseCoverSource {P V : Type} (d : ℕ) (f : P × Plane → V) : P × Plane → V :=
  fun x => f (x.1, (coverPower d).symm x.2)

theorem inverseCoverSource_shift {P V : Type} (d : ℕ) (f : P × Plane → V)
    (p : P) (k : Frequency)
    (hf : ∀ Y : Plane, f (p, Y + TorusAverages.latticePoint k) = f (p,Y)) (Y : Plane) :
    inverseCoverSource d f (p, Y + TorusAverages.latticePoint (coverIndex d k)) =
      inverseCoverSource d f (p,Y) := by
  unfold inverseCoverSource
  rw [← coverPower_lattice, map_add, ContinuousLinearEquiv.symm_apply_apply]
  exact hf _

theorem inverseCoverSource_subcoverPeriodic {P V : Type} (d : ℕ) (f : P × Plane → V)
    (p : P) (hf : PeriodicAt f p) : SubcoverPeriodicAt d (inverseCoverSource d f) p :=
  fun Y k => inverseCoverSource_shift d f p k (fun Z => hf Z k) Y

/-- Pushing a sublattice-periodic field back through the same cover
recovers the corresponding unit-lattice shift. -/
theorem cover_pullback_shift {P V : Type} (d : ℕ) (f : P × Plane → V)
    (p : P) (k : Frequency)
    (hf : ∀ Y : Plane,
      f (p, Y + TorusAverages.latticePoint (coverIndex d k)) = f (p,Y)) (Y : Plane) :
    f (p, coverPower d (Y + TorusAverages.latticePoint k)) = f (p, coverPower d Y) := by
  rw [map_add, coverPower_lattice]
  exact hf _

section SubcoverFields

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

omit [NormedSpace ℝ P] in
omit [NormedAddCommGroup P] in
theorem commonVelocity_subcover_shift (t : TangentData P ProblemStatement.Space)
    (f : P × Plane → ComplexVector) (g : Geometry) {a b : ℝ} (hab : a ≤ b)
    (κ : Plane → ℝ) (d : ℕ) (k : Frequency) (p : P)
    (hf : ∀ Y : Plane,
      f (p, Y + TorusAverages.latticePoint (coverIndex d k)) = f (p,Y)) (Y : Plane) :
    commonVelocity t f g hab κ (p, Y + TorusAverages.latticePoint (coverIndex d k)) =
      commonVelocity t f g hab κ (p,Y) :=
  commonVelocity_shift t f g hab κ (coverIndex d k) p hf Y

omit [NormedSpace ℝ P] in
omit [NormedAddCommGroup P] in
theorem commonPressure_subcover_shift (t : TangentData P ProblemStatement.Space)
    (f : P × Plane → ComplexVector) (g : Geometry) {a b : ℝ} (hab : a ≤ b)
    (κ : Plane → ℝ) (frequency : ℝ) (d : ℕ) (k : Frequency) (p : P)
    (hf : ∀ Y : Plane,
      f (p, Y + TorusAverages.latticePoint (coverIndex d k)) = f (p,Y)) (Y : Plane) :
    commonPressure t f g hab κ frequency (p, Y + TorusAverages.latticePoint (coverIndex d k)) =
      commonPressure t f g hab κ frequency (p,Y) :=
  commonPressure_shift t f g hab κ frequency (coverIndex d k) p hf Y

omit [NormedSpace ℝ P] in
omit [NormedAddCommGroup P] in
theorem commonVelocity_subcoverPeriodic (t : TangentData P ProblemStatement.Space)
    (f : P × Plane → ComplexVector) (g : Geometry) {a b : ℝ} (hab : a ≤ b)
    (κ : Plane → ℝ) (d : ℕ) (p : P) (hf : SubcoverPeriodicAt d f p) :
    SubcoverPeriodicAt d (commonVelocity t f g hab κ) p :=
  fun Y k => commonVelocity_subcover_shift t f g hab κ d k p (fun Z => hf Z k) Y

omit [NormedSpace ℝ P] in
omit [NormedAddCommGroup P] in
theorem commonPressure_subcoverPeriodic (t : TangentData P ProblemStatement.Space)
    (f : P × Plane → ComplexVector) (g : Geometry) {a b : ℝ} (hab : a ≤ b)
    (κ : Plane → ℝ) (frequency : ℝ) (d : ℕ) (p : P) (hf : SubcoverPeriodicAt d f p) :
    SubcoverPeriodicAt d (commonPressure t f g hab κ frequency) p :=
  fun Y k => commonPressure_subcover_shift t f g hab κ frequency d k p (fun Z => hf Z k) Y

omit [NormedSpace ℝ P] in
omit [NormedAddCommGroup P] in
/-- A single symmetry of the original source yields precisely the
transported symmetry of the solved inverse-cover source. -/
theorem commonVelocity_inverseCoverSource_shift (t : TangentData P ProblemStatement.Space)
    (f : P × Plane → ComplexVector) (g : Geometry) {a b : ℝ} (hab : a ≤ b)
    (κ : Plane → ℝ) (d : ℕ) (k : Frequency) (p : P)
    (hf : ∀ Y : Plane, f (p, Y + TorusAverages.latticePoint k) = f (p,Y)) (Y : Plane) :
    commonVelocity t (inverseCoverSource d f) g hab κ
        (p, Y + TorusAverages.latticePoint (coverIndex d k)) =
      commonVelocity t (inverseCoverSource d f) g hab κ (p,Y) :=
  commonVelocity_subcover_shift t _ g hab κ d k p
    (inverseCoverSource_shift d f p k hf) Y

omit [NormedSpace ℝ P] in
omit [NormedAddCommGroup P] in
theorem commonPressure_inverseCoverSource_shift (t : TangentData P ProblemStatement.Space)
    (f : P × Plane → ComplexVector) (g : Geometry) {a b : ℝ} (hab : a ≤ b)
    (κ : Plane → ℝ) (frequency : ℝ) (d : ℕ) (k : Frequency) (p : P)
    (hf : ∀ Y : Plane, f (p, Y + TorusAverages.latticePoint k) = f (p,Y)) (Y : Plane) :
    commonPressure t (inverseCoverSource d f) g hab κ frequency
        (p, Y + TorusAverages.latticePoint (coverIndex d k)) =
      commonPressure t (inverseCoverSource d f) g hab κ frequency (p,Y) :=
  commonPressure_subcover_shift t _ g hab κ frequency d k p
    (inverseCoverSource_shift d f p k hf) Y

end SubcoverFields

end NavierStokes.SubcoverPeriodicity

end
end

end

@[expose] public section

noncomputable section

namespace NavierStokes.ActualReferenceRebase

open Set Function Filter WeightedClasses CorrectionState HarmonicFields HarmonicCalculus
open CommonCoverSolve TorusInverse PhysicalParticularWave
open scoped ContDiff Topology BigOperators ComplexConjugate

/-! ## Pullback of the actual state through an invertible linear map -/

section Pullback

variable {D E : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Pull field, defined pointwise by `f n (e x)`. -/
noncomputable def pullField (e : D ≃L[ℝ] E) (f : MeanIncrementBounds.Field E) :
    MeanIncrementBounds.Field D := fun n x => f n (e x)

/-- Pull triple, given by `⟨pullField e v.radial, pullField e v.angular, pullField e v.axial⟩`. -/
noncomputable def pullTriple (e : D ≃L[ℝ] E) (v : MeanIncrementBounds.Triple E) :
    MeanIncrementBounds.Triple D :=
  ⟨pullField e v.radial, pullField e v.angular, pullField e v.axial⟩

/-- Pull operators, bundling `epsilon`, `radialFrequency`, `fastCoefficient`, `radius` and the
required compatibility proofs. -/
noncomputable def pullOperators (e : D ≃L[ℝ] E) (o : MeanIncrementBounds.Operators E) :
    MeanIncrementBounds.Operators D where
  epsilon := o.epsilon
  radialFrequency := o.radialFrequency
  fastCoefficient := o.fastCoefficient
  radius x := o.radius (e x)
  radialProfile x := o.radialProfile (e x)
  eR := e.symm o.eR
  eZ := e.symm o.eZ
  eT := e.symm o.eT
  vR := e.symm o.vR
  vT := e.symm o.vT

/-- Pull context, bundling `operators`, `base`, `virtualTheta`, `virtualAxial`. -/
noncomputable def pullContext (e : D ≃L[ℝ] E) (c : Context E) : Context D where
  operators := pullOperators e c.operators
  base := pullTriple e c.base
  virtualTheta := pullField e c.virtualTheta
  virtualAxial := pullField e c.virtualAxial

/-- Pull oscillation, defined pointwise by `u n (e x.1, x.2)`. -/
noncomputable def pullOscillation (e : D ≃L[ℝ] E) (u : Oscillation E) : Oscillation D :=
  fun n x => u n (e x.1, x.2)

/-- Pull errors, given by `⟨pullOscillation e u.base, pullOscillation e u.gaussian,
pullOscillation e u.aliasError⟩`. -/
noncomputable def pullErrors (e : D ≃L[ℝ] E) (u : ExcludedErrors E) : ExcludedErrors D :=
  ⟨pullOscillation e u.base, pullOscillation e u.gaussian, pullOscillation e u.aliasError⟩

/-- Pull state, bundling `mean`, `pressure`, `oscillation`, `oscillatoryPressure` and the
required compatibility proofs. -/
noncomputable def pullState (e : D ≃L[ℝ] E) (u : State E) : State D where
  mean := pullTriple e u.mean
  pressure := pullField e u.pressure
  oscillation := pullOscillation e u.oscillation
  oscillatoryPressure n x := u.oscillatoryPressure n (e x.1, x.2)
  errors := pullErrors e u.errors

/-- Pull coefficients, given by `AddMonoidAlgebra.ofCoeff (Finsupp.mapRange (fun f : E → ℂ =>
fun x => f (e x)) rfl a.coeff)`. -/
noncomputable def pullCoefficients (e : D ≃L[ℝ] E) (a : Coefficients E) : Coefficients D :=
  AddMonoidAlgebra.ofCoeff (Finsupp.mapRange (fun f : E → ℂ => fun x => f (e x)) rfl a.coeff)

@[simp] theorem pullCoefficients_apply (e : D ≃L[ℝ] E) (a : Coefficients E)
    (j : ℤ) (x : D) : pullCoefficients e a j x = a j (e x) := rfl

theorem pullCoefficients_support (e : D ≃L[ℝ] E) (a : Coefficients E) :
    (pullCoefficients e a).support = a.support := by
  ext j
  simp only [Finsupp.mem_support_iff]
  apply not_congr
  constructor
  · intro h
    funext y
    obtain ⟨x, rfl⟩ := e.surjective y
    exact congrFun h x
  · intro h
    funext x
    exact congrFun h (e x)

theorem pullCoefficients_field (e : D ≃L[ℝ] E) (a : Coefficients E)
    (K : ℝ) (Phi : E → ℝ) (kp : ℤ) (x : D × ℝ) :
    field (pullCoefficients e a) K (fun y => Phi (e y)) kp x =
      field a K Phi kp (e x.1, x.2) := by
  simp only [field, evaluate, Finsupp.sum, pullCoefficients_support, pullCoefficients_apply]

/-- Pull block, bundling `velocity`, `pressure`, `frequency`, `phase` and the required
compatibility proofs. -/
noncomputable def pullBlock (e : D ≃L[ℝ] E) (b : HarmonicBlock E) : HarmonicBlock D where
  velocity n i := pullCoefficients e (b.velocity n i)
  pressure n := pullCoefficients e (b.pressure n)
  frequency := b.frequency
  phase n x := b.phase n (e x)
  angularFrequency := b.angularFrequency

/-- Pull block coefficients, defined pointwise by `pullCoefficients e (a n i)`. -/
noncomputable def pullBlockCoefficients (e : D ≃L[ℝ] E)
    (a : HarmonicResidual.BlockCoefficients E) : HarmonicResidual.BlockCoefficients D :=
  fun n i => pullCoefficients e (a n i)

theorem pullBlock_oscillation (e : D ≃L[ℝ] E) (b : HarmonicBlock E)
    (n : ℕ) (x : D × ℝ) :
    (pullBlock e b).oscillation n x = b.oscillation n (e x.1, x.2) := by
  funext i
  exact congrArg Complex.re (pullCoefficients_field e (b.velocity n i)
    (b.frequency n) (b.phase n) (b.angularFrequency n) x)

theorem pullBlock_pressure (e : D ≃L[ℝ] E) (b : HarmonicBlock E)
    (n : ℕ) (x : D × ℝ) :
    (pullBlock e b).oscillatoryPressure n x = b.oscillatoryPressure n (e x.1, x.2) :=
  congrArg Complex.re (pullCoefficients_field e (b.pressure n)
    (b.frequency n) (b.phase n) (b.angularFrequency n) x)

/-- Pull frame, bundling `radius`, `radial`, `axial`, `time` and the required compatibility
proofs. -/
noncomputable def pullFrame (e : D ≃L[ℝ] E) (g : HarmonicResidual.Frame E) :
    HarmonicResidual.Frame D where
  radius x := g.radius (e x)
  radial x := e.symm (g.radial (e x))
  axial x := e.symm (g.axial (e x))
  time x := e.symm (g.time (e x))
  viscosity := g.viscosity

theorem pullContext_frame (e : D ≃L[ℝ] E) (c : Context E) (n : ℕ) :
    HarmonicResidual.contextFrame (pullContext e c) n =
      pullFrame e (HarmonicResidual.contextFrame c n) := by
  unfold HarmonicResidual.contextFrame pullContext pullOperators pullFrame
  congr 1 <;> funext x <;> simp only [map_add, map_smul, map_sub]

theorem pullFrame_on (e : D ≃L[ℝ] E) (g : HarmonicResidual.Frame E) :
    PhysicalResidualNaturality.FrameOn univ e 1 1 (pullFrame e g) g := by
  constructor <;> simp [pullFrame]

/-- The full residual, rather than only its on-graph values, is pulled back.
No carrier nondegeneracy or differentiability premise is needed. -/
theorem pull_residualSource (e : D ≃L[ℝ] E) (c : Context E) (u : State E)
    (b : HarmonicBlock E) (G A : HarmonicResidual.BlockCoefficients E)
    (j : ℤ) (n : ℕ) (x : D) :
    ParticularWaveAssembly.residualSource (pullContext e c) (pullState e u)
      (pullBlock e b) (pullBlockCoefficients e G) (pullBlockCoefficients e A) j n x =
      ParticularWaveAssembly.residualSource c u b G A j n (e x) := by
  have hlabel : PhysicalResidualNaturality.LabelOn univ e 1 1
      (HarmonicResidual.ofBlock (pullBlock e b) (pullBlockCoefficients e G)
        (pullBlockCoefficients e A) n) (HarmonicResidual.ofBlock b G A n) := by
    constructor
    · intro y hy; rfl
    · rfl
    · intro i k y hy
      simp [HarmonicResidual.ofBlock, HarmonicResidual.realCoefficients_apply,
        pullBlock]
    · intro k y hy
      simp [HarmonicResidual.ofBlock, HarmonicResidual.realCoefficients_apply,
        pullBlock]
    · intro i k y hy
      simp [HarmonicResidual.ofBlock, HarmonicResidual.realCoefficients_apply,
        pullBlockCoefficients]
    · intro i k y hy
      simp [HarmonicResidual.ofBlock, HarmonicResidual.realCoefficients_apply,
        pullBlockCoefficients]
  have hg : PhysicalResidualNaturality.FrameOn univ e 1 1
      (HarmonicResidual.contextFrame (pullContext e c) n)
      (HarmonicResidual.contextFrame c n) := by
    rw [pullContext_frame]
    exact pullFrame_on e _
  have hb : ∀ y ∈ (univ : Set D), HarmonicResidual.contextBase (pullContext e c) n y =
      (1 : ℝ) • HarmonicResidual.contextBase c n (e y) := by
    intro y hy; simp [HarmonicResidual.contextBase, pullContext, pullTriple, pullField]
  have hm : ∀ y ∈ (univ : Set D), HarmonicResidual.stateMean (pullState e u) n y =
      (1 : ℝ) • HarmonicResidual.stateMean u n (e y) := by
    intro y hy; simp [HarmonicResidual.stateMean, pullState, pullTriple, pullField]
  funext i
  have he := hlabel.waveResidualCoefficients isOpen_univ one_ne_zero hg hb hm i j x (mem_univ x)
  simp only [one_mul, one_smul] at he
  exact he

/-- Pull strip, bundling `domain`, `isOpen_domain`, `epsilon`, `epsilon_pos` and the required
compatibility proofs. -/
noncomputable def pullStrip (e : D ≃L[ℝ] E) (s : StripData E) : StripData D where
  domain := e ⁻¹' s.domain
  isOpen_domain := s.isOpen_domain.preimage e.continuous
  epsilon := s.epsilon
  epsilon_pos := s.epsilon_pos
  epsilon_le_one := s.epsilon_le_one
  slow := s.slow
  one_le_slow := s.one_le_slow
  delta x := s.delta (e x)
  delta_pos x hx := s.delta_pos (e x) hx
  zeta x := s.zeta (e x)
  zeta_smooth := s.zeta_smooth.comp e.contDiff.contDiffOn (fun _ hx => hx)
  zeta_nonneg x hx := s.zeta_nonneg (e x) hx

/-- Pull wave, bundling `radius`, `radialBase`, `frequencyBase`, `axialBase` and the required
compatibility proofs. -/
noncomputable def pullWave (e : D ≃L[ℝ] E) (a : LinearWaveBounds.WaveCoefficients E) :
    LinearWaveBounds.WaveCoefficients D where
  radius n x := a.radius n (e x)
  radialBase n x := a.radialBase n (e x)
  frequencyBase n x := a.frequencyBase n (e x)
  axialBase n x := a.axialBase n (e x)
  phase n x := a.phase n (e x)
  amplitude n x := a.amplitude n (e x)
  pressure n x := a.pressure n (e x)
  frequency := a.frequency

/-- Pull directions, bundling `radial`, `auxiliary`, `axial`, `angular` and the required
compatibility proofs. -/
noncomputable def pullDirections (e : D ≃L[ℝ] E) (d : LinearWaveBounds.GraphDirections E) :
    LinearWaveBounds.GraphDirections D where
  radial := e.symm d.radial
  auxiliary := e.symm d.auxiliary
  axial := e.symm d.axial
  angular := e.symm d.angular
  slow := e.symm d.slow
  fast := e.symm d.fast
  radialScale := d.radialScale
  fastScale := d.fastScale
  radialProfile x := d.radialProfile (e x)

theorem pullDirections_radial (e : D ≃L[ℝ] E) (d : LinearWaveBounds.GraphDirections E)
    (n : ℕ) (x : D) : (pullDirections e d).radialField n x =
      e.symm (d.radialField n (e x)) := by
  simp only [LinearWaveBounds.GraphDirections.radialField, pullDirections, map_add, map_smul]

theorem pullDirections_axial (e : D ≃L[ℝ] E) (d : LinearWaveBounds.GraphDirections E)
    (s : StripData E) (n : ℕ) (x : D) :
    (pullDirections e d).axialField (pullStrip e s) n x = e.symm (d.axialField s n (e x)) := by
  simp only [LinearWaveBounds.GraphDirections.axialField, pullDirections, pullStrip, map_smul]

end Pullback

/-! ## A separate, genuine native-reference assembly -/

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Inverse cover, given by `(ContinuousLinearEquiv.refl ℝ P).prodCongr (coverPower k).symm`. -/
noncomputable def inverseCover (k : ℕ) : (P × Plane) ≃L[ℝ] (P × Plane) :=
  (ContinuousLinearEquiv.refl ℝ P).prodCongr (coverPower k).symm

@[simp] theorem inverseCover_apply (k : ℕ) (x : P × Plane) :
    inverseCover k x = (x.1, (coverPower k).symm x.2) := rfl

@[simp] theorem inverseCover_symm_apply (k : ℕ) (x : P × Plane) :
    (inverseCover (P := P) k).symm x = (x.1, coverPower k x.2) := rfl

/-- All fields, all directions and the complete source are expressed in the
native fast coordinate.  This assembly is only a reference view; the target
solver keeps its original common-cover data. -/
noncomputable def rebaseAssembly (D : ParticularWaveAssembly.AssemblyData P) (k : ℕ) :
    ParticularWaveAssembly.AssemblyData P where
  reference := D.reference
  charts := ⟨fun _ => id, fun _ => 0, fun _ => 1⟩
  context := pullContext (inverseCover k) D.context
  state := pullState (inverseCover k) D.state
  carrierBlock := pullBlock (inverseCover k) D.carrierBlock
  gaussianInput := pullBlockCoefficients (inverseCover k) D.gaussianInput
  aliasInput := pullBlockCoefficients (inverseCover k) D.aliasInput
  background := pullWave (inverseCover k) D.background
  copy := D.copy
  strip := pullStrip (inverseCover k) D.strip
  directions := pullDirections (inverseCover k) D.directions

theorem rebaseAssembly_source (D : ParticularWaveAssembly.AssemblyData P) (k : ℕ)
    (j : ℤ) (n : ℕ) (x : P × Plane) :
    ParticularWaveAssembly.residualSource (rebaseAssembly D k).context
      (rebaseAssembly D k).state (rebaseAssembly D k).carrierBlock
      (rebaseAssembly D k).gaussianInput (rebaseAssembly D k).aliasInput j n x =
      ParticularWaveAssembly.residualSource D.context D.state D.carrierBlock
        D.gaussianInput D.aliasInput j n (x.1, (coverPower k).symm x.2) := by
  change ParticularWaveAssembly.residualSource
    (pullContext (inverseCover k) D.context) (pullState (inverseCover k) D.state)
    (pullBlock (inverseCover k) D.carrierBlock)
    (pullBlockCoefficients (inverseCover k) D.gaussianInput)
    (pullBlockCoefficients (inverseCover k) D.aliasInput) j n x = _
  simpa only [inverseCover_apply] using
    (pull_residualSource (inverseCover (P := P) k) D.context D.state D.carrierBlock
      D.gaussianInput D.aliasInput j n x)

theorem rebaseAssembly_referenceIdentity
    (D : ParticularWaveAssembly.AssemblyData PhysicalParticularWave.Parameter) (k : ℕ) :
    PhysicalParticularWave.ReferenceIdentity (rebaseAssembly D k) := ⟨rfl, rfl, rfl⟩

/-! ## Binding to the one actual initializer choice and current cycle state -/

open CorrectionInitialization CorrectionInitialization.ActualPrimary

variable {B N0 : ℕ}

/-- Reference residual source as an element of `PhysicalResidualNaturality.Associated →
ComplexVector`. -/
noncomputable def referenceResidualSource
    (x : CorrectionStep.CycleState (ActualParticularStageControls.Label B N0))
    (l : ActualParticularStageControls.Label B N0) (j : ℤ) :
    PhysicalResidualNaturality.Associated → ComplexVector :=
  fun z => ParticularWaveAssembly.residualSource (ActualParticularStageControls.assembly x
      l).context
    (ActualParticularStageControls.assembly x l).state (ActualParticularStageControls.assembly x
        l).carrierBlock
    (ActualParticularStageControls.assembly x l).gaussianInput
        (ActualParticularStageControls.assembly x l).aliasInput
    j (BaseChartJets.cellBand l.2)
    (z.1, (coverPower (ActualParticularStageControls.gap l (BaseChartJets.cellBand l.2))).symm z.2)

/-- Native assembly, given by `rebaseAssembly (ActualParticularStageControls.assembly x l)
(ActualParticularStageControls.gap l (BaseChartJets.cellBand l.2))`. -/
noncomputable def nativeAssembly
    (x : CorrectionStep.CycleState (ActualParticularStageControls.Label B N0))
    (l : ActualParticularStageControls.Label B N0) : ParticularWaveAssembly.AssemblyData Parameter
        :=
  rebaseAssembly (ActualParticularStageControls.assembly x l)
    (ActualParticularStageControls.gap l (BaseChartJets.cellBand l.2))

theorem nativeAssembly_reference
    (x : CorrectionStep.CycleState (ActualParticularStageControls.Label B N0))
    (l : ActualParticularStageControls.Label B N0) :
    (nativeAssembly x l).reference = ActualParticularStageControls.reference l := rfl

theorem nativeAssembly_source
    (x : CorrectionStep.CycleState (ActualParticularStageControls.Label B N0))
    (l : ActualParticularStageControls.Label B N0) (j : ℤ) :
    PhysicalParticularWave.referenceSource (nativeAssembly x l) j = referenceResidualSource x l j
        := by
  funext z
  exact rebaseAssembly_source (ActualParticularStageControls.assembly x l)
    (ActualParticularStageControls.gap l (BaseChartJets.cellBand l.2)) j
    (BaseChartJets.cellBand l.2) z

theorem nativeAssembly_identity
    (x : CorrectionStep.CycleState (ActualParticularStageControls.Label B N0))
    (l : ActualParticularStageControls.Label B N0) :
    PhysicalParticularWave.ReferenceIdentity (nativeAssembly x l) :=
  rebaseAssembly_referenceIdentity _ _

theorem nativeAssembly_raw
    (x : CorrectionStep.CycleState (ActualParticularStageControls.Label B N0))
    (l : ActualParticularStageControls.Label B N0) (j : ℤ) :
    PhysicalParticularWave.referenceRaw (nativeAssembly x l) j =
      ParticularWaveAssembly.angleLift (ParticularWaveBounds.commonVelocity
        ((ActualParticularStageControls.reference l).tangent j) (referenceResidualSource x l j)
        (ActualParticularStageControls.reference l).geometry
        (ActualParticularStageControls.reference l).length_pos.le
        (ActualParticularStageControls.reference l).cutoff) := by
  change ParticularWaveAssembly.angleLift (ParticularWaveBounds.commonVelocity _
    (PhysicalParticularWave.referenceSource (nativeAssembly x l) j) _ _ _) = _
  rw [nativeAssembly_source]
  rfl

theorem nativeAssembly_rawPressure
    (x : CorrectionStep.CycleState (ActualParticularStageControls.Label B N0))
    (l : ActualParticularStageControls.Label B N0) (j : ℤ) :
    PhysicalParticularWave.referenceRawPressure (nativeAssembly x l) j =
      ParticularWaveAssembly.angleLift (ParticularWaveBounds.commonPressure
        ((ActualParticularStageControls.reference l).tangent j) (referenceResidualSource x l j)
        (ActualParticularStageControls.reference l).geometry
        (ActualParticularStageControls.reference l).length_pos.le
        (ActualParticularStageControls.reference l).cutoff
        ((j : ℝ) * (x.coefficients.blocks l).frequency (BaseChartJets.cellBand l.2))) := by
  change ParticularWaveAssembly.angleLift (ParticularWaveBounds.commonPressure _
    (PhysicalParticularWave.referenceSource (nativeAssembly x l) j) _ _ _ _) = _
  rw [nativeAssembly_source]
  rfl

/-! The native reference has its own actual frame and phase. -/

@[simp] theorem associatedToLift_symm_apply (z : PhysicalResidualNaturality.Lift) :
    PhysicalResidualNaturality.associatedToLift.symm z =
      ((z.1, (z.2.1.2, z.2.1.1)), z.2.2) := rfl

@[simp] theorem cycleAssoc_apply (z : CorrectionStep.CyclePoint) :
    CorrectionStep.cycleAssoc z = ((z.1, z.2.1), z.2.2) := rfl

@[simp] theorem cycleAssoc_symm_apply (z : PhysicalResidualNaturality.Associated) :
    CorrectionStep.cycleAssoc.symm z = (z.1.1, (z.1.2, z.2)) := rfl

theorem inverseCover_associatedFrame (h Q : ℝ) (i k : ℕ) :
    pullFrame (inverseCover k) (PhysicalResidualNaturality.associatedFrame h Q i) =
      PhysicalResidualNaturality.associatedFrame h Q (i+k) := by
  unfold pullFrame PhysicalResidualNaturality.associatedFrame StateReindex.frame
    StateReindex.vector ParticularWaveBounds.reindexVector PhysicalResidualNaturality.commonFrame
  congr 1
  · funext x
    change ((1, (0, 0)), coverPower k
      ((ChartScales.Lambda ^ i * Q ^ (ChartScales.radialExponent h / 2) *
        GraphCalculus.radialSpeed (ChartScales.radialExponent h) x.1.1) •
          PhysicalGraphBounds.radialDirection)) = _
    rw [map_smul, coverPower_apply, PhysicalGraphBounds.cover_pow_radialDirection, smul_smul]
    congr 2
    simp only [ PhysicalResidualBridge.commonGraph,
      PhysicalResidualNaturality.associatedToLift_apply]
    rw [pow_add]
    ring
  · funext x
    change ((0, (0, Q ^ h)), coverPower k 0) = _
    rw [map_zero]
    rfl
  · funext x
    change ((0, (-(Q ^ h), 0)), coverPower k
      ((ChartScales.Tg ^ i * Q ^ (1+h)) • PhysicalGraphBounds.timeDirection)) = _
    rw [map_smul, coverPower_apply, PhysicalGraphBounds.cover_pow_timeDirection, smul_smul]
    congr 2
    simp only [PhysicalResidualBridge.commonGraph]
    rw [pow_add]
    ring

theorem associatedContext_frame (B n : ℕ) :
    HarmonicResidual.contextFrame (ActualParticularStageControls.associatedContext (B := B)) n =
      PhysicalResidualNaturality.associatedFrame h (ChartScales.Q n) (CommonWindow.index h n) := by
  rw [ActualParticularStageControls.associatedContext, StateReindex.contextFrame_pull]
  unfold StateReindex.frame StateReindex.vector ParticularWaveBounds.reindexVector
    PhysicalResidualNaturality.associatedFrame PhysicalResidualNaturality.commonFrame
  congr 1
  · funext x
    simp [HarmonicResidual.contextFrame, commonContext, CommonBaseContext.context,
      CommonBaseContext.operators, CorrectionState.graphOperators, CommonBaseContext.reconstruction,
      CommonBaseContext.radialFrequency, PhysicalResidualBridge.ScaledGraph.radial,
      PhysicalResidualBridge.commonGraph, GraphCalculus.radialSpeed, RadialPullback.radialJacobian,
          PhysicalGraphBounds.radialDirection, TorusInverse.vector, StateReindex.vector,
              ParticularWaveBounds.reindexVector,
      PhysicalResidualNaturality.associatedToLift_apply]
    rfl
  · funext x
    simp [HarmonicResidual.contextFrame, commonContext, CommonBaseContext.context,
      CommonBaseContext.operators, CorrectionState.graphOperators, ChartScales.epsilon,
      PhysicalResidualBridge.ScaledGraph.axial, PhysicalResidualBridge.commonGraph,
          StateReindex.vector, ParticularWaveBounds.reindexVector]
  · funext x
    simp [HarmonicResidual.contextFrame, commonContext, CommonBaseContext.context,
      CommonBaseContext.operators, CorrectionState.graphOperators,
          CommonBaseContext.fastCoefficient,
      PhysicalResidualBridge.ScaledGraph.temporal, PhysicalResidualBridge.commonGraph,
          StateReindex.vector, ParticularWaveBounds.reindexVector,
      PhysicalGraphBounds.timeDirection, TorusInverse.vector, ChartScales.epsilon]

theorem nativeAssembly_frame
    (x : CorrectionStep.CycleState (ActualParticularStageControls.Label B N0))
    (l : ActualParticularStageControls.Label B N0) :
    HarmonicResidual.contextFrame (nativeAssembly x l).context (BaseChartJets.cellBand l.2) =
      PhysicalResidualNaturality.associatedFrame h (ChartScales.Q (BaseChartJets.cellBand l.2))
        (ChartScales.nativeIndex h (BaseChartJets.cellBand l.2)) := by
  change HarmonicResidual.contextFrame
    (pullContext (inverseCover (ActualParticularStageControls.gap l (BaseChartJets.cellBand l.2)))
      (ActualParticularStageControls.associatedContext (B := B))) _ = _
  rw [pullContext_frame, associatedContext_frame, inverseCover_associatedFrame]
  rw [ActualParticularStageControls.gap, Nat.add_sub_of_le (CommonWindow.index_le_native h _)]

theorem rebaseAssembly_phase (D : ParticularWaveAssembly.AssemblyData Parameter) (k : ℕ)
    (j : ℤ) (z : WaveSpace) :
    PhysicalParticularWave.referencePhase (rebaseAssembly D k) j z =
      PhysicalParticularWave.referencePhase D j (inverseCover k z) := rfl

theorem rebaseAssembly_frequency (D : ParticularWaveAssembly.AssemblyData Parameter)
    (k : ℕ) (j : ℤ) :
    PhysicalParticularWave.referenceFrequency (rebaseAssembly D k) j =
      PhysicalParticularWave.referenceFrequency D j := rfl

theorem ratioPower_self {Q : ℝ} (hQ : 0 < Q) (a : ℝ) : ratioPower Q Q a = 1 :=
  div_self (Real.rpow_pos_of_pos hQ a).ne'

theorem cylinderChange_inverseCover (h : ℝ) {Q : ℝ} (hQ : 0 < Q) (k : ℕ)
    (z : WaveSpace) :
    cylinderChange h Q Q k (waveEquiv.symm (inverseCover k z)) = waveEquiv.symm z := by
  change ((ratioPower Q Q (1/2) * z.1.1.1,
      ((ratioPower Q Q (CoordinateAlgebra.D h) * z.1.1.2.2,
        ratioPower Q Q 1 * z.1.1.2.1), coverPower k ((coverPower k).symm z.2))), z.1.2) = _
  simp only [ratioPower_self hQ, one_mul, ContinuousLinearEquiv.apply_symm_apply]
  rfl

theorem nativeAssembly_background_phase
    (x : CorrectionStep.CycleState (ActualParticularStageControls.Label B N0))
    (l : ActualParticularStageControls.Label B N0) (z : WaveSpace) :
    (nativeAssembly x l).background.phase (BaseChartJets.cellBand l.2) z =
      ActualSignedGeometry.preparedPhase certificate modulation slots (choice B N0).prepared
        l.1 l.2 (waveEquiv.symm z) := by
  let m := BaseChartJets.cellBand l.2
  let k := ActualParticularStageControls.gap l m
  change (chartCoefficients l.1 l.2).phase m
    (ActualParticularStageControls.nativeToFull (inverseCover k z)) = _
  rw [chartCoefficients_phase_view l.1 l.2 m (CommonWindow.index_le_native h m)]
  change (ChartScales.carrier h m : ℝ) / ChartScales.carrier h m *
    ActualSignedGeometry.preparedPhase certificate modulation slots (choice B N0).prepared l.1 l.2
      (cylinderChange h (ChartScales.Q m) (ChartScales.Q m) k
        (waveEquiv.symm (inverseCover k z))) = _
  rw [div_self (by
      exact_mod_cast (Scaling.carrier_frequency_pos (ChartScales.epsilon_pos h m)).ne'), one_mul,
    cylinderChange_inverseCover h (ChartScales.Q_pos m)]

/-! ## Dependence of a copy solve on one complete parameter fiber -/

section FiberLocality

open ParticularWaveBounds

variable {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]

omit [NormedAddCommGroup Q] [NormedSpace ℝ Q] in
theorem real_copySolve_source_congr (t : TangentData Q ProblemStatement.Space)
    (f g : Q × Plane → ComplexVector) (G : Geometry) {a b : ℝ} (hab : a ≤ b)
    (q : Q) (hf : ∀ Y, f (q, Y) = g (q, Y)) (copy : Frequency) (Y : Plane) :
    (realData t f).linearData.copySolve G hab copy (q,Y) =
      (realData t g).linearData.copySolve G hab copy (q,Y) := by
  apply CopySolveCompatibility.anchoredSolve_eq_of_sameInputs
  refine ⟨fun _ => rfl, ?_⟩
  intro z Z
  change t.linearData.forcingMap (q,z) (realPart (f (q,Z))) =
    t.linearData.forcingMap (q,z) (realPart (g (q,Z)))
  rw [hf Z]

omit [NormedAddCommGroup Q] [NormedSpace ℝ Q] in
theorem imag_copySolve_source_congr (t : TangentData Q ProblemStatement.Space)
    (f g : Q × Plane → ComplexVector) (G : Geometry) {a b : ℝ} (hab : a ≤ b)
    (q : Q) (hf : ∀ Y, f (q, Y) = g (q, Y)) (copy : Frequency) (Y : Plane) :
    (imagData t f).linearData.copySolve G hab copy (q,Y) =
      (imagData t g).linearData.copySolve G hab copy (q,Y) := by
  apply CopySolveCompatibility.anchoredSolve_eq_of_sameInputs
  refine ⟨fun _ => rfl, ?_⟩
  intro z Z
  change t.linearData.forcingMap (q,z) (imagPart (f (q,Z))) =
    t.linearData.forcingMap (q,z) (imagPart (g (q,Z)))
  rw [hf Z]

omit [NormedAddCommGroup Q] [NormedSpace ℝ Q] in
theorem copyVelocity_source_congr (t : TangentData Q ProblemStatement.Space)
    (f g : Q × Plane → ComplexVector) (G : Geometry) {a b : ℝ} (hab : a ≤ b)
    (q : Q) (hf : ∀ Y, f (q, Y) = g (q, Y)) (copy : Frequency) (Y : Plane) :
    complexCopyVelocity t f G hab copy (q,Y) = complexCopyVelocity t g G hab copy (q,Y) := by
  simp only [complexCopyVelocity, copyVelocity, real_copySolve_source_congr t f g G hab q hf,
    imag_copySolve_source_congr t f g G hab q hf]

omit [NormedAddCommGroup Q] [NormedSpace ℝ Q] in
theorem copyPressure_source_congr (t : TangentData Q ProblemStatement.Space)
    (f g : Q × Plane → ComplexVector) (G : Geometry) {a b : ℝ} (hab : a ≤ b)
    (q : Q) (hf : ∀ Y, f (q, Y) = g (q, Y)) (copy : Frequency) (K : ℝ) (Y : Plane) :
    complexCopyPressure t f G hab copy K (q,Y) = complexCopyPressure t g G hab copy K (q,Y) := by
  simp only [complexCopyPressure, copyPressure, copyPressureReal,
    real_copySolve_source_congr t f g G hab q hf,
    imag_copySolve_source_congr t f g G hab q hf]
  simp only [realData, imagData, hf Y]

omit [NormedAddCommGroup Q] [NormedSpace ℝ Q] in
theorem commonVelocity_source_congr (t : TangentData Q ProblemStatement.Space)
    (f g : Q × Plane → ComplexVector) (G : Geometry) {a b : ℝ} (hab : a ≤ b)
    (cutoff : Plane → ℝ) (q : Q) (hf : ∀ Y, f (q, Y) = g (q, Y)) (Y : Plane) :
    ParticularWaveBounds.commonVelocity t f G hab cutoff (q,Y) =
      ParticularWaveBounds.commonVelocity t g G hab cutoff (q,Y) := by
  apply tsum_congr
  intro copy
  exact congrArg (fun v => cutoff (G.coordinates copy Y) • v)
    (copyVelocity_source_congr t f g G hab q hf copy Y)

omit [NormedAddCommGroup Q] [NormedSpace ℝ Q] in
theorem commonPressure_source_congr (t : TangentData Q ProblemStatement.Space)
    (f g : Q × Plane → ComplexVector) (G : Geometry) {a b : ℝ} (hab : a ≤ b)
    (cutoff : Plane → ℝ) (K : ℝ) (q : Q) (hf : ∀ Y, f (q, Y) = g (q, Y)) (Y : Plane) :
    ParticularWaveBounds.commonPressure t f G hab cutoff K (q,Y) =
      ParticularWaveBounds.commonPressure t g G hab cutoff K (q,Y) := by
  apply tsum_congr
  intro copy
  exact congrArg (fun v => cutoff (G.coordinates copy Y) • v)
    (copyPressure_source_congr t f g G hab q hf copy K Y)

end FiberLocality

/-! ## Actual common-band comparison, without truncated reverse gaps -/

/-- Common reference chart as an element of `PhysicalResidualNaturality.Associated ≃L[ℝ]
PhysicalResidualNaturality.Associated`. -/
noncomputable def commonReferenceChart (l : ActualParticularStageControls.Label B N0) (n : ℕ) :
    PhysicalResidualNaturality.Associated ≃L[ℝ] PhysicalResidualNaturality.Associated :=
  (PhysicalResidualNaturality.associatedChart h (ChartScales.Q_pos n)
    (ChartScales.Q_pos (BaseChartJets.cellBand l.2)) (ActualParticularStageControls.gap l n)).trans
      (inverseCover (ActualParticularStageControls.gap l (BaseChartJets.cellBand l.2)))

@[simp] theorem commonReferenceChart_apply (l : ActualParticularStageControls.Label B N0)
    (n : ℕ) (z : PhysicalResidualNaturality.Associated) :
    commonReferenceChart l n z =
      (parameterChange h (ChartScales.Q n) (ChartScales.Q (BaseChartJets.cellBand l.2)) z.1,
        (coverPower (ActualParticularStageControls.gap l (BaseChartJets.cellBand l.2))).symm
          (coverPower (ActualParticularStageControls.gap l n) z.2)) := rfl

theorem associatedChart_stateChart (n m k : ℕ) (z : PhysicalResidualNaturality.Associated) :
    CorrectionStep.cycleAssoc.symm
      (PhysicalResidualNaturality.associatedChart h (ChartScales.Q_pos n) (ChartScales.Q_pos m) k
          z) =
      GaugeStateCoherence.bandChartEquiv h n m k (CorrectionStep.cycleAssoc.symm z) := by
  simp only [PhysicalResidualNaturality.associatedChart_apply, cycleAssoc_symm_apply,
    GaugeStateCoherence.bandChartEquiv_apply, GaugeStateCoherence.bandSlowEquiv_apply,
    MeanChartCompatibility.coverMap_eq_coverPower, GaugeStateCoherence.bandScale_eq_ratioPower,
    parameterChange, ratioPower, Real.rpow_one,
    Real.div_rpow (ChartScales.Q_pos n).le (ChartScales.Q_pos m).le]

theorem commonReferenceChart_forward (l : ActualParticularStageControls.Label B N0)
    (n k : ℕ) (hi : CommonWindow.index h n + k = CommonWindow.index h (BaseChartJets.cellBand l.2))
    (z : PhysicalResidualNaturality.Associated) :
    CorrectionStep.cycleAssoc.symm (commonReferenceChart l n z) =
      GaugeStateCoherence.bandChartEquiv h n (BaseChartJets.cellBand l.2) k
        (CorrectionStep.cycleAssoc.symm z) := by
  have hg : ActualParticularStageControls.gap l n =
      ActualParticularStageControls.gap l (BaseChartJets.cellBand l.2) + k := by
    have hm := CommonWindow.index_le_native h (BaseChartJets.cellBand l.2)
    unfold ActualParticularStageControls.gap
    omega
  rw [commonReferenceChart_apply, hg, CopySolveCompatibility.coverPower_add,
    ContinuousLinearEquiv.symm_apply_apply]
  exact associatedChart_stateChart n (BaseChartJets.cellBand l.2) k z

theorem assembly_source
    (x : CorrectionStep.CycleState (ActualParticularStageControls.Label B N0))
    (l : ActualParticularStageControls.Label B N0) (j : ℤ) (n : ℕ)
    (z : PhysicalResidualNaturality.Associated) :
    ParticularWaveAssembly.residualSource (ActualParticularStageControls.assembly x l).context
      (ActualParticularStageControls.assembly x l).state (ActualParticularStageControls.assembly x
          l).carrierBlock
      (ActualParticularStageControls.assembly x l).gaussianInput
          (ActualParticularStageControls.assembly x l).aliasInput
      j n z = ParticularWaveAssembly.residualSource (commonContext B) x.state
        (x.coefficients.blocks l) (x.coefficients.gaussian l) (x.coefficients.aliasCoefficients l)
        j n (CorrectionStep.cycleAssoc.symm z) := by
  funext i
  exact congrArg (fun b => b.velocity n i j z)
    (StateReindex.residualBlock_pull CorrectionStep.cycleAssoc.symm (commonContext B) x.state
      (x.coefficients.blocks l) (x.coefficients.gaussian l) (x.coefficients.aliasCoefficients l))

theorem transportedSource_eq_commonReference
    (x : CorrectionStep.CycleState (ActualParticularStageControls.Label B N0))
    (l : ActualParticularStageControls.Label B N0) (j : ℤ) (n : ℕ)
    (z : PhysicalResidualNaturality.Associated) :
    PhysicalParticularWave.transportedResidualSource (nativeAssembly x l) h (ChartScales.Q n)
      (ChartScales.Q (BaseChartJets.cellBand l.2)) (ActualParticularStageControls.gap l n) j z =
      sourceWeight h (ChartScales.Q n) (ChartScales.Q (BaseChartJets.cellBand l.2)) •
        ParticularWaveAssembly.residualSource (commonContext B) x.state (x.coefficients.blocks l)
          (x.coefficients.gaussian l) (x.coefficients.aliasCoefficients l) j
              (BaseChartJets.cellBand l.2)
          (CorrectionStep.cycleAssoc.symm (commonReferenceChart l n z)) := by
  rw [PhysicalParticularWave.transportedResidualSource_apply _ h (ChartScales.Q_pos n)
    (ChartScales.Q_pos (BaseChartJets.cellBand l.2)), nativeAssembly_source]
  exact congrArg (fun v : ComplexVector => sourceWeight h (ChartScales.Q n)
    (ChartScales.Q (BaseChartJets.cellBand l.2)) • v)
      (assembly_source x l j (BaseChartJets.cellBand l.2) (commonReferenceChart l n z))

theorem state_sourceWeight (n m : ℕ) :
    GaugeStateCoherence.bandVelocityScale h n m * GaugeStateCoherence.bandVelocityScale h n m *
      GaugeStateCoherence.bandScale n m = sourceWeight h (ChartScales.Q n) (ChartScales.Q m) := by
  simpa only [GaugeStateCoherence.bandVelocityScale_eq_ratioPower,
    GaugeStateCoherence.bandScale_eq_ratioPower, velocityWeight] using
      PhysicalResidualNaturality.weight_source (ChartScales.Q_pos n) (ChartScales.Q_pos m) h

/-- This consumes exactly the full-fiber state and block conclusions of the
physical recurrence.  It does not assume source or solved-wave coherence. -/
theorem source_forward
    (x : CorrectionStep.CycleState (ActualParticularStageControls.Label B N0))
    (l : ActualParticularStageControls.Label B N0) {V : Set Plane} (hV : IsOpen V)
    (htime : ∀ s ∈ V, 0 < s.1) (n k : ℕ)
    (hi : CommonWindow.index h n + k = CommonWindow.index h (BaseChartJets.cellBand l.2))
    (HS : PhysicalResidualNaturality.StateOn (PhysicalMeanDomain.slowDomain V)
      (GaugeStateCoherence.bandChartEquiv h n (BaseChartJets.cellBand l.2) k)
      (GaugeStateCoherence.bandVelocityScale h n (BaseChartJets.cellBand l.2))
      (GaugeStateCoherence.bandScale n (BaseChartJets.cellBand l.2))
      x.state x.state n (BaseChartJets.cellBand l.2))
    (HB : PhysicalResidualNaturality.BlockFieldsOn (PhysicalMeanDomain.slowDomain V)
      (GaugeStateCoherence.bandChartEquiv h n (BaseChartJets.cellBand l.2) k)
      (GaugeStateCoherence.bandVelocityScale h n (BaseChartJets.cellBand l.2))
      (GaugeStateCoherence.bandScale n (BaseChartJets.cellBand l.2))
      (x.coefficients.blocks l) (x.coefficients.blocks l)
      (x.coefficients.gaussian l) (x.coefficients.aliasCoefficients l)
      (x.coefficients.gaussian l) (x.coefficients.aliasCoefficients l) n (BaseChartJets.cellBand
          l.2))
    (j : ℤ) (z : PhysicalResidualNaturality.Associated) (hz : z.1.2 ∈ V) :
    ParticularWaveAssembly.residualSource (ActualParticularStageControls.assembly x l).context
      (ActualParticularStageControls.assembly x l).state (ActualParticularStageControls.assembly x
          l).carrierBlock
      (ActualParticularStageControls.assembly x l).gaussianInput
          (ActualParticularStageControls.assembly x l).aliasInput
      j n z = PhysicalParticularWave.transportedResidualSource (nativeAssembly x l) h
          (ChartScales.Q n)
        (ChartScales.Q (BaseChartJets.cellBand l.2)) (ActualParticularStageControls.gap l n) j z :=
            by
  have he := HS.source (ActualInitialCoherence.context_band B htime n (BaseChartJets.cellBand l.2)
      k hi)
    (PhysicalMeanDomain.slowDomain_open hV) (GaugeStateCoherence.bandScale_pos n
        (BaseChartJets.cellBand l.2)).ne'
      HB j (x := CorrectionStep.cycleAssoc.symm z) hz
  rw [state_sourceWeight] at he
  rw [assembly_source, transportedSource_eq_commonReference, commonReferenceChart_forward l n k hi]
  exact he

/-! The reference operator identities hold on the entire free lift. -/

/-- Angle embed, given by `((v.1, 0), v.2)`. -/
noncomputable def angleEmbed (v : PhysicalResidualNaturality.Associated) : WaveSpace :=
  ((v.1, 0), v.2)

theorem associatedDirections_radial (B n : ℕ) (z : WaveSpace) :
    (ActualParticularStageControls.directions (B := B)).radialField n z =
      angleEmbed ((HarmonicResidual.contextFrame
        (ActualParticularStageControls.associatedContext (B := B)) n).radial (z.1.1,z.2)) := by
  simp only [ActualParticularStageControls.directions, ParticularWaveBounds.reindex_radialField,
    PrimaryResidualClass.directions_radial, ActualParticularStageControls.associatedContext,
    StateReindex.contextFrame_pull, ParticularWaveBounds.reindexVector,
    HarmonicResidual.liftDirection, StateReindex.frame, StateReindex.vector]
  rfl

theorem associatedDirections_axial (B n : ℕ) (z : WaveSpace) :
    (ActualParticularStageControls.directions (B := B)).axialField
      (CorrectionStep.ParticularParameters.nativeStrip
          ActualParticularStageControls.associatedStrip) n z =
      angleEmbed ((HarmonicResidual.contextFrame
        (ActualParticularStageControls.associatedContext (B := B)) n).axial (z.1.1,z.2)) := by
  change (ChartScales.Q n ^ h) •
      (ActualParticularStageControls.nativeToFull.symm ((commonContext B).operators.eZ,0)) = _
  rw [← LinearIsometryEquiv.map_smul]
  simp only [Prod.smul_mk, smul_zero]
  rfl

theorem nativeDirections_radial
    (x : CorrectionStep.CycleState (ActualParticularStageControls.Label B N0))
    (l : ActualParticularStageControls.Label B N0) (n : ℕ) (z : WaveSpace) :
    (nativeAssembly x l).directions.radialField n z =
      angleEmbed ((HarmonicResidual.contextFrame (nativeAssembly x l).context n).radial
          (z.1.1,z.2)) := by
  change (pullDirections (inverseCover (ActualParticularStageControls.gap l (BaseChartJets.cellBand
      l.2)))
    (ActualParticularStageControls.directions (B := B))).radialField n z = _
  rw [pullDirections_radial, associatedDirections_radial]
  change _ = angleEmbed ((HarmonicResidual.contextFrame
    (pullContext (inverseCover (ActualParticularStageControls.gap l (BaseChartJets.cellBand l.2)))
      (ActualParticularStageControls.associatedContext (B := B))) n).radial _)
  rw [pullContext_frame]
  rfl

theorem nativeDirections_axial
    (x : CorrectionStep.CycleState (ActualParticularStageControls.Label B N0))
    (l : ActualParticularStageControls.Label B N0) (n : ℕ) (z : WaveSpace) :
    (nativeAssembly x l).directions.axialField (nativeAssembly x l).strip n z =
      angleEmbed ((HarmonicResidual.contextFrame (nativeAssembly x l).context n).axial (z.1.1,z.2))
          := by
  change (pullDirections (inverseCover (ActualParticularStageControls.gap l (BaseChartJets.cellBand
      l.2)))
    (ActualParticularStageControls.directions (B := B))).axialField
      (pullStrip (inverseCover (ActualParticularStageControls.gap l (BaseChartJets.cellBand l.2)))
        (CorrectionStep.ParticularParameters.nativeStrip
            ActualParticularStageControls.associatedStrip)) n z = _
  rw [pullDirections_axial, associatedDirections_axial]
  change _ = angleEmbed ((HarmonicResidual.contextFrame
    (pullContext (inverseCover (ActualParticularStageControls.gap l (BaseChartJets.cellBand l.2)))
      (ActualParticularStageControls.associatedContext (B := B))) n).axial _)
  rw [pullContext_frame]
  rfl

theorem nativeDirections_angular
    (x : CorrectionStep.CycleState (ActualParticularStageControls.Label B N0))
    (l : ActualParticularStageControls.Label B N0) :
    (nativeAssembly x l).directions.angular = (((0 : Parameter),1),(0 : Plane)) := by
  change ((inverseCover (P := Parameter × ℝ)
    (ActualParticularStageControls.gap l (BaseChartJets.cellBand l.2))).symm
      (((0 : Parameter),1),(0 : Plane))) = _
  rw [inverseCover_symm_apply, map_zero]

theorem nativeAssembly_referenceChart
    (x : CorrectionStep.CycleState (ActualParticularStageControls.Label B N0))
    (l : ActualParticularStageControls.Label B N0) :
    PhysicalParticularWave.ReferenceChart (nativeAssembly x l) h
      (ChartScales.Q (BaseChartJets.cellBand l.2)) (ChartScales.nativeIndex h
          (BaseChartJets.cellBand l.2)) := by
  refine ⟨nativeAssembly_identity x l, ?_, ?_, ?_, ?_⟩
  · rfl
  · funext z
    apply waveEquiv.injective
    change (nativeAssembly x l).directions.radialField (BaseChartJets.cellBand l.2) (waveEquiv z) =
        _
    rw [nativeDirections_radial, nativeAssembly_frame]
    rfl
  · rw [nativeDirections_angular]
    rfl
  · funext z
    apply waveEquiv.injective
    change (nativeAssembly x l).directions.axialField (nativeAssembly x l).strip
      (BaseChartJets.cellBand l.2) (waveEquiv z) = _
    rw [nativeDirections_axial, nativeAssembly_frame]
    rfl

/-! ## Reverse index order and the original recurrence interface -/

theorem ratioPower_reverse_mul {Q Qr : ℝ} (hQ : 0 < Q) (hQr : 0 < Qr) (a : ℝ) :
    ratioPower Q Qr a * ratioPower Qr Q a = 1 := by
  unfold ratioPower
  field_simp [(Real.rpow_pos_of_pos hQ a).ne', (Real.rpow_pos_of_pos hQr a).ne']

theorem parameterChange_inverse (h : ℝ) {Q Qr : ℝ} (hQ : 0 < Q) (hQr : 0 < Qr)
    (p : Parameter) : parameterChange h Qr Q (parameterChange h Q Qr p) = p := by
  ext <;> simp only [parameterChange, ← mul_assoc, ratioPower_reverse_mul hQr hQ, one_mul]

theorem commonReferenceChart_backward (l : ActualParticularStageControls.Label B N0)
    (n k : ℕ) (hi : CommonWindow.index h (BaseChartJets.cellBand l.2) + k = CommonWindow.index h n)
    (hn : CommonWindow.index h n ≤ ChartScales.nativeIndex h (BaseChartJets.cellBand l.2))
    (z : PhysicalResidualNaturality.Associated) :
    GaugeStateCoherence.bandChartEquiv h (BaseChartJets.cellBand l.2) n k
      (CorrectionStep.cycleAssoc.symm (commonReferenceChart l n z)) =
          CorrectionStep.cycleAssoc.symm z := by
  have hg : ActualParticularStageControls.gap l (BaseChartJets.cellBand l.2) =
      ActualParticularStageControls.gap l n + k := by
    unfold ActualParticularStageControls.gap
    omega
  rw [← associatedChart_stateChart]
  apply congrArg CorrectionStep.cycleAssoc.symm
  rw [PhysicalResidualNaturality.associatedChart_apply, commonReferenceChart_apply,
    parameterChange_inverse h (ChartScales.Q_pos n) (ChartScales.Q_pos (BaseChartJets.cellBand
        l.2))]
  apply Prod.ext
  · rfl
  · change coverPower k ((coverPower (ActualParticularStageControls.gap l (BaseChartJets.cellBand
      l.2))).symm
      (coverPower (ActualParticularStageControls.gap l n) z.2)) = z.2
    apply (coverPower (ActualParticularStageControls.gap l n)).injective
    rw [← CopySolveCompatibility.coverPower_add, ← hg, ContinuousLinearEquiv.apply_symm_apply]

/-- State comparison type used in actual reference rebase. -/
abbrev StateComparison (x : CorrectionStep.CycleState (ActualParticularStageControls.Label B N0))
    (V : Set Plane) (n m k : ℕ) : Prop :=
  PhysicalResidualNaturality.StateOn (PhysicalMeanDomain.slowDomain V)
    (GaugeStateCoherence.bandChartEquiv h n m k) (GaugeStateCoherence.bandVelocityScale h n m)
    (GaugeStateCoherence.bandScale n m) x.state x.state n m

/-- Block comparison type used in actual reference rebase. -/
abbrev BlockComparison (x : CorrectionStep.CycleState (ActualParticularStageControls.Label B N0))
    (l : ActualParticularStageControls.Label B N0) (V : Set Plane) (n m k : ℕ) : Prop :=
  PhysicalResidualNaturality.BlockFieldsOn (PhysicalMeanDomain.slowDomain V)
    (GaugeStateCoherence.bandChartEquiv h n m k) (GaugeStateCoherence.bandVelocityScale h n m)
    (GaugeStateCoherence.bandScale n m) (x.coefficients.blocks l) (x.coefficients.blocks l)
    (x.coefficients.gaussian l) (x.coefficients.aliasCoefficients l)
    (x.coefficients.gaussian l) (x.coefficients.aliasCoefficients l) n m

theorem source_backward
    (x : CorrectionStep.CycleState (ActualParticularStageControls.Label B N0))
    (l : ActualParticularStageControls.Label B N0) {V : Set Plane} (hV : IsOpen V)
    (htime : ∀ s ∈ V, 0 < s.1) (n k : ℕ)
    (hi : CommonWindow.index h (BaseChartJets.cellBand l.2) + k = CommonWindow.index h n)
    (hn : CommonWindow.index h n ≤ ChartScales.nativeIndex h (BaseChartJets.cellBand l.2))
    (HS : StateComparison x V (BaseChartJets.cellBand l.2) n k)
    (HB : BlockComparison x l V (BaseChartJets.cellBand l.2) n k)
    (j : ℤ) (z : PhysicalResidualNaturality.Associated)
    (hz : (commonReferenceChart l n z).1.2 ∈ V) :
    ParticularWaveAssembly.residualSource (ActualParticularStageControls.assembly x l).context
      (ActualParticularStageControls.assembly x l).state (ActualParticularStageControls.assembly x
          l).carrierBlock
      (ActualParticularStageControls.assembly x l).gaussianInput
          (ActualParticularStageControls.assembly x l).aliasInput
      j n z = PhysicalParticularWave.transportedResidualSource (nativeAssembly x l) h
          (ChartScales.Q n)
        (ChartScales.Q (BaseChartJets.cellBand l.2)) (ActualParticularStageControls.gap l n) j z :=
            by
  have he := HS.source (ActualInitialCoherence.context_band B htime (BaseChartJets.cellBand l.2) n
      k hi)
    (PhysicalMeanDomain.slowDomain_open hV) (GaugeStateCoherence.bandScale_pos
        (BaseChartJets.cellBand l.2) n).ne'
      HB j (x := CorrectionStep.cycleAssoc.symm (commonReferenceChart l n z)) hz
  rw [state_sourceWeight, commonReferenceChart_backward l n k hi hn] at he
  have he' := congrArg (fun v : ComplexVector =>
    sourceWeight h (ChartScales.Q n) (ChartScales.Q (BaseChartJets.cellBand l.2)) • v) he
  rw [smul_smul, show sourceWeight h (ChartScales.Q n) (ChartScales.Q (BaseChartJets.cellBand l.2))
      *
      sourceWeight h (ChartScales.Q (BaseChartJets.cellBand l.2)) (ChartScales.Q n) = 1 from
        ratioPower_reverse_mul (ChartScales.Q_pos n) (ChartScales.Q_pos (BaseChartJets.cellBand
            l.2)) _, one_smul] at he'
  rw [assembly_source, transportedSource_eq_commonReference]
  exact he'.symm

/-! ## Regularity and support are transported, not postulated anew -/

theorem referenceResidualSource_smooth
    (x : CorrectionStep.CycleState (ActualParticularStageControls.Label B N0))
    (l : ActualParticularStageControls.Label B N0) (j : ℤ) (V : Set Parameter)
    (hf : ContDiffOn ℝ ∞ (ParticularWaveAssembly.residualSource
      (ActualParticularStageControls.assembly x l).context (ActualParticularStageControls.assembly
          x l).state
      (ActualParticularStageControls.assembly x l).carrierBlock
      (ActualParticularStageControls.assembly x l).gaussianInput
          (ActualParticularStageControls.assembly x l).aliasInput
      j (BaseChartJets.cellBand l.2)) (V ×ˢ univ)) :
    ContDiffOn ℝ ∞ (referenceResidualSource x l j) (V ×ˢ univ) :=
  hf.comp (inverseCover (P := Parameter)
    (ActualParticularStageControls.gap l (BaseChartJets.cellBand l.2))).contDiff.contDiffOn
      (fun _ hz => ⟨hz.1, mem_univ _⟩)

theorem referenceResidualSource_support
    (x : CorrectionStep.CycleState (ActualParticularStageControls.Label B N0))
    (l : ActualParticularStageControls.Label B N0) (j : ℤ) :
    support (referenceResidualSource x l j) =
      inverseCover (P := Parameter) (ActualParticularStageControls.gap l (BaseChartJets.cellBand
          l.2)) ⁻¹'
        support (ParticularWaveAssembly.residualSource (ActualParticularStageControls.assembly x
            l).context
          (ActualParticularStageControls.assembly x l).state
              (ActualParticularStageControls.assembly x l).carrierBlock
          (ActualParticularStageControls.assembly x l).gaussianInput
              (ActualParticularStageControls.assembly x l).aliasInput
          j (BaseChartJets.cellBand l.2)) := rfl

/-! ## The unchanged target solve uses this native reference -/

theorem residualBandAmplitude_rebase_at (D : ParticularWaveAssembly.AssemblyData Parameter)
    (h : ℝ) {Q Qr : ℝ} (hQ : 0 < Q) (hQr : 0 < Qr) (kr gap : ℕ)
    (K : ℝ) (j : ℤ) (n : ℕ) (p : Parameter)
    (hf : ∀ Y, ParticularWaveAssembly.residualSource D.context D.state D.carrierBlock
      D.gaussianInput D.aliasInput j n (p, Y) =
        PhysicalParticularWave.transportedResidualSource (rebaseAssembly D kr) h Q Qr gap j (p, Y))
    (Y : Plane) :
    PhysicalParticularWave.residualBandAmplitude D h hQ hQr gap K j n (p,Y) =
      PhysicalParticularWave.bandAmplitude (rebaseAssembly D kr) h hQ hQr gap K j (p,Y) := by
  unfold PhysicalParticularWave.residualBandAmplitude PhysicalParticularWave.bandAmplitude
  apply commonVelocity_source_congr
  exact hf

theorem residualBandPressure_rebase_at (D : ParticularWaveAssembly.AssemblyData Parameter)
    (h : ℝ) {Q Qr : ℝ} (hQ : 0 < Q) (hQr : 0 < Qr) (kr gap : ℕ)
    (K : ℝ) (j : ℤ) (n : ℕ) (p : Parameter)
    (hf : ∀ Y, ParticularWaveAssembly.residualSource D.context D.state D.carrierBlock
      D.gaussianInput D.aliasInput j n (p, Y) =
        PhysicalParticularWave.transportedResidualSource (rebaseAssembly D kr) h Q Qr gap j (p, Y))
    (Y : Plane) :
    PhysicalParticularWave.residualBandPressure D h hQ hQr gap K j n (p,Y) =
      PhysicalParticularWave.bandPressure (rebaseAssembly D kr) h hQ hQr gap K j (p,Y) := by
  unfold PhysicalParticularWave.residualBandPressure PhysicalParticularWave.bandPressure
  apply commonPressure_source_congr
  exact hf

/-- The literal current-source common coefficient in the actual stage. -/
noncomputable def actualCoefficients
    (x : CorrectionStep.CycleState (ActualParticularStageControls.Label B N0))
    (l : ActualParticularStageControls.Label B N0) (j : ℤ) : LinearWaveBounds.WaveCoefficients
        WaveSpace :=
  ((ActualParticularStageControls.parameters x l).copyData
    (ActualParticularStageControls.assembly x l).context (ActualParticularStageControls.assembly x
        l).state
    (ActualParticularStageControls.assembly x l).carrierBlock
    (ActualParticularStageControls.assembly x l).gaussianInput
    (ActualParticularStageControls.assembly x l).aliasInput j).common

theorem actualAmplitude_rebase_at
    (x : CorrectionStep.CycleState (ActualParticularStageControls.Label B N0))
    (l : ActualParticularStageControls.Label B N0) (j : ℤ) (n : ℕ) (p : Parameter)
    (hf : ∀ Y, ParticularWaveAssembly.residualSource (ActualParticularStageControls.assembly x
        l).context
      (ActualParticularStageControls.assembly x l).state (ActualParticularStageControls.assembly x
          l).carrierBlock
      (ActualParticularStageControls.assembly x l).gaussianInput
          (ActualParticularStageControls.assembly x l).aliasInput
      j n (p, Y) = PhysicalParticularWave.transportedResidualSource (nativeAssembly x l) h
          (ChartScales.Q n)
        (ChartScales.Q (BaseChartJets.cellBand l.2)) (ActualParticularStageControls.gap l n) j
            (p, Y))
    (theta : ℝ) (Y : Plane) :
    (actualCoefficients x l j).amplitude n ((p,theta),Y) =
      PhysicalParticularWave.bandAmplitude (nativeAssembly x l) h (ChartScales.Q_pos n)
        (ChartScales.Q_pos (BaseChartJets.cellBand l.2)) (ActualParticularStageControls.gap l n)
        ((j : ℝ) * (x.coefficients.blocks l).frequency n) j (p,Y) := by
  have he := congrFun (CorrectionStep.ParticularParameters.fromReference_amplitude
    (ActualParticularStageControls.assembly x l) h (ActualParticularStageControls.gap l) j n)
        ((p,theta),Y)
  exact he.trans (residualBandAmplitude_rebase_at (ActualParticularStageControls.assembly x l) h
    (ChartScales.Q_pos n) (ChartScales.Q_pos (BaseChartJets.cellBand l.2))
    (ActualParticularStageControls.gap l (BaseChartJets.cellBand l.2))
        (ActualParticularStageControls.gap l n)
    ((j : ℝ) * (x.coefficients.blocks l).frequency n) j n p hf Y)

theorem actualPressure_rebase_at
    (x : CorrectionStep.CycleState (ActualParticularStageControls.Label B N0))
    (l : ActualParticularStageControls.Label B N0) (j : ℤ) (n : ℕ) (p : Parameter)
    (hK : (j : ℝ) * (x.coefficients.blocks l).frequency n ≠ 0)
    (hf : ∀ Y, ParticularWaveAssembly.residualSource (ActualParticularStageControls.assembly x
        l).context
      (ActualParticularStageControls.assembly x l).state (ActualParticularStageControls.assembly x
          l).carrierBlock
      (ActualParticularStageControls.assembly x l).gaussianInput
          (ActualParticularStageControls.assembly x l).aliasInput
      j n (p, Y) = PhysicalParticularWave.transportedResidualSource (nativeAssembly x l) h
          (ChartScales.Q n)
        (ChartScales.Q (BaseChartJets.cellBand l.2)) (ActualParticularStageControls.gap l n) j
            (p, Y))
    (theta : ℝ) (Y : Plane) :
    (actualCoefficients x l j).pressure n ((p,theta),Y) =
      PhysicalParticularWave.bandPressure (nativeAssembly x l) h (ChartScales.Q_pos n)
        (ChartScales.Q_pos (BaseChartJets.cellBand l.2)) (ActualParticularStageControls.gap l n)
        ((j : ℝ) * (x.coefficients.blocks l).frequency n) j (p,Y) := by
  have he := congrFun (CorrectionStep.ParticularParameters.fromReference_pressure
    (ActualParticularStageControls.assembly x l) h (ActualParticularStageControls.gap l) j n hK)
        ((p,theta),Y)
  exact he.trans (residualBandPressure_rebase_at (ActualParticularStageControls.assembly x l) h
    (ChartScales.Q_pos n) (ChartScales.Q_pos (BaseChartJets.cellBand l.2))
    (ActualParticularStageControls.gap l (BaseChartJets.cellBand l.2))
        (ActualParticularStageControls.gap l n)
    ((j : ℝ) * (x.coefficients.blocks l).frequency n) j n p hf Y)

theorem actualAmplitude_forward
    (x : CorrectionStep.CycleState (ActualParticularStageControls.Label B N0))
    (l : ActualParticularStageControls.Label B N0) {V : Set Plane} (hV : IsOpen V)
    (htime : ∀ s ∈ V, 0 < s.1) (n k : ℕ)
    (hi : CommonWindow.index h n + k = CommonWindow.index h (BaseChartJets.cellBand l.2))
    (HS : StateComparison x V n (BaseChartJets.cellBand l.2) k)
    (HB : BlockComparison x l V n (BaseChartJets.cellBand l.2) k)
    (j : ℤ) (p : Parameter) (hp : p.2 ∈ V) (theta : ℝ) (Y : Plane) :
    (actualCoefficients x l j).amplitude n ((p,theta),Y) =
      PhysicalParticularWave.bandAmplitude (nativeAssembly x l) h (ChartScales.Q_pos n)
        (ChartScales.Q_pos (BaseChartJets.cellBand l.2)) (ActualParticularStageControls.gap l n)
        ((j : ℝ) * (x.coefficients.blocks l).frequency n) j (p,Y) :=
  actualAmplitude_rebase_at x l j n p (fun Z => source_forward x l hV htime n k hi HS HB j (p,Z)
      hp) theta Y

theorem actualPressure_forward
    (x : CorrectionStep.CycleState (ActualParticularStageControls.Label B N0))
    (l : ActualParticularStageControls.Label B N0) {V : Set Plane} (hV : IsOpen V)
    (htime : ∀ s ∈ V, 0 < s.1) (n k : ℕ)
    (hi : CommonWindow.index h n + k = CommonWindow.index h (BaseChartJets.cellBand l.2))
    (HS : StateComparison x V n (BaseChartJets.cellBand l.2) k)
    (HB : BlockComparison x l V n (BaseChartJets.cellBand l.2) k)
    (j : ℤ) (hK : (j : ℝ) * (x.coefficients.blocks l).frequency n ≠ 0)
    (p : Parameter) (hp : p.2 ∈ V) (theta : ℝ) (Y : Plane) :
    (actualCoefficients x l j).pressure n ((p,theta),Y) =
      PhysicalParticularWave.bandPressure (nativeAssembly x l) h (ChartScales.Q_pos n)
        (ChartScales.Q_pos (BaseChartJets.cellBand l.2)) (ActualParticularStageControls.gap l n)
        ((j : ℝ) * (x.coefficients.blocks l).frequency n) j (p,Y) :=
  actualPressure_rebase_at x l j n p hK (fun Z => source_forward x l hV htime n k hi HS HB j (p,Z)
      hp) theta Y

theorem actualAmplitude_backward
    (x : CorrectionStep.CycleState (ActualParticularStageControls.Label B N0))
    (l : ActualParticularStageControls.Label B N0) {V : Set Plane} (hV : IsOpen V)
    (htime : ∀ s ∈ V, 0 < s.1) (n k : ℕ)
    (hi : CommonWindow.index h (BaseChartJets.cellBand l.2) + k = CommonWindow.index h n)
    (hn : CommonWindow.index h n ≤ ChartScales.nativeIndex h (BaseChartJets.cellBand l.2))
    (HS : StateComparison x V (BaseChartJets.cellBand l.2) n k)
    (HB : BlockComparison x l V (BaseChartJets.cellBand l.2) n k)
    (j : ℤ) (p : Parameter)
    (hp : (parameterChange h (ChartScales.Q n) (ChartScales.Q (BaseChartJets.cellBand l.2)) p).2 ∈
        V)
    (theta : ℝ) (Y : Plane) :
    (actualCoefficients x l j).amplitude n ((p,theta),Y) =
      PhysicalParticularWave.bandAmplitude (nativeAssembly x l) h (ChartScales.Q_pos n)
        (ChartScales.Q_pos (BaseChartJets.cellBand l.2)) (ActualParticularStageControls.gap l n)
        ((j : ℝ) * (x.coefficients.blocks l).frequency n) j (p,Y) :=
  actualAmplitude_rebase_at x l j n p (fun Z => source_backward x l hV htime n k hi hn HS HB j
      (p,Z) hp) theta Y

theorem actualPressure_backward
    (x : CorrectionStep.CycleState (ActualParticularStageControls.Label B N0))
    (l : ActualParticularStageControls.Label B N0) {V : Set Plane} (hV : IsOpen V)
    (htime : ∀ s ∈ V, 0 < s.1) (n k : ℕ)
    (hi : CommonWindow.index h (BaseChartJets.cellBand l.2) + k = CommonWindow.index h n)
    (hn : CommonWindow.index h n ≤ ChartScales.nativeIndex h (BaseChartJets.cellBand l.2))
    (HS : StateComparison x V (BaseChartJets.cellBand l.2) n k)
    (HB : BlockComparison x l V (BaseChartJets.cellBand l.2) n k)
    (j : ℤ) (hK : (j : ℝ) * (x.coefficients.blocks l).frequency n ≠ 0)
    (p : Parameter)
    (hp : (parameterChange h (ChartScales.Q n) (ChartScales.Q (BaseChartJets.cellBand l.2)) p).2 ∈
        V)
    (theta : ℝ) (Y : Plane) :
    (actualCoefficients x l j).pressure n ((p,theta),Y) =
      PhysicalParticularWave.bandPressure (nativeAssembly x l) h (ChartScales.Q_pos n)
        (ChartScales.Q_pos (BaseChartJets.cellBand l.2)) (ActualParticularStageControls.gap l n)
        ((j : ℝ) * (x.coefficients.blocks l).frequency n) j (p,Y) :=
  actualPressure_rebase_at x l j n p hK (fun Z => source_backward x l hV htime n k hi hn HS HB j
      (p,Z) hp) theta Y

/-! The full carrier uses the same rebase, including the angular integer. -/

theorem carrier_phase_rebase {K Kr J a theta phi psi : ℝ}
    (hK : K ≠ 0) (hKr : Kr ≠ 0) (hJ : J ≠ 0) (hphi : K * phi = Kr * psi) :
    (J * Kr) / (J * K) * (psi + a / Kr * theta) = phi + a / K * theta := by
  have he : (Kr / K) * psi = phi := by
    rw [div_mul_eq_mul_div]
    exact (div_eq_iff hK).2 (by simpa only [mul_comm] using hphi.symm)
  rw [mul_div_mul_left _ _ hJ]
  calc
    _ = (Kr/K)*psi + ((Kr/K)*(a/Kr))*theta := by ring
    _ = phi + (a/K)*theta := by rw [he]; congr 2 ; field_simp

theorem actualPhase_rebase_at
    (x : CorrectionStep.CycleState (ActualParticularStageControls.Label B N0))
    (l : ActualParticularStageControls.Label B N0) (j : ℤ) (hj : j ≠ 0) (n : ℕ)
    (hn : (x.coefficients.blocks l).frequency n ≠ 0)
    (hm : (x.coefficients.blocks l).frequency (BaseChartJets.cellBand l.2) ≠ 0)
    (p : Parameter) (Y : Plane)
    (hp : (x.coefficients.blocks l).frequency n *
        (x.coefficients.blocks l).phase n (CorrectionStep.cycleAssoc.symm (p, Y)) =
      (x.coefficients.blocks l).frequency (BaseChartJets.cellBand l.2) *
        (x.coefficients.blocks l).phase (BaseChartJets.cellBand l.2)
          (CorrectionStep.cycleAssoc.symm (commonReferenceChart l n (p, Y))))
    (ha : (x.coefficients.blocks l).angularFrequency n =
      (x.coefficients.blocks l).angularFrequency (BaseChartJets.cellBand l.2)) (theta : ℝ) :
    PhysicalParticularWave.bandPhase (nativeAssembly x l) h (ChartScales.Q n)
      (ChartScales.Q (BaseChartJets.cellBand l.2)) (ActualParticularStageControls.gap l n)
      ((j : ℝ) * (x.coefficients.blocks l).frequency n) j (waveEquiv.symm ((p,theta),Y)) =
        (actualCoefficients x l j).phase n ((p,theta),Y) := by
  change ((j : ℝ) * (x.coefficients.blocks l).frequency (BaseChartJets.cellBand l.2)) /
      ((j : ℝ) * (x.coefficients.blocks l).frequency n) *
    ((x.coefficients.blocks l).phase (BaseChartJets.cellBand l.2)
        (CorrectionStep.cycleAssoc.symm (commonReferenceChart l n (p,Y))) +
      ((x.coefficients.blocks l).angularFrequency (BaseChartJets.cellBand l.2) : ℝ) /
        (x.coefficients.blocks l).frequency (BaseChartJets.cellBand l.2) * theta) =
    (x.coefficients.blocks l).phase n (CorrectionStep.cycleAssoc.symm (p,Y)) +
      ((x.coefficients.blocks l).angularFrequency n : ℝ) / (x.coefficients.blocks l).frequency n *
          theta
  rw [ha]
  exact carrier_phase_rebase hn hm (by exact_mod_cast hj) hp

theorem actualPhase_forward
    (x : CorrectionStep.CycleState (ActualParticularStageControls.Label B N0))
    (l : ActualParticularStageControls.Label B N0) (V : Set Plane) (n k : ℕ)
    (hi : CommonWindow.index h n + k = CommonWindow.index h (BaseChartJets.cellBand l.2))
    (HB : BlockComparison x l V n (BaseChartJets.cellBand l.2) k)
    (j : ℤ) (hj : j ≠ 0) (hn : (x.coefficients.blocks l).frequency n ≠ 0)
    (hm : (x.coefficients.blocks l).frequency (BaseChartJets.cellBand l.2) ≠ 0)
    (p : Parameter) (hp : p.2 ∈ V) (theta : ℝ) (Y : Plane) :
    PhysicalParticularWave.bandPhase (nativeAssembly x l) h (ChartScales.Q n)
      (ChartScales.Q (BaseChartJets.cellBand l.2)) (ActualParticularStageControls.gap l n)
      ((j : ℝ) * (x.coefficients.blocks l).frequency n) j (waveEquiv.symm ((p,theta),Y)) =
        (actualCoefficients x l j).phase n ((p,theta),Y) := by
  apply actualPhase_rebase_at x l j hj n hn hm p Y _ HB.angular theta
  rw [commonReferenceChart_forward l n k hi]
  exact HB.phase (x := CorrectionStep.cycleAssoc.symm (p,Y)) hp

theorem actualPhase_backward
    (x : CorrectionStep.CycleState (ActualParticularStageControls.Label B N0))
    (l : ActualParticularStageControls.Label B N0) (V : Set Plane) (n k : ℕ)
    (hi : CommonWindow.index h (BaseChartJets.cellBand l.2) + k = CommonWindow.index h n)
    (hcover : CommonWindow.index h n ≤ ChartScales.nativeIndex h (BaseChartJets.cellBand l.2))
    (HB : BlockComparison x l V (BaseChartJets.cellBand l.2) n k)
    (j : ℤ) (hj : j ≠ 0) (hn : (x.coefficients.blocks l).frequency n ≠ 0)
    (hm : (x.coefficients.blocks l).frequency (BaseChartJets.cellBand l.2) ≠ 0)
    (p : Parameter)
    (hp : (parameterChange h (ChartScales.Q n) (ChartScales.Q (BaseChartJets.cellBand l.2)) p).2 ∈
        V)
    (theta : ℝ) (Y : Plane) :
    PhysicalParticularWave.bandPhase (nativeAssembly x l) h (ChartScales.Q n)
      (ChartScales.Q (BaseChartJets.cellBand l.2)) (ActualParticularStageControls.gap l n)
      ((j : ℝ) * (x.coefficients.blocks l).frequency n) j (waveEquiv.symm ((p,theta),Y)) =
        (actualCoefficients x l j).phase n ((p,theta),Y) := by
  apply actualPhase_rebase_at x l j hj n hn hm p Y _ HB.angular.symm theta
  have he := HB.phase (x := CorrectionStep.cycleAssoc.symm (commonReferenceChart l n (p,Y))) hp
  dsimp only at he
  rw [commonReferenceChart_backward l n k hi hcover] at he
  exact he.symm

/-! Precisely the inherited lattice is retained. -/

theorem referenceResidualSource_subcoverPeriodic
    (x : CorrectionStep.CycleState (ActualParticularStageControls.Label B N0))
    (l : ActualParticularStageControls.Label B N0) (j : ℤ) (p : Parameter)
    (hf : PeriodicAt (ParticularWaveAssembly.residualSource (ActualParticularStageControls.assembly
        x l).context
      (ActualParticularStageControls.assembly x l).state (ActualParticularStageControls.assembly x
          l).carrierBlock
      (ActualParticularStageControls.assembly x l).gaussianInput
          (ActualParticularStageControls.assembly x l).aliasInput
      j (BaseChartJets.cellBand l.2)) p) :
    SubcoverPeriodicity.SubcoverPeriodicAt
      (ActualParticularStageControls.gap l (BaseChartJets.cellBand l.2)) (referenceResidualSource x
          l j) p :=
  SubcoverPeriodicity.inverseCoverSource_subcoverPeriodic _ _ p hf

theorem nativeRaw_subcoverPeriodic
    (x : CorrectionStep.CycleState (ActualParticularStageControls.Label B N0))
    (l : ActualParticularStageControls.Label B N0) (j : ℤ) (p : Parameter)
    (hf : PeriodicAt (ParticularWaveAssembly.residualSource (ActualParticularStageControls.assembly
        x l).context
      (ActualParticularStageControls.assembly x l).state (ActualParticularStageControls.assembly x
          l).carrierBlock
      (ActualParticularStageControls.assembly x l).gaussianInput
          (ActualParticularStageControls.assembly x l).aliasInput
      j (BaseChartJets.cellBand l.2)) p) :
    SubcoverPeriodicity.SubcoverPeriodicAt
      (ActualParticularStageControls.gap l (BaseChartJets.cellBand l.2))
      (ParticularWaveBounds.commonVelocity ((ActualParticularStageControls.reference l).tangent j)
        (referenceResidualSource x l j) (ActualParticularStageControls.reference l).geometry
        (ActualParticularStageControls.reference l).length_pos.le
            (ActualParticularStageControls.reference l).cutoff) p :=
  SubcoverPeriodicity.commonVelocity_subcoverPeriodic _ _ _ _ _ _ p
    (referenceResidualSource_subcoverPeriodic x l j p hf)

theorem nativePressure_subcoverPeriodic
    (x : CorrectionStep.CycleState (ActualParticularStageControls.Label B N0))
    (l : ActualParticularStageControls.Label B N0) (j : ℤ) (p : Parameter)
    (hf : PeriodicAt (ParticularWaveAssembly.residualSource (ActualParticularStageControls.assembly
        x l).context
      (ActualParticularStageControls.assembly x l).state (ActualParticularStageControls.assembly x
          l).carrierBlock
      (ActualParticularStageControls.assembly x l).gaussianInput
          (ActualParticularStageControls.assembly x l).aliasInput
      j (BaseChartJets.cellBand l.2)) p) :
    SubcoverPeriodicity.SubcoverPeriodicAt
      (ActualParticularStageControls.gap l (BaseChartJets.cellBand l.2))
      (ParticularWaveBounds.commonPressure ((ActualParticularStageControls.reference l).tangent j)
        (referenceResidualSource x l j) (ActualParticularStageControls.reference l).geometry
        (ActualParticularStageControls.reference l).length_pos.le
            (ActualParticularStageControls.reference l).cutoff
        (PhysicalParticularWave.referenceFrequency (nativeAssembly x l) j)) p :=
  SubcoverPeriodicity.commonPressure_subcoverPeriodic _ _ _ _ _ _ _ p
    (referenceResidualSource_subcoverPeriodic x l j p hf)

end NavierStokes.ActualReferenceRebase
