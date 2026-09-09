/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ParticularWaveBounds

@[expose] public section

/-!
# A single deck shift of the actual particular solve

Only invariance under the specified lattice vector is assumed.  Equality of
the actual anchored coefficient and forcing paths gives equality of the
Volterra solves, and a bijective copy reindexing gives the same symmetry of
the periodized velocity and pressure.
-/

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

theorem anchoredSolve_shift (d : LinearData P V E) (g : Geometry)
    {a b : ℝ} (hab : a ≤ b) (j K : Frequency) (p : P)
    (hf : ∀ Y : Plane, d.source (p, Y + TorusAverages.latticePoint K) = d.source (p,Y))
    (Y : Plane) (s : ℝ) :
    d.anchoredSolve g hab (j + coverIndex g.gap K) (p, Y + TorusAverages.latticePoint K) s =
      d.anchoredSolve g hab j (p,Y) s := by
  unfold LinearData.anchoredSolve
  rw [d.coefficientPath_deck, forcingPath_shift d g j K p hf]

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

theorem copyVelocity_shift (t : TangentData P ProblemStatement.Space) (g : Geometry)
    {a b : ℝ} (hab : a ≤ b) (j K : Frequency) (p : P)
    (hf : ∀ Y : Plane, t.source (p, Y + TorusAverages.latticePoint K) = t.source (p,Y))
    (Y : Plane) :
    copyVelocity t g hab (j + coverIndex g.gap K) (p, Y + TorusAverages.latticePoint K) =
      copyVelocity t g hab j (p,Y) := by
  unfold copyVelocity
  rw [copySolve_shift t.linearData g hab j K p hf]

theorem copyPressure_shift (t : TangentData P ProblemStatement.Space) (g : Geometry)
    {a b : ℝ} (hab : a ≤ b) (j K : Frequency) (frequency : ℝ) (p : P)
    (hf : ∀ Y : Plane, t.source (p, Y + TorusAverages.latticePoint K) = t.source (p,Y))
    (Y : Plane) :
    copyPressure t g hab (j + coverIndex g.gap K) frequency (p, Y + TorusAverages.latticePoint K) =
      copyPressure t g hab j frequency (p,Y) := by
  simp only [copyPressure, copyPressureReal, nativePoint, g.coordinates_deck,
    copySolve_shift t.linearData g hab j K p hf Y, hf Y]

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

theorem complexCopyVelocity_shift_of_gap_zero (t : TangentData P ProblemStatement.Space)
    (f : P × Plane → ComplexVector) (g : Geometry) (hg : g.gap = 0)
    {a b : ℝ} (hab : a ≤ b) (j K : Frequency) (p : P)
    (hf : ∀ Y : Plane, f (p, Y + TorusAverages.latticePoint K) = f (p,Y)) (Y : Plane) :
    complexCopyVelocity t f g hab (j + K) (p, Y + TorusAverages.latticePoint K) =
      complexCopyVelocity t f g hab j (p,Y) := by
  simpa only [hg, coverIndex, Function.iterate_zero, id_eq] using
    complexCopyVelocity_shift t f g hab j K p hf Y

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
    (hF : ∀ j Y, F (j + coverIndex g.gap K) (p, Y + TorusAverages.latticePoint K) = F j (p,Y))
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

theorem commonVelocity_shift (t : TangentData P ProblemStatement.Space)
    (f : P × Plane → ComplexVector) (g : Geometry) {a b : ℝ} (hab : a ≤ b)
    (κ : Plane → ℝ) (K : Frequency) (p : P)
    (hf : ∀ Y : Plane, f (p, Y + TorusAverages.latticePoint K) = f (p,Y)) (Y : Plane) :
    commonVelocity t f g hab κ (p, Y + TorusAverages.latticePoint K) =
      commonVelocity t f g hab κ (p,Y) :=
  periodizedCopies_shift g κ _ K p (fun j Y => complexCopyVelocity_shift t f g hab j K p hf Y) Y

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

theorem commonVelocity_subcover_shift (t : TangentData P ProblemStatement.Space)
    (f : P × Plane → ComplexVector) (g : Geometry) {a b : ℝ} (hab : a ≤ b)
    (κ : Plane → ℝ) (d : ℕ) (k : Frequency) (p : P)
    (hf : ∀ Y : Plane,
      f (p, Y + TorusAverages.latticePoint (coverIndex d k)) = f (p,Y)) (Y : Plane) :
    commonVelocity t f g hab κ (p, Y + TorusAverages.latticePoint (coverIndex d k)) =
      commonVelocity t f g hab κ (p,Y) :=
  commonVelocity_shift t f g hab κ (coverIndex d k) p hf Y

theorem commonPressure_subcover_shift (t : TangentData P ProblemStatement.Space)
    (f : P × Plane → ComplexVector) (g : Geometry) {a b : ℝ} (hab : a ≤ b)
    (κ : Plane → ℝ) (frequency : ℝ) (d : ℕ) (k : Frequency) (p : P)
    (hf : ∀ Y : Plane,
      f (p, Y + TorusAverages.latticePoint (coverIndex d k)) = f (p,Y)) (Y : Plane) :
    commonPressure t f g hab κ frequency (p, Y + TorusAverages.latticePoint (coverIndex d k)) =
      commonPressure t f g hab κ frequency (p,Y) :=
  commonPressure_shift t f g hab κ frequency (coverIndex d k) p hf Y

theorem commonVelocity_subcoverPeriodic (t : TangentData P ProblemStatement.Space)
    (f : P × Plane → ComplexVector) (g : Geometry) {a b : ℝ} (hab : a ≤ b)
    (κ : Plane → ℝ) (d : ℕ) (p : P) (hf : SubcoverPeriodicAt d f p) :
    SubcoverPeriodicAt d (commonVelocity t f g hab κ) p :=
  fun Y k => commonVelocity_subcover_shift t f g hab κ d k p (fun Z => hf Z k) Y

theorem commonPressure_subcoverPeriodic (t : TangentData P ProblemStatement.Space)
    (f : P × Plane → ComplexVector) (g : Geometry) {a b : ℝ} (hab : a ≤ b)
    (κ : Plane → ℝ) (frequency : ℝ) (d : ℕ) (p : P) (hf : SubcoverPeriodicAt d f p) :
    SubcoverPeriodicAt d (commonPressure t f g hab κ frequency) p :=
  fun Y k => commonPressure_subcover_shift t f g hab κ frequency d k p (fun Z => hf Z k) Y

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
