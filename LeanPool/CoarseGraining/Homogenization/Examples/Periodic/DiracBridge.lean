/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.MainResults
public import LeanPool.CoarseGraining.Homogenization.Deterministic.HomogenizationBlackBoxes.Duality
public import LeanPool.CoarseGraining.Homogenization.Probability.RegCoeffField.EllipticSupport

/-!
# Dirac-law bridge for deterministic periodic examples

**Shared foundation.** Builds the periodic stochastic `Setup` from a deterministic
coefficient field (`periodicSetup`), the engine consumed by all three periodic
comparators (`PeriodicGeneralComparison`, `PeriodicConcreteComparison`,
`PeriodicSmoothComparison`).  See `Audit/README.md` for the comparator map.

Following the carrier redesign, the deterministic field is carried as an honest
`RegCoeffField d` (a constant/periodic smooth field is trivially entrywise
measurable and locally integrable), and the law is the Dirac point mass on the
carrier.  The pushforward invariance fields of the stochastic setup reduce to
pointwise invariance of the deterministic coefficient field through the carrier
endomorphisms (`Measure.map_dirac'`); unit-range dependence is formal because
`RestrictionSigmaR` events are *genuinely* measurable on the carrier; and the
uniform-ellipticity support event is the genuinely measurable fixed-constant
event of `RegCoeffField/EllipticSupport.lean`.
-/

@[expose] public section

namespace Homogenization
namespace Examples
namespace Periodic

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- The deterministic law concentrated at a carrier coefficient field. -/
abbrev diracCoeffLaw {d : ℕ} (a₀ : RegCoeffField d) : Book.Ch04.RestrictionCoeffLaw d :=
  Measure.dirac a₀

/-- Integer-periodicity of a deterministic coefficient field. -/
def IsPeriodicCoeffField {d : ℕ} (a₀ : CoeffField d) : Prop :=
  ∀ z : Fin d → ℤ, translateByInt z a₀ = a₀

/-- Signed-permutation invariance of a deterministic coefficient field. -/
def IsIsotropicCoeffField {d : ℕ} (a₀ : CoeffField d) : Prop :=
  ∀ R : Mat d, IsSignedPermutationMatrix R → rotateCoeffField R a₀ = a₀

/-- Adjoint invariance of a deterministic coefficient field. -/
def IsAdjointInvariantCoeffField {d : ℕ} (a₀ : CoeffField d) : Prop :=
  adjointCoeffField a₀ = a₀

/-- Pointwise periodicity lifts to the carrier translation endomorphism. -/
theorem translateReg_eq_self_of_periodic {d : ℕ} {a₀ : RegCoeffField d}
    (hper : IsPeriodicCoeffField a₀.toFun) (z : Fin d → ℤ) :
    translateReg (intVecToRealVec z) a₀ = a₀ := by
  apply RegCoeffField.ext
  intro x
  have h := congrFun (hper z) x
  simpa [translateByInt, translateCoeffField, intVecToRealVec] using! h

/-- Pointwise signed-permutation invariance lifts to the carrier rotation
endomorphism. -/
theorem rotateReg_eq_self_of_isotropic {d : ℕ} {a₀ : RegCoeffField d}
    (hiso : IsIsotropicCoeffField a₀.toFun) {R : Mat d}
    (hR : IsSignedPermutationMatrix R) :
    rotateReg R hR a₀ = a₀ := by
  apply RegCoeffField.ext
  intro x
  have h := congrFun (hiso R hR) x
  simpa [rotateCoeffField] using h

/-- Pointwise adjoint invariance lifts to the carrier adjoint endomorphism. -/
theorem adjointReg_eq_self_of_adjointInvariant {d : ℕ} {a₀ : RegCoeffField d}
    (hadj : IsAdjointInvariantCoeffField a₀.toFun) :
    adjointReg a₀ = a₀ := by
  apply RegCoeffField.ext
  intro x
  have h := congrFun hadj x
  simpa [adjointCoeffField, matTranspose] using h

/-- Pointwise periodicity gives stationarity of the Dirac law. -/
theorem dirac_stationary {d : ℕ} {a₀ : RegCoeffField d}
    (hper : IsPeriodicCoeffField a₀.toFun) :
    Book.Ch04.RestrictionStationaryLaw (diracCoeffLaw a₀) := by
  intro z
  rw [diracCoeffLaw, Measure.map_dirac' (measurable_translateReg (intVecToRealVec z)),
    translateReg_eq_self_of_periodic hper z]

/-- Pointwise signed-permutation invariance gives isotropy of the Dirac law. -/
theorem dirac_isotropic {d : ℕ} {a₀ : RegCoeffField d}
    (hiso : IsIsotropicCoeffField a₀.toFun) :
    Book.Ch04.RestrictionIsotropicLaw (diracCoeffLaw a₀) := by
  intro R hR
  rw [diracCoeffLaw, Measure.map_dirac' (measurable_rotateReg R hR),
    rotateReg_eq_self_of_isotropic hiso hR]

/-- Pointwise adjoint invariance gives adjoint invariance of the Dirac law. -/
theorem dirac_adjointInvariant {d : ℕ} {a₀ : RegCoeffField d}
    (hadj : IsAdjointInvariantCoeffField a₀.toFun) :
    Book.Ch04.RestrictionAdjointInvariantLaw (diracCoeffLaw a₀) := by
  show Measure.map adjointReg (Measure.dirac a₀) = Measure.dirac a₀
  rw [Measure.map_dirac' measurable_adjointReg,
    adjointReg_eq_self_of_adjointInvariant hadj]

/-- **Restriction-unit-range dependence of a deterministic Dirac law is
automatic**, and on the carrier it is *genuine*: `RestrictionSigmaR` events are
genuinely measurable, so the Dirac law evaluates them by membership. -/
theorem dirac_restrictionUnitRangeDependent {d : ℕ} (a₀ : RegCoeffField d) :
    Book.Ch04.RestrictionUnitRangeDependentLaw (diracCoeffLaw a₀) := by
  intro U V hU hV _hsep
  rw [ProbabilityTheory.Indep_iff]
  intro s t hs ht
  have hs' : MeasurableSet s := restrictionSigmaR_le U hU s hs
  have ht' : MeasurableSet t := restrictionSigmaR_le V hV t ht
  rw [Measure.dirac_apply' _ (hs'.inter ht'), Measure.dirac_apply' _ hs',
    Measure.dirac_apply' _ ht']
  by_cases hsa : a₀ ∈ s <;> by_cases hta : a₀ ∈ t <;>
    simp [hsa, hta]

/-- Uniform ellipticity for the deterministic field gives the law-level uniform
ellipticity statement for the Dirac law, through the genuinely measurable
fixed-constant support event. -/
theorem dirac_uniformEllipticityBounds {d : ℕ}
    {a₀ : RegCoeffField d} {lam Lam : ℝ}
    (hlam : 0 < lam) (hle : lam ≤ Lam)
    (hell : ∀ Q : TriadicCube d,
      Book.Ch04.AEEllipticOn lam Lam (openCubeSet Q) a₀) :
    Book.MainResults.UniformEllipticityBounds (diracCoeffLaw a₀) lam Lam where
  lam_pos := hlam
  lam_le_Lam := hle
  aee_elliptic := by
    refine (MeasureTheory.ae_dirac_iff ?_).2 hell
    exact measurableSet_forall_openCubeSet_isAEEllipticFieldOn lam Lam

/-- The law-carrier part of the Dirac bridge follows from law-level uniform
ellipticity support. -/
theorem dirac_lawCarrier {d : ℕ} {a₀ : RegCoeffField d} {lam Lam : ℝ}
    (hUE : Book.MainResults.UniformEllipticityBounds (diracCoeffLaw a₀) lam Lam) :
    Book.Ch04.RestrictionLawCarrier (diracCoeffLaw a₀) :=
  Book.Ch04.lawCarrier_of_aeLocallyUniformlyElliptic
    hUE.toAELocallyUniformlyEllipticLaw

/--
The structural-law part of the Dirac bridge.  Stationarity, isotropy, and
adjoint invariance reduce to pointwise deterministic invariance, while
restriction-unit-range dependence is automatic for a Dirac law.
-/
theorem dirac_structuralLaw {d : ℕ} {a₀ : RegCoeffField d}
    (hper : IsPeriodicCoeffField a₀.toFun)
    (hiso : IsIsotropicCoeffField a₀.toFun)
    (hadj : IsAdjointInvariantCoeffField a₀.toFun) :
    Book.Ch04.RestrictionStructuralLaw (diracCoeffLaw a₀) where
  stationary := dirac_stationary hper
  unit_range := dirac_restrictionUnitRangeDependent a₀
  isotropic := dirac_isotropic hiso
  adjoint_invariant := dirac_adjointInvariant hadj

/-- Assemble a `MainResults.Setup` from a deterministic carrier field. -/
def dirac_setup {d : ℕ} [NeZero d]
    (two_le_dim : 2 ≤ d) (a₀ : RegCoeffField d) (lam Lam : ℝ)
    (hper : IsPeriodicCoeffField a₀.toFun)
    (hiso : IsIsotropicCoeffField a₀.toFun)
    (hadj : IsAdjointInvariantCoeffField a₀.toFun)
    (hlam : 0 < lam) (hle : lam ≤ Lam)
    (hell : ∀ Q : TriadicCube d,
      Book.Ch04.AEEllipticOn lam Lam (openCubeSet Q) a₀) :
    Book.MainResults.Setup d where
  two_le_dim := two_le_dim
  P := diracCoeffLaw a₀
  hP := dirac_lawCarrier
    (dirac_uniformEllipticityBounds (a₀ := a₀) hlam hle hell)
  hStruct := dirac_structuralLaw hper hiso hadj
  lam := lam
  Lam := Lam
  hUE := dirac_uniformEllipticityBounds (a₀ := a₀) hlam hle hell

/-- Public periodic deterministic setup constructor. -/
def periodicSetup {d : ℕ} [NeZero d]
    (two_le_dim : 2 ≤ d) (a₀ : RegCoeffField d) (lam Lam : ℝ)
    (hper : IsPeriodicCoeffField a₀.toFun)
    (hiso : IsIsotropicCoeffField a₀.toFun)
    (hadj : IsAdjointInvariantCoeffField a₀.toFun)
    (hlam : 0 < lam) (hle : lam ≤ Lam)
    (hell : ∀ Q : TriadicCube d,
      Book.Ch04.AEEllipticOn lam Lam (openCubeSet Q) a₀) :
    Book.MainResults.Setup d :=
  dirac_setup two_le_dim a₀ lam Lam hper hiso hadj hlam hle hell

/-! ## A concrete constant scalar periodic witness -/

/-- The constant scalar coefficient field `x ↦ σ I` (raw sample). -/
abbrev constantScalarCoeffField {d : ℕ} (σ : ℝ) : CoeffField d :=
  constantCoeffField (scalarMatrix (d := d) σ)

/-- The constant scalar coefficient field as a carrier element. -/
abbrev constantScalarRegField {d : ℕ} (σ : ℝ) : RegCoeffField d :=
  RegCoeffField.constRegCoeffField (scalarMatrix (d := d) σ)

@[simp] theorem constantScalarRegField_toFun {d : ℕ} (σ : ℝ) :
    (constantScalarRegField (d := d) σ).toFun = constantScalarCoeffField σ := rfl

/-- Constant scalar fields are integer-periodic. -/
theorem constantScalarCoeffField_periodic {d : ℕ} (σ : ℝ) :
    IsPeriodicCoeffField (constantScalarCoeffField (d := d) σ) := by
  intro z
  ext x i j
  simp [constantScalarCoeffField, constantCoeffField, translateByInt, translateCoeffField]

/-- Rotating a constant scalar field by a signed permutation leaves it unchanged. -/
theorem constantScalarCoeffField_isotropic {d : ℕ} (σ : ℝ) :
    IsIsotropicCoeffField (constantScalarCoeffField (d := d) σ) := by
  intro R hR
  ext x i j
  simp [constantScalarCoeffField, constantCoeffField, rotateCoeffField, scalarMatrix,
    hR.transpose_mul_self]

/-- Constant scalar fields are adjoint-invariant. -/
theorem constantScalarCoeffField_adjointInvariant {d : ℕ} (σ : ℝ) :
    IsAdjointInvariantCoeffField (constantScalarCoeffField (d := d) σ) := by
  ext x i j
  by_cases hij : i = j
  · subst j
    simp [constantScalarCoeffField, constantCoeffField, adjointCoeffField,
      matTranspose, scalarMatrix]
  · have hji : j ≠ i := Ne.symm hij
    simp [constantScalarCoeffField, constantCoeffField, adjointCoeffField,
      matTranspose, scalarMatrix, hij, hji]

/-- A positive constant scalar field is a.e. elliptic on every measurable set. -/
theorem constantScalarRegField_aeeEllipticOn {d : ℕ} {U : Set (Vec d)} {σ : ℝ}
    (hU : MeasurableSet U) (hσ : 0 < σ) :
    Book.Ch04.AEEllipticOn σ σ U (constantScalarRegField (d := d) σ) := by
  exact IsAEEllipticFieldOn.of_isEllipticFieldOn
    (isEllipticFieldOn_constantCoeffField hU (isEllipticMatrix_scalarMatrix hσ))

/--
Concrete non-vacuity witness for the public main-theorem setup: the Dirac law
concentrated on the constant scalar coefficient field `x ↦ σ I`.
-/
def constantScalarPeriodicSetup {d : ℕ} [NeZero d]
    (two_le_dim : 2 ≤ d) {σ : ℝ} (hσ : 0 < σ) :
    Book.MainResults.Setup d :=
  periodicSetup two_le_dim (constantScalarRegField (d := d) σ) σ σ
    (constantScalarCoeffField_periodic σ)
    (constantScalarCoeffField_isotropic σ)
    (constantScalarCoeffField_adjointInvariant σ)
    hσ le_rfl
    (fun Q => constantScalarRegField_aeeEllipticOn (measurableSet_openCubeSet Q) hσ)

end

end Periodic
end Examples
end Homogenization
