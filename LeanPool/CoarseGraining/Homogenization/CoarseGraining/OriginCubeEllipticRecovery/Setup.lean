/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.CoarseGraining.BlockResponse.Equalities
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MagicIdentities
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MuRecoveryBlockResponse
import LeanPool.CoarseGraining.Homogenization.Deterministic.MultiscaleQuantitiesBasic.Response
import LeanPool.CoarseGraining.Homogenization.Geometry.CubeMeasure

/-!
# Origin-cube elliptic recovery -- volume lemmas, data package, descendant family

Basic volume-of-centered-cube lemmas, the HasOpenCubeEllipticRecoveryData
package, the canonical instance from an elliptic field, and the descendant
recovery family used downstream.
-/

namespace Homogenization

/--
The centered open cube has finite Lebesgue measure.

This is the finite-volume input needed to instantiate the `L²` and recovery
machinery on `openCubeSet (originCube d n)`.
-/
theorem volume_openCubeSet_originCube_lt_top {d : ℕ} (n : ℤ) :
    MeasureTheory.volume (openCubeSet (originCube d n)) < ⊤ := by
  rw [lt_top_iff_ne_top]
  intro htop
  have hzero : (MeasureTheory.volume (openCubeSet (originCube d n))).toReal = 0 := by
    simp [htop]
  rw [volume_openCubeSet_toReal] at hzero
  exact (ne_of_gt (cubeVolume_pos (originCube d n))) hzero

/--
The centered open cube has strictly positive Lebesgue volume.

This is the normalization hypothesis required by the deterministic doubled
operator construction from ellipticity.
-/
theorem volume_openCubeSet_originCube_toReal_pos {d : ℕ} (n : ℤ) :
    0 < (MeasureTheory.volume (openCubeSet (originCube d n))).toReal := by
  rw [volume_openCubeSet_toReal]
  exact cubeVolume_pos (originCube d n)

/-- Integer translation shift identifying a nonnegative-scale triadic cube
with the corresponding translated origin cube. -/
def originCubeScaleTranslationShift {d : ℕ} (k : ℤ) (Q : TriadicCube d) : Fin d → ℤ :=
  fun i => Int.ofNat (3 ^ Int.toNat k) * Q.index i

/--
Package the deterministic hypotheses that upgrade raw ellipticity on the
centered open cube to the compatibility data needed by the `Mu` recovery
machinery.

The recovery space `R` is fixed once and for all on the domain
`openCubeSet (originCube d n)`. For a given coefficient field `a`, this
predicate asks for:
1. an ellipticity witness for `a` on that domain;
2. the compatibility data identifying the note's `Mu` with the Hilbert-space
   minimization problem built from that ellipticity witness.
-/
def HasOpenCubeEllipticRecoveryData {d : ℕ} (n : ℤ)
    (R : PotentialSolenoidalL2RecoveryData (openCubeSet (originCube d n)))
    {lam Lam : ℝ} (a : CoeffField d) : Prop := by
  let U : Set (Vec d) := openCubeSet (originCube d n)
  letI : Fact (MeasureTheory.volume U < ⊤) :=
    ⟨volume_openCubeSet_originCube_lt_top (d := d) n⟩
  exact
    ∃ hEll : IsEllipticFieldOn lam Lam U a,
      PotentialSolenoidalL2RecoveryData.MuRecoveryCompatibilityData (a := a) R
        (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll
          (volume_openCubeSet_originCube_toReal_pos (d := d) n))

/-- Build the origin-cube recovery package from ellipticity and the single
remaining hard compatibility field `Mu = muCandidate`.

The pairing-integrability part of `HasOpenCubeEllipticRecoveryData` is already
automatic from ellipticity and the `L²` control of recovered fields. -/
theorem hasOpenCubeEllipticRecoveryData_of_isEllipticFieldOn_of_mu_eq_muCandidate
    {d : ℕ} (n : ℤ)
    (R : PotentialSolenoidalL2RecoveryData (openCubeSet (originCube d n)))
    {lam Lam : ℝ} {a : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet (originCube d n)) a)
    (mu_eq_muCandidate :
      ∀ P : BlockVec d,
        Mu (openCubeSet (originCube d n)) P a =
          ((R.toMuHilbertRealization
            (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll
              (volume_openCubeSet_originCube_toReal_pos (d := d) n))).muCandidate P)) :
    HasOpenCubeEllipticRecoveryData (d := d) n R
      (lam := lam) (Lam := Lam) a := by
  exact ⟨hEll,
    R.muRecoveryCompatibilityData_of_isEllipticFieldOn_of_mu_eq_muCandidate
      hEll (volume_openCubeSet_originCube_toReal_pos (d := d) n) mu_eq_muCandidate⟩

/--
Descendant-family version of `HasOpenCubeEllipticRecoveryData`.

This packages the translated origin-cube recovery input on every descendant of
the parent cube `Q`. It is the natural upstream hypothesis for producing the
deterministic Chapter-2 coarse data needed by the top Chapter-3 coarse
Poincare wrappers.
-/
def OpenCubeDescendantEllipticRecoveryFamily {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) {lam Lam : ℝ} : Prop :=
  ∀ l ≤ Q.scale, ∀ R ∈ descendantsAtScale Q l,
    ∃ RR : PotentialSolenoidalL2RecoveryData (openCubeSet (originCube d R.scale)),
      HasOpenCubeEllipticRecoveryData (d := d) R.scale RR
        (lam := lam) (Lam := Lam)
        (translateCoeffField (fun i => (R.index i : ℝ) * cubeScaleFactor R) a)

end Homogenization
