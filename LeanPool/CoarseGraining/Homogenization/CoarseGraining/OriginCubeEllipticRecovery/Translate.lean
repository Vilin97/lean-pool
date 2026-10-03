/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.OriginCubeEllipticRecovery.QuadraticMu

/-!
# Origin-cube elliptic recovery -- translated and descendant variants

Quadraticity / coarse-block-matrix existence on translateSet variants of the
centered open cube and on openCubeSet / cubeSet of an arbitrary TriadicCube,
produced by transporting recovery data through translations.
-/

@[expose] public section

namespace Homogenization


/--
Translate origin-cube elliptic recovery data for the shifted field
`translateCoeffField z a` into quadraticity of `Mu` on the translated open
cube.
-/
theorem hasQuadraticMu_translateSet_openCubeSet_originCube_of_hasOpenCubeEllipticRecoveryData
    {d : ℕ} {n : ℤ} (z : Vec d)
    (R : PotentialSolenoidalL2RecoveryData (openCubeSet (originCube d n)))
    {lam Lam : ℝ} {a : CoeffField d}
    (hData :
      HasOpenCubeEllipticRecoveryData (d := d) n R
        (lam := lam) (Lam := Lam) (translateCoeffField z a)) :
    HasQuadraticMu (translateSet z (openCubeSet (originCube d n))) a := by
  exact
    (hasQuadraticMu_translateSet_iff z (openCubeSet (originCube d n)) a).2
      (hasQuadraticMu_openCubeSet_originCube_of_hasOpenCubeEllipticRecoveryData
        (R := R) (lam := lam) (Lam := Lam)
        (a := translateCoeffField z a) hData)

/--
Translate origin-cube elliptic recovery data for the shifted field
`translateCoeffField z a` into existence of the coarse block matrix on the
translated open cube.
-/
theorem exists_coarseBlockMatrix_translateSet_openCubeSet_originCube_of_hasOpenCubeEllipticRecoveryData
    {d : ℕ} {n : ℤ} (z : Vec d)
    (R : PotentialSolenoidalL2RecoveryData (openCubeSet (originCube d n)))
    {lam Lam : ℝ} {a : CoeffField d}
    (hData :
      HasOpenCubeEllipticRecoveryData (d := d) n R
        (lam := lam) (Lam := Lam) (translateCoeffField z a)) :
    ∃ Abar : BlockMat d,
      IsCoarseBlockMatrix (translateSet z (openCubeSet (originCube d n))) a Abar := by
  rcases
      exists_coarseBlockMatrix_openCubeSet_originCube_of_hasOpenCubeEllipticRecoveryData
        (R := R) (lam := lam) (Lam := Lam)
        (a := translateCoeffField z a) hData with
    ⟨Abar, hA⟩
  refine ⟨Abar, ?_⟩
  exact (isCoarseBlockMatrix_translateSet_iff z (openCubeSet (originCube d n)) a Abar).2 hA

/-- A nonnegative-scale triadic open cube is an integer translate of the
origin open cube at the same scale. -/
theorem openCubeSet_eq_translateSet_originCube_of_nonneg_scale {d : ℕ}
    {Q : TriadicCube d} (hQ : 0 ≤ Q.scale) :
    openCubeSet Q =
      translateSet (intVecToRealVec (originCubeScaleTranslationShift Q.scale Q))
        (openCubeSet (originCube d Q.scale)) := by
  calc
    openCubeSet Q =
        translateSet (fun i => (Q.index i : ℝ) * cubeScaleFactor Q)
          (openCubeSet (originCube d Q.scale)) := by
            exact openCubeSet_eq_translateSet_originCube_of_triadicCube Q
    _ =
        translateSet (intVecToRealVec (originCubeScaleTranslationShift Q.scale Q))
          (openCubeSet (originCube d Q.scale)) := by
            congr 1
            funext i
            have hpow :
                (((Int.ofNat (3 ^ Int.toNat Q.scale) : ℤ) : ℝ)) = cubeScaleFactor Q := by
              calc
                (((Int.ofNat (3 ^ Int.toNat Q.scale) : ℤ) : ℝ))
                    = (((3 ^ Int.toNat Q.scale : ℕ) : ℝ)) := by
                        simp
                _ = (3 : ℝ) ^ Int.toNat Q.scale := by
                  simp [Nat.cast_pow]
                _ = (3 : ℝ) ^ Q.scale := by
                  symm
                  calc
                    (3 : ℝ) ^ Q.scale = (3 : ℝ) ^ ((Int.toNat Q.scale : ℤ)) := by
                      rw [Int.toNat_of_nonneg hQ]
                    _ = (3 : ℝ) ^ Int.toNat Q.scale := by
                      rw [zpow_natCast]
            calc
              (Q.index i : ℝ) * cubeScaleFactor Q
                  = (Q.index i : ℝ) * (((Int.ofNat (3 ^ Int.toNat Q.scale) : ℤ) : ℝ)) := by
                      rw [hpow]
              _ = intVecToRealVec (originCubeScaleTranslationShift Q.scale Q) i := by
                      simp [intVecToRealVec, originCubeScaleTranslationShift, mul_comm]

/--
Triadic-cube version of
`hasQuadraticMu_translateSet_openCubeSet_originCube_of_hasOpenCubeEllipticRecoveryData`.
-/
theorem hasQuadraticMu_openCubeSet_of_triadicCube_of_hasOpenCubeEllipticRecoveryData
    {d : ℕ} (Q : TriadicCube d)
    (R : PotentialSolenoidalL2RecoveryData (openCubeSet (originCube d Q.scale)))
    {lam Lam : ℝ} {a : CoeffField d}
    (hData :
      HasOpenCubeEllipticRecoveryData (d := d) Q.scale R
        (lam := lam) (Lam := Lam)
        (translateCoeffField (fun i => (Q.index i : ℝ) * cubeScaleFactor Q) a)) :
    HasQuadraticMu (openCubeSet Q) a := by
  let z : Vec d := fun i => (Q.index i : ℝ) * cubeScaleFactor Q
  simpa [z, openCubeSet_eq_translateSet_originCube_of_triadicCube Q] using!
    hasQuadraticMu_translateSet_openCubeSet_originCube_of_hasOpenCubeEllipticRecoveryData
      (n := Q.scale) (z := z) (R := R) (a := a) hData

/--
Triadic-cube version of
`exists_coarseBlockMatrix_translateSet_openCubeSet_originCube_of_hasOpenCubeEllipticRecoveryData`.
-/
theorem exists_coarseBlockMatrix_openCubeSet_of_triadicCube_of_hasOpenCubeEllipticRecoveryData
    {d : ℕ} (Q : TriadicCube d)
    (R : PotentialSolenoidalL2RecoveryData (openCubeSet (originCube d Q.scale)))
    {lam Lam : ℝ} {a : CoeffField d}
    (hData :
      HasOpenCubeEllipticRecoveryData (d := d) Q.scale R
        (lam := lam) (Lam := Lam)
        (translateCoeffField (fun i => (Q.index i : ℝ) * cubeScaleFactor Q) a)) :
    ∃ Abar : BlockMat d, IsCoarseBlockMatrix (openCubeSet Q) a Abar := by
  let z : Vec d := fun i => (Q.index i : ℝ) * cubeScaleFactor Q
  simpa [z, openCubeSet_eq_translateSet_originCube_of_triadicCube Q] using!
    exists_coarseBlockMatrix_translateSet_openCubeSet_originCube_of_hasOpenCubeEllipticRecoveryData
      (n := Q.scale) (z := z) (R := R) (a := a) hData

/--
Canonical coarse block matrix witness on an arbitrary triadic open cube,
packaged from translated origin-cube recovery data.
-/
theorem
    isCoarseBlockMatrix_coarseBlockMatrix_openCubeSet_of_triadicCube_of_hasOpenCubeEllipticRecoveryData
    {d : ℕ} (Q : TriadicCube d)
    (R : PotentialSolenoidalL2RecoveryData (openCubeSet (originCube d Q.scale)))
    {lam Lam : ℝ} {a : CoeffField d}
    (hData :
      HasOpenCubeEllipticRecoveryData (d := d) Q.scale R
        (lam := lam) (Lam := Lam)
        (translateCoeffField (fun i => (Q.index i : ℝ) * cubeScaleFactor Q) a)) :
    IsCoarseBlockMatrix (openCubeSet Q) a (coarseBlockMatrix (openCubeSet Q) a) :=
  isCoarseBlockMatrix_coarseBlockMatrix
    (exists_coarseBlockMatrix_openCubeSet_of_triadicCube_of_hasOpenCubeEllipticRecoveryData
      Q R hData)

/--
Quadratic formula for `Mu` on an arbitrary triadic open cube, packaged from
translated origin-cube recovery data.
-/
theorem
    Mu_eq_half_blockVecDot_coarseBlockMatrix_openCubeSet_of_triadicCube_of_hasOpenCubeEllipticRecoveryData
    {d : ℕ} (Q : TriadicCube d)
    (R : PotentialSolenoidalL2RecoveryData (openCubeSet (originCube d Q.scale)))
    {lam Lam : ℝ} {a : CoeffField d}
    (hData :
      HasOpenCubeEllipticRecoveryData (d := d) Q.scale R
        (lam := lam) (Lam := Lam)
        (translateCoeffField (fun i => (Q.index i : ℝ) * cubeScaleFactor Q) a))
    (P : BlockVec d) :
    Mu (openCubeSet Q) P a =
      (1 / 2 : ℝ) * blockVecDot P
        (blockMatVecMul (coarseBlockMatrix (openCubeSet Q) a) P) :=
  Mu_eq_half_blockVecDot_coarseBlockMatrix_of_hasQuadraticMu
    (hasQuadraticMu_openCubeSet_of_triadicCube_of_hasOpenCubeEllipticRecoveryData
      Q R hData) P

/--
Quadraticity of `Mu` on an arbitrary triadic half-open cube, transported from
the open-cube recovery data across the null boundary.
-/
theorem hasQuadraticMu_cubeSet_of_triadicCube_of_hasOpenCubeEllipticRecoveryData
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (R : PotentialSolenoidalL2RecoveryData (openCubeSet (originCube d Q.scale)))
    {lam Lam : ℝ} {a : CoeffField d}
    (hData :
      HasOpenCubeEllipticRecoveryData (d := d) Q.scale R
        (lam := lam) (Lam := Lam)
        (translateCoeffField (fun i => (Q.index i : ℝ) * cubeScaleFactor Q) a)) :
    HasQuadraticMu (cubeSet Q) a :=
  (hasQuadraticMu_cubeSet_iff_openCubeSet_of_triadicCube Q).2
    (hasQuadraticMu_openCubeSet_of_triadicCube_of_hasOpenCubeEllipticRecoveryData
      Q R hData)

/--
Coarse block matrix existence on an arbitrary triadic half-open cube,
transported from translated origin-cube recovery data.
-/
theorem exists_coarseBlockMatrix_cubeSet_of_triadicCube_of_hasOpenCubeEllipticRecoveryData
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (R : PotentialSolenoidalL2RecoveryData (openCubeSet (originCube d Q.scale)))
    {lam Lam : ℝ} {a : CoeffField d}
    (hData :
      HasOpenCubeEllipticRecoveryData (d := d) Q.scale R
        (lam := lam) (Lam := Lam)
        (translateCoeffField (fun i => (Q.index i : ℝ) * cubeScaleFactor Q) a)) :
    ∃ Abar : BlockMat d, IsCoarseBlockMatrix (cubeSet Q) a Abar :=
  exists_coarseBlockMatrix_of_hasQuadraticMu
    (hasQuadraticMu_cubeSet_of_triadicCube_of_hasOpenCubeEllipticRecoveryData
      Q R hData)

/--
Canonical coarse block matrix witness on an arbitrary triadic half-open cube,
transported from translated origin-cube recovery data.
-/
theorem
    isCoarseBlockMatrix_coarseBlockMatrix_cubeSet_of_triadicCube_of_hasOpenCubeEllipticRecoveryData
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (R : PotentialSolenoidalL2RecoveryData (openCubeSet (originCube d Q.scale)))
    {lam Lam : ℝ} {a : CoeffField d}
    (hData :
      HasOpenCubeEllipticRecoveryData (d := d) Q.scale R
        (lam := lam) (Lam := Lam)
        (translateCoeffField (fun i => (Q.index i : ℝ) * cubeScaleFactor Q) a)) :
    IsCoarseBlockMatrix (cubeSet Q) a (coarseBlockMatrix (cubeSet Q) a) :=
  isCoarseBlockMatrix_coarseBlockMatrix
    (exists_coarseBlockMatrix_cubeSet_of_triadicCube_of_hasOpenCubeEllipticRecoveryData
      Q R hData)

/--
Quadratic formula for `Mu` on an arbitrary triadic half-open cube, transported
from translated origin-cube recovery data.
-/
theorem
    Mu_eq_half_blockVecDot_coarseBlockMatrix_cubeSet_of_triadicCube_of_hasOpenCubeEllipticRecoveryData
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (R : PotentialSolenoidalL2RecoveryData (openCubeSet (originCube d Q.scale)))
    {lam Lam : ℝ} {a : CoeffField d}
    (hData :
      HasOpenCubeEllipticRecoveryData (d := d) Q.scale R
        (lam := lam) (Lam := Lam)
        (translateCoeffField (fun i => (Q.index i : ℝ) * cubeScaleFactor Q) a))
    (P : BlockVec d) :
    Mu (cubeSet Q) P a =
      (1 / 2 : ℝ) * blockVecDot P
        (blockMatVecMul (coarseBlockMatrix (cubeSet Q) a) P) :=
  Mu_eq_half_blockVecDot_coarseBlockMatrix_of_hasQuadraticMu
    (hasQuadraticMu_cubeSet_of_triadicCube_of_hasOpenCubeEllipticRecoveryData
      Q R hData) P


end Homogenization
