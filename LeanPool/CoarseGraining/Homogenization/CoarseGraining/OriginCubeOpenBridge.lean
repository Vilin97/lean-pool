/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.CoarseGraining.OriginCubeSymmetry
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.Translation
import LeanPool.CoarseGraining.Homogenization.PDE.HarmonicCube
import LeanPool.CoarseGraining.Homogenization.Sobolev.L2Ambient
import LeanPool.CoarseGraining.Homogenization.Sobolev.PotentialSolenoidalCubeBridge
import LeanPool.CoarseGraining.Homogenization.Sobolev.PotentialSolenoidalOriginCubeBridge

/-! # Origin Cube Open Bridge -/

namespace Homogenization

/-!
# Deterministic origin-cube open/closed bridge

This file keeps the deterministic cube/open-cube equivalences needed by Chapter
2 and coarse-graining.  The old probability-facing annealed wrappers around
these facts live only in the legacy probability archive.
-/
private theorem cubeSet_eq_translateSet_originCube_of_triadicCube_bridge {d : ℕ}
    (Q : TriadicCube d) :
    cubeSet Q =
      translateSet (fun i => (Q.index i : ℝ) * cubeScaleFactor Q)
        (cubeSet (originCube d Q.scale)) := by
  cases Q with
  | mk scale index =>
      apply Set.ext
      intro x
      rw [mem_translateSet_iff_sub_mem]
      constructor
      · intro hx i
        simpa [cubeSet, originCube, cubeScaleFactor, sub_eq_add_neg,
          add_assoc, add_left_comm, add_comm, add_mul] using hx i
      · intro hx i
        simpa [cubeSet, originCube, cubeScaleFactor, sub_eq_add_neg,
          add_assoc, add_left_comm, add_comm, add_mul] using hx i

private theorem openCubeSet_eq_translateSet_originCube_of_triadicCube_bridge {d : ℕ}
    (Q : TriadicCube d) :
    openCubeSet Q =
      translateSet (fun i => (Q.index i : ℝ) * cubeScaleFactor Q)
        (openCubeSet (originCube d Q.scale)) := by
  cases Q with
  | mk scale index =>
      apply Set.ext
      intro x
      rw [mem_translateSet_iff_sub_mem]
      constructor
      · intro hx i
        simpa [openCubeSet, originCube, cubeScaleFactor, sub_eq_add_neg,
          add_assoc, add_left_comm, add_comm, add_mul] using hx i
      · intro hx i
        simpa [openCubeSet, originCube, cubeScaleFactor, sub_eq_add_neg,
          add_assoc, add_left_comm, add_comm, add_mul] using hx i

/--
Deterministic bridge data from the half-open origin cube to the corresponding
open cube at scale `n`.

This isolates the only genuinely domain-sensitive missing theorem needed to
transport the Chapter-4 symmetry argument from the literally invariant open cube
back to the currently defined half-open at-scale objects.
-/
structure OriginCubeOpenBridge {d : ℕ} (n : ℤ) where
  coarseBlockMatrix_eq :
    ∀ a : CoeffField d,
      coarseBlockMatrix (cubeSet (originCube d n)) a =
        coarseBlockMatrix (openCubeSet (originCube d n)) a

theorem volumeAverage_cubeSet_originCube_eq_openCubeSet {d : ℕ} (n : ℤ) (f : Vec d → ℝ) :
    volumeAverage (cubeSet (originCube d n)) f =
      volumeAverage (openCubeSet (originCube d n)) f := by
  simp [volumeAverage,
    volume_openCubeSet_eq_volume_cubeSet,
    setIntegral_cubeSet_originCube_eq_setIntegral_openCubeSet_originCube]

theorem responseJValueSet_cubeSet_originCube_eq_openCubeSet
    {d : ℕ} [NeZero d] (n : ℤ) (p q : Vec d) (a : CoeffField d) :
    responseJValueSet (cubeSet (originCube d n)) p q a =
      responseJValueSet (openCubeSet (originCube d n)) p q a := by
  ext m
  constructor
  · rintro ⟨u, hm⟩
    refine ⟨u.toOpenCubeSetOriginCube (n := n), ?_⟩
    calc
      m = volumeAverage (cubeSet (originCube d n))
            (scalarResponseIntegrand (cubeSet (originCube d n)) a p q u) := hm
      _ = volumeAverage (openCubeSet (originCube d n))
            (scalarResponseIntegrand (cubeSet (originCube d n)) a p q u) :=
          volumeAverage_cubeSet_originCube_eq_openCubeSet (d := d) n
            (scalarResponseIntegrand (cubeSet (originCube d n)) a p q u)
      _ = volumeAverage (openCubeSet (originCube d n))
            (scalarResponseIntegrand (openCubeSet (originCube d n)) a p q
              (u.toOpenCubeSetOriginCube (n := n))) := by
          congr with x
  · rintro ⟨u, hm⟩
    refine ⟨u.toCubeSetOriginCube (n := n), ?_⟩
    calc
      m = volumeAverage (openCubeSet (originCube d n))
            (scalarResponseIntegrand (openCubeSet (originCube d n)) a p q u) := hm
      _ = volumeAverage (cubeSet (originCube d n))
            (scalarResponseIntegrand (openCubeSet (originCube d n)) a p q u) := by
          symm
          exact volumeAverage_cubeSet_originCube_eq_openCubeSet (d := d) n
            (scalarResponseIntegrand (openCubeSet (originCube d n)) a p q u)
      _ = volumeAverage (cubeSet (originCube d n))
            (scalarResponseIntegrand (cubeSet (originCube d n)) a p q
              (u.toCubeSetOriginCube (n := n))) := by
          congr with x

theorem ResponseJ_cubeSet_originCube_eq_openCubeSet
    {d : ℕ} [NeZero d] (n : ℤ) (p q : Vec d) (a : CoeffField d) :
    ResponseJ (cubeSet (originCube d n)) p q a =
      ResponseJ (openCubeSet (originCube d n)) p q a := by
  rw [ResponseJ, ResponseJ, responseJValueSet_cubeSet_originCube_eq_openCubeSet (d := d) n p q a]

theorem responseJ_cubeSet_eq_openCubeSet_of_triadicCube
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (p q : Vec d) (a : CoeffField d) :
    ResponseJ (cubeSet Q) p q a = ResponseJ (openCubeSet Q) p q a := by
  let z : Vec d := fun i => (Q.index i : ℝ) * cubeScaleFactor Q
  have hcube :
      cubeSet Q = translateSet z (cubeSet (originCube d Q.scale)) := by
    simpa [z] using cubeSet_eq_translateSet_originCube_of_triadicCube_bridge Q
  have hopen :
      openCubeSet Q = translateSet z (openCubeSet (originCube d Q.scale)) := by
    simpa [z] using openCubeSet_eq_translateSet_originCube_of_triadicCube_bridge Q
  calc
    ResponseJ (cubeSet Q) p q a
        = ResponseJ (translateSet z (cubeSet (originCube d Q.scale))) p q a := by
            rw [hcube]
    _ = ResponseJ (cubeSet (originCube d Q.scale)) p q (translateCoeffField z a) := by
          exact ResponseJ_translateSet_eq_translateCoeffField z
            (cubeSet (originCube d Q.scale)) p q a
    _ = ResponseJ (openCubeSet (originCube d Q.scale)) p q (translateCoeffField z a) := by
          exact ResponseJ_cubeSet_originCube_eq_openCubeSet
            (d := d) (n := Q.scale) p q (translateCoeffField z a)
    _ = ResponseJ (translateSet z (openCubeSet (originCube d Q.scale))) p q a := by
          symm
          exact ResponseJ_translateSet_eq_translateCoeffField z
            (openCubeSet (originCube d Q.scale)) p q a
    _ = ResponseJ (openCubeSet Q) p q a := by
          rw [hopen]

theorem isBlockMuAdmissible_cubeSet_originCube_iff_openCubeSet
    {d : ℕ} [NeZero d] {n : ℤ} {P : BlockVec d} {X : BlockState d} :
    IsBlockMuAdmissible (cubeSet (originCube d n)) P X ↔
      IsBlockMuAdmissible (openCubeSet (originCube d n)) P X := by
  constructor
  · rintro ⟨hpotL2, hpot, hsolL2, hsol⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [MemVectorL2, volumeMeasureOn,
        volume_restrict_cubeSet_originCube_eq_volume_restrict_openCubeSet_originCube (d := d) n]
        using hpotL2
    · exact isPotentialZeroTraceOn_openCubeSet_originCube_of_cubeSet hpot
    · simpa [MemVectorL2, volumeMeasureOn,
        volume_restrict_cubeSet_originCube_eq_volume_restrict_openCubeSet_originCube (d := d) n]
        using hsolL2
    · exact isSolenoidalZeroNormalTraceOn_openCubeSet_originCube_of_cubeSet hsol
  · rintro ⟨hpotL2, hpot, hsolL2, hsol⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [MemVectorL2, volumeMeasureOn,
        volume_restrict_cubeSet_originCube_eq_volume_restrict_openCubeSet_originCube (d := d) n]
        using hpotL2
    · exact isPotentialZeroTraceOn_cubeSet_originCube_of_openCubeSet hpot
    · simpa [MemVectorL2, volumeMeasureOn,
        volume_restrict_cubeSet_originCube_eq_volume_restrict_openCubeSet_originCube (d := d) n]
        using hsolL2
    · exact isSolenoidalZeroNormalTraceOn_cubeSet_originCube_of_openCubeSet hsol

/-- Arbitrary-triadic-cube version of the open/half-open admissibility bridge
for the doubled `Mu` problem. -/
theorem isBlockMuAdmissible_cubeSet_triadicCube_iff_openCubeSet
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {P : BlockVec d} {X : BlockState d} :
    IsBlockMuAdmissible (cubeSet Q) P X ↔
      IsBlockMuAdmissible (openCubeSet Q) P X := by
  constructor
  · rintro ⟨hpotL2, hpot, hsolL2, hsol⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [MemVectorL2, volumeMeasureOn,
        volume_restrict_cubeSet_eq_volume_restrict_openCubeSet (Q := Q)]
        using hpotL2
    · exact isPotentialZeroTraceOn_openCubeSet_triadicCube_of_cubeSet hpot
    · simpa [MemVectorL2, volumeMeasureOn,
        volume_restrict_cubeSet_eq_volume_restrict_openCubeSet (Q := Q)]
        using hsolL2
    · exact isSolenoidalZeroNormalTraceOn_openCubeSet_triadicCube_of_cubeSet hsol
  · rintro ⟨hpotL2, hpot, hsolL2, hsol⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [MemVectorL2, volumeMeasureOn,
        volume_restrict_cubeSet_eq_volume_restrict_openCubeSet (Q := Q)]
        using hpotL2
    · exact isPotentialZeroTraceOn_cubeSet_triadicCube_of_openCubeSet hpot
    · simpa [MemVectorL2, volumeMeasureOn,
        volume_restrict_cubeSet_eq_volume_restrict_openCubeSet (Q := Q)]
        using hsolL2
    · exact isSolenoidalZeroNormalTraceOn_cubeSet_triadicCube_of_openCubeSet hsol

theorem muValueSet_cubeSet_originCube_eq_openCubeSet
    {d : ℕ} [NeZero d] (n : ℤ) (P : BlockVec d) (a : CoeffField d) :
    muValueSet (cubeSet (originCube d n)) P a =
      muValueSet (openCubeSet (originCube d n)) P a := by
  ext m
  constructor
  · rintro ⟨X, hX, hm⟩
    refine ⟨X, (isBlockMuAdmissible_cubeSet_originCube_iff_openCubeSet (n := n)).1 hX, ?_⟩
    calc
      m = volumeAverage (cubeSet (originCube d n)) (blockEnergyDensity a X) := hm
      _ = volumeAverage (openCubeSet (originCube d n)) (blockEnergyDensity a X) :=
        volumeAverage_cubeSet_originCube_eq_openCubeSet (d := d) n (blockEnergyDensity a X)
  · rintro ⟨X, hX, hm⟩
    refine ⟨X, (isBlockMuAdmissible_cubeSet_originCube_iff_openCubeSet (n := n)).2 hX, ?_⟩
    calc
      m = volumeAverage (openCubeSet (originCube d n)) (blockEnergyDensity a X) := hm
      _ = volumeAverage (cubeSet (originCube d n)) (blockEnergyDensity a X) := by
        symm
        exact volumeAverage_cubeSet_originCube_eq_openCubeSet (d := d) n (blockEnergyDensity a X)

theorem Mu_cubeSet_originCube_eq_openCubeSet
    {d : ℕ} [NeZero d] (n : ℤ) (P : BlockVec d) (a : CoeffField d) :
    Mu (cubeSet (originCube d n)) P a = Mu (openCubeSet (originCube d n)) P a := by
  rw [Mu, Mu, muValueSet_cubeSet_originCube_eq_openCubeSet (d := d) n P a]

theorem blockResponseSpace_cubeSet_originCube_iff_openCubeSet
    {d : ℕ} [NeZero d] {n : ℤ} {a : CoeffField d} {X : BlockState d} :
    BlockResponseSpace a (cubeSet (originCube d n)) X ↔
      BlockResponseSpace a (openCubeSet (originCube d n)) X := by
  constructor
  · rintro ⟨hpot, hsol, horth⟩
    refine ⟨?_, ?_, ?_⟩
    · exact isPotentialOn_openCubeSet_originCube_of_cubeSet hpot
    · exact isSolenoidalOn_openCubeSet_originCube_of_cubeSet hsol
    · intro Y hY
      have hYcube : IsBlockTestOn (cubeSet (originCube d n)) Y := by
        exact
          ⟨isPotentialZeroTraceOn_cubeSet_originCube_of_openCubeSet hY.1,
            isSolenoidalZeroNormalTraceOn_cubeSet_originCube_of_openCubeSet hY.2⟩
      have hcube := horth Y hYcube
      have hset :
          ∫ x in cubeSet (originCube d n),
              blockVecDot (Y.eval x) (blockMatVecMul (blockCoeffField a x) (X.eval x))
                ∂MeasureTheory.volume =
            ∫ x in openCubeSet (originCube d n),
              blockVecDot (Y.eval x) (blockMatVecMul (blockCoeffField a x) (X.eval x))
                ∂MeasureTheory.volume := by
        exact setIntegral_cubeSet_eq_setIntegral_openCubeSet (Q := originCube d n)
      rw [hset] at hcube
      exact hcube
  · rintro ⟨hpot, hsol, horth⟩
    refine ⟨?_, ?_, ?_⟩
    · exact isPotentialOn_cubeSet_originCube_of_openCubeSet hpot
    · exact isSolenoidalOn_cubeSet_originCube_of_openCubeSet hsol
    · intro Y hY
      have hYopen : IsBlockTestOn (openCubeSet (originCube d n)) Y := by
        exact
          ⟨isPotentialZeroTraceOn_openCubeSet_originCube_of_cubeSet hY.1,
            isSolenoidalZeroNormalTraceOn_openCubeSet_originCube_of_cubeSet hY.2⟩
      have hopen := horth Y hYopen
      have hset :
          ∫ x in cubeSet (originCube d n),
              blockVecDot (Y.eval x) (blockMatVecMul (blockCoeffField a x) (X.eval x))
                ∂MeasureTheory.volume =
            ∫ x in openCubeSet (originCube d n),
              blockVecDot (Y.eval x) (blockMatVecMul (blockCoeffField a x) (X.eval x))
                ∂MeasureTheory.volume := by
        exact setIntegral_cubeSet_eq_setIntegral_openCubeSet (Q := originCube d n)
      rw [hset]
      exact hopen

theorem blockResponseIntegrabilityData_cubeSet_originCube_iff_openCubeSet
    {d : ℕ} [NeZero d] {n : ℤ} {a : CoeffField d} {X : BlockState d} :
    BlockResponseIntegrabilityData (cubeSet (originCube d n)) a X ↔
      BlockResponseIntegrabilityData (openCubeSet (originCube d n)) a X := by
  constructor
  · rintro ⟨hflux, henergy⟩
    refine ⟨?_, ?_⟩
    · simpa [MemVectorL2, volumeMeasureOn,
        volume_restrict_cubeSet_originCube_eq_volume_restrict_openCubeSet_originCube
          (d := d) n] using hflux
    · exact (integrableOn_cubeSet_originCube_iff_integrableOn_openCubeSet_originCube).1
        henergy
  · rintro ⟨hflux, henergy⟩
    refine ⟨?_, ?_⟩
    · simpa [MemVectorL2, volumeMeasureOn,
        volume_restrict_cubeSet_originCube_eq_volume_restrict_openCubeSet_originCube
          (d := d) n] using hflux
    · exact (integrableOn_cubeSet_originCube_iff_integrableOn_openCubeSet_originCube).2
        henergy

theorem blockJValueSet_cubeSet_originCube_eq_openCubeSet
    {d : ℕ} [NeZero d] (n : ℤ) (P Q : BlockVec d) (a : CoeffField d) :
    blockJValueSet (cubeSet (originCube d n)) P Q a =
      blockJValueSet (openCubeSet (originCube d n)) P Q a := by
  ext m
  constructor
  · rintro ⟨X, hX, hInt, hm⟩
    refine ⟨X, (blockResponseSpace_cubeSet_originCube_iff_openCubeSet (n := n)).1 hX,
      (blockResponseIntegrabilityData_cubeSet_originCube_iff_openCubeSet (n := n)).1 hInt, ?_⟩
    calc
      m = volumeAverage (cubeSet (originCube d n)) (blockResponseIntegrand a P Q X) := hm
      _ = volumeAverage (openCubeSet (originCube d n)) (blockResponseIntegrand a P Q X) :=
          volumeAverage_cubeSet_originCube_eq_openCubeSet (d := d) n
            (blockResponseIntegrand a P Q X)
  · rintro ⟨X, hX, hInt, hm⟩
    refine ⟨X, (blockResponseSpace_cubeSet_originCube_iff_openCubeSet (n := n)).2 hX,
      (blockResponseIntegrabilityData_cubeSet_originCube_iff_openCubeSet (n := n)).2 hInt, ?_⟩
    calc
      m = volumeAverage (openCubeSet (originCube d n)) (blockResponseIntegrand a P Q X) := hm
      _ = volumeAverage (cubeSet (originCube d n)) (blockResponseIntegrand a P Q X) := by
          symm
          exact volumeAverage_cubeSet_originCube_eq_openCubeSet (d := d) n
            (blockResponseIntegrand a P Q X)

theorem BlockJ_cubeSet_originCube_eq_openCubeSet
    {d : ℕ} [NeZero d] (n : ℤ) (P Q : BlockVec d) (a : CoeffField d) :
    BlockJ (cubeSet (originCube d n)) P Q a =
      BlockJ (openCubeSet (originCube d n)) P Q a := by
  rw [BlockJ, BlockJ, blockJValueSet_cubeSet_originCube_eq_openCubeSet (d := d) n P Q a]

theorem Mu_cubeSet_eq_openCubeSet_of_triadicCube
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (P : BlockVec d) (a : CoeffField d) :
    Mu (cubeSet Q) P a = Mu (openCubeSet Q) P a := by
  let z : Vec d := fun i => (Q.index i : ℝ) * cubeScaleFactor Q
  have hcube :
      cubeSet Q = translateSet z (cubeSet (originCube d Q.scale)) := by
    simpa [z] using cubeSet_eq_translateSet_originCube_of_triadicCube_bridge Q
  have hopen :
      openCubeSet Q = translateSet z (openCubeSet (originCube d Q.scale)) := by
    simpa [z] using openCubeSet_eq_translateSet_originCube_of_triadicCube_bridge Q
  calc
    Mu (cubeSet Q) P a
        = Mu (translateSet z (cubeSet (originCube d Q.scale))) P a := by
            rw [hcube]
    _ = Mu (cubeSet (originCube d Q.scale)) P (translateCoeffField z a) := by
          exact Mu_translateSet_eq_translateCoeffField z
            (cubeSet (originCube d Q.scale)) P a
    _ = Mu (openCubeSet (originCube d Q.scale)) P (translateCoeffField z a) := by
          exact Mu_cubeSet_originCube_eq_openCubeSet
            (d := d) (n := Q.scale) P (translateCoeffField z a)
    _ = Mu (translateSet z (openCubeSet (originCube d Q.scale))) P a := by
          symm
          exact Mu_translateSet_eq_translateCoeffField z
            (openCubeSet (originCube d Q.scale)) P a
    _ = Mu (openCubeSet Q) P a := by
          rw [hopen]

theorem BlockJ_cubeSet_eq_openCubeSet_of_triadicCube
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (P Q' : BlockVec d) (a : CoeffField d) :
    BlockJ (cubeSet Q) P Q' a = BlockJ (openCubeSet Q) P Q' a := by
  let z : Vec d := fun i => (Q.index i : ℝ) * cubeScaleFactor Q
  have hcube :
      cubeSet Q = translateSet z (cubeSet (originCube d Q.scale)) := by
    simpa [z] using cubeSet_eq_translateSet_originCube_of_triadicCube_bridge Q
  have hopen :
      openCubeSet Q = translateSet z (openCubeSet (originCube d Q.scale)) := by
    simpa [z] using openCubeSet_eq_translateSet_originCube_of_triadicCube_bridge Q
  calc
    BlockJ (cubeSet Q) P Q' a
        = BlockJ (translateSet z (cubeSet (originCube d Q.scale))) P Q' a := by
            rw [hcube]
    _ = BlockJ (cubeSet (originCube d Q.scale)) P Q' (translateCoeffField z a) := by
          exact BlockJ_translateSet_eq_translateCoeffField z
            (cubeSet (originCube d Q.scale)) P Q' a
    _ = BlockJ (openCubeSet (originCube d Q.scale)) P Q' (translateCoeffField z a) := by
          exact BlockJ_cubeSet_originCube_eq_openCubeSet
            (d := d) (n := Q.scale) P Q' (translateCoeffField z a)
    _ = BlockJ (translateSet z (openCubeSet (originCube d Q.scale))) P Q' a := by
          symm
          exact BlockJ_translateSet_eq_translateCoeffField z
            (openCubeSet (originCube d Q.scale)) P Q' a
    _ = BlockJ (openCubeSet Q) P Q' a := by
          rw [hopen]

theorem hasQuadraticMu_cubeSet_iff_openCubeSet_of_triadicCube
    {d : ℕ} [NeZero d] (Q : TriadicCube d) {a : CoeffField d} :
    HasQuadraticMu (cubeSet Q) a ↔ HasQuadraticMu (openCubeSet Q) a := by
  constructor
  · rintro ⟨Qform, hQ⟩
    refine ⟨Qform, ?_⟩
    intro P
    rw [← Mu_cubeSet_eq_openCubeSet_of_triadicCube (Q := Q) (P := P) a]
    exact hQ P
  · rintro ⟨Qform, hQ⟩
    refine ⟨Qform, ?_⟩
    intro P
    rw [Mu_cubeSet_eq_openCubeSet_of_triadicCube (Q := Q) (P := P) a]
    exact hQ P

theorem coarseBlockMatrix_cubeSet_originCube_eq_openCubeSet
    {d : ℕ} [NeZero d] (n : ℤ) (a : CoeffField d) :
    coarseBlockMatrix (cubeSet (originCube d n)) a =
      coarseBlockMatrix (openCubeSet (originCube d n)) a := by
  exact coarseBlockMatrix_eq_of_mu_eq (U := cubeSet (originCube d n))
    (V := openCubeSet (originCube d n)) (a := a)
    (fun P => Mu_cubeSet_originCube_eq_openCubeSet (d := d) n P a)

theorem isSigmaStarCoarse_cubeSet_originCube_iff_openCubeSet
    {d : ℕ} [NeZero d] {n : ℤ} {a : CoeffField d} {sigmaStar : Mat d} :
    IsSigmaStarCoarse (cubeSet (originCube d n)) a sigmaStar ↔
      IsSigmaStarCoarse (openCubeSet (originCube d n)) a sigmaStar := by
  constructor
  · rintro ⟨hsymm, hresp⟩
    refine ⟨hsymm, ?_⟩
    intro q
    rw [← ResponseJ_cubeSet_originCube_eq_openCubeSet (d := d) n 0 q a]
    exact hresp q
  · rintro ⟨hsymm, hresp⟩
    refine ⟨hsymm, ?_⟩
    intro q
    rw [ResponseJ_cubeSet_originCube_eq_openCubeSet (d := d) n 0 q a]
    exact hresp q

theorem isKappaCoarse_cubeSet_originCube_iff_openCubeSet
    {d : ℕ} [NeZero d] {n : ℤ} {a : CoeffField d} {sigmaStar kappa : Mat d} :
    IsKappaCoarse (cubeSet (originCube d n)) a sigmaStar kappa ↔
      IsKappaCoarse (openCubeSet (originCube d n)) a sigmaStar kappa := by
  constructor
  · intro hK p q
    rw [← ResponseJ_cubeSet_originCube_eq_openCubeSet (d := d) n p q a,
      ← ResponseJ_cubeSet_originCube_eq_openCubeSet (d := d) n p 0 a,
      ← ResponseJ_cubeSet_originCube_eq_openCubeSet (d := d) n 0 q a]
    exact hK p q
  · intro hK p q
    rw [ResponseJ_cubeSet_originCube_eq_openCubeSet (d := d) n p q a,
      ResponseJ_cubeSet_originCube_eq_openCubeSet (d := d) n p 0 a,
      ResponseJ_cubeSet_originCube_eq_openCubeSet (d := d) n 0 q a]
    exact hK p q

theorem isSigmaCoarse_cubeSet_originCube_iff_openCubeSet
    {d : ℕ} [NeZero d] {n : ℤ} {a : CoeffField d} {sigma sigmaStar kappa : Mat d} :
    IsSigmaCoarse (cubeSet (originCube d n)) a sigma sigmaStar kappa ↔
      IsSigmaCoarse (openCubeSet (originCube d n)) a sigma sigmaStar kappa := by
  constructor
  · rintro ⟨hsymm, hresp⟩
    refine ⟨hsymm, ?_⟩
    intro p
    rw [← ResponseJ_cubeSet_originCube_eq_openCubeSet (d := d) n p 0 a]
    exact hresp p
  · rintro ⟨hsymm, hresp⟩
    refine ⟨hsymm, ?_⟩
    intro p
    rw [ResponseJ_cubeSet_originCube_eq_openCubeSet (d := d) n p 0 a]
    exact hresp p

theorem sigmaStarInvCoarse_cubeSet_originCube_eq_openCubeSet_of_isSigmaStarCoarse
    {d : ℕ} [NeZero d] {n : ℤ} {a : CoeffField d} {sigmaStar : Mat d}
    (hS : IsSigmaStarCoarse (cubeSet (originCube d n)) a sigmaStar) :
    sigmaStarInvCoarse (cubeSet (originCube d n)) a =
      sigmaStarInvCoarse (openCubeSet (originCube d n)) a := by
  rw [sigmaStarInvCoarse_eq_inv_of_isSigmaStarCoarse hS,
    sigmaStarInvCoarse_eq_inv_of_isSigmaStarCoarse
      ((isSigmaStarCoarse_cubeSet_originCube_iff_openCubeSet (n := n)).1 hS)]

theorem sigmaStarCoarse_cubeSet_originCube_eq_openCubeSet_of_isSigmaStarCoarse
    {d : ℕ} [NeZero d] {n : ℤ} {a : CoeffField d} {sigmaStar : Mat d}
    (hS : IsSigmaStarCoarse (cubeSet (originCube d n)) a sigmaStar)
    (hdet : IsUnit sigmaStar.det) :
    sigmaStarCoarse (cubeSet (originCube d n)) a =
      sigmaStarCoarse (openCubeSet (originCube d n)) a := by
  rw [eq_sigmaStarCoarse_of_isSigmaStarCoarse hS hdet,
    eq_sigmaStarCoarse_of_isSigmaStarCoarse
      ((isSigmaStarCoarse_cubeSet_originCube_iff_openCubeSet (n := n)).1 hS) hdet]

theorem sigmaStarInvKappaCoarse_cubeSet_originCube_eq_openCubeSet_of_isKappaCoarse
    {d : ℕ} [NeZero d] {n : ℤ} {a : CoeffField d} {sigmaStar kappa : Mat d}
    (hK : IsKappaCoarse (cubeSet (originCube d n)) a sigmaStar kappa) :
    sigmaStarInvKappaCoarse (cubeSet (originCube d n)) a =
      sigmaStarInvKappaCoarse (openCubeSet (originCube d n)) a := by
  rw [sigmaStarInvKappaCoarse_eq_mul_of_isKappaCoarse hK,
    sigmaStarInvKappaCoarse_eq_mul_of_isKappaCoarse
      ((isKappaCoarse_cubeSet_originCube_iff_openCubeSet (n := n)).1 hK)]

theorem kappaCoarse_cubeSet_originCube_eq_openCubeSet_of_isSigmaStarCoarse_and_isKappaCoarse
    {d : ℕ} [NeZero d] {n : ℤ} {a : CoeffField d} {sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse (cubeSet (originCube d n)) a sigmaStar)
    (hK : IsKappaCoarse (cubeSet (originCube d n)) a sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) :
    kappaCoarse (cubeSet (originCube d n)) a =
      kappaCoarse (openCubeSet (originCube d n)) a := by
  rw [eq_kappaCoarse_of_isKappaCoarse hS hK hdet,
    eq_kappaCoarse_of_isKappaCoarse
      ((isSigmaStarCoarse_cubeSet_originCube_iff_openCubeSet (n := n)).1 hS)
      ((isKappaCoarse_cubeSet_originCube_iff_openCubeSet (n := n)).1 hK) hdet]

theorem sigmaCorrectedResponse_cubeSet_originCube_eq_openCubeSet_of_isSigmaStarCoarse_and_isKappaCoarse
    {d : ℕ} [NeZero d] {n : ℤ} {a : CoeffField d} {sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse (cubeSet (originCube d n)) a sigmaStar)
    (hK : IsKappaCoarse (cubeSet (originCube d n)) a sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) (p : Vec d) :
    sigmaCorrectedResponse (cubeSet (originCube d n)) a p =
      sigmaCorrectedResponse (openCubeSet (originCube d n)) a p := by
  rw [sigmaCorrectedResponse, sigmaCorrectedResponse,
    ResponseJ_cubeSet_originCube_eq_openCubeSet (d := d) n p 0 a,
    kappaCoarse_cubeSet_originCube_eq_openCubeSet_of_isSigmaStarCoarse_and_isKappaCoarse
      (n := n) hS hK hdet,
    sigmaStarInvCoarse_cubeSet_originCube_eq_openCubeSet_of_isSigmaStarCoarse (n := n) hS]

theorem sigmaCoarse_cubeSet_originCube_eq_openCubeSet_of_isSigmaCoarse
    {d : ℕ} [NeZero d] {n : ℤ} {a : CoeffField d} {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse (cubeSet (originCube d n)) a sigmaStar)
    (hK : IsKappaCoarse (cubeSet (originCube d n)) a sigmaStar kappa)
    (hSigma : IsSigmaCoarse (cubeSet (originCube d n)) a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) :
    sigmaCoarse (cubeSet (originCube d n)) a =
      sigmaCoarse (openCubeSet (originCube d n)) a := by
  rw [sigmaCoarse_eq_of_isSigmaCoarse hS hK hSigma hdet,
    sigmaCoarse_eq_of_isSigmaCoarse
      ((isSigmaStarCoarse_cubeSet_originCube_iff_openCubeSet (n := n)).1 hS)
      ((isKappaCoarse_cubeSet_originCube_iff_openCubeSet (n := n)).1 hK)
      ((isSigmaCoarse_cubeSet_originCube_iff_openCubeSet (n := n)).1 hSigma) hdet]

theorem bCoarse_sigmaCoarse_sigmaStarCoarse_kappaCoarse_cubeSet_originCube_eq_openCubeSet_of_isSigmaCoarse
    {d : ℕ} [NeZero d] {n : ℤ} {a : CoeffField d} {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse (cubeSet (originCube d n)) a sigmaStar)
    (hK : IsKappaCoarse (cubeSet (originCube d n)) a sigmaStar kappa)
    (hSigma : IsSigmaCoarse (cubeSet (originCube d n)) a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) :
    bCoarse (sigmaCoarse (cubeSet (originCube d n)) a)
        (sigmaStarCoarse (cubeSet (originCube d n)) a)
        (kappaCoarse (cubeSet (originCube d n)) a) =
      bCoarse (sigmaCoarse (openCubeSet (originCube d n)) a)
        (sigmaStarCoarse (openCubeSet (originCube d n)) a)
        (kappaCoarse (openCubeSet (originCube d n)) a) := by
  rw [sigmaCoarse_eq_of_isSigmaCoarse hS hK hSigma hdet,
    eq_sigmaStarCoarse_of_isSigmaStarCoarse hS hdet,
    eq_kappaCoarse_of_isKappaCoarse hS hK hdet,
    sigmaCoarse_eq_of_isSigmaCoarse
      ((isSigmaStarCoarse_cubeSet_originCube_iff_openCubeSet (n := n)).1 hS)
      ((isKappaCoarse_cubeSet_originCube_iff_openCubeSet (n := n)).1 hK)
      ((isSigmaCoarse_cubeSet_originCube_iff_openCubeSet (n := n)).1 hSigma) hdet,
    eq_sigmaStarCoarse_of_isSigmaStarCoarse
      ((isSigmaStarCoarse_cubeSet_originCube_iff_openCubeSet (n := n)).1 hS) hdet,
    eq_kappaCoarse_of_isKappaCoarse
      ((isSigmaStarCoarse_cubeSet_originCube_iff_openCubeSet (n := n)).1 hS)
      ((isKappaCoarse_cubeSet_originCube_iff_openCubeSet (n := n)).1 hK) hdet]

theorem originCubeOpenBridge {d : ℕ} [NeZero d] (n : ℤ) :
    OriginCubeOpenBridge (d := d) n where
  coarseBlockMatrix_eq := coarseBlockMatrix_cubeSet_originCube_eq_openCubeSet (d := d) n

end Homogenization
