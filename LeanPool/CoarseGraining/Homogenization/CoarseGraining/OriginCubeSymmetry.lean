/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.CoarseGraining.Definitions
import LeanPool.CoarseGraining.Homogenization.Probability.RandomField
import LeanPool.CoarseGraining.Homogenization.Sobolev.L2Ambient
import LeanPool.CoarseGraining.Homogenization.Sobolev.PotentialSolenoidalOriginCubeSymmetry
import Mathlib.LinearAlgebra.Matrix.Swap

/-! # Origin Cube Symmetry -/

namespace Homogenization

noncomputable section

namespace BlockState

/--
Coordinate sign-flip transport of a doubled state field.
-/
def signFlip {d : ℕ} (X : BlockState d) (i : Fin d) : BlockState d :=
  { potential := fun x =>
      signFlipVecContinuousLinearEquiv i (X.potential (signFlipVecContinuousLinearEquiv i x))
    flux := fun x =>
      signFlipVecContinuousLinearEquiv i (X.flux (signFlipVecContinuousLinearEquiv i x)) }

/--
Coordinate swap transport of a doubled state field.
-/
def swap {d : ℕ} (X : BlockState d) (i j : Fin d) : BlockState d :=
  { potential := fun x =>
      swapVecContinuousLinearEquiv i j (X.potential (swapVecContinuousLinearEquiv i j x))
    flux := fun x =>
      swapVecContinuousLinearEquiv i j (X.flux (swapVecContinuousLinearEquiv i j x)) }

@[simp] theorem signFlip_signFlip {d : ℕ} (X : BlockState d) (i : Fin d) :
    (X.signFlip i).signFlip i = X := by
  cases X
  case mk potential flux =>
    apply BlockState.ext
    · funext x
      have hxx :
          signFlipVecContinuousLinearEquiv i (signFlipVecContinuousLinearEquiv i x) = x :=
        signFlipVecContinuousLinearEquiv_self_apply (i := i) x
      calc
        signFlipVecContinuousLinearEquiv i
            (signFlipVecContinuousLinearEquiv i
              (potential (signFlipVecContinuousLinearEquiv i (signFlipVecContinuousLinearEquiv i x))))
            = signFlipVecContinuousLinearEquiv i
                (signFlipVecContinuousLinearEquiv i (potential x)) := by
                  rw [hxx]
        _ = potential x := by
              simpa using
                (signFlipVecContinuousLinearEquiv_self_apply (i := i) (potential x))
    · funext x
      have hxx :
          signFlipVecContinuousLinearEquiv i (signFlipVecContinuousLinearEquiv i x) = x :=
        signFlipVecContinuousLinearEquiv_self_apply (i := i) x
      calc
        signFlipVecContinuousLinearEquiv i
            (signFlipVecContinuousLinearEquiv i
              (flux (signFlipVecContinuousLinearEquiv i (signFlipVecContinuousLinearEquiv i x))))
            = signFlipVecContinuousLinearEquiv i
                (signFlipVecContinuousLinearEquiv i (flux x)) := by
                  rw [hxx]
        _ = flux x := by
              simpa using
                (signFlipVecContinuousLinearEquiv_self_apply (i := i) (flux x))

@[simp] theorem swap_swap {d : ℕ} (X : BlockState d) (i j : Fin d) :
    (X.swap i j).swap i j = X := by
  cases X
  case mk potential flux =>
    apply BlockState.ext
    · funext x
      have hxx :
          swapVecContinuousLinearEquiv i j (swapVecContinuousLinearEquiv i j x) = x :=
        swapVecContinuousLinearEquiv_self_apply (i := i) (j := j) x
      calc
        swapVecContinuousLinearEquiv i j
            (swapVecContinuousLinearEquiv i j
              (potential (swapVecContinuousLinearEquiv i j (swapVecContinuousLinearEquiv i j x))))
            = swapVecContinuousLinearEquiv i j
                (swapVecContinuousLinearEquiv i j (potential x)) := by
                  rw [hxx]
        _ = potential x := by
              simpa using
                (swapVecContinuousLinearEquiv_self_apply (i := i) (j := j) (potential x))
    · funext x
      have hxx :
          swapVecContinuousLinearEquiv i j (swapVecContinuousLinearEquiv i j x) = x :=
        swapVecContinuousLinearEquiv_self_apply (i := i) (j := j) x
      calc
        swapVecContinuousLinearEquiv i j
            (swapVecContinuousLinearEquiv i j
              (flux (swapVecContinuousLinearEquiv i j (swapVecContinuousLinearEquiv i j x))))
            = swapVecContinuousLinearEquiv i j
                (swapVecContinuousLinearEquiv i j (flux x)) := by
                  rw [hxx]
        _ = flux x := by
              simpa using
                (swapVecContinuousLinearEquiv_self_apply (i := i) (j := j) (flux x))

end BlockState

@[simp] theorem blockVecConj_signFlipMatrix_signFlipMatrix {d : ℕ}
    (P : BlockVec d) (i : Fin d) :
    blockVecConj (signFlipMatrix i) (blockVecConj (signFlipMatrix i) P) = P := by
  rcases P with ⟨p, q⟩
  apply Prod.ext
  · simpa [blockVecConj, signFlipVecContinuousLinearEquiv_apply] using
      (signFlipVecContinuousLinearEquiv_self_apply (i := i) p)
  · simpa [blockVecConj, signFlipVecContinuousLinearEquiv_apply] using
      (signFlipVecContinuousLinearEquiv_self_apply (i := i) q)

@[simp] theorem blockVecConj_swap_swap {d : ℕ}
    (P : BlockVec d) (i j : Fin d) :
    blockVecConj (Matrix.swap ℝ i j) (blockVecConj (Matrix.swap ℝ i j) P) = P := by
  rcases P with ⟨p, q⟩
  apply Prod.ext
  · simpa [blockVecConj, swapVecContinuousLinearEquiv_apply] using
      (swapVecContinuousLinearEquiv_self_apply (i := i) (j := j) p)
  · simpa [blockVecConj, swapVecContinuousLinearEquiv_apply] using
      (swapVecContinuousLinearEquiv_self_apply (i := i) (j := j) q)

@[simp] theorem rotateCoeffField_signFlipMatrix_signFlipMatrix {d : ℕ}
    (a : CoeffField d) (i : Fin d) :
    rotateCoeffField (signFlipMatrix i) (rotateCoeffField (signFlipMatrix i) a) = a := by
  funext x
  have hx :
      matVecMul (signFlipMatrix i) (matVecMul (signFlipMatrix i) x) = x := by
    simpa [signFlipVecContinuousLinearEquiv_apply] using
      (signFlipVecContinuousLinearEquiv_self_apply (i := i) x)
  calc
    rotateCoeffField (signFlipMatrix i) (rotateCoeffField (signFlipMatrix i) a) x
        = matTranspose (signFlipMatrix i) *
            (matTranspose (signFlipMatrix i) * a (matVecMul (signFlipMatrix i)
              (matVecMul (signFlipMatrix i) x)) * signFlipMatrix i) *
              signFlipMatrix i := by
            rfl
    _ = signFlipMatrix i * (signFlipMatrix i * a x * signFlipMatrix i) * signFlipMatrix i := by
          simp [matTranspose_signFlipMatrix, hx]
    _ = (signFlipMatrix i * signFlipMatrix i) * a x * (signFlipMatrix i * signFlipMatrix i) := by
          simp [Matrix.mul_assoc]
    _ = a x := by
          simp [signFlipMatrix_mul_self]

@[simp] theorem rotateCoeffField_swap_swap {d : ℕ}
    (a : CoeffField d) (i j : Fin d) :
    rotateCoeffField (Matrix.swap ℝ i j) (rotateCoeffField (Matrix.swap ℝ i j) a) = a := by
  funext x
  have hx :
      matVecMul (Matrix.swap ℝ i j) (matVecMul (Matrix.swap ℝ i j) x) = x := by
    simpa [swapVecContinuousLinearEquiv_apply] using
      (swapVecContinuousLinearEquiv_self_apply (i := i) (j := j) x)
  calc
    rotateCoeffField (Matrix.swap ℝ i j) (rotateCoeffField (Matrix.swap ℝ i j) a) x
        = matTranspose (Matrix.swap ℝ i j) *
            (matTranspose (Matrix.swap ℝ i j) * a (matVecMul (Matrix.swap ℝ i j)
              (matVecMul (Matrix.swap ℝ i j) x)) * Matrix.swap ℝ i j) *
              Matrix.swap ℝ i j := by
            rfl
    _ = Matrix.swap ℝ i j * (Matrix.swap ℝ i j * a x * Matrix.swap ℝ i j) * Matrix.swap ℝ i j := by
          simp [matTranspose, hx]
    _ = (Matrix.swap ℝ i j * Matrix.swap ℝ i j) * a x *
          (Matrix.swap ℝ i j * Matrix.swap ℝ i j) := by
          simp [Matrix.mul_assoc]
    _ = a x := by
          simp [Matrix.swap_mul_self (R := ℝ) i j]

private theorem measurePreserving_signFlipVecContinuousLinearEquiv {d : ℕ} (i : Fin d) :
    MeasureTheory.MeasurePreserving (signFlipVecContinuousLinearEquiv i) MeasureTheory.volume
      MeasureTheory.volume := by
  classical
  simpa [signFlipVecContinuousLinearEquiv_apply] using!
    (MeasureTheory.volume_preserving_pi fun j : Fin d =>
      by
        by_cases h : j = i
        · subst h
          simpa using!
            (MeasureTheory.Measure.measurePreserving_neg
              (MeasureTheory.volume : MeasureTheory.Measure ℝ))
        · simpa [h] using
            (MeasureTheory.MeasurePreserving.id
              (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ))))

private theorem measurePreserving_swapVecContinuousLinearEquiv {d : ℕ} (i j : Fin d) :
    MeasureTheory.MeasurePreserving (swapVecContinuousLinearEquiv i j) MeasureTheory.volume
      MeasureTheory.volume := by
  simpa [swapVecContinuousLinearEquiv] using!
    (MeasureTheory.volume_measurePreserving_piCongrLeft
      (fun _ : Fin d => ℝ) (Equiv.swap i j))

private theorem measurePreserving_signFlipVecContinuousLinearEquiv_restrict_openCubeSet_originCube
    {d : ℕ} (i : Fin d) (n : ℤ) :
    MeasureTheory.MeasurePreserving (signFlipVecContinuousLinearEquiv i)
      (MeasureTheory.volume.restrict (openCubeSet (originCube d n)))
      (MeasureTheory.volume.restrict (openCubeSet (originCube d n))) := by
  let U := openCubeSet (originCube d n)
  have hpre : (signFlipVecContinuousLinearEquiv i) ⁻¹' U = U := by
    ext x
    simpa [U] using (mem_openCubeSet_originCube_signFlipMatrix_iff (m := n) (i := i) (x := x))
  simpa [U, hpre] using
    (measurePreserving_signFlipVecContinuousLinearEquiv i).restrict_preimage_emb
      (signFlipVecContinuousLinearEquiv i).toHomeomorph.measurableEmbedding U

private theorem measurePreserving_swapVecContinuousLinearEquiv_restrict_openCubeSet_originCube
    {d : ℕ} (i j : Fin d) (n : ℤ) :
    MeasureTheory.MeasurePreserving (swapVecContinuousLinearEquiv i j)
      (MeasureTheory.volume.restrict (openCubeSet (originCube d n)))
      (MeasureTheory.volume.restrict (openCubeSet (originCube d n))) := by
  let U := openCubeSet (originCube d n)
  have hpre : (swapVecContinuousLinearEquiv i j) ⁻¹' U = U := by
    ext x
    simpa [U] using (mem_openCubeSet_originCube_swap_iff (m := n) (i := i) (j := j) (x := x))
  simpa [U, hpre] using
    (measurePreserving_swapVecContinuousLinearEquiv i j).restrict_preimage_emb
      (swapVecContinuousLinearEquiv i j).toHomeomorph.measurableEmbedding U

theorem isBlockMuAdmissible_signFlip_openCubeSet_originCube
    {d : ℕ} {n : ℤ} {P : BlockVec d} {X : BlockState d}
    (hX : IsBlockMuAdmissible (openCubeSet (originCube d n)) P X) (i : Fin d) :
    IsBlockMuAdmissible (openCubeSet (originCube d n))
      (blockVecConj (signFlipMatrix i) P) (X.signFlip i) := by
  rcases hX with ⟨hpotL2, hpot, hsolL2, hsol⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · convert
      ((signFlipVecContinuousLinearEquiv i).toContinuousLinearMap.comp_memLp'
        (hpotL2.comp_measurePreserving
          (measurePreserving_signFlipVecContinuousLinearEquiv_restrict_openCubeSet_originCube
            i n))) using 1
    funext x
    simp [BlockState.signFlip, blockVecConj, signFlipVecContinuousLinearEquiv_apply, map_sub]
  · convert
      isPotentialZeroTraceOn_signFlip_openCubeSet_originCube
        (f := fun x => X.potential x - P.1) hpot i using 1
    funext x
    simp [BlockState.signFlip, blockVecConj, signFlipVecContinuousLinearEquiv_apply,
      sub_eq_add_neg, matVecMul_add, matVecMul_neg]
  · convert
      ((signFlipVecContinuousLinearEquiv i).toContinuousLinearMap.comp_memLp'
        (hsolL2.comp_measurePreserving
          (measurePreserving_signFlipVecContinuousLinearEquiv_restrict_openCubeSet_originCube
            i n))) using 1
    funext x
    simp [BlockState.signFlip, blockVecConj, signFlipVecContinuousLinearEquiv_apply, map_sub]
  · convert
      isSolenoidalZeroNormalTraceOn_signFlip_openCubeSet_originCube
        (g := fun x => X.flux x - P.2) hsol i using 1
    funext x
    simp [BlockState.signFlip, blockVecConj, signFlipVecContinuousLinearEquiv_apply,
      sub_eq_add_neg, matVecMul_add, matVecMul_neg]

theorem isBlockMuAdmissible_swap_openCubeSet_originCube
    {d : ℕ} {n : ℤ} {P : BlockVec d} {X : BlockState d}
    (hX : IsBlockMuAdmissible (openCubeSet (originCube d n)) P X) (i j : Fin d) :
    IsBlockMuAdmissible (openCubeSet (originCube d n))
      (blockVecConj (Matrix.swap ℝ i j) P) (X.swap i j) := by
  rcases hX with ⟨hpotL2, hpot, hsolL2, hsol⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · convert
      ((swapVecContinuousLinearEquiv i j).toContinuousLinearMap.comp_memLp'
        (hpotL2.comp_measurePreserving
          (measurePreserving_swapVecContinuousLinearEquiv_restrict_openCubeSet_originCube i j n)))
      using 1
    funext x
    simp [BlockState.swap, blockVecConj, swapVecContinuousLinearEquiv_apply, map_sub]
  · convert
      isPotentialZeroTraceOn_swap_openCubeSet_originCube
        (f := fun x => X.potential x - P.1) hpot i j using 1
    funext x
    simp [BlockState.swap, blockVecConj, swapVecContinuousLinearEquiv_apply,
      sub_eq_add_neg, matVecMul_add, matVecMul_neg]
  · convert
      ((swapVecContinuousLinearEquiv i j).toContinuousLinearMap.comp_memLp'
        (hsolL2.comp_measurePreserving
          (measurePreserving_swapVecContinuousLinearEquiv_restrict_openCubeSet_originCube i j n)))
      using 1
    funext x
    simp [BlockState.swap, blockVecConj, swapVecContinuousLinearEquiv_apply, map_sub]
  · convert
      isSolenoidalZeroNormalTraceOn_swap_openCubeSet_originCube
        (g := fun x => X.flux x - P.2) hsol i j using 1
    funext x
    simp [BlockState.swap, blockVecConj, swapVecContinuousLinearEquiv_apply,
      sub_eq_add_neg, matVecMul_add, matVecMul_neg]

theorem blockEnergyDensity_rotateCoeffField_signFlip
    {d : ℕ} (a : CoeffField d) (X : BlockState d) (i : Fin d) (x : Vec d) :
    blockEnergyDensity (rotateCoeffField (signFlipMatrix i) a) (X.signFlip i) x =
      blockEnergyDensity a X (signFlipVecContinuousLinearEquiv i x) := by
  let Y : BlockState d :=
    { potential := fun y => X.potential (signFlipVecContinuousLinearEquiv i y)
      flux := fun y => X.flux (signFlipVecContinuousLinearEquiv i y) }
  have h :=
    blockEnergyDensity_mapMatrix_signFlipMatrix_conj
      (a := fun y => a (signFlipVecContinuousLinearEquiv i y)) (X := Y) (i := i) (x := x)
  simpa [rotateCoeffField, blockEnergyDensity, blockCoeffField, BlockState.signFlip,
    BlockState.eval, Y, signFlipVecContinuousLinearEquiv_apply, matTranspose_signFlipMatrix]
    using! h

theorem blockEnergyDensity_rotateCoeffField_swap
    {d : ℕ} (a : CoeffField d) (X : BlockState d) (i j : Fin d) (x : Vec d) :
    blockEnergyDensity (rotateCoeffField (Matrix.swap ℝ i j) a) (X.swap i j) x =
      blockEnergyDensity a X (swapVecContinuousLinearEquiv i j x) := by
  let Y : BlockState d :=
    { potential := fun y => X.potential (swapVecContinuousLinearEquiv i j y)
      flux := fun y => X.flux (swapVecContinuousLinearEquiv i j y) }
  have h :=
    blockEnergyDensity_mapMatrix_swap_conj
      (a := fun y => a (swapVecContinuousLinearEquiv i j y)) (X := Y) (i := i) (j := j) (x := x)
  simpa [rotateCoeffField, blockEnergyDensity, blockCoeffField, BlockState.swap,
    BlockState.eval, Y, swapVecContinuousLinearEquiv_apply, matTranspose] using! h

theorem volumeAverage_blockEnergyDensity_signFlip_openCubeSet_originCube
    {d : ℕ} (n : ℤ) (a : CoeffField d) (X : BlockState d) (i : Fin d) :
    volumeAverage (openCubeSet (originCube d n))
      (blockEnergyDensity (rotateCoeffField (signFlipMatrix i) a) (X.signFlip i)) =
        volumeAverage (openCubeSet (originCube d n)) (blockEnergyDensity a X) := by
  unfold volumeAverage
  have hfun :
      (fun x =>
        blockEnergyDensity (rotateCoeffField (signFlipMatrix i) a) (X.signFlip i) x) =
        fun x => blockEnergyDensity a X (signFlipVecContinuousLinearEquiv i x) := by
    funext x
    exact blockEnergyDensity_rotateCoeffField_signFlip a X i x
  rw [hfun, setIntegral_comp_signFlipVecContinuousLinearEquiv_openCubeSet_originCube]

theorem volumeAverage_blockEnergyDensity_swap_openCubeSet_originCube
    {d : ℕ} (n : ℤ) (a : CoeffField d) (X : BlockState d) (i j : Fin d) :
    volumeAverage (openCubeSet (originCube d n))
      (blockEnergyDensity (rotateCoeffField (Matrix.swap ℝ i j) a) (X.swap i j)) =
        volumeAverage (openCubeSet (originCube d n)) (blockEnergyDensity a X) := by
  unfold volumeAverage
  have hfun :
      (fun x =>
        blockEnergyDensity (rotateCoeffField (Matrix.swap ℝ i j) a) (X.swap i j) x) =
        fun x => blockEnergyDensity a X (swapVecContinuousLinearEquiv i j x) := by
    funext x
    exact blockEnergyDensity_rotateCoeffField_swap a X i j x
  rw [hfun, setIntegral_comp_swapVecContinuousLinearEquiv_openCubeSet_originCube]

theorem muValueSet_signFlip_openCubeSet_originCube
    {d : ℕ} (n : ℤ) (P : BlockVec d) (a : CoeffField d) (i : Fin d) :
    muValueSet (openCubeSet (originCube d n))
        (blockVecConj (signFlipMatrix i) P) (rotateCoeffField (signFlipMatrix i) a) =
      muValueSet (openCubeSet (originCube d n)) P a := by
  ext m
  constructor
  · rintro ⟨X, hX, hm⟩
    refine ⟨X.signFlip i, ?_, ?_⟩
    · simpa using
        isBlockMuAdmissible_signFlip_openCubeSet_originCube
          (n := n) (P := blockVecConj (signFlipMatrix i) P) (X := X) hX i
    · calc
        m = volumeAverage (openCubeSet (originCube d n))
              (blockEnergyDensity (rotateCoeffField (signFlipMatrix i) a) X) := hm
        _ = volumeAverage (openCubeSet (originCube d n))
              (blockEnergyDensity
                (rotateCoeffField (signFlipMatrix i)
                  (rotateCoeffField (signFlipMatrix i) a)) (X.signFlip i)) := by
              symm
              exact volumeAverage_blockEnergyDensity_signFlip_openCubeSet_originCube
                (n := n) (a := rotateCoeffField (signFlipMatrix i) a) (X := X) i
        _ = volumeAverage (openCubeSet (originCube d n))
              (blockEnergyDensity a (X.signFlip i)) := by
              simp
  · rintro ⟨X, hX, hm⟩
    refine ⟨X.signFlip i, ?_, ?_⟩
    · exact isBlockMuAdmissible_signFlip_openCubeSet_originCube
        (n := n) (P := P) (X := X) hX i
    · calc
        m = volumeAverage (openCubeSet (originCube d n)) (blockEnergyDensity a X) := hm
        _ = volumeAverage (openCubeSet (originCube d n))
              (blockEnergyDensity (rotateCoeffField (signFlipMatrix i) a) (X.signFlip i)) :=
              (volumeAverage_blockEnergyDensity_signFlip_openCubeSet_originCube
                (n := n) (a := a) (X := X) i).symm

theorem muValueSet_swap_openCubeSet_originCube
    {d : ℕ} (n : ℤ) (P : BlockVec d) (a : CoeffField d) (i j : Fin d) :
    muValueSet (openCubeSet (originCube d n))
        (blockVecConj (Matrix.swap ℝ i j) P) (rotateCoeffField (Matrix.swap ℝ i j) a) =
      muValueSet (openCubeSet (originCube d n)) P a := by
  ext m
  constructor
  · rintro ⟨X, hX, hm⟩
    refine ⟨X.swap i j, ?_, ?_⟩
    · simpa using
        isBlockMuAdmissible_swap_openCubeSet_originCube
          (n := n) (P := blockVecConj (Matrix.swap ℝ i j) P) (X := X) hX i j
    · calc
        m = volumeAverage (openCubeSet (originCube d n))
              (blockEnergyDensity (rotateCoeffField (Matrix.swap ℝ i j) a) X) := hm
        _ = volumeAverage (openCubeSet (originCube d n))
              (blockEnergyDensity
                (rotateCoeffField (Matrix.swap ℝ i j)
                  (rotateCoeffField (Matrix.swap ℝ i j) a)) (X.swap i j)) := by
              symm
              exact volumeAverage_blockEnergyDensity_swap_openCubeSet_originCube
                (n := n) (a := rotateCoeffField (Matrix.swap ℝ i j) a) (X := X) i j
        _ = volumeAverage (openCubeSet (originCube d n))
              (blockEnergyDensity a (X.swap i j)) := by
              simp
  · rintro ⟨X, hX, hm⟩
    refine ⟨X.swap i j, ?_, ?_⟩
    · exact isBlockMuAdmissible_swap_openCubeSet_originCube
        (n := n) (P := P) (X := X) hX i j
    · calc
        m = volumeAverage (openCubeSet (originCube d n)) (blockEnergyDensity a X) := hm
        _ = volumeAverage (openCubeSet (originCube d n))
              (blockEnergyDensity (rotateCoeffField (Matrix.swap ℝ i j) a) (X.swap i j)) :=
              (volumeAverage_blockEnergyDensity_swap_openCubeSet_originCube
                (n := n) (a := a) (X := X) i j).symm

theorem Mu_signFlip_openCubeSet_originCube
    {d : ℕ} (n : ℤ) (P : BlockVec d) (a : CoeffField d) (i : Fin d) :
    Mu (openCubeSet (originCube d n))
        (blockVecConj (signFlipMatrix i) P) (rotateCoeffField (signFlipMatrix i) a) =
      Mu (openCubeSet (originCube d n)) P a := by
  rw [Mu, Mu, muValueSet_signFlip_openCubeSet_originCube (d := d) n P a i]

theorem Mu_swap_openCubeSet_originCube
    {d : ℕ} (n : ℤ) (P : BlockVec d) (a : CoeffField d) (i j : Fin d) :
    Mu (openCubeSet (originCube d n))
        (blockVecConj (Matrix.swap ℝ i j) P) (rotateCoeffField (Matrix.swap ℝ i j) a) =
      Mu (openCubeSet (originCube d n)) P a := by
  rw [Mu, Mu, muValueSet_swap_openCubeSet_originCube (d := d) n P a i j]

private theorem isSymmetricBlockMat_blockMatConj_of_transpose_eq_self {d : ℕ}
    {Abar : BlockMat d} {R : Mat d} (hA : IsSymmetricBlockMat Abar)
    (hR : matTranspose R = R) :
    IsSymmetricBlockMat (blockMatConj R Abar) := by
  have hul : matTranspose Abar.upperLeft = Abar.upperLeft := by
    ext i j
    simpa [matTranspose] using! hA (Sum.inl j) (Sum.inl i)
  have hur : matTranspose Abar.upperRight = Abar.lowerLeft := by
    ext i j
    simpa [matTranspose] using! hA (Sum.inl j) (Sum.inr i)
  have hll : matTranspose Abar.lowerLeft = Abar.upperRight := by
    ext i j
    simpa [matTranspose] using! hA (Sum.inr j) (Sum.inl i)
  have hlr : matTranspose Abar.lowerRight = Abar.lowerRight := by
    ext i j
    simpa [matTranspose] using! hA (Sum.inr j) (Sum.inr i)
  intro α β
  cases α with
  | inl i =>
      cases β with
      | inl j =>
          have hconj :
              matTranspose (R * Abar.upperLeft * R) = R * Abar.upperLeft * R := by
            rw [matTranspose_mul_mul_of_transpose_eq_self hR, hul]
          have h := congrArg (fun M => M j i) hconj
          simpa [blockMatConj, blockMatEntry, matTranspose] using h
      | inr j =>
          have hconj :
              matTranspose (R * Abar.upperRight * R) = R * Abar.lowerLeft * R := by
            rw [matTranspose_mul_mul_of_transpose_eq_self hR, hur]
          have h := congrArg (fun M => M j i) hconj
          simpa [blockMatConj, blockMatEntry, matTranspose] using h
  | inr i =>
      cases β with
      | inl j =>
          have hconj :
              matTranspose (R * Abar.lowerLeft * R) = R * Abar.upperRight * R := by
            rw [matTranspose_mul_mul_of_transpose_eq_self hR, hll]
          have h := congrArg (fun M => M j i) hconj
          simpa [blockMatConj, blockMatEntry, matTranspose] using h
      | inr j =>
          have hconj :
              matTranspose (R * Abar.lowerRight * R) = R * Abar.lowerRight * R := by
            rw [matTranspose_mul_mul_of_transpose_eq_self hR, hlr]
          have h := congrArg (fun M => M j i) hconj
          simpa [blockMatConj, blockMatEntry, matTranspose] using h

namespace IsCoarseBlockMatrix

theorem signFlip_openCubeSet_originCube
    {d : ℕ} {n : ℤ} {a : CoeffField d} {Abar : BlockMat d}
    (hA : IsCoarseBlockMatrix (openCubeSet (originCube d n)) a Abar) (i : Fin d) :
    IsCoarseBlockMatrix (openCubeSet (originCube d n))
      (rotateCoeffField (signFlipMatrix i) a) (blockMatConj (signFlipMatrix i) Abar) := by
  rcases hA with ⟨hsymm, hmu⟩
  refine ⟨isSymmetricBlockMat_blockMatConj_of_transpose_eq_self hsymm
    (matTranspose_signFlipMatrix i), ?_⟩
  intro P
  have hMuP :
      Mu (openCubeSet (originCube d n)) P (rotateCoeffField (signFlipMatrix i) a) =
        Mu (openCubeSet (originCube d n)) (blockVecConj (signFlipMatrix i) P) a := by
    simpa using
      (Mu_signFlip_openCubeSet_originCube (d := d) (n := n)
        (P := blockVecConj (signFlipMatrix i) P) (a := a) i)
  have hmv :
      blockMatVecMul (blockMatConj (signFlipMatrix i) Abar) P =
        blockVecConj (signFlipMatrix i)
          (blockMatVecMul Abar (blockVecConj (signFlipMatrix i) P)) := by
    simpa using
      (blockMatVecMul_blockMatConj_of_mul_self_eq_one
        (R := signFlipMatrix i) (B := Abar) (X := blockVecConj (signFlipMatrix i) P)
        (hR2 := signFlipMatrix_mul_self i))
  have hdot :
      blockVecDot P (blockMatVecMul (blockMatConj (signFlipMatrix i) Abar) P) =
        blockVecDot (blockVecConj (signFlipMatrix i) P)
          (blockMatVecMul Abar (blockVecConj (signFlipMatrix i) P)) := by
    calc
      blockVecDot P (blockMatVecMul (blockMatConj (signFlipMatrix i) Abar) P)
          = blockVecDot (blockVecConj (signFlipMatrix i) (blockVecConj (signFlipMatrix i) P))
              (blockVecConj (signFlipMatrix i)
                (blockMatVecMul Abar (blockVecConj (signFlipMatrix i) P))) := by
                  simp [hmv]
      _ = blockVecDot (blockVecConj (signFlipMatrix i) P)
            (blockMatVecMul Abar (blockVecConj (signFlipMatrix i) P)) := by
            simpa using
              (blockVecDot_blockVecConj_of_transpose_eq_self_of_mul_self_eq_one
                (R := signFlipMatrix i)
                (X := blockVecConj (signFlipMatrix i) P)
                (Y := blockMatVecMul Abar (blockVecConj (signFlipMatrix i) P))
                (hR := matTranspose_signFlipMatrix i)
                (hR2 := signFlipMatrix_mul_self i))
  calc
    Mu (openCubeSet (originCube d n)) P (rotateCoeffField (signFlipMatrix i) a)
        = Mu (openCubeSet (originCube d n)) (blockVecConj (signFlipMatrix i) P) a := hMuP
    _ = (1 / 2 : ℝ) *
          blockVecDot (blockVecConj (signFlipMatrix i) P)
            (blockMatVecMul Abar (blockVecConj (signFlipMatrix i) P)) := hmu _
    _ = (1 / 2 : ℝ) * blockVecDot P (blockMatVecMul (blockMatConj (signFlipMatrix i) Abar) P) := by
          rw [hdot]

theorem swap_openCubeSet_originCube
    {d : ℕ} {n : ℤ} {a : CoeffField d} {Abar : BlockMat d}
    (hA : IsCoarseBlockMatrix (openCubeSet (originCube d n)) a Abar) (i j : Fin d) :
    IsCoarseBlockMatrix (openCubeSet (originCube d n))
      (rotateCoeffField (Matrix.swap ℝ i j) a) (blockMatConj (Matrix.swap ℝ i j) Abar) := by
  rcases hA with ⟨hsymm, hmu⟩
  refine ⟨isSymmetricBlockMat_blockMatConj_of_transpose_eq_self hsymm
    (by simp [matTranspose]), ?_⟩
  intro P
  have hMuP :
      Mu (openCubeSet (originCube d n)) P (rotateCoeffField (Matrix.swap ℝ i j) a) =
        Mu (openCubeSet (originCube d n)) (blockVecConj (Matrix.swap ℝ i j) P) a := by
    simpa using
      (Mu_swap_openCubeSet_originCube (d := d) (n := n)
        (P := blockVecConj (Matrix.swap ℝ i j) P) (a := a) i j)
  have hmv :
      blockMatVecMul (blockMatConj (Matrix.swap ℝ i j) Abar) P =
        blockVecConj (Matrix.swap ℝ i j)
          (blockMatVecMul Abar (blockVecConj (Matrix.swap ℝ i j) P)) := by
    simpa using
      (blockMatVecMul_blockMatConj_of_mul_self_eq_one
        (R := Matrix.swap ℝ i j) (B := Abar) (X := blockVecConj (Matrix.swap ℝ i j) P)
        (hR2 := Matrix.swap_mul_self (R := ℝ) i j))
  have hdot :
      blockVecDot P (blockMatVecMul (blockMatConj (Matrix.swap ℝ i j) Abar) P) =
        blockVecDot (blockVecConj (Matrix.swap ℝ i j) P)
          (blockMatVecMul Abar (blockVecConj (Matrix.swap ℝ i j) P)) := by
    calc
      blockVecDot P (blockMatVecMul (blockMatConj (Matrix.swap ℝ i j) Abar) P)
          = blockVecDot (blockVecConj (Matrix.swap ℝ i j) (blockVecConj (Matrix.swap ℝ i j) P))
              (blockVecConj (Matrix.swap ℝ i j)
                (blockMatVecMul Abar (blockVecConj (Matrix.swap ℝ i j) P))) := by
                  simp [hmv]
      _ = blockVecDot (blockVecConj (Matrix.swap ℝ i j) P)
            (blockMatVecMul Abar (blockVecConj (Matrix.swap ℝ i j) P)) := by
            simpa using
              (blockVecDot_blockVecConj_of_transpose_eq_self_of_mul_self_eq_one
                (R := Matrix.swap ℝ i j)
                (X := blockVecConj (Matrix.swap ℝ i j) P)
                (Y := blockMatVecMul Abar (blockVecConj (Matrix.swap ℝ i j) P))
                (hR := by simp [matTranspose])
                (hR2 := Matrix.swap_mul_self (R := ℝ) i j))
  calc
    Mu (openCubeSet (originCube d n)) P (rotateCoeffField (Matrix.swap ℝ i j) a)
        = Mu (openCubeSet (originCube d n)) (blockVecConj (Matrix.swap ℝ i j) P) a := hMuP
    _ = (1 / 2 : ℝ) *
          blockVecDot (blockVecConj (Matrix.swap ℝ i j) P)
            (blockMatVecMul Abar (blockVecConj (Matrix.swap ℝ i j) P)) := hmu _
    _ = (1 / 2 : ℝ) * blockVecDot P (blockMatVecMul (blockMatConj (Matrix.swap ℝ i j) Abar) P) := by
          rw [hdot]

end IsCoarseBlockMatrix

theorem coarseBlockMatrix_signFlip_openCubeSet_originCube_of_exists
    {d : ℕ} {n : ℤ} {a : CoeffField d}
    (hex : ∃ Abar : BlockMat d, IsCoarseBlockMatrix (openCubeSet (originCube d n)) a Abar)
    (i : Fin d) :
    coarseBlockMatrix (openCubeSet (originCube d n)) (rotateCoeffField (signFlipMatrix i) a) =
      blockMatConj (signFlipMatrix i) (coarseBlockMatrix (openCubeSet (originCube d n)) a) := by
  rcases hex with ⟨Abar, hA⟩
  have hArot := IsCoarseBlockMatrix.signFlip_openCubeSet_originCube (n := n) hA i
  calc
    coarseBlockMatrix (openCubeSet (originCube d n)) (rotateCoeffField (signFlipMatrix i) a)
        = blockMatConj (signFlipMatrix i) Abar := by
            symm
            exact eq_coarseBlockMatrix_of_isCoarseBlockMatrix hArot
    _ = blockMatConj (signFlipMatrix i) (coarseBlockMatrix (openCubeSet (originCube d n)) a) := by
          rw [eq_coarseBlockMatrix_of_isCoarseBlockMatrix hA]

theorem coarseBlockMatrix_swap_openCubeSet_originCube_of_exists
    {d : ℕ} {n : ℤ} {a : CoeffField d}
    (hex : ∃ Abar : BlockMat d, IsCoarseBlockMatrix (openCubeSet (originCube d n)) a Abar)
    (i j : Fin d) :
    coarseBlockMatrix (openCubeSet (originCube d n)) (rotateCoeffField (Matrix.swap ℝ i j) a) =
      blockMatConj (Matrix.swap ℝ i j) (coarseBlockMatrix (openCubeSet (originCube d n)) a) := by
  rcases hex with ⟨Abar, hA⟩
  have hArot := IsCoarseBlockMatrix.swap_openCubeSet_originCube (n := n) hA i j
  calc
    coarseBlockMatrix (openCubeSet (originCube d n)) (rotateCoeffField (Matrix.swap ℝ i j) a)
        = blockMatConj (Matrix.swap ℝ i j) Abar := by
            symm
            exact eq_coarseBlockMatrix_of_isCoarseBlockMatrix hArot
    _ = blockMatConj (Matrix.swap ℝ i j) (coarseBlockMatrix (openCubeSet (originCube d n)) a) := by
          rw [eq_coarseBlockMatrix_of_isCoarseBlockMatrix hA]

theorem coarseBlockMatrix_upperLeft_signFlip_openCubeSet_originCube_of_exists
    {d : ℕ} {n : ℤ} {a : CoeffField d}
    (hex : ∃ Abar : BlockMat d, IsCoarseBlockMatrix (openCubeSet (originCube d n)) a Abar)
    (i : Fin d) :
    (coarseBlockMatrix (openCubeSet (originCube d n))
        (rotateCoeffField (signFlipMatrix i) a)).upperLeft =
      signFlipMatrix i *
        (coarseBlockMatrix (openCubeSet (originCube d n)) a).upperLeft *
          signFlipMatrix i := by
  simpa [blockMatConj] using
    congrArg BlockMat.upperLeft
      (coarseBlockMatrix_signFlip_openCubeSet_originCube_of_exists (n := n) hex i)

theorem coarseBlockMatrix_lowerRight_signFlip_openCubeSet_originCube_of_exists
    {d : ℕ} {n : ℤ} {a : CoeffField d}
    (hex : ∃ Abar : BlockMat d, IsCoarseBlockMatrix (openCubeSet (originCube d n)) a Abar)
    (i : Fin d) :
    (coarseBlockMatrix (openCubeSet (originCube d n))
        (rotateCoeffField (signFlipMatrix i) a)).lowerRight =
      signFlipMatrix i *
        (coarseBlockMatrix (openCubeSet (originCube d n)) a).lowerRight *
          signFlipMatrix i := by
  simpa [blockMatConj] using
    congrArg BlockMat.lowerRight
      (coarseBlockMatrix_signFlip_openCubeSet_originCube_of_exists (n := n) hex i)

theorem coarseBlockMatrix_upperLeft_swap_openCubeSet_originCube_of_exists
    {d : ℕ} {n : ℤ} {a : CoeffField d}
    (hex : ∃ Abar : BlockMat d, IsCoarseBlockMatrix (openCubeSet (originCube d n)) a Abar)
    (i j : Fin d) :
    (coarseBlockMatrix (openCubeSet (originCube d n))
        (rotateCoeffField (Matrix.swap ℝ i j) a)).upperLeft =
      Matrix.swap ℝ i j *
        (coarseBlockMatrix (openCubeSet (originCube d n)) a).upperLeft *
          Matrix.swap ℝ i j := by
  simpa [blockMatConj] using
    congrArg BlockMat.upperLeft
      (coarseBlockMatrix_swap_openCubeSet_originCube_of_exists (n := n) hex i j)

theorem coarseBlockMatrix_lowerRight_swap_openCubeSet_originCube_of_exists
    {d : ℕ} {n : ℤ} {a : CoeffField d}
    (hex : ∃ Abar : BlockMat d, IsCoarseBlockMatrix (openCubeSet (originCube d n)) a Abar)
    (i j : Fin d) :
    (coarseBlockMatrix (openCubeSet (originCube d n))
        (rotateCoeffField (Matrix.swap ℝ i j) a)).lowerRight =
      Matrix.swap ℝ i j *
        (coarseBlockMatrix (openCubeSet (originCube d n)) a).lowerRight *
          Matrix.swap ℝ i j := by
  simpa [blockMatConj] using
    congrArg BlockMat.lowerRight
      (coarseBlockMatrix_swap_openCubeSet_originCube_of_exists (n := n) hex i j)

end

end Homogenization
