/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Besov.Localization
public import LeanPool.CoarseGraining.Homogenization.Besov.Poincare.Descendants
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.BlockMatrixProperties
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.BlockResponse
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.OriginCubeOpenBridge
public import LeanPool.CoarseGraining.Homogenization.Geometry.OriginCubeBoundaryPush

/-! # Subadditivity -/

@[expose] public section

namespace Homogenization

noncomputable section

/-!
Subadditivity and scaling results for the deterministic coarse objects.

This file is reserved for the theorem families implementing the Chapter-2 note
label `l.cg.subadditivity.basic.definitions` together with the downstream
block-matrix subadditivity consequences.

Planned theorem-family prefixes:

- `responseJ_subadditive_*`
- `coarseBlockMatrix_subadditive_*`
- `coarseStarredBlockMatrixInv_subadditive_*`
-/

private theorem volumeAverage_openCubeSet_eq_cubeAverage {d : ℕ} (Q : TriadicCube d)
    (f : Vec d → ℝ) :
    volumeAverage (openCubeSet Q) f = cubeAverage Q f := by
  calc
    volumeAverage (openCubeSet Q) f
      = (cubeVolume Q)⁻¹ * ∫ x in openCubeSet Q, f x ∂MeasureTheory.volume := by
          unfold volumeAverage
          rw [volume_openCubeSet_toReal]
    _ = (cubeVolume Q)⁻¹ * ∫ x in cubeSet Q, f x ∂MeasureTheory.volume := by
          rw [setIntegral_cubeSet_eq_setIntegral_openCubeSet]
    _ = cubeAverage Q f := rfl

private theorem volumeAverage_openCubeSet_eq_descendantsAverage_volumeAverage_openCubeSet_of_integrableOn
    {d : ℕ} (Q : TriadicCube d) (f : Vec d → ℝ)
    (hf : MeasureTheory.IntegrableOn f (openCubeSet Q) MeasureTheory.volume) :
    volumeAverage (openCubeSet Q) f =
      descendantsAverage Q 1 (fun R => volumeAverage (openCubeSet R) f) := by
  have hCube : MeasureTheory.IntegrableOn f (cubeSet Q) MeasureTheory.volume :=
    (integrableOn_cubeSet_iff_integrableOn_openCubeSet).2 hf
  rw [volumeAverage_openCubeSet_eq_cubeAverage]
  rw [cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn Q 1 f hCube]
  unfold descendantsAverage
  refine congrArg (fun t => ((descendantsAtDepth Q 1).card : ℝ)⁻¹ * t) ?_
  refine Finset.sum_congr rfl ?_
  intro R hR
  exact (volumeAverage_openCubeSet_eq_cubeAverage R f).symm

private theorem descendantsAverage_add_const {d : ℕ} (Q : TriadicCube d) (j : ℕ)
    (F : TriadicCube d → ℝ) (c : ℝ) :
    descendantsAverage Q j (fun R => F R + c) = descendantsAverage Q j F + c := by
  classical
  let D := descendantsAtDepth Q j
  change (↑D.card)⁻¹ * D.sum (fun R => F R + c) = (↑D.card)⁻¹ * D.sum F + c
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, left_distrib]
  have hD : D.Nonempty := by
    simpa [D] using descendantsAtDepth_nonempty Q j
  have hcard : ((D.card : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr hD)
  calc
    (↑D.card)⁻¹ * D.sum F + (↑D.card)⁻¹ * (↑D.card * c)
      = (↑D.card)⁻¹ * D.sum F + ((↑D.card)⁻¹ * ↑D.card) * c := by ring
    _ = (↑D.card)⁻¹ * D.sum F + c := by
          rw [inv_mul_cancel₀ hcard, one_mul]

theorem descendantsAverage_add {d : ℕ} (Q : TriadicCube d) (j : ℕ)
    (F G : TriadicCube d → ℝ) :
    descendantsAverage Q j (fun R => F R + G R) =
      descendantsAverage Q j F + descendantsAverage Q j G := by
  classical
  let D := descendantsAtDepth Q j
  change (↑D.card)⁻¹ * D.sum (fun R => F R + G R) =
    (↑D.card)⁻¹ * D.sum F + (↑D.card)⁻¹ * D.sum G
  rw [Finset.sum_add_distrib, left_distrib]

theorem descendantsAverage_smul {d : ℕ} (Q : TriadicCube d) (j : ℕ)
    (c : ℝ) (F : TriadicCube d → ℝ) :
    descendantsAverage Q j (fun R => c * F R) = c * descendantsAverage Q j F := by
  simpa using descendantsAverage_mul_left Q j c F

/--
Entrywise descendants average of a matrix-valued observable on the depth-`j`
descendants of `Q`.
-/
noncomputable def descendantsAverageMat {d : ℕ} (Q : TriadicCube d) (j : ℕ)
    (F : TriadicCube d → Mat d) : Mat d :=
  fun i k => descendantsAverage Q j (fun R => F R i k)

/--
Entrywise descendants average of a block-matrix-valued observable on the
depth-`j` descendants of `Q`.
-/
noncomputable def descendantsAverageBlockMat {d : ℕ} (Q : TriadicCube d) (j : ℕ)
    (F : TriadicCube d → BlockMat d) : BlockMat d :=
  { upperLeft := descendantsAverageMat Q j (fun R => (F R).upperLeft)
    upperRight := descendantsAverageMat Q j (fun R => (F R).upperRight)
    lowerLeft := descendantsAverageMat Q j (fun R => (F R).lowerLeft)
    lowerRight := descendantsAverageMat Q j (fun R => (F R).lowerRight) }

theorem matVecMul_descendantsAverageMat {d : ℕ} (Q : TriadicCube d) (j : ℕ)
    (F : TriadicCube d → Mat d) (x : Vec d) :
    matVecMul (descendantsAverageMat Q j F) x =
      fun i => descendantsAverage Q j (fun R => matVecMul (F R) x i) := by
  classical
  funext i
  let D := descendantsAtDepth Q j
  let c : ℝ := ((D.card : ℝ)⁻¹)
  calc
    matVecMul (descendantsAverageMat Q j F) x i
      = ∑ k, (c * D.sum (fun R => F R i k)) * x k := by
          simp [descendantsAverageMat, descendantsAverage, matVecMul, D, c]
    _ = ∑ k, c * (D.sum (fun R => F R i k) * x k) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          ring
    _ = c * ∑ k, D.sum (fun R => F R i k) * x k := by
          rw [← Finset.mul_sum]
    _ = c * ∑ k, D.sum (fun R => F R i k * x k) := by
          simp_rw [Finset.sum_mul]
    _ = c * D.sum (fun R => ∑ k, F R i k * x k) := by
          rw [Finset.sum_comm]
    _ = descendantsAverage Q j (fun R => matVecMul (F R) x i) := by
          simp [descendantsAverage, matVecMul, D, c]

theorem vecDot_matVecMul_descendantsAverageMat {d : ℕ} (Q : TriadicCube d) (j : ℕ)
    (F : TriadicCube d → Mat d) (x y : Vec d) :
    vecDot x (matVecMul (descendantsAverageMat Q j F) y) =
      descendantsAverage Q j (fun R => vecDot x (matVecMul (F R) y)) := by
  classical
  rw [matVecMul_descendantsAverageMat]
  let D := descendantsAtDepth Q j
  let c : ℝ := ((D.card : ℝ)⁻¹)
  calc
    vecDot x (fun i => descendantsAverage Q j (fun R => matVecMul (F R) y i))
      = ∑ i, x i * (c * D.sum (fun R => matVecMul (F R) y i)) := by
          simp [vecDot, descendantsAverage, D, c]
    _ = ∑ i, c * (x i * D.sum (fun R => matVecMul (F R) y i)) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          ring
    _ = c * ∑ i, x i * D.sum (fun R => matVecMul (F R) y i) := by
          rw [← Finset.mul_sum]
    _ = c * ∑ i, D.sum (fun R => x i * matVecMul (F R) y i) := by
          simp_rw [Finset.mul_sum]
    _ = c * D.sum (fun R => ∑ i, x i * matVecMul (F R) y i) := by
          rw [Finset.sum_comm]
    _ = descendantsAverage Q j (fun R => vecDot x (matVecMul (F R) y)) := by
          simp [vecDot, descendantsAverage, D, c]

theorem blockVecDot_blockMatVecMul_descendantsAverageBlockMat {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (F : TriadicCube d → BlockMat d)
    (X Y : BlockVec d) :
    blockVecDot X (blockMatVecMul (descendantsAverageBlockMat Q j F) Y) =
      descendantsAverage Q j (fun R => blockVecDot X (blockMatVecMul (F R) Y)) := by
  rcases X with ⟨p, q⟩
  rcases Y with ⟨r, s⟩
  simp [descendantsAverageBlockMat, blockVecDot, blockMatVecMul,
    vecDot_add_right, vecDot_matVecMul_descendantsAverageMat, descendantsAverage_add,
    add_assoc]

theorem responseJ_subadditive_openCubeSet_childCubes_of_isEllipticFieldOn {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (p q : Vec d) :
    ResponseJ (openCubeSet Q) p q a ≤
      descendantsAverage Q 1 (fun R => ResponseJ (openCubeSet R) p q a) := by
  let : Fact (MeasureTheory.volume (openCubeSet Q) < ⊤) := ⟨volume_openCubeSet_lt_top Q⟩
  have hQvol : (MeasureTheory.volume (openCubeSet Q)).toReal ≠ 0 := by
    rw [volume_openCubeSet_toReal]
    exact (cubeVolume_pos Q).ne'
  have hQopen : IsOpen (openCubeSet Q) := isOpen_openCubeSet Q
  unfold ResponseJ
  refine csSup_le (responseJValueSet_nonempty (openCubeSet Q) p q a) ?_
  rintro m ⟨u, rfl⟩
  have hrespInt :
      MeasureTheory.IntegrableOn
        (scalarResponseIntegrand (openCubeSet Q) a p q u) (openCubeSet Q) := by
    exact scalarResponseIntegrand_integrableOn_of_isEllipticFieldOn hEll p q u
  calc
    volumeAverage (openCubeSet Q) (scalarResponseIntegrand (openCubeSet Q) a p q u)
      = descendantsAverage Q 1
          (fun R => volumeAverage (openCubeSet R)
            (scalarResponseIntegrand (openCubeSet Q) a p q u)) := by
              exact
                volumeAverage_openCubeSet_eq_descendantsAverage_volumeAverage_openCubeSet_of_integrableOn
                  Q (scalarResponseIntegrand (openCubeSet Q) a p q u) hrespInt
    _ ≤ descendantsAverage Q 1 (fun R => ResponseJ (openCubeSet R) p q a) := by
          unfold descendantsAverage
          refine mul_le_mul_of_nonneg_left ?_ ?_
          · refine Finset.sum_le_sum ?_
            intro R hR
            have hRchild : R ∈ childCubes Q := by
              simpa [descendantsAtDepth_one] using hR
            have hRsub : openCubeSet R ⊆ openCubeSet Q :=
              openCubeSet_subset_of_mem_childCubes hRchild
            have hEllR :
                IsEllipticFieldOn lam Lam (openCubeSet R) a :=
              IsEllipticFieldOn.mono hEll (measurableSet_openCubeSet R) hRsub
            let : Fact (MeasureTheory.volume (openCubeSet R) < ⊤) :=
              ⟨volume_openCubeSet_lt_top R⟩
            have hRvol : (MeasureTheory.volume (openCubeSet R)).toReal ≠ 0 := by
              rw [volume_openCubeSet_toReal]
              exact (cubeVolume_pos R).ne'
            let uR : AHarmonicFunction a (openCubeSet R) :=
              u.restrictOfIsEllipticFieldOn hQopen (isOpen_openCubeSet R) hRsub hEllR
            have hcongr :
                scalarResponseIntegrand (openCubeSet Q) a p q u =
                  scalarResponseIntegrand (openCubeSet R) a p q uR := by
              funext x
              simp [uR, scalarResponseIntegrand, H1Function.restrict]
            have hmem :
                volumeAverage (openCubeSet R)
                    (scalarResponseIntegrand (openCubeSet R) a p q uR) ∈
                  responseJValueSet (openCubeSet R) p q a :=
              responseJValueSet_mem (openCubeSet R) p q a uR
            calc
              volumeAverage (openCubeSet R)
                  (scalarResponseIntegrand (openCubeSet Q) a p q u)
                = volumeAverage (openCubeSet R)
                    (scalarResponseIntegrand (openCubeSet R) a p q uR) := by
                      exact congrArg (volumeAverage (openCubeSet R)) hcongr
              _ ≤ ResponseJ (openCubeSet R) p q a := by
                    exact le_responseJ_of_mem_responseJValueSet_of_isEllipticFieldOn
                      hEllR hRvol p q hmem
          · positivity

theorem responseJ_subadditive_openCubeSet_originCube_childCubes_of_isEllipticFieldOn
    {d : ℕ} (n : ℤ) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet (originCube d n)) a) (p q : Vec d) :
    ResponseJ (openCubeSet (originCube d n)) p q a ≤
      descendantsAverage (originCube d n) 1 (fun R => ResponseJ (openCubeSet R) p q a) := by
  simpa using responseJ_subadditive_openCubeSet_childCubes_of_isEllipticFieldOn
    (Q := originCube d n) a hEll p q

theorem responseJ_subadditive_openCubeSet_descendantsAtDepth_of_isEllipticFieldOn {d : ℕ}
    (j : ℕ) (Q : TriadicCube d) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (p q : Vec d) :
    ResponseJ (openCubeSet Q) p q a ≤
      descendantsAverage Q j (fun R => ResponseJ (openCubeSet R) p q a) := by
  induction j generalizing Q with
  | zero =>
      unfold descendantsAverage
      simp
  | succ j ih =>
      calc
        ResponseJ (openCubeSet Q) p q a
          ≤ descendantsAverage Q 1 (fun R => ResponseJ (openCubeSet R) p q a) := by
              exact responseJ_subadditive_openCubeSet_childCubes_of_isEllipticFieldOn
                Q a hEll p q
        _ ≤ descendantsAverage Q 1
              (fun R => descendantsAverage R j (fun S => ResponseJ (openCubeSet S) p q a)) := by
                unfold descendantsAverage
                refine mul_le_mul_of_nonneg_left ?_ ?_
                · refine Finset.sum_le_sum ?_
                  intro R hR
                  have hRchild : R ∈ childCubes Q := by
                    simpa [descendantsAtDepth_one] using hR
                  have hRsub : openCubeSet R ⊆ openCubeSet Q :=
                    openCubeSet_subset_of_mem_childCubes hRchild
                  have hEllR :
                      IsEllipticFieldOn lam Lam (openCubeSet R) a :=
                    IsEllipticFieldOn.mono hEll (measurableSet_openCubeSet R) hRsub
                  exact ih (Q := R) hEllR
                · positivity
        _ = descendantsAverage Q (j + 1)
              (fun R => ResponseJ (openCubeSet R) p q a) := by
                have havg :=
                  descendantsAverage_add_eq_descendantsAverage_descendantsAverage Q 1 j
                    (fun R => ResponseJ (openCubeSet R) p q a)
                simpa [Nat.add_comm] using havg.symm

theorem responseJ_subadditive_cubeSet_childCubes_of_isEllipticFieldOn
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (p q : Vec d) :
    ResponseJ (cubeSet Q) p q a ≤
      descendantsAverage Q 1 (fun R => ResponseJ (cubeSet R) p q a) := by
  calc
    ResponseJ (cubeSet Q) p q a = ResponseJ (openCubeSet Q) p q a := by
      exact responseJ_cubeSet_eq_openCubeSet_of_triadicCube Q p q a
    _ ≤ descendantsAverage Q 1 (fun R => ResponseJ (openCubeSet R) p q a) := by
      exact responseJ_subadditive_openCubeSet_childCubes_of_isEllipticFieldOn Q a hEll p q
    _ = descendantsAverage Q 1 (fun R => ResponseJ (cubeSet R) p q a) := by
      unfold descendantsAverage
      refine congrArg (fun t => ((descendantsAtDepth Q 1).card : ℝ)⁻¹ * t) ?_
      refine Finset.sum_congr rfl ?_
      intro R hR
      rw [responseJ_cubeSet_eq_openCubeSet_of_triadicCube R p q a]

theorem responseJ_subadditive_cubeSet_descendantsAtDepth_of_isEllipticFieldOn
    {d : ℕ} [NeZero d] (j : ℕ) (Q : TriadicCube d) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (p q : Vec d) :
    ResponseJ (cubeSet Q) p q a ≤
      descendantsAverage Q j (fun R => ResponseJ (cubeSet R) p q a) := by
  calc
    ResponseJ (cubeSet Q) p q a = ResponseJ (openCubeSet Q) p q a := by
      exact responseJ_cubeSet_eq_openCubeSet_of_triadicCube Q p q a
    _ ≤ descendantsAverage Q j (fun R => ResponseJ (openCubeSet R) p q a) := by
      exact responseJ_subadditive_openCubeSet_descendantsAtDepth_of_isEllipticFieldOn
        j Q a hEll p q
    _ = descendantsAverage Q j (fun R => ResponseJ (cubeSet R) p q a) := by
      unfold descendantsAverage
      refine congrArg (fun t => ((descendantsAtDepth Q j).card : ℝ)⁻¹ * t) ?_
      refine Finset.sum_congr rfl ?_
      intro R hR
      rw [responseJ_cubeSet_eq_openCubeSet_of_triadicCube R p q a]

theorem responseJ_subadditive_openCubeSet_originCube_descendantsAtDepth_of_isEllipticFieldOn
    {d : ℕ} (j : ℕ) (n : ℤ) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet (originCube d n)) a) (p q : Vec d) :
    ResponseJ (openCubeSet (originCube d n)) p q a ≤
      descendantsAverage (originCube d n) j (fun R => ResponseJ (openCubeSet R) p q a) := by
  simpa using responseJ_subadditive_openCubeSet_descendantsAtDepth_of_isEllipticFieldOn
    (Q := originCube d n) j a hEll p q

theorem responseJ_subadditive_cubeSet_originCube_childCubes_of_isEllipticFieldOn
    {d : ℕ} [NeZero d] (n : ℤ) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet (originCube d n)) a) (p q : Vec d) :
    ResponseJ (cubeSet (originCube d n)) p q a ≤
      descendantsAverage (originCube d n) 1 (fun R => ResponseJ (cubeSet R) p q a) := by
  simpa using
    responseJ_subadditive_cubeSet_childCubes_of_isEllipticFieldOn
      (Q := originCube d n) a hEll p q

theorem responseJ_subadditive_cubeSet_originCube_descendantsAtDepth_of_isEllipticFieldOn
    {d : ℕ} [NeZero d] (j : ℕ) (n : ℤ) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet (originCube d n)) a) (p q : Vec d) :
    ResponseJ (cubeSet (originCube d n)) p q a ≤
      descendantsAverage (originCube d n) j (fun R => ResponseJ (cubeSet R) p q a) := by
  simpa using
    responseJ_subadditive_cubeSet_descendantsAtDepth_of_isEllipticFieldOn
      (Q := originCube d n) j a hEll p q

theorem coarseBlockMatrix_subadditive_openCubeSet_descendantsAtDepth_pair_of_responseJ_blockQuadratic
    {d : ℕ} (j : ℕ) (Q : TriadicCube d) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hRespQ :
      ∀ p q : Vec d,
        ResponseJ (openCubeSet Q) p q a =
          (1 / 2 : ℝ) * blockVecDot (-p, q)
            (blockMatVecMul (coarseBlockMatrix (openCubeSet Q) a) (-p, q)) -
            vecDot p q)
    (hRespDesc :
      ∀ R ∈ descendantsAtDepth Q j, ∀ p q : Vec d,
        ResponseJ (openCubeSet R) p q a =
          (1 / 2 : ℝ) * blockVecDot (-p, q)
            (blockMatVecMul (coarseBlockMatrix (openCubeSet R) a) (-p, q)) -
            vecDot p q)
    (p q : Vec d) :
    (1 / 2 : ℝ) * blockVecDot (-p, q)
        (blockMatVecMul (coarseBlockMatrix (openCubeSet Q) a) (-p, q)) ≤
      descendantsAverage Q j
        (fun R =>
          (1 / 2 : ℝ) * blockVecDot (-p, q)
            (blockMatVecMul (coarseBlockMatrix (openCubeSet R) a) (-p, q))) := by
  have hscalar :
      ResponseJ (openCubeSet Q) p q a ≤
        descendantsAverage Q j (fun R => ResponseJ (openCubeSet R) p q a) :=
    responseJ_subadditive_openCubeSet_descendantsAtDepth_of_isEllipticFieldOn
      j Q a hEll p q
  calc
    (1 / 2 : ℝ) * blockVecDot (-p, q)
        (blockMatVecMul (coarseBlockMatrix (openCubeSet Q) a) (-p, q))
      = ResponseJ (openCubeSet Q) p q a + vecDot p q := by
          linarith [hRespQ p q]
    _ ≤ descendantsAverage Q j (fun R => ResponseJ (openCubeSet R) p q a) + vecDot p q := by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_right hscalar (vecDot p q)
    _ = descendantsAverage Q j (fun R => ResponseJ (openCubeSet R) p q a + vecDot p q) := by
          symm
          exact descendantsAverage_add_const Q j
            (fun R => ResponseJ (openCubeSet R) p q a) (vecDot p q)
    _ = descendantsAverage Q j
          (fun R =>
            (1 / 2 : ℝ) * blockVecDot (-p, q)
              (blockMatVecMul (coarseBlockMatrix (openCubeSet R) a) (-p, q))) := by
          unfold descendantsAverage
          refine congrArg (fun t => ((descendantsAtDepth Q j).card : ℝ)⁻¹ * t) ?_
          refine Finset.sum_congr rfl ?_
          intro R hR
          linarith [hRespDesc R hR p q]

theorem coarseBlockMatrix_subadditive_openCubeSet_descendantsAtDepth_blockQuadratic_of_responseJ_blockQuadratic
    {d : ℕ} (j : ℕ) (Q : TriadicCube d) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hRespQ :
      ∀ p q : Vec d,
        ResponseJ (openCubeSet Q) p q a =
          (1 / 2 : ℝ) * blockVecDot (-p, q)
            (blockMatVecMul (coarseBlockMatrix (openCubeSet Q) a) (-p, q)) -
            vecDot p q)
    (hRespDesc :
      ∀ R ∈ descendantsAtDepth Q j, ∀ p q : Vec d,
        ResponseJ (openCubeSet R) p q a =
          (1 / 2 : ℝ) * blockVecDot (-p, q)
            (blockMatVecMul (coarseBlockMatrix (openCubeSet R) a) (-p, q)) -
            vecDot p q)
    (X : BlockVec d) :
    (1 / 2 : ℝ) * blockVecDot X
        (blockMatVecMul (coarseBlockMatrix (openCubeSet Q) a) X) ≤
      descendantsAverage Q j
        (fun R =>
          (1 / 2 : ℝ) * blockVecDot X
            (blockMatVecMul (coarseBlockMatrix (openCubeSet R) a) X)) := by
  simpa using
    coarseBlockMatrix_subadditive_openCubeSet_descendantsAtDepth_pair_of_responseJ_blockQuadratic
      j Q a hEll hRespQ hRespDesc (-X.1) X.2

theorem coarseBlockMatrix_subadditive_openCubeSet_descendantsAtDepth_in_loewner_order_of_responseJ_blockQuadratic
    {d : ℕ} (j : ℕ) (Q : TriadicCube d) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hRespQ :
      ∀ p q : Vec d,
        ResponseJ (openCubeSet Q) p q a =
          (1 / 2 : ℝ) * blockVecDot (-p, q)
            (blockMatVecMul (coarseBlockMatrix (openCubeSet Q) a) (-p, q)) -
            vecDot p q)
    (hRespDesc :
      ∀ R ∈ descendantsAtDepth Q j, ∀ p q : Vec d,
        ResponseJ (openCubeSet R) p q a =
          (1 / 2 : ℝ) * blockVecDot (-p, q)
            (blockMatVecMul (coarseBlockMatrix (openCubeSet R) a) (-p, q)) -
            vecDot p q) :
    BlockMatLoewnerLE (coarseBlockMatrix (openCubeSet Q) a)
      (descendantsAverageBlockMat Q j (fun R => coarseBlockMatrix (openCubeSet R) a)) := by
  intro X
  calc
    (1 / 2 : ℝ) * blockVecDot X
        (blockMatVecMul (coarseBlockMatrix (openCubeSet Q) a) X)
      ≤ descendantsAverage Q j
          (fun R =>
            (1 / 2 : ℝ) * blockVecDot X
              (blockMatVecMul (coarseBlockMatrix (openCubeSet R) a) X)) := by
            exact
              coarseBlockMatrix_subadditive_openCubeSet_descendantsAtDepth_blockQuadratic_of_responseJ_blockQuadratic
                j Q a hEll hRespQ hRespDesc X
    _ = (1 / 2 : ℝ) *
          blockVecDot X
            (blockMatVecMul
              (descendantsAverageBlockMat Q j (fun R => coarseBlockMatrix (openCubeSet R) a)) X) := by
            rw [descendantsAverage_smul]
            rw [blockVecDot_blockMatVecMul_descendantsAverageBlockMat]

theorem coarseStarredBlockMatrixInv_subadditive_openCubeSet_descendantsAtDepth_blockQuadratic_of_responseJ_blockQuadratic
    {d : ℕ} (j : ℕ) (Q : TriadicCube d) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hRespQ :
      ∀ p q : Vec d,
        ResponseJ (openCubeSet Q) p q a =
          (1 / 2 : ℝ) * blockVecDot (-p, q)
            (blockMatVecMul (coarseBlockMatrix (openCubeSet Q) a) (-p, q)) -
            vecDot p q)
    (hRespDesc :
      ∀ R ∈ descendantsAtDepth Q j, ∀ p q : Vec d,
        ResponseJ (openCubeSet R) p q a =
          (1 / 2 : ℝ) * blockVecDot (-p, q)
            (blockMatVecMul (coarseBlockMatrix (openCubeSet R) a) (-p, q)) -
            vecDot p q)
    (X : BlockVec d) :
    (1 / 2 : ℝ) * blockVecDot X
        (blockMatVecMul (coarseStarredBlockMatrixInv (openCubeSet Q) a) X) ≤
      descendantsAverage Q j
        (fun R =>
          (1 / 2 : ℝ) * blockVecDot X
            (blockMatVecMul (coarseStarredBlockMatrixInv (openCubeSet R) a) X)) := by
  simpa [coarseStarredBlockMatrixInv_eq_blockReflect] using
    coarseBlockMatrix_subadditive_openCubeSet_descendantsAtDepth_blockQuadratic_of_responseJ_blockQuadratic
      j Q a hEll hRespQ hRespDesc (X.2, X.1)

theorem coarseStarredBlockMatrixInv_subadditive_openCubeSet_descendantsAtDepth_in_loewner_order_of_responseJ_blockQuadratic
    {d : ℕ} (j : ℕ) (Q : TriadicCube d) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hRespQ :
      ∀ p q : Vec d,
        ResponseJ (openCubeSet Q) p q a =
          (1 / 2 : ℝ) * blockVecDot (-p, q)
            (blockMatVecMul (coarseBlockMatrix (openCubeSet Q) a) (-p, q)) -
            vecDot p q)
    (hRespDesc :
      ∀ R ∈ descendantsAtDepth Q j, ∀ p q : Vec d,
        ResponseJ (openCubeSet R) p q a =
          (1 / 2 : ℝ) * blockVecDot (-p, q)
            (blockMatVecMul (coarseBlockMatrix (openCubeSet R) a) (-p, q)) -
            vecDot p q) :
    BlockMatLoewnerLE (coarseStarredBlockMatrixInv (openCubeSet Q) a)
      (descendantsAverageBlockMat Q j
        (fun R => coarseStarredBlockMatrixInv (openCubeSet R) a)) := by
  intro X
  calc
    (1 / 2 : ℝ) * blockVecDot X
        (blockMatVecMul (coarseStarredBlockMatrixInv (openCubeSet Q) a) X)
      ≤ descendantsAverage Q j
          (fun R =>
            (1 / 2 : ℝ) * blockVecDot X
              (blockMatVecMul (coarseStarredBlockMatrixInv (openCubeSet R) a) X)) := by
            exact
              coarseStarredBlockMatrixInv_subadditive_openCubeSet_descendantsAtDepth_blockQuadratic_of_responseJ_blockQuadratic
                j Q a hEll hRespQ hRespDesc X
    _ = (1 / 2 : ℝ) *
          blockVecDot X
            (blockMatVecMul
              (descendantsAverageBlockMat Q j
                (fun R => coarseStarredBlockMatrixInv (openCubeSet R) a)) X) := by
            rw [descendantsAverage_smul]
            rw [blockVecDot_blockMatVecMul_descendantsAverageBlockMat]

theorem coarseStarredBlockMatrixInv_upperLeft_subadditive_openCubeSet_descendantsAtDepth_of_responseJ_blockQuadratic
    {d : ℕ} (j : ℕ) (Q : TriadicCube d) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hRespQ :
      ∀ p q : Vec d,
        ResponseJ (openCubeSet Q) p q a =
          (1 / 2 : ℝ) * blockVecDot (-p, q)
            (blockMatVecMul (coarseBlockMatrix (openCubeSet Q) a) (-p, q)) -
            vecDot p q)
    (hRespDesc :
      ∀ R ∈ descendantsAtDepth Q j, ∀ p q : Vec d,
        ResponseJ (openCubeSet R) p q a =
          (1 / 2 : ℝ) * blockVecDot (-p, q)
            (blockMatVecMul (coarseBlockMatrix (openCubeSet R) a) (-p, q)) -
            vecDot p q)
    (p : Vec d) :
    (1 / 2 : ℝ) * vecDot p
        (matVecMul (coarseStarredBlockMatrixInv (openCubeSet Q) a).upperLeft p) ≤
      descendantsAverage Q j
        (fun R =>
          (1 / 2 : ℝ) * vecDot p
            (matVecMul (coarseStarredBlockMatrixInv (openCubeSet R) a).upperLeft p)) := by
  simpa [blockVecDot, blockMatVecMul, matVecMul_zero, vecDot_zero_left, vecDot_zero_right] using
    coarseStarredBlockMatrixInv_subadditive_openCubeSet_descendantsAtDepth_blockQuadratic_of_responseJ_blockQuadratic
      j Q a hEll hRespQ hRespDesc (p, 0)

theorem coarseStarredBlockMatrixInv_lowerRight_subadditive_openCubeSet_descendantsAtDepth_of_responseJ_blockQuadratic
    {d : ℕ} (j : ℕ) (Q : TriadicCube d) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hRespQ :
      ∀ p q : Vec d,
        ResponseJ (openCubeSet Q) p q a =
          (1 / 2 : ℝ) * blockVecDot (-p, q)
            (blockMatVecMul (coarseBlockMatrix (openCubeSet Q) a) (-p, q)) -
            vecDot p q)
    (hRespDesc :
      ∀ R ∈ descendantsAtDepth Q j, ∀ p q : Vec d,
        ResponseJ (openCubeSet R) p q a =
          (1 / 2 : ℝ) * blockVecDot (-p, q)
            (blockMatVecMul (coarseBlockMatrix (openCubeSet R) a) (-p, q)) -
            vecDot p q)
    (q : Vec d) :
    (1 / 2 : ℝ) * vecDot q
        (matVecMul (coarseStarredBlockMatrixInv (openCubeSet Q) a).lowerRight q) ≤
      descendantsAverage Q j
        (fun R =>
          (1 / 2 : ℝ) * vecDot q
            (matVecMul (coarseStarredBlockMatrixInv (openCubeSet R) a).lowerRight q)) := by
  simpa [blockVecDot, blockMatVecMul, matVecMul_zero, vecDot_zero_left, vecDot_zero_right] using
    coarseStarredBlockMatrixInv_subadditive_openCubeSet_descendantsAtDepth_blockQuadratic_of_responseJ_blockQuadratic
      j Q a hEll hRespQ hRespDesc (0, q)

end

end Homogenization
