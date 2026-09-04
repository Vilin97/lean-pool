/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Foundations.TwoOpenTransition
public import LeanPool.HopfProblem.Pi1.FundamentalGroupVanKampen2
import all LeanPool.HopfProblem.Foundations.Core1
import all LeanPool.HopfProblem.HomologyTheory.SingularMayerVietoris
import all LeanPool.HopfProblem.Lattice.Core1
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology1
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology3
import all LeanPool.HopfProblem.Foundations.Core2
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology4
import all LeanPool.HopfProblem.PeriodFamily.PeriodPoint
import all LeanPool.HopfProblem.Foundations.Core3
import all LeanPool.HopfProblem.PeriodFamily.HolomorphicPeriodMap1
import all LeanPool.HopfProblem.HomologyTheory.FirstHurewicz3
import all LeanPool.HopfProblem.Elliptic.Core1
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods1
import all LeanPool.HopfProblem.Pi1.MappingTorus
import all LeanPool.HopfProblem.Elliptic.Core2
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology6
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology7
import all LeanPool.HopfProblem.Elliptic.Core3
import all LeanPool.HopfProblem.Elliptic.Core4
import all LeanPool.HopfProblem.Foundations.TwoOpenTransition
import all LeanPool.HopfProblem.Pi1.FundamentalGroupVanKampen2

/-!
# Hopf problem: elliptic · core 5

Supporting definitions and proofs for this stage of the six-sphere construction.
-/


open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

noncomputable section

namespace Mathoverflow1973

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

private abbrev Elliptic.HigherHomology.FibreLattice :=
  Fin 3 → ℤ

private abbrev Elliptic.HigherHomology.FibreMatrix :=
  Matrix (Fin 3) (Fin 3) ℤ

private def Elliptic.HigherHomology.fibreMatrix : Elliptic.Kind → FibreMatrix
  | .three => !![0, 1, 0; -1, -1, 0; 1, 0, 1]
  | .four => !![0, -1, 0; 1, 0, 0; 0, 1, 1]

private theorem
    Elliptic.HigherHomology.fibreMatrix_det (j : Elliptic.Kind) : (fibreMatrix j).det = 1 := by
  cases j <;> decide

private theorem Elliptic.HigherHomology.fibreMatrix_pow_order (j : Elliptic.Kind) :
    (fibreMatrix j) ^ j.order = 1 := by cases j <;> decide

private def Elliptic.HigherHomology.fibreSL (j : Elliptic.Kind) : SL(3, ℤ) :=
  ⟨fibreMatrix j, fibreMatrix_det j⟩

private def Elliptic.HigherHomology.fibrePair : Fin 3 → Fin 2 → Fin 3 :=
  ![![0, 1], ![0, 2], ![1, 2] ]

private def Elliptic.HigherHomology.fibreSquareMatrix : Elliptic.Kind → FibreMatrix
  | .three => !![1, 0, 0; -1, 0, 1; 1, -1, -1]
  | .four => !![1, 0, 0; 0, 0, -1; 1, 1, 0]

private theorem Elliptic.HigherHomology.fibreSquareMatrix_minor (j : Elliptic.Kind) (i k : Fin 3) :
    fibreSquareMatrix j i k =
      fibreMatrix j (fibrePair i 0) (fibrePair k 0) *
          fibreMatrix j (fibrePair i 1) (fibrePair k 1) -
        fibreMatrix j (fibrePair i 0) (fibrePair k 1) *
          fibreMatrix j (fibrePair i 1) (fibrePair k 0) := by
  cases j <;> fin_cases i <;> fin_cases k <;> decide

private theorem Elliptic.HigherHomology.fibreSquareMatrix_det (j : Elliptic.Kind) :
    (fibreSquareMatrix j).det = 1 := by cases j <;> decide

private def Elliptic.HigherHomology.twistBasisMatrix : Elliptic.Kind → LatticeMatrix
  | .three => !![1, 0, 0, 0; 2, 1, 0, 0; -4, 0, 1, 0; 0, 0, 0, 1]
  | .four => !![-1, 0, 0, 0; -3, 1, 0, 0; 3, 0, 1, 0; 0, 0, 0, 1]

private def Elliptic.HigherHomology.twistBasisInvMatrix : Elliptic.Kind → LatticeMatrix
  | .three => !![1, 0, 0, 0; -2, 1, 0, 0; 4, 0, 1, 0; 0, 0, 0, 1]
  | .four => !![-1, 0, 0, 0; -3, 1, 0, 0; 3, 0, 1, 0; 0, 0, 0, 1]

private theorem
    Elliptic.HigherHomology.twistBasisInvMatrix_mul_twistBasisMatrix (j : Elliptic.Kind) :
    twistBasisInvMatrix j * twistBasisMatrix j = 1 := by cases j <;> decide

private theorem
    Elliptic.HigherHomology.twistBasisMatrix_mul_twistBasisInvMatrix (j : Elliptic.Kind) :
    twistBasisMatrix j * twistBasisInvMatrix j = 1 := by cases j <;> decide

private abbrev Elliptic.HigherHomology.FibreCoordinates :=
  Fin 3 → ℝ

private def Elliptic.HigherHomology.fibreLinear (j : Elliptic.Kind) :
    FibreCoordinates →ₗ[ℝ] FibreCoordinates :=
  ((fibreMatrix j).map (Int.castRingHom ℝ)).mulVecLin

private def Elliptic.HigherHomology.splitRealCoordinates (j : Elliptic.Kind) :
    Elliptic.RealCoordinates ≃L[ℝ] ℝ × FibreCoordinates :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun x =>
        ((j.twist 0 : ℝ) * x 0, fun i =>
          x i.succ - ((j.twist 0 : ℝ) * x 0) * (j.twist i.succ : ℝ))
      invFun := fun x => x.1 • Elliptic.realCast j.twist + Fin.cons 0 x.2
      left_inv := by
        intro x
        funext i
        refine Fin.cases ?_ (fun k => ?_) i
        · cases j <;> simp [Elliptic.Kind.twist, Elliptic.realCast, ε, ε']
        · simp [Elliptic.realCast]
      right_inv := by
        rintro ⟨t, k⟩
        apply Prod.ext
        · cases j <;> simp [Elliptic.Kind.twist, Elliptic.realCast, ε, ε']
        · funext i
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.cons_zero, Fin.cons_succ]
          cases j <;> fin_cases i <;> simp [Elliptic.Kind.twist, Elliptic.realCast, ε, ε']
      map_add' := by
        intro x y
        apply Prod.ext
        · simp [mul_add]
        · funext i
          simp only [Pi.add_apply, Prod.mk_add_mk]
          ring
      map_smul' := by
        intro r x
        apply Prod.ext
        · simp only [Pi.smul_apply, smul_eq_mul, Prod.smul_mk, RingHom.id_apply]
          ring
        · funext i
          simp only [Pi.smul_apply, smul_eq_mul, Prod.smul_mk, RingHom.id_apply]
          ring }

@[simp]
private theorem Elliptic.HigherHomology.splitRealCoordinates_apply (j : Elliptic.Kind)
    (x : Elliptic.RealCoordinates) :
    splitRealCoordinates j x =
      ((j.twist 0 : ℝ) * x 0, fun i =>
        x i.succ - ((j.twist 0 : ℝ) * x 0) * (j.twist i.succ : ℝ)) :=
  rfl

@[simp]
private theorem Elliptic.HigherHomology.splitRealCoordinates_symm_apply (j : Elliptic.Kind)
    (x : ℝ × FibreCoordinates) :
    (splitRealCoordinates j).symm x = x.1 • Elliptic.realCast j.twist + Fin.cons 0 x.2 :=
  rfl

private theorem
    Elliptic.HigherHomology.flatLinear_fibre (j : Elliptic.Kind) (k : FibreCoordinates) :
    Elliptic.flatLinear j (Fin.cons 0 k) = Fin.cons 0 (fibreLinear j k) := by
  ext i
  refine Fin.cases ?_ (fun a => ?_) i
  · cases j <;>
      simp [Elliptic.flatLinear, Elliptic.Kind.matrix, A₁, A₂, Matrix.mulVec, dotProduct,
        Fin.sum_univ_succ]
  · rw [Fin.cons_succ]
    cases j <;> fin_cases a <;>
      simp [Elliptic.flatLinear, fibreLinear, fibreMatrix, Elliptic.Kind.matrix, A₁, A₂,
        Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

private theorem Elliptic.HigherHomology.flatLinear_twist (j : Elliptic.Kind) :
    Elliptic.flatLinear j (Elliptic.realCast j.twist) = Elliptic.realCast j.twist := by
  rw [Elliptic.flatLinear_realCast, j.matrix_fixes_twist]

private theorem Elliptic.HigherHomology.splitRealCoordinates_flatAffine (j : Elliptic.Kind)
    (x : Elliptic.RealCoordinates) :
    splitRealCoordinates j (Elliptic.flatAffine j j.twist x) =
      ((splitRealCoordinates j x).1 + 1 / (j.order : ℝ),
        fibreLinear j (splitRealCoordinates j x).2) := by
  obtain ⟨⟨t, k⟩, rfl⟩ := (splitRealCoordinates j).symm.surjective x
  simp only [ContinuousLinearEquiv.apply_symm_apply]
  apply (splitRealCoordinates j).symm.injective
  simp only [ContinuousLinearEquiv.symm_apply_apply, splitRealCoordinates_symm_apply,
    Elliptic.flatAffine, map_add, map_smul, flatLinear_twist, flatLinear_fibre]
  simp only [add_smul]
  abel

private def Elliptic.HigherHomology.matrixTorusHomeomorph {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℤ)
    (hBA : B * A = 1) (hAB : A * B = 1) :
    PeriodTorusHigherHomology.ProductTorus n ≃ₜ PeriodTorusHigherHomology.ProductTorus n
    where
  toFun := PeriodTorusHigherHomology.torusMatrixMap A
  invFun := PeriodTorusHigherHomology.torusMatrixMap B
  left_inv
    x := by
    change
      ((PeriodTorusHigherHomology.torusMatrixMap B).comp
            (PeriodTorusHigherHomology.torusMatrixMap A))
          x =
        x
    rw [← PeriodTorusHigherHomology.torusMatrixMap_mul, hBA,
      PeriodTorusHigherHomology.torusMatrixMap_one]
    rfl
  right_inv
    x := by
    change
      ((PeriodTorusHigherHomology.torusMatrixMap A).comp
            (PeriodTorusHigherHomology.torusMatrixMap B))
          x =
        x
    rw [← PeriodTorusHigherHomology.torusMatrixMap_mul, hAB,
      PeriodTorusHigherHomology.torusMatrixMap_one]
    rfl
  continuous_toFun := PeriodTorusHigherHomology.torusMatrixLinearMap_continuous A
  continuous_invFun := PeriodTorusHigherHomology.torusMatrixLinearMap_continuous B

private def Elliptic.HigherHomology.fibreTorusHomeomorph (j : Elliptic.Kind) :
    PeriodTorusHigherHomology.ProductTorus 3 ≃ₜ PeriodTorusHigherHomology.ProductTorus 3 :=
  matrixTorusHomeomorph (fibreMatrix j) (((fibreSL j)⁻¹ : SL(3, ℤ)) : FibreMatrix)
    (congrArg (fun C : SL(3, ℤ) => C.val) (inv_mul_cancel (fibreSL j)))
    (congrArg (fun C : SL(3, ℤ) => C.val) (mul_inv_cancel (fibreSL j)))

@[simp]
private theorem Elliptic.HigherHomology.fibreTorusHomeomorph_apply (j : Elliptic.Kind)
    (x : PeriodTorusHigherHomology.ProductTorus 3) :
    fibreTorusHomeomorph j x = PeriodTorusHigherHomology.torusMatrixMap (fibreMatrix j) x :=
  rfl

private theorem
    Elliptic.HigherHomology.fibreTorusHomeomorph_coordinateProjection (j : Elliptic.Kind)
    (k : FibreCoordinates) :
    fibreTorusHomeomorph j (PeriodTorusHigherHomology.coordinateProjection 3 k) =
      PeriodTorusHigherHomology.coordinateProjection 3 (fibreLinear j k) :=
  PeriodTorusHigherHomology.torusMatrixMap_coordinateProjection (fibreMatrix j) k

private theorem Elliptic.HigherHomology.twistBasisInvMatrix_real_mulVec (j : Elliptic.Kind)
    (x : Elliptic.RealCoordinates) :
    (twistBasisInvMatrix j).map (Int.castRingHom ℝ) *ᵥ x =
      Fin.cons (splitRealCoordinates j x).1 (splitRealCoordinates j x).2 := by
  ext i
  refine Fin.cases ?_ (fun a => ?_) i
  · cases j <;>
      simp [twistBasisInvMatrix, splitRealCoordinates_apply, Elliptic.Kind.twist, ε, ε',
        Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  · rw [Fin.cons_succ]
    cases j <;> fin_cases a <;>
        simp [twistBasisInvMatrix, splitRealCoordinates_apply, Elliptic.Kind.twist, ε, ε',
          Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
      ring

private def Elliptic.HigherHomology.splitFlatTorusHomeomorph (j : Elliptic.Kind) :
    RealTorus₄ ≃ₜ AddCircle (1 : ℝ) × PeriodTorusHigherHomology.ProductTorus 3 :=
  PeriodTorusHigherHomology.flatTorusCircleHomeomorph.trans
    ((matrixTorusHomeomorph (twistBasisInvMatrix j) (twistBasisMatrix j)
          (twistBasisMatrix_mul_twistBasisInvMatrix j)
          (twistBasisInvMatrix_mul_twistBasisMatrix j)).trans
      (PeriodTorusHigherHomology.productTorusSuccHomeomorph 3))

private theorem Elliptic.HigherHomology.splitFlatTorusHomeomorph_mkQ (j : Elliptic.Kind)
    (x : Elliptic.RealCoordinates) :
    splitFlatTorusHomeomorph j (standardLattice.mkQ x) =
      (((splitRealCoordinates j x).1 : AddCircle (1 : ℝ)),
        PeriodTorusHigherHomology.coordinateProjection 3 (splitRealCoordinates j x).2) := by
  change
    PeriodTorusHigherHomology.productTorusSuccHomeomorph 3
        (PeriodTorusHigherHomology.torusMatrixMap (twistBasisInvMatrix j)
          (PeriodTorusHigherHomology.coordinateProjection 4 x)) =
      _
  rw [PeriodTorusHigherHomology.torusMatrixMap_coordinateProjection,
    twistBasisInvMatrix_real_mulVec]
  apply Prod.ext
  · rfl
  · funext i
    rfl

private theorem Elliptic.HigherHomology.splitFlatTorusHomeomorph_symm_coordinateProjection
    (j : Elliptic.Kind) (t : ℝ) (k : FibreCoordinates) :
    (splitFlatTorusHomeomorph j).symm
        ((t : AddCircle (1 : ℝ)), PeriodTorusHigherHomology.coordinateProjection 3 k) =
      standardLattice.mkQ ((splitRealCoordinates j).symm (t, k)) := by
  apply (splitFlatTorusHomeomorph j).injective
  rw [Homeomorph.apply_symm_apply, splitFlatTorusHomeomorph_mkQ,
    ContinuousLinearEquiv.apply_symm_apply]

private theorem Elliptic.HigherHomology.splitFlatTorusHomeomorph_flatTorusAffine (j : Elliptic.Kind)
    (x : RealTorus₄) :
    splitFlatTorusHomeomorph j (Elliptic.flatTorusAffine j j.twist x) =
      ((splitFlatTorusHomeomorph j x).1 + ((1 / (j.order : ℝ) : ℝ) : AddCircle (1 : ℝ)),
        fibreTorusHomeomorph j (splitFlatTorusHomeomorph j x).2) := by
  obtain ⟨v, rfl⟩ := standardLattice.mkQ_surjective x
  simp only [Elliptic.flatTorusAffine_mkQ, splitFlatTorusHomeomorph_mkQ,
    splitRealCoordinates_flatAffine, AddCircle.coe_add, fibreTorusHomeomorph_coordinateProjection]

private theorem
    Elliptic.HigherHomology.flatTorusAffine_splitFlatTorusHomeomorph_symm (j : Elliptic.Kind)
    (t : AddCircle (1 : ℝ)) (k : PeriodTorusHigherHomology.ProductTorus 3) :
    Elliptic.flatTorusAffine j j.twist ((splitFlatTorusHomeomorph j).symm (t, k)) =
      (splitFlatTorusHomeomorph j).symm
        (t + ((1 / (j.order : ℝ) : ℝ) : AddCircle (1 : ℝ)), fibreTorusHomeomorph j k) := by
  apply (splitFlatTorusHomeomorph j).injective
  rw [splitFlatTorusHomeomorph_flatTorusAffine, Homeomorph.apply_symm_apply,
    Homeomorph.apply_symm_apply]

private def
    Elliptic.HigherHomology.splitPeriodTorusHomeomorph (j : Elliptic.Kind) (p : PeriodDomain) :
    p.Torus ≃ₜ AddCircle (1 : ℝ) × PeriodTorusHigherHomology.ProductTorus 3 :=
  (Elliptic.flatTorusPeriodHomeomorph p).symm.trans (splitFlatTorusHomeomorph j)

private theorem
    Elliptic.HigherHomology.splitPeriodTorusHomeomorph_affineBiholomorph (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) (x : p.val.Torus) :
    splitPeriodTorusHomeomorph j p.val (Elliptic.affineBiholomorph j p j.twist x) =
      ((splitPeriodTorusHomeomorph j p.val x).1 + ((1 / (j.order : ℝ) : ℝ) : AddCircle (1 : ℝ)),
        fibreTorusHomeomorph j (splitPeriodTorusHomeomorph j p.val x).2) := by
  obtain ⟨y, rfl⟩ := (Elliptic.flatTorusPeriodHomeomorph p.val).surjective x
  rw [← Elliptic.flatTorusAffine_periodHomeomorph]
  simp only [splitPeriodTorusHomeomorph, Homeomorph.trans_apply, Homeomorph.symm_apply_apply]
  exact splitFlatTorusHomeomorph_flatTorusAffine j y

private def Elliptic.HigherHomology.fibreDifference (j : Elliptic.Kind) :
    FibreLattice →ₗ[ℤ] FibreLattice :=
  (fibreMatrix j - 1).mulVecLin

private theorem Elliptic.HigherHomology.fibreDifference_three_apply (v : FibreLattice) :
    fibreDifference .three v = ![v 1 - v 0, -v 0 - 2 * v 1, v 0] := by
  ext i
  fin_cases i <;> simp [fibreDifference, fibreMatrix, dotProduct, Fin.sum_univ_succ]
  all_goals ring

private theorem Elliptic.HigherHomology.fibreDifference_four_apply (v : FibreLattice) :
    fibreDifference .four v = ![-v 0 - v 1, v 0 - v 1, v 1] := by
  ext i
  fin_cases i <;> simp [fibreDifference, fibreMatrix, dotProduct, Fin.sum_univ_succ]
  all_goals ring

private theorem Elliptic.HigherHomology.fibreDifference_mem_ker_iff (j : Elliptic.Kind)
    (v : FibreLattice) : v ∈ LinearMap.ker (fibreDifference j) ↔ v 0 = 0 ∧ v 1 = 0 := by
  rw [LinearMap.mem_ker]
  cases j with
  | three =>
    rw [fibreDifference_three_apply]
    constructor
    · intro hv
      have h0 := congrFun hv 0
      have h2 := congrFun hv 2
      change v 1 - v 0 = 0 at h0
      change v 0 = 0 at h2
      omega
    · rintro ⟨h0, h1⟩
      ext i
      fin_cases i <;> simp [h0, h1]
  | four =>
    rw [fibreDifference_four_apply]
    constructor
    · intro hv
      have h0 := congrFun hv 0
      have h2 := congrFun hv 2
      change -v 0 - v 1 = 0 at h0
      change v 1 = 0 at h2
      omega
    · rintro ⟨h0, h1⟩
      ext i
      fin_cases i <;> simp [h0, h1]

private def Elliptic.HigherHomology.fibreKernelVector : FibreLattice :=
  ![0, 0, 1]

private def Elliptic.HigherHomology.fibreKernelEquivInt (j : Elliptic.Kind) :
    LinearMap.ker (fibreDifference j) ≃ₗ[ℤ] ℤ
    where
  toFun v := v.1 2
  invFun k := ⟨![0, 0, k], (fibreDifference_mem_ker_iff j _).mpr (by simp)⟩
  left_inv
    v := by
    apply Subtype.ext
    obtain ⟨h0, h1⟩ := (fibreDifference_mem_ker_iff j v.1).mp v.2
    ext i
    fin_cases i <;> simp [h0, h1]
  right_inv k := rfl
  map_add' v w := rfl
  map_smul' k v := rfl

private def
    Elliptic.HigherHomology.fibreCoinvariantCoordinate (j : Elliptic.Kind) : FibreLattice →ₗ[ℤ] ℤ
    where
  toFun
    v :=
    match j with
    | .three => 2 * v 0 + v 1 + 3 * v 2
    | .four => v 0 + v 1 + 2 * v 2
  map_add' v w := by cases j <;> simp only [Pi.add_apply] <;> ring
  map_smul' k
    v := by cases j <;> simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply] <;> ring

@[simp]
private theorem
    Elliptic.HigherHomology.fibreCoinvariantCoordinate_section (j : Elliptic.Kind) (k : ℤ) :
    fibreCoinvariantCoordinate j ![0, k, 0] = k := by
  cases j <;> simp [fibreCoinvariantCoordinate]

private theorem Elliptic.HigherHomology.fibreCoinvariantCoordinate_surjective (j : Elliptic.Kind) :
    Function.Surjective (fibreCoinvariantCoordinate j) := fun k =>
  ⟨![0, k, 0], fibreCoinvariantCoordinate_section j k⟩

@[simp]
private theorem Elliptic.HigherHomology.fibreCoinvariantCoordinate_difference (j : Elliptic.Kind)
    (v : FibreLattice) : fibreCoinvariantCoordinate j (fibreDifference j v) = 0 := by
  cases j <;>
      simp [fibreCoinvariantCoordinate, fibreDifference_three_apply,
        fibreDifference_four_apply] <;>
    ring

private def Elliptic.HigherHomology.fibreRangePreimage (j : Elliptic.Kind) (v : FibreLattice) :
    FibreLattice :=
  match j with
  | .three => ![v 2, v 0 + v 2, 0]
  | .four => ![-v 0 - v 2, v 2, 0]

private theorem Elliptic.HigherHomology.fibreDifference_rangePreimage (j : Elliptic.Kind)
    (v : FibreLattice) (hv : fibreCoinvariantCoordinate j v = 0) :
    fibreDifference j (fibreRangePreimage j v) = v := by
  cases j with
  | three =>
    change 2 * v 0 + v 1 + 3 * v 2 = 0 at hv
    rw [fibreDifference_three_apply]
    ext i
    fin_cases i <;> simp [fibreRangePreimage]
    all_goals omega
  | four =>
    change v 0 + v 1 + 2 * v 2 = 0 at hv
    rw [fibreDifference_four_apply]
    ext i
    fin_cases i <;> simp [fibreRangePreimage]
    all_goals omega

private theorem
    Elliptic.HigherHomology.fibreDifference_range_iff (j : Elliptic.Kind) (v : FibreLattice) :
    v ∈ LinearMap.range (fibreDifference j) ↔ fibreCoinvariantCoordinate j v = 0 := by
  constructor
  · rintro ⟨w, rfl⟩
    exact fibreCoinvariantCoordinate_difference j w
  · intro hv
    exact ⟨fibreRangePreimage j v, fibreDifference_rangePreimage j v hv⟩

private theorem Elliptic.HigherHomology.fibreDifference_range_eq_ker (j : Elliptic.Kind) :
    LinearMap.range (fibreDifference j) = LinearMap.ker (fibreCoinvariantCoordinate j) := by
  ext v
  exact fibreDifference_range_iff j v

private def Elliptic.HigherHomology.fibreCokernelEquivInt (j : Elliptic.Kind) :
    (FibreLattice ⧸ LinearMap.range (fibreDifference j)) ≃ₗ[ℤ] ℤ :=
  (Submodule.quotEquivOfEq _ _ (fibreDifference_range_eq_ker j)).trans
    ((fibreCoinvariantCoordinate j).quotKerEquivOfSurjective
      (fibreCoinvariantCoordinate_surjective j))

private def Elliptic.HigherHomology.fibreSquareDifference (j : Elliptic.Kind) :
    FibreLattice →ₗ[ℤ] FibreLattice :=
  (fibreSquareMatrix j - 1).mulVecLin

@[simp]
private theorem Elliptic.HigherHomology.fibreSquareDifference_three_apply (v : FibreLattice) :
    fibreSquareDifference .three v = ![0, -v 0 - v 1 + v 2, v 0 - v 1 - 2 * v 2] := by
  ext i
  fin_cases i <;>
    simp [fibreSquareDifference, fibreSquareMatrix, dotProduct, Fin.sum_univ_succ, sub_eq_add_neg]
  all_goals ring

@[simp]
private theorem Elliptic.HigherHomology.fibreSquareDifference_four_apply (v : FibreLattice) :
    fibreSquareDifference .four v = ![0, -v 1 - v 2, v 0 + v 1 - v 2] := by
  ext i
  fin_cases i <;>
    simp [fibreSquareDifference, fibreSquareMatrix, dotProduct, Fin.sum_univ_succ, sub_eq_add_neg]
  ring

@[simp]
private theorem Elliptic.HigherHomology.fibreSquareDifference_apply_zero (j : Elliptic.Kind)
    (v : FibreLattice) : fibreSquareDifference j v 0 = 0 := by cases j <;> simp

private def Elliptic.HigherHomology.fibreSquareKernelVector : Elliptic.Kind → FibreLattice
  | .three => ![3, -1, 2]
  | .four => ![2, -1, 1]

@[simp]
private theorem Elliptic.HigherHomology.fibreSquareKernelVector_one (j : Elliptic.Kind) :
    fibreSquareKernelVector j 1 = -1 := by cases j <;> rfl

@[simp]
private theorem Elliptic.HigherHomology.fibreSquareDifference_kernelVector (j : Elliptic.Kind) :
    fibreSquareDifference j (fibreSquareKernelVector j) = 0 := by
  cases j <;> ext i <;> fin_cases i <;> simp [fibreSquareKernelVector]

private theorem Elliptic.HigherHomology.fibreSquareDifference_mem_ker_iff (j : Elliptic.Kind)
    (v : FibreLattice) :
    v ∈ LinearMap.ker (fibreSquareDifference j) ↔ v = (-v 1) • fibreSquareKernelVector j := by
  constructor
  · intro hv
    have h : fibreSquareDifference j v = 0 := hv
    cases j
    · have h₁ : -v 0 - v 1 + v 2 = 0 := by simpa [fibreSquareKernelVector] using congrFun h 1
      have h₂ : v 0 - v 1 - 2 * v 2 = 0 := by simpa [fibreSquareKernelVector] using congrFun h 2
      ext i
      fin_cases i <;> simp [fibreSquareKernelVector] <;> omega
    · have h₁ : -v 1 - v 2 = 0 := by simpa [fibreSquareKernelVector] using congrFun h 1
      have h₂ : v 0 + v 1 - v 2 = 0 := by simpa [fibreSquareKernelVector] using congrFun h 2
      ext i
      fin_cases i <;> simp [fibreSquareKernelVector] <;> omega
  · intro hv
    rw [LinearMap.mem_ker, hv, map_smul, fibreSquareDifference_kernelVector, smul_zero]

private def Elliptic.HigherHomology.fibreSquareKernelEquivInt (j : Elliptic.Kind) :
    LinearMap.ker (fibreSquareDifference j) ≃ₗ[ℤ] ℤ
    where
  toFun v := -(v : FibreLattice) 1
  invFun
    k :=
    ⟨k • fibreSquareKernelVector j, by
      rw [LinearMap.mem_ker, map_smul, fibreSquareDifference_kernelVector, smul_zero]⟩
  left_inv
    v := by
    apply Subtype.ext
    exact ((fibreSquareDifference_mem_ker_iff j v).mp v.property).symm
  right_inv
    k := by
    change -(k • fibreSquareKernelVector j) 1 = k
    simp
  map_add' v
    w := by
    change
      -((v : FibreLattice) 1 + (w : FibreLattice) 1) =
        -(v : FibreLattice) 1 + -(w : FibreLattice) 1
    exact neg_add _ _
  map_smul' k
    v := by
    change -(k * (v : FibreLattice) 1) = k * (-(v : FibreLattice) 1)
    ring

private def
    Elliptic.HigherHomology.fibreSquareRangePreimage (j : Elliptic.Kind) (w : FibreLattice) :
    FibreLattice :=
  match j with
  | .three => ![-2 * w 1 - w 2, 0, -w 1 - w 2]
  | .four => ![w 1 + w 2, -w 1, 0]

private theorem Elliptic.HigherHomology.fibreSquareDifference_rangePreimage (j : Elliptic.Kind)
    (w : FibreLattice) (hw : w 0 = 0) :
    fibreSquareDifference j (fibreSquareRangePreimage j w) = w := by
  cases j <;> ext i <;> fin_cases i <;> simp [fibreSquareRangePreimage, hw] <;> ring

private theorem Elliptic.HigherHomology.fibreSquareDifference_range_iff (j : Elliptic.Kind)
    (w : FibreLattice) : w ∈ LinearMap.range (fibreSquareDifference j) ↔ w 0 = 0 := by
  constructor
  · rintro ⟨v, rfl⟩
    exact fibreSquareDifference_apply_zero j v
  · intro hw
    exact ⟨fibreSquareRangePreimage j w, fibreSquareDifference_rangePreimage j w hw⟩

private def Elliptic.HigherHomology.fibreSquareFirstCoordinate : FibreLattice →ₗ[ℤ] ℤ :=
  LinearMap.proj 0

@[simp]
private theorem Elliptic.HigherHomology.fibreSquareFirstCoordinate_apply (w : FibreLattice) :
    fibreSquareFirstCoordinate w = w 0 :=
  rfl

private theorem Elliptic.HigherHomology.fibreSquareFirstCoordinate_surjective :
    Function.Surjective fibreSquareFirstCoordinate := by
  intro k
  exact ⟨![k, 0, 0], rfl⟩

private theorem Elliptic.HigherHomology.fibreSquareDifference_range_eq_ker (j : Elliptic.Kind) :
    LinearMap.range (fibreSquareDifference j) = LinearMap.ker fibreSquareFirstCoordinate := by
  ext w
  rw [fibreSquareDifference_range_iff, LinearMap.mem_ker, fibreSquareFirstCoordinate_apply]

private def Elliptic.HigherHomology.fibreSquareCokernelEquivInt (j : Elliptic.Kind) :
    (FibreLattice ⧸ LinearMap.range (fibreSquareDifference j)) ≃ₗ[ℤ] ℤ :=
  (Submodule.quotEquivOfEq _ _ (fibreSquareDifference_range_eq_ker j)).trans
    (fibreSquareFirstCoordinate.quotKerEquivOfSurjective fibreSquareFirstCoordinate_surjective)

private theorem Elliptic.HigherHomology.matrixInverseDifference_mul (M : FibreMatrix)
    (hM : IsUnit M.det) : (1 - M⁻¹) * M = M - 1 := by
  rw [sub_mul, one_mul, Matrix.nonsing_inv_mul M hM]

private theorem Elliptic.HigherHomology.matrixInverseDifference_ker_eq (M : FibreMatrix)
    (hM : IsUnit M.det) : LinearMap.ker (1 - M⁻¹).mulVecLin = LinearMap.ker (M - 1).mulVecLin := by
  ext v
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.one_mulVec,
    sub_eq_zero]
  constructor
  · intro hv
    have h := congrArg (fun w : FibreLattice => M *ᵥ w) hv
    simpa only [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M hM, Matrix.one_mulVec] using h
  · intro hv
    have h := congrArg (fun w : FibreLattice => M⁻¹ *ᵥ w) hv
    simpa only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul M hM, Matrix.one_mulVec] using h

private theorem Elliptic.HigherHomology.matrixInverseDifference_range_eq (M : FibreMatrix)
    (hM : IsUnit M.det) :
    LinearMap.range (1 - M⁻¹).mulVecLin = LinearMap.range (M - 1).mulVecLin := by
  ext v
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨M⁻¹ *ᵥ w, ?_⟩
    change (M - 1) *ᵥ M⁻¹ *ᵥ w = v
    rw [Matrix.mulVec_mulVec, sub_mul, Matrix.mul_nonsing_inv M hM, one_mul]
    exact hw
  · rintro ⟨w, hw⟩
    refine ⟨M *ᵥ w, ?_⟩
    change (1 - M⁻¹) *ᵥ M *ᵥ w = v
    rw [Matrix.mulVec_mulVec, matrixInverseDifference_mul M hM]
    exact hw

private def Elliptic.HigherHomology.fibreInverseDifference (j : Elliptic.Kind) :
    FibreLattice →ₗ[ℤ] FibreLattice :=
  (1 - (fibreMatrix j)⁻¹).mulVecLin

private def Elliptic.HigherHomology.fibreSquareInverseDifference (j : Elliptic.Kind) :
    FibreLattice →ₗ[ℤ] FibreLattice :=
  (1 - (fibreSquareMatrix j)⁻¹).mulVecLin

private theorem Elliptic.HigherHomology.fibreInverseDifference_ker_eq (j : Elliptic.Kind) :
    LinearMap.ker (fibreInverseDifference j) = LinearMap.ker (fibreDifference j) :=
  matrixInverseDifference_ker_eq _ (by simp [fibreMatrix_det])

private theorem Elliptic.HigherHomology.fibreInverseDifference_range_eq (j : Elliptic.Kind) :
    LinearMap.range (fibreInverseDifference j) = LinearMap.range (fibreDifference j) :=
  matrixInverseDifference_range_eq _ (by simp [fibreMatrix_det])

private theorem Elliptic.HigherHomology.fibreSquareInverseDifference_ker_eq (j : Elliptic.Kind) :
    LinearMap.ker (fibreSquareInverseDifference j) = LinearMap.ker (fibreSquareDifference j) :=
  matrixInverseDifference_ker_eq _ (by simp [fibreSquareMatrix_det])

private theorem Elliptic.HigherHomology.fibreSquareInverseDifference_range_eq (j : Elliptic.Kind) :
    LinearMap.range (fibreSquareInverseDifference j) =
      LinearMap.range (fibreSquareDifference j) :=
  matrixInverseDifference_range_eq _ (by simp [fibreSquareMatrix_det])

private def Elliptic.HigherHomology.fibreInverseKernelEquivInt (j : Elliptic.Kind) :
    LinearMap.ker (fibreInverseDifference j) ≃ₗ[ℤ] ℤ :=
  (LinearEquiv.ofEq _ _ (fibreInverseDifference_ker_eq j)).trans (fibreKernelEquivInt j)

private def Elliptic.HigherHomology.fibreInverseCokernelEquivInt (j : Elliptic.Kind) :
    (FibreLattice ⧸ LinearMap.range (fibreInverseDifference j)) ≃ₗ[ℤ] ℤ :=
  (Submodule.quotEquivOfEq _ _ (fibreInverseDifference_range_eq j)).trans
    (fibreCokernelEquivInt j)

private def Elliptic.HigherHomology.fibreSquareInverseKernelEquivInt (j : Elliptic.Kind) :
    LinearMap.ker (fibreSquareInverseDifference j) ≃ₗ[ℤ] ℤ :=
  (LinearEquiv.ofEq _ _ (fibreSquareInverseDifference_ker_eq j)).trans
    (fibreSquareKernelEquivInt j)

private def Elliptic.HigherHomology.fibreSquareInverseCokernelEquivInt (j : Elliptic.Kind) :
    (FibreLattice ⧸ LinearMap.range (fibreSquareInverseDifference j)) ≃ₗ[ℤ] ℤ :=
  (Submodule.quotEquivOfEq _ _ (fibreSquareInverseDifference_range_eq j)).trans
    (fibreSquareCokernelEquivInt j)

private def Elliptic.HigherHomology.inclusionMatrix_mo1973_21667 : Matrix (Fin 4) (Fin 3) ℤ :=
  !![0, 0, 0; 1, 0, 0; 0, 1, 0; 0, 0, 1]

private def Elliptic.HigherHomology.projectionMatrix_mo1973_21668 : Matrix (Fin 3) (Fin 4) ℤ :=
  !![0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

private theorem Elliptic.HigherHomology.projection_inclusion_mo1973_21669 :
    projectionMatrix_mo1973_21668 * inclusionMatrix_mo1973_21667 = 1 := by decide

private theorem Elliptic.HigherHomology.projection_inclusion_mulVec_mo1973_21670
    (v : FibreLattice) :
    projectionMatrix_mo1973_21668 *ᵥ (inclusionMatrix_mo1973_21667 *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, projection_inclusion_mo1973_21669, Matrix.one_mulVec]

private theorem Elliptic.HigherHomology.projected_coordinateH1_four_mo1973_21671 :
    (FirstHurewicz.inducedHomology
            (PeriodTorusHigherHomology.torusMatrixMap projectionMatrix_mo1973_21668)).comp
        ((PeriodTorusHigherHomology.coordinateH1 4).comp inclusionMatrix_mo1973_21667.mulVecLin) =
      PeriodTorusHigherHomology.coordinateH1 3 := by
  apply (Pi.basisFun ℤ (Fin 3)).ext
  intro i
  simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply]
  rw [PeriodTorusHigherHomology.coordinateH1_four_apply (Elliptic.examplePeriod .four),
    PeriodTorusHigherHomology.torusMatrixMap_coordinatePeriodHomology,
    projection_inclusion_mulVec_mo1973_21670, PeriodTorusHigherHomology.coordinateH1_basis]
  simp only [Pi.basisFun_apply]

private theorem Elliptic.HigherHomology.coordinateH1_three_apply (v : FibreLattice) :
    PeriodTorusHigherHomology.coordinateH1 3 v =
      FirstHurewicz.loopHomologyClass (PeriodTorusHigherHomology.coordinatePeriodLoop 3 v) := by
  rw [← projected_coordinateH1_four_mo1973_21671]
  change
    FirstHurewicz.inducedHomology
        (PeriodTorusHigherHomology.torusMatrixMap projectionMatrix_mo1973_21668)
        (PeriodTorusHigherHomology.coordinateH1 4 (inclusionMatrix_mo1973_21667 *ᵥ v)) =
      _
  rw [PeriodTorusHigherHomology.coordinateH1_four_apply (Elliptic.examplePeriod .four),
    PeriodTorusHigherHomology.torusMatrixMap_coordinatePeriodHomology,
    projection_inclusion_mulVec_mo1973_21670]

private theorem Elliptic.HigherHomology.projection_inclusion_homology_mo1973_21673
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 1) :
    FirstHurewicz.inducedHomology
        (PeriodTorusHigherHomology.torusMatrixMap projectionMatrix_mo1973_21668)
        (FirstHurewicz.inducedHomology
          (PeriodTorusHigherHomology.torusMatrixMap inclusionMatrix_mo1973_21667) a) =
      a := by
  calc
    _ =
        FirstHurewicz.inducedHomology
          ((PeriodTorusHigherHomology.torusMatrixMap projectionMatrix_mo1973_21668).comp
            (PeriodTorusHigherHomology.torusMatrixMap inclusionMatrix_mo1973_21667))
          a := by rw [FirstHurewicz.inducedHomology_comp, LinearMap.comp_apply]
    _ = a := by
      rw [← PeriodTorusHigherHomology.torusMatrixMap_mul, projection_inclusion_mo1973_21669,
        PeriodTorusHigherHomology.torusMatrixMap_one, FirstHurewicz.inducedHomology_id,
        LinearMap.id_apply]

private theorem Elliptic.HigherHomology.coordinateH1_three_bijective :
    Function.Bijective (PeriodTorusHigherHomology.coordinateH1 3) := by
  constructor
  · intro v w hvw
    have h :=
      congrArg
        (FirstHurewicz.inducedHomology
          (PeriodTorusHigherHomology.torusMatrixMap inclusionMatrix_mo1973_21667))
        hvw
    rw [coordinateH1_three_apply, coordinateH1_three_apply,
      PeriodTorusHigherHomology.torusMatrixMap_coordinatePeriodHomology,
      PeriodTorusHigherHomology.torusMatrixMap_coordinatePeriodHomology] at h
    have h' : inclusionMatrix_mo1973_21667 *ᵥ v = inclusionMatrix_mo1973_21667 *ᵥ w :=
      (PeriodTorusHigherHomology.coordinateH1_four_bijective
            (Elliptic.examplePeriod .four)).injective
        (by
          simpa only [PeriodTorusHigherHomology.coordinateH1_four_apply
                (Elliptic.examplePeriod .four)] using
            h)
    have h'' := congrArg (fun u => projectionMatrix_mo1973_21668 *ᵥ u) h'
    simpa only [projection_inclusion_mulVec_mo1973_21670] using h''
  · intro a
    obtain ⟨v, hv⟩ :=
      (PeriodTorusHigherHomology.coordinateH1_four_bijective
            (Elliptic.examplePeriod .four)).surjective
        (FirstHurewicz.inducedHomology
          (PeriodTorusHigherHomology.torusMatrixMap inclusionMatrix_mo1973_21667) a)
    refine ⟨projectionMatrix_mo1973_21668 *ᵥ v, ?_⟩
    calc
      _ =
          FirstHurewicz.inducedHomology
            (PeriodTorusHigherHomology.torusMatrixMap projectionMatrix_mo1973_21668)
            (PeriodTorusHigherHomology.coordinateH1 4 v) := by
        rw [coordinateH1_three_apply,
          PeriodTorusHigherHomology.coordinateH1_four_apply (Elliptic.examplePeriod .four),
          PeriodTorusHigherHomology.torusMatrixMap_coordinatePeriodHomology]
      _ = a := by rw [hv, projection_inclusion_homology_mo1973_21673]

private theorem Elliptic.HigherHomology.coordinateH1_three_matrix_natural (A : FibreMatrix)
    (v : FibreLattice) :
    SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusMatrixMap A) 1
        (PeriodTorusHigherHomology.coordinateH1 3 v) =
      PeriodTorusHigherHomology.coordinateH1 3 (A *ᵥ v) := by
  rw [SingularMayerVietoris.singularHomologyMap_one, coordinateH1_three_apply,
    coordinateH1_three_apply, PeriodTorusHigherHomology.torusMatrixMap_coordinatePeriodHomology]

private def Elliptic.HigherHomology.torusH1Equiv :
    SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 1 ≃ₗ[ℤ]
      FibreLattice :=
  (LinearEquiv.ofBijective (PeriodTorusHigherHomology.coordinateH1 3)
      coordinateH1_three_bijective).symm

private theorem Elliptic.HigherHomology.torusH1Equiv_symm_apply_loop (v : FibreLattice) :
    torusH1Equiv.symm v =
      FirstHurewicz.loopHomologyClass (PeriodTorusHigherHomology.coordinatePeriodLoop 3 v) :=
  coordinateH1_three_apply v

@[simp]
private theorem Elliptic.HigherHomology.torusH1Equiv_coordinateH1 (v : FibreLattice) :
    torusH1Equiv (PeriodTorusHigherHomology.coordinateH1 3 v) = v :=
  torusH1Equiv.apply_symm_apply v

private theorem Elliptic.HigherHomology.torusH1Equiv_matrix_natural (A : FibreMatrix)
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 1) :
    torusH1Equiv
        (SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusMatrixMap A) 1
          a) =
      A *ᵥ torusH1Equiv a := by
  obtain ⟨v, rfl⟩ := coordinateH1_three_bijective.surjective a
  rw [coordinateH1_three_matrix_natural, torusH1Equiv_coordinateH1, torusH1Equiv_coordinateH1]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def Elliptic.HigherHomology.markedWedgeTwo (G : Type) [TopologicalSpace G] [AddCommGroup G]
    [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)] {M : Type*}
    [AddCommGroup M] [Module ℤ M] (c : M →ₗ[ℤ] SingularMayerVietoris.SingularHomology G 1) :
    (⋀[ℤ]^2 M) →ₗ[ℤ] SingularMayerVietoris.SingularHomology G 2 :=
  (PeriodTorusHigherHomologyPontryagin.homologyWedgeTwo G).comp (exteriorPower.map 2 c)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def
    Elliptic.HigherHomology.markedWedgeThree (G : Type) [TopologicalSpace G] [AddCommGroup G]
    [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)] {M : Type*}
    [AddCommGroup M] [Module ℤ M] (c : M →ₗ[ℤ] SingularMayerVietoris.SingularHomology G 1) :
    (⋀[ℤ]^3 M) →ₗ[ℤ] SingularMayerVietoris.SingularHomology G 3 :=
  (PeriodTorusHigherHomologyPontryagin.homologyWedgeThree G).comp (exteriorPower.map 3 c)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
private theorem Elliptic.HigherHomology.markedWedgeTwo_apply_ιMulti (G : Type) [TopologicalSpace G]
    [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)] {M : Type*}
    [AddCommGroup M] [Module ℤ M] (c : M →ₗ[ℤ] SingularMayerVietoris.SingularHomology G 1)
    (v : Fin 2 → M) :
    markedWedgeTwo G c (exteriorPower.ιMulti ℤ 2 v) =
      PeriodTorusHigherHomologyPontryagin.product11 G (c (v 0)) (c (v 1)) := by
  change
    PeriodTorusHigherHomologyPontryagin.homologyWedgeTwo G
        (exteriorPower.map 2 c (exteriorPower.ιMulti ℤ 2 v)) =
      _
  rw [exteriorPower.map_apply_ιMulti,
    PeriodTorusHigherHomologyPontryagin.homologyWedgeTwo_apply_ιMulti]
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
private theorem
    Elliptic.HigherHomology.markedWedgeThree_apply_ιMulti (G : Type) [TopologicalSpace G]
    [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)] {M : Type*}
    [AddCommGroup M] [Module ℤ M] (c : M →ₗ[ℤ] SingularMayerVietoris.SingularHomology G 1)
    (v : Fin 3 → M) :
    markedWedgeThree G c (exteriorPower.ιMulti ℤ 3 v) =
      PeriodTorusHigherHomologyPontryagin.tripleProduct G (c (v 0)) (c (v 1)) (c (v 2)) := by
  change
    PeriodTorusHigherHomologyPontryagin.homologyWedgeThree G
        (exteriorPower.map 3 c (exteriorPower.ιMulti ℤ 3 v)) =
      _
  rw [exteriorPower.map_apply_ιMulti,
    PeriodTorusHigherHomologyPontryagin.homologyWedgeThree_apply_ιMulti]
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    Elliptic.HigherHomology.product11_mem_range_markedWedgeTwo (G : Type) [TopologicalSpace G]
    [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)] {M : Type*}
    [AddCommGroup M] [Module ℤ M] (c : M →ₗ[ℤ] SingularMayerVietoris.SingularHomology G 1)
    (hc : Function.Surjective c) (a b : SingularMayerVietoris.SingularHomology G 1) :
    PeriodTorusHigherHomologyPontryagin.product11 G a b ∈ LinearMap.range (markedWedgeTwo G c) := by
  obtain ⟨v, rfl⟩ := hc a
  obtain ⟨w, rfl⟩ := hc b
  refine ⟨exteriorPower.ιMulti ℤ 2 ![v, w], ?_⟩
  simp

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem Elliptic.HigherHomology.tripleProduct_mem_range_markedWedgeThree (G : Type)
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)] {M : Type*}
    [AddCommGroup M] [Module ℤ M] (c : M →ₗ[ℤ] SingularMayerVietoris.SingularHomology G 1)
    (hc : Function.Surjective c) (a b d : SingularMayerVietoris.SingularHomology G 1) :
    PeriodTorusHigherHomologyPontryagin.tripleProduct G a b d ∈
      LinearMap.range (markedWedgeThree G c) := by
  obtain ⟨v, rfl⟩ := hc a
  obtain ⟨w, rfl⟩ := hc b
  obtain ⟨u, rfl⟩ := hc d
  refine ⟨exteriorPower.ιMulti ℤ 3 ![v, w, u], ?_⟩
  simp

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem Elliptic.HigherHomology.markedWedgeTwo_natural {G H : Type} [TopologicalSpace G]
    [AddCommGroup G] [IsTopologicalAddGroup G] [TopologicalSpace H] [AddCommGroup H]
    [IsTopologicalAddGroup H]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology H 2)] {M N : Type*}
    [AddCommGroup M] [Module ℤ M] [AddCommGroup N] [Module ℤ N] (f : C(G, H))
    (hf : ∀ x y, f (x + y) = f x + f y) (c : M →ₗ[ℤ] SingularMayerVietoris.SingularHomology G 1)
    (d : N →ₗ[ℤ] SingularMayerVietoris.SingularHomology H 1) (A : M →ₗ[ℤ] N)
    (hmark : ∀ v, SingularMayerVietoris.singularHomologyMap f 1 (c v) = d (A v)) :
    (SingularMayerVietoris.singularHomologyMap f 2).comp (markedWedgeTwo G c) =
      (markedWedgeTwo H d).comp (exteriorPower.map 2 A) := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  change
    SingularMayerVietoris.singularHomologyMap f 2
        (markedWedgeTwo G c (exteriorPower.ιMulti ℤ 2 v)) =
      markedWedgeTwo H d (exteriorPower.map 2 A (exteriorPower.ιMulti ℤ 2 v))
  rw [exteriorPower.map_apply_ιMulti, markedWedgeTwo_apply_ιMulti, markedWedgeTwo_apply_ιMulti,
    PeriodTorusHigherHomologyPontryagin.product_natural f hf 1, hmark, hmark]
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem Elliptic.HigherHomology.markedWedgeThree_natural {G H : Type} [TopologicalSpace G]
    [AddCommGroup G] [IsTopologicalAddGroup G] [TopologicalSpace H] [AddCommGroup H]
    [IsTopologicalAddGroup H]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology H 2)] {M N : Type*}
    [AddCommGroup M] [Module ℤ M] [AddCommGroup N] [Module ℤ N] (f : C(G, H))
    (hf : ∀ x y, f (x + y) = f x + f y) (c : M →ₗ[ℤ] SingularMayerVietoris.SingularHomology G 1)
    (d : N →ₗ[ℤ] SingularMayerVietoris.SingularHomology H 1) (A : M →ₗ[ℤ] N)
    (hmark : ∀ v, SingularMayerVietoris.singularHomologyMap f 1 (c v) = d (A v)) :
    (SingularMayerVietoris.singularHomologyMap f 3).comp (markedWedgeThree G c) =
      (markedWedgeThree H d).comp (exteriorPower.map 3 A) := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  change
    SingularMayerVietoris.singularHomologyMap f 3
        (markedWedgeThree G c (exteriorPower.ιMulti ℤ 3 v)) =
      markedWedgeThree H d (exteriorPower.map 3 A (exteriorPower.ιMulti ℤ 3 v))
  rw [exteriorPower.map_apply_ιMulti, markedWedgeThree_apply_ιMulti,
    markedWedgeThree_apply_ιMulti, PeriodTorusHigherHomologyPontryagin.tripleProduct_natural f hf,
    hmark, hmark, hmark]
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem Elliptic.HigherHomology.map_topClass_two_mem_range_markedWedgeTwo {G : Type}
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)] {M : Type*}
    [AddCommGroup M] [Module ℤ M] (c : M →ₗ[ℤ] SingularMayerVietoris.SingularHomology G 1)
    (hc : Function.Surjective c) (f : C(PeriodTorusHigherHomology.ProductTorus 2, G))
    (hf : ∀ x y, f (x + y) = f x + f y) :
    SingularMayerVietoris.singularHomologyMap f 2
        (PeriodTorusHigherHomology.productTorusTopClass 2) ∈
      LinearMap.range (markedWedgeTwo G c) := by
  obtain ⟨a, b, hab⟩ := PeriodTorusHigherHomology.productTorusTopClass_two_is_product
  rw [hab, PeriodTorusHigherHomologyPontryagin.product_natural f hf 1]
  exact product11_mem_range_markedWedgeTwo G c hc _ _

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem Elliptic.HigherHomology.map_topClass_three_mem_range_markedWedgeThree {G : Type}
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)] {M : Type*}
    [AddCommGroup M] [Module ℤ M] (c : M →ₗ[ℤ] SingularMayerVietoris.SingularHomology G 1)
    (hc : Function.Surjective c) (f : C(PeriodTorusHigherHomology.ProductTorus 3, G))
    (hf : ∀ x y, f (x + y) = f x + f y) :
    SingularMayerVietoris.singularHomologyMap f 3
        (PeriodTorusHigherHomology.productTorusTopClass 3) ∈
      LinearMap.range (markedWedgeThree G c) := by
  obtain ⟨a, b, d, habd⟩ := PeriodTorusHigherHomology.productTorusTopClass_three_is_tripleProduct
  rw [habd, PeriodTorusHigherHomologyPontryagin.tripleProduct_natural f hf]
  exact tripleProduct_mem_range_markedWedgeThree G c hc _ _ _

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    Elliptic.HigherHomology.coordinateTorusClassAlong_mem_range_markedWedgeTwo {G : Type}
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)] {M : Type*}
    [AddCommGroup M] [Module ℤ M] {r : ℕ} (e : G ≃ₜ PeriodTorusHigherHomology.ProductTorus r)
    (he : ∀ x y, e (x + y) = e x + e y) (c : M →ₗ[ℤ] SingularMayerVietoris.SingularHomology G 1)
    (hc : Function.Surjective c) (i : Fin (r.choose 2)) :
    PeriodTorusHigherHomology.coordinateTorusClassAlong e 2 i ∈
      LinearMap.range (markedWedgeTwo G c) :=
  map_topClass_two_mem_range_markedWedgeTwo c hc
    (PeriodTorusHigherHomology.coordinateTorusMapAlong e 2 i)
    (PeriodTorusHigherHomology.coordinateTorusMapAlong_add e he 2 i)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    Elliptic.HigherHomology.coordinateTorusClassAlong_mem_range_markedWedgeThree {G : Type}
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)] {M : Type*}
    [AddCommGroup M] [Module ℤ M] {r : ℕ} (e : G ≃ₜ PeriodTorusHigherHomology.ProductTorus r)
    (he : ∀ x y, e (x + y) = e x + e y) (c : M →ₗ[ℤ] SingularMayerVietoris.SingularHomology G 1)
    (hc : Function.Surjective c) (i : Fin (r.choose 3)) :
    PeriodTorusHigherHomology.coordinateTorusClassAlong e 3 i ∈
      LinearMap.range (markedWedgeThree G c) :=
  map_topClass_three_mem_range_markedWedgeThree c hc
    (PeriodTorusHigherHomology.coordinateTorusMapAlong e 3 i)
    (PeriodTorusHigherHomology.coordinateTorusMapAlong_add e he 3 i)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem Elliptic.HigherHomology.markedWedgeTwo_surjective_of_torusHomeomorph {G : Type}
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)] {M : Type*}
    [AddCommGroup M] [Module ℤ M] {r : ℕ} (e : G ≃ₜ PeriodTorusHigherHomology.ProductTorus r)
    (he : ∀ x y, e (x + y) = e x + e y) (c : M →ₗ[ℤ] SingularMayerVietoris.SingularHomology G 1)
    (hc : Function.Surjective c) : Function.Surjective (markedWedgeTwo G c) :=
  PeriodTorusHigherHomology.surjective_of_coordinateTorusClassAlong_mem_range e 2
    (markedWedgeTwo G c) (coordinateTorusClassAlong_mem_range_markedWedgeTwo e he c hc)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem Elliptic.HigherHomology.markedWedgeThree_surjective_of_torusHomeomorph {G : Type}
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)] {M : Type*}
    [AddCommGroup M] [Module ℤ M] {r : ℕ} (e : G ≃ₜ PeriodTorusHigherHomology.ProductTorus r)
    (he : ∀ x y, e (x + y) = e x + e y) (c : M →ₗ[ℤ] SingularMayerVietoris.SingularHomology G 1)
    (hc : Function.Surjective c) : Function.Surjective (markedWedgeThree G c) :=
  PeriodTorusHigherHomology.surjective_of_coordinateTorusClassAlong_mem_range e 3
    (markedWedgeThree G c) (coordinateTorusClassAlong_mem_range_markedWedgeThree e he c hc)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def Elliptic.HigherHomology.torusWedgeTwo :
    (⋀[ℤ]^2 FibreLattice) →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 2 := by
  letI := PeriodTorusHigherHomology.productTorus_homology_torsionFree 3 2
  exact
    markedWedgeTwo (PeriodTorusHigherHomology.ProductTorus 3)
      (PeriodTorusHigherHomology.coordinateH1 3)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def Elliptic.HigherHomology.torusWedgeThree :
    (⋀[ℤ]^3 FibreLattice) →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 3 := by
  letI := PeriodTorusHigherHomology.productTorus_homology_torsionFree 3 2
  exact
    markedWedgeThree (PeriodTorusHigherHomology.ProductTorus 3)
      (PeriodTorusHigherHomology.coordinateH1 3)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
private theorem Elliptic.HigherHomology.torusWedgeTwo_ιMulti (v : Fin 2 → FibreLattice) :
    torusWedgeTwo (exteriorPower.ιMulti ℤ 2 v) =
      PeriodTorusHigherHomologyPontryagin.product11 (PeriodTorusHigherHomology.ProductTorus 3)
        (PeriodTorusHigherHomology.coordinateH1 3 (v 0))
        (PeriodTorusHigherHomology.coordinateH1 3 (v 1)) := by
  let := PeriodTorusHigherHomology.productTorus_homology_torsionFree 3 2
  exact
    markedWedgeTwo_apply_ιMulti (PeriodTorusHigherHomology.ProductTorus 3)
      (PeriodTorusHigherHomology.coordinateH1 3) v

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
private theorem Elliptic.HigherHomology.torusWedgeThree_ιMulti (v : Fin 3 → FibreLattice) :
    torusWedgeThree (exteriorPower.ιMulti ℤ 3 v) =
      PeriodTorusHigherHomologyPontryagin.tripleProduct (PeriodTorusHigherHomology.ProductTorus 3)
        (PeriodTorusHigherHomology.coordinateH1 3 (v 0))
        (PeriodTorusHigherHomology.coordinateH1 3 (v 1))
        (PeriodTorusHigherHomology.coordinateH1 3 (v 2)) := by
  let := PeriodTorusHigherHomology.productTorus_homology_torsionFree 3 2
  exact
    markedWedgeThree_apply_ιMulti (PeriodTorusHigherHomology.ProductTorus 3)
      (PeriodTorusHigherHomology.coordinateH1 3) v

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem Elliptic.HigherHomology.torusWedgeTwo_ιMulti_loops (v : Fin 2 → FibreLattice) :
    torusWedgeTwo (exteriorPower.ιMulti ℤ 2 v) =
      PeriodTorusHigherHomologyPontryagin.product11 (PeriodTorusHigherHomology.ProductTorus 3)
        (FirstHurewicz.loopHomologyClass (PeriodTorusHigherHomology.coordinatePeriodLoop 3 (v 0)))
        (FirstHurewicz.loopHomologyClass
          (PeriodTorusHigherHomology.coordinatePeriodLoop 3 (v 1))) := by
  rw [torusWedgeTwo_ιMulti, coordinateH1_three_apply, coordinateH1_three_apply]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem Elliptic.HigherHomology.torusWedgeThree_ιMulti_loops (v : Fin 3 → FibreLattice) :
    torusWedgeThree (exteriorPower.ιMulti ℤ 3 v) =
      PeriodTorusHigherHomologyPontryagin.tripleProduct (PeriodTorusHigherHomology.ProductTorus 3)
        (FirstHurewicz.loopHomologyClass (PeriodTorusHigherHomology.coordinatePeriodLoop 3 (v 0)))
        (FirstHurewicz.loopHomologyClass (PeriodTorusHigherHomology.coordinatePeriodLoop 3 (v 1)))
        (FirstHurewicz.loopHomologyClass
          (PeriodTorusHigherHomology.coordinatePeriodLoop 3 (v 2))) := by
  rw [torusWedgeThree_ιMulti, coordinateH1_three_apply, coordinateH1_three_apply,
    coordinateH1_three_apply]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem Elliptic.HigherHomology.torusWedgeTwo_natural
    (f : C(PeriodTorusHigherHomology.ProductTorus 3, PeriodTorusHigherHomology.ProductTorus 3))
    (hf : ∀ x y, f (x + y) = f x + f y) (A : FibreLattice →ₗ[ℤ] FibreLattice)
    (hmark :
      ∀ v,
        SingularMayerVietoris.singularHomologyMap f 1
            (PeriodTorusHigherHomology.coordinateH1 3 v) =
          PeriodTorusHigherHomology.coordinateH1 3 (A v)) :
    (SingularMayerVietoris.singularHomologyMap f 2).comp torusWedgeTwo =
      torusWedgeTwo.comp (exteriorPower.map 2 A) := by
  let := PeriodTorusHigherHomology.productTorus_homology_torsionFree 3 2
  exact
    markedWedgeTwo_natural f hf (PeriodTorusHigherHomology.coordinateH1 3)
      (PeriodTorusHigherHomology.coordinateH1 3) A hmark

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem Elliptic.HigherHomology.torusWedgeThree_natural
    (f : C(PeriodTorusHigherHomology.ProductTorus 3, PeriodTorusHigherHomology.ProductTorus 3))
    (hf : ∀ x y, f (x + y) = f x + f y) (A : FibreLattice →ₗ[ℤ] FibreLattice)
    (hmark :
      ∀ v,
        SingularMayerVietoris.singularHomologyMap f 1
            (PeriodTorusHigherHomology.coordinateH1 3 v) =
          PeriodTorusHigherHomology.coordinateH1 3 (A v)) :
    (SingularMayerVietoris.singularHomologyMap f 3).comp torusWedgeThree =
      torusWedgeThree.comp (exteriorPower.map 3 A) := by
  let := PeriodTorusHigherHomology.productTorus_homology_torsionFree 3 2
  exact
    markedWedgeThree_natural f hf (PeriodTorusHigherHomology.coordinateH1 3)
      (PeriodTorusHigherHomology.coordinateH1 3) A hmark

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    Elliptic.HigherHomology.torusWedgeTwo_surjective : Function.Surjective torusWedgeTwo := by
  let := PeriodTorusHigherHomology.productTorus_homology_torsionFree 3 2
  exact
    markedWedgeTwo_surjective_of_torusHomeomorph
      (Homeomorph.refl (PeriodTorusHigherHomology.ProductTorus 3)) (fun _ _ => rfl)
      (PeriodTorusHigherHomology.coordinateH1 3) coordinateH1_three_bijective.surjective

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem Elliptic.HigherHomology.torusWedgeThree_surjective :
    Function.Surjective torusWedgeThree := by
  let := PeriodTorusHigherHomology.productTorus_homology_torsionFree 3 2
  exact
    markedWedgeThree_surjective_of_torusHomeomorph
      (Homeomorph.refl (PeriodTorusHigherHomology.ProductTorus 3)) (fun _ _ => rfl)
      (PeriodTorusHigherHomology.coordinateH1 3) coordinateH1_three_bijective.surjective

private abbrev Elliptic.HigherHomology.torusExterior (n : ℕ) :=
  ⋀[ℤ]^n FibreLattice

private def Elliptic.HigherHomology.torusLatticeBasis : Module.Basis (Fin 3) ℤ FibreLattice :=
  Pi.basisFun ℤ (Fin 3)

private def Elliptic.HigherHomology.torusExteriorBasis (n : ℕ) :
    Module.Basis (Set.powersetCard (Fin 3) n) ℤ (torusExterior n) :=
  PeriodTorusHigherHomologyExterior.standardExteriorBasis 3 n

private theorem
    Elliptic.HigherHomology.fibrePair_strictMono (i : Fin 3) : StrictMono (fibrePair i) := by
  fin_cases i <;> decide

private theorem
    Elliptic.HigherHomology.fibrePair_injective : Function.Injective fibrePair := by decide

private def Elliptic.HigherHomology.torusPairEmbedding (i : Fin 3) : Fin 2 ↪o Fin 3 :=
  OrderEmbedding.ofStrictMono (fibrePair i) (fibrePair_strictMono i)

private def Elliptic.HigherHomology.torusTripleEmbedding (_i : Fin 1) : Fin 3 ↪o Fin 3 :=
  OrderEmbedding.ofStrictMono id strictMono_id

private def Elliptic.HigherHomology.torusPairSubset (i : Fin 3) : Set.powersetCard (Fin 3) 2 :=
  Set.powersetCard.ofFinEmbEquiv (torusPairEmbedding i)

private def Elliptic.HigherHomology.torusTripleSubset (i : Fin 1) : Set.powersetCard (Fin 3) 3 :=
  Set.powersetCard.ofFinEmbEquiv (torusTripleEmbedding i)

@[simp]
private theorem Elliptic.HigherHomology.torusPairSubset_ordered (i : Fin 3) :
    (Set.powersetCard.ofFinEmbEquiv.symm (torusPairSubset i) : Fin 2 → Fin 3) = fibrePair i := by
  rw [torusPairSubset, Equiv.symm_apply_apply]
  rfl

@[simp]
private theorem Elliptic.HigherHomology.torusTripleSubset_ordered (i : Fin 1) :
    (Set.powersetCard.ofFinEmbEquiv.symm (torusTripleSubset i) : Fin 3 → Fin 3) = id := by
  rw [torusTripleSubset, Equiv.symm_apply_apply]
  rfl

private theorem
    Elliptic.HigherHomology.torusPairSubset_injective : Function.Injective torusPairSubset := by
  intro i j hij
  apply fibrePair_injective
  simpa only [torusPairSubset_ordered] using
    congrArg (fun s => (Set.powersetCard.ofFinEmbEquiv.symm s : Fin 2 → Fin 3)) hij

private theorem Elliptic.HigherHomology.torusTripleSubset_injective :
    Function.Injective torusTripleSubset := by
  intro i j _
  exact Subsingleton.elim i j

private theorem
    Elliptic.HigherHomology.torusPairSubset_bijective : Function.Bijective torusPairSubset := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨torusPairSubset_injective, ?_⟩
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fin, show Nat.choose 3 2 = 3 by decide] using
    (Set.powersetCard.card (Fin 3) 2).symm

private theorem Elliptic.HigherHomology.torusTripleSubset_bijective :
    Function.Bijective torusTripleSubset := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨torusTripleSubset_injective, ?_⟩
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fin, show Nat.choose 3 3 = 1 by decide] using
    (Set.powersetCard.card (Fin 3) 3).symm

private def Elliptic.HigherHomology.torusPairSubsetEquiv : Fin 3 ≃ Set.powersetCard (Fin 3) 2 :=
  Equiv.ofBijective torusPairSubset torusPairSubset_bijective

private def Elliptic.HigherHomology.torusTripleSubsetEquiv : Fin 1 ≃ Set.powersetCard (Fin 3) 3 :=
  Equiv.ofBijective torusTripleSubset torusTripleSubset_bijective

private def Elliptic.HigherHomology.torusSquareBasis : Module.Basis (Fin 3) ℤ (torusExterior 2) :=
  (torusExteriorBasis 2).reindex torusPairSubsetEquiv.symm

private def Elliptic.HigherHomology.torusCubeBasis : Module.Basis (Fin 1) ℤ (torusExterior 3) :=
  (torusExteriorBasis 3).reindex torusTripleSubsetEquiv.symm

private theorem Elliptic.HigherHomology.torusSquareBasis_apply (i : Fin 3) :
    torusSquareBasis i = exteriorPower.ιMulti ℤ 2 (torusLatticeBasis ∘ fibrePair i) := by
  rw [torusSquareBasis, Module.Basis.reindex_apply]
  change (Pi.basisFun ℤ (Fin 3)).exteriorPower 2 (torusPairSubset i) = _
  rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family, torusPairSubset_ordered]
  rfl

private theorem Elliptic.HigherHomology.torusCubeBasis_apply (i : Fin 1) :
    torusCubeBasis i = exteriorPower.ιMulti ℤ 3 torusLatticeBasis := by
  rw [torusCubeBasis, Module.Basis.reindex_apply]
  change (Pi.basisFun ℤ (Fin 3)).exteriorPower 3 (torusTripleSubset i) = _
  rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family, torusTripleSubset_ordered]
  rfl

private def Elliptic.HigherHomology.torusSquareCoordinates : torusExterior 2 ≃ₗ[ℤ] (Fin 3 → ℤ) :=
  torusSquareBasis.equivFun

private def
    Elliptic.HigherHomology.torusCubeVectorCoordinates : torusExterior 3 ≃ₗ[ℤ] (Fin 1 → ℤ) :=
  torusCubeBasis.equivFun

private def Elliptic.HigherHomology.torusCubeCoordinates : torusExterior 3 ≃ₗ[ℤ] ℤ :=
  torusCubeVectorCoordinates.trans (LinearEquiv.piUnique ℤ (fun _ : Fin 1 => ℤ))

@[simp]
private theorem
    Elliptic.HigherHomology.torusSquareCoordinates_apply (x : torusExterior 2) (i : Fin 3) :
    torusSquareCoordinates x i = torusSquareBasis.repr x i :=
  congrFun (torusSquareBasis.equivFun_apply x) i

@[simp]
private theorem Elliptic.HigherHomology.torusCubeCoordinates_apply (x : torusExterior 3) :
    torusCubeCoordinates x = torusCubeBasis.repr x 0 :=
  congrFun (torusCubeBasis.equivFun_apply x) 0

@[simp]
private theorem Elliptic.HigherHomology.torusSquareCoordinates_basis (i : Fin 3) :
    torusSquareCoordinates (torusSquareBasis i) = Pi.single i 1 := by
  ext j
  simp only [torusSquareCoordinates_apply, Module.Basis.repr_self, Finsupp.single_eq_pi_single]

private theorem Elliptic.HigherHomology.torusCubeCoordinates_basis (i : Fin 1) :
    torusCubeCoordinates (torusCubeBasis i) = 1 := by
  have hi : i = 0 := Subsingleton.elim _ _
  rw [hi, torusCubeCoordinates_apply, Module.Basis.repr_self, Finsupp.single_eq_same]

private instance
    Elliptic.HigherHomology.torusExteriorFree (n : ℕ) : Module.Free ℤ (torusExterior n) :=
  inferInstance

private instance Elliptic.HigherHomology.torusExteriorFinite (n : ℕ) :
    Module.Finite ℤ (torusExterior n) :=
  inferInstance

private theorem Elliptic.HigherHomology.torusExterior_finrank (n : ℕ) :
    Module.finrank ℤ (torusExterior n) = Nat.choose 3 n := by
  rw [exteriorPower.finrank_eq, Module.finrank_eq_card_basis torusLatticeBasis, Fintype.card_fin]

private def Elliptic.HigherHomology.torusSquareMatrix (A : FibreMatrix) : FibreMatrix := fun i j =>
  A (fibrePair i 0) (fibrePair j 0) * A (fibrePair i 1) (fibrePair j 1) -
    A (fibrePair i 0) (fibrePair j 1) * A (fibrePair i 1) (fibrePair j 0)

private theorem Elliptic.HigherHomology.torusSquareMatrix_eq_det_submatrix (A : FibreMatrix)
    (i j : Fin 3) : torusSquareMatrix A i j = (A.submatrix (fibrePair i) (fibrePair j)).det := by
  rw [Matrix.det_fin_two]
  rfl

@[simp]
private theorem Elliptic.HigherHomology.torusSquareMatrix_fibreMatrix (j : Elliptic.Kind) :
    torusSquareMatrix (fibreMatrix j) = fibreSquareMatrix j := by
  ext i k
  exact (fibreSquareMatrix_minor j i k).symm

private def Elliptic.HigherHomology.torusExteriorMap (n : ℕ) (A : FibreMatrix) :
    torusExterior n →ₗ[ℤ] torusExterior n :=
  exteriorPower.map n A.mulVecLin

@[simp]
private theorem Elliptic.HigherHomology.torusExteriorMap_one (n : ℕ) :
    torusExteriorMap n 1 = LinearMap.id := by
  simp only [torusExteriorMap, Matrix.mulVecLin_one, exteriorPower.map_id]

private theorem Elliptic.HigherHomology.torusExteriorMap_mul (n : ℕ) (A B : FibreMatrix) :
    torusExteriorMap n (A * B) = (torusExteriorMap n A).comp (torusExteriorMap n B) := by
  simp only [torusExteriorMap, Matrix.mulVecLin_mul, exteriorPower.map_comp]

private theorem Elliptic.HigherHomology.torusSquareMap_coefficient (A : FibreMatrix) (i j : Fin 3) :
    torusSquareBasis.repr (torusExteriorMap 2 A (torusSquareBasis j)) i =
      torusSquareMatrix A i j := by
  rw [torusSquareBasis, Module.Basis.repr_reindex_apply, Module.Basis.reindex_apply]
  change
    (PeriodTorusHigherHomologyExterior.standardExteriorBasis 3 2).repr
        (exteriorPower.map 2 A.mulVecLin
          (PeriodTorusHigherHomologyExterior.standardExteriorBasis 3 2 (torusPairSubset j)))
        (torusPairSubset i) =
      _
  rw [PeriodTorusHigherHomologyExterior.standardExterior_map_coefficient, torusPairSubset_ordered,
    torusPairSubset_ordered]
  exact (torusSquareMatrix_eq_det_submatrix A i j).symm

private theorem Elliptic.HigherHomology.torusCubeMap_coefficient (A : FibreMatrix) (i j : Fin 1) :
    torusCubeBasis.repr (torusExteriorMap 3 A (torusCubeBasis j)) i = A.det := by
  rw [torusCubeBasis, Module.Basis.repr_reindex_apply, Module.Basis.reindex_apply]
  change
    (PeriodTorusHigherHomologyExterior.standardExteriorBasis 3 3).repr
        (exteriorPower.map 3 A.mulVecLin
          (PeriodTorusHigherHomologyExterior.standardExteriorBasis 3 3 (torusTripleSubset j)))
        (torusTripleSubset i) =
      _
  rw [PeriodTorusHigherHomologyExterior.standardExterior_map_coefficient,
    torusTripleSubset_ordered, torusTripleSubset_ordered]
  rfl

private theorem Elliptic.HigherHomology.torusSquareMap_toMatrix (A : FibreMatrix) :
    LinearMap.toMatrix torusSquareBasis torusSquareBasis (torusExteriorMap 2 A) =
      torusSquareMatrix A := by
  ext i j
  rw [LinearMap.toMatrix_apply]
  exact torusSquareMap_coefficient A i j

private theorem Elliptic.HigherHomology.torusCubeMap_toMatrix (A : FibreMatrix) :
    LinearMap.toMatrix torusCubeBasis torusCubeBasis (torusExteriorMap 3 A) =
      (fun _ _ : Fin 1 => A.det) := by
  ext i j
  rw [LinearMap.toMatrix_apply]
  exact torusCubeMap_coefficient A i j

private theorem Elliptic.HigherHomology.torusSquareCoordinates_map (A : FibreMatrix)
    (x : torusExterior 2) :
    torusSquareCoordinates (torusExteriorMap 2 A x) =
      torusSquareMatrix A *ᵥ torusSquareCoordinates x := by
  have h :=
    LinearMap.toMatrix_mulVec_repr torusSquareBasis torusSquareBasis (torusExteriorMap 2 A) x
  rw [torusSquareMap_toMatrix] at h
  simpa only [torusSquareCoordinates, Module.Basis.equivFun_apply] using h.symm

private theorem
    Elliptic.HigherHomology.torusCubeCoordinates_map (A : FibreMatrix) (x : torusExterior 3) :
    torusCubeCoordinates (torusExteriorMap 3 A x) = A.det * torusCubeCoordinates x := by
  rw [torusCubeCoordinates_apply, torusCubeCoordinates_apply]
  have h := LinearMap.toMatrix_mulVec_repr torusCubeBasis torusCubeBasis (torusExteriorMap 3 A) x
  rw [torusCubeMap_toMatrix] at h
  simpa only [Matrix.mulVec, dotProduct, Fin.sum_univ_one] using (congrFun h 0).symm

@[simp]
private theorem Elliptic.HigherHomology.torusSquareMatrix_one : torusSquareMatrix 1 = 1 := by
  rw [← torusSquareMap_toMatrix, torusExteriorMap_one, LinearMap.toMatrix_id]

private theorem Elliptic.HigherHomology.torusSquareMatrix_mul (A B : FibreMatrix) :
    torusSquareMatrix (A * B) = torusSquareMatrix A * torusSquareMatrix B := by
  rw [← torusSquareMap_toMatrix, torusExteriorMap_mul,
    LinearMap.toMatrix_comp torusSquareBasis torusSquareBasis torusSquareBasis,
    torusSquareMap_toMatrix, torusSquareMap_toMatrix]

private theorem
    Elliptic.HigherHomology.torusWedgeTwo_bijective : Function.Bijective torusWedgeTwo := by
  let := PeriodTorusHigherHomology.productTorus_homology_free 3 2
  let := PeriodTorusHigherHomology.productTorus_homology_finite 3 2
  apply
    OrzechProperty.bijective_of_surjective_of_finrank_le torusWedgeTwo torusWedgeTwo_surjective
  rw [torusExterior_finrank, PeriodTorusHigherHomology.productTorus_homology_finrank]

private theorem
    Elliptic.HigherHomology.torusWedgeThree_bijective : Function.Bijective torusWedgeThree := by
  let := PeriodTorusHigherHomology.productTorus_homology_free 3 3
  let := PeriodTorusHigherHomology.productTorus_homology_finite 3 3
  apply
    OrzechProperty.bijective_of_surjective_of_finrank_le torusWedgeThree
      torusWedgeThree_surjective
  rw [torusExterior_finrank, PeriodTorusHigherHomology.productTorus_homology_finrank]

private def Elliptic.HigherHomology.torusWedgeTwoEquiv :
    torusExterior 2 ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 2 :=
  LinearEquiv.ofBijective torusWedgeTwo torusWedgeTwo_bijective

private def Elliptic.HigherHomology.torusWedgeThreeEquiv :
    torusExterior 3 ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 3 :=
  LinearEquiv.ofBijective torusWedgeThree torusWedgeThree_bijective

private def Elliptic.HigherHomology.torusH2ExteriorEquiv :
    SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 2 ≃ₗ[ℤ]
      torusExterior 2 :=
  torusWedgeTwoEquiv.symm

private def Elliptic.HigherHomology.torusH3ExteriorEquiv :
    SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 3 ≃ₗ[ℤ]
      torusExterior 3 :=
  torusWedgeThreeEquiv.symm

@[simp]
private theorem Elliptic.HigherHomology.torusH2ExteriorEquiv_wedge (v : torusExterior 2) :
    torusH2ExteriorEquiv (torusWedgeTwo v) = v :=
  torusWedgeTwoEquiv.symm_apply_apply v

@[simp]
private theorem Elliptic.HigherHomology.torusH3ExteriorEquiv_wedge (v : torusExterior 3) :
    torusH3ExteriorEquiv (torusWedgeThree v) = v :=
  torusWedgeThreeEquiv.symm_apply_apply v

private theorem
    Elliptic.HigherHomology.torusH2ExteriorEquiv_symm_ιMulti (v : Fin 2 → FibreLattice) :
    torusH2ExteriorEquiv.symm (exteriorPower.ιMulti ℤ 2 v) =
      PeriodTorusHigherHomologyPontryagin.product11 (PeriodTorusHigherHomology.ProductTorus 3)
        (FirstHurewicz.loopHomologyClass (PeriodTorusHigherHomology.coordinatePeriodLoop 3 (v 0)))
        (FirstHurewicz.loopHomologyClass
          (PeriodTorusHigherHomology.coordinatePeriodLoop 3 (v 1))) :=
  torusWedgeTwo_ιMulti_loops v

private theorem
    Elliptic.HigherHomology.torusH3ExteriorEquiv_symm_ιMulti (v : Fin 3 → FibreLattice) :
    torusH3ExteriorEquiv.symm (exteriorPower.ιMulti ℤ 3 v) =
      PeriodTorusHigherHomologyPontryagin.tripleProduct (PeriodTorusHigherHomology.ProductTorus 3)
        (FirstHurewicz.loopHomologyClass (PeriodTorusHigherHomology.coordinatePeriodLoop 3 (v 0)))
        (FirstHurewicz.loopHomologyClass (PeriodTorusHigherHomology.coordinatePeriodLoop 3 (v 1)))
        (FirstHurewicz.loopHomologyClass
          (PeriodTorusHigherHomology.coordinatePeriodLoop 3 (v 2))) :=
  torusWedgeThree_ιMulti_loops v

private theorem Elliptic.HigherHomology.torusH2ExteriorEquiv_natural
    (f : C(PeriodTorusHigherHomology.ProductTorus 3, PeriodTorusHigherHomology.ProductTorus 3))
    (hf : ∀ x y, f (x + y) = f x + f y) (A : FibreLattice →ₗ[ℤ] FibreLattice)
    (hmark :
      ∀ v,
        SingularMayerVietoris.singularHomologyMap f 1
            (PeriodTorusHigherHomology.coordinateH1 3 v) =
          PeriodTorusHigherHomology.coordinateH1 3 (A v))
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 2) :
    torusH2ExteriorEquiv (SingularMayerVietoris.singularHomologyMap f 2 a) =
      exteriorPower.map 2 A (torusH2ExteriorEquiv a) := by
  obtain ⟨v, rfl⟩ := torusWedgeTwo_surjective a
  have h := LinearMap.congr_fun (torusWedgeTwo_natural f hf A hmark) v
  change
    SingularMayerVietoris.singularHomologyMap f 2 (torusWedgeTwo v) =
      torusWedgeTwo (exteriorPower.map 2 A v) at h
  rw [h, torusH2ExteriorEquiv_wedge, torusH2ExteriorEquiv_wedge]

private theorem Elliptic.HigherHomology.torusH3ExteriorEquiv_natural
    (f : C(PeriodTorusHigherHomology.ProductTorus 3, PeriodTorusHigherHomology.ProductTorus 3))
    (hf : ∀ x y, f (x + y) = f x + f y) (A : FibreLattice →ₗ[ℤ] FibreLattice)
    (hmark :
      ∀ v,
        SingularMayerVietoris.singularHomologyMap f 1
            (PeriodTorusHigherHomology.coordinateH1 3 v) =
          PeriodTorusHigherHomology.coordinateH1 3 (A v))
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 3) :
    torusH3ExteriorEquiv (SingularMayerVietoris.singularHomologyMap f 3 a) =
      exteriorPower.map 3 A (torusH3ExteriorEquiv a) := by
  obtain ⟨v, rfl⟩ := torusWedgeThree_surjective a
  have h := LinearMap.congr_fun (torusWedgeThree_natural f hf A hmark) v
  change
    SingularMayerVietoris.singularHomologyMap f 3 (torusWedgeThree v) =
      torusWedgeThree (exteriorPower.map 3 A v) at h
  rw [h, torusH3ExteriorEquiv_wedge, torusH3ExteriorEquiv_wedge]

private theorem Elliptic.HigherHomology.torusH2ExteriorEquiv_matrix_natural (A : FibreMatrix)
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 2) :
    torusH2ExteriorEquiv
        (SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusMatrixMap A) 2
          a) =
      exteriorPower.map 2 A.mulVecLin (torusH2ExteriorEquiv a) :=
  torusH2ExteriorEquiv_natural (PeriodTorusHigherHomology.torusMatrixMap A)
    (PeriodTorusHigherHomology.torusMatrixMap_add A) A.mulVecLin
    (coordinateH1_three_matrix_natural A) a

private theorem Elliptic.HigherHomology.torusH3ExteriorEquiv_matrix_natural (A : FibreMatrix)
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 3) :
    torusH3ExteriorEquiv
        (SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusMatrixMap A) 3
          a) =
      exteriorPower.map 3 A.mulVecLin (torusH3ExteriorEquiv a) :=
  torusH3ExteriorEquiv_natural (PeriodTorusHigherHomology.torusMatrixMap A)
    (PeriodTorusHigherHomology.torusMatrixMap_add A) A.mulVecLin
    (coordinateH1_three_matrix_natural A) a

private def Elliptic.HigherHomology.torusH2Coordinates :
    SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 2 ≃ₗ[ℤ]
      (Fin 3 → ℤ) :=
  torusH2ExteriorEquiv.trans torusSquareCoordinates

private def Elliptic.HigherHomology.torusH3Coordinates :
    SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 3 ≃ₗ[ℤ] ℤ :=
  torusH3ExteriorEquiv.trans torusCubeCoordinates

private theorem Elliptic.HigherHomology.torusH2Coordinates_matrix_natural (A : FibreMatrix)
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 2) :
    torusH2Coordinates
        (SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusMatrixMap A) 2
          a) =
      torusSquareMatrix A *ᵥ torusH2Coordinates a := by
  change
    torusSquareCoordinates
        (torusH2ExteriorEquiv
          (SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusMatrixMap A)
            2 a)) =
      _
  rw [torusH2ExteriorEquiv_matrix_natural]
  exact torusSquareCoordinates_map A (torusH2ExteriorEquiv a)

private theorem Elliptic.HigherHomology.torusH3Coordinates_matrix_natural (A : FibreMatrix)
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 3) :
    torusH3Coordinates
        (SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusMatrixMap A) 3
          a) =
      A.det * torusH3Coordinates a := by
  change
    torusCubeCoordinates
        (torusH3ExteriorEquiv
          (SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusMatrixMap A)
            3 a)) =
      _
  rw [torusH3ExteriorEquiv_matrix_natural]
  exact torusCubeCoordinates_map A (torusH3ExteriorEquiv a)

private theorem Elliptic.HigherHomology.torusH2Coordinates_symm_basis (i : Fin 3) :
    torusH2Coordinates.symm (Pi.single i 1) =
      PeriodTorusHigherHomologyPontryagin.product11 (PeriodTorusHigherHomology.ProductTorus 3)
        (FirstHurewicz.loopHomologyClass
          (PeriodTorusHigherHomology.coordinatePeriodLoop 3 (Pi.single (fibrePair i 0) 1)))
        (FirstHurewicz.loopHomologyClass
          (PeriodTorusHigherHomology.coordinatePeriodLoop 3 (Pi.single (fibrePair i 1) 1))) := by
  change torusH2ExteriorEquiv.symm (torusSquareCoordinates.symm (Pi.single i 1)) = _
  rw [← torusSquareCoordinates_basis i, LinearEquiv.symm_apply_apply, torusSquareBasis_apply,
    torusH2ExteriorEquiv_symm_ιMulti]
  simp only [Function.comp_apply, torusLatticeBasis, Pi.basisFun_apply]

private theorem Elliptic.HigherHomology.torusH3Coordinates_symm_one :
    torusH3Coordinates.symm 1 =
      PeriodTorusHigherHomologyPontryagin.tripleProduct (PeriodTorusHigherHomology.ProductTorus 3)
        (FirstHurewicz.loopHomologyClass
          (PeriodTorusHigherHomology.coordinatePeriodLoop 3 (Pi.single 0 1)))
        (FirstHurewicz.loopHomologyClass
          (PeriodTorusHigherHomology.coordinatePeriodLoop 3 (Pi.single 1 1)))
        (FirstHurewicz.loopHomologyClass
          (PeriodTorusHigherHomology.coordinatePeriodLoop 3 (Pi.single 2 1))) := by
  change torusH3ExteriorEquiv.symm (torusCubeCoordinates.symm 1) = _
  have h : torusCubeCoordinates.symm 1 = torusCubeBasis (0 : Fin 1) := by
    rw [← torusCubeCoordinates_basis (0 : Fin 1), LinearEquiv.symm_apply_apply]
  rw [h, torusCubeBasis_apply, torusH3ExteriorEquiv_symm_ιMulti]
  simp only [torusLatticeBasis, Pi.basisFun_apply]

private theorem Elliptic.HigherHomology.torusH2Coordinates_fibreMatrix (j : Elliptic.Kind)
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 2) :
    torusH2Coordinates
        (SingularMayerVietoris.singularHomologyMap
          (PeriodTorusHigherHomology.torusMatrixMap (fibreMatrix j)) 2 a) =
      fibreSquareMatrix j *ᵥ torusH2Coordinates a := by
  rw [torusH2Coordinates_matrix_natural, torusSquareMatrix_fibreMatrix]

private theorem Elliptic.HigherHomology.torusH3Coordinates_fibreMatrix (j : Elliptic.Kind)
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 3) :
    torusH3Coordinates
        (SingularMayerVietoris.singularHomologyMap
          (PeriodTorusHigherHomology.torusMatrixMap (fibreMatrix j)) 3 a) =
      torusH3Coordinates a := by rw [torusH3Coordinates_matrix_natural, fibreMatrix_det, one_mul]

private theorem Elliptic.HigherHomology.fibreTorusHomeomorph_pow_apply (j : Elliptic.Kind) (n : ℕ)
    (x : PeriodTorusHigherHomology.ProductTorus 3) :
    (fibreTorusHomeomorph j ^ n) x =
      PeriodTorusHigherHomology.torusMatrixMap (fibreMatrix j ^ n) x := by
  induction n generalizing x with
  | zero =>
    simp only [pow_zero, Homeomorph.one_apply, PeriodTorusHigherHomology.torusMatrixMap_one]; rfl
  | succ n
    ih =>
    rw [pow_succ, Homeomorph.mul_apply, ih, fibreTorusHomeomorph_apply, pow_succ,
      PeriodTorusHigherHomology.torusMatrixMap_mul]
    rfl

private theorem Elliptic.HigherHomology.fibreTorusHomeomorph_pow_order (j : Elliptic.Kind) :
    fibreTorusHomeomorph j ^ j.order = 1 := by
  ext x
  rw [fibreTorusHomeomorph_pow_apply, fibreMatrix_pow_order,
    PeriodTorusHigherHomology.torusMatrixMap_one]
  rfl

private theorem Elliptic.HigherHomology.fibreSL_inv_val (j : Elliptic.Kind) :
    (((fibreSL j)⁻¹ : SL(3, ℤ)) : FibreMatrix) = (fibreMatrix j)⁻¹ := by
  have hleft : (((fibreSL j)⁻¹ : SL(3, ℤ)) : FibreMatrix) * fibreMatrix j = 1 :=
    congrArg (fun C : SL(3, ℤ) => C.val) (inv_mul_cancel (fibreSL j))
  calc
    (((fibreSL j)⁻¹ : SL(3, ℤ)) : FibreMatrix) = (((fibreSL j)⁻¹ : SL(3, ℤ)) : FibreMatrix) * 1 :=
      (mul_one _).symm
    _ = (((fibreSL j)⁻¹ : SL(3, ℤ)) : FibreMatrix) * (fibreMatrix j * (fibreMatrix j)⁻¹) := by
      rw [Matrix.mul_nonsing_inv _ (by simp [fibreMatrix_det])]
    _ = (fibreMatrix j)⁻¹ := by rw [← mul_assoc, hleft, one_mul]

private theorem Elliptic.HigherHomology.torusSquareMatrix_fibreMatrix_inv (j : Elliptic.Kind) :
    torusSquareMatrix ((fibreMatrix j)⁻¹) = (fibreSquareMatrix j)⁻¹ := by
  have hleft : torusSquareMatrix ((fibreMatrix j)⁻¹) * fibreSquareMatrix j = 1 := by
    rw [← torusSquareMatrix_fibreMatrix, ← torusSquareMatrix_mul,
      Matrix.nonsing_inv_mul _ (by simp [fibreMatrix_det]), torusSquareMatrix_one]
  calc
    torusSquareMatrix ((fibreMatrix j)⁻¹) = torusSquareMatrix ((fibreMatrix j)⁻¹) * 1 :=
      (mul_one _).symm
    _ = torusSquareMatrix ((fibreMatrix j)⁻¹) * (fibreSquareMatrix j * (fibreSquareMatrix j)⁻¹) :=
      by rw [Matrix.mul_nonsing_inv _ (by simp [fibreSquareMatrix_det])]
    _ = (fibreSquareMatrix j)⁻¹ := by rw [← mul_assoc, hleft, one_mul]

private theorem Elliptic.HigherHomology.fibreMatrix_inv_det (j : Elliptic.Kind) :
    (fibreMatrix j)⁻¹.det = 1 := by
  have h := Matrix.det_nonsing_inv_mul_det (fibreMatrix j) (by simp [fibreMatrix_det])
  simpa only [fibreMatrix_det, mul_one] using h

private abbrev Elliptic.HigherHomology.mappingTorusModel (j : Elliptic.Kind) :=
  MappingTorus.Torus (fibreTorusHomeomorph j).symm

private theorem Elliptic.HigherHomology.mappingTorusMonodromy_one (j : Elliptic.Kind)
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 1) :
    torusH1Equiv (MappingTorusHomology.monodromyHomologyMap (fibreTorusHomeomorph j).symm 1 a) =
      (fibreMatrix j)⁻¹ *ᵥ torusH1Equiv a := by
  change
    torusH1Equiv
        (SingularMayerVietoris.singularHomologyMap
          (PeriodTorusHigherHomology.torusMatrixMap (((fibreSL j)⁻¹ : SL(3, ℤ)) : FibreMatrix)) 1
          a) =
      _
  rw [fibreSL_inv_val, torusH1Equiv_matrix_natural]

private theorem Elliptic.HigherHomology.mappingTorusMonodromy_two (j : Elliptic.Kind)
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 2) :
    torusH2Coordinates
        (MappingTorusHomology.monodromyHomologyMap (fibreTorusHomeomorph j).symm 2 a) =
      (fibreSquareMatrix j)⁻¹ *ᵥ torusH2Coordinates a := by
  change
    torusH2Coordinates
        (SingularMayerVietoris.singularHomologyMap
          (PeriodTorusHigherHomology.torusMatrixMap (((fibreSL j)⁻¹ : SL(3, ℤ)) : FibreMatrix)) 2
          a) =
      _
  rw [fibreSL_inv_val, torusH2Coordinates_matrix_natural, torusSquareMatrix_fibreMatrix_inv]

private theorem Elliptic.HigherHomology.mappingTorusMonodromy_three (j : Elliptic.Kind)
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 3) :
    torusH3Coordinates
        (MappingTorusHomology.monodromyHomologyMap (fibreTorusHomeomorph j).symm 3 a) =
      torusH3Coordinates a := by
  change
    torusH3Coordinates
        (SingularMayerVietoris.singularHomologyMap
          (PeriodTorusHigherHomology.torusMatrixMap (((fibreSL j)⁻¹ : SL(3, ℤ)) : FibreMatrix)) 3
          a) =
      _
  rw [fibreSL_inv_val, torusH3Coordinates_matrix_natural, fibreMatrix_inv_det, one_mul]

private theorem Elliptic.HigherHomology.mappingTorusDifference_one (j : Elliptic.Kind)
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 1) :
    torusH1Equiv (MappingTorusHomology.wangDifference (fibreTorusHomeomorph j).symm 1 a) =
      fibreInverseDifference j (torusH1Equiv a) := by
  change
    torusH1Equiv
        (a - MappingTorusHomology.monodromyHomologyMap (fibreTorusHomeomorph j).symm 1 a) =
      _
  rw [map_sub, mappingTorusMonodromy_one]
  simp only [fibreInverseDifference, Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.one_mulVec]

private theorem Elliptic.HigherHomology.mappingTorusDifference_two (j : Elliptic.Kind)
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 2) :
    torusH2Coordinates (MappingTorusHomology.wangDifference (fibreTorusHomeomorph j).symm 2 a) =
      fibreSquareInverseDifference j (torusH2Coordinates a) := by
  change
    torusH2Coordinates
        (a - MappingTorusHomology.monodromyHomologyMap (fibreTorusHomeomorph j).symm 2 a) =
      _
  rw [map_sub, mappingTorusMonodromy_two]
  simp only [fibreSquareInverseDifference, Matrix.mulVecLin_apply, Matrix.sub_mulVec,
    Matrix.one_mulVec]

private theorem Elliptic.HigherHomology.mappingTorusDifference_three (j : Elliptic.Kind) :
    MappingTorusHomology.wangDifference (fibreTorusHomeomorph j).symm 3 = 0 := by
  ext a
  apply torusH3Coordinates.injective
  change
    torusH3Coordinates
        (a - MappingTorusHomology.monodromyHomologyMap (fibreTorusHomeomorph j).symm 3 a) =
      torusH3Coordinates 0
  rw [map_sub, mappingTorusMonodromy_three, sub_self, map_zero]

private abbrev Elliptic.HigherHomology.surfaceProductQuotient (j : Elliptic.Kind) :=
  MappingTorusQuotient.ProductQuotient j.order (fibreTorusHomeomorph j)
    (fibreTorusHomeomorph_pow_order j)

private def Elliptic.HigherHomology.surfaceSplitQuotientHomeomorph (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) :
    Elliptic.Surface j p j.twist (Elliptic.mainTwist_admissible j) ≃ₜ surfaceProductQuotient j :=
  MappingTorusQuotient.cyclicQuotientCongr (Elliptic.affinePermutation j p j.twist)
    (Elliptic.affinePermutation_pow_order j p j.twist j.matrix_fixes_twist)
    (MappingTorusQuotient.twist j.order (fibreTorusHomeomorph j)).toEquiv
    (MappingTorusQuotient.twistPerm_pow_order j.order (fibreTorusHomeomorph j)
      (fibreTorusHomeomorph_pow_order j))
    (splitPeriodTorusHomeomorph j p.val)
    (fun x => splitPeriodTorusHomeomorph_affineBiholomorph j p x)

@[simp]
private theorem
    Elliptic.HigherHomology.surfaceSplitQuotientHomeomorph_projection (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) (x : p.val.Torus) :
    surfaceSplitQuotientHomeomorph j p
        (Elliptic.surfaceProjection j p j.twist (Elliptic.mainTwist_admissible j) x) =
      MappingTorusQuotient.project j.order (fibreTorusHomeomorph j)
        (fibreTorusHomeomorph_pow_order j) (splitPeriodTorusHomeomorph j p.val x) :=
  rfl

@[simp]
private theorem
    Elliptic.HigherHomology.surfaceSplitQuotientHomeomorph_symm_project (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j)
    (x : MappingTorus.Circle × PeriodTorusHigherHomology.ProductTorus 3) :
    (surfaceSplitQuotientHomeomorph j p).symm
        (MappingTorusQuotient.project j.order (fibreTorusHomeomorph j)
          (fibreTorusHomeomorph_pow_order j) x) =
      Elliptic.surfaceProjection j p j.twist (Elliptic.mainTwist_admissible j)
        ((splitPeriodTorusHomeomorph j p.val).symm x) :=
  rfl

private def Elliptic.HigherHomology.surfaceMappingTorusHomeomorph (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) :
    Elliptic.Surface j p j.twist (Elliptic.mainTwist_admissible j) ≃ₜ mappingTorusModel j :=
  (surfaceSplitQuotientHomeomorph j p).trans
    (MappingTorusQuotient.mappingTorusHomeomorph j.order (fibreTorusHomeomorph j)
      (fibreTorusHomeomorph_pow_order j))

private theorem
    Elliptic.HigherHomology.surfaceMappingTorusHomeomorph_splitPeriodTorus (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) (t : ℝ) (x : PeriodTorusHigherHomology.ProductTorus 3) :
    surfaceMappingTorusHomeomorph j p
        (Elliptic.surfaceProjection j p j.twist (Elliptic.mainTwist_admissible j)
          ((splitPeriodTorusHomeomorph j p.val).symm ((t : MappingTorus.Circle), x))) =
      MappingTorus.mk (fibreTorusHomeomorph j).symm (t * j.order, x) := by
  rw [surfaceMappingTorusHomeomorph, Homeomorph.trans_apply,
    surfaceSplitQuotientHomeomorph_projection, Homeomorph.apply_symm_apply,
    MappingTorusQuotient.mappingTorusHomeomorph_project]

private theorem Elliptic.HigherHomology.surfaceMappingTorusHomeomorph_symm_mk (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) (t : ℝ) (x : PeriodTorusHigherHomology.ProductTorus 3) :
    (surfaceMappingTorusHomeomorph j p).symm
        (MappingTorus.mk (fibreTorusHomeomorph j).symm (t, x)) =
      Elliptic.surfaceProjection j p j.twist (Elliptic.mainTwist_admissible j)
        ((splitPeriodTorusHomeomorph j p.val).symm
          (((t / j.order : ℝ) : MappingTorus.Circle), x)) := by
  change
    (surfaceSplitQuotientHomeomorph j p).symm
        ((MappingTorusQuotient.mappingTorusHomeomorph j.order (fibreTorusHomeomorph j)
              (fibreTorusHomeomorph_pow_order j)).symm
          (MappingTorus.mk (fibreTorusHomeomorph j).symm (t, x))) =
      _
  rw [MappingTorusQuotient.mappingTorusHomeomorph_symm_mk,
    surfaceSplitQuotientHomeomorph_symm_project]

private def Elliptic.Equivariant.Data.centralInclusion {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) : D.centralPeriod.val.Torus → D.TotalSpace :=
  D.periods.fibreInclusion SpecialPeriods.discZero

private theorem Elliptic.Equivariant.Data.centralInclusion_injective {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) : Function.Injective D.centralInclusion :=
  D.periods.fibreInclusion_injective SpecialPeriods.discZero

private theorem Elliptic.Equivariant.Data.centralInclusion_continuous {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) : Continuous D.centralInclusion :=
  continuous_const.prodMk (D.periods.torusHomeomorph SpecialPeriods.discZero).symm.continuous

private theorem Elliptic.Equivariant.Data.centralInclusion_mkQ {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (z : ComplexPlane₂) :
    D.centralInclusion (D.centralPeriod.val.lattice.mkQ z) =
      D.periods.quotientMap (SpecialPeriods.discZero, z) :=
  D.periods.fibreInclusion_mkQ SpecialPeriods.discZero z

private theorem Elliptic.Equivariant.Data.range_centralInclusion {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) :
    Set.range D.centralInclusion = D.periods.projection ⁻¹' { SpecialPeriods.discZero } :=
  D.periods.range_fibreInclusion SpecialPeriods.discZero

private theorem Elliptic.Equivariant.Data.mem_range_centralInclusion_iff {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (x : D.TotalSpace) :
    x ∈ Set.range D.centralInclusion ↔ x.1 = SpecialPeriods.discZero := by
  rw [D.range_centralInclusion]
  rfl

private theorem Elliptic.Equivariant.Data.centralInclusion_flatProjection {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (x : Elliptic.RealCoordinates) :
    D.centralInclusion (Elliptic.flatProjection D.centralPeriod.val x) =
      (SpecialPeriods.discZero, standardLattice.mkQ x) := by
  rw [Elliptic.flatProjection, D.centralInclusion_mkQ]
  change
    (SpecialPeriods.discZero,
        standardLattice.mkQ
          ((D.periods.periodEquiv SpecialPeriods.discZero).symm
            (Elliptic.periodEquiv (D.periods.point SpecialPeriods.discZero) x))) =
      _
  rw [← D.periodEquiv_eq_periodEquiv, LinearEquiv.symm_apply_apply]

private theorem Elliptic.Equivariant.Data.permutation_centralInclusion {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (x : D.centralPeriod.val.Torus) :
    D.permutation v (D.centralInclusion x) =
      D.centralInclusion (Elliptic.affineBiholomorph j D.centralPeriod v x) := by
  obtain ⟨y, rfl⟩ := Elliptic.flatProjection_surjective D.centralPeriod.val x
  rw [D.centralInclusion_flatProjection, D.permutation_apply,
    Elliptic.affineBiholomorph_flatProjection, D.centralInclusion_flatProjection]
  exact Prod.ext (Elliptic.familyRotation_zero j) (Elliptic.flatTorusAffine_mkQ j v y)

private theorem Elliptic.Equivariant.Data.permutation_iterate_centralInclusion {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (n : ℕ) (x : D.centralPeriod.val.Torus) :
    (D.permutation v)^[n] (D.centralInclusion x) =
      D.centralInclusion ((Elliptic.affineBiholomorph j D.centralPeriod v)^[n] x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      D.permutation_centralInclusion]

private theorem Elliptic.Equivariant.Data.permutation_pow_centralInclusion {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (n : ℕ) (x : D.centralPeriod.val.Torus) :
    (D.permutation v ^ n) (D.centralInclusion x) =
      D.centralInclusion ((Elliptic.affinePermutation j D.centralPeriod v ^ n) x) := by
  rw [Equiv.Perm.coe_pow, Equiv.Perm.coe_pow]
  exact D.permutation_iterate_centralInclusion v n x

private theorem Elliptic.Equivariant.Data.centralInclusion_smul {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : j.matrix *ᵥ v = v)
    (g : Elliptic.CyclicGroup j) (x : D.centralPeriod.val.Torus) :
    letI := Elliptic.affineAction j D.centralPeriod v hv
    letI := D.action v hv
    D.centralInclusion (g • x) = g • D.centralInclusion x := by
  let := Elliptic.affineAction j D.centralPeriod v hv
  let := D.action v hv
  change
    D.centralInclusion ((Elliptic.affinePermutation j D.centralPeriod v ^ g.toAdd.val) x) =
      (D.permutation v ^ g.toAdd.val) (D.centralInclusion x)
  exact (D.permutation_pow_centralInclusion v g.toAdd.val x).symm

private theorem Elliptic.Equivariant.Data.centralInclusion_quotient_invariant {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v)
    (g : Elliptic.CyclicGroup j) (x : D.centralPeriod.val.Torus) :
    letI := Elliptic.affineAction j D.centralPeriod v hv.1
    D.quotient v hv (D.centralInclusion (g • x)) = D.quotient v hv (D.centralInclusion x) := by
  let := Elliptic.affineAction j D.centralPeriod v hv.1
  let := D.action v hv.1
  rw [D.centralInclusion_smul]
  exact D.quotient_smul v hv g (D.centralInclusion x)

private def Elliptic.Equivariant.Data.centralFibreInclusion {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) :
    Elliptic.Surface j D.centralPeriod v hv → D.Space v hv := by
  let := Elliptic.affineAction j D.centralPeriod v hv.1
  exact
    Elliptic.FiniteQuotient.descend (D.quotient v hv ∘ D.centralInclusion)
      (D.centralInclusion_quotient_invariant v hv)

@[simp]
private theorem
    Elliptic.Equivariant.Data.centralFibreInclusion_surfaceProjection {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v)
    (x : D.centralPeriod.val.Torus) :
    D.centralFibreInclusion v hv (Elliptic.surfaceProjection j D.centralPeriod v hv x) =
      D.quotient v hv (D.centralInclusion x) :=
  rfl

private theorem Elliptic.Equivariant.Data.centralFibreInclusion_continuous {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) :
    Continuous (D.centralFibreInclusion v hv) := by
  let := Elliptic.affineAction j D.centralPeriod v hv.1
  exact
    Elliptic.FiniteQuotient.descend_continuous (D.quotient v hv ∘ D.centralInclusion)
      (D.centralInclusion_quotient_invariant v hv)
      ((D.quotient_continuous v hv).comp D.centralInclusion_continuous)

private theorem Elliptic.Equivariant.Data.centralFibreInclusion_injective {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) :
    Function.Injective (D.centralFibreInclusion v hv) := by
  intro a b hab
  obtain ⟨x, rfl⟩ := Elliptic.surfaceProjection_surjective j D.centralPeriod v hv a
  obtain ⟨y, rfl⟩ := Elliptic.surfaceProjection_surjective j D.centralPeriod v hv b
  rw [D.centralFibreInclusion_surfaceProjection, D.centralFibreInclusion_surfaceProjection] at hab
  let := Elliptic.affineAction j D.centralPeriod v hv.1
  let := D.action v hv.1
  obtain ⟨g, hg⟩ := (D.quotient_eq_iff_mem_orbit v hv _ _).mp hab
  apply
    (Elliptic.FiniteQuotient.project_eq_iff_mem_orbit (Elliptic.CyclicGroup j)
        D.centralPeriod.val.Torus x y).mpr
  refine ⟨g, D.centralInclusion_injective ?_⟩
  rw [D.centralInclusion_smul]
  exact hg

private theorem
    Elliptic.Equivariant.Data.centralFibreInclusion_isClosedEmbedding {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) :
    Topology.IsClosedEmbedding (D.centralFibreInclusion v hv) :=
  (D.centralFibreInclusion_continuous v hv).isClosedEmbedding
    (D.centralFibreInclusion_injective v hv)

private theorem Elliptic.Equivariant.Data.range_centralFibreInclusion {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) :
    Set.range (D.centralFibreInclusion v hv) = D.projection v hv ⁻¹' { Elliptic.discZero } := by
  rw [D.projection_central_fibre]
  ext q
  constructor
  · rintro ⟨s, rfl⟩
    obtain ⟨x, rfl⟩ := Elliptic.surfaceProjection_surjective j D.centralPeriod v hv s
    exact ⟨D.centralInclusion x, rfl, (D.centralFibreInclusion_surfaceProjection v hv x).symm⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨y, hy⟩ := (D.mem_range_centralInclusion_iff x).mpr hx
    refine ⟨Elliptic.surfaceProjection j D.centralPeriod v hv y, ?_⟩
    rw [D.centralFibreInclusion_surfaceProjection, hy]

@[simp]
private theorem Elliptic.Equivariant.Data.projection_centralFibreInclusion {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v)
    (x : Elliptic.Surface j D.centralPeriod v hv) :
    D.projection v hv (D.centralFibreInclusion v hv x) = Elliptic.discZero := by
  have hx := Set.mem_range_self (f := D.centralFibreInclusion v hv) x
  rw [D.range_centralFibreInclusion] at hx
  exact hx

private def Elliptic.Equivariant.Data.centralFibreHomeomorph {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) :
    Elliptic.Surface j D.centralPeriod v hv ≃ₜ D.projection v hv ⁻¹' { Elliptic.discZero } :=
  (D.centralFibreInclusion_isClosedEmbedding v hv).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (D.range_centralFibreInclusion v hv))

private def Elliptic.Equivariant.Data.surfaceIntoFilling {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) :
    ContinuousMap (Elliptic.Surface j D.centralPeriod v hv) (D.Space v hv) :=
  ⟨D.centralFibreInclusion v hv, D.centralFibreInclusion_continuous v hv⟩

private def Elliptic.Equivariant.Data.fillingSurfaceRetraction {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) :
    ContinuousMap (D.Space v hv) (Elliptic.Surface j D.centralPeriod v hv) :=
  ContinuousMap.comp
    ⟨(D.centralFibreHomeomorph v hv).symm, (D.centralFibreHomeomorph v hv).symm.continuous⟩
    (D.fillingCentralRetraction v hv)

@[simp]
private theorem
    Elliptic.Equivariant.Data.fillingSurfaceRetraction_comp_inclusion {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) :
    (D.fillingSurfaceRetraction v hv).comp (D.surfaceIntoFilling v hv) = ContinuousMap.id _ := by
  ext x
  have he :
    D.fillingCentralRetraction v hv (D.centralFibreInclusion v hv x) =
      D.centralFibreHomeomorph v hv x := by
    apply Subtype.ext
    exact D.fillingRadial_fixed v hv 1 _ (D.projection_centralFibreInclusion v hv x)
  change
    (D.centralFibreHomeomorph v hv).symm
        (D.fillingCentralRetraction v hv (D.centralFibreInclusion v hv x)) =
      x
  rw [he, Homeomorph.symm_apply_apply]

private theorem Elliptic.Equivariant.Data.surfaceIntoFilling_comp_retraction {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) :
    (D.surfaceIntoFilling v hv).comp (D.fillingSurfaceRetraction v hv) =
      (D.fillingCentralSubtypeInclusion v hv).comp (D.fillingCentralRetraction v hv) := by
  ext x
  exact
    congrArg Subtype.val
      ((D.centralFibreHomeomorph v hv).apply_symm_apply (D.fillingCentralRetraction v hv x))

private def Elliptic.Equivariant.Data.fillingSurfaceStrongDeformationRetraction {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) :
    (ContinuousMap.id (D.Space v hv)).HomotopyRel
      ((D.surfaceIntoFilling v hv).comp (D.fillingSurfaceRetraction v hv))
      (Set.range (D.surfaceIntoFilling v hv))
    where
  toFun p := D.fillingRadial v hv p.1 p.2
  continuous_toFun := D.fillingRadial_continuous v hv
  map_zero_left := D.fillingRadial_zero v hv
  map_one_left
    x :=
    congrArg (fun f : ContinuousMap (D.Space v hv) (D.Space v hv) => f x)
      (D.surfaceIntoFilling_comp_retraction v hv).symm
  prop' t x
    hx := by
    obtain ⟨y, rfl⟩ := hx
    exact D.fillingRadial_fixed v hv t _ (D.projection_centralFibreInclusion v hv y)

private theorem Elliptic.HigherHomology.threeTorusMappingTorus_homology_subsingleton
    (f : PeriodTorusHigherHomology.ProductTorus 3 ≃ₜ PeriodTorusHigherHomology.ProductTorus 3)
    {n : ℕ} (hn : 4 < n) :
    Subsingleton (SingularMayerVietoris.SingularHomology (MappingTorus.Torus f) n) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
  have :=
    PeriodTorusHigherHomology.productTorus_homology_subsingleton_of_lt (show 3 < k + 1 by omega)
  have := PeriodTorusHigherHomology.productTorus_homology_subsingleton_of_lt (show 3 < k by omega)
  have hzero :
    ∀ a : SingularMayerVietoris.SingularHomology (MappingTorus.Torus f) (k + 1), a = 0 := by
    intro a
    have ha : a ∈ LinearMap.ker (MappingTorusHomology.wangBoundary f k) := by
      change MappingTorusHomology.wangBoundary f k a = 0
      exact Subsingleton.elim _ _
    rw [← MappingTorusHomology.wang_exact_at_mappingTorus f k] at ha
    obtain ⟨x, hx⟩ := ha
    have hx0 : x = 0 := Subsingleton.elim _ _
    rw [hx0, map_zero] at hx
    exact hx.symm
  exact ⟨fun a b => (hzero a).trans (hzero b).symm⟩

private theorem
    Elliptic.HigherHomology.conjugacy_ker_mem_iff {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] (e : M ≃ₗ[ℤ] N) (L : M →ₗ[ℤ] M) (A : N →ₗ[ℤ] N)
    (h : ∀ x, e (L x) = A (e x)) (x : M) : x ∈ LinearMap.ker L ↔ e x ∈ LinearMap.ker A := by
  change L x = 0 ↔ A (e x) = 0
  rw [← h x, e.map_eq_zero_iff]

private theorem Elliptic.HigherHomology.conjugacy_range_mem_iff {M N : Type*} [AddCommGroup M]
    [Module ℤ M] [AddCommGroup N] [Module ℤ N] (e : M ≃ₗ[ℤ] N) (L : M →ₗ[ℤ] M) (A : N →ₗ[ℤ] N)
    (h : ∀ x, e (L x) = A (e x)) (x : M) : x ∈ LinearMap.range L ↔ e x ∈ LinearMap.range A := by
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨e y, (h y).symm⟩
  · rintro ⟨y, hy⟩
    refine ⟨e.symm y, ?_⟩
    apply e.injective
    rw [h, e.apply_symm_apply]
    exact hy

private theorem
    Elliptic.HigherHomology.conjugacy_map_ker {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] (e : M ≃ₗ[ℤ] N) (L : M →ₗ[ℤ] M) (A : N →ₗ[ℤ] N)
    (h : ∀ x, e (L x) = A (e x)) : (LinearMap.ker L).map e.toLinearMap = LinearMap.ker A := by
  ext y
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (conjugacy_ker_mem_iff e L A h x).mp hx
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    apply (conjugacy_ker_mem_iff e L A h (e.symm y)).mpr
    simpa only [e.apply_symm_apply] using hy

private theorem
    Elliptic.HigherHomology.conjugacy_map_range {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] (e : M ≃ₗ[ℤ] N) (L : M →ₗ[ℤ] M) (A : N →ₗ[ℤ] N)
    (h : ∀ x, e (L x) = A (e x)) : (LinearMap.range L).map e.toLinearMap = LinearMap.range A := by
  ext y
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (conjugacy_range_mem_iff e L A h x).mp hx
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    apply (conjugacy_range_mem_iff e L A h (e.symm y)).mpr
    simpa only [e.apply_symm_apply] using hy

private def Elliptic.HigherHomology.conjugacyKernelEquiv {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] (e : M ≃ₗ[ℤ] N) (L : M →ₗ[ℤ] M) (A : N →ₗ[ℤ] N)
    (h : ∀ x, e (L x) = A (e x)) : LinearMap.ker L ≃ₗ[ℤ] LinearMap.ker A :=
  (@LinearEquiv.toAddEquiv _ _ _ _ _ _ _ _ _ _ _ _ (LinearMap.ker L).module
      (LinearMap.ker A).module (e.ofSubmodules _ _ (conjugacy_map_ker e L A h))).toIntLinearEquiv

private def
    Elliptic.HigherHomology.conjugacyCokernelEquiv {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] (e : M ≃ₗ[ℤ] N) (L : M →ₗ[ℤ] M) (A : N →ₗ[ℤ] N)
    (h : ∀ x, e (L x) = A (e x)) : (M ⧸ LinearMap.range L) ≃ₗ[ℤ] (N ⧸ LinearMap.range A) :=
  (@LinearEquiv.toAddEquiv _ _ _ _ _ _ _ _ _ _ _ _ (Submodule.Quotient.module (LinearMap.range L))
      (Submodule.Quotient.module (LinearMap.range A))
      (Submodule.Quotient.equiv _ _ e (conjugacy_map_range e L A h))).toIntLinearEquiv

private def
    Elliptic.HigherHomology.shortExtensionLiftOne {M : Type*} [AddCommGroup M] [modM : Module ℤ M]
    (d : M →ₗ[ℤ] ℤ) (hd : Function.Surjective d) : M :=
  Classical.choose (hd 1)

@[simp]
private theorem Elliptic.HigherHomology.shortExtensionLiftOne_boundary {M : Type*} [AddCommGroup M]
    [modM : Module ℤ M] (d : M →ₗ[ℤ] ℤ) (hd : Function.Surjective d) :
    d (shortExtensionLiftOne d hd) = 1 :=
  Classical.choose_spec (hd 1)

private theorem
    Elliptic.HigherHomology.shortExtension_boundary_inclusion {A M : Type*} [AddCommGroup A]
    [Module ℤ A] [AddCommGroup M] [modM : Module ℤ M] (i : A →ₗ[ℤ] M) (d : M →ₗ[ℤ] ℤ)
    (hexact : LinearMap.range i = LinearMap.ker d) (a : A) : d (i a) = 0 := by
  have ha : i a ∈ LinearMap.range i := ⟨a, rfl⟩
  rw [hexact] at ha
  exact ha

private def
    Elliptic.HigherHomology.shortExtensionAssembly {A M : Type*} [AddCommGroup A] [Module ℤ A]
    [AddCommGroup M] [modM : Module ℤ M] (i : A →ₗ[ℤ] M) (u : M) : A × ℤ →ₗ[ℤ] M
    where
  toFun x := i x.1 + x.2 • u
  map_add' x
    y := by
    simp only [Prod.fst_add, Prod.snd_add, map_add, add_zsmul]
    abel
  map_smul' r
    x := by
    change i (r • x.1) + (r * x.2) • u = modM.smul r (i x.1 + x.2 • u)
    rw [int_smul_eq_zsmul]
    simp [map_zsmul, mul_zsmul, zsmul_add]

@[simp]
private theorem Elliptic.HigherHomology.shortExtensionAssembly_apply {A M : Type*} [AddCommGroup A]
    [Module ℤ A] [AddCommGroup M] [modM : Module ℤ M] (i : A →ₗ[ℤ] M) (u : M) (x : A × ℤ) :
    shortExtensionAssembly i u x = i x.1 + x.2 • u :=
  rfl

private theorem
    Elliptic.HigherHomology.shortExtensionAssembly_boundary {A M : Type*} [AddCommGroup A]
    [Module ℤ A] [AddCommGroup M] [modM : Module ℤ M] (i : A →ₗ[ℤ] M) (d : M →ₗ[ℤ] ℤ)
    (hexact : LinearMap.range i = LinearMap.ker d) (u : M) (hu : d u = 1) (x : A × ℤ) :
    d (shortExtensionAssembly i u x) = x.2 := by
  simp [shortExtensionAssembly_apply, shortExtension_boundary_inclusion i d hexact, hu]

private theorem
    Elliptic.HigherHomology.shortExtensionAssembly_injective {A M : Type*} [AddCommGroup A]
    [Module ℤ A] [AddCommGroup M] [modM : Module ℤ M] (i : A →ₗ[ℤ] M) (d : M →ₗ[ℤ] ℤ)
    (hi : Function.Injective i) (hexact : LinearMap.range i = LinearMap.ker d) (u : M)
    (hu : d u = 1) : Function.Injective (shortExtensionAssembly i u) := by
  intro x y hxy
  have hs : x.2 = y.2 := by
    have h := congrArg d hxy
    simpa only [shortExtensionAssembly_boundary i d hexact u hu] using h
  have ha : x.1 = y.1 := by
    apply hi
    apply add_right_cancel (b := x.2 • u)
    simpa only [shortExtensionAssembly_apply, hs] using hxy
  exact Prod.ext ha hs

private theorem
    Elliptic.HigherHomology.shortExtensionAssembly_surjective {A M : Type*} [AddCommGroup A]
    [Module ℤ A] [AddCommGroup M] [modM : Module ℤ M] (i : A →ₗ[ℤ] M) (d : M →ₗ[ℤ] ℤ)
    (hexact : LinearMap.range i = LinearMap.ker d) (u : M) (hu : d u = 1) :
    Function.Surjective (shortExtensionAssembly i u) := by
  intro x
  have hx : x - d x • u ∈ LinearMap.range i := by
    rw [hexact]
    change d (x - d x • u) = 0
    simp [hu]
  obtain ⟨a, ha⟩ := hx
  refine ⟨(a, d x), ?_⟩
  change i a + d x • u = x
  rw [ha, sub_add_cancel]

private def
    Elliptic.HigherHomology.shortExtensionProductEquiv {A M : Type*} [AddCommGroup A] [Module ℤ A]
    [AddCommGroup M] [modM : Module ℤ M] (i : A →ₗ[ℤ] M) (d : M →ₗ[ℤ] ℤ)
    (hi : Function.Injective i) (hd : Function.Surjective d)
    (hexact : LinearMap.range i = LinearMap.ker d) : M ≃ₗ[ℤ] A × ℤ :=
  (LinearEquiv.ofBijective (shortExtensionAssembly i (shortExtensionLiftOne d hd))
      ⟨shortExtensionAssembly_injective i d hi hexact _ (shortExtensionLiftOne_boundary d hd),
        shortExtensionAssembly_surjective i d hexact _
          (shortExtensionLiftOne_boundary d hd)⟩).symm

@[simp]
private theorem Elliptic.HigherHomology.shortExtensionProductEquiv_symm_apply {A M : Type*}
    [AddCommGroup A] [Module ℤ A] [AddCommGroup M] [modM : Module ℤ M] (i : A →ₗ[ℤ] M)
    (d : M →ₗ[ℤ] ℤ) (hi : Function.Injective i) (hd : Function.Surjective d)
    (hexact : LinearMap.range i = LinearMap.ker d) (x : A × ℤ) :
    (shortExtensionProductEquiv i d hi hd hexact).symm x =
      i x.1 + x.2 • shortExtensionLiftOne d hd :=
  rfl

@[simp]
private theorem
    Elliptic.HigherHomology.shortExtensionProductEquiv_snd {A M : Type*} [AddCommGroup A]
    [Module ℤ A] [AddCommGroup M] [modM : Module ℤ M] (i : A →ₗ[ℤ] M) (d : M →ₗ[ℤ] ℤ)
    (hi : Function.Injective i) (hd : Function.Surjective d)
    (hexact : LinearMap.range i = LinearMap.ker d) (x : M) :
    (shortExtensionProductEquiv i d hi hd hexact x).2 = d x := by
  obtain ⟨y, rfl⟩ := (shortExtensionProductEquiv i d hi hd hexact).symm.surjective x
  rw [LinearEquiv.apply_symm_apply, shortExtensionProductEquiv_symm_apply]
  simp [shortExtension_boundary_inclusion i d hexact]

@[simp]
private theorem Elliptic.HigherHomology.shortExtensionProductEquiv_inclusion {A M : Type*}
    [AddCommGroup A] [Module ℤ A] [AddCommGroup M] [modM : Module ℤ M] (i : A →ₗ[ℤ] M)
    (d : M →ₗ[ℤ] ℤ) (hi : Function.Injective i) (hd : Function.Surjective d)
    (hexact : LinearMap.range i = LinearMap.ker d) (a : A) :
    shortExtensionProductEquiv i d hi hd hexact (i a) = (a, 0) := by
  apply (shortExtensionProductEquiv i d hi hd hexact).symm.injective
  simp


private def Elliptic.HigherHomology.shortExtensionEndpointCoordinates {A : Type*} [AddCommGroup A]
    [Module ℤ A] (eA : A ≃ₗ[ℤ] ℤ) : (A × ℤ) ≃ₗ[ℤ] (Fin 2 → ℤ)
    where
  toFun x := ![eA x.1, x.2]
  invFun x := (eA.symm (x 0), x 1)
  left_inv x := by simp
  right_inv x := by ext k; fin_cases k <;> simp
  map_add' x y := by ext k; fin_cases k <;> simp
  map_smul' n x := by ext k; fin_cases k <;> simp

public
theorem Elliptic.HigherHomology.shortExtension_normalized_boundary_ker {M : Type*}
    [AddCommGroup M] [modM : Module ℤ M] {B : Type*} [AddCommGroup B] [Module ℤ B] (d : M →ₗ[ℤ] B)
    (eB : B ≃ₗ[ℤ] ℤ) : LinearMap.ker (eB.toLinearMap.comp d) = LinearMap.ker d := by
  ext x
  change eB (d x) = 0 ↔ d x = 0
  exact eB.map_eq_zero_iff

private def
    Elliptic.HigherHomology.shortExtensionFinTwoEquivOfEndpoints {A M : Type*} [AddCommGroup A]
    [Module ℤ A] [AddCommGroup M] [modM : Module ℤ M] {B : Type*} [AddCommGroup B] [Module ℤ B]
    (i : A →ₗ[ℤ] M) (d : M →ₗ[ℤ] B) (eA : A ≃ₗ[ℤ] ℤ) (eB : B ≃ₗ[ℤ] ℤ) (hi : Function.Injective i)
    (hd : Function.Surjective d) (hexact : LinearMap.range i = LinearMap.ker d) :
    M ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  (shortExtensionProductEquiv i (eB.toLinearMap.comp d) hi (eB.surjective.comp hd)
        (hexact.trans (shortExtension_normalized_boundary_ker d eB).symm)).trans
    (shortExtensionEndpointCoordinates eA)

@[simp]
private theorem Elliptic.HigherHomology.shortExtensionFinTwoEquivOfEndpoints_one {A M : Type*}
    [AddCommGroup A] [Module ℤ A] [AddCommGroup M] [modM : Module ℤ M] {B : Type*}
    [AddCommGroup B] [Module ℤ B] (i : A →ₗ[ℤ] M) (d : M →ₗ[ℤ] B) (eA : A ≃ₗ[ℤ] ℤ)
    (eB : B ≃ₗ[ℤ] ℤ) (hi : Function.Injective i) (hd : Function.Surjective d)
    (hexact : LinearMap.range i = LinearMap.ker d) (x : M) :
    shortExtensionFinTwoEquivOfEndpoints i d eA eB hi hd hexact x 1 = eB (d x) :=
  shortExtensionProductEquiv_snd i (eB.toLinearMap.comp d) hi (eB.surjective.comp hd)
    (hexact.trans (shortExtension_normalized_boundary_ker d eB).symm) x

@[simp]
private theorem Elliptic.HigherHomology.shortExtensionFinTwoEquivOfEndpoints_inclusion {A M : Type*}
    [AddCommGroup A] [Module ℤ A] [AddCommGroup M] [modM : Module ℤ M] {B : Type*}
    [AddCommGroup B] [Module ℤ B] (i : A →ₗ[ℤ] M) (d : M →ₗ[ℤ] B) (eA : A ≃ₗ[ℤ] ℤ)
    (eB : B ≃ₗ[ℤ] ℤ) (hi : Function.Injective i) (hd : Function.Surjective d)
    (hexact : LinearMap.range i = LinearMap.ker d) (a : A) :
    shortExtensionFinTwoEquivOfEndpoints i d eA eB hi hd hexact (i a) = ![eA a, 0] := by
  change
    shortExtensionEndpointCoordinates eA
        (shortExtensionProductEquiv i (eB.toLinearMap.comp d) hi (eB.surjective.comp hd)
          (hexact.trans (shortExtension_normalized_boundary_ker d eB).symm) (i a)) =
      _
  rw [shortExtensionProductEquiv_inclusion]
  rfl

private def Elliptic.HigherHomology.mappingTorusKernelOneEquiv (j : Elliptic.Kind) :
    LinearMap.ker (MappingTorusHomology.wangDifference (fibreTorusHomeomorph j).symm 1) ≃ₗ[ℤ] ℤ :=
  (conjugacyKernelEquiv torusH1Equiv _ _ (mappingTorusDifference_one j)).trans
    (fibreInverseKernelEquivInt j)

private def Elliptic.HigherHomology.mappingTorusCokernelOneEquiv (j : Elliptic.Kind) :
    (SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 1 ⧸
        LinearMap.range
          (MappingTorusHomology.wangDifference (fibreTorusHomeomorph j).symm 1)) ≃ₗ[ℤ]
      ℤ :=
  (conjugacyCokernelEquiv torusH1Equiv _ _ (mappingTorusDifference_one j)).trans
    (fibreInverseCokernelEquivInt j)

@[simp]
private theorem Elliptic.HigherHomology.mappingTorusCokernelOneEquiv_mk (j : Elliptic.Kind)
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 1) :
    mappingTorusCokernelOneEquiv j (Submodule.Quotient.mk a) =
      fibreCoinvariantCoordinate j (torusH1Equiv a) :=
  rfl

private def Elliptic.HigherHomology.mappingTorusKernelTwoEquiv (j : Elliptic.Kind) :
    LinearMap.ker (MappingTorusHomology.wangDifference (fibreTorusHomeomorph j).symm 2) ≃ₗ[ℤ] ℤ :=
  (conjugacyKernelEquiv torusH2Coordinates _ _ (mappingTorusDifference_two j)).trans
    (fibreSquareInverseKernelEquivInt j)

private def Elliptic.HigherHomology.mappingTorusCokernelTwoEquiv (j : Elliptic.Kind) :
    (SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 2 ⧸
        LinearMap.range
          (MappingTorusHomology.wangDifference (fibreTorusHomeomorph j).symm 2)) ≃ₗ[ℤ]
      ℤ :=
  (conjugacyCokernelEquiv torusH2Coordinates _ _ (mappingTorusDifference_two j)).trans
    (fibreSquareInverseCokernelEquivInt j)

@[simp]
private theorem Elliptic.HigherHomology.mappingTorusCokernelTwoEquiv_mk (j : Elliptic.Kind)
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 2) :
    mappingTorusCokernelTwoEquiv j (Submodule.Quotient.mk a) = torusH2Coordinates a 0 :=
  rfl

private def Elliptic.HigherHomology.mappingTorusKernelThreeEquiv (j : Elliptic.Kind) :
    LinearMap.ker (MappingTorusHomology.wangDifference (fibreTorusHomeomorph j).symm 3) ≃ₗ[ℤ] ℤ :=
  by
  letI :=
    (LinearMap.ker (MappingTorusHomology.wangDifference (fibreTorusHomeomorph j).symm 3)).module
  letI :=
    (⊤ :
        Submodule ℤ
          (SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3)
            3)).module
  exact
    (((LinearEquiv.ofEq
                (LinearMap.ker
                  (MappingTorusHomology.wangDifference (fibreTorusHomeomorph j).symm 3))
                (⊤ :
                  Submodule ℤ
                    (SingularMayerVietoris.SingularHomology
                      (PeriodTorusHigherHomology.ProductTorus 3) 3))
                (by rw [mappingTorusDifference_three, LinearMap.ker_zero])).toAddEquiv.trans
            Submodule.topEquiv.toAddEquiv).trans
        torusH3Coordinates.toAddEquiv).toIntLinearEquiv

private def Elliptic.HigherHomology.mappingTorusCokernelThreeEquiv (j : Elliptic.Kind) :
    (SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 3 ⧸
        LinearMap.range
          (MappingTorusHomology.wangDifference (fibreTorusHomeomorph j).symm 3)) ≃ₗ[ℤ]
      ℤ := by
  letI :=
    Submodule.Quotient.module
      (LinearMap.range (MappingTorusHomology.wangDifference (fibreTorusHomeomorph j).symm 3))
  exact
    ((Submodule.quotEquivOfEqBot
            (LinearMap.range
              (MappingTorusHomology.wangDifference (fibreTorusHomeomorph j).symm 3))
            (by rw [mappingTorusDifference_three, LinearMap.range_zero])).toAddEquiv.trans
        torusH3Coordinates.toAddEquiv).toIntLinearEquiv

@[simp]
private theorem Elliptic.HigherHomology.mappingTorusCokernelThreeEquiv_mk (j : Elliptic.Kind)
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 3) :
    mappingTorusCokernelThreeEquiv j (Submodule.Quotient.mk a) = torusH3Coordinates a :=
  rfl

private def Elliptic.HigherHomology.mappingTorusH2Equiv (j : Elliptic.Kind) :
    SingularMayerVietoris.SingularHomology (mappingTorusModel j) 2 ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  shortExtensionFinTwoEquivOfEndpoints
    (MappingTorusHomology.cokernelInclusion (fibreTorusHomeomorph j).symm 2)
    (MappingTorusHomology.kernelBoundary (fibreTorusHomeomorph j).symm 1)
    (mappingTorusCokernelTwoEquiv j) (mappingTorusKernelOneEquiv j)
    (MappingTorusHomology.cokernelInclusion_injective _ _)
    (MappingTorusHomology.kernelBoundary_surjective _ _)
    (MappingTorusHomology.cokernelInclusion_range_eq_ker_kernelBoundary _ _)

private theorem Elliptic.HigherHomology.mappingTorusH2Equiv_boundary (j : Elliptic.Kind)
    (a : SingularMayerVietoris.SingularHomology (mappingTorusModel j) 2) :
    mappingTorusH2Equiv j a 1 =
      torusH1Equiv (MappingTorusHomology.wangBoundary (fibreTorusHomeomorph j).symm 1 a) 2 := by
  exact shortExtensionFinTwoEquivOfEndpoints_one _ _ _ _ _ _ _ a

private theorem Elliptic.HigherHomology.mappingTorusH2Equiv_fibre (j : Elliptic.Kind)
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 2) :
    mappingTorusH2Equiv j
        (MappingTorusHomology.fibreHomologyMap (fibreTorusHomeomorph j).symm 2 a) =
      ![torusH2Coordinates a 0, 0] := by
  change
    mappingTorusH2Equiv j
        (MappingTorusHomology.cokernelInclusion (fibreTorusHomeomorph j).symm 2
          (Submodule.Quotient.mk a)) =
      _
  rw [mappingTorusH2Equiv, shortExtensionFinTwoEquivOfEndpoints_inclusion,
    mappingTorusCokernelTwoEquiv_mk]

private def Elliptic.HigherHomology.mappingTorusH3Equiv (j : Elliptic.Kind) :
    SingularMayerVietoris.SingularHomology (mappingTorusModel j) 3 ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  shortExtensionFinTwoEquivOfEndpoints
    (MappingTorusHomology.cokernelInclusion (fibreTorusHomeomorph j).symm 3)
    (MappingTorusHomology.kernelBoundary (fibreTorusHomeomorph j).symm 2)
    (mappingTorusCokernelThreeEquiv j) (mappingTorusKernelTwoEquiv j)
    (MappingTorusHomology.cokernelInclusion_injective _ _)
    (MappingTorusHomology.kernelBoundary_surjective _ _)
    (MappingTorusHomology.cokernelInclusion_range_eq_ker_kernelBoundary _ _)

private theorem Elliptic.HigherHomology.mappingTorusH3Equiv_boundary (j : Elliptic.Kind)
    (a : SingularMayerVietoris.SingularHomology (mappingTorusModel j) 3) :
    mappingTorusH3Equiv j a 1 =
      -(torusH2Coordinates (MappingTorusHomology.wangBoundary (fibreTorusHomeomorph j).symm 2 a)
          1) := by exact shortExtensionFinTwoEquivOfEndpoints_one _ _ _ _ _ _ _ a

private theorem Elliptic.HigherHomology.mappingTorusH3Equiv_fibre (j : Elliptic.Kind)
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 3) :
    mappingTorusH3Equiv j
        (MappingTorusHomology.fibreHomologyMap (fibreTorusHomeomorph j).symm 3 a) =
      ![torusH3Coordinates a, 0] := by
  change
    mappingTorusH3Equiv j
        (MappingTorusHomology.cokernelInclusion (fibreTorusHomeomorph j).symm 3
          (Submodule.Quotient.mk a)) =
      _
  rw [mappingTorusH3Equiv, shortExtensionFinTwoEquivOfEndpoints_inclusion,
    mappingTorusCokernelThreeEquiv_mk]

private theorem
    Elliptic.HigherHomology.mappingTorusKernelBoundary_three_injective (j : Elliptic.Kind) :
    Function.Injective (MappingTorusHomology.kernelBoundary (fibreTorusHomeomorph j).symm 3) := by
  have :=
    PeriodTorusHigherHomology.productTorus_homology_subsingleton_of_lt (show 3 < 4 by decide)
  intro a b hab
  have hzero : MappingTorusHomology.wangBoundary (fibreTorusHomeomorph j).symm 3 (a - b) = 0 := by
    rw [map_sub]
    exact sub_eq_zero.mpr (congrArg Subtype.val hab)
  have hmem :
    a - b ∈ LinearMap.ker (MappingTorusHomology.wangBoundary (fibreTorusHomeomorph j).symm 3) :=
    hzero
  rw [← MappingTorusHomology.wang_exact_at_mappingTorus] at hmem
  obtain ⟨v, hv⟩ := hmem
  have hv0 : v = 0 := Subsingleton.elim _ _
  rw [hv0, map_zero] at hv
  exact sub_eq_zero.mp hv.symm

private def Elliptic.HigherHomology.mappingTorusH4Equiv (j : Elliptic.Kind) :
    SingularMayerVietoris.SingularHomology (mappingTorusModel j) 4 ≃ₗ[ℤ] ℤ :=
  (LinearEquiv.ofBijective (MappingTorusHomology.kernelBoundary (fibreTorusHomeomorph j).symm 3)
        ⟨mappingTorusKernelBoundary_three_injective j,
          MappingTorusHomology.kernelBoundary_surjective _ _⟩).trans
    (mappingTorusKernelThreeEquiv j)

private theorem Elliptic.HigherHomology.mappingTorusH4Equiv_boundary (j : Elliptic.Kind)
    (a : SingularMayerVietoris.SingularHomology (mappingTorusModel j) 4) :
    mappingTorusH4Equiv j a =
      torusH3Coordinates (MappingTorusHomology.wangBoundary (fibreTorusHomeomorph j).symm 3 a) :=
  rfl

private abbrev Elliptic.HigherHomology.torusH0Coordinates :
    SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 0 ≃ₗ[ℤ] ℤ :=
  PeriodTorusHigherHomology.connectedHomologyZeroEquiv (PeriodTorusHigherHomology.ProductTorus 3)

private theorem Elliptic.HigherHomology.torusH0Coordinates_pointClass
    (x : PeriodTorusHigherHomology.ProductTorus 3) :
    torusH0Coordinates (PeriodTorusHigherHomology.pointClass x) = 1 :=
  PeriodTorusHigherHomology.connectedHomologyZeroEquiv_pointClass x

private theorem Elliptic.HigherHomology.mappingTorusMonodromy_zero (j : Elliptic.Kind)
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 0) :
    torusH0Coordinates
        (MappingTorusHomology.monodromyHomologyMap (fibreTorusHomeomorph j).symm 0 a) =
      torusH0Coordinates a :=
  PeriodTorusHigherHomology.connectedHomologyZeroEquiv_natural
    ((fibreTorusHomeomorph j).symm :
      C(PeriodTorusHigherHomology.ProductTorus 3, PeriodTorusHigherHomology.ProductTorus 3))
    a

private theorem Elliptic.HigherHomology.mappingTorusDifference_zero (j : Elliptic.Kind) :
    MappingTorusHomology.wangDifference (fibreTorusHomeomorph j).symm 0 = 0 := by
  ext a
  apply torusH0Coordinates.injective
  change
    torusH0Coordinates
        (a - MappingTorusHomology.monodromyHomologyMap (fibreTorusHomeomorph j).symm 0 a) =
      torusH0Coordinates 0
  rw [map_sub, mappingTorusMonodromy_zero, sub_self, map_zero]

private def Elliptic.HigherHomology.mappingTorusKernelZeroEquiv (j : Elliptic.Kind) :
    LinearMap.ker (MappingTorusHomology.wangDifference (fibreTorusHomeomorph j).symm 0) ≃ₗ[ℤ] ℤ :=
  by
  letI :=
    (LinearMap.ker (MappingTorusHomology.wangDifference (fibreTorusHomeomorph j).symm 0)).module
  letI :=
    (⊤ :
        Submodule ℤ
          (SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3)
            0)).module
  exact
    (((LinearEquiv.ofEq
                (LinearMap.ker
                  (MappingTorusHomology.wangDifference (fibreTorusHomeomorph j).symm 0))
                (⊤ :
                  Submodule ℤ
                    (SingularMayerVietoris.SingularHomology
                      (PeriodTorusHigherHomology.ProductTorus 3) 0))
                (by rw [mappingTorusDifference_zero, LinearMap.ker_zero])).toAddEquiv.trans
            Submodule.topEquiv.toAddEquiv).trans
        torusH0Coordinates.toAddEquiv).toIntLinearEquiv

private def Elliptic.HigherHomology.mappingTorusCokernelZeroEquiv (j : Elliptic.Kind) :
    (SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 0 ⧸
        LinearMap.range
          (MappingTorusHomology.wangDifference (fibreTorusHomeomorph j).symm 0)) ≃ₗ[ℤ]
      ℤ := by
  letI :=
    Submodule.Quotient.module
      (LinearMap.range (MappingTorusHomology.wangDifference (fibreTorusHomeomorph j).symm 0))
  exact
    ((Submodule.quotEquivOfEqBot
            (LinearMap.range
              (MappingTorusHomology.wangDifference (fibreTorusHomeomorph j).symm 0))
            (by rw [mappingTorusDifference_zero, LinearMap.range_zero])).toAddEquiv.trans
        torusH0Coordinates.toAddEquiv).toIntLinearEquiv

private def Elliptic.HigherHomology.mappingTorusH0Equiv (j : Elliptic.Kind) :
    SingularMayerVietoris.SingularHomology (mappingTorusModel j) 0 ≃ₗ[ℤ] ℤ :=
  (MappingTorusHomology.degreeZeroHomologyEquiv (fibreTorusHomeomorph j).symm).trans
    (mappingTorusCokernelZeroEquiv j)

private def Elliptic.HigherHomology.mappingTorusH1Equiv (j : Elliptic.Kind) :
    SingularMayerVietoris.SingularHomology (mappingTorusModel j) 1 ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  shortExtensionFinTwoEquivOfEndpoints
    (MappingTorusHomology.cokernelInclusion (fibreTorusHomeomorph j).symm 1)
    (MappingTorusHomology.kernelBoundary (fibreTorusHomeomorph j).symm 0)
    (mappingTorusCokernelOneEquiv j) (mappingTorusKernelZeroEquiv j)
    (MappingTorusHomology.cokernelInclusion_injective _ _)
    (MappingTorusHomology.kernelBoundary_surjective _ _)
    (MappingTorusHomology.cokernelInclusion_range_eq_ker_kernelBoundary _ _)

private theorem Elliptic.HigherHomology.mappingTorusH1Equiv_boundary (j : Elliptic.Kind)
    (a : SingularMayerVietoris.SingularHomology (mappingTorusModel j) 1) :
    mappingTorusH1Equiv j a 1 =
      torusH0Coordinates (MappingTorusHomology.wangBoundary (fibreTorusHomeomorph j).symm 0 a) := by
  exact shortExtensionFinTwoEquivOfEndpoints_one _ _ _ _ _ _ _ a

private theorem Elliptic.HigherHomology.mappingTorusH1Equiv_fibre (j : Elliptic.Kind)
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 1) :
    mappingTorusH1Equiv j
        (MappingTorusHomology.fibreHomologyMap (fibreTorusHomeomorph j).symm 1 a) =
      ![fibreCoinvariantCoordinate j (torusH1Equiv a), 0] := by
  change
    mappingTorusH1Equiv j
        (MappingTorusHomology.cokernelInclusion (fibreTorusHomeomorph j).symm 1
          (Submodule.Quotient.mk a)) =
      _
  rw [mappingTorusH1Equiv, shortExtensionFinTwoEquivOfEndpoints_inclusion,
    mappingTorusCokernelOneEquiv_mk]

private def Elliptic.psiOne : Lattice →ₗ[ℤ] ℤ
    where
  toFun w := 2 * w 1 + w 2 + 3 * w 3
  map_add' w z := by simp only [Pi.add_apply]; ring
  map_smul' a w := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

private def Elliptic.psiTwo : Lattice →ₗ[ℤ] ℤ
    where
  toFun w := w 1 + w 2 + 2 * w 3
  map_add' w z := by simp only [Pi.add_apply]; ring
  map_smul' a w := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

private def Elliptic.psi : Kind → Lattice →ₗ[ℤ] ℤ
  | .three => psiOne
  | .four => psiTwo

private def Elliptic.coinvariantMap (j : Kind) : Lattice →ₗ[ℤ] (Fin 2 → ℤ)
    where
  toFun w := ![γ w, psi j w]
  map_add' w z := by ext k; fin_cases k <;> simp [γ]
  map_smul' a
    w := by
    ext k
    fin_cases k
    · rfl
    · exact (psi j).map_smul a w

private def Elliptic.coinvariantSection (j : Kind) : (Fin 2 → ℤ) →ₗ[ℤ] Lattice
    where
  toFun
    c :=
    match j with
    | .three => ![c 0, 0, c 1, 0]
    | .four => ![c 0, c 1, 0, 0]
  map_add' c d := by cases j <;> ext k <;> fin_cases k <;> simp
  map_smul' a c := by cases j <;> ext k <;> fin_cases k <;> simp

@[simp]
private theorem Elliptic.coinvariantMap_section (j : Kind) (c : Fin 2 → ℤ) :
    coinvariantMap j (coinvariantSection j c) = c := by
  cases j <;> ext k <;> fin_cases k <;>
    simp [coinvariantMap, coinvariantSection, γ, psi, psiOne, psiTwo]

private theorem
    Elliptic.coinvariantMap_surjective (j : Kind) : Function.Surjective (coinvariantMap j) :=
  fun c => ⟨coinvariantSection j c, coinvariantMap_section j c⟩

private def Elliptic.coinvariantDifference (j : Kind) : Lattice →ₗ[ℤ] Lattice :=
  (j.matrix - 1).mulVecLin

private theorem Elliptic.coinvariantDifference_apply (j : Kind) (w : Lattice) :
    coinvariantDifference j w = j.matrix *ᵥ w - w := by simp [coinvariantDifference]

private theorem Elliptic.coinvariantMap_monodromy (j : Kind) (w : Lattice) :
    coinvariantMap j (j.matrix *ᵥ w) = coinvariantMap j w := by
  cases j <;> ext k <;> fin_cases k <;>
      simp [coinvariantMap, γ, psi, psiOne, psiTwo, Kind.matrix, A₁, A₂, dotProduct,
        Fin.sum_univ_succ] <;>
    ring

@[simp]
private theorem Elliptic.coinvariantMap_difference (j : Kind) (w : Lattice) :
    coinvariantMap j (coinvariantDifference j w) = 0 := by
  rw [coinvariantDifference_apply, map_sub, coinvariantMap_monodromy, sub_self]

private def Elliptic.coinvariantKernelLift (j : Kind) (w : Lattice) : Lattice :=
  match j with
  | .three => ![0, w 3, w 1 + w 3, 0]
  | .four => ![0, -w 1 - w 3, w 3, 0]

private theorem Elliptic.coinvariantDifference_kernelLift (j : Kind) (w : Lattice)
    (hw : coinvariantMap j w = 0) : coinvariantDifference j (coinvariantKernelLift j w) = w := by
  have h0 : w 0 = 0 := congrFun hw 0
  have hψ : psi j w = 0 := congrFun hw 1
  cases j with
  | three =>
    change 2 * w 1 + w 2 + 3 * w 3 = 0 at hψ
    ext k
    fin_cases k <;> simp [coinvariantDifference, coinvariantKernelLift, Kind.matrix, A₁] <;> omega
  | four =>
    change w 1 + w 2 + 2 * w 3 = 0 at hψ
    ext k
    fin_cases k <;> simp [coinvariantDifference, coinvariantKernelLift, Kind.matrix, A₂] <;> omega

private theorem Elliptic.coinvariantMap_ker_eq_range (j : Kind) :
    LinearMap.ker (coinvariantMap j) = LinearMap.range (coinvariantDifference j) := by
  ext w
  change coinvariantMap j w = 0 ↔ ∃ u, coinvariantDifference j u = w
  constructor
  · intro hw
    exact ⟨coinvariantKernelLift j w, coinvariantDifference_kernelLift j w hw⟩
  · rintro ⟨u, rfl⟩
    exact coinvariantMap_difference j u

private abbrev Elliptic.AffineAutomorphism :=
  RealCoordinates ≃ᵃ[ℝ] RealCoordinates

private theorem
    Elliptic.matrix_pow_pred_mul (j : Kind) : j.matrix ^ (j.order - 1) * j.matrix = 1 := by
  rw [← pow_succ, Nat.sub_add_cancel j.order_pos, j.matrix_pow_order]

private theorem
    Elliptic.matrix_mul_pow_pred (j : Kind) : j.matrix * j.matrix ^ (j.order - 1) = 1 := by
  rw [← pow_succ', Nat.sub_add_cancel j.order_pos, j.matrix_pow_order]

private theorem Elliptic.realMatrix_pow_pred_mul_mo1973_22121 (j : Kind) :
    (j.matrix.map (Int.castRingHom ℝ)) ^ (j.order - 1) * j.matrix.map (Int.castRingHom ℝ) = 1 := by
  rw [← Matrix.map_pow, ← Matrix.map_mul, matrix_pow_pred_mul]
  simp

private theorem Elliptic.realMatrix_mul_pow_pred_mo1973_22122 (j : Kind) :
    j.matrix.map (Int.castRingHom ℝ) * (j.matrix.map (Int.castRingHom ℝ)) ^ (j.order - 1) = 1 := by
  rw [← Matrix.map_pow, ← Matrix.map_mul, matrix_mul_pow_pred]
  simp

private def Elliptic.flatLinearEquiv (j : Kind) : RealCoordinates ≃ₗ[ℝ] RealCoordinates
    where
  __ := flatLinear j
  invFun x := (j.matrix.map (Int.castRingHom ℝ)) ^ (j.order - 1) *ᵥ x
  left_inv
    x := by
    change
      (j.matrix.map (Int.castRingHom ℝ)) ^ (j.order - 1) *ᵥ
          (j.matrix.map (Int.castRingHom ℝ) *ᵥ x) =
        x
    rw [Matrix.mulVec_mulVec, realMatrix_pow_pred_mul_mo1973_22121, Matrix.one_mulVec]
  right_inv
    x := by
    change
      j.matrix.map (Int.castRingHom ℝ) *ᵥ
          ((j.matrix.map (Int.castRingHom ℝ)) ^ (j.order - 1) *ᵥ x) =
        x
    rw [Matrix.mulVec_mulVec, realMatrix_mul_pow_pred_mo1973_22122, Matrix.one_mulVec]

private def Elliptic.realCastAddHom : Lattice →+ RealCoordinates
    where
  toFun := realCast
  map_zero' := by ext k; simp [realCast]
  map_add' w z := by ext k; simp [realCast]

private def Elliptic.integerTranslationHom : Multiplicative Lattice →* AffineAutomorphism :=
  (AffineEquiv.constVAddHom ℝ RealCoordinates).comp realCastAddHom.toMultiplicative

private def Elliptic.integerTranslation (w : Lattice) : AffineAutomorphism :=
  integerTranslationHom (Multiplicative.ofAdd w)

@[simp]
private theorem Elliptic.integerTranslation_apply (w : Lattice) (x : RealCoordinates) :
    integerTranslation w x = realCast w + x :=
  rfl

@[simp]
private theorem Elliptic.integerTranslation_zero : integerTranslation 0 = 1 :=
  integerTranslationHom.map_one

private theorem Elliptic.integerTranslation_add (w z : Lattice) :
    integerTranslation (w + z) = integerTranslation w * integerTranslation z :=
  integerTranslationHom.map_mul (Multiplicative.ofAdd w) (Multiplicative.ofAdd z)

@[simp]
private theorem Elliptic.integerTranslation_neg (w : Lattice) :
    integerTranslation (-w) = (integerTranslation w)⁻¹ :=
  integerTranslationHom.map_inv (Multiplicative.ofAdd w)

private def Elliptic.affineGenerator (j : Kind) (v : Lattice) : AffineAutomorphism
    where
  toFun := flatAffine j v
  invFun x := (flatLinearEquiv j).symm (x - (1 / (j.order : ℝ)) • realCast v)
  left_inv
    x := by
    change
      (flatLinearEquiv j).symm
          ((flatLinearEquiv j x + (1 / (j.order : ℝ)) • realCast v) -
            (1 / (j.order : ℝ)) • realCast v) =
        x
    rw [add_sub_cancel_right, LinearEquiv.symm_apply_apply]
  right_inv
    x := by
    change
      flatLinearEquiv j ((flatLinearEquiv j).symm (x - (1 / (j.order : ℝ)) • realCast v)) +
          (1 / (j.order : ℝ)) • realCast v =
        x
    rw [LinearEquiv.apply_symm_apply, sub_add_cancel]
  linear := flatLinearEquiv j
  map_vadd' x
    w := by
    change
      flatLinear j (w + x) + (1 / (j.order : ℝ)) • realCast v =
        flatLinear j w + (flatLinear j x + (1 / (j.order : ℝ)) • realCast v)
    rw [map_add, add_assoc]

@[simp]
private theorem Elliptic.affineGenerator_apply (j : Kind) (v : Lattice) (x : RealCoordinates) :
    affineGenerator j v x = flatAffine j v x :=
  rfl

private theorem
    Elliptic.affineAutomorphism_mul_apply (f g : AffineAutomorphism) (x : RealCoordinates) :
    (f * g) x = f (g x) :=
  rfl

private theorem Elliptic.affineAutomorphism_pow_apply (f : AffineAutomorphism) (n : ℕ)
    (x : RealCoordinates) : (f ^ n) x = (f : RealCoordinates → RealCoordinates)^[n] x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', affineAutomorphism_mul_apply, ih, Function.iterate_succ_apply']

private theorem Elliptic.affineGenerator_pow_apply (j : Kind) (v : Lattice) (n : ℕ)
    (x : RealCoordinates) : (affineGenerator j v ^ n) x = (flatAffine j v)^[n] x :=
  affineAutomorphism_pow_apply _ _ _

private theorem Elliptic.affineGenerator_translation (j : Kind) (v w : Lattice) :
    affineGenerator j v * integerTranslation w =
      integerTranslation (j.matrix *ᵥ w) * affineGenerator j v := by
  ext x
  simp only [affineAutomorphism_mul_apply, affineGenerator_apply, integerTranslation_apply,
    flatAffine, map_add, flatLinear_realCast, add_assoc]

private theorem
    Elliptic.affineGenerator_pow_order (j : Kind) (v : Lattice) (hv : j.matrix *ᵥ v = v) :
    affineGenerator j v ^ j.order = integerTranslation v := by
  ext x
  rw [affineGenerator_pow_apply, flatAffine_iterate_order j v hv, integerTranslation_apply,
    add_comm]

private theorem Elliptic.affineGenerator_pow_translation (j : Kind) (v w : Lattice) (n : ℕ) :
    affineGenerator j v ^ n * integerTranslation w =
      integerTranslation (j.matrix ^ n *ᵥ w) * affineGenerator j v ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      affineGenerator j v ^ (n + 1) * integerTranslation w =
          affineGenerator j v * (affineGenerator j v ^ n * integerTranslation w) := by
        rw [pow_succ', mul_assoc]
      _ =
          affineGenerator j v *
            (integerTranslation (j.matrix ^ n *ᵥ w) * affineGenerator j v ^ n) := by rw [ih]
      _ =
          (affineGenerator j v * integerTranslation (j.matrix ^ n *ᵥ w)) *
            affineGenerator j v ^ n :=
        (mul_assoc _ _ _).symm
      _ =
          (integerTranslation (j.matrix *ᵥ (j.matrix ^ n *ᵥ w)) * affineGenerator j v) *
            affineGenerator j v ^ n := by rw [affineGenerator_translation]
      _ = integerTranslation (j.matrix ^ (n + 1) *ᵥ w) * affineGenerator j v ^ (n + 1) := by
        rw [mul_assoc, ← pow_succ', Matrix.mulVec_mulVec, ← pow_succ']

private theorem Elliptic.affineAutomorphism_continuous (f : AffineAutomorphism) : Continuous f :=
  f.continuous_of_finiteDimensional

private theorem Elliptic.flatProjection_isCoveringMap (p : PeriodDomain) :
    IsCoveringMap (flatProjection p) := by
  have hq : IsAddQuotientCoveringMap p.lattice.mkQ p.lattice.toAddSubgroup := by
    apply p.lattice.toAddSubgroup.isAddQuotientCoveringMap_of_comm
    change IsDiscrete (p.lattice : Set ComplexPlane₂)
    let : DiscreteTopology (p.lattice : Set ComplexPlane₂) := p.lattice_discrete
    exact DiscreteTopology.isDiscrete
  exact hq.isCoveringMap.comp_homeomorph (periodEquiv p).toHomeomorph

private def Elliptic.affineCoverProjection (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) : RealCoordinates → Surface j p v hv :=
  surfaceProjection j p v hv ∘ flatProjection p.val

private theorem
    Elliptic.affineCoverProjection_continuous (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) : Continuous (affineCoverProjection j p v hv) :=
  (surfaceProjection_continuous j p v hv).comp (flatProjection_continuous p.val)

private theorem
    Elliptic.affineCoverProjection_surjective (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) : Function.Surjective (affineCoverProjection j p v hv) :=
  (surfaceProjection_surjective j p v hv).comp (flatProjection_surjective p.val)

private theorem Elliptic.affineCoverProjection_eq_iff_flatCongruent (j : Kind) (p : FixedPeriod j)
    (v : Lattice) (hv : AdmissibleTwist j v) (x y : RealCoordinates) :
    affineCoverProjection j p v hv x = affineCoverProjection j p v hv y ↔
      ∃ r : ℕ, r < j.order ∧ FlatCongruent x ((flatAffine j v)^[r] y) := by
  let := affineAction j p v hv.1
  change
    FiniteQuotient.project (CyclicGroup j) p.val.Torus (flatProjection p.val x) =
        FiniteQuotient.project (CyclicGroup j) p.val.Torus (flatProjection p.val y) ↔
      _
  rw [FiniteQuotient.project_eq_iff_mem_orbit]
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨g.toAdd.val, ZMod.val_lt _, (flatProjection_eq_iff p.val _ _).mp ?_⟩
    have hA :
      g • flatProjection p.val y = flatProjection p.val ((flatAffine j v)^[g.toAdd.val] y) :=
      affinePermutation_pow_flatProjection j p v g.toAdd.val y
    exact hg.symm.trans hA
  · rintro ⟨r, hr, hxy⟩
    refine ⟨Multiplicative.ofAdd (r : ZMod j.order), ?_⟩
    change
      (affinePermutation j p v ^ (r : ZMod j.order).val) (flatProjection p.val y) =
        flatProjection p.val x
    rw [ZMod.val_natCast_of_lt hr, affinePermutation_pow_flatProjection]
    exact ((flatProjection_eq_iff p.val _ _).mpr hxy).symm

private theorem Elliptic.affineCoverProjection_eq_iff_translate (j : Kind) (p : FixedPeriod j)
    (v : Lattice) (hv : AdmissibleTwist j v) (x y : RealCoordinates) :
    affineCoverProjection j p v hv x = affineCoverProjection j p v hv y ↔
      ∃ r : ℕ, r < j.order ∧ ∃ w : Lattice, x = realCast w + (flatAffine j v)^[r] y := by
  rw [affineCoverProjection_eq_iff_flatCongruent]
  simp only [FlatCongruent, sub_eq_iff_eq_add]

private theorem Elliptic.realCast_injective : Function.Injective realCast := by
  intro w z h
  funext i
  have hi := congrFun h i
  change (w i : ℝ) = (z i : ℝ) at hi
  exact_mod_cast hi

private theorem Elliptic.affineTranslate_unique (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) (x : RealCoordinates) (r s : Fin j.order) (w z : Lattice)
    (h : realCast w + (flatAffine j v)^[r.val] x = realCast z + (flatAffine j v)^[s.val] x) :
    r = s ∧ w = z := by
  let := affineAction j p v hv.1
  let := affineAction_free j p v hv
  have hproj := congrArg (flatProjection p.val) h
  simp only [flatProjection_add, flatProjection_realCast, zero_add] at hproj
  have hsmul :
    Multiplicative.ofAdd (r.val : ZMod j.order) • flatProjection p.val x =
      Multiplicative.ofAdd (s.val : ZMod j.order) • flatProjection p.val x := by
    change
      (affinePermutation j p v ^ (r.val : ZMod j.order).val) (flatProjection p.val x) =
        (affinePermutation j p v ^ (s.val : ZMod j.order).val) (flatProjection p.val x)
    rw [ZMod.val_natCast_of_lt r.isLt, ZMod.val_natCast_of_lt s.isLt,
      affinePermutation_pow_flatProjection, affinePermutation_pow_flatProjection]
    exact hproj
  have hg := IsCancelSMul.right_cancel _ _ (flatProjection p.val x) hsmul
  have hval := congrArg (fun g : CyclicGroup j => g.toAdd.val) hg
  change (r.val : ZMod j.order).val = (s.val : ZMod j.order).val at hval
  rw [ZMod.val_natCast_of_lt r.isLt, ZMod.val_natCast_of_lt s.isLt] at hval
  have hrs : r = s := Fin.ext hval
  subst s
  exact ⟨rfl, realCast_injective (add_right_cancel h)⟩

private theorem Elliptic.surfaceProjection_fibre_finite (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) (x : Surface j p v hv) :
    Finite (surfaceProjection j p v hv ⁻¹' { x }) := by
  apply Nat.finite_of_card_ne_zero
  rw [surfaceProjection_fibre_card]
  exact Nat.ne_of_gt j.order_pos

private theorem
    Elliptic.affineCoverProjection_isCoveringMap (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) : IsCoveringMap (affineCoverProjection j p v hv) :=
  CoveringComposition.covering_comp_of_finite_fibres (flatProjection_isCoveringMap p.val)
    (surfaceProjection_isCoveringMap j p v hv) (surfaceProjection_fibre_finite j p v hv)

private def Elliptic.affineNormalForm (j : Kind) (v w : Lattice) (r : ℕ) : AffineAutomorphism :=
  integerTranslation w * affineGenerator j v ^ r

private theorem
    Elliptic.affineNormalForm_apply (j : Kind) (v w : Lattice) (r : ℕ) (x : RealCoordinates) :
    affineNormalForm j v w r x = realCast w + (flatAffine j v)^[r] x := by
  rw [affineNormalForm, affineAutomorphism_mul_apply, integerTranslation_apply,
    affineGenerator_pow_apply]

private theorem Elliptic.affineNormalForm_mul (j : Kind) (v w z : Lattice) (r s : ℕ) :
    affineNormalForm j v w r * affineNormalForm j v z s =
      affineNormalForm j v (w + j.matrix ^ r *ᵥ z) (r + s) := by
  unfold affineNormalForm
  calc
    (integerTranslation w * affineGenerator j v ^ r) *
          (integerTranslation z * affineGenerator j v ^ s) =
        integerTranslation w * (affineGenerator j v ^ r * integerTranslation z) *
          affineGenerator j v ^ s := by simp only [mul_assoc]
    _ =
        (integerTranslation w * integerTranslation (j.matrix ^ r *ᵥ z)) *
          (affineGenerator j v ^ r * affineGenerator j v ^ s) := by
      rw [affineGenerator_pow_translation]
      simp only [mul_assoc]
    _ = integerTranslation (w + j.matrix ^ r *ᵥ z) * affineGenerator j v ^ (r + s) := by
      rw [← integerTranslation_add, ← pow_add]

private theorem
    Elliptic.affineNormalForm_reduce_order (j : Kind) (v w : Lattice) (hv : j.matrix *ᵥ v = v)
    (n : ℕ) (hn : j.order ≤ n) :
    affineNormalForm j v w n = affineNormalForm j v (w + v) (n - j.order) := by
  unfold affineNormalForm
  rw [integerTranslation_add, ← affineGenerator_pow_order j v hv, mul_assoc, ← pow_add,
    Nat.add_sub_of_le hn]

private def Elliptic.affineNormalFormsSubgroup (j : Kind) (v : Lattice) (hv : j.matrix *ᵥ v = v) :
    Subgroup AffineAutomorphism
    where
  carrier := {g | ∃ w : Lattice, ∃ r : Fin j.order, g = affineNormalForm j v w r.val}
  one_mem' := ⟨0, ⟨0, j.order_pos⟩, by simp [affineNormalForm]⟩
  mul_mem' := by
    rintro f g ⟨w, r, rfl⟩ ⟨z, s, rfl⟩
    by_cases h : r.val + s.val < j.order
    · exact
        ⟨w + j.matrix ^ r.val *ᵥ z, ⟨r.val + s.val, h⟩, affineNormalForm_mul j v w z r.val s.val⟩
    · have hge : j.order ≤ r.val + s.val := Nat.le_of_not_gt h
      have hlt : r.val + s.val - j.order < j.order := by omega
      exact
        ⟨w + j.matrix ^ r.val *ᵥ z + v, ⟨r.val + s.val - j.order, hlt⟩,
          (affineNormalForm_mul j v w z r.val s.val).trans
            (affineNormalForm_reduce_order j v _ hv _ hge)⟩
  inv_mem' := by
    rintro f ⟨w, r, rfl⟩
    by_cases hr : r.val = 0
    · refine ⟨-w, ⟨0, j.order_pos⟩, ?_⟩
      simp [affineNormalForm, hr]
    · have hk : j.order - r.val < j.order := by omega
      let k := j.order - r.val
      have hrk : r.val + k = j.order := Nat.add_sub_of_le r.isLt.le
      refine ⟨j.matrix ^ k *ᵥ (-v - w), ⟨k, hk⟩, ?_⟩
      apply inv_eq_of_mul_eq_one_right
      rw [affineNormalForm_mul, Matrix.mulVec_mulVec, ← pow_add, hrk, j.matrix_pow_order,
        Matrix.one_mulVec]
      have hw : w + (-v - w) = -v := by abel
      rw [hw, affineNormalForm, affineGenerator_pow_order j v hv, integerTranslation_neg,
        inv_mul_cancel]

private def Elliptic.affineDeckSubgroup (j : Kind) (v : Lattice) : Subgroup AffineAutomorphism :=
  Subgroup.closure (Set.range integerTranslation ∪ {affineGenerator j v})

private theorem Elliptic.integerTranslation_mem_affineDeckSubgroup (j : Kind) (v w : Lattice) :
    integerTranslation w ∈ affineDeckSubgroup j v :=
  Subgroup.subset_closure (Or.inl (Set.mem_range_self w))

private theorem Elliptic.affineGenerator_mem_affineDeckSubgroup (j : Kind) (v : Lattice) :
    affineGenerator j v ∈ affineDeckSubgroup j v :=
  Subgroup.subset_closure (Or.inr rfl)

private theorem
    Elliptic.affineNormalForm_mem_affineDeckSubgroup (j : Kind) (v w : Lattice) (r : ℕ) :
    affineNormalForm j v w r ∈ affineDeckSubgroup j v :=
  (affineDeckSubgroup j v).mul_mem (integerTranslation_mem_affineDeckSubgroup j v w)
    ((affineDeckSubgroup j v).pow_mem (affineGenerator_mem_affineDeckSubgroup j v) r)

private theorem Elliptic.affineDeckSubgroup_eq_normalForms (j : Kind) (v : Lattice)
    (hv : j.matrix *ᵥ v = v) : affineDeckSubgroup j v = affineNormalFormsSubgroup j v hv := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    intro g hg
    rcases hg with ⟨w, rfl⟩ | rfl
    · exact ⟨w, ⟨0, j.order_pos⟩, by simp [affineNormalForm]⟩
    · have hm : 1 < j.order := by cases j <;> decide
      exact ⟨0, ⟨1, hm⟩, by simp [affineNormalForm]⟩
  · rintro g ⟨w, r, rfl⟩
    exact affineNormalForm_mem_affineDeckSubgroup j v w r.val

private theorem
    Elliptic.mem_affineDeckSubgroup_iff (j : Kind) (v : Lattice) (hv : j.matrix *ᵥ v = v)
    (g : AffineAutomorphism) :
    g ∈ affineDeckSubgroup j v ↔
      ∃ w : Lattice, ∃ r : Fin j.order, g = affineNormalForm j v w r.val := by
  rw [affineDeckSubgroup_eq_normalForms j v hv]
  rfl

private abbrev Elliptic.AffineDeckGroup (j : Kind) (v : Lattice) :=
  affineDeckSubgroup j v

private def Elliptic.deckTranslationHom (j : Kind) (v : Lattice) :
    Multiplicative Lattice →* AffineDeckGroup j v :=
  integerTranslationHom.codRestrict (affineDeckSubgroup j v)
    (fun w => integerTranslation_mem_affineDeckSubgroup j v w.toAdd)

private def Elliptic.deckGenerator (j : Kind) (v : Lattice) : AffineDeckGroup j v :=
  ⟨affineGenerator j v, affineGenerator_mem_affineDeckSubgroup j v⟩

private def Elliptic.deckNormalForm (j : Kind) (v : Lattice) (a : Lattice × Fin j.order) :
    AffineDeckGroup j v :=
  deckTranslationHom j v (Multiplicative.ofAdd a.1) * deckGenerator j v ^ a.2.val

private theorem
    Elliptic.deckNormalForm_surjective (j : Kind) (v : Lattice) (hv : j.matrix *ᵥ v = v) :
    Function.Surjective (deckNormalForm j v) := by
  intro g
  obtain ⟨w, r, hr⟩ := (mem_affineDeckSubgroup_iff j v hv g).mp g.property
  exact ⟨(w, r), Subtype.ext hr.symm⟩

private theorem Elliptic.deckGenerator_pow_order (j : Kind) (v : Lattice) (hv : j.matrix *ᵥ v = v) :
    deckGenerator j v ^ j.order = deckTranslationHom j v (Multiplicative.ofAdd v) :=
  Subtype.ext (affineGenerator_pow_order j v hv)

private instance Elliptic.affineDeckGroupMulAction (j : Kind) (v : Lattice) :
    MulAction (AffineDeckGroup j v) RealCoordinates
    where
  smul g x := (g : AffineAutomorphism) x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

private instance Elliptic.affineDeckGroupContinuousConstSMul (j : Kind) (v : Lattice) :
    ContinuousConstSMul (AffineDeckGroup j v) RealCoordinates where
  continuous_const_smul g := affineAutomorphism_continuous g.val

private theorem Elliptic.affineDeckGroup_eval_injective (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (x : RealCoordinates) :
    Function.Injective (fun g : AffineDeckGroup j v => g • x) := by
  intro g h hgh
  obtain ⟨a, rfl⟩ := deckNormalForm_surjective j v hv.1 g
  obtain ⟨b, rfl⟩ := deckNormalForm_surjective j v hv.1 h
  have he : affineNormalForm j v a.1 a.2.val x = affineNormalForm j v b.1 b.2.val x := hgh
  rw [affineNormalForm_apply, affineNormalForm_apply] at he
  have hu := affineTranslate_unique j (exampleFixedPeriod j) v hv x a.2 b.2 a.1 b.1 he
  exact congrArg (deckNormalForm j v) (Prod.ext hu.2 hu.1)

private theorem Elliptic.affineDeckGroup_free (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) :
    IsCancelSMul (AffineDeckGroup j v) RealCoordinates where
  right_cancel' _ _ x hgh := affineDeckGroup_eval_injective j v hv x hgh

private theorem
    Elliptic.affineCoverProjection_orbit_iff (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) (x y : RealCoordinates) :
    affineCoverProjection j p v hv x = affineCoverProjection j p v hv y ↔
      x ∈ MulAction.orbit (AffineDeckGroup j v) y := by
  rw [affineCoverProjection_eq_iff_translate]
  constructor
  · rintro ⟨r, hr, w, hx⟩
    refine ⟨deckNormalForm j v (w, ⟨r, hr⟩), ?_⟩
    change affineNormalForm j v w r y = x
    rw [affineNormalForm_apply]
    exact hx.symm
  · rintro ⟨g, hg⟩
    obtain ⟨a, rfl⟩ := deckNormalForm_surjective j v hv.1 g
    refine ⟨a.2.val, a.2.isLt, a.1, ?_⟩
    have he : affineNormalForm j v a.1 a.2.val y = x := hg
    exact he.symm.trans (affineNormalForm_apply j v a.1 a.2.val y)

private theorem Elliptic.affineCoverProjection_isQuotientCoveringMap (j : Kind) (p : FixedPeriod j)
    (v : Lattice) (hv : AdmissibleTwist j v) :
    IsQuotientCoveringMap (affineCoverProjection j p v hv) (AffineDeckGroup j v) := by
  let := affineDeckGroup_free j v hv
  exact
    quotientCoveringMap_of_localHomeomorph
      (affineCoverProjection_isCoveringMap j p v hv).isLocalHomeomorph
      (affineCoverProjection_surjective j p v hv) (affineCoverProjection_orbit_iff j p v hv)

private def
    Elliptic.surfaceFundamentalGroupDeckOppositeEquiv (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) (y : RealCoordinates) :
    FundamentalGroup (Surface j p v hv) (affineCoverProjection j p v hv y) ≃*
      (AffineDeckGroup j v)ᵐᵒᵖ :=
  (affineCoverProjection_isQuotientCoveringMap j p v hv).fundamentalGroupEquiv ⟨y, rfl⟩

private def Elliptic.surfaceFundamentalGroupDeckEquiv (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) (y : RealCoordinates) :
    FundamentalGroup (Surface j p v hv) (affineCoverProjection j p v hv y) ≃*
      AffineDeckGroup j v :=
  (surfaceFundamentalGroupDeckOppositeEquiv j p v hv y).trans
    (MulEquiv.inv' (AffineDeckGroup j v)).symm

private theorem Elliptic.surfaceFundamentalGroupDeckEquiv_monodromy (j : Kind) (p : FixedPeriod j)
    (v : Lattice) (hv : AdmissibleTwist j v) (y : RealCoordinates)
    (γ : FundamentalGroup (Surface j p v hv) (affineCoverProjection j p v hv y)) :
    (surfaceFundamentalGroupDeckEquiv j p v hv y γ)⁻¹ • y =
      ((affineCoverProjection_isQuotientCoveringMap j p v hv).isCoveringMap.monodromy γ ⟨y, rfl⟩ :
        RealCoordinates) := by
  let hq := affineCoverProjection_isQuotientCoveringMap j p v hv
  change ((hq.fundamentalGroupToMulOpposite ⟨y, rfl⟩ γ).unop⁻¹)⁻¹ • y = _
  rw [inv_inv]
  exact hq.unop_fundamentalGroupToMulOpposite_smul

private def Elliptic.HigherHomology.periodCover (j : Elliptic.Kind) (p : Elliptic.FixedPeriod j)
    (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) :
    C(p.val.Torus, Elliptic.Surface j p v hv) :=
  ⟨Elliptic.surfaceProjection j p v hv, Elliptic.surfaceProjection_continuous j p v hv⟩

private def Elliptic.HigherHomology.surfaceMappingTorusHomologyEquiv (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) (n : ℕ) :
    SingularMayerVietoris.SingularHomology
        (Elliptic.Surface j p j.twist (Elliptic.mainTwist_admissible j)) n ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (mappingTorusModel j) n :=
  PeriodTorusHigherHomology.homeomorphHomologyEquiv (surfaceMappingTorusHomeomorph j p) n

private def
    Elliptic.HigherHomology.surfaceH2Equiv (j : Elliptic.Kind) (p : Elliptic.FixedPeriod j) :
    SingularMayerVietoris.SingularHomology
        (Elliptic.Surface j p j.twist (Elliptic.mainTwist_admissible j)) 2 ≃ₗ[ℤ]
      (Fin 2 → ℤ) :=
  (surfaceMappingTorusHomologyEquiv j p 2).trans (mappingTorusH2Equiv j)

private def
    Elliptic.HigherHomology.surfaceH3Equiv (j : Elliptic.Kind) (p : Elliptic.FixedPeriod j) :
    SingularMayerVietoris.SingularHomology
        (Elliptic.Surface j p j.twist (Elliptic.mainTwist_admissible j)) 3 ≃ₗ[ℤ]
      (Fin 2 → ℤ) :=
  (surfaceMappingTorusHomologyEquiv j p 3).trans (mappingTorusH3Equiv j)

private def
    Elliptic.HigherHomology.surfaceH4Equiv (j : Elliptic.Kind) (p : Elliptic.FixedPeriod j) :
    SingularMayerVietoris.SingularHomology
        (Elliptic.Surface j p j.twist (Elliptic.mainTwist_admissible j)) 4 ≃ₗ[ℤ]
      ℤ :=
  (surfaceMappingTorusHomologyEquiv j p 4).trans (mappingTorusH4Equiv j)

private def Elliptic.HigherHomology.ellipticBettiNumber : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | 2 => 2
  | 3 => 2
  | 4 => 1
  | _ + 5 => 0

private theorem Elliptic.HigherHomology.ellipticBettiNumber_eq_zero_of_lt {n : ℕ} (hn : 4 < n) :
    ellipticBettiNumber n = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
  rfl

private def Elliptic.HigherHomology.mappingTorusHomologyCoordinates (j : Elliptic.Kind) :
    (n : ℕ) →
      SingularMayerVietoris.SingularHomology (mappingTorusModel j) n ≃ₗ[ℤ]
        (Fin (ellipticBettiNumber n) → ℤ)
  | 0 => (mappingTorusH0Equiv j).trans (LinearEquiv.funUnique (Fin 1) ℤ ℤ).symm
  | 1 => mappingTorusH1Equiv j
  | 2 => mappingTorusH2Equiv j
  | 3 => mappingTorusH3Equiv j
  | 4 => (mappingTorusH4Equiv j).trans (LinearEquiv.funUnique (Fin 1) ℤ ℤ).symm
  | n + 5 =>
    by
    have :=
      threeTorusMappingTorus_homology_subsingleton (fibreTorusHomeomorph j).symm
        (show 4 < n + 5 by omega)
    exact LinearEquiv.ofSubsingleton _ (Fin 0 → ℤ)

private def Elliptic.HigherHomology.surfaceHomologyCoordinates (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) (n : ℕ) :
    SingularMayerVietoris.SingularHomology
        (Elliptic.Surface j p j.twist (Elliptic.mainTwist_admissible j)) n ≃ₗ[ℤ]
      (Fin (ellipticBettiNumber n) → ℤ) :=
  (surfaceMappingTorusHomologyEquiv j p n).trans (mappingTorusHomologyCoordinates j n)

private abbrev Elliptic.CanonicalBundle.Model :=
  ComplexPlane₂


private theorem
    Elliptic.fillingRadial_projection_coe (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v)
    (u : unitInterval) (x : Filling j v hv) :
    (fillingProjection j v hv (fillingRadial j v hv u x) : ℂ) =
      (((1 - (u : ℝ) : ℝ) : ℂ) ^ j.order) * (fillingProjection j v hv x : ℂ) := by
  obtain ⟨y, rfl⟩ := fillingQuotient_surjective j v hv x
  rw [fillingRadial_fillingQuotient]
  change
    ((1 - (u : ℝ)) • (y.1 : ℂ)) ^ j.order =
      (((1 - (u : ℝ) : ℝ) : ℂ) ^ j.order) * (y.1 : ℂ) ^ j.order
  rw [Complex.real_smul, mul_pow]

private theorem
    Elliptic.fillingRadial_projection_norm (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v)
    (u : unitInterval) (x : Filling j v hv) :
    ‖(fillingProjection j v hv (fillingRadial j v hv u x) : ℂ)‖ =
      (1 - (u : ℝ)) ^ j.order * ‖(fillingProjection j v hv x : ℂ)‖ := by
  rw [fillingRadial_projection_coe, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr u.property.2)]

private theorem Elliptic.fillingRadial_projection_norm_le (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (u : unitInterval) (x : Filling j v hv) :
    ‖(fillingProjection j v hv (fillingRadial j v hv u x) : ℂ)‖ ≤
      ‖(fillingProjection j v hv x : ℂ)‖ := by
  rw [fillingRadial_projection_norm]
  exact
    mul_le_of_le_one_left (norm_nonneg _)
      (pow_le_one₀ (sub_nonneg.mpr u.property.2) (by linarith [u.property.1]))

end Mathoverflow1973

end
