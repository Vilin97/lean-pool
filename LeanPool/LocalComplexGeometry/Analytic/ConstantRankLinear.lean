/-
Copyright (c) 2026 BochaoKong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BochaoKong
-/

import LeanPool.LocalComplexGeometry.Analytic.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Topology.Algebra.Module.Complement
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Linear algebra for the constant-rank theorem

The lemmas here isolate the finite-dimensional arguments used in the analytic
constant-rank proof: invariance of range dimension under injective/surjective
composition, a vertical-kernel criterion, and canonical product coordinates on
`Fin (r + k) → ℂ`.
-/


namespace LocalComplexGeometry

noncomputable section

/-- Range dimension for a continuous complex-linear map between arbitrary
complex normed spaces. -/
def complexLinearRank
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (A : E →L[ℂ] F) : ℕ :=
  Module.finrank ℂ (LinearMap.range A.toLinearMap)

@[simp]
theorem complexLinearRank_eq_complexRank {n m : ℕ}
    (A : ComplexEuclidean n →L[ℂ] ComplexEuclidean m) :
    complexLinearRank A = complexRank A :=
  rfl

/-- Surjective precomposition does not change range dimension. -/
theorem complexLinearRank_comp_of_surjective_right
    {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (A : F →L[ℂ] G) (B : E →L[ℂ] F)
    (hB : Function.Surjective B) :
    complexLinearRank (A.comp B) = complexLinearRank A := by
  unfold complexLinearRank
  rw [ContinuousLinearMap.toLinearMap_comp]
  rw [LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.mpr hB)]

/-- Injective postcomposition does not change range dimension. -/
theorem complexLinearRank_comp_of_injective_left
    {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (B : F →L[ℂ] G) (A : E →L[ℂ] F)
    (hB : Function.Injective B) :
    complexLinearRank (B.comp A) = complexLinearRank A := by
  have hker : LinearMap.ker (B.comp A).toLinearMap =
      LinearMap.ker A.toLinearMap := by
    ext x
    change B (A x) = 0 ↔ A x = 0
    exact ⟨fun h ↦ hB (by simpa using h), fun h ↦ by rw [h, map_zero]⟩
  have h₁ := LinearMap.finrank_range_add_finrank_ker (B.comp A).toLinearMap
  have h₂ := LinearMap.finrank_range_add_finrank_ker A.toLinearMap
  unfold complexLinearRank
  rw [hker] at h₁
  omega

/-- If the first component of `B : U × V → U × W` is the first
projection and `B` has the minimal possible rank `dim U`, then every vertical
vector is killed by `B`. -/
theorem apply_zero_prod_eq_zero_of_rank_eq
    {U V W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℂ U] [FiniteDimensional ℂ U]
    [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    [NormedAddCommGroup W] [NormedSpace ℂ W]
    (B : U × V →L[ℂ] U × W)
    (hfst : (ContinuousLinearMap.fst ℂ U W).comp B =
      ContinuousLinearMap.fst ℂ U V)
    (hrank : complexLinearRank B = Module.finrank ℂ U)
    (v : V) :
    B (0, v) = 0 := by
  let T : LinearMap.range B.toLinearMap →ₗ[ℂ] U :=
    (ContinuousLinearMap.fst ℂ U W).toLinearMap.domRestrict
      (LinearMap.range B.toLinearMap)
  have hTsurj : Function.Surjective T := by
    intro u
    let z : LinearMap.range B.toLinearMap :=
      ⟨B (u, 0), ⟨(u, 0), rfl⟩⟩
    refine ⟨z, ?_⟩
    change (B (u, 0)).1 = u
    simpa using DFunLike.congr_fun hfst (u, 0)
  have hdim : Module.finrank ℂ (LinearMap.range B.toLinearMap) =
      Module.finrank ℂ U :=
    hrank
  have hTinj : Function.Injective T :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2 hTsurj
  let z : LinearMap.range B.toLinearMap :=
    ⟨B (0, v), ⟨(0, v), rfl⟩⟩
  have hTz : T z = 0 := by
    change (B (0, v)).1 = 0
    simpa using DFunLike.congr_fun hfst (0, v)
  have hz : z = 0 := hTinj (by simpa using hTz)
  exact congrArg Subtype.val hz

/-- Canonically concatenate an `r`-tuple and a `k`-tuple. -/
def finProdContinuousLinearEquiv (r k : ℕ) :
    (ComplexEuclidean r × ComplexEuclidean k) ≃L[ℂ]
      ComplexEuclidean (r + k) where
  toFun x := Fin.append x.1 x.2
  invFun x :=
    (fun i ↦ x (Fin.castAdd k i), fun j ↦ x (Fin.natAdd r j))
  left_inv x := by ext <;> simp
  right_inv _ := Fin.append_castAdd_natAdd
  map_add' x y := by
    ext i
    cases i using Fin.addCases <;> simp
  map_smul' c x := by
    ext i
    cases i using Fin.addCases <;> simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp]
theorem finProdContinuousLinearEquiv_apply_castAdd (r k : ℕ)
    (x : ComplexEuclidean r × ComplexEuclidean k) (i : Fin r) :
    finProdContinuousLinearEquiv r k x (Fin.castAdd k i) = x.1 i := by
  simp [finProdContinuousLinearEquiv]

@[simp]
theorem finProdContinuousLinearEquiv_apply_natAdd (r k : ℕ)
    (x : ComplexEuclidean r × ComplexEuclidean k) (i : Fin k) :
    finProdContinuousLinearEquiv r k x (Fin.natAdd r i) = x.2 i := by
  simp [finProdContinuousLinearEquiv]

@[simp]
theorem finProdContinuousLinearEquiv_symm_fst_apply (r k : ℕ)
    (x : ComplexEuclidean (r + k)) (i : Fin r) :
    ((finProdContinuousLinearEquiv r k).symm x).1 i =
      x (Fin.castAdd k i) := by
  change ((finProdContinuousLinearEquiv r k).invFun x).1 i = _
  rfl

@[simp]
theorem finProdContinuousLinearEquiv_symm_snd_apply (r k : ℕ)
    (x : ComplexEuclidean (r + k)) (i : Fin k) :
    ((finProdContinuousLinearEquiv r k).symm x).2 i =
      x (Fin.natAdd r i) := by
  change ((finProdContinuousLinearEquiv r k).invFun x).2 i = _
  rfl

/-- Concatenating the first block of a vector with a zero block is precisely
the standard rank map. -/
theorem finProd_fst_zero_eq_standardRankMap (r n' m' : ℕ)
    (x : ComplexEuclidean (r + n')) :
    finProdContinuousLinearEquiv r m'
        (((finProdContinuousLinearEquiv r n').symm x).1, 0) =
      standardRankMap (r + n') (r + m') r x := by
  funext j
  generalize hs : finSumFinEquiv.symm j = s
  cases s with
  | inl i =>
      have hj : j = Fin.castAdd m' i := by
        apply finSumFinEquiv.symm.injective
        simpa using hs
      subst j
      have hir : i.1 < r := i.2
      have hin : i.1 < r + n' := lt_of_lt_of_le hir (Nat.le_add_right r n')
      simp only [finProdContinuousLinearEquiv_apply_castAdd,
        finProdContinuousLinearEquiv_symm_fst_apply,
        standardRankMap_apply]
      rw [dite_eq_left]
      · exact congrArg x (Fin.ext rfl)
      · exact ⟨hin, hir⟩
  | inr i =>
      have hj : j = Fin.natAdd r i := by
        apply finSumFinEquiv.symm.injective
        simpa using hs
      subst j
      simp [standardRankMap_apply]

/-- The preceding coordinate calculation after arbitrary linear coordinate
choices on the three factors.  The same equivalence is used on the rank
factor in source and target. -/
theorem productEquiv_fst_zero_eq_standardRankMap
    {U V W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℂ U]
    [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup W] [NormedSpace ℂ W]
    (r n' m' : ℕ)
    (eU : U ≃L[ℂ] ComplexEuclidean r)
    (eV : V ≃L[ℂ] ComplexEuclidean n')
    (eW : W ≃L[ℂ] ComplexEuclidean m')
    (x : ComplexEuclidean (r + n')) :
    ((eU.prodCongr eW).trans (finProdContinuousLinearEquiv r m'))
        (((((eU.prodCongr eV).trans
          (finProdContinuousLinearEquiv r n')).symm x).1), 0) =
      standardRankMap (r + n') (r + m') r x := by
  simpa [ContinuousLinearEquiv.trans_apply] using
    finProd_fst_zero_eq_standardRankMap r n' m' x

end

end LocalComplexGeometry
