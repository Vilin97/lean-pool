/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/

import LeanPool.BollobasNikiforov.Basic.Spectrum
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Topology.Instances.Matrix

/-!
# Nonnegative Perron vector for a symmetric nonnegative matrix

A real symmetric entrywise-nonnegative matrix has a nonnegative unit maximizer of the
Rayleigh quotient, and that maximizer is an eigenvector for `lambdaMax`.
-/

namespace BollobasNikiforov

open Matrix Module.End Metric WithLp
open scoped InnerProductSpace


variable {n : Type*} [Fintype n] [DecidableEq n]
variable {B : Matrix n n ℝ}

/-- The Euclidean unit sphere in coordinates `{x | ∑ i, x i ^ 2 = 1}`. -/
def l2Sphere : Set (n → ℝ) := {x | ∑ i, x i ^ 2 = 1}

omit [DecidableEq n] in
lemma mem_l2Sphere {x : n → ℝ} : x ∈ l2Sphere ↔ ∑ i, x i ^ 2 = 1 := Iff.rfl

omit [DecidableEq n] in
lemma isCompact_l2Sphere : IsCompact (l2Sphere : Set (n → ℝ)) := by
  have hc := (isCompact_sphere (0 : EuclideanSpace ℝ n) 1).image
    (EuclideanSpace.equiv n ℝ).continuous
  convert hc
  ext x
  constructor
  · intro hx
    refine ⟨toLp 2 x, ?_, rfl⟩
    rw [EuclideanSpace.sphere_zero_eq 1 (by exact zero_le_one), Set.mem_ofPred]
    simpa [l2Sphere] using hx
  · rintro ⟨y, hy, rfl⟩
    rw [EuclideanSpace.sphere_zero_eq 1 (by exact zero_le_one), Set.mem_ofPred] at hy
    simpa [l2Sphere] using hy

omit [DecidableEq n] in
lemma l2Sphere_nonempty [Nonempty n] : (l2Sphere : Set (n → ℝ)).Nonempty := by
  classical
  let i0 : n := Classical.arbitrary n
  refine ⟨Pi.single i0 (1 : ℝ), ?_⟩
  rw [mem_l2Sphere, Fintype.sum_eq_single i0]
  · simp
  · intro j hj
    simp [hj]

omit [DecidableEq n] in
lemma continuous_dotProduct_mulVec :
    Continuous fun x : n → ℝ => x ⬝ᵥ B *ᵥ x :=
  continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)

private lemma reApplyInnerSelf_eq_dotProduct_mulVec (hB : B.IsHermitian)
    (x : EuclideanSpace ℝ n) :
    (isSymmetric_toEuclideanLin_iff.mpr hB).toSelfAdjoint.1.reApplyInnerSelf x =
      ofLp x ⬝ᵥ B *ᵥ ofLp x := by
  rw [ContinuousLinearMap.reApplyInnerSelf_apply]
  have : (isSymmetric_toEuclideanLin_iff.mpr hB).toSelfAdjoint.1 x = B.toEuclideanLin x := rfl
  rw [this, EuclideanSpace.inner_eq_star_dotProduct]
  simp [ofLp_toLpLin, toLin'_apply]

omit [DecidableEq n] in
/-- **SP01.** Replacing a vector by its absolute value cannot decrease the Rayleigh
form of an entrywise nonnegative matrix. -/
lemma dotProduct_mulVec_le_abs (hnn : ∀ i j, 0 ≤ B i j) (x : n → ℝ) :
    x ⬝ᵥ B *ᵥ x ≤ |x| ⬝ᵥ B *ᵥ |x| := by
  simp_rw [dot_mulVec_eq_sum_sum]
  refine Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun i _ => ?_
  have hx : x i * x j ≤ |x i| * |x j| :=
    (le_abs_self (x i * x j)).trans_eq (abs_mul (x i) (x j))
  calc
    x i * B i j * x j = B i j * (x i * x j) := by ring
    _ ≤ B i j * (|x i| * |x j|) := mul_le_mul_of_nonneg_left hx (hnn i j)
    _ = |x| i * B i j * |x| j := by simp [Pi.abs_apply]; ring

omit [DecidableEq n] in
/-- **SP02** (existence). The Rayleigh form of a symmetric matrix attains a maximum on
the Euclidean unit sphere. -/
lemma exists_isMaxOn_dotProduct_mulVec (_hB : B.IsHermitian) [Nonempty n] :
    ∃ u, u ∈ l2Sphere ∧ IsMaxOn (fun x : n → ℝ => x ⬝ᵥ B *ᵥ x) l2Sphere u :=
  isCompact_l2Sphere.exists_isMaxOn l2Sphere_nonempty
    continuous_dotProduct_mulVec.continuousOn

omit [DecidableEq n] in
/-- **SP02.** If `B` is also entrywise nonnegative, some maximizer is nonnegative. -/
lemma exists_nonneg_isMaxOn_dotProduct_mulVec (hB : B.IsHermitian)
    (hnn : ∀ i j, 0 ≤ B i j) [Nonempty n] :
    ∃ u, u ∈ l2Sphere ∧ (∀ i, 0 ≤ u i) ∧
      IsMaxOn (fun x : n → ℝ => x ⬝ᵥ B *ᵥ x) l2Sphere u := by
  obtain ⟨u, hu, hmax⟩ := exists_isMaxOn_dotProduct_mulVec hB
  refine ⟨|u|, ?_, fun i => abs_nonneg _, ?_⟩
  · simpa [l2Sphere, sq_abs] using hu
  · intro y hy
    exact (hmax hy).trans (dotProduct_mulVec_le_abs hnn u)

/-- **SP03.** A symmetric entrywise-nonnegative matrix has a nonnegative unit eigenvector
for `lambdaMax`. -/
lemma exists_nonneg_eigenvector_lambdaMax (hB : B.IsHermitian)
    (hnn : ∀ i j, 0 ≤ B i j) [Nonempty n] :
    ∃ u : n → ℝ, (∀ i, 0 ≤ u i) ∧ ∑ i, u i ^ 2 = 1 ∧ B *ᵥ u = lambdaMax hB • u := by
  obtain ⟨u, hu, hu0, hmax⟩ := exists_nonneg_isMaxOn_dotProduct_mulVec hB hnn
  let hT := isSymmetric_toEuclideanLin_iff (A := B).mpr hB
  let T := hT.toSelfAdjoint
  let uE : EuclideanSpace ℝ n := toLp 2 u
  have hTfun : ∀ x, (T.1 : EuclideanSpace ℝ n → EuclideanSpace ℝ n) x = B.toEuclideanLin x :=
    fun _ => rfl
  have hRayEq : ∀ x, T.1.reApplyInnerSelf x = ofLp x ⬝ᵥ B *ᵥ ofLp x :=
    reApplyInnerSelf_eq_dotProduct_mulVec hB
  have huE_mem : uE ∈ sphere (0 : EuclideanSpace ℝ n) 1 := by
    rw [EuclideanSpace.sphere_zero_eq 1 (by exact zero_le_one), Set.mem_ofPred]
    simpa [uE, l2Sphere] using hu
  have huE_norm : ‖uE‖ = 1 := mem_sphere_zero_iff_norm.mp huE_mem
  have huE_ne : uE ≠ 0 := by
    intro h
    simp [h] at huE_norm
  have hmaxE : IsMaxOn T.1.reApplyInnerSelf (sphere (0 : EuclideanSpace ℝ n) ‖uE‖) uE := by
    rw [huE_norm]
    refine isMaxOn_iff.mpr fun y hy => ?_
    have hy' : ofLp y ∈ l2Sphere := by
      rw [EuclideanSpace.sphere_zero_eq 1 (by exact zero_le_one), Set.mem_ofPred] at hy
      simpa [l2Sphere] using hy
    have : ofLp y ⬝ᵥ B *ᵥ ofLp y ≤ u ⬝ᵥ B *ᵥ u := hmax hy'
    rwa [hRayEq, hRayEq, show ofLp uE = u from rfl]
  have hvec := T.prop.hasEigenvector_of_isMaxOn huE_ne hmaxE
  set μ : ℝ := ⨆ x : { x : EuclideanSpace ℝ n // x ≠ 0 }, T.1.rayleighQuotient x
  have hμ_ev : HasEigenvalue (B.toEuclideanLin : EuclideanSpace ℝ n →ₗ[ℝ] EuclideanSpace ℝ n) μ :=
    hasEigenvalue_of_hasEigenvector hvec
  have hμ_le : μ ≤ lambdaMax hB := by
    obtain ⟨i, hi⟩ := hT.exists_eigenvalues_eq finrank_euclideanSpace hμ_ev
    have hi' : hB.eigenvalues₀ i = μ := hi
    calc
      μ = hB.eigenvalues₀ i := hi'.symm
      _ ≤ hB.eigenvalues₀ ⟨0, Fintype.card_pos⟩ := hB.eigenvalues₀_antitone (Fin.zero_le _)
      _ = lambdaMax hB := rfl
  have hlam_le : lambdaMax hB ≤ μ := by
    have hlam : HasEigenvalue
        (B.toEuclideanLin : EuclideanSpace ℝ n →ₗ[ℝ] EuclideanSpace ℝ n)
        (lambdaMax hB) :=
      hT.hasEigenvalue_eigenvalues finrank_euclideanSpace ⟨0, Fintype.card_pos⟩
    obtain ⟨v, hv⟩ := hlam.exists_hasEigenvector
    have hv0 : v ≠ 0 := hv.2
    have hRay : T.1.rayleighQuotient v = lambdaMax hB := by
      unfold ContinuousLinearMap.rayleighQuotient ContinuousLinearMap.reApplyInnerSelf
      rw [real_inner_comm, hTfun,
        inner_product_apply_eigenvector (T := B.toEuclideanLin) hv.apply_eq_smul]
      simp [mul_div_cancel_right₀ _ (pow_ne_zero (n := 2) (norm_ne_zero_iff.mpr hv0))]
    have hbdd : BddAbove (Set.range fun x : { x : EuclideanSpace ℝ n // x ≠ 0 } =>
        T.1.rayleighQuotient x) := by
      refine ⟨‖T.1‖, ?_⟩
      rintro _ ⟨x, rfl⟩
      exact (le_abs_self _).trans (T.1.rayleighQuotient_le_norm _)
    exact hRay.symm.trans_le (le_ciSup hbdd ⟨v, hv0⟩)
  have hμ : μ = lambdaMax hB := le_antisymm hμ_le hlam_le
  refine ⟨u, hu0, mem_l2Sphere.mp hu, ?_⟩
  have happly : (T.1 : EuclideanSpace ℝ n → EuclideanSpace ℝ n) uE = μ • uE :=
    hvec.apply_eq_smul
  have hlin : B.toEuclideanLin uE = lambdaMax hB • uE := by
    rw [← hTfun, happly, hμ]
  simpa [uE, ofLp_toLpLin, toLin'_apply] using congrArg ofLp hlin

end BollobasNikiforov
