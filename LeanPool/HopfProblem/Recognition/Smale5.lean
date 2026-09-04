/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology6
import all LeanPool.HopfProblem.Recognition.Smale1
import all LeanPool.HopfProblem.Recognition.Smale2
import all LeanPool.HopfProblem.Recognition.Smale3
import all LeanPool.HopfProblem.Recognition.Smale4
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology6

/-!
# Hopf problem: recognition · smale 5

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

private def Degree.SupportedGerms.Realizes {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : Set E) (f : E → E) : Prop :=
  ∃ (d : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞) (K : Set E),
    IsCompact K ∧
      K ⊆ U ∧
        Nonempty (Smale.SupportedDiffeomorph.SupportedRelativeIsotopy d K {0}) ∧
          (d : E → E) =ᶠ[𝓝 (0 : E)] f

private theorem
    Degree.SupportedGerms.Realizes.comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} {f g : E → E} (hf : Degree.SupportedGerms.Realizes U f)
    (hg : Degree.SupportedGerms.Realizes U g) : Degree.SupportedGerms.Realizes U (f ∘ g) := by
  obtain ⟨d, K, hK, hKU, ⟨A⟩, hd⟩ := hf
  obtain ⟨e, L, hL, hLU, ⟨B⟩, he⟩ := hg
  have he0 : e (0 : E) = 0 := B.endpoint_fixed_on 0 rfl
  have het : Filter.Tendsto e (𝓝 (0 : E)) (𝓝 0) := by
    simpa only [he0] using e.continuous.tendsto (0 : E)
  have C : Smale.SupportedDiffeomorph.SupportedRelativeIsotopy (e.trans d) (K ∪ L) {0} := by
    refine
      ⟨(fun p => A.family (p.1, B.family p)), A.smooth.comp (contMDiff_fst.prodMk B.smooth), ?_,
        ?_, ?_, ?_, ?_⟩
    · intro x
      rw [B.zero, A.zero]
    · intro x
      change A.family (1, B.family (1, x)) = d (e x)
      rw [B.one, A.one]
    · intro t
      obtain ⟨dₜ, hdₜ⟩ := A.slices t
      obtain ⟨eₜ, heₜ⟩ := B.slices t
      refine ⟨eₜ.trans dₜ, ?_⟩
      intro x
      change dₜ (eₜ x) = A.family (t, B.family (t, x))
      rw [heₜ, hdₜ]
    · intro t x hx
      rw [B.fixedOutside t x (fun h => hx (Or.inr h)),
        A.fixedOutside t x (fun h => hx (Or.inl h))]
    · intro t x hx
      rw [B.fixedOn t x hx, A.fixedOn t x hx]
  refine ⟨e.trans d, K ∪ L, hK.union hL, Set.union_subset hKU hLU, ⟨C⟩, ?_⟩
  filter_upwards [hd.comp_tendsto het, he] with x hx hy
  change d (e x) = f (g x)
  exact hx.trans (congrArg f hy)

private theorem
    Degree.SupportedGerms.Realizes.conj {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (c : E ≃L[ℝ] F) {U : Set E} {f : E → E}
    (hf : Degree.SupportedGerms.Realizes U f) :
    Degree.SupportedGerms.Realizes (c '' U) (fun y => c (f (c.symm y))) := by
  obtain ⟨d, K, hK, hKU, ⟨A⟩, hd⟩ := hf
  let D := (c.symm.toDiffeomorph.trans d).trans c.toDiffeomorph
  have B : Smale.SupportedDiffeomorph.SupportedRelativeIsotopy D (c '' K) {0} := by
    refine
      ⟨(fun p => c (A.family (p.1, c.symm p.2))),
        c.toDiffeomorph.contMDiff.comp
          (A.smooth.comp
            (contMDiff_fst.prodMk (c.symm.toDiffeomorph.contMDiff.comp contMDiff_snd))),
        ?_, ?_, ?_, ?_, ?_⟩
    · intro y
      rw [A.zero, c.apply_symm_apply]
    · intro y
      change c (A.family (1, c.symm y)) = c (d (c.symm y))
      rw [A.one]
    · intro t
      obtain ⟨e, he⟩ := A.slices t
      refine ⟨(c.symm.toDiffeomorph.trans e).trans c.toDiffeomorph, ?_⟩
      intro y
      change c (e (c.symm y)) = c (A.family (t, c.symm y))
      rw [he]
    · intro t y hy
      have hnot : c.symm y ∉ K := fun h => hy ⟨c.symm y, h, c.apply_symm_apply y⟩
      rw [A.fixedOutside t (c.symm y) hnot, c.apply_symm_apply]
    · intro t y hy
      have hy0 : y = 0 := Set.mem_singleton_iff.mp hy
      subst y
      rw [map_zero, A.fixedOn t 0 rfl, map_zero]
  refine ⟨D, c '' K, hK.image c.continuous, Set.image_mono hKU, ⟨B⟩, ?_⟩
  have ht : Filter.Tendsto c.symm (𝓝 (0 : F)) (𝓝 0) := by
    simpa only [map_zero] using c.symm.continuous.tendsto (0 : F)
  filter_upwards [hd.comp_tendsto ht] with y hy
  exact congrArg c hy

private theorem Degree.SupportedGerms.realizes_shear {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] (L : F →L[ℝ] E) {U : Set (E × F)} (hU : IsOpen U)
    (h0 : (0 : E × F) ∈ U) : Realizes U (fun p => (p.1 + L p.2, p.2)) := by
  obtain ⟨A, K, hK, hKU, hA, hA0, hdiff, hfix, -, hcore, hgerm⟩ :=
    Smale.SupportedDiffeomorph.exists_supported_shear_isotopy L hU h0
  obtain ⟨d, hd⟩ := hdiff 1
  have H : Smale.SupportedDiffeomorph.SupportedRelativeIsotopy d K {0} := by
    refine ⟨A, hA, hA0, fun x => (hd x).symm, hdiff, hfix, ?_⟩
    intro t x hx
    have hx0 : x = 0 := Set.mem_singleton_iff.mp hx
    subst x
    exact hcore t 0
  refine ⟨d, K, hK, hKU, ⟨H⟩, ?_⟩
  filter_upwards [hgerm] with x hx
  exact (hd x).trans hx

private theorem
    Degree.LinearFramePaths.diag2n_decompose {ι : Type*} [Fintype ι] [DecidableEq ι] {i j : ι}
    (hij : i ≠ j) (a : ℝ) (ha : a ≠ 0) :
    Matrix.SpecialLinearGroup.diag2n hij a ha =
      Matrix.SpecialLinearGroup.transvection hij a *
                Matrix.SpecialLinearGroup.transvection hij.symm (-a⁻¹) *
              Matrix.SpecialLinearGroup.transvection hij a *
            Matrix.SpecialLinearGroup.transvection hij (-1) *
          Matrix.SpecialLinearGroup.transvection hij.symm 1 *
        Matrix.SpecialLinearGroup.transvection hij (-1) := by
  apply Subtype.ext
  change
    Matrix.diagonal (fun k => if k = i then a else if k = j then a⁻¹ else 1) =
      (1 + Matrix.single i j a) * (1 + Matrix.single j i (-a⁻¹)) * (1 + Matrix.single i j a) *
            (1 + Matrix.single i j (-1)) *
          (1 + Matrix.single j i 1) *
        (1 + Matrix.single i j (-1))
  simp only [mul_add, add_mul, one_mul, mul_one, Matrix.single_mul_single_same,
    Matrix.single_mul_single_of_ne _ _ _ _ hij, Matrix.single_mul_single_of_ne _ _ _ _ hij.symm]
  ext k l
  by_cases hki : k = i <;> by_cases hkj : k = j <;> by_cases hli : l = i <;>
      by_cases hlj : l = j <;>
    simp_all [Matrix.diagonal_apply, Matrix.one_apply, Matrix.single_apply, eq_comm]

private theorem
    Degree.LinearFramePaths.joined_one_transvection {ι : Type*} [Fintype ι] [DecidableEq ι]
    {i j : ι} (hij : i ≠ j) (a : ℝ) :
    Joined (1 : Matrix.SpecialLinearGroup ι ℝ) (Matrix.SpecialLinearGroup.transvection hij a) := by
  refine
    ⟨{  toFun := fun t => Matrix.SpecialLinearGroup.transvection hij ((t : ℝ) * a)
        continuous_toFun := ?_
        source' := by simp
        target' := by simp }⟩
  apply Continuous.subtype_mk
  change Continuous (fun t : unitInterval => (1 : Matrix ι ι ℝ) + Matrix.single i j ((t : ℝ) * a))
  apply continuous_pi
  intro k
  apply continuous_pi
  intro l
  simp only [Matrix.add_apply, Matrix.single_apply]
  by_cases h : i = k ∧ j = l
  · simp only [h, and_self, ite_true]
    fun_prop
  · simp only [h, ite_false]
    fun_prop

private theorem
    Degree.LinearFramePaths.joined_one_specialLinear {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nontrivial ι] (A : Matrix.SpecialLinearGroup ι ℝ) :
    Joined (1 : Matrix.SpecialLinearGroup ι ℝ) A := by
  apply
    Matrix.SpecialLinearGroup.diagonal_transvection_induction'
      (fun A => Joined (1 : Matrix.SpecialLinearGroup ι ℝ) A) A
  · intro i j hij a ha
    rw [diag2n_decompose hij a ha]
    have hmul {A B : Matrix.SpecialLinearGroup ι ℝ} (hA : Joined 1 A) (hB : Joined 1 B) :
      Joined 1 (A * B) := by simpa only [one_mul] using hA.mul hB
    exact
      hmul
        (hmul
          (hmul
            (hmul (hmul (joined_one_transvection hij a) (joined_one_transvection hij.symm (-a⁻¹)))
              (joined_one_transvection hij a))
            (joined_one_transvection hij (-1)))
          (joined_one_transvection hij.symm 1))
        (joined_one_transvection hij (-1))
  · exact fun i j hij a => joined_one_transvection hij a
  · intro A B hA hB
    simpa only [one_mul] using hA.mul hB

private def Degree.SupportedGerms.coordinateSplit {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) :
    (ι → ℝ) ≃L[ℝ] ℝ × ({ j : ι // j ≠ i } → ℝ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun x => (x i, fun j => x j)
      invFun := fun p j => if h : j = i then p.1 else p.2 ⟨j, h⟩
      left_inv := by
        intro x
        funext j
        by_cases h : j = i <;> simp [h]
      right_inv := by
        rintro ⟨a, x⟩
        apply Prod.ext
        · simp
        · funext j
          simp [j.property]
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

private theorem Degree.SupportedGerms.realizes_transvection {ι : Type*} [Fintype ι] [DecidableEq ι]
    {U : Set (ι → ℝ)} (hU : IsOpen U) (h0 : (0 : ι → ℝ) ∈ U) {i j : ι} (hij : i ≠ j) (a : ℝ) :
    Realizes U
      (Matrix.SpecialLinearGroup.toLin' (Matrix.SpecialLinearGroup.transvection hij a)) := by
  let c := coordinateSplit i
  let L : ({ k : ι // k ≠ i } → ℝ) →L[ℝ] ℝ := a • ContinuousLinearMap.proj ⟨j, Ne.symm hij⟩
  have h :=
    (realizes_shear L (c.toHomeomorph.isOpenMap _ hU)
          (show (0 : ℝ × ({ k : ι // k ≠ i } → ℝ)) ∈ c '' U from ⟨0, h0, map_zero c⟩)).conj
      c.symm
  have hset : c.symm '' (c '' U) = U := by
    rw [← Set.image_comp]
    simp only [ContinuousLinearEquiv.symm_comp_self, Set.image_id]
  change Realizes (c.symm '' (c '' U)) (fun y => c.symm ((c y).1 + L (c y).2, (c y).2)) at h
  rw [hset] at h
  convert h using 1
  funext x k
  change
    ((Matrix.SpecialLinearGroup.transvection hij a : Matrix ι ι ℝ) *ᵥ x) k =
      (c.symm ((c x).1 + L (c x).2, (c x).2)) k
  rw [Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.single_mulVec_eq]
  by_cases hk : k = i
  · subst k
    simp [c, coordinateSplit, L]
  · simp [c, coordinateSplit, L, hk]

private theorem Degree.SupportedGerms.realizes_specialLinear {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nontrivial ι] {U : Set (ι → ℝ)} (hU : IsOpen U) (h0 : (0 : ι → ℝ) ∈ U)
    (A : Matrix.SpecialLinearGroup ι ℝ) : Realizes U (Matrix.SpecialLinearGroup.toLin' A) := by
  have hmul (A B : Matrix.SpecialLinearGroup ι ℝ)
    (hA : Realizes U (Matrix.SpecialLinearGroup.toLin' A))
    (hB : Realizes U (Matrix.SpecialLinearGroup.toLin' B)) :
    Realizes U (Matrix.SpecialLinearGroup.toLin' (A * B)) := by
    convert hA.comp hB using 1
    funext x
    rw [map_mul]
    rfl
  apply
    Matrix.SpecialLinearGroup.diagonal_transvection_induction'
      (fun A => Realizes U (Matrix.SpecialLinearGroup.toLin' A)) A
  · intro i j hij a ha
    rw [Degree.LinearFramePaths.diag2n_decompose hij a ha]
    exact
      hmul _ _
        (hmul _ _
          (hmul _ _
            (hmul _ _
              (hmul _ _ (realizes_transvection hU h0 hij a)
                (realizes_transvection hU h0 hij.symm (-a⁻¹)))
              (realizes_transvection hU h0 hij a))
            (realizes_transvection hU h0 hij (-1)))
          (realizes_transvection hU h0 hij.symm 1))
        (realizes_transvection hU h0 hij (-1))
  · exact fun i j hij a => realizes_transvection hU h0 hij a
  · exact hmul

private theorem
    Degree.SupportedGerms.realizes_det_one {ι : Type*} [Finite ι] [Nontrivial ι] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (b : Module.Basis ι ℝ E)
    (C : E ≃L[ℝ] E) (hdet : C.toLinearMap.det = 1) {U : Set E} (hU : IsOpen U)
    (h0 : (0 : E) ∈ U) : Realizes U C := by
  classical
  let := Fintype.ofFinite ι
  let A : Matrix.SpecialLinearGroup ι ℝ :=
    ⟨LinearMap.toMatrix b b C.toLinearMap, (LinearMap.det_toMatrix b C.toLinearMap).trans hdet⟩
  let c : (ι → ℝ) ≃L[ℝ] E := b.equivFun.symm.toContinuousLinearEquiv
  have h :=
    (realizes_specialLinear (c.symm.toHomeomorph.isOpenMap _ hU)
          (show (0 : ι → ℝ) ∈ c.symm '' U from ⟨0, h0, map_zero c.symm⟩) A).conj
      c
  change Realizes (c '' (c.symm '' U)) (fun y => c (A.toLin' (c.symm y))) at h
  have hset : c '' (c.symm '' U) = U := by
    rw [← Set.image_comp]
    simp only [ContinuousLinearEquiv.self_comp_symm, Set.image_id]
  rw [hset] at h
  convert h using 1
  funext x
  apply c.symm.injective
  rw [c.symm_apply_apply]
  exact (LinearMap.toMatrix_mulVec_repr b b C.toLinearMap x).symm

private theorem
    Smale.SmallPerturbation.lipschitzWith_cutoff_smul {P E : Type*} [PseudoMetricSpace P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {u : P → E} {β : P → ℝ} {S : Set P} {a b R : ℝ≥0}
    (hu : LipschitzOnWith a u S) (hbound : ∀ x ∈ S, ‖u x‖ ≤ R) (hβ : LipschitzWith b β)
    (hβbound : ∀ x, |β x| ≤ 1) (hzero : ∀ x ∉ S, β x = 0) :
    LipschitzWith (a + b * R) (fun x => β x • u x) := by
  have hcross (x y : P) (hx : x ∈ S) (hy : y ∉ S) :
    Dist.dist (β x • u x) (β y • u y) ≤ ((a + b * R : ℝ≥0) : ℝ) * Dist.dist x y := by
    have hβx : |β x| ≤ (b : ℝ) * Dist.dist x y := by
      have h := hβ.dist_le_mul x y
      simpa only [hzero y hy, Real.dist_eq, sub_zero] using h
    rw [hzero y hy, zero_smul, dist_zero_right, norm_smul, Real.norm_eq_abs]
    calc
      |β x| * ‖u x‖ ≤ ((b : ℝ) * Dist.dist x y) * R :=
        mul_le_mul hβx (hbound x hx) (norm_nonneg _) (by positivity)
      _ ≤ ((a + b * R : ℝ≥0) : ℝ) * Dist.dist x y := by
        simp only [NNReal.coe_add, NNReal.coe_mul]
        nlinarith [mul_nonneg a.coe_nonneg (dist_nonneg (x := x) (y := y))]
  apply LipschitzWith.of_dist_le_mul
  intro x y
  by_cases hx : x ∈ S
  · by_cases hy : y ∈ S
    · have hu' : ‖u x - u y‖ ≤ (a : ℝ) * Dist.dist x y := by
        simpa only [dist_eq_norm] using hu.dist_le_mul x hx y hy
      have hβ' : |β x - β y| ≤ (b : ℝ) * Dist.dist x y := by
        simpa only [Real.dist_eq] using hβ.dist_le_mul x y
      have hsplit : β x • u x - β y • u y = β x • (u x - u y) + (β x - β y) • u y := by
        rw [smul_sub, sub_smul]
        abel
      rw [dist_eq_norm, hsplit]
      calc
        ‖β x • (u x - u y) + (β x - β y) • u y‖ ≤ ‖β x • (u x - u y)‖ + ‖(β x - β y) • u y‖ :=
          norm_add_le _ _
        _ = |β x| * ‖u x - u y‖ + |β x - β y| * ‖u y‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
        _ ≤ 1 * ((a : ℝ) * Dist.dist x y) + ((b : ℝ) * Dist.dist x y) * R := by
          exact
            add_le_add (mul_le_mul (hβbound x) hu' (norm_nonneg _) (by norm_num))
              (mul_le_mul hβ' (hbound y hy) (norm_nonneg _) (by positivity))
        _ = ((a + b * R : ℝ≥0) : ℝ) * Dist.dist x y := by
          simp only [NNReal.coe_add, NNReal.coe_mul]
          ring
    · exact hcross x y hx hy
  · by_cases hy : y ∈ S
    · simpa only [dist_comm] using hcross y x hy hx
    · rw [hzero x hx, hzero y hy, zero_smul, zero_smul, dist_self]
      positivity

private theorem
    Smale.SmallPerturbation.exists_closedBall_small_lipschitz_of_fderiv_zero {P E : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E] {u : P → E}
    {U : Set P} (hU : IsOpen U) (hzero : (0 : P) ∈ U) (hu : ContDiffOn ℝ ∞ u U)
    (hdu : fderiv ℝ u 0 = 0) {a : ℝ≥0} (ha : 0 < a) :
    ∃ ρ : ℝ,
      0 < ρ ∧
        Metric.closedBall (0 : P) ρ ⊆ U ∧ LipschitzOnWith a u (Metric.closedBall (0 : P) ρ) := by
  have hd : ContinuousAt (fderiv ℝ u) 0 :=
    (hu.continuousOn_fderiv_of_isOpen hU (by simp)).continuousAt (hU.mem_nhds hzero)
  have hsmall : ∀ᶠ x in 𝓝 (0 : P), ‖fderiv ℝ u x‖ < (a : ℝ) := by
    have h : ∀ᶠ x in 𝓝 (0 : P), fderiv ℝ u x ∈ Metric.ball (fderiv ℝ u 0) (a : ℝ) :=
      hd.preimage_mem_nhds (Metric.ball_mem_nhds (fderiv ℝ u 0) (show (0 : ℝ) < a from ha))
    simpa only [hdu, mem_ball_zero_iff] using h
  have hnear : ∀ᶠ x in 𝓝 (0 : P), x ∈ U := hU.mem_nhds hzero
  obtain ⟨ρ, hρ, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hnear.and hsmall)
  refine ⟨ρ, hρ, fun x hx => (hball hx).1, ?_⟩
  apply (convex_closedBall (0 : P) ρ).lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
  · intro x hx
    exact (hu.contDiffAt (hU.mem_nhds (hball hx).1)).differentiableAt (by simp)
  · intro x hx
    exact (hball hx).2.le

private theorem Smale.SmallPerturbation.exists_lipschitz_supported_germ {P E : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] [NormedAddCommGroup E]
    [NormedSpace ℝ E] {u : P → E} {U : Set P} (hU : IsOpen U) (hzero : (0 : P) ∈ U)
    (hu : ContDiffOn ℝ ∞ u U) (hu₀ : u 0 = 0) (hdu : fderiv ℝ u 0 = 0) {κ : ℝ≥0} (hκ : 0 < κ) :
    ∃ w : P → E,
      ContDiff ℝ ∞ w ∧
        HasCompactSupport w ∧
          tsupport w ⊆ U ∧
            LipschitzWith κ w ∧ w =ᶠ[𝓝 (0 : P)] u ∧ ∀ x, ∃ c ∈ Set.Icc (0 : ℝ) 1, w x = c • u x :=
  by
  obtain ⟨β, hβ, hβcompact, hβsupport, hβone, hβrange⟩ :=
    Smale.exists_compact_smooth_cutoff (K := {(0 : P)}) (U := Metric.ball (0 : P) 1)
      isCompact_singleton Metric.isOpen_ball (by simp)
  obtain ⟨k, hk⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hβcompact hβ (by simp)
  let a : ℝ≥0 := κ / (1 + k)
  have hden : (0 : ℝ≥0) < 1 + k := by positivity
  have ha : 0 < a := div_pos hκ hden
  obtain ⟨ρ, hρ, hρU, hlocal⟩ :=
    exists_closedBall_small_lipschitz_of_fderiv_zero hU hzero hu hdu ha
  let r : ℝ≥0 := ⟨ρ, hρ.le⟩
  have hr : 0 < r := hρ
  let βρ : P → ℝ := fun x => β (ρ⁻¹ • x)
  have hβρ : ContDiff ℝ ∞ βρ := hβ.comp (ρ⁻¹ • ContinuousLinearMap.id ℝ P).contDiff
  have hβρlip : LipschitzWith (k * ‖ρ⁻¹‖₊) βρ := hk.comp (lipschitzWith_smul ρ⁻¹)
  have hβρbound (x : P) : |βρ x| ≤ 1 := by
    change |β (ρ⁻¹ • x)| ≤ 1
    rw [abs_of_nonneg (hβrange _).1]
    exact (hβrange _).2
  have hβρzero (x : P) (hx : x ∉ Metric.closedBall (0 : P) ρ) : βρ x = 0 := by
    by_contra hne
    have hm : ρ⁻¹ • x ∈ Metric.ball (0 : P) 1 := hβsupport (subset_tsupport β hne)
    have hn : ‖ρ⁻¹ • x‖ < 1 := mem_ball_zero_iff.mp hm
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρ), inv_mul_lt_one₀ hρ] at hn
    exact hx (mem_closedBall_zero_iff.mpr hn.le)
  have hbound : ∀ x ∈ Metric.closedBall (0 : P) ρ, ‖u x‖ ≤ (a * r : ℝ≥0) := by
    intro x hx
    have h0 : (0 : P) ∈ Metric.closedBall (0 : P) ρ := by simpa using hρ.le
    have hn := hlocal.dist_le_mul x hx 0 h0
    rw [hu₀, dist_zero_right, dist_zero_right] at hn
    change ‖u x‖ ≤ (a : ℝ) * ρ
    exact hn.trans (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hx) a.coe_nonneg)
  let w : P → E := fun x => βρ x • u x
  have hwzero (x : P) (hx : x ∉ Metric.closedBall (0 : P) ρ) : w x = 0 := by
    change βρ x • u x = 0
    rw [hβρzero x hx, zero_smul]
  have hsmooth : ContDiff ℝ ∞ w := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ U
    · exact hβρ.contDiffAt.smul (hu.contDiffAt (hU.mem_nhds hx))
    · have hnot : x ∉ Metric.closedBall (0 : P) ρ := fun h => hx (hρU h)
      have hc : ContDiffAt ℝ ∞ (fun _ : P => (0 : E)) x := contDiffAt_const
      apply hc.congr_of_eventuallyEq
      filter_upwards [Metric.isClosed_closedBall.isOpen_compl.mem_nhds hnot] with y hy
      exact hwzero y hy
  have hcompact : HasCompactSupport w :=
    HasCompactSupport.intro (ProperSpace.isCompact_closedBall (0 : P) ρ) hwzero
  have hsupport : tsupport w ⊆ Metric.closedBall (0 : P) ρ := by
    apply closure_minimal _ Metric.isClosed_closedBall
    intro x hx
    by_contra hnot
    exact hx (hwzero x hnot)
  have hwlip : LipschitzWith (a + (k * ‖ρ⁻¹‖₊) * (a * r)) w :=
    lipschitzWith_cutoff_smul hlocal hbound hβρlip hβρbound hβρzero
  have hnn : ‖ρ‖₊ = r := Real.nnnorm_of_nonneg hρ.le
  have hcoeff : a + (k * ‖ρ⁻¹‖₊) * (a * r) = κ := by
    rw [nnnorm_inv, hnn]
    calc
      a + (k * r⁻¹) * (a * r) = a + (k * a) * (r⁻¹ * r) := by ring
      _ = a + k * a := by rw [inv_mul_cancel₀ hr.ne', mul_one]
      _ = (1 + k) * a := by ring
      _ = κ := by
        dsimp [a]
        rw [div_eq_mul_inv, ← mul_assoc, mul_comm (1 + k) κ, mul_assoc, mul_inv_cancel₀ hden.ne',
          mul_one]
  rw [hcoeff] at hwlip
  have hβ₀ : ∀ᶠ x in 𝓝 (0 : P), β x = 1 :=
    hβone.filter_mono (nhds_le_nhdsSet (Set.mem_singleton (0 : P)))
  have hscale : Filter.Tendsto (fun x : P => ρ⁻¹ • x) (𝓝 0) (𝓝 0) := by
    have hs : Continuous (fun x : P => ρ⁻¹ • x) := (ρ⁻¹ • ContinuousLinearMap.id ℝ P).continuous
    simpa only [smul_zero] using (hs.continuousAt (x := (0 : P))).tendsto
  have hgerm : w =ᶠ[𝓝 (0 : P)] u := by
    have hscaled : ∀ᶠ x in 𝓝 (0 : P), β (ρ⁻¹ • x) = 1 := hscale hβ₀
    filter_upwards [hscaled] with x hx
    change β (ρ⁻¹ • x) • u x = u x
    rw [hx, one_smul]
  refine ⟨w, hsmooth, hcompact, hsupport.trans hρU, hwlip, hgerm, ?_⟩
  intro x
  exact ⟨βρ x, hβrange _, rfl⟩

private theorem Smale.SmallPerturbation.exists_supported_tangent_identity_isotopy {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {f : E → E} {U : Set E}
    (hU : IsOpen U) (hzero : (0 : E) ∈ U) (hf : ContDiffOn ℝ ∞ f U) (hf₀ : f 0 = 0)
    (hdf : fderiv ℝ f 0 = ContinuousLinearMap.id ℝ E) :
    ∃ (A : ℝ × E → E) (K : Set E),
      IsCompact K ∧
        K ⊆ U ∧
          ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ A ∧
            (∀ x, A (0, x) = x) ∧
              (∀ t, ∃ D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞, ∀ x, D x = A (t, x)) ∧
                (∀ t x, x ∉ K → A (t, x) = x) ∧
                  (∀ t x, ∃ c ∈ Set.Icc (0 : ℝ) 1, A (t, x) = x + c • (f x - x)) ∧
                    (fun x => A (1, x)) =ᶠ[𝓝 (0 : E)] f := by
  let u : E → E := fun x => f x - x
  have hu : ContDiffOn ℝ ∞ u U := hf.sub contDiffOn_id
  have hu₀ : u 0 = 0 := by simp [u, hf₀]
  have hdu : fderiv ℝ u 0 = 0 := by
    have hdiff : DifferentiableAt ℝ f 0 :=
      (hf.contDiffAt (hU.mem_nhds hzero)).differentiableAt (by simp)
    change fderiv ℝ (f - id) 0 = 0
    rw [fderiv_sub hdiff differentiableAt_id, hdf, fderiv_id, sub_self]
  obtain ⟨w, hw, hwcompact, hwsupport, hwlip, hweq, hwscalar⟩ :=
    exists_lipschitz_supported_germ hU hzero hu hu₀ hdu (show (0 : ℝ≥0) < 1 / 2 by norm_num)
  let A : ℝ × E → E := fun p => p.2 + Real.smoothTransition p.1 • w p.2
  have hθ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ Real.smoothTransition :=
    (Real.smoothTransition.contDiff (n := ⊤)).contMDiff
  have hA : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ A :=
    contMDiff_snd.add ((hθ.comp contMDiff_fst).smul (hw.contMDiff.comp contMDiff_snd))
  refine ⟨A, tsupport w, hwcompact.isCompact, hwsupport, hA, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    simp [A, Real.smoothTransition.zero]
  · intro t
    have hs : ContDiff ℝ ∞ (fun x => Real.smoothTransition t • w x) := contDiff_const.smul hw
    have hlip :
      LipschitzWith (‖Real.smoothTransition t‖₊ * (1 / 2))
        (fun x => Real.smoothTransition t • w x) :=
      (lipschitzWith_smul (Real.smoothTransition t)).comp hwlip
    have hθnorm : ‖Real.smoothTransition t‖₊ ≤ 1 := by
      change ‖Real.smoothTransition t‖ ≤ (1 : ℝ)
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.smoothTransition.nonneg t)]
      exact Real.smoothTransition.le_one t
    have hsmall : ‖Real.smoothTransition t‖₊ * (1 / 2 : ℝ≥0) < 1 := by
      calc
        _ ≤ 1 * (1 / 2 : ℝ≥0) := mul_le_mul_of_nonneg_right hθnorm (by positivity)
        _ < 1 := by norm_num
    exact ⟨diffeomorphIdAdd hs hlip hsmall, fun _ => rfl⟩
  · intro t x hx
    have hz : w x = 0 := by
      by_contra hne
      exact hx (subset_tsupport w hne)
    simp only [A, hz, smul_zero, add_zero]
  · intro t x
    obtain ⟨c, hc, hwc⟩ := hwscalar x
    refine
      ⟨Real.smoothTransition t * c,
        ⟨mul_nonneg (Real.smoothTransition.nonneg t) hc.1,
          (mul_le_mul_of_nonneg_right (Real.smoothTransition.le_one t) hc.1).trans
            (by simpa only [one_mul] using hc.2)⟩,
        ?_⟩
    change x + Real.smoothTransition t • w x = x + _
    rw [hwc, smul_smul]
  · filter_upwards [hweq] with x hx
    change x + Real.smoothTransition 1 • w x = f x
    rw [Real.smoothTransition.one, one_smul, hx]
    change x + (f x - x) = f x
    abel

private theorem Smale.SmallPerturbation.exists_relative_tangent_identity_isotopy {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : E → E} {U S : Set E} (hU : IsOpen U) (hzero : (0 : E) ∈ U)
    (hf : ContDiffOn ℝ ∞ f U) (hf₀ : f 0 = 0) (hdf : fderiv ℝ f 0 = ContinuousLinearMap.id ℝ E)
    (Q : E →L[ℝ] F) (hQ : ∀ x ∈ U, Q (f x) = Q x) (hS : ∀ x ∈ U ∩ S, f x = x) :
    ∃ (A : ℝ × E → E) (K : Set E),
      IsCompact K ∧
        K ⊆ U ∧
          ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ A ∧
            (∀ x, A (0, x) = x) ∧
              (∀ t, ∃ D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞, ∀ x, D x = A (t, x)) ∧
                (∀ t x, x ∉ K → A (t, x) = x) ∧
                  (∀ t x, Q (A (t, x)) = Q x) ∧
                    (∀ t x, x ∈ S → A (t, x) = x) ∧ (fun x => A (1, x)) =ᶠ[𝓝 (0 : E)] f := by
  obtain ⟨A, K, hK, hKU, hA, hA₀, hdiff, hfix, hscalar, hgerm⟩ :=
    exists_supported_tangent_identity_isotopy hU hzero hf hf₀ hdf
  refine ⟨A, K, hK, hKU, hA, hA₀, hdiff, hfix, ?_, ?_, hgerm⟩
  · intro t x
    by_cases hx : x ∈ U
    · obtain ⟨c, _, heq⟩ := hscalar t x
      rw [heq, map_add, map_smul, map_sub, hQ x hx, sub_self, smul_zero, add_zero]
    · rw [hfix t x (fun h => hx (hKU h))]
  · intro t x hxS
    by_cases hx : x ∈ U
    · obtain ⟨c, _, heq⟩ := hscalar t x
      rw [heq, hS x ⟨hx, hxS⟩, sub_self, smul_zero, add_zero]
    · exact hfix t x (fun h => hx (hKU h))

private theorem
    Smale.SmallPerturbation.fderiv_preserves_projection {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → E} {U : Set E}
    (hU : IsOpen U) (hzero : (0 : E) ∈ U) (hf : DifferentiableAt ℝ f 0) (Q : E →L[ℝ] F)
    (hQ : ∀ x ∈ U, Q (f x) = Q x) : Q.comp (fderiv ℝ f 0) = Q := by
  have heq : Q ∘ f =ᶠ[𝓝 (0 : E)] Q := by
    filter_upwards [hU.mem_nhds hzero] with x hx
    exact hQ x hx
  have hc : fderiv ℝ (Q ∘ f) 0 = Q.comp (fderiv ℝ f 0) :=
    (Q.hasFDerivAt.comp 0 hf.hasFDerivAt).fderiv
  exact hc.symm.trans (heq.fderiv_eq.trans Q.fderiv)

private theorem Smale.SmallPerturbation.fderiv_fixes_subspace {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → E} {U : Set E} (hU : IsOpen U) (hzero : (0 : E) ∈ U)
    (hf : DifferentiableAt ℝ f 0) (S : Submodule ℝ E) (hS : ∀ x ∈ U ∩ (S : Set E), f x = x) :
    ∀ x ∈ S, fderiv ℝ f 0 x = x := by
  have heq : f ∘ (S.subtypeL : S → E) =ᶠ[𝓝 (0 : S)] (S.subtypeL : S → E) := by
    have hn : ∀ᶠ x : S in 𝓝 (0 : S), (x : E) ∈ U :=
      S.subtypeL.continuous.continuousAt.preimage_mem_nhds (hU.mem_nhds hzero)
    filter_upwards [hn] with x hx
    exact hS x ⟨hx, x.property⟩
  have hc : fderiv ℝ (f ∘ (S.subtypeL : S → E)) (0 : S) = (fderiv ℝ f 0).comp S.subtypeL :=
    (hf.hasFDerivAt.comp (0 : S) S.subtypeL.hasFDerivAt).fderiv
  have hlinear : (fderiv ℝ f 0).comp S.subtypeL = S.subtypeL :=
    hc.symm.trans (heq.fderiv_eq.trans S.subtypeL.fderiv)
  intro x hx
  exact congrArg (fun A : S →L[ℝ] E => A ⟨x, hx⟩) hlinear

private theorem Smale.SmallPerturbation.exists_relative_germ_linearization_isotopy {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : E → E} {U : Set E} (hU : IsOpen U) (hzero : (0 : E) ∈ U)
    (hf : ContDiffOn ℝ ∞ f U) (hf₀ : f 0 = 0) (hdf : Function.Bijective (fderiv ℝ f 0))
    (Q : E →L[ℝ] F) (hQ : ∀ x ∈ U, Q (f x) = Q x) (S : Submodule ℝ E)
    (hS : ∀ x ∈ U ∩ (S : Set E), f x = x) :
    ∃ (C : E ≃L[ℝ] E) (A : ℝ × E → E) (K : Set E),
      C.toContinuousLinearMap = fderiv ℝ f 0 ∧
        (∀ x, Q (C x) = Q x) ∧
          (∀ x ∈ S, C x = x) ∧
            IsCompact K ∧
              K ⊆ U ∧
                ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ A ∧
                  (∀ x, A (0, x) = x) ∧
                    (∀ t, ∃ D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞, ∀ x, D x = A (t, x)) ∧
                      (∀ t x, x ∉ K → A (t, x) = x) ∧
                        (∀ t x, Q (A (t, x)) = Q x) ∧
                          (∀ t x, x ∈ S → A (t, x) = x) ∧
                            f =ᶠ[𝓝 (0 : E)] (fun x => C (A (1, x))) := by
  have hfd : DifferentiableAt ℝ f 0 :=
    (hf.contDiffAt (hU.mem_nhds hzero)).differentiableAt (by simp)
  let C := (LinearEquiv.ofBijective (fderiv ℝ f 0).toLinearMap hdf).toContinuousLinearEquiv
  have hC : C.toContinuousLinearMap = fderiv ℝ f 0 := rfl
  have hQC : ∀ x, Q (C x) = Q x := by
    intro x
    exact congrArg (fun A : E →L[ℝ] F => A x) (fderiv_preserves_projection hU hzero hfd Q hQ)
  have hCS : ∀ x ∈ S, C x = x := fderiv_fixes_subspace hU hzero hfd S hS
  have hQCinv (y : E) : Q (C.symm y) = Q y := by
    have h := (hQC (C.symm y)).symm
    simpa only [C.apply_symm_apply] using h
  have hCSinv (x : E) (hx : x ∈ S) : C.symm x = x := by
    have h := C.symm_apply_apply x
    rwa [hCS x hx] at h
  let G : E → E := C.symm ∘ f
  have hG : ContDiffOn ℝ ∞ G U := C.symm.contDiff.comp_contDiffOn hf
  have hG₀ : G 0 = 0 := by simp [G, hf₀]
  have hGder : fderiv ℝ G 0 = C.symm.toContinuousLinearMap.comp (fderiv ℝ f 0) :=
    (C.symm.toContinuousLinearMap.hasFDerivAt.comp 0 hfd.hasFDerivAt).fderiv
  have hdG : fderiv ℝ G 0 = ContinuousLinearMap.id ℝ E := by
    rw [hGder, ← hC]
    ext x
    exact C.symm_apply_apply x
  have hQG : ∀ x ∈ U, Q (G x) = Q x := by
    intro x hx
    change Q (C.symm (f x)) = Q x
    rw [hQCinv, hQ x hx]
  have hSG : ∀ x ∈ U ∩ (S : Set E), G x = x := by
    intro x hx
    change C.symm (f x) = x
    rw [hS x hx, hCSinv x hx.2]
  obtain ⟨A, K, hK, hKU, hA, hA₀, hdiff, hfix, hprojection, hfixed, hgerm⟩ :=
    exists_relative_tangent_identity_isotopy hU hzero hG hG₀ hdG Q hQG hSG
  refine ⟨C, A, K, hC, hQC, hCS, hK, hKU, hA, hA₀, hdiff, hfix, hprojection, hfixed, ?_⟩
  filter_upwards [hgerm] with x hx
  change A (1, x) = C.symm (f x) at hx
  rw [hx, C.apply_symm_apply]

private theorem Degree.SupportedGerms.realizes_local_germ {E ι : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Finite ι] [Nontrivial ι] (b : Module.Basis ι ℝ E)
    {f : E → E} {U : Set E} (hU : IsOpen U) (h0 : (0 : E) ∈ U) (hf : ContDiffOn ℝ ∞ f U)
    (hf0 : f 0 = 0) (hbij : Function.Bijective (fderiv ℝ f 0))
    (hdet : (fderiv ℝ f 0).toLinearMap.det = 1) : Realizes U f := by
  classical
  let := Fintype.ofFinite ι
  obtain ⟨C, A, K, hC, -, -, hK, hKU, hA, hA0, hdiff, hfix, -, hfixed, hgerm⟩ :=
    Smale.SmallPerturbation.exists_relative_germ_linearization_isotopy hU h0 hf hf0 hbij
      (0 : E →L[ℝ] ℝ) (fun _ _ => rfl) (⊥ : Submodule ℝ E)
      (by
        intro x hx
        have hx0 : x = 0 := hx.2
        subst x
        exact hf0)
  have hCdet : C.toLinearMap.det = 1 := by
    change C.toContinuousLinearMap.toLinearMap.det = 1
    rw [hC]
    exact hdet
  obtain ⟨d, hd⟩ := hdiff 1
  have H : Smale.SupportedDiffeomorph.SupportedRelativeIsotopy d K {0} := by
    refine ⟨A, hA, hA0, fun x => (hd x).symm, hdiff, hfix, ?_⟩
    intro t x hx
    exact hfixed t x (Set.mem_singleton_iff.mp hx)
  have hdreal : Realizes U (fun x => A (1, x)) :=
    ⟨d, K, hK, hKU, ⟨H⟩, Filter.Eventually.of_forall hd⟩
  obtain ⟨D, L, hL, hLU, hH, hDgerm⟩ := (realizes_det_one b C hCdet hU h0).comp hdreal
  exact ⟨D, L, hL, hLU, hH, hDgerm.trans hgerm.symm⟩

private def Degree.LinearFramePaths.scalarDiagonal {ι : Type*} [DecidableEq ι] (i : ι) (a : ℝ) :
    Matrix ι ι ℝ :=
  Matrix.diagonal (fun k => if k = i then a else 1)

private theorem
    Degree.LinearFramePaths.det_scalarDiagonal {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι)
    (a : ℝ) : Matrix.det (scalarDiagonal i a) = a := by simp [scalarDiagonal, Matrix.det_diagonal]

private theorem
    Degree.LinearFramePaths.scalarDiagonal_mul {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι)
    (a b : ℝ) : scalarDiagonal i a * scalarDiagonal i b = scalarDiagonal i (a * b) := by
  rw [scalarDiagonal, scalarDiagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext k
  by_cases h : k = i <;> simp [h]

private theorem Degree.LinearFramePaths.scalarDiagonal_one {ι : Type*} [DecidableEq ι] (i : ι) :
    scalarDiagonal i 1 = 1 := by simp [scalarDiagonal]

private theorem
    Degree.LinearFramePaths.continuous_scalarDiagonal {ι : Type*} [DecidableEq ι] (i : ι) :
    Continuous (scalarDiagonal i) := by
  apply continuous_pi
  intro k
  apply continuous_pi
  intro l
  simp only [scalarDiagonal, Matrix.diagonal_apply]
  by_cases hkl : k = l
  · simp only [hkl, ite_true]
    by_cases hli : l = i
    · simp only [hli, ite_true]
      fun_prop
    · simp only [hli, ite_false]
      fun_prop
  · simp only [hkl, ite_false]
    fun_prop

private def
    Degree.LinearFramePaths.determinantComponent {ι : Type*} [Fintype ι] [DecidableEq ι] (σ : ℝ) :
    TopologicalSpace.Opens (Matrix ι ι ℝ) :=
  ⟨{A | 0 < σ * Matrix.det A},
    isOpen_lt continuous_const (continuous_const.mul continuous_id.matrix_det)⟩

private def
    Degree.LinearFramePaths.diagonalPoint {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) {σ : ℝ}
    (A : determinantComponent (ι := ι) σ) : determinantComponent (ι := ι) σ :=
  ⟨scalarDiagonal i (Matrix.det (A : Matrix ι ι ℝ)),
    by
    change 0 < σ * Matrix.det (scalarDiagonal i (Matrix.det (A : Matrix ι ι ℝ)))
    rw [det_scalarDiagonal]
    exact A.property⟩

private theorem
    Degree.LinearFramePaths.joined_diagonal_to_matrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nontrivial ι] (i : ι) {σ : ℝ} (A : determinantComponent (ι := ι) σ) :
    Joined (diagonalPoint i A) A := by
  have ha : Matrix.det (A : Matrix ι ι ℝ) ≠ 0 := by
    intro hz
    have hh : 0 < σ * Matrix.det (A : Matrix ι ι ℝ) := A.property
    rw [hz, MulZeroClass.mul_zero] at hh
    exact lt_irrefl _ hh
  let N : Matrix.SpecialLinearGroup ι ℝ :=
    ⟨scalarDiagonal i (Matrix.det (A : Matrix ι ι ℝ))⁻¹ * (A : Matrix ι ι ℝ), by
      rw [Matrix.det_mul, det_scalarDiagonal, inv_mul_cancel₀ ha]⟩
  let ψ : Matrix.SpecialLinearGroup ι ℝ → determinantComponent (ι := ι) σ := fun L =>
    ⟨scalarDiagonal i (Matrix.det (A : Matrix ι ι ℝ)) * (L : Matrix ι ι ℝ),
      by
      change 0 < σ * Matrix.det (scalarDiagonal i (Matrix.det (A : Matrix ι ι ℝ)) * L.val)
      rw [Matrix.det_mul, det_scalarDiagonal, L.property, mul_one]
      exact A.property⟩
  have hψ : Continuous ψ := (continuous_const.mul continuous_subtype_val).subtype_mk _
  have h0 : ψ 1 = diagonalPoint i A := by
    apply Subtype.ext
    change scalarDiagonal i (Matrix.det (A : Matrix ι ι ℝ)) * 1 = _
    rw [mul_one]
    rfl
  have h1 : ψ N = A := by
    apply Subtype.ext
    change
      scalarDiagonal i (Matrix.det (A : Matrix ι ι ℝ)) *
          (scalarDiagonal i (Matrix.det (A : Matrix ι ι ℝ))⁻¹ * (A : Matrix ι ι ℝ)) =
        _
    rw [← mul_assoc, scalarDiagonal_mul, mul_inv_cancel₀ ha, scalarDiagonal_one, one_mul]
  have h := (joined_one_specialLinear N).map hψ
  rwa [h0, h1] at h

private theorem
    Degree.LinearFramePaths.joined_diagonal_points {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) {σ : ℝ} (A B : determinantComponent (ι := ι) σ) :
    Joined (diagonalPoint i A) (diagonalPoint i B) := by
  let g := fun t : unitInterval =>
    (1 - (t : ℝ)) * Matrix.det (A : Matrix ι ι ℝ) + (t : ℝ) * Matrix.det (B : Matrix ι ι ℝ)
  have hg : Continuous g := by fun_prop
  have hpos (t : unitInterval) : 0 < σ * g t := by
    have hh :=
      (convex_Ioi (0 : ℝ)) A.property B.property (sub_nonneg.mpr t.property.2) t.property.1
        (show 1 - (t : ℝ) + (t : ℝ) = 1 by ring)
    change
      0 <
        (1 - (t : ℝ)) * (σ * Matrix.det (A : Matrix ι ι ℝ)) +
          (t : ℝ) * (σ * Matrix.det (B : Matrix ι ι ℝ)) at hh
    convert hh using 1
    dsimp only [g]
    ring
  refine
    ⟨{  toFun := fun t =>
          ⟨scalarDiagonal i (g t),
            by
            change 0 < σ * Matrix.det (scalarDiagonal i (g t))
            rw [det_scalarDiagonal]
            exact hpos t⟩
        continuous_toFun :=
          ((continuous_scalarDiagonal i).comp hg).subtype_mk
            (fun t => by
              change 0 < σ * Matrix.det (scalarDiagonal i (g t))
              rw [det_scalarDiagonal]
              exact hpos t)
        source' := ?_
        target' := ?_ }⟩
  · apply Subtype.ext
    simp [g, diagonalPoint]
  · apply Subtype.ext
    simp [g, diagonalPoint]

private theorem Degree.LinearFramePaths.joined_determinantComponent {ι : Type*} [Fintype ι]
    [DecidableEq ι] [Nontrivial ι] {σ : ℝ} (A B : determinantComponent (ι := ι) σ) : Joined A B :=
  by
  let i := Classical.choice (inferInstance : Nonempty ι)
  exact
    (joined_diagonal_to_matrix i A).symm.trans
      ((joined_diagonal_points i A B).trans (joined_diagonal_to_matrix i B))

private theorem
    Degree.SupportedGerms.exists_linearEquiv_with_det {B ι : Type*} [NormedAddCommGroup B]
    [NormedSpace ℝ B] [FiniteDimensional ℝ B] [Finite ι] (b : Module.Basis ι ℝ B) (i : ι) {r : ℝ}
    (hr : r ≠ 0) : ∃ R : B ≃L[ℝ] B, R.toLinearMap.det = r := by
  classical
  let := Fintype.ofFinite ι
  let L : B →ₗ[ℝ] B := Matrix.toLin b b (Degree.LinearFramePaths.scalarDiagonal i r)
  have hdet : L.det = r := by
    rw [← LinearMap.det_toMatrix b L]
    change
      Matrix.det
          (LinearMap.toMatrix b b
            (Matrix.toLin b b (Degree.LinearFramePaths.scalarDiagonal i r))) =
        r
    rw [LinearMap.toMatrix_toLin]
    exact Degree.LinearFramePaths.det_scalarDiagonal i r
  have hker : L.ker = ⊥ := by
    by_contra hk
    exact hr (hdet.symm.trans (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hk))
  have hi : Function.Injective L := LinearMap.ker_eq_bot.mp hker
  have hbij : Function.Bijective L :=
    ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hi⟩
  exact ⟨(LinearEquiv.ofBijective L hbij).toContinuousLinearEquiv, hdet⟩

private theorem
    Degree.SupportedGerms.exists_normal_det_correction {A B ι : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [FiniteDimensional ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [FiniteDimensional ℝ B] [Finite ι] (b : Module.Basis ι ℝ B) (i : ι)
    (C : (A × B) ≃L[ℝ] (A × B)) :
    ∃ R : B ≃L[ℝ] B,
      (((ContinuousLinearEquiv.refl ℝ A).prodCongr R).toContinuousLinearMap.comp
            C.toContinuousLinearMap).toLinearMap.det =
        1 := by
  classical
  let := Fintype.ofFinite ι
  have hne : C.toLinearMap.det ≠ 0 := C.toLinearEquiv.isUnit_det'.ne_zero
  obtain ⟨R, hR⟩ := exists_linearEquiv_with_det b i (inv_ne_zero hne)
  refine ⟨R, ?_⟩
  change LinearMap.det ((LinearMap.id.prodMap R.toLinearMap).comp C.toLinearMap) = 1
  rw [LinearMap.det_comp, LinearMap.det_prodMap, LinearMap.det_id, one_mul, hR,
    inv_mul_cancel₀ hne]

private theorem Degree.SupportedGerms.exists_supported_disk_germ_alignment {A B ι κ : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A] [NormedAddCommGroup B]
    [NormedSpace ℝ B] [FiniteDimensional ℝ B] [Finite ι] [Finite κ] [Nontrivial κ]
    (b : Module.Basis ι ℝ B) (i : ι) (basis : Module.Basis κ ℝ (A × B))
    (Φ : PartialDiffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, A × B) (A × B) (A × B) ∞)
    (h0 : (0 : A × B) ∈ Φ.source) (hΦ0 : Φ 0 = 0) {U : Set (A × B)} (hU : IsOpen U)
    (h0U : (0 : A × B) ∈ U) :
    ∃ (d : Diffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, A × B) (A × B) (A × B) ∞) (K : Set (A × B)),
      IsCompact K ∧
        K ⊆ U ∧
          Nonempty (Smale.SupportedDiffeomorph.SupportedRelativeIsotopy d K {0}) ∧
            (fun x : A => d (Φ (x, 0))) =ᶠ[𝓝 (0 : A)] (fun x => (x, (0 : B))) := by
  classical
  let := Fintype.ofFinite ι
  let := Fintype.ofFinite κ
  have ht0 : (0 : A × B) ∈ Φ.target := hΦ0 ▸ Φ.map_source' h0
  have hi0 : Φ.symm 0 = 0 := by
    have hh := Φ.left_inv' h0
    rwa [hΦ0] at hh
  have hi : ContDiffOn ℝ ∞ (Φ.symm : (A × B) → A × B) Φ.target := Φ.contMDiffOn_invFun.contDiffOn
  have hib : Function.Bijective (fderiv ℝ Φ.symm 0) := by
    have hh := Smale.PartialChart.bijective_mfderiv Φ.symm ht0
    change
      Function.Bijective (mfderiv 𝓘(ℝ, A × B) 𝓘(ℝ, A × B) Φ.symm 0 : (A × B) →L[ℝ] (A × B)) at hh
    rwa [mfderiv_eq_fderiv] at hh
  let C := (LinearEquiv.ofBijective (fderiv ℝ Φ.symm 0).toLinearMap hib).toContinuousLinearEquiv
  obtain ⟨R, hR⟩ := exists_normal_det_correction b i C
  let T := (ContinuousLinearEquiv.refl ℝ A).prodCongr R
  let f : (A × B) → A × B := T ∘ Φ.symm
  have hf : ContDiffOn ℝ ∞ f (U ∩ Φ.target) :=
    T.contDiff.comp_contDiffOn (hi.mono Set.inter_subset_right)
  have hf0 : f 0 = 0 := by simp only [f, Function.comp_apply, hi0, map_zero]
  have hfi :=
    ((hi.contDiffAt (Φ.open_target.mem_nhds ht0)).differentiableAt (by simp)).hasFDerivAt
  have hdf : fderiv ℝ f 0 = T.toContinuousLinearMap.comp C.toContinuousLinearMap :=
    (T.toContinuousLinearMap.hasFDerivAt.comp 0 hfi).fderiv
  have hfb : Function.Bijective (fderiv ℝ f 0) := by
    rw [hdf]
    exact T.bijective.comp C.bijective
  have hdet : (fderiv ℝ f 0).toLinearMap.det = 1 := by
    rw [hdf]
    exact hR
  obtain ⟨d, K, hK, hKU, hH, hgerm⟩ :=
    realizes_local_germ basis (hU.inter Φ.open_target) ⟨h0U, ht0⟩ hf hf0 hfb hdet
  refine ⟨d, K, hK, hKU.trans Set.inter_subset_left, hH, ?_⟩
  have hΦt : Filter.Tendsto Φ (𝓝 (0 : A × B)) (𝓝 0) := by
    have hh := Φ.toOpenPartialHomeomorph.continuousAt h0
    change Filter.Tendsto Φ (𝓝 (0 : A × B)) (𝓝 (Φ 0)) at hh
    rwa [hΦ0] at hh
  have hcore : Filter.Tendsto (fun x : A => (x, (0 : B))) (𝓝 0) (𝓝 (0 : A × B)) :=
    (continuous_id.prodMk continuous_const).tendsto 0
  filter_upwards [(hgerm.comp_tendsto hΦt).comp_tendsto hcore,
    hcore (Φ.open_source.mem_nhds h0)] with x hx hxsource
  change d (Φ (x, 0)) = f (Φ (x, 0)) at hx
  rw [hx]
  change T (Φ.symm (Φ (x, 0))) = (x, 0)
  have hinv : Φ.symm (Φ (x, 0)) = (x, 0) := Φ.left_inv' hxsource
  rw [hinv]
  simp [T]

private theorem Degree.SupportedGerms.exists_native_disk_germ_alignment {A B E H M ι κ : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A] [NormedAddCommGroup B]
    [NormedSpace ℝ B] [FiniteDimensional ℝ B] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {J : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [Finite ι] [Finite κ] [Nontrivial κ] (b : Module.Basis ι ℝ B) (i : ι)
    (basis : Module.Basis κ ℝ (A × B)) (Φ Ψ : PartialDiffeomorph 𝓘(ℝ, A × B) J (A × B) M ∞)
    (hΦ0 : (0 : A × B) ∈ Φ.source) (hΨ0 : (0 : A × B) ∈ Ψ.source) (hcenter : Φ 0 = Ψ 0) :
    ∃ (D : Diffeomorph J J M M ∞) (K : Set M),
      IsCompact K ∧
        K ⊆ Ψ.target ∧
          Nonempty (Smale.SupportedDiffeomorph.SupportedRelativeIsotopy D K {Ψ 0}) ∧
            (fun x : A => D (Φ (x, 0))) =ᶠ[𝓝 (0 : A)] (fun x => Ψ (x, (0 : B))) := by
  classical
  let := Fintype.ofFinite ι
  let := Fintype.ofFinite κ
  let Θ := Φ.trans Ψ.symm
  have hΘ0 : (0 : A × B) ∈ Θ.source := by
    refine ⟨hΦ0, ?_⟩
    change Φ 0 ∈ Ψ.target
    rw [hcenter]
    exact Ψ.map_source' hΨ0
  have hΘzero : Θ 0 = 0 := by
    change Ψ.symm (Φ 0) = 0
    rw [hcenter]
    exact Ψ.left_inv' hΨ0
  obtain ⟨d, L, hL, hLsource, ⟨Hiso⟩, hgerm⟩ :=
    exists_supported_disk_germ_alignment b i basis Θ hΘ0 hΘzero Ψ.open_source hΨ0
  let D := Smale.SupportedDiffeomorph.extension Ψ d hL hLsource Hiso.endpoint_fixed_outside
  have hfixed : ∀ x ∈ Ψ.source, Ψ x ∈ ({Ψ 0} : Set M) → x ∈ ({0} : Set (A × B)) := by
    intro x hx hh
    exact
      Set.mem_singleton_iff.mpr
        (Ψ.toOpenPartialHomeomorph.injOn hx hΨ0 (Set.mem_singleton_iff.mp hh))
  have HD := Hiso.extension Ψ hL hLsource hfixed
  refine
    ⟨D, Ψ '' L, hL.image_of_continuousOn (Ψ.contMDiffOn_toFun.continuousOn.mono hLsource), ?_,
      ⟨HD⟩, ?_⟩
  · rintro y ⟨x, hx, rfl⟩
    exact Ψ.map_source' (hLsource hx)
  · have hcore : Filter.Tendsto (fun x : A => (x, (0 : B))) (𝓝 0) (𝓝 (0 : A × B)) :=
      (continuous_id.prodMk continuous_const).tendsto 0
    filter_upwards [hgerm, hcore (Θ.open_source.mem_nhds hΘ0)] with x hx hxsource
    have ht : Φ (x, 0) ∈ Ψ.target := hxsource.2
    have hback : Ψ (Θ (x, 0)) = Φ (x, 0) := Ψ.right_inv' ht
    calc
      D (Φ (x, 0)) = D (Ψ (Θ (x, 0))) := congrArg D hback.symm
      _ = Ψ (d (Θ (x, 0))) :=
        (Smale.SupportedDiffeomorph.extension_chart Ψ d hL hLsource Hiso.endpoint_fixed_outside
          (Ψ.map_target' ht))
      _ = Ψ (x, 0) := congrArg Ψ hx

private def
    Smale.SmoothRadial.radialMap {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N] (φ : ℝ → ℝ)
    (x : N) : N :=
  φ (‖x‖ ^ 2) • x

private theorem
    Smale.SmoothRadial.norm_radialMap {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    {φ : ℝ → ℝ} (hpos : ∀ s, 0 < φ s) (x : N) : ‖radialMap φ x‖ = φ (‖x‖ ^ 2) * ‖x‖ := by
  rw [radialMap, norm_smul, Real.norm_eq_abs, abs_of_pos (hpos _)]

private theorem Smale.SmoothRadial.radius_strictMono {φ : ℝ → ℝ} (hpos : ∀ s, 0 < φ s)
    (hmono : Monotone φ) : StrictMonoOn (fun r => φ (r ^ 2) * r) (Set.Ici 0) := by
  intro r hr s hs hrs
  have hsq : r ^ 2 ≤ s ^ 2 := (sq_le_sq₀ hr hs).mpr hrs.le
  exact (mul_lt_mul_of_pos_left hrs (hpos _)).trans_le (mul_le_mul_of_nonneg_right (hmono hsq) hs)

private theorem Smale.SmoothRadial.radialMap_injective {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] {φ : ℝ → ℝ} (hpos : ∀ s, 0 < φ s) (hmono : Monotone φ) :
    Function.Injective (radialMap (N := N) φ) := by
  intro x y hxy
  have hn : ‖x‖ = ‖y‖ := by
    apply (radius_strictMono hpos hmono).injOn (norm_nonneg x) (norm_nonneg y)
    simpa only [norm_radialMap hpos] using congrArg Norm.norm hxy
  change φ (‖x‖ ^ 2) • x = φ (‖y‖ ^ 2) • y at hxy
  rw [hn] at hxy
  exact smul_right_injective N (hpos _).ne' hxy

private theorem Smale.SmoothRadial.radialMap_surjective {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] {φ : ℝ → ℝ} (hc : Continuous φ) {R : ℝ} (hR : 0 < R)
    (hout : ∀ s, R ^ 2 ≤ s → φ s = 1) : Function.Surjective (radialMap (N := N) φ) := by
  intro y
  by_cases hy : R ≤ ‖y‖
  · refine ⟨y, ?_⟩
    rw [radialMap, hout _ ((sq_le_sq₀ hR.le (norm_nonneg y)).mpr hy), one_smul]
  by_cases hyzero : y = 0
  · subst y
    exact ⟨0, by simp only [radialMap, smul_zero]⟩
  have hypos : 0 < ‖y‖ := norm_pos_iff.mpr hyzero
  have htarget : ‖y‖ ∈ Set.Icc (φ (0 ^ 2) * 0) (φ (R ^ 2) * R) := by
    simpa only [MulZeroClass.mul_zero, hout _ le_rfl, one_mul, Set.mem_Icc] using
      And.intro hypos.le (le_of_not_ge hy)
  have hcont : Continuous (fun r : ℝ => φ (r ^ 2) * r) :=
    (hc.comp (continuous_id.pow 2)).mul continuous_id
  obtain ⟨r, hr, hradius⟩ := intermediate_value_Icc hR.le hcont.continuousOn htarget
  change φ (r ^ 2) * r = ‖y‖ at hradius
  let x : N := (r / ‖y‖) • y
  have hnorm : ‖x‖ = r := by
    change ‖(r / ‖y‖) • y‖ = r
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hr.1 hypos.le),
      div_mul_cancel₀ _ hypos.ne']
  refine ⟨x, ?_⟩
  change φ (‖x‖ ^ 2) • ((r / ‖y‖) • y) = y
  rw [hnorm, smul_smul, ← mul_div_assoc, hradius, div_self hypos.ne', one_smul]

private theorem Smale.SmoothRadial.contDiff_radialMap {N : Type*} [NormedAddCommGroup N]
    [InnerProductSpace ℝ N] {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (radialMap (N := N) φ) :=
  (hφ.comp (contDiff_id.norm_sq ℝ)).smul contDiff_id

private theorem Smale.SmoothRadial.fderiv_radialMap_apply {N : Type*} [NormedAddCommGroup N]
    [InnerProductSpace ℝ N] {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (x v : N) :
    fderiv ℝ (radialMap φ) x v =
      φ (‖x‖ ^ 2) • v + (2 * deriv φ (‖x‖ ^ 2) * Inner.inner ℝ x v) • x := by
  have hscale :=
    ((hφ.differentiable (by simp) (‖x‖ ^ 2)).hasDerivAt).comp_hasFDerivAt x
      (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have hd := hscale.smul (hasFDerivAt_id x)
  rw [show fderiv ℝ (radialMap φ) x = _ from hd.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_eq_mul, Function.comp_apply,
    id_eq]
  congr 1
  ring_nf

private theorem Smale.SmoothRadial.fderiv_radialMap_injective {N : Type*} [NormedAddCommGroup N]
    [InnerProductSpace ℝ N] {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hpos : ∀ s, 0 < φ s)
    (hmono : Monotone φ) (x : N) : Function.Injective (fderiv ℝ (radialMap φ) x) := by
  have hzero : ∀ v : N, fderiv ℝ (radialMap φ) x v = 0 → v = 0 := by
    intro v hv
    have heq := congrArg (fun w : N => Inner.inner ℝ v w) hv
    rw [fderiv_radialMap_apply hφ, inner_add_right, inner_smul_right, inner_smul_right,
      real_inner_self_eq_norm_sq, real_inner_comm v x, inner_zero_right] at heq
    have hd : 0 ≤ deriv φ (‖x‖ ^ 2) := hmono.deriv_nonneg
    have hnonneg : 0 ≤ 2 * deriv φ (‖x‖ ^ 2) * (Inner.inner ℝ v x) ^ 2 := by positivity
    have hterm : φ (‖x‖ ^ 2) * ‖v‖ ^ 2 ≤ 0 := by nlinarith
    have hsq : ‖v‖ ^ 2 ≤ 0 := by
      by_contra hn
      exact (not_lt_of_ge hterm) (mul_pos (hpos _) (lt_of_not_ge hn))
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg v])
  intro v w hvw
  have hsub : fderiv ℝ (radialMap φ) x (v - w) = 0 := by rw [map_sub, hvw, sub_self]
  exact sub_eq_zero.mp (hzero (v - w) hsub)

private theorem Smale.SmoothRadial.isInvertible_fderiv_radialMap {N : Type*} [NormedAddCommGroup N]
    [InnerProductSpace ℝ N] [FiniteDimensional ℝ N] {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hpos : ∀ s, 0 < φ s) (hmono : Monotone φ) (x : N) :
    (fderiv ℝ (radialMap (N := N) φ) x).IsInvertible := by
  let L :=
    (LinearEquiv.ofInjectiveEndo (fderiv ℝ (radialMap φ) x).toLinearMap
        (fderiv_radialMap_injective hφ hpos hmono x)).toContinuousLinearEquiv
  exact ⟨L, by ext v; rfl⟩

private def
    Smale.SmoothRadial.diffeomorph {N : Type*} [NormedAddCommGroup N] [InnerProductSpace ℝ N]
    [FiniteDimensional ℝ N] {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hpos : ∀ s, 0 < φ s)
    (hmono : Monotone φ) {R : ℝ} (hR : 0 < R) (hout : ∀ s, R ^ 2 ≤ s → φ s = 1) :
    Diffeomorph 𝓘(ℝ, N) 𝓘(ℝ, N) N N ∞ := by
  have hlocal : IsLocalDiffeomorph 𝓘(ℝ, N) 𝓘(ℝ, N) ∞ (radialMap (N := N) φ) := by
    intro x
    apply
      Smale.isLocalDiffeomorphAt_of_contMDiffOn isOpen_univ (Set.mem_univ x)
        (contDiff_radialMap hφ).contMDiff.contMDiffOn
    rw [mfderiv_eq_fderiv]
    exact isInvertible_fderiv_radialMap hφ hpos hmono x
  exact
    hlocal.diffeomorphOfBijective
      ⟨radialMap_injective hpos hmono, radialMap_surjective hφ.continuous hR hout⟩

private def Smale.SmoothRadial.shrinkTimeFactor (a t : ℝ) : ℝ :=
  1 + (a - 1) * Real.smoothTransition t

private theorem Smale.SmoothRadial.shrinkTimeFactor_bounds {a : ℝ} (ha₁ : a ≤ 1) (t : ℝ) :
    a ≤ shrinkTimeFactor a t ∧ shrinkTimeFactor a t ≤ 1 := by
  have ht₀ := Real.smoothTransition.nonneg t
  have ht₁ := Real.smoothTransition.le_one t
  unfold shrinkTimeFactor
  constructor <;> nlinarith

private theorem Smale.SmoothRadial.shrinkTimeFactor_zero (a : ℝ) : shrinkTimeFactor a 0 = 1 := by
  simp only [shrinkTimeFactor, Real.smoothTransition.zero, MulZeroClass.mul_zero, add_zero]

private theorem Smale.SmoothRadial.shrinkTimeFactor_one (a : ℝ) : shrinkTimeFactor a 1 = a := by
  simp only [shrinkTimeFactor, Real.smoothTransition.one, mul_one]
  ring

private theorem Smale.SmoothRadial.contDiff_shrinkTimeFactor (a : ℝ) :
    ContDiff ℝ ∞ (shrinkTimeFactor a) :=
  contDiff_const.add (contDiff_const.mul (Real.smoothTransition.contDiff (n := ⊤)))

private def Degree.DiskShrinking.scale (R a s : ℝ) : ℝ :=
  a + (1 - a) * Real.smoothTransition ((s - 1) / (R ^ 2 - 1))

private theorem Degree.DiskShrinking.contDiff_scale (R a : ℝ) : ContDiff ℝ ∞ (scale R a) :=
  contDiff_const.add
    (contDiff_const.mul
      ((Real.smoothTransition.contDiff (n := ⊤)).comp
        ((contDiff_id.sub contDiff_const).div_const _)))

private theorem Degree.DiskShrinking.scale_pos {a : ℝ} (ha : 0 < a) (ha₁ : a ≤ 1) (R s : ℝ) :
    0 < scale R a s :=
  add_pos_of_pos_of_nonneg ha (mul_nonneg (sub_nonneg.mpr ha₁) (Real.smoothTransition.nonneg _))

private theorem Degree.DiskShrinking.scale_monotone {R a : ℝ} (hR : 1 < R) (ha₁ : a ≤ 1) :
    Monotone (scale R a) := by
  have hden : 0 < R ^ 2 - 1 := by nlinarith
  intro s t hst
  exact
    add_le_add_right
      (mul_le_mul_of_nonneg_left
        (Real.smoothTransition.monotone
          (div_le_div_of_nonneg_right (sub_le_sub_right hst 1) hden.le))
        (sub_nonneg.mpr ha₁))
      a

private theorem Degree.DiskShrinking.scale_inner {R : ℝ} (hR : 1 < R) (a : ℝ) {s : ℝ} (hs : s ≤ 1) :
    scale R a s = a := by
  have hden : 0 < R ^ 2 - 1 := by nlinarith
  rw [scale,
    Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hs) hden.le)]
  simp only [MulZeroClass.mul_zero, add_zero]

private theorem
    Degree.DiskShrinking.scale_outer {R : ℝ} (hR : 1 < R) (a : ℝ) {s : ℝ} (hs : R ^ 2 ≤ s) :
    scale R a s = 1 := by
  have hden : 0 < R ^ 2 - 1 := by nlinarith
  rw [scale, Real.smoothTransition.one_of_one_le ((le_div_iff₀ hden).mpr (by linarith))]
  ring

private theorem Degree.DiskShrinking.scale_one (R s : ℝ) : scale R 1 s = 1 := by
  simp only [scale, sub_self, MulZeroClass.zero_mul, add_zero]

private def Degree.DiskShrinking.family {N : Type*} [NormedAddCommGroup N] [InnerProductSpace ℝ N]
    (R a : ℝ) (p : ℝ × N) : N :=
  Smale.SmoothRadial.radialMap (scale R (Smale.SmoothRadial.shrinkTimeFactor a p.1)) p.2

private theorem Degree.DiskShrinking.contMDiff_family {N : Type*} [NormedAddCommGroup N]
    [InnerProductSpace ℝ N] (R a : ℝ) :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, N)) 𝓘(ℝ, N) ∞ (family (N := N) R a) := by
  have ht :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, N)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × N => Smale.SmoothRadial.shrinkTimeFactor a p.1) :=
    (Smale.SmoothRadial.contDiff_shrinkTimeFactor a).contMDiff.comp contMDiff_fst
  have hn : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, N)) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × N => ‖p.2‖ ^ 2) :=
    (show ContDiff ℝ ∞ (fun x : N => ‖x‖ ^ 2) from contDiff_id.norm_sq ℝ).contMDiff.comp
      contMDiff_snd
  have hz :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, N)) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × N => (‖p.2‖ ^ 2 - 1) / (R ^ 2 - 1)) :=
    by
    simpa only [div_eq_mul_inv, Pi.mul_def, Pi.sub_def] using
      (hn.sub contMDiff_const).mul (contMDiff_const (c := (R ^ 2 - 1)⁻¹))
  exact
    (ht.add
          ((contMDiff_const.sub ht).mul
            ((Real.smoothTransition.contDiff (n := ⊤)).contMDiff.comp hz))).smul
      contMDiff_snd

private theorem Degree.DiskShrinking.family_zero {N : Type*} [NormedAddCommGroup N]
    [InnerProductSpace ℝ N] (R a : ℝ) (x : N) : family R a (0, x) = x := by
  simp only [family, Smale.SmoothRadial.shrinkTimeFactor_zero, Smale.SmoothRadial.radialMap,
    scale_one, one_smul]

private theorem Degree.DiskShrinking.family_slices {N : Type*} [NormedAddCommGroup N]
    [InnerProductSpace ℝ N] [FiniteDimensional ℝ N] {R a : ℝ} (hR : 1 < R) (ha : 0 < a)
    (ha₁ : a ≤ 1) (t : ℝ) :
    ∃ D : Diffeomorph 𝓘(ℝ, N) 𝓘(ℝ, N) N N ∞, ∀ x, D x = family R a (t, x) := by
  have ht := Smale.SmoothRadial.shrinkTimeFactor_bounds ha₁ t
  exact
    ⟨Smale.SmoothRadial.diffeomorph (contDiff_scale R _) (scale_pos (ha.trans_le ht.1) ht.2 R)
        (scale_monotone hR ht.2) (zero_lt_one.trans hR) (fun _ hs => scale_outer hR _ hs),
      fun _ => rfl⟩

private theorem Degree.DiskShrinking.family_outer {N : Type*} [NormedAddCommGroup N]
    [InnerProductSpace ℝ N] {R : ℝ} (hR : 1 < R) (a t : ℝ) {x : N}
    (hx : R ≤ ‖x‖) : family R a (t, x) = x := by
  rw [family, Smale.SmoothRadial.radialMap,
    scale_outer hR _ ((sq_le_sq₀ (zero_lt_one.trans hR).le (norm_nonneg x)).mpr hx), one_smul]

private theorem Degree.DiskShrinking.family_one_inner {N : Type*} [NormedAddCommGroup N]
    [InnerProductSpace ℝ N] {R : ℝ} (hR : 1 < R) (a : ℝ) {x : N}
    (hx : ‖x‖ ≤ 1) : family R a (1, x) = a • x := by
  rw [family, Smale.SmoothRadial.radialMap, Smale.SmoothRadial.shrinkTimeFactor_one,
    scale_inner hR a (by nlinarith [norm_nonneg x])]

private theorem Degree.DiskShrinking.family_origin {N : Type*} [NormedAddCommGroup N]
    [InnerProductSpace ℝ N] (R a t : ℝ) : family R a (t, (0 : N)) = 0 := by
  simp only [family, Smale.SmoothRadial.radialMap, smul_zero]

private theorem
    Degree.DiskShrinking.exists_larger_closedBall_subset {D : Type*} [NormedAddCommGroup D]
    [InnerProductSpace ℝ D] [FiniteDimensional ℝ D] {U : Set D} (hU : IsOpen U)
    (hunit : Metric.closedBall (0 : D) 1 ⊆ U) :
    ∃ R : ℝ, 1 < R ∧ Metric.closedBall (0 : D) R ⊆ U := by
  let T : Set ℝ := {r | ∀ x ∈ Metric.closedBall (0 : D) 1, r • x ∈ U}
  have hT : IsOpen T :=
    Smale.MorsePerturbation.isOpen_forall_mem_compact (ProperSpace.isCompact_closedBall (0 : D) 1)
      (hU.preimage (continuous_fst.smul continuous_snd))
  have h1 : (1 : ℝ) ∈ T := by
    intro x hx
    simpa only [one_smul] using hunit hx
  obtain ⟨δ, hδ, hδT⟩ := Metric.mem_nhds_iff.mp (hT.mem_nhds h1)
  let R : ℝ := 1 + δ / 2
  have hR : 1 < R := by dsimp [R]; linarith
  have hRpos : 0 < R := zero_lt_one.trans hR
  have hRT : R ∈ T :=
    hδT
      (by
        rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (by dsimp [R]; linarith)]
        dsimp [R]
        linarith)
  refine ⟨R, hR, ?_⟩
  intro x hx
  have hnorm : ‖R⁻¹ • x‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hRpos)]
    exact
      (inv_mul_le_iff₀ hRpos).mpr (by simpa only [mul_one] using mem_closedBall_zero_iff.mp hx)
  have hh := hRT (R⁻¹ • x) (mem_closedBall_zero_iff.mpr hnorm)
  simpa only [smul_inv_smul₀ hRpos.ne'] using hh

private theorem
    Degree.DiskShrinking.exists_disk_ellipsoid_in_open {D Z : Type*} [NormedAddCommGroup D]
    [InnerProductSpace ℝ D] [FiniteDimensional ℝ D] [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
    [FiniteDimensional ℝ Z] {U : Set (D × Z)} (hU : IsOpen U)
    (hzero : Metric.closedBall (0 : D) 1 ×ˢ {(0 : Z)} ⊆ U) :
    ∃ R : ℝ,
      1 < R ∧
        ∃ L : WithLp 2 (D × Z) ≃L[ℝ] D × Z,
          (∀ x : D, L (WithLp.toLp 2 (x, (0 : Z))) = (x, 0)) ∧
            Set.MapsTo L (Metric.closedBall 0 R) U := by
  obtain ⟨A, B, hA, hB, hKA, h0B, hAB⟩ :=
    generalized_tube_lemma (ProperSpace.isCompact_closedBall (0 : D) 1)
      (isCompact_singleton (x := (0 : Z))) hU hzero
  obtain ⟨R, hR, hRA⟩ := exists_larger_closedBall_subset hA hKA
  obtain ⟨ε, hε, hεB⟩ :=
    Metric.nhds_basis_closedBall.mem_iff.mp (hB.mem_nhds (h0B (Set.mem_singleton (0 : Z))))
  have hRpos : 0 < R := zero_lt_one.trans hR
  let δ : ℝ := ε / R
  have hδ : 0 < δ := div_pos hε hRpos
  let T : Z ≃L[ℝ] Z := (LinearEquiv.smulOfNeZero ℝ Z δ hδ.ne').toContinuousLinearEquiv
  let L : WithLp 2 (D × Z) ≃L[ℝ] D × Z :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ D Z).trans
      ((ContinuousLinearEquiv.refl ℝ D).prodCongr T)
  have hL (p : WithLp 2 (D × Z)) : L p = (p.fst, δ • p.snd) := rfl
  refine ⟨R, hR, L, ?_, ?_⟩
  · intro x
    rw [hL]
    change (x, δ • (0 : Z)) = (x, 0)
    rw [smul_zero]
  · intro p hp
    rw [hL]
    apply hAB
    refine
      ⟨hRA
          (mem_closedBall_zero_iff.mpr
            ((WithLp.norm_fst_le D p).trans (mem_closedBall_zero_iff.mp hp))),
        hεB ?_⟩
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hδ]
    calc
      δ * ‖p.snd‖ ≤ δ * R :=
        mul_le_mul_of_nonneg_left ((WithLp.norm_snd_le D p).trans (mem_closedBall_zero_iff.mp hp))
          hδ.le
      _ = ε := div_mul_cancel₀ ε hRpos.ne'

private theorem Smale.SupportedDiffeomorph.exists_supported_isotopy_extension {E F H H' X Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
    [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H' Y] [T2Space Y]
    (Φ : PartialDiffeomorph I J X Y ∞) {A : ℝ × X → X} (hA : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ A)
    (hA₀ : ∀ x, A (0, x) = x) (hdiff : ∀ t, ∃ D : Diffeomorph I I X X ∞, ∀ x, D x = A (t, x))
    {K : Set X} (hK : IsCompact K) (hKsource : K ⊆ Φ.source)
    (hfix : ∀ t x, x ∉ K → A (t, x) = x) :
    ∃ (B : ℝ × Y → Y) (L : Set Y),
      IsCompact L ∧
        L ⊆ Φ.target ∧
          ContMDiff (𝓘(ℝ, ℝ).prod J) J ∞ B ∧
            (∀ y, B (0, y) = y) ∧
              (∀ t, ∃ D : Diffeomorph J J Y Y ∞, ∀ y, D y = B (t, y)) ∧
                (∀ t y, y ∉ L → B (t, y) = y) ∧
                  (∀ t, Set.MapsTo (fun x => A (t, x)) Φ.source Φ.source) ∧
                    ∀ t x, x ∈ Φ.source → B (t, Φ x) = Φ (A (t, x)) := by
  have hsource : ∀ t, Set.MapsTo (fun x => A (t, x)) Φ.source Φ.source := by
    intro t
    obtain ⟨D, hD⟩ := hdiff t
    have hDfix : ∀ x ∉ K, D x = x := fun x hx => (hD x).trans (hfix t x hx)
    have heq : (fun x => A (t, x)) = D := funext (fun x => (hD x).symm)
    rw [heq]
    exact mapsTo_source Φ D.toEquiv hKsource hDfix
  let B : ℝ × Y → Y := fun q => extendMap Φ (fun x => A (q.1, x)) q.2
  refine
    ⟨B, Φ '' K, hK.image_of_continuousOn (Φ.contMDiffOn_toFun.continuousOn.mono hKsource), ?_,
      contMDiff_extendFamily Φ hA hK hKsource hfix hsource, ?_, ?_, ?_, hsource, ?_⟩
  · rintro y ⟨x, hx, rfl⟩
    exact Φ.map_source' (hKsource hx)
  · intro y
    have heq : (fun x => A (0, x)) = id := funext hA₀
    change extendMap Φ (fun x => A (0, x)) y = y
    rw [heq]
    exact extendMap_id Φ y
  · intro t
    obtain ⟨D, hD⟩ := hdiff t
    have hDfix : ∀ x ∉ K, D x = x := fun x hx => (hD x).trans (hfix t x hx)
    refine ⟨extension Φ D hK hKsource hDfix, ?_⟩
    intro y
    exact congrArg (fun f : X → X => extendMap Φ f y) (funext hD)
  · intro t y hy
    exact extendMap_eq_of_notMem_image Φ (hfix t) hy
  · intro t x hx
    exact extendMap_chart Φ (fun z => A (t, z)) hx

private theorem Degree.DiskShrinking.exists_chart_disk_shrinking {D Z E H M : Type*}
    [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D] [NormedAddCommGroup Z]
    [InnerProductSpace ℝ Z] [FiniteDimensional ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] (Φ : PartialDiffeomorph 𝓘(ℝ, D × Z) I (D × Z) M ∞)
    (hzero : Metric.closedBall (0 : D) 1 ×ˢ {(0 : Z)} ⊆ Φ.source) {a : ℝ} (ha : 0 < a)
    (ha₁ : a ≤ 1) :
    ∃ K : Set M,
      IsCompact K ∧
        K ⊆ Φ.target ∧
          ∃ P : Diffeomorph I I M M ∞,
            Nonempty (Smale.SupportedDiffeomorph.SupportedRelativeIsotopy P K {Φ (0, 0)}) ∧
              ∀ x : D, ‖x‖ ≤ 1 → P (Φ (x, 0)) = Φ (a • x, 0) := by
  obtain ⟨R, hR, L, hLzero, hLsource⟩ := exists_disk_ellipsoid_in_open Φ.open_source hzero
  let Ψ := L.toDiffeomorph.toPartialDiffeomorph.trans Φ
  have hsource : Metric.closedBall (0 : WithLp 2 (D × Z)) R ⊆ Ψ.source := by
    intro z hz
    exact ⟨Set.mem_univ z, hLsource hz⟩
  have htarget : Ψ.target ⊆ Φ.target := fun _ hy => hy.1
  have hΨ (x : D) : Ψ (WithLp.toLp 2 (x, (0 : Z))) = Φ (x, 0) := by
    change Φ (L (WithLp.toLp 2 (x, (0 : Z)))) = _
    rw [hLzero]
  have hΨ0 : Ψ (0 : WithLp 2 (D × Z)) = Φ (0, 0) := hΨ 0
  have h0source : (0 : WithLp 2 (D × Z)) ∈ Ψ.source :=
    hsource (Metric.mem_closedBall_self (zero_le_one.trans hR.le))
  have hfix : ∀ t (z : WithLp 2 (D × Z)), z ∉ Metric.closedBall 0 R → family R a (t, z) = z := by
    intro t z hz
    exact family_outer hR a t (le_of_not_ge (fun hn => hz (mem_closedBall_zero_iff.mpr hn)))
  obtain ⟨B, K, hK, hKt, hB, hB0, hBt, hBfix, -, hchart⟩ :=
    Smale.SupportedDiffeomorph.exists_supported_isotopy_extension Ψ (contMDiff_family R a)
      (family_zero R a) (family_slices hR ha ha₁) (ProperSpace.isCompact_closedBall 0 R) hsource
      hfix
  obtain ⟨P, hP⟩ := hBt 1
  refine
    ⟨K, hK, hKt.trans htarget, P,
      ⟨{  family := B
          smooth := hB
          zero := hB0
          one := fun y => (hP y).symm
          slices := hBt
          fixedOutside := hBfix
          fixedOn := ?_ }⟩, ?_⟩
  · intro t y hy
    rcases Set.mem_singleton_iff.mp hy with rfl
    rw [← hΨ0, hchart t 0 h0source, family_origin]
  · intro x hx
    have hn : ‖WithLp.toLp 2 (x, (0 : Z))‖ ≤ 1 := by simpa only [WithLp.norm_toLp_fst] using hx
    have hs : WithLp.toLp 2 (x, (0 : Z)) ∈ Ψ.source :=
      hsource (mem_closedBall_zero_iff.mpr (hn.trans hR.le))
    have hsmul : a • WithLp.toLp 2 (x, (0 : Z)) = WithLp.toLp 2 (a • x, (0 : Z)) := by
      change WithLp.toLp 2 (a • x, a • (0 : Z)) = _
      rw [smul_zero]
    rw [← hΨ x, hP, hchart 1 _ hs, family_one_inner hR a hn, hsmul, hΨ]

private theorem
    Smale.SupportedDiffeomorph.IsotopicToIdentity.symm {F H M : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace H] {J : ModelWithCorners ℝ F H} [TopologicalSpace M]
    [ChartedSpace H M] {e : Diffeomorph J J M M ∞}
    (he : Smale.SupportedDiffeomorph.IsotopicToIdentity e) :
    Smale.SupportedDiffeomorph.IsotopicToIdentity e.symm := by
  obtain ⟨A, hA, hA₀, hA₁, hdiff⟩ := he
  let B : ℝ × M → M := fun p => e.symm (A (1 - p.1, p.2))
  have hrev : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun t : ℝ => 1 - t) :=
    (contDiff_const.sub contDiff_id).contMDiff
  have hB : ContMDiff (𝓘(ℝ, ℝ).prod J) J ∞ B :=
    e.symm.contMDiff.comp (hA.comp ((hrev.comp contMDiff_fst).prodMk contMDiff_snd))
  refine ⟨B, hB, ?_, ?_, ?_⟩
  · intro x
    change e.symm (A (1 - 0, x)) = x
    rw [sub_zero, hA₁, e.symm_apply_apply]
  · intro x
    change e.symm (A (1 - 1, x)) = e.symm x
    rw [sub_self, hA₀]
  · intro t
    obtain ⟨d, hd⟩ := hdiff (1 - t)
    refine ⟨d.trans e.symm, ?_⟩
    intro x
    change e.symm (A (1 - t, x)) = e.symm (d x)
    rw [hd]

private theorem Degree.SupportedGerms.exists_disk_chart_isotopy {A B E H M ι κ : Type*}
    [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A] [NormedAddCommGroup B]
    [InnerProductSpace ℝ B] [FiniteDimensional ℝ B] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {J : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [Finite ι] [Finite κ] [Nontrivial κ] (b : Module.Basis ι ℝ B) (i : ι)
    (basis : Module.Basis κ ℝ (A × B)) (Φ Ψ : PartialDiffeomorph 𝓘(ℝ, A × B) J (A × B) M ∞)
    (hΦ : Metric.closedBall (0 : A) 1 ×ˢ {(0 : B)} ⊆ Φ.source)
    (hΨ : Metric.closedBall (0 : A) 1 ×ˢ {(0 : B)} ⊆ Ψ.source) (hcenter : Φ 0 = Ψ 0) :
    ∃ D : Diffeomorph J J M M ∞,
      Smale.SupportedDiffeomorph.IsotopicToIdentity D ∧
        ∀ x ∈ Metric.closedBall (0 : A) 1, D (Φ (x, 0)) = Ψ (x, 0) := by
  classical
  let := Fintype.ofFinite ι
  let := Fintype.ofFinite κ
  have hz : (0 : A × B) ∈ Metric.closedBall (0 : A) 1 ×ˢ {(0 : B)} :=
    ⟨Metric.mem_closedBall_self zero_le_one, rfl⟩
  obtain ⟨D, K, -, -, ⟨HD⟩, hgerm⟩ :=
    exists_native_disk_germ_alignment b i basis Φ Ψ (hΦ hz) (hΨ hz) hcenter
  obtain ⟨ε, hε, hεeq⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hgerm
  let a : ℝ := Min.min 1 ε
  have ha : 0 < a := lt_min zero_lt_one hε
  have ha1 : a ≤ 1 := min_le_left _ _
  obtain ⟨KΦ, -, -, P, ⟨HP⟩, hP⟩ := Degree.DiskShrinking.exists_chart_disk_shrinking Φ hΦ ha ha1
  obtain ⟨KΨ, -, -, Q, ⟨HQ⟩, hQ⟩ := Degree.DiskShrinking.exists_chart_disk_shrinking Ψ hΨ ha ha1
  refine
    ⟨(P.trans D).trans Q.symm,
      (HP.isotopicToIdentity.trans HD.isotopicToIdentity).trans HQ.isotopicToIdentity.symm, ?_⟩
  intro x hx
  have hn : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx
  have hsmall : a • x ∈ Metric.closedBall (0 : A) ε := by
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos ha]
    exact (mul_le_of_le_one_right ha.le hn).trans (min_le_right _ _)
  have heq : D (Φ (a • x, 0)) = Ψ (a • x, 0) := hεeq hsmall
  change Q.symm (D (P (Φ (x, 0)))) = Ψ (x, 0)
  rw [hP x hn, heq, ← hQ x hn, Q.symm_apply_apply]

private theorem Degree.DiskShrinking.exists_embedded_disk_isotopy_of_same_center {D E M : Type*}
    [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f g : D → M}
    (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f) (hg : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ g)
    (hfi : Set.InjOn f (Metric.closedBall (0 : D) 1))
    (hgi : Set.InjOn g (Metric.closedBall (0 : D) 1))
    (hfd : ∀ x ∈ Metric.closedBall (0 : D) 1, Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x))
    (hgd : ∀ x ∈ Metric.closedBall (0 : D) 1, Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) g x))
    (n : ℕ) (hn : 0 < n) (hdim : Module.finrank ℝ D + n = Module.finrank ℝ E)
    (hE : 2 ≤ Module.finrank ℝ E) (hcenter : f 0 = g 0) :
    ∃ P : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞,
      Smale.SupportedDiffeomorph.IsotopicToIdentity P ∧
        ∀ x ∈ Metric.closedBall (0 : D) 1, P (f x) = g x := by
  classical
  let B := EuclideanSpace ℝ (Fin n)
  obtain ⟨ε, hε, Φ, hΦprod, hΦzero, -⟩ :=
    Smale.exists_tubularNeighborhood_in_open_of_embedded_closedBall hf hfi hfd n hdim isOpen_univ
      (Set.mapsTo_univ _ _)
  obtain ⟨δ, hδ, Ψ, hΨprod, hΨzero, -⟩ :=
    Smale.exists_tubularNeighborhood_in_open_of_embedded_closedBall hg hgi hgd n hdim isOpen_univ
      (Set.mapsTo_univ _ _)
  have hΦ : Metric.closedBall (0 : D) 1 ×ˢ {(0 : B)} ⊆ Φ.source := by
    rintro ⟨x, z⟩ ⟨hx, hz⟩
    rcases Set.mem_singleton_iff.mp hz with rfl
    exact hΦprod ⟨hx, Metric.mem_closedBall_self hε.le⟩
  have hΨ : Metric.closedBall (0 : D) 1 ×ˢ {(0 : B)} ⊆ Ψ.source := by
    rintro ⟨x, z⟩ ⟨hx, hz⟩
    rcases Set.mem_singleton_iff.mp hz with rfl
    exact hΨprod ⟨hx, Metric.mem_closedBall_self hδ.le⟩
  have hcenter' : Φ 0 = Ψ 0 := by
    change Φ (0, 0) = Ψ (0, 0)
    rw [hΦzero 0 (Metric.mem_closedBall_self zero_le_one),
      hΨzero 0 (Metric.mem_closedBall_self zero_le_one), hcenter]
  have hB : 0 < Module.finrank ℝ B := by simpa only [B, finrank_euclideanSpace_fin] using hn
  have hDB : 2 ≤ Module.finrank ℝ (D × B) := by
    simpa only [Module.finrank_prod, B, finrank_euclideanSpace_fin, hdim] using hE
  let _ : Nontrivial (Fin (Module.finrank ℝ (D × B))) := Fin.nontrivial_iff_two_le.mpr hDB
  obtain ⟨P, hP, hformula⟩ :=
    Degree.SupportedGerms.exists_disk_chart_isotopy (Module.finBasis ℝ B) ⟨0, hB⟩
      (Module.finBasis ℝ (D × B)) Φ Ψ hΦ hΨ hcenter'
  refine ⟨P, hP, ?_⟩
  intro x hx
  rw [← hΦzero x hx, hformula x hx, hΨzero x hx]

private theorem Smale.SupportedDiffeomorph.exists_supported_pointMoving {E F H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace H] {J : ModelWithCorners ℝ F H} [TopologicalSpace M]
    [ChartedSpace H M] [T2Space M] (Φ : PartialDiffeomorph 𝓘(ℝ, E) J E M ∞) {x : E}
    (hx : x ∈ Φ.source) :
    ∃ ε : ℝ,
      0 < ε ∧
        Metric.ball x ε ⊆ Φ.source ∧
          ∀ y ∈ Metric.ball x ε,
            ∃ A : ℝ × M → M,
              ContMDiff (𝓘(ℝ, ℝ).prod J) J ∞ A ∧
                (∀ z, A (0, z) = z) ∧
                  (∀ t, ∃ d : Diffeomorph J J M M ∞, ∀ z, A (t, z) = d z) ∧
                    (∀ t z, z ∉ Φ.target → A (t, z) = z) ∧ A (1, Φ x) = Φ y := by
  obtain ⟨β, hβsupport, hβcompact, hβsmooth, -, hβx⟩ :=
    exists_contDiff_tsupport_subset (n := ⊤) (Φ.open_source.mem_nhds hx)
  obtain ⟨δ, hδ, hmove⟩ := exists_small_supported_bump_isotopy Φ hβsmooth hβcompact hβsupport
  obtain ⟨ρ, hρ, hρsource⟩ := Metric.mem_nhds_iff.mp (Φ.open_source.mem_nhds hx)
  refine ⟨Min.min δ ρ, lt_min hδ hρ, ?_, ?_⟩
  · exact (Metric.ball_subset_ball (min_le_right _ _)).trans hρsource
  · intro y hy
    have hnear : ‖y - x‖ < δ := by
      simpa only [dist_eq_norm] using
        (show Dist.dist y x < Min.min δ ρ from hy).trans_le (min_le_left _ _)
    obtain ⟨A, hA, hzero, hdiff, hfix, hend⟩ := hmove (y - x) hnear
    refine ⟨A, hA, hzero, hdiff, ?_, ?_⟩
    · intro t z hz
      apply hfix t z
      rintro ⟨q, hq, rfl⟩
      exact hz (Φ.map_source' (hβsupport hq))
    · have hterminal := hend x hx
      rw [hβx, one_smul] at hterminal
      have hxy : x + (y - x) = y := by abel
      exact hterminal.trans (congrArg Φ hxy)

private theorem
    Smale.SupportedDiffeomorph.exists_open_pointMoving {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
    [J.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold J ∞ M] [T2Space M]
    {U : Set M} (hU : IsOpen U) {x : M} (hx : x ∈ U) :
    ∃ V : Set M,
      IsOpen V ∧
        x ∈ V ∧ V ⊆ U ∧ ∀ y ∈ V, ∃ d : Diffeomorph J J M M ∞, d x = y ∧ ∀ z ∉ U, d z = z := by
  let c := NoExotic.modelChartPartialDiffeomorph (I := J) x
  let Φ := Smale.PartialChart.restrictTarget c.symm hU
  have hxc : x ∈ c.source := mem_extChartAt_source x
  have hcx : c.symm (c x) = x := c.left_inv' hxc
  have hxΦ : c x ∈ Φ.source := by
    refine ⟨c.map_source' hxc, ?_⟩
    change c.symm (c x) ∈ U
    rw [hcx]
    exact hx
  have hΦx : Φ (c x) = x := hcx
  obtain ⟨ε, hε, hball, hmove⟩ := exists_supported_pointMoving Φ hxΦ
  refine
    ⟨Φ '' Metric.ball (c x) ε,
      Φ.toOpenPartialHomeomorph.isOpen_image_of_subset_source Metric.isOpen_ball hball,
      ⟨c x, Metric.mem_ball_self hε, hΦx⟩, ?_, ?_⟩
  · rintro _ ⟨v, hv, rfl⟩
    exact (Φ.map_source' (hball hv)).2
  · rintro _ ⟨v, hv, rfl⟩
    obtain ⟨A, _, _, hdiff, hfix, hend⟩ := hmove v hv
    obtain ⟨d, hd⟩ := hdiff 1
    refine ⟨d, ?_, ?_⟩
    · rw [hΦx] at hend
      exact (hd x).symm.trans hend
    · intro z hz
      exact (hd z).symm.trans (hfix 1 z (fun h => hz h.2))

private theorem MorseCancel.exists_open_isotopic_pointMoving {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
    [J.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold J ∞ M] [T2Space M]
    {U : Set M} (hU : IsOpen U) {x : M} (hx : x ∈ U) :
    ∃ V : Set M,
      IsOpen V ∧
        x ∈ V ∧
          V ⊆ U ∧
            ∀ y ∈ V,
              ∃ d : Diffeomorph J J M M ∞,
                Smale.SupportedDiffeomorph.IsotopicToIdentity d ∧ d x = y ∧ ∀ z ∉ U, d z = z := by
  let c := NoExotic.modelChartPartialDiffeomorph (I := J) x
  let Φ := Smale.PartialChart.restrictTarget c.symm hU
  have hxc : x ∈ c.source := mem_extChartAt_source x
  have hcx : c.symm (c x) = x := c.left_inv' hxc
  have hxΦ : c x ∈ Φ.source := by
    refine ⟨c.map_source' hxc, ?_⟩
    change c.symm (c x) ∈ U
    rw [hcx]
    exact hx
  have hΦx : Φ (c x) = x := hcx
  obtain ⟨ε, hε, hball, hmove⟩ := Smale.SupportedDiffeomorph.exists_supported_pointMoving Φ hxΦ
  refine
    ⟨Φ '' Metric.ball (c x) ε,
      Φ.toOpenPartialHomeomorph.isOpen_image_of_subset_source Metric.isOpen_ball hball,
      ⟨c x, Metric.mem_ball_self hε, hΦx⟩, ?_, ?_⟩
  · rintro _ ⟨v, hv, rfl⟩
    exact (Φ.map_source' (hball hv)).2
  · rintro _ ⟨v, hv, rfl⟩
    obtain ⟨A, hA, hzero, hdiff, hfix, hend⟩ := hmove v hv
    obtain ⟨d, hd⟩ := hdiff 1
    refine ⟨d, ⟨A, hA, hzero, hd, hdiff⟩, ?_, ?_⟩
    · rw [hΦx] at hend
      exact (hd x).symm.trans hend
    · intro z hz
      exact (hd z).symm.trans (hfix 1 z (fun h => hz h.2))

private theorem
    MorseCancel.exists_isotopic_two_points_in_dense {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
    [J.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold J ∞ M] [T2Space M]
    {B : Set M} (hB : Dense B) {x y : M} (hxy : x ≠ y) :
    ∃ d : Diffeomorph J J M M ∞,
      Smale.SupportedDiffeomorph.IsotopicToIdentity d ∧ d x ∈ B ∧ d y ∈ B := by
  obtain ⟨U, V, hU, hV, hx, hy, hdisj⟩ := t2_separation hxy
  obtain ⟨U', hU', hx', hU'U, hmoveU⟩ := exists_open_isotopic_pointMoving (J := J) hU hx
  obtain ⟨V', hV', hy', hV'V, hmoveV⟩ := exists_open_isotopic_pointMoving (J := J) hV hy
  obtain ⟨x', hx'B, hx'U⟩ := hB.exists_mem_open hU' ⟨x, hx'⟩
  obtain ⟨y', hy'B, hy'V⟩ := hB.exists_mem_open hV' ⟨y, hy'⟩
  obtain ⟨d, hd, hdx, hdfix⟩ := hmoveU x' hx'U
  obtain ⟨e, he, hey, hefix⟩ := hmoveV y' hy'V
  have hyU : y ∉ U := fun h => Set.disjoint_left.mp hdisj h hy
  have hxV : x' ∉ V := fun h => Set.disjoint_left.mp hdisj (hU'U hx'U) h
  refine ⟨d.trans e, hd.trans he, ?_, ?_⟩
  · change e (d x) ∈ B
    rw [hdx, hefix x' hxV]
    exact hx'B
  · change e (d y) ∈ B
    rw [hdfix y hyU, hey]
    exact hy'B

private theorem MorseCancel.isotopicToIdentity_joined {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
     [TopologicalSpace M] [ChartedSpace H M]
    {d : Diffeomorph J J M M ∞} (hd : Smale.SupportedDiffeomorph.IsotopicToIdentity d) (x : M) :
    Joined x (d x) := by
  obtain ⟨A, hA, hzero, hone, -⟩ := hd
  exact
    ⟨{  toFun := fun t => A ((t : ℝ), x)
        continuous_toFun := hA.continuous.comp (continuous_subtype_val.prodMk continuous_const)
        source' := hzero x
        target' := hone x }⟩

private def MorseCancel.isotopicPointOrbit {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] (J : ModelWithCorners ℝ E H)
    (U : Set M) (x : M) : Set M :=
  {y |
    y ∈ U ∧
      ∃ d : Diffeomorph J J M M ∞,
        Smale.SupportedDiffeomorph.IsotopicToIdentity d ∧ d x = y ∧ ∀ z ∉ U, d z = z}

private theorem MorseCancel.isOpen_isotopicPointOrbit {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
    [J.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold J ∞ M] [T2Space M]
    {U : Set M} (hU : IsOpen U) (x : M) : IsOpen (isotopicPointOrbit J U x) := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨hyU, d, hd, hdx, hdfix⟩
  obtain ⟨V, hV, hyV, hVU, hmove⟩ := exists_open_isotopic_pointMoving (J := J) hU hyU
  apply Filter.mem_of_superset (hV.mem_nhds hyV)
  intro z hz
  obtain ⟨e, he, hey, hefix⟩ := hmove z hz
  refine ⟨hVU hz, d.trans e, hd.trans he, ?_, ?_⟩
  · change e (d x) = z
    rw [hdx, hey]
  · intro w hw
    change e (d w) = w
    rw [hdfix w hw, hefix w hw]

private theorem MorseCancel.isOpen_sdiff_isotopicPointOrbit {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
    [J.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold J ∞ M] [T2Space M]
    {U : Set M} (hU : IsOpen U) (x : M) : IsOpen (U \ isotopicPointOrbit J U x) := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨hyU, hyOrbit⟩
  obtain ⟨V, hV, hyV, hVU, hmove⟩ := exists_open_isotopic_pointMoving (J := J) hU hyU
  apply Filter.mem_of_superset (hV.mem_nhds hyV)
  intro z hz
  refine ⟨hVU hz, ?_⟩
  rintro ⟨_, d, hd, hdx, hdfix⟩
  obtain ⟨e, he, hey, hefix⟩ := hmove z hz
  apply hyOrbit
  refine ⟨hyU, d.trans e.symm, hd.trans he.symm, ?_, ?_⟩
  · change e.symm (d x) = y
    rw [hdx, ← hey, e.symm_apply_apply]
  · intro w hw
    change e.symm (d w) = w
    rw [hdfix w hw]
    exact Smale.SupportedDiffeomorph.inverse_fixed_outside e.toEquiv hefix w hw

private theorem MorseCancel.exists_isotopic_pointMoving_of_preconnected {E H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
    {J : ModelWithCorners ℝ E H} [J.Boundaryless] [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold J ∞ M] [T2Space M] {U A : Set M} (hU : IsOpen U) (hA : IsPreconnected A)
    (hAU : A ⊆ U) {x y : M} (hx : x ∈ A) (hy : y ∈ A) :
    ∃ d : Diffeomorph J J M M ∞,
      Smale.SupportedDiffeomorph.IsotopicToIdentity d ∧ d x = y ∧ ∀ z ∉ U, d z = z := by
  have hxOrbit : x ∈ isotopicPointOrbit J U x :=
    ⟨hAU hx, Diffeomorph.refl J M ∞, Smale.SupportedDiffeomorph.isotopicToIdentity_refl, rfl,
      fun _ _ => rfl⟩
  have hcover : A ⊆ isotopicPointOrbit J U x ∪ (U \ isotopicPointOrbit J U x) := by
    intro z hz
    by_cases hh : z ∈ isotopicPointOrbit J U x
    · exact Or.inl hh
    · exact Or.inr ⟨hAU hz, hh⟩
  have hdisjoint : Disjoint (isotopicPointOrbit J U x) (U \ isotopicPointOrbit J U x) := by
    rw [Set.disjoint_left]
    exact fun _ hz hw => hw.2 hz
  have hsub :=
    hA.subset_left_of_subset_union (isOpen_isotopicPointOrbit hU x)
      (isOpen_sdiff_isotopicPointOrbit hU x) hdisjoint hcover ⟨x, hx, hxOrbit⟩
  exact (hsub hy).2

private theorem
    MorseCancel.exists_isotopic_pointMoving_of_path {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
    [J.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold J ∞ M] [T2Space M]
    {U : Set M} (hU : IsOpen U) {x y : M} (γ : Path x y) (hγ : ∀ t, γ t ∈ U) :
    ∃ d : Diffeomorph J J M M ∞,
      Smale.SupportedDiffeomorph.IsotopicToIdentity d ∧ d x = y ∧ ∀ z ∉ U, d z = z := by
  apply
    exists_isotopic_pointMoving_of_preconnected (J := J) hU
      (isConnected_range γ.continuous).isPreconnected
      (show Set.range γ ⊆ U from by rintro _ ⟨t, rfl⟩; exact hγ t)
  · exact ⟨0, γ.source⟩
  · exact ⟨1, γ.target⟩

private def Smale.CurveImmersion.smoothTime (t : ℝ) : unitInterval :=
  Set.projIcc 0 1 zero_le_one (Real.smoothTransition t)

private theorem
    Smale.CurveImmersion.contMDiff_smoothTime : ContMDiff 𝓘(ℝ, ℝ) (𝓡∂ 1) ∞ smoothTime := by
  let : Fact ((0 : ℝ) < 1) := ⟨zero_lt_one⟩
  have hp : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡∂ 1) ∞ (Set.projIcc (0 : ℝ) 1 zero_le_one) (Set.Icc 0 1) :=
    contMDiffOn_projIcc
  have ht : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  apply contMDiffOn_univ.mp
  exact
    hp.comp ht.contMDiff.contMDiffOn
      (fun t _ => ⟨Real.smoothTransition.nonneg t, Real.smoothTransition.le_one t⟩)

private theorem Smale.CurveImmersion.smoothTime_zero : smoothTime 0 = 0 := by
  apply Subtype.ext
  simp [smoothTime]

private theorem Smale.CurveImmersion.smoothTime_one : smoothTime 1 = 1 := by
  apply Subtype.ext
  simp [smoothTime]

private theorem Smale.exists_smooth_connecting_curve {G H N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [J.Boundaryless]
    [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] {x y : N} (γ : Path x y) :
    ∃ f : C(ℝ, N), ContMDiff 𝓘(ℝ, ℝ) J ∞ f ∧ f 0 = x ∧ f 1 = y := by
  let Z := EuclideanSpace ℝ (Fin 0)
  let f₀ : C(Z, N) := ContinuousMap.const Z x
  let f₁ : C(Z, N) := ContinuousMap.const Z y
  let H : f₀.Homotopy f₁ :=
    { toFun := fun q => γ q.1
      continuous_toFun := γ.continuous.comp continuous_fst
      map_zero_left := fun _ => γ.source
      map_one_left := fun _ => γ.target }
  obtain ⟨H', hH', -, -⟩ :=
    ManifoldSmoothing.exists_smooth_homotopy_with_collars (I := 𝓘(ℝ, Z)) (J := J) contMDiff_const
      contMDiff_const H
  let f : ℝ → N := fun t => H' (CurveImmersion.smoothTime t, (0 : Z))
  have hf : ContMDiff 𝓘(ℝ, ℝ) J ∞ f :=
    hH'.comp (CurveImmersion.contMDiff_smoothTime.prodMk contMDiff_const)
  refine ⟨⟨f, hf.continuous⟩, hf, ?_, ?_⟩
  · change H' (CurveImmersion.smoothTime 0, (0 : Z)) = x
    rw [CurveImmersion.smoothTime_zero, H'.apply_zero]
    rfl
  · change H' (CurveImmersion.smoothTime 1, (0 : Z)) = y
    rw [CurveImmersion.smoothTime_one, H'.apply_one]
    rfl

private def
    Smale.SupportedDiffeomorph.pointOrbit {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] (J : ModelWithCorners ℝ E H)
    (U : Set M) (x : M) : Set M :=
  {y | y ∈ U ∧ ∃ d : Diffeomorph J J M M ∞, d x = y ∧ ∀ z ∉ U, d z = z}

private theorem Smale.SupportedDiffeomorph.isOpen_pointOrbit {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
    [J.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold J ∞ M] [T2Space M]
    {U : Set M} (hU : IsOpen U) (x : M) : IsOpen (pointOrbit J U x) := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨hyU, d, hd, hdfix⟩
  obtain ⟨V, hV, hyV, hVU, hmove⟩ := exists_open_pointMoving (J := J) hU hyU
  apply Filter.mem_of_superset (hV.mem_nhds hyV)
  intro z hz
  obtain ⟨e, he, hefix⟩ := hmove z hz
  refine ⟨hVU hz, d.trans e, ?_, ?_⟩
  · change e (d x) = z
    rw [hd, he]
  · intro w hw
    change e (d w) = w
    rw [hdfix w hw, hefix w hw]

private theorem
    Smale.SupportedDiffeomorph.isOpen_sdiff_pointOrbit {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
    [J.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold J ∞ M] [T2Space M]
    {U : Set M} (hU : IsOpen U) (x : M) : IsOpen (U \ pointOrbit J U x) := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨hyU, hyOrbit⟩
  obtain ⟨V, hV, hyV, hVU, hmove⟩ := exists_open_pointMoving (J := J) hU hyU
  apply Filter.mem_of_superset (hV.mem_nhds hyV)
  intro z hz
  refine ⟨hVU hz, ?_⟩
  rintro ⟨_, d, hd, hdfix⟩
  obtain ⟨e, he, hefix⟩ := hmove z hz
  apply hyOrbit
  refine ⟨hyU, d.trans e.symm, ?_, ?_⟩
  · change e.symm (d x) = y
    rw [hd, ← he]
    exact e.toEquiv.symm_apply_apply y
  · intro w hw
    change e.symm (d w) = w
    rw [hdfix w hw]
    exact inverse_fixed_outside e.toEquiv hefix w hw

private theorem Smale.SupportedDiffeomorph.exists_pointMoving_of_preconnected {E H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
    {J : ModelWithCorners ℝ E H} [J.Boundaryless] [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold J ∞ M] [T2Space M] {U S : Set M} (hU : IsOpen U) (hS : IsPreconnected S)
    (hSU : S ⊆ U) {x y : M} (hx : x ∈ S) (hy : y ∈ S) :
    ∃ d : Diffeomorph J J M M ∞, d x = y ∧ ∀ z ∉ U, d z = z := by
  have hxOrbit : x ∈ pointOrbit J U x := ⟨hSU hx, Diffeomorph.refl J M ∞, rfl, fun _ _ => rfl⟩
  have hcover : S ⊆ pointOrbit J U x ∪ (U \ pointOrbit J U x) := by
    intro z hz
    by_cases h : z ∈ pointOrbit J U x
    · exact Or.inl h
    · exact Or.inr ⟨hSU hz, h⟩
  have hdisjoint : Disjoint (pointOrbit J U x) (U \ pointOrbit J U x) := by
    rw [Set.disjoint_left]
    exact fun _ hz hw => hw.2 hz
  have hsub :=
    hS.subset_left_of_subset_union (isOpen_pointOrbit hU x) (isOpen_sdiff_pointOrbit hU x)
      hdisjoint hcover ⟨x, hx, hxOrbit⟩
  exact (hsub hy).2

private theorem Smale.SupportedDiffeomorph.exists_pointMoving_of_path {E H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
    {J : ModelWithCorners ℝ E H} [J.Boundaryless] [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold J ∞ M] [T2Space M] {U : Set M} (hU : IsOpen U) {x y : M} (γ : Path x y)
    (hγ : ∀ t, γ t ∈ U) : ∃ d : Diffeomorph J J M M ∞, d x = y ∧ ∀ z ∉ U, d z = z := by
  apply
    exists_pointMoving_of_preconnected (J := J) hU (isConnected_range γ.continuous).isPreconnected
      (show Set.range γ ⊆ U from by rintro _ ⟨t, rfl⟩; exact hγ t)
  · exact ⟨0, γ.source⟩
  · exact ⟨1, γ.target⟩

private theorem Smale.exists_smooth_path_avoiding_finite {G H N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
    [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N]
    {x y : N} (γ : Path x y) (hdim : 2 ≤ Module.finrank ℝ G) {S : Set N} (hS : S.Finite)
    (hx : x ∉ S) (hy : y ∉ S) : ∃ η : Path x y, ContMDiff (𝓡∂ 1) J ∞ η ∧ ∀ t, η t ∉ S := by
  let : Fintype S := hS.fintype
  let Z := EuclideanSpace ℝ (Fin 0)
  let : ChartedSpace Z S := ChartedSpace.ofDiscreteTopology
  let : IsManifold 𝓘(ℝ, Z) ∞ S := IsManifold.of_discreteTopology _
  let g : C(S, N) := ⟨Subtype.val, continuous_subtype_val⟩
  have hg : ContMDiff 𝓘(ℝ, Z) J ∞ g := contMDiff_of_discreteTopology
  have hrange : Set.range g = S := by ext z; simp [g]
  obtain ⟨f, hf, hf0, hf1⟩ := exists_smooth_connecting_curve (J := J) γ
  let fI : C(unitInterval, N) := ⟨fun t => f t, f.continuous.comp continuous_subtype_val⟩
  have hfI : ContMDiff (𝓡∂ 1) J ∞ fI := hf.comp contMDiff_subtypeVal_Icc
  have hdim' :
    Module.finrank ℝ (EuclideanSpace ℝ (Fin 1)) + Module.finrank ℝ Z < Module.finrank ℝ G := by
    simp only [Z, finrank_euclideanSpace_fin]
    omega
  have hfixed : ∀ t ∈ ({0, 1} : Set unitInterval), fI t ∉ Set.range g := by
    intro t ht
    rw [hrange]
    rcases ht with rfl | ht
    · change f 0 ∉ S
      rw [hf0]
      exact hx
    · have ht1 : t = 1 := ht
      subst t
      change f 1 ∉ S
      rw [hf1]
      exact hy
  obtain ⟨f', hf', hrel, hdisjoint⟩ :=
    GeneralPosition.exists_disjoint_smooth_map_homotopicRel fI g hfI hg hdim'
      ((Set.finite_singleton (1 : unitInterval)).insert 0).isClosed hfixed
  have hf'0 : f' 0 = x := (hrel.fst_eq_snd (by simp)).symm.trans hf0
  have hf'1 : f' 1 = y := (hrel.fst_eq_snd (by simp)).symm.trans hf1
  let η : Path x y := { toContinuousMap := f', source' := hf'0, target' := hf'1 }
  refine ⟨η, hf', ?_⟩
  intro t ht
  rw [hrange] at hdisjoint
  exact Set.disjoint_left.mp hdisjoint ⟨t, rfl⟩ ht

private theorem Smale.exists_pointMoving_fixing_finite {G H N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
    [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N]
    {x y : N} (γ : Path x y) (hdim : 2 ≤ Module.finrank ℝ G) {S : Set N} (hS : S.Finite)
    (hx : x ∉ S) (hy : y ∉ S) : ∃ d : Diffeomorph J J N N ∞, d x = y ∧ ∀ z ∈ S, d z = z := by
  obtain ⟨η, _, hη⟩ := exists_smooth_path_avoiding_finite (J := J) γ hdim hS hx hy
  obtain ⟨d, hd, hfix⟩ :=
    SupportedDiffeomorph.exists_pointMoving_of_path (J := J) hS.isClosed.isOpen_compl η hη
  exact ⟨d, hd, fun z hz => hfix z (fun hn => hn hz)⟩

private def Smale.ChartMapPerturbation.collisionDomain {G F K X N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
    {J : ModelWithCorners ℝ G K} [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (f : X → N) (β : X → ℝ) : Set (X × X) :=
  {q | f q.1 ∈ c.source ∧ f q.2 ∈ c.source ∧ β q.1 - β q.2 ≠ 0}

private def Smale.ChartMapPerturbation.collisionParameter {G F K X N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
    {J : ModelWithCorners ℝ G K} [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (f : X → N) (β : X → ℝ) (q : X × X) : F :=
  (β q.1 - β q.2)⁻¹ • (c (f q.2) - c (f q.1))

private theorem Smale.ChartMapPerturbation.isOpen_collisionDomain {G F K X N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace K] {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [TopologicalSpace N]
    [ChartedSpace K N] (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {β : X → ℝ}
    (hf : Continuous f) (hβ : Continuous β) : IsOpen (collisionDomain c f β) :=
  (c.open_source.preimage (hf.comp continuous_fst)).inter
    ((c.open_source.preimage (hf.comp continuous_snd)).inter
      (isOpen_ne_fun ((hβ.comp continuous_fst).sub (hβ.comp continuous_snd)) continuous_const))

private theorem Smale.ChartMapPerturbation.contMDiffOn_collisionParameter {E G F H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace K]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G K} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {β : X → ℝ} (hf : ContMDiff I J ∞ f)
    (hβ : ContMDiff I 𝓘(ℝ, ℝ) ∞ β) :
    ContMDiffOn (I.prod I) 𝓘(ℝ, F) ∞ (collisionParameter c f β) (collisionDomain c f β) := by
  intro q hq
  have hcf : ContMDiffAt (I.prod I) 𝓘(ℝ, F) ∞ (fun r : X × X => c (f r.1)) q :=
    (c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hq.1)).comp q
      (hf.comp contMDiff_fst).contMDiffAt
  have hcg : ContMDiffAt (I.prod I) 𝓘(ℝ, F) ∞ (fun r : X × X => c (f r.2)) q :=
    (c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hq.2.1)).comp q
      (hf.comp contMDiff_snd).contMDiffAt
  have hb : ContMDiffAt (I.prod I) 𝓘(ℝ, ℝ) ∞ (fun r : X × X => β r.1 - β r.2) q :=
    (hβ.comp contMDiff_fst).contMDiffAt.sub (hβ.comp contMDiff_snd).contMDiffAt
  exact ((hb.inv₀ hq.2.2).smul (hcg.sub hcf)).contMDiffWithinAt

private theorem Smale.ChartMapPerturbation.collision_imp_old_and_equal_cutoff {G F K X N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace K] {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [TopologicalSpace N]
    [ChartedSpace K N] (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {β : X → ℝ}
    (hsupport : tsupport β ⊆ f ⁻¹' c.source) {a : F} (hvalid : Valid c f β a)
    (hgood : a ∉ collisionParameter c f β '' collisionDomain c f β) {x y : X}
    (heq : perturb c f β a x = perturb c f β a y) : f x = f y ∧ β x = β y := by
  classical
  by_cases hx : f x ∈ c.source
  · have hpy : perturb c f β a y ∈ c.source := heq ▸ perturb_mem_source c f β hvalid hx
    have hy : f y ∈ c.source := by
      by_contra hn
      simp only [perturb, hn, ite_false] at hpy
    have hcoord : c (f x) + β x • a = c (f y) + β y • a := by
      have hh := congrArg c heq
      simpa only [chart_perturb c f β hvalid hx, chart_perturb c f β hvalid hy,
        coordinateFamily] using hh
    by_cases hb : β x = β y
    · refine ⟨c.toPartialEquiv.injOn hx hy ?_, hb⟩
      rw [hb] at hcoord
      exact add_right_cancel hcoord
    · have hd : β x - β y ≠ 0 := sub_ne_zero.mpr hb
      have hs : (β x - β y) • a = c (f y) - c (f x) := by
        rw [sub_smul]
        exact sub_eq_sub_iff_add_eq_add.mpr (by simpa only [add_comm] using hcoord)
      exfalso
      apply hgood
      refine ⟨(x, y), ⟨hx, hy, hd⟩, ?_⟩
      change (β x - β y)⁻¹ • (c (f y) - c (f x)) = a
      rw [← hs, inv_smul_smul₀ hd]
  · have hpx : perturb c f β a x = f x := by simp only [perturb, hx, ite_false]
    have hy : f y ∉ c.source := by
      intro hy
      have hpy := perturb_mem_source c f β hvalid hy
      rw [← heq, hpx] at hpy
      exact hx hpy
    have hpy : perturb c f β a y = f y := by simp only [perturb, hy, ite_false]
    have hβx : β x = 0 := by
      by_contra hn
      exact hx (hsupport (subset_tsupport β hn))
    have hβy : β y = 0 := by
      by_contra hn
      exact hy (hsupport (subset_tsupport β hn))
    exact ⟨hpx.symm.trans (heq.trans hpy), hβx.trans hβy.symm⟩

private theorem Smale.ChartMapPerturbation.exists_small_collision_removing_parameter
    {E G F H K X N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
    [TopologicalSpace K] {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G K}
    [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {β : X → ℝ} [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] [IsManifold I ∞ X] [LindelofSpace (X × X)] (hf : ContMDiff I J ∞ f)
    (hβ : ContMDiff I 𝓘(ℝ, ℝ) ∞ β) (hcompact : HasCompactSupport β)
    (hsupport : tsupport β ⊆ f ⁻¹' c.source) (hdim : 2 * Module.finrank ℝ E < Module.finrank ℝ F)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a : F,
      ‖a‖ < ε ∧
        Valid c f β a ∧
          ContMDiff I J ∞ (perturb c f β a) ∧
            ∀ x y, perturb c f β a x = perturb c f β a y → f x = f y ∧ β x = β y := by
  have hd : Module.finrank ℝ (E × E) < Module.finrank ℝ F := by
    simpa only [Module.finrank_prod, two_mul] using hdim
  have hdense :=
    Smale.GeneralPosition.dense_compl_manifold_image
      (isOpen_collisionDomain c hf.continuous hβ.continuous)
      (contMDiffOn_collisionParameter c hf hβ) hd
  obtain ⟨δ, hδ, hvalid⟩ := exists_radius_valid c hf hβ hcompact hsupport
  obtain ⟨a, hgood, har⟩ := hdense.exists_dist_lt 0 (lt_min hε hδ)
  have ha : ‖a‖ < Min.min ε δ := by simpa only [dist_zero_left] using har
  have hv := hvalid a (lt_of_lt_of_le ha (min_le_right _ _))
  exact
    ⟨a, lt_of_lt_of_le ha (min_le_left _ _), hv, contMDiff_perturb c hf hβ hsupport hv,
      fun _ _ heq => collision_imp_old_and_equal_cutoff c hsupport hv hgood heq⟩

private def Smale.ChartMapPerturbation.obstacleDomain {G F K X Y N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
    {J : ModelWithCorners ℝ G K} [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (f : X → N) (g : Y → N) (β : X → ℝ) : Set (X × Y) :=
  {q | f q.1 ∈ c.source ∧ g q.2 ∈ c.source ∧ β q.1 ≠ 0}

private def
    Smale.ChartMapPerturbation.obstacleParameter {G F K X Y N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
    {J : ModelWithCorners ℝ G K} [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (f : X → N) (g : Y → N) (β : X → ℝ) (q : X × Y) :
    F :=
  (β q.1)⁻¹ • (c (g q.2) - c (f q.1))

private theorem Smale.ChartMapPerturbation.isOpen_obstacleDomain {G F K X Y N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace K] {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace N] [ChartedSpace K N] (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N}
    {g : Y → N} {β : X → ℝ} (hf : Continuous f) (hg : Continuous g) (hβ : Continuous β) :
    IsOpen (obstacleDomain c f g β) :=
  (c.open_source.preimage (hf.comp continuous_fst)).inter
    ((c.open_source.preimage (hg.comp continuous_snd)).inter
      (isOpen_ne_fun (hβ.comp continuous_fst) continuous_const))

private theorem
    Smale.ChartMapPerturbation.contMDiffOn_obstacleParameter {E E' G F H H' K X Y N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace K] {I : ModelWithCorners ℝ E H}
    {I' : ModelWithCorners ℝ E' H'} {J : ModelWithCorners ℝ G K} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H' Y] [TopologicalSpace N]
    [ChartedSpace K N] (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {g : Y → N}
    {β : X → ℝ} (hf : ContMDiff I J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hβ : ContMDiff I 𝓘(ℝ, ℝ) ∞ β) :
    ContMDiffOn (I.prod I') 𝓘(ℝ, F) ∞ (obstacleParameter c f g β) (obstacleDomain c f g β) := by
  intro q hq
  have hcf : ContMDiffAt (I.prod I') 𝓘(ℝ, F) ∞ (fun r : X × Y => c (f r.1)) q :=
    (c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hq.1)).comp q
      (hf.comp contMDiff_fst).contMDiffAt
  have hcg : ContMDiffAt (I.prod I') 𝓘(ℝ, F) ∞ (fun r : X × Y => c (g r.2)) q :=
    (c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hq.2.1)).comp q
      (hg.comp contMDiff_snd).contMDiffAt
  exact (((hβ.comp contMDiff_fst).contMDiffAt.inv₀ hq.2.2).smul (hcg.sub hcf)).contMDiffWithinAt

private theorem Smale.ChartMapPerturbation.avoids_of_not_obstacle_parameter {G F K X Y N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace K] {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [TopologicalSpace N]
    [ChartedSpace K N] (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {g : Y → N}
    {β : X → ℝ} (hsupport : tsupport β ⊆ f ⁻¹' c.source) {a : F} (ha : Valid c f β a)
    (hgood : a ∉ obstacleParameter c f g β '' obstacleDomain c f g β) (x : X) (hx : β x ≠ 0)
    (y : Y) : perturb c f β a x ≠ g y := by
  intro heq
  have hfx : f x ∈ c.source := hsupport (subset_tsupport β hx)
  have hgy : g y ∈ c.source := heq ▸ perturb_mem_source c f β ha hfx
  have hcoord : c (f x) + β x • a = c (g y) := by
    rw [← heq, chart_perturb c f β ha hfx]
    rfl
  apply hgood
  refine ⟨(x, y), ⟨hfx, hgy, hx⟩, ?_⟩
  change (β x)⁻¹ • (c (g y) - c (f x)) = a
  rw [← hcoord, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hx, one_smul]

private theorem Smale.ChartMapPerturbation.exists_small_embedding_avoiding_parameter
    {E E' G F H H' K X Y N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace K]
    {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'} {J : ModelWithCorners ℝ G K}
    [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [TopologicalSpace Y]
    [ChartedSpace H' Y] [IsManifold I' ∞ Y] [TopologicalSpace N] [ChartedSpace K N]
    [LindelofSpace (X × X)] [LindelofSpace (X × Y)] (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞)
    {f : X → N} {g : Y → N} {β : X → ℝ} (hf : ContMDiff I J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hβ : ContMDiff I 𝓘(ℝ, ℝ) ∞ β) (hcompact : HasCompactSupport β)
    (hsupport : tsupport β ⊆ f ⁻¹' c.source) (hself : 2 * Module.finrank ℝ E < Module.finrank ℝ F)
    (hobstacle : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ F) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ a : F,
      ‖a‖ < ε ∧
        Valid c f β a ∧
          ContMDiff I J ∞ (perturb c f β a) ∧
            (∀ x y, perturb c f β a x = perturb c f β a y → f x = f y) ∧
              ∀ x, β x ≠ 0 → ∀ y, perturb c f β a x ≠ g y := by
  have hdself : Module.finrank ℝ (E × E) < Module.finrank ℝ F := by
    simpa only [Module.finrank_prod, two_mul] using hself
  have hdobstacle : Module.finrank ℝ (E × E') < Module.finrank ℝ F := by
    simpa only [Module.finrank_prod] using hobstacle
  have hs :=
    Smale.GeneralPosition.dimH_image_manifold_le
      (isOpen_collisionDomain c hf.continuous hβ.continuous)
      (contMDiffOn_collisionParameter c hf hβ)
  have ho :=
    Smale.GeneralPosition.dimH_image_manifold_le
      (isOpen_obstacleDomain c hf.continuous hg.continuous hβ.continuous)
      (contMDiffOn_obstacleParameter c hf hg hβ)
  have hdense :
    Dense
      ((collisionParameter c f β '' collisionDomain c f β) ∪
          (obstacleParameter c f g β '' obstacleDomain c f g β))ᶜ := by
    apply dense_compl_of_dimH_lt_finrank
    rw [dimH_union]
    exact max_lt (hs.trans_lt (Nat.cast_lt.mpr hdself)) (ho.trans_lt (Nat.cast_lt.mpr hdobstacle))
  obtain ⟨δ, hδ, hvalid⟩ := exists_radius_valid c hf hβ hcompact hsupport
  obtain ⟨a, hgood, hnorm⟩ := hdense.exists_dist_lt 0 (lt_min hε hδ)
  have ha : ‖a‖ < Min.min ε δ := by simpa only [dist_zero_left] using hnorm
  have hv := hvalid a (lt_min_iff.mp ha).2
  refine ⟨a, (lt_min_iff.mp ha).1, hv, contMDiff_perturb c hf hβ hsupport hv, ?_, ?_⟩
  · intro x y hxy
    exact (collision_imp_old_and_equal_cutoff c hsupport hv (fun h => hgood (Or.inl h)) hxy).1
  · exact avoids_of_not_obstacle_parameter c hsupport hv (fun h => hgood (Or.inr h))

private theorem Smale.ManifoldImmersion.injective_fderiv_chart_iff {E G F H N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
    [TopologicalSpace N] [ChartedSpace H N] (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : E → N}
    {x : E} (hf : MDifferentiableAt 𝓘(ℝ, E) J f x) (hx : f x ∈ c.source) :
    Function.Injective (fderiv ℝ (c ∘ f) x) ↔ Function.Injective (mfderiv 𝓘(ℝ, E) J f x) := by
  have hderiv : fderiv ℝ (c ∘ f) x = (mfderiv J 𝓘(ℝ, F) c (f x)).comp (mfderiv 𝓘(ℝ, E) J f x) := by
    rw [← mfderiv_eq_fderiv, mfderiv_comp x (c.mdifferentiableAt (by simp) hx) hf]
  have hc : Function.Injective (mfderiv J 𝓘(ℝ, F) c (f x)) :=
    ((c.isLocalDiffeomorphAt J 𝓘(ℝ, F) ∞ hx).mfderivToContinuousLinearEquiv (by simp)).injective
  rw [hderiv]
  constructor
  · intro h v w hvw
    exact h (congrArg (mfderiv J 𝓘(ℝ, F) c (f x)) hvw)
  · exact fun h => hc.comp h

private theorem Smale.ManifoldImmersion.fderiv_chart_eq_zero_iff {E G F H N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
    [TopologicalSpace N] [ChartedSpace H N] (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : E → N}
    {x : E} (hf : MDifferentiableAt 𝓘(ℝ, E) J f x) (hx : f x ∈ c.source) (v : E) :
    fderiv ℝ (c ∘ f) x v = 0 ↔ mfderiv 𝓘(ℝ, E) J f x v = 0 := by
  have hderiv : fderiv ℝ (c ∘ f) x = (mfderiv J 𝓘(ℝ, F) c (f x)).comp (mfderiv 𝓘(ℝ, E) J f x) := by
    rw [← mfderiv_eq_fderiv, mfderiv_comp x (c.mdifferentiableAt (by simp) hx) hf]
  have hc : Function.Injective (mfderiv J 𝓘(ℝ, F) c (f x)) :=
    ((c.isLocalDiffeomorphAt J 𝓘(ℝ, F) ∞ hx).mfderivToContinuousLinearEquiv (by simp)).injective
  rw [hderiv]
  change (mfderiv J 𝓘(ℝ, F) c (f x)) (mfderiv 𝓘(ℝ, E) J f x v) = 0 ↔ _
  constructor
  · intro h
    apply hc
    simpa only [map_zero] using h
  · intro h
    rw [h, map_zero]

private theorem Smale.ManifoldImmersion.isOpen_injective_nativeDerivative {P E G H N : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold J ∞ N] {f : P → E → N} {W : Set (P × E)} (hW : IsOpen W)
    (hf : ContMDiffOn (𝓘(ℝ, P).prod 𝓘(ℝ, E)) J ∞ (Function.uncurry f) W) :
    IsOpen {q : P × E | q ∈ W ∧ Function.Injective (mfderiv 𝓘(ℝ, E) J (f q.1) q.2)} := by
  rw [isOpen_iff_mem_nhds]
  rintro q ⟨hq, hqinj⟩
  let c := NoExotic.modelChartPartialDiffeomorph (I := J) (f q.1 q.2)
  let U := W ∩ (Function.uncurry f) ⁻¹' c.source
  have hU : IsOpen U := hf.continuousOn.isOpen_inter_preimage hW c.open_source
  have hqU : q ∈ U := ⟨hq, mem_extChartAt_source (f q.1 q.2)⟩
  have hc : ContDiffOn ℝ ∞ (fun r : P × E => c (f r.1 r.2)) U := by
    intro r hr
    have hmap :
      ContMDiffAt 𝓘(ℝ, P × E) (𝓘(ℝ, P).prod 𝓘(ℝ, E)) ∞ (fun s : P × E => (s.1, s.2)) r :=
      contDiffAt_fst.contMDiffAt.prodMk contDiffAt_snd.contMDiffAt
    have hfr := (hf.contMDiffAt (hW.mem_nhds hr.1)).comp r hmap
    exact
      ((c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hr.2)).comp r
          hfr) |>.contDiffAt.contDiffWithinAt
  have hd :=
    Smale.MorsePerturbation.contDiffOn_spatialDerivative (f := fun a x => c (f a x)) hU hc
  have hgood :
    IsOpen
      (U ∩
        (fun r : P × E => fderiv ℝ (c ∘ f r.1) r.2) ⁻¹' {L : E →L[ℝ] G | Function.Injective L}) :=
    hd.continuousOn.isOpen_inter_preimage hU ContinuousLinearMap.isOpen_injective
  have hiff (r : P × E) (hr : r ∈ U) :
    Function.Injective (fderiv ℝ (c ∘ f r.1) r.2) ↔
      Function.Injective (mfderiv 𝓘(ℝ, E) J (f r.1) r.2) := by
    have hs : ContMDiffAt 𝓘(ℝ, E) J ∞ (f r.1) r.2 :=
      (hf.contMDiffAt (hW.mem_nhds hr.1)).comp r.2 (f := fun x : E => (r.1, x))
        (contMDiffAt_const.prodMk contMDiffAt_id)
    exact injective_fderiv_chart_iff c (hs.mdifferentiableAt (by simp)) hr.2
  have hn := hgood.mem_nhds ⟨hqU, (hiff q hqU).mpr hqinj⟩
  apply Filter.mem_of_superset hn
  intro r hr
  exact ⟨hr.1.1, (hiff r hr.1).mp hr.2⟩

private theorem Smale.ManifoldImmersion.isOpen_injective_derivative_on {E G H N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [J.Boundaryless]
    [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] {f : E → N} {W : Set E}
    (hW : IsOpen W) (hf : ContMDiffOn 𝓘(ℝ, E) J ∞ f W) :
    IsOpen {x : E | x ∈ W ∧ Function.Injective (mfderiv 𝓘(ℝ, E) J f x)} := by
  have hfamily :
    ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) J ∞ (fun q : ℝ × E => f q.2) (Prod.snd ⁻¹' W) :=
    hf.comp contMDiff_snd.contMDiffOn (fun _ hp => hp)
  have hopen :=
    (isOpen_injective_nativeDerivative (f := fun (_ : ℝ) => f) (hW.preimage continuous_snd)
          hfamily).preimage
      ((continuous_const (y := (0 : ℝ))).prodMk (continuous_id : Continuous (id : E → E)))
  exact hopen

private theorem Smale.ManifoldImmersion.isOpen_injective_derivative {E G H N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [J.Boundaryless]
    [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] {f : E → N}
    (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) :
    IsOpen {x : E | Function.Injective (mfderiv 𝓘(ℝ, E) J f x)} := by
  have hfamily : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) J ∞ (fun q : ℝ × E => f q.2) :=
    hf.comp contMDiff_snd
  have hopen :=
    (isOpen_injective_nativeDerivative (f := fun (_ : ℝ) => f) isOpen_univ
          hfamily.contMDiffOn).preimage
      ((continuous_const (y := (0 : ℝ))).prodMk (continuous_id : Continuous (id : E → E)))
  change IsOpen {x : E | True ∧ Function.Injective (mfderiv 𝓘(ℝ, E) J f x)} at hopen
  simpa only [true_and] using hopen

private theorem Smale.ManifoldImmersion.eventually_injective_nativeDerivative {P E G H N : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold J ∞ N] {f : P → E → N} {W : Set (P × E)} (hW : IsOpen W)
    (hf : ContMDiffOn (𝓘(ℝ, P).prod 𝓘(ℝ, E)) J ∞ (Function.uncurry f) W) {K : Set E}
    (hK : IsCompact K) {a₀ : P} (hmem : ∀ x ∈ K, (a₀, x) ∈ W)
    (hinj : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J (f a₀) x)) :
    ∀ᶠ a in 𝓝 a₀, ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J (f a) x) := by
  have hopen :=
    Smale.MorsePerturbation.isOpen_forall_mem_compact hK (isOpen_injective_nativeDerivative hW hf)
  have hn := hopen.mem_nhds (fun x hx => ⟨hmem x hx, hinj x hx⟩)
  filter_upwards [hn] with a ha x hx
  exact (ha x hx).2

private theorem
    Smale.ChartMapPerturbation.eventually_perturb_injective_derivative {E G F H N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold J ∞ N] (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : E → N} {β : E → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) (hβ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ β)
    (hcompact : HasCompactSupport β) (hsupport : tsupport β ⊆ f ⁻¹' c.source) {K : Set E}
    (hK : IsCompact K) (hinj : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x)) :
    ∀ᶠ a : F in 𝓝 0, ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J (perturb c f β a) x) := by
  obtain ⟨δ, hδ, hvalid⟩ := exists_radius_valid c hf hβ hcompact hsupport
  let W : Set (F × E) := {q | ‖q.1‖ < δ}
  have hW : IsOpen W := isOpen_lt continuous_fst.norm continuous_const
  have hfamily :
    ContMDiffOn (𝓘(ℝ, F).prod 𝓘(ℝ, E)) J ∞ (fun q : F × E => perturb c f β q.1 q.2) W := by
    intro q hq
    exact (contMDiffAt_perturb c hf hβ hsupport q (hvalid q.1 hq)).contMDiffWithinAt
  apply Smale.ManifoldImmersion.eventually_injective_nativeDerivative hW hfamily hK
  · intro x _
    change ‖(0 : F)‖ < δ
    simpa only [norm_zero] using hδ
  · intro x hx
    have heq : perturb c f β (0 : F) = f := funext (perturb_zero c f β)
    change Function.Injective (mfderiv 𝓘(ℝ, E) J (perturb c f β (0 : F)) x)
    rw [heq]
    exact hinj x hx

private theorem Smale.ManifoldImmersion.exists_embedded_image_avoidance_step_controlled
    {E E' G H H' Y N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    {J : ModelWithCorners ℝ G H} {I' : ModelWithCorners ℝ E' H'} [J.Boundaryless]
    [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y] [LindelofSpace (E × Y)]
    [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] {ι : Type*} [Finite ι]
    {C K : Set E} (p : ι → Smale.GeneralPosition.MapAvoidancePatch 𝓘(ℝ, E) J (N := N) C) (i : ι)
    (f : C(E, N)) (g : C(Y, N)) (A : Set Y) (hf : ContMDiff 𝓘(ℝ, E) J ∞ f)
    (hg : ContMDiff I' J ∞ g) (hcompatible : ∀ j, (p j).Compatible f)
    (hself : 2 * Module.finrank ℝ E < Module.finrank ℝ G)
    (hobstacle : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ G) (hK : IsCompact K)
    (hderiv : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x)) {O : Set N} (hO : IsOpen O)
    (hmaps : Set.MapsTo f K O) :
    ∃ f' : C(E, N),
      ContMDiff 𝓘(ℝ, E) J ∞ f' ∧
        (∀ j, (p j).Compatible f') ∧
          Smale.HomotopicRelWithin f f' C K O ∧
            (∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f' x)) ∧
              (∀ x y, f' x = f' y → f x = f y) ∧
                Set.MapsTo f' K O ∧ ∀ x, (f x ∉ g '' A ∨ (p i).cutoff x ≠ 0) → f' x ∉ g '' A := by
  have hkeep :
    ∀ᶠ a in 𝓝 (0 : G),
      ∀ j, (p j).Compatible (Smale.ChartMapPerturbation.perturb (p i).chart f (p i).cutoff a) := by
    apply Filter.eventually_all.mpr
    intro j
    exact
      Smale.ChartMapPerturbation.eventually_maps_compact_into_open (p i).chart hf (p i).smooth
        (hcompatible i) (p j).compact.isCompact (p j).chart.open_source (hcompatible j)
  have hold :=
    Smale.ChartMapPerturbation.eventually_perturb_injective_derivative (p i).chart hf (p i).smooth
      (p i).compact (hcompatible i) hK hderiv
  have hstay :=
    Smale.ChartMapPerturbation.eventually_maps_compact_into_open (p i).chart hf (p i).smooth
      (hcompatible i) hK hO hmaps
  obtain ⟨δ, hδ, hδkeep⟩ := Metric.mem_nhds_iff.mp (hkeep.and (hold.and hstay))
  obtain ⟨r, hr, hvalid⟩ :=
    Smale.ChartMapPerturbation.exists_radius_valid (p i).chart hf (p i).smooth (p i).compact
      (hcompatible i)
  obtain ⟨a, ha, -, hsmooth, hnoNew, havoid⟩ :=
    Smale.ChartMapPerturbation.exists_small_embedding_avoiding_parameter (p i).chart hf hg
      (p i).smooth (p i).compact (hcompatible i) hself hobstacle (lt_min hδ hr)
  have haδ : ‖a‖ < δ := (lt_min_iff.mp ha).1
  have har : ‖a‖ < r := (lt_min_iff.mp ha).2
  let f' : C(E, N) := ⟨_, hsmooth.continuous⟩
  have hretained :=
    hδkeep (show a ∈ Metric.ball 0 δ by simpa only [Metric.mem_ball, dist_zero_right] using haδ)
  let Hrel :=
    Smale.ChartMapPerturbation.homotopyRel (p i).chart hf (p i).smooth (hcompatible i) hvalid har
  refine ⟨f', hsmooth, hretained.1, ?_, hretained.2.1, hnoNew, hretained.2.2, ?_⟩
  · refine ⟨{ Hrel.toHomotopy with prop' := fun t x hx => Hrel.eq_fst t ((p i).fixed x hx) }, ?_⟩
    intro t x hx
    change Smale.ChartMapPerturbation.perturb (p i).chart f (p i).cutoff ((t : ℝ) • a) x ∈ O
    have hsmall : (t : ℝ) • a ∈ Metric.ball (0 : G) δ := by
      simpa only [Metric.mem_ball, dist_zero_right] using
        Smale.ChartMapPerturbation.norm_interval_smul_lt haδ t
    exact (hδkeep hsmall).2.2 hx
  · intro x hx
    by_cases hzero : (p i).cutoff x = 0
    · have hold : f x ∉ g '' A := hx.resolve_right (Classical.not_not.mpr hzero)
      change Smale.ChartMapPerturbation.perturb (p i).chart f (p i).cutoff a x ∉ g '' A
      rwa [Smale.ChartMapPerturbation.perturb_eq_of_zero _ _ _ _ hzero]
    · rintro ⟨y, _, hy⟩
      exact havoid x hzero y hy.symm

private theorem Smale.ManifoldImmersion.exists_finite_embedded_image_avoidance_controlled
    {E E' G H H' Y N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    {J : ModelWithCorners ℝ G H} {I' : ModelWithCorners ℝ E' H'} [J.Boundaryless]
    [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y] [LindelofSpace (E × Y)]
    [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] {ι : Type*} [Finite ι]
    {C K : Set E} (p : ι → Smale.GeneralPosition.MapAvoidancePatch 𝓘(ℝ, E) J (N := N) C)
    (f : C(E, N)) (g : C(Y, N)) (A : Set Y) (hf : ContMDiff 𝓘(ℝ, E) J ∞ f)
    (hg : ContMDiff I' J ∞ g) (hcompatible : ∀ j, (p j).Compatible f)
    (hself : 2 * Module.finrank ℝ E < Module.finrank ℝ G)
    (hobstacle : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ G) (hK : IsCompact K)
    (hderiv : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x)) {O : Set N} (hO : IsOpen O)
    (hmaps : Set.MapsTo f K O) (s : Finset ι) :
    ∃ f' : C(E, N),
      ContMDiff 𝓘(ℝ, E) J ∞ f' ∧
        (∀ j, (p j).Compatible f') ∧
          Smale.HomotopicRelWithin f f' C K O ∧
            (∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f' x)) ∧
              (∀ x y, f' x = f' y → f x = f y) ∧
                Set.MapsTo f' K O ∧
                  ∀ x, (f x ∉ g '' A ∨ ∃ i ∈ s, (p i).cutoff x ≠ 0) → f' x ∉ g '' A := by
  classical
    induction s using Finset.induction_on with
  |
    empty =>
    refine
      ⟨f, hf, hcompatible, Smale.HomotopicRelWithin.refl f C hmaps, hderiv, (fun _ _ hxy => hxy),
        hmaps, ?_⟩
    intro x hx
    simpa only [Finset.notMem_empty, false_and, exists_false, or_false] using hx
  | @insert i s _
    ih =>
    obtain ⟨f₁, hf₁, hc₁, hhom₁, hd₁, hnoNew₁, hmaps₁, havoid₁⟩ := ih
    obtain ⟨f₂, hf₂, hc₂, hhom₂, hd₂, hnoNew₂, hmaps₂, havoid₂⟩ :=
      exists_embedded_image_avoidance_step_controlled p i f₁ g A hf₁ hg hc₁ hself hobstacle hK hd₁
        hO hmaps₁
    refine
      ⟨f₂, hf₂, hc₂, hhom₁.trans hhom₂, hd₂, (fun x y hxy => hnoNew₁ x y (hnoNew₂ x y hxy)),
        hmaps₂, ?_⟩
    intro x hx
    apply havoid₂ x
    rcases hx with hold | ⟨j, hj, hactive⟩
    · exact Or.inl (havoid₁ x (Or.inl hold))
    · rcases Finset.mem_insert.mp hj with rfl | hjs
      · exact Or.inr hactive
      · exact Or.inl (havoid₁ x (Or.inr ⟨j, hjs, hactive⟩))

private theorem
    Smale.ManifoldImmersion.exists_embedded_avoidance_on_compact_of_isClosed_image_controlled
    {E E' G H H' Y N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    {J : ModelWithCorners ℝ G H} {I' : ModelWithCorners ℝ E' H'} [J.Boundaryless]
    [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y] [LindelofSpace (E × Y)]
    [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N] (f : C(E, N))
    (g : C(Y, N)) (A : Set Y) (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hclosed : IsClosed (g '' A)) (hself : 2 * Module.finrank ℝ E < Module.finrank ℝ G)
    (hobstacle : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ G) {K L C : Set E}
    (hK : IsCompact K) (hL : IsCompact L) (hC : IsClosed C) (hinj : Set.InjOn f K)
    (hderiv : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x))
    (hfixed : ∀ x ∈ L ∩ C, f x ∉ g '' A) {O : Set N} (hO : IsOpen O) (hmaps : Set.MapsTo f K O) :
    ∃ f' : C(E, N),
      ContMDiff 𝓘(ℝ, E) J ∞ f' ∧
        Smale.HomotopicRelWithin f f' C K O ∧
          Topology.IsClosedEmbedding (fun x : K => f' x) ∧
            (∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f' x)) ∧
              (∀ x y, f' x = f' y → f x = f y) ∧
                Set.MapsTo f' K O ∧ ∀ x, (f x ∉ g '' A ∨ x ∈ L) → f' x ∉ g '' A := by
  classical
  let bad : Set E := L ∩ f ⁻¹' g '' A
  have hbad : IsCompact bad := hL.inter_right (hclosed.preimage f.continuous)
  have hp (x : bad) :
    ∃ p : Smale.GeneralPosition.MapAvoidancePatch 𝓘(ℝ, E) J (N := N) C,
      p.Compatible f ∧ p.cutoff x.1 ≠ 0 :=
    Smale.GeneralPosition.exists_avoidance_patch_at (I := 𝓘(ℝ, E)) (J := J) f hC
      (fun hx => hfixed x.1 ⟨x.property.1, hx⟩ x.property.2)
  choose p hpcompatible hpactive using hp
  have hopen (x : bad) : IsOpen (Function.support (p x).cutoff) :=
    isOpen_ne_fun (p x).smooth.continuous continuous_const
  have hcover : bad ⊆ ⋃ x : bad, Function.support (p x).cutoff := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hpactive ⟨x, hx⟩⟩
  obtain ⟨s, hs⟩ :=
    hbad.elim_finite_subcover (fun x : bad => Function.support (p x).cutoff) hopen hcover
  obtain ⟨f', hf', -, hhom, hderiv', hnoNew, hmaps', havoid⟩ :=
    exists_finite_embedded_image_avoidance_controlled (fun i : s => p i.1) f g A hf hg
      (fun i => hpcompatible i.1) hself hobstacle hK hderiv hO hmaps Finset.univ
  refine ⟨f', hf', hhom, ?_, hderiv', hnoNew, hmaps', ?_⟩
  · let : CompactSpace K := isCompact_iff_compactSpace.mp hK
    apply (f'.continuous.comp continuous_subtype_val).isClosedEmbedding
    intro x y hxy
    exact Subtype.ext (hinj x.property y.property (hnoNew x y hxy))
  · intro x hx
    apply havoid x
    rcases hx with hold | hxL
    · exact Or.inl hold
    · by_cases hxg : f x ∈ g '' A
      · have hx : x ∈ bad := ⟨hxL, hxg⟩
        obtain ⟨i, hi, hix⟩ := Set.mem_iUnion₂.mp (hs hx)
        exact Or.inr ⟨⟨i, hi⟩, Finset.mem_univ _, hix⟩
      · exact Or.inl hxg

private theorem Smale.ManifoldImmersion.exists_embedded_avoidance_on_compact_of_isClosed_image
    {E E' G H H' Y N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    {J : ModelWithCorners ℝ G H} {I' : ModelWithCorners ℝ E' H'} [J.Boundaryless]
    [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y] [LindelofSpace (E × Y)]
    [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N] (f : C(E, N))
    (g : C(Y, N)) (A : Set Y) (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hclosed : IsClosed (g '' A)) (hself : 2 * Module.finrank ℝ E < Module.finrank ℝ G)
    (hobstacle : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ G) {K L C : Set E}
    (hK : IsCompact K) (hL : IsCompact L) (hC : IsClosed C) (hinj : Set.InjOn f K)
    (hderiv : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x))
    (hfixed : ∀ x ∈ L ∩ C, f x ∉ g '' A) {O : Set N} (hO : IsOpen O) (hmaps : Set.MapsTo f K O) :
    ∃ f' : C(E, N),
      ContMDiff 𝓘(ℝ, E) J ∞ f' ∧
        f.HomotopicRel f' C ∧
          Topology.IsClosedEmbedding (fun x : K => f' x) ∧
            (∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f' x)) ∧
              (∀ x y, f' x = f' y → f x = f y) ∧
                Set.MapsTo f' K O ∧ ∀ x, (f x ∉ g '' A ∨ x ∈ L) → f' x ∉ g '' A := by
  obtain ⟨f', hf', hhom, hemb, hd, hnoNew, hmaps', havoid⟩ :=
    exists_embedded_avoidance_on_compact_of_isClosed_image_controlled f g A hf hg hclosed hself
      hobstacle hK hL hC hinj hderiv hfixed hO hmaps
  exact ⟨f', hf', hhom.homotopicRel, hemb, hd, hnoNew, hmaps', havoid⟩

private theorem Smale.ManifoldImmersion.exists_embedded_avoidance_on_compact_of_isClosed_range
    {E E' G H H' Y N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    {J : ModelWithCorners ℝ G H} {I' : ModelWithCorners ℝ E' H'} [J.Boundaryless]
    [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y] [LindelofSpace (E × Y)]
    [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N] (f : C(E, N))
    (g : C(Y, N)) (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hclosed : IsClosed (Set.range g)) (hself : 2 * Module.finrank ℝ E < Module.finrank ℝ G)
    (hobstacle : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ G) {K L C : Set E}
    (hK : IsCompact K) (hL : IsCompact L) (hC : IsClosed C) (hinj : Set.InjOn f K)
    (hderiv : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x))
    (hfixed : ∀ x ∈ L ∩ C, f x ∉ Set.range g) :
    ∃ f' : C(E, N),
      ContMDiff 𝓘(ℝ, E) J ∞ f' ∧
        f.HomotopicRel f' C ∧
          Topology.IsClosedEmbedding (fun x : K => f' x) ∧
            (∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f' x)) ∧
              (∀ x y, f' x = f' y → f x = f y) ∧
                ∀ x, (f x ∉ Set.range g ∨ x ∈ L) → f' x ∉ Set.range g := by
  obtain ⟨f', hf', hhom, hemb, hd, hnoNew, -, havoid⟩ :=
    exists_embedded_avoidance_on_compact_of_isClosed_image f g Set.univ hf hg
      (by simpa only [Set.image_univ] using hclosed) hself hobstacle hK hL hC hinj hderiv
      (by simpa only [Set.image_univ] using hfixed) isOpen_univ (fun _ _ => Set.mem_univ _)
  refine ⟨f', hf', hhom, hemb, hd, hnoNew, ?_⟩
  simpa only [Set.image_univ] using havoid

private abbrev Smale.PlaneImmersion.Plane :=
  ℝ × ℝ

private def Smale.PlaneImmersion.linearMap {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : F × F) : Plane →L[ℝ] F :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight A.1 + (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight A.2

private theorem
    Smale.PlaneImmersion.linearMap_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : F × F) (v : Plane) : linearMap A v = v.1 • A.1 + v.2 • A.2 :=
  rfl

private def Smale.PlaneImmersion.perturb {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Plane → F) (A : F × F) (x : Plane) : F :=
  f x + linearMap A x

private theorem Smale.PlaneImmersion.contDiff_perturb_family {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : Plane → F} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun q : (F × F) × Plane => perturb f q.1 q.2) :=
  (hf.comp contDiff_snd).add
    (((contDiff_fst.comp contDiff_snd).smul (contDiff_fst.comp contDiff_fst)).add
      ((contDiff_snd.comp contDiff_snd).smul (contDiff_snd.comp contDiff_fst)))

private theorem
    Smale.PlaneImmersion.fderiv_perturb {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Plane → F} (hf : ContDiff ℝ ∞ f) (A : F × F) (x : Plane) :
    fderiv ℝ (perturb f A) x = fderiv ℝ f x + linearMap A :=
  ((hf.differentiable (by simp) x).hasFDerivAt.add (linearMap A).hasFDerivAt).fderiv

private def Smale.PlaneImmersion.firstCollisionDomain {F : Type*} : Set (Plane × (Plane × F)) :=
  {q | q.1.1 - q.2.1.1 ≠ 0}

private def Smale.PlaneImmersion.secondCollisionDomain {F : Type*} : Set (Plane × (Plane × F)) :=
  {q | q.1.2 - q.2.1.2 ≠ 0}

private def Smale.PlaneImmersion.firstCollision {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Plane → F) (q : Plane × (Plane × F)) : F × F :=
  ((q.1.1 - q.2.1.1)⁻¹ • (f q.2.1 - f q.1 - (q.1.2 - q.2.1.2) • q.2.2), q.2.2)

private def
    Smale.PlaneImmersion.secondCollision {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Plane → F) (q : Plane × (Plane × F)) : F × F :=
  (q.2.2, (q.1.2 - q.2.1.2)⁻¹ • (f q.2.1 - f q.1 - (q.1.1 - q.2.1.1) • q.2.2))

private theorem
    Smale.PlaneImmersion.isOpen_firstCollisionDomain {F : Type*} [NormedAddCommGroup F] :
    IsOpen (firstCollisionDomain (F := F)) :=
  isOpen_ne.preimage (continuous_fst.fst.sub continuous_snd.fst.fst)

private theorem
    Smale.PlaneImmersion.isOpen_secondCollisionDomain {F : Type*} [NormedAddCommGroup F] :
    IsOpen (secondCollisionDomain (F := F)) :=
  isOpen_ne.preimage (continuous_fst.snd.sub continuous_snd.fst.snd)

private theorem Smale.PlaneImmersion.contDiffOn_firstCollision {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : Plane → F} (hf : ContDiff ℝ ∞ f) :
    ContDiffOn ℝ ∞ (firstCollision f) firstCollisionDomain := by
  have h₁ : ContDiff ℝ ∞ (fun q : Plane × (Plane × F) => q.1.1 - q.2.1.1) :=
    contDiff_fst.fst.sub contDiff_snd.fst.fst
  have h₂ : ContDiff ℝ ∞ (fun q : Plane × (Plane × F) => q.1.2 - q.2.1.2) :=
    contDiff_fst.snd.sub contDiff_snd.fst.snd
  exact
    ((h₁.contDiffOn.inv (fun _ h => h)).smul
          (((hf.comp contDiff_snd.fst).sub (hf.comp contDiff_fst)).sub
              (h₂.smul contDiff_snd.snd)).contDiffOn).prodMk
      contDiff_snd.snd.contDiffOn

private theorem Smale.PlaneImmersion.contDiffOn_secondCollision {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : Plane → F} (hf : ContDiff ℝ ∞ f) :
    ContDiffOn ℝ ∞ (secondCollision f) secondCollisionDomain := by
  have h₁ : ContDiff ℝ ∞ (fun q : Plane × (Plane × F) => q.1.1 - q.2.1.1) :=
    contDiff_fst.fst.sub contDiff_snd.fst.fst
  have h₂ : ContDiff ℝ ∞ (fun q : Plane × (Plane × F) => q.1.2 - q.2.1.2) :=
    contDiff_fst.snd.sub contDiff_snd.fst.snd
  exact
    contDiff_snd.snd.contDiffOn.prodMk
      ((h₂.contDiffOn.inv (fun _ h => h)).smul
        (((hf.comp contDiff_snd.fst).sub (hf.comp contDiff_fst)).sub
            (h₁.smul contDiff_snd.snd)).contDiffOn)

private theorem Smale.PlaneImmersion.mem_collision_of_eq {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : Plane → F) (A : F × F) {x y : Plane} (hxy : x ≠ y)
    (heq : perturb f A x = perturb f A y) :
    A ∈ firstCollision f '' firstCollisionDomain ∪ secondCollision f '' secondCollisionDomain := by
  have hlinear : linearMap A (x - y) = f y - f x := by
    rw [map_sub]
    change f x + linearMap A x = f y + linearMap A y at heq
    exact (sub_eq_sub_iff_add_eq_add).mpr (by simpa only [add_comm] using heq)
  change (x.1 - y.1) • A.1 + (x.2 - y.2) • A.2 = f y - f x at hlinear
  by_cases hfirst : x.1 - y.1 = 0
  · have hsecond : x.2 - y.2 ≠ 0 := by
      intro h
      exact hxy (Prod.ext (sub_eq_zero.mp hfirst) (sub_eq_zero.mp h))
    apply Or.inr
    refine ⟨(x, (y, A.1)), hsecond, Prod.ext rfl ?_⟩
    change (x.2 - y.2)⁻¹ • (f y - f x - (x.1 - y.1) • A.1) = A.2
    rw [← eq_sub_of_add_eq' hlinear, inv_smul_smul₀ hsecond]
  · apply Or.inl
    refine ⟨(x, (y, A.2)), hfirst, Prod.ext ?_ rfl⟩
    change (x.1 - y.1)⁻¹ • (f y - f x - (x.2 - y.2) • A.2) = A.1
    rw [← eq_sub_of_add_eq hlinear, inv_smul_smul₀ hfirst]

private theorem
    Smale.PlaneImmersion.injective_perturb_of_not_collision {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : Plane → F) {A : F × F}
    (hA :
      A ∉ firstCollision f '' firstCollisionDomain ∪ secondCollision f '' secondCollisionDomain) :
    Function.Injective (perturb f A) := by
  intro x y heq
  by_contra hxy
  exact hA (mem_collision_of_eq f A hxy heq)

private def Smale.PlaneImmersion.badFirst {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Plane → F) (q : Plane × (ℝ × F)) : F × F :=
  (-fderiv ℝ f q.1 (1, q.2.1) - q.2.1 • q.2.2, q.2.2)

private def Smale.PlaneImmersion.badSecond {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Plane → F) (q : Plane × (ℝ × F)) : F × F :=
  (q.2.2, -fderiv ℝ f q.1 (q.2.1, 1) - q.2.1 • q.2.2)

private theorem Smale.PlaneImmersion.contDiff_badFirst {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : Plane → F} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (badFirst f) := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have he : ContDiff ℝ ∞ (fun q : Plane × (ℝ × F) => fderiv ℝ f q.1 (1, q.2.1)) :=
    (hd.comp contDiff_fst).clm_apply (contDiff_const.prodMk (contDiff_fst.comp contDiff_snd))
  exact
    (he.neg.sub ((contDiff_fst.comp contDiff_snd).smul (contDiff_snd.comp contDiff_snd))).prodMk
      (contDiff_snd.comp contDiff_snd)

private theorem Smale.PlaneImmersion.contDiff_badSecond {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : Plane → F} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (badSecond f) := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have he : ContDiff ℝ ∞ (fun q : Plane × (ℝ × F) => fderiv ℝ f q.1 (q.2.1, 1)) :=
    (hd.comp contDiff_fst).clm_apply ((contDiff_fst.comp contDiff_snd).prodMk contDiff_const)
  exact
    (contDiff_snd.comp contDiff_snd).prodMk
      (he.neg.sub ((contDiff_fst.comp contDiff_snd).smul (contDiff_snd.comp contDiff_snd)))

private theorem Smale.PlaneImmersion.mem_bad_of_nonzero_kernel {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : Plane → F) (A : F × F) (x v : Plane) (hv : v ≠ 0)
    (hker : (fderiv ℝ f x + linearMap A) v = 0) :
    A ∈ Set.range (badFirst f) ∪ Set.range (badSecond f) := by
  by_cases hfirst : v.1 = 0
  · have hsecond : v.2 ≠ 0 := by
      intro h
      exact hv (Prod.ext hfirst h)
    let r := v.1 / v.2
    have hvec : (r, (1 : ℝ)) = v.2⁻¹ • v := by
      apply Prod.ext
      · change v.1 / v.2 = v.2⁻¹ * v.1
        rw [div_eq_mul_inv, mul_comm]
      · change (1 : ℝ) = v.2⁻¹ * v.2
        rw [inv_mul_cancel₀ hsecond]
    have hz : (fderiv ℝ f x + linearMap A) (r, 1) = 0 := by rw [hvec, map_smul, hker, smul_zero]
    change fderiv ℝ f x (r, 1) + (r • A.1 + (1 : ℝ) • A.2) = 0 at hz
    rw [one_smul, ← add_assoc] at hz
    have hsolve : A.2 = -(fderiv ℝ f x (r, 1) + r • A.1) := eq_neg_of_add_eq_zero_right hz
    apply Or.inr
    refine ⟨(x, (r, A.1)), Prod.ext rfl ?_⟩
    change -fderiv ℝ f x (r, 1) - r • A.1 = A.2
    simpa only [neg_add, sub_eq_add_neg] using hsolve.symm
  · let r := v.2 / v.1
    have hvec : ((1 : ℝ), r) = v.1⁻¹ • v := by
      apply Prod.ext
      · change (1 : ℝ) = v.1⁻¹ * v.1
        rw [inv_mul_cancel₀ hfirst]
      · change v.2 / v.1 = v.1⁻¹ * v.2
        rw [div_eq_mul_inv, mul_comm]
    have hz : (fderiv ℝ f x + linearMap A) (1, r) = 0 := by rw [hvec, map_smul, hker, smul_zero]
    change fderiv ℝ f x (1, r) + ((1 : ℝ) • A.1 + r • A.2) = 0 at hz
    rw [one_smul, ← add_assoc] at hz
    have hsolve : fderiv ℝ f x (1, r) + A.1 = -(r • A.2) := eq_neg_of_add_eq_zero_left hz
    apply Or.inl
    refine ⟨(x, (r, A.2)), Prod.ext ?_ rfl⟩
    change -fderiv ℝ f x (1, r) - r • A.2 = A.1
    rw [sub_eq_add_neg, ← hsolve, neg_add_cancel_left]

private theorem
    Smale.PlaneImmersion.injective_add_linearMap_of_not_bad {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : Plane → F) {A : F × F}
    (hA : A ∉ Set.range (badFirst f) ∪ Set.range (badSecond f)) (x : Plane) :
    Function.Injective (fderiv ℝ f x + linearMap A) := by
  intro v w hvw
  have hz : (fderiv ℝ f x + linearMap A) (v - w) = 0 := by rw [map_sub, hvw, sub_self]
  have heq : v - w = 0 := by
    by_contra hne
    exact hA (mem_bad_of_nonzero_kernel f A x (v - w) hne hz)
  exact sub_eq_zero.mp heq

private theorem Smale.PlaneImmersion.dimH_bad_parameters_le {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] {f : Plane → F} (hf : ContDiff ℝ ∞ f) :
    dimH (Set.range (badFirst f) ∪ Set.range (badSecond f)) ≤
      (Module.finrank ℝ (Plane × (ℝ × F)) : ℝ≥0∞) := by
  have hfirst : dimH (Set.range (badFirst f)) ≤ (Module.finrank ℝ (Plane × (ℝ × F)) : ℝ≥0∞) := by
    rw [← Set.image_univ]
    exact
      Smale.GeneralPosition.dimH_image_manifold_le isOpen_univ
        (contDiff_badFirst hf).contMDiff.contMDiffOn
  have hsecond : dimH (Set.range (badSecond f)) ≤ (Module.finrank ℝ (Plane × (ℝ × F)) : ℝ≥0∞) := by
    rw [← Set.image_univ]
    exact
      Smale.GeneralPosition.dimH_image_manifold_le isOpen_univ
        (contDiff_badSecond hf).contMDiff.contMDiffOn
  rw [dimH_union]
  exact max_le hfirst hsecond

private theorem Smale.PlaneImmersion.dimH_collision_parameters_le {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] {f : Plane → F} (hf : ContDiff ℝ ∞ f) :
    dimH (firstCollision f '' firstCollisionDomain ∪ secondCollision f '' secondCollisionDomain) ≤
      (Module.finrank ℝ (Plane × (Plane × F)) : ℝ≥0∞) := by
  have hfirst :=
    Smale.GeneralPosition.dimH_image_manifold_le (isOpen_firstCollisionDomain (F := F))
      (contDiffOn_firstCollision hf).contMDiffOn
  have hsecond :=
    Smale.GeneralPosition.dimH_image_manifold_le (isOpen_secondCollisionDomain (F := F))
      (contDiffOn_secondCollision hf).contMDiffOn
  rw [dimH_union]
  exact max_le hfirst hsecond

private theorem Smale.PlaneImmersion.dense_injective_immersive_parameters {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {f : Plane → F}
    (hf : ContDiff ℝ ∞ f) (hdim : 5 ≤ Module.finrank ℝ F) :
    Dense
      ((Set.range (badFirst f) ∪ Set.range (badSecond f)) ∪
          (firstCollision f '' firstCollisionDomain ∪
            secondCollision f '' secondCollisionDomain))ᶜ := by
  have hd₁ : Module.finrank ℝ (Plane × (ℝ × F)) < Module.finrank ℝ (F × F) := by
    change Module.finrank ℝ ((ℝ × ℝ) × (ℝ × F)) < Module.finrank ℝ (F × F)
    simp only [Module.finrank_prod, Module.finrank_self]
    omega
  have hd₂ : Module.finrank ℝ (Plane × (Plane × F)) < Module.finrank ℝ (F × F) := by
    change Module.finrank ℝ ((ℝ × ℝ) × ((ℝ × ℝ) × F)) < Module.finrank ℝ (F × F)
    simp only [Module.finrank_prod, Module.finrank_self]
    omega
  apply dense_compl_of_dimH_lt_finrank
  rw [dimH_union]
  exact
    max_lt ((dimH_bad_parameters_le hf).trans_lt (Nat.cast_lt.mpr hd₁))
      ((dimH_collision_parameters_le hf).trans_lt (Nat.cast_lt.mpr hd₂))

private theorem Smale.PlaneImmersion.exists_small_affine_injective_immersion {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {f : Plane → F}
    (hf : ContDiff ℝ ∞ f) (hdim : 5 ≤ Module.finrank ℝ F) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : F × F,
      ‖A‖ < ε ∧
        ContDiff ℝ ∞ (perturb f A) ∧
          Function.Injective (perturb f A) ∧ ∀ x, Function.Injective (fderiv ℝ (perturb f A) x) :=
  by
  obtain ⟨A, hA, hnorm⟩ := (dense_injective_immersive_parameters hf hdim).exists_dist_lt 0 hε
  refine ⟨A, ?_, ?_, ?_, ?_⟩
  · simpa only [dist_zero_left] using hnorm
  · exact (contDiff_perturb_family hf).comp (contDiff_const.prodMk contDiff_id)
  · exact injective_perturb_of_not_collision f (fun h => hA (Or.inr h))
  · intro x
    rw [fderiv_perturb hf]
    exact injective_add_linearMap_of_not_bad f (fun h => hA (Or.inl h)) x

private def Smale.PlaneImmersion.displacement {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (β : Plane → ℝ) (A : F × F) (x : Plane) : F :=
  β x • linearMap A x

private theorem Smale.PlaneImmersion.contDiff_displacement_family {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {β : Plane → ℝ} (hβ : ContDiff ℝ ∞ β) :
    ContDiff ℝ ∞ (fun q : (F × F) × Plane => displacement β q.1 q.2) :=
  (hβ.comp contDiff_snd).smul
    ((contDiff_snd.fst.smul contDiff_fst.fst).add (contDiff_snd.snd.smul contDiff_fst.snd))

private theorem Smale.PlaneImmersion.displacement_zero {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (β : Plane → ℝ) (x : Plane) : displacement β (0 : F × F) x = 0 := by
  simp only [displacement, linearMap_apply, Prod.fst_zero, Prod.snd_zero, smul_zero, add_zero]

private theorem Smale.PlaneImmersion.displacement_of_zero {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {β : Plane → ℝ} (A : F × F) {x : Plane} (hx : β x = 0) :
    displacement β A x = 0 := by simp only [displacement, hx, zero_smul]

private theorem Smale.PlaneImmersion.eventually_displacement_lt {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {β : Plane → ℝ} (hβ : ContDiff ℝ ∞ β) (hcompact : HasCompactSupport β)
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ A : F × F in 𝓝 0, ∀ x, ‖displacement β A x‖ < ε := by
  have hsupport : ∀ᶠ A : F × F in 𝓝 0, ∀ x ∈ tsupport β, ‖displacement β A x‖ < ε := by
    apply hcompact.isCompact.eventually_forall_of_forall_eventually
    intro x _
    have hc :=
      (contDiff_displacement_family (F := F) hβ).continuous.norm.continuousAt (x :=
        ((0 : F × F), x))
    have hval : ‖displacement β (0 : F × F) x‖ < ε := by
      simpa only [displacement_zero, norm_zero] using hε
    exact hc.preimage_mem_nhds (isOpen_Iio.mem_nhds hval)
  filter_upwards [hsupport] with A hA x
  by_cases hx : x ∈ tsupport β
  · exact hA x hx
  · have hzero : β x = 0 := by
      by_contra hne
      exact hx (subset_tsupport β hne)
    simpa only [displacement_of_zero A hzero, norm_zero] using hε

private theorem
    Smale.PlaneImmersion.exists_radius_displacement_lt {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {β : Plane → ℝ} (hβ : ContDiff ℝ ∞ β) (hcompact : HasCompactSupport β)
    {ε : ℝ} (hε : 0 < ε) : ∃ δ > (0 : ℝ), ∀ A : F × F, ‖A‖ < δ → ∀ x, ‖displacement β A x‖ < ε := by
  have hn : {A : F × F | ∀ x, ‖displacement β A x‖ < ε} ∈ 𝓝 0 :=
    eventually_displacement_lt hβ hcompact hε
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hn
  exact ⟨δ, hδ, fun A hA => hball (by simpa only [Metric.mem_ball, dist_zero_right] using hA)⟩

private def
    Smale.ManifoldImmersion.affinePatch {G F H N : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
    [TopologicalSpace N] [ChartedSpace H N] (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞)
    (f : Smale.PlaneImmersion.Plane → N) (β : Smale.PlaneImmersion.Plane → ℝ) (A : F × F) :
    Smale.PlaneImmersion.Plane → N :=
  Smale.ChartMapPerturbation.variablePerturb c f β (Smale.PlaneImmersion.displacement β A)

private theorem Smale.ManifoldImmersion.chart_affinePatch_on_plateau {G F H N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [TopologicalSpace N] [ChartedSpace H N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : Smale.PlaneImmersion.Plane → N}
    {β χ : Smale.PlaneImmersion.Plane → ℝ} {A : F × F} (hsupport : tsupport β ⊆ f ⁻¹' c.source)
    (hχ : ∀ x ∈ tsupport β, χ x = 1)
    (hvalid :
      ∀ x, Smale.ChartMapPerturbation.Valid c f β (Smale.PlaneImmersion.displacement β A x))
    {x : Smale.PlaneImmersion.Plane} (hx : β x = 1) :
    c (affinePatch c f β A x) =
      Smale.PlaneImmersion.perturb (Smale.ChartMapPerturbation.cutoffCoordinates c f χ) A x := by
  have hxs : x ∈ tsupport β := subset_tsupport β (by change β x ≠ 0; rw [hx]; norm_num)
  change
    c (Smale.ChartMapPerturbation.perturb c f β (Smale.PlaneImmersion.displacement β A x) x) = _
  rw [Smale.ChartMapPerturbation.chart_perturb c f β (hvalid x) (hsupport hxs)]
  simp only [Smale.ChartMapPerturbation.coordinateFamily, Smale.PlaneImmersion.perturb,
    Smale.ChartMapPerturbation.cutoffCoordinates, Smale.PlaneImmersion.displacement, hx, hχ x hxs,
    one_smul]

private theorem
    Smale.ManifoldImmersion.contMDiff_affinePatch {G F H N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [TopologicalSpace N] [ChartedSpace H N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : Smale.PlaneImmersion.Plane → N}
    {β : Smale.PlaneImmersion.Plane → ℝ} {A : F × F}
    (hf : ContMDiff 𝓘(ℝ, Smale.PlaneImmersion.Plane) J ∞ f) (hβ : ContDiff ℝ ∞ β)
    (hsupport : tsupport β ⊆ f ⁻¹' c.source)
    (hvalid :
      ∀ x, Smale.ChartMapPerturbation.Valid c f β (Smale.PlaneImmersion.displacement β A x)) :
    ContMDiff 𝓘(ℝ, Smale.PlaneImmersion.Plane) J ∞ (affinePatch c f β A) := by
  have hd :=
    (Smale.PlaneImmersion.contDiff_displacement_family (F := F) hβ).comp
      (contDiff_const (c := A) |>.prodMk contDiff_id)
  intro x
  exact
    Smale.ChartMapPerturbation.contMDiffAt_variablePerturb c hsupport hf.contMDiffAt
      hβ.contMDiff.contMDiffAt hd.contMDiff.contMDiffAt (hvalid x)

private theorem
    Smale.ManifoldImmersion.exists_affine_embedding_patch_with_property {G F H N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [TopologicalSpace N] [ChartedSpace H N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) [FiniteDimensional ℝ F] [T2Space N]
    (f : C(Smale.PlaneImmersion.Plane, N)) (hf : ContMDiff 𝓘(ℝ, Smale.PlaneImmersion.Plane) J ∞ f)
    {β χ : Smale.PlaneImmersion.Plane → ℝ} (hβ : ContDiff ℝ ∞ β) (hχ : ContDiff ℝ ∞ χ)
    (hcompact : HasCompactSupport β) (hχsupport : tsupport χ ⊆ f ⁻¹' c.source)
    (hχone : ∀ x ∈ tsupport β, χ x = 1) (hdim : 5 ≤ Module.finrank ℝ F)
    (Q : (Smale.PlaneImmersion.Plane → N) → Prop)
    (hQ : ∀ᶠ A : F × F in 𝓝 0, Q (affinePatch c f β A)) {K : Set Smale.PlaneImmersion.Plane}
    (hK : IsCompact K) (hKsub : K ⊆ interior {x | β x = 1}) :
    ∃ g : C(Smale.PlaneImmersion.Plane, N),
      ContMDiff 𝓘(ℝ, Smale.PlaneImmersion.Plane) J ∞ g ∧
        Q g ∧
          Nonempty (f.HomotopyRel g {x | β x = 0}) ∧
            Topology.IsClosedEmbedding (fun x : K => g x) ∧
              ∀ x ∈ interior {x | β x = 1},
                Function.Injective (mfderiv 𝓘(ℝ, Smale.PlaneImmersion.Plane) J g x) := by
  have hsupport : tsupport β ⊆ f ⁻¹' c.source := by
    intro x hx
    exact hχsupport (subset_tsupport χ (by change χ x ≠ 0; rw [hχone x hx]; norm_num))
  let k := Smale.ChartMapPerturbation.cutoffCoordinates c f χ
  have hk : ContDiff ℝ ∞ k := by
    have hm : ContMDiff 𝓘(ℝ, Smale.PlaneImmersion.Plane) 𝓘(ℝ, F) ∞ k := fun x =>
      Smale.ChartMapPerturbation.contMDiffAt_cutoffCoordinates c hχsupport hf.contMDiffAt
        hχ.contMDiff.contMDiffAt
    exact hm.contDiff
  obtain ⟨ε, hε, hvalid⟩ :=
    Smale.ChartMapPerturbation.exists_radius_valid c hf hβ.contMDiff hcompact hsupport
  obtain ⟨δ, hδ, hδbound⟩ :=
    Smale.PlaneImmersion.exists_radius_displacement_lt (F := F) hβ hcompact hε
  have hQmem : {A : F × F | Q (affinePatch c f β A)} ∈ 𝓝 0 := hQ
  obtain ⟨η, hη, hηkeep⟩ := Metric.mem_nhds_iff.mp hQmem
  obtain ⟨A, hA, -, hinj, hderiv⟩ :=
    Smale.PlaneImmersion.exists_small_affine_injective_immersion hk hdim (lt_min hδ hη)
  have hbound : ∀ x, ‖Smale.PlaneImmersion.displacement β A x‖ < ε :=
    hδbound A (lt_of_lt_of_le hA (min_le_left _ _))
  have hv :
    ∀ x, Smale.ChartMapPerturbation.Valid c f β (Smale.PlaneImmersion.displacement β A x) :=
    fun x => hvalid _ (hbound x)
  have hsmooth := contMDiff_affinePatch c hf hβ hsupport hv
  let g : C(Smale.PlaneImmersion.Plane, N) := ⟨affinePatch c f β A, hsmooth.continuous⟩
  have hcoord (x : Smale.PlaneImmersion.Plane) (hx : β x = 1) :
    c (g x) = Smale.PlaneImmersion.perturb k A x :=
    chart_affinePatch_on_plateau c hsupport hχone hv hx
  have hQg : Q g :=
    hηkeep
      (show A ∈ Metric.ball 0 η by
        simpa only [Metric.mem_ball, dist_zero_right] using
          (lt_of_lt_of_le hA (min_le_right δ η)))
  refine ⟨g, hsmooth, hQg, ?_, ?_, ?_⟩
  · have hd :=
      (Smale.PlaneImmersion.contDiff_displacement_family (F := F) hβ).comp
        (contDiff_const (c := A) |>.prodMk contDiff_id)
    exact
      ⟨Smale.ChartMapPerturbation.variableHomotopyRel c f.continuous hβ.continuous hsupport
          hd.continuous hvalid hbound (fun _ hx => Or.inl hx)⟩
  · let : CompactSpace K := isCompact_iff_compactSpace.mp hK
    apply (g.continuous.comp continuous_subtype_val).isClosedEmbedding
    intro x y hxy
    change g x = g y at hxy
    apply Subtype.ext
    apply hinj
    rw [← hcoord x (interior_subset (s := {z | β z = 1}) (hKsub x.property)), ←
      hcoord y (interior_subset (s := {z | β z = 1}) (hKsub y.property)), hxy]
  · intro x hx
    have hβx : β x = 1 := interior_subset (s := {z | β z = 1}) hx
    have hxs : f x ∈ c.source :=
      hsupport (subset_tsupport β (by change β x ≠ 0; rw [hβx]; norm_num))
    have hgs : g x ∈ c.source := Smale.ChartMapPerturbation.perturb_mem_source c f β (hv x) hxs
    apply (injective_fderiv_chart_iff c (hsmooth.mdifferentiableAt (by simp)) hgs).mp
    have heq : (c ∘ g) =ᶠ[𝓝 x] Smale.PlaneImmersion.perturb k A := by
      filter_upwards [isOpen_interior.mem_nhds hx] with y hy
      exact hcoord y (interior_subset (s := {z | β z = 1}) hy)
    change Function.Injective (fderiv ℝ (c ∘ g) x)
    rw [heq.fderiv_eq]
    exact hderiv x

private theorem Smale.ManifoldImmersion.affinePatch_zero {G F H N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [TopologicalSpace N] [ChartedSpace H N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (f : Smale.PlaneImmersion.Plane → N)
    (β : Smale.PlaneImmersion.Plane → ℝ) : affinePatch c f β (0 : F × F) = f := by
  funext x
  change
    Smale.ChartMapPerturbation.perturb c f β (Smale.PlaneImmersion.displacement β 0 x) x = f x
  rw [Smale.PlaneImmersion.displacement_zero, Smale.ChartMapPerturbation.perturb_zero]

private theorem Smale.ManifoldImmersion.contMDiffAt_affinePatch_family {G F H N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [TopologicalSpace N] [ChartedSpace H N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : Smale.PlaneImmersion.Plane → N}
    {β : Smale.PlaneImmersion.Plane → ℝ} (hf : ContMDiff 𝓘(ℝ, Smale.PlaneImmersion.Plane) J ∞ f)
    (hβ : ContDiff ℝ ∞ β) (hsupport : tsupport β ⊆ f ⁻¹' c.source)
    (q : (F × F) × Smale.PlaneImmersion.Plane)
    (hvalid :
      Smale.ChartMapPerturbation.Valid c f β (Smale.PlaneImmersion.displacement β q.1 q.2)) :
    ContMDiffAt (𝓘(ℝ, F × F).prod 𝓘(ℝ, Smale.PlaneImmersion.Plane)) J ∞
      (fun r : (F × F) × Smale.PlaneImmersion.Plane => affinePatch c f β r.1 r.2) q := by
  have hid :
    ContMDiffAt (𝓘(ℝ, F × F).prod 𝓘(ℝ, Smale.PlaneImmersion.Plane))
      𝓘(ℝ, (F × F) × Smale.PlaneImmersion.Plane) ∞
      (fun r : (F × F) × Smale.PlaneImmersion.Plane => r) q :=
    (contMDiffAt_prod_module_iff _).mpr ⟨contMDiffAt_fst, contMDiffAt_snd⟩
  have hd :=
    (Smale.PlaneImmersion.contDiff_displacement_family (F := F) hβ).contMDiff.contMDiffAt |>.comp
      q hid
  exact
    (Smale.ChartMapPerturbation.contMDiffAt_perturb c hf hβ.contMDiff hsupport
          (Smale.PlaneImmersion.displacement β q.1 q.2, q.2) hvalid).comp
      q (f := fun r : (F × F) × Smale.PlaneImmersion.Plane =>
      (Smale.PlaneImmersion.displacement β r.1 r.2, r.2)) (hd.prodMk contMDiffAt_snd)

private theorem
    Smale.ManifoldImmersion.eventually_affinePatch_maps_compact_into_open {G F H N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [TopologicalSpace N] [ChartedSpace H N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : Smale.PlaneImmersion.Plane → N}
    {β : Smale.PlaneImmersion.Plane → ℝ} (hf : ContMDiff 𝓘(ℝ, Smale.PlaneImmersion.Plane) J ∞ f)
    (hβ : ContDiff ℝ ∞ β) (hsupport : tsupport β ⊆ f ⁻¹' c.source)
    {K : Set Smale.PlaneImmersion.Plane} (hK : IsCompact K) {U : Set N} (hU : IsOpen U)
    (hmap : Set.MapsTo f K U) : ∀ᶠ A : F × F in 𝓝 0, Set.MapsTo (affinePatch c f β A) K U := by
  apply hK.eventually_forall_of_forall_eventually
  intro x hx
  have hvalid :
    Smale.ChartMapPerturbation.Valid c f β (Smale.PlaneImmersion.displacement β (0 : F × F) x) := by
    rw [Smale.PlaneImmersion.displacement_zero]
    exact Smale.ChartMapPerturbation.valid_zero c f β hsupport
  have hc := (contMDiffAt_affinePatch_family c hf hβ hsupport (0, x) hvalid).continuousAt
  apply hc.preimage_mem_nhds
  apply hU.mem_nhds
  rw [affinePatch_zero]
  exact hmap hx

private theorem
    Smale.ManifoldImmersion.eventually_affinePatch_injective_derivative {G F H N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [TopologicalSpace N] [ChartedSpace H N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) [J.Boundaryless] [IsManifold J ∞ N]
    {f : Smale.PlaneImmersion.Plane → N} {β : Smale.PlaneImmersion.Plane → ℝ}
    (hf : ContMDiff 𝓘(ℝ, Smale.PlaneImmersion.Plane) J ∞ f) (hβ : ContDiff ℝ ∞ β)
    (hcompact : HasCompactSupport β) (hsupport : tsupport β ⊆ f ⁻¹' c.source)
    {K : Set Smale.PlaneImmersion.Plane} (hK : IsCompact K)
    (hinj : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, Smale.PlaneImmersion.Plane) J f x)) :
    ∀ᶠ A : F × F in 𝓝 0,
      ∀ x ∈ K,
        Function.Injective (mfderiv 𝓘(ℝ, Smale.PlaneImmersion.Plane) J (affinePatch c f β A) x) :=
  by
  obtain ⟨ε, hε, hvalid⟩ :=
    Smale.ChartMapPerturbation.exists_radius_valid c hf hβ.contMDiff hcompact hsupport
  obtain ⟨δ, hδ, hδbound⟩ :=
    Smale.PlaneImmersion.exists_radius_displacement_lt (F := F) hβ hcompact hε
  let W : Set ((F × F) × Smale.PlaneImmersion.Plane) := {q | ‖q.1‖ < δ}
  have hW : IsOpen W := isOpen_lt continuous_fst.norm continuous_const
  have hfamily :
    ContMDiffOn (𝓘(ℝ, F × F).prod 𝓘(ℝ, Smale.PlaneImmersion.Plane)) J ∞
      (fun q : (F × F) × Smale.PlaneImmersion.Plane => affinePatch c f β q.1 q.2) W := by
    intro q hq
    exact
      (contMDiffAt_affinePatch_family c hf hβ hsupport q
          (hvalid _ (hδbound q.1 hq q.2))).contMDiffWithinAt
  apply eventually_injective_nativeDerivative hW hfamily hK
  · intro x _
    change ‖(0 : F × F)‖ < δ
    simpa only [norm_zero] using hδ
  · intro x hx
    change
      Function.Injective
        (mfderiv 𝓘(ℝ, Smale.PlaneImmersion.Plane) J (affinePatch c f β (0 : F × F)) x)
    rw [affinePatch_zero]
    exact hinj x hx

private theorem
    Smale.ManifoldImmersion.exists_immersion_patch_step {G H N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
    [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N]
    {ι : Type*} [Finite ι]
    (p :
      ι →
        Smale.ManifoldSmoothing.MapSmoothingPatch 𝓘(ℝ, Smale.PlaneImmersion.Plane) J (X :=
          Smale.PlaneImmersion.Plane) (N := N))
    (i : ι) (f : C(Smale.PlaneImmersion.Plane, N))
    (hf : ContMDiff 𝓘(ℝ, Smale.PlaneImmersion.Plane) J ∞ f)
    (hcompatible : ∀ j, (p j).Compatible f) (hdim : 5 ≤ Module.finrank ℝ G)
    {K L C : Set Smale.PlaneImmersion.Plane} (hK : IsCompact K) (hL : IsCompact L)
    (hinj : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, Smale.PlaneImmersion.Plane) J f x))
    (hLsub : L ⊆ (p i).plateau) (hfixed : ∀ x ∈ C, (p i).cutoff x = 0) :
    ∃ g : C(Smale.PlaneImmersion.Plane, N),
      ContMDiff 𝓘(ℝ, Smale.PlaneImmersion.Plane) J ∞ g ∧
        (∀ j, (p j).Compatible g) ∧
          f.HomotopicRel g C ∧
            Topology.IsClosedEmbedding (fun x : L => g x) ∧
              ∀ x ∈ K ∪ L, Function.Injective (mfderiv 𝓘(ℝ, Smale.PlaneImmersion.Plane) J g x) := by
  have hinner := (p i).inner_compatible (hcompatible i)
  have hkeep :
    ∀ᶠ A : G × G in 𝓝 0, ∀ j, (p j).Compatible (affinePatch (p i).chart f (p i).cutoff A) := by
    apply Filter.eventually_all.mpr
    intro j
    exact
      eventually_affinePatch_maps_compact_into_open (p i).chart hf (p i).smooth.contDiff hinner
        (p j).outer_compact.isCompact (p j).chart.open_source (hcompatible j)
  have hold :=
    eventually_affinePatch_injective_derivative (p i).chart hf (p i).smooth.contDiff (p i).compact
      hinner hK hinj
  let Q : (Smale.PlaneImmersion.Plane → N) → Prop := fun g =>
    (∀ j, (p j).Compatible g) ∧
      ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, Smale.PlaneImmersion.Plane) J g x)
  have hQ : ∀ᶠ A : G × G in 𝓝 0, Q (affinePatch (p i).chart f (p i).cutoff A) := hkeep.and hold
  obtain ⟨g, hg, ⟨hc, hKnew⟩, ⟨Hrel⟩, hemb, hplateau⟩ :=
    exists_affine_embedding_patch_with_property (p i).chart f hf (p i).smooth.contDiff
      (p i).outer_smooth.contDiff (p i).compact (hcompatible i) (p i).nested hdim Q hQ hL hLsub
  refine ⟨g, hg, hc, ?_, hemb, ?_⟩
  · exact ⟨{ Hrel.toHomotopy with prop' := fun t x hx => Hrel.eq_fst t (hfixed x hx) }⟩
  · intro x hx
    rcases hx with hx | hx
    · exact hKnew x hx
    · exact hplateau x (hLsub hx)

private theorem Smale.ManifoldImmersion.exists_finite_patch_immersion {G H N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold J ∞ N] [T2Space N] {ι : Type*} [Finite ι]
    (p :
      ι →
        Smale.ManifoldSmoothing.MapSmoothingPatch 𝓘(ℝ, Smale.PlaneImmersion.Plane) J (X :=
          Smale.PlaneImmersion.Plane) (N := N))
    (L : ι → Set Smale.PlaneImmersion.Plane) (hL : ∀ i, IsCompact (L i))
    (hLsub : ∀ i, L i ⊆ (p i).plateau) (f : C(Smale.PlaneImmersion.Plane, N))
    (hf : ContMDiff 𝓘(ℝ, Smale.PlaneImmersion.Plane) J ∞ f)
    (hcompatible : ∀ i, (p i).Compatible f) (hdim : 5 ≤ Module.finrank ℝ G)
    {K C : Set Smale.PlaneImmersion.Plane} (hK : IsCompact K)
    (hinj : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, Smale.PlaneImmersion.Plane) J f x))
    (hfixed : ∀ i x, x ∈ C → (p i).cutoff x = 0) (s : Finset ι) :
    ∃ g : C(Smale.PlaneImmersion.Plane, N),
      ContMDiff 𝓘(ℝ, Smale.PlaneImmersion.Plane) J ∞ g ∧
        (∀ i, (p i).Compatible g) ∧
          f.HomotopicRel g C ∧
            ∀ x ∈ K ∪ ⋃ i ∈ s, L i,
              Function.Injective (mfderiv 𝓘(ℝ, Smale.PlaneImmersion.Plane) J g x) := by
  classical
    induction s using Finset.induction_on with
  | empty =>
    refine ⟨f, hf, hcompatible, ContinuousMap.HomotopicRel.refl f, ?_⟩
    simpa only [Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty, Set.union_empty] using
      hinj
  | @insert i s _ ih =>
    obtain ⟨g₁, hg₁, hc₁, hhom₁, hinj₁⟩ := ih
    have hKold : IsCompact (K ∪ ⋃ j ∈ s, L j) := hK.union (s.isCompact_biUnion (fun j _ => hL j))
    obtain ⟨g₂, hg₂, hc₂, hhom₂, -, hinj₂⟩ :=
      exists_immersion_patch_step p i g₁ hg₁ hc₁ hdim hKold (hL i) hinj₁ (hLsub i) (hfixed i)
    refine ⟨g₂, hg₂, hc₂, hhom₁.trans hhom₂, ?_⟩
    intro x hx
    apply hinj₂ x
    rcases hx with hx | hx
    · exact Or.inl (Or.inl hx)
    · obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp hx
      rcases Finset.mem_insert.mp hj with rfl | hjs
      · exact Or.inr hxj
      · exact Or.inl (Or.inr (Set.mem_iUnion₂.mpr ⟨j, hjs, hxj⟩))

private theorem Smale.ManifoldImmersion.exists_relative_immersion_patch_at_in_open {E G H N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [J.Boundaryless]
    [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] (f : C(E, N)) {C : Set E}
    (hC : IsClosed C) {x : E} (hx : x ∉ C) {O : Set N} (hO : IsOpen O) (hxO : f x ∈ O) :
    ∃ p : Smale.ManifoldSmoothing.MapSmoothingPatch 𝓘(ℝ, E) J (X := E) (N := N),
      ∃ L : Set E,
        p.Compatible f ∧
          IsCompact L ∧
            L ∈ 𝓝 x ∧ L ⊆ p.plateau ∧ (∀ y ∈ C, p.cutoff y = 0) ∧ p.chart.source ⊆ O := by
  classical
  let c₀ := NoExotic.modelChartPartialDiffeomorph (I := J) (f x)
  let c := Smale.PartialChart.restrictSource c₀ hO
  have hsource : f x ∈ c.source := ⟨mem_extChartAt_source (I := J) (f x), hxO⟩
  have hU : f ⁻¹' c.source ∩ Cᶜ ∈ 𝓝 x :=
    ((c.open_source.preimage f.continuous).inter hC.isOpen_compl).mem_nhds ⟨hsource, hx⟩
  obtain ⟨χ, _, hχ⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓘(ℝ, E)) x).mem_iff.mp hU
  have hχone : {y : E | χ y = 1} ∈ 𝓝 x := χ.eventuallyEq_one
  obtain ⟨β, _, hβ⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓘(ℝ, E)) x).mem_iff.mp hχone
  let p : Smale.ManifoldSmoothing.MapSmoothingPatch 𝓘(ℝ, E) J (X := E) (N := N) :=
    { chart := c
      cutoff := β
      outer := χ
      smooth := β.contMDiff
      outer_smooth := χ.contMDiff
      compact := β.hasCompactSupport
      outer_compact := χ.hasCompactSupport
      nested := fun y hy => hβ hy }
  have hxp : x ∈ p.plateau := mem_interior_iff_mem_nhds.mpr β.eventuallyEq_one
  obtain ⟨L, hxL, hLp, hL⟩ := local_compact_nhds (isOpen_interior.mem_nhds hxp)
  refine ⟨p, L, (fun _ hy => (hχ hy).1), hL, hxL, hLp, ?_, fun _ hz => hz.2⟩
  intro y hy
  change β y = 0
  by_contra hne
  have hi : y ∈ tsupport β := subset_tsupport β hne
  have ho : y ∈ tsupport χ :=
    subset_tsupport χ
      (by
        change χ y ≠ 0
        rw [hβ hi]
        exact one_ne_zero)
  exact (hχ ho).2 hy

private theorem Smale.ManifoldImmersion.exists_relative_immersion_patch_at {E G H N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [J.Boundaryless]
    [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] (f : C(E, N)) {C : Set E}
    (hC : IsClosed C) {x : E} (hx : x ∉ C) :
    ∃ p : Smale.ManifoldSmoothing.MapSmoothingPatch 𝓘(ℝ, E) J (X := E) (N := N),
      ∃ L : Set E,
        p.Compatible f ∧ IsCompact L ∧ L ∈ 𝓝 x ∧ L ⊆ p.plateau ∧ ∀ y ∈ C, p.cutoff y = 0 := by
  obtain ⟨p, L, hc, hL, hn, hp, hfix, _⟩ :=
    exists_relative_immersion_patch_at_in_open (J := J) f hC hx isOpen_univ (Set.mem_univ _)
  exact ⟨p, L, hc, hL, hn, hp, hfix⟩

private theorem Smale.ManifoldImmersion.exists_immersion_on_compact_rel {G H N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold J ∞ N] [T2Space N] (f : C(Smale.PlaneImmersion.Plane, N))
    (hf : ContMDiff 𝓘(ℝ, Smale.PlaneImmersion.Plane) J ∞ f) (hdim : 5 ≤ Module.finrank ℝ G)
    {K L C : Set Smale.PlaneImmersion.Plane} (hK : IsCompact K) (hL : IsCompact L)
    (hinj : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, Smale.PlaneImmersion.Plane) J f x))
    (hC : IsClosed C) (hdis : Disjoint L C) :
    ∃ g : C(Smale.PlaneImmersion.Plane, N),
      ContMDiff 𝓘(ℝ, Smale.PlaneImmersion.Plane) J ∞ g ∧
        f.HomotopicRel g C ∧
          ∀ x ∈ K ∪ L, Function.Injective (mfderiv 𝓘(ℝ, Smale.PlaneImmersion.Plane) J g x) := by
  classical
  have hp (x : L) :=
    exists_relative_immersion_patch_at (J := J) f hC
      (show (x : Smale.PlaneImmersion.Plane) ∉ C from fun hx =>
        Set.disjoint_left.mp hdis x.property hx)
  choose p T hcompatible hT hn hsub hfixed using hp
  have hcover : L ⊆ ⋃ x : L, interior (T x) := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, mem_interior_iff_mem_nhds.mpr (hn ⟨x, hx⟩)⟩
  obtain ⟨s, hs⟩ :=
    hL.elim_finite_subcover (fun x : L => interior (T x)) (fun _ => isOpen_interior) hcover
  obtain ⟨g, hg, -, hhom, hderiv⟩ :=
    exists_finite_patch_immersion (fun i : s => p i.1) (fun i : s => T i.1) (fun i => hT i.1)
      (fun i => hsub i.1) f hf (fun i => hcompatible i.1) hdim hK hinj (fun i => hfixed i.1)
      Finset.univ
  refine ⟨g, hg, hhom, ?_⟩
  intro x hx
  apply hderiv x
  rcases hx with hx | hx
  · exact Or.inl hx
  · obtain ⟨i, his, hxi⟩ := Set.mem_iUnion₂.mp (hs hx)
    exact Or.inr (Set.mem_iUnion₂.mpr ⟨⟨i, his⟩, Finset.mem_univ _, interior_subset hxi⟩)

private theorem Smale.ManifoldImmersion.exists_selfIntersection_removal_step_within_target
    {E G H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold J ∞ N] {ι : Type*} [Finite ι] {C K : Set E}
    (p : ι → Smale.GeneralPosition.MapAvoidancePatch 𝓘(ℝ, E) J (N := N) C) (i : ι) (f : C(E, N))
    (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) (hcompatible : ∀ j, (p j).Compatible f)
    (hdim : 2 * Module.finrank ℝ E < Module.finrank ℝ G) (hK : IsCompact K)
    (hinj : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x)) {D : Set E} {O : Set N}
    (hsource : (p i).chart.source ⊆ O) (hmaps : Set.MapsTo f D O) :
    ∃ g : C(E, N),
      ContMDiff 𝓘(ℝ, E) J ∞ g ∧
        (∀ j, (p j).Compatible g) ∧
          Smale.HomotopicRelWithin f g C D O ∧
            (∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J g x)) ∧
              ∀ x y, g x = g y → f x = f y ∧ (p i).cutoff x = (p i).cutoff y := by
  have hkeep :
    ∀ᶠ a in 𝓝 (0 : G),
      ∀ j, (p j).Compatible (Smale.ChartMapPerturbation.perturb (p i).chart f (p i).cutoff a) := by
    apply Filter.eventually_all.mpr
    intro j
    exact
      Smale.ChartMapPerturbation.eventually_maps_compact_into_open (p i).chart hf (p i).smooth
        (hcompatible i) (p j).compact.isCompact (p j).chart.open_source (hcompatible j)
  have hold :=
    Smale.ChartMapPerturbation.eventually_perturb_injective_derivative (p i).chart hf (p i).smooth
      (p i).compact (hcompatible i) hK hinj
  obtain ⟨δ, hδ, hδkeep⟩ := Metric.mem_nhds_iff.mp (hkeep.and hold)
  obtain ⟨r, hr, hvalid⟩ :=
    Smale.ChartMapPerturbation.exists_radius_valid (p i).chart hf (p i).smooth (p i).compact
      (hcompatible i)
  obtain ⟨a, ha, -, hsmooth, hremove⟩ :=
    Smale.ChartMapPerturbation.exists_small_collision_removing_parameter (p i).chart hf
      (p i).smooth (p i).compact (hcompatible i) hdim (lt_min hδ hr)
  have haδ : ‖a‖ < δ := (lt_min_iff.mp ha).1
  have har : ‖a‖ < r := (lt_min_iff.mp ha).2
  let g : C(E, N) := ⟨_, hsmooth.continuous⟩
  have hretained :=
    hδkeep (show a ∈ Metric.ball 0 δ by simpa only [Metric.mem_ball, dist_zero_right] using haδ)
  refine ⟨g, hsmooth, hretained.1, ?_, hretained.2, hremove⟩
  have hrel :=
    Smale.ChartMapPerturbation.homotopicRelWithin_of_source_subset (p i).chart hf (p i).smooth
      (hcompatible i) hvalid har hsource hmaps
  exact hrel.mono (fun x hx => (p i).fixed x hx) (Set.Subset.refl D) (Set.Subset.refl O)

private theorem Smale.ManifoldImmersion.exists_finite_selfIntersection_removal_within_target
    {E G H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold J ∞ N] {ι : Type*} [Finite ι] {C K : Set E}
    (p : ι → Smale.GeneralPosition.MapAvoidancePatch 𝓘(ℝ, E) J (N := N) C) (f : C(E, N))
    (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) (hcompatible : ∀ j, (p j).Compatible f)
    (hdim : 2 * Module.finrank ℝ E < Module.finrank ℝ G) (hK : IsCompact K)
    (hinj : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x)) {D : Set E} {O : Set N}
    (hsource : ∀ i, (p i).chart.source ⊆ O) (hmaps : Set.MapsTo f D O) (s : Finset ι) :
    ∃ g : C(E, N),
      ContMDiff 𝓘(ℝ, E) J ∞ g ∧
        (∀ j, (p j).Compatible g) ∧
          Smale.HomotopicRelWithin f g C D O ∧
            (∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J g x)) ∧
              ∀ x y, g x = g y → f x = f y ∧ ∀ i ∈ s, (p i).cutoff x = (p i).cutoff y := by
  classical
    induction s using Finset.induction_on with
  | empty =>
    exact
      ⟨f, hf, hcompatible, Smale.HomotopicRelWithin.refl f C hmaps, hinj, fun _ _ hxy =>
        ⟨hxy, fun _ hi => False.elim (Finset.notMem_empty _ hi)⟩⟩
  | @insert i s _ ih =>
    obtain ⟨g₁, hg₁, hc₁, hhom₁, hinj₁, hpair₁⟩ := ih
    obtain ⟨g₂, hg₂, hc₂, hhom₂, hinj₂, hpair₂⟩ :=
      exists_selfIntersection_removal_step_within_target p i g₁ hg₁ hc₁ hdim hK hinj₁ (hsource i)
        hhom₁.mapsTo_right
    refine ⟨g₂, hg₂, hc₂, hhom₁.trans hhom₂, hinj₂, ?_⟩
    intro x y hxy
    have hnew := hpair₂ x y hxy
    have hold := hpair₁ x y hnew.1
    refine ⟨hold.1, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hjs
    · exact hnew.2
    · exact hold.2 j hjs

private theorem Smale.ManifoldImmersion.exists_embedding_of_finite_separating_patches_within_target
    {E G H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold J ∞ N] [T2Space N] {ι : Type*} [Finite ι] {C K : Set E}
    (p : ι → Smale.GeneralPosition.MapAvoidancePatch 𝓘(ℝ, E) J (N := N) C) (f : C(E, N))
    (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) (hcompatible : ∀ j, (p j).Compatible f)
    (hdim : 2 * Module.finrank ℝ E < Module.finrank ℝ G) (hK : IsCompact K)
    (hinj : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x))
    (hseparate : ∀ x ∈ K, ∀ y ∈ K, x ≠ y → f x = f y → ∃ i, (p i).cutoff x ≠ (p i).cutoff y)
    {D : Set E} {O : Set N} (hsource : ∀ i, (p i).chart.source ⊆ O) (hmaps : Set.MapsTo f D O) :
    ∃ g : C(E, N),
      ContMDiff 𝓘(ℝ, E) J ∞ g ∧
        Smale.HomotopicRelWithin f g C D O ∧
          Topology.IsClosedEmbedding (fun x : K => g x) ∧
            ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J g x) := by
  classical
  let := Fintype.ofFinite ι
  obtain ⟨g, hg, -, hhom, hinjg, hpairs⟩ :=
    exists_finite_selfIntersection_removal_within_target p f hf hcompatible hdim hK hinj hsource
      hmaps Finset.univ
  refine ⟨g, hg, hhom, ?_, hinjg⟩
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  apply (g.continuous.comp continuous_subtype_val).isClosedEmbedding
  intro x y hxy
  apply Subtype.ext
  by_contra hne
  obtain ⟨hold, hcutoffs⟩ := hpairs x y hxy
  obtain ⟨i, hi⟩ := hseparate x x.property y y.property hne hold
  exact hi (hcutoffs i (Finset.mem_univ i))

private theorem Smale.ManifoldImmersion.exists_separating_patch_in_open {E G H N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [J.Boundaryless]
    [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] (f : C(E, N)) {C : Set E}
    (hC : IsClosed C) {x y : E} (hx : x ∉ C) (hxy : x ≠ y) {O : Set N} (hO : IsOpen O)
    (hxO : f x ∈ O) :
    ∃ p : Smale.GeneralPosition.MapAvoidancePatch 𝓘(ℝ, E) J (N := N) C,
      p.Compatible f ∧ p.cutoff x = 1 ∧ p.cutoff y = 0 ∧ p.chart.source ⊆ O := by
  classical
  let c₀ := NoExotic.modelChartPartialDiffeomorph (I := J) (f x)
  let c := Smale.PartialChart.restrictSource c₀ hO
  have hsource : f x ∈ c.source := ⟨mem_extChartAt_source (I := J) (f x), hxO⟩
  have hU : f ⁻¹' c.source ∩ (C ∪ { y })ᶜ ∈ 𝓝 x := by
    apply
      ((c.open_source.preimage f.continuous).inter
          ((hC.union isClosed_singleton).isOpen_compl)).mem_nhds
    exact ⟨hsource, fun h => h.elim hx (fun h => hxy h)⟩
  obtain ⟨β, -, hβ⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓘(ℝ, E)) x).mem_iff.mp hU
  let p : Smale.GeneralPosition.MapAvoidancePatch 𝓘(ℝ, E) J (N := N) C :=
    { chart := c
      cutoff := β
      smooth := β.contMDiff
      compact := β.hasCompactSupport
      fixed := fun z hz => image_eq_zero_of_notMem_tsupport (fun ht => (hβ ht).2 (Or.inl hz)) }
  refine ⟨p, (fun _ ht => (hβ ht).1), β.eq_one, ?_, fun _ hz => hz.2⟩
  exact image_eq_zero_of_notMem_tsupport (fun ht => (hβ ht).2 (Or.inr rfl))

private theorem Smale.ManifoldImmersion.exists_separating_patch_of_not_both_fixed_in_open
    {E G H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
    [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] (f : C(E, N))
    {C : Set E} (hC : IsClosed C) {x y : E} (hxy : x ≠ y) (hfixed : ¬(x ∈ C ∧ y ∈ C)) {O : Set N}
    (hO : IsOpen O) (hxO : x ∉ C → f x ∈ O) (hyO : y ∉ C → f y ∈ O) :
    ∃ p : Smale.GeneralPosition.MapAvoidancePatch 𝓘(ℝ, E) J (N := N) C,
      p.Compatible f ∧ p.cutoff x ≠ p.cutoff y ∧ p.chart.source ⊆ O := by
  by_cases hx : x ∈ C
  · have hy : y ∉ C := fun hy => hfixed ⟨hx, hy⟩
    obtain ⟨p, hp, hpy, hpx, hs⟩ :=
      exists_separating_patch_in_open (J := J) f hC hy hxy.symm hO (hyO hy)
    exact ⟨p, hp, by rw [hpx, hpy]; exact zero_ne_one, hs⟩
  · obtain ⟨p, hp, hpx, hpy, hs⟩ :=
      exists_separating_patch_in_open (J := J) f hC hx hxy hO (hxO hx)
    exact ⟨p, hp, by rw [hpx, hpy]; exact one_ne_zero, hs⟩

private theorem Smale.ManifoldImmersion.exists_open_injOn_of_injective_fderiv {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] {f : E → F} {U : Set E} {x : E} (hU : IsOpen U)
    (hx : x ∈ U) (hf : ContDiffOn ℝ ∞ f U) (hinj : Function.Injective (fderiv ℝ f x)) :
    ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ Set.InjOn f V := by
  obtain ⟨L, hL⟩ := ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional hinj
  have hdf := (hf.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hderiv : HasFDerivAt (L ∘ f) (ContinuousLinearMap.id ℝ E) x := by
    convert L.hasFDerivAt.comp x hdf.hasFDerivAt using 1
    ext v
    exact (hL v).symm
  have hcomp : ContDiffOn ℝ ∞ (L ∘ f) U := L.contDiff.comp_contDiffOn hf
  have hinv : (fderiv ℝ (L ∘ f) x).IsInvertible := by
    rw [hderiv.fderiv]
    exact ⟨ContinuousLinearEquiv.refl ℝ E, rfl⟩
  obtain ⟨φ, hxφ, hφU, hφeq⟩ := NoExotic.exists_partialDiffeomorph_of_contDiffOn hU hx hcomp hinv
  refine ⟨φ.source, φ.open_source, hxφ, hφU, ?_⟩
  intro y hy z hz hyz
  apply φ.toPartialEquiv.injOn hy hz
  rw [hφeq]
  exact congrArg L hyz

private theorem
    Smale.ManifoldImmersion.exists_open_injOn_of_injective_nativeDerivative_on {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {G H N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold J ∞ N] {f : E → N} {W : Set E} (hW : IsOpen W) (hf : ContMDiffOn 𝓘(ℝ, E) J ∞ f W)
    {x : E} (hxW : x ∈ W) (hinj : Function.Injective (mfderiv 𝓘(ℝ, E) J f x)) :
    ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ V ⊆ W ∧ Set.InjOn f V := by
  let c := NoExotic.modelChartPartialDiffeomorph (I := J) (f x)
  have hx : f x ∈ c.source := mem_extChartAt_source (f x)
  let U := W ∩ f ⁻¹' c.source
  have hU : IsOpen U := hf.continuousOn.isOpen_inter_preimage hW c.open_source
  have hc : ContDiffOn ℝ ∞ (c ∘ f) U :=
    (c.contMDiffOn_toFun.comp (hf.mono Set.inter_subset_left) (fun _ h => h.2)).contDiffOn
  have hfx := hf.contMDiffAt (hW.mem_nhds hxW)
  have hi := (injective_fderiv_chart_iff c (hfx.mdifferentiableAt (by simp)) hx).mpr hinj
  obtain ⟨V, hV, hxV, hVU, hinjV⟩ := exists_open_injOn_of_injective_fderiv hU ⟨hxW, hx⟩ hc hi
  exact
    ⟨V, hV, hxV, hVU.trans Set.inter_subset_left, fun _ hy _ hz heq =>
      hinjV hy hz (congrArg c heq)⟩

private theorem Smale.ManifoldImmersion.exists_open_injOn_of_injective_nativeDerivative {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {G H N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold J ∞ N] {f : E → N} (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) {x : E}
    (hinj : Function.Injective (mfderiv 𝓘(ℝ, E) J f x)) :
    ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ Set.InjOn f V := by
  obtain ⟨V, hV, hxV, _, hinjV⟩ :=
    exists_open_injOn_of_injective_nativeDerivative_on isOpen_univ hf.contMDiffOn (Set.mem_univ x)
      hinj
  exact ⟨V, hV, hxV, hinjV⟩

private theorem Smale.ManifoldImmersion.exists_open_injOn_near_compact_on {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {G H N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold J ∞ N] [T2Space N] {f : E → N} {W : Set E} (hW : IsOpen W)
    (hf : ContMDiffOn 𝓘(ℝ, E) J ∞ f W) {K : Set E} (hK : IsCompact K) (hKW : K ⊆ W)
    (hinj : Set.InjOn f K) (hi : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x)) :
    ∃ V : Set E, IsOpen V ∧ K ⊆ V ∧ V ⊆ W ∧ Set.InjOn f V := by
  have hc : ∀ x ∈ K, ContinuousAt f x := fun x hx =>
    hf.continuousOn.continuousAt (hW.mem_nhds (hKW hx))
  have hlocal : ∀ x ∈ K, ∃ V ∈ nhds x, Set.InjOn f V := by
    intro x hx
    obtain ⟨V, hV, hxV, _, hinjV⟩ :=
      exists_open_injOn_of_injective_nativeDerivative_on hW hf (hKW hx) (hi x hx)
    exact ⟨V, hV.mem_nhds hxV, hinjV⟩
  obtain ⟨V, hV, hKV, hinjV⟩ := hinj.exists_isOpen_superset hK hc hlocal
  exact
    ⟨V ∩ W, hV.inter hW, fun _ hx => ⟨hKV hx, hKW hx⟩, Set.inter_subset_right,
      hinjV.mono Set.inter_subset_left⟩

private theorem Smale.ManifoldImmersion.exists_open_embedded_immersive_neighborhood {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {G H N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold J ∞ N] [T2Space N] {f : E → N} {W : Set E} (hW : IsOpen W)
    (hf : ContMDiffOn 𝓘(ℝ, E) J ∞ f W) {K : Set E} (hK : IsCompact K) (hKW : K ⊆ W)
    (hinj : Set.InjOn f K) (hi : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x)) :
    ∃ V : Set E,
      IsOpen V ∧
        K ⊆ V ∧ V ⊆ W ∧ Set.InjOn f V ∧ ∀ x ∈ V, Function.Injective (mfderiv 𝓘(ℝ, E) J f x) := by
  let O := {x : E | x ∈ W ∧ Function.Injective (mfderiv 𝓘(ℝ, E) J f x)}
  have hO : IsOpen O := isOpen_injective_derivative_on hW hf
  have hOW : O ⊆ W := fun _ hx => hx.1
  obtain ⟨V, hV, hKV, hVO, hinjV⟩ :=
    exists_open_injOn_near_compact_on hO (hf.mono hOW) hK (fun x hx => ⟨hKW hx, hi x hx⟩) hinj hi
  exact ⟨V, hV, hKV, hVO.trans hOW, hinjV, fun x hx => (hVO hx).2⟩

private theorem
    Smale.ManifoldImmersion.exists_open_injOn_near_compact {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {G H N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
    [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N]
    {f : E → N} (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) {K : Set E} (hK : IsCompact K)
    (hinj : Set.InjOn f K) (hi : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x)) :
    ∃ V : Set E, IsOpen V ∧ K ⊆ V ∧ Set.InjOn f V := by
  apply hinj.exists_isOpen_superset hK (fun _ _ => hf.continuous.continuousAt)
  intro x hx
  obtain ⟨V, hV, hxV, hinjV⟩ := exists_open_injOn_of_injective_nativeDerivative hf (hi x hx)
  exact ⟨V, hV.mem_nhds hxV, hinjV⟩

private def
    Smale.ManifoldImmersion.doublePoints {X N : Type*} (f : X → N) (K : Set X) : Set (X × X) :=
  {q | q.1 ∈ K ∧ q.2 ∈ K ∧ q.1 ≠ q.2 ∧ f q.1 = f q.2}

private theorem Smale.ManifoldImmersion.isCompact_doublePoints_of_locally_injective {X N : Type*}
    [TopologicalSpace X] [TopologicalSpace N] [T2Space N] {f : X → N} (hf : Continuous f)
    {K : Set X} (hK : IsCompact K)
    (hlocal : ∀ x ∈ K, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ Set.InjOn f U) :
    IsCompact (doublePoints f K) := by
  classical
  choose U hU hmem hinj using (fun x : K => hlocal x x.property)
  let V : Set (X × X) := ⋃ x : K, (U x) ×ˢ (U x)
  have hV : IsOpen V := isOpen_iUnion (fun x => (hU x).prod (hU x))
  have hclosed : IsClosed {q : X × X | f q.1 = f q.2} :=
    isClosed_eq (hf.comp continuous_fst) (hf.comp continuous_snd)
  have heq : doublePoints f K = ((K ×ˢ K) ∩ {q : X × X | f q.1 = f q.2}) ∩ Vᶜ := by
    ext q
    constructor
    · rintro ⟨hx, hy, hne, hcoll⟩
      refine ⟨⟨⟨hx, hy⟩, hcoll⟩, ?_⟩
      intro hv
      obtain ⟨x, hxU, hyU⟩ := Set.mem_iUnion.mp hv
      exact hne (hinj x hxU hyU hcoll)
    · rintro ⟨⟨⟨hx, hy⟩, hcoll⟩, hv⟩
      refine ⟨hx, hy, ?_, hcoll⟩
      intro hxy
      apply hv
      apply Set.mem_iUnion.mpr
      refine ⟨⟨q.1, hx⟩, hmem ⟨q.1, hx⟩, ?_⟩
      rw [← hxy]
      exact hmem ⟨q.1, hx⟩
  rw [heq]
  exact ((hK.prod hK).inter_right hclosed).inter_right hV.isClosed_compl

private theorem Smale.ManifoldImmersion.isCompact_doublePoints_of_injective_nativeDerivative
    {E G H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold J ∞ N] [T2Space N] {f : E → N} (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) {K : Set E}
    (hK : IsCompact K) (hinj : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x)) :
    IsCompact (doublePoints f K) :=
  isCompact_doublePoints_of_locally_injective hf.continuous hK
    (fun _ hx => exists_open_injOn_of_injective_nativeDerivative hf (hinj _ hx))

private theorem Smale.ManifoldImmersion.exists_compact_embedding_of_immersion_within_target
    {E G H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold J ∞ N] [T2Space N] (f : C(E, N)) (hf : ContMDiff 𝓘(ℝ, E) J ∞ f)
    (hdim : 2 * Module.finrank ℝ E < Module.finrank ℝ G) {K C : Set E} (hK : IsCompact K)
    (hinj : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x)) (hC : IsClosed C)
    (hfixed : Set.InjOn f (K ∩ C)) {O : Set N} (hO : IsOpen O) (hmaps : Set.MapsTo f (K \ C) O) :
    ∃ g : C(E, N),
      ContMDiff 𝓘(ℝ, E) J ∞ g ∧
        Smale.HomotopicRelWithin f g C (K \ C) O ∧
          Topology.IsClosedEmbedding (fun x : K => g x) ∧
            ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J g x) := by
  classical
  let bad := doublePoints f K
  have hbad : IsCompact bad := isCompact_doublePoints_of_injective_nativeDerivative hf hK hinj
  have hp (q : bad) :
    ∃ p : Smale.GeneralPosition.MapAvoidancePatch 𝓘(ℝ, E) J (N := N) C,
      p.Compatible f ∧ p.cutoff q.1.1 ≠ p.cutoff q.1.2 ∧ p.chart.source ⊆ O := by
    have hq := q.property
    rcases hq with ⟨hx, hy, hne, heq⟩
    have hnot : ¬(q.1.1 ∈ C ∧ q.1.2 ∈ C) := by
      rintro ⟨hxC, hyC⟩
      exact hne (hfixed ⟨hx, hxC⟩ ⟨hy, hyC⟩ heq)
    exact
      exists_separating_patch_of_not_both_fixed_in_open f hC hne hnot hO
        (fun hxC => hmaps ⟨hx, hxC⟩) (fun hyC => hmaps ⟨hy, hyC⟩)
  choose p hpcompatible hpactive hpsource using hp
  let U (q : bad) : Set (E × E) := {r | (p q).cutoff r.1 ≠ (p q).cutoff r.2}
  have hU (q : bad) : IsOpen (U q) :=
    isOpen_ne_fun ((p q).smooth.continuous.comp continuous_fst)
      ((p q).smooth.continuous.comp continuous_snd)
  have hcover : bad ⊆ ⋃ q : bad, U q := by
    intro q hq
    exact Set.mem_iUnion.mpr ⟨⟨q, hq⟩, hpactive ⟨q, hq⟩⟩
  obtain ⟨s, hs⟩ := hbad.elim_finite_subcover U hU hcover
  refine
    exists_embedding_of_finite_separating_patches_within_target (fun i : s => p i.1) f hf
      (fun i => hpcompatible i.1) hdim hK hinj ?_ (fun i => hpsource i.1) hmaps
  intro x hx y hy hne heq
  have hxy : (x, y) ∈ bad := ⟨hx, hy, hne, heq⟩
  obtain ⟨i, hi, hsep⟩ := Set.mem_iUnion₂.mp (hs hxy)
  exact ⟨⟨i, hi⟩, hsep⟩

private theorem Smale.ManifoldImmersion.exists_compact_embedding_of_immersion {E G H N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
    [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N]
    (f : C(E, N)) (hf : ContMDiff 𝓘(ℝ, E) J ∞ f)
    (hdim : 2 * Module.finrank ℝ E < Module.finrank ℝ G) {K C : Set E} (hK : IsCompact K)
    (hinj : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x)) (hC : IsClosed C)
    (hfixed : Set.InjOn f (K ∩ C)) :
    ∃ g : C(E, N),
      ContMDiff 𝓘(ℝ, E) J ∞ g ∧
        f.HomotopicRel g C ∧
          Topology.IsClosedEmbedding (fun x : K => g x) ∧
            ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J g x) := by
  obtain ⟨g, hg, hrel, he, hi⟩ :=
    exists_compact_embedding_of_immersion_within_target f hf hdim hK hinj hC hfixed isOpen_univ
      (Set.mapsTo_univ f (K \ C))
  exact ⟨g, hg, hrel.homotopicRel, he, hi⟩

private theorem Smale.ManifoldImmersion.exists_relative_compact_embedding {G H N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold J ∞ N] [T2Space N] (f : C(Smale.PlaneImmersion.Plane, N))
    (hf : ContMDiff 𝓘(ℝ, Smale.PlaneImmersion.Plane) J ∞ f) (hdim : 5 ≤ Module.finrank ℝ G)
    {K C : Set Smale.PlaneImmersion.Plane} (hK : IsCompact K) (hC : IsClosed C)
    (hfixed : Set.InjOn f (K ∩ C))
    (hderiv : ∀ x ∈ K ∩ C, Function.Injective (mfderiv 𝓘(ℝ, Smale.PlaneImmersion.Plane) J f x)) :
    ∃ g : C(Smale.PlaneImmersion.Plane, N),
      ContMDiff 𝓘(ℝ, Smale.PlaneImmersion.Plane) J ∞ g ∧
        f.HomotopicRel g C ∧
          Topology.IsClosedEmbedding (fun x : K => g x) ∧
            ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, Smale.PlaneImmersion.Plane) J g x) := by
  let U : Set Smale.PlaneImmersion.Plane :=
    {x | Function.Injective (mfderiv 𝓘(ℝ, Smale.PlaneImmersion.Plane) J f x)}
  have hU : IsOpen U := isOpen_injective_derivative hf
  have hCU : K ∩ C ⊆ U := fun x hx => hderiv x hx
  obtain ⟨D, hD, hCD, hDU⟩ := exists_compact_between (hK.inter_right hC) hU hCU
  let L := K \ interior D
  have hL : IsCompact L := hK.inter_right isOpen_interior.isClosed_compl
  have hdis : Disjoint L C := Set.disjoint_left.mpr (fun _ hx hxC => hx.2 (hCD ⟨hx.1, hxC⟩))
  obtain ⟨g₁, hg₁, hhom₁, hinj₁⟩ :=
    exists_immersion_on_compact_rel f hf hdim hD hL (fun x hx => hDU hx) hC hdis
  have hKinj : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, Smale.PlaneImmersion.Plane) J g₁ x) := by
    intro x hx
    apply hinj₁ x
    by_cases hxD : x ∈ D
    · exact Or.inl hxD
    · exact Or.inr ⟨hx, fun hi => hxD (interior_subset hi)⟩
  have hfixed₁ : Set.InjOn g₁ (K ∩ C) := by
    intro x hx y hy hxy
    apply hfixed hx hy
    rw [hhom₁.fst_eq_snd hx.2, hhom₁.fst_eq_snd hy.2]
    exact hxy
  have hd : 2 * Module.finrank ℝ Smale.PlaneImmersion.Plane < Module.finrank ℝ G := by
    simp only [Smale.PlaneImmersion.Plane, Module.finrank_prod, Module.finrank_self]
    omega
  obtain ⟨g₂, hg₂, hhom₂, hemb, hinj₂⟩ :=
    exists_compact_embedding_of_immersion g₁ hg₁ hd hK hKinj hC hfixed₁
  exact ⟨g₂, hg₂, hhom₁.trans hhom₂, hemb, hinj₂⟩

private theorem Smale.ManifoldImmersion.injective_mfderiv_comp_linearEquiv_iff {E E' G H N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
    [TopologicalSpace N] [ChartedSpace H N] (e : E' ≃L[ℝ] E) {f : E → N} {x : E'}
    (hf : MDifferentiableAt 𝓘(ℝ, E) J f (e x)) :
    Function.Injective (mfderiv 𝓘(ℝ, E') J (f ∘ e) x) ↔
      Function.Injective (mfderiv 𝓘(ℝ, E) J f (e x)) := by
  have he : mfderiv 𝓘(ℝ, E') 𝓘(ℝ, E) e x = e.toContinuousLinearMap := by
    rw [mfderiv_eq_fderiv]
    exact e.toContinuousLinearMap.fderiv
  have hesmooth : ContMDiff 𝓘(ℝ, E') 𝓘(ℝ, E) ∞ e := e.contDiff.contMDiff
  rw [mfderiv_comp x hf (hesmooth.mdifferentiableAt (by simp)), he]
  constructor
  · intro h v w hvw
    apply e.symm.injective
    apply h
    change (mfderiv 𝓘(ℝ, E) J f (e x)) (e (e.symm v)) = (mfderiv 𝓘(ℝ, E) J f (e x)) (e (e.symm w))
    exact
      (congrArg (mfderiv 𝓘(ℝ, E) J f (e x)) (e.apply_symm_apply (v : E))).trans
        (hvw.trans (congrArg (mfderiv 𝓘(ℝ, E) J f (e x)) (e.apply_symm_apply (w : E))).symm)
  · exact fun h => h.comp e.injective

private theorem
    Smale.ManifoldImmersion.exists_relative_compact_embedding_twoDimensional {E G H N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [TopologicalSpace N] [ChartedSpace H N]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ G] [J.Boundaryless] [IsManifold J ∞ N]
    [T2Space N] (f : C(E, N)) (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) (hsourceDim : Module.finrank ℝ E = 2)
    (hdim : 5 ≤ Module.finrank ℝ G) {K C : Set E} (hK : IsCompact K) (hC : IsClosed C)
    (hfixed : Set.InjOn f (K ∩ C))
    (hderiv : ∀ x ∈ K ∩ C, Function.Injective (mfderiv 𝓘(ℝ, E) J f x)) :
    ∃ g : C(E, N),
      ContMDiff 𝓘(ℝ, E) J ∞ g ∧
        f.HomotopicRel g C ∧
          Topology.IsClosedEmbedding (fun x : K => g x) ∧
            ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J g x) := by
  let e : Smale.PlaneImmersion.Plane ≃L[ℝ] E :=
    ContinuousLinearEquiv.ofFinrankEq
      (by
        simp only [Smale.PlaneImmersion.Plane, Module.finrank_prod, Module.finrank_self]
        omega)
  let fp : C(Smale.PlaneImmersion.Plane, N) := ⟨f ∘ e, f.continuous.comp e.continuous⟩
  have hfp : ContMDiff 𝓘(ℝ, Smale.PlaneImmersion.Plane) J ∞ fp := hf.comp e.contDiff.contMDiff
  have hKp : IsCompact (e ⁻¹' K) := e.toHomeomorph.isCompact_preimage.mpr hK
  have hCp : IsClosed (e ⁻¹' C) := hC.preimage e.continuous
  have hfixedp : Set.InjOn fp ((e ⁻¹' K) ∩ (e ⁻¹' C)) := by
    intro x hx y hy hxy
    exact e.injective (hfixed ⟨hx.1, hx.2⟩ ⟨hy.1, hy.2⟩ hxy)
  have hderivp :
    ∀ x ∈ (e ⁻¹' K) ∩ (e ⁻¹' C),
      Function.Injective (mfderiv 𝓘(ℝ, Smale.PlaneImmersion.Plane) J fp x) := by
    intro x hx
    exact
      (injective_mfderiv_comp_linearEquiv_iff e (hf.mdifferentiableAt (by simp))).mpr
        (hderiv (e x) ⟨hx.1, hx.2⟩)
  obtain ⟨gp, hgp, ⟨Hrel⟩, hembp, hgpderiv⟩ :=
    exists_relative_compact_embedding fp hfp hdim hKp hCp hfixedp hderivp
  let g : C(E, N) := ⟨gp ∘ e.symm, gp.continuous.comp e.symm.continuous⟩
  have hg : ContMDiff 𝓘(ℝ, E) J ∞ g := hgp.comp e.symm.contDiff.contMDiff
  have hpreK (x : E) (hx : x ∈ K) : e.symm x ∈ e ⁻¹' K := by
    change e (e.symm x) ∈ K
    simpa only [e.apply_symm_apply] using hx
  refine ⟨g, hg, ?_, ?_, ?_⟩
  · refine
      ⟨{  toFun := fun q => Hrel (q.1, e.symm q.2)
          continuous_toFun :=
            Hrel.continuous.comp (continuous_fst.prodMk (e.symm.continuous.comp continuous_snd))
          map_zero_left := ?_
          map_one_left := ?_
          prop' := ?_ }⟩
    · intro x
      rw [Hrel.apply_zero]
      exact congrArg f (e.apply_symm_apply x)
    · intro x
      exact Hrel.apply_one (e.symm x)
    · intro t x hx
      change Hrel (t, e.symm x) = f x
      have hpreC : e.symm x ∈ e ⁻¹' C := by
        change e (e.symm x) ∈ C
        simpa only [e.apply_symm_apply] using hx
      rw [Hrel.eq_fst t hpreC]
      exact congrArg f (e.apply_symm_apply x)
  · let : CompactSpace K := isCompact_iff_compactSpace.mp hK
    apply (g.continuous.comp continuous_subtype_val).isClosedEmbedding
    intro x y hxy
    apply Subtype.ext
    apply e.symm.injective
    have hpeq : gp (e.symm x) = gp (e.symm y) := hxy
    exact
      congrArg Subtype.val
        (hembp.injective (a₁ := ⟨e.symm x, hpreK x x.property⟩) (a₂ :=
          ⟨e.symm y, hpreK y y.property⟩) hpeq)
  · intro x hx
    exact
      (injective_mfderiv_comp_linearEquiv_iff e.symm (hgp.mdifferentiableAt (by simp))).mpr
        (hgpderiv (e.symm x) (hpreK x hx))

private theorem Smale.ManifoldImmersion.exists_embedded_image_avoidance_relative_neighborhood
    {E E' G H H' Y N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    {J : ModelWithCorners ℝ G H} {I' : ModelWithCorners ℝ E' H'} [J.Boundaryless]
    [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y] [LindelofSpace (E × Y)]
    [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N] (f : C(E, N))
    (g : C(Y, N)) (A : Set Y) (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hclosed : IsClosed (g '' A)) (hself : 2 * Module.finrank ℝ E < Module.finrank ℝ G)
    (hobstacle : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ G) {K C B : Set E}
    (hK : IsCompact K) (hC : IsClosed C) (hBC : B ⊆ interior C) (hinj : Set.InjOn f K)
    (hderiv : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x))
    (hclean : ∀ x ∈ K ∩ C, x ∉ B → f x ∉ g '' A) {O : Set N} (hO : IsOpen O)
    (hmaps : Set.MapsTo f K O) :
    ∃ f' : C(E, N),
      ContMDiff 𝓘(ℝ, E) J ∞ f' ∧
        f.HomotopicRel f' C ∧
          Topology.IsClosedEmbedding (fun x : K => f' x) ∧
            (∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f' x)) ∧
              Set.MapsTo f' K O ∧ ∀ x ∈ K \ B, f' x ∉ g '' A := by
  let L : Set E := K \ interior C
  have hL : IsCompact L := hK.inter_right isOpen_interior.isClosed_compl
  have hfixed : ∀ x ∈ L ∩ C, f x ∉ g '' A := by
    intro x hx
    exact hclean x ⟨hx.1.1, hx.2⟩ (fun hxB => hx.1.2 (hBC hxB))
  obtain ⟨f', hf', hhom, hemb, hderiv', -, hmaps', havoid⟩ :=
    exists_embedded_avoidance_on_compact_of_isClosed_image f g A hf hg hclosed hself hobstacle hK
      hL hC hinj hderiv hfixed hO hmaps
  refine ⟨f', hf', hhom, hemb, hderiv', hmaps', ?_⟩
  intro x hx
  by_cases hxC : x ∈ C
  · exact havoid x (Or.inl (hclean x ⟨hx.1, hxC⟩ hx.2))
  · exact havoid x (Or.inr ⟨hx.1, fun hi => hxC (interior_subset hi)⟩)

private theorem
    Smale.ManifoldImmersion.exists_embedded_avoidance_relative_neighborhood_of_isClosed_range
    {E E' G H H' Y N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    {J : ModelWithCorners ℝ G H} {I' : ModelWithCorners ℝ E' H'} [J.Boundaryless]
    [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y] [LindelofSpace (E × Y)]
    [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N] (f : C(E, N))
    (g : C(Y, N)) (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hclosed : IsClosed (Set.range g)) (hself : 2 * Module.finrank ℝ E < Module.finrank ℝ G)
    (hobstacle : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ G) {K C B : Set E}
    (hK : IsCompact K) (hC : IsClosed C) (hBC : B ⊆ interior C) (hinj : Set.InjOn f K)
    (hderiv : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x))
    (hclean : ∀ x ∈ K ∩ C, x ∉ B → f x ∉ Set.range g) :
    ∃ f' : C(E, N),
      ContMDiff 𝓘(ℝ, E) J ∞ f' ∧
        f.HomotopicRel f' C ∧
          Topology.IsClosedEmbedding (fun x : K => f' x) ∧
            (∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f' x)) ∧
              ∀ x ∈ K \ B, f' x ∉ Set.range g := by
  obtain ⟨f', hf', hhom, hemb, hd, -, havoid⟩ :=
    exists_embedded_image_avoidance_relative_neighborhood f g Set.univ hf hg
      (by simpa only [Set.image_univ] using hclosed) hself hobstacle hK hC hBC hinj hderiv
      (by simpa only [Set.image_univ] using hclean) isOpen_univ (fun _ _ => Set.mem_univ _)
  refine ⟨f', hf', hhom, hemb, hd, ?_⟩
  simpa only [Set.image_univ] using havoid

private theorem
  Smale.ManifoldImmersion.exists_relative_embedded_avoidance_of_clean_neighborhood_of_isClosed_range
    {E E' G H H' Y N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    {J : ModelWithCorners ℝ G H} {I' : ModelWithCorners ℝ E' H'} [J.Boundaryless]
    [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y] [LindelofSpace (E × Y)]
    [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N] (f : C(E, N))
    (g : C(Y, N)) (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hclosed : IsClosed (Set.range g)) (hsourceDim : Module.finrank ℝ E = 2)
    (hdim : 5 ≤ Module.finrank ℝ G)
    (hobstacle : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ G) {K C B : Set E}
    (hK : IsCompact K) (hC : IsClosed C) (hBC : B ⊆ interior C) (hinj : Set.InjOn f (K ∩ C))
    (hderiv : ∀ x ∈ K ∩ C, Function.Injective (mfderiv 𝓘(ℝ, E) J f x))
    (hclean : ∀ x ∈ K ∩ C, x ∉ B → f x ∉ Set.range g) :
    ∃ f' : C(E, N),
      ContMDiff 𝓘(ℝ, E) J ∞ f' ∧
        f.HomotopicRel f' C ∧
          Topology.IsClosedEmbedding (fun x : K => f' x) ∧
            (∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f' x)) ∧
              ∀ x ∈ K \ B, f' x ∉ Set.range g := by
  obtain ⟨f₁, hf₁, hhom₁, hemb₁, hderiv₁⟩ :=
    exists_relative_compact_embedding_twoDimensional f hf hsourceDim hdim hK hC hinj hderiv
  have hinj₁ : Set.InjOn f₁ K := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (hemb₁.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)
  have hclean₁ : ∀ x ∈ K ∩ C, x ∉ B → f₁ x ∉ Set.range g := by
    intro x hx hxB
    rw [← hhom₁.fst_eq_snd hx.2]
    exact hclean x hx hxB
  have hself : 2 * Module.finrank ℝ E < Module.finrank ℝ G := by omega
  obtain ⟨f₂, hf₂, hhom₂, hemb₂, hderiv₂, havoid₂⟩ :=
    exists_embedded_avoidance_relative_neighborhood_of_isClosed_range f₁ g hf₁ hg hclosed hself
      hobstacle hK hC hBC hinj₁ hderiv₁ hclean₁
  exact ⟨f₂, hf₂, hhom₁.trans hhom₂, hemb₂, hderiv₂, havoid₂⟩

private theorem Smale.ManifoldImmersion.exists_embedded_avoidance_relative_neighborhood
    {E E' G H H' Y N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    {J : ModelWithCorners ℝ G H} {I' : ModelWithCorners ℝ E' H'} [J.Boundaryless]
    [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y] [LindelofSpace (E × Y)]
    [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N] [CompactSpace Y]
    (f : C(E, N)) (g : C(Y, N)) (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hself : 2 * Module.finrank ℝ E < Module.finrank ℝ G)
    (hobstacle : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ G) {K C B : Set E}
    (hK : IsCompact K) (hC : IsClosed C) (hBC : B ⊆ interior C) (hinj : Set.InjOn f K)
    (hderiv : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x))
    (hclean : ∀ x ∈ K ∩ C, x ∉ B → f x ∉ Set.range g) :
    ∃ f' : C(E, N),
      ContMDiff 𝓘(ℝ, E) J ∞ f' ∧
        f.HomotopicRel f' C ∧
          Topology.IsClosedEmbedding (fun x : K => f' x) ∧
            (∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f' x)) ∧
              ∀ x ∈ K \ B, f' x ∉ Set.range g :=
  exists_embedded_avoidance_relative_neighborhood_of_isClosed_range f g hf hg
    (isCompact_range g.continuous).isClosed hself hobstacle hK hC hBC hinj hderiv hclean

private def Smale.OpenObstacle.source {Y N : Type*} [TopologicalSpace Y] [TopologicalSpace N]
    (g : C(Y, N)) (U : TopologicalSpace.Opens N) : TopologicalSpace.Opens Y :=
  ⟨g ⁻¹' (U : Set N), U.isOpen.preimage g.continuous⟩

private def Smale.OpenObstacle.restrict {Y N : Type*} [TopologicalSpace Y] [TopologicalSpace N]
    (g : C(Y, N)) (U : TopologicalSpace.Opens N) : C(source g U, U)
    where
  toFun y := ⟨g y, y.property⟩
  continuous_toFun := (g.continuous.comp continuous_subtype_val).subtype_mk _

private theorem Smale.OpenObstacle.mem_range_restrict_iff {Y N : Type*} [TopologicalSpace Y]
    [TopologicalSpace N] (g : C(Y, N)) (U : TopologicalSpace.Opens N) (x : U) :
    x ∈ Set.range (Smale.OpenObstacle.restrict g U) ↔ (x : N) ∈ Set.range g := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, congrArg Subtype.val hy⟩
  · rintro ⟨y, hy⟩
    have hyU : y ∈ source g U := by
      change g y ∈ U
      exact hy.symm ▸ x.property
    exact ⟨⟨y, hyU⟩, Subtype.ext hy⟩

private theorem
    Smale.OpenObstacle.range_restrict {Y N : Type*} [TopologicalSpace Y] [TopologicalSpace N]
    (g : C(Y, N)) (U : TopologicalSpace.Opens N) :
    Set.range (Smale.OpenObstacle.restrict g U) = (Subtype.val : U → N) ⁻¹' Set.range g := by
  ext x
  exact mem_range_restrict_iff g U x

private theorem Smale.OpenObstacle.isClosed_range_restrict {Y N : Type*} [TopologicalSpace Y]
    [TopologicalSpace N] (g : C(Y, N)) (U : TopologicalSpace.Opens N)
    (hclosed : IsClosed (Set.range g)) : IsClosed (Set.range (Smale.OpenObstacle.restrict g U)) :=
  by
  rw [Smale.OpenObstacle.range_restrict]
  exact hclosed.preimage continuous_subtype_val

private theorem
    Smale.OpenObstacle.image_restrict {Y N : Type*} [TopologicalSpace Y] [TopologicalSpace N]
    (g : C(Y, N)) (U : TopologicalSpace.Opens N) (A : Set Y) :
    Smale.OpenObstacle.restrict g U '' ((Subtype.val : source g U → Y) ⁻¹' A) =
      (Subtype.val : U → N) ⁻¹' (g '' A) := by
  ext x
  constructor
  · rintro ⟨y, hy, heq⟩
    exact ⟨y, hy, congrArg Subtype.val heq⟩
  · rintro ⟨y, hy, heq⟩
    have hyU : y ∈ source g U := by
      change g y ∈ U
      exact heq.symm ▸ x.property
    exact ⟨⟨y, hyU⟩, hy, Subtype.ext heq⟩

private theorem Smale.OpenObstacle.isClosed_image_restrict {Y N : Type*} [TopologicalSpace Y]
    [TopologicalSpace N] (g : C(Y, N)) (U : TopologicalSpace.Opens N) (A : Set Y)
    (hclosed : IsClosed (g '' A)) :
    IsClosed (Smale.OpenObstacle.restrict g U '' ((Subtype.val : source g U → Y) ⁻¹' A)) := by
  rw [Smale.OpenObstacle.image_restrict]
  exact hclosed.preimage continuous_subtype_val

private theorem
    Smale.OpenObstacle.contMDiff_restrict {E' G H H' Y N : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
    [TopologicalSpace H'] {J : ModelWithCorners ℝ G H} {I' : ModelWithCorners ℝ E' H'}
    [TopologicalSpace Y] [ChartedSpace H' Y] [TopologicalSpace N] [ChartedSpace H N] (g : C(Y, N))
    (U : TopologicalSpace.Opens N) (hg : ContMDiff I' J ∞ g) :
    ContMDiff I' J ∞ (Smale.OpenObstacle.restrict g U) := by
  apply (ContMDiff.subtypeVal_comp_iff U (Smale.OpenObstacle.restrict g U)).mp
  exact hg.comp contMDiff_subtype_val

private theorem MorseCancel.exists_smooth_path_avoiding_closed_image {E G H H' N Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G H'} [J.Boundaryless]
    [TopologicalSpace Y] [ChartedSpace H Y] [IsManifold I ∞ Y] [SecondCountableTopology Y]
    [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] {x y : N}
    (γ : Path x y) (g : C(Y, N)) (hg : ContMDiff I J ∞ g) (hclosed : IsClosed (Set.range g))
    (hdim : 1 + Module.finrank ℝ E < Module.finrank ℝ G) (hx : x ∉ Set.range g)
    (hy : y ∉ Set.range g) : ∃ η : Path x y, ContMDiff (𝓡∂ 1) J ∞ η ∧ ∀ t, η t ∉ Set.range g := by
  obtain ⟨f, hf, hf0, hf1⟩ := Smale.exists_smooth_connecting_curve (J := J) γ
  let fI : C(unitInterval, N) := ⟨fun t => f t, f.continuous.comp continuous_subtype_val⟩
  have hfI : ContMDiff (𝓡∂ 1) J ∞ fI := hf.comp contMDiff_subtypeVal_Icc
  have hdim' :
    Module.finrank ℝ (EuclideanSpace ℝ (Fin 1)) + Module.finrank ℝ E < Module.finrank ℝ G := by
    simpa only [finrank_euclideanSpace_fin] using hdim
  have hfixed : ∀ t ∈ ({0, 1} : Set unitInterval), fI t ∉ Set.range g := by
    intro t ht
    rcases ht with rfl | ht
    · change f 0 ∉ Set.range g
      rwa [hf0]
    · have ht1 : t = 1 := ht
      subst t
      change f 1 ∉ Set.range g
      rwa [hf1]
  obtain ⟨f', hf', hrel, hdisjoint⟩ :=
    Smale.GeneralPosition.exists_disjoint_smooth_map_homotopicRel_of_isClosed_range fI g hfI hg
      hclosed hdim' ((Set.finite_singleton (1 : unitInterval)).insert 0).isClosed hfixed
  have h0 : f' 0 = x := (hrel.fst_eq_snd (by simp)).symm.trans hf0
  have h1 : f' 1 = y := (hrel.fst_eq_snd (by simp)).symm.trans hf1
  let η : Path x y := { toContinuousMap := f', source' := h0, target' := h1 }
  exact ⟨η, hf', fun t ht => Set.disjoint_left.mp hdisjoint ⟨t, rfl⟩ ht⟩

private theorem MorseCancel.exists_smooth_path_avoiding_closed_image_in_open {E G H H' N Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G H'} [J.Boundaryless]
    [TopologicalSpace Y] [ChartedSpace H Y] [IsManifold I ∞ Y] [SecondCountableTopology Y]
    [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
    (U : TopologicalSpace.Opens N) {x y : U} (γ : Path x y) (g : C(Y, N)) (hg : ContMDiff I J ∞ g)
    (hclosed : IsClosed (Set.range g)) (hdim : 1 + Module.finrank ℝ E < Module.finrank ℝ G)
    (hx : x.val ∉ Set.range g) (hy : y.val ∉ Set.range g) :
    ∃ η : Path x y, ContMDiff (𝓡∂ 1) J ∞ η ∧ ∀ t, (η t).val ∉ Set.range g := by
  obtain ⟨η, hη, havoid⟩ :=
    exists_smooth_path_avoiding_closed_image γ (Smale.OpenObstacle.restrict g U)
      (Smale.OpenObstacle.contMDiff_restrict g U hg)
      (Smale.OpenObstacle.isClosed_range_restrict g U hclosed) hdim
      (fun h => hx ((Smale.OpenObstacle.mem_range_restrict_iff g U x).mp h))
      (fun h => hy ((Smale.OpenObstacle.mem_range_restrict_iff g U y).mp h))
  exact
    ⟨η, hη, fun t ht => havoid t ((Smale.OpenObstacle.mem_range_restrict_iff g U (η t)).mpr ht)⟩

private theorem
    Smale.ManifoldSmoothing.exists_smooth_map_homotopicRel_of_smooth_off_compact_within_target
    {E G H H' X N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G H'} [J.Boundaryless]
    [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [T2Space X] [SigmaCompactSpace X]
    [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] (f : C(X, N)) {K C U : Set X}
    (hK : IsCompact K) (hC : IsClosed C) (hU : IsOpen U) (hCU : C ⊆ U)
    (hfU : ContMDiffOn I J ∞ f U) (hfK : ContMDiffOn I J ∞ f Kᶜ) {D : Set X} {O : Set N}
    (hO : IsOpen O) (hKO : Set.MapsTo f K O) (hmaps : Set.MapsTo f D O) :
    ∃ f' : C(X, N), ContMDiff I J ∞ f' ∧ Smale.HomotopicRelWithin f f' C D O := by
  classical
  have hp (x : K) :=
    exists_smoothing_patch_at_in_open (I := I) (J := J) f (x : X) hO (hKO x.property)
  choose p hcompatible hplateau hsource using hp
  have hcover : K ⊆ ⋃ x : K, (p x).plateau := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hplateau ⟨x, hx⟩⟩
  obtain ⟨s, hs⟩ :=
    hK.elim_finite_subcover (fun x : K => (p x).plateau) (fun _ => isOpen_interior) hcover
  obtain ⟨f', _, hhom, hsm⟩ :=
    exists_finite_patch_smoothing_within_target (fun i : s => p i.1) f (fun i => hcompatible i.1)
      hC hU hCU hfU (fun i => hsource i.1) hmaps Finset.univ
  refine ⟨f', ?_, hhom⟩
  intro x
  apply hsm x
  by_cases hx : x ∈ K
  · obtain ⟨i, his, hxi⟩ := Set.mem_iUnion₂.mp (hs hx)
    exact Or.inr ⟨⟨i, his⟩, Finset.mem_univ _, hxi⟩
  · exact Or.inl ((hfK x hx).contMDiffAt (hK.isClosed.isOpen_compl.mem_nhds hx))

private theorem Smale.ManifoldSmoothing.exists_smooth_map_homotopicRel_of_smooth_off_compact
    {E G H H' X N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G H'} [J.Boundaryless]
    [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [T2Space X] [SigmaCompactSpace X]
    [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] (f : C(X, N)) {K C U : Set X}
    (hK : IsCompact K) (hC : IsClosed C) (hU : IsOpen U) (hCU : C ⊆ U)
    (hfU : ContMDiffOn I J ∞ f U) (hfK : ContMDiffOn I J ∞ f Kᶜ) :
    ∃ f' : C(X, N), ContMDiff I J ∞ f' ∧ f.HomotopicRel f' C := by
  obtain ⟨f', hf', hrel⟩ :=
    exists_smooth_map_homotopicRel_of_smooth_off_compact_within_target f hK hC hU hCU hfU hfK
      isOpen_univ (Set.mapsTo_univ f K) (Set.mapsTo_univ f Set.univ)
  exact ⟨f', hf', hrel.homotopicRel⟩

private theorem Smale.CurveImmersion.exists_continuous_curve_with_endpoint_germs {N : Type*}
    [TopologicalSpace N] (a b : C(ℝ, N)) (γ : Path (a 0) (b 1)) :
    ∃ f : C(ℝ, N), Set.EqOn f a (Set.Iic (1 / 4 : ℝ)) ∧ Set.EqOn f b (Set.Ici (3 / 4 : ℝ)) := by
  classical
  let α : Path (a (1 / 4)) (a 0) :=
    Path.ofLine (f := fun t : ℝ => a ((1 - t) / 4))
      ((a.continuous.comp ((continuous_const.sub continuous_id).div_const 4)).continuousOn)
      (by norm_num) (by norm_num)
  let β : Path (b 1) (b (3 / 4)) :=
    Path.ofLine (f := fun t : ℝ => b (1 - t / 4))
      ((b.continuous.comp (continuous_const.sub (continuous_id.div_const 4))).continuousOn)
      (by norm_num) (by norm_num)
  let η := α.trans (γ.trans β)
  let mid : ℝ → N := fun t => η.extend (2 * t - 1 / 2)
  have hmid : Continuous mid :=
    η.continuous_extend.comp ((continuous_const.mul continuous_id).sub continuous_const)
  have hm₀ : mid (1 / 4) = a (1 / 4) := by
    change η.extend (2 * (1 / 4) - 1 / 2) = _
    norm_num
  have hm₁ : mid (3 / 4) = b (3 / 4) := by
    change η.extend (2 * (3 / 4) - 1 / 2) = _
    norm_num
  let right : ℝ → N := fun t => if t ≤ 3 / 4 then mid t else b t
  have hr : Continuous right :=
    hmid.if_le b.continuous continuous_id continuous_const (fun t ht => ht ▸ hm₁)
  let f : ℝ → N := fun t => if t ≤ 1 / 4 then a t else right t
  have hf : Continuous f :=
    a.continuous.if_le hr continuous_id continuous_const
      (by
        intro t ht
        subst t
        simpa only [right, ite_eq_left (show (1 / 4 : ℝ) ≤ 3 / 4 by norm_num)] using hm₀.symm)
  refine ⟨⟨f, hf⟩, ?_, ?_⟩
  · intro t ht
    exact ite_eq_left ht
  · intro t ht
    change 3 / 4 ≤ t at ht
    change (if t ≤ 1 / 4 then a t else if t ≤ 3 / 4 then mid t else b t) = b t
    rw [ite_eq_right (show ¬t ≤ 1 / 4 by linarith)]
    by_cases hte : t = 3 / 4
    · subst t
      simpa only [ite_eq_left le_rfl] using hm₁
    · exact ite_eq_right (by intro h; exact hte (le_antisymm h ht))

private theorem Smale.exists_smooth_curve_with_endpoint_germs {G H N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [J.Boundaryless]
    [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] (a b : C(ℝ, N))
    (ha : ContMDiff 𝓘(ℝ, ℝ) J ∞ a) (hb : ContMDiff 𝓘(ℝ, ℝ) J ∞ b) (γ : Path (a 0) (b 1)) :
    ∃ f : C(ℝ, N),
      ContMDiff 𝓘(ℝ, ℝ) J ∞ f ∧
        Set.EqOn f a (Set.Iic (1 / 8 : ℝ)) ∧ Set.EqOn f b (Set.Ici (7 / 8 : ℝ)) := by
  obtain ⟨g, hgleft, hgright⟩ := CurveImmersion.exists_continuous_curve_with_endpoint_germs a b γ
  let K := Set.Icc (1 / 4 : ℝ) (3 / 4)
  let U := Set.Iio (1 / 4 : ℝ) ∪ Set.Ioi (3 / 4)
  let C := Set.Iic (1 / 8 : ℝ) ∪ Set.Ici (7 / 8)
  have hU : IsOpen U := isOpen_Iio.union isOpen_Ioi
  have hC : IsClosed C := isClosed_Iic.union isClosed_Ici
  have hCU : C ⊆ U := by
    intro t ht
    rcases ht with ht | ht
    · change t ≤ 1 / 8 at ht
      exact Or.inl (show t < 1 / 4 by linarith)
    · change 7 / 8 ≤ t at ht
      exact Or.inr (show 3 / 4 < t by linarith)
  have hgU : ContMDiffOn 𝓘(ℝ, ℝ) J ∞ g U := by
    intro t ht
    apply ContMDiffAt.contMDiffWithinAt
    rcases ht with ht | ht
    · have heq : g =ᶠ[𝓝 t] a := by
        filter_upwards [isOpen_Iio.mem_nhds (show t ∈ Set.Iio (1 / 4 : ℝ) from ht)] with s hs
        exact hgleft (show s ≤ 1 / 4 from hs.le)
      exact ha.contMDiffAt.congr_of_eventuallyEq heq
    · have heq : g =ᶠ[𝓝 t] b := by
        filter_upwards [isOpen_Ioi.mem_nhds (show t ∈ Set.Ioi (3 / 4 : ℝ) from ht)] with s hs
        exact hgright (show 3 / 4 ≤ s from hs.le)
      exact hb.contMDiffAt.congr_of_eventuallyEq heq
  have hKU : Kᶜ ⊆ U := by
    intro t ht
    change ¬(1 / 4 ≤ t ∧ t ≤ 3 / 4) at ht
    change t < 1 / 4 ∨ 3 / 4 < t
    exact not_and_or.mp ht |>.imp lt_of_not_ge lt_of_not_ge
  obtain ⟨f, hf, hrel⟩ :=
    ManifoldSmoothing.exists_smooth_map_homotopicRel_of_smooth_off_compact g
      CompactIccSpace.isCompact_Icc hC hU hCU hgU (hgU.mono hKU)
  refine ⟨f, hf, ?_, ?_⟩
  · intro t ht
    change t ≤ 1 / 8 at ht
    exact
      (hrel.fst_eq_snd (Or.inl ht)).symm.trans
        (hgleft (show t ∈ Set.Iic (1 / 4 : ℝ) from by change t ≤ 1 / 4; linarith))
  · intro t ht
    change 7 / 8 ≤ t at ht
    exact
      (hrel.fst_eq_snd (Or.inr ht)).symm.trans
        (hgright (show t ∈ Set.Ici (3 / 4 : ℝ) from by change 3 / 4 ≤ t; linarith))

private theorem Smale.ManifoldImmersion.exists_clean_curve_endpoint_neighborhood {G H N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold J ∞ N] [T2Space N] {f : ℝ → N} (hf : ContMDiff 𝓘(ℝ, ℝ) J ∞ f) (hxy : f 0 ≠ f 1)
    (hi0 : Function.Injective (mfderiv 𝓘(ℝ, ℝ) J f 0))
    (hi1 : Function.Injective (mfderiv 𝓘(ℝ, ℝ) J f 1)) {S : Set N} (hS : S.Finite) :
    ∃ C : Set ℝ,
      IsCompact C ∧
        {(0 : ℝ), 1} ⊆ interior C ∧
          Set.InjOn f C ∧
            (∀ t ∈ C, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J f t)) ∧
              (∀ t ∈ C, t ∉ ({0, 1} : Set ℝ) → f t ∉ S) := by
  let B : Set ℝ := {0, 1}
  have hB : IsCompact B := ((Set.finite_singleton (1 : ℝ)).insert 0).isCompact
  have h0B : (0 : ℝ) ∈ B := by simp [B]
  have h1B : (1 : ℝ) ∈ B := by simp [B]
  have hinjB : Set.InjOn f B := by
    intro s hs t ht heq
    simp only [B, Set.mem_insert_iff, Set.mem_singleton_iff] at hs ht
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
    · rfl
    · exact (hxy heq).elim
    · exact (hxy heq.symm).elim
    · rfl
  have hiB : ∀ t ∈ B, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J f t) := by
    intro t ht
    simp only [B, Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl
    · exact hi0
    · exact hi1
  obtain ⟨V, hV, hBV, hinjV⟩ := exists_open_injOn_near_compact hf hB hinjB hiB
  let R := S \ {f 0, f 1}
  have hR : IsClosed R := (hS.subset Set.sdiff_subset).isClosed
  let U := (V ∩ {t | Function.Injective (mfderiv 𝓘(ℝ, ℝ) J f t)}) ∩ f ⁻¹' Rᶜ
  have hU : IsOpen U :=
    (hV.inter (isOpen_injective_derivative hf)).inter (hR.isOpen_compl.preimage hf.continuous)
  have hBU : B ⊆ U := by
    intro t ht
    refine ⟨⟨hBV ht, hiB t ht⟩, ?_⟩
    simp only [B, Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl <;> simp [R]
  obtain ⟨C, hC, hBC, hCU⟩ := exists_compact_between hB hU hBU
  refine ⟨C, hC, hBC, hinjV.mono (fun t ht => (hCU ht).1.1), fun t ht => (hCU ht).1.2, ?_⟩
  intro t ht htB htS
  apply (hCU ht).2
  refine ⟨htS, ?_⟩
  intro hends
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hends
  rcases hends with h0 | h1
  · have ht0 : t = 0 := hinjV (hCU ht).1.1 (hBV h0B) h0
    exact htB (by simp [ht0])
  · have ht1 : t = 1 := hinjV (hCU ht).1.1 (hBV h1B) h1
    exact htB (by simp [ht1])

private def
    Smale.WeightedPerturbation.perturb {E F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (β : E → ℝ) (a : F) (x : E) : F :=
  f x + β x • a

private theorem Smale.WeightedPerturbation.contDiff_perturb {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {β : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hβ : ContDiff ℝ ∞ β) (a : F) : ContDiff ℝ ∞ (perturb f β a) :=
  hf.add (hβ.smul contDiff_const)

private theorem Smale.WeightedPerturbation.fderiv_perturb {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {β : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hβ : ContDiff ℝ ∞ β) (a : F) (x : E) :
    fderiv ℝ (perturb f β a) x = fderiv ℝ f x + (fderiv ℝ β x).smulRight a :=
  ((hf.differentiable (by simp) x).hasFDerivAt.add
      ((hβ.differentiable (by simp) x).hasFDerivAt.smul_const a)).fderiv

private def
    Smale.WeightedPerturbation.badDomain {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {X : Type*} (b : X → E) (β : E → ℝ) : Set (X × E) :=
  {q | fderiv ℝ β (b q.1) q.2 ≠ 0}

private def
    Smale.WeightedPerturbation.badParameter {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {X : Type*} (b : X → E) (f : E → F) (β : E → ℝ)
    (q : X × E) : F :=
  (fderiv ℝ β (b q.1) q.2)⁻¹ • (-(fderiv ℝ f (b q.1) q.2))

private theorem
    Smale.WeightedPerturbation.contMDiff_scalarDerivative {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {B H X : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [TopologicalSpace H] {I : ModelWithCorners ℝ B H} [TopologicalSpace X] [ChartedSpace H X]
    {b : X → E} {β : E → ℝ} (hb : ContMDiff I 𝓘(ℝ, E) ∞ b) (hβ : ContDiff ℝ ∞ β) :
    ContMDiff (I.prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞ (fun q : X × E => fderiv ℝ β (b q.1) q.2) :=
  ((hβ.fderiv_right (by simp)).contMDiff.comp (hb.comp contMDiff_fst)).clm_apply contMDiff_snd

private theorem Smale.WeightedPerturbation.isOpen_badDomain {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {B H X : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [TopologicalSpace H] {I : ModelWithCorners ℝ B H} [TopologicalSpace X] [ChartedSpace H X]
    {b : X → E} {β : E → ℝ} (hb : ContMDiff I 𝓘(ℝ, E) ∞ b) (hβ : ContDiff ℝ ∞ β) :
    IsOpen (badDomain b β) :=
  isOpen_ne_fun (contMDiff_scalarDerivative hb hβ).continuous continuous_const

private theorem
    Smale.WeightedPerturbation.contMDiffOn_badParameter {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {B H X : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
    [TopologicalSpace X] [ChartedSpace H X] {b : X → E} {f : E → F} {β : E → ℝ}
    (hb : ContMDiff I 𝓘(ℝ, E) ∞ b) (hf : ContDiff ℝ ∞ f) (hβ : ContDiff ℝ ∞ β) :
    ContMDiffOn (I.prod 𝓘(ℝ, E)) 𝓘(ℝ, F) ∞ (badParameter b f β) (badDomain b β) := by
  have hdf : ContMDiff (I.prod 𝓘(ℝ, E)) 𝓘(ℝ, F) ∞ (fun q : X × E => fderiv ℝ f (b q.1) q.2) :=
    ((hf.fderiv_right (by simp)).contMDiff.comp (hb.comp contMDiff_fst)).clm_apply contMDiff_snd
  intro q hq
  exact
    (((contMDiff_scalarDerivative hb hβ).contMDiffAt.inv₀ hq).smul
        hdf.contMDiffAt.neg).contMDiffWithinAt

private theorem
    Smale.WeightedPerturbation.kernel_iff_of_not_bad {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {X : Type*} {b : X → E} {f : E → F}
    {β : E → ℝ} (hf : ContDiff ℝ ∞ f) (hβ : ContDiff ℝ ∞ β) {a : F}
    (hgood : a ∉ badParameter b f β '' badDomain b β) (x : X) (v : E) :
    fderiv ℝ (perturb f β a) (b x) v = 0 ↔ fderiv ℝ f (b x) v = 0 ∧ fderiv ℝ β (b x) v = 0 := by
  rw [fderiv_perturb hf hβ]
  change fderiv ℝ f (b x) v + fderiv ℝ β (b x) v • a = 0 ↔ _
  constructor
  · intro hker
    have hbzero : fderiv ℝ β (b x) v = 0 := by
      by_contra hn
      apply hgood
      refine ⟨(x, v), hn, ?_⟩
      have heq : fderiv ℝ β (b x) v • a = -(fderiv ℝ f (b x) v) :=
        eq_neg_of_add_eq_zero_right hker
      change (fderiv ℝ β (b x) v)⁻¹ • (-(fderiv ℝ f (b x) v)) = a
      rw [← heq, inv_smul_smul₀ hn]
    exact ⟨by simpa only [hbzero, zero_smul, add_zero] using hker, hbzero⟩
  · rintro ⟨hfzero, hbzero⟩
    simp only [hfzero, hbzero, zero_smul, add_zero]

private theorem Smale.WeightedPerturbation.exists_small_parameter_with_common_kernel {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {B H X : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H]
    {I : ModelWithCorners ℝ B H} [TopologicalSpace X] [ChartedSpace H X] [FiniteDimensional ℝ B]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [IsManifold I ∞ X] [LindelofSpace (X × E)]
    {b : X → E} {f : E → F} {β : E → ℝ} (hb : ContMDiff I 𝓘(ℝ, E) ∞ b) (hf : ContDiff ℝ ∞ f)
    (hβ : ContDiff ℝ ∞ β) (hdim : Module.finrank ℝ B + Module.finrank ℝ E < Module.finrank ℝ F)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a : F,
      ‖a‖ < ε ∧
        ContDiff ℝ ∞ (perturb f β a) ∧
          ∀ x v,
            fderiv ℝ (perturb f β a) (b x) v = 0 ↔
              fderiv ℝ f (b x) v = 0 ∧ fderiv ℝ β (b x) v = 0 := by
  have hd : Module.finrank ℝ (B × E) < Module.finrank ℝ F := by
    simpa only [Module.finrank_prod] using hdim
  have hdense :=
    Smale.GeneralPosition.dense_compl_manifold_image (isOpen_badDomain hb hβ)
      (contMDiffOn_badParameter hb hf hβ) hd
  obtain ⟨a, hgood, hnorm⟩ := hdense.exists_dist_lt 0 hε
  exact
    ⟨a, by simpa only [dist_zero_left] using hnorm, contDiff_perturb hf hβ a,
      kernel_iff_of_not_bad hf hβ hgood⟩

private def
    Smale.CurveImmersion.perturb {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : ℝ → F)
    (a : F) : ℝ → F :=
  Smale.WeightedPerturbation.perturb f id a

private theorem
    Smale.CurveImmersion.exists_small_affine_immersion {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] {f : ℝ → F} (hf : ContDiff ℝ ∞ f)
    (hdim : 3 ≤ Module.finrank ℝ F) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : F,
      ‖a‖ < ε ∧ ContDiff ℝ ∞ (perturb f a) ∧ ∀ t, Function.Injective (fderiv ℝ (perturb f a) t) :=
  by
  have hd : Module.finrank ℝ ℝ + Module.finrank ℝ ℝ < Module.finrank ℝ F := by
    simp only [Module.finrank_self]
    omega
  obtain ⟨a, ha, hs, hker⟩ :=
    Smale.WeightedPerturbation.exists_small_parameter_with_common_kernel (I := 𝓘(ℝ, ℝ)) (b := id)
      (β := id) contMDiff_id hf contDiff_id hd hε
  refine ⟨a, ha, hs, ?_⟩
  intro t u v huv
  have hz : fderiv ℝ (perturb f a) t (u - v) = 0 := by rw [map_sub, huv, sub_self]
  have hzero := ((hker t (u - v)).mp hz).2
  have huv0 : u - v = 0 := by simpa only [fderiv_id, ContinuousLinearMap.id_apply] using hzero
  exact sub_eq_zero.mp huv0

private def Smale.CurveImmersion.weight (β : ℝ → ℝ) (t : ℝ) : ℝ :=
  β t * t

private theorem Smale.CurveImmersion.contDiff_weight {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) :
    ContDiff ℝ ∞ (weight β) :=
  hβ.mul contDiff_id

private theorem
    Smale.CurveImmersion.hasCompactSupport_weight {β : ℝ → ℝ} (hβ : HasCompactSupport β) :
    HasCompactSupport (weight β) :=
  hβ.mul_right (f' := id)

private theorem Smale.CurveImmersion.tsupport_weight_subset (β : ℝ → ℝ) :
    tsupport (weight β) ⊆ tsupport β :=
  tsupport_mul_subset_left (f := β) (g := id)

private theorem
    Smale.CurveImmersion.weight_eq_zero {β : ℝ → ℝ} {t : ℝ} (ht : β t = 0) : weight β t = 0 :=
  by simp only [weight, ht, MulZeroClass.zero_mul]

private theorem Smale.ManifoldImmersion.exists_curve_immersion_patch_with_property_within_target
    {G F H N : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
    [TopologicalSpace N] [ChartedSpace H N] (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (f : C(ℝ, N))
    (hf : ContMDiff 𝓘(ℝ, ℝ) J ∞ f) {β χ : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) (hχ : ContDiff ℝ ∞ χ)
    (hcompact : HasCompactSupport β) (hχsupport : tsupport χ ⊆ f ⁻¹' c.source)
    (hχone : ∀ t ∈ tsupport β, χ t = 1) (hdim : 3 ≤ Module.finrank ℝ F) (Q : (ℝ → N) → Prop)
    (hQ :
      ∀ᶠ a : F in 𝓝 0,
        Q (Smale.ChartMapPerturbation.perturb c f (Smale.CurveImmersion.weight β) a))
    {D : Set ℝ} {O : Set N} (hsource : c.source ⊆ O) (hmaps : Set.MapsTo f D O) :
    ∃ g : C(ℝ, N),
      ContMDiff 𝓘(ℝ, ℝ) J ∞ g ∧
        Q g ∧
          Smale.HomotopicRelWithin f g {t | β t = 0} D O ∧
            ∀ t ∈ interior {t | β t = 1}, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J g t) := by
  have hsupport : tsupport β ⊆ f ⁻¹' c.source := by
    intro t ht
    exact hχsupport (subset_tsupport χ (by change χ t ≠ 0; rw [hχone t ht]; norm_num))
  have hw := Smale.CurveImmersion.contDiff_weight hβ
  have hwsupport : tsupport (Smale.CurveImmersion.weight β) ⊆ f ⁻¹' c.source :=
    (Smale.CurveImmersion.tsupport_weight_subset β).trans hsupport
  let k := Smale.ChartMapPerturbation.cutoffCoordinates c f χ
  have hk : ContDiff ℝ ∞ k := by
    have hm : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, F) ∞ k := fun t =>
      Smale.ChartMapPerturbation.contMDiffAt_cutoffCoordinates c hχsupport hf.contMDiffAt
        hχ.contMDiff.contMDiffAt
    exact hm.contDiff
  obtain ⟨ε, hε, hvalid⟩ :=
    Smale.ChartMapPerturbation.exists_radius_valid c hf hw.contMDiff
      (Smale.CurveImmersion.hasCompactSupport_weight hcompact) hwsupport
  obtain ⟨δ, hδ, hδkeep⟩ := Metric.mem_nhds_iff.mp hQ
  obtain ⟨a, ha, -, hderiv⟩ :=
    Smale.CurveImmersion.exists_small_affine_immersion hk hdim (lt_min hε hδ)
  have haε : ‖a‖ < ε := ha.trans_le (min_le_left _ _)
  have hv := hvalid a haε
  have hsmooth := Smale.ChartMapPerturbation.contMDiff_perturb c hf hw.contMDiff hwsupport hv
  let g : C(ℝ, N) :=
    ⟨Smale.ChartMapPerturbation.perturb c f (Smale.CurveImmersion.weight β) a, hsmooth.continuous⟩
  have hcoord (t : ℝ) (ht : β t = 1) : c (g t) = Smale.CurveImmersion.perturb k a t := by
    have hts : t ∈ tsupport β := subset_tsupport β (by change β t ≠ 0; rw [ht]; norm_num)
    change c (Smale.ChartMapPerturbation.perturb c f (Smale.CurveImmersion.weight β) a t) = _
    rw [Smale.ChartMapPerturbation.chart_perturb c f (Smale.CurveImmersion.weight β) hv
        (hsupport hts)]
    simp only [Smale.ChartMapPerturbation.coordinateFamily, Smale.CurveImmersion.perturb,
      Smale.WeightedPerturbation.perturb, k, Smale.ChartMapPerturbation.cutoffCoordinates,
      Smale.CurveImmersion.weight, ht, hχone t hts, one_mul, one_smul, id_eq]
  have hQg : Q g :=
    hδkeep
      (show a ∈ Metric.ball 0 δ by
        simpa only [Metric.mem_ball, dist_zero_right] using ha.trans_le (min_le_right ε δ))
  refine ⟨g, hsmooth, hQg, ?_, ?_⟩
  · have hrel :=
      Smale.ChartMapPerturbation.homotopicRelWithin_of_source_subset c hf hw.contMDiff hwsupport
        hvalid haε hsource hmaps
    exact
      hrel.mono (fun _ hx => Smale.CurveImmersion.weight_eq_zero hx) (Set.Subset.refl D)
        (Set.Subset.refl O)
  · intro t ht
    have hβt : β t = 1 := interior_subset (s := {t | β t = 1}) ht
    have hfs : f t ∈ c.source :=
      hsupport (subset_tsupport β (by change β t ≠ 0; rw [hβt]; norm_num))
    have hgs : g t ∈ c.source :=
      Smale.ChartMapPerturbation.perturb_mem_source c f (Smale.CurveImmersion.weight β) hv hfs
    apply (injective_fderiv_chart_iff c (hsmooth.mdifferentiableAt (by simp)) hgs).mp
    have heq : (c ∘ g) =ᶠ[𝓝 t] Smale.CurveImmersion.perturb k a := by
      filter_upwards [isOpen_interior.mem_nhds ht] with s hs
      exact hcoord s (interior_subset (s := {t | β t = 1}) hs)
    change Function.Injective (fderiv ℝ (c ∘ g) t)
    rw [heq.fderiv_eq]
    exact hderiv t

private theorem
    Smale.ManifoldImmersion.exists_curve_immersion_patch_step_within_target {G H N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold J ∞ N] {ι : Type*} [Finite ι]
    (p : ι → Smale.ManifoldSmoothing.MapSmoothingPatch 𝓘(ℝ, ℝ) J (X := ℝ) (N := N)) (i : ι)
    (f : C(ℝ, N)) (hf : ContMDiff 𝓘(ℝ, ℝ) J ∞ f) (hcompatible : ∀ j, (p j).Compatible f)
    (hdim : 3 ≤ Module.finrank ℝ G) {K L C : Set ℝ} (hK : IsCompact K)
    (hinj : ∀ t ∈ K, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J f t)) (hLsub : L ⊆ (p i).plateau)
    (hfixed : ∀ t ∈ C, (p i).cutoff t = 0) {D : Set ℝ} {O : Set N}
    (hsource : (p i).chart.source ⊆ O) (hmaps : Set.MapsTo f D O) :
    ∃ g : C(ℝ, N),
      ContMDiff 𝓘(ℝ, ℝ) J ∞ g ∧
        (∀ j, (p j).Compatible g) ∧
          Smale.HomotopicRelWithin f g C D O ∧
            ∀ t ∈ K ∪ L, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J g t) := by
  let w := Smale.CurveImmersion.weight (p i).cutoff
  have hw : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ w :=
    (Smale.CurveImmersion.contDiff_weight (p i).smooth.contDiff).contMDiff
  have hinner := (p i).inner_compatible (hcompatible i)
  have hwsupport : tsupport w ⊆ f ⁻¹' (p i).chart.source :=
    (Smale.CurveImmersion.tsupport_weight_subset (p i).cutoff).trans hinner
  have hkeep :
    ∀ᶠ a : G in 𝓝 0,
      ∀ j, (p j).Compatible (Smale.ChartMapPerturbation.perturb (p i).chart f w a) := by
    apply Filter.eventually_all.mpr
    intro j
    exact
      Smale.ChartMapPerturbation.eventually_maps_compact_into_open (p i).chart hf hw hwsupport
        (p j).outer_compact.isCompact (p j).chart.open_source (hcompatible j)
  have hold :=
    Smale.ChartMapPerturbation.eventually_perturb_injective_derivative (p i).chart hf hw
      (Smale.CurveImmersion.hasCompactSupport_weight (p i).compact) hwsupport hK hinj
  let Q : (ℝ → N) → Prop := fun g =>
    (∀ j, (p j).Compatible g) ∧ ∀ t ∈ K, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J g t)
  have hQ : ∀ᶠ a : G in 𝓝 0, Q (Smale.ChartMapPerturbation.perturb (p i).chart f w a) :=
    hkeep.and hold
  obtain ⟨g, hg, ⟨hc, hKnew⟩, hrel, hplateau⟩ :=
    exists_curve_immersion_patch_with_property_within_target (p i).chart f hf
      (p i).smooth.contDiff (p i).outer_smooth.contDiff (p i).compact (hcompatible i) (p i).nested
      hdim Q hQ hsource hmaps
  refine ⟨g, hg, hc, ?_, ?_⟩
  · exact hrel.mono hfixed (Set.Subset.refl D) (Set.Subset.refl O)
  · intro t ht
    rcases ht with ht | ht
    · exact hKnew t ht
    · exact hplateau t (hLsub ht)

private theorem
    Smale.ManifoldImmersion.exists_finite_curve_patch_immersion_within_target {G H N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold J ∞ N] {ι : Type*} [Finite ι]
    (p : ι → Smale.ManifoldSmoothing.MapSmoothingPatch 𝓘(ℝ, ℝ) J (X := ℝ) (N := N))
    (L : ι → Set ℝ) (hL : ∀ i, IsCompact (L i)) (hLsub : ∀ i, L i ⊆ (p i).plateau) (f : C(ℝ, N))
    (hf : ContMDiff 𝓘(ℝ, ℝ) J ∞ f) (hcompatible : ∀ i, (p i).Compatible f)
    (hdim : 3 ≤ Module.finrank ℝ G) {K C : Set ℝ} (hK : IsCompact K)
    (hinj : ∀ t ∈ K, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J f t))
    (hfixed : ∀ i t, t ∈ C → (p i).cutoff t = 0) {D : Set ℝ} {O : Set N}
    (hsource : ∀ i, (p i).chart.source ⊆ O) (hmaps : Set.MapsTo f D O) (s : Finset ι) :
    ∃ g : C(ℝ, N),
      ContMDiff 𝓘(ℝ, ℝ) J ∞ g ∧
        (∀ i, (p i).Compatible g) ∧
          Smale.HomotopicRelWithin f g C D O ∧
            ∀ t ∈ K ∪ ⋃ i ∈ s, L i, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J g t) := by
  classical
    induction s using Finset.induction_on with
  | empty =>
    refine ⟨f, hf, hcompatible, Smale.HomotopicRelWithin.refl f C hmaps, ?_⟩
    simpa only [Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty, Set.union_empty] using
      hinj
  | @insert i s _ ih =>
    obtain ⟨g₁, hg₁, hc₁, hhom₁, hinj₁⟩ := ih
    have hKold : IsCompact (K ∪ ⋃ j ∈ s, L j) := hK.union (s.isCompact_biUnion (fun j _ => hL j))
    obtain ⟨g₂, hg₂, hc₂, hhom₂, hinj₂⟩ :=
      exists_curve_immersion_patch_step_within_target p i g₁ hg₁ hc₁ hdim hKold hinj₁ (hLsub i)
        (hfixed i) (hsource i) hhom₁.mapsTo_right
    refine ⟨g₂, hg₂, hc₂, hhom₁.trans hhom₂, ?_⟩
    intro t ht
    apply hinj₂ t
    rcases ht with ht | ht
    · exact Or.inl (Or.inl ht)
    · obtain ⟨j, hj, htj⟩ := Set.mem_iUnion₂.mp ht
      rcases Finset.mem_insert.mp hj with rfl | hjs
      · exact Or.inr htj
      · exact Or.inl (Or.inr (Set.mem_iUnion₂.mpr ⟨j, hjs, htj⟩))

private theorem Smale.ManifoldImmersion.exists_curve_immersion_on_compact_rel_within_target
    {G H N : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N]
    [ChartedSpace H N] [IsManifold J ∞ N] (f : C(ℝ, N)) (hf : ContMDiff 𝓘(ℝ, ℝ) J ∞ f)
    (hdim : 3 ≤ Module.finrank ℝ G) {K L C : Set ℝ} (hK : IsCompact K) (hL : IsCompact L)
    (hinj : ∀ t ∈ K, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J f t)) (hC : IsClosed C)
    (hdis : Disjoint L C) {D : Set ℝ} {O : Set N} (hO : IsOpen O) (hLO : Set.MapsTo f L O)
    (hmaps : Set.MapsTo f D O) :
    ∃ g : C(ℝ, N),
      ContMDiff 𝓘(ℝ, ℝ) J ∞ g ∧
        Smale.HomotopicRelWithin f g C D O ∧
          ∀ t ∈ K ∪ L, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J g t) := by
  classical
  have hp (t : L) :=
    exists_relative_immersion_patch_at_in_open (J := J) f hC
      (show (t : ℝ) ∉ C from fun ht => Set.disjoint_left.mp hdis t.property ht) hO
      (hLO t.property)
  choose p T hcompatible hT hn hsub hfixed hsource using hp
  have hcover : L ⊆ ⋃ t : L, interior (T t) := by
    intro t ht
    exact Set.mem_iUnion.mpr ⟨⟨t, ht⟩, mem_interior_iff_mem_nhds.mpr (hn ⟨t, ht⟩)⟩
  obtain ⟨s, hs⟩ :=
    hL.elim_finite_subcover (fun t : L => interior (T t)) (fun _ => isOpen_interior) hcover
  obtain ⟨g, hg, -, hhom, hderiv⟩ :=
    exists_finite_curve_patch_immersion_within_target (fun i : s => p i.1) (fun i : s => T i.1)
      (fun i => hT i.1) (fun i => hsub i.1) f hf (fun i => hcompatible i.1) hdim hK hinj
      (fun i => hfixed i.1) (fun i => hsource i.1) hmaps Finset.univ
  refine ⟨g, hg, hhom, ?_⟩
  intro t ht
  apply hderiv t
  rcases ht with ht | ht
  · exact Or.inl ht
  · obtain ⟨i, his, hti⟩ := Set.mem_iUnion₂.mp (hs ht)
    exact Or.inr (Set.mem_iUnion₂.mpr ⟨⟨i, his⟩, Finset.mem_univ _, interior_subset hti⟩)

private theorem Smale.ManifoldImmersion.exists_relative_compact_curve_embedding_within_target
    {G H N : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N]
    [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N] (f : C(ℝ, N)) (hf : ContMDiff 𝓘(ℝ, ℝ) J ∞ f)
    (hdim : 3 ≤ Module.finrank ℝ G) {K C : Set ℝ} (hK : IsCompact K) (hC : IsClosed C)
    (hfixed : Set.InjOn f (K ∩ C))
    (hderiv : ∀ t ∈ K ∩ C, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J f t)) {O : Set N} (hO : IsOpen O)
    (hmaps : Set.MapsTo f (K \ C) O) :
    ∃ g : C(ℝ, N),
      ContMDiff 𝓘(ℝ, ℝ) J ∞ g ∧
        Smale.HomotopicRelWithin f g C (K \ C) O ∧
          Topology.IsClosedEmbedding (fun t : K => g t) ∧
            ∀ t ∈ K, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J g t) := by
  let U : Set ℝ := {t | Function.Injective (mfderiv 𝓘(ℝ, ℝ) J f t)}
  have hU : IsOpen U := isOpen_injective_derivative hf
  have hCU : K ∩ C ⊆ U := fun t ht => hderiv t ht
  obtain ⟨D, hD, hCD, hDU⟩ := exists_compact_between (hK.inter_right hC) hU hCU
  let L := K \ interior D
  have hL : IsCompact L := hK.inter_right isOpen_interior.isClosed_compl
  have hdis : Disjoint L C := Set.disjoint_left.mpr (fun _ ht htC => ht.2 (hCD ⟨ht.1, htC⟩))
  have hLO : Set.MapsTo f L O := fun t ht => hmaps ⟨ht.1, fun htC => ht.2 (hCD ⟨ht.1, htC⟩)⟩
  obtain ⟨g₁, hg₁, hhom₁, hinj₁⟩ :=
    exists_curve_immersion_on_compact_rel_within_target f hf hdim hD hL (fun t ht => hDU ht) hC
      hdis hO hLO hmaps
  have hKinj : ∀ t ∈ K, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J g₁ t) := by
    intro t ht
    apply hinj₁ t
    by_cases htD : t ∈ D
    · exact Or.inl htD
    · exact Or.inr ⟨ht, fun hi => htD (interior_subset hi)⟩
  have hfixed₁ : Set.InjOn g₁ (K ∩ C) := by
    intro t ht s hs hts
    apply hfixed ht hs
    rw [hhom₁.homotopicRel.fst_eq_snd ht.2, hhom₁.homotopicRel.fst_eq_snd hs.2]
    exact hts
  have hd : 2 * Module.finrank ℝ ℝ < Module.finrank ℝ G := by
    simp only [Module.finrank_self]
    omega
  obtain ⟨g₂, hg₂, hhom₂, hemb, hinj₂⟩ :=
    exists_compact_embedding_of_immersion_within_target g₁ hg₁ hd hK hKinj hC hfixed₁ hO
      hhom₁.mapsTo_right
  exact ⟨g₂, hg₂, hhom₁.trans hhom₂, hemb, hinj₂⟩

private theorem Smale.ManifoldImmersion.exists_relative_compact_curve_embedding {G H N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold J ∞ N] [T2Space N] (f : C(ℝ, N)) (hf : ContMDiff 𝓘(ℝ, ℝ) J ∞ f)
    (hdim : 3 ≤ Module.finrank ℝ G) {K C : Set ℝ} (hK : IsCompact K) (hC : IsClosed C)
    (hfixed : Set.InjOn f (K ∩ C))
    (hderiv : ∀ t ∈ K ∩ C, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J f t)) :
    ∃ g : C(ℝ, N),
      ContMDiff 𝓘(ℝ, ℝ) J ∞ g ∧
        f.HomotopicRel g C ∧
          Topology.IsClosedEmbedding (fun t : K => g t) ∧
            ∀ t ∈ K, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J g t) := by
  obtain ⟨g, hg, hrel, he, hi⟩ :=
    exists_relative_compact_curve_embedding_within_target f hf hdim hK hC hfixed hderiv
      isOpen_univ (Set.mapsTo_univ f (K \ C))
  exact ⟨g, hg, hrel.homotopicRel, he, hi⟩

private theorem Smale.ManifoldImmersion.exists_relative_curve_avoidance_of_clean_neighborhood
    {G H N : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N]
    [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N] {F H' Y : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] [TopologicalSpace H'] {I' : ModelWithCorners ℝ F H'}
    [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y] [CompactSpace Y]
    [LindelofSpace (ℝ × Y)] (f : C(ℝ, N)) (g : C(Y, N)) (hf : ContMDiff 𝓘(ℝ, ℝ) J ∞ f)
    (hg : ContMDiff I' J ∞ g) (hdim : 3 ≤ Module.finrank ℝ G)
    (hobstacle : 1 + Module.finrank ℝ F < Module.finrank ℝ G) {K C B : Set ℝ} (hK : IsCompact K)
    (hC : IsClosed C) (hBC : B ⊆ interior C) (hfixed : Set.InjOn f (K ∩ C))
    (hderiv : ∀ t ∈ K ∩ C, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J f t))
    (hclean : ∀ t ∈ K ∩ C, t ∉ B → f t ∉ Set.range g) :
    ∃ f' : C(ℝ, N),
      ContMDiff 𝓘(ℝ, ℝ) J ∞ f' ∧
        f.HomotopicRel f' C ∧
          Topology.IsClosedEmbedding (fun t : K => f' t) ∧
            (∀ t ∈ K, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J f' t)) ∧
              ∀ t ∈ K \ B, f' t ∉ Set.range g := by
  obtain ⟨f₁, hf₁, hhom₁, hemb₁, hderiv₁⟩ :=
    exists_relative_compact_curve_embedding f hf hdim hK hC hfixed hderiv
  have hinj₁ : Set.InjOn f₁ K := by
    intro t ht s hs hts
    exact congrArg Subtype.val (hemb₁.injective (a₁ := ⟨t, ht⟩) (a₂ := ⟨s, hs⟩) hts)
  have hclean₁ : ∀ t ∈ K ∩ C, t ∉ B → f₁ t ∉ Set.range g := by
    intro t ht htB
    rw [← hhom₁.fst_eq_snd ht.2]
    exact hclean t ht htB
  have hself : 2 * Module.finrank ℝ ℝ < Module.finrank ℝ G := by
    simp only [Module.finrank_self]
    omega
  have hobs : Module.finrank ℝ ℝ + Module.finrank ℝ F < Module.finrank ℝ G := by
    simpa only [Module.finrank_self] using hobstacle
  obtain ⟨f₂, hf₂, hhom₂, hemb₂, hderiv₂, havoid⟩ :=
    exists_embedded_avoidance_relative_neighborhood f₁ g hf₁ hg hself hobs hK hC hBC hinj₁ hderiv₁
      hclean₁
  exact ⟨f₂, hf₂, hhom₁.trans hhom₂, hemb₂, hderiv₂, havoid⟩

private theorem Smale.ManifoldImmersion.exists_relative_curve_avoiding_finite {G H N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold J ∞ N] [T2Space N] (f : C(ℝ, N)) (hf : ContMDiff 𝓘(ℝ, ℝ) J ∞ f)
    (hdim : 3 ≤ Module.finrank ℝ G) {S : Set N} (hS : S.Finite) {K C B : Set ℝ} (hK : IsCompact K)
    (hC : IsClosed C) (hBC : B ⊆ interior C) (hfixed : Set.InjOn f (K ∩ C))
    (hderiv : ∀ t ∈ K ∩ C, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J f t))
    (hclean : ∀ t ∈ K ∩ C, t ∉ B → f t ∉ S) :
    ∃ f' : C(ℝ, N),
      ContMDiff 𝓘(ℝ, ℝ) J ∞ f' ∧
        f.HomotopicRel f' C ∧
          Topology.IsClosedEmbedding (fun t : K => f' t) ∧
            (∀ t ∈ K, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J f' t)) ∧ ∀ t ∈ K \ B, f' t ∉ S := by
  let : Fintype S := hS.fintype
  let Z := EuclideanSpace ℝ (Fin 0)
  let : ChartedSpace Z S := ChartedSpace.ofDiscreteTopology
  let : IsManifold 𝓘(ℝ, Z) ∞ S := IsManifold.of_discreteTopology _
  let g : C(S, N) := ⟨Subtype.val, continuous_subtype_val⟩
  have hg : ContMDiff 𝓘(ℝ, Z) J ∞ g := contMDiff_of_discreteTopology
  have hrange : Set.range g = S := by ext y; simp [g]
  have hobs : 1 + Module.finrank ℝ Z < Module.finrank ℝ G := by
    simp only [Z, finrank_euclideanSpace_fin]
    omega
  have hclean' : ∀ t ∈ K ∩ C, t ∉ B → f t ∉ Set.range g := by simpa only [hrange] using hclean
  obtain ⟨f', hf', hrel, hemb, hi, havoid⟩ :=
    exists_relative_curve_avoidance_of_clean_neighborhood f g hf hg hdim hobs hK hC hBC hfixed
      hderiv hclean'
  refine ⟨f', hf', hrel, hemb, hi, ?_⟩
  simpa only [hrange] using havoid

private theorem Smale.exists_embedded_arc_with_endpoint_germs {G H N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
    [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N]
    (a b : C(ℝ, N)) (ha : ContMDiff 𝓘(ℝ, ℝ) J ∞ a) (hb : ContMDiff 𝓘(ℝ, ℝ) J ∞ b)
    (hia : Function.Injective (mfderiv 𝓘(ℝ, ℝ) J a 0))
    (hib : Function.Injective (mfderiv 𝓘(ℝ, ℝ) J b 1)) (γ : Path (a 0) (b 1)) (hxy : a 0 ≠ b 1)
    (hdim : 3 ≤ Module.finrank ℝ G) {S : Set N} (hS : S.Finite) :
    ∃ f : C(ℝ, N),
      ContMDiff 𝓘(ℝ, ℝ) J ∞ f ∧
        (f =ᶠ[𝓝 (0 : ℝ)] a) ∧
          (f =ᶠ[𝓝 (1 : ℝ)] b) ∧
            Topology.IsClosedEmbedding (fun t : unitInterval => f t) ∧
              (∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J f t)) ∧
                (∀ t ∈ Set.Ioo (0 : ℝ) 1, f t ∉ S) := by
  obtain ⟨g, hg, hga, hgb⟩ := exists_smooth_curve_with_endpoint_germs a b ha hb γ
  have hga0 : g =ᶠ[𝓝 (0 : ℝ)] a := by
    filter_upwards [Iio_mem_nhds (show (0 : ℝ) < 1 / 8 by norm_num)] with t ht
    change t < 1 / 8 at ht
    exact hga ht.le
  have hgb1 : g =ᶠ[𝓝 (1 : ℝ)] b := by
    filter_upwards [Ioi_mem_nhds (show (7 / 8 : ℝ) < 1 by norm_num)] with t ht
    change 7 / 8 < t at ht
    exact hgb ht.le
  have hgxy : g 0 ≠ g 1 := by
    rw [hga0.eq_of_nhds, hgb1.eq_of_nhds]
    exact hxy
  have hig0 : Function.Injective (mfderiv 𝓘(ℝ, ℝ) J g 0) := by
    rw [hga0.mfderiv_eq]
    exact hia
  have hig1 : Function.Injective (mfderiv 𝓘(ℝ, ℝ) J g 1) := by
    rw [hgb1.mfderiv_eq]
    exact hib
  obtain ⟨C, hC, hBC, hinjC, hiC, hclean⟩ :=
    ManifoldImmersion.exists_clean_curve_endpoint_neighborhood hg hgxy hig0 hig1 hS
  obtain ⟨f, hf, hrel, hemb, hi, havoid⟩ :=
    ManifoldImmersion.exists_relative_curve_avoiding_finite g hg hdim hS
      (CompactIccSpace.isCompact_Icc (a := (0 : ℝ)) (b := 1)) hC.isClosed hBC
      (hinjC.mono Set.inter_subset_right) (fun t ht => hiC t ht.2) (fun t ht => hclean t ht.2)
  have hfg (t : ℝ) (ht : t ∈ ({0, 1} : Set ℝ)) : f =ᶠ[𝓝 t] g := by
    filter_upwards [isOpen_interior.mem_nhds (hBC ht)] with s hs
    exact (hrel.fst_eq_snd (interior_subset hs)).symm
  refine ⟨f, hf, (hfg 0 (by simp)).trans hga0, (hfg 1 (by simp)).trans hgb1, hemb, hi, ?_⟩
  intro t ht
  apply havoid t ⟨⟨ht.1.le, ht.2.le⟩, ?_⟩
  intro htB
  rcases htB with ht0 | ht1
  · exact ht.1.ne' ht0
  · exact ht.2.ne ht1

private theorem Smale.exists_smooth_curve_with_germ_at {G H N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [TopologicalSpace N]
    [ChartedSpace H N] {a : ℝ → N} {U : Set ℝ} {t₀ : ℝ} (ha : ContMDiffOn 𝓘(ℝ, ℝ) J ∞ a U)
    (hU : IsOpen U) (ht₀ : t₀ ∈ U) : ∃ f : C(ℝ, N), ContMDiff 𝓘(ℝ, ℝ) J ∞ f ∧ (f =ᶠ[𝓝 t₀] a) := by
  obtain ⟨f, hf, heq⟩ := exists_smooth_extension_near_point ha hU ht₀
  exact ⟨⟨f, hf.continuous⟩, hf, heq⟩

private theorem
    Smale.exists_embedded_arc_with_local_endpoint_germs {G H N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
    [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N]
    {a b : ℝ → N} {U V : Set ℝ} (ha : ContMDiffOn 𝓘(ℝ, ℝ) J ∞ a U)
    (hb : ContMDiffOn 𝓘(ℝ, ℝ) J ∞ b V) (hU : IsOpen U) (hV : IsOpen V) (h0U : (0 : ℝ) ∈ U)
    (h1V : (1 : ℝ) ∈ V) (hia : Function.Injective (mfderiv 𝓘(ℝ, ℝ) J a 0))
    (hib : Function.Injective (mfderiv 𝓘(ℝ, ℝ) J b 1)) (γ : Path (a 0) (b 1)) (hxy : a 0 ≠ b 1)
    (hdim : 3 ≤ Module.finrank ℝ G) {S : Set N} (hS : S.Finite) :
    ∃ f : C(ℝ, N),
      ContMDiff 𝓘(ℝ, ℝ) J ∞ f ∧
        (f =ᶠ[𝓝 (0 : ℝ)] a) ∧
          (f =ᶠ[𝓝 (1 : ℝ)] b) ∧
            Topology.IsClosedEmbedding (fun t : unitInterval => f t) ∧
              (∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J f t)) ∧
                (∀ t ∈ Set.Ioo (0 : ℝ) 1, f t ∉ S) := by
  obtain ⟨a', ha', heqa⟩ := exists_smooth_curve_with_germ_at ha hU h0U
  obtain ⟨b', hb', heqb⟩ := exists_smooth_curve_with_germ_at hb hV h1V
  have hia' : Function.Injective (mfderiv 𝓘(ℝ, ℝ) J a' 0) := by
    rw [heqa.mfderiv_eq]
    exact hia
  have hib' : Function.Injective (mfderiv 𝓘(ℝ, ℝ) J b' 1) := by
    rw [heqb.mfderiv_eq]
    exact hib
  have hxy' : a' 0 ≠ b' 1 := by
    rw [heqa.eq_of_nhds, heqb.eq_of_nhds]
    exact hxy
  obtain ⟨f, hf, hfa, hfb, hemb, hi, havoid⟩ :=
    exists_embedded_arc_with_endpoint_germs a' b' ha' hb' hia' hib'
      (γ.cast heqa.eq_of_nhds heqb.eq_of_nhds) hxy' hdim hS
  exact ⟨f, hf, hfa.trans heqa, hfb.trans heqb, hemb, hi, havoid⟩

private theorem MorseCancel.exists_clean_arc_with_local_endpoint_germs {G V H H' N Y : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] [TopologicalSpace H] [TopologicalSpace H']
    {J : ModelWithCorners ℝ G H} {I : ModelWithCorners ℝ V H'} [J.Boundaryless]
    [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N] [TopologicalSpace Y]
    [ChartedSpace H' Y] [IsManifold I ∞ Y] [SecondCountableTopology Y] {a b : ℝ → N} {U W : Set ℝ}
    (ha : ContMDiffOn 𝓘(ℝ, ℝ) J ∞ a U) (hb : ContMDiffOn 𝓘(ℝ, ℝ) J ∞ b W) (hU : IsOpen U)
    (hW : IsOpen W) (h0U : (0 : ℝ) ∈ U) (h1W : (1 : ℝ) ∈ W)
    (hia : Function.Injective (mfderiv 𝓘(ℝ, ℝ) J a 0))
    (hib : Function.Injective (mfderiv 𝓘(ℝ, ℝ) J b 1)) (γ : Path (a 0) (b 1)) (hxy : a 0 ≠ b 1)
    (hdim : 3 ≤ Module.finrank ℝ G) (o : C(Y, N)) (ho : ContMDiff I J ∞ o)
    (hclosed : IsClosed (Set.range o)) (hobdim : 1 + Module.finrank ℝ V < Module.finrank ℝ G)
    (hclean0 : ∀ᶠ t in 𝓝 (0 : ℝ), a t ∈ Set.range o → t = 0)
    (hclean1 : ∀ᶠ t in 𝓝 (1 : ℝ), b t ∈ Set.range o → t = 1) :
    ∃ f : C(ℝ, N),
      ContMDiff 𝓘(ℝ, ℝ) J ∞ f ∧
        (f =ᶠ[𝓝 (0 : ℝ)] a) ∧
          (f =ᶠ[𝓝 (1 : ℝ)] b) ∧
            Topology.IsClosedEmbedding (fun t : unitInterval => f t) ∧
              (∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J f t)) ∧
                ∀ t ∈ Set.Ioo (0 : ℝ) 1, f t ∉ Set.range o := by
  obtain ⟨f, hf, hfa, hfb, hemb, hfd, -⟩ :=
    Smale.exists_embedded_arc_with_local_endpoint_germs ha hb hU hW h0U h1W hia hib γ hxy hdim
      (S := ∅) Set.finite_empty
  have hnear0 : ∀ᶠ t in 𝓝 (0 : ℝ), f t ∈ Set.range o → t = 0 := by
    filter_upwards [hfa, hclean0] with t he hc
    rw [he]
    exact hc
  have hnear1 : ∀ᶠ t in 𝓝 (1 : ℝ), f t ∈ Set.range o → t = 1 := by
    filter_upwards [hfb, hclean1] with t he hc
    rw [he]
    exact hc
  obtain ⟨r, hr, hball0⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hnear0
  obtain ⟨s, hs, hball1⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hnear1
  let C : Set ℝ := Metric.closedBall 0 r ∪ Metric.closedBall 1 s
  have h0C : C ∈ 𝓝 (0 : ℝ) :=
    Filter.mem_of_superset (Metric.ball_mem_nhds 0 hr)
      (fun _ ht => Or.inl (Metric.ball_subset_closedBall ht))
  have h1C : C ∈ 𝓝 (1 : ℝ) :=
    Filter.mem_of_superset (Metric.ball_mem_nhds 1 hs)
      (fun _ ht => Or.inr (Metric.ball_subset_closedBall ht))
  have hBC : ({0, 1} : Set ℝ) ⊆ interior C := by
    intro t ht
    rcases ht with rfl | ht
    · exact mem_interior_iff_mem_nhds.mpr h0C
    · have ht1 : t = 1 := ht
      subst t
      exact mem_interior_iff_mem_nhds.mpr h1C
  have hclean : ∀ t ∈ Set.Icc (0 : ℝ) 1 ∩ C, t ∉ ({0, 1} : Set ℝ) → f t ∉ Set.range o := by
    intro t ht htB hto
    rcases ht.2 with ht0 | ht1
    · exact htB (Or.inl (hball0 ht0 hto))
    · exact htB (Or.inr (hball1 ht1 hto))
  have hfi : Set.InjOn f (Set.Icc (0 : ℝ) 1) := by
    intro x hx y hy he
    exact congrArg Subtype.val (hemb.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) he)
  have hself : 2 * Module.finrank ℝ ℝ < Module.finrank ℝ G := by
    simp only [Module.finrank_self]
    omega
  have hobs : Module.finrank ℝ ℝ + Module.finrank ℝ V < Module.finrank ℝ G := by
    simpa only [Module.finrank_self] using hobdim
  obtain ⟨g, hg, hrel, hge, hgd, havoid⟩ :=
    Smale.ManifoldImmersion.exists_embedded_avoidance_relative_neighborhood_of_isClosed_range f o
      hf ho hclosed hself hobs CompactIccSpace.isCompact_Icc
      (show IsClosed C from Metric.isClosed_closedBall.union Metric.isClosed_closedBall) hBC hfi
      hfd hclean
  refine ⟨g, hg, ?_, ?_, hge, hgd, ?_⟩
  · filter_upwards [h0C, hfa] with t ht he
    exact (hrel.fst_eq_snd ht).symm.trans he
  · filter_upwards [h1C, hfb] with t ht he
    exact (hrel.fst_eq_snd ht).symm.trans he
  · intro t ht hto
    have htB : t ∉ ({0, 1} : Set ℝ) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨ne_of_gt ht.1, ne_of_lt ht.2⟩
    exact havoid t ⟨⟨ht.1.le, ht.2.le⟩, htB⟩ hto

private theorem
    Smale.NativeEuclideanEmbedding.exists_smooth_normalFrame_near_starConvex {E M D : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [NormedAddCommGroup D] [InnerProductSpace ℝ D]
    [FiniteDimensional ℝ D] (e : Smale.NativeEuclideanEmbedding E M) {f : D → M}
    (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f) {K : Set D} (hK : IsCompact K) (hz : (0 : D) ∈ K)
    (hstar : StarConvex ℝ (0 : D) K)
    (hi : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x)) (n : ℕ)
    (hcodim : Module.finrank ℝ D + n = Module.finrank ℝ E) :
    ∃ V : Set D,
      IsOpen V ∧
        K ⊆ V ∧
          ∃ A : D → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension),
            ContDiffOn ℝ ∞ A V ∧
              ∀ x ∈ K, Function.Injective (A x) ∧ (A x).range = e.diskNormalSpace f x := by
  obtain ⟨U, hU, hKU, hsP, hP⟩ := e.exists_open_diskNormalProjection hf hi
  have hidem : ∀ x ∈ K, IsIdempotentElem (e.diskNormalProjection f x) := by
    intro x hx
    rw [hP x (hKU hx)]
    exact (e.diskNormalSpace f x).isIdempotentElem_starProjection
  obtain ⟨V, hV, hKV, A, hA, hAi⟩ :=
    Smale.DiskFraming.exists_smooth_frame_near_starConvex hK hstar hU hKU
      (e.diskNormalProjection f) hidem hsP
  have hr : (e.diskNormalProjection f 0).range = e.diskNormalSpace f 0 := by
    rw [hP 0 (hKU hz), Submodule.range_starProjection]
  have hdim : Module.finrank ℝ (e.diskNormalSpace f 0) = n := by
    have h := e.finrank_diskTangent_add_normal hf (hi 0 hz)
    omega
  have hcenter : Module.finrank ℝ (e.diskNormalProjection f 0).range = n :=
    (congrArg
          (fun S : Submodule ℝ (EuclideanSpace ℝ (Fin e.ambientDimension)) => Module.finrank ℝ S)
          hr).trans
      hdim
  let φ : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (e.diskNormalProjection f 0).range :=
    ContinuousLinearEquiv.ofFinrankEq (finrank_euclideanSpace_fin.trans hcenter.symm)
  refine
    ⟨V, hV, hKV, fun x => (A x).comp φ.toContinuousLinearMap, hA.clm_comp contDiffOn_const, ?_⟩
  intro x hx
  refine ⟨((hAi x hx).1).comp φ.injective, ?_⟩
  calc
    ((A x).comp φ.toContinuousLinearMap).range = (A x).range :=
      LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr φ.surjective)
    _ = (e.diskNormalProjection f x).range := (hAi x hx).2
    _ = e.diskNormalSpace f x := by rw [hP x (hKU hx), Submodule.range_starProjection]

private theorem Smale.exists_tubularNeighborhood_in_open_of_embedded_starConvex_with_global_zero
    {E M D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D] {f : D → M}
    (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f) {K : Set D} (hK : IsCompact K) (hz : (0 : D) ∈ K)
    (hstar : StarConvex ℝ (0 : D) K) (hinj : Set.InjOn f K)
    (hi : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x)) (n : ℕ)
    (hcodim : Module.finrank ℝ D + n = Module.finrank ℝ E) {O : Set M} (hO : IsOpen O)
    (hfO : Set.MapsTo f K O) :
    ∃ ε : ℝ,
      0 < ε ∧
        ∃ Φ :
          PartialDiffeomorph 𝓘(ℝ, D × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E)
            (D × EuclideanSpace ℝ (Fin n)) M ∞,
          K ×ˢ Metric.closedBall 0 ε ⊆ Φ.source ∧ (∀ x, Φ (x, 0) = f x) ∧ Φ.target ⊆ O := by
  let : Nonempty M := ⟨f 0⟩
  obtain ⟨e⟩ := nonempty_nativeEuclideanEmbedding (E := E) (M := M)
  obtain ⟨r⟩ := e.nonempty_smoothRetraction
  obtain ⟨V, hV, hKV, A, hA, hframe⟩ :=
    e.exists_smooth_normalFrame_near_starConvex hf hK hz hstar hi n hcodim
  obtain ⟨Φ, hzero, -, hΦ⟩ :=
    r.exists_diskTubularNeighborhood hf hK hV hKV hinj hi hA (fun x hx => (hframe x hx).1)
      (fun x hx => (hframe x hx).2)
  let W := Φ.source ∩ Φ ⁻¹' O
  have hW : IsOpen W := Φ.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage Φ.open_source hO
  have hWloc : IsLocalDiffeomorphOn 𝓘(ℝ, D × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E) ∞ Φ W := fun p =>
    ⟨Φ, p.property.1, fun _ _ => rfl⟩
  let Ψ :=
    partialDiffeomorphOfInjectiveLocal hW (Φ.toPartialEquiv.injOn.mono Set.inter_subset_left)
      hWloc
  have hzeroΨ : K ×ˢ {(0 : EuclideanSpace ℝ (Fin n))} ⊆ Ψ.source := by
    rintro ⟨x, v⟩ ⟨hx, hv⟩
    have hv0 : v = 0 := hv
    subst v
    refine ⟨hzero ⟨hx, rfl⟩, ?_⟩
    change Φ (x, 0) ∈ O
    rw [hΦ, r.diskCoordinates_zero]
    exact hfO hx
  obtain ⟨ε, hε, hprod⟩ := DiskFraming.exists_pos_prod_closedBall_subset hK Ψ.open_source hzeroΨ
  refine ⟨ε, hε, Ψ, hprod, ?_, ?_⟩
  · intro x
    change Φ (x, 0) = f x
    rw [hΦ, r.diskCoordinates_zero]
  · change Φ '' W ⊆ O
    rintro _ ⟨p, hp, rfl⟩
    exact hp.2

private theorem
    Smale.exists_normed_tubularNeighborhood_in_open_of_embedded_starConvex_with_global_zero
    {E M D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D] {f : D → M}
    (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f) {K : Set D} (hK : IsCompact K) (hz : (0 : D) ∈ K)
    (hstar : StarConvex ℝ (0 : D) K) (hinj : Set.InjOn f K)
    (hi : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x)) (n : ℕ)
    (hcodim : Module.finrank ℝ D + n = Module.finrank ℝ E) {O : Set M} (hO : IsOpen O)
    (hfO : Set.MapsTo f K O) :
    ∃ ε : ℝ,
      0 < ε ∧
        ∃ Φ :
          PartialDiffeomorph 𝓘(ℝ, D × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E)
            (D × EuclideanSpace ℝ (Fin n)) M ∞,
          K ×ˢ Metric.closedBall 0 ε ⊆ Φ.source ∧ (∀ x, Φ (x, 0) = f x) ∧ Φ.target ⊆ O := by
  let D₀ := EuclideanSpace ℝ (Fin (Module.finrank ℝ D))
  let e : D₀ ≃L[ℝ] D := ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin
  let f₀ := f ∘ e
  let K₀ := e ⁻¹' K
  have hf₀ : ContMDiff 𝓘(ℝ, D₀) 𝓘(ℝ, E) ∞ f₀ := hf.comp e.contDiff.contMDiff
  have hK₀ : IsCompact K₀ := e.toHomeomorph.isCompact_preimage.mpr hK
  have hz₀ : (0 : D₀) ∈ K₀ := by
    change e 0 ∈ K
    simpa only [map_zero] using hz
  have hstar₀ : StarConvex ℝ (0 : D₀) K₀ := by
    apply StarConvex.linear_preimage e.toLinearMap
    simpa only [ContinuousLinearEquiv.coe_coe, map_zero] using hstar
  have hinj₀ : Set.InjOn f₀ K₀ := fun _ hx _ hy hxy => e.injective (hinj hx hy hxy)
  have hi₀ : ∀ x ∈ K₀, Function.Injective (mfderiv 𝓘(ℝ, D₀) 𝓘(ℝ, E) f₀ x) := by
    intro x hx
    exact
      (ManifoldImmersion.injective_mfderiv_comp_linearEquiv_iff e
            (hf.mdifferentiableAt (by simp))).mpr
        (hi (e x) hx)
  have hcodim₀ : Module.finrank ℝ D₀ + n = Module.finrank ℝ E := by
    simpa only [D₀, finrank_euclideanSpace_fin] using hcodim
  obtain ⟨ε, hε, Φ, hsource, hzero, htarget⟩ :=
    exists_tubularNeighborhood_in_open_of_embedded_starConvex_with_global_zero hf₀ hK₀ hz₀ hstar₀
      hinj₀ hi₀ n hcodim₀ hO (fun _ hx => hfO hx)
  let eprod := e.symm.prodCongr (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin n)))
  let c := eprod.toDiffeomorph
  let Ψ := c.toPartialDiffeomorph.trans Φ
  have hpre (x : D) (hx : x ∈ K) : e.symm x ∈ K₀ := by
    change e (e.symm x) ∈ K
    simpa only [e.apply_symm_apply] using hx
  refine ⟨ε, hε, Ψ, ?_, ?_, ?_⟩
  · rintro ⟨x, v⟩ ⟨hx, hv⟩
    exact ⟨Set.mem_univ _, hsource ⟨hpre x hx, hv⟩⟩
  · intro x
    change Φ (e.symm x, 0) = f x
    rw [hzero (e.symm x)]
    exact congrArg f (e.apply_symm_apply x)
  · intro y hy
    exact htarget hy.1

private theorem Smale.exists_local_tubularNeighborhood_of_embedded_starConvex {E M D : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D] {f : D → M} {K U : Set D}
    (hf : ContMDiffOn 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f U) (hK : IsCompact K) (hz : (0 : D) ∈ K)
    (hstar : StarConvex ℝ (0 : D) K) (hU : IsOpen U) (hKU : K ⊆ U) (hinj : Set.InjOn f K)
    (hi : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x)) (n : ℕ)
    (hcodim : Module.finrank ℝ D + n = Module.finrank ℝ E) {O : Set M} (hO : IsOpen O)
    (hfO : Set.MapsTo f K O) :
    ∃ ε : ℝ,
      0 < ε ∧
        ∃ Φ :
          PartialDiffeomorph 𝓘(ℝ, D × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E)
            (D × EuclideanSpace ℝ (Fin n)) M ∞,
          K ×ˢ Metric.closedBall 0 ε ⊆ Φ.source ∧
            Φ.source ⊆ U ×ˢ Set.univ ∧ (∀ x, (x, 0) ∈ Φ.source → Φ (x, 0) = f x) ∧ Φ.target ⊆ O :=
  by
  obtain ⟨g, hg, V, hV, hKV, hVU, heq⟩ :=
    exists_smooth_extension_near_starConvex hK hz hstar hU hKU hf
  have hinjg : Set.InjOn g K := by
    intro x hx y hy hxy
    apply hinj hx hy
    simpa only [heq (hKV hx), heq (hKV hy)] using hxy
  have hig : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) g x) := by
    intro x hx
    have hnear : g =ᶠ[𝓝 x] f := Filter.Eventually.mono (hV.mem_nhds (hKV hx)) heq
    rw [hnear.mfderiv_eq]
    exact hi x hx
  have hgO : Set.MapsTo g K O := by
    intro x hx
    rw [heq (hKV hx)]
    exact hfO hx
  obtain ⟨ε, hε, Φ, hsource, hzero, htarget⟩ :=
    exists_normed_tubularNeighborhood_in_open_of_embedded_starConvex_with_global_zero hg hK hz
      hstar hinjg hig n hcodim hO hgO
  let Ψ :=
    PartialChart.restrictSource Φ
      (hV.preimage (continuous_fst : Continuous (Prod.fst : D × EuclideanSpace ℝ (Fin n) → D)))
  refine ⟨ε, hε, Ψ, ?_, ?_, ?_, ?_⟩
  · intro p hp
    exact ⟨hsource hp, hKV hp.1⟩
  · intro p hp
    exact ⟨hVU hp.2, Set.mem_univ _⟩
  · intro x hx
    change Φ (x, 0) = f x
    exact (hzero x).trans (heq hx.2)
  · intro y hy
    exact htarget hy.1

private theorem Smale.exists_clean_tubularNeighborhood_of_embedded_starConvex {E M D : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D] {f : D → M} {K U : Set D}
    (hf : ContMDiffOn 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f U) (hK : IsCompact K) (hz : (0 : D) ∈ K)
    (hstar : StarConvex ℝ (0 : D) K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hemb : Topology.IsEmbedding (fun x : U => f x))
    (hi : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x)) (n : ℕ)
    (hcodim : Module.finrank ℝ D + n = Module.finrank ℝ E) {O : Set M} (hO : IsOpen O)
    (hfO : Set.MapsTo f K O) :
    ∃ ε : ℝ,
      0 < ε ∧
        ∃ Φ :
          PartialDiffeomorph 𝓘(ℝ, D × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E)
            (D × EuclideanSpace ℝ (Fin n)) M ∞,
          K ×ˢ Metric.closedBall 0 ε ⊆ Φ.source ∧
            Φ.source ⊆ U ×ˢ Set.univ ∧
              Φ.target ⊆ O ∧
                (∀ x, (x, 0) ∈ Φ.source → Φ (x, 0) = f x) ∧
                  (∀ q ∈ Φ.source, Φ q ∈ f '' U ↔ q.2 = 0) := by
  have hinj : Set.InjOn f K := by
    intro x hx y hy hxy
    exact
      congrArg Subtype.val
        (hemb.injective
          (show (fun u : U => f u) ⟨x, hKU hx⟩ = (fun u : U => f u) ⟨y, hKU hy⟩ from hxy))
  obtain ⟨a, ha, Φ, hprod, hsource, hzero, htarget⟩ :=
    exists_local_tubularNeighborhood_of_embedded_starConvex hf hK hz hstar hU hKU hinj hi n hcodim
      hO hfO
  have hbase : IsOpen {x : U | ((x : D), (0 : EuclideanSpace ℝ (Fin n))) ∈ Φ.source} :=
    Φ.open_source.preimage (continuous_subtype_val.prodMk continuous_const)
  obtain ⟨A, hA, hpreA⟩ := hemb.isInducing.isOpen_iff.mp hbase
  have haxis {x : D} (hx : x ∈ U) (hxA : f x ∈ A) : (x, 0) ∈ Φ.source := by
    have hx' : (⟨x, hx⟩ : U) ∈ (fun u : U => f u) ⁻¹' A := hxA
    rw [hpreA] at hx'
    exact hx'
  have hKA : Set.MapsTo f K A := by
    intro x hx
    have hx' :
      (⟨x, hKU hx⟩ : U) ∈ {u : U | ((u : D), (0 : EuclideanSpace ℝ (Fin n))) ∈ Φ.source} :=
      hprod ⟨hx, Metric.mem_closedBall_self ha.le⟩
    rw [← hpreA] at hx'
    exact hx'
  let Ψ := PartialChart.restrictTarget Φ hA
  have hKzero : K ×ˢ {(0 : EuclideanSpace ℝ (Fin n))} ⊆ Ψ.source := by
    rintro ⟨x, v⟩ ⟨hx, hv⟩
    have hv0 : v = 0 := hv
    subst v
    have hxΦ := hprod ⟨hx, Metric.mem_closedBall_self ha.le⟩
    refine ⟨hxΦ, ?_⟩
    change Φ (x, 0) ∈ A
    rw [hzero x hxΦ]
    exact hKA hx
  obtain ⟨ε, hε, hεprod⟩ := DiskFraming.exists_pos_prod_closedBall_subset hK Ψ.open_source hKzero
  refine
    ⟨ε, hε, Ψ, hεprod, fun _ hq => hsource hq.1, fun _ hy => htarget hy.1, fun x hx =>
      hzero x hx.1, ?_⟩
  rintro ⟨x, z⟩ hq
  constructor
  · rintro ⟨u, hu, heq⟩
    have huA : f u ∈ A := heq ▸ hq.2
    have huΦ := haxis hu huA
    have hpair : (x, z) = (u, 0) :=
      Φ.toPartialEquiv.injOn hq.1 huΦ (heq.symm.trans (hzero u huΦ).symm)
    exact congrArg Prod.snd hpair
  · intro hz
    change z = 0 at hz
    subst z
    exact ⟨x, (hsource hq.1).1, (hzero x hq.1).symm⟩

private theorem
    Smale.exists_clean_embedded_sheet_neighborhood {E M D G N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace N]
    [ChartedSpace G N] {F : N → M} (hF : ContMDiff 𝓘(ℝ, G) 𝓘(ℝ, E) ∞ F)
    (hembF : Topology.IsEmbedding F) (c : PartialDiffeomorph 𝓘(ℝ, D) 𝓘(ℝ, G) D N ∞) {K : Set D}
    (hK : IsCompact K) (hz : (0 : D) ∈ K) (hstar : StarConvex ℝ (0 : D) K) (hKc : K ⊆ c.source)
    (hiF : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, G) 𝓘(ℝ, E) F (c x))) (n : ℕ)
    (hcodim : Module.finrank ℝ D + n = Module.finrank ℝ E) {O : Set M} (hO : IsOpen O)
    (hFO : Set.MapsTo (F ∘ c) K O) :
    ∃ ε : ℝ,
      0 < ε ∧
        ∃ Φ :
          PartialDiffeomorph 𝓘(ℝ, D × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E)
            (D × EuclideanSpace ℝ (Fin n)) M ∞,
          K ×ˢ Metric.closedBall 0 ε ⊆ Φ.source ∧
            Φ.source ⊆ c.source ×ˢ Set.univ ∧
              Φ.target ⊆ O ∧
                (∀ x, (x, 0) ∈ Φ.source → Φ (x, 0) = F (c x)) ∧
                  (∀ q ∈ Φ.source, Φ q ∈ Set.range F ↔ q.2 = 0) := by
  let f := F ∘ c
  have hf : ContMDiffOn 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f c.source := hF.comp_contMDiffOn c.contMDiffOn_toFun
  have hembf : Topology.IsEmbedding (fun x : c.source => f x) :=
    hembF.comp c.toOpenPartialHomeomorph.isEmbedding_restrict
  have hi : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x) := by
    intro x hx
    rw [mfderiv_comp x (hF.mdifferentiableAt (by simp)) (c.mdifferentiableAt (by simp) (hKc hx))]
    exact (hiF x hx).comp (PartialChart.bijective_mfderiv c (hKc hx)).1
  obtain ⟨A, hA, hpreA⟩ := hembF.isInducing.isOpen_iff.mp c.open_target
  have hfA : Set.MapsTo f K A := by
    intro x hx
    change c x ∈ F ⁻¹' A
    rw [hpreA]
    exact c.map_source' (hKc hx)
  obtain ⟨ε, hε, Φ, hprod, hsource, htarget, hzero, himage⟩ :=
    exists_clean_tubularNeighborhood_of_embedded_starConvex hf hK hz hstar c.open_source hKc hembf
      hi n hcodim (hO.inter hA) (fun x hx => ⟨hFO hx, hfA hx⟩)
  refine ⟨ε, hε, Φ, hprod, hsource, fun _ hy => (htarget hy).1, hzero, ?_⟩
  intro q hq
  have hqA := (htarget (Φ.map_source' hq)).2
  have hrange : Φ q ∈ Set.range F ↔ Φ q ∈ f '' c.source := by
    constructor
    · rintro ⟨y, hy⟩
      have hyA : F y ∈ A := hy ▸ hqA
      have hyT : y ∈ c.target := by
        change y ∈ F ⁻¹' A at hyA
        rwa [hpreA] at hyA
      exact ⟨c.invFun y, c.map_target' hyT, (congrArg F (c.right_inv' hyT)).trans hy⟩
    · rintro ⟨u, _, hu⟩
      exact ⟨c u, hu⟩
  exact hrange.trans (himage q hq)

private def MorseCancel.sheetAxisShuffle {D B : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup B] [NormedSpace ℝ B] : (ℝ × (D × B)) ≃L[ℝ] (D × (ℝ × B))
    where
  toLinearEquiv :=
    { toFun := fun p => (p.2.1, (p.1, p.2.2))
      invFun := fun p => (p.2.1, (p.1, p.2.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  continuous_toFun := continuous_snd.fst.prodMk (continuous_fst.prodMk continuous_snd.snd)
  continuous_invFun := continuous_snd.fst.prodMk (continuous_fst.prodMk continuous_snd.snd)

private theorem MorseCancel.exists_clean_sheet_axis_chart {D : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] {E M X : Type*} [FiniteDimensional ℝ D] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [TopologicalSpace X] [ChartedSpace D X]
    [IsManifold 𝓘(ℝ, D) ∞ X] {f : X → M} (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f)
    (hemb : Topology.IsEmbedding f) (hi : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x))
    (n : ℕ) (hdim : Module.finrank ℝ D + (1 + n) = Module.finrank ℝ E) (x : X) {U : Set M}
    (hU : IsOpen U) (hxU : f x ∈ U) :
    ∃ Φ :
      PartialDiffeomorph 𝓘(ℝ, ℝ × (D × EuclideanSpace ℝ (Fin n))) 𝓘(ℝ, E)
        (ℝ × (D × EuclideanSpace ℝ (Fin n))) M ∞,
      (0 : ℝ × (D × EuclideanSpace ℝ (Fin n))) ∈ Φ.source ∧
        Φ 0 = f x ∧ Φ.target ⊆ U ∧ ∀ z ∈ Φ.source, Φ z ∈ Set.range f ↔ z.1 = 0 ∧ z.2.2 = 0 := by
  let c := Smale.NativeParametrization.centered (D := D) x
  have hc0 : (0 : D) ∈ c.source := Smale.NativeParametrization.zero_mem_centered_source x
  have hcx : c 0 = x := Smale.NativeParametrization.centered_zero x
  obtain ⟨ε, hε, Q, hprod, -, hQU, hzero, hrecognition⟩ :=
    Smale.exists_clean_embedded_sheet_neighborhood hf hemb c isCompact_singleton
      (Set.mem_singleton (0 : D)) (starConvex_singleton (0 : D))
      (Set.singleton_subset_iff.mpr hc0) (fun z _ => hi (c z)) (1 + n) hdim hU
      (show Set.MapsTo (f ∘ c) {0} U by
        intro z hz
        rcases Set.mem_singleton_iff.mp hz with rfl
        change f (c 0) ∈ U
        rw [hcx]
        exact hxU)
  let B := EuclideanSpace ℝ (Fin n)
  let N := EuclideanSpace ℝ (Fin (1 + n))
  let L : (ℝ × B) ≃L[ℝ] N :=
    ContinuousLinearEquiv.ofFinrankEq
      (by simp only [B, N, Module.finrank_prod, Module.finrank_self, finrank_euclideanSpace_fin])
  let P : (ℝ × (D × B)) ≃L[ℝ] (D × N) :=
    (sheetAxisShuffle (D := D) (B := B)).trans ((ContinuousLinearEquiv.refl ℝ D).prodCongr L)
  let Φ := P.toDiffeomorph.toPartialDiffeomorph.trans Q
  have hQ0 : (0 : D × N) ∈ Q.source :=
    hprod ⟨Set.mem_singleton 0, Metric.mem_closedBall_self hε.le⟩
  have hΦ0 : (0 : ℝ × (D × B)) ∈ Φ.source := by
    refine ⟨Set.mem_univ _, ?_⟩
    change P 0 ∈ Q.source
    rw [map_zero]
    exact hQ0
  refine ⟨Φ, hΦ0, ?_, fun z hz => hQU hz.1, ?_⟩
  · change Q (P 0) = f x
    rw [map_zero]
    exact (hzero 0 hQ0).trans (congrArg f hcx)
  · intro z hz
    change Q (P z) ∈ Set.range f ↔ _
    rw [hrecognition (P z) hz.2]
    change L (z.1, z.2.2) = 0 ↔ z.1 = 0 ∧ z.2.2 = 0
    constructor
    · intro h
      have he : (z.1, z.2.2) = (0, (0 : B)) := L.injective (h.trans L.map_zero.symm)
      exact ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩
    · rintro ⟨h1, h2⟩
      rw [h1, h2]
      exact L.map_zero

private theorem MorseCancel.chart_axis_curve_properties {V E H M : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {J : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) J (ℝ × V) M ∞) (p : ℝ) (hp : (p, (0 : V)) ∈ Φ.source) :
    ∃ U : Set ℝ,
      IsOpen U ∧
        p ∈ U ∧
          (∀ t ∈ U, (t, (0 : V)) ∈ Φ.source) ∧
            ContMDiffOn 𝓘(ℝ, ℝ) J ∞ (fun t => Φ (t, (0 : V))) U ∧
              Function.Injective (mfderiv 𝓘(ℝ, ℝ) J (fun t => Φ (t, (0 : V))) p) := by
  let L := ContinuousLinearMap.inl ℝ ℝ V
  have hL : ContDiff ℝ ∞ L := L.contDiff
  let U : Set ℝ := L ⁻¹' Φ.source
  have hU : IsOpen U := Φ.open_source.preimage L.continuous
  have hcurve : ContMDiffOn 𝓘(ℝ, ℝ) J ∞ (Φ ∘ L) U :=
    Φ.contMDiffOn_toFun.comp hL.contMDiff.contMDiffOn (fun _ ht => ht)
  refine ⟨U, hU, hp, fun _ ht => ht, hcurve, ?_⟩
  change Function.Injective (mfderiv 𝓘(ℝ, ℝ) J (Φ ∘ L) p)
  rw [mfderiv_comp p (Φ.mdifferentiableAt (by simp) hp)
      (hL.contMDiff.mdifferentiableAt (by simp)),
    mfderiv_eq_fderiv, L.fderiv]
  exact
    (Smale.PartialChart.bijective_mfderiv Φ hp).injective.comp (fun _ _ h => congrArg Prod.fst h)

private def
    MorseCancel.terminalSheetCoordinates {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] :
    Diffeomorph 𝓘(ℝ, ℝ × (D × D)) 𝓘(ℝ, ℝ × (D × D)) (ℝ × (D × D)) (ℝ × (D × D)) ∞
    where
  toEquiv :=
    { toFun := fun z => (z.1 - 1, (z.2.2, z.2.1))
      invFun := fun z => (z.1 + 1, (z.2.2, z.2.1))
      left_inv := by intro z; ext <;> simp
      right_inv := by intro z; ext <;> simp }
  contMDiff_toFun :=
    ((contDiff_fst.sub contDiff_const).prodMk
        (contDiff_snd.snd.prodMk contDiff_snd.fst)).contMDiff
  contMDiff_invFun :=
    ((contDiff_fst.add contDiff_const).prodMk
        (contDiff_snd.snd.prodMk contDiff_snd.fst)).contMDiff

private theorem MorseCancel.exists_clean_two_sheet_arc {E M X Y : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) X] [IsManifold (𝓡 2) ∞ X] [CompactSpace X]
    [SecondCountableTopology X] [TopologicalSpace Y] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) Y]
    [IsManifold (𝓡 2) ∞ Y] [CompactSpace Y] [SecondCountableTopology Y] {f : X → M} {g : Y → M}
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, E) ∞ f) (hg : ContMDiff (𝓡 2) 𝓘(ℝ, E) ∞ g)
    (hfe : Topology.IsEmbedding f) (hge : Topology.IsEmbedding g)
    (hfi : ∀ x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, E) f x))
    (hgi : ∀ y, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, E) g y)) (hdim : Module.finrank ℝ E = 5)
    (x : X) (y : Y) (hx : f x ∉ Set.range g) (hy : g y ∉ Set.range f) (γ : Path (f x) (g y)) :
    ∃ Φ Ψ :
      PartialDiffeomorph 𝓘(ℝ, (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))))
        𝓘(ℝ, E) (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) M ∞,
      (0 : (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))) ∈ Φ.source ∧
        ((1 : ℝ), (0 : (EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) ∈ Ψ.source ∧
          Φ 0 = f x ∧
            Ψ (1, 0) = g y ∧
              Φ.target ⊆ (Set.range g)ᶜ ∧
                Ψ.target ⊆ (Set.range f)ᶜ ∧
                  (∀ z ∈ Φ.source, Φ z ∈ Set.range f ↔ z.1 = 0 ∧ z.2.2 = 0) ∧
                    (∀ z ∈ Ψ.source, Ψ z ∈ Set.range g ↔ z.1 = 1 ∧ z.2.1 = 0) ∧
                      ∃ a : C(ℝ, M),
                        ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ a ∧
                          (a =ᶠ[𝓝 (0 : ℝ)] fun t => Φ (t, 0)) ∧
                            (a =ᶠ[𝓝 (1 : ℝ)] fun t => Ψ (t, 0)) ∧
                              Topology.IsClosedEmbedding (fun t : unitInterval => a t) ∧
                                (∀ t ∈ Set.Icc (0 : ℝ) 1,
                                    Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) a t)) ∧
                                  (∀ t ∈ Set.Icc (0 : ℝ) 1, a t ∈ Set.range f ↔ t = 0) ∧
                                    (∀ t ∈ Set.Icc (0 : ℝ) 1, a t ∈ Set.range g ↔ t = 1) := by
  have hclosedf : IsClosed (Set.range f) := (isCompact_range hf.continuous).isClosed
  have hclosedg : IsClosed (Set.range g) := (isCompact_range hg.continuous).isClosed
  have hcodim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) + (1 + 2) = Module.finrank ℝ E := by
    rw [finrank_euclideanSpace_fin, hdim]
  obtain ⟨Φ, hΦ0, hΦx, hΦavoid, hΦrec⟩ :=
    exists_clean_sheet_axis_chart hf hfe hfi 2 hcodim x hclosedg.isOpen_compl hx
  obtain ⟨Q, hQ0, hQy, hQavoid, hQrec⟩ :=
    exists_clean_sheet_axis_chart hg hge hgi 2 hcodim y hclosedf.isOpen_compl hy
  let T := terminalSheetCoordinates (D := (EuclideanSpace ℝ (Fin 2)))
  let Ψ := T.toPartialDiffeomorph.trans Q
  have hT1 : T ((1 : ℝ), (0 : (EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) = 0 := by
    change ((1 : ℝ) - 1, ((0 : (EuclideanSpace ℝ (Fin 2))), (0 : (EuclideanSpace ℝ (Fin 2))))) = 0
    rw [sub_self]
    rfl
  have hΨ1 :
    ((1 : ℝ), (0 : (EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) ∈ Ψ.source := by
    refine ⟨Set.mem_univ _, ?_⟩
    change T (1, 0) ∈ Q.source
    rw [hT1]
    exact hQ0
  have hΨy : Ψ (1, 0) = g y := by
    change Q (T (1, 0)) = g y
    rw [hT1]
    exact hQy
  have hΨavoid : Ψ.target ⊆ (Set.range f)ᶜ := fun z hz => hQavoid hz.1
  have hΨrec : ∀ z ∈ Ψ.source, Ψ z ∈ Set.range g ↔ z.1 = 1 ∧ z.2.1 = 0 := by
    intro z hz
    change Q (T z) ∈ Set.range g ↔ _
    rw [hQrec (T z) hz.2]
    change z.1 - 1 = 0 ∧ z.2.1 = 0 ↔ _
    rw [sub_eq_zero]
  let o : C(X ⊕ Y, M) := ⟨Sum.elim f g, hf.continuous.sumElim hg.continuous⟩
  have ho : ContMDiff (𝓡 2) 𝓘(ℝ, E) ∞ o := hf.sumElim hg
  have horange : Set.range o = Set.range f ∪ Set.range g := by
    ext z
    constructor
    · rintro ⟨a | b, he⟩
      · exact Or.inl ⟨a, he⟩
      · exact Or.inr ⟨b, he⟩
    · rintro (⟨a, he⟩ | ⟨b, he⟩)
      · exact ⟨Sum.inl a, he⟩
      · exact ⟨Sum.inr b, he⟩
  have hoclosed : IsClosed (Set.range o) := by rw [horange]; exact hclosedf.union hclosedg
  obtain ⟨U, hU, h0U, hUΦ, ha, hia⟩ := chart_axis_curve_properties Φ 0 hΦ0
  obtain ⟨W, hW, h1W, hWΨ, hb, hib⟩ := chart_axis_curve_properties Ψ 1 hΨ1
  have hclean0 :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      Φ (t, (0 : (EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) ∈ Set.range o →
        t = 0 := by
    filter_upwards [hU.mem_nhds h0U] with t ht
    rw [horange]
    rintro (h | h)
    · exact ((hΦrec (t, 0) (hUΦ t ht)).mp h).1
    · exact (hΦavoid (Φ.map_source' (hUΦ t ht)) h).elim
  have hclean1 :
    ∀ᶠ t in 𝓝 (1 : ℝ),
      Ψ (t, (0 : (EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) ∈ Set.range o →
        t = 1 := by
    filter_upwards [hW.mem_nhds h1W] with t ht
    rw [horange]
    rintro (h | h)
    · exact (hΨavoid (Ψ.map_source' (hWΨ t ht)) h).elim
    · exact ((hΨrec (t, 0) (hWΨ t ht)).mp h).1
  have hxy : f x ≠ g y := fun h => hx ⟨y, h.symm⟩
  have hends : Φ (0, 0) ≠ Ψ (1, 0) := by
    change Φ 0 ≠ Ψ (1, 0)
    rw [hΦx, hΨy]
    exact hxy
  obtain ⟨a, ha', hleft, hright, hemb, hi, havoid⟩ :=
    exists_clean_arc_with_local_endpoint_germs ha hb hU hW h0U h1W hia hib (γ.cast hΦx hΨy) hends
      (by omega) o ho hoclosed (by rw [finrank_euclideanSpace_fin, hdim]; norm_num) hclean0
      hclean1
  have ha0 : a 0 = f x := hleft.eq_of_nhds.trans hΦx
  have ha1 : a 1 = g y := hright.eq_of_nhds.trans hΨy
  refine
    ⟨Φ, Ψ, hΦ0, hΨ1, hΦx, hΨy, hΦavoid, hΨavoid, hΦrec, hΨrec, a, ha', hleft, hright, hemb, hi,
      ?_, ?_⟩
  · intro t ht
    constructor
    · intro h
      by_contra ht0
      have ht1 : t ≠ 1 := by intro he; subst t; rw [ha1] at h; exact hy h
      exact
        havoid t ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
          (horange.symm ▸ Or.inl h)
    · intro he
      subst t
      rw [ha0]
      exact Set.mem_range_self x
  · intro t ht
    constructor
    · intro h
      by_contra ht1
      have ht0 : t ≠ 0 := by intro he; subst t; rw [ha0] at h; exact hx h
      exact
        havoid t ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
          (horange.symm ▸ Or.inr h)
    · intro he
      subst t
      rw [ha1]
      exact Set.mem_range_self y

private theorem
    Smale.TransverseCoordinates.surjective_coprod_swap {D Z E : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E]
    [NormedSpace ℝ E] (A : D →L[ℝ] E) (C : Z →L[ℝ] E) (h : Function.Surjective (A.coprod C)) :
    Function.Surjective (C.coprod A) := by
  intro w
  obtain ⟨⟨u, v⟩, huv⟩ := h w
  refine ⟨(v, u), ?_⟩
  change C v + A u = w
  rw [add_comm]
  exact huv

private theorem Smale.TransverseCoordinates.surjective_normal_comp {D Z E B : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup B] [NormedSpace ℝ B]
    (Q : E →L[ℝ] B) (A : D →L[ℝ] E) (C : Z →L[ℝ] E) (hQ : Function.Surjective Q)
    (hAC : Function.Surjective (A.coprod C)) (hQA : Q.comp A = 0) :
    Function.Surjective (Q.comp C) := by
  intro w
  obtain ⟨z, hz⟩ := hQ w
  obtain ⟨⟨u, v⟩, huv⟩ := hAC z
  have hAu : Q (A u) = 0 := congrArg (fun T : D →L[ℝ] B => T u) hQA
  refine ⟨v, ?_⟩
  change Q (C v) = w
  have hsum : Q (A u + C v) = w := (congrArg Q huv).trans hz
  simpa only [map_add, hAu, zero_add] using hsum

private theorem
    Smale.TransverseCoordinates.bijective_normal_comp {D Z E B : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ Z]
    [FiniteDimensional ℝ B] (Q : E →L[ℝ] B) (A : D →L[ℝ] E) (C : Z →L[ℝ] E)
    (hQ : Function.Surjective Q) (hAC : Function.Surjective (A.coprod C)) (hQA : Q.comp A = 0)
    (hdim : Module.finrank ℝ Z = Module.finrank ℝ B) : Function.Bijective (Q.comp C) := by
  have hs := surjective_normal_comp Q A C hQ hAC hQA
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hs, hs⟩

private def
    Smale.FrameField.complementQuotient {D Z F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (G : D →L[ℝ] F) (C : Z →L[ℝ] F) : F →L[ℝ] Z :=
  (ContinuousLinearMap.snd ℝ D Z).comp (G.coprod C).inverse

private theorem Smale.FrameField.complementQuotient_left {D Z F : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (G : D →L[ℝ] F) (C : Z →L[ℝ] F) (h : (G.coprod C).IsInvertible) (u : D) :
    complementQuotient G C (G u) = 0 := by
  have hi := h.inverse_apply_self (u, 0)
  change (G.coprod C).inverse (G u + C 0) = (u, 0) at hi
  rw [map_zero, add_zero] at hi
  exact congrArg Prod.snd hi

private theorem Smale.FrameField.complementQuotient_right {D Z F : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (G : D →L[ℝ] F) (C : Z →L[ℝ] F) (h : (G.coprod C).IsInvertible) (v : Z) :
    complementQuotient G C (C v) = v := by
  have hi := h.inverse_apply_self (0, v)
  change (G.coprod C).inverse (G 0 + C v) = (0, v) at hi
  rw [map_zero, zero_add] at hi
  exact congrArg Prod.snd hi

private theorem Smale.FrameField.ker_complementQuotient {D Z F : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (G : D →L[ℝ] F) (C : Z →L[ℝ] F) (h : (G.coprod C).IsInvertible) :
    (complementQuotient G C).ker = G.range := by
  ext w
  constructor
  · intro hw
    let p := (G.coprod C).inverse w
    have hp : p.2 = 0 := hw
    have hi := h.self_apply_inverse w
    change G p.1 + C p.2 = w at hi
    rw [hp, map_zero, add_zero] at hi
    exact ⟨p.1, hi⟩
  · rintro ⟨u, rfl⟩
    exact complementQuotient_left G C h u

private theorem Smale.FrameField.bijective_coprod_of_quotient {D Z F : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (G : D →L[ℝ] F) (C H : Z →L[ℝ] F) (h : (G.coprod C).IsInvertible)
    (hH : Function.Bijective ((complementQuotient G C).comp H)) :
    Function.Bijective (G.coprod H) := by
  have hG : Function.Injective G := by
    intro u v huv
    have hpair : (G.coprod C) (u, 0) = (G.coprod C) (v, 0) := by
      change G u + C 0 = G v + C 0
      rw [huv]
    exact congrArg Prod.fst (h.injective hpair)
  constructor
  · intro p q hpq
    have hq := congrArg (complementQuotient G C) hpq
    change complementQuotient G C (G p.1 + H p.2) = complementQuotient G C (G q.1 + H q.2) at hq
    rw [map_add, map_add, complementQuotient_left G C h, complementQuotient_left G C h, zero_add,
      zero_add] at hq
    have hp₂ : p.2 = q.2 := hH.1 hq
    have hp₁ : p.1 = q.1 := by
      change G p.1 + H p.2 = G q.1 + H q.2 at hpq
      rw [hp₂] at hpq
      exact hG (add_right_cancel hpq)
    exact Prod.ext hp₁ hp₂
  · intro w
    obtain ⟨v, hv⟩ := hH.2 (complementQuotient G C w)
    have hmem : w - H v ∈ G.range := by
      rw [← ker_complementQuotient G C h]
      change complementQuotient G C (w - H v) = 0
      rw [map_sub]
      change complementQuotient G C w - ((complementQuotient G C).comp H) v = 0
      rw [hv, sub_self]
    obtain ⟨u, hu⟩ := hmem
    refine ⟨(u, v), ?_⟩
    change G u + H v = w
    change G u = w - H v at hu
    rw [hu, sub_add_cancel]

private def
    Smale.FrameField.correctedComplement {D Z F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (G : D →L[ℝ] F) (C L : Z →L[ℝ] F) (K : Z →L[ℝ] Z) : Z →L[ℝ] F :=
  L + C.comp (K - (complementQuotient G C).comp L)

private theorem Smale.FrameField.quotient_correctedComplement {D Z F : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (G : D →L[ℝ] F) (C L : Z →L[ℝ] F) (K : Z →L[ℝ] Z)
    (h : (G.coprod C).IsInvertible) :
    (complementQuotient G C).comp (correctedComplement G C L K) = K := by
  apply ContinuousLinearMap.ext
  intro v
  change complementQuotient G C (L v + C ((K - (complementQuotient G C).comp L) v)) = K v
  rw [map_add, complementQuotient_right G C h]
  change complementQuotient G C (L v) + (K v - complementQuotient G C (L v)) = K v
  rw [← add_sub_assoc, add_sub_cancel_left]

private theorem Smale.FrameField.correctedComplement_self {D Z F : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (G : D →L[ℝ] F) (C L : Z →L[ℝ] F) :
    correctedComplement G C L ((complementQuotient G C).comp L) = L := by
  simp only [correctedComplement, sub_self, ContinuousLinearMap.comp_zero, add_zero]

private theorem Smale.FrameField.bijective_coprod_correctedComplement {D Z F : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (G : D →L[ℝ] F) (C L : Z →L[ℝ] F) (K : Z →L[ℝ] Z)
    (h : (G.coprod C).IsInvertible) (hK : Function.Bijective K) :
    Function.Bijective (G.coprod (correctedComplement G C L K)) := by
  apply bijective_coprod_of_quotient G C _ h
  rw [quotient_correctedComplement G C L K h]
  exact hK

private theorem Smale.FrameField.contDiffOn_coprod {X D Z F : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [NormedAddCommGroup F] [NormedSpace ℝ F] {G : X → (D →L[ℝ] F)}
    {C : X → (Z →L[ℝ] F)} {U : Set X} (hG : ContDiffOn ℝ ∞ G U) (hC : ContDiffOn ℝ ∞ C U) :
    ContDiffOn ℝ ∞ (fun x => (G x).coprod (C x)) U :=
  (hG.clm_comp (contDiffOn_const (c := ContinuousLinearMap.fst ℝ D Z))).add
    (hC.clm_comp (contDiffOn_const (c := ContinuousLinearMap.snd ℝ D Z)))

public
theorem Smale.FrameField.isInvertible_coprod_of_bijective {D Z F : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ D] [FiniteDimensional ℝ Z] (G : D →L[ℝ] F)
    (C : Z →L[ℝ] F) (h : Function.Bijective (G.coprod C)) : (G.coprod C).IsInvertible := by
  let e := (LinearEquiv.ofBijective (G.coprod C).toLinearMap h).toContinuousLinearEquiv
  exact ⟨e, rfl⟩

private theorem
    Smale.FrameField.contDiffOn_complementQuotient {X D Z F : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ D]
    [FiniteDimensional ℝ Z] {G : X → (D →L[ℝ] F)} {C : X → (Z →L[ℝ] F)} {U : Set X}
    (hU : IsOpen U) (hG : ContDiffOn ℝ ∞ G U) (hC : ContDiffOn ℝ ∞ C U)
    (hi : ∀ x ∈ U, ((G x).coprod (C x)).IsInvertible) :
    ContDiffOn ℝ ∞ (fun x => complementQuotient (G x) (C x)) U := by
  have hT := contDiffOn_coprod hG hC
  have hInv : ContDiffOn ℝ ∞ (fun x => ((G x).coprod (C x)).inverse) U := by
    intro x hx
    exact
      ((hi x hx).contDiffAt_map_inverse.comp x (hT.contDiffAt (hU.mem_nhds hx))).contDiffWithinAt
  exact contDiffOn_const.clm_comp hInv

private theorem
    Smale.FrameField.contDiffOn_correctedComplement {X D Z F : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ D]
    [FiniteDimensional ℝ Z] {G : X → (D →L[ℝ] F)} {C L : X → (Z →L[ℝ] F)} {K : X → (Z →L[ℝ] Z)}
    {U : Set X} (hU : IsOpen U) (hG : ContDiffOn ℝ ∞ G U) (hC : ContDiffOn ℝ ∞ C U)
    (hL : ContDiffOn ℝ ∞ L U) (hK : ContDiffOn ℝ ∞ K U)
    (hi : ∀ x ∈ U, ((G x).coprod (C x)).IsInvertible) :
    ContDiffOn ℝ ∞ (fun x => correctedComplement (G x) (C x) (L x) (K x)) U :=
  hL.add (hC.clm_comp (hK.sub ((contDiffOn_complementQuotient hU hG hC hi).clm_comp hL)))

private def Smale.FrameField.shearedBlock {X Z F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : Z →L[ℝ] X) (T : Z →L[ℝ] F) : (X × Z) →L[ℝ] (X × F) :=
  (ContinuousLinearMap.inl ℝ X F).coprod (A.prod T)

private theorem Smale.FrameField.shearedBlock_apply {X Z F : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (A : Z →L[ℝ] X) (T : Z →L[ℝ] F) (p : X × Z) :
    shearedBlock A T p = (p.1 + A p.2, T p.2) := by
  simp [shearedBlock, ContinuousLinearMap.coprod_apply]

private theorem Smale.FrameField.shearedBlock_horizontal {X Z F : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (A : Z →L[ℝ] X) (T : Z →L[ℝ] F) (x : X) :
    shearedBlock A T (x, 0) = (x, 0) := by simp only [shearedBlock_apply, map_zero, add_zero]

private theorem Smale.FrameField.bijective_shearedBlock {X Z F : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (A : Z →L[ℝ] X) (T : Z →L[ℝ] F) (hi : Function.Bijective T) :
    Function.Bijective (shearedBlock A T) := by
  constructor
  · intro p q hpq
    have hz : p.2 = q.2 := hi.1 (by simpa only [shearedBlock_apply] using congrArg Prod.snd hpq)
    have hx : p.1 + A p.2 = q.1 + A q.2 := by
      simpa only [shearedBlock_apply] using congrArg Prod.fst hpq
    rw [hz] at hx
    exact Prod.ext (add_right_cancel hx) hz
  · intro q
    obtain ⟨z, hz⟩ := hi.2 q.2
    refine ⟨(q.1 - A z, z), ?_⟩
    rw [shearedBlock_apply]
    simp only [sub_add_cancel, hz]

private def Smale.FrameField.shearedMap {X Z F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : X → (Z →L[ℝ] X)) (T : X → (Z →L[ℝ] F)) (p : X × Z) : X × F :=
  (p.1 + A p.1 p.2, T p.1 p.2)

private theorem
    Smale.FrameField.shearedMap_zero {X Z F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : X → (Z →L[ℝ] X)) (T : X → (Z →L[ℝ] F)) (x : X) : shearedMap A T (x, 0) = (x, 0) := by
  simp only [shearedMap, map_zero, add_zero]

private theorem Smale.FrameField.contDiffOn_shearedMap {X Z F : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {A : X → (Z →L[ℝ] X)} {T : X → (Z →L[ℝ] F)} {U : Set X}
    (hA : ContDiffOn ℝ ∞ A U) (hT : ContDiffOn ℝ ∞ T U) :
    ContDiffOn ℝ ∞ (shearedMap A T) (Prod.fst ⁻¹' U) :=
  (contDiffOn_fst.add ((hA.comp contDiffOn_fst (fun _ hp => hp)).clm_apply contDiffOn_snd)).prodMk
    ((hT.comp contDiffOn_fst (fun _ hp => hp)).clm_apply contDiffOn_snd)

private theorem Smale.FrameField.hasFDerivAt_shearedMap_zero {X Z F : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {A : X → (Z →L[ℝ] X)} {T : X → (Z →L[ℝ] F)} {x : X}
    (hA : DifferentiableAt ℝ A x) (hT : DifferentiableAt ℝ T x) :
    HasFDerivAt (shearedMap A T) (shearedBlock (A x) (T x)) (x, 0) := by
  have hAa :
    HasFDerivAt (fun p : X × Z => A p.1) ((fderiv ℝ A x).comp (ContinuousLinearMap.fst ℝ X Z))
      (x, 0) :=
    hA.hasFDerivAt.comp (x, 0) hasFDerivAt_fst
  have hTt :
    HasFDerivAt (fun p : X × Z => T p.1) ((fderiv ℝ T x).comp (ContinuousLinearMap.fst ℝ X Z))
      (x, 0) :=
    hT.hasFDerivAt.comp (x, 0) hasFDerivAt_fst
  have hs : HasFDerivAt (fun p : X × Z => p.2) (ContinuousLinearMap.snd ℝ X Z) (x, 0) :=
    hasFDerivAt_snd
  have hf : HasFDerivAt (fun p : X × Z => p.1) (ContinuousLinearMap.fst ℝ X Z) (x, 0) :=
    hasFDerivAt_fst
  have hd := (hf.add (hAa.clm_apply hs)).prodMk (hTt.clm_apply hs)
  convert hd using 1 <;>
    first
    | rfl
    | (apply ContinuousLinearMap.ext; intro p; simp [shearedBlock_apply])

private theorem Smale.FrameField.isInvertible_shearedBlock {X Z F : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ X] [FiniteDimensional ℝ Z] (A : Z →L[ℝ] X)
    (T : Z →L[ℝ] F) (hi : T.IsInvertible) : (shearedBlock A T).IsInvertible := by
  let e :=
    (LinearEquiv.ofBijective (shearedBlock A T).toLinearMap
        (bijective_shearedBlock A T hi.bijective)).toContinuousLinearEquiv
  exact ⟨e, rfl⟩

private theorem Smale.FrameField.exists_sheared_frame_chart {X Z F : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ X] [FiniteDimensional ℝ Z] {A : X → (Z →L[ℝ] X)}
    {T : X → (Z →L[ℝ] F)} {K U : Set X} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hA : ContDiffOn ℝ ∞ A U) (hT : ContDiffOn ℝ ∞ T U) (hi : ∀ x ∈ K, (T x).IsInvertible) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, X × Z) 𝓘(ℝ, X × F) (X × Z) (X × F) ∞,
      K ×ˢ {(0 : Z)} ⊆ Φ.source ∧
        Φ.source ⊆ Prod.fst ⁻¹' U ∧ (Φ : X × Z → X × F) = shearedMap A T := by
  have hzeroInj : Set.InjOn (shearedMap A T) (K ×ˢ {(0 : Z)}) := by
    rintro ⟨x, z⟩ ⟨hx, hz⟩ ⟨y, w⟩ ⟨hy, hw⟩ heq
    have hz0 : z = 0 := hz
    have hw0 : w = 0 := hw
    subst z
    subst w
    rw [shearedMap_zero, shearedMap_zero] at heq
    exact Prod.ext (congrArg (fun q : X × F => q.1) heq) rfl
  have hlocal :
    ∀ p ∈ K ×ˢ {(0 : Z)}, IsLocalDiffeomorphAt 𝓘(ℝ, X × Z) 𝓘(ℝ, X × F) ∞ (shearedMap A T) p := by
    rintro ⟨x, z⟩ ⟨hx, hz⟩
    have hz0 : z = 0 := hz
    subst z
    apply
      Smale.isLocalDiffeomorphAt_of_contMDiffOn (D := X × Z) (E := X × F) (M := X × F)
        (hU.preimage continuous_fst) (show (x, (0 : Z)) ∈ Prod.fst ⁻¹' U from hKU hx)
        (contDiffOn_shearedMap hA hT).contMDiffOn
    rw [mfderiv_eq_fderiv,
      (hasFDerivAt_shearedMap_zero
          ((hA.contDiffAt (hU.mem_nhds (hKU hx))).differentiableAt (by simp))
          ((hT.contDiffAt (hU.mem_nhds (hKU hx))).differentiableAt (by simp))).fderiv]
    exact isInvertible_shearedBlock (A x) (T x) (hi x hx)
  exact
    Smale.exists_partialDiffeomorph_near_compact (hK.prod isCompact_singleton) hzeroInj hlocal
      (hU.preimage continuous_fst) (fun _ hp => hKU hp.1)

private def Degree.AxisCoordinates.tangentShear {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : (ℝ × V) →L[ℝ] (ℝ × V)) : V →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ V).comp (L.comp (ContinuousLinearMap.inr ℝ ℝ V))

end Mathoverflow1973

end
