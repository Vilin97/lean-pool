/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
module


public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Algebra.Star.Unitary
public import LeanPool.OperatorTheory.Operator.Dilation.Halmos

/-!
# The Schäffer unitary power dilation

This file proves the Schäffer dilation through a repeated-interaction model on
the bilateral Hilbert sum `ℓ²(ℤ, E ⊕₂ E)`.  A Halmos unitary acts independently
at every site, after which the environment output moves one site to the right.
The negative sites stay zero, so the system component at site zero evolves as
`Tⁿ`.  The boundary theorem packages this unitary, its isometric embedding, and
the resulting power-compression identity.
-/

@[expose] public section

open scoped ENNReal InnerProductSpace

universe u

noncomputable section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- The Hilbert sum used for the Schäffer dilation. -/
abbrev SchaefferSpace (E : Type u) [NormedAddCommGroup E] :=
  lp (fun _ : ℤ => E) 2

/-- Embed `E` isometrically as coordinate zero of its bilateral Hilbert sum. -/
noncomputable def schaefferEmbedding : E →L[ℂ] SchaefferSpace E :=
  lp.singleContinuousLinearMap ℂ (fun _ : ℤ => E) 2 0

omit [CompleteSpace E] in
@[simp]
theorem schaefferEmbedding_apply (x : E) :
    schaefferEmbedding x = lp.single 2 (0 : ℤ) x := rfl

omit [CompleteSpace E] in
/-- The coordinate-zero embedding preserves the inner product. -/
theorem inner_schaefferEmbedding (x y : E) :
    ⟪schaefferEmbedding x, schaefferEmbedding y⟫_ℂ = ⟪x, y⟫_ℂ := by
  simp only [schaefferEmbedding_apply, lp.inner_single_left, lp.single_apply_self]

/-- The adjoint of the coordinate-zero embedding extracts coordinate zero. -/
theorem adjoint_schaefferEmbedding_apply (f : SchaefferSpace E) :
    ContinuousLinearMap.adjoint (schaefferEmbedding : E →L[ℂ] SchaefferSpace E) f = f 0 := by
  refine ext_inner_right ℂ fun x => ?_
  rw [ContinuousLinearMap.adjoint_inner_left]
  simp only [schaefferEmbedding_apply, lp.inner_single_right]

/-- Reindex a square-summable family along an equivalence. -/
noncomputable def lpReindexForward {ι ι' : Type*} (e : ι ≃ ι')
    (f : lp (fun _ : ι => E) 2) : lp (fun _ : ι' => E) 2 :=
  ⟨fun j => f (e.symm j), by
    change Memℓp (fun j : ι' => f (e.symm j)) 2
    rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    exact e.symm.summable_iff.mpr
      ((lp.memℓp f).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal))⟩

omit [InnerProductSpace ℂ E] [CompleteSpace E] in
@[simp]
private theorem lpReindexForward_apply {ι ι' : Type*} (e : ι ≃ ι')
    (f : lp (fun _ : ι => E) 2) (j : ι') :
    lpReindexForward e f j = f (e.symm j) := rfl

omit [InnerProductSpace ℂ E] [CompleteSpace E] in
private theorem norm_lpReindexForward {ι ι' : Type*} (e : ι ≃ ι')
    (f : lp (fun _ : ι => E) 2) : ‖lpReindexForward e f‖ = ‖f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  calc
    ‖lpReindexForward e f‖ ^ 2 = ∑' j : ι', ‖f (e.symm j)‖ ^ (2 : ℕ) := by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two, lpReindexForward_apply] using
        lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞))
          (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (lpReindexForward e f)
    _ = ∑' i : ι, ‖f i‖ ^ (2 : ℕ) :=
      e.symm.tsum_eq (fun i : ι => ‖f i‖ ^ (2 : ℕ))
    _ = ‖f‖ ^ 2 := by
      symm
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
        lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞))
          (by norm_num : 0 < (2 : ℝ≥0∞).toReal) f

/-- Reindexing a square-summable family along an equivalence is a linear isometry equivalence. -/
noncomputable def lpReindex {ι ι' : Type*} (e : ι ≃ ι') :
    lp (fun _ : ι => E) 2 ≃ₗᵢ[ℂ] lp (fun _ : ι' => E) 2 where
  toFun := lpReindexForward e
  invFun := lpReindexForward e.symm
  left_inv f := by
    apply lp.ext
    funext i
    simp only [lpReindexForward_apply, Equiv.symm_symm, e.symm_apply_apply]
  right_inv f := by
    apply lp.ext
    funext i
    simp only [lpReindexForward_apply, Equiv.symm_symm, e.apply_symm_apply]
  map_add' _ _ := by
    apply lp.ext
    rfl
  map_smul' _ _ := by
    apply lp.ext
    rfl
  norm_map' := by exact norm_lpReindexForward e

/-- The right bilateral shift, as a linear isometry equivalence of the dilation space. -/
noncomputable def schaefferBilateralShiftEquiv :
    SchaefferSpace E ≃ₗᵢ[ℂ] SchaefferSpace E :=
  lpReindex (Equiv.addRight (1 : ℤ))

omit [CompleteSpace E] in
@[simp]
theorem schaefferBilateralShiftEquiv_apply (f : SchaefferSpace E) (j : ℤ) :
    schaefferBilateralShiftEquiv f j = f (j - 1) := rfl

/-- The bilateral shift as an element of the unitary group. -/
noncomputable def schaefferBilateralShiftUnitary :
    unitary (SchaefferSpace E →L[ℂ] SchaefferSpace E) :=
  Unitary.linearIsometryEquiv.symm schaefferBilateralShiftEquiv

/-- The right bilateral shift, bundled as a continuous linear map. -/
noncomputable def schaefferBilateralShift :
    SchaefferSpace E →L[ℂ] SchaefferSpace E :=
  schaefferBilateralShiftUnitary (E := E)

/-- The bilateral shift is unitary. -/
theorem schaefferBilateralShift_mem_unitary :
    schaefferBilateralShift (E := E) ∈
      unitary (SchaefferSpace E →L[ℂ] SchaefferSpace E) :=
  (schaefferBilateralShiftUnitary (E := E)).property

@[simp]
theorem schaefferBilateralShift_apply (f : SchaefferSpace E) (j : ℤ) :
    schaefferBilateralShift f j = f (j - 1) := by
  change schaefferBilateralShiftEquiv f j = f (j - 1)
  exact schaefferBilateralShiftEquiv_apply f j

/-- One site in the repeated-interaction model: a system and one environment copy. -/
abbrev SchaefferNetworkFiber (E : Type u) := WithLp 2 (E × E)

/-- The bilateral Hilbert sum of system-environment sites. -/
abbrev SchaefferNetworkSpace (E : Type u) [NormedAddCommGroup E] :=
  lp (fun _ : ℤ => SchaefferNetworkFiber E) 2

/-- Insert the system space into the system component of one network site. -/
noncomputable def schaefferFiberEmbedding :
    E →L[ℂ] SchaefferNetworkFiber E :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ E E).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℂ E E)

omit [CompleteSpace E] in
@[simp]
private theorem schaefferFiberEmbedding_apply (x : E) :
    schaefferFiberEmbedding x = WithLp.toLp 2 (x, 0) := rfl

/-- Embed the original space at the system component of site zero. -/
noncomputable def schaefferNetworkEmbedding :
    E →L[ℂ] SchaefferNetworkSpace E :=
  (lp.singleContinuousLinearMap ℂ (fun _ : ℤ => SchaefferNetworkFiber E) 2 0).comp
    schaefferFiberEmbedding

omit [CompleteSpace E] in
@[simp]
theorem schaefferNetworkEmbedding_apply (x : E) :
    schaefferNetworkEmbedding x = lp.single 2 (0 : ℤ) (WithLp.toLp 2 (x, 0)) := rfl

omit [CompleteSpace E] in
/-- The network embedding preserves inner products. -/
theorem inner_schaefferNetworkEmbedding (x y : E) :
    ⟪schaefferNetworkEmbedding x, schaefferNetworkEmbedding y⟫_ℂ = ⟪x, y⟫_ℂ := by
  simp only [schaefferNetworkEmbedding_apply, lp.inner_single_left,
    lp.single_apply_self, WithLp.prod_inner_apply, inner_zero_right, add_zero]

/-- The adjoint of the network embedding extracts the system component at site zero. -/
theorem adjoint_schaefferNetworkEmbedding_apply (f : SchaefferNetworkSpace E) :
    ContinuousLinearMap.adjoint
      (schaefferNetworkEmbedding : E →L[ℂ] SchaefferNetworkSpace E) f = (f 0).fst := by
  refine ext_inner_right ℂ fun x => ?_
  rw [ContinuousLinearMap.adjoint_inner_left]
  simp only [schaefferNetworkEmbedding_apply, lp.inner_single_right,
    WithLp.prod_inner_apply, inner_zero_right, add_zero]
  rfl

private def lpPointwiseForward
    (W : SchaefferNetworkFiber E ≃ₗᵢ[ℂ] SchaefferNetworkFiber E)
    (f : SchaefferNetworkSpace E) : SchaefferNetworkSpace E :=
  ⟨fun i => W (f i), by
    change Memℓp (fun i : ℤ => W (f i)) 2
    rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    simpa only [W.norm_map] using
      (lp.memℓp f).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)⟩

omit [CompleteSpace E] in
@[simp]
private theorem lpPointwiseForward_apply
    (W : SchaefferNetworkFiber E ≃ₗᵢ[ℂ] SchaefferNetworkFiber E)
    (f : SchaefferNetworkSpace E) (i : ℤ) :
    lpPointwiseForward W f i = W (f i) := rfl

omit [CompleteSpace E] in
private theorem norm_lpPointwiseForward
    (W : SchaefferNetworkFiber E ≃ₗᵢ[ℂ] SchaefferNetworkFiber E)
    (f : SchaefferNetworkSpace E) : ‖lpPointwiseForward W f‖ = ‖f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [show ‖lpPointwiseForward W f‖ ^ 2 =
      ∑' i : ℤ, ‖lpPointwiseForward W f i‖ ^ (2 : ℕ) by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞))
        (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (lpPointwiseForward W f)]
  rw [show ‖f‖ ^ 2 = ∑' i : ℤ, ‖f i‖ ^ (2 : ℕ) by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞))
        (by norm_num : 0 < (2 : ℝ≥0∞).toReal) f]
  simp only [lpPointwiseForward_apply, W.norm_map]

/-- Apply the same fiberwise unitary at every integer site. -/
private def lpPointwiseEquiv
    (W : SchaefferNetworkFiber E ≃ₗᵢ[ℂ] SchaefferNetworkFiber E) :
    SchaefferNetworkSpace E ≃ₗᵢ[ℂ] SchaefferNetworkSpace E where
  toFun := lpPointwiseForward W
  invFun := lpPointwiseForward W.symm
  left_inv f := by
    apply lp.ext
    funext i
    simp only [lpPointwiseForward_apply, W.symm_apply_apply]
  right_inv f := by
    apply lp.ext
    funext i
    simp only [lpPointwiseForward_apply, W.apply_symm_apply]
  map_add' _ _ := by
    apply lp.ext
    funext i
    simp only [lpPointwiseForward_apply, lp.coeFn_add, Pi.add_apply, map_add]
  map_smul' _ _ := by
    apply lp.ext
    funext i
    simp only [lpPointwiseForward_apply, lp.coeFn_smul, Pi.smul_apply, map_smul,
      RingHom.id_apply]
  norm_map' := norm_lpPointwiseForward W

/-- Lift a two-coordinate unitary to the pointwise unitary on the network space. -/
private def schaefferPointwiseUnitary
    (J : unitary (SchaefferNetworkFiber E →L[ℂ] SchaefferNetworkFiber E)) :
    unitary (SchaefferNetworkSpace E →L[ℂ] SchaefferNetworkSpace E) :=
  Unitary.linearIsometryEquiv.symm
    (lpPointwiseEquiv (Unitary.linearIsometryEquiv J))

omit [CompleteSpace E] in
omit [InnerProductSpace ℂ E] in
private theorem summable_network_fst_sq (f : SchaefferNetworkSpace E) :
    Summable fun i : ℤ => ‖(f i).fst‖ ^ (2 : ℕ) := by
  have hf : Summable fun i : ℤ => ‖f i‖ ^ (2 : ℕ) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (lp.memℓp f).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  refine hf.of_nonneg_of_le (fun _ => sq_nonneg _) (fun i => ?_)
  have h := WithLp.prod_norm_sq_eq_of_L2 (f i)
  nlinarith only [h, sq_nonneg ‖(f i).snd‖]

omit [CompleteSpace E] in
omit [InnerProductSpace ℂ E] in
private theorem summable_network_snd_sq (f : SchaefferNetworkSpace E) :
    Summable fun i : ℤ => ‖(f i).snd‖ ^ (2 : ℕ) := by
  have hf : Summable fun i : ℤ => ‖f i‖ ^ (2 : ℕ) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (lp.memℓp f).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  refine hf.of_nonneg_of_le (fun _ => sq_nonneg _) (fun i => ?_)
  have h := WithLp.prod_norm_sq_eq_of_L2 (f i)
  nlinarith only [h, sq_nonneg ‖(f i).fst‖]

private def schaefferIntShift : ℤ ≃ ℤ := Equiv.addRight (1 : ℤ)

private def schaefferRouteForward (f : SchaefferNetworkSpace E) :
    SchaefferNetworkSpace E :=
  ⟨fun i => WithLp.toLp 2 ((f i).fst, (f (schaefferIntShift.symm i)).snd), by
    change Memℓp
      (fun i : ℤ => WithLp.toLp 2
        ((f i).fst, (f (schaefferIntShift.symm i)).snd)) 2
    rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    have hs : Summable fun i : ℤ =>
        ‖(f (schaefferIntShift.symm i)).snd‖ ^ (2 : ℕ) :=
      schaefferIntShift.symm.summable_iff.mpr (summable_network_snd_sq f)
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two,
      WithLp.prod_norm_sq_eq_of_L2, WithLp.toLp_fst, WithLp.toLp_snd] using
      (summable_network_fst_sq f).add hs⟩

omit [CompleteSpace E] in
omit [InnerProductSpace ℂ E] in
@[simp]
private theorem schaefferRouteForward_apply (f : SchaefferNetworkSpace E) (i : ℤ) :
    schaefferRouteForward f i =
      WithLp.toLp 2 ((f i).fst, (f (schaefferIntShift.symm i)).snd) := rfl

private def schaefferRouteBackward (f : SchaefferNetworkSpace E) :
    SchaefferNetworkSpace E :=
  ⟨fun i => WithLp.toLp 2 ((f i).fst, (f (schaefferIntShift i)).snd), by
    change Memℓp
      (fun i : ℤ => WithLp.toLp 2 ((f i).fst, (f (schaefferIntShift i)).snd)) 2
    rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    have hs : Summable fun i : ℤ => ‖(f (schaefferIntShift i)).snd‖ ^ (2 : ℕ) :=
      schaefferIntShift.summable_iff.mpr (summable_network_snd_sq f)
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two,
      WithLp.prod_norm_sq_eq_of_L2, WithLp.toLp_fst, WithLp.toLp_snd] using
      (summable_network_fst_sq f).add hs⟩

omit [CompleteSpace E] in
omit [InnerProductSpace ℂ E] in
@[simp]
private theorem schaefferRouteBackward_apply (f : SchaefferNetworkSpace E) (i : ℤ) :
    schaefferRouteBackward f i =
      WithLp.toLp 2 ((f i).fst, (f (schaefferIntShift i)).snd) := rfl

omit [CompleteSpace E] in
omit [InnerProductSpace ℂ E] in
private theorem norm_schaefferRouteForward (f : SchaefferNetworkSpace E) :
    ‖schaefferRouteForward f‖ = ‖f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have ha := summable_network_fst_sq f
  have hb := summable_network_snd_sq f
  have hbShift : Summable fun i : ℤ =>
      ‖(f (schaefferIntShift.symm i)).snd‖ ^ (2 : ℕ) :=
    schaefferIntShift.symm.summable_iff.mpr hb
  calc
    ‖schaefferRouteForward f‖ ^ 2 =
        ∑' i : ℤ, (‖(f i).fst‖ ^ (2 : ℕ) +
          ‖(f (schaefferIntShift.symm i)).snd‖ ^ (2 : ℕ)) := by
      rw [show ‖schaefferRouteForward f‖ ^ 2 =
          ∑' i : ℤ, ‖schaefferRouteForward f i‖ ^ (2 : ℕ) by
        simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
          lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞))
            (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (schaefferRouteForward f)]
      simp only [schaefferRouteForward_apply, WithLp.prod_norm_sq_eq_of_L2,
        WithLp.toLp_fst, WithLp.toLp_snd]
    _ = (∑' i : ℤ, ‖(f i).fst‖ ^ (2 : ℕ)) +
        ∑' i : ℤ, ‖(f (schaefferIntShift.symm i)).snd‖ ^ (2 : ℕ) :=
      ha.tsum_add hbShift
    _ = (∑' i : ℤ, ‖(f i).fst‖ ^ (2 : ℕ)) +
        ∑' i : ℤ, ‖(f i).snd‖ ^ (2 : ℕ) := by
      rw [schaefferIntShift.symm.tsum_eq
        (fun i : ℤ => ‖(f i).snd‖ ^ (2 : ℕ))]
    _ = ∑' i : ℤ, (‖(f i).fst‖ ^ (2 : ℕ) + ‖(f i).snd‖ ^ (2 : ℕ)) :=
      (ha.tsum_add hb).symm
    _ = ‖f‖ ^ 2 := by
      rw [show ‖f‖ ^ 2 = ∑' i : ℤ, ‖f i‖ ^ (2 : ℕ) by
        simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
          lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞))
            (by norm_num : 0 < (2 : ℝ≥0∞).toReal) f]
      simp only [WithLp.prod_norm_sq_eq_of_L2]

/-- Keep each system component fixed and shift each environment component one site right. -/
private def schaefferRouteEquiv :
    SchaefferNetworkSpace E ≃ₗᵢ[ℂ] SchaefferNetworkSpace E where
  toFun := schaefferRouteForward
  invFun := schaefferRouteBackward
  left_inv f := by
    apply lp.ext
    funext i
    apply WithLp.ofLp_injective
    simp only [schaefferRouteBackward_apply, schaefferRouteForward_apply,
      WithLp.toLp_fst, WithLp.toLp_snd, WithLp.ofLp_toLp,
      schaefferIntShift.symm_apply_apply]
    exact Prod.eta _
  right_inv f := by
    apply lp.ext
    funext i
    apply WithLp.ofLp_injective
    simp only [schaefferRouteBackward_apply, schaefferRouteForward_apply,
      WithLp.toLp_fst, WithLp.toLp_snd, WithLp.ofLp_toLp,
      schaefferIntShift.apply_symm_apply]
    exact Prod.eta _
  map_add' _ _ := by
    apply lp.ext
    funext i
    apply WithLp.ofLp_injective
    apply Prod.ext <;> rfl
  map_smul' _ _ := by
    apply lp.ext
    funext i
    apply WithLp.ofLp_injective
    apply Prod.ext <;> rfl
  norm_map' := norm_schaefferRouteForward

private def schaefferRouteUnitary :
    unitary (SchaefferNetworkSpace E →L[ℂ] SchaefferNetworkSpace E) :=
  Unitary.linearIsometryEquiv.symm schaefferRouteEquiv

/-- Apply the same Halmos interaction at every site, then move each environment output
one site to the right. -/
private def schaefferGlobalUnitary
    (J : unitary (SchaefferNetworkFiber E →L[ℂ] SchaefferNetworkFiber E)) :
    unitary (SchaefferNetworkSpace E →L[ℂ] SchaefferNetworkSpace E) :=
  schaefferRouteUnitary * schaefferPointwiseUnitary J

private noncomputable def schaefferGlobalOperator
    (J : unitary (SchaefferNetworkFiber E →L[ℂ] SchaefferNetworkFiber E)) :
    SchaefferNetworkSpace E →L[ℂ] SchaefferNetworkSpace E :=
  schaefferGlobalUnitary J

private theorem schaefferGlobalOperator_mem_unitary
    (J : unitary (SchaefferNetworkFiber E →L[ℂ] SchaefferNetworkFiber E)) :
    schaefferGlobalOperator J ∈
      unitary (SchaefferNetworkSpace E →L[ℂ] SchaefferNetworkSpace E) :=
  (schaefferGlobalUnitary J).property

@[simp]
private theorem schaefferGlobalOperator_apply
    (J : unitary (SchaefferNetworkFiber E →L[ℂ] SchaefferNetworkFiber E))
    (f : SchaefferNetworkSpace E) (i : ℤ) :
    schaefferGlobalOperator J f i = WithLp.toLp 2
      (((J : SchaefferNetworkFiber E →L[ℂ] SchaefferNetworkFiber E) (f i)).fst,
        ((J : SchaefferNetworkFiber E →L[ℂ] SchaefferNetworkFiber E)
          (f (schaefferIntShift.symm i))).snd) := by
  change schaefferRouteEquiv
    (lpPointwiseEquiv (Unitary.linearIsometryEquiv J) f) i = _
  rfl

private noncomputable def schaefferOrbit
    (J : unitary (SchaefferNetworkFiber E →L[ℂ] SchaefferNetworkFiber E))
    (n : ℕ) (x : E) : SchaefferNetworkSpace E :=
  (schaefferGlobalOperator J ^ n) (schaefferNetworkEmbedding x)

@[simp]
private theorem schaefferOrbit_succ_apply
    (J : unitary (SchaefferNetworkFiber E →L[ℂ] SchaefferNetworkFiber E))
    (n : ℕ) (x : E) (i : ℤ) :
    schaefferOrbit J (n + 1) x i = WithLp.toLp 2
      (((J : SchaefferNetworkFiber E →L[ℂ] SchaefferNetworkFiber E)
        (schaefferOrbit J n x i)).fst,
       ((J : SchaefferNetworkFiber E →L[ℂ] SchaefferNetworkFiber E)
        (schaefferOrbit J n x (schaefferIntShift.symm i))).snd) := by
  rw [schaefferOrbit, pow_succ']
  exact schaefferGlobalOperator_apply J _ i

private theorem schaeffer_power_state
    (T : E →L[ℂ] E)
    (J : unitary (SchaefferNetworkFiber E →L[ℂ] SchaefferNetworkFiber E))
    (hJ : ∀ z : E,
      ((J : SchaefferNetworkFiber E →L[ℂ] SchaefferNetworkFiber E)
        (WithLp.toLp 2 (z, 0))).fst = T z)
    (n : ℕ) (x : E) :
    (schaefferOrbit J n x 0).fst = (T ^ n) x ∧
    (schaefferOrbit J n x 0).snd = 0 ∧
    ∀ i : ℤ, i < 0 → schaefferOrbit J n x i = 0 := by
  induction n with
  | zero =>
      refine ⟨?_, ?_, ?_⟩
      · simp only [schaefferOrbit, pow_zero, one_apply_eq_self,
          schaefferNetworkEmbedding_apply, lp.single_apply_self,
          WithLp.toLp_fst]
      · simp only [schaefferOrbit, pow_zero, one_apply_eq_self,
          schaefferNetworkEmbedding_apply, lp.single_apply_self,
          WithLp.toLp_snd]
      intro i hi
      simp only [schaefferOrbit, pow_zero, one_apply_eq_self,
        schaefferNetworkEmbedding_apply]
      rw [lp.single_apply_ne]
      exact ne_of_lt hi
  | succ n ih =>
      rcases ih with ⟨ihfst, ihsnd, ihneg⟩
      have hzero : schaefferOrbit J n x 0 = WithLp.toLp 2 ((T ^ n) x, 0) := by
        apply WithLp.ofLp_injective
        exact Prod.ext ihfst ihsnd
      refine ⟨?_, ?_, ?_⟩
      · rw [schaefferOrbit_succ_apply, WithLp.toLp_fst, hzero, hJ,
          pow_succ', mul_apply_eq_comp]
      · rw [schaefferOrbit_succ_apply, WithLp.toLp_snd]
        have hm1 : schaefferIntShift.symm (0 : ℤ) = -1 := rfl
        rw [hm1, ihneg (-1) (by omega), map_zero]
        rfl
      · intro i hi
        rw [schaefferOrbit_succ_apply]
        have hprev : schaefferIntShift.symm i < 0 := by
          change i - 1 < 0
          omega
        rw [ihneg i hi, ihneg _ hprev, map_zero]
        rfl

/-- Every contraction has a unitary power dilation on a larger Hilbert space. -/
theorem exists_unitary_power_dilation (T : E →L[ℂ] E) (hT : ‖T‖ ≤ 1) :
    ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H)
      (V : E →L[ℂ] H) (U : H →L[ℂ] H),
    (∀ x y : E, ⟪V x, V y⟫_ℂ = ⟪x, y⟫_ℂ) ∧
    U ∈ unitary (H →L[ℂ] H) ∧
    (∀ (n : ℕ) (x : E),
      ContinuousLinearMap.adjoint V ((U ^ n) (V x)) = (T ^ n) x) := by
  obtain ⟨J, hJunitary, hJcompression⟩ := exists_halmos_unitary_dilation T hT
  let JU : unitary (SchaefferNetworkFiber E →L[ℂ] SchaefferNetworkFiber E) :=
    ⟨J, hJunitary⟩
  have hJU : ∀ z : E,
      ((JU : SchaefferNetworkFiber E →L[ℂ] SchaefferNetworkFiber E)
        (WithLp.toLp 2 (z, 0))).fst = T z := hJcompression
  refine ⟨SchaefferNetworkSpace E, inferInstance, inferInstance, inferInstance,
    schaefferNetworkEmbedding, schaefferGlobalOperator JU, ?_, ?_, ?_⟩
  · exact inner_schaefferNetworkEmbedding
  · exact schaefferGlobalOperator_mem_unitary JU
  · intro n x
    rw [adjoint_schaefferNetworkEmbedding_apply]
    change (schaefferOrbit JU n x 0).fst = (T ^ n) x
    exact (schaeffer_power_state T JU hJU n x).1

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
