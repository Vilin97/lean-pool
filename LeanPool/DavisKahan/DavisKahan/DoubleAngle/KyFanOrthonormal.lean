/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
import LeanPool.DavisKahan.DavisKahan.OperatorIdeal.ApproximationNumbers.Core

/-!
# The Ky Fan variational bound for approximation-number prefixes

The infinite-dimensional max–min counterpart of the finite rectangular Ky Fan
variational principle: for a bounded operator `K` between Hilbert spaces and
orthonormal families `u`, `v` of length `k`,

`re (∑ i, ⟪u i, K (v i)⟫) ≤ kyFanApproximationGauge k K`.

The finite principle (`re_sum_inner_map_le_kyFanSum`) requires both
spaces finite-dimensional.  The proof here compresses `K` to the spans of the
two families — a map between `k`-dimensional spaces — where the finite
principle and the finite bridge
`kyFanSum_eq_kyFanApproximationGauge` apply, and then transports
back along the ideal inequality `approximationSingularValue_comp_le`, using
that the orthogonal projection and the subspace inclusion are contractions.

This closes the max–min gap in the approximation-number layer; the natural
upstream home is `DavisKahan/OperatorIdeal/ApproximationNumbers/Core.lean`.
-/

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
/-- **Ky Fan variational bound for approximation numbers.**  For orthonormal
families `u : Fin k → F` and `v : Fin k → E`, the paired coefficient sum of a
bounded operator is controlled by the `k`-th approximation-number prefix. -/
theorem re_sum_inner_map_le_kyFanApproximationGauge
    (K : E →L[𝕜] F) {k : ℕ} {u : Fin k → F} {v : Fin k → E}
    (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v) :
    RCLike.re (∑ i, ⟪u i, K (v i)⟫_𝕜) ≤ kyFanApproximationGauge k K := by
  classical
  set L₁ : Submodule 𝕜 F := Submodule.span 𝕜 (Set.range u) with hL₁def
  set L₂ : Submodule 𝕜 E := Submodule.span 𝕜 (Set.range v) with hL₂def
  have : FiniteDimensional 𝕜 L₁ :=
    FiniteDimensional.span_of_finite 𝕜 (Set.finite_range u)
  have : FiniteDimensional 𝕜 L₂ :=
    FiniteDimensional.span_of_finite 𝕜 (Set.finite_range v)
  have : CompleteSpace L₁ := FiniteDimensional.complete 𝕜 L₁
  have : CompleteSpace L₂ := FiniteDimensional.complete 𝕜 L₂
  set K' : L₂ →L[𝕜] L₁ :=
    L₁.orthogonalProjectionOnto ∘L K ∘L L₂.subtypeL with hK'def
  -- the corestricted families
  have humem : ∀ i, u i ∈ L₁ := fun i =>
    Submodule.subset_span (Set.mem_range_self i)
  have hvmem : ∀ i, v i ∈ L₂ := fun i =>
    Submodule.subset_span (Set.mem_range_self i)
  set u' : Fin k → L₁ := fun i => ⟨u i, humem i⟩ with hu'def
  set v' : Fin k → L₂ := fun i => ⟨v i, hvmem i⟩ with hv'def
  have hu' : Orthonormal 𝕜 u' := by
    rw [orthonormal_iff_ite] at hu ⊢
    intro i j
    simpa [u', Submodule.coe_inner] using hu i j
  have hv' : Orthonormal 𝕜 v' := by
    rw [orthonormal_iff_ite] at hv ⊢
    intro i j
    simpa [v', Submodule.coe_inner] using hv i j
  have hkle : k ≤ finrank 𝕜 L₂ := by
    have h := finrank_span_eq_card hv.linearIndependent
    rw [← hL₂def] at h
    simp [h]
  -- the compressed pairing agrees with the ambient pairing
  have hpair : ∀ i, ⟪u' i, K' (v' i)⟫_𝕜 = ⟪u i, K (v i)⟫_𝕜 := by
    intro i
    have hval : ((K' (v' i) : L₁) : F) = L₁.starProjection (K (v i)) := rfl
    rw [Submodule.coe_inner, hval, ← L₁.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.mpr (humem i)]
  -- finite Ky Fan principle on the compression
  have hfin : RCLike.re (∑ i, ⟪u' i, K' (v' i)⟫_𝕜) ≤
      TauCeti.kyFanSum
        k K'.toLinearMap :=
    TauCeti.re_sum_inner_map_le_kyFanSum
      hkle hu' hv'
  -- finite bridge to the approximation-number prefix
  have hK'id : K'.toLinearMap.toContinuousLinearMap = K' := by
    ext x; rfl
  have hbridge :
      TauCeti.kyFanSum
        k K'.toLinearMap = kyFanApproximationGauge k K' := by
    rw [kyFanSum_eq_kyFanApproximationGauge, hK'id]
  -- the compression does not increase approximation numbers
  have hmono : kyFanApproximationGauge k K' ≤ kyFanApproximationGauge k K := by
    unfold kyFanApproximationGauge ContinuousLinearMap.kyFanGauge
    refine Finset.sum_le_sum fun n _ => ?_
    have hcomp := approximationSingularValue_comp_le n
      L₁.orthogonalProjectionOnto K L₂.subtypeL
    refine hcomp.trans ?_
    have h1 : ‖L₁.orthogonalProjectionOnto‖ ≤ 1 :=
      L₁.orthogonalProjectionOnto_norm_le
    have h2 : ‖L₂.subtypeL‖ ≤ 1 := L₂.norm_subtypeL_le
    have h0 := approximationSingularValue_nonneg n K
    calc ‖L₁.orthogonalProjectionOnto‖ * approximationSingularValue n K *
          ‖L₂.subtypeL‖
        ≤ 1 * approximationSingularValue n K * 1 := by
          refine mul_le_mul (mul_le_mul h1 le_rfl h0 zero_le_one) h2
            (norm_nonneg _) ?_
          positivity
      _ = approximationSingularValue n K := by ring
  calc RCLike.re (∑ i, ⟪u i, K (v i)⟫_𝕜)
      = RCLike.re (∑ i, ⟪u' i, K' (v' i)⟫_𝕜) := by
        congr 1
        exact Finset.sum_congr rfl fun i _ => (hpair i).symm
    _ ≤ TauCeti.kyFanSum
          k K'.toLinearMap := hfin
    _ = kyFanApproximationGauge k K' := hbridge
    _ ≤ kyFanApproximationGauge k K := hmono

omit [CompleteSpace E] [CompleteSpace F] in
/-- Witness form of the variational bound: pointwise lower bounds by paired
coefficients sum to at most the approximation-number prefix. -/
theorem sum_le_kyFanApproximationGauge_of_orthonormal
    (K : E →L[𝕜] F) {k : ℕ} {u : Fin k → F} {v : Fin k → E}
    (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v) {t : Fin k → ℝ}
    (ht : ∀ i, t i ≤ RCLike.re ⟪u i, K (v i)⟫_𝕜) :
    ∑ i, t i ≤ kyFanApproximationGauge k K := by
  refine le_trans ?_ (re_sum_inner_map_le_kyFanApproximationGauge K hu hv)
  rw [map_sum]
  exact Finset.sum_le_sum fun i _ => ht i

omit [CompleteSpace E] [CompleteSpace F] in
/-- Flipping the sign of individual members of an orthonormal family keeps it
orthonormal. -/
theorem orthonormal_signFlip {k : ℕ} {u : Fin k → F} (hu : Orthonormal 𝕜 u)
    (σ : Fin k → Bool) :
    Orthonormal 𝕜 (fun i => if σ i then u i else -u i) := by
  rw [orthonormal_iff_ite] at hu ⊢
  intro i j
  have key :
      ⟪(if σ i then u i else -u i), (if σ j then u j else -u j)⟫_𝕜 =
        (if σ i then (1 : 𝕜) else -1) *
          ((if σ j then (1 : 𝕜) else -1) * ⟪u i, u j⟫_𝕜) := by
    rcases hi : σ i with _ | _ <;> rcases hj : σ j with _ | _ <;>
      simp [inner_neg_left, inner_neg_right]
  rw [key, hu i j]
  rcases eq_or_ne i j with rfl | hne
  · rcases σ i with _ | _ <;> simp
  · simp [hne]

omit [CompleteSpace E] [CompleteSpace F] in
/-- **Magnitude form of the approximation-number Ky Fan variational bound.**
The paired coefficients may be replaced by their absolute values, because
rephasing each member of the left orthonormal family by the sign of its
coefficient keeps the family orthonormal.

This is the approximation-number counterpart of
`TauCeti.sum_abs_le_kyFanSum_of_orthonormal`,
and it is what a *branch-free* estimate consumes: the sign of the matched
coefficient is dictated by the configuration, not chosen in advance. -/
theorem sum_abs_le_kyFanApproximationGauge_of_orthonormal
    (K : E →L[𝕜] F) {k : ℕ} {u : Fin k → F} {v : Fin k → E}
    (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v) {t : Fin k → ℝ}
    (ht : ∀ i, t i ≤ |RCLike.re ⟪u i, K (v i)⟫_𝕜|) :
    ∑ i, t i ≤ kyFanApproximationGauge k K := by
  classical
  set σ : Fin k → Bool :=
    fun i => decide (0 ≤ RCLike.re ⟪u i, K (v i)⟫_𝕜) with hσ
  set u' : Fin k → F := fun i => if σ i then u i else -u i with hu'
  have habs : ∀ i, |RCLike.re ⟪u i, K (v i)⟫_𝕜| =
      RCLike.re ⟪u' i, K (v i)⟫_𝕜 := by
    intro i
    by_cases h : 0 ≤ RCLike.re ⟪u i, K (v i)⟫_𝕜
    · simp only [hu', hσ, decide_eq_true_eq, ite_eq_left h]
      exact abs_of_nonneg h
    · have hneg : σ i = false := by simp [hσ, h]
      rw [abs_of_neg (not_le.mp h)]
      simp [hu', hneg, inner_neg_left]
  refine sum_le_kyFanApproximationGauge_of_orthonormal K
    (orthonormal_signFlip hu σ) hv (t := t) ?_
  intro i
  exact (ht i).trans_eq (habs i)

/-!
## Relaxing orthonormality to a contraction bound

The variational bound above needs both families to be exactly orthonormal.  An
*approximate* double-angle eigenfamily produces families whose Gram matrices are
`1 + O(ε)` rather than `1`, and — for the third of them — whose defect is
controlled only in the positive-semidefinite order.  That is exactly a bound on
`‖∑ i, α i • u i‖`, so the right relaxation is a **contraction system**.
-/

omit [CompleteSpace F] in
/-- The squared length of a linear combination of an orthonormal family. -/
theorem norm_sq_sum_smul_of_orthonormal {k : ℕ} {u : Fin k → F}
    (hu : Orthonormal 𝕜 u) (α : Fin k → 𝕜) :
    ‖∑ i, α i • u i‖ ^ 2 = ∑ i, ‖α i‖ ^ 2 := by
  have h := hu.inner_sum α α Finset.univ
  have h3 := congrArg RCLike.re h
  rw [inner_self_eq_norm_sq_to_K] at h3
  simp only [map_sum, RCLike.conj_mul, ← RCLike.ofReal_pow,
    RCLike.ofReal_re] at h3
  exact h3

omit [CompleteSpace F] in
/-- An orthonormal family is a contraction system with any constant `1 ≤ c`. -/
theorem sq_norm_sum_smul_le_of_orthonormal {k : ℕ} {u : Fin k → F}
    (hu : Orthonormal 𝕜 u) {c : ℝ} (hc : 1 ≤ c) (α : Fin k → 𝕜) :
    ‖∑ i, α i • u i‖ ^ 2 ≤ c ^ 2 * ∑ i, ‖α i‖ ^ 2 := by
  rw [norm_sq_sum_smul_of_orthonormal hu]
  have hsum : (0 : ℝ) ≤ ∑ i, ‖α i‖ ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hc2 : (1 : ℝ) ≤ c ^ 2 := by nlinarith [hc]
  nlinarith [hsum, hc2]

/-- The bounded map `α ↦ ∑ i, α i • u i` on `EuclideanSpace 𝕜 (Fin k)` attached
to a finite family.  Its operator norm is the family's contraction constant. -/
noncomputable def familyCombination {k : ℕ} (u : Fin k → F) :
    EuclideanSpace 𝕜 (Fin k) →L[𝕜] F :=
  ∑ i, (EuclideanSpace.proj (𝕜 := 𝕜) i).smulRight (u i)

omit [CompleteSpace F] in
/-- `familyCombination` evaluates to the corresponding linear combination. -/
theorem familyCombination_apply {k : ℕ} (u : Fin k → F)
    (α : EuclideanSpace 𝕜 (Fin k)) :
    familyCombination u α = ∑ i, α i • u i := by
  simp [familyCombination]

omit [CompleteSpace F] in
/-- `familyCombination` sends the standard basis to the family. -/
theorem familyCombination_single {k : ℕ} (u : Fin k → F) (j : Fin k) :
    familyCombination u (EuclideanSpace.single j (1 : 𝕜)) = u j := by
  classical
  rw [familyCombination_apply]
  have h : ∀ i : Fin k, (EuclideanSpace.single j (1 : 𝕜)) i • u i =
      if i = j then u i else 0 := by
    intro i
    by_cases hij : i = j <;> simp [PiLp.single_apply, hij]
  rw [Finset.sum_congr rfl fun i _ => h i]
  simp

omit [CompleteSpace F] in
/-- A contraction system has family map of operator norm at most `c`. -/
theorem norm_familyCombination_le {k : ℕ} {u : Fin k → F} {c : ℝ} (hc : 0 ≤ c)
    (hu : ∀ α : Fin k → 𝕜, ‖∑ i, α i • u i‖ ^ 2 ≤ c ^ 2 * ∑ i, ‖α i‖ ^ 2) :
    ‖familyCombination (𝕜 := 𝕜) u‖ ≤ c := by
  refine ContinuousLinearMap.opNorm_le_bound _ hc fun α => ?_
  rw [familyCombination_apply]
  have hn : ‖α‖ ^ 2 = ∑ i, ‖α i‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  have h1 : ‖∑ i, α i • u i‖ ^ 2 ≤ (c * ‖α‖) ^ 2 := by
    rw [mul_pow, hn]
    exact hu α.ofLp
  have h2 : (0 : ℝ) ≤ c * ‖α‖ := mul_nonneg hc (norm_nonneg α)
  calc ‖∑ i, α i • u i‖ = √(‖∑ i, α i • u i‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ √((c * ‖α‖) ^ 2) := Real.sqrt_le_sqrt h1
    _ = c * ‖α‖ := Real.sqrt_sq h2

omit [CompleteSpace E] in
/-- **Contraction form of the Ky Fan variational bound.**

`re (∑ i, ⟪u i, K (v i)⟫) ≤ cu * cv * kyFanApproximationGauge k K` when the two
families are *contraction systems* rather than orthonormal: every linear
combination obeys `‖∑ i, α i • u i‖ ≤ cu ‖α‖`, and likewise for `v` with `cv`.
Orthonormality is the case `cu = cv = 1`, where the hypothesis holds with
equality.

The proof is the orthonormal one with the two span compressions replaced by the
family maps: `⟪u i, K (v i)⟫ = ⟪eᵢ, (M⋆ ∘ K ∘ N) eᵢ⟫` for the standard basis `e`
of `EuclideanSpace 𝕜 (Fin k)`, and the ideal inequality
`approximationSingularValue_comp_le` absorbs `‖M⋆‖ ≤ cu` and `‖N‖ ≤ cv`.  No
singular-value decomposition and no Abel summation are needed. -/
theorem re_sum_inner_map_le_kyFanApproximationGauge_of_contraction
    (K : E →L[𝕜] F) {k : ℕ} {u : Fin k → F} {v : Fin k → E} {cu cv : ℝ}
    (hcu : 0 ≤ cu) (hcv : 0 ≤ cv)
    (hu : ∀ α : Fin k → 𝕜, ‖∑ i, α i • u i‖ ^ 2 ≤ cu ^ 2 * ∑ i, ‖α i‖ ^ 2)
    (hv : ∀ α : Fin k → 𝕜, ‖∑ i, α i • v i‖ ^ 2 ≤ cv ^ 2 * ∑ i, ‖α i‖ ^ 2) :
    RCLike.re (∑ i, ⟪u i, K (v i)⟫_𝕜) ≤
      cu * cv * kyFanApproximationGauge k K := by
  classical
  set M : EuclideanSpace 𝕜 (Fin k) →L[𝕜] F := familyCombination u with hM
  set N : EuclideanSpace 𝕜 (Fin k) →L[𝕜] E := familyCombination v with hN
  set X : EuclideanSpace 𝕜 (Fin k) →L[𝕜] EuclideanSpace 𝕜 (Fin k) :=
    ContinuousLinearMap.adjoint M ∘L K ∘L N with hX
  have he : Orthonormal 𝕜 fun i : Fin k => EuclideanSpace.single i (1 : 𝕜) :=
    EuclideanSpace.orthonormal_single
  have hpair : ∀ i : Fin k,
      ⟪EuclideanSpace.single i (1 : 𝕜), X (EuclideanSpace.single i (1 : 𝕜))⟫_𝕜 =
        ⟪u i, K (v i)⟫_𝕜 := by
    intro i
    rw [hX]
    simp only [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.adjoint_inner_right, hM, hN,
      familyCombination_single, familyCombination_single]
  have hfin := re_sum_inner_map_le_kyFanApproximationGauge X he he
  have hMn : ‖ContinuousLinearMap.adjoint M‖ ≤ cu := by
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact norm_familyCombination_le hcu hu
  have hNn : ‖N‖ ≤ cv := norm_familyCombination_le hcv hv
  have hmono : kyFanApproximationGauge k X ≤
      cu * cv * kyFanApproximationGauge k K := by
    unfold kyFanApproximationGauge ContinuousLinearMap.kyFanGauge
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun n _ => ?_
    have hcomp := approximationSingularValue_comp_le n
      (ContinuousLinearMap.adjoint M) K N
    have h0 := approximationSingularValue_nonneg n K
    have s1 : ‖ContinuousLinearMap.adjoint M‖ * approximationSingularValue n K ≤
        cu * approximationSingularValue n K :=
      mul_le_mul_of_nonneg_right hMn h0
    have s2 : ‖ContinuousLinearMap.adjoint M‖ * approximationSingularValue n K *
        ‖N‖ ≤ cu * approximationSingularValue n K * ‖N‖ :=
      mul_le_mul_of_nonneg_right s1 (norm_nonneg N)
    have s3 : cu * approximationSingularValue n K * ‖N‖ ≤
        cu * approximationSingularValue n K * cv :=
      mul_le_mul_of_nonneg_left hNn (by positivity)
    have s4 : cu * approximationSingularValue n K * cv =
        cu * cv * approximationSingularValue n K := by ring
    exact hcomp.trans (le_trans s2 (s3.trans_eq s4))
  calc RCLike.re (∑ i, ⟪u i, K (v i)⟫_𝕜)
      = RCLike.re (∑ i, ⟪EuclideanSpace.single i (1 : 𝕜),
          X (EuclideanSpace.single i (1 : 𝕜))⟫_𝕜) := by
        congr 1
        exact Finset.sum_congr rfl fun i _ => (hpair i).symm
    _ ≤ kyFanApproximationGauge k X := hfin
    _ ≤ cu * cv * kyFanApproximationGauge k K := hmono

omit [CompleteSpace E] in
/-- Witness form of the contraction Ky Fan bound: pointwise lower bounds by
paired coefficients sum to at most `cu * cv` times the approximation-number
prefix. -/
theorem sum_le_kyFanApproximationGauge_of_contraction
    (K : E →L[𝕜] F) {k : ℕ} {u : Fin k → F} {v : Fin k → E} {cu cv : ℝ}
    (hcu : 0 ≤ cu) (hcv : 0 ≤ cv)
    (hu : ∀ α : Fin k → 𝕜, ‖∑ i, α i • u i‖ ^ 2 ≤ cu ^ 2 * ∑ i, ‖α i‖ ^ 2)
    (hv : ∀ α : Fin k → 𝕜, ‖∑ i, α i • v i‖ ^ 2 ≤ cv ^ 2 * ∑ i, ‖α i‖ ^ 2)
    {t : Fin k → ℝ} (ht : ∀ i, t i ≤ RCLike.re ⟪u i, K (v i)⟫_𝕜) :
    ∑ i, t i ≤ cu * cv * kyFanApproximationGauge k K := by
  refine le_trans ?_
    (re_sum_inner_map_le_kyFanApproximationGauge_of_contraction K hcu hcv hu hv)
  rw [map_sum]
  exact Finset.sum_le_sum fun i _ => ht i

end ExactSinTheta
end DavisKahan
end TauCeti
