/-
Copyright (c) 2026 Jon Crall, Edward Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Edward Wang
-/

/-
Staged for Mathlib: additions to `Mathlib/Analysis/InnerProductSpace/` (new file
`RotationBound.lean`).

Davis Result B: the sharper total-rotation estimate (Davis 1963, Theorem 3.2, eq. 3.1) and its
corollary combining with Result A (Theorem 4.1). Tickets PD-18 + BL1/BL2/BL4/BL5/BL6.
-/

import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.IntertwiningUnitary
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.EigenvalueChange
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Spectrum

/-! # Davis's sharper total-rotation estimate (Davis 1963, Theorem 3.2)

For self-adjoint `T, S` on a finite-dimensional inner product space with `H = S − T`, eigenbases
`xᵢ` (of `T`) and `vᵢ` (of `S`), eigenvalues `λᵢ`, `λ'ᵢ`, Davis's Theorem 3.2 bounds the total
rotation of the spectral resolution by the perturbation minus the eigenvalue displacement:
under the separation `γ'² + (λᵢ − λ'ᵢ)² ≤ (λᵢ − λ'ⱼ)²` (all `i ≠ j`),

`γ'² ∑ᵢ sin²θᵢ + ∑ᵢ (λᵢ − λ'ᵢ)² ≤ ‖H‖²_F`,   `sin²θᵢ = 1 − ‖⟪vᵢ, xᵢ⟫‖²`.

The proof is the two-sided evaluation of `⟨(S − λᵢ)² xᵢ, xᵢ⟩`: computing (`(S − λᵢ) xᵢ = H xᵢ`,
BL1) gives the row Frobenius norm; expanding in the `S`-eigenbasis and using the separation (BL2)
gives the rotation-plus-displacement lower bound; summing over `i` is eq. 3.1 (BL5).

The angles are identified with the canonical intertwining unitary of the two rank-one spectral
families (`OrthoProjFamily.sqSinAngle`, BL4/PD-18), and combining with Result A
(`sum_sq_eigenvalues_sub_ge`, Theorem 4.1) yields the payoff (BL6):

`γ'² ∑ᵢ sin²θᵢ ≤ 2 ‖𝒞⊥H‖²_F` —

eigenvector rotation is controlled by the *off-diagonal* part of the perturbation alone.

## Main results

* `TauCeti.rotation_add_displacement_le_hilbertSchmidt` — Theorem 3.2, eq. 3.1 (overlap form).
* `TauCeti.sqSinAngle_ofOrthonormalBasis` — `sin²θᵢ = 1 − ‖⟪vᵢ, xᵢ⟫‖²` for the canonical
  unitary of the rank-one spectral families (BL4).
* `TauCeti.rotation_add_displacement_le_hilbertSchmidt_intertwining` — Theorem 3.2 stated
  through the canonical intertwining unitary (PD-18 milestone).
* `TauCeti.rotation_le_two_mul_offDiag` — the corollary `(γ')² ∑ sin²θᵢ ≤ 2 ‖𝒞⊥H‖²_F` (BL6).

## References

* Chandler Davis, *The rotation of eigenvectors by a perturbation*, J. Math. Anal. Appl.
  6 (1963), 159–173, Theorem 3.2 and §5.
-/

namespace TauCeti
open scoped InnerProductSpace
open LinearMap InnerProductSpace Module

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} {T S : E →ₗ[𝕜] E}

/-! ### Theorem 3.2, eq. 3.1 — overlap form (BL1 + BL2 + BL5) -/

/-- **Davis's sharper total-rotation estimate** (Davis 1963, Theorem 3.2, eq. 3.1), overlap form.
If the hybrid separation `γ'² + (λᵢ − λ'ᵢ)² ≤ (λᵢ − λ'ⱼ)²` holds for all `i ≠ j` — Davis's
`(γ')² = minᵢ {γᵢ² − (λᵢ − λ'ᵢ)²}` with `γᵢ = min_{j≠i} |λᵢ − λ'ⱼ|` — then

`γ'² ∑ᵢ (1 − ‖⟪vᵢ, xᵢ⟫‖²) + ∑ᵢ (λᵢ − λ'ᵢ)² ≤ ∑ᵢ ‖(S − T) xᵢ‖² = ‖S − T‖²_F`. -/
theorem rotation_add_displacement_le_hilbertSchmidt
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n) {γ' : ℝ}
    (hsep : ∀ i j, i ≠ j →
      γ' ^ 2 + (hT.eigenvalues hn i - hS.eigenvalues hn i) ^ 2
        ≤ (hT.eigenvalues hn i - hS.eigenvalues hn j) ^ 2) :
    γ' ^ 2 * ∑ i, (1 - ‖⟪hS.eigenvectorBasis hn i, hT.eigenvectorBasis hn i⟫_𝕜‖ ^ 2)
        + ∑ i, (hT.eigenvalues hn i - hS.eigenvalues hn i) ^ 2
      ≤ ∑ i, ‖(S - T) (hT.eigenvectorBasis hn i)‖ ^ 2 := by
  have key : ∀ i : Fin n,
      γ' ^ 2 * (1 - ‖⟪hS.eigenvectorBasis hn i, hT.eigenvectorBasis hn i⟫_𝕜‖ ^ 2)
          + (hT.eigenvalues hn i - hS.eigenvalues hn i) ^ 2
        ≤ ‖(S - T) (hT.eigenvectorBasis hn i)‖ ^ 2 := by
    intro i
    -- BL1: each Fourier coefficient of `(S − T) xᵢ` in the `S`-eigenbasis is an eigenvalue
    -- difference times an overlap
    have hcross : ∀ j, ‖⟪hS.eigenvectorBasis hn j, (S - T) (hT.eigenvectorBasis hn i)⟫_𝕜‖ ^ 2
        = (hT.eigenvalues hn i - hS.eigenvalues hn j) ^ 2
            * ‖⟪hS.eigenvectorBasis hn j, hT.eigenvectorBasis hn i⟫_𝕜‖ ^ 2 := fun j => by
      have h := inner_eigenvectorBasis_map_sub_eigenvectorBasis hS hT hn j i
      have h2 : ⟪hS.eigenvectorBasis hn j, (S - T) (hT.eigenvectorBasis hn i)⟫_𝕜
          = -(((hT.eigenvalues hn i - hS.eigenvalues hn j : ℝ) : 𝕜)
              * ⟪hS.eigenvectorBasis hn j, hT.eigenvectorBasis hn i⟫_𝕜) := by
        rw [← h, ← inner_neg_right]
        congr 1
        simp [LinearMap.sub_apply]
      rw [h2, norm_neg, norm_mul, mul_pow, RCLike.norm_ofReal, sq_abs]
    -- Parseval: the overlaps sum to `‖xᵢ‖² = 1`
    have hparse : ∑ j, ‖⟪hS.eigenvectorBasis hn j, hT.eigenvectorBasis hn i⟫_𝕜‖ ^ 2 = 1 := by
      rw [(hS.eigenvectorBasis hn).sum_sq_norm_inner_right (hT.eigenvectorBasis hn i),
        (hT.eigenvectorBasis hn).orthonormal.1 i, one_pow]
    have hsplit := Finset.add_sum_erase Finset.univ
      (fun j => ‖⟪hS.eigenvectorBasis hn j, hT.eigenvectorBasis hn i⟫_𝕜‖ ^ 2)
      (Finset.mem_univ i)
    -- BL2: the separation turns the off-`i` mass into the rotation term
    calc γ' ^ 2 * (1 - ‖⟪hS.eigenvectorBasis hn i, hT.eigenvectorBasis hn i⟫_𝕜‖ ^ 2)
          + (hT.eigenvalues hn i - hS.eigenvalues hn i) ^ 2
        = (hT.eigenvalues hn i - hS.eigenvalues hn i) ^ 2
              * ‖⟪hS.eigenvectorBasis hn i, hT.eigenvectorBasis hn i⟫_𝕜‖ ^ 2
            + (γ' ^ 2 + (hT.eigenvalues hn i - hS.eigenvalues hn i) ^ 2)
              * (1 - ‖⟪hS.eigenvectorBasis hn i, hT.eigenvectorBasis hn i⟫_𝕜‖ ^ 2) := by
          ring
      _ ≤ (hT.eigenvalues hn i - hS.eigenvalues hn i) ^ 2
              * ‖⟪hS.eigenvectorBasis hn i, hT.eigenvectorBasis hn i⟫_𝕜‖ ^ 2
            + ∑ j ∈ Finset.univ.erase i, (hT.eigenvalues hn i - hS.eigenvalues hn j) ^ 2
              * ‖⟪hS.eigenvectorBasis hn j, hT.eigenvectorBasis hn i⟫_𝕜‖ ^ 2 := by
          have h1 : (γ' ^ 2 + (hT.eigenvalues hn i - hS.eigenvalues hn i) ^ 2)
              * (1 - ‖⟪hS.eigenvectorBasis hn i, hT.eigenvectorBasis hn i⟫_𝕜‖ ^ 2)
              = ∑ j ∈ Finset.univ.erase i,
                  (γ' ^ 2 + (hT.eigenvalues hn i - hS.eigenvalues hn i) ^ 2)
                    * ‖⟪hS.eigenvectorBasis hn j, hT.eigenvectorBasis hn i⟫_𝕜‖ ^ 2 := by
            rw [← Finset.mul_sum]
            congr 1
            linarith [hsplit, hparse]
          rw [h1]
          refine add_le_add le_rfl (Finset.sum_le_sum fun j hj => ?_)
          exact mul_le_mul_of_nonneg_right
            (hsep i j (Finset.ne_of_mem_erase hj).symm) (sq_nonneg _)
      _ = ∑ j, (hT.eigenvalues hn i - hS.eigenvalues hn j) ^ 2
            * ‖⟪hS.eigenvectorBasis hn j, hT.eigenvectorBasis hn i⟫_𝕜‖ ^ 2 :=
          Finset.add_sum_erase Finset.univ
            (fun j => (hT.eigenvalues hn i - hS.eigenvalues hn j) ^ 2
              * ‖⟪hS.eigenvectorBasis hn j, hT.eigenvectorBasis hn i⟫_𝕜‖ ^ 2)
            (Finset.mem_univ i)
      _ = ∑ j, ‖⟪hS.eigenvectorBasis hn j, (S - T) (hT.eigenvectorBasis hn i)⟫_𝕜‖ ^ 2 :=
          Finset.sum_congr rfl fun j _ => (hcross j).symm
      _ = ‖(S - T) (hT.eigenvectorBasis hn i)‖ ^ 2 :=
          (hS.eigenvectorBasis hn).sum_sq_norm_inner_right _
  calc γ' ^ 2 * ∑ i, (1 - ‖⟪hS.eigenvectorBasis hn i, hT.eigenvectorBasis hn i⟫_𝕜‖ ^ 2)
        + ∑ i, (hT.eigenvalues hn i - hS.eigenvalues hn i) ^ 2
      = ∑ i, (γ' ^ 2 * (1 - ‖⟪hS.eigenvectorBasis hn i, hT.eigenvectorBasis hn i⟫_𝕜‖ ^ 2)
          + (hT.eigenvalues hn i - hS.eigenvalues hn i) ^ 2) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    _ ≤ ∑ i, ‖(S - T) (hT.eigenvectorBasis hn i)‖ ^ 2 := Finset.sum_le_sum fun i _ => key i

/-! ### The canonical unitary of two rank-one spectral families (BL4 / PD-18) -/

/-- If each `b'`-vector overlaps its matching `b`-vector, the rank-one spectral families of the
two orthonormal bases satisfy Davis's non-degeneracy hypothesis. -/
theorem nonDegenerate_ofOrthonormalBasis {b b' : OrthonormalBasis (Fin n) 𝕜 E}
    (h : ∀ i, ⟪b' i, b i⟫_𝕜 ≠ 0) :
    (OrthoProjFamily.ofOrthonormalBasis b).NonDegenerate
      (OrthoProjFamily.ofOrthonormalBasis b') := by
  intro j z hz hz0 hcontra
  simp only [OrthoProjFamily.ofOrthonormalBasis_proj,
      OrthonormalBasis.spanIndicesProjection_singleton_apply]
    at hz hcontra
  rcases smul_eq_zero.mp hcontra with hc | hb
  · have hzc : ⟪b j, z⟫_𝕜 ≠ 0 := fun h0 => hz0 (by rw [← hz, h0, zero_smul])
    have hexp : ⟪b' j, z⟫_𝕜 = ⟪b j, z⟫_𝕜 * ⟪b' j, b j⟫_𝕜 := by
      conv_lhs => rw [← hz]
      rw [inner_smul_right]
    rw [hexp] at hc
    exact mul_ne_zero hzc (h j) hc
  · have h1 : ‖b' j‖ = 1 := b'.orthonormal.1 j
    rw [hb, norm_zero] at h1
    exact zero_ne_one h1

/-- The canonical intertwining unitary of the rank-one spectral families rotates `b i` onto the
`b' i` axis: `U (b i) = (⟪b' i, b i⟫ / ‖⟪b' i, b i⟫‖) • b' i` — the polar phase of the overlap.
Davis §2 (the polar factor of `P'ᵢ Pᵢ` on a one-dimensional block). -/
theorem intertwiningUnitary_apply_ofOrthonormalBasis {b b' : OrthonormalBasis (Fin n) 𝕜 E}
    (h : ∀ i, ⟪b' i, b i⟫_𝕜 ≠ 0) (i : Fin n) :
    OrthoProjFamily.intertwiningUnitary (nonDegenerate_ofOrthonormalBasis h) (b i)
      = (((‖⟪b' i, b i⟫_𝕜‖⁻¹ : ℝ) : 𝕜) * ⟪b' i, b i⟫_𝕜) • b' i := by
  have hcnorm : ‖⟪b' i, b i⟫_𝕜‖ ≠ 0 := norm_ne_zero_iff.mpr (h i)
  have hPb : OrthonormalBasis.spanIndicesProjection b {i} (b i) = b i := by
    rw [OrthonormalBasis.spanIndicesProjection_apply_basis]
    simp
  have hP'b' : OrthonormalBasis.spanIndicesProjection b' {i} (b' i) = b' i := by
    rw [OrthonormalBasis.spanIndicesProjection_apply_basis]
    simp
  have hMb : (OrthonormalBasis.spanIndicesProjection b' {i} ∘ₗ
        OrthonormalBasis.spanIndicesProjection b {i}) (b i)
      = ⟪b' i, b i⟫_𝕜 • b' i := by
    rw [LinearMap.comp_apply, hPb, OrthonormalBasis.spanIndicesProjection_singleton_apply]
  -- `|Mᵢ|` acts on `b i` as multiplication by the overlap size `‖c‖`
  have habs : operatorAbs (OrthonormalBasis.spanIndicesProjection b' {i} ∘ₗ
        OrthonormalBasis.spanIndicesProjection b {i}) (b i)
      = ((‖⟪b' i, b i⟫_𝕜‖ : ℝ) : 𝕜) • b i := by
    refine (isPositive_operatorAbs _).apply_eq_smul_of_apply_apply_eq_smul (norm_nonneg _) ?_
    have h2 := congrArg (fun f : E →ₗ[𝕜] E => f (b i))
      (operatorAbs_mul_self (OrthonormalBasis.spanIndicesProjection b' {i} ∘ₗ
            OrthonormalBasis.spanIndicesProjection b {i}))
    simp only [LinearMap.comp_apply] at h2
    rw [h2, LinearMap.adjoint_comp,
      (OrthonormalBasis.isPositive_spanIndicesProjection b {i}).adjoint_eq,
      (OrthonormalBasis.isPositive_spanIndicesProjection b' {i}).adjoint_eq]
    -- Pᵢ (P'ᵢ (P'ᵢ (Pᵢ (b i)))) = (c * conj c) • b i = ‖c‖² • b i
    simp only [hPb, OrthonormalBasis.spanIndicesProjection_singleton_apply, LinearMap.comp_apply, map_smul,
        hP'b',
      map_smul, OrthonormalBasis.spanIndicesProjection_singleton_apply, smul_smul,
      ← inner_conj_symm (b i) (b' i), RCLike.mul_conj, pow_two]
  -- collapse the intertwining unitary's sum to the `i`-th block polar factor
  rw [OrthoProjFamily.intertwiningUnitary_apply]
  simp only [OrthoProjFamily.ofOrthonormalBasis_proj]
  rw [Finset.sum_eq_single i (fun j _ hji => ?_) (fun hi => absurd (Finset.mem_univ i) hi)]
  · -- the block polar factor sends `b i` to the polar phase of the overlap times `b' i`
    have hinv : operatorAbs (OrthonormalBasis.spanIndicesProjection b' {i} ∘ₗ
          OrthonormalBasis.spanIndicesProjection b {i})
        (((‖⟪b' i, b i⟫_𝕜‖⁻¹ : ℝ) : 𝕜) • b i) = b i := by
      rw [map_smul, habs, smul_smul, ← RCLike.ofReal_mul, inv_mul_cancel₀ hcnorm]
      simp
    rw [hPb]
    conv_lhs => rw [← hinv]
    rw [polarFactor_apply_operatorAbs_apply, map_smul, hMb, smul_smul]
  · rw [OrthonormalBasis.spanIndicesProjection_apply_basis]
    simp only [Finset.mem_singleton]
    rw [ite_eq_right (Ne.symm hji), map_zero]

/-- **BL4 — the angle interpretation for eigen-families:** the squared sine of the `i`-th
rotation angle of the canonical unitary is the complementary squared overlap,
`sin²θᵢ = 1 − ‖⟪b'ᵢ, bᵢ⟫‖²`. Davis §2, lines 265–312. -/
theorem sqSinAngle_ofOrthonormalBasis {b b' : OrthonormalBasis (Fin n) 𝕜 E}
    (h : ∀ i, ⟪b' i, b i⟫_𝕜 ≠ 0) (i : Fin n) :
    OrthoProjFamily.sqSinAngle (nonDegenerate_ofOrthonormalBasis h) b i
      = 1 - ‖⟪b' i, b i⟫_𝕜‖ ^ 2 := by
  have hcnorm : ‖⟪b' i, b i⟫_𝕜‖ ≠ 0 := norm_ne_zero_iff.mpr (h i)
  have hscalar : ‖⟪b' i, b i⟫_𝕜‖⁻¹ * ‖⟪b' i, b i⟫_𝕜‖ ^ 2 = ‖⟪b' i, b i⟫_𝕜‖ := by
    rw [pow_two, ← mul_assoc, inv_mul_cancel₀ hcnorm, one_mul]
  unfold OrthoProjFamily.sqSinAngle
  simp only [intertwiningUnitary_apply_ofOrthonormalBasis h i, inner_smul_right,
    ← inner_conj_symm (b i) (b' i), mul_assoc, RCLike.mul_conj, ← RCLike.ofReal_pow,
    ← RCLike.ofReal_mul, hscalar, RCLike.norm_ofReal, abs_norm]

/-- **Theorem 3.2 through the canonical intertwining unitary** (PD-18 milestone): Davis's
sharper total-rotation estimate with the rotation measured by
`OrthoProjFamily.sqSinAngle` of the canonical unitary matching the two eigen-decompositions. -/
theorem rotation_add_displacement_le_hilbertSchmidt_intertwining
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n) {γ' : ℝ}
    (hover : ∀ i, ⟪hS.eigenvectorBasis hn i, hT.eigenvectorBasis hn i⟫_𝕜 ≠ 0)
    (hsep : ∀ i j, i ≠ j →
      γ' ^ 2 + (hT.eigenvalues hn i - hS.eigenvalues hn i) ^ 2
        ≤ (hT.eigenvalues hn i - hS.eigenvalues hn j) ^ 2) :
    γ' ^ 2 * ∑ i, OrthoProjFamily.sqSinAngle (nonDegenerate_ofOrthonormalBasis hover)
          (hT.eigenvectorBasis hn) i
        + ∑ i, (hT.eigenvalues hn i - hS.eigenvalues hn i) ^ 2
      ≤ ∑ i, ‖(S - T) (hT.eigenvectorBasis hn i)‖ ^ 2 := by
  have hrw : ∑ i, OrthoProjFamily.sqSinAngle (nonDegenerate_ofOrthonormalBasis hover)
      (hT.eigenvectorBasis hn) i
      = ∑ i, (1 - ‖⟪hS.eigenvectorBasis hn i, hT.eigenvectorBasis hn i⟫_𝕜‖ ^ 2) :=
    Finset.sum_congr rfl fun i _ => sqSinAngle_ofOrthonormalBasis hover i
  rw [hrw]
  exact rotation_add_displacement_le_hilbertSchmidt hT hS hn hsep

/-! ### The corollary with Result A (BL6) -/

omit [FiniteDimensional 𝕜 E] in
/-- The diagonal entry of a symmetric operator is real, so its squared norm is the squared
real part. -/
private theorem norm_sq_inner_map_self (hS : S.IsSymmetric) (y : E) :
    ‖⟪y, S y⟫_𝕜‖ ^ 2 = RCLike.re ⟪y, S y⟫_𝕜 ^ 2 := by
  have hconj : (starRingEnd 𝕜) ⟪y, S y⟫_𝕜 = ⟪y, S y⟫_𝕜 := by
    rw [inner_conj_symm, hS y y]
  rw [← RCLike.conj_eq_iff_re.mp hconj, RCLike.norm_ofReal, sq_abs, RCLike.ofReal_re]

/-- **Davis's two encodings of `‖𝒞⊥H‖²_F` agree**: the Frobenius energy of `S` above its
diagonal (in `T`'s eigenbasis) equals that of `H = S − T`, because `T` is diagonal there:
`∑ᵢ λ'ᵢ² − ∑ᵢ (re⟪xᵢ, S xᵢ⟫)² = ∑ᵢ ‖H xᵢ‖² − ∑ᵢ (re⟪xᵢ, H xᵢ⟫)²`. -/
theorem sum_sq_eigenvalues_sub_diag_eq (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (hn : finrank 𝕜 E = n) :
    (∑ i, hS.eigenvalues hn i ^ 2)
        - ∑ i, RCLike.re ⟪hT.eigenvectorBasis hn i, S (hT.eigenvectorBasis hn i)⟫_𝕜 ^ 2
      = (∑ i, ‖(S - T) (hT.eigenvectorBasis hn i)‖ ^ 2)
        - ∑ i, RCLike.re
            ⟪hT.eigenvectorBasis hn i, (S - T) (hT.eigenvectorBasis hn i)⟫_𝕜 ^ 2 := by
  -- Frobenius invariance: `∑ᵢ ‖S xᵢ‖² = ∑ⱼ λ'ⱼ²`
  have hfrob : ∑ i, ‖S (hT.eigenvectorBasis hn i)‖ ^ 2 = ∑ j, hS.eigenvalues hn j ^ 2 := by
    have h2 : ∀ (i j : Fin n), ‖⟪hS.eigenvectorBasis hn j, S (hT.eigenvectorBasis hn i)⟫_𝕜‖ ^ 2
        = hS.eigenvalues hn j ^ 2
            * ‖⟪hS.eigenvectorBasis hn j, hT.eigenvectorBasis hn i⟫_𝕜‖ ^ 2 := fun i j => by
      have hj : ⟪hS.eigenvectorBasis hn j, S (hT.eigenvectorBasis hn i)⟫_𝕜
          = ((hS.eigenvalues hn j : ℝ) : 𝕜)
              * ⟪hS.eigenvectorBasis hn j, hT.eigenvectorBasis hn i⟫_𝕜 := by
        rw [← hS (hS.eigenvectorBasis hn j) (hT.eigenvectorBasis hn i),
          hS.apply_eigenvectorBasis, inner_smul_left, RCLike.conj_ofReal]
      rw [hj, norm_mul, mul_pow, RCLike.norm_ofReal, sq_abs]
    calc ∑ i, ‖S (hT.eigenvectorBasis hn i)‖ ^ 2
        = ∑ i, ∑ j, ‖⟪hS.eigenvectorBasis hn j, S (hT.eigenvectorBasis hn i)⟫_𝕜‖ ^ 2 :=
          Finset.sum_congr rfl fun i _ =>
            ((hS.eigenvectorBasis hn).sum_sq_norm_inner_right _).symm
      _ = ∑ j, ∑ i, hS.eigenvalues hn j ^ 2
            * ‖⟪hS.eigenvectorBasis hn j, hT.eigenvectorBasis hn i⟫_𝕜‖ ^ 2 := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => h2 i j
      _ = ∑ j, hS.eigenvalues hn j ^ 2 := Finset.sum_congr rfl fun j _ => by
          rw [← Finset.mul_sum, (hT.eigenvectorBasis hn).sum_sq_norm_inner_left
            (hS.eigenvectorBasis hn j), (hS.eigenvectorBasis hn).orthonormal.1 j, one_pow,
            mul_one]
  -- per-row: removing the (real) diagonal entry, `S` and `H` have the same off-diagonal mass
  have hrow : ∀ i, ‖S (hT.eigenvectorBasis hn i)‖ ^ 2
        - RCLike.re ⟪hT.eigenvectorBasis hn i, S (hT.eigenvectorBasis hn i)⟫_𝕜 ^ 2
      = ‖(S - T) (hT.eigenvectorBasis hn i)‖ ^ 2
        - RCLike.re
            ⟪hT.eigenvectorBasis hn i, (S - T) (hT.eigenvectorBasis hn i)⟫_𝕜 ^ 2 := by
    intro i
    have hoff : ∀ j, j ≠ i → ⟪hT.eigenvectorBasis hn j, S (hT.eigenvectorBasis hn i)⟫_𝕜
        = ⟪hT.eigenvectorBasis hn j, (S - T) (hT.eigenvectorBasis hn i)⟫_𝕜 := fun j hj => by
      rw [LinearMap.sub_apply, inner_sub_right, hT.apply_eigenvectorBasis, inner_smul_right,
        orthonormal_iff_ite.mp (hT.eigenvectorBasis hn).orthonormal j i, ite_eq_right hj]
      simp
    have h1 := Finset.add_sum_erase Finset.univ
      (fun j => ‖⟪hT.eigenvectorBasis hn j, S (hT.eigenvectorBasis hn i)⟫_𝕜‖ ^ 2)
      (Finset.mem_univ i)
    have h2 := Finset.add_sum_erase Finset.univ
      (fun j => ‖⟪hT.eigenvectorBasis hn j, (S - T) (hT.eigenvectorBasis hn i)⟫_𝕜‖ ^ 2)
      (Finset.mem_univ i)
    have hsum : ∑ j ∈ Finset.univ.erase i,
        ‖⟪hT.eigenvectorBasis hn j, S (hT.eigenvectorBasis hn i)⟫_𝕜‖ ^ 2
        = ∑ j ∈ Finset.univ.erase i,
          ‖⟪hT.eigenvectorBasis hn j, (S - T) (hT.eigenvectorBasis hn i)⟫_𝕜‖ ^ 2 :=
      Finset.sum_congr rfl fun j hj => by rw [hoff j (Finset.ne_of_mem_erase hj)]
    simp only [← (hT.eigenvectorBasis hn).sum_sq_norm_inner_right (S (hT.eigenvectorBasis hn i)),
      ← (hT.eigenvectorBasis hn).sum_sq_norm_inner_right ((S - T) (hT.eigenvectorBasis hn i)),
      ← h1, ← h2, hsum, norm_sq_inner_map_self hS, norm_sq_inner_map_self (hS.sub hT)]
    ring
  calc (∑ i, hS.eigenvalues hn i ^ 2)
        - ∑ i, RCLike.re ⟪hT.eigenvectorBasis hn i, S (hT.eigenvectorBasis hn i)⟫_𝕜 ^ 2
      = ∑ i, (‖S (hT.eigenvectorBasis hn i)‖ ^ 2
          - RCLike.re ⟪hT.eigenvectorBasis hn i, S (hT.eigenvectorBasis hn i)⟫_𝕜 ^ 2) := by
        rw [Finset.sum_sub_distrib, hfrob]
    _ = ∑ i, (‖(S - T) (hT.eigenvectorBasis hn i)‖ ^ 2
          - RCLike.re
              ⟪hT.eigenvectorBasis hn i, (S - T) (hT.eigenvectorBasis hn i)⟫_𝕜 ^ 2) :=
        Finset.sum_congr rfl fun i _ => hrow i
    _ = _ := by rw [Finset.sum_sub_distrib]

/-- **The payoff (BL6, Davis digest §5):** combining the sharper rotation bound (Theorem 3.2)
with the eigenvalue-change lower bound (Theorem 4.1, `sum_sq_eigenvalues_sub_ge`), a fixed
perturbation budget spent on eigenvalue motion is unavailable for rotation:

`(γ')² ∑ᵢ sin²θᵢ ≤ 2 ‖𝒞⊥H‖²_F = 2 (∑ᵢ ‖H xᵢ‖² − ∑ᵢ (re⟪xᵢ, H xᵢ⟫)²)`

— eigenvector rotation is controlled by the off-diagonal part of the perturbation alone. -/
theorem rotation_le_two_mul_offDiag
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n)
    {γ γ' : ℝ} (hγ : 0 ≤ γ)
    (hsepS : ∀ i j, i ≠ j → γ ≤ |hS.eigenvalues hn i - hS.eigenvalues hn j|)
    (hCH : ∑ i, RCLike.re
        ⟪hT.eigenvectorBasis hn i, (S - T) (hT.eigenvectorBasis hn i)⟫_𝕜 ^ 2
      ≤ (γ / Real.sqrt 2) ^ 2)
    (hover : ∀ i, ⟪hS.eigenvectorBasis hn i, hT.eigenvectorBasis hn i⟫_𝕜 ≠ 0)
    (hsep : ∀ i j, i ≠ j →
      γ' ^ 2 + (hT.eigenvalues hn i - hS.eigenvalues hn i) ^ 2
        ≤ (hT.eigenvalues hn i - hS.eigenvalues hn j) ^ 2) :
    γ' ^ 2 * ∑ i, OrthoProjFamily.sqSinAngle (nonDegenerate_ofOrthonormalBasis hover)
        (hT.eigenvectorBasis hn) i
      ≤ 2 * ((∑ i, ‖(S - T) (hT.eigenvectorBasis hn i)‖ ^ 2)
          - ∑ i, RCLike.re
              ⟪hT.eigenvectorBasis hn i, (S - T) (hT.eigenvectorBasis hn i)⟫_𝕜 ^ 2) := by
  have hB := rotation_add_displacement_le_hilbertSchmidt_intertwining hT hS hn hover hsep
  have hA := sum_sq_eigenvalues_sub_ge hT hS hn hγ hsepS hCH
  have hid := sum_sq_eigenvalues_sub_diag_eq hT hS hn
  have hsym : ∑ i, (hS.eigenvalues hn i - hT.eigenvalues hn i) ^ 2
      = ∑ i, (hT.eigenvalues hn i - hS.eigenvalues hn i) ^ 2 :=
    Finset.sum_congr rfl fun i _ => by ring
  linarith [hB, hA, hid, hsym]

end TauCeti
