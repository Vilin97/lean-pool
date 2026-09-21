/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.TanTwoThetaUnboundedGramBridge
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SharpKyFan

/-! # Tan Two Theta Unbounded Gram Middle -/

open TauCeti.DavisKahan.Angle


open TauCeti.DavisKahan.Sylvester

/-!
# The middle inequality of the unbounded `tan 2Θ` chain

`TanTwoThetaUnboundedGramBridge.lean` proves the two outer pieces of

`kyFan k T₀ ≤ ∑_{n<k} tan (arcsin aₙ(S₀)) ≤ (2/δ) · kyFan k R`

on the typed directed corners.  This module proves the **middle inequality**,
with no extremality and no eigenbasis hypothesis anywhere.

## The approximate sum layer

`TanTwoThetaUnboundedKyFan.lean` supplies the approximate *per-vector* estimate
`gap_mul_sq_le_paired_of_approximateDoubleAngleEigenvector` and the compressed
Gram estimate `abs_norm_sq_offDiagonalPart_sum_sub_le` on a whole linear
combination.  What is added here is the *sum* layer: approximate analogues of
`sq_norm_sum_smul_diagonalPart_offDiagonalPart_le_of_compressed` and
`gap_mul_sum_tangent_le_kyFan_of_compressedDoubleAngleEigenfamily`.

The families a `GramSpectralBandModel` selects are exactly orthonormal, but the
three *normalised* systems `S xᵢ / qᵢ`, `C xᵢ / cᵢ` and `C (S xᵢ) / (qᵢ cᵢ)` are
not.  They are still **contraction systems**, with constants `1 + O(ρ)` at a
fixed threshold `θ` on the retained singular values, and
`sum_le_kyFanApproximationGauge_of_contraction` consumes exactly that.

## The order of the passages

Three parameters occur and the order in which they are released is load bearing.

* `ρ → 0` **at fixed `τ` and fixed `θ`**.  The unbounded operator `A` is met
  once, in `gap_mul_sq_le_paired_of_approximateDoubleAngleEigenvector`, and it
  contributes `(τ + |b|) ρ / (4κ)` per retained index — a product of `τ` with a
  quantity that goes to zero *at fixed `τ`*.  No term of the form
  `τ · cutoff-error(τ)` is ever formed.
* `θ → 0` next.  Dropping the singular values below `θ` costs `k θ / κ`.
* `Ω → I` last, through
  `tendsto_sum_tanArcsin_approximationNumber_reflectionSineCorner_comp`.  By
  then the bound `2 · kyFan k R` carries no `τ`, no `ρ` and no `θ`, so the
  cutoff level of the net is unconstrained.

## Main results

* `sq_norm_offDiagonalPart_sq_sum_ge` — the approximate lower bound on `‖S² g‖`.
* `sq_norm_sum_smul_offDiagonalPart_le_of_approximate`,
  `sq_norm_sum_smul_diagonalPart_le_of_approximate`,
  `sq_norm_sum_smul_diagonalPart_offDiagonalPart_le_of_approximate` — Checkpoint
  C1, the three contraction systems.
* `gap_mul_sum_tangent_le_kyFan_of_approximateDoubleAngleEigenfamily` —
  Checkpoint C2, the fixed-`(τ, θ, ρ)` summed estimate.
* `gap_mul_sum_tanArcsin_le_two_mul_kyFan_of_cutoff` — Checkpoint C3, the
  fixed-cutoff middle inequality after `ρ → 0` and `θ → 0`.
* `gap_mul_kyFan_reflectionTangentCorner_le_two_mul_kyFan` — the full endpoint,
  composed with the two halves of `TanTwoThetaUnboundedGramBridge.lean`.
* `mem_and_gauge_le_reflectionTangentCorner` — the same endpoint at every
  Fan-dominant unitarily invariant ideal gauge.

Both Ky Fan pairings are charged to the **typed** directed residual corner
`reflectionResidualCorner U B = blockCompression Uᗮ U B`, through
`sum_le_kyFanApproximationGauge_reflectionResidualCorner_of_contraction`.  That
keeps tangent and residual in one space pair, which is what the Fan-dominance
bridge needs, and it is also what pins the sharp constant: the two pairings are
charged **once each to the same gauge**.

## References

* C. Davis and W. M. Kahan, *The rotation of eigenvectors by a perturbation.
  III*, SIAM J. Numer. Anal. 7 (1970), 1--46, Section 7 and the Appendix to
  Section 6.
-/

namespace TauCeti
namespace DavisKahan1970

open scoped InnerProductSpace BigOperators

open TauCeti.DavisKahan.ExactSinTheta
open TauCeti.ApproximationNumber
open scoped TauCeti.CompleteSubspace

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

variable {U : Submodule ℂ H} [U.HasOrthogonalProjection]
variable {A : H →ₗ.[ℂ] H} {B Z : H →L[ℂ] H} {a b τ : ℝ}

/-! ### Checkpoint C1: the three contraction systems -/

/-- **The approximate lower bound on the squared odd block.**

At a compressed eigenfamily `‖S² g‖² ≥ ∑ᵢ |βᵢ|² qᵢ⁴` holds exactly, because the
trial-space part of `S² g` is `∑ᵢ βᵢ qᵢ² xᵢ` and dropping the leakage only
decreases the norm.  With only an approximate compressed relation the same
argument survives with one additive error: the cutoff is a contraction, so
`‖S² g‖ ≥ ‖Ω S² g‖`, and `Ω S² g` differs from `∑ᵢ βᵢ qᵢ² xᵢ` by at most
`n ε ‖g‖`.

This is the one place the *lower* Gram bound is used, and its sign is what keeps
the fourth auxiliary system a contraction. -/
theorem sq_norm_offDiagonalPart_sq_sum_ge
    (Ω : TauCeti.BoundedCutoff A U τ)
    {n : ℕ} {x : Fin n → H}
    (hx : Orthonormal ℂ x)
    {q : Fin n → ℝ} {ε : ℝ} (hε : 0 ≤ ε) (hq1 : ∀ i, q i ^ 2 ≤ 1)
    (heig : ∀ i, ‖Ω.toProj (U.offDiagonalPart Z (U.offDiagonalPart Z (x i))) -
      ((q i ^ 2 : ℝ) : ℂ) • x i‖ ≤ ε)
    (β : Fin n → ℂ) :
    (∑ i, ‖β i‖ ^ 2 * q i ^ 4) - 2 * (n * ε) * (∑ i, ‖β i‖ ^ 2) ≤
      ‖U.offDiagonalPart Z
        (U.offDiagonalPart Z (∑ i, β i • x i))‖ ^ 2 := by
  classical
  set g : H := ∑ i, β i • x i with hgdef
  set d : Fin n → H := fun i =>
    Ω.toProj (U.offDiagonalPart Z (U.offDiagonalPart Z (x i))) -
      ((q i ^ 2 : ℝ) : ℂ) • x i with hddef
  set p : H := ∑ i, (β i * ((q i ^ 2 : ℝ) : ℂ)) • x i with hpdef
  have hgnorm : ‖g‖ ^ 2 = ∑ i, ‖β i‖ ^ 2 :=
    norm_sq_sum_smul_of_orthonormal hx β
  have hpnorm : ‖p‖ ^ 2 = ∑ i, ‖β i‖ ^ 2 * q i ^ 4 := by
    rw [hpdef, norm_sq_sum_smul_of_orthonormal hx]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg (q i))]
    ring
  have hsplit : Ω.toProj (U.offDiagonalPart Z (U.offDiagonalPart Z g)) =
      p + ∑ i, β i • d i := by
    rw [hgdef, hpdef, map_sum, map_sum, map_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, map_smul, map_smul, hddef]
    simp only [smul_sub, smul_smul]
    module
  have hDnorm : ‖∑ i, β i • d i‖ ≤ n * ε * ‖g‖ := by
    refine le_trans (norm_sum_le _ _) ?_
    have hbd : ∀ i : Fin n, ‖β i • d i‖ ≤ ‖g‖ * ε := by
      intro i
      rw [norm_smul]
      have hβ : ‖β i‖ ≤ ‖g‖ := by
        have h1 : ‖β i‖ ^ 2 ≤ ∑ j, ‖β j‖ ^ 2 :=
          Finset.single_le_sum (f := fun j => ‖β j‖ ^ 2)
            (fun j _ => sq_nonneg _) (Finset.mem_univ i)
        nlinarith [norm_nonneg (β i), norm_nonneg g, hgnorm, h1]
      exact mul_le_mul hβ (heig i) (norm_nonneg _) (norm_nonneg g)
    calc ∑ i, ‖β i • d i‖ ≤ ∑ _i : Fin n, ‖g‖ * ε :=
          Finset.sum_le_sum fun i _ => hbd i
      _ = n * ε * ‖g‖ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have hple : ‖p‖ ≤ ‖g‖ := by
    have hterm : ∑ i, ‖β i‖ ^ 2 * q i ^ 4 ≤ ∑ i, ‖β i‖ ^ 2 := by
      refine Finset.sum_le_sum fun i _ => ?_
      have h4 : q i ^ 4 ≤ 1 := by nlinarith [hq1 i, sq_nonneg (q i)]
      nlinarith [sq_nonneg ‖β i‖, h4, sq_nonneg (q i)]
    nlinarith [hpnorm, hgnorm, norm_nonneg p, norm_nonneg g, hterm]
  have htri : ‖p‖ - ‖∑ i, β i • d i‖ ≤
      ‖U.offDiagonalPart Z (U.offDiagonalPart Z g)‖ := by
    refine le_trans ?_ (Ω.norm_toProj_apply_le _)
    rw [hsplit]
    have h := norm_sub_le (p + ∑ i, β i • d i) (∑ i, β i • d i)
    rw [add_sub_cancel_right] at h
    linarith
  set N : ℝ := ‖U.offDiagonalPart Z (U.offDiagonalPart Z g)‖ with hNdef
  have hN0 : 0 ≤ N := norm_nonneg _
  have hD0 : 0 ≤ ‖∑ i, β i • d i‖ := norm_nonneg _
  have hP0 : 0 ≤ ‖p‖ := norm_nonneg _
  have hG0 : 0 ≤ ‖g‖ := norm_nonneg _
  have hnε : 0 ≤ (n : ℝ) * ε := mul_nonneg (Nat.cast_nonneg n) hε
  rw [← hpnorm, ← hgnorm]
  rcases le_or_gt (‖∑ i, β i • d i‖) ‖p‖ with hcase | hcase
  · have hstep : ‖p‖ - ‖∑ i, β i • d i‖ ≤ N := htri
    nlinarith [hstep, hcase, hDnorm, hple, hN0, hP0, hG0, hnε]
  · nlinarith [hcase, hDnorm, hple, hN0, hP0, hG0, hnε]

/-- **The first normalised system is a contraction system.**

The vectors `S xᵢ / qᵢ` are exactly orthonormal at an exact eigenfamily.  At an
approximate one their Gram matrix is `1 + O(ε / θ²)`, where `θ` is a lower
threshold on the retained singular values `qᵢ`: the compressed Gram estimate
controls the defect by `n ε ∑ᵢ |βᵢ|²`, and the retained coefficients satisfy
`θ² ∑ᵢ |βᵢ|² ≤ ∑ᵢ |αᵢ|²`.

The sign of the system is flipped, because that is the shape the branch-free
per-index estimate produces. -/
theorem sq_norm_sum_smul_offDiagonalPart_le_of_approximate
    (hZsa : IsSelfAdjoint Z) (Ω : TauCeti.BoundedCutoff A U τ)
    {n : ℕ} {x : Fin n → H}
    (hx : Orthonormal ℂ x) (hxΩ : ∀ i, Ω.toProj (x i) = x i)
    {q : Fin n → ℝ} {ε θ c : ℝ} (hε : 0 ≤ ε) (hθ : 0 < θ)
    (hqθ : ∀ i, θ ≤ q i)
    (heig : ∀ i, ‖Ω.toProj (U.offDiagonalPart Z (U.offDiagonalPart Z (x i))) -
      ((q i ^ 2 : ℝ) : ℂ) • x i‖ ≤ ε)
    (hc : 1 + (n : ℝ) * ε / θ ^ 2 ≤ c ^ 2) (α : Fin n → ℂ) :
    ‖∑ i, α i • (-((((q i : ℝ)) : ℂ)⁻¹ • U.offDiagonalPart Z (x i)))‖ ^ 2 ≤
      c ^ 2 * ∑ i, ‖α i‖ ^ 2 := by
  classical
  have hqpos : ∀ i, 0 < q i := fun i => lt_of_lt_of_le hθ (hqθ i)
  have hqne : ∀ i, (((q i : ℝ) : ℂ)) ≠ 0 := fun i => by simpa using (hqpos i).ne'
  set β : Fin n → ℂ := fun i => α i * (((q i : ℝ) : ℂ))⁻¹ with hβdef
  set g : H := ∑ i, β i • x i with hgdef
  have hcomb : ∑ i, α i • (-((((q i : ℝ)) : ℂ)⁻¹ •
      U.offDiagonalPart Z (x i))) = -(U.offDiagonalPart Z g) := by
    rw [hgdef, map_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_neg, smul_smul]
  have hnβ : ∀ i, ‖β i‖ = ‖α i‖ * (q i)⁻¹ := by
    intro i
    rw [hβdef]
    simp only [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (hqpos i)]
  have hAB : ∑ i, ‖β i‖ ^ 2 * q i ^ 2 = ∑ i, ‖α i‖ ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hnβ i, mul_pow, inv_pow,
      inv_mul_cancel_right₀ (pow_ne_zero 2 (hqpos i).ne')]
  have hBA : θ ^ 2 * ∑ i, ‖β i‖ ^ 2 ≤ ∑ i, ‖α i‖ ^ 2 := by
    rw [Finset.mul_sum, ← hAB]
    refine Finset.sum_le_sum fun i _ => ?_
    have hsq : θ ^ 2 ≤ q i ^ 2 := by nlinarith [hqθ i, hθ, hqpos i]
    nlinarith [sq_nonneg ‖β i‖, hsq]
  have hgram := abs_norm_sq_offDiagonalPart_sum_sub_le hZsa Ω hx hxΩ heig β
  have hupper : ‖U.offDiagonalPart Z g‖ ^ 2 ≤
      ∑ i, ‖α i‖ ^ 2 + (n * ε) * ∑ i, ‖β i‖ ^ 2 := by
    have h := le_of_abs_le hgram
    rw [hAB] at h
    linarith [h]
  have hα0 : (0 : ℝ) ≤ ∑ i, ‖α i‖ ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hnε : (0 : ℝ) ≤ (n : ℝ) * ε := mul_nonneg (Nat.cast_nonneg n) hε
  have hkey : (n * ε) * ∑ i, ‖β i‖ ^ 2 ≤
      ((n : ℝ) * ε / θ ^ 2) * ∑ i, ‖α i‖ ^ 2 := by
    have hθ2 : (0 : ℝ) < θ ^ 2 := by positivity
    rw [div_mul_eq_mul_div, le_div_iff₀ hθ2]
    nlinarith [hBA, hnε]
  rw [hcomb, norm_neg]
  nlinarith [hupper, hkey, hc, hα0]

/-- **The second normalised system is a contraction system.**

The vectors `C xᵢ / cᵢ`, `cᵢ = √(1 - qᵢ²)`, with constant `1 + O(ε / κ²)` for a
lower bound `κ` on the cosine factors.  Here the compressed Gram estimate is used
in the *lower* direction, through the double-angle Pythagoras identity
`‖C h‖² = ‖h‖² - ‖S h‖²`. -/
theorem sq_norm_sum_smul_diagonalPart_le_of_approximate
    (hZsa : IsSelfAdjoint Z) (hZ2 : Z * Z = 1) (Ω : TauCeti.BoundedCutoff A U τ)
    {n : ℕ} {x : Fin n → H}
    (hx : Orthonormal ℂ x) (hxΩ : ∀ i, Ω.toProj (x i) = x i)
    {q : Fin n → ℝ} {ε κ c : ℝ} (hε : 0 ≤ ε) (hκ : 0 < κ)
    (hκq : ∀ i, κ ^ 2 ≤ 1 - q i ^ 2)
    (heig : ∀ i, ‖Ω.toProj (U.offDiagonalPart Z (U.offDiagonalPart Z (x i))) -
      ((q i ^ 2 : ℝ) : ℂ) • x i‖ ≤ ε)
    (hc : 1 + (n : ℝ) * ε / κ ^ 2 ≤ c ^ 2) (α : Fin n → ℂ) :
    ‖∑ i, α i • ((((√(1 - q i ^ 2) : ℝ)) : ℂ)⁻¹ •
      U.diagonalPart Z (x i))‖ ^ 2 ≤ c ^ 2 * ∑ i, ‖α i‖ ^ 2 := by
  classical
  have hc0 : ∀ i, 0 < 1 - q i ^ 2 := fun i => lt_of_lt_of_le (by positivity) (hκq i)
  have hcpos : ∀ i, 0 < √(1 - q i ^ 2) := fun i => Real.sqrt_pos.mpr (hc0 i)
  have hcsq : ∀ i, √(1 - q i ^ 2) ^ 2 = 1 - q i ^ 2 :=
    fun i => Real.sq_sqrt (hc0 i).le
  set γ : Fin n → ℂ := fun i => α i * (((√(1 - q i ^ 2) : ℝ) : ℂ))⁻¹ with hγdef
  set h : H := ∑ i, γ i • x i with hhdef
  have hcomb : ∑ i, α i • ((((√(1 - q i ^ 2) : ℝ)) : ℂ)⁻¹ •
      U.diagonalPart Z (x i)) = U.diagonalPart Z h := by
    rw [hhdef, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_smul]
  have hnγ : ∀ i, ‖γ i‖ = ‖α i‖ * (√(1 - q i ^ 2))⁻¹ := by
    intro i
    rw [hγdef]
    simp only [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (hcpos i)]
  have hAB : ∑ i, ‖γ i‖ ^ 2 * (1 - q i ^ 2) = ∑ i, ‖α i‖ ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hnγ i, mul_pow, inv_pow, hcsq i, inv_mul_cancel_right₀ (hc0 i).ne']
  have hBA : κ ^ 2 * ∑ i, ‖γ i‖ ^ 2 ≤ ∑ i, ‖α i‖ ^ 2 := by
    rw [Finset.mul_sum, ← hAB]
    refine Finset.sum_le_sum fun i _ => ?_
    nlinarith [sq_nonneg ‖γ i‖, hκq i]
  have hgram := abs_norm_sq_offDiagonalPart_sum_sub_le hZsa Ω hx hxΩ heig γ
  have hpyth := norm_sq_diagonalPart_apply (U := U) hZsa hZ2 h
  have hhnorm : ‖h‖ ^ 2 = ∑ i, ‖γ i‖ ^ 2 :=
    norm_sq_sum_smul_of_orthonormal hx γ
  have hlower : ∑ i, ‖γ i‖ ^ 2 * q i ^ 2 - (n * ε) * ∑ i, ‖γ i‖ ^ 2 ≤
      ‖U.offDiagonalPart Z h‖ ^ 2 := by
    have h1 := neg_le_of_abs_le hgram
    linarith [h1]
  have hα0 : (0 : ℝ) ≤ ∑ i, ‖α i‖ ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hnε : (0 : ℝ) ≤ (n : ℝ) * ε := mul_nonneg (Nat.cast_nonneg n) hε
  have hsplit : ∑ i, ‖γ i‖ ^ 2 - ∑ i, ‖γ i‖ ^ 2 * q i ^ 2 = ∑ i, ‖α i‖ ^ 2 := by
    rw [← hAB, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hkey : (n * ε) * ∑ i, ‖γ i‖ ^ 2 ≤
      ((n : ℝ) * ε / κ ^ 2) * ∑ i, ‖α i‖ ^ 2 := by
    have hκ2 : (0 : ℝ) < κ ^ 2 := by positivity
    rw [div_mul_eq_mul_div, le_div_iff₀ hκ2]
    nlinarith [hBA, hnε]
  rw [hcomb, hpyth, hhnorm]
  nlinarith [hlower, hkey, hsplit, hc, hα0]

/-- **The third normalised system is a contraction system.**

`C (S xᵢ) / (qᵢ cᵢ)`, with constant `1 + O(ε / (θ² κ²))`.  This is the
approximate analogue of
`sq_norm_sum_smul_diagonalPart_offDiagonalPart_le_of_compressed`, and it is the
system whose defect is *not* controlled by the compressed Gram estimate alone:
`‖C S g‖² = ‖S g‖² - ‖S² g‖²` needs an upper bound on the first term and a
**lower** bound on the second, and the latter is
`sq_norm_offDiagonalPart_sq_sum_ge`.  Both errors have the same sign, so they
add rather than cancel, and the constant is `1 + 3nε/(θ²κ²)`. -/
theorem sq_norm_sum_smul_diagonalPart_offDiagonalPart_le_of_approximate
    (hZsa : IsSelfAdjoint Z) (hZ2 : Z * Z = 1) (Ω : TauCeti.BoundedCutoff A U τ)
    {n : ℕ} {x : Fin n → H}
    (hx : Orthonormal ℂ x) (hxΩ : ∀ i, Ω.toProj (x i) = x i)
    {q : Fin n → ℝ} {ε θ κ c : ℝ} (hε : 0 ≤ ε) (hθ : 0 < θ) (hκ : 0 < κ)
    (hqθ : ∀ i, θ ≤ q i) (hκq : ∀ i, κ ^ 2 ≤ 1 - q i ^ 2)
    (heig : ∀ i, ‖Ω.toProj (U.offDiagonalPart Z (U.offDiagonalPart Z (x i))) -
      ((q i ^ 2 : ℝ) : ℂ) • x i‖ ≤ ε)
    (hc : 1 + 3 * (n : ℝ) * ε / (θ ^ 2 * κ ^ 2) ≤ c ^ 2) (α : Fin n → ℂ) :
    ‖∑ i, α i • ((((q i * √(1 - q i ^ 2)) : ℝ) : ℂ)⁻¹ •
        U.diagonalPart Z (U.offDiagonalPart Z (x i)))‖ ^ 2 ≤
      c ^ 2 * ∑ i, ‖α i‖ ^ 2 := by
  classical
  have hqpos : ∀ i, 0 < q i := fun i => lt_of_lt_of_le hθ (hqθ i)
  have hc0 : ∀ i, 0 < 1 - q i ^ 2 := fun i => lt_of_lt_of_le (by positivity) (hκq i)
  have hcpos : ∀ i, 0 < √(1 - q i ^ 2) := fun i => Real.sqrt_pos.mpr (hc0 i)
  have hcsq : ∀ i, √(1 - q i ^ 2) ^ 2 = 1 - q i ^ 2 :=
    fun i => Real.sq_sqrt (hc0 i).le
  have hqcpos : ∀ i, 0 < q i * √(1 - q i ^ 2) :=
    fun i => mul_pos (hqpos i) (hcpos i)
  have hq1 : ∀ i, q i ^ 2 ≤ 1 := fun i => by nlinarith [hc0 i]
  set β : Fin n → ℂ := fun i => α i * ((((q i * √(1 - q i ^ 2)) : ℝ) : ℂ))⁻¹
    with hβdef
  set g : H := ∑ i, β i • x i with hgdef
  have hcomb : ∑ i, α i • ((((q i * √(1 - q i ^ 2)) : ℝ) : ℂ)⁻¹ •
      U.diagonalPart Z (U.offDiagonalPart Z (x i))) =
      U.diagonalPart Z (U.offDiagonalPart Z g) := by
    rw [hgdef, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, map_smul, smul_smul]
  have hnβ : ∀ i, ‖β i‖ = ‖α i‖ * (q i * √(1 - q i ^ 2))⁻¹ := by
    intro i
    have hinvnorm : ‖((((q i * √(1 - q i ^ 2)) : ℝ) : ℂ))⁻¹‖ =
        (q i * √(1 - q i ^ 2))⁻¹ := by
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hqcpos i)]
    simp only [hβdef, norm_mul, hinvnorm]
  have hAB : ∑ i, ‖β i‖ ^ 2 * (q i ^ 2 * (1 - q i ^ 2)) = ∑ i, ‖α i‖ ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    have hqc2 : (q i * √(1 - q i ^ 2)) ^ 2 = q i ^ 2 * (1 - q i ^ 2) := by
      rw [mul_pow, hcsq i]
    have hne : q i ^ 2 * (1 - q i ^ 2) ≠ 0 :=
      ne_of_gt (mul_pos (pow_pos (hqpos i) 2) (hc0 i))
    rw [hnβ i, mul_pow, inv_pow, hqc2, inv_mul_cancel_right₀ hne]
  have hBA : θ ^ 2 * κ ^ 2 * ∑ i, ‖β i‖ ^ 2 ≤ ∑ i, ‖α i‖ ^ 2 := by
    rw [Finset.mul_sum, ← hAB]
    refine Finset.sum_le_sum fun i _ => ?_
    have hsq : θ ^ 2 ≤ q i ^ 2 := by nlinarith [hqθ i, hθ, hqpos i]
    have h1 : θ ^ 2 * κ ^ 2 ≤ q i ^ 2 * (1 - q i ^ 2) :=
      le_trans (mul_le_mul_of_nonneg_right hsq (sq_nonneg κ))
        (mul_le_mul_of_nonneg_left (hκq i) (sq_nonneg (q i)))
    calc θ ^ 2 * κ ^ 2 * ‖β i‖ ^ 2 ≤ q i ^ 2 * (1 - q i ^ 2) * ‖β i‖ ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
      _ = ‖β i‖ ^ 2 * (q i ^ 2 * (1 - q i ^ 2)) := by ring
  have hgram := abs_norm_sq_offDiagonalPart_sum_sub_le hZsa Ω hx hxΩ heig β
  have hsq := sq_norm_offDiagonalPart_sq_sum_ge (Z := Z) Ω hx hε hq1 heig β
  have hpyth := norm_sq_diagonalPart_apply (U := U) hZsa hZ2
    (U.offDiagonalPart Z g)
  have hα0 : (0 : ℝ) ≤ ∑ i, ‖α i‖ ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hnε : (0 : ℝ) ≤ (n : ℝ) * ε := mul_nonneg (Nat.cast_nonneg n) hε
  have hdiff : ∑ i, ‖β i‖ ^ 2 * q i ^ 2 - ∑ i, ‖β i‖ ^ 2 * q i ^ 4 =
      ∑ i, ‖α i‖ ^ 2 := by
    rw [← hAB, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hkey : 3 * ((n : ℝ) * ε) * ∑ i, ‖β i‖ ^ 2 ≤
      (3 * (n : ℝ) * ε / (θ ^ 2 * κ ^ 2)) * ∑ i, ‖α i‖ ^ 2 := by
    have hd : (0 : ℝ) < θ ^ 2 * κ ^ 2 := by positivity
    rw [div_mul_eq_mul_div, le_div_iff₀ hd]
    nlinarith [hBA, hnε]
  rw [hcomb, hpyth]
  have hupper := le_of_abs_le hgram
  nlinarith [hupper, hsq, hkey, hdiff, hc, hα0]

/-! ### Charging a pairing to the typed directed residual corner -/

section ScalarGenericResidualCorner

variable {𝕜 : Type*} [RCLike 𝕜] {G : Type u} [NormedAddCommGroup G]
  [InnerProductSpace 𝕜 G] [CompleteSpace G]

/-- The directed residual corner `R₀ : U → Uᗮ`, the companion of
`reflectionSineCorner` and `reflectionTangentCorner`. -/
abbrev reflectionResidualCorner (U : Submodule 𝕜 G) [U.HasOrthogonalProjection]
    (B : G →L[𝕜] G) : U →L[𝕜] Uᗮ := blockCompression Uᗮ U B

end ScalarGenericResidualCorner

/-- Pairing a vector of `Uᗮ` with the directed corner of `K` is the ambient
pairing: the projection in the corner is invisible on `Uᗮ`. -/
theorem inner_reflectionResidualCorner (K : H →L[ℂ] H) (u : Uᗮ) (v : U) :
    ⟪u, reflectionResidualCorner U K v⟫_ℂ = ⟪(u : H), K ((v : U) : H)⟫_ℂ := by
  have h : ((reflectionResidualCorner U K v : Uᗮ) : H) =
      Uᗮ.starProjection (K ((v : U) : H)) :=
    coe_blockCompression_apply Uᗮ U K v
  have h2 : ⟪u, reflectionResidualCorner U K v⟫_ℂ =
      ⟪(u : H), ((reflectionResidualCorner U K v : Uᗮ) : H)⟫_ℂ := rfl
  rw [h2, h, ← Submodule.inner_starProjection_left_eq_right,
    Submodule.starProjection_eq_self_iff.mpr u.2]

omit [CompleteSpace H] in
/-- A linear combination of a family inside a subspace has the same norm read in
the subspace and in the ambient space. -/
theorem norm_sum_smul_coe {W : Submodule ℂ H} [W.HasOrthogonalProjection]
    {n : ℕ} (u : Fin n → W) (α : Fin n → ℂ) :
    ‖∑ i, α i • u i‖ = ‖∑ i, α i • ((u i : W) : H)‖ := by
  have h : ((∑ i, α i • u i : W) : H) = ∑ i, α i • ((u i : W) : H) := by
    simp
  rw [← h]
  rfl

/-- **The contraction Ky Fan bound, charged to the directed corner.**

`sum_le_kyFanApproximationGauge_of_contraction` for an ambient operator `K`, two
ambient contraction systems lying in `Uᗮ` and `U` respectively, and the *typed*
gauge of `blockCompression Uᗮ U K`.  Charging to the corner rather than to
the ambient operator is what keeps the endpoint inside a single space pair, so
that the Fan-dominance bridge applies. -/
theorem sum_le_kyFanApproximationGauge_reflectionResidualCorner_of_contraction
    (K : H →L[ℂ] H) {n : ℕ} {u v : Fin n → H} {cu cv : ℝ}
    (hcu : 0 ≤ cu) (hcv : 0 ≤ cv)
    (hu : ∀ i, u i ∈ Uᗮ) (hv : ∀ i, v i ∈ U)
    (hucon : ∀ α : Fin n → ℂ, ‖∑ i, α i • u i‖ ^ 2 ≤ cu ^ 2 * ∑ i, ‖α i‖ ^ 2)
    (hvcon : ∀ α : Fin n → ℂ, ‖∑ i, α i • v i‖ ^ 2 ≤ cv ^ 2 * ∑ i, ‖α i‖ ^ 2)
    {t : Fin n → ℝ} (ht : ∀ i, t i ≤ RCLike.re ⟪u i, K (v i)⟫_ℂ) :
    ∑ i, t i ≤ cu * cv * kyFanApproximationGauge n
      (reflectionResidualCorner U K) := by
  classical
  set uu : Fin n → Uᗮ := fun i => ⟨u i, hu i⟩ with huudef
  set vv : Fin n → U := fun i => ⟨v i, hv i⟩ with hvvdef
  have hucoe : ∀ i, ((uu i : Uᗮ) : H) = u i := fun i => rfl
  have hvcoe : ∀ i, ((vv i : U) : H) = v i := fun i => rfl
  refine sum_le_kyFanApproximationGauge_of_contraction
    (reflectionResidualCorner U K) (u := uu) (v := vv) (cu := cu) (cv := cv)
    hcu hcv ?_ ?_ ?_
  · intro α
    rw [norm_sum_smul_coe]
    simpa only [hucoe] using hucon α
  · intro α
    rw [norm_sum_smul_coe]
    simpa only [hvcoe] using hvcon α
  · intro i
    rw [inner_reflectionResidualCorner, hucoe, hvcoe]
    exact ht i

/-! ### Checkpoint C2: the fixed-`(τ, θ, ρ)` summed estimate -/

/-- **The unbounded `tan 2Θ` Ky Fan estimate on an approximate double-angle
eigenfamily.**

The approximate analogue of
`gap_mul_sum_tangent_le_kyFan_of_compressedDoubleAngleEigenfamily`.  The exact
Gram relation is replaced by a *cutoff-compressed* defect bound
`‖Ω S² xᵢ - qᵢ² xᵢ‖ ≤ ρ qᵢ / 4`, which is exactly the residual a
`GramSpectralBandModel` delivers, and the exact orthonormality of the three
normalised systems by the contraction bounds above.

Two errors appear and both are charged once:

* the unbounded-`A` error `(τ + |b|) ρ / (4 κ)` per retained index — the factor
  `qᵢ` in the Gram residual cancels the `qᵢ` from the division, so **no
  small-`qᵢ` blow-up occurs here**, and the pole is excluded uniformly by `κ`;
* the contraction slack, which multiplies the *single* Ky Fan charge `2` by
  `c²`.  Both pairings are charged to the **same** gauge `kyFanApproximationGauge
  n B`, which is where the sharp `2` comes from. -/
theorem gap_mul_sum_tangent_le_kyFan_of_approximateDoubleAngleEigenfamily
    (hred : TauCeti.LinearPMap.ReducesSubspace A U) (hB : TauCeti.IsOddFor U B)
    (hZsa : IsSelfAdjoint Z) (hZ2 : Z * Z = 1)
    (hZdom : TauCeti.LinearPMap.MapsDomainTo A A Z)
    (hZcomm : ∀ x : A.domain,
      A ⟨Z (x : H), hZdom x⟩ + B (Z (x : H)) = Z (A x) + Z (B (x : H)))
    (hUa : ∀ x : A.domain, (x : H) ∈ U →
      RCLike.re ⟪A x, (x : H)⟫_ℂ ≤ a * ‖(x : H)‖ ^ 2)
    (hUb : ∀ x : A.domain, (x : H) ∈ Uᗮ →
      b * ‖(x : H)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : H)⟫_ℂ)
    (hτ : 0 ≤ τ) (Ω : TauCeti.BoundedCutoff A U τ)
    {n : ℕ} {x : Fin n → H}
    (hx : Orthonormal ℂ x) (hxΩ : ∀ i, Ω.toProj (x i) = x i)
    {q : Fin n → ℝ} {ρ θ κ c : ℝ} (hρ : 0 ≤ ρ) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hqθ : ∀ i, θ ≤ q i) (hκq : ∀ i, κ ^ 2 ≤ 1 - q i ^ 2)
    (heig : ∀ i, ‖Ω.toProj (U.offDiagonalPart Z (U.offDiagonalPart Z (x i))) -
      ((q i ^ 2 : ℝ) : ℂ) • x i‖ ≤ ρ * q i / 4)
    (hc1 : 1 ≤ c)
    (hc : 1 + 3 * (n : ℝ) * (ρ / 4) / (θ ^ 2 * κ ^ 2) ≤ c ^ 2) :
    (b - a) * ∑ i, q i / √(1 - q i ^ 2) ≤
      2 * c ^ 2 * kyFanApproximationGauge n (reflectionResidualCorner U B) +
        n * ((τ + |b|) * ρ / (4 * κ)) := by
  classical
  have hc0' : (0 : ℝ) ≤ c := le_trans zero_le_one hc1
  have hqpos : ∀ i, 0 < q i := fun i => lt_of_lt_of_le hθ (hqθ i)
  have hcsq0 : ∀ i, 0 < 1 - q i ^ 2 :=
    fun i => lt_of_lt_of_le (by positivity) (hκq i)
  have hcpos : ∀ i, 0 < √(1 - q i ^ 2) := fun i => Real.sqrt_pos.mpr (hcsq0 i)
  have hq1 : ∀ i, q i ≤ 1 := by
    intro i
    nlinarith [hcsq0 i, hqpos i]
  have hκc : ∀ i, κ ≤ √(1 - q i ^ 2) := by
    intro i
    have h := Real.sqrt_le_sqrt (hκq i)
    rwa [Real.sqrt_sq hκ.le] at h
  have hx1 : ∀ i, ‖x i‖ = 1 := fun i => hx.norm_eq_one i
  have hε0 : (0 : ℝ) ≤ ρ / 4 := by linarith
  have heig' : ∀ i, ‖Ω.toProj (U.offDiagonalPart Z
      (U.offDiagonalPart Z (x i))) - ((q i ^ 2 : ℝ) : ℂ) • x i‖ ≤ ρ / 4 := by
    intro i
    refine le_trans (heig i) ?_
    have := hq1 i
    nlinarith [hρ]
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hθ2 : (0 : ℝ) < θ ^ 2 := by positivity
  have hκ2 : (0 : ℝ) < κ ^ 2 := by positivity
  have hcS : 1 + (n : ℝ) * (ρ / 4) / θ ^ 2 ≤ c ^ 2 := by
    refine le_trans ?_ hc
    have hnum : (0 : ℝ) ≤ (n : ℝ) * (ρ / 4) := mul_nonneg hn0 hε0
    have hκsq1 : κ ^ 2 ≤ 1 := by nlinarith [hκ.le, hκ1]
    have h1 : (n : ℝ) * (ρ / 4) / θ ^ 2 ≤ 3 * (n : ℝ) * (ρ / 4) / (θ ^ 2 * κ ^ 2) := by
      rw [div_le_div_iff₀ hθ2 (by positivity)]
      nlinarith [mul_nonneg hnum hθ2.le, hκsq1]
    linarith
  have hcC : 1 + (n : ℝ) * (ρ / 4) / κ ^ 2 ≤ c ^ 2 := by
    refine le_trans ?_ hc
    have hnum : (0 : ℝ) ≤ (n : ℝ) * (ρ / 4) := mul_nonneg hn0 hε0
    have hθsq1 : θ ^ 2 ≤ 1 := by nlinarith [hθ.le, hθ1]
    have h1 : (n : ℝ) * (ρ / 4) / κ ^ 2 ≤ 3 * (n : ℝ) * (ρ / 4) / (θ ^ 2 * κ ^ 2) := by
      rw [div_le_div_iff₀ hκ2 (by positivity)]
      nlinarith [mul_nonneg hnum hκ2.le, hθsq1]
    linarith
  have hG0 : (0 : ℝ) ≤ kyFanApproximationGauge n (reflectionResidualCorner U B) := by
    rw [kyFanApproximationGauge, ContinuousLinearMap.kyFanGauge]
    exact Finset.sum_nonneg fun m _ =>
      (reflectionResidualCorner U B).approximationNumber_nonneg m
  have hxU : ∀ i, x i ∈ U := fun i => Ω.mem_subspace_of_eq (hxΩ i)
  have hSU : ∀ i, U.offDiagonalPart Z (x i) ∈ Uᗮ :=
    fun i => TauCeti.offDiagonalPart_mem_orthogonal_of_mem U Z (hxU i)
  have hCSU : ∀ i, U.diagonalPart Z (U.offDiagonalPart Z (x i)) ∈ Uᗮ :=
    fun i => TauCeti.diagonalPart_mem_orthogonal_of_mem_orthogonal U Z (hSU i)
  have hCU : ∀ i, U.diagonalPart Z (x i) ∈ U :=
    fun i => TauCeti.diagonalPart_mem_of_mem U Z (hxU i)
  -- the per-index estimate, divided by `qᵢ cᵢ`
  have hstep : ∀ i, (b - a) * (q i / √(1 - q i ^ 2)) ≤
      (τ + |b|) * ρ / (4 * κ) +
      (RCLike.re ⟪(((q i * √(1 - q i ^ 2)) : ℝ) : ℂ)⁻¹ •
          U.diagonalPart Z (U.offDiagonalPart Z (x i)), B (x i)⟫_ℂ +
        RCLike.re ⟪-(((q i : ℝ) : ℂ)⁻¹ • U.offDiagonalPart Z (x i)),
          B ((((√(1 - q i ^ 2) : ℝ) : ℂ)⁻¹ •
            U.diagonalPart Z (x i)))⟫_ℂ) := by
    intro i
    have hqc : 0 < q i * √(1 - q i ^ 2) := mul_pos (hqpos i) (hcpos i)
    have hqne : q i ≠ 0 := (hqpos i).ne'
    have hcne : √(1 - q i ^ 2) ≠ 0 := (hcpos i).ne'
    have hmain := gap_mul_sq_le_paired_of_approximateDoubleAngleEigenvector hred
      hB hZsa hZdom hZcomm hUa hUb Ω (hxΩ i) (hx1 i) (heig i)
    have hterm1 : RCLike.re ⟪(((q i * √(1 - q i ^ 2)) : ℝ) : ℂ)⁻¹ •
        U.diagonalPart Z (U.offDiagonalPart Z (x i)), B (x i)⟫_ℂ =
        (q i * √(1 - q i ^ 2))⁻¹ *
          RCLike.re ⟪B (x i),
            U.diagonalPart Z (U.offDiagonalPart Z (x i))⟫_ℂ := by
      rw [inner_smul_left, ← Complex.ofReal_inv, Complex.conj_ofReal,
        ← Complex.real_smul, RCLike.smul_re, inner_re_symm]
    have hterm2 : RCLike.re ⟪-(((q i : ℝ) : ℂ)⁻¹ • U.offDiagonalPart Z (x i)),
        B ((((√(1 - q i ^ 2) : ℝ) : ℂ)⁻¹ • U.diagonalPart Z (x i)))⟫_ℂ =
        -((q i * √(1 - q i ^ 2))⁻¹ *
          RCLike.re ⟪B (U.diagonalPart Z (x i)),
            U.offDiagonalPart Z (x i)⟫_ℂ) := by
      rw [mul_inv]
      simp only [map_smul, inner_neg_left, inner_smul_left, inner_smul_right,
        ← Complex.ofReal_inv, Complex.conj_ofReal]
      rw [mul_neg, ← mul_assoc, ← Complex.ofReal_mul, ← Complex.real_smul,
        map_neg, RCLike.smul_re, inner_re_symm]
      ring
    rw [hterm1, hterm2]
    set P1 : ℝ := RCLike.re ⟪B (x i),
      U.diagonalPart Z (U.offDiagonalPart Z (x i))⟫_ℂ with hP1def
    set P2 : ℝ := RCLike.re ⟪B (U.diagonalPart Z (x i)),
      U.offDiagonalPart Z (x i)⟫_ℂ with hP2def
    have hinv0 : (0 : ℝ) ≤ (q i * √(1 - q i ^ 2))⁻¹ := le_of_lt (inv_pos.mpr hqc)
    have hmul := mul_le_mul_of_nonneg_left hmain hinv0
    have hexpand : (q i * √(1 - q i ^ 2))⁻¹ *
        ((τ + |b|) * (ρ * q i / 4) + (P1 - P2)) =
        (q i * √(1 - q i ^ 2))⁻¹ * ((τ + |b|) * (ρ * q i / 4)) +
          ((q i * √(1 - q i ^ 2))⁻¹ * P1 -
            (q i * √(1 - q i ^ 2))⁻¹ * P2) := by ring
    rw [hexpand] at hmul
    have hdiv : (b - a) * (q i / √(1 - q i ^ 2)) =
        (q i * √(1 - q i ^ 2))⁻¹ * ((b - a) * q i ^ 2) := by
      field_simp
    have herr : (q i * √(1 - q i ^ 2))⁻¹ * ((τ + |b|) * (ρ * q i / 4)) ≤
        (τ + |b|) * ρ / (4 * κ) := by
      have heq : (q i * √(1 - q i ^ 2))⁻¹ * ((τ + |b|) * (ρ * q i / 4)) =
          (τ + |b|) * ρ / (4 * √(1 - q i ^ 2)) := by
        field_simp
      rw [heq]
      have hnum : (0 : ℝ) ≤ (τ + |b|) * ρ :=
        mul_nonneg (by positivity) hρ
      gcongr
      exact hκc i
    rw [hdiv]
    linarith [hmul, herr]
  have hsum1 : ∑ i, RCLike.re ⟪(((q i * √(1 - q i ^ 2)) : ℝ) : ℂ)⁻¹ •
      U.diagonalPart Z (U.offDiagonalPart Z (x i)), B (x i)⟫_ℂ ≤
      c * 1 * kyFanApproximationGauge n (reflectionResidualCorner U B) :=
    sum_le_kyFanApproximationGauge_reflectionResidualCorner_of_contraction B
      hc0' zero_le_one
      (fun i => Uᗮ.smul_mem _ (hCSU i)) hxU
      (sq_norm_sum_smul_diagonalPart_offDiagonalPart_le_of_approximate hZsa hZ2 Ω
        hx hxΩ hε0 hθ hκ hqθ hκq heig' hc)
      (fun α => sq_norm_sum_smul_le_of_orthonormal hx (le_refl (1 : ℝ)) α)
      (fun _ => le_rfl)
  have hsum2 : ∑ i, RCLike.re ⟪-(((q i : ℝ) : ℂ)⁻¹ • U.offDiagonalPart Z (x i)),
      B ((((√(1 - q i ^ 2) : ℝ) : ℂ)⁻¹ • U.diagonalPart Z (x i)))⟫_ℂ ≤
      c * c * kyFanApproximationGauge n (reflectionResidualCorner U B) :=
    sum_le_kyFanApproximationGauge_reflectionResidualCorner_of_contraction B
      hc0' hc0'
      (fun i => Uᗮ.neg_mem (Uᗮ.smul_mem _ (hSU i)))
      (fun i => U.smul_mem _ (hCU i))
      (sq_norm_sum_smul_offDiagonalPart_le_of_approximate hZsa Ω hx hxΩ hε0 hθ
        hqθ heig' hcS)
      (sq_norm_sum_smul_diagonalPart_le_of_approximate hZsa hZ2 Ω hx hxΩ hε0 hκ
        hκq heig' hcC)
      (fun _ => le_rfl)
  calc (b - a) * ∑ i, q i / √(1 - q i ^ 2)
      = ∑ i, (b - a) * (q i / √(1 - q i ^ 2)) := by rw [Finset.mul_sum]
    _ ≤ ∑ i, ((τ + |b|) * ρ / (4 * κ) +
        (RCLike.re ⟪(((q i * √(1 - q i ^ 2)) : ℝ) : ℂ)⁻¹ •
            U.diagonalPart Z (U.offDiagonalPart Z (x i)), B (x i)⟫_ℂ +
          RCLike.re ⟪-(((q i : ℝ) : ℂ)⁻¹ • U.offDiagonalPart Z (x i)),
            B ((((√(1 - q i ^ 2) : ℝ) : ℂ)⁻¹ •
              U.diagonalPart Z (x i)))⟫_ℂ)) :=
        Finset.sum_le_sum fun i _ => hstep i
    _ = (n : ℝ) * ((τ + |b|) * ρ / (4 * κ)) +
        ((∑ i, RCLike.re ⟪(((q i * √(1 - q i ^ 2)) : ℝ) : ℂ)⁻¹ •
            U.diagonalPart Z (U.offDiagonalPart Z (x i)), B (x i)⟫_ℂ) +
          ∑ i, RCLike.re ⟪-(((q i : ℝ) : ℂ)⁻¹ • U.offDiagonalPart Z (x i)),
            B ((((√(1 - q i ^ 2) : ℝ) : ℂ)⁻¹ •
              U.diagonalPart Z (x i)))⟫_ℂ) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ 2 * c ^ 2 * kyFanApproximationGauge n (reflectionResidualCorner U B) +
        (n : ℝ) * ((τ + |b|) * ρ / (4 * κ)) := by
        have hcsq : c ≤ c ^ 2 := by nlinarith [hc1]
        have hcc : c * kyFanApproximationGauge n (reflectionResidualCorner U B) ≤
            c ^ 2 * kyFanApproximationGauge n (reflectionResidualCorner U B) :=
          mul_le_mul_of_nonneg_right hcsq hG0
        nlinarith [hsum1, hsum2, hcc]

/-! ### Checkpoint C3: the passages `ρ → 0` at fixed `τ`, then `θ → 0` -/

/-- The compressed cutoff is a contraction.  Needed to see that composing with
the cutoff cannot push the sine corner's approximation numbers up to the pole. -/
theorem norm_cutoffCorner_le (Ω : TauCeti.BoundedCutoff A U τ) :
    ‖cutoffCorner Ω‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => ?_
  have hcoe : ‖cutoffCorner Ω y‖ = ‖Ω.toProj ((y : U) : H)‖ := by
    rw [← coe_cutoffCorner_apply Ω y]
    rfl
  rw [hcoe, one_mul]
  exact Ω.norm_toProj_apply_le _

/-- **The Gram operator of the cutoff-composed sine corner, in the ambient
space.**  At a vector fixed by the compressed cutoff it is `Ω S² ·`, which is
exactly the object the approximate Section-7 estimates are stated about. -/
theorem coe_gramOperator_reflectionSineCorner_comp_cutoffCorner_apply
    (hZsa : IsSelfAdjoint Z) (Ω : TauCeti.BoundedCutoff A U τ) {y : U}
    (hy : cutoffCorner Ω y = y) :
    ((gramOperator (reflectionSineCorner U Z ∘L cutoffCorner Ω) y : U) : H) =
      Ω.toProj (U.offDiagonalPart Z (U.offDiagonalPart Z ((y : U) : H))) := by
  have hadj : (reflectionSineCorner U Z ∘L cutoffCorner Ω).adjoint =
      cutoffCorner Ω ∘L (reflectionSineCorner U Z).adjoint := by
    rw [ContinuousLinearMap.adjoint_comp,
      (isSelfAdjoint_cutoffCorner Ω).adjoint_eq]
  have h1 : gramOperator (reflectionSineCorner U Z ∘L cutoffCorner Ω) y =
      cutoffCorner Ω (gramOperator (reflectionSineCorner U Z) y) := by
    simp only [gramOperator, ContinuousLinearMap.comp_apply, hy, hadj]
  rw [h1, coe_cutoffCorner_apply,
    coe_gramOperator_reflectionSineCorner_apply hZsa]
private theorem gramSpectralBandModel_ambient_residual
    (hZsa : IsSelfAdjoint Z) (Ω : TauCeti.BoundedCutoff A U τ) {k : ℕ} {ρ : ℝ}
    (M : TauCeti.DavisKahan.GramSpectralBandModel
      (reflectionSineCorner U Z ∘L cutoffCorner Ω) k ρ) (j : Fin M.count) :
    let X := reflectionSineCorner U Z ∘L cutoffCorner Ω
    let q : ℝ := X.approximationNumber (j : ℕ)
    let y : H := ((M.right j : U) : H)
    ‖Ω.toProj (U.offDiagonalPart Z (U.offDiagonalPart Z y)) -
      ((q ^ 2 : ℝ) : ℂ) • y‖ ≤ ρ * q / 4 := by
  let X := reflectionSineCorner U Z ∘L cutoffCorner Ω
  let q : ℝ := X.approximationNumber (j : ℕ)
  let y : H := ((M.right j : U) : H)
  have hfix : cutoffCorner Ω (M.right j) = M.right j :=
    eq_of_mem_polarInitial_comp (isSelfAdjoint_cutoffCorner Ω)
      (isIdempotentElem_cutoffCorner Ω) (reflectionSineCorner U Z)
      (M.right_mem_polarInitial j)
  have hgram := coe_gramOperator_reflectionSineCorner_comp_cutoffCorner_apply hZsa Ω hfix
  have hcoe : (((gramOperator X (M.right j) -
      ((q : ℂ)) ^ 2 • M.right j) : U) : H) =
      Ω.toProj (U.offDiagonalPart Z (U.offDiagonalPart Z y)) -
        ((q ^ 2 : ℝ) : ℂ) • y := by
    rw [Submodule.coe_sub, Submodule.coe_smul, hgram]
    norm_cast
  have hnorm : ‖gramOperator X (M.right j) - ((q : ℂ)) ^ 2 • M.right j‖ =
      ‖Ω.toProj (U.offDiagonalPart Z (U.offDiagonalPart Z y)) -
        ((q ^ 2 : ℝ) : ℂ) • y‖ := by
    rw [← hcoe]
    rfl
  change ‖Ω.toProj (U.offDiagonalPart Z (U.offDiagonalPart Z y)) -
    ((q ^ 2 : ℝ) : ℂ) • y‖ ≤ ρ * q / 4
  rw [← hnorm]
  exact M.gram_residual j

private theorem sum_tanArcsin_le_of_retained_bound
    (α : ℕ → ℝ) (m k : ℕ) (a b τ θ κ ρ c gm g : ℝ)
    (hmk : m ≤ k) (hδ : 0 < b - a) (hτ : 0 ≤ τ)
    (hθ : 0 < θ) (hθ1 : θ < 1) (hκ : 0 < κ)
    (hρ : 0 < ρ) (hρdef : ρ = θ ^ 4) (hρθ : ρ ≤ θ)
    (ha0 : ∀ p, 0 ≤ α p)
    (hdenominator : ∀ p, κ ≤ √(1 - α p ^ 2))
    (hleading : ∀ p, m ≤ p → p < k → α p ≤ θ)
    (hcsq : c ^ 2 = 1 + 3 * (k : ℝ) * (ρ / 4) / (θ ^ 2 * κ ^ 2))
    (hG0 : 0 ≤ g) (hGm : gm ≤ g)
    (hmain : (b - a) * ∑ p ∈ Finset.range m, Real.tan (Real.arcsin (α p)) ≤
      2 * c ^ 2 * gm + (m : ℝ) * ((τ + |b|) * ρ / (4 * κ))) :
    (b - a) * ∑ p ∈ Finset.range k, Real.tan (Real.arcsin (α p)) ≤
      2 * g + θ * (3 * k * g / (2 * κ ^ 2) +
        k * (τ + |b|) / (4 * κ) + (b - a) * k / κ) := by
  -- the dropped tail
  have htail : ∑ p ∈ Finset.Ico m k, Real.tan (Real.arcsin
      (α p)) ≤ (k : ℝ) * (θ / κ) := by
    have hbd : ∀ p ∈ Finset.Ico m k, Real.tan (Real.arcsin
        (α p)) ≤ θ / κ := by
      intro p hp
      obtain ⟨hp1, hp2⟩ := Finset.mem_Ico.mp hp
      have hle : α p ≤ θ :=
        hleading p hp1 hp2
      rw [Real.tan_arcsin]
      have hden : κ ≤ √(1 - α p ^ 2) :=
        hdenominator p
      have hden0 : 0 < √(1 - α p ^ 2) := lt_of_lt_of_le hκ hden
      rw [div_le_div_iff₀ hden0 hκ]
      nlinarith [ha0 p, hκ.le, hden]
    calc ∑ p ∈ Finset.Ico m k, Real.tan (Real.arcsin
          (α p)) ≤ ∑ _p ∈ Finset.Ico m k, θ / κ :=
          Finset.sum_le_sum hbd
      _ = (k - m : ℕ) * (θ / κ) := by
          rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
      _ ≤ (k : ℝ) * (θ / κ) := by
          have h1 : ((k - m : ℕ) : ℝ) ≤ (k : ℝ) := by
            exact_mod_cast Nat.sub_le k m
          have h2 : (0 : ℝ) ≤ θ / κ := by positivity
          exact mul_le_mul_of_nonneg_right h1 h2
  have hsplit : ∑ p ∈ Finset.range k, Real.tan (Real.arcsin
      (α p)) =
      (∑ p ∈ Finset.range m, Real.tan (Real.arcsin
        (α p))) +
      ∑ p ∈ Finset.Ico m k, Real.tan (Real.arcsin
        (α p)) :=
    (Finset.sum_range_add_sum_Ico
      (f := fun p => Real.tan (Real.arcsin (α p))) hmk).symm
  -- assemble
  have hmkR : (m : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hmk
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hcsq0 : (0 : ℝ) ≤ c ^ 2 := sq_nonneg c
  have hstep1 : 2 * c ^ 2 * gm +
      (m : ℝ) * ((τ + |b|) * ρ / (4 * κ)) ≤
      2 * g +
        (3 * (k : ℝ) * ρ / (2 * θ ^ 2 * κ ^ 2)) *
          g +
        (k : ℝ) * ((τ + |b|) * ρ / (4 * κ)) := by
    have h1 : 2 * c ^ 2 * gm ≤
        2 * c ^ 2 * g := by
      have : (0 : ℝ) ≤ 2 * c ^ 2 := by positivity
      exact mul_le_mul_of_nonneg_left hGm this
    have h2 : 2 * c ^ 2 * g =
        2 * g +
          (3 * (k : ℝ) * ρ / (2 * θ ^ 2 * κ ^ 2)) *
            g := by
      rw [hcsq]
      field_simp
      ring
    have h3 : (0 : ℝ) ≤ (τ + |b|) * ρ / (4 * κ) := by
      have hnn : (0 : ℝ) ≤ τ + |b| := by positivity
      positivity
    have hmE : (m : ℝ) * ((τ + |b|) * ρ / (4 * κ)) ≤
        (k : ℝ) * ((τ + |b|) * ρ / (4 * κ)) :=
      mul_le_mul_of_nonneg_right hmkR h3
    linarith [h1, h2, hmE]
  rw [hsplit, mul_add]
  have hfinal : (b - a) * ∑ p ∈ Finset.Ico m k, Real.tan (Real.arcsin
      (α p)) ≤ (b - a) * ((k : ℝ) * (θ / κ)) :=
    mul_le_mul_of_nonneg_left htail hδ.le
  have hθ4 : ρ ≤ θ := hρθ
  have hθ2θ : θ ^ 2 ≤ θ := by nlinarith [hθ, hθ1]
  have hκ2pos : (0 : ℝ) < κ ^ 2 := by positivity
  have hE1 : (3 * (k : ℝ) * ρ / (2 * θ ^ 2 * κ ^ 2)) *
      g ≤
      θ * (3 * (k : ℝ) * g / (2 * κ ^ 2)) := by
    have hid : (3 * (k : ℝ) * ρ / (2 * θ ^ 2 * κ ^ 2)) *
        g =
        θ ^ 2 * (3 * (k : ℝ) * g / (2 * κ ^ 2)) := by
      rw [hρdef]
      field_simp
    rw [hid]
    have hcoef : (0 : ℝ) ≤ 3 * (k : ℝ) * g /
        (2 * κ ^ 2) := by positivity
    exact mul_le_mul_of_nonneg_right hθ2θ hcoef
  have hE2 : (k : ℝ) * ((τ + |b|) * ρ / (4 * κ)) ≤
      θ * ((k : ℝ) * (τ + |b|) / (4 * κ)) := by
    have hcoef : (0 : ℝ) ≤ (k : ℝ) * (τ + |b|) / (4 * κ) := by
      have : (0 : ℝ) ≤ τ + |b| := by positivity
      positivity
    have hid : (k : ℝ) * ((τ + |b|) * ρ / (4 * κ)) =
        ρ * ((k : ℝ) * (τ + |b|) / (4 * κ)) := by
      field_simp
    rw [hid]
    exact mul_le_mul_of_nonneg_right hθ4 hcoef
  have hE3 : (b - a) * ((k : ℝ) * (θ / κ)) = θ * ((b - a) * (k : ℝ) / κ) := by
    field_simp
  rw [mul_add]
  linarith [hmain, hstep1, hfinal, hE1, hE2, hE3.le, hE3.ge]


/-- **The fixed-cutoff middle inequality, with an explicit `θ`-error.**

For every threshold `θ ∈ (0, 1)`, taking the Gram-band radius `ρ := θ⁴` gives

`δ ∑_{n<k} tan (arcsin aₙ(S₀ ∘ Ω)) ≤ 2 · kyFan k R + θ · M`,

where `M` is a constant free of `θ` and `ρ`.  All three errors — the contraction
slack `3kθ²/(2κ²) · kyFan k R`, the unbounded-`A` error `k(τ+|b|)θ⁴/(4κ)` and
the dropped tail `δkθ/κ` — are bounded by `θ` times a `θ`-free constant, so the
single passage `θ → 0` releases all of them at once.

The `τ` in `M` is multiplied by `θ⁴`, never by a cutoff error that grows with
`τ`: this is the ordering that distinguishes the route from the spectral-cutoff
lane. -/
theorem gap_mul_sum_tanArcsin_le_two_mul_kyFan_add_of_cutoff
    (hred : TauCeti.LinearPMap.ReducesSubspace A U) (hB : TauCeti.IsOddFor U B)
    (hZsa : IsSelfAdjoint Z) (hZ2 : Z * Z = 1)
    (hZdom : TauCeti.LinearPMap.MapsDomainTo A A Z)
    (hZcomm : ∀ x : A.domain,
      A ⟨Z (x : H), hZdom x⟩ + B (Z (x : H)) = Z (A x) + Z (B (x : H)))
    (hUa : ∀ x : A.domain, (x : H) ∈ U →
      RCLike.re ⟪A x, (x : H)⟫_ℂ ≤ a * ‖(x : H)‖ ^ 2)
    (hUb : ∀ x : A.domain, (x : H) ∈ Uᗮ →
      b * ‖(x : H)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : H)⟫_ℂ)
    (hab : a < b) (hS1 : ‖U.offDiagonalPart Z‖ < 1)
    (hτ : 0 ≤ τ) (Ω : TauCeti.BoundedCutoff A U τ) (k : ℕ)
    {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) :
    (b - a) * ∑ p ∈ Finset.range k, Real.tan (Real.arcsin
        ((reflectionSineCorner U Z ∘L cutoffCorner Ω).approximationNumber p)) ≤
      2 * kyFanApproximationGauge k (reflectionResidualCorner U B) +
        θ * (3 * k * kyFanApproximationGauge k (reflectionResidualCorner U B) /
              (2 * (√(1 - ‖U.offDiagonalPart Z‖ ^ 2)) ^ 2) +
            k * (τ + |b|) / (4 * √(1 - ‖U.offDiagonalPart Z‖ ^ 2)) +
            (b - a) * k / √(1 - ‖U.offDiagonalPart Z‖ ^ 2)) := by
  classical
  set X : U →L[ℂ] Uᗮ := reflectionSineCorner U Z ∘L cutoffCorner Ω with hXdef
  set r : ℝ := ‖U.offDiagonalPart Z‖ with hrdef
  have hr0 : 0 ≤ r := norm_nonneg _
  have hrsq : r ^ 2 < 1 := by nlinarith
  set κ : ℝ := √(1 - r ^ 2) with hκdef
  have hκ : 0 < κ := Real.sqrt_pos.mpr (by linarith)
  have hκsq : κ ^ 2 = 1 - r ^ 2 := Real.sq_sqrt (by linarith)
  have hκ1 : κ ≤ 1 := by nlinarith [hκ, hκsq, sq_nonneg r]
  have hδ : 0 < b - a := by linarith
  set ρ : ℝ := θ ^ 4 with hρdef
  have hρ : 0 < ρ := by positivity
  have hρθ : ρ < θ := by
    have h3 : θ ^ 3 < 1 := pow_lt_one₀ hθ.le hθ1 (by norm_num)
    have h4 : θ ^ 4 = θ * θ ^ 3 := by ring
    rw [hρdef, h4]
    nlinarith [hθ, h3]
  -- the cutoff cannot move the singular values towards the pole
  have hXnorm : ‖X‖ ≤ r := by
    refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
    have h1 := norm_reflectionSineCorner_le (U := U) (Z := Z)
    have h2 := norm_cutoffCorner_le Ω
    nlinarith [norm_nonneg (reflectionSineCorner U Z),
      norm_nonneg (cutoffCorner Ω)]
  have har : ∀ p, X.approximationNumber p ≤ r :=
    fun p => le_trans (X.approximationNumber_le_norm p) hXnorm
  have ha0 : ∀ p, 0 ≤ X.approximationNumber p :=
    fun p => X.approximationNumber_nonneg p
  have htan : ∀ s : ℝ, 0 ≤ s → s ≤ r →
      Real.tan (Real.arcsin s) = s / √(1 - s ^ 2) := fun s _ _ =>
    Real.tan_arcsin s
  have hcκ : ∀ s : ℝ, 0 ≤ s → s ≤ r → κ ≤ √(1 - s ^ 2) := by
    intro s hs0 hsr
    refine Real.sqrt_le_sqrt ?_
    nlinarith
  -- the Gram band model at radius `ρ`
  obtain ⟨M⟩ := TauCeti.DavisKahan.exists_gramSpectralBandModel X k hρ
  set m : ℕ := leadingCount X k θ with hmdef
  have hmk : m ≤ k := leadingCount_le X k θ
  have hmc : m ≤ M.count := by
    rcases Nat.lt_or_ge M.count m with hlt | hle
    swap
    · exact hle
    · exfalso
      have h1 : θ < X.approximationNumber M.count :=
        approximationNumber_gt_of_lt_leadingCount X k θ hlt
      have h2 : X.approximationNumber M.count ≤ ρ :=
        M.tail_small M.count le_rfl (lt_of_lt_of_le hlt hmk)
      linarith
  set y : Fin m → H := fun j => ((M.right (Fin.castLE hmc j) : U) : H) with hydef
  set q : Fin m → ℝ := fun j => X.approximationNumber (j : ℕ) with hqdef
  have hyon : Orthonormal ℂ y := by
    have hon0 : Orthonormal ℂ (fun j : Fin m => M.right (Fin.castLE hmc j)) :=
      M.right_orthonormal.comp _ (Fin.castLE_injective hmc)
    rw [orthonormal_iff_ite] at hon0 ⊢
    intro i j
    simpa [hydef, Submodule.coe_inner] using hon0 i j
  have hyΩ : ∀ j, Ω.toProj (y j) = y j := fun j =>
    gramSpectralBandModel_toProj_right Ω M (Fin.castLE hmc j)
  have hqθ : ∀ j : Fin m, θ ≤ q j := fun j =>
    le_of_lt (approximationNumber_gt_of_lt_leadingCount X k θ j.isLt)
  have hκq : ∀ j : Fin m, κ ^ 2 ≤ 1 - q j ^ 2 := by
    intro j
    have h := har (j : ℕ)
    have h0 := ha0 (j : ℕ)
    rw [hκsq]
    nlinarith
  have heig : ∀ j : Fin m,
      ‖Ω.toProj (U.offDiagonalPart Z (U.offDiagonalPart Z (y j))) -
        ((q j ^ 2 : ℝ) : ℂ) • y j‖ ≤ ρ * q j / 4 :=
    fun j => gramSpectralBandModel_ambient_residual hZsa Ω M (Fin.castLE hmc j)
  -- the summed estimate at the retained indices
  set c : ℝ := √(1 + 3 * (k : ℝ) * (ρ / 4) / (θ ^ 2 * κ ^ 2)) with hcdef
  have hcarg : (0 : ℝ) ≤ 1 + 3 * (k : ℝ) * (ρ / 4) / (θ ^ 2 * κ ^ 2) := by
    have : (0 : ℝ) ≤ 3 * (k : ℝ) * (ρ / 4) / (θ ^ 2 * κ ^ 2) := by positivity
    linarith
  have hcsq : c ^ 2 = 1 + 3 * (k : ℝ) * (ρ / 4) / (θ ^ 2 * κ ^ 2) :=
    Real.sq_sqrt hcarg
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have hA1 : (1 : ℝ) ≤ 1 + 3 * (k : ℝ) * (ρ / 4) / (θ ^ 2 * κ ^ 2) := by
    have hnn : (0 : ℝ) ≤ 3 * (k : ℝ) * (ρ / 4) / (θ ^ 2 * κ ^ 2) := by positivity
    linarith
  have hc1 : 1 ≤ c := by nlinarith [hcsq, hc0, hA1]
  have hcm : 1 + 3 * (m : ℝ) * (ρ / 4) / (θ ^ 2 * κ ^ 2) ≤ c ^ 2 := by
    rw [hcsq]
    have hmkR : (m : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hmk
    have hden : (0 : ℝ) < θ ^ 2 * κ ^ 2 := by positivity
    have hnum : 3 * (m : ℝ) * (ρ / 4) ≤ 3 * (k : ℝ) * (ρ / 4) := by
      nlinarith [hρ.le]
    have hdiv : 3 * (m : ℝ) * (ρ / 4) / (θ ^ 2 * κ ^ 2) ≤
        3 * (k : ℝ) * (ρ / 4) / (θ ^ 2 * κ ^ 2) := by
      rw [div_le_div_iff₀ hden hden]
      nlinarith [hnum, hden]
    linarith
  have hmain := gap_mul_sum_tangent_le_kyFan_of_approximateDoubleAngleEigenfamily
    hred hB hZsa hZ2 hZdom hZcomm hUa hUb hτ Ω hyon hyΩ hρ.le hθ hθ1.le hκ hκ1
    hqθ hκq heig hc1 hcm
  -- the retained prefix, as a sum over `Finset.range m`
  have hretained : ∑ p ∈ Finset.range m, Real.tan (Real.arcsin
      (X.approximationNumber p)) = ∑ j : Fin m, q j / √(1 - q j ^ 2) := by
    rw [← Fin.sum_univ_eq_sum_range
      (fun p => Real.tan (Real.arcsin (X.approximationNumber p))) m]
    exact Finset.sum_congr rfl fun j _ => Real.tan_arcsin _
  have hG0 : (0 : ℝ) ≤ kyFanApproximationGauge k (reflectionResidualCorner U B) := by
    rw [kyFanApproximationGauge, ContinuousLinearMap.kyFanGauge]
    exact Finset.sum_nonneg fun p _ =>
      (reflectionResidualCorner U B).approximationNumber_nonneg p
  have hGm := TauCeti.DavisKahan.kyFanApproximationGauge_mono_length
    (reflectionResidualCorner U B) hmk
  rw [← hretained] at hmain
  exact sum_tanArcsin_le_of_retained_bound
    (fun p => X.approximationNumber p) m k a b τ θ κ ρ c
    (kyFanApproximationGauge m (reflectionResidualCorner U B))
    (kyFanApproximationGauge k (reflectionResidualCorner U B))
    hmk hδ hτ hθ hθ1 hκ hρ hρdef hρθ.le ha0
    (fun p => hcκ _ (ha0 p) (har p))
    (fun p hp1 hp2 => approximationNumber_le_of_leadingCount_le X k θ hp1 hp2)
    hcsq hG0 hGm hmain

/-- **The fixed-cutoff middle inequality.**

`δ ∑_{n<k} tan (arcsin aₙ(S₀ ∘ Ω)) ≤ 2 · kyFan k R`, with **no extremality
hypothesis, no eigenbasis and no attainment clause**, at every bounded cutoff
`Ω` of every level `τ` and every prefix length `k`.

This is the `θ → 0` passage of the previous theorem.  Note what has disappeared
from the bound: the cutoff level `τ`, the Gram-band radius `ρ` and the retention
threshold `θ`.  That is what makes the cutoff net of the next theorem
unconstrained. -/
theorem gap_mul_sum_tanArcsin_le_two_mul_kyFan_of_cutoff
    (hred : TauCeti.LinearPMap.ReducesSubspace A U) (hB : TauCeti.IsOddFor U B)
    (hZsa : IsSelfAdjoint Z) (hZ2 : Z * Z = 1)
    (hZdom : TauCeti.LinearPMap.MapsDomainTo A A Z)
    (hZcomm : ∀ x : A.domain,
      A ⟨Z (x : H), hZdom x⟩ + B (Z (x : H)) = Z (A x) + Z (B (x : H)))
    (hUa : ∀ x : A.domain, (x : H) ∈ U →
      RCLike.re ⟪A x, (x : H)⟫_ℂ ≤ a * ‖(x : H)‖ ^ 2)
    (hUb : ∀ x : A.domain, (x : H) ∈ Uᗮ →
      b * ‖(x : H)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : H)⟫_ℂ)
    (hab : a < b) (hS1 : ‖U.offDiagonalPart Z‖ < 1)
    (hτ : 0 ≤ τ) (Ω : TauCeti.BoundedCutoff A U τ) (k : ℕ) :
    (b - a) * ∑ p ∈ Finset.range k, Real.tan (Real.arcsin
        ((reflectionSineCorner U Z ∘L cutoffCorner Ω).approximationNumber p)) ≤
      2 * kyFanApproximationGauge k (reflectionResidualCorner U B) := by
  classical
  set r : ℝ := ‖U.offDiagonalPart Z‖ with hrdef
  have hr0 : 0 ≤ r := norm_nonneg _
  have hrsq : r ^ 2 < 1 := by nlinarith
  set κ : ℝ := √(1 - r ^ 2) with hκdef
  have hκ : 0 < κ := Real.sqrt_pos.mpr (by linarith)
  have hδ : 0 < b - a := by linarith
  have hG0 : (0 : ℝ) ≤ kyFanApproximationGauge k (reflectionResidualCorner U B) := by
    rw [kyFanApproximationGauge, ContinuousLinearMap.kyFanGauge]
    exact Finset.sum_nonneg fun p _ =>
      (reflectionResidualCorner U B).approximationNumber_nonneg p
  set W : ℝ := 3 * (k : ℝ) * kyFanApproximationGauge k (reflectionResidualCorner U B) / (2 * κ ^ 2) +
      (k : ℝ) * (τ + |b|) / (4 * κ) + (b - a) * (k : ℝ) / κ with hWdef
  have hW0 : (0 : ℝ) ≤ W := by
    have h1 : (0 : ℝ) ≤ 3 * (k : ℝ) * kyFanApproximationGauge k (reflectionResidualCorner U B) /
        (2 * κ ^ 2) := by positivity
    have hbb : (0 : ℝ) ≤ τ + |b| := by positivity
    have h2 : (0 : ℝ) ≤ (k : ℝ) * (τ + |b|) / (4 * κ) := by positivity
    have h3 : (0 : ℝ) ≤ (b - a) * (k : ℝ) / κ := by positivity
    rw [hWdef]
    linarith
  refine le_of_forall_pos_le_add fun η hη => ?_
  set θ : ℝ := min (1 / 2) (η / (W + 1)) with hθdef
  have hW1 : (0 : ℝ) < W + 1 := by linarith
  have hθpos : 0 < θ := by
    rw [hθdef]
    exact lt_min (by norm_num) (by positivity)
  have hθ1 : θ < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hθW : θ * W ≤ η := by
    have hle : θ ≤ η / (W + 1) := min_le_right _ _
    have h1 : θ * W ≤ (η / (W + 1)) * W :=
      mul_le_mul_of_nonneg_right hle hW0
    have h2 : (η / (W + 1)) * W ≤ η := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hW1]
      nlinarith [hη.le, hW0]
    linarith
  have hmain := gap_mul_sum_tanArcsin_le_two_mul_kyFan_add_of_cutoff hred hB hZsa
    hZ2 hZdom hZcomm hUa hUb hab hS1 hτ Ω k hθpos hθ1
  rw [← hrdef, ← hκdef] at hmain
  have hWeq : 3 * (k : ℝ) * kyFanApproximationGauge k (reflectionResidualCorner U B) / (2 * κ ^ 2) +
      (k : ℝ) * (τ + |b|) / (4 * κ) + (b - a) * (k : ℝ) / κ = W := hWdef.symm
  rw [hWeq] at hmain
  linarith [hmain, hθW]

/-- **The middle inequality on the full trial subspace.**

Releasing the cutoff.  Given *any* net of bounded cutoffs — of *unrestricted*
levels `σ i`, since the bound of the previous theorem contains no `τ` — whose
compressed corners are orthogonal projections increasing strongly to the
identity of `U`, the fixed-cutoff bound passes to the limit. -/
theorem gap_mul_sum_tanArcsin_le_two_mul_kyFan
    (hred : TauCeti.LinearPMap.ReducesSubspace A U) (hB : TauCeti.IsOddFor U B)
    (hZsa : IsSelfAdjoint Z) (hZ2 : Z * Z = 1)
    (hZdom : TauCeti.LinearPMap.MapsDomainTo A A Z)
    (hZcomm : ∀ x : A.domain,
      A ⟨Z (x : H), hZdom x⟩ + B (Z (x : H)) = Z (A x) + Z (B (x : H)))
    (hUa : ∀ x : A.domain, (x : H) ∈ U →
      RCLike.re ⟪A x, (x : H)⟫_ℂ ≤ a * ‖(x : H)‖ ^ 2)
    (hUb : ∀ x : A.domain, (x : H) ∈ Uᗮ →
      b * ‖(x : H)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : H)⟫_ℂ)
    (hab : a < b) (hS1 : ‖U.offDiagonalPart Z‖ < 1)
    {ι : Type*} {l : Filter ι} [l.NeBot] {σ : ι → ℝ} (hσ : ∀ i, 0 ≤ σ i)
    (Ω : ∀ i, TauCeti.BoundedCutoff A U (σ i))
    (hproj : ∀ i, TauCeti.ApproximationNumber.IsOrthogonalProjectionMap
      (cutoffCorner (Ω i)))
    (hstrong : TauCeti.ApproximationNumber.StronglyTendsto
      (fun i => cutoffCorner (Ω i)) l (ContinuousLinearMap.id ℂ U))
    (k : ℕ) :
    (b - a) * ∑ p ∈ Finset.range k, Real.tan (Real.arcsin
        ((reflectionSineCorner U Z).approximationNumber p)) ≤
      2 * kyFanApproximationGauge k (reflectionResidualCorner U B) := by
  have hlim :=
    (tendsto_sum_tanArcsin_approximationNumber_reflectionSineCorner_comp hS1
      hproj hstrong k).const_mul (b - a)
  refine le_of_tendsto hlim (Filter.Eventually.of_forall fun i => ?_)
  exact gap_mul_sum_tanArcsin_le_two_mul_kyFan_of_cutoff hred hB hZsa hZ2 hZdom
    hZcomm hUa hUb hab hS1 (hσ i) (Ω i) k

/-- **The unbounded, residual-form `tan 2Θ` theorem at every Ky Fan prefix, with
no extremality hypothesis.**

`δ · kyFan k T₀ ≤ 2 · kyFan k R` on the typed directed corners, for every prefix
length `k`.

This is the target chain of `TanTwoThetaUnboundedGramBridge.lean` closed:
`kyFan_reflectionTangentCorner_le` is the left half and
`gap_mul_sum_tanArcsin_le_two_mul_kyFan` is the middle inequality.  Neither
`IsCompressedDoubleAngleEigenbasis` nor any other attainment condition occurs in
the hypotheses or in the dependency closure.

The compressed cutoffs are *not* asked to be orthogonal projections:
`isOrthogonalProjectionMap_cutoffCorner` proves that for every `BoundedCutoff`,
so the hypothesis this endpoint used to carry was redundant and is discharged
internally. -/
theorem gap_mul_kyFan_reflectionTangentCorner_le_two_mul_kyFan
    (hred : TauCeti.LinearPMap.ReducesSubspace A U) (hB : TauCeti.IsOddFor U B)
    (hZsa : IsSelfAdjoint Z) (hZ2 : Z * Z = 1)
    (hZdom : TauCeti.LinearPMap.MapsDomainTo A A Z)
    (hZcomm : ∀ x : A.domain,
      A ⟨Z (x : H), hZdom x⟩ + B (Z (x : H)) = Z (A x) + Z (B (x : H)))
    (hUa : ∀ x : A.domain, (x : H) ∈ U →
      RCLike.re ⟪A x, (x : H)⟫_ℂ ≤ a * ‖(x : H)‖ ^ 2)
    (hUb : ∀ x : A.domain, (x : H) ∈ Uᗮ →
      b * ‖(x : H)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : H)⟫_ℂ)
    (hab : a < b) (hS1 : ‖U.offDiagonalPart Z‖ < 1)
    {ι : Type*} {l : Filter ι} [l.NeBot] {σ : ι → ℝ} (hσ : ∀ i, 0 ≤ σ i)
    (Ω : ∀ i, TauCeti.BoundedCutoff A U (σ i))
    (hstrong : TauCeti.ApproximationNumber.StronglyTendsto
      (fun i => cutoffCorner (Ω i)) l (ContinuousLinearMap.id ℂ U))
    (k : ℕ) :
    (b - a) * kyFanApproximationGauge k (reflectionTangentCorner U Z) ≤
      2 * kyFanApproximationGauge k (reflectionResidualCorner U B) := by
  have hleft := kyFan_reflectionTangentCorner_le hZsa hZ2 hS1 k
  have hmid := gap_mul_sum_tanArcsin_le_two_mul_kyFan hred hB hZsa hZ2 hZdom
    hZcomm hUa hUb hab hS1 hσ Ω (fun i => isOrthogonalProjectionMap_cutoffCorner (Ω i))
    hstrong k
  have hδ : (0 : ℝ) ≤ b - a := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hleft hδ, hmid]

section ScalarGenericAmbientBound

variable {𝕜 : Type*} [RCLike 𝕜] {G : Type u} [NormedAddCommGroup G]
  [InnerProductSpace 𝕜 G] [CompleteSpace G]

/-- The directed corner never has larger approximation numbers than the ambient
operator: it is the ambient operator pre- and post-composed with contractions. -/
theorem kyFanApproximationGauge_reflectionResidualCorner_le
    (U : Submodule 𝕜 G) [U.HasOrthogonalProjection] (K : G →L[𝕜] G)
    (k : ℕ) :
    kyFanApproximationGauge k (reflectionResidualCorner U K) ≤
      kyFanApproximationGauge k K := by
  have hdef : reflectionResidualCorner U K =
      Uᗮ.subtypeL.adjoint ∘L K ∘L U.subtypeL := rfl
  rw [hdef]
  unfold kyFanApproximationGauge ContinuousLinearMap.kyFanGauge
  refine Finset.sum_le_sum fun p _ => ?_
  have hcomp := approximationSingularValue_comp_le p
    (Uᗮ.subtypeL.adjoint) K U.subtypeL
  have h1 : ‖(Uᗮ.subtypeL : Uᗮ →L[𝕜] G).adjoint‖ ≤ 1 := by
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact Uᗮ.norm_subtypeL_le
  have h2 : ‖U.subtypeL‖ ≤ 1 := U.norm_subtypeL_le
  have h0 := approximationSingularValue_nonneg p K
  refine hcomp.trans ?_
  calc ‖(Uᗮ.subtypeL : Uᗮ →L[𝕜] G).adjoint‖ * approximationSingularValue p K *
        ‖U.subtypeL‖
      ≤ 1 * approximationSingularValue p K * 1 := by
        refine mul_le_mul (mul_le_mul h1 le_rfl h0 zero_le_one) h2
          (norm_nonneg U.subtypeL) ?_
        positivity
    _ = approximationSingularValue p K := by ring

end ScalarGenericAmbientBound

/-- **The endpoint against the ambient residual.**  The form the exact- and
compressed-eigenfamily endpoints of `TanTwoThetaUnboundedKyFan.lean` are stated
in, now with no extremality hypothesis. -/
theorem gap_mul_kyFan_reflectionTangentCorner_le_two_mul_kyFan_ambient
    (hred : TauCeti.LinearPMap.ReducesSubspace A U) (hB : TauCeti.IsOddFor U B)
    (hZsa : IsSelfAdjoint Z) (hZ2 : Z * Z = 1)
    (hZdom : TauCeti.LinearPMap.MapsDomainTo A A Z)
    (hZcomm : ∀ x : A.domain,
      A ⟨Z (x : H), hZdom x⟩ + B (Z (x : H)) = Z (A x) + Z (B (x : H)))
    (hUa : ∀ x : A.domain, (x : H) ∈ U →
      RCLike.re ⟪A x, (x : H)⟫_ℂ ≤ a * ‖(x : H)‖ ^ 2)
    (hUb : ∀ x : A.domain, (x : H) ∈ Uᗮ →
      b * ‖(x : H)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : H)⟫_ℂ)
    (hab : a < b) (hS1 : ‖U.offDiagonalPart Z‖ < 1)
    {ι : Type*} {l : Filter ι} [l.NeBot] {σ : ι → ℝ} (hσ : ∀ i, 0 ≤ σ i)
    (Ω : ∀ i, TauCeti.BoundedCutoff A U (σ i))
    (hstrong : TauCeti.ApproximationNumber.StronglyTendsto
      (fun i => cutoffCorner (Ω i)) l (ContinuousLinearMap.id ℂ U))
    (k : ℕ) :
    (b - a) * kyFanApproximationGauge k (reflectionTangentCorner U Z) ≤
      2 * kyFanApproximationGauge k B := by
  have h := gap_mul_kyFan_reflectionTangentCorner_le_two_mul_kyFan hred hB hZsa
    hZ2 hZdom hZcomm hUa hUb hab hS1 hσ Ω hstrong k
  have h2 := kyFanApproximationGauge_reflectionResidualCorner_le (U := U) B k
  linarith

/-- **The unbounded, residual-form `tan 2Θ` theorem at every Fan-dominant
unitarily invariant ideal gauge, with no extremality hypothesis.**

`δ N(tan 2Θ₀) ≤ 2 N(R₀)` in the repository's scaled form, on the typed directed
corners.  Ideal membership of the scaled tangent corner is concluded, not
assumed.

This is the arbitrary-unitarily-invariant-norm endpoint of the chain; it is the
`mem_and_gauge_le_of_compressedDoubleAngleEigenbasis` statement with the
extremality hypothesis `IsCompressedDoubleAngleEigenbasis` deleted rather than
discharged. -/
theorem mem_and_gauge_le_reflectionTangentCorner
    (N : KyFanDominantIdealFamily (𝕜 := ℂ))
    (hred : TauCeti.LinearPMap.ReducesSubspace A U) (hB : TauCeti.IsOddFor U B)
    (hZsa : IsSelfAdjoint Z) (hZ2 : Z * Z = 1)
    (hZdom : TauCeti.LinearPMap.MapsDomainTo A A Z)
    (hZcomm : ∀ x : A.domain,
      A ⟨Z (x : H), hZdom x⟩ + B (Z (x : H)) = Z (A x) + Z (B (x : H)))
    (hUa : ∀ x : A.domain, (x : H) ∈ U →
      RCLike.re ⟪A x, (x : H)⟫_ℂ ≤ a * ‖(x : H)‖ ^ 2)
    (hUb : ∀ x : A.domain, (x : H) ∈ Uᗮ →
      b * ‖(x : H)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : H)⟫_ℂ)
    (hab : a < b) (hS1 : ‖U.offDiagonalPart Z‖ < 1)
    {ι : Type*} {l : Filter ι} [l.NeBot] {σ : ι → ℝ} (hσ : ∀ i, 0 ≤ σ i)
    (Ω : ∀ i, TauCeti.BoundedCutoff A U (σ i))
    (hstrong : TauCeti.ApproximationNumber.StronglyTendsto
      (fun i => cutoffCorner (Ω i)) l (ContinuousLinearMap.id ℂ U))
    (hBmem : N.Mem (reflectionResidualCorner U B)) :
    N.Mem ((((b - a) / 2 : ℝ) : ℂ) • reflectionTangentCorner U Z) ∧
      N.gauge ((((b - a) / 2 : ℝ) : ℂ) • reflectionTangentCorner U Z) ≤
        N.gauge (reflectionResidualCorner U B) := by
  refine mem_and_gauge_le_of_all_kyFanApproximationGauge_le N.toFanDominantIdealFamily hBmem fun k => ?_
  rw [kyFanApproximationGauge_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by linarith : (0 : ℝ) ≤ (b - a) / 2)]
  have h := gap_mul_kyFan_reflectionTangentCorner_le_two_mul_kyFan hred hB hZsa
    hZ2 hZdom hZcomm hUa hUb hab hS1 hσ Ω hstrong k
  linarith

end

end DavisKahan1970
end TauCeti
