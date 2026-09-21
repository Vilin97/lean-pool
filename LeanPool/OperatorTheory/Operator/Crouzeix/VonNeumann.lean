/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import LeanPool.OperatorTheory.Operator.Dilation.Schaeffer
import LeanPool.OperatorTheory.Operator.SpectralSet.Basic

/-!
# Von Neumann's inequality (L4.1)

For a contraction `T` on a complex Hilbert space `E` and a polynomial `p`,
`‖p(T)‖ ≤ sup_{‖z‖ ≤ 1} ‖p(z)‖`.

Route (task-spec L4.1, via dilation): the Schäffer dilation (L3.1) gives a Hilbert space `H`,
an inner-product-preserving `V : E →L[ℂ] H` and a unitary `U` on `H` with
`V† U^n V = T^n` for all `n`. Then

1. `V† p(U) V = p(T)` by linearity (`adjoint_aeval_apply_of_forall_pow`);
2. `‖p(T)‖ ≤ ‖V†‖ ‖p(U)‖ ‖V‖ ≤ ‖p(U)‖` since `‖V†‖ = ‖V‖ ≤ 1`
   (`norm_aeval_le_norm_aeval_of_dilation`);
3. for unitary `U` the element `p(U)` is normal, so `‖p(U)‖` equals its spectral radius; the
   spectral mapping theorem and `σ(U) ⊆ 𝕊¹ ⊆ closedBall 0 1` bound this by the sup-norm of `p` on
   the closed unit disk (`norm_aeval_le_polynomialSupNorm_closedBall_of_mem_unitary`).

## Main declarations

* `norm_eval_le_polynomialSupNorm` — `‖p.eval z‖ ≤ polynomialSupNorm p X` for `z ∈ X` whenever
  the values of `p` on `X` are bounded; `polynomialSupNorm_nonneg`; and
  `bddAbove_norm_eval_image_of_isCompact` for compact `X`.
* `norm_aeval_le_polynomialSupNorm_closedBall_of_mem_unitary` — step 3, in any C*-algebra.
* `adjoint_aeval_apply_of_forall_pow`, `norm_aeval_le_norm_aeval_of_dilation` — steps 1–2.
* `vonNeumann_inequality_of_exists_unitary_power_dilation` — the inequality for any `T`
  admitting a unitary power dilation (the exact conclusion of L3.1 as a hypothesis).
* `vonNeumann_inequality` — the boundary theorem for contractions, obtained by applying the
  preceding dilation inequality to L3.1 (`exists_unitary_power_dilation`).

Requires `[CompleteSpace E]` (adjoints, the C*-algebra structure on `E →L[ℂ] E`).
-/

open Polynomial ContinuousLinearMap
open scoped InnerProductSpace

universe u

/-! ### The polynomial sup-norm -/

/-- The polynomial sup-norm is nonnegative. -/
theorem polynomialSupNorm_nonneg (p : ℂ[X]) (X : Set ℂ) : 0 ≤ polynomialSupNorm p X :=
  Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => norm_nonneg _

/-- If the values `‖p.eval z‖`, `z ∈ X`, are bounded above, then each of them is at most
`polynomialSupNorm p X`. -/
theorem norm_eval_le_polynomialSupNorm (p : ℂ[X]) {X : Set ℂ}
    (hX : BddAbove ((fun z => ‖p.eval z‖) '' X)) {z : ℂ} (hz : z ∈ X) :
    ‖p.eval z‖ ≤ polynomialSupNorm p X := by
  obtain ⟨M, hM⟩ := hX
  unfold polynomialSupNorm
  refine le_ciSup₂ (f := fun z (_ : z ∈ X) => ‖p.eval z‖) ⟨M, ?_⟩ z hz
  rintro y hy
  rw [Set.mem_iUnion] at hy
  obtain ⟨w, hw⟩ := hy
  rw [Set.mem_range] at hw
  obtain ⟨hwX, rfl⟩ := hw
  exact hM ⟨w, hwX, rfl⟩

/-- On a compact set the values `‖p.eval z‖` are bounded above. -/
theorem bddAbove_norm_eval_image_of_isCompact (p : ℂ[X]) {K : Set ℂ} (hK : IsCompact K) :
    BddAbove ((fun z => ‖p.eval z‖) '' K) :=
  hK.bddAbove_image p.continuous.norm.continuousOn

/-! ### Polynomials in a unitary -/

/-- **Von Neumann's inequality for unitaries**, in any C*-algebra: for `U` unitary,
`‖p(U)‖ ≤ sup_{‖z‖ ≤ 1} ‖p(z)‖`. Since `p(U)` is normal, `‖p(U)‖` is its spectral radius, and
`σ(p(U)) = p(σ(U))` with `σ(U)` contained in the unit circle. -/
theorem norm_aeval_le_polynomialSupNorm_closedBall_of_mem_unitary {A : Type*} [CStarAlgebra A]
    {U : A} (hU : U ∈ unitary A) (p : ℂ[X]) :
    ‖aeval U p‖ ≤ polynomialSupNorm p (Metric.closedBall (0 : ℂ) 1) := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · rw [Subsingleton.elim (aeval U p) 0, norm_zero]
    exact polynomialSupNorm_nonneg p _
  have : IsStarNormal U := isStarNormal_of_mem_unitary hU
  have : IsStarNormal (aeval U p) := by
    rw [← cfc_polynomial p U]
    exact cfc_predicate _ U
  have hM0 : 0 ≤ polynomialSupNorm p (Metric.closedBall (0 : ℂ) 1) :=
    polynomialSupNorm_nonneg p _
  have hbound : spectralRadius ℂ (aeval U p) ≤
      ((polynomialSupNorm p (Metric.closedBall (0 : ℂ) 1)).toNNReal : ENNReal) := by
    rw [spectralRadius_eq_of_unital]
    refine iSup₂_le fun k hk => ?_
    rw [spectrum.map_polynomial_aeval] at hk
    obtain ⟨z, hz, rfl⟩ := hk
    have hz1 : z ∈ Metric.closedBall (0 : ℂ) 1 :=
      Metric.sphere_subset_closedBall (spectrum.subset_circle_of_unitary hU hz)
    rw [ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hM0]
    exact norm_eval_le_polynomialSupNorm p
      (bddAbove_norm_eval_image_of_isCompact p (isCompact_closedBall (0 : ℂ) 1)) hz1
  rw [IsStarNormal.spectralRadius_eq_nnnorm (aeval U p), ENNReal.coe_le_coe,
    ← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hM0] at hbound
  exact hbound

/-! ### Compression through a power dilation -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- If `V† U^n V = T^n` for all `n`, then `V† p(U) V = p(T)` for every polynomial `p`. -/
theorem adjoint_aeval_apply_of_forall_pow (T : E →L[ℂ] E) (V : E →L[ℂ] H) (U : H →L[ℂ] H)
    (hpow : ∀ (n : ℕ) (x : E), adjoint V ((U ^ n) (V x)) = (T ^ n) x) (p : ℂ[X]) (x : E) :
    adjoint V ((aeval U p) (V x)) = (aeval T p) x := by
  rw [aeval_eq_sum_range, aeval_eq_sum_range]
  simp only [sum_apply, smul_apply, map_sum, map_smul, hpow]

/-- If `V` preserves inner products and `V† U^n V = T^n` for all `n`, then
`‖p(T)‖ ≤ ‖p(U)‖` for every polynomial `p`. -/
theorem norm_aeval_le_norm_aeval_of_dilation (T : E →L[ℂ] E) (V : E →L[ℂ] H) (U : H →L[ℂ] H)
    (hV : ∀ x y : E, ⟪V x, V y⟫_ℂ = ⟪x, y⟫_ℂ)
    (hpow : ∀ (n : ℕ) (x : E), adjoint V ((U ^ n) (V x)) = (T ^ n) x) (p : ℂ[X]) :
    ‖aeval T p‖ ≤ ‖aeval U p‖ := by
  have hVnorm : ∀ x, ‖V x‖ = ‖x‖ := (LinearMap.norm_map_iff_inner_map_map V).mpr hV
  have hV1 : ‖V‖ ≤ 1 := V.opNorm_le_bound zero_le_one fun x => by rw [hVnorm x, one_mul]
  refine (aeval T p).opNorm_le_bound (norm_nonneg _) fun x => ?_
  rw [← adjoint_aeval_apply_of_forall_pow T V U hpow p x]
  calc ‖adjoint V ((aeval U p) (V x))‖
      ≤ ‖adjoint V‖ * ‖(aeval U p) (V x)‖ := le_opNorm _ _
    _ ≤ ‖adjoint V‖ * (‖aeval U p‖ * ‖V x‖) := by gcongr; exact le_opNorm _ _
    _ = ‖V‖ * ‖aeval U p‖ * ‖x‖ := by rw [adjoint.norm_map, hVnorm]; ring
    _ ≤ 1 * ‖aeval U p‖ * ‖x‖ := by gcongr
    _ = ‖aeval U p‖ * ‖x‖ := by ring

/-! ### Von Neumann's inequality -/

/-- **Von Neumann's inequality** for an operator admitting a unitary power dilation: if there are
a Hilbert space `H`, an inner-product-preserving `V : E →L[ℂ] H` and a unitary `U` on `H` with
`V† U^n V = T^n` for all `n` (the conclusion of L3.1), then
`‖p(T)‖ ≤ sup_{‖z‖ ≤ 1} ‖p(z)‖` for every polynomial `p`. -/
theorem vonNeumann_inequality_of_exists_unitary_power_dilation (T : E →L[ℂ] E)
    (hdil : ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H) (V : E →L[ℂ] H) (U : H →L[ℂ] H),
      (∀ x y : E, ⟪V x, V y⟫_ℂ = ⟪x, y⟫_ℂ) ∧
      U ∈ unitary (H →L[ℂ] H) ∧
      (∀ (n : ℕ) (x : E), adjoint V ((U ^ n) (V x)) = (T ^ n) x))
    (p : ℂ[X]) :
    ‖aeval T p‖ ≤ polynomialSupNorm p (Metric.closedBall (0 : ℂ) 1) := by
  obtain ⟨H, _, _, _, V, U, hV, hU, hpow⟩ := hdil
  exact (norm_aeval_le_norm_aeval_of_dilation T V U hV hpow p).trans
    (norm_aeval_le_polynomialSupNorm_closedBall_of_mem_unitary hU p)

/-- **Von Neumann's inequality**: for a contraction `T` and a polynomial `p`,
`‖p(T)‖ ≤ sup_{‖z‖ ≤ 1} ‖p(z)‖`. -/
theorem vonNeumann_inequality (T : E →L[ℂ] E) (hT : ‖T‖ ≤ 1) (p : ℂ[X]) :
    ‖aeval T p‖ ≤ polynomialSupNorm p (Metric.closedBall (0 : ℂ) 1) := by
  exact vonNeumann_inequality_of_exists_unitary_power_dilation T
    (exists_unitary_power_dilation T hT) p

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
