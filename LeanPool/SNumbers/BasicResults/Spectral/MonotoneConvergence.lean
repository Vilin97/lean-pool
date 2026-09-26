/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Monotone convergence of positive operators (analytic core)

*Why this file is needed:* the complex spectral projection in `Projection` is a
strong-operator limit of an antitone sequence of positive operators; this file provides the
analytic foundation that makes that limit exist and be a bounded operator.

The key inequality is, for a positive operator `A` on a complex Hilbert space,
`‖A x‖² ≤ ‖A‖ · re⟪A x, x⟫`. It comes from the operator inequality
`A² ≤ ‖A‖ • A` (true because `t² ≤ ‖A‖·t` on the spectrum `[0, ‖A‖]`) together
with `‖A x‖² = re⟪A² x, x⟫`.
-/

@[expose] public section

open ContinuousLinearMap RCLike
open scoped InnerProductSpace

namespace SpectralRepresentation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [Nontrivial H]

/-- For a positive operator `A`, `A² ≤ ‖A‖ • A`. On the spectrum `[0, ‖A‖]`
one has `t² ≤ ‖A‖ · t`, and the continuous functional calculus transfers this
pointwise inequality to the operator order. -/
theorem sq_le_norm_smul_of_isPositive {A : H →L[ℂ] H} (hA : A.IsPositive) :
    A ^ 2 ≤ (‖A‖ : ℝ) • A := by
  have hsa : IsSelfAdjoint A := hA.isSelfAdjoint
  have h0A : (0 : H →L[ℂ] H) ≤ A := by
    rw [ContinuousLinearMap.le_def, sub_zero]; exact hA
  rw [← sub_nonneg]
  have key : (‖A‖ : ℝ) • A - A ^ 2 = cfc (fun t : ℝ => ‖A‖ * t - t ^ 2) A := by
    rw [cfc_sub _ _ A, cfc_const_mul .., cfc_pow_id .., cfc_id' ..]
  rw [key]
  apply cfc_nonneg
  intro t ht
  have ht0 : 0 ≤ t := spectrum_nonneg_of_nonneg h0A ht
  have htle : t ≤ ‖A‖ := by
    have := spectrum.norm_le_norm_of_mem ht
    rwa [Real.norm_eq_abs, abs_of_nonneg ht0] at this
  nlinarith [ht0, htle]

/-- **Cauchy estimate for positive operators.** For `A` positive,
`‖A x‖² ≤ ‖A‖ · re⟪A x, x⟫`. This powers the strong-operator monotone
convergence of positive operators. -/
theorem norm_apply_sq_le_of_isPositive {A : H →L[ℂ] H} (hA : A.IsPositive) (x : H) :
    ‖A x‖ ^ 2 ≤ ‖A‖ * RCLike.re (⟪A x, x⟫_ℂ) := by
  have hsa : adjoint A = A := hA.isSelfAdjoint
  -- `‖A x‖² = re ⟪A² x, x⟫`.
  have hAsq : RCLike.re (⟪(A ^ 2) x, x⟫_ℂ) = ‖A x‖ ^ 2 := by
    rw [pow_two, mul_apply_eq_comp,
      ← ContinuousLinearMap.adjoint_inner_right A (A x) x, hsa, inner_self_eq_norm_sq]
  -- Monotonicity of `re⟪· x, x⟫` from `A² ≤ ‖A‖ • A`.
  have hpos : ((‖A‖ : ℝ) • A - A ^ 2).IsPositive := sq_le_norm_smul_of_isPositive hA
  have hmono : RCLike.re (⟪(A ^ 2) x, x⟫_ℂ) ≤ RCLike.re (⟪((‖A‖ : ℝ) • A) x, x⟫_ℂ) := by
    have h0 := hpos.2 x
    rw [ContinuousLinearMap.reApplyInnerSelf_apply, sub_apply,
      inner_sub_left, map_sub, sub_nonneg] at h0
    exact h0
  -- `re⟪(‖A‖ • A) x, x⟫ = ‖A‖ · re⟪A x, x⟫`.
  have hsmul : RCLike.re (⟪((‖A‖ : ℝ) • A) x, x⟫_ℂ) = ‖A‖ * RCLike.re (⟪A x, x⟫_ℂ) := by
    rw [smul_apply, RCLike.real_smul_eq_coe_smul (K := ℂ),
      inner_smul_left, RCLike.conj_ofReal, RCLike.re_ofReal_mul]
  rw [← hAsq]
  exact hmono.trans_eq hsmul

open Filter Topology in
omit [CompleteSpace H] [Nontrivial H] in
/-- `re⟪(B - C) x, x⟫` splits additively over the difference. -/
private theorem reApplyInnerSelf_sub (B C : H →L[ℂ] H) (x : H) :
    (B - C).reApplyInnerSelf x = B.reApplyInnerSelf x - C.reApplyInnerSelf x := by
  simp only [ContinuousLinearMap.reApplyInnerSelf_apply, sub_apply,
    inner_sub_left, map_sub]

omit [CompleteSpace H] [Nontrivial H] in
/-- The map `B ↦ re⟪B x, x⟫` is monotone for the Loewner order. -/
theorem reApplyInnerSelf_mono {B C : H →L[ℂ] H} (h : B ≤ C) (x : H) :
    B.reApplyInnerSelf x ≤ C.reApplyInnerSelf x := by
  have hpos : (C - B).IsPositive := h
  have h2 := hpos.2 x
  rw [reApplyInnerSelf_sub, sub_nonneg] at h2
  exact h2

open Filter Topology in
/-- **Strong-operator monotone convergence.** A pointwise-antitone sequence of
positive operators converges in the strong operator topology: for every `x`,
`fun n => T n x` converges. The proof shows the sequence is Cauchy, controlling
`‖T n x - T m x‖²` by `2‖T 0‖ · (re⟪T n x,x⟫ - re⟪T m x,x⟫)` (the Cauchy
estimate `norm_apply_sq_le_of_isPositive`), the latter being Cauchy as a bounded
antitone real sequence. -/
theorem exists_tendsto_of_antitone_isPositive {T : ℕ → (H →L[ℂ] H)}
    (hpos : ∀ n, (T n).IsPositive) (hanti : Antitone T) (x : H) :
    ∃ y, Tendsto (fun n => T n x) atTop (𝓝 y) := by
  set a : ℕ → ℝ := fun n => (T n).reApplyInnerSelf x with ha_def
  have ha_anti : Antitone a := fun m n hmn => reApplyInnerSelf_mono (hanti hmn) x
  have ha_bdd : BddBelow (Set.range a) := ⟨0, by rintro _ ⟨n, rfl⟩; exact (hpos n).2 x⟩
  set L : ℝ := ⨅ n, a n with hL_def
  have ha_tendsto : Tendsto a atTop (𝓝 L) := tendsto_atTop_ciInf ha_anti ha_bdd
  have hnorm_bound : ∀ m n, ‖T m - T n‖ ≤ 2 * ‖T 0‖ := by
    intro m n
    have hbnd : ∀ k, ‖T k‖ ≤ ‖T 0‖ := fun k => by
      have hk0 : (0 : H →L[ℂ] H) ≤ T k := by
        rw [ContinuousLinearMap.le_def, sub_zero]; exact hpos k
      exact CStarAlgebra.norm_le_norm_of_le_of_nonneg (hanti (Nat.zero_le k)) hk0
    calc ‖T m - T n‖ ≤ ‖T m‖ + ‖T n‖ := norm_sub_le _ _
      _ ≤ ‖T 0‖ + ‖T 0‖ := by gcongr <;> exact hbnd _
      _ = 2 * ‖T 0‖ := by ring
  have key : ∀ m n, n ≤ m → ‖T m x - T n x‖ ^ 2 ≤ 2 * ‖T 0‖ * (a n - a m) := by
    intro m n hnm
    have hpmn : (T n - T m).IsPositive := hanti hnm
    have h1 : ‖T m x - T n x‖ = ‖(T n - T m) x‖ := by
      rw [sub_apply]; exact norm_sub_rev _ _
    rw [h1]
    calc ‖(T n - T m) x‖ ^ 2
        ≤ ‖T n - T m‖ * RCLike.re (⟪(T n - T m) x, x⟫_ℂ) :=
          norm_apply_sq_le_of_isPositive hpmn x
      _ = ‖T n - T m‖ * (a n - a m) := by
          rw [← ContinuousLinearMap.reApplyInnerSelf_apply, reApplyInnerSelf_sub]
      _ ≤ 2 * ‖T 0‖ * (a n - a m) :=
          mul_le_mul_of_nonneg_right (hnorm_bound n m) (sub_nonneg.mpr (ha_anti hnm))
  have hCauchy : CauchySeq (fun n => T n x) := by
    refine cauchySeq_of_le_tendsto_0 (fun N => Real.sqrt (2 * ‖T 0‖ * (a N - L))) ?_ ?_
    · intro n m N hNn hNm
      have hbound : ∀ i j, j ≤ i → N ≤ j → ‖T i x - T j x‖ ^ 2 ≤ 2 * ‖T 0‖ * (a N - L) := by
        intro i j hji hNj
        refine (key i j hji).trans ?_
        have hj : a j ≤ a N := ha_anti hNj
        have hi : L ≤ a i := ciInf_le ha_bdd i
        exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      rw [dist_eq_norm, ← Real.sqrt_sq (norm_nonneg (T n x - T m x))]
      apply Real.sqrt_le_sqrt
      rcases le_total m n with hmn | hnm
      · exact hbound n m hmn hNm
      · rw [show ‖T n x - T m x‖ = ‖T m x - T n x‖ from norm_sub_rev _ _]
        exact hbound m n hnm hNn
    · have h0 : Tendsto (fun N => 2 * ‖T 0‖ * (a N - L)) atTop (𝓝 0) := by
        have : Tendsto (fun N => a N - L) atTop (𝓝 0) := by simpa using ha_tendsto.sub_const L
        simpa using this.const_mul (2 * ‖T 0‖)
      have hsqrt := (Real.continuous_sqrt.tendsto 0).comp h0
      rw [Real.sqrt_zero] at hsqrt
      exact hsqrt
  exact cauchySeq_tendsto_of_complete hCauchy

open Filter Topology in
/-- **The strong limit as a bounded operator.** A pointwise-antitone sequence of
positive operators has a continuous-linear strong limit `E`: `T n x → E x` for
every `x`, with `‖E‖ ≤ ‖T 0‖`.

The continuity of the limit is established here by hand, via the uniform bound
`‖T k‖ ≤ ‖T 0‖` and `LinearMap.mkContinuous`. Mathlib's
`continuousLinearMapOfTendsto` proves the same thing in general — a pointwise
limit of continuous linear maps along a countably generated filter is again
continuous — but it rests on Banach–Steinhaus, so using it would pull
`Mathlib.Analysis.LocallyConvex.Barrelled` into this file. Since the uniform
bound is available for free here, the elementary route is kept. -/
theorem exists_continuousLinearMap_tendsto {T : ℕ → (H →L[ℂ] H)}
    (hpos : ∀ n, (T n).IsPositive) (hanti : Antitone T) :
    ∃ E : H →L[ℂ] H, ∀ x, Tendsto (fun n => T n x) atTop (𝓝 (E x)) := by
  have hbnd : ∀ k, ‖T k‖ ≤ ‖T 0‖ := fun k => by
    have hk0 : (0 : H →L[ℂ] H) ≤ T k := by
      rw [ContinuousLinearMap.le_def, sub_zero]; exact hpos k
    exact CStarAlgebra.norm_le_norm_of_le_of_nonneg (hanti (Nat.zero_le k)) hk0
  choose e he using fun x => exists_tendsto_of_antitone_isPositive hpos hanti x
  let L : H →ₗ[ℂ] H :=
    { toFun := e
      map_add' := fun x y => by
        refine tendsto_nhds_unique (he (x + y)) ?_
        have h : (fun n => T n (x + y)) = (fun n => T n x + T n y) :=
          funext fun n => map_add (T n) x y
        rw [h]; exact (he x).add (he y)
      map_smul' := fun c x => by
        refine tendsto_nhds_unique (he (c • x)) ?_
        have h : (fun n => T n (c • x)) = (fun n => c • T n x) :=
          funext fun n => map_smul (T n) c x
        rw [h]; exact (he x).const_smul c }
  refine ⟨L.mkContinuous ‖T 0‖ fun x => ?_, fun x => he x⟩
  refine le_of_tendsto' (he x).norm fun n => ?_
  exact (T n).le_opNorm x |>.trans (mul_le_mul_of_nonneg_right (hbnd n) (norm_nonneg x))

/-! ### Properties preserved by the strong limit

If `E` is a strong limit of `T n` (`T n x → E x` for all `x`), then `E`
inherits self-adjointness, positivity, and commutation with a fixed operator.
These transfer the per-`n` facts to the limit by continuity of the inner
product and of operator application. -/

open Filter Topology in
omit [CompleteSpace H] [Nontrivial H] in
/-- A strong limit of symmetric operators is symmetric (`⟪E x, y⟫ = ⟪x, E y⟫`). -/
theorem isSymmetric_of_tendsto {T : ℕ → H →L[ℂ] H} {E : H →L[ℂ] H}
    (hsymm : ∀ n, (T n : H →ₗ[ℂ] H).IsSymmetric)
    (hE : ∀ x, Tendsto (fun n => T n x) atTop (𝓝 (E x))) : (E : H →ₗ[ℂ] H).IsSymmetric := by
  intro x y
  refine tendsto_nhds_unique ((hE x).inner tendsto_const_nhds) ?_
  have heq : (fun n => ⟪T n x, y⟫_ℂ) = (fun n => ⟪x, T n y⟫_ℂ) := funext fun n => hsymm n x y
  rw [heq]
  exact tendsto_const_nhds.inner (hE y)

open Filter Topology in
omit [CompleteSpace H] [Nontrivial H] in
/-- A strong limit of positive operators is positive. -/
theorem isPositive_of_tendsto {T : ℕ → H →L[ℂ] H} {E : H →L[ℂ] H}
    (hpos : ∀ n, (T n).IsPositive)
    (hE : ∀ x, Tendsto (fun n => T n x) atTop (𝓝 (E x))) : E.IsPositive := by
  refine ⟨isSymmetric_of_tendsto (fun n => (hpos n).1) hE, fun x => ?_⟩
  rw [ContinuousLinearMap.reApplyInnerSelf_apply]
  refine ge_of_tendsto' ((RCLike.continuous_re.tendsto _).comp ((hE x).inner tendsto_const_nhds))
    fun n => ?_
  have := (hpos n).2 x
  rwa [ContinuousLinearMap.reApplyInnerSelf_apply] at this

open Filter Topology in
omit [CompleteSpace H] [Nontrivial H] in
/-- If every `T n` commutes with `P`, so does the strong limit `E`. -/
theorem commute_of_tendsto {T : ℕ → H →L[ℂ] H} {E P : H →L[ℂ] H}
    (hcomm : ∀ n, (T n).comp P = P.comp (T n))
    (hE : ∀ x, Tendsto (fun n => T n x) atTop (𝓝 (E x))) : E.comp P = P.comp E := by
  ext x
  simp only [ContinuousLinearMap.comp_apply]
  refine tendsto_nhds_unique (hE (P x)) ?_
  have heq : (fun n => T n (P x)) = (fun n => P (T n x)) := funext fun n => by
    rw [← ContinuousLinearMap.comp_apply, hcomm n, ContinuousLinearMap.comp_apply]
  rw [heq]
  exact (P.continuous.tendsto (E x)).comp (hE x)

end SpectralRepresentation

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
