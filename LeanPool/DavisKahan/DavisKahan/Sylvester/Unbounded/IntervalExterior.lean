/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.BoundedFromSpectrum
import LeanPool.DavisKahan.DavisKahan.OperatorIdeal.CanonicalRealView
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.GapResolvent
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Resolvent

/-! # Interval Exterior -/

open TauCeti.DavisKahan.Sylvester

/-!
# Theorem 5.2, interval/exterior orientation, with genuine spectra

The fully unbounded interval/exterior Sylvester estimates at
unitary-invariant ideal scope, with both blocks closed self-adjoint
operators and all spectral hypotheses phrased through the Spectra spectrum:

* `semibounded_of_spectrum_subset_Icc` — spectral inclusion in `[β, α]`
  yields the matching quadratic-form bounds, through the bounded
  realization of `BoundedFromSpectrum`;
* `unbounded_sylvester_mem_and_gauge_le_of_spectra_exteriorLeft_intervalRight`
  and `..._intervalLeft_exteriorRight` — the two orientations of the
  Davis--Kahan Theorem 5.2 interval/exterior configuration:
  `A X - X B = C` with one block's spectrum in `[β, α]` and the other's
  avoiding `(β - δ, α + δ)` gives `X ∈ N` and `δ · gauge X ≤ gauge C`.

The interval block is secretly bounded (`BoundedFromSpectrum`), the
exterior block carries the Spectra-backed shifted resolvent
(`twoSidedShiftedInverseBound_of_spectrum_gap`), and the ideal-scope
Neumann engines of `SinTheta/Unbounded/Gauge.lean` finish both orientations.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan


open TauCeti.DavisKahan.ExactSinTheta

universe v

variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

namespace Sylvester

/-- **Interval/exterior separation** for two self-adjoint closed operators, stated over the
Spectra spectrum.  Either orientation is permitted: one operator's real spectrum sits inside
`[β, α]` while the other avoids the `δ`-enlargement `(β - δ, α + δ)`.

`RealSpectrumIntervalExteriorGap` (`Sylvester/Gap.lean`) is the `realSpectrum` spelling of the
same configuration; `realSpectrum_eq_spectraSpectrum` identifies the two spectra.

**Placed here rather than in either consumer.**  `Sylvester/Unbounded/AllGap.lean` and
`SinTheta/Unbounded/IntervalExterior.lean` each carried a character-for-character copy of this
definition (`SylvesterIntervalExteriorGap` and `SpectralIntervalExteriorGap`).  They are siblings
— neither may import the other, since `SinTheta -> Sylvester` is the only permitted direction —
so the single surviving definition has to live in the module they share. -/
def SpectralIntervalExteriorGap
    (A : E →ₗ.[ℂ] E) (B : F →ₗ.[ℂ] F)
    (β α δ : ℝ) : Prop :=
  (Complex.ofReal ⁻¹' TauCeti.LinearPMap.spectrum A ⊆
        Set.Icc β α ∧
    ∀ lam ∈ Set.Ioo (β - δ) (α + δ),
      (lam : ℂ) ∉ TauCeti.LinearPMap.spectrum B) ∨
  (Complex.ofReal ⁻¹' TauCeti.LinearPMap.spectrum B ⊆
        Set.Icc β α ∧
    ∀ lam ∈ Set.Ioo (β - δ) (α + δ),
      (lam : ℂ) ∉ TauCeti.LinearPMap.spectrum A)

end Sylvester

/-- **Form bounds from spectral inclusion.**  A closed self-adjoint operator
with Spectra spectrum in `[β, α]` has its quadratic form in `[β, α]`:
transported through the bounded realization and the centered norm bound. -/
theorem semibounded_of_spectrum_subset_Icc
    {B : F →ₗ.[ℂ] F}
    (hB : IsSelfAdjoint B)
    {β α : ℝ} (hβα : β ≤ α)
    (hσ : Complex.ofReal ⁻¹' TauCeti.LinearPMap.spectrum B ⊆
        Set.Icc β α) :
    TauCeti.LinearPMap.SemiboundedBelow B β ∧
      TauCeti.LinearPMap.SemiboundedAbove B α := by
  obtain ⟨R, hnorm⟩ :=
    exists_boundedRealization_of_spectrum_subset_Icc hB hβα hσ
  have key : ∀ x : B.domain,
      |RCLike.re ⟪B x, (x : F)⟫_ℂ -
        (β + α) / 2 * ‖(x : F)‖ ^ 2| ≤
      (α - β) / 2 * ‖(x : F)‖ ^ 2 := by
    intro x
    have hag : R.operator (x : F) = B x := R.agrees x
    have happ : (R.operator - (((β + α) / 2 : ℝ) : ℂ) •
        ContinuousLinearMap.id ℂ F) (x : F) =
        B x - (((β + α) / 2 : ℝ) : ℂ) • (x : F) := by
      rw [sub_apply, smul_apply, ContinuousLinearMap.id_apply, hag]
    have hn : ‖B x - (((β + α) / 2 : ℝ) : ℂ) • (x : F)‖ ≤
        (α - β) / 2 * ‖(x : F)‖ := by
      rw [← happ]
      exact le_trans (ContinuousLinearMap.le_opNorm _ _)
        (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _))
    have h1 : RCLike.re ⟪B x -
        (((β + α) / 2 : ℝ) : ℂ) • (x : F), (x : F)⟫_ℂ =
        RCLike.re ⟪B x, (x : F)⟫_ℂ -
          (β + α) / 2 * ‖(x : F)‖ ^ 2 := by
      simp only [inner_sub_left, map_sub, inner_smul_left, Complex.conj_ofReal,
        ← Complex.real_smul, RCLike.smul_re, inner_self_eq_norm_sq]
    have h2 : |RCLike.re ⟪B x -
        (((β + α) / 2 : ℝ) : ℂ) • (x : F), (x : F)⟫_ℂ| ≤
        (α - β) / 2 * ‖(x : F)‖ ^ 2 := by
      refine le_trans (RCLike.abs_re_le_norm _) ?_
      refine le_trans (norm_inner_le_norm _ _) ?_
      calc ‖B x - (((β + α) / 2 : ℝ) : ℂ) • (x : F)‖ *
            ‖(x : F)‖
          ≤ ((α - β) / 2 * ‖(x : F)‖) * ‖(x : F)‖ :=
            mul_le_mul_of_nonneg_right hn (norm_nonneg _)
        _ = (α - β) / 2 * ‖(x : F)‖ ^ 2 := by ring
    rw [h1] at h2
    exact h2
  constructor
  · intro x
    have h := (abs_le.mp (key x)).1
    have hring : (β + α) / 2 * ‖(x : F)‖ ^ 2 -
        (α - β) / 2 * ‖(x : F)‖ ^ 2 = β * ‖(x : F)‖ ^ 2 := by ring
    have hlegacy : β * ‖(x : F)‖ ^ 2 ≤
        RCLike.re ⟪B x, (x : F)⟫_ℂ := by
      linarith
    exact hlegacy
  · intro x
    have h := (abs_le.mp (key x)).2
    have hring : (β + α) / 2 * ‖(x : F)‖ ^ 2 +
        (α - β) / 2 * ‖(x : F)‖ ^ 2 = α * ‖(x : F)‖ ^ 2 := by ring
    have hlegacy :
        RCLike.re ⟪B x, (x : F)⟫_ℂ ≤
          α * ‖(x : F)‖ ^ 2 := by
      linarith
    exact hlegacy

/-- **Davis--Kahan Theorem 5.2, interval/exterior, exterior block on the
left, genuine spectra.**  For closed self-adjoint `A`, `B` with the
Sylvester equation `A X - X B = C`, the spectrum of `B` in `[β, α]`, and
the spectrum of `A` avoiding `(β - δ, α + δ)`, membership of `C` in a
rectangular symmetric ideal family passes to `X` with
`δ · gauge X ≤ gauge C`. -/
theorem unbounded_sylvester_mem_and_gauge_le_of_spectra_exteriorLeft_intervalRight
    (N : TauCeti.SymmetricOperatorIdealFamily.{0, v} ℂ)
    [N.toOperatorIdealFamily.IsComplete]
    {A : E →ₗ.[ℂ] E} {B : F →ₗ.[ℂ] F}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {X C : F →L[ℂ] E} {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hσA : ∀ lam ∈ Set.Ioo (β - δ) (α + δ),
      (lam : ℂ) ∉ TauCeti.LinearPMap.spectrum A)
    (hσB : Complex.ofReal ⁻¹' TauCeti.LinearPMap.spectrum B ⊆
        Set.Icc β α)
    (hEq : TauCeti.LinearPMap.SylvesterEquation A B X C)
    (hC : N.Mem C) :
    N.Mem X ∧ δ * N.gaugeReal X ≤ N.gaugeReal C := by
  obtain ⟨hBlow, hBhigh⟩ := semibounded_of_spectrum_subset_Icc hB hβα hσB
  have hAres : TwoSidedShiftedInverseBound A ((α + β) / 2)
      ((α - β) / 2 + δ) := by
    refine twoSidedShiftedInverseBound_of_spectrum_gap hA (by linarith) ?_
    intro lam hlam
    refine hσA lam ?_
    rw [Set.mem_Ioo] at hlam ⊢
    exact ⟨by linarith [hlam.1], by linarith [hlam.2]⟩
  exact mem_and_gauge_le_of_exteriorLeft_intervalRight N
    hA.isClosed hB.dense_domain hβα hδ
    (TauCeti.LinearPMap.isSymmetric_of_isSelfAdjoint hB) hBlow hBhigh hAres hEq hC

/-- **Davis--Kahan Theorem 5.2, interval/exterior, interval block on the
left, genuine spectra.**  The opposite orientation: the spectrum of `A`
in `[β, α]` and the spectrum of `B` avoiding `(β - δ, α + δ)`.  The
interval block is replaced by its bounded realization and the ideal-scope
Neumann engine finishes. -/
theorem unbounded_sylvester_mem_and_gauge_le_of_spectra_intervalLeft_exteriorRight
    (N : TauCeti.SymmetricOperatorIdealFamily.{0, v} ℂ)
    [N.toOperatorIdealFamily.IsComplete]
    {A : E →ₗ.[ℂ] E} {B : F →ₗ.[ℂ] F}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {X C : F →L[ℂ] E} {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hσA : Complex.ofReal ⁻¹' TauCeti.LinearPMap.spectrum A ⊆
        Set.Icc β α)
    (hσB : ∀ lam ∈ Set.Ioo (β - δ) (α + δ),
      (lam : ℂ) ∉ TauCeti.LinearPMap.spectrum B)
    (hEq : TauCeti.LinearPMap.SylvesterEquation A B X C)
    (hC : N.Mem C) :
    N.Mem X ∧ δ * N.gaugeReal X ≤ N.gaugeReal C := by
  have hr0 : (0 : ℝ) ≤ (α - β) / 2 := by linarith
  obtain ⟨R, hRnorm⟩ :=
    exists_boundedRealization_of_spectrum_subset_Icc hA hβα hσA
  have hRnorm' : ‖R.operator - (((α + β) / 2 : ℝ) : ℂ) •
      ContinuousLinearMap.id ℂ E‖ ≤ (α - β) / 2 := by
    have h : ((β + α) / 2 : ℝ) = (α + β) / 2 := by ring
    rwa [h] at hRnorm
  have hBres : TwoSidedShiftedInverseBound B ((α + β) / 2)
      ((α - β) / 2 + δ) := by
    refine twoSidedShiftedInverseBound_of_spectrum_gap hB (by linarith) ?_
    intro lam hlam
    refine hσB lam ?_
    rw [Set.mem_Ioo] at hlam ⊢
    exact ⟨by linarith [hlam.1], by linarith [hlam.2]⟩
  obtain ⟨J, hdom, _hleft, hright, hJnorm⟩ := hBres
  have hEq' : ∀ y : B.domain,
      (R.operator - (((α + β) / 2 : ℝ) : ℂ) •
        ContinuousLinearMap.id ℂ E) (X (y : F)) -
        (X (B y) -
          (((α + β) / 2 : ℝ) : ℂ) • X (y : F)) = C (y : F) := by
    intro y
    have h1 := hEq.equation y
    have h2 : R.operator (X (y : F)) =
        A ⟨X (y : F), hEq.mapsTo_domain y⟩ :=
      R.agrees ⟨X (y : F), hEq.mapsTo_domain y⟩
    rw [sub_apply, smul_apply, ContinuousLinearMap.id_apply, h2, ← h1]
    abel
  exact mem_and_gauge_le_of_boundedLeft_exteriorRight N hr0 hδ hRnorm'
    hdom hright hJnorm hEq' hC

end DavisKahan
end TauCeti
