/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.Family.OperatorNorm
public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.Adjoint

/-!
# Compact operators as an ideal family

The compact operators, gauged by the operator norm, form a symmetric operator
ideal family: the smallest interesting one, sitting inside
`TauCeti.operatorNormFamily` with the same gauge but a proper carrier.

Everything the ideal laws need is in Mathlib already — `IsCompactOperator.add`,
`.smul`, `.comp_clm`, `.clm_comp`, `isCompactOperator_zero` and
`isClosed_setOfPred_isCompactOperator` — except adjoint-invariance, which is
Schauder's theorem; that is
`TauCeti.ContinuousLinearMap.isCompactOperator_adjoint`, whose own docstring
records that it was written to unblock exactly this family.

## The gauge is `∞` off the ideal

`OperatorIdealFamily` carries an `ℝ≥0∞`-valued gauge that is `∞` exactly off the
carrier, so the compact family's gauge is the operator norm on compact operators
and `∞` elsewhere.  Two of the four laws then need a case split that the
operator-norm family does not:

* `gauge_smul` at `c = 0`, where the left side is `gauge 0 = 0` and the right is
  `0 * ∞ = 0` — the `ℝ≥0∞` convention is what makes this come out right;
* `gauge_comp_le` when `A` is *not* compact, where the bound is vacuous unless
  `L` or `R` is zero, and then `L ∘L A ∘L R` is zero and so compact.

## Main definitions

* `TauCeti.compactOperatorIdealFamily`
* `TauCeti.compactOperatorFamily`: its symmetric (adjoint-invariant) refinement.
* `TauCeti.instIsCompleteCompactOperatorIdealFamily`: the ideal is complete,
  because the compact operators are closed for the operator norm and the gauge
  *is* the operator norm on them.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: authored directly in `ForTauCeti`; it has had no prior home.
* Extraction class: **authored in place** for the Tau Ceti staging layer.
* Original authors / copyright: Jon Crall, Claude Opus 5; Copyright (c) 2026
  Kitware, Inc.; Apache 2.0.
* Spectra influence: **none** — this module imports only Mathlib and sibling
  `ForTauCeti` staging modules.
-/

public section

namespace TauCeti

open scoped ENNReal

universe u v w

section Base

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E H : Type v} {F G : Type w}
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

open scoped Classical in
/-- **The compact operators, gauged by the operator norm**, as an operator ideal
family.  The gauge is `∞` off the compact operators, which is how
`OperatorIdealFamily` records the carrier. -/
@[expose]
noncomputable def compactOperatorIdealFamily (𝕜 : Type u) [RCLike 𝕜] :
    OperatorIdealFamily.{u, v, w} 𝕜 where
  gauge A := if IsCompactOperator A then ‖A‖ₑ else ⊤
  gauge_add_le A B := by
    classical
    by_cases hA : IsCompactOperator A
    · by_cases hB : IsCompactOperator B
      · have hAB : IsCompactOperator (A + B) := hA.add hB
        simp only [ite_eq_left hA, ite_eq_left hB, ite_eq_left hAB]
        simpa [enorm_eq_nnnorm, ← ENNReal.coe_add] using nnnorm_add_le A B
      · simp [ite_eq_right hB]
    · simp [ite_eq_right hA]
  gauge_smul c A := by
    classical
    rcases eq_or_ne c 0 with rfl | hc
    · have hz : IsCompactOperator ((0 : 𝕜) • A) := by
        rw [zero_smul]; exact isCompactOperator_zero
      have h1 : ‖((0 : 𝕜) • A)‖ₑ = 0 := by
        rw [zero_smul]; simp [enorm_eq_nnnorm]
      have h2 : ‖(0 : 𝕜)‖ₑ = 0 := by simp [enorm_eq_nnnorm]
      rw [ite_eq_left hz, h1, h2, zero_mul]
    · by_cases hA : IsCompactOperator A
      · have hcA : IsCompactOperator (c • A) := hA.smul c
        simp only [ite_eq_left hA, ite_eq_left hcA]
        simp [enorm_eq_nnnorm, nnnorm_smul]
      · have hcA : ¬ IsCompactOperator (c • A) := by
          intro h
          refine hA ?_
          have h' : IsCompactOperator (c⁻¹ • (c • A)) := h.smul c⁻¹
          rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h'
        -- The `if` condition normalises to the bare-function form `c • ⇑A`, which
        -- `ite_eq_right hcA` no longer matches.
        have hcA' : ¬ IsCompactOperator (c • ⇑A) := by simpa using hcA
        simp [ite_eq_right hA, ite_eq_right hcA', ENNReal.mul_top, hc]
  enorm_le_gauge A := by
    classical
    by_cases hA : IsCompactOperator A
    · simp [ite_eq_left hA]
    · simp [ite_eq_right hA]
  gauge_comp_le L A R := by
    classical
    by_cases hA : IsCompactOperator A
    · have hcomp : IsCompactOperator (L ∘L A ∘L R) :=
        (hA.comp_clm R).clm_comp L
      simp only [ite_eq_left hA, ite_eq_left hcomp]
      exact (operatorNormIdealFamily.{u, v, w} 𝕜).gauge_comp_le L A R
    · simp only [ite_eq_right hA]
      by_cases hL : L = 0
      · have hzero : L ∘L A ∘L R = 0 := by
          rw [hL, ContinuousLinearMap.zero_comp]
        have hz : IsCompactOperator (L ∘L A ∘L R) := by
          rw [hzero]; exact isCompactOperator_zero
        have hz0 : ‖L ∘L A ∘L R‖ₑ = 0 := by
          rw [hzero]; simp [enorm_eq_nnnorm]
        rw [ite_eq_left hz, hz0]
        exact zero_le
      by_cases hR : R = 0
      · have hzero : L ∘L A ∘L R = 0 := by
          rw [hR, ContinuousLinearMap.comp_zero, ContinuousLinearMap.comp_zero]
        have hz : IsCompactOperator (L ∘L A ∘L R) := by
          rw [hzero]; exact isCompactOperator_zero
        have hz0 : ‖L ∘L A ∘L R‖ₑ = 0 := by
          rw [hzero]; simp [enorm_eq_nnnorm]
        rw [ite_eq_left hz, hz0]
        exact zero_le
      · have hLe : ‖L‖ₑ ≠ 0 := by
          simp only [enorm_eq_nnnorm, ne_eq, ENNReal.coe_eq_zero, nnnorm_eq_zero]
          exact hL
        have hRe : ‖R‖ₑ ≠ 0 := by
          simp only [enorm_eq_nnnorm, ne_eq, ENNReal.coe_eq_zero, nnnorm_eq_zero]
          exact hR
        rw [ENNReal.mul_top hLe, ENNReal.top_mul hRe]
        exact le_top

open scoped Classical in
/-- The compact family's gauge, unfolded. -/
theorem gauge_compactOperatorIdealFamily (A : E →L[𝕜] F) :
    (compactOperatorIdealFamily.{u, v, w} 𝕜).gauge A =
      if IsCompactOperator A then ‖A‖ₑ else ⊤ := (rfl)

/-- **Membership in the compact ideal is compactness.** -/
theorem mem_carrier_compactOperatorIdealFamily {A : E →L[𝕜] F} :
    A ∈ (compactOperatorIdealFamily.{u, v, w} 𝕜).carrier ↔ IsCompactOperator A := by
  classical
  rw [OperatorIdealFamily.mem_carrier_iff, gauge_compactOperatorIdealFamily]
  by_cases hA : IsCompactOperator A
  · simp only [ite_eq_left hA, ne_eq, enorm_ne_top, not_false_eq_true, true_iff]
    exact hA
  · simp [hA]

/-- On the ideal, the gauge is the operator norm; the compact family differs from
`operatorNormIdealFamily` only in its carrier. -/
theorem gauge_compactOperatorIdealFamily_of_isCompactOperator
    {A : E →L[𝕜] F} (hA : IsCompactOperator A) :
    (compactOperatorIdealFamily.{u, v, w} 𝕜).gauge A = ‖A‖ₑ := by
  classical
  rw [gauge_compactOperatorIdealFamily, ite_eq_left hA]

/-- The ideal of the compact family, as a normed space, is isometric to Mathlib's
submodule of compact operators.  This is what carries completeness across: the
gauge is the operator norm on members, so the two norms agree. -/
noncomputable def compactOperatorIdealFamilyElemEquiv :
    (compactOperatorIdealFamily.{u, v, w} 𝕜).Elem E F ≃ₗᵢ[𝕜]
      ↥(_root_.compactOperator (RingHom.id 𝕜) E F) where
  toFun A := ⟨A.val, mem_carrier_compactOperatorIdealFamily.mp A.val_mem⟩
  invFun A := OperatorIdealFamily.Elem.mk
    (N := compactOperatorIdealFamily 𝕜)
    (mem_carrier_compactOperatorIdealFamily.mpr A.2)
  left_inv A := by
    refine OperatorIdealFamily.Elem.ext ?_
    exact OperatorIdealFamily.Elem.val_mk
      (N := compactOperatorIdealFamily 𝕜) A.val_mem
  right_inv A := by
    refine Subtype.ext ?_
    exact OperatorIdealFamily.Elem.val_mk
      (N := compactOperatorIdealFamily 𝕜)
      (mem_carrier_compactOperatorIdealFamily.mpr A.2)
  map_add' A B := by
    refine Subtype.ext ?_
    exact OperatorIdealFamily.Elem.val_add A B
  map_smul' c A := by
    refine Subtype.ext ?_
    exact OperatorIdealFamily.Elem.val_smul c A
  norm_map' A := by
    have hA : IsCompactOperator A.val :=
      mem_carrier_compactOperatorIdealFamily.mp A.val_mem
    change ‖A.val‖ = ‖A‖
    rw [OperatorIdealFamily.Elem.norm_def,
      gauge_compactOperatorIdealFamily_of_isCompactOperator hA, toReal_enorm]

/-- **The compact ideal is complete.**  The compact operators are closed for the
operator norm, and on them the ideal norm *is* the operator norm, so the ideal
inherits completeness from the ambient operator space. -/
instance instIsCompleteCompactOperatorIdealFamily :
    (compactOperatorIdealFamily.{u, v, w} 𝕜).IsComplete where
  completeSpace := by
    intro E F _ _ _ _ _ _
    have hclosed : IsClosed
        (_root_.compactOperator (RingHom.id 𝕜) E F : Set (E →L[𝕜] F)) :=
      isClosed_setOfPred_isCompactOperator
    have : CompleteSpace
        ↥(_root_.compactOperator (RingHom.id 𝕜) E F) :=
      hclosed.completeSpace_coe
    exact (compactOperatorIdealFamilyElemEquiv
      (𝕜 := 𝕜) (E := E) (F := F)).toIsometryEquiv.completeSpace

end Base

section Symmetric

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- **The compact operators as a symmetric ideal family.**

Adjoint-invariance of the carrier is Schauder's theorem
(`ContinuousLinearMap.isCompactOperator_adjoint_iff`); adjoint-invariance of the
gauge is then the isometry of the adjoint, exactly as for the operator-norm
family. -/
@[expose]
noncomputable def compactOperatorFamily (𝕜 : Type u) [RCLike 𝕜] :
    SymmetricOperatorIdealFamily.{u, v} 𝕜 where
  toOperatorIdealFamily := compactOperatorIdealFamily 𝕜
  gauge_adjoint A := by
    classical
    by_cases hA : IsCompactOperator A
    · have hAdj : IsCompactOperator (ContinuousLinearMap.adjoint A) :=
        ContinuousLinearMap.isCompactOperator_adjoint hA
      rw [gauge_compactOperatorIdealFamily, gauge_compactOperatorIdealFamily,
        ite_eq_left hAdj, ite_eq_left hA, ← ofReal_norm, ← ofReal_norm,
        ContinuousLinearMap.adjoint.norm_map]
    · have hAdj : ¬ IsCompactOperator (ContinuousLinearMap.adjoint A) := fun h =>
        hA (ContinuousLinearMap.isCompactOperator_adjoint_iff.mp h)
      rw [gauge_compactOperatorIdealFamily, gauge_compactOperatorIdealFamily,
        ite_eq_right hAdj, ite_eq_right hA]

/-- Completeness transfers to the symmetric view, which shares its underlying
family.  Restated rather than inherited for the reason recorded on
`operatorNormFamily`: the base instance is at three independent universes and the
symmetric family constrains the last two to be equal. -/
instance : (compactOperatorFamily.{u, v} 𝕜).toOperatorIdealFamily.IsComplete :=
  inferInstanceAs (compactOperatorIdealFamily.{u, v, v} 𝕜).IsComplete

/-- The symmetric compact family has the same gauge as the plain one. -/
theorem gauge_compactOperatorFamily_of_isCompactOperator
    {A : E →L[𝕜] F} (hA : IsCompactOperator A) :
    (compactOperatorFamily.{u, v} 𝕜).gauge A = ‖A‖ₑ :=
  gauge_compactOperatorIdealFamily_of_isCompactOperator hA

/-- Membership in the symmetric compact family is compactness. -/
theorem mem_carrier_compactOperatorFamily {A : E →L[𝕜] F} :
    A ∈ (compactOperatorFamily.{u, v} 𝕜).toOperatorIdealFamily.carrier ↔
      IsCompactOperator A :=
  mem_carrier_compactOperatorIdealFamily

end Symmetric

end TauCeti
