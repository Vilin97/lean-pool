/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Measurability.Init

/-!
Quantitative operator algebra for the actual fixed-space endpoint solve.
The input called `R` below is an inverse operator; the transverse specialization
constructs it by coercivity and discharges all of its norm bounds.
-/

@[expose] public section


noncomputable section


namespace EulerCoerciveEndpointBounds

open ContinuousLinearMap

variable {S E V F G W : Type*}
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem norm_comp_sub_le (A B : F →L[ℝ] G) (C D : W →L[ℝ] F) :
    ‖A.comp C - B.comp D‖ ≤ ‖A - B‖ * ‖C‖ + ‖B‖ * ‖C - D‖ := by
  have he : A.comp C - B.comp D = (A - B).comp C + B.comp (C - D) := by
    ext x
    simp only [comp_apply, sub_apply, add_apply, map_sub]
    abel
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add (opNorm_comp_le _ _) (opNorm_comp_le _ _))

/-- The actual algebraic stationary correction in a fixed coordinate space. -/
def correctionOperator (D : S →L[ℝ] E) (R : S →L[ℝ] S) (A : E →L[ℝ] E) : E →L[ℝ] E :=
  D.comp (R.comp (D.adjoint.comp A))

/-- Endpoint operator, given by `L - (correctionOperator D R A).comp L`. -/
def endpointOperator (D : S →L[ℝ] E) (R : S →L[ℝ] S) (A : E →L[ℝ] E)
    (L : V →L[ℝ] E) : V →L[ℝ] E := L - (correctionOperator D R A).comp L

theorem correctionOperator_norm_le (D : S →L[ℝ] E) (R : S →L[ℝ] S) (A : E →L[ℝ] E)
    (d r a : ℝ) (hd : ‖D‖ ≤ d) (hr : ‖R‖ ≤ r) (ha : ‖A‖ ≤ a) :
    ‖correctionOperator D R A‖ ≤ d ^ 2 * r * a := by
  have hd0 := (norm_nonneg D).trans hd
  have hr0 := (norm_nonneg R).trans hr
  have ha0 := (norm_nonneg A).trans ha
  have hDA : ‖D.adjoint.comp A‖ ≤ d * a := by
    apply (opNorm_comp_le _ _).trans
    rw [LinearIsometryEquiv.norm_map]
    exact mul_le_mul hd ha (norm_nonneg _) hd0
  have hRDA : ‖R.comp (D.adjoint.comp A)‖ ≤ r * (d * a) :=
    (opNorm_comp_le _ _).trans (mul_le_mul hr hDA (norm_nonneg _) hr0)
  exact ((opNorm_comp_le _ _).trans
    (mul_le_mul hd hRDA (norm_nonneg _) hd0)).trans_eq (by ring)

theorem correctionOperator_sub_norm_le
    (D D' : S →L[ℝ] E) (R R' : S →L[ℝ] S) (A A' : E →L[ℝ] E)
    (d r a δd δr δa : ℝ)
    (hd : ‖D‖ ≤ d) (hd' : ‖D'‖ ≤ d) (hr : ‖R‖ ≤ r) (hr' : ‖R'‖ ≤ r)
    (ha : ‖A‖ ≤ a) (_ha' : ‖A'‖ ≤ a)
    (hδd : ‖D - D'‖ ≤ δd) (hδr : ‖R - R'‖ ≤ δr) (hδa : ‖A - A'‖ ≤ δa) :
    ‖correctionOperator D R A - correctionOperator D' R' A'‖ ≤
      2 * d * r * a * δd + d ^ 2 * a * δr + d ^ 2 * r * δa := by
  have hd0 := (norm_nonneg D).trans hd
  have hr0 := (norm_nonneg R).trans hr
  have ha0 := (norm_nonneg A).trans ha
  have hδd0 := (norm_nonneg (D-D')).trans hδd
  have hδr0 := (norm_nonneg (R-R')).trans hδr
  have hδa0 := (norm_nonneg (A-A')).trans hδa
  have hDA : ‖D.adjoint.comp A‖ ≤ d * a := by
    apply (opNorm_comp_le _ _).trans
    rw [LinearIsometryEquiv.norm_map]
    exact mul_le_mul hd ha (norm_nonneg _) hd0
  have hDAδ : ‖D.adjoint.comp A - D'.adjoint.comp A'‖ ≤ δd * a + d * δa := by
    apply (norm_comp_sub_le _ _ _ _).trans
    have hh : ‖D.adjoint - D'.adjoint‖ = ‖D-D'‖ := by
      rw [← map_sub, LinearIsometryEquiv.norm_map]
    rw [hh, LinearIsometryEquiv.norm_map]
    exact add_le_add (mul_le_mul hδd ha (norm_nonneg _) hδd0)
      (mul_le_mul hd' hδa (norm_nonneg _) hd0)
  have hRDA : ‖R.comp (D.adjoint.comp A)‖ ≤ r * (d * a) :=
    (opNorm_comp_le _ _).trans (mul_le_mul hr hDA (norm_nonneg _) hr0)
  have hRDAδ : ‖R.comp (D.adjoint.comp A) - R'.comp (D'.adjoint.comp A')‖ ≤
      δr * (d * a) + r * (δd * a + d * δa) := by
    apply (norm_comp_sub_le _ _ _ _).trans
    exact add_le_add (mul_le_mul hδr hDA (norm_nonneg _) hδr0)
      (mul_le_mul hr' hDAδ (norm_nonneg _) hr0)
  apply ((norm_comp_sub_le _ _ _ _).trans
    (add_le_add (mul_le_mul hδd hRDA (norm_nonneg _) hδd0)
      (mul_le_mul hd' hRDAδ (norm_nonneg _) hd0))).trans_eq
  ring

theorem endpointOperator_norm_le (D : S →L[ℝ] E) (R : S →L[ℝ] S) (A : E →L[ℝ] E)
    (L : V →L[ℝ] E) (d r a l : ℝ)
    (hd : ‖D‖ ≤ d) (hr : ‖R‖ ≤ r) (ha : ‖A‖ ≤ a) (hl : ‖L‖ ≤ l) :
    ‖endpointOperator D R A L‖ ≤ (1 + d ^ 2 * r * a) * l := by
  have hs := correctionOperator_norm_le D R A d r a hd hr ha
  have hs0 := (norm_nonneg _).trans hs
  apply ((norm_sub_le _ _).trans (add_le_add hl ((opNorm_comp_le _ _).trans
    (mul_le_mul hs hl (norm_nonneg _) hs0)))).trans_eq
  ring

theorem endpointOperator_sub_norm_le
    (D D' : S →L[ℝ] E) (R R' : S →L[ℝ] S) (A A' : E →L[ℝ] E)
    (L L' : V →L[ℝ] E) (d r a l δd δr δa δl : ℝ)
    (hd : ‖D‖ ≤ d) (hd' : ‖D'‖ ≤ d) (hr : ‖R‖ ≤ r) (hr' : ‖R'‖ ≤ r)
    (ha : ‖A‖ ≤ a) (ha' : ‖A'‖ ≤ a) (hl : ‖L‖ ≤ l)
    (hδd : ‖D - D'‖ ≤ δd) (hδr : ‖R - R'‖ ≤ δr)
    (hδa : ‖A - A'‖ ≤ δa) (hδl : ‖L - L'‖ ≤ δl) :
    ‖endpointOperator D R A L - endpointOperator D' R' A' L'‖ ≤
      (1 + d ^ 2 * r * a) * δl +
        (2 * d * r * a * δd + d ^ 2 * a * δr + d ^ 2 * r * δa) * l := by
  have hs := correctionOperator_norm_le D' R' A' d r a hd' hr' ha'
  have hs0 := (norm_nonneg _).trans hs
  have hds := correctionOperator_sub_norm_le D D' R R' A A' d r a δd δr δa
    hd hd' hr hr' ha ha' hδd hδr hδa
  have hds0 := (norm_nonneg _).trans hds
  have hprod := (norm_comp_sub_le (correctionOperator D R A)
    (correctionOperator D' R' A') L L').trans
      (add_le_add (mul_le_mul hds hl (norm_nonneg _) hds0)
        (mul_le_mul hs hδl (norm_nonneg _) hs0))
  have he : endpointOperator D R A L - endpointOperator D' R' A' L' =
      (L-L') - ((correctionOperator D R A).comp L - (correctionOperator D' R' A').comp L') := by
    unfold endpointOperator
    abel
  rw [he]
  exact ((norm_sub_le _ _).trans (add_le_add hδl hprod)).trans_eq (by ring)

/-- The transported quadratic form used by the fixed-coordinate inverse. -/
def formOperator (D : S →L[ℝ] E) (A : E →L[ℝ] E) : S →L[ℝ] S :=
  D.adjoint.comp (A.comp D)

theorem formOperator_sub_norm_le
    (D D' : S →L[ℝ] E) (A A' : E →L[ℝ] E) (d a δd δa : ℝ)
    (hd : ‖D‖ ≤ d) (hd' : ‖D'‖ ≤ d) (ha : ‖A‖ ≤ a) (ha' : ‖A'‖ ≤ a)
    (hδd : ‖D - D'‖ ≤ δd) (hδa : ‖A - A'‖ ≤ δa) :
    ‖formOperator D A - formOperator D' A'‖ ≤ 2 * d * a * δd + d ^ 2 * δa := by
  have had : ‖D.adjoint-D'.adjoint‖ ≤ δd := by
    rw [← map_sub, LinearIsometryEquiv.norm_map]
    exact hδd
  have h := correctionOperator_sub_norm_le D.adjoint D'.adjoint A A'
    (ContinuousLinearMap.id ℝ S) (ContinuousLinearMap.id ℝ S) d a 1 δd δa 0
    (by simpa only [LinearIsometryEquiv.norm_map] using hd)
    (by simpa only [LinearIsometryEquiv.norm_map] using hd') ha ha' norm_id_le norm_id_le
    had hδa (by simp)
  simpa only [correctionOperator, adjoint_adjoint, comp_id, mul_one, mul_zero, add_zero,
    formOperator] using h

end EulerCoerciveEndpointBounds
