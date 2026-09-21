/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.DifferenceQuotientWeakDerivative

/-! # Linear algebra and integration by parts for actual difference quotients

Translations preserve Euclidean L². Their inverse is the opposite translation,
so the difference-quotient adjoint is minus the quotient with opposite step.
-/

@[expose] public noncomputable section
open MeasureTheory

namespace AlmostSchur

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Euclidean translation as a genuine L² linear isometry. -/
def translationL2 (a : E) : Lp ℝ 2 (volume : Measure E) →ₗᵢ[ℝ] Lp ℝ 2 (volume : Measure E) :=
  Lp.compMeasurePreservingₗᵢ ℝ (fun x => x + a) (measurePreserving_add_right volume a)

/-- Opposite translation is an exact inverse on L² classes. -/
theorem translationL2_neg_apply (a : E) (u : Lp ℝ 2 (volume : Measure E)) :
    translationL2 a (translationL2 (-a) u) = u := by
  change Lp.compMeasurePreserving _ _ (Lp.compMeasurePreserving _ _ u) = u
  rw [← Lp.compMeasurePreserving_comp_apply]
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving u
    ((measurePreserving_add_right volume (-a)).comp (measurePreserving_add_right volume a))]
    with x hx
  simpa [Function.comp_def] using hx

/-- The adjoint of translation by `a` is translation by `-a`. -/
theorem inner_translationL2 (a : E) (u q : Lp ℝ 2 (volume : Measure E)) :
    inner ℝ (translationL2 a u) q = inner ℝ u (translationL2 (-a) q) := by
  calc
    _ = inner ℝ (translationL2 a u) (translationL2 a (translationL2 (-a) q)) := by
      rw [translationL2_neg_apply]
    _ = _ := (translationL2 a).inner_map_map u (translationL2 (-a) q)

/-- The actual difference quotient is a bounded linear operator for every fixed step. -/
def directionalDifferenceQuotientL (v : E) (h : ℝ) :
    Lp ℝ 2 (volume : Measure E) →L[ℝ] Lp ℝ 2 (volume : Measure E) :=
  h⁻¹ • ((translationL2 (h • v)).toContinuousLinearMap - ContinuousLinearMap.id ℝ _)

theorem directionalDifferenceQuotientL_apply (v : E) (h : ℝ)
    (u : Lp ℝ 2 (volume : Measure E)) :
    directionalDifferenceQuotientL v h u = directionalDifferenceQuotient u v h := rfl

/-- Discrete integration by parts holds for arbitrary L² functions, including zero step. -/
theorem inner_directionalDifferenceQuotient_adjoint
    (u q : Lp ℝ 2 (volume : Measure E)) (v : E) (h : ℝ) :
    inner ℝ (directionalDifferenceQuotient u v h) q =
      -inner ℝ u (directionalDifferenceQuotient q v (-h)) := by
  change inner ℝ (h⁻¹ • (translationL2 (h • v) u - u)) q =
    -inner ℝ u ((-h)⁻¹ • (translationL2 ((-h) • v) q - q))
  rw [real_inner_smul_left, inner_sub_left, real_inner_smul_right, inner_sub_right,
    inner_translationL2]
  simp only [neg_inv, neg_smul]
  ring

/-- The elementary operator estimate; uniform estimates as `h → 0` need derivative information. -/
theorem norm_directionalDifferenceQuotient_le
    (u : Lp ℝ 2 (volume : Measure E)) (v : E) (h : ℝ) :
    ‖directionalDifferenceQuotient u v h‖ ≤ 2 * |h|⁻¹ * ‖u‖ := by
  change ‖h⁻¹ • (translationL2 (h • v) u - u)‖ ≤ _
  rw [norm_smul]
  calc
    _ ≤ ‖h⁻¹‖ * (‖translationL2 (h • v) u‖ + ‖u‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _)
    _ = _ := by rw [(translationL2 (h • v)).norm_map, norm_inv, Real.norm_eq_abs]; ring

end AlmostSchur
