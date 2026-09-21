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

public import LeanPool.PoincareGeometry.AlmostSchur.DifferenceQuotientAlgebra
public import LeanPool.PoincareGeometry.AlmostSchur.L2Multiplier

/-! # The discrete product rule for bounded L² multipliers

The translated coefficient and its actual difference quotient occur explicitly.
All products are actual L² classes with proved representative identities.
-/

@[expose] public noncomputable section
open MeasureTheory Filter

namespace AlmostSchur

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Translation preserves measurable bounded coefficient hypotheses. -/
theorem bounded_coefficient_translate (a : E → ℝ)
    (ha : AEStronglyMeasurable a (volume : Measure E))
    (C : ℝ) (hb : ∀ᵐ x ∂(volume : Measure E), ‖a x‖ ≤ C) (s : E) :
    AEStronglyMeasurable (fun x => a (x + s)) (volume : Measure E) ∧
      ∀ᵐ x ∂(volume : Measure E), ‖a (x + s)‖ ≤ C :=
  ⟨ha.comp_quasiMeasurePreserving (measurePreserving_add_right volume s).quasiMeasurePreserving,
    (measurePreserving_add_right volume s).quasiMeasurePreserving.ae hb⟩

/-- The representative bound gives the expected L² multiplier estimate. -/
theorem norm_boundedL2Multiplier_apply_le (a : E → ℝ)
    (ha : AEStronglyMeasurable a (volume : Measure E))
    (C : ℝ) (hb : ∀ᵐ x ∂(volume : Measure E), ‖a x‖ ≤ C)
    (u : Lp ℝ 2 (volume : Measure E)) :
    ‖boundedL2Multiplier a ha C hb u‖ ≤ C * ‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [boundedL2Multiplier_ae_eq a ha C hb u, hb] with x hx hbx
  rw [hx, norm_mul]
  exact mul_le_mul_of_nonneg_right hbx (norm_nonneg _)

/-- The discrete product rule is an equality of genuine L² classes. -/
theorem directionalDifferenceQuotient_bounded_mul
    (a : E → ℝ) (ha : AEStronglyMeasurable a (volume : Measure E))
    (C : ℝ) (hb : ∀ᵐ x ∂(volume : Measure E), ‖a x‖ ≤ C)
    (u : Lp ℝ 2 (volume : Measure E)) (v : E) (h D : ℝ)
    (hD : ∀ᵐ x ∂(volume : Measure E), ‖h⁻¹ * (a (x + h • v) - a x)‖ ≤ D) :
    directionalDifferenceQuotient (boundedL2Multiplier a ha C hb u) v h =
      boundedL2Multiplier (fun x => a (x + h • v))
        (bounded_coefficient_translate a ha C hb (h • v)).1 C
        (bounded_coefficient_translate a ha C hb (h • v)).2 (directionalDifferenceQuotient u v h) +
      boundedL2Multiplier (fun x => h⁻¹ * (a (x + h • v) - a x))
        (aestronglyMeasurable_const.mul
          ((bounded_coefficient_translate a ha C hb (h • v)).1.sub ha)) D hD u := by
  let au := boundedL2Multiplier a ha C hb u
  have hau := boundedL2Multiplier_ae_eq a ha C hb u
  have hshift := (measurePreserving_add_right volume (h • v)).quasiMeasurePreserving.ae hau
  let ht := bounded_coefficient_translate a ha C hb (h • v)
  let Q := boundedL2Multiplier (fun x => a (x + h • v)) ht.1 C ht.2
    (directionalDifferenceQuotient u v h)
  let R := boundedL2Multiplier (fun x => h⁻¹ * (a (x + h • v) - a x))
    (aestronglyMeasurable_const.mul (ht.1.sub ha)) D hD u
  apply Lp.ext
  filter_upwards [directionalDifferenceQuotient_ae_eq au v h, hau, hshift,
    boundedL2Multiplier_ae_eq (fun x => a (x + h • v)) ht.1 C ht.2
      (directionalDifferenceQuotient u v h),
    boundedL2Multiplier_ae_eq (fun x => h⁻¹ * (a (x + h • v) - a x))
      (aestronglyMeasurable_const.mul (ht.1.sub ha)) D hD u,
    directionalDifferenceQuotient_ae_eq u v h, Lp.coeFn_add Q R]
      with x hd ha0 has hq hr hu hsum
  change directionalDifferenceQuotient au v h x = (Q + R) x
  rw [hd, hsum]
  change h⁻¹ * (au (x + h • v) - au x) = Q x + R x
  rw [hq, hr, hu]
  change h⁻¹ * (boundedL2Multiplier a ha C hb u (x + h • v) -
      boundedL2Multiplier a ha C hb u x) = _
  rw [has, ha0]
  ring

/-- The coefficient commutator is controlled independently of the quotient of `u`. -/
theorem norm_directionalDifferenceQuotient_bounded_mul_le
    (a : E → ℝ) (ha : AEStronglyMeasurable a (volume : Measure E))
    (C : ℝ) (hb : ∀ᵐ x ∂(volume : Measure E), ‖a x‖ ≤ C)
    (u : Lp ℝ 2 (volume : Measure E)) (v : E) (h D : ℝ)
    (hD : ∀ᵐ x ∂(volume : Measure E), ‖h⁻¹ * (a (x + h • v) - a x)‖ ≤ D) :
    ‖directionalDifferenceQuotient (boundedL2Multiplier a ha C hb u) v h‖ ≤
      C * ‖directionalDifferenceQuotient u v h‖ + D * ‖u‖ := by
  rw [directionalDifferenceQuotient_bounded_mul a ha C hb u v h D hD]
  exact (norm_add_le _ _).trans (add_le_add
    (norm_boundedL2Multiplier_apply_le _ _ C _ _)
    (norm_boundedL2Multiplier_apply_le _ _ D hD u))

end AlmostSchur
