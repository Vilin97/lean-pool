/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.RouteAGradientProducerUniform
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientGluedTwoRegimeMorrey
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientLargeCells

/-!
# The every-cell bound of the symmetric carrier, in its two regimes

The uniform Route A gradient conclusion asks for one integrable weak pressure
gradient on the inner parabolic ball whose Morrey cells are bounded at **every**
centre and **every** positive radius by a single finite constant.  That bound
cannot be proved by one uniform argument: the slice estimate at a cell's own
scale needs the doubled cell to stay inside the region where the solution is
controlled, which fails once the cell is large compared with its distance to the
boundary of the carrier.

The bound therefore has two regimes.  Below the margin scale `r₀` the cell is
controlled at its own radius; at or above `r₀` the cell power integral is at
most the integral over the whole carrier, and since the growth exponent
`5 (1 - (6/5)/κ)` is nonnegative for `6/5 ≤ κ`, that constant bound is itself of
the required growth form, at the price of the explicit factor
`r₀ ^ (-(5 (1 - (6/5)/κ)))`.

The margin scale of this carrier is `R / 3`: a cell of radius at most `R / 3`
that meets the inner ball `Metric.ball z₀ (R / 2)` has its doubled parabolic
cylinder inside `Metric.ball z₀ (2 * R)`, which is the region the hypotheses
control.
-/

@[expose] public section

section

/-!
# Pressure Gradient HGCloser Transfer

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

open CKN.Core.HeatPotential MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open scoped ENNReal NNReal Topology


namespace CKN.Core.Step4

/-! # Pressure-gradient Morrey membership for an identified field

The cell estimate applies to the same integrable weak pressure gradient
produced on the inner parabolic ball. Its finite bound is uniform over
components, cell centres, and radii, but may depend on the solution.
-/

/-- Convert a glued integrable weak pressure gradient with bounds on every
Morrey cell into the uniform Route A gradient conclusion. -/
theorem routeA_gradient_of_glued_field_cell_bounds
    (hGlued :
      ∀ q τ : ℝ, 5 / 2 < q → 25 / 3 ≤ τ → τ ≤ 25 →
        ∀ {Ω : Set Vec3} {I : Set ℝ}
          {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
          {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
          IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
          ∀ (z₀ : ParabolicPoint) (R : ℝ), 0 < R →
          Metric.ball z₀ (2 * R) ⊆ spaceTimeSet Ω I →
          morreyVecMem 3 τ (Metric.ball z₀ R) u →
          (∀ i : Fin 3, morreyVecMem 2 (25 / 8 : ℝ)
            (Metric.ball z₀ R) (fun z => Du z i)) →
          ∃ Dp : ParabolicPoint → Vec3,
            (∀ i : Fin 3, AEMeasurable (fun z => Dp z i)
              (volume.restrict (Metric.ball z₀ (R / 2)))) ∧
            (∀ i : Fin 3, Integrable (fun z => Dp z i)
              (volume.restrict (Metric.ball z₀ (R / 2)))) ∧
            (∀ i : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ,
              ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ →
              tsupport ψ ⊆ parabolicHomeomorph.symm ⁻¹' Metric.ball z₀ (R / 2) →
              (∫ z : ParabolicPoint, p z * spatialPartial ψ i z) =
                -(∫ z : ParabolicPoint, Dp z i * ψ z)) ∧
            ∃ Ccell : ℝ, ∀ i : Fin 3, ∀ z : ParabolicPoint,
              ∀ r : {r : ℝ // 0 < r},
                morreyCell (6 / 5 : ℝ) (min ((1 / τ + 8 / 25)⁻¹) q)
                  ((Metric.ball z₀ (R / 2)).indicator (fun w => Dp w i)) z r.1 ≤
                  ENNReal.ofReal Ccell) : routeAGradientProducerUniform := by
  intro q τ hq hτ hτ' Ω I u Du p f hsol z₀ R hR hdom hu hDu
  obtain ⟨Dp, hAE, _hInt, hweak, Ccell, hbound⟩ :=
    hGlued q τ hq hτ hτ' hsol z₀ R hR hdom hu hDu
  refine ⟨Dp, hAE, hweak, ?_⟩
  exact pressure_gradient_morreyVecMem_of_cell_bounds_real
    (C := Ccell) (routeA_uniform_kappa_min_lower hq hτ)
    (lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top) hbound

end CKN.Core.Step4

end

open MeasureTheory Set
open scoped ENNReal
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey

noncomputable section
namespace CKN.Core.Step4

/-- The integral of a field over a measurable carrier is unchanged by
restricting the field to that carrier. -/
theorem lintegral_carrier_indicator_eq
    {S : Set ParabolicPoint} (hS : MeasurableSet S)
    (g : ParabolicPoint → ℝ) (P : ℝ) :
    (∫⁻ w in S, ENNReal.ofReal |S.indicator g w| ^ P) =
      ∫⁻ w in S, ENNReal.ofReal |g w| ^ P := by
  refine lintegral_congr_ae ?_
  filter_upwards [ae_restrict_mem hS] with w hw
  rw [Set.indicator_of_mem hw]

/-- The single finite every-cell constant of the uniform Route A conclusion,
assembled from the margin-safe cells and the whole-carrier integral.  The field
is fixed before the two integral constants, and both constants are bound after
it; nothing here quantifies a bound before the field. -/
theorem exists_routeA_cell_constant_of_two_regime_bounds
    {z₀ : ParabolicPoint} {R κ r₀ : ℝ} {Dp : ParabolicPoint → Vec3} {A B : ℝ≥0∞}
    (hκ : (6 : ℝ) / 5 ≤ κ) (hr₀ : 0 < r₀) (hA : A < ⊤) (hB : B < ⊤)
    (hsmall : ∀ i : Fin 3, ∀ (z : ParabolicPoint) (r : ℝ), 0 < r → r ≤ r₀ →
      cylinderPowerIntegral (6 / 5 : ℝ)
          ((Metric.ball z₀ (R / 2)).indicator (fun w => Dp w i)) z r ≤
        A * ENNReal.ofReal (r ^ (5 * (1 - (6 / 5 : ℝ) / κ))))
    (hglobal : ∀ i : Fin 3,
      (∫⁻ w in Metric.ball z₀ (R / 2),
        ENNReal.ofReal |Dp w i| ^ (6 / 5 : ℝ)) ≤ B) :
    ∃ Ccell : ℝ, ∀ i : Fin 3, ∀ z : ParabolicPoint, ∀ r : {r : ℝ // 0 < r},
      morreyCell (6 / 5 : ℝ) κ
        ((Metric.ball z₀ (R / 2)).indicator (fun w => Dp w i)) z r.1 ≤
        ENNReal.ofReal Ccell := by
  have hP : (0 : ℝ) < 6 / 5 := by norm_num
  have hS : MeasurableSet (Metric.ball z₀ (R / 2)) := measurableSet_ball
  set K : ℝ≥0∞ :=
    (A + B * ENNReal.ofReal (r₀ ^ (-(5 * (1 - (6 / 5 : ℝ) / κ))))) ^
      (1 / (6 / 5 : ℝ) : ℝ) with hK
  have hKtop : K < ⊤ := two_regime_morrey_constant_lt_top hP hA hB
  refine ⟨K.toReal, ?_⟩
  intro i z r
  have hvan : ∀ w, w ∉ Metric.ball z₀ (R / 2) →
      (Metric.ball z₀ (R / 2)).indicator (fun w => Dp w i) w = 0 :=
    fun w hw => Set.indicator_of_notMem hw _
  have hglob : (∫⁻ w in Metric.ball z₀ (R / 2),
      ENNReal.ofReal |(Metric.ball z₀ (R / 2)).indicator
        (fun w => Dp w i) w| ^ (6 / 5 : ℝ)) ≤ B := by
    rw [lintegral_carrier_indicator_eq hS]
    exact hglobal i
  have hcell := morreyCell_le_two_regimes hS hvan hP hκ hr₀ hglob
    (hsmall i) z r.2
  rw [ENNReal.ofReal_toReal hKtop.ne]
  exact hcell

/-- The uniform Route A gradient conclusion from a glued field whose every-cell
bound is supplied in the two regimes.  The field comes first; the two integral
constants and their finiteness are bound after it, and every cell clause refers
to that same field. -/
theorem routeA_gradient_of_two_regime_glued_field
    (hGlued :
      ∀ q τ : ℝ, 5 / 2 < q → 25 / 3 ≤ τ → τ ≤ 25 →
        ∀ {Ω : Set Vec3} {I : Set ℝ}
          {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
          {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
          IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
          ∀ (z₀ : ParabolicPoint) (R : ℝ), 0 < R →
          Metric.ball z₀ (2 * R) ⊆ spaceTimeSet Ω I →
          morreyVecMem 3 τ (Metric.ball z₀ R) u →
          (∀ i : Fin 3, morreyVecMem 2 (25 / 8 : ℝ)
            (Metric.ball z₀ R) (fun z => Du z i)) →
          ∃ Dp : ParabolicPoint → Vec3,
            (∀ i : Fin 3, AEMeasurable (fun z => Dp z i)
              (volume.restrict (Metric.ball z₀ (R / 2)))) ∧
            (∀ i : Fin 3, Integrable (fun z => Dp z i)
              (volume.restrict (Metric.ball z₀ (R / 2)))) ∧
            (∀ i : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ,
              ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ →
              tsupport ψ ⊆ parabolicHomeomorph.symm ⁻¹' Metric.ball z₀ (R / 2) →
              (∫ z : ParabolicPoint, p z * spatialPartial ψ i z) =
                -(∫ z : ParabolicPoint, Dp z i * ψ z)) ∧
            ∃ A B : ℝ≥0∞, A < ⊤ ∧ B < ⊤ ∧
              (∀ i : Fin 3, ∀ (z : ParabolicPoint) (r : ℝ), 0 < r → r ≤ R / 3 →
                cylinderPowerIntegral (6 / 5 : ℝ)
                    ((Metric.ball z₀ (R / 2)).indicator (fun w => Dp w i)) z r ≤
                  A * ENNReal.ofReal
                    (r ^ (5 * (1 - (6 / 5 : ℝ) /
                      min ((1 / τ + 8 / 25)⁻¹) q)))) ∧
              (∀ i : Fin 3, (∫⁻ w in Metric.ball z₀ (R / 2),
                ENNReal.ofReal |Dp w i| ^ (6 / 5 : ℝ)) ≤ B)) :
    routeAGradientProducerUniform := by
  refine routeA_gradient_of_glued_field_cell_bounds ?_
  intro q τ hq hτ hτ' Ω I u Du p f hsol z₀ R hR hdom hu hDu
  obtain ⟨Dp, hAE, hInt, hweak, A, B, hA, hB, hsmall, hglobal⟩ :=
    hGlued q τ hq hτ hτ' hsol z₀ R hR hdom hu hDu
  refine ⟨Dp, hAE, hInt, hweak, ?_⟩
  exact exists_routeA_cell_constant_of_two_regime_bounds
    (routeA_uniform_kappa_min_lower hq hτ) (by positivity) hA hB hsmall hglobal

/-- The same every-cell constant, assembled from the two regimes separately: the
small-cell growth bound below the margin scale, and the established large-cell
normalization of the whole-carrier integral at or above it.  This is the form in
which the two halves are read off independently, and its constant is the sum of
the two contributions rather than the power of a sum. -/
theorem exists_routeA_cell_constant_of_small_cells_and_carrier_integral
    {z₀ : ParabolicPoint} {R κ r₀ : ℝ} {Dp : ParabolicPoint → Vec3} {A B : ℝ≥0∞}
    (hκ : (6 : ℝ) / 5 ≤ κ) (hr₀ : 0 < r₀) (hA : A < ⊤) (hB : B < ⊤)
    (hsmall : ∀ i : Fin 3, ∀ (z : ParabolicPoint) (r : ℝ), 0 < r → r ≤ r₀ →
      cylinderPowerIntegral (6 / 5 : ℝ)
          ((Metric.ball z₀ (R / 2)).indicator (fun w => Dp w i)) z r ≤
        A * ENNReal.ofReal (r ^ (5 * (1 - (6 / 5 : ℝ) / κ))))
    (hglobal : ∀ i : Fin 3,
      (∫⁻ w in Metric.ball z₀ (R / 2),
        ENNReal.ofReal |Dp w i| ^ (6 / 5 : ℝ)) ≤ B) :
    ∃ Ccell : ℝ, ∀ i : Fin 3, ∀ z : ParabolicPoint, ∀ r : {r : ℝ // 0 < r},
      morreyCell (6 / 5 : ℝ) κ
        ((Metric.ball z₀ (R / 2)).indicator (fun w => Dp w i)) z r.1 ≤
        ENNReal.ofReal Ccell := by
  have hP : (0 : ℝ) < 6 / 5 := by norm_num
  set K : ℝ≥0∞ :=
    A ^ (5 / 6 : ℝ) +
      ENNReal.ofReal (r₀ ^ (5 / κ - 25 / 6)) * B ^ (5 / 6 : ℝ) with hK
  have hKtop : K < ⊤ := by
    refine ENNReal.add_lt_top.mpr ⟨?_, ?_⟩
    · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hA.ne
    · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hB.ne)
  refine ⟨K.toReal, ?_⟩
  intro i z r
  rw [ENNReal.ofReal_toReal hKtop.ne]
  rcases le_total r.1 r₀ with hle | hge
  · have hcell := morreyCell_le_of_cylinderPowerIntegral_growth hP r.2
      (hsmall i z r.1 r.2 hle)
    rw [show (1 / (6 / 5 : ℝ) : ℝ) = (5 / 6 : ℝ) by norm_num] at hcell
    exact hcell.trans le_self_add
  · refine le_trans (pressure_gradient_ball_large_cell_le (f := fun w => Dp w i)
      (R := R / 2) z₀ hκ hr₀ hge z) ?_
    refine le_trans (mul_le_mul' (le_refl (ENNReal.ofReal (r₀ ^ (5 / κ - 25 / 6))))
      (ENNReal.rpow_le_rpow (hglobal i) (by norm_num : (0 : ℝ) ≤ 5 / 6))) ?_
    exact le_add_self

end CKN.Core.Step4
