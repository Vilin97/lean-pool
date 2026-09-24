/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOneSidedOrigin
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientGluedMarginGeometry
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.RouteAGradientProducerUniformExponents

/-!
# The every-cell bound of the origin carrier, at the margin scale

The origin-carrier cell output asks for a bound on **every** Morrey cell of the
selected pressure gradient, at every centre and every positive radius.  The
one-sided transfer supplies it from two inputs: a growth bound on cells below a
fixed scale `ρ₀`, and the total integral on the carrier cylinder.  The scale
`ρ₀` is a free parameter of that transfer, and choosing it is exactly the choice
of where the two regimes meet.

Choosing `ρ₀ = R₁`, the radius of the carrier itself, makes the small-cell input
impossible to supply, for two independent reasons.

* In time, a cell centred at `z` with `z.2 ∈ Ioc (-(3/4) ^ 2) 0` and radius up
  to `R₁ < 3/4` has window `Ioc (z.2 - R₁ ^ 2) z.2`, which reaches below
  `-9/16 - R₁ ^ 2` and hence below `-1`.  Nothing in the hypotheses of the
  estimate controls the solution before time `-1`.
* In space, the slice estimate at a cell of radius `r` is applied on a cylinder
  of radius `2 * r`, and for `r` comparable with `R₁` that doubled ball leaves
  the ball of radius `R₀` on which the pressure slice data lives.

Choosing instead the **margin scale** `ρ₀ = (1 - R₁) / 4` removes both.  The
region the domain hypothesis controls is the closed unit cylinder, so the
governing margin is the one between the carrier radius `R₁` and `1`, not the one
between `R₁` and `R₀`.  At that scale `3 * r ≤ 1 - R₁`, so a cell meeting the
carrier has its doubled ball inside the unit ball; and `r ≤ 1/4`, so
`(2 * r) ^ 2 ≤ 1/4` and every doubled window stays inside `Ioc (-1) 0`.  Cells at
or above the margin scale are not reached by the slice estimate at all and are
bounded by the total integral on the carrier, with the explicit scale factor that
the one-sided transfer constant carries.

The margin scale must not be allowed to degenerate.  Because `R₁ < 3/4`, the
scale `(1 - R₁) / 4` lies in `[1/16, 1/4)`, bounded away from zero uniformly in
the admissible data.  A scale proportional to `R₀ - R₁` would not be: by
`oneSidedMorreyBound_scale_eq`, measuring the transfer constant at a scale `ρ₀`
instead of at `R₁` inflates the whole-carrier constant by exactly
`(R₁ / ρ₀) ^ (5 (1 - (6/5)/κ))`, and with `ρ₀ = (R₀ - R₁) / 3` that factor is
unbounded as `R₁ ↑ R₀`, which would make the comparison with the explicit
majorant of the estimate unsatisfiable at the top of the admissible range.  At
`ρ₀ = (1 - R₁) / 4` the factor is at most `12 ^ (5 (1 - (6/5)/κ))`.

Nothing else in the estimate changes: the transfer, the carrier, the field and
the conclusion are the established ones.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey
open CKN.Core.Endgame

noncomputable section
namespace CKN.Core.Step4

/-- The margin scale of the origin carrier is below a quarter, which is what
keeps every doubled window inside the unit time interval. -/
theorem originMarginScale_lt_quarter {R₁ : ℝ} (hR₁ : 0 < R₁) :
    (1 - R₁) / 4 < 1 / 4 := by
  linarith only [hR₁]

/-- The margin scale of the origin carrier is positive, and in fact at least
`1/16` on the admissible range `R₁ < 3/4`: it does not degenerate. -/
theorem originMarginScale_pos {R₁ : ℝ} (hR₁ : R₁ < 1) : 0 < (1 - R₁) / 4 := by
  linarith only [hR₁]

/-- The margin scale of the origin carrier is bounded below uniformly in the
admissible data.  This is what keeps the comparison with the explicit majorant
of the estimate from degenerating. -/
theorem originMarginScale_lower_bound {R₁ : ℝ} (hR₁quarter : R₁ < 3 / 4) :
    1 / 16 < (1 - R₁) / 4 := by
  linarith only [hR₁quarter]

/-- At the margin scale the doubled radius is still small enough for the
time-side inclusion. -/
theorem originMarginScale_double_sq_le {R₁ r : ℝ} (hR₁ : 0 < R₁) (hr : 0 < r)
    (hmargin : r ≤ (1 - R₁) / 4) : (2 * r) ^ 2 ≤ 1 / 4 := by
  have h : r < 1 / 4 := lt_of_le_of_lt hmargin (originMarginScale_lt_quarter hR₁)
  nlinarith only [hr, h]

/-- At the margin scale a cell meeting the carrier has its doubled ball inside
the unit ball. -/
theorem originMarginScale_triple_le {R₁ r : ℝ} (hR₁ : R₁ < 1)
    (hmargin : r ≤ (1 - R₁) / 4) : 3 * r ≤ 1 - R₁ := by
  linarith only [hR₁, hmargin]

/-- **Every window of a margin-scale cell lies inside the unit time interval.**
This is the satisfiability certificate of the small-cell regime: the data
hypotheses of the estimate control the solution only on `Ioc (-1) 0`, and a cell
centred anywhere in the cylinder of admissible centres, at a radius at most the
margin scale, never reaches outside that interval. -/
theorem margin_cell_window_subset_unit_time
    {r : ℝ} {z : ParabolicPoint}
    (hz : z ∈ parabolicCylinder (0 : Vec3) 0 (3 / 4))
    (hr2 : (2 * r) ^ 2 ≤ 1 / 4) :
    Ioc (z.2 - (2 * r) ^ 2) z.2 ⊆ Ioc (-1 : ℝ) 0 := by
  have hzt : 0 - (3 / 4 : ℝ) ^ 2 < z.2 ∧ z.2 ≤ 0 := ⟨hz.2.1, hz.2.2⟩
  intro s hs
  refine ⟨?_, le_trans hs.2 hzt.2⟩
  have h1 : -(9 / 16 : ℝ) < z.2 := by
    have := hzt.1
    linarith only [this]
  have hlow : z.2 - (2 * r) ^ 2 > -1 := by linarith only [h1, hr2]
  linarith only [hs.1, hlow]


/-- The origin-carrier cell output from the two regimes, with the small-cell
input taken only below a free scale `ρ₀`.  The centres are the ones the one-sided
transfer consumes, so the statement composes with the established transfer without
change; only the radius threshold moves from `R₁` to `ρ₀`. -/
theorem originCellOutput_of_margin_cell_bounds
    {R₁ κ ρ₀ : ℝ} {A B : ℝ≥0∞} {Dp : ParabolicPoint → Vec3}
    (hR₁ : 0 < R₁) (hR₁quarter : R₁ < 3 / 4) (hκ : 6 / 5 ≤ κ) (hρ₀ : 0 < ρ₀)
    (hsmall : ∀ i : Fin 3, ∀ z ∈ parabolicCylinder (0 : Vec3) 0 (3 / 4),
      ∀ r : ℝ, 0 < r → r ≤ ρ₀ →
      cylinderPowerIntegral (6 / 5 : ℝ) (fun w => Dp w i) z r ≤
        A * ENNReal.ofReal (r ^ (5 * (1 - (6 / 5 : ℝ) / κ))))
    (hglobal : ∀ i : Fin 3,
      (∫⁻ w in parabolicCylinder (0 : Vec3) 0 R₁,
        ENNReal.ofReal |Dp w i| ^ (6 / 5 : ℝ)) ≤ B) :
    oneSidedPressureGradientOriginCellOutput R₁ κ
      (oneSidedMorreyBound (6 / 5) κ ρ₀ A B) Dp := by
  intro i z r
  have hnorm := morreyNorm_one_sided_indicator_le_on_cylinder
    R₁ (6 / 5) κ ρ₀ A B hR₁ hR₁quarter (by norm_num) hκ
    hρ₀ (fun w => Dp w i) (hsmall i) (hglobal i)
  refine le_trans ?_ hnorm
  unfold morreyNorm
  exact le_iSup_of_le z (le_iSup_of_le r le_rfl)

/-- **The origin-carrier cell producer from margin-scale past-cylinder slice
data.**  This is the established past-slice route with the growth clause taken only
at the margin scale, where it is supplyable, and with the resulting transfer
constant compared against the explicit majorant of the estimate.  The field is
bound before every clause that mentions it, and the two integral constants are
bound with it. -/
theorem originCellProducer_of_margin_past_slice_data
    (hPast :
    ∀ q τ C_CZ R₀ R₁ ε : ℝ, ∀ KU KD : ℝ≥0∞,
      5 / 2 < q → 25 / 3 ≤ τ → τ ≤ 25 →
      0 ≤ C_CZ →
      0 < R₁ → R₁ < R₀ → R₀ < 3 / 4 → 0 ≤ ε →
      KU < ∞ → KD < ∞ →
      ∀ {Ω : Set Vec3} {I : Set ℝ}
          {u : ParabolicPoint → Vec3}
          {Du : ParabolicPoint → Fin 3 → Vec3}
          {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
          IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
          closure (parabolicCylinder 0 0 1) ⊆ spaceTimeSet Ω I →
          (∀ i, morreyNorm 3 τ
            ((parabolicCylinder (0 : Vec3) 0 R₀).indicator
              (fun z => u z i)) ≤ KU) →
          (∀ i j, morreyNorm 2 (25 / 8 : ℝ)
            ((parabolicCylinder (0 : Vec3) 0 R₀).indicator
              (fun z => Du z i j)) ≤ KD) →
          ((∫⁻ z in parabolicCylinder 0 0 1,
            ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
            ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
            ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤ ENNReal.ofReal ε) →
          ∃ Dp : ParabolicPoint → Vec3,
            (∀ i, AEMeasurable (fun z => Dp z i)
              (volume.restrict (vec3Ball 0 R₁ ×ˢ I))) ∧
            (∀ (U : Set Vec3) (J : Set ℝ), localBox Ω I U J →
              U ⊆ vec3Ball 0 R₁ → ∀ i : Fin 3,
              Integrable (fun z => Dp z i)
                (volume.restrict (spaceTimeSet U J))) ∧
            (∀ i, ∀ ψ : Vec3 × ℝ → ℝ,
              ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ →
              tsupport ψ ⊆ vec3Ball 0 R₁ ×ˢ I →
              (∫ z : ParabolicPoint, p z * spatialPartial ψ i z) =
                -(∫ z : ParabolicPoint, Dp z i * ψ z)) ∧
            ∃ A B : ℝ≥0∞,
              (∀ i : Fin 3, ∀ z ∈ parabolicCylinder (0 : Vec3) 0 (3 / 4),
                ∀ r : ℝ, 0 < r → r ≤ (1 - R₁) / 4 →
                cylinderPowerIntegral (6 / 5 : ℝ) (fun w => Dp w i) z r ≤
                  A * ENNReal.ofReal
                    (r ^ (5 * (1 - (6 / 5 : ℝ) /
                      min ((1 / τ + 8 / 25)⁻¹) q)))) ∧
              (∀ i : Fin 3, (∫⁻ w in parabolicCylinder (0 : Vec3) 0 R₁,
                ENNReal.ofReal |Dp w i| ^ (6 / 5 : ℝ)) ≤ B) ∧
              oneSidedMorreyBound (6 / 5) (min ((1 / τ + 8 / 25)⁻¹) q)
                  ((1 - R₁) / 4) A B ≤
                oneSidedPressureGradientKP q τ C_CZ R₀ R₁ ε KU KD) :
    oneSidedPressureGradientOriginCellProducer := by
  intro q τ C_CZ R₀ R₁ ε KU KD hq hτ hτupper hC hR₁ hR₁R₀ hR₀ hε hKU hKD
    Ω I u Du p f hsol hdom hU hD hdata
  obtain ⟨Dp, hAE, hInt, hpair, A, B, hsmall, hglobal, hAB⟩ :=
    hPast q τ C_CZ R₀ R₁ ε KU KD hq hτ hτupper hC hR₁ hR₁R₀ hR₀ hε hKU hKD
      hsol hdom hU hD hdata
  refine ⟨Dp, hAE, hInt, hpair, ?_⟩
  intro i z r
  refine le_trans ?_ hAB
  exact originCellOutput_of_margin_cell_bounds hR₁ (lt_trans hR₁R₀ hR₀)
    (routeA_uniform_kappa_min_lower hq hτ)
    (originMarginScale_pos (by linarith only [hR₁R₀, hR₀])) hsmall hglobal i z r

end CKN.Core.Step4
