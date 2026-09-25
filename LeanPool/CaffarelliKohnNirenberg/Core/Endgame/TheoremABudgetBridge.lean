/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginClauseGauge
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginBudgetSufficient
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.CarrierRestriction
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginCellInstanceMargin
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginClauseField

/-! # Assembling the pressure-gradient estimate on the origin carrier

`lem:pressure-gradient-morrey` produces one measurable weak pressure
gradient and estimates it cell by cell. Two independent bounds are available
on each doubled source cell: the slice estimate of the selected gradient and
the fixed-carrier estimate of the harmonic and annular remainder. On each
cell the smaller of the two clipped time integrals may be used, where
"clipped" means integrated only over the part of the cell inside the
backward carrier, in both space and time, so that the integral is the one
produced by the indicator of that carrier.

Finite covers transfer these costs to the two coefficients of the one-sided
transfer: the small-cell growth coefficient and the whole-carrier mass.
A uniform bound on the covering sums is a genuine quantitative input;
finiteness of the local growth coefficients alone does not supply it.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Foundation.Euclidean CKN.Core.Step4

noncomputable section
namespace CKN.Core.Endgame

/-- The smaller of the shared slice cost and the fixed-carrier gauge cost,
both integrated only over the clipped backward time window. -/
def theoremAClippedCellCost (R₁ : ℝ)
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
    (N : Fin 3 → Vec3 → ℝ → ℝ → ℝ → ℝ≥0∞) (i : Fin 3)
    (c : ParabolicPoint × {r : ℝ // 0 < r}) : ℝ≥0∞ :=
  min (∫⁻ s in Ioc (c.1.2 - c.2.1 ^ 2) c.1.2 ∩ Ioc (-(R₁ ^ 2)) 0,
      N i c.1.1 c.1.2 (2 * c.2.1) s ^ (6 / 5 : ℝ))
    (∫⁻ s in Ioc (c.1.2 - c.2.1 ^ 2) c.1.2 ∩ Ioc (-(R₁ ^ 2)) 0,
      originClauseGaugeMajorant R₁ u Du p f c.1
        (show 0 < 2 * c.2.1 from mul_pos (by norm_num) c.2.2) s ^ (6 / 5 : ℝ))



/-- Integrals over a finite cover are bounded by the sum of the individual
bounds. Overlap costs nothing beyond this sum. -/
theorem theoremA_integral_le_cover_sum
    {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    {S : Set α} (s : Finset ι) (U : ι → Set α) (F : α → ℝ≥0∞)
    (b : ι → ℝ≥0∞) (hcover : S ⊆ ⋃ j ∈ s, U j)
    (hcell : ∀ j ∈ s, (∫⁻ x in U j, F x ∂μ) ≤ b j) :
    (∫⁻ x in S, F x ∂μ) ≤ ∑ j ∈ s, b j := by
  classical
  apply (lintegral_mono_set hcover).trans
  clear hcover
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
    apply (lintegral_union_le F _ _).trans
    exact add_le_add (hcell a (Finset.mem_insert_self _ _))
      (ih (fun j hj => hcell j (Finset.mem_insert_of_mem hj)))

/-- The scalar slice clause transfers to one measurable origin gradient. On
admissible cells, either the shared majorant or the explicit pressure gauge
can pay for its clipped power integral. -/
theorem theoremA_field_cell_cost_of_slice_majorant
    {q R₁ : ℝ} (hR₁ : 0 < R₁) (hR₁one : R₁ < 1)
    {Ω : Set Vec3} {I : Set ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hdom : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I)
    (N : Fin 3 → Vec3 → ℝ → ℝ → ℝ → ℝ≥0∞)
    (hslice : ∀ (i : Fin 3) (c : Vec3) (t ρ : ℝ), 0 < ρ →
      closure (parabolicCylinder c t ρ) ⊆ spaceTimeSet Ω I →
      ∀ᵐ s ∂volume.restrict (Ioc (t - ρ ^ 2) t), ∃ g : Vec3 → ℝ,
        LocallyIntegrableOn g (euclideanBall c (ρ / 2)) volume ∧
        HasWeakPartialDerivOn (euclideanBall c (ρ / 2)) i (fun y => p (y, s)) g ∧
        eLpNorm g (ENNReal.ofReal (6 / 5 : ℝ))
          (volume.restrict (euclideanBall c (ρ / 2))) ≤ N i c t ρ s) :
    ∃ Dp : ParabolicPoint → Vec3, Measurable Dp ∧
      (∀ᵐ s ∂volume.restrict I, ∀ i : Fin 3,
        LocallyIntegrableOn (fun y => Dp (y, s) i) (vec3Ball 0 R₁) volume ∧
        HasWeakPartialDerivOn (vec3Ball 0 R₁) i
          (fun y => p (y, s)) (fun y => Dp (y, s) i)) ∧
      (∀ (c : ParabolicPoint × {r : ℝ // 0 < r}),
        c.2.1 ≤ (1 - R₁) / 2 →
        c.1 ∈ closure (parabolicCylinder (0 : Vec3) 0 R₁) → ∀ i : Fin 3,
        (∫⁻ w in parabolicCylinder c.1.1 c.1.2 c.2.1 ∩
          parabolicCylinder (0 : Vec3) 0 R₁,
          ENNReal.ofReal |Dp w i| ^ (6 / 5 : ℝ)) ≤
            theoremAClippedCellCost R₁ u Du p f N i c) := by
  obtain ⟨Dp, hDp, hfield, hgauge⟩ :=
    originClauseGauge_exists_doubled_cell_bounds_of_sws hsol hdom hR₁ hR₁one
  obtain ⟨_hΩ, hI⟩ := OriginInstance.originUnitBall_subset_of_dom hdom
  refine ⟨Dp, hDp, hfield, ?_⟩
  intro c hmargin hc i
  apply le_min
  · apply originClauseCarrierCellIntegral_le_of_double_radius hR₁.le hR₁one.le hI
      c.2.2 (((measurable_pi_apply i).comp hDp).aemeasurable.restrict)
      (hfield.mono (fun _ hs => hs i))
    exact hslice i c.1.1 c.1.2 (2 * c.2.1) (mul_pos (by norm_num) c.2.2)
      ((originClauseGauge_doubleRadius_subset_unit hR₁ hR₁one c.2.2 hmargin hc).trans hdom)
  · exact hgauge c.1 hc c.2.1 c.2.2 (by linarith only [hmargin]) i

private theorem norm_power_integral_eq
    {Dp : ParabolicPoint → Vec3} (hDp : Measurable Dp)
    (i : Fin 3) (E : Set Vec3) (T : Set ℝ) :
    (∫⁻ s in T, eLpNorm (fun y => Dp (y, s) i) (ENNReal.ofReal (6 / 5 : ℝ))
      (volume.restrict E) ^ (6 / 5 : ℝ)) =
      ∫⁻ w in E ×ˢ T, ENNReal.ofReal |Dp w i| ^ (6 / 5 : ℝ) := by
  have hm : AEMeasurable (fun w : ParabolicPoint => Dp w i)
      (volume.restrict (E ×ˢ T)) := ((measurable_pi_apply i).comp hDp).aemeasurable.restrict
  rw [prodPowerIntegral_eq_lintegral_slices hm]
  apply lintegral_congr
  intro s
  have hs : AEStronglyMeasurable (fun y => Dp (y, s) i) (volume.restrict E) :=
    (((measurable_pi_apply i).comp hDp).comp (measurable_id.prodMk
      measurable_const)).aestronglyMeasurable
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) ENNReal.ofReal_ne_top hs]
  norm_num only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 6 / 5)]
  rw [← ENNReal.rpow_mul]
  norm_num only [one_div, inv_mul_cancel₀ (by norm_num : (6 / 5 : ℝ) ≠ 0), ENNReal.rpow_one]
  simp only [Real.enorm_eq_ofReal_abs]

/-- Uniform finite-cover costs give the two clipped slice budgets on the
origin carrier. All numerical constants precede the solution. The only
additional analytic input beyond the shared scalar slice clause is the
explicit covering-sum bound `hCoverBudget`; its two parts pay for local cells
and for the whole carrier, respectively. -/
theorem theoremA_clause_integrals_of_cover_budget
    (q τ R₁ : ℝ) (A B : ℝ≥0∞)
    (hR₁ : 0 < R₁) (hR₁34 : R₁ < 3 / 4)
    {Ω : Set Vec3} {I : Set ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hdom : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I)
    (N : Fin 3 → Vec3 → ℝ → ℝ → ℝ → ℝ≥0∞)
    (hslice : ∀ (i : Fin 3) (c : Vec3) (t ρ : ℝ), 0 < ρ →
      closure (parabolicCylinder c t ρ) ⊆ spaceTimeSet Ω I →
      ∀ᵐ s ∂volume.restrict (Ioc (t - ρ ^ 2) t), ∃ g : Vec3 → ℝ,
        LocallyIntegrableOn g (euclideanBall c (ρ / 2)) volume ∧
        HasWeakPartialDerivOn (euclideanBall c (ρ / 2)) i (fun y => p (y, s)) g ∧
        eLpNorm g (ENNReal.ofReal (6 / 5 : ℝ))
          (volume.restrict (euclideanBall c (ρ / 2))) ≤ N i c t ρ s)
    (hCoverBudget :
      (∀ i : Fin 3, ∀ z ∈ parabolicCylinder (0 : Vec3) 0 (3 / 4),
        ∀ r : ℝ, 0 < r → r ≤ R₁ →
        ∃ s : Finset (ParabolicPoint × {r : ℝ // 0 < r}),
          (parabolicCylinder z.1 z.2 r ∩ parabolicCylinder (0 : Vec3) 0 R₁) ⊆
            ⋃ c ∈ s, parabolicCylinder c.1.1 c.1.2 c.2.1 ∩
              parabolicCylinder (0 : Vec3) 0 R₁ ∧
          (∀ c ∈ s, c.2.1 ≤ (1 - R₁) / 2 ∧
            c.1 ∈ closure (parabolicCylinder (0 : Vec3) 0 R₁)) ∧
          (∑ c ∈ s, theoremAClippedCellCost R₁ u Du p f N i c) ≤
            A * ENNReal.ofReal
              (r ^ (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q)))) ∧
      (∀ i : Fin 3, ∃ s : Finset (ParabolicPoint × {r : ℝ // 0 < r}),
          parabolicCylinder (0 : Vec3) 0 R₁ ⊆
            ⋃ c ∈ s, parabolicCylinder c.1.1 c.1.2 c.2.1 ∩
              parabolicCylinder (0 : Vec3) 0 R₁ ∧
          (∀ c ∈ s, c.2.1 ≤ (1 - R₁) / 2 ∧
            c.1 ∈ closure (parabolicCylinder (0 : Vec3) 0 R₁)) ∧
          (∑ c ∈ s, theoremAClippedCellCost R₁ u Du p f N i c) ≤ B)) :
    ∃ Dp : ParabolicPoint → Vec3, Measurable Dp ∧
      (∀ᵐ s ∂volume.restrict I, ∀ i : Fin 3,
        LocallyIntegrableOn (fun y => Dp (y, s) i) (vec3Ball 0 R₁) volume ∧
        HasWeakPartialDerivOn (vec3Ball 0 R₁) i
          (fun y => p (y, s)) (fun y => Dp (y, s) i)) ∧
      (∀ i : Fin 3, ∀ z ∈ parabolicCylinder (0 : Vec3) 0 (3 / 4),
        ∀ r : ℝ, 0 < r → r ≤ R₁ →
        (∫⁻ s in Ioc (z.2 - r ^ 2) z.2 ∩ Ioc (-(R₁ ^ 2)) 0,
          eLpNorm (fun y => Dp (y, s) i) (ENNReal.ofReal (6 / 5 : ℝ))
            (volume.restrict (vec3Ball z.1 r ∩ vec3Ball 0 R₁)) ^ (6 / 5 : ℝ)) ≤
          A * ENNReal.ofReal
            (r ^ (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q)))) ∧
      (∀ i : Fin 3, (∫⁻ s in Ioc (-(R₁ ^ 2)) 0,
          eLpNorm (fun y => Dp (y, s) i) (ENNReal.ofReal (6 / 5 : ℝ))
            (volume.restrict (vec3Ball 0 R₁)) ^ (6 / 5 : ℝ)) ≤ B) := by
  classical
  obtain ⟨Dp, hDp, hfield, hcost⟩ := theoremA_field_cell_cost_of_slice_majorant
    hR₁ (by linarith only [hR₁34]) hsol hdom N hslice
  have hsum (i : Fin 3) (S : Set ParabolicPoint)
      (s : Finset (ParabolicPoint × {r : ℝ // 0 < r}))
      (hcover : S ⊆ ⋃ c ∈ s, parabolicCylinder c.1.1 c.1.2 c.2.1 ∩
        parabolicCylinder (0 : Vec3) 0 R₁)
      (hgeom : ∀ c ∈ s, c.2.1 ≤ (1 - R₁) / 2 ∧
        c.1 ∈ closure (parabolicCylinder (0 : Vec3) 0 R₁)) :
      (∫⁻ w in S, ENNReal.ofReal |Dp w i| ^ (6 / 5 : ℝ)) ≤
        ∑ c ∈ s, theoremAClippedCellCost R₁ u Du p f N i c := by
    apply theoremA_integral_le_cover_sum s _ _ _ hcover
    intro c hc
    exact hcost c (hgeom c hc).1 (hgeom c hc).2 i
  refine ⟨Dp, hDp, hfield, ?_, ?_⟩
  · intro i z hz r hr hrR₁
    obtain ⟨s, hcover, hgeom, hbound⟩ := hCoverBudget.1 i z hz r hr hrR₁
    rw [norm_power_integral_eq hDp]
    rw [← parabolicCylinder_inter_origin_eq_prod]
    exact (hsum i _ s hcover hgeom).trans hbound
  · intro i
    obtain ⟨s, hcover, hgeom, hbound⟩ := hCoverBudget.2 i
    rw [norm_power_integral_eq hDp]
    have hprod : vec3Ball (0 : Vec3) R₁ ×ˢ Ioc (-(R₁ ^ 2)) 0 =
        parabolicCylinder (0 : Vec3) 0 R₁ := by
      simp only [parabolicCylinder, zero_sub]
    rw [hprod]
    exact (hsum i _ s hcover hgeom).trans hbound








/-- The clipped origin construction with an arbitrary final numerical
majorant. Selection, integrability and pairing are the same carrier-radius
construction; only the last order comparison is parameterized. -/
theorem theoremA_origin_cell_producer_of_clipped_data
    {q τ R₀ R₁ : ℝ} {A B KP : ℝ≥0∞}
    (hq : 5 / 2 < q) (hτ : 25 / 3 ≤ τ)
    (hR₁ : 0 < R₁) (hR₁R₀ : R₁ < R₀) (hR₀ : R₀ < 3 / 4)
    {Ω : Set Vec3} {I : Set ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hdom : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I)
    (M : Fin 3 → Vec3 → ℝ → ℝ → ℝ≥0∞)
    (hdata :
          (∀ (i : Fin 3) (x : Vec3) (r : ℝ),
              ∀ᵐ s ∂(volume.restrict I), ∃ g : Vec3 → ℝ,
                LocallyIntegrableOn g (vec3Ball (0 : Vec3) R₁) volume ∧
                HasWeakPartialDerivOn (vec3Ball (0 : Vec3) R₁) i
                  (fun y => p (y, s)) g ∧
                eLpNorm g (ENNReal.ofReal (6 / 5 : ℝ))
                  (volume.restrict
                    (vec3Ball x r ∩ vec3Ball (0 : Vec3) R₁)) ≤ M i x r s) ∧
            (∀ i : Fin 3, ∀ᵐ s ∂(volume.restrict I),
              M i (0 : Vec3) R₁ s ≠ ∞) ∧
            (∀ i : Fin 3, ∀ T : Set ℝ, IsCompact (closure T) → closure T ⊆ I →
              Integrable (fun s => (M i (0 : Vec3) R₁ s).toReal)
                (volume.restrict T)) ∧
            (∀ i : Fin 3, ∀ z ∈ parabolicCylinder (0 : Vec3) 0 (3 / 4),
              ∀ r : ℝ, 0 < r → r ≤ R₁ →
              (∫⁻ s in Ioc (z.2 - r ^ 2) z.2 ∩ Ioc (-(R₁ ^ 2)) 0,
                M i z.1 r s ^ (6 / 5 : ℝ)) ≤
                A * ENNReal.ofReal
                  (r ^ (5 * (1 - (6 / 5 : ℝ) /
                    min ((1 / τ + 8 / 25)⁻¹) q)))) ∧
            (∀ i : Fin 3, (∫⁻ s in Ioc (-(R₁ ^ 2)) 0,
              M i (0 : Vec3) R₁ s ^ (6 / 5 : ℝ)) ≤ B))
    (hcompare : oneSidedMorreyBound (6 / 5) (min ((1 / τ + 8 / 25)⁻¹) q) R₁ A B ≤ KP) :
    ∃ Dp : ParabolicPoint → Vec3,
          (∀ i, AEMeasurable (fun z => Dp z i)
            (volume.restrict (vec3Ball 0 R₁ ×ˢ I))) ∧
          (∀ (U : Set Vec3) (J : Set ℝ), CKN.localBox Ω I U J →
            U ⊆ vec3Ball 0 R₁ → ∀ i : Fin 3,
            Integrable (fun z => Dp z i)
              (volume.restrict (CKN.spaceTimeSet U J))) ∧
          (∀ i, ∀ ψ : Vec3 × ℝ → ℝ,
            ψ ∈ CKN.spaceTimeTestFunction (V := ℝ) Set.univ Set.univ →
            tsupport ψ ⊆ vec3Ball 0 R₁ ×ˢ I →
            (∫ z : ParabolicPoint, p z * spatialPartial ψ i z) =
              -(∫ z : ParabolicPoint, Dp z i * ψ z)) ∧
          oneSidedPressureGradientOriginCellOutput R₁
            (min ((1 / τ + 8 / 25)⁻¹) q)
            KP Dp := by
  obtain ⟨hslice, hMtop, hMint, hgrowth, hglobal⟩ := hdata
  obtain ⟨_hΩ, hIcc⟩ := originClauseUnitBall_subset_of_dom hdom
  have hR₁one : R₁ ≤ 1 := by linarith only [hR₁R₀, hR₀]
  have hR₁ltone : R₁ < 1 := by linarith only [hR₁R₀, hR₀]
  let Rstar : ℝ := (R₁ + R₀) / 2
  have hR₁Rstar : R₁ < Rstar := by
    dsimp [Rstar]
    linarith only [hR₁R₀]
  have hRstarR₀ : Rstar < R₀ := by
    dsimp [Rstar]
    linarith only [hR₁R₀]
  have hRstar : Rstar < 3 / 4 := hRstarR₀.trans hR₀
  have hRstarMargin : Rstar ≤ (1 + R₁) / 2 := by
    dsimp [Rstar]
    linarith only [hR₀]
  obtain ⟨Dpm, _hmeasM, hmarginWeak, _hmarginBound⟩ :=
    origin_measurable_gradient_margin_bounds_of_sws hsol hdom hR₁ hR₁ltone
  have hsliceLift : ∀ (i : Fin 3) (x : Vec3) (r : ℝ),
      ∀ᵐ t ∂(volume.restrict I), ∃ g : Vec3 → ℝ,
      LocallyIntegrableOn g (vec3Ball (0 : Vec3) Rstar) volume ∧
      HasWeakPartialDerivOn (vec3Ball (0 : Vec3) Rstar) i
        (fun x => p (x, t)) g ∧
      eLpNorm g (ENNReal.ofReal (6 / 5 : ℝ))
        (volume.restrict (vec3Ball x r ∩ vec3Ball (0 : Vec3) R₁)) ≤ M i x r t := by
    intro i x r
    filter_upwards [hmarginWeak, hslice i x r] with t hm hs
    obtain ⟨g, hgloc, hweak, hgnorm⟩ := hs
    obtain ⟨hmloc, hmweak⟩ := hm i
    have hballStarMargin : vec3Ball (0 : Vec3) Rstar ⊆
        vec3Ball (0 : Vec3) ((1 + R₁) / 2) := vec3Ball_mono hRstarMargin
    have hballOneStar : vec3Ball (0 : Vec3) R₁ ⊆ vec3Ball (0 : Vec3) Rstar :=
      vec3Ball_mono hR₁Rstar.le
    have hballOneMargin : vec3Ball (0 : Vec3) R₁ ⊆
        vec3Ball (0 : Vec3) ((1 + R₁) / 2) := hballOneStar.trans hballStarMargin
    have hmlocOne := hmloc.mono_set hballOneMargin
    have hmweakOne := hmweak.restrict (isOpen_vec3Ball _ _) hballOneMargin
    have huniq := HasWeakPartialDerivOn.ae_eq (isOpen_vec3Ball _ _)
      hgloc hmlocOne hweak hmweakOne
    let gm : Vec3 → ℝ := fun y => Dpm (y, t) i
    have hlocStar : LocallyIntegrableOn gm (vec3Ball (0 : Vec3) Rstar) volume :=
      hmloc.mono_set hballStarMargin
    have hweakStar : HasWeakPartialDerivOn (vec3Ball (0 : Vec3) Rstar) i
        (fun y => p (y, t)) gm := hmweak.restrict (isOpen_vec3Ball _ _) hballStarMargin
    have huniqMeasure : g =ᵐ[volume.restrict (vec3Ball (0 : Vec3) R₁)] gm := by
      simpa [gm] using huniq
    have huniqCell : g =ᵐ[volume.restrict
        (vec3Ball x r ∩ vec3Ball (0 : Vec3) R₁)] gm :=
      huniqMeasure.filter_mono
        (ae_mono (Measure.restrict_mono_set volume inter_subset_right))
    refine ⟨gm, hlocStar, hweakStar, ?_⟩
    rw [← eLpNorm_congr_ae huniqCell]
    exact hgnorm
  have hsliceTop : ∀ k : Fin 3, ∀ᵐ t ∂(volume.restrict I), ∃ g : Vec3 → ℝ,
      LocallyIntegrableOn g (vec3Ball (0 : Vec3) Rstar) volume ∧
      HasWeakPartialDerivOn (vec3Ball (0 : Vec3) Rstar) k (fun x => p (x, t)) g ∧
      eLpNorm g (ENNReal.ofReal (6 / 5 : ℝ))
        (volume.restrict (vec3Ball (0 : Vec3) R₁)) ≤ M k (0 : Vec3) R₁ t := by
    intro k
    filter_upwards [hsliceLift k (0 : Vec3) R₁] with t hs
    simpa only [Set.inter_self] using hs
  obtain ⟨Dp, hAE, hInt, hpair, hident, _hbound, _hvan⟩ :=
    exists_originClause_pressure_gradient_field hsol hdom hR₁ hR₁Rstar hRstar
      hsliceTop hMtop hMint
  obtain ⟨hcell, hmass⟩ :=
    originClauseCellBounds_of_multiscale_majorant (R₀ := Rstar) (p := p)
      hR₁.le hR₁one hIcc hsliceLift hgrowth hglobal Dp hAE hident
  refine ⟨Dp, hAE, hInt, hpair, ?_⟩
  intro i z r
  refine le_trans ?_ hcompare
  exact originCellOutput_of_carrier_cell_bounds hR₁ (by linarith only [hR₁R₀, hR₀])
    (routeA_uniform_kappa_min_lower hq hτ) hcell hmass i z r


end CKN.Core.Endgame
