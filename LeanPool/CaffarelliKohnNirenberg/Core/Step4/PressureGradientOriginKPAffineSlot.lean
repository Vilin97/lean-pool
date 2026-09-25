/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOneSidedKP

/-!
# Pressure Gradient Origin KPAffine Slot

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Core.Endgame

noncomputable section

namespace CKN.Core.Step4

/-!
# A homogeneous small-cell budget for the origin pressure-gradient majorant

The small-cell budget `A` of `oneSidedMorreyBound (6/5) κ ρ₀ A B` bounds a
time integral of the `6/5` power of a spatial `L^{6/5}` norm by `A · r^θ`.
It is therefore homogeneous of degree `6/5` in any norm of the pressure
gradient. The budget of `oneSidedPressureGradientKP` is linear in the
source bound `X = 3·KU·KD + forceSourceMorreyBound q ε`, so it has one fifth
of a power too little: the zero-velocity datum with linear pressure `a·x₀`
and balancing force `a·e₀` has cell integrals equal to `X^{6/5} r⁵` at the
sharp data size, which exceeds any fixed multiple of `X` once `a` is large.

The budget `originKPAffineASlot` keeps the old linear term, adds its `6/5`
power (the source term, also used by `oneSidedPressureGradientKP'`), and
adds a pressure-mass term `128 · ε^{4/5}`. The last term is the `6/5` power
of the `L^{3/2}` size `ε^{2/3}` of the pressure; it is needed for pressure
gradients driven by a fast time oscillation of a spatially constant velocity,
which carry no force and no velocity-gradient source.

`lem:pressure-gradient-morrey` asserts only that the bound is a finite
function of the incoming Morrey norms, the local energy, pressure and force
norms, the exponents and the radii. `oneSidedPressureGradientKPAffine` is
one such function, written out. Its two summands are the two regimes of the
one-sided transfer: `originKPAffineASlot` controls every small cell through
its growth in the radius, and the second summand is the mass of the gradient
over the whole carrier, which pays for the remaining cells.

The small-cell coefficient is not linear in the source size. With
`X = 3·K_U·K_D` plus the force contribution, the datum with zero velocity,
pressure `a·x₀` and balancing force `a·e₀` has cell integrals of size
`X^{6/5} r⁵`, which no fixed multiple of `X` dominates as `a` grows. The
coefficient therefore carries the `6/5` power as well, together with a term
of size `ε^{4/5}`, the `6/5` power of the `L^{3/2}` size of the pressure,
which is needed for gradients driven by a fast time oscillation of a
spatially constant velocity: such data carry no force and no
velocity-gradient source.

## Main results
- `oneSidedPressureGradientKP'_le_oneSidedPressureGradientKPAffine`: the
  majorant with the `6/5`-power budget is dominated by the new one.
- `oneSidedPressureGradientKP_le_oneSidedPressureGradientKPAffine`: the
  original majorant is dominated by the new one, with no parameter
  assumptions.
- `source_time_power_le_originKPAffineASlot`: the source time-power
  coefficient `X^{6/5}` lies below the new budget.
- `clipped_clause_le_oneSidedPressureGradientKPAffine`,
  `restricted_clause_le_oneSidedPressureGradientKPAffine`: the clipped and
  restricted scale conversions land below the new majorant for `0 < R₁ < 1`.
- `oneSidedPressureGradientQuantitative_to_KPAffine`: the explicit AE binder
  with the original majorant yields the same binder with the new one.
-/

/-- The enlarged small-cell budget for the origin pressure-gradient
estimate. With `c = |C_CZ| + 1` and `X = 3·KU·KD + forceSourceMorreyBound q ε`
it is `c·3X + (c·3X)^{6/5} + c·128·ε^{4/5}`. -/
def originKPAffineASlot (q C_CZ ε : ℝ) (KU KD : ℝ≥0∞) : ℝ≥0∞ :=
  ENNReal.ofReal (|C_CZ| + 1) * (3 * (3 * KU * KD + forceSourceMorreyBound q ε)) +
    (ENNReal.ofReal (|C_CZ| + 1) *
      (3 * (3 * KU * KD + forceSourceMorreyBound q ε))) ^ (6 / 5 : ℝ) +
    ENNReal.ofReal (|C_CZ| + 1) * (128 * ENNReal.ofReal ε ^ (4 / 5 : ℝ))

/-- The enlarged origin pressure-gradient majorant: the small-cell budget
`originKPAffineASlot` together with the whole-carrier budget of
`oneSidedPressureGradientKP'`, which carries the clipped-scale inflation. -/
def oneSidedPressureGradientKPAffine
    (q τ C_CZ R₀ R₁ ε : ℝ) (KU KD : ℝ≥0∞) : ℝ≥0∞ :=
  oneSidedMorreyBound (6 / 5) (min ((1 / τ + 8 / 25)⁻¹) q) R₁
    (originKPAffineASlot q C_CZ ε KU KD)
    ((ENNReal.ofReal (|C_CZ| + 1) * ENNReal.ofReal (|R₀| + |R₁| + |ε| + 1)) *
      ENNReal.ofReal (max 1 ((2 * R₁ / (1 - R₁)) ^
        (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q)))))

/-- The coefficient `|C_CZ| + 1` is at least one. -/
theorem one_le_ofReal_abs_add_one (C : ℝ) : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (|C| + 1) := by
  rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
  exact ENNReal.ofReal_le_ofReal (by linarith only [abs_nonneg C])


/-- The budget of `oneSidedPressureGradientKP'` lies below the enlarged
budget. -/
theorem power_A_le_originKPAffineASlot (q C_CZ ε : ℝ) (KU KD : ℝ≥0∞) :
    ENNReal.ofReal (|C_CZ| + 1) * (3 * (3 * KU * KD + forceSourceMorreyBound q ε)) +
        (ENNReal.ofReal (|C_CZ| + 1) *
          (3 * (3 * KU * KD + forceSourceMorreyBound q ε))) ^ (6 / 5 : ℝ) ≤
      originKPAffineASlot q C_CZ ε KU KD := by
  unfold originKPAffineASlot
  exact le_add_right le_rfl


/-- Any quantity whose `6/5` power controls the budget: every `Y ≤ c·3X`
has `Y^{6/5}` below the enlarged budget. -/
theorem rpow_le_originKPAffineASlot_of_le (q C_CZ ε : ℝ) (KU KD Y : ℝ≥0∞)
    (hY : Y ≤ ENNReal.ofReal (|C_CZ| + 1) *
      (3 * (3 * KU * KD + forceSourceMorreyBound q ε))) :
    Y ^ (6 / 5 : ℝ) ≤ originKPAffineASlot q C_CZ ε KU KD := by
  unfold originKPAffineASlot
  calc
    Y ^ (6 / 5 : ℝ) ≤ (ENNReal.ofReal (|C_CZ| + 1) *
        (3 * (3 * KU * KD + forceSourceMorreyBound q ε))) ^ (6 / 5 : ℝ) :=
      ENNReal.rpow_le_rpow hY (by norm_num)
    _ ≤ _ := le_add_right (le_add_left le_rfl)

/-- The source time-power coefficient `(3·KU·KD + forceSourceMorreyBound q ε)^{6/5}`
lies below the enlarged budget. -/
theorem source_time_power_le_originKPAffineASlot (q C_CZ ε : ℝ) (KU KD : ℝ≥0∞) :
    (3 * KU * KD + forceSourceMorreyBound q ε) ^ (6 / 5 : ℝ) ≤
      originKPAffineASlot q C_CZ ε KU KD := by
  apply rpow_le_originKPAffineASlot_of_le
  calc
    3 * KU * KD + forceSourceMorreyBound q ε =
        1 * (1 * (3 * KU * KD + forceSourceMorreyBound q ε)) := by rw [one_mul, one_mul]
    _ ≤ ENNReal.ofReal (|C_CZ| + 1) * (3 * (3 * KU * KD + forceSourceMorreyBound q ε)) :=
      mul_le_mul' (one_le_ofReal_abs_add_one C_CZ)
        (mul_le_mul' (by norm_num) le_rfl)

/-- The enlarged budget is finite for finite velocity and gradient budgets
and an admissible force exponent. -/
theorem originKPAffineASlot_lt_top (q C_CZ ε : ℝ) (KU KD : ℝ≥0∞)
    (hq : 5 / 2 < q) (hKU : KU < ⊤) (hKD : KD < ⊤) :
    originKPAffineASlot q C_CZ ε KU KD < ⊤ := by
  have hc : ENNReal.ofReal (|C_CZ| + 1) < ⊤ := ENNReal.ofReal_lt_top
  have hX : 3 * KU * KD + forceSourceMorreyBound q ε < ⊤ :=
    ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top (ENNReal.mul_lt_top (by simp) hKU) hKD,
      forceSourceMorreyBound_lt_top q ε hq⟩
  have hlin : ENNReal.ofReal (|C_CZ| + 1) *
      (3 * (3 * KU * KD + forceSourceMorreyBound q ε)) < ⊤ :=
    ENNReal.mul_lt_top hc (ENNReal.mul_lt_top (by simp) hX)
  have hmass : ENNReal.ofReal (|C_CZ| + 1) * (128 * ENNReal.ofReal ε ^ (4 / 5 : ℝ)) < ⊤ :=
    ENNReal.mul_lt_top hc (ENNReal.mul_lt_top (by simp)
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top))
  unfold originKPAffineASlot
  exact ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr ⟨hlin,
    ENNReal.rpow_lt_top_of_nonneg (by norm_num) hlin.ne⟩, hmass⟩

/-- The enlarged majorant is finite for finite velocity and gradient budgets
and an admissible force exponent. -/
theorem oneSidedPressureGradientKPAffine_lt_top
    (q τ C_CZ R₀ R₁ ε : ℝ) (KU KD : ℝ≥0∞)
    (hq : 5 / 2 < q) (hKU : KU < ⊤) (hKD : KD < ⊤) :
    oneSidedPressureGradientKPAffine q τ C_CZ R₀ R₁ ε KU KD < ⊤ := by
  unfold oneSidedPressureGradientKPAffine
  exact oneSidedMorreyBound_lt_top (by norm_num)
    (originKPAffineASlot_lt_top q C_CZ ε KU KD hq hKU hKD)
    (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
      ENNReal.ofReal_lt_top)

/-- The majorant with the `6/5`-power budget is dominated by the enlarged
majorant, with no parameter assumptions. -/
theorem oneSidedPressureGradientKP'_le_oneSidedPressureGradientKPAffine
    (q τ C_CZ R₀ R₁ ε : ℝ) (KU KD : ℝ≥0∞) :
    oneSidedPressureGradientKP' q τ C_CZ R₀ R₁ ε KU KD ≤
      oneSidedPressureGradientKPAffine q τ C_CZ R₀ R₁ ε KU KD := by
  dsimp only [oneSidedPressureGradientKP', oneSidedPressureGradientKPAffine]
  exact oneSidedMorreyBound_mono_left (by norm_num)
    (power_A_le_originKPAffineASlot q C_CZ ε KU KD)

/-- The original majorant is dominated by the enlarged majorant, with no
parameter assumptions. -/
theorem oneSidedPressureGradientKP_le_oneSidedPressureGradientKPAffine
    (q τ C_CZ R₀ R₁ ε : ℝ) (KU KD : ℝ≥0∞) :
    oneSidedPressureGradientKP q τ C_CZ R₀ R₁ ε KU KD ≤
      oneSidedPressureGradientKPAffine q τ C_CZ R₀ R₁ ε KU KD :=
  (oneSidedPressureGradientKP_le_oneSidedPressureGradientKP' q τ C_CZ R₀ R₁ ε KU KD).trans
    (oneSidedPressureGradientKP'_le_oneSidedPressureGradientKPAffine q τ C_CZ R₀ R₁ ε KU KD)

/-- The clipped-scale inflation factor is at most its floor at one. -/
private theorem clipped_ratio_le_max {R₁ θ : ℝ} (hR₁lt : R₁ < 1) :
    ENNReal.ofReal ((R₁ / ((1 - R₁) / 2)) ^ θ) ≤
      ENNReal.ofReal (max 1 ((2 * R₁ / (1 - R₁)) ^ θ)) := by
  have hden : (1 : ℝ) - R₁ ≠ 0 := ne_of_gt (by linarith only [hR₁lt])
  have hratio : R₁ / ((1 - R₁) / 2) = 2 * R₁ / (1 - R₁) := by
    field_simp
  rw [hratio]
  exact ENNReal.ofReal_le_ofReal (le_max_right _ _)

/-- **Clipped route.** Small-cell budget below `originKPAffineASlot` and a
whole-carrier budget below `c·(|R₀| + |R₁| + |ε| + 1)` at the clipped scale
`(1 - R₁)/2` give a constant below the enlarged majorant, for every
`0 < R₁ < 1`; the scale inflation is absorbed into the whole-carrier budget. -/
theorem clipped_clause_le_oneSidedPressureGradientKPAffine
    {q τ C_CZ R₀ R₁ ε : ℝ} {KU KD A B : ℝ≥0∞}
    (hR₁ : 0 < R₁) (hR₁lt : R₁ < 1)
    (hA : A ≤ originKPAffineASlot q C_CZ ε KU KD)
    (hB : B ≤ ENNReal.ofReal (|C_CZ| + 1) * ENNReal.ofReal (|R₀| + |R₁| + |ε| + 1)) :
    oneSidedMorreyBound (6 / 5) (min ((1 / τ + 8 / 25)⁻¹) q) ((1 - R₁) / 2) A B ≤
      oneSidedPressureGradientKPAffine q τ C_CZ R₀ R₁ ε KU KD := by
  rw [oneSidedMorreyBound_scale_eq (by norm_num) (clipped_scale_pos hR₁lt) hR₁]
  unfold oneSidedPressureGradientKPAffine
  exact oneSidedMorreyBound_mono (by norm_num) hA (mul_le_mul' hB (clipped_ratio_le_max hR₁lt))

/-- **Restricted route.** Small-cell budget below `originKPAffineASlot` and a
whole-carrier budget inflated by the doubled-margin ratio
`(R₁ / (2·((1 - R₁)/4)))^θ` give a constant below the enlarged majorant, for
every `0 < R₁ < 1`. -/
theorem restricted_clause_le_oneSidedPressureGradientKPAffine
    {q τ C_CZ R₀ R₁ ε : ℝ} {KU KD A B : ℝ≥0∞}
    (hR₁lt : R₁ < 1)
    (hA : A ≤ originKPAffineASlot q C_CZ ε KU KD)
    (hB : B ≤ ENNReal.ofReal (|C_CZ| + 1) * ENNReal.ofReal (|R₀| + |R₁| + |ε| + 1)) :
    oneSidedMorreyBound (6 / 5) (min ((1 / τ + 8 / 25)⁻¹) q) R₁ A
        (B * ENNReal.ofReal ((R₁ / (2 * ((1 - R₁) / 4))) ^
          (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q)))) ≤
      oneSidedPressureGradientKPAffine q τ C_CZ R₀ R₁ ε KU KD := by
  have hmargin : R₁ / (2 * ((1 - R₁) / 4)) = R₁ / ((1 - R₁) / 2) := by ring
  rw [hmargin]
  unfold oneSidedPressureGradientKPAffine
  exact oneSidedMorreyBound_mono (by norm_num) hA (mul_le_mul' hB (clipped_ratio_le_max hR₁lt))

/-- The explicit AE binder with the original majorant yields the same binder
with the enlarged majorant: each output estimate is carried upward by
`oneSidedPressureGradientKP_le_oneSidedPressureGradientKPAffine`. -/
theorem oneSidedPressureGradientQuantitative_to_KPAffine
    (hGA : oneSidedPressureGradientQuantitative) :
    ∀ q τ C_CZ R₀ R₁ ε : ℝ, ∀ KU KD : ℝ≥0∞,
    5 / 2 < q → 25 / 3 ≤ τ → τ ≤ 25 →
    0 ≤ C_CZ →
    0 < R₁ → R₁ < R₀ → R₀ < 3 / 4 → 0 ≤ ε →
    KU < ⊤ → KD < ⊤ →
    oneSidedPressureGradientKPAffine q τ C_CZ R₀ R₁ ε KU KD < ⊤ ∧
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
          (∀ i, morreyNorm (6 / 5 : ℝ)
              (min ((1 / τ + 8 / 25)⁻¹) q)
              ((parabolicCylinder (0 : Vec3) 0 R₁).indicator
                (fun z => Dp z i)) ≤
            oneSidedPressureGradientKPAffine q τ C_CZ R₀ R₁ ε KU KD) := by
  intro q τ C_CZ R₀ R₁ ε KU KD hq hτ hτupper hC hR₁ hR₁R₀ hR₀ hε hKU hKD
  obtain ⟨_hfinite, hout⟩ :=
    oneSidedPressureGradientQuantitative_to_KP' hGA
      q τ C_CZ R₀ R₁ ε KU KD hq hτ hτupper hC hR₁ hR₁R₀ hR₀ hε hKU hKD
  refine ⟨oneSidedPressureGradientKPAffine_lt_top q τ C_CZ R₀ R₁ ε KU KD hq hKU hKD, ?_⟩
  intro Ω I u Du p f hsol hdom hU hD hsmall
  obtain ⟨Dp, hAE, hInt, hweak, hMorrey⟩ := hout hsol hdom hU hD hsmall
  exact ⟨Dp, hAE, hInt, hweak, fun i => (hMorrey i).trans
    (oneSidedPressureGradientKP'_le_oneSidedPressureGradientKPAffine
      q τ C_CZ R₀ R₁ ε KU KD)⟩

end CKN.Core.Step4

end
