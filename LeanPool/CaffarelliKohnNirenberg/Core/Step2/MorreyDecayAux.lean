/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Iteration.Arithmetic
public import LeanPool.CaffarelliKohnNirenberg.Core.Step2.Iteration
public import LeanPool.CaffarelliKohnNirenberg.Setting.SliceNormBounds
public import LeanPool.CaffarelliKohnNirenberg.Setting.Energy.PointwiseEnergy

/-!
# Morrey Decay Aux

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic


noncomputable section

namespace CKN
namespace MorreyDecayAux

theorem max_components_le_theta
    {κ : ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    {z : ParabolicPoint} {r : ℝ}
    (hκ : 0 < κ) (hκle : κ ≤ 1)
    (hα : 0 ≤ alpha u z r) (hβ : 0 ≤ beta u Du z r) :
    max (max (alpha u z r) (beta u Du z r)) (delta p z r ^ 2) ≤
      theta κ u Du p z r := by
  have hκfactor : 1 ≤ κ ^ (-4 : ℝ) := by
    have h := Real.rpow_le_rpow_of_exponent_ge hκ hκle
      (by norm_num : (-4 : ℝ) ≤ 0)
    simpa using h
  have hδ : delta p z r ^ 2 ≤ κ ^ (-4 : ℝ) * delta p z r ^ 2 := by
    simpa only [one_mul] using
      (mul_le_mul_of_nonneg_right hκfactor (sq_nonneg (delta p z r)))
  have hθ : 0 ≤ theta κ u Du p z r := by
    unfold theta
    positivity
  have hα' : alpha u z r ≤ theta κ u Du p z r := by
    unfold theta at *
    nlinarith only [hβ, hδ]
  have hβ' : beta u Du z r ≤ theta κ u Du p z r := by
    unfold theta at *
    nlinarith only [hα, hδ]
  have hδ' : delta p z r ^ 2 ≤ theta κ u Du p z r := by
    unfold theta at *
    nlinarith only [hα, hβ, hδ]
  exact max_le (max_le hα' hβ') hδ'

theorem lambda_le_of_subset
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z z' : ParabolicPoint} {r R : ℝ} (hr : 0 < r)
    (hsub : parabolicCylinder z.1 z.2 r ⊆
      parabolicCylinder z'.1 z'.2 R)
    (hI : (∫⁻ w in parabolicCylinder z'.1 z'.2 R,
      ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q) < ⊤) :
    lambda q f z r ≤ r ^ (3 - 5 / q) *
      (∫⁻ w in parabolicCylinder z'.1 z'.2 R,
        ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q).toReal ^ (1 / q : ℝ) := by
  have hq : 0 < q := lt_trans (by norm_num : (0 : ℝ) < 5 / 2)
    hsol.2.2.2.1
  have hIle : (∫⁻ w in parabolicCylinder z.1 z.2 r,
        ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q) ≤
      ∫⁻ w in parabolicCylinder z'.1 z'.2 R,
        ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q :=
    lintegral_mono_set hsub
  have hIle' := ENNReal.toReal_mono (ne_of_lt hI) hIle
  have hroot := Real.rpow_le_rpow ENNReal.toReal_nonneg hIle'
    (by positivity : 0 ≤ (1 / q : ℝ))
  unfold lambda
  exact mul_le_mul_of_nonneg_left hroot
    (Real.rpow_nonneg (by positivity) _)

theorem exists_small_normalized
    {T L : ℕ → ℝ} {ηd C₂₉ : ℝ}
    (hηd : 0 < ηd)
    (hrec : ∀ n, T (n + 1) ≤ (3 / 8 : ℝ) * T n + C₂₉ * L n)
    (hsource : ∀ n, C₂₉ * L n ≤ ηd / 16) :
    ∃ n, T n ≤ ηd / 4 := by
  have hbound : ∀ n, T n ≤ (3 / 8 : ℝ) ^ n * T 0 + ηd / 10 := by
    intro n
    induction n with
    | zero =>
        simpa using (le_add_of_nonneg_right
          (by positivity : 0 ≤ ηd / 10) : T 0 ≤ T 0 + ηd / 10)
    | succ n ih =>
        calc
          T (n + 1) ≤ (3 / 8 : ℝ) * T n + C₂₉ * L n := hrec n
          _ ≤ (3 / 8 : ℝ) *
              ((3 / 8 : ℝ) ^ n * T 0 + ηd / 10) + ηd / 16 := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left ih (by norm_num)) (hsource n)
          _ = (3 / 8 : ℝ) ^ (n + 1) * T 0 + ηd / 10 := by
            rw [pow_succ]
            ring
  have hpow : Tendsto (fun n : ℕ => (3 / 8 : ℝ) ^ n * T 0)
      atTop (𝓝 (0 : ℝ)) := by
    simpa using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 3 / 8)
        (by norm_num : (3 / 8 : ℝ) < 1)).mul_const (T 0)
  have hev : ∀ᶠ n : ℕ in atTop, (3 / 8 : ℝ) ^ n * T 0 < 3 * ηd / 20 :=
    (tendsto_order.1 hpow).2 _ (by positivity)
  obtain ⟨n, hn⟩ := (eventually_atTop.1 hev)
  refine ⟨n, ?_⟩
  have hn' := hn n le_rfl
  have hb := hbound n
  nlinarith only [hb, hn', hηd]

end MorreyDecayAux
end CKN
