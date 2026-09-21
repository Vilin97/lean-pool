/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.ObataScalarLimits
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # An explicit clock for the Obata scalar ODE

The logarithmic clock supplies a differentiable inverse time change on
the open interval between the extremal values.
-/

@[expose] public noncomputable section
open Set

namespace LichnerowiczObata

def obataClock (K a s : ℝ) : ℝ :=
  (Real.log (a + s) - Real.log (a - s)) / (2 * K * a)
theorem hasDerivAt_obataClock {K a s : ℝ} (hK : 0 < K) (ha : 0 < a)
    (hs : -a < s ∧ s < a) :
    HasDerivAt (obataClock K a) (1 / (K * (a ^ 2 - s ^ 2))) s := by
  change HasDerivAt (fun x : ℝ => (Real.log (a + x) - Real.log (a - x)) / (2 * K * a))
    (1 / (K * (a ^ 2 - s ^ 2))) s
  have hp : a + s ≠ 0 := ne_of_gt (by linarith)
  have hm : a - s ≠ 0 := ne_of_gt (sub_pos.2 hs.2)
  have hd := (((hasDerivAt_id s).const_add a).log hp).sub
    (((hasDerivAt_id s).const_sub a).log hm)
  have he := hd.div_const (2 * K * a)
  have heq : (1 / (a + s) - -1 / (a - s)) / (2 * K * a) =
      1 / (K * (a ^ 2 - s ^ 2)) := by
    have hsq : a ^ 2 - s ^ 2 ≠ 0 := ne_of_gt (by nlinarith [hs.1, hs.2])
    field_simp
    <;> ring
  simpa only [obataClock, Pi.sub_def, id_eq, heq] using he

/-- The logarithmic clock advances at unit rate along a regular scalar solution. -/
theorem obataClock_along_solution {K a : ℝ} (hK : 0 < K) (ha : 0 < a)
    {u : ℝ → ℝ} (hs : ∀ t, -a < u t ∧ u t < a)
    (hd : ∀ t, HasDerivAt u (K * (a ^ 2 - u t ^ 2)) t) (t : ℝ) :
    obataClock K a (u t) = obataClock K a (u 0) + t := by
  have hder : ∀ s, HasDerivAt (fun z => obataClock K a (u z) - z) 0 s := by
    intro s
    have hpos : K * (a ^ 2 - u s ^ 2) ≠ 0 :=
      ne_of_gt (mul_pos hK (by nlinarith [(hs s).1, (hs s).2]))
    have hc := (hasDerivAt_obataClock hK ha (hs s)).comp s (hd s)
    have hc' : HasDerivAt (fun z => obataClock K a (u z)) 1 s := by
      simpa only [Function.comp_def, one_div, inv_mul_cancel₀ hpos] using hc
    simpa only [Pi.sub_def, id_eq, sub_self] using hc'.sub (hasDerivAt_id s)
  have he := is_const_of_deriv_eq_zero (fun s => (hder s).differentiableAt)
    (fun s => (hder s).deriv) t 0
  simp only [sub_zero] at he
  linarith

/-- The explicit inverse clock reaches any prescribed regular level. -/
theorem obataClock_inverse_level {K a : ℝ} (hK : 0 < K) (ha : 0 < a)
    {u : ℝ → ℝ} (hs : ∀ t, -a < u t ∧ u t < a)
    (hd : ∀ t, HasDerivAt u (K * (a ^ 2 - u t ^ 2)) t)
    {b : ℝ} (hb : -a < b ∧ b < a) :
    u (obataClock K a b - obataClock K a (u 0)) = b := by
  obtain ⟨t, ht⟩ := exists_time_obata_scalar hK ha (fun t => ⟨(hs t).1.le, (hs t).2.le⟩)
    hd (hs 0) hb
  have he := obataClock_along_solution hK ha hs hd t
  rw [ht] at he
  have htime : obataClock K a b - obataClock K a (u 0) = t := by linarith
  simpa only [htime] using ht

end LichnerowiczObata
