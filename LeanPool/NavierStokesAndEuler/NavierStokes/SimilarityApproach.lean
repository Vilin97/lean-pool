/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.SimilarityProfile
public import LeanPool.NavierStokesAndEuler.NavierStokes.DiagonalResidual

@[expose] public section

/-!
# The actual similarity scale at the singular point

The coordinate solves `q - z^2 q^a = tau`. Its positive branch tends to zero
when `tau` and `z` tend to zero together. The value assigned outside the
positive-time domain is never used in this assertion.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace NavierStokes.SimilarityApproach

open SimilarityCoordinates

noncomputable def upperScale (a : ℝ) (p : ℝ × ℝ) : ℝ :=
  2 * p.1 + (2 * p.2 ^ 2) ^ (1 - a)⁻¹

theorem coordinateQ_le_upperScale {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    {p : ℝ × ℝ} (hp : 0 < p.1) : coordinateQ a p ≤ upperScale a p := by
  obtain ⟨hq, he⟩ := coordinateQ_spec ha ha1 hp
  have hd : 0 < 1 - a := sub_pos.mpr ha1
  have htail : 0 ≤ (2 * p.2 ^ 2) ^ (1 - a)⁻¹ :=
    Real.rpow_nonneg (by positivity) _
  by_cases hsmall : coordinateQ a p ≤ 2 * p.1
  · exact hsmall.trans (le_add_of_nonneg_right htail)
  · have hlarge : 2 * p.1 < coordinateQ a p := lt_of_not_ge hsmall
    have hqa : 0 < coordinateQ a p ^ a := Real.rpow_pos_of_pos hq _
    have hprod : coordinateQ a p ^ a * coordinateQ a p ^ (1 - a) =
        coordinateQ a p := by
      have hadd : a + (1 - a) = 1 := by ring
      rw [← Real.rpow_add hq, hadd, Real.rpow_one]
    have hpower : coordinateQ a p ^ (1 - a) < 2 * p.2 ^ 2 := by
      apply (mul_lt_mul_iff_left₀ hqa).mp
      rw [mul_comm (coordinateQ a p ^ (1 - a)), hprod]
      dsimp [forwardScalar] at he
      nlinarith
    have hbound := Real.rpow_le_rpow
      (Real.rpow_nonneg hq.le (1 - a)) hpower.le (inv_pos.mpr hd).le
    rw [Real.rpow_rpow_inv hq.le hd.ne'] at hbound
    exact hbound.trans (le_add_of_nonneg_left (by positivity))

theorem upperScale_continuous {a : ℝ} (ha1 : a < 1) : Continuous (upperScale a) :=
  (continuous_const.mul continuous_fst).add
    ((Real.continuous_rpow_const (inv_nonneg.mpr (sub_nonneg.mpr ha1.le))).comp
      (continuous_const.mul (continuous_snd.pow 2)))

@[simp] theorem upperScale_origin {a : ℝ} (ha1 : a < 1) :
    upperScale a (0, 0) = 0 := by
  simp [upperScale, Real.zero_rpow (inv_pos.mpr (sub_pos.mpr ha1)).ne']

/-- Joint approach; neither a fixed axial coordinate nor a prescribed path
is required. Positive time is required eventually. -/
theorem coordinateQ_tendsto_zero {α : Type*} {l : Filter α} {tau z : α → ℝ}
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (htau : Tendsto tau l (𝓝 0)) (hz : Tendsto z l (𝓝 0))
    (hpos : ∀ᶠ i in l, 0 < tau i) :
    Tendsto (fun i => coordinateQ a (tau i, z i)) l (𝓝 0) := by
  have hmajor : Tendsto (fun i => upperScale a (tau i, z i)) l (𝓝 0) := by
    simpa only [upperScale_origin ha1, Function.comp_def] using
      ((upperScale_continuous ha1).tendsto (0, 0)).comp (htau.prodMk_nhds hz)
  apply squeeze_zero' _ _ hmajor
  · filter_upwards [hpos] with i hi
    exact (coordinateQ_spec ha ha1 hi).1.le
  · filter_upwards [hpos] with i hi
    exact coordinateQ_le_upperScale ha ha1 hi

theorem physical_q_bound {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : SimilarityProfile.PhysicalPoint} (ht : p.1 < 1) :
    SimilarityProfile.q h p ≤
      2 * (1 - p.1) + (2 * p.2.2 ^ 2) ^ (1 - 2 * h)⁻¹ :=
  coordinateQ_le_upperScale (by linarith) (by linarith) (sub_pos.mpr ht)

theorem physical_q_tendsto_zero {α : Type*} {l : Filter α}
    {p : α → SimilarityProfile.PhysicalPoint} {h : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2)
    (ht : Tendsto (fun i => (p i).1) l (𝓝 1))
    (hz : Tendsto (fun i => (p i).2.2) l (𝓝 0))
    (hbefore : ∀ᶠ i in l, (p i).1 < 1) :
    Tendsto (fun i => SimilarityProfile.q h (p i)) l (𝓝 0) := by
  refine coordinateQ_tendsto_zero (by linarith) (by linarith) ?_ hz ?_
  · simpa using (tendsto_const_nhds :
      Tendsto (fun _ : α => (1 : ℝ)) l (𝓝 1)).sub ht
  · exact hbefore.mono (fun _ hi => sub_pos.mpr hi)

/-- A proved positive-order estimate of an actual derivative gives its
zero limit once the actual scale has the joint limit above. -/
theorem jet_tendsto_zero {D V : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {l : Filter D} {q : D → ℝ} {f : D → V} {m : ℕ}
    (hjet : DiagonalResidual.JetRate l q f m 1)
    (hq : Tendsto q l (𝓝 0)) :
    Tendsto (iteratedFDeriv ℝ m f) l (𝓝 0) := by
  obtain ⟨C, _, hbound⟩ := hjet
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _
    (show Tendsto (fun x => C * q x) l (𝓝 0) by simpa using hq.const_mul C)
  exact hbound.mono (fun x hx => by simpa only [Real.rpow_one] using hx)

end NavierStokes.SimilarityApproach
