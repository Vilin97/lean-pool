/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ParametricHeatTail
public import LeanPool.NavierStokesAndEuler.NavierStokes.TerminalStress

/-!
# The heat edit in the actual implicit physical coordinates

The parameter is `eta = z / q^(1/2-h)`, where the positive implicit branch
satisfies `1-t = q - z^2*q^(2*h)`.  The quadratic-coordinate helper with
`q = tau + z^2` is not used here.  These identities connect the actual heat
edit to the terminal angular velocity, including its normalization.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.PhysicalHeatCoordinates

open SimilarityProfile
open scoped ContDiff

theorem diffusion_eq_ratio {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : PhysicalPoint} (ht : p.1 < 1) :
    ParametricHeatTail.diffusion (eta h p) = (1 - p.1) / q h p := by
  have hq := q_pos hh hh1 ht
  have he : 1 - p.1 = q h p * (1 - eta h p ^ 2) :=
    SimilarityCoordinates.tau_coordinate_identity (by linarith) (by linarith)
      (p := (1 - p.1, p.2.2)) (sub_pos.mpr ht)
  apply (eq_div_iff hq.ne').2
  change (1 - eta h p ^ 2) * q h p = 1 - p.1
  rw [mul_comm]
  exact he.symm

theorem heat_argument {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : PhysicalPoint} (ht : p.1 < 1) (hs : 0 < p.2.1) :
    2 * ParametricHeatTail.diffusion (eta h p) / X h p =
      2 * (1 - p.1) / p.2.1 := by
  rw [diffusion_eq_ratio hh hh1 ht]
  exact ParametricHeatTail.heat_ratio_physical (q_pos hh hh1 ht) hs

/-- Normalization, given by `HeatTailEdit.outgoingAmplitude d * K ^ HeatTailEdit.exponent d.h`. -/
noncomputable def normalization (d : OutgoingTail.TailData) (K : ℝ) : ℝ :=
  HeatTailEdit.outgoingAmplitude d * K ^ HeatTailEdit.exponent d.h

theorem normalization_pos (d : OutgoingTail.TailData) {K : ℝ} (hK : 0 < K) :
    0 < normalization d K :=
  mul_pos (HeatTailEdit.outgoingAmplitude_pos d) (Real.rpow_pos_of_pos hK _)

/-- Edited angular, given by `q d.h p ^ (-HeatTailEdit.exponent d.h) *
ParametricHeatTail.physicalEdit d K (eta d.h p) (X d.h p)`. -/
noncomputable def editedAngular (d : OutgoingTail.TailData) (K : ℝ)
    (p : PhysicalPoint) : ℝ :=
  q d.h p ^ (-HeatTailEdit.exponent d.h) *
    ParametricHeatTail.physicalEdit d K (eta d.h p) (X d.h p)

/-- Shape, given by `OutgoingTail.tailShape d (y - Real.log K + 1 / 5)`. -/
noncomputable def shape (d : OutgoingTail.TailData) (K y : ℝ) : ℝ :=
  OutgoingTail.tailShape d (y - Real.log K + 1 / 5)

theorem editedAngular_eq_heat (d : OutgoingTail.TailData) {K : ℝ}
    (hK : 0 < K) (hh1 : d.h < 1 / 2) {p : PhysicalPoint}
    (ht : p.1 < 1) (hs : 0 < p.2.1)
    (hfull : 1 / 2 ≤ Real.log (X d.h p / K) + 1 / 5) :
    editedAngular d K p =
      TerminalStress.physicalHeat (normalization d K) (1 + d.h) p *
        TerminalStress.flattening d.h (shape d K) p := by
  have hq := q_pos d.h_pos hh1 ht
  have hX : 0 < X d.h p := div_pos hs hq
  have he := ParametricHeatTail.physicalEdit_heat_carrier d hK hq hs
    (diffusion_eq_ratio d.h_pos hh1 ht) hfull
  change editedAngular d K p =
    TerminalStress.physicalHeat (normalization d K) (1 + d.h) p *
      OutgoingTail.tailShape d (Real.log (X d.h p / K) + 1 / 5) at he
  rw [Real.log_div hX.ne' hK.ne'] at he
  exact he

theorem editedAngular_eq_pure_heat (d : OutgoingTail.TailData) {K : ℝ}
    (hK : 0 < K) (hh1 : d.h < 1 / 2) {p : PhysicalPoint}
    (ht : p.1 < 1) (hs : 0 < p.2.1)
    (hlate : 3 ≤ Real.log (X d.h p / K) + 1 / 5) :
    editedAngular d K p =
      TerminalStress.physicalHeat (normalization d K) (1 + d.h) p := by
  exact ParametricHeatTail.physicalEdit_eventual_heat_carrier d hK
    (q_pos d.h_pos hh1 ht) hs (diffusion_eq_ratio d.h_pos hh1 ht) hlate

theorem editedAngular_div_radius (d : OutgoingTail.TailData) {K : ℝ}
    (hK : 0 < K) (hh1 : d.h < 1 / 2) {p : PhysicalPoint}
    (ht : p.1 < 1) (hs : 0 < p.2.1)
    (hfull : 1 / 2 ≤ Real.log (X d.h p / K) + 1 / 5) :
    editedAngular d K p / Real.sqrt (2 * p.2.1) =
      TerminalStress.swirlCoefficient (normalization d K) d.h (shape d K) p := by
  rw [editedAngular_eq_heat d hK hh1 ht hs hfull]
  rfl

/-- The normalized section is used only inside the physical time domain.
It supplies a direct profile-parameter comparison without `log(1-eta^2)`.
Endpoint extensions of profile factors are proved separately. -/
noncomputable def normalizedSection (x e : ℝ) : PhysicalPoint := (e ^ 2, (x, e))

theorem q_normalizedSection {h e : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (he : e ^ 2 < 1) (x : ℝ) : q h (normalizedSection x e) = 1 := by
  apply (SimilarityCoordinates.eq_coordinateQ (by linarith) (by linarith)
    (p := (1 - e ^ 2, e)) (sub_pos.mpr he) (q := 1) (by norm_num) ?_).symm
  simp [SimilarityCoordinates.forwardScalar]

theorem eta_normalizedSection {h e : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (he : e ^ 2 < 1) (x : ℝ) : eta h (normalizedSection x e) = e := by
  change e / q h (normalizedSection x e) ^ ((1 - 2 * h) / 2) = e
  rw [q_normalizedSection hh hh1 he x]
  simp

theorem X_normalizedSection {h e : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (he : e ^ 2 < 1) (x : ℝ) : X h (normalizedSection x e) = x := by
  change x / q h (normalizedSection x e) = x
  rw [q_normalizedSection hh hh1 he x, div_one]

theorem editedAngular_normalizedSection (d : OutgoingTail.TailData)
    (hh1 : d.h < 1 / 2) {e : ℝ} (he : e ^ 2 < 1) (K x : ℝ) :
    editedAngular d K (normalizedSection x e) =
      ParametricHeatTail.physicalEdit d K e x := by
  simp only [editedAngular, q_normalizedSection d.h_pos hh1 he x,
    eta_normalizedSection d.h_pos hh1 he x, X_normalizedSection d.h_pos hh1 he x,
    Real.one_rpow, one_mul]

end NavierStokes.PhysicalHeatCoordinates
