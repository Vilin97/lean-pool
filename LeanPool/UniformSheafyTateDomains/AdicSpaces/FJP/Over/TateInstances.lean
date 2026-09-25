/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/
module


/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.Over.JetRings
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.FaithfulLocLift

/-!
# The uniformizer-free Huber/Tate structure of the four jet rings over a general base

`RationalLocData.IsRational.span_eq_top` (Wedhorn 7.30(1)) needs `[IsTateRing 𝓐]`, and the
`HasLocLiftPowerBounded`/`restrictionMap` vocabulary needs `[IsHuberRing E]` at each vertex.
Over the abstract base these do *not* require a uniformizer: `NontriviallyNormedField K`
already provides a scaling constant `c` with `0 < ‖c‖ < 1` (the inverse of a norm-`>1`
element), and the constants of each jet ring scale the norm exactly. So — unlike the
ϖ-parametric pseudouniformizer package `piA …`/`isTateRing_JetA …` of `Over/JetRings.lean`,
which the graph–Koszul engine consumes — the bare topological classes are honest instances,
and with them the faithful pair-free loc-lift discharger applies to all four rings
unconditionally.

## Why this is its own module (the comparator trust boundary)

These instances used to live in `Over/Functoriality.lean`. That file imports
`Over/Chart.lean`, which *proves* `not_isStablyUniform_JetA` — one of the statements the
comparator certificate judges. A challenge file stating `¬ IsStablyUniform (JetA K)` at a
general base needs the `IsHuberRing` instance to elaborate the statement at all, so with the
instances in `Functoriality` the challenge's import closure would have contained the proof
it is supposed to be independent of.

Splitting them out here — this module's closure is `Over/JetRings` → `FJP.CDVFBase` +
`FJP.FiniteJetRings`, the definition layer, plus the base-agnostic `FaithfulLocLift` —
lets `Comparator/Challenge.lean` state the general-base conclusions from definitions alone.
This is the same fix that was applied to the Laurent case, where the generic
`NonarchimedeanRing` witness was moved from `FiniteJetFunctoriality.lean` down into
`FiniteJetRings.lean`.
-/

@[expose] public section

namespace FiniteJetOver

open FiniteJet
open FiniteJet.RestrictedLaurent
open ValuationSpectrum

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

noncomputable section

/-- A norm-window scaling constant of the base field. -/
theorem exists_norm_window : ∃ c : K, IsUnit c ∧ ‖c‖ < 1 ∧ 0 < ‖c‖ := by
  obtain ⟨x, hx⟩ := NormedField.exists_one_lt_norm K
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, norm_zero] at hx
    linarith
  exact ⟨x⁻¹, isUnit_iff_ne_zero.mpr (inv_ne_zero hx0),
    by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hx,
    by rw [norm_inv]; exact inv_pos.mpr (lt_trans one_pos hx)⟩

/-- Scaling by an arbitrary base constant in `𝓐` is exactly norm-multiplicative
(the ϖ-free form of `norm_piA_mul`). -/
theorem norm_constA_mul (c : K) (z : JetA K) :
    ‖constA K c * z‖ = ‖constA K c‖ * ‖z‖ := by
  show ‖(constC K c * (z : JetC K) : JetC K)‖ = _
  rw [norm_constC_mul]
  congr 1
  exact (norm_constA K c).symm

/-- The constant of `𝓑` at a base element (the ϖ-free form of `piB`). -/
def constB (c : K) : JetB K := TrivSqZeroExt.inl (constHomPS K c)

theorem norm_constB (c : K) : ‖constB K c‖ = ‖c‖ := by
  rw [constB, JetNorm.norm_inl]
  exact norm_restrictedC _

theorem norm_constB_mul (c : K) (x : JetB K) : ‖constB K c * x‖ = ‖constB K c‖ * ‖x‖ := by
  have hsnd : (constB K c * x).snd = constHomPS K c * x.snd := by
    rw [TrivSqZeroExt.snd_mul, smul_eq_mul, op_smul_eq_mul]
    show _ + (constB K c).snd * x.fst = _
    rw [show (constB K c).snd = 0 from rfl, zero_mul, add_zero]
    rfl
  have hfst : (constB K c * x).fst = constHomPS K c * x.fst := rfl
  rw [norm_constB, JetNorm.norm_def, JetNorm.norm_def, hfst, hsnd]
  show max ‖PowerSeries.Restricted.C (1 : ℝ) _ * x.fst‖
    ‖PowerSeries.Restricted.C (1 : ℝ) _ * x.snd‖ = _
  rw [norm_restrictedC_mul, norm_restrictedC_mul,
    mul_max_of_nonneg _ _ (norm_nonneg c)]

theorem isUnit_constB {c : K} (hc : IsUnit c) : IsUnit (constB K c) := by
  refine IsUnit.map ((TrivSqZeroExt.inlHom _ _).comp (constHomPS K)) ?_
  exact hc

/-- The constant of `𝓓` at a base element (the ϖ-free form of `piD`). -/
def constD (c : K) : JetD K := TrivSqZeroExt.inl (RestrictedLaurent.C c)

theorem norm_constD (c : K) : ‖constD K c‖ = ‖c‖ := by
  rw [constD, JetNorm.norm_inl]
  show ‖single 0 _‖ = _
  rw [norm_single]

theorem norm_constD_mul (c : K) (x : JetD K) : ‖constD K c * x‖ = ‖constD K c‖ * ‖x‖ := by
  have hsnd : (constD K c * x).snd = RestrictedLaurent.C c * x.snd := by
    rw [TrivSqZeroExt.snd_mul, smul_eq_mul, op_smul_eq_mul]
    show _ + (constD K c).snd * x.fst = _
    rw [show (constD K c).snd = 0 from rfl, zero_mul, add_zero]
    rfl
  have hfst : (constD K c * x).fst = RestrictedLaurent.C c * x.fst := rfl
  rw [norm_constD, JetNorm.norm_def, JetNorm.norm_def, hfst, hsnd]
  show max ‖RestrictedLaurent.C _ * x.fst‖ ‖RestrictedLaurent.C _ * x.snd‖ = _
  rw [norm_C_mul, norm_C_mul, mul_max_of_nonneg _ _ (norm_nonneg c)]

theorem isUnit_constD {c : K} (hc : IsUnit c) : IsUnit (constD K c) := by
  refine IsUnit.map ((TrivSqZeroExt.inlHom _ _).comp (RestrictedLaurent.C (R := K))) ?_
  exact hc

instance : IsHuberRing (JetA K) := by
  obtain ⟨c, hcu, hc1, hc0⟩ := exists_norm_window K
  exact isHuberRing_of_scale (constA K c) (IsUnit.map (constA K) hcu)
    (by rw [norm_constA]; exact hc1) (by rw [norm_constA]; exact hc0)
    (norm_constA_mul K c)

instance : IsTateRing (JetA K) := by
  obtain ⟨c, hcu, hc1, hc0⟩ := exists_norm_window K
  exact isTateRing_of_scale (constA K c) (IsUnit.map (constA K) hcu)
    (by rw [norm_constA]; exact hc1) (by rw [norm_constA]; exact hc0)
    (norm_constA_mul K c)

instance : IsHuberRing (JetB K) := by
  obtain ⟨c, hcu, hc1, hc0⟩ := exists_norm_window K
  exact isHuberRing_of_scale (constB K c) (isUnit_constB K hcu)
    (by rw [norm_constB]; exact hc1) (by rw [norm_constB]; exact hc0)
    (norm_constB_mul K c)

instance : IsTateRing (JetB K) := by
  obtain ⟨c, hcu, hc1, hc0⟩ := exists_norm_window K
  exact isTateRing_of_scale (constB K c) (isUnit_constB K hcu)
    (by rw [norm_constB]; exact hc1) (by rw [norm_constB]; exact hc0)
    (norm_constB_mul K c)

instance : IsHuberRing (JetC K) := by
  obtain ⟨c, hcu, hc1, hc0⟩ := exists_norm_window K
  exact isHuberRing_of_scale (constC K c) (IsUnit.map (constC K) hcu)
    (by rw [norm_constC]; exact hc1) (by rw [norm_constC]; exact hc0)
    (fun f => by rw [norm_constC_mul, norm_constC])

instance : IsTateRing (JetC K) := by
  obtain ⟨c, hcu, hc1, hc0⟩ := exists_norm_window K
  exact isTateRing_of_scale (constC K c) (IsUnit.map (constC K) hcu)
    (by rw [norm_constC]; exact hc1) (by rw [norm_constC]; exact hc0)
    (fun f => by rw [norm_constC_mul, norm_constC])

instance : IsHuberRing (JetD K) := by
  obtain ⟨c, hcu, hc1, hc0⟩ := exists_norm_window K
  exact isHuberRing_of_scale (constD K c) (isUnit_constD K hcu)
    (by rw [norm_constD]; exact hc1) (by rw [norm_constD]; exact hc0)
    (norm_constD_mul K c)

instance : IsTateRing (JetD K) := by
  obtain ⟨c, hcu, hc1, hc0⟩ := exists_norm_window K
  exact isTateRing_of_scale (constD K c) (isUnit_constD K hcu)
    (by rw [norm_constD]; exact hc1) (by rw [norm_constD]; exact hc0)
    (norm_constD_mul K c)

/-- The faithful pair-free loc-lift package at each ring: with the Huber/Tate instances
above, `hasLocLiftPowerBounded_faithful` applies with no uniformizer input (all its other
hypotheses — `T2Space`, `NonarchimedeanRing`, right-uniformity completeness,
`IsRingOfIntegralElements` — are instances from `Over/JetRings.lean`). -/
instance hasLocLiftPowerBounded_JetB : HasLocLiftPowerBounded (JetB K) :=
  hasLocLiftPowerBounded_faithful

instance hasLocLiftPowerBounded_JetC : HasLocLiftPowerBounded (JetC K) :=
  hasLocLiftPowerBounded_faithful

instance hasLocLiftPowerBounded_JetD : HasLocLiftPowerBounded (JetD K) :=
  hasLocLiftPowerBounded_faithful

/-- `HasLocLiftPowerBounded 𝓐` — 𝓐 is *not* noetherian, but the faithful pair-free
discharger is noetherianity-free, so it applies just as at the vertices. -/
instance hasLocLiftPowerBounded_JetA : HasLocLiftPowerBounded (JetA K) :=
  hasLocLiftPowerBounded_faithful

end

end FiniteJetOver
