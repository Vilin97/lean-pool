/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.AdamsM4
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.PotentialFiniteness

/-!
# Potential Measurability

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey

noncomputable section

namespace CKN.Core.Endgame

/-- A measurable source has a measurable extended-real Riesz potential. -/
theorem measurable_riesz_potential (β : ℝ)
    {f : ParabolicPoint → ℝ} (hf : Measurable f) :
    Measurable (parabolicRieszPotential β f) := by
  let _ : SFinite (volume : Measure ParabolicPoint) := by
    change SFinite (volume : Measure (Vec3 × ℝ))
    infer_instance
  have hn : Measurable (fun x : Vec3 => vec3EuclideanNorm x) := by
    simp only [vec3EuclideanNorm_eq_l2]
    exact (continuous_norm.comp (PiLp.continuous_toLp 2 _)).measurable
  have hx : Measurable (fun zw : ParabolicPoint × ParabolicPoint => zw.1.1 - zw.2.1) :=
    (measurable_fst.comp measurable_fst).sub (measurable_fst.comp measurable_snd)
  have ht : Measurable (fun zw : ParabolicPoint × ParabolicPoint => zw.1.2 - zw.2.2) :=
    (measurable_snd.comp measurable_fst).sub (measurable_snd.comp measurable_snd)
  have hρ : Measurable (fun zw : ParabolicPoint × ParabolicPoint =>
      parabolicRho₂ zw.1 zw.2) :=
    (Real.continuous_sqrt.measurable.comp (continuous_abs.measurable.comp ht)).add
      (hn.comp hx)
  unfold parabolicRieszPotential
  apply Measurable.lintegral_prod_right
  exact (hρ.ennreal_ofReal.pow_const (-(5 - β))).mul
    ((continuous_abs.measurable.comp (hf.comp measurable_snd)).ennreal_ofReal)

/-- Almost-everywhere measurable sources also have measurable potentials:
their measurable representatives give the same potential at every point. -/
theorem measurable_riesz_potential_of_aemeasurable (β : ℝ)
    {f : ParabolicPoint → ℝ} (hf : AEMeasurable f volume) :
    Measurable (parabolicRieszPotential β f) := by
  have heq : parabolicRieszPotential β f = parabolicRieszPotential β (hf.mk f) := by
    funext z
    exact riesz_potential_congr_ae hf.ae_eq_mk z
  rw [heq]
  exact measurable_riesz_potential β hf.measurable_mk

end CKN.Core.Endgame
