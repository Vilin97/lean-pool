/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.DecompositionSWS

/-!
# Identification Extension Pairing Slice

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
noncomputable section
namespace CKN

/-- Almost-everywhere slice integrability of the velocity tensor, the pressure and the
force on the support of a spatial cut-off.  For a suitable weak solution on `Ω × I`,
a compactly supported cut-off `η` whose topological support lies in `Ω`, and any
`c : ℝ → Vec3`, for almost every time `s` the functions
`pressureUTensor u c (·, s) i j`, `p (·, s)` and `f (·, s) j` are integrable on
`tsupport η` with respect to the spatial measure.  This supplies the slice data consumed
by the localized pressure pairing identity (paper label: pressure cut-off identity). -/
theorem pressureCutoff_slice_data_ae_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {η : Vec3 → ℝ} (hηc : HasCompactSupport η) (hηΩ : tsupport η ⊆ Ω)
    (c : ℝ → Vec3) :
    ∀ᵐ s ∂volume.restrict I,
      (∀ i j : Fin 3, IntegrableOn (fun y : Vec3 => pressureUTensor u c (y, s) i j)
          (tsupport η) volume) ∧
        IntegrableOn (fun y : Vec3 => p (y, s)) (tsupport η) volume ∧
        (∀ j : Fin 3, IntegrableOn (fun y : Vec3 => f (y, s) j) (tsupport η) volume) := by
  classical
  obtain ⟨Ω', _hΩ'open, hηΩ', _hηΩ'', hΩ'compact, _hΩ'Ω, hLp⟩ :=
    decomposition_slice_integrability hsol hηc hηΩ hηc hηΩ
  haveI : IsFiniteMeasure (volume.restrict Ω') := by
    apply isFiniteMeasure_restrict.mpr
    exact (lt_of_le_of_lt (measure_mono (μ := volume) subset_closure)
      hΩ'compact.measure_lt_top).ne
  filter_upwards [hLp] with s hLp_s
  have huComp (i : Fin 3) : MemLp (fun x : Vec3 => u (x, s) i) 2
      (volume.restrict Ω') :=
    hLp_s.1.continuousLinearMap_comp
      (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ)
  have huInt (i : Fin 3) : Integrable (fun x : Vec3 => u (x, s) i)
      (volume.restrict Ω') := huComp i |>.integrable (by norm_num)
  have hfInt (i : Fin 3) : Integrable (fun x : Vec3 => f (x, s) i)
      (volume.restrict Ω') := by
    apply hLp_s.2.2.mono
      ((ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ).continuous.comp_aestronglyMeasurable
        hLp_s.2.2.aestronglyMeasurable)
    filter_upwards [] with x
    change ‖f (x, s) i‖ ≤ ‖f (x, s)‖
    rw [Pi.norm_def]
    simpa only [coe_nnnorm] using
      (NNReal.coe_le_coe.mpr
        (Finset.le_sup (s := (Finset.univ : Finset (Fin 3)))
          (f := fun b => ‖f (x, s) b‖₊) (Finset.mem_univ i)))
  have hmono {g : Vec3 → ℝ} (hg : Integrable g (volume.restrict Ω')) :
      IntegrableOn g (tsupport η) volume :=
    IntegrableOn.mono_set hg hηΩ'
  have htensor (i j : Fin 3) : IntegrableOn
      (fun y : Vec3 => pressureUTensor u c (y, s) i j) Ω' volume := by
    have hprod : Integrable (fun x : Vec3 => u (x, s) i * u (x, s) j)
        (volume.restrict Ω') := (huComp i).integrable_mul (huComp j)
    have hsum : Integrable
        (fun x : Vec3 => -(u (x, s) i * u (x, s) j) + c s j * u (x, s) i)
        (volume.restrict Ω') := hprod.neg.add ((huInt i).const_mul (c s j))
    exact hsum.congr (Filter.Eventually.of_forall fun x => by
      simp only [pressureUTensor]
      ring)
  exact ⟨fun i j => IntegrableOn.mono_set (htensor i j) hηΩ',
    hmono hLp_s.2.1, fun j => hmono (hfInt j)⟩

end CKN
