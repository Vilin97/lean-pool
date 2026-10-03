/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.RelativeInitialDefectPositiveTransport
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.ScalarQuadraticL2

/-! Positive source primitives from genuine spacetime L2 control. Neither
source traces at zero nor pointwise-in-time source estimates are needed. -/

@[expose] public section

noncomputable section
open MeasureTheory Filter Topology Homogenization AVenhance AVenhance.Infra.Section4
namespace AVenhance.Infra.Section5.RelativeError

/-- Closed spatial unit cell used for compactness and periodic integration. -/
def RelativeInitialDefectSourceIntegral.sourceClosedCube : Set (Vec 2) :=
  Set.pi Set.univ fun _ : Fin 2 => Set.Icc (0 : ℝ) 1

theorem RelativeInitialDefectSourceIntegral.sourceClosedCube_compact : IsCompact
    RelativeInitialDefectSourceIntegral.sourceClosedCube :=
  isCompact_univ_pi fun _ => isCompact_Icc

theorem RelativeInitialDefectSourceIntegral.sourceCube_ae_eq :
    unitCube =ᵐ[(volume : Measure (Vec 2))] RelativeInitialDefectSourceIntegral.sourceClosedCube
        := by
  simpa [volume_pi, unitCube, RelativeInitialDefectSourceIntegral.sourceClosedCube] using
    (Measure.univ_pi_Ioo_ae_eq_Icc (f := fun _ : Fin 2 => (0 : ℝ))
      (g := fun _ : Fin 2 => (1 : ℝ)))

instance RelativeInitialDefectSourceIntegral.sourceWindow_locallyCompact (a b : ℝ) :
    LocallyCompactSpace {t // t ∈ Set.Icc a b} := isClosed_Icc.locallyCompactSpace

/-- Positive joint continuity gives continuity of the spatial L2 norm on each
positive compact window. -/
theorem relative_initial_source_norm_continuous_pos {f : ℝ → Vec 2 → ℝ}
    (hf : ContinuousOn (fun z : ℝ × Vec 2 => f z.1 z.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ)) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun t => Real.sqrt (l2NormSq (f t))) (Set.Icc a b) := by
  let K := Set.Icc a b
  have hjoint : Continuous (fun p : K × Vec 2 => f p.1.1 p.2) := by
    have hmap : Continuous (fun p : K × Vec 2 => (p.1.1, p.2)) := by fun_prop
    exact hf.comp_continuous hmap
      (fun p => ⟨ha.trans_le p.1.2.1, Set.mem_univ _⟩)
  have hparam : Continuous (fun t : K => ∫ x in
      RelativeInitialDefectSourceIntegral.sourceClosedCube, f t.1 x ^ 2) :=
    continuous_parametric_integral_of_continuous
      (f := fun (t : K) (x : Vec 2) => f t.1 x ^ 2) (by
        change Continuous (fun p : K × Vec 2 => f p.1.1 p.2 ^ 2)
        exact hjoint.pow 2) RelativeInitialDefectSourceIntegral.sourceClosedCube_compact
  have heq (t : K) : (∫ x in RelativeInitialDefectSourceIntegral.sourceClosedCube, f t.1 x ^ 2) =
      l2NormSq (f t.1) :=
    setIntegral_congr_set RelativeInitialDefectSourceIntegral.sourceCube_ae_eq.symm
  have henergy : ContinuousOn (fun t => l2NormSq (f t)) K := by
    rw [continuousOn_iff_continuous_domRestrict]
    change Continuous (fun t : K => l2NormSq (f t.1))
    have hfun : (fun t : K => ∫ x in RelativeInitialDefectSourceIntegral.sourceClosedCube, f t.1 x
        ^ 2) =
        fun t => l2NormSq (f t.1) := funext heq
    rw [← hfun]
    exact hparam
  exact henergy.sqrt

/-- The endpoint source L2 bound controls its primitive uniformly as the
left endpoint tends to zero through positive times. -/
theorem relative_initial_source_integral_of_eLpNorm {f : ℝ → Vec 2 → ℝ}
    (hf : ContinuousOn (fun z : ℝ × Vec 2 => f z.1 z.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ))
    {B a b : ℝ} (hB : 0 ≤ B) (ha : 0 < a) (hab : a ≤ b) (hb : b < 1)
    (hbound : eLpNorm (fun z : ℝ × Vec 2 => f z.1 z.2) 2
      (volume.restrict timeCube) ≤ ENNReal.ofReal B) :
    (∫ t in a..b, Real.sqrt (l2NormSq (f t))) ≤ Real.sqrt b * B := by
  have hsub : Set.Ioc a b ×ˢ unitCube ⊆ timeCube := by
    intro z hz
    exact ⟨⟨ha.trans hz.1.1, hz.1.2.trans_lt hb⟩, hz.2⟩
  have hμ : volume.restrict timeCube ≪ volume.restrict
      (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2))) :=
    Measure.absolutelyContinuous_of_le (Measure.restrict_mono
      (show timeCube ⊆ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2)) from
        fun z hz => ⟨hz.1.1, Set.mem_univ _⟩) le_rfl)
  have hmeas : AEStronglyMeasurable (fun z : ℝ × Vec 2 => f z.1 z.2)
      (volume.restrict timeCube) :=
    (hf.aestronglyMeasurable (isOpen_Ioi.prod isOpen_univ).measurableSet
      (μ := volume)).mono_ac hμ
  have hmem : MemLp (fun z : ℝ × Vec 2 => f z.1 z.2) 2 (volume.restrict timeCube) :=
    hbound.trans_lt (by finiteness)
  have hsq : IntegrableOn (fun z : ℝ × Vec 2 => f z.1 z.2 ^ 2) timeCube := hmem.integrable_sq
  have hquad := amnr_scalar_square_le_of_eLpNorm_two hmeas hB hbound
  have hwin := hsq.mono_set hsub
  have hmono : (∫ z in Set.Ioc a b ×ˢ unitCube, f z.1 z.2 ^ 2) ≤ B ^ 2 :=
    (setIntegral_mono_set hsq (Filter.Eventually.of_forall fun z => sq_nonneg _)
      (Filter.Eventually.of_forall hsub)).trans hquad
  rw [Measure.volume_eq_prod, setIntegral_prod _ (by
    simpa only [← Measure.volume_eq_prod] using hwin)] at hmono
  have hquadwin : (∫ t in a..b, Real.sqrt (l2NormSq (f t)) ^ 2) ≤ B ^ 2 := by
    simp_rw [Real.sq_sqrt (show 0 ≤ l2NormSq (f _) from integral_nonneg fun _ => sq_nonneg _)]
    rw [intervalIntegral.integral_of_le hab]
    exact hmono
  exact relative_initial_source_L1_of_positive_L2 ha hab hB
    (relative_initial_source_norm_continuous_pos hf ha) hquadwin

end AVenhance.Infra.Section5.RelativeError
