/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginCellInstanceGlue
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginCellInstanceExhaustion
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginCellInstancePairing

/-!
# The pressure-gradient field on the origin carrier

Display `eq:pressure-gradient-morrey` selects, for almost every time of the
solution interval, a weak spatial gradient of the pressure slice on a ball
around the origin, together with its `L^{6/5}` bound on a smaller ball.  The
one-sided estimate `prop:bootstrap` consumes a single space-time field with
three properties: joint measurability on the carrier, integrability on every
compactly interior box, and the space-time integration-by-parts identity
against test functions supported in the carrier.

This module performs that passage.  The selection is made on each member of a
compact exhaustion of the time interval and the resulting fields are glued;
the field is then cut off outside the spatial ball of the carrier, which
changes neither the pairing identity, since the test functions vanish there,
nor the slice bounds.  The output also records the identification of the field
with every slice weak gradient, which is what pins it almost everywhere.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration
open CKN.Foundation.Parabolic.Morrey

noncomputable section

namespace CKN.Core.Step4.OriginInstance

/-- The restriction of the space-time volume to a product box is the product of
the restrictions. -/
private theorem origin_restrict_prod_eq (S : Set Vec3) (T : Set ℝ) :
    (volume : Measure (Vec3 × ℝ)).restrict (S ×ˢ T)
      = ((volume : Measure Vec3).restrict S).prod ((volume : Measure ℝ).restrict T) := by
  rw [volume_eq_prod, ← Measure.prod_restrict]

/-- The space-time field of display `eq:pressure-gradient-morrey` on the origin
carrier `vec3Ball 0 R₁ ×ˢ I`.  From slice weak gradients on the ball of radius
`R₀` with an `L^{6/5}` majorant `K` on the ball of radius `R₁`, integrable on
every compactly interior time window, one obtains a single field with the
measurability, integrability and pairing properties consumed by the one-sided
estimate, identified almost everywhere with the slice gradients and vanishing
off the carrier. -/
theorem exists_origin_pressure_gradient_field
    {Ω : Set Vec3} {I : Set ℝ} {q R₀ R₁ : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    {K : Fin 3 → ℝ → ℝ≥0∞}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hdom : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ CKN.spaceTimeSet Ω I)
    (hR₁ : 0 < R₁) (hR₁R₀ : R₁ < R₀) (hR₀ : R₀ < 3 / 4)
    (hslice : ∀ k : Fin 3, ∀ᵐ t ∂(volume.restrict I), ∃ g : Vec3 → ℝ,
      LocallyIntegrableOn g (vec3Ball (0 : Vec3) R₀) volume ∧
      HasWeakPartialDerivOn (vec3Ball (0 : Vec3) R₀) k (fun x => p (x, t)) g ∧
      eLpNorm g (ENNReal.ofReal (6 / 5 : ℝ))
        (volume.restrict (vec3Ball (0 : Vec3) R₁)) ≤ K k t)
    (hKtop : ∀ k : Fin 3, ∀ᵐ t ∂(volume.restrict I), K k t ≠ ∞)
    (hKint : ∀ k : Fin 3, ∀ T : Set ℝ, IsCompact (closure T) → closure T ⊆ I →
      Integrable (fun t => (K k t).toReal) (volume.restrict T)) :
    ∃ Dp : ParabolicPoint → Vec3,
      (∀ i : Fin 3, AEMeasurable (fun z => Dp z i)
        (volume.restrict (vec3Ball (0 : Vec3) R₁ ×ˢ I))) ∧
      (∀ (U : Set Vec3) (T : Set ℝ), CKN.localBox Ω I U T →
        U ⊆ vec3Ball (0 : Vec3) R₁ → ∀ i : Fin 3,
        Integrable (fun z => Dp z i) (volume.restrict (CKN.spaceTimeSet U T))) ∧
      (∀ i : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ,
        ψ ∈ CKN.spaceTimeTestFunction (V := ℝ) Set.univ Set.univ →
        tsupport ψ ⊆ vec3Ball (0 : Vec3) R₁ ×ˢ I →
        (∫ z : ParabolicPoint, p z * spatialPartial ψ i z) =
          -(∫ z : ParabolicPoint, Dp z i * ψ z)) ∧
      (∀ i : Fin 3, ∀ᵐ t ∂(volume.restrict I), ∀ g : Vec3 → ℝ,
        LocallyIntegrableOn g (vec3Ball (0 : Vec3) R₀) volume →
        HasWeakPartialDerivOn (vec3Ball (0 : Vec3) R₀) i (fun x => p (x, t)) g →
        (fun x => Dp (x, t) i) =ᵐ[volume.restrict (vec3Ball (0 : Vec3) R₁)] g) ∧
      (∀ i : Fin 3, ∀ᵐ t ∂(volume.restrict I),
        eLpNorm (fun x => Dp (x, t) i) (ENNReal.ofReal (6 / 5 : ℝ))
          (volume.restrict (vec3Ball (0 : Vec3) R₁)) ≤ K i t) ∧
      (∀ z : ParabolicPoint, z ∉ vec3Ball (0 : Vec3) R₁ ×ˢ I → Dp z = 0) := by
  classical
  obtain ⟨hΩ, _hI⟩ := originUnitBall_subset_of_dom hdom
  have hR₀pos : 0 < R₀ := lt_trans hR₁ hR₁R₀
  have hR₀one : R₀ < 1 := by linarith only [hR₀]
  have hImeas : MeasurableSet I := hsol.2.1.measurableSet
  obtain ⟨J, _hJmono, hJord, hJcpt, hJI, hJunion, hJcover⟩ :=
    exists_compact_ordConnected_exhaustion hsol.2.1 hsol.2.2.1
  have hJmeas : ∀ n, MeasurableSet (J n) := fun n => (hJcpt n).isClosed.measurableSet
  have hbox : ∀ n, CKN.localBox Ω I (vec3Ball (0 : Vec3) R₀) (J n) :=
    fun n => originLocalBox_of_time hR₀pos hR₀one hΩ (hJord n) (hJcpt n) (hJI n)
  have hpint : ∀ n, IntegrableOn p (vec3Ball (0 : Vec3) R₀ ×ˢ J n) volume :=
    fun n => pressure_integrable_on_of_suitable_local_box hsol (hbox n) subset_rfl
  have hinner : closure (vec3Ball (0 : Vec3) R₁) ⊆ vec3Ball (0 : Vec3) R₀ := by
    rw [closure_vec3Ball hR₁]
    intro y hy
    exact lt_of_le_of_lt hy hR₁R₀
  have hsel : ∀ k : Fin 3, ∃ D : ParabolicPoint → ℝ,
      AEMeasurable D (volume.restrict (vec3Ball (0 : Vec3) R₁ ×ˢ I)) ∧
      (∀ᵐ t ∂(volume.restrict I), ∀ g : Vec3 → ℝ,
        LocallyIntegrableOn g (vec3Ball (0 : Vec3) R₀) volume →
        HasWeakPartialDerivOn (vec3Ball (0 : Vec3) R₀) k (fun x => p (x, t)) g →
        (fun x => D (x, t)) =ᵐ[volume.restrict (vec3Ball (0 : Vec3) R₁)] g) ∧
      (∀ n : ℕ, ∀ Ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) Ψ → HasCompactSupport Ψ →
        tsupport Ψ ⊆ vec3Ball (0 : Vec3) R₁ ×ˢ J n →
        (∫ t in J n, ∫ x in vec3Ball (0 : Vec3) R₁,
            p (x, t) * spatialPartial Ψ k (x, t)) =
          -∫ t in J n, ∫ x in vec3Ball (0 : Vec3) R₁, D (x, t) * Ψ (x, t)) ∧
      (∀ z : ParabolicPoint, z.2 ∉ I → D z = 0) := by
    intro k
    exact exists_spacetime_weak_gradient_on_time_union k
      (isOpen_vec3Ball _ _) (vec3Ball_measurable _ _)
      (originIsCompact_closure_vec3Ball hR₁) hinner hJmeas hJunion hpint
      (by
        filter_upwards [hslice k] with t ht
        obtain ⟨g, hg, hgw, _⟩ := ht
        exact ⟨g, hg, hgw⟩)
  choose D hDmeas hDuniq hDpair hDzero using hsel
  set Dp : ParabolicPoint → Vec3 :=
    fun z => if z.1 ∈ vec3Ball (0 : Vec3) R₁ then (fun i => D i z) else 0 with hDpdef
  have hDpval : ∀ (z : ParabolicPoint), z.1 ∈ vec3Ball (0 : Vec3) R₁ →
      ∀ i : Fin 3, Dp z i = D i z := by
    intro z hz i
    simp only [hDpdef, hz, ite_true]
  have hDpzero : ∀ (z : ParabolicPoint), z.1 ∉ vec3Ball (0 : Vec3) R₁ → Dp z = 0 := by
    intro z hz
    simp only [hDpdef, hz, ite_false]
  have hAE : ∀ i : Fin 3, AEMeasurable (fun z => Dp z i)
      (volume.restrict (vec3Ball (0 : Vec3) R₁ ×ˢ I)) := by
    intro i
    refine (hDmeas i).congr ?_
    refine (ae_restrict_iff' ((vec3Ball_measurable _ _).prod hImeas)).mpr
      (Eventually.of_forall ?_)
    intro z hz
    exact (hDpval z hz.1 i).symm
  have hident : ∀ i : Fin 3, ∀ᵐ t ∂(volume.restrict I), ∀ g : Vec3 → ℝ,
      LocallyIntegrableOn g (vec3Ball (0 : Vec3) R₀) volume →
      HasWeakPartialDerivOn (vec3Ball (0 : Vec3) R₀) i (fun x => p (x, t)) g →
      (fun x => Dp (x, t) i) =ᵐ[volume.restrict (vec3Ball (0 : Vec3) R₁)] g := by
    intro i
    filter_upwards [hDuniq i] with t ht g hg hgw
    refine Filter.EventuallyEq.trans ?_ (ht g hg hgw)
    refine (ae_restrict_iff' (vec3Ball_measurable _ _)).mpr (Eventually.of_forall ?_)
    intro x hx
    exact hDpval (x, t) hx i
  have hbound : ∀ i : Fin 3, ∀ᵐ t ∂(volume.restrict I),
      eLpNorm (fun x => Dp (x, t) i) (ENNReal.ofReal (6 / 5 : ℝ))
        (volume.restrict (vec3Ball (0 : Vec3) R₁)) ≤ K i t := by
    intro i
    filter_upwards [hident i, hslice i] with t ht hg
    obtain ⟨g, hgloc, hgw, hgn⟩ := hg
    rw [eLpNorm_congr_ae (ht g hgloc hgw)]
    exact hgn
  have hvanish : ∀ z : ParabolicPoint, z ∉ vec3Ball (0 : Vec3) R₁ ×ˢ I → Dp z = 0 := by
    intro z hz
    by_cases hz1 : z.1 ∈ vec3Ball (0 : Vec3) R₁
    · have hz2 : z.2 ∉ I := fun h => hz ⟨hz1, h⟩
      funext i
      rw [hDpval z hz1 i, hDzero i z hz2]
      rfl
    · exact hDpzero z hz1
  have hintball : ∀ T : Set ℝ, IsCompact (closure T) → closure T ⊆ I → ∀ i : Fin 3,
      Integrable (fun z => Dp z i)
        (volume.restrict (vec3Ball (0 : Vec3) R₁ ×ˢ T)) := by
    intro T hTcpt hTI i
    have hTsub : T ⊆ I := subset_trans subset_closure hTI
    let _ : IsFiniteMeasure ((volume : Measure Vec3).restrict (vec3Ball (0 : Vec3) R₁)) :=
      isFiniteMeasure_restrict.mpr (volume_vec3Ball_lt_top (x := (0 : Vec3)) (r := R₁)).ne
    have hm : ∀ j : Fin 3, AEMeasurable (fun z => Dp z j)
        (((volume : Measure Vec3).restrict (vec3Ball (0 : Vec3) R₁)).prod
          ((volume : Measure ℝ).restrict T)) := by
      intro j
      rw [← origin_restrict_prod_eq]
      exact (hAE j).mono_measure
        (Measure.restrict_mono_set volume (Set.prod_mono subset_rfl hTsub))
    have hb : ∀ j : Fin 3, ∀ᵐ t ∂(volume.restrict T),
        eLpNorm (fun x => Dp (x, t) j) (ENNReal.ofReal (6 / 5 : ℝ))
          (volume.restrict (vec3Ball (0 : Vec3) R₁)) ≤ K j t :=
      fun j => ae_restrict_of_ae_restrict_of_subset hTsub (hbound j)
    have hk1 : ∀ j : Fin 3, ∀ᵐ t ∂(volume.restrict T), K j t ≠ ∞ :=
      fun j => ae_restrict_of_ae_restrict_of_subset hTsub (hKtop j)
    have hk2 : ∀ j : Fin 3, Integrable (fun t => (K j t).toReal) (volume.restrict T) :=
      fun j => hKint j T hTcpt hTI
    have := pressure_gradient_integrable_on_of_selected_bounds
      (B := vec3Ball (0 : Vec3) R₁) (J := T) (Dp := Dp) (K := K) hm hb hk1 hk2 i
    rwa [← origin_restrict_prod_eq] at this
  refine ⟨Dp, hAE, ?_, ?_, hident, hbound, hvanish⟩
  · intro U T hboxU hU i
    have hTI : closure T ⊆ I := hboxU.2.2.2.2.2
    have := hintball T hboxU.2.2.2.2.1 hTI i
    refine this.mono_measure (Measure.restrict_mono_set volume ?_)
    exact Set.prod_mono hU subset_rfl
  · intro i ψ hψ hsupp
    have hTcpt : IsCompact (Prod.snd '' tsupport ψ) :=
      hψ.2.1.isCompact.image continuous_snd
    have hTI : Prod.snd '' tsupport ψ ⊆ I := by
      rintro t ⟨z, hz, rfl⟩
      exact (hsupp hz).2
    obtain ⟨n, hn⟩ := hJcover _ hTcpt hTI
    have hsuppn : tsupport ψ ⊆ vec3Ball (0 : Vec3) R₁ ×ˢ J n := by
      intro z hz
      exact ⟨(hsupp hz).1, hn ⟨z, hz, rfl⟩⟩
    have hpn : IntegrableOn p (vec3Ball (0 : Vec3) R₁ ×ˢ J n) volume :=
      (hpint n).mono_set (Set.prod_mono (vec3Ball_mono hR₁R₀.le) subset_rfl)
    have hDn : IntegrableOn (fun z => Dp z i)
        (vec3Ball (0 : Vec3) R₁ ×ˢ J n) volume := by
      refine hintball (J n) ?_ ?_ i
      · rw [(hJcpt n).isClosed.closure_eq]
        exact hJcpt n
      · rw [(hJcpt n).isClosed.closure_eq]
        exact hJI n
    have hiter : (∫ t in J n, ∫ x in vec3Ball (0 : Vec3) R₁,
          p (x, t) * spatialPartial ψ i (x, t)) =
        -∫ t in J n, ∫ x in vec3Ball (0 : Vec3) R₁, Dp (x, t) i * ψ (x, t) := by
      have hinner2 : ∀ t : ℝ, (∫ x in vec3Ball (0 : Vec3) R₁, Dp (x, t) i * ψ (x, t)) =
          ∫ x in vec3Ball (0 : Vec3) R₁, D i (x, t) * ψ (x, t) := by
        intro t
        refine setIntegral_congr_fun (vec3Ball_measurable _ _) ?_
        intro x hx
        show Dp (x, t) i * ψ (x, t) = D i (x, t) * ψ (x, t)
        rw [hDpval (x, t) hx i]
      simp only [hinner2]
      exact hDpair i n ψ hψ.1 hψ.2.1 hsuppn
    exact spacetime_pairing_of_iterated hψ hsuppn hpn hDn hiter

end CKN.Core.Step4.OriginInstance
