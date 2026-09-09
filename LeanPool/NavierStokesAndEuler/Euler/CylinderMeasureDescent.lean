/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.EulerProof
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

@[expose] public section

/-! A volume-preserving map of the real cylinder cover which commutes
with deck translations induces a measure-preserving cylinder map. The
proof compares genuine fundamental domains; it does not integrate a
nonzero periodic function over the whole real cover. -/

noncomputable section

namespace EulerCylinderMeasureDescent

open Set Function MeasureTheory EulerLiftedGradientSpace
open scoped Pointwise

variable (P : ℝ) [Fact (0 < P)]

local instance (priority := 2000) deckVAdd : VAdd (AddSubgroup.zmultiples P) LiftTangent where
  vadd c z := (z.1,(c : ℝ)+z.2)

local instance deckAction : AddAction (AddSubgroup.zmultiples P) LiftTangent where
  vadd := (· +ᵥ ·)
  zero_vadd z := by
    change (z.1,(0 : ℝ)+z.2)=z
    simp
  add_vadd c d z := by
    change (z.1,((c : ℝ)+(d : ℝ))+z.2) = (z.1,(c : ℝ)+((d : ℝ)+z.2))
    rw [add_assoc]

omit [Fact (0 < P)] in
theorem deck_apply (c : AddSubgroup.zmultiples P) (z : LiftTangent) :
    c +ᵥ z = (z.1,(c : ℝ)+z.2) := rfl

local instance deckMeasurable : MeasurableConstVAdd (AddSubgroup.zmultiples P) LiftTangent where
  measurable_const_vadd _c := measurable_fst.prodMk (measurable_const.add measurable_snd)

local instance deckInvariant : VAddInvariantMeasure (AddSubgroup.zmultiples P) LiftTangent volume
  where
  measure_preimage_vadd c s hs := by
    have hp := (MeasurePreserving.id (volume : Measure Vector3)).prod
      (measurePreserving_add_left (volume : Measure ℝ) (c : ℝ))
    exact hp.measure_preimage hs.nullMeasurableSet

omit [Fact (0 < P)] in
theorem coveringMap_deck (c : AddSubgroup.zmultiples P) (z : LiftTangent) :
    coveringMap P (c +ᵥ z) = coveringMap P z := by
  have hc : ((c : ℝ) : AddCircle P)=0 := (QuotientAddGroup.eq_zero_iff _).2 c.property
  simp only [deck_apply,coveringMap,AddCircle.coe_add,hc,zero_add]

def strip : Set LiftTangent := Prod.snd ⁻¹' Ioc (0 : ℝ) P

omit [Fact (0 < P)] in
theorem strip_measurable : MeasurableSet (strip P) := measurable_snd measurableSet_Ioc

theorem strip_fundamental : IsAddFundamentalDomain (AddSubgroup.zmultiples P) (strip P) volume := by
  have h := (isAddFundamentalDomain_Ioc (Fact.out : 0 < P) 0).preimage_of_equiv
    (G := AddSubgroup.zmultiples P) (H := AddSubgroup.zmultiples P)
    (f := (Prod.snd : LiftTangent → ℝ))
    (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure Vector3)) (ν := volume))
    (e := id) Function.bijective_id (fun _ _ => rfl)
  convert! h using 1
  simp only [zero_add,strip]

theorem coveringMap_measurePreserving :
    MeasurePreserving (coveringMap P) (volume.restrict (strip P)) (liftMeasure P) := by
  have hm : (volume : Measure LiftTangent).restrict (strip P) =
      (volume : Measure Vector3).prod ((volume : Measure ℝ).restrict (Ioc (0 : ℝ) P)) := by
    change (volume.prod volume).restrict (Prod.snd ⁻¹' Ioc (0 : ℝ) P) = _
    rw [← univ_prod,← Measure.prod_restrict,Measure.restrict_univ]
  rw [hm]
  have hp := (MeasurePreserving.id (volume : Measure Vector3)).prod (AddCircle.measurePreserving_mk
    P 0)
  simp only [zero_add] at hp
  convert! hp using 1

theorem quotient_set_measure (s : Set (LiftDomain P)) (hs : MeasurableSet s) :
    liftMeasure P s = volume (coveringMap P ⁻¹' s ∩ strip P) := by
  have h := (coveringMap_measurePreserving P).measure_preimage hs.nullMeasurableSet
  rw [Measure.restrict_apply ((coveringMap_measurePreserving P).measurable hs)] at h
  exact h.symm

theorem measurePreserving_of_cover
    (f : LiftTangent → LiftTangent) (g : LiftDomain P → LiftDomain P)
    (hf : MeasurePreserving f volume volume) (hg : Measurable g)
    (hdeck : ∀ (c : AddSubgroup.zmultiples P) z,
      f (z.1,(c : ℝ)+z.2) = ((f z).1,(c : ℝ)+(f z).2))
    (hcover : ∀ z, coveringMap P (f z)=g (coveringMap P z)) :
    MeasurePreserving g (liftMeasure P) (liftMeasure P) := by
  have hequiv (c : AddSubgroup.zmultiples P) : Semiconj f (c +ᵥ ·) (c +ᵥ ·) := hdeck c
  have hfd := strip_fundamental P
  have hfd' : IsAddFundamentalDomain (AddSubgroup.zmultiples P) (f ⁻¹' strip P) volume :=
    hfd.preimage_of_equiv hf.quasiMeasurePreserving (e := id) Function.bijective_id hequiv
  refine ⟨hg,?_⟩
  ext s hs
  rw [Measure.map_apply hg hs,quotient_set_measure P (g ⁻¹' s) (hg hs),quotient_set_measure P s hs]
  have hset : coveringMap P ⁻¹' (g ⁻¹' s) = f ⁻¹' (coveringMap P ⁻¹' s) := by
    ext z
    simp only [mem_preimage,hcover]
  rw [hset]
  have hA : MeasurableSet (coveringMap P ⁻¹' s) := (coveringMap_measurePreserving P).measurable hs
  calc
    volume (f ⁻¹' (coveringMap P ⁻¹' s) ∩ strip P) =
        volume (f ⁻¹' (coveringMap P ⁻¹' s) ∩ f ⁻¹' strip P) := by
      apply hfd.measure_set_eq hfd' (hf.measurable hA)
      intro c
      ext z
      change coveringMap P (f (c +ᵥ z)) ∈ s ↔ coveringMap P (f z) ∈ s
      rw [hequiv c z,coveringMap_deck]
    _ = volume (f ⁻¹' ((coveringMap P ⁻¹' s) ∩ strip P)) := by rw [preimage_inter]
    _ = volume ((coveringMap P ⁻¹' s) ∩ strip P) :=
      hf.measure_preimage (hA.inter (strip_measurable P)).nullMeasurableSet

end EulerCylinderMeasureDescent
