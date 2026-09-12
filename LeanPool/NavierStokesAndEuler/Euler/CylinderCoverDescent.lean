/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.LiftedGradientSpace
import LeanPool.NavierStokesAndEuler.Euler.CylinderMeasureDescent

/-! Canonical descent of periodic cover fields and deck-equivariant maps
to the cylinder, with genuine continuity, inverse and volume properties. -/

@[expose] public section


noncomputable section

namespace EulerCylinderCoverDescent

open Set Function MeasureTheory EulerLiftedGradientSpace

variable (P : ℝ) [Fact (0 < P)]

/-- Section point, given by `(q.1,(AddCircle.equivIoc P 0 q.2 : ℝ))`. -/
def sectionPoint (q : LiftDomain P) : LiftTangent :=
  (q.1,(AddCircle.equivIoc P 0 q.2 : ℝ))

theorem coveringMap_sectionPoint (q : LiftDomain P) : coveringMap P (sectionPoint P q)=q := by
  simp only [sectionPoint,coveringMap,AddCircle.coe_equivIoc,Prod.mk.eta]

theorem sectionPoint_measurable : Measurable (sectionPoint P) :=
  measurable_fst.prodMk ((measurable_subtype_coe.comp
    (AddCircle.measurableEquivIoc P 0).measurable).comp measurable_snd)

/-- Descend, given by `f (sectionPoint P q)`. -/
def descend {V : Type*} (f : LiftTangent → V) (q : LiftDomain P) : V := f (sectionPoint P q)

theorem descend_cover {V : Type*} (f : LiftTangent → V)
    (hf : ∀ a b, coveringMap P a = coveringMap P b → f a = f b) (z : LiftTangent) :
    descend P f (coveringMap P z)=f z :=
  hf _ _ (coveringMap_sectionPoint P (coveringMap P z))

theorem descend_measurable {V : Type*} [MeasurableSpace V] (f : LiftTangent → V)
    (hf : Measurable f) : Measurable (descend P f) := hf.comp (sectionPoint_measurable P)

theorem descend_continuous {V : Type*} [TopologicalSpace V] (f : LiftTangent → V)
    (hf : Continuous f) (he : ∀ a b, coveringMap P a = coveringMap P b → f a = f b) :
    Continuous (descend P f) := by
  apply (coveringMap_isOpenQuotient P).isQuotientMap.continuous_iff.mpr
  have h : descend P f ∘ coveringMap P = f := funext (descend_cover P f he)
  rw [h]
  exact hf

theorem descend_joint_continuous {K V : Type*} [TopologicalSpace K] [TopologicalSpace V]
    (f : K → LiftTangent → V) (hf : Continuous (Function.uncurry f))
    (he : ∀ t a b, coveringMap P a = coveringMap P b → f t a = f t b) :
    Continuous (fun z : K × LiftDomain P => descend P (f z.1) z.2) := by
  apply (IsOpenQuotientMap.id.prodMap (coveringMap_isOpenQuotient
      P)).isQuotientMap.continuous_iff.mpr
  have h : (fun z : K × LiftDomain P => descend P (f z.1) z.2) ∘
      Prod.map id (coveringMap P) = Function.uncurry f := by
    funext z
    exact descend_cover P (f z.1) (he z.1) z.2
  rw [h]
  exact hf

omit [Fact (0 < P)] in
theorem fiber_constant_of_deck {V : Type*} (f : LiftTangent → V)
    (hf : ∀ (c : AddSubgroup.zmultiples P) z, f (z.1, (c : ℝ) + z.2) = f z)
    (a b : LiftTangent) (h : coveringMap P a = coveringMap P b) : f a=f b := by
  have h₁ : a.1=b.1 := congrArg (fun q : LiftDomain P => q.1) h
  have h₂ : (a.2 : AddCircle P)=(b.2 : AddCircle P) :=
    congrArg (fun q : LiftDomain P => q.2) h
  have hm : a.2-b.2 ∈ AddSubgroup.zmultiples P := QuotientAddGroup.eq_iff_sub_mem.mp h₂
  let c : AddSubgroup.zmultiples P := ⟨a.2-b.2,hm⟩
  have hz : (b.1,(c : ℝ)+b.2)=a := by
    apply Prod.ext
    · exact h₁.symm
    · exact sub_add_cancel a.2 b.2
  rw [← hz]
  exact hf c b

/-- Descend map, given by `descend P (coveringMap P ∘ f)`. -/
def descendMap (f : LiftTangent → LiftTangent) : LiftDomain P → LiftDomain P :=
  descend P (coveringMap P ∘ f)

variable (f : LiftTangent → LiftTangent)
  (hdeck : ∀ (c : AddSubgroup.zmultiples P) z,
    f (z.1, (c : ℝ) + z.2) = ((f z).1, (c : ℝ) + (f z).2))

include hdeck in
omit [Fact (0 < P)] in
theorem map_fiber_constant (a b : LiftTangent) (h : coveringMap P a = coveringMap P b) :
    coveringMap P (f a)=coveringMap P (f b) := by
  apply fiber_constant_of_deck P (coveringMap P ∘ f) _ a b h
  intro c z
  change coveringMap P (f (z.1,(c : ℝ)+z.2))=coveringMap P (f z)
  rw [hdeck]
  exact EulerCylinderMeasureDescent.coveringMap_deck P c (f z)

include hdeck in
theorem descendMap_cover (z : LiftTangent) :
    descendMap P f (coveringMap P z)=coveringMap P (f z) :=
  descend_cover P (coveringMap P ∘ f) (map_fiber_constant P f hdeck) z

include hdeck in
theorem descendMap_continuous (hf : Continuous f) : Continuous (descendMap P f) :=
  descend_continuous P _ ((coveringMap_isOpenQuotient P).continuous.comp hf)
    (map_fiber_constant P f hdeck)

include hdeck in
theorem descendMap_measurePreserving (hf : MeasurePreserving f volume volume) :
    MeasurePreserving (descendMap P f) (liftMeasure P) (liftMeasure P) :=
  EulerCylinderMeasureDescent.measurePreserving_of_cover P f (descendMap P f) hf
    (descend_measurable P _ ((coveringMap_isOpenQuotient P).continuous.measurable.comp
        hf.measurable))
    hdeck (fun z => (descendMap_cover P f hdeck z).symm)

include hdeck in
theorem descendMap_leftInverse (g : LiftTangent → LiftTangent)
    (hg : ∀ (c : AddSubgroup.zmultiples P) z,
      g (z.1, (c : ℝ) + z.2) = ((g z).1, (c : ℝ) + (g z).2))
    (hgf : Function.LeftInverse g f) :
    Function.LeftInverse (descendMap P g) (descendMap P f) := by
  intro q
  obtain ⟨z,rfl⟩ := (coveringMap_isOpenQuotient P).surjective q
  rw [descendMap_cover P f hdeck,descendMap_cover P g hg,hgf]

end EulerCylinderCoverDescent
