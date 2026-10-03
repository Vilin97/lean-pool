/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Infinite.AbsoluteFiniteQuotients
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData
/-!
# Transition maps between absolute finite quotients

The canonical finite quotient identifications commute with quotient
transition on the profinite side and restriction on the Galois side.
-/

@[expose] public section

noncomputable
section

namespace LocalClassFieldTheory

open LocalFieldTheory
open RamificationTheory

variable {K : Type} [Field K]

/-- Pullback of open normal subgroups is monotone. -/
theorem absoluteFiniteQuotientPreimage_mono
    {N M : OpenNormalSubgroup (localAbsoluteAbelianProfinite K)}
    (hNM : N ≤ M) :
    absoluteFiniteQuotientPreimage K N ≤
      absoluteFiniteQuotientPreimage K M := by
  intro σ hσ
  exact hNM hσ

/-- Inclusion of open normal subgroups reverses the corresponding fixed
fields. -/
theorem absoluteFiniteQuotientField_antitone
    {N M : OpenNormalSubgroup (localAbsoluteAbelianProfinite K)}
    (hNM : N ≤ M) :
    absoluteFiniteQuotientField K M ≤
      absoluteFiniteQuotientField K N := by
  intro x hx
  change x ∈ IntermediateField.fixedField
    (absoluteFiniteQuotientPreimage K M).toSubgroup at hx
  change x ∈ IntermediateField.fixedField
    (absoluteFiniteQuotientPreimage K N).toSubgroup
  rw [IntermediateField.mem_fixedField_iff] at hx ⊢
  intro σ hσ
  exact hx σ (absoluteFiniteQuotientPreimage_mono hNM hσ)

/-- The canonical transition map between two finite quotients. -/
noncomputable def absoluteFiniteQuotientTransition
    {N M : OpenNormalSubgroup (localAbsoluteAbelianProfinite K)}
    (hNM : N ≤ M) :
    localAbsoluteAbelianProfinite K ⧸ N.toSubgroup →ₜ*
      localAbsoluteAbelianProfinite K ⧸ M.toSubgroup := by
  letI : DiscreteTopology
      (localAbsoluteAbelianProfinite K ⧸ N.toSubgroup) :=
    QuotientGroup.discreteTopology N.isOpen'
  let f : localAbsoluteAbelianProfinite K ⧸ N.toSubgroup →*
      localAbsoluteAbelianProfinite K ⧸ M.toSubgroup :=
    QuotientGroup.map N.toSubgroup M.toSubgroup (MonoidHom.id _)
      (fun x hx => hNM hx)
  exact
    { f with
      continuous_toFun := continuous_of_discreteTopology }

/-- States the theorem `absoluteFiniteQuotientTransition_mk`. -/
@[simp]
theorem absoluteFiniteQuotientTransition_mk
    {N M : OpenNormalSubgroup (localAbsoluteAbelianProfinite K)}
    (hNM : N ≤ M) (x : localAbsoluteAbelianProfinite K) :
    absoluteFiniteQuotientTransition hNM (QuotientGroup.mk x) =
      QuotientGroup.mk x := by
  rfl

/-- Under the finite quotient identifications, quotient transition is
exactly restriction of automorphisms to the smaller fixed field. -/
theorem absoluteFiniteQuotientEquiv_transition
    {N M : OpenNormalSubgroup (localAbsoluteAbelianProfinite K)}
    (hNM : N ≤ M) :
    (intermediateFieldRestrictContinuous K
      (absoluteFiniteQuotientField K M)
      (absoluteFiniteQuotientField K N)
      (absoluteFiniteQuotientField_antitone hNM)).comp
        (ContinuousMonoidHom.toContinuousMonoidHom
          (absoluteFiniteQuotientEquiv K N)) =
      (ContinuousMonoidHom.toContinuousMonoidHom
        (absoluteFiniteQuotientEquiv K M)).comp
          (absoluteFiniteQuotientTransition hNM) := by
  apply ContinuousMonoidHom.ext
  intro x
  obtain ⟨p, rfl⟩ := QuotientGroup.mk'_surjective N.toSubgroup x
  obtain ⟨σ, rfl⟩ := QuotientGroup.mk'_surjective
    (commutator (intrinsicAbsoluteGalois K)).topologicalClosure p
  change intermediateFieldRestrictNormalHom
      (absoluteFiniteQuotientField K M)
      (absoluteFiniteQuotientField K N)
      (absoluteFiniteQuotientField_antitone hNM)
      (absoluteFiniteQuotientEquiv K N
        (QuotientGroup.mk
          (QuotientGroup.mk σ : localAbsoluteAbelianProfinite K))) =
    absoluteFiniteQuotientEquiv K M
      (absoluteFiniteQuotientTransition hNM
        (QuotientGroup.mk
          (QuotientGroup.mk σ : localAbsoluteAbelianProfinite K)))
  let r := intermediateFieldRestrictNormalHom
    (absoluteFiniteQuotientField K M)
    (absoluteFiniteQuotientField K N)
    (absoluteFiniteQuotientField_antitone hNM)
  have hrestrict :
      r (AlgEquiv.restrictNormalHom (absoluteFiniteQuotientField K N) σ) =
        AlgEquiv.restrictNormalHom (absoluteFiniteQuotientField K M) σ := by
    apply AlgEquiv.ext
    intro y
    apply Subtype.ext
    exact (intermediateFieldRestrictNormalHom_apply_val
        (absoluteFiniteQuotientField K M)
        (absoluteFiniteQuotientField K N)
        (absoluteFiniteQuotientField_antitone hNM)
        (AlgEquiv.restrictNormalHom
          (absoluteFiniteQuotientField K N) σ) y).trans
      ((AlgEquiv.restrictNormal_commutes σ
        (absoluteFiniteQuotientField K N)
        (IntermediateField.inclusion
          (absoluteFiniteQuotientField_antitone hNM) y)).trans
        (AlgEquiv.restrictNormal_commutes σ
          (absoluteFiniteQuotientField K M) y).symm)
  have hright := (congrArg (absoluteFiniteQuotientEquiv K M)
      (absoluteFiniteQuotientTransition_mk hNM
        (QuotientGroup.mk σ : localAbsoluteAbelianProfinite K))).trans
    (absoluteFiniteQuotientEquiv_mk_mk K M σ)
  exact (congrArg r (absoluteFiniteQuotientEquiv_mk_mk K N σ)).trans
    (hrestrict.trans hright.symm)

end LocalClassFieldTheory
