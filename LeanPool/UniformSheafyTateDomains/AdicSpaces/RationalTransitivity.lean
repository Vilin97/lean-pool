/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.SpaRationalSubsetCorrespondence
import LeanPool.UniformSheafyTateDomains.AdicSpaces.RelativeDescent

/-!
# Existential transitivity of rational localization

Huber, *Continuous valuations*, Prop 3.9 / Lemma 1.5(ii)–(iii); Wedhorn
Prop 8.2(2) + Remark 8.4, in existential form (2026-07-29 route review): for a
rational datum `D` on a complete Tate `A` and a rational datum `E` on
`B := 𝒪_A(D)`, there is a rational datum `F` on `A` with
`𝒪_B(E) ≃+* 𝒪_A(F)` bicontinuously.

The heavy topological content is already in the library:
`exists_downstairs_rationalDatum` (the perturbation into the dense
localization image, simultaneous denominator clearing, and the dominated
unit-power padding) and the noetherian-free `keystone`
(Wedhorn Lemma 8.1 / Prop 8.2(2)).  This file adds only the glue:

* `rationalOpenEqEquiv` — the generic equal-open bicontinuous equivalence of
  section rings (restriction maps both ways);
* `imgDatum_interRational_rationalOpen` — intersecting the downstairs datum
  with the base `D` does not change the upstairs rational open;
* `exists_rationalLocalization_transitivity` — the assembly.
-/

@[expose] public section

open scoped Classical

namespace ValuationSpectrum

universe u

variable {A : Type u} [CommRing A] [TopologicalSpace A]

section EqOpen

variable [IsTopologicalRing A] [PlusSubring A] [IsHuberRing A]
  [HasLocLiftPowerBounded A]

/-- **The equal-open equivalence of section rings**: two rational data with the
same rational open have canonically bicontinuously isomorphic completed
localizations (restriction maps both ways; Wedhorn Prop 8.2(1) uniqueness). -/
noncomputable def rationalOpenEqEquiv (D D' : RationalLocData A)
    (h : rationalOpen D.T D.s = rationalOpen D'.T D'.s) :
    presheafValue D ≃+* presheafValue D' where
  toFun := restrictionMap D D' h.ge
  invFun := restrictionMap D' D h.le
  left_inv x := by
    have hc := congrFun (restrictionMap_comp D D' D h.ge h.le) x
    rw [Function.comp_apply] at hc
    rw [hc]
    exact congrFun (restrictionMap_id D) x
  right_inv x := by
    have hc := congrFun (restrictionMap_comp D' D D' h.le h.ge) x
    rw [Function.comp_apply] at hc
    rw [hc]
    exact congrFun (restrictionMap_id D') x
  map_mul' := map_mul _
  map_add' := map_add _

theorem rationalOpenEqEquiv_continuous (D D' : RationalLocData A)
    (h : rationalOpen D.T D.s = rationalOpen D'.T D'.s) :
    Continuous (rationalOpenEqEquiv D D' h) :=
  restrictionMapHom_continuous D D' h.ge

theorem rationalOpenEqEquiv_symm_continuous (D D' : RationalLocData A)
    (h : rationalOpen D.T D.s = rationalOpen D'.T D'.s) :
    Continuous (rationalOpenEqEquiv D D' h).symm :=
  restrictionMapHom_continuous D' D h.le

end EqOpen

section Transitivity

variable [IsTateRing A] [PlusSubring A]

/-- Intersecting the downstairs datum with the base does not change the
upstairs rational open: an upstairs `Spa`-point's canonical pull-back already
lies in `R(D)`. -/
theorem imgDatum_interRational_rationalOpen
    (D W : RationalLocData A) (hD : D.IsRational) (hW : W.IsRational) :
    rationalOpen
        (imgDatum D (D.interRational W hD hW)
          (D.interRational_isRational W hD hW).span_eq_top).T
        (imgDatum D (D.interRational W hD hW)
          (D.interRational_isRational W hD hW).span_eq_top).s =
      rationalOpen (imgDatum D W hW.span_eq_top).T
        (imgDatum D W hW.span_eq_top).s := by
  ext w
  rw [imgDatum_mem_rationalOpen_iff, imgDatum_mem_rationalOpen_iff]
  constructor
  · rintro ⟨hspa, hmem⟩
    refine ⟨hspa, ?_⟩
    rw [RationalLocData.interRational_rationalOpen D W hD hW] at hmem
    exact hmem.2
  · rintro ⟨hspa, hmem⟩
    refine ⟨hspa, ?_⟩
    rw [RationalLocData.interRational_rationalOpen D W hD hW]
    exact ⟨(comap_canonicalMap_mem_rationalOpen_inter_spa D ⟨w, hspa⟩).1, hmem⟩

variable [NonarchimedeanRing A]
  [IsRingOfIntegralElements (A⁺ : Subring A)] [HasLocLiftPowerBounded A]

/-- **Existential transitivity of rational localization** (Huber Lemma
1.5(ii)–(iii) / Wedhorn Prop 8.2(2) + Rem 8.4): a rational localization of a
rational localization is bicontinuously a single rational localization of the
base.  `F` is the intersection of the base datum with the descended datum;
the equivalence is [equal-open] ∘ [equal-open] ∘ [keystone⁻¹]. -/
theorem exists_rationalLocalization_transitivity
    (D : RationalLocData A) (hD : D.IsRational)
    (E : RationalLocData (presheafValue D)) (hE : E.IsRational) :
    ∃ (F : RationalLocData A) (_ : F.IsRational)
      (e : presheafValue E ≃+* presheafValue F),
      Continuous ⇑e ∧ Continuous ⇑e.symm := by
  classical
  obtain ⟨W, hW, hEW⟩ := exists_downstairs_rationalDatum D hD E hE
  refine ⟨D.interRational W hD hW, D.interRational_isRational W hD hW, ?_⟩
  have hF : (D.interRational W hD hW).IsRational :=
    D.interRational_isRational W hD hW
  have hFD : rationalOpen (D.interRational W hD hW).T
      (D.interRational W hD hW).s ⊆ rationalOpen D.T D.s :=
    D.interRational_subset_left W hD hW
  have himg :
      rationalOpen (imgDatum D (D.interRational W hD hW)
          hF.span_eq_top).T
        (imgDatum D (D.interRational W hD hW) hF.span_eq_top).s =
      rationalOpen (imgDatum D W hW.span_eq_top).T
        (imgDatum D W hW.span_eq_top).s :=
    imgDatum_interRational_rationalOpen D W hD hW
  haveI hTateB : IsTateRing (presheafValue D) :=
    presheafValue_isTateRing_concrete D
  haveI : IsHuberRing (presheafValue D) := hTateB.toIsHuberRing
  refine ⟨((rationalOpenEqEquiv E (imgDatum D W hW.span_eq_top) hEW).trans
    ((rationalOpenEqEquiv (imgDatum D W hW.span_eq_top)
      (imgDatum D (D.interRational W hD hW) hF.span_eq_top)
      himg.symm).trans
    (keystone D hF.span_eq_top hFD).symm)), ?_, ?_⟩
  · show Continuous fun x => (keystone D hF.span_eq_top hFD).symm
      ((rationalOpenEqEquiv (imgDatum D W hW.span_eq_top)
        (imgDatum D (D.interRational W hD hW) hF.span_eq_top) himg.symm)
        ((rationalOpenEqEquiv E (imgDatum D W hW.span_eq_top) hEW) x))
    exact Continuous.comp (keystoneInv_continuous D hF.span_eq_top hFD)
      (Continuous.comp (rationalOpenEqEquiv_continuous _ _ himg.symm)
        (rationalOpenEqEquiv_continuous _ _ hEW))
  · show Continuous fun x =>
      (rationalOpenEqEquiv E (imgDatum D W hW.span_eq_top) hEW).symm
      ((rationalOpenEqEquiv (imgDatum D W hW.span_eq_top)
        (imgDatum D (D.interRational W hD hW) hF.span_eq_top)
          himg.symm).symm
        ((keystone D hF.span_eq_top hFD) x))
    exact Continuous.comp (rationalOpenEqEquiv_symm_continuous _ _ hEW)
      (Continuous.comp (rationalOpenEqEquiv_symm_continuous _ _ himg.symm)
        (keystoneHom_continuous D hF.span_eq_top))

end Transitivity

end ValuationSpectrum
