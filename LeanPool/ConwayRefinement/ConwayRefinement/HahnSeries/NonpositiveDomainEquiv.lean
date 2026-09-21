/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.DomainEquiv
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Nonpositive
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrderType

/-!
# Reindexing nonpositive Hahn series along an exponent equivalence

An ordered additive equivalence of exponent groups induces a ring equivalence of their
nonpositive Hahn-series rings. Since the exponent types may live in different universes, support
order types are compared after lifting both ordinals to a common universe.

This is the exponent-domain transport needed when LM24 assumption `(A1)_σ` identifies an
Archimedean stratum with the additive ordered group of real numbers.
-/

public noncomputable section

namespace HahnSeries.Nonpositive

universe u v w

variable {G : Type u} {H : Type v} {K : Type w}
variable [LinearOrder G] [AddCommGroup G] [IsOrderedAddMonoid G]
variable [LinearOrder H] [AddCommGroup H] [IsOrderedAddMonoid H]
variable [CommRing K]

/-- Reindex nonpositive Hahn series along an ordered additive equivalence of exponent groups. -/
def embDomainRingEquiv (e : G ≃+o H) : Nonpositive G K ≃+* Nonpositive H K where
  toFun x := ⟨HahnSeries.embDomainRingEquiv e x, by
    rw [HahnSeries.mem_nonpositiveSubring]
    intro h hh
    rw [HahnSeries.support_embDomainRingEquiv] at hh
    obtain ⟨g, hg, rfl⟩ := hh
    change e g ≤ 0
    simpa only [map_zero] using e.strictMono.monotone (support_subset x hg)⟩
  invFun x := ⟨HahnSeries.embDomainRingEquiv e.symm x, by
    rw [HahnSeries.mem_nonpositiveSubring]
    intro g hg
    rw [HahnSeries.support_embDomainRingEquiv] at hg
    obtain ⟨h, hh, rfl⟩ := hg
    change e.symm h ≤ 0
    simpa only [map_zero] using e.symm.strictMono.monotone (support_subset x hh)⟩
  left_inv x := by
    apply Subtype.ext
    ext g
    have h := HahnSeries.embDomainRingEquiv_coeff e.symm
      (HahnSeries.embDomainRingEquiv e (x : K⟦G⟧)) (e g)
    rw [e.symm_apply_apply, HahnSeries.embDomainRingEquiv_coeff] at h
    exact h
  right_inv x := by
    apply Subtype.ext
    ext h
    have hh := HahnSeries.embDomainRingEquiv_coeff e
      (HahnSeries.embDomainRingEquiv e.symm (x : K⟦H⟧)) (e.symm h)
    rw [e.apply_symm_apply, HahnSeries.embDomainRingEquiv_coeff] at hh
    exact hh
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul (HahnSeries.embDomainRingEquiv e) (x : K⟦G⟧) y
  map_add' x y := by
    apply Subtype.ext
    exact map_add (HahnSeries.embDomainRingEquiv e) (x : K⟦G⟧) y

/-- The underlying Hahn series is the unrestricted exponent-domain equivalence. -/
@[simp]
theorem coe_embDomainRingEquiv (e : G ≃+o H) (x : Nonpositive G K) :
    (embDomainRingEquiv e x : K⟦H⟧) = HahnSeries.embDomainRingEquiv e x :=
  (rfl)

/-- Reindexing identifies supports as ordered sets, so their order types agree after lifting. -/
theorem lift_supportOrderType_embDomainRingEquiv (e : G ≃+o H)
    (x : Nonpositive G K) :
    Ordinal.lift.{u, v}
        (HahnSeries.supportOrderType (embDomainRingEquiv e x : K⟦H⟧)) =
      Ordinal.lift.{v, u} (HahnSeries.supportOrderType (x : K⟦G⟧)) := by
  letI : WellFoundedLT (x : K⟦G⟧).support := (x : K⟦G⟧).isWF_support
  letI : WellFoundedLT (embDomainRingEquiv e x : K⟦H⟧).support :=
    (embDomainRingEquiv e x : K⟦H⟧).isWF_support
  let supportEquiv : (embDomainRingEquiv e x : K⟦H⟧).support ≃o
      (x : K⟦G⟧).support :=
    (OrderIso.setCongr _ (e '' (x : K⟦G⟧).support) (by
      rw [coe_embDomainRingEquiv, HahnSeries.support_embDomainRingEquiv])).trans
        (StrictMonoOn.orderIso e (x : K⟦G⟧).support
          (e.strictMono.strictMonoOn (x : K⟦G⟧).support)).symm
  rw [HahnSeries.supportOrderType_eq_typeLT (OrderIso.refl _),
    HahnSeries.supportOrderType_eq_typeLT (OrderIso.refl _)]
  exact supportEquiv.toRelIsoLT.ordinal_lift_type_eq

end HahnSeries.Nonpositive
