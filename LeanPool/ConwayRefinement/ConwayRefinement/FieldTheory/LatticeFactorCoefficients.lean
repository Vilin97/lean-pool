/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.FieldTheory.LaurentFactorCoefficients
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.MonoidAlgebra.LatticeFunctional

/-!
# Clearing a scalar out of a factor over a finite-rank exponent lattice

A functional separating the exponents that occur collapses the lattice to a single variable
without merging any of them, and relabelling exponents commutes with extending coefficients. So a
factorisation whose product has coefficients in the subfield descends to the one-variable case,
where a monic factor of a monic polynomial has coefficients integral, hence algebraic, hence in
the subfield when it is relatively algebraically closed. Reading the coefficients back through the
separating functional clears one scalar out of the factor.
-/

universe u v w

namespace AddMonoidAlgebra

public section

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

omit [Algebra K L] in
/-- Coefficient extension is `Finsupp.mapRange` on the underlying finitely supported function. -/
theorem mapRingHom_apply' {M : Type*} [AddMonoid M] (f : K →+* L) (x : AddMonoidAlgebra K M) :
    AddMonoidAlgebra.mapRingHom M f x = ofCoeff (Finsupp.mapRange f (map_zero f) x.coeff) := rfl

omit [Algebra K L] in
/-- Relabelling exponents commutes with extending coefficients. -/
theorem mapDomain_mapRingHom {M N : Type*} [AddMonoid M] [AddMonoid N] (psi : M →+ N)
    (f : K →+* L) (x : AddMonoidAlgebra K M) :
    AddMonoidAlgebra.mapDomainRingHom L psi (AddMonoidAlgebra.mapRingHom M f x) =
      AddMonoidAlgebra.mapRingHom N f (AddMonoidAlgebra.mapDomainRingHom K psi x) := by
  exact (DFunLike.congr_fun (mapRingHom_comp_mapDomainRingHom f psi) x).symm

/-- Lattice form of scalar clearing: collapse the lattice to one variable along a functional that
separates the exponents in play. -/
theorem exists_scalar_of_mul_eq_map_lattice {k : ℕ}
    (hclosed : Algebra.IsRelativelyAlgebraicallyClosed K L)
    {q r : AddMonoidAlgebra L (Fin k → ℤ)} {P : AddMonoidAlgebra K (Fin k → ℤ)}
    (hq : q ≠ 0) (hr : r ≠ 0)
    (hqr : q * r = AddMonoidAlgebra.mapRingHom (Fin k → ℤ) (algebraMap K L) P) :
    ∃ c : L, c ≠ 0 ∧ ∀ g, c * q.coeff g ∈ (algebraMap K L).range := by
  classical
  obtain ⟨psi, hpsi⟩ := AddMonoidHom.exists_injOn_finInt (q.coeff.support ∪ r.coeff.support)
  have hsub : (q.coeff.support : Set (Fin k → ℤ)) ⊆ ((q.coeff.support ∪ r.coeff.support : Finset
    _) : Set _) :=
    fun x hx ↦ Finset.mem_coe.mpr (Finset.mem_union_left _ (Finset.mem_coe.mp hx))
  have hinjq : Set.InjOn psi (q.coeff.support : Set (Fin k → ℤ)) := hpsi.mono hsub
  have htransfer : ∀ g ∈ q.coeff.support,
      (AddMonoidAlgebra.mapDomainRingHom L psi q).coeff (psi g) = q.coeff g := fun g hg ↦
    Finsupp.mapDomain_apply' _ q.coeff hsub hpsi (Finset.mem_union_left _ hg)
  have hq0 : AddMonoidAlgebra.mapDomainRingHom L psi q ≠ 0 := by
    obtain ⟨g, hg⟩ := Finsupp.support_nonempty_iff.mpr (coeff_eq_zero.not.mpr hq)
    intro h0
    rw [h0] at htransfer
    exact (Finsupp.mem_support_iff.mp hg) (htransfer g hg).symm
  have hr0 : AddMonoidAlgebra.mapDomainRingHom L psi r ≠ 0 := by
    obtain ⟨g, hg⟩ := Finsupp.support_nonempty_iff.mpr (coeff_eq_zero.not.mpr hr)
    have hsubr : (r.coeff.support : Set (Fin k → ℤ)) ⊆ ((q.coeff.support ∪ r.coeff.support :
      Finset _) : Set _) :=
      fun x hx ↦ Finset.mem_coe.mpr (Finset.mem_union_right _ (Finset.mem_coe.mp hx))
    intro h0
    have := Finsupp.mapDomain_apply' ((q.coeff.support ∪ r.coeff.support : Finset _) : Set _)
      r.coeff hsubr hpsi
      (Finset.mem_union_right _ hg)
    have h0' : Finsupp.mapDomain psi r.coeff = 0 := by
      simpa only [mapDomainRingHom_apply, mapDomain, coeff_ofCoeff, coeff_zero]
        using congrArg AddMonoidAlgebra.coeff h0
    rw [h0'] at this
    exact (Finsupp.mem_support_iff.mp hg) this.symm
  have hrel : (AddMonoidAlgebra.mapDomainRingHom L psi q) *
      (AddMonoidAlgebra.mapDomainRingHom L psi r) =
      AddMonoidAlgebra.mapRingHom ℤ (algebraMap K L)
        (AddMonoidAlgebra.mapDomainRingHom K psi P) := by
    rw [← map_mul, hqr, mapDomain_mapRingHom]
  obtain ⟨c, hc, hcoeff⟩ :=
    LaurentPolynomial.exists_scalar_of_mul_eq_map hclosed hq0 hr0 hrel
  refine ⟨c, hc, fun g ↦ ?_⟩
  by_cases hg : g ∈ q.coeff.support
  · rw [← htransfer g hg]
    exact hcoeff _
  · rw [Finsupp.notMem_support_iff.mp hg, mul_zero]
    exact ⟨0, map_zero _⟩

/-- Scalar clearing over any free exponent group of finite rank. -/
theorem exists_scalar_of_mul_eq_map_free {H : Type w} [AddCommGroup H]
    (hfree : ∃ k : ℕ, Nonempty (H ≃+ (Fin k → ℤ)))
    (hclosed : Algebra.IsRelativelyAlgebraicallyClosed K L)
    {q r : AddMonoidAlgebra L H} {P : AddMonoidAlgebra K H} (hq : q ≠ 0) (hr : r ≠ 0)
    (hqr : q * r = AddMonoidAlgebra.mapRingHom H (algebraMap K L) P) :
    ∃ c : L, c ≠ 0 ∧ ∀ g, c * q.coeff g ∈ (algebraMap K L).range := by
  obtain ⟨k, ⟨e⟩⟩ := hfree
  have hinj : Function.Injective (e : H → (Fin k → ℤ)) := e.injective
  have htrans : ∀ (x : AddMonoidAlgebra L H) (g : H),
      (AddMonoidAlgebra.mapDomainRingHom L e.toAddMonoidHom x).coeff (e g) = x.coeff g := by
    intro x g
    rw [mapDomainRingHom_apply]
    exact Finsupp.mapDomain_apply_of_injective hinj x.coeff g
  have hq0 : AddMonoidAlgebra.mapDomainRingHom L e.toAddMonoidHom q ≠ 0 := by
    obtain ⟨g, hg⟩ := Finsupp.support_nonempty_iff.mpr (coeff_eq_zero.not.mpr hq)
    intro h0
    apply Finsupp.mem_support_iff.mp hg
    rw [← htrans q g, h0]
    rfl
  have hr0 : AddMonoidAlgebra.mapDomainRingHom L e.toAddMonoidHom r ≠ 0 := by
    obtain ⟨g, hg⟩ := Finsupp.support_nonempty_iff.mpr (coeff_eq_zero.not.mpr hr)
    intro h0
    apply Finsupp.mem_support_iff.mp hg
    rw [← htrans r g, h0]
    rfl
  have hrel : (AddMonoidAlgebra.mapDomainRingHom L e.toAddMonoidHom q) *
      (AddMonoidAlgebra.mapDomainRingHom L e.toAddMonoidHom r) =
      AddMonoidAlgebra.mapRingHom (Fin k → ℤ) (algebraMap K L)
        (AddMonoidAlgebra.mapDomainRingHom K e.toAddMonoidHom P) := by
    rw [← map_mul, hqr, mapDomain_mapRingHom]
  obtain ⟨c, hc, hcoeff⟩ := exists_scalar_of_mul_eq_map_lattice hclosed hq0 hr0 hrel
  refine ⟨c, hc, fun g ↦ ?_⟩
  rw [← htrans q g]
  exact hcoeff _

end

end AddMonoidAlgebra
