/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Henselian.EtaleLifting
import Mathlib.RingTheory.Polynomial.UniversalFactorizationRing
/-!
# Coprime factor lifting from the simple-root Hensel property

A coprime monic factorization over the residue field gives a point of the
universal coprime factorization algebra. This algebra is etale, so its residue
point lifts over a Henselian pair. The universal factors give the requested
factorization, with their degrees and prescribed reductions.
-/

namespace ValuationTheory.Henselian

open Polynomial

variable {R : Type*} [CommRing R] {I : Ideal R} [I.IsMaximal] [HenselianRing R I]

/-- A coprime monic factorization modulo a maximal Henselian ideal lifts to
a coprime monic factorization over the base ring with the same degrees. -/
theorem exists_coprime_factor_lift
    (f : R[X]) (gbar hbar : (R ⧸ I)[X])
    (hf : f.Monic) (hgbar : gbar.Monic) (hhbar : hbar.Monic)
    (hfac : f.map (Ideal.Quotient.mk I) = gbar * hbar)
    (hcop : IsCoprime gbar hbar) :
    ∃ g h : R[X], g.Monic ∧ h.Monic ∧ f = g * h ∧
      g.natDegree = gbar.natDegree ∧ h.natDegree = hbar.natDegree ∧
      g.map (Ideal.Quotient.mk I) = gbar ∧ h.map (Ideal.Quotient.mk I) = hbar ∧
      IsCoprime g h := by
  have : Nontrivial (R ⧸ I) :=
    Ideal.Quotient.nontrivial_iff.mpr (Ideal.IsMaximal.ne_top (inferInstance : I.IsMaximal))
  have hn : f.natDegree = gbar.natDegree + hbar.natDegree := by
    calc
      f.natDegree = (f.map (Ideal.Quotient.mk I)).natDegree :=
        (hf.natDegree_map (Ideal.Quotient.mk I)).symm
      _ = gbar.natDegree + hbar.natDegree := by
        rw [hfac, hgbar.natDegree_mul hhbar]
  let p : MonicDegreeEq R f.natDegree := MonicDegreeEq.mk f hf rfl
  let g₀ : MonicDegreeEq (R ⧸ I) gbar.natDegree := MonicDegreeEq.mk gbar hgbar rfl
  let h₀ : MonicDegreeEq (R ⧸ I) hbar.natDegree := MonicDegreeEq.mk hbar hhbar rfl
  let c : { q : MonicDegreeEq (R ⧸ I) gbar.natDegree ×
      MonicDegreeEq (R ⧸ I) hbar.natDegree //
      q.1.1 * q.2.1 = p.1.map (algebraMap R (R ⧸ I)) ∧ IsCoprime q.1.1 q.2.1 } :=
    ⟨(g₀, h₀), hfac.symm, hcop⟩
  let σ : UniversalCoprimeFactorizationRing gbar.natDegree hbar.natDegree hn p →ₐ[R]
      R ⧸ I :=
    (UniversalCoprimeFactorizationRing.homEquiv (R ⧸ I)
      gbar.natDegree hbar.natDegree hn p).symm c
  obtain ⟨τ, hτ⟩ := exists_etale_lift σ
  let factors := UniversalCoprimeFactorizationRing.homEquiv R
    gbar.natDegree hbar.natDegree hn p τ
  have hres : (UniversalCoprimeFactorizationRing.homEquiv (R ⧸ I)
      gbar.natDegree hbar.natDegree hn p ((Ideal.Quotient.mkₐ R I).comp τ)).1 = c.1 := by
    rw [hτ]
    exact congrArg Subtype.val
      ((UniversalCoprimeFactorizationRing.homEquiv (R ⧸ I)
        gbar.natDegree hbar.natDegree hn p).apply_symm_apply c)
  have hg : factors.1.1.1.map (Ideal.Quotient.mk I) = gbar := by
    have heq := UniversalCoprimeFactorizationRing.homEquiv_comp_fst R
      gbar.natDegree hbar.natDegree hn p τ (Ideal.Quotient.mkₐ R I)
    have hfst := congrArg (fun q => q.1.1) hres
    rw [heq] at hfst
    exact hfst
  have hh : factors.1.2.1.map (Ideal.Quotient.mk I) = hbar := by
    have heq := UniversalCoprimeFactorizationRing.homEquiv_comp_snd R
      gbar.natDegree hbar.natDegree hn p τ (Ideal.Quotient.mkₐ R I)
    have hsnd := congrArg (fun q => q.2.1) hres
    rw [heq] at hsnd
    exact hsnd
  refine ⟨factors.1.1.1, factors.1.2.1, factors.1.1.monic, factors.1.2.monic,
    ?_, ?_, ?_, hg, hh, factors.2.2⟩
  · simpa only [Algebra.algebraMap_self, Polynomial.map_id, p, MonicDegreeEq.mk_coe]
      using factors.2.1.symm
  · exact ((factors.1.1.monic.natDegree_map (Ideal.Quotient.mk I)).symm).trans
      (congrArg Polynomial.natDegree hg)
  · exact ((factors.1.2.monic.natDegree_map (Ideal.Quotient.mk I)).symm).trans
      (congrArg Polynomial.natDegree hh)

end ValuationTheory.Henselian
