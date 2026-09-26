/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.Unramified.HenselianAlgebraicExtension
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Henselian.ValuationExtensionCriterion
/-!
# the unramified base-change theorem: irreducible reduction source

The base-change proof uses the following exact Hensel step.  If a
monic polynomial over a Henselian valuation ring is irreducible over the
fraction field and its reduction is separable, then that reduction is already
irreducible.  Otherwise a nontrivial residual factorization is coprime and
Hensel lifting contradicts irreducibility upstairs.
-/

@[expose] public section

noncomputable
section

open scoped Polynomial

namespace AlgebraicNumberTheory
namespace Valuations

/-- A monic polynomial irreducible over the valued field has irreducible
reduction whenever that reduction is separable. -/
theorem irreducible_residue_of_irreducible_of_separable_of_henselian
    {K : Type*} [Field K]
    (V : ValuationSubring K)
    (hhens : ValuationTheory.DiscreteValuationField.HenselFactorizationProperty V)
    {f : V[X]} (hf : f.Monic)
    (hirr : Irreducible (f.map (algebraMap V K)))
    (hsep : (f.map (IsLocalRing.residue V)).Separable) :
    Irreducible (f.map (IsLocalRing.residue V)) := by
  let qbar := f.map (IsLocalRing.residue V)
  have hqmonic : qbar.Monic := hf.map (IsLocalRing.residue V)
  have hinj : Function.Injective (algebraMap V K) := by
    intro a b hab
    exact Subtype.ext hab
  have hfFieldDegree :
      (f.map (algebraMap V K)).natDegree = f.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hinj f
  have hfpos : 0 < f.natDegree := by
    rw [← hfFieldDegree]
    exact hirr.natDegree_pos
  have hqne : qbar ≠ 1 := by
    intro hq
    have hfzero : f.natDegree = 0 := by
      rw [← hf.natDegree_map (IsLocalRing.residue V), show
        f.map (IsLocalRing.residue V) = qbar from rfl, hq]
      simp
    exact (Nat.ne_of_gt hfpos) hfzero
  rw [Polynomial.irreducible_of_monic hqmonic hqne]
  intro gbar hbar hgmonic hhmonic hfactor
  have hprodSep : (gbar * hbar).Separable := by
    rw [hfactor]
    exact hsep
  have hcoprime : IsCoprime gbar hbar := hprodSep.isCoprime
  have hlift : DiscreteValuationField.MonicResidualCoprimeFactorLifting V :=
    DiscreteValuationField.monicResidualCoprimeFactorLifting_of_henselFactorization
      hhens
  have hdegree :=
    hlift.irreducible_monic_reduction_coprime_factor_degree_zero
      hf hirr hgmonic hhmonic (by simpa [qbar] using hfactor.symm) hcoprime
  exact hdegree.imp hgmonic.natDegree_eq_zero.mp
    hhmonic.natDegree_eq_zero.mp

end Valuations
end AlgebraicNumberTheory

end
