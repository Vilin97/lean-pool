/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import Mathlib.GroupTheory.SpecificGroups.Alternating
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.MaximalFlagEncodingStepTwo
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.OrbitIncidenceQuotient
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.OrbitRepresentatives
/-!
# Prime-symmetry orbit quotient of the Fox--Neuwirth top-flag cycle

The completed top-flag chain is invariant over `ZMod p` under the selected prime symmetry group:
for odd primes the group consists of even permutations, while for `p = 2` both integer signs have
the same image modulo two.  Simplicial incidence is equivariant because relabelling commutes with
face restriction.

This module proves freeness of relabelling on barred permutations and hence on every nonempty
order-complex simplex.  It then applies the generic orbit-incidence quotient construction to the
unconditional top-flag cycle.  The resulting finite incidence cycle has one top cell and one facet
per prime-symmetry orbit and is the correct input for orbit-level zero counts.
-/

namespace NRR

open scoped BigOperators

variable {p d : Nat}

namespace BarredPermutation

/-- Relabelling of a barred permutation is free because its rank is a permutation. -/
theorem primeSymmetry_action_free
    (hp : Nat.Prime p) {g : PrimeSymmetry hp} {c : BarredPermutation p}
    (hgc : g • c = c) : g = 1 := by
  apply PrimeSymmetry.toPerm_injective hp
  have hsymm : (PrimeSymmetry.toPerm hp g).symm = 1 := by
    apply Equiv.ext
    intro i
    have hrank := congrArg (fun a : BarredPermutation p => a.rank i) hgc
    change c.rank ((PrimeSymmetry.toPerm hp g).symm i) = c.rank i at hrank
    exact c.rank.injective hrank
  have hperm : PrimeSymmetry.toPerm hp g = 1 := by
    calc
      PrimeSymmetry.toPerm hp g =
          (PrimeSymmetry.toPerm hp g).symm.symm :=
        (Equiv.symm_symm _).symm
      _ = (1 : Equiv.Perm (Fin p)).symm := congrArg Equiv.symm hsymm
      _ = 1 := by rfl
  simpa using hperm

end BarredPermutation

namespace FoxNeuwirthOrderComplex
namespace Simplex

/-- The prime symmetry action is free on every order-complex simplex. -/
theorem primeSymmetry_action_free
    (hp : Nat.Prime p) {g : PrimeSymmetry hp} {s : Simplex p d}
    (hgs : g • s = s) : g = 1 := by
  apply BarredPermutation.primeSymmetry_action_free hp
    (c := s 0)
  have hv := congrArg (fun t : Simplex p d => t 0) hgs
  simpa using hv

end Simplex

namespace PrimeOrbitCycle

open TopFlagSubdivision

/-- The sign of every selected prime-symmetry permutation becomes one in `ZMod p`. -/
theorem primeSymmetry_sign_cast_eq_one
    (hp : Nat.Prime p) (g : PrimeSymmetry hp) :
    ((((Equiv.Perm.sign (PrimeSymmetry.toPerm hp g) : ℤˣ) : ℤ) : ZMod p)) = 1 := by
  classical
  by_cases h2 : p = 2
  · subst p
    rcases Int.units_eq_one_or (Equiv.Perm.sign (PrimeSymmetry.toPerm hp g)) with hsign | hsign
    · rw [hsign]; decide
    · rw [hsign]; decide
  · have hmem : (PrimeSymmetry.toPerm hp g) ∈ alternatingGroup (Fin p) := by
      rw [← primeSymmetrySubgroup_eq_alternating hp h2]
      exact g.property
    have hsign : Equiv.Perm.sign (PrimeSymmetry.toPerm hp g) = 1 := by
      simpa [alternatingGroup] using hmem
    rw [hsign]; simp

/-- Bar indicators and hence bar-removal matrices are unchanged by relabelling. -/
theorem barDifferenceMatrix_smul
    (hp : Nat.Prime p) (g : PrimeSymmetry hp) (s : Simplex p (p - 1)) :
    barDifferenceMatrix (g • s) = barDifferenceMatrix s := by
  ext r k
  simp [barDifferenceMatrix, barIndicator]
  rfl

/-- The bar-removal determinant is invariant under prime-symmetry relabelling. -/
theorem barRemovalDeterminant_smul
    (hp : Nat.Prime p) (g : PrimeSymmetry hp) (s : Simplex p (p - 1)) :
    barRemovalDeterminant (g • s) = barRemovalDeterminant s := by
  unfold barRemovalDeterminant
  rw [barDifferenceMatrix_smul hp g s]

/-- The bottom-cell orientation changes by the label-permutation sign. -/
theorem permutationOrientationSign_smul
    (hp : Nat.Prime p) (g : PrimeSymmetry hp) (c : BarredPermutation p) :
    (((permutationOrientationSign (g • c) : Int) : ZMod p)) =
      (((permutationOrientationSign c : Int) : ZMod p)) := by
  classical
  unfold permutationOrientationSign
  change (((((Equiv.Perm.sign
    ((PrimeSymmetry.toPerm hp g).symm.trans c.rank) : ℤˣ) : ℤ) : ZMod p))) = _
  rw [Equiv.Perm.sign_trans, Equiv.Perm.sign_symm]
  push_cast
  rw [primeSymmetry_sign_cast_eq_one hp g]
  simp

/-- The completed top-flag chain coefficient is constant on prime-symmetry orbits. -/
theorem chain_smul
    (hp : Nat.Prime p) (g : PrimeSymmetry hp) (s : Simplex p (p - 1)) :
    TopFlagSubdivision.chain (g • s) = TopFlagSubdivision.chain s := by
  unfold TopFlagSubdivision.chain TopFlagSubdivision.integralCoefficient
  push_cast
  simp only [Simplex.prime_smul_apply]
  rw [permutationOrientationSign_smul hp g (s 0)]
  rw [barRemovalDeterminant_smul hp g s]

/-- Simplicial incidence is invariant under simultaneous relabelling. -/
theorem simplicialIncidence_smul
    (hp : Nat.Prime p)
    (g : PrimeSymmetry hp)
    (target : Simplex p d) (source : Simplex p (d + 1)) :
    SimplicialIncidence.incidence (R := ZMod p) (g • target) (g • source) =
      SimplicialIncidence.incidence (R := ZMod p) target source := by
  classical
  unfold SimplicialIncidence.incidence
  apply Finset.sum_congr rfl
  intro k hk
  have hequiv : (g • source).restrict (FaceMap.delete k)
      = g • (source.restrict (FaceMap.delete k)) := by
    apply Simplex.ext; intro i; rfl
  simp only [hequiv, smul_left_cancel_iff]

/-- The covering finite incidence cycle associated with the completed top-flag chain. -/
noncomputable def coveringCycle (hp : Nat.Prime p) : FiniteIncidenceCycle (ZMod p) := by
  have hdim : p - 1 = (p - 2) + 1 := by
    have := hp.two_le
    omega
  let c : SimplicialChain (ZMod p) p ((p - 2) + 1) := hdim ▸ TopFlagSubdivision.chain
  have hcycle : SimplicialChain.boundary c = 0 := by
    simpa [c, TopFlagSubdivision.boundary] using
      (MaximalFlagCode.topFlagCycle hp)
  exact SimplicialIncidence.ofCycle c hcycle

noncomputable instance instMulActionCoveringTopCell (hp : Nat.Prime p) :
    MulAction (PrimeSymmetry hp) (coveringCycle hp).TopCell :=
  inferInstanceAs (MulAction (PrimeSymmetry hp) (Simplex p ((p - 2) + 1)))

noncomputable instance instMulActionCoveringFacet (hp : Nat.Prime p) :
    MulAction (PrimeSymmetry hp) (coveringCycle hp).Facet :=
  inferInstanceAs (MulAction (PrimeSymmetry hp) (Simplex p (p - 2)))

/-- Equivariance data for the covering top-flag cycle. -/
noncomputable def coveringEquivariantData
    (hp : Nat.Prime p) :
    FiniteIncidenceCycle.EquivariantData
      (G := PrimeSymmetry hp) (coveringCycle hp) where
  coefficient_smul := by
    intro g s
    have hdim : p - 1 = (p - 2) + 1 := by
      have := hp.two_le
      omega
    change (hdim ▸ TopFlagSubdivision.chain) (g • s) =
      (hdim ▸ TopFlagSubdivision.chain) s
    have gen : ∀ {D : Nat} (h : p - 1 = D) (t : Simplex p D),
        (h ▸ TopFlagSubdivision.chain) (g • t) = (h ▸ TopFlagSubdivision.chain) t := by
      intro D h t
      subst h
      exact chain_smul hp g t
    exact gen hdim s
  incidence_smul := by
    intro g f s
    exact simplicialIncidence_smul hp g f s

/-- Prime-symmetry orbit quotient of the unconditional top-flag cycle. -/
noncomputable def orbitCycle (hp : Nat.Prime p) : FiniteIncidenceCycle (ZMod p) :=
  FiniteIncidenceCycle.orbitQuotient
    (G := PrimeSymmetry hp) (coveringCycle hp) (coveringEquivariantData hp)

/-- The quotient cycle has zero boundary by construction. -/
theorem orbitCycle_boundary_zero
    (hp : Nat.Prime p) (f : (orbitCycle hp).Facet) :
    ∑ c : (orbitCycle hp).TopCell,
      (orbitCycle hp).incidence f c * (orbitCycle hp).coefficient c = 0 :=
  (orbitCycle hp).boundary_zero f

/-- Top orbit type of the prime-symmetry quotient. -/
abbrev TopOrbit (hp : Nat.Prime p) :=
  (orbitCycle hp).TopCell

/-- Facet orbit type of the prime-symmetry quotient. -/
abbrev FacetOrbit (hp : Nat.Prime p) :=
  (orbitCycle hp).Facet

/-- Canonical representative of a top orbit. -/
noncomputable def topRepresentative
    (hp : Nat.Prime p) (q : TopOrbit hp) :
    (coveringCycle hp).TopCell :=
  FiniteIncidenceCycle.topRepresentative
    (G := PrimeSymmetry hp) (coveringCycle hp) q

/-- Canonical representative of a facet orbit. -/
noncomputable def facetRepresentative
    (hp : Nat.Prime p) (q : FacetOrbit hp) :
    (coveringCycle hp).Facet :=
  FiniteIncidenceCycle.facetRepresentative
    (G := PrimeSymmetry hp) (coveringCycle hp) q

end PrimeOrbitCycle
end FoxNeuwirthOrderComplex

namespace AAK

/-- Step S4: the completed Fox--Neuwirth simplicial cycle descends to a finite incidence cycle on
prime-symmetry top and facet orbits. -/
theorem simplestRoute_primeOrbitCycle_complete :
    ∀ {p : Nat} (hp : Nat.Prime p),
      Nonempty (FiniteIncidenceCycle.{0, 0, 0} (ZMod p)) :=
  fun hp => ⟨FoxNeuwirthOrderComplex.PrimeOrbitCycle.orbitCycle hp⟩

end AAK

end NRR
