/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.SetTheory.Cardinal.Finite
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.PadicLinearOfContinuous
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.FieldUnitFactors
public import Mathlib.Algebra.Module.PID
public import Mathlib.NumberTheory.Padics.ProperSpace
/-!
# Topological structure of a finite p-adic module

This file packages the PID step in the mixed-characteristic proof of
the local-field structure theory, the field-unit structure theorem.  Once the torsion submodule
  is known to
be a finite cyclic group of order `p^a`, and the torsion-free quotient has
rank `d`, the module is topologically the product of that cyclic factor and
`d` copies of `Z_p`.
-/

@[expose] public section

noncomputable
section

universe u

namespace LocalFieldTheory.DiscreteValuationField
namespace CompleteDVF
namespace higherPrincipalUnitGroup

/-- A finite topological `Z_p`-module with cyclic torsion of order `p^a` and
torsion-free quotient of rank `d` is topologically
`ZMod (p^a) × Z_p^d`.

The algebraic splitting is obtained by projectively lifting the quotient map
and applying `lequivProdOfRightSplitExact`.  For continuity, its restriction
to the finite torsion factor is automatic, while its restriction to the free
factor is a linear map out of a finite Cartesian power of `Z_p`. -/
noncomputable def chosenPadicModuleContinuousAddEquivZModProdFinPi
    (p : ℕ) [Fact p.Prime]
    (M : Type u) [TopologicalSpace M] [AddCommGroup M] [Module ℤ_[p] M]
    [ContinuousAdd M] [ContinuousSMul ℤ_[p] M]
    [T2Space M] [Module.Finite ℤ_[p] M]
    (a d : ℕ)
    [Finite (Submodule.torsion ℤ_[p] M)]
    (hcyclic : IsAddCyclic (Submodule.torsion ℤ_[p] M))
    (hcard : Nat.card (Submodule.torsion ℤ_[p] M) = p ^ a)
    (hfinrank : Module.finrank ℤ_[p]
      (M ⧸ Submodule.torsion ℤ_[p] M) = d) :
    (ZMod (p ^ a) × (Fin d → ℤ_[p])) ≃ₜ+ M := by
  let T : Submodule ℤ_[p] M := Submodule.torsion ℤ_[p] M
  let Q := M ⧸ T
  letI : Module.Finite ℤ_[p] Q := Module.Finite.quotient ℤ_[p] T
  letI : Module.IsTorsionFree ℤ_[p] Q :=
    Submodule.QuotientTorsion.instIsTorsionFree
  letI : Module.Free ℤ_[p] Q :=
    Module.free_of_finite_type_torsion_free'
  let b : Module.Basis (Fin d) ℤ_[p] Q :=
    Module.finBasisOfFinrankEq ℤ_[p] Q (by simpa [Q, T] using hfinrank)
  let q : M →ₗ[ℤ_[p]] Q := T.mkQ
  have hliftExists : ∃ lift : Q →ₗ[ℤ_[p]] M,
      q.comp lift = LinearMap.id :=
    Module.projective_lifting_property q LinearMap.id T.mkQ_surjective
  let lift : Q →ₗ[ℤ_[p]] M := Classical.choose hliftExists
  have hlift : q.comp lift = LinearMap.id := Classical.choose_spec hliftExists
  have hexact : LinearMap.range T.subtype = LinearMap.ker q := by
    change LinearMap.range T.subtype = LinearMap.ker T.mkQ
    rw [Submodule.range_subtype, Submodule.ker_mkQ]
  let split : (T × Q) ≃ₗ[ℤ_[p]] M :=
    lequivProdOfRightSplitExact T.injective_subtype hexact hlift
  let torsionEquiv : ZMod (p ^ a) ≃+ T := by
    rw [← hcard]
    exact zmodAddCyclicAddEquiv hcyclic
  let freeEquiv : (Fin d → ℤ_[p]) ≃ₗ[ℤ_[p]] Q := b.equivFun.symm
  let algebraic : (ZMod (p ^ a) × (Fin d → ℤ_[p])) ≃+ M :=
    (torsionEquiv.prodCongr freeEquiv.toAddEquiv).trans split.toAddEquiv
  let freeToM : (Fin d → ℤ_[p]) →ₗ[ℤ_[p]] M :=
    split.toLinearMap.comp
      ((LinearMap.inr ℤ_[p] T Q).comp freeEquiv.toLinearMap)
  have hfree : Continuous freeToM :=
    continuous_padicInt_finPi_linearMap d freeToM
  have htorsion : Continuous (fun z : ZMod (p ^ a) =>
      split (torsionEquiv z, (0 : Q))) :=
    continuous_of_discreteTopology
  have halgebraic : Continuous algebraic := by
    have hfun : (fun z : ZMod (p ^ a) × (Fin d → ℤ_[p]) => algebraic z) =
        fun z =>
          split (torsionEquiv z.1, (0 : Q)) +
            freeToM z.2 := by
      funext z
      change split (torsionEquiv z.1, freeEquiv z.2) =
        split (torsionEquiv z.1, 0) + split (0, freeEquiv z.2)
      rw [← split.map_add]
      simp
    change Continuous (fun z => algebraic z)
    rw [hfun]
    exact (htorsion.comp continuous_fst).add (hfree.comp continuous_snd)
  exact continuousAddEquivOfCompactToT2 algebraic halgebraic

end higherPrincipalUnitGroup
end CompleteDVF
end LocalFieldTheory.DiscreteValuationField
