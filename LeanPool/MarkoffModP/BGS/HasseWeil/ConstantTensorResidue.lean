/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteFieldCompositum
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber

/-!
# Residue fields of constant tensor extensions

For a maximal ideal `q` of `S ⊗[C] R`, let `p` be its contraction to `R`.
Reduction gives a canonical map

`S ⊗[C] κ(p) → κ(q)`.

This file proves that the map is surjective.  For finite fields, the residue
degree is therefore the least common multiple of the degrees of `S` and
`κ(p)` over `C`.  The result is ring-theoretic; applying it to places in a
constant extension additionally requires identifying the normalization after
base change with the corresponding tensor ring.
-/

@[expose] public section

open scoped TensorProduct

namespace BGS.HasseWeil

noncomputable section

/-- The scalar extension of a commutative `C`-algebra `R` to a commutative
`C`-algebra `S`. -/
abbrev ConstantTensorRing (C R S : Type*)
    [CommRing C] [CommRing R] [CommRing S]
    [Algebra C R] [Algebra C S] :=
  S ⊗[C] R

section General

variable (C R S : Type*)
  [CommRing C] [CommRing R] [CommRing S]
  [Algebra C R] [Algebra C S]

local instance constantTensorRingAlgebra :
    Algebra R (ConstantTensorRing C R S) :=
  Algebra.TensorProduct.rightAlgebra

/-- The canonical map from the tensor product of the enlarged constants and
the contracted residue field to the upstairs residue field. -/
def constantTensorResidueAlgHom
    (q : Ideal (ConstantTensorRing C R S)) [q.IsMaximal] :
    let p := q.comap
      (Algebra.TensorProduct.includeRight
        (R := C) (A := S) (B := R)).toRingHom
    S ⊗[C] p.ResidueField →ₐ[C] q.ResidueField := by
  let p := q.comap
    (Algebra.TensorProduct.includeRight
      (R := C) (A := S) (B := R)).toRingHom
  let iR := Algebra.TensorProduct.includeRight
    (R := C) (A := S) (B := R)
  let iS := Algebra.TensorProduct.includeLeft
    (R := C) (S := C) (A := S) (B := R)
  let fS : S →ₐ[C] q.ResidueField :=
    (IsScalarTower.toAlgHom C (ConstantTensorRing C R S)
      q.ResidueField).comp iS
  let fp : p.ResidueField →ₐ[C] q.ResidueField :=
    Ideal.ResidueField.mapₐ p q iR rfl
  exact Algebra.TensorProduct.lift fS fp fun _ _ => Commute.all _ _

/-- The canonical residue-field map of a constant tensor extension is
surjective. -/
theorem constantTensorResidueAlgHom_surjective
    (q : Ideal (ConstantTensorRing C R S)) [q.IsMaximal] :
    Function.Surjective (constantTensorResidueAlgHom C R S q) := by
  let p := q.comap
    (Algebra.TensorProduct.includeRight
      (R := C) (A := S) (B := R)).toRingHom
  intro z
  obtain ⟨a, rfl⟩ := q.algebraMap_residueField_surjective z
  induction a using TensorProduct.inductionOn with
  | tmul s r =>
      refine ⟨s ⊗ₜ[C] algebraMap R p.ResidueField r, ?_⟩
      simp only [constantTensorResidueAlgHom,
        Algebra.TensorProduct.lift_tmul, AlgHom.coe_comp,
        Function.comp_apply, Ideal.ResidueField.mapₐ_apply,
        Algebra.TensorProduct.includeLeft_apply]
      have hpmap :
          (Ideal.ResidueField.map p q
            (Algebra.TensorProduct.includeRight
              (R := C) (A := S) (B := R)).toRingHom rfl)
              (algebraMap R p.ResidueField r) =
            algebraMap (ConstantTensorRing C R S) q.ResidueField
              (Algebra.TensorProduct.includeRight
                (R := C) (A := S) (B := R) r) := by
        exact Ideal.ResidueField.map_algebraMap p q
          (Algebra.TensorProduct.includeRight
            (R := C) (A := S) (B := R)).toRingHom rfl r
      rw [hpmap]
      change
        algebraMap (ConstantTensorRing C R S) q.ResidueField
            (s ⊗ₜ[C] (1 : R)) *
          algebraMap (ConstantTensorRing C R S) q.ResidueField
            ((1 : S) ⊗ₜ[C] r) =
        algebraMap (ConstantTensorRing C R S) q.ResidueField
          (s ⊗ₜ[C] r)
      rw [← map_mul]
      simp
  | add x y hx hy =>
      obtain ⟨x', hx'⟩ := hx
      obtain ⟨y', hy'⟩ := hy
      refine ⟨x' + y', ?_⟩
      rw [map_add, map_add, hx', hy']

end General

section FiniteFields

variable (C R S : Type*)
  [Field C] [CommRing R] [Field S]
  [Algebra C R] [Algebra C S]

local instance finiteConstantTensorRingAlgebra :
    Algebra R (ConstantTensorRing C R S) :=
  Algebra.TensorProduct.rightAlgebra

/-- For finite fields, the residue field of a constant tensor extension has
degree equal to the least common multiple of the new-constant degree and the
contracted residue degree. -/
theorem constantTensorResidue_finrank_eq_lcm
    (q : Ideal (ConstantTensorRing C R S)) [q.IsMaximal]
    [Finite C] [Finite S]
    [Finite ((q.comap (Algebra.TensorProduct.includeRight
      (R := C) (A := S) (B := R)).toRingHom).ResidueField)]
    [Finite q.ResidueField] :
    let p := q.comap
      (Algebra.TensorProduct.includeRight
        (R := C) (A := S) (B := R)).toRingHom
    Module.finrank C q.ResidueField =
      Nat.lcm (Module.finrank C S)
        (Module.finrank C p.ResidueField) := by
  let p := q.comap
    (Algebra.TensorProduct.includeRight
      (R := C) (A := S) (B := R)).toRingHom
  let iS := Algebra.TensorProduct.includeLeft
    (R := C) (S := C) (A := S) (B := R)
  let iR := Algebra.TensorProduct.includeRight
    (R := C) (A := S) (B := R)
  let fS : S →ₐ[C] q.ResidueField :=
    (IsScalarTower.toAlgHom C (ConstantTensorRing C R S)
      q.ResidueField).comp iS
  let fp : p.ResidueField →ₐ[C] q.ResidueField :=
    Ideal.ResidueField.mapₐ p q iR rfl
  change Module.finrank C q.ResidueField =
    Nat.lcm (Module.finrank C S)
      (Module.finrank C p.ResidueField)
  apply finiteField_finrank_eq_lcm_of_tensorLift_surjective
    C S p.ResidueField q.ResidueField fS fp
    (fun _ _ => Commute.all _ _)
  simpa only [constantTensorResidueAlgHom, p, iS, iR, fS, fp] using
    (constantTensorResidueAlgHom_surjective C R S q)

end FiniteFields

end

end BGS.HasseWeil
