/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.CorvajaZannier.LaurentFrobeniusBasis
import Mathlib.FieldTheory.LinearDisjoint

/-!
# The completion linear-disjointness bridge

This file isolates the abstract algebraic content of Corvaja--Zannier's
completion argument.  Suppose that `L / F` has a basis
`1, z, ..., z^(q - 1)`, that `L` is embedded in a Laurent-series field, and
that the completed field over `F` has the same carrier as the exponent-
dilation subfield `K((z^q))`.  The residue classes of exponents modulo `q`
then show that the basis remains linearly independent over the completed
field.  Hence the completed field and `L` are linearly disjoint over `F`, and
their intersection in the ambient Laurent-series field is exactly the image
of `F`.

The hypotheses below deliberately expose both compatibility conditions that
must come from curve geometry:

* `hcompletion` identifies the chosen completed field, as a subfield of the
  ambient Laurent-series field, with the exponent-dilation subfield;
* `hbasis` says that the ambient images of the chosen `F`-basis of `L` really
  are `1, z, ..., z^(q - 1)`.

No assertion here constructs a completion map or proves these compatibility
conditions for a plane curve.
-/

open HahnSeries
open Module

noncomputable section

namespace BGS.CorvajaZannier

section AbstractBasisBridge

universe u v w

variable {F : Type u} {L : Type v} {E : Type w}
  [Field F] [Field L] [Field E]
  [Algebra F L] [Algebra F E] [Algebra L E] [IsScalarTower F L E]

/-- A basis of `L / F` which remains linearly independent over an ambient
intermediate field proves linear disjointness and identifies the intersection
with the embedded base field.

This is the abstract linear-algebra boundary used by the Laurent-series
specialization below. -/
theorem linearDisjoint_and_inf_eq_bot_of_basis_ambient_linearIndependent
    (C : IntermediateField F E) {ι : Type*} (b : Basis ι F L)
    (hlinear : LinearIndependent C (fun i => algebraMap L E (b i))) :
    C.LinearDisjoint L ∧
      C ⊓ (IsScalarTower.toAlgHom F L E).fieldRange = ⊥ := by
  have hdisjoint : C.LinearDisjoint L :=
    IntermediateField.LinearDisjoint.of_basis_right' b (by
      change LinearIndependent C (fun i => algebraMap L E (b i))
      exact hlinear)
  have hdisjointRange :
      C.LinearDisjoint (IsScalarTower.toAlgHom F L E).fieldRange := by
    rw [IntermediateField.linearDisjoint_iff', AlgHom.fieldRange_toSubalgebra]
    exact hdisjoint
  exact ⟨hdisjoint, hdisjointRange.inf_eq_bot⟩

end AbstractBasisBridge

section LaurentCompletion

universe u v w

variable {K : Type u} {F : Type v} {L : Type w}
  [Field K] [Field F] [Field L]
  [Algebra F L]
  [Algebra F (LaurentSeries K)]
  [Algebra L (LaurentSeries K)]
  [IsScalarTower F L (LaurentSeries K)]

private def sameCarrierRingEquiv
    (C : IntermediateField F (LaurentSeries K))
    (D : IntermediateField K (LaurentSeries K))
    (hcarrier : ∀ x : LaurentSeries K, x ∈ C ↔ x ∈ D) : C ≃+* D where
  toFun x := ⟨x, (hcarrier x).mp x.property⟩
  invFun x := ⟨x, (hcarrier x).mpr x.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_mul' := fun _ _ => rfl
  map_add' := fun _ _ => rfl

/-- **Completion form of Corvaja--Zannier's Lemma 2.**

Let `C` be the completed exponent-dilation field inside `K((z))`, represented
as an intermediate field over `F`.  If `L / F` has a `Fin q`-indexed basis
whose ambient images are `1, z, ..., z^(q - 1)`, then `C` and `L` are linearly
disjoint over `F`.  Their intersection inside `K((z))` is the bottom
intermediate field, i.e. the image of `F`.

The carrier equality is stated elementwise because `C` and
`laurentExponentSubfield K hq` have different declared base fields even
though they are subfields of the same Laurent-series field. -/
theorem laurentExponentCompletion_linearDisjoint_and_inf_eq_bot
    {q : ℕ} (hq : 0 < q)
    (C : IntermediateField F (LaurentSeries K))
    (hcompletion : ∀ x : LaurentSeries K,
      x ∈ C ↔ x ∈ laurentExponentSubfield K hq)
    (b : Basis (Fin q) F L)
    (hbasis : ∀ i : Fin q,
      algebraMap L (LaurentSeries K) (b i) =
        laurentParameter K ^ (i : ℕ)) :
    C.LinearDisjoint L ∧
      C ⊓ (IsScalarTower.toAlgHom F L (LaurentSeries K)).fieldRange = ⊥ := by
  let D : IntermediateField K (LaurentSeries K) :=
    laurentExponentSubfield K hq
  let e : C ≃+* D := sameCarrierRingEquiv C D hcompletion
  have he_val (c : C) : ((e c : D) : LaurentSeries K) = (c : LaurentSeries K) := rfl
  have hpowersD : LinearIndependent D
      (fun i : Fin q => laurentParameter K ^ (i : ℕ)) := by
    simpa only [D] using linearIndependent_laurentParameter_pow K hq
  have hpowersC : LinearIndependent C
      (fun i : Fin q => laurentParameter K ^ (i : ℕ)) := by
    refine hpowersD.map_of_injective_injective
      (fun c : C => e c) (AddMonoidHom.id (LaurentSeries K)) ?_ ?_ ?_
    · intro c hc
      exact e.injective (by simpa using hc)
    · intro x hx
      exact hx
    · intro c x
      change ((e c : D) : LaurentSeries K) * x = (c : LaurentSeries K) * x
      rw [he_val]
  have hbasisLinear : LinearIndependent C
      (fun i : Fin q => algebraMap L (LaurentSeries K) (b i)) := by
    rw [show (fun i : Fin q => algebraMap L (LaurentSeries K) (b i)) =
        (fun i : Fin q => laurentParameter K ^ (i : ℕ)) from funext hbasis]
    exact hpowersC
  exact linearDisjoint_and_inf_eq_bot_of_basis_ambient_linearIndependent
    C b hbasisLinear

end LaurentCompletion

end BGS.CorvajaZannier
