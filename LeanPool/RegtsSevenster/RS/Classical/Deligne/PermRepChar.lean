/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.CharSplit
import LeanPool.RegtsSevenster.RS.Classical.Deligne.SuperSeries
import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.SignedTensor

/-!
# One-sided super specialisations are multiplicities

The Schur specialisations at the one-sided super power sums
`superPS p 0` and `superPS 0 q` are multiplicities of the recast
Jacobi–Trudi irreducibles in genuine representations of `S_n`,
hence natural numbers.  The symmetric group permutes the
colourings `Fin n → Fin p` — the basis of the `n`-th tensor power
of `ℂ^p` — and the character of the resulting permutation
representation is the completed cycle product of `superPS p 0`:
the colourings fixed by a permutation are the colourings constant
on its orbits.  Twisting by the sign character produces the
completed cycle product of `superPS 0 q`.  Pairing either
character against a recast Jacobi–Trudi character identifies the
Schur specialisation as the dimension of an equivariant Hom
space.
-/

namespace RS

open Finset Equiv MonoidAlgebra



/-! ### The colour space and its permutation action -/

/-- The colour space: all colourings of `n` sites in `p` colours,
the basis of the `n`-th tensor power of `ℂ^p`. -/
def colourSpace (n p : ℕ) : Type := Fin n → Fin p

/-- The colour space is finite. -/
instance colourSpace.fintype (n p : ℕ) : Fintype (colourSpace n p) :=
  inferInstanceAs (Fintype (Fin n → Fin p))

/-- And its members can be compared. -/
noncomputable instance colourSpace.decidableEq (n p : ℕ) :
    DecidableEq (colourSpace n p) :=
  Classical.decEq _

/-- The symmetric group acts on the colour space by precomposition
with the inverse permutation. -/
instance colourSpace.mulAction {n p : ℕ} :
    MulAction (Equiv.Perm (Fin n)) (colourSpace n p) where
  smul π g := g ∘ ⇑π⁻¹
  one_smul g := by
    funext i
    rfl
  mul_smul π ρ g := by
    change g ∘ ⇑(π * ρ)⁻¹ = (g ∘ ⇑ρ⁻¹) ∘ ⇑π⁻¹
    rw [mul_inv_rev]
    rfl

/-- The permutation representation of `S_n` on the free vector
space over the colour space: the `n`-th tensor power of the
defining `p`-dimensional permutation representation. -/
noncomputable def permRep (p n : ℕ) :
    Representation ℂ (Equiv.Perm (Fin n)) ℂ[colourSpace n p] :=
  Representation.ofMulAction ℂ _ _

private theorem fixed_iff_comp_eq {n p : ℕ} (π : Equiv.Perm (Fin n))
    (g : colourSpace n p) :
    π • g = g ↔ g ∘ ⇑π = g := by
  constructor
  · intro h
    funext i
    have := congrFun h (π i)
    change g (π⁻¹ (π i)) = g (π i) at this
    simp at this
    exact this.symm
  · intro h
    funext i
    change g (π⁻¹ i) = g i
    have := congrFun h (π⁻¹ i)
    change g (π (π⁻¹ i)) = g (π⁻¹ i) at this
    simp at this
    exact this.symm

/-! ### The character of the permutation representation -/

private theorem char_permRep_count (p n : ℕ)
    (π : Equiv.Perm (Fin n)) :
    (permRep p n).character π =
      ((Finset.univ.filter
        (fun g : colourSpace n p => π • g = g)).card : ℂ) := by
  change LinearMap.trace ℂ _ ((permRep p n) π) = _
  set b := MonoidAlgebra.basis (colourSpace n p) ℂ with hb_def
  rw [LinearMap.trace_eq_matrix_trace ℂ b]
  change ∑ g : colourSpace n p,
    LinearMap.toMatrix b b ((permRep p n) π) g g = _
  have hdiag : ∀ g : colourSpace n p,
      LinearMap.toMatrix b b ((permRep p n) π) g g =
        if π • g = g then 1 else 0 := by
    intro g
    rw [LinearMap.toMatrix_apply]
    change (b.repr ((permRep p n) π (MonoidAlgebra.single g 1))) g =
      if π • g = g then 1 else 0
    rw [show (permRep p n) π (MonoidAlgebra.single g 1) =
      MonoidAlgebra.single (π • g) 1 from
      Representation.ofMulAction_single π g 1]
    change ((coeffLinearEquiv ℂ)
      (MonoidAlgebra.single (π • g) (1 : ℂ))) g =
        if π • g = g then 1 else 0
    rw [coeffLinearEquiv_apply]
    simp [ Finsupp.single_apply, eq_comm]
  rw [Finset.sum_congr rfl (fun g _ => hdiag g)]
  rw [← Finset.sum_filter]
  simp

open scoped Classical in
private theorem fixedPoints_card (p n : ℕ) (π : Equiv.Perm (Fin n)) :
    (Finset.univ.filter
      (fun g : colourSpace n p => π • g = g)).card =
      p ^ (Multiset.card π.cycleType + (n - π.cycleType.sum)) := by
  have h1 : (Finset.univ.filter
      (fun g : colourSpace n p => π • g = g)).card =
      Fintype.card {g : colourSpace n p // π • g = g} :=
    (Fintype.card_subtype _).symm
  have e : {g : colourSpace n p // π • g = g} ≃
      {f : Fin n → Fin p // f ∘ ⇑π = f} :=
    { toFun := fun g => ⟨g.1, (fixed_iff_comp_eq π g.1).mp g.2⟩
      invFun := fun f => ⟨f.1, (fixed_iff_comp_eq π f.1).mpr f.2⟩
      left_inv := fun g => rfl
      right_inv := fun f => rfl }
  have h2 : Fintype.card {g : colourSpace n p // π • g = g} =
      Fintype.card {f : Fin n → Fin p // f ∘ ⇑π = f} :=
    Fintype.card_congr e
  have h3 : Fintype.card {f : Fin n → Fin p // f ∘ ⇑π = f} =
      Fintype.card (OrbitSpace π → Fin p) :=
    Fintype.card_congr (fixedFunEquiv π (Fin p))
  have h4 : Fintype.card (OrbitSpace π → Fin p) =
      p ^ Fintype.card (OrbitSpace π) := by
    rw [Fintype.card_fun, Fintype.card_fin]
  rw [h1, h2, h3, h4, card_orbitSpace]

/-- The completed cycle product of the one-sided super power sums
`superPS p 0` is `p` raised to the number of orbits. -/
theorem cycleFun_superPS_h {n : ℕ} (p : ℕ)
    (π : Equiv.Perm (Fin n)) :
    cycleFun (superPS p 0) π =
      (p : ℂ) ^ (Multiset.card π.cycleType +
        (n - π.cycleType.sum)) := by
  rw [show superPS p 0 = fun _ => (p : ℂ) from by
    funext c; simp [superPS]]
  rw [cycleFun_eq_cycleProd, cycleProd_const]

/-- **The character of the colour-space permutation
representation** is the completed cycle product of the one-sided
super power sums `superPS p 0`. -/
theorem char_permRep (p n : ℕ) (π : Equiv.Perm (Fin n)) :
    (permRep p n).character π = cycleFun (superPS p 0) π := by
  rw [char_permRep_count p n π, fixedPoints_card p n π,
    cycleFun_superPS_h p π, Nat.cast_pow]

/-! ### The sign twist -/

/-- The sign representation of the symmetric group on `ℂ`. -/
noncomputable def signRep (n : ℕ) :
    Representation ℂ (Equiv.Perm (Fin n)) ℂ where
  toFun π := ((Equiv.Perm.sign π : ℤ) : ℂ) • LinearMap.id
  map_one' := by simp [Module.End.one_eq_id]
  map_mul' π ρ := by
    refine LinearMap.ext fun z => ?_
    change ((Equiv.Perm.sign (π * ρ) : ℤ) : ℂ) • z =
      ((Equiv.Perm.sign π : ℤ) : ℂ) •
        (((Equiv.Perm.sign ρ : ℤ) : ℂ) • z)
    rw [map_mul]
    push_cast
    rw [mul_smul]

/-- The character of the sign representation is the sign. -/
theorem char_signRep (n : ℕ) (π : Equiv.Perm (Fin n)) :
    (signRep n).character π = ((Equiv.Perm.sign π : ℤ) : ℂ) := by
  change LinearMap.trace ℂ ℂ
    (((Equiv.Perm.sign π : ℤ) : ℂ) • LinearMap.id) = _
  rw [map_smul, LinearMap.trace_id]
  simp

/-- The sign twist of the colour-space permutation representation:
the tensor product with the sign character. -/
noncomputable def signPermRep (q n : ℕ) :
    Representation ℂ (Equiv.Perm (Fin n))
      (TensorProduct ℂ ℂ ℂ[colourSpace n q]) :=
  Representation.tprod (signRep n) (permRep q n)

private theorem prod_map_sign_pow (m : Multiset ℕ) :
    (m.map fun c => (-1 : ℂ) ^ (c + 1)).prod =
      (-1 : ℂ) ^ (m.sum + Multiset.card m) := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
      rw [Multiset.map_cons, Multiset.prod_cons, ih,
        Multiset.sum_cons, Multiset.card_cons, ← pow_add,
        show a + 1 + (m.sum + Multiset.card m) =
          a + m.sum + (Multiset.card m + 1) from by omega]

/-- The completed cycle product of the one-sided super power sums
`superPS 0 q` is the sign times `q` raised to the number of
orbits. -/
theorem cycleFun_superPS_e {n : ℕ} (q : ℕ)
    (π : Equiv.Perm (Fin n)) :
    cycleFun (superPS 0 q) π =
      ((Equiv.Perm.sign π : ℤ) : ℂ) *
        (q : ℂ) ^ (Multiset.card π.cycleType +
          (n - π.cycleType.sum)) := by
  rw [show superPS 0 q =
      fun c => ((fun c => (-1 : ℂ) ^ (c + 1)) c) *
        ((fun _ => (q : ℂ)) c) from by
    funext c
    change superPS 0 q c = (-1 : ℂ) ^ (c + 1) * (q : ℂ)
    simp [superPS]]
  rw [cycleFun_mul]
  rw [show cycleFun (fun _ => (q : ℂ)) π =
      (q : ℂ) ^ (Multiset.card π.cycleType +
        (n - π.cycleType.sum)) from by
    rw [cycleFun_eq_cycleProd, cycleProd_const]]
  rw [show cycleFun (fun c => (-1 : ℂ) ^ (c + 1)) π =
      ((Equiv.Perm.sign π : ℤ) : ℂ) from by
    rw [cycleFun, prod_map_sign_pow, sign_cast_complex]
    norm_num]

/-- **The character of the sign-twisted permutation
representation** is the completed cycle product of the one-sided
super power sums `superPS 0 q`. -/
theorem char_signPermRep (q n : ℕ) (π : Equiv.Perm (Fin n)) :
    (signPermRep q n).character π = cycleFun (superPS 0 q) π := by
  have h : (signPermRep q n).character π =
      (signRep n).character π * (permRep q n).character π := by
    change (Representation.tprod (signRep n)
      (permRep q n)).character π = _
    rw [Representation.char_tensor]
    rfl
  rw [h, char_signRep, char_permRep, cycleFun_superPS_h,
    cycleFun_superPS_e]

/-! ### The multiplicity conclusions

Pairing either character against a recast Jacobi–Trudi character
identifies the Schur specialisation at the one-sided super power
sums as the dimension of an equivariant Hom space. -/

/-- **Schur specialisations at `superPS p 0` are multiplicities**:
the value is the dimension of an equivariant Hom space, a natural
number. -/
theorem diagramSchur_superPS_h_exists_nat {n : ℕ} (p : ℕ)
    (μ : Shape n) :
    ∃ m : ℕ, diagramSchur μ.val (superPS p 0) = m := by
  classical
  set ρμ : Representation ℂ (Equiv.Perm (Fin n))
      (subCarrier (jtSimple μ.val)) :=
    (rhoS (jtSimple μ.val)).comp (permCastHom μ.prop.symm) with hρμ
  have hcard0 : ((Nat.card (Equiv.Perm (Fin n)) : ℂ)) ≠ 0 := by
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast Fintype.card_ne_zero
  have : Invertible ((Nat.card (Equiv.Perm (Fin n)) : ℂ)) :=
    invertibleOfNonzero hcard0
  have h := Representation.card_inv_mul_sum_char_mul_char_eq_finrank
    ρμ (permRep p n)
  refine ⟨Module.finrank ℂ
    (Representation.IntertwiningMap ρμ (permRep p n)), ?_⟩
  rw [← h, ← jtChar_shape_frobenius μ (superPS p 0)]
  rw [show ((Nat.card (Equiv.Perm (Fin n)) : ℂ))⁻¹ =
      ((n.factorial : ℂ))⁻¹ from by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm,
      Fintype.card_fin]]
  congr 1
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [char_permRep p n π]
  rw [show ρμ.character π⁻¹ =
    jtChar μ.val (permCast μ.prop.symm π) from by
      rw [show ρμ.character π⁻¹ =
        nChar (jtSimple μ.val) (permCast μ.prop.symm π⁻¹) from rfl,
        permCast_inv, ← jtSimple_char μ.val, jtChar_inv]]
  ring

/-- **Schur specialisations at `superPS 0 q` are multiplicities**:
the value is the dimension of an equivariant Hom space, a natural
number. -/
theorem diagramSchur_superPS_e_exists_nat {n : ℕ} (q : ℕ)
    (μ : Shape n) :
    ∃ m : ℕ, diagramSchur μ.val (superPS 0 q) = m := by
  classical
  set ρμ : Representation ℂ (Equiv.Perm (Fin n))
      (subCarrier (jtSimple μ.val)) :=
    (rhoS (jtSimple μ.val)).comp (permCastHom μ.prop.symm) with hρμ
  have hcard0 : ((Nat.card (Equiv.Perm (Fin n)) : ℂ)) ≠ 0 := by
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast Fintype.card_ne_zero
  have : Invertible ((Nat.card (Equiv.Perm (Fin n)) : ℂ)) :=
    invertibleOfNonzero hcard0
  have h := Representation.card_inv_mul_sum_char_mul_char_eq_finrank
    ρμ (signPermRep q n)
  refine ⟨Module.finrank ℂ
    (Representation.IntertwiningMap ρμ (signPermRep q n)), ?_⟩
  rw [← h, ← jtChar_shape_frobenius μ (superPS 0 q)]
  rw [show ((Nat.card (Equiv.Perm (Fin n)) : ℂ))⁻¹ =
      ((n.factorial : ℂ))⁻¹ from by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm,
      Fintype.card_fin]]
  congr 1
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [char_signPermRep q n π]
  rw [show ρμ.character π⁻¹ =
    jtChar μ.val (permCast μ.prop.symm π) from by
      rw [show ρμ.character π⁻¹ =
        nChar (jtSimple μ.val) (permCast μ.prop.symm π⁻¹) from rfl,
        permCast_inv, ← jtSimple_char μ.val, jtChar_inv]]
  ring

end RS
