/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.CycleSplit
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.MixedConc

/-!
# Additive splitting of Schur specialisations

The Schur specialisation of a diagram at a pointwise sum of scalar
sequences splits over pairs of shapes whose sizes add to the size of
the diagram, with induction multiplicities: the normalized pairings
of the recast Jacobi–Trudi character of the diagram, restricted to a
block product of symmetric groups, against the characters of the two
shapes.  The multiplicities are nonnegative integers, being
dimensions of equivariant Hom spaces over the product group.

The route: the Frobenius formula at a sum of sequences, the additive
splitting of the completed cycle product over invariant subsets, a
reindexing of the invariant permutations of a subset of fixed size
by pairs of block permutations, the collapse of the subset sum by
the binomial count, and the character expansion of each block
factor.
-/

@[expose] public section

namespace RS

open Finset Equiv

/-! ### Conjugation invariance of the Jacobi–Trudi character -/

open scoped Classical in
/-- The Jacobi–Trudi character is a class function. -/
theorem jtChar_conj (μ : YoungDiagram) (τ π : Equiv.Perm (Fin μ.card)) :
    jtChar μ (τ * π * τ⁻¹) = jtChar μ π := by
  rw [jtChar, jtChar]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  by_cases hp : ∀ i, 0 ≤ jtSigned μ σ i
  · rw [ite_eq_left hp, ite_eq_left hp, colourChar_conj]
  · rw [ite_eq_right hp, ite_eq_right hp]

/-- **Transport independence of the recast Jacobi–Trudi character**:
relabelling a permutation of an abstract carrier into the symmetric
group of the diagram gives the same character value whichever
equivalence performs the relabelling — two choices differ by an
inner automorphism. -/
theorem jtChar_permCongr_congr (lam : YoungDiagram) {α : Type*}
    (g₁ g₂ : α ≃ Fin lam.card) (π : Equiv.Perm α) :
    jtChar lam (g₁.permCongr π) = jtChar lam (g₂.permCongr π) := by
  have key : g₁.permCongr π =
      (g₁.symm.trans g₂)⁻¹ * g₂.permCongr π * (g₁.symm.trans g₂) := by
    refine Equiv.ext fun x => ?_
    simp [Equiv.Perm.mul_apply, Equiv.Perm.inv_def]
  have h := jtChar_conj lam (g₁.symm.trans g₂)⁻¹ (g₂.permCongr π)
  rw [inv_inv] at h
  rw [key, h]

/-! ### The block embedding as a homomorphism from the product -/

/-- **The block embedding of the product group**: the monoid
homomorphism `S_a × S_b →* S_{a + b}` carrying a pair to its block
embedding, the first factor on the first `a` slots and the second on
the last `b`. -/
noncomputable def blockEmbedHom (a b : ℕ) :
    Equiv.Perm (Fin a) × Equiv.Perm (Fin b) →*
      Equiv.Perm (Fin (a + b)) where
  toFun p := blockEmbed p.1 p.2
  map_one' := blockEmbed_one
  map_mul' p q := blockEmbed_mul p.1 q.1 p.2 q.2

/-- The block embedding carries inverses to inverses. -/
theorem blockEmbed_inv {a b : ℕ} (σ : Equiv.Perm (Fin a))
    (τ : Equiv.Perm (Fin b)) :
    blockEmbed σ⁻¹ τ⁻¹ = (blockEmbed σ τ)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← blockEmbed_mul, inv_mul_cancel, inv_mul_cancel, blockEmbed_one]

private theorem blockEmbed_injective {a b : ℕ}
    {σ σ' : Equiv.Perm (Fin a)} {τ τ' : Equiv.Perm (Fin b)}
    (h : blockEmbed σ τ = blockEmbed σ' τ') : σ = σ' ∧ τ = τ' := by
  constructor
  · refine Equiv.ext fun i => ?_
    have h1 : Fin.castAdd b (σ i) = Fin.castAdd b (σ' i) := by
      rw [← blockEmbed_castAdd σ τ i, h, blockEmbed_castAdd]
    have h2 := congrArg Fin.val h1
    exact Fin.ext h2
  · refine Equiv.ext fun j => ?_
    have h1 : Fin.natAdd a (τ j) = Fin.natAdd a (τ' j) := by
      rw [← blockEmbed_natAdd σ τ j, h, blockEmbed_natAdd]
    have h2 : a + (τ j).val = a + (τ' j).val := congrArg Fin.val h1
    exact Fin.ext (Nat.add_left_cancel h2)

/-! ### Induction multiplicities -/

/-- **The induction multiplicity** of a pair of shapes in a shape of
the joint size: the normalized pairing, over the block product
`S_a × S_b`, of the recast Jacobi–Trudi character of the joint shape
with the recast characters of the two shapes. -/
noncomputable def indMult {a b : ℕ} (lam : Shape (a + b)) (μ : Shape a)
    (ν : Shape b) : ℂ :=
  ((a.factorial : ℂ) * (b.factorial : ℂ))⁻¹ *
    ∑ σ : Equiv.Perm (Fin a), ∑ τ : Equiv.Perm (Fin b),
      jtChar lam.val (permCast lam.prop.symm (blockEmbed σ τ)) *
        jtChar μ.val (permCast μ.prop.symm σ) *
        jtChar ν.val (permCast ν.prop.symm τ)

/-- **Induction multiplicities are nonnegative integers**: the
pairing is the dimension of the space of `S_a × S_b`-equivariant
maps from the restricted joint irreducible to the external tensor
product of the two block irreducibles. -/
theorem indMult_exists_nat {a b : ℕ} (lam : Shape (a + b))
    (μ : Shape a) (ν : Shape b) :
    ∃ m : ℕ, indMult lam μ ν = m := by
  classical
  set ρl : Representation ℂ (Equiv.Perm (Fin a) × Equiv.Perm (Fin b))
      (subCarrier (jtSimple lam.val)) :=
    (rhoS (jtSimple lam.val)).comp
      ((permCastHom lam.prop.symm).comp (blockEmbedHom a b)) with hρl
  set ρμ : Representation ℂ (Equiv.Perm (Fin a) × Equiv.Perm (Fin b))
      (subCarrier (jtSimple μ.val)) :=
    (rhoS (jtSimple μ.val)).comp
      ((permCastHom μ.prop.symm).comp (MonoidHom.fst _ _)) with hρμ
  set ρν : Representation ℂ (Equiv.Perm (Fin a) × Equiv.Perm (Fin b))
      (subCarrier (jtSimple ν.val)) :=
    (rhoS (jtSimple ν.val)).comp
      ((permCastHom ν.prop.symm).comp (MonoidHom.snd _ _)) with hρν
  have hcard0 : ((Nat.card
      (Equiv.Perm (Fin a) × Equiv.Perm (Fin b)) : ℂ)) ≠ 0 := by
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast Fintype.card_ne_zero
  have : Invertible ((Nat.card
      (Equiv.Perm (Fin a) × Equiv.Perm (Fin b)) : ℂ)) :=
    invertibleOfNonzero hcard0
  have h := Representation.card_inv_mul_sum_char_mul_char_eq_finrank
    (W := TensorProduct ℂ (subCarrier (jtSimple μ.val))
      (subCarrier (jtSimple ν.val)))
    ρl (Representation.tprod ρμ ρν)
  refine ⟨Module.finrank ℂ
    (Representation.IntertwiningMap ρl
      (Representation.tprod ρμ ρν)), ?_⟩
  rw [← h, indMult]
  rw [show ((a.factorial : ℂ) * (b.factorial : ℂ))⁻¹ =
      ((Nat.card (Equiv.Perm (Fin a) × Equiv.Perm (Fin b)) : ℂ))⁻¹
      from by
    rw [Nat.card_eq_fintype_card, Fintype.card_prod,
      Fintype.card_perm, Fintype.card_perm, Fintype.card_fin,
      Fintype.card_fin, Nat.cast_mul]]
  congr 1
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun σ _ => ?_
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Representation.char_tensor, Pi.mul_apply]
  rw [show ρμ.character (σ, τ) =
      jtChar μ.val (permCast μ.prop.symm σ) from by
    rw [jtSimple_char μ.val]; rfl]
  rw [show ρν.character (σ, τ) =
      jtChar ν.val (permCast ν.prop.symm τ) from by
    rw [jtSimple_char ν.val]; rfl]
  rw [show ρl.character (σ, τ)⁻¹ =
      jtChar lam.val (permCast lam.prop.symm (blockEmbed σ τ)) from by
    rw [show ρl.character (σ, τ)⁻¹ = nChar (jtSimple lam.val)
        (permCast lam.prop.symm (blockEmbed σ⁻¹ τ⁻¹)) from rfl,
      blockEmbed_inv, permCast_inv, ← jtSimple_char lam.val,
      jtChar_inv]]
  ring

/-! ### Assembling a subset and its complement into a block carrier

A subset of `Fin n` of size `a` with complement of size `b`, once
equivalences of the subset with `Fin a` and of the complement with
`Fin b` are chosen, assembles into an equivalence
`Fin n ≃ Fin (a + b)` carrying the subset onto the first block.
Conjugation along it carries a permutation preserving the subset to
the block embedding of its two restrictions. -/

section Assemble

variable {n a b : ℕ} {s : Finset (Fin n)}

/-- The assembled block equivalence of a subset and its
complement. -/
private noncomputable def assembleE (es : {x // x ∈ s} ≃ Fin a)
    (ec : {x // x ∈ sᶜ} ≃ Fin b) : Fin n ≃ Fin (a + b) :=
  (Equiv.sumCompl (fun x => x ∈ s)).symm.trans
    ((es.sumCongr
      ((Equiv.subtypeEquivRight
        (fun x => Iff.symm (Finset.mem_compl (a := x)))).trans ec)).trans
      finSumFinEquiv)

private theorem assembleE_coe_mem (es : {x // x ∈ s} ≃ Fin a)
    (ec : {x // x ∈ sᶜ} ≃ Fin b) (u : {x // x ∈ s}) :
    assembleE es ec ↑u = Fin.castAdd b (es u) := by
  simp [assembleE]

private theorem assembleE_coe_compl (es : {x // x ∈ s} ≃ Fin a)
    (ec : {x // x ∈ sᶜ} ≃ Fin b) (u : {x // x ∈ sᶜ}) :
    assembleE es ec ↑u = Fin.natAdd a (ec u) := by
  have hu : ¬ (↑u : Fin n) ∈ s := Finset.mem_compl.mp u.2
  have hval : ((Equiv.subtypeEquivRight
      (fun x => Iff.symm (Finset.mem_compl (a := x))))
        ⟨↑u, hu⟩ : {x // x ∈ sᶜ}) = u :=
    Subtype.ext rfl
  simp [assembleE, Equiv.sumCompl_symm_apply_of_neg hu, hval]

private theorem assembleE_symm_castAdd (es : {x // x ∈ s} ≃ Fin a)
    (ec : {x // x ∈ sᶜ} ≃ Fin b) (i : Fin a) :
    (assembleE es ec).symm (Fin.castAdd b i) = ↑(es.symm i) := by
  rw [Equiv.symm_apply_eq, assembleE_coe_mem, Equiv.apply_symm_apply]

private theorem assembleE_symm_natAdd (es : {x // x ∈ s} ≃ Fin a)
    (ec : {x // x ∈ sᶜ} ≃ Fin b) (j : Fin b) :
    (assembleE es ec).symm (Fin.natAdd a j) = ↑(ec.symm j) := by
  rw [Equiv.symm_apply_eq, assembleE_coe_compl, Equiv.apply_symm_apply]

/-- Conjugating an invariant permutation along the assembled block
equivalence gives the block embedding of its two restrictions. -/
private theorem assembleE_permCongr (es : {x // x ∈ s} ≃ Fin a)
    (ec : {x // x ∈ sᶜ} ≃ Fin b) {π : Equiv.Perm (Fin n)}
    (h : ∀ x, π x ∈ s ↔ x ∈ s) (hc : ∀ x, π x ∈ sᶜ ↔ x ∈ sᶜ) :
    (assembleE es ec).permCongr π =
      blockEmbed (es.permCongr (π.subtypePerm h))
        (ec.permCongr (π.subtypePerm hc)) := by
  refine Equiv.ext fun x => ?_
  induction x using Fin.addCases with
  | left i =>
    rw [blockEmbed_castAdd, Equiv.permCongr_apply, assembleE_symm_castAdd,
      show π ↑(es.symm i) = ↑((π.subtypePerm h) (es.symm i)) from rfl,
      assembleE_coe_mem, Equiv.permCongr_apply]
  | right j =>
    rw [blockEmbed_natAdd, Equiv.permCongr_apply, assembleE_symm_natAdd,
      show π ↑(ec.symm j) = ↑((π.subtypePerm hc) (ec.symm j)) from rfl,
      assembleE_coe_compl, Equiv.permCongr_apply]

/-- The assembled conjugate of a block embedding preserves the
subset. -/
private theorem assembled_invariant (es : {x // x ∈ s} ≃ Fin a)
    (ec : {x // x ∈ sᶜ} ≃ Fin b) (σ : Equiv.Perm (Fin a))
    (τ : Equiv.Perm (Fin b)) :
    ∀ x ∈ s, (assembleE es ec).symm.permCongr (blockEmbed σ τ) x ∈ s := by
  intro x hx
  rw [Equiv.permCongr_apply, Equiv.symm_symm,
    show (assembleE es ec) x = Fin.castAdd b (es ⟨x, hx⟩) from
      assembleE_coe_mem es ec ⟨x, hx⟩,
    blockEmbed_castAdd, assembleE_symm_castAdd]
  exact (es.symm _).2

end Assemble

private theorem permCongr_comp {α β γ : Type*} (e : α ≃ β) (f : β ≃ γ)
    (π : Equiv.Perm α) :
    f.permCongr (e.permCongr π) = (e.trans f).permCongr π := by
  refine Equiv.ext fun x => ?_
  simp

/-! ### The invariant-permutation sum at a fixed subset -/

/-- The sum over permutations preserving a subset of size `a`, of
the recast character of `lam` against the two restricted completed
cycle products, reindexed by pairs of block permutations. -/
private theorem sum_invariant_eq {n a b : ℕ} (lam : YoungDiagram)
    (hL : lam.card = n) (hab : lam.card = a + b) (t t' : ℕ → ℂ)
    (s : Finset (Fin n)) (hs : s.card = a) (hsc : sᶜ.card = b) :
    ∑ π ∈ Finset.univ.filter
        (fun π : Equiv.Perm (Fin n) => ∀ x ∈ s, π x ∈ s),
      jtChar lam (permCast hL.symm π) *
        (cycleFunG t (permRestrict π s) *
          cycleFunG t' (permRestrict π sᶜ)) =
    ∑ σ : Equiv.Perm (Fin a), ∑ τ : Equiv.Perm (Fin b),
      jtChar lam (permCast hab.symm (blockEmbed σ τ)) *
        (cycleFun t σ * cycleFun t' τ) := by
  classical
  have hes : Fintype.card {x // x ∈ s} = a := by
    rw [Fintype.card_coe]; exact hs
  have hec : Fintype.card {x // x ∈ sᶜ} = b := by
    rw [Fintype.card_coe]; exact hsc
  set es : {x // x ∈ s} ≃ Fin a := Fintype.equivFinOfCardEq hes
    with hesdef
  set ec : {x // x ∈ sᶜ} ≃ Fin b := Fintype.equivFinOfCardEq hec
    with hecdef
  refine Eq.trans ?_ (Fintype.sum_prod_type
    (f := fun p : Equiv.Perm (Fin a) × Equiv.Perm (Fin b) =>
      jtChar lam (permCast hab.symm (blockEmbed p.1 p.2)) *
        (cycleFun t p.1 * cycleFun t' p.2)))
  refine Finset.sum_nbij'
    (fun π => (es.permCongr (permRestrict π s),
      ec.permCongr (permRestrict π sᶜ)))
    (fun p => (assembleE es ec).symm.permCongr (blockEmbed p.1 p.2))
    ?_ ?_ ?_ ?_ ?_
  · exact fun π _ => Finset.mem_univ _
  · intro p _
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, assembled_invariant es ec p.1 p.2⟩
  · intro π hπ
    rw [Finset.mem_filter] at hπ
    have hinv := mem_iff_of_invariant hπ.2
    have hinvc := mem_iff_of_invariant (invariant_compl hπ.2)
    rw [permRestrict_of_invariant hinv, permRestrict_of_invariant hinvc,
      ← assembleE_permCongr es ec hinv hinvc]
    exact Equiv.symm_apply_apply
      (Equiv.permCongr (assembleE es ec)) π
  · intro p _
    have hone : ∀ x ∈ s,
        (assembleE es ec).symm.permCongr (blockEmbed p.1 p.2) x ∈ s :=
      assembled_invariant es ec p.1 p.2
    have hinv := mem_iff_of_invariant hone
    have hinvc := mem_iff_of_invariant (invariant_compl hone)
    have hkey : (assembleE es ec).permCongr
        ((assembleE es ec).symm.permCongr (blockEmbed p.1 p.2)) =
        blockEmbed p.1 p.2 :=
      Equiv.apply_symm_apply
        (Equiv.permCongr (assembleE es ec)) (blockEmbed p.1 p.2)
    have heq := (assembleE_permCongr es ec hinv hinvc).symm.trans hkey
    obtain ⟨h1, h2⟩ := blockEmbed_injective heq
    rw [permRestrict_of_invariant hinv, permRestrict_of_invariant hinvc]
    exact Prod.ext h1 h2
  · intro π hπ
    rw [Finset.mem_filter] at hπ
    have hinv := mem_iff_of_invariant hπ.2
    have hinvc := mem_iff_of_invariant (invariant_compl hπ.2)
    dsimp only
    rw [← cycleFunG_fin t, ← cycleFunG_fin t',
      cycleFunG_permCongr es, cycleFunG_permCongr ec,
      permRestrict_of_invariant hinv, permRestrict_of_invariant hinvc,
      ← assembleE_permCongr es ec hinv hinvc]
    congr 1
    rw [show permCast hab.symm ((assembleE es ec).permCongr π) =
        ((assembleE es ec).trans (finCongr hab.symm)).permCongr π from
      permCongr_comp _ _ _]
    rw [show permCast hL.symm π = (finCongr hL.symm).permCongr π from
      rfl]
    exact jtChar_permCongr_congr lam _ _ π

/-! ### Character expansion of the block sums -/

/-- A weighted sum of completed cycle products expands over the
shapes with Schur coefficients. -/
private theorem sum_mul_cycleFun_expand {m : ℕ} (t : ℕ → ℂ)
    (F : Equiv.Perm (Fin m) → ℂ) :
    ∑ σ : Equiv.Perm (Fin m), F σ * cycleFun t σ =
      ∑ μ : Shape m, diagramSchur μ.val t *
        ∑ σ : Equiv.Perm (Fin m),
          F σ * jtChar μ.val (permCast μ.prop.symm σ) := by
  rw [Finset.sum_congr rfl fun σ _ => by
    rw [cycleFun_expand t σ, Finset.mul_sum]]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => by ring

/-- The normalization exchange: dividing the binomial count by the
joint factorial is dividing by the product of the block
factorials. -/
private theorem inv_factorial_choose {n a : ℕ} (h : a ≤ n) :
    ((n.factorial : ℂ))⁻¹ * (n.choose a : ℂ) =
      ((a.factorial : ℂ) * ((n - a).factorial : ℂ))⁻¹ := by
  have hnat : n.choose a * (a.factorial * (n - a).factorial) =
      n.factorial := by
    rw [← mul_assoc]
    exact Nat.choose_mul_factorial_mul_factorial h
  have hcast : (n.choose a : ℂ) *
      ((a.factorial : ℂ) * ((n - a).factorial : ℂ)) =
      (n.factorial : ℂ) := by
    exact_mod_cast congrArg (fun k : ℕ => (k : ℂ)) hnat
  have ha0 : (a.factorial : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero a)
  have hb0 : ((n - a).factorial : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n - a))
  have hn0 : (n.factorial : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  field_simp
  linear_combination hcast

/-- **The block pair sum is the induction-multiplicity expansion**:
normalizing the sum of the recast joint character against the two
completed cycle products and expanding each factor over its shapes
produces the induction multiplicities. -/
private theorem pairSum_expand {a b : ℕ} (lam : YoungDiagram)
    (hab : lam.card = a + b) (t t' : ℕ → ℂ) :
    ((a.factorial : ℂ) * (b.factorial : ℂ))⁻¹ *
      ∑ σ : Equiv.Perm (Fin a), ∑ τ : Equiv.Perm (Fin b),
        jtChar lam (permCast hab.symm (blockEmbed σ τ)) *
          (cycleFun t σ * cycleFun t' τ) =
    ∑ μ : Shape a, ∑ ν : Shape b,
      indMult ⟨lam, hab⟩ μ ν *
        diagramSchur μ.val t * diagramSchur ν.val t' := by
  classical
  -- expand the τ-factor over the shapes of `b`
  rw [Finset.sum_congr rfl fun σ _ => by
    rw [Finset.sum_congr rfl fun τ _ =>
        (mul_assoc (jtChar lam (permCast hab.symm (blockEmbed σ τ)))
          (cycleFun t σ) (cycleFun t' τ)).symm,
      sum_mul_cycleFun_expand t'
        (fun τ => jtChar lam (permCast hab.symm (blockEmbed σ τ)) *
          cycleFun t σ)]]
  -- swap the σ-sum inside the ν-sum
  rw [Finset.sum_comm]
  -- expand the σ-factor over the shapes of `a`
  rw [Finset.sum_congr rfl fun ν _ => by
    rw [Finset.sum_congr rfl fun σ _ => by
      rw [Finset.sum_congr rfl fun τ _ => show
          (jtChar lam (permCast hab.symm (blockEmbed σ τ)) *
              cycleFun t σ) *
            jtChar ν.val (permCast ν.prop.symm τ) =
          (jtChar lam (permCast hab.symm (blockEmbed σ τ)) *
              jtChar ν.val (permCast ν.prop.symm τ)) *
            cycleFun t σ from by ring,
        ← Finset.sum_mul, ← mul_assoc],
      sum_mul_cycleFun_expand t
        (fun σ => diagramSchur ν.val t' *
          ∑ τ : Equiv.Perm (Fin b),
            jtChar lam (permCast hab.symm (blockEmbed σ τ)) *
              jtChar ν.val (permCast ν.prop.symm τ))]]
  -- swap the shape sums of the target to align the binders
  rw [Finset.sum_comm (s := (Finset.univ : Finset (Shape a)))
    (t := (Finset.univ : Finset (Shape b)))
    (f := fun μ ν => indMult ⟨lam, hab⟩ μ ν *
      diagramSchur μ.val t * diagramSchur ν.val t')]
  -- distribute the normalization and identify the multiplicities
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.sum_congr rfl fun σ _ => show
      (diagramSchur ν.val t' *
          ∑ τ : Equiv.Perm (Fin b),
            jtChar lam (permCast hab.symm (blockEmbed σ τ)) *
              jtChar ν.val (permCast ν.prop.symm τ)) *
        jtChar μ.val (permCast μ.prop.symm σ) =
      diagramSchur ν.val t' *
        ∑ τ : Equiv.Perm (Fin b),
          jtChar lam (permCast hab.symm (blockEmbed σ τ)) *
            jtChar μ.val (permCast μ.prop.symm σ) *
            jtChar ν.val (permCast ν.prop.symm τ) from by
    rw [mul_assoc, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun τ _ => by ring]
  rw [← Finset.mul_sum]
  dsimp only [indMult]
  ring

/-! ### The splitting identity -/

/-- Swapping a sum over a filtered inner range: the filter moves to
the other variable through the indicator form. -/
private theorem sum_sum_filter_comm {α β : Type*} [Fintype α]
    [Fintype β] (p : α → β → Prop) [∀ a b, Decidable (p a b)]
    (F : α → β → ℂ) :
    ∑ a : α, ∑ b ∈ Finset.univ.filter (p a), F a b =
      ∑ b : β, ∑ a ∈ Finset.univ.filter (fun a => p a b), F a b := by
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_filter (p a) (F a)]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ =>
    (Finset.sum_filter (fun a => p a b) (fun a => F a b)).symm

/-- The splitting identity in fixed-size form: the diagram sum over
the sizes of the first block, with the block pair sums still
unexpanded. -/
private theorem diagramSchur_add_aux (lam : YoungDiagram)
    (t t' : ℕ → ℂ) :
    diagramSchur lam (fun c => t c + t' c) =
      ∑ a ∈ (Finset.range (lam.card + 1)).attach,
        ((a.1.factorial : ℂ) * ((lam.card - a.1).factorial : ℂ))⁻¹ *
          ∑ σ : Equiv.Perm (Fin a.1),
            ∑ τ : Equiv.Perm (Fin (lam.card - a.1)),
              jtChar lam (permCast (Nat.add_sub_cancel'
                  (Nat.lt_succ_iff.mp (Finset.mem_range.mp a.2)))
                  (blockEmbed σ τ)) *
                (cycleFun t σ * cycleFun t' τ) := by
  classical
  rw [show diagramSchur lam (fun c => t c + t' c) =
      diagramSchur (⟨lam, rfl⟩ : Shape lam.card).val
        (fun c => t c + t' c) from rfl,
    ← jtChar_shape_frobenius (⟨lam, rfl⟩ : Shape lam.card)
      (fun c => t c + t' c)]
  rw [Finset.sum_congr rfl fun π _ => by
    rw [cycleFun_add_split t t' π, Finset.mul_sum]]
  rw [sum_sum_filter_comm
    (fun (π : Equiv.Perm (Fin lam.card)) (s : Finset (Fin lam.card)) =>
      ∀ x ∈ s, π x ∈ s)
    (fun π s => jtChar (⟨lam, rfl⟩ : Shape lam.card).val
        (permCast (⟨lam, rfl⟩ : Shape lam.card).prop.symm π) *
      (cycleFunG t (permRestrict π s) *
        cycleFunG t' (permRestrict π sᶜ)))]
  rw [← Finset.sum_fiberwise_of_maps_to
    (g := Finset.card) (t := Finset.range (lam.card + 1))
    (fun s _ => Finset.mem_range.mpr (Nat.lt_succ_of_le
      (le_trans (Finset.card_le_univ s)
        (le_of_eq (Fintype.card_fin lam.card)))))
    (fun s => ∑ π ∈ Finset.univ.filter
        (fun π : Equiv.Perm (Fin lam.card) => ∀ x ∈ s, π x ∈ s),
      jtChar (⟨lam, rfl⟩ : Shape lam.card).val
          (permCast (⟨lam, rfl⟩ : Shape lam.card).prop.symm π) *
        (cycleFunG t (permRestrict π s) *
          cycleFunG t' (permRestrict π sᶜ)))]
  rw [← Finset.sum_attach (Finset.range (lam.card + 1))
    (fun j => ∑ s ∈ Finset.univ.filter
        (fun s : Finset (Fin lam.card) => s.card = j),
      ∑ π ∈ Finset.univ.filter
          (fun π : Equiv.Perm (Fin lam.card) => ∀ x ∈ s, π x ∈ s),
        jtChar (⟨lam, rfl⟩ : Shape lam.card).val
            (permCast (⟨lam, rfl⟩ : Shape lam.card).prop.symm π) *
          (cycleFunG t (permRestrict π s) *
            cycleFunG t' (permRestrict π sᶜ)))]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hle : a.1 ≤ lam.card :=
    Nat.lt_succ_iff.mp (Finset.mem_range.mp a.2)
  have hab : lam.card = a.1 + (lam.card - a.1) :=
    (Nat.add_sub_cancel' hle).symm
  rw [Finset.sum_congr rfl fun s hs =>
    sum_invariant_eq lam rfl hab t t' s
      (Finset.mem_filter.mp hs).2
      (by rw [Finset.card_compl, Fintype.card_fin,
        (Finset.mem_filter.mp hs).2])]
  rw [Finset.sum_const]
  rw [show (Finset.univ.filter
      (fun s : Finset (Fin lam.card) => s.card = a.1)) =
      Finset.powersetCard a.1 (Finset.univ : Finset (Fin lam.card))
      from by
    rw [Finset.powersetCard_eq_filter, Finset.powerset_univ]]
  rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← mul_assoc, inv_factorial_choose hle]

/-- **The additive splitting of Schur specialisations** — the
character shadow of the `⊕`-splitting: the Schur specialisation of
a diagram at a pointwise sum of scalar sequences is the sum, over
splittings of its size recorded on the antidiagonal and over pairs
of shapes of the two parts, of the induction-multiplicity-weighted
products of the Schur specialisations of the parts.  The
antidiagonal is attached so that each index carries the proof that
its parts sum to the size of the diagram. -/
theorem diagramSchur_add (lam : YoungDiagram) (t t' : ℕ → ℂ) :
    diagramSchur lam (fun c => t c + t' c) =
      ∑ ab ∈ (Finset.antidiagonal lam.card).attach,
        ∑ μ : Shape ab.1.1, ∑ ν : Shape ab.1.2,
          indMult ⟨lam, (Finset.mem_antidiagonal.mp ab.2).symm⟩ μ ν *
            diagramSchur μ.val t * diagramSchur ν.val t' := by
  classical
  rw [diagramSchur_add_aux lam t t']
  rw [Finset.sum_congr rfl fun a _ =>
    pairSum_expand lam
      ((Nat.add_sub_cancel'
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp a.2))).symm) t t']
  refine Finset.sum_nbij'
    (fun a => ⟨(a.1, lam.card - a.1), Finset.mem_antidiagonal.mpr
      (Nat.add_sub_cancel'
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp a.2)))⟩)
    (fun ab => ⟨ab.1.1, Finset.mem_range.mpr (Nat.lt_succ_of_le
      (le_of_add_le_left
        (le_of_eq (Finset.mem_antidiagonal.mp ab.2))))⟩)
    ?_ ?_ ?_ ?_ ?_
  · exact fun a _ => Finset.mem_attach _ _
  · exact fun ab _ => Finset.mem_attach _ _
  · exact fun a _ => Subtype.ext rfl
  · intro ab _
    refine Subtype.ext ?_
    have h := Finset.mem_antidiagonal.mp ab.2
    have h2 : lam.card - ab.1.1 = ab.1.2 := by omega
    exact Prod.ext rfl h2
  · exact fun a _ => rfl

end RS
