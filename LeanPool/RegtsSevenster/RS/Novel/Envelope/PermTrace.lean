/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Envelope.TensorPowSplit
public import LeanPool.RegtsSevenster.RS.Novel.Envelope.CycleTrace

/-!
# The trace of a permutation against a tensor power

The trace of `Φ(π) ∘ g ^ ⊗ n` for an arbitrary permutation `π`: it
is the product of `tr (g ^ c)` over the full cycle type of `π`,
fixed points included.

The three ingredients are conjugation invariance, multiplicativity
over a block sum, and the value on a single cycle.  Every
permutation is conjugate to a block sum of rotations whose block
lengths are its full cycle type (`exists_conj_blockCycles`), so the
three combine to give the general formula.
-/

@[expose] public section

namespace RS

open CategoryTheory CategoryTheory.MonoidalCategory

universe v u

variable {A : Type u}

/-! ## Conjugation invariance -/

/-- **The trace is a class function.**  Conjugating the permutation
leaves the trace unchanged: the action is functorial and commutes
with the tensor power, so the conjugating factors travel around the
loop and cancel. -/
theorem catTrace_permMor_conj
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [RigidCategory A]
    (X : A) (g : End X) (n : ℕ)
    (ρ π : Equiv.Perm (Fin n)) :
    catTrace (permMor X n (ρ * π * ρ⁻¹) ≫ powHom X g n) =
      catTrace (permMor X n π ≫ powHom X g n) := by
  have hsplit : permMor X n (ρ * π * ρ⁻¹) =
      permMor X n ρ⁻¹ ≫ permMor X n π ≫ permMor X n ρ := by
    rw [permMor_mul, permMor_mul]
  have hcancel : permMor X n ρ ≫ permMor X n ρ⁻¹ =
      𝟙 (tensorPow A X n) := by
    rw [← permMor_mul, inv_mul_cancel, permMor_one]
  calc catTrace (permMor X n (ρ * π * ρ⁻¹) ≫ powHom X g n)
      = catTrace (permMor X n ρ⁻¹ ≫
          (permMor X n π ≫ powHom X g n ≫ permMor X n ρ)) := by
        rw [hsplit, Category.assoc, Category.assoc,
          permMor_comp_powHom]
    _ = catTrace ((permMor X n π ≫ powHom X g n ≫ permMor X n ρ) ≫
          permMor X n ρ⁻¹) :=
        catTrace_comp_comm _ _
    _ = catTrace (permMor X n π ≫ powHom X g n) := by
        rw [Category.assoc, Category.assoc, hcancel, Category.comp_id]

/-! ## Multiplicativity over a block sum -/

/-- **The trace is multiplicative over a block sum.**  A block sum
of permutations acts blockwise on the splitting of the tensor power,
as does the tensor power of the endomorphism, so the loop factors
into the two blocks' loops. -/
theorem catTrace_permMor_blockSum
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [RigidCategory A]
    (X : A) (g : End X) {p q : ℕ}
    (σ : Equiv.Perm (Fin p)) (τ : Equiv.Perm (Fin q)) :
    catTrace (permMor X (p + q) (blockSum σ τ) ≫
        powHom X g (p + q)) =
      catTrace (permMor X p σ ≫ powHom X g p) *
        catTrace (permMor X q τ ≫ powHom X g q) := by
  have hu : (permMor X (p + q) (blockSum σ τ) ≫
        powHom X g (p + q)) ≫ (splitPow X p q).hom =
      (splitPow X p q).hom ≫
        ((permMor X p σ ≫ powHom X g p) ⊗ₘ
          (permMor X q τ ≫ powHom X g q)) := by
    calc (permMor X (p + q) (blockSum σ τ) ≫
            powHom X g (p + q)) ≫ (splitPow X p q).hom
        = permMor X (p + q) (blockSum σ τ) ≫
            (powHom X g (p + q) ≫ (splitPow X p q).hom) :=
          Category.assoc _ _ _
      _ = permMor X (p + q) (blockSum σ τ) ≫
            ((splitPow X p q).hom ≫
              (powHom X g p ⊗ₘ powHom X g q)) :=
          congrArg (fun z => permMor X (p + q) (blockSum σ τ) ≫ z)
            (powHom_comp_splitPow X g p q)
      _ = (permMor X (p + q) (blockSum σ τ) ≫
            (splitPow X p q).hom) ≫
            (powHom X g p ⊗ₘ powHom X g q) :=
          (Category.assoc _ _ _).symm
      _ = ((splitPow X p q).hom ≫
            (permMor X p σ ⊗ₘ permMor X q τ)) ≫
            (powHom X g p ⊗ₘ powHom X g q) :=
          congrArg (fun z => z ≫ (powHom X g p ⊗ₘ powHom X g q))
            (permMor_comp_splitPow X σ q τ)
      _ = (splitPow X p q).hom ≫
            ((permMor X p σ ⊗ₘ permMor X q τ) ≫
              (powHom X g p ⊗ₘ powHom X g q)) :=
          Category.assoc _ _ _
      _ = (splitPow X p q).hom ≫
            ((permMor X p σ ≫ powHom X g p) ⊗ₘ
              (permMor X q τ ≫ powHom X g q)) :=
          congrArg (fun z => (splitPow X p q).hom ≫ z)
            (tensorHom_comp_tensorHom _ _ _ _)
  calc catTrace (permMor X (p + q) (blockSum σ τ) ≫
          powHom X g (p + q))
      = catTrace (((permMor X (p + q) (blockSum σ τ) ≫
          powHom X g (p + q)) ≫ (splitPow X p q).hom) ≫
          (splitPow X p q).inv) := by
        rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    _ = catTrace ((splitPow X p q).inv ≫
          ((permMor X (p + q) (blockSum σ τ) ≫
            powHom X g (p + q)) ≫ (splitPow X p q).hom)) :=
        catTrace_comp_comm _ _
    _ = catTrace ((splitPow X p q).inv ≫ ((splitPow X p q).hom ≫
          ((permMor X p σ ≫ powHom X g p) ⊗ₘ
            (permMor X q τ ≫ powHom X g q)))) :=
        congrArg (fun z => catTrace ((splitPow X p q).inv ≫ z)) hu
    _ = catTrace ((permMor X p σ ≫ powHom X g p) ⊗ₘ
          (permMor X q τ ≫ powHom X g q)) := by
        rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    _ = catTrace (permMor X p σ ≫ powHom X g p) *
          catTrace (permMor X q τ ≫ powHom X g q) :=
        catTrace_tensorHom _ _

/-! ## A single cycle -/

/-- **The trace of a full rotation**: the rotation of `m + 1` slots
against the tensor power of `g` traces to `tr (g ^ (m + 1))`. -/
theorem catTrace_permMor_finRotate
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [RigidCategory A]
    (X : A) (g : End X) (m : ℕ) :
    catTrace (permMor X (m + 1) (finRotate (m + 1)) ≫
        powHom X g (m + 1)) = catTrace (g ^ (m + 1)) := by
  rw [← topCycle_zero, permMor_topCycle,
    show ((0 : Fin (m + 1)) : ℕ) = 0 from rfl, Nat.sub_zero,
    catTrace_insertTop X g (le_refl m), Nat.sub_self, pow_zero,
    one_mul]

/-! ## A block sum of rotations -/

/-- **The trace of a block sum of rotations** is the product of the
cycle traces of its block lengths. -/
theorem catTrace_blockCycles
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [RigidCategory A]
    (X : A) (g : End X) :
    ∀ l : List ℕ, (∀ c ∈ l, 1 ≤ c) →
      catTrace (permMor X l.sum (blockCycles l) ≫
          powHom X g l.sum) =
        (l.map (fun c => catTrace (g ^ c))).prod
  | [], _ => by
      change catTrace (permMor X 0 1 ≫ powHom X g 0) = 1
      rw [permMor_one, powHom_zero]
      erw [Category.id_comp]
      exact (catTrace_id _).trans catDim_unit
  | c :: rest, hmem => by
      obtain ⟨m, rfl⟩ : ∃ m, c = m + 1 :=
        ⟨c - 1, by have := hmem c (by simp); omega⟩
      have hrest : ∀ d ∈ rest, 1 ≤ d := fun d hd =>
        hmem d (by simp [hd])
      change catTrace (permMor X ((m + 1) + rest.sum)
          (blockSum (finRotate (m + 1)) (blockCycles rest)) ≫
          powHom X g ((m + 1) + rest.sum)) = _
      rw [catTrace_permMor_blockSum, catTrace_permMor_finRotate,
        catTrace_blockCycles X g rest hrest, List.map_cons,
        List.prod_cons]

/-! ## An arbitrary permutation -/

/-- **The trace of a permutation against a tensor power.**  It is
the product of `tr (g ^ c)` over the full cycle type of the
permutation, fixed points contributing `tr g`.  Every permutation is
conjugate to the block sum of rotations along its full cycle type,
and the trace is a class function. -/
theorem catTrace_permMor_powHom
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [RigidCategory A]
    (X : A) (g : End X) {n : ℕ}
    (π : Equiv.Perm (Fin n)) :
    catTrace (permMor X n π ≫ powHom X g n) =
      ((fullCycleType π).map (fun c => catTrace (g ^ c))).prod := by
  obtain ⟨l, hsum, ρ, hmem, hcoe, hconj⟩ := exists_conj_blockCycles π
  subst hsum
  have hfin : (finCongr (rfl : l.sum = l.sum)).permCongr
      (blockCycles l) = blockCycles l := by
    simp [show (Equiv.refl (Fin l.sum)) =
      (1 : Equiv.Perm (Fin l.sum)) from rfl]
  rw [← hcoe, ← hconj, hfin, catTrace_permMor_conj,
    catTrace_blockCycles X g l hmem]
  simp

end RS
