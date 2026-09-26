/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Envelope.TensorPowHom
public import LeanPool.RegtsSevenster.RS.Novel.Envelope.CycleNormal

/-!
# Splitting a tensor power into two blocks

The tensor power `X ^ ⊗ (p + q)` is isomorphic to
`X ^ ⊗ p ⊗ X ^ ⊗ q` by reassociation alone (`splitPow`), and the
structure carried by a tensor power respects the splitting: a block
sum of permutations acts as the two permutations acting on the two
blocks (`permMor_blockSum`), and the factorwise endomorphism power
splits factorwise (`powHom_splitPow`).  These are the identities
that let the trace of a permutation-and-endomorphism word be
computed block by block.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory

universe v u

variable {A : Type u}

/-! ## The splitting isomorphism -/

/-- **The block splitting**: `X ^ ⊗ (p + q) ≅ X ^ ⊗ p ⊗ X ^ ⊗ q`,
by recursion on the upper block.  At `q = 0` it is the right
unitor's inverse; each further factor is carried across by the
associator, so the isomorphism is built from unitors and
associators alone. -/
noncomputable def splitPow [Category.{v} A] [MonoidalCategory A]
    (X : A) : (p q : ℕ) →
    (tensorPow A X (p + q) ≅ tensorPow A X p ⊗ tensorPow A X q)
  | p, 0 => (ρ_ (tensorPow A X p)).symm
  | p, q + 1 =>
      whiskerRightIso (splitPow X p q) X ≪≫
        α_ (tensorPow A X p) (tensorPow A X q) X

/-- The empty upper block splits off along the right unitor. -/
@[simp]
theorem splitPow_zero [Category.{v} A] [MonoidalCategory A]
    (X : A) (p : ℕ) :
    splitPow (A := A) X p 0 = (ρ_ (tensorPow A X p)).symm := rfl

/-- The recursion equation: one more factor is carried across by
the associator. -/
theorem splitPow_succ [Category.{v} A] [MonoidalCategory A]
    (X : A) (p q : ℕ) :
    splitPow (A := A) X p (q + 1) =
      whiskerRightIso (splitPow X p q) X ≪≫
        α_ (tensorPow A X p) (tensorPow A X q) X := rfl

/-! ## The block sum of two permutations -/

/-- The block sum of two permutations: `σ` acts on the lower `p`
slots and `τ` on the upper `q`, with no interaction between the
blocks. -/
def blockSum {p q : ℕ} (σ : Equiv.Perm (Fin p))
    (τ : Equiv.Perm (Fin q)) : Equiv.Perm (Fin (p + q)) :=
  finSumFinEquiv.permCongr (Equiv.sumCongr σ τ)

/-- The block sum acts on the lower block by `σ`. -/
theorem blockSum_castAdd {p q : ℕ} (σ : Equiv.Perm (Fin p))
    (τ : Equiv.Perm (Fin q)) (i : Fin p) :
    blockSum σ τ (Fin.castAdd q i) = Fin.castAdd q (σ i) := by
  simp [blockSum]

/-- The block sum acts on the upper block by `τ`. -/
theorem blockSum_natAdd {p q : ℕ} (σ : Equiv.Perm (Fin p))
    (τ : Equiv.Perm (Fin q)) (j : Fin q) :
    blockSum σ τ (Fin.natAdd p j) = Fin.natAdd p (τ j) := by
  simp [blockSum]

/-- Against an empty upper block the block sum is `σ` alone. -/
theorem blockSum_of_zero {p : ℕ} (σ : Equiv.Perm (Fin p))
    (τ : Equiv.Perm (Fin 0)) : blockSum σ τ = σ :=
  Equiv.ext fun x =>
    (congrArg (blockSum σ τ)
      (Fin.ext rfl : x = Fin.castAdd 0 x)).trans
      ((blockSum_castAdd σ τ x).trans (Fin.ext rfl))

/-- The block sum sends the top slot within the upper block: its
image is `topImage τ`, shifted past the lower block. -/
theorem topImage_blockSum {p q : ℕ} (σ : Equiv.Perm (Fin p))
    (τ : Equiv.Perm (Fin (q + 1))) :
    topImage (n := p + q) (blockSum (p := p) (q := q + 1) σ τ) =
      Fin.natAdd p (topImage τ) :=
  (congrArg (blockSum (p := p) (q := q + 1) σ τ)
    (Fin.ext rfl : Fin.last (p + q) = Fin.natAdd p (Fin.last q))).trans
    (blockSum_natAdd σ τ (Fin.last q))

/-- Reinsertion above a pivot commutes with the shift into the
upper block. -/
private theorem natAdd_succAbove {p q : ℕ} (a : Fin (q + 1))
    (b : Fin q) :
    Fin.natAdd p (a.succAbove b) =
      (Fin.natAdd p a).succAbove (Fin.natAdd p b) := by
  rcases Fin.lt_or_le b.castSucc a with h | h
  · have h' : (Fin.natAdd p b).castSucc < Fin.natAdd p a := by
      rw [Fin.lt_def] at h ⊢
      simp only [Fin.val_castSucc, Fin.val_natAdd] at h ⊢
      omega
    rw [Fin.succAbove_of_castSucc_lt _ _ h,
      Fin.succAbove_of_castSucc_lt _ _ h']
    exact Fin.ext rfl
  · have h' : Fin.natAdd p a ≤ (Fin.natAdd p b).castSucc := by
      rw [Fin.le_def] at h ⊢
      simp only [Fin.val_castSucc, Fin.val_natAdd] at h ⊢
      omega
    rw [Fin.succAbove_of_le_castSucc _ _ h,
      Fin.succAbove_of_le_castSucc _ _ h']
    exact Fin.ext rfl

/-- **Restriction respects the block sum**: peeling the top slot
off the upper block commutes with summing the blocks. -/
theorem restPerm_blockSum {p q : ℕ} (σ : Equiv.Perm (Fin p))
    (τ : Equiv.Perm (Fin (q + 1))) :
    restPerm (n := p + q) (blockSum (p := p) (q := q + 1) σ τ) =
      blockSum σ (restPerm τ) := by
  refine Equiv.ext fun j => ?_
  refine Fin.succAbove_right_injective
    (p := topImage (n := p + q) (blockSum (p := p) (q := q + 1) σ τ)) ?_
  rw [succAbove_restPerm, topImage_blockSum]
  induction j using Fin.addCases with
  | left i =>
    have h' : (Fin.castAdd q (σ i)).castSucc <
        Fin.natAdd p (topImage τ) := by
      rw [Fin.lt_def]
      simp only [Fin.val_castSucc, Fin.val_castAdd, Fin.val_natAdd]
      have := (σ i).isLt
      omega
    rw [blockSum_castAdd,
      show (Fin.castAdd q i).castSucc = Fin.castAdd (q + 1) i from
        Fin.ext rfl,
      blockSum_castAdd, Fin.succAbove_of_castSucc_lt _ _ h']
    exact Fin.ext rfl
  | right j' =>
    rw [blockSum_natAdd,
      show (Fin.natAdd p j').castSucc = Fin.natAdd p j'.castSucc from
        Fin.ext rfl,
      blockSum_natAdd, ← succAbove_restPerm τ j']
    exact natAdd_succAbove _ _

/-! ## The braiding respects the splitting -/

/-- Braiding the last two factors over a general base. -/
private noncomputable def swapBase [Category.{v} A] [MonoidalCategory A]
    (T X : A) [SymmetricCategory A] :
    (T ⊗ X) ⊗ X ⟶ (T ⊗ X) ⊗ X :=
  (α_ T X X).hom ≫ (T ◁ (β_ X X).hom) ≫ (α_ T X X).inv

/-- **The braiding of the last two factors is natural in the base.**
The braiding touches only those two factors, so a morphism of the
base passes through. -/
private theorem swapBase_naturality [Category.{v} A] [MonoidalCategory A]
    {T T' : A} (X : A)
    [SymmetricCategory A] (f : T ⟶ T') :
    ((f ▷ X) ▷ X) ≫ swapBase T' X = swapBase T X ≫ ((f ▷ X) ▷ X) := by
  change ((f ▷ X) ▷ X) ≫
      ((α_ T' X X).hom ≫ (T' ◁ (β_ X X).hom) ≫ (α_ T' X X).inv) =
    ((α_ T X X).hom ≫ (T ◁ (β_ X X).hom) ≫ (α_ T X X).inv) ≫
      ((f ▷ X) ▷ X)
  rw [associator_naturality_left_assoc,
    ← whisker_exchange_assoc, associator_inv_naturality_left]
  simp only [Category.assoc]

/-- **The braiding of the last two factors passes a left factor of
the base.**  Both sides carry the same braiding on the same two
strands; only the bracketing of the base differs. -/
private theorem swapBase_tensor [Category.{v} A] [MonoidalCategory A]
    (P Q X : A) [SymmetricCategory A] :
    swapBase (P ⊗ Q) X ≫ ((α_ P Q X).hom ▷ X) ≫
        (α_ P (Q ⊗ X) X).hom =
      ((α_ P Q X).hom ▷ X) ≫ (α_ P (Q ⊗ X) X).hom ≫
        (P ◁ swapBase Q X) := by
  change swapBase (P ⊗ Q) X ≫ ((α_ P Q X).hom ▷ X) ≫
      (α_ P (Q ⊗ X) X).hom =
    ((α_ P Q X).hom ▷ X) ≫ (α_ P (Q ⊗ X) X).hom ≫
      (P ◁ ((α_ Q X X).hom ≫ (Q ◁ (β_ X X).hom) ≫ (α_ Q X X).inv))
  change ((α_ (P ⊗ Q) X X).hom ≫ ((P ⊗ Q) ◁ (β_ X X).hom) ≫
      (α_ (P ⊗ Q) X X).inv) ≫ ((α_ P Q X).hom ▷ X) ≫
      (α_ P (Q ⊗ X) X).hom = _
  simp only [whiskerLeft_comp, Category.assoc]
  monoidal

/-- **The braiding respects the splitting**: braiding the last two
factors of a tensor power is braiding them inside the upper block. -/
theorem swapTop_comp_splitPow [Category.{v} A] [MonoidalCategory A]
    (X : A) [SymmetricCategory A]
    (p q : ℕ) :
    swapTop X (p + q) ≫ (splitPow X p (q + 1 + 1)).hom =
      (splitPow X p (q + 1 + 1)).hom ≫
        (tensorPow A X p ◁ swapTop X q) := by
  rw [splitPow_succ, splitPow_succ]
  change swapBase (tensorPow A X (p + q)) X ≫
      ((((splitPow X p q).hom ▷ X) ≫
        (α_ (tensorPow A X p) (tensorPow A X q) X).hom) ▷ X) ≫
      (α_ (tensorPow A X p) (tensorPow A X q ⊗ X) X).hom =
    (((((splitPow X p q).hom ▷ X) ≫
        (α_ (tensorPow A X p) (tensorPow A X q) X).hom) ▷ X) ≫
      (α_ (tensorPow A X p) (tensorPow A X q ⊗ X) X).hom) ≫
      (tensorPow A X p ◁ swapBase (tensorPow A X q) X)
  rw [comp_whiskerRight]
  simp only [Category.assoc]
  rw [← Category.assoc (swapBase (tensorPow A X (p + q)) X),
    ← swapBase_naturality X (splitPow X p q).hom]
  simp only [Category.assoc]
  rw [swapBase_tensor]

/-! ## Transferring a splitting to one more factor -/

/-- **One more factor**: a morphism that respects the splitting
whiskered by one further factor still respects it.  This is the
inductive step every splitting statement below is proved by. -/
private theorem whiskerRight_comp_splitPow [Category.{v} A] [MonoidalCategory A]
    (X : A) (p q : ℕ)
    {u : tensorPow A X (p + q) ⟶ tensorPow A X (p + q)}
    {v : tensorPow A X q ⟶ tensorPow A X q}
    (h : u ≫ (splitPow X p q).hom =
      (splitPow X p q).hom ≫ (tensorPow A X p ◁ v)) :
    (u ▷ X) ≫ (splitPow X p (q + 1)).hom =
      (splitPow X p (q + 1)).hom ≫
        (tensorPow A X p ◁ (v ▷ X)) := by
  rw [splitPow_succ]
  change (u ▷ X) ≫ (((splitPow X p q).hom ▷ X) ≫
      (α_ (tensorPow A X p) (tensorPow A X q) X).hom) =
    ((((splitPow X p q).hom ▷ X) ≫
      (α_ (tensorPow A X p) (tensorPow A X q) X).hom)) ≫
      (tensorPow A X p ◁ (v ▷ X))
  rw [← Category.assoc, ← comp_whiskerRight, h, comp_whiskerRight,
    Category.assoc, Category.assoc,
    whisker_assoc (tensorPow A X p) v X]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-! ## Bubbling respects the splitting -/

/-- **Bubbling respects the splitting**: bubbling the top factor
down at most `q` slots never reaches the lower block, so it is
bubbling inside the upper block. -/
theorem insertTop_comp_splitPow [Category.{v} A] [MonoidalCategory A]
    (X : A) [SymmetricCategory A]
    (p : ℕ) :
    ∀ (k q : ℕ), k ≤ q →
      insertTop X (p + q) k ≫ (splitPow X p (q + 1)).hom =
        (splitPow X p (q + 1)).hom ≫
          (tensorPow A X p ◁ insertTop X q k)
  | 0, q, _ => by
      rw [insertTop_zero, insertTop_zero,
        MonoidalCategory.whiskerLeft_id, Category.id_comp,
        Category.comp_id]
  | k + 1, q, hk => by
      obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
      have hkr : k ≤ r := by omega
      have hL : insertTop X (p + (r + 1)) (k + 1) =
          swapTop X (p + r) ≫ (insertTop X (p + r) k ▷ X) :=
        insertTop_succ X (p + r) k
      have hR : tensorPow A X p ◁ insertTop X (r + 1) (k + 1) =
          (tensorPow A X p ◁ swapTop X r) ≫
            (tensorPow A X p ◁ (insertTop X r k ▷ X)) := by
        rw [insertTop_succ]
        exact MonoidalCategory.whiskerLeft_comp _ _ _
      have hstep := whiskerRight_comp_splitPow X p (r + 1)
        (insertTop_comp_splitPow X p k r hkr)
      rw [hL, hR]
      erw [Category.assoc, hstep, ← Category.assoc,
        swapTop_comp_splitPow X p r, Category.assoc]
      rfl

/-! ## Tensor powers respect the splitting -/

/-- **One more factor, in tensor form**: a morphism that respects
the splitting, tensored with a morphism of the new factor, still
respects it. -/
private theorem tensorHom_comp_splitPow [Category.{v} A] [MonoidalCategory A]
    (X : A) (p q : ℕ)
    {u : tensorPow A X (p + q) ⟶ tensorPow A X (p + q)}
    {a : tensorPow A X p ⟶ tensorPow A X p}
    {b : tensorPow A X q ⟶ tensorPow A X q} {c : X ⟶ X}
    (h : u ≫ (splitPow X p q).hom =
      (splitPow X p q).hom ≫ (a ⊗ₘ b)) :
    (u ⊗ₘ c) ≫ (splitPow X p (q + 1)).hom =
      (splitPow X p (q + 1)).hom ≫ (a ⊗ₘ (b ⊗ₘ c)) := by
  rw [splitPow_succ]
  change (u ⊗ₘ c) ≫ (((splitPow X p q).hom ▷ X) ≫
      (α_ (tensorPow A X p) (tensorPow A X q) X).hom) =
    ((((splitPow X p q).hom ▷ X) ≫
      (α_ (tensorPow A X p) (tensorPow A X q) X).hom)) ≫
      (a ⊗ₘ (b ⊗ₘ c))
  have hst : (u ⊗ₘ c) ≫ ((splitPow X p q).hom ▷ X) =
      ((splitPow X p q).hom ▷ X) ≫ ((a ⊗ₘ b) ⊗ₘ c) := by
    rw [← tensorHom_id (splitPow X p q).hom X,
      tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, h,
      Category.comp_id, Category.id_comp]
  calc (u ⊗ₘ c) ≫ (((splitPow X p q).hom ▷ X) ≫
          (α_ (tensorPow A X p) (tensorPow A X q) X).hom)
      = ((u ⊗ₘ c) ≫ ((splitPow X p q).hom ▷ X)) ≫
          (α_ (tensorPow A X p) (tensorPow A X q) X).hom :=
        (Category.assoc _ _ _).symm
    _ = (((splitPow X p q).hom ▷ X) ≫ ((a ⊗ₘ b) ⊗ₘ c)) ≫
          (α_ (tensorPow A X p) (tensorPow A X q) X).hom :=
        congrArg (· ≫ (α_ (tensorPow A X p) (tensorPow A X q) X).hom)
          hst
    _ = ((splitPow X p q).hom ▷ X) ≫ (((a ⊗ₘ b) ⊗ₘ c) ≫
          (α_ (tensorPow A X p) (tensorPow A X q) X).hom) :=
        Category.assoc _ _ _
    _ = ((splitPow X p q).hom ▷ X) ≫
          ((α_ (tensorPow A X p) (tensorPow A X q) X).hom ≫
            (a ⊗ₘ (b ⊗ₘ c))) :=
        congrArg (fun z => ((splitPow X p q).hom ▷ X) ≫ z)
          (associator_naturality a b c)
    _ = (((splitPow X p q).hom ▷ X) ≫
          (α_ (tensorPow A X p) (tensorPow A X q) X).hom) ≫
          (a ⊗ₘ (b ⊗ₘ c)) := (Category.assoc _ _ _).symm

/-- **The tensor power of an endomorphism respects the splitting.**
-/
theorem powHom_comp_splitPow [Category.{v} A] [MonoidalCategory A]
    (X : A) (g : End X) (p : ℕ) :
    ∀ q : ℕ,
      powHom X g (p + q) ≫ (splitPow X p q).hom =
        (splitPow X p q).hom ≫ (powHom X g p ⊗ₘ powHom X g q)
  | 0 => by
      rw [splitPow_zero]
      change powHom X g p ≫ (ρ_ (tensorPow A X p)).inv =
        (ρ_ (tensorPow A X p)).inv ≫ (powHom X g p ⊗ₘ 𝟙 (𝟙_ A))
      rw [tensorHom_id, rightUnitor_inv_naturality]
  | q + 1 => by
      have h := tensorHom_comp_splitPow X p q (c := g)
        (powHom_comp_splitPow X g p q)
      exact h

/-! ## The action respects the splitting -/

/-- **The action respects the splitting**: a block sum of
permutations acts as the two permutations acting on the two
blocks. -/
theorem permMor_comp_splitPow [Category.{v} A] [MonoidalCategory A]
    (X : A) [SymmetricCategory A] {p : ℕ}
    (σ : Equiv.Perm (Fin p)) :
    ∀ (q : ℕ) (τ : Equiv.Perm (Fin q)),
      permMor X (p + q) (blockSum σ τ) ≫ (splitPow X p q).hom =
        (splitPow X p q).hom ≫ (permMor X p σ ⊗ₘ permMor X q τ)
  | 0, τ => by
      rw [blockSum_of_zero, splitPow_zero]
      change permMor X p σ ≫ (ρ_ (tensorPow A X p)).inv =
        (ρ_ (tensorPow A X p)).inv ≫ (permMor X p σ ⊗ₘ 𝟙 (𝟙_ A))
      rw [tensorHom_id, rightUnitor_inv_naturality]
  | q + 1, τ => by
      have htop : ((topImage τ : ℕ)) ≤ q := Nat.lt_succ_iff.mp
        (topImage τ).isLt
      have hval : ((topImage (n := p + q)
          (blockSum (p := p) (q := q + 1) σ τ) : ℕ)) =
          p + (topImage τ : ℕ) :=
        congrArg Fin.val (topImage_blockSum σ τ)
      have hk : p + q - ((topImage (n := p + q)
          (blockSum (p := p) (q := q + 1) σ τ) : ℕ)) =
          q - (topImage τ : ℕ) := by omega
      have hkq : q - (topImage τ : ℕ) ≤ q := by omega
      have hL : permMor X (p + (q + 1))
          (blockSum (p := p) (q := q + 1) σ τ) =
          (permMor X (p + q) (blockSum σ (restPerm τ)) ▷ X) ≫
            insertTop X (p + q) (q - (topImage τ : ℕ)) := by
        change permMor X (p + q + 1)
            (blockSum (p := p) (q := q + 1) σ τ) = _
        rw [permMor_succ X (p + q)
            (blockSum (p := p) (q := q + 1) σ τ),
          restPerm_blockSum, hk]
      have hR : permMor X (q + 1) τ =
          (permMor X q (restPerm τ) ▷ X) ≫
            insertTop X q (q - (topImage τ : ℕ)) :=
        permMor_succ X q τ
      have hw := tensorHom_comp_splitPow X p q (c := 𝟙 X)
        (permMor_comp_splitPow X σ q (restPerm τ))
      have hi := insertTop_comp_splitPow X p (q - (topImage τ : ℕ)) q
        hkq
      rw [hL, hR]
      erw [Category.assoc, hi, ← Category.assoc,
        ← tensorHom_id (permMor X (p + q) (blockSum σ (restPerm τ))) X, hw]
      erw [Category.assoc,
        ← id_tensorHom (tensorPow A X p) (insertTop X q (q - (topImage τ : ℕ))),
        tensorHom_comp_tensorHom, Category.comp_id, tensorHom_id]
      rfl

end RS
