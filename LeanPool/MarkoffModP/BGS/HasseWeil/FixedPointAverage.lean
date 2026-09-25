/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.Index
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Fixed-point averaging for finite transitive actions

This file isolates the Burnside-counting identity used in the fixed-field
part of the Hasse--Weil argument.
-/

@[expose] public section

namespace BGS.HasseWeil

open scoped BigOperators

/-- For a nonempty finite transitive `G`-set, the sum over group elements of
the number of fixed points is exactly the order of `G`. -/
theorem sum_card_fixedBy_eq_card_group_of_isPretransitive
    (G X : Type*) [Group G] [Fintype G] [MulAction G X] [Finite X]
    [MulAction.IsPretransitive G X] [Nonempty X] :
    (∑ g : G, Nat.card (MulAction.fixedBy X g)) = Nat.card G := by
  let : Fintype X := Fintype.ofFinite X
  let (g : G) : Fintype (MulAction.fixedBy X g) := Fintype.ofFinite _
  let Ω := MulAction.orbitRel.Quotient G X
  let : Fintype Ω := Fintype.ofFinite Ω
  have hΩ : Fintype.card Ω = 1 :=
    Fintype.card_eq_one_iff_nonempty_unique.mpr
      ((MulAction.pretransitive_iff_unique_quotient_of_nonempty G X).mp inferInstance)
  dsimp only [Ω] at hΩ
  simp_rw [Nat.card_eq_fintype_card]
  rw [MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group, hΩ, one_mul]

/-- A finite family of nonempty transitive `G`-sets contributes `|G|` fixed
points per fiber after summing over all group elements. -/
theorem sum_card_fixedBy_fibers_eq_card_mul_card_group
    {ι G : Type*} [Fintype ι] [Group G] [Fintype G]
    (X : ι → Type*) [∀ i, MulAction G (X i)] [∀ i, Finite (X i)]
    [∀ i, MulAction.IsPretransitive G (X i)] [∀ i, Nonempty (X i)] :
    (∑ g : G, ∑ i : ι, Nat.card (MulAction.fixedBy (X i) g)) =
      Nat.card ι * Nat.card G := by
  classical
  rw [Finset.sum_comm]
  calc
    (∑ i : ι, ∑ g : G, Nat.card (MulAction.fixedBy (X i) g)) =
        ∑ _i : ι, Nat.card G := by
      apply Finset.sum_congr rfl
      intro i _
      exact sum_card_fixedBy_eq_card_group_of_isPretransitive G (X i)
    _ = Nat.card ι * Nat.card G := by simp

/-- If every point stabilizer maps onto a quotient group, then the kernel of
that quotient map still acts transitively.  This is the transitivity input for
the Frobenius-coset form of Burnside averaging. -/
theorem MonoidHom.ker_isPretransitive_of_stabilizer_surjective
    {G C X : Type*} [Group G] [Group C] [MulAction G X]
    [MulAction.IsPretransitive G X]
    (π : G →* C)
    (hstab : ∀ x : X, Function.Surjective
      (π.comp (MulAction.stabilizer G x).subtype)) :
    MulAction.IsPretransitive π.ker X := by
  constructor
  intro x y
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G x y
  obtain ⟨h, hh⟩ := hstab x (π g)
  change π (h : G) = π g at hh
  have hfix : (h : G) • x = x := h.2
  have hinv : ((h : MulAction.stabilizer G x) : G)⁻¹ • x = x := by
    exact (congrArg (fun z : X => (h : G)⁻¹ • z) hfix.symm).trans
      (inv_smul_smul (h : G) x)
  refine ⟨⟨g * (h : G)⁻¹, ?_⟩, ?_⟩
  · change π (g * (h : G)⁻¹) = 1
    rw [map_mul, map_inv, hh]
    exact mul_inv_cancel (π g)
  · change (g * (h : G)⁻¹) • x = y
    simpa only [mul_smul, hinv] using hg

/-- A homomorphism of finite groups is surjective when the source cardinality
is the product of the kernel and target cardinalities. -/
theorem MonoidHom.surjective_of_card_eq_card_ker_mul_card
    {G C : Type*} [Group G] [Group C] [Finite G] [Finite C]
    (π : G →* C)
    (hcard : Nat.card G = Nat.card π.ker * Nat.card C) :
    Function.Surjective π := by
  apply MonoidHom.surjective_of_card_ker_le_div
  rw [hcard, Nat.mul_comm (Nat.card π.ker) (Nat.card C),
    Nat.mul_div_right _ Nat.card_pos]

/-- Incidence pairs between elements in one quotient fiber and their fixed
points can be transposed into stabilizer elements in that fiber. -/
def MonoidHom.sigmaFiberFixedByEquivSigmaStabilizerFiber
    {G C X : Type*} [Group G] [Group C] [MulAction G X]
    (π : G →* C) (c : C) :
    (Σ g : π ⁻¹' ({c} : Set C), MulAction.fixedBy X g.1) ≃
      (Σ x : X,
        (π.comp (MulAction.stabilizer G x).subtype) ⁻¹' ({c} : Set C)) where
  toFun p :=
    ⟨p.2.1, ⟨⟨p.1.1, p.2.2⟩, p.1.2⟩⟩
  invFun p :=
    ⟨⟨p.2.1.1, p.2.2⟩, ⟨p.1, p.2.1.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Stabilizer kernels, summed over points, are the same incidence type as
fixed points of elements in the global kernel. -/
def MonoidHom.sigmaStabilizerKerEquivSigmaKerFixedBy
    {G C X : Type*} [Group G] [Group C] [MulAction G X]
    (π : G →* C) :
    (Σ x : X, (π.comp (MulAction.stabilizer G x).subtype).ker) ≃
      (Σ g : π.ker, MulAction.fixedBy X g) where
  toFun p :=
    ⟨⟨p.2.1.1, p.2.2⟩, ⟨p.1, p.2.1.2⟩⟩
  invFun p :=
    ⟨p.2.1, ⟨⟨p.1.1, p.2.2⟩, p.1.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Coset form of Burnside's lemma.  For a finite transitive `G`-set, if the
restriction of `π : G → C` to every point stabilizer is surjective, then the
sum of fixed-point counts over any fiber of `π` is exactly `|ker π|`.

In Stichtenoth's fixed-field argument, `π` is the constant-field Frobenius
quotient and the fiber is a Frobenius coset. -/
theorem sum_card_fixedBy_quotientFiber_eq_card_ker
    {G C X : Type*} [Group G] [Group C] [Finite G]
    [MulAction G X] [Finite X] [MulAction.IsPretransitive G X]
    [Nonempty X]
    (π : G →* C)
    (hstab : ∀ x : X, Function.Surjective
      (π.comp (MulAction.stabilizer G x).subtype))
    (c : C) :
    letI : Fintype (π ⁻¹' ({c} : Set C)) := Fintype.ofFinite _
    (∑ g : π ⁻¹' ({c} : Set C),
      Nat.card (MulAction.fixedBy X g.1)) = Nat.card π.ker := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let : Fintype X := Fintype.ofFinite X
  let : Fintype (π ⁻¹' ({c} : Set C)) := Fintype.ofFinite _
  let (x : X) : Fintype
      ((π.comp (MulAction.stabilizer G x).subtype) ⁻¹' ({c} : Set C)) :=
    Fintype.ofFinite _
  let : MulAction.IsPretransitive π.ker X :=
    MonoidHom.ker_isPretransitive_of_stabilizer_surjective π hstab
  let (g : π ⁻¹' ({c} : Set C)) :
      Fintype (MulAction.fixedBy X g.1) := Fintype.ofFinite _
  let (g : π.ker) : Fintype (MulAction.fixedBy X g) := Fintype.ofFinite _
  let e₁ :=
    MonoidHom.sigmaFiberFixedByEquivSigmaStabilizerFiber (X := X) π c
  let e₂ :
      (Σ x : X,
        (π.comp (MulAction.stabilizer G x).subtype) ⁻¹' ({c} : Set C)) ≃
        (Σ x : X, (π.comp (MulAction.stabilizer G x).subtype).ker) :=
    Equiv.sigmaCongrRight fun x : X =>
      MonoidHom.fiberEquivKerOfSurjective
        (f := π.comp (MulAction.stabilizer G x).subtype) (hstab x) c
  let e₃ := MonoidHom.sigmaStabilizerKerEquivSigmaKerFixedBy (X := X) π
  calc
    (∑ g : π ⁻¹' ({c} : Set C),
        Nat.card (MulAction.fixedBy X g.1)) =
        Fintype.card (Σ g : π ⁻¹' ({c} : Set C),
          MulAction.fixedBy X g.1) := by
      simp_rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
    _ = Fintype.card (Σ g : π.ker, MulAction.fixedBy X g) := by
      exact Fintype.card_congr (e₁.trans (e₂.trans e₃))
    _ = ∑ g : π.ker, Nat.card (MulAction.fixedBy X g) := by
      simp_rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
    _ = Nat.card π.ker :=
      sum_card_fixedBy_eq_card_group_of_isPretransitive π.ker X

/-- Finite-family form of Frobenius-coset Burnside averaging.  If the
constant-quotient map is surjective on every stabilizer in every transitive
fiber, then summing the fixed-point counts first over the quotient fiber and
then over the family contributes one copy of `|ker π|` per family member.

For a function-field cover, the family is the finite set of rational base
places and `X i` is the corresponding restriction fiber of top places. -/
theorem sum_card_fixedBy_quotientFiber_fibers_eq_card_mul_card_ker
    {ι G C : Type*} [Fintype ι] [Group G] [Group C]
    [Finite G]
    (X : ι → Type*) [∀ i, MulAction G (X i)] [∀ i, Finite (X i)]
    [∀ i, MulAction.IsPretransitive G (X i)] [∀ i, Nonempty (X i)]
    (π : G →* C)
    (hstab : ∀ i (x : X i), Function.Surjective
      (π.comp (MulAction.stabilizer G x).subtype))
    (c : C) :
    letI : Fintype (π ⁻¹' ({c} : Set C)) := Fintype.ofFinite _
    (∑ g : π ⁻¹' ({c} : Set C),
        ∑ i : ι, Nat.card (MulAction.fixedBy (X i) g.1)) =
      Nat.card ι * Nat.card π.ker := by
  classical
  let : Fintype (π ⁻¹' ({c} : Set C)) := Fintype.ofFinite _
  rw [Finset.sum_comm]
  calc
    (∑ i : ι, ∑ g : π ⁻¹' ({c} : Set C),
        Nat.card (MulAction.fixedBy (X i) g.1)) =
        ∑ _i : ι, Nat.card π.ker := by
      apply Finset.sum_congr rfl
      intro i _
      exact sum_card_fixedBy_quotientFiber_eq_card_ker
        π (hstab i) c
    _ = Nat.card ι * Nat.card π.ker := by simp

/-- A group action restricted to a fiber of an invariant map. -/
@[implicit_reducible]
def invariantFiberMulAction
    {G X ι : Type*} [Group G] [MulAction G X]
    (base : X → ι) (hbase : ∀ (g : G) (x : X), base (g • x) = base x)
    (i : ι) : MulAction G {x : X // base x = i} where
  smul g x := ⟨g • x.1, (hbase g x.1).trans x.2⟩
  one_smul x := by
    apply Subtype.ext
    exact one_smul G x.1
  mul_smul g h x := by
    apply Subtype.ext
    exact mul_smul g h x.1

/-- Fixed points of an invariant global type are the disjoint union of the
fixed points in its fibers.  This is the nonduplicating assembly used when a
top place is indexed by its restricted base place. -/
def fixedByEquivSigmaInvariantFiberFixedBy
    {G X ι : Type*} [Group G] [MulAction G X]
    (base : X → ι) (hbase : ∀ (g : G) (x : X), base (g • x) = base x)
    (g : G) :
    MulAction.fixedBy X g ≃
      Σ i : ι,
        @MulAction.fixedBy G {x : X // base x = i}
          _ (invariantFiberMulAction base hbase i) g where
  toFun x :=
    ⟨base x.1, ⟨⟨x.1, rfl⟩, by
      apply Subtype.ext
      exact x.2⟩⟩
  invFun x := ⟨x.2.1.1, congrArg Subtype.val x.2.2⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv x := by
    rcases x with ⟨i, ⟨⟨x, hxi⟩, hxg⟩⟩
    subst i
    rfl

/-- Cardinal form of the invariant-fiber fixed-point decomposition. -/
theorem natCard_fixedBy_eq_sum_natCard_invariantFiberFixedBy
    {G X ι : Type*} [Group G] [MulAction G X]
    [Finite X] [Fintype ι]
    (base : X → ι) (hbase : ∀ (g : G) (x : X), base (g • x) = base x)
    (g : G) :
    Nat.card (MulAction.fixedBy X g) =
      ∑ i : ι,
        Nat.card
          (@MulAction.fixedBy G {x : X // base x = i}
            _ (invariantFiberMulAction base hbase i) g) := by
  rw [Nat.card_congr
    (fixedByEquivSigmaInvariantFiberFixedBy base hbase g), Nat.card_sigma]

/-- Cardinality form of the Frobenius-coset Burnside lemma.  It replaces
stabilizer-surjectivity by the exact decomposition-group order identity used
in the function-field argument. -/
theorem sum_card_fixedBy_quotientFiber_eq_card_ker_of_stabilizer_card
    {G C X : Type*} [Group G] [Group C] [Finite G] [Finite C]
    [MulAction G X] [Finite X] [MulAction.IsPretransitive G X]
    [Nonempty X]
    (π : G →* C)
    (hcard : ∀ x : X,
      Nat.card (MulAction.stabilizer G x) =
        Nat.card (π.comp (MulAction.stabilizer G x).subtype).ker * Nat.card C)
    (c : C) :
    letI : Fintype (π ⁻¹' ({c} : Set C)) := Fintype.ofFinite _
    (∑ g : π ⁻¹' ({c} : Set C),
      Nat.card (MulAction.fixedBy X g.1)) = Nat.card π.ker := by
  apply sum_card_fixedBy_quotientFiber_eq_card_ker π (fun x => ?_) c
  exact MonoidHom.surjective_of_card_eq_card_ker_mul_card
    (π.comp (MulAction.stabilizer G x).subtype) (hcard x)

end BGS.HasseWeil
