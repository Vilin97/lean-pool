/-
Copyright (c) 2026 David Muñoz-Lahoz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Muñoz-Lahoz
-/

module

public import LeanPool.OrderClosures.BanLat.Disjoint
public import LeanPool.OrderClosures.BanLat.LLexpr
public import LeanPool.OrderClosures.BanLat.Normed
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Geometry.Convex.Cone.Pointed
public import Mathlib.Order.Sublattice
public import Mathlib.Order.SupClosed


/-!
# Sublattices of vector lattices

A **vector sublattice** of a vector lattice is a linear subspace closed under the lattice
operations. Since all lattice operations are expressible in terms of each other, it suffices
that the subspace be closed under any one operation — for example, `⊔` or `|·|`. The key
characterisation proved here is that closure under absolute value is equivalent to the
sublattice property. The file also constructs generated sublattices, describes
them in terms of sup- and inf-closures, and records the induced normed vector
lattice structure on closed sublattices.
-/

@[expose] public section

variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]

/-! ### Sup- and inf-closure of a pointed cone

In a vector lattice, the sup-closure and inf-closure of a pointed cone
`C ⊆ X` are again pointed cones. -/

namespace PointedCone

omit [VectorLattice X] in
/-- If `s` is closed under addition, so is its sup-closure. -/
theorem add_mem_supClosure_of_addClosed {s : Set X}
    (hadd : ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → a + b ∈ s)
    {x y : X} (hx : x ∈ _root_.supClosure s) (hy : y ∈ _root_.supClosure s) :
    x + y ∈ _root_.supClosure s := by
  have step : ∀ a ∈ s, ∀ b ∈ _root_.supClosure s, a + b ∈ _root_.supClosure s := by
    intro a ha b hb
    have h_sc : SupClosed {c : X | a + c ∈ _root_.supClosure s} := fun u hu v hv => by
      change a + (u ⊔ v) ∈ _root_.supClosure s
      rw [add_sup]; exact supClosed_supClosure hu hv
    have hsub : s ⊆ {c : X | a + c ∈ _root_.supClosure s} :=
      fun c hc => subset_supClosure (hadd ha hc)
    exact supClosure_min hsub h_sc hb
  have h_sc : SupClosed {c : X | c + y ∈ _root_.supClosure s} := fun u hu v hv => by
    change (u ⊔ v) + y ∈ _root_.supClosure s
    rw [sup_add]; exact supClosed_supClosure hu hv
  have hsub : s ⊆ {c : X | c + y ∈ _root_.supClosure s} :=
    fun c hc => step c hc y hy
  exact supClosure_min hsub h_sc hx

/-- If `s` is closed under non-negative scaling, so is its sup-closure. -/
theorem smul_mem_supClosure_of_smulClosed {s : Set X}
    (hsmul : ∀ ⦃a : ℝ⦄, 0 ≤ a → ∀ ⦃x⦄, x ∈ s → a • x ∈ s)
    {a : ℝ} (ha : 0 ≤ a) {x : X} (hx : x ∈ _root_.supClosure s) :
    a • x ∈ _root_.supClosure s := by
  have h_sc : SupClosed {c : X | a • c ∈ _root_.supClosure s} := fun u hu v hv => by
    change a • (u ⊔ v) ∈ _root_.supClosure s
    rw [nonneg_smul_sup u v a ha]; exact supClosed_supClosure hu hv
  have hsub : s ⊆ {c : X | a • c ∈ _root_.supClosure s} :=
    fun c hc => subset_supClosure (hsmul ha hc)
  exact supClosure_min hsub h_sc hx

omit [VectorLattice X] in
/-- If `s` is closed under addition, so is its inf-closure. -/
theorem add_mem_infClosure_of_addClosed {s : Set X}
    (hadd : ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → a + b ∈ s)
    {x y : X} (hx : x ∈ _root_.infClosure s) (hy : y ∈ _root_.infClosure s) :
    x + y ∈ _root_.infClosure s := by
  have step : ∀ a ∈ s, ∀ b ∈ _root_.infClosure s, a + b ∈ _root_.infClosure s := by
    intro a ha b hb
    have h_ic : InfClosed {c : X | a + c ∈ _root_.infClosure s} := fun u hu v hv => by
      change a + (u ⊓ v) ∈ _root_.infClosure s
      rw [add_inf]; exact infClosed_infClosure hu hv
    have hsub : s ⊆ {c : X | a + c ∈ _root_.infClosure s} :=
      fun c hc => subset_infClosure (hadd ha hc)
    exact infClosure_min hsub h_ic hb
  have h_ic : InfClosed {c : X | c + y ∈ _root_.infClosure s} := fun u hu v hv => by
    change (u ⊓ v) + y ∈ _root_.infClosure s
    rw [inf_add]; exact infClosed_infClosure hu hv
  have hsub : s ⊆ {c : X | c + y ∈ _root_.infClosure s} :=
    fun c hc => step c hc y hy
  exact infClosure_min hsub h_ic hx

/-- If `s` is closed under non-negative scaling, so is its inf-closure. -/
theorem smul_mem_infClosure_of_smulClosed {s : Set X}
    (hsmul : ∀ ⦃a : ℝ⦄, 0 ≤ a → ∀ ⦃x⦄, x ∈ s → a • x ∈ s)
    {a : ℝ} (ha : 0 ≤ a) {x : X} (hx : x ∈ _root_.infClosure s) :
    a • x ∈ _root_.infClosure s := by
  have h_ic : InfClosed {c : X | a • c ∈ _root_.infClosure s} := fun u hu v hv => by
    change a • (u ⊓ v) ∈ _root_.infClosure s
    rw [nonneg_smul_inf u v a ha]; exact infClosed_infClosure hu hv
  have hsub : s ⊆ {c : X | a • c ∈ _root_.infClosure s} :=
    fun c hc => subset_infClosure (hsmul ha hc)
  exact infClosure_min hsub h_ic hx

/-- The sup-closure of a pointed cone is a pointed cone. -/
def supClosure (C : PointedCone ℝ X) : PointedCone ℝ X where
  carrier := _root_.supClosure (C : Set X)
  zero_mem' := subset_supClosure C.zero_mem
  add_mem' hx hy := add_mem_supClosure_of_addClosed (fun _ hx _ hy => C.add_mem hx hy) hx hy
  smul_mem' c _ hx :=
    smul_mem_supClosure_of_smulClosed (fun _ ha _ hx => C.smul_mem ha hx) c.2 hx

@[simp]
theorem coe_supClosure (C : PointedCone ℝ X) :
    (supClosure C : Set X) = _root_.supClosure (C : Set X) := rfl

/-- The inf-closure of a pointed cone is a pointed cone. -/
def infClosure (C : PointedCone ℝ X) : PointedCone ℝ X where
  carrier := _root_.infClosure (C : Set X)
  zero_mem' := subset_infClosure C.zero_mem
  add_mem' hx hy := add_mem_infClosure_of_addClosed (fun _ hx _ hy => C.add_mem hx hy) hx hy
  smul_mem' c _ hx :=
    smul_mem_infClosure_of_smulClosed (fun _ ha _ hx => C.smul_mem ha hx) c.2 hx

@[simp]
theorem coe_infClosure (C : PointedCone ℝ X) :
    (infClosure C : Set X) = _root_.infClosure (C : Set X) := rfl

end PointedCone

/-- A `VectorSublattice` of a vector lattice `X` is a linear subspace closed under
`⊔`. This is the bundled version: it extends `Submodule ℝ X` with lattice closure. -/
structure VectorSublattice (X : Type*) [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] extends Submodule ℝ X where
  sup_mem' : ∀ {x y : X}, x ∈ carrier → y ∈ carrier → x ⊔ y ∈ carrier

namespace VectorSublattice

instance : SetLike (VectorSublattice X) X where
  coe Y := Y.carrier
  coe_injective p q h := by
    cases p; cases q; congr
    exact SetLike.ext' h

variable (Y : VectorSublattice X)

/-- A vector sublattice is closed under `⊔`. -/
theorem sup_mem {x y : X} (hx : x ∈ Y) (hy : y ∈ Y) :
    x ⊔ y ∈ Y :=
  Y.sup_mem' hx hy

/-- A vector sublattice is closed under `⊓`. -/
theorem inf_mem {x y : X} (hx : x ∈ Y) (hy : y ∈ Y) :
    x ⊓ y ∈ Y := by
  rw [inf_eq_sub_posPart x y]
  exact Y.toSubmodule.sub_mem hx (Y.sup_mem' (Y.toSubmodule.sub_mem hx hy) (Y.toSubmodule.zero_mem))

/-- A vector sublattice is closed under the positive part. -/
theorem posPart_mem {x : X} (hx : x ∈ Y) : x⁺ ∈ Y :=
  Y.sup_mem' hx (Y.toSubmodule.zero_mem)

/-- A vector sublattice is closed under the negative part. -/
theorem negPart_mem {x : X} (hx : x ∈ Y) : x⁻ ∈ Y :=
  posPart_mem Y (Y.toSubmodule.neg_mem hx)

/-- A vector sublattice is closed under absolute value. -/
theorem abs_mem {x : X} (hx : x ∈ Y) : |x| ∈ Y :=
  sup_mem Y hx (Y.toSubmodule.neg_mem hx)

/-- The underlying set of a vector sublattice is an `IsSublattice`. -/
theorem isSublattice : IsSublattice (Y : Set X) where
  supClosed := by intro _ ha _ hb; exact sup_mem Y ha hb
  infClosed := by intro _ ha _ hb; exact inf_mem Y ha hb

/-! ### Construction from absolute-value closure -/

/-- The positive part lies in a submodule closed under absolute value. -/
private theorem posPart_mem_of_absClosed (M : Submodule ℝ X)
    (h : ∀ x : X, x ∈ M → |x| ∈ M) {x : X} (hx : x ∈ M) : x⁺ ∈ M := by
  have key : x + |x| = 2 • x⁺ := add_abs_eq_two_nsmul_posPart x
  have h2 : (2 : ℝ)⁻¹ • (x + |x|) = x⁺ := by
    rw [key, ← Nat.cast_smul_eq_nsmul ℝ 2]; norm_num [smul_smul]
  rw [← h2]
  exact M.smul_mem _ (M.add_mem hx (h x hx))

/-- Build a `VectorSublattice` from a submodule closed under `|·|`. -/
def ofAbsClosed (M : Submodule ℝ X)
    (h : ∀ x : X, x ∈ M → |x| ∈ M) : VectorSublattice X where
  toSubmodule := M
  sup_mem' := fun {x y} hx hy => by
    rw [sup_eq_add_posPart x y]
    exact M.add_mem hx (posPart_mem_of_absClosed M h (M.sub_mem hy hx))

/-- A submodule is a vector sublattice iff it is closed under absolute value. -/
theorem abs_mem_iff_sup_mem (M : Submodule ℝ X) :
    (∀ x : X, x ∈ M → |x| ∈ M) ↔
      ∀ x y : X, x ∈ M → y ∈ M → x ⊔ y ∈ M := by
  constructor
  · intro h x y hx hy
    exact (ofAbsClosed M h).sup_mem' hx hy
  · intro h x hx
    exact h x (-x) hx (M.neg_mem hx)

/-! ### Coercion to submodule -/

/-- The coercion to `Submodule ℝ X` is injective. -/
theorem toSubmodule_injective :
    Function.Injective
      (toSubmodule : VectorSublattice X → Submodule ℝ X) := by
  intro p q h
  cases p; cases q; congr

/-- A vector sublattice and its underlying submodule have the same carrier. -/
@[simp]
theorem coe_toSubmodule : (Y.toSubmodule : Set X) = (Y : Set X) := rfl

/-! ### Coercion to pointed cone

Every vector sublattice, being a linear subspace, is in particular a pointed
convex cone. -/

/-- Every vector sublattice is (canonically) a pointed cone. -/
instance : CoeHead (VectorSublattice X) (PointedCone ℝ X) where
  coe Y :=
    { toAddSubmonoid := Y.toSubmodule.toAddSubmonoid
      smul_mem' := fun c _ hx => Y.toSubmodule.smul_mem c.1 hx }

theorem coe_toPointedCone (Y : VectorSublattice X) :
    ((Y : PointedCone ℝ X) : Set X) = (Y : Set X) := rfl

/-! ### Lattice structure on the underlying subtype

A vector sublattice `Y` inherits a lattice and vector-lattice structure from
the ambient space, with `⊔` and `⊓` computed pointwise. -/

/-- The lattice structure on the underlying subtype of a vector sublattice. -/
noncomputable instance instLatticeSubtype : Lattice ↥Y.toSubmodule :=
  Subtype.lattice (P := fun x => x ∈ Y.toSubmodule)
    (fun _ _ hx hy => Y.sup_mem hx hy) (fun _ _ hx hy => Y.inf_mem hx hy)

/-- The subtype of a vector sublattice is an ordered additive monoid. -/
instance instIsOrderedAddMonoidSubtype :
    IsOrderedAddMonoid ↥Y.toSubmodule where
  add_le_add_left := by
    intro a b (h : a.1 ≤ b.1) c; exact add_le_add_left h c.1
  add_le_add_right := by
    intro a b (h : a.1 ≤ b.1) c; exact add_le_add_right h c.1

/-- Scalar multiplication by non-negative reals is monotone on the subtype of
a vector sublattice. -/
instance instPosSMulMonoSubtype : PosSMulMono ℝ ↥Y.toSubmodule where
  smul_le_smul_of_nonneg_left := by
    intro a ha b₁ b₂ h
    change (a • b₁).1 ≤ (a • b₂).1
    exact smul_le_smul_of_nonneg_left h ha

/-- The subtype of a vector sublattice is itself a vector lattice. -/
instance instVectorLatticeSubtype : VectorLattice ↥Y.toSubmodule := ⟨⟩

/-! ### Lattice structure on `VectorSublattice X`

The collection of vector sublattices of `X` is ordered by inclusion. It
contains the whole space `⊤ = X` and the zero subspace `⊥ = {0}`, and is
closed under arbitrary intersections. -/

instance : PartialOrder (VectorSublattice X) :=
  PartialOrder.lift (fun Y => (Y : Set X)) SetLike.coe_injective

/-- The whole space `X` is a vector sublattice. -/
instance : Top (VectorSublattice X) where
  top :=
    { toSubmodule := ⊤
      sup_mem' := fun _ _ => Submodule.mem_top }

/-- Every element belongs to `⊤`. -/
@[simp]
theorem mem_top {x : X} : x ∈ (⊤ : VectorSublattice X) :=
  Submodule.mem_top

/-- The zero subspace `{0}` is a vector sublattice. -/
instance : Bot (VectorSublattice X) where
  bot :=
    { toSubmodule := ⊥
      sup_mem' := fun {x y} hx hy => by
        have hx' : x = 0 := (Submodule.mem_bot ℝ).mp hx
        have hy' : y = 0 := (Submodule.mem_bot ℝ).mp hy
        rw [hx', hy', sup_idem]; exact Submodule.zero_mem _ }

/-- An element of `⊥` is zero. -/
@[simp]
theorem mem_bot {x : X} : x ∈ (⊥ : VectorSublattice X) ↔ x = 0 :=
  Submodule.mem_bot ℝ

/-- Arbitrary intersections of vector sublattices are vector sublattices. -/
instance : InfSet (VectorSublattice X) where
  sInf S :=
    { toSubmodule := sInf ((·.toSubmodule) '' S)
      sup_mem' := fun {x y} hx hy => by
        have hx' := (Submodule.mem_sInf).mp hx
        have hy' := (Submodule.mem_sInf).mp hy
        refine (Submodule.mem_sInf).mpr ?_
        rintro _ ⟨Y, hY, rfl⟩
        exact Y.sup_mem (hx' _ ⟨Y, hY, rfl⟩) (hy' _ ⟨Y, hY, rfl⟩) }

/-! ### The vector sublattice generated by a set

The vector sublattice generated by a set `s ⊆ X` is by definition the
smallest vector sublattice of `X` containing `s`, obtained as the infimum
of all vector sublattices containing `s`. -/

/-- The vector sublattice generated by a set `s`: the smallest vector
sublattice of `X` containing `s`. -/
def generated (s : Set X) : VectorSublattice X :=
  sInf {Y : VectorSublattice X | s ⊆ Y}

/-- The generating set is contained in the vector sublattice it generates. -/
theorem subset_generated (s : Set X) : s ⊆ (generated s : Set X) := by
  intro x hx
  refine (Submodule.mem_sInf).mpr ?_
  rintro _ ⟨Y, hY, rfl⟩
  exact hY hx

/-- The vector sublattice generated by `s` is contained in every vector
sublattice containing `s`. -/
theorem generated_le {s : Set X} {Y : VectorSublattice X} (h : s ⊆ Y) :
    generated s ≤ Y := by
  intro x hx
  have := (Submodule.mem_sInf).mp hx
  exact this _ ⟨Y, h, rfl⟩

/-- For a submodule `M`, its lattice closure is closed under addition. -/
private lemma latticeClosure_add_mem_of_submodule (M : Submodule ℝ X)
    {x y : X} (hx : x ∈ latticeClosure (M : Set X))
    (hy : y ∈ latticeClosure (M : Set X)) :
    x + y ∈ latticeClosure (M : Set X) := by
  let := AddCommGroup.toDistribLattice X
  refine latticeClosure_sup_inf_induction
    (p := fun a _ => a + y ∈ latticeClosure (M : Set X)) ?_ ?_ ?_ hx
  · intro a ha
    refine latticeClosure_sup_inf_induction
      (p := fun b _ => a + b ∈ latticeClosure (M : Set X)) ?_ ?_ ?_ hy
    · intro b hb; exact subset_latticeClosure (M.add_mem ha hb)
    · intro p _ q _ h₁ h₂
      rw [add_sup]; exact isSublattice_latticeClosure.supClosed h₁ h₂
    · intro p _ q _ h₁ h₂
      rw [add_inf]; exact isSublattice_latticeClosure.infClosed h₁ h₂
  · intro p _ q _ h₁ h₂
    rw [sup_add]; exact isSublattice_latticeClosure.supClosed h₁ h₂
  · intro p _ q _ h₁ h₂
    rw [inf_add]; exact isSublattice_latticeClosure.infClosed h₁ h₂

/-- For a submodule `M`, its lattice closure is closed under scaling. -/
private lemma latticeClosure_smul_mem_of_submodule (M : Submodule ℝ X)
    (c : ℝ) {x : X} (hx : x ∈ latticeClosure (M : Set X)) :
    c • x ∈ latticeClosure (M : Set X) := by
  let := AddCommGroup.toDistribLattice X
  rcases le_or_gt 0 c with hc | hc
  · refine latticeClosure_sup_inf_induction
      (p := fun a _ => c • a ∈ latticeClosure (M : Set X)) ?_ ?_ ?_ hx
    · intro a ha; exact subset_latticeClosure (M.smul_mem c ha)
    · intro p _ q _ h₁ h₂
      rw [nonneg_smul_sup p q c hc]
      exact isSublattice_latticeClosure.supClosed h₁ h₂
    · intro p _ q _ h₁ h₂
      rw [nonneg_smul_inf p q c hc]
      exact isSublattice_latticeClosure.infClosed h₁ h₂
  · have hc' : 0 ≤ -c := by linarith
    refine latticeClosure_sup_inf_induction
      (p := fun a _ => c • a ∈ latticeClosure (M : Set X)) ?_ ?_ ?_ hx
    · intro a ha; exact subset_latticeClosure (M.smul_mem c ha)
    · intro p _ q _ h₁ h₂
      have eq : c • (p ⊔ q) = (c • p) ⊓ (c • q) := by
        rw [show c • (p ⊔ q) = -((-c) • (p ⊔ q)) by rw [neg_smul, neg_neg],
          nonneg_smul_sup p q (-c) hc', neg_sup, neg_smul, neg_neg, neg_smul, neg_neg]
      rw [eq]
      exact isSublattice_latticeClosure.infClosed h₁ h₂
    · intro p _ q _ h₁ h₂
      have eq : c • (p ⊓ q) = (c • p) ⊔ (c • q) := by
        rw [show c • (p ⊓ q) = -((-c) • (p ⊓ q)) by rw [neg_smul, neg_neg],
          nonneg_smul_inf p q (-c) hc', neg_inf, neg_smul, neg_neg, neg_smul, neg_neg]
      rw [eq]
      exact isSublattice_latticeClosure.supClosed h₁ h₂

/-- The vector sublattice whose underlying set is the lattice closure of a
submodule. -/
private def sublatticeOfSubmoduleLatticeClosure (M : Submodule ℝ X) :
    VectorSublattice X where
  toSubmodule :=
    { carrier := latticeClosure (M : Set X)
      zero_mem' := subset_latticeClosure M.zero_mem
      add_mem' := latticeClosure_add_mem_of_submodule M
      smul_mem' := latticeClosure_smul_mem_of_submodule M }
  sup_mem' := fun {_ _} hx hy => by
    let := AddCommGroup.toDistribLattice X
    exact isSublattice_latticeClosure.supClosed hx hy

/-- The vector sublattice generated by a linear subspace `M` coincides with
the sup-closure of the inf-closure of `M`. -/
theorem generated_submodule_eq_supClosure_infClosure (M : Submodule ℝ X) :
    (generated (M : Set X) : Set X) = supClosure (infClosure (M : Set X)) := by
  let := AddCommGroup.toDistribLattice X
  rw [supClosure_infClosure]
  refine Set.Subset.antisymm ?_ ?_
  · have h : (M : Set X) ⊆ (sublatticeOfSubmoduleLatticeClosure M : Set X) :=
      fun _ hx => subset_latticeClosure hx
    exact generated_le h
  · exact latticeClosure_min (subset_generated _)
      (generated (M : Set X)).isSublattice

/-- The vector sublattice generated by a linear subspace `M` coincides with
the inf-closure of the sup-closure of `M`. -/
theorem generated_submodule_eq_infClosure_supClosure (M : Submodule ℝ X) :
    (generated (M : Set X) : Set X) = infClosure (supClosure (M : Set X)) := by
  let := AddCommGroup.toDistribLattice X
  rw [infClosure_supClosure, ← supClosure_infClosure]
  exact generated_submodule_eq_supClosure_infClosure M

open scoped Pointwise in
/-- The difference set `supClosure C - supClosure C` of a pointed cone is a
vector sublattice. -/
private def sublatticeOfConeSupClosureDiff (C : PointedCone ℝ X) :
    VectorSublattice X where
  toSubmodule :=
    { carrier := _root_.supClosure (C : Set X) - _root_.supClosure (C : Set X)
      zero_mem' :=
        ⟨0, subset_supClosure C.zero_mem, 0, subset_supClosure C.zero_mem, sub_self 0⟩
      add_mem' := by
        rintro _ _ ⟨u₁, hu₁, v₁, hv₁, rfl⟩ ⟨u₂, hu₂, v₂, hv₂, rfl⟩
        refine ⟨u₁ + u₂, ?_, v₁ + v₂, ?_, ?_⟩
        · exact PointedCone.add_mem_supClosure_of_addClosed
            (fun _ h _ h' => C.add_mem h h') hu₁ hu₂
        · exact PointedCone.add_mem_supClosure_of_addClosed
            (fun _ h _ h' => C.add_mem h h') hv₁ hv₂
        · change (u₁ + u₂) - (v₁ + v₂) = (u₁ - v₁) + (u₂ - v₂); abel
      smul_mem' := by
        rintro c _ ⟨u, hu, v, hv, rfl⟩
        rcases le_or_gt 0 c with hc | hc
        · refine ⟨c • u, ?_, c • v, ?_, ?_⟩
          · exact PointedCone.smul_mem_supClosure_of_smulClosed
              (fun _ h _ h' => C.smul_mem h h') hc hu
          · exact PointedCone.smul_mem_supClosure_of_smulClosed
              (fun _ h _ h' => C.smul_mem h h') hc hv
          · change c • u - c • v = c • (u - v); rw [smul_sub]
        · have hc' : 0 ≤ -c := by linarith
          refine ⟨(-c) • v, ?_, (-c) • u, ?_, ?_⟩
          · exact PointedCone.smul_mem_supClosure_of_smulClosed
              (fun _ h _ h' => C.smul_mem h h') hc' hv
          · exact PointedCone.smul_mem_supClosure_of_smulClosed
              (fun _ h _ h' => C.smul_mem h h') hc' hu
          · change (-c) • v - (-c) • u = c • (u - v)
            rw [smul_sub, neg_smul, neg_smul]; abel }
  sup_mem' := by
    rintro _ _ ⟨u₁, hu₁, v₁, hv₁, rfl⟩ ⟨u₂, hu₂, v₂, hv₂, rfl⟩
    refine ⟨(u₁ + v₂) ⊔ (u₂ + v₁), ?_, v₁ + v₂, ?_, ?_⟩
    · exact supClosed_supClosure
        (PointedCone.add_mem_supClosure_of_addClosed
          (fun _ h _ h' => C.add_mem h h') hu₁ hv₂)
        (PointedCone.add_mem_supClosure_of_addClosed
          (fun _ h _ h' => C.add_mem h h') hu₂ hv₁)
    · exact PointedCone.add_mem_supClosure_of_addClosed
        (fun _ h _ h' => C.add_mem h h') hv₁ hv₂
    · have h : ((u₁ - v₁) ⊔ (u₂ - v₂)) + (v₁ + v₂) = (u₁ + v₂) ⊔ (u₂ + v₁) := by
        rw [sup_add]; congr 1 <;> abel
      change ((u₁ + v₂) ⊔ (u₂ + v₁)) - (v₁ + v₂) = (u₁ - v₁) ⊔ (u₂ - v₂)
      rw [← h]; abel

open scoped Pointwise in
/-- The vector sublattice generated by a pointed cone `C` coincides with the
difference set of the sup-closure of `C` with itself. -/
theorem generated_pointedCone_eq_sub_supClosure (C : PointedCone ℝ X) :
    (generated (C : Set X) : Set X)
      = supClosure (C : Set X) - supClosure (C : Set X) := by
  refine Set.Subset.antisymm ?_ ?_
  · have h : (C : Set X) ⊆ (sublatticeOfConeSupClosureDiff C : Set X) := fun x hx =>
      ⟨x, subset_supClosure hx, 0, subset_supClosure C.zero_mem, sub_zero x⟩
    exact generated_le h
  · rintro _ ⟨u, hu, v, hv, rfl⟩
    have hC : (C : Set X) ⊆ (generated (C : Set X) : Set X) := subset_generated _
    have h_sup : SupClosed (generated (C : Set X) : Set X) :=
      (generated (C : Set X)).isSublattice.supClosed
    have hu_gen := supClosure_min hC h_sup hu
    have hv_gen := supClosure_min hC h_sup hv
    exact (generated (C : Set X)).toSubmodule.sub_mem hu_gen hv_gen

open scoped Pointwise in
/-- The difference set `infClosure C - infClosure C` of a pointed cone is a
vector sublattice. -/
private def sublatticeOfConeInfClosureDiff (C : PointedCone ℝ X) :
    VectorSublattice X where
  toSubmodule :=
    { carrier := _root_.infClosure (C : Set X) - _root_.infClosure (C : Set X)
      zero_mem' :=
        ⟨0, subset_infClosure C.zero_mem, 0, subset_infClosure C.zero_mem, sub_self 0⟩
      add_mem' := by
        rintro _ _ ⟨u₁, hu₁, v₁, hv₁, rfl⟩ ⟨u₂, hu₂, v₂, hv₂, rfl⟩
        refine ⟨u₁ + u₂, ?_, v₁ + v₂, ?_, ?_⟩
        · exact PointedCone.add_mem_infClosure_of_addClosed
            (fun _ h _ h' => C.add_mem h h') hu₁ hu₂
        · exact PointedCone.add_mem_infClosure_of_addClosed
            (fun _ h _ h' => C.add_mem h h') hv₁ hv₂
        · change (u₁ + u₂) - (v₁ + v₂) = (u₁ - v₁) + (u₂ - v₂); abel
      smul_mem' := by
        rintro c _ ⟨u, hu, v, hv, rfl⟩
        rcases le_or_gt 0 c with hc | hc
        · refine ⟨c • u, ?_, c • v, ?_, ?_⟩
          · exact PointedCone.smul_mem_infClosure_of_smulClosed
              (fun _ h _ h' => C.smul_mem h h') hc hu
          · exact PointedCone.smul_mem_infClosure_of_smulClosed
              (fun _ h _ h' => C.smul_mem h h') hc hv
          · change c • u - c • v = c • (u - v); rw [smul_sub]
        · have hc' : 0 ≤ -c := by linarith
          refine ⟨(-c) • v, ?_, (-c) • u, ?_, ?_⟩
          · exact PointedCone.smul_mem_infClosure_of_smulClosed
              (fun _ h _ h' => C.smul_mem h h') hc' hv
          · exact PointedCone.smul_mem_infClosure_of_smulClosed
              (fun _ h _ h' => C.smul_mem h h') hc' hu
          · change (-c) • v - (-c) • u = c • (u - v)
            rw [smul_sub, neg_smul, neg_smul]; abel }
  sup_mem' := by
    rintro _ _ ⟨u₁, hu₁, v₁, hv₁, rfl⟩ ⟨u₂, hu₂, v₂, hv₂, rfl⟩
    have hadd : ∀ ⦃a⦄, a ∈ (C : Set X) → ∀ ⦃b⦄, b ∈ (C : Set X) → a + b ∈ (C : Set X) :=
      fun _ ha _ hb => C.add_mem ha hb
    have hu₁v₂ : u₁ + v₂ ∈ _root_.infClosure (C : Set X) :=
      PointedCone.add_mem_infClosure_of_addClosed hadd hu₁ hv₂
    have hu₂v₁ : u₂ + v₁ ∈ _root_.infClosure (C : Set X) :=
      PointedCone.add_mem_infClosure_of_addClosed hadd hu₂ hv₁
    have hv₁v₂ : v₁ + v₂ ∈ _root_.infClosure (C : Set X) :=
      PointedCone.add_mem_infClosure_of_addClosed hadd hv₁ hv₂
    have hinf : (u₁ + v₂) ⊓ (u₂ + v₁) ∈ _root_.infClosure (C : Set X) :=
      infClosed_infClosure hu₁v₂ hu₂v₁
    refine ⟨u₁ + u₂ + v₁ + v₂, ?_, (u₁ + v₂) ⊓ (u₂ + v₁) + (v₁ + v₂), ?_, ?_⟩
    · have heq : u₁ + u₂ + v₁ + v₂ = (u₁ + v₂) + (u₂ + v₁) := by abel
      rw [heq]
      exact PointedCone.add_mem_infClosure_of_addClosed hadd hu₁v₂ hu₂v₁
    · exact PointedCone.add_mem_infClosure_of_addClosed hadd hinf hv₁v₂
    · have step1 : (u₁ + v₂) ⊔ (u₂ + v₁) =
          (u₁ + v₂) + (u₂ + v₁) - (u₁ + v₂) ⊓ (u₂ + v₁) := by
        rw [eq_sub_iff_add_eq, add_comm]
        exact inf_add_sup _ _
      have step2 : ((u₁ - v₁) ⊔ (u₂ - v₂)) + (v₁ + v₂) =
          (u₁ + v₂) ⊔ (u₂ + v₁) := by
        rw [sup_add]; congr 1 <;> abel
      change u₁ + u₂ + v₁ + v₂ - ((u₁ + v₂) ⊓ (u₂ + v₁) + (v₁ + v₂))
        = (u₁ - v₁) ⊔ (u₂ - v₂)
      symm
      calc (u₁ - v₁) ⊔ (u₂ - v₂)
          = ((u₁ + v₂) ⊔ (u₂ + v₁)) - (v₁ + v₂) := by rw [← step2]; abel
        _ = ((u₁ + v₂) + (u₂ + v₁) - (u₁ + v₂) ⊓ (u₂ + v₁)) - (v₁ + v₂) := by rw [← step1]
        _ = u₁ + u₂ + v₁ + v₂ - ((u₁ + v₂) ⊓ (u₂ + v₁) + (v₁ + v₂)) := by abel

open scoped Pointwise in
/-- The vector sublattice generated by a pointed cone `C` coincides with the
difference set of the inf-closure of `C` with itself. -/
theorem generated_pointedCone_eq_sub_infClosure (C : PointedCone ℝ X) :
    (generated (C : Set X) : Set X)
      = infClosure (C : Set X) - infClosure (C : Set X) := by
  refine Set.Subset.antisymm ?_ ?_
  · have h : (C : Set X) ⊆ (sublatticeOfConeInfClosureDiff C : Set X) := fun x hx =>
      ⟨x, subset_infClosure hx, 0, subset_infClosure C.zero_mem, sub_zero x⟩
    exact generated_le h
  · rintro _ ⟨u, hu, v, hv, rfl⟩
    have hC : (C : Set X) ⊆ (generated (C : Set X) : Set X) := subset_generated _
    have h_inf : InfClosed (generated (C : Set X) : Set X) :=
      (generated (C : Set X)).isSublattice.infClosed
    have hu_gen := infClosure_min hC h_inf hu
    have hv_gen := infClosure_min hC h_inf hv
    exact (generated (C : Set X)).toSubmodule.sub_mem hu_gen hv_gen

omit [VectorLattice X] in
/-- For a finite set `s` of pairwise lattice-disjoint elements and a family
`g : X → X` taking values disjoint from a fixed `a`, the sum over `s` remains
lattice-disjoint from `a`. -/
private lemma isVLDisjoint_finsetSum {a : X} {s : Finset X} {g : X → X}
    (h : ∀ i ∈ s, IsVLDisjoint a (g i)) :
    IsVLDisjoint a (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isVLDisjoint_zero_right a
  | insert b s hb ih =>
    rw [Finset.sum_insert hb]
    refine (h b (Finset.mem_insert_self b s)).add_right ?_
    exact ih (fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- Disjoint sum of a scalar family: for a Finset `s` of pairwise-disjoint
elements with any scalars `f`, `|∑ f(a) • a| = ∑ |f(a)| • |a|`. -/
private lemma abs_sum_finset_of_pairwise_vlDisjoint {s : Finset X} {f : X → ℝ}
    (hdisj : (s : Set X).Pairwise IsVLDisjoint) :
    |∑ a ∈ s, f a • a| = ∑ a ∈ s, |f a| • |a| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hdisj_s : (s : Set X).Pairwise IsVLDisjoint := fun i hi j hj hij =>
      hdisj (Finset.mem_insert_of_mem hi) (Finset.mem_insert_of_mem hj) hij
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hdisj_head : IsVLDisjoint (f a • a) (∑ i ∈ s, f i • i) := by
      apply isVLDisjoint_finsetSum
      intro i hi
      have hne_ai : a ≠ i := fun h => ha (h ▸ hi)
      exact ((hdisj (Finset.mem_insert_self a s)
        (Finset.mem_insert_of_mem hi) hne_ai).smul_left (f a)).smul_right (f i)
    rw [abs_add_of_isVLDisjoint hdisj_head, abs_smul', ih hdisj_s]

/-- The vector sublattice generated by a set of pairwise lattice-disjoint,
non-negative elements coincides with its linear span. -/
theorem generated_eq_span_of_pairwise_vlDisjoint {A : Set X}
    (hA : A.Pairwise IsVLDisjoint) (hA_nn : ∀ a ∈ A, 0 ≤ a) :
    (generated A).toSubmodule = Submodule.span ℝ A := by
  refine le_antisymm ?_ (Submodule.span_le.mpr (subset_generated A))
  have h_abs : ∀ u, u ∈ Submodule.span ℝ A → |u| ∈ Submodule.span ℝ A := by
    intro u hu
    obtain ⟨f, t, ht_sub, _, hsum⟩ :=
      Submodule.mem_span_iff_exists_finset_subset.mp hu
    have hdisj_t : (t : Set X).Pairwise IsVLDisjoint := fun i hi j hj hij =>
      hA (ht_sub hi) (ht_sub hj) hij
    have hnn_t : ∀ a ∈ t, 0 ≤ a := fun a ha => hA_nn a (ht_sub ha)
    rw [← hsum, abs_sum_finset_of_pairwise_vlDisjoint hdisj_t]
    refine Submodule.sum_mem _ fun a ha => ?_
    rw [abs_of_nonneg (hnn_t a ha)]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (ht_sub ha))
  let Y : VectorSublattice X := ofAbsClosed (Submodule.span ℝ A) h_abs
  have hA_sub : A ⊆ (Y : Set X) := Submodule.subset_span
  have hle := generated_le (Y := Y) hA_sub
  intro x hx
  exact hle hx

end VectorSublattice

namespace LLexpr

variable {n : ℕ}

section Combinations

variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]

/-- The sublattice generated by the image of a tuple `x : Fin n → X` coincides
with the set of lattice-linear combinations of `x`. -/
theorem generated_range_eq_combinations (x : Fin n → X) :
    (VectorSublattice.generated (Set.range x) : Set X)
      = combinations x := by
  let Y : VectorSublattice X :=
    { toSubmodule :=
        { carrier := combinations x
          zero_mem' := ⟨.zero, rfl⟩
          add_mem' := by
            rintro _ _ ⟨e₁, rfl⟩ ⟨e₂, rfl⟩
            exact ⟨.add e₁ e₂, rfl⟩
          smul_mem' := by
            rintro r _ ⟨e, rfl⟩
            exact ⟨.smul r e, rfl⟩ }
      sup_mem' := by
        rintro _ _ ⟨e₁, rfl⟩ ⟨e₂, rfl⟩
        exact ⟨.sup e₁ e₂, rfl⟩ }
  refine Set.Subset.antisymm ?_ ?_
  · change (VectorSublattice.generated (Set.range x) : Set X) ⊆ (Y : Set X)
    exact VectorSublattice.generated_le (Y := Y) (by
      rintro _ ⟨i, rfl⟩
      exact ⟨.var i, rfl⟩)
  · rintro _ ⟨e, rfl⟩
    induction e with
    | zero =>
        exact (VectorSublattice.generated (Set.range x)).toSubmodule.zero_mem
    | var i =>
        exact VectorSublattice.subset_generated (Set.range x) ⟨i, rfl⟩
    | add e₁ e₂ he₁ he₂ =>
        exact (VectorSublattice.generated (Set.range x)).toSubmodule.add_mem he₁ he₂
    | smul r e he =>
        exact (VectorSublattice.generated (Set.range x)).toSubmodule.smul_mem r he
    | sup e₁ e₂ he₁ he₂ =>
        exact (VectorSublattice.generated (Set.range x)).sup_mem he₁ he₂
    | inf e₁ e₂ he₁ he₂ =>
        exact (VectorSublattice.generated (Set.range x)).inf_mem he₁ he₂

/-- The sublattice generated by a set `s` coincides with the union, over all
natural numbers `n` and all `n`-tuples `x` with values in `s`, of the sets of
lattice-linear combinations of `x`. -/
theorem generated_eq_iUnion_combinations (s : Set X) :
    (VectorSublattice.generated s : Set X)
      = ⋃ (n : ℕ) (x : Fin n → s), combinations ((↑) ∘ x) := by
  let U : Set X := ⋃ (n : ℕ) (x : Fin n → s), combinations ((↑) ∘ x)
  let Y : VectorSublattice X :=
    { toSubmodule :=
        { carrier := U
          zero_mem' := by
            refine Set.mem_iUnion.mpr ⟨0, ?_⟩
            refine Set.mem_iUnion.mpr ⟨Fin.elim0, ?_⟩
            exact ⟨.zero, rfl⟩
          add_mem' := by
            rintro _ _ hx hy
            simp only [U, Set.mem_iUnion] at hx hy ⊢
            obtain ⟨m, x, e₁, rfl⟩ := hx
            obtain ⟨k, y, e₂, rfl⟩ := hy
            refine ⟨m + k, Fin.append x y, .add (reindexExpr (Fin.castAdd k) e₁)
              (reindexExpr (Fin.natAdd m) e₂), ?_⟩
            simp [Function.comp_def]
          smul_mem' := by
            rintro r _ hx
            simp only [U, Set.mem_iUnion] at hx ⊢
            obtain ⟨m, x, e, rfl⟩ := hx
            exact ⟨m, x, .smul r e, rfl⟩ }
      sup_mem' := by
        rintro _ _ hx hy
        simp only [U, Set.mem_iUnion] at hx hy ⊢
        obtain ⟨m, x, e₁, rfl⟩ := hx
        obtain ⟨k, y, e₂, rfl⟩ := hy
        refine ⟨m + k, Fin.append x y, .sup (reindexExpr (Fin.castAdd k) e₁)
          (reindexExpr (Fin.natAdd m) e₂), ?_⟩
        simp [Function.comp_def] }
  have hsY : s ⊆ Y := by
    intro a ha
    change a ∈ U
    refine Set.mem_iUnion.mpr ⟨1, ?_⟩
    refine Set.mem_iUnion.mpr ⟨(fun _ : Fin 1 => ⟨a, ha⟩), ?_⟩
    exact ⟨.var 0, rfl⟩
  refine Set.Subset.antisymm ?_ ?_
  · exact VectorSublattice.generated_le hsY
  · intro a ha
    simp only [Set.mem_iUnion] at ha
    obtain ⟨m, x, hx⟩ := ha
    have hxgen :
        a ∈
          (VectorSublattice.generated (Set.range ((Subtype.val : s → X) ∘ x)) : Set X) := by
      rwa [generated_range_eq_combinations ((Subtype.val : s → X) ∘ x)]
    exact VectorSublattice.generated_le (Y := VectorSublattice.generated s) (fun y hy => by
      obtain ⟨i, rfl⟩ := hy
      exact VectorSublattice.subset_generated s (x i).2) hxgen

end Combinations

end LLexpr

/-! ### Normed and Banach lattice structure on sublattices -/

section Normed

variable {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [NormedVectorLattice X]

namespace VectorSublattice

variable (Y : VectorSublattice X)

/-- A vector sublattice of a normed vector lattice is itself a normed vector
lattice under the induced norm and lattice operations. -/
instance instNormedVectorLatticeSubtype :
    NormedVectorLattice ↥Y.toSubmodule where
  solid := by
    intro x y h
    change ‖x.1‖ ≤ ‖y.1‖
    exact HasSolidNorm.solid h
  norm_smul a x := norm_smul a x.1

/-- The closure of a vector sublattice in a normed vector lattice is again a
vector sublattice. -/
noncomputable def topologicalClosure (Y : VectorSublattice X) : VectorSublattice X where
  toSubmodule := Y.toSubmodule.topologicalClosure
  sup_mem' := fun {x y} hx hy => by
    have hx' : x ∈ closure (Y.toSubmodule : Set X) := by
      rw [← Submodule.topologicalClosure_coe]; exact hx
    have hy' : y ∈ closure (Y.toSubmodule : Set X) := by
      rw [← Submodule.topologicalClosure_coe]; exact hy
    have hxy : x ⊔ y ∈ closure (Y.toSubmodule : Set X) :=
      map_mem_closure₂ (f := fun a b : X => a ⊔ b)
        NormedVectorLattice.continuous_sup hx' hy'
        (fun _ ha _ hb => Y.sup_mem ha hb)
    rw [← Submodule.topologicalClosure_coe] at hxy
    exact hxy

/-- A norm-closed vector sublattice of a Banach lattice is itself a Banach
lattice under the induced structures. -/
@[reducible]
noncomputable def banachLatticeSubtype [CompleteSpace X]
    (hclosed : IsClosed (Y : Set X)) : BanachLattice ↥Y.toSubmodule where
  toCompleteSpace := by
    have : IsClosed (Y.toSubmodule : Set X) := hclosed
    infer_instance

omit [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X] [NormedVectorLattice X] in
/-- Finite subsets of a countable set form a countable set of finsets. -/
private lemma countable_finsets_subset {D : Set X} (hD : D.Countable) :
    {t : Finset X | ↑t ⊆ D}.Countable := by
  classical
  have h_fin : {u : Set X | u.Finite ∧ u ⊆ D}.Countable :=
    Set.countable_ofPred_finite_subset hD
  apply Set.Countable.mono ?_ (h_fin.image
    (fun (u : Set X) => if h : u.Finite then h.toFinset else ∅))
  intro t ht
  refine ⟨↑t, ⟨Finset.finite_toSet t, ht⟩, ?_⟩
  simp

omit [IsOrderedAddMonoid X] [NormedVectorLattice X] in
/-- If `D` is countable, then so is its sup-closure. -/
private lemma countable_supClosure {D : Set X} (hD : D.Countable) :
    (_root_.supClosure D).Countable := by
  classical
  set FD := {t : Finset X | ↑t ⊆ D} with hFD_def
  have hFD : FD.Countable := countable_finsets_subset hD
  apply Set.Countable.mono ?_
    (hFD.image (fun t : Finset X => if h : t.Nonempty then t.sup' h id else (0 : X)))
  intro x hx
  obtain ⟨t, ht, hsub, rfl⟩ := hx
  refine ⟨t, hsub, ?_⟩
  simp [dite_eq_left ht]

omit [IsOrderedAddMonoid X] [NormedVectorLattice X] in
/-- If `D` is countable, then so is its inf-closure. -/
private lemma countable_infClosure {D : Set X} (hD : D.Countable) :
    (_root_.infClosure D).Countable := by
  classical
  set FD := {t : Finset X | ↑t ⊆ D} with hFD_def
  have hFD : FD.Countable := countable_finsets_subset hD
  apply Set.Countable.mono ?_
    (hFD.image (fun t : Finset X => if h : t.Nonempty then t.inf' h id else (0 : X)))
  intro x hx
  obtain ⟨t, ht, hsub, rfl⟩ := hx
  refine ⟨t, hsub, ?_⟩
  simp [dite_eq_left ht]

/-- If `s ⊆ closure D`, then every element of `supClosure s` belongs to the closure of
`supClosure D`. -/
private lemma supClosure_subset_closure_supClosure {s D : Set X}
    (h : s ⊆ closure D) :
    _root_.supClosure s ⊆ closure (_root_.supClosure D) := by
  intro x hx
  obtain ⟨t, ht, hsub, rfl⟩ := hx
  classical
  have ht_attach : t.attach.Nonempty := Finset.attach_nonempty_iff.mpr ht
  choose f hf_mem hf_tendsto using fun (y : {a // a ∈ t}) =>
    (mem_closure_iff_seq_limit.mp (h (hsub y.property)) :
      ∃ seq, (∀ n, seq n ∈ D) ∧ Filter.Tendsto seq Filter.atTop (nhds y.val))
  set xn : ℕ → X := fun n => t.attach.sup' ht_attach (fun y => f y n)
  have h_sum_mem : ∀ n, xn n ∈ _root_.supClosure D := by
    intro n
    refine ⟨t.attach.image (fun y => f y n), ht_attach.image _, ?_, ?_⟩
    · rintro z hz
      simp only [Finset.coe_image, Set.mem_image] at hz
      obtain ⟨y, _, rfl⟩ := hz
      exact hf_mem y n
    · rw [Finset.sup'_image]
      rfl
  have h_eq : t.attach.sup' ht_attach (Subtype.val : {a // a ∈ t} → X) = t.sup' ht id := by
    refine le_antisymm ?_ ?_
    · exact Finset.sup'_le _ _ fun y _ => Finset.le_sup' (f := id) y.2
    · refine Finset.sup'_le _ _ fun a ha => ?_
      exact Finset.le_sup' (f := Subtype.val) (Finset.mem_attach t ⟨a, ha⟩)
  have h_tendsto : Filter.Tendsto xn Filter.atTop
      (nhds (t.attach.sup' ht_attach (Subtype.val : {a // a ∈ t} → X))) :=
    Filter.Tendsto.finset_sup'_nhds_apply ht_attach (fun y _ => hf_tendsto y)
  rw [← h_eq]
  exact mem_closure_of_tendsto h_tendsto (Filter.Eventually.of_forall h_sum_mem)

/-- Dual version for inf-closure. -/
private lemma infClosure_subset_closure_infClosure {s D : Set X}
    (h : s ⊆ closure D) :
    _root_.infClosure s ⊆ closure (_root_.infClosure D) := by
  intro x hx
  obtain ⟨t, ht, hsub, rfl⟩ := hx
  classical
  have ht_attach : t.attach.Nonempty := Finset.attach_nonempty_iff.mpr ht
  choose f hf_mem hf_tendsto using fun (y : {a // a ∈ t}) =>
    (mem_closure_iff_seq_limit.mp (h (hsub y.property)) :
      ∃ seq, (∀ n, seq n ∈ D) ∧ Filter.Tendsto seq Filter.atTop (nhds y.val))
  set xn : ℕ → X := fun n => t.attach.inf' ht_attach (fun y => f y n)
  have h_sum_mem : ∀ n, xn n ∈ _root_.infClosure D := by
    intro n
    refine ⟨t.attach.image (fun y => f y n), ht_attach.image _, ?_, ?_⟩
    · rintro z hz
      simp only [Finset.coe_image, Set.mem_image] at hz
      obtain ⟨y, _, rfl⟩ := hz
      exact hf_mem y n
    · rw [Finset.inf'_image]
      rfl
  have h_eq : t.attach.inf' ht_attach (Subtype.val : {a // a ∈ t} → X) = t.inf' ht id := by
    refine le_antisymm ?_ ?_
    · refine Finset.le_inf' _ _ fun a ha => ?_
      exact Finset.inf'_le (f := Subtype.val) (Finset.mem_attach t ⟨a, ha⟩)
    · exact Finset.le_inf' _ _ fun y _ => Finset.inf'_le (f := id) y.2
  have h_tendsto : Filter.Tendsto xn Filter.atTop
      (nhds (t.attach.inf' ht_attach (Subtype.val : {a // a ∈ t} → X))) :=
    Filter.Tendsto.finset_inf'_nhds_apply ht_attach (fun y _ => hf_tendsto y)
  rw [← h_eq]
  exact mem_closure_of_tendsto h_tendsto (Filter.Eventually.of_forall h_sum_mem)

/-- IsSeparable is preserved under sup-closure in a normed vector lattice. -/
private lemma isSeparable_supClosure {s : Set X}
    (hs : TopologicalSpace.IsSeparable s) :
    TopologicalSpace.IsSeparable (_root_.supClosure s) := by
  obtain ⟨D, hD_ctble, hs_sub⟩ := hs
  exact ⟨_root_.supClosure D, countable_supClosure hD_ctble,
    supClosure_subset_closure_supClosure hs_sub⟩

/-- IsSeparable is preserved under inf-closure in a normed vector lattice. -/
private lemma isSeparable_infClosure {s : Set X}
    (hs : TopologicalSpace.IsSeparable s) :
    TopologicalSpace.IsSeparable (_root_.infClosure s) := by
  obtain ⟨D, hD_ctble, hs_sub⟩ := hs
  exact ⟨_root_.infClosure D, countable_infClosure hD_ctble,
    infClosure_subset_closure_infClosure hs_sub⟩

/-- The closed vector sublattice generated by a countable subset of a normed
vector lattice is separable. -/
theorem separableSpace_topologicalClosure_generated_of_countable
    {A : Set X} (hA : A.Countable) :
    TopologicalSpace.SeparableSpace
      ↥(topologicalClosure (generated A)).toSubmodule := by
  have h_span_eq : (generated A : Set X) =
      (generated (Submodule.span ℝ A : Set X) : Set X) := by
    refine Set.Subset.antisymm ?_ ?_
    · exact generated_le (Set.Subset.trans Submodule.subset_span (subset_generated _))
    · exact generated_le
        (Submodule.span_le.mpr (subset_generated A))
  have h_gen : (generated A : Set X) =
      _root_.supClosure (_root_.infClosure (Submodule.span ℝ A : Set X)) := by
    rw [h_span_eq]; exact generated_submodule_eq_supClosure_infClosure _
  have h_span_sep : TopologicalSpace.IsSeparable (Submodule.span ℝ A : Set X) :=
    (hA.isSeparable).span
  have h_gen_sep : TopologicalSpace.IsSeparable (generated A : Set X) := by
    rw [h_gen]
    exact isSeparable_supClosure (isSeparable_infClosure h_span_sep)
  have h_closure_sep : TopologicalSpace.IsSeparable
      ((topologicalClosure (generated A)).toSubmodule : Set X) := by
    have : ((topologicalClosure (generated A)).toSubmodule : Set X) =
        closure (generated A : Set X) := Submodule.topologicalClosure_coe _
    rw [this]
    exact h_gen_sep.closure
  exact h_closure_sep.separableSpace

end VectorSublattice

end Normed
