/-
Copyright (c) 2026 David Muñoz-Lahoz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Muñoz-Lahoz
-/

module

public import LeanPool.OrderClosures.BanLat.Substructures.Sublattice
public import LeanPool.OrderClosures.BanLat.Normed
public import LeanPool.OrderClosures.BanLat.OrderUnit
public import Mathlib.Analysis.Normed.Group.Completeness


/-!
# Order ideals of vector lattices

An **order ideal** (or simply *ideal*) of a vector lattice is a sublattice that is **solid**:
if `x ∈ J` and `|y| ≤ |x|` then `y ∈ J`. Equivalently, an ideal is precisely a solid
subspace. This file defines the bundled `OrderIdeal` structure extending
`VectorSublattice` and establishes the basic characterisations and properties.
-/

@[expose] public section

variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]

/-- An `OrderIdeal` of a vector lattice `X` is a vector sublattice that is **solid**:
whenever `x ∈ J` and `0 ≤ y ≤ x`, we have `y ∈ J`. -/
structure OrderIdeal (X : Type*) [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X]
    extends VectorSublattice X where
  solid' : ∀ {x y : X}, x ∈ carrier → 0 ≤ y → y ≤ x → y ∈ carrier

namespace OrderIdeal

instance : SetLike (OrderIdeal X) X where
  coe J := J.carrier
  coe_injective p q h := by
    cases p; cases q; congr
    exact SetLike.ext' h

/-- Order ideals of `X`, ordered by inclusion, form a **partial order**. -/
instance : PartialOrder (OrderIdeal X) := .ofSetLike (OrderIdeal X) X

variable (J : OrderIdeal X)

/-- An order ideal is solid: `x ∈ J` and `0 ≤ y ≤ x` imply `y ∈ J`. -/
theorem solid {x y : X} (hx : x ∈ J) (hy0 : 0 ≤ y) (hyx : y ≤ x) :
    y ∈ J :=
  J.solid' hx hy0 hyx

/-- Every order ideal is a vector sublattice. -/
def toVectorSublattice' : VectorSublattice X :=
  J.toVectorSublattice

/-- An order ideal is closed under `⊔`. -/
theorem sup_mem {x y : X} (hx : x ∈ J) (hy : y ∈ J) :
    x ⊔ y ∈ J :=
  J.toVectorSublattice.sup_mem hx hy

/-- An order ideal is closed under `⊓`. -/
theorem inf_mem {x y : X} (hx : x ∈ J) (hy : y ∈ J) :
    x ⊓ y ∈ J :=
  J.toVectorSublattice.inf_mem hx hy

/-- An order ideal is closed under absolute value. -/
theorem abs_mem {x : X} (hx : x ∈ J) : |x| ∈ J :=
  J.toVectorSublattice.abs_mem hx

/-- If `|x| ∈ J` then `x ∈ J`. -/
theorem mem_of_abs_mem {x : X} (h : |x| ∈ J) : x ∈ J := by
  have hpos : x⁺ ∈ J := J.solid h (posPart_nonneg x) (sup_le (le_abs_self x) (abs_nonneg x))
  have hneg : x⁻ ∈ J := J.solid h (negPart_nonneg x) (sup_le (neg_le_abs x) (abs_nonneg x))
  have := J.toSubmodule.sub_mem hpos hneg
  rwa [posPart_sub_negPart] at this

/-- Solidity in terms of absolute value: `x ∈ J` and `|y| ≤ |x|` imply
`y ∈ J`. -/
theorem mem_of_abs_le_abs {x y : X} (hx : x ∈ J)
    (h : |y| ≤ |x|) : y ∈ J :=
  J.mem_of_abs_mem (J.solid (J.abs_mem hx) (abs_nonneg y) h)

/-! ### Construction from solidity -/

/-- Build an `OrderIdeal` from a submodule that is solid in the absolute-value
sense: `x ∈ M` and `|y| ≤ |x|` imply `y ∈ M`. Every solid subspace is
automatically a sublattice and an ideal. -/
def ofSolid (M : Submodule ℝ X)
    (h : ∀ x y : X, x ∈ M → |y| ≤ |x| → y ∈ M) :
    OrderIdeal X where
  toSubmodule := M
  sup_mem' := fun {x y} hx hy => by
    have hax : |x| ∈ M := h x (|x|) hx (abs_of_nonneg (abs_nonneg x)).le
    have hay : |y| ∈ M := h y (|y|) hy (abs_of_nonneg (abs_nonneg y)).le
    have hab : |x| + |y| ∈ M := M.add_mem hax hay
    apply h (|x| + |y|) (x ⊔ y) hab
    rw [abs_of_nonneg (add_nonneg (abs_nonneg x) (abs_nonneg y))]
    apply sup_le
    · exact sup_le
        (le_trans (le_abs_self x) (le_add_of_nonneg_right (abs_nonneg y)))
        (le_trans (le_abs_self y) (le_add_of_nonneg_left (abs_nonneg x)))
    · calc -(x ⊔ y) = (-x) ⊓ (-y) := neg_sup x y
        _ ≤ -x := inf_le_left
        _ ≤ |x| := neg_le_abs x
        _ ≤ |x| + |y| := le_add_of_nonneg_right (abs_nonneg y)
  solid' := fun {x y} hx hy0 hyx =>
    h x y hx (by rwa [abs_of_nonneg hy0, abs_of_nonneg (le_trans hy0 hyx)])

/-- A submodule is the carrier of an order ideal iff it is solid. -/
theorem solid_iff (M : Submodule ℝ X) :
    (∀ x y : X, x ∈ M → |y| ≤ |x| → y ∈ M) ↔
      (∀ x y : X, x ∈ M → 0 ≤ y → y ≤ x → y ∈ M) ∧
        ∀ x y : X, x ∈ M → y ∈ M → x ⊔ y ∈ M := by
  constructor
  · intro h
    exact ⟨fun _ _ hx hy0 hyx => (ofSolid M h).solid' hx hy0 hyx,
           fun _ _ hx hy => (ofSolid M h).sup_mem' hx hy⟩
  · intro ⟨hsol, hsup⟩ x y hx hle
    -- |x| ∈ M
    have habs_x : |x| ∈ M := hsup x (-x) hx (M.neg_mem hx)
    -- |y| ∈ M by solidity: 0 ≤ |y| ≤ |x| and |x| ∈ M
    have habs_y : |y| ∈ M := hsol (|x|) (|y|) habs_x (abs_nonneg y) hle
    -- y⁺ ∈ M: 0 ≤ y⁺ ≤ |y|
    have hpos : y⁺ ∈ M :=
      hsol (|y|) y⁺ habs_y (posPart_nonneg y) (sup_le (le_abs_self y) (abs_nonneg y))
    -- y⁻ ∈ M: 0 ≤ y⁻ ≤ |y|
    have hneg : y⁻ ∈ M :=
      hsol (|y|) y⁻ habs_y (negPart_nonneg y) (sup_le (neg_le_abs y) (abs_nonneg y))
    have := M.sub_mem hpos hneg
    rwa [posPart_sub_negPart] at this

/-- The coercion to `Submodule ℝ X` is injective. -/
theorem toSubmodule_injective :
    Function.Injective
      (fun J : OrderIdeal X => J.toSubmodule) := by
  intro p q h
  cases p; cases q; congr
  exact VectorSublattice.toSubmodule_injective h

/-! ### Ideal generated by a set -/

/-- The intersection of two order ideals is an order ideal. -/
protected def inf (J₁ J₂ : OrderIdeal X) : OrderIdeal X where
  toSubmodule := J₁.toSubmodule ⊓ J₂.toSubmodule
  sup_mem' := fun hx hy =>
    ⟨J₁.sup_mem hx.1 hy.1, J₂.sup_mem hx.2 hy.2⟩
  solid' := fun hx hy0 hyx =>
    ⟨J₁.solid hx.1 hy0 hyx, J₂.solid hx.2 hy0 hyx⟩

/-- Order ideals of `X` admit arbitrary intersections: they form a complete
semilattice for the `⊓` operation. -/
instance : InfSet (OrderIdeal X) where
  sInf S :=
    { toSubmodule := InfSet.sInf ((fun J : OrderIdeal X => J.toSubmodule) '' S)
      sup_mem' := fun {x y} hx hy => by
        have hx' := (Submodule.mem_sInf).mp hx
        have hy' := (Submodule.mem_sInf).mp hy
        refine (Submodule.mem_sInf).mpr ?_
        rintro _ ⟨J, hJ, rfl⟩
        exact J.sup_mem (hx' _ ⟨J, hJ, rfl⟩) (hy' _ ⟨J, hJ, rfl⟩)
      solid' := fun {x y} hx hy0 hyx => by
        have hx' := (Submodule.mem_sInf).mp hx
        refine (Submodule.mem_sInf).mpr ?_
        rintro _ ⟨J, hJ, rfl⟩
        exact J.solid (hx' _ ⟨J, hJ, rfl⟩) hy0 hyx }

/-- Membership in an arbitrary intersection of order ideals. -/
@[simp] theorem mem_sInf {S : Set (OrderIdeal X)} {x : X} :
    x ∈ (InfSet.sInf S : OrderIdeal X) ↔ ∀ J ∈ S, x ∈ J := by
  change x ∈ InfSet.sInf ((fun J : OrderIdeal X => J.toSubmodule) '' S) ↔ _
  rw [Submodule.mem_sInf]
  exact ⟨fun h J hJ => h _ ⟨J, hJ, rfl⟩, by rintro h _ ⟨J, hJ, rfl⟩; exact h J hJ⟩

/-- The **ideal generated by a set** `s ⊆ X` is the smallest order ideal of
`X` containing `s`, defined as the intersection of all order ideals containing
`s`. -/
def generated (s : Set X) : OrderIdeal X :=
  InfSet.sInf {J : OrderIdeal X | s ⊆ (J : Set X)}

/-- The set `s` is contained in the ideal it generates. -/
theorem subset_generated (s : Set X) : s ⊆ (generated s : Set X) :=
  fun _ hx => mem_sInf.mpr (fun _ hJ => hJ hx)

/-- The ideal generated by `s` is contained in any ideal containing `s`. -/
theorem generated_le {s : Set X} {J : OrderIdeal X} (h : s ⊆ (J : Set X)) :
    generated s ≤ J :=
  fun _ hx => mem_sInf.mp hx J h

/-- The order ideal of elements bounded in absolute value by a non-negative
linear combination of `|y|`'s for `y ∈ s`. -/
private def generatedAux (s : Set X) : OrderIdeal X :=
  ofSolid
    { carrier := {x : X | ∃ (t : Finset X) (c : X → ℝ),
        (∀ y ∈ t, y ∈ s) ∧ (∀ y ∈ t, 0 ≤ c y) ∧ |x| ≤ ∑ y ∈ t, c y • |y|}
      add_mem' := by
        classical
        rintro x x' ⟨t, c, hts, hc, hxle⟩ ⟨t', c', ht's, hc', hx'le⟩
        refine ⟨t ∪ t',
          fun y => (if y ∈ t then c y else 0) + (if y ∈ t' then c' y else 0),
          ?_, ?_, ?_⟩
        · intro y hy
          rcases Finset.mem_union.mp hy with h | h
          · exact hts y h
          · exact ht's y h
        · intro y _
          refine add_nonneg ?_ ?_
          · split_ifs with h
            · exact hc y h
            · exact le_rfl
          · split_ifs with h
            · exact hc' y h
            · exact le_rfl
        · have h1 : ∑ y ∈ t, c y • |y| =
              ∑ y ∈ t ∪ t', (if y ∈ t then c y else 0) • |y| := by
            rw [show ∑ y ∈ t, c y • |y| =
                ∑ y ∈ t, (if y ∈ t then c y else 0) • |y| from
              Finset.sum_congr rfl (fun y hy => by rw [ite_eq_left hy])]
            exact Finset.sum_subset Finset.subset_union_left
              (fun y _ hy => by rw [ite_eq_right hy, zero_smul])
          have h2 : ∑ y ∈ t', c' y • |y| =
              ∑ y ∈ t ∪ t', (if y ∈ t' then c' y else 0) • |y| := by
            rw [show ∑ y ∈ t', c' y • |y| =
                ∑ y ∈ t', (if y ∈ t' then c' y else 0) • |y| from
              Finset.sum_congr rfl (fun y hy => by rw [ite_eq_left hy])]
            exact Finset.sum_subset Finset.subset_union_right
              (fun y _ hy => by rw [ite_eq_right hy, zero_smul])
          calc |x + x'|
              ≤ |x| + |x'| := abs_add_le _ _
            _ ≤ (∑ y ∈ t, c y • |y|) + (∑ y ∈ t', c' y • |y|) :=
                add_le_add hxle hx'le
            _ = (∑ y ∈ t ∪ t', (if y ∈ t then c y else 0) • |y|) +
                (∑ y ∈ t ∪ t', (if y ∈ t' then c' y else 0) • |y|) := by
                rw [h1, h2]
            _ = ∑ y ∈ t ∪ t', ((if y ∈ t then c y else 0) +
                  (if y ∈ t' then c' y else 0)) • |y| := by
                rw [← Finset.sum_add_distrib]
                refine Finset.sum_congr rfl fun y _ => ?_
                rw [add_smul]
      zero_mem' := ⟨∅, fun _ => 0, by simp, by simp, by simp⟩
      smul_mem' := by
        rintro r x ⟨t, c, hts, hc, hxle⟩
        refine ⟨t, fun y => |r| * c y, hts,
          fun y hy => mul_nonneg (abs_nonneg _) (hc y hy), ?_⟩
        rw [abs_smul']
        calc |r| • |x|
            ≤ |r| • ∑ y ∈ t, c y • |y| :=
              smul_le_smul_of_nonneg_left hxle (abs_nonneg _)
          _ = ∑ y ∈ t, (|r| * c y) • |y| := by
              rw [Finset.smul_sum]
              refine Finset.sum_congr rfl fun y _ => ?_
              rw [smul_smul] }
    (fun x y ⟨t, c, hts, hc, hxle⟩ hyx_abs =>
      ⟨t, c, hts, hc, le_trans hyx_abs hxle⟩)

/-- **Explicit description of the generated ideal.** An element `x` lies in the
ideal generated by `s` if and only if `|x|` is bounded above by a non-negative
linear combination of absolute values of elements of `s`. -/
theorem mem_generated_iff {s : Set X} {x : X} :
    x ∈ generated s ↔
      ∃ (t : Finset X) (c : X → ℝ),
        (∀ y ∈ t, y ∈ s) ∧ (∀ y ∈ t, 0 ≤ c y) ∧
          |x| ≤ ∑ y ∈ t, c y • |y| := by
  refine ⟨fun hx => ?_, ?_⟩
  · have h : generated s ≤ generatedAux s := by
      apply generated_le
      intro y hy
      exact ⟨{y}, fun _ => 1, by
              intro z hz; rw [Finset.mem_singleton] at hz; exact hz ▸ hy,
            by intros; exact zero_le_one,
            by simp⟩
    exact h hx
  · rintro ⟨t, c, hts, hc, hxle⟩
    refine (mem_sInf (S := {J : OrderIdeal X | s ⊆ (J : Set X)})).mpr fun J hJ => ?_
    have hsum : ∑ y ∈ t, c y • |y| ∈ J := by
      apply J.toSubmodule.sum_mem
      intro y hy
      exact J.toSubmodule.smul_mem _ (J.abs_mem (hJ (hts y hy)))
    exact J.mem_of_abs_mem (J.solid hsum (abs_nonneg _) hxle)

/-! ### Principal ideal -/

/-- The **principal ideal** generated by `a` is the set of elements `x` with
`|x| ≤ c • |a|` for some `c ≥ 0`. -/
def principal (a : X) : OrderIdeal X where
  toSubmodule :=
    { carrier := {x : X | ∃ c : ℝ, 0 ≤ c ∧ |x| ≤ c • |a|}
      add_mem' := fun {x y} ⟨cx, hcx, hx⟩ ⟨cy, hcy, hy⟩ =>
        ⟨cx + cy, add_nonneg hcx hcy, by
          calc |x + y| ≤ |x| + |y| := abs_add_le x y
            _ ≤ cx • |a| + cy • |a| := add_le_add hx hy
            _ = (cx + cy) • |a| := (add_smul cx cy |a|).symm⟩
      zero_mem' := ⟨0, le_rfl, by simp⟩
      smul_mem' := fun r x ⟨c, hc, hx⟩ =>
        ⟨|r| * c, mul_nonneg (abs_nonneg r) hc, by
          rw [abs_smul' x r]
          calc |r| • |x| ≤ |r| • (c • |a|) :=
                smul_le_smul_of_nonneg_left hx (abs_nonneg r)
            _ = (|r| * c) • |a| := smul_smul |r| c |a|⟩ }
  sup_mem' := fun {x y} ⟨cx, hcx, hx⟩ ⟨cy, hcy, hy⟩ =>
    ⟨cx + cy, add_nonneg hcx hcy, by
      have : |x ⊔ y| ≤ |x| + |y| := by
        apply sup_le
        · exact sup_le
            (le_trans (le_abs_self x) (le_add_of_nonneg_right (abs_nonneg y)))
            (le_trans (le_abs_self y) (le_add_of_nonneg_left (abs_nonneg x)))
        · calc -(x ⊔ y) = (-x) ⊓ (-y) := neg_sup x y
            _ ≤ -x := inf_le_left
            _ ≤ |x| := neg_le_abs x
            _ ≤ |x| + |y| := le_add_of_nonneg_right (abs_nonneg y)
      calc |x ⊔ y| ≤ |x| + |y| := this
        _ ≤ cx • |a| + cy • |a| := add_le_add hx hy
        _ = (cx + cy) • |a| := (add_smul cx cy |a|).symm⟩
  solid' := fun {x y} ⟨c, hc, hx⟩ hy0 hyx =>
    ⟨c, hc, le_trans (by rw [abs_of_nonneg hy0]; exact le_trans hyx (le_abs_self x)) hx⟩

/-- Characterisation of membership in the principal ideal. -/
theorem mem_principal {a x : X} :
    x ∈ principal a ↔ ∃ c : ℝ, 0 ≤ c ∧ |x| ≤ c • |a| := Iff.rfl

/-- The generator belongs to its own principal ideal. -/
theorem self_mem_principal (a : X) : a ∈ principal a :=
  ⟨1, zero_le_one, by simp⟩

/-- The principal ideal generated by `a` coincides with the ideal generated by
the singleton `{|a|}`. -/
theorem principal_eq_generated_abs (a : X) :
    principal a = generated ({|a|} : Set X) := by
  refine le_antisymm (fun x hx => ?_) (generated_le ?_)
  · obtain ⟨c, hc, hxle⟩ := hx
    refine (mem_sInf (S := {J : OrderIdeal X | {|a|} ⊆ (J : Set X)})).mpr fun J hJ => ?_
    have ha : |a| ∈ J := hJ rfl
    have hca : c • |a| ∈ J := J.toSubmodule.smul_mem c ha
    exact J.mem_of_abs_mem (J.solid hca (abs_nonneg _) hxle)
  · intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact ⟨1, zero_le_one, by rw [abs_abs, one_smul]⟩

/-! ### Gauge norm on the principal ideal -/

variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]

/-- The **gauge norm** (or order-unit norm) of `x` with respect to `a` is
`inf {c ≥ 0 | |x| ≤ c • |a|}`. For `x` in the principal ideal of `a`, this
is finite and defines a lattice seminorm; it is a norm precisely when the
ambient space is Archimedean. -/
noncomputable def gaugeNorm (a x : X) : ℝ :=
  sInf {c : ℝ | 0 ≤ c ∧ |x| ≤ c • |a|}

variable (a : X)

/-- The gauge norm is non-negative. -/
theorem gaugeNorm_nonneg (x : X) : 0 ≤ gaugeNorm a x := by
  unfold gaugeNorm
  by_cases h : {c : ℝ | 0 ≤ c ∧ |x| ≤ c • |a|}.Nonempty
  · exact le_csInf h fun _ ⟨hc, _⟩ => hc
  · rw [Set.not_nonempty_iff_eq_empty.mp h, Real.sInf_empty]

/-- The gauge norm of zero is zero. -/
theorem gaugeNorm_zero : gaugeNorm a 0 = 0 := by
  apply le_antisymm
  · exact csInf_le ⟨0, fun _ ⟨hd, _⟩ => hd⟩ ⟨le_rfl, by simp⟩
  · exact gaugeNorm_nonneg a 0

/-- The gauge norm is symmetric. -/
theorem gaugeNorm_neg (x : X) :
    gaugeNorm a (-x) = gaugeNorm a x := by
  simp only [gaugeNorm, abs_neg]

/-- Triangle inequality for the gauge norm. -/
private theorem gaugeNorm_bddBelow (x : X) :
    BddBelow {c : ℝ | 0 ≤ c ∧ |x| ≤ c • |a|} :=
  ⟨0, fun _ ⟨hc, _⟩ => hc⟩

theorem gaugeNorm_add_le {x y : X} (hx : x ∈ principal a) (hy : y ∈ principal a) :
    gaugeNorm a (x + y) ≤ gaugeNorm a x + gaugeNorm a y := by
  -- Bound `gaugeNorm a (x + y) - cy` for each admissible bound `cy` of `y`.
  have step1 : ∀ cy, cy ∈ {c : ℝ | 0 ≤ c ∧ |y| ≤ c • |a|} →
      gaugeNorm a (x + y) - cy ≤ gaugeNorm a x := by
    intro cy ⟨hcy, hcy_le⟩
    apply le_csInf hx
    intro cx ⟨hcx, hcx_le⟩
    have : cx + cy ∈ {c : ℝ | 0 ≤ c ∧ |x + y| ≤ c • |a|} :=
      ⟨add_nonneg hcx hcy, le_trans (abs_add_le x y)
        (by rw [add_smul]; exact add_le_add hcx_le hcy_le)⟩
    exact sub_le_iff_le_add.mpr (csInf_le (gaugeNorm_bddBelow a (x + y)) this)
  -- Then take the infimum over admissible bounds of `y`.
  have step2 : gaugeNorm a (x + y) - gaugeNorm a x ≤ gaugeNorm a y :=
    le_csInf hy (fun cy hcy => by linarith [step1 cy hcy])
  linarith

/-- Absolute homogeneity of the gauge norm. -/
private theorem gaugeNorm_div_mem {r : ℝ} (hr_pos : 0 < |r|) {x : X} {c : ℝ}
    (hc : 0 ≤ c) (hle : |r| • |x| ≤ c • |a|) :
    c / |r| ∈ {c : ℝ | 0 ≤ c ∧ |x| ≤ c • |a|} := by
  refine ⟨div_nonneg hc hr_pos.le, ?_⟩
  have := smul_le_smul_of_nonneg_left hle (inv_nonneg.mpr hr_pos.le)
  rw [smul_smul, inv_mul_cancel₀ (ne_of_gt hr_pos), one_smul, smul_smul] at this
  rwa [div_eq_inv_mul]

theorem gaugeNorm_smul (r : ℝ) (x : X) :
    gaugeNorm a (r • x) = |r| * gaugeNorm a x := by
  by_cases hr : r = 0
  · simp [hr, gaugeNorm_zero]
  · have hr_pos : (0 : ℝ) < |r| := abs_pos.mpr hr
    -- S_x nonempty ↔ S_{rx} nonempty (when r ≠ 0)
    by_cases hne : {c : ℝ | 0 ≤ c ∧ |x| ≤ c • |a|}.Nonempty
    · apply le_antisymm
      · -- ≤: gaugeNorm(rx)/|r| ≤ gaugeNorm(x), then multiply
        suffices h : gaugeNorm a (r • x) / |r| ≤ gaugeNorm a x from
          (div_le_iff₀ hr_pos).mp h |>.trans (le_of_eq (mul_comm _ _))
        apply le_csInf hne
        intro d ⟨hd, hle⟩
        rw [div_le_iff₀ hr_pos]
        exact (csInf_le (gaugeNorm_bddBelow a (r • x))
          ⟨mul_nonneg hr_pos.le hd, by
            rw [abs_smul' x r, mul_smul]
            exact smul_le_smul_of_nonneg_left hle hr_pos.le⟩).trans (le_of_eq (mul_comm _ _))
      · -- ≥: for any c in S_{rx}, c/|r| ∈ S_x, so gaugeNorm(x) ≤ c/|r|
        obtain ⟨d, hd, hle⟩ := hne
        have hne_rx : {c : ℝ | 0 ≤ c ∧ |r • x| ≤ c • |a|}.Nonempty :=
          ⟨|r| * d, mul_nonneg hr_pos.le hd, by
            rw [abs_smul' x r, mul_smul]
            exact smul_le_smul_of_nonneg_left hle hr_pos.le⟩
        apply le_csInf hne_rx
        intro c ⟨hc, hle'⟩
        calc |r| * gaugeNorm a x
            ≤ |r| * (c / |r|) :=
              mul_le_mul_of_nonneg_left
                (csInf_le (gaugeNorm_bddBelow a x) (gaugeNorm_div_mem a hr_pos hc
                  (by rwa [abs_smul' x r] at hle'))) hr_pos.le
          _ = c := by field_simp
    · -- Both S_x and S_{rx} empty: both sides are 0
      have hne2 : ¬{c : ℝ | 0 ≤ c ∧ |r • x| ≤ c • |a|}.Nonempty := by
        intro ⟨c, hc, hle⟩
        exact hne ⟨c / |r|, gaugeNorm_div_mem a hr_pos hc
          (by rwa [abs_smul' x r] at hle)⟩
      simp only [gaugeNorm, Set.not_nonempty_iff_eq_empty.mp hne,
        Set.not_nonempty_iff_eq_empty.mp hne2, Real.sInf_empty, mul_zero]

/-- The gauge norm controls the absolute value: `|x| ≤ ‖x‖_a • |a|` for
`x` in the principal ideal. -/
theorem abs_le_gaugeNorm_smul_abs [IsVLArchimedean X] {x : X}
    (hx : x ∈ principal a) : |x| ≤ gaugeNorm a x • |a| := by
  suffices h : (|x| - gaugeNorm a x • |a|)⁺ = 0 by
    have := le_posPart (|x| - gaugeNorm a x • |a|)
    rw [h] at this; exact sub_nonpos.mp this
  apply IsVLArchimedean.eq_zero_of_nonneg_of_forall_nsmul_le (y := |a|) (posPart_nonneg _)
  intro n
  by_cases hn : n = 0
  · simp [hn]
  · have hne : {c : ℝ | 0 ≤ c ∧ |x| ≤ c • |a|}.Nonempty := hx
    have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hlt : gaugeNorm a x < gaugeNorm a x + 1 / ↑n :=
      lt_add_of_pos_right _ (div_pos one_pos hn_pos)
    obtain ⟨c, ⟨_, hcle⟩, hc_lt⟩ := exists_lt_of_csInf_lt hne hlt
    have hstep : |x| - gaugeNorm a x • |a| ≤ (1 / (↑n : ℝ)) • |a| := by
      calc |x| - gaugeNorm a x • |a|
          ≤ c • |a| - gaugeNorm a x • |a| := sub_le_sub_right hcle _
        _ = (c - gaugeNorm a x) • |a| := (sub_smul c (gaugeNorm a x) |a|).symm
        _ ≤ (1 / ↑n) • |a| :=
            smul_le_smul_of_nonneg_right (by linarith) (abs_nonneg a)
    have hpos_le : (|x| - gaugeNorm a x • |a|)⁺ ≤ (1 / (↑n : ℝ)) • |a| :=
      sup_le hstep (smul_nonneg (div_nonneg one_pos.le hn_pos.le) (abs_nonneg a))
    calc n • (|x| - gaugeNorm a x • |a|)⁺
        ≤ n • ((1 / (↑n : ℝ)) • |a|) :=
          nsmul_le_nsmul hpos_le (smul_nonneg (div_nonneg one_pos.le hn_pos.le)
            (abs_nonneg a)) le_rfl
      _ = ((↑n : ℝ) * (1 / ↑n)) • |a| := by
          rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
      _ = |a| := by rw [mul_one_div_cancel (ne_of_gt hn_pos), one_smul]

/-- Any admissible constant bounds the gauge norm from above. -/
theorem gaugeNorm_le_of_abs_le {x : X} {c : ℝ} (hc : 0 ≤ c)
    (h : |x| ≤ c • |a|) : gaugeNorm a x ≤ c :=
  csInf_le ⟨0, fun _ ⟨hd, _⟩ => hd⟩ ⟨hc, h⟩

/-- The gauge norm is monotone with respect to `|·|`: the solid-norm
property. -/
theorem gaugeNorm_mono_abs {x y : X} (hy : y ∈ principal a) (h : |x| ≤ |y|) :
    gaugeNorm a x ≤ gaugeNorm a y := by
  -- S_y ⊆ S_x, so sInf S_x ≤ sInf S_y
  apply le_csInf hy
  intro c ⟨hc, hle⟩
  exact csInf_le (gaugeNorm_bddBelow a x) ⟨hc, le_trans h hle⟩

/-- In an Archimedean vector lattice the gauge norm is definite:
`gaugeNorm a x = 0 ↔ x = 0` for `x` in the principal ideal of `a`. -/
theorem gaugeNorm_eq_zero_iff [IsVLArchimedean X] {x : X}
    (hx : x ∈ principal a) : gaugeNorm a x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have := abs_le_gaugeNorm_smul_abs a hx
    rw [h, zero_smul] at this
    exact (abs_eq_zero_iff_zero x).mp (le_antisymm this (abs_nonneg x))
  · intro h; rw [h]; exact gaugeNorm_zero a

/-- The closed unit ball of the gauge norm is the order interval
`[-|a|, |a|]`. -/
theorem gaugeNorm_le_one_iff [IsVLArchimedean X] {x : X} (hx : x ∈ principal a) :
    gaugeNorm a x ≤ 1 ↔ |x| ≤ |a| := by
  constructor
  · intro h
    calc |x| ≤ gaugeNorm a x • |a| := abs_le_gaugeNorm_smul_abs a hx
      _ ≤ 1 • |a| := smul_le_smul_of_nonneg_right h (abs_nonneg a)
      _ = |a| := one_smul ℝ |a|
  · intro h
    exact gaugeNorm_le_of_abs_le a one_pos.le (by rwa [one_smul])

/-- If `0 ≤ e ≤ u` then `‖·‖_u ≤ ‖·‖_e` on `I_e`. -/
theorem gaugeNorm_anti {e u : X} (he : 0 ≤ e) (heu : e ≤ u)
    {x : X} (hx : x ∈ principal e) : gaugeNorm u x ≤ gaugeNorm e x := by
  -- S_e ⊆ S_u (since |e| = e ≤ u = |u|, so c • |e| ≤ c • |u|)
  apply le_csInf hx
  intro c ⟨hc, hle⟩
  apply csInf_le (gaugeNorm_bddBelow u x)
  exact ⟨hc, le_trans hle (smul_le_smul_of_nonneg_left
    (by rwa [abs_of_nonneg he, abs_of_nonneg (le_trans he heu)]) hc)⟩

/-! ### Normed vector lattice structure on the principal ideal -/

/-- The underlying submodule of the principal ideal. -/
abbrev principalSubmodule (a : X) : Submodule ℝ X :=
  (principal a).toSubmodule

/-- The gauge norm as a `Norm` instance on the principal ideal. -/
noncomputable instance instNormPrincipal (a : X) :
    Norm ↥(principalSubmodule a) where
  norm x := gaugeNorm a x.1

/-- The principal ideal inherits a lattice structure from `X`. -/
noncomputable instance instLatticePrincipal (a : X) :
    Lattice ↥(principalSubmodule a) where
  sup x y := ⟨x.1 ⊔ y.1, (principal a).sup_mem x.2 y.2⟩
  inf x y := ⟨x.1 ⊓ y.1, (principal a).inf_mem x.2 y.2⟩
  le_sup_left := fun x y => show x.1 ≤ x.1 ⊔ y.1 from le_sup_left
  le_sup_right := fun x y => show y.1 ≤ x.1 ⊔ y.1 from le_sup_right
  sup_le := fun x y z h1 h2 => show x.1 ⊔ y.1 ≤ z.1 from sup_le h1 h2
  inf_le_left := fun x y => show x.1 ⊓ y.1 ≤ x.1 from inf_le_left
  inf_le_right := fun x y => show x.1 ⊓ y.1 ≤ y.1 from inf_le_right
  le_inf := fun x y z h1 h2 => show x.1 ≤ y.1 ⊓ z.1 from le_inf h1 h2

/-- The principal ideal is an ordered additive monoid. -/
instance instIsOrderedAddMonoidPrincipal (a : X) :
    @IsOrderedAddMonoid ↥(principalSubmodule a)
      inferInstance (instLatticePrincipal a).toPartialOrder.toPreorder where
  add_le_add_left := fun x y (h : x.1 ≤ y.1) z =>
    show x.1 + z.1 ≤ y.1 + z.1 from add_le_add_left h _

/-- In an Archimedean vector lattice, the principal ideal `I_a` with the gauge
norm is a normed additive commutative group. -/
@[reducible]
noncomputable def principalNormedAddCommGroup [IsVLArchimedean X]
    (a : X) :
    NormedAddCommGroup ↥(principalSubmodule a) :=
  NormedAddCommGroup.ofCore (𝕜 := ℝ) {
    toCore := {
      norm_nonneg := fun x => gaugeNorm_nonneg a x.1
      norm_smul := fun r x => gaugeNorm_smul a r x.1
      norm_triangle := fun x y => gaugeNorm_add_le a x.2 y.2
    }
    norm_eq_zero_iff := fun x => (gaugeNorm_eq_zero_iff a x.2).trans
      ⟨fun h => Subtype.ext h, fun h => congr_arg Subtype.val h⟩
  }

/-- In an Archimedean vector lattice, the principal ideal `I_a` with the gauge
norm admits a `VectorLattice` structure. -/
@[reducible]
noncomputable def principalVectorLattice (a : X) :
    @VectorLattice ↥(principalSubmodule a) inferInstance
      (instLatticePrincipal a)
      (instIsOrderedAddMonoidPrincipal a) where
  toModule := (principalSubmodule a).module
  smul_le_smul_of_nonneg_left := by
    intro c hc x y hxy
    change c • x.1 ≤ c • y.1
    exact smul_le_smul_of_nonneg_left hxy hc

/-- In an Archimedean vector lattice, the principal ideal `I_a` equipped with
the gauge norm is a normed vector lattice. -/
@[reducible]
noncomputable def principalNormedVectorLattice [IsVLArchimedean X]
    (a : X) :
    @NormedVectorLattice ↥(principalSubmodule a)
      (principalNormedAddCommGroup a)
      (instLatticePrincipal a)
      (instIsOrderedAddMonoidPrincipal a) := by
  letI : NormedAddCommGroup ↥(principalSubmodule a) := principalNormedAddCommGroup a
  letI : Lattice ↥(principalSubmodule a) := instLatticePrincipal a
  letI : IsOrderedAddMonoid ↥(principalSubmodule a) := instIsOrderedAddMonoidPrincipal a
  letI : VectorLattice ↥(principalSubmodule a) := principalVectorLattice a
  let solidNorm : HasSolidNorm ↥(principalSubmodule a) := {
    solid := by
      intro x y h
      change gaugeNorm a x.1 ≤ gaugeNorm a y.1
      exact gaugeNorm_mono_abs a y.2 h
  }
  let normSmul : NormSMulClass ℝ ↥(principalSubmodule a) := {
    norm_smul := by
      intro r x
      change gaugeNorm a (r • x.1) = ‖r‖ * gaugeNorm a x.1
      rw [gaugeNorm_smul a r x.1, Real.norm_eq_abs]
  }
  exact @NormedVectorLattice.mk ↥(principalSubmodule a)
    (principalNormedAddCommGroup a)
    (instLatticePrincipal a)
    (instIsOrderedAddMonoidPrincipal a)
    (principalVectorLattice a)
    solidNorm
    normSmul

/-! ### Sum of ideals -/

/-- A non-negative element dominated by a sum `u₁ + u₂` of positive elements of
`J₁` and `J₂` can be split accordingly, so it lies in `J₁ + J₂`. -/
private theorem sum_pos_mem (J₁ J₂ : OrderIdeal X) {v u₁ u₂ : X}
    (hu₁ : u₁ ∈ J₁) (hu₂ : u₂ ∈ J₂) (hu₁0 : 0 ≤ u₁) (hu₂0 : 0 ≤ u₂)
    (hv0 : 0 ≤ v) (hvle : v ≤ u₁ + u₂) :
    v ∈ J₁.toSubmodule + J₂.toSubmodule := by
  have hv₁ : v ⊓ u₁ ∈ J₁ := J₁.solid hu₁ (le_inf hv0 hu₁0) inf_le_right
  have heq : v - v ⊓ u₁ = (v - u₁)⁺ := by
    rw [inf_eq_sub_posPart_sub]; abel
  have hv₂ : v - v ⊓ u₁ ∈ J₂ := by
    rw [heq]
    exact J₂.solid hu₂ (posPart_nonneg _)
      (sup_le (sub_le_iff_le_add'.mpr hvle) hu₂0)
  refine Submodule.mem_sup.mpr ⟨v ⊓ u₁, hv₁, v - v ⊓ u₁, hv₂, ?_⟩
  abel

/-- The sum of two order ideals (as submodules) is again an order ideal. -/
def sum (J₁ J₂ : OrderIdeal X) : OrderIdeal X :=
  ofSolid (J₁.toSubmodule + J₂.toSubmodule) <| by
    intro x y hx hyx
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := Submodule.mem_sup.mp hx
    -- `|y| ≤ |x₁| + |x₂|`; split `y⁺` and `y⁻` separately using `sum_pos_mem`.
    have habs : |y| ≤ |x₁| + |x₂| := le_trans hyx (abs_add_le x₁ x₂)
    have h_pos_le : y⁺ ≤ |x₁| + |x₂| :=
      le_trans (sup_le (le_abs_self y) (abs_nonneg y)) habs
    have h_neg_le : y⁻ ≤ |x₁| + |x₂| :=
      le_trans (sup_le (neg_le_abs y) (abs_nonneg y)) habs
    have hpos : y⁺ ∈ J₁.toSubmodule + J₂.toSubmodule :=
      sum_pos_mem J₁ J₂ (J₁.abs_mem hx₁) (J₂.abs_mem hx₂)
        (abs_nonneg _) (abs_nonneg _) (posPart_nonneg _) h_pos_le
    have hneg : y⁻ ∈ J₁.toSubmodule + J₂.toSubmodule :=
      sum_pos_mem J₁ J₂ (J₁.abs_mem hx₁) (J₂.abs_mem hx₂)
        (abs_nonneg _) (abs_nonneg _) (negPart_nonneg _) h_neg_le
    have := (J₁.toSubmodule + J₂.toSubmodule).sub_mem hpos hneg
    rwa [posPart_sub_negPart] at this

/-- The underlying submodule of `sum J₁ J₂` is `J₁.toSubmodule + J₂.toSubmodule`. -/
@[simp]
theorem sum_toSubmodule (J₁ J₂ : OrderIdeal X) :
    (sum J₁ J₂).toSubmodule = J₁.toSubmodule + J₂.toSubmodule := rfl

/-- **Positive decomposition** in the sum of two ideals: every non-negative
element of `J₁ + J₂` admits a splitting `y = y₁ + y₂` with `0 ≤ y₁ ∈ J₁` and
`0 ≤ y₂ ∈ J₂`. -/
theorem exists_sum_decomp_nonneg (J₁ J₂ : OrderIdeal X) {y : X}
    (hy : y ∈ J₁.toSubmodule + J₂.toSubmodule) (hy0 : 0 ≤ y) :
    ∃ y₁ y₂ : X, y₁ ∈ J₁ ∧ y₂ ∈ J₂ ∧ y₁ + y₂ = y ∧ 0 ≤ y₁ ∧ 0 ≤ y₂ := by
  obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Submodule.mem_sup.mp hy
  have hau₁ : |u₁| ∈ J₁ := J₁.abs_mem hu₁
  have hau₂ : |u₂| ∈ J₂ := J₂.abs_mem hu₂
  have hau₁_nn : 0 ≤ |u₁| := abs_nonneg _
  have hau₂_nn : 0 ≤ |u₂| := abs_nonneg _
  have hyle : u₁ + u₂ ≤ |u₁| + |u₂| :=
    add_le_add (le_abs_self u₁) (le_abs_self u₂)
  refine ⟨(u₁ + u₂) ⊓ |u₁|, (u₁ + u₂) - (u₁ + u₂) ⊓ |u₁|,
    J₁.solid hau₁ (le_inf hy0 hau₁_nn) inf_le_right,
    ?_, by abel, le_inf hy0 hau₁_nn, ?_⟩
  · have heq : (u₁ + u₂) - (u₁ + u₂) ⊓ |u₁| = ((u₁ + u₂) - |u₁|)⁺ := by
      rw [inf_eq_sub_posPart_sub]; abel
    rw [heq]
    exact J₂.solid hau₂ (posPart_nonneg _)
      (sup_le (sub_le_iff_le_add'.mpr hyle) hau₂_nn)
  · have heq : (u₁ + u₂) - (u₁ + u₂) ⊓ |u₁| = ((u₁ + u₂) - |u₁|)⁺ := by
      rw [inf_eq_sub_posPart_sub]; abel
    rw [heq]; exact posPart_nonneg _

/-- **Bounded decomposition** in the sum of two ideals: every element of
`J₁ + J₂` admits a splitting `z = a + b` with `a ∈ J₁`, `b ∈ J₂` and the
lattice estimates `|a| ≤ |z|`, `|b| ≤ |z|`. -/
theorem exists_sum_decomp (J₁ J₂ : OrderIdeal X) {z : X}
    (hz : z ∈ J₁.toSubmodule + J₂.toSubmodule) :
    ∃ a b : X, a ∈ J₁ ∧ b ∈ J₂ ∧ a + b = z ∧ |a| ≤ |z| ∧ |b| ≤ |z| := by
  obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Submodule.mem_sup.mp hz
  have habs : |u₁ + u₂| ≤ |u₁| + |u₂| := abs_add_le u₁ u₂
  -- Positive part split
  have hxp_le : (u₁ + u₂)⁺ ≤ |u₁| + |u₂| :=
    le_trans (sup_le (le_abs_self _) (abs_nonneg _)) habs
  let ap := (u₁ + u₂)⁺ ⊓ |u₁|
  have hap_nn : 0 ≤ ap := le_inf (posPart_nonneg _) (abs_nonneg _)
  have hap_le_xp : ap ≤ (u₁ + u₂)⁺ := inf_le_left
  have hap_mem : ap ∈ J₁ := J₁.solid (J₁.abs_mem hu₁) hap_nn inf_le_right
  let bp := (u₁ + u₂)⁺ - ap
  have hbp_eq : bp = ((u₁ + u₂)⁺ - |u₁|)⁺ := by
    change (u₁ + u₂)⁺ - (u₁ + u₂)⁺ ⊓ |u₁| = ((u₁ + u₂)⁺ - |u₁|)⁺
    rw [inf_eq_sub_posPart_sub]; abel
  have hbp_nn : 0 ≤ bp := by rw [hbp_eq]; exact posPart_nonneg _
  have hbp_le_xp : bp ≤ (u₁ + u₂)⁺ := sub_le_self _ hap_nn
  have hbp_mem : bp ∈ J₂ := by
    rw [hbp_eq]
    exact J₂.solid (J₂.abs_mem hu₂) (posPart_nonneg _)
      (sup_le (sub_le_iff_le_add'.mpr hxp_le) (abs_nonneg _))
  have hab_p_sum : ap + bp = (u₁ + u₂)⁺ := by
    change ap + ((u₁ + u₂)⁺ - ap) = _
    abel
  -- Negative part split
  have hxn_le : (u₁ + u₂)⁻ ≤ |u₁| + |u₂| :=
    le_trans (sup_le (neg_le_abs _) (abs_nonneg _)) habs
  let an := (u₁ + u₂)⁻ ⊓ |u₁|
  have han_nn : 0 ≤ an := le_inf (negPart_nonneg _) (abs_nonneg _)
  have han_le_xn : an ≤ (u₁ + u₂)⁻ := inf_le_left
  have han_mem : an ∈ J₁ := J₁.solid (J₁.abs_mem hu₁) han_nn inf_le_right
  let bn := (u₁ + u₂)⁻ - an
  have hbn_eq : bn = ((u₁ + u₂)⁻ - |u₁|)⁺ := by
    change (u₁ + u₂)⁻ - (u₁ + u₂)⁻ ⊓ |u₁| = ((u₁ + u₂)⁻ - |u₁|)⁺
    rw [inf_eq_sub_posPart_sub]; abel
  have hbn_nn : 0 ≤ bn := by rw [hbn_eq]; exact posPart_nonneg _
  have hbn_le_xn : bn ≤ (u₁ + u₂)⁻ := sub_le_self _ han_nn
  have hbn_mem : bn ∈ J₂ := by
    rw [hbn_eq]
    exact J₂.solid (J₂.abs_mem hu₂) (posPart_nonneg _)
      (sup_le (sub_le_iff_le_add'.mpr hxn_le) (abs_nonneg _))
  have hab_n_sum : an + bn = (u₁ + u₂)⁻ := by
    change an + ((u₁ + u₂)⁻ - an) = _
    abel
  -- Assemble
  refine ⟨ap - an, bp - bn,
    J₁.toSubmodule.sub_mem hap_mem han_mem,
    J₂.toSubmodule.sub_mem hbp_mem hbn_mem, ?_, ?_, ?_⟩
  · calc ap - an + (bp - bn)
        = (ap + bp) - (an + bn) := by abel
      _ = (u₁ + u₂)⁺ - (u₁ + u₂)⁻ := by rw [hab_p_sum, hab_n_sum]
      _ = u₁ + u₂ := posPart_sub_negPart _
  · calc |ap - an|
        = |ap + (-an)| := by rw [sub_eq_add_neg]
      _ ≤ |ap| + |(-an)| := abs_add_le _ _
      _ = ap + an := by rw [abs_of_nonneg hap_nn, abs_neg, abs_of_nonneg han_nn]
      _ ≤ (u₁ + u₂)⁺ + (u₁ + u₂)⁻ := add_le_add hap_le_xp han_le_xn
      _ = |u₁ + u₂| := posPart_add_negPart _
  · calc |bp - bn|
        = |bp + (-bn)| := by rw [sub_eq_add_neg]
      _ ≤ |bp| + |(-bn)| := abs_add_le _ _
      _ = bp + bn := by rw [abs_of_nonneg hbp_nn, abs_neg, abs_of_nonneg hbn_nn]
      _ ≤ (u₁ + u₂)⁺ + (u₁ + u₂)⁻ := add_le_add hbp_le_xp hbn_le_xn
      _ = |u₁ + u₂| := posPart_add_negPart _

/-! ### Complete lattice structure -/

/-- The whole space `X` is an order ideal. -/
instance : Top (OrderIdeal X) where
  top :=
    { toSubmodule := ⊤
      sup_mem' := fun _ _ => Submodule.mem_top
      solid' := fun _ _ _ => Submodule.mem_top }

@[simp] theorem mem_top {x : X} : x ∈ (⊤ : OrderIdeal X) := Submodule.mem_top

/-- The trivial ideal `{0}` is an order ideal. -/
instance : Bot (OrderIdeal X) where
  bot :=
    { toSubmodule := ⊥
      sup_mem' := fun {x y} hx hy => by
        have hx' : x = 0 := (Submodule.mem_bot ℝ).mp hx
        have hy' : y = 0 := (Submodule.mem_bot ℝ).mp hy
        rw [hx', hy', sup_idem]; exact Submodule.zero_mem _
      solid' := fun {x y} hx hy0 hyx => by
        have hx' : x = 0 := (Submodule.mem_bot ℝ).mp hx
        rw [hx'] at hyx
        exact (Submodule.mem_bot ℝ).mpr (le_antisymm hyx hy0) }

@[simp] theorem mem_bot {x : X} : x ∈ (⊥ : OrderIdeal X) ↔ x = 0 :=
  Submodule.mem_bot ℝ

/-- Order ideals of `X`, ordered by inclusion, form a **complete lattice**.
Binary joins are given by the (Minkowski) sum `sum`, binary meets and arbitrary
infima are given by intersection, the bottom element is the trivial ideal
`{0}`, and the top element is the whole space. -/
instance : CompleteLattice (OrderIdeal X) where
  __ := (inferInstance : PartialOrder (OrderIdeal X))
  sup := sum
  inf := OrderIdeal.inf
  top := ⊤
  bot := ⊥
  sInf := sInf
  sSup S := sInf {K : OrderIdeal X | ∀ I ∈ S, I ≤ K}
  le_top := fun _ _ _ => Submodule.mem_top
  bot_le := fun J x hx => by
    have hx' : x ∈ (⊥ : Submodule ℝ X) := hx
    have : x = 0 := (Submodule.mem_bot ℝ).mp hx'
    exact this ▸ J.toSubmodule.zero_mem
  le_sup_left := fun J₁ J₂ x hx =>
    Submodule.mem_sup.mpr ⟨x, hx, 0, J₂.toSubmodule.zero_mem, add_zero x⟩
  le_sup_right := fun J₁ J₂ x hx =>
    Submodule.mem_sup.mpr ⟨0, J₁.toSubmodule.zero_mem, x, hx, zero_add x⟩
  sup_le := fun J₁ J₂ K hJ₁ hJ₂ x hx => by
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := Submodule.mem_sup.mp hx
    exact K.toSubmodule.add_mem (hJ₁ hx₁) (hJ₂ hx₂)
  inf_le_left := fun _ _ _ hx => hx.1
  inf_le_right := fun _ _ _ hx => hx.2
  le_inf := fun _ _ _ h₁ h₂ _ hx => ⟨h₁ hx, h₂ hx⟩
  isLUB_sSup := fun S => by
    refine ⟨?_, ?_⟩
    · intro J hJ x hx
      rw [mem_sInf]
      intro K hK
      exact hK J hJ hx
    · intro J hJ x hx
      rw [mem_sInf] at hx
      exact hx J hJ
  isGLB_sInf := fun S => by
    refine ⟨?_, ?_⟩
    · intro J hJ x hx
      rw [mem_sInf] at hx
      exact hx J hJ
    · intro J hJ x hx
      rw [mem_sInf]
      intro K hK
      exact hJ hK hx

@[simp] theorem sup_toSubmodule (J₁ J₂ : OrderIdeal X) :
    (J₁ ⊔ J₂).toSubmodule = J₁.toSubmodule + J₂.toSubmodule := rfl

@[simp] theorem inf_toSubmodule (J₁ J₂ : OrderIdeal X) :
    (J₁ ⊓ J₂).toSubmodule = J₁.toSubmodule ⊓ J₂.toSubmodule := rfl

/-! ### Strong order units and the principal ideal -/

/-- An element is a strong order unit precisely when it is non-negative and the
principal ideal it generates is the whole space. -/
theorem strongOrderUnit_iff_principal_eq_top {e : X} :
    StrongOrderUnit e ↔ 0 ≤ e ∧ principal e = ⊤ := by
  refine ⟨fun ⟨he, hdom⟩ => ⟨he, ?_⟩, fun ⟨he, htop⟩ => ⟨he, fun x => ?_⟩⟩
  · refine SetLike.ext fun x => iff_of_true ?_ mem_top
    obtain ⟨c, hc, hxc⟩ := hdom x
    exact ⟨c, hc, by rwa [abs_of_nonneg he]⟩
  · have hx : x ∈ principal e := htop ▸ mem_top
    obtain ⟨c, hc, hxc⟩ := hx
    exact ⟨c, hc, by rwa [abs_of_nonneg he] at hxc⟩

/-! ### Existence of proper non-trivial ideals -/

/-- Two non-negative lattice-disjoint elements cannot sit in a common principal
ideal: if `0 ≤ p, q` with `p ⊓ q = 0` and `q ∈ principal p`, then `q = 0`. -/
private lemma eq_zero_of_mem_principal_disjoint {p q : X} (hp : 0 ≤ p)
    (hq : 0 ≤ q) (hpq : p ⊓ q = 0) (hq_in : q ∈ principal p) : q = 0 := by
  obtain ⟨c, hc, hle⟩ := hq_in
  rw [abs_of_nonneg hq, abs_of_nonneg hp] at hle
  rcases le_or_gt 1 c with h1 | h1
  · have hq_le_cq : q ≤ c • q := by
      calc q = (1 : ℝ) • q := (one_smul ℝ q).symm
        _ ≤ c • q := smul_le_smul_of_nonneg_right h1 hq
    have hboth : q ≤ c • p ⊓ c • q := le_inf hle hq_le_cq
    rw [← nonneg_smul_inf p q c (le_trans zero_le_one h1), hpq, smul_zero] at hboth
    exact le_antisymm hboth hq
  · have hcp_le_p : c • p ≤ p := by
      calc c • p ≤ (1 : ℝ) • p := smul_le_smul_of_nonneg_right h1.le hp
        _ = p := one_smul ℝ p
    have hq_le_p : q ≤ p := le_trans hle hcp_le_p
    have : p ⊓ q = q := inf_eq_right.mpr hq_le_p
    rwa [this] at hpq

/-- If the real dimension of `X` is strictly greater than one, then `X` admits
an order ideal that is **neither trivial nor the whole space**. -/
theorem exists_proper_nontrivial [IsVLArchimedean X] (h : 1 < Module.rank ℝ X) :
    ∃ J : OrderIdeal X, J ≠ ⊥ ∧ J ≠ ⊤ := by
  obtain ⟨u, v, hu, hv, huv⟩ := exists_pair_ne_zero_isVLDisjoint h
  have habs_u_nn : 0 ≤ |u| := abs_nonneg u
  have habs_v_nn : 0 ≤ |v| := abs_nonneg v
  have habs_u_nz : |u| ≠ 0 := fun h => hu ((abs_eq_zero_iff_zero u).mp h)
  have habs_v_nz : |v| ≠ 0 := fun h => hv ((abs_eq_zero_iff_zero v).mp h)
  refine ⟨principal (|u|), ?_, ?_⟩
  · intro heq
    have : (|u| : X) ∈ (⊥ : OrderIdeal X) := heq ▸ self_mem_principal |u|
    exact habs_u_nz (mem_bot.mp this)
  · intro heq
    have hv_mem : (|v| : X) ∈ principal (|u|) := heq ▸ mem_top
    exact habs_v_nz
      (eq_zero_of_mem_principal_disjoint habs_u_nn habs_v_nn huv hv_mem)

/-! ### Closure of an ideal in a normed vector lattice -/

section Closure

variable {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [NormedVectorLattice X]

/-- The topological closure of the underlying submodule of an order ideal is
itself solid: if `x` lies in the closure and `|y| ≤ |x|`, then `y` lies in the
closure. -/
theorem topologicalClosure_solid (J : OrderIdeal X) :
    ∀ x y : X, x ∈ J.toSubmodule.topologicalClosure → |y| ≤ |x| →
      y ∈ J.toSubmodule.topologicalClosure := by
  intro x y hx hy_abs
  have hx' : x ∈ closure (J.toSubmodule : Set X) := by
    rwa [← Submodule.topologicalClosure_coe]
  obtain ⟨xn, hxn_mem, hxn_lim⟩ := mem_closure_iff_seq_limit.mp hx'
  -- Truncated sequence yₙ = (y ⊔ -|xₙ|) ⊓ |xₙ|, which lies in J and converges to y.
  set yn : ℕ → X := fun n => (y ⊔ (-|xn n|)) ⊓ |xn n| with hyn_def
  have habs_nn : ∀ n, (0 : X) ≤ |xn n| := fun _ => abs_nonneg _
  have hyn_mem : ∀ n, yn n ∈ J.toSubmodule := by
    intro n
    have habs_mem : |xn n| ∈ J := J.abs_mem (hxn_mem n)
    have h_le : yn n ≤ |xn n| := inf_le_right
    have h_neg_le : -|xn n| ≤ |xn n| :=
      le_trans (neg_nonpos_of_nonneg (habs_nn n)) (habs_nn n)
    have h_ge : -|xn n| ≤ yn n := le_inf le_sup_right h_neg_le
    have h_abs_yn : |yn n| ≤ |xn n| := by
      rw [abs_le']; exact ⟨h_le, by rwa [neg_le]⟩
    have : |yn n| ∈ J := J.solid habs_mem (abs_nonneg _) h_abs_yn
    exact J.mem_of_abs_mem this
  -- Continuity of `|·|`, `⊔`, `⊓` makes `yn → y`.
  have hcont_abs : Continuous (|·| : X → X) :=
    NormedVectorLattice.lipschitzWith_abs.continuous
  have habs_tendsto : Filter.Tendsto (fun n => |xn n|) Filter.atTop (nhds |x|) :=
    (hcont_abs.tendsto _).comp hxn_lim
  have hneg_tendsto : Filter.Tendsto (fun n => -|xn n|) Filter.atTop (nhds (-|x|)) :=
    habs_tendsto.neg
  have hsup_tendsto :
      Filter.Tendsto (fun n => y ⊔ (-|xn n|)) Filter.atTop (nhds (y ⊔ (-|x|))) :=
    (NormedVectorLattice.continuous_sup.tendsto _).comp
      (tendsto_const_nhds.prodMk_nhds hneg_tendsto)
  have hyn_tendsto :
      Filter.Tendsto yn Filter.atTop (nhds ((y ⊔ (-|x|)) ⊓ |x|)) :=
    (NormedVectorLattice.continuous_inf.tendsto _).comp
      (hsup_tendsto.prodMk_nhds habs_tendsto)
  have h_le_abs : y ≤ |x| := le_trans (le_abs_self y) hy_abs
  have h_neg_le : -|x| ≤ y := by rw [neg_le]; exact le_trans (neg_le_abs y) hy_abs
  have hy_eq : (y ⊔ (-|x|)) ⊓ |x| = y := by
    rw [sup_eq_left.mpr h_neg_le, inf_eq_left.mpr h_le_abs]
  rw [hy_eq] at hyn_tendsto
  have hy_in_closure : y ∈ closure (J.toSubmodule : Set X) :=
    mem_closure_of_tendsto hyn_tendsto (Filter.Eventually.of_forall hyn_mem)
  rwa [← Submodule.topologicalClosure_coe] at hy_in_closure

/-- The **norm closure** of an order ideal `J` in a normed vector lattice is
again an order ideal, whose underlying submodule is the topological closure of
`J.toSubmodule`. -/
def topologicalClosure (J : OrderIdeal X) : OrderIdeal X :=
  ofSolid J.toSubmodule.topologicalClosure (topologicalClosure_solid J)

@[simp]
theorem topologicalClosure_toSubmodule (J : OrderIdeal X) :
    (topologicalClosure J).toSubmodule = J.toSubmodule.topologicalClosure := rfl

end Closure

end OrderIdeal

/-- A **closed order ideal** of a Banach lattice is an order ideal whose
underlying set is closed in the norm topology. -/
structure ClosedOrderIdeal (X : Type*) [NormedAddCommGroup X]
    [Lattice X] [IsOrderedAddMonoid X] [BanachLattice X]
    extends OrderIdeal X where
  isClosed' : IsClosed (toOrderIdeal : Set X)

namespace ClosedOrderIdeal

variable {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [BanachLattice X]

instance : SetLike (ClosedOrderIdeal X) X where
  coe J := J.toOrderIdeal
  coe_injective p q h := by
    cases p; cases q; congr
    exact SetLike.coe_injective h

/-- A closed order ideal is closed as a subset of `X`. -/
theorem isClosed (J : ClosedOrderIdeal X) : IsClosed (J : Set X) :=
  J.isClosed'

/-- Closed order ideals form a partial order under inclusion. -/
instance : PartialOrder (ClosedOrderIdeal X) :=
  .ofSetLike (ClosedOrderIdeal X) X

/-- The intersection of two closed order ideals is a closed order ideal. -/
def inf (J₁ J₂ : ClosedOrderIdeal X) : ClosedOrderIdeal X where
  toOrderIdeal := J₁.toOrderIdeal ⊓ J₂.toOrderIdeal
  isClosed' := J₁.isClosed.inter J₂.isClosed

/-- **Norm-bounded decomposition** in the sum of two ideals of a normed vector
lattice: every element of `J₁ + J₂` splits as `z = a + b` with `a ∈ J₁`,
`b ∈ J₂` and `‖a‖ ≤ ‖z‖`, `‖b‖ ≤ ‖z‖`. -/
private theorem exists_sum_decomp_norm (J₁ J₂ : OrderIdeal X) {z : X}
    (hz : z ∈ J₁.toSubmodule + J₂.toSubmodule) :
    ∃ a b : X, a ∈ J₁ ∧ b ∈ J₂ ∧ a + b = z ∧ ‖a‖ ≤ ‖z‖ ∧ ‖b‖ ≤ ‖z‖ := by
  obtain ⟨a, b, ha, hb, hsum, habs_a, habs_b⟩ := OrderIdeal.exists_sum_decomp J₁ J₂ hz
  refine ⟨a, b, ha, hb, hsum, ?_, ?_⟩
  · rw [← norm_abs_eq_norm z]; exact norm_le_norm_of_abs_le_abs (by rwa [abs_abs])
  · rw [← norm_abs_eq_norm z]; exact norm_le_norm_of_abs_le_abs (by rwa [abs_abs])

/-- The sum of two closed order ideals in a Banach lattice is again closed. -/
theorem isClosed_sum {J₁ J₂ : OrderIdeal X}
    (h₁ : IsClosed (J₁ : Set X)) (h₂ : IsClosed (J₂ : Set X)) :
    IsClosed ((OrderIdeal.sum J₁ J₂ : OrderIdeal X) : Set X) := by
  rw [← isSeqClosed_iff_isClosed]
  intro z_seq z hz_mem hz_lim
  -- Extract a subsequence whose consecutive distances are summable.
  have hCauchy : CauchySeq z_seq := hz_lim.cauchySeq
  obtain ⟨φ, hφ_mono, hφ_sum⟩ :=
    Metric.exists_subseq_summable_dist_of_cauchySeq z_seq hCauchy
  -- The subsequence still converges to z.
  have hsub_lim : Filter.Tendsto (z_seq ∘ φ) Filter.atTop (nhds z) :=
    hz_lim.comp hφ_mono.tendsto_atTop
  -- Differences along the subsequence.
  set w : ℕ → X := fun k => z_seq (φ (k + 1)) - z_seq (φ k) with hw_def
  have hw_norm : ∀ k, ‖w k‖ = dist (z_seq (φ (k + 1))) (z_seq (φ k)) := by
    intro k; rw [hw_def, dist_eq_norm]
  have hw_summable : Summable fun k => ‖w k‖ := by
    simpa [hw_norm] using hφ_sum
  have hw_mem : ∀ k, w k ∈ J₁.toSubmodule + J₂.toSubmodule := fun k =>
    (J₁.toSubmodule + J₂.toSubmodule).sub_mem (hz_mem _) (hz_mem _)
  -- Decompose each difference with norm bounds.
  choose a b ha hb hab ha_norm hb_norm using
    fun k => exists_sum_decomp_norm J₁ J₂ (hw_mem k)
  have ha_summable : Summable fun k => ‖a k‖ :=
    hw_summable.of_nonneg_of_le (fun _ => norm_nonneg _) ha_norm
  have hb_summable : Summable fun k => ‖b k‖ :=
    hw_summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb_norm
  have ha_sum : Summable a := ha_summable.of_norm
  have hb_sum : Summable b := hb_summable.of_norm
  obtain ⟨A, hA_hasSum⟩ := ha_sum
  obtain ⟨B, hB_hasSum⟩ := hb_sum
  -- The partial sums of `a` live in the closed ideal `J₁`, hence so does `A`.
  have hA_mem : A ∈ J₁ :=
    h₁.mem_of_tendsto hA_hasSum
      (Filter.Eventually.of_forall fun s =>
        J₁.toSubmodule.sum_mem (fun k _ => ha k))
  have hB_mem : B ∈ J₂ :=
    h₂.mem_of_tendsto hB_hasSum
      (Filter.Eventually.of_forall fun s =>
        J₂.toSubmodule.sum_mem (fun k _ => hb k))
  -- `w k = a k + b k`, so `HasSum w (A + B)`.
  have hw_hasSum : HasSum w (A + B) := by
    have : HasSum (fun k => a k + b k) (A + B) := hA_hasSum.add hB_hasSum
    convert this using 1
    funext k; exact (hab k).symm
  -- Telescoping: partial sums of `w` tend to `z - z_seq (φ 0)`.
  have htelescope : Filter.Tendsto
      (fun n : ℕ => ∑ k ∈ Finset.range n, w k) Filter.atTop
      (nhds (z - z_seq (φ 0))) := by
    have hsum_eq : ∀ n, (∑ k ∈ Finset.range n, w k)
        = z_seq (φ n) - z_seq (φ 0) := by
      intro n
      simpa [hw_def] using
        Finset.sum_range_sub (fun k => z_seq (φ k)) n
    simp only [hsum_eq]
    exact hsub_lim.sub_const _
  -- Identify the two limits of the partial sums.
  have hAB_eq : A + B = z - z_seq (φ 0) :=
    tendsto_nhds_unique hw_hasSum.tendsto_sum_nat htelescope
  have hz_eq : z = z_seq (φ 0) + (A + B) := by rw [hAB_eq]; abel
  change z ∈ (J₁.toSubmodule + J₂.toSubmodule : Submodule ℝ X)
  rw [hz_eq]
  exact (J₁.toSubmodule + J₂.toSubmodule).add_mem
    (hz_mem (φ 0))
    (Submodule.mem_sup.mpr ⟨A, hA_mem, B, hB_mem, rfl⟩)

/-- The sum of two closed order ideals of a Banach lattice is again a closed
order ideal. -/
def sup (J₁ J₂ : ClosedOrderIdeal X) : ClosedOrderIdeal X where
  toOrderIdeal := OrderIdeal.sum J₁.toOrderIdeal J₂.toOrderIdeal
  isClosed' := isClosed_sum J₁.isClosed J₂.isClosed

/-- The arbitrary intersection of a family of closed order ideals is a closed
order ideal. -/
def sInf (S : Set (ClosedOrderIdeal X)) : ClosedOrderIdeal X where
  toOrderIdeal := InfSet.sInf ((fun J : ClosedOrderIdeal X => J.toOrderIdeal) '' S)
  isClosed' := by
    have h : ((InfSet.sInf ((fun J : ClosedOrderIdeal X => J.toOrderIdeal) '' S) :
        OrderIdeal X) : Set X) =
        ⋂ J ∈ S, (J : Set X) := by
      ext x
      rw [Set.mem_iInter₂]
      exact OrderIdeal.mem_sInf.trans
        ⟨fun h J hJ => h _ ⟨J, hJ, rfl⟩, by rintro h _ ⟨J, hJ, rfl⟩; exact h J hJ⟩
    rw [show ((InfSet.sInf ((fun J : ClosedOrderIdeal X => J.toOrderIdeal) '' S) :
        OrderIdeal X) : Set X) =
        ⋂ J ∈ S, (J : Set X) from h]
    exact isClosed_biInter fun J _ => J.isClosed

/-- Closed order ideals of a Banach lattice form a **lattice** under inclusion,
with binary meets given by intersection and binary joins by the sum. -/
instance : Lattice (ClosedOrderIdeal X) where
  sup := sup
  inf := inf
  le_sup_left := fun J₁ J₂ x hx => by
    change x ∈ OrderIdeal.sum J₁.toOrderIdeal J₂.toOrderIdeal
    exact Submodule.mem_sup.mpr ⟨x, hx, 0, J₂.toSubmodule.zero_mem, add_zero x⟩
  le_sup_right := fun J₁ J₂ x hx => by
    change x ∈ OrderIdeal.sum J₁.toOrderIdeal J₂.toOrderIdeal
    exact Submodule.mem_sup.mpr ⟨0, J₁.toSubmodule.zero_mem, x, hx, zero_add x⟩
  sup_le := fun J₁ J₂ K hJ₁ hJ₂ x hx => by
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := Submodule.mem_sup.mp hx
    exact K.toSubmodule.add_mem (hJ₁ hx₁) (hJ₂ hx₂)
  inf_le_left := fun _ _ _ hx => hx.1
  inf_le_right := fun _ _ _ hx => hx.2
  le_inf := fun _ _ _ h₁ h₂ _ hx => ⟨h₁ hx, h₂ hx⟩

/-- Closed order ideals of a Banach lattice admit **arbitrary intersections**:
they form a complete semilattice for the `⊓` operation. -/
instance : InfSet (ClosedOrderIdeal X) where
  sInf := sInf

/-- Membership in an arbitrary intersection of closed order ideals. -/
@[simp] theorem mem_sInf {S : Set (ClosedOrderIdeal X)} {x : X} :
    x ∈ (InfSet.sInf S : ClosedOrderIdeal X) ↔ ∀ J ∈ S, x ∈ J := by
  change x ∈ (InfSet.sInf ((fun J : ClosedOrderIdeal X => J.toOrderIdeal) '' S) : OrderIdeal X) ↔ _
  rw [OrderIdeal.mem_sInf]
  refine ⟨fun h J hJ => h _ ⟨J, hJ, rfl⟩, ?_⟩
  rintro h _ ⟨J, hJ, rfl⟩; exact h J hJ

/-- The underlying submodule of a binary meet is the intersection of the
underlying submodules. -/
@[simp] theorem inf_toSubmodule (J₁ J₂ : ClosedOrderIdeal X) :
    (J₁ ⊓ J₂).toSubmodule = J₁.toSubmodule ⊓ J₂.toSubmodule := rfl

/-- The underlying submodule of a binary join is the sum of the underlying
submodules. -/
@[simp] theorem sup_toSubmodule (J₁ J₂ : ClosedOrderIdeal X) :
    (J₁ ⊔ J₂).toSubmodule = J₁.toSubmodule + J₂.toSubmodule := rfl

end ClosedOrderIdeal
