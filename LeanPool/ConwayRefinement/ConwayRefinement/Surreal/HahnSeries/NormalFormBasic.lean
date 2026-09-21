/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov, Violeta Hernández Palacios
-/
module

public import LeanPool.ConwayRefinement.CombinatorialGames.Surreal.HahnSeries.Basic

/-!
# Ordinal-indexed presentations of surreal Hahn series

This module supplies the sequence presentation used in the Conway normal-form construction. It
follows CombinatorialGames PR #316 by Violeta Hernández Palacios, adapted as a downstream module
so the pinned dependency remains unchanged.
-/

universe u

public noncomputable section

instance {α β : Type*} {r : α → α → Prop} {s} [IsWellOrder β s] :
    Subsingleton (r ≃r s) where
  allEq f g := by
    ext x
    change f.toInitialSeg x = g.toInitialSeg x
    congr 1
    subsingleton

open Order Set

namespace SurrealHahnSeries

open Ordinal

/-- Vanishing of a coefficient is nonmembership in the support. -/
theorem notMem_support_iff {x : SurrealHahnSeries} {i : Surreal} :
    i ∉ x.support ↔ x.coeff i = 0 :=
  mem_support_iff.not_left

/-! ### Assemble Hahn series from sequences -/

/-- An ordinal-indexed strictly decreasing sequence of exponents with bundled coefficients. -/
structure TermSeq : Type (u + 1) where
  /-- The length of the sequence. -/
  protected length : Ordinal.{u}
  /-- The exponents in the sequence. -/
  protected exp : Iio length → Surreal.{u}
  /-- The coefficients in the sequence. -/
  protected coeff : Iio length → ℝ
  /-- The sequence of exponents must be strictly antitone. -/
  exp_strictAnti : StrictAnti exp
  /-- All of the coefficients must be non-zero. -/
  coeff_ne_zero (i) : coeff i ≠ 0

namespace TermSeq

attribute [simp, grind .] coeff_ne_zero

@[ext]
theorem ext {s t : TermSeq} (hl : s.length = t.length)
    (he : ∀ i (hs : i < s.length) (ht : i < t.length), s.exp ⟨i, hs⟩ = t.exp ⟨i, ht⟩)
    (hc : ∀ i (hs : i < s.length) (ht : i < t.length), s.coeff ⟨i, hs⟩ = t.coeff ⟨i, ht⟩) :
    s = t := by
  cases s
  cases t
  cases hl
  simp_rw [mk.injEq, heq_eq_eq, true_and]
  constructor <;> ext
  · exact he ..
  · exact hc ..

@[simp, grind =]
theorem exp_lt_exp_iff {s : TermSeq} {i j} : s.exp i < s.exp j ↔ j < i :=
  s.exp_strictAnti.lt_iff_gt

@[simp, grind =]
theorem exp_le_exp_iff {s : TermSeq} {i j} : s.exp i ≤ s.exp j ↔ j ≤ i :=
  s.exp_strictAnti.le_iff_ge

@[simp, grind =]
theorem exp_inj {s : TermSeq} {i j} : s.exp i = s.exp j ↔ i = j :=
  s.exp_strictAnti.injective.eq_iff

@[simps]
instance : Zero TermSeq where
  zero := .mk 0 0 0 (fun _ ↦ by simp) (by simp)

@[simp, grind =]
theorem length_eq_zero {s : TermSeq} : s.length = 0 ↔ s = 0 where
  mp h := by
    ext x _ hx
    · rw [h, zero_length]
    · simp at hx
    · simp at hx
  mpr := by simp +contextual

open Classical in
private theorem toSurrealHahnSeries_aux (o : Ordinal.{u}) (f : Iio o → Surreal.{u} × ℝ) :
    Function.support (fun i ↦ if h : ∃ o, (f o).1 = i then (f <| Classical.choose h).2 else 0) ⊆
      range (Prod.fst ∘ f) := by
  aesop

/-- Cast a sequence of terms into a `SurrealHahnSeries`. -/
@[coe]
def toSurrealHahnSeries (s : TermSeq) : SurrealHahnSeries :=
  have H := toSurrealHahnSeries_aux s.length fun i ↦ (s.exp i, s.coeff i)
  .mk _ (small_subset H) (.subset (by
    rw [wellFoundedOn_range]
    convert wellFounded_lt (α := Iio s.length)
    ext
    exact s.exp_strictAnti.lt_iff_gt
  ) H)

instance : Coe TermSeq SurrealHahnSeries where
  coe := toSurrealHahnSeries

/-- Build a `TermSeq` from a `SurrealHahnSeries`. -/
@[simps, expose]
def ofSurrealHahnSeries (x : SurrealHahnSeries) : TermSeq where
  length := x.length
  exp := (↑) ∘ x.exp
  coeff i := x.coeffIdx i
  exp_strictAnti _ := by simp
  coeff_ne_zero := by simp

@[simp, grind =]
theorem coeff_coe {s : TermSeq} (i : Iio s.length) : coeff s (s.exp i) = s.coeff i := by
  rw [toSurrealHahnSeries, coeff_mk, dif_pos ⟨i, rfl⟩]
  generalize_proofs H
  rw [s.exp_strictAnti.injective <| Classical.choose_spec H]

theorem coeff_coe_of_notMem {s : TermSeq} {x : Surreal} (h : x ∉ range s.exp) : coeff s x = 0 := by
  grind [toSurrealHahnSeries]

@[simp, grind =]
theorem support_coe (s : TermSeq) : support s = range s.exp := by
  ext i
  by_cases hi : i ∈ range s.exp
  · obtain ⟨i, rfl⟩ := hi
    simp
  · grind [coeff_coe_of_notMem hi]

/-- Order isomorphism between `Iio x.length` and the range of `x.exp`. -/
private def relIso' (s : TermSeq) : (· < · : Iio s.length → _) ≃r (· > · : range s.exp → _) := by
  refine .ofSurjective ⟨⟨fun i ↦ ⟨s.exp i, ⟨i, rfl⟩⟩, fun a b h ↦ s.exp_strictAnti.injective ?_⟩,
    s.exp_lt_exp_iff⟩ fun _ ↦ ?_ <;> aesop

/-- Order isomorphism between `Iio s.length` and the support of `x`. -/
private def relIso (s : TermSeq) : (· < · : Iio s.length → _) ≃r (· > · : support s → _) :=
  (relIso' s).trans (RelIso.subrel (· > ·) (by simp))

@[simp, grind =]
theorem length_coe (s : TermSeq) : length s = s.length := by
  rw [← lift_inj, ← type_support, ← type_lt_Iio]
  exact (relIso s).ordinalType_congr.symm

@[simp, grind =]
theorem exp_coe (s : TermSeq) (i) : exp s i = s.exp ⟨i, by simpa using i.2⟩ := by
  let e : (· < · : Iio (length (s : SurrealHahnSeries)) → _) ≃r
      (· > · : support (s : SurrealHahnSeries) → _) :=
    RelIso.ofSurjective
      { toFun := fun j ↦
          ⟨s.exp ⟨j, by simpa using j.2⟩, by
            rw [support_coe]
            exact ⟨⟨j, by simpa using j.2⟩, rfl⟩⟩
        inj' := fun a b h ↦ by
          apply_fun Subtype.val at h
          have hab :
              (⟨a, by simpa using a.2⟩ : Iio s.length) =
                ⟨b, by simpa using b.2⟩ :=
            s.exp_strictAnti.injective h
          exact Subtype.ext (congrArg (fun z : Iio s.length ↦ z.1) hab)
        map_rel_iff' := by
          intro a b
          change s.exp ⟨a, by simpa using a.2⟩ > s.exp ⟨b, by simpa using b.2⟩ ↔
            a < b
          constructor
          · intro h
            exact (s.exp_strictAnti.lt_iff_gt.mp h : _)
          · intro h
            exact s.exp_strictAnti h }
      (by
        rintro ⟨j, hj⟩
        rw [support_coe] at hj
        obtain ⟨k, rfl⟩ := hj
        exact ⟨⟨k, by rw [length_coe]; exact k.2⟩, rfl⟩)
  have hexp : exp (s : SurrealHahnSeries) = e := Subsingleton.elim _ _
  rw [hexp]
  rfl

theorem coeffIdx_coe_of_lt {s : TermSeq} {i} (h : i < s.length) :
    coeffIdx s i = s.coeff ⟨i, h⟩ := by
  rw [coeffIdx_of_lt (by simpa), exp_coe, coeff_coe]

theorem coeffIdx_coe_of_le {s : TermSeq} {i} (h : s.length ≤ i) : coeffIdx s i = 0 :=
  coeffIdx_of_le (by simpa)

@[aesop simp]
theorem coeffIdx_coe (s : TermSeq) (i) :
    coeffIdx s i = if h : i < s.length then s.coeff ⟨i, h⟩ else 0 := by
  split_ifs with h
  · exact coeffIdx_coe_of_lt h
  · exact coeffIdx_coe_of_le (le_of_not_gt h)

theorem term_coe_of_lt {s : TermSeq} {i} (h : i < s.length) :
    term s i = s.coeff ⟨i, h⟩ * ω^ s.exp ⟨i, h⟩ := by
  rw [term_of_lt (by simpa), coeffIdx_coe_of_lt, exp_coe]

theorem term_coe_of_le {s : TermSeq} {i} (h : s.length ≤ i) : term s i = 0 :=
  term_of_le (by simpa)

@[aesop simp]
theorem term_coe (s : TermSeq) (i) :
    term s i = if h : i < s.length then s.coeff ⟨i, h⟩ * ω^ s.exp ⟨i, h⟩ else 0 := by
  split_ifs with h
  · exact term_coe_of_lt h
  · exact term_coe_of_le (le_of_not_gt h)

/-- `TermSeq` and `SurrealHahnSeries` are alternate representations for the same structure. -/
@[simps!, expose]
def surrealHahnSeriesEquiv : TermSeq ≃ SurrealHahnSeries where
  toFun := toSurrealHahnSeries
  invFun := ofSurrealHahnSeries
  left_inv s := by
    ext x _ h
    · simp
    · simp
    · simp [coeffIdx_coe_of_lt h]
  right_inv x := by
    ext i
    by_cases h : i ∈ x.support
    · obtain ⟨i, hi, rfl⟩ := eq_exp_of_mem_support h
      apply (coeff_coe (s := ofSurrealHahnSeries x) i).trans
      simp
    · have hx : x.coeff i = 0 := by rwa [← notMem_support_iff]
      rw [coeff_coe_of_notMem, hx]
      simpa [ofSurrealHahnSeries]

@[simp]
theorem coe_ofSurrealHahnSeries (x : SurrealHahnSeries) : ofSurrealHahnSeries x = x :=
  surrealHahnSeriesEquiv.apply_symm_apply x

@[simp]
theorem ofSurrealHahnSeries_coe (x : TermSeq) : ofSurrealHahnSeries x = x :=
  surrealHahnSeriesEquiv.symm_apply_apply x

@[simp]
theorem coe_inj {x y : TermSeq} : (x : SurrealHahnSeries) = y ↔ x = y :=
  surrealHahnSeriesEquiv.apply_eq_iff_eq

@[simp]
theorem ofSurrealHahnSeries_inj {x y : SurrealHahnSeries} :
    ofSurrealHahnSeries x = ofSurrealHahnSeries y ↔ x = y :=
  surrealHahnSeriesEquiv.symm.apply_eq_iff_eq

end TermSeq

end SurrealHahnSeries
