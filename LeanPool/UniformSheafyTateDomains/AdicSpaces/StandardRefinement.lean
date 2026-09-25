/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/
module


/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.SheafyRing

/-!
# Standard covers from generating families (Kedlaya 1.6.5, generation side)

The **generation side** of standard-cover cofinality (Kedlaya Lemma 1.6.8 / Wedhorn
Lemma 7.54): for every valid rational base `R(D₀)` and every finite family `F`
generating the unit ideal, the **generated cover**

    { R(D₀) ∩ R(F/f) : f ∈ F }

is a `StandardCoverData` — its subordination *and covering* conditions hold
`Spa`-uniformly (pointwise in the valuation, for every choice of `A⁺`
simultaneously). The covering condition is the classical maximum argument: a
valuation cannot vanish on all of a generating family (`exists_not_vle_zero_of_span_eq_top`
— else `v(1) = 0` by the span combination and subadditivity), so among the finitely
many values `v(f)`, `f ∈ F`, a nonzero maximum exists (`exists_max_vle_of_span_eq_top`)
and `v` lies in the corresponding piece.

This populates `StandardSheafCondition`'s quantifier with the covers Kedlaya's
argument actually uses, and provides the `Spv`-level toolkit (multiplicativity,
cancellation `Spv.vle_of_vle_mul_right` — the slot-comparison engine of the
refinement lemma) on which the remaining **descent** branch of Lemma 1.6.8 (the
subordination of the product-selection pieces to an *arbitrary* rational cover, and
the elimination of the unslotted pieces — Wedhorn 7.54's normalization) will be
built; that branch is the missing API recorded in
`WedhornStandardCoverRefinement.lean` and is not on the dependency path of the
strongly noetherian theorems.
-/

@[expose] public section

noncomputable section

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-! ### `Spv`-level multiplicative toolkit -/

/-- Multiplicativity of `vle`: `v(a) ≤ v(a')` and `v(b) ≤ v(b')` give
`v(ab) ≤ v(a'b')`. -/
theorem Spv.vle_mul_of_vle_of_vle {v : Spv A} {a a' b b' : A}
    (ha : v.vle a a') (hb : v.vle b b') : v.vle (a * b) (a' * b') := by
  rw [vle_iff_canonical] at ha hb ⊢
  letI : ValuativeRel A := v.toValuativeRel
  rw [map_mul, map_mul]
  exact mul_le_mul' ha hb

/-- A product with a zero factor has value zero. -/
theorem Spv.vle_mul_zero_left {v : Spv A} {a : A} (b : A) (ha : v.vle a 0) :
    v.vle (a * b) 0 := by
  rw [vle_zero_iff_canonical] at ha ⊢
  letI : ValuativeRel A := v.toValuativeRel
  rw [map_mul, ha, zero_mul]

/-- A product of nonvanishing values does not vanish. -/
theorem Spv.not_vle_mul_zero {v : Spv A} {a b : A} (ha : ¬ v.vle a 0)
    (hb : ¬ v.vle b 0) : ¬ v.vle (a * b) 0 := by
  rw [vle_zero_iff_canonical] at ha hb ⊢
  letI : ValuativeRel A := v.toValuativeRel
  rw [map_mul]
  exact mul_ne_zero ha hb

/-- The left factor of a nonvanishing product does not vanish. -/
theorem Spv.not_vle_zero_left_of_mul {v : Spv A} {a b : A}
    (h : ¬ v.vle (a * b) 0) : ¬ v.vle a 0 :=
  fun ha => h (Spv.vle_mul_zero_left b ha)

/-- The right factor of a nonvanishing product does not vanish. -/
theorem Spv.not_vle_zero_right_of_mul {v : Spv A} {a b : A}
    (h : ¬ v.vle (a * b) 0) : ¬ v.vle b 0 :=
  fun hb => h (mul_comm a b ▸ Spv.vle_mul_zero_left a hb)

/-- **Cancellation** (the slot-comparison engine of Kedlaya Lemma 1.6.8):
`v(ac) ≤ v(bc)` and `v(c) ≠ 0` give `v(a) ≤ v(b)`. -/
theorem Spv.vle_of_vle_mul_right {v : Spv A} {a b c : A}
    (h : v.vle (a * c) (b * c)) (hc : ¬ v.vle c 0) : v.vle a b := by
  rw [vle_iff_canonical] at h ⊢
  rw [vle_zero_iff_canonical] at hc
  letI : ValuativeRel A := v.toValuativeRel
  rw [map_mul, map_mul] at h
  exact le_of_mul_le_mul_right h (lt_of_le_of_ne zero_le (Ne.symm hc))

/-! ### The maximum argument (Kedlaya 1.6.2) -/

/-- A valuation cannot vanish on a family generating the unit ideal: else the span
combination `1 = ∑ cₐ·a` and subadditivity force `v(1) = 0`. -/
theorem exists_not_vle_zero_of_span_eq_top {v : Spv A} {F : Finset A}
    (hF : Ideal.span (F : Set A) = ⊤) : ∃ f ∈ F, ¬ v.vle f 0 := by
  classical
  by_contra hall
  push Not at hall
  letI : ValuativeRel A := v.toValuativeRel
  have h1 : (1 : A) ∈ Ideal.span (F : Set A) := hF ▸ Submodule.mem_top
  obtain ⟨c, -, hc⟩ := Submodule.mem_span_finset.mp h1
  have hzero : ValuativeRel.valuation A (1 : A) = 0 := by
    rw [← hc]
    have hle : ValuativeRel.valuation A (∑ a ∈ F, c a • a) ≤ 0 := by
      refine Valuation.map_sum_le _ (fun a ha => ?_)
      have hva : ValuativeRel.valuation A a = 0 :=
        (vle_zero_iff_canonical v a).mp (hall a ha)
      rw [smul_eq_mul, map_mul, hva, mul_zero]
    exact le_antisymm hle zero_le
  exact v.not_vle_one_zero ((vle_zero_iff_canonical v 1).mpr hzero)

/-- **The maximum argument**: for every valuation and every family generating the
unit ideal there is an element of maximal — and nonzero — value. This is why the
generated cover covers every `Spa (A, A⁺)` simultaneously (Kedlaya 1.6.2). -/
theorem exists_max_vle_of_span_eq_top (v : Spv A) {F : Finset A}
    (hF : Ideal.span (F : Set A) = ⊤) :
    ∃ f ∈ F, (¬ v.vle f 0) ∧ ∀ g ∈ F, v.vle g f := by
  classical
  obtain ⟨f₀, hf₀F, hf₀⟩ := exists_not_vle_zero_of_span_eq_top (v := v) hF
  letI : ValuativeRel A := v.toValuativeRel
  obtain ⟨f, hfF, hfmax⟩ := F.exists_max_image (fun a => ValuativeRel.valuation A a)
    ⟨f₀, hf₀F⟩
  refine ⟨f, hfF, fun hf0 => hf₀ ?_, fun g hg => ?_⟩
  · rw [vle_zero_iff_canonical] at hf0 ⊢
    exact le_antisymm (hf0 ▸ hfmax f₀ hf₀F) zero_le
  · exact (vle_iff_canonical v g f).mpr (hfmax g hg)

/-! ### The generated standard cover (Kedlaya Definition 1.6.5, relative form) -/

variable [DecidableEq A] [DecidableEq (RationalLocData A)] [IsTateRing A]

/-- The pieces of the generated cover: `R(D₀) ∩ R(F/f)` for `f ∈ F` (as a named
`Finset`, keeping downstream field types small). -/
def genCoverPieces (D₀ : RationalLocData A) (hD₀ : D₀.IsRational)
    (F : Finset A) (hF : Ideal.span (F : Set A) = ⊤) : Finset (RationalLocData A) :=
  F.attach.image fun f =>
    D₀.interRational (genPieceDatum D₀.P F f.1 hF) hD₀
      (RationalLocData.isRational_of_span_eq_top hF)

theorem mem_genCoverPieces (D₀ : RationalLocData A) (hD₀ : D₀.IsRational)
    (F : Finset A) (hF : Ideal.span (F : Set A) = ⊤) {E : RationalLocData A} :
    E ∈ genCoverPieces D₀ hD₀ F hF ↔
      ∃ f : ↥F, D₀.interRational (genPieceDatum D₀.P F f.1 hF) hD₀
        (RationalLocData.isRational_of_span_eq_top hF) = E := by
  unfold genCoverPieces
  simp only [Finset.mem_image, Finset.mem_attach, true_and]

/-- The tray-condition of a generated piece specializes to a product comparison. -/
theorem genCover_tray_cond {D₀ : RationalLocData A} {hD₀ : D₀.IsRational}
    {F : Finset A} {hF : Ideal.span (F : Set A) = ⊤} {f : A} (hfF : f ∈ F)
    {v : Spv A}
    (hv : ∀ t ∈ (D₀.interRational (genPieceDatum D₀.P F f hF) hD₀
        (RationalLocData.isRational_of_span_eq_top hF)).T,
      v.vle t (D₀.interRational (genPieceDatum D₀.P F f hF) hD₀
        (RationalLocData.isRational_of_span_eq_top hF)).s)
    {a b : A} (ha : a ∈ insert D₀.s D₀.T) (hb : b ∈ insert f (F : Finset A)) :
    v.vle (a * b) (D₀.s * f) := by
  have hmem : a * b ∈ (D₀.interRational (genPieceDatum D₀.P F f hF) hD₀
      (RationalLocData.isRational_of_span_eq_top hF)).T := by
    show a * b ∈ D₀.interTray (genPieceDatum D₀.P F f hF)
    exact Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, rfl⟩
  exact hv (a * b) hmem

/-- **The generated cover is standard** (Kedlaya Definition 1.6.5/Lemma 1.6.2,
relative to a valid rational base): for a finite family `F` generating the unit
ideal, the pieces `R(D₀) ∩ R(F/f)`, `f ∈ F`, are subordinate to `R(D₀)` and cover it
**uniformly in the valuation** — the maximum argument places every valuation with the
base conditions in the piece of a maximal-value generator. Instantiating
(`StandardCoverData.toCovering`) yields a genuine `RationalCoveringData` at **every**
choice of `A⁺` at once. -/
def StandardCoverData.ofSpanTop (D₀ : RationalLocData A) (hD₀ : D₀.IsRational)
    (F : Finset A) (hF : Ideal.span (F : Set A) = ⊤) : StandardCoverData A where
  base := D₀
  covers := genCoverPieces D₀ hD₀ F hF
  base_isRational := hD₀
  covers_isRational := by
    intro E hE
    obtain ⟨f, hfeq⟩ := (mem_genCoverPieces D₀ hD₀ F hF).mp hE
    exact hfeq ▸ RationalLocData.interRational_isRational _ _ _ _
  subset_uniform := by
    intro E hE v hv
    obtain ⟨f, hfeq⟩ := (mem_genCoverPieces D₀ hD₀ F hF).mp hE
    subst hfeq
    obtain ⟨htray, hs0⟩ := hv
    -- the piece's denominator is `D₀.s * f`; neither factor vanishes
    have hs0' : ¬ v.vle (D₀.s * f) 0 := hs0
    have hf0 : ¬ v.vle f 0 := Spv.not_vle_zero_right_of_mul hs0'
    refine ⟨fun t₀ ht₀ => ?_, Spv.not_vle_zero_left_of_mul hs0'⟩
    -- `v(t₀·f) ≤ v(D₀.s·f)` from the tray; cancel `f`
    have h := genCover_tray_cond f.2 htray
      (Finset.mem_insert_of_mem ht₀) (Finset.mem_insert_self f.1 F)
    exact Spv.vle_of_vle_mul_right h hf0
  cover_uniform := by
    intro v _ hbase
    obtain ⟨f, hfF, hf0, hfmax⟩ := exists_max_vle_of_span_eq_top v hF
    refine ⟨D₀.interRational (genPieceDatum D₀.P F f hF) hD₀
        (RationalLocData.isRational_of_span_eq_top hF),
      (mem_genCoverPieces D₀ hD₀ F hF).mpr ⟨⟨f, hfF⟩, rfl⟩, ?_, ?_⟩
    · -- the tray condition: every product `a·b ≤ D₀.s·f`
      intro t ht
      obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp
        (show t ∈ ((insert D₀.s D₀.T).product (insert f F)).image
          (fun p => p.1 * p.2) from ht)
      obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
      have hva : v.vle a D₀.s := by
        rcases Finset.mem_insert.mp ha with rfl | haT
        · exact (v.vle_total _ _).elim id id
        · exact hbase.1 a haT
      have hvb : v.vle b f := by
        rcases Finset.mem_insert.mp hb with rfl | hbF
        · exact (v.vle_total _ _).elim id id
        · exact hfmax b hbF
      exact Spv.vle_mul_of_vle_of_vle hva hvb
    · -- the denominator does not vanish
      exact Spv.not_vle_mul_zero hbase.2 hf0

/-- The generated standard cover instantiates as a rational covering at every valid
`A⁺` (regression wiring: the object `StandardSheafCondition` quantifies over). -/
example [PlusSubring A] (D₀ : RationalLocData A) (hD₀ : D₀.IsRational)
    (F : Finset A) (hF : Ideal.span (F : Set A) = ⊤) : RationalCoveringData A :=
  (StandardCoverData.ofSpanTop D₀ hD₀ F hF).toCovering

end ValuationSpectrum
