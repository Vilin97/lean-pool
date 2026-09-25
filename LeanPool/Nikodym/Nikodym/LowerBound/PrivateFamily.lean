/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module


public import LeanPool.Nikodym.Nikodym.LowerBound.Lines.Basic

/-!
# Private families of lines indexed by their anchors

This file implements blueprint node **F05** of the lower-bound side of the sharp finite-field
Nikodym exponent.

A *private family* `Nikodym.LowerBound.PrivateFamily F d E` is a finite index type `E` together
with anchors `b : E → Fin d → F` and nonzero directions `v : E → Fin d → F` such that the line
`T ↦ b e + T • v e` through `b e` contains no other anchor: `b f = b e + t • v e` forces `f = e`.

The main results are

* `PrivateFamily.b_injective`: the anchor map is injective;
* `PrivateFamily.lineIdeal_ne`: distinct indices give distinct line ideals
  `λ_{ι(b e), ι(v e)} ≠ λ_{ι(b f), ι(v f)}` in `MvPolynomial (Fin d) K` for any field extension
  `K` of `F`;
* `PrivateFamily.comap` / `PrivateFamily.restrict`: every subfamily is private, with
  `PrivateFamily.card_restrict_le`;
* `PrivateFamily.anchors = b(E)` (the set `B₀` of the blueprint) with
  `PrivateFamily.card_anchors : #B₀ = Fintype.card E`;
* `PrivateFamily.filter_on_line_eq` / `PrivateFamily.card_filter_on_line`: each line of the
  family contains exactly one index of the family, namely its own, and
  `PrivateFamily.card_filter_anchors_on_line`: exactly one anchor of `B₀`.

The number `L` of lines of the blueprint is `Fintype.card E`.
-/

@[expose] public section

namespace Nikodym.LowerBound

open Finset

variable {K : Type*} [Field K] {d : ℕ}

/-- Blueprint F05: a private family of lines in `F^d`: anchors `b e`, nonzero directions `v e`,
such that the line through `b e` with direction `v e` contains no other anchor of the family. -/
structure PrivateFamily (F : Type*) [Field F] (d : ℕ) (E : Type*) [Fintype E] where
  /-- The anchors of the lines. -/
  b : E → Fin d → F
  /-- The directions of the lines. -/
  v : E → Fin d → F
  /-- Every direction is nonzero. -/
  v_ne_zero : ∀ e, v e ≠ 0
  /-- The line through `b e` with direction `v e` contains no other anchor of the family. -/
  anchor_private : ∀ e f : E, ∀ t : F, b f = b e + t • v e → f = e

namespace PrivateFamily

variable {F : Type*} [Field F] {E : Type*} [Fintype E] (P : PrivateFamily F d E)

/-- Blueprint F05: an index whose anchor lies on the line of `e` is `e` itself. -/
theorem eq_of_mem_line {e f : E} (h : ∃ t : F, P.b f = P.b e + t • P.v e) : f = e := by
  obtain ⟨t, ht⟩ := h
  exact P.anchor_private e f t ht

/-- Blueprint F05: the anchor of `e` is the unique anchor of the family on the line of `e`. -/
theorem exists_unique_anchor_on_line (e : E) : ∃! f, ∃ t : F, P.b f = P.b e + t • P.v e :=
  ⟨e, ⟨0, by rw [zero_smul, add_zero]⟩, fun _ hf ↦ P.eq_of_mem_line hf⟩

/-- Blueprint F05: the anchor map is injective. -/
theorem b_injective : Function.Injective P.b := fun e f h ↦
  (P.anchor_private e f 0 (by rw [zero_smul, add_zero, h])).symm

section LineIdeal

variable [Algebra F K]

/-- Blueprint F05: the line ideal `λ_{ι(b e), ι(v e)}` of the `e`-th line, over the extension
field `K`. -/
noncomputable def lineIdeal (e : E) : Ideal (MvPolynomial (Fin d) K) :=
  LowerBound.lineIdeal (liftPt (K := K) (P.b e)) (liftPt (P.v e))

/-- Blueprint F05: the line ideal of the `e`-th line is prime. -/
theorem lineIdeal_isPrime (e : E) : (P.lineIdeal (K := K) e).IsPrime :=
  LowerBound.lineIdeal_isPrime _ _

/-- Blueprint F05: the line ideal of the `e`-th line is proper. -/
theorem lineIdeal_ne_top (e : E) : P.lineIdeal (K := K) e ≠ ⊤ :=
  LowerBound.lineIdeal_ne_top _ _

/-- Blueprint F05: `H_{λ_e}(t) = t + 1`. -/
theorem hilbert_lineIdeal (e : E) (t : ℕ) : hilbert (P.lineIdeal (K := K) e) t = t + 1 :=
  LowerBound.hilbert_lineIdeal _ (liftPt_ne_zero (P.v_ne_zero e)) t

/-- Blueprint F05: the `e`-th line passes through its anchor. -/
theorem lineIdeal_le_pointIdeal_b (e : E) :
    P.lineIdeal (K := K) e ≤ pointIdeal (liftPt (P.b e)) :=
  lineIdeal_le_pointIdeal_self _ _

/-- Blueprint F05: the `e`-th line passes through the points `ι(b e + a • v e)`, `a : F`. -/
theorem lineIdeal_le_pointIdeal (e : E) (a : F) :
    P.lineIdeal (K := K) e ≤ pointIdeal (liftPt (P.b e + a • P.v e)) := by
  rw [liftPt_add, liftPt_smul]
  exact LowerBound.lineIdeal_le_pointIdeal _ _ _

/-- Blueprint F05: the anchor of `f` lies on the (extended) line of `e` only if `f = e`. -/
theorem eq_of_lineIdeal_le_pointIdeal {e f : E}
    (h : P.lineIdeal (K := K) e ≤ pointIdeal (liftPt (P.b f))) : f = e :=
  P.eq_of_mem_line (exists_eq_add_smul_of_lineIdeal_liftPt_le (P.v_ne_zero e) h)

/-- Blueprint F05: distinct indices give distinct line ideals. -/
theorem lineIdeal_ne {e f : E} (hef : e ≠ f) :
    LowerBound.lineIdeal (liftPt (K := K) (P.b e)) (liftPt (P.v e)) ≠
      LowerBound.lineIdeal (liftPt (P.b f)) (liftPt (P.v f)) := by
  intro heq
  refine hef (P.eq_of_lineIdeal_le_pointIdeal (K := K) ?_).symm
  change LowerBound.lineIdeal (liftPt (P.b e)) (liftPt (P.v e)) ≤ _
  rw [heq]
  exact lineIdeal_le_pointIdeal_self _ _

/-- Blueprint F05: the map `e ↦ λ_e` is injective. -/
theorem lineIdeal_injective : Function.Injective (P.lineIdeal (K := K)) := by
  intro e f h
  by_contra hef
  exact P.lineIdeal_ne hef h

end LineIdeal

section Subfamily

/-- Blueprint F05: pulling back a private family along an injective map of index types gives a
private family. -/
def comap {E' : Type*} [Fintype E'] (g : E' → E) (hg : Function.Injective g) :
    PrivateFamily F d E' where
  b := P.b ∘ g
  v := P.v ∘ g
  v_ne_zero e := P.v_ne_zero (g e)
  anchor_private e f t h := hg (P.anchor_private (g e) (g f) t h)

/-- Blueprint F05: anchors of the pulled-back family. -/
@[simp]
theorem comap_b {E' : Type*} [Fintype E'] (g : E' → E) (hg : Function.Injective g) (e : E') :
    (P.comap g hg).b e = P.b (g e) :=
  rfl

/-- Blueprint F05: directions of the pulled-back family. -/
@[simp]
theorem comap_v {E' : Type*} [Fintype E'] (g : E' → E) (hg : Function.Injective g) (e : E') :
    (P.comap g hg).v e = P.v (g e) :=
  rfl

/-- Blueprint F05: every subfamily (indexed by a finset `s` of indices) is private. -/
def restrict (s : Finset E) : PrivateFamily F d s :=
  P.comap Subtype.val Subtype.val_injective

/-- Blueprint F05: anchors of the subfamily. -/
@[simp]
theorem restrict_b (s : Finset E) (e : s) : (P.restrict s).b e = P.b e :=
  rfl

/-- Blueprint F05: directions of the subfamily. -/
@[simp]
theorem restrict_v (s : Finset E) (e : s) : (P.restrict s).v e = P.v e :=
  rfl

/-- Blueprint F05: a subfamily has at most as many lines as the family (the number of lines of
`P.restrict s` is `Fintype.card s = #s`, see `Fintype.card_coe`). -/
theorem card_restrict_le (s : Finset E) : Fintype.card s ≤ Fintype.card E := by
  rw [Fintype.card_coe]
  exact card_le_univ s

end Subfamily

section Anchors

/-- Blueprint F05: the finite set `B₀ = b(E)` of anchors of the family. -/
def anchors : Finset (Fin d → F) :=
  univ.map ⟨P.b, P.b_injective⟩

/-- Blueprint F05: membership in `B₀`. -/
theorem mem_anchors {x : Fin d → F} : x ∈ P.anchors ↔ ∃ e, P.b e = x := by
  simp [anchors]

/-- Blueprint F05: every anchor lies in `B₀`. -/
theorem b_mem_anchors (e : E) : P.b e ∈ P.anchors :=
  P.mem_anchors.mpr ⟨e, rfl⟩

/-- Blueprint F05: `#B₀ = L = Fintype.card E`. -/
theorem card_anchors : #P.anchors = Fintype.card E := by
  rw [anchors, card_map, card_univ]

/-- Blueprint F05: the indices whose anchor lies on the line of `e` form the singleton `{e}`. -/
theorem filter_on_line_eq (e : E) [DecidablePred fun f : E ↦ ∃ t : F, P.b f = P.b e + t • P.v e] :
    (univ.filter fun f : E ↦ ∃ t : F, P.b f = P.b e + t • P.v e) = {e} := by
  rw [eq_singleton_iff_unique_mem]
  refine ⟨mem_filter.mpr ⟨mem_univ e, 0, by rw [zero_smul, add_zero]⟩, fun f hf ↦ ?_⟩
  exact P.eq_of_mem_line (mem_filter.mp hf).2

/-- Blueprint F05: exactly one index of the family has its anchor on the line of `e`. -/
theorem card_filter_on_line (e : E)
    [DecidablePred fun f : E ↦ ∃ t : F, P.b f = P.b e + t • P.v e] :
    #(univ.filter fun f : E ↦ ∃ t : F, P.b f = P.b e + t • P.v e) = 1 := by
  rw [P.filter_on_line_eq e, card_singleton]

/-- Blueprint F05: the anchors of `B₀` lying on the line of `e` form the singleton `{b e}`. -/
theorem filter_anchors_on_line_eq (e : E)
    [DecidablePred fun x : Fin d → F ↦ ∃ t : F, x = P.b e + t • P.v e] :
    (P.anchors.filter fun x : Fin d → F ↦ ∃ t : F, x = P.b e + t • P.v e) = {P.b e} := by
  rw [eq_singleton_iff_unique_mem]
  refine ⟨mem_filter.mpr ⟨P.b_mem_anchors e, 0, by rw [zero_smul, add_zero]⟩, fun x hx ↦ ?_⟩
  obtain ⟨⟨f, rfl⟩, hf⟩ := (mem_filter.mp hx).imp_left P.mem_anchors.mp
  rw [P.eq_of_mem_line hf]

/-- Blueprint F05: each line of the family contains exactly one anchor of `B₀`, its own. -/
theorem card_filter_anchors_on_line (e : E)
    [DecidablePred fun x : Fin d → F ↦ ∃ t : F, x = P.b e + t • P.v e] :
    #(P.anchors.filter fun x : Fin d → F ↦ ∃ t : F, x = P.b e + t • P.v e) = 1 := by
  rw [P.filter_anchors_on_line_eq e, card_singleton]

end Anchors

end PrivateFamily

end Nikodym.LowerBound

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
