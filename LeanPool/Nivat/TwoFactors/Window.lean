/-
Copyright (c) 2026 Boon Suan Ho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boon Suan Ho
-/

module

public import LeanPool.Nivat.Core.Lattice
public import LeanPool.Nivat.TwoFactors.BoundaryCounting
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic.FieldSimp

/-
Upstream: https://github.com/boonsuan/nivat
Commit: 84fe839635bdebb7d5e80c209b4f578a0c767fcf
Originally released under MIT; the upstream copyright and permission notice follow.

MIT License

Copyright (c) 2026 Boon Suan Ho

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

/-!
# Selecting a short boundary from a convex lattice window

The geometric part of Lemma 5.5 (`lem:boundary-window`) of `paper/nivat.tex`.
Integer slices of convex sets are consecutive blocks. Rational interpolation
and integer rounding give the sharp lower bound of `e - 1` sites on intermediate
rows. A low-complexity row band of least cardinality has positive discrepancy
after either nonempty endpoint is deleted; choosing its shorter endpoint gives
the boundary cost inequality. This finite minimization implements the
lemma's discrepancy-crossing selection.
-/

@[expose] public section

namespace Nivat.TwoFactors

/-- A finite set containing exactly the integer points of a convex subset of the rational plane;
this includes rectangles expressed in an arbitrary lattice basis. Lemma 5.5
(`lem:boundary-window`). -/
def LatticeConvex (D : Finset Lattice) : Prop :=
  ∃ S : Set (ℚ × ℚ), Convex ℚ S ∧ ∀ z : Lattice, z ∈ D ↔ latticeRatCast z ∈ S

/-- A subset retaining every original site between any two occupied row levels, as occurs when
extreme rows are deleted. Lemma 5.5 (`lem:boundary-window`). -/
def RowBandSubset (D₀ D : Finset Lattice) : Prop :=
  D ⊆ D₀ ∧ ∀ z ∈ D₀, (∃ u ∈ D, u.2 ≤ z.2) → (∃ v ∈ D, z.2 ≤ v.2) → z ∈ D

/-- The original finite window is a row band of itself, so it is an admissible initial window
for discrepancy selection. Lemma 5.5 (`lem:boundary-window`). -/
theorem RowBandSubset.refl (D : Finset Lattice) : RowBandSubset D D := by
  exact ⟨Finset.Subset.refl _, fun z hz _ _ => hz⟩

/-- Deleting all rows at or below a level preserves the property of retaining every original
site between occupied rows. Lemma 5.5 (`lem:boundary-window`). -/
theorem RowBandSubset.filter_gt {D₀ D : Finset Lattice} (hD : RowBandSubset D₀ D) (a : ℤ) :
    RowBandSubset D₀ (D.filter (fun z => a < z.2)) := by
  refine ⟨(Finset.filter_subset _ _).trans hD.1, ?_⟩
  intro z hz hu hv
  obtain ⟨u, hu, huz⟩ := hu
  obtain ⟨v, hv, hzv⟩ := hv
  obtain ⟨huD, hau⟩ := Finset.mem_filter.mp hu
  obtain ⟨hvD, _⟩ := Finset.mem_filter.mp hv
  exact Finset.mem_filter.mpr ⟨hD.2 z hz ⟨u, huD, huz⟩ ⟨v, hvD, hzv⟩, hau.trans_le huz⟩

/-- Deleting all rows at or above a level preserves the property of retaining every original
site between occupied rows. Lemma 5.5 (`lem:boundary-window`). -/
theorem RowBandSubset.filter_lt {D₀ D : Finset Lattice} (hD : RowBandSubset D₀ D) (b : ℤ) :
    RowBandSubset D₀ (D.filter (fun z => z.2 < b)) := by
  refine ⟨(Finset.filter_subset _ _).trans hD.1, ?_⟩
  intro z hz hu hv
  obtain ⟨u, hu, huz⟩ := hu
  obtain ⟨v, hv, hzv⟩ := hv
  obtain ⟨huD, _⟩ := Finset.mem_filter.mp hu
  obtain ⟨hvD, hvb⟩ := Finset.mem_filter.mp hv
  exact Finset.mem_filter.mpr ⟨hD.2 z hz ⟨u, huD, huz⟩ ⟨v, hvD, hzv⟩, hzv.trans_lt hvb⟩

/-- Among the row bands with nonpositive discrepancy, choose one of least cardinality; deleting
an occupied extreme row from it must give positive discrepancy. Lemma 5.5
(`lem:boundary-window`). -/
theorem exists_minimal_lowcomplex_rowBand {A : Type*} (c : Configuration A)
    (D₀ : Finset Lattice) (hlow : complexity c D₀ ≤ D₀.card) :
    ∃ D : Finset Lattice, RowBandSubset D₀ D ∧ complexity c D ≤ D.card ∧
      ∀ E : Finset Lattice, RowBandSubset D₀ E → complexity c E ≤ E.card → D.card ≤ E.card := by
  classical
  let F := D₀.powerset.filter (fun D => RowBandSubset D₀ D ∧ complexity c D ≤ D.card)
  have hF : F.Nonempty := by
    refine ⟨D₀, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.Subset.refl _), ?_⟩⟩
    exact ⟨RowBandSubset.refl D₀, hlow⟩
  obtain ⟨D, hD, hmin⟩ := Finset.exists_min_image F Finset.card hF
  obtain ⟨_, hband, hlowD⟩ := Finset.mem_filter.mp hD
  refine ⟨D, hband, hlowD, ?_⟩
  intro E hE hlE
  exact hmin E (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hE.1, hE, hlE⟩)

/-- A convex subset of the rational plane contains the full horizontal interval between two
points of the same row. Lemma 5.5 (`lem:boundary-window`). -/
theorem convex_horizontal_interval {S : Set (ℚ × ℚ)} (hS : Convex ℚ S)
    {l r t j : ℚ} (hl : (l, j) ∈ S) (hr : (r, j) ∈ S)
    (hlt : l ≤ t) (htr : t ≤ r) : (t, j) ∈ S := by
  have hline : Convex ℚ {v : ℚ | (v, j) ∈ S} := by
    intro x hx y hy a b ha hb hab
    have h := hS hx hy ha hb hab
    simpa only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, ← add_mul, hab, one_mul,
      Set.mem_ofPred_eq] using h
  exact hline.ordConnected.out hl hr ⟨hlt, htr⟩

/-- Every integer site between two sites in one row of a lattice-convex window belongs to that
window. Lemma 5.5 (`lem:boundary-window`). -/
theorem LatticeConvex.row_interval {D : Finset Lattice} (hD : LatticeConvex D)
    {l r t j : ℤ} (hl : (l, j) ∈ D) (hr : (r, j) ∈ D)
    (hlt : l ≤ t) (htr : t ≤ r) : (t, j) ∈ D := by
  obtain ⟨S, hS, hmem⟩ := hD
  apply (hmem _).mpr
  exact convex_horizontal_interval (l := (l : ℚ)) (r := (r : ℚ)) (t := (t : ℚ))
    (j := (j : ℚ)) hS ((hmem (l, j)).mp hl) ((hmem (r, j)).mp hr)
    (by exact_mod_cast hlt) (by exact_mod_cast htr)

/-- If both extreme rows have at least `e` consecutive sites, convex interpolation gives at
least `e - 1` consecutive integer sites on every intermediate row. Ceiling the interpolated
left endpoint accounts for the sharp loss of one site. Lemma 5.5 (`lem:boundary-window`). -/
theorem LatticeConvex.row_interpolation {D : Finset Lattice} (hD : LatticeConvex D)
    (a b l₀ l₁ : ℤ) (e : ℕ) (he : 0 < e) (hab : a < b)
    (hbottom : ∀ r : ℕ, r < e → (l₀ + (r : ℤ), a) ∈ D)
    (htop : ∀ r : ℕ, r < e → (l₁ + (r : ℤ), b) ∈ D)
    (j : ℤ) (haj : a ≤ j) (hjb : j ≤ b) :
    ∃ l : ℤ, ∀ r : ℕ, r < e - 1 → (l + (r : ℤ), j) ∈ D := by
  obtain ⟨S, hS, hmem⟩ := hD
  let α : ℚ := ((b : ℚ) - j) / ((b : ℚ) - a)
  let β : ℚ := ((j : ℚ) - a) / ((b : ℚ) - a)
  have hden : (0 : ℚ) < (b : ℚ) - a := by exact_mod_cast sub_pos.mpr hab
  have hα : 0 ≤ α := div_nonneg (by exact_mod_cast sub_nonneg.mpr hjb) hden.le
  have hβ : 0 ≤ β := div_nonneg (by exact_mod_cast sub_nonneg.mpr haj) hden.le
  have hsum : α + β = 1 := by dsimp [α, β]; field_simp; ring
  have hheight : α * a + β * b = j := by dsimp [α, β]; field_simp; ring
  let L : ℚ := α * l₀ + β * l₁
  have hleft : (L, (j : ℚ)) ∈ S := by
    have h := hS ((hmem _).mp (hbottom 0 he)) ((hmem _).mp (htop 0 he)) hα hβ hsum
    simpa only [latticeRatCast, Nat.cast_zero, add_zero, Prod.smul_mk, Prod.mk_add_mk,
      smul_eq_mul, hheight, L] using h
  have hright : (L + (e - 1 : ℕ), (j : ℚ)) ∈ S := by
    have h := hS ((hmem _).mp (hbottom (e - 1) (by omega)))
      ((hmem _).mp (htop (e - 1) (by omega))) hα hβ hsum
    have hw : α * ((l₀ : ℚ) + (e - 1 : ℕ)) + β * ((l₁ : ℚ) + (e - 1 : ℕ)) =
        L + (e - 1 : ℕ) := by dsimp [L]; nlinarith [hsum]
    simpa only [latticeRatCast, Int.cast_add, Int.cast_natCast, Prod.smul_mk, Prod.mk_add_mk,
      smul_eq_mul, hheight, hw] using h
  refine ⟨⌈L⌉, ?_⟩
  intro r hr
  apply (hmem _).mpr
  have hlo := Int.le_ceil L
  have hhi := Int.ceil_lt_add_one L
  have hrq : (r : ℚ) + 1 ≤ (e - 1 : ℕ) := by exact_mod_cast hr
  apply convex_horizontal_interval hS hleft hright <;>
    dsimp only [latticeRatCast] <;> push_cast <;> linarith

/-- The integer sites of an axis-aligned rectangle are exactly the integer points in the
corresponding convex rational rectangle. Lemma 5.5 (`lem:boundary-window`). -/
theorem latticeConvex_rectangle (m n : ℕ) : LatticeConvex (rectangle m n) := by
  refine ⟨Set.Icc (0 : ℚ) ((m : ℚ) - 1) ×ˢ Set.Icc (0 : ℚ) ((n : ℚ) - 1),
    (convex_Icc _ _).prod (convex_Icc _ _), ?_⟩
  intro z
  simp only [mem_rectangle, latticeRatCast, Set.mem_prod, Set.mem_Icc]
  constructor
  · rintro ⟨hx0, hxm, hy0, hyn⟩
    have hx : z.1 ≤ (m : ℤ) - 1 := by omega
    have hy : z.2 ≤ (n : ℤ) - 1 := by omega
    exact ⟨⟨by exact_mod_cast hx0, by exact_mod_cast hx⟩,
      ⟨by exact_mod_cast hy0, by exact_mod_cast hy⟩⟩
  · rintro ⟨⟨hx0, hxm⟩, ⟨hy0, hyn⟩⟩
    have hx : z.1 ≤ (m : ℤ) - 1 := by exact_mod_cast hxm
    have hy : z.2 ≤ (n : ℤ) - 1 := by exact_mod_cast hyn
    refine ⟨by exact_mod_cast hx0, by omega, by exact_mod_cast hy0, by omega⟩

/-- A compatible rational linear map pulls a lattice-convex window back to another
lattice-convex window. The membership equation records the actual preimage in the chosen
basis. Lemma 5.5 (`lem:boundary-window`). -/
theorem LatticeConvex.linear_preimage {D₀ D : Finset Lattice} (hD₀ : LatticeConvex D₀)
    (φ : Lattice → Lattice) (L : (ℚ × ℚ) →ₗ[ℚ] (ℚ × ℚ))
    (hcompat : ∀ z, latticeRatCast (φ z) = L (latticeRatCast z))
    (hmem : ∀ z, z ∈ D ↔ φ z ∈ D₀) : LatticeConvex D := by
  obtain ⟨S, hS, hSsites⟩ := hD₀
  refine ⟨L ⁻¹' S, hS.linear_preimage L, ?_⟩
  intro z
  rw [hmem, hSsites, hcompat]
  rfl

/-- The sites of a finite window at a fixed row level. Lemma 5.5 (`lem:boundary-window`). -/
def rowSites (D : Finset Lattice) (j : ℤ) : Finset Lattice := D.filter (fun z => z.2 = j)

/-- The horizontal integer coordinates of the sites at a fixed row level. Lemma 5.5
(`lem:boundary-window`). -/
def rowCoordinates (D : Finset Lattice) (j : ℤ) : Finset ℤ := (rowSites D j).image Prod.fst

/-- An integer is a row coordinate exactly when its paired lattice point belongs to that row of
the window. Lemma 5.5 (`lem:boundary-window`). -/
@[simp] theorem mem_rowCoordinates (D : Finset Lattice) (j i : ℤ) :
    i ∈ rowCoordinates D j ↔ (i, j) ∈ D := by
  simp only [rowCoordinates, rowSites, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨⟨x, y⟩, ⟨hz, hy⟩, hx⟩
    dsimp at hy hx
    simpa only [hx, hy] using hz
  · intro h
    exact ⟨(i, j), ⟨h, rfl⟩, rfl⟩

/-- Projection to the horizontal coordinate is injective within a fixed row and therefore
preserves its number of sites. Lemma 5.5 (`lem:boundary-window`). -/
theorem card_rowCoordinates (D : Finset Lattice) (j : ℤ) :
    (rowCoordinates D j).card = (rowSites D j).card := by
  apply Finset.card_image_iff.mpr
  intro x hx y hy hxy
  apply Prod.ext hxy
  exact (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm

/-- An occupied row of a row band retains every site between any two of its sites, by row
convexity of the original window. Lemma 5.5 (`lem:boundary-window`). -/
theorem RowBandSubset.row_interval {D₀ D : Finset Lattice} (hband : RowBandSubset D₀ D)
    (hD₀ : LatticeConvex D₀) {l r t j : ℤ}
    (hl : (l, j) ∈ D) (hr : (r, j) ∈ D) (hlt : l ≤ t) (htr : t ≤ r) :
    (t, j) ∈ D := by
  exact hband.2 (t, j) (hD₀.row_interval (hband.1 hl) (hband.1 hr) hlt htr)
    ⟨(l, j), hl, le_rfl⟩ ⟨(r, j), hr, le_rfl⟩

/-- A nonempty finite integer row with no gaps consists exactly of a consecutive block whose
length is its cardinality. Lemma 5.5 (`lem:boundary-window`). -/
theorem row_exact_block {D : Finset Lattice} (j : ℤ)
    (hrow : ∀ l r t : ℤ, (l, j) ∈ D → (r, j) ∈ D → l ≤ t → t ≤ r → (t, j) ∈ D)
    (hne : (rowCoordinates D j).Nonempty) :
    ∃ l : ℤ, ∀ i : ℤ, (i, j) ∈ D ↔
      ∃ r : ℕ, r < (rowCoordinates D j).card ∧ i = l + (r : ℤ) := by
  let R := rowCoordinates D j
  let l := R.min' hne
  let u := R.max' hne
  have hl : l ∈ R := Finset.min'_mem _ _
  have hu : u ∈ R := Finset.max'_mem _ _
  have hlu : l ≤ u := Finset.min'_le _ _ hu
  have hR : R = Finset.Icc l u := by
    ext i
    rw [Finset.mem_Icc]
    constructor
    · intro hi
      exact ⟨Finset.min'_le _ _ hi, Finset.le_max' _ _ hi⟩
    · rintro ⟨hli, hiu⟩
      exact (mem_rowCoordinates D j i).mpr (hrow l u i
        ((mem_rowCoordinates D j l).mp hl) ((mem_rowCoordinates D j u).mp hu) hli hiu)
  have hcard : (R.card : ℤ) = u + 1 - l := by
    rw [hR, Int.card_Icc]
    exact Int.toNat_of_nonneg (by omega)
  refine ⟨l, ?_⟩
  intro i
  rw [← mem_rowCoordinates]
  change i ∈ R ↔ _
  rw [hR, Finset.mem_Icc]
  constructor
  · rintro ⟨hli, hiu⟩
    have hir : ((i - l).toNat : ℤ) = i - l := Int.toNat_of_nonneg (by omega)
    refine ⟨(i - l).toNat, ?_, by omega⟩
    change (i - l).toNat < R.card
    omega
  · rintro ⟨r, hr, rfl⟩
    change r < R.card at hr
    constructor <;> omega

/-- Deleting a nonempty endpoint row from a smallest low-complexity band crosses to positive
discrepancy, so the increase in pattern count is smaller than the number of deleted sites.
Lemma 5.5 (`lem:boundary-window`), equation `eq:boundary-cost`. -/
theorem small_cost_of_minimal_rowBand_endpoint {A : Type*} (c : Configuration A)
    {D₀ D : Finset Lattice} (hband : RowBandSubset D₀ D)
    (hlow : complexity c D ≤ D.card)
    (hmin : ∀ E : Finset Lattice, RowBandSubset D₀ E → complexity c E ≤ E.card → D.card ≤ E.card)
    (a : ℤ) (hend : (∀ z ∈ D, a ≤ z.2) ∨ (∀ z ∈ D, z.2 ≤ a))
    (hne : ∃ z ∈ D, z.2 = a) :
    complexity c D < complexity c (D.filter (fun z => z.2 ≠ a)) + (rowSites D a).card := by
  let C := D.filter (fun z => z.2 ≠ a)
  have hCband : RowBandSubset D₀ C := by
    rcases hend with hlo | hhi
    · have hC : C = D.filter (fun z => a < z.2) := by
        apply Finset.filter_congr
        intro z hz
        have := hlo z hz
        omega
      rw [hC]
      exact hband.filter_gt a
    · have hC : C = D.filter (fun z => z.2 < a) := by
        apply Finset.filter_congr
        intro z hz
        have := hhi z hz
        omega
      rw [hC]
      exact hband.filter_lt a
  have hlt : C.card < D.card := by
    apply Finset.card_lt_card
    apply Finset.filter_ssubset.mpr
    obtain ⟨z, hz, hza⟩ := hne
    exact ⟨z, hz, by simpa using hza⟩
  have hpositive : C.card < complexity c C := by
    by_contra! hc
    have := hmin C hCband hc
    omega
  have hcards : (rowSites D a).card + C.card = D.card :=
    Finset.card_filter_add_card_filter_not (s := D) (p := fun z => z.2 = a)
  change complexity c D < complexity c C + (rowSites D a).card
  omega

/-- The selected window before translation and normal reflection: an extreme consecutive edge,
its interior, the boundary cost, and consecutive-block witnesses in every row. Lemma 5.5
(`lem:boundary-window`). -/
structure ShapeWindow {A : Type*} (c : Configuration A) (D₀ : Finset Lattice) where
  /-- The selected row band inside the input window. -/
  D : Finset Lattice
  /-- The interior obtained by deleting the selected extreme row. -/
  C : Finset Lattice
  /-- The lowest row of the selected band. -/
  lo : ℤ
  /-- The highest row of the selected band. -/
  hi : ℤ
  /-- The row selected for deletion. -/
  edge : ℤ
  /-- The horizontal coordinate of the first edge site. -/
  start : ℤ
  /-- The positive number of consecutive edge sites. -/
  e : ℕ
  /-- All input sites between occupied rows are retained. -/
  band : RowBandSubset D₀ D
  /-- The lower row does not exceed the upper row. -/
  ordered : lo ≤ hi
  /-- Every selected site lies between the extreme rows. -/
  bounds : ∀ z ∈ D, lo ≤ z.2 ∧ z.2 ≤ hi
  /-- The selected edge is one of the two extreme rows. -/
  edge_side : edge = lo ∨ edge = hi
  /-- The selected edge is nonempty. -/
  positive : 0 < e
  /-- The selected edge is exactly the consecutive block of length `e`. -/
  edge_exact : ∀ i : ℤ, (i, edge) ∈ D ↔ ∃ r : ℕ, r < e ∧ i = start + (r : ℤ)
  /-- The edge length agrees with its finite-set cardinality. -/
  edge_card : (rowSites D edge).card = e
  /-- The interior consists of all selected sites off the edge. -/
  interior_eq : C = D.filter (fun z => z.2 ≠ edge)
  /-- The selected band has nonpositive discrepancy. -/
  low_complexity : complexity c D ≤ D.card
  /-- The boundary pattern increase is less than the edge length. -/
  small_cost : complexity c D < complexity c C + e
  /-- Every row of the band contains `e - 1` consecutive sites. -/
  row_blocks : ∀ j : ℤ, lo ≤ j → j ≤ hi →
    ∃ l : ℤ, ∀ r : ℕ, r < e - 1 → (l + (r : ℤ), j) ∈ D

/-- A low-complexity lattice-convex window contains a row band with a shorter extreme edge whose
deletion has cost less than the edge length and leaves the required `e - 1` row blocks.
Lemma 5.5 (`lem:boundary-window`). -/
theorem exists_shapeWindow {A : Type*} (c : Configuration A) (hc : FiniteRange c)
    (D₀ : Finset Lattice) (hconv : LatticeConvex D₀)
    (hlow₀ : complexity c D₀ ≤ D₀.card) : Nonempty (ShapeWindow c D₀) := by
  obtain ⟨D, hband, hlow, hmin⟩ := exists_minimal_lowcomplex_rowBand c D₀ hlow₀
  have hD : D.Nonempty := Finset.card_pos.mp ((complexity_pos hc D).trans_le hlow)
  obtain ⟨z₀, hz₀, hlo⟩ := Finset.exists_min_image D Prod.snd hD
  obtain ⟨z₁, hz₁, hhi⟩ := Finset.exists_max_image D Prod.snd hD
  have hord : z₀.2 ≤ z₁.2 := hlo z₁ hz₁
  have hR₀ : (rowCoordinates D z₀.2).Nonempty :=
    ⟨z₀.1, (mem_rowCoordinates _ _ _).mpr hz₀⟩
  have hR₁ : (rowCoordinates D z₁.2).Nonempty :=
    ⟨z₁.1, (mem_rowCoordinates _ _ _).mpr hz₁⟩
  obtain ⟨l₀, hex₀⟩ := row_exact_block z₀.2
    (fun _ _ _ hl hr hlt htr => hband.row_interval hconv hl hr hlt htr) hR₀
  obtain ⟨l₁, hex₁⟩ := row_exact_block z₁.2
    (fun _ _ _ hl hr hlt htr => hband.row_interval hconv hl hr hlt htr) hR₁
  obtain ⟨edge, start, e, he, hside, he₀, he₁, hex, hcard⟩ :
      ∃ (edge start : ℤ) (e : ℕ), 0 < e ∧ (edge = z₀.2 ∨ edge = z₁.2) ∧
        e ≤ (rowCoordinates D z₀.2).card ∧ e ≤ (rowCoordinates D z₁.2).card ∧
        (∀ i : ℤ, (i, edge) ∈ D ↔ ∃ r : ℕ, r < e ∧ i = start + (r : ℤ)) ∧
        (rowSites D edge).card = e := by
    by_cases hn : (rowCoordinates D z₀.2).card ≤ (rowCoordinates D z₁.2).card
    · exact ⟨z₀.2, l₀, _, Finset.card_pos.mpr hR₀, Or.inl rfl, le_rfl, hn,
        hex₀, (card_rowCoordinates D z₀.2).symm⟩
    · exact ⟨z₁.2, l₁, _, Finset.card_pos.mpr hR₁, Or.inr rfl, by omega, le_rfl,
        hex₁, (card_rowCoordinates D z₁.2).symm⟩
  let C := D.filter (fun z => z.2 ≠ edge)
  have hend : (∀ z ∈ D, edge ≤ z.2) ∨ (∀ z ∈ D, z.2 ≤ edge) := by
    rcases hside with rfl | rfl
    · exact Or.inl hlo
    · exact Or.inr hhi
  have hne : ∃ z ∈ D, z.2 = edge := by
    refine ⟨(start, edge), (hex start).mpr ⟨0, he, by simp⟩, rfl⟩
  have hcost : complexity c D < complexity c C + e := by
    simpa only [C, hcard] using
      small_cost_of_minimal_rowBand_endpoint c hband hlow hmin edge hend hne
  refine ⟨⟨D, C, z₀.2, z₁.2, edge, start, e, hband, hord,
    fun z hz => ⟨hlo z hz, hhi z hz⟩, hside, he, hex, hcard, rfl, hlow, hcost, ?_⟩⟩
  intro j hjlo hjhi
  by_cases hlt : z₀.2 < z₁.2
  · obtain ⟨l, hl⟩ := hconv.row_interpolation z₀.2 z₁.2 l₀ l₁ e he hlt
      (fun r hr => hband.1 ((hex₀ _).mpr ⟨r, lt_of_lt_of_le hr he₀, rfl⟩))
      (fun r hr => hband.1 ((hex₁ _).mpr ⟨r, lt_of_lt_of_le hr he₁, rfl⟩))
      j hjlo hjhi
    refine ⟨l, fun r hr => hband.2 _ (hl r hr) ?_ ?_⟩
    · exact ⟨z₀, hz₀, hjlo⟩
    · exact ⟨z₁, hz₁, hjhi⟩
  · have hj : j = z₀.2 := by omega
    subst j
    exact ⟨l₀, fun r hr => (hex₀ _).mpr ⟨r, by omega, rfl⟩⟩

/-- At every row other than the selected extreme edge, the consecutive-block witnesses lie in
the interior. Lemma 5.5 (`lem:boundary-window`). -/
theorem ShapeWindow.interior_row_blocks {A : Type*} {c : Configuration A}
    {D₀ : Finset Lattice} (w : ShapeWindow c D₀) (j : ℤ)
    (hlo : w.lo ≤ j) (hhi : j ≤ w.hi) (hne : j ≠ w.edge) :
    ∃ l : ℤ, ∀ r : ℕ, r < w.e - 1 → (l + (r : ℤ), j) ∈ w.C := by
  obtain ⟨l, hl⟩ := w.row_blocks j hlo hhi
  refine ⟨l, fun r hr => ?_⟩
  rw [w.interior_eq]
  exact Finset.mem_filter.mpr ⟨hl r hr, hne⟩

end Nivat.TwoFactors
