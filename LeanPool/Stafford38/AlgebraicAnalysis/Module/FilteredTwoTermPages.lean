/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Tactic

/-!
# Pages of a filtered two-term complex

This file constructs the `Z_r` and `B_r` subquotients for a two-term filtered
complex. The page differential is induced by the original differential on
representatives; no successor-page equivalence is part of the input.

We use a decreasing, integer-indexed filtration `G`, as obtained from an
increasing filtration `F` by `G p = F (-p)`.
-/

namespace AlgebraicAnalysis.FilteredTwoTermPages

universe u v

variable {k : Type u} [Ring k]
variable {M : Type v} [AddCommGroup M] [Module k M]

/-- A filtration-preserving two-term complex `M --f--> M`. -/
structure FilteredTwoTerm (k : Type u) (M : Type v) [Ring k]
    [AddCommGroup M] [Module k M] where
  /-- The decreasing filtration on the underlying module. -/
  G : ℤ → Submodule k M
  antitone : Antitone G
  /-- The differential of the two-term complex. -/
  f : M →ₗ[k] M
  map_le : ∀ p, (G p).map f ≤ G p

namespace FilteredTwoTerm

variable (K : FilteredTwoTerm k M)

/-- The numerator of `Z_r` in the source. -/
def cycles (r : ℕ) (p : ℤ) : Submodule k M :=
  K.G p ⊓ (K.G (p + r)).comap K.f

/-- The numerator of `B_r` in the target. -/
def boundaries (r : ℕ) (p : ℤ) : Submodule k M :=
  (K.G p ⊓ (K.G (p - r + 1)).map K.f) ⊔ K.G (p + 1)

theorem next_le (p : ℤ) : K.G (p + 1) ≤ K.G p :=
  K.antitone (by omega)

theorem boundaries_le (r : ℕ) (p : ℤ) : K.boundaries r p ≤ K.G p := by
  apply sup_le
  · exact inf_le_left
  · exact K.next_le p

/-- The actual source page.  Using the intersection numerator gives the
canonical model
`(G^p ∩ f⁻¹G^{p+r}) / (G^{p+1} ∩ f⁻¹G^{p+r})`, equivalent to the displayed
`(intersection + G^{p+1})/G^{p+1}` formula. -/
abbrev SourcePage (r : ℕ) (p : ℤ) :=
  K.cycles r p ⧸ (K.G (p + 1)).comap (K.cycles r p).subtype

/-- The actual target page `G^p/B_r`. -/
abbrev TargetPage (r : ℕ) (p : ℤ) :=
  K.G p ⧸ (K.boundaries r p).comap (K.G p).subtype

-- Explicit instances also resolve these groups inside dependent direct sums.
instance sourcePageAddCommGroup (r : ℕ) (p : ℤ) : AddCommGroup (K.SourcePage r p) :=
  inferInstanceAs (AddCommGroup
    (K.cycles r p ⧸ (K.G (p + 1)).comap (K.cycles r p).subtype))

instance targetPageAddCommGroup (r : ℕ) (p : ℤ) : AddCommGroup (K.TargetPage r p) :=
  inferInstanceAs (AddCommGroup
    (K.G p ⧸ (K.boundaries r p).comap (K.G p).subtype))

private def restrictedDrop (r : ℕ) (p : ℤ) :
    K.cycles r p →ₗ[k] K.G (p + r) :=
  (K.f.comp (K.cycles r p).subtype).codRestrict (K.G (p + r))
    (fun x => x.property.2)

private theorem drop_denominator (r : ℕ) (p : ℤ) :
    (K.G (p + 1)).comap (K.cycles r p).subtype ≤
      ((K.boundaries r (p + r)).comap (K.G (p + r)).subtype).comap
        (K.restrictedDrop r p) := by
  intro x hx
  change K.f (x : M) ∈ K.boundaries r (p + r)
  apply Submodule.mem_sup.mpr
  refine ⟨K.f (x : M), ⟨x.property.2, ?_⟩, 0, Submodule.zero_mem _, by simp⟩
  refine ⟨x, ?_, ?_⟩
  · simpa using hx
  rfl

/-- The page differential, formed by applying `f` to a representative. -/
def drop (r : ℕ) (p : ℤ) :
    K.SourcePage r p →ₗ[k] K.TargetPage r (p + r) :=
  Submodule.mapQ _ _ (K.restrictedDrop r p) (K.drop_denominator r p)

/-- Representative formula for the page differential. -/
@[simp]
theorem drop_mk (r : ℕ) (p : ℤ) (x : K.cycles r p) :
    K.drop r p (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (K.restrictedDrop r p x) := rfl

/-- Cycle numerators decrease from page `r` to page `r+1`. -/
theorem cycles_succ_le (r : ℕ) (p : ℤ) :
    K.cycles (r + 1) p ≤ K.cycles r p := by
  intro x hx
  exact ⟨hx.1, K.antitone (by push_cast; omega) hx.2⟩

/-- Boundary numerators increase from page `r` to page `r+1`. -/
theorem boundaries_le_succ (r : ℕ) (p : ℤ) :
    K.boundaries r p ≤ K.boundaries (r + 1) p := by
  apply sup_le
  · apply le_sup_of_le_left
    intro x hx
    refine ⟨hx.1, ?_⟩
    rcases hx.2 with ⟨z, hz, rfl⟩
    refine ⟨z, K.antitone (by push_cast; omega) hz, rfl⟩
  · exact le_sup_of_le_right le_rfl

/-- A representative in `Z_{r+1}` is killed by the `r`-page differential. -/
theorem drop_mk_eq_zero_of_mem_cycles_succ (r : ℕ) (p : ℤ)
    (x : K.cycles r p) (hx : (x : M) ∈ K.cycles (r + 1) p) :
    K.drop r p (Submodule.Quotient.mk x) = 0 := by
  rw [K.drop_mk]
  rw [Submodule.Quotient.mk_eq_zero]
  change K.f (x : M) ∈ K.boundaries r (p + r)
  have hind : p + (r + 1 : ℕ) = p + (r : ℕ) + 1 := by
    push_cast
    omega
  exact Submodule.mem_sup.mpr
    ⟨0, Submodule.zero_mem _, K.f (x : M), (hind ▸ hx.2), by simp⟩

/-- Conversely, a representative killed by `d_r` can be changed by an
element of `G^{p+1}` to a representative in `Z_{r+1}`. -/
theorem exists_cycles_succ_rep_of_drop_mk_eq_zero (r : ℕ) (p : ℤ)
    (x : K.cycles r p) (hx : K.drop r p (Submodule.Quotient.mk x) = 0) :
    ∃ z ∈ K.G (p + 1), (x : M) - z ∈ K.cycles (r + 1) p := by
  rw [K.drop_mk, Submodule.Quotient.mk_eq_zero] at hx
  rcases Submodule.mem_sup.mp hx with ⟨a, ha, e, he, hsum⟩
  rcases ha.2 with ⟨z, hz, rfl⟩
  change K.f z + e = K.f (x : M) at hsum
  refine ⟨z, ?_, ?_⟩
  · simpa using hz
  refine ⟨Submodule.sub_mem _ x.property.1 (K.next_le p (by simpa using hz)), ?_⟩
  have hind : p + (r + 1 : ℕ) = p + (r : ℕ) + 1 := by
    push_cast
    omega
  rw [hind]
  have hfe : K.f ((x : M) - z) = e := by
    rw [map_sub, ← hsum]
    simp
  change K.f ((x : M) - z) ∈ K.G (p + (r : ℤ) + 1)
  rw [hfe]
  exact he

/-- Every new boundary representative is a drop plus a lower-filtration term. -/
theorem mem_boundaries_succ_rep (r : ℕ) (p : ℤ)
    {y : M} (hy : y ∈ K.boundaries (r + 1) p) :
    ∃ z ∈ K.G (p - r), ∃ e ∈ K.G (p + 1), y = K.f z + e := by
  rcases Submodule.mem_sup.mp hy with ⟨y', hy', e, he, hsum⟩
  rcases hy' with ⟨hyp, z, hz, rfl⟩
  have hind : p - ((r + 1 : ℕ) : ℤ) + 1 = p - (r : ℤ) := by
    push_cast
    omega
  exact ⟨z, hind ▸ hz,
    e, he, hsum.symm⟩

/-- Surjectivity exhausts the target boundary numerators. -/
theorem exists_mem_boundaries_of_surjective
    (hG : ∀ z : M, ∃ s : ℤ, z ∈ K.G s)
    (hf : Function.Surjective K.f) {p : ℤ} {y : M} (hy : y ∈ K.G p) :
    ∃ r : ℕ, y ∈ K.boundaries r p := by
  obtain ⟨z, rfl⟩ := hf y
  obtain ⟨s, hs⟩ := hG z
  obtain ⟨r, hr⟩ : ∃ r : ℕ, p - r + 1 ≤ s := by
    refine ⟨Int.toNat (p - s + 1), ?_⟩
    omega
  refine ⟨r, Submodule.mem_sup.mpr ?_⟩
  exact ⟨K.f z, ⟨hy, ⟨z, K.antitone hr hs, rfl⟩⟩,
    0, Submodule.zero_mem _, by simp⟩

end FilteredTwoTerm

end AlgebraicAnalysis.FilteredTwoTermPages
