/-
Copyright (c) 2026 Jim Fowler, Dennis Sweeney. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jim Fowler, Dennis Sweeney
-/
module

public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Tactic


/-!
# Noncompact

Supporting results for the classification of compact one-dimensional manifolds.
-/

@[expose] public section

namespace OneMfld

open Set

/-- `[0, ∞) ⊆ ℝ` is not compact. -/
lemma not_isCompact_Ici_zero_real : ¬ IsCompact (Ici (0 : ℝ)) := by
  classical
  intro hIci0
  -- Open cover U n = (-∞, n)
  let U : ℕ → Set ℝ := fun n => Iio (n : ℝ)
  have hUopen : ∀ n, IsOpen (U n) := fun _ => isOpen_Iio
  -- This open cover really does cover `[0, ∞)`.
  have hCover : Ici (0 : ℝ) ⊆ ⋃ n : ℕ, U n := by
    intro x hx
    -- For any real x, there exists n : ℕ with x < n.
    obtain ⟨n, hn⟩ := exists_nat_gt x
    refine mem_iUnion.mpr ?_
    exact ⟨n, hn⟩
  -- By compactness, we get a finite subcover.
  obtain ⟨s, hs⟩ := hIci0.elim_finite_subcover U hUopen hCover
  -- s : Finset ℕ, hs : Ici (0 : ℝ) ⊆ ⋃ n ∈ s, U n

  -- Let N be the supremum (i.e., max) of the finite set s.
  let N : ℕ := s.sup id
  -- N (as a real) is in `[0, ∞)`.
  have hNmem : (N : ℝ) ∈ Ici (0 : ℝ) := by
    have : (0 : ℝ) ≤ N := by exact_mod_cast Nat.zero_le N
    exact this
  -- But N is *not* in the finite union ⋃ n ∈ s, U n.
  have hNnot : (N : ℝ) ∉ ⋃ n ∈ s, U n := by
    intro hmem
    -- From membership in the union, pick some n ∈ s with (N : ℝ) < n.
    rcases mem_iUnion.mp hmem with ⟨n, hmem'⟩
    rcases mem_iUnion.mp hmem' with ⟨hn_in_s, hmemU⟩
    -- hmemU says (N : ℝ) < n, since U n = Iio n.
    have hlt : (N : ℝ) < n := hmemU
    -- But by definition of N as sup over s, every n ∈ s satisfies n ≤ N.
    have hle : n ≤ N := by
      -- `le_sup` says `id n ≤ s.sup id` for n ∈ s.
      simpa [N] using (Finset.le_sup (s := s) (f := id) hn_in_s)
    -- So we get (N : ℝ) < n ≤ N, hence (N : ℝ) < (N : ℝ), contradiction.
    have hcontr : (N : ℝ) < (N : ℝ) :=
      lt_of_lt_of_le hlt (by exact_mod_cast hle)
    exact lt_irrefl _ hcontr
  -- But hs says the finite subcover covers `[0, ∞)`, so it must contain N.
  exact hNnot (hs hNmem)

/-- `NNReal` (the nonnegative reals with the induced topology) is not a compact space. -/
theorem not_compactSpace_NNReal : ¬ CompactSpace NNReal := by
  intro h
  -- Use the assumed instance `CompactSpace NNReal`.
  have : CompactSpace NNReal := h
  -- The whole space is compact.
  have hK : IsCompact (univ : Set NNReal) := isCompact_univ
  -- Consider the inclusion `NNReal → ℝ`.
  have hImage :
      IsCompact ((fun x : NNReal => (x : ℝ)) '' (univ : Set NNReal)) :=
    hK.image (by
      -- continuity of the inclusion
      simpa using NNReal.continuous_coe)
  -- Identify the image with `[0, ∞)` as a subset of ℝ.
  have hImage_eq : ((fun x : NNReal => (x : ℝ)) '' (univ : Set NNReal))
                    = Ici (0 : ℝ) := by
    ext x; constructor
    · -- forward direction: any `x = ↑y` with y ≥ 0 lies in `[0,∞)`
      rintro ⟨y, -, rfl⟩
      exact y.coe_nonneg
    · -- backward: any real x ≥ 0 comes from some nnreal y with y.val = x
      intro hx
      exact ⟨NNReal.mk x hx, trivial, rfl⟩
  have hIci0 : IsCompact (Ici (0 : ℝ)) := by
    simpa [hImage_eq] using hImage
  -- Contradiction with the previous lemma.
  exact not_isCompact_Ici_zero_real hIci0

end OneMfld
