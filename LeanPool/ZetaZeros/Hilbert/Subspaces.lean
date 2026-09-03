/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import LeanPool.ZetaZeros.Hilbert.L2

/-!
# The three nested subspaces

`U ⊆ V ⊆ W` inside `L²((-lam, lam))`, spanned by the twisted functions attached to the three parts
of the support. These are the spaces the Gram–Schmidt process is run on, and the nesting is what
makes an *adapted* orthonormal basis possible.

Each family is indexed by the whole of `nonRealPart Z` rather than by a choice of one point from
each conjugate pair. That is legitimate because `gz` is conjugation-invariant and `hz` is
conjugation-anti-invariant, so the span is unchanged — and it removes the enumeration
`z₁, conj z₁, …, z_k, conj z_k` that the source has to carry.
-/

@[expose] public section

namespace ZetaZeros

open MeasureTheory

variable {lam : ℝ} {eta : ℝ → ℝ}

/-- The ambient Hilbert space: square-integrable functions on the interval. -/
noncomputable abbrev L2Interval (lam : ℝ) := Lp ℂ 2 (volume.restrict (Set.Ioo (-lam) lam))

/-- The twisted function as an element of `L²`. -/
noncomputable def fzL2 (h : IsAdmissible lam eta) (z : ℂ) : L2Interval lam :=
  MemLp.toLp _ (memLp_fz h z)

/-- The even part as an element of `L²`. -/
noncomputable def gzL2 (h : IsAdmissible lam eta) (z : ℂ) : L2Interval lam :=
  MemLp.toLp _ (memLp_gz h z)

/-- The odd part as an element of `L²`. -/
noncomputable def hzL2 (h : IsAdmissible lam eta) (z : ℂ) : L2Interval lam :=
  MemLp.toLp _ (memLp_hz h z)

/-- The first subspace, spanned by the twisted functions at the multiple real points together with
the even parts at the non-real points. -/
@[zz_tag "def_U"]
noncomputable def subspaceU (h : IsAdmissible lam eta) (Z : Finset ℂ) (m : ℂ → ℕ) :
    Submodule ℂ (L2Interval lam) :=
  Submodule.span ℂ
    ((fzL2 h '' (multipleRealPart Z m : Set ℂ)) ∪ (gzL2 h '' (nonRealPart Z : Set ℂ)))

/-- The second subspace, adding the twisted functions at the simple real points. -/
@[zz_tag "def_V"]
noncomputable def subspaceV (h : IsAdmissible lam eta) (Z : Finset ℂ) (m : ℂ → ℕ) :
    Submodule ℂ (L2Interval lam) :=
  Submodule.span ℂ
    ((fzL2 h '' ((simpleRealPart Z m ∪ multipleRealPart Z m : Finset ℂ) : Set ℂ))
      ∪ (gzL2 h '' (nonRealPart Z : Set ℂ)))

/-- The third subspace, adding the odd parts at the non-real points. -/
@[zz_tag "def_W"]
noncomputable def subspaceW (h : IsAdmissible lam eta) (Z : Finset ℂ) (m : ℂ → ℕ) :
    Submodule ℂ (L2Interval lam) :=
  Submodule.span ℂ
    ((fzL2 h '' ((simpleRealPart Z m ∪ multipleRealPart Z m : Finset ℂ) : Set ℂ))
      ∪ (gzL2 h '' (nonRealPart Z : Set ℂ))
      ∪ (hzL2 h '' (nonRealPart Z : Set ℂ)))

/-- The subspaces are nested: `U ≤ V`. -/
theorem subspaceU_le_subspaceV (h : IsAdmissible lam eta) (Z : Finset ℂ) (m : ℂ → ℕ) :
    subspaceU h Z m ≤ subspaceV h Z m := by
  refine Submodule.span_mono (Set.union_subset_union_left _ (Set.image_mono ?_))
  intro x hx
  simp only [Finset.coe_union, Set.mem_union]
  exact Or.inr hx

/-- The subspaces are nested: `V ≤ W`. -/
theorem subspaceV_le_subspaceW (h : IsAdmissible lam eta) (Z : Finset ℂ) (m : ℂ → ℕ) :
    subspaceV h Z m ≤ subspaceW h Z m :=
  Submodule.span_mono Set.subset_union_left

end ZetaZeros
