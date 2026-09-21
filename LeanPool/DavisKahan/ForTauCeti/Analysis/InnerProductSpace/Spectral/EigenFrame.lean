/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/

/-
Staged for Tau Ceti: additions to `Mathlib/Analysis/InnerProductSpace/Spectrum.lean`,
next to `LinearMap.IsSymmetric.eigenvectorBasis`.
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.EigenblockSpan
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Projection.Geometry
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Spectral.Gap

/-! # Eigenfamilies and ordered eigenframes

`LinearMap.IsSymmetric.eigenvectorBasis` is *a* choice of orthonormal
eigenbasis.  When an eigenvalue is repeated the choice inside its eigenspace is
arbitrary, so a hypothesis phrased as "`V` is the span of the basis vectors at
indices `s`" silently fixes that arbitrary choice.  Statements about
*eigenvectors belonging to prescribed eigenvalues* must not do this: the
mathematics quantifies over every admissible choice.

This file supplies the two notions that keep the choice free.

* `TauCeti.IsEigenFamily T c y` — an orthonormal family `y` of `T`-eigenvectors
  with real eigenvalues `c`, with no reference to any chosen basis.
* `TauCeti.IsOrderedEigenframe hT hn e w` — the same, with the eigenvalues
  pinned to the *sorted* list at the indices `e i`.  This is the exact hypothesis
  carried by perturbation theorems that compare two operators index by index:
  `w i` may be any unit eigenvector for the `e i`-th largest eigenvalue.

The two structural facts a consumer needs are here.  An eigenfamily spans an
invariant subspace whose restricted spectrum is contained in the recorded
eigenvalue list (`IsEigenFamily.restrictedPointSpectrum_span_subset`), and — the
point of the file — a *gap-separated* ordered eigenframe spans the canonical
`spanIndices` block no matter which eigenvectors were chosen
(`IsOrderedEigenframe.span_eq_spanIndices`).  So a spectral gap makes the block
canonical, and without one it genuinely is not.

## Main results

* `TauCeti.IsEigenFamily.restrictedPointSpectrum_span_subset`: the eigenvalues
  carried by the span are among the recorded ones.
* `TauCeti.IsOrderedEigenframe.span_eq_spanIndices`: under a population gap
  separating `Set.range e` from its complement, the span is the canonical block.
* `TauCeti.IsOrderedEigenframe.pointInternalGap_span`: the same hypotheses give the
  intrinsic `PointInternalGap` used by the residual estimates.
-/

public section

open Module (finrank)
open Module.End (eigenspace)
open scoped InnerProductSpace

namespace TauCeti

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **An orthonormal family of eigenvectors** of `T`, with the real eigenvalue
of `y i` recorded as `c i`.  No basis is chosen and no ordering is assumed, so
the notion is stable under an arbitrary rotation inside a repeated
eigenspace. -/
structure IsEigenFamily {ι : Type*} (T : E →ₗ[𝕜] E) (c : ι → ℝ) (y : ι → E) : Prop where
  /-- The family is orthonormal. -/
  orthonormal : Orthonormal 𝕜 y
  /-- Each member is an eigenvector for the recorded real eigenvalue. -/
  apply_eq : ∀ i, T (y i) = (c i : 𝕜) • y i

namespace IsEigenFamily

variable {ι : Type*} {T : E →ₗ[𝕜] E} {c : ι → ℝ} {y : ι → E}

/-- The span of an eigenfamily is invariant. -/
theorem isInvariant_span (h : IsEigenFamily T c y) :
    IsInvariant T (Submodule.span 𝕜 (Set.range y)) := by
  intro x hx
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨i, rfl⟩
    rw [h.apply_eq i]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb; rw [map_add]; exact Submodule.add_mem _ ha hb
  · intro a b _ hb; rw [map_smul]; exact Submodule.smul_mem _ _ hb

/-- Every recorded eigenvalue is carried by the span. -/
theorem eigenvalue_mem_restrictedPointSpectrum (h : IsEigenFamily T c y) (i : ι) :
    c i ∈ restrictedPointSpectrum T (Submodule.span 𝕜 (Set.range y)) :=
  mem_restrictedPointSpectrum (Submodule.subset_span ⟨i, rfl⟩) (h.orthonormal.ne_zero i)
    (h.apply_eq i)

/-- The span of an eigenfamily has the dimension of its index type. -/
theorem finrank_span [Fintype ι] (h : IsEigenFamily T c y) :
    finrank 𝕜 (Submodule.span 𝕜 (Set.range y)) = Fintype.card ι :=
  finrank_span_eq_card h.orthonormal.linearIndependent

/-- **The span of an eigenfamily carries no other eigenvalues.**  An eigenvector
of `T` lying in `span (range y)` has one of the recorded eigenvalues: testing it
against `y i` multiplies the coordinate by `c i` on one side and by the
eigenvalue on the other, so every coordinate of a vector with a new eigenvalue
vanishes and the vector is `0`.

This is what makes an eigenframe hypothesis usable as a *spectral* hypothesis:
`PointInternalGap` quantifies over `restrictedPointSpectrum`, which a caller can only
control through a statement of this kind. -/
theorem restrictedPointSpectrum_span_subset [Finite ι] [FiniteDimensional 𝕜 E]
    (h : IsEigenFamily T c y) (hT : T.IsSymmetric) :
    restrictedPointSpectrum T (Submodule.span 𝕜 (Set.range y)) ⊆ Set.range c := by
  classical
  have _ : Fintype ι := Fintype.ofFinite ι
  intro lam hlam
  obtain ⟨x, hxU, hx0, hxEig⟩ := mem_restrictedPointSpectrum_iff.mp hlam
  by_contra hnot
  -- Every coordinate of `x` against the family vanishes.
  have hcoord : ∀ i, ⟪y i, x⟫_𝕜 = 0 := by
    intro i
    have hleft : ⟪y i, T x⟫_𝕜 = (c i : 𝕜) * ⟪y i, x⟫_𝕜 := by
      rw [← hT (y i) x, h.apply_eq i, inner_smul_left, RCLike.conj_ofReal]
    have hright : ⟪y i, T x⟫_𝕜 = (lam : 𝕜) * ⟪y i, x⟫_𝕜 := by
      rw [hxEig, inner_smul_right]
    have hne : (c i : 𝕜) - (lam : 𝕜) ≠ 0 := by
      simp only [sub_ne_zero, ne_eq, RCLike.ofReal_inj]
      exact fun hci => hnot ⟨i, hci⟩
    have hzero : ((c i : 𝕜) - (lam : 𝕜)) * ⟪y i, x⟫_𝕜 = 0 := by
      rw [sub_mul, ← hleft, ← hright, sub_self]
    exact (mul_eq_zero.mp hzero).resolve_left hne
  -- Hence `x` is its own projection onto the span, which is `0`.
  have hspan : Submodule.span 𝕜 (Set.range y) =
      Submodule.span 𝕜 (y '' (↑(Finset.univ : Finset ι) : Set ι)) := by simp
  have hproj : (Submodule.span 𝕜 (Set.range y)).starProjection x = x :=
    Submodule.starProjection_eq_self_iff.mpr hxU
  rw [hspan] at hproj
  rw [Orthonormal.starProjection_span_image_apply h.orthonormal Finset.univ x] at hproj
  refine hx0 ?_
  rw [← hproj]
  exact Finset.sum_eq_zero fun i _ => by rw [hcoord i, zero_smul]

end IsEigenFamily

variable [FiniteDimensional 𝕜 E] {n d : ℕ} {T : E →ₗ[𝕜] E}

/-- **An ordered eigenframe**: an orthonormal family `w` of eigenvectors of `T`
whose eigenvalues are the *sorted* eigenvalues at the indices `e i`.

This is the hypothesis a two-operator perturbation theorem must carry.  It fixes
which eigenvalues the frame belongs to — that is what makes Weyl and
Hoffman--Wielandt applicable index by index — while leaving the eigenvectors
free inside a repeated eigenspace, which is what the classical statements
quantify over. -/
def IsOrderedEigenframe (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n)
    (e : Fin d ↪ Fin n) (w : Fin d → E) : Prop :=
  IsEigenFamily T (fun i => hT.eigenvalues hn (e i)) w

/-- **The characteristic lemma.**  An ordered eigenframe is exactly an
eigenfamily whose eigenvalue list is read off the sorted spectrum; the body is
not exposed, so this is how a consumer converts. -/
theorem isOrderedEigenframe_iff {hT : T.IsSymmetric} {hn : finrank 𝕜 E = n}
    {e : Fin d ↪ Fin n} {w : Fin d → E} :
    IsOrderedEigenframe hT hn e w ↔
      IsEigenFamily T (fun i => hT.eigenvalues hn (e i)) w :=
  Iff.rfl

/-- **The canonical block is an ordered eigenframe.**  Selecting `d` indices of
the sorted eigenbasis gives one; this is the special case in which the arbitrary
choice inside a repeated eigenspace happens to be Mathlib's. -/
theorem isOrderedEigenframe_eigenvectorBasis (hT : T.IsSymmetric)
    (hn : finrank 𝕜 E = n) (e : Fin d ↪ Fin n) :
    IsOrderedEigenframe hT hn e fun i => hT.eigenvectorBasis hn (e i) :=
  isOrderedEigenframe_iff.mpr
    { orthonormal := (hT.eigenvectorBasis hn).orthonormal.comp _ e.injective
      apply_eq := fun i => hT.apply_eigenvectorBasis hn (e i) }

/-- **The sub-basis selected by a `Finset` is an eigenfamily.**  The companion
of `isOrderedEigenframe_eigenvectorBasis` for an unordered index set; it is the
form needed for the *complementary* block, whose enumeration is irrelevant. -/
theorem isEigenFamily_eigenvectorBasis_coe (hT : T.IsSymmetric)
    (hn : finrank 𝕜 E = n) (s : Finset (Fin n)) :
    IsEigenFamily T (fun k : {x // x ∈ s} => hT.eigenvalues hn ↑k)
      fun k : {x // x ∈ s} => hT.eigenvectorBasis hn ↑k where
  orthonormal := (hT.eigenvectorBasis hn).orthonormal.comp _ Subtype.val_injective
  apply_eq k := hT.apply_eigenvectorBasis hn ↑k

/-- The span of the sub-basis selected by `s` is the `spanIndices` block. -/
theorem span_range_eigenvectorBasis_coe (hT : T.IsSymmetric)
    (hn : finrank 𝕜 E = n) (s : Finset (Fin n)) :
    Submodule.span 𝕜 (Set.range fun k : {x // x ∈ s} => hT.eigenvectorBasis hn ↑k) =
      (hT.eigenvectorBasis hn).spanIndices (↑s : Set (Fin n)) := by
  rw [OrthonormalBasis.spanIndices_eq_span, Set.image_eq_range]
  rfl

namespace IsOrderedEigenframe

variable {hT : T.IsSymmetric} {hn : finrank 𝕜 E = n} {e : Fin d ↪ Fin n} {w : Fin d → E}

/-- The underlying eigenfamily. -/
theorem toIsEigenFamily (hw : IsOrderedEigenframe hT hn e w) :
    IsEigenFamily T (fun i => hT.eigenvalues hn (e i)) w :=
  isOrderedEigenframe_iff.mp hw

/-- An ordered eigenframe is orthonormal. -/
theorem orthonormal (hw : IsOrderedEigenframe hT hn e w) : Orthonormal 𝕜 w :=
  hw.toIsEigenFamily.orthonormal

/-- The eigenvalue equation of an ordered eigenframe. -/
theorem apply_eq (hw : IsOrderedEigenframe hT hn e w) (i : Fin d) :
    T (w i) = (hT.eigenvalues hn (e i) : 𝕜) • w i :=
  hw.toIsEigenFamily.apply_eq i

/-- The span of an ordered eigenframe is invariant. -/
theorem isInvariant_span (hw : IsOrderedEigenframe hT hn e w) :
    IsInvariant T (Submodule.span 𝕜 (Set.range w)) :=
  hw.toIsEigenFamily.isInvariant_span

/-- The span of an ordered eigenframe has dimension `d`. -/
theorem finrank_span (hw : IsOrderedEigenframe hT hn e w) :
    finrank 𝕜 (Submodule.span 𝕜 (Set.range w)) = d := by
  rw [hw.toIsEigenFamily.finrank_span, Fintype.card_fin]

/-- **A gap-separated ordered eigenframe spans the canonical block.**

If every selected eigenvalue is `Δ`-separated from every unselected one, with
`Δ > 0`, then the eigenvalue of `w i` has *all* of its indices inside
`Set.range e`; so `w i` lies in the corresponding eigenspace, which is the span
of those basis vectors.  A dimension count upgrades the inclusion to equality.

This is why the population side of a population-gap perturbation theorem needs
no choice datum, and — read contrapositively — why the perturbed side does. -/
theorem span_eq_spanIndices (hw : IsOrderedEigenframe hT hn e w) {Δ : ℝ} (hΔ : 0 < Δ)
    (hgap : ∀ (i : Fin d) (k : Fin n), k ∉ Set.range e →
      Δ ≤ |hT.eigenvalues hn (e i) - hT.eigenvalues hn k|) :
    Submodule.span 𝕜 (Set.range w) = (hT.eigenvectorBasis hn).spanIndices (Set.range e) := by
  classical
  have hle : Submodule.span 𝕜 (Set.range w) ≤
      (hT.eigenvectorBasis hn).spanIndices (Set.range e) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    -- The level set of `w i`'s eigenvalue sits inside the selected indices.
    have hlevel : {k : Fin n | (hT.eigenvalues hn k : 𝕜) =
        ((hT.eigenvalues hn (e i) : ℝ) : 𝕜)} ⊆ Set.range e := by
      intro k hk
      by_contra hkn
      have hkeq : hT.eigenvalues hn k = hT.eigenvalues hn (e i) := by
        exact_mod_cast hk
      have := hgap i k hkn
      rw [hkeq, sub_self, abs_zero] at this
      exact absurd this (not_le.mpr hΔ)
    have hmem : w i ∈ eigenspace T ((hT.eigenvalues hn (e i) : ℝ) : 𝕜) :=
      Module.End.mem_eigenspace_iff.mpr (hw.apply_eq i)
    rw [← hT.spanIndices_eigenvalueLevel hn] at hmem
    exact (OrthonormalBasis.spanIndices_mono _ hlevel) hmem
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  rw [hw.finrank_span]
  have hrange : (Set.range e) = ↑(Finset.univ.map e) := by
    ext k; simp
  rw [hrange, OrthonormalBasis.finrank_spanIndices]
  simp

/-- **The intrinsic gap.**  A `Δ`-separated ordered eigenframe spans a subspace
with `PointInternalGap T · Δ`: both the selected and the complementary spectrum are
read off the sorted eigenvalue list, and the index separation is exactly the
hypothesis. -/
theorem pointInternalGap_span (hw : IsOrderedEigenframe hT hn e w) {Δ : ℝ} (hΔ : 0 < Δ)
    (hgap : ∀ (i : Fin d) (k : Fin n), k ∉ Set.range e →
      Δ ≤ |hT.eigenvalues hn (e i) - hT.eigenvalues hn k|) :
    PointInternalGap T (Submodule.span 𝕜 (Set.range w)) Δ := by
  classical
  refine ⟨hw.isInvariant_span, ?_⟩
  intro lam μ hlam hμ
  -- The selected side: `lam` is one of the frame's own eigenvalues.
  obtain ⟨i, rfl⟩ := hw.toIsEigenFamily.restrictedPointSpectrum_span_subset hT hlam
  -- The complementary side: `Uᗮ` is the span of the unselected basis vectors.
  rw [hw.span_eq_spanIndices hΔ hgap] at hμ
  set S : Finset (Fin n) := Finset.univ.map e with hS
  have hrange : (Set.range e) = (↑S : Set (Fin n)) := by rw [hS]; ext k; simp
  have hcompl : ((↑S : Set (Fin n))ᶜ) = (↑(Sᶜ) : Set (Fin n)) := by ext k; simp
  rw [hrange, OrthonormalBasis.orthogonal_spanIndices, hcompl,
    ← span_range_eigenvectorBasis_coe hT hn Sᶜ] at hμ
  obtain ⟨k, rfl⟩ :=
    (isEigenFamily_eigenvectorBasis_coe hT hn Sᶜ).restrictedPointSpectrum_span_subset hT hμ
  refine hgap i ↑k ?_
  rw [hrange]
  exact fun hk => (Finset.mem_compl.mp k.2) hk

end IsOrderedEigenframe

end TauCeti
