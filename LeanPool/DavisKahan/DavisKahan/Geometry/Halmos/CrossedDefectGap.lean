/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.BoundedOperator.Projector
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Projection.Blocks
public import LeanPool.DavisKahan.DavisKahan.BoundedOperator.Problem
public import LeanPool.DavisKahan.DavisKahan.Geometry.Halmos.GenericRotationPredicates
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.AngleGeometry
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.SeparableOrthonormal

/-! # Crossed Defect Gap -/

@[expose] public section

open TauCeti.DavisKahan.Sylvester

/-!
# Davis--Kahan 1970, standing assumption (3.5): the symmetric gap is directed

Section 3 of the paper runs under a standing assumption, printed as (3.5), that
the two crossed intersections `U ⊓ Vᗮ` and `Uᗮ ⊓ V` carry the same data.  This
module records what that assumption buys at the level of gaps:

`subspaceGap U V = directedGap U V`.

The hypothesis is `CrossedDefectsEquivalent`, the repository's *constructive*
form of (3.5) — a linear isometric identification of the two crossed defects,
not an equality of cardinals.  Nothing stronger is used, and in fact only its
qualitative shadow is consumed: one crossed defect is trivial exactly when the
other is.

## What carries the mathematics

Everything except the transfer of triviality across the identification is
generic two-subspace geometry and lives in `ForTauCeti`:

* `Submodule.directedProjectionGap_le_of_inf_orthogonal_eq_bot` — a single
  vanishing crossed intersection already reverses the directed estimate;
* `Submodule.directedProjectionGap_eq_one_of_inf_orthogonal_ne_bot` — a nonzero
  crossed intersection pins its directed gap at `1`;
* `Submodule.projectionGap_eq_directedProjectionGap_of_inf_orthogonal_eq_bot_iff`
  — the combination, through `projectionGap_eq_max_directedProjectionGap`.

## Why (3.5) is not implied by (1.5)

`Geometry/Halmos/BilateralShiftExample.lean` builds the separating pair: on
`ℓ²(ℤ)` the shift-related half-spaces satisfy (1.5) while their source crossed
defect is a line and their target crossed defect is zero.  The two directed gaps
of that pair are `1` and `0`, so `directedGap_comm_of_crossedDefectsEquivalent`
fails on it outright; that is recorded there, next to the pair, as
`directedGap_asymmetric_coordinateHalfSpace`.  The paper's own Remark, which
reads that pair as the separation of (1.5) from (3.5), is
`DavisKahan1970.remark3_2_bilateralShift_separates_dimensionHypotheses`.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan


universe u

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]

omit [CompleteSpace H] in
/-- A submodule linearly isometric to a trivial submodule is itself trivial.

Only surjectivity and linearity are used, so the isometry hypothesis is more
than needed; it is kept because `CrossedDefectsEquivalent` supplies exactly
this datum. -/
theorem eq_bot_of_linearIsometryEquiv {K L : Submodule 𝕜 H} (e : K ≃ₗᵢ[𝕜] L)
    (hK : K = ⊥) : L = ⊥ := by
  refine (Submodule.eq_bot_iff L).mpr fun x hx => ?_
  have hzero : e.symm ⟨x, hx⟩ = 0 := by
    have hmem : ((e.symm ⟨x, hx⟩ : K) : H) ∈ K := (e.symm ⟨x, hx⟩).2
    exact Subtype.ext ((Submodule.eq_bot_iff K).mp hK _ hmem)
  have hnorm : ‖(⟨x, hx⟩ : L)‖ = 0 := by
    rw [← e.symm.norm_map ⟨x, hx⟩, hzero, norm_zero]
  simpa using congrArg Subtype.val (norm_eq_zero.mp hnorm)

omit [CompleteSpace H] in
/-- **The qualitative content of (3.5).**

Under the crossed-defect equivalence the source crossed intersection `U ⊓ Vᗮ`
is trivial exactly when the target crossed intersection `Uᗮ ⊓ V` is.  This is
the only consequence of (3.5) that the gap identity consumes. -/
theorem halmosSourceDefect_eq_bot_iff_halmosTargetDefect_eq_bot
    (U V : Submodule 𝕜 H)
    (h : CrossedDefectsEquivalent U V) :
    halmosSourceDefect U V = ⊥ ↔ halmosTargetDefect U V = ⊥ := by
  obtain ⟨e⟩ := h
  exact ⟨eq_bot_of_linearIsometryEquiv e, eq_bot_of_linearIsometryEquiv e.symm⟩

/-- **Under (3.5) the two directed gaps agree.**

Either both crossed defects vanish, and each directed gap bounds the other by
`Submodule.directedProjectionGap_le_of_inf_orthogonal_eq_bot`, or neither does
and both directed gaps equal `1`.

This is the statement that fails on the bilateral-shift pair of the Remark
after Proposition 3.2, where the two sides are `1` and `0`. -/
theorem directedGap_comm_of_crossedDefectsEquivalent
    (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (h : CrossedDefectsEquivalent U V) :
    U.directedProjectionGap V = V.directedProjectionGap U :=
  U.directedProjectionGap_comm_of_inf_orthogonal_eq_bot_iff V
    (halmosSourceDefect_eq_bot_iff_halmosTargetDefect_eq_bot U V h)

/-- **Davis--Kahan 1970, the effect of standing assumption (3.5) on the gap.**

The symmetric projection gap `‖P_U - P_V‖` is the maximum of the two directed
gaps, so under (3.5) it is either one of them.  This is the identification the
paper performs silently whenever it reads a directed `sin Θ` estimate as a
statement about the maximal angle, and it replaces the equal-`finrank`
conversion that finite-dimensional consumers currently use. -/
theorem subspaceGap_eq_directedGap_of_crossedDefectsEquivalent
    (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (h : CrossedDefectsEquivalent U V) :
    U.projectionGap V = U.directedProjectionGap V :=
  U.projectionGap_eq_directedProjectionGap_of_inf_orthogonal_eq_bot_iff V
    (halmosSourceDefect_eq_bot_iff_halmosTargetDefect_eq_bot U V h)

omit [CompleteSpace H] in
/-- **In the nonacute case the crossed defect spaces are nonzero.**

Acuteness of a pair is the vanishing of both crossed intersections `U ⊓ Vᗮ` and
`Uᗮ ⊓ V`, so failing to be acute makes at least one of them nonzero; the
identification supplied by (3.5) then transports that to the source defect. -/
theorem halmosSourceDefect_ne_bot_of_not_isAcute
    (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hdefect : CrossedDefectsEquivalent U V) (hnonacute : ¬ TauCeti.IsAcute U V) :
    halmosSourceDefect U V ≠ ⊥ := by
  intro hbot
  exact hnonacute (TauCeti.isAcute_iff_inf_orthogonal_eq_bot.mpr
    ⟨hbot, (halmosSourceDefect_eq_bot_iff_halmosTargetDefect_eq_bot U V hdefect).mp hbot⟩)

omit [CompleteSpace H] in
/-- **An acute pair satisfies the crossed-dimension condition (3.5).**

Acuteness says exactly that neither crossed intersection contains a nonzero
vector: a vector of `U` killed by `P_V` must be zero, and symmetrically.  Both
`halmosSourceDefect` and `halmosTargetDefect` are therefore trivial, and the
identification (3.5) asks for is the one between two zero spaces.

This is the discharge Section 4 needs for the Proposition 4.4 counterexample.
That counterexample is acute by construction, so it satisfies the section's
standing setup rather than escaping it -- which is what makes it a refutation of
the printed proposition rather than of a statement the paper never made. -/
theorem crossedDefectsEquivalent_of_isAcute
    (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (h : TauCeti.IsAcute U V) :
    CrossedDefectsEquivalent U V := by
  have hzero : ∀ (W : Submodule 𝕜 H) [W.HasOrthogonalProjection] (x : H),
      x ∈ Wᗮ → W.starProjection x = 0 := by
    intro W _ x hx
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero W.zero_mem ?_
    intro w hw
    simpa [inner_eq_zero_symm] using (Submodule.mem_orthogonal W x).mp hx w hw
  have hs : halmosSourceDefect U V = ⊥ := by
    refine (Submodule.eq_bot_iff _).2 ?_
    rintro x ⟨hxU, hxV⟩
    exact h.1 x hxU (hzero V x hxV)
  have ht : halmosTargetDefect U V = ⊥ := by
    refine (Submodule.eq_bot_iff _).2 ?_
    rintro y ⟨hyU, hyV⟩
    exact h.2 y hyV (hzero U y hyU)
  refine ⟨?_⟩
  rw [hs, ht]
  exact LinearIsometryEquiv.refl 𝕜 _


omit [CompleteSpace H] in
/-- **(3.5) is exactly the paper's equality of crossed defect dimensions.**

Davis and Kahan state condition (3.5) as an equality of Hilbert dimensions of
the two crossed defect spaces.  This repository represents it constructively, as
`CrossedDefectsEquivalent`: a linear isometric equivalence between them.  In
finite dimension the two readings are literally the same condition, and this is
the theorem that says so -- an isometric equivalence forces equal `finrank`, and
equal `finrank` builds one through the standard orthonormal bases.

The constructive form is the right general reading rather than a convenience.
Dimension equality of Hilbert spaces *is* the existence of an isometry between
them; stating it as data is what lets Proposition 3.2 produce a direct rotation
from it, which an equality of cardinals could not do. -/
theorem crossedDefectsEquivalent_iff_finrank_eq
    (U V : Submodule 𝕜 H)
    [FiniteDimensional 𝕜 (halmosSourceDefect U V)]
    [FiniteDimensional 𝕜 (halmosTargetDefect U V)] :
    CrossedDefectsEquivalent U V ↔
      Module.finrank 𝕜 (halmosSourceDefect U V)
        = Module.finrank 𝕜 (halmosTargetDefect U V) := by
  constructor
  · rintro ⟨e⟩
    exact e.toLinearEquiv.finrank_eq
  · intro h
    refine ⟨?_⟩
    exact (stdOrthonormalBasis 𝕜 (halmosSourceDefect U V)).repr.trans
      (((stdOrthonormalBasis 𝕜 (halmosTargetDefect U V)).reindex
        (finCongr h.symm)).repr).symm


/-! ## Condition (3.5) at the paper's separable scope

`crossedDefectsEquivalent_iff_finrank_eq` settles the finite-dimensional case, and the
repository has carried the infinite-dimensional reading as a representation convention: the
source says the two crossed defect spaces have equal Hilbert dimension, and Lean asserts a
linear isometric equivalence.

Davis and Kahan work throughout on a *separable* Hilbert space, and at that scope the reading
is a theorem rather than a convention.  Two infinite-dimensional separable Hilbert spaces are
isometric outright (`TauCeti.nonempty_linearIsometryEquiv_of_separable_of_infiniteDimensional`),
so "equal Hilbert dimension" for a separable pair means exactly: both finite-dimensional with
equal `finrank`, or both infinite-dimensional. -/

section Separable

/-- **Equal Hilbert dimension for a separable pair, spelled without cardinals.**

Both crossed defects finite-dimensional with the same `finrank`, or both
infinite-dimensional.  On a separable space this is what "the two crossed defect spaces have
equal Hilbert dimension" says. -/
def CrossedDefectsSameDimension (U V : Submodule 𝕜 H)
      : Prop :=
  (FiniteDimensional 𝕜 (halmosSourceDefect U V) ∧
      FiniteDimensional 𝕜 (halmosTargetDefect U V) ∧
      Module.finrank 𝕜 (halmosSourceDefect U V)
        = Module.finrank 𝕜 (halmosTargetDefect U V)) ∨
    (¬ FiniteDimensional 𝕜 (halmosSourceDefect U V) ∧
      ¬ FiniteDimensional 𝕜 (halmosTargetDefect U V))

/-- **Condition (3.5) is exactly equality of the crossed defects' Hilbert dimensions, on a
separable space.**

This closes the reading the repository had been carrying as a convention.  The forward
direction splits on whether the source defect is finite-dimensional and transports that across
the isometry; the converse is `crossedDefectsEquivalent_iff_finrank_eq` in the finite branch
and the separable classification in the infinite one. -/
theorem crossedDefectsEquivalent_iff_sameDimension [TopologicalSpace.SeparableSpace H]
    (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    CrossedDefectsEquivalent U V ↔ CrossedDefectsSameDimension U V := by
  classical
  constructor
  · rintro ⟨e⟩
    by_cases hfin : FiniteDimensional 𝕜 (halmosSourceDefect U V)
    · have hfin' : FiniteDimensional 𝕜 (halmosTargetDefect U V) :=
        e.toLinearEquiv.finiteDimensional
      exact Or.inl ⟨hfin, hfin', e.toLinearEquiv.finrank_eq⟩
    · refine Or.inr ⟨hfin, fun hfin' => hfin ?_⟩
      exact e.toLinearEquiv.symm.finiteDimensional
  · rintro (⟨hfin, hfin', hrank⟩ | ⟨hinf, hinf'⟩)
    · exact (crossedDefectsEquivalent_iff_finrank_eq U V).2 hrank
    · have hUcl : IsClosed ((U : Submodule 𝕜 H) : Set H) :=
        (Submodule.isComplete_coe_of_hasOrthogonalProjection U).isClosed
      have hVcl : IsClosed ((V : Submodule 𝕜 H) : Set H) :=
        (Submodule.isComplete_coe_of_hasOrthogonalProjection V).isClosed
      have hs : IsClosed ((halmosSourceDefect U V : Submodule 𝕜 H) : Set H) := by
        simpa [halmosSourceDefect] using
          hUcl.inter (Submodule.isClosed_orthogonal V)
      have ht : IsClosed ((halmosTargetDefect U V : Submodule 𝕜 H) : Set H) := by
        simpa [halmosTargetDefect] using
          (Submodule.isClosed_orthogonal U).inter hVcl
      have _ : CompleteSpace (halmosSourceDefect U V) := hs.completeSpace_coe
      have _ : CompleteSpace (halmosTargetDefect U V) := ht.completeSpace_coe
      have _ : SecondCountableTopology H := UniformSpace.secondCountable_of_separable H
      exact TauCeti.nonempty_linearIsometryEquiv_of_separable_of_infiniteDimensional hinf hinf'

end Separable

end DavisKahan
end TauCeti
