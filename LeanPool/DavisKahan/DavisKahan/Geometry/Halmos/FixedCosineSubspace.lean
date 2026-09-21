/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.BoundedOperator.Projector
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Projection.Blocks
import LeanPool.DavisKahan.DavisKahan.BoundedOperator.Problem
-- supplies `IsUniformlyAcute`, carried only by the archival
-- `proposition3_5_fixedAngle_maximal_uniformlyAcute_form` below.  It is a leaf module
-- over `ForTauCeti`, and `TwoProjections` already reaches it, so the import is explicit
-- rather than load-bearing.
import LeanPool.DavisKahan.DavisKahan.Geometry.Halmos.TwoProjections

/-! # Fixed Cosine Subspace -/
-- supplies `halmosCosineSq` and the two-projection calculus this module extends.

/-!
# The fixed-cosine eigenspace of two subspaces

Davis--Kahan 1970, Proposition 3.5, asks for the largest subspace `M` that reduces both
projections and on which every vector of `M ⊓ U` makes one fixed angle `θ` with `V`, and
every vector of `M ⊓ Uᗮ` makes that same angle with `Vᗮ`.  The answer is an eigenspace:
with `c = cos θ`, it is `ker (cos²Θ - c²)` for the Halmos cosine square
`cos²Θ = P_U P_V P_U + P_Uᗮ P_Vᗮ P_Uᗮ`.

This module owns that eigenspace and everything the maximality argument needs.  It was
extracted from the Section 3 frontier module; the mathematics is unchanged.  The extraction
is what lets `DavisKahan/Geometry/Angle/Proposition35Infinite.lean` -- which identifies this
eigenspace with the operator-angle eigenspace `Ω({θ})H` -- stop importing
the former `DavisKahan.Section3`, so no stable geometry module depends on the frontier.

## Scope

Everything here is scalar-generic: it holds over any `RCLike` field, at arbitrary dimension,
with no completeness assumption.  The recorded obstruction to real scalars was
`eigen_of_reducing_quadratic`, whose old proof ran the complex polarization identity; it is
replaced by a symmetric-operator argument that needs no complex structure.

## Two predicates, and why both

`IsPrintedFixedCosineReducingSubspace` is what Proposition 3.5(a)(b)(c) actually prints:
four conjuncts, with the angle conditions indexed by `{M ⊓ U, M ⊓ Uᗮ}`.
`IsFixedCosineReducingSubspace` is the symmetrised six-conjunct form, which also constrains
`M ⊓ V` and `M ⊓ Vᗮ`.  The two extra conjuncts are **redundant**
(`isFixedCosineReducingSubspace_of_printed`), so the eigenspace satisfies the stronger
predicate while maximality is proved against the weaker printed one -- both halves of
`proposition3_5_fixedAngle_maximal` are therefore at their strongest.

## Main results

* `fixedCosineSubspace`: the eigenspace `ker (cos²Θ - c²)`.
* `fixedCosineSubspace_isFixedCosineReducing`: it has all six properties.
* `fixedCosineSubspace_maximal`: the printed hypotheses alone put `M` inside it.
* `proposition3_5_fixedAngle_maximal`: the bundled Proposition 3.5 maximality clause.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan

universe u

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
variable (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection]
  [V.HasOrthogonalProjection]

/-- A subspace on which both projections reduce and every nonzero vector of
each of the four blocks `M ∩ U`, `M ∩ V`, `M ∩ Uᗮ`, `M ∩ Vᗮ` makes the fixed
angle with the opposite subspace.

This is the *symmetrised* predicate, strictly stronger than the printed
`IsPrintedFixedCosineReducingSubspace` of Proposition 3.5(a)(b)(c).  An earlier
docstring here claimed the two extra conjuncts were forced, because a nonzero
vector of the exterior `Uᗮ ⊓ Vᗮ` was said to satisfy the printed conditions
*vacuously*.  That is false: such a vector lies in `Uᗮ`, so printed (c) applies
to it and already yields `‖Pᗮ_V x‖ = ‖x‖ = c * ‖x‖`, which excludes it for
`c < 1`.  The printed four conditions are in fact sufficient
(`fixedCosineSubspace_maximal`) and the two extra conjuncts are redundant
(`isFixedCosineReducingSubspace_of_printed`). -/
def IsFixedCosineReducingSubspace
    (M : Submodule 𝕜 H) (c : ℝ) : Prop :=
  (U.starProjection).Reduces M ∧
  (V.starProjection).Reduces M ∧
  (∀ x : H, x ∈ M → x ∈ U → ‖V.starProjection x‖ = c * ‖x‖) ∧
  (∀ x : H, x ∈ M → x ∈ V → ‖U.starProjection x‖ = c * ‖x‖) ∧
  (∀ x : H, x ∈ M → x ∈ Uᗮ → ‖(Vᗮ).starProjection x‖ = c * ‖x‖) ∧
  (∀ x : H, x ∈ M → x ∈ Vᗮ → ‖(Uᗮ).starProjection x‖ = c * ‖x‖)

/-- The Halmos cosine square is a symmetric operator. -/
theorem halmosCosineSq_isSymmetric : (halmosCosineSq U V).IsSymmetric := by
  intro x y
  change ⟪(U.starProjection * V.starProjection * U.starProjection +
      (Uᗮ).starProjection * (Vᗮ).starProjection *
        (Uᗮ).starProjection) x, y⟫_𝕜 = _
  change ⟪_, _⟫_𝕜 = ⟪x, (U.starProjection * V.starProjection * U.starProjection +
      (Uᗮ).starProjection * (Vᗮ).starProjection *
        (Uᗮ).starProjection) y⟫_𝕜
  simp only [add_apply, mul_apply_eq_comp, inner_add_left, inner_add_right]
  congr 1
  · calc ⟪U.starProjection (V.starProjection (U.starProjection x)), y⟫_𝕜
        = ⟪V.starProjection (U.starProjection x), U.starProjection y⟫_𝕜 :=
          U.starProjection_isSymmetric _ _
      _ = ⟪U.starProjection x, V.starProjection (U.starProjection y)⟫_𝕜 :=
          V.starProjection_isSymmetric _ _
      _ = ⟪x, U.starProjection (V.starProjection (U.starProjection y))⟫_𝕜 :=
          U.starProjection_isSymmetric _ _
  · calc ⟪(Uᗮ).starProjection ((Vᗮ).starProjection
            ((Uᗮ).starProjection x)), y⟫_𝕜
        = ⟪(Vᗮ).starProjection ((Uᗮ).starProjection x),
            (Uᗮ).starProjection y⟫_𝕜 := Uᗮ.starProjection_isSymmetric _ _
      _ = ⟪(Uᗮ).starProjection x,
            (Vᗮ).starProjection ((Uᗮ).starProjection y)⟫_𝕜 :=
          Vᗮ.starProjection_isSymmetric _ _
      _ = ⟪x, (Uᗮ).starProjection ((Vᗮ).starProjection
            ((Uᗮ).starProjection y))⟫_𝕜 := Uᗮ.starProjection_isSymmetric _ _

/-- The shifted cosine square `cos²Θ - c ^ 2` is a symmetric operator. -/
theorem halmosCosineSq_sub_smul_isSymmetric (c : ℝ) :
    (halmosCosineSq U V - (c : 𝕜) ^ 2 • (1 : H →L[𝕜] H)).IsSymmetric := by
  intro x y
  have hc : (starRingEnd 𝕜) ((c : 𝕜) ^ 2) = (c : 𝕜) ^ 2 := by
    rw [map_pow, RCLike.conj_ofReal]
  change ⟪(halmosCosineSq U V - (c : 𝕜) ^ 2 • (1 : H →L[𝕜] H)) x, y⟫_𝕜 = _
  change ⟪_, _⟫_𝕜 = ⟪x, (halmosCosineSq U V - (c : 𝕜) ^ 2 • (1 : H →L[𝕜] H)) y⟫_𝕜
  have hs : ⟪halmosCosineSq U V x, y⟫_𝕜 = ⟪x, halmosCosineSq U V y⟫_𝕜 :=
    halmosCosineSq_isSymmetric U V x y
  simp only [sub_apply, smul_apply, one_apply_eq_self, inner_sub_left,
    inner_sub_right, inner_smul_left, inner_smul_right, hc]
  rw [hs]

/-- Symmetric replacement for complex polarization: a **symmetric** bounded
operator that preserves a subspace and has vanishing quadratic form there
vanishes on it.

The previous form of this lemma assumed no symmetry and ran the complex
polarization identity, testing against `w + Complex.I • v`.  That route is
unavailable over `ℝ` — every skew-symmetric operator has vanishing quadratic
form — and it was recorded as a genuine obstruction to real scalars.  It is not
one.  With `T` symmetric the single test vector `w + T w` suffices over any
`RCLike` field: `⟪T (w + T w), w + T w⟫ = 2 * ⟪T w, T w⟫`, because `⟪T w, w⟫`
and `⟪T (T w), T w⟫` vanish by hypothesis and `⟪T (T w), w⟫ = ⟪T w, T w⟫` by
symmetry.  Symmetry is available at every call site here: the operator is
`cos²Θ - c ^ 2` (`halmosCosineSq_sub_smul_isSymmetric`). -/
theorem eigen_of_reducing_quadratic {T : H →L[𝕜] H} (hT : T.IsSymmetric)
    {W : Submodule 𝕜 H}
    (hTW : ∀ w ∈ W, T w ∈ W) (hquad : ∀ w ∈ W, ⟪T w, w⟫_𝕜 = 0)
    {w : H} (hw : w ∈ W) : T w = 0 := by
  have hqw := hquad w hw
  have hqTw := hquad (T w) (hTW w hw)
  have h1 := hquad (w + T w) (W.add_mem hw (hTW w hw))
  have hsym : ⟪T (T w), w⟫_𝕜 = ⟪T w, T w⟫_𝕜 := hT (T w) w
  rw [map_add, inner_add_left, inner_add_right, inner_add_right, hqw, hqTw,
    hsym] at h1
  have h2 : (2 : 𝕜) * ⟪T w, T w⟫_𝕜 = 0 := by linear_combination h1
  have h3 : ⟪T w, T w⟫_𝕜 = 0 := (mul_eq_zero.mp h2).resolve_left (by norm_num)
  exact inner_self_eq_zero.mp h3

/-- The Halmos cosine square is symmetric in the ordered pair: it is
`1 - (P_U - P_V) ^ 2`, invariant under swapping the projections. -/
theorem halmosCosineSq_symm :
    halmosCosineSq U V = halmosCosineSq V U := by
  rw [halmosCosineSq_eq_one_sub_projection_sub_sq U V,
    halmosCosineSq_eq_one_sub_projection_sub_sq V U]
  noncomm_ring

/-- Squared-norm quadratic form, with the real-to-complex coercion pinned to
`RCLike.ofReal`. -/
theorem inner_self_ofReal (x : H) : ⟪x, x⟫_𝕜 = (‖x‖ : 𝕜) ^ 2 :=
  inner_self_eq_norm_sq_to_K x

/-- The quadratic form of an orthogonal projection is its squared norm. -/
theorem inner_starProjection_self_eq (K : Submodule 𝕜 H)
    [K.HasOrthogonalProjection] (y : H) :
    ⟪K.starProjection y, y⟫_𝕜 = (‖K.starProjection y‖ : 𝕜) ^ 2 := by
  have hidem : K.starProjection (K.starProjection y) = K.starProjection y :=
    Submodule.starProjection_eq_self_iff.mpr (K.starProjection_apply_mem y)
  calc ⟪K.starProjection y, y⟫_𝕜
      = ⟪K.starProjection (K.starProjection y), y⟫_𝕜 := by rw [hidem]
    _ = ⟪K.starProjection y, K.starProjection y⟫_𝕜 := K.starProjection_isSymmetric _ _
    _ = (‖K.starProjection y‖ : 𝕜) ^ 2 := inner_self_eq_norm_sq_to_K _

/-- On the source subspace, the cosine-square quadratic form is `‖P_V x‖ ^ 2`. -/
theorem inner_halmosCosineSq_source (x : H) (hx : x ∈ U) :
    ⟪halmosCosineSq U V x, x⟫_𝕜 = (‖V.starProjection x‖ : 𝕜) ^ 2 := by
  have hPU : U.starProjection x = x := Submodule.starProjection_eq_self_iff.mpr hx
  have hPUc : (Uᗮ).starProjection x = 0 := by
    have hx' : Uᗮ.starProjection x = x - U.starProjection x :=
      congrArg (fun T : H →L[𝕜] H => T x) (Submodule.starProjection_orthogonal' U)
    rw [show (Uᗮ).starProjection x = Uᗮ.starProjection x from rfl, hx', hPU, sub_self]
  have hval : halmosCosineSq U V x = U.starProjection (V.starProjection x) := by
    change (U.starProjection * V.starProjection * U.starProjection
      + (Uᗮ).starProjection * (Vᗮ).starProjection
        * (Uᗮ).starProjection) x = _
    simp only [add_apply, mul_apply_eq_comp, hPU,
      hPUc, map_zero, add_zero]
  rw [hval]
  calc ⟪U.starProjection (V.starProjection x), x⟫_𝕜
      = ⟪V.starProjection x, U.starProjection x⟫_𝕜 := U.starProjection_isSymmetric _ _
    _ = ⟪V.starProjection x, x⟫_𝕜 := by rw [hPU]
    _ = (‖V.starProjection x‖ : 𝕜) ^ 2 := inner_starProjection_self_eq V x

/-- On the source complement, the cosine-square quadratic form is
`‖Pᗮ_V x‖ ^ 2`. -/
theorem inner_halmosCosineSq_source_compl (x : H) (hx : x ∈ Uᗮ) :
    ⟪halmosCosineSq U V x, x⟫_𝕜 = (‖(Vᗮ).starProjection x‖ : 𝕜) ^ 2 := by
  have hPUc : (Uᗮ).starProjection x = x :=
    Submodule.starProjection_eq_self_iff.mpr hx
  have hPU : U.starProjection x = 0 := by
    have hx' : Uᗮ.starProjection x = x - U.starProjection x :=
      congrArg (fun T : H →L[𝕜] H => T x) (Submodule.starProjection_orthogonal' U)
    rw [show (Uᗮ).starProjection x = Uᗮ.starProjection x from rfl] at hPUc
    have hUeq : U.starProjection x = x - Uᗮ.starProjection x := by rw [hx']; abel
    rw [show U.starProjection x = U.starProjection x from rfl, hUeq, hPUc, sub_self]
  have hval : halmosCosineSq U V x
      = (Uᗮ).starProjection ((Vᗮ).starProjection x) := by
    change (U.starProjection * V.starProjection * U.starProjection
      + (Uᗮ).starProjection * (Vᗮ).starProjection
        * (Uᗮ).starProjection) x = _
    simp only [add_apply, mul_apply_eq_comp, hPU,
      hPUc, map_zero, zero_add]
  rw [hval]
  calc ⟪(Uᗮ).starProjection ((Vᗮ).starProjection x), x⟫_𝕜
      = ⟪(Vᗮ).starProjection x, (Uᗮ).starProjection x⟫_𝕜 :=
        Uᗮ.starProjection_isSymmetric _ _
    _ = ⟪(Vᗮ).starProjection x, x⟫_𝕜 := by rw [hPUc]
    _ = (‖(Vᗮ).starProjection x‖ : 𝕜) ^ 2 := inner_starProjection_self_eq Vᗮ x

/-- The fixed-cosine subspace: the `c ^ 2`-eigenspace of the Halmos cosine
square `cos²Θ`.  For a singleton this eigenspace coincides with the
`{c ^ 2}`-spectral subspace, but presenting it as `ker (cos²Θ - c ^ 2)` makes
the fixed-cosine eigenvalue equation available definitionally, so no
projection-valued-measure eigenvalue extraction is needed downstream. -/
noncomputable def fixedCosineSubspace (c : ℝ) : Submodule 𝕜 H :=
  (halmosCosineSq U V - (c : 𝕜) ^ 2 • (1 : H →L[𝕜] H)).ker

/-- Membership in the fixed-cosine subspace is the eigenvalue equation. -/
theorem mem_fixedCosineSubspace (c : ℝ) (w : H) :
    w ∈ fixedCosineSubspace U V c ↔ halmosCosineSq U V w = (c : 𝕜) ^ 2 • w := by
  rw [fixedCosineSubspace, LinearMap.mem_ker]
  simp only [ContinuousLinearMap.coe_coe, sub_apply,
    smul_apply, one_apply_eq_self]
  rw [sub_eq_zero]

/-- A projection commuting with the cosine square reduces the eigenspace. -/
theorem reduces_projection_of_commute (c : ℝ) (W : Submodule 𝕜 H)
    [W.HasOrthogonalProjection]
    (hcomm : Commute (halmosCosineSq U V) (W.starProjection)) :
    (W.starProjection).Reduces (fixedCosineSubspace U V c) := by
  refine ContinuousLinearMap.IsSymmetric.reduces_of_invariant W.starProjection_isSymmetric ?_
  intro x hx
  rw [mem_fixedCosineSubspace] at hx ⊢
  have hcm := congrArg (fun T : H →L[𝕜] H => T x) hcomm.eq
  simp only [mul_apply_eq_comp] at hcm
  rw [hcm, hx, map_smul]

/-- Extract a real norm equality from a complex squared identity. -/
theorem norm_eq_from_ofReal_sq {p q c : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hc : 0 ≤ c)
    (h : (p : 𝕜) ^ 2 = (c : 𝕜) ^ 2 * (q : 𝕜) ^ 2) : p = c * q := by
  have hr : p ^ 2 = (c * q) ^ 2 := by
    have hcast : ((p ^ 2 : ℝ) : 𝕜) = (((c * q) ^ 2 : ℝ) : 𝕜) := by
      push_cast; linear_combination h
    exact_mod_cast hcast
  have hcq : 0 ≤ c * q := mul_nonneg hc hq
  calc p = Real.sqrt (p ^ 2) := (Real.sqrt_sq hp).symm
    _ = Real.sqrt ((c * q) ^ 2) := by rw [hr]
    _ = c * q := Real.sqrt_sq hcq

/-- The cosine square commutes with the target projection too. -/
theorem halmosCosineSq_commute_projection_right :
    Commute (halmosCosineSq U V) (V.starProjection) := by
  rw [halmosCosineSq_symm U V]
  exact halmosCosineSq_commute_projection V U

/-- Vector form of the cosine square on the source subspace. -/
theorem halmosCosineSq_source_apply (x : H) (hx : x ∈ U) :
    halmosCosineSq U V x = U.starProjection (V.starProjection x) := by
  have hPU : U.starProjection x = x := Submodule.starProjection_eq_self_iff.mpr hx
  have hPUc : (Uᗮ).starProjection x = 0 := by
    have hx' : Uᗮ.starProjection x = x - U.starProjection x :=
      congrArg (fun T : H →L[𝕜] H => T x) (Submodule.starProjection_orthogonal' U)
    rw [show (Uᗮ).starProjection x = Uᗮ.starProjection x from rfl, hx', hPU, sub_self]
  change (U.starProjection * V.starProjection * U.starProjection
    + (Uᗮ).starProjection * (Vᗮ).starProjection
      * (Uᗮ).starProjection) x = _
  simp only [add_apply, mul_apply_eq_comp, hPU,
    hPUc, map_zero, add_zero]

/-- Vector form of the cosine square on the source complement. -/
theorem halmosCosineSq_source_compl_apply (x : H) (hx : x ∈ Uᗮ) :
    halmosCosineSq U V x
      = (Uᗮ).starProjection ((Vᗮ).starProjection x) := by
  have hPUc : (Uᗮ).starProjection x = x :=
    Submodule.starProjection_eq_self_iff.mpr hx
  have hPU : U.starProjection x = 0 := by
    have hx' : Uᗮ.starProjection x = x - U.starProjection x :=
      congrArg (fun T : H →L[𝕜] H => T x) (Submodule.starProjection_orthogonal' U)
    rw [show (Uᗮ).starProjection x = Uᗮ.starProjection x from rfl] at hPUc
    have hUeq : U.starProjection x = x - Uᗮ.starProjection x := by rw [hx']; abel
    rw [show U.starProjection x = U.starProjection x from rfl, hUeq, hPUc, sub_self]
  change (U.starProjection * V.starProjection * U.starProjection
    + (Uᗮ).starProjection * (Vᗮ).starProjection
      * (Uᗮ).starProjection) x = _
  simp only [add_apply, mul_apply_eq_comp, hPU,
    hPUc, map_zero, zero_add]

/-- Complementary projections preserve a subspace reducing the projection. -/
theorem complementaryProjection_mem_of_reduces {W M : Submodule 𝕜 H}
    [W.HasOrthogonalProjection] (hR : (W.starProjection).Reduces M) {w : H}
    (hw : w ∈ M) : (Wᗮ).starProjection w ∈ M := by
  have hcompl : (Wᗮ).starProjection w = w - W.starProjection w :=
    congrArg (fun T : H →L[𝕜] H => T w) (Submodule.starProjection_orthogonal' W)
  rw [hcompl]
  exact M.sub_mem hw (hR.1 w hw)

/-- The cosine square preserves a subspace reducing both projections. -/
theorem halmosCosineSq_mem_of_reduces {M : Submodule 𝕜 H}
    (hRU : (U.starProjection).Reduces M) (hRV : (V.starProjection).Reduces M)
    {w : H} (hw : w ∈ M) : halmosCosineSq U V w ∈ M := by
  have hval : halmosCosineSq U V w
      = U.starProjection (V.starProjection (U.starProjection w))
        + (Uᗮ).starProjection ((Vᗮ).starProjection
            ((Uᗮ).starProjection w)) := by
    change (U.starProjection * V.starProjection * U.starProjection
      + (Uᗮ).starProjection * (Vᗮ).starProjection
        * (Uᗮ).starProjection) w = _
    simp only [add_apply, mul_apply_eq_comp]
  rw [hval]
  refine M.add_mem (hRU.1 _ (hRV.1 _ (hRU.1 _ hw))) ?_
  exact complementaryProjection_mem_of_reduces hRU
    (complementaryProjection_mem_of_reduces hRV
      (complementaryProjection_mem_of_reduces hRU hw))

/-- Forward direction of Proposition 3.5: the fixed-cosine eigenspace reduces
both projections and every source, target, source-complement and
target-complement vector makes the fixed cosine `c`. -/
theorem fixedCosineSubspace_isFixedCosineReducing (c : ℝ) (hc0 : 0 < c) :
    IsFixedCosineReducingSubspace U V (fixedCosineSubspace U V c) c := by
  refine ⟨reduces_projection_of_commute U V c U (halmosCosineSq_commute_projection U V),
    reduces_projection_of_commute U V c V (halmosCosineSq_commute_projection_right U V),
    ?_, ?_, ?_, ?_⟩
  · intro x hxM hxU
    refine norm_eq_from_ofReal_sq (𝕜 := 𝕜) (norm_nonneg _) (norm_nonneg _) hc0.le ?_
    rw [← inner_halmosCosineSq_source U V x hxU, (mem_fixedCosineSubspace U V c x).mp hxM,
      inner_smul_left, map_pow, RCLike.conj_ofReal, inner_self_ofReal]
  · intro x hxM hxV
    refine norm_eq_from_ofReal_sq (𝕜 := 𝕜) (norm_nonneg _) (norm_nonneg _) hc0.le ?_
    rw [← inner_halmosCosineSq_source V U x hxV, ← halmosCosineSq_symm U V,
      (mem_fixedCosineSubspace U V c x).mp hxM, inner_smul_left, map_pow,
      RCLike.conj_ofReal, inner_self_ofReal]
  · intro x hxM hxU
    refine norm_eq_from_ofReal_sq (𝕜 := 𝕜) (norm_nonneg _) (norm_nonneg _) hc0.le ?_
    rw [← inner_halmosCosineSq_source_compl U V x hxU, (mem_fixedCosineSubspace U V c x).mp hxM,
      inner_smul_left, map_pow, RCLike.conj_ofReal, inner_self_ofReal]
  · intro x hxM hxV
    refine norm_eq_from_ofReal_sq (𝕜 := 𝕜) (norm_nonneg _) (norm_nonneg _) hc0.le ?_
    rw [← inner_halmosCosineSq_source_compl V U x hxV, ← halmosCosineSq_symm U V,
      (mem_fixedCosineSubspace U V c x).mp hxM, inner_smul_left, map_pow,
      RCLike.conj_ofReal, inner_self_ofReal]

/-- Maximality direction of Proposition 3.5: any subspace with constant
source-side cosine `c` lies in the fixed-cosine eigenspace. -/
theorem fixedCosineSubspace_maximal (c : ℝ) {M : Submodule 𝕜 H}
    (hRU : (U.starProjection).Reduces M) (hRV : (V.starProjection).Reduces M)
    (hU : ∀ x : H, x ∈ M → x ∈ U → ‖V.starProjection x‖ = c * ‖x‖)
    (hUc : ∀ x : H, x ∈ M → x ∈ Uᗮ → ‖(Vᗮ).starProjection x‖ = c * ‖x‖) :
    M ≤ fixedCosineSubspace U V c := by
  have hEU : ∀ w ∈ M, w ∈ U → halmosCosineSq U V w = (c : 𝕜) ^ 2 • w := by
    intro w hwM hwU
    have hclaim : (halmosCosineSq U V - (c : 𝕜) ^ 2 • (1 : H →L[𝕜] H)) w = 0 := by
      refine eigen_of_reducing_quadratic (halmosCosineSq_sub_smul_isSymmetric U V c)
        (W := M ⊓ U) ?_ ?_
        (Submodule.mem_inf.mpr ⟨hwM, hwU⟩)
      · intro y hy
        obtain ⟨hyM, hyU⟩ := Submodule.mem_inf.mp hy
        simp only [sub_apply, smul_apply,
          one_apply_eq_self]
        refine Submodule.mem_inf.mpr
          ⟨M.sub_mem (halmosCosineSq_mem_of_reduces U V hRU hRV hyM) (M.smul_mem _ hyM), ?_⟩
        rw [halmosCosineSq_source_apply U V y hyU]
        exact U.sub_mem (U.starProjection_apply_mem _) (U.smul_mem _ hyU)
      · intro y hy
        obtain ⟨hyM, hyU⟩ := Submodule.mem_inf.mp hy
        rw [sub_apply, inner_sub_left,
          smul_apply, one_apply_eq_self,
          inner_halmosCosineSq_source U V y hyU, inner_smul_left, map_pow,
          RCLike.conj_ofReal, inner_self_ofReal, hU y hyM hyU]
        push_cast; ring
    have heq : halmosCosineSq U V w - (c : 𝕜) ^ 2 • w = 0 := by
      rwa [sub_apply, smul_apply,
        one_apply_eq_self] at hclaim
    exact sub_eq_zero.mp heq
  have hEUc : ∀ w ∈ M, w ∈ Uᗮ → halmosCosineSq U V w = (c : 𝕜) ^ 2 • w := by
    intro w hwM hwU
    have hclaim : (halmosCosineSq U V - (c : 𝕜) ^ 2 • (1 : H →L[𝕜] H)) w = 0 := by
      refine eigen_of_reducing_quadratic (halmosCosineSq_sub_smul_isSymmetric U V c)
        (W := M ⊓ Uᗮ) ?_ ?_
        (Submodule.mem_inf.mpr ⟨hwM, hwU⟩)
      · intro y hy
        obtain ⟨hyM, hyU⟩ := Submodule.mem_inf.mp hy
        simp only [sub_apply, smul_apply,
          one_apply_eq_self]
        refine Submodule.mem_inf.mpr
          ⟨M.sub_mem (halmosCosineSq_mem_of_reduces U V hRU hRV hyM) (M.smul_mem _ hyM), ?_⟩
        rw [halmosCosineSq_source_compl_apply U V y hyU]
        exact Uᗮ.sub_mem (Uᗮ.starProjection_apply_mem _) (Uᗮ.smul_mem _ hyU)
      · intro y hy
        obtain ⟨hyM, hyU⟩ := Submodule.mem_inf.mp hy
        rw [sub_apply, inner_sub_left,
          smul_apply, one_apply_eq_self,
          inner_halmosCosineSq_source_compl U V y hyU, inner_smul_left, map_pow,
          RCLike.conj_ofReal, inner_self_ofReal, hUc y hyM hyU]
        push_cast; ring
    have heq : halmosCosineSq U V w - (c : 𝕜) ^ 2 • w = 0 := by
      rwa [sub_apply, smul_apply,
        one_apply_eq_self] at hclaim
    exact sub_eq_zero.mp heq
  intro w hw
  rw [mem_fixedCosineSubspace]
  have hdecomp : w = U.starProjection w + (Uᗮ).starProjection w := by
    have hcompl : (Uᗮ).starProjection w = w - U.starProjection w :=
      congrArg (fun T : H →L[𝕜] H => T w) (Submodule.starProjection_orthogonal' U)
    rw [hcompl]; abel
  have e1 := hEU (U.starProjection w) (hRU.1 w hw) (U.starProjection_apply_mem w)
  have e2 := hEUc ((Uᗮ).starProjection w)
    (complementaryProjection_mem_of_reduces hRU hw) (Uᗮ.starProjection_apply_mem w)
  conv_lhs => rw [hdecomp]
  conv_rhs => rw [hdecomp]
  rw [map_add, e1, e2, smul_add]

/-- The predicate actually printed in Proposition 3.5(a)(b)(c): `M` reduces `P`
and `Q`, every vector of `M ∩ P𝓗` makes the fixed angle with `Q`, and every
vector of `M ∩ Ptilde𝓗` makes the fixed angle with `Qtilde`.

Transcription `prop:3.5`, clauses (a)(b)(c): the two angle conditions are
indexed by `{M ∩ U, M ∩ Uᗮ}`, not by `{M ∩ U, M ∩ V}`.  The norm form
`‖P_V x‖ = c * ‖x‖` is the cosine form of `∠(x, Q x) = θ` with `c = cos θ`. -/
def IsPrintedFixedCosineReducingSubspace
    (M : Submodule 𝕜 H) (c : ℝ) : Prop :=
  (U.starProjection).Reduces M ∧
  (V.starProjection).Reduces M ∧
  (∀ x : H, x ∈ M → x ∈ U → ‖V.starProjection x‖ = c * ‖x‖) ∧
  (∀ x : H, x ∈ M → x ∈ Uᗮ → ‖(Vᗮ).starProjection x‖ = c * ‖x‖)

/-- Bundled form of `fixedCosineSubspace_maximal`: the printed hypotheses
(a)(b)(c) alone put `M` inside the fixed-cosine eigenspace. -/
theorem fixedCosineSubspace_maximal_printed (c : ℝ) {M : Submodule 𝕜 H}
    (hM : IsPrintedFixedCosineReducingSubspace U V M c) :
    M ≤ fixedCosineSubspace U V c :=
  fixedCosineSubspace_maximal U V c hM.1 hM.2.1 hM.2.2.1 hM.2.2.2

/-- The two extra conjuncts of `IsFixedCosineReducingSubspace` are **redundant**:
the printed four already imply the target-side and target-complement-side
conditions.  Maximality carries `M` into the eigenspace, and on the eigenspace
all four block conditions hold. -/
theorem isFixedCosineReducingSubspace_of_printed (c : ℝ) (hc0 : 0 < c)
    {M : Submodule 𝕜 H} (hM : IsPrintedFixedCosineReducingSubspace U V M c) :
    IsFixedCosineReducingSubspace U V M c := by
  obtain ⟨hRU, hRV, hUcond, hUperp⟩ := hM
  have hle : M ≤ fixedCosineSubspace U V c :=
    fixedCosineSubspace_maximal U V c hRU hRV hUcond hUperp
  obtain ⟨-, -, -, hVcond, -, hVperp⟩ :=
    fixedCosineSubspace_isFixedCosineReducing U V c hc0
  exact ⟨hRU, hRV, hUcond, fun x hxM hxV => hVcond x (hle hxM) hxV, hUperp,
    fun x hxM hxV => hVperp x (hle hxM) hxV⟩

/-- The symmetrised predicate implies the printed one, by dropping conjuncts. -/
theorem isPrintedFixedCosineReducingSubspace_of_isFixedCosineReducingSubspace
    (c : ℝ) {M : Submodule 𝕜 H} (hM : IsFixedCosineReducingSubspace U V M c) :
    IsPrintedFixedCosineReducingSubspace U V M c :=
  ⟨hM.1, hM.2.1, hM.2.2.1, hM.2.2.2.2.1⟩

/-- Davis--Kahan 1970, Proposition 3.5, maximal-subspace clause: for every
`c > 0` the fixed-angle eigenspace of the Halmos cosine square is the unique
maximal subspace with the printed properties (a)(b)(c).

Stated at the **printed** hypotheses.  Three narrowings that earlier versions of
this statement carried are gone, and none of them was load-bearing.

* `IsUniformlyAcute U V` — printed Proposition 3.5 says "in the acute case",
  which is `IsAcute` (Definition 3.2), and `IsUniformlyAcute` is strictly
  stronger in infinite dimension.  Neither is needed: the proof never used the
  hypothesis, which the earlier statement bound and discarded.
* `c ≤ 1` — likewise unused.
* The maximality clause quantified over `IsFixedCosineReducingSubspace`, which
  has two conjuncts more than printed (a)(b)(c).  It now quantifies over the
  printed `IsPrintedFixedCosineReducingSubspace`, i.e. over a strictly larger
  class of `M`, while the first conjunct still asserts the *stronger*
  symmetrised predicate of the eigenspace.  So both halves are at least as
  strong as before; see
  `proposition3_5_fixedAngle_maximal_uniformlyAcute_form`. -/
theorem proposition3_5_fixedAngle_maximal (c : ℝ) (hc0 : 0 < c) :
    IsFixedCosineReducingSubspace U V (fixedCosineSubspace U V c) c ∧
      ∀ M : Submodule 𝕜 H,
        IsPrintedFixedCosineReducingSubspace U V M c →
          M ≤ fixedCosineSubspace U V c :=
  ⟨fixedCosineSubspace_isFixedCosineReducing U V c hc0,
    fun _ hM => fixedCosineSubspace_maximal_printed U V c hM⟩

/-- The previously compiled form of Proposition 3.5, re-derived from the printed
form above: acuteness and `c ≤ 1` are discarded and the maximality clause is
restricted from the printed predicate back to the narrower symmetrised one.  It
is recorded to witness that nothing was weakened by the restatement. -/
theorem proposition3_5_fixedAngle_maximal_uniformlyAcute_form
    (_hacute : IsUniformlyAcute U V) (c : ℝ) (hc0 : 0 < c) (_hc1 : c ≤ 1) :
    IsFixedCosineReducingSubspace U V (fixedCosineSubspace U V c) c ∧
      ∀ M : Submodule 𝕜 H,
        IsFixedCosineReducingSubspace U V M c →
          M ≤ fixedCosineSubspace U V c :=
  ⟨(proposition3_5_fixedAngle_maximal U V c hc0).1,
    fun M hM => (proposition3_5_fixedAngle_maximal U V c hc0).2 M
      (isPrintedFixedCosineReducingSubspace_of_isFixedCosineReducingSubspace
        U V c hM)⟩

end DavisKahan
end TauCeti
