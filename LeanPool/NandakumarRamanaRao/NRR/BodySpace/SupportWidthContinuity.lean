/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import Mathlib
import LeanPool.NandakumarRamanaRao.NRR.BodySpace.PositiveArea
import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.SupportFunctionParametric
import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.WidthFamilies

/-!
# `NRR.BodySpace` — joint support-function and width continuity

This module proves that support functions and widths depend continuously on *both* the body and
the direction, for bodies varying in the fixed-parent hyperspace `ConvexSubbody K` and in the
lower-area subspace `BodySpace K A`.

## Core reusable lemma

The heart of the file is a body-parameter continuity criterion for the *solid* geometry bodies:
if a family `K : α → Geometry.ConvexBody Plane` is continuous for the Hausdorff-metric topology,
then it is a `SupportFunctionContinuousFamily` and a `WidthContinuousFamily`. The proof follows the
standard split of `h_{K a}(u) - h_{K a₀}(u₀)` into a *body-variation* term, controlled by the
Hausdorff–Lipschitz estimate `abs_supportFunction_sub_le_hausdorffDist_mul_norm`, and a
*direction-variation* term, controlled by the fixed-body direction continuity
`continuous_supportFunction`.

## Possibly-degenerate subbodies

The project support function `Geometry.ConvexBody.supportFunction` is defined only on the *solid*
bundled type `Geometry.ConvexBody`, whereas a `ConvexSubbody K` may be lower-dimensional. We
therefore work with the support function of the underlying compact convex set directly — the same
`sSup ⟪·, u⟫` formula as `Geometry.ConvexBody.supportFunction`, now for a possibly-degenerate
carrier — packaged as `ConvexSubbody.supportFunction`. It agrees with the geometry support function
whenever the subbody is solid. Its joint continuity uses the Hausdorff–Lipschitz estimate (whose
proof needs only carrier compactness and nonemptiness) and the fixed-body direction continuity,
both re-established here at the set level.

## Positive lower area

When `A > 0` every element of `BodySpace K A` is genuinely solid, so the solid bridge
`BodySpace.toGeometryConvexBody` lands in `Geometry.ConvexBody Plane`; the solid family predicates
follow from the core reusable lemma applied to the continuous bridge
`BodySpace.continuous_toGeometryConvexBody`.
-/

open MeasureTheory Metric Filter Topology

open NRR.Geometry

namespace NRR.Geometry

namespace ConvexBody

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-
**Body-parameter support continuity.** If a family of solid geometry bodies is continuous for
the Hausdorff-metric topology, then `(t, u) ↦ h_{K_t}(u)` is jointly continuous. The estimate
`abs_supportFunction_sub_le_hausdorffDist_mul_norm` controls the body-variation term and
`continuous_supportFunction` the direction-variation term.
-/
theorem SupportFunctionContinuousFamily.of_continuous
    {α : Type*} [TopologicalSpace α] {K : α → ConvexBody E}
    (hK : Continuous K) :
    SupportFunctionContinuousFamily K := by
  refine continuous_iff_continuousAt.mpr fun p => Metric.tendsto_nhds.mpr fun ε εpos => ?_
  have hbound : ∀ᶠ (x : α × E) in 𝓝 p,
      |(K x.1).supportFunction x.2 - (K p.1).supportFunction x.2| ≤
        Metric.hausdorffDist (K x.1 : Set E) (K p.1 : Set E) * ‖x.2‖ :=
    Filter.Eventually.of_forall fun x =>
      NRR.Geometry.ConvexBody.abs_supportFunction_sub_le_hausdorffDist_mul_norm (K x.1) (K p.1) x.2
  have hc : Continuous (fun x : ConvexBody E => Metric.hausdorffDist (x : Set E) (K p.1 : Set E)) := by
    have h_mathlib : Continuous (fun x : _root_.ConvexBody E => dist x (K p.1).toMathlib) :=
      continuous_id.dist continuous_const
    have h_toMathlib : Continuous (fun x : ConvexBody E => x.toMathlib) := continuous_induced_dom
    have h_comp := h_mathlib.comp h_toMathlib
    have h_eq : (fun x : ConvexBody E => Metric.hausdorffDist (x : Set E) (K p.1 : Set E))
        = (fun x : _root_.ConvexBody E => dist x (K p.1).toMathlib) ∘ (fun x : ConvexBody E => x.toMathlib) := by
      ext x; rfl
    rw [h_eq]
    exact h_comp
  have htend : Filter.Tendsto (fun x : α × E => Metric.hausdorffDist (K x.1 : Set E) (K p.1 : Set E) * ‖x.2‖) (𝓝 p) (𝓝 0) := by
    have h1 : Continuous (fun x : α × E => Metric.hausdorffDist (K x.1 : Set E) (K p.1 : Set E) * ‖x.2‖) :=
      (hc.comp (hK.comp continuous_fst)).mul (continuous_norm.comp continuous_snd)
    have h2 := h1.tendsto p
    have h3 : Metric.hausdorffDist (K p.1 : Set E) (K p.1 : Set E) * ‖p.2‖ = (0 : ℝ) := by
      simp [Metric.hausdorffDist_self_zero]
    exact h3 ▸ h2
  have hdir : Filter.Tendsto (fun x : α × E => (K p.1).supportFunction x.2 - (K p.1).supportFunction p.2) (𝓝 p) (𝓝 0) := by
    have h1 : Continuous (fun x : α × E => (K p.1).supportFunction x.2 - (K p.1).supportFunction p.2) :=
      ((K p.1).continuous_supportFunction.comp continuous_snd).sub continuous_const
    have h2 := h1.tendsto p
    have h3 : (K p.1).supportFunction p.2 - (K p.1).supportFunction p.2 = (0 : ℝ) := by ring
    exact h3 ▸ h2
  filter_upwards [hbound,
    htend.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 2 by linarith)),
    hdir.eventually (Metric.ball_mem_nhds _ (half_pos εpos))] with x hx₁ hx₂ hx₃
  rw [Real.dist_eq, abs_lt]
  rw [Real.dist_eq, abs_lt, sub_zero] at hx₃
  have hb := abs_le.mp hx₁
  constructor <;> nlinarith [hb.1, hb.2, hx₂, hx₃.1, hx₃.2]

/-- **Body-parameter width continuity** for a Hausdorff-continuous family of solid bodies. -/
theorem WidthContinuousFamily.of_continuous
    {α : Type*} [TopologicalSpace α] {K : α → ConvexBody E}
    (hK : Continuous K) :
    WidthContinuousFamily K :=
  WidthContinuousFamily.of_support (SupportFunctionContinuousFamily.of_continuous hK)

end ConvexBody

end NRR.Geometry

namespace NRR

namespace ConvexSubbody

variable {K : Geometry.ConvexBody Plane}

/-- **Support function of a convex subbody.** The supremum of `⟪x, u⟫` over the (compact, nonempty)
carrier of `C`. This is the same formula as `Geometry.ConvexBody.supportFunction`, valid for a
possibly-degenerate carrier; it agrees with the geometry support function on solid subbodies. -/
noncomputable def supportFunction (C : ConvexSubbody K) (u : Plane) : ℝ :=
  sSup ((fun x : Plane => (inner ℝ x u : ℝ)) '' (C.body : Set Plane))

/-- Unfolding lemma for the subbody support function. -/
theorem supportFunction_eq_sSup (C : ConvexSubbody K) (u : Plane) :
    C.supportFunction u = sSup ((fun x : Plane => (inner ℝ x u : ℝ)) '' (C.body : Set Plane)) :=
  rfl

/-- The image `{⟪x, u⟫ | x ∈ C}` is bounded above (the carrier is compact, hence bounded). -/
theorem inner_image_bddAbove (C : ConvexSubbody K) (u : Plane) :
    BddAbove ((fun x : Plane => (inner ℝ x u : ℝ)) '' (C.body : Set Plane)) :=
  C.isCompact.bddAbove_image (by fun_prop)

/-- **Support point.** The supremum defining `h_C(u)` is attained at some point of the carrier. -/
theorem exists_supportPoint (C : ConvexSubbody K) (u : Plane) :
    ∃ x ∈ (C.body : Set Plane), C.supportFunction u = (inner ℝ x u : ℝ) := by
  obtain ⟨x, hx, hmax⟩ :=
    C.isCompact.exists_isMaxOn C.nonempty (f := fun x : Plane => (inner ℝ x u : ℝ)) (by fun_prop)
  refine ⟨x, hx, ?_⟩
  apply le_antisymm
  · refine csSup_le ⟨(inner ℝ x u : ℝ), x, hx, rfl⟩ ?_
    rintro b ⟨y, hy, rfl⟩
    exact hmax hy
  · exact le_csSup (C.inner_image_bddAbove u) ⟨x, hx, rfl⟩

/-- Every point of the carrier gives an inner product bounded by the support function. -/
theorem inner_le_supportFunction (C : ConvexSubbody K) {x u : Plane}
    (hx : x ∈ (C.body : Set Plane)) :
    (inner ℝ x u : ℝ) ≤ C.supportFunction u :=
  le_csSup (C.inner_image_bddAbove u) ⟨x, hx, rfl⟩

/-- **Agreement with the geometry support function.** Whenever a subbody shares its carrier with a
solid geometry body, the two support functions coincide (both are the `sSup` of `⟪·, u⟫` over the
common carrier). This certifies that `ConvexSubbody.supportFunction` is the standard support
function, extended to possibly-degenerate carriers. -/
theorem supportFunction_eq_geometry (C : ConvexSubbody K) (G : Geometry.ConvexBody Plane)
    (h : (C.body : Set Plane) = (G : Set Plane)) (u : Plane) :
    C.supportFunction u = G.supportFunction u := by
  rw [supportFunction_eq_sSup, Geometry.ConvexBody.supportFunction_eq_sSup, h]

/-- **Width function of a convex subbody**: `w_C(u) = h_C(u) + h_C(-u)`. -/
noncomputable def widthFunction (C : ConvexSubbody K) (u : Plane) : ℝ :=
  C.supportFunction u + C.supportFunction (-u)

/-- Unfolding lemma for the subbody width function. -/
@[simp] theorem widthFunction_def (C : ConvexSubbody K) (u : Plane) :
    C.widthFunction u = C.supportFunction u + C.supportFunction (-u) :=
  rfl

/-- **Fixed-body direction continuity.** For a fixed subbody, `u ↦ h_C(u)` is continuous. The
carrier is compact, hence norm-bounded, and the support function is Lipschitz in `u` with that
bound. -/
theorem continuous_supportFunction_dir (C : ConvexSubbody K) :
    Continuous fun u : Plane => C.supportFunction u := by
  obtain ⟨R, hR⟩ := C.isCompact.isBounded.subset_closedBall 0
  have hRb : ∀ x ∈ (C.body : Set Plane), ‖x‖ ≤ R := by
    intro x hx; have := hR hx; simpa [Metric.mem_closedBall, dist_eq_norm] using this
  have hRnn : 0 ≤ R := by
    obtain ⟨x, hx⟩ := C.nonempty; exact le_trans (norm_nonneg x) (hRb x hx)
  have hle : ∀ a b : Plane, C.supportFunction a - C.supportFunction b ≤ R * ‖a - b‖ := by
    intro a b
    obtain ⟨x, hx, hx'⟩ := exists_supportPoint C a
    rw [hx']
    have h1 : (inner ℝ x b : ℝ) ≤ C.supportFunction b := inner_le_supportFunction C hx
    have h2 : (inner ℝ x (a - b) : ℝ) ≤ ‖x‖ * ‖a - b‖ := real_inner_le_norm _ _
    have h3 : ‖x‖ * ‖a - b‖ ≤ R * ‖a - b‖ := mul_le_mul_of_nonneg_right (hRb x hx) (norm_nonneg _)
    have heq : (inner ℝ x a : ℝ) = (inner ℝ x b : ℝ) + (inner ℝ x (a - b) : ℝ) := by
      rw [inner_sub_right]; ring
    rw [heq]; linarith
  have hlip : LipschitzWith R.toNNReal (fun u : Plane => C.supportFunction u) := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro u v
    rw [Real.dist_eq, Real.coe_toNNReal R hRnn, dist_eq_norm, abs_sub_le_iff]
    exact ⟨hle u v, by have := hle v u; rwa [norm_sub_rev] at this⟩
  exact hlip.continuous

/-- **Hausdorff–Lipschitz estimate for subbodies.** The support functions of two subbodies differ
by at most `d_H(C, D) · ‖u‖`. Only carrier compactness and nonemptiness are used. -/
theorem abs_supportFunction_sub_le_hausdorffDist_mul_norm
    (C D : ConvexSubbody K) (u : Plane) :
    |C.supportFunction u - D.supportFunction u| ≤
      Metric.hausdorffDist (C.body : Set Plane) (D.body : Set Plane) * ‖u‖ := by
  have hbdd : Bornology.IsBounded (C.body : Set Plane) ∧ Bornology.IsBounded (D.body : Set Plane) :=
    ⟨C.isCompact.isBounded, D.isCompact.isBounded⟩
  refine abs_sub_le_iff.mpr ⟨?_, ?_⟩
  · obtain ⟨x, hx, hx'⟩ := exists_supportPoint C u
    obtain ⟨y, hy, hy'⟩ : ∃ y ∈ (D.body : Set Plane),
        dist x y = Metric.infDist x (D.body : Set Plane) := by
      have := D.isCompact.exists_infDist_eq_dist D.nonempty x; aesop
    have hdist : Metric.infDist x (D.body : Set Plane) ≤
        Metric.hausdorffDist (C.body : Set Plane) (D.body : Set Plane) :=
      Metric.infDist_le_hausdorffDist_of_mem hx
        (Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded C.nonempty D.nonempty hbdd.1 hbdd.2)
    have hin : (inner ℝ (x - y) u : ℝ) ≤ ‖x - y‖ * ‖u‖ := real_inner_le_norm _ _
    rw [hx']
    have h2 : (inner ℝ y u : ℝ) ≤ D.supportFunction u := inner_le_supportFunction D hy
    have heq : (inner ℝ x u : ℝ) - (inner ℝ y u : ℝ) = (inner ℝ (x - y) u : ℝ) := by
      rw [inner_sub_left]
    nlinarith [hin, h2, hdist, norm_nonneg u, dist_eq_norm x y ▸ hy']
  · obtain ⟨x, hx, hx'⟩ := exists_supportPoint D u
    obtain ⟨y, hy, hy'⟩ : ∃ y ∈ (C.body : Set Plane),
        dist x y = Metric.infDist x (C.body : Set Plane) := by
      have := C.isCompact.exists_infDist_eq_dist C.nonempty x; aesop
    have hdist : Metric.infDist x (C.body : Set Plane) ≤
        Metric.hausdorffDist (D.body : Set Plane) (C.body : Set Plane) :=
      Metric.infDist_le_hausdorffDist_of_mem hx
        (Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded D.nonempty C.nonempty hbdd.2 hbdd.1)
    have hin : (inner ℝ (x - y) u : ℝ) ≤ ‖x - y‖ * ‖u‖ := real_inner_le_norm _ _
    rw [hx', Metric.hausdorffDist_comm]
    have h2 : (inner ℝ y u : ℝ) ≤ C.supportFunction u := inner_le_supportFunction C hy
    have heq : (inner ℝ x u : ℝ) - (inner ℝ y u : ℝ) = (inner ℝ (x - y) u : ℝ) := by
      rw [inner_sub_left]
    nlinarith [hin, h2, hdist, norm_nonneg u, dist_eq_norm x y ▸ hy']

/-- **Joint support continuity.** The map `(C, u) ↦ h_C(u)` is continuous on
`ConvexSubbody K × Plane`. -/
theorem continuous_supportFunction :
    Continuous fun z : ConvexSubbody K × Plane => z.1.supportFunction z.2 := by
  refine continuous_iff_continuousAt.mpr ?_
  intro p
  refine Metric.tendsto_nhds.mpr ?_
  intro ε εpos
  have hbound : ∀ᶠ x : ConvexSubbody K × Plane in 𝓝 p,
      |x.1.supportFunction x.2 - p.1.supportFunction x.2| ≤
        Metric.hausdorffDist (x.1.body : Set Plane) (p.1.body : Set Plane) * ‖x.2‖ :=
    Filter.Eventually.of_forall fun x =>
      abs_supportFunction_sub_le_hausdorffDist_mul_norm x.1 p.1 x.2
  have htend : Tendsto (fun x : ConvexSubbody K × Plane =>
      Metric.hausdorffDist (x.1.body : Set Plane) (p.1.body : Set Plane) * ‖x.2‖) (𝓝 p) (𝓝 0) := by
    have hc : Continuous fun C : ConvexSubbody K =>
        Metric.hausdorffDist (C.body : Set Plane) (p.1.body : Set Plane) := by
      have hEq : (fun C : ConvexSubbody K =>
            Metric.hausdorffDist (C.body : Set Plane) (p.1.body : Set Plane))
          = fun C : ConvexSubbody K => dist C p.1 := by
        funext C; rw [dist_eq_hausdorffDist]
      rw [hEq]; exact continuous_id.dist continuous_const
    have h1 : Continuous (fun x : ConvexSubbody K × Plane =>
        Metric.hausdorffDist (x.1.body : Set Plane) (p.1.body : Set Plane) * ‖x.2‖) :=
      (hc.comp continuous_fst).mul (continuous_norm.comp continuous_snd)
    have h2 := h1.tendsto p
    have h3 : Metric.hausdorffDist (p.1.body : Set Plane) (p.1.body : Set Plane) * ‖p.2‖ = (0 : ℝ) := by
      simp [Metric.hausdorffDist_self_zero]
    exact h3 ▸ h2
  have hdir : Tendsto (fun x : ConvexSubbody K × Plane =>
      p.1.supportFunction x.2 - p.1.supportFunction p.2) (𝓝 p) (𝓝 0) := by
    have h := ((continuous_supportFunction_dir p.1).comp continuous_snd).tendsto p
    have h2 : Tendsto (fun x : ConvexSubbody K × Plane =>
        p.1.supportFunction x.2 - p.1.supportFunction p.2) (𝓝 p)
        (𝓝 (p.1.supportFunction p.2 - p.1.supportFunction p.2)) :=
      h.sub tendsto_const_nhds
    simpa using h2
  filter_upwards [hbound,
    htend.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 2 by linarith)),
    hdir.eventually (Metric.ball_mem_nhds _ (half_pos εpos))] with x hx₁ hx₂ hx₃
  rw [Real.dist_eq, abs_lt]
  rw [Real.dist_eq, abs_lt, sub_zero] at hx₃
  have hb := abs_le.mp hx₁
  constructor <;> nlinarith [hb.1, hb.2, hx₂, hx₃.1, hx₃.2]

/-- **Support-function continuous family** for `ConvexSubbody K`: the joint map `(C, u) ↦ h_C(u)`
is continuous. (Since the project support function is solid-only, this is the subbody-level analogue
of `Geometry.ConvexBody.SupportFunctionContinuousFamily` for the carrier support function.) -/
theorem supportFunctionContinuousFamily :
    Continuous fun z : ConvexSubbody K × Plane => z.1.supportFunction z.2 :=
  continuous_supportFunction

/-- **Joint width continuity.** The map `(C, u) ↦ w_C(u)` is continuous. -/
theorem continuous_width :
    Continuous fun z : ConvexSubbody K × Plane => z.1.widthFunction z.2 := by
  have hneg : Continuous fun z : ConvexSubbody K × Plane => z.1.supportFunction (-z.2) :=
    continuous_supportFunction.comp (continuous_fst.prodMk (continuous_neg.comp continuous_snd))
  exact continuous_supportFunction.add hneg

/-- **Width continuous family** for `ConvexSubbody K`: the joint map `(C, u) ↦ w_C(u)` is
continuous. -/
theorem widthContinuousFamily :
    Continuous fun z : ConvexSubbody K × Plane => z.1.widthFunction z.2 :=
  continuous_width

end ConvexSubbody

namespace BodySpace

variable {K : Geometry.ConvexBody Plane} {A : ℝ}

/-- **Support-function continuous family for positive lower area.** When `A > 0`, the solid bridge
`toGeometryConvexBody` yields a Hausdorff-continuous family of solid geometry bodies, so the
geometry support function is a `SupportFunctionContinuousFamily`. -/
theorem supportFunctionContinuousFamily
    (hA : 0 < A) :
    Geometry.ConvexBody.SupportFunctionContinuousFamily
      (fun C : BodySpace K A => C.toGeometryConvexBody hA) :=
  Geometry.ConvexBody.SupportFunctionContinuousFamily.of_continuous
    (BodySpace.continuous_toGeometryConvexBody hA)

/-- **Width continuous family for positive lower area.** -/
theorem widthContinuousFamily
    (hA : 0 < A) :
    Geometry.ConvexBody.WidthContinuousFamily
      (fun C : BodySpace K A => C.toGeometryConvexBody hA) :=
  Geometry.ConvexBody.WidthContinuousFamily.of_continuous
    (BodySpace.continuous_toGeometryConvexBody hA)

end BodySpace

end NRR
