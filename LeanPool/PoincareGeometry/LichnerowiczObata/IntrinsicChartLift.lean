/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.IntrinsicNormalChart
public import LeanPool.PoincareGeometry.LichnerowiczObata.NormalRadialProduct

/-! # Lifting a specified coordinate normal chart without changing its map -/

@[expose] public noncomputable section
open Bundle FiberBundle Set AlmostSchur
open scoped Manifold ContDiff Topology

namespace LichnerowiczObata
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]

local notation "TM" => (TangentSpace I : M → Type _)

omit [FiniteDimensional ℝ E] in
/-- A specified coordinate chart is lifted to the intrinsic tangent space.
Both the forward map and its exact source are retained, so metric formulas
for the coordinate chart apply to every point of the lifted source. -/
theorem exists_intrinsic_chart_lift (c : M) {z : E}
    (hz : z ∈ (extChartAt I c).target) (e : OpenPartialHomeomorph E E)
    (he0 : (0 : E) ∈ e.source) (hez : e 0 = z)
    (hout : ∀ u ∈ e.source, e u ∈ (extChartAt I c).target)
    {ρ : M → ℝ} {t : ℝ}
    (hrad : ∀ u ∈ e.source, ρ ((extChartAt I c).symm (e u)) =
      t * ‖(trivializationAt E TM c).symmL ℝ ((extChartAt I c).symm z) u‖) :
    let p := (extChartAt I c).symm z
    ∃ F : OpenPartialHomeomorph (TM p) M,
      0 ∈ F.source ∧ F 0 = p ∧
      (∀ v, F v = (extChartAt I c).symm
        (e ((trivializationAt E TM c).continuousLinearMapAt ℝ p v))) ∧
      (∀ v, v ∈ F.source ↔ (trivializationAt E TM c).continuousLinearMapAt ℝ p v ∈ e.source) ∧
      ∀ v ∈ F.source, ρ (F v) = t * ‖v‖ := by
  let p := (extChartAt I c).symm z
  have hp : p ∈ (chartAt H c).source := by simpa [p] using (extChartAt I c).map_target hz
  let L := (trivializationAt E TM c).continuousLinearEquivAt ℝ p hp
  let C : OpenPartialHomeomorph M E :=
    { toPartialEquiv := extChartAt I c
      open_source := isOpen_extChartAt_source c
      open_target := isOpen_extChartAt_target c
      continuousOn_toFun := continuousOn_extChartAt c
      continuousOn_invFun := continuousOn_extChartAt_symm c }
  let F := L.toHomeomorph.toOpenPartialHomeomorph.trans (e.trans C.symm)
  have hLv (v : TM p) : L v = (trivializationAt E TM c).continuousLinearMapAt ℝ p v :=
    congrFun ((trivializationAt E TM c).coe_continuousLinearEquivAt_eq hp) v
  have hsource (v : TM p) : v ∈ F.source ↔
      (trivializationAt E TM c).continuousLinearMapAt ℝ p v ∈ e.source := by
    change (v ∈ univ ∧ L v ∈ e.source ∧ e (L v) ∈ C.target) ↔ _
    rw [hLv]
    exact ⟨fun hv => hv.2.1, fun hv => ⟨mem_univ v, hv, hout _ hv⟩⟩
  have hmap (v : TM p) : F v = (extChartAt I c).symm
      (e ((trivializationAt E TM c).continuousLinearMapAt ℝ p v)) := by
    change C.symm (e (L v)) = _
    rw [hLv]
    rfl
  refine ⟨F, (hsource 0).mpr (by simpa only [map_zero] using he0), ?_, hmap, hsource, ?_⟩
  · rw [hmap, map_zero, hez]
  · intro v hv
    rw [hmap, hrad _ ((hsource v).mp hv)]
    have hcancel : (trivializationAt E TM c).symmL ℝ p
        ((trivializationAt E TM c).continuousLinearMapAt ℝ p v) = v :=
      (trivializationAt E TM c).symmL_continuousLinearMapAt hp v
    rw [hcancel]

omit [FiniteDimensional ℝ E] in
/-- The spherical product retains the specified coordinate chart and radial
family in its forward formula, while its angular sphere uses the intrinsic
tangent-space norm. Every angular parameter lies in the coordinate source. -/
theorem exists_coordinate_normal_radial_product_map [CompactSpace M]
    (c : M) {z : E} (hz : z ∈ (extChartAt I c).target)
    (e : OpenPartialHomeomorph E E) (he0 : (0 : E) ∈ e.source) (hez : e 0 = z)
    (hout : ∀ u ∈ e.source, e u ∈ (extChartAt I c).target)
    {ρ : M → ℝ} (hcρ : Continuous ρ) (hn : ∀ x, 0 ≤ ρ x)
    (hzero : ∀ x, ρ x = 0 ↔ x = (extChartAt I c).symm z)
    {t ℓ : ℝ} (ht : 0 < t) (hℓ : 0 < ℓ)
    (hrad : ∀ u ∈ e.source, ρ ((extChartAt I c).symm (e u)) =
      t * ‖(trivializationAt E TM c).symmL ℝ ((extChartAt I c).symm z) u‖)
    (U : Set M) (hU : ∀ x, x ∈ U ↔ ρ x ∈ Ioo 0 ℓ)
    (η : M × ℝ → M) (hcη : ContinuousOn η (U ×ˢ Ioo 0 ℓ))
    (hlevel : ∀ x ∈ U, ∀ r ∈ Ioo 0 ℓ, ρ (η (x, r)) = r)
    (hinit : ∀ x ∈ U, η (x, ρ x) = x)
    (hreset : ∀ x ∈ U, ∀ r ∈ Ioo 0 ℓ, ∀ s ∈ Ioo 0 ℓ, η (η (x, r), s) = η (x, s)) :
    let p := (extChartAt I c).symm z
    ∃ R : ℝ, 0 < R ∧ t * R ∈ Ioo 0 ℓ ∧
      (∀ v ∈ Metric.ball (0 : TM p) (2 * R),
        (trivializationAt E TM c).continuousLinearMapAt ℝ p v ∈ e.source) ∧
      (∀ v : Metric.sphere (0 : TM p) R,
        (trivializationAt E TM c).continuousLinearMapAt ℝ p v ∈ e.source) ∧
      ∃ H : Metric.sphere (0 : TM p) R × Ioo 0 ℓ ≃ₜ U,
        ∀ q, (H q : M) = η ((extChartAt I c).symm
          (e ((trivializationAt E TM c).continuousLinearMapAt ℝ p q.1)), q.2) := by
  obtain ⟨F, hF0, hFp, hmap, hsource, hradF⟩ :=
    exists_intrinsic_chart_lift c hz e he0 hez hout hrad
  have hzF : ∀ x, ρ x = 0 ↔ x = F 0 := by
    rw [hFp]
    exact hzero
  obtain ⟨R, hR, hlevelR, hball, hRs, H, hH⟩ := exists_normal_radial_product_map F hF0 hcρ hn hzF ht hℓ
    hradF U hU η hcη hlevel hinit hreset
  refine ⟨R, hR, hlevelR, fun v hv => (hsource v).mp (hball hv),
    fun v => (hsource v).mp (hRs v), H, ?_⟩
  intro q
  rw [hH, hmap]

end LichnerowiczObata
