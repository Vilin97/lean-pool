/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.IntrinsicNormalChart
public import LeanPool.PoincareGeometry.LichnerowiczObata.ObataUniquePoles

/-! # The regular Obata region has spherical angular topology -/

@[expose] public noncomputable section
open Bundle Set AlmostSchur
open scoped Manifold ContDiff Topology

namespace LichnerowiczObata
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless] [PreconnectedSpace M]
  [CompactSpace M] [T2Space M] [Nonempty M]
  [ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I ∞ E (TangentSpace I : M → Type _)]

/-- The Obata equation alone supplies the two unique poles and the global
tangent-sphere product for the regular region. No pole, normal chart, radius,
or choice of coordinate basis is assumed. This is a topological conclusion,
not yet a Riemannian isometry. -/
theorem obata_regular_tangent_sphere_product
    (hdim : 1 < Module.rank ℝ E) {K : ℝ} (hK : 0 < K) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hnon : ∃ x y, f x ≠ f y)
    (hH : ∀ (x : M) (v w : TangentSpace I x),
      hessian (leviCivitaConnection (I := I)) f x v w = -K * f x * inner ℝ v w) :
    ∃ a : ℝ, 0 < a ∧ (∀ x, -a ≤ f x ∧ f x ≤ a) ∧ ∃ p q : M,
      p ≠ q ∧ (∀ x, f x = a ↔ x = p) ∧ (∀ x, f x = -a ↔ x = q) ∧
      ∃ R : ℝ, 0 < R ∧ Nonempty ({x : M // -a < f x ∧ f x < a} ≃ₜ
        Metric.sphere (0 : TangentSpace I p) R × Ioo 0 (Real.pi / Real.sqrt K)) := by
  have hf2 : ContMDiff I 𝓘(ℝ, ℝ) 2 f :=
    hf.of_le (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))
  obtain ⟨a, ha, hb, p, q, hp, _, hpq, hmax, hmin, _⟩ :=
    obata_unique_poles hdim hK hf2 hnon hH
  have hpm : IsMaxOn f univ p := fun x _ => by rw [hp]; exact (hb x).2
  have hcrit : gradient (I := I) f p = 0 := gradient_eq_zero_of_local_extremum
    ((hf2 p).mdifferentiableAt (by norm_num)) (Or.inr (hpm.isLocalMax (by simp)))
  have hz := (extChartAt I p).map_source (mem_extChartAt_source (I := I) p)
  have he : (extChartAt I p).symm ((extChartAt I p) p) = p :=
    (extChartAt I p).left_inv (mem_extChartAt_source (I := I) p)
  have hcrit' : gradient (I := I) f ((extChartAt I p).symm ((extChartAt I p) p)) = 0 := by
    rw [he]
    exact hcrit
  have hmax' : ∀ x, f x = a ↔ x = (extChartAt I p).symm ((extChartAt I p) p) := by
    simpa only [he] using hmax
  have hprod := exists_obata_tangent_sphere_product (Module.finBasis ℝ E)
    hf hnon hK ha hH p hz hcrit' hmax'
  rw [he] at hprod
  exact ⟨a, ha, hb, p, q, hpq, hmax, hmin, hprod⟩

/-- Removing precisely the two constructed poles gives the global spherical
product. In particular, the product covers every other manifold point. -/
theorem obata_punctured_tangent_sphere_product
    (hdim : 1 < Module.rank ℝ E) {K : ℝ} (hK : 0 < K) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hnon : ∃ x y, f x ≠ f y)
    (hH : ∀ (x : M) (v w : TangentSpace I x),
      hessian (leviCivitaConnection (I := I)) f x v w = -K * f x * inner ℝ v w) :
    ∃ p q : M, p ≠ q ∧ ∃ R : ℝ, 0 < R ∧
      Nonempty ({x : M // x ≠ p ∧ x ≠ q} ≃ₜ
        Metric.sphere (0 : TangentSpace I p) R × Ioo 0 (Real.pi / Real.sqrt K)) := by
  obtain ⟨a, ha, hb, p, q, hpq, hmax, hmin, R, hR, ⟨e⟩⟩ :=
    obata_regular_tangent_sphere_product hdim hK hf hnon hH
  have heq : {x : M | x ≠ p ∧ x ≠ q} = {x : M | -a < f x ∧ f x < a} := by
    ext x
    change (x ≠ p ∧ x ≠ q) ↔ (-a < f x ∧ f x < a)
    constructor
    · intro hx
      exact ⟨lt_of_le_of_ne (hb x).1 (fun he => hx.2 ((hmin x).mp he.symm)),
        lt_of_le_of_ne (hb x).2 (fun he => hx.1 ((hmax x).mp he))⟩
    · intro hx
      exact ⟨fun he => (ne_of_lt hx.2) ((hmax x).mpr he),
        fun he => (ne_of_lt hx.1) ((hmin x).mpr he).symm⟩
  exact ⟨p, q, hpq, R, hR, ⟨(Homeomorph.setCongr heq).trans e⟩⟩

end LichnerowiczObata
