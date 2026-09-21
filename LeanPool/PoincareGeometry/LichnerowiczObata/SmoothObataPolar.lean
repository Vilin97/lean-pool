/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.SmoothPolarTransport
public import LeanPool.PoincareGeometry.LichnerowiczObata.SmoothRadialFlow
public import LeanPool.PoincareGeometry.LichnerowiczObata.NormalChartRadialFlow
public import Mathlib.Geometry.Manifold.Instances.Sphere

/-! # Smoothness of the actual Obata polar map on the regular cylinder -/

@[expose] public noncomputable section
open Bundle Set AlmostSchur
open scoped Manifold ContDiff Topology
namespace LichnerowiczObata
variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]
  [FiniteDimensional ℝ P] {n : ℕ} [Fact (Module.finrank ℝ P = n + 1)]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
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

omit [FiniteDimensional ℝ P] [ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I] in
/-- The actual polar map, restricted to unit directions, is smooth at every
regular radius. The transport used in the proof is constructed from the
smooth gradient flow and identified with the given rays by ODE uniqueness. -/
theorem HasRadialPoleModel.contMDiffAt_obata_polar
    {Φ : P × ℝ → M} {p : M} (hpole : HasRadialPoleModel I Φ p)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hnon : ∃ x y, f x ≠ f y)
    {K a : ℝ} (hK : 0 < K) (ha : 0 < a)
    (hH : ∀ (y : M) (v w : TangentSpace I y),
      hessian (leviCivitaConnection (I := I)) f y v w = -K * f y * inner ℝ v w)
    (hcrit : gradient (I := I) f p = 0) (hmax : f p = a)
    (hreg : ∀ u : Metric.sphere (0 : P) 1, ∀ r ∈ Ioo 0 (Real.pi / Real.sqrt K),
      -a < f (Φ (u, r)) ∧ f (Φ (u, r)) < a)
    (hrad : ∀ u : Metric.sphere (0 : P) 1, ∀ r ∈ Ioo 0 (Real.pi / Real.sqrt K),
      obataRadial K a f (Φ (u, r)) = r)
    (hcurves : ∀ u : Metric.sphere (0 : P) 1,
      IsMIntegralCurveOn (fun r => Φ (u, r)) (gradient (I := I) (obataRadial K a f))
        (Ioo 0 (Real.pi / Real.sqrt K)))
    (u : Metric.sphere (0 : P) 1) {r : ℝ} (hr : r ∈ Ioo 0 (Real.pi / Real.sqrt K)) :
    ContMDiffAt ((𝓡 n).prod 𝓘(ℝ, ℝ)) I ∞
      (fun q : Metric.sphere (0 : P) 1 × ℝ => Φ (q.1, q.2)) (u, r) := by
  obtain ⟨a', ha', _, hn, η, hη, hηcurves⟩ :=
    exists_smooth_obata_radial_family hK hf hnon hH
  have he := hn p
  rw [hcrit, hmax, norm_zero, zero_pow (by decide : 2 ≠ 0)] at he
  have heq : a' = a := by
    have hs : a' ^ 2 - a ^ 2 = 0 := (mul_eq_zero.mp he.symm).resolve_left hK.ne'
    nlinarith
  subst a'
  have hf2 : ContMDiff I 𝓘(ℝ, ℝ) 2 f :=
    hf.of_le (WithTop.coe_le_coe.mpr le_top)
  have hreset : ∀ u : Metric.sphere (0 : P) 1,
      ∀ s r, s ∈ Ioo 0 (Real.pi / Real.sqrt K) → r ∈ Ioo 0 (Real.pi / Real.sqrt K) →
        Φ (u, r) = η (Φ (u, s), r) := by
    intro u s r hs hr
    have hi := (hηcurves _ (hreg u s hs)).1
    rw [hrad u s hs] at hi
    exact obataRadial_integralCurve_eqOn ha hf2 hs (hreg u) (hcurves u)
      (hηcurves _ (hreg u s hs)).2.2.1 hi.symm hr
  obtain ⟨χ, _, hχ, _, δ, hδ, hseed⟩ := hpole
  apply contMDiffAt_of_smooth_pole_transport (fun u : Metric.sphere (0 : P) 1 => (u : P))
    contMDiff_coe_sphere χ hχ
    (fun q : Metric.sphere (0 : P) 1 × ℝ => Φ (q.1, q.2)) η hδ
    (div_pos Real.pi_pos (Real.sqrt_pos.mpr hK)) hseed hreset ?_ u hr
  intro u s r hs hr
  have hopen : IsOpen ({x : M | -a < f x ∧ f x < a} ×ˢ Ioo 0 (Real.pi / Real.sqrt K)) :=
    ((isOpen_lt continuous_const hf.continuous).inter
      (isOpen_lt hf.continuous continuous_const)).prod isOpen_Ioo
  exact (hη (Φ (u, s), r) ⟨hreg u s hs, hr⟩).contMDiffAt
    (hopen.mem_nhds ⟨hreg u s hs, hr⟩)

end LichnerowiczObata
