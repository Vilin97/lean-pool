/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.ObataMatchedPolarModels
public import LeanPool.PoincareGeometry.LichnerowiczObata.PolarComparisonMetric
public import LeanPool.PoincareGeometry.LichnerowiczObata.IntrinsicRoundInverse

/-! # The regular metric comparison for a specified polar model -/

@[expose] public noncomputable section
open Bundle Set TopologicalSpace
open scoped Manifold Topology
namespace LichnerowiczObata
variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]
  {n : ℕ} [Fact (Module.finrank ℝ P = n + 1)]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]

/-- The full polar metric gives differentiable ambient comparison maps in
both directions and the forward metric for the specified coordinate
homeomorphism. No new choice of polar model is made. -/
theorem HasUnitPolarMetric.regular_comparison
    {K : ℝ} {Φ : P × ℝ → M} (hm : HasUnitPolarMetric I K Φ) (hK : 0 < K)
    (U : Opens M)
    (Q : Metric.sphere (0 : P) 1 × Ioo 0 (Real.pi / Real.sqrt K) ≃ₜ U)
    (hQ : ∀ q, (Q q : M) = Φ (q.1, q.2))
    (hDim : Module.finrank ℝ E = n + 1) :
    let F := Q.symm.trans (curvatureRoundPolarHomeomorph hK)
    ∃ T : M → RoundAmbient P,
      (∀ y : U, T (y : M) = ((F y).1 : RoundAmbient P) ∧
        MDifferentiableAt I 𝓘(ℝ, RoundAmbient P) T (y : M) ∧
        ∀ v w : TangentSpace I (y : M),
          inner ℝ (mfderiv I 𝓘(ℝ, RoundAmbient P) T (y : M) v)
            (mfderiv I 𝓘(ℝ, RoundAmbient P) T (y : M) w) = inner ℝ v w) ∧
      ∃ G : RoundAmbient P → M,
        ∀ x : RoundPuncturedSphere (1 / Real.sqrt K) (roundNorth : RoundAmbient P),
          G (x.1 : RoundAmbient P) = (F.symm x : M) ∧
          MDifferentiableAt 𝓘(ℝ, RoundAmbient P) I G (x.1 : RoundAmbient P) := by
  let : Nontrivial P := Module.nontrivial_of_finrank_eq_succ (R := ℝ)
    (show Module.finrank ℝ P = n + 1 from Fact.out)
  obtain ⟨u, hu⟩ := NormedSpace.sphere_nonempty (E := P) |>.mpr (show (0 : ℝ) ≤ 1 by norm_num)
  have hL : 0 < Real.pi / Real.sqrt K := div_pos Real.pi_pos (Real.sqrt_pos.mpr hK)
  let r : Ioo 0 (Real.pi / Real.sqrt K) :=
    ⟨(Real.pi / Real.sqrt K) / 2, by constructor <;> linarith⟩
  obtain ⟨e, hs, ht, he, hi, hd⟩ := hm.exists_differentiable_inverse hK U Q (⟨u, hu⟩, r) hQ hDim
  let Ψ := fun q : P × ℝ => roundPolarCurve (1 / Real.sqrt K)
    roundNorth (roundAngularInclusion q.1) q.2
  let Ψs := fun q : Metric.sphere (0 : P) 1 × ℝ => Ψ (q.1, q.2)
  let T := Ψs ∘ e.symm
  refine ⟨T, ?_, ?_⟩
  · intro y
    have hΨ : MDifferentiableAt 𝓘(ℝ, P × ℝ) 𝓘(ℝ, RoundAmbient P)
        Ψ ((e.symm (y : M)).1, (e.symm (y : M)).2) := by
      apply mdifferentiableAt_iff_differentiableAt.mpr
      dsimp only [Ψ, roundPolarCurve]
      fun_prop
    have hΨs : MDifferentiableAt ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, RoundAmbient P)
        Ψs (e.symm (y : M)) := mdifferentiableAt_sphere_polar_restriction _ _ hΨ
    have hTy := hΨs.comp (y : M) (hd y y.property)
    refine ⟨?_, hTy, ?_⟩
    · change Ψs (e.symm (y : M)) = _
      rw [hi y]
      exact (curvatureRoundPolarHomeomorph_apply hK (Q.symm y)).symm
    · let q := Q.symm y
      have hqy : Φ ((q.1 : P), (q.2 : ℝ)) = (y : M) := by
        rw [← hQ q]
        exact congrArg (fun z : U => (z : M)) (Q.apply_symm_apply y)
      have hTq : MDifferentiableAt I 𝓘(ℝ, RoundAmbient P) T (Φ ((q.1 : P), (q.2 : ℝ))) := by
        rw [hqy]
        exact hTy
      have hΨq : MDifferentiableAt 𝓘(ℝ, P × ℝ) 𝓘(ℝ, RoundAmbient P)
          Ψ ((q.1 : P), (q.2 : ℝ)) := by
        apply mdifferentiableAt_iff_differentiableAt.mpr
        dsimp only [Ψ, roundPolarCurve]
        fun_prop
      have hsource : (q.1, (q.2 : ℝ)) ∈ e.source := by rw [hs]; exact q.2.property
      have hlocal : (fun b : Metric.sphere (0 : P) 1 × ℝ => T (Φ (b.1, b.2)))
          =ᶠ[𝓝 (q.1, (q.2 : ℝ))] Ψs := by
        filter_upwards [e.open_source.mem_nhds hsource] with b hb
        change Ψs (e.symm (Φ (b.1, b.2))) = Ψs b
        rw [← he b hb, e.left_inv hb]
      have hinj : Set.InjOn (mfderiv 𝓘(ℝ, P × ℝ) I Φ ((q.1 : P), (q.2 : ℝ)))
          {z : P × ℝ | inner ℝ (q.1 : P) z.1 = 0} := by
        apply polar_derivative_injOn _ (obata_polar_coefficient_pos hK q.2.property)
        intro v hv t
        exact (hm q.1 q.2 q.2.property).2 v v hv hv t t
      have hmetric := polar_comparison_derivative_inner q.1 (q.2 : ℝ) hDim
        (hm q.1 q.2 q.2.property).1 hΨq hTq hinj
        (by
          intro w v hw hv s t
          rw [mfderiv_eq_fderiv]
          exact ((hm q.1 q.2 q.2.property).2 w v hw hv s t).trans
            (intrinsicRoundPolar_metric hK (q.1 : P) w v
              (mem_sphere_zero_iff_norm.mp q.1.property) hw hv q.2 s t).symm)
        hlocal
      change ∀ v w : TangentSpace I (Φ ((q.1 : P), (q.2 : ℝ))),
        inner ℝ (mfderiv I 𝓘(ℝ, RoundAmbient P) T (Φ ((q.1 : P), (q.2 : ℝ))) v)
          (mfderiv I 𝓘(ℝ, RoundAmbient P) T (Φ ((q.1 : P), (q.2 : ℝ))) w) = inner ℝ v w at hmetric
      rw [hqy] at hmetric
      exact hmetric
  · let G := Φ ∘ intrinsicRoundInverseCoordinates (1 / Real.sqrt K)
    refine ⟨G, ?_⟩
    intro x
    let q := (curvatureRoundPolarHomeomorph hK).symm x
    have hcoord := intrinsicRoundInverseCoordinates_eq_inverse hK x
    have hΦ : MDifferentiableAt 𝓘(ℝ, P × ℝ) I Φ
        (intrinsicRoundInverseCoordinates (1 / Real.sqrt K) (x.1 : RoundAmbient P)) := by
      rw [hcoord]
      exact (hm q.1 q.2 q.2.property).1
    have hD := (contDiffAt_intrinsicRoundInverseCoordinates hK x).differentiableAt (by norm_num)
    refine ⟨?_, hΦ.comp (x.1 : RoundAmbient P)
      (mdifferentiableAt_iff_differentiableAt.mpr hD)⟩
    change Φ (intrinsicRoundInverseCoordinates (1 / Real.sqrt K) (x.1 : RoundAmbient P)) = (Q q : M)
    rw [hcoord]
    exact (hQ q).symm

end LichnerowiczObata
