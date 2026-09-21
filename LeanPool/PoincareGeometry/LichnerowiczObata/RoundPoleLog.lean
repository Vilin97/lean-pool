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

public import LeanPool.PoincareGeometry.LichnerowiczObata.SmoothRoundPoleLog
public import LeanPool.PoincareGeometry.LichnerowiczObata.NormalChartRadialFlow
public import LeanPool.PoincareGeometry.LichnerowiczObata.IntrinsicRoundInverse
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-! # Smooth ambient inverse extensions at the north pole -/

@[expose] public noncomputable section
open Bundle Set Filter Asymptotics
open scoped Topology Manifold ContDiff
namespace LichnerowiczObata
variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]

/-- A smooth Cartesian pole model gives a smooth ambient extension of
the inverse comparison at the north pole, agreeing with every sufficiently
short actual round polar ray. No south-pole regularity is assumed. -/
theorem HasRadialPoleModel.exists_round_north_extension [CompleteSpace P]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [Bundle.RiemannianBundle (TangentSpace I : M → Type _)]
    {Φ : P × ℝ → M} {p : M} (hmodel : HasRadialPoleModel I Φ p)
    {R : ℝ} (hR : 0 < R) :
    ∃ G : RoundAmbient P → M,
      G (R • roundNorth) = p ∧
      ContMDiffAt 𝓘(ℝ, RoundAmbient P) I ∞ G (R • roundNorth) ∧
      (∀ v w : P,
        inner ℝ (mfderiv 𝓘(ℝ, RoundAmbient P) I G (R • roundNorth) (roundAngularInclusion v))
          (mfderiv 𝓘(ℝ, RoundAmbient P) I G (R • roundNorth) (roundAngularInclusion w)) = inner ℝ v w) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ u : Metric.sphere (0 : P) 1, ∀ r ∈ Ioo 0 δ,
        G (roundPolarCurve R roundNorth (roundAngularInclusion u) r) = Φ (u, r) := by
  obtain ⟨χ, hχ0, hχ, hχmetric, δ, hδ, hpolar⟩ := hmodel
  let A := WithLp.fstL 2 ℝ P ℝ
  let G := χ ∘ roundPoleLog R ∘ A
  have hA : A (R • roundNorth) = 0 := by simp [A, roundNorth]
  refine ⟨G, ?_, ?_, ?_, min δ (Real.pi * R / 2),
    lt_min hδ (div_pos (mul_pos Real.pi_pos hR) (by norm_num)), ?_⟩
  · change χ (roundPoleLog R (A (R • roundNorth))) = p
    rw [hA, roundPoleLog_zero, hχ0]
  · have hlog : ContMDiffAt 𝓘(ℝ, P) 𝓘(ℝ, P) ∞ (roundPoleLog R)
        (A (R • roundNorth)) := by
      rw [hA]
      exact contMDiffAt_iff_contDiffAt.mpr (contDiffAt_roundPoleLog_zero hR)
    have hc : ContMDiffAt 𝓘(ℝ, P) I ∞ χ (roundPoleLog R (A (R • roundNorth))) := by
      rw [hA, roundPoleLog_zero]
      exact hχ
    exact hc.comp (f := roundPoleLog R ∘ A) (R • roundNorth)
      (hlog.comp _ (contMDiffAt_iff_contDiffAt.mpr A.contDiff.contDiffAt))
  · let B := roundPoleLog R ∘ A
    have hB0 : B (R • roundNorth) = 0 := by
      change roundPoleLog R (A (R • roundNorth)) = 0
      rw [hA, roundPoleLog_zero]
    have hl : HasFDerivAt (roundPoleLog R) (ContinuousLinearMap.id ℝ P) (A (R • roundNorth)) := by
      rw [hA]
      exact hasFDerivAt_roundPoleLog_zero R
    have hB : HasFDerivAt B A (R • roundNorth) := by
      simpa only [ContinuousLinearMap.id_comp] using hl.comp (R • roundNorth) A.hasFDerivAt
    have hBm : MDifferentiableAt 𝓘(ℝ, RoundAmbient P) 𝓘(ℝ, P) B (R • roundNorth) :=
      mdifferentiableAt_iff_differentiableAt.mpr hB.differentiableAt
    have hc : MDifferentiableAt 𝓘(ℝ, P) I χ (B (R • roundNorth)) := by
      rw [hB0]
      exact hχ.mdifferentiableAt (by norm_num)
    have hm : ∀ v w : P, inner ℝ (mfderiv 𝓘(ℝ, P) I χ (B (R • roundNorth)) v)
        (mfderiv 𝓘(ℝ, P) I χ (B (R • roundNorth)) w) = inner ℝ v w := by
      rw [hB0]
      exact hχmetric
    have hBA (v : P) : mfderiv 𝓘(ℝ, RoundAmbient P) 𝓘(ℝ, P) B (R • roundNorth)
        (roundAngularInclusion v) = v := by
      rw [mfderiv_eq_fderiv, hB.fderiv]
      rfl
    intro v w
    change inner ℝ (mfderiv 𝓘(ℝ, RoundAmbient P) I (χ ∘ B) (R • roundNorth) (roundAngularInclusion v))
      (mfderiv 𝓘(ℝ, RoundAmbient P) I (χ ∘ B) (R • roundNorth) (roundAngularInclusion w)) = _
    rw [mfderiv_comp_apply _ hc hBm, mfderiv_comp_apply _ hc hBm, hBA, hBA]
    exact hm v w
  · intro u r hr
    change χ (roundPoleLog R (A (roundPolarCurve R roundNorth (roundAngularInclusion u) r))) = _
    rw [roundPoleLog_polar_projection hR (u : P) (mem_sphere_zero_iff_norm.mp u.2)
      ⟨hr.1, lt_of_lt_of_le hr.2 (min_le_right _ _)⟩]
    exact (hpolar u r ⟨hr.1, lt_of_lt_of_le hr.2 (min_le_left _ _)⟩).symm

/-- A north-pole extension attached to one specified regular comparison. -/
def HasRoundNorthInverseExtension
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [Bundle.RiemannianBundle (TangentSpace I : M → Type _)]
    (K : ℝ) {U : Set M}
    (F : U ≃ₜ RoundPuncturedSphere (1 / Real.sqrt K) (roundNorth : RoundAmbient P))
    (p : M) : Prop :=
  ∃ N : RoundAmbient P → M,
    N ((1 / Real.sqrt K) • roundNorth) = p ∧
    ContMDiffAt 𝓘(ℝ, RoundAmbient P) I ∞ N ((1 / Real.sqrt K) • roundNorth) ∧
    (∀ v w : P,
      inner ℝ (mfderiv 𝓘(ℝ, RoundAmbient P) I N ((1 / Real.sqrt K) • roundNorth) (roundAngularInclusion v))
        (mfderiv 𝓘(ℝ, RoundAmbient P) I N ((1 / Real.sqrt K) • roundNorth) (roundAngularInclusion w)) = inner ℝ v w) ∧
    ∃ δ : ℝ, 0 < δ ∧
      ∀ x : RoundPuncturedSphere (1 / Real.sqrt K) (roundNorth : RoundAmbient P),
        (intrinsicRoundInverseCoordinates (1 / Real.sqrt K) (x.1 : RoundAmbient P)).2 < δ →
          N (x.1 : RoundAmbient P) = (F.symm x : M)

/-- The pole model belongs to the exact comparison obtained from its
polar homeomorphism, so it can be carried with that map's metric properties. -/
theorem HasRadialPoleModel.round_north_inverse_extension [CompleteSpace P]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [Bundle.RiemannianBundle (TangentSpace I : M → Type _)]
    {Φ : P × ℝ → M} {p : M} (hmodel : HasRadialPoleModel I Φ p)
    {K : ℝ} (hK : 0 < K) {U : Set M}
    (Q : Metric.sphere (0 : P) 1 × Ioo 0 (Real.pi / Real.sqrt K) ≃ₜ U)
    (hQ : ∀ q, (Q q : M) = Φ (q.1, q.2)) :
    HasRoundNorthInverseExtension I K (Q.symm.trans (curvatureRoundPolarHomeomorph hK)) p := by
  obtain ⟨N, hN0, hNd, hNm, δ, hδ, hN⟩ := hmodel.exists_round_north_extension
    (one_div_pos.mpr (Real.sqrt_pos.mpr hK))
  refine ⟨N, hN0, hNd, hNm, δ, hδ, ?_⟩
  intro x hx
  let q := (curvatureRoundPolarHomeomorph hK).symm x
  have hpoint : (x.1 : RoundAmbient P) =
      roundPolarCurve (1 / Real.sqrt K) roundNorth (roundAngularInclusion (q.1 : P)) q.2 := by
    simpa only [q, Homeomorph.apply_symm_apply] using curvatureRoundPolarHomeomorph_apply hK q
  have hcoords := intrinsicRoundInverseCoordinates_eq_inverse hK x
  have hrδ : (q.2 : ℝ) < δ := by
    have hh : (intrinsicRoundInverseCoordinates (1 / Real.sqrt K) (x.1 : RoundAmbient P)).2 =
        (q.2 : ℝ) := congrArg Prod.snd hcoords
    rw [← hh]
    exact hx
  change N (x.1 : RoundAmbient P) = (Q q : M)
  rw [hpoint]
  exact (hN q.1 q.2 ⟨q.2.property.1, hrδ⟩).trans (hQ q).symm

end LichnerowiczObata
