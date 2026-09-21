/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.TwoPointExtension
public import LeanPool.PoincareGeometry.LichnerowiczObata.RoundComparisonPoleLimits

/-! # Extending the punctured round comparison over both poles -/

@[expose] public noncomputable section
open Set Filter
open scoped Topology
namespace LichnerowiczObata
variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]

def roundNorthPoint {R : ℝ} (hR : 0 < R) : Metric.sphere (0 : RoundAmbient P) R :=
  ⟨R • roundNorth, by
    rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_of_pos hR,
      roundNorth_norm, mul_one]⟩

def roundSouthPoint {R : ℝ} (hR : 0 < R) : Metric.sphere (0 : RoundAmbient P) R :=
  ⟨-(R • roundNorth), by
    rw [mem_sphere_zero_iff_norm, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hR,
      roundNorth_norm, mul_one]⟩

theorem roundNorthPoint_ne_southPoint {R : ℝ} (hR : 0 < R) :
    roundNorthPoint (P := P) hR ≠ roundSouthPoint hR := by
  intro he
  have hh := congrArg (fun x : Metric.sphere (0 : RoundAmbient P) R =>
    inner ℝ roundNorth (x : RoundAmbient P)) he
  change inner ℝ (roundNorth : RoundAmbient P) (R • roundNorth) =
    inner ℝ roundNorth (-(R • roundNorth)) at hh
  rw [inner_neg_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
    roundNorth_norm] at hh
  norm_num at hh
  linarith

/-- Filling in the two limiting pole values extends a punctured round
comparison to a global homeomorphism. The conclusion retains the original
comparison on every regular sphere point. This is a topological result. -/
theorem exists_round_comparison_extension [FiniteDimensional ℝ P]
    {M : Type*} [TopologicalSpace M] [T2Space M]
    {R : ℝ} (hR : 0 < R) {U : Set M} (p q : M) (hpq : p ≠ q)
    (hU : U = {x : M | x ≠ p ∧ x ≠ q})
    (F : U ≃ₜ RoundPuncturedSphere R (roundNorth : RoundAmbient P))
    (G : RoundAmbient P → M)
    (hG : ∀ x : RoundPuncturedSphere R (roundNorth : RoundAmbient P),
      G (x.1 : RoundAmbient P) = (F.symm x : M))
    (hGc : ∀ x : RoundPuncturedSphere R (roundNorth : RoundAmbient P),
      ContinuousAt G (x.1 : RoundAmbient P))
    (hN : Tendsto (fun x => (F.symm x : M))
      (Filter.comap (fun x : RoundPuncturedSphere R (roundNorth : RoundAmbient P) =>
        (x.1 : RoundAmbient P)) (𝓝 (R • roundNorth))) (𝓝 p))
    (hS : Tendsto (fun x => (F.symm x : M))
      (Filter.comap (fun x : RoundPuncturedSphere R (roundNorth : RoundAmbient P) =>
        (x.1 : RoundAmbient P)) (𝓝 (-R • roundNorth))) (𝓝 q)) :
    ∃ H : Metric.sphere (0 : RoundAmbient P) R ≃ₜ M,
      H (roundNorthPoint hR) = p ∧ H (roundSouthPoint hR) = q ∧
      ∀ x : RoundPuncturedSphere R (roundNorth : RoundAmbient P),
        H x.1 = (F.symm x : M) := by
  let N := roundNorthPoint (P := P) hR
  let S := roundSouthPoint (P := P) hR
  have hNS : N ≠ S := roundNorthPoint_ne_southPoint hR
  have hreg : {x : Metric.sphere (0 : RoundAmbient P) R | x ≠ N ∧ x ≠ S} =
      {x : Metric.sphere (0 : RoundAmbient P) R |
        (x : RoundAmbient P) ≠ R • roundNorth ∧ (x : RoundAmbient P) ≠ -(R • roundNorth)} := by
    ext x
    simp only [mem_ofPred_eq, ne_eq, Subtype.ext_iff]
    rfl
  let A := Homeomorph.setCongr hreg
  let E := A.trans (F.symm.trans (Homeomorph.setCongr hU))
  let g := fun x : Metric.sphere (0 : RoundAmbient P) R => G (x : RoundAmbient P)
  have he : ∀ x : {x : Metric.sphere (0 : RoundAmbient P) R // x ≠ N ∧ x ≠ S},
      g x = (E x : M) := fun x => hG (A x)
  have hc : ∀ x, x ≠ N → x ≠ S → ContinuousAt g x := by
    intro x hxN hxS
    exact (hGc (A ⟨x, hxN, hxS⟩)).comp continuous_subtype_val.continuousAt
  have hn : Tendsto (fun x : {x : Metric.sphere (0 : RoundAmbient P) R // x ≠ N ∧ x ≠ S} => g x)
      (Filter.comap Subtype.val (𝓝 N)) (𝓝 p) := by
    have hi : Tendsto (fun x : {x : Metric.sphere (0 : RoundAmbient P) R // x ≠ N ∧ x ≠ S} =>
        ((A x).1 : RoundAmbient P)) (Filter.comap Subtype.val (𝓝 N)) (𝓝 (R • roundNorth)) :=
      continuous_subtype_val.continuousAt.tendsto.comp tendsto_comap
    have ht := hN.comp (tendsto_comap_iff.mpr hi)
    exact ht.congr' (Eventually.of_forall (fun x => (hG (A x)).symm))
  have hs : Tendsto (fun x : {x : Metric.sphere (0 : RoundAmbient P) R // x ≠ N ∧ x ≠ S} => g x)
      (Filter.comap Subtype.val (𝓝 S)) (𝓝 q) := by
    have hi : Tendsto (fun x : {x : Metric.sphere (0 : RoundAmbient P) R // x ≠ N ∧ x ≠ S} =>
        ((A x).1 : RoundAmbient P)) (Filter.comap Subtype.val (𝓝 S)) (𝓝 (-R • roundNorth)) := by
      rw [neg_smul]
      exact continuous_subtype_val.continuousAt.tendsto.comp tendsto_comap
    have ht := hS.comp (tendsto_comap_iff.mpr hi)
    exact ht.congr' (Eventually.of_forall (fun x => (hG (A x)).symm))
  obtain ⟨H, hHN, hHS, hH⟩ := exists_twoPointExtension_homeomorph g hNS hpq E he hc hn hs
  refine ⟨H, hHN, hHS, ?_⟩
  intro x
  exact hH (A.symm x)

/-- Agreement on sufficiently small punctured radial levels, together
with agreement at the pole, gives agreement on a full sphere neighborhood. -/
theorem round_north_eventuallyEq_of_punctured
    {M : Type*} {R : ℝ} (hR : 0 < R)
    (H : Metric.sphere (0 : RoundAmbient P) R → M) (N : RoundAmbient P → M)
    (hN : N (R • roundNorth) = H (roundNorthPoint hR))
    {δ : ℝ} (hδ : 0 < δ)
    (hreg : ∀ x : RoundPuncturedSphere R (roundNorth : RoundAmbient P),
      (intrinsicRoundInverseCoordinates R (x.1 : RoundAmbient P)).2 < δ →
        N (x.1 : RoundAmbient P) = H x.1) :
    (fun x : Metric.sphere (0 : RoundAmbient P) R => N (x : RoundAmbient P)) =ᶠ[𝓝 (roundNorthPoint hR)] H := by
  have hρ0 : (intrinsicRoundInverseCoordinates R
      ((roundNorthPoint (P := P) hR).val)).2 = 0 := by
    change (intrinsicRoundInverseCoordinates R (R • (roundNorth : RoundAmbient P))).2 = 0
    exact intrinsicRoundInverse_radius_north (P := P) (R := R) hR
  have hρ : Tendsto (fun x : Metric.sphere (0 : RoundAmbient P) R =>
      (intrinsicRoundInverseCoordinates R (x : RoundAmbient P)).2)
      (𝓝 (roundNorthPoint hR)) (𝓝 0) := by
    rw [← hρ0]
    exact ((continuous_intrinsicRoundInverse_radius R).comp continuous_subtype_val).continuousAt.tendsto
  filter_upwards [hρ.eventually (gt_mem_nhds hδ),
    eventually_ne_nhds (roundNorthPoint_ne_southPoint (P := P) hR)] with x hx hxS
  by_cases hxN : x = roundNorthPoint hR
  · subst x
    exact hN
  · let y : RoundPuncturedSphere R (roundNorth : RoundAmbient P) :=
      ⟨x, fun he => hxN (Subtype.ext he), fun he => hxS (Subtype.ext he)⟩
    exact hreg y hx

/-- The analogous neighborhood agreement at the south pole is controlled
by the remaining polar radius, not by a fixed angular direction. -/
theorem round_south_eventuallyEq_of_punctured
    {M : Type*} {R : ℝ} (hR : 0 < R)
    (H : Metric.sphere (0 : RoundAmbient P) R → M) (N : RoundAmbient P → M)
    (hN : N (-(R • roundNorth)) = H (roundSouthPoint hR))
    {δ : ℝ} (hδ : 0 < δ)
    (hreg : ∀ x : RoundPuncturedSphere R (roundNorth : RoundAmbient P),
      Real.pi * R - (intrinsicRoundInverseCoordinates R (x.1 : RoundAmbient P)).2 < δ →
        N (x.1 : RoundAmbient P) = H x.1) :
    (fun x : Metric.sphere (0 : RoundAmbient P) R => N (x : RoundAmbient P)) =ᶠ[𝓝 (roundSouthPoint hR)] H := by
  have hρ0 : Real.pi * R - (intrinsicRoundInverseCoordinates R
      ((roundSouthPoint (P := P) hR).val)).2 = 0 := by
    change Real.pi * R - (intrinsicRoundInverseCoordinates R (-(R • (roundNorth : RoundAmbient P)))).2 = 0
    rw [← neg_smul, intrinsicRoundInverse_radius_south hR, sub_self]
  have hρ : Tendsto (fun x : Metric.sphere (0 : RoundAmbient P) R =>
      Real.pi * R - (intrinsicRoundInverseCoordinates R (x : RoundAmbient P)).2)
      (𝓝 (roundSouthPoint hR)) (𝓝 0) := by
    rw [← hρ0]
    exact (continuous_const.sub
      ((continuous_intrinsicRoundInverse_radius R).comp continuous_subtype_val)).continuousAt.tendsto
  filter_upwards [hρ.eventually (gt_mem_nhds hδ),
    eventually_ne_nhds (roundNorthPoint_ne_southPoint (P := P) hR).symm] with x hx hxN
  by_cases hxS : x = roundSouthPoint hR
  · subst x
    exact hN
  · let y : RoundPuncturedSphere R (roundNorth : RoundAmbient P) :=
      ⟨x, fun he => hxN (Subtype.ext he), fun he => hxS (Subtype.ext he)⟩
    exact hreg y hx

end LichnerowiczObata
