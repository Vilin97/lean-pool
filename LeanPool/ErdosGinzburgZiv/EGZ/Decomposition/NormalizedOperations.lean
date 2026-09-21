/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.NormalizedFace
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.NormalizedGap
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.NormalizedComplete

/-!
# Uniform providers for normalized refinement operations

The three concrete operations share a single increasing radius bound and a
monotone prime threshold. A finite radius horizon therefore fixes the prime
before any choices in the refinement run are made.
-/

namespace EGZ

open FlagDecomposition

variable {p d : ℕ} [NeZero p] [Fact p.Prime] {f : FpCoord p d → ℕ}

/-- Concrete chart data for a normalized face operation. -/
structure NormalizedFaceStep (Φ : FlagDecomposition p d f) (anchor : Φ.flag.Node)
    (Γ : (Φ.flag.polytope anchor).Face) (K R : ℕ) where
  odd : Odd p
  /-- Integer lattice charts for the lifted supports of the face-refined decomposition. -/
  charts : ∀ x, IntegerLatticeChart
    ((FaceRefinement.decomposition Φ anchor (Φ.faceSelector anchor Γ) odd).liftedSupport x)
  modInjective : ∀ x, Function.Injective ((Rechart.chart
    (FaceRefinement.decomposition Φ anchor (Φ.faceSelector anchor Γ) odd) charts x).modp p)
  centered : ∀ x q, q ∈ (charts x).coordinateSupport → IsCenteredLift p q
  /-- The radius of the normalized face step, bounded between `K` and `R`. -/
  radius : ℕ
  radius_ge : K ≤ radius
  radius_le : radius ≤ R
  bounded : (FaceRefinement.normalized Φ anchor Γ odd charts modInjective centered).IsKBounded
    (fun _ ↦ radius)

/-- The normalized decomposition supplied by a face step. -/
noncomputable abbrev NormalizedFaceStep.decomposition
    {Φ : FlagDecomposition p d f} {anchor : Φ.flag.Node}
    {Γ : (Φ.flag.polytope anchor).Face} {K R : ℕ} (D : NormalizedFaceStep Φ anchor Γ K R) :=
  FaceRefinement.normalized Φ anchor Γ D.odd D.charts D.modInjective D.centered

/-- Concrete deletion and chart data for normalized gap cleanup. -/
structure NormalizedGapStep (Φ : FlagDecomposition p d f) (K R : ℕ) (α : ℝ) where
  /-- The pruned weights used to correct the gap condition. -/
  weights : PrunedWeights Φ
  odd : Odd p
  /-- Integer lattice charts for the supports remaining after cleaning the pruned weights. -/
  charts : ∀ x, IntegerLatticeChart ((weights.cleaned odd).liftedSupport x)
  modInjective : ∀ x, Function.Injective ((Rechart.chart (weights.cleaned odd) charts x).modp p)
  centered : ∀ x q, q ∈ (charts x).coordinateSupport → IsCenteredLift p q
  /-- The radius of the normalized gap step, bounded between `K` and `R`. -/
  radius : ℕ
  radius_ge : K ≤ radius
  radius_le : radius ≤ R
  atoms : ∀ x v, weights.weight x v = 0 ∨ weights.weight x v = Φ.localWeight x v
  bounded : (weights.normalized odd charts modInjective centered).IsKBounded (fun _ ↦ radius)
  mass_loss : (Φ.retainedMass : ℝ) -
    (weights.normalized odd charts modInjective centered).retainedMass ≤ α * Φ.retainedMass
  gap_bound : ∀ x, α * (Φ.retainedMass : ℝ) /
    ((Fintype.card Φ.flag.Node : ℝ) * (2 * (radius : ℝ) + 1) ^ d) ≤
      ((weights.normalized odd charts modInjective centered).gap x : ℝ)

/-- The normalized decomposition supplied by a gap step. -/
noncomputable abbrev NormalizedGapStep.decomposition
    {Φ : FlagDecomposition p d f} {K R : ℕ} {α : ℝ} (D : NormalizedGapStep Φ K R α) :=
  D.weights.normalized D.odd D.charts D.modInjective D.centered

/-- Concrete selected directions, active nodes, and charts for a normalized
complete-element operation. -/
structure NormalizedCompleteStep (Φ : FlagDecomposition p d f) (anchor : Φ.flag.Node)
    (g : ℕ → ℕ) (K R : ℕ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hsmall : (3 : ℝ) ^ (d + 1) * δ < 1) where
  odd : Odd p
  /-- The width bound chosen for each dimension during complete preparation. -/
  widths : ℕ → ℕ
  /-- The data preparing the anchor for the completeness refinement. -/
  preparation : CompletePreparation Φ anchor widths δ
  /-- Integer lattice charts for the supports in the prepared completion diagram. -/
  charts : ∀ x, IntegerLatticeChart ((preparation.diagram odd hδ hsmall).support x)
  modInjective : ∀ x, Function.Injective ((IntegralAffineMap.ofIntAffineMap (charts x).map).modp p)
  centered : ∀ x q, q ∈ (charts x).coordinateSupport → IsCenteredLift p q
  /-- The radius of the normalized completion step, bounded between `K` and `R`. -/
  radius : ℕ
  radius_ge : K ≤ radius
  radius_le : radius ≤ R
  widths_monotone : Monotone widths
  widths_zero : widths 0 = K
  desired_width : g radius ≤ widths (preparation.count + 1)
  bounded : (preparation.normalized odd hδ hsmall charts modInjective centered).IsKBounded
    (fun _ ↦ radius)

/-- The normalized decomposition supplied by a completion step. -/
noncomputable abbrev NormalizedCompleteStep.decomposition
    {Φ : FlagDecomposition p d f} {anchor : Φ.flag.Node}
    {g : ℕ → ℕ} {K R : ℕ} {δ : ℝ} {hδ : 0 ≤ δ}
    {hsmall : (3 : ℝ) ^ (d + 1) * δ < 1}
    (D : NormalizedCompleteStep Φ anchor g K R δ hδ hsmall) :=
  D.preparation.normalized D.odd hδ hsmall D.charts D.modInjective D.centered

namespace NormalizedFaceStep

variable {Φ : FlagDecomposition p d f} {anchor : Φ.flag.Node}
    {Γ : (Φ.flag.polytope anchor).Face} {K R : ℕ} (D : NormalizedFaceStep Φ anchor Γ K R)

theorem isMinimal : D.decomposition.IsMinimal :=
  FaceRefinement.normalized_isMinimal Φ anchor Γ D.odd D.charts D.modInjective D.centered

theorem isReduced : D.decomposition.IsReduced :=
  FaceRefinement.normalized_isReduced Φ anchor Γ D.odd D.charts D.modInjective D.centered

theorem retainedMass : D.decomposition.retainedMass = Φ.retainedMass :=
  FaceRefinement.normalized_retainedMass Φ anchor Γ D.odd D.charts D.modInjective D.centered

theorem card_le : @Fintype.card D.decomposition.flag.Node D.decomposition.flag.nodeFintype ≤
    2 * Fintype.card Φ.flag.Node :=
  FaceRefinement.normalized_card_le Φ anchor Γ D.odd D.charts D.modInjective D.centered

/-- The subdivision map carried by the normalized face step. -/
noncomputable def subdivisionMap : SubdivisionMap Φ D.decomposition :=
  FaceRefinement.normalizedSubdivisionMap Φ anchor Γ D.odd D.charts D.modInjective D.centered

/-- The retained target node of the normalized face step. -/
noncomputable abbrev targetNode (hΓ : Γ ≠ ⊤) (hred : Φ.IsReducedElement anchor) :
    D.decomposition.flag.Node :=
  FaceRefinement.normalizedTargetNode Φ anchor Γ D.odd D.charts D.modInjective D.centered hΓ hred

/-- The target face of the normalized face step in its new coordinates. -/
noncomputable def targetFace (hΓ : Γ ≠ ⊤) (hred : Φ.IsReducedElement anchor) :
    (D.decomposition.flag.polytope (D.targetNode hΓ hred)).Face :=
  FaceRefinement.normalizedTargetFace Φ anchor Γ D.odd D.charts D.modInjective D.centered hΓ hred

theorem target_isRealized (hΓ : Γ ≠ ⊤) (hred : Φ.IsReducedElement anchor) :
    D.decomposition.IsRealizedFace (D.targetNode hΓ hred) (D.targetFace hΓ hred) :=
  FaceRefinement.normalizedTargetFace_isRealized Φ anchor Γ D.odd D.charts D.modInjective
    D.centered hΓ hred

theorem target_projection (hΓ : Γ ≠ ⊤) (hred : Φ.IsReducedElement anchor) :
    D.subdivisionMap.node (D.targetNode hΓ hred) = anchor := rfl

theorem targetFace_carrier (hΓ : Γ ≠ ⊤) (hred : Φ.IsReducedElement anchor) :
    (D.targetFace hΓ hred).carrier =
      (D.decomposition.flag.polytope (D.targetNode hΓ hred)).carrier ∩
        D.subdivisionMap.fibre (D.targetNode hΓ hred) ⁻¹' Γ.carrier := rfl

end NormalizedFaceStep

namespace NormalizedGapStep

variable {Φ : FlagDecomposition p d f} {K R : ℕ} {α : ℝ} (D : NormalizedGapStep Φ K R α)

theorem isMinimal : D.decomposition.IsMinimal :=
  D.weights.normalized_isMinimal D.odd D.charts D.modInjective D.centered

theorem isReduced : D.decomposition.IsReduced :=
  D.weights.normalized_isReduced D.odd D.charts D.modInjective D.centered

theorem card_le : @Fintype.card D.decomposition.flag.Node D.decomposition.flag.nodeFintype ≤
    Fintype.card Φ.flag.Node :=
  D.weights.normalized_card_le D.odd D.charts D.modInjective D.centered

/-- The subdivision map carried by the normalized gap step. -/
noncomputable def subdivisionMap : SubdivisionMap Φ D.decomposition :=
  D.weights.normalizedSubdivisionMap D.odd D.charts D.modInjective D.centered

end NormalizedGapStep

namespace NormalizedCompleteStep

variable {Φ : FlagDecomposition p d f} {anchor : Φ.flag.Node}
    {g : ℕ → ℕ} {K R : ℕ} {δ : ℝ} {hδ : 0 ≤ δ}
    {hsmall : (3 : ℝ) ^ (d + 1) * δ < 1}
    (D : NormalizedCompleteStep Φ anchor g K R δ hδ hsmall)

theorem isMinimal : D.decomposition.IsMinimal :=
  D.preparation.normalized_isMinimal D.odd hδ hsmall D.charts D.modInjective D.centered

theorem isReduced : D.decomposition.IsReduced :=
  D.preparation.normalized_isReduced D.odd hδ hsmall D.charts D.modInjective D.centered

theorem mass_loss : (Φ.retainedMass : ℝ) - D.decomposition.retainedMass ≤
    (3 : ℝ) ^ (d + 1) * δ * natMass (Φ.cumulativeWeight anchor) :=
  D.preparation.normalized_retainedMass_loss_le D.odd hδ hsmall D.charts D.modInjective D.centered

theorem card_le : @Fintype.card D.decomposition.flag.Node D.decomposition.flag.nodeFintype ≤
    2 * Fintype.card Φ.flag.Node :=
  D.preparation.normalized_card_le D.odd hδ hsmall D.charts D.modInjective D.centered

/-- The subdivision map carried by the normalized completion step. -/
noncomputable def subdivisionMap : SubdivisionMap Φ D.decomposition :=
  D.preparation.normalizedSubdivisionMap D.odd hδ hsmall D.charts D.modInjective D.centered

/-- The distinguished complete node of the normalized completion step. -/
noncomputable abbrev targetNode : D.decomposition.flag.Node :=
  D.preparation.normalizedCompleteNode D.odd hδ hsmall D.charts D.modInjective D.centered

theorem target_isComplete : D.decomposition.IsCompleteElement D.targetNode (g D.radius) δ :=
  (D.preparation.normalizedCompleteNode_isCompleteElement D.odd hδ hsmall D.charts
    D.modInjective D.centered).mono_width D.desired_width

theorem target_cumulativeWeight : D.decomposition.cumulativeWeight D.targetNode =
    restrictWeight (Φ.cumulativeWeight anchor) D.preparation.selectedSet :=
  D.preparation.normalizedCompleteNode_cumulativeWeight D.odd hδ hsmall D.charts
    D.modInjective D.centered

theorem node_ne_upperAnchor (x : D.decomposition.flag.Node) :
    x.val ≠ D.preparation.upperAnchor D.odd hδ hsmall :=
  D.preparation.normalized_node_ne_upperAnchor D.odd hδ hsmall D.charts D.modInjective D.centered x

end NormalizedCompleteStep

/-- Uniform numerical parameters together with providers of all three
concrete normalized operations. -/
structure NormalizedOperationParameters (d : ℕ) (g : ℕ → ℕ) where
  /-- A uniform bound on the radius after one normalized operation. -/
  radiusGrowth : ℕ → ℕ
  radiusGrowth_growing : IsGrowing radiusGrowth
  /-- The prime threshold ensuring normalized operations exist at the specified radius. -/
  primeThreshold : ℕ → ℕ
  primeThreshold_monotone : Monotone primeThreshold
  primeThreshold_ge_two : ∀ K, 2 ≤ primeThreshold K
  face : ∀ K (p : ℕ) [NeZero p] [Fact p.Prime], primeThreshold K < p →
    ∀ (f : FpCoord p d → ℕ) (Φ : FlagDecomposition p d f)
      (anchor : Φ.flag.Node) (Γ : (Φ.flag.polytope anchor).Face), Γ ≠ ⊤ →
      Φ.IsReducedElement anchor → Φ.IsKBounded (fun _ ↦ K) →
      Nonempty (NormalizedFaceStep Φ anchor Γ K (radiusGrowth K))
  gap : ∀ K (p : ℕ) [NeZero p] [Fact p.Prime], primeThreshold K < p →
    ∀ (f : FpCoord p d → ℕ) (Φ : FlagDecomposition p d f),
      Φ.IsKBounded (fun _ ↦ K) → ∀ α : ℝ, 0 ≤ α → α < 1 →
      Nonempty (NormalizedGapStep Φ K (radiusGrowth K) α)
  complete : ∀ K (p : ℕ) [NeZero p] [Fact p.Prime], primeThreshold K < p →
    ∀ (f : FpCoord p d → ℕ) (Φ : FlagDecomposition p d f) (anchor : Φ.flag.Node)
      (δ : ℝ) (hδ : 0 ≤ δ) (hsmall : (3 : ℝ) ^ (d + 1) * δ < 1),
      Φ.IsKBounded (fun _ ↦ K) →
      Nonempty (NormalizedCompleteStep Φ anchor g K (radiusGrowth K) δ hδ hsmall)

/-- Monotone majorant of a numerical threshold, taking a finite maximum
over all smaller radii. -/
def thresholdEnvelope (q : ℕ → ℕ) (K : ℕ) : ℕ := (Finset.range (K + 1)).sup q

theorem le_thresholdEnvelope (q : ℕ → ℕ) (K : ℕ) : q K ≤ thresholdEnvelope q K :=
  Finset.le_sup (Finset.mem_range.mpr (Nat.lt_succ_self K))

theorem thresholdEnvelope_monotone (q : ℕ → ℕ) : Monotone (thresholdEnvelope q) := by
  intro a b hab
  apply Finset.sup_mono
  exact Finset.range_mono (Nat.add_le_add_right hab 1)

theorem exists_normalizedOperationParameters (d : ℕ) (g : ℕ → ℕ) (hg : Monotone g) :
    Nonempty (NormalizedOperationParameters d g) := by
  classical
  obtain ⟨A, hAmono, hAge, hA⟩ := normalized_face_refinement_lemma d
  obtain ⟨B, hBmono, hBge, hB⟩ := normalized_gap_cleanup_lemma d
  obtain ⟨C, hCmono, hCge, hC⟩ := normalized_complete_refinement_lemma d g hg
  let H : ℕ → ℕ := fun K ↦ max (K + 1) (max (A K) (max (B K) (C K)))
  have hH : IsGrowing H := by
    constructor
    · intro i j hij
      exact max_le_max (Nat.add_le_add_right hij 1)
        (max_le_max (hAmono hij) (max_le_max (hBmono hij) (hCmono hij)))
    · intro i
      exact (Nat.lt_succ_self i).trans_le (le_max_left _ _)
  have hAH : ∀ K, A K ≤ H K := fun K ↦ (le_max_left _ _).trans (le_max_right _ _)
  have hBH : ∀ K, B K ≤ H K := fun K ↦
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hCH : ∀ K, C K ≤ H K := fun K ↦
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  let qA := fun K ↦ (hA K).choose
  let qB := fun K ↦ (hB K).choose
  let qC := fun K ↦ (hC K).choose
  let q := fun K ↦ max (qA K) (max (qB K) (qC K))
  let Q := thresholdEnvelope q
  have hAQ : ∀ K, qA K ≤ Q K := fun K ↦ (le_max_left _ _).trans (le_thresholdEnvelope q K)
  have hBQ : ∀ K, qB K ≤ Q K := fun K ↦
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_thresholdEnvelope q K))
  have hCQ : ∀ K, qC K ≤ Q K := fun K ↦
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_thresholdEnvelope q K))
  refine ⟨{
    radiusGrowth := H
    radiusGrowth_growing := hH
    primeThreshold := Q
    primeThreshold_monotone := thresholdEnvelope_monotone q
    primeThreshold_ge_two := fun K ↦ (hA K).choose_spec.1.trans (hAQ K)
    face := ?_
    gap := ?_
    complete := ?_ }⟩
  · intro K p _ _ hp f Φ anchor Γ hΓ hred hΦ
    obtain ⟨hp', charts, hmod, hcenter, _hmin, _hred, hbound, _hrest⟩ :=
      (hA K).choose_spec.2 p ((hAQ K).trans_lt hp) f Φ anchor Γ hΓ hred hΦ
    exact ⟨⟨hp', charts, hmod, hcenter, A K, hAge K, hAH K, hbound⟩⟩
  · intro K p _ _ hp f Φ hΦ α hα hαone
    obtain ⟨D, hp', charts, hmod, hcenter, hatoms, _hmin, _hred, hbound, _hcard, hmass, hgap⟩ :=
      (hB K).choose_spec.2 p ((hBQ K).trans_lt hp) f Φ (fun _ ↦ K) hΦ (fun _ ↦ le_rfl)
        α hα hαone
    exact ⟨⟨D, hp', charts, hmod, hcenter, B K, hBge K, hBH K, hatoms, hbound, hmass, hgap⟩⟩
  · intro K p _ _ hp f Φ anchor δ hδ hsmall hΦ
    obtain ⟨hp', t, D, charts, hmod, hcenter, b, hKb, hbC, ht, ht0, hgb,
      _hmin, _hred, hbound, _hrest⟩ :=
      (hC K).choose_spec.2 p ((hCQ K).trans_lt hp) f Φ anchor δ hδ hsmall hΦ
    exact ⟨⟨hp', t, D, charts, hmod, hcenter, b, hKb, hbC.trans (hCH K), ht, ht0, hgb, hbound⟩⟩

/-- Choose uniform radius and prime bounds together with providers of the normalized
operations. -/
noncomputable def normalizedOperationParameters (d : ℕ) (g : ℕ → ℕ) (hg : Monotone g) :
    NormalizedOperationParameters d g :=
  Classical.choice (exists_normalizedOperationParameters d g hg)

namespace NormalizedOperationParameters

variable {d : ℕ} {g : ℕ → ℕ} (P : NormalizedOperationParameters d g)

theorem radiusGrowth_ge (K : ℕ) : K ≤ P.radiusGrowth K := (P.radiusGrowth_growing.2 K).le

/-- The radius bound obtained after `N` successive applications of the growth function. -/
def radiusHorizon (K N : ℕ) : ℕ := P.radiusGrowth^[N] K

/-- The prime threshold at the radius bound after `N` normalized operations. -/
def primeHorizon (K N : ℕ) : ℕ := P.primeThreshold (P.radiusHorizon K N)

theorem radius_sequence_le (r : ℕ → ℕ) {K : ℕ} (hstart : r 0 ≤ K)
    (hstep : ∀ i, r (i + 1) ≤ P.radiusGrowth (r i)) (i : ℕ) :
    r i ≤ P.radiusHorizon K i := by
  induction i with
  | zero => exact hstart
  | succ i hi =>
    change r (i + 1) ≤ P.radiusGrowth^[i + 1] K
    rw [Function.iterate_succ_apply']
    exact (hstep i).trans (P.radiusGrowth_growing.1 hi)

theorem radiusHorizon_monotone (K : ℕ) : Monotone (P.radiusHorizon K) := by
  intro i j hij
  exact Function.monotone_iterate_of_id_le P.radiusGrowth_ge hij K

/-- One prime chosen for the finite horizon works at every smaller radius,
including radii produced by arbitrary prior refinement choices. -/
theorem primeThreshold_lt_of_le_horizon {K N b p : ℕ}
    (hp : P.primeHorizon K N < p) (hb : b ≤ P.radiusHorizon K N) :
    P.primeThreshold b < p := (P.primeThreshold_monotone hb).trans_lt hp

theorem primeThreshold_lt_of_radius_sequence (r : ℕ → ℕ) {K N p : ℕ}
    (hp : P.primeHorizon K N < p) (hstart : r 0 ≤ K)
    (hstep : ∀ i, r (i + 1) ≤ P.radiusGrowth (r i)) {i : ℕ} (hi : i ≤ N) :
    P.primeThreshold (r i) < p :=
  P.primeThreshold_lt_of_le_horizon hp
    ((P.radius_sequence_le r hstart hstep i).trans (P.radiusHorizon_monotone K hi))

end NormalizedOperationParameters
end EGZ
