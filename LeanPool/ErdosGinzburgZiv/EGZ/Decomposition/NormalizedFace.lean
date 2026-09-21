/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.FaceSurvival
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Minimalization

/-!
# Minimal and reduced face refinements

Minimalizing the active face split and then restricting to reduced nodes
keeps the upper anchor for every proper selected face of a reduced old node.
This gives a normalized operation with unchanged mass and uniform bounds.
-/

namespace EGZ.FlagDecomposition.Rechart

variable {p d : ℕ} [NeZero p] [Fact p.Prime] {f : FpCoord p d → ℕ}
    (Φ : FlagDecomposition p d f) (C : ∀ x, IntegerLatticeChart (Φ.liftedSupport x))
    (hp : Odd p) (hmod : ∀ x, Function.Injective ((chart Φ C x).modp p))
    (hcenter : ∀ x q, q ∈ (C x).coordinateSupport → IsCenteredLift p q)

theorem decomposition_isReducedElement_iff (x : Φ.flag.Node) :
    (decomposition Φ C hp hmod hcenter).IsReducedElement x ↔ Φ.IsReducedElement x := by
  rw [(decomposition Φ C hp hmod hcenter).isReducedElement_iff_sup'_localWeight hp,
    Φ.isReducedElement_iff_sup'_localWeight hp]

end EGZ.FlagDecomposition.Rechart

namespace EGZ.FlagDecomposition.FaceRefinement

variable {p d : ℕ} [NeZero p] [Fact p.Prime] {f : FpCoord p d → ℕ}
    (Φ : FlagDecomposition p d f) (anchor : Φ.flag.Node)
    (Γ : (Φ.flag.polytope anchor).Face) (hp : Odd p)
    (C : ∀ x, IntegerLatticeChart
      ((decomposition Φ anchor (Φ.faceSelector anchor Γ) hp).liftedSupport x))
    (hmod : ∀ x, Function.Injective
      ((Rechart.chart (decomposition Φ anchor (Φ.faceSelector anchor Γ) hp) C x).modp p))
    (hcenter : ∀ x q, q ∈ (C x).coordinateSupport → IsCenteredLift p q)

/-- The face refinement expressed in minimal integer lattice charts. -/
noncomputable abbrev minimalized : FlagDecomposition p d f :=
  Rechart.decomposition (decomposition Φ anchor (Φ.faceSelector anchor Γ) hp) C hp hmod hcenter

/-- The minimalized face refinement after reduction. -/
noncomputable abbrev normalized : FlagDecomposition p d f :=
  (minimalized Φ anchor Γ hp C hmod hcenter).reduced hp

theorem minimalized_upperAnchor_isReduced (hΓ : Γ ≠ ⊤) (hred : Φ.IsReducedElement anchor) :
    (minimalized Φ anchor Γ hp C hmod hcenter).IsReducedElement
      (upper Φ anchor (Φ.faceSelector anchor Γ) hp anchor) :=
  (Rechart.decomposition_isReducedElement_iff _ _ _ _ _ _).mpr
    (face_upperAnchor_isReduced Φ anchor hp Γ hΓ hred)

/-- The retained upper copy of the anchor in the normalized face refinement. -/
noncomputable abbrev normalizedTargetNode (hΓ : Γ ≠ ⊤) (hred : Φ.IsReducedElement anchor) :
    (normalized Φ anchor Γ hp C hmod hcenter).flag.Node :=
  ⟨upper Φ anchor (Φ.faceSelector anchor Γ) hp anchor,
    minimalized_upperAnchor_isReduced Φ anchor Γ hp C hmod hcenter hΓ hred⟩

/-- The face corresponding to the original target face in normalized coordinates. -/
noncomputable def normalizedTargetFace (hΓ : Γ ≠ ⊤) (hred : Φ.IsReducedElement anchor) :
    ((normalized Φ anchor Γ hp C hmod hcenter).flag.polytope
      (normalizedTargetNode Φ anchor Γ hp C hmod hcenter hΓ hred)).Face :=
  (Rechart.subdivisionMap (decomposition Φ anchor (Φ.faceSelector anchor Γ) hp)
    C hp hmod hcenter).face (upper Φ anchor (Φ.faceSelector anchor Γ) hp anchor)
      (upperFace Φ anchor (Φ.faceSelector anchor Γ) hp anchor Γ)
      (Rechart.face_preimage_nonempty _ _ _ _)

theorem normalizedTargetFace_isRealized (hΓ : Γ ≠ ⊤) (hred : Φ.IsReducedElement anchor) :
    (normalized Φ anchor Γ hp C hmod hcenter).IsRealizedFace
      (normalizedTargetNode Φ anchor Γ hp C hmod hcenter hΓ hred)
      (normalizedTargetFace Φ anchor Γ hp C hmod hcenter hΓ hred) := by
  apply ((minimalized Φ anchor Γ hp C hmod hcenter).reduced_isRealizedFace_iff hp _ _).mpr
  exact Rechart.decomposition_isRealizedFace
    (decomposition Φ anchor (Φ.faceSelector anchor Γ) hp) C hp hmod hcenter _ _
    (face_isRealized Φ anchor hp Γ)

theorem normalized_isMinimal : (normalized Φ anchor Γ hp C hmod hcenter).IsMinimal :=
  (minimalized Φ anchor Γ hp C hmod hcenter).reduced_isMinimal hp
    (Rechart.decomposition_isMinimal _ _ _ _ _)

theorem normalized_isReduced : (normalized Φ anchor Γ hp C hmod hcenter).IsReduced :=
  (minimalized Φ anchor Γ hp C hmod hcenter).reduced_isReduced hp

theorem normalized_retainedMass :
    (normalized Φ anchor Γ hp C hmod hcenter).retainedMass = Φ.retainedMass := by
  rw [(minimalized Φ anchor Γ hp C hmod hcenter).reduced_retainedMass,
    Rechart.decomposition_retainedMass]
  exact retainedMass Φ anchor (Φ.faceSelector anchor Γ) hp

theorem normalized_card_le :
    @Fintype.card (normalized Φ anchor Γ hp C hmod hcenter).flag.Node
      (normalized Φ anchor Γ hp C hmod hcenter).flag.nodeFintype ≤
        2 * Fintype.card Φ.flag.Node :=
  ((minimalized Φ anchor Γ hp C hmod hcenter).card_reduced_le hp).trans
    (card_le Φ anchor (Φ.faceSelector anchor Γ) hp)

theorem normalized_isKBounded {K B : ℕ} (hK : Φ.IsKBounded (fun _ ↦ K))
    (hC : ∀ x (q : IntCoord (C x).rank),
      latticeSupNorm ((C x).map q) ≤ K → latticeSupNorm q ≤ B) :
    (normalized Φ anchor Γ hp C hmod hcenter).IsKBounded (fun _ ↦ B) :=
  (minimalized Φ anchor Γ hp C hmod hcenter).reduced_isKBounded hp
    (Rechart.decomposition_isKBounded _ _ _ _ _
      (isKBounded Φ anchor (Φ.faceSelector anchor Γ) hp hK) hC)

/-- The subdivision map from the original decomposition to the normalized face refinement. -/
noncomputable def normalizedSubdivisionMap :
    SubdivisionMap Φ (normalized Φ anchor Γ hp C hmod hcenter) :=
  (subdivisionMap Φ anchor (Φ.faceSelector anchor Γ) hp).comp
    ((Rechart.subdivisionMap (decomposition Φ anchor (Φ.faceSelector anchor Γ) hp)
      C hp hmod hcenter).comp
      ((minimalized Φ anchor Γ hp C hmod hcenter).reducedSubdivisionMap hp))

@[simp]
theorem normalizedTargetNode_projection (hΓ : Γ ≠ ⊤) (hred : Φ.IsReducedElement anchor) :
    (normalizedSubdivisionMap Φ anchor Γ hp C hmod hcenter).node
      (normalizedTargetNode Φ anchor Γ hp C hmod hcenter hΓ hred) = anchor := rfl

/-- The realized target face is exactly the pullback of the selected old
face through the normalized subdivision, including its polytope constraint. -/
theorem normalizedTargetFace_carrier (hΓ : Γ ≠ ⊤) (hred : Φ.IsReducedElement anchor) :
    (normalizedTargetFace Φ anchor Γ hp C hmod hcenter hΓ hred).carrier =
      ((normalized Φ anchor Γ hp C hmod hcenter).flag.polytope
        (normalizedTargetNode Φ anchor Γ hp C hmod hcenter hΓ hred)).carrier ∩
      (normalizedSubdivisionMap Φ anchor Γ hp C hmod hcenter).fibre
        (normalizedTargetNode Φ anchor Γ hp C hmod hcenter hΓ hred) ⁻¹' Γ.carrier := rfl

theorem normalized_isRealizedFace
    (x : (normalized Φ anchor Γ hp C hmod hcenter).flag.Node)
    (Δ : (Φ.flag.polytope ((normalizedSubdivisionMap Φ anchor Γ hp C hmod hcenter).node x)).Face)
    (hne : (((normalized Φ anchor Γ hp C hmod hcenter).flag.polytope x).carrier ∩
      (normalizedSubdivisionMap Φ anchor Γ hp C hmod hcenter).fibre x ⁻¹' Δ.carrier).Nonempty)
    (hΔ : Φ.IsRealizedFace ((normalizedSubdivisionMap Φ anchor Γ hp C hmod hcenter).node x) Δ) :
    (normalized Φ anchor Γ hp C hmod hcenter).IsRealizedFace x
      ((normalizedSubdivisionMap Φ anchor Γ hp C hmod hcenter).face x Δ hne) :=
  (normalizedSubdivisionMap Φ anchor Γ hp C hmod hcenter).isRealizedFace x Δ hne hΔ

end EGZ.FlagDecomposition.FaceRefinement

namespace EGZ

open FlagDecomposition

/-- Uniform normalization of a proper-face refinement at a reduced node.
The new radius depends only on the original radius and ambient dimension. -/
theorem normalized_face_refinement_lemma (d : ℕ) :
    ∃ A : ℕ → ℕ, Monotone A ∧ (∀ K, K ≤ A K) ∧
      ∀ K : ℕ, ∃ p₀ : ℕ, 2 ≤ p₀ ∧
        ∀ (p : ℕ) [NeZero p] [Fact p.Prime], p₀ < p →
          ∀ (f : FpCoord p d → ℕ) (Φ : FlagDecomposition p d f)
            (anchor : Φ.flag.Node) (Γ : (Φ.flag.polytope anchor).Face)
            (hΓ : Γ ≠ ⊤) (hred : Φ.IsReducedElement anchor),
            Φ.IsKBounded (fun _ ↦ K) →
            ∃ (hp : Odd p)
              (C : ∀ x, IntegerLatticeChart
                ((FaceRefinement.decomposition Φ anchor
                  (Φ.faceSelector anchor Γ) hp).liftedSupport x))
              (hmod : ∀ x, Function.Injective ((Rechart.chart
                (FaceRefinement.decomposition Φ anchor (Φ.faceSelector anchor Γ) hp) C x).modp p))
              (hcenter : ∀ x q, q ∈ (C x).coordinateSupport → IsCenteredLift p q),
              let Ψ := FaceRefinement.normalized Φ anchor Γ hp C hmod hcenter
              Ψ.IsMinimal ∧ Ψ.IsReduced ∧ Ψ.IsKBounded (fun _ ↦ A K) ∧
              Ψ.retainedMass = Φ.retainedMass ∧
              @Fintype.card Ψ.flag.Node Ψ.flag.nodeFintype ≤ 2 * Fintype.card Φ.flag.Node ∧
              Ψ.IsRealizedFace
                (FaceRefinement.normalizedTargetNode Φ anchor Γ hp C hmod hcenter hΓ hred)
                (FaceRefinement.normalizedTargetFace Φ anchor Γ hp C hmod hcenter hΓ hred) := by
  obtain ⟨A, hAmono, hAge, hA⟩ := exists_uniform_rechart_parameters d
  refine ⟨A, hAmono, hAge, ?_⟩
  intro K
  obtain ⟨p₀, hp₀, hparams⟩ := hA K
  refine ⟨p₀, hp₀, ?_⟩
  intro p _ _ hpp f Φ anchor Γ hΓ hred hΦ
  have hp : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  let Θ := FaceRefinement.decomposition Φ anchor (Φ.faceSelector anchor Γ) hp
  have hΘ : Θ.IsKBounded (fun _ ↦ K) :=
    FaceRefinement.isKBounded Φ anchor (Φ.faceSelector anchor Γ) hp hΦ
  obtain ⟨C, hmod, hcenter, hbox, _hpoly⟩ :=
    hparams p hpp f Θ (fun _ ↦ K) hΘ (fun _ ↦ le_rfl)
  exact ⟨hp, C, hmod, hcenter,
    FaceRefinement.normalized_isMinimal Φ anchor Γ hp C hmod hcenter,
    FaceRefinement.normalized_isReduced Φ anchor Γ hp C hmod hcenter,
    FaceRefinement.normalized_isKBounded Φ anchor Γ hp C hmod hcenter hΦ hbox,
    FaceRefinement.normalized_retainedMass Φ anchor Γ hp C hmod hcenter,
    FaceRefinement.normalized_card_le Φ anchor Γ hp C hmod hcenter,
    FaceRefinement.normalizedTargetFace_isRealized Φ anchor Γ hp C hmod hcenter hΓ hred⟩

end EGZ
