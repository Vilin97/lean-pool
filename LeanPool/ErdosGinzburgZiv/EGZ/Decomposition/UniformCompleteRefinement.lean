/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.CompleteBounds
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.CompleteRefinement
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.RefinementGrowth

/-!
# Uniform parameters for complete-element refinements

The coordinate growth function is selected using only the ambient dimension.
Iterating a growth step gives all slab widths and a prime threshold uniform
over the input decomposition, its local masses, and the selected anchor.
-/

namespace EGZ

open FlagDecomposition

/-- All possible maximal thin-direction preparations share one prime
threshold. The chart bound uses their actual number of selected directions. -/
theorem exists_uniform_completePreparation_charts (d : ℕ) (g : ℕ → ℕ) :
    ∃ A : ℕ → ℕ, Monotone A ∧ (∀ K, K ≤ A K) ∧
      ∀ K : ℕ, ∃ p₀ : ℕ, 2 ≤ p₀ ∧
        ∀ (p : ℕ) [NeZero p] [Fact p.Prime], p₀ < p →
          ∃ hp : Odd p,
            ∀ (f : FpCoord p d → ℕ) (Φ : FlagDecomposition p d f)
              (anchor : Φ.flag.Node) (δ : ℝ) (hδ : 0 ≤ δ)
              (hsmall : (3 : ℝ) ^ (d + 1) * δ < 1)
              (D : CompletePreparation Φ anchor (refinementWidth A g K) δ),
              Φ.IsKBounded (fun _ ↦ K) →
              (∀ i : Fin D.count, 2 * refinementWidth A g K (i + 1) < p) ∧
              ∃ C : ∀ x, IntegerLatticeChart ((D.diagram hp hδ hsmall).support x),
                (∀ x, Function.Injective (((D.diagram hp hδ hsmall).chart C x).modp p)) ∧
                (∀ x q, q ∈ (C x).coordinateSupport → IsCenteredLift p q) ∧
                (∀ x (q : IntCoord (C x).rank),
                  q.real ∈ (((D.diagram hp hδ hsmall).chartedFlag C).polytope x).carrier →
                    latticeSupNorm q ≤ A (refinementWidth A g K D.count)) := by
  obtain ⟨A, hAmono, hAge, hA⟩ := exists_uniform_supportChart_parameters (2 * d)
  refine ⟨A, hAmono, hAge, ?_⟩
  intro K
  obtain ⟨q₀, hq₀, hparams⟩ := hA (refinementWidth A g K d)
  refine ⟨max q₀ (2 * refinementWidth A g K d), hq₀.trans (le_max_left _ _), ?_⟩
  intro p _ _ hpp
  have hq : q₀ < p := (le_max_left _ _).trans_lt hpp
  have hwidth : 2 * refinementWidth A g K d < p := (le_max_right _ _).trans_lt hpp
  have hp : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  refine ⟨hp, ?_⟩
  intro f Φ anchor δ hδ hsmall D hΦ
  have htsmall : ∀ i : Fin D.count, 2 * refinementWidth A g K (i + 1) < p := by
    intro i
    have hi : (i : ℕ) + 1 ≤ d := by have := D.count_le; omega
    exact (Nat.mul_le_mul_left 2 (refinementWidth_mono A g K hi)).trans_lt hwidth
  refine ⟨htsmall, ?_⟩
  obtain ⟨C, hmod, hcenter, _hbox, hpoly⟩ :=
    hparams p hq (D.diagram hp hδ hsmall) (fun _ ↦ refinementWidth A g K D.count)
      (D.diagram_rank_le hp hδ hsmall)
      (D.diagram_support_bound hp hδ hsmall hΦ (refinementWidth_mono A g K)
        (le_refinementWidth A g K D.count) htsmall)
      (fun _ ↦ refinementWidth_mono A g K D.count_le)
  exact ⟨C, hmod, hcenter, hpoly⟩

/-- A uniform complete-element refinement, retaining its concrete direction
preparation and lattice charts. The output radius is bounded by one monotone
function of the original radius; its reduced complete node and non-reduced
upper anchor are explicit nodes of the constructed two-layer flag. -/
theorem complete_refinement_lemma (d : ℕ) (g : ℕ → ℕ) (hg : Monotone g) :
    ∃ B : ℕ → ℕ, Monotone B ∧ (∀ K, K ≤ B K) ∧
      ∀ K : ℕ, ∃ p₀ : ℕ, 2 ≤ p₀ ∧
        ∀ (p : ℕ) [NeZero p] [Fact p.Prime], p₀ < p →
          ∀ (f : FpCoord p d → ℕ) (Φ : FlagDecomposition p d f)
            (anchor : Φ.flag.Node) (δ : ℝ) (hδ : 0 ≤ δ)
            (hsmall : (3 : ℝ) ^ (d + 1) * δ < 1),
            Φ.IsKBounded (fun _ ↦ K) →
            ∃ (hp : Odd p) (t : ℕ → ℕ) (D : CompletePreparation Φ anchor t δ)
              (C : ∀ x, IntegerLatticeChart ((D.diagram hp hδ hsmall).support x))
              (hmod : ∀ x, Function.Injective
                ((IntegralAffineMap.ofIntAffineMap (C x).map).modp p))
              (hcenter : ∀ x q, q ∈ (C x).coordinateSupport → IsCenteredLift p q)
              (b : ℕ),
              let Ψ := D.refined hp hδ hsmall C hmod hcenter
              let S := D.refinedSubdivisionMap hp hδ hsmall C hmod hcenter
              K ≤ b ∧ b ≤ B K ∧ Monotone t ∧ t 0 = K ∧
              g b ≤ t (D.count + 1) ∧
              Ψ.IsMinimal ∧ Ψ.IsKBounded (fun _ ↦ b) ∧
              Antitone (fun _ : Ψ.flag.Node ↦ b) ∧
              (Φ.retainedMass : ℝ) - Ψ.retainedMass ≤
                (3 : ℝ) ^ (d + 1) * δ * natMass (Φ.cumulativeWeight anchor) ∧
              @Fintype.card Ψ.flag.Node Ψ.flag.nodeFintype ≤
                2 * Fintype.card Φ.flag.Node ∧
              Ψ.IsCompleteElement (D.lowerAnchor hp hδ hsmall) (g b) δ ∧
              D.completeNode hp hδ hsmall C hmod hcenter ≤ D.lowerAnchor hp hδ hsmall ∧
              Ψ.IsReducedElement (D.completeNode hp hδ hsmall C hmod hcenter) ∧
              Ψ.IsCompleteElement (D.completeNode hp hδ hsmall C hmod hcenter) (g b) δ ∧
              Ψ.cumulativeWeight (D.completeNode hp hδ hsmall C hmod hcenter) =
                Ψ.cumulativeWeight (D.lowerAnchor hp hδ hsmall) ∧
              ¬ Ψ.IsReducedElement (D.upperAnchor hp hδ hsmall) ∧
              S.node (D.lowerAnchor hp hδ hsmall) = anchor ∧
              S.node (D.upperAnchor hp hδ hsmall) = anchor ∧
              (∀ (x : Ψ.flag.Node) (Γ : (Φ.flag.polytope (S.node x)).Face)
                (hne : ((Ψ.flag.polytope x).carrier ∩ S.fibre x ⁻¹' Γ.carrier).Nonempty),
                Φ.IsRealizedFace (S.node x) Γ → Ψ.IsRealizedFace x (S.face x Γ hne)) := by
  obtain ⟨A, hAmono, hAge, hA⟩ := exists_uniform_completePreparation_charts d g
  let B : ℕ → ℕ := fun K ↦ A (refinementWidth A g K d)
  have hBmono : Monotone B := hAmono.comp (refinementWidth_mono_initial hAmono hg d)
  have hBge : ∀ K, K ≤ B K := fun K ↦
    (le_refinementWidth A g K d).trans (hAge _)
  refine ⟨B, hBmono, hBge, ?_⟩
  intro K
  obtain ⟨p₀, hp₀, hparams⟩ := hA K
  refine ⟨p₀, hp₀, ?_⟩
  intro p _ _ hpp f Φ anchor δ hδ hsmall hΦ
  obtain ⟨hp, hcharts⟩ := hparams p hpp
  let t := refinementWidth A g K
  let D : CompletePreparation Φ anchor t δ :=
    Classical.choice (nonempty_completePreparation Φ anchor t δ)
  obtain ⟨_htsmall, C, hmod, hcenter, hpoly⟩ := hcharts f Φ anchor δ hδ hsmall D hΦ
  let b := A (t D.count)
  have hgb : g b ≤ t (D.count + 1) := desired_width_le_refinementWidth_succ A g K D.count
  refine ⟨hp, t, D, C, hmod, hcenter, b,
    (le_refinementWidth A g K D.count).trans (hAge _),
    hAmono (refinementWidth_mono A g K D.count_le),
    refinementWidth_mono A g K, rfl, hgb,
    D.refined_isMinimal hp hδ hsmall C hmod hcenter,
    D.refined_isKBounded hp hδ hsmall C hmod hcenter hpoly,
    fun _ _ _ ↦ le_rfl,
    D.refined_retainedMass_loss_le hp hδ hsmall C hmod hcenter,
    D.refined_card_le hp hδ hsmall C hmod hcenter,
    (D.refined_lowerAnchor_isCompleteElement hp hδ hsmall C hmod hcenter).mono_width hgb,
    D.completeNode_le_lowerAnchor hp hδ hsmall C hmod hcenter,
    D.completeNode_isReduced hp hδ hsmall C hmod hcenter,
    (D.completeNode_isCompleteElement hp hδ hsmall C hmod hcenter).mono_width hgb,
    (D.completeNode_cumulativeWeight hp hδ hsmall C hmod hcenter).trans
      (D.lowerAnchor_cumulativeWeight hp hδ hsmall).symm,
    D.refined_upperAnchor_not_isReducedElement hp hδ hsmall C hmod hcenter,
    rfl, rfl, ?_⟩
  exact (D.refinedSubdivisionMap hp hδ hsmall C hmod hcenter).isRealizedFace

end EGZ
