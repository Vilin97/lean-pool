/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.GapCleanup
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Minimalization

/-!
# Gap cleanup followed by minimalization

Recharting the reduced gap-cleanup output produces a minimal and reduced
decomposition. Its weights, mass, gaps, and node count are unchanged by
the coordinate change. Increasing the coordinate bounds only weakens the
required inverse-power gap threshold.
-/

namespace EGZ

/-- Increasing the box radius decreases the gap threshold. -/
theorem gapThreshold_antitone_radius {a : ℝ} (ha : 0 ≤ a)
    {n K B : ℕ} (hn : 0 < n) (hKB : K ≤ B) (d : ℕ) :
    a / ((n : ℝ) * (2 * (B : ℝ) + 1) ^ d) ≤
      a / ((n : ℝ) * (2 * (K : ℝ) + 1) ^ d) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hKBR : (K : ℝ) ≤ B := by exact_mod_cast hKB
  apply div_le_div_of_nonneg_left ha (by positivity)
  gcongr

namespace FlagDecomposition.PrunedWeights

variable {p d : ℕ} [NeZero p] [Fact p.Prime] {f : FpCoord p d → ℕ}
    {Φ : FlagDecomposition p d f} (D : PrunedWeights Φ) (hp : Odd p)
    (C : ∀ x, IntegerLatticeChart ((D.cleaned hp).liftedSupport x))
    (hmod : ∀ x, Function.Injective ((Rechart.chart (D.cleaned hp) C x).modp p))
    (hcenter : ∀ x q, q ∈ (C x).coordinateSupport → IsCenteredLift p q)

/-- Minimalize the reduced output of gap cleanup. -/
noncomputable abbrev normalized : FlagDecomposition p d f :=
  Rechart.decomposition (D.cleaned hp) C hp hmod hcenter

/-- Embed surviving nodes of the normalized pruning into the original node set. -/
noncomputable def normalizedNodeEmbedding :
    (D.normalized hp C hmod hcenter).flag.Node ↪ Φ.flag.Node where
  toFun x := x.val.val
  inj' _ _ h := Subtype.ext (Subtype.ext h)

@[simp]
theorem normalized_localWeight (x : (D.cleaned hp).flag.Node) :
    (D.normalized hp C hmod hcenter).localWeight x = D.weight x.val.val := rfl

theorem normalized_cumulativeWeight (x : (D.cleaned hp).flag.Node) :
    (D.normalized hp C hmod hcenter).cumulativeWeight x = D.cumulative x.val.val :=
  D.cleaned_cumulativeWeight hp x

theorem normalized_localWeight_le (x : (D.cleaned hp).flag.Node) (v : FpCoord p d) :
    (D.normalized hp C hmod hcenter).localWeight x v ≤ Φ.localWeight x.val.val v :=
  D.weight_le x.val.val v

theorem normalized_cumulativeWeight_le (x : (D.cleaned hp).flag.Node) (v : FpCoord p d) :
    (D.normalized hp C hmod hcenter).cumulativeWeight x v ≤
      Φ.cumulativeWeight x.val.val v := by
  rw [D.normalized_cumulativeWeight]
  exact FlagDecompositionRaw.cumulativeWeight_mono D.weight_le x.val.val v

theorem normalized_retainedWeight : (D.normalized hp C hmod hcenter).retainedWeight =
    FlagDecompositionRaw.retainedWeight D.weight := by
  change (D.cleaned hp).retainedWeight = _
  rw [reduced_retainedWeight, (D.rebuildData hp).decomposition_retainedWeight]

theorem normalized_retainedWeight_le (v : FpCoord p d) :
    (D.normalized hp C hmod hcenter).retainedWeight v ≤ Φ.retainedWeight v := by
  rw [D.normalized_retainedWeight]
  exact Finset.sum_le_sum (fun x _ ↦ D.weight_le x v)

@[simp]
theorem normalized_retainedMass : (D.normalized hp C hmod hcenter).retainedMass =
    (D.cleaned hp).retainedMass := rfl

@[simp]
theorem normalized_gap (x : (D.cleaned hp).flag.Node) :
    (D.normalized hp C hmod hcenter).gap x = (D.cleaned hp).gap x :=
  Rechart.decomposition_gap (D.cleaned hp) C hp hmod hcenter x

theorem normalized_hat (x : (D.cleaned hp).flag.Node) (q : IntCoord (C x).rank) :
    (D.normalized hp C hmod hcenter).hat x q = D.hat x.val.val ((C x).map q) := by
  rw [Rechart.decomposition_hat, D.cleaned_hat]

theorem normalized_localLift (x : (D.cleaned hp).flag.Node) (q : IntCoord (C x).rank) :
    (D.normalized hp C hmod hcenter).localLift x q = D.localLift x.val.val ((C x).map q) := by
  rw [Rechart.decomposition_localLift]
  rfl

theorem normalized_isMinimal : (D.normalized hp C hmod hcenter).IsMinimal :=
  Rechart.decomposition_isMinimal (D.cleaned hp) C hp hmod hcenter

theorem normalized_isReduced : (D.normalized hp C hmod hcenter).IsReduced :=
  Rechart.decomposition_isReduced (D.cleaned hp) C hp hmod hcenter (D.cleaned_isReduced hp)

theorem normalized_card_eq :
    @Fintype.card (D.normalized hp C hmod hcenter).flag.Node
      (D.normalized hp C hmod hcenter).flag.nodeFintype =
        @Fintype.card (D.cleaned hp).flag.Node (D.cleaned hp).flag.nodeFintype := rfl

theorem normalized_card_le :
    @Fintype.card (D.normalized hp C hmod hcenter).flag.Node
      (D.normalized hp C hmod hcenter).flag.nodeFintype ≤ Fintype.card Φ.flag.Node :=
  D.cleaned_card_le hp

theorem normalized_isKBounded {K : Φ.flag.Node → ℕ}
    {B : (D.cleaned hp).flag.Node → ℕ} (hK : Φ.IsKBounded K)
    (hC : ∀ x (q : IntCoord (C x).rank),
      latticeSupNorm ((C x).map q) ≤ K x.val.val → latticeSupNorm q ≤ B x) :
    (D.normalized hp C hmod hcenter).IsKBounded B :=
  Rechart.decomposition_isKBounded (D.cleaned hp) C hp hmod hcenter
    (D.cleaned_isKBounded hp hK) hC

/-- The coordinate change preserves the already established mass-loss bound. -/
theorem normalized_retainedMass_loss_le {α : ℝ}
    (hmass : (1 - α) * (Φ.retainedMass : ℝ) ≤ (D.cleaned hp).retainedMass) :
    (Φ.retainedMass : ℝ) - (D.normalized hp C hmod hcenter).retainedMass ≤
      α * Φ.retainedMass := by
  rw [D.normalized_retainedMass]
  linarith

/-- A gap bound in the old coordinates remains valid at larger coordinate
bounds after recharting. The denominator uses the old node count. -/
theorem normalized_gap_bound {K : Φ.flag.Node → ℕ}
    {B : (D.cleaned hp).flag.Node → ℕ} {α : ℝ} (hα : 0 ≤ α)
    (hKB : ∀ x, K x.val.val ≤ B x)
    (hgap : ∀ x : (D.cleaned hp).flag.Node,
      α * (Φ.retainedMass : ℝ) /
        ((Fintype.card Φ.flag.Node : ℝ) * (2 * (K x.val.val : ℝ) + 1) ^ d) ≤
          ((D.cleaned hp).gap x : ℝ)) (x : (D.cleaned hp).flag.Node) :
    α * (Φ.retainedMass : ℝ) /
      ((Fintype.card Φ.flag.Node : ℝ) * (2 * (B x : ℝ) + 1) ^ d) ≤
        ((D.normalized hp C hmod hcenter).gap x : ℝ) := by
  rw [D.normalized_gap]
  exact (gapThreshold_antitone_radius (mul_nonneg hα (Nat.cast_nonneg _))
    Fintype.card_pos (hKB x) d).trans (hgap x)

/-- The subdivision map obtained by cleaning and normalizing the pruned weights. -/
noncomputable def normalizedSubdivisionMap :
    SubdivisionMap Φ (D.normalized hp C hmod hcenter) :=
  (D.cleanedSubdivisionMap hp).comp (Rechart.subdivisionMap (D.cleaned hp) C hp hmod hcenter)

@[simp]
theorem normalizedSubdivisionMap_node (x : (D.cleaned hp).flag.Node) :
    (D.normalizedSubdivisionMap hp C hmod hcenter).node x = x.val.val := rfl

theorem normalized_isRealizedFace (x : (D.cleaned hp).flag.Node)
    (Γ : (Φ.flag.polytope x.val.val).Face)
    (hne : (((D.normalized hp C hmod hcenter).flag.polytope x).carrier ∩
      (D.normalizedSubdivisionMap hp C hmod hcenter).fibre x ⁻¹' Γ.carrier).Nonempty)
    (hΓ : Φ.IsRealizedFace x.val.val Γ) :
    (D.normalized hp C hmod hcenter).IsRealizedFace x
      ((D.normalizedSubdivisionMap hp C hmod hcenter).face x Γ hne) :=
  (D.normalizedSubdivisionMap hp C hmod hcenter).isRealizedFace x Γ hne hΓ

theorem normalized_isCompleteElement {x : (D.cleaned hp).flag.Node} {t : ℕ}
    {ε δ α : ℝ} (hε : 0 < ε) (hα : 0 ≤ α)
    (hlarge : Φ.IsLargeElement ε x.val.val) (hcomplete : Φ.IsCompleteElement x.val.val t δ)
    (hloss : (Φ.retainedMass : ℝ) - (D.normalized hp C hmod hcenter).retainedMass ≤
      α * Φ.retainedMass) :
    (D.normalized hp C hmod hcenter).IsCompleteElement x t (δ - α / ε) :=
  Rechart.decomposition_isCompleteElement (D.cleaned hp) C hp hmod hcenter x t _
    (D.cleaned_isCompleteElement hp hε hα hlarge hcomplete hloss)

end FlagDecomposition.PrunedWeights

open FlagDecomposition

/-- Uniform normalized gap cleanup. The coordinate growth function depends
only on dimension, and the prime threshold only on the old uniform bound.
The resulting operation is both minimal and reduced. -/
theorem normalized_gap_cleanup_lemma (d : ℕ) :
    ∃ A : ℕ → ℕ, Monotone A ∧ (∀ K, K ≤ A K) ∧
      ∀ BK : ℕ, ∃ p₀ : ℕ, 2 ≤ p₀ ∧
        ∀ (p : ℕ) [NeZero p] [Fact p.Prime], p₀ < p →
          ∀ (f : FpCoord p d → ℕ) (Φ : FlagDecomposition p d f)
            (K : Φ.flag.Node → ℕ), Φ.IsKBounded K → (∀ x, K x ≤ BK) →
            ∀ α : ℝ, 0 ≤ α → α < 1 →
              ∃ (D : PrunedWeights Φ) (hp : Odd p)
                (C : ∀ x, IntegerLatticeChart ((D.cleaned hp).liftedSupport x))
                (hmod : ∀ x, Function.Injective ((Rechart.chart (D.cleaned hp) C x).modp p))
                (hcenter : ∀ x q, q ∈ (C x).coordinateSupport → IsCenteredLift p q),
                let Ψ := D.normalized hp C hmod hcenter
                (∀ x v, D.weight x v = 0 ∨ D.weight x v = Φ.localWeight x v) ∧
                Ψ.IsMinimal ∧ Ψ.IsReduced ∧
                Ψ.IsKBounded (fun x ↦ A (K x.val.val)) ∧
                @Fintype.card Ψ.flag.Node Ψ.flag.nodeFintype ≤ Fintype.card Φ.flag.Node ∧
                (Φ.retainedMass : ℝ) - Ψ.retainedMass ≤ α * Φ.retainedMass ∧
                (∀ x, α * (Φ.retainedMass : ℝ) /
                  ((Fintype.card Φ.flag.Node : ℝ) * (2 * (A (K x.val.val) : ℝ) + 1) ^ d) ≤
                    (Ψ.gap x : ℝ)) := by
  obtain ⟨A, hAmono, hAge, hA⟩ := exists_uniform_rechart_parameters d
  refine ⟨A, hAmono, hAge, ?_⟩
  intro BK
  obtain ⟨p₀, hp₀, hparams⟩ := hA BK
  refine ⟨p₀, hp₀, ?_⟩
  intro p _ _ hpp f Φ K hK hBK α hα hαone
  have hp : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  obtain ⟨D, hatoms, _, hcleanK, hgap, hmass⟩ := Φ.gap_cleanup_lemma hp hK hα hαone
  obtain ⟨C, hmod, hcenter, hbox, _⟩ := hparams p hpp f (D.cleaned hp)
    (fun x ↦ K x.val.val) hcleanK (fun x ↦ hBK x.val.val)
  exact ⟨D, hp, C, hmod, hcenter, hatoms,
    D.normalized_isMinimal hp C hmod hcenter,
    D.normalized_isReduced hp C hmod hcenter,
    D.normalized_isKBounded hp C hmod hcenter hK hbox,
    D.normalized_card_le hp C hmod hcenter,
    D.normalized_retainedMass_loss_le hp C hmod hcenter hmass,
    D.normalized_gap_bound hp C hmod hcenter hα (fun x ↦ hAge (K x.val.val)) hgap⟩

end EGZ
