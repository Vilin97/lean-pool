/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Levels
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.RealSupportRank
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.FaceRefinement

/-!
# Strict level increase after face refinement and minimalization

The face operation first splits atoms while retaining old coordinates.
Minimalizing the resulting lower anchor identifies its lattice rank with
the dimension of the selected proper face. Its represented space must then
shrink, giving the strict level increase used in termination.
-/

namespace EGZ.FlagDecomposition.FaceRefinement

variable {p d : ℕ} [Fact p.Prime] {f : FpCoord p d → ℕ}
    (Φ : FlagDecomposition p d f) (anchor : Φ.flag.Node) (hp : Odd p)
    (Γ : (Φ.flag.polytope anchor).Face)
variable (C : ∀ x : (decomposition Φ anchor (Φ.faceSelector anchor Γ) hp).flag.Node,
    IntegerLatticeChart ((decomposition Φ anchor (Φ.faceSelector anchor Γ) hp).liftedSupport x))

/-- A proper face gives a strictly smaller support-generated lattice at
the lower anchor, even if the input coordinates were not minimal. -/
theorem lowerAnchor_rechart_rank_lt (hΓ : Γ.carrier ⊂ (Φ.flag.polytope anchor).carrier) :
    (C (lowerAnchor Φ anchor hp Γ)).rank < Φ.flag.rank anchor := by
  have hdim : Γ.dimension < (RationalPolytope.Face.top (Φ.flag.polytope anchor)).dimension := by
    apply Γ.dimension_lt_of_subset_of_witness (RationalPolytope.Face.top _)
      Γ.subset_polytope
    obtain ⟨q, hqP, hqΓ⟩ := Set.not_subset.mp (not_le_of_gt hΓ)
    exact ⟨q, hqP, hqP, hqΓ⟩
  have hr := Rechart.rank_eq_polytope_dimension
    (decomposition Φ anchor (Φ.faceSelector anchor Γ) hp) C (lowerAnchor Φ anchor hp Γ)
  rw [lowerAnchor_polytope] at hr
  exact hr ▸ hdim.trans_le (RationalPolytope.Face.top _).dimension_le

variable (hinj : ∀ x, Function.Injective
    ((Rechart.chart (decomposition Φ anchor (Φ.faceSelector anchor Γ) hp) C x).modp p))
    (hcenter : ∀ x q, q ∈ (C x).coordinateSupport → IsCenteredLift p q)
/-- Strict increase at the lower anchor after changing to minimal
support-generated coordinates. -/
theorem lowerAnchor_rechart_level_lt (hΓ : Γ.carrier ⊂ (Φ.flag.polytope anchor).carrier) :
    Φ.level anchor <
      (Rechart.decomposition (decomposition Φ anchor (Φ.faceSelector anchor Γ) hp)
        C hp hinj hcenter).level (lowerAnchor Φ anchor hp Γ) := by
  let Ψ := decomposition Φ anchor (Φ.faceSelector anchor Γ) hp
  let Θ := Rechart.decomposition Ψ C hp hinj hcenter
  let a := lowerAnchor Φ anchor hp Γ
  apply Φ.representation.level_lt_of_rank_lt_of_factor Θ.representation anchor a
    ((Rechart.chart Ψ C a).modp p)
  · exact Rechart.space_le_original Ψ a
  · intro v hv
    exact (Rechart.chart_map Ψ C hp hinj a v hv).symm
  · exact lowerAnchor_rechart_rank_lt Φ anchor hp Γ C hΓ

/-- Every surviving lower-layer node has strictly larger level than the
old anchor. -/
theorem lower_rechart_level_lt (hΓ : Γ.carrier ⊂ (Φ.flag.polytope anchor).carrier)
    (x : (decomposition Φ anchor (Φ.faceSelector anchor Γ) hp).flag.Node)
    (hx : x.1.1.2 = 0) : Φ.level anchor <
      (Rechart.decomposition (decomposition Φ anchor (Φ.faceSelector anchor Γ) hp)
        C hp hinj hcenter).level x := by
  have hxa : x ≤ (lowerAnchor Φ anchor hp Γ) := by
    change x.1.1.1 ≤ anchor ∧ x.1.1.2 ≤ (0 : Fin 2)
    exact ⟨x.1.2 hx, by rw [hx]⟩
  exact (lowerAnchor_rechart_level_lt Φ anchor hp Γ C hinj hcenter hΓ).trans_le
    ((Rechart.decomposition (decomposition Φ anchor (Φ.faceSelector anchor Γ) hp)
      C hp hinj hcenter).level_antitone hxa)

/-- Upper levels are unchanged when the input was already minimal: both
their cumulative support and their lifted support remain the original ones. -/
theorem upper_rechart_level_eq (hΦ : Φ.IsMinimal) (x : Φ.flag.Node) :
    (Rechart.decomposition (decomposition Φ anchor (Φ.faceSelector anchor Γ) hp)
      C hp hinj hcenter).level (upper Φ anchor (Φ.faceSelector anchor Γ) hp x) = Φ.level x := by
  let Ψ := decomposition Φ anchor (Φ.faceSelector anchor Γ) hp
  let Θ := Rechart.decomposition Ψ C hp hinj hcenter
  let u := upper Φ anchor (Φ.faceSelector anchor Γ) hp x
  have hs : Θ.representation.space u = Φ.representation.space x := by
    change affineSpan (ZMod p) {v | Ψ.cumulativeWeight u v ≠ 0} = _
    rw [upper_cumulativeWeight]
    exact (hΦ x).1.symm
  have hr : (C u).rank = Φ.flag.rank x := by
    rw [Rechart.rank_eq_polytope_dimension, upper_polytope]
    change Module.finrank ℝ (affineSpan ℝ (Φ.flag.polytope x).carrier).direction = Φ.flag.rank x
    rw [Φ.polytope_affineSpan_eq_top hΦ x, AffineSubspace.direction_top]
    simp
  change (d + 1) * (d - Module.finrank (ZMod p) (Θ.representation.space u).direction) +
    (C u).rank = (d + 1) * (d - Module.finrank (ZMod p) (Φ.representation.space x).direction) +
      Φ.flag.rank x
  rw [hs, hr]

end EGZ.FlagDecomposition.FaceRefinement
