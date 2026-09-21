/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.FaceLevels
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.CompleteLevels
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.LevelInjectivity
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.NormalizedFace
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.NormalizedComplete

/-!
# Levels and coordinate injectivity of normalized operations

Reduced restriction leaves the level calculations intact. These wrappers
state the comparisons using the actual normalized subdivision maps, ready
for tracking persistent nodes through an iteration.
-/

namespace EGZ.FlagDecomposition

namespace FaceRefinement

variable {p d : ℕ} [Fact p.Prime] {f : FpCoord p d → ℕ}
    (Φ : FlagDecomposition p d f) (anchor : Φ.flag.Node)
    (Γ : (Φ.flag.polytope anchor).Face) (hp : Odd p)
    (C : ∀ x, IntegerLatticeChart
      ((decomposition Φ anchor (Φ.faceSelector anchor Γ) hp).liftedSupport x))
    (hmod : ∀ x, Function.Injective
      ((Rechart.chart (decomposition Φ anchor (Φ.faceSelector anchor Γ) hp) C x).modp p))
    (hcenter : ∀ x q, q ∈ (C x).coordinateSupport → IsCenteredLift p q)

theorem normalized_level_le (x : (normalized Φ anchor Γ hp C hmod hcenter).flag.Node) :
    Φ.level ((normalizedSubdivisionMap Φ anchor Γ hp C hmod hcenter).node x) ≤
      (normalized Φ anchor Γ hp C hmod hcenter).level x :=
  Rechart.decomposition_level_le (decomposition Φ anchor (Φ.faceSelector anchor Γ) hp)
    C hp hmod hcenter x.1

theorem normalized_lower_level_lt
    (hΓ : Γ.carrier ⊂ (Φ.flag.polytope anchor).carrier)
    (x : (normalized Φ anchor Γ hp C hmod hcenter).flag.Node) (hx : x.1.1.1.2 = 0) :
    Φ.level anchor < (normalized Φ anchor Γ hp C hmod hcenter).level x :=
  lower_rechart_level_lt Φ anchor hp Γ C hmod hcenter hΓ x.1 hx

theorem normalizedTargetNode_level_eq (hΦ : Φ.IsMinimal)
    (hΓ : Γ ≠ ⊤) (hred : Φ.IsReducedElement anchor) :
    (normalized Φ anchor Γ hp C hmod hcenter).level
      (normalizedTargetNode Φ anchor Γ hp C hmod hcenter hΓ hred) = Φ.level anchor :=
  upper_rechart_level_eq Φ anchor hp Γ C hmod hcenter hΦ anchor

/-- Face refinement uses injective charts at every surviving node. -/
theorem normalizedSubdivisionMap_fibre_injective
    (x : (normalized Φ anchor Γ hp C hmod hcenter).flag.Node) :
    Function.Injective ((normalizedSubdivisionMap Φ anchor Γ hp C hmod hcenter).fibre x) :=
  Rechart.chart_real_injective (decomposition Φ anchor (Φ.faceSelector anchor Γ) hp) C x.1

end FaceRefinement

namespace CompletePreparation

variable {p d : ℕ} [Fact p.Prime] {f : FpCoord p d → ℕ}
    {Φ : FlagDecomposition p d f} {anchor : Φ.flag.Node} {t : ℕ → ℕ} {δ : ℝ}
    (D : CompletePreparation Φ anchor t δ)
    (hp : Odd p) (hδ : 0 ≤ δ) (hsmall : (3 : ℝ) ^ (d + 1) * δ < 1)
    (C : ∀ x, IntegerLatticeChart ((D.diagram hp hδ hsmall).support x))
    (hmod : ∀ x, Function.Injective ((IntegralAffineMap.ofIntAffineMap (C x).map).modp p))
    (hcenter : ∀ x q, q ∈ (C x).coordinateSupport → IsCenteredLift p q)

theorem normalized_level_le (x : (D.normalized hp hδ hsmall C hmod hcenter).flag.Node) :
    Φ.level ((D.normalizedSubdivisionMap hp hδ hsmall C hmod hcenter).node x) ≤
      (D.normalized hp hδ hsmall C hmod hcenter).level x :=
  D.refined_level_le hp hδ hsmall C hmod hcenter x.1

theorem normalized_lower_level_lt (hcount : 0 < D.count)
    (x : (D.normalized hp hδ hsmall C hmod hcenter).flag.Node) (hx : x.1.1.1.2 = 0) :
    Φ.level anchor < (D.normalized hp hδ hsmall C hmod hcenter).level x :=
  D.lower_refined_level_lt hp hδ hsmall C hmod hcenter hcount x.1 hx

theorem normalizedCompleteNode_level_lt_of_not_complete
    (T : ℕ) (hwidth : T ≤ t 1) (hnot : ¬ Φ.IsCompleteElement anchor T δ) :
    Φ.level anchor < (D.normalized hp hδ hsmall C hmod hcenter).level
      (D.normalizedCompleteNode hp hδ hsmall C hmod hcenter) :=
  D.completeNode_level_lt_of_not_complete hp hδ hsmall C hmod hcenter T hwidth hnot

/-- At a persistent level, forgetting added coordinates is injective on
the whole real coordinate space of the surviving normalized node. -/
theorem normalizedSubdivisionMap_fibre_injective_of_level_eq
    (x : (D.normalized hp hδ hsmall C hmod hcenter).flag.Node)
    (hlevel : Φ.level ((D.normalizedSubdivisionMap hp hδ hsmall C hmod hcenter).node x) =
      (D.normalized hp hδ hsmall C hmod hcenter).level x) :
    Function.Injective ((D.normalizedSubdivisionMap hp hδ hsmall C hmod hcenter).fibre x) := by
  exact Φ.representation.factor_real_injective_of_level_eq
    (D.normalized hp hδ hsmall C hmod hcenter).representation
    ((D.normalizedSubdivisionMap hp hδ hsmall C hmod hcenter).node x) x
    (Augmented.forget (D.split hp hδ hsmall) (D.extra hp hδ hsmall) D.chain.direction hp
      (D.extra_antitone hp hδ hsmall) C x.1)
    (D.refined_space_le_original hp hδ hsmall C hmod hcenter x.1)
    (fun v hv ↦ (D.refined_forget_map hp hδ hsmall C hmod hcenter x.1 v hv).symm) hlevel

end CompletePreparation
end EGZ.FlagDecomposition
