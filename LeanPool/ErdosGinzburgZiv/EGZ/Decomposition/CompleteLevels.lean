/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/
module


public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Levels
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.CompleteRefinement

/-!
# Levels after complete-element refinement

Forgetting augmented coordinates factors the old represented map, so levels
never decrease. If at least one direction was added, its independence from
the old fibre-constant functionals forces every lower level above the old
anchor. In particular this applies to the reduced complete representative.
-/

@[expose] public section

namespace EGZ.FlagDecomposition.CompletePreparation

variable {p d : ℕ} [Fact p.Prime] {f : FpCoord p d → ℕ}
    {Φ : FlagDecomposition p d f} {anchor : Φ.flag.Node} {t : ℕ → ℕ} {δ : ℝ}
    (D : CompletePreparation Φ anchor t δ)
    (hp : Odd p) (hδ : 0 ≤ δ) (hsmall : (3 : ℝ) ^ (d + 1) * δ < 1)
    (C : ∀ x, IntegerLatticeChart ((D.diagram hp hδ hsmall).support x))
    (hmod : ∀ x, Function.Injective ((IntegralAffineMap.ofIntAffineMap (C x).map).modp p))
    (hcenter : ∀ x q, q ∈ (C x).coordinateSupport → IsCenteredLift p q)

theorem refined_space_le_original (x : (D.split hp hδ hsmall).flag.Node) :
    (D.refined hp hδ hsmall C hmod hcenter).representation.space x ≤
      Φ.representation.space x.1.1.1.1 :=
  Augmented.representation_space_le_original (D.split hp hδ hsmall)
    (D.extra hp hδ hsmall) D.chain.direction hp (D.extra_antitone hp hδ hsmall) C hmod x

theorem refined_forget_map (x : (D.split hp hδ hsmall).flag.Node) (v : FpCoord p d)
    (hv : v ∈ (D.refined hp hδ hsmall C hmod hcenter).representation.space x) :
    (Augmented.forget (D.split hp hδ hsmall) (D.extra hp hδ hsmall) D.chain.direction hp
      (D.extra_antitone hp hδ hsmall) C x).modp p
        ((D.refined hp hδ hsmall C hmod hcenter).representation.map x v) =
      Φ.representation.map x.1.1.1.1 v :=
  Augmented.forget_representation_map (D.split hp hδ hsmall)
    (D.extra hp hδ hsmall) D.chain.direction hp (D.extra_antitone hp hδ hsmall) C hmod x v hv

/-- Every output node has level at least that of its original base. -/
theorem refined_level_le (x : (D.split hp hδ hsmall).flag.Node) :
    Φ.level x.1.1.1.1 ≤ (D.refined hp hδ hsmall C hmod hcenter).level x := by
  apply Φ.representation.level_le_of_space_le_of_factor
    (D.refined hp hδ hsmall C hmod hcenter).representation x.1.1.1.1 x
    ((Augmented.forget (D.split hp hδ hsmall) (D.extra hp hδ hsmall) D.chain.direction hp
      (D.extra_antitone hp hδ hsmall) C x).modp p)
    (D.refined_space_le_original hp hδ hsmall C hmod hcenter x)
  intro v hv
  exact (D.refined_forget_map hp hδ hsmall C hmod hcenter x v hv).symm

omit hmod hcenter in
/-- Read one added functional from the new chart coordinates. -/
noncomputable def addedCoordinate (x : (D.split hp hδ hsmall).flag.Node)
    (i : Fin (D.extra hp hδ hsmall x)) : FpCoord p (C x).rank →ᵃ[ZMod p] ZMod p :=
  (AffineMap.proj i : FpCoord p (D.extra hp hδ hsmall x) →ᵃ[ZMod p] ZMod p).comp
    ((Coord.last ((D.split hp hδ hsmall).flag.rank x) (D.extra hp hδ hsmall x)).toAffineMap.comp
      (((D.diagram hp hδ hsmall).chart C x).modp p))

theorem addedCoordinate_map (x : (D.split hp hδ hsmall).flag.Node)
    (i : Fin (D.extra hp hδ hsmall x)) (v : FpCoord p d)
    (hv : v ∈ (D.refined hp hδ hsmall C hmod hcenter).representation.space x) :
    D.addedCoordinate hp hδ hsmall C x i
        ((D.refined hp hδ hsmall C hmod hcenter).representation.map x v) =
      D.chain.direction i v := by
  have h := congrArg
    (fun q ↦ Coord.last ((D.split hp hδ hsmall).flag.rank x) (D.extra hp hδ hsmall x) q i)
    (Augmented.chart_representation_map (D.split hp hδ hsmall) (D.extra hp hδ hsmall)
      D.chain.direction hp (D.extra_antitone hp hδ hsmall) C hmod x v hv)
  simpa only [addedCoordinate, AffineMap.comp_apply, AffineMap.proj_apply,
    LinearMap.coe_toAffineMap, Augmented.map, Coord.last_append, AffineMap.pi_apply] using h

omit hp hδ hsmall C hmod hcenter in
theorem first_direction_nonconstant (hcount : 0 < D.count) :
    Φ.representation.NonconstantOnFibers anchor (D.chain.direction 0) := by
  have hi := D.chain.independent 0 hcount
  rw [D.chain.initial] at hi
  by_contra hn
  exact hi ((Φ.representation.mem_fiberConstantSubmodule_iff anchor _).mpr hn)

/-- Each surviving lower node has strictly greater level than the old
anchor as soon as at least one thin direction was selected. -/
theorem lower_refined_level_lt (hcount : 0 < D.count)
    (x : (D.split hp hδ hsmall).flag.Node) (hx : x.1.1.2 = 0) :
    Φ.level anchor < (D.refined hp hδ hsmall C hmod hcenter).level x := by
  have hbase : x.1.1.1.1 ≤ anchor := x.1.2 hx
  have hextra : 0 < D.extra hp hδ hsmall x := by
    change 0 < (if x.1.1.2 = 0 then D.count else 0)
    rwa [ite_eq_left hx]
  apply Φ.representation.level_lt_of_nonconstant_factor_at_upper
    (D.refined hp hδ hsmall C hmod hcenter).representation hbase x
    ((Augmented.forget (D.split hp hδ hsmall) (D.extra hp hδ hsmall) D.chain.direction hp
      (D.extra_antitone hp hδ hsmall) C x).modp p)
    (D.refined_space_le_original hp hδ hsmall C hmod hcenter x)
    (fun v hv ↦ (D.refined_forget_map hp hδ hsmall C hmod hcenter x v hv).symm)
    (D.chain.direction 0) (D.first_direction_nonconstant hcount)
    (D.addedCoordinate hp hδ hsmall C x ⟨0, hextra⟩)
  intro v hv
  exact (D.addedCoordinate_map hp hδ hsmall C hmod hcenter x ⟨0, hextra⟩ v hv).symm

theorem completeNode_level_lt (hcount : 0 < D.count) :
    Φ.level anchor < (D.refined hp hδ hsmall C hmod hcenter).level
      (D.completeNode hp hδ hsmall C hmod hcenter) :=
  (D.lower_refined_level_lt hp hδ hsmall C hmod hcenter hcount
    (D.lowerAnchor hp hδ hsmall) rfl).trans_le
      ((D.refined hp hδ hsmall C hmod hcenter).level_antitone
        (D.completeNode_le_lowerAnchor hp hδ hsmall C hmod hcenter))

/-- Failure of completeness at the trigger width yields the strict
level increase required by the iteration. -/
theorem completeNode_level_lt_of_not_complete (T : ℕ) (hwidth : T ≤ t 1)
    (hnot : ¬ Φ.IsCompleteElement anchor T δ) :
    Φ.level anchor < (D.refined hp hδ hsmall C hmod hcenter).level
      (D.completeNode hp hδ hsmall C hmod hcenter) :=
  D.completeNode_level_lt hp hδ hsmall C hmod hcenter
    (D.count_pos_of_not_complete hδ T hwidth hnot)

end EGZ.FlagDecomposition.CompletePreparation
