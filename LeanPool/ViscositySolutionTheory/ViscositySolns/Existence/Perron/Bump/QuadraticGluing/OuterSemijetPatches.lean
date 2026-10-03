/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Existence.Perron.Bump.QuadraticGluing.BentStrictNegativity

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Quadratic gluing data for the Perron bump step (OuterSemijetPatches)

Part of the quadratic-gluing development connecting the lifted quadratic
supplied by operator continuity to the strict local max-patch formulation.
Split from `QuadraticGluing.lean`; see the umbrella module docstring.
-/

@[expose] public noncomputable section

open Filter
open scoped MatrixOrder

namespace ViscositySolns

variable {n : Nat}

namespace PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallGeometricSemijetPatchAt

/--
Open-domain geometry supplies the no-branch-LSC geometric package.
-/
theorem of_isOpen
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g} {x : Point n} {J : Jet n}
    (hx : x ∈ C) (hCopen : IsOpen C)
    (hboundaryOutside : ∀ z : Point n, z ∈ boundary -> z ∉ C) :
    PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallGeometricSemijetPatchAt
      C boundary F g B x J := by
  intro _γ _V _hγpos _hVopen _hV
  rcases Metric.mem_nhds_iff.1 (hCopen.mem_nhds hx) with
    ⟨ε, hεpos, hεC⟩
  refine ⟨ε / 2, half_pos hεpos, hboundaryOutside, ?_⟩
  intro r _hrpos hrle z hzClosed
  have hr_lt_ε : r < ε := by
    linarith
  exact hεC (Metric.closedBall_subset_ball hr_lt_ε hzClosed)

end PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallGeometricSemijetPatchAt

namespace PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallGeometricSemijetPatch

/--
Open-domain geometry supplies the global no-branch-LSC geometric semijet
package.
-/
theorem of_isOpen
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g}
    (hCopen : IsOpen C)
    (hboundaryOutside : ∀ z : Point n, z ∈ boundary -> z ∉ C) :
    PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallGeometricSemijetPatch
      C boundary F g B := by
  intro x hx J _hJ _hneg
  exact PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallGeometricSemijetPatchAt.of_isOpen
    hx hCopen hboundaryOutside

end PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallGeometricSemijetPatch

/--
Small-radius semijet-driven outer-annulus source data without branch
lower-semicontinuity.
-/
def PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallSmallRadiusSemijetPatchAt
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) (x : Point n) (J : Jet n) :
    Prop :=
  ∃ γ : Real, ∃ V : Set (Point n), ∃ ρ : Real,
    let Xb : Hessian n := J.hessian - γ • (1 : Hessian n)
    0 < γ ∧
      IsOpen V ∧
        V ∈ nhdsWithin x C ∧
          0 < ρ ∧
            (∀ z : Point n, z ∈ boundary -> z ∉ C) ∧
              ∀ r : Real, 0 < r -> r <= ρ ->
                let δ : Real := γ * r ^ 2 / 8
                let q : Point n -> Real := fun z =>
                  quadraticModel x
                    (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + δ)
                    J.gradient Xb z
                (∀ z : Point n, z ∈ Metric.closedBall x r -> z ∈ C) ∧
                  ∀ z : Point n, z ∈ V -> z ∈ C ->
                    F z (q z)
                        (quadraticModelJetAt x J.gradient Xb z).gradient
                        (quadraticModelJetAt x J.gradient Xb z).hessian < 0

/--
Small-radius semijet-driven outer-annulus source data without branch
lower-semicontinuity at every failed lower-envelope subjet inequality.
-/
def PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallSmallRadiusSemijetPatch
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallSmallRadiusSemijetPatchAt
          C boundary F g B x J

namespace PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallGeometricSemijetPatchAt

/--
Operator continuity supplies the strict-negativity part of the no-branch-LSC
small-radius semijet package; the geometric package supplies closed-ball
domain control.
-/
theorem smallRadiusSemijetPatchAt
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g} {x : Point n} {J : Jet n}
    (hgeom :
      PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallGeometricSemijetPatchAt
        C boundary F g B x J)
    (hF : OperatorContinuous F)
    (hneg :
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0) :
    PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallSmallRadiusSemijetPatchAt
      C boundary F g B x J := by
  rcases hF.exists_sourceOuterClosedBall_smallRadius_bentStrictNegativity
      (C := C) (boundary := boundary) (g := g) (B := B) (x := x) (J := J)
      hneg with
    ⟨γ, V, ρneg, hγpos, hVopen, hV, hρnegpos, hstrict⟩
  rcases hgeom γ V hγpos hVopen hV with
    ⟨ρgeom, hρgeompos, hboundaryOutside, hclosedBallSmall⟩
  let ρ : Real := min ρneg ρgeom
  have hρpos : 0 < ρ := lt_min hρnegpos hρgeompos
  refine ⟨γ, V, ρ, hγpos, hVopen, hV, hρpos, hboundaryOutside, ?_⟩
  intro r hrpos hrle
  have hr_le_neg : r <= ρneg := hrle.trans (min_le_left ρneg ρgeom)
  have hr_le_geom : r <= ρgeom := hrle.trans (min_le_right ρneg ρgeom)
  refine ⟨hclosedBallSmall r hrpos hr_le_geom, ?_⟩
  simpa using hstrict r hrpos hr_le_neg

end PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallGeometricSemijetPatchAt

namespace PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallGeometricSemijetPatch

/--
Global no-branch-LSC geometric semijet data supplies the no-branch-LSC
small-radius package once operator continuity provides the source
strict-negativity scale.
-/
theorem smallRadiusSemijetPatch
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g}
    (hgeom :
      PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallGeometricSemijetPatch
        C boundary F g B)
    (hF : OperatorContinuous F) :
    PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallSmallRadiusSemijetPatch
      C boundary F g B := by
  intro x hx J hJ hneg
  exact (hgeom x hx J hJ hneg).smallRadiusSemijetPatchAt hF hneg

end PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallGeometricSemijetPatch

/--
Semijet-driven outer-annulus source data without branch lower-semicontinuity.
-/
def PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallSemijetPatchAt
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) (x : Point n) (J : Jet n) :
    Prop :=
  ∃ γ : Real, ∃ V : Set (Point n),
    let Xb : Hessian n := J.hessian - γ • (1 : Hessian n)
    0 < γ ∧
      IsOpen V ∧
        V ∈ nhdsWithin x C ∧
          ∀ S : Set (Point n), S ∈ nhdsWithin x C ->
            ∃ r : Real,
              let δ : Real := γ * r ^ 2 / 8
              let q : Point n -> Real := fun z =>
                quadraticModel x
                  (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + δ)
                  J.gradient Xb z
              let K : Set (Point n) :=
                {z : Point n | 3 * r / 4 <= dist z x ∧ dist z x <= r}
              0 < r ∧
                (∀ z : Point n, z ∈ Metric.ball x r -> z ∈ V) ∧
                  (∀ z : Point n, z ∈ Metric.closedBall x r -> z ∈ C) ∧
                    (∀ z : Point n, z ∈ boundary -> z ∉ C) ∧
                      lowerEnvelope C
                          (perronEnvelope C boundary F g B.lower B.upper) x < q x ∧
                        ContinuousWithinAt q C x ∧
                          (∀ z : Point n, z ∈ V -> z ∈ C ->
                            F z (q z)
                                (quadraticModelJetAt x J.gradient Xb z).gradient
                                (quadraticModelJetAt x J.gradient Xb z).hessian < 0) ∧
                            ∀ z : Point n, z ∈ K -> z ∈ S

/--
Semijet-driven outer-annulus source data without branch lower-semicontinuity at
every failed lower-envelope subjet inequality.
-/
def PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallSemijetPatch
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallSemijetPatchAt
          C boundary F g B x J

namespace PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallSmallRadiusSemijetPatchAt

/--
Small-radius no-branch-LSC data supplies the relative-neighborhood semijet
package by shrinking the radius so the explicit outer annulus lies in the
prescribed relative neighborhood.
-/
theorem semijetPatchAt
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g} {x : Point n} {J : Jet n}
    (hx : x ∈ C)
    (hpatch :
      PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallSmallRadiusSemijetPatchAt
        C boundary F g B x J) :
    PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallSemijetPatchAt
      C boundary F g B x J := by
  let W : Point n -> Real :=
    lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)
  rcases hpatch with
    ⟨γ, V, ρ, hγpos, hVopen, hV, hρpos, hboundaryOutside, hsmall⟩
  let Xb : Hessian n := J.hessian - γ • (1 : Hessian n)
  have hxV : x ∈ V := mem_of_mem_nhdsWithin hx hV
  rcases Metric.mem_nhds_iff.1 (hVopen.mem_nhds hxV) with
    ⟨ρV, hρVpos, hρVsubset⟩
  refine ⟨γ, V, hγpos, hVopen, hV, ?_⟩
  intro S hS
  rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hS with
    ⟨U, hU, hUS⟩
  rcases Metric.mem_nhds_iff.1 hU with ⟨σ, hσpos, hσU⟩
  let r : Real := min (min ρ σ) ρV / 2
  have hminpos : 0 < min (min ρ σ) ρV := lt_min (lt_min hρpos hσpos) hρVpos
  have hrpos : 0 < r := by
    dsimp [r]
    linarith
  have hr_le_ρ : r <= ρ := by
    have hhalf_le_min : min (min ρ σ) ρV / 2 <= min (min ρ σ) ρV := by
      linarith
    exact hhalf_le_min.trans ((min_le_left (min ρ σ) ρV).trans (min_le_left ρ σ))
  have hr_lt_σ : r < σ := by
    have hmin_le_σ : min (min ρ σ) ρV <= σ :=
      (min_le_left (min ρ σ) ρV).trans (min_le_right ρ σ)
    dsimp [r]
    linarith
  have hr_le_ρV : r <= ρV := by
    have hhalf_le_min : min (min ρ σ) ρV / 2 <= min (min ρ σ) ρV := by
      linarith
    exact hhalf_le_min.trans (min_le_right (min ρ σ) ρV)
  rcases hsmall r hrpos hr_le_ρ with ⟨hclosedBallC, hneg⟩
  have hballV : ∀ z : Point n, z ∈ Metric.ball x r -> z ∈ V := by
    intro z hz
    exact hρVsubset (Metric.ball_subset_ball hr_le_ρV hz)
  let δ : Real := γ * r ^ 2 / 8
  let q : Point n -> Real := fun z => quadraticModel x (W x + δ) J.gradient Xb z
  let K : Set (Point n) := {z : Point n | 3 * r / 4 <= dist z x ∧ dist z x <= r}
  refine ⟨r, hrpos, hballV, hclosedBallC, hboundaryOutside, ?_, ?_, hneg, ?_⟩
  · have hδpos : 0 < δ := by
      dsimp [δ]
      positivity
    have hqx : q x = W x + δ := by
      simp [q, quadraticModel]
    change W x < q x
    rw [hqx]
    exact lt_add_of_pos_right (W x) hδpos
  · simpa [W, q, Xb] using
      (continuous_quadraticModel x (W x + δ) J.gradient Xb).continuousWithinAt
  · intro z hzK
    have hzClosed : z ∈ Metric.closedBall x r := by
      simpa [Metric.mem_closedBall] using hzK.2
    have hzC : z ∈ C := hclosedBallC z hzClosed
    have hzBallσ : z ∈ Metric.ball x σ := by
      have hdist_lt : dist z x < σ := lt_of_le_of_lt hzK.2 hr_lt_σ
      simpa [Metric.mem_ball] using hdist_lt
    exact hUS ⟨hσU hzBallσ, hzC⟩

end PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallSmallRadiusSemijetPatchAt

namespace PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallSmallRadiusSemijetPatch

/--
Global small-radius no-branch-LSC data supplies the semijet-driven
relative-neighborhood package.
-/
theorem semijetPatch
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g}
    (hpatch :
      PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallSmallRadiusSemijetPatch
        C boundary F g B) :
    PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallSemijetPatch
      C boundary F g B := by
  intro x hx J hJ hneg
  exact (hpatch x hx J hJ hneg).semijetPatchAt hx

end PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallSmallRadiusSemijetPatch

namespace PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallSemijetPatchAt

/--
The no-branch-LSC semijet support estimate supplies strict lower-envelope
domination on the outer annulus once the annulus is chosen inside its relative
neighborhood.
-/
theorem outerClosedBallLowerEnvelopePatchAt
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g} {x : Point n} {J : Jet n}
    (hpatch :
      PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallSemijetPatchAt
        C boundary F g B x J)
    (hJ : J ∈ Subjet C
      (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x) :
    PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallLowerEnvelopePatchAt
      C boundary F g B x J := by
  let W : Point n -> Real :=
    lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)
  rcases hpatch with ⟨γ, V, hγpos, hVopen, hV, hchoose⟩
  let Xb : Hessian n := J.hessian - γ • (1 : Hessian n)
  let S : Set (Point n) := {z : Point n |
    ∀ δ : Real, δ < ((1 / 4 : Real) * γ) * ‖z - x‖ ^ 2 ->
      quadraticModel x (W x + δ) J.gradient Xb z < W z}
  have hS : S ∈ nhdsWithin x C := by
    exact
      (eventually_forall_quadraticModel_lift_hessian_sub_identity_lt_of_subjet
        (C := C) (u := W) (x := x) (J := J) hγpos hJ)
  rcases hchoose S hS with
    ⟨r, hrpos, hballV, hclosedBallC, hboundaryOutside, hWltq,
      hqCont, hneg, hKS⟩
  let δ : Real := γ * r ^ 2 / 8
  let q : Point n -> Real := fun z =>
    quadraticModel x (W x + δ) J.gradient Xb z
  let K : Set (Point n) := {z : Point n | 3 * r / 4 <= dist z x ∧ dist z x <= r}
  refine ⟨γ, r, V, hγpos, hrpos, hVopen, hV, hballV,
    hclosedBallC, hboundaryOutside, ?_, ?_, ?_, ?_⟩
  · simpa [W, δ, q] using hWltq
  · simpa [W, δ, q, Xb] using hqCont
  · simpa [W, δ, q, Xb] using hneg
  · intro z hzK
    have hzS : z ∈ S := hKS z hzK
    have hmargin :
        δ < ((1 / 4 : Real) * γ) * ‖z - x‖ ^ 2 := by
      simpa [δ] using
        (sourceOuterAnnulus_lift_lt_bendMargin
          (x := x) (z := z) hγpos hrpos hzK)
    simpa [S, W, δ, q, Xb] using hzS δ hmargin

end PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallSemijetPatchAt

namespace PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallSemijetPatch

/--
Global no-branch-LSC semijet-driven outer-annulus source data supplies the
no-branch-LSC outer-annulus lower-envelope package.
-/
theorem outerClosedBallLowerEnvelopePatch
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g}
    (hpatch :
      PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallSemijetPatch
        C boundary F g B) :
    PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallLowerEnvelopePatch
      C boundary F g B := by
  intro x hx J hJ hneg
  exact (hpatch x hx J hJ hneg).outerClosedBallLowerEnvelopePatchAt hJ

end PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallSemijetPatch

namespace PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallGeometricSemijetPatch

/--
Global no-branch-LSC geometric semijet data supplies the no-branch-LSC
outer-annulus lower-envelope package once operator continuity provides the
source strict-negativity scale.
-/
theorem outerClosedBallLowerEnvelopePatch
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g}
    (hgeom :
      PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallGeometricSemijetPatch
        C boundary F g B)
    (hF : OperatorContinuous F) :
    PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallLowerEnvelopePatch
      C boundary F g B :=
  (hgeom.smallRadiusSemijetPatch hF).semijetPatch.outerClosedBallLowerEnvelopePatch

end PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallGeometricSemijetPatch

/--
Operator continuity and open-domain geometry supply the final no-branch-LSC
source outer-closed-ball lower-envelope patch package.
-/
theorem OperatorContinuous.perronLowerEnvelope_sourceOuterClosedBallLowerEnvelopePatch
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g}
    (hF : OperatorContinuous F)
    (hCopen : IsOpen C)
    (hboundaryOutside : ∀ z : Point n, z ∈ boundary -> z ∉ C) :
    PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallLowerEnvelopePatch
      C boundary F g B :=
  (PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallGeometricSemijetPatch.of_isOpen
    (B := B) hCopen hboundaryOutside).outerClosedBallLowerEnvelopePatch hF

/--
The explicit closed annulus supplies the abstract transition-annulus
selection interface.
-/
theorem PerronLowerEnvelopeBentQuadraticSourceClosedAnnulusSelectionPatchAt.annulusSelectionPatchAt
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g} {x : Point n} {J : Jet n}
    (hpatch :
      PerronLowerEnvelopeBentQuadraticSourceClosedAnnulusSelectionPatchAt
        C boundary F g B x J) :
    PerronLowerEnvelopeBentQuadraticSourceAnnulusSelectionPatchAt
      C boundary F g B x J := by
  rcases hpatch with
    ⟨γ, r, V, hγpos, hrpos, hVopen, hV, hballV, hWltq,
      hqCont, hneg, hlocalOld, hboundaryAway⟩
  let δ : Real := γ * r ^ 2 / 8
  let Xb : Hessian n := J.hessian - γ • (1 : Hessian n)
  let q : Point n -> Real := fun z =>
    quadraticModel x
      (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + δ)
      J.gradient Xb z
  let K : Set (Point n) := {z : Point n | r / 2 <= dist z x ∧ dist z x <= r}
  have hKcompact : IsCompact K := by
    have hClosedLower : IsClosed {z : Point n | r / 2 <= dist z x} := by
      exact isClosed_le continuous_const (continuous_id.dist continuous_const)
    have hCompactClosed : IsCompact (Metric.closedBall x r) :=
      isCompact_closedBall x r
    have hCompactInter : IsCompact (Metric.closedBall x r ∩
        {z : Point n | r / 2 <= dist z x}) :=
      hCompactClosed.inter_right hClosedLower
    simpa [K, Metric.mem_closedBall, Set.inter_def, and_comm, and_left_comm,
      and_assoc] using hCompactInter
  refine ⟨γ, r, V, K, hγpos, hrpos, hVopen, hV, hballV, hWltq,
    hqCont, hneg, hKcompact, ?_, hlocalOld, ?_, hboundaryAway⟩
  · intro z _hz
    exact self_mem_nhdsWithin
  · intro z _hzC hzNotBall
    by_cases hzClosed : z ∈ Metric.closedBall x r
    · have hzle : dist z x <= r := by
        simpa [Metric.mem_closedBall] using hzClosed
      have hrle : r <= dist z x := by
        simpa [Metric.mem_ball, not_lt] using hzNotBall
      have hdist_eq : dist z x = r := le_antisymm hzle hrle
      let ε : Real := r / 2
      have hεpos : 0 < ε := by
        dsimp [ε]
        linarith
      have hball : Metric.ball z ε ∈ nhdsWithin z C :=
        mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds z hεpos)
      filter_upwards [hball] with y hyz
      by_cases hyOutside : y ∉ Metric.ball x r
      · exact Or.inl hyOutside
      · have hyBall : y ∈ Metric.ball x r := not_not.mp hyOutside
        have hyUpperLt : dist y x < r := by
          simpa [Metric.mem_ball] using hyBall
        have hyUpper : dist y x <= r := le_of_lt hyUpperLt
        have hyz' : dist z y < ε := by
          simpa [Metric.mem_ball, dist_comm] using hyz
        have htri : dist z x <= dist z y + dist y x := dist_triangle z y x
        have hlt : r < ε + dist y x := by
          have hltAdd : dist z y + dist y x < ε + dist y x := by
            linarith
          have hlt' : dist z x < ε + dist y x :=
            lt_of_le_of_lt htri hltAdd
          simpa [hdist_eq] using hlt'
        have hyLower : r / 2 <= dist y x := by
          dsimp [ε] at hlt
          linarith
        exact Or.inr ⟨hyLower, hyUpper⟩
    · filter_upwards
        [eventually_not_mem_ball_of_not_mem_closedBall
          (C := C) (x := x) (z := z) (r := r) hzClosed] with y hy
      exact Or.inl hy

/--
Global closed-annulus source-radius transition data supplies the abstract
transition-annulus selection interface.
-/
theorem PerronLowerEnvelopeBentQuadraticSourceClosedAnnulusSelectionPatch.annulusSelectionPatch
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g}
    (hpatch :
      PerronLowerEnvelopeBentQuadraticSourceClosedAnnulusSelectionPatch
        C boundary F g B) :
    PerronLowerEnvelopeBentQuadraticSourceAnnulusSelectionPatch
      C boundary F g B := by
  intro x hx J hJ hneg
  exact (hpatch x hx J hJ hneg).annulusSelectionPatchAt

/--
A concrete piecewise-set constructor for the localized bent lower-barrier
patch interface.

The set `P` is the region where the patch uses `max(lower, q)`. It must be a
relative neighborhood of every active point, locally inactive off the active
neighborhood, and inactive or dominated on the Dirichlet boundary.
-/
theorem PerronLowerEnvelopeBentQuadraticLocalizedLowerPatchAt.of_piecewiseSet
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g} {x : Point n} {J : Jet n}
    (hsets :
      ∀ δ γ : Real, ∀ V : Set (Point n),
        ∀ Xb : Hessian n, ∀ q : Point n -> Real,
        Xb = J.hessian - γ • (1 : Hessian n) ->
        q = (fun z =>
          quadraticModel x
            (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + δ)
            J.gradient Xb z) ->
        0 < δ ->
          0 < γ ->
            IsOpen V ->
              V ∈ nhdsWithin x C ->
                lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x < q x ->
                  ContinuousWithinAt q C x ->
                    (∀ z : Point n, z ∈ V -> z ∈ C ->
                      F z (q z)
                          (quadraticModelJetAt x J.gradient Xb z).gradient
                          (quadraticModelJetAt x J.gradient Xb z).hessian < 0) ->
                      ∃ P : Set (Point n),
                        (∀ z : Point n, z ∈ C -> z ∈ V -> P ∈ nhdsWithin z C) ∧
                        (∀ z : Point n, z ∈ C -> z ∉ V ->
                            ∀ᶠ y in nhdsWithin z C, y ∉ P ∨ q y <= B.lower y) ∧
                            (∀ z : Point n, z ∈ boundary ->
                              z ∉ closure P ∨ q z <= B.lower z)) :
    PerronLowerEnvelopeBentQuadraticLocalizedLowerPatchAt C boundary F g B x J := by
  intro δ γ V Xb q hδpos hγpos hVopen hV hWltq hqCont hneg
  classical
  rcases hsets δ γ V Xb q rfl rfl hδpos hγpos hVopen hV hWltq hqCont hneg with
    ⟨P, hactive, hinactive, hboundary⟩
  let patched : Point n -> Real := fun y =>
    if y ∈ P then Max.max (B.lower y) (q y) else B.lower y
  refine ⟨patched, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz hzV
    filter_upwards [hactive z hz hzV] with y hyP
    simp [patched, hyP]
  · intro z hz hzV
    filter_upwards [hinactive z hz hzV] with y hy
    rcases hy with hyP | hyle
    · simp [patched, hyP]
    · by_cases hyP : y ∈ P
      · simp [patched, hyP, max_eq_left hyle]
      · simp [patched, hyP]
  · intro z hz
    rcases hboundary z hz with hzP | hzle
    · have hznotP : z ∉ P := fun hp => hzP (subset_closure hp)
      simp [patched, hznotP]
    · by_cases hzP : z ∈ P
      · simp [patched, hzP, max_eq_left hzle]
      · simp [patched, hzP]
  · intro z hz
    exact UpperSemicontinuousOn.piecewise_max_boundary
      B.lower_dirichlet.upperSemicontinuousOn
      (continuous_quadraticModel _ _ _ _)
      (Set.mem_union_right C hz) (hboundary z hz)
  · intro z _hz
    by_cases hzP : z ∈ P
    · simp [patched, hzP]
    · simp [patched, hzP]

/--
Open patch-set data supplies the localized lower-barrier patch interface.
-/
theorem PerronLowerEnvelopeBentQuadraticOpenPiecewisePatchAt.localizedLowerPatchAt
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g} {x : Point n} {J : Jet n}
    (hpatch :
      PerronLowerEnvelopeBentQuadraticOpenPiecewisePatchAt C boundary F g B x J) :
    PerronLowerEnvelopeBentQuadraticLocalizedLowerPatchAt C boundary F g B x J := by
  refine PerronLowerEnvelopeBentQuadraticLocalizedLowerPatchAt.of_piecewiseSet ?_
  intro δ γ V Xb q hXb hq hδpos hγpos hVopen hV hWltq hqCont hneg
  subst Xb
  subst q
  rcases hpatch δ γ V hδpos hγpos hVopen hV hWltq hqCont hneg with
    ⟨P, hPopen, hVsubset, hinactive, hboundary⟩
  refine ⟨P, ?_, hinactive, hboundary⟩
  intro z hz hzV
  exact mem_nhdsWithin_of_mem_nhds (hPopen.mem_nhds (hVsubset z hzV))

/--
Global open patch-set data supplies the global localized lower-barrier patch
interface.
-/
theorem PerronLowerEnvelopeBentQuadraticOpenPiecewisePatch.localizedLowerPatch
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g}
    (hpatch :
      PerronLowerEnvelopeBentQuadraticOpenPiecewisePatch C boundary F g B) :
    PerronLowerEnvelopeBentQuadraticLocalizedLowerPatch C boundary F g B := by
  intro x hx J hJ hneg
  exact (hpatch x hx J hJ hneg).localizedLowerPatchAt

/--
Boundary-away open patch-set data supplies the open piecewise patch interface.
-/
theorem PerronLowerEnvelopeBentQuadraticBoundaryAwayOpenPatchAt.openPiecewisePatchAt
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g} {x : Point n} {J : Jet n}
    (hpatch :
      PerronLowerEnvelopeBentQuadraticBoundaryAwayOpenPatchAt C boundary F g B x J) :
    PerronLowerEnvelopeBentQuadraticOpenPiecewisePatchAt C boundary F g B x J := by
  intro δ γ V Xb q hδpos hγpos hVopen hV hWltq hqCont hneg
  rcases hpatch δ γ V hδpos hγpos hVopen hV hWltq hqCont hneg with
    ⟨P, hPopen, hVsubset, hinactive, hboundaryAway⟩
  exact ⟨P, hPopen, hVsubset, hinactive,
    fun z hz => Or.inl (hboundaryAway z hz)⟩

/--
Global boundary-away open patch-set data supplies the global open piecewise
patch interface.
-/
theorem PerronLowerEnvelopeBentQuadraticBoundaryAwayOpenPatch.openPiecewisePatch
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g}
    (hpatch :
      PerronLowerEnvelopeBentQuadraticBoundaryAwayOpenPatch C boundary F g B) :
    PerronLowerEnvelopeBentQuadraticOpenPiecewisePatch C boundary F g B := by
  intro x hx J hJ hneg
  exact (hpatch x hx J hJ hneg).openPiecewisePatchAt

/--
Ball patch data supplies the boundary-away open patch-set interface.
-/
theorem PerronLowerEnvelopeBentQuadraticBallPatchAt.boundaryAwayOpenPatchAt
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g} {x : Point n} {J : Jet n}
    (hpatch : PerronLowerEnvelopeBentQuadraticBallPatchAt C boundary F g B x J) :
    PerronLowerEnvelopeBentQuadraticBoundaryAwayOpenPatchAt C boundary F g B x J := by
  intro δ γ V Xb q hδpos hγpos hVopen hV hWltq hqCont hneg
  rcases hpatch δ γ V hδpos hγpos hVopen hV hWltq hqCont hneg with
    ⟨r, hrpos, hVball, hinactive, hboundaryAway⟩
  have hboundaryClosure : ∀ z : Point n, z ∈ boundary ->
      z ∉ closure (Metric.ball x r) := by
    intro z hz hzClosure
    exact hboundaryAway z hz (Metric.closure_ball_subset_closedBall hzClosure)
  exact ⟨Metric.ball x r, Metric.isOpen_ball, hVball, hinactive,
    hboundaryClosure⟩

/--
Global ball patch data supplies the global boundary-away open patch-set
interface.
-/
theorem PerronLowerEnvelopeBentQuadraticBallPatch.boundaryAwayOpenPatch
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g}
    (hpatch : PerronLowerEnvelopeBentQuadraticBallPatch C boundary F g B) :
    PerronLowerEnvelopeBentQuadraticBoundaryAwayOpenPatch C boundary F g B := by
  intro x hx J hJ hneg
  exact (hpatch x hx J hJ hneg).boundaryAwayOpenPatchAt

/--
Closed-ball annulus data supplies the ball patch interface.
-/
theorem PerronLowerEnvelopeBentQuadraticClosedBallAnnulusPatchAt.ballPatchAt
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g} {x : Point n} {J : Jet n}
    (hpatch :
      PerronLowerEnvelopeBentQuadraticClosedBallAnnulusPatchAt C boundary F g B x J) :
    PerronLowerEnvelopeBentQuadraticBallPatchAt C boundary F g B x J := by
  intro δ γ V Xb q hδpos hγpos hVopen hV hWltq hqCont hneg
  rcases hpatch δ γ V hδpos hγpos hVopen hV hWltq hqCont hneg with
    ⟨r, hrpos, hVball, hannulus, hboundaryAway⟩
  refine ⟨r, hrpos, hVball, ?_, hboundaryAway⟩
  intro z hz hzV
  by_cases hzClosed : z ∈ Metric.closedBall x r
  · filter_upwards [hannulus z hz hzV hzClosed] with y hy
    exact Or.inr hy
  · filter_upwards [eventually_not_mem_ball_of_not_mem_closedBall
      (C := C) (x := x) (z := z) (r := r) hzClosed] with y hy
    exact Or.inl hy

/--
Global closed-ball annulus data supplies the global ball patch interface.
-/
theorem PerronLowerEnvelopeBentQuadraticClosedBallAnnulusPatch.ballPatch
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g}
    (hpatch :
      PerronLowerEnvelopeBentQuadraticClosedBallAnnulusPatch C boundary F g B) :
    PerronLowerEnvelopeBentQuadraticBallPatch C boundary F g B := by
  intro x hx J hJ hneg
  exact (hpatch x hx J hJ hneg).ballPatchAt

/--
Shrinking closed-ball annulus data supplies the shrinkable localized patch
interface.
-/
theorem PerronLowerEnvelopeBentQuadraticShrinkingClosedBallAnnulusPatchAt.shrinkingPatchAt
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g} {x : Point n} {J : Jet n}
    (hpatch :
      PerronLowerEnvelopeBentQuadraticShrinkingClosedBallAnnulusPatchAt
        C boundary F g B x J) :
    PerronLowerEnvelopeBentQuadraticShrinkingLocalizedLowerPatchAt
      C boundary F g B x J := by
  intro δ γ V Xb q hδpos hγpos hVopen hV hWltq hqCont hneg
  classical
  rcases hpatch δ γ V hδpos hγpos hVopen hV hWltq hqCont hneg with
    ⟨r, hrpos, hballV, hannulus, hboundaryAway⟩
  let P : Set (Point n) := Metric.ball x r
  let patched : Point n -> Real := fun y =>
    if y ∈ P then Max.max (B.lower y) (q y) else B.lower y
  refine ⟨P, patched, Metric.isOpen_ball, ?_, hballV, ?_, ?_, ?_, ?_, ?_⟩
  · exact mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x hrpos)
  · intro z hz hzP
    have hPnhds : P ∈ nhds z :=
      Metric.isOpen_ball.mem_nhds (by simpa [P] using hzP)
    filter_upwards [mem_nhdsWithin_of_mem_nhds hPnhds] with y hyP
    simp [patched, hyP]
  · intro z hz hzP
    by_cases hzClosed : z ∈ Metric.closedBall x r
    · filter_upwards [hannulus z hz hzP hzClosed] with y hy
      have hyq : q y <= B.lower y := by
        simpa [q, Xb] using hy
      by_cases hyP : y ∈ P
      · simp [patched, hyP, max_eq_left hyq]
      · simp [patched, hyP]
    · filter_upwards [eventually_not_mem_ball_of_not_mem_closedBall
        (C := C) (x := x) (z := z) (r := r) hzClosed] with y hyP
      have hyP' : y ∉ P := by
        simpa [P] using hyP
      simp [patched, hyP']
  · intro z hz
    have hzP : z ∉ P := fun hzP => hboundaryAway z hz
      (Metric.ball_subset_closedBall (by simpa [P] using hzP))
    simp [patched, hzP]
  · intro z hz
    apply UpperSemicontinuousOn.piecewise_max_boundary
      B.lower_dirichlet.upperSemicontinuousOn
      (continuous_quadraticModel _ _ _ _)
      (Set.mem_union_right C hz)
    apply Or.inl
    intro hzClosure
    exact hboundaryAway z hz
      (Metric.closure_ball_subset_closedBall (by simpa [P] using hzClosure))
  · intro z _hz
    by_cases hzP : z ∈ P
    · simp [patched, hzP]
    · simp [patched, hzP]

/--
Global shrinking closed-ball annulus data supplies the global shrinkable
localized patch interface.
-/
theorem PerronLowerEnvelopeBentQuadraticShrinkingClosedBallAnnulusPatch.shrinkingPatch
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g}
    (hpatch :
      PerronLowerEnvelopeBentQuadraticShrinkingClosedBallAnnulusPatch
        C boundary F g B) :
    PerronLowerEnvelopeBentQuadraticShrinkingLocalizedLowerPatch
      C boundary F g B := by
  intro x hx J hJ hneg
  exact (hpatch x hx J hJ hneg).shrinkingPatchAt

/--
Small-radius annulus data supplies shrinking annulus data by choosing a radius
inside both the active operator-continuity neighborhood and the analytic
small-radius range.
-/
theorem PerronLowerEnvelopeBentQuadraticSmallRadiusClosedBallAnnulusPatchAt.shrinkingAt
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g} {x : Point n} {J : Jet n}
    (hx : x ∈ C)
    (hpatch :
      PerronLowerEnvelopeBentQuadraticSmallRadiusClosedBallAnnulusPatchAt
        C boundary F g B x J) :
    PerronLowerEnvelopeBentQuadraticShrinkingClosedBallAnnulusPatchAt
      C boundary F g B x J := by
  intro δ γ V Xb q hδpos hγpos hVopen hV hWltq hqCont hneg
  have hxV : x ∈ V := mem_of_mem_nhdsWithin hx hV
  rcases Metric.mem_nhds_iff.mp (hVopen.mem_nhds hxV) with
    ⟨ρV, hρVpos, hρVsubset⟩
  rcases hpatch δ γ V hδpos hγpos hVopen hV hWltq hqCont hneg with
    ⟨ρE, hρEpos, hsmall⟩
  let r : Real := min ρV ρE / 2
  have hminpos : 0 < min ρV ρE := lt_min hρVpos hρEpos
  have hrpos : 0 < r := by
    dsimp [r]
    linarith
  have hr_le_V : r <= ρV := by
    have hhalf_le_min : min ρV ρE / 2 <= min ρV ρE := by
      linarith
    exact hhalf_le_min.trans (min_le_left ρV ρE)
  have hr_le_E : r <= ρE := by
    have hhalf_le_min : min ρV ρE / 2 <= min ρV ρE := by
      linarith
    exact hhalf_le_min.trans (min_le_right ρV ρE)
  rcases hsmall r hrpos hr_le_E with ⟨hannulus, hboundaryAway⟩
  refine ⟨r, hrpos, ?_, hannulus, hboundaryAway⟩
  intro z hzball
  exact hρVsubset (Metric.ball_subset_ball hr_le_V hzball)

/--
Global small-radius annulus data supplies global shrinking annulus data.
-/
theorem PerronLowerEnvelopeBentQuadraticSmallRadiusClosedBallAnnulusPatch.shrinking
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g}
    (hpatch :
      PerronLowerEnvelopeBentQuadraticSmallRadiusClosedBallAnnulusPatch
        C boundary F g B) :
    PerronLowerEnvelopeBentQuadraticShrinkingClosedBallAnnulusPatch
      C boundary F g B := by
  intro x hx J hJ hneg
  exact (hpatch x hx J hJ hneg).shrinkingAt hx

/--
Source-radius annulus data supplies one chosen localized lower-barrier patch.
-/
theorem PerronLowerEnvelopeBentQuadraticSourceClosedBallAnnulusPatchAt.chosenPatchAt
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g} {x : Point n} {J : Jet n}
    (hpatch :
      PerronLowerEnvelopeBentQuadraticSourceClosedBallAnnulusPatchAt
        C boundary F g B x J) :
    PerronLowerEnvelopeBentQuadraticChosenLocalizedLowerPatchAt
      C boundary F g B x J := by
  rcases hpatch with
    ⟨γ, r, V, hγpos, hrpos, hVopen, hV, hballV, hWltq, hqCont,
      hneg, hannulus, hboundaryAway⟩
  classical
  let δ : Real := γ * r ^ 2 / 8
  let Xb : Hessian n := J.hessian - γ • (1 : Hessian n)
  let q : Point n -> Real := fun z =>
    quadraticModel x
      (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + δ)
      J.gradient Xb z
  let P : Set (Point n) := Metric.ball x r
  let patched : Point n -> Real := fun y =>
    if y ∈ P then Max.max (B.lower y) (q y) else B.lower y
  have hδpos : 0 < δ := by
    dsimp [δ]
    positivity
  refine ⟨δ, γ, V, P, patched, hδpos, hγpos, hVopen, hV, hWltq, hqCont,
    hneg, Metric.isOpen_ball, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x hrpos)
  · intro z hzP
    exact hballV z (by simpa [P] using hzP)
  · intro z hz hzP
    have hPnhds : P ∈ nhds z :=
      Metric.isOpen_ball.mem_nhds (by simpa [P] using hzP)
    filter_upwards [mem_nhdsWithin_of_mem_nhds hPnhds] with y hyP
    change patched y = Max.max (B.lower y) (q y)
    simp [patched, hyP]
  · intro z hz hzP
    by_cases hzClosed : z ∈ Metric.closedBall x r
    · have hzBall : z ∉ Metric.ball x r := by
        simpa [P] using hzP
      filter_upwards [hannulus z hz hzBall hzClosed] with y hy
      have hyq : q y <= B.lower y := by
        simpa [q, Xb, δ] using hy
      by_cases hyP : y ∈ P
      · simp [patched, hyP, max_eq_left hyq]
      · simp [patched, hyP]
    · filter_upwards [eventually_not_mem_ball_of_not_mem_closedBall
        (C := C) (x := x) (z := z) (r := r) hzClosed] with y hyP
      have hyP' : y ∉ P := by
        simpa [P] using hyP
      simp [patched, hyP']
  · intro z hz
    have hzP : z ∉ P := fun hzP => hboundaryAway z hz
      (Metric.ball_subset_closedBall (by simpa [P] using hzP))
    simp [patched, hzP]
  · intro z hz
    apply UpperSemicontinuousOn.piecewise_max_boundary
      B.lower_dirichlet.upperSemicontinuousOn
      (continuous_quadraticModel _ _ _ _)
      (Set.mem_union_right C hz)
    apply Or.inl
    intro hzClosure
    exact hboundaryAway z hz
      (Metric.closure_ball_subset_closedBall (by simpa [P] using hzClosure))
  · intro z _hz
    by_cases hzP : z ∈ P
    · simp [patched, hzP]
    · simp [patched, hzP]

/--
Global source-radius annulus data supplies global chosen localized patches.
-/
theorem PerronLowerEnvelopeBentQuadraticSourceClosedBallAnnulusPatch.chosenPatch
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g}
    (hpatch :
      PerronLowerEnvelopeBentQuadraticSourceClosedBallAnnulusPatch
        C boundary F g B) :
    PerronLowerEnvelopeBentQuadraticChosenLocalizedLowerPatch
      C boundary F g B := by
  intro x hx J hJ hneg
  exact (hpatch x hx J hJ hneg).chosenPatchAt

/--
If both the ambient domain and the active neighborhood are open, their
intersection is the active local domain required by the compact-inactive patch
interfaces.
-/
theorem exists_activeDomain_inter_of_isOpen
    {C V : Set (Point n)} (hCopen : IsOpen C) (hVopen : IsOpen V)
    {z : Point n} (hzC : z ∈ C) (hzV : z ∈ V) :
    ∃ D : Set (Point n),
      D ⊆ C ∧
        D ∈ nhdsWithin z C ∧
          (∀ y : Point n, y ∈ D -> D ∈ nhdsWithin y C) ∧
            (∀ y : Point n, y ∈ D -> y ∈ interior D) ∧
              ∀ y : Point n, y ∈ D -> y ∈ V := by
  let D : Set (Point n) := C ∩ V
  have hDopen : IsOpen D := hCopen.inter hVopen
  refine ⟨D, Set.inter_subset_left, ?_, ?_, ?_, ?_⟩
  · exact mem_nhdsWithin_of_mem_nhds (hDopen.mem_nhds ⟨hzC, hzV⟩)
  · intro y hy
    exact mem_nhdsWithin_of_mem_nhds (hDopen.mem_nhds hy)
  · intro y hy
    simpa [hDopen.interior_eq] using hy
  · intro y hy
    exact hy.2

/--
Bent quadratic max-patch data feeds the generic strict-local max-patch
interface.
-/
theorem PerronLowerEnvelopeBentQuadraticMaxPatchAt.strictLocalPatchAt
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g} {x : Point n} {J : Jet n}
    (hpatch : PerronLowerEnvelopeBentQuadraticMaxPatchAt C boundary F g B x J) :
    PerronLowerEnvelopeStrictLocalPatchAt C boundary F g B x := by
  rcases hpatch with
    ⟨δ, γ, V, old, hδpos, _hγpos, hV, hWltq, hqCont, hold, hmax⟩
  let Xb : Hessian n := J.hessian - γ • (1 : Hessian n)
  let q : Point n -> Real := fun z =>
    quadraticModel x
      (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + δ)
      J.gradient Xb z
  rcases exists_between hWltq with ⟨a, hWlta, haqx⟩
  have hqAbove : {y : Point n | a < q y} ∈ nhdsWithin x C :=
    lowerSemicontinuousWithinAt_iff.mp hqCont.lowerSemicontinuousWithinAt a haqx
  refine ⟨a, V ∩ {y : Point n | a < q y}, old, q,
    Filter.inter_mem hV hqAbove, ?_, hWlta, hold, ?_⟩
  · intro y hy
    exact hy.2
  · simpa [q, Xb] using hmax

/--
Global bent quadratic max-patch data feeds the global strict-local patch
interface.
-/
theorem PerronLowerEnvelopeBentQuadraticMaxPatch.strictLocalPatch
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g}
    (hpatch : PerronLowerEnvelopeBentQuadraticMaxPatch C boundary F g B) :
    PerronLowerEnvelopeStrictLocalPatch C boundary F g B := by
  intro x hx J hJ hneg
  exact (hpatch x hx J hJ hneg).strictLocalPatchAt

end ViscositySolns
