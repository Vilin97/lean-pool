/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Existence.Perron.Bump.QuadraticGluing.AnnulusSelectionPatches
public import LeanPool.ViscositySolutionTheory.ViscositySolns.Existence.Perron.Bump.QuadraticGluing.CompactInactivePatches

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Quadratic gluing data for the Perron bump step (BentStrictNegativity)

Part of the quadratic-gluing development connecting the lifted quadratic
supplied by operator continuity to the strict local max-patch formulation.
Split from `QuadraticGluing.lean`; see the umbrella module docstring.
-/

@[expose] public noncomputable section

open Filter
open scoped MatrixOrder

namespace ViscositySolns

variable {n : Nat}

namespace PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallLowerEnvelopeLscSelectionPatchAt

/--
The outer closed annulus supplies the abstract transition-annulus selection
interface. Local lower boundedness compares the lower relaxed Perron envelope
with the Perron envelope on the annulus, and lower semicontinuity turns
pointwise Perron-branch approximation into local domination.
-/
theorem sourceAnnulusSelectionPatchAt
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g} {x : Point n} {J : Jet n}
    (hpatch :
      PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallLowerEnvelopeLscSelectionPatchAt
        C boundary F g B x J)
    (hlowerBddBelow : ∀ z : Point n, z ∈ C ∪ boundary ->
      (nhdsWithin z C).IsBoundedUnder (· >= ·) B.lower) :
    PerronLowerEnvelopeBentQuadraticSourceAnnulusSelectionPatchAt
      C boundary F g B x J := by
  rcases hpatch with
    ⟨γ, r, V, hγpos, hrpos, hVopen, hV, hballV, hclosedBallC,
      hboundaryOutside, hWltq, hqCont, hneg, hlowerAnnulus, hfamilyLsc⟩
  let δ : Real := γ * r ^ 2 / 8
  let Xb : Hessian n := J.hessian - γ • (1 : Hessian n)
  let q : Point n -> Real := fun z =>
    quadraticModel x
      (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + δ)
      J.gradient Xb z
  let K : Set (Point n) := {z : Point n | 3 * r / 4 <= dist z x ∧ dist z x <= r}
  have hKcompact : IsCompact K := by
    have hClosedLower : IsClosed {z : Point n | 3 * r / 4 <= dist z x} := by
      exact isClosed_le continuous_const (continuous_id.dist continuous_const)
    have hCompactClosed : IsCompact (Metric.closedBall x r) :=
      isCompact_closedBall x r
    have hCompactInter : IsCompact (Metric.closedBall x r ∩
        {z : Point n | 3 * r / 4 <= dist z x}) :=
      hCompactClosed.inter_right hClosedLower
    simpa [K, Metric.mem_closedBall, Set.inter_def, and_comm, and_left_comm,
      and_assoc] using hCompactInter
  refine ⟨γ, r, V, K, hγpos, hrpos, hVopen, hV, hballV, hWltq,
    hqCont, hneg, hKcompact, ?_, ?_, ?_, ?_⟩
  · intro z _hz
    exact self_mem_nhdsWithin
  · intro z hzK
    have hzClosed : z ∈ Metric.closedBall x r := by
      simpa [Metric.mem_closedBall] using hzK.2
    have hzC : z ∈ C := hclosedBallC z hzClosed
    have hle :
        lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) z <=
          perronEnvelope C boundary F g B.lower B.upper z :=
      lowerEnvelope_le hzC
        (B.perronEnvelope_isBoundedUnder_ge (hlowerBddBelow z (Or.inl hzC)))
    have henv : q z < perronEnvelope C boundary F g B.lower B.upper z :=
      lt_of_lt_of_le (hlowerAnnulus z hzK) hle
    have hbdd : BddAbove {a : Real | ∃ w : Point n -> Real,
        PerronClass C boundary F g B.lower B.upper w ∧ a = w z} := by
      refine ⟨B.upper z, ?_⟩
      intro a ha
      rcases ha with ⟨w, hw, rfl⟩
      exact hw.le_upper (Or.inl hzC)
    rcases B.exists_perronFamily_gt_of_lt_perronEnvelope_of_bddAbove
        hbdd henv with ⟨w, hwgt⟩
    refine ⟨w, ?_⟩
    rcases exists_between hwgt with ⟨a, hqa, haw⟩
    have hqContK : ContinuousWithinAt q K z := by
      exact (continuous_quadraticModel x
        (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + δ)
        J.gradient Xb).continuousWithinAt
    have hqNear : ∀ᶠ y in nhdsWithin z K, q y < a :=
      hqContK (isOpen_Iio.mem_nhds hqa)
    have hwNear : ∀ᶠ y in nhdsWithin z K, a < w.fun y :=
      (hfamilyLsc w z hzK) a haw
    filter_upwards [hqNear, hwNear] with y hyq hyw
    exact le_of_lt (hyq.trans hyw)
  · intro z _hzC hzNotBall
    by_cases hzClosed : z ∈ Metric.closedBall x r
    · have hzle : dist z x <= r := by
        simpa [Metric.mem_closedBall] using hzClosed
      have hrle : r <= dist z x := by
        simpa [Metric.mem_ball, not_lt] using hzNotBall
      have hdist_eq : dist z x = r := le_antisymm hzle hrle
      let ε : Real := r / 4
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
        have hyLower : 3 * r / 4 <= dist y x := by
          dsimp [ε] at hlt
          linarith
        exact Or.inr ⟨hyLower, hyUpper⟩
    · filter_upwards
        [eventually_not_mem_ball_of_not_mem_closedBall
          (C := C) (x := x) (z := z) (r := r) hzClosed] with y hy
      exact Or.inl hy
  · intro z hzBoundary hzBall
    exact hboundaryOutside z hzBoundary
      (hclosedBallC z hzBall)

end PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallLowerEnvelopeLscSelectionPatchAt

namespace PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallLowerEnvelopeLscSelectionPatch

/--
Global outer-transition closed-ball lower-envelope data supplies the abstract
source annulus selection interface.
-/
theorem sourceAnnulusSelectionPatch
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g}
    (hpatch :
      PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallLowerEnvelopeLscSelectionPatch
        C boundary F g B)
    (hlowerBddBelow : ∀ z : Point n, z ∈ C ∪ boundary ->
      (nhdsWithin z C).IsBoundedUnder (· >= ·) B.lower) :
    PerronLowerEnvelopeBentQuadraticSourceAnnulusSelectionPatch
      C boundary F g B := by
  intro x hx J hJ hneg
  exact (hpatch x hx J hJ hneg).sourceAnnulusSelectionPatchAt
    hlowerBddBelow

end PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallLowerEnvelopeLscSelectionPatch

/--
On the outer transition annulus, the source lift `γ * r^2 / 8` is strictly
smaller than the bend margin coming from the subjet support estimate.
-/
theorem sourceOuterAnnulus_lift_lt_bendMargin
    {γ r : Real} {x z : Point n}
    (hγpos : 0 < γ) (hrpos : 0 < r)
    (hzK : 3 * r / 4 <= dist z x ∧ dist z x <= r) :
    γ * r ^ 2 / 8 < ((1 / 4 : Real) * γ) * ‖z - x‖ ^ 2 := by
  have hdist_norm : dist z x = ‖z - x‖ := by
    rw [dist_eq_norm]
  have hnorm_lower : 3 * r / 4 <= ‖z - x‖ := by
    simpa [hdist_norm] using hzK.1
  have hleft_nonneg : 0 <= 3 * r / 4 := by
    linarith
  have hnorm_sq :
      (3 * r / 4) ^ 2 <= ‖z - x‖ ^ 2 :=
    (sq_le_sq₀ hleft_nonneg (norm_nonneg (z - x))).2 hnorm_lower
  have hr_sq_pos : 0 < r ^ 2 := sq_pos_of_pos hrpos
  have hmargin_no_gamma : r ^ 2 / 8 < (1 / 4 : Real) * ‖z - x‖ ^ 2 := by
    nlinarith
  have hmul := mul_lt_mul_of_pos_left hmargin_no_gamma hγpos
  nlinarith

/--
Geometric small-radius semijet data.

For the bend and active neighborhood supplied by operator continuity, this
package supplies the domain geometry and branch lower semicontinuity on all
sufficiently small source outer annuli.
-/
def PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallGeometricSemijetLscSelectionPatchAt
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) (x : Point n) (_J : Jet n) :
    Prop :=
  ∀ γ : Real, ∀ V : Set (Point n),
    0 < γ ->
      IsOpen V ->
        V ∈ nhdsWithin x C ->
          ∃ ρ : Real,
            0 < ρ ∧
              (∀ z : Point n, z ∈ boundary -> z ∉ C) ∧
                ∀ r : Real, 0 < r -> r <= ρ ->
                  let K : Set (Point n) :=
                    {z : Point n | 3 * r / 4 <= dist z x ∧ dist z x <= r}
                  (∀ z : Point n, z ∈ Metric.closedBall x r -> z ∈ C) ∧
                    ∀ w : PerronFamily C boundary F g B.lower B.upper,
                      LowerSemicontinuousOn w.fun K

/--
Geometric small-radius semijet data at every failed lower-envelope subjet
inequality.
-/
def PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallGeometricSemijetLscSelectionPatch
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallGeometricSemijetLscSelectionPatchAt
          C boundary F g B x J

/--
Pure outer-annulus lower-semicontinuity radius data.

For any bend and active neighborhood later chosen by operator continuity, this
package only supplies a small-radius scale on which Perron-family branches are
lower semicontinuous on the source outer annulus. Domain closed-ball
containment is derived separately from openness of `C`.
-/
def PerronLowerEnvelopeBentQuadraticSourceOuterAnnulusLscSelectionPatchAt
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) (x : Point n) (_J : Jet n) :
    Prop :=
  ∀ γ : Real, ∀ V : Set (Point n),
    0 < γ ->
      IsOpen V ->
        V ∈ nhdsWithin x C ->
          ∃ ρ : Real,
            0 < ρ ∧
              ∀ r : Real, 0 < r -> r <= ρ ->
                let K : Set (Point n) :=
                  {z : Point n | 3 * r / 4 <= dist z x ∧ dist z x <= r}
                ∀ w : PerronFamily C boundary F g B.lower B.upper,
                  LowerSemicontinuousOn w.fun K

/--
Pure outer-annulus lower-semicontinuity radius data at every failed
lower-envelope subjet inequality.
-/
def PerronLowerEnvelopeBentQuadraticSourceOuterAnnulusLscSelectionPatch
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        PerronLowerEnvelopeBentQuadraticSourceOuterAnnulusLscSelectionPatchAt
          C boundary F g B x J

/--
Domain lower-semicontinuity for every Perron-family branch.

This is the branch regularity actually needed to supply the source outer
annulus LSC package: once the contact point is interior to the open PDE domain,
the annulus radius can be chosen small enough that the annulus lies in `C`.
-/
def PerronFamilyLowerSemicontinuousOnDomain
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ w : PerronFamily C boundary F g B.lower B.upper,
    LowerSemicontinuousOn w.fun C

/--
Operator continuity supplies a bend, an active open neighborhood, and a
small-radius scale on which the source-radius lifted bent quadratic has
strictly negative operator value.
-/
theorem OperatorContinuous.exists_sourceOuterClosedBall_smallRadius_bentStrictNegativity
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g} (hF : OperatorContinuous F)
    {x : Point n} {J : Jet n}
    (hneg :
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0) :
    ∃ γ : Real, ∃ V : Set (Point n), ∃ ρ : Real,
      let Xb : Hessian n := J.hessian - γ • (1 : Hessian n)
      0 < γ ∧
        IsOpen V ∧
          V ∈ nhdsWithin x C ∧
            0 < ρ ∧
              ∀ r : Real, 0 < r -> r <= ρ ->
                let δ : Real := γ * r ^ 2 / 8
                let q : Point n -> Real := fun z =>
                  quadraticModel x
                    (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + δ)
                    J.gradient Xb z
                ∀ z : Point n, z ∈ V -> z ∈ C ->
                  F z (q z)
                      (quadraticModelJetAt x J.gradient Xb z).gradient
                      (quadraticModelJetAt x J.gradient Xb z).hessian < 0 := by
  let W : Point n -> Real :=
    lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)
  have hzero :
      F x (quadraticModel x (W x) J.gradient
            (J.hessian - (0 : Real) • (1 : Hessian n)) x)
          (quadraticModelJetAt x J.gradient
            (J.hessian - (0 : Real) • (1 : Hessian n)) x).gradient
          (quadraticModelJetAt x J.gradient
            (J.hessian - (0 : Real) • (1 : Hessian n)) x).hessian < 0 := by
    simpa [W, quadraticModel] using hneg
  have hpathγ : Continuous fun γ : Real =>
      ((x,
          quadraticModel x (W x) J.gradient
            (J.hessian - γ • (1 : Hessian n)) x),
        quadraticModelJetAt x J.gradient
          (J.hessian - γ • (1 : Hessian n)) x) := by
    have hH : Continuous fun γ : Real =>
        J.hessian - γ • (1 : Hessian n) :=
      continuous_const.sub (continuous_id.smul continuous_const)
    have hval : Continuous fun γ : Real =>
        quadraticModel x (W x) J.gradient
          (J.hessian - γ • (1 : Hessian n)) x := by
      let jetPath : Real -> Jet n := fun γ =>
        { gradient := J.gradient
          hessian := J.hessian - γ • (1 : Hessian n) }
      have hJet : Continuous jetPath := by
        apply continuous_induced_rng.mpr
        change Continuous fun γ : Real =>
          ((jetPath γ).gradient, (jetPath γ).hessian)
        simpa [jetPath] using Continuous.prodMk continuous_const hH
      exact (continuous_quadraticModel_jet x (W x) x).comp hJet
    have hjet : Continuous fun γ : Real =>
        quadraticModelJetAt x J.gradient
          (J.hessian - γ • (1 : Hessian n)) x := by
      apply continuous_induced_rng.mpr
      change Continuous fun γ : Real =>
        ((quadraticModelJetAt x J.gradient
            (J.hessian - γ • (1 : Hessian n)) x).gradient,
          (quadraticModelJetAt x J.gradient
            (J.hessian - γ • (1 : Hessian n)) x).hessian)
      simpa [quadraticModelJetAt] using Continuous.prodMk continuous_const hH
    exact Continuous.prodMk (Continuous.prodMk continuous_const hval) hjet
  have hcontγ : Continuous fun γ : Real =>
      F x
          (quadraticModel x (W x) J.gradient
            (J.hessian - γ • (1 : Hessian n)) x)
          (quadraticModelJetAt x J.gradient
            (J.hessian - γ • (1 : Hessian n)) x).gradient
          (quadraticModelJetAt x J.gradient
            (J.hessian - γ • (1 : Hessian n)) x).hessian := by
    exact hF.continuous.comp hpathγ
  have hnearγ : ∀ᶠ γ in nhds (0 : Real),
      F x
          (quadraticModel x (W x) J.gradient
            (J.hessian - γ • (1 : Hessian n)) x)
          (quadraticModelJetAt x J.gradient
            (J.hessian - γ • (1 : Hessian n)) x).gradient
          (quadraticModelJetAt x J.gradient
            (J.hessian - γ • (1 : Hessian n)) x).hessian < 0 := by
    exact hcontγ.continuousAt (isOpen_Iio.mem_nhds hzero)
  have : NeBot (nhdsWithin (0 : Real) (Set.Ioi 0)) := by infer_instance
  have hnearγWithin : ∀ᶠ γ in nhdsWithin (0 : Real) (Set.Ioi 0),
      F x
          (quadraticModel x (W x) J.gradient
            (J.hessian - γ • (1 : Hessian n)) x)
          (quadraticModelJetAt x J.gradient
            (J.hessian - γ • (1 : Hessian n)) x).gradient
          (quadraticModelJetAt x J.gradient
            (J.hessian - γ • (1 : Hessian n)) x).hessian < 0 :=
    hnearγ.filter_mono nhdsWithin_le_nhds
  have hposWithin : ∀ᶠ γ in nhdsWithin (0 : Real) (Set.Ioi 0),
      γ ∈ Set.Ioi (0 : Real) :=
    self_mem_nhdsWithin
  rcases (hnearγWithin.and hposWithin).exists with
    ⟨γ, hbaseBent, hγpos⟩
  let Xb : Hessian n := J.hessian - γ • (1 : Hessian n)
  let sourceEval : Point n × Real -> Real := fun y =>
    F y.1
      (quadraticModel x (W x + γ * y.2 ^ 2 / 8) J.gradient Xb y.1)
      (quadraticModelJetAt x J.gradient Xb y.1).gradient
      (quadraticModelJetAt x J.gradient Xb y.1).hessian
  let sourceNegSet : Set (Point n × Real) := {y | sourceEval y < 0}
  have hsourceCont : Continuous sourceEval := by
    have hdx : Continuous fun y : Point n × Real => y.1 - x :=
      continuous_fst.sub continuous_const
    have hlift : Continuous fun y : Point n × Real => W x + γ * y.2 ^ 2 / 8 := by
      have ht2 : Continuous fun y : Point n × Real => y.2 ^ 2 :=
        continuous_snd.pow 2
      exact continuous_const.add ((continuous_const.mul ht2).div_const 8)
    have hlin : Continuous fun y : Point n × Real =>
        dotProduct J.gradient (y.1 - x) :=
      continuous_const.dotProduct hdx
    have hquad : Continuous fun y : Point n × Real =>
        dotProduct (Matrix.mulVec Xb (y.1 - x)) (y.1 - x) := by
      exact (continuous_const.matrix_mulVec hdx).dotProduct hdx
    have hq : Continuous fun y : Point n × Real =>
        quadraticModel x (W x + γ * y.2 ^ 2 / 8) J.gradient Xb y.1 := by
      have htotal : Continuous fun y : Point n × Real =>
          (W x + γ * y.2 ^ 2 / 8) + dotProduct J.gradient (y.1 - x) +
            (1 / 2 : Real) * dotProduct (Matrix.mulVec Xb (y.1 - x)) (y.1 - x) :=
        (hlift.add hlin).add (continuous_const.mul hquad)
      simpa [quadraticModel, add_assoc] using htotal
    have hjet : Continuous fun y : Point n × Real =>
        quadraticModelJetAt x J.gradient Xb y.1 :=
      (continuous_quadraticModelJetAt x J.gradient Xb).comp continuous_fst
    have hpath : Continuous fun y : Point n × Real =>
        ((y.1,
            quadraticModel x (W x + γ * y.2 ^ 2 / 8) J.gradient Xb y.1),
          quadraticModelJetAt x J.gradient Xb y.1) :=
      Continuous.prodMk (Continuous.prodMk continuous_fst hq) hjet
    exact hF.continuous.comp hpath
  have hsourceOpen : IsOpen sourceNegSet := by
    exact isOpen_Iio.preimage hsourceCont
  have hbaseSource : (x, (0 : Real)) ∈ sourceNegSet := by
    simpa [sourceNegSet, sourceEval, Xb, W, quadraticModel] using hbaseBent
  have hsourceNhds : sourceNegSet ∈ nhds (x, (0 : Real)) :=
    hsourceOpen.mem_nhds hbaseSource
  rcases mem_nhds_prod_iff.1 hsourceNhds with
    ⟨U, hU, T, hT, hUT⟩
  rcases Metric.mem_nhds_iff.1 hU with ⟨ε, hεpos, hεU⟩
  rcases Metric.mem_nhds_iff.1 hT with ⟨σ, hσpos, hσT⟩
  let V : Set (Point n) := Metric.ball x ε
  let ρ : Real := σ / 2
  have hρpos : 0 < ρ := by
    dsimp [ρ]
    linarith
  refine ⟨γ, V, ρ, hγpos, Metric.isOpen_ball,
    mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x hεpos), hρpos, ?_⟩
  intro r hrpos hrle
  dsimp
  intro z hzV _hzC
  have hzU : z ∈ U := hεU hzV
  have hrT : r ∈ T := by
    have hr_abs : dist r (0 : Real) < σ := by
      rw [Real.dist_eq]
      have hsub : r - 0 = r := by ring
      rw [hsub, abs_of_nonneg hrpos.le]
      dsimp [ρ] at hrle
      linarith
    exact hσT hr_abs
  have hzrt : (z, r) ∈ sourceNegSet := hUT ⟨hzU, hrT⟩
  simpa [sourceNegSet, sourceEval, Xb, W] using hzrt

namespace PerronLowerEnvelopeBentQuadraticSourceOuterAnnulusLscSelectionPatchAt

/--
Open-domain geometry turns pure annulus-LSC radius data into the geometric
closed-ball semijet package.
-/
theorem geometricSemijetLscSelectionPatchAt
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g} {x : Point n} {J : Jet n}
    (hpatch :
      PerronLowerEnvelopeBentQuadraticSourceOuterAnnulusLscSelectionPatchAt
        C boundary F g B x J)
    (hx : x ∈ C) (hCopen : IsOpen C)
    (hboundaryOutside : ∀ z : Point n, z ∈ boundary -> z ∉ C) :
    PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallGeometricSemijetLscSelectionPatchAt
      C boundary F g B x J := by
  intro γ V hγpos hVopen hV
  rcases hpatch γ V hγpos hVopen hV with ⟨ρLsc, hρLscpos, hLsc⟩
  rcases Metric.mem_nhds_iff.1 (hCopen.mem_nhds hx) with
    ⟨ε, hεpos, hεC⟩
  let ρ : Real := min ρLsc (ε / 2)
  have hρpos : 0 < ρ := lt_min hρLscpos (half_pos hεpos)
  refine ⟨ρ, hρpos, hboundaryOutside, ?_⟩
  intro r hrpos hrle
  have hr_le_Lsc : r <= ρLsc := hrle.trans (min_le_left ρLsc (ε / 2))
  have hr_lt_ε : r < ε := by
    have hr_le_half : r <= ε / 2 := hrle.trans (min_le_right ρLsc (ε / 2))
    linarith
  refine ⟨?_, hLsc r hrpos hr_le_Lsc⟩
  intro z hzClosed
  exact hεC (Metric.closedBall_subset_ball hr_lt_ε hzClosed)

end PerronLowerEnvelopeBentQuadraticSourceOuterAnnulusLscSelectionPatchAt

namespace PerronLowerEnvelopeBentQuadraticSourceOuterAnnulusLscSelectionPatch

/--
Global pure annulus-LSC data supplies the geometric semijet package when the
domain is open and the Dirichlet boundary is outside the domain.
-/
theorem geometricSemijetLscSelectionPatch
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g}
    (hpatch :
      PerronLowerEnvelopeBentQuadraticSourceOuterAnnulusLscSelectionPatch
        C boundary F g B)
    (hCopen : IsOpen C)
    (hboundaryOutside : ∀ z : Point n, z ∈ boundary -> z ∉ C) :
    PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallGeometricSemijetLscSelectionPatch
      C boundary F g B := by
  intro x hx J hJ hneg
  exact (hpatch x hx J hJ hneg).geometricSemijetLscSelectionPatchAt
    hx hCopen hboundaryOutside

end PerronLowerEnvelopeBentQuadraticSourceOuterAnnulusLscSelectionPatch

namespace PerronFamilyLowerSemicontinuousOnDomain

/--
Domain lower-semicontinuity for Perron-family branches supplies the pure
outer-annulus LSC package on an open domain.
-/
theorem bentSourceOuterAnnulusLscSelectionPatch
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g}
    (hreg : PerronFamilyLowerSemicontinuousOnDomain C boundary F g B)
    (hCopen : IsOpen C) :
    PerronLowerEnvelopeBentQuadraticSourceOuterAnnulusLscSelectionPatch
      C boundary F g B := by
  intro x hx _J _hJ _hneg γ V _hγpos _hVopen _hV
  rcases Metric.mem_nhds_iff.1 (hCopen.mem_nhds hx) with
    ⟨ε, hεpos, hεC⟩
  refine ⟨ε / 2, half_pos hεpos, ?_⟩
  intro r _hrpos hrle
  let K : Set (Point n) := {z : Point n | 3 * r / 4 <= dist z x ∧ dist z x <= r}
  dsimp only
  intro w
  exact (hreg w).mono (by
    intro z hzK
    have hdist_lt : dist z x < ε := by
      linarith [hzK.2]
    exact hεC (by
      simpa [Metric.mem_ball] using hdist_lt))

end PerronFamilyLowerSemicontinuousOnDomain

/--
Small-radius semijet-driven outer-annulus source data.

This is the geometric small-radius form of the current semijet package: once
the bend, active neighborhood, and radius scale are chosen, all sufficiently
small radii have the closed ball in the domain, the patch ball in the active
neighborhood, the strict operator inequality, and Perron-family lower
semicontinuity on the outer transition annulus. The bridge below shrinks the
radius further to place that annulus inside any prescribed relative
neighborhood.
-/
def PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallSmallRadiusSemijetLscSelectionPatchAt
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
                let K : Set (Point n) :=
                  {z : Point n | 3 * r / 4 <= dist z x ∧ dist z x <= r}
                (∀ z : Point n, z ∈ Metric.closedBall x r -> z ∈ C) ∧
                  (∀ z : Point n, z ∈ V -> z ∈ C ->
                    F z (q z)
                        (quadraticModelJetAt x J.gradient Xb z).gradient
                        (quadraticModelJetAt x J.gradient Xb z).hessian < 0) ∧
                    ∀ w : PerronFamily C boundary F g B.lower B.upper,
                      LowerSemicontinuousOn w.fun K

/--
Small-radius semijet-driven outer-annulus source data at every failed
lower-envelope subjet inequality.
-/
def PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallSmallRadiusSemijetLscSelectionPatch
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallSmallRadiusSemijetLscSelectionPatchAt
          C boundary F g B x J

namespace PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallGeometricSemijetLscSelectionPatchAt

/--
Operator continuity supplies the strict-negativity part of the small-radius
semijet package; the geometric package supplies the closed-ball domain,
boundary, and branch-lower-semicontinuity fields.
-/
theorem smallRadiusSemijetLscSelectionPatchAt
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g} {x : Point n} {J : Jet n}
    (hgeom :
      PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallGeometricSemijetLscSelectionPatchAt
        C boundary F g B x J)
    (hF : OperatorContinuous F)
    (hneg :
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0) :
    PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallSmallRadiusSemijetLscSelectionPatchAt
      C boundary F g B x J := by
  rcases hF.exists_sourceOuterClosedBall_smallRadius_bentStrictNegativity
      (C := C) (boundary := boundary) (g := g) (B := B) (x := x) (J := J)
      hneg with
    ⟨γ, V, ρneg, hγpos, hVopen, hV, hρnegpos, hstrict⟩
  rcases hgeom γ V hγpos hVopen hV with
    ⟨ρgeom, hρgeompos, hboundaryOutside, hgeomSmall⟩
  let ρ : Real := min ρneg ρgeom
  have hρpos : 0 < ρ := lt_min hρnegpos hρgeompos
  refine ⟨γ, V, ρ, hγpos, hVopen, hV, hρpos, hboundaryOutside, ?_⟩
  intro r hrpos hrle
  have hr_le_neg : r <= ρneg := hrle.trans (min_le_left ρneg ρgeom)
  have hr_le_geom : r <= ρgeom := hrle.trans (min_le_right ρneg ρgeom)
  rcases hgeomSmall r hrpos hr_le_geom with ⟨hclosedBallC, hfamilyLsc⟩
  refine ⟨hclosedBallC, ?_, hfamilyLsc⟩
  simpa using hstrict r hrpos hr_le_neg

end PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallGeometricSemijetLscSelectionPatchAt

namespace PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallGeometricSemijetLscSelectionPatch

/--
Global geometric semijet data supplies the small-radius semijet package once
operator continuity provides the source strict-negativity scale.
-/
theorem smallRadiusSemijetLscSelectionPatch
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g}
    (hgeom :
      PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallGeometricSemijetLscSelectionPatch
        C boundary F g B)
    (hF : OperatorContinuous F) :
    PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallSmallRadiusSemijetLscSelectionPatch
      C boundary F g B := by
  intro x hx J hJ hneg
  exact (hgeom x hx J hJ hneg).smallRadiusSemijetLscSelectionPatchAt hF hneg

end PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallGeometricSemijetLscSelectionPatch

/--
Semijet-driven outer-annulus source data.

The caller chooses the bend and active neighborhood first. For every relative
neighborhood supplied later, it can choose a sufficiently small patch radius so
the outer transition annulus lies inside that neighborhood. The bridge below
uses the neighborhood supplied by the subjet support estimate.
-/
def PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallSemijetLscSelectionPatchAt
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
                            (∀ z : Point n, z ∈ K -> z ∈ S) ∧
                              ∀ w : PerronFamily C boundary F g B.lower B.upper,
                                LowerSemicontinuousOn w.fun K

/--
Semijet-driven outer-annulus source data at every failed lower-envelope subjet
inequality.
-/
def PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallSemijetLscSelectionPatch
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallSemijetLscSelectionPatchAt
          C boundary F g B x J

namespace PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallSemijetLscSelectionPatchAt

/--
The semijet support estimate supplies strict lower-envelope domination on the
outer annulus once the annulus is chosen inside its relative neighborhood.
-/
theorem outerClosedBallLowerEnvelopeLscSelectionPatchAt
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g} {x : Point n} {J : Jet n}
    (hpatch :
      PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallSemijetLscSelectionPatchAt
        C boundary F g B x J)
    (hJ : J ∈ Subjet C
      (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x) :
    PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallLowerEnvelopeLscSelectionPatchAt
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
      hqCont, hneg, hKS, hfamilyLsc⟩
  let δ : Real := γ * r ^ 2 / 8
  let q : Point n -> Real := fun z =>
    quadraticModel x (W x + δ) J.gradient Xb z
  let K : Set (Point n) := {z : Point n | 3 * r / 4 <= dist z x ∧ dist z x <= r}
  refine ⟨γ, r, V, hγpos, hrpos, hVopen, hV, hballV,
    hclosedBallC, hboundaryOutside, ?_, ?_, ?_, ?_, ?_⟩
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
  · simpa [K] using hfamilyLsc

/--
The semijet support estimate also supplies the no-branch-LSC lower-envelope
package by forgetting the legacy branch lower-semicontinuity field.
-/
theorem outerClosedBallLowerEnvelopePatchAt
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g} {x : Point n} {J : Jet n}
    (hpatch :
      PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallSemijetLscSelectionPatchAt
        C boundary F g B x J)
    (hJ : J ∈ Subjet C
      (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x) :
    PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallLowerEnvelopePatchAt
      C boundary F g B x J :=
  (hpatch.outerClosedBallLowerEnvelopeLscSelectionPatchAt hJ).lowerEnvelopePatchAt

end PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallSemijetLscSelectionPatchAt

namespace PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallSemijetLscSelectionPatch

/--
Global semijet-driven outer-annulus source data supplies the current
outer-annulus lower-envelope package.
-/
theorem outerClosedBallLowerEnvelopeLscSelectionPatch
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g}
    (hpatch :
      PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallSemijetLscSelectionPatch
        C boundary F g B) :
    PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallLowerEnvelopeLscSelectionPatch
      C boundary F g B := by
  intro x hx J hJ hneg
  exact (hpatch x hx J hJ hneg).outerClosedBallLowerEnvelopeLscSelectionPatchAt hJ

/--
Global semijet-driven outer-annulus source data supplies the no-branch-LSC
outer-annulus lower-envelope package.
-/
theorem outerClosedBallLowerEnvelopePatch
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g}
    (hpatch :
      PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallSemijetLscSelectionPatch
        C boundary F g B) :
    PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallLowerEnvelopePatch
      C boundary F g B := by
  intro x hx J hJ hneg
  exact (hpatch x hx J hJ hneg).outerClosedBallLowerEnvelopePatchAt hJ

end PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallSemijetLscSelectionPatch

namespace PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallSmallRadiusSemijetLscSelectionPatchAt

/--
Small-radius data supplies the relative-neighborhood selection package by
shrinking the radius so the explicit outer annulus lies in the prescribed
relative neighborhood.
-/
theorem semijetLscSelectionPatchAt
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g} {x : Point n} {J : Jet n}
    (hx : x ∈ C)
    (hpatch :
      PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallSmallRadiusSemijetLscSelectionPatchAt
        C boundary F g B x J) :
    PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallSemijetLscSelectionPatchAt
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
  rcases hsmall r hrpos hr_le_ρ with ⟨hclosedBallC, hneg, hfamilyLsc⟩
  have hballV : ∀ z : Point n, z ∈ Metric.ball x r -> z ∈ V := by
    intro z hz
    exact hρVsubset (Metric.ball_subset_ball hr_le_ρV hz)
  let δ : Real := γ * r ^ 2 / 8
  let q : Point n -> Real := fun z => quadraticModel x (W x + δ) J.gradient Xb z
  let K : Set (Point n) := {z : Point n | 3 * r / 4 <= dist z x ∧ dist z x <= r}
  refine ⟨r, hrpos, hballV, hclosedBallC, hboundaryOutside, ?_, ?_, hneg, ?_,
    ?_⟩
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
  · simpa [K, q, W, Xb] using hfamilyLsc

end PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallSmallRadiusSemijetLscSelectionPatchAt

namespace PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallSmallRadiusSemijetLscSelectionPatch

/--
Global small-radius data supplies the semijet-driven relative-neighborhood
selection package.
-/
theorem semijetLscSelectionPatch
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g}
    (hpatch :
      PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallSmallRadiusSemijetLscSelectionPatch
        C boundary F g B) :
    PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallSemijetLscSelectionPatch
      C boundary F g B := by
  intro x hx J hJ hneg
  exact (hpatch x hx J hJ hneg).semijetLscSelectionPatchAt hx

/--
Global small-radius semijet data supplies the no-branch-LSC outer-annulus
lower-envelope package.
-/
theorem outerClosedBallLowerEnvelopePatch
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g}
    (hpatch :
      PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallSmallRadiusSemijetLscSelectionPatch
        C boundary F g B) :
    PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallLowerEnvelopePatch
      C boundary F g B :=
  hpatch.semijetLscSelectionPatch.outerClosedBallLowerEnvelopePatch

end PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallSmallRadiusSemijetLscSelectionPatch

namespace PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallGeometricSemijetLscSelectionPatch

/--
Global geometric semijet data supplies the no-branch-LSC outer-annulus
lower-envelope package once operator continuity provides the source
strict-negativity scale.
-/
theorem outerClosedBallLowerEnvelopePatch
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g}
    (hgeom :
      PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallGeometricSemijetLscSelectionPatch
        C boundary F g B)
    (hF : OperatorContinuous F) :
    PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallLowerEnvelopePatch
      C boundary F g B :=
  (hgeom.smallRadiusSemijetLscSelectionPatch hF).outerClosedBallLowerEnvelopePatch

end PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallGeometricSemijetLscSelectionPatch

/--
Geometric small-radius semijet data without Perron-family branch
lower-semicontinuity.

For any bend and active neighborhood later chosen by operator continuity, this
package supplies a small-radius scale on which the closed patch ball lies in
the PDE domain.
-/
def PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallGeometricSemijetPatchAt
    (C boundary : Set (Point n)) (_F : Operator n) (_g : Point n -> Real)
    (_B : DirichletBarrierPair C boundary _F _g) (x : Point n) (_J : Jet n) :
    Prop :=
  ∀ γ : Real, ∀ V : Set (Point n),
    0 < γ ->
      IsOpen V ->
        V ∈ nhdsWithin x C ->
          ∃ ρ : Real,
            0 < ρ ∧
              (∀ z : Point n, z ∈ boundary -> z ∉ C) ∧
                ∀ r : Real, 0 < r -> r <= ρ ->
                  ∀ z : Point n, z ∈ Metric.closedBall x r -> z ∈ C

/--
Geometric small-radius semijet data without branch lower-semicontinuity at
every failed lower-envelope subjet inequality.
-/
def PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallGeometricSemijetPatch
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallGeometricSemijetPatchAt
          C boundary F g B x J

end ViscositySolns
