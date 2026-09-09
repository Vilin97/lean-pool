/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.AxisEvaluation
public import LeanPool.NavierStokesAndEuler.NavierStokes.AxisResolvent
import Mathlib.Topology.MetricSpace.Contracting

/-!
# The nonlinear natural-axis fixed point

The local bounds below are computed from bounded linear and bilinear
operations. In particular, the nonlinear remainders' Lipschitz estimates
are conclusions, not assumptions.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.AxisContraction

open Set Metric
open scoped NNReal ContDiff

variable {E F G H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- A function with explicit bounds on a fixed norm ball. -/
structure Controlled (E F : Type*) [NormedAddCommGroup E] [NormedAddCommGroup F]
    (R : ℝ) where
  /-- Eval of `Controlled`, of type `E → F`. -/
  eval : E → F
  /-- Bound of `Controlled`, of type `ℝ`. -/
  bound : ℝ
  /-- Lip of `Controlled`, of type `ℝ`. -/
  lip : ℝ
  bound_nonneg : 0 ≤ bound
  lip_nonneg : 0 ≤ lip
  norm_le : ∀ x, ‖x‖ ≤ R → ‖eval x‖ ≤ bound
  sub_le : ∀ x y, ‖x‖ ≤ R → ‖y‖ ≤ R →
    ‖eval x - eval y‖ ≤ lip * ‖x - y‖

namespace Controlled

variable {R : ℝ}

/-- Const bound, bundling `eval`, `bound`, `lip`, `bound_nonneg` and the required compatibility
proofs. -/
noncomputable def constBound (a : F) (B : ℝ) (hB : 0 ≤ B) (ha : ‖a‖ ≤ B) :
    Controlled E F R where
  eval := fun _ => a
  bound := B
  lip := 0
  bound_nonneg := hB
  lip_nonneg := le_rfl
  norm_le := fun _ _ => ha
  sub_le := by intro x y hx hy; simp

/-- Const, given by `constBound a ‖a‖ (norm_nonneg a) le_rfl`. -/
noncomputable def const (a : F) : Controlled E F R :=
  constBound a ‖a‖ (norm_nonneg a) le_rfl

/-- Fst, bundling `eval`, `bound`, `lip`, `bound_nonneg` and the required compatibility proofs. -/
noncomputable def fst (hR : 0 ≤ R) : Controlled (E × F) E R where
  eval := Prod.fst
  bound := R
  lip := 1
  bound_nonneg := hR
  lip_nonneg := by norm_num
  norm_le := fun x hx => (norm_fst_le x).trans hx
  sub_le := by
    intro x y hx hy
    simpa only [one_mul, Prod.fst_sub] using norm_fst_le (x - y)

/-- Snd, bundling `eval`, `bound`, `lip`, `bound_nonneg` and the required compatibility proofs. -/
noncomputable def snd (hR : 0 ≤ R) : Controlled (E × F) F R where
  eval := Prod.snd
  bound := R
  lip := 1
  bound_nonneg := hR
  lip_nonneg := by norm_num
  norm_le := fun x hx => (norm_snd_le x).trans hx
  sub_le := by
    intro x y hx hy
    simpa only [one_mul, Prod.snd_sub] using norm_snd_le (x - y)

/-- Add, bundling `eval`, `bound`, `lip`, `bound_nonneg` and the required compatibility proofs. -/
noncomputable def add (f g : Controlled E F R) : Controlled E F R where
  eval := fun x => f.eval x + g.eval x
  bound := f.bound + g.bound
  lip := f.lip + g.lip
  bound_nonneg := add_nonneg f.bound_nonneg g.bound_nonneg
  lip_nonneg := add_nonneg f.lip_nonneg g.lip_nonneg
  norm_le := by
    intro x hx
    exact (norm_add_le _ _).trans (add_le_add (f.norm_le x hx) (g.norm_le x hx))
  sub_le := by
    intro x y hx hy
    have hid : f.eval x + g.eval x - (f.eval y + g.eval y) =
        (f.eval x - f.eval y) + (g.eval x - g.eval y) := by abel
    rw [hid, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (f.sub_le x y hx hy) (g.sub_le x y hx hy))

/-- Neg, bundling `eval`, `bound`, `lip`, `bound_nonneg` and the required compatibility proofs. -/
noncomputable def neg (f : Controlled E F R) : Controlled E F R where
  eval := fun x => -f.eval x
  bound := f.bound
  lip := f.lip
  bound_nonneg := f.bound_nonneg
  lip_nonneg := f.lip_nonneg
  norm_le := by intro x hx; simpa using f.norm_le x hx
  sub_le := by
    intro x y hx hy
    simpa only [neg_sub_neg, norm_sub_rev] using f.sub_le x y hx hy

/-- Sub, given by `add f (neg g)`. -/
noncomputable def sub (f g : Controlled E F R) : Controlled E F R := add f (neg g)

/-- Scaling by a scalar of absolute value at most one keeps the same upper
bounds, making the final bounds uniform in the parameter inverse. -/
noncomputable def unitSmul (c : ℝ) (hc : |c| ≤ 1) (f : Controlled E F R) :
    Controlled E F R where
  eval := fun x => c • f.eval x
  bound := f.bound
  lip := f.lip
  bound_nonneg := f.bound_nonneg
  lip_nonneg := f.lip_nonneg
  norm_le := by
    intro x hx
    calc
      ‖c • f.eval x‖ = |c| * ‖f.eval x‖ := norm_smul _ _
      _ ≤ 1 * f.bound := mul_le_mul hc (f.norm_le x hx) (norm_nonneg _) (by norm_num)
      _ = f.bound := one_mul _
  sub_le := by
    intro x y hx hy
    rw [← smul_sub, norm_smul, Real.norm_eq_abs]
    calc
      |c| * ‖f.eval x - f.eval y‖ ≤
          1 * (f.lip * ‖x - y‖) :=
        mul_le_mul hc (f.sub_le x y hx hy) (norm_nonneg _) (by norm_num)
      _ = _ := one_mul _

/-- Linear, bundling `eval`, `bound`, `lip`, `bound_nonneg` and the required compatibility
proofs. -/
noncomputable def linear (L : F →L[ℝ] G) (f : Controlled E F R) : Controlled E G R where
  eval := fun x => L (f.eval x)
  bound := ‖L‖ * f.bound
  lip := ‖L‖ * f.lip
  bound_nonneg := mul_nonneg (norm_nonneg _) f.bound_nonneg
  lip_nonneg := mul_nonneg (norm_nonneg _) f.lip_nonneg
  norm_le := by
    intro x hx
    exact (L.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (f.norm_le x hx) (norm_nonneg _))
  sub_le := by
    intro x y hx hy
    rw [← L.map_sub]
    exact (L.le_opNorm _).trans
      ((mul_le_mul_of_nonneg_left (f.sub_le x y hx hy) (norm_nonneg _)).trans_eq
        (mul_assoc _ _ _).symm)

/-- Bilinear, bundling `eval`, `bound`, `lip`, `bound_nonneg` and the required compatibility
proofs. -/
noncomputable def bilinear (B : F →L[ℝ] G →L[ℝ] H)
    (f : Controlled E F R) (g : Controlled E G R) : Controlled E H R where
  eval := fun x => B (f.eval x) (g.eval x)
  bound := ‖B‖ * f.bound * g.bound
  lip := ‖B‖ * (f.lip * g.bound + f.bound * g.lip)
  bound_nonneg := mul_nonneg (mul_nonneg (norm_nonneg B) f.bound_nonneg) g.bound_nonneg
  lip_nonneg := mul_nonneg (norm_nonneg B)
    (add_nonneg (mul_nonneg f.lip_nonneg g.bound_nonneg)
      (mul_nonneg f.bound_nonneg g.lip_nonneg))
  norm_le := by
    intro x hx
    calc
      ‖B (f.eval x) (g.eval x)‖ ≤ ‖B‖ * ‖f.eval x‖ * ‖g.eval x‖ :=
        B.le_opNorm₂ _ _
      _ ≤ ‖B‖ * f.bound * g.bound :=
        mul_le_mul
          (mul_le_mul_of_nonneg_left (f.norm_le x hx) (norm_nonneg B))
          (g.norm_le x hx) (norm_nonneg _)
          (mul_nonneg (norm_nonneg B) f.bound_nonneg)
  sub_le := by
    intro x y hx hy
    have hid : B (f.eval x) (g.eval x) - B (f.eval y) (g.eval y) =
        B (f.eval x - f.eval y) (g.eval x) +
          B (f.eval y) (g.eval x - g.eval y) := by
      simp only [map_sub, _root_.sub_apply]
      abel
    rw [hid]
    calc
      ‖B (f.eval x - f.eval y) (g.eval x) +
          B (f.eval y) (g.eval x - g.eval y)‖ ≤
          ‖B (f.eval x - f.eval y) (g.eval x)‖ +
            ‖B (f.eval y) (g.eval x - g.eval y)‖ := norm_add_le _ _
      _ ≤ ‖B‖ * ‖f.eval x - f.eval y‖ * ‖g.eval x‖ +
          ‖B‖ * ‖f.eval y‖ * ‖g.eval x - g.eval y‖ :=
        add_le_add (B.le_opNorm₂ _ _) (B.le_opNorm₂ _ _)
      _ ≤ ‖B‖ * (f.lip * ‖x - y‖) * g.bound +
          ‖B‖ * f.bound * (g.lip * ‖x - y‖) :=
        add_le_add
          (mul_le_mul
            (mul_le_mul_of_nonneg_left (f.sub_le x y hx hy) (norm_nonneg B))
            (g.norm_le x hx) (norm_nonneg _)
            (mul_nonneg (norm_nonneg B) (mul_nonneg f.lip_nonneg (norm_nonneg _))))
          (mul_le_mul
            (mul_le_mul_of_nonneg_left (f.norm_le y hy) (norm_nonneg B))
            (g.sub_le x y hx hy) (norm_nonneg _)
            (mul_nonneg (norm_nonneg B) f.bound_nonneg))
      _ = (‖B‖ * (f.lip * g.bound + f.bound * g.lip)) * ‖x - y‖ := by ring

/-- Pair, bundling `eval`, `bound`, `lip`, `bound_nonneg` and the required compatibility proofs. -/
noncomputable def pair (f : Controlled E F R) (g : Controlled E G R) : Controlled E (F × G) R where
  eval := fun x => (f.eval x, g.eval x)
  bound := f.bound + g.bound
  lip := f.lip + g.lip
  bound_nonneg := add_nonneg f.bound_nonneg g.bound_nonneg
  lip_nonneg := add_nonneg f.lip_nonneg g.lip_nonneg
  norm_le := by
    intro x hx
    apply (norm_prod_le_iff).mpr
    exact ⟨(f.norm_le x hx).trans (le_add_of_nonneg_right g.bound_nonneg),
      (g.norm_le x hx).trans (le_add_of_nonneg_left f.bound_nonneg)⟩
  sub_le := by
    intro x y hx hy
    apply (norm_prod_le_iff).mpr
    constructor
    · exact (f.sub_le x y hx hy).trans
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right g.lip_nonneg) (norm_nonneg _))
    · exact (g.sub_le x y hx hy).trans
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left f.lip_nonneg) (norm_nonneg _))

end Controlled

/-- The complete-subset fixed point step used after constructing, rather
than assuming, the remainder's local estimates. -/
theorem exists_fixedPoint_of_controlled [CompleteSpace E]
    (x₀ : E) (f : Controlled E E (‖x₀‖ + 1))
    (s : ℝ) (hs : 0 ≤ s) (hbound : s * f.bound ≤ 1)
    (hlip : s * f.lip ≤ 1 / 2) :
    ∃ x : E, ‖x - x₀‖ ≤ 1 ∧
      x₀ + s • f.eval x = x ∧
      ‖x - x₀‖ ≤ s * f.bound ∧
      ∀ y : E, ‖y - x₀‖ ≤ 1 → x₀ + s • f.eval y = y → y = x := by
  let F : E → E := fun x => x₀ + s • f.eval x
  have hnorm {x : E} (hx : x ∈ closedBall x₀ 1) : ‖x‖ ≤ ‖x₀‖ + 1 := by
    have hxn : ‖x - x₀‖ ≤ 1 := by simpa only [mem_closedBall, dist_eq_norm] using hx
    calc
      ‖x‖ = ‖(x - x₀) + x₀‖ := by rw [sub_add_cancel]
      _ ≤ ‖x - x₀‖ + ‖x₀‖ := norm_add_le _ _
      _ ≤ 1 + ‖x₀‖ := add_le_add_left hxn _
      _ = ‖x₀‖ + 1 := add_comm _ _
  have herr {x : E} (hx : x ∈ closedBall x₀ 1) :
      ‖F x - x₀‖ ≤ s * f.bound := by
    have heq : F x - x₀ = s • f.eval x := by dsimp [F]; abel
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs]
    exact mul_le_mul_of_nonneg_left (f.norm_le x (hnorm hx)) hs
  have hmaps : MapsTo F (closedBall x₀ 1) (closedBall x₀ 1) := by
    intro x hx
    simpa only [mem_closedBall, dist_eq_norm] using (herr hx).trans hbound
  have hdiff {x y : E} (hx : x ∈ closedBall x₀ 1) (hy : y ∈ closedBall x₀ 1) :
      ‖F x - F y‖ ≤ (1 / 2 : ℝ) * ‖x - y‖ := by
    have heq : F x - F y = s • (f.eval x - f.eval y) := by
      dsimp [F]
      rw [smul_sub]
      abel
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs]
    calc
      s * ‖f.eval x - f.eval y‖ ≤ s * (f.lip * ‖x - y‖) :=
        mul_le_mul_of_nonneg_left (f.sub_le x y (hnorm hx) (hnorm hy)) hs
      _ = (s * f.lip) * ‖x - y‖ := (mul_assoc _ _ _).symm
      _ ≤ (1 / 2) * ‖x - y‖ := mul_le_mul_of_nonneg_right hlip (norm_nonneg _)
  have hc : ContractingWith (1 / 2 : ℝ≥0)
      (hmaps.restrict F (closedBall x₀ 1) (closedBall x₀ 1)) := by
    refine ⟨one_half_lt_one, LipschitzWith.of_dist_le_mul ?_⟩
    intro x y
    change dist (F x.1) (F y.1) ≤ (↑(1 / 2 : ℝ≥0) : ℝ) * dist x.1 y.1
    simpa only [dist_eq_norm, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] using
      hdiff x.property y.property
  obtain ⟨x, hx, hfix, _, _⟩ :=
    ContractingWith.exists_fixedPoint' isClosed_closedBall.isComplete hmaps hc
      (x := x₀) (by simp) (edist_ne_top _ _)
  refine ⟨x, by simpa only [mem_closedBall, dist_eq_norm] using hx,
    hfix, ?_, ?_⟩
  · simpa only [hfix.eq] using herr hx
  · intro y hy hyfix
    have hym : y ∈ closedBall x₀ 1 := by
      simpa only [mem_closedBall, dist_eq_norm] using hy
    have h := hdiff hym hx
    change ‖F y - F x‖ ≤ (1 / 2 : ℝ) * ‖y - x‖ at h
    rw [show F y = y from hyfix, hfix.eq] at h
    have : ‖y - x‖ = 0 := by nlinarith [norm_nonneg (y - x)]
    exact sub_eq_zero.mp (norm_eq_zero.mp this)

/-- Actual bounded coefficient operators, later instantiated by AxisOperators.
The derivative operators occur only after their regular radial inverses. -/
structure NaturalOperators (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] where
  /-- Product of `NaturalOperators`, of type `V →L[ℝ] V →L[ℝ] V`. -/
  product : V →L[ℝ] V →L[ℝ] V
  /-- Average of `NaturalOperators`, of type `V →L[ℝ] V`. -/
  average : V →L[ℝ] V
  /-- Primitive of `NaturalOperators`, of type `V →L[ℝ] V`. -/
  primitive : V →L[ℝ] V
  /-- Parameter primitive of `NaturalOperators`, of type `V →L[ℝ] V`. -/
  parameterPrimitive : V →L[ℝ] V
  /-- Mul Y of `NaturalOperators`, of type `V →L[ℝ] V`. -/
  mulY : V →L[ℝ] V
  /-- J1 of `NaturalOperators`, of type `V →L[ℝ] V`. -/
  j1 : V →L[ℝ] V
  /-- J2 of `NaturalOperators`, of type `V →L[ℝ] V`. -/
  j2 : V →L[ℝ] V
  /-- Param1 of `NaturalOperators`, of type `V →L[ℝ] V →L[ℝ] V`. -/
  param1 : V →L[ℝ] V →L[ℝ] V
  /-- Param2 of `NaturalOperators`, of type `V →L[ℝ] V →L[ℝ] V`. -/
  param2 : V →L[ℝ] V →L[ℝ] V
  /-- Dot1 of `NaturalOperators`, of type `V →L[ℝ] V →L[ℝ] V`. -/
  dot1 : V →L[ℝ] V →L[ℝ] V
  /-- Dot2 of `NaturalOperators`, of type `V →L[ℝ] V →L[ℝ] V`. -/
  dot2 : V →L[ℝ] V →L[ℝ] V
  /-- Mixed1 of `NaturalOperators`, of type `V →L[ℝ] V →L[ℝ] V`. -/
  mixed1 : V →L[ℝ] V →L[ℝ] V
  /-- Mixed2 of `NaturalOperators`, of type `V →L[ℝ] V →L[ℝ] V`. -/
  mixed2 : V →L[ℝ] V →L[ℝ] V

/-- Fixed analytic coefficient data. In the manuscript all entries have
radial degree zero. The normalized gradient is ξ₀/Λ, independent of Λ. -/
structure AxisData (V : Type*) where
  /-- A of `AxisData`, of type `ℝ`. -/
  A : ℝ
  /-- Domain data of `AxisData`, of type `ℝ`. -/
  D : ℝ
  /-- Step-size parameter of `AxisData`, of type `ℝ`. -/
  h : ℝ
  /-- One of `AxisData`, of type `V`. -/
  one : V
  /-- Eta of `AxisData`, of type `V`. -/
  eta : V
  /-- D of `AxisData`, of type `V`. -/
  d : V
  /-- Inverse L of `AxisData`, of type `V`. -/
  inverseL : V
  /-- U star of `AxisData`, of type `V`. -/
  uStar : V
  /-- U star eta of `AxisData`, of type `V`. -/
  uStarEta : V
  /-- W star of `AxisData`, of type `V`. -/
  wStar : V
  /-- H star of `AxisData`, of type `V`. -/
  hStar : V
  /-- Normalized gradient of `AxisData`, of type `V`. -/
  normalizedGradient : V
  /-- Z star of `AxisData`, of type `V`. -/
  zStar : V

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Angular linear coefficient, given by `d.wStar + d.h • d.one - (2 * d.h) • O.product d.eta
d.uStar`. -/
def angularLinearCoefficient (O : NaturalOperators V) (d : AxisData V) : V :=
  d.wStar + d.h • d.one - (2 * d.h) • O.product d.eta d.uStar

/-- Angular quadratic coefficient, given by `O.product d.d d.normalizedGradient`. -/
def angularQuadraticCoefficient (O : NaturalOperators V) (d : AxisData V) : V :=
  O.product d.d d.normalizedGradient

/-- Average coefficient, given by `(2 * d.D) • d.eta`. -/
def averageCoefficient (d : AxisData V) : V := (2 * d.D) • d.eta

/-- Angular slow coefficient, given by `(2 * d.h) • d.eta`. -/
def angularSlowCoefficient (d : AxisData V) : V := (2 * d.h) • d.eta

/-- Axial linear coefficient, given by `d.A • d.one - (4 * d.A) • O.product d.eta d.uStar +
O.product d.d d.uStarEta`. -/
def axialLinearCoefficient (O : NaturalOperators V) (d : AxisData V) : V :=
  d.A • d.one - (4 * d.A) • O.product d.eta d.uStar + O.product d.d d.uStarEta

/-- Axial quadratic coefficient, given by `(2 * d.A) • d.eta`. -/
def axialQuadraticCoefficient (d : AxisData V) : V := (2 * d.A) • d.eta

/-- The exact expanded, radially integrated nonlinear remainders.
The first component also includes the bounded angular resolvent.
Here t is Λ⁻¹ and a is φ*/C. -/
def naturalRemainder (O : NaturalOperators V) (d : AxisData V)
    (S : V →L[ℝ] V) (t : ℝ) (a : V) (x : V × V) : V × V :=
  let φ := x.1
  let u := x.2
  let bu := O.average u
  let lin1 := O.j2 (O.product (angularLinearCoefficient O d) φ) +
    O.dot2 d.wStar φ + O.param2 φ d.hStar
  let quad1 := O.j2 (O.product (O.product (angularQuadraticCoefficient O d) u) φ)
  let slow1 := O.j2 (O.product
      (O.product (averageCoefficient d) bu + O.product (angularSlowCoefficient d) u) φ) +
    O.param2 bu (O.product d.d φ) +
    O.dot2 (O.product (averageCoefficient d) bu) φ +
    O.product d.d (O.mixed2 bu φ) -
    O.param2 φ (O.product d.d u)
  let lin2 := O.j1 (O.product (axialLinearCoefficient O d) u) +
    O.dot1 d.wStar u + O.param1 u d.hStar
  let slow2 := O.j1 (O.product (axialQuadraticCoefficient d) (O.product u u)) +
    O.dot1 (O.product (averageCoefficient d) bu) u +
    O.product d.d (O.mixed1 bu u) -
    O.param1 u (O.product d.d u)
  let source := O.product (O.product a a) (O.product φ φ)
  let pressure := O.j1
    (-O.product ((4 * d.A) • d.eta) (O.primitive source) +
      O.product d.d (O.parameterPrimitive source) -
      O.product ((2 : ℝ) • d.eta) (O.mulY source))
  (S (O.product d.inverseL (lin1 + quad1 - t • slow1)),
    O.product d.inverseL (lin2 - t • slow2 + pressure))

/-- The reference pair about which the nonlinear iteration is performed. -/
def referencePair (O : NaturalOperators V) (d : AxisData V) (S : V →L[ℝ] V) : V × V :=
  (S d.one, -(1 / 2 : ℝ) • O.j1 (O.product d.inverseL d.zStar))

/-- Scalar check of the angular grouping used before applying the actual
linear radial inverse. No derivative terms are omitted in the expansion. -/
theorem angular_remainder_expansion
    (t h D η d U W H κ φ u bu buη φdot φη : ℝ) :
    ((W + h - 2 * h * η * U) * φ + W * φdot + H * φη) +
        d * κ * u * φ -
        t * (((2 * D * η) * bu + (2 * h * η) * u) * φ +
          d * buη * φ + (2 * D * η) * bu * φdot +
          d * buη * φdot - d * u * φη) =
      ((W - t * ((2 * D * η) * bu + d * buη)) +
          h * (1 - 2 * η * (U + t * u)) + d * u * κ) * φ +
        (W - t * ((2 * D * η) * bu + d * buη)) * φdot +
        (H + t * d * u) * φη := by ring

/-- Scalar check of the axial grouping, including the pressure terms. -/
theorem axial_remainder_expansion
    (t A D η d U Uη W H u bu buη udot uη P Pη Pdot : ℝ) :
    ((A - 4 * A * η * U + d * Uη) * u + W * udot + H * uη) -
        t * ((2 * A * η) * (u * u) + (2 * D * η) * bu * udot +
          d * buη * udot - d * u * uη) +
        (-4 * A * η * P + d * Pη - 2 * η * Pdot) =
      A * (1 - 4 * η * U) * u - 2 * A * η * t * (u * u) +
        (W - t * ((2 * D * η) * bu + d * buη)) * udot +
        H * uη + d * Uη * u + t * d * u * uη -
        4 * A * η * P + d * Pη - 2 * η * Pdot := by ring

/-- Explicit propagation of local bounds through every term in the actual
integrated remainders. Its numerical fields do not depend on t or a,
only on the uniform upper bound M for the norm of a. -/
def controlledRemainder (O : NaturalOperators V) (d : AxisData V)
    (S : V →L[ℝ] V) (R M : ℝ) (hR : 0 ≤ R) (hM : 0 ≤ M)
    (t : ℝ) (ht : |t| ≤ 1) (a : V) (ha : ‖a‖ ≤ M) :
    Controlled (V × V) (V × V) R :=
  let c : V → Controlled (V × V) V R := Controlled.const
  let mul := Controlled.bilinear O.product
  let add := Controlled.add
  let sub := Controlled.sub
  let φ : Controlled (V × V) V R := Controlled.fst hR
  let u : Controlled (V × V) V R := Controlled.snd hR
  let bu := Controlled.linear O.average u
  let j1 := Controlled.linear O.j1
  let j2 := Controlled.linear O.j2
  let p1 := Controlled.bilinear O.param1
  let p2 := Controlled.bilinear O.param2
  let q1 := Controlled.bilinear O.dot1
  let q2 := Controlled.bilinear O.dot2
  let m1 := Controlled.bilinear O.mixed1
  let m2 := Controlled.bilinear O.mixed2
  let lin1 := add
    (add (j2 (mul (c (angularLinearCoefficient O d)) φ)) (q2 (c d.wStar) φ))
    (p2 φ (c d.hStar))
  let quad1 := j2 (mul (mul (c (angularQuadraticCoefficient O d)) u) φ)
  let slow1 := sub
    (add
      (add
        (add
          (j2 (mul (add (mul (c (averageCoefficient d)) bu)
            (mul (c (angularSlowCoefficient d)) u)) φ))
          (p2 bu (mul (c d.d) φ)))
        (q2 (mul (c (averageCoefficient d)) bu) φ))
      (mul (c d.d) (m2 bu φ)))
    (p2 φ (mul (c d.d) u))
  let lin2 := add
    (add (j1 (mul (c (axialLinearCoefficient O d)) u)) (q1 (c d.wStar) u))
    (p1 u (c d.hStar))
  let slow2 := sub
    (add
      (add (j1 (mul (c (axialQuadraticCoefficient d)) (mul u u)))
        (q1 (mul (c (averageCoefficient d)) bu) u))
      (mul (c d.d) (m1 bu u)))
    (p1 u (mul (c d.d) u))
  let ac : Controlled (V × V) V R := Controlled.constBound a M hM ha
  let source := mul (mul ac ac) (mul φ φ)
  let pressure := j1 (sub
    (add
      (Controlled.neg (mul (c ((4 * d.A) • d.eta)) (Controlled.linear O.primitive source)))
      (mul (c d.d) (Controlled.linear O.parameterPrimitive source)))
    (mul (c ((2 : ℝ) • d.eta)) (Controlled.linear O.mulY source)))
  Controlled.pair
    (Controlled.linear S (mul (c d.inverseL)
      (sub (add lin1 quad1) (Controlled.unitSmul t ht slow1))))
    (mul (c d.inverseL) (add (sub lin2 (Controlled.unitSmul t ht slow2)) pressure))

@[simp] theorem controlledRemainder_eval (O : NaturalOperators V) (d : AxisData V)
    (S : V →L[ℝ] V) (R M : ℝ) (hR : 0 ≤ R) (hM : 0 ≤ M)
    (t : ℝ) (ht : |t| ≤ 1) (a : V) (ha : ‖a‖ ≤ M) (x : V × V) :
    (controlledRemainder O d S R M hR hM t ht a ha).eval x =
      naturalRemainder O d S t a x := by
  simp only [controlledRemainder, naturalRemainder, Controlled.const, Controlled.constBound,
    Controlled.fst, Controlled.snd, Controlled.linear, Controlled.bilinear,
    Controlled.add, Controlled.sub, Controlled.neg, Controlled.unitSmul, Controlled.pair,
    sub_eq_add_neg]

/-- An explicit expression in the fixed operator norms, coefficient norms,
ball radius, and upper bound for the pressure amplitude. -/
def remainderBound (O : NaturalOperators V) (d : AxisData V)
    (S : V →L[ℝ] V) (R M : ℝ) (hR : 0 ≤ R) (hM : 0 ≤ M) : ℝ :=
  (controlledRemainder O d S R M hR hM 0 (by simp) 0 (by simpa using hM)).bound

/-- Remainder lip, given by `(controlledRemainder O d S R M hR hM 0 (by simp) 0 (by simpa using
hM)).lip`. -/
def remainderLip (O : NaturalOperators V) (d : AxisData V)
    (S : V →L[ℝ] V) (R M : ℝ) (hR : 0 ≤ R) (hM : 0 ≤ M) : ℝ :=
  (controlledRemainder O d S R M hR hM 0 (by simp) 0 (by simpa using hM)).lip

theorem controlledRemainder_bound_eq (O : NaturalOperators V) (d : AxisData V)
    (S : V →L[ℝ] V) (R M : ℝ) (hR : 0 ≤ R) (hM : 0 ≤ M)
    (t : ℝ) (ht : |t| ≤ 1) (a : V) (ha : ‖a‖ ≤ M) :
    (controlledRemainder O d S R M hR hM t ht a ha).bound =
      remainderBound O d S R M hR hM := by rfl

theorem controlledRemainder_lip_eq (O : NaturalOperators V) (d : AxisData V)
    (S : V →L[ℝ] V) (R M : ℝ) (hR : 0 ≤ R) (hM : 0 ≤ M)
    (t : ℝ) (ht : |t| ≤ 1) (a : V) (ha : ‖a‖ ≤ M) :
    (controlledRemainder O d S R M hR hM t ht a ha).lip =
      remainderLip O d S R M hR hM := by rfl

theorem remainderBound_nonneg (O : NaturalOperators V) (d : AxisData V)
    (S : V →L[ℝ] V) (R M : ℝ) (hR : 0 ≤ R) (hM : 0 ≤ M) :
    0 ≤ remainderBound O d S R M hR hM :=
  (controlledRemainder O d S R M hR hM 0 (by simp) 0 (by simpa using hM)).bound_nonneg

theorem remainderLip_nonneg (O : NaturalOperators V) (d : AxisData V)
    (S : V →L[ℝ] V) (R M : ℝ) (hR : 0 ≤ R) (hM : 0 ≤ M) :
    0 ≤ remainderLip O d S R M hR hM :=
  (controlledRemainder O d S R M hR hM 0 (by simp) 0 (by simpa using hM)).lip_nonneg

/-- The actual remainder is bounded uniformly in both the small parameter
and every normalized angular amplitude with norm at most M. -/
theorem norm_naturalRemainder_le (O : NaturalOperators V) (d : AxisData V)
    (S : V →L[ℝ] V) (R M : ℝ) (hR : 0 ≤ R) (hM : 0 ≤ M)
    (t : ℝ) (ht : |t| ≤ 1) (a : V) (ha : ‖a‖ ≤ M)
    (x : V × V) (hx : ‖x‖ ≤ R) :
    ‖naturalRemainder O d S t a x‖ ≤ remainderBound O d S R M hR hM := by
  have h := (controlledRemainder O d S R M hR hM t ht a ha).norm_le x hx
  simpa only [controlledRemainder_eval, controlledRemainder_bound_eq] using h

/-- The local Lipschitz estimate is derived term by term from the actual
polynomial operators, including the mixed and pressure terms. -/
theorem naturalRemainder_sub_le (O : NaturalOperators V) (d : AxisData V)
    (S : V →L[ℝ] V) (R M : ℝ) (hR : 0 ≤ R) (hM : 0 ≤ M)
    (t : ℝ) (ht : |t| ≤ 1) (a : V) (ha : ‖a‖ ≤ M)
    (x y : V × V) (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) :
    ‖naturalRemainder O d S t a x - naturalRemainder O d S t a y‖ ≤
      remainderLip O d S R M hR hM * ‖x - y‖ := by
  have h := (controlledRemainder O d S R M hR hM t ht a ha).sub_le x y hx hy
  simpa only [controlledRemainder_eval, controlledRemainder_lip_eq] using h

/-- A finite threshold depending only on fixed operator/coefficient data,
the reference pair, and the uniform norm bound M. In particular it does
not depend on the normalized amplitude a. -/
def contractionThreshold (O : NaturalOperators V) (d : AxisData V)
    (S : V →L[ℝ] V) (x₀ : V × V) (M : ℝ) (hM : 0 ≤ M) : ℝ :=
  1 + remainderBound O d S (‖x₀‖ + 1) M (by positivity) hM +
    remainderLip O d S (‖x₀‖ + 1) M (by positivity) hM

theorem contractionThreshold_pos (O : NaturalOperators V) (d : AxisData V)
    (S : V →L[ℝ] V) (x₀ : V × V) (M : ℝ) (hM : 0 ≤ M) :
    0 < contractionThreshold O d S x₀ M hM := by
  have hb := remainderBound_nonneg O d S (‖x₀‖ + 1) M (by positivity) hM
  have hl := remainderLip_nonneg O d S (‖x₀‖ + 1) M (by positivity) hM
  unfold contractionThreshold
  linarith

/-- Existence, uniqueness in the reference ball, and an explicit
O(Λ⁻¹) norm error for the actual polynomial remainders.
The two remainder estimates used here were proved above term by term. -/
theorem exists_unique_natural_fixedPoint [CompleteSpace V]
    (O : NaturalOperators V) (d : AxisData V) (S : V →L[ℝ] V)
    (x₀ : V × V) (M : ℝ) (hM : 0 ≤ M)
    (Λ : ℝ) (hΛ : contractionThreshold O d S x₀ M hM ≤ Λ)
    (a : V) (ha : ‖a‖ ≤ M) :
    ∃ x : V × V, ‖x - x₀‖ ≤ 1 ∧
      x₀ + (1 / (2 * Λ)) • naturalRemainder O d S (1 / Λ) a x = x ∧
      ‖x - x₀‖ ≤ remainderBound O d S (‖x₀‖ + 1) M (by positivity) hM / (2 * Λ) ∧
      ∀ y : V × V, ‖y - x₀‖ ≤ 1 →
        x₀ + (1 / (2 * Λ)) • naturalRemainder O d S (1 / Λ) a y = y → y = x := by
  let R := ‖x₀‖ + 1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  let B := remainderBound O d S R M hR hM
  let L := remainderLip O d S R M hR hM
  have hB : 0 ≤ B := remainderBound_nonneg O d S R M hR hM
  have hL : 0 ≤ L := remainderLip_nonneg O d S R M hR hM
  have htotal : 1 + B + L ≤ Λ := hΛ
  have hΛ1 : 1 ≤ Λ := by linarith
  have hBΛ : B ≤ Λ := by linarith
  have hLΛ : L ≤ Λ := by linarith
  have hΛpos : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ1
  have hden : 0 < 2 * Λ := by positivity
  have ht : |1 / Λ| ≤ 1 := by
    rw [abs_of_pos (one_div_pos.mpr hΛpos)]
    exact (div_le_one hΛpos).mpr hΛ1
  have hs : 0 ≤ 1 / (2 * Λ) := by positivity
  let f := controlledRemainder O d S R M hR hM (1 / Λ) ht a ha
  have hb : (1 / (2 * Λ)) * f.bound ≤ 1 := by
    change (1 / (2 * Λ)) * B ≤ 1
    rw [show (1 / (2 * Λ)) * B = B / (2 * Λ) by ring]
    apply (div_le_iff₀ hden).mpr
    linarith
  have hl : (1 / (2 * Λ)) * f.lip ≤ 1 / 2 := by
    change (1 / (2 * Λ)) * L ≤ 1 / 2
    rw [show (1 / (2 * Λ)) * L = L / (2 * Λ) by ring]
    apply (div_le_iff₀ hden).mpr
    linarith
  obtain ⟨x, hx, hfixed, herr, huniq⟩ :=
    exists_fixedPoint_of_controlled x₀ f (1 / (2 * Λ)) hs hb hl
  refine ⟨x, hx, ?_, ?_, ?_⟩
  · simpa only [f, controlledRemainder_eval] using hfixed
  · change ‖x - x₀‖ ≤ B / (2 * Λ)
    change ‖x - x₀‖ ≤ (1 / (2 * Λ)) * B at herr
    simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using herr
  · intro y hy hyfixed
    apply huniq y hy
    simpa only [f, controlledRemainder_eval] using hyfixed

/-- The same threshold works for every admissible a = φ*/C; the
normalization hypothesis is a norm bound on the actual coefficient input,
not a hypothesis about the nonlinear map's Lipschitz constant. -/
theorem uniform_natural_fixedPoint [CompleteSpace V]
    (O : NaturalOperators V) (d : AxisData V) (S : V →L[ℝ] V)
    (M : ℝ) (hM : 0 ≤ M) :
    ∃ Λ₀ : ℝ, 0 < Λ₀ ∧ ∀ Λ : ℝ, Λ₀ ≤ Λ → ∀ a : V, ‖a‖ ≤ M →
      ∃ x : V × V,
        ‖x - referencePair O d S‖ ≤ 1 ∧
        referencePair O d S +
          (1 / (2 * Λ)) • naturalRemainder O d S (1 / Λ) a x = x ∧
        ‖x - referencePair O d S‖ ≤
          remainderBound O d S (‖referencePair O d S‖ + 1) M (by positivity) hM / (2 * Λ) ∧
        ∀ y : V × V, ‖y - referencePair O d S‖ ≤ 1 →
          referencePair O d S +
            (1 / (2 * Λ)) • naturalRemainder O d S (1 / Λ) a y = y → y = x := by
  refine ⟨contractionThreshold O d S (referencePair O d S) M hM,
    contractionThreshold_pos O d S (referencePair O d S) M hM, ?_⟩
  intro Λ hΛ a ha
  exact exists_unique_natural_fixedPoint O d S (referencePair O d S) M hM Λ hΛ a ha

theorem naturalRemainder_fst_resolvent (O : NaturalOperators V) (d : AxisData V)
    (S : V →L[ℝ] V) (t : ℝ) (a : V) (x : V × V) :
    (naturalRemainder O d S t a x).1 =
      S ((naturalRemainder O d (ContinuousLinearMap.id ℝ V) t a x).1) := rfl

theorem naturalRemainder_snd_resolvent (O : NaturalOperators V) (d : AxisData V)
    (S : V →L[ℝ] V) (t : ℝ) (a : V) (x : V × V) :
    (naturalRemainder O d S t a x).2 =
      (naturalRemainder O d (ContinuousLinearMap.id ℝ V) t a x).2 := rfl

/-- Undoing the actual angular resolvent turns the fixed point into the
two integrated natural equations. The only extra hypothesis is the
resolvent identity, independently proved in AxisResolvent. -/
theorem fixedPoint_integrated_equations (O : NaturalOperators V) (d : AxisData V)
    (S Q : V →L[ℝ] V) (hS : ∀ y : V, S y + Q (S y) = y)
    (t s : ℝ) (a : V) (x : V × V)
    (hfixed : referencePair O d S + s • naturalRemainder O d S t a x = x) :
    x.1 + Q x.1 =
        d.one + s • (naturalRemainder O d (ContinuousLinearMap.id ℝ V) t a x).1 ∧
      x.2 = -(1 / 2 : ℝ) • O.j1 (O.product d.inverseL d.zStar) +
        s • (naturalRemainder O d (ContinuousLinearMap.id ℝ V) t a x).2 := by
  have hφ := congrArg Prod.fst hfixed
  have hu := congrArg Prod.snd hfixed
  change S d.one + s • (naturalRemainder O d S t a x).1 = x.1 at hφ
  change -(1 / 2 : ℝ) • O.j1 (O.product d.inverseL d.zStar) +
    s • (naturalRemainder O d S t a x).2 = x.2 at hu
  rw [naturalRemainder_fst_resolvent] at hφ
  rw [naturalRemainder_snd_resolvent] at hu
  constructor
  · have hlin : S (d.one +
        s • (naturalRemainder O d (ContinuousLinearMap.id ℝ V) t a x).1) = x.1 := by
      simpa only [map_add, map_smul] using hφ
    have h := hS (d.one +
      s • (naturalRemainder O d (ContinuousLinearMap.id ℝ V) t a x).1)
    rwa [hlin] at h
  · exact hu.symm

/-- With the left resolvent identity, the two integrated equations also
imply the nonlinear fixed-point equation. -/
theorem integrated_equations_fixedPoint (O : NaturalOperators V) (d : AxisData V)
    (S Q : V →L[ℝ] V) (hS : ∀ y : V, S (y + Q y) = y)
    (t s : ℝ) (a : V) (x : V × V)
    (hφ : x.1 + Q x.1 =
      d.one + s • (naturalRemainder O d (ContinuousLinearMap.id ℝ V) t a x).1)
    (hu : x.2 = -(1 / 2 : ℝ) • O.j1 (O.product d.inverseL d.zStar) +
      s • (naturalRemainder O d (ContinuousLinearMap.id ℝ V) t a x).2) :
    referencePair O d S + s • naturalRemainder O d S t a x = x := by
  apply Prod.ext
  · change S d.one + s • (naturalRemainder O d S t a x).1 = x.1
    rw [naturalRemainder_fst_resolvent]
    calc
      S d.one + s • S ((naturalRemainder O d (ContinuousLinearMap.id ℝ V) t a x).1) =
          S (d.one + s • (naturalRemainder O d (ContinuousLinearMap.id ℝ V) t a x).1) := by
        rw [map_add, map_smul]
      _ = S (x.1 + Q x.1) := congrArg S hφ.symm
      _ = x.1 := hS x.1
  · change -(1 / 2 : ℝ) • O.j1 (O.product d.inverseL d.zStar) +
      s • (naturalRemainder O d S t a x).2 = x.2
    rw [naturalRemainder_snd_resolvent]
    exact hu.symm

/-- A single coefficient-space norm error controls every angular parameter
jet uniformly on the full real parameter interval. -/
theorem axis_angular_jet_error (I : AxisCoefficientSpace.Window) (ε : ℝ)
    (x x₀ : AxisCoefficientSpace.AxisSpace I ε × AxisCoefficientSpace.AxisSpace I ε)
    (B : ℝ) (hB : ‖x - x₀‖ ≤ B) (n m : ℕ) (η : ℝ) :
    |AxisCoefficientSpace.jet I (AxisWeightEstimates.weight ε) x.1.1 n m η -
      AxisCoefficientSpace.jet I (AxisWeightEstimates.weight ε) x₀.1.1 n m η| ≤
        |AxisWeightEstimates.weight ε n m| * B := by
  have hcomponent : ‖x.1 - x₀.1‖ ≤ B := (norm_fst_le (x - x₀)).trans hB
  exact (AxisCoefficientSpace.abs_jet_sub_le I (AxisWeightEstimates.weight ε)
    x.1 x₀.1 n m η).trans
      (mul_le_mul_of_nonneg_left hcomponent (abs_nonneg _))

/-- The same uniform control for every axial parameter jet. -/
theorem axis_axial_jet_error (I : AxisCoefficientSpace.Window) (ε : ℝ)
    (x x₀ : AxisCoefficientSpace.AxisSpace I ε × AxisCoefficientSpace.AxisSpace I ε)
    (B : ℝ) (hB : ‖x - x₀‖ ≤ B) (n m : ℕ) (η : ℝ) :
    |AxisCoefficientSpace.jet I (AxisWeightEstimates.weight ε) x.2.1 n m η -
      AxisCoefficientSpace.jet I (AxisWeightEstimates.weight ε) x₀.2.1 n m η| ≤
        |AxisWeightEstimates.weight ε n m| * B := by
  have hcomponent : ‖x.2 - x₀.2‖ ≤ B := (norm_snd_le (x - x₀)).trans hB
  exact (AxisCoefficientSpace.abs_jet_sub_le I (AxisWeightEstimates.weight ε)
    x.2 x₀.2 n m η).trans
      (mul_le_mul_of_nonneg_left hcomponent (abs_nonneg _))

/-- The coefficient fixed-point error controls actual mixed derivatives
of the evaluated functions, uniformly on every smaller radial interval. -/
theorem evaluated_mixed_error (I : AxisCoefficientSpace.Window)
    {ε R : ℝ} (hε : 0 < ε) (hR : 1 ≤ R) (hR20 : R < 20)
    (A B : AxisCoefficientSpace.AxisSpace I ε) (K : ℝ) (hK : ‖A - B‖ ≤ K)
    (k m : ℕ) {Y η : ℝ} (hY : |Y| ≤ R) (hη : η ∈ Ioo I.left I.right) :
    ‖iteratedDeriv m
        (fun z => iteratedDeriv k (fun y => AxisEvaluation.profile I ε A (y, z)) Y) η -
      iteratedDeriv m
        (fun z => iteratedDeriv k (fun y => AxisEvaluation.profile I ε B (y, z)) Y) η‖ ≤
        AxisEvaluation.jetBound ε R k m * K := by
  have hY20 : Y ∈ Ioo (-20 : ℝ) 20 := abs_lt.mp (hY.trans_lt hR20)
  rw [AxisEvaluation.mixed_derivative_profile I hε A k m hY20 hη,
    AxisEvaluation.mixed_derivative_profile I hε B k m hY20 hη]
  change ‖AxisEvaluation.mixedSeries I ε A k m (Y, η) -
    AxisEvaluation.mixedSeries I ε B k m (Y, η)‖ ≤ _
  exact (AxisEvaluation.mixedSeries_sub_bound I hε hR hR20 A B k m hY).trans
    (mul_le_mul_of_nonneg_left hK (AxisEvaluation.jetBound_nonneg hε hR k m))

/-- Concrete instantiation by the genuine coefficient product, radial
averages/inverses, and derivative composites constructed in AxisOperators. -/
def coefficientOperators (I : AxisCoefficientSpace.Window) {ε : ℝ} (hε : 0 < ε) :
    NaturalOperators (AxisCoefficientSpace.AxisSpace I ε) where
  product := AxisOperators.product I hε
  average := AxisOperators.average I hε
  primitive := AxisOperators.primitive I hε
  parameterPrimitive := AxisOperators.parameterPrimitive I hε
  mulY := AxisOperators.mulY I hε
  j1 := AxisOperators.regularInverse I hε 1 (by norm_num)
  j2 := AxisOperators.regularInverse I hε 2 (by norm_num)
  param1 := AxisOperators.inverseParamProduct I hε 1 (by norm_num)
  param2 := AxisOperators.inverseParamProduct I hε 2 (by norm_num)
  dot1 := AxisOperators.inverseDotProduct I hε 1 (by norm_num)
  dot2 := AxisOperators.inverseDotProduct I hε 2 (by norm_num)
  mixed1 := AxisOperators.inverseMixed I hε 1 (by norm_num)
  mixed2 := AxisOperators.inverseMixed I hε 2 (by norm_num)

/-- The nonlinear map on the actual complete smooth coefficient space
has a single threshold valid for all normalized angular data in a fixed
norm ball. No remainder bound is supplied as a hypothesis. -/
theorem coefficient_fixedPoint
    (I : AxisCoefficientSpace.Window) {ε : ℝ} (hε : 0 < ε)
    (d : AxisData (AxisCoefficientSpace.AxisSpace I ε))
    (S : AxisCoefficientSpace.AxisSpace I ε →L[ℝ] AxisCoefficientSpace.AxisSpace I ε)
    (M : ℝ) (hM : 0 ≤ M) :
    let O := coefficientOperators I hε
    ∃ Λ₀ : ℝ, 0 < Λ₀ ∧ ∀ Λ : ℝ, Λ₀ ≤ Λ →
      ∀ a : AxisCoefficientSpace.AxisSpace I ε, ‖a‖ ≤ M →
      ∃ x : AxisCoefficientSpace.AxisSpace I ε × AxisCoefficientSpace.AxisSpace I ε,
        ‖x - referencePair O d S‖ ≤ 1 ∧
        referencePair O d S +
          (1 / (2 * Λ)) • naturalRemainder O d S (1 / Λ) a x = x ∧
        ‖x - referencePair O d S‖ ≤
          remainderBound O d S (‖referencePair O d S‖ + 1) M (by positivity) hM / (2 * Λ) ∧
        ∀ y, ‖y - referencePair O d S‖ ≤ 1 →
          referencePair O d S +
            (1 / (2 * Λ)) • naturalRemainder O d S (1 / Λ) a y = y → y = x :=
  uniform_natural_fixedPoint (coefficientOperators I hε) d S M hM

/-- Existence of actual smooth coefficient profiles for the natural
integrated system, with the constructed angular resolvent and uniform
large-Λ estimate. The initial analytic coefficient data remain explicit. -/
theorem natural_axis_profiles
    (I : AxisCoefficientSpace.Window) {ε : ℝ} (hε : 0 < ε)
    (χ : AxisCoefficientSpace.AxisSpace I ε)
    (d : AxisData (AxisCoefficientSpace.AxisSpace I ε))
    (M : ℝ) (hM : 0 ≤ M) :
    let O := coefficientOperators I hε
    let S := AxisResolvent.naturalResolvent I hε χ
    let Q := AxisResolvent.naturalOperator I hε χ
    let x₀ := referencePair O d S
    ∃ Λ₀ : ℝ, 0 < Λ₀ ∧ ∀ Λ : ℝ, Λ₀ ≤ Λ →
      ∀ a : AxisCoefficientSpace.AxisSpace I ε, ‖a‖ ≤ M →
      ∃ x : AxisCoefficientSpace.AxisSpace I ε × AxisCoefficientSpace.AxisSpace I ε,
        ‖x - x₀‖ ≤ 1 ∧
        ‖x - x₀‖ ≤ remainderBound O d S (‖x₀‖ + 1) M (by positivity) hM / (2 * Λ) ∧
        x.1 + Q x.1 = d.one + (1 / (2 * Λ)) •
          (naturalRemainder O d (ContinuousLinearMap.id ℝ _) (1 / Λ) a x).1 ∧
        x.2 = -(1 / 2 : ℝ) • O.j1 (O.product d.inverseL d.zStar) +
          (1 / (2 * Λ)) • (naturalRemainder O d (ContinuousLinearMap.id ℝ _) (1 / Λ) a x).2 ∧
        ContDiffOn ℝ ∞ (AxisEvaluation.profile I ε x.1) (AxisEvaluation.strip I 20) ∧
        ContDiffOn ℝ ∞ (AxisEvaluation.profile I ε x.2) (AxisEvaluation.strip I 20) := by
  dsimp only
  obtain ⟨Λ₀, hΛ₀, hexists⟩ :=
    coefficient_fixedPoint I hε d (AxisResolvent.naturalResolvent I hε χ) M hM
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ a ha
  obtain ⟨x, hball, hfixed, herr, _⟩ := hexists Λ hΛ a ha
  have heq := fixedPoint_integrated_equations (coefficientOperators I hε) d
    (AxisResolvent.naturalResolvent I hε χ) (AxisResolvent.naturalOperator I hε χ)
    (AxisResolvent.naturalResolvent_equation I hε χ) (1 / Λ) (1 / (2 * Λ)) a x hfixed
  exact ⟨x, hball, herr, heq.1, heq.2,
    AxisEvaluation.profile_smooth I hε x.1, AxisEvaluation.profile_smooth I hε x.2⟩

end NavierStokes.AxisContraction
