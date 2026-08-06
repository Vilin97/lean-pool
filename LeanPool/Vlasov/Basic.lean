/-
Copyright (c) 2026 Joseph K. Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph K. Miller
-/
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Tight
import LeanPool.Vlasov.Base.Geometry
import LeanPool.Vlasov.OT.Wasserstein

/-!
# Derivation of the Vlasov equation from N-particle Hamiltonian dynamics

Formalization of the companion paper (`vlasov.tex`).  This file develops the
mean-field theory of the Vlasov equation:

* the N-particle mean-field Hamiltonian and Newton equations of motion;
* the empirical measure of a configuration and its weak (distributional)
  evolution along Newton trajectories;
* the distributional Vlasov equation and its Lagrangian (characteristic-flow)
  formulation;
* the Kantorovich–Rubinstein convolution estimate and the Dobrushin
  Wasserstein-1 stability estimate;
* the mean-field limit theorem: the empirical measures of the N-particle
  system converge in W₁ to the Vlasov solution as N → ∞.

`(tex: …)` labels cross-reference the companion LaTeX paper.
-/

open MeasureTheory

namespace Vlasov

/-!
## Basic type aliases and notation

Throughout, `d : ℕ` is the spatial dimension and `N : ℕ` is the number of particles.
Phase space for a single particle is `EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)`.
-/

variable {d : ℕ} [NeZero d]

-- `PhysSpace`/`PhaseSpace` live in `LeanPool/Vlasov/Base/Geometry.lean`.

/-! ## §1 Equation (Hamiltonian)  (`tex: eq:HN`) -/

/-- (tex: eq:HN)
The mean-field Hamiltonian for N identical unit-mass particles in ℝ^d:

  H_N(X, V) = Σ_{i=1}^{N} |v_i|² / 2  +  (1/N) Σ_{1 ≤ i < j ≤ N} W(x_i − x_j).

The factor 1/N normalises the interaction energy so that kinetic and potential
energies are of the same order as N → ∞.
-/
noncomputable def hamiltonianN (N : ℕ) (W : PhysSpace d → ℝ)
    (X V : Fin N → PhysSpace d) : ℝ :=
  (∑ i : Fin N, ‖V i‖ ^ 2 / 2)
  + (1 / (N : ℝ)) * ∑ i : Fin N, ∑ j : Fin N,
      if (i : ℕ) < j then W (X i - X j) else 0

/-! ## §2 Equation (Hamilton / Newton equations of motion)  (`tex: eq:newton`) -/

/-- (tex: eq:newton)
Predicate asserting that a curve (X, V) : ℝ → (Fin N → PhysSpace d)²
satisfies the N-particle mean-field Newton equations

  x'_i = v_i,
  v'_i = −(1/N) Σ_{j ≠ i} ∇W(x_i − x_j),   i = 1, …, N.

`gradW` is the gradient ∇W : ℝ^d → ℝ^d of the pair potential.
-/
def IsNewtonSolution (N : ℕ) (gradW : PhysSpace d → PhysSpace d)
    (X V : ℝ → Fin N → PhysSpace d) : Prop :=
  -- position equations: X'_i(t) = V_i(t)
  (∀ t i, HasDerivAt (fun t => X t i) (V t i) t) ∧
  -- velocity equations: V'_i(t) = −(1/N) Σ_{j ≠ i} ∇W(X_i(t) − X_j(t))
  (∀ t i, HasDerivAt (fun t => V t i)
      (-(1 / (N : ℝ)) • ∑ j : Fin N, if j ≠ i then gradW (X t i - X t j) else 0)
      t)

/-! ## §3 Assumption  (`tex: ass:W`) -/

/-- (tex: ass:W)
Standing assumption on the pair potential W : ℝ^d → ℝ.

W belongs to C^{1,1}(ℝ^d): it is differentiable with a globally Lipschitz
gradient.  Additionally W is even: W(−x) = W(x) for all x.
The Lipschitz constant L := Lip(∇W) is finite.
-/
class AssW (W : PhysSpace d → ℝ) : Prop where
  /-- W is continuously differentiable. -/
  differentiable : Differentiable ℝ W
  /-- W is even. -/
  even : ∀ x : PhysSpace d, W (-x) = W x
  /-- The gradient ∇W is Lipschitz with some constant L ≥ 0. -/
  lipschitzGrad : ∃ L : NNReal, LipschitzWith L (fun x => fderiv ℝ W x)

/-- (tex: ass:W2)
Strengthened standing assumption for the weak ⟹ Lagrangian bridge: `AssW` (so `W ∈ C^{1,1}`,
i.e. ∇W globally Lipschitz, and W even) together with `∇W ∈ C¹` (so `W ∈ C²`).

The extra `gradContDiff` field is stated on `fun x => fderiv ℝ W x` — the same object as
`AssW.lipschitzGrad` — so the `C^{1,1}` (Lipschitz) and `C²` (continuously differentiable)
facts concern one map.  This is what makes the Vlasov phase-space field C¹ in space, which the
characteristic flow's C¹ dependence on its initial point (the variational equation) requires.

Only the weak ⟹ Lagrangian bridge (`LeanPool/Vlasov/OT/WeakToLagrangian.lean`) carries `AssW2`; the
marquee `vlasovWellPosedness` / `dobrushin` stay at the weaker `AssW` (arbitrary Lipschitz
constant). -/
class AssW2 (W : PhysSpace d → ℝ) : Prop extends AssW W where
  /-- ∇W is continuously differentiable (equivalently `W ∈ C²`). -/
  gradContDiff : ContDiff ℝ 1 (fun x => fderiv ℝ W x)

omit [NeZero d] in
/-- Helper: under `[AssW W]` (even + differentiable), the gradient of `W`
at the origin vanishes.

Mathematical content: differentiating `W(-x) = W(x)` at `x = 0` and using
`HasFDerivAt.unique` gives `fderiv W 0 = -fderiv W 0`, hence
`gradient W 0 = -gradient W 0`. In the real vector space `EuclideanSpace ℝ (Fin d)`
this forces `gradient W 0 = 0`.

Used by `empiricalMeasureSolvesVlasov` (cor:empirical-vlasov) to kill the
diagonal correction term in `weakEvolutionEmpiricalMeasure`. -/
lemma gradient_zero_of_even (W : PhysSpace d → ℝ) [hW : AssW W] :
    gradient W 0 = 0 := by
  -- Step A: the claim that the gradient at 0 equals its own negation.
  suffices h : gradient W 0 = -gradient W 0 by
    -- x = -x in a ℝ-vector space ⟹ x = 0.
    have h2 : gradient W 0 + gradient W 0 = 0 := by
      nth_rewrite 2 [h]
      exact add_neg_cancel (gradient W 0)
    -- Rewrite x + x as 2 • x and use the real-vector-space cancellation.
    have h3 : (2 : ℝ) • gradient W 0 = 0 := by
      rw [show (2 : ℝ) • gradient W 0 = gradient W 0 + gradient W 0 from by
            rw [two_smul]]
      exact h2
    exact (smul_eq_zero.mp h3).resolve_left (by norm_num)
  -- Step B: prove gradient W 0 = -gradient W 0 via the fderiv chain rule on
  -- the (trivial) composition W ∘ Neg.neg = W.
  have hdiff : Differentiable ℝ W := hW.differentiable
  -- Strategy: prove `gradient W 0 = -gradient W 0` by exhibiting two
  -- HasFDerivAt witnesses for W at 0 and invoking uniqueness.
  -- The first witness is the standard `fderiv ℝ W 0`; the second comes
  -- from the chain rule on `(fun x => W (-x))`, which equals W by
  -- evenness.
  have h_W0 : HasFDerivAt W (fderiv ℝ W 0) 0 :=
    hdiff.differentiableAt.hasFDerivAt
  -- Derivative of `(fun x : PhysSpace d => -x)` at 0 is `-id` (as a CLM).
  -- We get it from `hasFDerivAt_id` and `.neg` (which negates the function
  -- pointwise, equivalent to applying negation to the argument).
  have h_neg : HasFDerivAt (fun x : PhysSpace d => -x)
      (-ContinuousLinearMap.id ℝ (PhysSpace d)) 0 :=
    (hasFDerivAt_id (𝕜 := ℝ) (0 : PhysSpace d)).neg
  -- Need h_W0 phrased at `-(0 : PhysSpace d)` for the chain rule below.
  have h_W_at_neg0 : HasFDerivAt W (fderiv ℝ W 0) (-(0 : PhysSpace d)) := by
    rw [neg_zero]; exact h_W0
  -- Chain rule applied to W ∘ (-·) gives `HasFDerivAt (fun x => W (-x)) ...`.
  have h_chain : HasFDerivAt (fun x : PhysSpace d => W (-x))
      ((fderiv ℝ W 0).comp (-ContinuousLinearMap.id ℝ (PhysSpace d))) 0 :=
    h_W_at_neg0.comp 0 h_neg
  -- Evenness rewrites `(fun x => W (-x))` to `W`, giving a second
  -- HasFDerivAt witness for W at 0.
  have hcomp_eq : (fun x : PhysSpace d => W (-x)) = W := funext hW.even
  rw [hcomp_eq] at h_chain
  -- Uniqueness of the Fréchet derivative.
  have h_fderiv : fderiv ℝ W 0
      = (fderiv ℝ W 0).comp (-ContinuousLinearMap.id ℝ (PhysSpace d)) :=
    h_W0.unique h_chain
  -- f.comp (-id) = -f for any CLM f.
  have h_comp_neg : (fderiv ℝ W 0).comp (-ContinuousLinearMap.id ℝ (PhysSpace d))
      = -(fderiv ℝ W 0) := by
    ext v
    simp only [ContinuousLinearMap.comp_apply, neg_apply,
               ContinuousLinearMap.id_apply, ContinuousLinearMap.map_neg]
  rw [h_comp_neg] at h_fderiv
  -- Push `fderiv ℝ W 0 = -fderiv ℝ W 0` through `(toDual).symm`
  -- (a linear isomorphism) to land at `gradient W 0 = -gradient W 0`.
  have h_grad : gradient W 0 = -gradient W 0 :=
    (congrArg (InnerProductSpace.toDual ℝ (PhysSpace d)).symm h_fderiv).trans
      (map_neg _ _)
  exact h_grad

/-! ## §4 Definition (Empirical measure)  (`tex: def:empirical`) -/

-- TODO(mathlib): Mathlib does not yet have a ready-made `empiricalMeasure`
-- construction returning a `ProbabilityMeasure`.  We define it here as a
-- placeholder using `MeasureTheory.Measure.dirac` and a finite sum.

/-- (tex: def:empirical)
The empirical measure of a configuration (X, V) ∈ (ℝ^d × ℝ^d)^N:

  μ^N[X, V] := (1/N) Σ_{i=1}^{N} δ_{(X_i, V_i)}.

Returns a `MeasureTheory.Measure (PhaseSpace d)`.  It is a probability measure
when N ≥ 1.
-/
noncomputable def empiricalMeasure (N : ℕ) (X V : Fin N → PhysSpace d) :
    Measure (PhaseSpace d) :=
  (1 / (N : ENNReal)) • ∑ i : Fin N, Measure.dirac (X i, V i)

omit [NeZero d] in
/-- (tex: def:empirical)
When N ≥ 1 the empirical measure is a probability measure.

Proof: μ(univ) = (1/N) · Σᵢ δ_{zᵢ}(univ) = (1/N) · N · 1 = 1, where each
Dirac mass evaluates to 1 on the universal set via the
`Measure.dirac.isProbabilityMeasure` instance. -/
lemma empiricalMeasure_isProbabilityMeasure (N : ℕ) [NeZero N]
    (X V : Fin N → PhysSpace d) :
    IsProbabilityMeasure (empiricalMeasure N X V) := by
  refine ⟨?_⟩
  simp only [empiricalMeasure, Measure.smul_apply, Measure.finsetSum_apply,
             measure_univ, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
             smul_eq_mul, nsmul_eq_mul, mul_one]
  exact ENNReal.div_mul_cancel
    (Nat.cast_ne_zero.mpr (NeZero.ne N)) (ENNReal.natCast_ne_top N)

/-- (tex: def:empirical)
The time-dependent empirical measure μ_t^N along a solution of eq:newton. -/
noncomputable def empiricalMeasureCurve (N : ℕ) (X V : ℝ → Fin N → PhysSpace d) :
    ℝ → Measure (PhaseSpace d) :=
  fun t => empiricalMeasure N (X t) (V t)

/-! ## §5 Proposition (Weak evolution of the empirical measure)  (`tex: prop:weak`) -/

-- TODO(mathlib): Convolution of a function with a measure (∇W * ρ) is used
-- below.  In Mathlib this would be `MeasureTheory.Measure.convolution` or a
-- hand-rolled integral.  We give a local definition as a placeholder.

/-- Convolution of a function k : ℝ^d → ℝ^d with a (finite) measure ρ on ℝ^d:
  (k * ρ)(x) := ∫ k(x − y) dρ(y).
-/
noncomputable def convolveFunctionMeasure (k : PhysSpace d → PhysSpace d)
    (ρ : Measure (PhysSpace d)) (x : PhysSpace d) : PhysSpace d :=
  ∫ y, k (x - y) ∂ρ

/-- Spatial marginal of a measure on phase space. -/
noncomputable def spatialMarginal (μ : Measure (PhaseSpace d)) :
    Measure (PhysSpace d) :=
  Measure.map Prod.fst μ

omit [NeZero d] in
/-- The integral of a function φ against the empirical measure `empiricalMeasure N X V`
equals `(1/N) * ∑ i, φ(X i, V i)`, by unfolding the weighted sum of Dirac masses. -/
lemma empiricalMeasure_integral_eq (N : ℕ)
    (X V : Fin N → PhysSpace d)
    (φ : PhaseSpace d → ℝ) :
    ∫ z, φ z ∂(empiricalMeasure N X V) =
      (1 / (N : ℝ)) * ∑ i : Fin N, φ (X i, V i) := by
  simp only [empiricalMeasure]
  rw [integral_smul_measure]
  rw [integral_finsetSum_measure (fun i _ => integrable_dirac (by simp))]
  simp [integral_dirac, ENNReal.toReal_natCast, smul_eq_mul]

omit [NeZero d] in
/-- For a smooth test function φ, the chain rule gives: the map `t ↦ φ(X t i, V t i)` has
derivative `⟨V t i, gradXφ (X t i, V t i)⟩ + ⟨a t i, gradVφ (X t i, V t i)⟩` at t,
where `a t i` is the acceleration vector at particle i and time t.

φ's Fréchet derivative is an input hypothesis `hφ_fderiv` rather than derived
inside the helper, keeping the body a straight composition:
  · `HasDerivAt.prodMk hX hV` gives the curve derivative `t ↦ (X t i, V t i)`.
  · `(hφ_fderiv (X t i, V t i)).comp_hasDerivAt` composes through φ.
  · Unfolding `gradXφ`/`gradVφ` via `hgradXφ`/`hgradVφ` and rewriting the
    Fréchet derivative's action via inner-product partial-derivative
    identities gives the target inner-product form. -/
lemma hasDerivAt_phi_along_trajectory (N : ℕ)
    (X V : ℝ → Fin N → PhysSpace d)
    (hX : ∀ t i, HasDerivAt (fun t => X t i) (V t i) t)
    (a : ℝ → Fin N → PhysSpace d)
    (hV : ∀ t i, HasDerivAt (fun t => V t i) (a t i) t)
    (φ : PhaseSpace d → ℝ)
    (φ' : PhaseSpace d → (PhaseSpace d →L[ℝ] ℝ))
    (hφ_fderiv : ∀ z, HasFDerivAt φ (φ' z) z)
    (gradXφ gradVφ : PhaseSpace d → PhysSpace d)
    (hgradXφ : ∀ z, gradXφ z = gradient (fun x => φ (x, z.2)) z.1)
    (hgradVφ : ∀ z, gradVφ z = gradient (fun v => φ (z.1, v)) z.2)
    (t : ℝ) (i : Fin N) :
    HasDerivAt (fun s => φ (X s i, V s i))
      (@inner ℝ (PhysSpace d) _ (V t i) (gradXφ (X t i, V t i)) +
       @inner ℝ (PhysSpace d) _ (a t i) (gradVφ (X t i, V t i))) t := by
  -- Step 1: curve derivative
  have hcurve : HasDerivAt (fun s => (X s i, V s i)) (V t i, a t i) t :=
    (hX t i).prodMk (hV t i)
  -- Step 2: compose φ through the curve
  have hcomp : HasDerivAt (fun s => φ (X s i, V s i))
      ((φ' (X t i, V t i)) (V t i, a t i)) t :=
    (hφ_fderiv (X t i, V t i)).comp_hasDerivAt t hcurve
  -- Step 3: rewrite the derivative value
  convert hcomp using 1
  -- Step 4: show φ'(z)(V,a) = ⟨V, gradXφ z⟩ + ⟨a, gradVφ z⟩
  set z := (X t i, V t i)
  -- partial x: HasFDerivAt (fun x => φ(x, z.2)) (φ' z ∘L inl ℝ _ _) z.1
  have hpX : HasFDerivAt (fun x => φ (x, z.2))
      ((φ' z).comp (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d))) z.1 :=
    (hφ_fderiv z).comp z.1 (hasFDerivAt_prodMk_left z.1 z.2)
  have hpV : HasFDerivAt (fun v => φ (z.1, v))
      ((φ' z).comp (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d))) z.2 :=
    (hφ_fderiv z).comp z.2 (hasFDerivAt_prodMk_right z.1 z.2)
  simp only [hgradXφ z, hgradVφ z]
  -- inner(V, ∇f z.1) = fderiv f z.1 V via inner_gradient_right (real case: conj = id)
  have hgX : @inner ℝ (PhysSpace d) _ (V t i) (gradient (fun x => φ (x, z.2)) z.1) =
      fderiv ℝ (fun x => φ (x, z.2)) z.1 (V t i) := by
    rw [inner_gradient_right]
    simp
  have hgV : @inner ℝ (PhysSpace d) _ (a t i) (gradient (fun v => φ (z.1, v)) z.2) =
      fderiv ℝ (fun v => φ (z.1, v)) z.2 (a t i) := by
    rw [inner_gradient_right]
    simp
  rw [hgX, hgV, hpX.fderiv, hpV.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
        ContinuousLinearMap.inr_apply]
  rw [← map_add]
  simp [Prod.mk_add_mk]

omit [NeZero d] in
/-- The derivative of `t ↦ ∫ φ d(empiricalMeasureCurve N X V t)` equals the finite sum
expression `(1/N) * Σᵢ [⟨V t i, gradXφ (X t i, V t i)⟩ + ⟨aᵢ, gradVφ (X t i, V t i)⟩]`
where `aᵢ = -(1/N) Σ_{j≠i} gradW(X t i - X t j)` is the Newton acceleration,
obtained by combining `empiricalMeasure_integral_eq` and `hasDerivAt_phi_along_trajectory`
with `HasDerivAt.sum` and `HasDerivAt.const_smul`. -/
lemma hasDerivAt_empiricalIntegral_sum (N : ℕ)
    (gradW : PhysSpace d → PhysSpace d)
    (X V : ℝ → Fin N → PhysSpace d)
    (hSol : IsNewtonSolution N gradW X V)
    (φ : PhaseSpace d → ℝ)
    (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ)
    (gradXφ gradVφ : PhaseSpace d → PhysSpace d)
    (hgradXφ : ∀ z, gradXφ z = gradient (fun x => φ (x, z.2)) z.1)
    (hgradVφ : ∀ z, gradVφ z = gradient (fun v => φ (z.1, v)) z.2)
    (t : ℝ) :
    HasDerivAt (fun s => ∫ z, φ z ∂(empiricalMeasureCurve N X V s))
      ((1 / (N : ℝ)) * ∑ i : Fin N,
        (@inner ℝ (PhysSpace d) _ (V t i) (gradXφ (X t i, V t i)) +
         @inner ℝ (PhysSpace d) _ (
           -(1 / (N : ℝ)) • ∑ j : Fin N, if j ≠ i then gradW (X t i - X t j) else 0)
           (gradVφ (X t i, V t i)))) t := by
  -- Construct φ's Fréchet derivative witness from smoothness.
  have hφ_diff : Differentiable ℝ φ := hφ_smooth.differentiable (by norm_num)
  have hφ_fderiv : ∀ z, HasFDerivAt φ (fderiv ℝ φ z) z := fun z =>
    hφ_diff.differentiableAt.hasFDerivAt
  -- The Newton-acceleration function, packaged for hasDerivAt_phi_along_trajectory.
  let acc : ℝ → Fin N → PhysSpace d := fun s i =>
    -(1 / (N : ℝ)) • ∑ j : Fin N, if j ≠ i then gradW (X s i - X s j) else 0
  -- Rewrite the integral via empiricalMeasure_integral_eq (per-time-slice).
  have hint : ∀ s : ℝ, ∫ z, φ z ∂(empiricalMeasureCurve N X V s) =
      (1 / (N : ℝ)) * ∑ i : Fin N, φ (X s i, V s i) := fun s => by
    simp only [empiricalMeasureCurve]
    exact empiricalMeasure_integral_eq N (X s) (V s) φ
  simp_rw [hint]
  -- Differentiate (1/N) * Σᵢ φ(Xₛᵢ, Vₛᵢ) wrt s.  Establish the per-particle
  -- derivative via hasDerivAt_phi_along_trajectory (using `acc` for the
  -- Newton acceleration), combine termwise via HasDerivAt.sum, then pull
  -- the (1/N) constant out via HasDerivAt.const_mul.
  have h_each : ∀ i : Fin N,
      HasDerivAt (fun s : ℝ => φ (X s i, V s i))
        (@inner ℝ (PhysSpace d) _ (V t i) (gradXφ (X t i, V t i)) +
         @inner ℝ (PhysSpace d) _ (acc t i) (gradVφ (X t i, V t i))) t := fun i =>
    hasDerivAt_phi_along_trajectory N X V hSol.1 acc hSol.2 φ
      (fderiv ℝ φ) hφ_fderiv gradXφ gradVφ hgradXφ hgradVφ t i
  have h_sum : HasDerivAt (fun s : ℝ => ∑ i : Fin N, φ (X s i, V s i))
      (∑ i : Fin N,
        (@inner ℝ (PhysSpace d) _ (V t i) (gradXφ (X t i, V t i)) +
         @inner ℝ (PhysSpace d) _ (acc t i) (gradVφ (X t i, V t i)))) t :=
    HasDerivAt.fun_sum (fun i _ => h_each i)
  exact h_sum.const_mul (1 / (N : ℝ))

omit [NeZero d] in
/-- Convolution of the kernel `gradW` against the spatial marginal ofthe
empirical measure unfolds to the explicit finite sum
`(1/N) • Σⱼ gradW(X t i − X t j)`.  This separates the measure-pushforward /
Dirac-integration machinery from the algebraic "add and subtract the diagonal"
step in `diagonalCorrection_eq`.

Proof strategy:
  1. `empiricalMeasureCurve` and `empiricalMeasure` unfold to
     `(1/N : ℝ≥0∞) • Σⱼ Measure.dirac (X t j, V t j)`.
  2. `Measure.map_smul` (`MeasureTheory/Measure/Map.lean:127`) pushes
     `Prod.fst` through the scalar.
  3. `Measure.map_add` (`MeasureTheory/Measure/Map.lean:103`) + finset
     induction distributes `Prod.fst` over the sum, giving
     `(1/N : ℝ≥0∞) • Σⱼ Measure.dirac (X t j)`.
  4. `convolveFunctionMeasure` unfolds to `∫ y, gradW(X t i − y) ∂ρ`.
  5. `integral_smul_measure` (Bochner) extracts the `(1/N).toReal = 1/N`
     scalar; `integral_finsetSum_measure` (`Integral/Bochner/Basic.lean`)
     distributes integration over the finite sum of Diracs;
     `integral_dirac'` (`Integral/Bochner/Basic.lean`) collapses each
     summand to `gradW(X t i − X t j)`. -/
lemma convolveFunctionMeasure_empiricalSpatial_eq (N : ℕ)
    (gradW : PhysSpace d → PhysSpace d)
    (hgradW_meas : Measurable gradW)
    (X V : ℝ → Fin N → PhysSpace d) (t : ℝ) (i : Fin N) :
    convolveFunctionMeasure gradW
        (spatialMarginal (empiricalMeasureCurve N X V t)) (X t i) =
      (1 / (N : ℝ)) • ∑ j : Fin N, gradW (X t i - X t j) := by
  -- Measurability witnesses
  have hmeas_y : Measurable (fun y : PhysSpace d => gradW (X t i - y)) :=
    hgradW_meas.comp (measurable_const.sub measurable_id)
  have hsm_y : StronglyMeasurable (fun y : PhysSpace d => gradW (X t i - y)) :=
    hmeas_y.stronglyMeasurable
  have hmeas_z : Measurable (fun z : PhaseSpace d => gradW (X t i - z.1)) :=
    hgradW_meas.comp (measurable_const.sub measurable_fst)
  have hsm_z : StronglyMeasurable (fun z : PhaseSpace d => gradW (X t i - z.1)) :=
    hmeas_z.stronglyMeasurable
  -- Unfold the layered definitions.
  unfold convolveFunctionMeasure spatialMarginal empiricalMeasureCurve empiricalMeasure
  -- Convert integration against the pushforward (Prod.fst) to integration on the product.
  rw [integral_map measurable_fst.aemeasurable hsm_y.aestronglyMeasurable]
  -- Pull out the (1 / N : ℝ≥0∞) scalar.
  rw [integral_smul_measure]
  -- Distribute integration over the finite sum of Dirac measures.
  rw [integral_finsetSum_measure (fun j _ =>
        integrable_dirac' hsm_z (by simp [enorm_lt_top]))]
  -- Each Dirac integral collapses to the function value at the centre.
  simp only [integral_dirac' _ _ hsm_z]
  -- Normalize (1/(N:ℝ≥0∞)).toReal = 1/(N:ℝ); the .1 projection collapses on pairs.
  simp [ENNReal.toReal_natCast]

omit [NeZero d] in
/-- The remainder term `r` in the weak evolution identity equals
`(1/N²) * Σᵢ ⟨gradW 0, gradVφ(X t i, V t i)⟩`: this is the diagonal correction
obtained when extending the Newton-equation sum `Σ_{j≠i}` to all `j` (the diagonal
`j = i` summand contributes `gradW(X t i - X t i) = gradW 0`).

This lemma is pure inner-product algebra atop
`convolveFunctionMeasure_empiricalSpatial_eq`: extend `Σ_{j≠i}` to `Σⱼ` via
`Finset.sum_ite_ne` or `Finset.sum_compl_add_sum`, distribute the inner
product with `inner_sub_left`/`inner_smul_left`, recognise the
`(1/N) • Σⱼ gradW` factor as the convolveFunctionMeasure unfolding. -/
lemma diagonalCorrection_eq (N : ℕ)
    (gradW : PhysSpace d → PhysSpace d)
    (hgradW_meas : Measurable gradW)
    (X V : ℝ → Fin N → PhysSpace d)
    (gradVφ : PhaseSpace d → PhysSpace d)
    (t : ℝ) :
    (1 / (N : ℝ)) * ∑ i : Fin N,
      @inner ℝ (PhysSpace d) _ (
        -(1 / (N : ℝ)) • ∑ j : Fin N, if j ≠ i then gradW (X t i - X t j) else 0)
        (gradVφ (X t i, V t i))
    = -(1 / (N : ℝ)) * ∑ i : Fin N,
        @inner ℝ (PhysSpace d) _
          (convolveFunctionMeasure gradW
            (spatialMarginal (empiricalMeasureCurve N X V t)) (X t i))
          (gradVφ (X t i, V t i))
      + (1 / (N : ℝ)^2) * ∑ i : Fin N,
          @inner ℝ (PhysSpace d) _ (gradW 0) (gradVφ (X t i, V t i)) := by
  -- Step 1: unfold the convolution form on the RHS using the proved helper.
  have hconv : ∀ i : Fin N,
      convolveFunctionMeasure gradW
        (spatialMarginal (empiricalMeasureCurve N X V t)) (X t i)
      = (1 / (N : ℝ)) • ∑ j : Fin N, gradW (X t i - X t j) := fun i =>
    convolveFunctionMeasure_empiricalSpatial_eq N gradW hgradW_meas X V t i
  -- Step 2: extend the LHS's `Σ_{j≠i}` (via the ite/0 pattern) to `Σ_j − gradW 0`.
  have hext : ∀ i : Fin N,
      (∑ j : Fin N, if j ≠ i then gradW (X t i - X t j) else (0 : PhysSpace d))
      = (∑ j : Fin N, gradW (X t i - X t j)) - gradW 0 := by
    intro i
    have hsub : ∀ j : Fin N,
        (if j ≠ i then gradW (X t i - X t j) else (0 : PhysSpace d))
        = gradW (X t i - X t j)
          - (if j = i then gradW (X t i - X t j) else (0 : PhysSpace d)) := fun j => by
      by_cases hj : j = i <;> simp [hj]
    simp_rw [hsub]
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' Finset.univ i]
    simp
  -- Step 3: rewrite each per-i LHS inner product into scalar form.
  -- Use `real_inner_smul_left` (not generic `inner_smul_left`) to avoid a
  -- `starRingEnd ℝ` wrapper on the scalar that `ring` can't see through.
  have hlhs_i : ∀ i : Fin N,
      @inner ℝ (PhysSpace d) _
        (-(1 / (N : ℝ)) • ∑ j : Fin N, if j ≠ i then gradW (X t i - X t j) else (0 : PhysSpace d))
        (gradVφ (X t i, V t i))
      = -(1 / (N : ℝ)) *
          (@inner ℝ (PhysSpace d) _ (∑ j : Fin N, gradW (X t i - X t j)) (gradVφ (X t i, V t i))
           - @inner ℝ (PhysSpace d) _ (gradW 0) (gradVφ (X t i, V t i))) := by
    intro i
    rw [hext i, real_inner_smul_left, inner_sub_left]
  -- Step 4: rewrite each per-i RHS conv-term into scalar form.
  have hrhs_i : ∀ i : Fin N,
      @inner ℝ (PhysSpace d) _
        (convolveFunctionMeasure gradW
          (spatialMarginal (empiricalMeasureCurve N X V t)) (X t i))
        (gradVφ (X t i, V t i))
      = (1 / (N : ℝ)) * @inner ℝ (PhysSpace d) _
          (∑ j : Fin N, gradW (X t i - X t j)) (gradVφ (X t i, V t i)) := by
    intro i
    rw [hconv i, real_inner_smul_left]
  -- Step 5: substitute both rewrites and reduce to a ring identity on two abbreviated sums.
  simp_rw [hlhs_i, hrhs_i]
  -- Distribute the per-summand subtraction (mul_sub then sum_sub_distrib),
  -- pull constants outside via reverse Finset.mul_sum, then abbreviate.
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum]
  -- Goal is now an equation in two structural sums; ring closes the scalar identity.
  ring

omit [NeZero d] in
/-- The remainder bound: for the diagonal correction `r = (1/N²) * Σᵢ⟨gradW 0, gradVφ(zᵢ)⟩`,
we have `|r| ≤ (1/N) * (⨆ x, ‖gradW x‖) * (⨆ z, ‖gradVφ z‖)`, using
`abs_inner_le_norm` on each summand and the fact that the sum has N terms.

The two `BddAbove` hypotheses are essential: `ciSup` over an unbounded
function returns junk value 0 on `ℝ`, which would make the inequality
false in the unbounded case. The .tex's `‖∇W‖_∞ ‖∇_v φ‖_∞` implicitly
assumes L^∞ boundedness; making it explicit here keeps the lemma
honest. (For `gradVφ`: it comes from `∇_v φ` of a smooth compactly
supported `φ`, so the bound is a consequence of `HasCompactSupport`
— but expressing that derivation requires Mathlib API that's awkward
to assemble; easier to pass the bound as a hypothesis.) -/
lemma diagonalCorrection_bound (N : ℕ) [NeZero N]
    (gradW : PhysSpace d → PhysSpace d)
    (X V : ℝ → Fin N → PhysSpace d)
    (gradVφ : PhaseSpace d → PhysSpace d)
    (hgradW_bdd : BddAbove (Set.range (fun x => ‖gradW x‖)))
    (hgradVφ_bdd : BddAbove (Set.range (fun z => ‖gradVφ z‖)))
    (t : ℝ) :
    |(1 / (N : ℝ)^2) * ∑ i : Fin N,
        @inner ℝ (PhysSpace d) _ (gradW 0) (gradVφ (X t i, V t i))| ≤
      (1 / (N : ℝ)) * ⨆ x, ‖gradW x‖ * ⨆ z, ‖gradVφ z‖ := by
  -- Positivity facts.
  have hN_pos : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  have h_sW : 0 ≤ ⨆ x, ‖gradW x‖ := le_trans (norm_nonneg _) (le_ciSup hgradW_bdd 0)
  have h_sV : 0 ≤ ⨆ z, ‖gradVφ z‖ := le_trans (norm_nonneg _)
    (le_ciSup hgradVφ_bdd ((X t ⟨0, NeZero.pos N⟩), V t ⟨0, NeZero.pos N⟩))
  -- Per-summand bound: Cauchy-Schwarz + sup bounds.
  have h_term : ∀ i : Fin N,
      |@inner ℝ (PhysSpace d) _ (gradW 0) (gradVφ (X t i, V t i))| ≤
        (⨆ x, ‖gradW x‖) * (⨆ z, ‖gradVφ z‖) := fun i =>
    (abs_real_inner_le_norm _ _).trans
      (mul_le_mul (le_ciSup hgradW_bdd 0) (le_ciSup hgradVφ_bdd _)
        (norm_nonneg _) h_sW)
  -- Sum bound: |Σ| ≤ Σ|·| ≤ N * sup·sup.
  have h_sum : |∑ i : Fin N, @inner ℝ (PhysSpace d) _ (gradW 0) (gradVφ (X t i, V t i))|
      ≤ (N : ℝ) * ((⨆ x, ‖gradW x‖) * (⨆ z, ‖gradVφ z‖)) := by
    calc |∑ i : Fin N, @inner ℝ (PhysSpace d) _ (gradW 0) (gradVφ (X t i, V t i))|
        ≤ ∑ i : Fin N, |@inner ℝ (PhysSpace d) _ (gradW 0) (gradVφ (X t i, V t i))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin N, (⨆ x, ‖gradW x‖) * (⨆ z, ‖gradVφ z‖) :=
          Finset.sum_le_sum (fun i _ => h_term i)
      _ = (N : ℝ) * ((⨆ x, ‖gradW x‖) * (⨆ z, ‖gradVφ z‖)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- The RHS's `⨆ x, ‖gradW x‖ * ⨆ z, ‖gradVφ z‖` parses with the x-lambda
  -- extending over the whole `‖gradW x‖ * ⨆ z, ‖gradVφ z‖` body.  Since
  -- `⨆ z, ‖gradVφ z‖` is x-independent and nonneg, we can pull it out via
  -- `Real.iSup_mul_of_nonneg`.
  rw [show (⨆ x, ‖gradW x‖ * ⨆ z, ‖gradVφ z‖) = (⨆ x, ‖gradW x‖) * (⨆ z, ‖gradVφ z‖) from
    (Real.iSup_mul_of_nonneg h_sV _).symm]
  -- Finish with absolute-value + ring arithmetic.
  rw [abs_mul, abs_of_nonneg (by positivity)]
  calc (1 / (N : ℝ) ^ 2) * |∑ i : Fin N, @inner ℝ (PhysSpace d) _ (gradW 0) (gradVφ (X t i, V t i))|
      ≤ (1 / (N : ℝ) ^ 2) * ((N : ℝ) * ((⨆ x, ‖gradW x‖) * (⨆ z, ‖gradVφ z‖))) :=
        mul_le_mul_of_nonneg_left h_sum (by positivity)
    _ = (1 / (N : ℝ)) * ((⨆ x, ‖gradW x‖) * (⨆ z, ‖gradVφ z‖)) := by
        field_simp

omit [NeZero d] in
/-- (tex: prop:weak)
Weak evolution of the empirical measure.

Let (X, V) : [0, T] → (ℝ^d × ℝ^d)^N solve the Newton equations eq:newton,
and let ρ_t^N be the spatial marginal of the empirical measure μ_t^N.
Then for every test function φ ∈ C_c^∞(ℝ^d × ℝ^d) and every time t,
there is a real remainder r = R_N(t) such that

  d/dt ⟨μ_t^N, φ⟩ = ⟨μ_t^N, v · ∇_x φ − (∇W * ρ_t^N) · ∇_v φ⟩ + r,

with |r| ≤ (1/N) ‖∇W‖_∞ ‖∇_v φ‖_∞.  Concretely, r is the diagonal correction
+(1/N²) Σᵢ ∇W(0) · ∇_v φ(xᵢ, vᵢ).  (The positive sign arises because extending
the Newton-equation sum Σ_{j≠i} to Σ_j subtracts the j=i term `gradW(0)`,
which then gets multiplied by the outer `−(1/N)` acceleration coefficient,
yielding `+(1/N²)·gradW(0)·gradVφ`.)  Under Assumption ass:W (W even ⟹
∇W(0) = 0) the diagonal vanishes and r = 0; that strengthening is the
content of `empiricalMeasureSolvesVlasov` below.

The remainder is quantified existentially because `HasDerivAt` has a
unique derivative — a free `R_N` parameter would make the statement
false. -/
theorem weakEvolutionEmpiricalMeasure
    (N : ℕ) [NeZero N]
    (W : PhysSpace d → ℝ) [AssW W]
    (gradW : PhysSpace d → PhysSpace d)
    (hgradW : ∀ x, gradW x = gradient W x)
    (X V : ℝ → Fin N → PhysSpace d)
    (hSol : IsNewtonSolution N gradW X V)
    -- φ is a smooth compactly supported test function on phase space
    (φ : PhaseSpace d → ℝ)
    (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ)
    (_hφ_compact : HasCompactSupport φ)
    -- ∇_x φ and ∇_v φ regarded as functions
    (gradXφ gradVφ : PhaseSpace d → PhysSpace d)
    (hgradXφ : ∀ z, gradXφ z = gradient (fun x => φ (x, z.2)) z.1)
    (hgradVφ : ∀ z, gradVφ z = gradient (fun v => φ (z.1, v)) z.2)
    -- L^∞ boundedness for ‖gradW‖ and ‖gradVφ‖, needed for the bound
    -- conjunct's `ciSup` to be meaningful (without these, the sups on
    -- the RHS collapse to junk value 0 on `ℝ`, making the bound vacuous
    -- — and the helper `diagonalCorrection_bound` unprovable).  The
    -- .tex's `‖∇W‖_∞ ‖∇_v φ‖_∞` implicitly assumes these.
    (hgradW_bdd : BddAbove (Set.range (fun x => ‖gradW x‖)))
    (hgradVφ_bdd : BddAbove (Set.range (fun z => ‖gradVφ z‖)))
    (t : ℝ) :
    -- existential witness for the remainder, with its explicit form
    -- exposed so downstream corollaries (e.g. `empiricalMeasureSolvesVlasov`)
    -- can compute it without re-deriving from scratch.  Concretely,
    -- `r` is the diagonal correction term picked up when extending the
    -- Newton-equation sum from `j ≠ i` to all `j` (the `j = i` summand
    -- contributes `gradW 0`).
    ∃ r : ℝ,
      -- explicit formula for the remainder
      r = (1 / (N : ℝ)^2) * ∑ i : Fin N,
            @inner ℝ (PhysSpace d) _ (gradW 0) (gradVφ (X t i, V t i)) ∧
      -- derivative identity at t
      HasDerivAt (fun s => ∫ z, φ z ∂(empiricalMeasureCurve N X V s)) (
        ∫ z, (@inner ℝ (PhysSpace d) _ z.2 (gradXφ z) -
                @inner ℝ (PhysSpace d) _
                  (convolveFunctionMeasure gradW
                    (spatialMarginal (empiricalMeasureCurve N X V t)) z.1)
                  (gradVφ z))
              ∂(empiricalMeasureCurve N X V t)
          + r) t
      -- pointwise remainder bound
      ∧ |r| ≤ (1 / (N : ℝ)) *
          ⨆ x, ‖gradW x‖ * ⨆ z, ‖gradVφ z‖ := by
  -- Provide the explicit diagonal correction as the remainder witness.
  refine ⟨(1 / (N : ℝ)^2) * ∑ i : Fin N,
      @inner ℝ (PhysSpace d) _ (gradW 0) (gradVφ (X t i, V t i)), rfl, ?_, ?_⟩
  · -- HasDerivAt: use hasDerivAt_empiricalIntegral_sum and diagonalCorrection_eq
    -- to relate the finite-sum derivative to the integral + remainder form.
    have hderiv := hasDerivAt_empiricalIntegral_sum N gradW X V hSol φ
      hφ_smooth gradXφ gradVφ hgradXφ hgradVφ t
    -- Derive Measurable gradW from AssW W (Lipschitz fderiv ⇒ continuous gradient ⇒ measurable).
    have hgradW_meas : Measurable gradW := by
      have hext : gradW = fun x => gradient W x := funext hgradW
      rw [hext]
      obtain ⟨_, hLip⟩ := (inferInstance : AssW W).lipschitzGrad
      exact ((InnerProductSpace.toDual ℝ (PhysSpace d)).symm.continuous.comp
        hLip.continuous).measurable
    have hcorr := diagonalCorrection_eq N gradW hgradW_meas X V gradVφ t
    -- Rearrange: the derivative value from hderiv equals (integral term) + r
    -- after applying hcorr to split the velocity inner products.
    refine hderiv.congr_deriv ?_
    -- Convert the integral on the goal's RHS into a finite sum so we can
    -- match against hderiv's value plus hcorr.
    have hint : (∫ z, (@inner ℝ (PhysSpace d) _ z.2 (gradXφ z) -
                  @inner ℝ (PhysSpace d) _
                    (convolveFunctionMeasure gradW
                      (spatialMarginal (empiricalMeasureCurve N X V t)) z.1)
                    (gradVφ z))
                ∂(empiricalMeasureCurve N X V t)) =
        (1 / (N : ℝ)) * ∑ i : Fin N,
          (@inner ℝ (PhysSpace d) _ (V t i) (gradXφ (X t i, V t i)) -
           @inner ℝ (PhysSpace d) _
             (convolveFunctionMeasure gradW
               (spatialMarginal (empiricalMeasureCurve N X V t)) (X t i))
             (gradVφ (X t i, V t i))) := by
      simp only [empiricalMeasureCurve]
      exact empiricalMeasure_integral_eq N (X t) (V t)
        (fun z => @inner ℝ (PhysSpace d) _ z.2 (gradXφ z) -
                  @inner ℝ (PhysSpace d) _
                    (convolveFunctionMeasure gradW
                      (spatialMarginal (empiricalMeasureCurve N X V t)) z.1)
                    (gradVφ z))
    rw [hint]
    -- Goal: D(t) = (1/N) * Σᵢ (Aᵢ - Cᵢ) + r
    -- where D(t) = (1/N) * Σᵢ (Aᵢ + Bᵢ),
    --   Aᵢ = ⟨V t i, gradXφ (X t i, V t i)⟩,
    --   Bᵢ = ⟨-(1/N) • Σⱼ≠ᵢ gradW(Xᵢ-Xⱼ), gradVφᵢ⟩,
    --   Cᵢ = ⟨conv_i, gradVφᵢ⟩,
    --   r  = (1/N²) * Σᵢ ⟨gradW 0, gradVφᵢ⟩.
    -- hcorr says: (1/N) * Σᵢ Bᵢ = -(1/N) * Σᵢ Cᵢ + r.
    -- So (1/N) * Σ (A+B) = (1/N) Σ A + (1/N) Σ B
    --                   = (1/N) Σ A − (1/N) Σ C + r       [by hcorr]
    --                   = (1/N) Σ (A − C) + r              [recombine]
    -- Distribute Σ over (+) and (−) on both sides (keeping (1/N) outside),
    -- then split (1/N) * (sum + sum) into (1/N)*sum + (1/N)*sum.  hcorr fits
    -- the resulting linear identity directly.
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_add, mul_sub]
    linarith [hcorr]
  · -- Bound: direct application of diagonalCorrection_bound.
    exact diagonalCorrection_bound N gradW X V gradVφ hgradW_bdd hgradVφ_bdd t

/-! ## §6 Equation (Weak form of empirical-measure evolution)  (`tex: eq:weak-eq`) -/

/-- (tex: eq:weak-eq)
The distributional evolution identity for the empirical measure (the content
of Proposition prop:weak):

  d/dt ⟨μ_t^N, φ⟩  =  ⟨μ_t^N, v · ∇_x φ − (∇W * ρ_t^N) · ∇_v φ⟩ + R_N(t),

for every φ ∈ C_c^∞(ℝ^d × ℝ^d), with |R_N(t)| ≤ (1/N) ‖∇W‖_∞ ‖∇_v φ‖_∞.

This is a `Prop`-valued definition packaging the statement of eq:weak-eq.
-/
def WeakEvolutionEq (gradW : PhysSpace d → PhysSpace d)
    (μ : ℝ → Measure (PhaseSpace d))
    (φ : PhaseSpace d → ℝ)
    (gradXφ gradVφ : PhaseSpace d → PhysSpace d)
    (R_N : ℝ → ℝ) : Prop :=
  ∀ t : ℝ,
    HasDerivAt (fun s => ∫ z, φ z ∂μ s)
      (∫ z, (@inner ℝ (PhysSpace d) _ z.2 (gradXφ z) -
              @inner ℝ (PhysSpace d) _
                (convolveFunctionMeasure gradW (spatialMarginal (μ t)) z.1)
                (gradVφ z))
        ∂μ t
        + R_N t) t

/-! ## §7 Corollary (Empirical measure solves Vlasov)  (`tex: cor:empirical-vlasov`) -/

omit [NeZero d] in
/-- (tex: cor:empirical-vlasov)
Under Assumption ass:W, the empirical measure μ_t^N satisfies the distributional
Vlasov equation eq:vlasov with remainder R_N ≡ 0: for every φ ∈ C_c^∞(ℝ^d × ℝ^d),

  d/dt ⟨μ_t^N, φ⟩ = ⟨μ_t^N, v · ∇_x φ − (∇W * ρ_t^N) · ∇_v φ⟩.
-/
theorem empiricalMeasureSolvesVlasov
    (N : ℕ) [NeZero N]
    (W : PhysSpace d → ℝ) [hW : AssW W]
    (gradW : PhysSpace d → PhysSpace d)
    (hgradW : ∀ x, gradW x = gradient W x)
    (X V : ℝ → Fin N → PhysSpace d)
    (hSol : IsNewtonSolution N gradW X V)
    (φ : PhaseSpace d → ℝ)
    (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ)
    (gradXφ gradVφ : PhaseSpace d → PhysSpace d)
    (hgradXφ : ∀ z, gradXφ z = gradient (fun x => φ (x, z.2)) z.1)
    (hgradVφ : ∀ z, gradVφ z = gradient (fun v => φ (z.1, v)) z.2)
    -- Threaded through from `weakEvolutionEmpiricalMeasure`'s bound conjunct.
    -- Not used in this corollary's body (we destructure the bound and
    -- ignore it), but required by the signature of the prop:weak call.
    (hgradW_bdd : BddAbove (Set.range (fun x => ‖gradW x‖)))
    (hgradVφ_bdd : BddAbove (Set.range (fun z => ‖gradVφ z‖))) :
    WeakEvolutionEq gradW (empiricalMeasureCurve N X V) φ gradXφ gradVφ (fun _ => 0) := by
  -- WeakEvolutionEq unfolds to `∀ t, HasDerivAt ... (... + (fun _ => 0) t) t`.
  intro t
  -- Invoke prop:weak at this `t` and destructure the now-explicit witness.
  obtain ⟨r, hr_eq, hr_deriv, _hr_bound⟩ :=
    weakEvolutionEmpiricalMeasure N W gradW hgradW X V hSol φ
      hφ_smooth hφ_compact gradXφ gradVφ hgradXφ hgradVφ hgradW_bdd hgradVφ_bdd t
  -- Under [AssW W] we have gradW 0 = gradient W 0 = 0 (the latter via
  -- the even-implies-zero-gradient helper).
  have hgrad0 : gradW 0 = 0 := by
    rw [hgradW]; exact gradient_zero_of_even W
  -- The explicit formula for `r` collapses to 0 once gradW 0 = 0:
  -- each inner product becomes ⟨0, _⟩ = 0, the finite sum is 0, and
  -- the leading scalar multiplication is 0.
  have hr_zero : r = 0 := by
    rw [hr_eq, hgrad0]
    simp [inner_zero_left]
  -- Substitute r = 0 into the HasDerivAt witness; the conclusion's
  -- `(fun _ => 0) t` is definitionally 0.
  simpa [hr_zero] using hr_deriv

/-! ## §8 Equation (Vlasov equation)  (`tex: eq:vlasov`) -/

-- TODO(mathlib): A full measure-valued notion of distributional solution to
-- the nonlinear Vlasov PDE is not in Mathlib.  We define a placeholder
-- predicate capturing the weak formulation.

/-- (tex: eq:vlasov)
The nonlinear Vlasov equation for a curve of probability measures f_t on ℝ^d × ℝ^d:

  ∂_t f + v · ∇_x f − (∇W * ρ_t)(x) · ∇_v f = 0,   ρ_t(x) = ∫ f_t(x, dv).

We encode this as the distributional statement: for every φ ∈ C_c^∞(ℝ^d × ℝ^d)
the map t ↦ ∫ φ df_t satisfies

  d/dt ∫ φ df_t = ∫ [v · ∇_x φ − (∇W * ρ_t)(x) · ∇_v φ] df_t.
-/
def IsVlasovSolution (gradW : PhysSpace d → PhysSpace d)
    (f : ℝ → Measure (PhaseSpace d)) : Prop :=
  ∀ (φ : PhaseSpace d → ℝ),
    ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
    ∀ (gradXφ gradVφ : PhaseSpace d → PhysSpace d),
      (∀ z, gradXφ z = gradient (fun x => φ (x, z.2)) z.1) →
      (∀ z, gradVφ z = gradient (fun v => φ (z.1, v)) z.2) →
      WeakEvolutionEq gradW f φ gradXφ gradVφ (fun _ => 0)

/-! ## §9 Theorem (Existence and uniqueness for Vlasov)  (`tex: thm:vlasov-wp`) -/

-- TODO(mathlib): `𝒫_1` (probability measures with finite first moment) is
-- expressed here via `IsProbabilityMeasure` together with a `HasFiniteIntegral`
-- condition on the norm.

/-- Predicate: μ is a probability measure on PhaseSpace d with finite first moment. -/
def HasFiniteFirstMoment (μ : Measure (PhaseSpace d)) : Prop :=
  IsProbabilityMeasure μ ∧ Integrable (fun z : PhaseSpace d => ‖z‖) μ

-- The §9 statement `vlasovWellPosedness` (tex: thm:vlasov-wp) lives in
-- `LeanPool/Vlasov/OT/CharacteristicFlow.lean`, where it composes directly with the
-- characteristic-flow infrastructure (`exists_vlasov_characteristicFlow`,
-- `flow_distance_growth_bound`,
-- `vlasovSolutionViaPushforward_isLagrangianVlasovSolution`).  The
-- `HasFiniteFirstMoment` predicate above stays here, used by
-- `vlasovWellPosedness`'s hypothesis and by the Lagrangian solution cascade.

/-! ## §10 Equation (Characteristic / mean-field ODE)  (`tex: eq:char`) -/

-- TODO(mathlib): The self-consistent / mean-field characteristic ODE involves
-- a fixed-point condition coupling the flow to the pushforward measure.
-- We define the notion of a characteristic flow for a *given* curve of measures.

/-- (tex: eq:char)
Predicate asserting that (charX, charV) : ℝ → PhaseSpace d → PhysSpace d × PhysSpace d
is the characteristic flow associated to a given curve of spatial marginal measures
ρ : ℝ → Measure (PhysSpace d) and pair-potential gradient gradW:

  X'(t, z) = V(t, z),
  V'(t, z) = −(∇W * ρ_t)(X(t, z)),
  (X, V)(0, z) = z.

The self-consistent condition (ρ_t is the pushforward of f_0 under X(t, ·)) is
captured by `IsCharacteristicFlowSelfConsistent`.
-/
def IsCharacteristicFlow
    (gradW : PhysSpace d → PhysSpace d)
    (ρ : ℝ → Measure (PhysSpace d))
    (charX charV : ℝ → PhaseSpace d → PhysSpace d) : Prop :=
  -- initial condition
  (∀ z : PhaseSpace d, charX 0 z = z.1 ∧ charV 0 z = z.2) ∧
  -- position ODE: X'(t, z) = V(t, z)
  (∀ t z, HasDerivAt (fun s => charX s z) (charV t z) t) ∧
  -- velocity ODE: V'(t, z) = −(∇W * ρ_t)(X(t, z))
  (∀ t z, HasDerivAt (fun s => charV s z)
      (-(convolveFunctionMeasure gradW (ρ t) (charX t z))) t)

/-- (tex: eq:char)
The self-consistency condition: the spatial marginal ρ_t equals the pushforward
of the initial spatial marginal f₀_x under the position map X(t, ·). -/
def IsCharacteristicFlowSelfConsistent
    (charX : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d))
    (ρ : ℝ → Measure (PhysSpace d)) : Prop :=
  ∀ t, ρ t = Measure.map (fun z => charX t z) f₀

/-- (tex: eq:char)
The Vlasov solution f_t is the pushforward of f_0 under the characteristic map
(X(t,·), V(t,·)). -/
noncomputable def vlasovSolutionViaPushforward
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d)) (t : ℝ) : Measure (PhaseSpace d) :=
  Measure.map (fun z => (charX t z, charV t z)) f₀

/-- A Vlasov solution with an explicit characteristic-flow representation.

Strictly stronger than `IsVlasovSolution`: every `IsLagrangianVlasovSolution`
satisfies the weak PDE AND admits a global characteristic flow `(charX, charV)`
such that `f t = (charX t, charV t)_# (f 0)` for every `t`.

This is the regularity level at which the dynamic-continuity / Lipschitz-on-
flow / dominated-convergence-on-trajectory arguments (upper semicontinuity of
W₁ under narrow convergence, the derivative bound feeding Gronwall, narrow
continuity in the KR-dual formulation) compose cleanly — these all need the
flow witness, which the abstract `IsVlasovSolution` does not carry.

Producers:
  * `vlasovSolutionViaPushforward_isLagrangianVlasovSolution`
    (`LeanPool/Vlasov/OT/CharacteristicFlow.lean`) — takes the flow as a hypothesis,
    and the pushforward equation holds by `vlasovSolutionViaPushforward`'s
    definition.
  * `vlasovWellPosedness` produces `IsLagrangianVlasovSolution` from a Banach
    fixed-point construction on spatial marginals — the characteristic flow
    falls out of the existence proof, so the stronger conclusion costs no
    extra infrastructure.

`IsLagrangianVlasovSolution gradW f → IsVlasovSolution gradW f` by `.1`. -/
def IsLagrangianVlasovSolution (gradW : PhysSpace d → PhysSpace d)
    (f : ℝ → Measure (PhaseSpace d)) : Prop :=
  IsVlasovSolution gradW f ∧
  ∃ charX charV : ℝ → PhaseSpace d → PhysSpace d,
    IsCharacteristicFlow gradW (fun t => spatialMarginal (f t)) charX charV ∧
    (∀ t, f t = Measure.map (fun z : PhaseSpace d => (charX t z, charV t z)) (f 0)) ∧
    (∀ s, AEMeasurable (fun z : PhaseSpace d => (charX s z, charV s z)) (f 0))

/-! ## §11 Theorem (Dobrushin, 1979)  (`tex: thm:dobrushin`) -/

-- The Wasserstein-1 distance (`wasserstein1`), `wassersteinCost`, and
-- `wassersteinBar` OT core live in `LeanPool/Vlasov/OT/Wasserstein.lean`.
-- `HasFiniteFirstMoment` (PhaseSpace-specific) stays here.
/-- Completeness of `(𝒫_1(PhysSpace d), W₁)` for Polish spaces.

A Cauchy sequence in W₁ with a uniform first-moment bound has a W₁-limit in
`𝒫_1`.  The proof routes through Prokhorov + tightness from the moment bound
+ narrow-to-W₁ upgrade under moment control.

Used to lift the Picard iteration's Cauchy sequence (from the
`Phi_supW1_contraction` contraction estimate) to a W₁-limit in the curve
space; the limit is a fixed point of the Picard iteration, yielding a
self-consistent characteristic flow + Vlasov solution on `[0, T₀]`. -/
theorem exists_wasserstein1_limit_of_cauchy {d : ℕ}
    (ν : ℕ → Measure (PhysSpace d)) [∀ n, IsProbabilityMeasure (ν n)]
    (M : ℝ) (hMom : ∀ n, ∫ y, ‖y‖ ∂(ν n) ≤ M)
    (h_yint : ∀ n, Integrable (fun y : PhysSpace d => ‖y‖) (ν n))
    -- Cauchy hypothesis in ENNReal form (kept in ENNReal throughout,
    -- projecting to ℝ via `.toReal` only at the boundary).
    (hCauchy : ∀ ε : ENNReal, 0 < ε → ∃ N, ∀ m n, N ≤ m → N ≤ n →
                 wasserstein1 (ν m) (ν n) < ε) :
    ∃ μ : Measure (PhysSpace d), IsProbabilityMeasure μ ∧
      Integrable (fun y : PhysSpace d => ‖y‖) μ ∧
      -- Moment-preservation: the bound `M` passes to the limit by
      -- lower-semicontinuity of `∫ ‖·‖ ∂·` under W₁-convergence.  Standard
      -- consequence of W₁-convergence + uniform moment control; exposed in
      -- the conclusion so downstream consumers
      -- (`picard_iterate_exists_limit`) can re-use the
      -- same moment bound for the limit's `VlasovMeasureCurve` packaging.
      ∫ y, ‖y‖ ∂μ ≤ M ∧
      -- Conclusion also in ENNReal form; downstream consumers project
      -- to ℝ when matching `VlasovMeasureCurve.hW1Cont`'s `.toReal` interface.
      Filter.Tendsto (fun n => wasserstein1 (ν n) μ)
        Filter.atTop (nhds 0) := by
  classical
  -- `M ≥ 0` from `0 ≤ ∫ ‖y‖ ∂(ν 0) ≤ M`.
  have hM_nonneg : (0 : ℝ) ≤ M :=
    le_trans (integral_nonneg fun _ => norm_nonneg _) (hMom 0)
  -- Package each `ν n` as a `ProbabilityMeasure`.
  set P : ℕ → ProbabilityMeasure (PhysSpace d) := fun n => ⟨ν n, inferInstance⟩ with hP_def
  have hP_coe : ∀ n, ((P n : ProbabilityMeasure (PhysSpace d)) : Measure (PhysSpace d)) = ν n :=
    fun n => rfl
  set S : Set (ProbabilityMeasure (PhysSpace d)) := Set.range P with hS_def
  -- === Step 1: tightness of `S` (as a set of measures). ===
  have h_tight :
      MeasureTheory.IsTightMeasureSet
        {((Q : ProbabilityMeasure (PhysSpace d)) : Measure (PhysSpace d)) | Q ∈ S} := by
    rw [MeasureTheory.isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
    intro ε hε
    -- Trivial case: ε = ∞.
    rcases eq_or_ne ε ⊤ with hε_top | hε_top
    · exact ⟨Metric.closedBall (0 : PhysSpace d) 1, isCompact_closedBall _ _,
        fun μ _ => by simp [hε_top]⟩
    -- Choose radius `R` with `M / R ≤ ε.toReal` and `R ≥ 1`.
    have hεR : (0 : ℝ) < ε.toReal := ENNReal.toReal_pos hε.ne' hε_top
    set R : ℝ := max 1 (M / ε.toReal) with hR_def
    have hR_pos : (0 : ℝ) < R := lt_of_lt_of_le one_pos (le_max_left _ _)
    have hR_ge : M / R ≤ ε.toReal := by
      rcases le_or_gt M 0 with hM0 | hM0
      · exact le_trans (div_nonpos_of_nonpos_of_nonneg hM0 hR_pos.le) hεR.le
      · have hRge : M / ε.toReal ≤ R := le_max_right _ _
        rw [div_le_iff₀ hR_pos]
        calc M = (M / ε.toReal) * ε.toReal := by field_simp
          _ ≤ R * ε.toReal := by gcongr
          _ = ε.toReal * R := by ring
    refine ⟨Metric.closedBall (0 : PhysSpace d) R, isCompact_closedBall _ _, ?_⟩
    rintro μ ⟨Q, ⟨n, rfl⟩, rfl⟩
    -- Now `μ = ν n`.
    rw [hP_coe n]
    -- Markov inequality at threshold `R`.
    have h_markov : R * (ν n).real {x | R ≤ ‖x‖} ≤ ∫ y, ‖y‖ ∂(ν n) :=
      MeasureTheory.mul_meas_ge_le_integral_of_nonneg
        (Filter.Eventually.of_forall fun _ => norm_nonneg _) (h_yint n) R
    have h_real_le : (ν n).real {x | R ≤ ‖x‖} ≤ M / R := by
      rw [le_div_iff₀ hR_pos]
      calc (ν n).real {x | R ≤ ‖x‖} * R = R * (ν n).real {x | R ≤ ‖x‖} := by ring
        _ ≤ ∫ y, ‖y‖ ∂(ν n) := h_markov
        _ ≤ M := hMom n
    -- The complement of the closed ball is contained in `{R ≤ ‖x‖}`.
    have h_subset : (Metric.closedBall (0 : PhysSpace d) R)ᶜ ⊆ {x | R ≤ ‖x‖} := by
      intro x hx
      simp only [Metric.mem_closedBall, dist_zero_right, Set.mem_compl_iff, not_le] at hx
      exact le_of_lt hx
    -- Convert the ENNReal goal `(ν n) Kᶜ ≤ ε` via the real measure.
    rw [← MeasureTheory.ofReal_measureReal (measure_ne_top (ν n) _),
        ← ENNReal.ofReal_toReal hε_top]
    refine ENNReal.ofReal_le_ofReal ?_
    calc (ν n).real (Metric.closedBall (0 : PhysSpace d) R)ᶜ
        ≤ (ν n).real {x | R ≤ ‖x‖} :=
          MeasureTheory.measureReal_mono h_subset (measure_ne_top (ν n) _)
      _ ≤ M / R := h_real_le
      _ ≤ ε.toReal := hR_ge
  -- === Step 2: Prokhorov → convergent subsequence. ===
  have h_compact : IsCompact (closure S) :=
    isCompact_closure_of_isTightMeasureSet h_tight
  obtain ⟨Plim, _hPlim_mem, φ, hφ_mono, hφ_tendsto⟩ :=
    h_compact.tendsto_subseq (x := P) (fun n => subset_closure (Set.mem_range_self n))
  -- The limit measure.
  set μ : Measure (PhysSpace d) := (Plim : Measure (PhysSpace d)) with hμ_def
  haveI : IsProbabilityMeasure μ := Plim.2
  -- === Step 3: narrow convergence in test-integral form. ===
  have h_narrow : ∀ g : BoundedContinuousFunction (PhysSpace d) ℝ,
      Filter.Tendsto (fun k => ∫ x, g x ∂(ν (φ k))) Filter.atTop
        (nhds (∫ x, g x ∂μ)) := by
    intro g
    have h := (MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1
      hφ_tendsto) g
    -- `(P ∘ φ) k` coerces to `ν (φ k)`, and `Plim` coerces to `μ`.
    simpa only [Function.comp_apply, hP_coe, hμ_def] using h
  -- === Step 4: moment bound + integrability of the limit. ===
  -- Truncations `bR k x = min ‖x‖ k`, as bounded continuous functions.
  set bR : ℕ → PhysSpace d → ℝ := fun k x => min ‖x‖ (k : ℝ) with hbR_def
  have hbR_nonneg : ∀ (k : ℕ) (x : PhysSpace d), 0 ≤ bR k x :=
    fun k x => le_min (norm_nonneg x) (Nat.cast_nonneg k)
  have hbR_cont : ∀ k, Continuous (bR k) := fun k => continuous_norm.min continuous_const
  have hbR_bdd : ∀ (k : ℕ) (x : PhysSpace d), |bR k x| ≤ (k : ℝ) := by
    intro k x
    rw [abs_of_nonneg (hbR_nonneg k x)]
    exact min_le_right _ _
  set gR : ℕ → BoundedContinuousFunction (PhysSpace d) ℝ := fun k =>
    BoundedContinuousFunction.mkOfBound ⟨bR k, hbR_cont k⟩ (2 * (k : ℝ))
      (fun x y => by
        have hx := hbR_bdd k x; have hy := hbR_bdd k y
        rw [abs_le] at hx hy
        simp only [ContinuousMap.coe_mk, Real.dist_eq]
        rw [abs_le]; constructor <;> linarith) with hgR_def
  -- Each `bR k` is integrable wrt any finite measure (it's a bounded continuous function).
  have hbR_int : ∀ (k : ℕ) (ρ : Measure (PhysSpace d)) [IsFiniteMeasure ρ],
      Integrable (bR k) ρ := by
    intro k ρ _
    have h := (gR k).integrable ρ
    simpa only [hgR_def, BoundedContinuousFunction.mkOfBound_coe, ContinuousMap.coe_mk] using h
  have hbR_int_μ : ∀ k, Integrable (bR k) μ := fun k => hbR_int k μ
  -- `∫ bR k dμ ≤ M`, via narrow convergence from the subsequence.
  have h_bR_μ_le : ∀ k, ∫ x, bR k x ∂μ ≤ M := by
    intro k
    have h_tend : Filter.Tendsto (fun j => ∫ x, bR k x ∂(ν (φ j))) Filter.atTop
        (nhds (∫ x, bR k x ∂μ)) := by
      have h := h_narrow (gR k)
      simpa only [hgR_def, BoundedContinuousFunction.mkOfBound_coe, ContinuousMap.coe_mk] using h
    refine le_of_tendsto' h_tend (fun j => ?_)
    calc ∫ x, bR k x ∂(ν (φ j)) ≤ ∫ x, ‖x‖ ∂(ν (φ j)) :=
          integral_mono (hbR_int k (ν (φ j))) (h_yint (φ j)) (fun x => min_le_left _ _)
      _ ≤ M := hMom (φ j)
  -- Lift to the lintegral: `∫⁻ ofReal ‖x‖ dμ ≤ ofReal M`.
  have h_lint_le : ∫⁻ x, ENNReal.ofReal ‖x‖ ∂μ ≤ ENNReal.ofReal M := by
    -- Monotone convergence of `ofReal (bR k x) ↑ ofReal ‖x‖`.
    have h_mc : Filter.Tendsto (fun k => ∫⁻ x, ENNReal.ofReal (bR k x) ∂μ)
        Filter.atTop (nhds (∫⁻ x, ENNReal.ofReal ‖x‖ ∂μ)) := by
      refine MeasureTheory.lintegral_tendsto_of_tendsto_of_monotone
        (fun k => ((hbR_cont k).measurable.ennreal_ofReal).aemeasurable)
        (Filter.Eventually.of_forall fun x => ?_)
        (Filter.Eventually.of_forall fun x => ?_)
      · intro i j hij
        refine ENNReal.ofReal_le_ofReal ?_
        simp only [hbR_def]
        exact min_le_min le_rfl (by exact_mod_cast hij)
      · -- `bR k x = min ‖x‖ k → ‖x‖`.
        have h_ev : ∀ᶠ k in Filter.atTop, ENNReal.ofReal (bR k x) = ENNReal.ofReal ‖x‖ := by
          filter_upwards [Filter.eventually_ge_atTop ⌈‖x‖⌉₊] with k hk
          have hk' : ‖x‖ ≤ (k : ℝ) := (Nat.le_ceil ‖x‖).trans (by exact_mod_cast hk)
          simp only [hbR_def, min_eq_left hk']
        exact tendsto_const_nhds.congr' (h_ev.mono fun k hk => hk.symm)
    -- Each lintegral bound `∫⁻ ofReal (bR k) ≤ ofReal M`.
    have h_each : ∀ k, ∫⁻ x, ENNReal.ofReal (bR k x) ∂μ ≤ ENNReal.ofReal M := by
      intro k
      rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hbR_int_μ k)
        (Filter.Eventually.of_forall (hbR_nonneg k))]
      exact ENNReal.ofReal_le_ofReal (h_bR_μ_le k)
    exact le_of_tendsto' h_mc h_each
  -- Integrability of `‖·‖` wrt `μ`.
  have hμ_int : Integrable (fun y : PhysSpace d => ‖y‖) μ := by
    refine ⟨continuous_norm.aestronglyMeasurable, ?_⟩
    rw [MeasureTheory.hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall fun _ => norm_nonneg _)]
    exact lt_of_le_of_lt h_lint_le ENNReal.ofReal_lt_top
  -- Moment bound `∫ ‖y‖ dμ ≤ M`.
  have hμ_mom : ∫ y, ‖y‖ ∂μ ≤ M := by
    rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun _ => norm_nonneg _)
      continuous_norm.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hM_nonneg h_lint_le
  -- === Step 5: W₁ convergence (the bridge). ===
  refine ⟨μ, inferInstance, hμ_int, hμ_mom, ?_⟩
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨N, hN⟩ := hCauchy ε hε
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  -- Apply the static narrow-LSC bridge with `μ := ν n`, `ν := μ`, subseq `ν ∘ φ`.
  have h_lsc :
      wasserstein1 (ν n) μ ≤
        Filter.liminf (fun k => wasserstein1 (ν n) (ν (φ k))) Filter.atTop :=
    wasserstein1_le_liminf_of_narrow (ν n) (h_yint n) (fun k => ν (φ k)) μ hμ_int h_narrow
  refine le_trans h_lsc ?_
  -- Bound the liminf by `ε`: eventually `φ k ≥ N`, so `W₁(ν n, ν (φ k)) ≤ ε`.
  have h_ev_le : ∀ᶠ k in Filter.atTop, wasserstein1 (ν n) (ν (φ k)) ≤ ε := by
    filter_upwards [Filter.eventually_ge_atTop N] with k hk
    have hφk : N ≤ φ k := le_trans hk (hφ_mono.id_le k)
    exact le_of_lt (hN n (φ k) hn hφk)
  calc Filter.liminf (fun k => wasserstein1 (ν n) (ν (φ k))) Filter.atTop
      ≤ Filter.liminf (fun _ : ℕ => ε) Filter.atTop :=
        Filter.liminf_le_liminf h_ev_le
    _ = ε := Filter.liminf_const ε

/-!
## Note on finiteness in the convolution Lipschitz cascade

`convolveLipschitz_KR_le`, `convolveLipschitz_inner_bound`, and
`norm_convolveFunctionMeasure_sub_le` conclude in `.toReal` of an ENNReal
expression involving `wasserstein1 ρ σ`.  The inequality requires a finiteness
hypothesis `wasserstein1 ρ σ ≠ ⊤`: without it `(⊤ : ℝ≥0∞).toReal = 0` would
collapse any positive LHS bound.  The hypothesis is threaded through the
cascade and discharged at the Dobrushin call site from `HasFiniteFirstMoment`
via `wasserstein1_lt_top_of_finite_moment`.  See `formalize/DESIGN.md` (in the source repository).
-/


/-- For fixed `x : PhysSpace d` and `v : PhysSpace d`, the function
`y ↦ @inner ℝ (PhysSpace d) _ (gradW (x - y)) v` is LipschitzWith `(L * ‖v‖₊)`.
Proof: the map `y ↦ gradW (x - y)` is L-Lipschitz (composition of the L-Lipschitz `gradW`
with the 1-Lipschitz subtraction `y ↦ x - y`), and `w ↦ ⟨w, v⟩` is `‖v‖₊`-Lipschitz
(bounded linear map with operator norm `‖v‖`); compose via `LipschitzWith.comp`. -/
lemma convolveLipschitz_inner_lipschitz
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (x v : PhysSpace d) :
    LipschitzWith (L * ‖v‖₊) (fun y : PhysSpace d =>
      @inner ℝ (PhysSpace d) _ (gradW (x - y)) v) := by
  -- Step 1: y ↦ x - y is 1-Lipschitz (direct check via dist)
  have h_sub : LipschitzWith 1 (fun y : PhysSpace d => x - y) := by
    refine LipschitzWith.of_dist_le_mul (fun a b => ?_)
    rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm,
        sub_sub_sub_cancel_left, norm_sub_rev]
  -- Step 2: gradW ∘ (x - ·) is L-Lipschitz (since L * 1 = L)
  have h_gW : LipschitzWith L (fun y : PhysSpace d => gradW (x - y)) := by
    simpa [Function.comp_def] using hL.comp h_sub
  -- Step 3: w ↦ ⟨w, v⟩ is ‖v‖₊-Lipschitz by Cauchy-Schwarz
  have h_inner_v : LipschitzWith ‖v‖₊
      (fun w : PhysSpace d => @inner ℝ (PhysSpace d) _ w v) := by
    refine LipschitzWith.of_dist_le_mul (fun a b => ?_)
    rw [Real.dist_eq, ← inner_sub_left, dist_eq_norm]
    calc |@inner ℝ (PhysSpace d) _ (a - b) v|
        ≤ ‖a - b‖ * ‖v‖ := abs_real_inner_le_norm _ _
      _ = (‖v‖₊ : ℝ) * ‖a - b‖ := by rw [mul_comm]; rfl
  -- Step 4: compose (Lipschitz constant is ‖v‖₊ * L; rewrite to L * ‖v‖₊)
  have h_comp := h_inner_v.comp h_gW
  rwa [mul_comm] at h_comp

/-- For any 1-Lipschitz function `φ : PhysSpace d → ℝ`, the integral difference
`∫ φ dρ − ∫ φ dσ ≤ (wasserstein1 ρ σ).toReal`.
This follows directly from the Kantorovich–Rubinstein definition of `wasserstein1` as the
supremum of integral differences over 1-Lipschitz test functions, together with
`ENNReal.toReal_iSup` and `ENNReal.ofReal_toReal` to convert between ENNReal and ℝ. -/
lemma convolveLipschitz_KR_le
    {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α]
    (ρ σ : Measure α) (φ : α → ℝ) (hφ : LipschitzWith 1 φ)
    (hW : wasserstein1 ρ σ ≠ ⊤) :
    ∫ y, φ y ∂ρ - ∫ y, φ y ∂σ ≤ (wasserstein1 ρ σ).toReal := by
  -- The KR-dual lower bound (property-only): ENNReal.ofReal (∫φdρ − ∫φdσ) ≤ W₁.
  have h_sup : ENNReal.ofReal (∫ y, φ y ∂ρ - ∫ y, φ y ∂σ) ≤ wasserstein1 ρ σ :=
    wasserstein1_dual_lower_bound ρ σ φ hφ
  -- Convert to .toReal preserving the inequality.
  by_cases h_pos : 0 ≤ ∫ y, φ y ∂ρ - ∫ y, φ y ∂σ
  · -- positive case: ENNReal.ofReal x .toReal = x
    have := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hW).mpr h_sup
    rwa [ENNReal.toReal_ofReal h_pos] at this
  · -- negative case: LHS < 0 ≤ wasserstein1.toReal
    push Not at h_pos
    exact h_pos.le.trans ENNReal.toReal_nonneg

/-- For any `v : PhysSpace d` with `‖v‖ ≤ 1`, the real inner product
`⟨(∇W∗ρ)(x) − (∇W∗σ)(x), v⟩` is bounded by `(L : ℝ) * (wasserstein1 ρ σ).toReal`.
Proof: unfold `convolveFunctionMeasure` to expose `∫ gradW(x−y) dρ` and `∫ gradW(x−y) dσ`;
commute the inner product `⟨·, v⟩` (a continuous linear map) through each integral via
`ContinuousLinearMap.integral_comp_comm`; then the integrand function
`y ↦ ⟨gradW(x−y), v⟩` has Lipschitz constant `L * ‖v‖` ≤ `L`
(from `convolveLipschitz_inner_lipschitz`), so `(1/L) * (that integrand)` is 1-Lipschitz and
`convolveLipschitz_KR_le` closes the estimate. -/
lemma convolveLipschitz_inner_bound
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ σ : Measure (PhysSpace d))
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure σ]
    (x : PhysSpace d)
    (hW : wasserstein1 ρ σ ≠ ⊤)
    (hρ_int : Integrable (fun y => gradW (x - y)) ρ)
    (hσ_int : Integrable (fun y => gradW (x - y)) σ) :
    ∀ v : PhysSpace d, ‖v‖ ≤ 1 →
      @inner ℝ (PhysSpace d) _ (convolveFunctionMeasure gradW ρ x -
        convolveFunctionMeasure gradW σ x) v ≤
        (L : ℝ) * (wasserstein1 ρ σ).toReal := by
  intro v hv
  unfold convolveFunctionMeasure
  -- Case 1: v = 0 — inner with 0 is 0, RHS ≥ 0.
  by_cases hv_zero : v = 0
  · subst hv_zero
    rw [inner_zero_right]
    exact mul_nonneg L.coe_nonneg ENNReal.toReal_nonneg
  have hv_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv_zero
  -- Case 2: L = 0 — gradW is constant, and probability measures both have mass 1,
  -- so the two convolution integrals are equal, the difference is 0, the inner is 0.
  by_cases hL_zero : L = 0
  · have hgW_const : ∀ y, gradW (x - y) = gradW x := fun y => by
      have h := hL.dist_le_mul (x - y) x
      rw [hL_zero, NNReal.coe_zero, zero_mul] at h
      have h0 : dist (gradW (x - y)) (gradW x) = 0 := le_antisymm h dist_nonneg
      exact dist_eq_zero.mp h0
    have h_fun_eq : (fun y => gradW (x - y)) = (fun _ : PhysSpace d => gradW x) :=
      funext hgW_const
    have hF : ∫ y, gradW (x - y) ∂ρ = gradW x := by
      rw [h_fun_eq, integral_const]; simp
    have hG : ∫ y, gradW (x - y) ∂σ = gradW x := by
      rw [h_fun_eq, integral_const]; simp
    rw [hF, hG, sub_self, inner_zero_left]
    rw [hL_zero, NNReal.coe_zero, zero_mul]
  -- Case 3: L > 0 and v ≠ 0 — main KR rescaling argument.
  have hL_pos : (0 : ℝ) < L := lt_of_le_of_ne L.coe_nonneg (fun h =>
    hL_zero (NNReal.coe_eq_zero.mp h.symm))
  have hc_pos : (0 : ℝ) < (L : ℝ) * ‖v‖ := mul_pos hL_pos hv_pos
  -- Distribute inner across subtraction
  rw [inner_sub_left]
  -- Swap inner with integral on each side (via integral_inner + real_inner_comm)
  have h_swap_ρ : @inner ℝ (PhysSpace d) _ (∫ y, gradW (x - y) ∂ρ) v =
                  ∫ y, @inner ℝ (PhysSpace d) _ (gradW (x - y)) v ∂ρ := by
    rw [real_inner_comm, ← integral_inner hρ_int v]
    simp_rw [real_inner_comm v]
  have h_swap_σ : @inner ℝ (PhysSpace d) _ (∫ y, gradW (x - y) ∂σ) v =
                  ∫ y, @inner ℝ (PhysSpace d) _ (gradW (x - y)) v ∂σ := by
    rw [real_inner_comm, ← integral_inner hσ_int v]
    simp_rw [real_inner_comm v]
  rw [h_swap_ρ, h_swap_σ]
  -- Now goal: ∫ψ dρ − ∫ψ dσ ≤ L · W₁.toReal, with ψ(y) := ⟪gradW(x-y), v⟫_ℝ.
  set ψ : PhysSpace d → ℝ := fun y => @inner ℝ (PhysSpace d) _ (gradW (x - y)) v
    with hψ_def
  have hψ_lip : LipschitzWith (L * ‖v‖₊) ψ :=
    convolveLipschitz_inner_lipschitz gradW L hL x v
  -- Rescale ψ by c := L · ‖v‖ to get 1-Lipschitz φ.
  set c : ℝ := (L : ℝ) * ‖v‖ with hc_def
  set φ : PhysSpace d → ℝ := fun y => ψ y / c with hφ_def
  -- Coerce: ((L * ‖v‖₊ : ℝ≥0) : ℝ) = c
  have h_coe : ((L * ‖v‖₊ : NNReal) : ℝ) = c := by
    simp [hc_def, NNReal.coe_mul]
  -- φ is 1-Lipschitz: bound dist (φ a) (φ b).
  have hφ_lip : LipschitzWith 1 φ := by
    refine LipschitzWith.of_dist_le_mul (fun a b => ?_)
    rw [NNReal.coe_one, one_mul]
    have hψ_d : dist (ψ a) (ψ b) ≤ c * dist a b := by
      have := hψ_lip.dist_le_mul a b
      rwa [h_coe] at this
    -- dist (ψ a / c) (ψ b / c) = dist (ψ a) (ψ b) / c   (c > 0)
    have h_dist_div : dist (φ a) (φ b) = dist (ψ a) (ψ b) / c := by
      simp [hφ_def, Real.dist_eq, ← sub_div, abs_div, abs_of_pos hc_pos]
    rw [h_dist_div, div_le_iff₀ hc_pos]
    linarith
  -- Apply KR easy direction to the rescaled φ.
  have h_kr : ∫ y, φ y ∂ρ - ∫ y, φ y ∂σ ≤ (wasserstein1 ρ σ).toReal :=
    convolveLipschitz_KR_le ρ σ φ hφ_lip hW
  -- ∫φ = ∫ψ / c  (Bochner integral commutes with scalar division)
  have h_int_φ_ρ : ∫ y, φ y ∂ρ = (∫ y, ψ y ∂ρ) / c := by
    simp_rw [hφ_def, div_eq_mul_inv]
    rw [integral_mul_const]
  have h_int_φ_σ : ∫ y, φ y ∂σ = (∫ y, ψ y ∂σ) / c := by
    simp_rw [hφ_def, div_eq_mul_inv]
    rw [integral_mul_const]
  rw [h_int_φ_ρ, h_int_φ_σ, ← sub_div, div_le_iff₀ hc_pos] at h_kr
  -- h_kr : ∫ψ dρ − ∫ψ dσ ≤ W₁.toReal * c
  -- Goal:  ∫ψ dρ − ∫ψ dσ ≤ L * W₁.toReal
  -- Bridge: c * W₁ = L * ‖v‖ * W₁ ≤ L * W₁  (since ‖v‖ ≤ 1, W₁ ≥ 0)
  have hW_nonneg : 0 ≤ (wasserstein1 ρ σ).toReal := ENNReal.toReal_nonneg
  have h_chain : (wasserstein1 ρ σ).toReal * c ≤ (L : ℝ) * (wasserstein1 ρ σ).toReal := by
    rw [hc_def]
    calc (wasserstein1 ρ σ).toReal * ((L : ℝ) * ‖v‖)
        = (L : ℝ) * ((wasserstein1 ρ σ).toReal * ‖v‖) := by ring
      _ ≤ (L : ℝ) * ((wasserstein1 ρ σ).toReal * 1) := by
          gcongr
      _ = (L : ℝ) * (wasserstein1 ρ σ).toReal := by ring
  linarith

/-- For `z : PhysSpace d` and `C : ℝ`, if every unit vector `v` (with `‖v‖ ≤ 1`) satisfies
`@inner ℝ (PhysSpace d) _ z v ≤ C`, then `‖z‖ ≤ C`.
Proof: in the `z = 0` case, `‖0‖ = 0 ≤ C` (from `C ≥ ⟨0, 0⟩ = 0`); in the `z ≠ 0` case,
take `v = z / ‖z‖` (which satisfies `‖v‖ = 1`); then
`‖z‖ = ⟨z, z/‖z‖⟩ = ⟨z, v⟩ ≤ C` by hypothesis via `real_inner_self_eq_norm_mul_norm`. -/
lemma convolveLipschitz_norm_le_of_inner_forall
    {d : ℕ}
    (z : PhysSpace d) (C : ℝ)
    (h : ∀ v : PhysSpace d, ‖v‖ ≤ 1 → @inner ℝ (PhysSpace d) _ z v ≤ C) :
    ‖z‖ ≤ C := by
  by_cases hz : z = 0
  · -- z = 0 case: ‖0‖ = 0 ≤ C follows from h 0 (which gives ⟨0, 0⟩ = 0 ≤ C).
    rw [hz, norm_zero]
    have h0 := h 0 (by simp)
    simpa using h0
  · -- z ≠ 0 case: take v = z/‖z‖, which is a unit vector.
    have hz_pos : 0 < ‖z‖ := norm_pos_iff.mpr hz
    set v : PhysSpace d := (‖z‖⁻¹) • z with hv_def
    have hv_norm : ‖v‖ = 1 := by
      rw [hv_def, norm_smul, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr hz_pos), inv_mul_cancel₀ hz_pos.ne']
    -- ⟨z, v⟩ = ‖z‖⁻¹ * ⟨z, z⟩ = ‖z‖⁻¹ * ‖z‖² = ‖z‖
    have h_inner : @inner ℝ (PhysSpace d) _ z v = ‖z‖ := by
      rw [hv_def, real_inner_smul_right, real_inner_self_eq_norm_mul_norm]
      field_simp
    rw [← h_inner]
    exact h v hv_norm.le

-- Mathlib gap: pointwise Lipschitz estimate for the convolution ∇W * ρ.
-- Requires Wasserstein-1 Kantorovich–Rubinstein duality, which is not yet
-- in Mathlib's stable API for general metric spaces.
theorem norm_convolveFunctionMeasure_sub_le
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ σ : Measure (PhysSpace d))
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure σ]
    (x : PhysSpace d)
    (hW : wasserstein1 ρ σ ≠ ⊤)
    (hρ_int : Integrable (fun y => gradW (x - y)) ρ)
    (hσ_int : Integrable (fun y => gradW (x - y)) σ) :
    ‖convolveFunctionMeasure gradW ρ x - convolveFunctionMeasure gradW σ x‖ ≤
      (L : ℝ) * (wasserstein1 ρ σ).toReal := by
  -- Compose: from convolveLipschitz_inner_bound (for all unit v, ⟨z, v⟩ ≤ M)
  --          and convolveLipschitz_norm_le_of_inner_forall (then ‖z‖ ≤ M).
  exact convolveLipschitz_norm_le_of_inner_forall
    (convolveFunctionMeasure gradW ρ x - convolveFunctionMeasure gradW σ x)
    ((L : ℝ) * (wasserstein1 ρ σ).toReal)
    (convolveLipschitz_inner_bound gradW L hL ρ σ x hW hρ_int hσ_int)

/-- W₁-continuity of the integral against a Lagrangian Vlasov solution.

Uses the enriched `IsLagrangianVlasovSolution` predicate (carrying the
characteristic flow), which makes the proof structurally clean: by the
pushforward equation `f t = Measure.map (charX t, charV t) (f 0)` and
`integral_map`, `∫ φ d(f t) = ∫ (φ ∘ (charX t, charV t)) d(f 0)`.  Continuity
in `t` then reduces to dominated convergence on the *fixed* measure `f 0`,
with pointwise continuity from the flow's `HasDerivAt` and an integrable
dominator from `HasFiniteFirstMoment (f 0)` + a flow-growth bound. -/
lemma continuousOn_integral_of_isLagrangianVlasovSolution
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f : ℝ → Measure (PhaseSpace d))
    (hf_lag : IsLagrangianVlasovSolution gradW f)
    (hf_prob_0 : HasFiniteFirstMoment (f 0))
    (T : ℝ) (hT : 0 ≤ T)
    -- Flow-growth prerequisites: callers (e.g. `vlasovWellPosedness`) derive
    -- these from `HasFiniteFirstMoment (f 0)` + `LipschitzWith gradW` via a
    -- Gronwall bootstrap on the first moment of the spatial marginal.
    (M_ρ : ℝ) (hM_ρ_nn : 0 ≤ M_ρ)
    (hM_ρ : ∀ t ∈ Set.Icc 0 T,
      ∫ y, ‖y‖ ∂(spatialMarginal (f t)) ≤ M_ρ)
    (h_y_int : ∀ t ∈ Set.Icc 0 T,
      Integrable (fun y : PhysSpace d => ‖y‖) (spatialMarginal (f t)))
    (h_conv_int : ∀ t (x : PhysSpace d),
      Integrable (fun y => gradW (x - y)) (spatialMarginal (f t)))
    [∀ t, IsProbabilityMeasure (spatialMarginal (f t))]
    (φ : PhaseSpace d → ℝ)
    (hφ_lip : LipschitzWith 1 φ) :
    ContinuousOn (fun t => ∫ z, φ z ∂(f t)) (Set.Icc 0 T) := by
  -- Step 1: Destructure IsLagrangianVlasovSolution
  obtain ⟨_, charX, charV, hflow, hpush, hflow_meas⟩ := hf_lag
  obtain ⟨hflow_init, hflow_x, hflow_v⟩ := hflow
  -- Step 2: Rewrite ∫ φ d(f t) = ∫ (φ ∘ (charX t, charV t)) d(f 0)
  have h_rw : ∀ t, ∫ z, φ z ∂(f t) = ∫ z, φ (charX t z, charV t z) ∂(f 0) := by
    intro t
    rw [hpush t]
    exact integral_map (hflow_meas t) hφ_lip.continuous.measurable.aestronglyMeasurable
  -- Step 3: Prove growth bound inline (replicate flow_distance_growth_bound)
  set ρ := fun t => spatialMarginal (f t) with hρ_def
  set K := 1 + (L : ℝ) with hK_def
  set ε₀ := ‖gradW 0‖ + (L : ℝ) * M_ρ with hε₀_def
  have hK_pos : 0 < K := by positivity
  have hε₀_nn : 0 ≤ ε₀ := by positivity
  -- Convolution bound: ‖(∇W ∗ ρ_s)(x)‖ ≤ ε₀ + L * ‖x‖
  have h_conv_bound : ∀ s ∈ Set.Icc 0 T, ∀ x : PhysSpace d,
      ‖convolveFunctionMeasure gradW (ρ s) x‖ ≤ ε₀ + (L : ℝ) * ‖x‖ := by
    intro s hs x
    unfold convolveFunctionMeasure
    have h_sub_int : Integrable (fun y => ‖x - y‖) (ρ s) :=
      Integrable.mono' ((integrable_const ‖x‖).add (h_y_int s hs))
        ((aestronglyMeasurable_const (b := x)).sub aestronglyMeasurable_id |>.norm)
        (Filter.Eventually.of_forall fun y => by
          simp only [Real.norm_of_nonneg (norm_nonneg _)]
          exact norm_sub_le x y)
    have h_bnd_int : Integrable (fun y => ‖gradW 0‖ + (L : ℝ) * ‖x - y‖) (ρ s) :=
      (integrable_const _).add (h_sub_int.const_mul _)
    have h_pt : ∀ y : PhysSpace d, ‖gradW (x - y)‖ ≤ ‖gradW 0‖ + (L : ℝ) * ‖x - y‖ := by
      intro y
      have hd := hL.dist_le_mul (x - y) 0
      simp only [dist_eq_norm, sub_zero] at hd
      have h_tri : ‖gradW (x - y)‖ ≤ ‖gradW 0‖ + ‖gradW (x - y) - gradW 0‖ := by
        have := norm_add_le (gradW (x - y) - gradW 0) (gradW 0)
        simp only [sub_add_cancel] at this; linarith
      linarith
    calc ‖∫ y, gradW (x - y) ∂(ρ s)‖
        ≤ ∫ y, ‖gradW (x - y)‖ ∂(ρ s) := norm_integral_le_integral_norm _
      _ ≤ ∫ y, (‖gradW 0‖ + (L : ℝ) * ‖x - y‖) ∂(ρ s) :=
          integral_mono (h_conv_int s x).norm h_bnd_int (fun y => h_pt y)
      _ = ‖gradW 0‖ + (L : ℝ) * ∫ y, ‖x - y‖ ∂(ρ s) := by
          rw [integral_add (integrable_const _) (h_sub_int.const_mul _)]
          simp [integral_const, measureReal_def, measure_univ, integral_const_mul]
      _ ≤ ε₀ + (L : ℝ) * ‖x‖ := by
          have h_int_le : ∫ y, ‖x - y‖ ∂(ρ s) ≤ ‖x‖ + M_ρ := by
            calc ∫ y, ‖x - y‖ ∂(ρ s)
                ≤ ∫ y, (‖x‖ + ‖y‖) ∂(ρ s) :=
                  integral_mono h_sub_int ((integrable_const _).add (h_y_int s hs))
                    (fun y => norm_sub_le x y)
              _ = ‖x‖ + ∫ y, ‖y‖ ∂(ρ s) := by
                  have hρs : ρ s = spatialMarginal (f s) := rfl
                  haveI : IsProbabilityMeasure (ρ s) := hρs ▸ inferInstance
                  have h_y_int_ρ : Integrable (fun y => ‖y‖) (ρ s) := hρs ▸ h_y_int s hs
                  rw [integral_add (integrable_const _) h_y_int_ρ, integral_const]
                  simp [measureReal_def]
              _ ≤ ‖x‖ + M_ρ := by linarith [hM_ρ s hs]
          simp only [hε₀_def]
          linarith [mul_le_mul_of_nonneg_left h_int_le (NNReal.coe_nonneg L)]
  -- Growth bound: ‖(charX t z, charV t z)‖ ≤ C_T * (‖z‖ + 1) for t ∈ Icc 0 T
  set C_T := gronwallBound 1 K ε₀ T with hC_T_def
  have hC_T_nn : 0 ≤ C_T := by
    have hmono := gronwallBound_mono (by norm_num : (0:ℝ) ≤ 1) hε₀_nn hK_pos.le hT
    linarith [gronwallBound_x0 1 K ε₀]
  have h_flow_bound : ∀ t ∈ Set.Icc 0 T, ∀ z : PhaseSpace d,
      ‖(charX t z, charV t z)‖ ≤ C_T * (‖z‖ + 1) := by
    intro t ht z
    have h_f_cont : ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc 0 T) :=
      continuousOn_of_forall_continuousAt fun s _ =>
        (hflow_x s z).continuousAt.prodMk (hflow_v s z).continuousAt
    have h_deriv : ∀ s ∈ Set.Ico 0 T,
        HasDerivWithinAt (fun s => (charX s z, charV s z))
          (charV s z, -convolveFunctionMeasure gradW (ρ s) (charX s z)) (Set.Ici s) s :=
      fun s _ => ((hflow_x s z).prodMk (hflow_v s z)).hasDerivWithinAt
    have h_init : ‖(charX 0 z, charV 0 z)‖ ≤ ‖z‖ := by
      obtain ⟨hx0, hv0⟩ := hflow_init z
      simp [hx0, hv0, Prod.norm_def]
    have h_bound : ∀ s ∈ Set.Ico 0 T,
        ‖(charV s z, -convolveFunctionMeasure gradW (ρ s) (charX s z))‖ ≤
          K * ‖(charX s z, charV s z)‖ + ε₀ := by
      intro s hs
      have hs_mem : s ∈ Set.Icc 0 T := ⟨hs.1, le_of_lt hs.2⟩
      simp only [Prod.norm_def, norm_neg]
      have hFsz := le_max_left ‖charX s z‖ ‖charV s z‖
      have hGsz := le_max_right ‖charX s z‖ ‖charV s z‖
      have hM_nn : 0 ≤ max ‖charX s z‖ ‖charV s z‖ :=
        le_max_iff.mpr (Or.inl (norm_nonneg _))
      have h_v_le : ‖charV s z‖ ≤ K * max ‖charX s z‖ ‖charV s z‖ + ε₀ :=
        calc ‖charV s z‖ ≤ max ‖charX s z‖ ‖charV s z‖ := hGsz
          _ ≤ K * max ‖charX s z‖ ‖charV s z‖ :=
              le_mul_of_one_le_left hM_nn (by linarith [NNReal.coe_nonneg L])
          _ ≤ K * max ‖charX s z‖ ‖charV s z‖ + ε₀ := le_add_of_nonneg_right hε₀_nn
      have h_conv_le : ‖convolveFunctionMeasure gradW (ρ s) (charX s z)‖ ≤
          K * max ‖charX s z‖ ‖charV s z‖ + ε₀ :=
        calc ‖convolveFunctionMeasure gradW (ρ s) (charX s z)‖
            ≤ ε₀ + (L : ℝ) * ‖charX s z‖ := h_conv_bound s hs_mem _
          _ ≤ ε₀ + K * max ‖charX s z‖ ‖charV s z‖ := by
              have hLK : (L : ℝ) ≤ K := le_add_of_nonneg_left zero_le_one
              linarith [mul_le_mul_of_nonneg_left hFsz (NNReal.coe_nonneg L),
                        mul_le_mul_of_nonneg_right hLK hM_nn]
          _ = K * max ‖charX s z‖ ‖charV s z‖ + ε₀ := by ring
      exact max_le h_v_le h_conv_le
    have h_grw := norm_le_gronwallBound_of_norm_deriv_right_le
      h_f_cont h_deriv h_init h_bound t ht
    simp only [sub_zero] at h_grw
    calc ‖(charX t z, charV t z)‖
        ≤ gronwallBound ‖z‖ K ε₀ t := h_grw
      _ ≤ gronwallBound ‖z‖ K ε₀ T :=
          gronwallBound_mono (norm_nonneg _) hε₀_nn hK_pos.le ht.2
      _ ≤ gronwallBound 1 K ε₀ T * (‖z‖ + 1) := by
          rw [gronwallBound_of_K_ne_0 hK_pos.ne', gronwallBound_of_K_ne_0 hK_pos.ne']
          simp only [one_mul]
          have he1 : 0 ≤ Real.exp (K * T) - 1 :=
            by linarith [Real.one_le_exp (mul_nonneg hK_pos.le hT)]
          have hεK := div_nonneg hε₀_nn hK_pos.le
          nlinarith [norm_nonneg z, Real.exp_nonneg (K * T),
            mul_nonneg hεK he1, mul_nonneg (norm_nonneg z) (mul_nonneg hεK he1)]
  -- Step 4: Apply continuousOn_of_dominated
  rw [show (fun t => ∫ z, φ z ∂(f t)) = (fun t => ∫ z, φ (charX t z, charV t z) ∂(f 0)) from
    funext h_rw]
  apply continuousOn_of_dominated (bound := fun z => ‖φ 0‖ + C_T * (‖z‖ + 1))
  · -- AEStronglyMeasurable
    intro t _
    exact hφ_lip.continuous.measurable.aestronglyMeasurable.comp_aemeasurable (hflow_meas t)
  · -- Uniform bound
    intro t ht
    apply Filter.Eventually.of_forall
    intro z
    have h_lip_bound : ‖φ (charX t z, charV t z)‖ ≤ ‖φ 0‖ + ‖(charX t z, charV t z)‖ := by
      have hd := hφ_lip.dist_le_mul (charX t z, charV t z) 0
      simp only [dist_eq_norm, NNReal.coe_one, one_mul, sub_zero] at hd
      have htri : ‖φ (charX t z, charV t z)‖ ≤ ‖φ (charX t z, charV t z) - φ 0‖ + ‖φ 0‖ := by
        have := norm_add_le (φ (charX t z, charV t z) - φ 0) (φ 0)
        simp only [sub_add_cancel] at this; linarith
      linarith
    linarith [h_flow_bound t ht z]
  · -- Integrable dominator
    haveI : IsProbabilityMeasure (f 0) := hf_prob_0.1
    have h_int_norm : Integrable (fun z : PhaseSpace d => ‖z‖) (f 0) := hf_prob_0.2
    have h_int_1 : Integrable (fun _ : PhaseSpace d => (1 : ℝ)) (f 0) :=
      integrable_const 1
    have h_int_norm1 : Integrable (fun z : PhaseSpace d => ‖z‖ + 1) (f 0) :=
      h_int_norm.add h_int_1
    exact (integrable_const ‖φ 0‖).add (h_int_norm1.const_mul C_T)
  · -- Pointwise continuity
    apply Filter.Eventually.of_forall
    intro z
    apply ContinuousOn.comp hφ_lip.continuous.continuousOn
    · exact continuousOn_of_forall_continuousAt fun s _ =>
        (hflow_x s z).continuousAt.prodMk (hflow_v s z).continuousAt
    · exact fun _ _ => Set.mem_univ _

/-- Given per-1-Lipschitz LSC of each summand `t ↦ ENNReal.ofReal(∫φd(f t) - ∫φd(g t))`,
the Wasserstein-1 distance `wasserstein1 (f t) (g t) = ⨆ φ (_ : LipschitzWith 1 φ), …`
is LowerSemicontinuousOn `Set.Icc 0 T` as a double supremum of LSC functions
via `lowerSemicontinuousOn_iSup` applied twice. -/
lemma w1_lscNarrow_of_summands
    {d : ℕ}
    (f g : ℝ → Measure (PhaseSpace d))
    (T : ℝ)
    (h_summands : ∀ (φ : PhaseSpace d → ℝ) (_hφ : LipschitzWith 1 φ),
        LowerSemicontinuousOn
          (fun t => ENNReal.ofReal (∫ z, φ z ∂(f t) - ∫ z, φ z ∂(g t)))
          (Set.Icc 0 T)) :
    LowerSemicontinuousOn (fun t => wasserstein1 (f t) (g t)) (Set.Icc 0 T) := by
  simp only [wasserstein1_eq_iSup_lipschitz]
  exact lowerSemicontinuousOn_biSup (fun φ hφ => h_summands φ hφ)

/-- For a continuous function h : ℝ → ℝ on [0, T] with h(0) ≤ δ and with
right-derivative liminf bounded by C * h(s) for all s ∈ [0, T),
Gronwall's inequality gives h(t) ≤ δ * Real.exp(C * t) for all t ∈ [0, T].
This wraps Mathlib's `le_gronwallBound_of_liminf_deriv_right_le` with ε = 0
and then simplifies via `gronwallBound_ε0`. -/
lemma wassersteinGronwallCoupling_gronwall_le
    (h : ℝ → ℝ) (δ C T : ℝ) (_hT : 0 ≤ T)
    (hcont : ContinuousOn h (Set.Icc 0 T))
    (hinit : h 0 ≤ δ)
    (hderiv : ∀ s ∈ Set.Ico 0 T, ∀ r : ℝ, C * h s < r →
        ∃ᶠ z in nhdsWithin s (Set.Ioi s), (z - s)⁻¹ * (h z - h s) < r) :
    ∀ t ∈ Set.Icc 0 T, h t ≤ δ * Real.exp (C * t) := by
  intro t ht
  have key := le_gronwallBound_of_liminf_deriv_right_le
    (f := h) (f' := fun s => C * h s)
    (δ := δ) (K := C) (ε := 0) (a := 0) (b := T)
    hcont hderiv hinit (fun _ _ => by linarith) t ht
  rwa [sub_zero, gronwallBound_ε0] at key

/-- **Scalar mild-form Gronwall**: a continuous nonnegative `Q` satisfying the
*integral* inequality `Q t ≤ q0 + K · ∫₀ᵗ Q` on `[0, T]` obeys
`Q t ≤ q0 · exp (K t)`.

This is the mild-form companion to `wassersteinGronwallCoupling_gronwall_le`
(which takes the Dini/right-derivative form).  The integrated coupling-Gronwall
bound produces `Q(t) = ∫‖Φ_f t · − Φ_g t ·‖ dπ₀` in the *integral* form (via
per-trajectory FTC + Tonelli on a nonnegative integrand), sidestepping the
reverse-Fatou difference-quotient interchange.  Proof: apply Mathlib's
`norm_le_gronwallBound_of_norm_deriv_right_le` to the C¹ primitive
`G t = q0 + K · ∫₀ᵗ Q` (with `G' t = K · Q t ≤ K · G t` since `Q ≤ G`), then
`Q ≤ G`. -/
lemma gronwall_mild_le (Q : ℝ → ℝ) (q0 K T : ℝ) (hK : 0 ≤ K) (hq0 : 0 ≤ q0)
    (hQcont : Continuous Q) (hQnn : ∀ t, 0 ≤ Q t)
    (hmild : ∀ t ∈ Set.Icc 0 T, Q t ≤ q0 + K * ∫ s in (0 : ℝ)..t, Q s) :
    ∀ t ∈ Set.Icc 0 T, Q t ≤ q0 * Real.exp (K * t) := by
  set G : ℝ → ℝ := fun t => q0 + K * ∫ s in (0:ℝ)..t, Q s with hGdef
  have hG_deriv : ∀ t, HasDerivAt G (K * Q t) t := by
    intro t
    have hftc : HasDerivAt (fun u => ∫ s in (0:ℝ)..u, Q s) (Q t) t :=
      intervalIntegral.integral_hasDerivAt_right
        (hQcont.intervalIntegrable 0 t)
        (hQcont.stronglyMeasurableAtFilter _ _) hQcont.continuousAt
    exact (hftc.const_mul K).const_add q0
  have hG_cont : Continuous G :=
    continuous_iff_continuousAt.mpr fun t => (hG_deriv t).continuousAt
  have hG_nonneg : ∀ t ∈ Set.Icc 0 T, 0 ≤ G t := by
    intro t ht
    have hint : 0 ≤ ∫ s in (0:ℝ)..t, Q s :=
      intervalIntegral.integral_nonneg ht.1 (fun s _ => hQnn s)
    change 0 ≤ q0 + K * ∫ s in (0 : ℝ)..t, Q s
    positivity
  have hG0 : G 0 = q0 := by simp [hGdef]
  intro t ht
  have hgb := norm_le_gronwallBound_of_norm_deriv_right_le
    (f := G) (a := 0) (b := T) hG_cont.continuousOn
    (fun s _ => (hG_deriv s).hasDerivWithinAt)
    (show ‖G 0‖ ≤ q0 by rw [hG0, Real.norm_eq_abs, abs_of_nonneg hq0])
    (fun s hs => by
      have hsI : s ∈ Set.Icc 0 T := ⟨hs.1, hs.2.le⟩
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK (hQnn s)),
          Real.norm_eq_abs, abs_of_nonneg (hG_nonneg s hsI), add_zero]
      have hQG : Q s ≤ G s := hmild s hsI
      nlinarith [hQnn s, hG_nonneg s hsI])
    t ht
  rw [sub_zero, gronwallBound_ε0, Real.norm_eq_abs, abs_of_nonneg (hG_nonneg t ht)] at hgb
  exact le_trans (hmild t ht) hgb

-- `wassersteinGronwallCoupling_real_bound` lives in
-- `LeanPool/Vlasov/OT/CharacteristicFlow.lean` §10, where it composes with the
-- CharFlow-resident W₁-continuity machinery and the
-- `wassersteinGronwallCoupling_gronwall_le` helper above.

/-- For reals δ ≥ 0 and C > 0 and t ≥ 0, if r ≤ δ * Real.exp(C * t) then
ENNReal.ofReal r ≤ ENNReal.ofReal (Real.exp (C * t)) * ENNReal.ofReal δ.
Uses ENNReal.ofReal_mul and mul_comm to reorder the product. -/
lemma wassersteinGronwallCoupling_ennreal_mul_comm
    (δ : ℝ) (hδ : 0 ≤ δ) (C t : ℝ) :
    ENNReal.ofReal (δ * Real.exp (C * t)) =
      ENNReal.ofReal (Real.exp (C * t)) * ENNReal.ofReal δ := by
  rw [ENNReal.ofReal_mul hδ, mul_comm]

omit [NeZero d] in
/-- If gradW is L-Lipschitz, then for any x : PhysSpace d and any two measures ρ, σ
on PhysSpace d, ‖(∇W*ρ)(x) − (∇W*σ)(x)‖ ≤ L · W₁(ρ,σ).toReal.
This is the key estimate: the convolution ∇W * ρ is Lipschitz in ρ with respect to
the Wasserstein-1 distance, via Kantorovich–Rubinstein duality.
A thin wrapper around `norm_convolveFunctionMeasure_sub_le`. -/
lemma convolveDiff_norm_le
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ σ : Measure (PhysSpace d))
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure σ]
    (x : PhysSpace d)
    (hW : wasserstein1 ρ σ ≠ ⊤)
    (hρ_int : Integrable (fun y => gradW (x - y)) ρ)
    (hσ_int : Integrable (fun y => gradW (x - y)) σ) :
    ‖convolveFunctionMeasure gradW ρ x - convolveFunctionMeasure gradW σ x‖ ≤
      (L : ℝ) * (wasserstein1 ρ σ).toReal :=
  norm_convolveFunctionMeasure_sub_le gradW L hL ρ σ x hW hρ_int hσ_int

/-- (tex: eq:dobrushin)
The exponential Wasserstein-1 stability estimate for Vlasov solutions
(the content of Theorem thm:dobrushin):

  W_1(f_t, g_t) ≤ e^{C·t} · W_1(f_0, g_0),   for all t ≥ 0.

This `Prop`-valued definition packages the statement as a reusable predicate.
-/
def DobrushinStabilityEstimate
    (f g : ℝ → Measure (PhaseSpace d))
    (C : ℝ) : Prop :=
  ∀ t : ℝ, 0 ≤ t →
    wasserstein1 (f t) (g t) ≤
      ENNReal.ofReal (Real.exp (C * t)) * wasserstein1 (f 0) (g 0)

/-! ## §13 Corollary (Mean-field limit)  (`tex: cor:mfl`) -/

omit [NeZero d] in
/-- (tex: cor:mfl)
Mean-field limit theorem.

Let f_0 ∈ 𝒫_1(ℝ^d × ℝ^d) and let (X^N, V^N) be the N-particle Newton
trajectories.  Write μ_0^N for the initial empirical measure of (X^N(0),
V^N(0)).  If μ_0^N → f_0 in W_1 as N → ∞ then, under Assumption ass:W and
the Dobrushin estimate, for every T > 0,

  sup_{t ∈ [0,T]} W_1(μ_t^N, f_t) ≤ e^{C·T} · W_1(μ_0^N, f_0)  →  0,  as N → ∞.

f_t is the unique Vlasov solution with initial datum f_0 (Theorem thm:vlasov-wp).
The .tex names the initial data `(X_0^N, V_0^N)`; here we identify them with
`X N 0` and `V N 0` rather than introducing redundant `X₀, V₀` parameters
that would need a separate hypothesis to link them to the trajectory.
-/
theorem meanFieldLimit
    (W : PhysSpace d → ℝ)
    (gradW : PhysSpace d → PhysSpace d)
    (_hgradW : ∀ x, gradW x = gradient W x)
    (L : NNReal) (_hL : LipschitzWith L gradW)
    -- the Vlasov solution with initial datum f₀
    (f₀ : Measure (PhaseSpace d)) (_hf₀ : HasFiniteFirstMoment f₀)
    (f : ℝ → Measure (PhaseSpace d))
    (_hf_sol : IsLagrangianVlasovSolution gradW f)
    (hf_init : f 0 = f₀)
    -- N-particle Newton trajectories; initial data is `(X N 0, V N 0)`.
    (X V : (N : ℕ) → ℝ → Fin N → PhysSpace d)
    (_hSol : ∀ (N : ℕ), IsNewtonSolution N gradW (X N) (V N))
    -- initial empirical measures converge to f₀ in W_1
    (hInit : Filter.Tendsto
      (fun N : ℕ => wasserstein1 (empiricalMeasure N (X N 0) (V N 0)) f₀)
      Filter.atTop (nhds 0))
    -- the Dobrushin constant C from Theorem thm:dobrushin
    (C : ℝ) (hC : 0 < C)
    (hDobrushin : ∀ (N : ℕ), DobrushinStabilityEstimate
      (empiricalMeasureCurve N (X N) (V N)) f C)
    (T : ℝ) (_hT : 0 < T) :
    Filter.Tendsto
      (fun N : ℕ => ⨆ t ∈ Set.Icc 0 T,
        wasserstein1 (empiricalMeasureCurve N (X N) (V N) t) (f t))
      Filter.atTop (nhds 0) := by
  -- (1) hsup_bound: for each N, the sup over t ∈ [0,T] is bounded by
  --     exp(C·T) · W_1(μ_0^N, f_0).  Uses hDobrushin pointwise then
  --     monotonicity of exp to lift `t` to the upper endpoint T.
  have hsup_bound : ∀ N : ℕ,
      ⨆ t ∈ Set.Icc 0 T, wasserstein1 (empiricalMeasureCurve N (X N) (V N) t) (f t) ≤
        ENNReal.ofReal (Real.exp (C * T)) *
          wasserstein1 (empiricalMeasureCurve N (X N) (V N) 0) (f 0) := by
    intro N
    apply iSup_le; intro t
    apply iSup_le; intro ht
    calc wasserstein1 (empiricalMeasureCurve N (X N) (V N) t) (f t)
        ≤ ENNReal.ofReal (Real.exp (C * t)) *
            wasserstein1 (empiricalMeasureCurve N (X N) (V N) 0) (f 0) :=
          hDobrushin N t ht.1
      _ ≤ ENNReal.ofReal (Real.exp (C * T)) *
            wasserstein1 (empiricalMeasureCurve N (X N) (V N) 0) (f 0) := by
          apply mul_le_mul_of_nonneg_right _ (zero_le)
          apply ENNReal.ofReal_le_ofReal
          exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 (le_of_lt hC))
  -- (2) hUpper: the upper-bound sequence tends to 0.  Apply
  --     ENNReal.Tendsto.const_mul to hInit; the witness for `a ≠ ∞` is
  --     `ENNReal.ofReal_ne_top`.  Rewrite empiricalMeasureCurve at t=0
  --     to expose hInit's empiricalMeasure form, and use hf_init to
  --     align f 0 with f₀.
  have hUpper : Filter.Tendsto
      (fun N : ℕ => ENNReal.ofReal (Real.exp (C * T)) *
        wasserstein1 (empiricalMeasureCurve N (X N) (V N) 0) (f 0))
      Filter.atTop (nhds 0) := by
    have h := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (Real.exp (C * T)))
      hInit (Or.inr ENNReal.ofReal_ne_top)
    simpa [empiricalMeasureCurve, hf_init, mul_zero] using h
  -- (3) Squeeze: 0 ≤ sup ≤ upper-bound → 0.
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hUpper
    (fun _ => zero_le) hsup_bound

end Vlasov
