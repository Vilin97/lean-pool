/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Existence.Perron.Basic
public import LeanPool.ViscositySolutionTheory.ViscositySolns.Comparison.ProperComparison.Compact.ConstantShiftBoundary

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Dirichlet comparison for the Laplace operator

The Laplace operator `F(x,r,p,X) = - trace X` is proper but has no strict
monotonicity in the scalar variable, so the constant-shift comparison adapter
does not apply to it directly. Instead we strictify a subsolution `u` by adding
the quadratic penalty `η (|y|² - K)`, whose Hessian `2η I` makes
`u + η (|y|² - K)` a strict subsolution with strictness `2 η n`. Choosing `K`
so that the penalty is at most `-η` on the compact closure keeps the boundary
inequality, and letting `η → 0` gives the comparison principle.

In dimension zero the principle fails (every function is a solution and the
boundary is empty), so the positive-dimension hypothesis is necessary.
-/

@[expose] public noncomputable section

namespace ViscositySolns

variable {n : Nat}

open scoped MatrixOrder

/-- The Laplace operator `F(x,r,p,X) = - trace X`, i.e. the equation `-Δu = 0`. -/
def laplaceOperator : Operator n :=
  traceSecondOrderOperator (fun _ => 1) (fun _ => 0) (fun _ => 0) (fun _ => 0)

@[simp]
theorem laplaceOperator_apply (x : Point n) (r : Real) (p : Point n) (X : Hessian n) :
    laplaceOperator x r p X = -Matrix.trace X := by
  simp [laplaceOperator]

theorem proper_laplaceOperator : Proper (laplaceOperator (n := n)) :=
  proper_traceSecondOrderOperator_of_posSemidef
    (fun _ => Matrix.PosSemidef.one) (fun _ => le_rfl)

theorem degenerateElliptic_laplaceOperator : DegenerateElliptic (laplaceOperator (n := n)) :=
  degenerateElliptic_traceSecondOrderOperator_of_posSemidef fun _ => Matrix.PosSemidef.one

theorem operatorContinuous_laplaceOperator : OperatorContinuous (laplaceOperator (n := n)) := by
  apply operatorContinuous_traceSecondOrderOperator
  · simp only [one_mul]
    exact (Jet.continuous_hessian.comp continuous_snd).matrix_trace.neg
  · simp only [zero_dotProduct]
    exact continuous_const
  · simp only [zero_mul]
    exact continuous_const
  · exact continuous_const

theorem ishiiOperatorComparisonConditionOn_laplaceOperator (C : Set (Point n))
    (R : Set Real) : IshiiOperatorComparisonConditionOn C R (laplaceOperator (n := n)) := by
  apply ishiiOperatorComparisonConditionOn_traceSecondOrderOperator_of_same_hessian_bound
    comparisonModulus_zero (fun _ _ => Matrix.PosSemidef.one)
  intro α hα x hx y hy r hr X Y hXY
  simp

/-- The Laplace operator is invariant under the sign duality `negOperator`. -/
theorem negOperator_laplaceOperator : negOperator (laplaceOperator (n := n)) = laplaceOperator := by
  funext x r p X
  simp [negOperator, Matrix.trace_neg]

/-- The strictifying penalty `y ↦ η (|y|² - K)`, written as a quadratic model. -/
def laplacePenalty (η K : Real) : Point n -> Real :=
  fun y => quadraticModel 0 (-(η * K)) 0 ((2 * η) • (1 : Hessian n)) y

theorem laplacePenalty_apply (η K : Real) (y : Point n) :
    laplacePenalty η K y = η * (dotProduct y y - K) := by
  simp only [laplacePenalty, quadraticModel, sub_zero, zero_dotProduct, add_zero,
    Matrix.smul_mulVec, Matrix.one_mulVec, smul_dotProduct, smul_eq_mul]
  ring

theorem continuous_laplacePenalty (η K : Real) :
    Continuous (laplacePenalty (n := n) η K) :=
  continuous_quadraticModel _ _ _ _

/--
Adding the penalty `η (|y|² - K)` to a subsolution of `-Δu = 0` produces a
strict subsolution: every superjet `(p, X)` satisfies `- trace X ≤ - 2 η n`.
-/
theorem ViscositySubsolution.strict_add_laplacePenalty
    {C : Set (Point n)} {u : Point n -> Real}
    (hu : ViscositySubsolution C laplaceOperator u) (η K : Real) :
    StrictViscositySubsolution C laplaceOperator (2 * η * n)
      (fun y => u y + laplacePenalty η K y) := by
  refine ⟨hu.1.add (continuous_laplacePenalty η K).continuousOn.upperSemicontinuousOn, ?_⟩
  intro x hx J hJ
  have hJu : J - quadraticModelJetAt 0 0 ((2 * η) • (1 : Hessian n)) x ∈ Superjet C u x :=
    superjet_sub_of_add_hasSecondOrderExpansionWithin hJ
      (hasSecondOrderExpansionWithin_quadraticModel_recenter 0 (-(η * K)) 0 _ x)
  have h := hu.2 x hx _ hJu
  simp only [laplaceOperator_apply, Jet.sub_hessian, quadraticModelJetAt,
    Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin,
    smul_eq_mul] at h
  simp only [laplaceOperator_apply]
  linarith

/--
Dirichlet comparison for the Laplace operator on a domain with compact closure
in positive dimension, with the topological frontier as the Dirichlet boundary.
-/
theorem dirichletComparisonPrinciple_laplaceOperator (hn : 0 < n)
    {C : Set (Point n)} [LocallyCompactSpace C] (hCcompact : CompactClosure C)
    (g : Point n -> Real) :
    DirichletComparisonPrinciple C (frontier C) laplaceOperator g := by
  intro u v hu hv x hx
  have hboundary : ∀ y ∈ frontier C, u y <= v y := fun y hy =>
    (hu.boundary_le hy).trans (hv.boundary_le hy)
  rcases hx with hxC | hxB
  swap
  · exact hboundary x hxB
  -- A bound for `|y|²` on the compact closure.
  obtain ⟨K₀, hK₀⟩ : ∃ K₀ : Real, ∀ y ∈ closure C, dotProduct y y <= K₀ := by
    obtain ⟨K₀, hK₀⟩ :=
      (hCcompact.isCompact_closure.image_of_continuousOn
        (continuous_id.dotProduct continuous_id).continuousOn).isBounded.bddAbove
    exact ⟨K₀, fun y hy => hK₀ ⟨y, hy, rfl⟩⟩
  set K : Real := max K₀ 0 + 1 with hKdef
  have hKpos : 0 < K := by positivity
  have hK : ∀ y ∈ closure C, dotProduct y y + 1 <= K := fun y hy => by
    have := hK₀ y hy
    have := le_max_left K₀ 0
    linarith
  have husc : UpperSemicontinuousOn u (closure C) := by
    simpa [closure_eq_self_union_frontier] using hu.upperSemicontinuousOn
  have hvlsc : LowerSemicontinuousOn v (closure C) := by
    simpa [closure_eq_self_union_frontier] using hv.lowerSemicontinuousOn
  have hnR : (0 : Real) < n := by exact_mod_cast hn
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set η : Real := ε / K with hηdef
  have hη : 0 < η := div_pos hε hKpos
  let w : Point n -> Real := fun y => u y + laplacePenalty η K y + η
  have hw : (fun y => w y - η) = fun y => u y + laplacePenalty η K y := by
    funext y
    simp only [w]
    ring
  have hwusc : UpperSemicontinuousOn (fun y => w y - η) (closure C) := by
    rw [hw]
    exact husc.add (continuous_laplacePenalty η K).continuousOn.upperSemicontinuousOn
  have hcompare := strictComparison_of_constantShift_boundary
    (C := C) (R := Set.univ) (F := laplaceOperator) (u := w) (v := v) (δ := η)
    (ε := 2 * η * n)
    (fun y hy => by
      have hyK := hK y (frontier_subset_closure hy)
      have hpen : laplacePenalty η K y + η <= 0 := by
        rw [laplacePenalty_apply]
        nlinarith
      have := hboundary y hy
      simp only [w]
      linarith)
    hη
    (by rw [hw]; exact hu.viscosity.strict_add_laplacePenalty η K)
    hv.viscosity operatorContinuous_laplaceOperator proper_laplaceOperator
    (ishiiOperatorComparisonConditionOn_laplaceOperator C Set.univ)
    (QuadraticPenaltyIshiiLemmaConstructorOn.of_localized_jensen_aleksandrov
      (JensenContactSetPositiveMeasureOnClosedBallTheorem.proof (n := n + n))
      (AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem.proof_external (n + n))
      _ v (hwusc.mono subset_closure) hv.viscosity.1)
    (by positivity)
    (fun _ _ => Set.mem_univ _)
    ⟨x, hxC⟩ hCcompact hwusc hvlsc
  have hx := hcompare x hxC
  simp only [w, laplacePenalty_apply] at hx
  have hxx : 0 <= dotProduct x x := by
    simpa [dotProduct, ← sq] using Finset.sum_nonneg fun i _ => sq_nonneg (x i)
  have hηK : η * K = ε := by
    rw [hηdef]
    field_simp
  nlinarith

end ViscositySolns
