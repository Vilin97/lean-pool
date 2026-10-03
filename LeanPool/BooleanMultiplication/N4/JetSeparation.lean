/-
Copyright (c) 2026 Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Morse
-/
module

public import LeanPool.BooleanMultiplication.N4.Tail

/-!
# First-jet separation

This is the coordinate-linear heart of the manuscript's jet-separation
lemma.  Modulo the feedback state `S = ⟨E₀,E₁,E₆,r₁⟩`, a target has only
three coordinates `A E₂ + B E₃ + C E₄`.  One outside--outside coefficient
kills `C`; the four remaining outside slices force `A = B = 0` unless the
auxiliary two-plane is exactly the anchor plane.
-/

public section

namespace UnrestrictedBooleanMul
namespace N4

noncomputable section

/-- The plane spanned by the constant-coefficient inputs of the two polynomials. -/
@[expose]
def anchorPlane : Submodule F₂ LinearForm :=
  Submodule.span F₂ (Set.range ![aLinear 0, bLinear 0])

/-- The target subspace spanned by the first two coefficients, the last, and evaluation at one. -/
@[expose]
def feedbackCoeffSpace : Submodule F₂ TargetCoeff :=
  Submodule.span F₂
    (Set.range ![targetBasis 0, targetBasis 1,
      targetBasis 6, rOneCoeff])

/-- The second coefficient relative to the evaluation-at-one component. -/
@[expose] def jetA (c : TargetCoeff) : F₂ := c 2 + c 5
/-- The third coefficient relative to the evaluation-at-one component. -/
@[expose] def jetB (c : TargetCoeff) : F₂ := c 3 + c 5
/-- The fourth coefficient relative to the evaluation-at-one component. -/
@[expose] def jetC (c : TargetCoeff) : F₂ := c 4 + c 5

/-- The feedback-subspace component in the chosen target decomposition. -/
def feedbackBasePart (c : TargetCoeff) : TargetCoeff :=
  (c 0 + c 5) • targetBasis 0 +
    (c 1 + c 5) • targetBasis 1 +
    (c 6 + c 5) • targetBasis 6 +
    c 5 • rOneCoeff

/-- The three remaining target coordinates after removing the feedback component. -/
@[expose]
def jetResidualCoeff (c : TargetCoeff) : TargetCoeff :=
  jetA c • targetBasis 2 + jetB c • targetBasis 3 +
    jetC c • targetBasis 4

theorem feedback_decomposition (c : TargetCoeff) :
    c = feedbackBasePart c + jetResidualCoeff c := by
  funext i
  fin_cases i <;>
    simp [feedbackBasePart, jetResidualCoeff, jetA, jetB, jetC, targetBasis_apply]
  all_goals ring_nf
  all_goals simp [N3Certificate.two_eq_zero_f2]

theorem feedbackBasePart_mem (c : TargetCoeff) :
    feedbackBasePart c ∈ feedbackCoeffSpace := by
  apply Submodule.add_mem
  · apply Submodule.add_mem
    · apply Submodule.add_mem
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, by simp⟩)
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, by simp⟩)
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨2, by simp⟩)
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨3, by simp⟩)

theorem anchorPlane_linearIndependent :
    LinearIndependent F₂ ![aLinear 0, bLinear 0] := by
  rw [Fintype.linearIndependent_iff]
  intro f h i
  have hc := congrFun h (if i = 0 then aCoord 0 else bCoord 0)
  fin_cases i <;>
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, aLinear, Pi.basisFun, aCoord, Fin.isValue,
      Fin.coe_ofNat_eq_mod, Nat.zero_mod, Fin.zero_eta, Module.Basis.coe_ofEquivFun,
      LinearEquiv.refl_symm, LinearEquiv.refl_apply, bLinear, bCoord, add_zero,
      Fin.reduceFinMk, ↓reduceIte, Finset.sum_apply, Pi.smul_apply, Matrix.cons_val',
      Pi.single_eq_same, ne_eq, Fin.reduceEq, not_false_eq_true, Pi.single_eq_of_ne,
      Matrix.cons_val_fin_one, smul_eq_mul, Fin.sum_univ_succ, Matrix.cons_val_zero, mul_one,
      Finset.univ_unique, Fin.default_eq_zero, Matrix.cons_val_succ, mul_zero,
      Finset.sum_const_zero, Pi.zero_apply, Fin.mk_one, one_ne_zero, Finset.sum_singleton,
      Fin.succ_zero_eq_one, zero_add] at hc ⊢
  · exact hc
  · exact hc

theorem anchorPlane_finrank : Module.finrank F₂ anchorPlane = 2 := by
  exact finrank_span_eq_card anchorPlane_linearIndependent

theorem anchorPlane_le_of_generators_mem {U : Submodule F₂ LinearForm}
    (hx : aLinear 0 ∈ U) (hy : bLinear 0 ∈ U) : anchorPlane ≤ U := by
  rw [anchorPlane, Submodule.span_le]
  rintro u ⟨i, rfl⟩
  fin_cases i
  · exact hx
  · exact hy

theorem submodule_eq_anchorPlane_of_generators_mem
    {U : Submodule F₂ LinearForm}
    (hUdim : Module.finrank F₂ U ≤ 2)
    (hx : aLinear 0 ∈ U) (hy : bLinear 0 ∈ U) : U = anchorPlane := by
  have hle := anchorPlane_le_of_generators_mem hx hy
  have hdim : Module.finrank F₂ U ≤ Module.finrank F₂ anchorPlane := by
    simpa [anchorPlane_finrank] using hUdim
  exact (Submodule.eq_of_le_of_finrank_le hle hdim).symm

/-- The second first-input slice of the residual jet coefficients. -/
@[expose] def jetSliceA2 (c : TargetCoeff) : LinearForm :=
  jetA c • bLinear 0 + jetB c • bLinear 1

/-- The third first-input slice of the residual jet coefficients. -/
@[expose] def jetSliceA3 (c : TargetCoeff) : LinearForm :=
  jetB c • bLinear 0

/-- The second second-input slice of the residual jet coefficients. -/
@[expose] def jetSliceB2 (c : TargetCoeff) : LinearForm :=
  jetA c • aLinear 0 + jetB c • aLinear 1

/-- The third second-input slice of the residual jet coefficients. -/
@[expose] def jetSliceB3 (c : TargetCoeff) : LinearForm :=
  jetB c • aLinear 0

/-- Jet separation in the exact algebraic interface used later: the
outside--outside part vanishes and all four outside slice vectors lie in a
subspace of dimension at most two different from the anchor plane. -/
theorem jet_separation
    (U : Submodule F₂ LinearForm)
    (hUdim : Module.finrank F₂ U ≤ 2)
    (hUne : U ≠ anchorPlane)
    (c : TargetCoeff)
    (hOutside :
      targetTwo (jetResidualCoeff c) (aCoord 2) (bCoord 2) = 0)
    (hA2 : jetSliceA2 c ∈ U)
    (hA3 : jetSliceA3 c ∈ U)
    (hB2 : jetSliceB2 c ∈ U)
    (hB3 : jetSliceB3 c ∈ U) :
    c ∈ feedbackCoeffSpace := by
  have hC : jetC c = 0 := by
    simpa [jetResidualCoeff, jetC, jetA, jetB, targetTwo_cross, targetBasis, Pi.basisFun
      ] using hOutside
  have hB : jetB c = 0 := by
    rcases f2_eq_zero_or_one (jetB c) with hB | hB
    · exact hB
    · exfalso
      have hy : bLinear 0 ∈ U := by
        simpa [jetSliceA3, hB] using hA3
      have hx : aLinear 0 ∈ U := by
        simpa [jetSliceB3, hB] using hB3
      exact hUne (submodule_eq_anchorPlane_of_generators_mem hUdim hx hy)
  have hA : jetA c = 0 := by
    rcases f2_eq_zero_or_one (jetA c) with hA | hA
    · exact hA
    · exfalso
      have hy : bLinear 0 ∈ U := by
        simpa [jetSliceA2, hA, hB] using hA2
      have hx : aLinear 0 ∈ U := by
        simpa [jetSliceB2, hA, hB] using hB2
      exact hUne (submodule_eq_anchorPlane_of_generators_mem hUdim hx hy)
  have hres : jetResidualCoeff c = 0 := by
    funext i
    fin_cases i <;>
      simp [jetResidualCoeff, hA, hB, hC]
  have hdecomp := feedback_decomposition c
  rw [hres, add_zero] at hdecomp
  rw [hdecomp]
  exact feedbackBasePart_mem c

end

end N4
end UnrestrictedBooleanMul
