/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.Core.TraceClassification

/-!
# The middle-game trace equation

This module gives the exact finite solution set for equation (41) and proves the elementary
quadratic-fiber bound used when one subgroup is small.  The genuinely deep uniform power-saving
estimate remains a separate Blueprint input.
-/

namespace BGS.Markoff

open Polynomial

variable {E : Type*} [Field E] [Fintype E]

/-- The twisted eigenvalue trace `h + sigma / h`. -/
noncomputable def twistedUnitTrace (sigma : E) (h : Eˣ) : E :=
  (h : E) + sigma * (h⁻¹ : Eˣ)

/-- The possible left-hand elements above one fixed right-hand trace. -/
noncomputable def traceEquationLeftFiber
    (sigma : E) (H₁ : Subgroup Eˣ) (h₂ : Eˣ) : Finset H₁ := by
  classical
  exact Finset.univ.filter fun h₁ =>
    twistedUnitTrace sigma h₁ = twistedUnitTrace 1 h₂

/-- Solutions of the middle-game trace equation inside two finite subgroups. -/
noncomputable def traceEquationSolutions
    (sigma : E) (H₁ H₂ : Subgroup Eˣ) : Finset (H₁ × H₂) := by
  classical
  exact Finset.univ.biUnion fun h₂ : H₂ =>
    (traceEquationLeftFiber sigma H₁ h₂).image fun h₁ => (h₁, h₂)

@[simp]
theorem mem_traceEquationSolutions_iff
    {sigma : E} {H₁ H₂ : Subgroup Eˣ} {h : H₁ × H₂} :
    h ∈ traceEquationSolutions sigma H₁ H₂ ↔
      twistedUnitTrace sigma h.1 = twistedUnitTrace 1 h.2 := by
  classical
  constructor
  · intro hh
    rw [traceEquationSolutions, Finset.mem_biUnion] at hh
    obtain ⟨h₂, _, hh⟩ := hh
    obtain ⟨h₁, hh₁, heq⟩ := Finset.mem_image.mp hh
    have hfirst : h₁ = h.1 := congrArg Prod.fst heq
    have hsecond : h₂ = h.2 := congrArg Prod.snd heq
    simpa [traceEquationLeftFiber, hfirst, hsecond] using hh₁
  · intro hh
    rw [traceEquationSolutions, Finset.mem_biUnion]
    refine ⟨h.2, Finset.mem_univ _, ?_⟩
    exact Finset.mem_image.mpr
      ⟨h.1, by simpa [traceEquationLeftFiber] using hh, rfl⟩

/-- After one trace value is fixed, the other unit satisfies a monic quadratic. -/
noncomputable def twistedTracePolynomial (sigma trace : E) : E[X] :=
  X ^ 2 - C trace * X + C sigma

omit [Fintype E] in
theorem twistedTracePolynomial_monic (sigma trace : E) :
    (twistedTracePolynomial sigma trace).Monic := by
  exact (isMonicOfDegree_sub_add_two trace sigma).monic

omit [Fintype E] in
@[simp]
theorem twistedTracePolynomial_natDegree (sigma trace : E) :
    (twistedTracePolynomial sigma trace).natDegree = 2 := by
  exact (isMonicOfDegree_sub_add_two trace sigma).natDegree_eq

omit [Fintype E] in
theorem eval_twistedTracePolynomial_eq_zero_iff
    (sigma trace : E) (h : Eˣ) :
    (twistedTracePolynomial sigma trace).eval (h : E) = 0 ↔
      twistedUnitTrace sigma h = trace := by
  have hh : (h : E) ≠ 0 := Units.ne_zero h
  simp only [twistedTracePolynomial, eval_add, eval_sub, eval_pow, eval_X, eval_mul,
    eval_C]
  rw [show twistedUnitTrace sigma h = (h : E) + sigma * (h : E)⁻¹ by
    simp [twistedUnitTrace]]
  constructor <;> intro heq
  · apply (mul_left_cancel₀ hh)
    field_simp [hh]
    linear_combination heq
  · field_simp [hh] at heq
    linear_combination heq

/-- For a fixed right-hand trace, at most two elements of the left subgroup solve the equation. -/
theorem traceEquationLeftFiber_card_le_two
    (sigma : E) (H₁ : Subgroup Eˣ) (h₂ : Eˣ) :
    (traceEquationLeftFiber sigma H₁ h₂).card ≤ 2 := by
  classical
  let f := twistedTracePolynomial sigma (twistedUnitTrace 1 h₂)
  have hf : f ≠ 0 := (twistedTracePolynomial_monic sigma _).ne_zero
  let rootEmbedding : ↥(traceEquationLeftFiber sigma H₁ h₂) ↪ ↥f.roots.toFinset :=
    { toFun := fun h₁ => ⟨((h₁.1 : Eˣ) : E), by
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hf]
        apply (eval_twistedTracePolynomial_eq_zero_iff sigma _ h₁.1).2
        simpa only [traceEquationLeftFiber, Finset.mem_filter, Finset.mem_univ, true_and]
          using h₁.2⟩
      inj' := by
        intro x y hxy
        apply Subtype.ext
        apply Subtype.ext
        apply Units.ext
        exact congrArg Subtype.val hxy }
  have hcard :
      (traceEquationLeftFiber sigma H₁ h₂).card ≤ f.roots.toFinset.card := by
    simpa only [Fintype.card_coe] using
      Fintype.card_le_of_injective rootEmbedding rootEmbedding.injective
  calc
    (traceEquationLeftFiber sigma H₁ h₂).card ≤ f.roots.toFinset.card := hcard
    _ ≤ f.roots.card := Multiset.toFinset_card_le _
    _ ≤ f.natDegree := Polynomial.card_roots' f
    _ = 2 := twistedTracePolynomial_natDegree sigma _

/-- The elementary bounded-right-subgroup estimate: every right element has at most two lifts. -/
theorem traceEquationSolutions_card_le_two_mul_right
    (sigma : E) (H₁ H₂ : Subgroup Eˣ) :
    (traceEquationSolutions sigma H₁ H₂).card ≤ 2 * Nat.card H₂ := by
  classical
  unfold traceEquationSolutions
  calc
    (Finset.univ.biUnion fun h₂ : H₂ =>
        (traceEquationLeftFiber sigma H₁ h₂).image fun h₁ => (h₁, h₂)).card ≤
        Finset.univ.card * 2 := by
      apply Finset.card_biUnion_le_card_mul
      intro h₂ _
      exact Finset.card_image_le.trans
        (traceEquationLeftFiber_card_le_two sigma H₁ h₂)
    _ = 2 * Nat.card H₂ := by
      rw [Finset.card_univ, Fintype.card_eq_nat_card]
      omega

end BGS.Markoff
