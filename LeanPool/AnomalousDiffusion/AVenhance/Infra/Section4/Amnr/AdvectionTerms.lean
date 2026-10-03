/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.CenteredJets

/-! Explicit finite monomials for noncommuting material-power corrections. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

/-- One actual velocity-component jet, including its precise operator word. -/
abbrev AmnrAdvectionFactor := Fin 2 × List (Option (Fin 2))

/-- A monomial in fast-velocity jets, ending in one actual scalar jet. -/
structure AmnrAdvectionTerm where
  /-- Velocity factors, each carrying its component and derivative word. -/
  factors : List AmnrAdvectionFactor
  /-- Derivative word applied to the scalar factor of the advection term. -/
  scalarWord : List (Option (Fin 2))

/-- The actual product of the prescribed velocity jets. -/
def amnrAdvectionProduct (c : AmnrSpace → Vec 2) (v : Fin 2 → AmnrSpace → ℝ) :
    List AmnrAdvectionFactor → AmnrSpace → ℝ
  | [] => 1
  | a :: A => amnrWord c a.2 (v a.1) * amnrAdvectionProduct c v A

/-- Actual evaluation of the finite correction monomial. -/
def amnrAdvectionTermValue (c : AmnrSpace → Vec 2) (v : Fin 2 → AmnrSpace → ℝ)
    (f : AmnrSpace → ℝ) (t : AmnrAdvectionTerm) : AmnrSpace → ℝ :=
  amnrAdvectionProduct c v t.factors * amnrWord c t.scalarWord f

/-- Prepending a genuine velocity factor. -/
def amnrAdvectionTermPrepend (a : AmnrAdvectionFactor) (t : AmnrAdvectionTerm) : AmnrAdvectionTerm
    :=
  ⟨a :: t.factors, t.scalarWord⟩

/-- Exact Leibniz terms for one spatial or coarse-material differentiation.
The operator order is retained in every factor and in the final scalar jet. -/
def amnrAdvectionDerivativeTerms (d : Option (Fin 2)) :
    List AmnrAdvectionFactor → List (Option (Fin 2)) → List AmnrAdvectionTerm
  | [], w => [⟨[], d :: w⟩]
  | a :: A, w => ⟨(a.1, d :: a.2) :: A, w⟩ ::
      (amnrAdvectionDerivativeTerms d A w).map (amnrAdvectionTermPrepend a)

/-- Every actual factor product is smooth from its primitive fields. -/
theorem amnrAdvectionProduct_contDiff {c : AmnrSpace → Vec 2}
    {v : Fin 2 → AmnrSpace → ℝ} (hc : ContDiff ℝ (⊤ : ℕ∞) c)
    (hv : ∀ p, ContDiff ℝ (⊤ : ℕ∞) (v p)) (A : List AmnrAdvectionFactor) :
    ContDiff ℝ (⊤ : ℕ∞) (amnrAdvectionProduct c v A) := by
  induction A with
  | nil => exact contDiff_const
  | cons a A ih =>
    exact (contDiffOn_univ.mp (amnrWord_contDiffOn_infty isOpen_univ hc.contDiffOn
      (hv a.1).contDiffOn a.2)).mul ih

theorem amnrAdvectionTermValue_contDiff {c : AmnrSpace → Vec 2}
    {v : Fin 2 → AmnrSpace → ℝ} {f : AmnrSpace → ℝ} (hc : ContDiff ℝ (⊤ : ℕ∞) c)
    (hv : ∀ p, ContDiff ℝ (⊤ : ℕ∞) (v p)) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : AmnrAdvectionTerm) : ContDiff ℝ (⊤ : ℕ∞) (amnrAdvectionTermValue c v f t) :=
  (amnrAdvectionProduct_contDiff hc hv t.factors).mul
    (contDiffOn_univ.mp (amnrWord_contDiffOn_infty isOpen_univ hc.contDiffOn hf.contDiffOn
        t.scalarWord))

/-- Prepending a factor is ordinary multiplication of actual monomial values. -/
theorem amnrAdvectionTermValue_prepend (c : AmnrSpace → Vec 2)
    (v : Fin 2 → AmnrSpace → ℝ) (f : AmnrSpace → ℝ) (a : AmnrAdvectionFactor)
    (t : AmnrAdvectionTerm) (z : AmnrSpace) :
    amnrAdvectionTermValue c v f (amnrAdvectionTermPrepend a t) z =
      amnrWord c a.2 (v a.1) z * amnrAdvectionTermValue c v f t z := by
  dsimp [amnrAdvectionTermValue, amnrAdvectionTermPrepend, amnrAdvectionProduct]
  ring

/-- A factor distributes over the exact finite sum of correction monomials. -/
theorem amnrAdvectionTermValue_sum_prepend (c : AmnrSpace → Vec 2)
    (v : Fin 2 → AmnrSpace → ℝ) (f : AmnrSpace → ℝ) (a : AmnrAdvectionFactor)
    (T : List AmnrAdvectionTerm) (z : AmnrSpace) :
    ((T.map (amnrAdvectionTermPrepend a)).map (fun t => amnrAdvectionTermValue c v f t z)).sum =
      amnrWord c a.2 (v a.1) z * (T.map (fun t => amnrAdvectionTermValue c v f t z)).sum := by
  induction T with
  | nil => simp
  | cons t T ih =>
    simp only [List.map_cons, List.sum_cons, amnrAdvectionTermValue_prepend, ih, mul_add]

/-- The explicit finite derivative list evaluates to the actual derivative.
Every intermediate derivative is admitted by proved smoothness. -/
theorem amnrAdvectionDerivativeTerms_value {c : AmnrSpace → Vec 2}
    {v : Fin 2 → AmnrSpace → ℝ} {f : AmnrSpace → ℝ} (hc : ContDiff ℝ (⊤ : ℕ∞) c)
    (hv : ∀ p, ContDiff ℝ (⊤ : ℕ∞) (v p)) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (d : Option (Fin 2)) (A : List AmnrAdvectionFactor) (w : List (Option (Fin 2))) (z :
        AmnrSpace) :
    amnrOp c d (amnrAdvectionTermValue c v f ⟨A, w⟩) z =
      ((amnrAdvectionDerivativeTerms d A w).map (fun t => amnrAdvectionTermValue c v f t z)).sum
          := by
  induction A with
  | nil =>
    simp only [amnrAdvectionDerivativeTerms, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero, amnrAdvectionTermValue, amnrAdvectionProduct, one_mul, amnrWord]
  | cons a A ih =>
    have hword : ContDiff ℝ (⊤ : ℕ∞) (amnrWord c a.2 (v a.1)) := contDiffOn_univ.mp
      (amnrWord_contDiffOn_infty isOpen_univ hc.contDiffOn (hv a.1).contDiffOn a.2)
    have hrest := amnrAdvectionTermValue_contDiff hc hv hf (⟨A, w⟩ : AmnrAdvectionTerm)
    have heq : amnrAdvectionTermValue c v f ⟨a :: A, w⟩ =
        amnrWord c a.2 (v a.1) * amnrAdvectionTermValue c v f ⟨A, w⟩ := by
      funext y
      dsimp [amnrAdvectionTermValue, amnrAdvectionProduct]
      ring
    rw [heq, amnrOp_mul d (hword.differentiable (by simp) z) (hrest.differentiable (by simp) z), ih]
    simp only [amnrAdvectionDerivativeTerms, List.map_cons, List.sum_cons,
        amnrAdvectionTermValue_sum_prepend]
    dsimp [amnrAdvectionTermValue, amnrAdvectionProduct, amnrWord]
    ring

end AVenhance.Infra.Section4
