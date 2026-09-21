/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Setup

/-! # Response -/

namespace Homogenization
namespace Book
namespace Ch02

noncomputable section

/-- Public normalized average over a Chapter 2 domain. -/
noncomputable def average {d : ℕ} (U : Domain d) (f : Vec d → ℝ) : ℝ :=
  (MeasureTheory.volume (U : Set (Vec d))).toReal⁻¹ *
    ∫ x in (U : Set (Vec d)), f x ∂MeasureTheory.volume

/-- Public normalized vector average over a Chapter 2 domain. -/
noncomputable def averageVec {d : ℕ} (U : Domain d) (F : Vec d → Vec d) : Vec d :=
  fun i => average U (fun x => F x i)

/-- The response integrand from the notes, used under the normalized volume average. -/
noncomputable def responseIntegrand {d : ℕ} (U : Domain d) (a : CoeffOn U)
    (p q : Vec d) (v : Solution U a) : Vec d → ℝ :=
  fun x =>
    -((1 / 2 : ℝ) *
        vecDot (v.toH1.grad x)
          (matVecMul (symmPart (a.toCoeffField x)) (v.toH1.grad x)))
      - vecDot p (matVecMul (a.toCoeffField x) (v.toH1.grad x))
      + vecDot q (v.toH1.grad x)

/-- The response value of one admissible solution. -/
noncomputable def responseValue {d : ℕ} (U : Domain d) (a : CoeffOn U)
    (p q : Vec d) (v : Solution U a) : ℝ :=
  average U (responseIntegrand U a p q v)

theorem responseIntegrand_ofAEEq {d : ℕ} {U : Domain d} {a b : CoeffOn U}
    (h : CoeffOn.AEEq a b) (p q : Vec d) (v : Solution U a) :
    responseIntegrand U b p q (Solution.ofAEEq h v)
      =ᵐ[volumeMeasureOn (U : Set (Vec d))]
    responseIntegrand U a p q v :=
  h.symm.mono fun x hx => by
    simp [responseIntegrand, hx]

theorem responseValue_ofAEEq {d : ℕ} {U : Domain d} {a b : CoeffOn U}
    (h : CoeffOn.AEEq a b) (p q : Vec d) (v : Solution U a) :
    responseValue U b p q (Solution.ofAEEq h v) = responseValue U a p q v := by
  unfold responseValue average
  congr 1
  exact MeasureTheory.integral_congr_ae (responseIntegrand_ofAEEq h p q v)

/-- The first-variation integrand appearing in the Euler-Lagrange equation for
the response maximizer. -/
noncomputable def firstVariationIntegrand {d : ℕ} (U : Domain d) (a : CoeffOn U)
    (p q : Vec d) (v w : Solution U a) : Vec d → ℝ :=
  fun x =>
    vecDot q (w.toH1.grad x)
      - vecDot p (matVecMul (a.toCoeffField x) (w.toH1.grad x))
      - vecDot (w.toH1.grad x)
          (matVecMul (symmPart (a.toCoeffField x)) (v.toH1.grad x))

/-- The averaged first variation. A maximizer makes this vanish for every
admissible direction. -/
noncomputable def firstVariationValue {d : ℕ} (U : Domain d) (a : CoeffOn U)
    (p q : Vec d) (v w : Solution U a) : ℝ :=
  average U (firstVariationIntegrand U a p q v w)

/-- The positive quadratic energy in the second-variation formula. -/
noncomputable def variationEnergyIntegrand {d : ℕ} (U : Domain d) (a : CoeffOn U)
    (w : Solution U a) : Vec d → ℝ :=
  fun x =>
    vecDot (w.toH1.grad x)
      (matVecMul (symmPart (a.toCoeffField x)) (w.toH1.grad x))

/-- The averaged quadratic energy of an admissible variation. -/
noncomputable def variationEnergyValue {d : ℕ} (U : Domain d) (a : CoeffOn U)
    (w : Solution U a) : ℝ :=
  average U (variationEnergyIntegrand U a w)

/-- The right-hand side in the second-variation identity for two admissible
solutions. -/
noncomputable def secondVariationEnergyValue {d : ℕ} (U : Domain d) (a : CoeffOn U)
    (v w : Solution U a) : ℝ :=
  average U fun x =>
    (1 / 2 : ℝ) *
      vecDot (v.toH1.grad x - w.toH1.grad x)
        (matVecMul (symmPart (a.toCoeffField x))
          (v.toH1.grad x - w.toH1.grad x))

/-- The averaged gradient of a Chapter 2 solution. -/
noncomputable def averageGradient {d : ℕ} (U : Domain d) (a : CoeffOn U)
    (v : Solution U a) : Vec d :=
  averageVec U v.toH1.grad

/-- The averaged flux of a Chapter 2 solution. -/
noncomputable def averageFlux {d : ℕ} (U : Domain d) (a : CoeffOn U)
    (v : Solution U a) : Vec d :=
  averageVec U fun x => matVecMul (a.toCoeffField x) (v.toH1.grad x)

/-- The averaged gradient is unchanged by a null-set change of coefficient
representative. -/
theorem averageGradient_ofAEEq {d : ℕ} {U : Domain d} {a b : CoeffOn U}
    (h : CoeffOn.AEEq a b) (v : Solution U a) :
    averageGradient U b (Solution.ofAEEq h v) = averageGradient U a v :=
  rfl

/-- The averaged flux is unchanged by a null-set change of coefficient
representative. -/
theorem averageFlux_ofAEEq {d : ℕ} {U : Domain d} {a b : CoeffOn U}
    (h : CoeffOn.AEEq a b) (v : Solution U a) :
    averageFlux U b (Solution.ofAEEq h v) = averageFlux U a v := by
  ext i
  unfold averageFlux averageVec average
  congr 1
  exact MeasureTheory.integral_congr_ae <| h.symm.mono fun x hx => by
    simp [hx]

theorem firstVariationIntegrand_ofAEEq {d : ℕ} {U : Domain d} {a b : CoeffOn U}
    (h : CoeffOn.AEEq a b) (p q : Vec d) (v w : Solution U a) :
    firstVariationIntegrand U b p q (Solution.ofAEEq h v) (Solution.ofAEEq h w)
      =ᵐ[volumeMeasureOn (U : Set (Vec d))]
    firstVariationIntegrand U a p q v w :=
  h.symm.mono fun x hx => by
    simp [firstVariationIntegrand, hx]

theorem firstVariationValue_ofAEEq {d : ℕ} {U : Domain d} {a b : CoeffOn U}
    (h : CoeffOn.AEEq a b) (p q : Vec d) (v w : Solution U a) :
    firstVariationValue U b p q (Solution.ofAEEq h v) (Solution.ofAEEq h w) =
      firstVariationValue U a p q v w := by
  unfold firstVariationValue average
  congr 1
  exact MeasureTheory.integral_congr_ae (firstVariationIntegrand_ofAEEq h p q v w)

theorem variationEnergyIntegrand_ofAEEq {d : ℕ} {U : Domain d} {a b : CoeffOn U}
    (h : CoeffOn.AEEq a b) (w : Solution U a) :
    variationEnergyIntegrand U b (Solution.ofAEEq h w)
      =ᵐ[volumeMeasureOn (U : Set (Vec d))]
    variationEnergyIntegrand U a w :=
  h.symm.mono fun x hx => by
    simp [variationEnergyIntegrand, hx]

theorem variationEnergyValue_ofAEEq {d : ℕ} {U : Domain d} {a b : CoeffOn U}
    (h : CoeffOn.AEEq a b) (w : Solution U a) :
    variationEnergyValue U b (Solution.ofAEEq h w) =
      variationEnergyValue U a w := by
  unfold variationEnergyValue average
  congr 1
  exact MeasureTheory.integral_congr_ae (variationEnergyIntegrand_ofAEEq h w)

theorem secondVariationEnergyValue_ofAEEq {d : ℕ} {U : Domain d} {a b : CoeffOn U}
    (h : CoeffOn.AEEq a b) (v w : Solution U a) :
    secondVariationEnergyValue U b (Solution.ofAEEq h v) (Solution.ofAEEq h w) =
      secondVariationEnergyValue U a v w := by
  unfold secondVariationEnergyValue average
  congr 1
  exact MeasureTheory.integral_congr_ae <| h.symm.mono fun x hx => by
    simp [hx]

/-- The set of values whose supremum is `J(U,p,q;a)`. -/
noncomputable def responseValueSet {d : ℕ} (U : Domain d) (a : CoeffOn U)
    (p q : Vec d) : Set ℝ :=
  {m | ∃ v : Solution U a, m = responseValue U a p q v}

theorem responseValueSet_nonempty {d : ℕ} (U : Domain d) (a : CoeffOn U)
    (p q : Vec d) : (responseValueSet U a p q).Nonempty :=
  ⟨responseValue U a p q (zeroSolution U a), zeroSolution U a, rfl⟩

/-- Public Chapter 2 response functional `J(U,p,q;a)`. -/
noncomputable def responseJ {d : ℕ} (U : Domain d) (a : CoeffOn U)
    (p q : Vec d) : ℝ :=
  sSup (responseValueSet U a p q)

theorem responseValueSet_eq_ofAEEq {d : ℕ} {U : Domain d} {a b : CoeffOn U}
    (h : CoeffOn.AEEq a b) (p q : Vec d) :
    responseValueSet U a p q = responseValueSet U b p q := by
  ext m
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨Solution.ofAEEq h v, (responseValue_ofAEEq h p q v).symm⟩
  · rintro ⟨v, rfl⟩
    exact ⟨Solution.ofAEEq h.symm v, (responseValue_ofAEEq h.symm p q v).symm⟩

theorem responseJ_eq_ofAEEq {d : ℕ} {U : Domain d} {a b : CoeffOn U}
    (h : CoeffOn.AEEq a b) (p q : Vec d) :
    responseJ U a p q = responseJ U b p q := by
  unfold responseJ
  rw [responseValueSet_eq_ofAEEq h p q]

/-- A solution is a response maximizer if it realizes the variational supremum. -/
def IsResponseMaximizer {d : ℕ} (U : Domain d) (a : CoeffOn U)
    (p q : Vec d) (v : Solution U a) : Prop :=
  ∀ w : Solution U a, responseValue U a p q w ≤ responseValue U a p q v

namespace IsResponseMaximizer

theorem ofAEEq {d : ℕ} {U : Domain d} {a b : CoeffOn U}
    (h : CoeffOn.AEEq a b) {p q : Vec d} {v : Solution U a}
    (hv : IsResponseMaximizer U a p q v) :
    IsResponseMaximizer U b p q (Solution.ofAEEq h v) := by
  intro w
  have hw := hv (Solution.ofAEEq h.symm w)
  simpa [responseValue_ofAEEq h.symm p q w, responseValue_ofAEEq h p q v] using hw

end IsResponseMaximizer

theorem responseValueSet_isGreatest_of_isResponseMaximizer {d : ℕ}
    {U : Domain d} {a : CoeffOn U} {p q : Vec d} {v : Solution U a}
    (hv : IsResponseMaximizer U a p q v) :
    IsGreatest (responseValueSet U a p q) (responseValue U a p q v) := by
  constructor
  · exact ⟨v, rfl⟩
  · intro y hy
    rcases hy with ⟨w, rfl⟩
    exact hv w

theorem responseJ_eq_responseValue_of_isResponseMaximizer {d : ℕ}
    {U : Domain d} {a : CoeffOn U} {p q : Vec d} {v : Solution U a}
    (hv : IsResponseMaximizer U a p q v) :
    responseJ U a p q = responseValue U a p q v := by
  unfold responseJ
  exact (responseValueSet_isGreatest_of_isResponseMaximizer hv).csSup_eq

/-- The mean-zero response maximizer as a packaged object. -/
structure CanonicalMaximizer {d : ℕ} (U : Domain d) (a : CoeffOn U)
    (p q : Vec d) where
  toSolution : Solution U a
  meanZero : MeanZeroOn (U : Set (Vec d)) toSolution.toH1.toFun
  isMaximizer : IsResponseMaximizer U a p q toSolution

namespace CanonicalMaximizer

instance {d : ℕ} {U : Domain d} {a : CoeffOn U} {p q : Vec d} :
    CoeOut (CanonicalMaximizer U a p q) (Solution U a) where
  coe v := v.toSolution

/-- Transport the canonical maximizer package across a null-set change of
coefficient representative. -/
def ofAEEq {d : ℕ} {U : Domain d} {a b : CoeffOn U}
    (h : CoeffOn.AEEq a b) {p q : Vec d}
    (v : CanonicalMaximizer U a p q) : CanonicalMaximizer U b p q where
  toSolution := Solution.ofAEEq h v.toSolution
  meanZero := by
    simpa using v.meanZero
  isMaximizer := v.isMaximizer.ofAEEq h

theorem responseJ_eq {d : ℕ} {U : Domain d} {a : CoeffOn U} {p q : Vec d}
    (v : CanonicalMaximizer U a p q) :
    responseJ U a p q = responseValue U a p q v.toSolution :=
  responseJ_eq_responseValue_of_isResponseMaximizer v.isMaximizer

end CanonicalMaximizer

end

end Ch02
end Book
end Homogenization
