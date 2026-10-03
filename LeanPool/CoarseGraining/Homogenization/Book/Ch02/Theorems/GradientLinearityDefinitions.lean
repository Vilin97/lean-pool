/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.ExistenceDefinitions

/-! # Gradient Linearity Definitions -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch02

noncomputable section

/-- Public theorem package for linearity of response-maximizer gradients.

The statement is made for arbitrary maximizers and uses a.e. gradient equality.
This keeps it independent of the particular chosen representative returned by
`canonicalMaximizer`. The canonical public theorem proving this package is
`responseGradientLinearityTheory` in `GradientLinearity.lean`. -/
structure ResponseGradientLinearityTheory {d : ℕ} (U : Domain d) (a : CoeffOn U) :
    Prop where
  add_gradient :
    ∀ p1 q1 p2 q2 : Vec d, ∀ v12 v1 v2 : Solution U a,
      IsResponseMaximizer U a (p1 + p2) (q1 + q2) v12 →
        IsResponseMaximizer U a p1 q1 v1 →
          IsResponseMaximizer U a p2 q2 v2 →
            v12.toH1.grad =ᵐ[volumeMeasureOn (U : Set (Vec d))]
              fun x => v1.toH1.grad x + v2.toH1.grad x
  smul_gradient :
    ∀ c : ℝ, ∀ p q : Vec d, ∀ vc v : Solution U a,
      IsResponseMaximizer U a (c • p) (c • q) vc →
        IsResponseMaximizer U a p q v →
          vc.toH1.grad =ᵐ[volumeMeasureOn (U : Set (Vec d))]
            fun x => c • v.toH1.grad x

namespace ResponseGradientLinearityTheory

theorem ofAEEq {d : ℕ} {U : Domain d} {a b : CoeffOn U}
    (h : CoeffOn.AEEq a b)
    (hLinear : ResponseGradientLinearityTheory U a) :
    ResponseGradientLinearityTheory U b where
  add_gradient := by
    intro p1 q1 p2 q2 v12 v1 v2 h12 h1 h2
    let va12 : Solution U a := Solution.ofAEEq h.symm v12
    let va1 : Solution U a := Solution.ofAEEq h.symm v1
    let va2 : Solution U a := Solution.ofAEEq h.symm v2
    have hmax12 : IsResponseMaximizer U a (p1 + p2) (q1 + q2) va12 :=
      h12.ofAEEq h.symm
    have hmax1 : IsResponseMaximizer U a p1 q1 va1 := h1.ofAEEq h.symm
    have hmax2 : IsResponseMaximizer U a p2 q2 va2 := h2.ofAEEq h.symm
    have hgrad := hLinear.add_gradient p1 q1 p2 q2 va12 va1 va2 hmax12 hmax1 hmax2
    simpa [va12, va1, va2] using hgrad
  smul_gradient := by
    intro c p q vc v hc hv
    let vac : Solution U a := Solution.ofAEEq h.symm vc
    let va : Solution U a := Solution.ofAEEq h.symm v
    have hmaxc : IsResponseMaximizer U a (c • p) (c • q) vac := hc.ofAEEq h.symm
    have hmax : IsResponseMaximizer U a p q va := hv.ofAEEq h.symm
    have hgrad := hLinear.smul_gradient c p q vac va hmaxc hmax
    simpa [vac, va] using hgrad

theorem iff_ofAEEq {d : ℕ} {U : Domain d} {a b : CoeffOn U}
    (h : CoeffOn.AEEq a b) :
    ResponseGradientLinearityTheory U a ↔ ResponseGradientLinearityTheory U b :=
  ⟨ofAEEq h, ofAEEq h.symm⟩

end ResponseGradientLinearityTheory

theorem gradient_add_of_response_maximizers {d : ℕ}
    {U : Domain d} {a : CoeffOn U}
    (hLinear : ResponseGradientLinearityTheory U a)
    {p1 q1 p2 q2 : Vec d} {v12 v1 v2 : Solution U a}
    (h12 : IsResponseMaximizer U a (p1 + p2) (q1 + q2) v12)
    (h1 : IsResponseMaximizer U a p1 q1 v1)
    (h2 : IsResponseMaximizer U a p2 q2 v2) :
    v12.toH1.grad =ᵐ[volumeMeasureOn (U : Set (Vec d))]
      fun x => v1.toH1.grad x + v2.toH1.grad x :=
  hLinear.add_gradient p1 q1 p2 q2 v12 v1 v2 h12 h1 h2

theorem gradient_smul_of_response_maximizers {d : ℕ}
    {U : Domain d} {a : CoeffOn U}
    (hLinear : ResponseGradientLinearityTheory U a)
    {c : ℝ} {p q : Vec d} {vc v : Solution U a}
    (hc : IsResponseMaximizer U a (c • p) (c • q) vc)
    (hv : IsResponseMaximizer U a p q v) :
    vc.toH1.grad =ᵐ[volumeMeasureOn (U : Set (Vec d))]
      fun x => c • v.toH1.grad x :=
  hLinear.smul_gradient c p q vc v hc hv

theorem canonicalMaximizer_add_gradientAE {d : ℕ}
    {U : Domain d} {a : CoeffOn U}
    (hTheory : ResponseExistenceTheory U a)
    (hLinear : ResponseGradientLinearityTheory U a)
    (p1 q1 p2 q2 : Vec d) :
    (canonicalMaximizer hTheory (p1 + p2) (q1 + q2)).toSolution.toH1.grad
      =ᵐ[volumeMeasureOn (U : Set (Vec d))]
        fun x =>
          (canonicalMaximizer hTheory p1 q1).toSolution.toH1.grad x +
            (canonicalMaximizer hTheory p2 q2).toSolution.toH1.grad x :=
  hLinear.add_gradient p1 q1 p2 q2
    (canonicalMaximizer hTheory (p1 + p2) (q1 + q2)).toSolution
    (canonicalMaximizer hTheory p1 q1).toSolution
    (canonicalMaximizer hTheory p2 q2).toSolution
    (canonicalMaximizer_isMaximizer hTheory (p1 + p2) (q1 + q2))
    (canonicalMaximizer_isMaximizer hTheory p1 q1)
    (canonicalMaximizer_isMaximizer hTheory p2 q2)

theorem canonicalMaximizer_smul_gradientAE {d : ℕ}
    {U : Domain d} {a : CoeffOn U}
    (hTheory : ResponseExistenceTheory U a)
    (hLinear : ResponseGradientLinearityTheory U a)
    (c : ℝ) (p q : Vec d) :
    (canonicalMaximizer hTheory (c • p) (c • q)).toSolution.toH1.grad
      =ᵐ[volumeMeasureOn (U : Set (Vec d))]
        fun x => c • (canonicalMaximizer hTheory p q).toSolution.toH1.grad x :=
  hLinear.smul_gradient c p q
    (canonicalMaximizer hTheory (c • p) (c • q)).toSolution
    (canonicalMaximizer hTheory p q).toSolution
    (canonicalMaximizer_isMaximizer hTheory (c • p) (c • q))
    (canonicalMaximizer_isMaximizer hTheory p q)

end

end Ch02
end Book
end Homogenization
