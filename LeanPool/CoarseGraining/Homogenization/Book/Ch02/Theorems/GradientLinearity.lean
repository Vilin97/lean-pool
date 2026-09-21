/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Internal.Ch02.GradientLinearity

/-! # Gradient Linearity -/

namespace Homogenization
namespace Book
namespace Ch02

noncomputable section

/-- Public Chapter 2 a.e. linearity theorem for response-maximizer gradients. -/
theorem responseGradientLinearityTheory {d : ℕ} (U : Domain d) (a : CoeffOn U) :
    ResponseGradientLinearityTheory U a :=
  Homogenization.Internal.Ch02.BookCh02.responseGradientLinearityTheory U a

/-- Public a.e. additivity of response-maximizer gradients. -/
theorem gradient_add_of_isResponseMaximizer {d : ℕ}
    {U : Domain d} {a : CoeffOn U}
    {p1 q1 p2 q2 : Vec d} {v12 v1 v2 : Solution U a}
    (h12 : IsResponseMaximizer U a (p1 + p2) (q1 + q2) v12)
    (h1 : IsResponseMaximizer U a p1 q1 v1)
    (h2 : IsResponseMaximizer U a p2 q2 v2) :
    v12.toH1.grad =ᵐ[volumeMeasureOn (U : Set (Vec d))]
      fun x => v1.toH1.grad x + v2.toH1.grad x :=
  gradient_add_of_response_maximizers
    (responseGradientLinearityTheory U a) h12 h1 h2

/-- Public a.e. homogeneity of response-maximizer gradients. -/
theorem gradient_smul_of_isResponseMaximizer {d : ℕ}
    {U : Domain d} {a : CoeffOn U}
    {c : ℝ} {p q : Vec d} {vc v : Solution U a}
    (hc : IsResponseMaximizer U a (c • p) (c • q) vc)
    (hv : IsResponseMaximizer U a p q v) :
    vc.toH1.grad =ᵐ[volumeMeasureOn (U : Set (Vec d))]
      fun x => c • v.toH1.grad x :=
  gradient_smul_of_response_maximizers
    (responseGradientLinearityTheory U a) hc hv

end

end Ch02
end Book
end Homogenization
