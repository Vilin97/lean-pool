/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Geometry.ProjectiveConormalDirections
import LeanPool.Stafford38.Stafford38.Geometry.LaurentConormalDirection

/-!
# Fibre equations of the smooth conormal closure

For a prime affine ideal, a fibre polynomial vanishing on all smooth conormal
fibres also vanishes on the entire equation-conormal locus.
-/

namespace Stafford38.Geometry.SmoothConormalFibreVanishing

open Stafford38.Geometry.AffineConormalClosure
open Stafford38.Geometry.ConormalPrincipalOpenDensity
open Stafford38.Geometry.SmoothAffineConormal
open Stafford38.Geometry.ProjectiveConormalDirections
open Stafford38.Geometry.LaurentConormalDirection

noncomputable section

theorem fibreLift_mem_vanishingIdeal_equationConormal
    {k : Type*} [Field k] [IsAlgClosed k] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) k)) (hI : I.IsPrime)
    (P : MvPolynomial (Fin n) k)
    (hP : P ∈ MvPolynomial.vanishingIdeal k (smoothConormalFibreProjection I)) :
    fibreLift P ∈ MvPolynomial.vanishingIdeal k (equationConormalLocus I) := by
  intro q hq
  have hclosure : q ∈ equationConormalClosure I := by
    intro f hf
    exact hf q hq
  rw [← equationConormalClosure_smoothAffine_eq I hI] at hclosure
  apply hclosure
  intro r hr
  have hproj : (fun i => r (.inr i)) ∈ smoothConormalFibreProjection I :=
    ⟨fun i => r (.inl i), hr.2, hr.1.2⟩
  have hv := hP _ hproj
  simpa [fibreLift, MvPolynomial.eval_rename, Function.comp_def] using hv


end
end Stafford38.Geometry.SmoothConormalFibreVanishing
