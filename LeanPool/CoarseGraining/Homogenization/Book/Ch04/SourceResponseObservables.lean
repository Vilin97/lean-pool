/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.DeterministicIdentities
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourceMu

/-!
# Exact-source scalar response observables

The deterministic Chapter 2 response identity turns the scalar `ResponseJ`
into one exact-source local `Mu` observable and a constant.  The local Chapter
2 coefficient realization below is built directly from source-carrier
ellipticity on the cube.
-/

namespace Homogenization.Book.Ch04

open MeasureTheory

noncomputable section

private noncomputable def sourceCoeffOnCube {d : ℕ} (a : Source.Coarse.Carrier d)
    (Q : TriadicCube d) : Ch02.CoeffOn (Ch02.cubeDomain Q) := by
  let hExists := exists_source_isAEEllipticFieldOn_cubeSet a Q
  let ε := Classical.choose hExists
  have hData : 0 < ε ∧ ε ≤ 1 ∧
      IsAEEllipticFieldOn ε ε⁻¹ (cubeSet Q) a.1 :=
    Classical.choose_spec hExists
  have hEll_open : IsAEEllipticFieldOn ε ε⁻¹ (openCubeSet Q) a.1 :=
    hData.2.2.mono (measurableSet_openCubeSet Q) (openCubeSet_subset_cubeSet Q)
  exact
    { toCoeffField := a.1
      lam := ε
      Lam := ε⁻¹
      lam_pos := hData.1
      lam_le_Lam := hData.2.1.trans ((one_le_inv₀ hData.1).2 hData.2.1)
      aeStronglyMeasurable := by
        intro i j
        simpa [Ch02.cubeDomain_coe] using
          hEll_open.2.1 i j
      aeElliptic := by
        simpa [Ch02.cubeDomain_coe] using hEll_open.ae_isEllipticMatrix }

/-- On the exact source carrier, the scalar response is the `Mu` energy at
`(-p,q)` minus the deterministic pairing. -/
theorem ResponseJ_cubeSet_eq_Mu_neg_left_sub_vecDot_source
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (p q : Vec d)
    (a : Source.Coarse.Carrier d) :
    ResponseJ (cubeSet Q) p q a.1 =
      Mu (cubeSet Q) (-p, q) a.1 - vecDot p q := by
  simpa only [sourceCoeffOnCube] using
    Ch02.ResponseJ_cubeSet_eq_Mu_neg_left_sub_vecDot Q (sourceCoeffOnCube a Q) p q

/-- The scalar response on a triadic cube is exact-source local. -/
theorem isSourceLocalRandomVariable_ResponseJ_cubeSet
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (p q : Vec d) :
    IsSourceLocalRandomVariable (cubeSet Q) (measurableSet_cubeSet Q)
      (fun a : Source.Coarse.Carrier d => ResponseJ (cubeSet Q) p q a.1) := by
  have hmu := (SourceObservable.mu Q (-p, q)).isLocal
  have hEq :
      (fun a : Source.Coarse.Carrier d => ResponseJ (cubeSet Q) p q a.1) =
        fun a => Mu (cubeSet Q) (-p, q) a.1 - vecDot p q := by
    funext a
    exact ResponseJ_cubeSet_eq_Mu_neg_left_sub_vecDot_source Q p q a
  rw [hEq]
  exact hmu.sub (IsSourceLocalRandomVariable.const (cubeSet Q)
    (measurableSet_cubeSet Q) (vecDot p q))

private theorem isSourceLocalRandomVariable_descendantsAverage
    {d : ℕ} (Q : TriadicCube d) (j : ℕ)
    {F : TriadicCube d → Source.Coarse.Carrier d → ℝ}
    (hF : ∀ R, R ∈ descendantsAtDepth Q j →
      IsSourceLocalRandomVariable (cubeSet R) (measurableSet_cubeSet R) (F R)) :
    IsSourceLocalRandomVariable (cubeSet Q) (measurableSet_cubeSet Q)
      (fun a => descendantsAverage Q j (fun R => F R a)) := by
  classical
  let D : Finset (TriadicCube d) := descendantsAtDepth Q j
  let : MeasurableSpace (Source.Coarse.Carrier d) :=
    Source.Coarse.localSigma (cubeSet Q) (measurableSet_cubeSet Q)
  have hsum : Measurable (fun a : Source.Coarse.Carrier d => D.sum (fun R => F R a)) := by
    refine Finset.measurable_sum D ?_
    intro R hR
    exact (hF R (by simpa [D] using hR)).mono
      (measurableSet_cubeSet R) (measurableSet_cubeSet Q)
      (cubeSet_subset_of_mem_descendantsAtDepth (by simpa [D] using hR))
  simpa [descendantsAverage, D] using! hsum.const_mul ((D.card : ℝ)⁻¹)

/-- The finite descendant average of the scalar response is exact-source local
on the parent cube. -/
theorem isSourceLocalRandomVariable_descendantsAverage_ResponseJ_cubeSet
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (j : ℕ) (p q : Vec d) :
    IsSourceLocalRandomVariable (cubeSet Q) (measurableSet_cubeSet Q)
      (fun a : Source.Coarse.Carrier d =>
        descendantsAverage Q j (fun R => ResponseJ (cubeSet R) p q a.1)) :=
  isSourceLocalRandomVariable_descendantsAverage Q j fun R _ =>
    isSourceLocalRandomVariable_ResponseJ_cubeSet R p q

namespace SourceObservable

/-- The scalar response on a triadic cube, bundled as an exact-source local
observable. -/
noncomputable def responseJ {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (p q : Vec d) : SourceObservable d (cubeSet Q) ℝ where
  measurableSet := measurableSet_cubeSet Q
  toFun := fun a => ResponseJ (cubeSet Q) p q a.1
  isLocal := isSourceLocalRandomVariable_ResponseJ_cubeSet Q p q

@[simp]
theorem responseJ_apply {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (p q : Vec d) (a : Source.Coarse.Carrier d) :
    responseJ Q p q a = ResponseJ (cubeSet Q) p q a.1 :=
  rfl

end SourceObservable

end

end Homogenization.Book.Ch04
