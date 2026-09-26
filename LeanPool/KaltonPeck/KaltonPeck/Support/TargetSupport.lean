/-
Copyright (c) 2026 Avik Das. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Avik Das
-/
module

/-
Copyright (c) 2026 adas1236. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: adas1236
-/
public import LeanPool.KaltonPeck.KaltonPeck.Support.Definitions

/-!
# Hyperplane extensions of complex structures

This file extends a complex structure from a closed hyperplane to the ambient Banach space and
computes the rank of the resulting square defect.
-/

@[expose] public section


namespace KaltonPeck.Support.TargetSupport

noncomputable
section

/-- A codimension-one complex structure extends by the identity on a one-dimensional topological
complement, and its square defect has exactly rank one.
Blueprint label: `lem:hyperplane-extension`; audit IDs `HID-HYPERPLANE-BLOCK-EXTENSION`,
`HID-RANK-ONE-COMPUTATION`, and `COV-HYPERPLANE-EXT`. -/
theorem hyperplaneExtension {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
     (H : Submodule ℝ X) (hH : IsHyperplane H) (J : H →L[ℝ] H)
    (hJ : IsComplexStructure J) :
    ∃ F : Submodule ℝ X,
      H.IsTopCompl F ∧ IsClosed (F : Set X) ∧ Module.finrank ℝ F = 1 ∧
        ∃ T : X →L[ℝ] X,
          (∀ h : H, T h = (J h : X)) ∧
            (∀ f : F, T f = (f : X)) ∧
            (∀ (h : H) (f : F),
              T ((h : X) + (f : X)) = (J h : X) + (f : X)) ∧
            (∀ (h : H) (f : F),
              (T ^ 2 + (1 : X →L[ℝ] X)) ((h : X) + (f : X)) = 2 • (f : X)) ∧
            (T ^ 2 + 1).toLinearMap.range = F ∧
              HasFiniteRank (T ^ 2 + 1) ∧ operatorRank (T ^ 2 + 1) = 1 := by
  rcases hH with ⟨hHclosed, hcodim⟩
  let : FiniteDimensional ℝ (X ⧸ H) :=
    FiniteDimensional.of_finrank_eq_succ hcodim
  obtain ⟨F, hHF⟩ :=
    (Submodule.ClosedComplemented.of_finiteDimensional_quotient hHclosed).exists_isTopCompl
  have hFclosed : IsClosed (F : Set X) := hHF.isClosed'
  let e := H.quotientEquivOfIsTopCompl F hHF
  have hFdim : Module.finrank ℝ F = 1 := by
    calc
      Module.finrank ℝ F = Module.finrank ℝ (X ⧸ H) := e.toLinearEquiv.finrank_eq.symm
      _ = 1 := hcodim
  let T : X →L[ℝ] X :=
    ContinuousLinearMap.ofIsTopCompl hHF (H.subtypeL.comp J) F.subtypeL
  have hTH (h : H) : T (h : X) = (J h : X) := by
    simp [T]
  have hTF (f : F) : T (f : X) = (f : X) := by
    simp [T]
  have hTadd (h : H) (f : F) :
      T ((h : X) + (f : X)) = (J h : X) + (f : X) := by
    rw [map_add, hTH, hTF]
  have hJJ (h : H) : J (J h) = -h := by
    have hh := congrArg (fun K : H →L[ℝ] H => K h) hJ
    simpa [pow_two] using hh
  have hdefect (h : H) (f : F) :
      (T ^ 2 + (1 : X →L[ℝ] X)) ((h : X) + (f : X)) = 2 • (f : X) := by
    calc
      (T ^ 2 + (1 : X →L[ℝ] X)) ((h : X) + (f : X)) =
          T (T ((h : X) + (f : X))) + ((h : X) + (f : X)) := by
            simp [pow_two]
      _ = T ((J h : X) + (f : X)) + ((h : X) + (f : X)) := by rw [hTadd]
      _ = ((J (J h) : H) : X) + (f : X) + ((h : X) + (f : X)) := by
            rw [hTadd]
      _ = 2 • (f : X) := by
            rw [hJJ]
            simp only [Submodule.coe_neg]
            module
  have hRange : (T ^ 2 + 1).toLinearMap.range = F := by
    apply le_antisymm
    · rintro x ⟨y, rfl⟩
      let h : H := H.projectionOntoL F hHF y
      let f : F := F.projectionOntoL H hHF.symm y
      have hy : (h : X) + (f : X) = y := by
        exact Submodule.projectionL_add_projectionL_eq_self hHF y
      rw [← hy]
      change (T ^ 2 + (1 : X →L[ℝ] X)) ((h : X) + (f : X)) ∈ F
      rw [hdefect]
      simpa only [two_nsmul] using F.add_mem f.property f.property
    · intro x hx
      let f : F := ⟨x, hx⟩
      refine ⟨((0 : H) : X) + (((2 : ℝ)⁻¹ • f : F) : X), ?_⟩
      change (T ^ 2 + (1 : X →L[ℝ] X))
          (((0 : H) : X) + (((2 : ℝ)⁻¹ • f : F) : X)) = x
      rw [hdefect]
      simp [f]
      module
  have hFinite : HasFiniteRank (T ^ 2 + 1) := by
    rw [HasFiniteRank, hRange]
    exact FiniteDimensional.of_finrank_eq_succ hFdim
  refine ⟨F, hHF, hFclosed, hFdim, T, hTH, hTF, hTadd, hdefect, hRange, hFinite, ?_⟩
  unfold operatorRank
  exact
    (congrArg (fun S : Submodule ℝ X => Module.finrank ℝ S) hRange).trans hFdim

end


end KaltonPeck.Support.TargetSupport

/-
Upstream license notice:
MIT License

Copyright (c) 2026 Avik Das

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
