/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.H1.Translation
import LeanPool.CoarseGraining.Homogenization.Sobolev.PotentialSolenoidal

/-! # Potential Solenoidal Translation -/

namespace Homogenization

theorem isPotentialOn_translateSet {d : ℕ} {U : Set (Vec d)} {f : Vec d → Vec d}
    (hf : IsPotentialOn U f) (z : Vec d) :
    IsPotentialOn (translateSet z U) (fun x => f (x - z)) := by
  rcases hf with ⟨u, rfl⟩
  exact ⟨u.translate z, by
    funext x
    simp⟩

theorem isPotentialZeroTraceOn_translateSet {d : ℕ} {U : Set (Vec d)} {f : Vec d → Vec d}
    (hf : IsPotentialZeroTraceOn U f) (z : Vec d) :
    IsPotentialZeroTraceOn (translateSet z U) (fun x => f (x - z)) := by
  rcases hf with ⟨u, rfl⟩
  exact ⟨u.translate z, by
    funext x
    simp⟩

theorem isSolenoidalOn_translateSet {d : ℕ} {U : Set (Vec d)} {g : Vec d → Vec d}
    (hg : IsSolenoidalOn U g) (z : Vec d) :
    IsSolenoidalOn (translateSet z U) (fun x => g (x - z)) := by
  intro φ
  have hU : translateSet (-z) (translateSet z U) = U := by
    simpa using (translateSet_translateSet (d := d) z (-z) U)
  have hg' : IsSolenoidalOn (translateSet (-z) (translateSet z U)) g := by
    simpa [hU] using hg
  have htest :
      ∫ x in U, vecDot (g x) (φ.toH1Function.grad (x + z)) ∂MeasureTheory.volume = 0 := by
    simpa [hU, H10Function.translate_toH1Function, H1Function.translate, sub_eq_add_neg, add_assoc]
      using hg' (φ.translate (-z))
  have hchange :
      ∫ x in U, vecDot (g x) (φ.toH1Function.grad (x + z)) ∂MeasureTheory.volume =
        ∫ x in translateSet z U,
          vecDot (g (x - z)) (φ.toH1Function.grad x) ∂MeasureTheory.volume := by
    simpa [sub_eq_add_neg, add_assoc] using
      (setIntegral_comp_addRight_translateSet (d := d) (E := ℝ) z U
        (fun x => vecDot (g (x - z)) (φ.toH1Function.grad x)))
  calc
    ∫ x in translateSet z U,
        vecDot (g (x - z)) (φ.toH1Function.grad x) ∂MeasureTheory.volume
      = ∫ x in U, vecDot (g x) (φ.toH1Function.grad (x + z)) ∂MeasureTheory.volume := by
          symm
          exact hchange
    _ = 0 := htest

theorem isSolenoidalZeroNormalTraceOn_translateSet {d : ℕ} {U : Set (Vec d)}
    {g : Vec d → Vec d} (hg : IsSolenoidalZeroNormalTraceOn U g) (z : Vec d) :
    IsSolenoidalZeroNormalTraceOn (translateSet z U) (fun x => g (x - z)) := by
  intro φ
  have hU : translateSet (-z) (translateSet z U) = U := by
    simpa using (translateSet_translateSet (d := d) z (-z) U)
  have hg' : IsSolenoidalZeroNormalTraceOn (translateSet (-z) (translateSet z U)) g := by
    simpa [hU] using hg
  have htest :
      ∫ x in U, vecDot (g x) (φ.grad (x + z)) ∂MeasureTheory.volume = 0 := by
    simpa [hU, H1Function.translate, sub_eq_add_neg, add_assoc] using
      hg' (φ.translate (-z))
  have hchange :
      ∫ x in U, vecDot (g x) (φ.grad (x + z)) ∂MeasureTheory.volume =
        ∫ x in translateSet z U, vecDot (g (x - z)) (φ.grad x) ∂MeasureTheory.volume := by
    simpa [sub_eq_add_neg, add_assoc] using
      (setIntegral_comp_addRight_translateSet (d := d) (E := ℝ) z U
        (fun x => vecDot (g (x - z)) (φ.grad x)))
  calc
    ∫ x in translateSet z U, vecDot (g (x - z)) (φ.grad x) ∂MeasureTheory.volume
      = ∫ x in U, vecDot (g x) (φ.grad (x + z)) ∂MeasureTheory.volume := by
          symm
          exact hchange
    _ = 0 := htest

end Homogenization
