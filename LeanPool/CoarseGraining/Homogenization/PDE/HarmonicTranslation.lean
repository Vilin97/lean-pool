/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.PDE.Harmonic
public import LeanPool.CoarseGraining.Homogenization.Sobolev.PotentialSolenoidalTranslation

/-!
# Translation of harmonic functions

This file contains the PDE-level translation API for `AHarmonicFunction`.  It is
used by both coarse-graining response identities and cube/open-cube transport.
-/

@[expose] public section

namespace Homogenization

@[simp] theorem translateCoeffField_neg_add_cancel {d : ℕ}
    (z : Vec d) (a : CoeffField d) :
    translateCoeffField (-z) (translateCoeffField z a) = a := by
  funext x
  simp [translateCoeffField, add_assoc]

theorem isAHarmonicGradient_translateSet {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    (z : Vec d) {f : Vec d → Vec d}
    (hf : IsAHarmonicGradient (translateCoeffField z a) U f) :
    IsAHarmonicGradient a (translateSet z U) (fun x => f (x - z)) := by
  rcases hf with ⟨hpot, hsol⟩
  constructor
  · exact isPotentialOn_translateSet hpot z
  · simpa [translateCoeffField, sub_eq_add_neg, add_assoc] using
      isSolenoidalOn_translateSet hsol z

namespace AHarmonicFunction

/-- Translate an `a(· + z)`-harmonic function on `U` to an `a`-harmonic
function on `U + z`. -/
noncomputable def translate {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    (z : Vec d) (u : AHarmonicFunction (translateCoeffField z a) U) :
    AHarmonicFunction a (translateSet z U) where
  toH1 := u.toH1.translate z
  isHarmonic := by
    simpa [H1Function.translate] using isAHarmonicGradient_translateSet z u.isHarmonic

@[simp] theorem grad_translate {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    (z : Vec d) (u : AHarmonicFunction (translateCoeffField z a) U) (x : Vec d) :
    (AHarmonicFunction.translate z u).toH1.grad x = u.toH1.grad (x - z) :=
  rfl

end AHarmonicFunction

end Homogenization
