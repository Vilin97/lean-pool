/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.CanonColour
public import LeanPool.RegtsSevenster.RS.Classical.Super.ColourFormMatch

/-!
# The Regts–Sevenster functional

The coordinates of the star vectors in the colouring model, and
the mixed functional at the canonical colouring. The accompanying
paper calls this witness `h^ξ` (§5.4). Its mate-based functional
satisfies `h^RS = h^ξ ∘ Sym_s(Ψ)`, where `Ψ` fixes the even basis
and sends `ξ_i` to `η_i`. Lemma 5.6 gives the coordinate dictionary;
Lemma 5.7 proves the change of basis and the invariance of the
partition function under the isometry `Ψ`.
-/

@[expose] public section

namespace RS

variable {R : ℕ} (f : EdgeRankParameter R)
variable (P : DelignePackage (SkeinObj f))
variable {k ℓ : ℕ}
variable (e' : P.ω.obj (SkeinObj.mk 1) ⟶ stdSuperPair k ℓ)

/-- The star coordinate: the vertex star vector transported to
the colouring model, read at a colouring; zero on odd-parity
colourings. -/
noncomputable def starCoord (d : ℕ)
    (c : MixedColouring k ℓ d) : ℂ :=
  if hc : c.IsEven then
    (colourPowerEquiv k ℓ d).evenEquiv
      (((stdFromOmega f P e' d) :
        SuperVect.Hom _ _).evenMap (starVec f P d)) ⟨c, hc⟩
  else 0

/-- Star coordinates vanish on odd-parity colourings. -/
theorem starCoord_odd (d : ℕ) (c : MixedColouring k ℓ d)
    (hc : ¬ c.IsEven) : starCoord f P e' d c = 0 :=
  dite_eq_right hc

/-- **The Regts–Sevenster functional**: the star coordinate at
the canonical colouring, the paper's witness `h^ξ` (§5.4). -/
noncomputable def hRS : MixedFunctional k ℓ := fun μm F =>
  starCoord f P e' (μm.card + F.card) (canonColouring μm F)

/-- The alternating evaluation on a duplicate-free list is the
sorting sign times the star coordinate at the canonical colouring. -/
theorem evalOdd_hRS_nodup (μm : Multiset (Fin k))
    (w : List (Fin (2 * ℓ))) (hw : w.Nodup) :
    (hRS f P e').evalOdd μm w =
      (sortSign w : ℂ) *
        starCoord f P e' (μm.card + w.toFinset.card)
          (canonColouring μm w.toFinset) := by
  unfold MixedFunctional.evalOdd hRS
  rw [ite_eq_left hw]

end RS
