/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Skein.StrandBundle

/-!
# Composition respects fragment equivalence

Interface gluing and composition are congruences for the
relabelling equivalence of fragments: equivalent inputs glue to
equivalent outputs.  These are the transport lemmas through which
every up-to-isomorphism identity about composition is proved.
-/

@[expose] public section

namespace RS

/-- Interface gluing respects fragment equivalence. -/
noncomputable def glueInterfaceCongr (s : ℕ) :
    (t : ℕ) → (u : ℕ) → {W₁ W₂ : Fragment (Fin (s + t) ⊕ Fin (t + u))} →
      W₁.Equiv W₂ →
      (glueInterface s t u W₁).Equiv (glueInterface s t u W₂)
  | 0, _, _, _, h => Fragment.Equiv.relabelCongr h _
  | t + 1, u, W₁, W₂, h =>
      glueInterfaceCongr s t u
        (Fragment.Equiv.relabelCongr
          (Fragment.Equiv.gluePairCongr h (by simp)) (interfaceStepEquiv s t
            u))

/-- Composition respects fragment equivalence in both arguments. -/
noncomputable def Fragment.composeCongr {s t u : ℕ}
    {F₁ F₂ : Fragment (Fin (s + t))} {G₁ G₂ : Fragment (Fin (t + u))}
    (hF : F₁.Equiv F₂) (hG : G₁.Equiv G₂) :
    (F₁.compose G₁).Equiv (F₂.compose G₂) :=
  Fragment.Equiv.relabelCongr
    (glueInterfaceCongr s t u (Fragment.Equiv.disjUnionCongr hF hG))
    finSumFinEquiv

end RS
