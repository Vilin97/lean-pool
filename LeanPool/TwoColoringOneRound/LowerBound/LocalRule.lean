/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/

import LeanPool.TwoColoringOneRound.LowerBound.Defs
import LeanPool.TwoColoringOneRound.LowerBound.EdgePatterns

/-!
# LeanPool.TwoColoringOneRound.LowerBound.LocalRule
-/

namespace Distributed2Coloring.LowerBound

namespace LocalRule

/-- Local rule from the report: `g(0,0,0)=1`, `g(1,1,1)=0`, otherwise `g(x,y,z)=y`. -/
def g : Bool → Bool → Bool → Bool
  | false, false, false => true
  | true, true, true => false
  | _, y, _ => y

lemma g_eq_iff_patterns (x y z w : Bool) :
    g x y z = g y z w ↔
      (x = false ∧ y = false ∧ z = false ∧ w = false) ∨
      (x = true ∧ y = true ∧ z = true ∧ w = true) ∨
      (x = true ∧ y = false ∧ z = false ∧ w = true) ∨
      (x = false ∧ y = true ∧ z = true ∧ w = false) := by
  cases x <;> cases y <;> cases z <;> cases w <;> decide

theorem monochromatic_iff_patterns {n : Nat} {two : Sym n} (round : Sym n → Bool)
    (hr_true : ∀ a : Sym n, round a = true ↔ two ≤ a)
    (hr_false : ∀ a : Sym n, round a = false ↔ a < two)
    (e : Edge n) :
    Edge.monochromatic
        (fun v => g (round (Vertex.a v)) (round (Vertex.b v)) (round (Vertex.c v))) e
      ↔
        EdgePatterns.Pat0000 (two := two) e ∨
          EdgePatterns.Pat1111 (two := two) e ∨
            EdgePatterns.Pat1001 (two := two) e ∨
              EdgePatterns.Pat0110 (two := two) e := by
  unfold Edge.monochromatic
  simpa [Edge.src, Edge.dst, Vertex.a, Vertex.b, Vertex.c, hr_true, hr_false,
    EdgePatterns.Pat0000, EdgePatterns.Pat1111, EdgePatterns.Pat1001, EdgePatterns.Pat0110]
    using
      (g_eq_iff_patterns (x := round (e.1 0)) (y := round (e.1 1))
        (z := round (e.1 2)) (w := round (e.1 3)))

end LocalRule

end Distributed2Coloring.LowerBound
