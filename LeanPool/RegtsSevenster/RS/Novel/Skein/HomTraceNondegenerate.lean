/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Skein.SkeinCategory
public import LeanPool.RegtsSevenster.RS.Novel.Skein.TraceNondegenerate

/-!
# Trace nondegeneracy on Hom classes

The accompanying paper's Lemma 3.6, categorified: a Hom-space
class all of whose composition traces vanish is zero.  This is
the input to the semisimplicity of the End algebras (Theorem 4.4)
and the atom dichotomy (Lemma 4.5).
-/

@[expose] public section

namespace RS

variable {R : ℕ} (f : EdgeRankParameter R)

/-- **Zero negligibles on classes** (accompanying paper,
Lemma 3.6): a class all of whose composition traces vanish is
zero. -/
theorem HomSpace.eq_zero_of_traces_vanish {t u : ℕ}
    (q : HomSpace f.val (t + u))
    (hq : ∀ G : Fragment (Fin (u + t)),
      HomSpace.traceMap f.val t
        (HomSpace.comp f t u t q
          (HomSpace.ofFragment f.val G)) = 0) :
    q = 0 := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  have hker : x ∈ LinearMap.ker (connectionMap f.val (t + u)) := by
    refine mem_ker_of_traces_vanish f.val f.iso_invariant x ?_
    intro G
    exact hq G
  change (LinearMap.ker (connectionMap f.val (t + u))).mkQ x = 0
  rw [Submodule.mkQ_apply]
  exact (Submodule.Quotient.mk_eq_zero _).mpr hker

end RS
