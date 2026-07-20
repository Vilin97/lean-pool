/-
Copyright (c) 2026 Alfie Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alfie Davies
-/
module

public import LeanPool.MisereGames.Form.Adjoint
public import LeanPool.MisereGames.Form.Misere.Outcome

/-!
Misere combinatorial games.
-/

namespace MisereGames

universe u

variable {G : Type (u + 1)} [Form G]

open Form
open Form.Misere.Outcome

public section

namespace Form.Misere.Adjoint

/--
`r` is a *root* for `A` if adding it to any `p` end in `A` leaves `p` winning
going first, just as `0` does (`isRoot_zero`). This is what lets the `r`-rooted
adjoint behave like the standard adjoint in
`misereOutcome_add_rootedAdjoint_eq_P`.
-/
abbrev IsRoot (A : G → Prop) (r : G) : Prop :=
  ∀ ⦃p : Player⦄ ⦃d : G⦄, A d → IsEnd p d → WinsGoingFirst p (d + r)

/--
Every zero-like form is a root for every set of forms.
-/
theorem isRoot_of_isZeroLike (A : G → Prop) {r : G} (hr : IsZeroLike r) : IsRoot A r :=
  fun _ _ _ hd => winsGoingFirst_of_isEnd (IsEnd.add_iff.mpr ⟨hd, hr _⟩)

/--
`0` is a root for every set of forms: adding `0` to an end yields an end.
-/
theorem isRoot_zero (A : G → Prop) : IsRoot A (0 : G) :=
  isRoot_of_isZeroLike A isZeroLike_zero

/--
For every form `g` in `A`, the sum `g + rootedAdjoint r g` is a
$\mathscr{P}$-position, provided `r` is a root for the hereditary set `A`
(`IsRoot`).

This generalises `misereOutcome_add_adjoint_eq_P`, which is the case where `A`
is arbitrary and `r = 0`.
-/
theorem misereOutcome_add_rootedAdjoint_eq_P {A : G → Prop} [Hereditary A] {r : G}
    (h_isRoot : IsRoot A r) {g : G} (hg : A g) :
    MisereOutcome (g + rootedAdjoint r g) = Outcome.P := by
  apply misereOutcome_P_of_miserePlayerOutcome_neg
  intro p
  unfold MiserePlayerOutcome
  have h1 : ¬(WinsGoingFirst p (g + rootedAdjoint r g)) := by
    rw [not_winsGoingFirst_iff]
    simp only [IsEndLike.add_iff, Form.Adjoint.rootedAdjoint_not_isEndLike, and_false,
               not_false_eq_true, moves_add, Set.mem_union, Set.mem_image, true_and]
    intro k h1
    apply Or.elim h1 <;> intro ⟨gr, h2, h3⟩ <;> rw [<-h3] <;> clear h1 h3 k
    · have h3 : gr + rootedAdjoint r gr ∈ moves (-p) (gr + rootedAdjoint r g) :=
        add_left_mem_moves_add (Form.Adjoint.mem_rootedAdjoint_mem_opposite h2) gr
      apply winsGoingFirst_of_moves
      use gr + rootedAdjoint r gr, h3
      exact not_winsGoingFirst_of_misereOutcome_P
        (misereOutcome_add_rootedAdjoint_eq_P h_isRoot (Hereditary.of_mem_moves hg h2))
    · by_cases h3 : IsEnd (-p) g
      · have h4 : gr = r := Form.Adjoint.mem_rootedAdjoint_end_opposite h2 h3
        rw [h4]
        exact h_isRoot hg h3
      · apply winsGoingFirst_of_moves
        have ⟨gl, h3, h4⟩ := Form.Adjoint.mem_rootedAdjoint_exists_opposite h2 h3
        rw [h4]
        use gl + rootedAdjoint r gl, add_right_mem_moves_add h3 (rootedAdjoint r gl)
        exact not_winsGoingFirst_of_misereOutcome_P
          (misereOutcome_add_rootedAdjoint_eq_P h_isRoot (Hereditary.of_mem_moves hg h3))
  simp only [h1, reduceIte]
termination_by g
decreasing_by all_goals form_wf

/--
[Siegel, (Proposition 3.3 on p. 228)][siegel:CanonicalPartizan:2015] showed
that, for every short game form $G$, the sum $G+G^\circ$ is always a
$\mathscr{P}$-position. (See also [Siegel, (Proposition 6.4 on p.
270)][siegel:CombinatorialGameTheory:2013].) [Siegel, (Proposition 5.7 on p.
214)][siegel:GeneralDeadendingUniverse:2025] later extended this result to
short augmented forms. The present result generalises further to transfinite
augmented forms.
-/
theorem misereOutcome_add_adjoint_eq_P (g : G) : MisereOutcome (g + g°) = Outcome.P :=
  misereOutcome_add_rootedAdjoint_eq_P (A := IsLong) (isRoot_zero _) (isLong _)

end Form.Misere.Adjoint

end

end MisereGames
