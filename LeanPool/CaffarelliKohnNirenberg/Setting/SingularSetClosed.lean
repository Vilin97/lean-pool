/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Statements.SingularSet
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeSet

/-!
# Relative closedness of the singular set

Paper label `lem:S-closed`: for a suitable weak solution on the space-time
carrier `𝒪 = Ω × I`, the singular set is relatively closed in `𝒪`.  The proof
is the paper's: the regular points form an open set, because the open
neighbourhood that witnesses regularity at one point witnesses it at every
point of that same neighbourhood; the singular set is then the trace on `𝒪`
of the complement, a closed set.
-/

@[expose] public section

open Set Filter


noncomputable section

open CKN.Foundation.Parabolic

namespace CKN

/-- Paper label `lem:S-closed`: the set of regular points is open.  If `z₀` is
regular, the open set `N` supplied by `def:regular` consists of regular points,
because it is contained in `spaceTimeSet Ω I` and its witness `w` and exponent
`γ` serve every point of `N` equally. -/
theorem isOpen_regularSet (Ω : Set Vec3) (I : Set ℝ)
    (u : ParabolicPoint → Vec3) : IsOpen {z | IsRegularPoint Ω I u z} := by
  rw [isOpen_iff_mem_nhds]
  rintro z ⟨_, N, hNopen, hzN, hNsub, γ, hγ, hγ1, w, hwu, hholder⟩
  refine mem_of_superset (hNopen.mem_nhds hzN) ?_
  intro z₁ hz₁
  exact ⟨hNsub hz₁, N, hNopen, hz₁, hNsub, γ, hγ, hγ1, w, hwu, hholder⟩

/-- Paper label `def:regular`: the singular set is the complement of the
regular set inside the space-time carrier `spaceTimeSet Ω I`. -/
theorem singularSet_eq_diff (Ω : Set Vec3) (I : Set ℝ)
    (u : ParabolicPoint → Vec3) :
    SingularSet Ω I u = spaceTimeSet Ω I \ {z | IsRegularPoint Ω I u z} := by
  ext z
  simp only [SingularSet, Set.mem_ofPred_eq, Set.mem_sdiff]

/-- Paper label `lem:S-closed`: the singular set is relatively closed in the
space-time carrier `spaceTimeSet Ω I`, that is, it is the trace on the carrier
of a closed set.  The closed set is the complement of the regular set. -/
theorem isClosed_singularSet_within (Ω : Set Vec3) (I : Set ℝ)
    (u : ParabolicPoint → Vec3) :
    ∃ C : Set ParabolicPoint, IsClosed C ∧
      SingularSet Ω I u = C ∩ spaceTimeSet Ω I := by
  refine ⟨{z | ¬ IsRegularPoint Ω I u z},
    (isOpen_regularSet Ω I u).isClosed_compl, ?_⟩
  rw [singularSet_eq_diff]
  ext z
  simp only [Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_inter_iff]
  tauto

end CKN
