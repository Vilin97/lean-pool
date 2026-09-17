/-
Copyright (c) 2023 PDL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDL formalization contributors (see project card)
-/

import LeanPool.PDL.Interpolation.ClusterInterpolation
import LeanPool.PDL.Interpolation.SingletonCluster

/-! # Defining interpolants (Theorem 8.13)

Here we put together the interpolants for singleton clusters and for proper clusters.
-/

namespace PDL

/-! ## Cluster roots below nodes with a singleton cluster -/

/-- If there is no `◃` cycle at `s`, then all children of `s` are cluster roots.
This is the analogue of `PathIn.isClusterRoot_of_edge_from_free` for loaded nodes that
form a singleton cluster. -/
lemma PathIn.isClusterRoot_of_edge_of_not_proper {X : Sequent} {tab : Tableau .nil X}
    {s t : PathIn tab} (h : ¬ s ◃⁺ s) (s_t : s ⋖_ t) : t.isClusterRoot := by
  intro p p_t t_p
  have p_eq_s : p = s := edge_leftInjective _ _ _ p_t s_t
  have s_c_t : s ◃ t := Or.inl s_t
  exact h (Relation.TransGen.trans_left (Relation.TransGen.single s_c_t) (p_eq_s ▸ t_p))

/-- A loaded path repeat always is in a proper cluster: it has a `♥` step to its companion
and the companion is an ancestor, so it can reach the repeat again. -/
lemma PathIn.proper_of_isLrep {X : Sequent} {tab : Tableau .nil X} {s : PathIn tab}
    (h : s.isLrep) : s ◃⁺ s := by
  rcases h2 : (tabAt s).2.2 with _ | _ | lpr
  case lrep =>
    have heart : s ♥ (companionOf s lpr h2) := ⟨lpr, h2, rfl⟩
    exact Relation.TransGen.head (Or.inr heart)
      (Relation.TransGen.mono (fun _ _ h => Or.inl h) _ _ (companion_lt heart))
  all_goals
    exfalso
    unfold PathIn.isLrep at h
    rw [h2] at h
    simp [Tableau.isLrep] at h

/-! ## From Tableau to Interpolant -/

/-- In a tableau starting with a free sequent at the root,
there exists a `PartInterpolant` for every cluster root in the tableau.

Note the extra hypothesis `s.isClusterRoot`: to interpolate at a loaded node we need to
know that it is the *first* node of its cluster along the branch leading to it, because
otherwise we cannot make a `LoadedCluster`. In particular, this hypothesis holds whenever
the parent of `s` is free (see `PathIn.isClusterRoot_of_edge_from_free`), which is the case
for all children of the free nodes we recurse into below. It also holds for the exits of a
cluster (see `isClusterRoot_of_isExitOf`), which need not have a free parent, but which are
always the first node of their own cluster.

At the root of the tableau the hypothesis is free of charge: `.nil` has no parent at all,
so `PathIn.isClusterRoot_nil` holds vacuously and `tabToInt` below can discharge it. Hence
for that we do not even need the additional assumption that the root sequent `X` is free,
but we do want it inside `clusterInterpolation` later.

Ideally this would be a computable `def` and not an existential.
But currently `PathIn.strong_upwards_inductionOn` only works with `Prop` motive.
-/
theorem tabToIntAt {X : Sequent} (h_free : X.isFree) (tab : Tableau .nil X) (t_u : tab.isUniform)
    (s : PathIn tab) :
    s.isClusterRoot → ∃ θ, isPartInterpolant (nodeAt s) θ := by
  induction s using PathIn.strong_upwards_inductionOn -- Strong!
  next s IH =>
  intro s_cr
  -- case distinction after `induction`.
  by_cases (nodeAt s).isLoaded
  case pos s_loaded =>
    by_cases s ◃⁺ s
    case pos is_proper =>
      -- HARD case, here we want to use `clusterInterpolation` and that is why we used
      -- `PathIn.strong_upwards_inductionOn` to have an IH applicable to "far away" exits.
      -- The exits of the cluster of `s` are proper successors of `s` and are themselves
      -- cluster roots, so the IH is applicable to them.
      have myExitIPs : ∀ e : PathIn tab, isExitOf s e → PartInterpolant (nodeAt e) := by
        intro e e_exit
        have IHe := IH (lt_of_isExitOf s_cr e_exit) (isClusterRoot_of_isExitOf e_exit)
        exact ⟨IHe.choose, IHe.choose_spec⟩
      rcases clusterInterpolation h_free t_u s s_cr is_proper s_loaded myExitIPs with ⟨θ, h_θ⟩
      exact ⟨θ, h_θ⟩
    case neg is_not_proper =>
      -- Here we have a loaded node, but still a singleton cluster.
      -- Hence we do *not* need `clusterInterpolation` and instead recurse into the
      -- children, just like in the EASY `neg s_free` case below. The only difference is
      -- that the children are cluster roots because there is no `◃` cycle at `s`
      -- (instead of because `s` is free) and that we use `loadedPdlRuleInterpolant`
      -- (instead of `freePdlRuleInterpolant`) for the PDL rules.
      rcases s_def : tabAt s with ⟨Hist, Z, s_tab⟩
      cases s_tab_def : s_tab
      case loc nbas ltZ nrep nexts =>
        have endIPsExist : ∀ Y ∈ endNodesOf ltZ, ∃ θ, isPartInterpolant Y θ := by
          intro Y Y_in
          subst s_tab_def
          -- Need to make a path-step to Y, def and proofs about it inspired by `Soundness.lean`
          let s_to_u : PathIn (tabAt s).2.2 :=
            s_def ▸ @PathIn.loc _ _ nrep nbas ltZ nexts Y Y_in .nil
          let u := s.append s_to_u
          have s_u : s ⋖_ u := by
            unfold u s_to_u
            apply edge_append_loc_nil
            grind
          specialize IH (Relation.TransGen.single s_u)
            (PathIn.isClusterRoot_of_edge_of_not_proper is_not_proper s_u)
          have tabAt_u_def : tabAt u = ⟨_, ⟨Y, nexts Y Y_in⟩⟩ := by
            unfold u s_to_u
            rw [tabAt_append]
            have : (tabAt (PathIn.loc Y_in PathIn.nil : PathIn (Tableau.loc nrep nbas ltZ nexts)))
                = ⟨Z :: _, ⟨Y, nexts Y Y_in⟩⟩ := by simp_all
            convert this <;> try rw [s_def]
            rw [eqRec_heq_iff]
          unfold nodeAt at IH
          rw [tabAt_u_def] at IH
          exact IH
        let ltIP := LocalTableau.interpolant ltZ ?endNodeIPsLoaded
        · rcases ltIP with ⟨θ, Z_ip_θ⟩
          use θ
          unfold nodeAt
          rw [s_def]
          simp_all
        · intro Y Y_in
          specialize endIPsExist Y Y_in
          exact ⟨endIPsExist.choose, endIPsExist.choose_spec⟩
      case pdl Y bas r nrep next =>
        subst s_tab_def
        -- The def of `t` here is inspired by the proof of `tableauThenNotSat` (with s/t swapped).
        let s_to_t : PathIn (Tableau.pdl nrep bas r next) := (.pdl .nil)
        let t : PathIn tab := s.append (s_def ▸ s_to_t)
        have s_t : s ⋖_ t := by
            convert @edge_append_pdl_nil .nil _ tab s (s_def ▸ nrep)
                                          (s_def ▸ bas) Y (s_def ▸ r) (s_def ▸ next) ?_ <;> grind
        have def_Y : nodeAt t = Y := by
          simp only [t, s_to_t, nodeAt_append]
          convert @nodeAt_pdl_nil _ _ _ nrep bas next r <;> grind
        specialize IH (Relation.TransGen.single s_t)
          (PathIn.isClusterRoot_of_edge_of_not_proper is_not_proper s_t)
        rw [def_Y] at IH
        unfold nodeAt at s_loaded ⊢
        rw [s_def] at s_loaded ⊢
        exact loadedPdlRuleInterpolant r s_loaded IH
      case lrep lpr =>
        exfalso
        refine is_not_proper (PathIn.proper_of_isLrep ?_)
        unfold PathIn.isLrep
        rw [s_def, s_tab_def]
        trivial
  case neg s_free =>
    -- EASY case, singleton cluster because not loaded.
    have s_isFree : (nodeAt s).isFree := by simp [Sequent.isFree, s_free]
    rcases s_def : tabAt s with ⟨Hist, X, s_tab⟩
    cases s_tab_def : s_tab
    case loc nbas ltX nrep nexts =>
      /- -- Interestingly, we do not *yet* care about the end node being free here.
      have Xfree : X.isFree := by rw [nodeAt, s_def] at s_free; grind [Sequent.isFree]
      have endFree := fun Y => @endNodesOf_free_are_free _ Y ltX Xfree
      -/
      have endIPsExist : ∀ Y ∈ endNodesOf ltX, ∃ θ, isPartInterpolant Y θ := by
        intro Y Y_in
        subst s_tab_def -- hmm?
        -- Need to make a path-step to Y, def and proofs about it inspired by `Soundness.lean`
        let s_to_u : PathIn (tabAt s).2.2 := s_def ▸ @PathIn.loc _ _ nrep nbas ltX nexts Y Y_in .nil
        let u := s.append s_to_u
        have s_u : s ⋖_ u := by
          unfold u s_to_u
          apply edge_append_loc_nil
          grind
        specialize IH (Relation.TransGen.single s_u)
          (PathIn.isClusterRoot_of_edge_from_free s_isFree s_u)
        have tabAt_u_def : tabAt u = ⟨_, ⟨Y, nexts Y Y_in⟩⟩ := by
          unfold u s_to_u
          rw [tabAt_append]
          have : (tabAt (PathIn.loc Y_in PathIn.nil : PathIn (Tableau.loc nrep nbas ltX nexts)))
              = ⟨X :: _, ⟨Y, nexts Y Y_in⟩⟩ := by simp_all
          convert this <;> try rw [s_def]
          rw [eqRec_heq_iff]
        unfold nodeAt at IH
        rw [tabAt_u_def] at IH
        exact IH
      let ltIP := LocalTableau.interpolant ltX ?endNodeIPs
      · rcases ltIP with ⟨θ, X_ip_θ⟩
        use θ
        unfold nodeAt
        rw [s_def]
        simp_all
      · intro Y Y_in
        specialize endIPsExist Y Y_in
        exact ⟨endIPsExist.choose, endIPsExist.choose_spec⟩
    case pdl Y bas r nrep next =>
      subst s_tab_def
      -- The def of `t` here is inspired by the proof of `tableauThenNotSat` (with s/t swapped).
      let s_to_t : PathIn (Tableau.pdl nrep bas r next) := (.pdl .nil)
      let t : PathIn tab := s.append (s_def ▸ s_to_t)
      have s_t : s ⋖_ t := by
          convert @edge_append_pdl_nil .nil _ tab s (s_def ▸ nrep)
                                        (s_def ▸ bas) Y (s_def ▸ r) (s_def ▸ next) ?_ <;> grind
      have def_Y : nodeAt t = Y := by
        simp only [t, s_to_t, nodeAt_append]
        convert @nodeAt_pdl_nil _ _ _ nrep bas next r <;> grind
      specialize IH (Relation.TransGen.single s_t)
        (PathIn.isClusterRoot_of_edge_from_free s_isFree s_t)
      unfold nodeAt at s_free
      rw [s_def] at s_free
      simp only at s_free
      unfold nodeAt
      rw [s_def]
      simp only
      rw [def_Y] at IH
      rcases IH with ⟨θY, θY_ip_Y⟩
      have := freePdlRuleInterpolant r (by grind [Sequent.isFree]) ⟨θY, θY_ip_Y⟩
      rcases this with ⟨θX, θX_ipX⟩
      use θX
    case lrep lpr =>
      exfalso
      absurd s_free
      rw [nodeAt, s_def]
      apply LoadedPathRepeat_rep_isLoaded lpr

theorem tabToInt {X : Sequent} (h_free : X.isFree) (tab : Tableau .nil X) (t_u : tab.isUniform) :
    ∃ θ, isPartInterpolant X θ := tabToIntAt h_free tab t_u .nil PathIn.isClusterRoot_nil

end PDL
