/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.GlueSubsetBij

/-!
# Transport of transition data across a single-pair glue

For `W' := W.gluePair i j hij` (in either the open or the closed
case) the internal flags of a glued edge subset `EdgeSubset.mk s'`
correspond to the internal flags of the lifted edge subset
(`liftSubsetOpen` / `liftSubsetClosed`) via `Subtype.val`: gluing
touches only the two boundary flags, and internal flags are
attached to vertices.

Along this correspondence we transport boundary-relative
transition systems (`RelTransitionSystem.unglueOpen/glueOpen`,
`unglueClosed/glueClosed`) and their orientations in both
directions, prove the round trips on `match_` pointwise at
internal flags, relate the walk steps (`iterWalk`-style
`match_ ∘ pairing`) away from the glued interface, record the
exact rewired step at the interface (what the circuit-count delta
of `GlueCircuitDelta.lean` reads), and prove that
`openCircuitCount` is stable under the transport when the glued
edge's flags do not participate.
-/

namespace RS



namespace Fragment

variable {α : Type} {W : Fragment α} {i j : α}

/-! ### Rewire evaluation lemmas -/

/-- Away from the glued interface, `rewire` agrees with the
original pairing. -/
theorem rewire_val_of_ne
    (hopen : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j)
    (f : SurvivingFlag W i j)
    (h1 : W.pairing f.val ≠ W.boundaryFlag i)
    (h2 : W.pairing f.val ≠ W.boundaryFlag j) :
    (rewire hopen f).val = W.pairing f.val := by
  unfold rewire
  rw [dite_eq_right h1, dite_eq_right h2]

/-- At the `i`-side of the interface, `rewire` jumps to the far
end of the `j`-edge. -/
theorem rewire_eq_partnerSurvJ
    (hopen : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j)
    (f : SurvivingFlag W i j)
    (h : W.pairing f.val = W.boundaryFlag i) :
    rewire hopen f = partnerSurvJ hopen := by
  unfold rewire
  rw [dite_eq_left h]
  rfl

/-- At the `j`-side of the interface, `rewire` jumps to the far
end of the `i`-edge. -/
theorem rewire_eq_partnerSurvI
    (hopen : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j)
    (f : SurvivingFlag W i j)
    (hne : W.pairing f.val ≠ W.boundaryFlag i)
    (h : W.pairing f.val = W.boundaryFlag j) :
    rewire hopen f = partnerSurvI hopen := by
  unfold rewire
  rw [dite_eq_right hne, dite_eq_left h]
  rfl

/-- A surviving flag whose pairing is the `i`-boundary flag is the
far end of the `i`-edge. -/
theorem eq_partnerSurvI_of_pairing
    (hopen : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j)
    (f : SurvivingFlag W i j)
    (h : W.pairing f.val = W.boundaryFlag i) :
    f = partnerSurvI hopen := by
  refine Subtype.ext ?_
  have h' := congrArg W.pairing h
  rwa [W.pairing_invol] at h'

/-- A surviving flag whose pairing is the `j`-boundary flag is the
far end of the `j`-edge. -/
theorem eq_partnerSurvJ_of_pairing
    (hopen : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j)
    (f : SurvivingFlag W i j)
    (h : W.pairing f.val = W.boundaryFlag j) :
    f = partnerSurvJ hopen := by
  refine Subtype.ext ?_
  have h' := congrArg W.pairing h
  rwa [W.pairing_invol] at h'

end Fragment

namespace EdgeSubset

open Fragment

variable {α : Type} {W : Fragment α} {i j : α}

/-! ### Generic transport helpers -/

/-- An internal flag of any edge subset of `W` survives a glue at
`{i, j}`: it is attached to a vertex, hence is no boundary flag. -/
theorem internal_surviving (i j : α) {F : EdgeSubset W}
    {f : W.Flag} (hf : f ∈ F.internalFlags) :
    f ≠ W.boundaryFlag i ∧ f ≠ W.boundaryFlag j := by
  obtain ⟨v, hv⟩ := attach_internal_of_mem F hf
  exact vertex_flag_surviving f v hv

/-- Extend a surviving-flag self-map to all of `W.Flag`:
apply it through the subtype on surviving flags, identity
elsewhere. -/
noncomputable def unglueMatch
    (m : SurvivingFlag W i j → SurvivingFlag W i j)
    (f : W.Flag) : W.Flag :=
  if h : f ≠ W.boundaryFlag i ∧ f ≠ W.boundaryFlag j then
    (m ⟨f, h⟩).val
  else f

/-- The unglued matching at a surviving flag is the glued matching
read through `Subtype.val`. -/
theorem unglueMatch_of_surviving
    (m : SurvivingFlag W i j → SurvivingFlag W i j)
    (f : W.Flag)
    (h : f ≠ W.boundaryFlag i ∧ f ≠ W.boundaryFlag j) :
    unglueMatch m f = (m ⟨f, h⟩).val := by
  unfold unglueMatch
  rw [dite_eq_left h]

/-- The same, stated on a surviving flag's underlying flag. -/
theorem unglueMatch_val
    (m : SurvivingFlag W i j → SurvivingFlag W i j)
    (g : SurvivingFlag W i j) :
    unglueMatch m g.val = (m g).val := by
  unfold unglueMatch
  rw [dite_eq_left g.prop]

/-- Restrict a flag self-map of `W` to the surviving flags on a
given internal-flag set: apply it through `Subtype.val` there
(with a supplied surviving-ness certificate), identity
elsewhere. -/
noncomputable def glueMatch (m : W.Flag → W.Flag)
    (P : Finset (SurvivingFlag W i j))
    (hP : ∀ f' ∈ P, m f'.val ≠ W.boundaryFlag i ∧
      m f'.val ≠ W.boundaryFlag j)
    (f' : SurvivingFlag W i j) : SurvivingFlag W i j :=
  if h : f' ∈ P then ⟨m f'.val, hP f' h⟩ else f'

/-- The glued matching on the flags it is defined at agrees with the
matching it came from. -/
theorem glueMatch_val_of_mem (m : W.Flag → W.Flag)
    (P : Finset (SurvivingFlag W i j))
    (hP : ∀ f' ∈ P, m f'.val ≠ W.boundaryFlag i ∧
      m f'.val ≠ W.boundaryFlag j)
    {f' : SurvivingFlag W i j} (h : f' ∈ P) :
    (glueMatch m P hP f').val = m f'.val := by
  unfold glueMatch
  rw [dite_eq_left h]

/-- Extend a surviving-flag orientation to all of `W.Flag`:
through the subtype on surviving flags, `false` elsewhere. -/
noncomputable def unglueIsOut
    (b : SurvivingFlag W i j → Bool) (f : W.Flag) : Bool :=
  if h : f ≠ W.boundaryFlag i ∧ f ≠ W.boundaryFlag j then
    b ⟨f, h⟩
  else false

/-- The unglued orientation at a surviving flag. -/
theorem unglueIsOut_of_surviving
    (b : SurvivingFlag W i j → Bool) (f : W.Flag)
    (h : f ≠ W.boundaryFlag i ∧ f ≠ W.boundaryFlag j) :
    unglueIsOut b f = b ⟨f, h⟩ := by
  unfold unglueIsOut
  rw [dite_eq_left h]

/-- The same, stated on a surviving flag's underlying flag. -/
theorem unglueIsOut_val
    (b : SurvivingFlag W i j → Bool) (g : SurvivingFlag W i j) :
    unglueIsOut b g.val = b g := by
  unfold unglueIsOut
  rw [dite_eq_left g.prop]

/-! ### The open case -/

section OpenGlue

variable (hij : i ≠ j)
  (hopen : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j)
  (s' : Finset (SurvivingFlag W i j))
  (hc' : ∀ f ∈ s', (W.gluePairOpen i j hij hopen).pairing f ∈ s')
  (hc : ∀ f ∈ liftSubsetOpen hopen s',
    W.pairing f ∈ liftSubsetOpen hopen s')

/-- The glued edge subset (with the fragment ascribed, since the
constructor cannot infer it from `s'` alone). -/
local notation "Fg" =>
  (EdgeSubset.mk s' hc' : EdgeSubset (W.gluePairOpen i j hij hopen))

/-- The lifted edge subset. -/
local notation "Fl" =>
  (EdgeSubset.mk (liftSubsetOpen hopen s') hc : EdgeSubset W)

/-! #### Internal-flag correspondence (open case) -/

/-- **Internal-flag correspondence (open case)**: the internal
flags of the glued subset and of the lifted subset correspond via
`Subtype.val`. -/
theorem mem_internalFlags_glueOpen {f' : SurvivingFlag W i j} :
    f' ∈ (Fg).internalFlags ↔
      f'.val ∈ (Fl).internalFlags := by
  constructor
  · intro h
    obtain ⟨v, hv⟩ := attach_internal_of_mem _ h
    refine mem_internalFlags_of ?_ ⟨v, (glueAttach_inl_iff f' v).mp hv⟩
    exact (surviving_val_mem_liftOpen_iff hopen s' f').mpr
      (mem_flags_of_internalFlags _ h)
  · intro h
    obtain ⟨v, hv⟩ := attach_internal_of_mem _ h
    refine mem_internalFlags_of ?_ ⟨v, (glueAttach_inl_iff f' v).mpr hv⟩
    exact (surviving_val_mem_liftOpen_iff hopen s' f').mp
      (mem_flags_of_internalFlags _ h)

/-- Forward direction of the correspondence, `val` form. -/
theorem internal_val_of_glueOpen {f' : SurvivingFlag W i j}
    (hf' : f' ∈ (Fg).internalFlags) :
    f'.val ∈ (Fl).internalFlags :=
  (mem_internalFlags_glueOpen hij hopen s' hc' hc).mp hf'

/-- Backward direction of the correspondence, `mk` form. -/
theorem internal_mk_of_glueOpen {f : W.Flag}
    (hf : f ∈ (Fl).internalFlags)
    (h1 : f ≠ W.boundaryFlag i) (h2 : f ≠ W.boundaryFlag j) :
    (⟨f, h1, h2⟩ : SurvivingFlag W i j) ∈ (Fg).internalFlags :=
  (mem_internalFlags_glueOpen hij hopen s' hc' hc).mpr hf

/-! #### Transition transport (open case) -/

/-- **Unglue (open case)**: transport a transition system on the
glued subset to the lifted subset.  The matching acts through the
surviving-flag subtype; identity junk at the two glued boundary
flags. -/
noncomputable def RelTransitionSystem.unglueOpen
    (κ' : (Fg).RelTransitionSystem) :
    (Fl).RelTransitionSystem where
  match_ := unglueMatch κ'.match_
  match_invol := by
    intro f hf
    obtain ⟨h1, h2⟩ := internal_surviving i j hf
    have hg := internal_mk_of_glueOpen hij hopen s' hc' hc hf h1 h2
    calc unglueMatch κ'.match_ (unglueMatch κ'.match_ f)
        = unglueMatch κ'.match_ (κ'.match_ ⟨f, h1, h2⟩).val := by
          rw [unglueMatch_of_surviving κ'.match_ f ⟨h1, h2⟩]
      _ = (κ'.match_ (κ'.match_ ⟨f, h1, h2⟩)).val :=
          unglueMatch_val κ'.match_ _
      _ = f := by rw [κ'.match_invol _ hg]
  match_ne := by
    intro f hf heq
    obtain ⟨h1, h2⟩ := internal_surviving i j hf
    have hg := internal_mk_of_glueOpen hij hopen s' hc' hc hf h1 h2
    rw [unglueMatch_of_surviving κ'.match_ f ⟨h1, h2⟩] at heq
    exact κ'.match_ne _ hg (Subtype.ext heq)
  match_mem := by
    intro f hf
    obtain ⟨h1, h2⟩ := internal_surviving i j hf
    have hg := internal_mk_of_glueOpen hij hopen s' hc' hc hf h1 h2
    rw [unglueMatch_of_surviving κ'.match_ f ⟨h1, h2⟩]
    exact internal_val_of_glueOpen hij hopen s' hc' hc
      (κ'.match_mem _ hg)
  match_vertex := by
    intro f hf v hv
    obtain ⟨h1, h2⟩ := internal_surviving i j hf
    have hg := internal_mk_of_glueOpen hij hopen s' hc' hc hf h1 h2
    rw [unglueMatch_of_surviving κ'.match_ f ⟨h1, h2⟩]
    exact (glueAttach_inl_iff (κ'.match_ ⟨f, h1, h2⟩) v).mp
      (κ'.match_vertex _ hg v
        ((glueAttach_inl_iff (⟨f, h1, h2⟩ : SurvivingFlag W i j)
          v).mpr hv))

/-- The open ungluing's matching at a surviving flag. -/
theorem unglueOpen_match_of_surviving
    (κ' : (Fg).RelTransitionSystem) (f : W.Flag)
    (h : f ≠ W.boundaryFlag i ∧ f ≠ W.boundaryFlag j) :
    (RelTransitionSystem.unglueOpen hij hopen s' hc' hc κ').match_
      f = (κ'.match_ ⟨f, h⟩).val :=
  unglueMatch_of_surviving κ'.match_ f h

/-- The same on a surviving flag's underlying flag. -/
theorem unglueOpen_match_val
    (κ' : (Fg).RelTransitionSystem) (g : SurvivingFlag W i j) :
    (RelTransitionSystem.unglueOpen hij hopen s' hc' hc κ').match_
      g.val = (κ'.match_ g).val :=
  unglueMatch_val κ'.match_ g

/-- The surviving-ness certificate for restricting a lifted-side
matching to the glued subset. -/
theorem glueOpen_cert
    (κ : (Fl).RelTransitionSystem) :
    ∀ f' ∈ (Fg).internalFlags,
      κ.match_ f'.val ≠ W.boundaryFlag i ∧
        κ.match_ f'.val ≠ W.boundaryFlag j :=
  fun _ h => internal_surviving i j (κ.match_mem _
    (internal_val_of_glueOpen hij hopen s' hc' hc h))

/-- **Glue (open case)**: restrict a transition system on the
lifted subset to the glued subset. -/
noncomputable def RelTransitionSystem.glueOpen
    (κ : (Fl).RelTransitionSystem) :
    (Fg).RelTransitionSystem where
  match_ := glueMatch κ.match_ (Fg).internalFlags
    (glueOpen_cert hij hopen s' hc' hc κ)
  match_invol := by
    intro f' hf'
    have hval := glueMatch_val_of_mem κ.match_ (Fg).internalFlags
      (glueOpen_cert hij hopen s' hc' hc κ) hf'
    have hm2 : glueMatch κ.match_ (Fg).internalFlags
        (glueOpen_cert hij hopen s' hc' hc κ) f' ∈
        (Fg).internalFlags := by
      refine (mem_internalFlags_glueOpen hij hopen s' hc' hc).mpr ?_
      rw [hval]
      exact κ.match_mem _
        (internal_val_of_glueOpen hij hopen s' hc' hc hf')
    refine Subtype.ext ?_
    rw [glueMatch_val_of_mem κ.match_ (Fg).internalFlags
      (glueOpen_cert hij hopen s' hc' hc κ) hm2, hval]
    exact κ.match_invol _
      (internal_val_of_glueOpen hij hopen s' hc' hc hf')
  match_ne := by
    intro f' hf' heq
    refine κ.match_ne f'.val
      (internal_val_of_glueOpen hij hopen s' hc' hc hf') ?_
    have h2 := congrArg Subtype.val heq
    rwa [glueMatch_val_of_mem κ.match_ (Fg).internalFlags
      (glueOpen_cert hij hopen s' hc' hc κ) hf'] at h2
  match_mem := by
    intro f' hf'
    refine (mem_internalFlags_glueOpen hij hopen s' hc' hc).mpr ?_
    rw [glueMatch_val_of_mem κ.match_ (Fg).internalFlags
      (glueOpen_cert hij hopen s' hc' hc κ) hf']
    exact κ.match_mem _
      (internal_val_of_glueOpen hij hopen s' hc' hc hf')
  match_vertex := by
    intro f' hf' v hv
    refine (glueAttach_inl_iff
      (glueMatch κ.match_ (Fg).internalFlags
        (glueOpen_cert hij hopen s' hc' hc κ) f') v).mpr ?_
    rw [glueMatch_val_of_mem κ.match_ (Fg).internalFlags
      (glueOpen_cert hij hopen s' hc' hc κ) hf']
    exact κ.match_vertex f'.val
      (internal_val_of_glueOpen hij hopen s' hc' hc hf') v
      ((glueAttach_inl_iff f' v).mp hv)

/-- The open gluing's matching at an internal flag: the round trip
agrees with the system it started from. -/
theorem glueOpen_match_val
    (κ : (Fl).RelTransitionSystem)
    {f' : SurvivingFlag W i j}
    (hf' : f' ∈ (Fg).internalFlags) :
    ((RelTransitionSystem.glueOpen hij hopen s' hc' hc κ).match_
      f').val = κ.match_ f'.val :=
  glueMatch_val_of_mem κ.match_ (Fg).internalFlags
    (glueOpen_cert hij hopen s' hc' hc κ) hf'

/-! #### Round trips (open case) -/

/-- Round trip lifted → glued → lifted: `match_` agrees pointwise
at internal flags. -/
theorem unglueOpen_glueOpen_match
    (κ : (Fl).RelTransitionSystem)
    {f : W.Flag}
    (hf : f ∈ (Fl).internalFlags) :
    (RelTransitionSystem.unglueOpen hij hopen s' hc' hc
      (RelTransitionSystem.glueOpen hij hopen s' hc' hc κ)).match_
        f = κ.match_ f := by
  obtain ⟨h1, h2⟩ := internal_surviving i j hf
  have hg := internal_mk_of_glueOpen hij hopen s' hc' hc hf h1 h2
  rw [unglueOpen_match_of_surviving hij hopen s' hc' hc _ f
    ⟨h1, h2⟩]
  exact glueOpen_match_val hij hopen s' hc' hc κ hg

/-! #### Orientation transport (open case) -/

/-- **Unglue an orientation (open case)**: through the subtype on
surviving flags, `false` junk at the two glued boundary flags
(which are never internal, so the structure fields do not
constrain them). -/
noncomputable def unglueOrientationOpen
    (κ' : (Fg).RelTransitionSystem) (o' : κ'.Orientation) :
    (RelTransitionSystem.unglueOpen hij hopen s' hc' hc
      κ').Orientation where
  isOut := unglueIsOut o'.isOut
  match_flip := by
    intro f hf
    obtain ⟨h1, h2⟩ := internal_surviving i j hf
    have hg := internal_mk_of_glueOpen hij hopen s' hc' hc hf h1 h2
    rw [unglueOpen_match_of_surviving hij hopen s' hc' hc κ' f
        ⟨h1, h2⟩,
      unglueIsOut_val o'.isOut (κ'.match_ ⟨f, h1, h2⟩),
      unglueIsOut_of_surviving o'.isOut f ⟨h1, h2⟩]
    exact o'.match_flip _ hg
  pairing_flip := by
    intro f hf hpf
    obtain ⟨h1, h2⟩ := internal_surviving i j hf
    obtain ⟨hp1, hp2⟩ := internal_surviving i j hpf
    have hg := internal_mk_of_glueOpen hij hopen s' hc' hc hf h1 h2
    have hpg := internal_mk_of_glueOpen hij hopen s' hc' hc hpf
      hp1 hp2
    have hrw : (W.gluePairOpen i j hij hopen).pairing ⟨f, h1, h2⟩ =
        (⟨W.pairing f, hp1, hp2⟩ : SurvivingFlag W i j) :=
      Subtype.ext (rewire_val_of_ne hopen ⟨f, h1, h2⟩ hp1 hp2)
    rw [unglueIsOut_of_surviving o'.isOut (W.pairing f) ⟨hp1, hp2⟩,
      unglueIsOut_of_surviving o'.isOut f ⟨h1, h2⟩]
    have hflip := o'.pairing_flip ⟨f, h1, h2⟩ hg
      (by rw [hrw]; exact hpg)
    rwa [hrw] at hflip

/-- **Glue an orientation (open case)**: through `Subtype.val`.
The rewired pairing crosses the interface, so a flip-compatibility
hypothesis between the two far ends is required (it is vacuous
when the interface edges do not participate). -/
noncomputable def glueOrientationOpen
    (κ : (Fl).RelTransitionSystem) (o : κ.Orientation)
    (hcompat : o.isOut (W.pairing (W.boundaryFlag j)) =
      !o.isOut (W.pairing (W.boundaryFlag i))) :
    (RelTransitionSystem.glueOpen hij hopen s' hc' hc
      κ).Orientation where
  isOut := fun f' => o.isOut f'.val
  match_flip := by
    intro f' hf'
    rw [glueOpen_match_val hij hopen s' hc' hc κ hf']
    exact o.match_flip f'.val
      (internal_val_of_glueOpen hij hopen s' hc' hc hf')
  pairing_flip := by
    intro f' hf' hpf'
    by_cases hi' : W.pairing f'.val = W.boundaryFlag i
    · have hrw : (W.gluePairOpen i j hij hopen).pairing f' =
          partnerSurvJ hopen :=
        rewire_eq_partnerSurvJ hopen f' hi'
      have hfv : f'.val = W.pairing (W.boundaryFlag i) := by
        have h' := congrArg W.pairing hi'
        rwa [W.pairing_invol] at h'
      rw [hrw, partnerSurvJ_val hopen, hfv]
      exact hcompat
    · by_cases hj' : W.pairing f'.val = W.boundaryFlag j
      · have hrw : (W.gluePairOpen i j hij hopen).pairing f' =
            partnerSurvI hopen :=
          rewire_eq_partnerSurvI hopen f' hi' hj'
        have hfv : f'.val = W.pairing (W.boundaryFlag j) := by
          have h' := congrArg W.pairing hj'
          rwa [W.pairing_invol] at h'
        rw [hrw, partnerSurvI_val hopen, hfv, hcompat,
          Bool.not_not]
      · have hrw : (W.gluePairOpen i j hij hopen).pairing f' =
            (⟨W.pairing f'.val, hi', hj'⟩ : SurvivingFlag W i j) :=
          Subtype.ext (rewire_val_of_ne hopen f' hi' hj')
        rw [hrw]
        refine o.pairing_flip f'.val
          (internal_val_of_glueOpen hij hopen s' hc' hc hf') ?_
        have h2 := internal_val_of_glueOpen hij hopen s' hc' hc
          hpf'
        rw [hrw] at h2
        exact h2

/-! #### Walk-step agreement (open case) -/

/-- The glued pairing at projection level, away from the
interface. -/
theorem gluePairOpen_pairing_val_of_ne (f' : SurvivingFlag W i j)
    (h1 : W.pairing f'.val ≠ W.boundaryFlag i)
    (h2 : W.pairing f'.val ≠ W.boundaryFlag j) :
    ((W.gluePairOpen i j hij hopen).pairing f').val =
      W.pairing f'.val :=
  rewire_val_of_ne hopen f' h1 h2

/-- **Walk-step agreement (open case, glue direction)**: when the
lifted pairing target is internal, the glued walk step projects to
the lifted walk step. -/
theorem glueOpen_step_agrees
    (κ : (Fl).RelTransitionSystem) (f' : SurvivingFlag W i j)
    (hp : W.pairing f'.val ∈ (Fl).internalFlags) :
    ((RelTransitionSystem.glueOpen hij hopen s' hc' hc κ).match_
      ((W.gluePairOpen i j hij hopen).pairing f')).val =
      κ.match_ (W.pairing f'.val) := by
  obtain ⟨hp1, hp2⟩ := internal_surviving i j hp
  have hrw : (W.gluePairOpen i j hij hopen).pairing f' =
      (⟨W.pairing f'.val, hp1, hp2⟩ : SurvivingFlag W i j) :=
    Subtype.ext (rewire_val_of_ne hopen f' hp1 hp2)
  rw [hrw, glueOpen_match_val hij hopen s' hc' hc κ
    (internal_mk_of_glueOpen hij hopen s' hc' hc hp hp1 hp2)]

/-! #### The interface (open case): the rewired step -/

/-- The glued pairing at the `i`-side of the interface, projection
level. -/
theorem gluePairOpen_pairing_interface_i (f' : SurvivingFlag W i j)
    (h : W.pairing f'.val = W.boundaryFlag i) :
    (W.gluePairOpen i j hij hopen).pairing f' =
      partnerSurvJ hopen :=
  rewire_eq_partnerSurvJ hopen f' h

/-- The glued pairing at the `j`-side of the interface, projection
level. -/
theorem gluePairOpen_pairing_interface_j (f' : SurvivingFlag W i j)
    (hne : W.pairing f'.val ≠ W.boundaryFlag i)
    (h : W.pairing f'.val = W.boundaryFlag j) :
    (W.gluePairOpen i j hij hopen).pairing f' =
      partnerSurvI hopen :=
  rewire_eq_partnerSurvI hopen f' hne h

/-! #### `openCircuitCount` stability (open case, interface not in
the subset) -/

include hc' in
/-- When the far end of the `i`-edge is absent, so is the far end
of the `j`-edge (by closure under the glued pairing). -/
theorem partnerSurvJ_notMem_of
    (hni : partnerSurvI hopen ∉ s') :
    partnerSurvJ hopen ∉ s' := by
  intro hmem
  apply hni
  have h := hc' _ hmem
  have hrw : (W.gluePairOpen i j hij hopen).pairing
      (partnerSurvJ hopen) = partnerSurvI hopen := by
    refine gluePairOpen_pairing_interface_j hij hopen _ ?_ ?_
    · rw [partnerSurvJ_val hopen, W.pairing_invol]
      exact fun hh => hij (W.boundaryFlag_injective hh).symm
    · rw [partnerSurvJ_val hopen, W.pairing_invol]
  rwa [hrw] at h

include hc' in
/-- When the interface is not in the subset, the glued pairing
agrees with the `W`-pairing on all subset flags. -/
theorem gluePairOpen_pairing_val_of_notMem_interface
    (hni : partnerSurvI hopen ∉ s')
    {g : SurvivingFlag W i j} (hg : g ∈ s') :
    ((W.gluePairOpen i j hij hopen).pairing g).val =
      W.pairing g.val := by
  refine gluePairOpen_pairing_val_of_ne hij hopen g ?_ ?_
  · intro hh
    exact hni (eq_partnerSurvI_of_pairing hopen g hh ▸ hg)
  · intro hh
    exact partnerSurvJ_notMem_of hij hopen s' hc' hni
      (eq_partnerSurvJ_of_pairing hopen g hh ▸ hg)

/-- Walk correspondence (glued-side continuation data): the lifted
walk is the projection of the glued walk, and the glued iterates
stay internal. -/
theorem iterWalk_unglueOpen
    (hni : partnerSurvI hopen ∉ s')
    (κ' : (Fg).RelTransitionSystem) {g : SurvivingFlag W i j}
    (hg : g ∈ (Fg).internalFlags) (n : ℕ)
    (hcont : ∀ m, m < n → (W.gluePairOpen i j hij hopen).pairing
      (iterWalk κ' g m) ∈ (Fg).internalFlags) :
    ∀ k, k ≤ n →
      iterWalk (RelTransitionSystem.unglueOpen hij hopen s' hc' hc
        κ') g.val k = (iterWalk κ' g k).val ∧
      iterWalk κ' g k ∈ (Fg).internalFlags := by
  intro k
  induction k with
  | zero => exact fun _ => ⟨rfl, hg⟩
  | succ k ih =>
    intro hk
    obtain ⟨hval, hmem⟩ := ih (by omega)
    have hp := hcont k (by omega)
    refine ⟨?_, ?_⟩
    · change (RelTransitionSystem.unglueOpen hij hopen s' hc' hc
          κ').match_ (W.pairing (iterWalk
            (RelTransitionSystem.unglueOpen hij hopen s' hc' hc
              κ') g.val k)) =
        (κ'.match_ ((W.gluePairOpen i j hij hopen).pairing
          (iterWalk κ' g k))).val
      rw [hval]
      have hag : W.pairing (iterWalk κ' g k).val =
          ((W.gluePairOpen i j hij hopen).pairing
            (iterWalk κ' g k)).val :=
        (gluePairOpen_pairing_val_of_notMem_interface hij hopen s'
          hc' hni (mem_flags_of_internalFlags _ hmem)).symm
      rw [hag, unglueOpen_match_val hij hopen s' hc' hc κ'
        ((W.gluePairOpen i j hij hopen).pairing (iterWalk κ' g k))]
    · exact κ'.match_mem _ hp

/-- Walk correspondence (lifted-side continuation data): the
converse bookkeeping, with the glued pairing-internality
reconstructed step by step. -/
theorem iterWalk_unglueOpen_rev
    (hni : partnerSurvI hopen ∉ s')
    (κ' : (Fg).RelTransitionSystem) {g : SurvivingFlag W i j}
    (hg : g ∈ (Fg).internalFlags) (n : ℕ)
    (hcontW : ∀ m, m < n → W.pairing (iterWalk
      (RelTransitionSystem.unglueOpen hij hopen s' hc' hc κ')
      g.val m) ∈ (Fl).internalFlags) :
    ∀ k, k ≤ n →
      iterWalk (RelTransitionSystem.unglueOpen hij hopen s' hc' hc
        κ') g.val k = (iterWalk κ' g k).val ∧
      iterWalk κ' g k ∈ (Fg).internalFlags ∧
      (k < n → (W.gluePairOpen i j hij hopen).pairing
        (iterWalk κ' g k) ∈ (Fg).internalFlags) := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨rfl, hg, ?_⟩
    intro h0
    have hpW := hcontW 0 h0
    rw [iterWalk_zero] at hpW
    have hag : ((W.gluePairOpen i j hij hopen).pairing g).val =
        W.pairing g.val :=
      gluePairOpen_pairing_val_of_notMem_interface hij hopen s'
        hc' hni (mem_flags_of_internalFlags _ hg)
    change (W.gluePairOpen i j hij hopen).pairing g ∈
      (Fg).internalFlags
    refine (mem_internalFlags_glueOpen hij hopen s' hc' hc).mpr ?_
    rw [hag]
    exact hpW
  | succ k ih =>
    intro hk
    obtain ⟨hval, hmem, hpair⟩ := ih (by omega)
    have hpG : (W.gluePairOpen i j hij hopen).pairing
        (iterWalk κ' g k) ∈ (Fg).internalFlags :=
      hpair (by omega)
    have hmem1 : iterWalk κ' g (k + 1) ∈ (Fg).internalFlags :=
      κ'.match_mem _ hpG
    have hstep : iterWalk (RelTransitionSystem.unglueOpen hij
        hopen s' hc' hc κ') g.val (k + 1) =
        (iterWalk κ' g (k + 1)).val := by
      change (RelTransitionSystem.unglueOpen hij hopen s' hc' hc
          κ').match_ (W.pairing (iterWalk
            (RelTransitionSystem.unglueOpen hij hopen s' hc' hc
              κ') g.val k)) =
        (κ'.match_ ((W.gluePairOpen i j hij hopen).pairing
          (iterWalk κ' g k))).val
      rw [hval]
      have hag : W.pairing (iterWalk κ' g k).val =
          ((W.gluePairOpen i j hij hopen).pairing
            (iterWalk κ' g k)).val :=
        (gluePairOpen_pairing_val_of_notMem_interface hij hopen s'
          hc' hni (mem_flags_of_internalFlags _ hmem)).symm
      rw [hag, unglueOpen_match_val hij hopen s' hc' hc κ'
        ((W.gluePairOpen i j hij hopen).pairing (iterWalk κ' g k))]
    refine ⟨hstep, hmem1, ?_⟩
    intro hk1
    have hpW := hcontW (k + 1) hk1
    rw [hstep] at hpW
    have hag : ((W.gluePairOpen i j hij hopen).pairing
        (iterWalk κ' g (k + 1))).val =
        W.pairing (iterWalk κ' g (k + 1)).val :=
      gluePairOpen_pairing_val_of_notMem_interface hij hopen s'
        hc' hni (mem_flags_of_internalFlags _ hmem1)
    refine (mem_internalFlags_glueOpen hij hopen s' hc' hc).mpr ?_
    rw [hag]
    exact hpW

/-- Periodic flags project forward along the unglue transport. -/
theorem periodicFlags_val_of_glueOpen
    (hni : partnerSurvI hopen ∉ s')
    (κ' : (Fg).RelTransitionSystem) {g : SurvivingFlag W i j}
    (hg : g ∈ κ'.periodicFlags) :
    g.val ∈ (RelTransitionSystem.unglueOpen hij hopen s' hc' hc
      κ').periodicFlags := by
  obtain ⟨hint, n, hn1, hcont, hperiod⟩ :=
    (κ'.mem_periodicFlags).mp hg
  refine ((RelTransitionSystem.unglueOpen hij hopen s' hc' hc
    κ').mem_periodicFlags).mpr
    ⟨internal_val_of_glueOpen hij hopen s' hc' hc hint,
      n, hn1, ?_, ?_⟩
  · intro m hm
    have hcorr := iterWalk_unglueOpen hij hopen s' hc' hc hni κ'
      hint n hcont m (le_of_lt hm)
    rw [hcorr.1]
    have hag : W.pairing (iterWalk κ' g m).val =
        ((W.gluePairOpen i j hij hopen).pairing
          (iterWalk κ' g m)).val :=
      (gluePairOpen_pairing_val_of_notMem_interface hij hopen s'
        hc' hni (mem_flags_of_internalFlags _ hcorr.2)).symm
    rw [hag]
    exact internal_val_of_glueOpen hij hopen s' hc' hc
      (hcont m hm)
  · have hcorr := iterWalk_unglueOpen hij hopen s' hc' hc hni κ'
      hint n hcont n le_rfl
    rw [hcorr.1, hperiod]

/-- Periodic flags lift backward along the unglue transport. -/
theorem periodicFlags_of_val_glueOpen
    (hni : partnerSurvI hopen ∉ s')
    (κ' : (Fg).RelTransitionSystem) {g : SurvivingFlag W i j}
    (hf : g.val ∈ (RelTransitionSystem.unglueOpen hij hopen s' hc'
      hc κ').periodicFlags) :
    g ∈ κ'.periodicFlags := by
  obtain ⟨hint, n, hn1, hcontW, hperiod⟩ :=
    ((RelTransitionSystem.unglueOpen hij hopen s' hc' hc
      κ').mem_periodicFlags).mp hf
  have hg : g ∈ (Fg).internalFlags :=
    internal_mk_of_glueOpen hij hopen s' hc' hc hint g.prop.1
      g.prop.2
  refine (κ'.mem_periodicFlags).mpr ⟨hg, n, hn1, ?_, ?_⟩
  · intro m hm
    exact (iterWalk_unglueOpen_rev hij hopen s' hc' hc hni κ' hg
      n hcontW m (le_of_lt hm)).2.2 hm
  · refine Subtype.ext ?_
    have hcorr := iterWalk_unglueOpen_rev hij hopen s' hc' hc hni
      κ' hg n hcontW n le_rfl
    rw [← hcorr.1]
    exact hperiod

/-- The `val`-bijection between the periodic flags of the two
sides. -/
noncomputable def periodicEquivGlueOpen
    (hni : partnerSurvI hopen ∉ s')
    (κ' : (Fg).RelTransitionSystem) :
    {f : W.Flag // f ∈ (RelTransitionSystem.unglueOpen hij hopen
      s' hc' hc κ').periodicFlags} ≃
      {g : (W.gluePairOpen i j hij hopen).Flag //
        g ∈ κ'.periodicFlags} where
  toFun f := ⟨(⟨f.val,
      (internal_surviving i j ((RelTransitionSystem.unglueOpen hij
        hopen s' hc' hc κ').periodicFlags_sub f.prop)).1,
      (internal_surviving i j ((RelTransitionSystem.unglueOpen hij
        hopen s' hc' hc κ').periodicFlags_sub f.prop)).2⟩ :
        SurvivingFlag W i j),
    periodicFlags_of_val_glueOpen hij hopen s' hc' hc hni κ'
      f.prop⟩
  invFun g := ⟨g.val.val,
    periodicFlags_val_of_glueOpen hij hopen s' hc' hc hni κ'
      g.prop⟩
  left_inv _f := Subtype.ext rfl
  right_inv _g := Subtype.ext (Subtype.ext rfl)

/-- The walk permutations on periodic flags agree under the
`val`-bijection. -/
theorem walkPermPeriodic_unglueOpen
    (hni : partnerSurvI hopen ∉ s')
    (κ' : (Fg).RelTransitionSystem) :
    (RelTransitionSystem.unglueOpen hij hopen s' hc' hc
      κ').walkPermPeriodic =
      (periodicEquivGlueOpen hij hopen s' hc' hc hni
        κ').symm.permCongr κ'.walkPermPeriodic := by
  apply Equiv.ext
  rintro ⟨f, hf⟩
  obtain ⟨h1, h2⟩ := internal_surviving i j
    ((RelTransitionSystem.unglueOpen hij hopen s' hc' hc
      κ').periodicFlags_sub hf)
  apply Subtype.ext
  change (RelTransitionSystem.unglueOpen hij hopen s' hc' hc
      κ').match_ (W.pairing f) =
    (κ'.match_ ((W.gluePairOpen i j hij hopen).pairing
      ⟨f, h1, h2⟩)).val
  have hs : (⟨f, h1, h2⟩ : SurvivingFlag W i j) ∈ s' :=
    mem_flags_of_internalFlags _
      (internal_mk_of_glueOpen hij hopen s' hc' hc
        ((RelTransitionSystem.unglueOpen hij hopen s' hc' hc
          κ').periodicFlags_sub hf) h1 h2)
  have hag : W.pairing f =
      ((W.gluePairOpen i j hij hopen).pairing ⟨f, h1, h2⟩).val :=
    (gluePairOpen_pairing_val_of_notMem_interface hij hopen s' hc' hni hs).symm
  rw [hag, unglueOpen_match_val hij hopen s' hc' hc κ'
    ((W.gluePairOpen i j hij hopen).pairing ⟨f, h1, h2⟩)]

/-- **`openCircuitCount` stability (open case)**: when the glued
edge's flags are not in the subset, the open circuit count is
unchanged by the unglue transport. -/
theorem openCircuitCount_unglueOpen
    (hni : partnerSurvI hopen ∉ s')
    (κ' : (Fg).RelTransitionSystem) :
    (RelTransitionSystem.unglueOpen hij hopen s' hc' hc
      κ').openCircuitCount = κ'.openCircuitCount := by
  unfold RelTransitionSystem.openCircuitCount
  rw [walkPermPeriodic_unglueOpen hij hopen s' hc' hc hni κ',
    cycleType_permCongr, card_fixedPoints_permCongr]

end OpenGlue

/-! ### The closed case -/

section ClosedGlue

variable (hclosed : W.pairing (W.boundaryFlag i) = W.boundaryFlag j)
  (b : Bool)
  (s' : Finset (SurvivingFlag W i j))
  (hc' : ∀ f ∈ s', (W.gluePairClosed i j hclosed).pairing f ∈ s')
  (hc : ∀ f ∈ liftSubsetClosed s' b,
    W.pairing f ∈ liftSubsetClosed s' b)

/-- The glued edge subset (closed case). -/
local notation "Fg" =>
  (EdgeSubset.mk s' hc' : EdgeSubset (W.gluePairClosed i j hclosed))

/-- The lifted edge subset (closed case). -/
local notation "Fl" =>
  (EdgeSubset.mk (liftSubsetClosed s' b) hc : EdgeSubset W)

include hclosed in
/-- In the closed case the pairing of a surviving flag is itself
surviving: the closed-off edge pairs its two boundary flags with
each other. -/
theorem pairing_val_surviving_closed (f' : SurvivingFlag W i j) :
    W.pairing f'.val ≠ W.boundaryFlag i ∧
      W.pairing f'.val ≠ W.boundaryFlag j := by
  constructor
  · intro h
    apply f'.prop.2
    have h' := congrArg W.pairing h
    rwa [W.pairing_invol, hclosed] at h'
  · intro h
    apply f'.prop.1
    have h' := congrArg W.pairing h
    rwa [W.pairing_invol, W.pairing_boundaryFlag_comm hclosed]
      at h'

/-- In the closed case the glued pairing agrees with the
`W`-pairing on all surviving flags, at projection level. -/
theorem gluePairClosed_pairing_val (f' : SurvivingFlag W i j) :
    ((W.gluePairClosed i j hclosed).pairing f').val =
      W.pairing f'.val := rfl

/-! #### Internal-flag correspondence (closed case) -/

/-- **Internal-flag correspondence (closed case)**. -/
theorem mem_internalFlags_glueClosed {f' : SurvivingFlag W i j} :
    f' ∈ (Fg).internalFlags ↔
      f'.val ∈ (Fl).internalFlags := by
  constructor
  · intro h
    obtain ⟨v, hv⟩ := attach_internal_of_mem _ h
    refine mem_internalFlags_of ?_
      ⟨v, (glueAttach_inl_iff f' v).mp hv⟩
    exact (surviving_val_mem_liftClosed_iff s' b f').mpr
      (mem_flags_of_internalFlags _ h)
  · intro h
    obtain ⟨v, hv⟩ := attach_internal_of_mem _ h
    refine mem_internalFlags_of ?_
      ⟨v, (glueAttach_inl_iff f' v).mpr hv⟩
    exact (surviving_val_mem_liftClosed_iff s' b f').mp
      (mem_flags_of_internalFlags _ h)

/-- Forward direction of the correspondence, `val` form. -/
theorem internal_val_of_glueClosed {f' : SurvivingFlag W i j}
    (hf' : f' ∈ (Fg).internalFlags) :
    f'.val ∈ (Fl).internalFlags :=
  (mem_internalFlags_glueClosed hclosed b s' hc' hc).mp hf'

/-- Backward direction of the correspondence, `mk` form. -/
theorem internal_mk_of_glueClosed {f : W.Flag}
    (hf : f ∈ (Fl).internalFlags)
    (h1 : f ≠ W.boundaryFlag i) (h2 : f ≠ W.boundaryFlag j) :
    (⟨f, h1, h2⟩ : SurvivingFlag W i j) ∈ (Fg).internalFlags :=
  (mem_internalFlags_glueClosed hclosed b s' hc' hc).mpr hf

/-! #### Transition transport (closed case) -/

/-- **Unglue (closed case)**: transport a transition system on the
glued subset to the lifted subset. -/
noncomputable def RelTransitionSystem.unglueClosed
    (κ' : (Fg).RelTransitionSystem) :
    (Fl).RelTransitionSystem where
  match_ := unglueMatch κ'.match_
  match_invol := by
    intro f hf
    obtain ⟨h1, h2⟩ := internal_surviving i j hf
    have hg := internal_mk_of_glueClosed hclosed b s' hc' hc hf
      h1 h2
    calc unglueMatch κ'.match_ (unglueMatch κ'.match_ f)
        = unglueMatch κ'.match_ (κ'.match_ ⟨f, h1, h2⟩).val := by
          rw [unglueMatch_of_surviving κ'.match_ f ⟨h1, h2⟩]
      _ = (κ'.match_ (κ'.match_ ⟨f, h1, h2⟩)).val :=
          unglueMatch_val κ'.match_ _
      _ = f := by rw [κ'.match_invol _ hg]
  match_ne := by
    intro f hf heq
    obtain ⟨h1, h2⟩ := internal_surviving i j hf
    have hg := internal_mk_of_glueClosed hclosed b s' hc' hc hf
      h1 h2
    rw [unglueMatch_of_surviving κ'.match_ f ⟨h1, h2⟩] at heq
    exact κ'.match_ne _ hg (Subtype.ext heq)
  match_mem := by
    intro f hf
    obtain ⟨h1, h2⟩ := internal_surviving i j hf
    have hg := internal_mk_of_glueClosed hclosed b s' hc' hc hf
      h1 h2
    rw [unglueMatch_of_surviving κ'.match_ f ⟨h1, h2⟩]
    exact internal_val_of_glueClosed hclosed b s' hc' hc
      (κ'.match_mem _ hg)
  match_vertex := by
    intro f hf v hv
    obtain ⟨h1, h2⟩ := internal_surviving i j hf
    have hg := internal_mk_of_glueClosed hclosed b s' hc' hc hf
      h1 h2
    rw [unglueMatch_of_surviving κ'.match_ f ⟨h1, h2⟩]
    exact (glueAttach_inl_iff (κ'.match_ ⟨f, h1, h2⟩) v).mp
      (κ'.match_vertex _ hg v
        ((glueAttach_inl_iff (⟨f, h1, h2⟩ : SurvivingFlag W i j)
          v).mpr hv))

/-- The closed ungluing's matching at a surviving flag. -/
theorem unglueClosed_match_of_surviving
    (κ' : (Fg).RelTransitionSystem) (f : W.Flag)
    (h : f ≠ W.boundaryFlag i ∧ f ≠ W.boundaryFlag j) :
    (RelTransitionSystem.unglueClosed hclosed b s' hc' hc
      κ').match_ f = (κ'.match_ ⟨f, h⟩).val :=
  unglueMatch_of_surviving κ'.match_ f h

/-- The same on a surviving flag's underlying flag. -/
theorem unglueClosed_match_val
    (κ' : (Fg).RelTransitionSystem) (g : SurvivingFlag W i j) :
    (RelTransitionSystem.unglueClosed hclosed b s' hc' hc
      κ').match_ g.val = (κ'.match_ g).val :=
  unglueMatch_val κ'.match_ g

/-- The surviving-ness certificate for restricting a lifted-side
matching to the glued subset (closed case). -/
theorem glueClosed_cert
    (κ : (Fl).RelTransitionSystem) :
    ∀ f' ∈ (Fg).internalFlags,
      κ.match_ f'.val ≠ W.boundaryFlag i ∧
        κ.match_ f'.val ≠ W.boundaryFlag j :=
  fun _ h => internal_surviving i j (κ.match_mem _
    (internal_val_of_glueClosed hclosed b s' hc' hc h))

/-- **Glue (closed case)**: restrict a transition system on the
lifted subset to the glued subset. -/
noncomputable def RelTransitionSystem.glueClosed
    (κ : (Fl).RelTransitionSystem) :
    (Fg).RelTransitionSystem where
  match_ := glueMatch κ.match_ (Fg).internalFlags
    (glueClosed_cert hclosed b s' hc' hc κ)
  match_invol := by
    intro f' hf'
    have hval := glueMatch_val_of_mem κ.match_ (Fg).internalFlags
      (glueClosed_cert hclosed b s' hc' hc κ) hf'
    have hm2 : glueMatch κ.match_ (Fg).internalFlags
        (glueClosed_cert hclosed b s' hc' hc κ) f' ∈
        (Fg).internalFlags := by
      refine (mem_internalFlags_glueClosed hclosed b s' hc'
        hc).mpr ?_
      rw [hval]
      exact κ.match_mem _
        (internal_val_of_glueClosed hclosed b s' hc' hc hf')
    refine Subtype.ext ?_
    rw [glueMatch_val_of_mem κ.match_ (Fg).internalFlags
      (glueClosed_cert hclosed b s' hc' hc κ) hm2, hval]
    exact κ.match_invol _
      (internal_val_of_glueClosed hclosed b s' hc' hc hf')
  match_ne := by
    intro f' hf' heq
    refine κ.match_ne f'.val
      (internal_val_of_glueClosed hclosed b s' hc' hc hf') ?_
    have h2 := congrArg Subtype.val heq
    rwa [glueMatch_val_of_mem κ.match_ (Fg).internalFlags
      (glueClosed_cert hclosed b s' hc' hc κ) hf'] at h2
  match_mem := by
    intro f' hf'
    refine (mem_internalFlags_glueClosed hclosed b s' hc' hc).mpr
      ?_
    rw [glueMatch_val_of_mem κ.match_ (Fg).internalFlags
      (glueClosed_cert hclosed b s' hc' hc κ) hf']
    exact κ.match_mem _
      (internal_val_of_glueClosed hclosed b s' hc' hc hf')
  match_vertex := by
    intro f' hf' v hv
    refine (glueAttach_inl_iff
      (glueMatch κ.match_ (Fg).internalFlags
        (glueClosed_cert hclosed b s' hc' hc κ) f') v).mpr ?_
    rw [glueMatch_val_of_mem κ.match_ (Fg).internalFlags
      (glueClosed_cert hclosed b s' hc' hc κ) hf']
    exact κ.match_vertex f'.val
      (internal_val_of_glueClosed hclosed b s' hc' hc hf') v
      ((glueAttach_inl_iff f' v).mp hv)

/-- The closed gluing's matching at an internal flag: the round trip
again agrees. -/
theorem glueClosed_match_val
    (κ : (Fl).RelTransitionSystem)
    {f' : SurvivingFlag W i j}
    (hf' : f' ∈ (Fg).internalFlags) :
    ((RelTransitionSystem.glueClosed hclosed b s' hc' hc
      κ).match_ f').val = κ.match_ f'.val :=
  glueMatch_val_of_mem κ.match_ (Fg).internalFlags
    (glueClosed_cert hclosed b s' hc' hc κ) hf'

/-! #### Round trips (closed case) -/

/-- Round trip lifted → glued → lifted: `match_` agrees pointwise
at internal flags. -/
theorem unglueClosed_glueClosed_match
    (κ : (Fl).RelTransitionSystem)
    {f : W.Flag}
    (hf : f ∈ (Fl).internalFlags) :
    (RelTransitionSystem.unglueClosed hclosed b s' hc' hc
      (RelTransitionSystem.glueClosed hclosed b s' hc' hc
        κ)).match_ f = κ.match_ f := by
  obtain ⟨h1, h2⟩ := internal_surviving i j hf
  have hg := internal_mk_of_glueClosed hclosed b s' hc' hc hf
    h1 h2
  rw [unglueClosed_match_of_surviving hclosed b s' hc' hc _ f
    ⟨h1, h2⟩]
  exact glueClosed_match_val hclosed b s' hc' hc κ hg

/-! #### Orientation transport (closed case) -/

/-- **Unglue an orientation (closed case)**: through the subtype,
`false` junk at the two glued boundary flags. -/
noncomputable def unglueOrientationClosed
    (κ' : (Fg).RelTransitionSystem) (o' : κ'.Orientation) :
    (RelTransitionSystem.unglueClosed hclosed b s' hc' hc
      κ').Orientation where
  isOut := unglueIsOut o'.isOut
  match_flip := by
    intro f hf
    obtain ⟨h1, h2⟩ := internal_surviving i j hf
    have hg := internal_mk_of_glueClosed hclosed b s' hc' hc hf
      h1 h2
    rw [unglueClosed_match_of_surviving hclosed b s' hc' hc κ' f
        ⟨h1, h2⟩,
      unglueIsOut_val o'.isOut (κ'.match_ ⟨f, h1, h2⟩),
      unglueIsOut_of_surviving o'.isOut f ⟨h1, h2⟩]
    exact o'.match_flip _ hg
  pairing_flip := by
    intro f hf hpf
    obtain ⟨h1, h2⟩ := internal_surviving i j hf
    obtain ⟨hp1, hp2⟩ := internal_surviving i j hpf
    have hg := internal_mk_of_glueClosed hclosed b s' hc' hc hf
      h1 h2
    have hpg := internal_mk_of_glueClosed hclosed b s' hc' hc hpf
      hp1 hp2
    have hrw : (W.gluePairClosed i j hclosed).pairing ⟨f, h1, h2⟩ =
        (⟨W.pairing f, hp1, hp2⟩ : SurvivingFlag W i j) := rfl
    rw [unglueIsOut_of_surviving o'.isOut (W.pairing f)
        ⟨hp1, hp2⟩,
      unglueIsOut_of_surviving o'.isOut f ⟨h1, h2⟩]
    have hflip := o'.pairing_flip ⟨f, h1, h2⟩ hg
      (by rw [hrw]; exact hpg)
    rwa [hrw] at hflip

/-- **Glue an orientation (closed case)**: through `Subtype.val`.
Unconditional: the closed glued pairing agrees with the
`W`-pairing on surviving flags. -/
noncomputable def glueOrientationClosed
    (κ : (Fl).RelTransitionSystem) (o : κ.Orientation) :
    (RelTransitionSystem.glueClosed hclosed b s' hc' hc
      κ).Orientation where
  isOut := fun f' => o.isOut f'.val
  match_flip := by
    intro f' hf'
    rw [glueClosed_match_val hclosed b s' hc' hc κ hf']
    exact o.match_flip f'.val
      (internal_val_of_glueClosed hclosed b s' hc' hc hf')
  pairing_flip := by
    intro f' hf' hpf'
    exact o.pairing_flip f'.val
      (internal_val_of_glueClosed hclosed b s' hc' hc hf')
      (internal_val_of_glueClosed hclosed b s' hc' hc hpf')

/-! #### `openCircuitCount` stability (closed case) -/

/-- Walk correspondence (glued-side continuation data), closed
case. -/
theorem iterWalk_unglueClosed
    (κ' : (Fg).RelTransitionSystem) {g : SurvivingFlag W i j}
    (hg : g ∈ (Fg).internalFlags) (n : ℕ)
    (hcont : ∀ m, m < n → (W.gluePairClosed i j hclosed).pairing
      (iterWalk κ' g m) ∈ (Fg).internalFlags) :
    ∀ k, k ≤ n →
      iterWalk (RelTransitionSystem.unglueClosed hclosed b s' hc'
        hc κ') g.val k = (iterWalk κ' g k).val ∧
      iterWalk κ' g k ∈ (Fg).internalFlags := by
  intro k
  induction k with
  | zero => exact fun _ => ⟨rfl, hg⟩
  | succ k ih =>
    intro hk
    obtain ⟨hval, hmem⟩ := ih (by omega)
    have hp := hcont k (by omega)
    refine ⟨?_, ?_⟩
    · change (RelTransitionSystem.unglueClosed hclosed b s' hc' hc
          κ').match_ (W.pairing (iterWalk
            (RelTransitionSystem.unglueClosed hclosed b s' hc' hc
              κ') g.val k)) =
        (κ'.match_ ((W.gluePairClosed i j hclosed).pairing
          (iterWalk κ' g k))).val
      rw [hval]
      exact unglueClosed_match_of_surviving hclosed b s' hc' hc κ'
        (W.pairing (iterWalk κ' g k).val)
        (pairing_val_surviving_closed hclosed (iterWalk κ' g k))
    · exact κ'.match_mem _ hp

/-- Walk correspondence (lifted-side continuation data), closed
case. -/
theorem iterWalk_unglueClosed_rev
    (κ' : (Fg).RelTransitionSystem) {g : SurvivingFlag W i j}
    (hg : g ∈ (Fg).internalFlags) (n : ℕ)
    (hcontW : ∀ m, m < n → W.pairing (iterWalk
      (RelTransitionSystem.unglueClosed hclosed b s' hc' hc κ')
      g.val m) ∈ (Fl).internalFlags) :
    ∀ k, k ≤ n →
      iterWalk (RelTransitionSystem.unglueClosed hclosed b s' hc'
        hc κ') g.val k = (iterWalk κ' g k).val ∧
      iterWalk κ' g k ∈ (Fg).internalFlags ∧
      (k < n → (W.gluePairClosed i j hclosed).pairing
        (iterWalk κ' g k) ∈ (Fg).internalFlags) := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨rfl, hg, ?_⟩
    intro h0
    have hpW := hcontW 0 h0
    rw [iterWalk_zero] at hpW
    change (W.gluePairClosed i j hclosed).pairing g ∈
      (Fg).internalFlags
    exact (mem_internalFlags_glueClosed hclosed b s' hc' hc).mpr
      hpW
  | succ k ih =>
    intro hk
    obtain ⟨hval, hmem, hpair⟩ := ih (by omega)
    have hpG : (W.gluePairClosed i j hclosed).pairing
        (iterWalk κ' g k) ∈ (Fg).internalFlags :=
      hpair (by omega)
    have hmem1 : iterWalk κ' g (k + 1) ∈ (Fg).internalFlags :=
      κ'.match_mem _ hpG
    have hstep : iterWalk (RelTransitionSystem.unglueClosed
        hclosed b s' hc' hc κ') g.val (k + 1) =
        (iterWalk κ' g (k + 1)).val := by
      change (RelTransitionSystem.unglueClosed hclosed b s' hc' hc
          κ').match_ (W.pairing (iterWalk
            (RelTransitionSystem.unglueClosed hclosed b s' hc' hc
              κ') g.val k)) =
        (κ'.match_ ((W.gluePairClosed i j hclosed).pairing
          (iterWalk κ' g k))).val
      rw [hval]
      exact unglueClosed_match_of_surviving hclosed b s' hc' hc κ'
        (W.pairing (iterWalk κ' g k).val)
        (pairing_val_surviving_closed hclosed (iterWalk κ' g k))
    refine ⟨hstep, hmem1, ?_⟩
    intro hk1
    have hpW := hcontW (k + 1) hk1
    rw [hstep] at hpW
    exact (mem_internalFlags_glueClosed hclosed b s' hc' hc).mpr
      hpW

/-- Periodic flags project forward along the unglue transport
(closed case). -/
theorem periodicFlags_val_of_glueClosed
    (κ' : (Fg).RelTransitionSystem) {g : SurvivingFlag W i j}
    (hg : g ∈ κ'.periodicFlags) :
    g.val ∈ (RelTransitionSystem.unglueClosed hclosed b s' hc' hc
      κ').periodicFlags := by
  obtain ⟨hint, n, hn1, hcont, hperiod⟩ :=
    (κ'.mem_periodicFlags).mp hg
  refine ((RelTransitionSystem.unglueClosed hclosed b s' hc' hc
    κ').mem_periodicFlags).mpr
    ⟨internal_val_of_glueClosed hclosed b s' hc' hc hint,
      n, hn1, ?_, ?_⟩
  · intro m hm
    have hcorr := iterWalk_unglueClosed hclosed b s' hc' hc κ'
      hint n hcont m (le_of_lt hm)
    rw [hcorr.1]
    exact internal_val_of_glueClosed hclosed b s' hc' hc
      (hcont m hm)
  · have hcorr := iterWalk_unglueClosed hclosed b s' hc' hc κ'
      hint n hcont n le_rfl
    rw [hcorr.1, hperiod]

/-- Periodic flags lift backward along the unglue transport
(closed case). -/
theorem periodicFlags_of_val_glueClosed
    (κ' : (Fg).RelTransitionSystem) {g : SurvivingFlag W i j}
    (hf : g.val ∈ (RelTransitionSystem.unglueClosed hclosed b s'
      hc' hc κ').periodicFlags) :
    g ∈ κ'.periodicFlags := by
  obtain ⟨hint, n, hn1, hcontW, hperiod⟩ :=
    ((RelTransitionSystem.unglueClosed hclosed b s' hc' hc
      κ').mem_periodicFlags).mp hf
  have hg : g ∈ (Fg).internalFlags :=
    internal_mk_of_glueClosed hclosed b s' hc' hc hint g.prop.1
      g.prop.2
  refine (κ'.mem_periodicFlags).mpr ⟨hg, n, hn1, ?_, ?_⟩
  · intro m hm
    exact (iterWalk_unglueClosed_rev hclosed b s' hc' hc κ' hg
      n hcontW m (le_of_lt hm)).2.2 hm
  · refine Subtype.ext ?_
    have hcorr := iterWalk_unglueClosed_rev hclosed b s' hc' hc
      κ' hg n hcontW n le_rfl
    rw [← hcorr.1]
    exact hperiod

/-- The `val`-bijection between the periodic flags of the two
sides (closed case). -/
noncomputable def periodicEquivGlueClosed
    (κ' : (Fg).RelTransitionSystem) :
    {f : W.Flag // f ∈ (RelTransitionSystem.unglueClosed hclosed
      b s' hc' hc κ').periodicFlags} ≃
      {g : (W.gluePairClosed i j hclosed).Flag //
        g ∈ κ'.periodicFlags} where
  toFun f := ⟨(⟨f.val,
      (internal_surviving i j ((RelTransitionSystem.unglueClosed
        hclosed b s' hc' hc κ').periodicFlags_sub f.prop)).1,
      (internal_surviving i j ((RelTransitionSystem.unglueClosed
        hclosed b s' hc' hc κ').periodicFlags_sub f.prop)).2⟩ :
        SurvivingFlag W i j),
    periodicFlags_of_val_glueClosed hclosed b s' hc' hc κ'
      f.prop⟩
  invFun g := ⟨g.val.val,
    periodicFlags_val_of_glueClosed hclosed b s' hc' hc κ'
      g.prop⟩
  left_inv _f := Subtype.ext rfl
  right_inv _g := Subtype.ext (Subtype.ext rfl)

/-- The walk permutations on periodic flags agree under the
`val`-bijection (closed case). -/
theorem walkPermPeriodic_unglueClosed
    (κ' : (Fg).RelTransitionSystem) :
    (RelTransitionSystem.unglueClosed hclosed b s' hc' hc
      κ').walkPermPeriodic =
      (periodicEquivGlueClosed hclosed b s' hc' hc
        κ').symm.permCongr κ'.walkPermPeriodic := by
  apply Equiv.ext
  rintro ⟨f, hf⟩
  obtain ⟨h1, h2⟩ := internal_surviving i j
    ((RelTransitionSystem.unglueClosed hclosed b s' hc' hc
      κ').periodicFlags_sub hf)
  apply Subtype.ext
  change (RelTransitionSystem.unglueClosed hclosed b s' hc' hc
      κ').match_ (W.pairing f) =
    (κ'.match_ ((W.gluePairClosed i j hclosed).pairing
      ⟨f, h1, h2⟩)).val
  exact unglueClosed_match_of_surviving hclosed b s' hc' hc κ'
    (W.pairing f)
    (pairing_val_surviving_closed hclosed ⟨f, h1, h2⟩)

/-- **`openCircuitCount` stability (closed case)**: the open
circuit count is unchanged by the unglue transport, for either
value of `b` (the closed-off circle-edge is boundary-attached in
`W` and never periodic). -/
theorem openCircuitCount_unglueClosed
    (κ' : (Fg).RelTransitionSystem) :
    (RelTransitionSystem.unglueClosed hclosed b s' hc' hc
      κ').openCircuitCount = κ'.openCircuitCount := by
  unfold RelTransitionSystem.openCircuitCount
  rw [walkPermPeriodic_unglueClosed hclosed b s' hc' hc κ',
    cycleType_permCongr, card_fixedPoints_permCongr]

end ClosedGlue

end EdgeSubset

end RS
