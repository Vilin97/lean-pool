/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Skein.GlueChords

/-!
# The boundary pairing of a glued system by chain following

For an open single-pair glue `W' = W.gluePairOpen i j hij hopen`
and a transition system `κ` on the lifted edge subset, this file
computes the `pathMatch` of the glued system
`RelTransitionSystem.glueOpen … κ` on the glued boundary flags in
terms of the `pathMatch` of `κ`:

* `mem_boundaryFlags_glueOpen` — a surviving flag is a boundary
  flag of the glued subset iff its value is a boundary flag of the
  lifted subset (the two cut flags are excluded automatically,
  being non-surviving).
* `pathMatch_glueOpen_of_ne` — when the `κ`-chain of `δ'` exits
  away from the two cut flags, the glued chain follows it exactly.
* `pathMatch_glueOpen_hit_i` / `pathMatch_glueOpen_hit_j` — when
  the `κ`-chain of `δ'` exits at a cut flag, the glued chain
  crosses the rewired interface and continues along the other cut
  flag's chain to its exit.
* `glued_participation_iff` — a glued boundary flag participates
  in the glued subset exactly when its value participates in the
  lifted one.
-/

@[expose] public section

namespace RS



namespace EdgeSubset

open Fragment

variable {α : Type} {W : Fragment α}

/-! ### The open-gluing context -/

variable {i j : α}

section OpenGluePathMatch

variable (hij : i ≠ j)
  (hopen : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j)
  (s' : Finset (SurvivingFlag W i j))
  (hc' : ∀ f ∈ s', (W.gluePairOpen i j hij hopen).pairing f ∈ s')
  (hc : ∀ f ∈ liftSubsetOpen hopen s',
    W.pairing f ∈ liftSubsetOpen hopen s')

/-- The glued edge subset. -/
local notation "Fg" =>
  (EdgeSubset.mk s' hc' : EdgeSubset (W.gluePairOpen i j hij hopen))

/-- The lifted edge subset. -/
local notation "Fl" =>
  (EdgeSubset.mk (liftSubsetOpen hopen s') hc : EdgeSubset W)

/-! #### Boundary-flag correspondence -/

/-- **Boundary-flag correspondence (open case)**: a surviving flag
is a boundary flag of the glued subset iff its value is a boundary
flag of the lifted subset.  (The two cut flags are not surviving,
so this is the lifted boundary minus the cut flags.) -/
theorem mem_boundaryFlags_glueOpen {δ' : SurvivingFlag W i j} :
    δ' ∈ (Fg).boundaryFlags ↔ δ'.val ∈ (Fl).boundaryFlags := by
  constructor
  · intro h
    have hf : δ'.val ∈ (Fl).flags :=
      (surviving_val_mem_liftOpen_iff hopen s' δ').mpr
        (mem_flags_of_boundaryFlags _ h)
    rcases mem_internalFlags_or_boundaryFlags (Fl) hf with hint | hbd
    · exact absurd h
        (Finset.disjoint_left.mp
          ((Fg).internalFlags_disjoint_boundaryFlags)
          ((mem_internalFlags_glueOpen hij hopen s' hc' hc).mpr
            hint))
    · exact hbd
  · intro h
    have hf : δ' ∈ (Fg).flags :=
      (surviving_val_mem_liftOpen_iff hopen s' δ').mp
        (mem_flags_of_boundaryFlags _ h)
    rcases mem_internalFlags_or_boundaryFlags (Fg) hf with hint | hbd
    · exact absurd h
        (Finset.disjoint_left.mp
          ((Fl).internalFlags_disjoint_boundaryFlags)
          ((mem_internalFlags_glueOpen hij hopen s' hc' hc).mp
            hint))
    · exact hbd

/-- Forward direction of the correspondence, `val` form. -/
theorem boundary_val_of_glueOpen {δ' : SurvivingFlag W i j}
    (hδ' : δ' ∈ (Fg).boundaryFlags) :
    δ'.val ∈ (Fl).boundaryFlags :=
  (mem_boundaryFlags_glueOpen hij hopen s' hc' hc).mp hδ'

/-- Backward direction of the correspondence, `mk` form. -/
theorem boundary_mk_of_glueOpen {f : W.Flag}
    (hf : f ∈ (Fl).boundaryFlags)
    (h1 : f ≠ W.boundaryFlag i) (h2 : f ≠ W.boundaryFlag j) :
    (⟨f, h1, h2⟩ : SurvivingFlag W i j) ∈ (Fg).boundaryFlags :=
  (mem_boundaryFlags_glueOpen hij hopen s' hc' hc).mpr hf

/-! #### The chord-diagram corollary -/

end OpenGluePathMatch

end EdgeSubset

/-! ## The pathMatch glue transport

The boundary-chain matching of a glued (open-cut) system at a
surviving boundary flag: the original chain when it avoids the
cut, and the through-composition with the far side's chain when
it hits either cut end — the tower-side engine of the joint-
matching invariant. -/

section PathMatchGlue

open EdgeSubset Fragment

variable {α : Type} {W : Fragment α} {i j : α}
  (hij : i ≠ j)
  (hopen : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j)
  (s' : Finset (SurvivingFlag W i j))
  (hc' : ∀ f ∈ s',
    (W.gluePairOpen i j hij hopen).pairing f ∈ s')
  (hc : ∀ f ∈ liftSubsetOpen hopen s',
    W.pairing f ∈ liftSubsetOpen hopen s')

local notation "Fg" =>
  (EdgeSubset.mk s' hc' :
    EdgeSubset (W.gluePairOpen i j hij hopen))

local notation "Fl" =>
  (EdgeSubset.mk (liftSubsetOpen hopen s') hc :
    EdgeSubset W)

/-- Walk agreement from a corresponding pair of starting flags:
while the base walk's pairings stay internal, the glued walk
projects to it and stays in the subset. -/
theorem iterWalk_glueOpen_from
    (κ : (Fl).RelTransitionSystem)
    {g' : SurvivingFlag W i j} {g : W.Flag}
    (hg : g'.val = g) (hgs : g' ∈ s') (n : ℕ)
    (hcont : ∀ m, m < n →
      W.pairing (iterWalk κ g m) ∈ (Fl).internalFlags) :
    ∀ k, k ≤ n →
      (iterWalk (RelTransitionSystem.glueOpen hij hopen s' hc'
        hc κ) g' k).val = iterWalk κ g k ∧
      iterWalk (RelTransitionSystem.glueOpen hij hopen s' hc'
        hc κ) g' k ∈ s' := by
  intro k
  induction k with
  | zero => exact fun _ => ⟨hg, hgs⟩
  | succ k ih =>
      intro hk
      obtain ⟨hval, hmem⟩ := ih (by omega)
      have hint : W.pairing (iterWalk κ g k) ∈
          (Fl).internalFlags := hcont k (by omega)
      have hintv : W.pairing ((iterWalk
          (RelTransitionSystem.glueOpen hij hopen s' hc' hc κ)
          g' k)).val ∈ (Fl).internalFlags := by
        rw [hval]; exact hint
      have hstep := glueOpen_step_agrees hij hopen s' hc' hc κ
        (iterWalk (RelTransitionSystem.glueOpen hij hopen s'
          hc' hc κ) g' k) hintv
      have hpair : (W.gluePairOpen i j hij hopen).pairing
          (iterWalk (RelTransitionSystem.glueOpen hij hopen s'
            hc' hc κ) g' k) ∈ (Fg).internalFlags := by
        refine (mem_internalFlags_glueOpen hij hopen s' hc'
          hc).mpr ?_
        have h12 := internal_surviving i j hintv
        have hrw : ((W.gluePairOpen i j hij hopen).pairing
            (iterWalk (RelTransitionSystem.glueOpen hij hopen
              s' hc' hc κ) g' k)).val =
            W.pairing (iterWalk
              (RelTransitionSystem.glueOpen hij hopen s' hc'
                hc κ) g' k).val :=
          rewire_val_of_ne hopen _ h12.1 h12.2
        rw [hrw]
        exact hintv
      refine ⟨?_, ?_⟩
      · change ((RelTransitionSystem.glueOpen hij hopen s' hc' hc κ).match_
            ((W.gluePairOpen i j hij hopen).pairing
              (iterWalk (RelTransitionSystem.glueOpen hij hopen s' hc' hc κ) g'
                k))).val =
          κ.match_ (W.pairing (iterWalk κ g k))
        exact hstep.trans (by rw [hval])
      · change (RelTransitionSystem.glueOpen hij hopen s' hc' hc κ).match_
            ((W.gluePairOpen i j hij hopen).pairing
              (iterWalk (RelTransitionSystem.glueOpen hij hopen s' hc' hc κ) g'
                k)) ∈ s'
        exact mem_flags_of_internalFlags _
          ((RelTransitionSystem.glueOpen hij hopen s' hc' hc κ).match_mem _
            hpair)

/-- A surviving flag over a lifted boundary flag is a glued
boundary flag. -/
theorem boundary_mk_of_glueOpen
    {f' : SurvivingFlag W i j} (hfs : f' ∈ s')
    (hbd : f'.val ∈ (Fl).boundaryFlags) :
    f' ∈ (Fg).boundaryFlags := by
  refine Finset.mem_filter.mpr ⟨hfs, ?_⟩
  obtain ⟨lbl, hat⟩ := (Finset.mem_filter.mp hbd).2
  rcases hga : glueAttach W i j f' with v | lb
  · have hspec := glueAttach_spec W i j f'
    rw [hga, hat] at hspec
    cases hspec
  · exact ⟨lb, hga⟩

/-- A glued boundary flag lies over a lifted boundary flag. -/
theorem boundary_val_of_glueOpen
    {f' : SurvivingFlag W i j}
    (hbd : f' ∈ (Fg).boundaryFlags) :
    f'.val ∈ (Fl).boundaryFlags := by
  refine Finset.mem_filter.mpr ⟨?_, ?_⟩
  · exact (surviving_val_mem_liftOpen_iff hopen s'
      f').mpr (Finset.mem_filter.mp hbd).1
  · obtain ⟨lb, hga⟩ := (Finset.mem_filter.mp hbd).2
    have hspec := glueAttach_spec W i j f'
    rw [show (W.gluePairOpen i j hij hopen).attach f' =
      glueAttach W i j f' from rfl] at hga
    rw [hga] at hspec
    exact ⟨lb.val, hspec.symm⟩

/-- **Exit-time uniqueness**: any explicitly exhibited chain walk
computes the path matching — the chain's exit step is unique, so
no fuel bookkeeping is needed. -/
theorem pathMatch_exit_unique {α' : Type}
    {W' : Fragment α'} {F : EdgeSubset W'}
    (κ : F.RelTransitionSystem) {b : W'.Flag}
    (hb : b ∈ F.boundaryFlags) (N : ℕ)
    (hcontN : ∀ m, m < N →
      W'.pairing (iterWalk κ b m) ∈ F.internalFlags)
    (htermN : W'.pairing (iterWalk κ b N) ∈ F.boundaryFlags) :
    κ.pathMatch b hb = W'.pairing (iterWalk κ b N) := by
  obtain ⟨k₂, hkle₂, hcont₂, hterm₂⟩ :=
    chain_terminates_with_data κ hb
  have hN : k₂ = N := by
    rcases lt_trichotomy k₂ N with hlt | heq | hgt
    · exact absurd (hcontN k₂ hlt)
        (fun hint => (Finset.disjoint_left.mp
          (internalFlags_disjoint_boundaryFlags _) hint)
          hterm₂)
    · exact heq
    · exact absurd (hcont₂ N hgt)
        (fun hint => (Finset.disjoint_left.mp
          (internalFlags_disjoint_boundaryFlags _) hint)
          htermN)
  subst hN
  exact κ.pathMatch_eq hb
    (traceChain_fuel_mono κ (by omega)
      (traceChain_forward κ b hcont₂ hterm₂))

/-- **pathMatch through an open glue, no cut hit**: when the
original chain's endpoint avoids both cut flags, the glued chain
has the same endpoint. -/
theorem pathMatch_glueOpen_of_ne
    [LinearOrder α]
    (κ : (Fl).RelTransitionSystem)
    {b' : SurvivingFlag W i j}
    (hbg : b' ∈ (Fg).boundaryFlags)
    (hbl : b'.val ∈ (Fl).boundaryFlags)
    (hni : κ.pathMatch b'.val hbl ≠ W.boundaryFlag i)
    (hnj : κ.pathMatch b'.val hbl ≠ W.boundaryFlag j) :
    ((RelTransitionSystem.glueOpen hij hopen s' hc' hc
      κ).pathMatch b' hbg).val = κ.pathMatch b'.val hbl := by
  obtain ⟨k, hkle, hcont, hterm⟩ :=
    chain_terminates_with_data κ hbl
  have hpm : κ.pathMatch b'.val hbl =
      W.pairing (iterWalk κ b'.val k) :=
    pathMatch_exit_unique κ hbl k hcont hterm
  have hbs : b' ∈ s' := (Finset.mem_filter.mp hbg).1
  -- ═══════ THE GLUED WALK FOLLOWS THE BASE WALK ═══════
  have hw := iterWalk_glueOpen_from hij hopen s' hc' hc κ
    (g := b'.val) rfl hbs k hcont
  have hcontg : ∀ m, m < k →
      (W.gluePairOpen i j hij hopen).pairing
        (iterWalk (RelTransitionSystem.glueOpen hij hopen s'
          hc' hc κ) b' m) ∈ (Fg).internalFlags := by
    intro m hm
    obtain ⟨hval, _⟩ := hw m (by omega)
    have hint := hcont m hm
    have hnecut := internal_surviving i j hint
    have hrw : ((W.gluePairOpen i j hij hopen).pairing
        (iterWalk (RelTransitionSystem.glueOpen hij hopen s'
          hc' hc κ) b' m)).val =
        W.pairing (iterWalk (RelTransitionSystem.glueOpen
          hij hopen s' hc' hc κ) b' m).val := by
      refine rewire_val_of_ne hopen _ ?_ ?_
      · rw [hval]; exact hnecut.1
      · rw [hval]; exact hnecut.2
    refine (mem_internalFlags_glueOpen hij hopen s' hc'
      hc).mpr ?_
    rw [hrw, hval]
    exact hint
  obtain ⟨hval, hmem⟩ := hw k (le_refl k)
  have hrw : ((W.gluePairOpen i j hij hopen).pairing
      (iterWalk (RelTransitionSystem.glueOpen hij hopen s'
        hc' hc κ) b' k)).val =
      W.pairing (iterWalk (RelTransitionSystem.glueOpen hij
        hopen s' hc' hc κ) b' k).val := by
    refine rewire_val_of_ne hopen _ ?_ ?_
    · rw [hval]; exact fun hcon => hni (hpm.trans hcon)
    · rw [hval]; exact fun hcon => hnj (hpm.trans hcon)
  have htermg : (W.gluePairOpen i j hij hopen).pairing
      (iterWalk (RelTransitionSystem.glueOpen hij hopen s'
        hc' hc κ) b' k) ∈ (Fg).boundaryFlags := by
    refine boundary_mk_of_glueOpen hij hopen s' hc' hc
      (hc' _ hmem) ?_
    rw [hrw, hval]
    exact hterm
  have hpmg := pathMatch_exit_unique
    (RelTransitionSystem.glueOpen hij hopen s' hc' hc κ)
    hbg k hcontg htermg
  rw [hpmg, hrw, hval, hpm]

private theorem pathMatch_reverse_eq {F : EdgeSubset W}
    (κ : F.RelTransitionSystem) {b x : W.Flag}
    (hb : b ∈ F.boundaryFlags) (hx : x ∈ F.boundaryFlags)
    (he : κ.pathMatch b hb = x) : κ.pathMatch x hx = b := by
  subst he
  exact κ.pathMatch_invol hb

private theorem iterWalk_glueOpen_internal
    (κ : (Fl).RelTransitionSystem) {b' : SurvivingFlag W i j}
    (hbs : b' ∈ s') (k : ℕ)
    (hcont : ∀ m, m < k →
      W.pairing (iterWalk κ b'.val m) ∈ (Fl).internalFlags) : ∀ m, m < k →
    (W.gluePairOpen i j hij hopen).pairing
      (iterWalk (RelTransitionSystem.glueOpen hij hopen s' hc' hc κ) b' m) ∈
        (Fg).internalFlags := by
  have hw := iterWalk_glueOpen_from hij hopen s' hc' hc κ
    (g := b'.val) rfl hbs k hcont
  intro m hm
  obtain ⟨hval, _⟩ := hw m (by omega)
  have hint := hcont m hm
  have hnecut := internal_surviving i j hint
  have hrw : ((W.gluePairOpen i j hij hopen).pairing
      (iterWalk (RelTransitionSystem.glueOpen hij hopen s' hc' hc κ) b'
        m)).val =
      W.pairing (iterWalk (RelTransitionSystem.glueOpen hij hopen s' hc' hc κ)
        b' m).val := by
    refine rewire_val_of_ne hopen _ ?_ ?_
    · rw [hval]; exact hnecut.1
    · rw [hval]; exact hnecut.2
  refine (mem_internalFlags_glueOpen hij hopen s' hc'
    hc).mpr ?_
  rw [hrw, hval]
  exact hint

/-- **pathMatch through an open glue, `i`-cut hit**: when the
original chain from a surviving boundary flag ends at the `i`-cut
flag, the glued chain continues through the cut and ends at the
`j`-side chain's endpoint. -/
theorem pathMatch_glueOpen_hit_i
    [LinearOrder α]
    (κ : (Fl).RelTransitionSystem)
    {b' : SurvivingFlag W i j}
    (hbg : b' ∈ (Fg).boundaryFlags)
    (hbl : b'.val ∈ (Fl).boundaryFlags)
    (hbfj : W.boundaryFlag j ∈ (Fl).boundaryFlags)
    (hhit : κ.pathMatch b'.val hbl = W.boundaryFlag i) :
    ((RelTransitionSystem.glueOpen hij hopen s' hc' hc κ).pathMatch b' hbg).val
      =
      κ.pathMatch (W.boundaryFlag j) hbfj := by
  obtain ⟨k, hkle, hcont, hterm⟩ :=
    chain_terminates_with_data κ hbl
  have hpm : κ.pathMatch b'.val hbl =
      W.pairing (iterWalk κ b'.val k) :=
    pathMatch_exit_unique κ hbl k hcont hterm
  have hbs : b' ∈ s' := (Finset.mem_filter.mp hbg).1
  -- ═══════ THE GLUED WALK FOLLOWS THE BASE WALK ═══════
  have hw := iterWalk_glueOpen_from hij hopen s' hc' hc κ
    (g := b'.val) rfl hbs k hcont
  have hcontg := iterWalk_glueOpen_internal hij hopen s' hc' hc κ hbs k hcont
  have hhitk : W.pairing (iterWalk κ b'.val k) =
      W.boundaryFlag i := hpm.symm.trans hhit
  -- ═══════ CROSSING THE REWIRED INTERFACE ═══════
  have hcross : (W.gluePairOpen i j hij hopen).pairing
      (iterWalk (RelTransitionSystem.glueOpen hij hopen s' hc' hc κ) b' k) =
        partnerSurvJ hopen :=
    gluePairOpen_pairing_interface_i hij hopen _
      (by rw [(hw k (le_refl k)).1]; exact hhitk)
  have hpsj : partnerSurvJ hopen ∈ s' := by
    rw [← hcross]
    exact hc' _ (hw k (le_refl k)).2
  -- ═══════ CONTINUING ALONG THE OTHER CUT FLAG'S CHAIN ═══════
  obtain ⟨k₃, hkle₃, hcont₃, hterm₃⟩ :=
    chain_terminates_with_data κ hbfj
  have hpm₃ : κ.pathMatch (W.boundaryFlag j) hbfj =
      W.pairing (iterWalk κ (W.boundaryFlag j) k₃) :=
    pathMatch_exit_unique κ hbfj k₃ hcont₃ hterm₃
  have hbfi : W.boundaryFlag i ∈ (Fl).boundaryFlags := by
    have := κ.pathMatch_mem hbl
    rw [hhit] at this
    exact this
  have hne₂j : κ.pathMatch (W.boundaryFlag j) hbfj ≠
      W.boundaryFlag j := κ.pathMatch_ne_self hbfj
  have hne₂i : κ.pathMatch (W.boundaryFlag j) hbfj ≠
      W.boundaryFlag i := by
    intro hcon
    have h2 := pathMatch_reverse_eq κ hbfj hbfi hcon
    have h3 := pathMatch_reverse_eq κ hbl hbfi hhit
    exact b'.prop.2 (h3.symm.trans h2)
  rcases mem_internalFlags_or_boundaryFlags (Fl)
      (hc _ ((Finset.mem_filter.mp hbfj).1)) with hint₂ | hb₂
  · -- continuing: the j-edge enters the interior
    have hk₃pos : 1 ≤ k₃ := by
      by_contra hz
      have hz0 : k₃ = 0 := by omega
      rw [hz0] at hterm₃
      exact (Finset.disjoint_left.mp
        (internalFlags_disjoint_boundaryFlags _) hint₂)
        (by simpa using hterm₃)
    have hpsjint : partnerSurvJ hopen ∈
        (Fg).internalFlags :=
      (mem_internalFlags_glueOpen hij hopen s' hc' hc).mpr
        (by rw [partnerSurvJ_val]; exact hint₂)
    have hb2v : (iterWalk (RelTransitionSystem.glueOpen hij hopen s' hc' hc κ)
      b' (k + 1)).val =
        κ.match_ (W.pairing (W.boundaryFlag j)) := by
      change ((RelTransitionSystem.glueOpen hij hopen s' hc' hc κ).match_
          ((W.gluePairOpen i j hij hopen).pairing
            (iterWalk (RelTransitionSystem.glueOpen hij hopen s' hc' hc κ) b'
              k))).val = _
      rw [hcross]
      exact (glueOpen_match_val hij hopen s' hc' hc κ
        hpsjint).trans (by rw [partnerSurvJ_val])
    have hmem2 : iterWalk (RelTransitionSystem.glueOpen hij hopen s' hc' hc κ)
      b' (k + 1) ∈ s' := by
      change (RelTransitionSystem.glueOpen hij hopen s' hc' hc κ).match_
          ((W.gluePairOpen i j hij hopen).pairing
            (iterWalk (RelTransitionSystem.glueOpen hij hopen s' hc' hc κ) b'
              k)) ∈ s'
      rw [hcross]
      exact mem_flags_of_internalFlags _
        ((RelTransitionSystem.glueOpen hij hopen s' hc' hc κ).match_mem _
          hpsjint)
    have hcontsh : ∀ m, m < k₃ - 1 →
        W.pairing (iterWalk κ
          (κ.match_ (W.pairing (W.boundaryFlag j))) m) ∈
          (Fl).internalFlags := by
      intro m hm
      rw [iterWalk_shift]
      exact hcont₃ (m + 1) (by omega)
    have hw₂ := iterWalk_glueOpen_from hij hopen s' hc' hc κ
      (g' := iterWalk (RelTransitionSystem.glueOpen hij hopen s' hc' hc κ) b'
        (k + 1)) hb2v hmem2
      (k₃ - 1) hcontsh
    have hadd := fun m =>
      (iterWalk_add (RelTransitionSystem.glueOpen hij hopen s' hc' hc κ) b'
        (k + 1) m).symm
    have hcontN : ∀ m, m < k + k₃ →
        (W.gluePairOpen i j hij hopen).pairing
          (iterWalk (RelTransitionSystem.glueOpen hij hopen s' hc' hc κ) b' m) ∈
            (Fg).internalFlags := by
      intro m hm
      rcases lt_trichotomy m k with hmk | hmk | hmk
      · exact hcontg m hmk
      · subst hmk
        rw [hcross]
        exact hpsjint
      · obtain ⟨m', rfl⟩ : ∃ m', m = k + 1 + m' :=
          ⟨m - (k + 1), by omega⟩
        obtain ⟨hval, _⟩ := hw₂ m' (by omega)
        rw [hadd] at hval
        have hint := by
          have := hcontsh m' (by omega)
          exact this
        have hintsh : W.pairing (iterWalk κ
            (W.boundaryFlag j) (m' + 1)) ∈
            (Fl).internalFlags := by
          rw [← iterWalk_shift]
          exact hint
        have hnecut := internal_surviving i j hintsh
        have hrw : ((W.gluePairOpen i j hij hopen).pairing
            (iterWalk (RelTransitionSystem.glueOpen hij hopen s' hc' hc κ) b' (k
              + 1 + m'))).val =
            W.pairing (iterWalk (RelTransitionSystem.glueOpen hij hopen s' hc'
              hc κ) b'
              (k + 1 + m')).val := by
          refine rewire_val_of_ne hopen _ ?_ ?_
          · rw [hval, iterWalk_shift]; exact hnecut.1
          · rw [hval, iterWalk_shift]; exact hnecut.2
        refine (mem_internalFlags_glueOpen hij hopen s' hc'
          hc).mpr ?_
        rw [hrw, hval, iterWalk_shift]
        exact hintsh
    have hNval : (iterWalk (RelTransitionSystem.glueOpen hij hopen s' hc' hc κ)
      b' (k + k₃)).val =
        iterWalk κ (W.boundaryFlag j) k₃ := by
      have hidx : k + k₃ = k + 1 + (k₃ - 1) := by omega
      rw [hidx, ← hadd]
      obtain ⟨hval, _⟩ := hw₂ (k₃ - 1) (le_refl _)
      rw [hval, iterWalk_shift,
        show k₃ - 1 + 1 = k₃ from by omega]
    have hNmem : iterWalk (RelTransitionSystem.glueOpen hij hopen s' hc' hc κ)
      b' (k + k₃) ∈ s' := by
      have hidx : k + k₃ = k + 1 + (k₃ - 1) := by omega
      rw [hidx, ← hadd]
      exact (hw₂ (k₃ - 1) (le_refl _)).2
    have hnecutN : W.pairing (iterWalk (RelTransitionSystem.glueOpen hij hopen
      s' hc' hc κ) b'
        (k + k₃)).val ≠ W.boundaryFlag i ∧
        W.pairing (iterWalk (RelTransitionSystem.glueOpen hij hopen s' hc' hc κ)
          b'
          (k + k₃)).val ≠ W.boundaryFlag j := by
      rw [hNval]
      exact ⟨fun hcon => hne₂i (hpm₃.trans hcon),
        fun hcon => hne₂j (hpm₃.trans hcon)⟩
    have hrwN : ((W.gluePairOpen i j hij hopen).pairing
        (iterWalk (RelTransitionSystem.glueOpen hij hopen s' hc' hc κ) b' (k +
          k₃))).val =
        W.pairing (iterWalk (RelTransitionSystem.glueOpen hij hopen s' hc' hc κ)
          b' (k + k₃)).val :=
      rewire_val_of_ne hopen _ hnecutN.1 hnecutN.2
    have htermN : (W.gluePairOpen i j hij hopen).pairing
        (iterWalk (RelTransitionSystem.glueOpen hij hopen s' hc' hc κ) b' (k +
          k₃)) ∈
        (Fg).boundaryFlags := by
      refine boundary_mk_of_glueOpen hij hopen s' hc' hc
        (hc' _ hNmem) ?_
      rw [hrwN, hNval]
      exact hterm₃
    have hpmg := pathMatch_exit_unique
      (RelTransitionSystem.glueOpen hij hopen s' hc' hc κ) hbg (k + k₃)
      hcontN htermN
    rw [hpmg, hrwN, hNval, hpm₃]
  · -- terminal: the j-edge is boundary-to-boundary
    have hpmT : κ.pathMatch (W.boundaryFlag j) hbfj =
        W.pairing (W.boundaryFlag j) :=
      κ.pathMatch_eq_pairing hbfj hb₂
    have htermg : (W.gluePairOpen i j hij hopen).pairing
        (iterWalk (RelTransitionSystem.glueOpen hij hopen s' hc' hc κ) b' k) ∈
          (Fg).boundaryFlags := by
      rw [hcross]
      refine boundary_mk_of_glueOpen hij hopen s' hc' hc
        hpsj ?_
      rw [partnerSurvJ_val]
      exact hb₂
    have hpmg := pathMatch_exit_unique
      (RelTransitionSystem.glueOpen hij hopen s' hc' hc κ) hbg k
      hcontg htermg
    rw [hpmg, hcross, partnerSurvJ_val, hpmT]

/-- **pathMatch through an open glue, `j`-cut hit**: when the
original chain from a surviving boundary flag ends at the `j`-cut
flag, the glued chain continues through the cut and ends at the
`i`-side chain's endpoint. -/
theorem pathMatch_glueOpen_hit_j
    [LinearOrder α]
    (κ : (Fl).RelTransitionSystem)
    {b' : SurvivingFlag W i j}
    (hbg : b' ∈ (Fg).boundaryFlags)
    (hbl : b'.val ∈ (Fl).boundaryFlags)
    (hbfi : W.boundaryFlag i ∈ (Fl).boundaryFlags)
    (hhit : κ.pathMatch b'.val hbl = W.boundaryFlag j) :
    ((RelTransitionSystem.glueOpen hij hopen s' hc' hc κ).pathMatch b' hbg).val
      =
      κ.pathMatch (W.boundaryFlag i) hbfi := by
  obtain ⟨k, hkle, hcont, hterm⟩ :=
    chain_terminates_with_data κ hbl
  have hpm : κ.pathMatch b'.val hbl =
      W.pairing (iterWalk κ b'.val k) :=
    pathMatch_exit_unique κ hbl k hcont hterm
  have hbs : b' ∈ s' := (Finset.mem_filter.mp hbg).1
  have hw := iterWalk_glueOpen_from hij hopen s' hc' hc κ
    (g := b'.val) rfl hbs k hcont
  have hcontg := iterWalk_glueOpen_internal hij hopen s' hc' hc κ hbs k hcont
  have hhitk : W.pairing (iterWalk κ b'.val k) =
      W.boundaryFlag j := hpm.symm.trans hhit
  have hhitne : W.pairing (iterWalk κ b'.val k) ≠
      W.boundaryFlag i := by
    rw [hhitk]
    exact fun hcon => hij (boundaryFlag_injective W hcon.symm)
  -- ═══════ CROSSING THE REWIRED INTERFACE ═══════
  have hcross : (W.gluePairOpen i j hij hopen).pairing
      (iterWalk (RelTransitionSystem.glueOpen hij hopen s' hc' hc κ) b' k) =
        partnerSurvI hopen :=
    gluePairOpen_pairing_interface_j hij hopen _
      (by rw [(hw k (le_refl k)).1]; exact hhitne)
      (by rw [(hw k (le_refl k)).1]; exact hhitk)
  have hpsj : partnerSurvI hopen ∈ s' := by
    rw [← hcross]
    exact hc' _ (hw k (le_refl k)).2
  obtain ⟨k₃, hkle₃, hcont₃, hterm₃⟩ :=
    chain_terminates_with_data κ hbfi
  have hpm₃ : κ.pathMatch (W.boundaryFlag i) hbfi =
      W.pairing (iterWalk κ (W.boundaryFlag i) k₃) :=
    pathMatch_exit_unique κ hbfi k₃ hcont₃ hterm₃
  have hbfj : W.boundaryFlag j ∈ (Fl).boundaryFlags := by
    have := κ.pathMatch_mem hbl
    rw [hhit] at this
    exact this
  have hne₂i : κ.pathMatch (W.boundaryFlag i) hbfi ≠
      W.boundaryFlag i := κ.pathMatch_ne_self hbfi
  have hne₂j : κ.pathMatch (W.boundaryFlag i) hbfi ≠
      W.boundaryFlag j := by
    intro hcon
    have h2 := pathMatch_reverse_eq κ hbfi hbfj hcon
    have h3 := pathMatch_reverse_eq κ hbl hbfj hhit
    exact b'.prop.1 (h3.symm.trans h2)
  rcases mem_internalFlags_or_boundaryFlags (Fl)
      (hc _ ((Finset.mem_filter.mp hbfi).1)) with hint₂ | hb₂
  · -- continuing: the j-edge enters the interior
    have hk₃pos : 1 ≤ k₃ := by
      by_contra hz
      have hz0 : k₃ = 0 := by omega
      rw [hz0] at hterm₃
      exact (Finset.disjoint_left.mp
        (internalFlags_disjoint_boundaryFlags _) hint₂)
        (by simpa using hterm₃)
    have hpsiint : partnerSurvI hopen ∈
        (Fg).internalFlags :=
      (mem_internalFlags_glueOpen hij hopen s' hc' hc).mpr
        (by rw [partnerSurvI_val]; exact hint₂)
    have hb2v : (iterWalk (RelTransitionSystem.glueOpen hij hopen s' hc' hc κ)
      b' (k + 1)).val =
        κ.match_ (W.pairing (W.boundaryFlag i)) := by
      change ((RelTransitionSystem.glueOpen hij hopen s' hc' hc κ).match_
          ((W.gluePairOpen i j hij hopen).pairing
            (iterWalk (RelTransitionSystem.glueOpen hij hopen s' hc' hc κ) b'
              k))).val = _
      rw [hcross]
      exact (glueOpen_match_val hij hopen s' hc' hc κ
        hpsiint).trans (by rw [partnerSurvI_val])
    have hmem2 : iterWalk (RelTransitionSystem.glueOpen hij hopen s' hc' hc κ)
      b' (k + 1) ∈ s' := by
      change (RelTransitionSystem.glueOpen hij hopen s' hc' hc κ).match_
          ((W.gluePairOpen i j hij hopen).pairing
            (iterWalk (RelTransitionSystem.glueOpen hij hopen s' hc' hc κ) b'
              k)) ∈ s'
      rw [hcross]
      exact mem_flags_of_internalFlags _
        ((RelTransitionSystem.glueOpen hij hopen s' hc' hc κ).match_mem _
          hpsiint)
    have hcontsh : ∀ m, m < k₃ - 1 →
        W.pairing (iterWalk κ
          (κ.match_ (W.pairing (W.boundaryFlag i))) m) ∈
          (Fl).internalFlags := by
      intro m hm
      rw [iterWalk_shift]
      exact hcont₃ (m + 1) (by omega)
    have hw₂ := iterWalk_glueOpen_from hij hopen s' hc' hc κ
      (g' := iterWalk (RelTransitionSystem.glueOpen hij hopen s' hc' hc κ) b'
        (k + 1)) hb2v hmem2
      (k₃ - 1) hcontsh
    have hadd := fun m =>
      (iterWalk_add (RelTransitionSystem.glueOpen hij hopen s' hc' hc κ) b'
        (k + 1) m).symm
    have hcontN : ∀ m, m < k + k₃ →
        (W.gluePairOpen i j hij hopen).pairing
          (iterWalk (RelTransitionSystem.glueOpen hij hopen s' hc' hc κ) b' m) ∈
            (Fg).internalFlags := by
      intro m hm
      rcases lt_trichotomy m k with hmk | hmk | hmk
      · exact hcontg m hmk
      · subst hmk
        rw [hcross]
        exact hpsiint
      · obtain ⟨m', rfl⟩ : ∃ m', m = k + 1 + m' :=
          ⟨m - (k + 1), by omega⟩
        obtain ⟨hval, _⟩ := hw₂ m' (by omega)
        rw [hadd] at hval
        have hint := by
          have := hcontsh m' (by omega)
          exact this
        have hintsh : W.pairing (iterWalk κ
            (W.boundaryFlag i) (m' + 1)) ∈
            (Fl).internalFlags := by
          rw [← iterWalk_shift]
          exact hint
        have hnecut := internal_surviving i j hintsh
        have hrw : ((W.gluePairOpen i j hij hopen).pairing
            (iterWalk (RelTransitionSystem.glueOpen hij hopen s' hc' hc κ) b' (k
              + 1 + m'))).val =
            W.pairing (iterWalk (RelTransitionSystem.glueOpen hij hopen s' hc'
              hc κ) b'
              (k + 1 + m')).val := by
          refine rewire_val_of_ne hopen _ ?_ ?_
          · rw [hval, iterWalk_shift]; exact hnecut.1
          · rw [hval, iterWalk_shift]; exact hnecut.2
        refine (mem_internalFlags_glueOpen hij hopen s' hc'
          hc).mpr ?_
        rw [hrw, hval, iterWalk_shift]
        exact hintsh
    have hNval : (iterWalk (RelTransitionSystem.glueOpen hij hopen s' hc' hc κ)
      b' (k + k₃)).val =
        iterWalk κ (W.boundaryFlag i) k₃ := by
      have hidx : k + k₃ = k + 1 + (k₃ - 1) := by omega
      rw [hidx, ← hadd]
      obtain ⟨hval, _⟩ := hw₂ (k₃ - 1) (le_refl _)
      rw [hval, iterWalk_shift,
        show k₃ - 1 + 1 = k₃ from by omega]
    have hNmem : iterWalk (RelTransitionSystem.glueOpen hij hopen s' hc' hc κ)
      b' (k + k₃) ∈ s' := by
      have hidx : k + k₃ = k + 1 + (k₃ - 1) := by omega
      rw [hidx, ← hadd]
      exact (hw₂ (k₃ - 1) (le_refl _)).2
    have hnecutN : W.pairing (iterWalk (RelTransitionSystem.glueOpen hij hopen
      s' hc' hc κ) b'
        (k + k₃)).val ≠ W.boundaryFlag i ∧
        W.pairing (iterWalk (RelTransitionSystem.glueOpen hij hopen s' hc' hc κ)
          b'
          (k + k₃)).val ≠ W.boundaryFlag j := by
      rw [hNval]
      exact ⟨fun hcon => hne₂i (hpm₃.trans hcon),
        fun hcon => hne₂j (hpm₃.trans hcon)⟩
    have hrwN : ((W.gluePairOpen i j hij hopen).pairing
        (iterWalk (RelTransitionSystem.glueOpen hij hopen s' hc' hc κ) b' (k +
          k₃))).val =
        W.pairing (iterWalk (RelTransitionSystem.glueOpen hij hopen s' hc' hc κ)
          b' (k + k₃)).val :=
      rewire_val_of_ne hopen _ hnecutN.1 hnecutN.2
    have htermN : (W.gluePairOpen i j hij hopen).pairing
        (iterWalk (RelTransitionSystem.glueOpen hij hopen s' hc' hc κ) b' (k +
          k₃)) ∈
        (Fg).boundaryFlags := by
      refine boundary_mk_of_glueOpen hij hopen s' hc' hc
        (hc' _ hNmem) ?_
      rw [hrwN, hNval]
      exact hterm₃
    have hpmg := pathMatch_exit_unique
      (RelTransitionSystem.glueOpen hij hopen s' hc' hc κ) hbg (k + k₃)
      hcontN htermN
    rw [hpmg, hrwN, hNval, hpm₃]
  · -- terminal: the j-edge is boundary-to-boundary
    have hpmT : κ.pathMatch (W.boundaryFlag i) hbfi =
        W.pairing (W.boundaryFlag i) :=
      κ.pathMatch_eq_pairing hbfi hb₂
    have htermg : (W.gluePairOpen i j hij hopen).pairing
        (iterWalk (RelTransitionSystem.glueOpen hij hopen s' hc' hc κ) b' k) ∈
          (Fg).boundaryFlags := by
      rw [hcross]
      refine boundary_mk_of_glueOpen hij hopen s' hc' hc
        hpsj ?_
      rw [partnerSurvI_val]
      exact hb₂
    have hpmg := pathMatch_exit_unique
      (RelTransitionSystem.glueOpen hij hopen s' hc' hc κ) hbg k
      hcontg htermg
    rw [hpmg, hcross, partnerSurvI_val, hpmT]

end PathMatchGlue

open EdgeSubset Fragment in
/-- Participation transports through the open glue at label
level. -/
theorem glued_participation_iff
    {α : Type} {W : Fragment α} {i j : α}
    (hij : i ≠ j)
    (hopen : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j)
    (s' : Finset (SurvivingFlag W i j))
    (hc' : ∀ f ∈ s',
      (W.gluePairOpen i j hij hopen).pairing f ∈ s')
    (hc : ∀ f ∈ liftSubsetOpen hopen s',
      W.pairing f ∈ liftSubsetOpen hopen s')
    (l : SurvivingLabel α i j) :
    (W.gluePairOpen i j hij hopen).boundaryFlag l ∈
      (EdgeSubset.mk s' hc' :
        EdgeSubset (W.gluePairOpen i j hij hopen)).boundaryFlags
    ↔ W.boundaryFlag l.val ∈
      (EdgeSubset.mk (liftSubsetOpen hopen s') hc :
        EdgeSubset W).boundaryFlags := by
  constructor
  · intro h
    have := boundary_val_of_glueOpen hij hopen s' hc' hc h
    rwa [show ((W.gluePairOpen i j hij hopen).boundaryFlag
      l).val = W.boundaryFlag l.val from rfl] at this
  · intro h
    refine boundary_mk_of_glueOpen hij hopen s' hc' hc ?_ ?_
    · exact (surviving_val_mem_liftOpen_iff hopen s'
        _).mp (Finset.mem_filter.mp h).1
    · exact h

end RS
