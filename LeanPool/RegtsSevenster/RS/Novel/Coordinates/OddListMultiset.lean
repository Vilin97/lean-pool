/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.TransitionExists

/-!
# A vertex's odd list, as a multiset

The odd list at a vertex is built by walking the flags there and
recording each one's per-flag odd value.  Read as a multiset it is
simply the image of those flags under that value, with the walking
order forgotten — the form in which two orientations' lists can be
compared, since only the order distinguishes them.
-/

namespace RS

open Finset Classical

variable {α : Type} {W : Fragment α} {F : EdgeSubset W} {ℓ : ℕ} {κ :
  F.TransitionSystem}

/-! ### Helper: bind of a two-element function splits into two maps -/

private theorem multiset_bind_pair {β γ : Type} (m : Multiset β)
    (a b : β → γ) :
    m.bind (fun x => ({a x} : Multiset γ) + {b x}) =
      m.map a + m.map b := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons x s ih =>
    rw [Multiset.cons_bind, ih, Multiset.map_cons, Multiset.map_cons,
      show a x ::ₘ Multiset.map a s = ({a x} : Multiset _) + Multiset.map a s
        from
        (Multiset.singleton_add _ _).symm,
      show b x ::ₘ Multiset.map b s = ({b x} : Multiset _) + Multiset.map b s
        from
        (Multiset.singleton_add _ _).symm]
    ac_rfl

/-! ### The attachWith–sort multiset equals the finset filter val -/

/-- The attachWith of the sorted list of a finset filter, as a multiset,
equals the val of `univ.filter` on the subtype. -/
theorem attachWith_sort_eq_filter_val
    (o : κ.Orientation) (v : W.Vertex) :
    (↑((F.inFlagsAt o v).attachWith (· ∈ F.flags)
        (fun _ hf => F.mem_of_mem_inFlagsAt hf)) :
      Multiset {f : W.Flag // f ∈ F.flags}) =
    (Finset.univ.filter (fun f : {f : W.Flag // f ∈ F.flags} =>
        W.attach f.val = Sum.inl v ∧ o.isOut f.val = false)).val := by
  letI := W.flagOrder
  letI := Classical.dec
  -- Both sides are nodup multisets with the same members; use Nodup.ext.
  have h_nd_r : (Finset.univ.filter (fun f : {f : W.Flag // f ∈ F.flags} =>
      W.attach f.val = Sum.inl v ∧ o.isOut f.val = false)).val.Nodup :=
    (Finset.univ.filter _).nodup
  have h_nd_l : ((↑((F.inFlagsAt o v).attachWith (· ∈ F.flags)
      (fun _ hf => F.mem_of_mem_inFlagsAt hf)) :
        Multiset {f : W.Flag // f ∈ F.flags})).Nodup := by
    rw [Multiset.coe_nodup]
    unfold EdgeSubset.inFlagsAt
    apply List.Nodup.pmap (fun _ _ _ _ h => Subtype.mk.inj h)
    exact Finset.sort_nodup _ (· ≤ ·)
  refine (h_nd_l.ext ?_ |>.mpr ?_)
  · convert h_nd_r
  · intro ⟨f, hf⟩
    rw [Multiset.mem_coe, List.mem_attachWith]
    simp only [Finset.mem_val, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hfin
      have : f ∈ F.flags.filter (fun f => W.attach f = Sum.inl v ∧ o.isOut f =
        false) := by
        convert (Finset.mem_sort (· ≤ ·)).mp hfin
      exact (Finset.mem_filter.mp this).2
    · intro hmem
      rw [show F.inFlagsAt o v = (F.flags.filter
          (fun f => W.attach f = Sum.inl v ∧ o.isOut f = false)).sort (· ≤ ·)
            from rfl]
      have hfilt : f ∈ F.flags.filter
          (fun f => W.attach f = Sum.inl v ∧ o.isOut f = false) :=
        Finset.mem_filter.mpr ⟨hf, hmem⟩
      convert (Finset.mem_sort (· ≤ ·)).mpr hfilt

/-! ### The match bijection between incoming and outgoing flags -/

/-- The match embedding on the flag subtype. -/
private noncomputable def matchEmb (κ : F.TransitionSystem) :
    {f : W.Flag // f ∈ F.flags} ↪ {f : W.Flag // f ∈ F.flags} where
  toFun f := ⟨κ.match_ f.val, κ.match_mem _ f.prop⟩
  inj' := fun ⟨a, ha⟩ ⟨b, hb⟩ h => by
    simp only [Subtype.mk.injEq] at h ⊢
    have h1 := κ.match_invol a ha
    have h2 := κ.match_invol b hb
    calc a = κ.match_ (κ.match_ a) := h1.symm
      _ = κ.match_ (κ.match_ b) := congrArg κ.match_ h
      _ = b := h2

/-- match maps incoming-at-v flags to outgoing-at-v flags. -/
private theorem match_maps_in_to_out (o : κ.Orientation) (v : W.Vertex)
    (f : {f : W.Flag // f ∈ F.flags})
    (hf : W.attach f.val = Sum.inl v ∧ o.isOut f.val = false) :
    W.attach (κ.match_ f.val) = Sum.inl v ∧
      o.isOut (κ.match_ f.val) = true := by
  exact ⟨κ.match_vertex f.val f.prop v hf.1,
    by rw [o.match_flip f.val f.prop, hf.2]; rfl⟩

/-- match maps outgoing-at-v flags to incoming-at-v flags. -/
private theorem match_maps_out_to_in (o : κ.Orientation) (v : W.Vertex)
    (f : {f : W.Flag // f ∈ F.flags})
    (hf : W.attach f.val = Sum.inl v ∧ o.isOut f.val = true) :
    W.attach (κ.match_ f.val) = Sum.inl v ∧
      o.isOut (κ.match_ f.val) = false := by
  exact ⟨κ.match_vertex f.val f.prop v hf.1,
    by rw [o.match_flip f.val f.prop, hf.2]; rfl⟩

/-- The match embedding maps the incoming-at-v finset to the outgoing-at-v
finset. -/
private theorem match_image_in_eq_out (o : κ.Orientation) (v : W.Vertex) :
    (Finset.univ.filter (fun f : {f : W.Flag // f ∈ F.flags} =>
      W.attach f.val = Sum.inl v ∧ o.isOut f.val = false)).map
        (matchEmb κ) =
    Finset.univ.filter (fun f : {f : W.Flag // f ∈ F.flags} =>
      W.attach f.val = Sum.inl v ∧ o.isOut f.val = true) := by
  ext ⟨g, hg⟩
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨f, hf⟩, ⟨hatt, hout⟩, heq⟩
    have hval : κ.match_ f = g := congrArg Subtype.val heq
    rw [← hval]
    exact match_maps_in_to_out o v ⟨f, hf⟩ ⟨hatt, hout⟩
  · intro ⟨hatt, hout⟩
    -- g is outgoing at v; its match is incoming at v
    refine ⟨⟨κ.match_ g, κ.match_mem g hg⟩, ?_, ?_⟩
    · exact match_maps_out_to_in o v ⟨g, hg⟩ ⟨hatt, hout⟩
    · exact Subtype.ext (κ.match_invol g hg)

/-! ### Splitting the all-at-v filter into in and out parts -/

private theorem filter_at_v_split (o : κ.Orientation) (v : W.Vertex) :
    (Finset.univ.filter (fun f : {f : W.Flag // f ∈ F.flags} =>
      W.attach f.val = Sum.inl v)).val =
    (Finset.univ.filter (fun f : {f : W.Flag // f ∈ F.flags} =>
      W.attach f.val = Sum.inl v ∧ o.isOut f.val = false)).val +
    (Finset.univ.filter (fun f : {f : W.Flag // f ∈ F.flags} =>
      W.attach f.val = Sum.inl v ∧ o.isOut f.val = true)).val := by
  -- Use Multiset.filter_add_not to split by the isOut predicate
  set S := (Finset.univ.filter (fun f : {f : W.Flag // f ∈ F.flags} =>
    W.attach f.val = Sum.inl v)).val
  -- filter_add_not gives S = filter p S + filter (¬p) S
  have hfan : Multiset.filter (fun f : {f : W.Flag // f ∈ F.flags} =>
      o.isOut f.val = false) S +
    Multiset.filter (fun f => ¬ (o.isOut f.val = false)) S = S :=
    Multiset.filter_add_not _ S
  -- Simplify ¬(isOut f.val = false) to (isOut f.val = true)
  have hfilt_in : Multiset.filter (fun f : {f : W.Flag // f ∈ F.flags} =>
      o.isOut f.val = false) S =
    (Finset.univ.filter (fun f : {f : W.Flag // f ∈ F.flags} =>
      W.attach f.val = Sum.inl v ∧ o.isOut f.val = false)).val := by
    simp only [S, Finset.filter_val, Multiset.filter_filter]
    congr 1; ext ⟨f, hf⟩
    simp only [and_comm]
  have hfilt_out : Multiset.filter (fun f : {f : W.Flag // f ∈ F.flags} =>
      ¬ (o.isOut f.val = false)) S =
    (Finset.univ.filter (fun f : {f : W.Flag // f ∈ F.flags} =>
      W.attach f.val = Sum.inl v ∧ o.isOut f.val = true)).val := by
    simp only [S, Finset.filter_val, Multiset.filter_filter]
    congr 1; ext ⟨f, hf⟩
    simp only [Bool.not_eq_false]
    exact and_comm
  rw [← hfilt_in, ← hfilt_out, hfan]

/-! ### Main theorem -/

/-- A vertex's odd list as a multiset: the per-flag odd values over
the flags at that vertex. -/
theorem oddListAt_coe_multiset (o : κ.Orientation) (φ : F.OddColouring ℓ)
    (v : W.Vertex) :
    (↑(F.oddListAt o φ v) : Multiset (Fin (2 * ℓ))) =
      (Finset.univ.filter (fun f : {f : W.Flag // f ∈ F.flags} =>
        W.attach f.val = Sum.inl v)).val.map
          (fun f => if o.isOut f.val = true
            then oddPartner ℓ (φ.val f) else φ.val f) := by
  -- Abbreviations
  set S_in := Finset.univ.filter (fun f : {f : W.Flag // f ∈ F.flags} =>
    W.attach f.val = Sum.inl v ∧ o.isOut f.val = false)
  set S_out := Finset.univ.filter (fun f : {f : W.Flag // f ∈ F.flags} =>
    W.attach f.val = Sum.inl v ∧ o.isOut f.val = true)
  set S_all := Finset.univ.filter (fun f : {f : W.Flag // f ∈ F.flags} =>
    W.attach f.val = Sum.inl v)
  set g := fun f : {f : W.Flag // f ∈ F.flags} =>
    if o.isOut f.val = true then oddPartner ℓ (φ.val f) else φ.val f
  -- Step 1: LHS = bind over S_in of pairs
  have h_lhs : (↑(F.oddListAt o φ v) : Multiset (Fin (2 * ℓ))) =
      S_in.val.bind (fun f => (↑(F.oddPairFn κ φ f) : Multiset _)) := by
    unfold EdgeSubset.oddListAt
    rw [← Multiset.coe_bind]
    congr 1
    exact attachWith_sort_eq_filter_val o v
  -- Step 2: Each oddPairFn gives a two-element multiset
  have h_pair : ∀ f : {f : W.Flag // f ∈ F.flags},
      (↑(F.oddPairFn κ φ f) : Multiset _) =
        ({φ.val f} : Multiset _) + {oddPartner ℓ (φ.val ⟨κ.match_ f.val,
          κ.match_mem _ f.prop⟩)} := by
    intro ⟨f, hf⟩
    -- oddPairFn produces [φ f, oddPartner (φ (match f))]
    -- As multisets: ↑[a, b] = a ::ₘ b ::ₘ 0 = {a} + {b}
    let a := φ.val ⟨f, hf⟩
    let b := oddPartner ℓ (φ.val ⟨κ.match_ f, κ.match_mem _ hf⟩)
    show (↑(F.oddPairFn κ φ ⟨f, hf⟩) : Multiset _) = ({a} : Multiset _) + {b}
    show (↑([a, b] : List _) : Multiset _) = ({a} : Multiset _) + {b}
    rfl
  -- Step 3: Bind of pairs = map of first + map of second
  have h_bind_split : S_in.val.bind (fun f => (↑(F.oddPairFn κ φ f) : Multiset
    _)) =
      S_in.val.map (fun f => φ.val f) +
      S_in.val.map (fun f => oddPartner ℓ (φ.val ⟨κ.match_ f.val, κ.match_mem _
        f.prop⟩)) := by
    rw [show S_in.val.bind (fun f => (↑(F.oddPairFn κ φ f) : Multiset _)) =
        S_in.val.bind (fun f =>
          ({φ.val f} : Multiset _) +
          {oddPartner ℓ (φ.val ⟨κ.match_ f.val, κ.match_mem _ f.prop⟩)}) from
      Multiset.bind_congr (fun f _ => h_pair f)]
    exact multiset_bind_pair S_in.val
      (fun f => φ.val f)
      (fun f => oddPartner ℓ (φ.val ⟨κ.match_ f.val, κ.match_mem _ f.prop⟩))
  -- Step 4: RHS splits into in and out parts
  have h_rhs_split : S_all.val.map g = S_in.val.map g + S_out.val.map g := by
    rw [filter_at_v_split o v, Multiset.map_add]
  -- Step 5: On S_in, g f = φ.val f
  have h_g_in : S_in.val.map g = S_in.val.map (fun f => φ.val f) := by
    apply Multiset.map_congr rfl
    intro f hf
    have : o.isOut f.val = false := by
      rw [Finset.mem_val, Finset.mem_filter] at hf
      exact hf.2.2
    simp [g, this]
  -- Step 6: On S_out, g f = oddPartner (φ.val f)
  have h_g_out : S_out.val.map g =
      S_out.val.map (fun f => oddPartner ℓ (φ.val f)) := by
    apply Multiset.map_congr rfl
    intro f hf
    have : o.isOut f.val = true := by
      rw [Finset.mem_val, Finset.mem_filter] at hf
      exact hf.2.2
    simp [g, this]
  -- Step 7: The match bijection equates the outgoing part with
  -- the incoming part mapped via match
  have h_out_eq_in_match :
      S_out.val.map (fun f => oddPartner ℓ (φ.val f)) =
      S_in.val.map (fun f => oddPartner ℓ (φ.val ⟨κ.match_ f.val, κ.match_mem _
        f.prop⟩)) := by
    -- S_out = S_in.map (matchEmb κ)
    have himg := match_image_in_eq_out o v
    have hval : S_out.val = S_in.val.map (matchEmb κ) := by
      have := congrArg Finset.val himg
      rw [Finset.map_val] at this
      exact this.symm
    calc S_out.val.map (fun f => oddPartner ℓ (φ.val f))
        = (S_in.val.map (matchEmb κ)).map (fun f => oddPartner ℓ (φ.val f))
          := by
          rw [hval]
      _ = S_in.val.map ((fun f => oddPartner ℓ (φ.val f)) ∘ (matchEmb κ)) :=
          Multiset.map_map _ _ _
      _ = S_in.val.map
          (fun f => oddPartner ℓ (φ.val ⟨κ.match_ f.val, κ.match_mem _ f.prop⟩))
            := by
          rfl
  -- Assemble
  rw [h_lhs, h_bind_split, h_rhs_split, h_g_in, h_g_out, h_out_eq_in_match]

end RS
