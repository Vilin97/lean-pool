/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Skein.GlueCircuitDelta

/-!
# The single-pair gluing infrastructure

The infrastructure of the single-pair gluing analysis: the
extended-state evaluation (`extendPair_left`, `extendPair_right`,
`extendPair_surviving`), the `glueAttach` correspondence, the
through-flag membership characterization, and the through-factor
arithmetic (`oddPartnerSign_sq`, `oddPartnerSign_cast_sq`).

Why every cut in the development is ordered: the naive
transposed-factor weighting is order-sensitive — the `W`-side
through-product of a closed-off edge reads
`throughStateFactor (st (min i j)) (st (max i j))`, so for
`i < j` the ε pairs with its transpose and the odd block sums to
`−2ℓ` (as required by the circle prefactor `(k − 2ℓ)`), while for
`j < i` it pairs with itself and sums to `+2ℓ`; gluing a strand's
two ends with `i = 1, j = 0` gives `k + 2ℓ` instead of `k − 2ℓ`.
All cuts in the development are therefore ordered.
-/

@[expose] public section

namespace RS



/-! ## Evaluation of the extended state -/

namespace GenBoundaryState

variable {k ℓ : ℕ} {α : Type} {i j : α}

/-- The extended state's value at the first glued label. -/
theorem extendPair_left
    (st : GenBoundaryState k ℓ (Fragment.SurvivingLabel α i j))
    (c c' : Fin k ⊕ Fin (2 * ℓ)) :
    extendPair i j st c c' i = c := by
  unfold extendPair
  exact dite_eq_left rfl

/-- At the second glued label. -/
theorem extendPair_right (hij : i ≠ j)
    (st : GenBoundaryState k ℓ (Fragment.SurvivingLabel α i j))
    (c c' : Fin k ⊕ Fin (2 * ℓ)) :
    extendPair i j st c c' j = c' := by
  unfold extendPair
  rw [dite_eq_right (Ne.symm hij), dite_eq_left rfl]

/-- And at a surviving label, where it is the state extended. -/
theorem extendPair_surviving
    (st : GenBoundaryState k ℓ (Fragment.SurvivingLabel α i j))
    (c c' : Fin k ⊕ Fin (2 * ℓ))
    (a : Fragment.SurvivingLabel α i j) :
    extendPair i j st c c' a.val = st a := by
  unfold extendPair
  rw [dite_eq_right a.prop.1, dite_eq_right a.prop.2]

end GenBoundaryState

/-! ## The ledger sums -/

/-- The square of the odd partner sign is one. -/
theorem oddPartnerSign_sq (ℓ : ℕ) (c : Fin (2 * ℓ)) :
    (oddPartnerSign ℓ c : ℂ) * (oddPartnerSign ℓ c : ℂ) = 1 := by
  unfold oddPartnerSign
  by_cases h : c.val < ℓ <;> simp [h]

/-- The square of the odd partner sign is one, read through the
integer cast. -/
theorem oddPartnerSign_cast_sq (ℓ : ℕ) (c : Fin (2 * ℓ)) :
    ((oddPartnerSign ℓ c : ℤ) : ℂ) *
      ((oddPartnerSign ℓ c : ℤ) : ℂ) = 1 :=
  oddPartnerSign_sq ℓ c

/-! ## The closed-case correspondence engine -/

namespace EdgeSubset

open Fragment

open scoped Classical in
/-- Unfolded membership in the through-flags (stated generically to
avoid reducibility friction at glued fragments). -/
theorem mem_throughFlags_iff {β : Type} {V : Fragment β}
    {F : EdgeSubset V} {f : V.Flag} :
    f ∈ F.throughFlags ↔ f ∈ F.flags ∧
      (∃ i : β, V.attach f = Sum.inr i) ∧
      (∃ j : β, V.attach (V.pairing f) = Sum.inr j) := by
  unfold EdgeSubset.throughFlags
  exact Finset.mem_filter

/-! ### List and membership helpers -/

/-- `attachWith` respects permutations. -/
theorem perm_attachWith {γ : Type _} {p : γ → Prop} :
    ∀ {l₁ l₂ : List γ}, l₁.Perm l₂ →
      ∀ (H₁ : ∀ x ∈ l₁, p x) (H₂ : ∀ x ∈ l₂, p x),
      (l₁.attachWith p H₁).Perm (l₂.attachWith p H₂) := by
  intro l₁ l₂ hperm
  induction hperm with
  | nil => intro _ _; exact List.Perm.refl _
  | cons a _ ih =>
    intro H₁ H₂
    rw [List.attachWith_cons, List.attachWith_cons]
    exact List.Perm.cons _ (ih _ _)
  | swap a b l =>
    intro H₁ H₂
    rw [List.attachWith_cons, List.attachWith_cons,
      List.attachWith_cons, List.attachWith_cons]
    exact List.Perm.swap _ _ _
  | trans h₁ _ ih₁ ih₂ =>
    intro H₁ H₂
    exact (ih₁ H₁ (fun x hx => H₁ x (h₁.symm.subset hx))).trans
      (ih₂ (fun x hx => H₁ x (h₁.symm.subset hx)) H₂)

/-- Finset-supported multisets map equally along a bijection of
their supports (stated without decidability data so that it
applies by unification against glued-fragment goals). -/
theorem multiset_map_eq_of_bij {γ δ X : Type _}
    (s : Finset γ) (t : Finset δ)
    (e : δ → γ) (hinj : Function.Injective e)
    (hmem : ∀ y, y ∈ t ↔ e y ∈ s)
    (hsurj : ∀ x ∈ s, ∃ y, e y = x)
    (g : γ → X) (g' : δ → X)
    (hg : ∀ y ∈ t, g (e y) = g' y) :
    s.val.map g = t.val.map g' := by
  have hset : s = t.map ⟨e, hinj⟩ := by
    ext x
    rw [Finset.mem_map]
    constructor
    · intro hx
      obtain ⟨y, rfl⟩ := hsurj x hx
      exact ⟨y, (hmem y).mpr hx, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact (hmem y).mp hy
  rw [hset,
    show (t.map ⟨e, hinj⟩).val = t.val.map e from rfl,
    Multiset.map_map]
  refine Multiset.map_congr rfl ?_
  intro y hy
  exact hg y (Finset.mem_val.mp hy)

section ClosedEngine

variable {α : Type} {W : Fragment α} {i j : α}
  (hij : i ≠ j)
  (hclosed : W.pairing (W.boundaryFlag i) = W.boundaryFlag j)
  (s' : Finset (SurvivingFlag W i j))
  (b : Bool)
  (hc' : ∀ f ∈ s', (W.gluePairClosed i j hclosed).pairing f ∈ s')
  (hc : ∀ f ∈ liftSubsetClosed s' b,
    W.pairing f ∈ liftSubsetClosed s' b)

local notation "Fg" =>
  (EdgeSubset.mk s' hc' : EdgeSubset (W.gluePairClosed i j hclosed))

local notation "Fl" =>
  (EdgeSubset.mk (liftSubsetClosed s' b) hc : EdgeSubset W)

variable
  (κ' : (EdgeSubset.mk s' hc' :
    EdgeSubset (W.gluePairClosed i j hclosed)).RelTransitionSystem)
  (o' : κ'.Orientation)

/-- The unglued transition system on the lift. -/
local notation "κW" =>
  RelTransitionSystem.unglueClosed hclosed b s' hc' hc κ'

/-- The unglued orientation on the lift. -/
local notation "oW" =>
  unglueOrientationClosed hclosed b s' hc' hc κ' o'

/-! ### The in-flag lists across the closed glue -/

/-- The lifted in-flag list is a permutation of the projected
glued in-flag list. -/
theorem relInFlagsAt_perm_closed (v : W.Vertex) :
    ((Fl).relInFlagsAt (oW) v).Perm
      (((Fg).relInFlagsAt o' v).map Subtype.val) := by
  refine List.perm_of_nodup_nodup_toFinset_eq
    (relInFlagsAt_nodup _ _)
    (List.Nodup.map (fun x y h => Subtype.ext h)
      (relInFlagsAt_nodup _ _)) ?_
  ext f
  simp only [List.mem_toFinset]
  constructor
  · intro hf
    obtain ⟨hmem, hv, hout⟩ := mem_relInFlagsAt_iff.mp hf
    have hsurv := vertex_flag_surviving (i := i) (j := j) f v hv
    refine List.mem_map.mpr ⟨⟨f, hsurv.1, hsurv.2⟩,
      mem_relInFlagsAt_iff.mpr ⟨?_, ?_, ?_⟩, rfl⟩
    · exact (surviving_val_mem_liftClosed_iff s' b
        ⟨f, hsurv.1, hsurv.2⟩).mp hmem
    · exact (glueAttach_inl_iff ⟨f, hsurv.1, hsurv.2⟩ v).mpr hv
    · exact (unglueIsOut_val o'.isOut
        ⟨f, hsurv.1, hsurv.2⟩).symm.trans hout
  · intro hf
    obtain ⟨f₀, hf₀, rfl⟩ := List.mem_map.mp hf
    obtain ⟨hmem, hv, hout⟩ := mem_relInFlagsAt_iff.mp hf₀
    refine mem_relInFlagsAt_iff.mpr
      ⟨(surviving_val_mem_liftClosed_iff s' b f₀).mpr hmem,
        (glueAttach_inl_iff f₀ v).mp hv,
        (unglueIsOut_val o'.isOut f₀).trans hout⟩

/-- Members of the projected glued in-flag list are internal in
the lift. -/
theorem mem_map_relInFlagsAt_internal {v : W.Vertex} :
    ∀ f ∈ ((Fg).relInFlagsAt o' v).map Subtype.val,
      f ∈ (Fl).internalFlags := by
  intro f hf
  obtain ⟨f₀, hf₀, rfl⟩ := List.mem_map.mp hf
  exact internal_val_of_glueClosed hclosed b s' hc' hc
    (mem_internal_of_mem_relInFlagsAt hf₀)

/-! ### Pointwise core data agreement -/

/-- The core-colour entry at the matched flag agrees. -/
private theorem coreOdd_match_entry_closed {ℓ : ℕ}
    (φW : (Fl).CoreOddColouring ℓ) (φ' : (Fg).CoreOddColouring ℓ)
    (hφ : ∀ (g : SurvivingFlag W i j)
      (h1 : g.val ∈ (Fl).coreFlags) (h2 : g ∈ (Fg).coreFlags),
      φW.val ⟨g.val, h1⟩ = φ'.val ⟨g, h2⟩)
    (f' : SurvivingFlag W i j) (_hint : f' ∈ (Fg).internalFlags)
    (h1 : (κW).match_ f'.val ∈ (Fl).coreFlags)
    (h2 : κ'.match_ f' ∈ (Fg).coreFlags) :
    φW.val ⟨(κW).match_ f'.val, h1⟩ =
      φ'.val ⟨κ'.match_ f', h2⟩ := by
  have hmv : (κW).match_ f'.val = (κ'.match_ f').val :=
    unglueClosed_match_val hclosed b s' hc' hc κ' f'
  have hmcoreW : (κ'.match_ f').val ∈ (Fl).coreFlags := by
    rw [← hmv]; exact h1
  exact (congrArg φW.val (Subtype.ext hmv)).trans
    (hφ (κ'.match_ f') hmcoreW h2)

/-- The core odd pair function agrees across the closed glue. -/
private theorem coreOddPairFn_lift_closed {ℓ : ℕ}
    (φW : (Fl).CoreOddColouring ℓ) (φ' : (Fg).CoreOddColouring ℓ)
    (hφ : ∀ (g : SurvivingFlag W i j)
      (h1 : g.val ∈ (Fl).coreFlags) (h2 : g ∈ (Fg).coreFlags),
      φW.val ⟨g.val, h1⟩ = φ'.val ⟨g, h2⟩)
    (f' : SurvivingFlag W i j) (hint : f' ∈ (Fg).internalFlags)
    (hintW : f'.val ∈ (Fl).internalFlags) :
    (Fl).coreOddPairFn (κW) φW ⟨f'.val, hintW⟩ =
      (Fg).coreOddPairFn κ' φ' ⟨f', hint⟩ := by
  unfold EdgeSubset.coreOddPairFn
  refine congrArg₂ (fun x y => [x, oddPartner ℓ y]) ?_ ?_
  · exact hφ f'
      (internalFlags_subset_coreFlags _ hintW)
      (internalFlags_subset_coreFlags _ hint)
  · exact coreOdd_match_entry_closed hclosed s' b hc' hc κ' φW φ'
      hφ f' hint
      (internalFlags_subset_coreFlags _ ((κW).match_mem _ hintW))
      (internalFlags_subset_coreFlags _ (κ'.match_mem _ hint))

/-- The core odd sign function agrees across the closed glue. -/
private theorem coreOddSignFn_lift_closed {ℓ : ℕ}
    (φW : (Fl).CoreOddColouring ℓ) (φ' : (Fg).CoreOddColouring ℓ)
    (hφ : ∀ (g : SurvivingFlag W i j)
      (h1 : g.val ∈ (Fl).coreFlags) (h2 : g ∈ (Fg).coreFlags),
      φW.val ⟨g.val, h1⟩ = φ'.val ⟨g, h2⟩)
    (f' : SurvivingFlag W i j) (hint : f' ∈ (Fg).internalFlags)
    (hintW : f'.val ∈ (Fl).internalFlags) :
    (Fl).coreOddSignFn (κW) φW ⟨f'.val, hintW⟩ =
      (Fg).coreOddSignFn κ' φ' ⟨f', hint⟩ := by
  unfold EdgeSubset.coreOddSignFn
  refine congrArg (oddPartnerSign ℓ) ?_
  exact coreOdd_match_entry_closed hclosed s' b hc' hc κ' φW φ'
    hφ f' hint
    (internalFlags_subset_coreFlags _ ((κW).match_mem _ hintW))
    (internalFlags_subset_coreFlags _ (κ'.match_mem _ hint))

/-! ### The list conversions -/

/-- Converting the flat-mapped pair list along the projection. -/
private theorem flatMap_pair_map_val {ℓ : ℕ}
    (φW : (Fl).CoreOddColouring ℓ) (φ' : (Fg).CoreOddColouring ℓ)
    (hφ : ∀ (g : SurvivingFlag W i j)
      (h1 : g.val ∈ (Fl).coreFlags) (h2 : g ∈ (Fg).coreFlags),
      φW.val ⟨g.val, h1⟩ = φ'.val ⟨g, h2⟩)
    (l : List (SurvivingFlag W i j)) :
    ∀ (H1 : ∀ f ∈ l.map Subtype.val, f ∈ (Fl).internalFlags)
      (H2 : ∀ f' ∈ l, f' ∈ (Fg).internalFlags),
      ((l.map Subtype.val).attachWith
        (· ∈ (Fl).internalFlags) H1).flatMap
          ((Fl).coreOddPairFn (κW) φW) =
      (l.attachWith (· ∈ (Fg).internalFlags) H2).flatMap
        ((Fg).coreOddPairFn κ' φ') := by
  induction l with
  | nil => intro _ _; rfl
  | cons f' t ih =>
    intro H1 H2
    change ((f'.val :: t.map Subtype.val).attachWith
        (· ∈ (Fl).internalFlags) H1).flatMap
          ((Fl).coreOddPairFn (κW) φW) =
      ((f' :: t).attachWith (· ∈ (Fg).internalFlags) H2).flatMap
        ((Fg).coreOddPairFn κ' φ')
    rw [List.attachWith_cons, List.attachWith_cons]
    refine congrArg₂ (· ++ ·) ?_ (ih _ _)
    exact coreOddPairFn_lift_closed hclosed s' b hc' hc κ' φW φ'
      hφ f' (H2 f' (List.mem_cons_self))
      (H1 f'.val (List.mem_map.mpr
        ⟨f', List.mem_cons_self, rfl⟩))

/-- Converting the mapped sign list along the projection. -/
private theorem map_sign_map_val {ℓ : ℕ}
    (φW : (Fl).CoreOddColouring ℓ) (φ' : (Fg).CoreOddColouring ℓ)
    (hφ : ∀ (g : SurvivingFlag W i j)
      (h1 : g.val ∈ (Fl).coreFlags) (h2 : g ∈ (Fg).coreFlags),
      φW.val ⟨g.val, h1⟩ = φ'.val ⟨g, h2⟩)
    (l : List (SurvivingFlag W i j)) :
    ∀ (H1 : ∀ f ∈ l.map Subtype.val, f ∈ (Fl).internalFlags)
      (H2 : ∀ f' ∈ l, f' ∈ (Fg).internalFlags),
      ((l.map Subtype.val).attachWith
        (· ∈ (Fl).internalFlags) H1).map
          ((Fl).coreOddSignFn (κW) φW) =
      (l.attachWith (· ∈ (Fg).internalFlags) H2).map
        ((Fg).coreOddSignFn κ' φ') := by
  induction l with
  | nil => intro _ _; rfl
  | cons f' t ih =>
    intro H1 H2
    change ((f'.val :: t.map Subtype.val).attachWith
        (· ∈ (Fl).internalFlags) H1).map
          ((Fl).coreOddSignFn (κW) φW) =
      ((f' :: t).attachWith (· ∈ (Fg).internalFlags) H2).map
        ((Fg).coreOddSignFn κ' φ')
    rw [List.attachWith_cons, List.attachWith_cons]
    refine congrArg₂ (· :: ·) ?_ (ih _ _)
    exact coreOddSignFn_lift_closed hclosed s' b hc' hc κ' φW φ'
      hφ f' (H2 f' (List.mem_cons_self))
      (H1 f'.val (List.mem_map.mpr
        ⟨f', List.mem_cons_self, rfl⟩))

/-! ### The vertex data transports -/

/-- The even colour multiset agrees across the closed glue. -/
theorem evenColoursAt_transport_closed [LinearOrder α] {k : ℕ}
    (ψW : (Fl).EvenColouring k) (ψ' : (Fg).EvenColouring k)
    (hψ : ∀ (g : SurvivingFlag W i j)
      (h1 : g.val ∉ liftSubsetClosed s' b) (h2 : g ∉ s'),
      ψW.val ⟨g.val, h1⟩ = ψ'.val ⟨g, h2⟩)
    (v : W.Vertex) :
    (Fl).evenColoursAt ψW v = (Fg).evenColoursAt ψ' v := by
  have hemb : ∀ x : {f' : (W.gluePairClosed i j hclosed).Flag //
      f' ∉ (Fg).flags},
      x.val.val ∉ (Fl).flags := by
    intro x hmem
    exact x.prop ((surviving_val_mem_liftClosed_iff s' b
      x.val).mp hmem)
  have hinj : Function.Injective
      (fun x : {f' : (W.gluePairClosed i j hclosed).Flag //
          f' ∉ (Fg).flags} =>
        (⟨x.val.val, hemb x⟩ : {f : W.Flag // f ∉ (Fl).flags}))
      := by
    intro x y hxy
    have hxy' : (⟨x.val.val, hemb x⟩ :
        {f : W.Flag // f ∉ (Fl).flags}) = ⟨y.val.val, hemb y⟩ :=
      hxy
    have hval : x.val.val = y.val.val := congrArg
      (fun z : {f : W.Flag // f ∉ (Fl).flags} => z.val) hxy'
    exact Subtype.ext (Subtype.ext hval)
  unfold EdgeSubset.evenColoursAt
  refine multiset_map_eq_of_bij _ _
    (fun x => ⟨x.val.val, hemb x⟩) hinj ?_ ?_ ψW.val ψ'.val ?_
  · intro y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact glueAttach_inl_iff y.val v
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    have hsurv := vertex_flag_surviving (i := i) (j := j)
      x.val v hx
    have hnot : (⟨x.val, hsurv.1, hsurv.2⟩ :
        SurvivingFlag W i j) ∉ s' := by
      intro hmem
      exact x.prop ((surviving_val_mem_liftClosed_iff s' b
        ⟨x.val, hsurv.1, hsurv.2⟩).mpr hmem)
    exact ⟨⟨⟨x.val, hsurv.1, hsurv.2⟩, hnot⟩, Subtype.ext rfl⟩
  · intro y _
    exact hψ y.val (hemb y) y.prop

/-- The core odd sign at a vertex agrees across the closed
glue. -/
theorem coreOddSignAt_transport_closed {ℓ : ℕ}
    (φW : (Fl).CoreOddColouring ℓ) (φ' : (Fg).CoreOddColouring ℓ)
    (hφ : ∀ (g : SurvivingFlag W i j)
      (h1 : g.val ∈ (Fl).coreFlags) (h2 : g ∈ (Fg).coreFlags),
      φW.val ⟨g.val, h1⟩ = φ'.val ⟨g, h2⟩)
    (v : W.Vertex) :
    (Fl).coreOddSignAt (oW) φW v = (Fg).coreOddSignAt o' φ' v
    := by
  unfold EdgeSubset.coreOddSignAt
  have hperm := perm_attachWith
    (relInFlagsAt_perm_closed hclosed s' b hc' hc κ' o' v)
    (fun _ hf => mem_internal_of_mem_relInFlagsAt hf)
    (mem_map_relInFlagsAt_internal hclosed s' b hc' hc κ' o'
      (v := v))
  rw [List.Perm.prod_eq (hperm.map ((Fl).coreOddSignFn (κW) φW))]
  rw [map_sign_map_val hclosed s' b hc' hc κ' φW φ' hφ
    ((Fg).relInFlagsAt o' v) _
    (fun _ hf => mem_internal_of_mem_relInFlagsAt hf)]
  rfl

/-- The evaluated core odd list at a vertex agrees across the
closed glue. -/
theorem evalOdd_coreOddListAt_transport_closed {k ℓ : ℕ}
    (h : MixedFunctional k ℓ)
    (φW : (Fl).CoreOddColouring ℓ) (φ' : (Fg).CoreOddColouring ℓ)
    (hφ : ∀ (g : SurvivingFlag W i j)
      (h1 : g.val ∈ (Fl).coreFlags) (h2 : g ∈ (Fg).coreFlags),
      φW.val ⟨g.val, h1⟩ = φ'.val ⟨g, h2⟩)
    (μ : Multiset (Fin k)) (v : W.Vertex) :
    h.evalOdd μ ((Fl).coreOddListAt (oW) φW v) =
      h.evalOdd μ ((Fg).coreOddListAt o' φ' v) := by
  unfold EdgeSubset.coreOddListAt
  have hperm := perm_attachWith
    (relInFlagsAt_perm_closed hclosed s' b hc' hc κ' o' v)
    (fun _ hf => mem_internal_of_mem_relInFlagsAt hf)
    (mem_map_relInFlagsAt_internal hclosed s' b hc' hc κ' o'
      (v := v))
  have hstep := h.evalOdd_flatMap_perm μ
    ((Fl).coreOddPairFn (κW) φW) (fun _ => rfl) hperm []
  simp only [List.nil_append] at hstep
  rw [hstep,
    flatMap_pair_map_val hclosed s' b hc' hc κ' φW φ' hφ
      ((Fg).relInFlagsAt o' v) _
      (fun _ hf => mem_internal_of_mem_relInFlagsAt hf)]
  rfl

/-! ### Boundary-match transports -/

/-- **The vertex factor transport across the closed glue.** -/
theorem vertexFactor_transport_closed [LinearOrder α] {k ℓ : ℕ}
    (h : MixedFunctional k ℓ)
    (ψW : (Fl).EvenColouring k) (ψ' : (Fg).EvenColouring k)
    (hψ : ∀ (g : SurvivingFlag W i j)
      (h1 : g.val ∉ liftSubsetClosed s' b) (h2 : g ∉ s'),
      ψW.val ⟨g.val, h1⟩ = ψ'.val ⟨g, h2⟩)
    (φW : (Fl).CoreOddColouring ℓ) (φ' : (Fg).CoreOddColouring ℓ)
    (hφ : ∀ (g : SurvivingFlag W i j)
      (h1 : g.val ∈ (Fl).coreFlags) (h2 : g ∈ (Fg).coreFlags),
      φW.val ⟨g.val, h1⟩ = φ'.val ⟨g, h2⟩)
    (v : W.Vertex) :
    ((Fl).coreOddSignAt (oW) φW v : ℂ) *
      h.evalOdd ((Fl).evenColoursAt ψW v)
        ((Fl).coreOddListAt (oW) φW v) =
    ((Fg).coreOddSignAt o' φ' v : ℂ) *
      h.evalOdd ((Fg).evenColoursAt ψ' v)
        ((Fg).coreOddListAt o' φ' v) := by
  rw [coreOddSignAt_transport_closed hclosed s' b hc' hc κ' o'
      φW φ' hφ v,
    evenColoursAt_transport_closed hclosed s' b hc' hc ψW ψ'
      hψ v,
    evalOdd_coreOddListAt_transport_closed hclosed s' b hc' hc
      κ' o' h φW φ' hφ ((Fg).evenColoursAt ψ' v) v]

end ClosedEngine

end EdgeSubset

end RS
