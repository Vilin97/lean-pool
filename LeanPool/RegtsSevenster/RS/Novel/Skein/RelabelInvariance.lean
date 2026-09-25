/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Skein.CanonExistence

/-!
# Monotone relabel invariance of the corrected constrained value

Transporting a fragment along an order isomorphism of its label
types leaves the corrected state-constrained partition value
unchanged, up to composing the boundary state with the
isomorphism.  `Fragment.relabel` keeps the flags, vertices,
pairing, and circles on the nose and only re-decorates the
boundary attachments, so every ingredient of the through value is
transported by identity-shaped conversions; the orientation guard
`i < j` of the through product is preserved because the relabeling
is monotone.

Both sides of the value are defined by a `Classical.choice` of
relative transition data, so the transport is stated for a value
already pinned to a choice: the relabel carries one side's data to
the other's, and the conversions are identity-shaped.
-/

@[expose] public section

namespace RS



section General

variable {α β : Type} {W : Fragment α} (ee : α ≃ β)

/-! ## Attachment decoding under a relabel -/

/-- The relabel keeps the pairing. -/
theorem relabel_pairing_eq : (W.relabel ee).pairing = W.pairing := rfl

/-- Internal attachment is untouched by a relabel. -/
theorem relabel_attach_inl_iff (f : W.Flag) (v : W.Vertex) :
    (W.relabel ee).attach f = Sum.inl v ↔ W.attach f = Sum.inl v := by
  change (W.attach f).map id ⇑ee = Sum.inl v ↔ W.attach f = Sum.inl v
  rcases W.attach f with w | i <;> simp

/-- Boundary attachment is shifted through the equivalence. -/
theorem relabel_attach_inr_iff (f : W.Flag) (i : α) :
    (W.relabel ee).attach f = Sum.inr (ee i) ↔ W.attach f = Sum.inr i := by
  change (W.attach f).map id ⇑ee = Sum.inr (ee i) ↔ W.attach f = Sum.inr i
  rcases W.attach f with w | j <;> simp

/-- Being internally attached is invariant under a relabel. -/
theorem relabel_attach_inl_exists (f : W.Flag) :
    (∃ v : W.Vertex, (W.relabel ee).attach f = Sum.inl v) ↔
      (∃ v : W.Vertex, W.attach f = Sum.inl v) :=
  exists_congr fun v => relabel_attach_inl_iff ee f v

/-- Being boundary-attached is invariant under a relabel. -/
theorem relabel_attach_inr_exists (f : W.Flag) :
    (∃ b : β, (W.relabel ee).attach f = Sum.inr b) ↔
      (∃ i : α, W.attach f = Sum.inr i) := by
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨ee.symm b, (relabel_attach_inr_iff ee f (ee.symm b)).mp ?_⟩
    rwa [Equiv.apply_symm_apply]
  · rintro ⟨i, hi⟩
    exact ⟨ee i, (relabel_attach_inr_iff ee f i).mpr hi⟩

private theorem filter_eq_of_iff {γ : Type} {p q : γ → Prop}
    {ip : DecidablePred p} {iq : DecidablePred q} {s t : Finset γ}
    (hst : s = t) (h : ∀ x, p x ↔ q x) :
    @Finset.filter γ p ip s = @Finset.filter γ q iq t := by
  subst hst
  ext x
  simp only [Finset.mem_filter]
  exact and_congr Iff.rfl (h x)

/-- The relabelled boundary flag at a pushed-forward label. -/
theorem relabel_boundaryFlag_apply (a : α) :
    (W.relabel ee).boundaryFlag (ee a) = W.boundaryFlag a := by
  change W.boundaryFlag (ee.symm (ee a)) = W.boundaryFlag a
  rw [Equiv.symm_apply_apply]

/-! ## Edge subsets under a relabel -/

/-- Transport of an edge subset along a relabel: the flags and the
pairing are untouched. -/
def EdgeSubset.relabelUp (F : EdgeSubset W) : EdgeSubset (W.relabel ee) where
  flags := F.flags
  pairing_mem := fun f hf => F.pairing_mem f hf

/-- Transport of an edge subset back along a relabel. -/
def EdgeSubset.relabelDown (F : EdgeSubset (W.relabel ee)) : EdgeSubset W where
  flags := F.flags
  pairing_mem := fun f hf => F.pairing_mem f hf

/-- Degrees are untouched by a relabel. -/
theorem relabelUp_deg (F : EdgeSubset W) (v : W.Vertex) :
    (F.relabelUp ee).deg v = F.deg v := by
  unfold EdgeSubset.deg
  exact congrArg Finset.card
    (filter_eq_of_iff rfl fun f => relabel_attach_inl_iff ee f v)

/-- The Eulerian condition is invariant under a relabel. -/
theorem relabelUp_eulerian (F : EdgeSubset W) :
    (F.relabelUp ee).Eulerian ↔ F.Eulerian := by
  unfold EdgeSubset.Eulerian
  exact forall_congr' fun v => by rw [relabelUp_deg ee F v]

/-- The internal flags are untouched by a relabel. -/
theorem relabelUp_internalFlags (F : EdgeSubset W) :
    (F.relabelUp ee).internalFlags = F.internalFlags := by
  unfold EdgeSubset.internalFlags
  exact filter_eq_of_iff rfl fun f => relabel_attach_inl_exists ee f

/-- The through flags are untouched by a relabel. -/
theorem relabelUp_throughFlags (F : EdgeSubset W) :
    (F.relabelUp ee).throughFlags = F.throughFlags := by
  unfold EdgeSubset.throughFlags
  exact filter_eq_of_iff rfl fun f =>
    and_congr (relabel_attach_inr_exists ee f)
      (relabel_attach_inr_exists ee (W.pairing f))

/-- The core flags are untouched by a relabel. -/
theorem relabelUp_coreFlags (F : EdgeSubset W) :
    (F.relabelUp ee).coreFlags = F.coreFlags := by
  unfold EdgeSubset.coreFlags
  rw [relabelUp_throughFlags]
  rfl

/-! ## The boundary-state matching under a relabel -/

/-- The subset boundary constraint reindexes through the
equivalence. -/
theorem relabel_genBoundarySubsetMatches_iff {k ℓ : ℕ}
    (s : Finset W.Flag) (st : GenBoundaryState k ℓ β) :
    genBoundarySubsetMatches (W.relabel ee) s st ↔
      genBoundarySubsetMatches W s (fun a => st (ee a)) := by
  constructor
  · intro hm a
    have h := hm (ee a)
    rw [relabel_boundaryFlag_apply ee a] at h
    exact h
  · intro hm b
    have h := hm (ee.symm b)
    simp only [Equiv.apply_symm_apply] at h
    exact h

/-! ## Relative transition systems under a relabel -/

/-- Transport of a relative transition system along a relabel. -/
def relabelTransUp (F : EdgeSubset W) (κ : F.RelTransitionSystem) :
    (F.relabelUp ee).RelTransitionSystem where
  match_ := κ.match_
  match_invol := fun f hf =>
    κ.match_invol f (by rwa [relabelUp_internalFlags ee F] at hf)
  match_ne := fun f hf =>
    κ.match_ne f (by rwa [relabelUp_internalFlags ee F] at hf)
  match_mem := fun f hf => by
    rw [relabelUp_internalFlags ee F]
    exact κ.match_mem f (by rwa [relabelUp_internalFlags ee F] at hf)
  match_vertex := fun f hf v hv =>
    (relabel_attach_inl_iff ee _ v).mpr
      (κ.match_vertex f (by rwa [relabelUp_internalFlags ee F] at hf) v
        ((relabel_attach_inl_iff ee f v).mp hv))

/-- Transport of a relative transition system back along a
relabel. -/
def relabelTransDown (F : EdgeSubset W)
    (κ : (F.relabelUp ee).RelTransitionSystem) : F.RelTransitionSystem where
  match_ := κ.match_
  match_invol := fun f hf =>
    κ.match_invol f (by rw [relabelUp_internalFlags ee F]; exact hf)
  match_ne := fun f hf =>
    κ.match_ne f (by rw [relabelUp_internalFlags ee F]; exact hf)
  match_mem := fun f hf => by
    have h := κ.match_mem f (by rw [relabelUp_internalFlags ee F]; exact hf)
    rwa [relabelUp_internalFlags ee F] at h
  match_vertex := fun f hf v hv =>
    (relabel_attach_inl_iff ee _ v).mp
      (κ.match_vertex f (by rw [relabelUp_internalFlags ee F]; exact hf) v
        ((relabel_attach_inl_iff ee f v).mpr hv))

/-- Transport of an orientation along a relabel. -/
def relabelOrientUp (F : EdgeSubset W) {κ : F.RelTransitionSystem}
    (o : κ.Orientation) : (relabelTransUp ee F κ).Orientation where
  isOut := o.isOut
  match_flip := fun f hf =>
    o.match_flip f (by rwa [relabelUp_internalFlags ee F] at hf)
  pairing_flip := fun f hf hp =>
    o.pairing_flip f (by rwa [relabelUp_internalFlags ee F] at hf)
      (by rwa [relabelUp_internalFlags ee F] at hp)

/-- Transport of an orientation back along a relabel. -/
def relabelOrientDown (F : EdgeSubset W)
    {κ : (F.relabelUp ee).RelTransitionSystem} (o : κ.Orientation) :
    (relabelTransDown ee F κ).Orientation where
  isOut := o.isOut
  match_flip := fun f hf =>
    o.match_flip f (by rw [relabelUp_internalFlags ee F]; exact hf)
  pairing_flip := fun f hf hp =>
    o.pairing_flip f (by rw [relabelUp_internalFlags ee F]; exact hf)
      (by rw [relabelUp_internalFlags ee F]; exact hp)

/-! ## The open circuit count under a relabel -/

/-- The iterated walk is untouched by a relabel. -/
theorem relabel_iterWalk (F : EdgeSubset W) (κ : F.RelTransitionSystem)
    (f : W.Flag) (n : ℕ) :
    EdgeSubset.iterWalk (relabelTransUp ee F κ) f n =
      EdgeSubset.iterWalk κ f n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (relabelTransUp ee F κ).match_ ((W.relabel ee).pairing
        (EdgeSubset.iterWalk (relabelTransUp ee F κ) f n)) =
      κ.match_ (W.pairing (EdgeSubset.iterWalk κ f n))
    rw [ih]
    rfl

/-- The periodic flags are untouched by a relabel. -/
theorem relabel_periodicFlags (F : EdgeSubset W)
    (κ : F.RelTransitionSystem) :
    (relabelTransUp ee F κ).periodicFlags = κ.periodicFlags := by
  unfold EdgeSubset.RelTransitionSystem.periodicFlags
  refine filter_eq_of_iff (relabelUp_internalFlags ee F) fun f => ?_
  constructor
  · rintro ⟨n, hn, hcont, hper⟩
    refine ⟨n, hn, fun j hj => ?_, ?_⟩
    · have h := hcont j hj
      rw [relabel_iterWalk ee F κ f j, relabelUp_internalFlags ee F] at h
      exact h
    · have h := hper
      rw [relabel_iterWalk ee F κ f n] at h
      exact h
  · rintro ⟨n, hn, hcont, hper⟩
    refine ⟨n, hn, fun j hj => ?_, ?_⟩
    · rw [relabel_iterWalk ee F κ f j, relabelUp_internalFlags ee F]
      exact hcont j hj
    · rw [relabel_iterWalk ee F κ f n]
      exact hper

/-- The periodic-flag subtypes agree under a relabel. -/
noncomputable def relabelPeriodicEquiv (F : EdgeSubset W)
    (κ : F.RelTransitionSystem) :
    {f : W.Flag // f ∈ (relabelTransUp ee F κ).periodicFlags} ≃
      {f : W.Flag // f ∈ κ.periodicFlags} where
  toFun g := ⟨g.val, by
    rw [← relabel_periodicFlags ee F κ]; exact g.prop⟩
  invFun g := ⟨g.val, by
    rw [relabel_periodicFlags ee F κ]; exact g.prop⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

/-- The periodic walk permutations agree under the canonical
equivalence. -/
theorem relabel_walkPermPeriodic (F : EdgeSubset W)
    (κ : F.RelTransitionSystem) :
    (relabelTransUp ee F κ).walkPermPeriodic =
      (relabelPeriodicEquiv ee F κ).symm.permCongr κ.walkPermPeriodic := by
  ext ⟨f, hf⟩
  simp only [EdgeSubset.RelTransitionSystem.walkPermPeriodic,
    Equiv.ofBijective_apply, relabelPeriodicEquiv]
  rfl

/-- The open circuit count is untouched by a relabel. -/
theorem relabel_openCircuitCount (F : EdgeSubset W)
    (κ : F.RelTransitionSystem) :
    (relabelTransUp ee F κ).openCircuitCount = κ.openCircuitCount := by
  have h1 : (relabelTransUp ee F κ).walkPermPeriodic.cycleType =
      κ.walkPermPeriodic.cycleType := by
    rw [relabel_walkPermPeriodic ee F κ]
    exact cycleType_permCongr _ _
  have h2 : Fintype.card
      (Function.fixedPoints ⇑(relabelTransUp ee F κ).walkPermPeriodic) =
      Fintype.card (Function.fixedPoints ⇑κ.walkPermPeriodic) := by
    rw [relabel_walkPermPeriodic ee F κ]
    exact card_fixedPoints_permCongr _ _
  unfold EdgeSubset.RelTransitionSystem.openCircuitCount
  exact congrArg₂ (fun (A B : ℕ) => (A + B) / 2)
    (congrArg Multiset.card h1) h2

/-! ## Colourings under a relabel -/

/-- The core odd colourings agree under a relabel, via the equality
of the core flag sets. -/
noncomputable def coreOddRelabelEquiv (F : EdgeSubset W) (ℓ : ℕ) :
    (F.relabelUp ee).CoreOddColouring ℓ ≃ F.CoreOddColouring ℓ where
  toFun φ :=
    ⟨fun f => φ.val ⟨f.val, (relabelUp_coreFlags ee F).symm ▸ f.prop⟩,
     fun f => (congrArg φ.val (Subtype.ext rfl)).trans
       (φ.prop ⟨f.val, (relabelUp_coreFlags ee F).symm ▸ f.prop⟩)⟩
  invFun φ :=
    ⟨fun f => φ.val ⟨f.val, (relabelUp_coreFlags ee F) ▸ f.prop⟩,
     fun f => (congrArg φ.val (Subtype.ext rfl)).trans
       (φ.prop ⟨f.val, (relabelUp_coreFlags ee F) ▸ f.prop⟩)⟩
  left_inv φ := Subtype.ext (funext fun _ =>
    congrArg φ.val (Subtype.ext rfl))
  right_inv φ := Subtype.ext (funext fun _ =>
    congrArg φ.val (Subtype.ext rfl))

/-- The even-colour multiset at a vertex is untouched by a
relabel. -/
theorem relabel_evenColoursAt (F : EdgeSubset W) {k : ℕ}
    (ψ : (F.relabelUp ee).EvenColouring k) (v : W.Vertex) :
    (F.relabelUp ee).evenColoursAt ψ v = F.evenColoursAt ψ v := by
  unfold EdgeSubset.evenColoursAt
  refine congrArg (Multiset.map _) (congrArg Finset.val ?_)
  exact filter_eq_of_iff rfl fun f => relabel_attach_inl_iff ee f.val v

/-! ## Vertex-local data under a relabel -/

/-- The in-flag list at a vertex is untouched by a relabel. -/
theorem relabel_relInFlagsAt (F : EdgeSubset W)
    {κ : F.RelTransitionSystem} (o : κ.Orientation) (v : W.Vertex) :
    (F.relabelUp ee).relInFlagsAt (relabelOrientUp ee F o) v =
      F.relInFlagsAt o v := by
  unfold EdgeSubset.relInFlagsAt
  let := (W.relabel ee).flagOrder
  let := Classical.dec
  exact congrArg
    (fun s : Finset (W.relabel ee).Flag => Finset.sort s (· ≤ ·))
    (filter_eq_of_iff rfl fun f =>
      and_congr (relabel_attach_inl_iff ee f v) Iff.rfl)

private theorem attachWith_flatMap_congr {δ γ : Type} {P : δ → Prop}
    (g : {x : δ // P x} → List γ) {l₁ l₂ : List δ} (hl : l₁ = l₂)
    (h₁ : ∀ x ∈ l₁, P x) (h₂ : ∀ x ∈ l₂, P x) :
    (l₁.attachWith P h₁).flatMap g = (l₂.attachWith P h₂).flatMap g := by
  subst hl; rfl

private theorem attachWith_map_congr {δ γ : Type} {P : δ → Prop}
    (g : {x : δ // P x} → γ) {l₁ l₂ : List δ} (hl : l₁ = l₂)
    (h₁ : ∀ x ∈ l₁, P x) (h₂ : ∀ x ∈ l₂, P x) :
    (l₁.attachWith P h₁).map g = (l₂.attachWith P h₂).map g := by
  subst hl; rfl

private theorem flatMap_core_relabel {ℓ : ℕ} (F : EdgeSubset W)
    (κ : F.RelTransitionSystem)
    (φ : (F.relabelUp ee).CoreOddColouring ℓ) (l : List W.Flag) :
    ∀ (h1 : ∀ f ∈ l, f ∈ (F.relabelUp ee).internalFlags)
      (h2 : ∀ f ∈ l, f ∈ F.internalFlags),
      (l.attachWith
          (fun x : (W.relabel ee).Flag =>
            x ∈ (F.relabelUp ee).internalFlags) h1).flatMap
        ((F.relabelUp ee).coreOddPairFn (relabelTransUp ee F κ) φ) =
      (l.attachWith (fun x : W.Flag => x ∈ F.internalFlags) h2).flatMap
        (F.coreOddPairFn κ (coreOddRelabelEquiv ee F ℓ φ)) := by
  induction l with
  | nil => intro h1 h2; rfl
  | cons a as ih =>
    intro h1 h2
    exact congrArg₂ (· ++ ·) rfl
      (ih (fun f hf => h1 f (List.mem_cons_of_mem a hf))
        (fun f hf => h2 f (List.mem_cons_of_mem a hf)))

private theorem map_sign_relabel {ℓ : ℕ} (F : EdgeSubset W)
    (κ : F.RelTransitionSystem)
    (φ : (F.relabelUp ee).CoreOddColouring ℓ) (l : List W.Flag) :
    ∀ (h1 : ∀ f ∈ l, f ∈ (F.relabelUp ee).internalFlags)
      (h2 : ∀ f ∈ l, f ∈ F.internalFlags),
      (l.attachWith
          (fun x : (W.relabel ee).Flag =>
            x ∈ (F.relabelUp ee).internalFlags) h1).map
        ((F.relabelUp ee).coreOddSignFn (relabelTransUp ee F κ) φ) =
      (l.attachWith (fun x : W.Flag => x ∈ F.internalFlags) h2).map
        (F.coreOddSignFn κ (coreOddRelabelEquiv ee F ℓ φ)) := by
  induction l with
  | nil => intro h1 h2; rfl
  | cons a as ih =>
    intro h1 h2
    exact congrArg₂ List.cons rfl
      (ih (fun f hf => h1 f (List.mem_cons_of_mem a hf))
        (fun f hf => h2 f (List.mem_cons_of_mem a hf)))

/-- The vertex odd list is transported by the colouring
equivalence. -/
theorem relabel_coreOddListAt (F : EdgeSubset W) {ℓ : ℕ}
    {κ : F.RelTransitionSystem} (o : κ.Orientation)
    (φ : (F.relabelUp ee).CoreOddColouring ℓ) (v : W.Vertex) :
    (F.relabelUp ee).coreOddListAt (relabelOrientUp ee F o) φ v =
      F.coreOddListAt o (coreOddRelabelEquiv ee F ℓ φ) v := by
  have h2 : ∀ f ∈ (F.relabelUp ee).relInFlagsAt (relabelOrientUp ee F o) v,
      f ∈ F.internalFlags := by
    intro f hf
    have h := EdgeSubset.mem_internal_of_mem_relInFlagsAt hf
    rwa [relabelUp_internalFlags ee F] at h
  refine Eq.trans (flatMap_core_relabel ee F κ φ
    ((F.relabelUp ee).relInFlagsAt (relabelOrientUp ee F o) v)
    (fun _ hf => EdgeSubset.mem_internal_of_mem_relInFlagsAt hf) h2) ?_
  exact attachWith_flatMap_congr _ (relabel_relInFlagsAt ee F o v) h2
    (fun _ hf => EdgeSubset.mem_internal_of_mem_relInFlagsAt hf)

/-- The vertex odd sign is transported by the colouring
equivalence. -/
theorem relabel_coreOddSignAt (F : EdgeSubset W) {ℓ : ℕ}
    {κ : F.RelTransitionSystem} (o : κ.Orientation)
    (φ : (F.relabelUp ee).CoreOddColouring ℓ) (v : W.Vertex) :
    (F.relabelUp ee).coreOddSignAt (relabelOrientUp ee F o) φ v =
      F.coreOddSignAt o (coreOddRelabelEquiv ee F ℓ φ) v := by
  have h2 : ∀ f ∈ (F.relabelUp ee).relInFlagsAt (relabelOrientUp ee F o) v,
      f ∈ F.internalFlags := by
    intro f hf
    have h := EdgeSubset.mem_internal_of_mem_relInFlagsAt hf
    rwa [relabelUp_internalFlags ee F] at h
  refine Eq.trans (congrArg List.prod (map_sign_relabel ee F κ φ
    ((F.relabelUp ee).relInFlagsAt (relabelOrientUp ee F o) v)
    (fun _ hf => EdgeSubset.mem_internal_of_mem_relInFlagsAt hf) h2)) ?_
  exact congrArg List.prod
    (attachWith_map_congr _ (relabel_relInFlagsAt ee F o v) h2
      (fun _ hf => EdgeSubset.mem_internal_of_mem_relInFlagsAt hf))

/-! ## The boundary colour matches under a relabel -/

/-- The even boundary match reindexes through the equivalence. -/
theorem relabel_genEvenBoundaryMatch_iff (F : EdgeSubset W) {k ℓ : ℕ}
    (st : GenBoundaryState k ℓ β)
    (hbnd : genBoundarySubsetMatches (W.relabel ee)
      (F.relabelUp ee).flags st)
    (hbnd' : genBoundarySubsetMatches W F.flags (fun a => st (ee a)))
    (ψ : (F.relabelUp ee).EvenColouring k) :
    genEvenBoundaryMatch (F.relabelUp ee) st hbnd ψ ↔
      genEvenBoundaryMatch F (fun a => st (ee a)) hbnd' ψ := by
  unfold genEvenBoundaryMatch
  constructor
  · intro hm a c hst
    have h := hm (ee a) c hst
    exact (congrArg ψ.val (Subtype.ext
      (relabel_boundaryFlag_apply ee a).symm)).trans h
  · intro hm b c hst
    exact hm (ee.symm b) c
      (by simp only [Equiv.apply_symm_apply]; exact hst)

/-- The core odd boundary match reindexes through the equivalence
and the colouring equivalence. -/
theorem relabel_coreOddBoundaryMatch_iff (F : EdgeSubset W) {k ℓ : ℕ}
    (st : GenBoundaryState k ℓ β)
    (φ : (F.relabelUp ee).CoreOddColouring ℓ) :
    (F.relabelUp ee).coreOddBoundaryMatch st φ ↔
      F.coreOddBoundaryMatch (fun a => st (ee a))
        (coreOddRelabelEquiv ee F ℓ φ) := by
  unfold EdgeSubset.coreOddBoundaryMatch
  constructor
  · intro hm a c hst hcore
    have hcore' : (W.relabel ee).boundaryFlag (ee a) ∈
        (F.relabelUp ee).coreFlags := by
      rw [relabel_boundaryFlag_apply ee a, relabelUp_coreFlags ee F]
      exact hcore
    have h := hm (ee a) c hst hcore'
    exact (congrArg φ.val (Subtype.ext
      (relabel_boundaryFlag_apply ee a).symm)).trans h
  · intro hm b c hst hcore
    have hcore' : W.boundaryFlag (ee.symm b) ∈ F.coreFlags := by
      rw [← relabelUp_coreFlags ee F]
      exact hcore
    exact hm (ee.symm b) c
      (by simp only [Equiv.apply_symm_apply]; exact hst) hcore'

end General

section Order

variable {α β : Type}

/-! ## The through product under a monotone relabel -/

/-- The through product transports along a monotone relabel: the
orientation guard is preserved by monotonicity. -/
theorem relabel_throughProduct
    [LinearOrder α] [LinearOrder β] (e : α ≃o β) {W : Fragment α}
    (F : EdgeSubset W) {k ℓ : ℕ}
    (st : GenBoundaryState k ℓ β) :
    (F.relabelUp e.toEquiv).throughProduct st =
      F.throughProduct (fun a => st (e a)) := by
  unfold EdgeSubset.throughProduct
  refine Finset.prod_bij'
    (fun a _ => (⟨a.val, relabelUp_throughFlags e.toEquiv F ▸ a.prop⟩ :
      {x // x ∈ F.throughFlags}))
    (fun b _ => ⟨b.val, (relabelUp_throughFlags e.toEquiv F).symm ▸ b.prop⟩)
    (fun a _ => Finset.mem_attach _ _) (fun b _ => Finset.mem_attach _ _)
    (fun a _ => Subtype.ext rfl) (fun b _ => Subtype.ext rfl)
    (fun a _ => ?_)
  beta_reduce
  rw [relabel_pairing_eq e.toEquiv]
  rcases ha : W.attach a.val with v | i₀
  · rw [(relabel_attach_inl_iff e.toEquiv a.val v).mpr ha]
  · rcases hb : W.attach (W.pairing a.val) with w | j₀
    · rw [(relabel_attach_inr_iff e.toEquiv a.val i₀).mpr ha,
        (relabel_attach_inl_iff e.toEquiv (W.pairing a.val) w).mpr hb]
    · rw [(relabel_attach_inr_iff e.toEquiv a.val i₀).mpr ha,
        (relabel_attach_inr_iff e.toEquiv (W.pairing a.val) j₀).mpr hb]
      change (if e.toEquiv i₀ < e.toEquiv j₀ then
          throughStateFactor (st (e.toEquiv i₀)) (st (e.toEquiv j₀))
          else 1) =
        (if i₀ < j₀ then throughStateFactor (st (e i₀)) (st (e j₀))
          else 1)
      exact if_congr e.lt_iff_lt rfl rfl

/-! ## The through summand and value under a monotone relabel -/

/-- The corrected constrained summand transports along a monotone
relabel, at converted transition data. -/
theorem relabel_throughSummand
    [LinearOrder α] [LinearOrder β] (e : α ≃o β) {W : Fragment α}
    (F : EdgeSubset W) {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) (st : GenBoundaryState k ℓ β)
    (hbnd : genBoundarySubsetMatches (W.relabel e.toEquiv)
      (F.relabelUp e.toEquiv).flags st)
    (hbnd' : genBoundarySubsetMatches W F.flags (fun a => st (e a)))
    {κ : F.RelTransitionSystem} (o : κ.Orientation) (c : ℕ) :
    (F.relabelUp e.toEquiv).throughSummand h st hbnd
        (relabelOrientUp e.toEquiv F o) c =
      F.throughSummand h (fun a => st (e a)) hbnd' o c := by
  unfold EdgeSubset.throughSummand
  rw [relabel_throughProduct e F st]
  refine congrArg (fun z => (-1 : ℂ) ^ c *
    F.throughProduct (fun a => st (e a)) * z) ?_
  refine Fintype.sum_equiv
    (Equiv.refl ((F.relabelUp e.toEquiv).EvenColouring k) :
      (F.relabelUp e.toEquiv).EvenColouring k ≃ F.EvenColouring k)
    _ _ fun ψ => ?_
  simp only [Equiv.refl_apply]
  refine if_congr
    (relabel_genEvenBoundaryMatch_iff e.toEquiv F st hbnd hbnd' ψ) ?_ rfl
  refine Fintype.sum_equiv (coreOddRelabelEquiv e.toEquiv F ℓ) _ _
    fun φ => ?_
  refine if_congr
    (relabel_coreOddBoundaryMatch_iff e.toEquiv F st φ) ?_ rfl
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [relabel_coreOddSignAt e.toEquiv F o φ v,
    relabel_coreOddListAt e.toEquiv F o φ v,
    relabel_evenColoursAt e.toEquiv F ψ v]

end Order

/-! ## The canonical-value migration

The corrected constrained value chooses among *path-canonical*
transition data and weights the chosen summand by the chord-crossing
sign.  Every ingredient transports along a monotone relabel: the
path matching is untouched (the walk and the flag classification
are), canonicality transports because labels move monotonically,
and the crossing count is invariant because the four chord
endpoints of each pair shift through the order isomorphism, which
preserves every comparison. -/

section Canon

variable {α β : Type}

open EdgeSubset

/-- The boundary flags are untouched by a relabel. -/
theorem relabelUp_boundaryFlags
    [LinearOrder α] [LinearOrder β] (e : α ≃o β) {W : Fragment α}
    (F : EdgeSubset W) :
    (F.relabelUp e.toEquiv).boundaryFlags = F.boundaryFlags := by
  unfold EdgeSubset.boundaryFlags
  exact filter_eq_of_iff rfl fun f => relabel_attach_inr_exists e.toEquiv f

/-- The path matching is untouched by a relabel: the transported
walk agrees step by step, so the transported chain data terminate at
the same flag. -/
theorem relabel_pathMatch
    [LinearOrder α] [LinearOrder β] (e : α ≃o β) {W : Fragment α}
    (F : EdgeSubset W) (κ : F.RelTransitionSystem)
    {b : W.Flag} (hb : b ∈ (F.relabelUp e.toEquiv).boundaryFlags)
    (hb' : b ∈ F.boundaryFlags) :
    (relabelTransUp e.toEquiv F κ).pathMatch b hb = κ.pathMatch b hb' := by
  obtain ⟨k, -, hcont, hpm⟩ := pathMatch_chain_length κ hb'
  have hcont' : ∀ t, t < k →
      (W.relabel e.toEquiv).pairing
          (iterWalk (relabelTransUp e.toEquiv F κ) b t) ∈
        (F.relabelUp e.toEquiv).internalFlags := by
    intro t ht
    rw [relabel_iterWalk e.toEquiv F κ b t,
      relabelUp_internalFlags e.toEquiv F]
    exact hcont t ht
  have hterm' : (W.relabel e.toEquiv).pairing
      (iterWalk (relabelTransUp e.toEquiv F κ) b k) ∈
        (F.relabelUp e.toEquiv).boundaryFlags := by
    rw [relabel_iterWalk e.toEquiv F κ b k,
      relabelUp_boundaryFlags e F]
    exact hpm ▸ κ.pathMatch_mem hb'
  rw [pathMatch_eq_of_chain (relabelTransUp e.toEquiv F κ) hb hcont' hterm',
    hpm]
  exact congrArg (W.relabel e.toEquiv).pairing
    (relabel_iterWalk e.toEquiv F κ b k)

/-- **Canonicality transport**: the transported orientation of a
path-canonical orientation is path-canonical — labels transport
monotonically, and every other ingredient is untouched. -/
theorem pathCanonical_relabelUp
    [LinearOrder α] [LinearOrder β] (e : α ≃o β) {W : Fragment α}
    (F : EdgeSubset W)
    {κ : F.RelTransitionSystem} {o : κ.Orientation}
    (hc : PathCanonical o) :
    PathCanonical (relabelOrientUp e.toEquiv F o) := by
  intro i j hb hint hpm hij
  have hb₀ : W.boundaryFlag (e.toEquiv.symm i) ∈ F.boundaryFlags := by
    rw [← relabelUp_boundaryFlags e F]
    exact hb
  have hint₀ : W.pairing (W.boundaryFlag (e.toEquiv.symm i)) ∈
      F.internalFlags := by
    rw [← relabelUp_internalFlags e.toEquiv F]
    exact hint
  have hpm₀ : κ.pathMatch (W.boundaryFlag (e.toEquiv.symm i)) hb₀ =
      W.boundaryFlag (e.toEquiv.symm j) :=
    (relabel_pathMatch e F κ hb hb₀).symm.trans hpm
  have hij₀ : e.toEquiv.symm i < e.toEquiv.symm j :=
    e.symm.lt_iff_lt.mpr hij
  exact hc (e.toEquiv.symm i) (e.toEquiv.symm j) hb₀ hint₀ hpm₀ hij₀

end Canon

end RS
