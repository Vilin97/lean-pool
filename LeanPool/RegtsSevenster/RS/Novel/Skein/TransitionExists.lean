/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Skein.MixedPartition

/-!
# Existence of transition systems with orientations

Every Eulerian edge subset whose participating flags all attach to
internal vertices admits a transition system equipped with an
orientation.  The construction proceeds in two parts:

1. **The matching κ** (Part 1): at each vertex the participating flags
   have even cardinality (from the Eulerian condition); a fixed-point-free
   involution matching flags at common vertices is built by the finite
   combinatorial lemma `exists_involution_of_even`, applied per-vertex
   and glued into a global function.

2. **The orientation** (Part 2): the edge pairing σ conjugates the
   walk permutation to its inverse; this forces the walk-orbit of f and
   of σ f to be disjoint for every participating f.  An orientation is
   obtained by choosing, for each orbit-pair, one side as "out" using
   orbit representatives under the flag order.
-/

@[expose] public section

namespace RS

/-! ### The involution lemma -/

open Classical in
/-- A finset of even cardinality admits a fixed-point-free involution
mapping the set to itself.  Proved by strong induction on the finset:
for cardinality 0 the properties are vacuous; for cardinality ≥ 2 pick
two distinct elements, match them, and recurse on the remainder. -/
theorem exists_involution_of_even {β : Type}
    (s : Finset β) (hs : Even s.card) :
    ∃ m : β → β, (∀ x ∈ s, m x ∈ s) ∧
      (∀ x ∈ s, m (m x) = x) ∧ (∀ x ∈ s, m x ≠ x) := by
  classical
  revert hs
  exact s.strongInductionOn fun s ih hs => by
    by_cases hempty : s.card = 0
    · exact ⟨id, fun x hx => by simp [Finset.card_eq_zero.mp hempty] at hx,
        fun x hx => by simp [Finset.card_eq_zero.mp hempty] at hx,
        fun x hx => by simp [Finset.card_eq_zero.mp hempty] at hx⟩
    · have hge2 : 1 < s.card := by rcases hs with ⟨k, hk⟩; omega
      rw [Finset.one_lt_card] at hge2
      obtain ⟨a, ha, b, hb, hab⟩ := hge2
      have hb_in_erase : b ∈ s.erase a :=
        Finset.mem_erase.mpr ⟨hab.symm, hb⟩
      set s' := (s.erase a).erase b with hs'_def
      have ha' : a ∉ s' := by simp [hs'_def]
      have hb' : b ∉ s' := by simp [hs'_def]
      have hs'_sub : s' ⊂ s :=
        ssubset_trans (Finset.erase_ssubset hb_in_erase) (Finset.erase_ssubset
          ha)
      have hs'_card : s'.card = s.card - 2 := by
        have h1 : (s.erase a).card = s.card - 1 := Finset.card_erase_of_mem ha
        have h2 : s'.card = (s.erase a).card - 1 := by
          change ((s.erase a).erase b).card = (s.erase a).card - 1
          exact Finset.card_erase_of_mem hb_in_erase
        omega
      have hs'_even : Even s'.card := by
        rw [hs'_card]
        rcases hs with ⟨k, hk⟩
        exact ⟨k - 1, by omega⟩
      obtain ⟨m', hm'_mem, hm'_invol, hm'_ne⟩ := ih s' hs'_sub hs'_even
      let m (x : β) : β := if x = a then b else if x = b then a else m' x
      have hm_a : m a = b := by simp [m]
      have hm_b : m b = a := by simp [m, hab.symm]
      have hm_other (x : β) (h1 : x ≠ a) (h2 : x ≠ b) : m x = m' x := by
        simp [m, h1, h2]
      refine ⟨m, ?_, ?_, ?_⟩
      · -- m maps s to s
        intro x hx
        by_cases h1 : x = a
        · rw [h1, hm_a]; exact hb
        · by_cases h2 : x = b
          · rw [h2, hm_b]; exact ha
          · rw [hm_other x h1 h2]
            have hxs' : x ∈ s' := by
              simp? [hs'_def, Finset.mem_erase]; exact ⟨h2, h1, hx⟩
            have := hm'_mem x hxs'
            simp? [hs'_def, Finset.mem_erase] at this; exact this.2.2
      · -- m is an involution on s
        intro x hx
        by_cases h1 : x = a
        · rw [h1, hm_a, hm_b]
        · by_cases h2 : x = b
          · rw [h2, hm_b, hm_a]
          · rw [hm_other x h1 h2]
            have hxs' : x ∈ s' := by
              simp? [hs'_def, Finset.mem_erase]; exact ⟨h2, h1, hx⟩
            have hm'x_ne_a : m' x ≠ a := fun heq => ha' (heq ▸ hm'_mem x hxs')
            have hm'x_ne_b : m' x ≠ b := fun heq => hb' (heq ▸ hm'_mem x hxs')
            rw [hm_other (m' x) hm'x_ne_a hm'x_ne_b]
            exact hm'_invol x hxs'
      · -- m has no fixed points on s
        intro x hx hfp
        by_cases h1 : x = a
        · rw [h1, hm_a] at hfp; exact hab hfp.symm
        · by_cases h2 : x = b
          · rw [h2, hm_b] at hfp; exact hab hfp
          · rw [hm_other x h1 h2] at hfp
            have hxs' : x ∈ s' := by
              simp? [hs'_def, Finset.mem_erase]; exact ⟨h2, h1, hx⟩
            exact hm'_ne x hxs' hfp

/-! ### Part 1: constructing the transition system -/

open Classical in
/-- Given an Eulerian edge subset whose flags all attach to internal
vertices, construct a transition system by building per-vertex
matchings and gluing them. -/
noncomputable def EdgeSubset.buildTransitionSystem {α : Type}
    {W : Fragment α} (F : EdgeSubset W)
    (hE : F.Eulerian) (hint : ∀ f ∈ F.flags, ∃ v : W.Vertex, W.attach f =
      Sum.inl v) :
    F.TransitionSystem := by
  letI := Classical.decEq W.Flag
  letI := Classical.decEq W.Vertex
  letI := Classical.decEq (W.Vertex ⊕ α)
  let flagsAt (v : W.Vertex) : Finset W.Flag :=
    F.flags.filter (fun f => W.attach f = Sum.inl v)
  have heven : ∀ v, Even (flagsAt v).card := hE
  have hinvol : ∀ v, ∃ m : W.Flag → W.Flag,
      (∀ x ∈ flagsAt v, m x ∈ flagsAt v) ∧
      (∀ x ∈ flagsAt v, m (m x) = x) ∧
      (∀ x ∈ flagsAt v, m x ≠ x) :=
    fun v => exists_involution_of_even (flagsAt v) (heven v)
  let mv (v : W.Vertex) := (hinvol v).choose
  have hmv_spec (v : W.Vertex) := (hinvol v).choose_spec
  let vertexOf (f : W.Flag) (hf : f ∈ F.flags) : W.Vertex := (hint f hf).choose
  have hvertexOf (f : W.Flag) (hf : f ∈ F.flags) :
      W.attach f = Sum.inl (vertexOf f hf) := (hint f hf).choose_spec
  let globalMatch (f : W.Flag) : W.Flag :=
    if hf : f ∈ F.flags then mv (vertexOf f hf) f else f
  have hf_in_flagsAt (f : W.Flag) (hf : f ∈ F.flags) :
      f ∈ flagsAt (vertexOf f hf) :=
    Finset.mem_filter.mpr ⟨hf, hvertexOf f hf⟩
  have hgm_unfold (f : W.Flag) (hf : f ∈ F.flags) :
      globalMatch f = mv (vertexOf f hf) f := dite_eq_left hf
  have hmatch_mem : ∀ f ∈ F.flags, globalMatch f ∈ F.flags := by
    intro f hf
    rw [hgm_unfold f hf]
    exact (Finset.mem_filter.mp ((hmv_spec (vertexOf f hf)).1 f (hf_in_flagsAt f
      hf))).1
  have hmatch_invol : ∀ f ∈ F.flags, globalMatch (globalMatch f) = f := by
    intro f hf
    have hgf : globalMatch f ∈ F.flags := hmatch_mem f hf
    rw [hgm_unfold (globalMatch f) hgf]
    -- Goal: mv (vertexOf (globalMatch f) hgf) (globalMatch f) = f
    have hmvf_in : mv (vertexOf f hf) f ∈ flagsAt (vertexOf f hf) :=
      (hmv_spec (vertexOf f hf)).1 f (hf_in_flagsAt f hf)
    have hmvf_attach : W.attach (mv (vertexOf f hf) f) =
        Sum.inl (vertexOf f hf) :=
      (Finset.mem_filter.mp hmvf_in).2
    have hvv' : vertexOf (globalMatch f) hgf = vertexOf f hf := by
      apply Sum.inl.inj
      rw [← hvertexOf (globalMatch f) hgf, hgm_unfold f hf]
      exact hmvf_attach
    conv_lhs => rw [hvv']
    -- Goal: mv (vertexOf f hf) (globalMatch f) = f
    rw [hgm_unfold f hf]
    -- Goal: mv (vertexOf f hf) (mv (vertexOf f hf) f) = f
    exact (hmv_spec (vertexOf f hf)).2.1 f (hf_in_flagsAt f hf)
  have hmatch_ne : ∀ f ∈ F.flags, globalMatch f ≠ f := by
    intro f hf
    rw [hgm_unfold f hf]
    exact (hmv_spec (vertexOf f hf)).2.2 f (hf_in_flagsAt f hf)
  have hmatch_vertex : ∀ f ∈ F.flags, ∀ v : W.Vertex,
      W.attach f = Sum.inl v → W.attach (globalMatch f) = Sum.inl v := by
    intro f hf v hv
    rw [hgm_unfold f hf]
    have hmvf_in : mv (vertexOf f hf) f ∈ flagsAt (vertexOf f hf) :=
      (hmv_spec (vertexOf f hf)).1 f (hf_in_flagsAt f hf)
    have hv_eq : vertexOf f hf = v :=
      Sum.inl.inj ((hvertexOf f hf).symm.trans hv)
    rw [← hv_eq]; exact (Finset.mem_filter.mp hmvf_in).2
  exact {
    match_ := globalMatch
    match_invol := hmatch_invol
    match_ne := hmatch_ne
    match_mem := hmatch_mem
    match_vertex := hmatch_vertex
    attach_internal := hint
  }

/-! ### Part 2: the walk–pairing conjugation and orientation -/

namespace EdgeSubset.TransitionSystem

variable {α : Type} {W : Fragment α} {F : EdgeSubset W}

/-- The walk applied to σ f gives κ f, since walk(σ f) = κ(σ(σ f)) = κ f. -/
theorem walk_pairing_eq (κ : F.TransitionSystem)
    {f : W.Flag} (_hf : f ∈ F.flags) :
    κ.walk (W.pairing f) = κ.match_ f := by
  unfold walk; rw [W.pairing_invol]

/-- Fundamental computation: walk(σ(walk(σ f))) = f for participating f. -/
theorem walk_pairing_walk_pairing (κ : F.TransitionSystem)
    {f : W.Flag} (hf : f ∈ F.flags) :
    κ.walk (W.pairing (κ.walk (W.pairing f))) = f := by
  unfold walk; rw [W.pairing_invol, W.pairing_invol]
  exact κ.match_invol f hf

end EdgeSubset.TransitionSystem

/-- The edge pairing as a permutation of participating flags. -/
noncomputable def EdgeSubset.pairingPerm {α : Type} {W : Fragment α}
    (F : EdgeSubset W) :
    Equiv.Perm {f : W.Flag // f ∈ F.flags} :=
  Equiv.ofBijective
    (fun f => ⟨W.pairing f.val, F.pairing_mem f.val f.prop⟩)
    (Finite.injective_iff_bijective.mp (fun ⟨f, hf⟩ ⟨g, hg⟩ h => by
      have hval : W.pairing f = W.pairing g := congrArg Subtype.val h
      have : f = g :=
        (W.pairing_invol f).symm.trans ((congrArg W.pairing hval).trans
          (W.pairing_invol g))
      exact Subtype.ext this))

section PairingPerm

variable {α : Type} {W : Fragment α} {F : EdgeSubset W}

/-- The edge pairing as a permutation of participating flags. -/
@[simp]
theorem EdgeSubset.pairingPerm_val (x : {f : W.Flag // f ∈ F.flags}) :
    (F.pairingPerm x).val = W.pairing x.val := by
  simp [EdgeSubset.pairingPerm, Equiv.ofBijective]

/-- σ² = 1 on participating flags. -/
theorem EdgeSubset.pairingPerm_mul_self :
    F.pairingPerm * F.pairingPerm = (1 : Equiv.Perm {f : W.Flag // f ∈ F.flags})
      := by
  ext ⟨f, hf⟩
  simp [Equiv.Perm.mul_apply, Equiv.Perm.one_apply, W.pairing_invol f]

/-- It is its own inverse. -/
theorem EdgeSubset.pairingPerm_inv :
    F.pairingPerm⁻¹ = (F.pairingPerm : Equiv.Perm {f : W.Flag // f ∈ F.flags})
      :=
  mul_left_cancel (by rw [mul_inv_cancel, EdgeSubset.pairingPerm_mul_self])

end PairingPerm

namespace EdgeSubset.TransitionSystem

variable {α : Type} {W : Fragment α} {F : EdgeSubset W}

/-- The walk permutation acts by the walk step. -/
@[simp]
theorem walkPerm_val (κ : F.TransitionSystem)
    (x : {f : W.Flag // f ∈ F.flags}) :
    (κ.walkPerm x).val = κ.walk x.val := by
  simp [walkPerm, Equiv.ofBijective]

/-- σ ∘ walk ∘ σ = walk⁻¹: the edge pairing conjugates the walk
permutation to its inverse. -/
theorem conj_eq_inv (κ : F.TransitionSystem) :
    F.pairingPerm * κ.walkPerm * F.pairingPerm = κ.walkPerm⁻¹ := by
  have h : κ.walkPerm * (F.pairingPerm * κ.walkPerm * F.pairingPerm) = 1 := by
    apply Equiv.Perm.ext; intro ⟨f, hf⟩
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
    exact Subtype.ext (by
      simp only [walkPerm_val, EdgeSubset.pairingPerm_val]
      exact κ.walk_pairing_walk_pairing hf)
  exact mul_left_cancel (by rw [h, mul_inv_cancel])

/-- σ ∘ walk^n ∘ σ = walk^{−n} for all n : ℤ. -/
theorem conj_zpow (κ : F.TransitionSystem) (n : ℤ) :
    F.pairingPerm * κ.walkPerm ^ n * F.pairingPerm = κ.walkPerm ^ (-n) := by
  have hσ_inv := EdgeSubset.pairingPerm_inv (F := F)
  calc F.pairingPerm * κ.walkPerm ^ n * F.pairingPerm
      = F.pairingPerm * κ.walkPerm ^ n * F.pairingPerm⁻¹ := by
        congr 1; exact hσ_inv.symm
    _ = (MulAut.conj F.pairingPerm) (κ.walkPerm ^ n) := rfl
    _ = ((MulAut.conj F.pairingPerm) κ.walkPerm) ^ n :=
        map_zpow (MulAut.conj F.pairingPerm).toMonoidHom κ.walkPerm n
    _ = κ.walkPerm⁻¹ ^ n := by
        congr 1
        change F.pairingPerm * κ.walkPerm * F.pairingPerm⁻¹ = κ.walkPerm⁻¹
        rw [hσ_inv]; exact κ.conj_eq_inv
    _ = κ.walkPerm ^ (-n) := inv_zpow' κ.walkPerm n

/-- If f and σ f were in the same walk-orbit, the conjugation identity
forces a contradiction. -/
theorem pairing_not_sameCycle (κ : F.TransitionSystem)
    {f : W.Flag} (hf : f ∈ F.flags) :
    ¬ κ.walkPerm.SameCycle ⟨f, hf⟩
      ⟨W.pairing f, F.pairing_mem f hf⟩ := by
  intro hsame
  obtain ⟨m, hm_pos, _, hm_eq⟩ := hsame.exists_pow_eq''
  have hconj_applied : ∀ n : ℤ,
      F.pairingPerm ((κ.walkPerm ^ n) (F.pairingPerm ⟨f, hf⟩)) =
        (κ.walkPerm ^ (-n)) ⟨f, hf⟩ := fun n => by
    have h := congr_fun (congr_arg DFunLike.coe (κ.conj_zpow n)) ⟨f, hf⟩
    simpa only [Equiv.Perm.mul_apply] using h
  have hm' : (κ.walkPerm ^ (m : ℤ)) ⟨f, hf⟩ = F.pairingPerm ⟨f, hf⟩ := by
    rw [zpow_natCast]
    exact Subtype.ext (by
      have := congrArg Subtype.val hm_eq
      simpa only [EdgeSubset.pairingPerm_val] using this)
  have hshift : ∀ n : ℤ,
      F.pairingPerm ((κ.walkPerm ^ (n + ↑m)) ⟨f, hf⟩) =
        (κ.walkPerm ^ (-n)) ⟨f, hf⟩ := by
    intro n
    rw [zpow_add, Equiv.Perm.mul_apply, hm']
    exact hconj_applied n
  rcases Nat.even_or_odd m with ⟨j, hj⟩ | ⟨j, hj⟩
  · -- Even case: m = 2*j; σ(walk^j f) = walk^j f
    have key := hshift (-(j : ℤ))
    have harith : -(j : ℤ) + ↑m = (j : ℤ) := by omega
    rw [harith, neg_neg] at key
    -- key : pairingPerm (walkPerm^j ⟨f,hf⟩) = walkPerm^j ⟨f,hf⟩
    have hval := congrArg Subtype.val key
    simp only [EdgeSubset.pairingPerm_val] at hval
    -- hval : W.pairing (walkPerm^j ⟨f,hf⟩).val = (walkPerm^j ⟨f,hf⟩).val
    exact W.pairing_ne _ hval
  · -- Odd case: m = 2*j+1; σ(walk^{j+1} f) = walk^j f → κ fixes
    have key := hshift (-(j : ℤ))
    have harith : -(j : ℤ) + ↑m = (j : ℤ) + 1 := by omega
    rw [harith, neg_neg] at key
    -- key : pairingPerm (walkPerm^{j+1} ⟨f,hf⟩) = walkPerm^j ⟨f,hf⟩
    have hstep : (κ.walkPerm ^ ((j : ℤ) + 1)) ⟨f, hf⟩ =
        κ.walkPerm ((κ.walkPerm ^ (j : ℤ)) ⟨f, hf⟩) := by
      conv_lhs => rw [show (j : ℤ) + 1 = 1 + (j : ℤ) from by ring]
      rw [zpow_add, zpow_one, Equiv.Perm.mul_apply]
    rw [hstep] at key
    set g := (κ.walkPerm ^ (j : ℤ)) ⟨f, hf⟩
    -- key : pairingPerm (walkPerm g) = g → σ(walk g.val) = g.val
    have hval : W.pairing (κ.walk g.val) = g.val := by
      have := congrArg Subtype.val key
      simpa only [EdgeSubset.pairingPerm_val, walkPerm_val] using this
    -- So walk g.val = σ g.val (applying σ to both sides)
    have hval2 : κ.walk g.val = W.pairing g.val := by
      have := congrArg W.pairing hval; rw [W.pairing_invol] at this; exact this
    -- walk g.val = match_(σ g.val), contradicting match_ne
    exact κ.match_ne _ (F.pairing_mem g.val g.prop) hval2

/-- κ f is in the walk-orbit of σ f: walk(σ f) = κ f gives a direct
witness. -/
theorem match_sameCycle_pairing (κ : F.TransitionSystem)
    {f : W.Flag} (hf : f ∈ F.flags) :
    κ.walkPerm.SameCycle
      ⟨κ.match_ f, κ.match_mem f hf⟩
      ⟨W.pairing f, F.pairing_mem f hf⟩ := by
  have h : κ.walkPerm.SameCycle
      ⟨W.pairing f, F.pairing_mem f hf⟩
      ⟨κ.match_ f, κ.match_mem f hf⟩ :=
    ⟨1, Subtype.ext (by
      simp only [zpow_one, walkPerm_val]
      exact κ.walk_pairing_eq hf)⟩
  exact h.symm

/-- σ(κ f) is in the walk-orbit of f: walk(σ(κ f)) = κ(σ(σ(κ f))) =
κ(κ f) = f gives a direct witness. -/
theorem pairing_match_sameCycle (κ : F.TransitionSystem)
    {f : W.Flag} (hf : f ∈ F.flags) :
    κ.walkPerm.SameCycle
      ⟨W.pairing (κ.match_ f), F.pairing_mem _ (κ.match_mem f hf)⟩
      ⟨f, hf⟩ :=
  ⟨1, Subtype.ext (by
    simp only [zpow_one, walkPerm_val]
    -- Goal: walk (σ(κ f)) = f
    -- walk g = κ(σ g), so walk(σ(κ f)) = κ(σ(σ(κ f))) = κ(κ f) = f
    show κ.walk (W.pairing (κ.match_ f)) = f
    unfold TransitionSystem.walk
    rw [W.pairing_invol]
    exact κ.match_invol f hf)⟩

end EdgeSubset.TransitionSystem

/-! ### Orientation construction -/

section Orientation

variable {α : Type} {W : Fragment α} {F : EdgeSubset W}

/-- In a linear order, a ≠ b implies decide(a < b) = !decide(b < a). -/
private theorem decide_lt_flip {γ : Type} [LinearOrder γ]
    [DecidableRel ((· < ·) : γ → γ → Prop)]
    {a b : γ} (h : a ≠ b) : decide (a < b) = !decide (b < a) := by
  rcases lt_or_gt_of_ne h with hab | hab
  · simp [hab, show ¬(b < a) from not_lt.mpr hab.le]
  · simp [hab, show ¬(a < b) from not_lt.mpr hab.le]

open Classical in
/-- Construct an orientation for a transition system.  Walk-orbits
come in σ-paired pairs; the orientation assigns "out" to one side
of each pair based on orbit representatives under the flag order. -/
noncomputable def EdgeSubset.TransitionSystem.buildOrientation
    (κ : F.TransitionSystem) : κ.Orientation := by
  letI flagOrd := W.flagOrder
  letI := Classical.dec
  letI subtypeOrd : LinearOrder {f : W.Flag // f ∈ F.flags} :=
    LinearOrder.lift' Subtype.val Subtype.val_injective
  -- Walk-orbit of a participating flag
  let orbitOf (x : {f : W.Flag // f ∈ F.flags}) : Finset {f : W.Flag // f ∈
    F.flags} :=
    Finset.univ.filter (fun y => κ.walkPerm.SameCycle x y)
  have orbit_nonempty (x : {f : W.Flag // f ∈ F.flags}) :
      (orbitOf x).Nonempty :=
    ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Equiv.Perm.SameCycle.rfl⟩⟩
  -- Orbit representative: minimum element
  let orbitMin (x : {f : W.Flag // f ∈ F.flags}) : {f : W.Flag // f ∈ F.flags}
    :=
    (orbitOf x).min' (orbit_nonempty x)
  -- orbitMin constant on walk-orbits
  have orbitMin_eq (x y : {f : W.Flag // f ∈ F.flags})
      (h : κ.walkPerm.SameCycle x y) : orbitMin x = orbitMin y := by
    simp only [orbitMin]
    congr 1
    ext z
    simp only [orbitOf, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun hz => h.symm.trans hz, fun hz => h.trans hz⟩
  -- orbitMin(σ f) ≠ orbitMin(f)
  have orbitMin_pairing_ne (x : {f : W.Flag // f ∈ F.flags}) :
      orbitMin (F.pairingPerm x) ≠ orbitMin x := by
    intro heq
    have hmin_in_x : orbitMin x ∈ orbitOf x := Finset.min'_mem _ _
    have hmin_in_σx : orbitMin (F.pairingPerm x) ∈ orbitOf (F.pairingPerm x) :=
      Finset.min'_mem _ _
    rw [heq] at hmin_in_σx
    simp only [orbitOf, Finset.mem_filter, Finset.mem_univ, true_and]
      at hmin_in_x hmin_in_σx
    -- hmin_in_x : SameCycle x (orbitMin x)
    -- hmin_in_σx : SameCycle (pairingPerm x) (orbitMin x)
    exact κ.pairing_not_sameCycle x.prop (hmin_in_x.trans hmin_in_σx.symm)
  -- κ f is in orbit(σ f), hence orbitMin(κ f) = orbitMin(σ f)
  have orbitMin_match (x : {f : W.Flag // f ∈ F.flags}) :
      orbitMin ⟨κ.match_ x.val, κ.match_mem x.val x.prop⟩ =
        orbitMin (F.pairingPerm x) := by
    apply orbitMin_eq
    -- Need: SameCycle ⟨κ x.val, _⟩ (pairingPerm x)
    have h := κ.match_sameCycle_pairing x.prop
    -- h : SameCycle ⟨κ x.val, _⟩ ⟨σ x.val, F.pairing_mem x.val x.prop⟩
    -- pairingPerm x has val = σ x.val
    convert h using 1
    exact Subtype.ext (by simp)
  -- σ(κ f) is in orbit(f), hence orbitMin(σ(κ f)) = orbitMin(f)
  have orbitMin_pairing_match (x : {f : W.Flag // f ∈ F.flags}) :
      orbitMin (F.pairingPerm ⟨κ.match_ x.val, κ.match_mem x.val x.prop⟩) =
        orbitMin x := by
    apply orbitMin_eq
    -- Need: SameCycle (pairingPerm ⟨κ x.val, _⟩) x
    have h := κ.pairing_match_sameCycle x.prop
    -- h : SameCycle ⟨σ(κ x.val), _⟩ ⟨x.val, x.prop⟩
    convert h using 1
    exact Subtype.ext (by simp)
  -- Define isOut
  let isOut (g : W.Flag) : Bool :=
    if hg : g ∈ F.flags then
      decide (orbitMin (F.pairingPerm ⟨g, hg⟩) < orbitMin ⟨g, hg⟩)
    else false
  -- match_flip
  have hmatch_flip : ∀ g ∈ F.flags, isOut (κ.match_ g) = !isOut g := by
    intro g hg
    simp only [isOut, dite_eq_left hg, dite_eq_left (κ.match_mem g hg)]
    rw [orbitMin_pairing_match ⟨g, hg⟩, orbitMin_match ⟨g, hg⟩]
    exact decide_lt_flip (Ne.symm (orbitMin_pairing_ne ⟨g, hg⟩))
  -- pairing_flip
  have hpairing_flip : ∀ g ∈ F.flags, isOut (W.pairing g) = !isOut g := by
    intro g hg
    simp only [isOut, dite_eq_left hg, dite_eq_left (F.pairing_mem g hg)]
    -- pairingPerm ⟨σ g, _⟩ = ⟨g, hg⟩ (since σ² = id)
    have hσσ : F.pairingPerm ⟨W.pairing g, F.pairing_mem g hg⟩ = ⟨g, hg⟩ :=
      Subtype.ext (by simp [W.pairing_invol g])
    -- ⟨σ g, _⟩ = pairingPerm ⟨g, hg⟩
    have hσ_eq : (⟨W.pairing g, F.pairing_mem g hg⟩ :
        {f : W.Flag // f ∈ F.flags}) = F.pairingPerm ⟨g, hg⟩ :=
      Subtype.ext (by simp)
    rw [hσσ, hσ_eq]
    exact decide_lt_flip (Ne.symm (orbitMin_pairing_ne ⟨g, hg⟩))
  exact ⟨isOut, hmatch_flip, hpairing_flip⟩

/-! ### The main theorem -/

open Classical in
/-- An Eulerian edge subset with internally-attached flags admits a
transition system equipped with an orientation. -/
theorem EdgeSubset.exists_transition_orientation {α : Type}
    {W : Fragment α} (F : EdgeSubset W) (hE : F.Eulerian)
    (hint : ∀ f ∈ F.flags, ∃ v : W.Vertex, W.attach f = Sum.inl v) :
    Nonempty ((κ : F.TransitionSystem) × κ.Orientation) :=
  let κ := F.buildTransitionSystem hE hint
  ⟨⟨κ, κ.buildOrientation⟩⟩

end Orientation

end RS
