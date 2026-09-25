/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Skein.EdgeSum
public import LeanPool.RegtsSevenster.RS.Novel.Skein.CutMatching
public import LeanPool.RegtsSevenster.RS.Novel.Skein.SuperGram
public import LeanPool.RegtsSevenster.RS.Novel.Skein.GluePathMatch
public import LeanPool.RegtsSevenster.RS.Novel.Skein.ConverseDischarge

/-!
# The fragment tensor

RS21 attaches to a fragment, an Eulerian subset, an Eulerian
orientation and a compatible local pairing the tensor

    t′_h(F,H,ω,κ) := Σ_χ t′_{h,χ}(F,H,ω,κ),

    t′_{h,χ} := (−1)^{ĉ(κ)} Σ_{ψ ∼ χ₀, φ ∼ χ₁}
                  ∏_{v ∈ V′(F)} h_v( … ) ⊗_{i ∈ [t]} c_{χ,ω,i}.

A basis coordinate of the tensor determines `χ`: an entering leg
carries `f_{χ₁(i)}`, so its coordinate is `χ₁(i)` itself, and a
leaving leg carries `g_{χ₁(i)}`, whose expansion is the partner
colour with the partner sign.  So the sum over `χ` collapses, and
the coordinate at `x` is the colourings' sum read at `untwist x`,
weighted by the leaving legs' signs.

The tensor is zero at a coordinate whose parity pattern is not the
subset's, which is the condition that `χ` be consistent with `S`.
-/

@[expose] public section

namespace RS

namespace EdgeSubset



variable {α : Type}

/-- **RS21's tensor `t′_h`, in coordinates.** -/
noncomputable def tPrime [LinearOrder α] [Fintype α] {W : Fragment α}
    (F : EdgeSubset W) {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) (κ : F.RelTransitionSystem)
    (o : κ.Orientation) (x : GenBoundaryState k ℓ α) : ℂ :=
  if hbnd : genBoundarySubsetMatches W F.flags (untwist F κ o x) then
    ((-1 : ℂ) ^ κ.openCircuitCount) * dualWeight F κ o x *
      ∑ ψ : F.EvenColouring k,
        if genEvenBoundaryMatch F (untwist F κ o x) hbnd ψ then
          ∑ φ : F.EdgeOddColouring ℓ,
            if edgeOddBoundaryMatch F (untwist F κ o x) φ then
              ∏ v : W.Vertex,
                ((F.coreOddSignAt o φ.core v : ℂ) *
                  h.evalOdd (F.evenColoursAt ψ v)
                    (F.coreOddListAt o φ.core v))
            else 0
        else 0
  else 0

/-- **RS21's tensor at given arc directions.**  The chain
orientation fixes the vertex signs; the arc directions fix which
legs carry `f` and which carry `g`. -/
noncomputable def tPrimeD [Fintype α] {W : Fragment α}
    (F : EdgeSubset W) {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) (κ : F.RelTransitionSystem)
    (o : κ.Orientation) (tl : UsedLab F → Bool)
    (x : GenBoundaryState k ℓ α) : ℂ :=
  if hbnd : genBoundarySubsetMatches W F.flags (untwistD F tl x) then
    ((-1 : ℂ) ^ κ.openCircuitCount) * dualWeightD F tl x *
      ∑ ψ : F.EvenColouring k,
        if genEvenBoundaryMatch F (untwistD F tl x) hbnd ψ then
          ∑ φ : F.EdgeOddColouring ℓ,
            if edgeOddBoundaryMatch F (untwistD F tl x) φ then
              ∏ v : W.Vertex,
                ((F.coreOddSignAt o φ.core v : ℂ) *
                  h.evalOdd (F.evenColoursAt ψ v)
                    (F.coreOddListAt o φ.core v))
            else 0
        else 0
  else 0

/-! ### The dual weight is a product of leg weights

The dual basis's weight is a product over the labels of a factor
that depends only on that leg's colour and its arc's direction, so
it is the leg weight the Gram computation uses.  At a label the
subset does not use, the colour is even and the factor is one.
-/

/-- The arc direction as a function of the label, with the unused
labels reading `false`. -/
noncomputable def legDir {W : Fragment α}
    (F : EdgeSubset W) (tl : UsedLab F → Bool)
    (i : α) : Bool :=
  if h : W.boundaryFlag i ∈ F.boundaryFlags then tl ⟨i, h⟩ else false

open Classical in
/-- **The dual weight is the product of the legs' weights.** -/
theorem dualWeightD_eq_prod_legWeight [Fintype α] {W : Fragment α}
    (F : EdgeSubset W) {k ℓ : ℕ}
    (tl : UsedLab F → Bool) (x : GenBoundaryState k ℓ α)
    (hx : genBoundarySubsetMatches W F.flags x) :
    dualWeightD F tl x
      = ∏ i : α, legWeight (legDir F tl i) (x i) := by
  unfold dualWeightD legDir
  refine Finset.prod_congr rfl (fun i _ => ?_)
  by_cases hb : W.boundaryFlag i ∈ F.boundaryFlags
  · rw [dite_eq_left hb, dite_eq_left hb]
    by_cases ht : tl ⟨i, hb⟩ = true
    · rw [ite_eq_left ht]
      rcases hxi : x i with a | c
      · change (1 : ℂ) = legWeight (tl ⟨i, hb⟩) (Sum.inl a)
        rfl
      · change dualSign ℓ c = legWeight (tl ⟨i, hb⟩) (Sum.inr c)
        change dualSign ℓ c = if tl ⟨i, hb⟩ then dualSign ℓ c else 1
        rw [ite_eq_left ht]
    · rw [ite_eq_right ht]
      rcases hxi : x i with a | c
      · rfl
      · change (1 : ℂ) = if tl ⟨i, hb⟩ then dualSign ℓ c else 1
        rw [ite_eq_right ht]
  · rw [dite_eq_right hb, dite_eq_right hb]
    have hev : ¬ ∃ c, x i = Sum.inr c := by
      intro hc
      exact hb (boundaryFlag_mem_boundaryFlags ((hx i).mpr hc))
    obtain ⟨a, ha⟩ := exists_left_of_not_right hev
    rw [ha]
    rfl

/-! ### The normalised tensor

RS21 normalises by a fourth root of unity per two used legs and by
the matching's sign:

    t_h(F,H,ω,κ) := (−1)^{|S|/4} · sgn(M(ω,κ)) · t′_h(F,H,ω,κ).

Since `|S|` is only even, `(−1)^{|S|/4}` is a fourth root: `i^{|S|/2}`.
The sign is taken against the reference matching with arcs
`(i₁,i₂),…`, which is `stdMatching` on the used labels.
-/

/-- The labels the subset uses — RS21's `S(H)`. -/
abbrev UsedLabel {W : Fragment α}
    (F : EdgeSubset W) : Type :=
  {i : α // W.boundaryFlag i ∈ F.boundaryFlags}

/-- The used labels are even in number: they are matched in pairs. -/
theorem card_usedLabel_eq [LinearOrder α] [Fintype α] {W : Fragment α}
    (F : EdgeSubset W)
    (κ : F.RelTransitionSystem) (o : κ.Orientation) :
    Fintype.card (UsedLabel F)
      = 2 * (Fintype.card (UsedLabel F) / 2) := by
  obtain ⟨r, hr⟩ := (cutMatching F κ o).even_card
  have hc : Fintype.card
      {i : α // W.boundaryFlag i ∈ F.boundaryFlags}
      = Fintype.card (UsedLabel F) :=
    Fintype.card_congr (Equiv.refl _)
  rw [hc] at hr
  omega

/-- **RS21's normalised tensor `t_h`, in coordinates.** -/
noncomputable def tFull [LinearOrder α] [Fintype α] {W : Fragment α}
    (F : EdgeSubset W) {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) (κ : F.RelTransitionSystem)
    (o : κ.Orientation) (x : GenBoundaryState k ℓ α) : ℂ :=
  Complex.I ^ (Fintype.card (UsedLabel F) / 2) *
    ((DirMatching.sgnRel
        (DirMatching.stdMatching (card_usedLabel_eq F κ o))
        (cutMatching F κ o) : ℤ) : ℂ)
    * F.tPrime h κ o x

/-- The used labels are even in number, for any directed matching on
them. -/
theorem card_usedLab_eq [LinearOrder α] [Fintype α] {W : Fragment α}
    (F : EdgeSubset W)
    (M : DirMatching (UsedLab F)) :
    Fintype.card (UsedLab F)
      = 2 * (Fintype.card (UsedLab F) / 2) := by
  obtain ⟨r, hr⟩ := M.even_card
  omega

/-- **RS21's normalised tensor at given arc directions.**  The
directions enter twice: through the matching's sign and through the
dual basis. -/
noncomputable def tFullD [LinearOrder α] [Fintype α] {W : Fragment α}
    (F : EdgeSubset W) {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) (κ : F.RelTransitionSystem)
    (o : κ.Orientation) (M : DirMatching (UsedLab F))
    (x : GenBoundaryState k ℓ α) : ℂ :=
  Complex.I ^ (Fintype.card (UsedLab F) / 2) *
    ((DirMatching.sgnRel
        (DirMatching.stdMatching (card_usedLab_eq F M)) M : ℤ) : ℂ)
    * F.tPrimeD h κ o M.tail x

/-- **The normalised tensor is the directed one at the chain
orientation's own directions.** -/
theorem tFull_eq_tFullD [LinearOrder α] [Fintype α] {W : Fragment α}
    (F : EdgeSubset W) {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) (κ : F.RelTransitionSystem)
    (o : κ.Orientation) (x : GenBoundaryState k ℓ α) :
    F.tFull h κ o x = F.tFullD h κ o (cutMatching F κ o) x := rfl

open Classical in
/-- **A disagreeing state carries no colouring.**  RS21 colours a
through-edge once, so a state whose two legs there disagree admits
no `φ ∼ χ₁`, and the tensor vanishes at it. -/
theorem tPrimeD_eq_zero_of_not_throughAgree [Fintype α] {W : Fragment α}
    (F : EdgeSubset W)
    {k ℓ : ℕ} (h : MixedFunctional k ℓ)
    (κ : F.RelTransitionSystem) (o : κ.Orientation)
    (tl : UsedLab F → Bool) (x : GenBoundaryState k ℓ α)
    (hbnd : genBoundarySubsetMatches W F.flags (untwistD F tl x))
    (hag : ¬ ThroughAgree F (untwistD F tl x) hbnd) :
    F.tPrimeD h κ o tl x = 0 := by
  unfold tPrimeD
  rw [dite_eq_left hbnd]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero (fun ψ _ => ?_))
  by_cases hev : genEvenBoundaryMatch F (untwistD F tl x) hbnd ψ
  · rw [ite_eq_left hev]
    exact Finset.sum_eq_zero (fun φ _ => ite_eq_right (fun hφ =>
      hag (throughAgree_of_edgeOddBoundaryMatch hbnd hφ)))
  · rw [ite_eq_right hev]

open Classical in
/-- **A disagreeing state carries no colouring**, at the chain
orientation's own directions. -/
theorem tPrime_eq_zero_of_not_throughAgree
    [LinearOrder α] [Fintype α] {W : Fragment α}
    (F : EdgeSubset W)
    {k ℓ : ℕ} (h : MixedFunctional k ℓ)
    (κ : F.RelTransitionSystem) (o : κ.Orientation)
    (x : GenBoundaryState k ℓ α)
    (hbnd : genBoundarySubsetMatches W F.flags (untwist F κ o x))
    (hag : ¬ ThroughAgree F (untwist F κ o x) hbnd) :
    F.tPrime h κ o x = 0 := by
  unfold tPrime
  rw [dite_eq_left hbnd]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero (fun ψ _ => ?_))
  by_cases hev : genEvenBoundaryMatch F (untwist F κ o x) hbnd ψ
  · rw [ite_eq_left hev]
    exact Finset.sum_eq_zero (fun φ _ => ite_eq_right (fun hφ =>
      hag (throughAgree_of_edgeOddBoundaryMatch hbnd hφ)))
  · rw [ite_eq_right hev]

open Classical in
/-- **RS21's `t_h` vanishes at a disagreeing state.** -/
theorem tFull_eq_zero_of_not_throughAgree
    [LinearOrder α] [Fintype α] {W : Fragment α}
    (F : EdgeSubset W)
    {k ℓ : ℕ} (h : MixedFunctional k ℓ)
    (κ : F.RelTransitionSystem) (o : κ.Orientation)
    (x : GenBoundaryState k ℓ α)
    (hbnd : genBoundarySubsetMatches W F.flags (untwist F κ o x))
    (hag : ¬ ThroughAgree F (untwist F κ o x) hbnd) :
    F.tFull h κ o x = 0 := by
  unfold tFull
  rw [tPrime_eq_zero_of_not_throughAgree F h κ o x hbnd hag, mul_zero]

open Classical in
/-- **The normalised tensor vanishes at a disagreeing state.** -/
theorem tFullD_eq_zero_of_not_throughAgree
    [LinearOrder α] [Fintype α] {W : Fragment α}
    (F : EdgeSubset W)
    {k ℓ : ℕ} (h : MixedFunctional k ℓ)
    (κ : F.RelTransitionSystem) (o : κ.Orientation)
    (M : DirMatching (UsedLab F)) (x : GenBoundaryState k ℓ α)
    (hbnd : genBoundarySubsetMatches W F.flags (untwistD F M.tail x))
    (hag : ¬ ThroughAgree F (untwistD F M.tail x) hbnd) :
    F.tFullD h κ o M x = 0 := by
  unfold tFullD
  rw [tPrimeD_eq_zero_of_not_throughAgree F h κ o M.tail x hbnd hag,
    mul_zero]

/-! ### The tensor's support

The tensor vanishes unless the state's odd legs are exactly the
labels the subset uses.  On that support the number of odd legs is
the number of used labels, and the legs whose arc leaves are half of
them.  These are the hypotheses RS21's leg count needs.
-/

open Classical in
/-- **The tensor vanishes off its support.** -/
theorem genBoundarySubsetMatches_of_tPrimeD_ne_zero [Fintype α] {W : Fragment α}
    (F : EdgeSubset W)
    {k ℓ : ℕ} (h : MixedFunctional k ℓ) (κ : F.RelTransitionSystem)
    (o : κ.Orientation) (tl : UsedLab F → Bool)
    (x : GenBoundaryState k ℓ α) (hne : F.tPrimeD h κ o tl x ≠ 0) :
    genBoundarySubsetMatches W F.flags x := by
  by_contra hc
  refine hne ?_
  unfold tPrimeD
  refine dite_eq_right (fun hb => hc ?_)
  exact (genBoundarySubsetMatches_untwistD F tl x).mp hb

open Classical in
/-- The same, for the normalised tensor. -/
theorem genBoundarySubsetMatches_of_tFullD_ne_zero
    [LinearOrder α] [Fintype α] {W : Fragment α}
    (F : EdgeSubset W)
    {k ℓ : ℕ} (h : MixedFunctional k ℓ) (κ : F.RelTransitionSystem)
    (o : κ.Orientation) (M : DirMatching (UsedLab F))
    (x : GenBoundaryState k ℓ α) (hne : F.tFullD h κ o M x ≠ 0) :
    genBoundarySubsetMatches W F.flags x := by
  refine genBoundarySubsetMatches_of_tPrimeD_ne_zero F h κ o M.tail x
    (fun hz => hne ?_)
  unfold tFullD
  rw [hz, mul_zero]

open Classical in
/-- **On the support the odd legs are the used labels.** -/
theorem oddCount_eq_card_usedLab {t : ℕ} {W : Fragment (Fin t)}
    (F : EdgeSubset W) {k ℓ : ℕ} (x : GenBoundaryState k ℓ (Fin t))
    (hx : genBoundarySubsetMatches W F.flags x) :
    oddCount x = Fintype.card (UsedLab F) := by
  have hiff : ∀ i : Fin t,
      (∃ c, x i = Sum.inr c) ↔ W.boundaryFlag i ∈ F.boundaryFlags := by
    intro i
    constructor
    · intro hc
      exact boundaryFlag_mem_boundaryFlags ((hx i).mpr hc)
    · intro hb
      exact (hx i).mp (mem_flags_of_boundaryFlags F hb)
  rw [oddCount, Fintype.card_subtype]
  exact congrArg Finset.card
    (Finset.filter_congr (fun i _ => hiff i))

/-- The leg direction agrees with the matching's on the used
labels. -/
theorem legDir_eq {W : Fragment α}
    (F : EdgeSubset W) (tl : UsedLab F → Bool)
    (i : α) (h : W.boundaryFlag i ∈ F.boundaryFlags) :
    legDir F tl i = tl ⟨i, h⟩ := dite_eq_left h

open Classical in
/-- **The fragment's change of basis is the abstract one** at its
own leg directions. -/
theorem untwistD_eq_untwistState {t : ℕ} {W : Fragment (Fin t)}
    (F : EdgeSubset W) {k ℓ : ℕ} (tl : UsedLab F → Bool)
    (x : GenBoundaryState k ℓ (Fin t)) :
    untwistD F tl x = untwistState (legDir F tl) x := by
  funext i
  by_cases hb : W.boundaryFlag i ∈ F.boundaryFlags
  · rw [untwistD_apply_mem F tl x hb]
    change (if tl ⟨i, hb⟩ then Sum.map id (oddPartner ℓ) (x i)
        else x i)
      = if legDir F tl i then dualLeg (x i) else x i
    rw [legDir_eq F tl i hb]
    by_cases ht : tl ⟨i, hb⟩ = true
    · rw [ite_eq_left ht, ite_eq_left ht]
      rcases x i with a | c <;> rfl
    · rw [ite_eq_right ht, ite_eq_right ht]
  · rw [untwistD_apply_not_mem F tl x hb]
    change x i = if legDir F tl i then dualLeg (x i) else x i
    rw [show legDir F tl i = false from dite_eq_right hb, ite_eq_right (by simp)]

open Classical in
/-- **Half the used legs**, in the form the leg count needs: the
legs whose arc leaves are half the odd ones. -/
theorem oddCount_eq_two_mul_legDir {t : ℕ} {W : Fragment (Fin t)}
    (F : EdgeSubset W) {k ℓ : ℕ} (x : GenBoundaryState k ℓ (Fin t))
    (hx : genBoundarySubsetMatches W F.flags x)
    (M : DirMatching (UsedLab F)) :
    oddCount x = 2 * (Finset.univ.filter (fun i =>
      (∃ c, x i = Sum.inr c)
        ∧ legDir F M.tail i = true)).card := by
  have hiff : ∀ i : Fin t,
      (∃ c, x i = Sum.inr c) ↔ W.boundaryFlag i ∈ F.boundaryFlags := by
    intro i
    constructor
    · intro hc
      exact boundaryFlag_mem_boundaryFlags ((hx i).mpr hc)
    · intro hb
      exact (hx i).mp (mem_flags_of_boundaryFlags F hb)
  have he : {i : Fin t //
      (∃ c, x i = Sum.inr c) ∧ legDir F M.tail i = true} ≃ M.Tail :=
    { toFun := fun y =>
        ⟨⟨y.val, (hiff y.val).mp y.prop.1⟩, by
          rw [← legDir_eq F M.tail y.val ((hiff y.val).mp y.prop.1)]
          exact y.prop.2⟩
      invFun := fun a =>
        ⟨a.val.val, (hiff a.val.val).mpr a.val.prop, by
          rw [legDir_eq F M.tail a.val.val a.val.prop]
          exact a.prop⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h1 : (Finset.univ.filter (fun i =>
      (∃ c, x i = Sum.inr c) ∧ legDir F M.tail i = true)).card
      = Fintype.card M.Tail := by
    rw [← Fintype.card_congr he, Fintype.card_subtype]
  rw [h1, oddCount_eq_card_usedLab F x hx, M.two_mul_card_tail]

/-- **The tensor vanishes off its support**, read on the state
itself rather than on its untwist. -/
theorem tFullD_eq_zero_of_not_matches
    [LinearOrder α] [Fintype α] {W : Fragment α}
    (F : EdgeSubset W) {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) (κ : F.RelTransitionSystem)
    (o : κ.Orientation) (M : DirMatching (UsedLab F))
    (x : GenBoundaryState k ℓ α)
    (hx : ¬ genBoundarySubsetMatches W F.flags x) :
    F.tFullD h κ o M x = 0 := by
  by_contra hne
  exact hx (genBoundarySubsetMatches_of_tFullD_ne_zero F h κ o M x hne)

/-- **The normalised tensor vanishes off its support.** -/
theorem tFull_eq_zero_of_not_matches
    [LinearOrder α] [Fintype α] {W : Fragment α}
    (F : EdgeSubset W) {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) (κ : F.RelTransitionSystem)
    (o : κ.Orientation) (x : GenBoundaryState k ℓ α)
    (hx : ¬ genBoundarySubsetMatches W F.flags x) :
    F.tFull h κ o x = 0 := by
  rw [tFull_eq_tFullD]
  exact tFullD_eq_zero_of_not_matches F h κ o _ x hx

/-! ### The tensor over the core sum

RS21's colouring sum runs over every edge of the subset.  By the
bridge it equals the sum over the core edges, which is the vertex
sum the mixed partition function is built from.  So the tensor is
the vertex sum, weighted by the circuit sign and the dual basis.
-/

open Classical in
/-- **The tensor is the vertex sum, weighted.** -/
theorem tPrime_eq_vertexSum [LinearOrder α] [Fintype α] {W : Fragment α}
    (F : EdgeSubset W) {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) (κ : F.RelTransitionSystem)
    (o : κ.Orientation) (x : GenBoundaryState k ℓ α)
    (hbnd : genBoundarySubsetMatches W F.flags (untwist F κ o x))
    (hag : ThroughAgree F (untwist F κ o x) hbnd) :
    F.tPrime h κ o x
      = ((-1 : ℂ) ^ κ.openCircuitCount) * dualWeight F κ o x
        * F.vertexSum h (untwist F κ o x) hbnd o := by
  unfold tPrime vertexSum
  rw [dite_eq_left hbnd]
  refine congrArg
    (fun z : ℂ => ((-1 : ℂ) ^ κ.openCircuitCount)
      * dualWeight F κ o x * z) ?_
  refine Finset.sum_congr rfl (fun ψ _ => ?_)
  by_cases hψ : genEvenBoundaryMatch F (untwist F κ o x) hbnd ψ
  · rw [ite_eq_left hψ, ite_eq_left hψ]
    exact sum_edgeOddColouring hbnd hag
      (fun φ' => ∏ v : W.Vertex,
        ((F.coreOddSignAt o φ' v : ℂ) *
          h.evalOdd (F.evenColoursAt ψ v)
            (F.coreOddListAt o φ' v)))
  · rw [ite_eq_right hψ, ite_eq_right hψ]

open Classical in
/-- **The tensor at given arc directions is the vertex sum,
weighted.** -/
theorem tPrimeD_eq_vertexSum [Fintype α] {W : Fragment α}
    (F : EdgeSubset W) {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) (κ : F.RelTransitionSystem)
    (o : κ.Orientation) (tl : UsedLab F → Bool)
    (x : GenBoundaryState k ℓ α)
    (hbnd : genBoundarySubsetMatches W F.flags (untwistD F tl x))
    (hag : ThroughAgree F (untwistD F tl x) hbnd) :
    F.tPrimeD h κ o tl x
      = ((-1 : ℂ) ^ κ.openCircuitCount) * dualWeightD F tl x
        * F.vertexSum h (untwistD F tl x) hbnd o := by
  unfold tPrimeD vertexSum
  rw [dite_eq_left hbnd]
  refine congrArg
    (fun z : ℂ => ((-1 : ℂ) ^ κ.openCircuitCount)
      * dualWeightD F tl x * z) ?_
  refine Finset.sum_congr rfl (fun ψ _ => ?_)
  by_cases hψ : genEvenBoundaryMatch F (untwistD F tl x) hbnd ψ
  · rw [ite_eq_left hψ, ite_eq_left hψ]
    exact sum_edgeOddColouring hbnd hag
      (fun φ' => ∏ v : W.Vertex,
        ((F.coreOddSignAt o φ' v : ℂ) *
          h.evalOdd (F.evenColoursAt ψ v)
            (F.coreOddListAt o φ' v)))
  · rw [ite_eq_right hψ, ite_eq_right hψ]

open Classical in
/-- **The tensor in the Gram computation's terms**: a fourth root
and the matching's sign, the circuit sign, the legs' weights, and
the vertex sum at the untwisted state.  Every factor but the last
is what RS21's sign bookkeeping handles; the last is what the
colouring sums multiply. -/
theorem tFullD_eq {t : ℕ} {W : Fragment (Fin t)} (F : EdgeSubset W)
    {k ℓ : ℕ} (h : MixedFunctional k ℓ) (κ : F.RelTransitionSystem)
    (o : κ.Orientation) (M : DirMatching (UsedLab F))
    (x : GenBoundaryState k ℓ (Fin t))
    (hx : genBoundarySubsetMatches W F.flags x)
    (hag : ThroughAgree F (untwistD F M.tail x)
      ((genBoundarySubsetMatches_untwistD F M.tail x).mpr hx)) :
    F.tFullD h κ o M x
      = (Complex.I ^ (Fintype.card (UsedLab F) / 2)
            * ((DirMatching.sgnRel
                (DirMatching.stdMatching (card_usedLab_eq F M)) M
                : ℤ) : ℂ)
            * ((-1 : ℂ) ^ κ.openCircuitCount))
          * ((∏ i : Fin t, legWeight (legDir F M.tail i) (x i))
            * F.vertexSum h (untwistD F M.tail x)
                ((genBoundarySubsetMatches_untwistD F M.tail x).mpr hx)
                o) := by
  unfold tFullD
  rw [tPrimeD_eq_vertexSum F h κ o M.tail x
      ((genBoundarySubsetMatches_untwistD F M.tail x).mpr hx) hag,
    dualWeightD_eq_prod_legWeight F M.tail x hx]
  ring

/-! ### The two fragments' vertex sums, paired

RS21's right-hand side is the composed graph's summand, whose
colouring sum runs over `V′(G) = V′(F₁) ⊔ V′(F₂)`.  The object the
Gram pairing produces is the two fragments' vertex sums multiplied
at a shared interface state; naming it separates the sign
bookkeeping from the colouring correspondence.
-/

open Classical in
/-- **The two fragments' vertex sums at a shared agreeing state.**
RS21 colours a through-edge once, so a state whose two legs there
disagree carries no colouring at all and both tensors vanish at it.
The pairing therefore sees only the agreeing states, and it is this
value, not the bare product of vertex sums, that it computes. -/
noncomputable def pairAgreeValue {t : ℕ} {W₁ W₂ : Fragment (Fin t)}
    (F₁ : EdgeSubset W₁) (F₂ : EdgeSubset W₂) {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) {κ₁ : F₁.RelTransitionSystem}
    (o₁ : κ₁.Orientation) {κ₂ : F₂.RelTransitionSystem}
    (o₂ : κ₂.Orientation) (st : GenBoundaryState k ℓ (Fin t)) : ℂ :=
  if h₁ : genBoundarySubsetMatches W₁ F₁.flags st then
    if h₂ : genBoundarySubsetMatches W₂ F₂.flags st then
      if ThroughAgree F₁ st h₁ ∧ ThroughAgree F₂ st h₂ then
        F₁.vertexSum h st h₁ o₁ * F₂.vertexSum h st h₂ o₂
      else 0
    else 0
  else 0

open Classical in
/-- **The agreeing value on its support** is the two colouring
sums. -/
theorem pairAgreeValue_pos {t : ℕ} {W₁ W₂ : Fragment (Fin t)}
    (F₁ : EdgeSubset W₁) (F₂ : EdgeSubset W₂) {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) {κ₁ : F₁.RelTransitionSystem}
    (o₁ : κ₁.Orientation) {κ₂ : F₂.RelTransitionSystem}
    (o₂ : κ₂.Orientation) (st : GenBoundaryState k ℓ (Fin t))
    (h₁ : genBoundarySubsetMatches W₁ F₁.flags st)
    (h₂ : genBoundarySubsetMatches W₂ F₂.flags st)
    (hag₁ : ThroughAgree F₁ st h₁) (hag₂ : ThroughAgree F₂ st h₂) :
    pairAgreeValue F₁ F₂ h o₁ o₂ st
      = F₁.vertexSum h st h₁ o₁ * F₂.vertexSum h st h₂ o₂ := by
  unfold pairAgreeValue
  rw [dite_eq_left h₁, dite_eq_left h₂, ite_eq_left ⟨hag₁, hag₂⟩]

open Classical in
/-- **The agreeing value vanishes off the first tensor's
support.** -/
theorem pairAgreeValue_eq_zero {t : ℕ} {W₁ W₂ : Fragment (Fin t)}
    (F₁ : EdgeSubset W₁) (F₂ : EdgeSubset W₂) {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) {κ₁ : F₁.RelTransitionSystem}
    (o₁ : κ₁.Orientation) {κ₂ : F₂.RelTransitionSystem}
    (o₂ : κ₂.Orientation) (st : GenBoundaryState k ℓ (Fin t))
    (h₁ : ¬ genBoundarySubsetMatches W₁ F₁.flags st) :
    pairAgreeValue F₁ F₂ h o₁ o₂ st = 0 := by
  unfold pairAgreeValue
  rw [dite_eq_right h₁]

open Classical in
/-- **The agreeing value vanishes where the first side
disagrees.** -/
theorem pairAgreeValue_eq_zero_of_not_agree₁ {t : ℕ}
    {W₁ W₂ : Fragment (Fin t)} (F₁ : EdgeSubset W₁)
    (F₂ : EdgeSubset W₂) {k ℓ : ℕ} (h : MixedFunctional k ℓ)
    {κ₁ : F₁.RelTransitionSystem} (o₁ : κ₁.Orientation)
    {κ₂ : F₂.RelTransitionSystem} (o₂ : κ₂.Orientation)
    (st : GenBoundaryState k ℓ (Fin t))
    (h₁ : genBoundarySubsetMatches W₁ F₁.flags st)
    (hag : ¬ ThroughAgree F₁ st h₁) :
    pairAgreeValue F₁ F₂ h o₁ o₂ st = 0 := by
  unfold pairAgreeValue
  rw [dite_eq_left h₁]
  by_cases h₂ : genBoundarySubsetMatches W₂ F₂.flags st
  · rw [dite_eq_left h₂, ite_eq_right (fun hx => hag hx.1)]
  · rw [dite_eq_right h₂]

open Classical in
/-- **The agreeing value vanishes where the second side
disagrees.** -/
theorem pairAgreeValue_eq_zero_of_not_agree₂ {t : ℕ}
    {W₁ W₂ : Fragment (Fin t)} (F₁ : EdgeSubset W₁)
    (F₂ : EdgeSubset W₂) {k ℓ : ℕ} (h : MixedFunctional k ℓ)
    {κ₁ : F₁.RelTransitionSystem} (o₁ : κ₁.Orientation)
    {κ₂ : F₂.RelTransitionSystem} (o₂ : κ₂.Orientation)
    (st : GenBoundaryState k ℓ (Fin t))
    (h₂ : genBoundarySubsetMatches W₂ F₂.flags st)
    (hag : ¬ ThroughAgree F₂ st h₂) :
    pairAgreeValue F₁ F₂ h o₁ o₂ st = 0 := by
  unfold pairAgreeValue
  by_cases h₁ : genBoundarySubsetMatches W₁ F₁.flags st
  · rw [dite_eq_left h₁, dite_eq_left h₂, ite_eq_right (fun hx => hag hx.2)]
  · rw [dite_eq_right h₁]

open Classical in
/-- **The paired value is the two colouring sums**, in RS21's own
form.  The agreement is not a condition imposed on top: it is the
support of the colouring sum itself. -/
theorem pairAgreeValue_eq_edgeSum {t : ℕ} {W₁ W₂ : Fragment (Fin t)}
    (F₁ : EdgeSubset W₁) (F₂ : EdgeSubset W₂) {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) {κ₁ : F₁.RelTransitionSystem}
    (o₁ : κ₁.Orientation) {κ₂ : F₂.RelTransitionSystem}
    (o₂ : κ₂.Orientation) (st : GenBoundaryState k ℓ (Fin t))
    (h₁ : genBoundarySubsetMatches W₁ F₁.flags st)
    (h₂ : genBoundarySubsetMatches W₂ F₂.flags st) :
    pairAgreeValue F₁ F₂ h o₁ o₂ st
      = F₁.edgeSum h st h₁ o₁ * F₂.edgeSum h st h₂ o₂ := by
  by_cases hag₁ : ThroughAgree F₁ st h₁
  · by_cases hag₂ : ThroughAgree F₂ st h₂
    · rw [pairAgreeValue_pos F₁ F₂ h o₁ o₂ st h₁ h₂ hag₁ hag₂,
        edgeSum_eq_vertexSum F₁ h st h₁ o₁ hag₁,
        edgeSum_eq_vertexSum F₂ h st h₂ o₂ hag₂]
    · rw [pairAgreeValue_eq_zero_of_not_agree₂ F₁ F₂ h o₁ o₂ st h₂
        hag₂, edgeSum_eq_zero_of_not_throughAgree F₂ h st h₂ o₂
        hag₂, mul_zero]
  · rw [pairAgreeValue_eq_zero_of_not_agree₁ F₁ F₂ h o₁ o₂ st h₁
      hag₁, edgeSum_eq_zero_of_not_throughAgree F₁ h st h₁ o₁ hag₁,
      zero_mul]

open Classical in
/-- **The Gram summand, per coordinate.**  At a coordinate the first
tensor supports, the product of the two tensors against the form is
the sign bookkeeping, the twists and leg weights the cancellation
consumes, and the two vertex sums at the shared state. -/
theorem superForm_mul_tFullD_mul_tFullD {t : ℕ}
    {W₁ W₂ : Fragment (Fin t)} (F₁ : EdgeSubset W₁)
    (F₂ : EdgeSubset W₂) {k ℓ : ℕ} (h : MixedFunctional k ℓ)
    {κ₁ : F₁.RelTransitionSystem} (o₁ : κ₁.Orientation)
    (M₁ : DirMatching (UsedLab F₁))
    {κ₂ : F₂.RelTransitionSystem} (o₂ : κ₂.Orientation)
    (M₂ : DirMatching (UsedLab F₂))
    (x : GenBoundaryState k ℓ (Fin t))
    (hx : genBoundarySubsetMatches W₁ F₁.flags x)
    (hag₁ : ThroughAgree F₁ (untwistD F₁ M₁.tail x)
      ((genBoundarySubsetMatches_untwistD F₁ M₁.tail x).mpr hx))
    (hx₂ : genBoundarySubsetMatches W₂ F₂.flags (dualState x))
    (hag₂ : ThroughAgree F₂ (untwistD F₂ M₂.tail (dualState x))
      ((genBoundarySubsetMatches_untwistD F₂ M₂.tail
        (dualState x)).mpr hx₂)) :
    (∏ i : Fin t, legSelf (x i)) * F₁.tFullD h κ₁ o₁ M₁ x
        * F₂.tFullD h κ₂ o₂ M₂ (dualState x)
      = (((DirMatching.sgnRel
              (DirMatching.stdMatching (card_usedLab_eq F₁ M₁)) M₁
              : ℤ) : ℂ) * ((-1 : ℂ) ^ κ₁.openCircuitCount)
          * (((DirMatching.sgnRel
              (DirMatching.stdMatching (card_usedLab_eq F₂ M₂)) M₂
              : ℤ) : ℂ) * ((-1 : ℂ) ^ κ₂.openCircuitCount)))
        * ((Complex.I ^ (Fintype.card (UsedLab F₁) / 2)
              * Complex.I ^ (Fintype.card (UsedLab F₂) / 2))
          * ((∏ i : Fin t, legWeight (legDir F₁ M₁.tail i) (x i))
              * (∏ i : Fin t,
                  legWeight (legDir F₂ M₂.tail i) (dualLeg (x i))))
          * (∏ i : Fin t, legSelf (x i)))
        * (F₁.vertexSum h (untwistD F₁ M₁.tail x)
              ((genBoundarySubsetMatches_untwistD F₁ M₁.tail x).mpr hx)
              o₁
            * F₂.vertexSum h (untwistD F₂ M₂.tail (dualState x))
              ((genBoundarySubsetMatches_untwistD F₂ M₂.tail
                (dualState x)).mpr hx₂) o₂) := by
  rw [tFullD_eq F₁ h κ₁ o₁ M₁ x hx hag₁,
    tFullD_eq F₂ h κ₂ o₂ M₂ (dualState x) hx₂ hag₂]
  have hd : ∀ i : Fin t, dualState x i = dualLeg (x i) := fun _ => rfl
  rw [Finset.prod_congr rfl (fun i _ => congrArg
    (legWeight (legDir F₂ M₂.tail i)) (hd i))]
  ring

open Classical in
/-- **RS21's (13), up to its sign bookkeeping.**  The Gram pairing
of the two fragments' tensors is the two colouring sums, multiplied
at a shared interface state and summed, times the two matchings'
signs and circuit signs.  What remains to identify it with the
composed graph's summand is (14) and the colouring correspondence. -/
theorem sum_sum_superForm_tFullD {t : ℕ} {W₁ W₂ : Fragment (Fin t)}
    (F₁ : EdgeSubset W₁) (F₂ : EdgeSubset W₂) {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) {κ₁ : F₁.RelTransitionSystem}
    (o₁ : κ₁.Orientation) (M₁ : DirMatching (UsedLab F₁))
    {κ₂ : F₂.RelTransitionSystem} (o₂ : κ₂.Orientation)
    (M₂ : DirMatching (UsedLab F₂)) (m : ℕ)
    (hcard₁ : Fintype.card (UsedLab F₁) = 2 * m)
    (hcard₂ : Fintype.card (UsedLab F₂) = 2 * m)
    (hused : ∀ i : Fin t, W₁.boundaryFlag i ∈ F₁.boundaryFlags
      ↔ W₂.boundaryFlag i ∈ F₂.boundaryFlags)
    (halt : ∀ i : Fin t, W₁.boundaryFlag i ∈ F₁.boundaryFlags →
      legDir F₂ M₂.tail i = !(legDir F₁ M₁.tail i))
 :
    (∑ x : GenBoundaryState k ℓ (Fin t),
        ∑ y : GenBoundaryState k ℓ (Fin t),
          superForm t x y * F₁.tFullD h κ₁ o₁ M₁ x
            * F₂.tFullD h κ₂ o₂ M₂ y)
      = (((DirMatching.sgnRel
              (DirMatching.stdMatching (card_usedLab_eq F₁ M₁)) M₁
              : ℤ) : ℂ) * ((-1 : ℂ) ^ κ₁.openCircuitCount)
          * (((DirMatching.sgnRel
              (DirMatching.stdMatching (card_usedLab_eq F₂ M₂)) M₂
              : ℤ) : ℂ) * ((-1 : ℂ) ^ κ₂.openCircuitCount)))
        * ∑ st : GenBoundaryState k ℓ (Fin t),
            pairAgreeValue F₁ F₂ h o₁ o₂ st := by
  classical
  rw [sum_sum_superForm (fun x => F₁.tFullD h κ₁ o₁ M₁ x)
    (fun y => F₂.tFullD h κ₂ o₂ M₂ y)]
  -- ═══════ THE DUAL STATE MATCHES THE SECOND SUBSET ═══════
  have hmatch₂ : ∀ x : GenBoundaryState k ℓ (Fin t),
      genBoundarySubsetMatches W₁ F₁.flags x →
      genBoundarySubsetMatches W₂ F₂.flags (dualState x) := by
    intro x hx i
    constructor
    · intro hf
      have h1 : W₁.boundaryFlag i ∈ F₁.boundaryFlags :=
        (hused i).mpr (boundaryFlag_mem_boundaryFlags hf)
      obtain ⟨c, hc⟩ := (hx i).mp (mem_flags_of_boundaryFlags F₁ h1)
      exact ⟨oddPartner ℓ c, by
        change dualLeg (x i) = Sum.inr (oddPartner ℓ c)
        rw [hc]; rfl⟩
    · rintro ⟨c, hc⟩
      have hodd : ∃ d, x i = Sum.inr d :=
        (dualState_isInr x i).mp ⟨c, hc⟩
      exact mem_flags_of_boundaryFlags F₂
        ((hused i).mp
          (boundaryFlag_mem_boundaryFlags ((hx i).mpr hodd)))
  have hterm : ∀ x : GenBoundaryState k ℓ (Fin t),
      (∏ i : Fin t, legSelf (x i)) * F₁.tFullD h κ₁ o₁ M₁ x
          * F₂.tFullD h κ₂ o₂ M₂ (dualState x)
        = (((DirMatching.sgnRel
              (DirMatching.stdMatching (card_usedLab_eq F₁ M₁)) M₁
              : ℤ) : ℂ) * ((-1 : ℂ) ^ κ₁.openCircuitCount)
            * (((DirMatching.sgnRel
              (DirMatching.stdMatching (card_usedLab_eq F₂ M₂)) M₂
              : ℤ) : ℂ) * ((-1 : ℂ) ^ κ₂.openCircuitCount)))
          * (((stateTwist x * stateTwist (dualState x))
              * (((∏ i : Fin t,
                    legWeight (legDir F₁ M₁.tail i) (x i))
                  * (∏ i : Fin t,
                    legWeight (legDir F₂ M₂.tail i) (dualLeg (x i))))
                * superForm t x (dualState x)))
            * pairAgreeValue F₁ F₂ h o₁ o₂
                (untwistState (legDir F₁ M₁.tail) x)) := by
    intro x
    by_cases hx : genBoundarySubsetMatches W₁ F₁.flags x
    · have hx₂ := hmatch₂ x hx
      have hst₁ : untwistD F₁ M₁.tail x
          = untwistState (legDir F₁ M₁.tail) x :=
        untwistD_eq_untwistState F₁ M₁.tail x
      have hst₂ : untwistD F₂ M₂.tail (dualState x)
          = untwistState (legDir F₁ M₁.tail) x := by
        rw [untwistD_eq_untwistState F₂ M₂.tail (dualState x)]
        refine untwistState_dualState' _ _ x (fun i hi => ?_)
        obtain ⟨c, hc⟩ := hi
        exact halt i
          (boundaryFlag_mem_boundaryFlags ((hx i).mpr ⟨c, hc⟩))
      have hm₁ : genBoundarySubsetMatches W₁ F₁.flags
          (untwistState (legDir F₁ M₁.tail) x) := by
        rw [← hst₁]
        exact (genBoundarySubsetMatches_untwistD F₁ M₁.tail x).mpr hx
      have hm₂ : genBoundarySubsetMatches W₂ F₂.flags
          (untwistState (legDir F₁ M₁.tail) x) := by
        rw [← hst₂]
        exact (genBoundarySubsetMatches_untwistD F₂ M₂.tail
          (dualState x)).mpr hx₂
      by_cases hag₁ : ThroughAgree F₁
          (untwistState (legDir F₁ M₁.tail) x) hm₁
      · by_cases hag₂ : ThroughAgree F₂
            (untwistState (legDir F₁ M₁.tail) x) hm₂
        · have htw : Complex.I ^ (Fintype.card (UsedLab F₁) / 2)
                * Complex.I ^ (Fintype.card (UsedLab F₂) / 2)
              = stateTwist x * stateTwist (dualState x) := by
            have h1 : oddCount x = 2 * m := by
              rw [oddCount_eq_card_usedLab F₁ x hx, hcard₁]
            have h2 : oddCount (dualState x) = 2 * m := by
              rw [oddCount_dualState x, h1]
            unfold stateTwist
            rw [h1, h2, hcard₁, hcard₂]
          have hpv : pairAgreeValue F₁ F₂ h o₁ o₂
                (untwistState (legDir F₁ M₁.tail) x)
              = F₁.vertexSum h (untwistD F₁ M₁.tail x)
                  ((genBoundarySubsetMatches_untwistD F₁ M₁.tail
                    x).mpr hx) o₁
                * F₂.vertexSum h (untwistD F₂ M₂.tail (dualState x))
                  ((genBoundarySubsetMatches_untwistD F₂ M₂.tail
                    (dualState x)).mpr hx₂) o₂ := by
            rw [pairAgreeValue_pos F₁ F₂ h o₁ o₂ _ hm₁ hm₂ hag₁ hag₂]
            congr 1
            · congr 1
              exact hst₁.symm
            · congr 1
              exact hst₂.symm
          rw [superForm_mul_tFullD_mul_tFullD F₁ F₂ h o₁ M₁ o₂ M₂ x hx
            ((throughAgree_congr hst₁ _ hm₁).mpr hag₁) hx₂
            ((throughAgree_congr hst₂ _ hm₂).mpr hag₂), hpv, htw,
            superForm_dualState x]
          ring
        · rw [tFullD_eq_zero_of_not_throughAgree F₂ h κ₂ o₂ M₂
              (dualState x)
              ((genBoundarySubsetMatches_untwistD F₂ M₂.tail
                (dualState x)).mpr hx₂)
              (fun hy => hag₂ ((throughAgree_congr hst₂ _ hm₂).mp hy)),
            pairAgreeValue_eq_zero_of_not_agree₂ F₁ F₂ h o₁ o₂ _ hm₂
              hag₂]
          ring
      · rw [tFullD_eq_zero_of_not_throughAgree F₁ h κ₁ o₁ M₁ x
            ((genBoundarySubsetMatches_untwistD F₁ M₁.tail x).mpr hx)
            (fun hy => hag₁ ((throughAgree_congr hst₁ _ hm₁).mp hy)),
          pairAgreeValue_eq_zero_of_not_agree₁ F₁ F₂ h o₁ o₂ _ hm₁
            hag₁]
        ring
    · have hz₁ : F₁.tFullD h κ₁ o₁ M₁ x = 0 := by
        by_contra hne
        exact hx (genBoundarySubsetMatches_of_tFullD_ne_zero F₁ h κ₁
          o₁ M₁ x hne)
      have hzp : pairAgreeValue F₁ F₂ h o₁ o₂
          (untwistState (legDir F₁ M₁.tail) x) = 0 := by
        unfold pairAgreeValue
        refine dite_eq_right (fun hc => hx ?_)
        rw [← untwistD_eq_untwistState F₁ M₁.tail x] at hc
        exact (genBoundarySubsetMatches_untwistD F₁ M₁.tail x).mp hc
      rw [hz₁, hzp]
      ring
  -- ═══════ THE SUM OVER STATES, WITH THE TWISTS ═══════
  -- Every term is the pair value at the state; what is left is the
  -- bracket sum, whose three side conditions follow.
  rw [Finset.sum_congr rfl (fun x _ => hterm x), ← Finset.mul_sum]
  congr 1
  refine sum_legBracket_with_twists' (legDir F₁ M₁.tail)
    (legDir F₂ M₂.tail) _ m ?_ ?_ ?_
  · intro x hne
    have hx : genBoundarySubsetMatches W₁ F₁.flags x := by
      by_contra hc
      refine hne ?_
      unfold pairAgreeValue
      refine dite_eq_right (fun hd => hc ?_)
      rw [← untwistD_eq_untwistState F₁ M₁.tail x] at hd
      exact (genBoundarySubsetMatches_untwistD F₁ M₁.tail x).mp hd
    have := oddCount_eq_two_mul_legDir F₁ x hx M₁
    rw [oddCount_eq_card_usedLab F₁ x hx, hcard₁] at this
    omega
  · intro x hne
    have hx : genBoundarySubsetMatches W₁ F₁.flags x := by
      by_contra hc
      refine hne ?_
      unfold pairAgreeValue
      refine dite_eq_right (fun hd => hc ?_)
      rw [← untwistD_eq_untwistState F₁ M₁.tail x] at hd
      exact (genBoundarySubsetMatches_untwistD F₁ M₁.tail x).mp hd
    rw [oddCount_eq_card_usedLab F₁ x hx, hcard₁]
  · intro x hne i hi
    have hx : genBoundarySubsetMatches W₁ F₁.flags x := by
      by_contra hc
      refine hne ?_
      unfold pairAgreeValue
      refine dite_eq_right (fun hd => hc ?_)
      rw [← untwistD_eq_untwistState F₁ M₁.tail x] at hd
      exact (genBoundarySubsetMatches_untwistD F₁ M₁.tail x).mp hd
    exact halt i (boundaryFlag_mem_boundaryFlags ((hx i).mpr hi))

/-! ### The vertex sum under a chain flip

The colouring sum's own chain-flip ledger, read on the vertex sum.
-/

open Classical in
/-- **The vertex sum under a chain flip.** -/
theorem vertexSum_portFlip {W : Fragment α}
    {F : EdgeSubset W}
    {κ : F.RelTransitionSystem} {S : Finset W.Flag} {p₁ p₂ : W.Flag}
    {i₁ i₂ : α} (hp : PortedFlipSet κ S p₁ p₂ i₁ i₂) {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) (st : GenBoundaryState k ℓ α)
    (hbnd : genBoundarySubsetMatches W F.flags st)
    {c₁ c₂ : Fin (2 * ℓ)} (hc₁ : st i₁ = Sum.inr c₁)
    (hc₂ : st i₂ = Sum.inr c₂) (o : κ.Orientation) :
    F.vertexSum h st hbnd (o.portFlip hp)
      = ((oddPartnerSign ℓ c₁ * oddPartnerSign ℓ c₂ : ℤ) : ℂ) *
        F.vertexSum h (stateOddFlip st i₁ i₂)
          (genBoundarySubsetMatches_stateOddFlip hbnd i₁ i₂) o :=
  psiSum_portFlip hp h st hbnd hc₁ hc₂ o

/-! ### The vertex sum ignores the through legs

The core colouring constraint reaches only the core flags, and a
through edge's legs are not among them.  Flipping the state's odd
colour to its partner at two such legs therefore leaves the vertex
sum alone: the even constraint does not see an odd leg at all, and
the odd constraint does not see a through one.
-/

open Classical in
/-- **Flipping the state at two through legs leaves the vertex sum
unchanged.** -/
theorem vertexSum_stateOddFlip_through {W : Fragment α}
    {F : EdgeSubset W} {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) (st : GenBoundaryState k ℓ α)
    (hbnd : genBoundarySubsetMatches W F.flags st)
    {κ : F.RelTransitionSystem} (o : κ.Orientation) (i₁ i₂ : α)
    (h₁ : W.boundaryFlag i₁ ∈ F.throughFlags)
    (h₂ : W.boundaryFlag i₂ ∈ F.throughFlags) :
    F.vertexSum h (stateOddFlip st i₁ i₂)
        (genBoundarySubsetMatches_stateOddFlip hbnd i₁ i₂) o
      = F.vertexSum h st hbnd o := by
  have hne : ∀ i : α, W.boundaryFlag i ∈ F.coreFlags →
      i ≠ i₁ ∧ i ≠ i₂ := by
    intro i hcore
    have hnt := (Finset.mem_sdiff.mp hcore).2
    exact ⟨fun hx => hnt (by rw [hx]; exact h₁),
      fun hx => hnt (by rw [hx]; exact h₂)⟩
  unfold vertexSum
  refine Finset.sum_congr rfl (fun ψ _ => ?_)
  have heven : genEvenBoundaryMatch F (stateOddFlip st i₁ i₂)
      (genBoundarySubsetMatches_stateOddFlip hbnd i₁ i₂) ψ
      ↔ genEvenBoundaryMatch F st hbnd ψ := by
    constructor
    · intro hm i c hst
      exact hm i c ((stateOddFlip_isInl (st := st) i c).mpr hst)
    · intro hm i c hst
      exact hm i c ((stateOddFlip_isInl (st := st) i c).mp hst)
  by_cases hψ : genEvenBoundaryMatch F st hbnd ψ
  · rw [ite_eq_left (heven.mpr hψ), ite_eq_left hψ]
    refine Finset.sum_congr rfl (fun φ _ => ?_)
    have hcore : F.coreOddBoundaryMatch (stateOddFlip st i₁ i₂) φ
        ↔ F.coreOddBoundaryMatch st φ := by
      constructor
      · intro hm i c hst hc
        obtain ⟨hn₁, hn₂⟩ := hne i hc
        exact hm i c (by rw [stateOddFlip_of_ne hn₁ hn₂]; exact hst) hc
      · intro hm i c hst hc
        obtain ⟨hn₁, hn₂⟩ := hne i hc
        refine hm i c ?_ hc
        rw [← stateOddFlip_of_ne (st := st) hn₁ hn₂]
        exact hst
    by_cases hφ : F.coreOddBoundaryMatch st φ
    · rw [ite_eq_left (hcore.mpr hφ), ite_eq_left hφ]
    · rw [ite_eq_right (fun hx => hφ (hcore.mp hx)), ite_eq_right hφ]
  · rw [ite_eq_right (fun hx => hψ (heven.mp hx)), ite_eq_right hψ]

/-! ### The tensor under a chain flip

RS21: inverting a directed trail negates `t′_h`.  The two ledgers
meet — the dual basis contributes `dualSign` at each chain end, the
colouring sum contributes the flipped state's own sign there — and
each pair is `1` where the trail leaves and `-1` where it enters.
Exactly one end of a chain is its tail, so the product is `-1`.
-/

/-- The dual sign against the state's own sign. -/
theorem dualSign_mul_self {ℓ : ℕ} (c : Fin (2 * ℓ)) :
    dualSign ℓ c * ((oddPartnerSign ℓ c : ℤ) : ℂ) = 1 :=
  oddPartnerSign_cast_sq ℓ c

/-- The dual sign against the partner colour's sign. -/
theorem dualSign_mul_partner {ℓ : ℕ} (c : Fin (2 * ℓ)) :
    dualSign ℓ c * ((oddPartnerSign ℓ (oddPartner ℓ c) : ℤ) : ℂ)
      = -1 := by
  have hsq := oddPartnerSign_cast_sq ℓ c
  unfold dualSign
  rw [oddPartnerSign_oddPartner]
  push_cast at hsq ⊢
  linear_combination -hsq

/-- **The tensor changes sign under a chain flip** — RS21's
`t′_h(F,H,ω,κ) = -t′_h(F,H,ω′,κ′)`.  The dual basis contributes the
chain ends' own signs and the colouring sum contributes the flipped
state's; each pair is `1` at the end the trail leaves and `-1` at the
end it enters, and a trail leaves exactly one of its two ends. -/
theorem tPrime_portFlip [LinearOrder α] [Fintype α] {W : Fragment α}
    (F : EdgeSubset W) {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) {κ : F.RelTransitionSystem}
    (o : κ.Orientation) {S : Finset W.Flag} {p₁ p₂ : W.Flag}
    {i₁ i₂ : α} (hp : PortedFlipSet κ S p₁ p₂ i₁ i₂)
    (hb₁ : W.boundaryFlag i₁ ∈ F.boundaryFlags)
    (hchord : chordInv F κ i₁ = i₂)
    (x : GenBoundaryState k ℓ α) {c₁ c₂ : Fin (2 * ℓ)}
    (hc₁ : x i₁ = Sum.inr c₁) (hc₂ : x i₂ = Sum.inr c₂)
    (hbnd : genBoundarySubsetMatches W F.flags (untwist F κ o x))
    (hbnd' : genBoundarySubsetMatches W F.flags
      (untwist F κ (o.portFlip hp) x))
    (hag : ThroughAgree F (untwist F κ o x) hbnd)
    (hag' : ThroughAgree F (untwist F κ (o.portFlip hp) x) hbnd') :
    F.tPrime h κ (o.portFlip hp) x = - F.tPrime h κ o x := by
  have hb₂ : W.boundaryFlag i₂ ∈ F.boundaryFlags := by
    rw [← hchord]; exact chordInv_mem F κ hb₁
  -- the two ends' directions are opposite
  have hedge : (cutMatching F κ o).edge ⟨i₁, hb₁⟩
      = ⟨i₂, hb₂⟩ := Subtype.ext hchord
  have ht12 : (cutMatching F κ o).tail ⟨i₂, hb₂⟩
      = !(cutMatching F κ o).tail ⟨i₁, hb₁⟩ := by
    rw [← hedge]
    exact (cutMatching F κ o).tail_flip ⟨i₁, hb₁⟩
  -- the flipped state's colours at the two ends
  have ha₁ : stateOddFlip (untwist F κ o x) i₁ i₂ i₁
      = Sum.inr (if (cutMatching F κ o).tail ⟨i₁, hb₁⟩ then c₁
        else oddPartner ℓ c₁) := by
    rw [stateOddFlip_left, untwist_apply_odd F κ o x hb₁ hc₁]
    by_cases ht : (cutMatching F κ o).tail ⟨i₁, hb₁⟩ = true
    · rw [ite_eq_left ht, ite_eq_left ht]
      change Sum.inr (oddPartner ℓ (oddPartner ℓ c₁)) = Sum.inr c₁
      rw [oddPartner_invol]
    · rw [ite_eq_right ht, ite_eq_right ht]
      rfl
  have ha₂ : stateOddFlip (untwist F κ o x) i₁ i₂ i₂
      = Sum.inr (if (cutMatching F κ o).tail ⟨i₂, hb₂⟩ then c₂
        else oddPartner ℓ c₂) := by
    rw [stateOddFlip_right, untwist_apply_odd F κ o x hb₂ hc₂]
    by_cases ht : (cutMatching F κ o).tail ⟨i₂, hb₂⟩ = true
    · rw [ite_eq_left ht, ite_eq_left ht]
      change Sum.inr (oddPartner ℓ (oddPartner ℓ c₂)) = Sum.inr c₂
      rw [oddPartner_invol]
    · rw [ite_eq_right ht, ite_eq_right ht]
      rfl
  -- the colouring sum's ledger
  have hVS : F.vertexSum h (untwist F κ (o.portFlip hp) x) hbnd'
        (o.portFlip hp)
      = ((oddPartnerSign ℓ (if (cutMatching F κ o).tail ⟨i₁, hb₁⟩
              then c₁ else oddPartner ℓ c₁) *
            oddPartnerSign ℓ (if (cutMatching F κ o).tail ⟨i₂, hb₂⟩
              then c₂ else oddPartner ℓ c₂) : ℤ) : ℂ) *
        F.vertexSum h (untwist F κ o x) hbnd o := by
    have hst := untwist_portFlip o hp hb₁ hchord x
    have hkey := vertexSum_portFlip hp h
      (stateOddFlip (untwist F κ o x) i₁ i₂)
      (by rw [← hst]; exact hbnd') ha₁ ha₂ o
    rw [show F.vertexSum h (untwist F κ (o.portFlip hp) x) hbnd'
          (o.portFlip hp)
        = F.vertexSum h (stateOddFlip (untwist F κ o x) i₁ i₂)
          (by rw [← hst]; exact hbnd') (o.portFlip hp) from by
      congr 1]
    rw [hkey]
    congr 2
    rw [stateOddFlip_stateOddFlip]
  -- the dual basis's weight
  have hdw : dualWeight F κ (o.portFlip hp) x
      = dualSign ℓ c₁ * dualSign ℓ c₂ * dualWeight F κ o x := by
    have h1 := dualWeight_portFlip_mul o hp hb₁ hchord x hc₁ hc₂
    have h2 := dualWeight_mul_self F κ o x
    calc dualWeight F κ (o.portFlip hp) x
        = dualWeight F κ (o.portFlip hp) x *
            (dualWeight F κ o x * dualWeight F κ o x) := by
          rw [h2, mul_one]
      _ = (dualWeight F κ (o.portFlip hp) x * dualWeight F κ o x) *
            dualWeight F κ o x := by ring
      _ = dualSign ℓ c₁ * dualSign ℓ c₂ * dualWeight F κ o x := by
          rw [h1]
  rw [tPrime_eq_vertexSum F h κ (o.portFlip hp) x hbnd' hag',
    tPrime_eq_vertexSum F h κ o x hbnd hag, hVS, hdw,
    show κ.openCircuitCount = κ.openCircuitCount from rfl]
  have hsign : dualSign ℓ c₁ * dualSign ℓ c₂ *
      ((oddPartnerSign ℓ (if (cutMatching F κ o).tail ⟨i₁, hb₁⟩
            then c₁ else oddPartner ℓ c₁) *
          oddPartnerSign ℓ (if (cutMatching F κ o).tail ⟨i₂, hb₂⟩
            then c₂ else oddPartner ℓ c₂) : ℤ) : ℂ) = -1 := by
    rw [ht12]
    cases hcase : (cutMatching F κ o).tail ⟨i₁, hb₁⟩
    · rw [ite_eq_right (by simp), Bool.not_false, ite_eq_left rfl]
      have hB := dualSign_mul_partner (ℓ := ℓ) c₁
      have hA := dualSign_mul_self (ℓ := ℓ) c₂
      push_cast
      linear_combination
        (dualSign ℓ c₂ * ((oddPartnerSign ℓ c₂ : ℤ) : ℂ)) * hB - hA
    · rw [ite_eq_left rfl, Bool.not_true, ite_eq_right (by simp)]
      have hA := dualSign_mul_self (ℓ := ℓ) c₁
      have hB := dualSign_mul_partner (ℓ := ℓ) c₂
      push_cast
      linear_combination
        (dualSign ℓ c₂ *
          ((oddPartnerSign ℓ (oddPartner ℓ c₂) : ℤ) : ℂ)) * hA + hB
  linear_combination (((-1 : ℂ) ^ κ.openCircuitCount) *
    dualWeight F κ o x *
    F.vertexSum h (untwist F κ o x) hbnd o) * hsign

/-! ### Inverting an edge joining two labelled ends

RS21's (12) inverts a directed trail.  When the trail is a single
edge with both ends labelled there is no transition to invert, so
the whole effect falls on the dual basis: the two legs exchange `f`
and `g`.  The colouring moves too — the edge's colour becomes its
partner — but that colour occurs at no vertex, so the vertex sum is
unchanged and the two weights differ by exactly one sign.  This is
RS21's count of one arc and no pairings.
-/

open Classical in
/-- **Inverting an edge joining two labelled ends negates the
tensor.** -/
theorem tPrimeD_reverseArc [LinearOrder α] [Fintype α] {W : Fragment α}
    (F : EdgeSubset W) {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) (κ : F.RelTransitionSystem)
    (o : κ.Orientation) (M : DirMatching (UsedLab F))
    (a : UsedLab F) (x : GenBoundaryState k ℓ α)
    (hthr₁ : W.boundaryFlag a.val ∈ F.throughFlags)
    (hthr₂ : W.boundaryFlag (M.edge a).val ∈ F.throughFlags)
    (hta : M.tail a = true) {c : Fin (2 * ℓ)}
    (hca : x a.val = Sum.inr c)
    (hca' : x (M.edge a).val = Sum.inr (oddPartner ℓ c))
    (hbnd : genBoundarySubsetMatches W F.flags (untwistD F M.tail x))
    (hbnd' : genBoundarySubsetMatches W F.flags
      (untwistD F (M.reverseArc a).tail x))
    (hag : ThroughAgree F (untwistD F M.tail x) hbnd)
    (hag' : ThroughAgree F (untwistD F (M.reverseArc a).tail x)
      hbnd') :
    F.tPrimeD h κ o (M.reverseArc a).tail x
      = - F.tPrimeD h κ o M.tail x := by
  -- the two weights differ by a sign
  have hmul := dualWeightD_reverseArc_mul F M a x hta hca hca'
  have hsq := dualWeightD_mul_self F M.tail x
  have hw : dualWeightD F (M.reverseArc a).tail x
      = - dualWeightD F M.tail x := by
    calc dualWeightD F (M.reverseArc a).tail x
        = dualWeightD F (M.reverseArc a).tail x
            * (dualWeightD F M.tail x * dualWeightD F M.tail x) := by
          rw [hsq, mul_one]
      _ = (dualWeightD F (M.reverseArc a).tail x
            * dualWeightD F M.tail x) * dualWeightD F M.tail x := by
          ring
      _ = - dualWeightD F M.tail x := by rw [hmul]; ring
  -- the vertex sums agree
  have hst := untwistD_reverseArc F M a x
  have hV : F.vertexSum h (untwistD F (M.reverseArc a).tail x) hbnd' o
      = F.vertexSum h (untwistD F M.tail x) hbnd o := by
    rw [show F.vertexSum h (untwistD F (M.reverseArc a).tail x) hbnd' o
        = F.vertexSum h
          (stateOddFlip (untwistD F M.tail x) a.val (M.edge a).val)
          (by rw [← hst]; exact hbnd') o from by congr 1]
    exact vertexSum_stateOddFlip_through h (untwistD F M.tail x) hbnd
      o a.val (M.edge a).val hthr₁ hthr₂
  rw [tPrimeD_eq_vertexSum F h κ o _ x hbnd' hag',
    tPrimeD_eq_vertexSum F h κ o _ x hbnd hag, hV, hw]
  ring

open Classical in
/-- **RS21's (12) at the normalised tensor**: inverting an edge
joining two labelled ends leaves `t_h` alone, because the matching's
sign and the tensor both change sign. -/
theorem tFullD_reverseArc [LinearOrder α] [Fintype α] {W : Fragment α}
    (F : EdgeSubset W) {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) (κ : F.RelTransitionSystem)
    (o : κ.Orientation) (M : DirMatching (UsedLab F))
    (a : UsedLab F) (x : GenBoundaryState k ℓ α)
    (hthr₁ : W.boundaryFlag a.val ∈ F.throughFlags)
    (hthr₂ : W.boundaryFlag (M.edge a).val ∈ F.throughFlags)
    (hta : M.tail a = true) {c : Fin (2 * ℓ)}
    (hca : x a.val = Sum.inr c)
    (hca' : x (M.edge a).val = Sum.inr (oddPartner ℓ c))
    (hbnd : genBoundarySubsetMatches W F.flags (untwistD F M.tail x))
    (hbnd' : genBoundarySubsetMatches W F.flags
      (untwistD F (M.reverseArc a).tail x))
    (hag : ThroughAgree F (untwistD F M.tail x) hbnd)
    (hag' : ThroughAgree F (untwistD F (M.reverseArc a).tail x)
      hbnd') :
    F.tFullD h κ o (M.reverseArc a) x = F.tFullD h κ o M x := by
  have hsgn := DirMatching.sgnRel_reverseArc
    (DirMatching.stdMatching (card_usedLab_eq F M)) M a
  have htp := tPrimeD_reverseArc F h κ o M a x hthr₁ hthr₂ hta hca
    hca' hbnd hbnd' hag hag'
  unfold tFullD
  rw [show (card_usedLab_eq F (M.reverseArc a))
      = (card_usedLab_eq F M) from rfl, hsgn, htp]
  push_cast
  ring

/-- **RS21's (12) at the normalised tensor, for a chain**:
inverting a directed trail through the interior leaves `t_h` alone,
because the matching's sign and the tensor both change sign.  The
orientation moves with the trail, which is what distinguishes this
from the case of an edge joining two labelled ends. -/
theorem tFull_portFlip [LinearOrder α] [Fintype α] {W : Fragment α}
    (F : EdgeSubset W) {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) {κ : F.RelTransitionSystem}
    (o : κ.Orientation) {S : Finset W.Flag} {p₁ p₂ : W.Flag}
    {i₁ i₂ : α} (hp : PortedFlipSet κ S p₁ p₂ i₁ i₂)
    (hb₁ : W.boundaryFlag i₁ ∈ F.boundaryFlags)
    (hchord : chordInv F κ i₁ = i₂)
    (x : GenBoundaryState k ℓ α) {c₁ c₂ : Fin (2 * ℓ)}
    (hc₁ : x i₁ = Sum.inr c₁) (hc₂ : x i₂ = Sum.inr c₂)
    (hbnd : genBoundarySubsetMatches W F.flags (untwist F κ o x))
    (hbnd' : genBoundarySubsetMatches W F.flags
      (untwist F κ (o.portFlip hp) x))
    (hag : ThroughAgree F (untwist F κ o x) hbnd)
    (hag' : ThroughAgree F (untwist F κ (o.portFlip hp) x) hbnd') :
    F.tFull h κ (o.portFlip hp) x = F.tFull h κ o x := by
  have hcut := cutMatching_portFlip o hp hb₁ hchord
  have hsgn : (DirMatching.sgnRel
      (DirMatching.stdMatching (card_usedLabel_eq F κ (o.portFlip hp)))
      (cutMatching F κ (o.portFlip hp)))
      = - DirMatching.sgnRel
        (DirMatching.stdMatching (card_usedLabel_eq F κ o))
        (cutMatching F κ o) := by
    rw [show (card_usedLabel_eq F κ (o.portFlip hp))
        = (card_usedLabel_eq F κ o) from rfl, hcut]
    exact DirMatching.sgnRel_reverseArc _ _ _
  have htp := tPrime_portFlip F h o hp hb₁ hchord x hc₁ hc₂ hbnd
    hbnd' hag hag'
  unfold tFull
  rw [hsgn, htp]
  push_cast
  ring

open Classical in
/-- **RS21's (12) for a chain, at every state.**  Off the tensor's
support both sides vanish, so the invariance needs no hypothesis on
the state. -/
theorem tFull_portFlip_all [LinearOrder α] [Fintype α] {W : Fragment α}
    (F : EdgeSubset W) {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) {κ : F.RelTransitionSystem}
    (o : κ.Orientation) {S : Finset W.Flag} {p₁ p₂ : W.Flag}
    {i₁ i₂ : α} (hp : PortedFlipSet κ S p₁ p₂ i₁ i₂)
    (hb₁ : W.boundaryFlag i₁ ∈ F.boundaryFlags)
    (hchord : chordInv F κ i₁ = i₂)
    (hnt₁ : ¬ IsThroughLabel F i₁) (hnt₂ : ¬ IsThroughLabel F i₂)
    (x : GenBoundaryState k ℓ α) :
    F.tFull h κ (o.portFlip hp) x = F.tFull h κ o x := by
  by_cases hx : genBoundarySubsetMatches W F.flags x
  · have hbnd := (genBoundarySubsetMatches_untwistD F
      (cutMatching F κ o).tail x).mpr hx
    have hbnd' := (genBoundarySubsetMatches_untwistD F
      (cutMatching F κ (o.portFlip hp)).tail x).mpr hx
    obtain ⟨c₁, hc₁⟩ := (hx i₁).mp (mem_flags_of_boundaryFlags F hb₁)
    have hb₂ : W.boundaryFlag i₂ ∈ F.boundaryFlags := by
      rw [← hchord]
      exact chordInv_mem F κ hb₁
    obtain ⟨c₂, hc₂⟩ := (hx i₂).mp (mem_flags_of_boundaryFlags F hb₂)
    have hthr : ∀ (f : W.Flag) (hb : f ∈ F.boundaryFlags),
        W.pairing f ∈ F.boundaryFlags →
        untwist F κ o x (F.boundaryLabel hb)
          = untwist F κ (o.portFlip hp) x (F.boundaryLabel hb) := by
      intro f hb hbp
      have hbf : W.boundaryFlag (F.boundaryLabel hb) = f :=
        boundaryFlag_boundaryLabel hb
      have hbi : W.boundaryFlag (F.boundaryLabel hb)
          ∈ F.boundaryFlags := by
        rw [hbf]; exact hb
      have hit : IsThroughLabel F (F.boundaryLabel hb) := by
        unfold IsThroughLabel
        rw [hbf]; exact hbp
      have hne : ¬ (F.boundaryLabel hb = i₁
          ∨ F.boundaryLabel hb = i₂) := by
        rintro (hx' | hx')
        · exact hnt₁ (hx' ▸ hit)
        · exact hnt₂ (hx' ▸ hit)
      simp only [untwist]
      rw [dite_eq_left hbi, dite_eq_left hbi,
        tail_portFlip_of_not_mem o hp hb₁ hchord hbi hne]
    by_cases hag : ThroughAgree F (untwist F κ o x) hbnd
    · exact tFull_portFlip F h o hp hb₁ hchord x hc₁ hc₂ hbnd hbnd'
        hag (throughAgree_of_eq_on_through hbnd hbnd' hthr hag)
    · rw [tFull_eq_zero_of_not_throughAgree F h κ (o.portFlip hp) x
          hbnd' (fun hy => hag (throughAgree_of_eq_on_through hbnd'
            hbnd (fun f hb hbp => (hthr f hb hbp).symm) hy)),
        tFull_eq_zero_of_not_throughAgree F h κ o x hbnd hag]
  · rw [tFull_eq_zero_of_not_matches F h κ _ x hx,
      tFull_eq_zero_of_not_matches F h κ o x hx]

/-! ### The tensor does not see those edges' directions

Since inverting such an edge leaves `t_h` alone, and any two
direction assignments on them differ by a set of such inversions,
the normalised tensor is the same for all of them.  This is RS21's
"we may assume that `ω₁, κ₁, ω₂, κ₂` are chosen so that the union is
Eulerian", for the half of the choice the chain orientation does not
already provide.
-/

open Classical in
/-- **The normalised tensor is independent of the directions given
to the edges joining two labelled ends.** -/
theorem tFullD_congr_through [LinearOrder α] [Fintype α] {W : Fragment α}
    (F : EdgeSubset W) {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) (κ : F.RelTransitionSystem)
    (o : κ.Orientation) (x : GenBoundaryState k ℓ α)
    (hx : genBoundarySubsetMatches W F.flags x) :
    ∀ (n : ℕ) (M M' : DirMatching (UsedLab F)),
      M'.edge = M.edge →
      (∀ N : DirMatching (UsedLab F), N.edge = M.edge →
        ThroughAgree F (untwistD F N.tail x)
          ((genBoundarySubsetMatches_untwistD F N.tail x).mpr hx)) →
      (∀ a : UsedLab F, M'.tail a ≠ M.tail a →
        W.boundaryFlag a.val ∈ F.throughFlags) →
      (∀ a : UsedLab F, W.boundaryFlag a.val ∈ F.throughFlags →
        W.boundaryFlag (M.edge a).val ∈ F.throughFlags) →
      (∀ a : UsedLab F, W.boundaryFlag a.val ∈ F.throughFlags →
        ∃ c : Fin (2 * ℓ), x a.val = Sum.inr c ∧
          x (M.edge a).val = Sum.inr (oddPartner ℓ c)) →
      (DirMatching.flipSet M M').card = 2 * n →
      F.tFullD h κ o M' x = F.tFullD h κ o M x := by
  intro n
  induction n with
  | zero =>
    intro M M' he _ _ _ _ hcard
    have hempty : DirMatching.flipSet M M' = ∅ :=
      Finset.card_eq_zero.mp (by omega)
    have htail : M'.tail = M.tail := by
      funext b
      by_contra hb
      have hmem : b ∈ DirMatching.flipSet M M' :=
        DirMatching.mem_flipSet.mpr hb
      rw [hempty] at hmem
      exact Finset.notMem_empty b hmem
    rw [DirMatching.ext he htail]
  | succ n ih =>
    intro M M' he hag hthr hclo hpart hcard
    have hpos : (DirMatching.flipSet M M').Nonempty := by
      rw [← Finset.card_pos]
      omega
    obtain ⟨a₀, ha₀⟩ := hpos
    -- take the end of the arc that the direction leaves
    obtain ⟨a, ha, hta⟩ :
        ∃ a, a ∈ DirMatching.flipSet M M' ∧ M.tail a = true := by
      by_cases h0 : M.tail a₀ = true
      · exact ⟨a₀, ha₀, h0⟩
      · refine ⟨M.edge a₀, DirMatching.edge_mem_flipSet he ha₀, ?_⟩
        rw [M.tail_flip a₀]
        cases hb : M.tail a₀
        · rfl
        · exact absurd hb h0
    have hthr₁ : W.boundaryFlag a.val ∈ F.throughFlags :=
      hthr a (DirMatching.mem_flipSet.mp ha)
    have hthr₂ : W.boundaryFlag (M.edge a).val ∈ F.throughFlags :=
      hclo a hthr₁
    obtain ⟨c, hc, hc'⟩ := hpart a hthr₁
    have hbnd := (genBoundarySubsetMatches_untwistD F M.tail x).mpr hx
    have hbnd' := (genBoundarySubsetMatches_untwistD F
      (M.reverseArc a).tail x).mpr hx
    have hstep := tFullD_reverseArc F h κ o M a x hthr₁ hthr₂ hta hc
      hc' hbnd hbnd' (hag M rfl)
      (hag (M.reverseArc a) rfl)
    have hea : M.edge a ∈ DirMatching.flipSet M M' :=
      DirMatching.edge_mem_flipSet he ha
    have hsub : ({a, M.edge a} : Finset (UsedLab F))
        ⊆ DirMatching.flipSet M M' := by
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact ha
      · rw [Finset.mem_singleton.mp hy]; exact hea
    have hcard' : (DirMatching.flipSet (M.reverseArc a) M').card
        = 2 * n := by
      rw [DirMatching.flipSet_reverseArc he ha]
      have hh := Finset.card_sdiff_add_card_eq_card hsub
      rw [Finset.card_pair (M.edge_ne a).symm] at hh
      omega
    have hthr' : ∀ b : UsedLab F,
        M'.tail b ≠ (M.reverseArc a).tail b →
        W.boundaryFlag b.val ∈ F.throughFlags := by
      intro b hb
      by_cases hbm : b = a ∨ b = M.edge a
      · rcases hbm with rfl | rfl
        · exact hthr₁
        · exact hthr₂
      · refine hthr b ?_
        rwa [DirMatching.reverseArc_tail, ite_eq_right hbm] at hb
    rw [ih (M.reverseArc a) M' he
      (fun N hN => hag N hN) hthr' hclo
      hpart hcard', hstep]

/-! ### A through edge's two labels carry partner colours

The colouring the tensor sums over gives a through edge one colour,
so in the twisted basis its two labels carry partner colours — which
is what RS21's (12) reads at such an edge.  It is not an extra
hypothesis: it follows from the agreement the colouring forces.
-/

open Classical in
/-- **At a through label the chord is the edge's other end.** -/
theorem boundaryFlag_chordInv_through [LinearOrder α] {W : Fragment α}
    (F : EdgeSubset W)
    (κ : F.RelTransitionSystem) {i : α}
    (hb : W.boundaryFlag i ∈ F.boundaryFlags)
    (hthr : IsThroughLabel F i) :
    W.boundaryFlag (chordInv F κ i)
      = W.pairing (W.boundaryFlag i) := by
  rw [boundaryFlag_chordInv F κ hb]
  exact pathMatch_exit_unique κ hb 0
    (fun t ht => absurd ht (by omega)) hthr

open Classical in
/-- **A through edge's two labels carry partner colours.** -/
theorem partner_of_throughAgree [LinearOrder α] {W : Fragment α}
    (F : EdgeSubset W) {k ℓ : ℕ}
    (κ : F.RelTransitionSystem) (M : DirMatching (UsedLab F))
    (hM : ∀ a : UsedLab F, (M.edge a).val = chordInv F κ a.val)
    (x : GenBoundaryState k ℓ α)
    (hx : genBoundarySubsetMatches W F.flags x)
    (hag : ThroughAgree F (untwistD F M.tail x)
      ((genBoundarySubsetMatches_untwistD F M.tail x).mpr hx))
    (a : UsedLab F) (hthr : W.boundaryFlag a.val ∈ F.throughFlags) :
    ∃ c : Fin (2 * ℓ), x a.val = Sum.inr c ∧
      x (M.edge a).val = Sum.inr (oddPartner ℓ c) := by
  have hbnd := (genBoundarySubsetMatches_untwistD F M.tail x).mpr hx
  have hit : IsThroughLabel F a.val :=
    isThroughLabel_of_mem_throughFlags hthr (W.attach_boundaryFlag _)
  have hbp : W.pairing (W.boundaryFlag a.val) ∈ F.boundaryFlags := hit
  have hpair := hag (W.boundaryFlag a.val) a.prop hbp
  -- the two ends' labels
  have hlab : F.boundaryLabel a.prop = a.val :=
    boundaryLabel_boundaryFlag F a.prop
  have hbe : W.boundaryFlag (M.edge a).val
      = W.pairing (W.boundaryFlag a.val) := by
    rw [hM a]
    exact boundaryFlag_chordInv_through F κ a.prop hit
  have hlab' : F.boundaryLabel hbp = (M.edge a).val := by
    refine W.boundaryFlag_injective ?_
    rw [boundaryFlag_boundaryLabel hbp, hbe]
  -- the untwisted colours agree
  have hs := usedColour_spec F (untwistD F M.tail x) hbnd a.prop
  have hs' := usedColour_spec F (untwistD F M.tail x) hbnd hbp
  rw [hlab] at hs
  rw [hlab'] at hs'
  rw [hpair] at hs'
  -- the two directions are opposite
  have htf : M.tail (M.edge a) = !M.tail a := M.tail_flip a
  obtain ⟨c, hc⟩ := (hx a.val).mp
    (mem_flags_of_boundaryFlags F a.prop)
  refine ⟨c, hc, ?_⟩
  rw [untwistD_apply_mem F M.tail x a.prop, hc] at hs
  rw [untwistD_apply_mem F M.tail x (M.edge a).prop, htf] at hs'
  cases hb : M.tail a with
  | false =>
    rw [hb] at hs hs'
    simp only [Bool.false_eq_true, ite_false, Bool.not_false,
      ite_true] at hs hs'
    rw [← hs] at hs'
    rcases hxe : x (M.edge a).val with b | d
    · rw [hxe] at hs'
      exact absurd hs' (by simp)
    · rw [hxe] at hs'
      have hd : oddPartner ℓ d = c := Sum.inr.inj hs'
      rw [← hd, oddPartner_invol ℓ]
  | true =>
    rw [hb] at hs hs'
    simp only [ite_true, Bool.not_true, Bool.false_eq_true,
      ite_false] at hs hs'
    rw [hs', ← hs]
    rfl

open Classical in
/-- **Agreement is a condition on the state alone.**  At a through
edge it says the two labels' colours are partners, and reading that
does not need the arc directions: reversing the edge replaces both
ends' colours by their partners at once. -/
theorem throughAgree_of_partner [LinearOrder α] {W : Fragment α}
    (F : EdgeSubset W) {k ℓ : ℕ}
    (κ : F.RelTransitionSystem) (M : DirMatching (UsedLab F))
    (hM : ∀ a : UsedLab F, (M.edge a).val = chordInv F κ a.val)
    (x : GenBoundaryState k ℓ α)
    (hx : genBoundarySubsetMatches W F.flags x)
    (hpart : ∀ (i : α), W.boundaryFlag i ∈ F.boundaryFlags →
      IsThroughLabel F i → ∀ c : Fin (2 * ℓ), x i = Sum.inr c →
        x (chordInv F κ i) = Sum.inr (oddPartner ℓ c)) :
    ThroughAgree F (untwistD F M.tail x)
      ((genBoundarySubsetMatches_untwistD F M.tail x).mpr hx) := by
  have hbnd := (genBoundarySubsetMatches_untwistD F M.tail x).mpr hx
  intro f hb hbp
  have hbf : W.boundaryFlag (F.boundaryLabel hb) = f :=
    boundaryFlag_boundaryLabel hb
  have hbi : W.boundaryFlag (F.boundaryLabel hb) ∈ F.boundaryFlags := by
    rw [hbf]; exact hb
  have hit : IsThroughLabel F (F.boundaryLabel hb) := by
    unfold IsThroughLabel
    rw [hbf]; exact hbp
  have hj : W.boundaryFlag (chordInv F κ (F.boundaryLabel hb))
      ∈ F.boundaryFlags := chordInv_mem F κ hbi
  have hbe : W.boundaryFlag (chordInv F κ (F.boundaryLabel hb))
      = W.pairing (W.boundaryFlag (F.boundaryLabel hb)) :=
    boundaryFlag_chordInv_through F κ hbi hit
  have hlab' : F.boundaryLabel hbp
      = chordInv F κ (F.boundaryLabel hb) := by
    refine W.boundaryFlag_injective ?_
    rw [boundaryFlag_boundaryLabel hbp, hbe, hbf]
  obtain ⟨c, hc⟩ := (hx (F.boundaryLabel hb)).mp
    (mem_flags_of_boundaryFlags F hbi)
  have hcj : x (chordInv F κ (F.boundaryLabel hb))
      = Sum.inr (oddPartner ℓ c) :=
    hpart (F.boundaryLabel hb) hbi hit c hc
  have hs := usedColour_spec F (untwistD F M.tail x) hbnd hb
  have hs' := usedColour_spec F (untwistD F M.tail x) hbnd hbp
  rw [hlab'] at hs'
  have hedge' : M.edge ⟨F.boundaryLabel hb, hbi⟩
      = ⟨chordInv F κ (F.boundaryLabel hb), hj⟩ :=
    Subtype.ext (hM ⟨F.boundaryLabel hb, hbi⟩)
  have htf' : M.tail ⟨chordInv F κ (F.boundaryLabel hb), hj⟩
      = !M.tail ⟨F.boundaryLabel hb, hbi⟩ := by
    rw [← hedge']
    exact M.tail_flip _
  rw [untwistD_apply_mem F M.tail x hbi, hc] at hs
  rw [untwistD_apply_mem F M.tail x hj, hcj, htf'] at hs'
  cases hb0 : M.tail ⟨F.boundaryLabel hb, hbi⟩ with
  | false =>
    simp only [hb0, Bool.false_eq_true, ite_false, Bool.not_false,
      ite_true, Sum.map_inr, oddPartner_invol] at hs hs'
    exact (Sum.inr.inj hs').symm.trans (Sum.inr.inj hs)
  | true =>
    simp only [hb0, ite_true, Bool.not_true, Bool.false_eq_true,
      ite_false, Sum.map_inr] at hs hs'
    exact (Sum.inr.inj hs').symm.trans (Sum.inr.inj hs)

open Classical in
/-- **The agreement does not read the arc directions.** -/
theorem throughAgree_congr_matching [LinearOrder α] {W : Fragment α}
    (F : EdgeSubset W) {k ℓ : ℕ}
    (κ : F.RelTransitionSystem) (M M' : DirMatching (UsedLab F))
    (hM : ∀ a : UsedLab F, (M.edge a).val = chordInv F κ a.val)
    (hM' : ∀ a : UsedLab F, (M'.edge a).val = chordInv F κ a.val)
    (x : GenBoundaryState k ℓ α)
    (hx : genBoundarySubsetMatches W F.flags x)
    (hag : ThroughAgree F (untwistD F M.tail x)
      ((genBoundarySubsetMatches_untwistD F M.tail x).mpr hx)) :
    ThroughAgree F (untwistD F M'.tail x)
      ((genBoundarySubsetMatches_untwistD F M'.tail x).mpr hx) := by
  refine throughAgree_of_partner F κ M' hM' x hx
    (fun i hb hit c hcx => ?_)
  obtain ⟨c', hc', hpc⟩ := partner_of_throughAgree F κ M hM x hx hag
    ⟨i, hb⟩ (mem_throughFlags_of_isThroughLabel hb hit)
  rw [hcx] at hc'
  rw [hM ⟨i, hb⟩] at hpc
  rw [hpc, Sum.inr.inj hc']

/-! ### RS21's step 1, the chain half

The directions at the chain labels are the chain orientation's own,
and a chain flip reverses exactly one of their arcs at no cost to the
tensor.  So the orientation can be chosen to give those labels any
directions the pairing allows — which is half of "we may assume that
`ω₁, κ₁, ω₂, κ₂` are chosen so that the union is Eulerian".
-/

open Classical in
/-- **The chain labels' directions can be chosen freely.** -/
theorem exists_orient_chainAgree [LinearOrder α] [Fintype α] {W : Fragment α}
    (F : EdgeSubset W) {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) (κ : F.RelTransitionSystem) :
    ∀ (n : ℕ) (o : κ.Orientation) (P : DirMatching (UsedLab F)),
      P.edge = (cutMatching F κ o).edge →
      ((DirMatching.flipSet (cutMatching F κ o) P).filter
        (fun a => ¬ IsThroughLabel F a.val)).card = 2 * n →
      ∃ o' : κ.Orientation,
        (∀ a : UsedLab F, ¬ IsThroughLabel F a.val →
          P.tail a = (cutMatching F κ o').tail a)
        ∧ (∀ x : GenBoundaryState k ℓ α,
            F.tFull h κ o' x = F.tFull h κ o x) := by
  intro n
  induction n with
  | zero =>
    intro o P _ hcard
    refine ⟨o, ?_, fun _ => rfl⟩
    intro a hnt
    by_contra hne
    have hmem : a ∈ (DirMatching.flipSet (cutMatching F κ o) P).filter
        (fun b => ¬ IsThroughLabel F b.val) :=
      Finset.mem_filter.mpr ⟨DirMatching.mem_flipSet.mpr hne, hnt⟩
    rw [Finset.card_eq_zero.mp (by omega : ((DirMatching.flipSet
      (cutMatching F κ o) P).filter
      (fun b => ¬ IsThroughLabel F b.val)).card = 0)] at hmem
    exact Finset.notMem_empty a hmem
  | succ n ih =>
    intro o P he hcard
    have hpos : ((DirMatching.flipSet (cutMatching F κ o) P).filter
        (fun b => ¬ IsThroughLabel F b.val)).Nonempty := by
      rw [← Finset.card_pos]
      omega
    obtain ⟨a, ha⟩ := hpos
    obtain ⟨haf, hant⟩ := Finset.mem_filter.mp ha
    obtain ⟨S, p₁, p₂, hp, hcut⟩ := exists_chainFlip κ o a.prop hant
    have hnt' : ¬ IsThroughLabel F
        ((cutMatching F κ o).edge a).val := by
      intro hx
      refine hant ?_
      have := isThroughLabel_chordInv F κ (chordInv_mem F κ a.prop) hx
      rwa [chordInv_invol] at this
    have haef : (cutMatching F κ o).edge a
        ∈ DirMatching.flipSet (cutMatching F κ o) P :=
      DirMatching.edge_mem_flipSet he haf
    have hsub : ({a, (cutMatching F κ o).edge a} : Finset (UsedLab F))
        ⊆ (DirMatching.flipSet (cutMatching F κ o) P).filter
          (fun b => ¬ IsThroughLabel F b.val) := by
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact ha
      · rw [Finset.mem_singleton.mp hy]
        exact Finset.mem_filter.mpr ⟨haef, hnt'⟩
    have hcut' : cutMatching F κ (o.portFlip hp)
        = (cutMatching F κ o).reverseArc a := hcut
    have he' : P.edge = (cutMatching F κ (o.portFlip hp)).edge := by
      rw [hcut']
      exact he
    have hcard' : ((DirMatching.flipSet
          (cutMatching F κ (o.portFlip hp)) P).filter
        (fun b => ¬ IsThroughLabel F b.val)).card = 2 * n := by
      have hfs : (DirMatching.flipSet
            (cutMatching F κ (o.portFlip hp)) P).filter
            (fun b => ¬ IsThroughLabel F b.val)
          = ((DirMatching.flipSet (cutMatching F κ o) P).filter
              (fun b => ¬ IsThroughLabel F b.val))
            \ {a, (cutMatching F κ o).edge a} := by
        rw [hcut', DirMatching.flipSet_reverseArc he haf]
        ext y
        simp only [Finset.mem_filter, Finset.mem_sdiff]
        tauto
      have hh : (((DirMatching.flipSet (cutMatching F κ o) P).filter
            (fun b => ¬ IsThroughLabel F b.val))
            \ {a, (cutMatching F κ o).edge a}).card + 2
          = ((DirMatching.flipSet (cutMatching F κ o) P).filter
              (fun b => ¬ IsThroughLabel F b.val)).card := by
        have h0 := Finset.card_sdiff_add_card_eq_card hsub
        rwa [Finset.card_pair
          ((cutMatching F κ o).edge_ne a).symm] at h0
      rw [hfs]
      omega
    obtain ⟨o', hagree, hval⟩ := ih (o.portFlip hp) P he' hcard'
    refine ⟨o', hagree, fun x => (hval x).trans ?_⟩
    exact tFull_portFlip_all F h o hp a.prop rfl hant hnt' x

open Classical in
/-- **RS21's step 1.**  The arc directions can be given any values
the pairing allows, at no cost to the tensor: the chain labels' by
choosing the orientation, the through labels' outright. -/
theorem exists_orient_tFullD [LinearOrder α] [Fintype α] {W : Fragment α}
    (F : EdgeSubset W) {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) (κ : F.RelTransitionSystem)
    (o : κ.Orientation) (P : DirMatching (UsedLab F))
    (hP : ∀ a : UsedLab F, (P.edge a).val = chordInv F κ a.val) :
    ∃ o' : κ.Orientation,
      (∀ a : UsedLab F, ¬ IsThroughLabel F a.val →
        P.tail a = (cutMatching F κ o').tail a) ∧
      ∀ x : GenBoundaryState k ℓ α,
        F.tFullD h κ o' P x = F.tFull h κ o x := by
  have hedge : ∀ õ : κ.Orientation, P.edge = (cutMatching F κ õ).edge :=
    fun _ => funext (fun a => Subtype.ext (hP a))
  have hnt' : ∀ (õ : κ.Orientation) (y : UsedLab F),
      ¬ IsThroughLabel F y.val →
      ¬ IsThroughLabel F ((cutMatching F κ õ).edge y).val := by
    intro _ y hy hxx
    refine hy ?_
    have hz := isThroughLabel_chordInv F κ (chordInv_mem F κ y.prop) hxx
    rwa [chordInv_invol] at hz
  have hthrough : ∀ (õ : κ.Orientation) (a : UsedLab F),
      W.boundaryFlag a.val ∈ F.throughFlags →
      W.boundaryFlag ((cutMatching F κ õ).edge a).val
        ∈ F.throughFlags := by
    intro _ a hthr
    exact mem_throughFlags_of_isThroughLabel (chordInv_mem F κ a.prop)
      (isThroughLabel_chordInv F κ a.prop
        (isThroughLabel_of_mem_throughFlags hthr
          (W.attach_boundaryFlag _)))
  obtain ⟨n, hn⟩ : ∃ n, ((DirMatching.flipSet
      (cutMatching F κ o) P).filter
      (fun a => ¬ IsThroughLabel F a.val)).card = 2 * n := by
    obtain ⟨r, hr⟩ := even_card_of_involution
      ((DirMatching.flipSet (cutMatching F κ o) P).filter
        (fun a => ¬ IsThroughLabel F a.val))
      (cutMatching F κ o).edge
      (fun y hy => Finset.mem_filter.mpr
        ⟨DirMatching.edge_mem_flipSet (hedge o)
          (Finset.mem_filter.mp hy).1,
          hnt' o y (Finset.mem_filter.mp hy).2⟩)
      (fun y _ => (cutMatching F κ o).edge_invol y)
      (fun y _ => (cutMatching F κ o).edge_ne y)
    exact ⟨r, by omega⟩
  obtain ⟨o', hagree, hval⟩ := exists_orient_chainAgree F h κ n o P
    (hedge o) hn
  refine ⟨o', hagree, fun x => ?_⟩
  by_cases hx : genBoundarySubsetMatches W F.flags x
  · by_cases hagP : ThroughAgree F (untwistD F P.tail x)
        ((genBoundarySubsetMatches_untwistD F P.tail x).mpr hx)
    · obtain ⟨m, hm⟩ := DirMatching.even_card_flipSet (hedge o')
      have hagN : ∀ N : DirMatching (UsedLab F),
          N.edge = (cutMatching F κ o').edge →
          ThroughAgree F (untwistD F N.tail x)
            ((genBoundarySubsetMatches_untwistD F N.tail x).mpr hx) :=
        fun N hN => throughAgree_congr_matching F κ P N hP
          (fun a => by rw [hN]; rfl) x hx hagP
      refine Eq.trans ?_ (hval x)
      refine tFullD_congr_through F h κ o' x hx m
        (cutMatching F κ o') P (hedge o') hagN
        (fun a hne => mem_throughFlags_of_isThroughLabel a.prop
          (by
            by_contra hnt
            exact hne (hagree a hnt)))
        (hthrough o')
        (fun a hthr => partner_of_throughAgree F κ
          (cutMatching F κ o') (fun _ => rfl) x hx (hagN _ rfl) a
          hthr)
        (by omega)
    · rw [tFullD_eq_zero_of_not_throughAgree F h κ o' P x
          ((genBoundarySubsetMatches_untwistD F P.tail x).mpr hx)
          hagP,
        tFull_eq_zero_of_not_throughAgree F h κ o x
          ((genBoundarySubsetMatches_untwistD F
            (cutMatching F κ o).tail x).mpr hx)
          (fun hy => hagP (throughAgree_congr_matching F κ
            (cutMatching F κ o) P (fun _ => rfl) hP x hx hy))]
  · rw [tFullD_eq_zero_of_not_matches F h κ o' P x hx,
      tFull_eq_zero_of_not_matches F h κ o x hx]

/-! ### The Eulerian position

RS21's step 1 asks for directions making `M(ω₁,κ₁) ∪ M(ω₂,κ₂)`
Eulerian, and Lemma 11's repair supplies them.  Since the tensor does
not read the directions beyond their pairing, they can be imposed on
both sides at once.
-/

/-- The two subsets' used labels, identified by the interface. -/
def usedLabInterfaceEquiv {t : ℕ} {W₁ W₂ : Fragment (Fin t)}
    (F₁ : EdgeSubset W₁) (F₂ : EdgeSubset W₂)
    (hused : ∀ i : Fin t, W₁.boundaryFlag i ∈ F₁.boundaryFlags
      ↔ W₂.boundaryFlag i ∈ F₂.boundaryFlags) :
    UsedLab F₁ ≃ UsedLab F₂ :=
  Equiv.subtypeEquivRight hused

open Classical in
/-- **The two subsets' arc directions can be put in Eulerian
position**, keeping the pairings. -/
theorem exists_eulerianPosition {t : ℕ} {W₁ W₂ : Fragment (Fin t)}
    (F₁ : EdgeSubset W₁) (F₂ : EdgeSubset W₂)
    (κ₁ : F₁.RelTransitionSystem) (o₁ : κ₁.Orientation)
    (κ₂ : F₂.RelTransitionSystem) (o₂ : κ₂.Orientation)
    (hused : ∀ i : Fin t, W₁.boundaryFlag i ∈ F₁.boundaryFlags
      ↔ W₂.boundaryFlag i ∈ F₂.boundaryFlags) :
    ∃ (M₁ : DirMatching (UsedLab F₁)) (M₂ : DirMatching (UsedLab F₂)),
      (∀ a : UsedLab F₁, (M₁.edge a).val = chordInv F₁ κ₁ a.val) ∧
      (∀ b : UsedLab F₂, (M₂.edge b).val = chordInv F₂ κ₂ b.val) ∧
      (∀ a : UsedLab F₁,
        M₂.tail (usedLabInterfaceEquiv F₁ F₂ hused a)
          = !M₁.tail a) := by
  set e := usedLabInterfaceEquiv F₁ F₂ hused with he
  obtain ⟨A, B, hAe, hBe, hAB⟩ :=
    DirMatching.exists_alternating_repair (cutMatching F₁ κ₁ o₁)
      ((cutMatching F₂ κ₂ o₂).map e.symm)
  refine ⟨A, B.map e, fun a => ?_, fun b => ?_, fun a => ?_⟩
  · exact congrArg Subtype.val (congrFun hAe a)
  · change (e (B.edge (e.symm b))).val = _
    rw [congrFun hBe (e.symm b)]
    change (e (e.symm ((cutMatching F₂ κ₂ o₂).edge
      (e (e.symm b))))).val = _
    rw [e.apply_symm_apply, e.apply_symm_apply]
    rfl
  · change B.tail (e.symm (e a)) = _
    rw [e.symm_apply_apply]
    exact hAB a

open Classical in
/-- **RS21's (13), with the directions discharged.**  Step 1 supplies
the Eulerian position and the tensor does not see it, so the pairing
of the two fragments' tensors is the two colouring sums against the
sign bookkeeping, with no hypothesis on the directions. -/
theorem exists_sum_sum_superForm_tFull {t : ℕ}
    {W₁ W₂ : Fragment (Fin t)} (F₁ : EdgeSubset W₁)
    (F₂ : EdgeSubset W₂) {k ℓ : ℕ} (h : MixedFunctional k ℓ)
    (κ₁ : F₁.RelTransitionSystem) (o₁ : κ₁.Orientation)
    (κ₂ : F₂.RelTransitionSystem) (o₂ : κ₂.Orientation) (m : ℕ)
    (hcard₁ : Fintype.card (UsedLab F₁) = 2 * m)
    (hcard₂ : Fintype.card (UsedLab F₂) = 2 * m)
    (hused : ∀ i : Fin t, W₁.boundaryFlag i ∈ F₁.boundaryFlags
      ↔ W₂.boundaryFlag i ∈ F₂.boundaryFlags) :
    ∃ (o₁' : κ₁.Orientation) (o₂' : κ₂.Orientation)
      (M₁ : DirMatching (UsedLab F₁))
      (M₂ : DirMatching (UsedLab F₂)),
      (∀ a : UsedLab F₁, (M₁.edge a).val = chordInv F₁ κ₁ a.val) ∧
      (∀ b : UsedLab F₂, (M₂.edge b).val = chordInv F₂ κ₂ b.val) ∧
      (∀ a : UsedLab F₁, M₂.tail (usedLabInterfaceEquiv F₁ F₂ hused a)
        = !M₁.tail a) ∧
      (∀ a : UsedLab F₁, ¬ IsThroughLabel F₁ a.val →
        M₁.tail a = (cutMatching F₁ κ₁ o₁').tail a) ∧
      (∀ b : UsedLab F₂, ¬ IsThroughLabel F₂ b.val →
        M₂.tail b = (cutMatching F₂ κ₂ o₂').tail b) ∧
      (∀ a : UsedLab F₁, ¬ IsThroughLabel F₁ a.val →
        ¬ IsThroughLabel F₂
          (usedLabInterfaceEquiv F₁ F₂ hused a).val →
        (cutMatching F₂ κ₂ o₂').tail
            (usedLabInterfaceEquiv F₁ F₂ hused a)
          = !(cutMatching F₁ κ₁ o₁').tail a) ∧
      (∑ x : GenBoundaryState k ℓ (Fin t),
          ∑ y : GenBoundaryState k ℓ (Fin t),
            superForm t x y * F₁.tFull h κ₁ o₁ x
              * F₂.tFull h κ₂ o₂ y)
        = (((DirMatching.sgnRel
                (DirMatching.stdMatching (card_usedLab_eq F₁ M₁)) M₁
                : ℤ) : ℂ) * ((-1 : ℂ) ^ κ₁.openCircuitCount)
            * (((DirMatching.sgnRel
                (DirMatching.stdMatching (card_usedLab_eq F₂ M₂)) M₂
                : ℤ) : ℂ) * ((-1 : ℂ) ^ κ₂.openCircuitCount)))
          * ∑ st : GenBoundaryState k ℓ (Fin t),
              pairAgreeValue F₁ F₂ h o₁' o₂' st := by
  obtain ⟨M₁, M₂, hM₁, hM₂, halt⟩ :=
    exists_eulerianPosition F₁ F₂ κ₁ o₁ κ₂ o₂ hused
  obtain ⟨o₁', hag₁, hval₁⟩ := exists_orient_tFullD F₁ h κ₁ o₁ M₁ hM₁
  obtain ⟨o₂', hag₂, hval₂⟩ := exists_orient_tFullD F₂ h κ₂ o₂ M₂ hM₂
  refine ⟨o₁', o₂', M₁, M₂, hM₁, hM₂, halt, hag₁, hag₂,
    fun a h1 h2 => ?_, ?_⟩
  · rw [← hag₂ _ h2, ← hag₁ a h1]
    exact halt a
  rw [show (∑ x : GenBoundaryState k ℓ (Fin t),
      ∑ y : GenBoundaryState k ℓ (Fin t),
        superForm t x y * F₁.tFull h κ₁ o₁ x * F₂.tFull h κ₂ o₂ y)
      = ∑ x : GenBoundaryState k ℓ (Fin t),
          ∑ y : GenBoundaryState k ℓ (Fin t),
            superForm t x y * F₁.tFullD h κ₁ o₁' M₁ x
              * F₂.tFullD h κ₂ o₂' M₂ y from by
    refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl
      (fun y _ => ?_))
    rw [hval₁ x, hval₂ y]]
  refine sum_sum_superForm_tFullD F₁ F₂ h o₁' M₁ o₂' M₂ m hcard₁
    hcard₂ hused (fun i hi => ?_)
  have hi₂ : W₂.boundaryFlag i ∈ F₂.boundaryFlags := (hused i).mp hi
  change (if hb : W₂.boundaryFlag i ∈ F₂.boundaryFlags then
      M₂.tail ⟨i, hb⟩ else false)
    = !(if hb : W₁.boundaryFlag i ∈ F₁.boundaryFlags then
      M₁.tail ⟨i, hb⟩ else false)
  rw [dite_eq_left hi₂, dite_eq_left hi]
  exact halt ⟨i, hi⟩

/-! ### The fragment's tensor

Summing the normalised tensors over the Eulerian subsets gives the
fragment's own tensor, at the transition data each subset's
canonical data provide.  Any choice of data serves, by the
invariance under reversing a trail.
-/

open Classical in
/-- **The fragment's tensor**: `Σ_H t_h(F,H,ω_H,κ_H)`. -/
noncomputable def _root_.RS.tensorSum [LinearOrder α] [Fintype α]
    (V : Fragment α) {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) (x : GenBoundaryState k ℓ α) : ℂ :=
  ∑ s : Finset V.Flag,
    if hc : ∀ f ∈ s, V.pairing f ∈ s then
      if _hE : (EdgeSubset.mk s hc).Eulerian then
        if hne : Nonempty (EdgeSubset.mk s hc).CanonData then
          (EdgeSubset.mk s hc).tFull h (Classical.choice hne).1
            (Classical.choice hne).2.val x
        else 0
      else 0
    else 0

end EdgeSubset

end RS
