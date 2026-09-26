/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Skein.ThroughEdgeCut
public import LeanPool.RegtsSevenster.RS.Novel.Skein.EdgeSum

/-!
# The colouring correspondence at one cut

RS21 glues two open ends by *removing* the two labelled vertices and
joining the two edges into one, so a colouring of the glued graph is
a colouring of the two halves that agrees at the join — and the
colour at the join is exactly the interface state's colour there.
Summing the halves' colouring sums over that colour is therefore the
glued graph's own colouring sum.

This file proves that, one cut at a time, for RS21's colouring sum
`edgeSum`.  The two ends of the cut are either both outside the
subset, when the join carries an even colour, or both inside it,
when it carries an odd one; the sum over the state's colour at the
cut runs over the corresponding block.
-/

@[expose] public section

namespace RS

namespace EdgeSubset

open Fragment
section OpenCut

variable {L : Type} {V : Fragment L} {i j : L}
  (hij : i ≠ j)
  (hopen : V.pairing (V.boundaryFlag i) ≠ V.boundaryFlag j)
  (t : Finset (SurvivingFlag V i j))
  (hct : ∀ f ∈ t, (V.gluePairOpen i j hij hopen).pairing f ∈ t)
  (hcL : ∀ f ∈ liftSubsetOpen hopen t,
    V.pairing f ∈ liftSubsetOpen hopen t)

/-! ## The cut the subset misses

Neither glued flag is in the subset, so the join carries an even
colour and the subset's own flags are the glued fragment's,
unchanged.
-/

section Miss

variable (hni : partnerSurvI hopen ∉ t)

include hij hopen hni in
/-- The `i`-flag is out of the lift. -/
theorem boundaryFlagI_notMem_lift_of_miss :
    V.boundaryFlag i ∉ liftSubsetOpen hopen t := fun hmem =>
  hni ((boundaryFlagI_mem_liftOpen_iff hij hopen t).mp hmem)

include hij hopen hct hni in
/-- The `j`-flag is out of the lift. -/
theorem boundaryFlagJ_notMem_lift_of_miss :
    V.boundaryFlag j ∉ liftSubsetOpen hopen t := fun hmem =>
  partnerSurvJ_notMem_of hij hopen t hct hni
    ((boundaryFlagJ_mem_liftOpen_iff hij hopen t).mp hmem)

include hij hopen hct hni in
/-- A flag of the lift survives the glue. -/
theorem surviving_of_mem_lift_of_miss {f : V.Flag}
    (hf : f ∈ liftSubsetOpen hopen t) :
    f ≠ V.boundaryFlag i ∧ f ≠ V.boundaryFlag j :=
  ⟨fun hx => boundaryFlagI_notMem_lift_of_miss hij hopen t hni
      (hx ▸ hf),
    fun hx => boundaryFlagJ_notMem_lift_of_miss hij hopen t hct
      hni (hx ▸ hf)⟩

/-- A flag of the lift, as a flag of the glued fragment. -/
noncomputable def survOfLift {f : V.Flag}
    (hf : f ∈ liftSubsetOpen hopen t) : SurvivingFlag V i j :=
  ⟨f, (surviving_of_mem_lift_of_miss hij hopen t hct hni hf).1,
    (surviving_of_mem_lift_of_miss hij hopen t hct hni hf).2⟩

/-- A flag of the lift, read as a glued flag, lies in the glued
subset. -/
theorem survOfLift_mem {f : V.Flag}
    (hf : f ∈ liftSubsetOpen hopen t) :
    survOfLift hij hopen t hct hni hf ∈ t :=
  (surviving_val_mem_liftOpen_iff hopen t _).mp hf

/-- Conversely a glued subset flag's underlying flag lies in the
lift. -/
theorem mem_lift_of_mem {g : SurvivingFlag V i j} (hg : g ∈ t) :
    g.val ∈ liftSubsetOpen hopen t :=
  (surviving_val_mem_liftOpen_iff hopen t g).mpr hg

/-- **Odd colourings agree across a missed cut.**  The cut's own
edge is outside the subset, so the two sides colour the same
edges. -/
noncomputable def oddColourEquivMiss (ℓ : ℕ) :
    (EdgeSubset.mk (liftSubsetOpen hopen t) hcL :
        EdgeSubset V).EdgeOddColouring ℓ
      ≃ (EdgeSubset.mk t hct :
        EdgeSubset (V.gluePairOpen i j hij hopen)).EdgeOddColouring
          ℓ where
  toFun φ :=
    ⟨fun g => φ.val ⟨g.val.val, mem_lift_of_mem hopen t g.prop⟩,
      fun g =>
        Eq.trans
          (congrArg φ.val (Subtype.ext
            (gluePairOpen_pairing_val_of_notMem_interface hij hopen t
              hct hni g.prop)))
          (φ.prop ⟨g.val.val, mem_lift_of_mem hopen t g.prop⟩)⟩
  invFun φ' :=
    ⟨fun f => φ'.val ⟨survOfLift hij hopen t hct hni f.prop,
        survOfLift_mem hij hopen t hct hni f.prop⟩,
      fun f => by
        have hpv := gluePairOpen_pairing_val_of_notMem_interface hij
          hopen t hct hni
          (survOfLift_mem hij hopen t hct hni f.prop)
        refine Eq.trans ?_ (φ'.prop
          ⟨survOfLift hij hopen t hct hni f.prop,
            survOfLift_mem hij hopen t hct hni f.prop⟩)
        exact congrArg φ'.val (Subtype.ext (Subtype.ext hpv.symm))⟩
  left_inv _ := rfl
  right_inv _ := rfl

include hij hopen hct hcL hni in
/-- **The odd boundary constraint matches across a missed cut.** -/
theorem edgeOddBoundaryMatch_miss {k ℓ : ℕ}
    (st' : GenBoundaryState k ℓ (SurvivingLabel L i j)) (a : Fin k)
    (φ : (EdgeSubset.mk (liftSubsetOpen hopen t) hcL :
      EdgeSubset V).EdgeOddColouring ℓ) :
    edgeOddBoundaryMatch
        (EdgeSubset.mk (liftSubsetOpen hopen t) hcL)
        (GenBoundaryState.extendPair i j st' (Sum.inl a)
          (Sum.inl a)) φ
      ↔ edgeOddBoundaryMatch (EdgeSubset.mk t hct :
            EdgeSubset (V.gluePairOpen i j hij hopen)) st'
          (oddColourEquivMiss hij hopen t hct hcL hni ℓ φ) := by
  constructor
  · intro hW b' c hst hmem
    have hml : V.boundaryFlag b'.val ∈ liftSubsetOpen hopen t :=
      mem_lift_of_mem hopen t hmem
    have hstW : GenBoundaryState.extendPair i j st' (Sum.inl a)
        (Sum.inl a) b'.val = Sum.inr c := by
      rw [GenBoundaryState.extendPair_surviving]
      exact hst
    exact Eq.trans (congrArg φ.val (Subtype.ext rfl))
      (hW b'.val c hstW hml)
  · intro hG b c hst hmem
    have hbi : b ≠ i := by
      intro hx
      rw [hx, GenBoundaryState.extendPair_left] at hst
      exact absurd hst (by simp)
    have hbj : b ≠ j := by
      intro hx
      rw [hx, GenBoundaryState.extendPair_right hij] at hst
      exact absurd hst (by simp)
    have hst' : st' ⟨b, hbi, hbj⟩ = Sum.inr c := by
      rw [← GenBoundaryState.extendPair_surviving st' (Sum.inl a)
        (Sum.inl a) ⟨b, hbi, hbj⟩]
      exact hst
    have hmg : glueBoundaryFlag V i j ⟨b, hbi, hbj⟩ ∈ t :=
      (surviving_val_mem_liftOpen_iff hopen t _).mp hmem
    exact Eq.trans (congrArg φ.val (Subtype.ext rfl))
      (hG ⟨b, hbi, hbj⟩ c hst' hmg)

section MissSum

variable (κ' : (EdgeSubset.mk t hct :
    EdgeSubset (V.gluePairOpen i j hij hopen)).RelTransitionSystem)
  (o' : κ'.Orientation)

local notation "Fg" =>
  (EdgeSubset.mk t hct :
    EdgeSubset (V.gluePairOpen i j hij hopen))

local notation "Fl" =>
  (EdgeSubset.mk (liftSubsetOpen hopen t) hcL : EdgeSubset V)

local notation "oW" =>
  unglueOrientationOpen hij hopen t hct hcL κ' o'

include hij hopen hct hcL hni in
open Classical in
/-- **The odd colouring sum transports across a missed cut.** -/
theorem sum_odd_miss
    [LinearOrder L]
    {k ℓ : ℕ} (h : MixedFunctional k ℓ)
    (st' : GenBoundaryState k ℓ (SurvivingLabel L i j)) (a : Fin k)
    (ψ' : (Fg).EvenColouring k) :
    (∑ φ : (Fl).EdgeOddColouring ℓ,
        if edgeOddBoundaryMatch (Fl)
            (GenBoundaryState.extendPair i j st' (Sum.inl a)
              (Sum.inl a)) φ then
          ∏ v : V.Vertex,
            (((Fl).coreOddSignAt (oW) φ.core v : ℂ) *
              h.evalOdd ((Fl).evenColoursAt
                  (evenPushOpen hij hopen t hct hcL hni ψ') v)
                ((Fl).coreOddListAt (oW) φ.core v))
        else 0)
      = ∑ φ' : (Fg).EdgeOddColouring ℓ,
          if edgeOddBoundaryMatch (Fg) st' φ' then
            ∏ v : V.Vertex,
              (((Fg).coreOddSignAt o' φ'.core v : ℂ) *
                h.evalOdd ((Fg).evenColoursAt ψ' v)
                  ((Fg).coreOddListAt o' φ'.core v))
          else 0 := by
  refine Fintype.sum_equiv
    (oddColourEquivMiss hij hopen t hct hcL hni ℓ) _ _ (fun φ => ?_)
  by_cases hm : edgeOddBoundaryMatch (Fl)
      (GenBoundaryState.extendPair i j st' (Sum.inl a) (Sum.inl a))
      φ
  · rw [ite_eq_left hm, ite_eq_left ((edgeOddBoundaryMatch_miss hij hopen t
      hct hcL hni st' a φ).mp hm)]
    refine Finset.prod_congr rfl (fun v _ => ?_)
    exact vertexFactor_transport_T hij hopen t hct hcL κ' o' h
      (evenPushOpen hij hopen t hct hcL hni ψ') ψ'
      (evenPushOpen_agrees hij hopen t hct hcL hni ψ')
      φ.core (oddColourEquivMiss hij hopen t hct hcL hni ℓ φ).core
      (fun g h1 h2 => congrArg φ.val (Subtype.ext rfl)) v
  · rw [ite_eq_right hm, ite_eq_right (fun hx => hm
      ((edgeOddBoundaryMatch_miss hij hopen t hct hcL hni st' a
        φ).mpr hx))]

include hij hopen hct hcL hni in
open Classical in
/-- **One missed cut, on RS21's colouring sums.**  The join carries
an even colour, and that colour is the glued colouring's own at the
far end of the cut — so the sum over it has a single term. -/
theorem edgeSum_openCut_miss
    [LinearOrder L]
    {k ℓ : ℕ} (h : MixedFunctional k ℓ)
    (st' : GenBoundaryState k ℓ (SurvivingLabel L i j))
    (hbnd' : genBoundarySubsetMatches
      (V.gluePairOpen i j hij hopen) t st')
    (hbndW : ∀ a : Fin k, genBoundarySubsetMatches V
      (liftSubsetOpen hopen t)
      (GenBoundaryState.extendPair i j st' (Sum.inl a)
        (Sum.inl a))) :
    (∑ a : Fin k, (Fl).edgeSum h
        (GenBoundaryState.extendPair i j st' (Sum.inl a)
          (Sum.inl a)) (hbndW a) (oW))
      = (Fg).edgeSum h st' hbnd' o' := by
  have hL : ∀ a : Fin k,
      (Fl).edgeSum h (GenBoundaryState.extendPair i j st'
          (Sum.inl a) (Sum.inl a)) (hbndW a) (oW)
        = ∑ ψ' : (Fg).EvenColouring k,
            if (ψ'.val ⟨partnerSurvI hopen, hni⟩ = a ∧
                genEvenBoundaryMatch (Fg) st' hbnd' ψ') then
              (∑ φ' : (Fg).EdgeOddColouring ℓ,
                if edgeOddBoundaryMatch (Fg) st' φ' then
                  ∏ v : V.Vertex,
                    (((Fg).coreOddSignAt o' φ'.core v : ℂ) *
                      h.evalOdd ((Fg).evenColoursAt ψ' v)
                        ((Fg).coreOddListAt o' φ'.core v))
                else 0)
            else 0 := by
    intro a
    unfold edgeSum
    rw [sum_even_open hij hopen t hct hcL hni st' a (hbndW a)
      (fun ψW => ∑ φ : (Fl).EdgeOddColouring ℓ,
        if edgeOddBoundaryMatch (Fl)
            (GenBoundaryState.extendPair i j st' (Sum.inl a)
              (Sum.inl a)) φ then
          ∏ v : V.Vertex,
            (((Fl).coreOddSignAt (oW) φ.core v : ℂ) *
              h.evalOdd ((Fl).evenColoursAt ψW v)
                ((Fl).coreOddListAt (oW) φ.core v))
        else 0)]
    refine Finset.sum_congr rfl (fun ψ' _ => ?_)
    by_cases hg : genEvenBoundaryMatch (Fl)
        (GenBoundaryState.extendPair i j st' (Sum.inl a)
          (Sum.inl a)) (hbndW a)
        (evenPushOpen hij hopen t hct hcL hni ψ')
    · rw [ite_eq_left hg, ite_eq_left ((genEvenBoundaryMatch_open_iff hij
        hopen t hct hcL hni st' a (hbndW a) hbnd' ψ').mp hg)]
      exact sum_odd_miss hij hopen t hct hcL hni κ' o' h st' a ψ'
    · rw [ite_eq_right hg, ite_eq_right (fun hx => hg
        ((genEvenBoundaryMatch_open_iff hij hopen t hct hcL hni st'
          a (hbndW a) hbnd' ψ').mpr hx))]
  rw [Finset.sum_congr rfl (fun a (_ : a ∈ Finset.univ) => hL a),
    Finset.sum_comm]
  unfold edgeSum
  refine Finset.sum_congr rfl (fun ψ' _ => ?_)
  by_cases hg : genEvenBoundaryMatch (Fg) st' hbnd' ψ'
  · rw [ite_eq_left hg, Finset.sum_eq_single
      (ψ'.val ⟨partnerSurvI hopen, hni⟩)
      (fun a _ hne => ite_eq_right (fun hx => hne hx.1.symm))
      (fun hx => absurd (Finset.mem_univ _) hx), ite_eq_left ⟨rfl, hg⟩]
    rfl
  · rw [ite_eq_right hg]
    exact Finset.sum_eq_zero (fun a _ => ite_eq_right (fun hx => hg hx.2))

end MissSum

end Miss

/-! ## The cut the subset carries

Both glued flags are in the subset, so the join carries an odd
colour; the even colourings are the same on both sides and the sum
over the join's colour is absorbed by the odd ones.
-/

section Hit

variable (hpi : partnerSurvI hopen ∈ t)

include hij hopen hpi in
/-- The `i`-flag is in the lift. -/
theorem boundaryFlagI_mem_lift_of_hit :
    V.boundaryFlag i ∈ liftSubsetOpen hopen t :=
  (boundaryFlagI_mem_liftOpen_iff hij hopen t).mpr hpi

include hij hopen hct hpi in
/-- The far end of the `j`-edge is in the subset too. -/
theorem partnerSurvJ_mem_of_hit : partnerSurvJ hopen ∈ t := by
  have hp := hct _ hpi
  rwa [gluePairOpen_pairing_interface_i hij hopen
    (partnerSurvI hopen)
    (by rw [partnerSurvI_val hopen, V.pairing_invol])] at hp

include hij hopen hct hpi in
/-- The `j`-flag is in the lift. -/
theorem boundaryFlagJ_mem_lift_of_hit :
    V.boundaryFlag j ∈ liftSubsetOpen hopen t :=
  (boundaryFlagJ_mem_liftOpen_iff hij hopen t).mpr
    (partnerSurvJ_mem_of_hit hij hopen t hct hpi)

include hij hopen hct hpi in
/-- A flag outside the lift survives the glue. -/
theorem surviving_of_notMem_lift_of_hit {f : V.Flag}
    (hf : f ∉ liftSubsetOpen hopen t) :
    f ≠ V.boundaryFlag i ∧ f ≠ V.boundaryFlag j :=
  ⟨fun hx => hf (hx ▸ boundaryFlagI_mem_lift_of_hit hij hopen t hpi),
    fun hx => hf (hx ▸ boundaryFlagJ_mem_lift_of_hit hij hopen t hct
      hpi)⟩

/-- A flag outside the lift, as a flag of the glued fragment. -/
noncomputable def survOfNotLift {f : V.Flag}
    (hf : f ∉ liftSubsetOpen hopen t) : SurvivingFlag V i j :=
  ⟨f, (surviving_of_notMem_lift_of_hit hij hopen t hct hpi hf).1,
    (surviving_of_notMem_lift_of_hit hij hopen t hct hpi hf).2⟩

/-- A flag outside the lift, read as a glued flag, lies outside the
glued subset. -/
theorem survOfNotLift_notMem {f : V.Flag}
    (hf : f ∉ liftSubsetOpen hopen t) :
    survOfNotLift hij hopen t hct hpi hf ∉ t := fun hm =>
  hf ((surviving_val_mem_liftOpen_iff hopen t _).mpr hm)

/-- Conversely a flag outside the glued subset has its underlying
flag outside the lift. -/
theorem notMem_lift_of_notMem {g : SurvivingFlag V i j}
    (hg : g ∉ t) : g.val ∉ liftSubsetOpen hopen t := fun hm =>
  hg ((surviving_val_mem_liftOpen_iff hopen t g).mp hm)

include hij hopen hct hpi in
/-- Away from the interface the glued pairing is the base's. -/
theorem pairing_val_hit {g : SurvivingFlag V i j} (hg : g ∉ t) :
    ((V.gluePairOpen i j hij hopen).pairing g).val
      = V.pairing g.val := by
  refine gluePairOpen_pairing_val_of_ne hij hopen g ?_ ?_
  · intro hh
    exact hg (eq_partnerSurvI_of_pairing hopen g hh ▸ hpi)
  · intro hh
    exact hg (eq_partnerSurvJ_of_pairing hopen g hh ▸
      partnerSurvJ_mem_of_hit hij hopen t hct hpi)

/-- **Even colourings agree across a carried cut.**  The cut's own
edge is in the subset, so the two sides colour the same
complement. -/
noncomputable def evenColourEquivHit (k : ℕ) :
    (EdgeSubset.mk (liftSubsetOpen hopen t) hcL :
        EdgeSubset V).EvenColouring k
      ≃ (EdgeSubset.mk t hct :
        EdgeSubset (V.gluePairOpen i j hij hopen)).EvenColouring
          k where
  toFun ψ :=
    ⟨fun g => ψ.val ⟨g.val.val,
        notMem_lift_of_notMem hopen t g.prop⟩,
      fun g =>
        Eq.trans
          (congrArg ψ.val (Subtype.ext
            (pairing_val_hit hij hopen t hct hpi g.prop)))
          (ψ.prop ⟨g.val.val,
            notMem_lift_of_notMem hopen t g.prop⟩)⟩
  invFun ψ' :=
    ⟨fun f => ψ'.val ⟨survOfNotLift hij hopen t hct hpi f.prop,
        survOfNotLift_notMem hij hopen t hct hpi f.prop⟩,
      fun f => by
        have hpv := pairing_val_hit hij hopen t hct hpi
          (survOfNotLift_notMem hij hopen t hct hpi f.prop)
        refine Eq.trans ?_ (ψ'.prop
          ⟨survOfNotLift hij hopen t hct hpi f.prop,
            survOfNotLift_notMem hij hopen t hct hpi f.prop⟩)
        exact congrArg ψ'.val (Subtype.ext (Subtype.ext hpv.symm))⟩
  left_inv _ := rfl
  right_inv _ := rfl

include hij hopen hct hpi in
/-- **The glued colouring is constant across the join.** -/
theorem glued_odd_merged {ℓ : ℕ}
    (φ' : (EdgeSubset.mk t hct :
      EdgeSubset (V.gluePairOpen i j hij hopen)).EdgeOddColouring
        ℓ) :
    φ'.val ⟨partnerSurvJ hopen,
        partnerSurvJ_mem_of_hit hij hopen t hct hpi⟩
      = φ'.val ⟨partnerSurvI hopen, hpi⟩ := by
  refine Eq.trans ?_ (φ'.prop ⟨partnerSurvI hopen, hpi⟩)
  refine congrArg φ'.val (Subtype.ext ?_)
  exact (gluePairOpen_pairing_interface_i hij hopen
    (partnerSurvI hopen)
    (by rw [partnerSurvI_val hopen, V.pairing_invol])).symm

/-- The pushed colouring's value at a flag of the lift. -/
noncomputable def oddPushHitFun {ℓ : ℕ}
    (φ' : (EdgeSubset.mk t hct :
      EdgeSubset (V.gluePairOpen i j hij hopen)).EdgeOddColouring ℓ)
    (f : {g : V.Flag // g ∈ liftSubsetOpen hopen t}) :
    Fin (2 * ℓ) :=
  if hfi : f.val = V.boundaryFlag i then
    φ'.val ⟨partnerSurvI hopen, hpi⟩
  else if hfj : f.val = V.boundaryFlag j then
    φ'.val ⟨partnerSurvI hopen, hpi⟩
  else φ'.val ⟨⟨f.val, hfi, hfj⟩,
    (surviving_val_mem_liftOpen_iff hopen t
      ⟨f.val, hfi, hfj⟩).mp f.prop⟩

/-- At the first glued boundary flag the pushed colouring takes the
join's colour. -/
theorem oddPushHitFun_at_i {ℓ : ℕ}
    (φ' : (EdgeSubset.mk t hct :
      EdgeSubset (V.gluePairOpen i j hij hopen)).EdgeOddColouring ℓ)
    (hP : V.boundaryFlag i ∈ liftSubsetOpen hopen t) :
    oddPushHitFun hij hopen t hct hpi φ' ⟨V.boundaryFlag i, hP⟩
      = φ'.val ⟨partnerSurvI hopen, hpi⟩ := dite_eq_left rfl

include hij in
/-- At the second it takes the same colour: the two ends of the
join are one edge after gluing. -/
theorem oddPushHitFun_at_j {ℓ : ℕ}
    (φ' : (EdgeSubset.mk t hct :
      EdgeSubset (V.gluePairOpen i j hij hopen)).EdgeOddColouring ℓ)
    (hP : V.boundaryFlag j ∈ liftSubsetOpen hopen t) :
    oddPushHitFun hij hopen t hct hpi φ' ⟨V.boundaryFlag j, hP⟩
      = φ'.val ⟨partnerSurvI hopen, hpi⟩ := by
  unfold oddPushHitFun
  rw [dite_eq_right (fun hEq => hij (V.boundaryFlag_injective hEq).symm),
    dite_eq_left rfl]

/-- Away from the two glued flags the pushed colouring is the
colouring it was pushed from. -/
theorem oddPushHitFun_agrees {ℓ : ℕ}
    (φ' : (EdgeSubset.mk t hct :
      EdgeSubset (V.gluePairOpen i j hij hopen)).EdgeOddColouring ℓ)
    (g : SurvivingFlag V i j)
    (h1 : g.val ∈ liftSubsetOpen hopen t) (h2 : g ∈ t) :
    oddPushHitFun hij hopen t hct hpi φ' ⟨g.val, h1⟩
      = φ'.val ⟨g, h2⟩ := by
  unfold oddPushHitFun
  rw [dite_eq_right g.prop.1, dite_eq_right g.prop.2]

/-- **Push a glued odd colouring up to the lift**, colouring the two
glued flags with the join's own colour. -/
noncomputable def oddPushHit {ℓ : ℕ}
    (φ' : (EdgeSubset.mk t hct :
      EdgeSubset (V.gluePairOpen i j hij hopen)).EdgeOddColouring ℓ) :
    (EdgeSubset.mk (liftSubsetOpen hopen t) hcL :
      EdgeSubset V).EdgeOddColouring ℓ :=
  ⟨oddPushHitFun hij hopen t hct hpi φ', by
    intro f
    by_cases hfi : f.val = V.boundaryFlag i
    · have hpv : V.pairing f.val = (partnerSurvI hopen).val := by
        rw [hfi]; rfl
      rw [show (⟨V.pairing f.val, _⟩ :
            {g : V.Flag // g ∈ liftSubsetOpen hopen t})
          = ⟨(partnerSurvI hopen).val,
            mem_lift_of_mem hopen t hpi⟩ from Subtype.ext hpv,
        oddPushHitFun_agrees hij hopen t hct hpi φ'
          (partnerSurvI hopen) _ hpi]
      change _ = oddPushHitFun hij hopen t hct hpi φ' ⟨f.val, f.prop⟩
      rw [show (⟨f.val, f.prop⟩ :
            {g : V.Flag // g ∈ liftSubsetOpen hopen t})
          = ⟨V.boundaryFlag i,
            boundaryFlagI_mem_lift_of_hit hij hopen t hpi⟩
        from Subtype.ext hfi,
        oddPushHitFun_at_i hij hopen t hct hpi φ']
    · by_cases hfj : f.val = V.boundaryFlag j
      · have hpv : V.pairing f.val
            = (partnerSurvJ hopen).val := by
          rw [hfj]; rfl
        rw [show (⟨V.pairing f.val, _⟩ :
              {g : V.Flag // g ∈ liftSubsetOpen hopen t})
            = ⟨(partnerSurvJ hopen).val,
              mem_lift_of_mem hopen t
                (partnerSurvJ_mem_of_hit hij hopen t hct hpi)⟩
          from Subtype.ext hpv,
          oddPushHitFun_agrees hij hopen t hct hpi φ'
            (partnerSurvJ hopen) _
            (partnerSurvJ_mem_of_hit hij hopen t hct hpi),
          glued_odd_merged hij hopen t hct hpi φ']
        change _ = oddPushHitFun hij hopen t hct hpi φ' ⟨f.val, f.prop⟩
        rw [show (⟨f.val, f.prop⟩ :
              {g : V.Flag // g ∈ liftSubsetOpen hopen t})
            = ⟨V.boundaryFlag j,
              boundaryFlagJ_mem_lift_of_hit hij hopen t hct hpi⟩
          from Subtype.ext hfj,
          oddPushHitFun_at_j hij hopen t hct hpi φ']
      · have hgt : (⟨f.val, hfi, hfj⟩ : SurvivingFlag V i j) ∈ t :=
          (surviving_val_mem_liftOpen_iff hopen t _).mp f.prop
        have hrhs : oddPushHitFun hij hopen t hct hpi φ' f
            = φ'.val ⟨⟨f.val, hfi, hfj⟩, hgt⟩ :=
          oddPushHitFun_agrees hij hopen t hct hpi φ'
            ⟨f.val, hfi, hfj⟩ f.prop hgt
        rw [hrhs]
        by_cases hpi' : V.pairing f.val = V.boundaryFlag i
        · rw [show (⟨V.pairing f.val, _⟩ :
                {g : V.Flag // g ∈ liftSubsetOpen hopen t})
              = ⟨V.boundaryFlag i,
                boundaryFlagI_mem_lift_of_hit hij hopen t hpi⟩
            from Subtype.ext hpi',
            oddPushHitFun_at_i hij hopen t hct hpi φ']
          exact congrArg φ'.val (Subtype.ext
            (eq_partnerSurvI_of_pairing hopen _ hpi').symm)
        · by_cases hpj' : V.pairing f.val = V.boundaryFlag j
          · rw [show (⟨V.pairing f.val, _⟩ :
                  {g : V.Flag // g ∈ liftSubsetOpen hopen t})
                = ⟨V.boundaryFlag j,
                  boundaryFlagJ_mem_lift_of_hit hij hopen t hct hpi⟩
              from Subtype.ext hpj',
              oddPushHitFun_at_j hij hopen t hct hpi φ',
              ← glued_odd_merged hij hopen t hct hpi φ']
            exact congrArg φ'.val (Subtype.ext
              (eq_partnerSurvJ_of_pairing hopen _ hpj').symm)
          · have hgt' : (⟨V.pairing f.val, hpi', hpj'⟩ :
                SurvivingFlag V i j) ∈ t :=
              (surviving_val_mem_liftOpen_iff hopen t _).mp
                (hcL _ f.prop)
            rw [show (⟨V.pairing f.val, _⟩ :
                  {g : V.Flag // g ∈ liftSubsetOpen hopen t})
                = ⟨(⟨V.pairing f.val, hpi', hpj'⟩ :
                    SurvivingFlag V i j).val,
                  mem_lift_of_mem hopen t hgt'⟩ from rfl,
              oddPushHitFun_agrees hij hopen t hct hpi φ' _ _ hgt']
            refine Eq.trans ?_ (φ'.prop ⟨⟨f.val, hfi, hfj⟩, hgt⟩)
            refine congrArg φ'.val (Subtype.ext (Subtype.ext ?_))
            exact (gluePairOpen_pairing_val_of_ne hij hopen
              ⟨f.val, hfi, hfj⟩ hpi' hpj').symm⟩

include hij hopen hct hcL hpi in
/-- **The odd boundary constraint across a carried cut.**  It pins
the join's colour to the state's, and is the glued constraint
otherwise. -/
theorem edgeOddBoundaryMatch_hit_iff {k ℓ : ℕ}
    (st' : GenBoundaryState k ℓ (SurvivingLabel L i j))
    (d : Fin (2 * ℓ))
    (φ' : (EdgeSubset.mk t hct :
      EdgeSubset (V.gluePairOpen i j hij hopen)).EdgeOddColouring
        ℓ) :
    edgeOddBoundaryMatch
        (EdgeSubset.mk (liftSubsetOpen hopen t) hcL)
        (GenBoundaryState.extendPair i j st' (Sum.inr d)
          (Sum.inr d))
        (oddPushHit hij hopen t hct hcL hpi φ')
      ↔ (φ'.val ⟨partnerSurvI hopen, hpi⟩ = d ∧
          edgeOddBoundaryMatch (EdgeSubset.mk t hct :
            EdgeSubset (V.gluePairOpen i j hij hopen)) st' φ') := by
  constructor
  · intro hW
    refine ⟨?_, ?_⟩
    · exact (oddPushHitFun_at_i hij hopen t hct hpi φ'
        (boundaryFlagI_mem_lift_of_hit hij hopen t hpi)).symm.trans
        (hW i d (GenBoundaryState.extendPair_left st' _ _)
          (boundaryFlagI_mem_lift_of_hit hij hopen t hpi))
    · intro b' c hst hmem
      have hstW : GenBoundaryState.extendPair i j st' (Sum.inr d)
          (Sum.inr d) b'.val = Sum.inr c := by
        rw [GenBoundaryState.extendPair_surviving]
        exact hst
      exact (oddPushHitFun_agrees hij hopen t hct hpi φ'
        (glueBoundaryFlag V i j b') _ hmem).symm.trans
        (hW b'.val c hstW (mem_lift_of_mem hopen t hmem))
  · rintro ⟨hx, hG⟩ b c hst hmem
    by_cases hbi : b = i
    · subst hbi
      rw [GenBoundaryState.extendPair_left] at hst
      exact (oddPushHitFun_at_i hij hopen t hct hpi φ' hmem).trans
        (hx.trans (Sum.inr.inj hst))
    · by_cases hbj : b = j
      · subst hbj
        rw [GenBoundaryState.extendPair_right hij] at hst
        exact (oddPushHitFun_at_j hij hopen t hct hpi φ' hmem).trans
          (hx.trans (Sum.inr.inj hst))
      · have hst' : st' ⟨b, hbi, hbj⟩ = Sum.inr c := by
          rw [← GenBoundaryState.extendPair_surviving st'
            (Sum.inr d) (Sum.inr d) ⟨b, hbi, hbj⟩]
          exact hst
        have hmg : glueBoundaryFlag V i j ⟨b, hbi, hbj⟩ ∈ t :=
          (surviving_val_mem_liftOpen_iff hopen t _).mp hmem
        exact (oddPushHitFun_agrees hij hopen t hct hpi φ'
          (glueBoundaryFlag V i j ⟨b, hbi, hbj⟩) hmem hmg).trans
          (hG ⟨b, hbi, hbj⟩ c hst' hmg)

include hij hopen hct hcL hpi in
/-- The push is injective. -/
theorem oddPushHit_injective {ℓ : ℕ} :
    Function.Injective
      (oddPushHit hij hopen t hct hcL hpi (ℓ := ℓ)) := by
  intro φ₁ φ₂ hEq
  refine Subtype.ext (funext fun x => ?_)
  have hv := congrArg (fun φ :
    (EdgeSubset.mk (liftSubsetOpen hopen t) hcL :
      EdgeSubset V).EdgeOddColouring ℓ =>
    φ.val ⟨x.val.val, mem_lift_of_mem hopen t x.prop⟩) hEq
  simp only [] at hv
  have h1 : (oddPushHit hij hopen t hct hcL hpi φ₁).val
      ⟨x.val.val, mem_lift_of_mem hopen t x.prop⟩
      = φ₁.val ⟨x.val, x.prop⟩ :=
    oddPushHitFun_agrees hij hopen t hct hpi φ₁ x.val _ x.prop
  have h2 : (oddPushHit hij hopen t hct hcL hpi φ₂).val
      ⟨x.val.val, mem_lift_of_mem hopen t x.prop⟩
      = φ₂.val ⟨x.val, x.prop⟩ :=
    oddPushHitFun_agrees hij hopen t hct hpi φ₂ x.val _ x.prop
  rw [h1, h2] at hv
  exact hv

include hij hopen hct hcL hpi in
/-- **Every colouring meeting the join's constraint is a push.** -/
theorem oddPushHit_covers {k ℓ : ℕ}
    (st' : GenBoundaryState k ℓ (SurvivingLabel L i j))
    (d : Fin (2 * ℓ))
    (φW : (EdgeSubset.mk (liftSubsetOpen hopen t) hcL :
      EdgeSubset V).EdgeOddColouring ℓ)
    (hmatch : edgeOddBoundaryMatch
      (EdgeSubset.mk (liftSubsetOpen hopen t) hcL)
      (GenBoundaryState.extendPair i j st' (Sum.inr d)
        (Sum.inr d)) φW) :
    ∃ φ' : (EdgeSubset.mk t hct :
        EdgeSubset (V.gluePairOpen i j hij hopen)).EdgeOddColouring
          ℓ,
      oddPushHit hij hopen t hct hcL hpi φ' = φW := by
  have hbi := boundaryFlagI_mem_lift_of_hit hij hopen t hpi
  have hbj := boundaryFlagJ_mem_lift_of_hit hij hopen t hct hpi
  have hvi : φW.val ⟨V.boundaryFlag i, hbi⟩ = d :=
    hmatch i d (GenBoundaryState.extendPair_left st' _ _) hbi
  have hvj : φW.val ⟨V.boundaryFlag j, hbj⟩ = d :=
    hmatch j d (GenBoundaryState.extendPair_right hij st' _ _) hbj
  have hvI : φW.val ⟨(partnerSurvI hopen).val,
      mem_lift_of_mem hopen t hpi⟩ = d := by
    refine Eq.trans ?_ hvi
    exact Eq.trans (congrArg φW.val (Subtype.ext rfl))
      (φW.prop ⟨V.boundaryFlag i, hbi⟩)
  have hvJ : φW.val ⟨(partnerSurvJ hopen).val,
      mem_lift_of_mem hopen t
        (partnerSurvJ_mem_of_hit hij hopen t hct hpi)⟩ = d := by
    refine Eq.trans ?_ hvj
    exact Eq.trans (congrArg φW.val (Subtype.ext rfl))
      (φW.prop ⟨V.boundaryFlag j, hbj⟩)
  -- ═══════ THE GLUED COLOURING, AND THAT IT IS ONE ═══════
  -- Above: the interface colour is `d` at all four of the cut's
  -- flags.  Below: restricting `φW` to the survivors is a colouring
  -- of the glued subset, and it pushes to `φW`.
  refine ⟨⟨fun g => φW.val ⟨g.val.val,
      mem_lift_of_mem hopen t g.prop⟩, ?_⟩, ?_⟩
  · intro g
    dsimp only []
    by_cases hpi' : V.pairing g.val.val = V.boundaryFlag i
    · have hg : g.val = partnerSurvI hopen :=
        eq_partnerSurvI_of_pairing hopen g.val hpi'
      have hgl : (V.gluePairOpen i j hij hopen).pairing g.val
          = partnerSurvJ hopen :=
        gluePairOpen_pairing_interface_i hij hopen g.val hpi'
      have hx : ((V.gluePairOpen i j hij hopen).pairing g.val).val
          = (partnerSurvJ hopen).val := congrArg Subtype.val hgl
      have hy : g.val.val = (partnerSurvI hopen).val :=
        congrArg Subtype.val hg
      have hmA : ((V.gluePairOpen i j hij hopen).pairing g.val).val
          ∈ liftSubsetOpen hopen t :=
        mem_lift_of_mem hopen t (hct _ g.prop)
      have hmB : (partnerSurvJ hopen).val
          ∈ liftSubsetOpen hopen t :=
        mem_lift_of_mem hopen t
          (partnerSurvJ_mem_of_hit hij hopen t hct hpi)
      have hmC : g.val.val ∈ liftSubsetOpen hopen t :=
        mem_lift_of_mem hopen t g.prop
      have hmD : (partnerSurvI hopen).val
          ∈ liftSubsetOpen hopen t :=
        mem_lift_of_mem hopen t hpi
      have h1 : (⟨_, hmA⟩ :
          {f : V.Flag // f ∈ liftSubsetOpen hopen t})
          = ⟨_, hmB⟩ := Subtype.ext hx
      have h2 : (⟨_, hmC⟩ :
          {f : V.Flag // f ∈ liftSubsetOpen hopen t})
          = ⟨_, hmD⟩ := Subtype.ext hy
      rw [h1, h2, hvJ, hvI]
    · by_cases hpj' : V.pairing g.val.val = V.boundaryFlag j
      · have hg : g.val = partnerSurvJ hopen :=
          eq_partnerSurvJ_of_pairing hopen g.val hpj'
        have hgl : (V.gluePairOpen i j hij hopen).pairing g.val
            = partnerSurvI hopen :=
          gluePairOpen_pairing_interface_j hij hopen g.val hpi' hpj'
        have hx : ((V.gluePairOpen i j hij hopen).pairing g.val).val
            = (partnerSurvI hopen).val := congrArg Subtype.val hgl
        have hy : g.val.val = (partnerSurvJ hopen).val :=
          congrArg Subtype.val hg
        have hmA : ((V.gluePairOpen i j hij hopen).pairing
            g.val).val ∈ liftSubsetOpen hopen t :=
          mem_lift_of_mem hopen t (hct _ g.prop)
        have hmB : (partnerSurvI hopen).val
            ∈ liftSubsetOpen hopen t :=
          mem_lift_of_mem hopen t hpi
        have hmC : g.val.val ∈ liftSubsetOpen hopen t :=
          mem_lift_of_mem hopen t g.prop
        have hmD : (partnerSurvJ hopen).val
            ∈ liftSubsetOpen hopen t :=
          mem_lift_of_mem hopen t
            (partnerSurvJ_mem_of_hit hij hopen t hct hpi)
        have h1 : (⟨_, hmA⟩ :
            {f : V.Flag // f ∈ liftSubsetOpen hopen t})
            = ⟨_, hmB⟩ := Subtype.ext hx
        have h2 : (⟨_, hmC⟩ :
            {f : V.Flag // f ∈ liftSubsetOpen hopen t})
            = ⟨_, hmD⟩ := Subtype.ext hy
        rw [h1, h2, hvI, hvJ]
      · have hx : ((V.gluePairOpen i j hij hopen).pairing g.val).val
            = V.pairing g.val.val :=
          gluePairOpen_pairing_val_of_ne hij hopen g.val hpi' hpj'
        have hmA : ((V.gluePairOpen i j hij hopen).pairing
            g.val).val ∈ liftSubsetOpen hopen t :=
          mem_lift_of_mem hopen t (hct _ g.prop)
        have hmC : g.val.val ∈ liftSubsetOpen hopen t :=
          mem_lift_of_mem hopen t g.prop
        have hmB : V.pairing g.val.val
            ∈ liftSubsetOpen hopen t := hcL _ hmC
        have h1 : (⟨_, hmA⟩ :
            {f : V.Flag // f ∈ liftSubsetOpen hopen t})
            = ⟨_, hmB⟩ := Subtype.ext hx
        rw [h1]
        exact φW.prop ⟨g.val.val, hmC⟩
  · refine Subtype.ext (funext fun f => ?_)
    change oddPushHitFun hij hopen t hct hpi _ f = φW.val f
    by_cases hfi : f.val = V.boundaryFlag i
    · have hfe : f = ⟨V.boundaryFlag i, hbi⟩ := Subtype.ext hfi
      rw [hfe]
      exact (oddPushHitFun_at_i hij hopen t hct hpi _ hbi).trans
        (hvI.trans hvi.symm)
    · by_cases hfj : f.val = V.boundaryFlag j
      · have hfe : f = ⟨V.boundaryFlag j, hbj⟩ := Subtype.ext hfj
        rw [hfe]
        exact (oddPushHitFun_at_j hij hopen t hct hpi _ hbj).trans
          (hvI.trans hvj.symm)
      · have hgt : (⟨f.val, hfi, hfj⟩ : SurvivingFlag V i j) ∈ t :=
          (surviving_val_mem_liftOpen_iff hopen t _).mp f.prop
        exact oddPushHitFun_agrees hij hopen t hct hpi _
          ⟨f.val, hfi, hfj⟩ f.prop hgt

include hij hopen hct hcL hpi in
/-- **The even boundary constraint across a carried cut.** -/
theorem genEvenBoundaryMatch_hit_iff {k ℓ : ℕ}
    (st' : GenBoundaryState k ℓ (SurvivingLabel L i j))
    (d : Fin (2 * ℓ))
    (hbndW : genBoundarySubsetMatches V
      (liftSubsetOpen hopen t)
      (GenBoundaryState.extendPair i j st' (Sum.inr d)
        (Sum.inr d)))
    (hbnd' : genBoundarySubsetMatches
      (V.gluePairOpen i j hij hopen) t st')
    (ψ' : (EdgeSubset.mk t hct :
      EdgeSubset (V.gluePairOpen i j hij hopen)).EvenColouring k) :
    genEvenBoundaryMatch
        (EdgeSubset.mk (liftSubsetOpen hopen t) hcL)
        (GenBoundaryState.extendPair i j st' (Sum.inr d)
          (Sum.inr d)) hbndW
        ((evenColourEquivHit hij hopen t hct hcL hpi k).symm ψ')
      ↔ genEvenBoundaryMatch (EdgeSubset.mk t hct :
          EdgeSubset (V.gluePairOpen i j hij hopen)) st' hbnd'
          ψ' := by
  constructor
  · intro hW b' y hst
    have hstW : GenBoundaryState.extendPair i j st' (Sum.inr d)
        (Sum.inr d) b'.val = Sum.inl y := by
      rw [GenBoundaryState.extendPair_surviving]
      exact hst
    exact (congrArg ψ'.val (Subtype.ext (Subtype.ext rfl))).symm.trans
      (hW b'.val y hstW)
  · intro hG b y hst
    have hbi : b ≠ i := by
      intro hx
      rw [hx, GenBoundaryState.extendPair_left] at hst
      exact absurd hst (by simp)
    have hbj : b ≠ j := by
      intro hx
      rw [hx, GenBoundaryState.extendPair_right hij] at hst
      exact absurd hst (by simp)
    have hst' : st' ⟨b, hbi, hbj⟩ = Sum.inl y := by
      rw [← GenBoundaryState.extendPair_surviving st' (Sum.inr d)
        (Sum.inr d) ⟨b, hbi, hbj⟩]
      exact hst
    exact (congrArg ψ'.val (Subtype.ext (Subtype.ext rfl))).trans
      (hG ⟨b, hbi, hbj⟩ y hst')

open scoped Classical in
include hij hopen hct hcL hpi in
/-- **The odd colouring sum is a sum over the glued colourings.** -/
theorem sum_odd_hit {k ℓ : ℕ}
    (st' : GenBoundaryState k ℓ (SurvivingLabel L i j))
    (d : Fin (2 * ℓ))
    (G : (EdgeSubset.mk (liftSubsetOpen hopen t) hcL :
      EdgeSubset V).EdgeOddColouring ℓ → ℂ) :
    (∑ φW : (EdgeSubset.mk (liftSubsetOpen hopen t) hcL :
        EdgeSubset V).EdgeOddColouring ℓ,
      if edgeOddBoundaryMatch
          (EdgeSubset.mk (liftSubsetOpen hopen t) hcL)
          (GenBoundaryState.extendPair i j st' (Sum.inr d)
            (Sum.inr d)) φW then G φW else 0)
      = ∑ φ' : (EdgeSubset.mk t hct :
          EdgeSubset (V.gluePairOpen i j hij hopen)).EdgeOddColouring
            ℓ,
          if edgeOddBoundaryMatch
              (EdgeSubset.mk (liftSubsetOpen hopen t) hcL)
              (GenBoundaryState.extendPair i j st' (Sum.inr d)
                (Sum.inr d))
              (oddPushHit hij hopen t hct hcL hpi φ') then
            G (oddPushHit hij hopen t hct hcL hpi φ') else 0 := by
  calc (∑ φW : (EdgeSubset.mk (liftSubsetOpen hopen t) hcL :
        EdgeSubset V).EdgeOddColouring ℓ,
      if edgeOddBoundaryMatch
          (EdgeSubset.mk (liftSubsetOpen hopen t) hcL)
          (GenBoundaryState.extendPair i j st' (Sum.inr d)
            (Sum.inr d)) φW then G φW else 0)
      = ∑ φW ∈ Finset.univ.image
          (oddPushHit hij hopen t hct hcL hpi (ℓ := ℓ)),
          (if edgeOddBoundaryMatch
              (EdgeSubset.mk (liftSubsetOpen hopen t) hcL)
              (GenBoundaryState.extendPair i j st' (Sum.inr d)
                (Sum.inr d)) φW then G φW else 0) := by
        refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
        intro φW _ hnotim
        rw [ite_eq_right (fun hmatch => hnotim ?_)]
        obtain ⟨φ', hφ'⟩ := oddPushHit_covers hij hopen t hct hcL
          hpi st' d φW hmatch
        exact Finset.mem_image.mpr ⟨φ', Finset.mem_univ _, hφ'⟩
    _ = _ := Finset.sum_image (fun x _ y _ hxy =>
        oddPushHit_injective hij hopen t hct hcL hpi hxy)

section HitSum

variable (κ' : (EdgeSubset.mk t hct :
    EdgeSubset (V.gluePairOpen i j hij hopen)).RelTransitionSystem)
  (o' : κ'.Orientation)

include hij hopen hct hcL hpi in
open Classical in
/-- **One carried cut, on RS21's colouring sums.**  The join carries
an odd colour, and that colour is the glued colouring's own there —
so again the sum over it has a single term. -/
theorem edgeSum_openCut_hit
    [LinearOrder L]
    {k ℓ : ℕ} (h : MixedFunctional k ℓ)
    (st' : GenBoundaryState k ℓ (SurvivingLabel L i j))
    (hbnd' : genBoundarySubsetMatches
      (V.gluePairOpen i j hij hopen) t st')
    (hbndW : ∀ d : Fin (2 * ℓ), genBoundarySubsetMatches V
      (liftSubsetOpen hopen t)
      (GenBoundaryState.extendPair i j st' (Sum.inr d)
        (Sum.inr d))) :
    (∑ d : Fin (2 * ℓ),
        (EdgeSubset.mk (liftSubsetOpen hopen t) hcL :
          EdgeSubset V).edgeSum h
          (GenBoundaryState.extendPair i j st' (Sum.inr d)
            (Sum.inr d)) (hbndW d)
          (unglueOrientationOpen hij hopen t hct hcL κ' o'))
      = (EdgeSubset.mk t hct : EdgeSubset
          (V.gluePairOpen i j hij hopen)).edgeSum h st' hbnd'
          o' := by
  -- ═══════ THE LIFTED SUM, ONE INTERFACE COLOUR AT A TIME ═══════
  have hL : ∀ d : Fin (2 * ℓ),
      (EdgeSubset.mk (liftSubsetOpen hopen t) hcL :
          EdgeSubset V).edgeSum h
          (GenBoundaryState.extendPair i j st' (Sum.inr d)
            (Sum.inr d)) (hbndW d)
          (unglueOrientationOpen hij hopen t hct hcL κ' o')
        = ∑ ψ' : (EdgeSubset.mk t hct :
              EdgeSubset (V.gluePairOpen i j hij hopen)).EvenColouring
                k,
            if genEvenBoundaryMatch (EdgeSubset.mk t hct :
                EdgeSubset (V.gluePairOpen i j hij hopen)) st'
                hbnd' ψ' then
              (∑ φ' : (EdgeSubset.mk t hct :
                  EdgeSubset (V.gluePairOpen i j hij
                    hopen)).EdgeOddColouring ℓ,
                if (φ'.val ⟨partnerSurvI hopen, hpi⟩ = d ∧
                    edgeOddBoundaryMatch (EdgeSubset.mk t hct :
                      EdgeSubset (V.gluePairOpen i j hij hopen))
                      st' φ') then
                  ∏ v : V.Vertex,
                    (((EdgeSubset.mk t hct : EdgeSubset
                        (V.gluePairOpen i j hij
                          hopen)).coreOddSignAt o' φ'.core v : ℂ) *
                      h.evalOdd ((EdgeSubset.mk t hct : EdgeSubset
                          (V.gluePairOpen i j hij
                            hopen)).evenColoursAt ψ' v)
                        ((EdgeSubset.mk t hct : EdgeSubset
                          (V.gluePairOpen i j hij
                            hopen)).coreOddListAt o' φ'.core v))
                else 0)
            else 0 := by
    intro d
    unfold edgeSum
    refine (Fintype.sum_equiv
      (evenColourEquivHit hij hopen t hct hcL hpi k).symm _ _
      (fun ψ' => ?_)).symm
    by_cases hg : genEvenBoundaryMatch (EdgeSubset.mk t hct :
        EdgeSubset (V.gluePairOpen i j hij hopen)) st' hbnd' ψ'
    · rw [ite_eq_left hg, ite_eq_left ((genEvenBoundaryMatch_hit_iff hij hopen
        t hct hcL hpi st' d (hbndW d) hbnd' ψ').mpr hg),
        sum_odd_hit hij hopen t hct hcL hpi st' d
          (fun φW => ∏ v : V.Vertex,
            (((EdgeSubset.mk (liftSubsetOpen hopen t) hcL :
                EdgeSubset V).coreOddSignAt
                (unglueOrientationOpen hij hopen t hct hcL κ' o')
                φW.core v : ℂ) *
              h.evalOdd ((EdgeSubset.mk (liftSubsetOpen hopen t)
                  hcL : EdgeSubset V).evenColoursAt
                  ((evenColourEquivHit hij hopen t hct hcL hpi
                    k).symm ψ') v)
                ((EdgeSubset.mk (liftSubsetOpen hopen t) hcL :
                  EdgeSubset V).coreOddListAt
                  (unglueOrientationOpen hij hopen t hct hcL κ' o')
                  φW.core v)))]
      refine Finset.sum_congr rfl (fun φ' _ => ?_)
      by_cases hp : (φ'.val ⟨partnerSurvI hopen, hpi⟩ = d ∧
          edgeOddBoundaryMatch (EdgeSubset.mk t hct :
            EdgeSubset (V.gluePairOpen i j hij hopen)) st' φ')
      · rw [ite_eq_left ((edgeOddBoundaryMatch_hit_iff hij hopen t hct
          hcL hpi st' d φ').mpr hp), ite_eq_left hp]
        refine Finset.prod_congr rfl (fun v _ => ?_)
        exact (vertexFactor_transport_T hij hopen t hct hcL κ' o' h
          ((evenColourEquivHit hij hopen t hct hcL hpi k).symm ψ')
          ψ' (fun g h1 h2 =>
            congrArg ψ'.val (Subtype.ext (Subtype.ext rfl)))
          (oddPushHit hij hopen t hct hcL hpi φ').core φ'.core
          (fun g h1 h2 => oddPushHitFun_agrees hij hopen t hct hpi
            φ' g _ _) v).symm
      · rw [ite_eq_right (fun hx => hp ((edgeOddBoundaryMatch_hit_iff hij
          hopen t hct hcL hpi st' d φ').mp hx)), ite_eq_right hp]
    · rw [ite_eq_right hg, ite_eq_right (fun hx => hg
        ((genEvenBoundaryMatch_hit_iff hij hopen t hct hcL hpi st' d
          (hbndW d) hbnd' ψ').mp hx))]
  -- ═══════ SUMMING THE COLOURS BACK UP ═══════
  rw [Finset.sum_congr rfl (fun d (_ : d ∈ Finset.univ) => hL d),
    Finset.sum_comm]
  unfold edgeSum
  refine Finset.sum_congr rfl (fun ψ' _ => ?_)
  by_cases hg : genEvenBoundaryMatch (EdgeSubset.mk t hct :
      EdgeSubset (V.gluePairOpen i j hij hopen)) st' hbnd' ψ'
  · simp only [ite_eq_left hg]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun φ' _ => ?_)
    by_cases hp : edgeOddBoundaryMatch (EdgeSubset.mk t hct :
        EdgeSubset (V.gluePairOpen i j hij hopen)) st' φ'
    · rw [ite_eq_left hp, Finset.sum_eq_single
        (φ'.val ⟨partnerSurvI hopen, hpi⟩)
        (fun d _ hne => ite_eq_right (fun hx => hne hx.1.symm))
        (fun hx => absurd (Finset.mem_univ _) hx), ite_eq_left ⟨rfl, hp⟩]
      rfl
    · rw [ite_eq_right hp]
      exact Finset.sum_eq_zero (fun d _ => ite_eq_right (fun hx => hp hx.2))
  · simp only [ite_eq_right hg]
    exact Finset.sum_const_zero

end HitSum

end Hit

end OpenCut

/-! ## The cut that closes

Gluing an edge whose two ends are both labelled removes it and
leaves a free circle.  RS21 records this explicitly; the colourings
see it as two blocks — the edge outside the subset, carrying an even
colour, and inside it, carrying an odd one — each of which is the
glued fragment's colouring sum over again.
-/

section ClosedCut

variable {L : Type} {V : Fragment L} {i j : L}
  (hij : i ≠ j)
  (hclosed : V.pairing (V.boundaryFlag i) = V.boundaryFlag j)
  (t : Finset (SurvivingFlag V i j))
  (hct : ∀ f ∈ t, (V.gluePairClosed i j hclosed).pairing f ∈ t)

section ClosedFalse

variable (hcL : ∀ f ∈ liftSubsetClosed t false,
  V.pairing f ∈ liftSubsetClosed t false)

include hij in
/-- The `i`-flag is out of the empty lift. -/
theorem boundaryFlagI_notMem_liftClosed_false :
    V.boundaryFlag i ∉ liftSubsetClosed t false := fun hmem =>
  Bool.false_ne_true
    ((boundaryFlagI_mem_liftClosed_iff hij t false).mp hmem)

include hij in
/-- The `j`-flag is out of the empty lift. -/
theorem boundaryFlagJ_notMem_liftClosed_false :
    V.boundaryFlag j ∉ liftSubsetClosed t false := fun hmem =>
  Bool.false_ne_true
    ((boundaryFlagJ_mem_liftClosed_iff hij t false).mp hmem)

include hij in
/-- A flag of the empty lift survives the glue. -/
theorem surviving_of_mem_liftClosed_false {f : V.Flag}
    (hf : f ∈ liftSubsetClosed t false) :
    f ≠ V.boundaryFlag i ∧ f ≠ V.boundaryFlag j :=
  ⟨fun hx => boundaryFlagI_notMem_liftClosed_false hij t (hx ▸ hf),
    fun hx => boundaryFlagJ_notMem_liftClosed_false hij t (hx ▸ hf)⟩

/-- A flag of the empty lift, as a flag of the glued fragment. -/
noncomputable def survOfLiftClosedFalse {f : V.Flag}
    (hf : f ∈ liftSubsetClosed t false) : SurvivingFlag V i j :=
  ⟨f, (surviving_of_mem_liftClosed_false hij t hf).1,
    (surviving_of_mem_liftClosed_false hij t hf).2⟩

/-- A glued subset flag's underlying flag lies in the untaken
closed lift. -/
theorem mem_liftClosed_false_of_mem {g : SurvivingFlag V i j}
    (hg : g ∈ t) : g.val ∈ liftSubsetClosed t false :=
  (surviving_val_mem_liftClosed_iff t false g).mpr hg

/-- A flag of the untaken closed lift lies in the glued subset. -/
theorem survOfLiftClosedFalse_mem {f : V.Flag}
    (hf : f ∈ liftSubsetClosed t false) :
    survOfLiftClosedFalse hij t hf ∈ t :=
  (surviving_val_mem_liftClosed_iff t false _).mp hf

/-- **Odd colourings agree across a closing cut the subset
misses.** -/
noncomputable def oddColourEquivClosedFalse (ℓ : ℕ) :
    (EdgeSubset.mk (liftSubsetClosed t false) hcL :
        EdgeSubset V).EdgeOddColouring ℓ
      ≃ (EdgeSubset.mk t hct :
        EdgeSubset (V.gluePairClosed i j hclosed)).EdgeOddColouring
          ℓ where
  toFun φ :=
    ⟨fun g => φ.val ⟨g.val.val,
        mem_liftClosed_false_of_mem t g.prop⟩,
      fun g =>
        Eq.trans
          (congrArg φ.val (Subtype.ext
            (gluePairClosed_pairing_val hclosed g.val)))
          (φ.prop ⟨g.val.val,
            mem_liftClosed_false_of_mem t g.prop⟩)⟩
  invFun φ' :=
    ⟨fun f => φ'.val ⟨survOfLiftClosedFalse hij t f.prop,
        survOfLiftClosedFalse_mem hij t f.prop⟩,
      fun f => by
        refine Eq.trans ?_ (φ'.prop
          ⟨survOfLiftClosedFalse hij t f.prop,
            survOfLiftClosedFalse_mem hij t f.prop⟩)
        exact congrArg φ'.val (Subtype.ext (Subtype.ext
          (gluePairClosed_pairing_val hclosed
            (survOfLiftClosedFalse hij t f.prop)).symm))⟩
  left_inv _ := rfl
  right_inv _ := rfl

include hij hclosed hct hcL in
/-- **The odd boundary constraint matches across a closing cut the
subset misses.** -/
theorem edgeOddBoundaryMatch_closedFalse {k ℓ : ℕ}
    (st' : GenBoundaryState k ℓ (SurvivingLabel L i j)) (a : Fin k)
    (φ : (EdgeSubset.mk (liftSubsetClosed t false) hcL :
      EdgeSubset V).EdgeOddColouring ℓ) :
    edgeOddBoundaryMatch
        (EdgeSubset.mk (liftSubsetClosed t false) hcL)
        (GenBoundaryState.extendPair i j st' (Sum.inl a)
          (Sum.inl a)) φ
      ↔ edgeOddBoundaryMatch (EdgeSubset.mk t hct :
          EdgeSubset (V.gluePairClosed i j hclosed)) st'
          (oddColourEquivClosedFalse hij hclosed t hct hcL ℓ φ) := by
  constructor
  · intro hW b' c hst hmem
    have hstW : GenBoundaryState.extendPair i j st' (Sum.inl a)
        (Sum.inl a) b'.val = Sum.inr c := by
      rw [GenBoundaryState.extendPair_surviving]
      exact hst
    exact Eq.trans (congrArg φ.val (Subtype.ext rfl))
      (hW b'.val c hstW (mem_liftClosed_false_of_mem t hmem))
  · intro hG b c hst hmem
    have hbi : b ≠ i := by
      intro hx
      rw [hx, GenBoundaryState.extendPair_left] at hst
      exact absurd hst (by simp)
    have hbj : b ≠ j := by
      intro hx
      rw [hx, GenBoundaryState.extendPair_right hij] at hst
      exact absurd hst (by simp)
    have hst' : st' ⟨b, hbi, hbj⟩ = Sum.inr c := by
      rw [← GenBoundaryState.extendPair_surviving st' (Sum.inl a)
        (Sum.inl a) ⟨b, hbi, hbj⟩]
      exact hst
    exact Eq.trans (congrArg φ.val (Subtype.ext rfl))
      (hG ⟨b, hbi, hbj⟩ c hst'
        ((surviving_val_mem_liftClosed_iff t false _).mp hmem))

/-- The pushed even colouring's value at a flag outside the
lift. -/
noncomputable def evenPushClosedFalseFun {k : ℕ} (a : Fin k)
    (ψ' : (EdgeSubset.mk t hct :
      EdgeSubset (V.gluePairClosed i j hclosed)).EvenColouring k)
    (f : {g : V.Flag // g ∉ liftSubsetClosed t false}) : Fin k :=
  if hfi : f.val = V.boundaryFlag i then a
  else if hfj : f.val = V.boundaryFlag j then a
  else ψ'.val ⟨⟨f.val, hfi, hfj⟩, fun hmem => f.prop
    ((surviving_val_mem_liftClosed_iff t false
      ⟨f.val, hfi, hfj⟩).mpr hmem)⟩

/-- At the first glued boundary flag the pushed even colouring
takes the summation colour. -/
theorem evenPushClosedFalseFun_at_i {k : ℕ} (a : Fin k)
    (ψ' : (EdgeSubset.mk t hct :
      EdgeSubset (V.gluePairClosed i j hclosed)).EvenColouring k)
    (hP : V.boundaryFlag i ∉ liftSubsetClosed t false) :
    evenPushClosedFalseFun hclosed t hct a ψ'
        ⟨V.boundaryFlag i, hP⟩ = a := dite_eq_left rfl

include hij in
/-- At the second it takes the same colour. -/
theorem evenPushClosedFalseFun_at_j {k : ℕ} (a : Fin k)
    (ψ' : (EdgeSubset.mk t hct :
      EdgeSubset (V.gluePairClosed i j hclosed)).EvenColouring k)
    (hP : V.boundaryFlag j ∉ liftSubsetClosed t false) :
    evenPushClosedFalseFun hclosed t hct a ψ'
        ⟨V.boundaryFlag j, hP⟩ = a := by
  unfold evenPushClosedFalseFun
  rw [dite_eq_right (fun hEq => hij (V.boundaryFlag_injective hEq).symm),
    dite_eq_left rfl]

/-- Away from the two glued flags the pushed even colouring is
unchanged. -/
theorem evenPushClosedFalseFun_agrees {k : ℕ} (a : Fin k)
    (ψ' : (EdgeSubset.mk t hct :
      EdgeSubset (V.gluePairClosed i j hclosed)).EvenColouring k)
    (g : SurvivingFlag V i j)
    (h1 : g.val ∉ liftSubsetClosed t false) (h2 : g ∉ t) :
    evenPushClosedFalseFun hclosed t hct a ψ' ⟨g.val, h1⟩
      = ψ'.val ⟨g, h2⟩ := by
  unfold evenPushClosedFalseFun
  rw [dite_eq_right g.prop.1, dite_eq_right g.prop.2]

/-- **Push a glued even colouring up to the lift**, colouring the
closed edge with the join's colour. -/
noncomputable def evenPushClosedFalse {k : ℕ} (a : Fin k)
    (ψ' : (EdgeSubset.mk t hct :
      EdgeSubset (V.gluePairClosed i j hclosed)).EvenColouring k) :
    (EdgeSubset.mk (liftSubsetClosed t false) hcL :
      EdgeSubset V).EvenColouring k :=
  ⟨evenPushClosedFalseFun hclosed t hct a ψ', by
    intro f
    have hbi := boundaryFlagI_notMem_liftClosed_false hij t
    have hbj := boundaryFlagJ_notMem_liftClosed_false hij t
    have hpn : V.pairing f.val ∉ liftSubsetClosed t false :=
      (EdgeSubset.mk (liftSubsetClosed t false)
        hcL).pairing_not_mem f.prop
    by_cases hfi : f.val = V.boundaryFlag i
    · have hpv : V.pairing f.val = V.boundaryFlag j := by
        rw [hfi]; exact hclosed
      have h1 : (⟨V.pairing f.val, hpn⟩ :
            {g : V.Flag // g ∉ liftSubsetClosed t false})
          = ⟨V.boundaryFlag j, hbj⟩ := Subtype.ext hpv
      have h2 : f = ⟨V.boundaryFlag i, hbi⟩ := Subtype.ext hfi
      rw [h1, h2, evenPushClosedFalseFun_at_i hclosed t hct,
        evenPushClosedFalseFun_at_j hij hclosed t hct]
    · by_cases hfj : f.val = V.boundaryFlag j
      · have hpv : V.pairing f.val = V.boundaryFlag i := by
          rw [hfj, ← hclosed, V.pairing_invol]
        have h1 : (⟨V.pairing f.val, hpn⟩ :
              {g : V.Flag // g ∉ liftSubsetClosed t false})
            = ⟨V.boundaryFlag i, hbi⟩ := Subtype.ext hpv
        have h2 : f = ⟨V.boundaryFlag j, hbj⟩ := Subtype.ext hfj
        rw [h1, h2, evenPushClosedFalseFun_at_i hclosed t hct,
          evenPushClosedFalseFun_at_j hij hclosed t hct]
      · have hpi' : V.pairing f.val ≠ V.boundaryFlag i := by
          intro hx
          exact hfj (by rw [← hclosed, ← hx, V.pairing_invol])
        have hpj' : V.pairing f.val ≠ V.boundaryFlag j := by
          intro hx
          exact hfi (by rw [← V.pairing_invol f.val, hx, ← hclosed,
            V.pairing_invol])
        have hgn : (⟨f.val, hfi, hfj⟩ : SurvivingFlag V i j) ∉ t :=
          fun hmem => f.prop
            ((surviving_val_mem_liftClosed_iff t false _).mpr hmem)
        have hgn' : ((V.gluePairClosed i j hclosed).pairing
            ⟨f.val, hfi, hfj⟩) ∉ t := fun hmem => hgn
          ((V.gluePairClosed i j hclosed).pairing_invol
            (⟨f.val, hfi, hfj⟩ : SurvivingFlag V i j) ▸ hct _ hmem)
        have hval : ((V.gluePairClosed i j hclosed).pairing
            ⟨f.val, hfi, hfj⟩).val = V.pairing f.val :=
          gluePairClosed_pairing_val hclosed ⟨f.val, hfi, hfj⟩
        have h1 : (⟨V.pairing f.val, hpn⟩ :
              {g : V.Flag // g ∉ liftSubsetClosed t false})
            = ⟨((V.gluePairClosed i j hclosed).pairing
                ⟨f.val, hfi, hfj⟩).val,
              fun hmem => hgn'
                ((surviving_val_mem_liftClosed_iff t false _).mp
                  hmem)⟩ := Subtype.ext hval.symm
        rw [h1, evenPushClosedFalseFun_agrees hclosed t hct a ψ' _ _
            hgn',
          evenPushClosedFalseFun_agrees hclosed t hct a ψ'
            ⟨f.val, hfi, hfj⟩ f.prop hgn]
        exact ψ'.prop ⟨⟨f.val, hfi, hfj⟩, hgn⟩⟩

include hij hclosed hct hcL in
/-- The push is injective. -/
theorem evenPushClosedFalse_injective {k : ℕ} (a : Fin k) :
    Function.Injective
      (evenPushClosedFalse hij hclosed t hct hcL a (k := k)) := by
  intro ψ₁ ψ₂ hEq
  refine Subtype.ext (funext fun x => ?_)
  have h1 : x.val.val ∉ liftSubsetClosed t false := fun hmem =>
    x.prop ((surviving_val_mem_liftClosed_iff t false x.val).mp
      hmem)
  have hv := congrArg (fun ψ :
    (EdgeSubset.mk (liftSubsetClosed t false) hcL :
      EdgeSubset V).EvenColouring k => ψ.val ⟨x.val.val, h1⟩) hEq
  simp only [] at hv
  have e1 : (evenPushClosedFalse hij hclosed t hct hcL a ψ₁).val
      ⟨x.val.val, h1⟩ = ψ₁.val ⟨x.val, x.prop⟩ :=
    evenPushClosedFalseFun_agrees hclosed t hct a ψ₁ x.val h1 x.prop
  have e2 : (evenPushClosedFalse hij hclosed t hct hcL a ψ₂).val
      ⟨x.val.val, h1⟩ = ψ₂.val ⟨x.val, x.prop⟩ :=
    evenPushClosedFalseFun_agrees hclosed t hct a ψ₂ x.val h1 x.prop
  rw [e1, e2] at hv
  exact hv

include hij hclosed hct hcL in
/-- **The even boundary constraint across a closing cut the subset
misses.** -/
theorem genEvenBoundaryMatch_closedFalse_iff {k ℓ : ℕ}
    (st' : GenBoundaryState k ℓ (SurvivingLabel L i j)) (a : Fin k)
    (hbndW : genBoundarySubsetMatches V (liftSubsetClosed t false)
      (GenBoundaryState.extendPair i j st' (Sum.inl a)
        (Sum.inl a)))
    (hbnd' : genBoundarySubsetMatches
      (V.gluePairClosed i j hclosed) t st')
    (ψ' : (EdgeSubset.mk t hct :
      EdgeSubset (V.gluePairClosed i j hclosed)).EvenColouring k) :
    genEvenBoundaryMatch
        (EdgeSubset.mk (liftSubsetClosed t false) hcL)
        (GenBoundaryState.extendPair i j st' (Sum.inl a)
          (Sum.inl a)) hbndW
        (evenPushClosedFalse hij hclosed t hct hcL a ψ')
      ↔ genEvenBoundaryMatch (EdgeSubset.mk t hct :
          EdgeSubset (V.gluePairClosed i j hclosed)) st' hbnd'
          ψ' := by
  constructor
  · intro hW b' y hst
    have hstW : GenBoundaryState.extendPair i j st' (Sum.inl a)
        (Sum.inl a) b'.val = Sum.inl y := by
      rw [GenBoundaryState.extendPair_surviving]
      exact hst
    exact (evenPushClosedFalseFun_agrees hclosed t hct a ψ'
      (glueBoundaryFlag V i j b') _ _).symm.trans
      (hW b'.val y hstW)
  · intro hG b y hst
    by_cases hbi : b = i
    · subst hbi
      have hy : y = a := Sum.inl.inj (hst.symm.trans
        (GenBoundaryState.extendPair_left st' (Sum.inl a)
          (Sum.inl a)))
      subst hy
      exact evenPushClosedFalseFun_at_i hclosed t hct _ ψ' _
    · by_cases hbj : b = j
      · subst hbj
        have hy : y = a := Sum.inl.inj (hst.symm.trans
          (GenBoundaryState.extendPair_right hij st' (Sum.inl a)
            (Sum.inl a)))
        subst hy
        exact evenPushClosedFalseFun_at_j hij hclosed t hct _ ψ' _
      · have hst' : st' ⟨b, hbi, hbj⟩ = Sum.inl y := by
          rw [← GenBoundaryState.extendPair_surviving st'
            (Sum.inl a) (Sum.inl a) ⟨b, hbi, hbj⟩]
          exact hst
        exact (evenPushClosedFalseFun_agrees hclosed t hct a ψ'
          (glueBoundaryFlag V i j ⟨b, hbi, hbj⟩) _ _).trans
          (hG ⟨b, hbi, hbj⟩ y hst')

include hij hclosed hct hcL in
/-- **Every colouring meeting the join's constraint is a push.** -/
theorem evenPushClosedFalse_covers {k ℓ : ℕ}
    (st' : GenBoundaryState k ℓ (SurvivingLabel L i j)) (a : Fin k)
    (hbndW : genBoundarySubsetMatches V (liftSubsetClosed t false)
      (GenBoundaryState.extendPair i j st' (Sum.inl a)
        (Sum.inl a)))
    (ψW : (EdgeSubset.mk (liftSubsetClosed t false) hcL :
      EdgeSubset V).EvenColouring k)
    (hmatch : genEvenBoundaryMatch
      (EdgeSubset.mk (liftSubsetClosed t false) hcL)
      (GenBoundaryState.extendPair i j st' (Sum.inl a)
        (Sum.inl a)) hbndW ψW) :
    ∃ ψ' : (EdgeSubset.mk t hct :
        EdgeSubset (V.gluePairClosed i j hclosed)).EvenColouring k,
      evenPushClosedFalse hij hclosed t hct hcL a ψ' = ψW := by
  have hbi := boundaryFlagI_notMem_liftClosed_false hij t
  have hbj := boundaryFlagJ_notMem_liftClosed_false hij t
  have hvi : ψW.val ⟨V.boundaryFlag i, hbi⟩ = a :=
    hmatch i a (GenBoundaryState.extendPair_left st' _ _)
  have hvj : ψW.val ⟨V.boundaryFlag j, hbj⟩ = a :=
    hmatch j a (GenBoundaryState.extendPair_right hij st' _ _)
  refine ⟨⟨fun g => ψW.val ⟨g.val.val, fun hmem => g.prop
      ((surviving_val_mem_liftClosed_iff t false g.val).mp hmem)⟩,
    ?_⟩, ?_⟩
  · intro g
    dsimp only []
    have hval : ((V.gluePairClosed i j hclosed).pairing g.val).val
        = V.pairing g.val.val :=
      gluePairClosed_pairing_val hclosed g.val
    have hmA : ((V.gluePairClosed i j hclosed).pairing g.val).val
        ∉ liftSubsetClosed t false := fun hmem =>
      ((EdgeSubset.mk t hct : EdgeSubset
          (V.gluePairClosed i j hclosed)).pairing_not_mem
        g.prop) ((surviving_val_mem_liftClosed_iff t false _).mp
          hmem)
    have hmC : g.val.val ∉ liftSubsetClosed t false := fun hmem =>
      g.prop ((surviving_val_mem_liftClosed_iff t false _).mp hmem)
    have hmB : V.pairing g.val.val ∉ liftSubsetClosed t false :=
      (EdgeSubset.mk (liftSubsetClosed t false)
        hcL).pairing_not_mem hmC
    have h1 : (⟨_, hmA⟩ :
        {f : V.Flag // f ∉ liftSubsetClosed t false})
        = ⟨_, hmB⟩ := Subtype.ext hval
    rw [h1]
    exact ψW.prop ⟨g.val.val, hmC⟩
  · refine Subtype.ext (funext fun f => ?_)
    change evenPushClosedFalseFun hclosed t hct a _ f = ψW.val f
    by_cases hfi : f.val = V.boundaryFlag i
    · have hfe : f = ⟨V.boundaryFlag i, hbi⟩ := Subtype.ext hfi
      rw [hfe]
      exact (evenPushClosedFalseFun_at_i hclosed t hct a _ hbi).trans
        hvi.symm
    · by_cases hfj : f.val = V.boundaryFlag j
      · have hfe : f = ⟨V.boundaryFlag j, hbj⟩ := Subtype.ext hfj
        rw [hfe]
        exact (evenPushClosedFalseFun_at_j hij hclosed t hct a _
          hbj).trans hvj.symm
      · have hgn : (⟨f.val, hfi, hfj⟩ : SurvivingFlag V i j) ∉ t :=
          fun hmem => f.prop
            ((surviving_val_mem_liftClosed_iff t false _).mpr hmem)
        exact evenPushClosedFalseFun_agrees hclosed t hct a _
          ⟨f.val, hfi, hfj⟩ f.prop hgn

section ClosedFalseSum

variable (κ' : (EdgeSubset.mk t hct :
    EdgeSubset (V.gluePairClosed i j hclosed)).RelTransitionSystem)
  (o' : κ'.Orientation)

include hij hclosed hct hcL in
open Classical in
/-- **The even colouring sum is a sum over the glued
colourings.** -/
theorem sum_even_closed_false {k ℓ : ℕ}
    (st' : GenBoundaryState k ℓ (SurvivingLabel L i j)) (a : Fin k)
    (hbndW : genBoundarySubsetMatches V (liftSubsetClosed t false)
      (GenBoundaryState.extendPair i j st' (Sum.inl a)
        (Sum.inl a)))
    (G : (EdgeSubset.mk (liftSubsetClosed t false) hcL :
      EdgeSubset V).EvenColouring k → ℂ) :
    (∑ ψW : (EdgeSubset.mk (liftSubsetClosed t false) hcL :
        EdgeSubset V).EvenColouring k,
      if genEvenBoundaryMatch
          (EdgeSubset.mk (liftSubsetClosed t false) hcL)
          (GenBoundaryState.extendPair i j st' (Sum.inl a)
            (Sum.inl a)) hbndW ψW then G ψW else 0)
      = ∑ ψ' : (EdgeSubset.mk t hct :
          EdgeSubset (V.gluePairClosed i j hclosed)).EvenColouring k,
          if genEvenBoundaryMatch
              (EdgeSubset.mk (liftSubsetClosed t false) hcL)
              (GenBoundaryState.extendPair i j st' (Sum.inl a)
                (Sum.inl a)) hbndW
              (evenPushClosedFalse hij hclosed t hct hcL a ψ') then
            G (evenPushClosedFalse hij hclosed t hct hcL a ψ')
          else 0 := by
  calc (∑ ψW : (EdgeSubset.mk (liftSubsetClosed t false) hcL :
        EdgeSubset V).EvenColouring k,
      if genEvenBoundaryMatch
          (EdgeSubset.mk (liftSubsetClosed t false) hcL)
          (GenBoundaryState.extendPair i j st' (Sum.inl a)
            (Sum.inl a)) hbndW ψW then G ψW else 0)
      = ∑ ψW ∈ Finset.univ.image
          (evenPushClosedFalse hij hclosed t hct hcL a (k := k)),
          (if genEvenBoundaryMatch
              (EdgeSubset.mk (liftSubsetClosed t false) hcL)
              (GenBoundaryState.extendPair i j st' (Sum.inl a)
                (Sum.inl a)) hbndW ψW then G ψW else 0) := by
        refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
        intro ψW _ hnotim
        rw [ite_eq_right (fun hmatch => hnotim ?_)]
        obtain ⟨ψ', hψ'⟩ := evenPushClosedFalse_covers hij hclosed t
          hct hcL st' a hbndW ψW hmatch
        exact Finset.mem_image.mpr ⟨ψ', Finset.mem_univ _, hψ'⟩
    _ = _ := Finset.sum_image (fun x _ y _ hxy =>
        evenPushClosedFalse_injective hij hclosed t hct hcL a hxy)

include hij hclosed hct hcL in
open Classical in
/-- **A closing cut the subset misses, on RS21's colouring sums.**
The closed edge carries the join's even colour and nothing else
changes, so each of the `k` colours reproduces the glued sum. -/
theorem edgeSum_closedCut_false
    [LinearOrder L]
    {k ℓ : ℕ} (h : MixedFunctional k ℓ)
    (st' : GenBoundaryState k ℓ (SurvivingLabel L i j)) (a : Fin k)
    (hbnd' : genBoundarySubsetMatches
      (V.gluePairClosed i j hclosed) t st')
    (hbndW : genBoundarySubsetMatches V (liftSubsetClosed t false)
      (GenBoundaryState.extendPair i j st' (Sum.inl a)
        (Sum.inl a))) :
    (EdgeSubset.mk (liftSubsetClosed t false) hcL :
        EdgeSubset V).edgeSum h
        (GenBoundaryState.extendPair i j st' (Sum.inl a)
          (Sum.inl a)) hbndW
        (unglueOrientationClosed hclosed false t hct hcL κ' o')
      = (EdgeSubset.mk t hct : EdgeSubset
          (V.gluePairClosed i j hclosed)).edgeSum h st' hbnd'
          o' := by
  unfold edgeSum
  rw [sum_even_closed_false hij hclosed t hct hcL st' a hbndW
    (fun ψW => ∑ φ : (EdgeSubset.mk (liftSubsetClosed t false)
        hcL : EdgeSubset V).EdgeOddColouring ℓ,
      if edgeOddBoundaryMatch
          (EdgeSubset.mk (liftSubsetClosed t false) hcL)
          (GenBoundaryState.extendPair i j st' (Sum.inl a)
            (Sum.inl a)) φ then
        ∏ v : V.Vertex,
          (((EdgeSubset.mk (liftSubsetClosed t false) hcL :
              EdgeSubset V).coreOddSignAt
              (unglueOrientationClosed hclosed false t hct hcL κ' o')
              φ.core v : ℂ) *
            h.evalOdd ((EdgeSubset.mk (liftSubsetClosed t false)
                hcL : EdgeSubset V).evenColoursAt ψW v)
              ((EdgeSubset.mk (liftSubsetClosed t false) hcL :
                EdgeSubset V).coreOddListAt
                (unglueOrientationClosed hclosed false t hct hcL κ'
                  o') φ.core v))
      else 0)]
  refine Finset.sum_congr rfl (fun ψ' _ => ?_)
  by_cases hg : genEvenBoundaryMatch (EdgeSubset.mk t hct :
      EdgeSubset (V.gluePairClosed i j hclosed)) st' hbnd' ψ'
  · rw [ite_eq_left ((genEvenBoundaryMatch_closedFalse_iff hij hclosed t
      hct hcL st' a hbndW hbnd' ψ').mpr hg), ite_eq_left hg]
    refine Fintype.sum_equiv
      (oddColourEquivClosedFalse hij hclosed t hct hcL ℓ) _ _
      (fun φ => ?_)
    by_cases hm : edgeOddBoundaryMatch
        (EdgeSubset.mk (liftSubsetClosed t false) hcL)
        (GenBoundaryState.extendPair i j st' (Sum.inl a)
          (Sum.inl a)) φ
    · rw [ite_eq_left hm, ite_eq_left ((edgeOddBoundaryMatch_closedFalse hij
        hclosed t hct hcL st' a φ).mp hm)]
      refine Finset.prod_congr rfl (fun v _ => ?_)
      exact vertexFactor_transport_closed hclosed t false hct hcL
        κ' o' h (evenPushClosedFalse hij hclosed t hct hcL a ψ') ψ'
        (fun g h1 h2 => evenPushClosedFalseFun_agrees hclosed t hct
          a ψ' g h1 h2)
        φ.core (oddColourEquivClosedFalse hij hclosed t hct hcL ℓ
          φ).core
        (fun g h1 h2 => congrArg φ.val (Subtype.ext rfl)) v
    · rw [ite_eq_right hm, ite_eq_right (fun hx => hm
        ((edgeOddBoundaryMatch_closedFalse hij hclosed t hct hcL st'
          a φ).mpr hx))]
  · rw [ite_eq_right (fun hx => hg ((genEvenBoundaryMatch_closedFalse_iff
      hij hclosed t hct hcL st' a hbndW hbnd' ψ').mp hx)),
      ite_eq_right hg]

end ClosedFalseSum

end ClosedFalse

section ClosedTrue

variable (hcT : ∀ f ∈ liftSubsetClosed t true,
  V.pairing f ∈ liftSubsetClosed t true)

include hij in
/-- The `i`-flag is in the carried lift. -/
theorem boundaryFlagI_mem_liftClosed_true :
    V.boundaryFlag i ∈ liftSubsetClosed t true :=
  (boundaryFlagI_mem_liftClosed_iff hij t true).mpr rfl

include hij in
/-- The `j`-flag is in the carried lift. -/
theorem boundaryFlagJ_mem_liftClosed_true :
    V.boundaryFlag j ∈ liftSubsetClosed t true :=
  (boundaryFlagJ_mem_liftClosed_iff hij t true).mpr rfl

include hij in
/-- A flag outside the carried lift survives the glue. -/
theorem surviving_of_notMem_liftClosed_true {f : V.Flag}
    (hf : f ∉ liftSubsetClosed t true) :
    f ≠ V.boundaryFlag i ∧ f ≠ V.boundaryFlag j :=
  ⟨fun hx => hf (hx ▸ boundaryFlagI_mem_liftClosed_true hij t),
    fun hx => hf (hx ▸ boundaryFlagJ_mem_liftClosed_true hij t)⟩

/-- A flag outside the carried lift, as a glued flag. -/
noncomputable def survOfNotLiftClosedTrue {f : V.Flag}
    (hf : f ∉ liftSubsetClosed t true) : SurvivingFlag V i j :=
  ⟨f, (surviving_of_notMem_liftClosed_true hij t hf).1,
    (surviving_of_notMem_liftClosed_true hij t hf).2⟩

/-- A flag outside the taken closed lift lies outside the glued
subset. -/
theorem survOfNotLiftClosedTrue_notMem {f : V.Flag}
    (hf : f ∉ liftSubsetClosed t true) :
    survOfNotLiftClosedTrue hij t hf ∉ t := fun hm =>
  hf ((surviving_val_mem_liftClosed_iff t true _).mpr hm)

/-- A glued subset flag's underlying flag lies in the taken closed
lift. -/
theorem mem_liftClosed_true_of_mem {g : SurvivingFlag V i j}
    (hg : g ∈ t) : g.val ∈ liftSubsetClosed t true :=
  (surviving_val_mem_liftClosed_iff t true g).mpr hg

/-- And a flag outside the glued subset lies outside it. -/
theorem notMem_liftClosed_true_of_notMem {g : SurvivingFlag V i j}
    (hg : g ∉ t) : g.val ∉ liftSubsetClosed t true := fun hm =>
  hg ((surviving_val_mem_liftClosed_iff t true g).mp hm)

/-- **Even colourings agree across a closing cut the subset
carries.** -/
noncomputable def evenColourEquivClosedTrue (k : ℕ) :
    (EdgeSubset.mk (liftSubsetClosed t true) hcT :
        EdgeSubset V).EvenColouring k
      ≃ (EdgeSubset.mk t hct :
        EdgeSubset (V.gluePairClosed i j hclosed)).EvenColouring
          k where
  toFun ψ :=
    ⟨fun g => ψ.val ⟨g.val.val,
        notMem_liftClosed_true_of_notMem t g.prop⟩,
      fun g =>
        Eq.trans
          (congrArg ψ.val (Subtype.ext
            (gluePairClosed_pairing_val hclosed g.val)))
          (ψ.prop ⟨g.val.val,
            notMem_liftClosed_true_of_notMem t g.prop⟩)⟩
  invFun ψ' :=
    ⟨fun f => ψ'.val ⟨survOfNotLiftClosedTrue hij t f.prop,
        survOfNotLiftClosedTrue_notMem hij t f.prop⟩,
      fun f => by
        refine Eq.trans ?_ (ψ'.prop
          ⟨survOfNotLiftClosedTrue hij t f.prop,
            survOfNotLiftClosedTrue_notMem hij t f.prop⟩)
        exact congrArg ψ'.val (Subtype.ext (Subtype.ext
          (gluePairClosed_pairing_val hclosed
            (survOfNotLiftClosedTrue hij t f.prop)).symm))⟩
  left_inv _ := rfl
  right_inv _ := rfl

include hij hclosed hct hcT in
/-- **The even boundary constraint across a closing cut the subset
carries.** -/
theorem genEvenBoundaryMatch_closedTrue_iff {k ℓ : ℕ}
    (st' : GenBoundaryState k ℓ (SurvivingLabel L i j))
    (d : Fin (2 * ℓ))
    (hbndW : genBoundarySubsetMatches V (liftSubsetClosed t true)
      (GenBoundaryState.extendPair i j st' (Sum.inr d)
        (Sum.inr d)))
    (hbnd' : genBoundarySubsetMatches
      (V.gluePairClosed i j hclosed) t st')
    (ψ' : (EdgeSubset.mk t hct :
      EdgeSubset (V.gluePairClosed i j hclosed)).EvenColouring k) :
    genEvenBoundaryMatch
        (EdgeSubset.mk (liftSubsetClosed t true) hcT)
        (GenBoundaryState.extendPair i j st' (Sum.inr d)
          (Sum.inr d)) hbndW
        ((evenColourEquivClosedTrue hij hclosed t hct hcT k).symm
          ψ')
      ↔ genEvenBoundaryMatch (EdgeSubset.mk t hct :
          EdgeSubset (V.gluePairClosed i j hclosed)) st' hbnd'
          ψ' := by
  constructor
  · intro hW b' y hst
    have hstW : GenBoundaryState.extendPair i j st' (Sum.inr d)
        (Sum.inr d) b'.val = Sum.inl y := by
      rw [GenBoundaryState.extendPair_surviving]
      exact hst
    exact (congrArg ψ'.val (Subtype.ext (Subtype.ext
      rfl))).symm.trans (hW b'.val y hstW)
  · intro hG b y hst
    have hbi : b ≠ i := by
      intro hx
      rw [hx, GenBoundaryState.extendPair_left] at hst
      exact absurd hst (by simp)
    have hbj : b ≠ j := by
      intro hx
      rw [hx, GenBoundaryState.extendPair_right hij] at hst
      exact absurd hst (by simp)
    have hst' : st' ⟨b, hbi, hbj⟩ = Sum.inl y := by
      rw [← GenBoundaryState.extendPair_surviving st' (Sum.inr d)
        (Sum.inr d) ⟨b, hbi, hbj⟩]
      exact hst
    exact (congrArg ψ'.val (Subtype.ext (Subtype.ext rfl))).trans
      (hG ⟨b, hbi, hbj⟩ y hst')

/-- The pushed odd colouring's value at a flag of the carried
lift. -/
noncomputable def oddPushClosedTrueFun {ℓ : ℕ} (d : Fin (2 * ℓ))
    (φ' : (EdgeSubset.mk t hct :
      EdgeSubset (V.gluePairClosed i j hclosed)).EdgeOddColouring ℓ)
    (f : {g : V.Flag // g ∈ liftSubsetClosed t true}) :
    Fin (2 * ℓ) :=
  if hfi : f.val = V.boundaryFlag i then d
  else if hfj : f.val = V.boundaryFlag j then d
  else φ'.val ⟨⟨f.val, hfi, hfj⟩,
    (surviving_val_mem_liftClosed_iff t true
      ⟨f.val, hfi, hfj⟩).mp f.prop⟩

/-- At the first glued boundary flag the pushed odd colouring takes
the circle's colour. -/
theorem oddPushClosedTrueFun_at_i {ℓ : ℕ} (d : Fin (2 * ℓ))
    (φ' : (EdgeSubset.mk t hct :
      EdgeSubset (V.gluePairClosed i j hclosed)).EdgeOddColouring ℓ)
    (hP : V.boundaryFlag i ∈ liftSubsetClosed t true) :
    oddPushClosedTrueFun hclosed t hct d φ' ⟨V.boundaryFlag i, hP⟩
      = d := dite_eq_left rfl

include hij in
/-- At the second it takes the same colour. -/
theorem oddPushClosedTrueFun_at_j {ℓ : ℕ} (d : Fin (2 * ℓ))
    (φ' : (EdgeSubset.mk t hct :
      EdgeSubset (V.gluePairClosed i j hclosed)).EdgeOddColouring ℓ)
    (hP : V.boundaryFlag j ∈ liftSubsetClosed t true) :
    oddPushClosedTrueFun hclosed t hct d φ' ⟨V.boundaryFlag j, hP⟩
      = d := by
  unfold oddPushClosedTrueFun
  rw [dite_eq_right (fun hEq => hij (V.boundaryFlag_injective hEq).symm),
    dite_eq_left rfl]

/-- Away from the two glued flags the pushed odd colouring is
unchanged. -/
theorem oddPushClosedTrueFun_agrees {ℓ : ℕ} (d : Fin (2 * ℓ))
    (φ' : (EdgeSubset.mk t hct :
      EdgeSubset (V.gluePairClosed i j hclosed)).EdgeOddColouring ℓ)
    (g : SurvivingFlag V i j)
    (h1 : g.val ∈ liftSubsetClosed t true) (h2 : g ∈ t) :
    oddPushClosedTrueFun hclosed t hct d φ' ⟨g.val, h1⟩
      = φ'.val ⟨g, h2⟩ := by
  unfold oddPushClosedTrueFun
  rw [dite_eq_right g.prop.1, dite_eq_right g.prop.2]

/-- **Push a glued odd colouring up to the carried lift**, colouring
the closed edge with the join's colour. -/
noncomputable def oddPushClosedTrue {ℓ : ℕ} (d : Fin (2 * ℓ))
    (φ' : (EdgeSubset.mk t hct :
      EdgeSubset (V.gluePairClosed i j hclosed)).EdgeOddColouring
        ℓ) :
    (EdgeSubset.mk (liftSubsetClosed t true) hcT :
      EdgeSubset V).EdgeOddColouring ℓ :=
  ⟨oddPushClosedTrueFun hclosed t hct d φ', by
    intro f
    have hbi := boundaryFlagI_mem_liftClosed_true hij t
    have hbj := boundaryFlagJ_mem_liftClosed_true hij t
    have hpm : V.pairing f.val ∈ liftSubsetClosed t true :=
      hcT _ f.prop
    by_cases hfi : f.val = V.boundaryFlag i
    · have hpv : V.pairing f.val = V.boundaryFlag j := by
        rw [hfi]; exact hclosed
      have h1 : (⟨V.pairing f.val, hpm⟩ :
            {g : V.Flag // g ∈ liftSubsetClosed t true})
          = ⟨V.boundaryFlag j, hbj⟩ := Subtype.ext hpv
      have h2 : f = ⟨V.boundaryFlag i, hbi⟩ := Subtype.ext hfi
      rw [h1, h2, oddPushClosedTrueFun_at_i hclosed t hct,
        oddPushClosedTrueFun_at_j hij hclosed t hct]
    · by_cases hfj : f.val = V.boundaryFlag j
      · have hpv : V.pairing f.val = V.boundaryFlag i := by
          rw [hfj, ← hclosed, V.pairing_invol]
        have h1 : (⟨V.pairing f.val, hpm⟩ :
              {g : V.Flag // g ∈ liftSubsetClosed t true})
            = ⟨V.boundaryFlag i, hbi⟩ := Subtype.ext hpv
        have h2 : f = ⟨V.boundaryFlag j, hbj⟩ := Subtype.ext hfj
        rw [h1, h2, oddPushClosedTrueFun_at_i hclosed t hct,
          oddPushClosedTrueFun_at_j hij hclosed t hct]
      · have hpi' : V.pairing f.val ≠ V.boundaryFlag i := by
          intro hx
          exact hfj (by rw [← hclosed, ← hx, V.pairing_invol])
        have hpj' : V.pairing f.val ≠ V.boundaryFlag j := by
          intro hx
          exact hfi (by rw [← V.pairing_invol f.val, hx, ← hclosed,
            V.pairing_invol])
        have hgt : (⟨f.val, hfi, hfj⟩ : SurvivingFlag V i j) ∈ t :=
          (surviving_val_mem_liftClosed_iff t true _).mp f.prop
        have hgt' : ((V.gluePairClosed i j hclosed).pairing
            ⟨f.val, hfi, hfj⟩) ∈ t := hct _ hgt
        have hval : ((V.gluePairClosed i j hclosed).pairing
            ⟨f.val, hfi, hfj⟩).val = V.pairing f.val :=
          gluePairClosed_pairing_val hclosed ⟨f.val, hfi, hfj⟩
        have h1 : (⟨V.pairing f.val, hpm⟩ :
              {g : V.Flag // g ∈ liftSubsetClosed t true})
            = ⟨((V.gluePairClosed i j hclosed).pairing
                ⟨f.val, hfi, hfj⟩).val,
              mem_liftClosed_true_of_mem t hgt'⟩ :=
          Subtype.ext hval.symm
        rw [h1, oddPushClosedTrueFun_agrees hclosed t hct d φ' _ _
            hgt',
          oddPushClosedTrueFun_agrees hclosed t hct d φ'
            ⟨f.val, hfi, hfj⟩ f.prop hgt]
        exact φ'.prop ⟨⟨f.val, hfi, hfj⟩, hgt⟩⟩

include hij hclosed hct hcT in
/-- The push is injective. -/
theorem oddPushClosedTrue_injective {ℓ : ℕ} (d : Fin (2 * ℓ)) :
    Function.Injective
      (oddPushClosedTrue hij hclosed t hct hcT d) := by
  intro φ₁ φ₂ hEq
  refine Subtype.ext (funext fun x => ?_)
  have h1 : x.val.val ∈ liftSubsetClosed t true :=
    mem_liftClosed_true_of_mem t x.prop
  have hv := congrArg (fun φ :
    (EdgeSubset.mk (liftSubsetClosed t true) hcT :
      EdgeSubset V).EdgeOddColouring ℓ => φ.val ⟨x.val.val, h1⟩) hEq
  simp only [] at hv
  have e1 : (oddPushClosedTrue hij hclosed t hct hcT d φ₁).val
      ⟨x.val.val, h1⟩ = φ₁.val ⟨x.val, x.prop⟩ :=
    oddPushClosedTrueFun_agrees hclosed t hct d φ₁ x.val h1 x.prop
  have e2 : (oddPushClosedTrue hij hclosed t hct hcT d φ₂).val
      ⟨x.val.val, h1⟩ = φ₂.val ⟨x.val, x.prop⟩ :=
    oddPushClosedTrueFun_agrees hclosed t hct d φ₂ x.val h1 x.prop
  rw [e1, e2] at hv
  exact hv

include hij hclosed hct hcT in
/-- **The odd boundary constraint across a closing cut the subset
carries.** -/
theorem edgeOddBoundaryMatch_closedTrue_iff {k ℓ : ℕ}
    (st' : GenBoundaryState k ℓ (SurvivingLabel L i j))
    (d : Fin (2 * ℓ))
    (φ' : (EdgeSubset.mk t hct :
      EdgeSubset (V.gluePairClosed i j hclosed)).EdgeOddColouring
        ℓ) :
    edgeOddBoundaryMatch
        (EdgeSubset.mk (liftSubsetClosed t true) hcT)
        (GenBoundaryState.extendPair i j st' (Sum.inr d)
          (Sum.inr d))
        (oddPushClosedTrue hij hclosed t hct hcT d φ')
      ↔ edgeOddBoundaryMatch (EdgeSubset.mk t hct :
          EdgeSubset (V.gluePairClosed i j hclosed)) st' φ' := by
  constructor
  · intro hW b' c hst hmem
    have hstW : GenBoundaryState.extendPair i j st' (Sum.inr d)
        (Sum.inr d) b'.val = Sum.inr c := by
      rw [GenBoundaryState.extendPair_surviving]
      exact hst
    exact (oddPushClosedTrueFun_agrees hclosed t hct d φ'
      (glueBoundaryFlag V i j b') _ hmem).symm.trans
      (hW b'.val c hstW (mem_liftClosed_true_of_mem t hmem))
  · intro hG b c hst hmem
    by_cases hbi : b = i
    · subst hbi
      have hc : c = d := Sum.inr.inj (hst.symm.trans
        (GenBoundaryState.extendPair_left st' (Sum.inr d)
          (Sum.inr d)))
      rw [hc]
      exact oddPushClosedTrueFun_at_i hclosed t hct d φ' hmem
    · by_cases hbj : b = j
      · subst hbj
        have hc : c = d := Sum.inr.inj (hst.symm.trans
          (GenBoundaryState.extendPair_right hij st' (Sum.inr d)
            (Sum.inr d)))
        rw [hc]
        exact oddPushClosedTrueFun_at_j hij hclosed t hct d φ' hmem
      · have hst' : st' ⟨b, hbi, hbj⟩ = Sum.inr c := by
          rw [← GenBoundaryState.extendPair_surviving st'
            (Sum.inr d) (Sum.inr d) ⟨b, hbi, hbj⟩]
          exact hst
        have hmg : glueBoundaryFlag V i j ⟨b, hbi, hbj⟩ ∈ t :=
          (surviving_val_mem_liftClosed_iff t true _).mp hmem
        exact (oddPushClosedTrueFun_agrees hclosed t hct d φ'
          (glueBoundaryFlag V i j ⟨b, hbi, hbj⟩) hmem hmg).trans
          (hG ⟨b, hbi, hbj⟩ c hst' hmg)

include hij hclosed hct hcT in
/-- **Every colouring meeting the join's constraint is a push.** -/
theorem oddPushClosedTrue_covers {k ℓ : ℕ}
    (st' : GenBoundaryState k ℓ (SurvivingLabel L i j))
    (d : Fin (2 * ℓ))
    (φW : (EdgeSubset.mk (liftSubsetClosed t true) hcT :
      EdgeSubset V).EdgeOddColouring ℓ)
    (hmatch : edgeOddBoundaryMatch
      (EdgeSubset.mk (liftSubsetClosed t true) hcT)
      (GenBoundaryState.extendPair i j st' (Sum.inr d)
        (Sum.inr d)) φW) :
    ∃ φ' : (EdgeSubset.mk t hct :
        EdgeSubset (V.gluePairClosed i j hclosed)).EdgeOddColouring
          ℓ,
      oddPushClosedTrue hij hclosed t hct hcT d φ' = φW := by
  have hbi := boundaryFlagI_mem_liftClosed_true hij t
  have hbj := boundaryFlagJ_mem_liftClosed_true hij t
  have hvi : φW.val ⟨V.boundaryFlag i, hbi⟩ = d :=
    hmatch i d (GenBoundaryState.extendPair_left st' _ _) hbi
  have hvj : φW.val ⟨V.boundaryFlag j, hbj⟩ = d :=
    hmatch j d (GenBoundaryState.extendPair_right hij st' _ _) hbj
  refine ⟨⟨fun g => φW.val ⟨g.val.val,
      mem_liftClosed_true_of_mem t g.prop⟩, ?_⟩, ?_⟩
  · intro g
    dsimp only []
    have hval : ((V.gluePairClosed i j hclosed).pairing g.val).val
        = V.pairing g.val.val :=
      gluePairClosed_pairing_val hclosed g.val
    have hmA : ((V.gluePairClosed i j hclosed).pairing g.val).val
        ∈ liftSubsetClosed t true :=
      mem_liftClosed_true_of_mem t (hct _ g.prop)
    have hmC : g.val.val ∈ liftSubsetClosed t true :=
      mem_liftClosed_true_of_mem t g.prop
    have hmB : V.pairing g.val.val ∈ liftSubsetClosed t true :=
      hcT _ hmC
    have h1 : (⟨_, hmA⟩ :
        {f : V.Flag // f ∈ liftSubsetClosed t true})
        = ⟨_, hmB⟩ := Subtype.ext hval
    rw [h1]
    exact φW.prop ⟨g.val.val, hmC⟩
  · refine Subtype.ext (funext fun f => ?_)
    change oddPushClosedTrueFun hclosed t hct d _ f = φW.val f
    by_cases hfi : f.val = V.boundaryFlag i
    · have hfe : f = ⟨V.boundaryFlag i, hbi⟩ := Subtype.ext hfi
      rw [hfe]
      exact (oddPushClosedTrueFun_at_i hclosed t hct d _ hbi).trans
        hvi.symm
    · by_cases hfj : f.val = V.boundaryFlag j
      · have hfe : f = ⟨V.boundaryFlag j, hbj⟩ := Subtype.ext hfj
        rw [hfe]
        exact (oddPushClosedTrueFun_at_j hij hclosed t hct d _
          hbj).trans hvj.symm
      · have hgt : (⟨f.val, hfi, hfj⟩ : SurvivingFlag V i j) ∈ t :=
          (surviving_val_mem_liftClosed_iff t true _).mp f.prop
        exact oddPushClosedTrueFun_agrees hclosed t hct d _
          ⟨f.val, hfi, hfj⟩ f.prop hgt

include hij hclosed hct hcT in
open Classical in
/-- **The odd colouring sum is a sum over the glued
colourings.** -/
theorem sum_odd_closed_true {k ℓ : ℕ}
    (st' : GenBoundaryState k ℓ (SurvivingLabel L i j))
    (d : Fin (2 * ℓ))
    (G : (EdgeSubset.mk (liftSubsetClosed t true) hcT :
      EdgeSubset V).EdgeOddColouring ℓ → ℂ) :
    (∑ φW : (EdgeSubset.mk (liftSubsetClosed t true) hcT :
        EdgeSubset V).EdgeOddColouring ℓ,
      if edgeOddBoundaryMatch
          (EdgeSubset.mk (liftSubsetClosed t true) hcT)
          (GenBoundaryState.extendPair i j st' (Sum.inr d)
            (Sum.inr d)) φW then G φW else 0)
      = ∑ φ' : (EdgeSubset.mk t hct :
          EdgeSubset (V.gluePairClosed i j
            hclosed)).EdgeOddColouring ℓ,
          if edgeOddBoundaryMatch
              (EdgeSubset.mk (liftSubsetClosed t true) hcT)
              (GenBoundaryState.extendPair i j st' (Sum.inr d)
                (Sum.inr d))
              (oddPushClosedTrue hij hclosed t hct hcT d φ') then
            G (oddPushClosedTrue hij hclosed t hct hcT d φ')
          else 0 := by
  calc (∑ φW : (EdgeSubset.mk (liftSubsetClosed t true) hcT :
        EdgeSubset V).EdgeOddColouring ℓ,
      if edgeOddBoundaryMatch
          (EdgeSubset.mk (liftSubsetClosed t true) hcT)
          (GenBoundaryState.extendPair i j st' (Sum.inr d)
            (Sum.inr d)) φW then G φW else 0)
      = ∑ φW ∈ Finset.univ.image
          (oddPushClosedTrue hij hclosed t hct hcT d),
          (if edgeOddBoundaryMatch
              (EdgeSubset.mk (liftSubsetClosed t true) hcT)
              (GenBoundaryState.extendPair i j st' (Sum.inr d)
                (Sum.inr d)) φW then G φW else 0) := by
        refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
        intro φW _ hnotim
        rw [ite_eq_right (fun hmatch => hnotim ?_)]
        obtain ⟨φ', hφ'⟩ := oddPushClosedTrue_covers hij hclosed t
          hct hcT st' d φW hmatch
        exact Finset.mem_image.mpr ⟨φ', Finset.mem_univ _, hφ'⟩
    _ = _ := Finset.sum_image (fun x _ y _ hxy =>
        oddPushClosedTrue_injective hij hclosed t hct hcT d hxy)

section ClosedTrueSum

variable (κ' : (EdgeSubset.mk t hct :
    EdgeSubset (V.gluePairClosed i j hclosed)).RelTransitionSystem)
  (o' : κ'.Orientation)

include hij hclosed hct hcT in
open Classical in
/-- **A closing cut the subset carries, on RS21's colouring sums.**
The closed edge carries the join's odd colour and nothing else
changes, so each of the `2ℓ` colours reproduces the glued sum. -/
theorem edgeSum_closedCut_true
    [LinearOrder L]
    {k ℓ : ℕ} (h : MixedFunctional k ℓ)
    (st' : GenBoundaryState k ℓ (SurvivingLabel L i j))
    (d : Fin (2 * ℓ))
    (hbnd' : genBoundarySubsetMatches
      (V.gluePairClosed i j hclosed) t st')
    (hbndW : genBoundarySubsetMatches V (liftSubsetClosed t true)
      (GenBoundaryState.extendPair i j st' (Sum.inr d)
        (Sum.inr d))) :
    (EdgeSubset.mk (liftSubsetClosed t true) hcT :
        EdgeSubset V).edgeSum h
        (GenBoundaryState.extendPair i j st' (Sum.inr d)
          (Sum.inr d)) hbndW
        (unglueOrientationClosed hclosed true t hct hcT κ' o')
      = (EdgeSubset.mk t hct : EdgeSubset
          (V.gluePairClosed i j hclosed)).edgeSum h st' hbnd'
          o' := by
  unfold edgeSum
  refine (Fintype.sum_equiv
    (evenColourEquivClosedTrue hij hclosed t hct hcT k).symm _ _
    (fun ψ' => ?_)).symm
  by_cases hg : genEvenBoundaryMatch (EdgeSubset.mk t hct :
      EdgeSubset (V.gluePairClosed i j hclosed)) st' hbnd' ψ'
  · rw [ite_eq_left hg, ite_eq_left ((genEvenBoundaryMatch_closedTrue_iff hij
      hclosed t hct hcT st' d hbndW hbnd' ψ').mpr hg),
      sum_odd_closed_true hij hclosed t hct hcT st' d
        (fun φW => ∏ v : V.Vertex,
          (((EdgeSubset.mk (liftSubsetClosed t true) hcT :
              EdgeSubset V).coreOddSignAt
              (unglueOrientationClosed hclosed true t hct hcT κ' o')
              φW.core v : ℂ) *
            h.evalOdd ((EdgeSubset.mk (liftSubsetClosed t true)
                hcT : EdgeSubset V).evenColoursAt
                ((evenColourEquivClosedTrue hij hclosed t hct hcT
                  k).symm ψ') v)
              ((EdgeSubset.mk (liftSubsetClosed t true) hcT :
                EdgeSubset V).coreOddListAt
                (unglueOrientationClosed hclosed true t hct hcT κ'
                  o') φW.core v)))]
    refine Finset.sum_congr rfl (fun φ' _ => ?_)
    by_cases hp : edgeOddBoundaryMatch (EdgeSubset.mk t hct :
        EdgeSubset (V.gluePairClosed i j hclosed)) st' φ'
    · rw [ite_eq_left hp, ite_eq_left ((edgeOddBoundaryMatch_closedTrue_iff
        hij hclosed t hct hcT st' d φ').mpr hp)]
      refine Finset.prod_congr rfl (fun v _ => ?_)
      exact (vertexFactor_transport_closed hclosed t true hct hcT
        κ' o' h
        ((evenColourEquivClosedTrue hij hclosed t hct hcT k).symm
          ψ') ψ'
        (fun g h1 h2 =>
          congrArg ψ'.val (Subtype.ext (Subtype.ext rfl)))
        (oddPushClosedTrue hij hclosed t hct hcT d φ').core
        φ'.core
        (fun g h1 h2 => oddPushClosedTrueFun_agrees hclosed t hct d
          φ' g _ _) v).symm
    · rw [ite_eq_right hp, ite_eq_right (fun hx => hp
        ((edgeOddBoundaryMatch_closedTrue_iff hij hclosed t hct hcT
          st' d φ').mp hx))]
  · rw [ite_eq_right hg, ite_eq_right (fun hx => hg
      ((genEvenBoundaryMatch_closedTrue_iff hij hclosed t hct hcT
        st' d hbndW hbnd' ψ').mp hx))]

end ClosedTrueSum

end ClosedTrue

end ClosedCut

end EdgeSubset

end RS
