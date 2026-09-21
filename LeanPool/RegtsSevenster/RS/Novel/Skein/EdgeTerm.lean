/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.ColourGlue
import LeanPool.RegtsSevenster.RS.Novel.Skein.InterfaceContract

/-!
# RS21's summand, at a prescribed circuit count

`edgeSum` is RS21's colouring sum; `s_h(F,H,ω,κ)` is that sum with
the circuit sign in front.  The composition carries its own count
from stage to stage — an open glue may or may not close a circuit,
and settling that is the ledger's business, not the colouring's — so
the summand is named here with the count as a parameter, extended by
zero off the good subsets, exactly as `termAt` is.
-/

namespace RS

namespace EdgeSubset

open Fragment Classical

variable {L : Type}

/-- Transporting the colouring sum along an equality of subsets. -/
theorem edgeSum_relOfEq {V : Fragment L}
    {F F' : EdgeSubset V} (hF : F = F')
    {k ℓ : ℕ} (h : MixedFunctional k ℓ)
    (st : GenBoundaryState k ℓ L)
    (hbnd : genBoundarySubsetMatches V F.flags st)
    (hbnd' : genBoundarySubsetMatches V F'.flags st)
    {κ : F.RelTransitionSystem} (o : κ.Orientation) :
    F'.edgeSum h st hbnd' (orientOfEq hF o)
      = F.edgeSum h st hbnd o := by
  subst hF
  rfl

open Classical in
/-- **RS21's summand at a prescribed circuit count.** -/
noncomputable def edgeTermAt [LinearOrder L] {V : Fragment L}
    {k ℓ : ℕ} (h : MixedFunctional k ℓ)
    (𝒟 : DataFamily V) (st : GenBoundaryState k ℓ L)
    (s : Finset V.Flag) (C : ℕ) : ℂ :=
  if hc : ∀ f ∈ s, V.pairing f ∈ s then
    if hbnd : genBoundarySubsetMatches V s st then
      if hE : (EdgeSubset.mk s hc).Eulerian then
        if hne : Nonempty (EdgeSubset.mk s hc).CanonData then
          ((-1 : ℂ) ^ C) *
            (EdgeSubset.mk s hc).edgeSum h st hbnd
              (𝒟 s hc hE hne).2
        else 0
      else 0
    else 0
  else 0

open Classical in
/-- The summand vanishes off edge-closed flag sets. -/
theorem edgeTermAt_eq_zero_of_not_closed [LinearOrder L] {V : Fragment L}
    {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) (𝒟 : DataFamily V)
    (st : GenBoundaryState k ℓ L) {s : Finset V.Flag}
    (hc : ¬ ∀ f ∈ s, V.pairing f ∈ s) (C : ℕ) :
    edgeTermAt h 𝒟 st s C = 0 := by
  unfold edgeTermAt
  rw [dif_neg hc]

open Classical in
/-- And off subsets that do not match the boundary state. -/
theorem edgeTermAt_eq_zero_of_not_matches [LinearOrder L] {V : Fragment L}
    {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) (𝒟 : DataFamily V)
    (st : GenBoundaryState k ℓ L) {s : Finset V.Flag}
    (hbnd : ¬ genBoundarySubsetMatches V s st) (C : ℕ) :
    edgeTermAt h 𝒟 st s C = 0 := by
  unfold edgeTermAt
  by_cases hc : ∀ f ∈ s, V.pairing f ∈ s
  · rw [dif_pos hc, dif_neg hbnd]
  · rw [dif_neg hc]

open Classical in
/-- And off non-Eulerian subsets. -/
theorem edgeTermAt_eq_zero_of_not_eulerian [LinearOrder L] {V : Fragment L}
    {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) (𝒟 : DataFamily V)
    (st : GenBoundaryState k ℓ L) {s : Finset V.Flag}
    (hc : ∀ f ∈ s, V.pairing f ∈ s)
    (hE : ¬ (EdgeSubset.mk s hc).Eulerian) (C : ℕ) :
    edgeTermAt h 𝒟 st s C = 0 := by
  unfold edgeTermAt
  rw [dif_pos hc]
  by_cases hbnd : genBoundarySubsetMatches V s st
  · rw [dif_pos hbnd, dif_neg hE]
  · rw [dif_neg hbnd]

open Classical in
/-- And off subsets carrying no canonical datum — so the sum runs
over the good subsets only. -/
theorem edgeTermAt_eq_zero_of_not_canon [LinearOrder L] {V : Fragment L}
    {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) (𝒟 : DataFamily V)
    (st : GenBoundaryState k ℓ L) {s : Finset V.Flag}
    (hc : ∀ f ∈ s, V.pairing f ∈ s)
    (hne : ¬ Nonempty (EdgeSubset.mk s hc).CanonData) (C : ℕ) :
    edgeTermAt h 𝒟 st s C = 0 := by
  unfold edgeTermAt
  rw [dif_pos hc]
  by_cases hbnd : genBoundarySubsetMatches V s st
  · rw [dif_pos hbnd]
    by_cases hE : (EdgeSubset.mk s hc).Eulerian
    · rw [dif_pos hE, dif_neg hne]
    · rw [dif_neg hE]
  · rw [dif_neg hbnd]

open Classical in
/-- The summand at a good subset. -/
theorem edgeTermAt_pos [LinearOrder L] {V : Fragment L}
    {k ℓ : ℕ} (h : MixedFunctional k ℓ)
    (𝒟 : DataFamily V) (st : GenBoundaryState k ℓ L)
    {s : Finset V.Flag} (hc : ∀ f ∈ s, V.pairing f ∈ s)
    (hbnd : genBoundarySubsetMatches V s st)
    (hE : (EdgeSubset.mk s hc).Eulerian)
    (hne : Nonempty (EdgeSubset.mk s hc).CanonData) (C : ℕ) :
    edgeTermAt h 𝒟 st s C
      = ((-1 : ℂ) ^ C) *
        (EdgeSubset.mk s hc).edgeSum h st hbnd
          (𝒟 s hc hE hne).2 := by
  unfold edgeTermAt
  rw [dif_pos hc, dif_pos hbnd, dif_pos hE, dif_pos hne]

/-! ## One open cut

The boundary state's colour at the cut is even exactly when the
subset misses it, so the sum over that colour runs over one block
and is the glued fragment's summand.
-/

section OpenCut

/-- A missed cut admits no odd colour at the interface. -/
theorem not_matches_liftOpen_odd_of_miss
    {V : Fragment L} {i : L} {j : L} (hij : i ≠ j)
    (hopen : V.pairing (V.boundaryFlag i) ≠ V.boundaryFlag j)
    (t : Finset (SurvivingFlag V i j))
    (hni : partnerSurvI hopen ∉ t) {k ℓ : ℕ}
    (st' : GenBoundaryState k ℓ (SurvivingLabel L i j))
    (d : Fin (2 * ℓ)) (c' : Fin k ⊕ Fin (2 * ℓ)) :
    ¬ genBoundarySubsetMatches V (liftSubsetOpen hopen t)
        (GenBoundaryState.extendPair i j st' (Sum.inr d) c') := by
  intro hm
  refine hni ((boundaryFlagI_mem_liftOpen_iff hij hopen t).mp
    ((hm i).mpr ⟨d, ?_⟩))
  exact GenBoundaryState.extendPair_left st' _ _

/-- A carried cut admits no even colour at the interface. -/
theorem not_matches_liftOpen_even_of_hit
    {V : Fragment L} {i : L} {j : L} (hij : i ≠ j)
    (hopen : V.pairing (V.boundaryFlag i) ≠ V.boundaryFlag j)
    (t : Finset (SurvivingFlag V i j))
    (hpi : partnerSurvI hopen ∈ t) {k ℓ : ℕ}
    (st' : GenBoundaryState k ℓ (SurvivingLabel L i j))
    (a : Fin k) (c' : Fin k ⊕ Fin (2 * ℓ)) :
    ¬ genBoundarySubsetMatches V (liftSubsetOpen hopen t)
        (GenBoundaryState.extendPair i j st' (Sum.inl a) c') := by
  intro hm
  obtain ⟨e, he⟩ := (hm i).mp
    ((boundaryFlagI_mem_liftOpen_iff hij hopen t).mpr hpi)
  rw [GenBoundaryState.extendPair_left] at he
  exact absurd he (by simp)

/-- On a missed cut the even extensions all match. -/
theorem matches_liftOpen_of_miss {V : Fragment L} {i : L} {j : L} (hij : i ≠ j)
    (hopen : V.pairing (V.boundaryFlag i) ≠ V.boundaryFlag j)
    (t : Finset (SurvivingFlag V i j))
    (hct : ∀ f ∈ t, (V.gluePairOpen i j hij hopen).pairing f ∈ t)
    (hni : partnerSurvI hopen ∉ t)
    {k ℓ : ℕ} (st' : GenBoundaryState k ℓ (SurvivingLabel L i j))
    (hbnd' : genBoundarySubsetMatches
      (V.gluePairOpen i j hij hopen) t st')
    (hcL : ∀ f ∈ liftSubsetOpen hopen t,
      V.pairing f ∈ liftSubsetOpen hopen t) (a : Fin k) :
    genBoundarySubsetMatches V (liftSubsetOpen hopen t)
      (GenBoundaryState.extendPair i j st' (Sum.inl a)
        (Sum.inl a)) := by
  intro b
  by_cases hbi : b = i
  · subst hbi
    rw [GenBoundaryState.extendPair_left,
      boundaryFlagI_mem_liftOpen_iff hij hopen t]
    exact ⟨fun hx => absurd hx hni, fun hx => absurd hx.choose_spec
      (by simp)⟩
  · by_cases hbj : b = j
    · subst hbj
      rw [GenBoundaryState.extendPair_right hij,
        boundaryFlagJ_mem_liftOpen_iff hij hopen t]
      exact ⟨fun hx => absurd hx (partnerSurvJ_notMem_of hij hopen t
          hct hni),
        fun hx => absurd hx.choose_spec (by simp)⟩
    · have hst : GenBoundaryState.extendPair i j st' (Sum.inl a)
          (Sum.inl a) b = st' ⟨b, hbi, hbj⟩ :=
        GenBoundaryState.extendPair_surviving st' _ _
          ⟨b, hbi, hbj⟩
      rw [show V.boundaryFlag b
          = (glueBoundaryFlag V i j ⟨b, hbi, hbj⟩).val from rfl,
        surviving_val_mem_liftOpen_iff hopen t, hst]
      exact hbnd' ⟨b, hbi, hbj⟩

/-- On a carried cut the odd extensions all match. -/
theorem matches_liftOpen_of_hit {V : Fragment L} {i : L} {j : L} (hij : i ≠ j)
    (hopen : V.pairing (V.boundaryFlag i) ≠ V.boundaryFlag j)
    (t : Finset (SurvivingFlag V i j))
    (hct : ∀ f ∈ t, (V.gluePairOpen i j hij hopen).pairing f ∈ t)
    (hpi : partnerSurvI hopen ∈ t)
    {k ℓ : ℕ} (st' : GenBoundaryState k ℓ (SurvivingLabel L i j))
    (hbnd' : genBoundarySubsetMatches
      (V.gluePairOpen i j hij hopen) t st') (d : Fin (2 * ℓ)) :
    genBoundarySubsetMatches V (liftSubsetOpen hopen t)
      (GenBoundaryState.extendPair i j st' (Sum.inr d)
        (Sum.inr d)) := by
  intro b
  by_cases hbi : b = i
  · subst hbi
    rw [GenBoundaryState.extendPair_left,
      boundaryFlagI_mem_liftOpen_iff hij hopen t]
    exact ⟨fun _ => ⟨d, rfl⟩, fun _ => hpi⟩
  · by_cases hbj : b = j
    · subst hbj
      rw [GenBoundaryState.extendPair_right hij,
        boundaryFlagJ_mem_liftOpen_iff hij hopen t]
      exact ⟨fun _ => ⟨d, rfl⟩, fun _ =>
        partnerSurvJ_mem_of_hit hij hopen t hct hpi⟩
    · have hst : GenBoundaryState.extendPair i j st' (Sum.inr d)
          (Sum.inr d) b = st' ⟨b, hbi, hbj⟩ :=
        GenBoundaryState.extendPair_surviving st' _ _
          ⟨b, hbi, hbj⟩
      rw [show V.boundaryFlag b
          = (glueBoundaryFlag V i j ⟨b, hbi, hbj⟩).val from rfl,
        surviving_val_mem_liftOpen_iff hopen t, hst]
      exact hbnd' ⟨b, hbi, hbj⟩

open Classical in
/-- **The base's summand at an open lift** is the glued fragment's
data, unglued. -/
theorem edgeTermAt_liftOpen
    [LinearOrder L] {V : Fragment L} {i : L} {j : L} (hij : i ≠ j)
    (hopen : V.pairing (V.boundaryFlag i) ≠ V.boundaryFlag j)
    (t : Finset (SurvivingFlag V i j))
    (hct : ∀ f ∈ t, (V.gluePairOpen i j hij hopen).pairing f ∈ t)
    {k ℓ : ℕ} (h : MixedFunctional k ℓ)
    (𝒟' : DataFamily (V.gluePairOpen i j hij hopen))
    (hcL : ∀ f ∈ liftSubsetOpen hopen t,
      V.pairing f ∈ liftSubsetOpen hopen t)
    (st : GenBoundaryState k ℓ L)
    (hbnd : genBoundarySubsetMatches V (liftSubsetOpen hopen t)
      st)
    (hE : (EdgeSubset.mk (liftSubsetOpen hopen t) hcL :
      EdgeSubset V).Eulerian)
    (hne : Nonempty (EdgeSubset.mk (liftSubsetOpen hopen t)
      hcL : EdgeSubset V).CanonData)
    (hEt : (EdgeSubset.mk t hct :
      EdgeSubset (V.gluePairOpen i j hij hopen)).Eulerian)
    (hnet : Nonempty (EdgeSubset.mk t hct :
      EdgeSubset (V.gluePairOpen i j hij hopen)).CanonData)
    (C : ℕ) :
    edgeTermAt h (unglueDataOpen hij hopen 𝒟') st
        (liftSubsetOpen hopen t) C
      = ((-1 : ℂ) ^ C) *
        (EdgeSubset.mk (liftSubsetOpen hopen t) hcL :
            EdgeSubset V).edgeSum h st hbnd
          (unglueOrientationOpen hij hopen t hct hcL
            (𝒟' t hct hEt hnet).1 (𝒟' t hct hEt hnet).2) := by
  rw [edgeTermAt_pos h (unglueDataOpen hij hopen 𝒟') st hcL hbnd hE
      hne C,
    unglueDataOpen_apply hij hopen 𝒟' _ hcL hE hne t
      (dropSubset_liftSubsetOpen hopen t) hct hcL rfl hEt hnet]
  exact congrArg (fun z => ((-1 : ℂ) ^ C) * z)
    (edgeSum_relOfEq rfl h st hbnd hbnd _)

open Classical in
/-- **One open cut, on RS21's summands.**  The interface colour is
even exactly when the subset misses the cut, so the sum over it is
the glued fragment's summand. -/
theorem edgeTermAt_openCut
    [LinearOrder L] {V : Fragment L} {i : L} {j : L} (hij : i ≠ j)
    (hopen : V.pairing (V.boundaryFlag i) ≠ V.boundaryFlag j)
    (t : Finset (SurvivingFlag V i j))
    (hct : ∀ f ∈ t, (V.gluePairOpen i j hij hopen).pairing f ∈ t)
    {k ℓ : ℕ} (h : MixedFunctional k ℓ)
    (𝒟' : DataFamily (V.gluePairOpen i j hij hopen))
    (st' : GenBoundaryState k ℓ (SurvivingLabel L i j))
    (hbnd' : genBoundarySubsetMatches
      (V.gluePairOpen i j hij hopen) t st')
    (hEt : (EdgeSubset.mk t hct :
      EdgeSubset (V.gluePairOpen i j hij hopen)).Eulerian)
    (hnet : Nonempty (EdgeSubset.mk t hct :
      EdgeSubset (V.gluePairOpen i j hij hopen)).CanonData)
    (C : ℕ) :
    (∑ c : Fin k ⊕ Fin (2 * ℓ),
        edgeTermAt h (unglueDataOpen hij hopen 𝒟')
          (GenBoundaryState.extendPair i j st' c c)
          (liftSubsetOpen hopen t) C)
      = edgeTermAt h 𝒟' st' t C := by
  have hcL := liftSubsetOpen_pairing_closed hij hopen t hct
  have hE : (EdgeSubset.mk (liftSubsetOpen hopen t) hcL :
      EdgeSubset V).Eulerian :=
    (eulerian_lift_open_iff hij hopen t hct hcL).mpr hEt
  have hne : Nonempty (EdgeSubset.mk (liftSubsetOpen hopen t)
      hcL : EdgeSubset V).CanonData :=
    nonempty_canonData_unglueOpen hij hopen t hct hcL hnet
  rw [edgeTermAt_pos h 𝒟' st' hct hbnd' hEt hnet C,
    Fintype.sum_sum_type]
  by_cases hni : partnerSurvI hopen ∈ t
  · have hz : ∀ a : Fin k,
        edgeTermAt h (unglueDataOpen hij hopen 𝒟')
          (GenBoundaryState.extendPair i j st' (Sum.inl a)
            (Sum.inl a)) (liftSubsetOpen hopen t) C = 0 :=
      fun a => edgeTermAt_eq_zero_of_not_matches h _ _
        (not_matches_liftOpen_even_of_hit hij hopen t hni st' a _) C
    rw [Finset.sum_congr rfl (fun a (_ : a ∈ Finset.univ) => hz a),
      Finset.sum_const_zero, zero_add,
      Finset.sum_congr rfl (fun d (_ : d ∈ Finset.univ) =>
        edgeTermAt_liftOpen hij hopen t hct h 𝒟' hcL _
          (matches_liftOpen_of_hit hij hopen t hct hni st' hbnd' d)
          hE hne hEt hnet C),
      ← Finset.mul_sum,
      edgeSum_openCut_hit hij hopen t hct hcL hni
        (𝒟' t hct hEt hnet).1 (𝒟' t hct hEt hnet).2 h st' hbnd'
        (matches_liftOpen_of_hit hij hopen t hct hni st' hbnd')]
  · have hz : ∀ d : Fin (2 * ℓ),
        edgeTermAt h (unglueDataOpen hij hopen 𝒟')
          (GenBoundaryState.extendPair i j st' (Sum.inr d)
            (Sum.inr d)) (liftSubsetOpen hopen t) C = 0 :=
      fun d => edgeTermAt_eq_zero_of_not_matches h _ _
        (not_matches_liftOpen_odd_of_miss hij hopen t hni st' d _) C
    rw [Finset.sum_congr rfl (fun d (_ : d ∈ Finset.univ) => hz d),
      Finset.sum_const_zero, add_zero,
      Finset.sum_congr rfl (fun a (_ : a ∈ Finset.univ) =>
        edgeTermAt_liftOpen hij hopen t hct h 𝒟' hcL _
          (matches_liftOpen_of_miss hij hopen t hct hni st' hbnd'
            hcL a) hE hne hEt hnet C),
      ← Finset.mul_sum,
      edgeSum_openCut_miss hij hopen t hct hcL hni
        (𝒟' t hct hEt hnet).1 (𝒟' t hct hEt hnet).2 h st' hbnd'
        (matches_liftOpen_of_miss hij hopen t hct hni st' hbnd'
          hcL)]

end OpenCut

/-! ## One open cut, with nothing assumed of the subset

The iteration sums over every subset of the glued fragment, so the
cut's identity is needed with no hypothesis on it.  Off the good
subsets both sides vanish — and where the glue's closure fails, what
kills the lift is the interface state's own diagonality: the lift
would hold one glued flag and not the other, and so want the state
odd at one label and even at the other.
-/

section OpenCutAll

/-- **A diagonal state forces the glue's closure.** -/
theorem rewire_closed_of_liftOpen_closed
    {V : Fragment L} {i : L} {j : L} (hij : i ≠ j)
    (hopen : V.pairing (V.boundaryFlag i) ≠ V.boundaryFlag j)
    (t : Finset (SurvivingFlag V i j))
    {k ℓ : ℕ}
    (st' : GenBoundaryState k ℓ (SurvivingLabel L i j))
    (c : Fin k ⊕ Fin (2 * ℓ))
    (hcl : ∀ f ∈ liftSubsetOpen hopen t,
      V.pairing f ∈ liftSubsetOpen hopen t)
    (hm : genBoundarySubsetMatches V (liftSubsetOpen hopen t)
      (GenBoundaryState.extendPair i j st' c c)) :
    ∀ f ∈ t, (V.gluePairOpen i j hij hopen).pairing f ∈ t := by
  have hi := hm i
  have hj := hm j
  rw [GenBoundaryState.extendPair_left,
    boundaryFlagI_mem_liftOpen_iff hij hopen t] at hi
  rw [GenBoundaryState.extendPair_right hij,
    boundaryFlagJ_mem_liftOpen_iff hij hopen t] at hj
  have hIJ : partnerSurvI hopen ∈ t ↔ partnerSurvJ hopen ∈ t :=
    hi.trans hj.symm
  intro g hg
  by_cases hpi : V.pairing g.val = V.boundaryFlag i
  · rw [gluePairOpen_pairing_interface_i hij hopen g hpi]
    exact hIJ.mp (eq_partnerSurvI_of_pairing hopen g hpi ▸ hg)
  · by_cases hpj : V.pairing g.val = V.boundaryFlag j
    · rw [gluePairOpen_pairing_interface_j hij hopen g hpi hpj]
      exact hIJ.mpr
        (eq_partnerSurvJ_of_pairing hopen g hpj ▸ hg)
    · refine (surviving_val_mem_liftOpen_iff hopen t _).mp ?_
      rw [gluePairOpen_pairing_val_of_ne hij hopen g hpi hpj]
      exact hcl _ ((surviving_val_mem_liftOpen_iff hopen t
        g).mpr hg)

open Classical in
/-- **One open cut, with nothing assumed of the subset.** -/
theorem edgeTermAt_openCut_all
    [LinearOrder L] {V : Fragment L} {i : L} {j : L} (hij : i ≠ j)
    (hopen : V.pairing (V.boundaryFlag i) ≠ V.boundaryFlag j)
    (t : Finset (SurvivingFlag V i j))
    {k ℓ : ℕ} (h : MixedFunctional k ℓ)
    (𝒟' : DataFamily (V.gluePairOpen i j hij hopen))
    (st' : GenBoundaryState k ℓ (SurvivingLabel L i j)) (C : ℕ) :
    (∑ c : Fin k ⊕ Fin (2 * ℓ),
        edgeTermAt h (unglueDataOpen hij hopen 𝒟')
          (GenBoundaryState.extendPair i j st' c c)
          (liftSubsetOpen hopen t) C)
      = edgeTermAt h 𝒟' st' t C := by
  by_cases hct : ∀ f ∈ t,
      (V.gluePairOpen i j hij hopen).pairing f ∈ t
  · have hcL := liftSubsetOpen_pairing_closed hij hopen t hct
    by_cases hbnd' : genBoundarySubsetMatches
        (V.gluePairOpen i j hij hopen) t st'
    · by_cases hEt : (EdgeSubset.mk t hct : EdgeSubset
          (V.gluePairOpen i j hij hopen)).Eulerian
      · by_cases hnet : Nonempty (EdgeSubset.mk t hct : EdgeSubset
            (V.gluePairOpen i j hij hopen)).CanonData
        · exact edgeTermAt_openCut hij hopen t hct h 𝒟' st' hbnd'
            hEt hnet C
        · rw [edgeTermAt_eq_zero_of_not_canon h 𝒟' st' hct hnet C]
          exact Finset.sum_eq_zero (fun c _ =>
            edgeTermAt_eq_zero_of_not_canon h _ _ hcL
              (fun hx => hnet (nonempty_canonData_glueOpen hij hopen
                t hct hcL hx)) C)
      · rw [edgeTermAt_eq_zero_of_not_eulerian h 𝒟' st' hct hEt C]
        exact Finset.sum_eq_zero (fun c _ =>
          edgeTermAt_eq_zero_of_not_eulerian h _ _ hcL
            (fun hx => hEt ((eulerian_lift_open_iff hij hopen t hct
              hcL).mp hx)) C)
    · rw [edgeTermAt_eq_zero_of_not_matches h 𝒟' st' hbnd' C]
      exact Finset.sum_eq_zero (fun c _ =>
        edgeTermAt_eq_zero_of_not_matches h _ _
          (fun hx => hbnd'
            (genBoundarySubsetMatches_glued_of_liftOpen hij hopen t
              st' c c hx)) C)
  · rw [edgeTermAt_eq_zero_of_not_closed h 𝒟' st' hct C]
    refine Finset.sum_eq_zero (fun c _ => ?_)
    by_cases hcL : ∀ f ∈ liftSubsetOpen hopen t,
        V.pairing f ∈ liftSubsetOpen hopen t
    · exact edgeTermAt_eq_zero_of_not_matches h _ _
        (fun hx => hct (rewire_closed_of_liftOpen_closed hij hopen t
          st' c hcL hx)) C
    · exact edgeTermAt_eq_zero_of_not_closed h _ _ hcL C

end OpenCutAll

/-! ## One closing cut

Gluing an edge with both ends labelled leaves a free circle.  On the
base the edge is a trail from one label to the other and carries no
circuit; in the composition it is a circuit, and the ledger records
that as the extra count the carried branch is taken at.  The two
branches then weigh `k` and `−2ℓ`, which is the circle's own value.
-/

section ClosedCut

/-- The empty branch admits no odd colour at the cut. -/
theorem not_matches_liftClosed_odd_false
    {V : Fragment L} {i : L} {j : L} (hij : i ≠ j)
    (t : Finset (SurvivingFlag V i j))
    {k ℓ : ℕ}
    (st' : GenBoundaryState k ℓ (SurvivingLabel L i j))
    (d : Fin (2 * ℓ)) (c' : Fin k ⊕ Fin (2 * ℓ)) :
    ¬ genBoundarySubsetMatches V (liftSubsetClosed t false)
        (GenBoundaryState.extendPair i j st' (Sum.inr d) c') := by
  intro hm
  refine Bool.false_ne_true
    ((boundaryFlagI_mem_liftClosed_iff hij t false).mp
      ((hm i).mpr ⟨d, ?_⟩))
  exact GenBoundaryState.extendPair_left st' _ _

/-- The carried branch admits no even colour at the cut. -/
theorem not_matches_liftClosed_even_true
    {V : Fragment L} {i : L} {j : L} (hij : i ≠ j)
    (t : Finset (SurvivingFlag V i j))
    {k ℓ : ℕ}
    (st' : GenBoundaryState k ℓ (SurvivingLabel L i j))
    (a : Fin k) (c' : Fin k ⊕ Fin (2 * ℓ)) :
    ¬ genBoundarySubsetMatches V (liftSubsetClosed t true)
        (GenBoundaryState.extendPair i j st' (Sum.inl a) c') := by
  intro hm
  obtain ⟨e, he⟩ := (hm i).mp
    ((boundaryFlagI_mem_liftClosed_iff hij t true).mpr rfl)
  rw [GenBoundaryState.extendPair_left] at he
  exact absurd he (by simp)

/-- On the empty branch the even extensions all match. -/
theorem matches_liftClosed_false {V : Fragment L} {i : L} {j : L} (hij : i ≠ j)
    (hclosed : V.pairing (V.boundaryFlag i) = V.boundaryFlag j)
    (t : Finset (SurvivingFlag V i j))
    {k ℓ : ℕ}
    (st' : GenBoundaryState k ℓ (SurvivingLabel L i j))
    (hbnd' : genBoundarySubsetMatches
      (V.gluePairClosed i j hclosed) t st') (a : Fin k) :
    genBoundarySubsetMatches V (liftSubsetClosed t false)
      (GenBoundaryState.extendPair i j st' (Sum.inl a)
        (Sum.inl a)) := by
  intro b
  by_cases hbi : b = i
  · subst hbi
    rw [GenBoundaryState.extendPair_left,
      boundaryFlagI_mem_liftClosed_iff hij t false]
    exact ⟨fun hx => absurd hx Bool.false_ne_true,
      fun hx => absurd hx.choose_spec (by simp)⟩
  · by_cases hbj : b = j
    · subst hbj
      rw [GenBoundaryState.extendPair_right hij,
        boundaryFlagJ_mem_liftClosed_iff hij t false]
      exact ⟨fun hx => absurd hx Bool.false_ne_true,
        fun hx => absurd hx.choose_spec (by simp)⟩
    · have hst : GenBoundaryState.extendPair i j st' (Sum.inl a)
          (Sum.inl a) b = st' ⟨b, hbi, hbj⟩ :=
        GenBoundaryState.extendPair_surviving st' _ _
          ⟨b, hbi, hbj⟩
      rw [show V.boundaryFlag b
          = (glueBoundaryFlag V i j ⟨b, hbi, hbj⟩).val from rfl,
        surviving_val_mem_liftClosed_iff t false, hst]
      exact hbnd' ⟨b, hbi, hbj⟩

/-- On the carried branch the odd extensions all match. -/
theorem matches_liftClosed_true {V : Fragment L} {i : L} {j : L} (hij : i ≠ j)
    (hclosed : V.pairing (V.boundaryFlag i) = V.boundaryFlag j)
    (t : Finset (SurvivingFlag V i j))
    {k ℓ : ℕ}
    (st' : GenBoundaryState k ℓ (SurvivingLabel L i j))
    (hbnd' : genBoundarySubsetMatches
      (V.gluePairClosed i j hclosed) t st') (d : Fin (2 * ℓ)) :
    genBoundarySubsetMatches V (liftSubsetClosed t true)
      (GenBoundaryState.extendPair i j st' (Sum.inr d)
        (Sum.inr d)) := by
  intro b
  by_cases hbi : b = i
  · subst hbi
    rw [GenBoundaryState.extendPair_left,
      boundaryFlagI_mem_liftClosed_iff hij t true]
    exact ⟨fun _ => ⟨d, rfl⟩, fun _ => rfl⟩
  · by_cases hbj : b = j
    · subst hbj
      rw [GenBoundaryState.extendPair_right hij,
        boundaryFlagJ_mem_liftClosed_iff hij t true]
      exact ⟨fun _ => ⟨d, rfl⟩, fun _ => rfl⟩
    · have hst : GenBoundaryState.extendPair i j st' (Sum.inr d)
          (Sum.inr d) b = st' ⟨b, hbi, hbj⟩ :=
        GenBoundaryState.extendPair_surviving st' _ _
          ⟨b, hbi, hbj⟩
      rw [show V.boundaryFlag b
          = (glueBoundaryFlag V i j ⟨b, hbi, hbj⟩).val from rfl,
        surviving_val_mem_liftClosed_iff t true, hst]
      exact hbnd' ⟨b, hbi, hbj⟩

open Classical in
/-- **The base's summand at a closed lift** is the glued fragment's
data, unglued. -/
theorem edgeTermAt_liftClosed
    [LinearOrder L] {V : Fragment L} {i : L} {j : L} (hij : i ≠ j)
    (hclosed : V.pairing (V.boundaryFlag i) = V.boundaryFlag j)
    (t : Finset (SurvivingFlag V i j))
    (hct : ∀ f ∈ t, (V.gluePairClosed i j hclosed).pairing f ∈ t)
    {k ℓ : ℕ} (h : MixedFunctional k ℓ)
    (𝒟' : DataFamily (V.gluePairClosed i j hclosed)) (b : Bool)
    (hcL : ∀ f ∈ liftSubsetClosed t b,
      V.pairing f ∈ liftSubsetClosed t b)
    (st : GenBoundaryState k ℓ L)
    (hbnd : genBoundarySubsetMatches V (liftSubsetClosed t b) st)
    (hE : (EdgeSubset.mk (liftSubsetClosed t b) hcL :
      EdgeSubset V).Eulerian)
    (hne : Nonempty (EdgeSubset.mk (liftSubsetClosed t b) hcL :
      EdgeSubset V).CanonData)
    (hEt : (EdgeSubset.mk t hct :
      EdgeSubset (V.gluePairClosed i j hclosed)).Eulerian)
    (hnet : Nonempty (EdgeSubset.mk t hct :
      EdgeSubset (V.gluePairClosed i j hclosed)).CanonData)
    (C : ℕ) :
    edgeTermAt h (unglueDataClosed hij hclosed 𝒟') st
        (liftSubsetClosed t b) C
      = ((-1 : ℂ) ^ C) *
        (EdgeSubset.mk (liftSubsetClosed t b) hcL :
            EdgeSubset V).edgeSum h st hbnd
          (unglueOrientationClosed hclosed b t hct hcL
            (𝒟' t hct hEt hnet).1 (𝒟' t hct hEt hnet).2) := by
  rw [edgeTermAt_pos h (unglueDataClosed hij hclosed 𝒟') st hcL hbnd
      hE hne C,
    unglueDataClosed_apply hij hclosed 𝒟' _ hcL hE hne t b
      (dropSubset_liftSubsetClosed t b)
      (by simp [boundaryFlagI_mem_liftClosed_iff hij]) hct hcL rfl
      hEt hnet]
  exact congrArg (fun z => ((-1 : ℂ) ^ C) * z)
    (edgeSum_relOfEq rfl h st hbnd hbnd _)

open Classical in
/-- **The empty branch of a closing cut weighs `k`.**  Only the even
colours reach it — the odd ones would ask for the cut's own edge —
and each of them gives the glued term back. -/
theorem edgeTermAt_closedCut_false_row
    [LinearOrder L] {V : Fragment L} {i : L} {j : L} (hij : i ≠ j)
    (hclosed : V.pairing (V.boundaryFlag i) = V.boundaryFlag j)
    (t : Finset (SurvivingFlag V i j))
    (hct : ∀ f ∈ t, (V.gluePairClosed i j hclosed).pairing f ∈ t)
    {k ℓ : ℕ}
    (h : MixedFunctional k ℓ)
    (𝒟' : DataFamily (V.gluePairClosed i j hclosed))
    (st' : GenBoundaryState k ℓ (SurvivingLabel L i j))
    (hbnd' : genBoundarySubsetMatches
      (V.gluePairClosed i j hclosed) t st')
    (hEt : (EdgeSubset.mk t hct :
      EdgeSubset (V.gluePairClosed i j hclosed)).Eulerian)
    (hnet : Nonempty (EdgeSubset.mk t hct :
      EdgeSubset (V.gluePairClosed i j hclosed)).CanonData)
    (C : ℕ) :
    (∑ c : Fin k ⊕ Fin (2 * ℓ),
        edgeTermAt h (unglueDataClosed hij hclosed 𝒟')
          (GenBoundaryState.extendPair i j st' c c)
          (liftSubsetClosed t false) C)
      = (k : ℂ) * edgeTermAt h 𝒟' st' t C := by
  have hcF := liftSubsetClosed_pairing_closed hclosed t false hct
  have hEf := (eulerian_liftClosed_iff' hclosed false t hct
    hcF).mpr hEt
  have hnef := nonempty_canonData_unglueClosed hclosed t hct false
    hcF hnet
  rw [Fintype.sum_sum_type,
    Finset.sum_congr rfl (fun d (_ : d ∈ Finset.univ) =>
      edgeTermAt_eq_zero_of_not_matches h _ _
        (not_matches_liftClosed_odd_false hij t st' d _) C),
    Finset.sum_const_zero, add_zero,
    Finset.sum_congr rfl (fun a (_ : a ∈ Finset.univ) =>
      (edgeTermAt_liftClosed hij hclosed t hct h 𝒟' false hcF _
          (matches_liftClosed_false hij hclosed t st' hbnd' a)
          hEf hnef hEt hnet C).trans
        (congrArg (fun z => ((-1 : ℂ) ^ C) * z)
          (edgeSum_closedCut_false hij hclosed t hct hcF
            (𝒟' t hct hEt hnet).1 (𝒟' t hct hEt hnet).2 h st' a
            hbnd' _))),
    Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, edgeTermAt_pos h 𝒟' st' hct hbnd' hEt hnet C]

open Classical in
/-- **The carried branch of a closing cut weighs `−2ℓ`.**  Only the
odd colours reach it, and each of them gives the glued term back with
the sign the extra carried cut supplies. -/
theorem edgeTermAt_closedCut_true_row
    [LinearOrder L] {V : Fragment L} {i : L} {j : L} (hij : i ≠ j)
    (hclosed : V.pairing (V.boundaryFlag i) = V.boundaryFlag j)
    (t : Finset (SurvivingFlag V i j))
    (hct : ∀ f ∈ t, (V.gluePairClosed i j hclosed).pairing f ∈ t)
    {k ℓ : ℕ}
    (h : MixedFunctional k ℓ)
    (𝒟' : DataFamily (V.gluePairClosed i j hclosed))
    (st' : GenBoundaryState k ℓ (SurvivingLabel L i j))
    (hbnd' : genBoundarySubsetMatches
      (V.gluePairClosed i j hclosed) t st')
    (hEt : (EdgeSubset.mk t hct :
      EdgeSubset (V.gluePairClosed i j hclosed)).Eulerian)
    (hnet : Nonempty (EdgeSubset.mk t hct :
      EdgeSubset (V.gluePairClosed i j hclosed)).CanonData)
    (C : ℕ) :
    (∑ c : Fin k ⊕ Fin (2 * ℓ),
        edgeTermAt h (unglueDataClosed hij hclosed 𝒟')
          (GenBoundaryState.extendPair i j st' c c)
          (liftSubsetClosed t true) (C + 1))
      = (-(2 * ℓ : ℕ) : ℂ) * edgeTermAt h 𝒟' st' t C := by
  have hcT := liftSubsetClosed_pairing_closed hclosed t true hct
  have hEr := (eulerian_liftClosed_iff' hclosed true t hct
    hcT).mpr hEt
  have hner := nonempty_canonData_unglueClosed hclosed t hct true
    hcT hnet
  rw [Fintype.sum_sum_type,
    Finset.sum_congr rfl (fun a (_ : a ∈ Finset.univ) =>
      edgeTermAt_eq_zero_of_not_matches h _ _
        (not_matches_liftClosed_even_true hij t st' a _) (C + 1)),
    Finset.sum_const_zero, zero_add,
    Finset.sum_congr rfl (fun d (_ : d ∈ Finset.univ) =>
      (edgeTermAt_liftClosed hij hclosed t hct h 𝒟' true hcT _
          (matches_liftClosed_true hij hclosed t st' hbnd' d)
          hEr hner hEt hnet (C + 1)).trans
        (congrArg (fun z => ((-1 : ℂ) ^ (C + 1)) * z)
          (edgeSum_closedCut_true hij hclosed t hct hcT
            (𝒟' t hct hEt hnet).1 (𝒟' t hct hEt hnet).2 h st' d
            hbnd' _))),
    Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, edgeTermAt_pos h 𝒟' st' hct hbnd' hEt hnet C,
    pow_succ]
  push_cast
  ring

open Classical in
/-- **One closing cut, on RS21's summands.**  The two branches of the
closed edge weigh `k` and `−2ℓ`, the free circle's own value. -/
theorem edgeTermAt_closedCut
    [LinearOrder L] {V : Fragment L} {i : L} {j : L} (hij : i ≠ j)
    (hclosed : V.pairing (V.boundaryFlag i) = V.boundaryFlag j)
    (t : Finset (SurvivingFlag V i j))
    (hct : ∀ f ∈ t, (V.gluePairClosed i j hclosed).pairing f ∈ t)
    {k ℓ : ℕ} (h : MixedFunctional k ℓ)
    (𝒟' : DataFamily (V.gluePairClosed i j hclosed))
    (st' : GenBoundaryState k ℓ (SurvivingLabel L i j))
    (hbnd' : genBoundarySubsetMatches
      (V.gluePairClosed i j hclosed) t st')
    (hEt : (EdgeSubset.mk t hct :
      EdgeSubset (V.gluePairClosed i j hclosed)).Eulerian)
    (hnet : Nonempty (EdgeSubset.mk t hct :
      EdgeSubset (V.gluePairClosed i j hclosed)).CanonData)
    (C : ℕ) :
    (∑ c : Fin k ⊕ Fin (2 * ℓ),
        edgeTermAt h (unglueDataClosed hij hclosed 𝒟')
          (GenBoundaryState.extendPair i j st' c c)
          (liftSubsetClosed t false) C)
      + (∑ c : Fin k ⊕ Fin (2 * ℓ),
          edgeTermAt h (unglueDataClosed hij hclosed 𝒟')
            (GenBoundaryState.extendPair i j st' c c)
            (liftSubsetClosed t true) (C + 1))
      = ((k : ℂ) - 2 * ℓ) * edgeTermAt h 𝒟' st' t C := by
  have hcF := liftSubsetClosed_pairing_closed hclosed t false hct
  have hcT := liftSubsetClosed_pairing_closed hclosed t true hct
  have hEf := (eulerian_liftClosed_iff' hclosed false t hct
    hcF).mpr hEt
  have hnef := nonempty_canonData_unglueClosed hclosed t hct false
    hcF hnet
  have hEr := (eulerian_liftClosed_iff' hclosed true t hct
    hcT).mpr hEt
  have hner := nonempty_canonData_unglueClosed hclosed t hct true
    hcT hnet
  have h1 : (∑ c : Fin k ⊕ Fin (2 * ℓ),
      edgeTermAt h (unglueDataClosed hij hclosed 𝒟')
        (GenBoundaryState.extendPair i j st' c c)
        (liftSubsetClosed t false) C)
      = (k : ℂ) * (((-1 : ℂ) ^ C) *
        (EdgeSubset.mk t hct : EdgeSubset
          (V.gluePairClosed i j hclosed)).edgeSum h st' hbnd'
          (𝒟' t hct hEt hnet).2) := by
    rw [Fintype.sum_sum_type,
      Finset.sum_congr rfl (fun d (_ : d ∈ Finset.univ) =>
        edgeTermAt_eq_zero_of_not_matches h _ _
          (not_matches_liftClosed_odd_false hij t st' d _) C),
      Finset.sum_const_zero, add_zero,
      Finset.sum_congr rfl (fun a (_ : a ∈ Finset.univ) =>
        (edgeTermAt_liftClosed hij hclosed t hct h 𝒟' false hcF _
            (matches_liftClosed_false hij hclosed t st' hbnd' a)
            hEf hnef hEt hnet C).trans
          (congrArg (fun z => ((-1 : ℂ) ^ C) * z)
            (edgeSum_closedCut_false hij hclosed t hct hcF
              (𝒟' t hct hEt hnet).1 (𝒟' t hct hEt hnet).2 h st' a
              hbnd' _))),
      Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
  have h2 : (∑ c : Fin k ⊕ Fin (2 * ℓ),
      edgeTermAt h (unglueDataClosed hij hclosed 𝒟')
        (GenBoundaryState.extendPair i j st' c c)
        (liftSubsetClosed t true) (C + 1))
      = ((2 * ℓ : ℕ) : ℂ) * (((-1 : ℂ) ^ (C + 1)) *
        (EdgeSubset.mk t hct : EdgeSubset
          (V.gluePairClosed i j hclosed)).edgeSum h st' hbnd'
          (𝒟' t hct hEt hnet).2) := by
    rw [Fintype.sum_sum_type,
      Finset.sum_congr rfl (fun a (_ : a ∈ Finset.univ) =>
        edgeTermAt_eq_zero_of_not_matches h _ _
          (not_matches_liftClosed_even_true hij t st' a _) (C + 1)),
      Finset.sum_const_zero, zero_add,
      Finset.sum_congr rfl (fun d (_ : d ∈ Finset.univ) =>
        (edgeTermAt_liftClosed hij hclosed t hct h 𝒟' true hcT _
            (matches_liftClosed_true hij hclosed t st' hbnd' d)
            hEr hner hEt hnet (C + 1)).trans
          (congrArg (fun z => ((-1 : ℂ) ^ (C + 1)) * z)
            (edgeSum_closedCut_true hij hclosed t hct hcT
              (𝒟' t hct hEt hnet).1 (𝒟' t hct hEt hnet).2 h st' d
              hbnd' _))),
      Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
  rw [h1, h2, edgeTermAt_pos h 𝒟' st' hct hbnd' hEt hnet C, pow_succ]
  push_cast
  ring

end ClosedCut

/-! ## One closing cut, with nothing assumed of the subset -/

section ClosedCutAll

/-- **The glued boundary constraint from the lift's.** -/
theorem genBoundarySubsetMatches_glued_of_liftClosed
    {V : Fragment L} {i : L} {j : L}
    (hclosed : V.pairing (V.boundaryFlag i) = V.boundaryFlag j)
    (t : Finset (SurvivingFlag V i j))
    {k ℓ : ℕ}
    (b : Bool) (st' : GenBoundaryState k ℓ (SurvivingLabel L i j))
    (c c' : Fin k ⊕ Fin (2 * ℓ))
    (hm : genBoundarySubsetMatches V (liftSubsetClosed t b)
      (GenBoundaryState.extendPair i j st' c c')) :
    genBoundarySubsetMatches (V.gluePairClosed i j hclosed) t st' :=
  by
  intro a
  have hval := hm a.val
  rw [GenBoundaryState.extendPair_surviving st' c c' a] at hval
  exact (surviving_val_mem_liftClosed_iff t b
    (glueBoundaryFlag V i j a)).symm.trans hval

/-- **A closed lift's closure is the glue's.** -/
theorem glued_closed_of_liftClosed_closed {V : Fragment L} {i : L} {j : L}
    (hclosed : V.pairing (V.boundaryFlag i) = V.boundaryFlag j)
    (t : Finset (SurvivingFlag V i j))
    (b : Bool)
    (hcl : ∀ f ∈ liftSubsetClosed t b,
      V.pairing f ∈ liftSubsetClosed t b) :
    ∀ f ∈ t, (V.gluePairClosed i j hclosed).pairing f ∈ t := by
  have h := dropSubset_pairing_closed_of_closed hclosed
    (liftSubsetClosed t b) hcl
  rwa [dropSubset_liftSubsetClosed t b] at h

open Classical in
/-- **One closing cut, with nothing assumed of the subset.** -/
theorem edgeTermAt_closedCut_all
    [LinearOrder L] {V : Fragment L} {i : L} {j : L} (hij : i ≠ j)
    (hclosed : V.pairing (V.boundaryFlag i) = V.boundaryFlag j)
    (t : Finset (SurvivingFlag V i j))
    {k ℓ : ℕ}
    (h : MixedFunctional k ℓ)
    (𝒟' : DataFamily (V.gluePairClosed i j hclosed))
    (st' : GenBoundaryState k ℓ (SurvivingLabel L i j)) (C : ℕ) :
    (∑ c : Fin k ⊕ Fin (2 * ℓ),
        edgeTermAt h (unglueDataClosed hij hclosed 𝒟')
          (GenBoundaryState.extendPair i j st' c c)
          (liftSubsetClosed t false) C)
      + (∑ c : Fin k ⊕ Fin (2 * ℓ),
          edgeTermAt h (unglueDataClosed hij hclosed 𝒟')
            (GenBoundaryState.extendPair i j st' c c)
            (liftSubsetClosed t true) (C + 1))
      = ((k : ℂ) - 2 * ℓ) * edgeTermAt h 𝒟' st' t C := by
  by_cases hct : ∀ f ∈ t,
      (V.gluePairClosed i j hclosed).pairing f ∈ t
  · have hcF := liftSubsetClosed_pairing_closed hclosed t false hct
    have hcT := liftSubsetClosed_pairing_closed hclosed t true hct
    by_cases hbnd' : genBoundarySubsetMatches
        (V.gluePairClosed i j hclosed) t st'
    · by_cases hEt : (EdgeSubset.mk t hct : EdgeSubset
          (V.gluePairClosed i j hclosed)).Eulerian
      · by_cases hnet : Nonempty (EdgeSubset.mk t hct : EdgeSubset
            (V.gluePairClosed i j hclosed)).CanonData
        · exact edgeTermAt_closedCut hij hclosed t hct h 𝒟' st'
            hbnd' hEt hnet C
        · rw [edgeTermAt_eq_zero_of_not_canon h 𝒟' st' hct hnet C,
            Finset.sum_eq_zero (fun c _ =>
              edgeTermAt_eq_zero_of_not_canon h _ _ hcF
                (fun hx => hnet (nonempty_canonData_glueClosed
                  hclosed t hct false hcF hx)) C),
            Finset.sum_eq_zero (fun c _ =>
              edgeTermAt_eq_zero_of_not_canon h _ _ hcT
                (fun hx => hnet (nonempty_canonData_glueClosed
                  hclosed t hct true hcT hx)) (C + 1))]
          ring
      · rw [edgeTermAt_eq_zero_of_not_eulerian h 𝒟' st' hct hEt C,
          Finset.sum_eq_zero (fun c _ =>
            edgeTermAt_eq_zero_of_not_eulerian h _ _ hcF
              (fun hx => hEt ((eulerian_liftClosed_iff' hclosed
                false t hct hcF).mp hx)) C),
          Finset.sum_eq_zero (fun c _ =>
            edgeTermAt_eq_zero_of_not_eulerian h _ _ hcT
              (fun hx => hEt ((eulerian_liftClosed_iff' hclosed
                true t hct hcT).mp hx)) (C + 1))]
        ring
    · rw [edgeTermAt_eq_zero_of_not_matches h 𝒟' st' hbnd' C,
        Finset.sum_eq_zero (fun c _ =>
          edgeTermAt_eq_zero_of_not_matches h _ _
            (fun hx => hbnd'
              (genBoundarySubsetMatches_glued_of_liftClosed hclosed t
                false st' c c hx)) C),
        Finset.sum_eq_zero (fun c _ =>
          edgeTermAt_eq_zero_of_not_matches h _ _
            (fun hx => hbnd'
              (genBoundarySubsetMatches_glued_of_liftClosed hclosed t
                true st' c c hx)) (C + 1))]
      ring
  · rw [edgeTermAt_eq_zero_of_not_closed h 𝒟' st' hct C,
      Finset.sum_eq_zero (fun c _ => by
        by_cases hcF : ∀ f ∈ liftSubsetClosed t false,
            V.pairing f ∈ liftSubsetClosed t false
        · exact absurd (glued_closed_of_liftClosed_closed hclosed t
            false hcF) hct
        · exact edgeTermAt_eq_zero_of_not_closed h _ _ hcF C),
      Finset.sum_eq_zero (fun c _ => by
        by_cases hcT : ∀ f ∈ liftSubsetClosed t true,
            V.pairing f ∈ liftSubsetClosed t true
        · exact absurd (glued_closed_of_liftClosed_closed hclosed t
            true hcT) hct
        · exact edgeTermAt_eq_zero_of_not_closed h _ _ hcT (C + 1))]
    ring

open Classical in
/-- **The empty branch of a closing cut weighs `k`**, with nothing
assumed of the subset. -/
theorem edgeTermAt_closedCut_false_row_all
    [LinearOrder L] {V : Fragment L} {i : L} {j : L} (hij : i ≠ j)
    (hclosed : V.pairing (V.boundaryFlag i) = V.boundaryFlag j)
    (t : Finset (SurvivingFlag V i j))
    {k ℓ : ℕ}
    (h : MixedFunctional k ℓ)
    (𝒟' : DataFamily (V.gluePairClosed i j hclosed))
    (st' : GenBoundaryState k ℓ (SurvivingLabel L i j)) (C : ℕ) :
    (∑ c : Fin k ⊕ Fin (2 * ℓ),
        edgeTermAt h (unglueDataClosed hij hclosed 𝒟')
          (GenBoundaryState.extendPair i j st' c c)
          (liftSubsetClosed t false) C)
      = (k : ℂ) * edgeTermAt h 𝒟' st' t C := by
  by_cases hct : ∀ f ∈ t,
      (V.gluePairClosed i j hclosed).pairing f ∈ t
  · have hcF := liftSubsetClosed_pairing_closed hclosed t false hct
    by_cases hbnd' : genBoundarySubsetMatches
        (V.gluePairClosed i j hclosed) t st'
    · by_cases hEt : (EdgeSubset.mk t hct : EdgeSubset
          (V.gluePairClosed i j hclosed)).Eulerian
      · by_cases hnet : Nonempty (EdgeSubset.mk t hct : EdgeSubset
            (V.gluePairClosed i j hclosed)).CanonData
        · exact edgeTermAt_closedCut_false_row hij hclosed t hct h
            𝒟' st' hbnd' hEt hnet C
        · rw [edgeTermAt_eq_zero_of_not_canon h 𝒟' st' hct hnet C,
            Finset.sum_eq_zero (fun c _ =>
              edgeTermAt_eq_zero_of_not_canon h _ _ hcF
                (fun hx => hnet (nonempty_canonData_glueClosed
                  hclosed t hct false hcF hx)) C)]
          ring
      · rw [edgeTermAt_eq_zero_of_not_eulerian h 𝒟' st' hct hEt C,
          Finset.sum_eq_zero (fun c _ =>
            edgeTermAt_eq_zero_of_not_eulerian h _ _ hcF
              (fun hx => hEt ((eulerian_liftClosed_iff' hclosed
                false t hct hcF).mp hx)) C)]
        ring
    · rw [edgeTermAt_eq_zero_of_not_matches h 𝒟' st' hbnd' C,
        Finset.sum_eq_zero (fun c _ =>
          edgeTermAt_eq_zero_of_not_matches h _ _
            (fun hx => hbnd'
              (genBoundarySubsetMatches_glued_of_liftClosed hclosed t
                false st' c c hx)) C)]
      ring
  · rw [edgeTermAt_eq_zero_of_not_closed h 𝒟' st' hct C,
      Finset.sum_eq_zero (fun c _ => by
        by_cases hcF : ∀ f ∈ liftSubsetClosed t false,
            V.pairing f ∈ liftSubsetClosed t false
        · exact absurd (glued_closed_of_liftClosed_closed hclosed t
            false hcF) hct
        · exact edgeTermAt_eq_zero_of_not_closed h _ _ hcF C)]
    ring

open Classical in
/-- **The carried branch of a closing cut weighs `−2ℓ`**, with
nothing assumed of the subset. -/
theorem edgeTermAt_closedCut_true_row_all
    [LinearOrder L] {V : Fragment L} {i : L} {j : L} (hij : i ≠ j)
    (hclosed : V.pairing (V.boundaryFlag i) = V.boundaryFlag j)
    (t : Finset (SurvivingFlag V i j))
    {k ℓ : ℕ}
    (h : MixedFunctional k ℓ)
    (𝒟' : DataFamily (V.gluePairClosed i j hclosed))
    (st' : GenBoundaryState k ℓ (SurvivingLabel L i j)) (C : ℕ) :
    (∑ c : Fin k ⊕ Fin (2 * ℓ),
        edgeTermAt h (unglueDataClosed hij hclosed 𝒟')
          (GenBoundaryState.extendPair i j st' c c)
          (liftSubsetClosed t true) (C + 1))
      = (-(2 * ℓ : ℕ) : ℂ) * edgeTermAt h 𝒟' st' t C := by
  by_cases hct : ∀ f ∈ t,
      (V.gluePairClosed i j hclosed).pairing f ∈ t
  · have hcT := liftSubsetClosed_pairing_closed hclosed t true hct
    by_cases hbnd' : genBoundarySubsetMatches
        (V.gluePairClosed i j hclosed) t st'
    · by_cases hEt : (EdgeSubset.mk t hct : EdgeSubset
          (V.gluePairClosed i j hclosed)).Eulerian
      · by_cases hnet : Nonempty (EdgeSubset.mk t hct : EdgeSubset
            (V.gluePairClosed i j hclosed)).CanonData
        · exact edgeTermAt_closedCut_true_row hij hclosed t hct h
            𝒟' st' hbnd' hEt hnet C
        · rw [edgeTermAt_eq_zero_of_not_canon h 𝒟' st' hct hnet C,
            Finset.sum_eq_zero (fun c _ =>
              edgeTermAt_eq_zero_of_not_canon h _ _ hcT
                (fun hx => hnet (nonempty_canonData_glueClosed
                  hclosed t hct true hcT hx)) (C + 1))]
          ring
      · rw [edgeTermAt_eq_zero_of_not_eulerian h 𝒟' st' hct hEt C,
          Finset.sum_eq_zero (fun c _ =>
            edgeTermAt_eq_zero_of_not_eulerian h _ _ hcT
              (fun hx => hEt ((eulerian_liftClosed_iff' hclosed
                true t hct hcT).mp hx)) (C + 1))]
        ring
    · rw [edgeTermAt_eq_zero_of_not_matches h 𝒟' st' hbnd' C,
        Finset.sum_eq_zero (fun c _ =>
          edgeTermAt_eq_zero_of_not_matches h _ _
            (fun hx => hbnd'
              (genBoundarySubsetMatches_glued_of_liftClosed hclosed t
                true st' c c hx)) (C + 1))]
      ring
  · rw [edgeTermAt_eq_zero_of_not_closed h 𝒟' st' hct C,
      Finset.sum_eq_zero (fun c _ => by
        by_cases hcT : ∀ f ∈ liftSubsetClosed t true,
            V.pairing f ∈ liftSubsetClosed t true
        · exact absurd (glued_closed_of_liftClosed_closed hclosed t
            true hcT) hct
        · exact edgeTermAt_eq_zero_of_not_closed h _ _ hcT (C + 1))]
    ring

end ClosedCutAll

/-! ## RS21's sum over a disjoint union

The two halves of a composition colour their own edges, and a
through-edge of the union is a through-edge of one of them, so the
agreement splits with the sum.
-/

section DisjUnion

/-- The named colour of a left flag is the left half's. -/
theorem usedColour_inl
    {α : Type} {β : Type} [LinearOrder (α ⊕ β)] {W₁ : Fragment α}
    {W₂ : Fragment β} (F : EdgeSubset (W₁.disjUnion W₂))
    {k ℓ : ℕ} (st : GenBoundaryState k ℓ (α ⊕ β))
    (hbnd : genBoundarySubsetMatches (W₁.disjUnion W₂) F.flags st)
    (hbnd₁ : genBoundarySubsetMatches W₁ (leftSub F).flags
      (fun a => st (Sum.inl a)))
    {g : W₁.Flag}
    (hbD : (Sum.inl g : (W₁.disjUnion W₂).Flag) ∈ F.boundaryFlags)
    (hb : g ∈ (leftSub F).boundaryFlags) :
    usedColour F st hbnd hbD
      = usedColour (leftSub F) (fun a => st (Sum.inl a)) hbnd₁ hb :=
  by
  have h1 := usedColour_spec F st hbnd hbD
  have h2 := usedColour_spec (leftSub F) (fun a => st (Sum.inl a))
    hbnd₁ hb
  rw [boundaryLabel_inl hbD hb] at h1
  exact Sum.inr.inj (h1.symm.trans h2)

/-- The named colour of a right flag is the right half's. -/
theorem usedColour_inr
    {α : Type} {β : Type} [LinearOrder (α ⊕ β)] {W₁ : Fragment α}
    {W₂ : Fragment β} (F : EdgeSubset (W₁.disjUnion W₂))
    {k ℓ : ℕ} (st : GenBoundaryState k ℓ (α ⊕ β))
    (hbnd : genBoundarySubsetMatches (W₁.disjUnion W₂) F.flags st)
    (hbnd₂ : genBoundarySubsetMatches W₂ (rightSub F).flags
      (fun b => st (Sum.inr b)))
    {g : W₂.Flag}
    (hbD : (Sum.inr g : (W₁.disjUnion W₂).Flag) ∈ F.boundaryFlags)
    (hb : g ∈ (rightSub F).boundaryFlags) :
    usedColour F st hbnd hbD
      = usedColour (rightSub F) (fun b => st (Sum.inr b)) hbnd₂ hb :=
  by
  have h1 := usedColour_spec F st hbnd hbD
  have h2 := usedColour_spec (rightSub F) (fun b => st (Sum.inr b))
    hbnd₂ hb
  rw [boundaryLabel_inr hbD hb] at h1
  exact Sum.inr.inj (h1.symm.trans h2)

/-- **Agreement restricts to the left half.** -/
theorem throughAgree_left
    {α : Type} {β : Type} [LinearOrder (α ⊕ β)] {W₁ : Fragment α}
    {W₂ : Fragment β} (F : EdgeSubset (W₁.disjUnion W₂))
    {k ℓ : ℕ}
    (st : GenBoundaryState k ℓ (α ⊕ β))
    (hbnd : genBoundarySubsetMatches (W₁.disjUnion W₂) F.flags st)
    (hbnd₁ : genBoundarySubsetMatches W₁ (leftSub F).flags
      (fun a => st (Sum.inl a)))
    (hag : ThroughAgree F st hbnd) :
    ThroughAgree (leftSub F) (fun a => st (Sum.inl a)) hbnd₁ := by
  intro g hb hbp
  have hbD : (Sum.inl g : (W₁.disjUnion W₂).Flag) ∈ F.boundaryFlags :=
    inl_mem_boundary.mpr hb
  have hbpD : (W₁.disjUnion W₂).pairing (Sum.inl g)
      ∈ F.boundaryFlags := inl_mem_boundary.mpr hbp
  rw [← usedColour_inl F st hbnd hbnd₁ hbpD hbp,
    ← usedColour_inl F st hbnd hbnd₁ hbD hb]
  exact hag (Sum.inl g) hbD hbpD

/-- **Agreement restricts to the right half.** -/
theorem throughAgree_right
    {α : Type} {β : Type} [LinearOrder (α ⊕ β)] {W₁ : Fragment α}
    {W₂ : Fragment β} (F : EdgeSubset (W₁.disjUnion W₂))
    {k ℓ : ℕ}
    (st : GenBoundaryState k ℓ (α ⊕ β))
    (hbnd : genBoundarySubsetMatches (W₁.disjUnion W₂) F.flags st)
    (hbnd₂ : genBoundarySubsetMatches W₂ (rightSub F).flags
      (fun b => st (Sum.inr b)))
    (hag : ThroughAgree F st hbnd) :
    ThroughAgree (rightSub F) (fun b => st (Sum.inr b)) hbnd₂ := by
  intro g hb hbp
  have hbD : (Sum.inr g : (W₁.disjUnion W₂).Flag) ∈ F.boundaryFlags :=
    inr_mem_boundary.mpr hb
  have hbpD : (W₁.disjUnion W₂).pairing (Sum.inr g)
      ∈ F.boundaryFlags := inr_mem_boundary.mpr hbp
  rw [← usedColour_inr F st hbnd hbnd₂ hbpD hbp,
    ← usedColour_inr F st hbnd hbnd₂ hbD hb]
  exact hag (Sum.inr g) hbD hbpD

/-- **Agreement on both halves is agreement.** -/
theorem throughAgree_of_parts
    {α : Type} {β : Type} [LinearOrder (α ⊕ β)] {W₁ : Fragment α}
    {W₂ : Fragment β} (F : EdgeSubset (W₁.disjUnion W₂))
    {k ℓ : ℕ}
    (st : GenBoundaryState k ℓ (α ⊕ β))
    (hbnd : genBoundarySubsetMatches (W₁.disjUnion W₂) F.flags st)
    (hbnd₁ : genBoundarySubsetMatches W₁ (leftSub F).flags
      (fun a => st (Sum.inl a)))
    (hbnd₂ : genBoundarySubsetMatches W₂ (rightSub F).flags
      (fun b => st (Sum.inr b)))
    (hag₁ : ThroughAgree (leftSub F) (fun a => st (Sum.inl a))
      hbnd₁)
    (hag₂ : ThroughAgree (rightSub F) (fun b => st (Sum.inr b))
      hbnd₂) :
    ThroughAgree F st hbnd := by
  rintro (g | g) hb hbp
  · have hb' : g ∈ (leftSub F).boundaryFlags := inl_mem_boundary.mp hb
    have hbp' : W₁.pairing g ∈ (leftSub F).boundaryFlags :=
      inl_mem_boundary.mp hbp
    have e1 : usedColour F st hbnd hbp
        = usedColour (leftSub F) (fun a => st (Sum.inl a)) hbnd₁
          hbp' := usedColour_inl F st hbnd hbnd₁ hbp hbp'
    have e2 : usedColour F st hbnd hb
        = usedColour (leftSub F) (fun a => st (Sum.inl a)) hbnd₁
          hb' := usedColour_inl F st hbnd hbnd₁ hb hb'
    rw [e1, e2]
    exact hag₁ g hb' hbp'
  · have hb' : g ∈ (rightSub F).boundaryFlags :=
      inr_mem_boundary.mp hb
    have hbp' : W₂.pairing g ∈ (rightSub F).boundaryFlags :=
      inr_mem_boundary.mp hbp
    have e1 : usedColour F st hbnd hbp
        = usedColour (rightSub F) (fun b => st (Sum.inr b)) hbnd₂
          hbp' := usedColour_inr F st hbnd hbnd₂ hbp hbp'
    have e2 : usedColour F st hbnd hb
        = usedColour (rightSub F) (fun b => st (Sum.inr b)) hbnd₂
          hb' := usedColour_inr F st hbnd hbnd₂ hb hb'
    rw [e1, e2]
    exact hag₂ g hb' hbp'

/-- **RS21's colouring sum splits over a disjoint union.** -/
theorem edgeSum_disjUnion
    {α : Type} {β : Type} [LinearOrder (α ⊕ β)] {W₁ : Fragment α}
    {W₂ : Fragment β} (F : EdgeSubset (W₁.disjUnion W₂))
    {k ℓ : ℕ} (h : MixedFunctional k ℓ)
    (st : GenBoundaryState k ℓ (α ⊕ β))
    (hbnd : genBoundarySubsetMatches (W₁.disjUnion W₂) F.flags st)
    (hbnd₁ : genBoundarySubsetMatches W₁ (leftSub F).flags
      (fun a => st (Sum.inl a)))
    (hbnd₂ : genBoundarySubsetMatches W₂ (rightSub F).flags
      (fun b => st (Sum.inr b)))
    {κ₁ : (leftSub F).RelTransitionSystem}
    {κ₂ : (rightSub F).RelTransitionSystem}
    (o₁ : κ₁.Orientation) (o₂ : κ₂.Orientation) :
    F.edgeSum h st hbnd (prodOrient o₁ o₂)
      = (leftSub F).edgeSum h (fun a => st (Sum.inl a)) hbnd₁ o₁
        * (rightSub F).edgeSum h (fun b => st (Sum.inr b)) hbnd₂
          o₂ := by
  by_cases hag : ThroughAgree F st hbnd
  · rw [edgeSum_eq_vertexSum F h st hbnd _ hag,
      edgeSum_eq_vertexSum (leftSub F) h _ hbnd₁ o₁
        (throughAgree_left F st hbnd hbnd₁ hag),
      edgeSum_eq_vertexSum (rightSub F) h _ hbnd₂ o₂
        (throughAgree_right F st hbnd hbnd₂ hag)]
    exact vertexSum_disjUnion F h st hbnd hbnd₁ hbnd₂ o₁ o₂
  · rw [edgeSum_eq_zero_of_not_throughAgree F h st hbnd _ hag]
    by_cases hag₁ : ThroughAgree (leftSub F)
        (fun a => st (Sum.inl a)) hbnd₁
    · by_cases hag₂ : ThroughAgree (rightSub F)
          (fun b => st (Sum.inr b)) hbnd₂
      · exact absurd (throughAgree_of_parts F st hbnd hbnd₁ hbnd₂
          hag₁ hag₂) hag
      · rw [edgeSum_eq_zero_of_not_throughAgree (rightSub F) h _
          hbnd₂ o₂ hag₂, mul_zero]
    · rw [edgeSum_eq_zero_of_not_throughAgree (leftSub F) h _ hbnd₁
        o₁ hag₁, zero_mul]

end DisjUnion

/-! ## RS21's sum under a relabel

The composition's stages relabel the surviving interface, and the
colouring sum does not see the labels beyond the boundary match.
-/

section Relabel

/-- The odd boundary constraint reindexes through the relabel. -/
theorem relabel_edgeOddBoundaryMatch_iff
    {α : Type} {β : Type} {W : Fragment α} (ee : α ≃ β)
    (F : EdgeSubset W)
    {k ℓ : ℕ} (st : GenBoundaryState k ℓ β)
    (φ : (F.relabelUp ee).EdgeOddColouring ℓ) :
    edgeOddBoundaryMatch (F.relabelUp ee) st φ ↔
      edgeOddBoundaryMatch F (fun a => st (ee a)) φ := by
  constructor
  · intro hm a c hst hmem
    have hmem' : (W.relabel ee).boundaryFlag (ee a)
        ∈ (F.relabelUp ee).flags := by
      rw [relabel_boundaryFlag_apply ee a]
      exact hmem
    have hval := hm (ee a) c hst hmem'
    exact (congrArg φ.val (Subtype.ext
      (relabel_boundaryFlag_apply ee a).symm)).trans hval
  · intro hm b c hst hmem
    have hmem' : W.boundaryFlag (ee.symm b) ∈ F.flags := by
      rw [show W.boundaryFlag (ee.symm b)
          = (W.relabel ee).boundaryFlag b from rfl]
      exact hmem
    have hval := hm (ee.symm b) c
      (by simp only [Equiv.apply_symm_apply]; exact hst) hmem'
    exact (congrArg φ.val (Subtype.ext rfl)).trans hval

/-- The odd colourings are the same on both sides of a relabel: the
flags and the pairing are untouched. -/
def edgeOddRelabelEquiv {α : Type} {β : Type} {W : Fragment α} (ee : α ≃ β)
    (F : EdgeSubset W) (ℓ : ℕ) :
    (F.relabelUp ee).EdgeOddColouring ℓ ≃ F.EdgeOddColouring ℓ :=
  Equiv.refl _

/-- The core of a relabelled colouring is the relabelled core. -/
theorem core_relabel_eq {α : Type} {β : Type} {W : Fragment α} (ee : α ≃ β)
    (F : EdgeSubset W) {ℓ : ℕ}
    (φ : (F.relabelUp ee).EdgeOddColouring ℓ) :
    coreOddRelabelEquiv ee F ℓ φ.core
      = (edgeOddRelabelEquiv ee F ℓ φ).core :=
  Subtype.ext (funext fun _ => congrArg φ.val (Subtype.ext rfl))

/-- **RS21's colouring sum is untouched by a relabel.** -/
theorem relabel_edgeSum {α : Type} {β : Type} {W : Fragment α} (ee : α ≃ β)
    (F : EdgeSubset W) {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) (st : GenBoundaryState k ℓ β)
    (hbnd : genBoundarySubsetMatches (W.relabel ee)
      (F.relabelUp ee).flags st)
    (hbnd' : genBoundarySubsetMatches W F.flags
      (fun a => st (ee a)))
    {κ : F.RelTransitionSystem} (o : κ.Orientation) :
    (F.relabelUp ee).edgeSum h st hbnd (relabelOrientUp ee F o)
      = F.edgeSum h (fun a => st (ee a)) hbnd' o := by
  unfold edgeSum
  refine Fintype.sum_equiv
    (Equiv.refl ((F.relabelUp ee).EvenColouring k) :
      (F.relabelUp ee).EvenColouring k ≃ F.EvenColouring k) _ _
    fun ψ => ?_
  simp only [Equiv.refl_apply]
  refine if_congr
    (relabel_genEvenBoundaryMatch_iff ee F st hbnd hbnd' ψ) ?_ rfl
  refine Fintype.sum_equiv (edgeOddRelabelEquiv ee F ℓ) _ _
    fun φ => ?_
  refine if_congr (relabel_edgeOddBoundaryMatch_iff ee F st φ) ?_ rfl
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [relabel_coreOddSignAt ee F o φ.core v,
    relabel_coreOddListAt ee F o φ.core v,
    relabel_evenColoursAt ee F ψ v, core_relabel_eq ee F φ]

/-- **The data family pulled back along a relabel.** -/
noncomputable def relabelDataDown {α' β' : Type} [LinearOrder α']
    [LinearOrder β'] (e : α' ≃o β') {W' : Fragment α'}
    (𝒟 : DataFamily (W'.relabel e.toEquiv)) : DataFamily W' :=
  fun s hc hE hne =>
    ⟨relabelTransDown e.toEquiv (EdgeSubset.mk s hc)
        (𝒟 s hc
          ((relabelUp_eulerian e.toEquiv
            (EdgeSubset.mk s hc)).mpr hE)
          ((nonempty_canonData_relabelUp e
            (EdgeSubset.mk s hc)).mpr hne)).1,
      relabelOrientDown e.toEquiv (EdgeSubset.mk s hc)
        (𝒟 s hc
          ((relabelUp_eulerian e.toEquiv
            (EdgeSubset.mk s hc)).mpr hE)
          ((nonempty_canonData_relabelUp e
            (EdgeSubset.mk s hc)).mpr hne)).2⟩

open Classical in
/-- **RS21's summand is untouched by a relabel.** -/
theorem edgeTermAt_relabel {α' β' : Type} [LinearOrder α']
    [LinearOrder β'] (e : α' ≃o β') {W' : Fragment α'} {k ℓ : ℕ}
    (h : MixedFunctional k ℓ)
    (𝒟 : DataFamily (W'.relabel e.toEquiv))
    (st : GenBoundaryState k ℓ β') (s : Finset W'.Flag) (C : ℕ) :
    edgeTermAt h 𝒟 st s C
      = edgeTermAt h (relabelDataDown e 𝒟) (fun a => st (e a)) s
        C := by
  by_cases hc : ∀ f ∈ s, W'.pairing f ∈ s
  · have hcU : ∀ f ∈ s, (W'.relabel e.toEquiv).pairing f ∈ s := hc
    by_cases hbnd : genBoundarySubsetMatches W' s (fun a => st (e a))
    · have hbndU : genBoundarySubsetMatches (W'.relabel e.toEquiv) s
          st :=
        (relabel_genBoundarySubsetMatches_iff e.toEquiv s st).mpr
          hbnd
      by_cases hE : (EdgeSubset.mk s hc : EdgeSubset W').Eulerian
      · have hEU : (EdgeSubset.mk s hcU :
            EdgeSubset (W'.relabel e.toEquiv)).Eulerian :=
          (relabelUp_eulerian e.toEquiv (EdgeSubset.mk s hc)).mpr hE
        by_cases hne : Nonempty (EdgeSubset.mk s hc :
            EdgeSubset W').CanonData
        · have hneU : Nonempty (EdgeSubset.mk s hcU :
              EdgeSubset (W'.relabel e.toEquiv)).CanonData :=
            (nonempty_canonData_relabelUp e
              (EdgeSubset.mk s hc)).mpr hne
          rw [edgeTermAt_pos h 𝒟 st hcU hbndU hEU hneU C,
            edgeTermAt_pos h (relabelDataDown e 𝒟) _ hc hbnd hE hne
              C]
          exact congrArg (fun z => ((-1 : ℂ) ^ C) * z)
            (relabel_edgeSum e.toEquiv (EdgeSubset.mk s hc) h st
              hbndU hbnd
              (relabelOrientDown e.toEquiv (EdgeSubset.mk s hc)
                (𝒟 s hc hEU hneU).2))
        · rw [edgeTermAt_eq_zero_of_not_canon h 𝒟 st hcU
            (fun hx => hne ((nonempty_canonData_relabelUp e
              (EdgeSubset.mk s hc)).mp hx)) C,
            edgeTermAt_eq_zero_of_not_canon h (relabelDataDown e 𝒟)
              (fun a => st (e a)) hc hne C]
      · rw [edgeTermAt_eq_zero_of_not_eulerian h 𝒟 st hcU
          (fun hx => hE ((relabelUp_eulerian e.toEquiv
            (EdgeSubset.mk s hc)).mp hx)) C,
          edgeTermAt_eq_zero_of_not_eulerian h (relabelDataDown e 𝒟)
            (fun a => st (e a)) hc hE C]
    · rw [edgeTermAt_eq_zero_of_not_matches h 𝒟 st
        (fun hx => hbnd ((relabel_genBoundarySubsetMatches_iff
          e.toEquiv s st).mp hx)) C,
        edgeTermAt_eq_zero_of_not_matches h (relabelDataDown e 𝒟) _
          hbnd C]
  · rw [edgeTermAt_eq_zero_of_not_closed h 𝒟 st hc C,
      edgeTermAt_eq_zero_of_not_closed h (relabelDataDown e 𝒟)
        (fun a => st (e a)) hc C]

end Relabel

end EdgeSubset

end RS
