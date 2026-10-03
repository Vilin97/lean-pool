/-
Copyright (c) 2023 PDL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDL formalization contributors (see project card)
-/

module

public import LeanPool.PDL.Interpolation.EvalQ
public import LeanPool.PDL.Interpolation.ClusterRho

/-! # Satisfiability down the quasi-tableau, and the right half of the correctness of `θ_r`

This file continues the development of `Pdl.ClusterRho` with

* Lemma 10.6: between a companion and its repeat there is a basic node,
* Lemma 10.7: if `Δ_x, ι_x` is satisfiable then so is `Δ_z, ι_z` for some `z ∈ cycs(x)`,
* Lemma 10.8: `Γ₂ ⊨ ¬θ_r`.

Definition 10.4 (the distance `d_α`) and Lemma 10.5 (its properties) are in `Pdl.Distance`,
where they are numbered 7.47. The auxiliary notions used below — the evaluation `evalQ` of
Q-formulas with an assignment, the witness distance `witDist`, and `BasicBetween` — are in
`Pdl.EvalQ`.
-/

public section

namespace PDL
/-! ## Lemma 10.6

If `x` is a repeat in `Q` then the path from `c(x)` to `x` passes through a node with a
basic label.

The proof in the paper claims that nodes of type 1 can only succeed nodes of type 3 with a
basic label; that is not the case, see Definition 9.8. What is true, and what we use here,
is that the label of a node of type 3 with a *non-basic* label strictly decreases when
passing to the children: the rule applied there is a local rule. Hence if no basic node
occurred between `c(x)` and `x` then `Δ_x` would be strictly smaller than `Δ_{c(x)}`,
contradicting `Δ_x = Δ_{c(x)}`. -/

namespace QuasiTab

/-- The possible addresses inside a node of type 1 that is not a leaf: the node itself,
its child of type 2, its grandchild of type 3, or an address inside one of the subtrees
below the node of type 3. -/
lemma atOpt_in_typeOneNode {Δ next t n}
    (h : (QNode Typ.one Δ [QNode Typ.two Δ [QNode Typ.three Δ next]]).atOpt t = some n) :
    t = [] ∨ t = [0] ∨ t = [0,0] ∨
      ∃ (i : Nat) (t' : List Nat) (hi : i < next.length),
        t = 0 :: 0 :: i :: t' ∧ next[i].atOpt t' = some n := by
  cases t with
  | nil => exact Or.inl rfl
  | cons j t2 =>
    cases j with
    | succ j => exfalso; simp [atOpt, children] at h
    | zero =>
      simp only [atOpt, children, List.getElem?_cons_zero] at h
      cases t2 with
      | nil => exact Or.inr (Or.inl rfl)
      | cons k t3 =>
        cases k with
        | succ k => exfalso; simp [atOpt, children] at h
        | zero =>
          simp only [atOpt, children, List.getElem?_cons_zero] at h
          cases t3 with
          | nil => exact Or.inr (Or.inr (Or.inl rfl))
          | cons i t4 =>
            simp only [atOpt, children] at h
            cases hi : next[i]? with
            | none => rw [hi] at h; simp at h
            | some c =>
              rw [hi] at h
              have hilt : i < next.length := by
                by_contra hcon
                rw [List.getElem?_eq_none (by omega)] at hi
                simp at hi
              refine Or.inr (Or.inr (Or.inr ⟨i, t4, hilt, rfl, ?_⟩))
              have hc : next[i] = c := by
                rwa [List.getElem?_eq_getElem hilt, Option.some.injEq] at hi
              rw [hc]
              exact h

end QuasiTab

/-! ### Helper lemmas about prefixes -/

/-- If `x` is a prefix of `c` and `c` is a prefix of `x ++ u` then `c = x ++ s` for a
scoped prefix `s` of `u`. -/
lemma prefix_sandwich {α} {x c u : List α} (h1 : x <+: c) (h2 : c <+: x ++ u) :
    ∃ s, s <+: u ∧ c = x ++ s := by
  obtain ⟨s, rfl⟩ := h1
  exact ⟨s, (List.prefix_append_right_inj x).mp h2, rfl⟩

lemma length_lt_of_mem_inits_dropLast {α} : ∀ {x z : List α},
    z ∈ x.inits.dropLast → z.length < x.length := by
  intro x
  induction x with
  | nil => intro z hz; simp [List.inits] at hz
  | cons a l ih =>
    intro z hz
    have hinits : (a :: l).inits = [] :: (l.inits.map (fun t => a :: t)) := by simp [List.inits]
    have hne : (l.inits.map (fun t => a :: t)) ≠ [] := by
      simp only [ne_eq, List.map_eq_nil_iff]
      cases l <;> simp [List.inits]
    rw [hinits, List.dropLast_cons_of_ne_nil hne, List.mem_cons] at hz
    rcases hz with rfl | hz
    · simp
    · rw [← List.map_dropLast, List.mem_map] at hz
      obtain ⟨z', hz', rfl⟩ := hz
      have := ih hz'
      simp only [List.length_cons]
      omega

/-- The addresses searched by `QuasiTab.companionOpt` are the proper prefixes. -/
lemma prefix_ne_of_mem_inits_dropLast {α} {x z : List α} (h : z ∈ x.inits.dropLast) :
    z <+: x ∧ z ≠ x := by
  have hlt := length_lt_of_mem_inits_dropLast h
  refine ⟨(List.mem_inits _ _).mp (List.dropLast_subset _ h), ?_⟩
  rintro rfl
  omega

namespace QuasiTab

/-- The companion of a repeat leaf is a proper ancestor with the same label and type 1. -/
lemma companionOpt_spec {q : QuasiTab} {z c : List Nat} (h : q.companionOpt z = some c) :
    c <+: z ∧ c ≠ z ∧ q.labelAt c = q.labelAt z ∧ q.typAt c = some Typ.one := by
  have h1 := prefix_ne_of_mem_inits_dropLast (List.mem_of_find?_eq_some h)
  have h2 := List.find?_some h
  simp only [decide_eq_true_eq] at h2
  exact ⟨h1.1, h1.2, h2.1, h2.2⟩

end QuasiTab

namespace LoadedCluster

variable {X : Sequent} {tab : Tableau .nil X} {C : LoadedCluster tab}

/-- Along the subtree of a node of type 1 the measure of the label does not increase,
unless a node of type 3 with a basic label is passed on the way. -/
lemma measure_le_or_basicBetween (C : LoadedCluster tab)
    (hm : ∀ Δ ∈ C.lambdaTwo, ¬ Δ.basic → ∀ Y ∈ C.stepOf Δ, ltSequent Y Δ) :
    ∀ (Hist : List Sequent) (Δ : Sequent) (x : List Nat),
      C.Q.atOpt x = some (QuasiTab.build C.lambdaTwo C.stepOfL Hist Δ) →
      ∀ (t : List Nat) (n : QuasiTab),
        (QuasiTab.build C.lambdaTwo C.stepOfL Hist Δ).atOpt t = some n →
        (n.label = Δ ∨ ltSequent n.label Δ) /- this was ≤ -/ ∨ C.Q.BasicBetween x (x ++ t) := by
  intro Hist Δ
  induction Hist, Δ using QuasiTab.build.induct (inC := C.lambdaTwo) with
  | case1 Hist Δ h IH =>
    intro x hx t n ht
    rw [QuasiTab.build_of_node h] at hx ht
    set next := (C.stepOfL Δ).map (fun Pi => QuasiTab.build C.lambdaTwo C.stepOfL (Δ :: Hist) Pi)
      with hnextdef
    have hx2 : C.Q.atOpt (x ++ [0]) = some (.QNode .two Δ [.QNode .three Δ next]) :=
      QuasiTab.atOpt_child hx (by simp)
    have hx3 : C.Q.atOpt (x ++ [0, 0]) = some (.QNode .three Δ next) := by
      simpa using QuasiTab.atOpt_child hx2 (i := 0) (by simp)
    rcases QuasiTab.atOpt_in_typeOneNode ht with rfl | rfl | rfl | ⟨i, t', hi, rfl, ht'⟩
    · simp only [QuasiTab.atOpt, Option.some.injEq] at ht
      subst ht
      exact Or.inl (Or.inl rfl)
    · simp only [QuasiTab.atOpt, QuasiTab.children, List.getElem?_cons_zero,
        Option.some.injEq] at ht
      subst ht
      exact Or.inl (Or.inl rfl)
    · simp only [QuasiTab.atOpt, QuasiTab.children, List.getElem?_cons_zero,
        Option.some.injEq] at ht
      subst ht
      exact Or.inl (Or.inl rfl)
    · have hilt : i < (C.stepOfL Δ).length := by simpa [hnextdef] using hi
      have hnexti :
          next[i] = QuasiTab.build C.lambdaTwo C.stepOfL (Δ :: Hist) (C.stepOfL Δ)[i] := by
        simp [hnextdef]
      have heq : x ++ [0, 0] ++ [i] ++ t' = x ++ 0 :: 0 :: i :: t' := by simp
      by_cases hb : Δ.basic
      · refine Or.inr ⟨x ++ [0, 0], Δ, List.prefix_append _ _, ⟨[i] ++ t', by simp⟩, ?_, ?_, hb⟩
        · rw [QuasiTab.typAt, hx3]; rfl
        · rw [QuasiTab.labelAt, hx3]; rfl
      · have hat : C.Q.atOpt (x ++ [0, 0] ++ [i])
            = some (QuasiTab.build C.lambdaTwo C.stepOfL (Δ :: Hist) (C.stepOfL Δ)[i]) := by
          rw [QuasiTab.atOpt_child hx3 hi, hnexti]
        have hIH := IH (C.stepOfL Δ)[i] (x ++ [0, 0] ++ [i]) hat t' n (by rwa [hnexti] at ht')
        have hstepmem : (C.stepOfL Δ)[i] ∈ C.stepOf Δ :=
          (Finset.mem_seqSort (C.stepOf Δ)).mp (List.getElem_mem hilt)
        have hlt : ltSequent (C.stepOfL Δ)[i] Δ := hm Δ h.1 hb _ hstepmem
        rcases hIH with hle | hbb
        · left
          right
          rcases hle with nlabel_def | nlabel_lt
          · rw [nlabel_def]
            exact hlt
          · -- Here we simulate the le + lt combo now, using that the DM ordering is transitive.
            exact ltSequent.trans nlabel_lt hlt
        · rw [heq] at hbb
          exact Or.inr (hbb.mono (by simp))
  | case2 Hist Δ h =>
    intro x hx t n ht
    rw [QuasiTab.build_of_leaf h] at ht
    cases t with
    | nil =>
      simp only [QuasiTab.atOpt, Option.some.injEq] at ht
      subst ht
      exact Or.inl (Or.inl rfl)
    | cons j t2 => exfalso; simp [QuasiTab.atOpt, QuasiTab.children] at ht

/-- Lemma 10.6, by induction along the construction of the quasi-tableau: if `z` is a
repeat with companion `c` then there is a node of type 3 with a basic label between `c`
and `z`. -/
lemma build_repeat_basicBetween (C : LoadedCluster tab)
    (hm : ∀ Δ ∈ C.lambdaTwo, ¬ Δ.basic → ∀ Y ∈ C.stepOf Δ, ltSequent Y Δ) :
    ∀ (Hist : List Sequent) (Δ : Sequent) (x : List Nat),
      C.Q.atOpt x = some (QuasiTab.build C.lambdaTwo C.stepOfL Hist Δ) →
      ∀ z c, x <+: z → C.Q.isRepeatLeaf z → C.Q.companionOpt z = some c → x <+: c →
        C.Q.BasicBetween c z := by
  intro Hist Δ
  induction Hist, Δ using QuasiTab.build.induct (inC := C.lambdaTwo) with
  | case1 Hist Δ h IH =>
    intro x hx z c hxz hrep hc hxc
    obtain ⟨t, rfl⟩ := hxz
    obtain ⟨hcpre, hcne, hclab, hctyp⟩ := QuasiTab.companionOpt_spec hc
    have hztyp : C.Q.typAt (x ++ t) = some Typ.one := C.Q.typAt_of_isRepeatLeaf hrep
    have hzleaf : C.Q.isLeafAt (x ++ t) := by
      simp only [QuasiTab.isRepeatLeaf, Bool.and_eq_true] at hrep
      exact hrep.1.1
    rw [QuasiTab.build_of_node h] at hx
    set next := (C.stepOfL Δ).map (fun Pi => QuasiTab.build C.lambdaTwo C.stepOfL (Δ :: Hist) Pi)
      with hnextdef
    have hx2 : C.Q.atOpt (x ++ [0]) = some (.QNode .two Δ [.QNode .three Δ next]) :=
      QuasiTab.atOpt_child hx (by simp)
    have hx3 : C.Q.atOpt (x ++ [0, 0]) = some (.QNode .three Δ next) := by
      simpa using QuasiTab.atOpt_child hx2 (i := 0) (by simp)
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (QuasiTab.isSome_atOpt_of_isLeafAt hzleaf)
    have hnt : (QuasiTab.QNode Typ.one Δ [.QNode .two Δ [.QNode .three Δ next]]).atOpt t
        = some n := by
      rw [QuasiTab.atOpt_append, hx] at hn
      simpa using hn
    rcases QuasiTab.atOpt_in_typeOneNode hnt with rfl | rfl | rfl | ⟨i, t', hi, rfl, ht'⟩
    · exfalso
      simp only [QuasiTab.isLeafAt, List.append_nil, hx, QuasiTab.children,
        List.isEmpty_cons] at hzleaf
      exact Bool.noConfusion hzleaf
    · exfalso
      rw [QuasiTab.typAt, hx2] at hztyp
      simp only [Option.map_some, Option.some.injEq, QuasiTab.typ] at hztyp
      exact absurd hztyp (by simp)
    · exfalso
      rw [QuasiTab.typAt, hx3] at hztyp
      simp only [Option.map_some, Option.some.injEq, QuasiTab.typ] at hztyp
      exact absurd hztyp (by simp)
    · have hilt : i < (C.stepOfL Δ).length := by simpa [hnextdef] using hi
      have hnexti :
          next[i] = QuasiTab.build C.lambdaTwo C.stepOfL (Δ :: Hist) (C.stepOfL Δ)[i] := by
        simp [hnextdef]
      have hxi : C.Q.atOpt (x ++ [0, 0] ++ [i])
          = some (QuasiTab.build C.lambdaTwo C.stepOfL (Δ :: Hist) (C.stepOfL Δ)[i]) := by
        rw [QuasiTab.atOpt_child hx3 hi, hnexti]
      have hprefz : x ++ [0, 0] ++ [i] <+: x ++ 0 :: 0 :: i :: t' := ⟨t', by simp⟩
      have heq : x ++ [0, 0] ++ [i] ++ t' = x ++ 0 :: 0 :: i :: t' := by simp
      by_cases hcx : c = x
      · subst hcx
        by_cases hb : Δ.basic
        · refine ⟨c ++ [0, 0], Δ, List.prefix_append _ _, ⟨[i] ++ t', by simp⟩, ?_, ?_, hb⟩
          · rw [QuasiTab.typAt, hx3]; rfl
          · rw [QuasiTab.labelAt, hx3]; rfl
        · have hlab : Δ = n.label := by
            have h1 : C.Q.labelAt c = some Δ := by rw [QuasiTab.labelAt, hx]; rfl
            have h2 : C.Q.labelAt (c ++ 0 :: 0 :: i :: t') = some n.label := by
              rw [QuasiTab.labelAt, hn]; rfl
            rw [h1, h2] at hclab
            exact Option.some.inj hclab
          have hstep := C.measure_le_or_basicBetween hm (Δ :: Hist) (C.stepOfL Δ)[i]
            (c ++ [0, 0] ++ [i]) hxi t' n (by rwa [hnexti] at ht')
          rcases hstep with hle | hbb
          · exfalso
            -- contradiction, `ltSequent` is irreflexive.
            have hstepmem : (C.stepOfL Δ)[i] ∈ C.stepOf Δ :=
              (Finset.mem_seqSort (C.stepOf Δ)).mp (List.getElem_mem hilt)
            have hlt : ltSequent (C.stepOfL Δ)[i] Δ := hm Δ h.1 hb _ hstepmem
            rw [← hlab] at hle
            have hself : ltSequent Δ Δ := by
              rcases hle with delta_def | delta_lt_step
              · rw [← delta_def] at hlt
                exact hlt
              · exact ltSequent.trans delta_lt_step hlt
            exact instIsWellFoundedSequentLt.asymmetric _ _ hself hself
          · rw [heq] at hbb
            exact hbb.mono (by simp)
      · obtain ⟨s, hs, rfl⟩ := prefix_sandwich hxc hcpre
        have hsne : s ≠ [] := by rintro rfl; exact hcx (by simp)
        have hs3 : [0, 0, i] <+: s := by
          rcases s with _ | ⟨j, s1⟩
          · exact absurd rfl hsne
          · have hj : j = 0 := by
              have := hs.getElem (i := 0) (by simp)
              simpa using this
            subst hj
            rcases s1 with _ | ⟨k, s2⟩
            · exfalso
              rw [QuasiTab.typAt, hx2] at hctyp
              simp only [Option.map_some, Option.some.injEq, QuasiTab.typ] at hctyp
              exact absurd hctyp (by simp)
            · have hk : k = 0 := by
                have := hs.getElem (i := 1) (by simp)
                simpa using this
              subst hk
              rcases s2 with _ | ⟨l, s3⟩
              · exfalso
                rw [QuasiTab.typAt, hx3] at hctyp
                simp only [Option.map_some, Option.some.injEq, QuasiTab.typ] at hctyp
                exact absurd hctyp (by simp)
              · have hl : l = i := by
                  have := hs.getElem (i := 2) (by simp)
                  simpa using this
                subst hl
                exact ⟨s3, by simp⟩
        obtain ⟨s', rfl⟩ := hs3
        refine IH (C.stepOfL Δ)[i] (x ++ [0, 0] ++ [i]) hxi (x ++ 0 :: 0 :: i :: t')
          (x ++ ([0, 0, i] ++ s')) hprefz hrep hc ⟨s', by simp⟩
  | case2 Hist Δ h =>
    intro x hx z c hxz hrep hc hxc
    exfalso
    obtain ⟨t, rfl⟩ := hxz
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (QuasiTab.isSome_atOpt_of_isLeafAt (by
      simp only [QuasiTab.isRepeatLeaf, Bool.and_eq_true] at hrep
      exact hrep.1.1))
    rw [QuasiTab.atOpt_append, hx, QuasiTab.build_of_leaf h] at hn
    have ht : t = [] := by
      cases t with
      | nil => rfl
      | cons j t2 =>
        exfalso
        simp only [Option.bind_some, QuasiTab.atOpt, QuasiTab.children,
          List.getElem?_nil] at hn
        exact absurd hn (by simp)
    subst ht
    obtain ⟨hcpre, hcne, -, -⟩ := QuasiTab.companionOpt_spec hc
    refine hcne ?_
    have hxeq : x = c :=
      hxc.eq_of_length (le_antisymm hxc.length_le (by simpa using hcpre.length_le))
    simp [← hxeq]

/-- **Lemma 10.6**: if `z` is a repeat in `Q` with companion `c(z)`, then the path from
`c(z)` to `z` passes through a node of type 3 whose label is basic.

The proof in the paper argues that a repeat is of type 1, and that in `Q` a node of type 1
can only succeed a node of type 3 with a basic label. In the construction of `Q`
(Definition 9.8) the children of a node of type 3 are of type 1 also when the label is
*not* basic, so that argument does not apply directly. We use instead that the labels of
the successors of a non-basic node are smaller in some measure `m`, so a repeat — which
has the *same* label as its companion — cannot be reached from its companion by non-basic
steps only. -/
theorem repeat_basicBetween (C : LoadedCluster tab)
    (hm : ∀ Δ ∈ C.lambdaTwo, ¬ Δ.basic → ∀ Y ∈ C.stepOf Δ, ltSequent Y Δ)
    {z c : List Nat} (hz : C.Q.isRepeatLeaf z) (hc : C.Q.companionOpt z = some c) :
    C.Q.BasicBetween c z :=
  C.build_repeat_basicBetween hm [] (nodeAt C.root).rightOnly [] rfl z c
    (List.nil_prefix) hz hc (List.nil_prefix)


/-! ## Assumptions about the steps of the quasi-tableau

Just like `LoadedCluster.PaperFacts` for Lemma 10.3, the proof of Lemma 10.7 uses facts
about the tableau `tab` and the sequents `Λ₂[C]` that are not (yet) available in this Lean
development. They are collected here in one record. -/

/-- Facts about the cluster `C` used in the proof of Lemma 10.7.

* `rightLoaded` says that all `Δ ∈ Λ₂[C]` carry their loaded formula on the right; this is
  the standing assumption of Section 9 that `Γ₂` is the loaded side.
* `stepLT` provides a decreasing measure needed for Lemma 10.6 (`repeat_basicBetween`).
  A local rule applied to an unloaded formula, or the rule `(◇)₂` applied to the loaded
  formula, strictly decreases the DM ordering on sequents.
* `basicStep` describes the modal step at a basic `Δ ∈ Λ₂[C]`: there is exactly one
  successor sequent `Y`, obtained by projecting along the leading atomic program `a` of
  the loaded formula and dropping `a` from it.
* `nonBasicStep` describes the local step at a non-basic `Δ ∈ Λ₂[C]`: whenever `Δ` holds at
  a state, one of the successor sequents holds at the same state, with the same witness
  distance. In the paper this is proved by a case distinction on whether the rule was
  applied to an unloaded formula (local invertibility) or to the loaded formula (in which
  case it is Lemma 10.5(h), `existsD_of_true_diamond`). -/
structure SatDownFacts (C : LoadedCluster tab) : Prop where
  /-- All sequents of `Λ₂[C]` have their loaded formula on the right. -/
  rightLoaded : ∀ Δ ∈ C.lambdaTwo, Δ.isRightLoaded
  /-- The DM measure strictly decreases at the non-basic steps of the quasi-tableau. -/
  stepLT : ∀ Δ ∈ C.lambdaTwo, ¬ Δ.basic → ∀ Y ∈ C.stepOf Δ, ltSequent Y Δ
  /-- The modal step at a basic sequent. -/
  basicStep : ∀ Δ ∈ C.lambdaTwo, Δ.basic → ∃ (A : Nat) (Y : Sequent),
    C.stepOf Δ = {Y}
    ∧ Δ.loadedProg = (·A : Program)
    ∧ Δ.loadedProgs = (·A : Program) :: Y.loadedProgs
    ∧ Y.loadedFma = Δ.loadedFma
    ∧ ∀ (W : Type) (M : KripkeModel W) (w v : W), (∀ φ ∈ Δ.right, evaluate M w φ) →
        relate M (·A : Program) w v → evaluate M v (~⌈⌈Y.loadedProgs⌉⌉Y.loadedFma) →
        ∀ φ ∈ Y.right, evaluate M v φ
  /-- The local step at a non-basic sequent. -/
  nonBasicStep : ∀ Δ ∈ C.lambdaTwo, ¬ Δ.basic → ∀ (W : Type) (M : KripkeModel W) (v : W),
    (∀ φ ∈ Δ.right, evaluate M v φ) →
    ∃ i, ∃ hi : i < (C.stepOfL Δ).length,
      (∀ φ ∈ ((C.stepOfL Δ)[i]'hi).right, evaluate M v φ)
      ∧ witDist M v ((C.stepOfL Δ)[i]'hi) = witDist M v Δ

/-! ## The claim in the proof of Lemma 10.7 -/

/-- The Claim in the proof of Lemma 10.7, for the node `x` of the quasi-tableau: whenever
`Δ_x, ι_x` is satisfied at a state `v`, there is a repeat leaf `z ∈ cycs(x)` and a state
`u` satisfying `Δ_z, ι_z` with a witness distance that is not larger, and that is strictly
smaller if there is a basic node between `x` and `z`.

The internal variables of the pre-interpolants are interpreted by an assignment `g`; see
the module docstring. -/
def SatDown (C : LoadedCluster tab) (θ : FinePathIn tab → Formula) (x : List Nat) : Prop :=
  ∀ (W : Type) (M : KripkeModel W) (g : List Nat → W → Prop) (v : W) (Δ : Sequent),
    C.Q.labelAt x = some Δ → (∀ φ ∈ Δ.right, evaluate M v φ) →
    QFormula.evalQ M g v (C.iitp θ x) →
    ∃ z ∈ C.Q.cycs x, ∃ (Z : Sequent) (u : W),
      C.Q.labelAt z = some Z ∧ (∀ φ ∈ Z.right, evaluate M u φ) ∧
      QFormula.evalQ M g u (C.iitp θ z) ∧
      witDist M u Z ≤ witDist M v Δ ∧
      (C.Q.BasicBetween x z → witDist M u Z < witDist M v Δ)


/-! ### The cases of the proof of the Claim -/

/-- Case `k(x) = 1` where `x` is a repeat leaf: take `z := x` and `u := v`. -/
lemma satDown_one_leaf_repeat {Δ c} (hx : C.Q.atOpt x = some (.QNode .one Δ []))
    (hc : C.Q.companionOpt x = some c) : C.SatDown θ x := by
  intro W M g v Z hlab hZ hι
  have hrep : C.Q.isRepeatLeaf x := by
    simp [QuasiTab.isRepeatLeaf, QuasiTab.isLeafAt_of_atOpt hx, QuasiTab.typAt, hx,
      QuasiTab.typ, hc]
  refine ⟨x, QuasiTab.mem_cycs_self hrep, Z, v, hlab, hZ, hι, le_refl _, ?_⟩
  rintro ⟨y, Y, h1, h2, h3, -, -⟩
  exfalso
  have hyx : x = y := h1.eq_of_length (le_antisymm h1.length_le h2.length_le)
  subst hyx
  rw [QuasiTab.typAt, hx] at h3
  simp [QuasiTab.typ] at h3

/-- Case `k(x) = 1` where `x` is a leaf that is not a repeat: here `ι_x = θ_{Δ_x}` and the
sequent `Δ_x, ι_x` is unsatisfiable by Lemma 9.14 (b), so the claim is vacuous. -/
lemma satDown_one_leaf_exit {Δ} (hx : C.Q.atOpt x = some (.QNode .one Δ []))
    (hc : C.Q.companionOpt x = none)
    (hθ : ∀ f ∈ C.fineExits, isPartInterpolant f.label (θ f)) : C.SatDown θ x := by
  intro W M g v Z hlab hZ hι
  exfalso
  have hZeq : Δ = Z := by rw [QuasiTab.labelAt, hx] at hlab; simpa using! hlab
  subst hZeq
  rw [C.iitp_one_leaf_exit hx hc, QFormula.evalQ_fma] at hι
  refine C.thetaOf_right θ hθ Δ ⟨W, M, v, ?_⟩
  intro φ hφ
  rcases Finset.mem_union.mp hφ with h | hmem
  · rw [Finset.mem_singleton.mp h]
    exact hι
  · exact hZ φ hmem

/-- Case `k(x) = 1` where `x` is neither a leaf nor a companion: `ι_x = ι_y` and
`Δ_x = Δ_y` for the unique child `y`, and `cycs(x) = cycs(y)`. -/
lemma satDown_one_inner {Δ y ys} (hx : C.Q.atOpt x = some (.QNode .one Δ (y :: ys)))
    (hcomp : x ∉ C.Q.companions) (hylab : C.Q.labelAt (x ++ [0]) = some Δ)
    (IH : C.SatDown θ (x ++ [0])) : C.SatDown θ x := by
  intro W M g v Z hlab hZ hι
  have hZeq : Δ = Z := by rw [QuasiTab.labelAt, hx] at hlab; simpa using! hlab
  subst hZeq
  rw [C.iitp_one_inner hx hcomp] at hι
  obtain ⟨z, hz, Y, u, h1, h2, h3, h4, h5⟩ := IH W M g v Δ hylab hZ hι
  refine ⟨z, QuasiTab.cycs_subset_of_qedge _ hcomp (QuasiTab.qedge_snoc hx (by simp)) z hz,
    Y, u, h1, h2, h3, h4, fun hbb => h5 (hbb.child (QuasiTab.prefix_of_mem_cycs hz) (by simp)
      (QuasiTab.notBasic_of_typ_ne hx (by simp)))⟩

/-- Case `k(x) = 2`: `ι_x = [¬θ_Δ?]ι_y`, and `Δ, θ_Δ` is unsatisfiable by Lemma 9.14 (b),
so `ι_y` holds at the same state. -/
lemma satDown_two {Δ y ys} (hx : C.Q.atOpt x = some (.QNode .two Δ (y :: ys)))
    (hylab : C.Q.labelAt (x ++ [0]) = some Δ)
    (hθ : ∀ f ∈ C.fineExits, isPartInterpolant f.label (θ f))
    (IH : C.SatDown θ (x ++ [0])) : C.SatDown θ x := by
  intro W M g v Z hlab hZ hι
  have hZeq : Δ = Z := by rw [QuasiTab.labelAt, hx] at hlab; simpa using! hlab
  subst hZeq
  have hcomp : x ∉ C.Q.companions := by
    intro hcon
    have := C.Q.typAt_of_mem_companions hcon
    rw [QuasiTab.typAt, hx] at this
    simp [QuasiTab.typ] at this
  have hnegθ : ¬ evaluate M v (C.thetaOf θ Δ) := by
    intro hcon
    refine C.thetaOf_right θ hθ Δ ⟨W, M, v, ?_⟩
    intro φ hφ
    rcases Finset.mem_union.mp hφ with h | hmem
    · rw [Finset.mem_singleton.mp h]
      exact hcon
    · exact hZ φ hmem
  rw [C.iitp_two hx, QFormula.evalQ_boxes] at hι
  have hι' : QFormula.evalQ M g v (C.iitp θ (x ++ [0])) := by
    refine hι v ?_
    rw [relateSeq_singleton]
    exact ⟨rfl, hnegθ⟩
  obtain ⟨z, hz, Y, u, h1, h2, h3, h4, h5⟩ := IH W M g v Δ hylab hZ hι'
  refine ⟨z, QuasiTab.cycs_subset_of_qedge _ hcomp (QuasiTab.qedge_snoc hx (by simp)) z hz,
    Y, u, h1, h2, h3, h4, fun hbb => h5 (hbb.child (QuasiTab.prefix_of_mem_cycs hz) (by simp)
      (QuasiTab.notBasic_of_typ_ne hx (by simp)))⟩

/-- Case `k(x) = 3` with `Δ_x` basic: the loaded formula is `¬⌊a γs⌋ψ` with `a` atomic and
`ι_x = [a]ι_y`. Going to a state `v'` at minimal witness distance decreases the witness
distance by exactly one. -/
lemma satDown_three_basic {Δ Y y ys} (hS : C.SatDownFacts) (hΔ : Δ ∈ C.lambdaTwo)
    (hb : Δ.basic) (hx : C.Q.atOpt x = some (.QNode .three Δ (y :: ys)))
    (hstep : C.stepOf Δ = {Y}) (hylab : C.Q.labelAt (x ++ [0]) = some Y)
    (IH : C.SatDown θ (x ++ [0])) : C.SatDown θ x := by
  intro W M g v Z hxlab hZ hι
  have hZeq : Δ = Z := by rw [QuasiTab.labelAt, hx] at hxlab; simpa using! hxlab
  subst hZeq
  have hcomp : x ∉ C.Q.companions := by
    intro hcon
    have := C.Q.typAt_of_mem_companions hcon
    rw [QuasiTab.typAt, hx] at this
    simp [QuasiTab.typ] at this
  obtain ⟨A, Y', hstep', hprog, hprogs, hfma, hproj⟩ := hS.basicStep Δ hΔ hb
  have hYY : Y' = Y := by rw [hstep] at hstep'; simp at hstep'; exact hstep'.symm
  rw [hYY] at hprogs hfma hproj
  -- the loaded formula `¬⌈⌈a γs⌉⌉ψ` holds at `v`
  have hloaded : evaluate M v (~⌈⌈Δ.loadedProgs⌉⌉Δ.loadedFma) :=
    hZ _ (Sequent.negBoxes_mem_right (hS.rightLoaded Δ hΔ))
  simp only [evaluate] at hloaded
  rw [evalBoxes] at hloaded
  push Not at hloaded
  obtain ⟨w1, hw1rel, hw1⟩ := hloaded
  -- a state `w0` at minimal witness distance
  have hne : Nonempty {w : W // evaluate M w (~ Δ.loadedFma)} := ⟨⟨w1, hw1⟩⟩
  obtain ⟨w0, hw0⟩ := @iInf_exists_eq {w : W // evaluate M w (~ Δ.loadedFma)} hne
    (fun w => distanceList M v w Δ.loadedProgs)
  have hwd : witDist M v Δ = distanceList M v (w0 : W) Δ.loadedProgs := hw0
  have hfin : distanceList M v (w0 : W) Δ.loadedProgs ≠ ⊤ := by
    have hle : distanceList M v (w0 : W) Δ.loadedProgs
        ≤ distanceList M v w1 Δ.loadedProgs :=
      hw0.symm.trans_le (iInf_le (fun w : {w : W // evaluate M w (~ Δ.loadedFma)} =>
        distanceList M v w Δ.loadedProgs) ⟨w1, hw1⟩)
    have hne1 : distanceList M v w1 Δ.loadedProgs ≠ ⊤ :=
      distance_list_iff_relate_Seq.mpr hw1rel
    intro hcon
    rw [hcon, top_le_iff] at hle
    exact hne1 hle
  have hrelseq : relateSeq M Δ.loadedProgs v (w0 : W) := distance_list_iff_relate_Seq.mp hfin
  rw [hprogs] at hrelseq
  obtain ⟨v', hAv', hgam, hsplit⟩ := exists_same_distance_of_relateSeq_cons hrelseq
  have hd : distanceList M v' (w0 : W) Y.loadedProgs ≠ ⊤ :=
    distance_list_iff_relate_Seq.mpr hgam
  have hone : distance M (·A : Program) v v' = 1 := by
    simp only [distance, ite_eq_left hAv']
  have hw0Y : evaluate M (w0 : W) (~ Y.loadedFma) := by rw [hfma]; exact w0.2
  have hwdY : witDist M v' Y ≤ distanceList M v' (w0 : W) Y.loadedProgs :=
    iInf_le (fun w : {w : W // evaluate M w (~ Y.loadedFma)} =>
      distanceList M v' w Y.loadedProgs) ⟨(w0 : W), hw0Y⟩
  have hlt : witDist M v' Y < witDist M v Δ := by
    refine lt_of_le_of_lt hwdY ?_
    rw [hwd, hprogs, hsplit, hone]
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hd
    rw [← hn]
    exact_mod_cast (by omega : n < 1 + n)
  -- the loaded formula of the child holds at `v'`
  have hYloaded : evaluate M v' (~⌈⌈Y.loadedProgs⌉⌉Y.loadedFma) := by
    simp only [evaluate]
    rw [evalBoxes]
    push Not
    exact ⟨(w0 : W), hgam, hw0Y⟩
  have hYright : ∀ φ ∈ Y.right, evaluate M v' φ := hproj W M v v' hZ hAv' hYloaded
  rw [C.iitp_three_basic hx hb, QFormula.evalQ_boxes] at hι
  have hiy : QFormula.evalQ M g v' (C.iitp θ (x ++ [0])) := by
    refine hι v' ?_
    rw [relateSeq_singleton, hprog]
    exact hAv'
  obtain ⟨z, hz, Z', u, h1, h2, h3, h4, -⟩ := IH W M g v' Y hylab hYright hiy
  exact ⟨z, QuasiTab.cycs_subset_of_qedge _ hcomp (QuasiTab.qedge_snoc hx (by simp)) z hz,
    Z', u, h1, h2, h3, le_of_lt (lt_of_le_of_lt h4 hlt), fun _ => lt_of_le_of_lt h4 hlt⟩

/-- Case `k(x) = 3` with `Δ_x` not basic: `ι_x = ⋀ᵢ ι_{y_i}` and by `SatDownFacts.nonBasicStep`
one of the children holds at the same state with the same witness distance. -/
lemma satDown_three_not_basic {Δ next} (hS : C.SatDownFacts) (hΔ : Δ ∈ C.lambdaTwo)
    (hb : ¬ Δ.basic) (hx : C.Q.atOpt x = some (.QNode .three Δ next))
    (hlen : next.length = (C.stepOfL Δ).length)
    (hlab : ∀ i, (hi : i < (C.stepOfL Δ).length) →
      C.Q.labelAt (x ++ [i]) = some ((C.stepOfL Δ)[i]'hi))
    (IH : ∀ i, i < next.length → C.SatDown θ (x ++ [i])) : C.SatDown θ x := by
  intro W M g v Z hxlab hZ hι
  have hZeq : Δ = Z := by rw [QuasiTab.labelAt, hx] at hxlab; simpa using! hxlab
  subst hZeq
  have hcomp : x ∉ C.Q.companions := by
    intro hcon
    have := C.Q.typAt_of_mem_companions hcon
    rw [QuasiTab.typAt, hx] at this
    simp [QuasiTab.typ] at this
  obtain ⟨i, hi, hright, hwd⟩ := hS.nonBasicStep Δ hΔ hb W M v hZ
  have hi' : i < next.length := by omega
  rw [C.iitp_three_not_basic hx hb, QFormula.evalQ_conj] at hι
  have hii : QFormula.evalQ M g v (C.iitp θ (x ++ [i])) := by
    refine hι _ ?_
    rw [← C.iitpList_getElem_eq_iitp hx hi']
    exact List.getElem_mem _
  obtain ⟨z, hz, Y, u, h1, h2, h3, h4, h5⟩ :=
    IH i hi' W M g v _ (hlab i hi) hright hii
  refine ⟨z, QuasiTab.cycs_subset_of_qedge _ hcomp (QuasiTab.qedge_snoc hx hi') z hz,
    Y, u, h1, h2, h3, hwd ▸ h4, fun hbb => hwd ▸ h5 (hbb.child
      (QuasiTab.prefix_of_mem_cycs hz) (by simp) (QuasiTab.notBasic_of_label hx hb))⟩

/-- Case `k(x) = 1` where `x` is a companion: `ι_x = gfp x ι_y`. Reinterpreting the
internal variable `q_x` by `ι_x` turns `ι_x` into `ι_y`, and a repeat `z ∈ cycs(y)` whose
companion is `x` itself sends us back to `x`, but with a strictly smaller witness distance
by Lemma 10.6, so the secondary induction applies. -/
lemma satDown_one_companion {Δ y ys} (hS : C.SatDownFacts)
    (hx : C.Q.atOpt x = some (.QNode .one Δ (y :: ys))) (hcomp : x ∈ C.Q.companions)
    (hylab : C.Q.labelAt (x ++ [0]) = some Δ)
    (IH : C.SatDown θ (x ++ [0])) : C.SatDown θ x := by
  obtain hm := hS.stepLT
  have hiitpx : C.iitp θ x = (C.iitp θ (x ++ [0])).gfp x := C.iitp_one_companion hx hcomp
  have hxl : C.Q.labelAt x = some Δ := by rw [QuasiTab.labelAt, hx]; rfl
  intro W M g
  have key : ∀ n : ℕ∞, ∀ v : W, witDist M v Δ = n →
      (∀ φ ∈ Δ.right, evaluate M v φ) → QFormula.evalQ M g v (C.iitp θ x) →
      ∃ z ∈ C.Q.cycs x, ∃ (Z : Sequent) (u : W),
        C.Q.labelAt z = some Z ∧ (∀ φ ∈ Z.right, evaluate M u φ) ∧
        QFormula.evalQ M g u (C.iitp θ z) ∧
        witDist M u Z ≤ witDist M v Δ ∧
        (C.Q.BasicBetween x z → witDist M u Z < witDist M v Δ) := by
    intro n
    induction n using WellFoundedLT.induction with
    | _ n ihn =>
      intro v hn hZ hι
      have hgfp : QFormula.evalQ M g v ((C.iitp θ (x ++ [0])).gfp x) := hiitpx ▸ hι
      have hchild := QFormula.evalQ_gfp_unfold (C.iitp θ (x ++ [0])) hgfp
      obtain ⟨z, hz, Z', u, hzlab, hzright, hzi, hle, hstrict⟩ :=
        IH W M _ v Δ hylab hZ hchild
      obtain ⟨hzrepl, c, hc, -, -⟩ := (C.Q.mem_cycs_iff _ _).mp hz
      have hzrep : C.Q.isRepeatLeaf z := by
        simp only [QuasiTab.repeatLeaves, List.mem_filter] at hzrepl
        exact hzrepl.2
      obtain ⟨Z'', hzat⟩ := QuasiTab.atOpt_of_isRepeatLeaf hzrep
      have hZeq : Z'' = Z' := by rw [QuasiTab.labelAt, hzat] at hzlab; simpa using! hzlab
      subst hZeq
      have hzitp : C.iitp θ z = .var c := C.iitp_one_leaf_repeat hzat hc
      by_cases hcx : c = x
      · -- the companion of `z` is `x` itself: apply the secondary induction hypothesis
        rw [hcx] at hc hzitp
        have hZΔ : Z'' = Δ := by
          obtain ⟨-, -, hclab, -⟩ := QuasiTab.companionOpt_spec hc
          rw [hxl, hzlab] at hclab
          exact (Option.some.inj hclab).symm
        subst hZΔ
        have hlt : witDist M u Z'' < witDist M v Z'' :=
          hstrict ((C.repeat_basicBetween hm hzrep hc).child
            (QuasiTab.prefix_of_mem_cycs hz) (by simp)
            (QuasiTab.notBasic_of_typ_ne hx (by simp)))
        have hui : QFormula.evalQ M g u (C.iitp θ x) := by
          rw [hzitp, QFormula.evalQ_var, Function.update_self] at hzi
          rw [hiitpx]
          exact hzi
        obtain ⟨z', hz', Z2, u2, h1, h2, h3, h4, -⟩ :=
          ihn (witDist M u Z'') (hn ▸ hlt) u rfl hzright hui
        exact ⟨z', hz', Z2, u2, h1, h2, h3, le_of_lt (lt_of_le_of_lt h4 hlt),
          fun _ => lt_of_le_of_lt h4 hlt⟩
      · -- the companion of `z` is a proper ancestor of `x`, so `z ∈ cycs(x)`
        have hzcycs : z ∈ C.Q.cycs x :=
          C.Q.mem_cycs_of_qedge_of_companion_ne (QuasiTab.qedge_snoc hx (by simp)) hz
            (by rw [hc]; simpa using hcx)
        refine ⟨z, hzcycs, Z'', u, hzlab, hzright, ?_, hle, ?_⟩
        · rw [hzitp, QFormula.evalQ_var]
          rw [hzitp, QFormula.evalQ_var, Function.update_of_ne hcx] at hzi
          exact hzi
        · intro hbb
          exact hstrict (hbb.child (QuasiTab.prefix_of_mem_cycs hz) (by simp)
            (QuasiTab.notBasic_of_typ_ne hx (by simp)))
  intro v Z hxlab hZ hι
  have hZeq : Δ = Z := by rw [hxl] at hxlab; simpa using hxlab
  subst hZeq
  exact key (witDist M v Δ) v rfl hZ hι

/-! ### The Claim for all nodes of the quasi-tableau -/

/-- The Claim in the proof of Lemma 10.7, for all nodes of the quasi-tableau, by
leaf-to-root induction along the construction of `Q` (Definition 9.8). -/
lemma satDown_build (C : LoadedCluster tab) (hS : C.SatDownFacts)
    (hθ : ∀ f ∈ C.fineExits, isPartInterpolant f.label (θ f)) :
    ∀ (Hist : List Sequent) (Δ : Sequent) (x : List Nat),
      C.Q.atOpt x = some (QuasiTab.build C.lambdaTwo C.stepOfL Hist Δ) →
      C.SatDown θ x := by
  intro Hist Δ
  induction Hist, Δ using QuasiTab.build.induct (inC := C.lambdaTwo) with
  | case1 Hist Δ h IH =>
    intro x hx
    rw [QuasiTab.build_of_node h] at hx
    set next := (C.stepOfL Δ).map (fun Pi => QuasiTab.build C.lambdaTwo C.stepOfL (Δ :: Hist) Pi)
      with hnextdef
    have h2 : C.Q.atOpt (x ++ [0]) = some (.QNode .two Δ [.QNode .three Δ next]) :=
      QuasiTab.atOpt_child hx (by simp)
    have h3 : C.Q.atOpt ((x ++ [0]) ++ [0]) = some (.QNode .three Δ next) :=
      QuasiTab.atOpt_child h2 (by simp)
    have hlab2 : C.Q.labelAt (x ++ [0]) = some Δ := by rw [QuasiTab.labelAt, h2]; rfl
    have hlab3 : C.Q.labelAt ((x ++ [0]) ++ [0]) = some Δ := by rw [QuasiTab.labelAt, h3]; rfl
    have hlen : next.length = (C.stepOfL Δ).length := by simp [hnextdef]
    have hchildlab : ∀ i, (hi : i < (C.stepOfL Δ).length) →
        C.Q.labelAt ((x ++ [0]) ++ [0] ++ [i]) = some ((C.stepOfL Δ)[i]'hi) := by
      intro i hi
      rw [QuasiTab.labelAt, QuasiTab.atOpt_child h3 (by omega)]
      simp [hnextdef]
    have IHchild : ∀ i, i < next.length → C.SatDown θ ((x ++ [0]) ++ [0] ++ [i]) := by
      intro i hi
      have hi' : i < (C.stepOfL Δ).length := by omega
      have hat : C.Q.atOpt ((x ++ [0]) ++ [0] ++ [i])
          = some (QuasiTab.build C.lambdaTwo C.stepOfL (Δ :: Hist) (C.stepOfL Δ)[i]) := by
        rw [QuasiTab.atOpt_child h3 hi]
        simp [hnextdef]
      exact IH (C.stepOfL Δ)[i] _ hat
    have h3sat : C.SatDown θ ((x ++ [0]) ++ [0]) := by
      by_cases hb : Δ.basic
      · obtain ⟨A, Y, hstep, -⟩ := hS.basicStep Δ h.1 hb
        have hstepL : C.stepOfL Δ = [Y] := by
          simp [stepOfL, hstep, Finset.pdlSeqSort]
        have hnextcons : next = [QuasiTab.build C.lambdaTwo C.stepOfL (Δ :: Hist) Y] := by
          rw [hnextdef, hstepL]
          simp
        refine C.satDown_three_basic hS h.1 hb (hnextcons ▸ h3) hstep ?_
          (IHchild 0 (by rw [hnextcons]; simp))
        have h0 : (0 : Nat) < (C.stepOfL Δ).length := by rw [hstepL]; simp
        rw [hchildlab 0 h0]
        simp [hstepL]
      · exact C.satDown_three_not_basic hS h.1 hb h3 hlen hchildlab IHchild
    have h2sat : C.SatDown θ (x ++ [0]) := C.satDown_two h2 hlab3 hθ h3sat
    by_cases hcomp : x ∈ C.Q.companions
    · exact C.satDown_one_companion hS hx hcomp hlab2 h2sat
    · exact C.satDown_one_inner hx hcomp hlab2 h2sat
  | case2 Hist Δ h =>
    intro x hx
    rw [QuasiTab.build_of_leaf h] at hx
    cases hc : C.Q.companionOpt x with
    | some c => exact C.satDown_one_leaf_repeat hx hc
    | none => exact C.satDown_one_leaf_exit hx hc hθ

/-- **Lemma 10.7** at the root of the quasi-tableau. -/
theorem satDown_root (C : LoadedCluster tab) (hS : C.SatDownFacts)
    (hθ : ∀ f ∈ C.fineExits, isPartInterpolant f.label (θ f)) :
    C.SatDown θ QuasiTab.rootAddress :=
  C.satDown_build hS hθ [] (nodeAt C.root).rightOnly QuasiTab.rootAddress rfl

/-! ## Lemma 10.8 -/

open HasSat in
/-- **Lemma 10.8**: `Γ₂ ⊨ ¬θ_r`, i.e. the right component of the root of the cluster
together with the interpolant of Definition 9.20 is unsatisfiable.

The hypothesis `Γ₁ ≠ ∅` is the one of Definition 9.20: for `Γ₁ = ∅` we have `θ_r = ⊤` by
Remark 9.19, and then the statement would say that `Γ₂` itself is unsatisfiable. -/
theorem right_unsat_itp (C : LoadedCluster tab) (hS : C.SatDownFacts)
    (hθ : ∀ f ∈ C.fineExits, isPartInterpolant f.label (θ f))
    (hΓ₁ : (nodeAt C.root).left ≠ {}) :
    ¬ satisfiable ({C.itp θ} ∪ (nodeAt C.root).right) := by
  rintro ⟨W, M, w, hw⟩
  have hitp : evaluate M w (C.itp θ) := hw _ (by simp_all)
  have hright : ∀ φ ∈ (nodeAt C.root).right, evaluate M w φ :=
    fun φ hφ => hw φ (by simp_all)
  rw [itp, ite_eq_right hΓ₁] at hitp
  have hev : QFormula.evalQ M (fun _ u => evaluate M u (⊤ : Formula)) w (C.rootIitp θ) :=
    (QFormula.evalQ_iff_evaluate_subst (C.rootIitp θ) w).mpr hitp
  have hroot : C.Q.atOpt QuasiTab.rootAddress = some C.Q := rfl
  have hlab : C.Q.labelAt QuasiTab.rootAddress = some (nodeAt C.root).rightOnly := by
    simp [QuasiTab.labelAt, hroot]
  obtain ⟨z, hz, -⟩ := C.satDown_root hS hθ W M _ w (nodeAt C.root).rightOnly hlab
    hright hev
  rw [C.Q.cycs_root] at hz
  exact absurd hz (List.not_mem_nil)

end LoadedCluster

end PDL
