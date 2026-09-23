/-
Copyright (c) 2023 PDL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDL formalization contributors (see project card)
-/

module

public import Mathlib.Data.ENat.Lattice

public import LeanPool.PDL.Local.UnfoldDia

/-! # Distance between states in a Kripke model

In the article these are used for the correctness of cluster interpolants in Section 7.
Here we also use them to state and prove `localLoadedDiamondList`, a local version
of the `loadedDiamondPaths` lemma that is part of the Soundness proof in Section 6.
-/

@[expose] public section

namespace PDL

/-! ## Walks -/

/-- A finite program walk whose recorded edges change the world. -/
inductive Walk : KripkeModel W → Program → W → W → Type
| nil a : Walk M a w w
| cons (h : relate M α w x) (p : Walk M α x v) (wx : w ≠ x) : Walk M α w v

open Classical in
/-- Prepend a program step, omitting it when its endpoints coincide. -/
noncomputable def Walk.cons' (h : relate M α w x) (p : Walk M α x v) : Walk M α w v :=
  if c : w = x then match c with | .refl _ => p else .cons h p c

variable {M : KripkeModel W}

/-- Sum natural-valued edge weights along a walk. -/
def Walk.flength' : Walk M α w v → (W → W → ℕ) → ℕ
| .nil α, _ => 0
| .cons (w := w) (x := x) _ p _, f => f w x + p.flength' f

/-- Sum possibly infinite edge weights along a walk. -/
def Walk.flength : Walk M α w v → (W → W → ℕ∞) → ℕ∞
| .nil α, _ => 0
| .cons (w := w) (x := x) _ p _, f => f w x + p.flength f

attribute [refl] Walk.nil

/-- Concatenate two program walks with a shared endpoint. -/
def Walk.append {M : KripkeModel W} {w v x : W} : Walk M α w x → Walk M α x v → Walk M α w v
  | .nil α, q => q
  | .cons h p wx, q => .cons h (p.append q) wx

/-- The infimum of natural-weighted lengths of program walks. -/
noncomputable def fdist' (M : KripkeModel W) (α : Program) (w v : W) (f : W → W → ℕ) : ℕ∞ :=
  ⨅ (p : Walk M α w v), p.flength' f

/-- The infimum of possibly infinite weighted lengths of program walks. -/
noncomputable def fdist (M : KripkeModel W) (α : Program) (w v : W) (f : W → W → ℕ∞) : ℕ∞ :=
  ⨅ (p : Walk M α w v), p.flength f

theorem fdist_cast (h : ∀ {x y} (_ : relate M α x y), f x y ≠ ⊤) :
    fdist M α w v f = fdist' M α w v (ENat.toNat <| f · ·) :=
  iInf_congr fun p => by induction p with
  | nil => rfl
  | cons r _ _ IH => calc
    _ = _ := congr_arg₂ _ (ENat.natCast_toNat <| h r).symm <| IH h
    _ = _ := (ENat.natCast_add _ _).symm

/-- Existence of a finite program walk between two worlds. -/
def Reachable (M : KripkeModel W) (α : Program) (w v : W) : Prop := Nonempty (Walk M α w v)

@[refl]
protected theorem Reachable.refl (w : W) : Reachable M α w w := ⟨.nil α⟩

@[trans]
protected theorem Reachable.trans {w v u : W} (hwv : Reachable M α w v) (hvu : Reachable M α v u) :
    Reachable M α w u :=
  hwv.elim fun pwv => hvu.elim fun pvu => ⟨pwv.append pvu⟩

theorem reachable_iff_star_relate {M} {α : Program} {w v : W} :
    Reachable M α w v ↔ relate M (∗α) w v := by
  constructor
  · rintro ⟨h⟩
    induction h with
    | nil => exact .refl
    | cons h' _ _ ih => exact (Relation.ReflTransGen.single h').trans ih
  · intro h
    induction h with
    | refl => rfl
    | tail _  ha hr => exact by_cases (p := _ = _) (Eq.subst · (motive := (Reachable _ _ _ ·)) hr)
                                                   (Reachable.trans hr ⟨Walk.cons ha (.nil α) ·⟩)

/-- Unused -/
theorem star_relate_of_Chain : List.IsChain (relate M α) (w :: l ++ [v]) → relate M (∗α) w v :=
  fun h => match l with
  | .nil => .single <| List.IsChain.rel h
  | .cons x xs => .head (b := x) (List.IsChain.rel h) <| star_relate_of_Chain (l := xs) <|
      match h with | .cons_cons _ h => h

/-! ## Distance -/

open Classical in
/-- The recursively weighted distance of a program between two worlds. -/
noncomputable def distance {W} (M : KripkeModel W) (α : Program) (w v : W) : ℕ∞ :=
  match α with
  | ·_ => ite (relate M α w v) 1 ⊤
  | ?'_ => ite (relate M α w v) 0 ⊤
  | α ⋓ β => (distance M α w v) ⊓ (distance M β w v)
  | ∗α => fdist' M α w v (ENat.toNat <| distance M α · ·)
  | α;' β => ⨅ x, distance M α w x + distance M β x v

theorem distance_self_star : distance M (∗α) w w = 0 := ciInf_eq_bot_of_bot_mem ⟨.nil α, rfl⟩

open Classical in
/-- The minimum total distance for a sequence of programs, allowing infinity. -/
noncomputable def distanceList {W} (M : KripkeModel W) (w v : W) : (δ : List Program) → ℕ∞
| [] => ite (w = v) 0 ⊤
| (α::δ) => ⨅ x, distance M α w x + distanceList M x v δ -- similar to α;'β case in `distance`

open Classical in
/-- 7.47 (a) -/
theorem dist_iff_rel : (distance M α w v) ≠ ⊤ ↔ relate M α w v :=
  match α with
  | ·_ => ite_ne_right_iff.trans <| (iff_self_and.mpr fun _ => ENat.one_ne_top).symm
  | ?'_ => ite_ne_right_iff.trans <| (iff_self_and.mpr fun _ => ENat.zero_ne_top).symm
  | _ ⋓ _ => (min_eq_top.not.trans not_and_or).trans <| or_congr (dist_iff_rel ..) (dist_iff_rel ..)
  | ∗_ => ENat.iInf_natCast_ne_top.trans <| reachable_iff_star_relate ..
  | _;' _ => iInf_eq_top.not.trans <| not_forall.trans <| exists_congr fun _ =>
    WithTop.add_ne_top.trans <| and_congr (dist_iff_rel ..) (dist_iff_rel ..)

theorem distance_cast : distance M (∗α) w v = fdist M α w v (distance M α · ·) :=
  Eq.symm <| fdist_cast dist_iff_rel.mpr

theorem distance_list_nil_self : distanceList M w w [] = 0 :=
  by simp only [distanceList, ↓reduceIte]

open Classical in
theorem eq_of_distance_nil (h : distanceList M w v [] ≠ ⊤) : w = v := (ite_ne_right_iff.mp h).1

theorem distance_list_singleton :
    distanceList M w v [α] = distance M α w v :=
  iInf_eq_of_forall_ge_of_forall_gt_exists_lt
    (fun x => by_cases
      (by simp_all only [self_le_add_right, implies_true] : x = v → _)
      (by simp_all only [distanceList, ite_false, add_top, le_top, implies_true]))
    (fun _ _ => ⟨v, by simp_all only [distanceList, ite_true, add_zero]⟩)

theorem ENat.min_neq_top_iff {M N : ℕ∞} : min M N ≠ ⊤ ↔ (M ≠ ⊤) ∨ (N ≠ ⊤) :=
  min_eq_top.not.trans not_and_or

theorem List.exists_mem_singleton {p : α → Prop} : (∃ x ∈ [a], p x) ↔ p a :=
  ⟨fun ⟨_, ⟨x_in, px⟩⟩ ↦ List.mem_singleton.mp x_in ▸ px, (⟨_, ⟨List.mem_singleton_self _, ·⟩⟩)⟩

theorem ite_eq_right_of_ne_left [Decidable c] (h : ite c t e ≠ t) : ite c t e = e :=
  (ite_eq_or_eq ..).elim (False.elim ∘ h) id

/-- The elements of `α` attained by a function into `WithTop α`. -/
def WithTop.domain (f : ι → WithTop α) : Set α := fun a => ∃ i, f i = a

theorem domain_nonempty_of_iInf_ne_top {f : ι → ℕ∞} (h : iInf f ≠ ⊤) :
    (WithTop.domain f).Nonempty :=
  have ⟨i, fi_ne_top⟩ := Classical.not_forall.mp <| iInf_eq_top.not.mp h
  ⟨(f i).untop fi_ne_top, i, ((f i).coe_untop _).symm⟩

open Classical in
theorem ENat.iInf_eq_find_of_ne_top {f : ι → ℕ∞} (h : iInf f ≠ ⊤)
    : iInf f = Nat.find (domain_nonempty_of_iInf_ne_top h) :=
  (ite_eq_right_of_ne_left h).trans <| congr_arg _ <| dite_eq_left _

open Classical in
theorem iInf_exists_eq_of_ne_top {f : ι → ℕ∞} (h : iInf f ≠ ⊤) : ∃ i, iInf f = f i :=
  have ⟨i, spec⟩ := Nat.find_spec (domain_nonempty_of_iInf_ne_top h)
  ⟨i, (ENat.iInf_eq_find_of_ne_top h).trans spec.symm⟩

theorem iInf_exists_eq [NE : Nonempty ι] (f : ι → ℕ∞) : ∃ i, iInf f = f i :=
  NE.elim fun i =>
    dite (iInf f = ⊤) (fun h => ⟨i, h.trans (iInf_eq_top.mp h _).symm⟩) iInf_exists_eq_of_ne_top

theorem iInf_of_min {f : ι → ℕ∞} {i : ι} (h : ∀ j, f i ≤ f j) : iInf f = f i :=
  iInf_eq_of_forall_ge_of_forall_gt_exists_lt h fun _ => (⟨i, ·⟩)

theorem add_iInf {f : ι → ℕ∞} {a : ℕ∞} : a + ⨅ i, f i = ⨅ i, a + f i :=
  (isEmpty_or_nonempty ι).elim
  (fun _ =>
    calc
    _ = ⊤ := iInf_of_empty f ▸ add_top a
    _ = _ := (iInf_of_empty _).symm)
  (fun _ =>
    let ⟨i, hi⟩ := iInf_exists_eq f
    let h : ⨅ i, a + f i = a + f i := iInf_of_min fun _ => add_le_add_right (hi ▸ iInf_le ..) _
    calc
      _ = a + f i := congr_arg _ hi
      _ = ⨅ i, a + f i := h.symm)

theorem iInf_add {f : ι → ℕ∞} {a : ℕ∞} : (⨅ i, f i) + a = ⨅ i, f i + a := calc
  _ = a + ⨅ i, f i := add_comm _ _
  _ = ⨅ i, a + f i := add_iInf
  _ = ⨅ i, f i + a := iInf_congr fun _ => add_comm ..

theorem distance_list_append (δ₁ δ₂ : List Program)
    : distanceList M w v (δ₁ ++ δ₂) = ⨅ x, distanceList M w x δ₁ + distanceList M x v δ₂ :=
  match δ₁ with
  | [] => Eq.symm <| iInf_eq_of_forall_ge_of_forall_gt_exists_lt
    (fun x => by_cases
      (by simp_all only [List.nil_append, self_le_add_left, implies_true])
      (fun h => le_of_le_of_eq le_top
        ((ite_eq_right h : distanceList _ _ _ [] = _) ▸ (top_add (distanceList ..)).symm)))
    fun _ _ => ⟨w, by simp_all only [List.nil_append, distanceList, ite_true, zero_add]⟩
  | (α::δ₁') =>
    let IH u := distance_list_append δ₁' δ₂
    calc
      _ = _ := iInf_congr (congr_arg _ <| IH ·)
      _ = ⨅ u, ⨅ x, distance M α w u + distanceList M u x δ₁' + distanceList M x v δ₂ := by
          simp only [add_iInf, add_assoc]
      _ = _ := iInf_comm
      _ = ⨅ x, (⨅ u, distance M α w u + distanceList M u x δ₁') + distanceList M x v δ₂ := by
          simp only [add_assoc, iInf_add]
      _ = _ := by simp only [distanceList]

theorem distance_list_cons {w v α δ} :
    distanceList M w v (α :: δ) = ⨅ x, distance M α w x + distanceList M x v δ := by
  simp only [distanceList]

theorem distance_list_concat {w v δ α} :
    distanceList M w v (δ ++ [α]) = ⨅ x, distanceList M w x δ + distance M α x v :=
  (distance_list_append δ [α]).trans <| iInf_congr fun _ => congr_arg _ distance_list_singleton

theorem distance_comp_eq_distList :
    distance M (β;'β') w v = distanceList M w v [β, β'] := by
  unfold distance
  rw [distance_list_cons]
  simp_rw [distance_list_singleton]

theorem distance_star_le x :
    distance M (∗α) w v ≤ distance M α w x + distance M (∗α) x v :=
  by_cases (p := distance M α w x + distance M (∗α) x v = ⊤) (· ▸ le_top) <|
   (let ⟨hwx, hxv⟩ := WithTop.add_ne_top.mp ·
    let ⟨p, h⟩ := iInf_exists_eq_of_ne_top hxv
    let rwx := dist_iff_rel.mp hwx
    by_cases (p := w = x) (fun _ => by simp_all [self_le_add_left]) (
    let p' : Walk M α w v := .cons rwx p ·
    calc
    _ ≤ _ := iInf_le _ p'
    _ = _ := ENat.natCast_add _ _
    _ ≤ _ := add_le_add (ENat.natCast_toNat_le_self _) <| le_of_eq h.symm)
   )

/-! ## Distance of diamond unfoldings

Here we relate `distance` to `H`.
-/

/-- 7.47 (b) -/
lemma distance_list_eq_distance_steps (M : KripkeModel W) (v w : W) δ :
    (distanceList M v w δ) = (distance M (Program.steps δ) v w) := by
  induction δ generalizing v w
  · simp_all [distanceList, distance]
    aesop
  case cons α δ IH =>
    simp_all [distanceList, distance]

/-- like 7.47 (a) but for lists -/
theorem distance_list_iff_relate_Seq :
    distanceList M w v δ ≠ ⊤ ↔ relateSeq M δ w v := by
  rw [distance_list_eq_distance_steps, @dist_iff_rel W M (Program.steps δ) w v]
  exact relate_steps_iff_relateSeq M δ w v

/-- 7.47 (c) -/
lemma dist_le_of_distList_le (h : ∀ u, distance M α v u ≤ distanceList M v u δ) :
    ∀ u, distanceList M v u (α :: γ) ≤ distanceList M v u (δ ++ γ) := by
  let β := Program.steps δ
  suffices ∀ u, distanceList M v u (α :: γ) ≤ distanceList M v u (β :: γ) by
    intro u
    specialize this u
    rw [distance_list_append, le_iInf_iff]
    intro u'
    rw [distance_list_eq_distance_steps M v u' δ] -- using (b)
    rw [@distance_list_cons W M v u β, le_iInf_iff] at this
    exact this u'
  intro u
  have := @iInf_exists_eq W ⟨v⟩ (fun u' => distance M β v u' + distanceList M u' u γ)
  rcases this with ⟨u', u'_minimizes⟩
  calc
    distanceList M v u (α :: γ)
      ≤ distance M α v u' + distanceList M u' u γ := by rw [distanceList]; apply iInf_le
    _ ≤ distance M β v u' + distanceList M u' u γ := by
          refine add_le_add ?_ (Preorder.le_refl (distanceList M u' u γ))
          unfold β
          rw [← distance_list_eq_distance_steps] -- using (b)
          apply h
    _ = distanceList M v u (β :: γ) := u'_minimizes.symm

open Classical in
/-- 7.47 (d) -/
theorem distance_le_Hdistance (in_D : (X, δ) ∈ Dset α) :
  (M, w) ⊨ con X → distance M α w v ≤ distanceList M w v δ :=
  let me := (evaluate M w <| con ·)
  fun ev => match α with
  | ·_ =>
    let ⟨_, hδ⟩ := Prod.eq_iff_fst_eq_snd_eq.mp <| List.eq_of_mem_singleton in_D
    calc
      _ = _ := distance_list_singleton.symm
      _ ≤ _ := le_of_eq <| congr_arg _ hδ.symm
  | ?'_ =>
    let ⟨hX, hδ⟩ := Prod.eq_iff_fst_eq_snd_eq.mp <| List.eq_of_mem_singleton in_D
    let d_eq_dl := ite_congr (propext ⟨And.left, (⟨·, hX.subst (motive := me) ev⟩)⟩)
                     (fun _ ↦ rfl) (fun _ => rfl)
    le_of_eq <| hδ.symm.subst (motive := (_ = distanceList _ _ _ ·)) d_eq_dl
  | _⋓_ => (List.mem_union_iff.mp in_D).elim
    (inf_le_left.trans <| distance_le_Hdistance · ev)
    (inf_le_right.trans <| distance_le_Hdistance · ev)
  | β;' β' =>
    let ⟨⟨_, δα⟩, in_Dβ, h⟩ := List.exists_of_mem_flatMap in_D
    if c : δα = []
      then by
        subst c
        simp only [↓reduceIte, List.mem_flatten, List.mem_map, Prod.exists] at h
        rcases h with ⟨l, ⟨Y, γ, in_Dβ', def_l⟩ , in_l⟩; subst def_l
        simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at in_l
        cases in_l; subst_eqs
        let evα := conEval.mpr (List.forall_mem_union.mp <| conEval.mp ev).1
        have IHβ := fun u => @distance_le_Hdistance _ _ _ _ u in_Dβ evα
        have c := @dist_le_of_distList_le W M β w _ [β'] IHβ v -- using (c) here
        let evβ' := conEval.mpr (List.forall_mem_union.mp <| conEval.mp ev).2
        have IHβ' := @distance_le_Hdistance _ _ _ _ v in_Dβ' evβ'
        -- "From these two observations ..."
        calc  distance M (β;' β') w v
            = distanceList M w v [β, β'] := distance_comp_eq_distList
          _ ≤ distanceList M w v [β'] := c
          _ = distance M β' w v := distance_list_singleton
          _ ≤ distanceList M w v δ := IHβ'
      else
        let h := (ite_eq_right c).subst h
        let ⟨hX, hδ⟩ := Prod.eq_iff_fst_eq_snd_eq.mp <| List.eq_of_mem_singleton <| h
        let evα := hX.subst (motive := me) ev
        let IHβ x := (distance_le_Hdistance (v := x) in_Dβ evα)
        calc  distance M (β;' β') w v
          _ ≤ ⨅ i, distance M β w i + distance M β' i v := le_iInf (iInf_le _)
          _ ≤ ⨅ x, distanceList M w x δα + distanceList M x v [β']
              := iInf_mono fun x => add_le_add (IHβ x) <| le_of_eq distance_list_singleton.symm
          _ = distanceList M w v (δα ++ [β']) := (distance_list_append _ _).symm
          _ = distanceList M w v (X, δ).2 := congr_arg _ hδ.symm
  | ∗_ =>
    (List.mem_union_iff.mp in_D).elim (
      let ⟨_, hδ⟩ := Prod.eq_iff_fst_eq_snd_eq.mp <| List.eq_of_mem_singleton ·
      dite (w = v)
      (· ▸ calc
        _ = _ := ENat.iInf_eq_zero.mpr ⟨.nil _, rfl⟩
        _ ≤ _ := bot_le)
      (fun c => calc
        _ ≤ _ := le_top
        _ = _ := Eq.symm <| hδ.symm.subst (motive := (distanceList _ _ _ · = _)) <| ite_eq_right c)
    ) (
      let ⟨_, in_Dα, h⟩ := List.exists_of_mem_flatMap ·
      let ⟨_, h⟩ := List.mem_ite_nil_left.mp h
      let ⟨hX, hδ⟩ := Prod.eq_iff_fst_eq_snd_eq.mp <| List.eq_of_mem_singleton h
      let hδ : δ = _ := hδ
      let evα := hX.subst (motive := me) ev
      calc
        _ ≤ _ := le_iInf fun u => (distance_star_le u).trans <|
          add_le_add (distance_le_Hdistance in_Dα evα) <| le_of_eq distance_list_singleton.symm
        _ = _ := hδ ▸ (distance_list_append ..).symm
    )

/-- 7.47 (e) -/
lemma distList_le_of_Hsat {Xδ} {W} M (v w : W) α γ
    (in_D : Xδ ∈ Dset α)
    (v_X : evaluate M v (con Xδ.1))
    : distanceList M v w (α :: γ) ≤ distanceList M v w (Xδ.2 ++ γ) :=
  dist_le_of_distList_le (fun _ => distance_le_Hdistance in_D v_X) w -- using (c) and (d)

/-- 7.47 (f) -/
theorem rel_existsD_dist (w_α_v : relate M α w v)
    : ∃ Xδ ∈ Dset α,
        evaluate M w (con Xδ.1)
      ∧ distanceList M w v Xδ.2 = distance M α w v :=
  have d_fin : distance M α w v ≠ ⊤ := dist_iff_rel.mpr w_α_v
  match α with
  | ·_ => List.exists_mem_singleton.mpr ⟨id, distance_list_singleton⟩
  | ?'_ => match w_α_v with | ⟨wv, wφ⟩ => List.exists_mem_singleton.mpr <|
    ⟨wφ, by simp_all only [relate, true_and, distanceList, ite_true, distance, and_self]⟩
  | α⋓β =>
    Or.elim (min_cases (distance M α w v) (distance M β w v))
    (fun ⟨min_eq, d_le⟩ =>
      let ⟨Fδ, in_D, eval, dl_eq_d⟩ :=
        rel_existsD_dist <| dist_iff_rel.mp <| ne_of_eq_of_ne min_eq.symm d_fin
      ⟨Fδ, List.mem_union_iff.mpr <| .inl in_D, eval, dl_eq_d.trans min_eq.symm⟩
    )
    (fun ⟨min_eq, d_le⟩ =>
      let ⟨Fδ, in_D, eval, dl_eq_d⟩ :=
        rel_existsD_dist <| dist_iff_rel.mp <| ne_of_eq_of_ne min_eq.symm d_fin
      ⟨Fδ, List.mem_union_iff.mpr <| .inr in_D, eval, dl_eq_d.trans min_eq.symm⟩
    )
  | α;'β =>
    let ⟨u, min_u⟩ := iInf_exists_eq_of_ne_top d_fin
    let ⟨dα_fin, dβ_fin⟩:= WithTop.add_ne_top.mp <| ne_of_eq_of_ne min_u.symm d_fin
    let ⟨⟨Xα, δα⟩, in_Dα, evα, dlα⟩ := rel_existsD_dist <| dist_iff_rel.mp dα_fin
    let ⟨⟨Xβ, δβ⟩, in_Dβ, evβ, dlβ⟩ := rel_existsD_dist <| dist_iff_rel.mp dβ_fin
    if c : δα = []
      then
        let wu : w = u := eq_of_distance_nil <| ne_of_eq_of_ne (c ▸ dlα) dα_fin
        let dα : distance M α w u = 0 := dlα.symm.trans <| c ▸ ite_eq_left wu
        let d : distance M (α;'β) w v = distance M β w v := min_u.trans (dα ▸ wu ▸ zero_add _)
        ⟨⟨Xα ∪ Xβ, δβ⟩, List.mem_flatMap_of_mem in_Dα (by aesop),
        conEval.mpr <| List.forall_mem_union.mpr ⟨conEval.mp evα, conEval.mp <| wu ▸ evβ⟩,
        d ▸ wu ▸ dlβ⟩
      else
        ⟨ ⟨Xα, δα ++ [β]⟩
        , List.mem_flatMap_of_mem in_Dα <| by simp only [c, ↓reduceIte, List.mem_singleton]
        , evα, calc
          _ = _ := distance_list_append _ _
          _ = _ := iInf_congr fun _ => congr_arg _ distance_list_singleton
          _ = _ := iInf_eq_of_forall_ge_of_forall_gt_exists_lt (
            fun _ => calc
              _ ≤ _ := iInf_le (fun x => distance M α w x + distance M β x v) _
              _ ≤ _ := add_le_add_left (distance_le_Hdistance in_Dα evα) _
            )
            fun _ => (⟨u, calc
              _ + _ = _ + _ := congr_arg (· + _) dlα
              _ < _ := min_u ▸ ·
            ⟩)
        ⟩
  | ∗α =>
  by_cases (p := w = v)
    (fun wv => ⟨([],[]), List.mem_union_iff.mpr <| .inl <| List.mem_singleton_self _, id, calc
      _ = 0 := wv ▸ distance_list_nil_self
      _ = distance .. := wv ▸ distance_self_star.symm⟩)
    (fun wv =>
      let ⟨p, min_p⟩ := iInf_exists_eq_of_ne_top (distance_cast.subst (motive := (· ≠ ⊤)) d_fin)
      match p with
      | .nil α => absurd rfl wv
      | .cons (x := x) rwx pxv wx =>
        let ⟨⟨Xα, δα⟩, in_Dα, evα, dlα⟩ := rel_existsD_dist rwx
        let dα_fin : distanceList M _ _ δα ≠ ⊤ := ne_of_eq_of_ne dlα <| dist_iff_rel.mpr rwx
        let hδα : δα ≠ [] := mt (eq_of_distance_nil <| · ▸ dα_fin) wx
        ⟨ (Xα, δα ++ [∗α])
        , List.mem_union_iff.mpr <| .inr <| List.mem_flatMap_of_mem in_Dα (by simp_all)
        , evα
        , distance_list_concat ▸ iInf_eq_of_forall_ge_of_forall_gt_exists_lt
          (fun y => (distance_star_le y).trans <|
                    add_le_add_left (distance_le_Hdistance in_Dα evα) _)
          fun _ => (⟨x, lt_of_eq_of_lt (calc
            _ = distance M α w x + fdist .. := congr_arg₂ (· + ·) dlα distance_cast
            _ = _ := eq_of_le_of_ge (add_le_add_right (iInf_le _ _) _) <| calc
              _ = _ := min_p.symm
              _ ≤ _ := le_iInf (iInf_le _ <| .cons rwx · wx)
              _ = _ := add_iInf.symm
            _ = _ := min_p.symm
            _ = _ := distance_cast.symm)
          ·⟩)
        ⟩
    )

/-- 7.47 (g) -/
theorem relateSeq_existsD_dist (v_αγ_w : relateSeq M (α :: γ) v w)
    : ∃ Xδ ∈ Dset α,
        evaluate M v (con Xδ.1)
      ∧ distanceList M v w (Xδ.2 ++ γ) = distanceList M v w (α :: γ) := by
  have claim : ∃ u, relate M α v u ∧ relateSeq M γ u w ∧
      distanceList M v w (α :: γ) = distance M α v u + distanceList M u w γ := by
    have αγ_not_inf := distance_list_iff_relate_Seq.mpr v_αγ_w -- using (a) for lists
    have := @iInf_exists_eq W ⟨v⟩ (fun u => distance M α v u + distanceList M u w γ)
    rcases this with ⟨u, u_minimizes⟩
    rw [distance_list_cons] at αγ_not_inf
    rw [distance_list_cons]
    refine ⟨u, ?_, ?_, u_minimizes⟩
    · rw [← dist_iff_rel]; aesop
    · rw [← distance_list_iff_relate_Seq]; aesop
  rcases claim with ⟨u, v_α_u, u_w, αγ_eq_α_γ⟩
  have := rel_existsD_dist v_α_u -- applying (f)
  rcases this with ⟨⟨X,δ⟩, in_D, v_X, δ_eq_α⟩
  simp only at δ_eq_α
  use ⟨X,δ⟩
  have one : distanceList M v w (α :: γ) ≥ distanceList M v w (δ ++ γ) := by
    rw [αγ_eq_α_γ, ← δ_eq_α]
    simp only [distance_list_append, ge_iff_le]
    apply iInf_le
  have two : distanceList M v w (α :: γ) ≤ distanceList M v w (δ ++ γ) :=
    distList_le_of_Hsat M v _ α γ in_D v_X -- use (e)
  exact ⟨in_D, v_X, eq_of_le_of_ge one two⟩

/-- 7.47 (h)
In the article this uses loaded formulas, we just use normal boxes. -/
theorem existsD_of_true_diamond α γ (ψ : Formula) (v_ : evaluate M v (~⌈⌈α :: γ⌉⌉ψ))
    : ∃ Xδ ∈ Dset α, evaluate M v (con Xδ.1)
                ∧ evaluate M v (~⌈⌈Xδ.2⌉⌉⌈⌈γ⌉⌉ψ)
                ∧   ⨅ w : {w // evaluate M w (~ψ)}, distanceList M v w (Xδ.2 ++ γ)
                  = ⨅ w : {w // evaluate M w (~ψ)}, distanceList M v w (α :: γ) := by
  simp only [evaluate] at v_
  rw [evalBoxes] at v_
  push Not at v_
  rcases v_ with ⟨w1, v_αγ_w1, w1_not_ψ⟩
  -- Let `w0` be the witness to minimize the `α :: γ` distance from `w0` to `~ψ`:
  have := @iInf_exists_eq {w // evaluate M w (~ψ)} ⟨w1, w1_not_ψ⟩
    (fun w => distanceList M v w (α :: γ))
  rcases this with ⟨w0, w0_minimizes⟩
  have v_αγ_w0 : relateSeq M (α :: γ) v w0 := by
    rw [← distance_list_iff_relate_Seq, ← w0_minimizes]
    simp only [evaluate, ne_eq, iInf_eq_top, Subtype.forall, not_forall]
    refine ⟨w1, w1_not_ψ, ?_⟩
    rw [← @Ne.eq_def, distance_list_iff_relate_Seq]
    exact v_αγ_w1
  have g := relateSeq_existsD_dist v_αγ_w0 -- use (g)
  rcases g with ⟨Xδ, in_D, v_X, same_dist⟩
  refine ⟨Xδ, in_D, v_X, ?_, ?_⟩
  · rw [← @boxes_append]
    simp only [evaluate, evalBoxes, not_forall]
    refine ⟨w0, ?_, by cases w0; assumption⟩
    rw [← distance_list_iff_relate_Seq, same_dist, distance_list_iff_relate_Seq]
    exact v_αγ_w0
  · apply eq_of_le_of_ge
    · -- second ≤ and = in the article:
      calc ⨅ w : {w // evaluate M w (~ψ)}, distanceList M v w (Xδ.2 ++ γ)
           ≤ distanceList M v w0 (α :: γ) := by rw [← same_dist]; apply iInf_le -- It follows ...
         _ = ⨅ w : {w // evaluate M w (~ψ)}, distanceList M v w (α :: γ) := w0_minimizes.symm
    · -- first ≤ in article:
      have e := fun w : {w // evaluate M w (~ψ)} => distList_le_of_Hsat M v w _ γ in_D v_X -- (e)
      exact iInf_mono e

/-- Summary definition of Lemma 7.47 -/
theorem distanceProps {Xδ} W M α {w v : W} δ :
      (distance M α w v ≠ ⊤ ↔ relate M α w v) -- a
    ∧ (distanceList M v w δ = distance M (Program.steps δ) v w) -- b
    ∧ ((∀ (u : W), distance M α v u ≤ distanceList M v u δ) →
        ∀ (u : W), distanceList M v u (α :: γ) ≤ distanceList M v u (δ ++ γ)) -- c
    ∧ ((X, δ) ∈ Dset α → (M, w)⊨con X → distance M α w v ≤ distanceList M w v δ) -- d
    ∧ (Xδ ∈ Dset α → evaluate M v (con Xδ.1) →
        distanceList M v w (α :: γ) ≤ distanceList M v w (Xδ.2 ++ γ) ) -- e
    ∧ (relate M α w v → ∃ Xδ ∈ Dset α,
        evaluate M w (con Xδ.1) ∧ distanceList M w v Xδ.2 = distance M α w v ) -- f
    ∧ (relateSeq M (α :: γ) v w → ∃ Xδ ∈ Dset α,
        evaluate M v (con Xδ.1) ∧
        distanceList M v w (Xδ.2 ++ γ) = distanceList M v w (α :: γ)) -- g
    ∧ (evaluate M v (~⌈⌈α :: γ⌉⌉ψ) → ∃ Xδ ∈ Dset α,
        evaluate M v (con Xδ.1) ∧
        evaluate M v (~⌈⌈Xδ.2⌉⌉⌈⌈γ⌉⌉ψ) ∧
          ⨅ w : {w // evaluate M w (~ψ)}, distanceList M v (↑w) (Xδ.2 ++ γ)
        = ⨅ w : {w // evaluate M w (~ψ)}, distanceList M v (↑w) (α :: γ) ) -- h
     :=
   ⟨ dist_iff_rel -- (a)
   , distance_list_eq_distance_steps M v w δ --(b)
   , dist_le_of_distList_le -- (c)
   , distance_le_Hdistance -- (d)
   , distList_le_of_Hsat M v w α γ -- (e)
   , rel_existsD_dist -- (f)
   , relateSeq_existsD_dist -- (g)
   , existsD_of_true_diamond α γ ψ -- (h)
   ⟩

theorem exists_same_distance_of_relateSeq_cons (w_αδ_v : relateSeq M (α :: δ) w v) :
    ∃ x, relate M α w x
       ∧ relateSeq M δ x v
       ∧ distanceList M w v (α :: δ) = distance M α w x + distanceList M x v δ := by
  have := @distance_list_iff_relate_Seq.mpr w_αδ_v
  have := iInf_exists_eq_of_ne_top this
  rcases this with ⟨x, same_dist⟩
  refine ⟨x, ?_, ?_, same_dist⟩
  · rw [← dist_iff_rel]
    intro hyp
    rw [← distance_list_cons] at same_dist
    simp_all
  · rw [← distance_list_iff_relate_Seq]
    intro hyp
    rw [← distance_list_cons] at same_dist
    simp_all

theorem exists_same_distance_list_relateSeq_concat (w_δα_v : relateSeq M (δ ++ [α]) w v) :
    ∃ x, relateSeq M δ w x
       ∧ relate M α x v
       ∧ distanceList M w v (δ ++ [α]) = distanceList M w x δ + distance M α x v := by
  rw[distance_list_concat]
  have := @distance_list_iff_relate_Seq.mpr w_δα_v
  rw[distance_list_concat] at this
  have := iInf_exists_eq_of_ne_top this
  rcases this with ⟨x, same_dist⟩
  refine ⟨x, ?_, ?_, same_dist⟩
  · rw [← distance_list_iff_relate_Seq]
    aesop
  · rw [← dist_iff_rel]
    aesop

end PDL
