/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import LeanPool.BlockSpectralSensitivity.LLL.Prob
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-!
# The asymmetric Lovász local lemma

Mathlib does not contain the Lovász local lemma, so we prove the version we need from
scratch, for the finite counting probability space of `BSLambda.LLL.Prob`.

Events are given by a family `Ev : I → Finset (Cfg β)`, each `Ev i` being determined by the
coordinate set `supp i`.  Two events are *dependent* when their supports meet.  `nbr supp i`
collects the indices of the events other than `i` that are dependent with `Ev i`.

The main results are `pr_avoid_pos` (the general asymmetric local lemma of Section 10 of
`bs_lambda.txt`) and `pr_avoid_pos_two_type` (the two-type statement of Section 10.2).

The last section is independent of the local lemma: `pr_le_prod_of_pinned` and its
constant-alphabet form `pr_le_pow_of_pinned` bound the probability of an event that pins a set
of coordinates to targets read off a disjoint set of coordinates.  They supply the hypothesis
`hcond` above at the places where the local lemma is applied.

Adapted for Lean Pool from `Timeroot/BS_Lam` at commit
`7bd39a8d41ee7910d3296d0477ad18f8fff9d870`; ported to Lean Pool with proof and dependency cleanup.
-/

public section

namespace BSLambda.LLL

variable {A : Type*} [Fintype A] [DecidableEq A]
variable {β : A → Type*} [∀ a, Fintype (β a)] [∀ a, DecidableEq (β a)] [∀ a, Nonempty (β a)]
variable {I : Type*} [Fintype I] [DecidableEq I]

/-! ## Dependency neighbourhoods and avoidance events -/

/-- The dependency neighbourhood: other events whose supports meet ours. -/
def nbr (supp : I → Finset A) (i : I) : Finset I :=
  Finset.univ.filter fun j ↦ j ≠ i ∧ ¬ Disjoint (supp i) (supp j)

omit [Fintype A] in
/-- Membership in the dependency neighbourhood. -/
@[simp] theorem mem_nbr {supp : I → Finset A} {i j : I} :
    j ∈ nbr supp i ↔ j ≠ i ∧ ¬ Disjoint (supp i) (supp j) := by
  simp [nbr]

omit [Fintype A] in
/-- The events indexed outside the dependency neighbourhood of `i` are supported away from
`supp i`. -/
theorem disjoint_supp_sup_sdiff_nbr {supp : I → Finset A} {i : I} {S : Finset I} (hi : i ∉ S) :
    Disjoint (supp i) ((S \ nbr supp i).sup supp) := by
  rw [Finset.disjoint_sup_right]
  intro j hj
  rw [Finset.mem_sdiff] at hj
  by_contra hc
  exact hj.2 (mem_nbr.mpr ⟨fun e ↦ hi (e ▸ hj.1), hc⟩)

/-- The event that none of the bad events indexed by `S` occurs. -/
def avoid (Ev : I → Finset (Cfg β)) (S : Finset I) : Finset (Cfg β) :=
  Finset.univ.filter fun ω ↦ ∀ i ∈ S, ω ∉ Ev i

section AvoidBasic

omit [∀ (a : A), Nonempty (β a)] in
/-- Membership in `avoid`. -/
@[simp] theorem mem_avoid {Ev : I → Finset (Cfg β)} {S : Finset I} {ω : Cfg β} :
    ω ∈ avoid Ev S ↔ ∀ i ∈ S, ω ∉ Ev i := by
  simp [avoid]

omit [∀ (a : A), Nonempty (β a)] in
/-- Avoiding no events is the sure event. -/
@[simp] theorem avoid_empty (Ev : I → Finset (Cfg β)) :
    avoid Ev ∅ = (Finset.univ : Finset (Cfg β)) := by
  ext ω
  simp

omit [∀ (a : A), Nonempty (β a)] in
/-- Avoiding every event is avoiding all of them. -/
theorem avoid_univ (Ev : I → Finset (Cfg β)) :
    avoid Ev (Finset.univ : Finset I) = Finset.univ.filter fun ω ↦ ∀ i, ω ∉ Ev i := by
  ext ω
  simp

omit [∀ (a : A), Nonempty (β a)] in
/-- Avoiding more events is a smaller event. -/
theorem avoid_anti {Ev : I → Finset (Cfg β)} {S T : Finset I} (h : S ⊆ T) :
    avoid Ev T ⊆ avoid Ev S :=
  fun _ hω ↦ mem_avoid.mpr fun i hi ↦ mem_avoid.mp hω i (h hi)

omit [∀ (a : A), Nonempty (β a)] in
/-- Peeling one event off `avoid`. -/
theorem avoid_insert (Ev : I → Finset (Cfg β)) (i : I) (S : Finset I) :
    avoid Ev (insert i S) = (Ev i)ᶜ ∩ avoid Ev S := by
  ext ω
  simp

omit [∀ (a : A), Nonempty (β a)] in
/-- `avoid Ev S` is determined by the union of the supports of the events indexed by `S`. -/
theorem determined_avoid {Ev : I → Finset (Cfg β)} {supp : I → Finset A}
    (hdet : ∀ i, Determined (supp i) (Ev i)) (S : Finset I) :
    Determined (S.sup supp) (avoid Ev S) := fun ω ω' h ↦ by
  simp only [mem_avoid]
  exact forall₂_congr fun i hi ↦
    not_congr (hdet i ω ω' fun a ha ↦ h a (Finset.le_sup (f := supp) hi ha))

end AvoidBasic

/-! ## The local lemma -/

section Telescope

omit [∀ (a : A), Nonempty (β a)] in
/-- **Peeling one event.**  If `Ev j` is conditionally bounded by `x j` given that the events
indexed by `S` are avoided, then also avoiding `Ev j` costs at most the factor `1 - x j`. -/
private theorem mul_pr_avoid_le_pr_avoid_insert {Ev : I → Finset (Cfg β)} {x : I → ℝ} {j : I}
    {S : Finset I} (h : pr (Ev j ∩ avoid Ev S) ≤ x j * pr (avoid Ev S)) :
    (1 - x j) * pr (avoid Ev S) ≤ pr (avoid Ev (insert j S)) := by
  rw [avoid_insert, pr_compl_inter, sub_mul, one_mul]
  exact sub_le_sub_left h _

omit [∀ (a : A), Nonempty (β a)] in
/-- **Telescoping step.**  If, along the way, every single event can be bounded by its
weight `x j` conditionally on the events avoided so far, then avoiding all of `T` on top of
`U` costs at most the factor `∏ j ∈ T, (1 - x j)`. -/
private theorem le_pr_avoid_union (Ev : I → Finset (Cfg β)) (x : I → ℝ) (hx1 : ∀ j, x j ≤ 1)
    (U T : Finset I) (hstep : ∀ T' ⊆ T, ∀ j ∈ T, j ∉ T' →
      pr (Ev j ∩ avoid Ev (U ∪ T')) ≤ x j * pr (avoid Ev (U ∪ T'))) :
    (∏ j ∈ T, (1 - x j)) * pr (avoid Ev U) ≤ pr (avoid Ev (U ∪ T)) := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T ha ih =>
    have hIH : (∏ j ∈ T, (1 - x j)) * pr (avoid Ev U) ≤ pr (avoid Ev (U ∪ T)) :=
      ih fun T' hT' j hj hj' ↦
        hstep T' (hT'.trans (Finset.subset_insert a T)) j (Finset.mem_insert_of_mem hj) hj'
    have hge : (1 - x a) * pr (avoid Ev (U ∪ T)) ≤ pr (avoid Ev (U ∪ insert a T)) := by
      rw [Finset.union_insert]
      exact mul_pr_avoid_le_pr_avoid_insert
        (hstep T (Finset.subset_insert a T) a (Finset.mem_insert_self a T) ha)
    rw [Finset.prod_insert ha, mul_assoc]
    exact (mul_le_mul_of_nonneg_left hIH (sub_nonneg.mpr (hx1 a))).trans hge

end Telescope

section Main

variable (Ev : I → Finset (Cfg β)) (supp : I → Finset A) (x : I → ℝ)

/-- Positivity of `pr (avoid Ev S)`, granted the conditional bounds on strictly smaller
index sets. -/
private theorem pr_avoid_pos_of_forall_card_lt (hx1 : ∀ i, x i < 1) (S : Finset I)
    (IH : ∀ T : Finset I, T.card < S.card →
      0 < pr (avoid Ev T) ∧ ∀ i ∉ T, pr (Ev i ∩ avoid Ev T) ≤ x i * pr (avoid Ev T)) :
    0 < pr (avoid Ev S) := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨j, hj⟩
  · simp
  obtain ⟨hpos, hbnd⟩ := IH (S.erase j) (Finset.card_erase_lt_of_mem hj)
  have h1 : (1 - x j) * pr (avoid Ev (S.erase j)) ≤ pr (avoid Ev S) := by
    conv_rhs => rw [← Finset.insert_erase hj]
    exact mul_pr_avoid_le_pr_avoid_insert (hbnd j (Finset.notMem_erase j S))
  exact (mul_pos (sub_pos.mpr (hx1 j)) hpos).trans_le h1

/-- The conditional bound `pr (Ev i ∩ avoid Ev S) ≤ x i * pr (avoid Ev S)`, granted the same
bound on strictly smaller index sets.  This is the inductive step of the local lemma. -/
private theorem pr_inter_avoid_le_of_forall_card_lt (hdet : ∀ i, Determined (supp i) (Ev i))
    (hx0 : ∀ i, 0 < x i) (hx1 : ∀ i, x i < 1)
    (hcond : ∀ i, pr (Ev i) ≤ x i * ∏ j ∈ nbr supp i, (1 - x j)) (S : Finset I)
    (IH : ∀ T : Finset I, T.card < S.card →
      ∀ i ∉ T, pr (Ev i ∩ avoid Ev T) ≤ x i * pr (avoid Ev T))
    {i : I} (hi : i ∉ S) :
    pr (Ev i ∩ avoid Ev S) ≤ x i * pr (avoid Ev S) := by
  -- the events indexed outside `nbr supp i` are independent of `Ev i`
  have hind : pr (Ev i ∩ avoid Ev (S \ nbr supp i))
      = pr (Ev i) * pr (avoid Ev (S \ nbr supp i)) :=
    pr_inter_of_disjoint_support (hdet i) (determined_avoid hdet _)
      (disjoint_supp_sup_sdiff_nbr hi)
  -- the neighbourhood product only shrinks when restricted to `S`
  have hkey : pr (Ev i) ≤ x i * ∏ j ∈ S ∩ nbr supp i, (1 - x j) :=
    (hcond i).trans <| mul_le_mul_of_nonneg_left
      (Finset.prod_le_prod_of_subset_of_le_one₀ Finset.inter_subset_right
        (fun j _ ↦ sub_nonneg.mpr (hx1 j).le) fun j _ _ ↦ sub_le_self _ (hx0 j).le) (hx0 i).le
  -- the telescoping lower bound on `pr (avoid Ev S)`
  have htel : (∏ j ∈ S ∩ nbr supp i, (1 - x j)) * pr (avoid Ev (S \ nbr supp i))
      ≤ pr (avoid Ev S) := by
    conv_rhs => rw [← Finset.sdiff_union_inter S (nbr supp i)]
    refine le_pr_avoid_union Ev x (fun j ↦ (hx1 j).le) _ _ fun T' hT' j hjS₁ hjT' ↦ ?_
    obtain ⟨hjS, hjnbr⟩ := Finset.mem_inter.mp hjS₁
    have hjmem : j ∉ S \ nbr supp i ∪ T' := fun h ↦
      (Finset.mem_union.mp h).elim (fun h' ↦ (Finset.mem_sdiff.mp h').2 hjnbr) hjT'
    refine IH _ ((Finset.card_le_card (Finset.subset_erase.mpr ⟨Finset.union_subset
      Finset.sdiff_subset (hT'.trans Finset.inter_subset_left), hjmem⟩)).trans_lt
      (Finset.card_erase_lt_of_mem hjS)) j hjmem
  calc pr (Ev i ∩ avoid Ev S)
      ≤ pr (Ev i ∩ avoid Ev (S \ nbr supp i)) :=
        pr_mono (Finset.inter_subset_inter_left (avoid_anti Finset.sdiff_subset))
    _ = pr (Ev i) * pr (avoid Ev (S \ nbr supp i)) := hind
    _ ≤ (x i * ∏ j ∈ S ∩ nbr supp i, (1 - x j)) * pr (avoid Ev (S \ nbr supp i)) :=
        mul_le_mul_of_nonneg_right hkey (pr_nonneg _)
    _ = x i * ((∏ j ∈ S ∩ nbr supp i, (1 - x j)) * pr (avoid Ev (S \ nbr supp i))) :=
        mul_assoc _ _ _
    _ ≤ x i * pr (avoid Ev S) := mul_le_mul_of_nonneg_left htel (hx0 i).le

/-- The two halves of the local-lemma induction, proved simultaneously by strong induction
on the size of the index set. -/
private theorem pr_avoid_pos_and_inter_le (hdet : ∀ i, Determined (supp i) (Ev i))
    (hx0 : ∀ i, 0 < x i) (hx1 : ∀ i, x i < 1)
    (hcond : ∀ i, pr (Ev i) ≤ x i * ∏ j ∈ nbr supp i, (1 - x j)) (S : Finset I) :
    0 < pr (avoid Ev S) ∧ ∀ i ∉ S, pr (Ev i ∩ avoid Ev S) ≤ x i * pr (avoid Ev S) := by
  generalize hn : S.card = n
  induction n using Nat.strong_induction_on generalizing S with
  | h n ih =>
    have IH : ∀ T : Finset I, T.card < S.card →
        0 < pr (avoid Ev T) ∧ ∀ i ∉ T, pr (Ev i ∩ avoid Ev T) ≤ x i * pr (avoid Ev T) :=
      fun T hT ↦ ih T.card (hn ▸ hT) T rfl
    exact ⟨pr_avoid_pos_of_forall_card_lt Ev x hx1 S IH, fun i hi ↦
      pr_inter_avoid_le_of_forall_card_lt Ev supp x hdet hx0 hx1 hcond S
        (fun T hT ↦ (IH T hT).2) hi⟩

/-- **The asymmetric Lovász local lemma** (Section 10.2 of `bs_lambda.txt`).  If each bad
event `Ev i` is determined by `supp i` and has probability at most
`x i * ∏ j ∈ nbr supp i, (1 - x j)` for some weights `x i ∈ (0, 1)`, then with positive
probability no bad event occurs. -/
theorem pr_avoid_pos (hdet : ∀ i, Determined (supp i) (Ev i))
    (hx0 : ∀ i, 0 < x i) (hx1 : ∀ i, x i < 1)
    (hcond : ∀ i, pr (Ev i) ≤ x i * ∏ j ∈ nbr supp i, (1 - x j)) :
    0 < pr (Finset.univ.filter fun ω ↦ ∀ i, ω ∉ Ev i) := by
  rw [← avoid_univ]
  exact (pr_avoid_pos_and_inter_le Ev supp x hdet hx0 hx1 hcond Finset.univ).1

end Main

/-! ## The two-type form -/

section TwoType

/-- The two-type asymmetric local lemma of Section 10.2 of `bs_lambda.txt`.  Each event has a
type `ty i : Bool`, and events of type `t` have probability at most `p t` and at most `D t s`
neighbours of type `s`. -/
theorem pr_avoid_pos_two_type (Ev : I → Finset (Cfg β)) (supp : I → Finset A)
    (hdet : ∀ i, Determined (supp i) (Ev i)) (ty : I → Bool)
    (p x : Bool → ℝ) (D : Bool → Bool → ℕ)
    (hp : ∀ i, pr (Ev i) ≤ p (ty i))
    (hD : ∀ i t, ((nbr supp i).filter fun j ↦ ty j = t).card ≤ D (ty i) t)
    (hx0 : ∀ t, 0 < x t) (hx1 : ∀ t, x t < 1)
    (hcond : ∀ t, p t ≤ x t * (1 - x false) ^ D t false * (1 - x true) ^ D t true) :
    0 < pr (Finset.univ.filter fun ω ↦ ∀ i, ω ∉ Ev i) := by
  refine pr_avoid_pos Ev supp (fun i ↦ x (ty i)) hdet (fun i ↦ hx0 _) (fun i ↦ hx1 _) fun i ↦ ?_
  set T : Finset I := nbr supp i
  have hnn (t : Bool) : (0 : ℝ) ≤ 1 - x t := sub_nonneg.mpr (hx1 t).le
  -- each type class contributes the constant factor `1 - x t`, raised to the size of that class
  have hc (t : Bool) : (∏ j ∈ T.filter fun j ↦ ty j = t, (1 - x (ty j)))
      = (1 - x t) ^ (T.filter fun j ↦ ty j = t).card :=
    (Finset.prod_congr rfl fun j hj ↦ by rw [(Finset.mem_filter.mp hj).2]).trans
      (Finset.prod_const _)
  have hb (t : Bool) : (1 - x t) ^ D (ty i) t
      ≤ (1 - x t) ^ (T.filter fun j ↦ ty j = t).card :=
    pow_le_pow_of_le_one (hnn t) (sub_le_self _ (hx0 t).le) (hD i t)
  -- splitting the neighbourhood product into its two type classes
  have hprod : (1 - x false) ^ D (ty i) false * (1 - x true) ^ D (ty i) true
      ≤ ∏ j ∈ T, (1 - x (ty j)) := by
    rw [← Finset.prod_filter_mul_prod_filter_not T (fun j ↦ ty j = false)]
    simp only [Bool.not_eq_false, hc false, hc true]
    exact mul_le_mul (hb false) (hb true) (pow_nonneg (hnn true) _) (pow_nonneg (hnn false) _)
  calc pr (Ev i) ≤ p (ty i) := hp i
    _ ≤ x (ty i) * (1 - x false) ^ D (ty i) false * (1 - x true) ^ D (ty i) true := hcond (ty i)
    _ = x (ty i) * ((1 - x false) ^ D (ty i) false * (1 - x true) ^ D (ty i) true) :=
        mul_assoc _ _ _
    _ ≤ x (ty i) * ∏ j ∈ T, (1 - x (ty j)) := mul_le_mul_of_nonneg_left hprod (hx0 (ty i)).le

end TwoType

/-! ## Pinning coordinates whose targets depend on other coordinates -/

section Fibre

variable {G : Finset A}

/-- The event that a configuration agrees on `G` with the partial configuration `c`. -/
def fibre (G : Finset A) (c : (a : A) → a ∈ G → β a) : Finset (Cfg β) :=
  Finset.univ.filter fun ω : Cfg β ↦ ∀ a, ∀ ha : a ∈ G, ω a = c a ha

omit [∀ (a : A), Nonempty (β a)] in
/-- Membership in a fibre. -/
@[simp] theorem mem_fibre {c : (a : A) → a ∈ G → β a} {ω : Cfg β} :
    ω ∈ fibre G c ↔ ∀ a, ∀ ha : a ∈ G, ω a = c a ha := by
  simp [fibre]

omit [∀ (a : A), Nonempty (β a)] in
/-- Every configuration lies in the fibre over its own restriction to `G`. -/
theorem mem_fibre_restrict (ω : Cfg β) : ω ∈ fibre G fun a _ ↦ ω a := by
  simp

omit [∀ (a : A), Nonempty (β a)] in
/-- A fibre over `G` is determined by `G`. -/
theorem determined_fibre (c : (a : A) → a ∈ G → β a) : Determined G (fibre G c) :=
  determined_filter_univ _ fun _ _ h ↦
    forall_congr' fun a ↦ forall_congr' fun ha ↦ by rw [h a ha]

omit [∀ (a : A), Nonempty (β a)] in
/-- Distinct partial configurations have disjoint fibres. -/
theorem disjoint_fibre {c c' : (a : A) → a ∈ G → β a} (h : c ≠ c') :
    Disjoint (fibre G c) (fibre G c') := by
  simp only [Finset.disjoint_left, mem_fibre]
  exact fun ω h1 h2 ↦ h (funext fun a ↦ funext fun ha ↦ (h1 a ha).symm.trans (h2 a ha))

/-- The fibres over `G` partition the configuration space, so their probabilities sum to `1`. -/
theorem sum_pr_fibre (G : Finset A) :
    ∑ c ∈ G.pi fun a ↦ (Finset.univ : Finset (β a)), pr (fibre G c) = 1 := by
  have hcover : (G.pi fun a ↦ (Finset.univ : Finset (β a))).biUnion (fibre G)
      = (Finset.univ : Finset (Cfg β)) :=
    Finset.eq_univ_of_forall fun ω ↦ Finset.mem_biUnion.mpr
      ⟨fun a _ ↦ ω a, Finset.mem_pi.mpr fun a _ ↦ Finset.mem_univ _, mem_fibre_restrict ω⟩
  rw [← pr_biUnion fun c _ c' _ hne ↦ disjoint_fibre hne, hcover, pr_univ]

end Fibre

section Pinned

omit [∀ a, DecidableEq (β a)] in
/-- **Pinning with targets read off other coordinates.**  If, on the event `E`, every
coordinate of `T` lands in a target set of size at most `m` that depends only on the
coordinates of a set `G` disjoint from `T`, then `E` has probability at most
`∏ a ∈ T, m / |β a|`.  This is the counting form of "condition on `G`; the coordinates of
`T` are still independent and uniform". -/
theorem pr_le_prod_of_pinned {G T : Finset A} (hGT : Disjoint G T)
    (tgt : ((a : A) → a ∈ G → β a) → (a : A) → Finset (β a)) (m : ℕ)
    (hm : ∀ c, ∀ a ∈ T, (tgt c a).card ≤ m) {E : Finset (Cfg β)}
    (hE : ∀ ω ∈ E, ∀ a ∈ T, ω a ∈ tgt (fun b _ ↦ ω b) a) :
    pr E ≤ ∏ a ∈ T, (m : ℝ) / (Fintype.card (β a) : ℝ) := by
  classical
  set C : Finset ((a : A) → a ∈ G → β a) := G.pi fun a ↦ (Finset.univ : Finset (β a))
  set P : ((a : A) → a ∈ G → β a) → Finset (Cfg β) :=
    fun c ↦ Finset.univ.filter fun ω : Cfg β ↦ ∀ a ∈ T, ω a ∈ tgt c a
  have hsub : E ⊆ C.biUnion fun c ↦ fibre G c ∩ P c := fun ω hω ↦
    Finset.mem_biUnion.mpr ⟨fun a _ ↦ ω a, Finset.mem_pi.mpr fun a _ ↦ Finset.mem_univ _,
      Finset.mem_inter.mpr ⟨mem_fibre_restrict ω, (Finset.mem_filter_univ ω).mpr (hE ω hω)⟩⟩
  calc pr E ≤ ∑ c ∈ C, pr (fibre G c ∩ P c) := pr_le_of_subset_biUnion C _ hsub
    _ = ∑ c ∈ C, pr (fibre G c) * pr (P c) := Finset.sum_congr rfl fun c _ ↦
        pr_inter_of_disjoint_support (determined_fibre c) (determined_pin T (tgt c)) hGT
    _ ≤ ∑ c ∈ C, pr (fibre G c) * ∏ a ∈ T, (m : ℝ) / (Fintype.card (β a) : ℝ) :=
        Finset.sum_le_sum fun c _ ↦
          mul_le_mul_of_nonneg_left (pr_pin_le T (tgt c) m (hm c)) (pr_nonneg _)
    _ = ∏ a ∈ T, (m : ℝ) / (Fintype.card (β a) : ℝ) := by
        rw [← Finset.sum_mul, sum_pr_fibre, one_mul]

omit [∀ a, DecidableEq (β a)] in
/-- The constant-alphabet form of `pr_le_prod_of_pinned`, as used in Sections 8.1 and 9. -/
theorem pr_le_pow_of_pinned {G T : Finset A} (hGT : Disjoint G T) (N : ℕ)
    (hN : ∀ a ∈ T, Fintype.card (β a) = N)
    (tgt : ((a : A) → a ∈ G → β a) → (a : A) → Finset (β a)) (m : ℕ)
    (hm : ∀ c, ∀ a ∈ T, (tgt c a).card ≤ m) {E : Finset (Cfg β)}
    (hE : ∀ ω ∈ E, ∀ a ∈ T, ω a ∈ tgt (fun b _ ↦ ω b) a) :
    pr E ≤ ((m : ℝ) / N) ^ T.card := by
  classical
  exact
  (pr_le_prod_of_pinned hGT tgt m hm hE).trans_eq <|
    (Finset.prod_congr rfl fun a ha ↦ by rw [hN a ha]).trans (Finset.prod_const _)

end Pinned

end BSLambda.LLL
