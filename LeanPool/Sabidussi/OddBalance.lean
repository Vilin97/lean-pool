/-
Copyright (c) 2026 Nikolay Ulyanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nikolay Ulyanov
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Equiv.Prod

/-!
# The odd balancing theorem

This file proves the parity lemma at the heart of the compatibility argument: for a symmetric,
row-cancelling interaction `b` over a finite vertex set, the number of frame assignments with no
obstruction at any vertex is odd, and in particular nonzero. The proof counts frame assignments
modulo two, expands the count over choices of partner vertices, and cancels the non-covering and
derangement contributions in pairs.
-/

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators
open Finset

namespace Sabidussi

namespace OddBalance

/-- The field with two elements, used for the parity counting argument. -/
abbrev F2 := ZMod 2

lemma F2.indicator_zero (a : F2) : (if a = 0 then 1 else 0) = 1 + a := by
  fin_cases a <;> decide

lemma F2.mul_self (a : F2) : a * a = a := by
  fin_cases a <;> decide

lemma F2.add_self (a : F2) : a + a = 0 := by
  fin_cases a <;> decide

section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The interaction obstruction at a vertex `v`: the sum over all other vertices `u` of the
pairwise interaction of the chosen frames at `v` and `u`. -/
def obstruction (b : V → V → Fin 3 → Fin 3 → F2) (x : V → Fin 3) (v : V) : F2 :=
  ∑ u ∈ Finset.univ.erase v, b v u (x v) (x u)

/-- The set of frame choices for which every vertex obstruction vanishes. -/
def solutions (b : V → V → Fin 3 → Fin 3 → F2) : Finset (V → Fin 3) :=
  Finset.univ.filter fun x => ∀ v, obstruction b x v = 0

lemma cast_solutions_card (b : V → V → Fin 3 → Fin 3 → F2) :
    ((solutions b).card : F2) =
      ∑ x : V → Fin 3, ∏ v : V, (1 + obstruction b x v) := by
  rw [solutions]
  calc
    ((Finset.univ.filter fun x : V → Fin 3 =>
        ∀ v, obstruction b x v = 0).card : F2) =
        ∑ x : V → Fin 3, if ∀ v, obstruction b x v = 0 then 1 else 0 := by
          simp [Finset.sum_boole]
    _ = ∑ x : V → Fin 3, ∏ v : V, (1 + obstruction b x v) := by
      apply Fintype.sum_congr
      intro x
      rw [show (if ∀ v, obstruction b x v = 0 then 1 else 0 : F2) =
          ∏ v : V, if obstruction b x v = 0 then 1 else 0 by
            simpa only [Finset.mem_univ, forall_const]
              using (Finset.prod_boole
                (s := Finset.univ) (p := fun v : V => obstruction b x v = 0)).symm]
      congr 1
      funext v
      exact F2.indicator_zero _

omit [DecidableEq V] in
lemma prod_one_add_expand (q : V → F2) :
    (∏ v : V, (1 + q v)) =
      ∑ S ∈ Finset.univ.powerset, ∏ v ∈ S, q v := by
  classical
  simpa [add_comm] using Finset.prod_add q (fun _ : V => (1 : F2)) Finset.univ

lemma sum_prod_one_add_expand (q : (V → Fin 3) → V → F2) :
    (∑ x : V → Fin 3, ∏ v : V, (1 + q x v)) =
      ∑ S ∈ Finset.univ.powerset, ∑ x : V → Fin 3, ∏ v ∈ S, q x v := by
  simp_rw [prod_one_add_expand]
  exact Finset.sum_comm

omit [Fintype V] in
lemma prod_sum_expand (S : Finset V) (t : V → Finset V) (a : V → V → F2) :
    (∏ v ∈ S, ∑ u ∈ t v, a v u) =
      ∑ f : (v : {v // v ∈ S}) → {u // u ∈ t v},
        ∏ v : {v // v ∈ S}, a v (f v) := by
  rw [Finset.prod_subtype S (fun _ => Iff.rfl)]
  · simp_rw [Finset.sum_subtype (t _) (fun _ => Iff.rfl)]
    exact Fintype.prod_sum (fun v : {v // v ∈ S} =>
      fun u : {u // u ∈ t v} => a v u)

/-- A choice, for each vertex of `S`, of a distinct partner vertex. -/
abbrev Choice (S : Finset V) :=
  (v : {v // v ∈ S}) → {u : V // u ≠ v}

/-- The product over `S` of the pairwise interactions along a choice of partners. -/
def choiceTerm (b : V → V → Fin 3 → Fin 3 → F2) (S : Finset V)
    (f : Choice S) (x : V → Fin 3) : F2 :=
  ∏ v : {v // v ∈ S}, b v (f v) (x v) (x (f v))

lemma obstruction_product_expand
    (b : V → V → Fin 3 → Fin 3 → F2) (S : Finset V) (x : V → Fin 3) :
    (∏ v ∈ S, obstruction b x v) =
      ∑ f : Choice S, choiceTerm b S f x := by
  rw [Finset.prod_subtype S (fun _ => Iff.rfl)]
  · have hsum (v : V) :
        (∑ u ∈ Finset.univ.erase v, b v u (x v) (x u)) =
          ∑ u : {u : V // u ≠ v}, b v u (x v) (x u) := by
      exact Finset.sum_subtype (Finset.univ.erase v) (by simp)
        (fun u => b v u (x v) (x u))
    simp_rw [obstruction, hsum]
    exact Fintype.prod_sum (fun v : {v // v ∈ S} =>
      fun u : {u : V // u ≠ v} => b v u (x v) (x u))

/-- The sum over all frame assignments of the choice term of a fixed choice of partners. -/
def totalChoiceTerm (b : V → V → Fin 3 → Fin 3 → F2)
    (S : Finset V) (f : Choice S) : F2 :=
  ∑ x : V → Fin 3, choiceTerm b S f x

lemma sum_obstruction_product_expand
    (b : V → V → Fin 3 → Fin 3 → F2) (S : Finset V) :
    (∑ x : V → Fin 3, ∏ v ∈ S, obstruction b x v) =
      ∑ f : Choice S, totalChoiceTerm b S f := by
  simp_rw [obstruction_product_expand]
  exact Finset.sum_comm

lemma sum_fun_split_at {A M : Type*} [Fintype A] [AddCommMonoid M]
    (w : V) (F : (V → A) → M) :
    (∑ x : V → A, F x) =
      ∑ a : A, ∑ y : ({v : V // v ≠ w} → A),
        F ((Equiv.funSplitAt w A).symm (a, y)) := by
  calc
    (∑ x : V → A, F x) =
        ∑ p : A × ({v : V // v ≠ w} → A),
          F ((Equiv.funSplitAt w A).symm p) := by
            apply Fintype.sum_equiv (Equiv.funSplitAt w A)
            intro x
            exact congrArg F ((Equiv.funSplitAt w A).symm_apply_apply x).symm
    _ = _ := Fintype.sum_prod_type _

lemma Fintype.prod_eq_mul_mul_prod_compl_pair {M : Type*} [CommMonoid M]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (a b : ι) (h : a ≠ b) (g : ι → M) :
    (∏ i, g i) = g a * g b * ∏ i ∈ ({a, b} : Finset ι)ᶜ, g i := by
  rw [Fintype.prod_eq_mul_prod_compl a]
  rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (by simpa using h.symm)]
  have hset : ({a} : Finset ι)ᶜ \ {b} = ({a, b} : Finset ι)ᶜ := by
    ext i
    simp only [Finset.mem_sdiff, Finset.mem_compl, Finset.mem_singleton,
      Finset.mem_insert, not_or]
  rw [hset, mul_assoc]

lemma totalChoiceTerm_eq_zero_of_source_leaf
    (b : V → V → Fin 3 → Fin 3 → F2)
    (hsymm : ∀ v u a c, b v u a c = b u v c a)
    (hrow : ∀ v u a, ∑ c : Fin 3, b v u a c = 0)
    (S : Finset V) (f : Choice S) (v₀ : {v // v ∈ S}) (w : V)
    (hw : (v₀ : V) = w) (hnotTarget : ∀ v, (f v : V) ≠ w) :
    totalChoiceTerm b S f = 0 := by
  rw [totalChoiceTerm, sum_fun_split_at w]
  rw [Finset.sum_comm]
  apply Fintype.sum_eq_zero
  intro y
  let x₀ : V → Fin 3 := (Equiv.funSplitAt w (Fin 3)).symm (0, y)
  let C : F2 := ∏ v ∈ ({v₀} : Finset {v // v ∈ S})ᶜ,
    b v (f v) (x₀ v) (x₀ (f v))
  have hfactor (a : Fin 3) :
      choiceTerm b S f ((Equiv.funSplitAt w (Fin 3)).symm (a, y)) =
        b w (f v₀) a (y ⟨f v₀, hnotTarget v₀⟩) * C := by
    rw [choiceTerm, Fintype.prod_eq_mul_prod_compl v₀]
    congr 1
    · simp [Equiv.funSplitAt_symm_apply, hw, hnotTarget]
    · apply Finset.prod_congr rfl
      intro v hv
      have hvne : v ≠ v₀ := by simpa using hv
      have hvw : (v : V) ≠ w := by
        intro h
        apply hvne
        apply Subtype.ext
        simpa [hw] using h
      simp [x₀, Equiv.funSplitAt_symm_apply, hvw, hnotTarget]
  simp_rw [hfactor]
  rw [← Finset.sum_mul]
  suffices (∑ a : Fin 3, b w (f v₀) a (y ⟨f v₀, hnotTarget v₀⟩)) = 0 by
    rw [this, zero_mul]
  calc
    (∑ a : Fin 3, b w (f v₀) a (y ⟨f v₀, hnotTarget v₀⟩)) =
        ∑ a : Fin 3, b (f v₀) w (y ⟨f v₀, hnotTarget v₀⟩) a := by
          apply Fintype.sum_congr
          intro a
          exact hsymm _ _ _ _
    _ = 0 := hrow (f v₀) w (y ⟨f v₀, hnotTarget v₀⟩)

lemma totalChoiceTerm_eq_zero_of_target_leaf
    (b : V → V → Fin 3 → Fin 3 → F2)
    (hrow : ∀ v u a, ∑ c : Fin 3, b v u a c = 0)
    (S : Finset V) (f : Choice S) (v₀ : {v // v ∈ S}) (w : V)
    (hw : (f v₀ : V) = w) (hnotSource : ∀ v, (v : V) ≠ w)
    (huniqueTarget : ∀ v, (f v : V) = w → v = v₀) :
    totalChoiceTerm b S f = 0 := by
  rw [totalChoiceTerm, sum_fun_split_at w]
  rw [Finset.sum_comm]
  apply Fintype.sum_eq_zero
  intro y
  let x₀ : V → Fin 3 := (Equiv.funSplitAt w (Fin 3)).symm (0, y)
  let C : F2 := ∏ v ∈ ({v₀} : Finset {v // v ∈ S})ᶜ,
    b v (f v) (x₀ v) (x₀ (f v))
  have hfactor (a : Fin 3) :
      choiceTerm b S f ((Equiv.funSplitAt w (Fin 3)).symm (a, y)) =
        b v₀ w (y ⟨v₀, hnotSource v₀⟩) a * C := by
    rw [choiceTerm, Fintype.prod_eq_mul_prod_compl v₀]
    congr 1
    · simp [Equiv.funSplitAt_symm_apply, hw, hnotSource]
    · apply Finset.prod_congr rfl
      intro v hv
      have hvne : v ≠ v₀ := by simpa using hv
      have hfw : (f v : V) ≠ w := by
        intro h
        exact hvne (huniqueTarget v h)
      simp [x₀, Equiv.funSplitAt_symm_apply, hnotSource]
  simp_rw [hfactor]
  rw [← Finset.sum_mul]
  rw [hrow, zero_mul]

lemma totalChoiceTerm_eq_zero_of_twoCycle
    (b : V → V → Fin 3 → Fin 3 → F2)
    (hsymm : ∀ v u a c, b v u a c = b u v c a)
    (hrow : ∀ v u a, ∑ c : Fin 3, b v u a c = 0)
    (S : Finset V) (f : Choice S) (v₀ v₁ : {v // v ∈ S})
    (hne : v₀ ≠ v₁)
    (hf₀ : (f v₀ : V) = v₁) (hf₁ : (f v₁ : V) = v₀)
    (_hu₀ : ∀ v, (f v : V) = v₀ → v = v₁)
    (hu₁ : ∀ v, (f v : V) = v₁ → v = v₀) :
    totalChoiceTerm b S f = 0 := by
  have hvne : (v₀ : V) ≠ v₁ := by
    intro h
    exact hne (Subtype.ext h)
  rw [totalChoiceTerm, sum_fun_split_at (v₁ : V)]
  rw [Finset.sum_comm]
  apply Fintype.sum_eq_zero
  intro y
  let x₀ : V → Fin 3 := (Equiv.funSplitAt (v₁ : V) (Fin 3)).symm (0, y)
  let C : F2 := ∏ v ∈ ({v₀, v₁} : Finset {v // v ∈ S})ᶜ,
    b v (f v) (x₀ v) (x₀ (f v))
  have hfactor (a : Fin 3) :
      choiceTerm b S f ((Equiv.funSplitAt (v₁ : V) (Fin 3)).symm (a, y)) =
        b v₀ v₁ (y ⟨v₀, hvne⟩) a * C := by
    rw [choiceTerm, Fintype.prod_eq_mul_mul_prod_compl_pair v₀ v₁ hne]
    have hfac₀ :
        b v₀ (f v₀)
          ((Equiv.funSplitAt (v₁ : V) (Fin 3)).symm (a, y) v₀)
          ((Equiv.funSplitAt (v₁ : V) (Fin 3)).symm (a, y) (f v₀)) =
          b v₀ v₁ (y ⟨v₀, hvne⟩) a := by
      simp [Equiv.funSplitAt_symm_apply, hf₀, hvne]
    have hfac₁ :
        b v₁ (f v₁)
          ((Equiv.funSplitAt (v₁ : V) (Fin 3)).symm (a, y) v₁)
          ((Equiv.funSplitAt (v₁ : V) (Fin 3)).symm (a, y) (f v₁)) =
          b v₀ v₁ (y ⟨v₀, hvne⟩) a := by
      rw [hsymm]
      simp [Equiv.funSplitAt_symm_apply, hf₁, hvne]
    rw [hfac₀, hfac₁, F2.mul_self]
    congr 1
    apply Finset.prod_congr rfl
    intro v hv
    have hvpair : v ≠ v₀ ∧ v ≠ v₁ := by simpa using hv
    have hv₀ : v ≠ v₀ := hvpair.1
    have hv₁ : v ≠ v₁ := hvpair.2
    have hvw : (v : V) ≠ v₁ := by
      intro h
      exact hv₁ (Subtype.ext h)
    have hfw : (f v : V) ≠ v₁ := by
      intro h
      exact hv₀ (hu₁ v h)
    simp [x₀, Equiv.funSplitAt_symm_apply, hvw, hfw]
  simp_rw [hfactor]
  rw [← Finset.sum_mul]
  rw [hrow, zero_mul]

/-- A derangement of the vertices of `S`: a fixed-point-free permutation. -/
def Derangement (S : Finset V) :=
  {σ : Equiv.Perm {v // v ∈ S} // ∀ v, σ v ≠ v}

noncomputable instance Derangement.instFintype (S : Finset V) : Fintype (Derangement S) :=
  Fintype.ofInjective
    (fun d : Derangement S => (d.1 : {v // v ∈ S} → {v // v ∈ S})) <| by
      intro d e h
      apply Subtype.ext
      apply Equiv.ext
      exact congrFun h

/-- The choice of partners induced by a derangement: each vertex is sent to its image. -/
def Derangement.choice {S : Finset V} (d : Derangement S) : Choice S :=
  fun v => ⟨d.1 v, by
    intro h
    exact d.2 v (Subtype.ext h)⟩

/-- The inverse derangement. -/
def Derangement.inv {S : Finset V} (d : Derangement S) : Derangement S :=
  ⟨d.1.symm, fun v h => d.2 v <| by
    calc
      d.1 v = d.1 (d.1.symm v) := congrArg d.1 h.symm
      _ = v := d.1.apply_symm_apply v⟩

omit [DecidableEq V] [Fintype V] in
lemma Derangement.inv_inv {S : Finset V} (d : Derangement S) : d.inv.inv = d := by
  apply Subtype.ext
  exact d.1.symm_symm

omit [DecidableEq V] [Fintype V] in
lemma choiceTerm_derangement_inv
    (b : V → V → Fin 3 → Fin 3 → F2)
    (hsymm : ∀ v u a c, b v u a c = b u v c a)
    (S : Finset V) (d : Derangement S) (x : V → Fin 3) :
    choiceTerm b S d.inv.choice x = choiceTerm b S d.choice x := by
  rw [choiceTerm, choiceTerm]
  calc
    (∏ v : {v // v ∈ S},
        b v (d.inv.choice v) (x v) (x (d.inv.choice v))) =
        ∏ v : {v // v ∈ S},
          b (d.1.symm v) v (x (d.1.symm v)) (x v) := by
            apply Fintype.prod_congr
            intro v
            exact hsymm _ _ _ _
    _ = ∏ v : {v // v ∈ S}, b v (d.choice v) (x v) (x (d.choice v)) := by
      simpa [Derangement.choice, Derangement.inv] using
        (d.1.symm.prod_comp (fun v : {v // v ∈ S} =>
          b v (d.1 v) (x v) (x (d.1 v))))

lemma totalChoiceTerm_derangement_inv
    (b : V → V → Fin 3 → Fin 3 → F2)
    (hsymm : ∀ v u a c, b v u a c = b u v c a)
    (S : Finset V) (d : Derangement S) :
    totalChoiceTerm b S d.inv.choice = totalChoiceTerm b S d.choice := by
  apply Fintype.sum_congr
  intro x
  exact choiceTerm_derangement_inv b hsymm S d x

lemma totalChoiceTerm_eq_zero_of_derangement_inv_eq_self
    (b : V → V → Fin 3 → Fin 3 → F2)
    (hsymm : ∀ v u a c, b v u a c = b u v c a)
    (hrow : ∀ v u a, ∑ c : Fin 3, b v u a c = 0)
    (S : Finset V) (hS : S.Nonempty) (d : Derangement S) (hd : d.inv = d) :
    totalChoiceTerm b S d.choice = 0 := by
  let v₀ : {v // v ∈ S} := ⟨hS.choose, hS.choose_spec⟩
  let v₁ : {v // v ∈ S} := d.1 v₀
  have hne : v₀ ≠ v₁ := (d.2 v₀).symm
  have hsigma : d.1.symm = d.1 := congrArg Subtype.val hd
  have hcycle : d.1 v₁ = v₀ := by
    have h := d.1.symm_apply_apply v₀
    rw [hsigma] at h
    exact h
  apply totalChoiceTerm_eq_zero_of_twoCycle b hsymm hrow S d.choice v₀ v₁ hne
  · rfl
  · exact congrArg Subtype.val hcycle
  · intro v hv
    apply d.1.injective
    calc
      d.1 v = v₀ := Subtype.ext hv
      _ = d.1 v₁ := hcycle.symm
  · intro v hv
    apply d.1.injective
    calc
      d.1 v = v₁ := Subtype.ext hv
      _ = d.1 v₀ := rfl

/-- A choice of partners whose image covers every vertex of `S`. -/
def CoveredChoice (S : Finset V) :=
  {f : Choice S // ∀ w : {w // w ∈ S}, ∃ v, (f v : V) = w}

noncomputable instance CoveredChoice.instFintype (S : Finset V) :
    Fintype (CoveredChoice S) :=
  Fintype.ofInjective (fun f : CoveredChoice S => f.1) Subtype.val_injective

/-- A covering choice of partners is a bijection, hence a derangement. -/
noncomputable def CoveredChoice.toDerangement {S : Finset V}
    (c : CoveredChoice S) : Derangement S := by
  let r : {w // w ∈ S} → {v // v ∈ S} := fun w => Classical.choose (c.2 w)
  have hr (w : {w // w ∈ S}) : (c.1 (r w) : V) = w :=
    Classical.choose_spec (c.2 w)
  have rinj : Function.Injective r := by
    intro w z h
    apply Subtype.ext
    calc
      (w : V) = c.1 (r w) := (hr w).symm
      _ = c.1 (r z) := by rw [h]
      _ = z := hr z
  have rsurj : Function.Surjective r :=
    (Finite.injective_iff_surjective.mp rinj)
  have hmem (v : {v // v ∈ S}) : (c.1 v : V) ∈ S := by
    obtain ⟨w, rfl⟩ := rsurj v
    rw [hr]
    exact w.2
  let g : {v // v ∈ S} → {v // v ∈ S} := fun v => ⟨c.1 v, hmem v⟩
  have gsurj : Function.Surjective g := by
    intro w
    obtain ⟨v, hv⟩ := c.2 w
    exact ⟨v, Subtype.ext hv⟩
  let σ : Equiv.Perm {v // v ∈ S} :=
    Equiv.ofBijective g ((Fintype.bijective_iff_surjective_and_card g).2 ⟨gsurj, rfl⟩)
  exact ⟨σ, fun v hv => (c.1 v).2 <| by
    have := congrArg Subtype.val hv
    exact this⟩

/-- The covering choice of partners underlying a derangement. -/
def Derangement.toCoveredChoice {S : Finset V} (d : Derangement S) : CoveredChoice S :=
  ⟨d.choice, fun w => ⟨d.1.symm w, by
    exact congrArg Subtype.val (d.1.apply_symm_apply w)⟩⟩

omit [DecidableEq V] in
lemma CoveredChoice.toDerangement_choice {S : Finset V} (c : CoveredChoice S) :
    c.toDerangement.choice = c.1 := by
  funext v
  apply Subtype.ext
  rfl

omit [DecidableEq V] [Fintype V] in
lemma Derangement.choice_injective {S : Finset V} :
    Function.Injective (fun d : Derangement S => d.choice) := by
  intro d e h
  apply Subtype.ext
  apply Equiv.ext
  intro v
  apply Subtype.ext
  simpa [Derangement.choice] using congrArg Subtype.val (congrFun h v)

/-- Covering choices of partners and derangements are in bijection. -/
noncomputable def coveredChoiceEquivDerangement (S : Finset V) :
    CoveredChoice S ≃ Derangement S where
  toFun := CoveredChoice.toDerangement
  invFun := Derangement.toCoveredChoice
  left_inv c := by
    apply Subtype.ext
    exact CoveredChoice.toDerangement_choice c
  right_inv d := by
    apply Derangement.choice_injective
    exact CoveredChoice.toDerangement_choice d.toCoveredChoice

lemma sum_derangement_totalChoiceTerm_eq_zero
    (b : V → V → Fin 3 → Fin 3 → F2)
    (hsymm : ∀ v u a c, b v u a c = b u v c a)
    (hrow : ∀ v u a, ∑ c : Fin 3, b v u a c = 0)
    (S : Finset V) (hS : S.Nonempty) :
    (∑ d : Derangement S, totalChoiceTerm b S d.choice) = 0 := by
  classical
  apply Finset.sum_involution (s := Finset.univ)
    (f := fun d : Derangement S => totalChoiceTerm b S d.choice)
    (g := fun d _ => d.inv)
  · intro d _
    rw [totalChoiceTerm_derangement_inv b hsymm S d]
    exact F2.add_self _
  · intro d _ hdne hinv
    apply hdne
    exact totalChoiceTerm_eq_zero_of_derangement_inv_eq_self
      b hsymm hrow S hS d hinv
  · simp
  · intro d _
    exact Derangement.inv_inv d

lemma sum_coveredChoice_totalChoiceTerm_eq_zero
    (b : V → V → Fin 3 → Fin 3 → F2)
    (hsymm : ∀ v u a c, b v u a c = b u v c a)
    (hrow : ∀ v u a, ∑ c : Fin 3, b v u a c = 0)
    (S : Finset V) (hS : S.Nonempty) :
    (∑ c : CoveredChoice S, totalChoiceTerm b S c.1) = 0 := by
  calc
    (∑ c : CoveredChoice S, totalChoiceTerm b S c.1) =
        ∑ d : Derangement S, totalChoiceTerm b S d.choice := by
          apply Fintype.sum_equiv (coveredChoiceEquivDerangement S)
          intro c
          change totalChoiceTerm b S c.1 =
            totalChoiceTerm b S c.toDerangement.choice
          exact congrArg (totalChoiceTerm b S)
            (CoveredChoice.toDerangement_choice c).symm
    _ = 0 := sum_derangement_totalChoiceTerm_eq_zero b hsymm hrow S hS

lemma sum_choice_totalChoiceTerm_eq_zero
    (b : V → V → Fin 3 → Fin 3 → F2)
    (hsymm : ∀ v u a c, b v u a c = b u v c a)
    (hrow : ∀ v u a, ∑ c : Fin 3, b v u a c = 0)
    (S : Finset V) (hS : S.Nonempty) :
    (∑ f : Choice S, totalChoiceTerm b S f) = 0 := by
  classical
  let covers : Choice S → Prop := fun f =>
    ∀ w : {w // w ∈ S}, ∃ v, (f v : V) = w
  have hgood :
      (∑ f ∈ Finset.univ.filter covers, totalChoiceTerm b S f) = 0 := by
    calc
      (∑ f ∈ Finset.univ.filter covers, totalChoiceTerm b S f) =
          ∑ c : CoveredChoice S, totalChoiceTerm b S c.1 := by
            exact Finset.sum_subtype (Finset.univ.filter covers) (by
              intro f
              simp [covers]) (fun f => totalChoiceTerm b S f)
      _ = 0 := sum_coveredChoice_totalChoiceTerm_eq_zero b hsymm hrow S hS
  have hbad :
      (∑ f ∈ Finset.univ.filter (fun f => ¬covers f), totalChoiceTerm b S f) = 0 := by
    apply Finset.sum_eq_zero
    intro f hf
    have hn : ¬covers f := (Finset.mem_filter.mp hf).2
    simp only [covers, not_forall, not_exists] at hn
    obtain ⟨w, hw⟩ := hn
    exact totalChoiceTerm_eq_zero_of_source_leaf b hsymm hrow S f w w rfl hw
  calc
    (∑ f : Choice S, totalChoiceTerm b S f) =
        (∑ f ∈ Finset.univ.filter covers, totalChoiceTerm b S f) +
          ∑ f ∈ Finset.univ.filter (fun f => ¬covers f), totalChoiceTerm b S f := by
            exact (Finset.sum_filter_add_sum_filter_not Finset.univ covers
              (fun f => totalChoiceTerm b S f)).symm
    _ = 0 := by rw [hgood, hbad, add_zero]

lemma sum_obstruction_product_eq_zero
    (b : V → V → Fin 3 → Fin 3 → F2)
    (hsymm : ∀ v u a c, b v u a c = b u v c a)
    (hrow : ∀ v u a, ∑ c : Fin 3, b v u a c = 0)
    (S : Finset V) (hS : S.Nonempty) :
    (∑ x : V → Fin 3, ∏ v ∈ S, obstruction b x v) = 0 := by
  rw [sum_obstruction_product_expand]
  exact sum_choice_totalChoiceTerm_eq_zero b hsymm hrow S hS

lemma sum_one_fin3_assignments : (∑ _x : V → Fin 3, (1 : F2)) = 1 := by
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
    Fintype.card_fin, nsmul_eq_mul, mul_one, Nat.cast_pow, Nat.cast_ofNat]
  rw [show (3 : F2) = 1 by decide]
  simp

theorem cast_solutions_card_eq_one
    (b : V → V → Fin 3 → Fin 3 → F2)
    (hsymm : ∀ v u a c, b v u a c = b u v c a)
    (hrow : ∀ v u a, ∑ c : Fin 3, b v u a c = 0) :
    ((solutions b).card : F2) = 1 := by
  rw [cast_solutions_card]
  rw [sum_prod_one_add_expand]
  rw [Finset.sum_eq_single ∅]
  · simpa using (sum_one_fin3_assignments (V := V))
  · intro S hSpow hSne
    apply sum_obstruction_product_eq_zero b hsymm hrow S
    simpa only [Finset.nonempty_iff_ne_empty] using hSne
  · simp

theorem solutions_card_odd
    (b : V → V → Fin 3 → Fin 3 → F2)
    (hsymm : ∀ v u a c, b v u a c = b u v c a)
    (hrow : ∀ v u a, ∑ c : Fin 3, b v u a c = 0) :
    Odd (solutions b).card :=
  ZMod.natCast_eq_one_iff_odd.mp (cast_solutions_card_eq_one b hsymm hrow)

/-- A symmetric row-cancelling interaction has a balanced choice at every vertex. -/
theorem exists_balanced
    (b : V → V → Fin 3 → Fin 3 → F2)
    (hsymm : ∀ v u a c, b v u a c = b u v c a)
    (hrow : ∀ v u a, ∑ c : Fin 3, b v u a c = 0) :
    ∃ x : V → Fin 3, ∀ v, obstruction b x v = 0 := by
  have hpos : 0 < (solutions b).card := (solutions_card_odd b hsymm hrow).pos
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
  refine ⟨x, ?_⟩
  simpa [solutions] using hx

end

end OddBalance

end Sabidussi
