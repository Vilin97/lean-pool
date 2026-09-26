/-
Copyright (c) 2026 Wouter Cames van Batenburg, Samuel Korsky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Cames van Batenburg, Samuel Korsky
-/

module

public import Mathlib.LinearAlgebra.Basis.Flag
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# A common ordered basis for two complete flags

This file isolates and proves the standard common-basis fact used as the first
step in the proof of Lemma 2.1 in Cames van Batenburg--Korsky.  It is not an
assumption: `common_apartment` constructs the basis and permutation, and
`common_basis_orderings` spells out the two prefix-span formulas
from the paper.

Lean Pool port of wewantmoore commit d59bd80ea93fabb9faf769e790ab47692645e022.
The port adds a namespace and adapts proofs to the current Mathlib APIs and repository style.
-/

@[expose] public section

namespace MooreBound

open Module

namespace DegreeDiameter

variable (K V : Type*) [DivisionRing K] [AddCommGroup V] [Module K V]

/-- A complete flag in an `n`-dimensional vector space, indexed by its ranks
`0, ..., n`. Both strictness and the rank condition are recorded explicitly,
ruling out degenerate chains. -/
structure CompleteFlag (n : ℕ) where
  /-- The subspace at each rank of the complete flag. -/
  space : Fin (n + 1) → Submodule K V
  strictMono_space : StrictMono space
  finrank_space : ∀ i, Module.finrank K (space i) = i
  space_zero : space 0 = ⊥
  space_last : space (Fin.last n) = ⊤

namespace CompleteFlag

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
  {n : ℕ}

instance : CoeFun (CompleteFlag K V n) (fun _ ↦ Fin (n + 1) → Submodule K V) :=
  ⟨CompleteFlag.space⟩

@[ext]
theorem ext {F G : CompleteFlag K V n} (h : ∀ i, F i = G i) : F = G := by
  cases F with
  | mk spaceF strictF rankF zeroF lastF =>
    cases G with
    | mk spaceG strictG rankG zeroG lastG =>
      have hspace : spaceF = spaceG := funext h
      cases hspace
      rfl

/-- The complete flag of prefix spans of an ordered basis. -/
noncomputable def ofBasis (b : Basis (Fin n) K V) : CompleteFlag K V n where
  space := b.flag
  strictMono_space := b.flag_strictMono
  finrank_space := by
    intro i
    classical
    rw [Module.Basis.flag,
      finrank_span_set_eq_card ((b.linearIndependent.linearIndepOn _).id_image)]
    rw [Set.toFinset_image, Finset.card_image_of_injective _ b.injective]
    rw [Set.toFinset_ofPred]
    change (Finset.filter (fun x : Fin n ↦ x.val < i.val) Finset.univ).card = i.val
    rw [Fin.card_filter_val_lt,
      Nat.min_eq_right (Nat.le_of_lt_succ i.isLt)]
  space_zero := b.flag_zero
  space_last := b.flag_last

end CompleteFlag

/-- The set of entries appearing before rank `i` in an ordering `σ`. -/
def PrefixSet {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin (n + 1)) : Set (Fin n) :=
  σ '' {j | j.castSucc < i}

theorem ofBasis_reindex_apply {n : ℕ} (b : Basis (Fin n) K V)
    (σ : Equiv.Perm (Fin n)) (i : Fin (n + 1)) :
    CompleteFlag.ofBasis (b.reindex σ.symm) i =
      Submodule.span K (b '' PrefixSet σ i) := by
  change (b.reindex σ.symm).flag i = _
  simp [Module.Basis.flag, PrefixSet, Module.Basis.coe_reindex,
    Set.image_image]

/-- Intersection ranks increase exactly where the second flag first contributes a new vector. -/
private theorem commonApartment_rankStep {n : ℕ} [FiniteDimensional K V]
    (F F' : CompleteFlag K V n) (σf : Fin n → Fin n)
    (hP_iff : ∀ i j, (∃ x : V, x ∈ F i.succ ∧ x ∈ F' j.succ ∧
      x ∉ F i.castSucc) ↔ σf i ≤ j) (i j : Fin n) :
    Module.finrank K ↥(F i.succ ⊓ F' j.succ) =
      Module.finrank K ↥(F i.castSucc ⊓ F' j.succ) +
        if σf i ≤ j then 1 else 0 := by
  classical
  by_cases hij : σf i ≤ j
  · rw [ite_eq_left hij]
    have hp : ∃ x : V, x ∈ F i.succ ∧ x ∈ F' j.succ ∧ x ∉ F i.castSucc := (hP_iff i j).2 hij
    obtain ⟨x, hxFi, hxFj, hxnot⟩ := hp
    let A : Submodule K V := F i.castSucc ⊓ F' j.succ
    let B : Submodule K V := F i.succ ⊓ F' j.succ
    have hABle : A ≤ B := inf_le_inf_right _ (F.strictMono_space.monotone
      (Fin.castSucc_lt_succ.le))
    have hABlt : A < B := lt_of_le_of_ne hABle (by
      intro hEq
      have hxA : x ∈ A := hEq ▸ show x ∈ B from ⟨hxFi, hxFj⟩
      exact hxnot hxA.1)
    have hrlt : Module.finrank K A < Module.finrank K B :=
      Submodule.finrank_lt_finrank_of_lt hABlt
    have hsup_le : F i.castSucc ⊔ B ≤ F i.succ :=
      sup_le (F.strictMono_space.monotone Fin.castSucc_lt_succ.le) inf_le_left
    have hinf : F i.castSucc ⊓ B = A := by
      apply le_antisymm
      · intro y hy
        exact ⟨hy.1, hy.2.2⟩
      · intro y hy
        exact ⟨hy.1, ⟨F.strictMono_space.monotone
          Fin.castSucc_lt_succ.le hy.1, hy.2⟩⟩
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq (F i.castSucc) B
    rw [hinf] at hdim
    have hsupdim : Module.finrank K ↥(F i.castSucc ⊔ B) ≤ i.val + 1 := by
      calc
        Module.finrank K ↥(F i.castSucc ⊔ B) ≤ Module.finrank K ↥(F i.succ) :=
          Submodule.finrank_mono hsup_le
        _ = i.succ.val := F.finrank_space i.succ
        _ = i.val + 1 := rfl
    have hFidim : Module.finrank K (F i.castSucc) = i.val :=
      F.finrank_space i.castSucc
    change Module.finrank K B = Module.finrank K A + 1
    omega
  · rw [ite_eq_right hij]
    have hnP : ¬∃ x : V, x ∈ F i.succ ∧ x ∈ F' j.succ ∧ x ∉ F i.castSucc := fun hp ↦ hij ((hP_iff
        i j).1 hp)
    have heq : F i.succ ⊓ F' j.succ = F i.castSucc ⊓ F' j.succ := by
      apply le_antisymm
      · intro x hx
        refine ⟨?_, hx.2⟩
        by_contra hxnot
        exact hnP ⟨x, hx.1, hx.2, hxnot⟩
      · exact inf_le_inf_right _ (F.strictMono_space.monotone
          Fin.castSucc_lt_succ.le)
    rw [heq]
    omega

/-- Prefix cardinalities characterize surjective maps of a finite ordered set. -/
private theorem surjective_of_prefix_card {m : ℕ} (σf : Fin (m + 1) → Fin (m + 1))
    (hcount : ∀ j : Fin (m + 1),
      (Finset.univ.filter (fun i ↦ σf i ≤ j)).card = j.val + 1) :
    Function.Surjective σf := by
  classical
  intro j
  by_contra hno
  have hno' : ∀ i, σf i ≠ j := by
    intro i hij
    exact hno ⟨i, hij⟩
  by_cases hj : j = 0
  · subst j
    have he : Finset.univ.filter (fun i : Fin (m + 1) ↦ σf i ≤ 0) = ∅ := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.notMem_empty, iff_false]
      intro hi
      exact hno' i (le_antisymm hi (Fin.zero_le _))
    have hc := hcount (0 : Fin (m + 1))
    rw [he] at hc
    simp at hc
  · let jp : Fin (m + 1) := ⟨j.val - 1, by omega⟩
    have he : Finset.univ.filter (fun i : Fin (m + 1) ↦ σf i ≤ j) =
        Finset.univ.filter (fun i : Fin (m + 1) ↦ σf i ≤ jp) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hi
        have hne := hno' i
        change (σf i).val ≤ jp.val
        change (σf i).val ≤ j.val at hi
        change σf i ≠ j at hne
        dsimp [jp]
        omega
      · intro hi
        change (σf i).val ≤ j.val
        change (σf i).val ≤ jp.val at hi
        dsimp [jp] at hi
        omega
    have hcj := hcount j
    have hcp := hcount jp
    rw [he] at hcj
    change (Finset.univ.filter (fun i : Fin (m + 1) ↦ σf i ≤ jp)).card =
      j.val + 1 at hcj
    change (Finset.univ.filter (fun i : Fin (m + 1) ↦ σf i ≤ jp)).card =
      (j.val - 1) + 1 at hcp
    have hjpos : 0 < j.val := by
      by_contra hz
      have hzv : j.val = 0 := Nat.eq_zero_of_not_pos hz
      apply hj
      apply Fin.ext
      simpa using hzv
    omega

/-- Any two complete flags lie in a common apartment: after choosing one
ordered basis, the second flag is obtained by permuting that same basis.
The inverse in `π.symm` compensates for Mathlib's convention for `Basis.reindex`. -/
theorem common_apartment {n : ℕ} (F F' : CompleteFlag K V n) :
    ∃ (b : Basis (Fin n) K V) (π : Equiv.Perm (Fin n)),
      F = CompleteFlag.ofBasis b ∧
      F' = CompleteFlag.ofBasis (b.reindex π.symm) := by
  classical
  cases n with
  | zero =>
      have htop_bot : (⊤ : Submodule K V) = ⊥ := by
        rw [← F.space_last]
        have hlast : (Fin.last 0 : Fin 1) = 0 := Fin.eq_zero _
        rw [hlast, F.space_zero]
      let : Subsingleton V :=
        ⟨fun x y ↦ by
          have hx : x ∈ (⊥ : Submodule K V) := by
            rw [← htop_bot]
            exact Submodule.mem_top
          have hy : y ∈ (⊥ : Submodule K V) := by
            rw [← htop_bot]
            exact Submodule.mem_top
          exact ((Submodule.mem_bot K).mp hx).trans ((Submodule.mem_bot K).mp hy).symm⟩
      let b : Basis (Fin 0) K V := Basis.empty V
      refine ⟨b, 1, ?_, ?_⟩
      · apply CompleteFlag.ext
        intro i
        have hi : i = 0 := Fin.eq_zero _
        subst i
        rw [F.space_zero]
        exact (CompleteFlag.ofBasis b).space_zero.symm
      · apply CompleteFlag.ext
        intro i
        have hi : i = 0 := Fin.eq_zero _
        subst i
        rw [F'.space_zero]
        exact (CompleteFlag.ofBasis (b.reindex (1 : Equiv.Perm (Fin 0)).symm)).space_zero.symm
  | succ m =>
      have hfin : Module.finrank K V = m + 1 := by
        rw [← finrank_top K V, ← F.space_last]
        simpa using F.finrank_space (Fin.last (m + 1))
      let : FiniteDimensional K V :=
        FiniteDimensional.of_finrank_pos (by omega)
      let P : Fin (m + 1) → Fin (m + 1) → Prop := fun i j ↦
        ∃ x : V, x ∈ F i.succ ∧ x ∈ F' j.succ ∧ x ∉ F i.castSucc
      have hP : ∀ i, ∃ j, P i j := by
        intro i
        obtain ⟨x, hxi, hxni⟩ :=
          IsConcreteLE.exists_of_lt (F.strictMono_space Fin.castSucc_lt_succ)
        refine ⟨Fin.last m, x, hxi, ?_, hxni⟩
        rw [show (Fin.last m).succ = Fin.last (m + 1) by
          ext
          simp, F'.space_last]
        exact Submodule.mem_top
      let σf : Fin (m + 1) → Fin (m + 1) := fun i ↦ Fin.find (P i) (hP i)
      have hσ_spec : ∀ i, P i (σf i) := fun i ↦ Fin.find_spec (hP i)
      have hP_iff (i j : Fin (m + 1)) : P i j ↔ σf i ≤ j := by
        constructor
        · exact Fin.find_le_of_pos (hP i)
        · intro hij
          obtain ⟨x, hxi, hxj, hxni⟩ := hσ_spec i
          refine ⟨x, hxi, ?_, hxni⟩
          exact F'.strictMono_space.monotone ((Fin.succ_le_succ_iff).2 hij) hxj
      let v : Fin (m + 1) → V := fun i ↦ Classical.choose (hσ_spec i)
      have hv_left (i) : v i ∈ F i.succ := (Classical.choose_spec (hσ_spec i)).1
      have hv_right (i) : v i ∈ F' (σf i).succ :=
        (Classical.choose_spec (hσ_spec i)).2.1
      have hv_not (i) : v i ∉ F i.castSucc :=
        (Classical.choose_spec (hσ_spec i)).2.2
      have hstep := commonApartment_rankStep K V F F' σf hP_iff
      let σN : ℕ → ℕ := fun a ↦
        if ha : a < m + 1 then (σf ⟨a, ha⟩).val else 0
      have hsum : ∀ (r : ℕ) (hr : r ≤ m + 1) (j : Fin (m + 1)),
          Module.finrank K ↥(F ⟨r, by omega⟩ ⊓ F' j.succ) =
            ∑ a ∈ Finset.range r, if σN a ≤ j.val then 1 else 0 := by
        intro r
        induction r with
        | zero =>
            intro hr j
            rw [show (⟨0, by omega⟩ : Fin (m + 2)) = 0 by rfl,
              F.space_zero]
            simp
        | succ r ih =>
            intro hr j
            have hrlt : r < m + 1 := hr
            let i : Fin (m + 1) := ⟨r, hrlt⟩
            have hprev := ih (Nat.le_of_succ_le hr) j
            change Module.finrank K ↥(F i.castSucc ⊓ F' j.succ) = _ at hprev
            change Module.finrank K ↥(F i.succ ⊓ F' j.succ) = _
            rw [hstep i j, hprev, Finset.sum_range_succ]
            congr 1
            change (if (σf ⟨r, hrlt⟩).val ≤ j.val then 1 else 0) = _
            have hrm : r ≤ m := by omega
            simp [σN, hrm]
      have hσ_surj : Function.Surjective σf := by
        have hcount (j : Fin (m + 1)) :
            (Finset.univ.filter (fun i : Fin (m + 1) ↦ σf i ≤ j)).card =
              j.val + 1 := by
          have hs := hsum (m + 1) le_rfl j
          have hlast : (⟨m + 1, by omega⟩ : Fin (m + 2)) = Fin.last (m + 1) := by
            apply Fin.ext
            rfl
          rw [hlast, F.space_last, top_inf_eq, F'.finrank_space] at hs
          rw [Finset.card_filter, Finset.sum_fin_eq_sum_range]
          calc
            (∑ i ∈ Finset.range (m + 1),
                if h : i < m + 1 then if σf ⟨i, h⟩ ≤ j then 1 else 0 else 0) =
                ∑ a ∈ Finset.range (m + 1), if σN a ≤ j.val then 1 else 0 := by
              apply Finset.sum_congr rfl
              intro a ha
              have halt : a < m + 1 := Finset.mem_range.mp ha
              have ham : a ≤ m := by omega
              rw [dite_eq_left halt]
              change (if (σf ⟨a, halt⟩).val ≤ j.val then 1 else 0) = _
              simp [σN, ham]
            _ = j.val + 1 := by simpa using hs.symm
        exact surjective_of_prefix_card σf hcount
      have hσ_bij : Function.Bijective σf :=
        (Fintype.bijective_iff_surjective_and_card σf).2 ⟨hσ_surj, rfl⟩
      let e : Fin (m + 1) ≃ Fin (m + 1) := Equiv.ofBijective σf hσ_bij
      have he_apply (i) : e i = σf i := rfl
      let vr : (r : ℕ) → r ≤ m + 1 → Fin r → V := fun r hr i ↦
        v ⟨i.val, i.isLt.trans_le hr⟩
      have hLIprefix : ∀ (r : ℕ) (hr : r ≤ m + 1),
          LinearIndependent K (vr r hr) := by
        intro r
        induction r with
        | zero =>
            intro hr
            exact linearIndependent_empty_type
        | succ r ih =>
            intro hr
            rw [linearIndependent_finSucc']
            constructor
            · have heq : Fin.init (vr (r + 1) hr) =
                  vr r (Nat.le_of_succ_le hr) := by
                funext i
                apply congrArg v
                apply Fin.ext
                rfl
              rw [heq]
              exact ih (Nat.le_of_succ_le hr)
            · intro hmem
              have hspan_le : Submodule.span K (Set.range (Fin.init (vr (r + 1) hr))) ≤
                  F ⟨r, by omega⟩ := by
                rw [Submodule.span_le]
                intro x hx
                obtain ⟨i, rfl⟩ := hx
                have hvF := hv_left ⟨i.val, by omega⟩
                exact F.strictMono_space.monotone
                  (Fin.castSucc_lt_iff_succ_le.mp (show i.val < r from i.isLt)) hvF
              exact hv_not ⟨r, by omega⟩ (hspan_le hmem)
      have hLI : LinearIndependent K v := by
        simpa [vr] using hLIprefix (m + 1) le_rfl
      let b : Basis (Fin (m + 1)) K V :=
        basisOfLinearIndependentOfCardEqFinrank' v hLI (by simp [hfin])
      have hb : (b : Fin (m + 1) → V) = v :=
        coe_basisOfLinearIndependentOfCardEqFinrank' v hLI (by simp [hfin])
      have hFb : F = CompleteFlag.ofBasis b := by
        apply CompleteFlag.ext
        intro r
        apply (Submodule.eq_of_le_of_finrank_eq ?_ ?_).symm
        · change Submodule.span K (b '' {i | i.castSucc < r}) ≤ F r
          rw [Submodule.span_le]
          intro x hx
          obtain ⟨i, hi, rfl⟩ := hx
          rw [hb]
          exact F.strictMono_space.monotone
            (Fin.castSucc_lt_iff_succ_le.mp hi) (hv_left i)
        · rw [(CompleteFlag.ofBasis b).finrank_space, F.finrank_space]
      have hF'b : F' = CompleteFlag.ofBasis (b.reindex e) := by
        apply CompleteFlag.ext
        intro r
        apply (Submodule.eq_of_le_of_finrank_eq ?_ ?_).symm
        · rw [show CompleteFlag.ofBasis (b.reindex e) r =
              Submodule.span K (b '' PrefixSet e.symm r) by
                simpa using ofBasis_reindex_apply K V b e.symm r,
            Submodule.span_le]
          intro x hx
          obtain ⟨i, ⟨j, hj, hji⟩, rfl⟩ := hx
          subst i
          rw [hb]
          have hjσ : (σf (e.symm j)).succ ≤ r := by
            rw [← he_apply]
            simp only [Equiv.apply_symm_apply]
            exact Fin.castSucc_lt_iff_succ_le.mp hj
          exact F'.strictMono_space.monotone hjσ (hv_right (e.symm j))
        · rw [(CompleteFlag.ofBasis (b.reindex e)).finrank_space, F'.finrank_space]
      refine ⟨b, e.symm, hFb, ?_⟩
      simpa using hF'b

/-- The common-basis step in the paper, written literally as prefix spans.
For `i : Fin (n + 1)`, `{j | j.castSucc < i}` represents the first `i`
positions.  Thus `b` is the ordered basis `(v₁, ..., vₙ)`, while `π` gives
the second ordering `(v_{π(1)}, ..., v_{π(n)})`. -/
theorem common_basis_orderings {n : ℕ}
    (F F' : CompleteFlag K V n) :
    ∃ (b : Basis (Fin n) K V) (π : Equiv.Perm (Fin n)),
      (∀ i, F i = Submodule.span K (b '' {j | j.castSucc < i})) ∧
      (∀ i, F' i = Submodule.span K (b '' PrefixSet π i)) := by
  obtain ⟨b, π, hF, hF'⟩ := common_apartment K V F F'
  refine ⟨b, π, ?_, ?_⟩
  · intro i
    rw [hF]
    rfl
  · intro i
    rw [hF']
    exact ofBasis_reindex_apply K V b π i

end DegreeDiameter

end MooreBound
