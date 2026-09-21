/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.ColourWeight
import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.CycleSum

/-!
# Weighted stabilizer factorization

The completed cycle-type weight summed over the stabilizer of a
colouring factorizes over the fibres, and the colour-character
weighted permutation sum evaluates to `n!` times the product of
the complete homogeneous values of the fibre sizes.  The two
cycle-type transport facts (invariance under `permCongr` and
additivity over `sigmaCongrRight`) enter as explicit hypotheses,
discharged in `ColourCycleSum.lean`.
-/

namespace RS

open Finset Equiv

variable {n N : ℕ}

/-- The completed cycle-type product on an arbitrary finite
carrier. -/
noncomputable def cycleProdOn {γ : Type} [Fintype γ] [DecidableEq γ]
    (t : ℕ → ℂ) (σ : Equiv.Perm γ) : ℂ :=
  (σ.cycleType.map t).prod *
    t 1 ^ (Fintype.card γ - σ.cycleType.sum)

/-- The permCongr-invariance hypothesis. -/
abbrev PermCongrCT : Prop :=
  ∀ (A B : Type) [Fintype A] [DecidableEq A] [Fintype B]
    [DecidableEq B] (e : A ≃ B) (σ : Equiv.Perm A),
    (e.permCongr σ).cycleType = σ.cycleType

/-- The sigma-additivity hypothesis. -/
abbrev SigmaCT : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (β : I → Type)
    [∀ i, Fintype (β i)] [∀ i, DecidableEq (β i)]
    (σ : ∀ i, Equiv.Perm (β i)),
    (Equiv.Perm.sigmaCongrRight σ).cycleType =
      ∑ i, (σ i).cycleType

/-- The general-carrier cycle sum, by transport along an
enumeration. -/
theorem sum_cycleProdOn_eq (H1 : PermCongrCT) {γ : Type}
    [Fintype γ] [DecidableEq γ] (t : ℕ → ℂ) :
    ∑ σ : Equiv.Perm γ, cycleProdOn t σ =
      ((Fintype.card γ).factorial : ℂ) *
        newtonH t (Fintype.card γ) := by
  classical
  set e : γ ≃ Fin (Fintype.card γ) := Fintype.equivFin γ with he
  rw [show (∑ σ : Equiv.Perm γ, cycleProdOn t σ) =
      ∑ π : Equiv.Perm (Fin (Fintype.card γ)), cycleProd t π from ?_]
  · exact cycleSum_eq t (Fintype.card γ)
  · rw [← Equiv.sum_comp (e.permCongr) (cycleProd t)]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [cycleProdOn, cycleProd, H1 γ (Fin (Fintype.card γ)) e σ]

/-- Multiset products of mapped Finset sums split. -/
private theorem prod_map_finset_sum {ι : Type*} (t : ℕ → ℂ)
    (s : Finset ι) (F : ι → Multiset ℕ) :
    (((∑ i ∈ s, F i).map t).prod) =
      ∏ i ∈ s, ((F i).map t).prod := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha,
      Multiset.map_add, Multiset.prod_add, ih]

/-- **The fiberwise cycle weight**: the completed cycle weight of
an assembled fixing permutation is the product of the fibre
weights. -/
theorem cycleProd_ofFibrePerms (H1 : PermCongrCT) (H2 : SigmaCT)
    (t : ℕ → ℂ) (f : Fin n → Fin N)
    (σ : ∀ j : Fin N, Equiv.Perm {i : Fin n // f i = j}) :
    cycleProd t (ofFibrePerms f σ) =
      ∏ j : Fin N, cycleProdOn t (σ j) := by
  classical
  have hct : (ofFibrePerms f σ).cycleType =
      ∑ j : Fin N, (σ j).cycleType := by
    rw [ofFibrePerms_def, H1 _ _ (sigmaFiberEquiv f)
      (Equiv.Perm.sigmaCongrRight σ), H2 _ _ σ]
  have hsle : ∀ j : Fin N,
      (σ j).cycleType.sum ≤ fibreCard f j := by
    intro j
    rw [Equiv.Perm.sum_cycleType, fibreCard_eq_card]
    exact le_trans (Finset.card_le_univ _)
      (le_of_eq (Finset.card_univ))
  have hsum_m : ∑ j : Fin N, fibreCard f j = n := sum_fibreCard f
  rw [cycleProd, hct, prod_map_finset_sum]
  rw [show (n - (∑ j : Fin N, (σ j).cycleType).sum) =
      ∑ j : Fin N, (fibreCard f j - (σ j).cycleType.sum) from ?_]
  · rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [cycleProdOn, fibreCard_eq_card]
  · rw [show (∑ j : Fin N, (σ j).cycleType).sum =
        ∑ j : Fin N, (σ j).cycleType.sum from
      map_sum Multiset.sumAddMonoidHom _ _]
    rw [Finset.sum_tsub_distrib _ (fun j _ => hsle j), hsum_m]

/-- **The weighted stabilizer factorization**: the completed cycle
weight summed over the stabilizer of a colouring is the product of
the fibre factorial-homogeneous values. -/
theorem sum_fixing_cycleProd (H1 : PermCongrCT) (H2 : SigmaCT)
    (t : ℕ → ℂ) (f : Fin n → Fin N) :
    ∑ π ∈ Finset.univ.filter
        (fun π : Equiv.Perm (Fin n) => f ∘ π = f),
      cycleProd t π =
    ∏ j : Fin N, ((fibreCard f j).factorial : ℂ) *
      newtonH t (fibreCard f j) := by
  classical
  calc ∑ π ∈ Finset.univ.filter
        (fun π : Equiv.Perm (Fin n) => f ∘ π = f), cycleProd t π
      = ∑ πh : {π : Equiv.Perm (Fin n) // f ∘ π = f},
          cycleProd t πh.1 :=
        Finset.sum_subtype _ (fun π => by simp) _
    _ = ∑ σ : ∀ j : Fin N, Equiv.Perm {i : Fin n // f i = j},
          cycleProd t (ofFibrePerms f σ) := by
        rw [← Equiv.sum_comp (fixingEquiv f).symm
          (fun πh : {π : Equiv.Perm (Fin n) // f ∘ π = f} =>
            cycleProd t πh.1)]
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [fixingEquiv_symm_apply]
    _ = ∑ σ : ∀ j : Fin N, Equiv.Perm {i : Fin n // f i = j},
          ∏ j : Fin N, cycleProdOn t (σ j) :=
        Finset.sum_congr rfl fun σ _ =>
          cycleProd_ofFibrePerms H1 H2 t f σ
    _ = ∏ j : Fin N, ∑ σj : Equiv.Perm {i : Fin n // f i = j},
          cycleProdOn t σj := by
        rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    _ = ∏ j : Fin N, ((fibreCard f j).factorial : ℂ) *
          newtonH t (fibreCard f j) := by
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [sum_cycleProdOn_eq H1 t, ← fibreCard_eq_card]

/-- **The colour cycle sum**: the `colourChar`-weighted completed
cycle sum evaluates to `n!` times the product of the complete
homogeneous values of the composition. -/
theorem colour_cycleSum (H1 : PermCongrCT) (H2 : SigmaCT)
    (t : ℕ → ℂ) (α : Fin N → ℕ) (hsum : ∑ j : Fin N, α j = n) :
    ∑ π : Equiv.Perm (Fin n),
        (colourChar α π : ℂ) * cycleProd t π =
      (n.factorial : ℂ) * ∏ j : Fin N, newtonH t (α j) := by
  classical
  rw [sum_colourChar_weight α (cycleProd t)]
  rw [Finset.sum_congr rfl
    (fun (g : {g : Fin n → Fin N // ∀ j, fibreCard g j = α j})
      (_ : g ∈ Finset.univ) => sum_fixing_cycleProd H1 H2 t g.1)]
  rw [Finset.sum_congr rfl
    (fun (g : {g : Fin n → Fin N // ∀ j, fibreCard g j = α j})
      (_ : g ∈ Finset.univ) =>
      Finset.prod_congr rfl (fun j _ => by rw [g.2 j]))]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Finset.prod_mul_distrib, ← mul_assoc]
  congr 1
  exact_mod_cast congrArg (Nat.cast (R := ℂ))
    (card_colourClass α hsum)
