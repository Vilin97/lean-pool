/-
Copyright (c) 2026 Arthur F. Ramos, David Barros Hulak, Ruy J.G.B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
module

public import LeanPool.MarshallHall.MarshallHall.GrushkoRose
public import LeanPool.MarshallHall.MarshallHall.GrushkoEdge


/-!
## The Euler bound for the marked graph

The initial subdivided rose can have many more than `n` geometric edges: a
short generating tuple may contain long reduced words.  The invariant used
by the fold induction is therefore the rank-one Euler bound

    oriented edges ≤ 2 * (n + vertices - 1).

This file establishes that bound for the initial rose and records the exact
cardinalities needed to transport it through a fold.
-/

@[expose] public section



open Function Monoid.Coprod Quiver

noncomputable section

namespace MarshallHall
namespace GeneralGrushko

universe u

variable {G H : Type u} [Group G] [Group H]

/-- Identifies packaged arrows of a rose with its explicitly indexed oriented edges. -/
def roseAllArrowEquiv {n : ℕ} (w : Fin n → List (Sum G H)) :
    AllArrow (V := RoseVertex w) ≃ RoseEdge w :=
  { toFun := fun e => e.2.2.1
    invFun := fun e =>
      ⟨roseEdgeSource e, roseEdgeTarget e, ⟨e, rfl, rfl⟩⟩
    left_inv := by
      intro e
      cases e with
      | mk a be =>
          cases be with
          | mk b e =>
              cases e with
              | mk edge h =>
                  cases h.1
                  cases h.2
                  rfl
    right_inv := by
      intro e
      rfl }

/-- Indexes rose edges by a petal, a letter position, and an orientation flag. -/
def roseEdgeSigmaEquiv {n : ℕ} (w : Fin n → List (Sum G H)) :
    RoseEdge w ≃ Σ i : Fin n, Fin ((w i).length) × Bool :=
  { toFun := fun e => ⟨e.i, e.k, e.forward⟩
    invFun := fun e => ⟨e.1, e.2.1, e.2.2⟩
    left_inv := by
      intro e
      cases e
      rfl
    right_inv := by
      intro e
      rfl }

noncomputable instance roseEdgeFintype {n : ℕ}
    (w : Fin n → List (Sum G H)) : Fintype (RoseEdge w) :=
  Fintype.ofEquiv (Σ i : Fin n, Fin ((w i).length) × Bool)
    (roseEdgeSigmaEquiv w).symm

noncomputable instance roseHomFintype {n : ℕ}
    (w : Fin n → List (Sum G H)) (a b : RoseVertex w) :
    Fintype (@Quiver.Hom (RoseVertex w) (roseQuiver w) a b) := by
  classical
  change Fintype {e : RoseEdge w // roseEdgeSource e = a ∧ roseEdgeTarget e = b}
  infer_instance

noncomputable instance roseAllArrowFintype {n : ℕ}
    (w : Fin n → List (Sum G H)) :
    Fintype (AllArrow (V := RoseVertex w)) := by
  letI (a b : RoseVertex w) : Fintype (@Quiver.Hom
      (RoseVertex w) (roseQuiver w) a b) := roseHomFintype w a b
  exact allArrowFintype

omit [Group G] [Group H] in
theorem roseEdge_card {n : ℕ} (w : Fin n → List (Sum G H)) :
    Fintype.card (RoseEdge w) =
      2 * ∑ i : Fin n, (w i).length := by
  rw [Fintype.card_congr (roseEdgeSigmaEquiv w)]
  simp only [Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_bool]
  rw [Finset.mul_sum]
  simp [Nat.mul_comm]

omit [Group G] [Group H] in
theorem roseVertex_card {n : ℕ} (w : Fin n → List (Sum G H)) :
    Fintype.card (RoseVertex w) =
      1 + ∑ i : Fin n, ((w i).length - 1) := by
  change Fintype.card (Option (Σ i : Fin n, Fin ((w i).length - 1))) = _
  rw [Fintype.card_option, Fintype.card_sigma]
  simp [Nat.add_comm]

omit [Group G] [Group H] in
theorem roseWords_length_le {n : ℕ} (w : Fin n → List (Sum G H)) :
    (∑ i : Fin n, (w i).length) ≤
      n + ∑ i : Fin n, ((w i).length - 1) := by
  calc
    (∑ i : Fin n, (w i).length) ≤
        ∑ i : Fin n, (1 + ((w i).length - 1)) := by
      exact Finset.sum_le_sum (fun i hi => by omega)
    _ = n + ∑ i : Fin n, ((w i).length - 1) := by
      simp [Finset.sum_add_distrib]

omit [Group G] [Group H] in
theorem roseAllArrow_card_eq_roseEdge_card {n : ℕ}
    (w : Fin n → List (Sum G H)) :
    Fintype.card (AllArrow (V := RoseVertex w)) = Fintype.card (RoseEdge w) := by
  exact Fintype.card_congr (roseAllArrowEquiv w)

omit [Group G] [Group H] in
theorem roseAllArrow_card_le_euler {n : ℕ}
    (w : Fin n → List (Sum G H)) :
    Fintype.card (AllArrow (V := RoseVertex w)) ≤
      2 * (n + Fintype.card (RoseVertex w) - 1) := by
  rw [roseAllArrow_card_eq_roseEdge_card, roseEdge_card, roseVertex_card]
  have hwords := roseWords_length_le w
  omega

theorem foldAllArrow_card_le_euler {V : Type u} [Fintype V]
    [qV : Quiver V] [hV : HasInvolutiveReverse V]
    [∀ a b : V, Fintype (a ⟶ b)] {n : ℕ}
    {a b : V} (e₀ : AllArrow (V := V)) (hab : a ≠ b)
    (hfree : ∀ e : AllArrow (V := V), allArrowReverse e ≠ e)
    (hEuler : Fintype.card (AllArrow (V := V)) ≤
      2 * (n + Fintype.card V - 1)) :
    Fintype.card (@AllArrow (foldVertex a b) (foldQuiver e₀)) ≤
      2 * (n + Fintype.card (foldVertex a b) - 1) := by
  have hedge := foldAllArrow_card_add_two_le (a := a) (b := b) e₀ (hfree e₀)
  have hv := foldQuotient_card_add_one_eq (a := a) (b := b) hab
  omega

theorem terminal_euler_gives_separated_generators {V : Type u} [Fintype V]
    [qV : Quiver V] [hV : HasInvolutiveReverse V]
    [∀ a b : V, Fintype (a ⟶ b)] {n : ℕ}
    (M : MarkedBinaryGraph (G := G) (H := H) (V := V) n)
    (hfree : ReverseFree (V := V)) (hgen : M.IsGenerating)
    (hEuler : Fintype.card (AllArrow (V := V)) ≤
      2 * (n + Fintype.card V - 1))
    (hone : Fintype.card V = 1) :
    ∃ s : Fin n → Sum G H,
      Subgroup.closure (Set.range (separatedMap ∘ s)) = ⊤ := by
  exact exists_separated_generators_of_euler_bound M hfree hgen hone hEuler

end GeneralGrushko
end MarshallHall
