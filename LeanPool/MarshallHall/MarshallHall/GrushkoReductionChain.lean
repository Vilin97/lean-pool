/-
Copyright (c) 2026 Arthur F. Ramos, David Barros Hulak, Ruy J.G.B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
module

public import LeanPool.MarshallHall.MarshallHall.GrushkoInvariant


/-!
## Termination of the safe-fold reduction

The graph files prove the local semantics of a fold and the invariant file
proves the Euler inequality that is preserved by it.  This file supplies the
global induction that those local facts support.  Its only hypothesis is the
existence of a safe complementary path at every non-terminal stage.  Thus the
remaining combinatorial issue is isolated precisely to the unfold case of
the classical proof.
-/

@[expose] public section




open Function Monoid.Coprod Quiver

noncomputable section

namespace MarshallHall
namespace GeneralGrushko

universe u v

variable {G H : Type u} [Group G] [Group H]

/-! ### The safe-path hypothesis -/

/-- A graph-level formulation of the one point still missing from the fold
argument.  The graph is assumed to be generating, connected, reverse-free,
and to satisfy the Euler bound.  At least one non-base vertex must admit a
null path whose first edge can be folded without reusing either orientation
in the complementary path. -/
def HasSafeNullFold : Prop :=
  ∀ (n : ℕ) (V : Type) [Fintype V] [qV : Quiver.{0, 0} V]
    [_hV : HasInvolutiveReverse V]
    [_hHom : ∀ a b : V, Fintype (a ⟶ b)]
    (M : MarkedBinaryGraph (G := G) (H := H) (V := V) n),
    ReverseFree (V := V) → M.IsGenerating → M.WeaklyConnected →
      Fintype.card (AllArrow (V := V)) ≤
        2 * (n + Fintype.card V - 1) →
      1 < Fintype.card V →
      ∃ v : V, v ≠ M.base ∧
        ∃ p : @Quiver.Path (Symmetrify V)
            (@Quiver.symmetrifyQuiver V qV)
            (show Symmetrify V from M.base) (show Symmetrify V from v),
          M.labeling.symmPathRead p = 1 ∧
          ∃ c : Symmetrify V,
            ∃ e : @Quiver.Hom (Symmetrify V)
              (@Quiver.symmetrifyQuiver V qV)
              (show Symmetrify V from M.base) c,
            ∃ q : @Quiver.Path (Symmetrify V)
              (@Quiver.symmetrifyQuiver V qV) c
              (show Symmetrify V from v),
              p = e.toPath.comp q ∧
                foldSymmPathAvoid (symmOrientedArrow e) q

/-- The geometric branch of the reduction hypothesis.  This is weaker than
`HasSafeNullFold`: it asks only for a geometrically simple null path, from
which the first edge is safe by `foldSymmPathAvoid_of_geometricallySimple`.
The complementary-path reuse case is exactly the part that still needs the
classical unfold construction. -/
def HasGeometricallySimpleNullPath : Prop :=
  ∀ (n : ℕ) (V : Type) [Fintype V] [qV : Quiver.{0, 0} V]
    [_hV : HasInvolutiveReverse V]
    [_hHom : ∀ a b : V, Fintype (a ⟶ b)]
    (M : MarkedBinaryGraph (G := G) (H := H) (V := V) n),
    M.IsGenerating → M.WeaklyConnected →
      1 < Fintype.card V →
      ∃ v : V, v ≠ M.base ∧
        ∃ p : @Quiver.Path (Symmetrify V)
            (@Quiver.symmetrifyQuiver V qV)
            (show Symmetrify V from M.base) (show Symmetrify V from v),
          M.labeling.symmPathRead p = 1 ∧
          GeometricallySimple (qV := qV) p

theorem hasSafeNullFold_of_hasGeometricallySimpleNullPath
    (hsimple : HasGeometricallySimpleNullPath (G := G) (H := H)) :
    HasSafeNullFold (G := G) (H := H) := by
  intro n V hF qV hV hHom M hfree hgen hconn hEuler hcard
  obtain ⟨v, hv, p, hp, hsimple⟩ :=
    hsimple n V M hgen hconn hcard
  have hp_len : p.length ≠ 0 := by
    intro hzero
    apply hv
    exact (@Path.eq_of_length_zero (Symmetrify V)
      (@Quiver.symmetrifyQuiver V qV) M.base v p hzero).symm
  obtain ⟨c, e, q, hpq⟩ :=
    BinaryLabelling.exists_first_edge_comp (V := V) p hp_len
  have hq : foldSymmPathAvoid (symmOrientedArrow e) q := by
    apply foldSymmPathAvoid_of_geometricallySimple e q
    rw [← hpq]
    exact hsimple
  exact ⟨v, hv, p, hp, c, e, q, hpq, hq⟩

/-! ### One safe step transports all induction data -/

theorem safe_null_fold_step {n : ℕ}
    {V : Type v} [Fintype V] [qV : Quiver V]
    [hV : HasInvolutiveReverse V]
    [hHom : ∀ a b : V, Fintype (a ⟶ b)]
    (M : MarkedBinaryGraph (G := G) (H := H) (V := V) n)
    (hfree : ReverseFree (V := V)) (hgen : M.IsGenerating)
    (hconn : M.WeaklyConnected)
    (hEuler : Fintype.card (AllArrow (V := V)) ≤
      2 * (n + Fintype.card V - 1))
    {v : V} (hv : v ≠ M.base)
    (p : @Quiver.Path (Symmetrify V) (@Quiver.symmetrifyQuiver V qV)
      (show Symmetrify V from M.base) (show Symmetrify V from v))
    (hp : M.labeling.symmPathRead p = 1)
    (hdecomp : ∃ c : Symmetrify V,
      ∃ e : @Quiver.Hom (Symmetrify V) (@Quiver.symmetrifyQuiver V qV)
        (show Symmetrify V from M.base) c,
      ∃ q : @Quiver.Path (Symmetrify V)
        (@Quiver.symmetrifyQuiver V qV) c (show Symmetrify V from v),
        p = e.toPath.comp q ∧ foldSymmPathAvoid (symmOrientedArrow e) q) :
    ∃ e₀ : AllArrow (V := V),
      ∃ ha : allArrowSource e₀ = M.base,
        ∃ q : @Quiver.Path (Symmetrify V)
          (@Quiver.symmetrifyQuiver V qV)
          ((@Quiver.Symmetrify.of V qV).obj (allArrowTarget e₀))
          ((@Quiver.Symmetrify.of V qV).obj v),
          ∃ hq : foldSymmPathAvoid e₀ q,
            letI : Fintype (foldVertex M.base v) := foldVertexFintype _ _
            letI : Quiver (foldVertex M.base v) :=
              foldQuiver (a := M.base) (b := v) e₀
            letI : HasInvolutiveReverse (foldVertex M.base v) :=
              foldHasReverse (a := M.base) (b := v) e₀
            letI (x y : foldVertex M.base v) : Fintype (x ⟶ y) :=
              foldQuiverHomFintype e₀ x y
            @MarkedBinaryGraph.IsGenerating n G H
                (foldVertex M.base v) _ _
                (foldQuiver (a := M.base) (b := v) e₀)
                (foldHasReverse (a := M.base) (b := v) e₀)
                (foldedMarkedGraphSymm (a := M.base) (b := v)
                  M e₀ ha q hq) ∧
            @MarkedBinaryGraph.WeaklyConnected n G H
                (foldVertex M.base v) _ _
                (foldQuiver (a := M.base) (b := v) e₀)
                (foldHasReverse (a := M.base) (b := v) e₀)
                (foldedMarkedGraphSymm (a := M.base) (b := v)
                  M e₀ ha q hq) ∧
            Fintype.card
                (@AllArrow (foldVertex M.base v)
                  (foldQuiver (a := M.base) (b := v) e₀)) ≤
              2 * (n + Fintype.card (foldVertex M.base v) - 1) ∧
            Fintype.card (foldVertex M.base v) < Fintype.card V ∧
            ReverseFree (V := foldVertex M.base v) := by
  obtain ⟨c, e, q, hpq, hq⟩ := hdecomp
  obtain ⟨e₀, ha, q', hq', hgen', hconn', hcard'⟩ :=
    exists_safe_folded_marked_graph M hv.symm p hp
      ⟨c, e, q, hpq, hq⟩ hgen hconn
  refine ⟨e₀, ha, q', hq', hgen', hconn', ?_, hcard', ?_⟩
  · exact foldAllArrow_card_le_euler
      (a := M.base) (b := v) e₀ hv.symm hfree hEuler
  · exact foldReverseFree e₀ hfree

/-! ### Strong induction on the number of vertices -/

theorem separated_generators_of_hasSafeNullFold
    (hsafe : HasSafeNullFold (G := G) (H := H)) :
    HasSeparatedReduction (G := G) (H := H) := by
  have hP : ∀ k : ℕ,
      ∀ (V : Type) [Fintype V] [qV : Quiver.{0, 0} V]
        [hV : HasInvolutiveReverse V]
        [hHom : ∀ a b : V, Fintype (a ⟶ b)]
        (n : ℕ) (M : MarkedBinaryGraph (G := G) (H := H) (V := V) n),
        Fintype.card V = k →
        ReverseFree (V := V) → M.IsGenerating → M.WeaklyConnected →
        Fintype.card (AllArrow (V := V)) ≤
          2 * (n + Fintype.card V - 1) →
        ∃ s : Fin n → Sum G H,
          Subgroup.closure (Set.range (separatedMap ∘ s)) = ⊤ := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro V hFV qV hV hHom n M hcard hfree hgen hconn hEuler
        by_cases hone : Fintype.card V = 1
        · exact exists_separated_generators_of_euler_bound M hfree hgen
            hone hEuler
        · have hpos : 0 < Fintype.card V := by
            exact Fintype.card_pos_iff.mpr ⟨M.base⟩
          have htwo : 1 < Fintype.card V := by omega
          obtain ⟨v, hv, p, hp, c, e, q, hpq, hq⟩ :=
            hsafe n V M hfree hgen hconn hEuler htwo
          have hdecomp : ∃ c : Symmetrify V,
              ∃ e : @Quiver.Hom (Symmetrify V)
                (@Quiver.symmetrifyQuiver V qV)
                (show Symmetrify V from M.base) c,
              ∃ q : @Quiver.Path (Symmetrify V)
                (@Quiver.symmetrifyQuiver V qV) c
                (show Symmetrify V from v),
                p = e.toPath.comp q ∧
                  foldSymmPathAvoid (symmOrientedArrow e) q :=
            ⟨c, e, q, hpq, hq⟩
          obtain ⟨e₀, ha, q', hq', hgen', hconn', hEuler', hcard',
              hfree'⟩ := safe_null_fold_step
            (G := G) (H := H) (V := V) (qV := qV) (v := v)
            M hfree hgen hconn hEuler
            hv p hp hdecomp
          let : Fintype (foldVertex M.base v) := foldVertexFintype _ _
          let : Quiver.{0, 0} (foldVertex M.base v) :=
            foldQuiver (a := M.base) (b := v) e₀
          let : HasInvolutiveReverse (foldVertex M.base v) :=
            foldHasReverse (a := M.base) (b := v) e₀
          let (x y : foldVertex M.base v) : Fintype (x ⟶ y) :=
            foldQuiverHomFintype e₀ x y
          have hcard'' : Fintype.card (foldVertex M.base v) < k := by
            simpa [hcard] using hcard'
          exact ih (V := foldVertex M.base v)
            (Fintype.card (foldVertex M.base v)) hcard'' n
            (foldedMarkedGraphSymm (a := M.base) (b := v)
              M e₀ ha q' hq') rfl hfree' hgen' hconn' hEuler'
  intro n x hx
  let V : Type := RoseVertex (fun i =>
    binaryReducedLetters (G := G) (H := H) (x i))
  let : Fintype V := by
    dsimp [V]
    infer_instance
  let : Quiver V := by
    dsimp [V]
    exact roseQuiver (fun i =>
      binaryReducedLetters (G := G) (H := H) (x i))
  let : HasInvolutiveReverse V := by
    dsimp [V]
    exact roseHasReverse (fun i =>
      binaryReducedLetters (G := G) (H := H) (x i))
  let (a b : V) : Fintype (a ⟶ b) := by
    dsimp [V]
    exact roseHomFintype _ _ _
  let M : MarkedBinaryGraph (G := G) (H := H) (V := V) n :=
    reducedTupleRose x
  have hMgen : M.IsGenerating := by
    dsimp [M]
    exact reducedTupleRose_isGenerating x hx
  have hMconn : M.WeaklyConnected := by
    dsimp [M]
    exact reducedTupleRose_weaklyConnected x
  have hMfree : ReverseFree (V := V) := by
    intro e
    dsimp [V] at e ⊢
    exact rose_allArrow_reverse_ne _ e
  have hMEuler : Fintype.card (AllArrow (V := V)) ≤
      2 * (n + Fintype.card V - 1) := by
    dsimp [V]
    exact roseAllArrow_card_le_euler
      (fun i => binaryReducedLetters (G := G) (H := H) (x i))
  exact hP (Fintype.card V) V n M rfl hMfree hMgen hMconn hMEuler

end GeneralGrushko
end MarshallHall
