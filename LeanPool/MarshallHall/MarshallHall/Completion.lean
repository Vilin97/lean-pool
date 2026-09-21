/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
import LeanPool.MarshallHall.MarshallHall.CoreSupport
import LeanPool.MarshallHall.MarshallHall.FiniteCore

open Set Function
open CategoryTheory CategoryTheory.ActionCategory CategoryTheory.SingleObj Quiver FreeGroup

noncomputable section
namespace MarshallHall

universe u
variable {α : Type u} [DecidableEq α]

/-!
## The finite core as an embedded labelled graph

The finite-state action from `Separation` remembers the cosets needed by the
given subgroup generators.  The predicates below select exactly those
labelled edges of the action groupoid which still agree with the original
left-coset action.  The resulting graph is the finite core used in the
completion argument.
-/

/-- The group element underlying a morphism in the action groupoid. -/
def actionScalar {O : Type u} [MulAction (FreeGroup α) O]
    {a b : ActionCategory (FreeGroup α) O}
    (f : Functor.Elements.Hom (F := actionAsFunctor (FreeGroup α) O) a b) : FreeGroup α :=
  f.hom

def goodGeneratorEdge (H : Subgroup (FreeGroup α)) {O : Type u}
    [MulAction (FreeGroup α) O]
    [IsFreeGroupoid (ActionCategory (FreeGroup α) O)]
    (q : O → LeftCosetQuotient H)
    {a b : IsFreeGroupoid.Generators (ActionCategory (FreeGroup α) O)}
    (e : a ⟶ b) : Prop :=
  leftMulEquiv H (actionScalar (IsFreeGroupoid.of (G := ActionCategory (FreeGroup α) O) e)) (q a.back) = q b.back

def goodSymmetricEdge (H : Subgroup (FreeGroup α)) {O : Type u}
    [MulAction (FreeGroup α) O]
    [IsFreeGroupoid (ActionCategory (FreeGroup α) O)]
    (q : O → LeftCosetQuotient H)
    {a b : Symmetrify (IsFreeGroupoid.Generators
      (ActionCategory (FreeGroup α) O))} (e : a ⟶ b) : Prop :=
  Sum.recOn e
    (fun f => goodGeneratorEdge H q f)
    (fun f => goodGeneratorEdge H q f)

def goodSymmetricSubquiver (H : Subgroup (FreeGroup α)) {O : Type u}
    [MulAction (FreeGroup α) O]
    [IsFreeGroupoid (ActionCategory (FreeGroup α) O)]
    (q : O → LeftCosetQuotient H) :
    WideSubquiver (Symmetrify (IsFreeGroupoid.Generators
      (ActionCategory (FreeGroup α) O))) :=
  fun a b => {e | goodSymmetricEdge H q e}

/-! A shortest-path tree in a rooted connected partial graph, flattened back
to the full edge type so that it can be used by the explicit Schreier basis. -/

def flatGeodesicSubtree {V : Type u} [Quiver V]
    (P : WideSubquiver V) (r : P)
    [RootedConnected r] : WideSubquiver V :=
  fun a b => {e | ∃ (he : e ∈ P a b) (p : @Path (WideSubquiver.toType V P)
      P.quiver r a),
      shortestPath r b = p.cons ⟨e, he⟩}

instance flatGeodesicArborescence {V : Type u} [Quiver V]
    (P : WideSubquiver V) (r : P)
    [RootedConnected r] : Arborescence (flatGeodesicSubtree P r) := by
  letI : Quiver (WideSubquiver.toType V P) := P.quiver
  let T := flatGeodesicSubtree P r
  change Arborescence (WideSubquiver.toType V T)
  apply @arborescenceMk (WideSubquiver.toType V T) T.quiver (r : T)
    (fun b => (shortestPath r b).length)
  · rintro a b ⟨e, ⟨he, p, h⟩⟩
    have hlen := congrArg Quiver.Path.length h
    have hp := shortest_path_spec r p
    change (shortestPath r b).length = p.length + 1 at hlen
    omega
  · rintro a b c ⟨e, ⟨he, p, h⟩⟩ ⟨f, ⟨hf, q, j⟩⟩
    cases h.symm.trans j
    constructor <;> rfl
  · intro b
    rcases hp : shortestPath r b with (_ | ⟨p, e⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨_, ⟨e.1, ⟨e.2, p, hp⟩⟩⟩

def coreCondition {H : Subgroup (FreeGroup α)}
    (A : Set (LeftCosetQuotient H)) (u : List (α × Bool)) : Prop :=
  ∀ v ∈ List.tails u, ∀ x ∈ actionStates v,
    (Quotient.mk'' x : LeftCosetQuotient H) ∈ A

theorem coreCondition_tail {H : Subgroup (FreeGroup α)}
    {A : Set (LeftCosetQuotient H)} {x : α × Bool} {u : List (α × Bool)}
    (h : coreCondition A (x :: u)) : coreCondition A u := by
  intro v hv y hy
  exact h v (by simp only [List.tails, List.mem_cons]; exact Or.inr hv) y hy

theorem goodCore_rootedConnected
    (H : Subgroup (FreeGroup α))
    (A : Set (LeftCosetQuotient H)) (base : A)
    [MulAction (FreeGroup α) A]
    (word_action : ∀ (w : List (α × Bool)), coreCondition A w →
      ((FreeGroup.mk w : FreeGroup α) • base : A).1 =
        (Quotient.mk'' (wordValue w) : LeftCosetQuotient H))
    (reach : ∀ z : MulAction.orbit (FreeGroup α) base, ∃ w,
      coreCondition A w ∧
        (Quotient.mk'' (wordValue w) : LeftCosetQuotient H) =
          (z.1 : A).1) :
    let O : Set A := MulAction.orbit (FreeGroup α) base
    let baseO : O := ⟨base, MulAction.mem_orbit_self base⟩
    let V := ActionCategory (FreeGroup α) O
    letI : IsFreeGroupoid V := freeActionGroupoidIsFree α O
    let P := goodSymmetricSubquiver H (fun z : O => (z.1 : A).1)
    let r : P := ActionCategory.objEquiv (FreeGroup α) O baseO
    @RootedConnected
      (WideSubquiver.toType
        (Symmetrify (IsFreeGroupoid.Generators V)) P)
      P.quiver r := by
  let O : Set A := MulAction.orbit (FreeGroup α) base
  let baseO : O := ⟨base, MulAction.mem_orbit_self base⟩
  let V := ActionCategory (FreeGroup α) O
  letI : IsFreeGroupoid V := freeActionGroupoidIsFree α O
  let P := goodSymmetricSubquiver H (fun z : O => (z.1 : A).1)
  let r : P := ActionCategory.objEquiv (FreeGroup α) O baseO
  have corePath : ∀ (w : List (α × Bool)), coreCondition A w →
      @Path (WideSubquiver.toType
        (Symmetrify (IsFreeGroupoid.Generators V)) P) P.quiver r
        (ActionCategory.objEquiv (FreeGroup α) O
          ((FreeGroup.mk w : FreeGroup α) • baseO)) := by
    intro w
    induction w with
    | nil =>
        intro hw
        have hbase : (FreeGroup.mk [] : FreeGroup α) • baseO = baseO := by
          rw [← FreeGroup.one_eq_mk, one_smul]
        rw [hbase]
        exact Path.nil
    | cons x w ih =>
        rcases x with ⟨a, b⟩
        cases b with
        | false =>
            intro hw
            have htail : coreCondition A w := coreCondition_tail hw
            have hs := word_action w htail
            have ht := word_action ((a, false) :: w) hw
            let sourceO : O := (FreeGroup.mk w : FreeGroup α) • baseO
            let targetO : O :=
              (FreeGroup.mk ((a, false) :: w) : FreeGroup α) • baseO
            let e : (ActionCategory.objEquiv (FreeGroup α) O targetO ⟶
                ActionCategory.objEquiv (FreeGroup α) O sourceO) :=
              ⟨a, by
                change FreeGroup.of a • targetO = sourceO
                dsimp [sourceO, targetO]
                rw [show FreeGroup.mk ((a, false) :: w) =
                    (FreeGroup.of a)⁻¹ * FreeGroup.mk w by
                  calc
                    FreeGroup.mk ((a, false) :: w) =
                        wordValue ((a, false) :: w) :=
                      (wordValue_eq_freeGroup_mk _).symm
                    _ = signedLetter (a, false) * wordValue w := rfl
                    _ = (FreeGroup.of a)⁻¹ * FreeGroup.mk w := by
                      simp [signedLetter, wordValue_eq_freeGroup_mk]]
                simp [smul_smul]⟩
            have hsO : (sourceO.1 : A).1 =
                (Quotient.mk'' (wordValue w) : LeftCosetQuotient H) := by
              change ((FreeGroup.mk w : FreeGroup α) • base : A).1 = _
              exact hs
            have htO : (targetO.1 : A).1 =
                (Quotient.mk'' (wordValue ((a, false) :: w)) :
                  LeftCosetQuotient H) := by
              change ((FreeGroup.mk ((a, false) :: w) : FreeGroup α) • base : A).1 = _
              exact ht
            have heP :
                (Sum.inr e :
                  (ActionCategory.objEquiv (FreeGroup α) O sourceO ⟶
                    ActionCategory.objEquiv (FreeGroup α) O targetO) ⊕
                  (ActionCategory.objEquiv (FreeGroup α) O targetO ⟶
                    ActionCategory.objEquiv (FreeGroup α) O sourceO)) ∈
                P (ActionCategory.objEquiv (FreeGroup α) O sourceO)
                  (ActionCategory.objEquiv (FreeGroup α) O targetO) := by
              change goodGeneratorEdge H (fun z : O => (z.1 : A).1) e
              change leftMulEquiv H (FreeGroup.of a) (targetO.1 : A).1 =
                (sourceO.1 : A).1
              rw [htO, hsO, leftMulEquiv_mk]
              simp [wordValue, signedLetter]
            have hp := ih htail
            exact Path.cons hp ⟨Sum.inr e, heP⟩
        | true =>
            intro hw
            have htail : coreCondition A w := coreCondition_tail hw
            have hs := word_action w htail
            have ht := word_action ((a, true) :: w) hw
            let sourceO : O := (FreeGroup.mk w : FreeGroup α) • baseO
            let targetO : O :=
              (FreeGroup.mk ((a, true) :: w) : FreeGroup α) • baseO
            let e : (ActionCategory.objEquiv (FreeGroup α) O sourceO ⟶
                ActionCategory.objEquiv (FreeGroup α) O targetO) :=
              ⟨a, by
                change FreeGroup.of a • sourceO = targetO
                dsimp [sourceO, targetO]
                rw [show FreeGroup.mk ((a, true) :: w) =
                    FreeGroup.of a * FreeGroup.mk w by
                  calc
                    FreeGroup.mk ((a, true) :: w) =
                        wordValue ((a, true) :: w) :=
                      (wordValue_eq_freeGroup_mk _).symm
                    _ = signedLetter (a, true) * wordValue w := rfl
                    _ = FreeGroup.of a * FreeGroup.mk w := by
                      simp [signedLetter, wordValue_eq_freeGroup_mk]]
                simp [smul_smul]⟩
            have hsO : (sourceO.1 : A).1 =
                (Quotient.mk'' (wordValue w) : LeftCosetQuotient H) := by
              change ((FreeGroup.mk w : FreeGroup α) • base : A).1 = _
              exact hs
            have htO : (targetO.1 : A).1 =
                (Quotient.mk'' (wordValue ((a, true) :: w)) :
                  LeftCosetQuotient H) := by
              change ((FreeGroup.mk ((a, true) :: w) : FreeGroup α) • base : A).1 = _
              exact ht
            have heP :
                (Sum.inl e :
                  (ActionCategory.objEquiv (FreeGroup α) O sourceO ⟶
                    ActionCategory.objEquiv (FreeGroup α) O targetO) ⊕
                  (ActionCategory.objEquiv (FreeGroup α) O targetO ⟶
                    ActionCategory.objEquiv (FreeGroup α) O sourceO)) ∈
                P (ActionCategory.objEquiv (FreeGroup α) O sourceO)
                  (ActionCategory.objEquiv (FreeGroup α) O targetO) := by
              change goodGeneratorEdge H (fun z : O => (z.1 : A).1) e
              change leftMulEquiv H (FreeGroup.of a) (sourceO.1 : A).1 =
                (targetO.1 : A).1
              rw [hsO, htO, leftMulEquiv_mk]
              simp [wordValue, signedLetter]
            have hp := ih htail
            exact Path.cons hp ⟨Sum.inl e, heP⟩
  constructor
  intro b
  obtain ⟨w, hw, hwz⟩ := reach b.back
  have hp := corePath w hw
  have hval : ((FreeGroup.mk w : FreeGroup α) • baseO : O).1.1 =
      b.back.1.1 := by
    change ((FreeGroup.mk w : FreeGroup α) • base : A).1 = _
    exact (word_action w hw).trans hwz
  have hO : ((FreeGroup.mk w : FreeGroup α) • baseO : O) = b.back := by
    apply Subtype.ext
    apply Subtype.ext
    exact hval
  have hV : ActionCategory.objEquiv (FreeGroup α) O
      ((FreeGroup.mk w : FreeGroup α) • baseO) = b := by
    exact (congrArg (ActionCategory.objEquiv (FreeGroup α) O) hO).trans
      ((ActionCategory.objEquiv (FreeGroup α) O).apply_symm_apply b)
  exact ⟨hV ▸ hp⟩

/-! The same recursive construction also remembers the word labelling its
path.  This is the bridge from a subgroup word to the corresponding loop in
the completed covering graph. -/

private theorem action_inv_hom {O : Type u} [MulAction (FreeGroup α) O]
    {a b : ActionCategory (FreeGroup α) O}
    (f : Functor.Elements.Hom (F := actionAsFunctor (FreeGroup α) O) a b) :
    (actionScalar (@CategoryTheory.inv (ActionCategory (FreeGroup α) O) _ a b f
      (@IsIso.of_groupoid (ActionCategory (FreeGroup α) O) _ a b f))) = ((actionScalar f) : FreeGroup α)⁻¹ := by
  have hi := @CategoryTheory.Groupoid.inv_eq_inv (ActionCategory (FreeGroup α) O)
    _ a b f
  exact (congrArg actionScalar hi).symm.trans (by rfl)

theorem goodCore_path
    (H : Subgroup (FreeGroup α))
    (A : Set (LeftCosetQuotient H)) (base : A)
    [MulAction (FreeGroup α) A]
    (word_action : ∀ (w : List (α × Bool)), coreCondition A w →
      ((FreeGroup.mk w : FreeGroup α) • base : A).1 =
        (Quotient.mk'' (wordValue w) : LeftCosetQuotient H))
    (w : List (α × Bool)) (hw : coreCondition A w) :
    let O : Set A := MulAction.orbit (FreeGroup α) base
    let baseO : O := ⟨base, MulAction.mem_orbit_self base⟩
    let V := ActionCategory (FreeGroup α) O
    letI : IsFreeGroupoid V := freeActionGroupoidIsFree α O
    let P := goodSymmetricSubquiver H (fun z : O => (z.1 : A).1)
    let r : P := ActionCategory.objEquiv (FreeGroup α) O baseO
    ∃ p : @Path (WideSubquiver.toType
        (Symmetrify (IsFreeGroupoid.Generators V)) P) P.quiver r
        (ActionCategory.objEquiv (FreeGroup α) O
          ((FreeGroup.mk w : FreeGroup α) • baseO)),
      (actionScalar (symPathHom (G := V)
        (a := (show Symmetrify (IsFreeGroupoid.Generators V) from
          (show V from r)))
        (forgetSubquiverPath p))) = FreeGroup.mk w := by
  let O : Set A := MulAction.orbit (FreeGroup α) base
  let baseO : O := ⟨base, MulAction.mem_orbit_self base⟩
  let V := ActionCategory (FreeGroup α) O
  letI : IsFreeGroupoid V := freeActionGroupoidIsFree α O
  let P := goodSymmetricSubquiver H (fun z : O => (z.1 : A).1)
  let r : P := ActionCategory.objEquiv (FreeGroup α) O baseO
  have corePath : ∀ (w : List (α × Bool)), coreCondition A w →
      ∃ p : @Path (WideSubquiver.toType
        (Symmetrify (IsFreeGroupoid.Generators V)) P) P.quiver r
        (ActionCategory.objEquiv (FreeGroup α) O
          ((FreeGroup.mk w : FreeGroup α) • baseO)),
        (actionScalar (symPathHom (G := V)
          (a := (show Symmetrify (IsFreeGroupoid.Generators V) from
            (show V from r)))
          (forgetSubquiverPath p))) = FreeGroup.mk w := by
    intro w
    induction w with
    | nil =>
        intro hw
        have hbase : (FreeGroup.mk [] : FreeGroup α) • baseO = baseO := by
          rw [← FreeGroup.one_eq_mk, one_smul]
        rw [hbase]
        refine ⟨Path.nil, ?_⟩
        change (1 : FreeGroup α) = FreeGroup.mk []
        rw [FreeGroup.one_eq_mk]
    | cons x w ih =>
        rcases x with ⟨a, b⟩
        cases b with
        | false =>
            intro hw
            have htail : coreCondition A w := coreCondition_tail hw
            have hs := word_action w htail
            have ht := word_action ((a, false) :: w) hw
            let sourceO : O := (FreeGroup.mk w : FreeGroup α) • baseO
            let targetO : O :=
              (FreeGroup.mk ((a, false) :: w) : FreeGroup α) • baseO
            let e : (ActionCategory.objEquiv (FreeGroup α) O targetO ⟶
                ActionCategory.objEquiv (FreeGroup α) O sourceO) :=
              ⟨a, by
                change FreeGroup.of a • targetO = sourceO
                dsimp [sourceO, targetO]
                rw [show FreeGroup.mk ((a, false) :: w) =
                    (FreeGroup.of a)⁻¹ * FreeGroup.mk w by
                  calc
                    FreeGroup.mk ((a, false) :: w) =
                        wordValue ((a, false) :: w) :=
                      (wordValue_eq_freeGroup_mk _).symm
                    _ = signedLetter (a, false) * wordValue w := rfl
                    _ = (FreeGroup.of a)⁻¹ * FreeGroup.mk w := by
                      simp [signedLetter, wordValue_eq_freeGroup_mk]]
                simp [smul_smul]⟩
            have hsO : (sourceO.1 : A).1 =
                (Quotient.mk'' (wordValue w) : LeftCosetQuotient H) := by
              change ((FreeGroup.mk w : FreeGroup α) • base : A).1 = _
              exact hs
            have htO : (targetO.1 : A).1 =
                (Quotient.mk'' (wordValue ((a, false) :: w)) :
                  LeftCosetQuotient H) := by
              change ((FreeGroup.mk ((a, false) :: w) : FreeGroup α) • base : A).1 = _
              exact ht
            have heP :
                (Sum.inr e :
                  (ActionCategory.objEquiv (FreeGroup α) O sourceO ⟶
                    ActionCategory.objEquiv (FreeGroup α) O targetO) ⊕
                  (ActionCategory.objEquiv (FreeGroup α) O targetO ⟶
                    ActionCategory.objEquiv (FreeGroup α) O sourceO)) ∈
                P (ActionCategory.objEquiv (FreeGroup α) O sourceO)
                  (ActionCategory.objEquiv (FreeGroup α) O targetO) := by
              change goodGeneratorEdge H (fun z : O => (z.1 : A).1) e
              change leftMulEquiv H (FreeGroup.of a) (targetO.1 : A).1 =
                (sourceO.1 : A).1
              rw [htO, hsO, leftMulEquiv_mk]
              simp [wordValue, signedLetter]
            obtain ⟨hp, hhp⟩ := ih htail
            refine ⟨Path.cons hp ⟨Sum.inr e, heP⟩, ?_⟩
            change ((actionScalar (@CategoryTheory.inv (ActionCategory (FreeGroup α) O) _ _ _
              (IsFreeGroupoid.of (G := ActionCategory (FreeGroup α) O) e) (@IsIso.of_groupoid (ActionCategory (FreeGroup α) O)
                _ _ _ (IsFreeGroupoid.of (G := ActionCategory (FreeGroup α) O) e)))) : FreeGroup α) *
              (actionScalar (symPathHom (forgetSubquiverPath hp))) = _
            rw [action_inv_hom]
            change (FreeGroup.of a)⁻¹ * (actionScalar (symPathHom (forgetSubquiverPath hp))) = _
            apply (congrArg ((FreeGroup.of a)⁻¹ * ·) hhp).trans
            change (FreeGroup.of a)⁻¹ * FreeGroup.mk w =
              FreeGroup.mk ((a, false) :: w)
            have hmk : FreeGroup.mk [(a, false)] = (FreeGroup.of a)⁻¹ := by
              rw [← wordValue_eq_freeGroup_mk]
              simp [wordValue, signedLetter]
            calc
              (FreeGroup.of a)⁻¹ * FreeGroup.mk w =
                  FreeGroup.mk [(a, false)] * FreeGroup.mk w := by rw [hmk]
              _ = FreeGroup.mk ([(a, false)] ++ w) :=
                FreeGroup.mul_mk.symm
              _ = FreeGroup.mk ((a, false) :: w) := rfl
        | true =>
            intro hw
            have htail : coreCondition A w := coreCondition_tail hw
            have hs := word_action w htail
            have ht := word_action ((a, true) :: w) hw
            let sourceO : O := (FreeGroup.mk w : FreeGroup α) • baseO
            let targetO : O :=
              (FreeGroup.mk ((a, true) :: w) : FreeGroup α) • baseO
            let e : (ActionCategory.objEquiv (FreeGroup α) O sourceO ⟶
                ActionCategory.objEquiv (FreeGroup α) O targetO) :=
              ⟨a, by
                change FreeGroup.of a • sourceO = targetO
                dsimp [sourceO, targetO]
                rw [show FreeGroup.mk ((a, true) :: w) =
                    FreeGroup.of a * FreeGroup.mk w by
                  calc
                    FreeGroup.mk ((a, true) :: w) =
                        wordValue ((a, true) :: w) :=
                      (wordValue_eq_freeGroup_mk _).symm
                    _ = signedLetter (a, true) * wordValue w := rfl
                    _ = FreeGroup.of a * FreeGroup.mk w := by
                      simp [signedLetter, wordValue_eq_freeGroup_mk]]
                simp [smul_smul]⟩
            have hsO : (sourceO.1 : A).1 =
                (Quotient.mk'' (wordValue w) : LeftCosetQuotient H) := by
              change ((FreeGroup.mk w : FreeGroup α) • base : A).1 = _
              exact hs
            have htO : (targetO.1 : A).1 =
                (Quotient.mk'' (wordValue ((a, true) :: w)) :
                  LeftCosetQuotient H) := by
              change ((FreeGroup.mk ((a, true) :: w) : FreeGroup α) • base : A).1 = _
              exact ht
            have heP :
                (Sum.inl e :
                  (ActionCategory.objEquiv (FreeGroup α) O sourceO ⟶
                    ActionCategory.objEquiv (FreeGroup α) O targetO) ⊕
                  (ActionCategory.objEquiv (FreeGroup α) O targetO ⟶
                    ActionCategory.objEquiv (FreeGroup α) O sourceO)) ∈
                P (ActionCategory.objEquiv (FreeGroup α) O sourceO)
                  (ActionCategory.objEquiv (FreeGroup α) O targetO) := by
              change goodGeneratorEdge H (fun z : O => (z.1 : A).1) e
              change leftMulEquiv H (FreeGroup.of a) (sourceO.1 : A).1 =
                (targetO.1 : A).1
              rw [hsO, htO, leftMulEquiv_mk]
              simp [wordValue, signedLetter]
            obtain ⟨hp, hhp⟩ := ih htail
            refine ⟨Path.cons hp ⟨Sum.inl e, heP⟩, ?_⟩
            change FreeGroup.of a * (actionScalar (symPathHom (forgetSubquiverPath hp))) = _
            apply (congrArg (FreeGroup.of a * ·) hhp).trans
            change FreeGroup.of a * FreeGroup.mk w =
              FreeGroup.mk ((a, true) :: w)
            have hmk : FreeGroup.mk [(a, true)] = FreeGroup.of a := by
              rw [← wordValue_eq_freeGroup_mk]
              simp [wordValue, signedLetter]
            calc
              FreeGroup.of a * FreeGroup.mk w =
                  FreeGroup.mk [(a, true)] * FreeGroup.mk w := by rw [hmk]
              _ = FreeGroup.mk ([(a, true)] ++ w) :=
                FreeGroup.mul_mk.symm
              _ = FreeGroup.mk ((a, true) :: w) := rfl
  exact corePath w hw

theorem good_tree_path
    (H : Subgroup (FreeGroup α)) {O : Type u}
    [MulAction (FreeGroup α) O]
    [IsFreeGroupoid (ActionCategory (FreeGroup α) O)]
    (q : O → LeftCosetQuotient H)
    (T : WideSubquiver (Symmetrify (IsFreeGroupoid.Generators
      (ActionCategory (FreeGroup α) O))))
    (hT : ∀ {a b} (e : a ⟶ b), e ∈ T a b →
      goodSymmetricEdge H q e)
    [Arborescence T]
    {a : T} (p : @Path (WideSubquiver.toType
      (Symmetrify (IsFreeGroupoid.Generators
        (ActionCategory (FreeGroup α) O))) T) T.quiver (root T) a) :
    leftMulEquiv H (actionScalar (IsFreeGroupoid.SpanningTree.homOfPath T p))
      (q (root T).back) = q a.back := by
  induction p with
  | nil =>
      change leftMulEquiv H 1 _ = _
      exact leftMulEquiv_one H _
  | @cons b c p e ih =>
      rcases e with ⟨e | e, heT⟩
      · change leftMulEquiv H ((actionScalar (IsFreeGroupoid.of (G := ActionCategory (FreeGroup α) O) e)) *
          (actionScalar (IsFreeGroupoid.SpanningTree.homOfPath T p))) _ = _
        exact (leftMulEquiv_mul H _ _ _).trans
          ((congrArg (leftMulEquiv H (actionScalar (IsFreeGroupoid.of (G := ActionCategory (FreeGroup α) O) e))) ih).trans
            (hT (Sum.inl e) heT))
      · change leftMulEquiv H
          (((actionScalar (@CategoryTheory.inv (ActionCategory (FreeGroup α) O) _ _ _
            (IsFreeGroupoid.of (G := ActionCategory (FreeGroup α) O) e) (@IsIso.of_groupoid (ActionCategory (FreeGroup α) O)
              _ _ _ (IsFreeGroupoid.of (G := ActionCategory (FreeGroup α) O) e)))) : FreeGroup α) *
            (actionScalar (IsFreeGroupoid.SpanningTree.homOfPath T p))) _ = _
        apply (congrArg (fun g : FreeGroup α =>
          leftMulEquiv H (g * actionScalar (IsFreeGroupoid.SpanningTree.homOfPath T p))
            (q (root T).back))
          (action_inv_hom (IsFreeGroupoid.of (G := ActionCategory (FreeGroup α) O) e))).trans
        rw [leftMulEquiv_mul, ih]
        have heP : leftMulEquiv H (actionScalar (IsFreeGroupoid.of (G := ActionCategory (FreeGroup α) O) e)) (q c.back) = q b.back :=
          hT (Sum.inr e) heT
        have h := congrArg (leftMulEquiv H (actionScalar (IsFreeGroupoid.of (G := ActionCategory (FreeGroup α) O) e))⁻¹) heP
        exact (leftMulEquiv_inv_apply H _ _).symm.trans h |>.symm

theorem good_loop_of_generator
    {O : Type u} [MulAction (FreeGroup α) O]
    [IsFreeGroupoid (ActionCategory (FreeGroup α) O)]
    (H : Subgroup (FreeGroup α)) (q : O → LeftCosetQuotient H)
    (P : WideSubquiver (Symmetrify (IsFreeGroupoid.Generators
      (ActionCategory (FreeGroup α) O))))
    (r : P)
    [@RootedConnected (WideSubquiver.toType
      (Symmetrify (IsFreeGroupoid.Generators (ActionCategory (FreeGroup α) O))) P)
      P.quiver r]
    (hP : ∀ {a b} (f : a ⟶ b), f ∈ P a b → goodSymmetricEdge H q f)
    {a b : IsFreeGroupoid.Generators (ActionCategory (FreeGroup α) O)}
    (e : a ⟶ b) (he : goodGeneratorEdge H q e) :
    let T := flatGeodesicSubtree P r
    leftMulEquiv H
        (actionScalar (IsFreeGroupoid.SpanningTree.loopOfHom T
          (IsFreeGroupoid.of (G := ActionCategory (FreeGroup α) O) e))) (q (root T).back) = q (root T).back := by
  let T := flatGeodesicSubtree P r
  have hT : ∀ {a b} (f : a ⟶ b), f ∈ T a b →
      goodSymmetricEdge H q f := by
    intro a b f hf
    rcases hf with ⟨hf, p, hp⟩
    exact hP f hf
  have ha : leftMulEquiv H
      (actionScalar (IsFreeGroupoid.SpanningTree.treeHom T a))
      (q (root T).back) = q a.back := by
    rw [IsFreeGroupoid.SpanningTree.treeHom_eq T
      (default : @Path T T.quiver (root T) (show T from a))]
    exact good_tree_path H q T hT
      (default : @Path T T.quiver (root T) (show T from a))
  have hb : leftMulEquiv H
      (actionScalar (IsFreeGroupoid.SpanningTree.treeHom T b))
      (q (root T).back) = q b.back := by
    rw [IsFreeGroupoid.SpanningTree.treeHom_eq T
      (default : @Path T T.quiver (root T) (show T from b))]
    exact good_tree_path H q T hT
      (default : @Path T T.quiver (root T) (show T from b))
  have hinv : leftMulEquiv H
      (actionScalar (@CategoryTheory.inv (ActionCategory (FreeGroup α) O) _ _ _
        (IsFreeGroupoid.SpanningTree.treeHom T b)
        (@IsIso.of_groupoid (ActionCategory (FreeGroup α) O) _ _ _
          (IsFreeGroupoid.SpanningTree.treeHom T b))))
      (q b.back) = q (root T).back := by
    have h := congrArg
      (leftMulEquiv H
        ((actionScalar (IsFreeGroupoid.SpanningTree.treeHom T b)))⁻¹) hb
    rw [leftMulEquiv_inv_apply] at h
    exact (congrArg (fun g => leftMulEquiv H g (q b.back))
      (action_inv_hom (IsFreeGroupoid.SpanningTree.treeHom T b))).trans h.symm
  change leftMulEquiv H
    (((actionScalar (@CategoryTheory.inv (ActionCategory (FreeGroup α) O) _ _ _
        (IsFreeGroupoid.SpanningTree.treeHom T b)
        (@IsIso.of_groupoid (ActionCategory (FreeGroup α) O) _ _ _
          (IsFreeGroupoid.SpanningTree.treeHom T b)))) : FreeGroup α) *
      (actionScalar (IsFreeGroupoid.of (G := ActionCategory (FreeGroup α) O) e)) * (actionScalar (IsFreeGroupoid.SpanningTree.treeHom T a))) _ = _
  rw [leftMulEquiv_mul, leftMulEquiv_mul, ha, he, hinv]

end MarshallHall
