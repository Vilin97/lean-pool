/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
import LeanPool.MarshallHall.MarshallHall.Completion
import LeanPool.MarshallHall.MarshallHall.Separation

open Set Function
open CategoryTheory CategoryTheory.ActionCategory CategoryTheory.SingleObj Quiver FreeGroup

noncomputable section
namespace MarshallHall

universe u
variable {α : Type u} [DecidableEq α]

/-! The finite-core completion argument.  Its conclusion records the actual
inclusion of the original subgroup into the finite-index subgroup. -/

private theorem loopOfHom_root {G : Type u} [Groupoid.{u} G] [IsFreeGroupoid G]
    (T : WideSubquiver (Symmetrify (IsFreeGroupoid.Generators G))) [Arborescence T]
    (p : End (spanningTreeRoot T)) : IsFreeGroupoid.SpanningTree.loopOfHom T p = p := by
  have ht : IsFreeGroupoid.SpanningTree.treeHom T (spanningTreeRoot T) = 𝟙 _ :=
    IsFreeGroupoid.SpanningTree.treeHom_root T
  change IsFreeGroupoid.SpanningTree.treeHom T _ ≫ p ≫
    inv (IsFreeGroupoid.SpanningTree.treeHom T _) = p
  have hi := congrArg (fun f : End (spanningTreeRoot T) =>
    @CategoryTheory.inv G _ _ _ f (@IsIso.of_groupoid G _ _ _ f)) ht
  exact (congrArg₂ (fun f g : End (spanningTreeRoot T) => f ≫ p ≫ g) ht hi).trans
    ((Category.id_comp _).trans
      ((congrArg (fun g : End (spanningTreeRoot T) => p ≫ g)
        (@CategoryTheory.IsIso.inv_id G _ (spanningTreeRoot T))).trans (Category.comp_id p)))

theorem finite_core_free_factor
    (H : Subgroup (FreeGroup α))
    (A : Set (LeftCosetQuotient H)) [Fintype A]
    (base : A)
    (hbase : base.1 = Quotient.mk'' (1 : FreeGroup α))
    [MulAction (FreeGroup α) A]
    (S : Finset (FreeGroup α))
    (hS : Subgroup.closure (S : Set (FreeGroup α)) = H)
    (hS_core : ∀ s ∈ S, coreCondition A s.toWord)
    (word_action : ∀ (w : List (α × Bool)), coreCondition A w →
      ((FreeGroup.mk w : FreeGroup α) • base : A).1 =
        (Quotient.mk'' (wordValue w) : LeftCosetQuotient H))
    (reach : ∀ z : MulAction.orbit (FreeGroup α) base, ∃ w,
      coreCondition A w ∧
        (Quotient.mk'' (wordValue w) : LeftCosetQuotient H) =
          (z.1 : A).1) :
    Nonempty (MarshallHallWitness H) := by
  let O : Set A := MulAction.orbit (FreeGroup α) base
  let baseO : O := ⟨base, MulAction.mem_orbit_self base⟩
  letI : IsFreeGroupoid (ActionCategory (FreeGroup α) O) := freeActionGroupoidIsFree α O
  let K : Subgroup (FreeGroup α) := MulAction.stabilizer (FreeGroup α) baseO
  have gen_mem : ∀ s ∈ S, s ∈ K := by
    intro s hs
    have hs_action : ((FreeGroup.mk s.toWord : FreeGroup α) • base : A).1 =
        (Quotient.mk'' (wordValue s.toWord) : LeftCosetQuotient H) :=
      word_action s.toWord (hS_core s hs)
    have hs_action' : (s • baseO : O).1.1 =
        (Quotient.mk'' s : LeftCosetQuotient H) := by
      change (s • base : A).1 = _
      simpa [wordValue_eq_freeGroup_mk, FreeGroup.mk_toWord] using hs_action
    apply (MulAction.mem_stabilizer_iff).2
    apply Subtype.ext
    apply Subtype.ext
    change (s • baseO : O).1.1 = base.1
    have hsH : s ∈ H := by
      rw [← hS]
      exact Subgroup.subset_closure hs
    rw [hs_action', (leftCoset_mk_eq_one_iff H s).2 hsH, hbase]
  have hHK : H ≤ K := by
    rw [← hS]
    exact (Subgroup.closure_le K).2 gen_mem
  have hKindex : K.index ≠ 0 := by
    dsimp [K]
    rw [MulAction.index_stabilizer]
    exact Nat.ne_of_gt ((Set.ncard_pos (s := MulAction.orbit (FreeGroup α) baseO)).2
      (MulAction.nonempty_orbit baseO))
  let q : O → LeftCosetQuotient H := fun z => (z.1 : A).1
  let P := goodSymmetricSubquiver H q
  let r : P := ActionCategory.objEquiv (FreeGroup α) O baseO
  have hroot : @RootedConnected
      (WideSubquiver.toType
        (Symmetrify (IsFreeGroupoid.Generators (ActionCategory (FreeGroup α) O))) P) P.quiver r := by
    dsimp [P, q, r, O, baseO]
    exact goodCore_rootedConnected H A base word_action reach
  letI : @RootedConnected
      (WideSubquiver.toType
        (Symmetrify (IsFreeGroupoid.Generators (ActionCategory (FreeGroup α) O))) P) P.quiver r := hroot
  let T := flatGeodesicSubtree P r
  let E := @End (ActionCategory (FreeGroup α) O)
    (@Groupoid.toCategory (ActionCategory (FreeGroup α) O) inferInstance).toCategoryStruct
    (spanningTreeRoot T)
  letI : Group E := @CategoryTheory.End.group (ActionCategory (FreeGroup α) O) inferInstance (spanningTreeRoot T)
  let eK : K ≃* E := by
    dsimp [K, E, T, r, P, q, O, baseO]
    exact ActionCategory.stabilizerIsoEnd (FreeGroup α) baseO
  let Pgen : Set (Quiver.Total (IsFreeGroupoid.Generators (ActionCategory (FreeGroup α) O))) :=
    {e | goodGeneratorEdge H q e.hom}
  let Y := basisSupport (T := T) Pgen
  have hP : ∀ {a b} (e : a ⟶ b), e ∈ P a b →
      goodSymmetricEdge H q e := by
    intro a b e he
    exact he
  have hQ : ∀ {a b} (e : a ⟶ b), e ∈ P a b →
      positiveEdgeOfSym e ∈ Pgen := by
    intro a b e he
    have he' := hP e he
    cases e with
    | inl f => exact he'
    | inr f => exact he'
  let HKH : Subgroup K := Subgroup.comap K.subtype H
  let HE : Subgroup E := Subgroup.map (eK : K →* E) HKH
  have hH : H ≃* HE :=
    (subgroupComapEquiv H K hHK).trans (MulEquiv.subgroupMap eK HKH)
  have hq : q (ActionCategory.objEquiv (FreeGroup α) O baseO).back =
      Quotient.mk'' (1 : FreeGroup α) := by
    change base.1 = _
    exact hbase
  have hY : ∀ y : Y, (spanningTreeBasis T) y ∈ HE := by
    change ∀ y : Y, (spanningTreeBasis T) y ∈
      Subgroup.map (eK : K →* E) HKH
    intro y
    have hyP : y.1.1 ∈ Pgen := by
      exact y.2
    have heGood : goodGeneratorEdge H q y.1.1.hom := by
      exact hyP
    have hloop := good_loop_of_generator H q P r hP y.1.1.hom heGood
    have hloopH : (actionScalar (IsFreeGroupoid.SpanningTree.loopOfHom T
        (IsFreeGroupoid.of y.1.1.hom))) ∈ H := by
      apply (leftCoset_mk_eq_one_iff H _).1
      dsimp at hloop
      have hroot' : (root T).back =
          (ActionCategory.objEquiv (FreeGroup α) O baseO).back := by
        rfl
      rw [hroot', hq] at hloop
      simpa [leftMulEquiv_mk] using hloop
    have hloopK : eK.symm (spanningTreeBasis T y) ∈ HKH := by
      change (eK.symm (spanningTreeBasis T y)).val ∈ H
      rw [spanningTreeBasis_apply]
      exact hloopH
    apply Subgroup.mem_map.mpr
    refine ⟨eK.symm (spanningTreeBasis T y), hloopK, ?_⟩
    exact eK.apply_symm_apply _
  have hgen_retract : ∀ (s : FreeGroup α) (hs : s ∈ S),
      retractBasisElement (spanningTreeBasis T) Y
          (eK ⟨s, gen_mem s hs⟩) = eK ⟨s, gen_mem s hs⟩ := by
    intro s hs
    let ks : K := ⟨s, gen_mem s hs⟩
    change retractBasisElement (spanningTreeBasis T) Y (eK ks) = eK ks
    obtain ⟨p, hp⟩ := goodCore_path H A base word_action
      s.toWord (hS_core s hs)
    dsimp [O, baseO, P, q] at p hp
    have hs_fix : (s • baseO : O) = baseO :=
      (MulAction.mem_stabilizer_iff.mp (gen_mem s hs))
    have hmk : FreeGroup.mk s.toWord = s := FreeGroup.mk_toWord
    let end0 : P :=
      ActionCategory.objEquiv (FreeGroup α) O
        ((FreeGroup.mk s.toWord : FreeGroup α) • baseO)
    let p_main : @Path (WideSubquiver.toType
        (Symmetrify (IsFreeGroupoid.Generators (ActionCategory (FreeGroup α) O))) P) P.quiver r end0 := by
      simpa [T, P, q, O, baseO, end0, r] using p
    have hroot_eq : (root T : (ActionCategory (FreeGroup α) O)) = r := by
      rfl
    have hend_eq : (root T : (ActionCategory (FreeGroup α) O)) = end0 := by
      dsimp [end0]
      rw [hmk, hs_fix]
      rfl
    let p_root : @Path (WideSubquiver.toType
        (Symmetrify (IsFreeGroupoid.Generators (ActionCategory (FreeGroup α) O))) P) P.quiver
        (root T) (root T) :=
      p_main.cast hroot_eq.symm hend_eq.symm
    have hpath := basis_retraction_loop_of_subquiver_path
      (G := (ActionCategory (FreeGroup α) O)) (T := T) Pgen P hQ p_root
    have hloop :
        IsFreeGroupoid.SpanningTree.loopOfHom T
            (symPathHom (G := (ActionCategory (FreeGroup α) O))
              (a := (show Symmetrify (IsFreeGroupoid.Generators (ActionCategory (FreeGroup α) O)) from
                (show T from root T)))
              (forgetSubquiverPath (P := P) p_root)) =
          symPathHom (G := (ActionCategory (FreeGroup α) O))
            (a := (show Symmetrify (IsFreeGroupoid.Generators (ActionCategory (FreeGroup α) O)) from
              (show T from root T)))
            (forgetSubquiverPath (P := P) p_root) := by
      exact loopOfHom_root T _
    have hplabel :
        (actionScalar (symPathHom (G := (ActionCategory (FreeGroup α) O))
          (a := (show Symmetrify (IsFreeGroupoid.Generators (ActionCategory (FreeGroup α) O)) from
            (show T from root T)))
          (forgetSubquiverPath (P := P) p_root))) = s := by
      have hp_main :
          (actionScalar (symPathHom (G := (ActionCategory (FreeGroup α) O))
            (a := (show Symmetrify (IsFreeGroupoid.Generators (ActionCategory (FreeGroup α) O)) from
              (show (ActionCategory (FreeGroup α) O) from r)))
            (forgetSubquiverPath (P := P) p_main))) =
            FreeGroup.mk s.toWord := by
        simpa [p_main, end0, T, P, q, O, baseO, r] using hp
      have hcast :
          (show FreeGroup α from (actionScalar (symPathHom (G := (ActionCategory (FreeGroup α) O))
            (a := (show Symmetrify (IsFreeGroupoid.Generators (ActionCategory (FreeGroup α) O)) from
              (show T from root T)))
            (forgetSubquiverPath (P := P) p_root)))) =
          (show FreeGroup α from (actionScalar (symPathHom (G := (ActionCategory (FreeGroup α) O))
            (a := (show Symmetrify (IsFreeGroupoid.Generators (ActionCategory (FreeGroup α) O)) from
              (show (ActionCategory (FreeGroup α) O) from r)))
            (forgetSubquiverPath (P := P) p_main)))) := by
        let label : ∀ {x y : (ActionCategory (FreeGroup α) O)},
            @Quiver.Hom (ActionCategory (FreeGroup α) O) (CategoryStruct.toQuiver) x y → FreeGroup α :=
          fun {x y} h => (actionScalar h)
        dsimp [p_root]
        exact symPathHom_forget_cast_apply
          (G := (ActionCategory (FreeGroup α) O)) (f := label) p_main hroot_eq.symm hend_eq.symm
      change (show FreeGroup α from
        (actionScalar (symPathHom (G := (ActionCategory (FreeGroup α) O))
          (a := (show Symmetrify (IsFreeGroupoid.Generators (ActionCategory (FreeGroup α) O)) from
            (show T from root T)))
          (forgetSubquiverPath (P := P) p_root)))) = s
      rw [hcast, hp_main, hmk]
    have heq : eK ks =
        IsFreeGroupoid.SpanningTree.loopOfHom T
            (symPathHom (G := (ActionCategory (FreeGroup α) O))
              (a := (show Symmetrify (IsFreeGroupoid.Generators (ActionCategory (FreeGroup α) O)) from
                (show T from root T)))
              (forgetSubquiverPath (P := P) p_root)) := by
      apply Functor.Elements.hom_ext
      change s = _
      rw [hloop]
      exact hplabel.symm
    rw [heq]
    exact hpath
  have hfix : ∀ (g : FreeGroup α) (hg : g ∈ H),
      retractBasisElement (spanningTreeBasis T) Y
          (eK ⟨g, hHK hg⟩) = eK ⟨g, hHK hg⟩ := by
    intro g hg
    have hg' : g ∈ Subgroup.closure (S : Set (FreeGroup α)) := by
      rw [hS]
      exact hg
    refine Subgroup.closure_induction
      (p := fun x hx =>
        retractBasisElement (spanningTreeBasis T) Y
            (eK ⟨x, hHK (by rw [← hS]; exact hx)⟩) =
          eK ⟨x, hHK (by rw [← hS]; exact hx)⟩) ?_ ?_ ?_ ?_ hg'
    · intro x hx
      simpa using hgen_retract x hx
    · change retractBasisElement (spanningTreeBasis T) Y
        (eK (1 : K)) = eK (1 : K)
      rw [eK.map_one]
      exact retractBasisElement_one (spanningTreeBasis T) Y
    · intro x y hx hy ihx ihy
      have hxH : x ∈ H := by rw [← hS]; exact hx
      have hyH : y ∈ H := by rw [← hS]; exact hy
      have hxy : x * y ∈ Subgroup.closure (S : Set (FreeGroup α)) :=
        mul_mem hx hy
      have hxyH : x * y ∈ H := by rw [← hS]; exact hxy
      have hkxy : (⟨x * y, hHK hxyH⟩ : K) =
          (⟨x, hHK hxH⟩ : K) * ⟨y, hHK hyH⟩ := by rfl
      change retractBasisElement (spanningTreeBasis T) Y
          (eK (⟨x * y, hHK hxyH⟩ : K)) =
        eK (⟨x * y, hHK hxyH⟩ : K)
      rw [hkxy, eK.map_mul, retractBasisElement_mul]
      have hm := congrArg₂ (fun a b => a * b) ihx ihy
      change _ ≫ _ = _ ≫ _
      exact hm
    · intro x hx ih
      have hxH : x ∈ H := by rw [← hS]; exact hx
      have hxi : x⁻¹ ∈ Subgroup.closure (S : Set (FreeGroup α)) :=
        inv_mem hx
      have hxiH : x⁻¹ ∈ H := by rw [← hS]; exact hxi
      have hkxi : (⟨x⁻¹, hHK hxiH⟩ : K) =
          (⟨x, hHK hxH⟩ : K)⁻¹ := by rfl
      change retractBasisElement (spanningTreeBasis T) Y
          (eK (⟨x⁻¹, hHK hxiH⟩ : K)) =
        eK (⟨x⁻¹, hHK hxiH⟩ : K)
      rw [hkxi, eK.map_inv, retractBasisElement_inv]
      have hi := congrArg (fun z : E => z⁻¹) ih
      exact hi
  let X : Set (Quiver.Total (IsFreeGroupoid.Generators (ActionCategory (FreeGroup α) O))) :=
    (wideSubquiverEquivSetTotal (wideSubquiverSymmetrify T))ᶜ
  have hHsupport : ∀ h : HE, ∃ w : FreeGroup Y,
      (spanningTreeBasis T).repr (h : E) =
        FreeGroup.map (fun y : Y => (y : X)) w := by
    intro h
    have hm : (h : E) ∈ Subgroup.map (eK : K →* E) HKH := h.2
    rcases Subgroup.mem_map.mp hm with ⟨k, hk, hkh⟩
    have hkH : (k : FreeGroup α) ∈ H := by
      exact hk
    have hfix_h :
        retractBasisElement (spanningTreeBasis T) Y (h : E) = h := by
      rw [← hkh]
      simpa using hfix k.val hkH
    let w : FreeGroup Y :=
      basisRetraction Y ((spanningTreeBasis T).repr (h : E))
    refine ⟨w, ?_⟩
    have hret :
        ((subsetBasisHom (spanningTreeBasis T) Y w :
          generatedByBasis (spanningTreeBasis T) Y) : E) = h := by
      simpa [retractBasisElement, w] using hfix_h
    calc
      (spanningTreeBasis T).repr (h : E) =
          (spanningTreeBasis T).repr
            ((subsetBasisHom (spanningTreeBasis T) Y w :
              generatedByBasis (spanningTreeBasis T) Y) : E) := by
        exact congrArg (spanningTreeBasis T).repr hret.symm
      _ = FreeGroup.map (fun y : Y => (y : X)) w :=
        repr_subsetBasisHom (spanningTreeBasis T) Y w
  have hHEfactor : IsFreeFactor HE :=
    isFreeFactor_of_basis_support HE (spanningTreeBasis T) Y hY hHsupport
  obtain ⟨wE⟩ := hHEfactor
  let wK : FreeFactorWitness HKH :=
    FreeFactorWitness.pullback eK (eK.subgroupMap HKH) wE (by
      intro k
      rfl)
  letI : Group wK.complement := wK.complementGroup
  let equivH : Monoid.Coprod (H : Type u) wK.complement ≃* (K : Type u) :=
    (MulEquiv.coprodCongr (subgroupComapEquiv H K hHK)
      (MulEquiv.refl wK.complement)).trans wK.equiv
  exact ⟨{
    K := K
    hHK := hHK
    finiteIndex := hKindex
    complement := wK.complement
    equiv := equivH
    inclusion := by
      intro h
      change wK.equiv (Monoid.Coprod.inl
        (subgroupComapEquiv H K hHK h)) = ⟨h.1, hHK h.2⟩
      rw [wK.inclusion]
      rfl
  }⟩

/-! The finite-state action supplies the hypotheses of the completion theorem.

The state set is the finite union of all suffix products of a generating set
and the identity word.  The latter makes the resulting finite cover based at
the identity coset; the generating-set states make the subgroup loops lie in
the finite core. -/

theorem marshallHall
    {α : Type u} [finite : Finite α]
    (H : Subgroup (FreeGroup α))
    [fg : Group.FG H] :
    Nonempty (MarshallHallWitness H) := by
  classical
  letI : DecidableEq α := Classical.decEq α
  obtain ⟨S, hS⟩ := (Group.fg_iff_subgroup_fg H).mp
    (inferInstance : Group.FG H)
  let A : Set (LeftCosetQuotient H) :=
    coreStateSet H S (1 : FreeGroup α)
  have hAfin : A.Finite := by
    exact coreStateSet_finite H S 1
  letI : Fintype A := hAfin.fintype
  let q0 : LeftCosetQuotient H := Quotient.mk'' (1 : FreeGroup α)
  have hq0 : q0 ∈ A := by
    exact one_mem_coreStateSet H S 1
  let base : A := ⟨q0, hq0⟩
  let genPerm : α → Equiv.Perm A := fun a =>
    Equiv.extendSubtype (restrictedEquiv A (leftMulEquiv H (FreeGroup.of a)))
  let rho : FreeGroup α →* Equiv.Perm A := FreeGroup.lift genPerm
  letI : MulAction (FreeGroup α) A := MulAction.compHom A rho
  have genPerm_apply {a : α} {z : A}
      (hz : leftMulEquiv H (FreeGroup.of a) z.1 ∈ A) :
      genPerm a z = ⟨leftMulEquiv H (FreeGroup.of a) z.1, hz⟩ := by
    apply Subtype.ext
    dsimp [genPerm]
    have h := Equiv.extendSubtype_apply_of_mem
      (restrictedEquiv A (leftMulEquiv H (FreeGroup.of a))) z hz
    simpa [restrictedEquiv] using congrArg Subtype.val h
  have genPerm_inv_apply {a : α} {z : A}
      (hz : leftMulEquiv H (FreeGroup.of a)⁻¹ z.1 ∈ A) :
      (genPerm a).symm z =
        ⟨leftMulEquiv H (FreeGroup.of a)⁻¹ z.1, hz⟩ := by
    let y : A := ⟨leftMulEquiv H (FreeGroup.of a)⁻¹ z.1, hz⟩
    have hy : leftMulEquiv H (FreeGroup.of a) y.1 ∈ A := by
      have he : leftMulEquiv H (FreeGroup.of a)
          (leftMulEquiv H (FreeGroup.of a)⁻¹ z.1) = z.1 := by
        exact (leftMulEquiv H (FreeGroup.of a)).apply_symm_apply z.1
      rw [show y.1 = leftMulEquiv H (FreeGroup.of a)⁻¹ z.1 by rfl, he]
      exact z.2
    have hforward : genPerm a y = z := by
      rw [genPerm_apply hy]
      exact Subtype.ext (by
        exact (leftMulEquiv H (FreeGroup.of a)).apply_symm_apply z.1)
    have hback := congrArg (genPerm a).symm hforward
    simpa [y] using hback.symm
  have rho_singleton (x : α × Bool) :
      rho (FreeGroup.mk [x]) =
        if x.2 then genPerm x.1 else (genPerm x.1).symm := by
    cases x with
    | mk a b =>
        cases b <;> simp [rho, FreeGroup.lift_mk, Equiv.Perm.inv_def]
  have word_action : ∀ (w : List (α × Bool)),
      coreCondition A w →
      ((rho (FreeGroup.mk w)) base : A).1 =
        (Quotient.mk'' (wordValue w) : LeftCosetQuotient H) := by
    intro w
    induction w with
    | nil =>
        intro hcore
        simp [rho, wordValue, q0, base]
    | cons x w ih =>
        rcases x with ⟨a, b⟩
        cases b with
        | false =>
            intro hcore
            have htail : coreCondition A w := by
              intro u hu x hx
              exact hcore u (by
                simp only [List.tails, List.mem_cons]
                exact Or.inr hu) x hx
            have hi := ih htail
            have hwfinal :
                (Quotient.mk'' (wordValue w) : LeftCosetQuotient H) ∈ A := by
              exact hcore w (by simp [List.tails]) _
                (wordValue_mem_actionStates w)
            have hi' : rho (FreeGroup.mk w) base =
                ⟨Quotient.mk'' (wordValue w), hwfinal⟩ := by
              apply Subtype.ext
              exact hi
            have hfinal :
                (Quotient.mk'' (wordValue ((a, false) :: w)) :
                  LeftCosetQuotient H) ∈ A := by
              exact hcore ((a, false) :: w) (by simp [List.tails]) _
                (wordValue_mem_actionStates ((a, false) :: w))
            have htarget :
                leftMulEquiv H (FreeGroup.of a)⁻¹
                    (Quotient.mk'' (wordValue w) : LeftCosetQuotient H) ∈ A := by
              rw [leftMulEquiv_mk]
              simpa [wordValue, signedLetter] using hfinal
            calc
              ((rho (FreeGroup.mk ((a, false) :: w))) base : A).1 =
                  ((rho (FreeGroup.mk [(a, false)]))
                    (rho (FreeGroup.mk w) base) : A).1 := by
                rw [show FreeGroup.mk ((a, false) :: w) =
                    FreeGroup.mk [(a, false)] * FreeGroup.mk w by
                  rw [FreeGroup.mul_mk]
                  rfl, rho.map_mul, Equiv.Perm.mul_apply]
              _ = ((genPerm a).symm
                    ⟨Quotient.mk'' (wordValue w), hwfinal⟩ : A).1 := by
                rw [hi', rho_singleton]
                rfl
              _ = (leftMulEquiv H (FreeGroup.of a)⁻¹
                    (Quotient.mk'' (wordValue w) : LeftCosetQuotient H)) := by
                rw [genPerm_inv_apply htarget]
              _ = (Quotient.mk'' (wordValue ((a, false) :: w)) :
                    LeftCosetQuotient H) := by
                rw [leftMulEquiv_mk]
                simp [wordValue, signedLetter]
        | true =>
            intro hcore
            have htail : coreCondition A w := by
              intro u hu x hx
              exact hcore u (by
                simp only [List.tails, List.mem_cons]
                exact Or.inr hu) x hx
            have hi := ih htail
            have hwfinal :
                (Quotient.mk'' (wordValue w) : LeftCosetQuotient H) ∈ A := by
              exact hcore w (by simp [List.tails]) _
                (wordValue_mem_actionStates w)
            have hi' : rho (FreeGroup.mk w) base =
                ⟨Quotient.mk'' (wordValue w), hwfinal⟩ := by
              apply Subtype.ext
              exact hi
            have hfinal :
                (Quotient.mk'' (wordValue ((a, true) :: w)) :
                  LeftCosetQuotient H) ∈ A := by
              exact hcore ((a, true) :: w) (by simp [List.tails]) _
                (wordValue_mem_actionStates ((a, true) :: w))
            have htarget :
                leftMulEquiv H (FreeGroup.of a)
                    (Quotient.mk'' (wordValue w) : LeftCosetQuotient H) ∈ A := by
              rw [leftMulEquiv_mk]
              simpa [wordValue, signedLetter] using hfinal
            calc
              ((rho (FreeGroup.mk ((a, true) :: w))) base : A).1 =
                  ((rho (FreeGroup.mk [(a, true)]))
                    (rho (FreeGroup.mk w) base) : A).1 := by
                rw [show FreeGroup.mk ((a, true) :: w) =
                    FreeGroup.mk [(a, true)] * FreeGroup.mk w by
                  rw [FreeGroup.mul_mk]
                  rfl, rho.map_mul, Equiv.Perm.mul_apply]
              _ = (genPerm a
                    ⟨Quotient.mk'' (wordValue w), hwfinal⟩ : A).1 := by
                rw [hi', rho_singleton]
                rfl
              _ = (leftMulEquiv H (FreeGroup.of a)
                    (Quotient.mk'' (wordValue w) : LeftCosetQuotient H)) := by
                rw [genPerm_apply htarget]
              _ = (Quotient.mk'' (wordValue ((a, true) :: w)) :
                    LeftCosetQuotient H) := by
                rw [leftMulEquiv_mk]
                simp [wordValue, signedLetter]
  have hS_core : ∀ s ∈ S, coreCondition A s.toWord := by
    intro s hs u hu x hx
    change (Quotient.mk'' x : LeftCosetQuotient H) ∈
      coreStateSet H S (1 : FreeGroup α)
    exact mem_coreStateSet
      (mem_corePoints_of_generator_suffix (g := (1 : FreeGroup α)) hs hu hx)
  have reach : ∀ z : MulAction.orbit (FreeGroup α) base, ∃ w,
      coreCondition A w ∧
        (Quotient.mk'' (wordValue w) : LeftCosetQuotient H) =
          (z.1 : A).1 := by
    intro z
    have hzA : (z.1 : A).1 ∈
        coreStateSet H S (1 : FreeGroup α) := by
      exact z.1.2
    rcases hzA with ⟨x, hx, hqx⟩
    rcases Finset.mem_union.mp hx with hxS | hxone
    · rcases Finset.mem_biUnion.mp hxS with ⟨s, hs, hxs⟩
      obtain ⟨w, hw, hword⟩ :=
        exists_wordValue_of_mem_allActionStates s.toWord hxs
      refine ⟨w, ?_, ?_⟩
      · intro v hv y hy
        have hvS : v ∈ List.tails s.toWord := by
          apply (List.mem_tails v s.toWord).2
          exact (List.mem_tails v w).1 hv |>.trans
            ((List.mem_tails w s.toWord).1 hw)
        simpa [A] using
          (mem_coreStateSet (H := H) (S := S) (g := (1 : FreeGroup α))
            (mem_corePoints_of_generator_suffix (g := (1 : FreeGroup α))
              hs hvS hy))
      · rw [← hword]
        exact hqx
    · obtain ⟨w, hw, hword⟩ :=
        exists_wordValue_of_mem_allActionStates (1 : FreeGroup α).toWord hxone
      refine ⟨w, ?_, ?_⟩
      · intro v hv y hy
        have hvG : v ∈ List.tails (1 : FreeGroup α).toWord := by
          apply (List.mem_tails v (1 : FreeGroup α).toWord).2
          exact (List.mem_tails v w).1 hv |>.trans
            ((List.mem_tails w (1 : FreeGroup α).toWord).1 hw)
        simpa [A] using
          (mem_coreStateSet (H := H) (S := S) (g := (1 : FreeGroup α))
            (mem_corePoints_of_separating_suffix (g := (1 : FreeGroup α))
              hvG hy))
      · rw [← hword]
        exact hqx
  exact finite_core_free_factor H A base (by
    change q0 = Quotient.mk'' (1 : FreeGroup α)
    rfl) S hS hS_core (by
      intro w hw
      exact word_action w hw) reach

end MarshallHall
