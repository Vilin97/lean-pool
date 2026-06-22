/-
Copyright (c) 2026 the LieLean team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Viviana del Barco, Gustavo Infanti, Exequiel Rivas, Paul Schwahn
-/
import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.Algebra.Lie.Solvable
import Mathlib.Algebra.Lie.Quotient
import Mathlib.Algebra.Lie.Nilpotent
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Data.Set.Image
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import LeanPool.LowDimSolvClassification.GeneralResults
import LeanPool.LowDimSolvClassification.Classification2

/-!
# LeanPool.LowDimSolvClassification.LemmasDim3
-/

open Module
open Submodule
namespace LieAlgebra
namespace Dim3

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]

--Case 1a: The commutator has dimension 1 and is contained in the center of L.
lemma case1a (dim3 : Module.finrank K L = 3) (h₁ : Module.finrank K (commutator K L) = 1)
      (h : IsTwoStepNilpotent K L) :
    ∃ B : Basis (Fin 3) K L, ⁅B 1, B 2⁆ = B 0 ∧ ⁅B 0, B 1⁆ = 0 ∧ ⁅B 0, B 2⁆ = 0 := by
  have fincomm := FiniteDimensional.of_finrank_eq_succ h₁
  have finL := FiniteDimensional.of_finrank_eq_succ dim3
  let B₁ := Module.finBasisOfFinrankEq K (commutator K L) h₁
  let e := (B₁ 0).val
  have ecomm : e ∈ commutator K L := (B₁ 0).property
  have enezero : e ≠ 0 := by simp [e,LinearIndependent.ne_zero 0 (Basis.linearIndependent B₁)]
  let ι : Set L := by
    apply LinearIndepOn.extend (v := id) (s := {e}) (t := Set.univ) (K := K)
    · exact LinearIndepOn.singleton enezero
    · apply Set.subset_univ
  --ι is a (set) basis of L that also contains e as an element
  have B₂li : LinearIndependent K (Subtype.val : ι → L) := LinearIndepOn.linearIndepOn_extend _ _
  have B₂span : Submodule.span K ι = Submodule.span K Set.univ
      := LinearIndepOn.span_extend_eq_span _ _
  have B₂span' : ⊤ ≤ Submodule.span K (Set.range (Subtype.val: ι → L)) := by
    simp [B₂span]
  let B₂ := Basis.mk B₂li B₂span'
  --B₂ is now the actual basis of L, consisting of the elements in ι
  have eι : e ∈ ι := Set.singleton_subset_iff.mp (LinearIndepOn.subset_extend _ _)
  --show that |ι|=3
  have finι : Finite ι := inferInstance
  have card3 := Module.finrank_eq_card_basis' B₂
  rw [dim3, ← Set.cast_ncard finι, Nat.cast_inj] at card3
  --construct elements f,g such that ι = {e,f,g}
  have : Set.ncard (ι \ {e}) = 2 := by
    rw [Set.ncard_sdiff_singleton_of_mem eι, ← card3]
  have : (ι \ {e}).Nonempty := by
    rw [← Set.ncard_pos]
    simp only [this, Nat.ofNat_pos]
  obtain ⟨f, hf⟩ := this
  have : Set.ncard (ι \ ({e} ∪ {f})) = 1 := by
    rw [← Set.sdiff_sdiff, Set.ncard_sdiff_singleton_of_mem hf, this]
  simp only [Set.union_singleton, Set.ncard_eq_one] at this
  obtain ⟨g, hg⟩ := this
  have fι := Set.mem_of_mem_sdiff hf
  have gι : g ∈ ι := by
    rw [Set.singleton_subset_iff.symm, ← hg]
    exact Set.sdiff_subset
  have hfg : ι = {e, f, g} := by
    apply Set.eq_of_subset_of_subset
    · have : ι ⊆ {f, e} ∪ {g} := by
        rw [← Set.sdiff_subset_iff, hg]
      simp only [Set.union_singleton] at this
      rw [Set.pair_comm, Set.insert_comm, Set.pair_comm]
      assumption
    · intro x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      intro hx
      rcases hx with rfl | rfl | rfl
      repeat assumption
  clear hf hg this
  --we have ⁅e, f⁆ = ⁅e, g⁆ = 0 since e is in the center.
  have ecenter : e ∈ center K L := h ecomm
  rw [LieModule.mem_maxTrivSubmodule] at ecenter
  have lieef : ⁅e, f⁆ = 0 := by
    calc _ = - ⁅f, e⁆ := by rw [lie_skew]
      _ = 0 := by simp [ecenter f]
  have liefe : ⁅f, e⁆ = 0 := ecenter f
  have lieeg : ⁅e, g⁆ = 0 := by
    calc _ = - ⁅g, e⁆ := by rw [lie_skew]
      _ = 0 := by simp [ecenter g]
  have liege : ⁅g, e⁆ = 0 := ecenter g
  let e' := ⁅f, g⁆
  have e'defn : e' = ⁅f, g⁆ := rfl
  --we reindex B₂ over Fin 3 for easier calculations
  let reind : Fin 3 → ι := ![⟨e, eι⟩, ⟨f, fι⟩, ⟨g, gι⟩]
  have : reind.Surjective := by
    intro ⟨x, hx⟩
    rw [hfg] at hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · use 0
      simp [reind]
    · use 1
      simp [reind]
    · use 2
      simp [reind]
  rw [Function.surjective_iff_hasRightInverse] at this
  obtain ⟨rinv, hrinv⟩ := this
  have : Fintype.card (Fin 3) ≤ Fintype.card ↑ι := by
    rw [Fintype.card_fin, card3, Set.ncard_eq_toFinset_card', Set.toFinset_card]
  let reind' : Fin 3 ≃ ι := Equiv.ofRightInverseOfCardLE this reind rinv hrinv
  let B₂' := Basis.reindex B₂ reind'.symm
  --since the Lie bracket is nontrivial we must have e' = ⁅f, g⁆ ≠ 0.
  --So this must span the commutator.
  have nontriv : e' ≠ 0 := by
    intro liefg
    rw [e'defn] at liefg
    have liegf : ⁅g, f⁆ = 0 := by
      calc _ = - ⁅f, g⁆ := by rw [lie_skew]
        _ = 0 := by simp [liefg]
    have : IsLieAbelian L := {
      trivial := by
        intro x y
        have hx := B₂'.linearCombination_repr x
        have hy := B₂'.linearCombination_repr y
        rw [← hx, ← hy]
        repeat rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype]
        · repeat rw [Fin.sum_univ_three]
          simp only [Basis.repr_reindex, Basis.mk_repr, Fin.isValue,
            Finsupp.mapDomain_equiv_apply, Equiv.symm_symm, Equiv.ofRightInverseOfCardLE_apply,
            Matrix.cons_val_zero, Basis.reindex_apply, Basis.coe_mk, Matrix.cons_val_one,
            Matrix.cons_val, lie_add, lie_smul, add_lie, smul_lie, lie_self, smul_zero, zero_add,
            smul_add, add_zero, B₂', B₂, reind', reind]
          rw [liefe, liege, lieef, liegf, lieeg, liefg]
          simp only [smul_zero, add_zero]
        repeat simp only [zero_smul, implies_true]
    }
    have : Module.finrank K (commutator K L) = 0 := LieAlgebra.abelian_iff_dim_comm_zero.mpr this
    rw [h₁] at this
    contradiction
  have e'comm : e' ∈ commutator K L := by
    apply LieSubmodule.lie_mem_lie
    repeat apply LieSubmodule.mem_top
  --B₁ is a basis of commutator K L, consisting only of {e}
  have espan : commutator K L = Submodule.span K {e} := by
    have B₁range : Set.range B₁ = {B₁ 0} := by
        ext x
        constructor
        · intro ⟨y, hx⟩
          rw [Fin.fin_one_eq_zero y] at hx
          rw [hx]
          simp only [Set.mem_singleton_iff]
        · intro hx
          use 0
          rw [Set.mem_singleton_iff] at hx
          rw [hx]
    ext x
    constructor
    · intro hx
      rw [Submodule.mem_span_singleton]
      have B₁span := Basis.mem_span B₁ ⟨x, hx⟩
      rw [B₁range, Submodule.mem_span_singleton] at B₁span
      obtain ⟨a, ha⟩ := B₁span
      use a
      simp only [e]
      rw [← Submodule.coe_smul, ha]
    · intro hx
      rw [Submodule.mem_span_singleton] at hx
      obtain ⟨a, ha⟩ := hx
      have B₁span := Basis.span_eq B₁
      rw [B₁range] at B₁span
      rw [← ha]
      apply Submodule.smul_mem'
      exact ecomm
  have : ∃ c : K, c • e = e' := by
    rw [← Submodule.mem_span_singleton, ← espan]
    exact e'comm
  obtain ⟨c, he'⟩ := this
  --e' is a nonzero multiple of e
  have cnezero : c ≠ 0 := by
    intro hc
    have : e' = 0 := by
      rw [← he', hc, zero_smul]
    contradiction
  --now let B be a basis with B 1 = f, B 2 = g, B 0 = e' = ⁅f, g⁆.
  --Starting from B₂', we scale the vector e to c • e = e'.
  let coef := ![c, 1, 1]
  let b : Fin 3 → L := fun n => coef n • B₂' n
  --remains to show that this is still linearly independent
  have lindep : LinearIndependent K b := by
    have B₂'li := Basis.linearIndependent B₂'
    rw [linearIndependent_iff] at *
    intro l hl
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype] at hl
    · simp only [b] at hl
      specialize B₂'li (Finsupp.ofSupportFinite (fun (i : Fin 3) => l i * coef i) ?_)
      · apply Set.toFinite
      rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype] at B₂'li
      · rw [Finsupp.ofSupportFinite_coe] at B₂'li
        simp_rw [mul_smul] at B₂'li
        specialize B₂'li hl
        rw [← Finsupp.coe_eq_zero, Finsupp.ofSupportFinite_coe] at B₂'li
        have : ∀ i : Fin 3, l i * coef i = 0 := by
          intro i
          change (fun i => l i * coef i) i = 0
          rw [B₂'li]
          simp only [Pi.zero_apply]
        ext i
        specialize this i
        fin_cases i;
        all_goals simp only
        · simp only [mul_eq_zero, coef] at this
          rcases this
          · assumption
          · contradiction
        · simp only [Fin.mk_one, Matrix.cons_val_one, coef] at this
          simp only [Fin.isValue, Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.cons_val_zero, mul_one,
            ] at this
          assumption
        · simp only [Fin.reduceFinMk, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
          mul_one, coef] at this
          assumption
      · simp only [zero_smul, implies_true]
    · simp only [zero_smul, implies_true]
  have cardeq : Fintype.card (Fin 3) = Module.finrank K L := by
    rw [Fintype.card_fin, dim3]
  use basisOfLinearIndependentOfCardEqFinrank lindep cardeq
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Basis.reindex_apply, Equiv.symm_symm,
    Equiv.ofRightInverseOfCardLE_apply, Basis.coe_mk, Fin.isValue,
    coe_basisOfLinearIndependentOfCardEqFinrank, Matrix.cons_val_one, Matrix.cons_val_zero,
    one_smul, Matrix.cons_val, smul_lie, lieef, smul_zero, lieeg, and_self, and_true, b, coef,
    B₂', B₂, reind', reind]
  rw [← e'defn, he']

--This is the iff version of the case1a
lemma case1a' : Module.finrank K L = 3 ∧ Module.finrank K (commutator K L) = 1 ∧
    IsTwoStepNilpotent K L ↔
    ∃ B : Basis (Fin 3) K L, ⁅B 1, B 2⁆ = B 0 ∧ ⁅B 0, B 1⁆ = 0 ∧ ⁅B 0, B 2⁆ = 0 := by
  constructor
  · exact fun ⟨dim3, h₁, h₂⟩ => case1a dim3 h₁ h₂
  · intro ⟨B, hB₁₂, hB₀₁, hB₀₂⟩
    have hcomm : (commutator K L).toSubmodule = span K {B 0} := by
      rw [commutator_eq_span]
      apply le_antisymm
      · rw [span_le]
        intro x ⟨y, z, h⟩
        rw [SetLike.mem_coe, mem_span_singleton]
        rw [← h]
        rw [Basis.repr_fin_three B y, Basis.repr_fin_three B z]
        simp only [lie_add, lie_smul, add_lie, smul_lie, lie_self, smul_zero, zero_add,
          smul_add, add_zero]
        rw [← lie_skew (B 1) (B 0), ← lie_skew (B 2) (B 0), ← lie_skew (B 2) (B 1)]
        repeat rw [hB₀₁, hB₀₂, hB₁₂]
        simp only [neg_zero, smul_zero, add_zero, smul_neg, zero_add]
        rw [← mul_smul, ← mul_smul, ← neg_smul, ← add_smul]
        apply exists_apply_eq_apply
      · apply span_mono
        rw [Set.singleton_subset_iff]
        use (B 1), (B 2)
    constructor
    · rw [finrank_eq_card_basis B, Fintype.card_fin]
    · constructor
      · rw [← (finrank_span_singleton (K := K) (Basis.ne_zero B 0)), ← hcomm]
        rfl
      · intro x hx
        rw [← LieSubmodule.mem_toSubmodule, hcomm, mem_span_singleton] at hx
        obtain ⟨a, hx⟩ := hx
        rw [LieModule.mem_maxTrivSubmodule]
        intro y
        rw [← hx, lie_smul, Basis.repr_fin_three B y]
        simp only [add_lie, smul_lie, lie_self, smul_zero, zero_add, smul_add]
        rw [← lie_skew (B 1) (B 0), ← lie_skew (B 2) (B 0), hB₀₁, hB₀₂]
        simp

--Case 1b: The commutator has dimension 1 and is NOT contained in the center of L.
lemma case1b (dim3 : Module.finrank K L = 3) (h₁ : Module.finrank K (commutator K L) = 1)
    (h : ¬ IsTwoStepNilpotent K L) :
    ∃ B : Basis (Fin 3) K L, ⁅B 0, B 1⁆ = 0 ∧ ⁅B 0, B 2⁆ = 0 ∧ ⁅B 1, B 2⁆ = B 1 := by
  have _ : Module.Finite K (commutator K L) := by
    exact finite_of_finrank_eq_succ h₁
  -- take a basis of the commutator
  let  V := finBasisOfFinrankEq K (commutator K L) h₁
  set e := V 0 with hs
  obtain ⟨e,he⟩:= e
  --every bracket is a multiple of e
  have lie_comm : ∀ (x y : L), ∃ (c : K), ⁅ x , y ⁆ = c • e := by
    intro x y
    have eq := Basis.repr_fin_one V ⟨⁅x, y⁆, lie_mem_commutator x y ⟩
    have meq := Subtype.ext_iff.mp eq
    simp only at meq
    use (V.repr ⟨⁅x, y⁆, lie_mem_commutator x y⟩ 0)
    rw [← hs] at meq
    simp only [Fin.isValue, SetLike.mk_smul_mk] at meq
    exact meq
  -- e is not in the center
  have enz : e ∉ center K L := by
    intro hz
    apply h
    intro x xcomm
    have u:= Basis.repr_fin_one (B:=V) (x:= ⟨x,xcomm⟩)
    rw [← hs] at u
    simp only [LieModule.mem_maxTrivSubmodule]
    intro x₁
    have := Subtype.ext_iff.mp u
    simp only [Fin.isValue, SetLike.mk_smul_mk] at this
    rw [this]
    rw [lie_smul]
    rw [hz, smul_zero]
  -- since e is not central, there must ba an f that does not commute with e
  have exf : ∃ f : L, ⁅f,e ⁆ ≠ 0 := Classical.exists_not_of_not_forall enz
  obtain ⟨f, hf⟩ := exf
  let ⟨a, ha⟩ := lie_comm e f
  have ane0 : a ≠ 0 := by
    rw [← lie_skew] at hf
    rw [ha] at hf
    simp_all only [ne_eq, neg_eq_zero, smul_eq_zero, not_or, not_false_eq_true]
  let f' := a⁻¹ • f
  have f'comm : ⁅e, f'⁆ = e := by
    simp only [lie_smul, f']
    rw [ha]
    exact inv_smul_smul₀ ane0 e
  have ene0 : e ≠ 0 := by
    have := Basis.ne_zero V 0
    intro h
    apply this
    rw [← hs]
    apply Subtype.ext
    simp only [ZeroMemClass.coe_zero]
    assumption
  -- the set e,f is linearly independent
  have fe_li: LinearIndependent K ![e,
    f'] := linearIndependent_of_bracket_ne_zero e f' (by rw [f'comm]; apply ene0)
  -- B is the extension of the l.i set  to a basis
  set B := Basis.extendFinSucc fe_li dim3 with Beq
  have B1f : B 1 = e := by
    have := Basis.extend_fin_succ_tail_eq fe_li dim3
    apply_fun (fun x ↦ x 0) at this
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Matrix.cons_val_zero] at this
    rw [← this]
    exact rfl
  have B2e : B 2 = f' := by
    have := Basis.extend_fin_succ_tail_eq fe_li dim3
    apply_fun (fun x ↦ x 1) at this
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Matrix.cons_val_one,
      Matrix.cons_val_fin_one] at this
    rw [← this]
    exact rfl
  -- we compute the brackets of g'=B 0 with e and f'
  let g' := B 0
  let ⟨a, ha⟩ := lie_comm g' e
  let ⟨b, hb⟩ := lie_comm g' f'
  -- now we redifine the basis B with the new g
  let g := g' - b • e + a • f'
  have ge : ⁅ g, e ⁆ = 0 := by
    simp only [add_lie, sub_lie, smul_lie, lie_self, smul_zero, sub_zero, g]
    rw [ha, ← lie_skew, f'comm]
    module
  have gf' : ⁅ g, f' ⁆ = 0 := by
    simp only [add_lie, sub_lie, smul_lie, lie_self, smul_zero, add_zero, g]
    rw [hb, f'comm]
    module
  have := B.linearIndependent
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd] at this
  -- we show that the set is l.i. after redifining
  have : LinearIndependent K ![g, e, f'] := by
    dsimp [g, g']
    repeat rw [← B1f, ← B2e]
    apply linearIndependent_iff.mpr
    intro l hl
    rw [Finsupp.linearCombination_apply (R:=K) (v:=![B 0 - b • B 1 + a • B 2, B 1,
      B 2]) (l:=l)] at hl
    rw [Finsupp.sum_fintype] at hl
    · rw [Fin.sum_univ_three] at hl
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Matrix.cons_val_zero, smul_add,
        Matrix.cons_val_one, Matrix.cons_val] at hl
      apply linearIndependent_iff.mp at this
      let llf : Fin 3 →₀ K := Finsupp.cons (l 0) (Finsupp.cons (-l 0 * b + l 1) (Finsupp.cons
          (l 0 * a + l 2) 0))
      --  llf := ![l 0, -l 0 * b + l 1, l 0 * a + l 2]
      specialize this llf
      rw [Finsupp.linearCombination_apply (R:=K) (v:=B) (l:=llf)] at this
      rw [Finsupp.sum_fintype] at this
      · rw [Fin.sum_univ_three] at this
        unfold llf at this
        have snd : (Finsupp.cons (l 0) (Finsupp.cons (-l 0 * b + l 1) (Finsupp.cons
            (l 0 * a + l 2) (0 : Fin 0 →₀ K)))) 1 = (-l 0 * b + l 1) := by
          rfl
        have thd : (Finsupp.cons (l 0) (Finsupp.cons (-l 0 * b + l 1) (Finsupp.cons
            (l 0 * a + l 2) (0 : Fin 0 →₀ K)))) 2 = l 0 * a + l 2 := by
          rfl
        rw [snd,thd] at this
        simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, neg_mul,
          Finsupp.cons_zero] at this
        have Hq : l 0 • B 0 + (-(l 0 * b) + l 1) • B 1 + (l 0 * a + l 2) • B 2 = l 0 •
            (B 0 - b • B 1) + l 0 • a • B 2 + l 1 • B 1 + l 2 • B 2 := by
          module
        rw [← Hq] at hl
        specialize this hl
        rw [← this]
        have l0z : l 0 = 0:= by
          apply_fun (fun x ↦ x.toFun 0) at this
          exact this
        rw [l0z]
        simp only [zero_mul, neg_zero, zero_add]
        ext i
        fin_cases i
        · assumption
        · rfl
        · rfl
      · simp
    · simp
  -- so it has to be a basis
  let Bn := basisOfLinearIndependentOfCardEqFinrank this (by rw [dim3]; simp)
  have Bn0 : Bn 0 = g := by
    unfold Bn
    rw [coe_basisOfLinearIndependentOfCardEqFinrank]
    rfl
  have Bn1 : Bn 1 = e := by
    unfold Bn
    rw [coe_basisOfLinearIndependentOfCardEqFinrank]
    rfl
  have Bn2 : Bn 2 = f' := by
    unfold Bn
    rw [coe_basisOfLinearIndependentOfCardEqFinrank]
    rfl
  use Bn
  -- finaly we show that the bracket relations in the statement are satisfied
  constructor
  · rw [Bn0, Bn1]
    exact ge
  · constructor
    · rw [Bn0, Bn2]
      exact gf'
    · rw [Bn1, Bn2]
      exact f'comm

--This is the iff version of case1b
lemma case1b' : Module.finrank K L = 3 ∧ Module.finrank K (commutator K L) = 1 ∧
    ¬IsTwoStepNilpotent K L ↔
    ∃ B : Basis (Fin 3) K L, ⁅B 0, B 1⁆ = 0 ∧ ⁅B 0, B 2⁆ = 0 ∧ ⁅B 1, B 2⁆ = B 1 := by
  constructor
  · exact fun ⟨dim3, h₁, h₂⟩ => case1b dim3 h₁ h₂
  · intro ⟨B, hB₀₁, hB₀₂, hB₁₂⟩
    have hcomm : (commutator K L).toSubmodule = span K {B 1} := by
      rw [commutator_eq_span]
      apply le_antisymm
      · rw [span_le]
        intro x ⟨y, z, h⟩
        rw [SetLike.mem_coe, mem_span_singleton]
        rw [← h]
        rw [Basis.repr_fin_three B y, Basis.repr_fin_three B z]
        simp only [lie_add, lie_smul, add_lie, smul_lie, lie_self, smul_zero, zero_add,
          smul_add, add_zero]
        rw [← lie_skew (B 1) (B 0), ← lie_skew (B 2) (B 0), ← lie_skew (B 2) (B 1)]
        repeat rw [hB₀₁, hB₀₂, hB₁₂]
        simp only [neg_zero, smul_zero, add_zero, smul_neg, zero_add]
        rw [← mul_smul, ← mul_smul, ← neg_smul, ← add_smul]
        apply exists_apply_eq_apply
      · apply span_mono
        rw [Set.singleton_subset_iff]
        use (B 1), (B 2)
    constructor
    · rw [finrank_eq_card_basis B, Fintype.card_fin]
    · constructor
      · rw [← (finrank_span_singleton (K := K) (Basis.ne_zero B 1)), ← hcomm]
        rfl
      · --show B 1 is not in the center
        intro h
        have : B 1 ∈ commutator K L := by
          rw [← LieSubmodule.mem_toSubmodule, hcomm, mem_span_singleton]
          use 1
          simp
        specialize h this
        rw [LieModule.mem_maxTrivSubmodule] at h
        specialize h (B 2)
        rw [← lie_skew, hB₁₂, neg_eq_zero] at h
        exact Basis.ne_zero B 1 h

--If the commutator subalgebra has dimension 2, it must itself be abelian.
lemma commutator_abelian_of_dim_two (dim3 : Module.finrank K L = 3)
    (h₂ : Module.finrank K (commutator K L) = 2) :
    IsLieAbelian (commutator K L) := by
  have h₂' : Module.finrank K (commutator K L).toSubmodule = 2 := by
    rw [← h₂]
    exact rfl
  have hc := Dim2.abelian_or_basis h₂
  rcases hc with ⟨u⟩ | ⟨B, hB⟩
  · assumption
  · have B_is_li_L := (LinearIndependent.iff_in_submodule
      (commutator K L).toSubmodule).mp B.linearIndependent
    have : FiniteDimensional K L := Module.finite_of_finrank_eq_succ dim3
    let Bn := Basis.extendFinSucc B_is_li_L dim3
    have Bn10 : Bn 1 = B 0 := by
      have := Basis.extend_fin_succ_tail_eq B_is_li_L dim3
      apply_fun (fun x ↦ x 0) at this
      simp only [Nat.reduceAdd, Fin.isValue, Function.comp_apply] at this
      rw [← this]
      unfold Bn
      exact rfl
    have Bn21 : Bn 2 = B 1 := by
      have := Basis.extend_fin_succ_tail_eq B_is_li_L dim3
      apply_fun (fun x ↦ x 1) at this
      simp only [Nat.reduceAdd, Fin.isValue, Function.comp_apply] at this
      rw [← this]
      unfold Bn
      exact rfl
    let u := ⁅ Bn 0, Bn 1 ⁆
    have ucomm : u ∈ commutator K L := by
      apply LieSubmodule.lie_mem_lie
      repeat apply LieSubmodule.mem_top
    have ucomp := Basis.repr_fin_two (B:=B) (x:=⟨u,ucomm⟩)
    let v := ⁅ Bn 0, Bn 2 ⁆
    have vcomm : v ∈ commutator K L := by
      apply LieSubmodule.lie_mem_lie
      repeat apply LieSubmodule.mem_top
    have vcomp := Basis.repr_fin_two (B:=B) (x:=⟨v,vcomm⟩)
    have nl : ⁅ Bn 1, Bn 2 ⁆ = Bn 2 := by
      rw [Bn10, Bn21]
      nth_rw 2 [← hB]
      rfl
    have br02 :=
      calc ⁅ Bn 0, Bn 2 ⁆ = ⁅ Bn 0, ⁅ Bn 1, Bn 2 ⁆ ⁆ := by rw [nl]
        _ = ⁅ ⁅ Bn 0, Bn 1 ⁆, Bn 2 ⁆ + ⁅ Bn 1, ⁅ Bn 0, Bn 2 ⁆ ⁆  := by rw [leibniz_lie]
        _ = ⁅ u , Bn 2 ⁆ + ⁅ Bn 1, ⁅ Bn 0, Bn 2 ⁆ ⁆  := by rfl
        _ = ⁅ (B.repr ⟨u, ucomm⟩) 0 • B 0 + (B.repr ⟨u, ucomm⟩) 1 • B 1 , Bn 2 ⁆ + ⁅ Bn 1, ⁅ Bn 0,
          Bn 2 ⁆ ⁆  := by
         rw [← ucomp]
         rfl
        _ =  (B.repr ⟨u, ucomm⟩) 0 •⁅  B 0 , Bn 2 ⁆ + (B.repr ⟨u, ucomm⟩) 1 • ⁅ B 1 ,
          Bn 2 ⁆ + ⁅ Bn 1, ⁅ Bn 0, Bn 2 ⁆ ⁆  := by simp
        _ =  (B.repr ⟨u, ucomm⟩) 0 •⁅  B 0 , B 1 ⁆ + (B.repr ⟨u, ucomm⟩) 1 • ⁅ B 1 , B 1 ⁆
             + ⁅ Bn 1, ⁅ Bn 0, Bn 2 ⁆ ⁆  := by
              rw [Bn21]
              rfl
        _ =  (B.repr ⟨u, ucomm⟩) 0 • B 1 + ⁅ Bn 1, ⁅ Bn 0, Bn 2 ⁆ ⁆  := by
          rw [show ((⁅B 0, B 1⁆ : commutator K L) : L) = ((B 1 : commutator K L) : L) from
            congr_arg _ hB]
          simp
        _ =  (B.repr ⟨u, ucomm⟩) 0 • B 1 + ⁅ Bn 1, (B.repr ⟨v, vcomm⟩) 0 • B 0 + (B.repr ⟨v,
          vcomm⟩) 1 • B 1 ⁆  := by
          rw [← vcomp]
          rfl
        _ =  (B.repr ⟨u, ucomm⟩) 0 • B 1 +  ⁅ Bn 1, (B.repr ⟨v, vcomm⟩) 0 • B 0⁆ +  ⁅ Bn 1,
          (B.repr ⟨v, vcomm⟩) 1 • B 1 ⁆  := by
          rw [lie_add (Bn 1)]
          push_cast
          rw [add_assoc]
        _ =  (B.repr ⟨u, ucomm⟩) 0 • B 1 +  (B.repr ⟨v, vcomm⟩) 0 •  ⁅ Bn 1, B 0⁆ + (B.repr ⟨v,
          vcomm⟩) 1 • ⁅ Bn 1,  B 1 ⁆  := by rw[lie_smul,lie_smul];rfl
        _ =  (B.repr ⟨u, ucomm⟩) 0 • B 1 +  (B.repr ⟨v, vcomm⟩) 0 •  ⁅ B 0, B 0⁆ + (B.repr ⟨v,
          vcomm⟩) 1 • ⁅ B 0,  B 1 ⁆  := by rw[Bn10];rfl
        _ =  (B.repr ⟨u, ucomm⟩) 0 • B 1 +   (B.repr ⟨v, vcomm⟩) 1 • ⁅ B 0,  B 1 ⁆  := by simp
        _ =  (B.repr ⟨u, ucomm⟩) 0 • B 1 +   (B.repr ⟨v, vcomm⟩) 1 • B 1:= by
          congr 1
          rw [show ((⁅B 0, B 1⁆ : commutator K L) : L) = ((B 1 : commutator K L) : L) from
            congr_arg _ hB]
        _ =  (((B.repr ⟨u, ucomm⟩) 0 +  (B.repr ⟨v, vcomm⟩) 1)) • B 1:= by rw [← add_smul]
    have vcomp' : v = (B.repr ⟨v, vcomm⟩) 0 • B 0 + (B.repr ⟨v, vcomm⟩) 1 • B 1 := by
      have := Subtype.ext_iff.mp vcomp
      exact this
    have d :=
      calc -(B.repr ⟨u, ucomm⟩) 0 • B 1 = - (B.repr ⟨u, ucomm⟩) 0 • Bn 2 := by rw [Bn21]
        _ = -(B.repr ⟨u, ucomm⟩) 0 • ⁅Bn 1 , Bn 2⁆ := by rw [nl]
        _ = (-1 : K)• ((B.repr ⟨u, ucomm⟩) 0) • ⁅Bn 1 , Bn 2⁆ := by simp []
        _ = ( (-1 : K) * ((B.repr ⟨u, ucomm⟩) 0) )•   ⁅Bn 1 , Bn 2⁆ := by rw [mul_smul]
        _ = ( ((B.repr ⟨u, ucomm⟩) 0)  * (-1 : K))•   ⁅Bn 1 , Bn 2⁆ := by rw [mul_comm]
        _ = ((B.repr ⟨u, ucomm⟩) 0)  •  (-1 : K)•   ⁅Bn 1 , Bn 2⁆ := by rw [mul_smul]
        _ = ((B.repr ⟨u, ucomm⟩) 0)  • ( (-1 : K)•   ⁅Bn 1 , Bn 2⁆) := by rw [← smul_assoc]
        _ = ((B.repr ⟨u, ucomm⟩) 0)  • ( - ⁅Bn 1 , Bn 2⁆) := by rw [neg_one_smul]
        _ = ((B.repr ⟨u, ucomm⟩) 0)  •  ⁅Bn 2 , Bn 1⁆ := by rw [lie_skew]
        _ = ((B.repr ⟨u, ucomm⟩) 0)  •  ⁅Bn 2 , Bn 1⁆ +  ((B.repr ⟨u, ucomm⟩) 1)  •  ⁅Bn 2 ,
          Bn 2⁆ := by rw [lie_self]; simp
        _ = ⁅Bn 2 ,((B.repr ⟨u, ucomm⟩) 0)  •   Bn 1⁆ +  ⁅Bn 2 ,((B.repr ⟨u,
          ucomm⟩) 1)  •  Bn 2⁆ := by simp
        _ = ⁅Bn 2 ,((B.repr ⟨u, ucomm⟩) 0)  •   Bn 1+((B.repr ⟨u, ucomm⟩) 1)  •  Bn 2⁆ := by simp
        _ = ⁅Bn 2 ,((B.repr ⟨u, ucomm⟩) 0)  •   B 0+((B.repr ⟨u, ucomm⟩) 1)  •  B 1⁆ := by
          push_cast
          rw [← Bn10, ← Bn21]
        _ = ⁅Bn 2 , u⁆ := by rw [← ucomp]; simp
        _ = ⁅Bn 2 , ⁅ Bn 0,Bn 1⁆⁆ := by rfl
        _ = ⁅⁅Bn 2 ,  Bn 0⁆,Bn 1⁆ + ⁅ Bn 0, ⁅Bn 2, Bn 1⁆⁆:= by rw [leibniz_lie]
        _ = ⁅-⁅Bn 0 ,  Bn 2⁆,Bn 1⁆ + ⁅ Bn 0, -⁅Bn 1, Bn 2⁆⁆:= by rw [← lie_skew];simp
        _ = ⁅-( (((B.repr ⟨u, ucomm⟩) 0 +  (B.repr ⟨v, vcomm⟩) 1)) • B 1),Bn 1⁆ + ⁅ Bn 0,
          -Bn 2⁆:= by rw [br02,nl];simp
        _ = ⁅(- (((B.repr ⟨u, ucomm⟩) 0 +  (B.repr ⟨v, vcomm⟩) 1))) • B 1,Bn 1⁆ + (-⁅ Bn 0,
          Bn 2 ⁆):= by rw [@neg_smul]; rw [@lie_neg]
        _ = (- (((B.repr ⟨u, ucomm⟩) 0 +  (B.repr ⟨v, vcomm⟩) 1))) • ⁅ B 1,Bn 1⁆ + (-⁅ Bn 0,
          Bn 2 ⁆):= by rw [@LieModule.smul_lie]
        _ = (- (((B.repr ⟨u, ucomm⟩) 0 +  (B.repr ⟨v, vcomm⟩) 1))) • ⁅ Bn 2,Bn 1⁆ + (-⁅ Bn 0,
          Bn 2 ⁆):= by
          rw [Bn21]
          rfl
        _ = (- (((B.repr ⟨u, ucomm⟩) 0 +  (B.repr ⟨v, vcomm⟩) 1))) • ⁅ Bn 2,Bn 1⁆ + (-(((B.repr ⟨u,
          ucomm⟩) 0 + (B.repr ⟨v, vcomm⟩) 1) • B 1)):= by rw [br02]
        _ = (- (((B.repr ⟨u, ucomm⟩) 0 +  (B.repr ⟨v, vcomm⟩) 1))) • (-⁅ Bn 1,Bn 2⁆) +
            (-(((B.repr ⟨u, ucomm⟩) 0 + (B.repr ⟨v, vcomm⟩) 1) • B 1)):= by rw [← lie_skew]
        _ = (- (((B.repr ⟨u, ucomm⟩) 0 +  (B.repr ⟨v, vcomm⟩) 1))) • (-Bn 2) + (-(((B.repr ⟨u,
          ucomm⟩) 0 + (B.repr ⟨v, vcomm⟩) 1) • B 1)):= by rw [nl]
        _ = (- (((B.repr ⟨u, ucomm⟩) 0 +  (B.repr ⟨v, vcomm⟩) 1))) • (-B 1) + (-(((B.repr ⟨u,
          ucomm⟩) 0 + (B.repr ⟨v, vcomm⟩) 1) • B 1)) := by rw [Bn21]
        _ = ( (((B.repr ⟨u, ucomm⟩) 0 +  (B.repr ⟨v, vcomm⟩) 1))) • B 1 + (-(((B.repr ⟨u,
          ucomm⟩) 0 + (B.repr ⟨v, vcomm⟩) 1)) • B 1) := by module
        _ = (( (((B.repr ⟨u, ucomm⟩) 0 +  (B.repr ⟨v, vcomm⟩) 1))) + (-(((B.repr ⟨u,
          ucomm⟩) 0 + (B.repr ⟨v, vcomm⟩) 1))))• B 1 := by module
        _ = 0 := by module
    have B1n0 : B 1 ≠ 0 := by
      exact Basis.ne_zero B 1
    have z : (B.repr ⟨u, ucomm⟩) 0 = 0 := by
      have sme := smul_eq_zero.mp d
      rcases sme with (p| q)
      · refine neg_eq_zero.mp ?_
        assumption
      · rw [@Submodule.coe_eq_zero] at q
        contradiction
    rw [z] at br02
    rw [z] at ucomp
    simp only [Fin.isValue, zero_smul, zero_add] at ucomp
    simp only [Nat.reduceAdd, Fin.isValue, zero_add] at br02
    rw [← Bn21] at br02
    have : ⁅Bn 0, Bn 1⁆ = (B.repr ⟨u, ucomm⟩) 1 • Bn 2 := by
      rw [Bn21]
      have := Subtype.ext_iff.mp ucomp
      exact this
    have h1 : Submodule.span K (Submodule.span K {Bn 2}).carrier = Submodule.span K {Bn 2} := by
      apply le_antisymm
      · exact Submodule.span_le.mpr fun ⦃a⦄ a ↦ a
      · apply Submodule.subset_span
    have hb : ∀ i j , ∃ (c: K), ⁅Bn i, Bn j⁆ = c • Bn 2 := by
      intro i j
      have i1: i = 0 ∨ i = 1 ∨ i = 2 := by
        fin_cases i <;> simp
      have i2: j = 0 ∨ j = 1 ∨ j = 2 := by
        fin_cases j <;> simp
      rcases i1 with (rfl|rfl|rfl)
      · rcases i2 with (rfl|rfl|rfl)
        · simp only [Nat.reduceAdd, Fin.isValue, lie_self]; use 0; simp
        · rw [this]; use (B.repr ⟨u, ucomm⟩) 1
        · rw [br02]; use (B.repr ⟨v, vcomm⟩) 1
      · rcases i2 with (rfl|rfl|rfl)
        · rw [← lie_skew,this]; use (- (B.repr ⟨u, ucomm⟩) 1); simp
        · simp only [Nat.reduceAdd, Fin.isValue, lie_self]; use 0; simp
        · rw [nl]; use 1; simp
      · rcases i2 with (rfl|rfl|rfl)
        · rw [← lie_skew,br02]; use (- (B.repr ⟨v, vcomm⟩) 1); simp
        · rw [← lie_skew,nl]; use (-1); simp
        · simp only [Nat.reduceAdd, Fin.isValue, lie_self]; use 0; simp
    have dimcomm := finrank_commutator_le_one_of_lie_basis Bn (Bn 2)
        (binary_predicate_3_choose_2 ⟨_, this⟩ ⟨_, br02⟩ ⟨1, by rw [one_smul]; exact nl⟩)
    rw [LieIdeal.finrank_toSubmodule] at dimcomm
    rw [h₂'] at dimcomm
    contradiction

/-- Helper for `case2_coarse_rat`: builds the linear-independence and bracket-equality witness.
Extracted to keep the proof of `case2_coarse_rat` within the proof-size limit. -/
private lemma case2_coarse_nuvn
    {B : Basis (Fin 3) K L}
    (h₂ : Module.finrank K (commutator K L) = 2)
    (br12 : ⁅B 1, B 2⁆ = 0)
    (hs : ∀ (α : K),
      ¬ (⁅B 0, B 1⁆ = α • B 1 ∧ ⁅B 0, B 2⁆ = α • B 2))
    {c01 c02 : K}
    (h01 : ⁅B 0, B 1⁆ = c01 • B 1)
    (h02 : ⁅B 0, B 2⁆ = c02 • B 2) :
    LinearIndependent K ![c01 • B 1 + c02 • B 2, B 1 + B 2] ∧
    ⁅B 0, B 1 + B 2⁆ = c01 • B 1 + c02 • B 2 := by
  have c01_not_zero : c01 ≠ 0 := by
    intro hc01
    rw [hc01] at h01
    simp only [Fin.isValue, zero_smul] at h01
    have comm_dim_1: Module.finrank K (commutator K L) ≤  1 := by
      have cs : {x : L | ∃ (y : L) (z : L), ⁅y, z⁆ = x} ≤  span K {B 2} := by
        intro x hx
        obtain ⟨y,z,hz⟩ := hx
        let cy := Basis.repr_fin_three B y
        let cz := Basis.repr_fin_three B z
        have cx : x = (((B.repr y) 0 • (B.repr z) 2 - (B.repr z) 0 •
            (B.repr y) 2) • c02) • B 2 := by
          calc x = ⁅(B.repr y) 0 • B 0 + (B.repr y) 1 • B 1 + (B.repr y) 2 • B 2,
            (B.repr z) 0 • B 0 + (B.repr z) 1 • B 1 + (B.repr z) 2 • B 2 ⁆:= by rw [← hz,← cy,
              ← cz]
               _ =  ⁅(B.repr y) 0 •  B 0, (B.repr z) 0 • B 0 + (B.repr z) 1 • B 1 +
                   (B.repr z) 2 • B 2 ⁆
                  + ⁅ (B.repr y) 1 • B 1, (B.repr z) 0 • B 0 + (B.repr z) 1 • B 1 +
                      (B.repr z) 2 • B 2 ⁆
                  + ⁅ (B.repr y) 2 • B 2, (B.repr z) 0 • B 0 + (B.repr z) 1 • B 1 +
                      (B.repr z) 2 • B 2 ⁆:= by rw[add_lie,add_lie]
               _ = (B.repr y) 0 •⁅  B 0, (B.repr z) 0 • B 0 + (B.repr z) 1 • B 1 +
                   (B.repr z) 2 • B 2 ⁆
                  + (B.repr y) 1 • ⁅  B 1, (B.repr z) 0 • B 0 + (B.repr z) 1 • B 1 +
                      (B.repr z) 2 • B 2 ⁆
                  + (B.repr y) 2 • ⁅  B 2, (B.repr z) 0 • B 0 + (B.repr z) 1 • B 1 +
                      (B.repr z) 2 • B 2 ⁆:= by rw[smul_lie,smul_lie,smul_lie]
               _ = (B.repr y) 0 • (B.repr z) 0 • ⁅ B 0,B 0 ⁆ + (B.repr y) 0 •
                   (B.repr z) 1 • ⁅ B 0,  B 1 ⁆ +(B.repr y) 0 • (B.repr z) 2 • ⁅ B 0,  B 2 ⁆
                  + (B.repr y) 1 •  (B.repr z) 0 •⁅  B 1, B 0 ⁆
                  + (B.repr y) 1 • (B.repr z) 1 •⁅  B 1,  B 1 ⁆
                  + (B.repr y) 1 •  (B.repr z) 2 •⁅  B 1,  B 2 ⁆
                  + (B.repr y) 2 • (B.repr z) 0 •⁅  B 2,  B 0  ⁆
                  + (B.repr y) 2 • (B.repr z) 1 • ⁅  B 2, B 1  ⁆
                  + (B.repr y) 2 •  (B.repr z) 2 •⁅  B 2,
                    B 2 ⁆:= by repeat rw[lie_add,lie_smul];simp;module
               _ =  (B.repr y) 0 • (B.repr z) 2 • ⁅ B 0,  B 2 ⁆
                  + (B.repr y) 1 •  (B.repr z) 0 •⁅  B 1, B 0 ⁆
                  + (B.repr y) 2 • (B.repr z) 0 •⁅  B 2,  B 0  ⁆
                  + (B.repr y) 2 • (B.repr z) 1 • ⁅  B 2,
                    B 1  ⁆  :=by repeat rw[lie_self];rw[h01,br12];simp
               _ =  (B.repr y) 0 • (B.repr z) 2 • ⁅ B 0,  B 2 ⁆
                  + (B.repr y) 1 •  (B.repr z) 0 • - ⁅  B 0, B 1 ⁆
                  + (B.repr y) 2 • (B.repr z) 0 •⁅  B 2,  B 0  ⁆
                  + (B.repr y) 2 • (B.repr z) 1 • -⁅  B 1,
                    B 2  ⁆  :=by nth_rw 2 [← lie_skew];nth_rw 4 [← lie_skew]
               _ =  (B.repr y) 0 • (B.repr z) 2 • ⁅ B 0,
                 B 2 ⁆ + (B.repr y) 2 • ((B.repr z) 0 • ((-1 : K) • ⁅  B 0,
                   B 2  ⁆)) :=by rw[h01,br12];simp
               _ =  (B.repr y) 0 • (B.repr z) 2 • ⁅ B 0,
                 B 2 ⁆+ ((B.repr y) 2 * ((B.repr z) 0 * (-1 : K)))• ⁅  B 0,
                   B 2  ⁆ :=by rw [smul_smul (a₂ := -1), smul_smul (a₁ := (B.repr y) 2)]
               _ =  ((B.repr y) 0 * (B.repr z) 2) • ⁅ B 0,
                 B 2 ⁆+ ((B.repr y) 2 * ((B.repr z) 0 * (-1 : K)))• ⁅  B 0,
                   B 2  ⁆ :=by rw [smul_smul]
               _ =  ((B.repr y) 0 * (B.repr z) 2 + (B.repr y) 2 * ((B.repr z) 0 *
                   (-1 : K))) • ⁅  B 0,  B 2 ⁆ :=by rw [add_smul]
               _ =  ( ((B.repr y) 0 * (B.repr z) 2 - (B.repr z) 0 * (B.repr y) 2)) • ⁅  B 0,
                 B 2 ⁆ := by rw [mul_neg, mul_neg, mul_one ((B.repr z) 0), sub_eq_add_neg,
                   mul_comm ((B.repr y) 2)]
               _ =  ( ((B.repr y) 0 • (B.repr z) 2 - (B.repr z) 0 •
                   (B.repr y) 2) • c02 ) • B 2 := by rw [h02]; rw [smul_assoc]; rfl
        symm at cx
        have mm := Submodule.mem_span_singleton.mpr ⟨_, cx⟩
        assumption
      apply Submodule.span_le.mpr at cs
      have : (commutator K L).toSubmodule = span K {x : L | ∃ (y : L) (z : L), ⁅y,
        z⁆ = x} := commutator_eq_span
      rw [← this] at cs
      apply Submodule.finrank_mono at cs
      rw [finrank_span_singleton] at cs
      · exact cs
      exact Basis.ne_zero B 2
    rw [h₂] at comm_dim_1
    contradiction
  have c02_not_zero : c02 ≠ 0 := by
    intro hc02
    rw [hc02] at h02
    simp only [Fin.isValue, zero_smul] at h02
    have h20 : ⁅B 2, B 0⁆ = 0 := by
      rw [← lie_skew, h02]
      simp
    have h10 : ⁅B 1, B 0⁆ = (-c01) • B 1 := by
      rw [← lie_skew, h01]
      simp
    have h21 : ⁅B 2, B 1⁆ = 0 := by
      rw [← lie_skew, br12]
      simp
    have comm_dim_1: Module.finrank K (commutator K L) ≤  1 := by
      have cs : {x : L | ∃ (y : L) (z : L), ⁅y, z⁆ = x} ≤  span K {B 1} := by
        intro x hx
        obtain ⟨y,z,hz⟩ := hx
        let cy := Basis.repr_fin_three B y
        let cz := Basis.repr_fin_three B z
        have cx : x = (((B.repr y) 0 • (B.repr z) 1 - (B.repr z) 0 •
            (B.repr y) 1) • c01) • B 1 := by
          rw [← hz]
          rw [cy, cz]
          repeat rw [lie_add]
          repeat rw [add_lie]
          repeat rw [lie_smul]
          repeat rw [smul_lie]
          rw [h01, h02, h20, h21, h10, br12]
          repeat rw [lie_self]
          simp only [Fin.isValue, smul_zero, neg_smul, smul_neg, zero_add,
            add_zero, map_add, map_smul, Basis.repr_self, Finsupp.smul_single,
            smul_eq_mul, mul_one, Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same,
            ne_eq, one_ne_zero, not_false_eq_true, Finsupp.single_eq_of_ne, Fin.reduceEq,
            zero_ne_one]
          module
        symm at cx
        have mm := Submodule.mem_span_singleton.mpr ⟨_, cx⟩
        assumption
      apply Submodule.span_le.mpr at cs
      have : (commutator K L).toSubmodule = span K {x : L | ∃ (y : L) (z : L), ⁅y,
        z⁆ = x} := commutator_eq_span
      rw [← this] at cs
      apply Submodule.finrank_mono at cs
      rw [finrank_span_singleton] at cs
      · exact cs
      exact Basis.ne_zero B 1
    rw [h₂] at comm_dim_1
    contradiction
  have c01_neq_c02 : c01 ≠ c02 := by
    intro c01c02
    specialize hs c01
    apply hs
    constructor
    · assumption
    · rw [c01c02]
      assumption
  constructor
  · apply (LinearIndependent.pair_iff' _).mpr
    · intro a ha
      rw [smul_add] at ha
      have B12_li : LinearIndependent K ![B 1, B 2] := by
        rw [@LinearIndependent.pair_iff]
        intro s t hst
        have := (Fintype.linearIndependent_iff).mp B.linearIndependent ![0, s, t]
        have heqq : ∑ x : Fin 3, ![0, s, t] x • B x = s • B 1 + t • B 2 := by
          rw [@Fin.sum_univ_three]
          simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue,
            Matrix.cons_val_zero, zero_smul, Matrix.cons_val_one, Matrix.head_cons,
            zero_add, Matrix.cons_val_two, Matrix.tail_cons]
        rw [hst] at heqq
        specialize this heqq
        constructor
        · exact (this 1)
        · exact (this 2)
      have hh := LinearIndependent.pair_iffₛ.mp B12_li (a • c01) (a • c02) 1 1
      have hha :  (a • c01) • B 1 + (a • c02) • B 2 = (1 : K) • B 1 + (1 : K) • B 2 := by
        simp only [smul_eq_mul, one_smul]
        rw [mul_smul, mul_smul]
        rw [ha]
      specialize hh hha
      apply c01_neq_c02
      have a_not_zero : a ≠ 0 := by
        simp only [smul_eq_mul] at hh
        let hh1 := hh.1
        rw [mul_comm] at hh1
        apply (right_ne_zero_of_mul (a := c01))
        have h : 1 ≠ (0 : K) := by simp
        rw [hh1]
        assumption
      have hc01 : c01 = (1 : K) / a := by
        rw [← hh.1]
        simp only [smul_eq_mul]
        rw [mul_div_cancel_left₀ _ a_not_zero]
      have hc02 : c02 = (1 : K) / a := by
        rw [← hh.2]
        simp only [smul_eq_mul]
        rw [mul_div_cancel_left₀ _ a_not_zero]
      rw [hc01,hc02]
    · intro heq
      have := (Fintype.linearIndependent_iff).mp B.linearIndependent ![0, c01, c02]
      have heqq : ∑ x : Fin 3, ![0, c01, c02] x • B x = c01 • B 1 + c02 • B 2 := by
        rw [@Fin.sum_univ_three]
        simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Matrix.cons_val_zero,
          zero_smul, Matrix.cons_val_one, Matrix.head_cons, zero_add, Matrix.cons_val_two,
          Matrix.tail_cons]
      rw [heq] at heqq
      specialize this heqq 1
      simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero] at this
      apply c01_not_zero
      exact this
  · rw [lie_add]
    rw [h01, h02]

/-- Helper for `case2_coarse`: produce a witness `X` such that `⁅B 0, X⁆` and `X`
are linearly independent and `X` lies in the commutator. Extracted to keep the
proof of `case2_coarse` within the proof-size limit. -/
private lemma case2_coarse_rat
    {B : Basis (Fin 3) K L}
    (h₂ : Module.finrank K (commutator K L) = 2)
    (B1c : B 1 ∈ commutator K L)
    (B2c : B 2 ∈ commutator K L)
    (br12 : ⁅B 1, B 2⁆ = 0)
    (hs : ∀ (α : K),
      ¬ (⁅B 0, B 1⁆ = α • B 1 ∧ ⁅B 0, B 2⁆ = α • B 2)) :
    ∃ (X : L), LinearIndependent K (![⁅B 0, X⁆, X]) ∧ X ∈ commutator K L := by
  by_cases ha : LinearIndependent K (![⁅B 0, B 1⁆,B 1 ])
  · use (B 1)
  · by_cases hb : LinearIndependent K (![⁅B 0, B 2⁆, B 2])
    · use (B 2)
    · rw [not_linearIndependent_pair_iff ⁅B 0, B 1⁆ (B 1) (Basis.ne_zero B 1)] at ha
      rw [not_linearIndependent_pair_iff ⁅B 0, B 2⁆ (B 2) (Basis.ne_zero B 2)] at hb
      obtain ⟨ c01, h01⟩ :=ha
      obtain ⟨ c02, h02⟩ :=hb
      have nuvn := case2_coarse_nuvn h₂ br12 hs h01 h02
      have := nuvn
      use (B 1 + B 2)
      rw [this.2]
      constructor
      · exact this.1
      · exact add_mem B1c B2c

/-- Helper for `case2_coarse`: linear independence of the candidate basis
`![B 0, X, ⁅B 0, X⁆]`. Extracted to keep the proof of `case2_coarse` within
the proof-size limit. -/
private lemma case2_coarse_Bnli
    {B : Basis (Fin 3) K L}
    {X : L}
    (h₂ : Module.finrank K (commutator K L) = 2)
    (hXli : LinearIndependent K ![⁅B 0, X⁆, X])
    (hXc : X ∈ commutator K L)
    (B1c : B 1 ∈ commutator K L)
    (B2c : B 2 ∈ commutator K L) :
    LinearIndependent K (![B 0, X, ⁅B 0, X⁆] : Fin 3 → L) := by
  rw [@linearIndependent_finSucc]
  have : Fin.tail (![B 0, X, ⁅B 0, X⁆] : Fin 3 → L) = ![X, ⁅B 0, X⁆] := rfl
  constructor
  · rw [this]
    rw [LinearIndependent.pair_iffₛ]
    rw [LinearIndependent.pair_iffₛ] at hXli
    intro s t s' t'
    rw [add_comm (a:=s' • X), add_comm ]
    intro u
    let ⟨s_eq_s', t_eq_t'⟩ := hXli t s t' s' u
    exact ⟨t_eq_t',s_eq_s'⟩
  · intro h
    rw [this] at h
    have Bn0B0 : (![B 0, X, ⁅B 0, X⁆] : Fin 3 → L) 0 = B 0 := rfl
    rw [Bn0B0] at h
    have subset : Set.range ![⁅B 0, X⁆, X] ⊆ commutator K L := by
      apply Set.range_subset_iff.mpr
      simp only [derivedSeriesOfIdeal_succ, derivedSeriesOfIdeal_zero, SetLike.mem_coe]
      intro w
      have i1 : w = 0 ∨ w = 1 := by fin_cases w <;> simp
      rcases i1 with (w1|w2)
      · rw [w1]
        simp only [Matrix.cons_val_zero]
        apply lie_mem_commutator
      · subst w2
        simp only [Fin.isValue, Matrix.cons_val_one]
        exact hXc
    have sc : span K (Set.range ![⁅B 0, X⁆, X]) ≤ commutator K L := span_le.mpr subset
    rw [@Matrix.range_cons_cons_empty] at h
    have B0c : B 0 ∈ commutator K L := by
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue,
        Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.union_singleton, derivedSeriesOfIdeal_succ,
        derivedSeriesOfIdeal_zero, LieIdeal.toLieSubalgebra_toSubmodule] at sc
      apply sc
      exact h
    have brange : Set.range B ⊆ commutator K L := by
      rw [Set.range_subset_iff]
      intro y
      have yr : y=0 ∨ y=1 ∨ y=2 := by fin_cases y <;> simp
      rcases yr with (j0|j1|j2)
      · rw [j0]; exact B0c
      · rw [j1]; exact B1c
      · rw [j2]; exact B2c
    have dimc : 3 ≤ Module.finrank K (commutator K L) := by
      have Bli := B.linearIndependent
      have hp := Submodule.linearIndependent_from_ambient (commutator K L) B Bli brange
      have : Module.Finite K ↥(LieIdeal.toLieSubalgebra K L (commutator K L)).toSubmodule := by
        simp only [LieIdeal.toLieSubalgebra_toSubmodule]
        change Module.Finite K (commutator K L)
        exact finite_of_finrank_eq_succ h₂
      have := LinearIndependent.fintype_card_le_finrank hp
      simp only [Fintype.card_fin, LieIdeal.toLieSubalgebra_toSubmodule,
        SetLike.coe_sort_coe] at this
      simp only [ge_iff_le]
      exact this
    rw [h₂] at dimc
    contradiction

--Case 2: The commutator has dimension 2.
lemma case2_coarse (dim3 : Module.finrank K L = 3) (h₂ : Module.finrank K (commutator K L) = 2) :
    (∃ B : Basis (Fin 3) K L, ⁅B 0, B 1⁆ =  B 1 ∧ ⁅B 0, B 2⁆ = B 2 ∧ ⁅B 1, B 2⁆ = 0) ∨ -- Hyperbolic
    (∃ B : Basis (Fin 3) K L, ⁅B 0, B 1⁆ = B 2 ∧ ⁅B 1, B 2⁆ = 0 ∧ (∃ α β : K, α ≠ 0 ∧ ⁅B 0,
      B 2⁆ = α • B 1 + β • B 2)) := by --Family α β , α ≠ 0
  have _ : Module.Finite K (commutator K L) := by
    exact finite_of_finrank_eq_succ h₂
  -- take a basis of the commutator
  let  V := finBasisOfFinrankEq K (commutator K L) h₂
  have V0c : (V 0).val ∈ (commutator K L) :=by
    exact SetLike.coe_mem (V 0)
  have V1c : (V 1).val ∈ (commutator K L) :=by
    exact SetLike.coe_mem (V 1)
  have Vli := V.linearIndependent
  have VL := (LinearIndependent.iff_in_submodule
      (commutator K L).toSubmodule).mp V.linearIndependent
  -- extend the basis of the commutator to a basis of L
  set B := Basis.extendFinSucc VL dim3 with Beq
  have B1isV0 : B 1 = V 0 := by
    have := Basis.extend_fin_succ_tail_eq VL dim3
    apply_fun (fun x ↦ x 0) at this
    simp only [Nat.reduceAdd, Fin.isValue, Function.comp_apply] at this
    rw [← this]
    exact rfl
  have B2isV1 : B 2 = V 1 := by
    have := Basis.extend_fin_succ_tail_eq VL dim3
    apply_fun (fun x ↦ x 1) at this
    simp only [Nat.reduceAdd, Fin.isValue, Function.comp_apply] at this
    rw [← this]
    exact rfl
  have B1c : (B 1) ∈ commutator K L := by
    rw [B1isV0]
    exact V0c
  have B2c : (B 2) ∈ commutator K L := by
    rw [B2isV1]
    exact V1c
  --the commutator is abelian
  have cab:= commutator_abelian_of_dim_two dim3 h₂
  rw [@LieSubmodule.lie_abelian_iff_lie_self_eq_bot] at cab
  rw [@LieSubmodule.lie_eq_bot_iff] at cab
  have br12 : ⁅B 1, B 2⁆ = 0 :=by
    exact cab (B 1) B1c (B 2) B2c
  --every Lie bracket is a linear combination of V
  have lie_comm : ∀ (x y : L), ∃ (c d : K), ⁅ x , y ⁆ = c • V 0 + d • V 1 := by
    intro x y
    have eq := Basis.repr_fin_two (B:=V) (x:=⟨⁅x, y⁆, lie_mem_commutator x y ⟩)
    have meq := Subtype.ext_iff.mp eq
    simp at meq
    use (V.repr ⟨⁅x, y⁆, lie_mem_commutator x y⟩ 0)
    use (V.repr ⟨⁅x, y⁆, lie_mem_commutator x y⟩ 1)
  -- we split the proof in two cases
  --- the fist case is when ad_{B0}=α Id
  by_cases  hs : ∃ (α : K), ⁅B 0, B 1⁆ = α • B 1 ∧ ⁅B 0, B 2⁆ = α • B 2
  · left
    obtain ⟨α, hα⟩ := hs
    have anz : α ≠ 0 :=by
      intro fa
      rw [fa] at hα
      simp only [Nat.reduceAdd, Fin.isValue, zero_smul] at hα
      have isab : IsLieAbelian L := by
        rw [abelian_iff_lie_basis_eq_zero B]
        apply binary_predicate_3_choose_2
        · exact hα.1
        · exact hα.2
        · exact br12
      have : FiniteDimensional K L:= Module.finite_of_finrank_eq_succ dim3
      have:= (LieAlgebra.abelian_iff_dim_comm_zero (K:=K)).mpr isab
      rw [this] at h₂
      contradiction
    let αunit : Kˣ := by
      apply Units.mk0 α⁻¹
      simp only [ne_eq, inv_eq_zero,anz,not_false_eq_true]
    let ⟨B'Basis, B'0, B'1, B'2⟩ := Basis.exists_unitsSMul B αunit 1 1
    use B'Basis
    rw [B'0, B'1, B'2]
    simp_all only [Units.smul_mk0, one_smul, smul_lie, ne_eq, not_false_eq_true, inv_smul_smul₀,
      and_self, V, B, αunit]
  --- the second case is when ad_{B0}≠ α Id, ∀ α
  · right
    rw [@Mathlib.Tactic.Push.not_exists] at hs
    --we rewrite the hypothesis ad_{B0}≠ α Id, ∀ α
    have hsn : ∀ (α : K), ⁅B 0, B 1⁆ ≠  α • B 1 ∨  ⁅B 0, B 2⁆ ≠  α • B 2 := by
      intro α
      repeat rw [@Ne.eq_def]
      rw [← not_and_or]
      exact hs α
    -- we claim that there exists X ∈ L such that [B 0, X] is linearly independent with X
    have rat : ∃ (X : L), LinearIndependent K (![⁅B 0, X⁆, X ]) ∧ (X ∈ commutator K L) :=
      case2_coarse_rat h₂ B1c B2c br12 (fun α => (hsn α).elim
        (fun h ⟨h₁, _⟩ => h h₁) (fun h ⟨_, h₂⟩ => h h₂))
    -- (rat extracted above as case2_coarse_rat)
    have _placeholder_rat : True := trivial
    -- old inline branch (now unused):
    -- (deleted; see case2_coarse_rat)
    -- BEGIN UNUSED

    -- we use the X above to produce a basis of L satisfying the conditions in the statement
    obtain ⟨X, hXli,hXc⟩ := rat
    let Bn := ![B 0, X, ⁅B 0, X⁆]
    have Bnli : LinearIndependent K Bn := case2_coarse_Bnli h₂ hXli hXc B1c B2c
    let BnBasis : Basis (Fin 3) K L :=
      basisOfLinearIndependentOfCardEqFinrank Bnli (by simp only [Fintype.card_fin]; rw [dim3])
    use BnBasis
    have BnB01 : ⁅BnBasis 0, BnBasis 1⁆ = BnBasis 2 := by
      rw [coe_basisOfLinearIndependentOfCardEqFinrank]
      dsimp [Bn]
    have BnB12 : ⁅BnBasis 1, BnBasis 2⁆ = 0 := by
      rw [coe_basisOfLinearIndependentOfCardEqFinrank]
      dsimp [Bn]
      simp only [V, B]
      apply cab
      · exact hXc
      · simp only [derivedSeriesOfIdeal_succ, derivedSeriesOfIdeal_zero, Fin.isValue]
        exact LieSubmodule.lie_mem_lie trivial trivial
    constructor
    · exact BnB01
    · constructor
      · exact BnB12
      · rw [coe_basisOfLinearIndependentOfCardEqFinrank]
        dsimp [Bn]
        simp only [exists_and_left, V, B]
        have XcX := Submodule.linearIndependent_from_ambient (commutator K L) (![⁅B 0, X⁆, X]) hXli
          (by simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Matrix.range_cons,
            Matrix.range_empty, Set.union_empty, Set.union_singleton,
            derivedSeriesOfIdeal_succ, derivedSeriesOfIdeal_zero,
            LieIdeal.toLieSubalgebra_toSubmodule, V, B]
              apply Set.pair_subset_iff.mpr
              constructor
              · exact hXc
              · exact LieSubmodule.lie_mem_lie trivial trivial
          )
        simp only [Nat.succ_eq_add_one, Nat.reduceAdd, LieIdeal.toLieSubalgebra_toSubmodule,
          SetLike.coe_sort_coe, Fin.isValue, V, B] at XcX
        let XcXBasis : Basis (Fin 2) K (commutator K L) :=
          basisOfLinearIndependentOfCardEqFinrank XcX (by simp only [Fintype.card_fin]; rw [h₂])
        have XcXBasis0 : XcXBasis 0 = ⁅B 0, X⁆ := by
          rw [coe_basisOfLinearIndependentOfCardEqFinrank]
          rw [Set.map_into_subtype_apply]
          simp [B]
        have XcXBasis1 : XcXBasis 1 = X := by
          rw [coe_basisOfLinearIndependentOfCardEqFinrank]
          rw [Set.map_into_subtype_apply]
          simp
        let x : commutator K L := ⟨⁅B 0, ⁅B 0, X⁆⁆, by
          simp only [derivedSeriesOfIdeal_succ, derivedSeriesOfIdeal_zero,
            Nat.reduceAdd, Fin.isValue, V, B]
          exact LieSubmodule.lie_mem_lie trivial trivial
         ⟩
        let co := Basis.repr_fin_two (B:=XcXBasis) (x:=x)
        use (XcXBasis.repr x) 1
        symm
        have BnB02 : ⁅BnBasis 0, BnBasis 2⁆ = (XcXBasis.repr x) 1 • BnBasis 1 +
            (XcXBasis.repr x) 0 • BnBasis 2 := by
          have meq := Subtype.ext_iff.mp co
          unfold x at meq
          simp only [Nat.reduceAdd, Fin.isValue, LieSubmodule.coe_add, SetLike.val_smul, V, B,
            ] at meq
          rw [XcXBasis0,XcXBasis1] at meq
          rw [coe_basisOfLinearIndependentOfCardEqFinrank]
          dsimp [Bn]
          simp only [Fin.isValue, B, V]
          rw [meq]
          module
        constructor
        · use (XcXBasis.repr x) 0
          rw [coe_basisOfLinearIndependentOfCardEqFinrank] at BnB02
          dsimp [Bn] at BnB02
          simp only [Fin.isValue, V, B] at BnB02
          exact BnB02
        · intro hr
          rw [hr] at co
          simp only [Fin.isValue, zero_smul, add_zero] at co
          dsimp [x] at co
          simp only [Fin.isValue, V, B] at co
          have BnB02' : ⁅BnBasis 0, BnBasis 2⁆ = (XcXBasis.repr x) 0 • BnBasis 2 := by
            rw [hr] at BnB02
            simp only [Fin.isValue, zero_smul, zero_add, V, B, x] at BnB02
            exact BnB02
          have dc : finrank K (commutator K L) ≤ 1 := by
            apply finrank_commutator_le_one_of_lie_basis BnBasis (BnBasis 2)
            apply binary_predicate_3_choose_2
            · use (1 : K); rw [BnB01, one_smul]
            · exact ⟨_, BnB02'⟩
            · use (0 : K); rw [BnB12, zero_smul]
          rw [h₂] at dc
          contradiction

lemma finrank_com_eq2_from_basis_bracket
    (hb : (∃ B : Basis (Fin 3) K L, ⁅B 0, B 1⁆ = B 2 ∧ ⁅B 1, B 2⁆ = 0 ∧ (∃ α β : K, α ≠ 0 ∧ ⁅B 0,
      B 2⁆ = α • B 1 + β • B 2))) :
      Module.finrank K (LieAlgebra.commutator K L) = 2 := by
  obtain ⟨B,⟨pfB01,pfB12,⟨α,β, ⟨anz,pfB02⟩⟩⟩⟩ := hb
  have hcomm :  (LieAlgebra.commutator K L).toSubmodule = Submodule.span K {B 1, B 2} := by
    rw [LieAlgebra.commutator_eq_span]
    apply le_antisymm
    · rw [Submodule.span_le]
      intro x ⟨y,z,h⟩
      rw [← h,Basis.repr_fin_three B y, Basis.repr_fin_three B z]
      simp only [lie_add, lie_smul, add_lie, smul_lie, lie_self, smul_zero,
       zero_add, smul_add, add_zero, SetLike.mem_coe]
      rw [← lie_skew (B 1) (B 0), ← lie_skew (B 2) (B 0), ← lie_skew (B 2) (B 1)]
      repeat rw [pfB01, pfB02, pfB12]
      simp only [smul_neg, neg_zero, smul_zero, add_zero]
      rw [Submodule.mem_span_pair]
      use (-(B.repr z) 0 • (B.repr y) 2 • α + (B.repr z) 2 • (B.repr y) 0 • α)
      use (  -(B.repr z) 0 • (B.repr y) 1  + -((B.repr z) 0 • (B.repr y) 2 • β ) + (B.repr z) 1 •
          (B.repr y) 0 + (B.repr z) 2 • (B.repr y) 0 • β  )
      match_scalars
      · simp only [smul_eq_mul,Fin.isValue, neg_mul, mul_one,smul_eq_mul]
      · simp only [Fin.isValue, smul_eq_mul, neg_mul, mul_one]
    · have h1 :  B 1 ∈  {x | ∃ (y z:L), ⁅y, z⁆ = x} :=by
        rw [Set.mem_setOf_eq]
        use α⁻¹ • B 0
        use B 2 - β • B 1
        simp_all only [Fin.isValue, ne_eq, lie_sub, smul_lie, smul_add, not_false_eq_true,
          inv_smul_smul₀, lie_smul]
        rw [smul_comm]
        simp
      have h2 :  B 2 ∈  {x | ∃ (y z:L), ⁅y, z⁆ = x} :=by
        rw [Set.mem_setOf_eq]
        use B 0
        use B 1
      apply  Submodule.span_monotone
      intro x hx
      simp_all only [Fin.isValue, ne_eq, Set.mem_setOf_eq, Set.mem_insert_iff,
        Set.mem_singleton_iff]
      cases hx with
        | inl eq =>
          subst eq
          exact h1
        | inr eq =>
          subst eq
          exact h2
  apply_fun (Module.finrank K) at hcomm
  have : Module.finrank K ↥(Submodule.span K {B 1, B 2}) = 2 := by
    have range_b : { B 1, B 2 } = Set.range ![B 1, B 2] := by aesop
    rw [range_b]
    rw [finrank_span_eq_card, Fintype.card_fin]
    convert_to LinearIndependent K (⇑B ∘ ![1, 2])
    · ext j; fin_cases j <;> rfl
    · apply LinearIndependent.comp B.linearIndependent
      intro x y hxy
      fin_cases x, y <;> simp_all
  rw [← this]
  exact hcomm

lemma case2 : Module.finrank K L = 3 ∧ Module.finrank K (commutator K L) = 2 ↔
    (∃ B : Basis (Fin 3) K L, ⁅B 0, B 1⁆ =  B 1 ∧ ⁅B 0, B 2⁆ = B 2 ∧ ⁅B 1, B 2⁆ = 0) ∨ --Hyperbolic
    (∃ B : Basis (Fin 3) K L, ⁅B 0, B 1⁆ = B 2 ∧ ⁅B 1, B 2⁆ = 0 ∧ (∃ α : K, α ≠ 0 ∧ ⁅B 0,
      B 2⁆ = α • B 1)) ∨ --Family α 0, α≠ 0
    (∃ B : Basis (Fin 3) K L, ⁅B 0, B 1⁆ = B 2 ∧ ⁅B 1, B 2⁆ = 0 ∧ (∃ α : K, α ≠ 0 ∧ ⁅B 0,
      B 2⁆ = α • B 1 + B 2)):= by --Family α 1 , α≠ 0
  constructor
  · intro ⟨dim3, dim2c⟩
    obtain (⟨B, pfB⟩|⟨B',⟨pfB01,pfB12,⟨α,β, ⟨anz,pfB02⟩⟩⟩⟩) := case2_coarse dim3 dim2c
    · left
      use B
    · right
      by_cases hb : (β =0)
      · left
        rw [hb] at pfB02
        simp only [Fin.isValue, zero_smul, add_zero] at pfB02
        use B'
        exact ⟨pfB01, pfB12, ⟨α,anz,pfB02⟩⟩
      · right
        let βunit : Kˣ := by
          apply Units.mk0 β
          simp only [ne_eq,hb,not_false_eq_true]
        let βinvunit : Kˣ := by
          apply Units.mk0 β⁻¹
          simp only [ne_eq, inv_eq_zero,hb,not_false_eq_true]
        let β2unit : Kˣ := by
          apply Units.mk0 (β*β)
          simp only [ne_eq, mul_eq_zero, or_self,hb,not_false_eq_true]
        let ⟨B'', B''0, B''1, B''2⟩ := Basis.exists_unitsSMul B' βinvunit β2unit βunit
        use B''
        rw [B''0, B''1, B''2]
        constructor
        · dsimp [βunit, βinvunit, β2unit]
          simp_all only [Fin.isValue, ne_eq, Units.smul_mk0, Units.mk0_mul, lie_smul, smul_lie,
            βinvunit, βunit,
            β2unit]
          match_scalars
          simp_all only [Fin.isValue, mul_one, isUnit_iff_ne_zero, ne_eq, not_false_eq_true,
            IsUnit.mul_inv_cancel_right]
        · dsimp [βunit, βinvunit, β2unit]
          constructor
          · rw [lie_smul,smul_lie,pfB12]
            simp only [smul_zero]
          · use α*(β^2)⁻¹
            constructor
            · simp_all only [Fin.isValue, ne_eq, Units.smul_mk0, Units.mk0_mul, mul_eq_zero,
              inv_eq_zero,
              OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, or_self, βinvunit, βunit,
                β2unit]
            · simp_all only [Fin.isValue, ne_eq, Units.smul_mk0, Units.mk0_mul, lie_smul, smul_lie,
              smul_add,
              not_false_eq_true, inv_smul_smul₀, smul_inv_smul₀, add_left_inj,
                βinvunit, βunit, β2unit]
              match_scalars
              simp only [mul_one]
              ring_nf
              simp_all only [Fin.isValue, inv_pow, isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero,
                not_false_eq_true,
                pow_eq_zero_iff, IsUnit.mul_inv_cancel_right]
  · rintro (⟨B,hB01,hB02,hB12⟩|⟨B,hB01,hB02,⟨α, anz, hB12⟩⟩| ⟨B,hB01,hB02,⟨α, anz, hB12⟩⟩)
    · constructor
      · rw [finrank_eq_card_basis B, Fintype.card_fin]
      · have hcomm : (commutator K L).toSubmodule = span K {B 1, B 2} := by
          rw [commutator_eq_span]
          apply le_antisymm
          · rw [span_le]
            intro x ⟨y,z,h⟩
            rw [← h,Basis.repr_fin_three B y, Basis.repr_fin_three B z]
            simp only [lie_add, lie_smul, add_lie, smul_lie, lie_self, smul_zero,
              zero_add, smul_add, add_zero, SetLike.mem_coe]
            rw [← lie_skew (B 1) (B 0), ← lie_skew (B 2) (B 0), ← lie_skew (B 2) (B 1)]
            repeat rw [hB01, hB02, hB12]
            simp only [smul_neg, neg_zero, smul_zero, add_zero]
            rw [@mem_span_pair]
            use (-((B.repr z) 0 • (B.repr y) 1 ) + (B.repr z) 1 • (B.repr y) 0 )
            use ( -((B.repr z) 0 • (B.repr y) 2 ) + (B.repr z) 2 • (B.repr y) 0 )
            simp only [smul_eq_mul]
            module
          · rw [span_le]
            trans {x | ∃ (y z:L), ⁅y, z⁆ = x}
            · intro Bi hBi
              simp_all only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq]
              cases hBi with
              | inl h => subst h; exact ⟨_, _, hB01⟩
              | inr h => subst h; exact ⟨_, _, hB02⟩
            · apply Submodule.subset_span
        apply_fun (finrank K) at hcomm
        trans finrank K ↥(span K {B 1, B 2})
        · exact hcomm
        · have range_b : { B 1, B 2 } = Set.range ![B 1, B 2] := by aesop
          have hli : LinearIndependent K (![B 1, B 2]) := by
            convert_to LinearIndependent K (⇑B ∘ ![1, 2])
            · ext j; fin_cases j <;> rfl
            · apply LinearIndependent.comp B.linearIndependent
              intro x y hxy
              fin_cases x, y <;> simp_all
          have key : Set.finrank K (Set.range ![B 1, B 2]) = Fintype.card (Fin 2) :=
            ((linearIndependent_iff_card_eq_finrank_span).mp hli).symm
          rw [show finrank K ↥(span K {B 1, B 2})
            = Set.finrank K (Set.range ![B 1, B 2]) by rw [Set.finrank, range_b], key,
            Fintype.card_fin]
    · constructor
      · rw [finrank_eq_card_basis B, Fintype.card_fin]
      · apply finrank_com_eq2_from_basis_bracket
        use B
        refine ⟨hB01,hB02, ⟨α,0,anz,(by simp only [Fin.isValue, zero_smul, add_zero];exact hB12)⟩⟩
    · constructor
      · rw [finrank_eq_card_basis B, Fintype.card_fin]
      · apply finrank_com_eq2_from_basis_bracket
        use B
        refine ⟨hB01,hB02, ⟨α,1,anz,(by simp only [Fin.isValue, one_smul];exact hB12)⟩⟩

end Dim3

end LieAlgebra
