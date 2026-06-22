/-
Copyright (c) 2026 the LieLean team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Viviana del Barco, Gustavo Infanti, Exequiel Rivas, Paul Schwahn
-/
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Solvable
import Mathlib.Algebra.Lie.Derivation.Basic
import Mathlib.Algebra.Lie.AdjointAction.Derivation
import Mathlib.Algebra.Lie.Submodule
import Mathlib.Algebra.Lie.Ideal
import Mathlib.Algebra.Lie.Nilpotent

/-!
# LeanPool.LowDimSolvClassification.GeneralResults
-/

---possible generalizations to commutative rings instead of fields

section linalg
open Module
open Submodule

variable {K L : Type*} [Field K] [AddCommGroup L] [Module K L]

/-- In a basis of size 1, we represent any element as an explicit sum. -/
theorem Basis.repr_fin_one (B : Basis (Fin 1) K L) (x : L) :
    x = B.repr x 0 • B 0 := by
  conv_lhs => rw [← B.sum_repr x]
  rw [Fin.sum_univ_one]

/-- In a basis of size 2, we represent any element as an explicit sum. -/
theorem Basis.repr_fin_two (B : Basis (Fin 2) K L) (x : L) :
    x = B.repr x 0 • B 0 + B.repr x 1 • B 1 := by
  conv_lhs => rw [← B.sum_repr x]
  rw [Fin.sum_univ_two]

/-- In a basis of size 3, we represent any element as an explicit sum. -/
theorem Basis.repr_fin_three (B : Basis (Fin 3) K L) (x : L) :
    x = B.repr x 0 • B 0 + B.repr x 1 • B 1 + B.repr x 2 • B 2 := by
  conv_lhs => rw [← B.sum_repr x]
  rw [Fin.sum_univ_three]

--a pair is linear dependent iff one can be written as a multiple of the nonzero other
--the reverse direction does not need y ≠ 0.
lemma not_linearIndependent_pair_iff (x y : L) (hy : y ≠ 0) : ¬LinearIndependent K ![x,y] ↔
    ∃ (c : K), x = c • y := by
  rw [LinearIndependent.pair_iffₛ]
  constructor
  · rw [@Mathlib.Tactic.Push.not_forall_eq]
    intro hli
    obtain ⟨s,hs⟩ := hli
    push Not at hs
    obtain ⟨t,s',t',a,b⟩ := hs
    apply_fun (fun m ↦ - s' • x + m - t • y) at a
    rw [← add_assoc,← add_assoc] at a
    simp only [neg_smul, add_sub_cancel_right, neg_add_cancel, zero_add] at a
    rw [add_comm] at a
    rw [← SubNegMonoid.sub_eq_add_neg] at a
    repeat rw [← sub_smul] at a
    have : ¬ (s=s') := by
      intro ns
      rw [← sub_eq_zero] at ns
      rw [ns] at a
      simp only [zero_smul] at a
      symm at a
      rw [smul_eq_zero] at a
      rcases a with u1 | u2
      · rw [sub_eq_zero] at ns
        rw [sub_eq_zero] at u1
        exact b ns u1.symm
      · contradiction
    rw [← sub_eq_zero] at this
    rw [← Ne.eq_def] at this
    have : x = ( (s-s')⁻¹ •  (t' - t) )• y := by
        calc _ = (s-s')⁻¹ • ( (s-s') • x ) :=by
              rw[← mul_smul,mul_comm,Field.mul_inv_cancel (s - s') this];module
             _ = ((s-s')⁻¹ •  (t' - t) )• y :=by rw [a,smul_assoc];
    use (s-s')⁻¹ •  (t' - t)
  · intro ⟨c,hc⟩
    push Not
    use 1, 0, 0, c
    simp only [one_smul, zero_smul, add_zero, zero_add, one_ne_zero, ne_eq, IsEmpty.forall_iff,
      and_true]
    assumption

/-- A linearly independent set in a submodule is linearly independent in the ambient space. -/
theorem LinearIndependent.iff_in_submodule {S : Type*} (N : Submodule K L) {f : S → N} :
    LinearIndependent K f ↔ LinearIndependent K (Subtype.val ∘ f: S → L) := by
  --LinearMap.linearIndependent_iff_of_injOn f
  rw [← Submodule.coe_subtype]
  symm
  exact LinearMap.linearIndependent_iff (Submodule.subtype N) (Submodule.ker_subtype N)

/-- A function into a submodule `N` defined by specifying a function into the ambient
    space with range in `N`. -/
def Submodule.mapIntoSubtype {S : Type*} (N : Submodule K L) (f : S → L) (hr : Set.range f ⊆ N) :
    S → N := fun x ↦ ⟨f x, hr (Set.mem_range_self x)⟩

/-- A function with range in a given subset gives rise to a function to the corresponding subtype.
-/
def Set.mapIntoSubtype {α β : Type*} (s : Set β) (f : α → β) (hr : Set.range f ⊆ s) :
    α → s := Subtype.coind f fun x => hr ⟨x, rfl⟩

theorem Set.map_into_subtype_apply {α β : Type*} (s : Set β) (f : α →
    β) (hr : Set.range f ⊆ s) (a : α) :
    Set.mapIntoSubtype s f hr a = f a := by
  rfl

/-- A linear independent set which is a subset of a submodule `N` gives a linear independent set in
the module `N`.
-/
theorem Submodule.linearIndependent_from_ambient
    {S : Type*} (N : Submodule K L) (f : S → L) (hs : LinearIndependent K f)
        (hr : Set.range f ⊆ N) :
    LinearIndependent K (Set.mapIntoSubtype N f hr) := by
  rw [linearIndependent_iff'] at *
  intro l hl sum i hi
  apply hs l hl
  · unfold Set.mapIntoSubtype Subtype.coind at sum
    simp only [SetLike.coe_sort_coe, SetLike.mk_smul_mk] at sum
    apply_fun (fun (x :  ↥N) ↦ x.val) at sum
    simp only [AddSubmonoidClass.coe_finsetSum, ZeroMemClass.coe_zero] at sum
    exact sum
  · exact hi

/-- extends linear independent set -/
noncomputable def LinearIndependent.extendFinSuccFun {n : ℕ} {l : Fin n → L}
    (hs : LinearIndependent K l)
    (ht : n + 1 ≤ Module.finrank K L) : Fin (n + 1) → L :=
  Fin.cons (Classical.choose (exists_linearIndependent_cons_of_lt_finrank hs ht)) l

/-- the previous extension gives a linearly independent set adding the new element as 0th element
of the new set -/
theorem LinearIndependent.extendFinSucc {n : ℕ} {l : Fin n → L}
    (hs : LinearIndependent K l)
    (ht : n + 1 ≤ Module.finrank K L) :
    LinearIndependent K (LinearIndependent.extendFinSuccFun hs ht) ∧
      ∀ (i : Fin n), (LinearIndependent.extendFinSuccFun hs ht) (i.succ) = l i := by
    refine ⟨?_, fun i => ?_⟩
    · exact Classical.choose_spec (exists_linearIndependent_cons_of_lt_finrank hs ht)
    · simp [LinearIndependent.extendFinSuccFun, Fin.cons_succ]

/-- extends a l.i. set of n elements to a n+k set, adding the new elements at the beggining -/
theorem LinearIndependent.extend_fin {n k : ℕ} {l : Fin n → L}
    (hs : LinearIndependent K l)
    (ht : n + k ≤ Module.finrank K L) :
    ∃ (b : Fin (n + k) → L), LinearIndependent K b ∧
      ∀ (i : Fin n), b (Fin.addNat i k) = l i := by
    induction k with
    | zero =>
      exact ⟨l,hs,fun i↦rfl⟩
    | succ k ih =>
      have le : n + k ≤ Module.finrank K L := by
        exact Nat.le_of_succ_le ht
      let ⟨b, bI, bH⟩ := ih le
      let ⟨b'I,b'H⟩ := LinearIndependent.extendFinSucc bI ht
      use (LinearIndependent.extendFinSuccFun bI ht)
      constructor
      · assumption
      · intro i
        rw [← bH]
        specialize b'H (i.addNat k)
        assumption

/-- extends a li set of n elements to a basis of n+1 elements (dim space = n+1) -/
noncomputable def Basis.extendFinSucc {n : ℕ} {l : Fin n → L}
    (hs : LinearIndependent K l)
    (ht : Module.finrank K L = n + 1) : Basis (Fin (n + 1)) K L :=
  basisOfLinearIndependentOfCardEqFinrank
    (LinearIndependent.extendFinSucc hs (Nat.le_of_eq ht.symm)).1
    (by rw [← ht]; simp)

/-- The underlying function of `Basis.extendFinSucc` is the extended family. -/
theorem Basis.coe_extend_fin_succ {n : ℕ} {l : Fin n → L}
    (hs : LinearIndependent K l)
    (ht : Module.finrank K L = n + 1) :
    ⇑(Basis.extendFinSucc hs ht) =
      LinearIndependent.extendFinSuccFun hs (Nat.le_of_eq ht.symm) := by
  simp [Basis.extendFinSucc, coe_basisOfLinearIndependentOfCardEqFinrank]

/-- states that Basis.extendFinSucc adds an element at the 0th place -/
theorem Basis.extend_fin_succ_tail_eq {n : ℕ} {l : Fin n → L}
    (hs : LinearIndependent K l)
    (ht : Module.finrank K L = n + 1) :
    Fin.tail ⇑(Basis.extendFinSucc hs ht) = l := by
  rw [Basis.coe_extend_fin_succ]
  funext i
  simp [LinearIndependent.extendFinSuccFun, Fin.tail]

/-- the new zeroth element is not contained in the span of l -/
theorem Basis.extend_fin_succ_head_not_in_span {n : ℕ} {l : Fin n → L}
    (hs : LinearIndependent K l)
    (ht : Module.finrank K L = n + 1) :
    ⇑(Basis.extendFinSucc hs ht) 0 ∉ Submodule.span K (Set.range l) := by
  intro h
  have h₁ : Module.finrank K (Submodule.span K (Set.range l)) = n := by
    rw [finrank_span_eq_card hs, Fintype.card_fin]
  have h₂ : Submodule.span K (Set.range l) = ⊤ := by
    apply le_antisymm
    · apply le_top
    · rw [← Basis.span_eq (Basis.extendFinSucc hs ht)]
      rw [Submodule.span_le]
      rw [Fin.range_fin_succ]
      intro x hx
      rcases hx with h₀ | htail
      · rw [h₀]
        exact h
      · rw [Basis.extend_fin_succ_tail_eq hs ht] at htail
        revert x htail
        rw [← Set.subset_def]
        exact Submodule.subset_span
  rw [h₂, finrank_top] at h₁
  linarith

namespace Basis

--extend to dimension n
lemma exists_unitsSMul (B : Basis (Fin 3) K L) (α β γ : Kˣ) :
      ∃ B' : Basis (Fin 3) K L, B' 0 = α • B 0 ∧
                                B' 1 = β • B 1 ∧
                                B' 2 = γ • B 2 := by
    let B'Basis := Basis.unitsSMul B ![α, β, γ]
    use B'Basis
    dsimp [B'Basis]
    repeat rw [Basis.unitsSMul_apply (v := B) (w := ![α, β, γ])]
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.tail_cons, and_self]

end Basis

variable {K L₁ L₂ : Type*} [CommRing K] [AddCommGroup L₁] [AddCommGroup L₂]
  [Module K L₁] [Module K L₂] (e : L₁ ≃ₗ[K] L₂)

theorem LinearEquiv.conj_symm : e.conj.symm = e.symm.conj := rfl

variable {K L : Type*} [Field K] [AddCommGroup L] [Module K L]

--might generalize to infinite dimension
theorem Submodule.compl_span_singleton_of_codim_one
      (p : Submodule K L) (h : Module.finrank K L = Module.finrank K p + 1) :
    ∃ x : L, IsCompl p (Submodule.span K {x}) := by
  have : FiniteDimensional K L := Module.finite_of_finrank_eq_succ h
  have : Module.finrank K p < Module.finrank K L := by
    apply Nat.lt_of_succ_le
    rw [h]
  obtain ⟨x, hx⟩ := Submodule.exists_of_finrank_lt p this
  use x
  specialize hx 1 one_ne_zero
  rw [one_smul] at hx
  have disj : Disjoint p (Submodule.span K {x}) := by
    rw [Submodule.disjoint_span_singleton']
    · exact hx
    · intro h
      rw [h] at hx
      exact hx (zero_mem _)
  constructor
  · exact disj
  · rw [codisjoint_iff]
    apply Submodule.eq_top_of_disjoint
    · rw [h, finrank_span_singleton]
      intro h
      rw [h] at hx
      exact hx (zero_mem _)
    · exact disj

variable {K L : Type*} [CommRing K] [AddCommGroup L] [Module K L] (p q : Submodule K L)

/-- The linear map from `M₁ × M₂` to `L` defined by specifying maps from `M₁` and `M₂` to `L`. -/
def LinearMap.ofProd {M₁ M₂ : Type*} [AddCommGroup M₁] [AddCommGroup M₂] [Module K M₁] [Module K M₂]
      (f : M₁ →ₗ[K] L) (g : M₂ →ₗ[K] L) :
    M₁ × M₂ →ₗ[K] L :=
  f ∘ₗLinearMap.fst K M₁ M₂ + g ∘ₗLinearMap.snd K M₁ M₂

@[simp]
theorem LinearMap.ofProd_apply {M₁ M₂ : Type*} [AddCommGroup M₁] [AddCommGroup M₂] [Module K M₁]
    [Module K M₂]
      (f : M₁ →ₗ[K] L) (g : M₂ →ₗ[K] L) (x : M₁ × M₂) :
    LinearMap.ofProd f g x = f x.1 + g x.2 := rfl

variable {K L : Type*} [CommRing K] [AddCommGroup L] [Module K L] {p q : Submodule K L}

/-- If two submodules are disjoint, then the canonical map from the product is injective. -/
theorem Submodule.prod_injective_of_disjoint (h : Disjoint p q) :
    Function.Injective (LinearMap.ofProd p.subtype q.subtype) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  simp only [LinearMap.mem_ker, LinearMap.ofProd_apply, subtype_apply] at hx
  rw [add_eq_zero_iff_neg_eq'] at hx
  have x₁p : x.1.val ∈ p := x.1.prop
  have x₁q : x.1.val ∈ q := by
    rw [← hx, Submodule.neg_mem_iff]
    exact x.2.prop
  have x₁0 := Submodule.disjoint_def.mp h _ x₁p x₁q
  have x₂p : x.2.val ∈ p := by
    rw [← Submodule.neg_mem_iff, hx]
    exact x.1.prop
  have x₂q : x.2.val ∈ q := x.2.prop
  have x₂0 := Submodule.disjoint_def.mp h _ x₂p x₂q
  ext
  · rw [x₁0]
    rfl
  · rw [x₂0]
    rfl

/-- If two submodules are codisjoint, then the canonical map from the product is surjectve. -/
theorem Submodule.prod_surjective_of_codisjoint (h : Codisjoint p q) :
    Function.Surjective (LinearMap.ofProd p.subtype q.subtype) := by
  intro x
  obtain ⟨y, z, hy, hz, hx⟩ := Submodule.codisjoint_iff_exists_add_eq.mp h x
  exact ⟨⟨⟨y, hy⟩, ⟨z, hz⟩⟩, hx⟩

/-- If two submodules are complementary, then their product is isomorphic to the ambient space. -/
noncomputable def LinearEquiv.ofComplSubmodules (h : IsCompl p q) :
    (p × q) ≃ₗ[K] L :=
  LinearEquiv.ofBijective (LinearMap.ofProd p.subtype q.subtype)
    ⟨Submodule.prod_injective_of_disjoint h.disjoint,
      Submodule.prod_surjective_of_codisjoint h.codisjoint⟩

@[simp]
theorem LinearEquiv.ofComplSubmodules_apply (h : IsCompl p q) (x : p × q) :
    (LinearEquiv.ofComplSubmodules h) x = x.1.val + x.2.val := rfl

theorem LinearEquiv.ofComplSubmodules_symm_apply (h : IsCompl p q)
      (x y z : L) (hy : y ∈ p) (hz : z ∈ q) (hx : x = y + z) :
    (LinearEquiv.ofComplSubmodules h).symm x = ⟨⟨y, hy⟩, ⟨z, hz⟩⟩ := by
  simp only [symm_apply_eq, LinearEquiv.ofComplSubmodules_apply h, hx]

theorem LinearEquiv.ofComplSubmodules_symm_apply_left (h : IsCompl p q) (x : L) (hx : x ∈ p) :
    (LinearEquiv.ofComplSubmodules h).symm x = ⟨⟨x, hx⟩, 0⟩ := by
  apply LinearEquiv.ofComplSubmodules_symm_apply
  rw [add_zero]

theorem LinearEquiv.ofComplSubmodules_symm_apply_right (h : IsCompl p q) (x : L) (hx : x ∈ q) :
    (LinearEquiv.ofComplSubmodules h).symm x = ⟨0, ⟨x, hx⟩⟩ := by
  apply LinearEquiv.ofComplSubmodules_symm_apply
  rw [zero_add]

theorem LinearEquiv.ofComplSubmodules_symm_add (h : IsCompl p q) (x : L) :
    x = ((LinearEquiv.ofComplSubmodules h).symm x).1.val +
      ((LinearEquiv.ofComplSubmodules h).symm x).2.val := by
  obtain ⟨y, z, hy, hz, hx⟩ := Submodule.codisjoint_iff_exists_add_eq.mp h.codisjoint x
  simp only [LinearEquiv.ofComplSubmodules_symm_apply h x y z hy hz hx.symm]
  exact hx.symm

variable (K L : Type*) [Field K] [AddCommGroup L] [Module K L]

/-- The natural map from the base field to scalar multiples of `x` is an isomorphism if `x ≠ 0`. -/
noncomputable def LinearEquiv.toSpanSingleton {x : L} (h : x ≠ 0) :
    K ≃ₗ[K] Submodule.span K {x} := by
  have f'inj : Function.Injective (LinearMap.toSpanSingleton K L x) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_toSpanSingleton K h]
  have f'range := LinearMap.span_singleton_eq_range K L x
  let f := LinearEquiv.ofInjective (LinearMap.toSpanSingleton K L x) f'inj
  rw [← f'range] at f
  exact f

@[simp]
theorem LinearEquiv.toSpanSingleton_apply {x : L} (h : x ≠ 0) (a : K) :
    LinearEquiv.toSpanSingleton K L h a = ⟨a • x, mem_span_singleton.mpr ⟨a, rfl⟩⟩ := by
  unfold toSpanSingleton
  ext
  simp only [eq_mp_eq_cast]
  have inj : Function.Injective (LinearMap.toSpanSingleton K L x) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_toSpanSingleton K h]
  have range := LinearMap.span_singleton_eq_range K L x
  rw [← LinearMap.toSpanSingleton_apply, ← LinearEquiv.ofInjective_apply (h := inj)]
  congr 2
  · rw [range]
  · rw [range]
  · rw [range]
  · rw [range]
  · apply cast_heq

@[simp]
theorem LinearEquiv.toSpanSingleton_symm_apply {x : L} (h : x ≠ 0) (a : K) :
    (LinearEquiv.toSpanSingleton K L h).symm ⟨a • x, mem_span_singleton.mpr ⟨a, rfl⟩⟩ = a := by
  rw [LinearEquiv.symm_apply_eq, LinearEquiv.toSpanSingleton_apply]

theorem LinearEquiv.toSpanSingleton_symm_apply' {x : L} (h : x ≠ 0) (y : Submodule.span K {x}) :
    ((LinearEquiv.toSpanSingleton K L h).symm y) • x = y := by
  obtain ⟨a, hy⟩ := Submodule.mem_span_singleton.mp y.2
  have : y = ⟨a • x, mem_span_singleton.mpr ⟨a, rfl⟩⟩ := by
    ext
    rw [← hy]
  rw [this, LinearEquiv.toSpanSingleton_symm_apply K L h]

end linalg

section liealg
open Module
open Submodule

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]

namespace LieAlgebra

lemma coeff_zero_of_lin_dep {X Y : L} {α β : K} (hXY : ⁅X, Y⁆ ≠ 0)
    (Hzero : α • X + β • Y = 0) : α = 0 := by
  have : α • ⁅X, Y⁆ = 0 :=
    calc α • ⁅X, Y⁆ = ⁅α • X + β • Y, Y⁆ := by
          simp
    _ = 0 := by
          simp [Hzero]
  simp_all only [smul_eq_zero, or_false]

/-- If `⁅X, Y⁆ ≠ 0`, then `X` and `Y` are linearly independent. -/
lemma linearIndependent_of_bracket_ne_zero
    (X Y : L) (hXY : ⁅X, Y⁆ ≠ 0) :
    LinearIndependent K ![X, Y] := by
  apply LinearIndependent.pair_iff.mpr
  intros α β Hzero
  constructor
  · exact coeff_zero_of_lin_dep hXY Hzero
  · rw [add_comm] at Hzero
    rw [← lie_skew, neg_ne_zero] at hXY
    exact coeff_zero_of_lin_dep hXY Hzero

/-- If `⁅X, Y⁆ ≠ 0` in a two-dimensional Lie algebra, then `X` and `Y` form a basis. -/
lemma basis_of_bracket_ne_zero (h : finrank K L = 2) (X Y : L) (hXY : ⁅X, Y⁆ ≠ 0) :
    ∃ B : Basis (Fin 2) K L, (B 0 = X ∧ B 1 = Y) := by
  have B_li : LinearIndependent K ![X, Y] := linearIndependent_of_bracket_ne_zero X Y hXY
  exists basisOfLinearIndependentOfCardEqFinrank B_li (by simp [h])
  simp

variable {K L : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]

/-- The k+1-th term of the derived series is spanned as submodule by Lie brackets of
    elements in the k-th term. -/
theorem derivedSeries_succ_is_span {k : ℕ} : (LieAlgebra.derivedSeries K L (k + 1)).toSubmodule =
    span K {x : L | ∃ (y : ↥(LieAlgebra.derivedSeries K L k))
        (z : ↥(LieAlgebra.derivedSeries K L k)), ⁅y, z⁆ = x} := by
  simp only [LieAlgebra.derivedSeriesOfIdeal_succ]
  rw [LieSubmodule.lieIdeal_oper_eq_span]
  apply le_antisymm
  · intro x hx
    induction hx using LieSubmodule.lieSpan_induction with
    | mem x hx => exact subset_span hx
    | zero => simp
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul a x _ hx => exact smul_mem _ a hx
    | lie x y _ hy =>
      refine span_induction ?mem ?zero ?add ?smul hy
      · intro z ⟨a, b, hz⟩
        simp only [LieIdeal.coe_bracket_of_module, LieSubmodule.coe_bracket,
          ] at hz
        rw [← hz, leibniz_lie]
        apply add_mem
        · apply subset_span
          use ⁅x, ↑a⁆, ↑b
          simp
        · apply subset_span
          use ↑a, ⁅x, ↑b⁆
          simp
      · simp
      · intro a_ b_ ha_ hb_ ha hb
        rw [lie_add]
        exact add_mem ha hb
      · intro k a_ ha_ ha
        rw [lie_smul]
        exact smul_mem _ k ha
  · apply LieSubmodule.submodule_span_le_lieSpan

/-- The commutator ideal of a Lie algebra. -/
abbrev commutator (K L : Type*) [CommRing K] [LieRing L] [LieAlgebra K L] : LieIdeal K L :=
  LieAlgebra.derivedSeries K L 1

/-- The commutator ideal is linearly spanned by Lie brackets. -/
theorem commutator_eq_span :
    (LieAlgebra.commutator K L).toSubmodule =
      span K {x : L | ∃ (y : L) (z : L), ⁅y, z⁆ = x} := by
  rw [LieAlgebra.derivedSeries_succ_is_span (k := 0) (K := K) (L := L)]
  congr 1
  ext x
  simp only [Set.mem_setOf_eq, LieIdeal.coe_bracket_of_module, Subtype.exists]
  exact ⟨fun ⟨a, _, b, _, h⟩ => ⟨a, b, h⟩, fun ⟨a, b, h⟩ => ⟨a, trivial, b, trivial, h⟩⟩

/-- Lie brackets are contained in the commutator ideal. -/
theorem lie_mem_commutator : ∀ (x y : L), ⁅x, y⁆ ∈ LieAlgebra.commutator K L := by
  intro x y
  exact LieSubmodule.lie_mem_lie trivial trivial

/-- If the commutator of a Lie algebra is solvable, then the Lie algebra is solvable. -/
theorem solvable_of_commutator_solvable
    (comm : LieAlgebra.IsSolvable (LieAlgebra.commutator K L)) :
    LieAlgebra.IsSolvable L := by
  rw [LieAlgebra.isSolvable_iff (R := K)] at comm
  obtain ⟨ m, pm ⟩ := comm
  rw [LieAlgebra.isSolvable_iff (R := K)]
  use m + 1
  rw [LieAlgebra.derivedSeries_def,LieAlgebra.derivedSeriesOfIdeal_add,
    ← LieAlgebra.derivedSeries_def]
  exact (LieIdeal.derivedSeries_eq_bot_iff (LieAlgebra.commutator K L) m).mp pm

end LieAlgebra

variable {K L : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]

theorem LieSubalgebra.mem_lieSpan_singleton {y x : L} : (x ∈ LieSubalgebra.lieSpan K L {y}) ↔
    ∃ a : K, a • y = x := by
  constructor
  · intro h
    induction h using LieSubalgebra.lieSpan_induction with
    | mem => exact ⟨1, by simp_all only [one_smul, Set.mem_singleton_iff]⟩
    | zero => exact ⟨0, by simp only [zero_smul]⟩
    | add x y _ _ hx hy =>
        obtain ⟨a, rfl⟩ := hx
        obtain ⟨b, rfl⟩ := hy
        exact ⟨a + b, by rw [add_smul]⟩
    | smul t x _ hx =>
        obtain ⟨m, rfl⟩ := hx
        exact ⟨t * m, by rw [smul_smul]⟩
    | lie x y _ _ hx hy =>
        obtain ⟨a, rfl⟩ := hx
        obtain ⟨b, rfl⟩ := hy
        exact ⟨0, by simp only [zero_smul, lie_smul, smul_lie, lie_self, smul_zero]⟩
  · rintro ⟨a, y, rfl⟩
    have H : a • y ∈ span K {y} := by
      apply Submodule.mem_span_singleton.mpr
      exact ⟨a, rfl⟩
    exact LieSubalgebra.submodule_span_le_lieSpan H

/-- The Lie subalgebra generated by a single element equals the linear subspace spanned by it. -/
theorem LieSubalgebra.lieSpan_singleton {x : L} : (LieSubalgebra.lieSpan K L
    {x}).toSubmodule = Submodule.span K {x} := by
  ext _
  rw [LieSubalgebra.mem_toSubmodule, LieSubalgebra.mem_lieSpan_singleton,
    Submodule.mem_span_singleton]

theorem LieSubmodule.mem_lieSpan_singleton {y x : L} (H : ∀ (z : L), ∃ (a : K), ⁅z, y⁆ = a • y) :
    (x ∈ LieSubmodule.lieSpan K L {y}) ↔ ∃ a : K, a • y = x := by
  constructor
  · intro h
    induction h using LieSubmodule.lieSpan_induction with
    | mem => exact ⟨1, by simp_all only [one_smul, Set.mem_singleton_iff]⟩
    | zero => exact ⟨0, by simp only [zero_smul]⟩
    | add u v _ _ hu hv =>
        obtain ⟨a, rfl⟩ := hu
        obtain ⟨b, rfl⟩ := hv
        exact ⟨a + b, by rw [add_smul]⟩
    | smul a u _ hu =>
        obtain ⟨m, rfl⟩ := hu
        exact ⟨a * m, by rw [smul_smul]⟩
    | lie u v _ hv =>
        obtain ⟨b, rfl⟩ := hv
        obtain ⟨a, H⟩ := H u
        use (b • a)
        simp [H, smul_smul]
  · rintro ⟨a, y, rfl⟩
    have H : a • y ∈ span K {y} := by
      apply Submodule.mem_span_singleton.mpr
      exact ⟨a, rfl⟩
    exact LieSubmodule.submodule_span_le_lieSpan H

/-- The Lie submodule generated by a single element `x` equals the linear subspace
    spanned by it if `⁅z, x⁆` is a multiple of `x` for all `z`. -/
theorem LieSubmodule.lieSpan_singleton {x : L} (H : ∀ (z : L), ∃ (a : K), ⁅z,
  x⁆ = a • x) : (LieSubmodule.lieSpan K L {x}).toSubmodule = Submodule.span K {x} := by
  ext _
  rw [LieSubmodule.mem_toSubmodule, LieSubmodule.mem_lieSpan_singleton H,
    Submodule.mem_span_singleton]

theorem LieIdeal.finrank_toSubmodule {I : LieIdeal K L} :
  Module.finrank K I = Module.finrank K I.toSubmodule := by
  rfl

lemma binary_predicate_3_choose_2 {P : Fin 3 → Fin 3 → Prop} (h₀₁ : P 0 1) (h₀₂ : P 0 2)
    (h₁₂ : P 1 2) :
    ∀ i j : Fin 3, i < j → P i j := by
  intros i j
  fin_cases i, j <;> intro ij <;> dsimp! at ij <;> try omega
  assumption'

-- `LieRing.ofAssociativeRing` is a local instance in Mathlib (a `def`, not a global instance), so
-- we re-enable it locally to view the commutative ring `K` as a Lie ring over itself.
attribute [local instance 100] LieRing.ofAssociativeRing

/-- `LinearMap.smulRight` as a Lie algebra homomorphism. -/
def LieHom.smulRight (f : End K L) : K →ₗ⁅K⁆ End K L := {
  LinearMap.smulRight (LinearMap.id : K →ₗ[K] K) f with
  map_lie' := by
    intro x y
    change (lieRingSelfModule.toBracket.1 x y : K) • f = ⁅x • f, y • f⁆
    rw [show (lieRingSelfModule.toBracket.1 x y : K) = x * y - y * x from rfl,
      show (⁅x • f, y • f⁆ : End K L) = (x • f) * (y • f) - (y • f) * (x • f) from rfl,
      smul_mul_smul_comm, smul_mul_smul_comm, mul_comm x y, sub_self, zero_smul, sub_self]
}

@[simp]
theorem LieHom.coe_smulRight (f : End K L) : ⇑(LieHom.smulRight f) = fun (a : K) => a • f := rfl

theorem LieHom.smulRight_apply (f : End K L) (a : K) : (LieHom.smulRight f) a = a • f := rfl

namespace LieAlgebra

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]

/-- If the Lie algebra `L` of dimension `n + 1` is solvable, then its commutator ideal has
dimension at most `n`.
-/
theorem codim_commutator_ge_one_of_solvable {n : ℕ} (dimn : Module.finrank K L = n + 1)
    (issolvable : LieAlgebra.IsSolvable L) :
    Module.finrank K (LieAlgebra.commutator K L) ≤ n := by
  have : Nontrivial L := Module.nontrivial_of_finrank_eq_succ dimn
  have s : LieAlgebra.commutator K L < ⊤ := by
   apply LieAlgebra.derivedSeries_lt_top_of_solvable K L
  have FD : FiniteDimensional K (⊤ : LieIdeal K L) :=by
   apply Module.finite_of_finrank_eq_succ (n:= n)
   rw [← finrank_top K L] at dimn
   assumption
  have t : Module.finrank K (LieAlgebra.commutator K L) < Module.finrank K (⊤ : Submodule K L) := by
   apply Submodule.finrank_lt_finrank_of_lt
   assumption
  rw [← finrank_top K L] at dimn
  rw [dimn] at t
  exact Nat.le_of_lt_succ t

/-- A finite-dimensional Lie algebra has commutator dimension at most one if for a basis,
  all Lie brackets are multiples of the same element. -/
theorem finrank_commutator_le_one_of_lie_basis {n : ℕ} (B : Basis (Fin n) K L) (X : L)
      (h : ∀ i j : Fin n, i < j → ∃ α : K, ⁅B i, B j⁆ = α • X) :
    Module.finrank K (LieAlgebra.commutator K L) ≤ 1 := by
  have h' : ∀ i j : Fin n, ∃ α : K, ⁅B i, B j⁆ = α • X := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
      use 0
      rw [lie_self, zero_smul]
    · rcases Fin.lt_or_lt_of_ne hij with hij | hij
      · exact h i j hij
      · obtain ⟨α, hα⟩ := h j i hij
        use -α
        rw [← lie_skew, hα, neg_smul]
  choose α h' using h'
  have h'' : (LieAlgebra.commutator K L).toSubmodule ≤ span K {X} := by
    rw [LieAlgebra.commutator_eq_span, span_le]
    intro x ⟨y, z, hxyz⟩
    rw [SetLike.mem_coe, mem_span_singleton, ← hxyz, ← B.sum_repr y, ← B.sum_repr z, sum_lie_sum]
    simp_rw [lie_smul, smul_lie, h', ← mul_smul]
    use ∑ i : Fin n, ∑ j : Fin n, ((B.repr z) j * ((B.repr y) i * α i j))
    simp_rw [Finset.sum_smul]
  by_cases hX: X = 0
  · rw [hX, span_zero_singleton, ← eq_bot_iff, LieSubmodule.toSubmodule_eq_bot] at h''
    rw [h'']
    refine le_trans ?_ (Nat.zero_le 1)
    rw [le_zero_iff]
    apply finrank_bot
  · apply Submodule.finrank_mono at h''
    rw [finrank_span_singleton hX] at h''
    assumption

variable (K L : Type*) [CommRing K] [LieRing L] [LieAlgebra K L]

/-- We define a Lie algebra to be two-step nilpotent if its commutator ideal is contained in the
center.
-/
def IsTwoStepNilpotent : Prop := commutator K L ≤ center K L

theorem isTwoStepNilpotent_iff : IsTwoStepNilpotent K L ↔ commutator K L ≤ center K L := by rfl

/-- A Lie algebra is two-step nilpotent iff its lower central series terminates after two steps. -/
theorem isTwoStepNilpotent_iff_lowerCentral :
    IsTwoStepNilpotent K L ↔ LieModule.lowerCentralSeries K L L 2 = ⊥ := by
  rw [isTwoStepNilpotent_iff]
  constructor
  · intro h
    simp only [LieModule.lowerCentralSeries_succ, LieModule.lowerCentralSeries_zero]
    rw [LieSubmodule.lie_eq_bot_iff]
    intro x _ y hy
    apply h at hy
    rw [LieModule.mem_maxTrivSubmodule] at hy
    exact hy x
  · intro h y hy
    simp only [LieModule.lowerCentralSeries_succ, LieModule.lowerCentralSeries_zero] at h
    rw [LieSubmodule.lie_eq_bot_iff] at h
    rw [LieModule.mem_maxTrivSubmodule]
    intro x
    exact h x (LieSubmodule.mem_top (R := K) (L := L) (M := L) x) y hy

/-- A Lie algebra is two-step nilpotent iff its lower central series terminates after two steps. -/
theorem isTwoStepNilpotent_iff_lowerCentral' :
    IsTwoStepNilpotent K L ↔ LieModule.lowerCentralSeries ℤ L L 2 = ⊥ := by
  rw [isTwoStepNilpotent_iff_lowerCentral]
  rw [← LieSubmodule.coe_injective.eq_iff]
  rw [LieModule.coe_lowerCentralSeries_eq_int K L L 2]
  rw [LieSubmodule.bot_coe, ← LieSubmodule.bot_coe (R := ℤ) (L := L)]
  rw [LieSubmodule.coe_injective.eq_iff]

--here L is necesarily finite dimensional (if K is a field). Could generalize this to
--infinite dimensions.
/-- A Lie algebra is almost abelian if it has a codimension one abelian ideal. -/
def IsAlmostAbelian : Prop :=
    ∃ I : LieIdeal K L, IsLieAbelian I ∧ Module.finrank K L = Module.finrank K I + 1

theorem isAlmostAbelian_iff :
    IsAlmostAbelian K L ↔ ∃ I : LieIdeal K L, IsLieAbelian I ∧
        Module.finrank K L = Module.finrank K I + 1 := by rfl

end LieAlgebra

variable (K L : Type*) [CommRing K] [LieRing L] [LieAlgebra K L]

@[simp]
theorem LieIdeal.rank_top : Module.rank K (⊤ : LieIdeal K L) = Module.rank K L :=
  LinearEquiv.rank_eq (LinearEquiv.ofTop ⊤ rfl)

@[simp]
theorem LieIdeal.finrank_top : Module.finrank K (⊤ : LieIdeal K L) = Module.finrank K L := by
  unfold finrank
  rw [LieIdeal.rank_top]

end liealg

section LieDerivations

variable {K L : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]

/-- A derivation of a Lie algebra maps the commutator into the commutator. -/
theorem LieDerivation.map_commutator (D : LieDerivation K L L) :
    Submodule.map D.toLinearMap (LieAlgebra.commutator K L).toSubmodule ≤
      (LieAlgebra.commutator K L).toSubmodule := by
  intro Dz
  simp only [Submodule.mem_map, LieSubmodule.mem_toSubmodule,
    forall_exists_index, and_imp]
  intro z hz hDz
  rw [← hDz]
  rw [← LieSubmodule.mem_toSubmodule, LieAlgebra.commutator_eq_span] at *
  refine Submodule.span_induction ?mem ?zero ?add ?smul hz
  · intro z ⟨x, y, hz⟩
    rw [← hz]
    change D ⁅x, y⁆ ∈ _
    rw [LieDerivation.apply_lie_eq_add]
    apply Submodule.add_mem
    · apply Submodule.subset_span
      exact ⟨x, D y, rfl⟩
    · apply Submodule.subset_span
      exact ⟨D x, y, rfl⟩
  · simp only [map_zero, Submodule.zero_mem]
  · intro x y _ _ hDx hDy
    rw [map_add]
    apply Submodule.add_mem
    repeat assumption
  · intro a x _ hDx
    rw [map_smul]
    apply Submodule.smul_mem
    assumption

/-- The adjoint action of a Lie algebra on itself maps everything into the commutator. -/
theorem LieAlgebra.ad_into_commutator' (x : L) :
    Submodule.map (LieDerivation.ad K L x).toLinearMap ⊤ ≤
      (LieAlgebra.commutator K L).toSubmodule := by
  intro y hy
  obtain ⟨z, _, rfl⟩ := hy
  change LieDerivation.ad K L x z ∈ _
  rw [LieDerivation.ad_apply_apply]
  simp only [derivedSeriesOfIdeal_succ, derivedSeriesOfIdeal_zero, LieSubmodule.mem_toSubmodule]
  apply LieSubmodule.subset_lieSpan
  simp only [Subtype.exists, LieSubmodule.mem_top, exists_const, Set.mem_setOf_eq,
    exists_apply_eq_apply2]

/-- The adjoint action of a Lie algebra on itself maps everything into the commutator. -/
theorem LieAlgebra.ad_into_commutator (x : L) :
    Submodule.map (LieAlgebra.ad K L x) ⊤ ≤ (LieAlgebra.commutator K L).toSubmodule := by
  intro y hy
  apply LieAlgebra.ad_into_commutator' x
  obtain ⟨z, _, hzy⟩ := hy
  refine ⟨z, trivial, ?_⟩
  change (LieDerivation.ad K L x) z = y
  rw [show ((LieDerivation.ad K L) x : L → L) z = (LieAlgebra.ad K L) x z by
        simp []]
  exact hzy

end LieDerivations

section LieAbelian

open Module

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]

/-- A finite-dimensional Lie algebra is abelian if and only if its commutator ideal has dimension
zero.
-/
theorem LieAlgebra.abelian_iff_dim_comm_zero [FiniteDimensional K L] :
    Module.finrank K (LieAlgebra.commutator K L) = 0 ↔ IsLieAbelian L := by
  constructor
  · intro h₀
    simp only [LieIdeal.finrank_toSubmodule, Submodule.finrank_eq_zero,
      LieSubmodule.toSubmodule_eq_bot] at h₀
    apply (LieAlgebra.abelian_iff_derived_one_eq_bot (⊤ : LieIdeal K L)).mpr at h₀
    refine { trivial := ?trivial }
    intro x y
    have := h₀.trivial ⟨x, trivial⟩ ⟨y, trivial⟩
    simp only [LieIdeal.coe_bracket_of_module] at this
    exact (LieSubmodule.mk_eq_zero _ _).mp this
  · intro abelian
    have : LieAlgebra.commutator K L = ⊥ := by
      simp only [LieAlgebra.derivedSeriesOfIdeal_succ, LieAlgebra.derivedSeriesOfIdeal_zero,
        LieSubmodule.trivial_lie_oper_zero]
    rw [this]
    exact finrank_bot K L

/-- A finite-dimensional Lie algebra is abelian if and only if for any basis,
  all Lie brackets vanish. -/
theorem LieAlgebra.abelian_iff_lie_basis_eq_zero {n : ℕ} (B : Basis (Fin n) K L) :
    IsLieAbelian L ↔ ∀ i j : Fin n, (i < j → ⁅B i, B j⁆ = 0) := by
  constructor
  · intro ⟨h⟩ _ _ _
    apply h
  · intro h
    have h' : ∀ i j : Fin n, ⁅B i, B j⁆ = 0 := by
      intro i j
      by_cases hij : i = j
      · rw [hij, lie_self]
      · rcases Fin.lt_or_lt_of_ne hij with hij | hij
        · exact h i j hij
        · rw [← lie_skew, h j i hij, neg_zero]
    constructor
    intro x y
    rw [← B.sum_repr x, ← B.sum_repr y, sum_lie_sum]
    simp_rw [lie_smul, smul_lie, h', smul_zero, Finset.sum_const_zero]

end LieAbelian

section lieequiv

variable {K L L' : Type*} [CommRing K] [LieRing L] [LieRing L'] [LieAlgebra K L] [LieAlgebra K L']

theorem LieEquiv.symm_toLinearEquiv (e : L ≃ₗ⁅K⁆ L') : e.symm.toLinearEquiv = e.toLinearEquiv.symm
    := rfl

/-- If `f` is a surjective homomorphism of Lie algebras, then `LieIdeal.map f I` is the image of
`I` under `f`
    (equality of submodules). -/
theorem LieIdeal.map_eq_image_of_surj {f : L →ₗ⁅K⁆ L'} (h : Function.Surjective f)
    (I : LieIdeal K L) :
    (LieIdeal.map f I).toSubmodule = Submodule.map f.toLinearMap I := by
  apply LieIdeal.map_toSubmodule
  ext x
  constructor
  · intro hx
    rcases LieIdeal.mem_map_of_surjective h hx with ⟨y, _⟩
    use y.1, y.2
  · intro hx
    rcases hx with ⟨y, hy, hxy⟩
    rw [← hxy]
    exact LieIdeal.mem_map hy

/-- If `f` is a surjective homomorphism of Lie algebras, then `LieIdeal.map f I` is the image of
`I` under `f`
    (equality of Lie subalgebras). -/
theorem LieIdeal.map_eq_image_of_surj' {f : L →ₗ⁅K⁆ L'} (h : Function.Surjective f)
    (I : LieIdeal K L) :
    (LieIdeal.map f I).toLieSubalgebra = LieSubalgebra.map f I := by
  unfold LieSubalgebra.map
  rw [← LieSubalgebra.toSubmodule_inj, toLieSubalgebra_toSubmodule,
    LieIdeal.map_eq_image_of_surj h I]

/-- If `f` is a surjective homomorphism of Lie algebras, then `LieIdeal.map f I` is the image of
`I` under `f`
    (equality of sets). -/
theorem LieIdeal.map_eq_image_of_surj'' {f : L →ₗ⁅K⁆ L'} (h : Function.Surjective f)
    (I : LieIdeal K L) :
    LieIdeal.map f I = f '' I := by
  rw [← coe_toLieSubalgebra, map_eq_image_of_surj' h I]
  rfl

theorem LieIdeal.map_comap_eq_of_surjective {f : L →ₗ⁅K⁆ L'} (h : Function.Surjective f)
    (I : LieIdeal K L') :
    LieIdeal.map f (LieIdeal.comap f I) = I := by
  rw [LieIdeal.map_comap_eq (LieHom.isIdealMorphism_of_surjective f h),
    LieHom.idealRange_eq_top_of_surjective f h, inf_of_le_right]
  exact le_top

/-- An equivalence of Lie algebras restricts to an equivalence from any ideal onto its image. -/
def LieEquiv.ofIdeals (e : L ≃ₗ⁅K⁆ L') (I : LieIdeal K L) (I' : LieIdeal K L')
   (h : LieIdeal.map e.toLieHom I = I') : I ≃ₗ⁅K⁆ I' := by
  apply LieEquiv.ofSubalgebras I I' e
  rw [← LieIdeal.map_eq_image_of_surj' (LieEquiv.surjective e) I, h]

/-- Under an equivalence of Lie algebras, the commutator is mapped to the commutator. -/
theorem LieEquiv.commutator_map (e : L ≃ₗ⁅K⁆ L') : LieIdeal.map e
    (LieAlgebra.commutator K L) = LieAlgebra.commutator K L' := by
  unfold LieAlgebra.commutator
  exact LieIdeal.derivedSeries_map_eq 1 (LieEquiv.surjective e)

/-- An equivalence of Lie algebras induces an equivalence of commutator subalgebras. -/
def LieEquiv.commutatorEquiv
    (e : L ≃ₗ⁅K⁆ L') : LieAlgebra.commutator K L ≃ₗ⁅K⁆ LieAlgebra.commutator K L' := by
  apply LieEquiv.ofIdeals e (LieAlgebra.commutator K L) (LieAlgebra.commutator K L')
  exact LieEquiv.commutator_map e

theorem LieEquiv.commutator_equiv_apply (e : L ≃ₗ⁅K⁆ L') (x : L)
    (hx : x ∈ LieAlgebra.commutator K L) :
    LieEquiv.commutatorEquiv e ⟨x, hx⟩ = ⟨e x, LieEquiv.commutator_map e ▸ LieIdeal.mem_map hx ⟩ :=
  rfl

theorem LieEquiv.commutator_equiv_symm (e : L ≃ₗ⁅K⁆ L') :
    e.commutatorEquiv.symm = e.symm.commutatorEquiv :=
  rfl

theorem LieAlgebra.dim_commutator_eq_of_lieEquiv (e : L ≃ₗ⁅K⁆ L') :
    Module.finrank K (LieAlgebra.commutator K L) = Module.finrank K (LieAlgebra.commutator K L') :=
  LinearEquiv.finrank_eq (LieEquiv.commutatorEquiv e).toLinearEquiv

/-- Under an equivalence of Lie algebras, the center is mapped to the center. -/
theorem LieEquiv.center_map (e : L ≃ₗ⁅K⁆ L') : LieIdeal.map e
    (LieAlgebra.center K L) = LieAlgebra.center K L' := by
  rw [← LieSubmodule.toSubmodule_inj, LieIdeal.map_eq_image_of_surj (LieEquiv.surjective e)]
  ext x
  simp only [LieIdeal.toLieSubalgebra_toSubmodule, Submodule.mem_map, LieSubmodule.mem_toSubmodule,
    LieModule.mem_maxTrivSubmodule, LieHom.coe_toLinearMap]
  constructor
  · intro ⟨y, hy, hxy⟩
    rw [← hxy]
    intro z
    obtain ⟨u, huz⟩ := LieEquiv.surjective e z
    rw [← huz, ← (e.toLieHom).map_lie, hy u, map_zero]
  · intro hx
    obtain ⟨y, hxy⟩ := LieEquiv.surjective e x
    use y
    symm
    use hxy
    intro u
    apply (injective_iff_map_eq_zero e.toLinearEquiv).mp (LieEquiv.injective e)
    rw [LieEquiv.coe_toLinearEquiv, ← LieEquiv.coe_toLieHom, (e.toLieHom).map_lie, hxy]
    apply hx

theorem LieIdeal.comap_map_eq_of_equiv (e : L ≃ₗ⁅K⁆ L') (I : LieIdeal K L) :
    LieIdeal.comap e.toLieHom (LieIdeal.map e.toLieHom I) = I := by
  rw [LieIdeal.comap_map_eq (LieIdeal.map_eq_image_of_surj'' (LieEquiv.surjective e) _),
    (LieHom.ker_eq_bot e.toLieHom).mpr (LieEquiv.injective e), sup_of_le_left]
  exact bot_le

/-- Under an equivalence of Lie algebras, two-step nilpotency is preserved. -/
theorem LieEquiv.preserves_isTwoStepNilpotent (e : L ≃ₗ⁅K⁆ L') :
    LieAlgebra.IsTwoStepNilpotent K L ↔ LieAlgebra.IsTwoStepNilpotent K L' := by
  repeat rw [LieAlgebra.isTwoStepNilpotent_iff]
  rw [← LieEquiv.commutator_map e, ← LieEquiv.center_map e]
  constructor
  · intro h
    exact LieIdeal.map_mono h
  · intro h
    rw [LieIdeal.map_le_iff_le_comap, LieIdeal.comap_map_eq_of_equiv] at h
    assumption

end lieequiv

section dim1linalg

open Module

variable {K : Type*} [CommRing K]

/-- The canonical isomorphism from `K` to `K →ₗ[K] K`. -/
def LinearEquiv.smulId : K ≃ₗ[K] (K →ₗ[K] K) := {
  toFun := fun x ↦ x • LinearMap.id
  invFun := fun f ↦ f 1
  left_inv := by
    intro x
    simp only [LinearMap.smul_apply, LinearMap.id_coe, id_eq, smul_eq_mul, mul_one]
  right_inv := by
    intro f
    ext
    simp only [LinearMap.smul_apply, LinearMap.id_coe, id_eq, smul_eq_mul, mul_one]
  map_add' := by
    intro x y
    exact Module.add_smul x y LinearMap.id
  map_smul' := by
    intro x y
    exact IsScalarTower.smul_assoc x y LinearMap.id
}

/-- The basis of `K →ₗ[K] K` consisting of `LinearMap.id`. -/
noncomputable def Basis.ofEndSelf : Basis (Fin 1) K (K →ₗ[K] K)
    := Basis.map (Basis.singleton (Fin 1) K) (LinearEquiv.smulId)

end dim1linalg
