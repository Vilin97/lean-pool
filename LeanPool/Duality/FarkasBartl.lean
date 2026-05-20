/-
Copyright (c) 2026 Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvorak
-/
import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.Module.Pi
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Have
import LeanPool.Duality.Common

private def withoutLastMap {m : ℕ} {R W : Type*} [Semiring R] [AddCommMonoid W] [Module R W]
    (A : W →ₗ[R] Fin m.succ → R) :
    W →ₗ[R] Fin m → R :=
  ⟨⟨
    fun w : W => fun i : Fin m => A w i.castSucc,
  by
    intros
    ext
    simp
  ⟩,
  by
    intros
    ext
    simp
  ⟩


private def auxLinMaps {m : ℕ} {R W : Type*} [Ring R] [AddCommMonoid W] [Module R W]
    (A : W →ₗ[R] Fin m.succ → R) (y : W) :
    W →ₗ[R] Fin m → R :=
  ⟨⟨
    withoutLastMap A - (A · ⟨m, m.lt_add_one⟩ • withoutLastMap A y),
  by
    intros
    ext
    simp only [withoutLastMap, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, map_add, smul_eq_mul, add_mul]
    abel
  ⟩,
  by
    intros
    ext
    simp [withoutLastMap, mul_sub, mul_assoc]
  ⟩

private def auxLinMap {m : ℕ} {R V W : Type*} [Semiring R] [AddCommGroup V] [Module R V]
    [AddCommMonoid W] [Module R W]
    (A : W →ₗ[R] Fin m.succ → R) (b : W →ₗ[R] V) (y : W) : W →ₗ[R] V :=
  ⟨⟨
    b - (A · ⟨m, m.lt_add_one⟩ • b y),
  by
    intros
    simp only [Pi.add_apply, Pi.sub_apply, map_add, add_smul]
    abel
  ⟩,
  by
    intros
    -- note that `simp` does not work here
    simp only [Pi.smul_apply, Pi.sub_apply, LinearMapClass.map_smul, RingHom.id_apply, smul_sub,
      IsScalarTower.smul_assoc]
  ⟩

private lemma filter_yielding_singleton_attach_sum {m : ℕ} {R V : Type*} [Semiring R]
    [AddCommMonoid V] [Module R V]
    (f : Fin m.succ → R) (v : V) :
    ∑ j ∈ (Finset.univ.filter (fun i : Fin m.succ => ¬(i.val < m))).attach, f j.val • v =
    f ⟨m, m.lt_add_one⟩ • v := by
  have singlet : Finset.univ.filter (fun i : Fin m.succ => ¬(i.val < m)) = {⟨m, m.lt_add_one⟩}
  · rw [Finset.ext_iff]
    intro i
    constructor <;> rw [Finset.mem_singleton, Finset.mem_filter] <;> intro hi
    · have him := hi.right
      push Not at him
      exact le_antisymm (Nat.le_of_lt_succ i.isLt) him
    · refine ⟨Finset.mem_univ i, ?_⟩
      rw [hi]
      push Not
      rfl
  rw [singlet, Finset.sum_attach _ (fun j : Fin m.succ => f j • v), Finset.sum_singleton]

private lemma impossible_index {m : ℕ} {i : Fin m.succ} (hi : ¬(i.val < m))
    (i_neq_m : i ≠ ⟨m, m.lt_add_one⟩) : False := by
  push Not at hi
  exact i_neq_m (le_antisymm (Fin.succ_le_succ_iff.→ i.isLt) hi)

variable {R V W : Type*}

private lemma finishing_piece {m : ℕ} [Semiring R]
    [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module R W]
    {A : W →ₗ[R] Fin m.succ → R} {w : W} {x : Fin m → V} :
    ∑ i : Fin m, withoutLastMap A w i • x i =
    ∑ i : { j : Fin m.succ // j ∈ Finset.univ.filter (·.val < m) }, A w i.val •
      x ⟨i.val.val, by aesop⟩ := by
  apply
    Finset.sum_bij'
      (fun i : Fin m =>
        ↓(⟨⟨i.val, by omega⟩, by aesop⟩ :
          { a : Fin m.succ // a ∈ Finset.univ.filter (·.val < m) }))
      (fun i' : { a : Fin m.succ // a ∈ Finset.univ.filter (·.val < m) } => ↓⟨i'.val.val, by aesop⟩)
      (by aesop)
      (by aesop)
      (by aesop)
      (by aesop)
  intros
  rfl

lemma industepFarkasBartl {m : ℕ} [DivisionRing R] [LinearOrder R] [IsStrictOrderedRing R]
    [AddCommGroup V] [LinearOrder V] [IsOrderedAddMonoid V] [Module R V] [PosSMulMono R V]
    [AddCommGroup W] [Module R W]
    (ih : ∀ A₀ : W →ₗ[R] Fin m → R, ∀ b₀ : W →ₗ[R] V,
      (∀ y₀ : W, 0 ≤ A₀ y₀ → 0 ≤ b₀ y₀) →
        (∃ x₀ : Fin m → V, 0 ≤ x₀ ∧ ∀ w₀ : W, ∑ i₀ : Fin m, A₀ w₀ i₀ • x₀ i₀ = b₀ w₀))
    {A : W →ₗ[R] Fin m.succ → R} {b : W →ₗ[R] V} (hAb : ∀ y : W, 0 ≤ A y → 0 ≤ b y) :
    ∃ x : Fin m.succ → V, 0 ≤ x ∧ ∀ w : W, ∑ i : Fin m.succ, A w i • x i = b w := by
  if
    is_easy : ∀ y : W, 0 ≤ withoutLastMap A y → 0 ≤ b y
  then
    obtain ⟨x, hx, hxb⟩ := ih (withoutLastMap A) b is_easy
    use (fun i : Fin m.succ => if hi : i.val < m then x ⟨i.val, hi⟩ else 0)
    constructor
    · intro i
      if hi : i.val < m then
        clear * - hi hx
        aesop
      else
        simp [hi]
    · intro w
      simp_rw [smul_dite, smul_zero]
      rw [Finset.sum_dite, Finset.sum_const_zero, add_zero]
      convert hxb w using 1
      symm
      apply finishing_piece
  else
    push Not at is_easy
    obtain ⟨y', hay', hby'⟩ := is_easy
    let M : Fin m.succ := ⟨m, lt_add_one m⟩ -- the last (new) index
    let y : W := (A y' M)⁻¹ • y' -- rescaled `y'`
    have hAy' : A y' M < 0
    · by_contra! contr
      exact (
        (hAb y' (fun i : Fin m.succ =>
          if hi : i.val < m then
            hay' ⟨i, hi⟩
          else if hiM : i = M then
            hiM ▸ contr
          else
            (impossible_index hi hiM).elim
        )).trans_lt hby'
      ).false
    have hAy : A y M = 1
    · convert inv_mul_cancel₀ hAy'.ne
      simp [y]
    have hAA : ∀ w : W, A (w - (A w M • y)) M = 0
    · intro w
      simp [hAy]
    have hbA : ∀ w : W, 0 ≤ withoutLastMap A (w - (A w M • y)) → 0 ≤ b (w - (A w M • y))
    · intro w hw
      apply hAb
      intro i
      if hi : i.val < m then
        exact hw ⟨i, hi⟩
      else if hiM : i = M then
        rw [hiM, hAA, Pi.zero_apply]
      else
        exfalso
        exact impossible_index hi hiM
    have hbAb : ∀ w : W,
        0 ≤ (withoutLastMap A - (A · M • withoutLastMap A y)) w → 0 ≤ (b - (A · M • b y)) w
    · simpa using hbA
    obtain ⟨x', hx', hxb'⟩ := ih (auxLinMaps A y) (auxLinMap A b y) hbAb
    use (fun i : Fin m.succ =>
      if hi : i.val < m then x' ⟨i.val, hi⟩ else b y - ∑ i : Fin m, withoutLastMap A y i • x' i)
    constructor
    · intro i
      if hi : i.val < m then
        clear * - hi hx'
        aesop
      else
        have hAy'' : (A y' M)⁻¹ ≤ 0
        · exact (inv_lt_zero.mpr hAy').le
        have hay : withoutLastMap A y ≤ 0
        · simpa [y] using smul_nonpos_of_nonpos_of_nonneg hAy'' hay'
        have hby : 0 ≤ b y
        · simpa [y] using smul_nonneg_of_nonpos_of_nonpos hAy'' hby'.le
        simpa [hi] using
          (Finset.sum_nonpos
            (fun i : Fin m => ↓(smul_nonpos_of_nonpos_of_nonneg (hay i) (hx' i)))).trans hby
    · intro w
      have haAa : ∑ i : Fin m, (withoutLastMap A w i - A w M * withoutLastMap A y i) • x' i =
          b w - A w M • b y
      · simpa using hxb' w
      rw [←add_eq_of_eq_sub haAa]
      simp_rw [smul_dite]
      rw [Finset.sum_dite]
      erw [filter_yielding_singleton_attach_sum]
      simp_rw [sub_smul]
      rw [Finset.sum_sub_distrib]
      simp_rw [←smul_smul, ←Finset.smul_sum]
      symm
      rw [smul_sub, finishing_piece]
      apply add_comm_sub

theorem finFarkasBartl {n : ℕ} [DivisionRing R] [LinearOrder R] [IsStrictOrderedRing R]
    [AddCommGroup V] [LinearOrder V] [IsOrderedAddMonoid V] [Module R V] [PosSMulMono R V]
    [AddCommGroup W] [Module R W]
    (A : W →ₗ[R] Fin n → R) (b : W →ₗ[R] V) :
    (∃ x : Fin n → V, 0 ≤ x ∧ ∀ w : W, ∑ j : Fin n, A w j • x j = b w) ≠
      (∃ y : W, 0 ≤ A y ∧ b y < 0) := by
  apply neq_of_iff_neg
  push Not
  refine ⟨fun ⟨x, hx, hb⟩ y hy => hb y ▸
    Finset.sum_nonneg (fun i : Fin n => ↓(smul_nonneg (hy i) (hx i))), ?_⟩
  induction n generalizing b with -- note that `A` is "generalized" automatically
  | zero =>
    have A_tauto : ∀ w : W, 0 ≤ A w := ↓(Nat.not_lt_zero _ ·.isLt |>.elim)
    intro hAb
    refine ⟨0, le_refl 0, fun w : W => ?_⟩
    simp_rw [Pi.zero_apply, smul_zero, Finset.sum_const_zero]
    apply le_antisymm (hAb w (A_tauto w))
    simpa using hAb (-w) (A_tauto (-w))
  | succ m ih =>
    exact industepFarkasBartl ih

theorem fintypeFarkasBartl {J : Type*} [Fintype J]
    [DivisionRing R] [LinearOrder R] [IsStrictOrderedRing R]
    [AddCommGroup V] [LinearOrder V] [IsOrderedAddMonoid V] [Module R V] [PosSMulMono R V]
    [AddCommGroup W] [Module R W]
    (A : W →ₗ[R] J → R) (b : W →ₗ[R] V) :
    (∃ x : J → V, 0 ≤ x ∧ ∀ w : W, ∑ j : J, A w j • x j = b w) ≠
      (∃ y : W, 0 ≤ A y ∧ b y < 0) := by
  convert
    finFarkasBartl ⟨⟨(A · ∘ (Fintype.equivFin J).symm), by aesop⟩, by aesop⟩ b
      using 1
  · constructor <;> intro ⟨x, hx, hA⟩
    · use x ∘ (Fintype.equivFin J).invFun
      constructor
      · intro j
        simpa using hx ((Fintype.equivFin J).invFun j)
      · intro w
        convert hA w
        apply Finset.sum_equiv (Fintype.equivFin J).symm <;>
        · intros
          simp
    · use x ∘ (Fintype.equivFin J).toFun
      constructor
      · intro j
        simpa using hx ((Fintype.equivFin J).toFun j)
      · intro w
        convert hA w
        apply Finset.sum_equiv (Fintype.equivFin J) <;>
        · intro
          simp
  · constructor <;> intro ⟨y, hAy, hby⟩ <;> refine ⟨y, fun j => ?_, hby⟩
    · simpa using hAy ((Fintype.equivFin J).invFun j)
    · simpa using hAy ((Fintype.equivFin J).toFun j)

theorem almostFarkasBartl {J : Type*} [Fintype J]
    [DivisionRing R] [LinearOrder R] [IsStrictOrderedRing R]
    [AddCommGroup W] [Module R W]
    (A : W →ₗ[R] J → R) (b : W →ₗ[R] R) :
    (∃ x : J → R, 0 ≤ x ∧ ∀ w : W, ∑ j : J, A w j • x j = b w) ≠
      (∃ y : W, 0 ≤ A y ∧ b y < 0) :=
  fintypeFarkasBartl A b

theorem coordinateFarkasBartl {I J : Type*} [Fintype J]
    [DivisionRing R] [LinearOrder R] [IsStrictOrderedRing R]
    (A : (I → R) →ₗ[R] J → R) (b : (I → R) →ₗ[R] R) :
    (∃ x : J → R, 0 ≤ x ∧ ∀ w : I → R, ∑ j : J, A w j • x j = b w) ≠
      (∃ y : I → R, 0 ≤ A y ∧ b y < 0) :=
  almostFarkasBartl A b
