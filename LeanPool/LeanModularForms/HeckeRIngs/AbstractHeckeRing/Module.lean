/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.HeckeRIngs.AbstractHeckeRing.Multiplication

/-!
# Hecke Rings: Module Action

The module action of `𝕋 P ℤ` on `HeckeModule P ℤ` (formal sums of left cosets) and the faithfulness
theorem `eq_of_smul_eq_smul_𝕋`.
-/

open MulOpposite Set DoubleCoset Subgroup Subgroup.Commensurable

open scoped Pointwise

namespace HeckeRing

variable {G : Type*} [Group G]

variable (P : HeckePair G) (Z : Type*) [CommRing Z]

open Finsupp

/-- The scalar multiplication on `𝕋` by itself, defined as reverse multiplication.
Higher priority than the inherited `Mul.toSMul` so that `•` denotes the reverse action. -/
noncomputable instance (priority := 1100) instSMul𝕋 : SMul (𝕋 P ℤ) (𝕋 P ℤ) where
  smul x y := y * x

/-- The orbit of a left coset representative `β` under double coset representative `g`:
the set of left cosets `{β · σ_i · g | σ_i ∈ H/(H ∩ gHg⁻¹)}`. -/
noncomputable def smulOrbit (g : P.Δ) (β : P.Δ) :
    Finset (HeckeLeftCoset P) :=
  Finset.image (fun i : decompQuot P g =>
    (⟦⟨(β : G) * (i.out : G) * (g : G),
      delta_mul_mem P.H P.Δ i.out β g P.h₀⟩⟧ : HeckeLeftCoset P)) ⊤

/-- The smul orbit of any left coset under any double coset is nonempty. -/
lemma smulOrbit_nonempty (g : P.Δ) (β : P.Δ) :
    (smulOrbit P g β).Nonempty := by rw [smulOrbit]; simp

/-- The orbit is invariant under left coset equivalence: if `β₁H = β₂H`, then
    `smulOrbit g β₁ = smulOrbit g β₂`. This is the key API lemma that lets us
    replace `HeckeLeftCoset.rep j` with any representative of `j`. -/
lemma smulOrbit_lcRel (g : P.Δ) {β₁ β₂ : P.Δ} (h : lcRel P β₁ β₂) :
    smulOrbit P g β₁ = smulOrbit P g β₂ := by
  -- lcRel means {β₁} * H = {β₂} * H
  -- Each orbit element ⟦⟨β * i.out * g, ...⟩⟧ only depends on the left coset {β * i.out * g} * H
  -- Since β₁H = β₂H, for each i there exists i' with {β₁ * i.out * g} * H = {β₂ * i'.out * g} * H
  ext x; simp only [smulOrbit, Finset.top_eq_univ, Finset.mem_image, Finset.mem_univ, true_and]
  -- Both directions: show ⟦⟨β₁ * i.out * g⟩⟧ ∈ image iff ⟦⟨β₂ * j.out * g⟩⟧ ∈ image
  -- by showing they produce the same set of HeckeLeftCoset values
  suffices hsuff : ∀ (β β' : P.Δ), lcRel P β β' → ∀ i : decompQuot P g,
      ∃ j : decompQuot P g,
        (⟦⟨(β : G) * (i.out : G) * (g : G),
          delta_mul_mem P.H P.Δ i.out β g P.h₀⟩⟧ : HeckeLeftCoset P) =
        ⟦⟨(β' : G) * (j.out : G) * (g : G),
          delta_mul_mem P.H P.Δ j.out β' g P.h₀⟩⟧ by
    constructor
    · rintro ⟨i, hi⟩; obtain ⟨j, hj⟩ := hsuff β₁ β₂ h i; exact ⟨j, hi ▸ hj.symm⟩
    · rintro ⟨i, hi⟩; obtain ⟨j, hj⟩ := hsuff β₂ β₁ h.symm i; exact ⟨j, hi ▸ hj.symm⟩
  intro β β' hlc i
  -- hlc : {β} * H = {β'} * H, so β' ∈ {β} * H
  have hβ'_mem : (β' : G) ∈ ({(β : G)} : Set G) * (P.H : Set G) := by
    rw [hlc]; exact ⟨β', rfl, 1, P.H.one_mem, mul_one _⟩
  obtain ⟨_, hβ_eq, k, hk, hβ'_eq⟩ := hβ'_mem
  rw [Set.mem_singleton_iff] at hβ_eq; subst hβ_eq
  -- hβ'_eq : β * k = β', so β' = β * k, k ∈ H
  -- We need j s.t. {β * i.out * g} * H = {β' * j.out * g} * H
  -- Use j = ⟦k⁻¹ * i.out⟧ so β' * j.out * g ≈ (β*k) * (k⁻¹*i.out) * g = β * i.out * g
  set j : decompQuot P g := ⟦⟨k⁻¹ * i.out, P.H.mul_mem (P.H.inv_mem hk) (SetLike.coe_mem i.out)⟩⟧
  refine ⟨j, Quotient.sound ?_⟩
  change ({(β : G) * (i.out : G) * (g : G)} : Set G) * (P.H : Set G) =
    {(β' : G) * (j.out : G) * (g : G)} * P.H
  -- j.out = (k⁻¹ * i.out) * n for some n in the conjugate subgroup
  obtain ⟨n, hn_eq⟩ := QuotientGroup.mk_out_eq_mul
    ((ConjAct.toConjAct (g : G) • P.H).subgroupOf P.H)
    ⟨k⁻¹ * i.out, P.H.mul_mem (P.H.inv_mem hk) i.out.2⟩
  have hj_coe : (j.out : G) = k⁻¹ * (i.out : G) * (n : G) := by
    have := congr_arg (Subtype.val : P.H → G) hn_eq; simpa [Subgroup.coe_mul] using this
  have hn_conj : (g : G)⁻¹ * (n : G) * g ∈ P.H := by
    have := n.2; rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      ConjAct.smul_def] at this
    simpa [ConjAct.ofConjAct_toConjAct] using this
  rw [hj_coe, ← hβ'_eq]
  conv_rhs =>
    rw [show (β : G) * k * (k⁻¹ * (i.out : G) * ↑n) * (g : G) =
      (β : G) * (i.out : G) * (g : G) * ((g : G)⁻¹ * ↑n * (g : G)) from by group,
      ← Set.singleton_mul_singleton, mul_assoc]
  rw [Subgroup.singleton_mul_subgroup hn_conj]

/-- Corollary: `smulOrbit g (HeckeLeftCoset.rep ⟦β⟧) = smulOrbit g β`. -/
lemma smulOrbit_rep_mk (g β : P.Δ) :
    smulOrbit P g (HeckeLeftCoset.rep ⟦β⟧) = smulOrbit P g β :=
  smulOrbit_lcRel P g (Quotient.exact (Quotient.out_eq (⟦β⟧ : HeckeLeftCoset P)))


/-- The module action of the Hecke ring on formal sums of left cosets. -/
noncomputable instance instSMulHeckeModule : SMul (𝕋 P Z) (HeckeModule P Z) where
  smul t mm := Finsupp.sum t fun D1 b₁ => mm.sum fun m b₂ =>
    (∑ i ∈ smulOrbit P (HeckeCoset.rep D1) (HeckeLeftCoset.rep m),
      Finsupp.single i (b₁ * b₂ : Z) : (HeckeLeftCoset P) →₀ Z)

/-- The scalar multiplication on `HeckeModule` unfolds as a double sum over orbits. -/
lemma smul_eq_sum (T : 𝕋 P Z) (m : HeckeModule P Z) :
    T • m = Finsupp.sum T (fun D1 b₁ => m.sum fun m b₂ =>
      (∑ i ∈ smulOrbit P (HeckeCoset.rep D1) (HeckeLeftCoset.rep m),
        Finsupp.single i (b₁ * b₂ : Z) : (HeckeLeftCoset P) →₀ Z)) := rfl

/-- The action of a basis Hecke element on a basis module element. -/
lemma single_smul_single (t : HeckeCoset P) (m : HeckeLeftCoset P) (a b : Z) :
    ((Finsupp.single t a) : 𝕋 P Z) • ((Finsupp.single m b) : HeckeModule P Z) =
    (∑ i ∈ smulOrbit P (HeckeCoset.rep t) (HeckeLeftCoset.rep m),
      Finsupp.single i (a * b : Z) : (HeckeLeftCoset P) →₀ Z) := by
  rw [smul_eq_sum]
  simp [mul_zero, single_zero, Finset.sum_const_zero, sum_single_index, zero_mul]

/-- Every finsupp is a sum of its basis elements. -/
lemma single_basis {α : Type*} (t : Finsupp α Z) :
    t = ∑ (i ∈ t.support), single i (t.toFun i) :=
  (Finsupp.sum_single t).symm

/-- The one element of `HeckeModule`: the basis element for the identity left coset. -/
noncomputable instance instOneHeckeModule : One (HeckeModule P Z) :=
  ⟨Finsupp.single (HeckeLeftCoset.one P) 1⟩

/-- The one element of `HeckeModule` is the basis element corresponding to the identity
left coset. -/
lemma one_eq_HeckeLeftCoset_single :
    (1 : HeckeModule P Z) = Finsupp.single (HeckeLeftCoset.one P) 1 := rfl

/-- The module action is additive in the Hecke ring argument. -/
lemma smul_add_left (T₁ T₂ : 𝕋 P Z) (m : HeckeModule P Z) :
    (T₁ + T₂) • m = T₁ • m + T₂ • m := by
  simp only [smul_eq_sum]
  refine Finsupp.sum_add_index' (fun D1 => ?_) (fun D1 y b₂ => ?_)
  · simp [zero_mul, Finsupp.single_zero, Finset.sum_const_zero, Finsupp.sum]
  · simp only [Finsupp.sum, add_mul, Finsupp.single_add, Finset.sum_add_distrib]

/-- The zero element of the Hecke ring acts as zero on the module. -/
lemma zero_smul_HeckeModule (z : HeckeModule P Z) : (0 : 𝕋 P Z) • z = 0 := by
  simp only [smul_eq_sum]; exact Finsupp.sum_zero_index

/-- Any Hecke ring element acts as zero on the zero module element. -/
lemma smul_zero_HeckeModule (T : 𝕋 P Z) : T • (0 : HeckeModule P Z) = 0 := by
  simp only [smul_eq_sum]
  have : ∀ D (b : Z), (0 : HeckeModule P Z).sum (fun m c =>
      ∑ i ∈ smulOrbit P (HeckeCoset.rep D) (HeckeLeftCoset.rep m),
        Finsupp.single i (b * c)) = 0 := fun _ _ => Finsupp.sum_zero_index
  simp_rw [this]; simp [Finsupp.sum]

/-- The module action is additive in the module argument. -/
lemma smul_add_right (T : 𝕋 P Z) (m₁ m₂ : HeckeModule P Z) :
    T • (m₁ + m₂) = T • m₁ + T • m₂ := by
  simp only [smul_eq_sum]
  have inner_split : ∀ D (b : Z),
      (m₁ + m₂).sum (fun m c =>
        ∑ i ∈ smulOrbit P (HeckeCoset.rep D) (HeckeLeftCoset.rep m),
          Finsupp.single i (b * c)) =
      m₁.sum (fun m c =>
        ∑ i ∈ smulOrbit P (HeckeCoset.rep D) (HeckeLeftCoset.rep m),
          Finsupp.single i (b * c)) +
      m₂.sum (fun m c =>
        ∑ i ∈ smulOrbit P (HeckeCoset.rep D) (HeckeLeftCoset.rep m),
          Finsupp.single i (b * c)) := by
    intro D b
    exact Finsupp.sum_add_index'
      (fun m => by simp [mul_zero, Finsupp.single_zero, Finset.sum_const_zero])
      (fun m c₁ c₂ => by simp only [← Finset.sum_add_distrib, mul_add, Finsupp.single_add])
  simp_rw [inner_split]
  exact Finsupp.sum_add

/-- The smul orbits of distinct double cosets acting on the same left coset are disjoint. -/
lemma smulOrbit_disjoint_of_ne (g₁ g₂ : P.Δ) (β : P.Δ)
    (hne : (⟦g₁⟧ : HeckeCoset P) ≠ ⟦g₂⟧) :
    Disjoint (smulOrbit P g₁ β) (smulOrbit P g₂ β) := by
  rw [Finset.disjoint_left]
  intro x hx₁ hx₂
  apply hne; apply Quotient.sound; change dcRel P _ _
  simp only [smulOrbit, Finset.mem_image] at hx₁ hx₂
  obtain ⟨i₁, _, hi₁⟩ := hx₁; obtain ⟨i₂, _, hi₂⟩ := hx₂
  rw [← hi₂] at hi₁
  have hset : ({(β : G) * (i₁.out : G) * (g₁ : G)} : Set G) * (P.H : Set G) =
      {(β : G) * (i₂.out : G) * (g₂ : G)} * P.H := Quotient.exact hi₁
  have hmem : (β : G) * ↑i₁.out * (g₁ : G) ∈
      ({(β : G) * ↑i₂.out * (g₂ : G)} : Set G) * (↑P.H : Set G) := by
    rw [← hset]; exact ⟨_, rfl, 1, P.H.one_mem, mul_one _⟩
  obtain ⟨_, ha, k, hk, hkk⟩ := hmem
  rw [Set.mem_singleton_iff] at ha; subst ha
  have hstep : ↑i₂.out * (g₂ : G) * k = ↑i₁.out * (g₁ : G) :=
    mul_left_cancel (a := (β : G)) (by have := hkk; dsimp at this; group at this ⊢; exact this)
  have hg : (g₁ : G) = ↑(i₁.out⁻¹ * i₂.out) * (g₂ : G) * k := by
    apply mul_left_cancel (a := (↑i₁.out : G))
    have : ↑i₁.out * (↑(i₁.out⁻¹ * i₂.out) * (g₂ : G) * k) = ↑i₂.out * (g₂ : G) * k := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
    rw [this]; exact hstep.symm
  change DoubleCoset.doubleCoset (g₁ : G) P.H P.H =
    DoubleCoset.doubleCoset (g₂ : G) P.H P.H
  conv_lhs => rw [show (g₁ : G) = _ from hg]
  exact (DoubleCoset.doubleCoset_mul_right_eq_self P ⟨k, hk⟩ _).trans
    (doset_mul_left_eq_self P (i₁.out⁻¹ * i₂.out) _)

private lemma smul_one_eval (T : 𝕋 P Z) (D : HeckeCoset P) (m : HeckeLeftCoset P)
    (hm : m ∈ smulOrbit P (HeckeCoset.rep D) (HeckeLeftCoset.rep (HeckeLeftCoset.one P))) :
    (T • (1 : HeckeModule P Z)).toFun m = T.toFun D := by
  rw [smul_eq_sum, one_eq_HeckeLeftCoset_single]
  have hsimp : ∀ D1 (b₁ : Z),
      Finsupp.sum (Finsupp.single (HeckeLeftCoset.one P) (1 : Z))
        (fun m' b₂ => ∑ i ∈ smulOrbit P (HeckeCoset.rep D1) (HeckeLeftCoset.rep m'),
          Finsupp.single i (b₁ * b₂)) =
      ∑ i ∈ smulOrbit P (HeckeCoset.rep D1) (HeckeLeftCoset.rep (HeckeLeftCoset.one P)),
        Finsupp.single i b₁ := by
    intro D1 b1
    rw [Finsupp.sum_single_index
      (by simp [mul_zero, Finsupp.single_zero, Finset.sum_const_zero]), mul_one]
  simp_rw [hsimp]; unfold Finsupp.sum
  change (∑ x ∈ T.support,
    ∑ i ∈ smulOrbit P (HeckeCoset.rep x) (HeckeLeftCoset.rep (HeckeLeftCoset.one P)),
      Finsupp.single i (T.toFun x)) m = T.toFun D
  rw [Finsupp.finsetSum_apply]
  simp_rw [Finsupp.finsetSum_apply, Finsupp.single_apply]
  rw [Finset.sum_eq_single D]
  · rw [Finset.sum_eq_single_of_mem m hm (fun b _ hb => if_neg hb), if_pos rfl]
  · intro D' _ hne
    exact Finset.sum_eq_zero fun i hi =>
      if_neg (fun heq => absurd (heq ▸ hi)
        (Finset.disjoint_left.mp
          (smulOrbit_disjoint_of_ne P (HeckeCoset.rep D) (HeckeCoset.rep D')
            (HeckeLeftCoset.rep (HeckeLeftCoset.one P))
            (by simp only [HeckeCoset.rep, Quotient.out_eq]; exact Ne.symm hne)) hm))
  · intro hns
    exact Finset.sum_eq_zero fun x _ => by
      have h0 : T.toFun D = 0 := Finsupp.notMem_support_iff.mp hns
      simp [h0]

/-- Faithfulness of the module action: if two Hecke ring elements act identically on all
module elements, they are equal. -/
lemma eq_of_smul_eq_smul_𝕋 (T1 T2 : (𝕋 P Z))
    (h : ∀ (a : HeckeModule P Z), T1 • a = T2 • a) :
    T1 = T2 :=
  Finsupp.ext fun D => by
    obtain ⟨m, hm⟩ := smulOrbit_nonempty P (HeckeCoset.rep D)
      (HeckeLeftCoset.rep (HeckeLeftCoset.one P))
    have h1 := congrFun (congrArg Finsupp.toFun (h 1)) m
    rwa [smul_one_eval P Z T1 D m hm, smul_one_eval P Z T2 D m hm] at h1

/-- The module action of `𝕋 P ℤ` on `HeckeModule P ℤ` is faithful. -/
noncomputable instance instFaithfulSMulHeckeModule :
    FaithfulSMul (𝕋 P ℤ) (HeckeModule P ℤ) where
  eq_of_smul_eq_smul {t1 t2} h := eq_of_smul_eq_smul_𝕋 P ℤ t1 t2 h

/-- The scalar multiplication on `𝕋` is defined as reverse multiplication. -/
lemma smul_def (f g : 𝕋 P ℤ) : f • g = g * f := rfl

end HeckeRing
