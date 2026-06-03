/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.HeckeRIngs.GL2.HeckeAction

/-!
# Hecke Operators as Endomorphisms of Modular Forms

Constructs the Hecke operator `T(D)` as an endomorphism of `ModularForm 𝒮ℒ k`,
proving holomorphicity, linearity, and boundedness at cusps.

## Main definitions

* `heckeOperator` — `T(D) : ModularForm 𝒮ℒ k → ModularForm 𝒮ℒ k`
* `heckeOperatorLinear` — `T(D)` as a ℂ-linear map
* `heckeOperator_comp` — composition corresponds to Hecke algebra multiplication

## References

* Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, §3.4
-/

open Matrix Matrix.SpecialLinearGroup Subgroup.Commensurable Pointwise
open HeckeRing DoubleCoset HeckeRing.GLn HeckeRing.GL2
open scoped Pointwise ModularForm MatrixGroups UpperHalfPlane Manifold

namespace HeckeRing.GL2

/-- `𝒮ℒ` has determinant 1: all elements come from SL₂(ℤ). -/
instance : Subgroup.HasDetOne 𝒮ℒ where
  det_eq {γ} hγ := by
    simp only [MonoidHom.mem_range] at hγ
    obtain ⟨s, rfl⟩ := hγ
    exact det_mapGL s

section Holomorphicity

/-- The Hecke slash action preserves holomorphicity. -/
lemma heckeSlash_holomorphic (k : ℤ) (D : HeckeCoset (GLPair 2)) (f : ℍ → ℂ)
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (heckeSlash k D f) :=
  MDifferentiable.sum fun _ _ => hf.slash k _

end Holomorphicity

section ModularFormConstructor

/-- `GL₂(ℚ)` maps cusps of `𝒮ℒ` to cusps: the Möbius action preserves `ℙ¹(ℚ)`. -/
lemma glMap_smul_isCusp (A : GL (Fin 2) ℚ) {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ) :
    IsCusp (glMap A • c) 𝒮ℒ := by
  rw [isCusp_SL2Z_iff] at hc ⊢
  obtain ⟨q, rfl⟩ := hc
  rw [show glMap A • OnePoint.map (Rat.cast : ℚ → ℝ) q =
      OnePoint.map (Rat.cast : ℚ → ℝ) (A • q)
      from (OnePoint.map_smul (algebraMap ℚ ℝ) A q).symm]
  exact ⟨_, rfl⟩

/-- The Hecke slash action preserves boundedness at cusps. -/
lemma heckeSlash_bdd_at_cusps (k : ℤ) (D : HeckeCoset (GLPair 2)) (f : ModularForm 𝒮ℒ k)
    {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ) : c.IsBoundedAt (heckeSlash k D f) k := by
  simp only [heckeSlash]
  apply Finset.sum_induction _ (fun g => c.IsBoundedAt g k) (fun _ _ ha hb => ha.add hb)
    ((0 : ModularForm 𝒮ℒ k).bdd_at_cusps' hc)
  intro i _
  exact OnePoint.IsBoundedAt.smul_iff.mp (f.bdd_at_cusps' (glMap_smul_isCusp _ hc))

/-- The Hecke operator `T(D)` on modular forms, preserving slash invariance and holomorphicity. -/
noncomputable def heckeOperator (k : ℤ) (D : HeckeCoset (GLPair 2)) (f : ModularForm 𝒮ℒ k) :
    ModularForm 𝒮ℒ k where
  toSlashInvariantForm := heckeSlashInvariant k D f.toSlashInvariantForm
  holo' := heckeSlash_holomorphic k D f f.holo'
  bdd_at_cusps' hc := heckeSlash_bdd_at_cusps k D f hc

end ModularFormConstructor

section LinearMap

/-- Hecke slash of negation. -/
lemma heckeSlash_neg (k : ℤ) (D : HeckeCoset (GLPair 2)) (f : ℍ → ℂ) :
    heckeSlash k D (-f) = -heckeSlash k D f := by
  simp only [heckeSlash, SlashAction.neg_slash, Finset.sum_neg_distrib]

/-- The Hecke operator `T(D)` as a `ℂ`-linear map on modular forms. -/
noncomputable def heckeOperatorLinear (k : ℤ) (D : HeckeCoset (GLPair 2)) :
    ModularForm 𝒮ℒ k →ₗ[ℂ] ModularForm 𝒮ℒ k where
  toFun := heckeOperator k D
  map_add' f g := by
    ext z
    change heckeSlash k D (↑(f + g)) z =
      (heckeOperator k D f + heckeOperator k D g) z
    simp only [ModularForm.add_apply]
    change heckeSlash k D (↑f + ↑g) z =
      heckeSlash k D (↑f) z + heckeSlash k D (↑g) z
    rw [heckeSlash_add]; rfl
  map_smul' c f := by
    ext z
    change heckeSlash k D (↑(c • f)) z = (c • heckeOperator k D f) z
    change heckeSlash k D (c • ↑f) z = c • heckeSlash k D (↑f) z
    rw [heckeSlash_smul]; rfl

end LinearMap

section FiberSum

/-- For each pair `(i,j)` with `mulMap(i,j) = D`, decompose `σᵢδ₁·σⱼδ₂ = h₁·δ_D·h₂`
    to get both the slash equality `f ∣[k] (σⱼδ₂·σᵢδ₁) = f ∣[k] tRep D q` and
    the right-coset condition `{σᵢδ₁}·{σⱼδ₂}·H = {q·δ_D}·H`. -/
private lemma slash_and_coset_of_mulMap_eq (k : ℤ) (D₁ D₂ D : HeckeCoset (GLPair 2))
    (f : ℍ → ℂ) (hf : ∀ γ ∈ 𝒮ℒ, f ∣[k] γ = f)
    (p : decompQuot (GLPair 2) (HeckeCoset.rep D₁) ×
         decompQuot (GLPair 2) (HeckeCoset.rep D₂))
    (hp : mulMap (GLPair 2) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) (p.1, p.2) = D) :
    ∃ q : decompQuot (GLPair 2) (HeckeCoset.rep D),
      (f ∣[k] (tRep D₂ p.2 * tRep D₁ p.1) = f ∣[k] tRep D q) ∧
      ({(p.1.out : GL _ ℚ) * (HeckeCoset.rep D₁ : GL _ ℚ)} : Set _) *
      {(p.2.out : GL _ ℚ) * (HeckeCoset.rep D₂ : GL _ ℚ)} *
      ((GLPair 2).H : Set (GL (Fin 2) ℚ)) =
      {(q.out : GL _ ℚ) * (HeckeCoset.rep D : GL _ ℚ)} *
      ((GLPair 2).H : Set (GL (Fin 2) ℚ)) := by
  have hmem : (p.1.out : GL (Fin 2) ℚ) * (HeckeCoset.rep D₁ : GL _ ℚ) *
      ((p.2.out : GL _ ℚ) * (HeckeCoset.rep D₂ : GL _ ℚ)) ∈ HeckeCoset.toSet D := by
    have : HeckeCoset.toSet (mulMap (GLPair 2) (HeckeCoset.rep D₁)
        (HeckeCoset.rep D₂) (p.1, p.2)) = HeckeCoset.toSet D := by rw [hp]
    rw [← this]
    change _ ∈ HeckeCoset.toSet (⟦⟨_, _⟩⟧ : HeckeCoset (GLPair 2))
    simp only [HeckeCoset.toSet_mk]; exact DoubleCoset.mem_doubleCoset_self _ _ _
  rw [HeckeCoset.toSet_eq_rep, DoubleCoset.mem_doubleCoset] at hmem
  obtain ⟨h₁, hh₁, h₂, hh₂, heq⟩ := hmem
  set q : decompQuot (GLPair 2) (HeckeCoset.rep D) := ⟦⟨h₁, hh₁⟩⟧; refine ⟨q, ?_, ?_⟩
  · rw [tRep_mul_anti D₁ D₂ p.1 p.2, heq]; exact slash_tRep_of_mem k D _ h₂ hh₁ hh₂ f hf
  · have h_K := QuotientGroup.leftRel_apply.mp (Quotient.exact (Quotient.out_eq q))
    rw [Subgroup.mem_subgroupOf] at h_K
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def] at h_K
    simp only [ConjAct.ofConjAct_toConjAct, map_inv, inv_inv] at h_K
    set κ := (HeckeCoset.rep D : GL _ ℚ)⁻¹ * ((q.out : GL _ ℚ)⁻¹ * h₁) *
        (HeckeCoset.rep D : GL _ ℚ)
    rw [Set.singleton_mul_singleton, heq]; apply leftCoset_eq_of_not_disjoint
    rw [Set.not_disjoint_iff]
    exact ⟨h₁ * (HeckeCoset.rep D : GL _ ℚ) * h₂,
      ⟨1, (GLPair 2).H.one_mem, by simp [smul_eq_mul]⟩,
      ⟨κ * h₂, (GLPair 2).H.mul_mem h_K hh₂, by simp only [smul_eq_mul, κ]; group⟩⟩

/-- The product `σᵢδ₁ · σⱼδ₂` lies in `toSet D` when a right-coset witness exists. -/
private lemma prod_mem_D_of_rightCoset (D : HeckeCoset (GLPair 2)) (g : GL (Fin 2) ℚ)
    (q : decompQuot (GLPair 2) (HeckeCoset.rep D)) (h : GL (Fin 2) ℚ)
    (hh : h ∈ ((GLPair 2).H : Set (GL (Fin 2) ℚ)))
    (hprod : g = (q.out : GL _ ℚ) * (HeckeCoset.rep D : GL _ ℚ) * h) :
    g ∈ HeckeCoset.toSet D := by
  rw [HeckeCoset.toSet_eq_rep, DoubleCoset.mem_doubleCoset]
  exact ⟨(q.out : GL (Fin 2) ℚ), SetLike.coe_mem q.out, h, hh, hprod⟩

/-- The product `σᵢδ₁ · σⱼδ₂` lies in `toSet (mulMap p)`. -/
private lemma prod_mem_mulMap (D₁ D₂ : HeckeCoset (GLPair 2))
    (p : decompQuot (GLPair 2) (HeckeCoset.rep D₁) ×
         decompQuot (GLPair 2) (HeckeCoset.rep D₂)) :
    (p.1.out : GL _ ℚ) * (HeckeCoset.rep D₁ : GL _ ℚ) *
      ((p.2.out : GL _ ℚ) * (HeckeCoset.rep D₂ : GL _ ℚ)) ∈
      HeckeCoset.toSet (mulMap (GLPair 2) (HeckeCoset.rep D₁)
        (HeckeCoset.rep D₂) (p.1, p.2)) := by
  change _ ∈ HeckeCoset.toSet (⟦⟨_, _⟩⟧ : HeckeCoset (GLPair 2))
  simp only [HeckeCoset.toSet_mk]; exact DoubleCoset.mem_doubleCoset_self _ _ _

/-- From a right-coset condition `{σᵢδ₁}·{σⱼδ₂}·H = {q·δ_D}·H`, derive
    that `mulMap(p) = D`: the product lands in the double coset `D`. -/
private lemma mulMap_eq_of_rightCoset (D₁ D₂ D : HeckeCoset (GLPair 2))
    (p : decompQuot (GLPair 2) (HeckeCoset.rep D₁) ×
         decompQuot (GLPair 2) (HeckeCoset.rep D₂))
    (q : decompQuot (GLPair 2) (HeckeCoset.rep D))
    (hp_rc : ({(p.1.out : GL _ ℚ) * (HeckeCoset.rep D₁ : GL _ ℚ)} : Set _) *
      {(p.2.out : GL _ ℚ) * (HeckeCoset.rep D₂ : GL _ ℚ)} *
      ((GLPair 2).H : Set (GL (Fin 2) ℚ)) =
      {(q.out : GL _ ℚ) * (HeckeCoset.rep D : GL _ ℚ)} *
      ((GLPair 2).H : Set (GL (Fin 2) ℚ))) :
    mulMap (GLPair 2) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) (p.1, p.2) = D := by
  have h_in_rc : (p.1.out : GL _ ℚ) * (HeckeCoset.rep D₁ : GL _ ℚ) *
      ((p.2.out : GL _ ℚ) * (HeckeCoset.rep D₂ : GL _ ℚ)) ∈
      ({(q.out : GL _ ℚ) * (HeckeCoset.rep D : GL _ ℚ)} : Set _) *
      ((GLPair 2).H : Set (GL (Fin 2) ℚ)) := by
    rw [← hp_rc, Set.singleton_mul_singleton]
    exact ⟨_, rfl, 1, (GLPair 2).H.one_mem, by simp only [mul_one]⟩
  obtain ⟨_, hd_eq, h, hh, hprod⟩ := h_in_rc
  rw [Set.mem_singleton_iff] at hd_eq; subst hd_eq
  set M := mulMap (GLPair 2) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) (p.1, p.2)
  exact HeckeCoset_ext_toSet (GLPair 2) (by
    rw [HeckeCoset.toSet_eq_rep, HeckeCoset.toSet_eq_rep]
    exact DoubleCoset.eq_of_not_disjoint (by
      rw [Set.not_disjoint_iff]
      have hm := prod_mem_mulMap D₁ D₂ p
      rw [HeckeCoset.toSet_eq_rep] at hm
      have hd := prod_mem_D_of_rightCoset D _ q h hh hprod.symm
      rw [HeckeCoset.toSet_eq_rep] at hd
      exact ⟨_, hm, hd⟩))

private lemma heckeSlash_fiber_sum [DecidableEq (HeckeCoset (GLPair 2))] (k : ℤ)
    (D₁ D₂ D : HeckeCoset (GLPair 2))
    (_hD : D ∈ mulSupport (GLPair 2) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂))
    (f : ℍ → ℂ) (hf : ∀ γ ∈ 𝒮ℒ, f ∣[k] γ = f) :
    (∑ p ∈ Finset.univ.filter
        (fun p : decompQuot (GLPair 2) (HeckeCoset.rep D₁) ×
                 decompQuot (GLPair 2) (HeckeCoset.rep D₂) =>
          mulMap (GLPair 2) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) (p.1, p.2) = D),
      f ∣[k] (tRep D₂ p.2 * tRep D₁ p.1)) =
    (m (GLPair 2) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂)) D •
      ∑ q : decompQuot (GLPair 2) (HeckeCoset.rep D),
        f ∣[k] tRep D q := by
  classical
  have h_main := slash_and_coset_of_mulMap_eq k D₁ D₂ D f hf
  set q_of : decompQuot (GLPair 2) (HeckeCoset.rep D₁) ×
      decompQuot (GLPair 2) (HeckeCoset.rep D₂) →
      decompQuot (GLPair 2) (HeckeCoset.rep D) := fun p =>
    if h : mulMap (GLPair 2) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) (p.1, p.2) = D
    then (h_main p h).choose else ⟦1⟧
  have h_slash_eq : ∀ p,
      mulMap (GLPair 2) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) (p.1, p.2) = D →
      f ∣[k] (tRep D₂ p.2 * tRep D₁ p.1) = f ∣[k] tRep D (q_of p) := by
    intro p hp; simp only [q_of, hp, dif_pos]; exact (h_main p hp).choose_spec.1
  have h_coset_eq : ∀ p,
      mulMap (GLPair 2) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) (p.1, p.2) = D →
      ({(p.1.out : GL _ ℚ) * (HeckeCoset.rep D₁ : GL _ ℚ)} : Set _) *
      {(p.2.out : GL _ ℚ) * (HeckeCoset.rep D₂ : GL _ ℚ)} *
      ((GLPair 2).H : Set (GL (Fin 2) ℚ)) =
      {((q_of p).out : GL _ ℚ) * (HeckeCoset.rep D : GL _ ℚ)} *
      ((GLPair 2).H : Set (GL (Fin 2) ℚ)) := by
    intro p hp; simp only [q_of, hp, dif_pos]; exact (h_main p hp).choose_spec.2
  set S := Finset.univ.filter (fun p : decompQuot (GLPair 2) (HeckeCoset.rep D₁) ×
      decompQuot (GLPair 2) (HeckeCoset.rep D₂) =>
      mulMap (GLPair 2) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) (p.1, p.2) = D)
  rw [Finset.sum_congr rfl (fun p hp => by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    exact h_slash_eq p hp)]
  rw [← Finset.sum_fiberwise (s := S) (g := q_of)]
  conv_lhs =>
    arg 2; ext q
    rw [Finset.sum_congr rfl (fun p hp => by
      simp only [Finset.mem_filter] at hp; rw [hp.2])]
    rw [Finset.sum_const]
  have h_fiber_eq : ∀ q : decompQuot (GLPair 2) (HeckeCoset.rep D),
      (S.filter (fun p => q_of p = q)).card = Nat.card
        {p : decompQuot (GLPair 2) (HeckeCoset.rep D₁) ×
             decompQuot (GLPair 2) (HeckeCoset.rep D₂) |
          ({(p.1.out : GL _ ℚ) * (HeckeCoset.rep D₁ : GL _ ℚ)} : Set _) *
          {(p.2.out : GL _ ℚ) * (HeckeCoset.rep D₂ : GL _ ℚ)} *
          ((GLPair 2).H : Set (GL (Fin 2) ℚ)) =
          {(q.out : GL _ ℚ) * (HeckeCoset.rep D : GL _ ℚ)} *
          ((GLPair 2).H : Set (GL (Fin 2) ℚ))} := by
    intro q; rw [← Nat.card_eq_finsetCard]; apply Nat.card_congr
    exact {
      toFun := fun ⟨p, hp⟩ => ⟨p, by
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hp
        rw [← hp.2]; exact h_coset_eq p hp.1⟩
      invFun := fun ⟨p, hp_rc⟩ => ⟨p, by
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
        have hmap := mulMap_eq_of_rightCoset D₁ D₂ D p q hp_rc
        refine ⟨hmap, ?_⟩; simp only [q_of, hmap, dif_pos]
        set q' := (h_main p hmap).choose; by_contra hne
        exact decompQuot_coset_diff (GLPair 2) (HeckeCoset.rep D) q' q hne
          ((h_main p hmap).choose_spec.2.symm.trans hp_rc)⟩
      left_inv := fun ⟨_, _⟩ => rfl
      right_inv := fun ⟨_, _⟩ => rfl }
  simp_rw [h_fiber_eq,
    heckeMultiplicity_uniform (GLPair 2) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) D]
  set n := Nat.card
    {p : decompQuot (GLPair 2) (HeckeCoset.rep D₁) ×
         decompQuot (GLPair 2) (HeckeCoset.rep D₂) |
      ({(p.1.out : GL _ ℚ) * (HeckeCoset.rep D₁ : GL _ ℚ)} : Set _) *
      {(p.2.out : GL _ ℚ) * (HeckeCoset.rep D₂ : GL _ ℚ)} *
      ((GLPair 2).H : Set (GL (Fin 2) ℚ)) =
      {(HeckeCoset.rep D : GL _ ℚ)} * ((GLPair 2).H : Set (GL (Fin 2) ℚ))}
  rw [show ∑ x : decompQuot (GLPair 2) (HeckeCoset.rep D), n • f ∣[k] tRep D x =
      n • ∑ x, f ∣[k] tRep D x from Finset.sum_nsmul _ _ _]
  simp only [m, Finsupp.coe_mk, heckeMultiplicity, n, Nat.cast_smul_eq_nsmul ℤ]

end FiberSum

section HeckeAlgebraAction

/-- The extended Hecke slash action: extends `heckeSlash` by ℤ-linearity from single
    double cosets `HeckeCoset` to formal sums `𝕋 (GLPair 2) ℤ` (the full Hecke algebra).
    `heckeSlashExt k T f = T.sum (fun D c => c • heckeSlash k D f)`. -/
noncomputable def heckeSlashExt (k : ℤ) (T : HeckeAlgebra 2) (f : ℍ → ℂ) : ℍ → ℂ :=
  T.sum (fun D c => c • heckeSlash k D f)

/-- The extended action on a single double coset recovers `heckeSlash`. -/
lemma heckeSlashExt_single (k : ℤ) (D : HeckeCoset (GLPair 2)) (f : ℍ → ℂ) :
    heckeSlashExt k (Finsupp.single D 1) f = heckeSlash k D f := by
  simp [heckeSlashExt, Finsupp.sum_single_index]

/-- Multiplicativity of the Hecke slash for Γ-invariant functions:
    `T(D₁)(T(D₂)(f)) = (T(D₂) * T(D₁))(f)` where `f` is any Γ-invariant function.
    The proof reindexes the double sum by grouping pairs `(i,j)` according to
    `mulMap(i,j)`, using `heckeMultiplicity_uniform` for the fiber counting. -/
private theorem heckeSlash_comp (k : ℤ) (D₁ D₂ : HeckeCoset (GLPair 2)) (f : ℍ → ℂ)
    (hf : ∀ γ ∈ 𝒮ℒ, f ∣[k] γ = f) : heckeSlash k D₁ (heckeSlash k D₂ f) =
    heckeSlashExt k (TSingle (GLPair 2) ℤ D₂ 1 * TSingle (GLPair 2) ℤ D₁ 1) f := by
  rw [show heckeSlashExt k (TSingle (GLPair 2) ℤ D₂ 1 *
      TSingle (GLPair 2) ℤ D₁ 1) f =
      (m (GLPair 2) (HeckeCoset.rep D₂) (HeckeCoset.rep D₁)).sum
        (fun D c => c • heckeSlash k D f) from by
    unfold heckeSlashExt; rw [mul_singleton_𝕋]; simp]
  have h_comm : m (GLPair 2) (HeckeCoset.rep D₂) (HeckeCoset.rep D₁) =
      m (GLPair 2) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) := by
    have h1 := @T_single_one_mul_T_single_one _ _ (GLPair 2) D₂ D₁
    have h2 := @T_single_one_mul_T_single_one _ _ (GLPair 2) D₁ D₂
    rw [← h1, ← h2]
    exact (instCommRingHeckeAlgebra (n := 2)).mul_comm _ _
  rw [h_comm]; simp_rw [heckeSlash]
  rw [show (∑ i : decompQuot (GLPair 2) (HeckeCoset.rep D₁),
      (∑ j : decompQuot (GLPair 2) (HeckeCoset.rep D₂),
        f ∣[k] tRep D₂ j) ∣[k] tRep D₁ i) =
      ∑ i, ∑ j, (f ∣[k] tRep D₂ j) ∣[k] tRep D₁ i from by
    congr 1; ext i
    induction Finset.univ (α := decompQuot (GLPair 2) (HeckeCoset.rep D₂))
        using Finset.cons_induction with
    | empty => simp [SlashAction.zero_slash]
    | cons a s has ih => simp [Finset.sum_cons, SlashAction.add_slash]]
  have h_slash_mul :
      ∀ (i : decompQuot (GLPair 2) (HeckeCoset.rep D₁))
        (j : decompQuot (GLPair 2) (HeckeCoset.rep D₂)),
      (f ∣[k] tRep D₂ j) ∣[k] tRep D₁ i = f ∣[k] (tRep D₂ j * tRep D₁ i) := by
    intro i j
    change (f ∣[k] glMap (tRep D₂ j)) ∣[k] glMap (tRep D₁ i) =
      f ∣[k] glMap (tRep D₂ j * tRep D₁ i)
    rw [map_mul, ← SlashAction.slash_mul]
  simp_rw [h_slash_mul]; rw [← Fintype.sum_prod_type']
  change (∑ p : decompQuot (GLPair 2) (HeckeCoset.rep D₁) ×
      decompQuot (GLPair 2) (HeckeCoset.rep D₂),
      f ∣[k] (tRep D₂ p.2 * tRep D₁ p.1)) = _
  letI : DecidableEq (HeckeCoset (GLPair 2)) := Classical.decEq _
  rw [← Finset.sum_fiberwise_of_maps_to
    (g := fun p => mulMap (GLPair 2) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) (p.1, p.2))
    (fun p _ => Finset.mem_image_of_mem _ (Finset.mem_univ _)),
    show Finset.image (mulMap (GLPair 2) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂))
      Finset.univ =
      mulSupport (GLPair 2) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) from rfl,
    Finsupp.sum,
    show (m (GLPair 2) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂)).support =
      mulSupport (GLPair 2) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) from rfl]
  exact Finset.sum_congr rfl fun D hD => heckeSlash_fiber_sum k D₁ D₂ D hD f hf

end HeckeAlgebraAction

section Composition

/-- Composing Hecke operators corresponds to Hecke algebra multiplication
    (Shimura Proposition 3.30): `T(D₁)(T(D₂)(f)) = (T(D₂) · T(D₁))(f)`. -/
theorem heckeOperator_comp (k : ℤ) (D₁ D₂ : HeckeCoset (GLPair 2)) (f : ModularForm 𝒮ℒ k) :
    (heckeOperator k D₁ (heckeOperator k D₂ f) : ℍ → ℂ) =
    heckeSlashExt k (TSingle (GLPair 2) ℤ D₂ 1 * TSingle (GLPair 2) ℤ D₁ 1) f :=
  heckeSlash_comp k D₁ D₂ f (fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ hγ)

end Composition

end HeckeRing.GL2

-- TODO: Package the Hecke action as an algebra anti-homomorphism
-- `HeckeAlgebra 2 →+* Module.End ℂ (ModularForm 𝒮ℒ k)`
-- using `heckeOperator_comp` for multiplicativity and `heckeOperatorLinear` for linearity.
-- Note: the order reversal D₂ * D₁ means this is an anti-homomorphism, or equivalently
-- a homomorphism from HeckeAlgebra 2ᵐᵒᵖ. Since HeckeAlgebra 2 is commutative, this is moot.
