/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/

import Mathlib

/-!
# The multiquadratic order

Blueprint node K02: the ring `𝒪_r = ℤ[X₁,…,Xₘ] / (Xⱼ² - rⱼ)`, monomials `mono S`,
sign embeddings `emb`, and conjugations `conj`. Linear independence of square roots is not
used here.
-/

open MvPolynomial Finset
open scoped symmDiff

namespace Nikodym.MultiQuad

noncomputable section

variable {m : ℕ}

/-- Blueprint K02: the relation ideal `(Xⱼ² - rⱼ)ⱼ` in `ℤ[X₁,…,Xₘ]`. -/
def relIdeal (r : Fin m → ℕ) : Ideal (MvPolynomial (Fin m) ℤ) :=
  Ideal.span (Set.range fun j => X j ^ 2 - C (r j : ℤ))

/-- Blueprint K02: the multiquadratic order `𝒪_r`. -/
abbrev Order (r : Fin m → ℕ) := MvPolynomial (Fin m) ℤ ⧸ relIdeal r

/-- Blueprint K02: the image of a square-free monomial `∏_{j ∈ S} Xⱼ` in `𝒪_r`. -/
def mono (r : Fin m → ℕ) (S : Finset (Fin m)) : Order r :=
  Ideal.Quotient.mk _ (∏ j ∈ S, X j)

/-- Blueprint K02: the image of the indeterminate `Xⱼ` in `𝒪_r`. -/
def gen (r : Fin m → ℕ) (j : Fin m) : Order r :=
  Ideal.Quotient.mk _ (X j)

/-- Constants in the polynomial ring map to integer casts in the order. -/
lemma mk_C (r : Fin m → ℕ) (z : ℤ) :
    Ideal.Quotient.mk (relIdeal r) (C z) = z := by
  rw [← map_intCast (Ideal.Quotient.mk (relIdeal r))]
  rfl

/-- Blueprint K02: `mono ∅ = 1`. -/
@[simp]
lemma mono_empty (r : Fin m → ℕ) : mono r ∅ = 1 := by
  simp [mono]

/-- Blueprint K02: `mono S` is the product of the generators indexed by `S`. -/
lemma mono_eq_prod_gen (r : Fin m → ℕ) (S : Finset (Fin m)) :
    mono r S = ∏ j ∈ S, gen r j := by
  simp [mono, gen, map_prod]

/-- Evaluation of a polynomial vanishes on `relIdeal r` as soon as it sends each generator
`Xⱼ² - rⱼ` to zero. -/
lemma eval₂Hom_eq_zero_of_mem_relIdeal {R : Type*} [CommRing R] (r : Fin m → ℕ)
    (f : ℤ →+* R) (s : Fin m → R) (hs : ∀ j, s j ^ 2 = f (r j)) :
    ∀ p ∈ relIdeal r, eval₂Hom f s p = 0 := by
  intro p hp
  have hle : relIdeal r ≤ RingHom.ker (eval₂Hom f s) := by
    rw [relIdeal, Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    simp [RingHom.mem_ker, hs]
  exact RingHom.mem_ker.mp (hle hp)

/-- Blueprint K02: `gen r j ^ 2 = rⱼ` in `𝒪_r`. -/
@[simp]
theorem gen_sq (r : Fin m → ℕ) (j : Fin m) : gen r j ^ 2 = (r j : Order r) := by
  refine eq_of_sub_eq_zero ?_
  have hr : (r j : Order r) = Ideal.Quotient.mk (relIdeal r) (C (r j : ℤ)) :=
    (mk_C r (r j)).symm
  simp only [gen, hr, ← map_pow, ← map_sub]
  exact (Ideal.Quotient.eq_zero_iff_mem).2 Ideal.mem_span_range_self

/-- Blueprint K02: if `j ∉ S` then `gen j * mono S = mono (insert j S)`. -/
lemma gen_mul_mono_of_notMem (r : Fin m → ℕ) {j : Fin m} {S : Finset (Fin m)}
    (hj : j ∉ S) : gen r j * mono r S = mono r (insert j S) := by
  simp [mono_eq_prod_gen, prod_insert hj]

/-- Blueprint K02: if `j ∈ S` then `gen j * mono S = rⱼ * mono (S.erase j)`. -/
lemma gen_mul_mono_of_mem (r : Fin m → ℕ) {j : Fin m} {S : Finset (Fin m)}
    (hj : j ∈ S) : gen r j * mono r S = (r j : Order r) * mono r (S.erase j) := by
  rw [mono_eq_prod_gen, ← mul_prod_erase _ _ hj, ← mul_assoc, ← sq, gen_sq, mono_eq_prod_gen]

/-- The `ℤ`-span of `{mono S}` is closed under multiplication by `gen r j`. -/
lemma mul_gen_mem_span (r : Fin m → ℕ) (j : Fin m) {x : Order r}
    (hx : x ∈ Submodule.span ℤ (Set.range (mono r))) :
    gen r j * x ∈ Submodule.span ℤ (Set.range (mono r)) := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨S, rfl⟩ := hy
    by_cases hj : j ∈ S
    · rw [gen_mul_mono_of_mem r hj]
      convert Submodule.smul_mem (Submodule.span ℤ (Set.range (mono r))) (r j : ℤ)
        (Submodule.subset_span ⟨S.erase j, rfl⟩) using 1
      rw [zsmul_eq_mul, Int.cast_natCast]
    · rw [gen_mul_mono_of_notMem r hj]
      exact Submodule.subset_span ⟨insert j S, rfl⟩
  | zero => simp
  | add x y _ _ hx hy =>
    rw [mul_add]
    exact add_mem hx hy
  | smul a x _ hx =>
    rw [zsmul_eq_mul, mul_left_comm, ← zsmul_eq_mul]
    exact Submodule.smul_mem _ a hx

/-- Blueprint K02: the family `{mono S}` spans `𝒪_r` as a `ℤ`-module. -/
theorem mono_span (r : Fin m → ℕ) :
    Submodule.span ℤ (Set.range (mono r)) = ⊤ := by
  refine Submodule.eq_top_iff'.mpr fun x ↦ ?_
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [mk_C, ← mul_one (a : Order r), ← zsmul_eq_mul, ← mono_empty]
    exact Submodule.smul_mem _ a (Submodule.subset_span ⟨∅, rfl⟩)
  | add p q hp hq =>
    rw [map_add]
    exact add_mem hp hq
  | mul_X p j hp =>
    rw [map_mul, mul_comm]
    simpa [gen] using mul_gen_mem_span r j hp

/-- Blueprint K02: every element of `𝒪_r` is a `ℤ`-linear combination of the `mono S`. -/
theorem exists_repr (r : Fin m → ℕ) (x : Order r) :
    ∃ c : Finset (Fin m) → ℤ, x = ∑ S, (c S : Order r) * mono r S := by
  have hx : x ∈ Submodule.span ℤ (Set.range (mono r)) := by
    rw [mono_span]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ (v := mono r)).mp hx
  refine ⟨c, ?_⟩
  simpa [zsmul_eq_mul] using hc.symm

/-- Blueprint K02: product of monomials, with squares reduced via `gen_sq`. -/
theorem mono_mul_mono (r : Fin m → ℕ) (S T : Finset (Fin m)) :
    mono r S * mono r T =
      (∏ j ∈ S ∩ T, (r j : Order r)) * mono r (S ∆ T) := by
  simp only [mono_eq_prod_gen]
  rw [← prod_union_inter (s₁ := S) (s₂ := T)]
  have hunion : S ∪ T = S ∆ T ∪ S ∩ T := by
    ext x
    simp [mem_symmDiff]
    tauto
  have hdisj : Disjoint (S ∆ T) (S ∩ T) := by
    refine disjoint_left.2 fun x hx hxi ↦ ?_
    simp [mem_symmDiff] at hx
    simp at hxi
    tauto
  rw [hunion, prod_union hdisj, mul_assoc, ← sq, ← prod_pow]
  simp_rw [gen_sq]
  rw [mul_comm]

section Sign

/-- Blueprint K02: the sign `ε_S = ∏_{j ∈ S} εⱼ` of a subset. -/
def sgn (ε : Fin m → ℤˣ) (S : Finset (Fin m)) : ℤ :=
  ∏ j ∈ S, (ε j : ℤ)

/-- Blueprint K02: the trivial sign vector has `ε_S = 1`. -/
@[simp]
theorem sgn_one (S : Finset (Fin m)) : sgn (1 : Fin m → ℤˣ) S = 1 := by
  simp [sgn]

/-- Blueprint K02: signs are multiplicative in the sign vector. -/
theorem sgn_mul (ε δ : Fin m → ℤˣ) (S : Finset (Fin m)) :
    sgn (ε * δ) S = sgn ε S * sgn δ S := by
  simp [sgn, Pi.mul_apply, Units.val_mul, prod_mul_distrib]

/-- Blueprint K02: `ε_S ε_T = ε_{S ∆ T}`, since each `εⱼ² = 1`. -/
theorem sgn_mul_sgn (ε : Fin m → ℤˣ) (S T : Finset (Fin m)) :
    sgn ε S * sgn ε T = sgn ε (S ∆ T) := by
  simp only [sgn]
  rw [← prod_union_inter (s₁ := S) (s₂ := T)]
  have hunion : S ∪ T = S ∆ T ∪ S ∩ T := by
    ext x
    simp [mem_symmDiff]
    tauto
  have hdisj : Disjoint (S ∆ T) (S ∩ T) := by
    refine disjoint_left.2 fun x hx hxi ↦ ?_
    simp [mem_symmDiff] at hx
    simp at hxi
    tauto
  rw [hunion, prod_union hdisj, mul_assoc, ← sq, ← prod_pow]
  simp [pow_two, Int.units_coe_mul_self]

end Sign

/-- Two ring homs out of `𝒪_r` agree if they agree on each `gen r j` (they automatically
agree on `ℤ` by `map_intCast`). -/
lemma ringHom_ext_order {R : Type*} [CommRing R] {r : Fin m → ℕ}
    {f g : Order r →+* R} (hX : ∀ j, f (gen r j) = g (gen r j)) : f = g := by
  refine Ideal.Quotient.ringHom_ext ?_
  refine MvPolynomial.ringHom_ext ?_ ?_
  · intro z
    rw [RingHom.comp_apply, RingHom.comp_apply, mk_C, map_intCast, map_intCast]
  · intro j
    simpa [RingHom.comp_apply, gen] using hX j

/-- `((±1) * √n)² = n`. -/
lemma units_mul_sqrt_sq (ε : ℤˣ) (n : ℕ) :
    (((ε : ℤ) : ℝ) * Real.sqrt n) ^ 2 = n := by
  rw [mul_pow, Real.sq_sqrt n.cast_nonneg, sq, ← Int.cast_mul, Int.units_coe_mul_self,
    Int.cast_one, one_mul]

/-- Blueprint K02: the real embedding `σ_ε` sending `Xⱼ ↦ εⱼ √rⱼ`. -/
noncomputable def emb (r : Fin m → ℕ) (ε : Fin m → ℤˣ) : Order r →+* ℝ :=
  Ideal.Quotient.lift _ (eval₂Hom (Int.castRingHom ℝ)
      fun j => ((ε j : ℤ) : ℝ) * Real.sqrt (r j))
    (eval₂Hom_eq_zero_of_mem_relIdeal r (Int.castRingHom ℝ) _
      fun j => by simpa using units_mul_sqrt_sq (ε j) (r j))

/-- Blueprint K02: `σ_ε` sends integers to themselves. -/
@[simp]
theorem emb_intCast (r : Fin m → ℕ) (ε : Fin m → ℤˣ) (z : ℤ) : emb r ε z = z :=
  map_intCast _ _

/-- Blueprint K02: `σ_ε(gen j) = εⱼ √rⱼ`. -/
@[simp]
theorem emb_gen (r : Fin m → ℕ) (ε : Fin m → ℤˣ) (j : Fin m) :
    emb r ε (gen r j) = (ε j : ℤ) * Real.sqrt (r j) := by
  simp [emb, gen]

/-- Blueprint K02: `σ_ε(mono S) = ε_S √r_S`. -/
theorem emb_mono (r : Fin m → ℕ) (ε : Fin m → ℤˣ) (S : Finset (Fin m)) :
    emb r ε (mono r S) = sgn ε S * Real.sqrt (∏ j ∈ S, (r j : ℝ)) := by
  simp only [mono_eq_prod_gen, map_prod, emb_gen]
  rw [prod_mul_distrib, Real.sqrt_prod S fun _ _ ↦ Nat.cast_nonneg _, ← Int.cast_prod]
  rfl

/-- `((ε) * gen j)² = rⱼ` in `𝒪_r`. -/
lemma units_mul_gen_sq (r : Fin m → ℕ) (ε : ℤˣ) (j : Fin m) :
    (((ε : ℤ) : Order r) * gen r j) ^ 2 = (r j : Order r) := by
  rw [mul_pow, gen_sq]
  have : ((ε : ℤ) : Order r) ^ 2 = 1 := by
    rw [← Int.cast_pow, sq, Int.units_coe_mul_self, Int.cast_one]
  rw [this, one_mul]

/-- Blueprint K02: the conjugation `τ_ε` sending `Xⱼ ↦ εⱼ Xⱼ`. -/
def conj (r : Fin m → ℕ) (ε : Fin m → ℤˣ) : Order r →+* Order r :=
  Ideal.Quotient.lift _
    (eval₂Hom ((Ideal.Quotient.mk (relIdeal r)).comp C)
      fun j => ((ε j : ℤ) : Order r) * gen r j)
    (eval₂Hom_eq_zero_of_mem_relIdeal r ((Ideal.Quotient.mk (relIdeal r)).comp C) _
      fun j => by
        simpa [RingHom.comp_apply, mk_C, Int.cast_natCast] using units_mul_gen_sq r (ε j) j)

/-- Blueprint K02: `τ_ε(gen j) = εⱼ gen j`. -/
@[simp]
theorem conj_gen (r : Fin m → ℕ) (ε : Fin m → ℤˣ) (j : Fin m) :
    conj r ε (gen r j) = ((ε j : ℤ) : Order r) * gen r j := by
  simp [conj, gen]

/-- Blueprint K02: conjugations fix integers. -/
@[simp]
theorem conj_intCast (r : Fin m → ℕ) (ε : Fin m → ℤˣ) (z : ℤ) : conj r ε z = z :=
  map_intCast _ _

/-- Blueprint K02: `τ_ε(mono S) = ε_S · mono S`. -/
theorem conj_mono (r : Fin m → ℕ) (ε : Fin m → ℤˣ) (S : Finset (Fin m)) :
    conj r ε (mono r S) = (sgn ε S : Order r) * mono r S := by
  simp only [mono_eq_prod_gen, map_prod, conj_gen]
  rw [prod_mul_distrib, ← Int.cast_prod]
  rfl

/-- Blueprint K02: `σ_ε = σ₁ ∘ τ_ε`. -/
theorem emb_comp_conj (r : Fin m → ℕ) (ε : Fin m → ℤˣ) :
    (emb r 1).comp (conj r ε) = emb r ε := by
  refine ringHom_ext_order fun j ↦ ?_
  simp [emb_gen, conj_gen, map_mul]

/-- Blueprint K02: pointwise form of `emb_comp_conj`. -/
theorem emb_conj (r : Fin m → ℕ) (ε : Fin m → ℤˣ) (x : Order r) :
    emb r ε x = emb r 1 (conj r ε x) :=
  (RingHom.congr_fun (emb_comp_conj r ε) x).symm

/-- Blueprint K02: `τ_ε ∘ τ_δ = τ_{εδ}`. -/
theorem conj_comp_conj (r : Fin m → ℕ) (ε δ : Fin m → ℤˣ) :
    (conj r ε).comp (conj r δ) = conj r (ε * δ) := by
  refine ringHom_ext_order fun j ↦ ?_
  simp [conj_gen, map_mul, mul_assoc, Pi.mul_apply, Units.val_mul, mul_left_comm]

/-- Blueprint K02: `τ₁` is the identity. -/
@[simp]
theorem conj_one (r : Fin m → ℕ) : conj r 1 = RingHom.id (Order r) := by
  refine ringHom_ext_order fun j ↦ ?_
  simp [conj_gen]

/-- Blueprint K02: each conjugation is an involution. -/
theorem conj_conj (r : Fin m → ℕ) (ε : Fin m → ℤˣ) (x : Order r) :
    conj r ε (conj r ε x) = x := by
  have hε : ε * ε = 1 := funext fun j ↦ Int.units_mul_self (ε j)
  simpa [hε, conj_one] using RingHom.congr_fun (conj_comp_conj r ε ε) x

/-- Blueprint K02: conjugations are injective. -/
theorem conj_injective (r : Fin m → ℕ) (ε : Fin m → ℤˣ) :
    Function.Injective (conj r ε) :=
  Function.Involutive.injective (conj_conj r ε)

/-- Blueprint K02: conjugations are bijective. -/
theorem conj_bijective (r : Fin m → ℕ) (ε : Fin m → ℤˣ) :
    Function.Bijective (conj r ε) :=
  Function.Involutive.bijective (conj_conj r ε)

end

end Nikodym.MultiQuad

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
