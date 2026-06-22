/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.HeckeRIngs.AbstractHeckeRing.Ring

/-!
# Hecke Rings: Degree Map

The degree ring homomorphism `deg : 𝕋 P ℤ →+* ℤ`, which sends each
double coset `HgH` to the number of left cosets it contains:
`deg(HgH) = [H : H ∩ gHg⁻¹]`.

This is Shimura §3.1, Proposition 3.3.

## Main definitions

* `HeckeCosetDeg P D` : the degree of a single double coset
* `deg P` : the degree ring homomorphism `𝕋 P ℤ →+* ℤ`

## Main results

* `deg_T_single` : `deg(TSingle D a) = a * HeckeCosetDeg D`
* `HeckeCoset_deg_pos` : `0 < HeckeCosetDeg D`
* `deg_one` : `deg 1 = 1`

## Proof strategy

Multiplicativity `deg(f * g) = deg(f) * deg(g)` is proved using the module action on
`HeckeModule P ℤ`.
We show `deg(f) = coeffSum(f • 1)` where `coeffSum` sums all coefficients, and then use
`IsScalarTower` (Shimura Prop 3.4) to get `(f * g) • 1 = g • (f • 1)`. The key intermediate
result is `coeffSum(f • m) = deg(f) * coeffSum(m)`, which follows from the orbit cardinality
lemma `smulOrbit_card`.
-/

open MulOpposite Set DoubleCoset Subgroup Subgroup.Commensurable

open scoped Pointwise

namespace HeckeRing

variable {G : Type*} [Group G]
variable (P : HeckePair G)

open Finsupp

/-- The degree of a double coset: `deg(HgH) = [H : H ∩ gHg⁻¹]`, the number of left cosets
in the decomposition of `HgH`. -/
noncomputable def HeckeCosetDeg (D : HeckeCoset P) : ℤ :=
  Fintype.card (decompQuot P (HeckeCoset.rep D))

/-- The degree of the identity double coset is 1. -/
@[simp] lemma HeckeCoset_deg_T_one : HeckeCosetDeg P (HeckeCoset.one P) = 1 := by
  simp only [HeckeCosetDeg]; haveI := subsingleton_decompQuot_T_one P
  haveI : Unique (decompQuot P (HeckeCoset.one P).rep) :=
    uniqueOfSubsingleton (one_in_decompQuot_T_one P).some
  simp [Fintype.card_unique]

/-- Every double coset has positive degree. -/
lemma HeckeCoset_deg_pos (D : HeckeCoset P) : 0 < HeckeCosetDeg P D := by
  simp only [HeckeCosetDeg]; exact_mod_cast Fintype.card_pos

section SmulOrbitCard

private lemma smulOrbit_map_inj (g : P.Δ) (β : P.Δ) :
    Function.Injective (fun i : decompQuot P g =>
      (⟦⟨(β : G) * (i.out : G) * (g : G),
        delta_mul_mem P.H P.Δ i.out β g P.h₀⟩⟧ : HeckeLeftCoset P)) := by
  intro i₁ i₂ heq
  by_contra hne
  have hset : ({(β : G) * (i₁.out : G) *
      (g : G)} : Set G) * (P.H : Set G) =
    {(β : G) * (i₂.out : G) *
      (g : G)} * P.H := Quotient.exact heq
  have hmem : (β : G) * (i₁.out : G) * (g : G) ∈
      ({(β : G) * (i₂.out : G) * (g : G)} : Set G) *
      (P.H : Set G) := by
    rw [← hset]; exact ⟨_, rfl, 1, P.H.one_mem, mul_one _⟩
  obtain ⟨_, ha, k, hk, hkk⟩ := hmem
  rw [Set.mem_singleton_iff] at ha; subst ha
  have cancel : (i₂.out : G) * (g : G) * k =
      (i₁.out : G) * (g : G) := by
    apply mul_left_cancel (a := (β : G))
    have := hkk; group at this ⊢; exact this
  exact decompQuot_coset_diff P g i₁ i₂ hne
    (leftCoset_eq_of_not_disjoint (H := P.H) _ _ (by
      rw [@not_disjoint_iff]
      exact ⟨(i₁.out : G) * (g : G),
        ⟨1, P.H.one_mem, mul_one _⟩,
        ⟨k, hk, cancel⟩⟩))

/-- The cardinality of a smul orbit equals the degree of the acting double coset. -/
lemma smulOrbit_card (g : P.Δ) (β : P.Δ) :
    (smulOrbit P g β).card = Fintype.card (decompQuot P g) := by
  classical
  have hinj := smulOrbit_map_inj P g β
  change (Finset.image _ ⊤).card = _
  rw [Finset.top_eq_univ]
  convert (Finset.card_image_of_injective Finset.univ hinj).trans Finset.card_univ using 2
  · rfl
  · apply heq_of_eq
    congr 1
    exact Subsingleton.elim _ _

/-- The cardinality of a smul orbit cast to `ℤ` equals `HeckeCosetDeg`. -/
lemma smulOrbit_card_intCast (D : HeckeCoset P) (β : P.Δ) :
    ((smulOrbit P (HeckeCoset.rep D) β).card : ℤ) = HeckeCosetDeg P D := by
  simp [smulOrbit_card, HeckeCosetDeg]

end SmulOrbitCard

section CoeffSum

/-- The coefficient sum homomorphism: sums all coefficients of a formal linear combination
of left cosets. -/
noncomputable def coeffSum : HeckeModule P ℤ →+ ℤ :=
  Finsupp.liftAddHom (fun _ : HeckeLeftCoset P => AddMonoidHom.id ℤ)

/-- The coefficient sum of a single basis element is its coefficient. -/
@[simp] lemma coeffSum_single (m₀ : HeckeLeftCoset P) (b : ℤ) :
    coeffSum P (HeckeLeftCosetSingle P ℤ m₀ b) = b := Finsupp.liftAddHom_apply_single _ _ _

/-- The coefficient sum of zero is zero. -/
lemma coeffSum_zero : coeffSum P (0 : HeckeModule P ℤ) = 0 := map_zero _

/-- The coefficient sum is additive. -/
lemma coeffSum_add (m₁ m₂ : HeckeModule P ℤ) :
    coeffSum P (m₁ + m₂) = coeffSum P m₁ + coeffSum P m₂ := map_add _ _ _

/-- The coefficient sum distributes over finite sums. -/
lemma coeffSum_finset_sum {ι : Type*} (s : Finset ι) (f : ι → HeckeModule P ℤ) :
    coeffSum P (∑ i ∈ s, f i) = ∑ i ∈ s, coeffSum P (f i) := map_sum _ _ _

/-- The coefficient sum of a single-single smul product equals `a * deg(D) * b`. -/
lemma coeffSum_single_smul_single (D : HeckeCoset P) (m₀ : HeckeLeftCoset P) (a b : ℤ) :
    coeffSum P (TSingle P ℤ D a • HeckeLeftCosetSingle P ℤ m₀ b) =
    a * HeckeCosetDeg P D * b := by
  rw [T_single_smul_HeckeLeftCoset_single, coeffSum_finset_sum]
  simp only [coeffSum_single, Finset.sum_const, Int.nsmul_eq_mul,
    smulOrbit_card_intCast P D (HeckeLeftCoset.rep m₀)]; ring

end CoeffSum

section DegreeMap

/-- The underlying function of the degree map: `Σ_D a_D * deg(D)`. -/
noncomputable def degFun (f : 𝕋 P ℤ) : ℤ := f.sum fun D a => a * HeckeCosetDeg P D

/-- The degree function of zero is zero. -/
@[simp] lemma deg_fun_zero : degFun P (0 : 𝕋 P ℤ) = 0 := Finsupp.sum_zero_index

/-- The degree function of a basis element is `a * deg(D)`. -/
@[simp] lemma deg_fun_T_single (D : HeckeCoset P) (a : ℤ) :
    degFun P (TSingle P ℤ D a) = a * HeckeCosetDeg P D :=
  Finsupp.sum_single_index (by simp)

/-- The degree function is additive. -/
lemma deg_fun_add (f g : 𝕋 P ℤ) :
    degFun P (f + g) = degFun P f + degFun P g :=
  Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by ring)

/-- The degree function of the identity is 1. -/
@[simp] lemma deg_fun_one : degFun P (1 : 𝕋 P ℤ) = 1 := by
  rw [one_def, deg_fun_T_single, HeckeCoset_deg_T_one, mul_one]

/-- The degree equals the coefficient sum of the action on the identity module element. -/
lemma deg_fun_eq_coeffSum_smul_one (f : 𝕋 P ℤ) :
    degFun P f = coeffSum P (f • (1 : HeckeModule P ℤ)) := by
  induction f using Finsupp.induction_linear with
  | zero => simp [zero_smul_HeckeModule]
  | add f g ihf ihg => rw [deg_fun_add, ihf, ihg, smul_add_left, coeffSum_add]
  | single D a =>
    rw [deg_fun_T_single, one_eq_HeckeLeftCoset_single, coeffSum_single_smul_single, mul_one]

/-- The coefficient sum of a smul product factors as `deg(f) * coeffSum(m)`. -/
lemma coeffSum_smul_eq (f : 𝕋 P ℤ) (m : HeckeModule P ℤ) :
    coeffSum P (f • m) = degFun P f * coeffSum P m := by
  induction f using Finsupp.induction_linear with
  | zero => simp [zero_smul_HeckeModule]
  | add f₁ f₂ ih₁ ih₂ =>
    rw [smul_add_left, coeffSum_add, ih₁, ih₂, deg_fun_add]; ring
  | single D a =>
    induction m using Finsupp.induction_linear with
    | zero => simp [smul_zero_HeckeModule]
    | add m₁ m₂ ih₁ ih₂ =>
      rw [smul_add_right, coeffSum_add, ih₁, ih₂, coeffSum_add,
        deg_fun_T_single]; ring
    | single m₀ b =>
      rw [coeffSum_single_smul_single, coeffSum_single, deg_fun_T_single]

/-- The degree function is multiplicative. -/
lemma deg_fun_mul (f g : 𝕋 P ℤ) :
    degFun P (f * g) = degFun P f * degFun P g := by
  have h := (instIsScalarTower P).smul_assoc g f (1 : HeckeModule P ℤ)
  simp only [smul_def] at h
  rw [deg_fun_eq_coeffSum_smul_one P (f * g), h, coeffSum_smul_eq,
    ← deg_fun_eq_coeffSum_smul_one P f]; ring

/-- The degree ring homomorphism `deg : 𝕋 P ℤ →+* ℤ`, sending each double coset to the
number of left cosets it contains (Shimura Proposition 3.3). -/
noncomputable def deg : 𝕋 P ℤ →+* ℤ where
  toFun := degFun P
  map_zero' := deg_fun_zero P
  map_one' := deg_fun_one P
  map_add' := deg_fun_add P
  map_mul' := deg_fun_mul P

end DegreeMap

section API

/-- The degree of a basis element is the coefficient times the degree of the double coset. -/
@[simp] lemma deg_T_single (D : HeckeCoset P) (a : ℤ) :
    deg P (TSingle P ℤ D a) = a * HeckeCosetDeg P D := deg_fun_T_single P D a

/-- The degree of the identity element is 1. -/
@[simp] lemma deg_one_val : deg P (1 : 𝕋 P ℤ) = 1 := (deg P).map_one

/-- The degree map is multiplicative: `deg(f * g) = deg(f) * deg(g)`. -/
lemma deg_mul (f g : 𝕋 P ℤ) :
    deg P (f * g) = deg P f * deg P g := (deg P).map_mul f g

/-- The degree map is additive: `deg(f + g) = deg(f) + deg(g)`. -/
lemma deg_add (f g : 𝕋 P ℤ) :
    deg P (f + g) = deg P f + deg P g := (deg P).map_add f g

/-- The degree of an integer cast is the integer itself. -/
lemma deg_intCast (n : ℤ) : deg P (n : 𝕋 P ℤ) = n := by
  simp [deg, degFun, HeckeCoset_deg_T_one]

end API

end HeckeRing
