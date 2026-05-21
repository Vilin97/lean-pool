/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.SampCert.SLang
import LeanPool.HopfieldNet.SampCert.DifferentialPrivacy.Sensitivity
import LeanPool.HopfieldNet.SampCert.Foundations.Basic

/-!
# Differential Privacy

This file defines an abstract system of differentially private operators.
-/

noncomputable section

open Classical Nat Int Real ENNReal

namespace SLang

abbrev Query (T U : Type) := List T → U

abbrev Mechanism (T U : Type) := List T → PMF U

/--
General (value-dependent) composition of mechanisms
-/
def privComposeAdaptive (nq1 : Mechanism T U) (nq2 : U -> Mechanism T V) (l : List T) : PMF (U × V) := do
  let A <- nq1 l
  let B <- nq2 A l
  return (A, B)

lemma compose_sum_rw_adaptive (nq1 : List T → PMF U) (nq2 : U -> List T → PMF V) (u : U) (v : V) (l : List T) :
  (∑' (a : U), nq1 l a * ∑' (a_1 : V), if u = a ∧ v = a_1 then nq2 a l a_1 else 0) = nq1 l u * nq2 u l v := by
  have hrw1 : ∀ (a : U), nq1 l a * (∑' (a_1 : V), if u = a ∧ v = a_1 then nq2 a l a_1 else 0) = if (u = a) then (nq1 l a * ∑' (a_1 : V), if u = a ∧ v = a_1 then nq2 a l a_1 else 0) else 0 := by
    intro a
    split
    · simp
    · aesop
  have hrw2 : ∀ (a : U), (if (u = a) then (nq1 l a * ∑' (a_1 : V), if u = a ∧ v = a_1 then nq2 a l a_1 else 0) else 0) = (nq1 l u * (∑' (a_1 : V), if u = a ∧ v = a_1 then nq2 u l a_1 else 0)) := by
    intro a
    split
    · aesop
    · aesop
  rw [tsum_congr hrw1]
  rw [tsum_congr hrw2]
  clear hrw1 hrw2
  rw [ENNReal.tsum_mul_left]
  congr 1
  rw [<- ENNReal.tsum_prod]
  have hrw3 : ∀ (p : U × V), (if u = p.1 ∧ v = p.2 then nq2 u l p.2 else 0) = nq2 u l v * (if p = (u, v) then 1 else 0) := by
    intro p
    split
    · aesop
    · aesop
  rw [tsum_congr hrw3]
  rw [ENNReal.tsum_mul_left]
  rw [tsum_ite_eq]
  exact MulOneClass.mul_one (nq2 u l v)


/--
Chain rule relating the adaptive composition definitions

The joint distribution decomposes into the conditional and marginal (ie, nq1 l) distributions
-/
lemma privComposeChainRule (nq1 : Mechanism T U) (nq2 : U -> Mechanism T V) (l : List T) :
  ∀ (u : U), ∀ (v : V), privComposeAdaptive nq1 nq2 l (u, v) = nq1 l u * nq2 u l v := by
  intros u v
  rw [<- compose_sum_rw_adaptive]
  simp [privComposeAdaptive]

/--
Product of mechanisms.
-/
def privCompose (nq1 : Mechanism T U) (nq2 : Mechanism T V) (l : List T) : PMF (U × V) :=
  privComposeAdaptive nq1 (fun _ => nq2) l

/--
Mechanism obtained by applying a post-processing function to a mechanism.
-/
def privPostProcess (nq : Mechanism T U) (pp : U → V) (l : List T) : PMF V := do
  let A ← nq l
  return pp A

/--
Constant mechanism
-/
def privConst (u : U) : Mechanism T U := fun _ => PMF.pure u


-- @[simp]
-- lemma bind_bind_indep (p : Mechanism T U) (q : Mechanism T V) (h : U → V → PMF A) :
--     (fun l => (p l) >>= (fun a : U => (q l) >>= fun b : V => h a b)) =
--     fun l => (privCompose p q l) >>= (fun z => h z.1 z.2) := by
--   ext l x
--   simp [privCompose, tsum_prod']
--
lemma compose_sum_rw (nq1 : U -> ENNReal) (nq2 : V -> ENNReal) (b : U) (c : V) :
  (∑' (a : U), nq1 a * ∑' (a_1 : V), if b = a ∧ c = a_1 then nq2 a_1 else 0) = nq1 b * nq2 c := by
  have A : ∀ a : U, ∀ b : U, (∑' (a_1 : V), if b = a ∧ c = a_1 then nq2 a_1 else 0) = if b = a then (∑' (a_1 : V), if c = a_1 then nq2 a_1 else 0) else 0 := by
    intro x  y
    split
    · rename_i h
      subst h
      simp
    · rename_i h
      simp
      intro h
      contradiction
  conv =>
    left
    right
    intro a
    right
    rw [A]
  rw [ENNReal.tsum_eq_add_tsum_ite b]
  simp
  have B : ∀ x : U, (if x = b then 0 else if b = x then nq1 x * ∑' (a_1 : V), if c = a_1 then nq2 a_1 else 0 else 0) = 0 := by
    intro x
    split
    · simp
    · split
      · rename_i h1 h2
        subst h2
        contradiction
      · simp
  conv =>
    left
    right
    right
    intro x
    rw [B]
  simp
  congr 1
  rw [ENNReal.tsum_eq_add_tsum_ite c]
  simp
  have C :∀ x : V,  (if x = c then 0 else if c = x then nq2 x else 0) = 0 := by
    intro x
    split
    · simp
    · split
      · rename_i h1 h2
        subst h2
        contradiction
      · simp
  conv =>
    left
    right
    right
    intro X
    rw [C]
  simp


/--
Partition series into fibers. `g` maps an element to its fiber.
-/
theorem ENNReal.HasSum_fiberwise {f : T → ENNReal} {a : ENNReal} (hf : HasSum f a) (g : T → V) :
    HasSum (fun c : V ↦ ∑' b : g ⁻¹' {c}, f b) a := by
  let A := (Equiv.sigmaFiberEquiv g)
  have B := @Equiv.hasSum_iff ENNReal T ((y : V) × { x // g x = y }) _ _ f a A
  replace B := B.2 hf
  have C := @HasSum.sigma ENNReal V _ _ _ _ (fun y : V => { x // g x = y }) (f ∘ ⇑(Equiv.sigmaFiberEquiv g)) (fun c => ∑' (b : ↑(g ⁻¹' {c})), f ↑b) a B
  apply C
  intro b
  have F := @Summable.hasSum_iff ENNReal _ _ _ (fun c => (f ∘ ⇑(Equiv.sigmaFiberEquiv g)) { fst := b, snd := c }) ((fun c => ∑' (b : ↑(g ⁻¹' {c})), f ↑b) b) _
  apply (F _).2
  · rfl
  · apply ENNReal.summable

/--
Partition series into fibers. `g` maps an element to its fiber.
-/
theorem ENNReal.tsum_fiberwise (p : T → ENNReal) (f : T → V) :
  ∑' (x : V), ∑' (b : (f ⁻¹' {x})), p b
    = ∑' i : T, p i := by
  apply HasSum.tsum_eq
  apply ENNReal.HasSum_fiberwise
  apply Summable.hasSum
  exact ENNReal.summable

/--
Rewrite a series into a sum over fibers. `f` maps an element into its fiber.
-/
theorem fiberwisation (p : T → ENNReal) (f : T → V) :
 (∑' i : T, p i)
    = ∑' (x : V), if {a : T | x = f a} = {} then 0 else ∑'(i : {a : T | x = f a}), p i := by
  rw [← ENNReal.tsum_fiberwise p f]
  have A : ∀ x, f ⁻¹' {x} = { a | x = f a } := by
    intro x
    simp [Set.preimage]
    rw [Set.ext_iff]
    simp
    intro y
    exact eq_comm
  conv =>
    left
    right
    intro x
    rw [A]
  clear A
  apply tsum_congr
  intro b
  split
  · rename_i h'
    rw [h']
    simp only [tsum_empty]
  · simp

lemma condition_to_subset (f : U → V) (g : U → ENNReal) (x : V) :
  (∑' a : U, if x = f a then g a else 0) = ∑' a : { a | x = f a }, g a := by
  have A := @tsum_split_ite U (fun a : U => x = f a) g (fun _ => 0)
  simp only [decide_eq_true_eq, tsum_zero, add_zero] at A
  rw [A]
  have B : ↑{i | decide (x = f i) = true} = ↑{a | x = f a} := by
    simp
  rw [B]

end SLang
