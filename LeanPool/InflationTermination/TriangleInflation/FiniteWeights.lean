/-
Copyright (c) 2026 William Blair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Blair
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Tactic.Ring

/-!
# Finite weights over a commutative semiring

Finite sums, coordinate products, pushforwards, and independence of disjoint coordinate
blocks share the same algebra for real and complex weights. These lemmas require neither
positivity nor additive inverses. The original real and complex APIs specialize this
common toolkit while retaining their existing weight definitions.
-/

@[expose] public section

namespace TriangleInflation.FiniteWeights

open Finset

variable {R : Type*} [CommSemiring R]

/-- Pushforward sums a finite weight over each fibre of a map. -/
def pushforward {α β : Type*} [Fintype α] [DecidableEq β] (w : α → R) (F : α → β) : β → R :=
  fun b => ∑ a : α, if F a = b then w a else 0

/-- The product of the weights of a Boolean coordinate configuration. -/
def prodLaw {ι : Type*} [Fintype ι] (w : ι → Bool → R) : (ι → Bool) → R :=
  fun x => ∏ i, w i (x i)

section Generic

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- A sum over all configurations of a dependent product factorizes. -/
theorem sum_pi_prod {A : κ → Type*} [∀ k, Fintype (A k)] (f : ∀ k, A k → R) :
    (∑ x : (k : κ) → A k, ∏ k, f k (x k)) = ∏ k, ∑ a, f k a := by
  have h := Finset.prod_univ_sum (fun k => (univ : Finset (A k))) f
  rw [Fintype.piFinset_univ] at h
  exact h.symm

omit [DecidableEq κ] in
/-- The indicator of an equality of configurations is a product of coordinate indicators. -/
theorem ite_funext_prod {B : κ → Type*} [∀ k, DecidableEq (B k)] (f g : ∀ k, B k) :
    (if f = g then (1 : R) else 0) = ∏ k, (if f k = g k then (1 : R) else 0) := by
  by_cases h : f = g
  · subst h; simp
  · rw [ite_eq_right h]
    obtain ⟨k, hk⟩ := Function.ne_iff.mp h
    exact (Finset.prod_eq_zero (mem_univ k) (ite_eq_right hk)).symm

/-- A dependent product weight pushed forward along a coordinatewise map. -/
theorem sum_dprod_sel {A B : κ → Type*} [∀ k, Fintype (A k)] [∀ k, DecidableEq (B k)]
    (W : ∀ k, A k → R) (sel : ∀ k, A k → B k) (y : ∀ k, B k) :
    (∑ x : (k : κ) → A k, (if (fun k => sel k (x k)) = y then (1 : R) else 0) * ∏ k, W k (x k))
      = ∏ k, ∑ a, (if sel k a = y k then (1 : R) else 0) * W k a := by
  rw [← sum_pi_prod (fun k a => (if sel k a = y k then (1 : R) else 0) * W k a)]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [ite_funext_prod (fun k => sel k (x k)) y, Finset.prod_mul_distrib]

end Generic

/-- A normalized independent family has its original weight at each selected coordinate. -/
theorem sum_sel_coord {B : Type*} [Fintype B] [DecidableEq B] {n : Type*} [Fintype n]
    [DecidableEq n] (ρ : B → R) (hρ : ∑ b, ρ b = 1) (r₀ : n) (b₀ : B) :
    ∑ v : n → B, (if v r₀ = b₀ then (1 : R) else 0) * ∏ r, ρ (v r) = ρ b₀ := by
  have hstep : ∀ v : n → B, (if v r₀ = b₀ then (1 : R) else 0) * ∏ r, ρ (v r)
      = ∏ r, (ρ (v r) * if r = r₀ then (if v r = b₀ then (1 : R) else 0) else 1) := by
    intro v
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' univ r₀
      (fun r => if v r = b₀ then (1 : R) else 0)]
    simp [mul_comm]
  rw [Finset.sum_congr rfl (fun v _ => hstep v),
    sum_pi_prod (fun (r : n) (b : B) =>
      ρ b * if r = r₀ then (if b = b₀ then (1 : R) else 0) else 1)]
  have hcol : ∀ r : n, (∑ b, ρ b * if r = r₀ then (if b = b₀ then (1 : R) else 0) else 1)
      = if r = r₀ then ρ b₀ else 1 := by
    intro r
    by_cases hr : r = r₀
    · simp only [hr, ite_true]
      rw [Finset.sum_eq_single b₀]
      · simp
      · exact fun b _ hb => by rw [ite_eq_right hb, mul_zero]
      · intro h; exact absurd (mem_univ _) h
    · simp only [hr, ite_false, mul_one]; exact hρ
  rw [Finset.prod_congr rfl (fun r _ => hcol r), Finset.prod_ite_eq' univ r₀ (fun _ => ρ b₀)]
  simp

section Push

variable {α β γ : Type*} [Fintype α] [Fintype β] [DecidableEq β] [DecidableEq γ]

/-- Integrating against a pushforward is integrating the pullback. -/
theorem sum_mul_comp (w : α → R) (F : α → β) (G : β → R) :
    ∑ a, w a * G (F a) = ∑ b, pushforward w F b * G b := by
  simp only [pushforward, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single (F a)]
  · simp
  · exact fun b _ hb => by rw [ite_eq_right (Ne.symm hb), zero_mul]
  · intro h; exact absurd (mem_univ (F a)) h

omit [Fintype β] in
/-- Postcomposing the read map with a bijection transports the pushforward. -/
theorem pushforward_comp_equiv (w : α → R) (F : α → β) (E : β ≃ γ) :
    pushforward w (fun a => E (F a)) = fun c => pushforward w F (E.symm c) := by
  funext c
  simp only [pushforward, ← Equiv.eq_symm_apply]

omit [Fintype β] in
/-- Pushing forward a finite mixture. -/
theorem pushforward_mix {ι : Type*} [Fintype ι] (c : ι → R) (ν : ι → α → R) (F : α → β) :
    pushforward (fun a => ∑ i, c i * ν i a) F = fun b => ∑ i, c i * pushforward (ν i) F b := by
  funext b
  simp only [pushforward, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : F a = b <;> simp [h]

end Push

/-! ## Marginals of a product law along an injective selection -/

/-- The marginal of a product weight on an injectively selected set of coordinates is the
product weight of the selected coordinates. -/
theorem pushforward_prodLaw_sel {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
     {w : ι → Bool → R} (hw : ∀ i, ∑ b, w i b = 1) {ν : κ → ι}
    (hν : Function.Injective ν) :
    pushforward (prodLaw w) (fun x k => x (ν k)) = prodLaw (fun k => w (ν k)) := by
  classical
  funext c
  set c' : ι → Bool := fun i => if h : ∃ k, ν k = i then c h.choose else false with hc'
  have hc'ν : ∀ k, c' (ν k) = c k := by
    intro k
    have hex : ∃ k', ν k' = ν k := ⟨k, rfl⟩
    have hb : c' (ν k) = if h : ∃ k', ν k' = ν k then c h.choose else false := rfl
    rw [hb, dite_eq_left hex]
    exact congrArg c (hν hex.choose_spec)
  set I : Finset ι := univ.image ν with hI
  have hind : ∀ x : ι → Bool,
      (if (fun k => x (ν k)) = c then (1 : R) else 0)
        = ∏ i ∈ I, (if x i = c' i then (1 : R) else 0) := by
    intro x
    rw [hI, Finset.prod_image (fun a _ b _ h => hν h)]
    rw [ite_funext_prod (fun k => x (ν k)) c]
    exact Finset.prod_congr rfl fun k _ => by rw [hc'ν k]
  have hstep : ∀ x : ι → Bool,
      (if (fun k => x (ν k)) = c then prodLaw w x else 0)
        = ∏ i, (w i (x i) * (if i ∈ I then (if x i = c' i then (1 : R) else 0) else 1)) := by
    intro x
    rw [Finset.prod_mul_distrib, Finset.prod_ite_mem, Finset.univ_inter, ← hind x]
    by_cases h : (fun k => x (ν k)) = c
    · rw [ite_eq_left h, ite_eq_left h, mul_one]; rfl
    · rw [ite_eq_right h, ite_eq_right h, mul_zero]
  simp only [pushforward]
  rw [Finset.sum_congr rfl (fun x _ => hstep x),
    sum_pi_prod (fun (i : ι) (b : Bool) =>
      w i b * (if i ∈ I then (if b = c' i then (1 : R) else 0) else 1))]
  have hsum : ∀ i : ι, (∑ b, w i b * (if i ∈ I then (if b = c' i then (1 : R) else 0) else 1))
      = if i ∈ I then w i (c' i) else 1 := by
    intro i
    by_cases hi : i ∈ I
    · simp only [hi, ite_true]
      rw [Finset.sum_eq_single (c' i)]
      · simp
      · exact fun b _ hb => by rw [ite_eq_right hb, mul_zero]
      · intro h; exact absurd (mem_univ _) h
    · simp only [hi, ite_false, mul_one]
      exact hw i
  rw [Finset.prod_congr rfl (fun i _ => hsum i), Finset.prod_ite_mem, Finset.univ_inter, hI,
    Finset.prod_image (fun a _ b _ h => hν h)]
  exact Finset.prod_congr rfl fun k _ => by rw [hc'ν k]


/-! ## Independence of functions of disjoint coordinate blocks, dependent fibres -/

section DProd

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*} [∀ i, Fintype (A i)]
variable {w : ∀ i, A i → R}

/-- The product weight of independent coordinates with dependent alphabets. -/
def dprod (w : ∀ i, A i → R) (x : ∀ i, A i) : R := ∏ i, w i (x i)

/-- A product of normalized coordinate weights has total mass one. -/
theorem sum_dprod (hw : ∀ i, ∑ a, w i a = 1) : ∑ x : (∀ i, A i), dprod w x = 1 := by
  rw [show (∑ x : (∀ i, A i), dprod w x) = ∏ i, ∑ a, w i a from sum_pi_prod _]
  exact Finset.prod_eq_one fun i _ => hw i

/-- `dmix I x y` takes its `I`-coordinates from `x` and the others from `y`. -/
def dmix (I : Finset ι) (x y : ∀ i, A i) : ∀ i, A i := fun i => if i ∈ I then x i else y i

omit [Fintype ι] [∀ i, Fintype (A i)] in
/-- Mixing retains the first configuration on a selected coordinate. -/
theorem dmix_mem {I : Finset ι} {x y : ∀ i, A i} {i : ι} (hi : i ∈ I) : dmix I x y i = x i := by
  simp [dmix, hi]

omit [Fintype ι] [∀ i, Fintype (A i)] in
/-- Mixing retains the second configuration outside the selected coordinates. -/
theorem dmix_not_mem {I : Finset ι} {x y : ∀ i, A i} {i : ι} (hi : i ∉ I) :
    dmix I x y i = y i := by simp [dmix, hi]

omit [∀ i, Fintype (A i)] in
/-- Swapping selected coordinates between two configurations preserves their combined weight. -/
theorem dprod_dmix_mul (I : Finset ι) (x y : ∀ i, A i) :
    dprod w (dmix I x y) * dprod w (dmix I y x) = dprod w x * dprod w y := by
  simp only [dprod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hi : i ∈ I
  · rw [dmix_mem hi, dmix_mem hi]
  · rw [dmix_not_mem hi, dmix_not_mem hi, mul_comm]

/-- Functions of disjoint coordinate blocks are uncorrelated under a product weight. -/
theorem sum_dprod_mul_mul (hw : ∀ i, ∑ a, w i a = 1) {I J : Finset ι} (hIJ : Disjoint I J)
    {φ ψ : (∀ i, A i) → R}
    (hφ : ∀ x y, (∀ i ∈ I, x i = y i) → φ x = φ y)
    (hψ : ∀ x y, (∀ i ∈ J, x i = y i) → ψ x = ψ y) :
    ∑ x, dprod w x * (φ x * ψ x) = (∑ x, dprod w x * φ x) * (∑ x, dprod w x * ψ x) := by
  classical
  set T : ((∀ i, A i) × (∀ i, A i)) → ((∀ i, A i) × (∀ i, A i)) :=
    fun q => (dmix I q.1 q.2, dmix I q.2 q.1) with hTdef
  have hTT : Function.LeftInverse T T := by
    intro q
    have h1 : dmix I (dmix I q.1 q.2) (dmix I q.2 q.1) = q.1 := by
      funext i
      by_cases hi : i ∈ I
      · rw [dmix_mem hi, dmix_mem hi]
      · rw [dmix_not_mem hi, dmix_not_mem hi]
    have h2 : dmix I (dmix I q.2 q.1) (dmix I q.1 q.2) = q.2 := by
      funext i
      by_cases hi : i ∈ I
      · rw [dmix_mem hi, dmix_mem hi]
      · rw [dmix_not_mem hi, dmix_not_mem hi]
    simp only [hTdef]
    exact Prod.ext h1 h2
  let e : ((∀ i, A i) × (∀ i, A i)) ≃ ((∀ i, A i) × (∀ i, A i)) := ⟨T, T, hTT, hTT⟩
  have hstep : ∀ q : ((∀ i, A i) × (∀ i, A i)),
      (dprod w q.1 * φ q.1) * (dprod w q.2 * ψ q.2)
        = (dprod w (e q).1 * (φ (e q).1 * ψ (e q).1)) * dprod w (e q).2 := by
    intro q
    have hφm : φ (dmix I q.1 q.2) = φ q.1 := hφ _ _ fun i hi => dmix_mem hi
    have hψm : ψ (dmix I q.1 q.2) = ψ q.2 :=
      hψ _ _ fun i hi => dmix_not_mem (Finset.disjoint_right.mp hIJ hi)
    have hp := dprod_dmix_mul (w := w) I q.1 q.2
    change (dprod w q.1 * φ q.1) * (dprod w q.2 * ψ q.2)
      = (dprod w (dmix I q.1 q.2) * (φ (dmix I q.1 q.2) * ψ (dmix I q.1 q.2)))
          * dprod w (dmix I q.2 q.1)
    rw [hφm, hψm]
    calc (dprod w q.1 * φ q.1) * (dprod w q.2 * ψ q.2)
        = (dprod w q.1 * dprod w q.2) * (φ q.1 * ψ q.2) := by ring
      _ = (dprod w (dmix I q.1 q.2) * dprod w (dmix I q.2 q.1)) * (φ q.1 * ψ q.2) := by rw [hp]
      _ = (dprod w (dmix I q.1 q.2) * (φ q.1 * ψ q.2)) * dprod w (dmix I q.2 q.1) := by ring
  have hsum := Fintype.sum_equiv e
    (fun q : ((∀ i, A i) × (∀ i, A i)) => (dprod w q.1 * φ q.1) * (dprod w q.2 * ψ q.2))
    (fun q : ((∀ i, A i) × (∀ i, A i)) => (dprod w q.1 * (φ q.1 * ψ q.1)) * dprod w q.2) hstep
  have e1 : (∑ x, dprod w x * φ x) * (∑ x, dprod w x * ψ x)
      = ∑ q : ((∀ i, A i) × (∀ i, A i)), (dprod w q.1 * φ q.1) * (dprod w q.2 * ψ q.2) := by
    simp only [Fintype.sum_prod_type]
    exact Finset.sum_mul_sum _ _ _ _
  have e2 : (∑ x, dprod w x * (φ x * ψ x)) * (∑ x, dprod w x)
      = ∑ q : ((∀ i, A i) × (∀ i, A i)), (dprod w q.1 * (φ q.1 * ψ q.1)) * dprod w q.2 := by
    simp only [Fintype.sum_prod_type]
    exact Finset.sum_mul_sum _ _ _ _
  rw [e1, hsum, ← e2, sum_dprod hw, mul_one]

/-- Functions of pairwise disjoint coordinate blocks have a product expectation. -/
theorem sum_dprod_prod (hw : ∀ i, ∑ a, w i a = 1) :
    ∀ {n : ℕ} (I : Fin n → Finset ι) (χ : Fin n → (∀ i, A i) → R),
      (∀ m m', m ≠ m' → Disjoint (I m) (I m')) →
      (∀ m x y, (∀ i ∈ I m, x i = y i) → χ m x = χ m y) →
      ∑ x, dprod w x * ∏ m, χ m x = ∏ m, ∑ x, dprod w x * χ m x := by
  intro n
  induction n with
  | zero => intro I χ _ _; simp [sum_dprod hw]
  | succ n ih =>
      intro I χ hI hχ
      have hsplit : ∀ x : ∀ i, A i,
          (∏ m : Fin (n + 1), χ m x) = χ 0 x * ∏ m : Fin n, χ m.succ x :=
        fun x => Fin.prod_univ_succ (fun m => χ m x)
      have hdisj : Disjoint (I 0) (univ.biUnion fun m : Fin n => I m.succ) := by
        rw [Finset.disjoint_biUnion_right]
        intro m _
        exact hI 0 m.succ (Ne.symm (Fin.succ_ne_zero m))
      have hdep : ∀ x y : ∀ i, A i,
          (∀ i ∈ univ.biUnion fun m : Fin n => I m.succ, x i = y i) →
            (∏ m : Fin n, χ m.succ x) = ∏ m : Fin n, χ m.succ y := by
        intro x y hxy
        refine Finset.prod_congr rfl fun m _ => ?_
        exact hχ m.succ x y fun i hi => hxy i (mem_biUnion.mpr ⟨m, mem_univ m, hi⟩)
      have key := sum_dprod_mul_mul hw hdisj (φ := χ 0)
        (ψ := fun x => ∏ m : Fin n, χ m.succ x) (hχ 0) hdep
      have hrest := ih (fun m : Fin n => I m.succ) (fun m : Fin n => χ m.succ)
        (fun m m' hm => hI m.succ m'.succ fun hc => hm (Fin.succ_injective n hc))
        (fun m => hχ m.succ)
      calc ∑ x, dprod w x * ∏ m : Fin (n + 1), χ m x
          = ∑ x, dprod w x * (χ 0 x * ∏ m : Fin n, χ m.succ x) := by
            exact Finset.sum_congr rfl fun x _ => by rw [hsplit x]
        _ = (∑ x, dprod w x * χ 0 x) * ∑ x, dprod w x * ∏ m : Fin n, χ m.succ x := key
        _ = (∑ x, dprod w x * χ 0 x) * ∏ m : Fin n, ∑ x, dprod w x * χ m.succ x := by rw [hrest]
        _ = ∏ m : Fin (n + 1), ∑ x, dprod w x * χ m x :=
            (Fin.prod_univ_succ (fun m => ∑ x, dprod w x * χ m x)).symm

end DProd

/-- Successive pushforwards equal the pushforward along the composite map. -/
theorem pushforward_comp {α β γ : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    [DecidableEq γ] (w : α → R) (F : α → β) (G : β → γ) :
    pushforward (pushforward w F) G = pushforward w (fun a => G (F a)) := by
  funext c
  simp only [pushforward]
  have key : ∀ b : β, (if G b = c then ∑ a, (if F a = b then w a else 0) else 0)
      = ∑ a, (if F a = b then (if G b = c then w a else 0) else 0) := by
    intro b
    by_cases h : G b = c <;> simp [h]
  rw [Finset.sum_congr rfl (fun b _ => key b), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_ite_eq Finset.univ (F a) (fun b => if G b = c then w a else 0)]
  simp

end TriangleInflation.FiniteWeights
