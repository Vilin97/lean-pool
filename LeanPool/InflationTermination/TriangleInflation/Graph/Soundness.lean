/-
Copyright (c) 2026 William Blair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Blair
-/

import Mathlib.Analysis.SpecialFunctions.Sqrt
import LeanPool.InflationTermination.TriangleInflation.Graph.Flips
import LeanPool.InflationTermination.TriangleInflation.Defect

/-!
# Nesting, soundness, and source-disjoint independence

Statements split from the original `Statements.lean` skeleton (one file per proving task);
see AUDIT-NOTES for the mathematics.

The witness that a genuine model gives at order `t` is `Sound.inflLaw`: sample every copied
source independently from the model's source law and answer every copied observation with the
model's response kernel. It is a mixture, over copied latent configurations, of product laws
on the copied observations, so all of its marginals are computed by the two facts that
`Sound.pushforward_prodLaw_sel` (an injectively selected block of a product law is the product
law of the block) and `Sound.sum_dprod_prod` (functions of disjoint coordinate blocks are
independent under a product weight) supply.

The four statements below are proved. `sourceDisjoint_independent` of the original skeleton
was false as stated (it quantified over arbitrary sets of copied observations rather than
vertex blocks) and has been removed; the vertex-block form is
`blockMarg_union_of_sourceDisjoint` in `DoubleStar.lean`. `compatible_gExpFeasible` is proved
in `RootSink.lean` from the root-sink lemma.
-/

namespace TriangleInflation.Graph

open Finset TriangleInflation

namespace Sound

/-! ## Generic finite-sum toolkit -/

section Generic

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- A sum over all configurations of a dependent product factorizes. -/
theorem sum_pi_prod {A : κ → Type*} [∀ k, Fintype (A k)] (f : ∀ k, A k → ℝ) :
    (∑ x : (k : κ) → A k, ∏ k, f k (x k)) = ∏ k, ∑ a, f k a := by
  have h := Finset.prod_univ_sum (fun k => (univ : Finset (A k))) f
  rw [Fintype.piFinset_univ] at h
  exact h.symm

omit [DecidableEq κ] in
/-- The indicator of an equality of configurations is a product of coordinate indicators. -/
theorem ite_funext_prod {B : κ → Type*} [∀ k, DecidableEq (B k)] (f g : ∀ k, B k) :
    (if f = g then (1 : ℝ) else 0) = ∏ k, (if f k = g k then (1 : ℝ) else 0) := by
  by_cases h : f = g
  · subst h; simp
  · rw [if_neg h]
    obtain ⟨k, hk⟩ := Function.ne_iff.mp h
    exact (Finset.prod_eq_zero (mem_univ k) (if_neg hk)).symm

/-- A dependent product weight pushed forward along a coordinatewise map. -/
theorem sum_dprod_sel {A B : κ → Type*} [∀ k, Fintype (A k)] [∀ k, DecidableEq (B k)]
    (W : ∀ k, A k → ℝ) (sel : ∀ k, A k → B k) (y : ∀ k, B k) :
    (∑ x : (k : κ) → A k, (if (fun k => sel k (x k)) = y then (1 : ℝ) else 0) * ∏ k, W k (x k))
      = ∏ k, ∑ a, (if sel k a = y k then (1 : ℝ) else 0) * W k a := by
  rw [← sum_pi_prod (fun k a => (if sel k a = y k then (1 : ℝ) else 0) * W k a)]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [ite_funext_prod (fun k => sel k (x k)) y, Finset.prod_mul_distrib]

end Generic

section Push

variable {α β γ : Type*} [Fintype α] [Fintype β] [DecidableEq β] [DecidableEq γ]

/-- Total mass is preserved by pushforward. -/
theorem sum_pushforward (w : α → ℝ) (F : α → β) : ∑ b, pushforward w F b = ∑ a, w a := by
  simp only [pushforward]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single (F a)]
  · simp
  · exact fun b _ hb => if_neg (Ne.symm hb)
  · intro h; exact absurd (mem_univ (F a)) h

/-- Integrating against a pushforward is integrating the pullback. -/
theorem sum_mul_comp (w : α → ℝ) (F : α → β) (G : β → ℝ) :
    ∑ a, w a * G (F a) = ∑ b, pushforward w F b * G b := by
  simp only [pushforward, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single (F a)]
  · simp
  · exact fun b _ hb => by rw [if_neg (Ne.symm hb), zero_mul]
  · intro h; exact absurd (mem_univ (F a)) h

omit [Fintype β] in
/-- Postcomposing the read map with a bijection transports the pushforward. -/
theorem pushforward_comp_equiv (w : α → ℝ) (F : α → β) (E : β ≃ γ) :
    pushforward w (fun a => E (F a)) = fun c => pushforward w F (E.symm c) := by
  funext c
  simp only [pushforward, ← Equiv.eq_symm_apply]

omit [Fintype β] in
/-- Pushing forward a finite mixture. -/
theorem pushforward_mix {ι : Type*} [Fintype ι] (c : ι → ℝ) (ν : ι → α → ℝ) (F : α → β) :
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
    [DecidableEq κ] {w : ι → Bool → ℝ} (hw : ∀ i, ∑ b, w i b = 1) {ν : κ → ι}
    (hν : Function.Injective ν) :
    pushforward (prodLaw w) (fun x k => x (ν k)) = prodLaw (fun k => w (ν k)) := by
  classical
  funext c
  set c' : ι → Bool := fun i => if h : ∃ k, ν k = i then c h.choose else false with hc'
  have hc'ν : ∀ k, c' (ν k) = c k := by
    intro k
    have hex : ∃ k', ν k' = ν k := ⟨k, rfl⟩
    have hb : c' (ν k) = if h : ∃ k', ν k' = ν k then c h.choose else false := rfl
    rw [hb, dif_pos hex]
    exact congrArg c (hν hex.choose_spec)
  set I : Finset ι := univ.image ν with hI
  have hind : ∀ x : ι → Bool,
      (if (fun k => x (ν k)) = c then (1 : ℝ) else 0)
        = ∏ i ∈ I, (if x i = c' i then (1 : ℝ) else 0) := by
    intro x
    rw [hI, Finset.prod_image (fun a _ b _ h => hν h)]
    rw [ite_funext_prod (fun k => x (ν k)) c]
    exact Finset.prod_congr rfl fun k _ => by rw [hc'ν k]
  have hstep : ∀ x : ι → Bool,
      (if (fun k => x (ν k)) = c then prodLaw w x else 0)
        = ∏ i, (w i (x i) * (if i ∈ I then (if x i = c' i then (1 : ℝ) else 0) else 1)) := by
    intro x
    rw [Finset.prod_mul_distrib, Finset.prod_ite_mem, Finset.univ_inter, ← hind x]
    by_cases h : (fun k => x (ν k)) = c
    · rw [if_pos h, if_pos h, mul_one]; rfl
    · rw [if_neg h, if_neg h, mul_zero]
  simp only [pushforward]
  rw [Finset.sum_congr rfl (fun x _ => hstep x),
    sum_pi_prod (fun (i : ι) (b : Bool) =>
      w i b * (if i ∈ I then (if b = c' i then (1 : ℝ) else 0) else 1))]
  have hsum : ∀ i : ι, (∑ b, w i b * (if i ∈ I then (if b = c' i then (1 : ℝ) else 0) else 1))
      = if i ∈ I then w i (c' i) else 1 := by
    intro i
    by_cases hi : i ∈ I
    · simp only [hi, if_true]
      rw [Finset.sum_eq_single (c' i)]
      · simp
      · exact fun b _ hb => by rw [if_neg hb, mul_zero]
      · intro h; exact absurd (mem_univ _) h
    · simp only [hi, if_false, mul_one]
      exact hw i
  rw [Finset.prod_congr rfl (fun i _ => hsum i), Finset.prod_ite_mem, Finset.univ_inter, hI,
    Finset.prod_image (fun a _ b _ h => hν h)]
  exact Finset.prod_congr rfl fun k _ => by rw [hc'ν k]


/-! ## Independence of functions of disjoint coordinate blocks, dependent fibres -/

section DProd

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*} [∀ i, Fintype (A i)]
variable {w : ∀ i, A i → ℝ}

/-- The product weight of independent coordinates with dependent alphabets. -/
def dprod (w : ∀ i, A i → ℝ) (x : ∀ i, A i) : ℝ := ∏ i, w i (x i)

theorem sum_dprod (hw : ∀ i, ∑ a, w i a = 1) : ∑ x : (∀ i, A i), dprod w x = 1 := by
  rw [show (∑ x : (∀ i, A i), dprod w x) = ∏ i, ∑ a, w i a from sum_pi_prod _]
  exact Finset.prod_eq_one fun i _ => hw i

/-- `dmix I x y` takes its `I`-coordinates from `x` and the others from `y`. -/
def dmix (I : Finset ι) (x y : ∀ i, A i) : ∀ i, A i := fun i => if i ∈ I then x i else y i

omit [Fintype ι] [∀ i, Fintype (A i)] in
theorem dmix_mem {I : Finset ι} {x y : ∀ i, A i} {i : ι} (hi : i ∈ I) : dmix I x y i = x i := by
  simp [dmix, hi]

omit [Fintype ι] [∀ i, Fintype (A i)] in
theorem dmix_not_mem {I : Finset ι} {x y : ∀ i, A i} {i : ι} (hi : i ∉ I) :
    dmix I x y i = y i := by simp [dmix, hi]

omit [∀ i, Fintype (A i)] in
theorem dprod_dmix_mul (I : Finset ι) (x y : ∀ i, A i) :
    dprod w (dmix I x y) * dprod w (dmix I y x) = dprod w x * dprod w y := by
  simp only [dprod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hi : i ∈ I
  · rw [dmix_mem hi, dmix_mem hi]
  · rw [dmix_not_mem hi, dmix_not_mem hi, mul_comm]

/-- Functions of disjoint coordinate blocks are uncorrelated under a product weight. -/
theorem sum_dprod_mul_mul (hw : ∀ i, ∑ a, w i a = 1) {I J : Finset ι} (hIJ : Disjoint I J)
    {φ ψ : (∀ i, A i) → ℝ}
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
    show (dprod w q.1 * φ q.1) * (dprod w q.2 * ψ q.2)
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
    ∀ {n : ℕ} (I : Fin n → Finset ι) (χ : Fin n → (∀ i, A i) → ℝ),
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

/-- The marginal of an i.i.d. family at a single coordinate. -/
theorem sum_sel_coord {B : Type*} [Fintype B] [DecidableEq B] {n : Type*} [Fintype n]
    [DecidableEq n] (ρ : B → ℝ) (hρ : ∑ b, ρ b = 1) (r₀ : n) (b₀ : B) :
    ∑ v : n → B, (if v r₀ = b₀ then (1 : ℝ) else 0) * ∏ r, ρ (v r) = ρ b₀ := by
  have hstep : ∀ v : n → B, (if v r₀ = b₀ then (1 : ℝ) else 0) * ∏ r, ρ (v r)
      = ∏ r, (ρ (v r) * if r = r₀ then (if v r = b₀ then (1 : ℝ) else 0) else 1) := by
    intro v
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' univ r₀
      (fun r => if v r = b₀ then (1 : ℝ) else 0)]
    simp [mul_comm]
  rw [Finset.sum_congr rfl (fun v _ => hstep v),
    sum_pi_prod (fun (r : n) (b : B) => ρ b * if r = r₀ then (if b = b₀ then (1 : ℝ) else 0) else 1)]
  have hcol : ∀ r : n, (∑ b, ρ b * if r = r₀ then (if b = b₀ then (1 : ℝ) else 0) else 1)
      = if r = r₀ then ρ b₀ else 1 := by
    intro r
    by_cases hr : r = r₀
    · simp only [hr, if_true]
      rw [Finset.sum_eq_single b₀]
      · simp
      · exact fun b _ hb => by rw [if_neg hb, mul_zero]
      · intro h; exact absurd (mem_univ _) h
    · simp only [hr, if_false, mul_one]; exact hρ
  rw [Finset.prod_congr rfl (fun r _ => hcol r), Finset.prod_ite_eq' univ r₀ (fun _ => ρ b₀)]
  simp

/-! ## Graph helpers -/

variable {Γ : PairGraph} {t : ℕ}

theorem inc_nonempty (Γ : PairGraph) (v : Γ.V) : (Γ.inc v).Nonempty := by
  obtain ⟨w, hw⟩ := Γ.no_isolated v
  refine ⟨⟨s(v, w), ?_⟩, ?_⟩
  · simpa using hw
  · simp [PairGraph.inc]

theorem gAncestors_nonempty (o : GObs Γ t) : (gAncestors o).Nonempty := by
  obtain ⟨e, he⟩ := inc_nonempty Γ o.1
  exact ⟨(e, o.2 ⟨e, he⟩), Finset.mem_image.mpr ⟨⟨e, he⟩, Finset.mem_univ _, rfl⟩⟩

theorem disjoint_of_gAI {S T : Finset (GObs Γ t)} (h : GAncestrallyIndependent S T) :
    Disjoint S T := by
  rw [Finset.disjoint_left]
  intro o hoS hoT
  obtain ⟨a, ha⟩ := gAncestors_nonempty o
  exact (Finset.disjoint_left.mp h (Finset.mem_biUnion.mpr ⟨o, hoS, ha⟩))
    (Finset.mem_biUnion.mpr ⟨o, hoT, ha⟩)

theorem eq_copyObs {ι : Γ.Edge → Fin t} {o : GObs Γ t} (h : o ∈ copySet ι) :
    o = copyObs ι o.1 := by
  obtain ⟨v, _, hv⟩ := Finset.mem_image.mp h
  subst hv
  rfl

theorem vertex_injective {S : Finset (GObs Γ t)} (hS : GInjectable S) :
    Function.Injective (fun o : S => o.1.1) := by
  obtain ⟨ι, hι⟩ := hS
  intro o p hop
  simp only at hop
  exact Subtype.ext (by rw [eq_copyObs (hι o.2), eq_copyObs (hι p.2), hop])

/-! ## The inflated model -/

section Model

variable (M : GModel Γ)

/-- Latent configurations of the order-`t` inflation. -/
abbrev GCfg (M : GModel Γ) (t : ℕ) := (l : GLatent Γ t) → M.L l.1

/-- Latent configurations of the model itself. -/
abbrev MCfg (M : GModel Γ) := (e : Γ.Edge) → M.L e

/-- The response probability of a copied observation under a copied latent configuration. -/
def obsResp (o : GObs Γ t) (x : GCfg M t) : ℝ := M.resp o.1 (fun e => x (e.1, o.2 e))

/-- The conditional per-observation weights of the inflated model. -/
def inflCond (x : GCfg M t) : GObs Γ t → Bool → ℝ := fun o b => respMass (obsResp M o x) b

/-- The weight of a copied latent configuration. -/
def cfgW (t : ℕ) : GCfg M t → ℝ := dprod (fun (l : GLatent Γ t) a => M.μ l.1 a)

/-- The weight of a latent configuration of the model. -/
def mcfgW : MCfg M → ℝ := dprod (fun (e : Γ.Edge) a => M.μ e a)

/-- The witness produced by running the model on the order-`t` inflation: sample every copied
source independently and answer every copied observation with the model's response kernel. -/
def inflLaw (t : ℕ) : GAssign Γ t → ℝ :=
  fun ω => ∑ x : GCfg M t, cfgW M t x * prodLaw (inflCond M x) ω

variable {M}

theorem respMass_sum (q : ℝ) : ∑ b, respMass q b = 1 := by
  rw [Fintype.sum_bool]; simp [respMass]

theorem inflCond_sum (x : GCfg M t) (o : GObs Γ t) : ∑ b, inflCond M x o b = 1 :=
  respMass_sum _

theorem inflCond_isLaw (hM : M.Valid) (x : GCfg M t) (o : GObs Γ t) : IsLaw (inflCond M x o) := by
  refine ⟨fun b => ?_, inflCond_sum x o⟩
  have h := hM.2 o.1 (fun e => x (e.1, o.2 e))
  cases b <;> simp [inflCond, respMass, obsResp] <;> linarith [h.1, h.2]

theorem sum_cfgW (hM : M.Valid) : ∑ x : GCfg M t, cfgW M t x = 1 := by
  rw [show (∑ x : GCfg M t, cfgW M t x) = ∏ l : GLatent Γ t, ∑ a, M.μ l.1 a from sum_pi_prod _]
  exact Finset.prod_eq_one fun l _ => (hM.1 l.1).2

theorem cfgW_nonneg (hM : M.Valid) (x : GCfg M t) : 0 ≤ cfgW M t x :=
  Finset.prod_nonneg fun l _ => (hM.1 l.1).1 _

theorem mcfgW_nonneg (hM : M.Valid) (y : MCfg M) : 0 ≤ mcfgW M y :=
  Finset.prod_nonneg fun e _ => (hM.1 e).1 _

/-- The witness is a mixture of product laws, so its pushforwards are mixtures. -/
theorem pushforward_inflLaw {β : Type*} [DecidableEq β] (F : GAssign Γ t → β) :
    pushforward (inflLaw M t) F
      = fun b => ∑ x : GCfg M t, cfgW M t x * pushforward (prodLaw (inflCond M x)) F b := by
  funext b
  simp only [inflLaw, pushforward, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases h : F ω = b <;> simp [h]

/-- Marginalizing the copied latent configuration onto one copy of the original scenario. -/
theorem latent_marginal (hM : M.Valid) (ι : Γ.Edge → Fin t) (F : MCfg M → ℝ) :
    ∑ x : GCfg M t, cfgW M t x * F (fun e => x (e, ι e)) = ∑ y : MCfg M, mcfgW M y * F y := by
  classical
  set E : GCfg M t ≃ ((e : Γ.Edge) → Fin t → M.L e) :=
    { toFun := fun x e r => x (e, r), invFun := fun u l => u l.1 l.2,
      left_inv := fun _ => rfl, right_inv := fun _ => rfl } with hE
  have h1 : ∑ x : GCfg M t, cfgW M t x * F (fun e => x (e, ι e))
      = ∑ u : ((e : Γ.Edge) → Fin t → M.L e),
          dprod (fun (e : Γ.Edge) (v : Fin t → M.L e) => ∏ r, M.μ e (v r)) u
            * F (fun e => u e (ι e)) := by
    refine Fintype.sum_equiv E _ _ fun x => ?_
    congr 1
    exact Fintype.prod_prod_type (fun l : Γ.Edge × Fin t => M.μ l.1 (x l))
  rw [h1, sum_mul_comp]
  refine Finset.sum_congr rfl fun y _ => ?_
  congr 1
  have hpush : pushforward (dprod (fun (e : Γ.Edge) (v : Fin t → M.L e) => ∏ r, M.μ e (v r)))
      (fun u e => u e (ι e)) y
      = ∑ u : ((e : Γ.Edge) → Fin t → M.L e),
          (if (fun e => u e (ι e)) = y then (1 : ℝ) else 0)
            * ∏ e, (fun (e : Γ.Edge) (v : Fin t → M.L e) => ∏ r, M.μ e (v r)) e (u e) := by
    simp only [pushforward, dprod]
    refine Finset.sum_congr rfl fun u _ => ?_
    by_cases h : (fun e => u e (ι e)) = y <;> simp [h]
  rw [hpush, sum_dprod_sel (fun (e : Γ.Edge) (v : Fin t → M.L e) => ∏ r, M.μ e (v r))
    (fun (e : Γ.Edge) (v : Fin t → M.L e) => v (ι e)) y]
  exact Finset.prod_congr rfl fun e _ => sum_sel_coord (M.μ e) (hM.1 e).2 (ι e) (y e)

end Model


/-! ## The witness built from a model -/

section Witness

variable {M : GModel Γ}

/-- Relabelling copy indices, as a bijection of copied latents. -/
def gLatentPerm (π : Γ.Edge → Equiv.Perm (Fin t)) : GLatent Γ t ≃ GLatent Γ t where
  toFun l := (l.1, π l.1 l.2)
  invFun l := (l.1, (π l.1).symm l.2)
  left_inv _ := by simp
  right_inv _ := by simp

/-- Relabelling copy indices, as a bijection of copied observations. -/
def gObsPerm (π : Γ.Edge → Equiv.Perm (Fin t)) : GObs Γ t ≃ GObs Γ t where
  toFun := gPerm π
  invFun := gPerm (fun e => (π e).symm)
  left_inv _ := by simp [gPerm]
  right_inv _ := by simp [gPerm]

/-- Relabelling copy indices, as a bijection of copied latent configurations. -/
def gCfgPerm (M : GModel Γ) (π : Γ.Edge → Equiv.Perm (Fin t)) : GCfg M t ≃ GCfg M t where
  toFun y := fun l => y (l.1, π l.1 l.2)
  invFun y := fun l => y (l.1, (π l.1).symm l.2)
  left_inv x := by
    funext l; obtain ⟨e, r⟩ := l
    show x (e, (π e) ((π e).symm r)) = x (e, r)
    rw [Equiv.apply_symm_apply]
  right_inv x := by
    funext l; obtain ⟨e, r⟩ := l
    show x (e, (π e).symm ((π e) r)) = x (e, r)
    rw [Equiv.symm_apply_apply]

/-- The witness is a law. -/
theorem isLaw_inflLaw (hM : M.Valid) : IsLaw (inflLaw M t) := by
  constructor
  · intro ω
    refine Finset.sum_nonneg fun x _ => mul_nonneg (cfgW_nonneg hM x) ?_
    exact Finset.prod_nonneg fun o _ => (inflCond_isLaw hM x o).1 _
  · calc ∑ ω : GAssign Γ t, inflLaw M t ω
        = ∑ x : GCfg M t, cfgW M t x * ∑ ω : GAssign Γ t, prodLaw (inflCond M x) ω := by
          simp only [inflLaw, Finset.mul_sum]
          rw [Finset.sum_comm]
      _ = ∑ x : GCfg M t, cfgW M t x := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [sum_prodLaw (fun o => inflCond_isLaw hM x o), mul_one]
      _ = 1 := sum_cfgW hM

/-- The witness is symmetric: the copies of each source are i.i.d. -/
theorem symmetric_inflLaw (M : GModel Γ) (t : ℕ) : GSymmetric t (inflLaw M t) := by
  intro π ω
  rw [show inflLaw M t (gRelabel π ω)
      = ∑ x : GCfg M t, cfgW M t x * prodLaw (inflCond M x) (gRelabel π ω) from rfl,
    ← Equiv.sum_comp (gCfgPerm M π)
      (fun x => cfgW M t x * prodLaw (inflCond M x) (gRelabel π ω))]
  refine Finset.sum_congr rfl fun y _ => ?_
  have h1 : cfgW M t (gCfgPerm M π y) = cfgW M t y :=
    Equiv.prod_comp (gLatentPerm π) (fun l => M.μ l.1 (y l))
  have h2 : prodLaw (inflCond M (gCfgPerm M π y)) (gRelabel π ω) = prodLaw (inflCond M y) ω :=
    Equiv.prod_comp (gObsPerm π) (fun o => respMass (obsResp M o y) (ω o))
  rw [h1, h2]

/-- The marginal of the witness on a block of copied observations. -/
theorem inflLaw_block (S : Finset (GObs Γ t)) (φ : S → Bool) :
    pushforward (inflLaw M t) (gRestrict S) φ
      = ∑ x : GCfg M t, cfgW M t x * ∏ o : S, respMass (obsResp M o.1 x) (φ o) := by
  rw [pushforward_inflLaw]
  refine Finset.sum_congr rfl fun x _ => ?_
  have h2 : pushforward (prodLaw (inflCond M x)) (gRestrict S)
      = prodLaw (fun k : S => inflCond M x (k : GObs Γ t)) :=
    pushforward_prodLaw_sel (ν := fun k : S => (k : GObs Γ t))
      (fun o => inflCond_sum x o) Subtype.val_injective
  rw [h2]
  rfl

/-- On a copy of the original scenario the copy indices are those of the copy. -/
theorem copySet_snd {ι : Γ.Edge → Fin t} {o : GObs Γ t} (h : o ∈ copySet ι) (e : Γ.inc o.1) :
    o.2 e = ι e.1 := by
  obtain ⟨v, _, hv⟩ := Finset.mem_image.mp h
  subst hv
  rfl

/-- Every injectable set carries the corresponding marginal of the model's law: the copied
observations of an injectable set read one copy of the original scenario. -/
theorem inflLaw_injectable (hM : M.Valid) {S : Finset (GObs Γ t)} (hS : GInjectable S) :
    pushforward (inflLaw M t) (gRestrict S) = pushforward M.law (gPartyRead S) := by
  obtain ⟨ι, hι⟩ := hS
  funext φ
  set F : MCfg M → ℝ :=
    fun y => ∏ o : S, respMass (M.resp o.1.1 (fun e => y e.1)) (φ o) with hF
  have hresp : ∀ (x : GCfg M t) (o : S),
      obsResp M o.1 x = M.resp o.1.1 (fun e => x (e.1, ι e.1)) :=
    fun x o => congrArg (M.resp o.1.1) (funext fun e => by rw [copySet_snd (hι o.2) e])
  have hL : pushforward (inflLaw M t) (gRestrict S) φ = ∑ y : MCfg M, mcfgW M y * F y := by
    rw [inflLaw_block S φ, ← latent_marginal hM ι F]
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 1
    exact Finset.prod_congr rfl fun o _ => by rw [hresp x o]
  have hR : pushforward M.law (gPartyRead S) φ = ∑ y : MCfg M, mcfgW M y * F y := by
    rw [show M.law = fun w => ∑ y : MCfg M,
        mcfgW M y * prodLaw (fun v b => respMass (M.resp v (fun e => y e.1)) b) w from rfl,
      pushforward_mix]
    refine Finset.sum_congr rfl fun y _ => ?_
    have h2 : pushforward (prodLaw (fun v b => respMass (M.resp v (fun e => y e.1)) b))
        (gPartyRead S)
        = prodLaw (fun k : S => (fun v b => respMass (M.resp v (fun e => y e.1)) b) k.1.1) :=
      pushforward_prodLaw_sel (ν := fun k : S => (k : GObs Γ t).1)
        (fun v => respMass_sum _) (vertex_injective ⟨ι, hι⟩)
    rw [h2]
    rfl
  rw [hL, hR]

/-! ## The diagonal law of the witness -/

/-- The copied observation that diagonal row `r` reads at the vertex `v`. -/
def diagObs (Γ : PairGraph) (t : ℕ) (p : Fin t × Γ.V) : GObs Γ t := ⟨p.2, fun _ => p.1⟩

/-- The `t · |V|` diagonal observations are distinct. -/
theorem diagObs_injective (Γ : PairGraph) (t : ℕ) : Function.Injective (diagObs Γ t) := by
  rintro ⟨r, v⟩ ⟨r', v'⟩ hEq
  simp only [diagObs, Sigma.mk.injEq] at hEq
  obtain ⟨hv, hfn⟩ := hEq
  subst hv
  obtain ⟨e, he⟩ := inc_nonempty Γ v
  have hr : r = r' := congrFun (eq_of_heq hfn) ⟨e, he⟩
  rw [hr]

theorem readDiag_factor (Γ : PairGraph) (t : ℕ) :
    (readDiag : GAssign Γ t → (Fin t → Γ.V → Bool))
      = fun ω => Equiv.curry (Fin t) Γ.V Bool (fun p => ω (diagObs Γ t p)) := rfl

/-- The diagonal law of the witness is the tensor power of the model's law: the `t` copies of
the scenario use disjoint copies of every source. -/
theorem inflLaw_diag (_hM : M.Valid) :
    pushforward (inflLaw M t) readDiag = gTensorPow t M.law := by
  funext w
  have h1 : pushforward (inflLaw M t) readDiag w
      = pushforward (inflLaw M t)
          (fun (ω : GAssign Γ t) (p : Fin t × Γ.V) => ω (diagObs Γ t p)) (fun p => w p.1 p.2) := by
    rw [readDiag_factor]
    exact congrFun (pushforward_comp_equiv (inflLaw M t)
      (fun (ω : GAssign Γ t) (p : Fin t × Γ.V) => ω (diagObs Γ t p))
      (Equiv.curry (Fin t) Γ.V Bool)) w
  have h2 : ∀ x : GCfg M t,
      pushforward (prodLaw (inflCond M x))
          (fun (ω : GAssign Γ t) (p : Fin t × Γ.V) => ω (diagObs Γ t p)) (fun p => w p.1 p.2)
        = ∏ r : Fin t, ∏ v : Γ.V, respMass (M.resp v (fun e => x (e.1, r))) (w r v) := by
    intro x
    rw [pushforward_prodLaw_sel (ν := diagObs Γ t) (fun o => inflCond_sum x o)
      (diagObs_injective Γ t)]
    exact Fintype.prod_prod_type
      (fun p : Fin t × Γ.V => respMass (obsResp M (diagObs Γ t p) x) (w p.1 p.2))
  set E2 : GCfg M t ≃ (Fin t → MCfg M) :=
    { toFun := fun x r e => x (e, r), invFun := fun z l => z l.2 l.1,
      left_inv := fun _ => rfl, right_inv := fun _ => rfl } with hE2
  have h3 : ∑ x : GCfg M t,
        cfgW M t x * ∏ r : Fin t, ∏ v : Γ.V, respMass (M.resp v (fun e => x (e.1, r))) (w r v)
      = ∑ z : Fin t → MCfg M, ∏ r : Fin t,
          (mcfgW M (z r) * ∏ v : Γ.V, respMass (M.resp v (fun e => z r e.1)) (w r v)) := by
    refine Fintype.sum_equiv E2 _ _ fun x => ?_
    rw [Finset.prod_mul_distrib]
    congr 1
    calc cfgW M t x = ∏ e : Γ.Edge, ∏ r : Fin t, M.μ e (x (e, r)) :=
          Fintype.prod_prod_type (fun l : Γ.Edge × Fin t => M.μ l.1 (x l))
      _ = ∏ r : Fin t, ∏ e : Γ.Edge, M.μ e (x (e, r)) := Finset.prod_comm
  rw [h1, pushforward_inflLaw]
  simp only [h2]
  rw [h3, sum_pi_prod (fun (r : Fin t) (y : MCfg M) =>
    mcfgW M y * ∏ v : Γ.V, respMass (M.resp v (fun e => y e.1)) (w r v))]
  rfl

/-! ## The ancestral-independence prescriptions -/

/-- Currying a Bool-valued function on a disjoint union of blocks. -/
def sigCurry {n : ℕ} (S : Fin n → Finset (GObs Γ t)) :
    ((Σ m : Fin n, ↥(S m)) → Bool) ≃ (∀ m : Fin n, ↥(S m) → Bool) where
  toFun f := fun m o => f ⟨m, o⟩
  invFun g := fun p => g p.1 p.2
  left_inv _ := by funext p; obtain ⟨m, o⟩ := p; rfl
  right_inv _ := rfl

theorem sigma_val_injective {n : ℕ} {S : Fin n → Finset (GObs Γ t)}
    (hd : ∀ m m', m ≠ m' → Disjoint (S m) (S m')) :
    Function.Injective (fun p : Σ m : Fin n, ↥(S m) => (p.2 : GObs Γ t)) := by
  rintro ⟨m, o⟩ ⟨m', o'⟩ h
  simp only at h
  have hmm : m = m' := by
    by_contra hne
    exact (Finset.disjoint_left.mp (hd m m' hne) o.2) (by rw [h]; exact o'.2)
  subst hmm
  simp only [Sigma.mk.injEq, heq_eq_eq, true_and]
  exact Subtype.ext h

theorem mem_gAncestorsOf {S : Finset (GObs Γ t)} {o : GObs Γ t} (ho : o ∈ S) (e : Γ.inc o.1) :
    (e.1, o.2 e) ∈ gAncestorsOf S :=
  Finset.mem_biUnion.mpr ⟨o, ho, Finset.mem_image.mpr ⟨e, Finset.mem_univ _, rfl⟩⟩

/-- The witness satisfies every ancestral-independence prescription: blocks with disjoint
copied ancestries are functions of disjoint families of independent copied sources. -/
theorem inflLaw_ai (hM : M.Valid) : GAncestralProducts t (inflLaw M t) M.law := by
  intro n S hinj hai
  have hdisj : ∀ m m', m ≠ m' → Disjoint (S m) (S m') := fun m m' h => disjoint_of_gAI (hai m m' h)
  funext φ
  have h1 : pushforward (inflLaw M t) (fun ω m => gRestrict (S m) ω) φ
      = pushforward (inflLaw M t)
          (fun (ω : GAssign Γ t) (p : Σ m : Fin n, ↥(S m)) => ω (p.2 : GObs Γ t))
          ((sigCurry S).symm φ) :=
    congrFun (pushforward_comp_equiv (inflLaw M t)
      (fun (ω : GAssign Γ t) (p : Σ m : Fin n, ↥(S m)) => ω (p.2 : GObs Γ t)) (sigCurry S)) φ
  have h2 : ∀ x : GCfg M t,
      pushforward (prodLaw (inflCond M x))
          (fun (ω : GAssign Γ t) (p : Σ m : Fin n, ↥(S m)) => ω (p.2 : GObs Γ t))
          ((sigCurry S).symm φ)
        = ∏ m : Fin n, ∏ o : ↥(S m), respMass (obsResp M o.1 x) (φ m o) := by
    intro x
    rw [pushforward_prodLaw_sel (ν := fun p : Σ m : Fin n, ↥(S m) => (p.2 : GObs Γ t))
      (fun o => inflCond_sum x o) (sigma_val_injective hdisj)]
    exact Fintype.prod_sigma
      (fun p : Σ m : Fin n, ↥(S m) => respMass (obsResp M (p.2 : GObs Γ t) x) (φ p.1 p.2))
  have hdep : ∀ (m : Fin n) (x y : GCfg M t),
      (∀ l ∈ gAncestorsOf (S m), x l = y l) →
        (∏ o : ↥(S m), respMass (obsResp M o.1 x) (φ m o))
          = ∏ o : ↥(S m), respMass (obsResp M o.1 y) (φ m o) := by
    intro m x y hxy
    refine Finset.prod_congr rfl fun o _ => ?_
    congr 1
    exact congrArg (M.resp o.1.1) (funext fun e => hxy (e.1, o.1.2 e) (mem_gAncestorsOf o.2 e))
  have h3 : ∑ x : GCfg M t,
        cfgW M t x * ∏ m : Fin n, ∏ o : ↥(S m), respMass (obsResp M o.1 x) (φ m o)
      = ∏ m : Fin n, ∑ x : GCfg M t,
          cfgW M t x * ∏ o : ↥(S m), respMass (obsResp M o.1 x) (φ m o) :=
    sum_dprod_prod (fun l => (hM.1 l.1).2) (fun m => gAncestorsOf (S m)) _
      (fun m m' hmm => hai m m' hmm) hdep
  rw [h1, pushforward_inflLaw]
  simp only [h2]
  rw [h3]
  refine Finset.prod_congr rfl fun m _ => ?_
  rw [← inflLaw_block (S m) (φ m), inflLaw_injectable hM (hinj m)]

end Witness


/-! ## From the expressible closure to the ancestral-independence prescriptions -/

section Nesting

theorem pushforward_id {α : Type*} [Fintype α] [DecidableEq α] (w : α → ℝ) :
    pushforward w id = w := by
  funext a
  simp only [pushforward, id]
  rw [Finset.sum_eq_single a]
  · simp
  · exact fun b _ hb => if_neg hb
  · intro h; exact absurd (mem_univ a) h

theorem pushforward_prod {α β α' β' : Type*} [Fintype α] [Fintype β] [DecidableEq α']
    [DecidableEq β'] (A : α → ℝ) (B : β → ℝ) (f : α → α') (g : β → β') :
    pushforward (fun p : α × β => A p.1 * B p.2) (fun p => (f p.1, g p.2))
      = fun q => pushforward A f q.1 * pushforward B g q.2 := by
  funext q
  simp only [pushforward, Fintype.sum_prod_type]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases h1 : f a = q.1 <;> by_cases h2 : g b = q.2 <;> simp [Prod.ext_iff, h1, h2]

/-- Restriction to a subset that contains everything is injective. -/
theorem subRestrict_injective {A B : Finset (GObs Γ t)} (hAB : A ⊆ B) (hBA : B ⊆ A) :
    Function.Injective (subRestrict hAB) := by
  intro χ χ' h
  funext o
  have := congrFun h ⟨o.1, hBA o.2⟩
  exact this

/-- A law is recovered from its restriction to a set with the same elements. -/
theorem pushforward_subRestrict_self {A B : Finset (GObs Γ t)} (hAB : A ⊆ B) (hBA : B ⊆ A)
    (μ : (↥B → Bool) → ℝ) (b : ↥B → Bool) :
    pushforward μ (subRestrict hAB) (subRestrict hAB b) = μ b := by
  simp only [pushforward]
  rw [Finset.sum_eq_single b]
  · simp
  · intro χ _ hχ
    exact if_neg fun h => hχ (subRestrict_injective hAB hBA h)
  · intro h; exact absurd (mem_univ b) h

theorem empty_fun_eq (f g : ↥(∅ : Finset (GObs Γ t)) → Bool) : f = g :=
  funext fun o => absurd o.2 (Finset.notMem_empty _)

theorem left_sub (X Y : Finset (GObs Γ t)) : X ⊆ X ∪ Y ∪ ∅ := fun a ha => by simp [ha]

theorem right_sub (X Y : Finset (GObs Γ t)) : Y ⊆ X ∪ Y ∪ ∅ := fun a ha => by simp [ha]

theorem union_empty_sub (X : Finset (GObs Γ t)) : X ∪ ∅ ⊆ X := fun a ha => by simpa using ha

theorem sub_union_empty (X : Finset (GObs Γ t)) : X ⊆ X ∪ ∅ := fun a ha => by simp [ha]

/-- Ancestrally disjoint sets are `d`-separated given the empty set: a trail between them
would have to be a single edge, and that edge is a shared copied parent. -/
theorem dsep_empty_of_ai {X Y : Finset (GObs Γ t)} (h : GAncestrallyIndependent X Y) :
    dsep X Y ∅ := by
  rintro o₀ mid o₁ ⟨hX, hY, hmid, hchain⟩
  have hnil : mid = [] := by
    rcases mid with _ | ⟨a, l⟩
    · rfl
    · exact absurd (hmid a (by simp)) (Finset.notMem_empty a)
  subst hnil
  simp only [List.nil_append] at hchain
  have hsp : SharesParent o₀ o₁ := by
    simpa using hchain
  refine hsp (Finset.disjoint_left.mpr fun a ha ha' => ?_)
  exact Finset.disjoint_left.mp h (Finset.mem_biUnion.mpr ⟨o₀, hX, ha⟩)
    (Finset.mem_biUnion.mpr ⟨o₁, hY, ha'⟩)

theorem gAncestorsOf_biUnion {n : ℕ} (T : Fin n → Finset (GObs Γ t)) :
    gAncestorsOf (univ.biUnion T) = univ.biUnion (fun m => gAncestorsOf (T m)) := by
  simp [gAncestorsOf, Finset.biUnion_biUnion]

/-- Splitting a Bool-valued function on a disjoint union into its two halves. -/
def pairSel (X Y : Finset (GObs Γ t)) (χ : ↥(X ∪ Y ∪ ∅) → Bool) :
    (↥X → Bool) × (↥Y → Bool) :=
  (subRestrict (left_sub X Y) χ, subRestrict (right_sub X Y) χ)

theorem pairSel_bijective {X Y : Finset (GObs Γ t)} (hXY : Disjoint X Y) :
    Function.Bijective (pairSel X Y) := by
  classical
  constructor
  · intro χ χ' h
    funext o
    have hmem : o.1 ∈ X ∨ o.1 ∈ Y := by simpa using o.2
    rcases hmem with hx | hy
    · exact congrFun (congrArg Prod.fst h) ⟨o.1, hx⟩
    · exact congrFun (congrArg Prod.snd h) ⟨o.1, hy⟩
  · rintro ⟨a, b⟩
    refine ⟨fun o => if h : o.1 ∈ X then a ⟨o.1, h⟩ else b ⟨o.1, ?_⟩, ?_⟩
    · have hm : o.1 ∈ X ∨ o.1 ∈ Y := by simpa using o.2
      exact hm.resolve_left h
    · refine Prod.ext ?_ ?_
      · funext o
        exact dif_pos o.2
      · funext o
        exact dif_neg (Finset.disjoint_right.mp hXY o.2)

/-- The two halves of a Bool-valued function on a disjoint union determine it. -/
noncomputable def pairEquiv {X Y : Finset (GObs Γ t)} (hXY : Disjoint X Y) :
    (↥(X ∪ Y ∪ ∅) → Bool) ≃ ((↥X → Bool) × (↥Y → Bool)) :=
  Equiv.ofBijective (pairSel X Y) (pairSel_bijective hXY)

end Nesting


section Induction

variable {P : GTarget Γ} {Δ : GAssign Γ t → ℝ}

/-- Splitting a dependent family over `Fin (n+1)` into its head and tail. -/
def consEquiv {n : ℕ} (β : Fin (n + 1) → Type*) :
    (β 0 × ∀ m : Fin n, β m.succ) ≃ (∀ m, β m) where
  toFun q := Fin.cons q.1 q.2
  invFun f := (f 0, fun m => f m.succ)
  left_inv _ := rfl
  right_inv f := by funext m; refine Fin.cases ?_ ?_ m <;> intros <;> rfl

/-- Restricting a function on the union of the tail blocks to each tail block. -/
def tailSel {n : ℕ} (S : Fin (n + 1) → Finset (GObs Γ t)) :
    (↥(univ.biUnion fun m : Fin n => S m.succ) → Bool) → (∀ m : Fin n, ↥(S m.succ) → Bool) :=
  fun b m => subRestrict
    (Finset.subset_biUnion_of_mem (fun m : Fin n => S m.succ) (Finset.mem_univ m)) b

/-- The head block keeps its function, the tail block is split. -/
def headTailSel {n : ℕ} (S : Fin (n + 1) → Finset (GObs Γ t)) :
    ((↥(S 0) → Bool) × (↥(univ.biUnion fun m : Fin n => S m.succ) → Bool))
      → ((↥(S 0) → Bool) × (∀ m : Fin n, ↥(S m.succ) → Bool)) :=
  fun q => (id q.1, tailSel S q.2)

/-- One gluing step with an empty conditioning set: an injectable block and an expressible
block with disjoint copied ancestries glue to their product. -/
theorem glue_pair (hPsum : ∑ w, P w = 1)
    (hexp : ∀ (S : Finset (GObs Γ t)) (μ : (↥S → Bool) → ℝ), Expressible t P S μ →
      pushforward Δ (gRestrict S) = μ)
    {X Y : Finset (GObs Γ t)} {μY : (↥Y → Bool) → ℝ}
    (hX : GInjectable X) (hμY : Expressible t P Y μY)
    (haiXY : GAncestrallyIndependent X Y) :
    Expressible t P (X ∪ Y ∪ ∅)
        (glueLaw X Y ∅ (pushforward P (gPartyRead (X ∪ ∅)))
          (pushforward μY (subRestrict (union_empty_sub Y)))) ∧
      pushforward Δ (fun ω => (gRestrict X ω, gRestrict Y ω))
        = fun q => pushforward P (gPartyRead X) q.1 * pushforward Δ (gRestrict Y) q.2 := by
  have hXY : Disjoint X Y := disjoint_of_gAI haiXY
  have h₁ : Expressible t P (X ∪ ∅) (pushforward P (gPartyRead (X ∪ ∅))) := by
    refine Expressible.inj ?_
    obtain ⟨ι₀, hι₀⟩ := hX
    exact ⟨ι₀, by simpa using hι₀⟩
  have h₂ : Expressible t P (Y ∪ ∅) (pushforward μY (subRestrict (union_empty_sub Y))) :=
    Expressible.marg (union_empty_sub Y) hμY
  have hglue := Expressible.glue h₁ h₂ hXY (by simp) (by simp) (dsep_empty_of_ai haiXY)
  refine ⟨hglue, ?_⟩
  have hW := hexp _ _ hglue
  have hμYΔ : pushforward Δ (gRestrict Y) = μY := hexp _ _ hμY
  have hmass : ∑ ψ : ↥(X ∪ ∅) → Bool, pushforward P (gPartyRead (X ∪ ∅)) ψ = 1 := by
    rw [sum_pushforward]; exact hPsum
  have hE : pushforward Δ (fun ω => (gRestrict X ω, gRestrict Y ω))
      = fun q => pushforward Δ (gRestrict (X ∪ Y ∪ ∅)) ((pairEquiv hXY).symm q) :=
    pushforward_comp_equiv Δ (gRestrict (X ∪ Y ∪ ∅)) (pairEquiv hXY)
  rw [hE]
  funext q
  obtain ⟨a, b⟩ := q
  have hEq : pairSel X Y ((pairEquiv hXY).symm (a, b)) = (a, b) :=
    (pairEquiv hXY).apply_symm_apply (a, b)
  have hEa : subRestrict (left_sub X Y) ((pairEquiv hXY).symm (a, b)) = a :=
    congrArg Prod.fst hEq
  have hEb : subRestrict (right_sub X Y) ((pairEquiv hXY).symm (a, b)) = b :=
    congrArg Prod.snd hEq
  have hra : subRestrict (sub_left_union X Y ∅) ((pairEquiv hXY).symm (a, b))
      = subRestrict (union_empty_sub X) a := by
    funext o
    exact congrFun hEa ⟨o.1, union_empty_sub X o.2⟩
  have hrb : subRestrict (sub_right_union X Y ∅) ((pairEquiv hXY).symm (a, b))
      = subRestrict (union_empty_sub Y) b := by
    funext o
    exact congrFun hEb ⟨o.1, union_empty_sub Y o.2⟩
  have hmz : pushforward (pushforward P (gPartyRead (X ∪ ∅))) (subRestrict (sub_mid_left X ∅))
      (subRestrict (sub_mid_union X Y ∅) ((pairEquiv hXY).symm (a, b))) = 1 := by
    simp only [pushforward]
    rw [Finset.sum_congr rfl (fun ψ _ =>
      if_pos (empty_fun_eq (subRestrict (sub_mid_left X ∅) ψ)
        (subRestrict (sub_mid_union X Y ∅) ((pairEquiv hXY).symm (a, b)))))]
    exact hmass
  have hμ₁ : pushforward P (gPartyRead (X ∪ ∅)) (subRestrict (union_empty_sub X) a)
      = pushforward P (gPartyRead X) a := by
    have hcomp : pushforward P (gPartyRead (X ∪ ∅))
        = pushforward (pushforward P (gPartyRead X)) (subRestrict (union_empty_sub X)) :=
      (pushforward_pushforward P (gPartyRead X) (subRestrict (union_empty_sub X))).symm
    rw [hcomp]
    exact pushforward_subRestrict_self (union_empty_sub X) (sub_union_empty X) _ a
  have hμ₂ : pushforward μY (subRestrict (union_empty_sub Y))
      (subRestrict (union_empty_sub Y) b) = μY b :=
    pushforward_subRestrict_self (union_empty_sub Y) (sub_union_empty Y) _ b
  rw [hW]
  simp only [glueLaw]
  rw [hra, hrb, hmz, if_pos one_pos, div_one, hμ₁, hμ₂, hμYΔ]

/-- With no blocks the ancestral-independence prescription is the total mass. -/
theorem ancestral_zero (hlaw : IsLaw Δ) (S : Fin 0 → Finset (GObs Γ t)) :
    pushforward Δ (fun ω m => gRestrict (S m) ω)
      = fun φ => ∏ m, pushforward P (gPartyRead (S m)) (φ m) := by
  funext φ
  have h0 : ∀ ψ : (∀ m : Fin 0, ↥(S m) → Bool), ψ = φ := fun ψ => funext fun m => m.elim0
  have hsum : pushforward Δ (fun ω m => gRestrict (S m) ω) φ = ∑ ω, Δ ω := by
    simp only [pushforward]
    exact Finset.sum_congr rfl fun ω _ => if_pos (h0 _)
  rw [hsum, hlaw.2]
  simp

/-- The expressible closure prescribes the ancestral-independence products: the blocks are
glued one at a time with an empty conditioning set, and the glue law with an empty
conditioning set is the product of the two block laws. -/
theorem exp_induct (hlaw : IsLaw Δ) (hPsum : ∑ w, P w = 1)
    (hexp : ∀ (S : Finset (GObs Γ t)) (μ : (↥S → Bool) → ℝ), Expressible t P S μ →
      pushforward Δ (gRestrict S) = μ) (ι : Γ.Edge → Fin t) :
    ∀ (n : ℕ) (S : Fin n → Finset (GObs Γ t)), (∀ m, GInjectable (S m)) →
      (∀ m m', m ≠ m' → GAncestrallyIndependent (S m) (S m')) →
      (∃ μ, Expressible t P (univ.biUnion S) μ) ∧
        pushforward Δ (fun ω m => gRestrict (S m) ω)
          = fun φ => ∏ m, pushforward P (gPartyRead (S m)) (φ m) := by
  intro n
  induction n with
  | zero =>
      intro S _ _
      exact ⟨⟨_, Expressible.inj (S := univ.biUnion S) ⟨ι, by simp⟩⟩, ancestral_zero hlaw S⟩
  | succ n ih =>
      intro S hinj hai
      obtain ⟨⟨μY, hμY⟩, hIH⟩ := ih (fun m => S m.succ) (fun m => hinj m.succ)
        (fun m m' h => hai m.succ m'.succ fun hc => h (Fin.succ_injective n hc))
      have haiXY : GAncestrallyIndependent (S 0) (univ.biUnion fun m : Fin n => S m.succ) := by
        rw [GAncestrallyIndependent, gAncestorsOf_biUnion, Finset.disjoint_biUnion_right]
        exact fun m _ => hai 0 m.succ (Ne.symm (Fin.succ_ne_zero m))
      obtain ⟨hglue, hpair⟩ := glue_pair (Δ := Δ) hPsum hexp (hinj 0) hμY haiXY
      have hsub : univ.biUnion S
          ⊆ S 0 ∪ (univ.biUnion fun m : Fin n => S m.succ) ∪ ∅ := by
        intro c hc
        obtain ⟨m, -, hm⟩ := Finset.mem_biUnion.mp hc
        rcases Fin.eq_zero_or_eq_succ m with rfl | ⟨m', rfl⟩
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ hm)
        · exact Finset.mem_union_left _ (Finset.mem_union_right _
            (Finset.mem_biUnion.mpr ⟨m', Finset.mem_univ _, hm⟩))
      refine ⟨⟨_, Expressible.marg hsub hglue⟩, ?_⟩
      have hmap : (fun (ω : GAssign Γ t) (m : Fin (n + 1)) => gRestrict (S m) ω)
          = fun ω => consEquiv (fun m : Fin (n + 1) => ↥(S m) → Bool)
              (headTailSel S (gRestrict (S 0) ω,
                gRestrict (univ.biUnion fun m : Fin n => S m.succ) ω)) := by
        funext ω m
        refine Fin.cases ?_ ?_ m <;> intros <;> rfl
      have e1 : pushforward Δ (fun ω m => gRestrict (S m) ω)
          = fun φ => pushforward Δ (fun ω => headTailSel S (gRestrict (S 0) ω,
              gRestrict (univ.biUnion fun m : Fin n => S m.succ) ω))
                ((consEquiv (fun m : Fin (n + 1) => ↥(S m) → Bool)).symm φ) := by
        rw [hmap]
        exact pushforward_comp_equiv Δ _ (consEquiv (fun m : Fin (n + 1) => ↥(S m) → Bool))
      have e2 : pushforward Δ (fun ω => headTailSel S (gRestrict (S 0) ω,
            gRestrict (univ.biUnion fun m : Fin n => S m.succ) ω))
          = pushforward (pushforward Δ (fun ω => (gRestrict (S 0) ω,
              gRestrict (univ.biUnion fun m : Fin n => S m.succ) ω))) (headTailSel S) :=
        (pushforward_pushforward Δ _ (headTailSel S)).symm
      have e3 : pushforward (fun q : (↥(S 0) → Bool)
              × (↥(univ.biUnion fun m : Fin n => S m.succ) → Bool) =>
            pushforward P (gPartyRead (S 0)) q.1
              * pushforward Δ (gRestrict (univ.biUnion fun m : Fin n => S m.succ)) q.2)
          (headTailSel S)
          = fun r => pushforward (pushforward P (gPartyRead (S 0))) id r.1
              * pushforward (pushforward Δ
                  (gRestrict (univ.biUnion fun m : Fin n => S m.succ))) (tailSel S) r.2 :=
        pushforward_prod _ _ id (tailSel S)
      have e4 : pushforward (pushforward Δ
            (gRestrict (univ.biUnion fun m : Fin n => S m.succ))) (tailSel S)
          = fun ψ => ∏ m : Fin n, pushforward P (gPartyRead (S m.succ)) (ψ m) := by
        rw [pushforward_pushforward]
        exact hIH
      have key : pushforward Δ (fun ω m => gRestrict (S m) ω)
          = fun φ => pushforward P (gPartyRead (S 0)) (φ 0)
              * ∏ m : Fin n, pushforward P (gPartyRead (S m.succ)) (φ m.succ) := by
        rw [e1, e2, hpair, e3, e4, pushforward_id]
        rfl
      rw [key]
      funext φ
      rw [Fin.prod_univ_succ]

end Induction

end Sound
variable {Γ : PairGraph} {t : ℕ}

/-! ## Nesting of the three hierarchies -/

/-- The expressible feasible set is contained in the AI feasible set: the AI prescriptions
are the injectable and ancestrally independent instances of the expressible closure
(paper equation (eq:nested)). -/
theorem gAIFeasible_of_gExpFeasible (Γ : PairGraph) (t : ℕ) (P : GTarget Γ) :
    GExpFeasible Γ t P → GAIFeasible Γ t P := by
  rintro ⟨Δ, hlaw, hsym, hdiag, hexp⟩
  have hinjm : GInjectableMarginals t Δ P := fun S hS => hexp S _ (Expressible.inj hS)
  refine ⟨Δ, hlaw, hsym, hdiag, hinjm, ?_⟩
  intro n
  cases n with
  | zero => exact fun S _ _ => Sound.ancestral_zero hlaw S
  | succ n =>
      intro S hinj hai
      obtain ⟨ι, -⟩ := hinj 0
      have hmass : ∑ ψ : ↥(copySet ι) → Bool, pushforward Δ (gRestrict (copySet ι)) ψ
          = ∑ ψ : ↥(copySet ι) → Bool, pushforward P (gPartyRead (copySet ι)) ψ := by
        rw [hinjm (copySet ι) ⟨ι, Finset.Subset.refl _⟩]
      rw [Sound.sum_pushforward, Sound.sum_pushforward, hlaw.2] at hmass
      exact (Sound.exp_induct hlaw hmass.symm hexp ι (n + 1) S hinj hai).2

/-- The AI feasible set is contained in the Navascués–Wolfe feasible set. -/
theorem gNWFeasible_of_gAIFeasible (Γ : PairGraph) (t : ℕ) (P : GTarget Γ) :
    GAIFeasible Γ t P → GNWFeasible Γ t P := by
  rintro ⟨Δ, h1, h2, h3, -, -⟩
  exact ⟨Δ, h1, h2, h3⟩

/-- A genuine model gives a witness at every order: run the inflated model. Hence the
compatible set is contained in every Navascués–Wolfe feasible set. -/
theorem compatible_gNWFeasible (Γ : PairGraph) (t : ℕ) (P : GTarget Γ) (h : GCompatible Γ P) :
    GNWFeasible Γ t P := by
  obtain ⟨M, hM, rfl⟩ := h
  exact ⟨Sound.inflLaw M t, Sound.isLaw_inflLaw hM, Sound.symmetric_inflLaw M t,
    Sound.inflLaw_diag hM⟩

/-- A genuine model gives a witness satisfying all injectable and ancestral-independence
prescriptions. -/
theorem compatible_gAIFeasible (Γ : PairGraph) (t : ℕ) (P : GTarget Γ) (h : GCompatible Γ P) :
    GAIFeasible Γ t P := by
  obtain ⟨M, hM, rfl⟩ := h
  exact ⟨Sound.inflLaw M t, Sound.isLaw_inflLaw hM, Sound.symmetric_inflLaw M t,
    Sound.inflLaw_diag hM, fun S hS => Sound.inflLaw_injectable hM hS, Sound.inflLaw_ai hM⟩

end TriangleInflation.Graph
