/-
Copyright (c) 2026 William Blair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Blair
-/

import LeanPool.InflationTermination.TriangleInflation.Graph.Linear

/-!
# The five-path witness at every order

AUDIT-NOTES A4 / Theorem `thm:fivepath`: the order-`t` witness `fivePath_witness` for the five-path target with `h = 1/(16t²)`, built as the inflated law of a complex-weighted pair-source model, and its recursively expressible form. Everything here is proved.
-/

namespace TriangleInflation.Graph

open Finset TriangleInflation FivePathAux

namespace P5WitnessAux


/-! ## Complex weights -/

/-- Pushforward of a complex weight function. -/
def cpush {α β : Type*} [Fintype α] [DecidableEq β] (w : α → ℂ) (F : α → β) : β → ℂ :=
  fun b => ∑ a : α, if F a = b then w a else 0

/-- Product of independent complex per-coordinate weights on `ι → Bool`. -/
def cprodLaw {ι : Type*} [Fintype ι] (w : ι → Bool → ℂ) : (ι → Bool) → ℂ :=
  fun x => ∏ i, w i (x i)

/-- `respMass` with a complex response weight. -/
def crespMass (q : ℂ) : Bool → ℂ := fun b => if b then 1 - q else q

theorem crespMass_ofReal (q : ℝ) (b : Bool) :
    crespMass ((q : ℝ) : ℂ) b = ((respMass q b : ℝ) : ℂ) := by
  cases b <;> simp [crespMass, respMass]

theorem crespMass_sum (q : ℂ) : ∑ b, crespMass q b = 1 := by
  rw [Fintype.sum_bool]; simp [crespMass]

theorem cpush_re {α β : Type*} [Fintype α] [DecidableEq β] (w : α → ℂ) (F : α → β) (b : β) :
    (cpush w F b).re = pushforward (fun a => (w a).re) F b := by
  simp only [cpush, pushforward, Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : F a = b <;> simp [h]

/-! ## Generic finite-sum toolkit, complex weights -/

section Generic

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem sum_pi_prod {A : κ → Type*} [∀ k, Fintype (A k)] (f : ∀ k, A k → ℂ) :
    (∑ x : (k : κ) → A k, ∏ k, f k (x k)) = ∏ k, ∑ a, f k a := by
  have h := Finset.prod_univ_sum (fun k => (univ : Finset (A k))) f
  rw [Fintype.piFinset_univ] at h
  exact h.symm

omit [DecidableEq κ] in
theorem ite_funext_prod {B : κ → Type*} [∀ k, DecidableEq (B k)] (f g : ∀ k, B k) :
    (if f = g then (1 : ℂ) else 0) = ∏ k, (if f k = g k then (1 : ℂ) else 0) := by
  by_cases h : f = g
  · subst h; simp
  · rw [ite_eq_right h]
    obtain ⟨k, hk⟩ := Function.ne_iff.mp h
    exact (Finset.prod_eq_zero (mem_univ k) (ite_eq_right hk)).symm

theorem sum_dprod_sel {A B : κ → Type*} [∀ k, Fintype (A k)] [∀ k, DecidableEq (B k)]
    (W : ∀ k, A k → ℂ) (sel : ∀ k, A k → B k) (y : ∀ k, B k) :
    (∑ x : (k : κ) → A k, (if (fun k => sel k (x k)) = y then (1 : ℂ) else 0) * ∏ k, W k (x k))
      = ∏ k, ∑ a, (if sel k a = y k then (1 : ℂ) else 0) * W k a := by
  rw [← sum_pi_prod (fun k a => (if sel k a = y k then (1 : ℂ) else 0) * W k a)]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [ite_funext_prod (fun k => sel k (x k)) y, Finset.prod_mul_distrib]

end Generic

section Push

variable {α β γ : Type*} [Fintype α] [Fintype β] [DecidableEq β] [DecidableEq γ]

theorem sum_mul_comp (w : α → ℂ) (F : α → β) (G : β → ℂ) :
    ∑ a, w a * G (F a) = ∑ b, cpush w F b * G b := by
  simp only [cpush, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single (F a)]
  · simp
  · exact fun b _ hb => by rw [ite_eq_right (Ne.symm hb), zero_mul]
  · intro h; exact absurd (mem_univ (F a)) h

omit [Fintype β] in
theorem cpush_comp_equiv (w : α → ℂ) (F : α → β) (E : β ≃ γ) :
    cpush w (fun a => E (F a)) = fun c => cpush w F (E.symm c) := by
  funext c
  simp only [cpush, ← Equiv.eq_symm_apply]

omit [Fintype β] in
theorem cpush_mix {ι : Type*} [Fintype ι] (c : ι → ℂ) (ν : ι → α → ℂ) (F : α → β) :
    cpush (fun a => ∑ i, c i * ν i a) F = fun b => ∑ i, c i * cpush (ν i) F b := by
  funext b
  simp only [cpush, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : F a = b <;> simp [h]

end Push

/-! ## Marginals of a product weight along an injective selection -/

theorem cpush_prodLaw_sel {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] {w : ι → Bool → ℂ} (hw : ∀ i, ∑ b, w i b = 1) {ν : κ → ι}
    (hν : Function.Injective ν) :
    cpush (cprodLaw w) (fun x k => x (ν k)) = cprodLaw (fun k => w (ν k)) := by
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
      (if (fun k => x (ν k)) = c then (1 : ℂ) else 0)
        = ∏ i ∈ I, (if x i = c' i then (1 : ℂ) else 0) := by
    intro x
    rw [hI, Finset.prod_image (fun a _ b _ h => hν h)]
    rw [ite_funext_prod (fun k => x (ν k)) c]
    exact Finset.prod_congr rfl fun k _ => by rw [hc'ν k]
  have hstep : ∀ x : ι → Bool,
      (if (fun k => x (ν k)) = c then cprodLaw w x else 0)
        = ∏ i, (w i (x i) * (if i ∈ I then (if x i = c' i then (1 : ℂ) else 0) else 1)) := by
    intro x
    rw [Finset.prod_mul_distrib, Finset.prod_ite_mem, Finset.univ_inter, ← hind x]
    by_cases h : (fun k => x (ν k)) = c
    · rw [ite_eq_left h, ite_eq_left h, mul_one]; rfl
    · rw [ite_eq_right h, ite_eq_right h, mul_zero]
  simp only [cpush]
  rw [Finset.sum_congr rfl (fun x _ => hstep x),
    sum_pi_prod (fun (i : ι) (b : Bool) =>
      w i b * (if i ∈ I then (if b = c' i then (1 : ℂ) else 0) else 1))]
  have hsum : ∀ i : ι, (∑ b, w i b * (if i ∈ I then (if b = c' i then (1 : ℂ) else 0) else 1))
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

/-! ## Independence of functions of disjoint coordinate blocks -/

section DProd

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*} [∀ i, Fintype (A i)]
variable {w : ∀ i, A i → ℂ}

/-- The complex product weight of independent coordinates with dependent alphabets. -/
def dprod (w : ∀ i, A i → ℂ) (x : ∀ i, A i) : ℂ := ∏ i, w i (x i)

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

theorem sum_dprod_mul_mul (hw : ∀ i, ∑ a, w i a = 1) {I J : Finset ι} (hIJ : Disjoint I J)
    {φ ψ : (∀ i, A i) → ℂ}
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
    (fun q : ((∀ i, A i) × (∀ i, A i)) =>
      (dprod w q.1 * (φ q.1 * ψ q.1)) * dprod w q.2) hstep
  have e1 : (∑ x, dprod w x * φ x) * (∑ x, dprod w x * ψ x)
      = ∑ q : ((∀ i, A i) × (∀ i, A i)), (dprod w q.1 * φ q.1) * (dprod w q.2 * ψ q.2) := by
    simp only [Fintype.sum_prod_type]
    exact Finset.sum_mul_sum _ _ _ _
  have e2 : (∑ x, dprod w x * (φ x * ψ x)) * (∑ x, dprod w x)
      = ∑ q : ((∀ i, A i) × (∀ i, A i)), (dprod w q.1 * (φ q.1 * ψ q.1)) * dprod w q.2 := by
    simp only [Fintype.sum_prod_type]
    exact Finset.sum_mul_sum _ _ _ _
  rw [e1, hsum, ← e2, sum_dprod hw, mul_one]

theorem sum_dprod_prod (hw : ∀ i, ∑ a, w i a = 1) :
    ∀ {n : ℕ} (I : Fin n → Finset ι) (χ : Fin n → (∀ i, A i) → ℂ),
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

theorem sum_sel_coord {B : Type*} [Fintype B] [DecidableEq B] {n : Type*} [Fintype n]
    [DecidableEq n] (ρ : B → ℂ) (hρ : ∑ b, ρ b = 1) (r₀ : n) (b₀ : B) :
    ∑ v : n → B, (if v r₀ = b₀ then (1 : ℂ) else 0) * ∏ r, ρ (v r) = ρ b₀ := by
  have hstep : ∀ v : n → B, (if v r₀ = b₀ then (1 : ℂ) else 0) * ∏ r, ρ (v r)
      = ∏ r, (ρ (v r) * if r = r₀ then (if v r = b₀ then (1 : ℂ) else 0) else 1) := by
    intro v
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' univ r₀
      (fun r => if v r = b₀ then (1 : ℂ) else 0)]
    simp [mul_comm]
  rw [Finset.sum_congr rfl (fun v _ => hstep v),
    sum_pi_prod (fun (r : n) (b : B) => ρ b * if r = r₀ then (if b = b₀ then (1 : ℂ) else 0) else 1)]
  have hcol : ∀ r : n, (∑ b, ρ b * if r = r₀ then (if b = b₀ then (1 : ℂ) else 0) else 1)
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


/-! ## The complex-weighted model and its inflation witness -/

variable {Γ : PairGraph} {t : ℕ}

/-- A pair-source model with complex source weights and complex response weights. Only the
normalization `∑ μ e = 1` is required; positivity is not part of the algebra. -/
structure CModel (Γ : PairGraph) where
  /-- The latent alphabet of each source. -/
  L : Γ.Edge → Type
  fintypeL : ∀ e, Fintype (L e)
  /-- The complex weight of each source. -/
  μ : ∀ e, L e → ℂ
  /-- The complex weight of the outcome `false` at `v`. -/
  resp : ∀ v : Γ.V, ((e : Γ.inc v) → L e.1) → ℂ

attribute [instance] CModel.fintypeL

/-- A complex model is normalized when every source weight sums to one. -/
def CModel.Valid (M : CModel Γ) : Prop := ∀ e, ∑ a, M.μ e a = 1

/-- The observed complex law of a complex model. -/
def CModel.law (M : CModel Γ) : (Γ.V → Bool) → ℂ := fun w =>
  ∑ x : (∀ e : Γ.Edge, M.L e),
    (∏ e : Γ.Edge, M.μ e (x e)) * ∏ v : Γ.V, crespMass (M.resp v (fun e => x e.1)) (w v)

section Model

variable (M : CModel Γ)

/-- Latent configurations of the order-`t` inflation. -/
abbrev CCfg (M : CModel Γ) (t : ℕ) := (l : GLatent Γ t) → M.L l.1

/-- Latent configurations of the model itself. -/
abbrev CMCfg (M : CModel Γ) := (e : Γ.Edge) → M.L e

/-- The response weight of a copied observation under a copied latent configuration. -/
def cObsResp (o : GObs Γ t) (x : CCfg M t) : ℂ := M.resp o.1 (fun e => x (e.1, o.2 e))

/-- The conditional per-observation weights of the inflated model. -/
def cInflCond (x : CCfg M t) : GObs Γ t → Bool → ℂ := fun o b => crespMass (cObsResp M o x) b

/-- The weight of a copied latent configuration. -/
def ccfgW (t : ℕ) : CCfg M t → ℂ := dprod (fun (l : GLatent Γ t) a => M.μ l.1 a)

/-- The weight of a latent configuration of the model. -/
def cmcfgW : CMCfg M → ℂ := dprod (fun (e : Γ.Edge) a => M.μ e a)

/-- The order-`t` inflation witness of a complex model. -/
def cInflLaw (t : ℕ) : GAssign Γ t → ℂ :=
  fun ω => ∑ x : CCfg M t, ccfgW M t x * cprodLaw (cInflCond M x) ω

variable {M}

theorem cInflCond_sum (x : CCfg M t) (o : GObs Γ t) : ∑ b, cInflCond M x o b = 1 :=
  crespMass_sum _

theorem sum_ccfgW (hM : M.Valid) : ∑ x : CCfg M t, ccfgW M t x = 1 :=
  sum_dprod (fun l => hM l.1)

theorem sum_cprodLaw {ι : Type*} [Fintype ι] [DecidableEq ι] {w : ι → Bool → ℂ} (hw : ∀ i, ∑ b, w i b = 1) :
    ∑ x : ι → Bool, cprodLaw w x = 1 := by
  rw [show (∑ x : ι → Bool, cprodLaw w x) = ∏ i, ∑ b, w i b from sum_pi_prod _]
  exact Finset.prod_eq_one fun i _ => hw i

theorem cpush_cInflLaw {β : Type*} [DecidableEq β] (F : GAssign Γ t → β) :
    cpush (cInflLaw M t) F
      = fun b => ∑ x : CCfg M t, ccfgW M t x * cpush (cprodLaw (cInflCond M x)) F b := by
  funext b
  simp only [cInflLaw, cpush, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases h : F ω = b <;> simp [h]

/-- Marginalizing the copied latent configuration onto one copy of the original scenario. -/
theorem clatent_marginal (hM : M.Valid) (ι : Γ.Edge → Fin t) (F : CMCfg M → ℂ) :
    ∑ x : CCfg M t, ccfgW M t x * F (fun e => x (e, ι e)) = ∑ y : CMCfg M, cmcfgW M y * F y := by
  classical
  set E : CCfg M t ≃ ((e : Γ.Edge) → Fin t → M.L e) :=
    { toFun := fun x e r => x (e, r), invFun := fun u l => u l.1 l.2,
      left_inv := fun _ => rfl, right_inv := fun _ => rfl } with hE
  have h1 : ∑ x : CCfg M t, ccfgW M t x * F (fun e => x (e, ι e))
      = ∑ u : ((e : Γ.Edge) → Fin t → M.L e),
          dprod (fun (e : Γ.Edge) (v : Fin t → M.L e) => ∏ r, M.μ e (v r)) u
            * F (fun e => u e (ι e)) := by
    refine Fintype.sum_equiv E _ _ fun x => ?_
    congr 1
    exact Fintype.prod_prod_type (fun l : Γ.Edge × Fin t => M.μ l.1 (x l))
  rw [h1, sum_mul_comp]
  refine Finset.sum_congr rfl fun y _ => ?_
  congr 1
  have hpush : cpush (dprod (fun (e : Γ.Edge) (v : Fin t → M.L e) => ∏ r, M.μ e (v r)))
      (fun u e => u e (ι e)) y
      = ∑ u : ((e : Γ.Edge) → Fin t → M.L e),
          (if (fun e => u e (ι e)) = y then (1 : ℂ) else 0)
            * ∏ e, (fun (e : Γ.Edge) (v : Fin t → M.L e) => ∏ r, M.μ e (v r)) e (u e) := by
    simp only [cpush, dprod]
    refine Finset.sum_congr rfl fun u _ => ?_
    by_cases h : (fun e => u e (ι e)) = y <;> simp [h]
  rw [hpush, sum_dprod_sel (fun (e : Γ.Edge) (v : Fin t → M.L e) => ∏ r, M.μ e (v r))
    (fun (e : Γ.Edge) (v : Fin t → M.L e) => v (ι e)) y]
  exact Finset.prod_congr rfl fun e _ => sum_sel_coord (M.μ e) (hM e) (ι e) (y e)

end Model

section Witness

variable {M : CModel Γ}

/-- Relabelling copy indices, as a bijection of copied latent configurations. -/
def cCfgPerm (M : CModel Γ) (π : Γ.Edge → Equiv.Perm (Fin t)) : CCfg M t ≃ CCfg M t where
  toFun y := fun l => y (l.1, π l.1 l.2)
  invFun y := fun l => y (l.1, (π l.1).symm l.2)
  left_inv x := by
    funext l; obtain ⟨e, r⟩ := l
    change x (e, (π e) ((π e).symm r)) = x (e, r)
    rw [Equiv.apply_symm_apply]
  right_inv x := by
    funext l; obtain ⟨e, r⟩ := l
    change x (e, (π e).symm ((π e) r)) = x (e, r)
    rw [Equiv.symm_apply_apply]

theorem sum_cInflLaw (hM : M.Valid) : ∑ ω : GAssign Γ t, cInflLaw M t ω = 1 := by
  calc ∑ ω : GAssign Γ t, cInflLaw M t ω
      = ∑ x : CCfg M t, ccfgW M t x * ∑ ω : GAssign Γ t, cprodLaw (cInflCond M x) ω := by
        simp only [cInflLaw, Finset.mul_sum]
        rw [Finset.sum_comm]
    _ = ∑ x : CCfg M t, ccfgW M t x := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [sum_cprodLaw (fun o => cInflCond_sum x o), mul_one]
    _ = 1 := sum_ccfgW hM

/-- The complex witness is symmetric under per-source relabelling of the copies. -/
theorem csymmetric_cInflLaw (M : CModel Γ) (t : ℕ) (π : Γ.Edge → Equiv.Perm (Fin t))
    (ω : GAssign Γ t) : cInflLaw M t (gRelabel π ω) = cInflLaw M t ω := by
  rw [show cInflLaw M t (gRelabel π ω)
      = ∑ x : CCfg M t, ccfgW M t x * cprodLaw (cInflCond M x) (gRelabel π ω) from rfl,
    ← Equiv.sum_comp (cCfgPerm M π)
      (fun x => ccfgW M t x * cprodLaw (cInflCond M x) (gRelabel π ω))]
  refine Finset.sum_congr rfl fun y _ => ?_
  have h1 : ccfgW M t (cCfgPerm M π y) = ccfgW M t y :=
    Equiv.prod_comp (Sound.gLatentPerm π) (fun l => M.μ l.1 (y l))
  have h2 : cprodLaw (cInflCond M (cCfgPerm M π y)) (gRelabel π ω) = cprodLaw (cInflCond M y) ω :=
    Equiv.prod_comp (Sound.gObsPerm π) (fun o => crespMass (cObsResp M o y) (ω o))
  rw [h1, h2]

/-- The marginal of the complex witness on a block of copied observations. -/
theorem cInflLaw_block (S : Finset (GObs Γ t)) (φ : S → Bool) :
    cpush (cInflLaw M t) (gRestrict S) φ
      = ∑ x : CCfg M t, ccfgW M t x * ∏ o : S, crespMass (cObsResp M o.1 x) (φ o) := by
  rw [cpush_cInflLaw]
  refine Finset.sum_congr rfl fun x _ => ?_
  have h2 : cpush (cprodLaw (cInflCond M x)) (gRestrict S)
      = cprodLaw (fun k : S => cInflCond M x (k : GObs Γ t)) :=
    cpush_prodLaw_sel (ν := fun k : S => (k : GObs Γ t))
      (fun o => cInflCond_sum x o) Subtype.val_injective
  rw [h2]
  rfl

/-- Every injectable set carries the corresponding marginal of the complex model's law. -/
theorem cInflLaw_injectable (hM : M.Valid) {S : Finset (GObs Γ t)} (hS : GInjectable S) :
    cpush (cInflLaw M t) (gRestrict S) = cpush M.law (gPartyRead S) := by
  obtain ⟨ι, hι⟩ := hS
  funext φ
  set F : CMCfg M → ℂ :=
    fun y => ∏ o : S, crespMass (M.resp o.1.1 (fun e => y e.1)) (φ o) with hF
  have hresp : ∀ (x : CCfg M t) (o : S),
      cObsResp M o.1 x = M.resp o.1.1 (fun e => x (e.1, ι e.1)) :=
    fun x o => congrArg (M.resp o.1.1) (funext fun e => by rw [Sound.copySet_snd (hι o.2) e])
  have hL : cpush (cInflLaw M t) (gRestrict S) φ = ∑ y : CMCfg M, cmcfgW M y * F y := by
    rw [cInflLaw_block S φ, ← clatent_marginal hM ι F]
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 1
    exact Finset.prod_congr rfl fun o _ => by rw [hresp x o]
  have hR : cpush M.law (gPartyRead S) φ = ∑ y : CMCfg M, cmcfgW M y * F y := by
    rw [show M.law = fun w => ∑ y : CMCfg M,
        cmcfgW M y * cprodLaw (fun v b => crespMass (M.resp v (fun e => y e.1)) b) w from rfl,
      cpush_mix]
    refine Finset.sum_congr rfl fun y _ => ?_
    have h2 : cpush (cprodLaw (fun v b => crespMass (M.resp v (fun e => y e.1)) b))
        (gPartyRead S)
        = cprodLaw (fun k : S => (fun v b => crespMass (M.resp v (fun e => y e.1)) b) k.1.1) :=
      cpush_prodLaw_sel (ν := fun k : S => (k : GObs Γ t).1)
        (fun v => crespMass_sum _) (Sound.vertex_injective ⟨ι, hι⟩)
    rw [h2]
    rfl
  rw [hL, hR]

/-- The complex witness satisfies every ancestral-independence prescription. -/
theorem cInflLaw_ai (hM : M.Valid) (n : ℕ) (S : Fin n → Finset (GObs Γ t))
    (hinj : ∀ m, GInjectable (S m))
    (hai : ∀ m m', m ≠ m' → GAncestrallyIndependent (S m) (S m')) :
    cpush (cInflLaw M t) (fun ω m => gRestrict (S m) ω)
      = fun φ : ∀ m : Fin n, (S m) → Bool => ∏ m : Fin n, cpush M.law (gPartyRead (S m)) (φ m) := by
  have hdisj : ∀ m m', m ≠ m' → Disjoint (S m) (S m') :=
    fun m m' h => Sound.disjoint_of_gAI (hai m m' h)
  funext φ
  have h1 : cpush (cInflLaw M t) (fun ω m => gRestrict (S m) ω) φ
      = cpush (cInflLaw M t)
          (fun (ω : GAssign Γ t) (p : Σ m : Fin n, ↥(S m)) => ω (p.2 : GObs Γ t))
          ((Sound.sigCurry S).symm φ) :=
    congrFun (cpush_comp_equiv (cInflLaw M t)
      (fun (ω : GAssign Γ t) (p : Σ m : Fin n, ↥(S m)) => ω (p.2 : GObs Γ t)) (Sound.sigCurry S)) φ
  have h2 : ∀ x : CCfg M t,
      cpush (cprodLaw (cInflCond M x))
          (fun (ω : GAssign Γ t) (p : Σ m : Fin n, ↥(S m)) => ω (p.2 : GObs Γ t))
          ((Sound.sigCurry S).symm φ)
        = ∏ m : Fin n, ∏ o : ↥(S m), crespMass (cObsResp M o.1 x) (φ m o) := by
    intro x
    rw [cpush_prodLaw_sel (ν := fun p : Σ m : Fin n, ↥(S m) => (p.2 : GObs Γ t))
      (fun o => cInflCond_sum x o) (Sound.sigma_val_injective hdisj)]
    exact Fintype.prod_sigma
      (fun p : Σ m : Fin n, ↥(S m) => crespMass (cObsResp M (p.2 : GObs Γ t) x) (φ p.1 p.2))
  have hdep : ∀ (m : Fin n) (x y : CCfg M t),
      (∀ l ∈ gAncestorsOf (S m), x l = y l) →
        (∏ o : ↥(S m), crespMass (cObsResp M o.1 x) (φ m o))
          = ∏ o : ↥(S m), crespMass (cObsResp M o.1 y) (φ m o) := by
    intro m x y hxy
    refine Finset.prod_congr rfl fun o _ => ?_
    congr 1
    exact congrArg (M.resp o.1.1) (funext fun e => hxy (e.1, o.1.2 e) (Sound.mem_gAncestorsOf o.2 e))
  have h3 : ∑ x : CCfg M t,
        ccfgW M t x * ∏ m : Fin n, ∏ o : ↥(S m), crespMass (cObsResp M o.1 x) (φ m o)
      = ∏ m : Fin n, ∑ x : CCfg M t,
          ccfgW M t x * ∏ o : ↥(S m), crespMass (cObsResp M o.1 x) (φ m o) :=
    sum_dprod_prod (fun l => hM l.1) (fun m => gAncestorsOf (S m)) _
      (fun m m' hmm => hai m m' hmm) hdep
  rw [h1, cpush_cInflLaw]
  simp only [h2]
  rw [h3]
  refine Finset.prod_congr rfl fun m _ => ?_
  rw [← cInflLaw_block (S m) (φ m), cInflLaw_injectable hM (hinj m)]


/-- The `t`-fold tensor power of a complex target law. -/
def cTensorPow (t : ℕ) (P : (Γ.V → Bool) → ℂ) : (Fin t → (Γ.V → Bool)) → ℂ :=
  fun v => ∏ r : Fin t, P (v r)

/-- The diagonal law of the complex witness is the tensor power of the model's law. -/
theorem cInflLaw_diag (_hM : M.Valid) :
    cpush (cInflLaw M t) readDiag = cTensorPow t M.law := by
  funext w
  have h1 : cpush (cInflLaw M t) readDiag w
      = cpush (cInflLaw M t)
          (fun (ω : GAssign Γ t) (p : Fin t × Γ.V) => ω (Sound.diagObs Γ t p))
          (fun p => w p.1 p.2) := by
    rw [Sound.readDiag_factor]
    exact congrFun (cpush_comp_equiv (cInflLaw M t)
      (fun (ω : GAssign Γ t) (p : Fin t × Γ.V) => ω (Sound.diagObs Γ t p))
      (Equiv.curry (Fin t) Γ.V Bool)) w
  have h2 : ∀ x : CCfg M t,
      cpush (cprodLaw (cInflCond M x))
          (fun (ω : GAssign Γ t) (p : Fin t × Γ.V) => ω (Sound.diagObs Γ t p))
          (fun p => w p.1 p.2)
        = ∏ r : Fin t, ∏ v : Γ.V, crespMass (M.resp v (fun e => x (e.1, r))) (w r v) := by
    intro x
    rw [cpush_prodLaw_sel (ν := Sound.diagObs Γ t) (fun o => cInflCond_sum x o)
      (Sound.diagObs_injective Γ t)]
    exact Fintype.prod_prod_type
      (fun p : Fin t × Γ.V => crespMass (cObsResp M (Sound.diagObs Γ t p) x) (w p.1 p.2))
  set E2 : CCfg M t ≃ (Fin t → CMCfg M) :=
    { toFun := fun x r e => x (e, r), invFun := fun z l => z l.2 l.1,
      left_inv := fun _ => rfl, right_inv := fun _ => rfl } with hE2
  have h3 : ∑ x : CCfg M t,
        ccfgW M t x * ∏ r : Fin t, ∏ v : Γ.V, crespMass (M.resp v (fun e => x (e.1, r))) (w r v)
      = ∑ z : Fin t → CMCfg M, ∏ r : Fin t,
          (cmcfgW M (z r) * ∏ v : Γ.V, crespMass (M.resp v (fun e => z r e.1)) (w r v)) := by
    refine Fintype.sum_equiv E2 _ _ fun x => ?_
    rw [Finset.prod_mul_distrib]
    congr 1
    calc ccfgW M t x = ∏ e : Γ.Edge, ∏ r : Fin t, M.μ e (x (e, r)) :=
          Fintype.prod_prod_type (fun l : Γ.Edge × Fin t => M.μ l.1 (x l))
      _ = ∏ r : Fin t, ∏ e : Γ.Edge, M.μ e (x (e, r)) := Finset.prod_comm
  rw [h1, cpush_cInflLaw]
  simp only [h2]
  rw [h3, sum_pi_prod (fun (r : Fin t) (y : CMCfg M) =>
    cmcfgW M y * ∏ v : Γ.V, crespMass (M.resp v (fun e => y e.1)) (w r v))]
  rfl

end Witness


/-! ## From a complex model to the real AI feasible set -/

theorem cpush_ofReal {α β : Type*} [Fintype α] [DecidableEq β] (w : α → ℝ) (F : α → β) (b : β) :
    cpush (fun a => ((w a : ℝ) : ℂ)) F b = ((pushforward w F b : ℝ) : ℂ) := by
  simp only [cpush, pushforward, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : F a = b <;> simp [h]

/-- The real part of a complex inflation witness whose model law is real and whose weights
have nonnegative real part discharges all five obligations of `GAIFeasible`. -/
theorem gAIFeasible_of_cModel (M : CModel Γ) (t : ℕ) (P : GTarget Γ) (hM : M.Valid)
    (hre : ∀ ω : GAssign Γ t, 0 ≤ (cInflLaw M t ω).re)
    (hlaw : ∀ w, M.law w = ((P w : ℝ) : ℂ)) :
    GAIFeasible Γ t P := by
  classical
  set Δ : GAssign Γ t → ℝ := fun ω => (cInflLaw M t ω).re with hΔ
  have hMlaw : M.law = fun w => ((P w : ℝ) : ℂ) := funext hlaw
  have hpushΔ : ∀ {β : Type} [Fintype β] [DecidableEq β] (F : GAssign Γ t → β),
      pushforward Δ F = fun b => (cpush (cInflLaw M t) F b).re := by
    intro β _ _ F
    funext b
    rw [cpush_re]
  refine ⟨Δ, ⟨hre, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [show (∑ ω : GAssign Γ t, Δ ω) = (∑ ω : GAssign Γ t, cInflLaw M t ω).re from
      (Complex.re_sum _ _).symm, sum_cInflLaw hM]
    simp
  · intro π ω
    exact congrArg Complex.re (csymmetric_cInflLaw M t π ω)
  · rw [hpushΔ readDiag, cInflLaw_diag hM]
    funext w
    rw [show cTensorPow t M.law w = ((gTensorPow t P w : ℝ) : ℂ) from by
      simp only [cTensorPow, gTensorPow, hMlaw, Complex.ofReal_prod]]
    simp
  · intro S hS
    rw [hpushΔ (gRestrict S), cInflLaw_injectable hM hS]
    funext φ
    rw [hMlaw, cpush_ofReal]
    simp
  · intro n S hinj hai
    rw [hpushΔ (fun ω m => gRestrict (S m) ω), cInflLaw_ai hM n S hinj hai]
    funext φ
    have : ∀ m : Fin n, cpush M.law (gPartyRead (S m)) (φ m)
        = ((pushforward P (gPartyRead (S m)) (φ m) : ℝ) : ℂ) := by
      intro m; rw [hMlaw, cpush_ofReal]
    simp only [this, ← Complex.ofReal_prod, Complex.ofReal_re]



/-! ## The five-path complex model -/

theorem ne01_12 : (E01 : fivePathGraph.Edge) ≠ E12 := by decide
theorem ne01_23 : (E01 : fivePathGraph.Edge) ≠ E23 := by decide
theorem ne01_34 : (E01 : fivePathGraph.Edge) ≠ E34 := by decide
theorem ne12_23 : (E12 : fivePathGraph.Edge) ≠ E23 := by decide
theorem ne12_34 : (E12 : fivePathGraph.Edge) ≠ E34 := by decide
theorem ne23_34 : (E23 : fivePathGraph.Edge) ≠ E34 := by decide

theorem memE01_0 : (E01 : fivePathGraph.Edge) ∈ fivePathGraph.inc (0 : Fin 5) := by decide
theorem memE01_1 : (E01 : fivePathGraph.Edge) ∈ fivePathGraph.inc (1 : Fin 5) := by decide
theorem memE12_1 : (E12 : fivePathGraph.Edge) ∈ fivePathGraph.inc (1 : Fin 5) := by decide
theorem memE12_2 : (E12 : fivePathGraph.Edge) ∈ fivePathGraph.inc (2 : Fin 5) := by decide
theorem memE23_2 : (E23 : fivePathGraph.Edge) ∈ fivePathGraph.inc (2 : Fin 5) := by decide
theorem memE23_3 : (E23 : fivePathGraph.Edge) ∈ fivePathGraph.inc (3 : Fin 5) := by decide
theorem memE34_3 : (E34 : fivePathGraph.Edge) ∈ fivePathGraph.inc (3 : Fin 5) := by decide
theorem memE34_4 : (E34 : fivePathGraph.Edge) ∈ fivePathGraph.inc (4 : Fin 5) := by decide

/-- The complex source weight of the five-path witness: the endpoint sources `E01` and `E34`
are fair, the source `E12` carries the formal weight `(1 + iγu)/2` on its auxiliary sign and
`E23` the conjugate weight `(1 - iγv)/2`. Every latent alphabet is `Bool × Bool`: a fair mask
and an auxiliary sign (the sign is unused on the endpoint sources). -/
noncomputable def pmu (γ : ℝ) (e : fivePathGraph.Edge) (a : Bool × Bool) : ℂ :=
  if e = E12 then (1 + Complex.I * ((γ : ℝ) : ℂ) * ((sgn a.2 : ℝ) : ℂ)) / 4
  else if e = E23 then (1 - Complex.I * ((γ : ℝ) : ℂ) * ((sgn a.2 : ℝ) : ℂ)) / 4
  else 1 / 4

@[simp] theorem pmu_E01 (γ : ℝ) (a : Bool × Bool) : pmu γ E01 a = 1 / 4 := by
  simp [pmu, ne01_12, ne01_23]
@[simp] theorem pmu_E12 (γ : ℝ) (a : Bool × Bool) :
    pmu γ E12 a = (1 + Complex.I * ((γ : ℝ) : ℂ) * ((sgn a.2 : ℝ) : ℂ)) / 4 := by simp [pmu]
@[simp] theorem pmu_E23 (γ : ℝ) (a : Bool × Bool) :
    pmu γ E23 a = (1 - Complex.I * ((γ : ℝ) : ℂ) * ((sgn a.2 : ℝ) : ℂ)) / 4 := by
  simp [pmu, ne12_23.symm]
@[simp] theorem pmu_E34 (γ : ℝ) (a : Bool × Bool) : pmu γ E34 a = 1 / 4 := by
  simp [pmu, ne12_34.symm, ne23_34.symm]

theorem pmu_sum (γ : ℝ) (e : fivePathGraph.Edge) : ∑ a : Bool × Bool, pmu γ e a = 1 := by
  rcases edge_cases e with h | h | h | h <;> subst h <;>
    simp [Fintype.sum_prod_type, sgn] <;> ring

/-- Reading the value of a named source out of an incidence-indexed configuration. -/
def rdE (v : fivePathGraph.V) (c : (e : fivePathGraph.inc v) → Bool × Bool)
    (e : fivePathGraph.Edge) : Bool × Bool :=
  if h : e ∈ fivePathGraph.inc v then c ⟨e, h⟩ else (false, false)

/-- The response weight of the vertex `v` given the values `X, L, R, Z` of the four sources:
`A = X`, `B = r u^X`, `C = rs` when `u = v` and fair otherwise, `D = s v^Z`, `E = Z`. The
first component of a latent value is the fair mask, the second the auxiliary sign. -/
noncomputable def pfR (v : Fin 5) (X L R Z : Bool × Bool) : ℝ :=
  if v = 0 then (if X.1 then 0 else 1)
  else if v = 1 then (if xor L.1 (X.1 && L.2) then 0 else 1)
  else if v = 2 then (if L.2 = R.2 then (if xor L.1 R.1 then 0 else 1) else 1 / 2)
  else if v = 3 then (if xor R.1 (Z.1 && R.2) then 0 else 1)
  else (if Z.1 then 0 else 1)

theorem pfR_mem (v : Fin 5) (X L R Z : Bool × Bool) :
    0 ≤ pfR v X L R Z ∧ pfR v X L R Z ≤ 1 := by
  unfold pfR; split_ifs <;> norm_num

/-- The real response weight of the five-path witness. -/
noncomputable def prespR (v : Fin 5) (c : (e : fivePathGraph.inc v) → Bool × Bool) : ℝ :=
  pfR v (rdE v c E01) (rdE v c E12) (rdE v c E23) (rdE v c E34)

theorem prespR_mem (v : Fin 5) (c : (e : fivePathGraph.inc v) → Bool × Bool) :
    0 ≤ prespR v c ∧ prespR v c ≤ 1 := pfR_mem _ _ _ _ _

/-- The five-path complex model at auxiliary amplitude `γ`. -/
noncomputable def PM (γ : ℝ) : CModel fivePathGraph where
  L := fun _ => Bool × Bool
  fintypeL := fun _ => inferInstance
  μ := pmu γ
  resp := fun v c => ((prespR v c : ℝ) : ℂ)

theorem PM_valid (γ : ℝ) : (PM γ).Valid := fun e => pmu_sum γ e

theorem presp0 (x : fivePathGraph.Edge → Bool × Bool) :
    prespR (0 : Fin 5) (fun e : fivePathGraph.inc (0 : Fin 5) => x e.1)
      = (if (x E01).1 then 0 else 1) := by
  simp [prespR, pfR, rdE, memE01_0]

theorem presp1 (x : fivePathGraph.Edge → Bool × Bool) :
    prespR (1 : Fin 5) (fun e : fivePathGraph.inc (1 : Fin 5) => x e.1)
      = (if xor (x E12).1 ((x E01).1 && (x E12).2) then 0 else 1) := by
  simp [prespR, pfR, rdE, memE01_1, memE12_1]

theorem presp2 (x : fivePathGraph.Edge → Bool × Bool) :
    prespR (2 : Fin 5) (fun e : fivePathGraph.inc (2 : Fin 5) => x e.1)
      = (if (x E12).2 = (x E23).2 then (if xor (x E12).1 (x E23).1 then 0 else 1) else 1 / 2) := by
  simp [prespR, pfR, rdE, memE12_2, memE23_2]

theorem presp3 (x : fivePathGraph.Edge → Bool × Bool) :
    prespR (3 : Fin 5) (fun e : fivePathGraph.inc (3 : Fin 5) => x e.1)
      = (if xor (x E23).1 ((x E34).1 && (x E23).2) then 0 else 1) := by
  simp [prespR, pfR, rdE, memE23_3, memE34_3]

theorem presp4 (x : fivePathGraph.Edge → Bool × Bool) :
    prespR (4 : Fin 5) (fun e : fivePathGraph.inc (4 : Fin 5) => x e.1)
      = (if (x E34).1 then 0 else 1) := by
  simp [prespR, pfR, rdE, memE34_4]



/-! ### The observed law of the five-path complex model -/

theorem PM_resp (γ : ℝ) (v : Fin 5) (c : (e : fivePathGraph.inc v) → Bool × Bool) :
    (PM γ).resp v c = ((prespR v c : ℝ) : ℂ) := rfl

theorem crespMass_bool (b b' : Bool) :
    crespMass (((if b then 0 else 1 : ℝ)) : ℂ) b' = if b' = b then 1 else 0 := by
  cases b <;> cases b' <;> simp [crespMass]

theorem crespMass_ite (p : Prop) [Decidable p] (b b' : Bool) :
    crespMass ((((if p then (if b then 0 else 1) else 1 / 2 : ℝ))) : ℂ) b'
      = if p then (if b' = b then 1 else 0) else 1 / 2 := by
  by_cases hp : p
  · simp only [ite_eq_left hp]; exact crespMass_bool b b'
  · simp only [ite_eq_right hp]; cases b' <;> norm_num [crespMass]

/-- The latent tuple of the four sources. -/
def eTup : (fivePathGraph.Edge → Bool × Bool)
    ≃ ((Bool × Bool) × (Bool × Bool) × (Bool × Bool) × (Bool × Bool)) where
  toFun x := (x E01, x E12, x E23, x E34)
  invFun p := fun e =>
    if e = E01 then p.1 else if e = E12 then p.2.1 else if e = E23 then p.2.2.1 else p.2.2.2
  left_inv x := by
    funext e
    rcases edge_cases e with h | h | h | h <;> subst h <;>
      simp [ne01_12.symm, ne01_23.symm, ne12_23.symm, ne01_34.symm, ne12_34.symm, ne23_34.symm]
  right_inv p := by
    simp [ne01_12.symm, ne01_23.symm, ne12_23.symm, ne01_34.symm, ne12_34.symm, ne23_34.symm]

/-- One term of the observed law of the five-path model, as a function of the four source
values `X = (x, ·)`, `L = (r, u)`, `R = (s, v)`, `Z = (z, ·)`. -/
noncomputable def lawSummand (γ : ℝ) (w : Fin 5 → Bool) (X L R Z : Bool × Bool) : ℂ :=
  (pmu γ E01 X * pmu γ E12 L * pmu γ E23 R * pmu γ E34 Z)
    * ((if w 0 = X.1 then 1 else 0)
      * (if w 1 = xor L.1 (X.1 && L.2) then 1 else 0)
      * (if L.2 = R.2 then (if w 2 = xor L.1 R.1 then 1 else 0) else 1 / 2)
      * (if w 3 = xor R.1 (Z.1 && R.2) then 1 else 0)
      * (if w 4 = Z.1 then 1 else 0))

theorem law_summand_eq (γ : ℝ) (w : fivePathGraph.V → Bool)
    (x : fivePathGraph.Edge → Bool × Bool) :
    (∏ e : fivePathGraph.Edge, pmu γ e (x e))
        * ∏ v : fivePathGraph.V, crespMass ((PM γ).resp v (fun e => x e.1)) (w v)
      = lawSummand γ w (x E01) (x E12) (x E23) (x E34) := by
  rw [prod_edge (fun e => pmu γ e (x e)), prod_vert]
  unfold lawSummand
  congr 1
  rw [PM_resp, PM_resp, PM_resp, PM_resp, PM_resp, presp0, presp1, presp2, presp3, presp4,
    crespMass_bool, crespMass_bool, crespMass_ite, crespMass_bool, crespMass_bool]

private theorem lawSum_00000 (γ : ℝ) :
    ∑ p : (Bool × Bool) × (Bool × Bool) × (Bool × Bool) × (Bool × Bool),
        lawSummand γ ![false, false, false, false, false] p.1 p.2.1 p.2.2.1 p.2.2.2
      = ((fivePathTarget (γ ^ 2) ![false, false, false, false, false] : ℝ) : ℂ) := by
  simp only [lawSummand, Fintype.sum_prod_type, Fintype.sum_bool, pmu_E01, pmu_E12, pmu_E23,
    pmu_E34, sgn, fivePathTarget]
  norm_num
  all_goals try rw [Complex.ext_iff]
  all_goals try constructor
  all_goals try simp [← Complex.ofReal_pow]
  all_goals ring

private theorem lawSum_00001 (γ : ℝ) :
    ∑ p : (Bool × Bool) × (Bool × Bool) × (Bool × Bool) × (Bool × Bool),
        lawSummand γ ![false, false, false, false, true] p.1 p.2.1 p.2.2.1 p.2.2.2
      = ((fivePathTarget (γ ^ 2) ![false, false, false, false, true] : ℝ) : ℂ) := by
  simp only [lawSummand, Fintype.sum_prod_type, Fintype.sum_bool, pmu_E01, pmu_E12, pmu_E23,
    pmu_E34, sgn, fivePathTarget]
  norm_num
  all_goals try rw [Complex.ext_iff]
  all_goals try constructor
  all_goals try simp [← Complex.ofReal_pow]
  all_goals ring

private theorem lawSum_00010 (γ : ℝ) :
    ∑ p : (Bool × Bool) × (Bool × Bool) × (Bool × Bool) × (Bool × Bool),
        lawSummand γ ![false, false, false, true, false] p.1 p.2.1 p.2.2.1 p.2.2.2
      = ((fivePathTarget (γ ^ 2) ![false, false, false, true, false] : ℝ) : ℂ) := by
  simp only [lawSummand, Fintype.sum_prod_type, Fintype.sum_bool, pmu_E01, pmu_E12, pmu_E23,
    pmu_E34, sgn, fivePathTarget]
  norm_num
  all_goals try rw [Complex.ext_iff]
  all_goals try constructor
  all_goals try simp [← Complex.ofReal_pow]
  all_goals ring

private theorem lawSum_00011 (γ : ℝ) :
    ∑ p : (Bool × Bool) × (Bool × Bool) × (Bool × Bool) × (Bool × Bool),
        lawSummand γ ![false, false, false, true, true] p.1 p.2.1 p.2.2.1 p.2.2.2
      = ((fivePathTarget (γ ^ 2) ![false, false, false, true, true] : ℝ) : ℂ) := by
  simp only [lawSummand, Fintype.sum_prod_type, Fintype.sum_bool, pmu_E01, pmu_E12, pmu_E23,
    pmu_E34, sgn, fivePathTarget]
  norm_num
  all_goals try rw [Complex.ext_iff]
  all_goals try constructor
  all_goals try simp [← Complex.ofReal_pow]
  all_goals ring

private theorem lawSum_00100 (γ : ℝ) :
    ∑ p : (Bool × Bool) × (Bool × Bool) × (Bool × Bool) × (Bool × Bool),
        lawSummand γ ![false, false, true, false, false] p.1 p.2.1 p.2.2.1 p.2.2.2
      = ((fivePathTarget (γ ^ 2) ![false, false, true, false, false] : ℝ) : ℂ) := by
  simp only [lawSummand, Fintype.sum_prod_type, Fintype.sum_bool, pmu_E01, pmu_E12, pmu_E23,
    pmu_E34, sgn, fivePathTarget]
  norm_num
  all_goals try rw [Complex.ext_iff]
  all_goals try constructor
  all_goals try simp [← Complex.ofReal_pow]
  all_goals ring

private theorem lawSum_00101 (γ : ℝ) :
    ∑ p : (Bool × Bool) × (Bool × Bool) × (Bool × Bool) × (Bool × Bool),
        lawSummand γ ![false, false, true, false, true] p.1 p.2.1 p.2.2.1 p.2.2.2
      = ((fivePathTarget (γ ^ 2) ![false, false, true, false, true] : ℝ) : ℂ) := by
  simp only [lawSummand, Fintype.sum_prod_type, Fintype.sum_bool, pmu_E01, pmu_E12, pmu_E23,
    pmu_E34, sgn, fivePathTarget]
  norm_num
  all_goals try rw [Complex.ext_iff]
  all_goals try constructor
  all_goals try simp [← Complex.ofReal_pow]
  all_goals ring

private theorem lawSum_00110 (γ : ℝ) :
    ∑ p : (Bool × Bool) × (Bool × Bool) × (Bool × Bool) × (Bool × Bool),
        lawSummand γ ![false, false, true, true, false] p.1 p.2.1 p.2.2.1 p.2.2.2
      = ((fivePathTarget (γ ^ 2) ![false, false, true, true, false] : ℝ) : ℂ) := by
  simp only [lawSummand, Fintype.sum_prod_type, Fintype.sum_bool, pmu_E01, pmu_E12, pmu_E23,
    pmu_E34, sgn, fivePathTarget]
  norm_num
  all_goals try rw [Complex.ext_iff]
  all_goals try constructor
  all_goals try simp [← Complex.ofReal_pow]
  all_goals ring

private theorem lawSum_00111 (γ : ℝ) :
    ∑ p : (Bool × Bool) × (Bool × Bool) × (Bool × Bool) × (Bool × Bool),
        lawSummand γ ![false, false, true, true, true] p.1 p.2.1 p.2.2.1 p.2.2.2
      = ((fivePathTarget (γ ^ 2) ![false, false, true, true, true] : ℝ) : ℂ) := by
  simp only [lawSummand, Fintype.sum_prod_type, Fintype.sum_bool, pmu_E01, pmu_E12, pmu_E23,
    pmu_E34, sgn, fivePathTarget]
  norm_num
  all_goals try rw [Complex.ext_iff]
  all_goals try constructor
  all_goals try simp [← Complex.ofReal_pow]
  all_goals ring

private theorem lawSum_01000 (γ : ℝ) :
    ∑ p : (Bool × Bool) × (Bool × Bool) × (Bool × Bool) × (Bool × Bool),
        lawSummand γ ![false, true, false, false, false] p.1 p.2.1 p.2.2.1 p.2.2.2
      = ((fivePathTarget (γ ^ 2) ![false, true, false, false, false] : ℝ) : ℂ) := by
  simp only [lawSummand, Fintype.sum_prod_type, Fintype.sum_bool, pmu_E01, pmu_E12, pmu_E23,
    pmu_E34, sgn, fivePathTarget]
  norm_num
  all_goals try rw [Complex.ext_iff]
  all_goals try constructor
  all_goals try simp [← Complex.ofReal_pow]
  all_goals ring

private theorem lawSum_01001 (γ : ℝ) :
    ∑ p : (Bool × Bool) × (Bool × Bool) × (Bool × Bool) × (Bool × Bool),
        lawSummand γ ![false, true, false, false, true] p.1 p.2.1 p.2.2.1 p.2.2.2
      = ((fivePathTarget (γ ^ 2) ![false, true, false, false, true] : ℝ) : ℂ) := by
  simp only [lawSummand, Fintype.sum_prod_type, Fintype.sum_bool, pmu_E01, pmu_E12, pmu_E23,
    pmu_E34, sgn, fivePathTarget]
  norm_num
  all_goals try rw [Complex.ext_iff]
  all_goals try constructor
  all_goals try simp [← Complex.ofReal_pow]
  all_goals ring

private theorem lawSum_01010 (γ : ℝ) :
    ∑ p : (Bool × Bool) × (Bool × Bool) × (Bool × Bool) × (Bool × Bool),
        lawSummand γ ![false, true, false, true, false] p.1 p.2.1 p.2.2.1 p.2.2.2
      = ((fivePathTarget (γ ^ 2) ![false, true, false, true, false] : ℝ) : ℂ) := by
  simp only [lawSummand, Fintype.sum_prod_type, Fintype.sum_bool, pmu_E01, pmu_E12, pmu_E23,
    pmu_E34, sgn, fivePathTarget]
  norm_num
  all_goals try rw [Complex.ext_iff]
  all_goals try constructor
  all_goals try simp [← Complex.ofReal_pow]
  all_goals ring

private theorem lawSum_01011 (γ : ℝ) :
    ∑ p : (Bool × Bool) × (Bool × Bool) × (Bool × Bool) × (Bool × Bool),
        lawSummand γ ![false, true, false, true, true] p.1 p.2.1 p.2.2.1 p.2.2.2
      = ((fivePathTarget (γ ^ 2) ![false, true, false, true, true] : ℝ) : ℂ) := by
  simp only [lawSummand, Fintype.sum_prod_type, Fintype.sum_bool, pmu_E01, pmu_E12, pmu_E23,
    pmu_E34, sgn, fivePathTarget]
  norm_num
  all_goals try rw [Complex.ext_iff]
  all_goals try constructor
  all_goals try simp [← Complex.ofReal_pow]
  all_goals ring

private theorem lawSum_01100 (γ : ℝ) :
    ∑ p : (Bool × Bool) × (Bool × Bool) × (Bool × Bool) × (Bool × Bool),
        lawSummand γ ![false, true, true, false, false] p.1 p.2.1 p.2.2.1 p.2.2.2
      = ((fivePathTarget (γ ^ 2) ![false, true, true, false, false] : ℝ) : ℂ) := by
  simp only [lawSummand, Fintype.sum_prod_type, Fintype.sum_bool, pmu_E01, pmu_E12, pmu_E23,
    pmu_E34, sgn, fivePathTarget]
  norm_num
  all_goals try rw [Complex.ext_iff]
  all_goals try constructor
  all_goals try simp [← Complex.ofReal_pow]
  all_goals ring

private theorem lawSum_01101 (γ : ℝ) :
    ∑ p : (Bool × Bool) × (Bool × Bool) × (Bool × Bool) × (Bool × Bool),
        lawSummand γ ![false, true, true, false, true] p.1 p.2.1 p.2.2.1 p.2.2.2
      = ((fivePathTarget (γ ^ 2) ![false, true, true, false, true] : ℝ) : ℂ) := by
  simp only [lawSummand, Fintype.sum_prod_type, Fintype.sum_bool, pmu_E01, pmu_E12, pmu_E23,
    pmu_E34, sgn, fivePathTarget]
  norm_num
  all_goals try rw [Complex.ext_iff]
  all_goals try constructor
  all_goals try simp [← Complex.ofReal_pow]
  all_goals ring

private theorem lawSum_01110 (γ : ℝ) :
    ∑ p : (Bool × Bool) × (Bool × Bool) × (Bool × Bool) × (Bool × Bool),
        lawSummand γ ![false, true, true, true, false] p.1 p.2.1 p.2.2.1 p.2.2.2
      = ((fivePathTarget (γ ^ 2) ![false, true, true, true, false] : ℝ) : ℂ) := by
  simp only [lawSummand, Fintype.sum_prod_type, Fintype.sum_bool, pmu_E01, pmu_E12, pmu_E23,
    pmu_E34, sgn, fivePathTarget]
  norm_num
  all_goals try rw [Complex.ext_iff]
  all_goals try constructor
  all_goals try simp [← Complex.ofReal_pow]
  all_goals ring

private theorem lawSum_01111 (γ : ℝ) :
    ∑ p : (Bool × Bool) × (Bool × Bool) × (Bool × Bool) × (Bool × Bool),
        lawSummand γ ![false, true, true, true, true] p.1 p.2.1 p.2.2.1 p.2.2.2
      = ((fivePathTarget (γ ^ 2) ![false, true, true, true, true] : ℝ) : ℂ) := by
  simp only [lawSummand, Fintype.sum_prod_type, Fintype.sum_bool, pmu_E01, pmu_E12, pmu_E23,
    pmu_E34, sgn, fivePathTarget]
  norm_num
  all_goals try rw [Complex.ext_iff]
  all_goals try constructor
  all_goals try simp [← Complex.ofReal_pow]
  all_goals ring

private theorem lawSum_10000 (γ : ℝ) :
    ∑ p : (Bool × Bool) × (Bool × Bool) × (Bool × Bool) × (Bool × Bool),
        lawSummand γ ![true, false, false, false, false] p.1 p.2.1 p.2.2.1 p.2.2.2
      = ((fivePathTarget (γ ^ 2) ![true, false, false, false, false] : ℝ) : ℂ) := by
  simp only [lawSummand, Fintype.sum_prod_type, Fintype.sum_bool, pmu_E01, pmu_E12, pmu_E23,
    pmu_E34, sgn, fivePathTarget]
  norm_num
  all_goals try rw [Complex.ext_iff]
  all_goals try constructor
  all_goals try simp [← Complex.ofReal_pow]
  all_goals ring

private theorem lawSum_10001 (γ : ℝ) :
    ∑ p : (Bool × Bool) × (Bool × Bool) × (Bool × Bool) × (Bool × Bool),
        lawSummand γ ![true, false, false, false, true] p.1 p.2.1 p.2.2.1 p.2.2.2
      = ((fivePathTarget (γ ^ 2) ![true, false, false, false, true] : ℝ) : ℂ) := by
  simp only [lawSummand, Fintype.sum_prod_type, Fintype.sum_bool, pmu_E01, pmu_E12, pmu_E23,
    pmu_E34, sgn, fivePathTarget]
  norm_num
  all_goals try rw [Complex.ext_iff]
  all_goals try constructor
  all_goals try simp [← Complex.ofReal_pow]
  all_goals ring

private theorem lawSum_10010 (γ : ℝ) :
    ∑ p : (Bool × Bool) × (Bool × Bool) × (Bool × Bool) × (Bool × Bool),
        lawSummand γ ![true, false, false, true, false] p.1 p.2.1 p.2.2.1 p.2.2.2
      = ((fivePathTarget (γ ^ 2) ![true, false, false, true, false] : ℝ) : ℂ) := by
  simp only [lawSummand, Fintype.sum_prod_type, Fintype.sum_bool, pmu_E01, pmu_E12, pmu_E23,
    pmu_E34, sgn, fivePathTarget]
  norm_num
  all_goals try rw [Complex.ext_iff]
  all_goals try constructor
  all_goals try simp [← Complex.ofReal_pow]
  all_goals ring

private theorem lawSum_10011 (γ : ℝ) :
    ∑ p : (Bool × Bool) × (Bool × Bool) × (Bool × Bool) × (Bool × Bool),
        lawSummand γ ![true, false, false, true, true] p.1 p.2.1 p.2.2.1 p.2.2.2
      = ((fivePathTarget (γ ^ 2) ![true, false, false, true, true] : ℝ) : ℂ) := by
  simp only [lawSummand, Fintype.sum_prod_type, Fintype.sum_bool, pmu_E01, pmu_E12, pmu_E23,
    pmu_E34, sgn, fivePathTarget]
  norm_num
  all_goals try rw [Complex.ext_iff]
  all_goals try constructor
  all_goals try simp [← Complex.ofReal_pow]
  all_goals ring

private theorem lawSum_10100 (γ : ℝ) :
    ∑ p : (Bool × Bool) × (Bool × Bool) × (Bool × Bool) × (Bool × Bool),
        lawSummand γ ![true, false, true, false, false] p.1 p.2.1 p.2.2.1 p.2.2.2
      = ((fivePathTarget (γ ^ 2) ![true, false, true, false, false] : ℝ) : ℂ) := by
  simp only [lawSummand, Fintype.sum_prod_type, Fintype.sum_bool, pmu_E01, pmu_E12, pmu_E23,
    pmu_E34, sgn, fivePathTarget]
  norm_num
  all_goals try rw [Complex.ext_iff]
  all_goals try constructor
  all_goals try simp [← Complex.ofReal_pow]
  all_goals ring

private theorem lawSum_10101 (γ : ℝ) :
    ∑ p : (Bool × Bool) × (Bool × Bool) × (Bool × Bool) × (Bool × Bool),
        lawSummand γ ![true, false, true, false, true] p.1 p.2.1 p.2.2.1 p.2.2.2
      = ((fivePathTarget (γ ^ 2) ![true, false, true, false, true] : ℝ) : ℂ) := by
  simp only [lawSummand, Fintype.sum_prod_type, Fintype.sum_bool, pmu_E01, pmu_E12, pmu_E23,
    pmu_E34, sgn, fivePathTarget]
  norm_num
  all_goals try rw [Complex.ext_iff]
  all_goals try constructor
  all_goals try simp [← Complex.ofReal_pow]
  all_goals ring

private theorem lawSum_10110 (γ : ℝ) :
    ∑ p : (Bool × Bool) × (Bool × Bool) × (Bool × Bool) × (Bool × Bool),
        lawSummand γ ![true, false, true, true, false] p.1 p.2.1 p.2.2.1 p.2.2.2
      = ((fivePathTarget (γ ^ 2) ![true, false, true, true, false] : ℝ) : ℂ) := by
  simp only [lawSummand, Fintype.sum_prod_type, Fintype.sum_bool, pmu_E01, pmu_E12, pmu_E23,
    pmu_E34, sgn, fivePathTarget]
  norm_num
  all_goals try rw [Complex.ext_iff]
  all_goals try constructor
  all_goals try simp [← Complex.ofReal_pow]
  all_goals ring

private theorem lawSum_10111 (γ : ℝ) :
    ∑ p : (Bool × Bool) × (Bool × Bool) × (Bool × Bool) × (Bool × Bool),
        lawSummand γ ![true, false, true, true, true] p.1 p.2.1 p.2.2.1 p.2.2.2
      = ((fivePathTarget (γ ^ 2) ![true, false, true, true, true] : ℝ) : ℂ) := by
  simp only [lawSummand, Fintype.sum_prod_type, Fintype.sum_bool, pmu_E01, pmu_E12, pmu_E23,
    pmu_E34, sgn, fivePathTarget]
  norm_num
  all_goals try rw [Complex.ext_iff]
  all_goals try constructor
  all_goals try simp [← Complex.ofReal_pow]
  all_goals ring

private theorem lawSum_11000 (γ : ℝ) :
    ∑ p : (Bool × Bool) × (Bool × Bool) × (Bool × Bool) × (Bool × Bool),
        lawSummand γ ![true, true, false, false, false] p.1 p.2.1 p.2.2.1 p.2.2.2
      = ((fivePathTarget (γ ^ 2) ![true, true, false, false, false] : ℝ) : ℂ) := by
  simp only [lawSummand, Fintype.sum_prod_type, Fintype.sum_bool, pmu_E01, pmu_E12, pmu_E23,
    pmu_E34, sgn, fivePathTarget]
  norm_num
  all_goals try rw [Complex.ext_iff]
  all_goals try constructor
  all_goals try simp [← Complex.ofReal_pow]
  all_goals ring

private theorem lawSum_11001 (γ : ℝ) :
    ∑ p : (Bool × Bool) × (Bool × Bool) × (Bool × Bool) × (Bool × Bool),
        lawSummand γ ![true, true, false, false, true] p.1 p.2.1 p.2.2.1 p.2.2.2
      = ((fivePathTarget (γ ^ 2) ![true, true, false, false, true] : ℝ) : ℂ) := by
  simp only [lawSummand, Fintype.sum_prod_type, Fintype.sum_bool, pmu_E01, pmu_E12, pmu_E23,
    pmu_E34, sgn, fivePathTarget]
  norm_num
  all_goals try rw [Complex.ext_iff]
  all_goals try constructor
  all_goals try simp [← Complex.ofReal_pow]
  all_goals ring

private theorem lawSum_11010 (γ : ℝ) :
    ∑ p : (Bool × Bool) × (Bool × Bool) × (Bool × Bool) × (Bool × Bool),
        lawSummand γ ![true, true, false, true, false] p.1 p.2.1 p.2.2.1 p.2.2.2
      = ((fivePathTarget (γ ^ 2) ![true, true, false, true, false] : ℝ) : ℂ) := by
  simp only [lawSummand, Fintype.sum_prod_type, Fintype.sum_bool, pmu_E01, pmu_E12, pmu_E23,
    pmu_E34, sgn, fivePathTarget]
  norm_num
  all_goals try rw [Complex.ext_iff]
  all_goals try constructor
  all_goals try simp [← Complex.ofReal_pow]
  all_goals ring

private theorem lawSum_11011 (γ : ℝ) :
    ∑ p : (Bool × Bool) × (Bool × Bool) × (Bool × Bool) × (Bool × Bool),
        lawSummand γ ![true, true, false, true, true] p.1 p.2.1 p.2.2.1 p.2.2.2
      = ((fivePathTarget (γ ^ 2) ![true, true, false, true, true] : ℝ) : ℂ) := by
  simp only [lawSummand, Fintype.sum_prod_type, Fintype.sum_bool, pmu_E01, pmu_E12, pmu_E23,
    pmu_E34, sgn, fivePathTarget]
  norm_num
  all_goals try rw [Complex.ext_iff]
  all_goals try constructor
  all_goals try simp [← Complex.ofReal_pow]
  all_goals ring

private theorem lawSum_11100 (γ : ℝ) :
    ∑ p : (Bool × Bool) × (Bool × Bool) × (Bool × Bool) × (Bool × Bool),
        lawSummand γ ![true, true, true, false, false] p.1 p.2.1 p.2.2.1 p.2.2.2
      = ((fivePathTarget (γ ^ 2) ![true, true, true, false, false] : ℝ) : ℂ) := by
  simp only [lawSummand, Fintype.sum_prod_type, Fintype.sum_bool, pmu_E01, pmu_E12, pmu_E23,
    pmu_E34, sgn, fivePathTarget]
  norm_num
  all_goals try rw [Complex.ext_iff]
  all_goals try constructor
  all_goals try simp [← Complex.ofReal_pow]
  all_goals ring

private theorem lawSum_11101 (γ : ℝ) :
    ∑ p : (Bool × Bool) × (Bool × Bool) × (Bool × Bool) × (Bool × Bool),
        lawSummand γ ![true, true, true, false, true] p.1 p.2.1 p.2.2.1 p.2.2.2
      = ((fivePathTarget (γ ^ 2) ![true, true, true, false, true] : ℝ) : ℂ) := by
  simp only [lawSummand, Fintype.sum_prod_type, Fintype.sum_bool, pmu_E01, pmu_E12, pmu_E23,
    pmu_E34, sgn, fivePathTarget]
  norm_num
  all_goals try rw [Complex.ext_iff]
  all_goals try constructor
  all_goals try simp [← Complex.ofReal_pow]
  all_goals ring

private theorem lawSum_11110 (γ : ℝ) :
    ∑ p : (Bool × Bool) × (Bool × Bool) × (Bool × Bool) × (Bool × Bool),
        lawSummand γ ![true, true, true, true, false] p.1 p.2.1 p.2.2.1 p.2.2.2
      = ((fivePathTarget (γ ^ 2) ![true, true, true, true, false] : ℝ) : ℂ) := by
  simp only [lawSummand, Fintype.sum_prod_type, Fintype.sum_bool, pmu_E01, pmu_E12, pmu_E23,
    pmu_E34, sgn, fivePathTarget]
  norm_num
  all_goals try rw [Complex.ext_iff]
  all_goals try constructor
  all_goals try simp [← Complex.ofReal_pow]
  all_goals ring

private theorem lawSum_11111 (γ : ℝ) :
    ∑ p : (Bool × Bool) × (Bool × Bool) × (Bool × Bool) × (Bool × Bool),
        lawSummand γ ![true, true, true, true, true] p.1 p.2.1 p.2.2.1 p.2.2.2
      = ((fivePathTarget (γ ^ 2) ![true, true, true, true, true] : ℝ) : ℂ) := by
  simp only [lawSummand, Fintype.sum_prod_type, Fintype.sum_bool, pmu_E01, pmu_E12, pmu_E23,
    pmu_E34, sgn, fivePathTarget]
  norm_num
  all_goals try rw [Complex.ext_iff]
  all_goals try constructor
  all_goals try simp [← Complex.ofReal_pow]
  all_goals ring

theorem lawSum (γ : ℝ) (w : Fin 5 → Bool) :
    ∑ p : (Bool × Bool) × (Bool × Bool) × (Bool × Bool) × (Bool × Bool),
        lawSummand γ w p.1 p.2.1 p.2.2.1 p.2.2.2
      = ((fivePathTarget (γ ^ 2) w : ℝ) : ℂ) := by
  have hw : w = ![w 0, w 1, w 2, w 3, w 4] := by
    funext i
    fin_cases i <;> rfl
  rw [hw]
  cases w 0 <;> cases w 1 <;> cases w 2 <;> cases w 3 <;> cases w 4
  · exact lawSum_00000 γ
  · exact lawSum_00001 γ
  · exact lawSum_00010 γ
  · exact lawSum_00011 γ
  · exact lawSum_00100 γ
  · exact lawSum_00101 γ
  · exact lawSum_00110 γ
  · exact lawSum_00111 γ
  · exact lawSum_01000 γ
  · exact lawSum_01001 γ
  · exact lawSum_01010 γ
  · exact lawSum_01011 γ
  · exact lawSum_01100 γ
  · exact lawSum_01101 γ
  · exact lawSum_01110 γ
  · exact lawSum_01111 γ
  · exact lawSum_10000 γ
  · exact lawSum_10001 γ
  · exact lawSum_10010 γ
  · exact lawSum_10011 γ
  · exact lawSum_10100 γ
  · exact lawSum_10101 γ
  · exact lawSum_10110 γ
  · exact lawSum_10111 γ
  · exact lawSum_11000 γ
  · exact lawSum_11001 γ
  · exact lawSum_11010 γ
  · exact lawSum_11011 γ
  · exact lawSum_11100 γ
  · exact lawSum_11101 γ
  · exact lawSum_11110 γ
  · exact lawSum_11111 γ

theorem PM_law (γ : ℝ) : (PM γ).law = fun w => ((fivePathTarget (γ ^ 2) w : ℝ) : ℂ) := by
  funext w
  rw [show (PM γ).law w = ∑ x : fivePathGraph.Edge → Bool × Bool,
      (∏ e : fivePathGraph.Edge, pmu γ e (x e))
        * ∏ v : fivePathGraph.V, crespMass ((PM γ).resp v (fun e => x e.1)) (w v) from rfl,
    Finset.sum_congr rfl (fun x _ => law_summand_eq γ w x),
    ← Equiv.sum_comp eTup.symm (fun x : fivePathGraph.Edge → Bool × Bool =>
      lawSummand γ w (x E01) (x E12) (x E23) (x E34))]
  rw [← lawSum γ w]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp [eTup, ne01_12.symm, ne01_23.symm, ne12_23.symm,
    ne01_34.symm, ne12_34.symm, ne23_34.symm]


/-! ### Positivity of the real part of the complex witness

The copied source weights of `PM γ` are `1/4` on the endpoint sources and `(1 ± iγ)/4` on the
two middle ones, so the weight of a copied latent configuration is a positive multiple of a
product of `2t` complex numbers of modulus `A = √(1+γ²)` and real part `1`. A telescoped
triangle inequality plus Cauchy–Schwarz bounds `A^n − Re ∏` by `n² A^{n-1}(A−1)`, which is
less than `A^n` for `γ = 1/(4t)`, `n = 2t`. -/

/-- The telescoped bound `‖A^{|s|} − ∏ f‖ · A ≤ |s| A^{|s|} d` for factors of modulus `A`
each within `d` of `A`. -/
theorem tel_bound {ι : Type*} [DecidableEq ι] (A d : ℝ) (hA : 0 ≤ A) (_hd0 : 0 ≤ d)
    (f : ι → ℂ) (hn : ∀ i, ‖f i‖ = A) (hdi : ∀ i, ‖(A : ℂ) - f i‖ ≤ d) (s : Finset ι) :
    ‖(A : ℂ) ^ s.card - ∏ i ∈ s, f i‖ * A ≤ s.card * A ^ s.card * d := by
  have hAC : ‖(A : ℂ)‖ = A := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hA]
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
      have hP : ‖∏ i ∈ s, f i‖ = A ^ s.card := by
        rw [norm_prod]
        rw [Finset.prod_congr rfl (fun i _ => hn i), Finset.prod_const]
      rw [Finset.card_cons, Finset.prod_cons]
      have hsplit : (A : ℂ) ^ (s.card + 1) - f a * ∏ i ∈ s, f i
          = (A : ℂ) * ((A : ℂ) ^ s.card - ∏ i ∈ s, f i)
            + ((A : ℂ) - f a) * ∏ i ∈ s, f i := by ring
      have hb : ‖(A : ℂ) ^ (s.card + 1) - f a * ∏ i ∈ s, f i‖
          ≤ A * ‖(A : ℂ) ^ s.card - ∏ i ∈ s, f i‖ + d * A ^ s.card := by
        rw [hsplit]
        refine le_trans (norm_add_le _ _) ?_
        rw [norm_mul, norm_mul, hAC, hP]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_right (hdi a) (by positivity))
      have hAn : (0 : ℝ) ≤ A ^ s.card := by positivity
      have hcard : (0 : ℝ) ≤ (s.card : ℝ) := Nat.cast_nonneg _
      have hmul := mul_le_mul_of_nonneg_right hb hA
      push_cast
      calc ‖(A : ℂ) ^ (s.card + 1) - f a * ∏ i ∈ s, f i‖ * A
          ≤ (A * ‖(A : ℂ) ^ s.card - ∏ i ∈ s, f i‖ + d * A ^ s.card) * A := hmul
        _ = A * (‖(A : ℂ) ^ s.card - ∏ i ∈ s, f i‖ * A) + d * A ^ s.card * A := by ring
        _ ≤ A * ((s.card : ℝ) * A ^ s.card * d) + d * A ^ s.card * A :=
              add_le_add (mul_le_mul_of_nonneg_left ih hA) le_rfl
        _ = ((s.card : ℝ) + 1) * A ^ (s.card + 1) * d := by rw [pow_succ]; ring

/-- If every factor has modulus `A ≥ 1` and lies within `√(2A(A−1))` of `A`, and
`n²(A−1) ≤ A` for `n` the number of factors, then the product has nonnegative real part. -/
theorem re_prod_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] (A : ℝ) (hA1 : 1 ≤ A)
    (f : ι → ℂ) (hn : ∀ i, ‖f i‖ = A)
    (hdsq : ∀ i, ‖(A : ℂ) - f i‖ ^ 2 = 2 * A * (A - 1))
    (hkey : ((Fintype.card ι : ℝ)) ^ 2 * (A - 1) ≤ A) :
    0 ≤ (∏ i, f i).re := by
  have hA0 : (0 : ℝ) < A := lt_of_lt_of_le one_pos hA1
  set n : ℕ := Fintype.card ι with hncard
  set d : ℝ := Real.sqrt (2 * A * (A - 1)) with hd
  have h2A : (0 : ℝ) ≤ 2 * A * (A - 1) := by nlinarith
  have hd0 : 0 ≤ d := Real.sqrt_nonneg _
  have hdsq' : d ^ 2 = 2 * A * (A - 1) := Real.sq_sqrt h2A
  have hdi : ∀ i, ‖(A : ℂ) - f i‖ ≤ d := by
    intro i
    have h1 : ‖(A : ℂ) - f i‖ ^ 2 = d ^ 2 := by rw [hdsq i, hdsq']
    nlinarith [norm_nonneg ((A : ℂ) - f i), hd0, h1]
  have hcard : (Finset.univ : Finset ι).card = n := rfl
  have htel := tel_bound A d (le_of_lt hA0) hd0 f hn hdi Finset.univ
  rw [hcard] at htel
  set P : ℂ := ∏ i, f i with hP
  have hPn : ‖P‖ = A ^ n := by
    rw [hP, norm_prod, Finset.prod_congr rfl (fun i _ => hn i), Finset.prod_const, hcard]
  have hAn : ((A : ℂ)) ^ n = (((A ^ n : ℝ)) : ℂ) := by push_cast; ring
  have hsq : ‖((A : ℂ)) ^ n - P‖ ^ 2 = 2 * A ^ n * (A ^ n - P.re) := by
    rw [hAn, norm_sub_sq_of_norm_eq (A ^ n) P hPn]
  have hAnpos : (0 : ℝ) < A ^ n := by positivity
  have hT0 : (0 : ℝ) ≤ ‖((A : ℂ)) ^ n - P‖ := norm_nonneg _
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  -- square the telescoped bound
  have hsq2 : (‖((A : ℂ)) ^ n - P‖ * A) ^ 2 ≤ ((n : ℝ) * A ^ n * d) ^ 2 := by
    have h1 : (0 : ℝ) ≤ ‖((A : ℂ)) ^ n - P‖ * A := by positivity
    nlinarith [htel, h1]
  have hexp : (2 * A ^ n * (A ^ n - P.re)) * A ^ 2 ≤ (n : ℝ) ^ 2 * (A ^ n) ^ 2 * (2 * A * (A - 1)) := by
    have := hsq2
    rw [mul_pow, hsq, mul_pow, mul_pow, hdsq'] at this
    nlinarith [this]
  have hstep : (A ^ n - P.re) * A ≤ (n : ℝ) ^ 2 * A ^ n * (A - 1) := by
    have hpos : (0 : ℝ) < 2 * A ^ n * A := by positivity
    nlinarith [hexp, hAnpos, hA0]
  have hfin : 0 ≤ A * P.re := by nlinarith [hstep, hAnpos, hkey, hA0]
  nlinarith [hfin, hA0]


theorem sgn_not (b : Bool) : sgn (!b) = -sgn b := by cases b <;> norm_num [sgn]

theorem pmu_E12' (γ : ℝ) (hγ : 0 ≤ γ) (a : Bool × Bool) :
    pmu γ E12 a = triAtom (γ ^ 2) a.2 / 4 := by
  rw [pmu_E12, triAtom, Real.sqrt_sq hγ]
  push_cast
  ring

theorem pmu_E23' (γ : ℝ) (hγ : 0 ≤ γ) (a : Bool × Bool) :
    pmu γ E23 a = triAtom (γ ^ 2) (!a.2) / 4 := by
  rw [pmu_E23, triAtom, Real.sqrt_sq hγ, sgn_not]
  push_cast
  ring

/-- The auxiliary complex factor of a copied latent configuration: the `t` copies of the
source `E12` carry `1 + iγu`, the `t` copies of `E23` carry `1 - iγv`. -/
noncomputable def zAt (γ : ℝ) {t : ℕ} (x : CCfg (PM γ) t) (k : Bool × Fin t) : ℂ :=
  triAtom (γ ^ 2) (if k.1 then !((x (E23, k.2)).2) else (x (E12, k.2)).2)

theorem ccfgW_eq (γ : ℝ) (hγ : 0 ≤ γ) (t : ℕ) (x : CCfg (PM γ) t) :
    ccfgW (PM γ) t x
      = (((1 / 4 : ℝ) ^ (4 * t) : ℝ) : ℂ) * ∏ k : Bool × Fin t, zAt γ x k := by
  have hL : ccfgW (PM γ) t x = ∏ e : fivePathGraph.Edge, ∏ r : Fin t, pmu γ e (x (e, r)) := by
    rw [show ccfgW (PM γ) t x = ∏ l : GLatent fivePathGraph t, pmu γ l.1 (x l) from rfl]
    exact Fintype.prod_prod_type (fun l : fivePathGraph.Edge × Fin t => pmu γ l.1 (x l))
  have hR : (∏ k : Bool × Fin t, zAt γ x k)
      = (∏ r : Fin t, triAtom (γ ^ 2) ((x (E12, r)).2))
        * ∏ r : Fin t, triAtom (γ ^ 2) (!((x (E23, r)).2)) := by
    rw [Fintype.prod_prod_type (fun k : Bool × Fin t => zAt γ x k), Fintype.prod_bool]
    rw [mul_comm]
    rfl
  have h01 : (∏ r : Fin t, pmu γ E01 (x (E01, r))) = ((4 : ℂ) ^ t)⁻¹ := by
    rw [Finset.prod_congr rfl (fun r _ => pmu_E01 γ (x (E01, r))), Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, div_pow, one_pow, one_div]
  have h34 : (∏ r : Fin t, pmu γ E34 (x (E34, r))) = ((4 : ℂ) ^ t)⁻¹ := by
    rw [Finset.prod_congr rfl (fun r _ => pmu_E34 γ (x (E34, r))), Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, div_pow, one_pow, one_div]
  have h12 : (∏ r : Fin t, pmu γ E12 (x (E12, r)))
      = (∏ r : Fin t, triAtom (γ ^ 2) ((x (E12, r)).2)) / 4 ^ t := by
    rw [Finset.prod_congr rfl (fun r _ => pmu_E12' γ hγ (x (E12, r))), Finset.prod_div_distrib,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have h23 : (∏ r : Fin t, pmu γ E23 (x (E23, r)))
      = (∏ r : Fin t, triAtom (γ ^ 2) (!((x (E23, r)).2))) / 4 ^ t := by
    rw [Finset.prod_congr rfl (fun r _ => pmu_E23' γ hγ (x (E23, r))), Finset.prod_div_distrib,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hc : (((1 / 4 : ℝ) ^ (4 * t) : ℝ) : ℂ) = (((4 : ℂ) ^ t)⁻¹) ^ 4 := by
    push_cast
    rw [div_pow, one_pow, one_div, show 4 * t = t * 4 from Nat.mul_comm 4 t, pow_mul, inv_pow]
  rw [hL, prod_edge (fun e => ∏ r : Fin t, pmu γ e (x (e, r))), h01, h12, h23, h34, hR, hc]
  have h4 : ((4 : ℂ)) ^ t ≠ 0 := pow_ne_zero t (by norm_num)
  field_simp

theorem zAt_norm (γ : ℝ) (t : ℕ) (x : CCfg (PM γ) t) (k : Bool × Fin t) :
    ‖zAt γ x k‖ = Real.sqrt (1 + γ ^ 2) := triAtom_norm (γ ^ 2) (sq_nonneg γ) _

theorem ccfgW_re_nonneg (γ : ℝ) (hγ : 0 ≤ γ) (t : ℕ)
    (hγt : (2 * (t : ℝ)) ^ 2 * γ ^ 2 ≤ 2) (x : CCfg (PM γ) t) :
    0 ≤ (ccfgW (PM γ) t x).re := by
  set A : ℝ := Real.sqrt (1 + γ ^ 2) with hA
  have hq : (0 : ℝ) ≤ 1 + γ ^ 2 := by positivity
  have hA1 : 1 ≤ A := by
    rw [hA, Real.one_le_sqrt]
    nlinarith [sq_nonneg γ]
  have hAsq : A ^ 2 = 1 + γ ^ 2 := Real.sq_sqrt hq
  have hcard : (Fintype.card (Bool × Fin t) : ℝ) = 2 * (t : ℝ) := by
    simp [Fintype.card_prod]
  have hd : (A - 1) * 2 ≤ γ ^ 2 := by nlinarith [sq_nonneg (A - 1), hAsq]
  have hkey : ((Fintype.card (Bool × Fin t) : ℝ)) ^ 2 * (A - 1) ≤ A := by
    rw [hcard]
    have h1 : (2 * (t : ℝ)) ^ 2 * ((A - 1) * 2) ≤ (2 * (t : ℝ)) ^ 2 * γ ^ 2 :=
      mul_le_mul_of_nonneg_left hd (sq_nonneg _)
    linarith [h1, hγt, hA1]
  have hre : 0 ≤ (∏ k : Bool × Fin t, zAt γ x k).re := by
    refine re_prod_nonneg A hA1 (zAt γ x) (fun k => zAt_norm γ t x k) (fun k => ?_) hkey
    rw [norm_sub_sq_of_norm_eq A (zAt γ x k) (zAt_norm γ t x k), zAt, triAtom_re]
  rw [ccfgW_eq γ hγ t x, Complex.re_ofReal_mul]
  have hpos : (0 : ℝ) ≤ (1 / 4 : ℝ) ^ (4 * t) := by positivity
  exact mul_nonneg hpos hre


theorem PM_respV (γ : ℝ) (v : fivePathGraph.V) (c : (e : fivePathGraph.inc v) → Bool × Bool) :
    (PM γ).resp v c = ((prespR v c : ℝ) : ℂ) := rfl

theorem cInflCond_PM (γ : ℝ) (t : ℕ) (x : CCfg (PM γ) t) (o : GObs fivePathGraph t) (b : Bool) :
    cInflCond (PM γ) x o b
      = ((respMass (prespR o.1 (fun e => x (e.1, o.2 e))) b : ℝ) : ℂ) := by
  rw [show cInflCond (PM γ) x o b
      = crespMass (((prespR o.1 (fun e => x (e.1, o.2 e)) : ℝ)) : ℂ) b from rfl,
    crespMass_ofReal]

theorem cprodLaw_PM (γ : ℝ) (t : ℕ) (x : CCfg (PM γ) t) (ω : GAssign fivePathGraph t) :
    ∃ c : ℝ, 0 ≤ c ∧ cprodLaw (cInflCond (PM γ) x) ω = ((c : ℝ) : ℂ) := by
  refine ⟨∏ o : GObs fivePathGraph t,
    respMass (prespR o.1 (fun e => x (e.1, o.2 e))) (ω o), ?_, ?_⟩
  · refine Finset.prod_nonneg fun o _ => ?_
    have hb := prespR_mem o.1 (fun e => x (e.1, o.2 e))
    cases hω : ω o <;> simp [respMass] <;> linarith [hb.1, hb.2]
  · rw [show cprodLaw (cInflCond (PM γ) x) ω
        = ∏ o : GObs fivePathGraph t, cInflCond (PM γ) x o (ω o) from rfl,
      Complex.ofReal_prod]
    exact Finset.prod_congr rfl fun o _ => cInflCond_PM γ t x o (ω o)

theorem cInflLaw_re_nonneg (γ : ℝ) (hγ : 0 ≤ γ) (t : ℕ) (hγt : (2 * (t : ℝ)) ^ 2 * γ ^ 2 ≤ 2)
    (ω : GAssign fivePathGraph t) : 0 ≤ (cInflLaw (PM γ) t ω).re := by
  rw [show cInflLaw (PM γ) t ω
      = ∑ x : CCfg (PM γ) t, ccfgW (PM γ) t x * cprodLaw (cInflCond (PM γ) x) ω from rfl,
    Complex.re_sum]
  refine Finset.sum_nonneg fun x _ => ?_
  obtain ⟨c, hc0, hc⟩ := cprodLaw_PM γ t x ω
  rw [hc, mul_comm, Complex.re_ofReal_mul]
  exact mul_nonneg hc0 (ccfgW_re_nonneg γ hγ t hγt x)

/-- AUDIT-NOTES A4, the witness: the five-path target at `h = γ²`, `γ = 1/(4t)`, lies in the
order-`t` ancestral-independence feasible set of `P₅`. -/
theorem fivePath_witness' (t : ℕ) (ht : 1 ≤ t) (h : ℝ) (hh : h = 1 / (16 * (t : ℝ) ^ 2)) :
    GAIFeasible fivePathGraph t (fivePathTarget h) := by
  have ht0 : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have htne : (t : ℝ) ≠ 0 := ne_of_gt ht0
  have hγ : (0 : ℝ) ≤ 1 / (4 * (t : ℝ)) := by positivity
  have hγsq : (1 / (4 * (t : ℝ))) ^ 2 = h := by rw [hh]; field_simp; ring
  have hγt : (2 * (t : ℝ)) ^ 2 * (1 / (4 * (t : ℝ))) ^ 2 ≤ 2 := by
    have hval : (2 * (t : ℝ)) ^ 2 * (1 / (4 * (t : ℝ))) ^ 2 = 1 / 4 := by field_simp; ring
    rw [hval]; norm_num
  refine gAIFeasible_of_cModel (PM (1 / (4 * (t : ℝ)))) t (fivePathTarget h)
    (PM_valid _) (cInflLaw_re_nonneg _ hγ t hγt) (fun w => ?_)
  have hw := congrFun (PM_law (1 / (4 * (t : ℝ)))) w
  rw [hγsq] at hw
  exact hw

end P5WitnessAux

/-- AUDIT-NOTES A4, the witness. At order `t` with `γ = 1/(4t)` and `h = γ² = 1/(16t²)`, the
five-path target lies in the AI feasible set. The witness draws auxiliary signs `u_i`, `v_j`
with the positive real law `H_t(u,v) = 2^{-2t} Re[∏(1+iγu_i) ∏(1−iγv_j)]`, fair endpoint
bits `X_a`, `Z_e`, fair masks `r_i`, `s_j` and fair private signs `ε_{ij}`, and sets
`A^a = X_a`, `B^{ai} = r_i u_i^{X_a}`, `D^{je} = s_j v_j^{Z_e}`, `E^e = Z_e`, and
`C^{ij} = r_i s_j` when `u_i = v_j`, `r_i s_j ε_{ij}` otherwise. -/
theorem fivePath_witness (t : ℕ) (ht : 1 ≤ t) (h : ℝ) (hh : h = 1 / (16 * (t : ℝ) ^ 2)) :
    GAIFeasible fivePathGraph t (fivePathTarget h) :=
  P5WitnessAux.fivePath_witness' t ht h hh

/-- The same witness passes the recursively expressible test, by AUDIT-NOTES A2. -/
theorem fivePath_exp_witness (t : ℕ) (ht : 1 ≤ t) (h : ℝ) (hh : h = 1 / (16 * (t : ℝ) ^ 2)) :
    GExpFeasible fivePathGraph t (fivePathTarget h) :=
  (gExpFeasible_iff_gAIFeasible fivePathGraph t (fivePathTarget h)).2
    (fivePath_witness t ht h hh)


end TriangleInflation.Graph
