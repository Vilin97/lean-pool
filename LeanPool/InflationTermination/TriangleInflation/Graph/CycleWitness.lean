/-
Copyright (c) 2026 William Blair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Blair
-/

import LeanPool.InflationTermination.TriangleInflation.Graph.Cycles
import LeanPool.InflationTermination.TriangleInflation.Graph.Soundness

/-!
# The order-`t` cycle witness (A5)

The auxiliary-sign construction of AUDIT-NOTES A5 and Lemma `lem:cyclewitness` of
`papers/inflation-nontermination/paper/sections/15-cycles.tex`.
-/

namespace TriangleInflation.Graph

open Finset TriangleInflation

namespace CycleWitnessAux

/-! ## Fourier synthesis on a finite Boolean cube -/

section Fourier

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The weight function on `ι → Bool` with prescribed Walsh coefficients. -/
noncomputable def fourier (c : Finset ι → ℝ) : (ι → Bool) → ℝ := fun s =>
  (1 / 2 : ℝ) ^ Fintype.card ι * ∑ F : Finset ι, c F * ∏ v ∈ F, sgn (s v)

/-- The Walsh moments of `fourier c` are the coefficients `c`. -/
theorem fourier_moment (c : Finset ι → ℝ) (F : Finset ι) :
    (∑ s : ι → Bool, fourier c s * ∏ v ∈ F, sgn (s v)) = c F := by
  have e1 : ∀ s : ι → Bool, fourier c s * ∏ v ∈ F, sgn (s v)
      = (1 / 2 : ℝ) ^ Fintype.card ι * ∑ F' : Finset ι,
          c F' * ∏ v ∈ symmDiff F' F, sgn (s v) := by
    intro s
    simp only [fourier]
    rw [mul_assoc, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun F' _ => ?_
    rw [mul_assoc, prod_sgn_mul_prod_sgn]
  rw [Finset.sum_congr rfl fun s _ => e1 s, ← Finset.mul_sum, Finset.sum_comm]
  have e2 : ∀ F' : Finset ι,
      (∑ s : ι → Bool, c F' * ∏ v ∈ symmDiff F' F, sgn (s v))
        = c F' * (if symmDiff F' F = ∅ then (2 : ℝ) ^ Fintype.card ι else 0) := by
    intro F'
    rw [← Finset.mul_sum, sum_prod_sgn]
  simp_rw [e2, ← Finset.bot_eq_empty, symmDiff_eq_bot, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ F (fun F' => c F' * (2 : ℝ) ^ Fintype.card ι)]
  rw [ite_eq_left (Finset.mem_univ _)]
  have h2 : ((1 : ℝ) / 2) ^ Fintype.card ι * (2 : ℝ) ^ Fintype.card ι = 1 := by
    rw [← mul_pow]; norm_num
  linear_combination (c F) * h2

omit [DecidableEq ι] in
/-- The generating identity `∑_F ρ^{|F|} = (1+ρ)^n`. -/
theorem sum_pow_card (ρ : ℝ) :
    (∑ F : Finset ι, ρ ^ F.card) = (1 + ρ) ^ Fintype.card ι := by
  classical
  have h := Fintype.prod_add (fun _ : ι => ρ) (fun _ : ι => (1 : ℝ))
  simp only [Finset.prod_const_one, mul_one, Finset.prod_const] at h
  rw [← h]
  simp [add_comm]

/-- `(1+ρ)^N ≤ 2` when `Nρ ≤ 1/2`: Bernoulli on `(1-ρ)^N` together with `(1-ρ²)^N ≤ 1`. -/
theorem one_add_pow_le_two {ρ : ℝ} {N : ℕ} (hρ0 : 0 ≤ ρ) (h : (N : ℝ) * ρ ≤ 1 / 2) :
    (1 + ρ) ^ N ≤ 2 := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; norm_num
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hρhalf : ρ ≤ 1 / 2 := by nlinarith
  have hb : 1 + (N : ℝ) * (-ρ) ≤ (1 + -ρ) ^ N := one_add_mul_le_pow (by linarith) N
  have hb2 : (1 : ℝ) / 2 ≤ (1 - ρ) ^ N := by
    have h3 : (1 + -ρ) ^ N = (1 - ρ) ^ N := by ring_nf
    rw [h3] at hb
    linarith
  have hmul : (1 + ρ) ^ N * (1 - ρ) ^ N ≤ 1 := by
    rw [← mul_pow]
    have h1 : (1 + ρ) * (1 - ρ) = 1 - ρ * ρ := by ring
    rw [h1]
    exact pow_le_one₀ (by nlinarith) (by nlinarith)
  have hpos : (0 : ℝ) ≤ (1 + ρ) ^ N := by positivity
  nlinarith

omit [DecidableEq ι] in
/-- Positivity of a Fourier synthesis whose nonconstant coefficients are dominated by a
geometric series summing to at most the constant coefficient. -/
theorem fourier_nonneg (c : Finset ι → ℝ) (ρ : ℝ) (_hρ0 : 0 ≤ ρ)
    (h0 : c ∅ = 1) (hc : ∀ F : Finset ι, F ≠ ∅ → |c F| ≤ ρ ^ F.card)
    (hexp : (1 + ρ) ^ Fintype.card ι ≤ 2) (s : ι → Bool) : 0 ≤ fourier c s := by
  classical
  set T : Finset ι → ℝ := fun F => c F * ∏ v ∈ F, sgn (s v) with hT
  have habs : ∀ F : Finset ι, F ≠ ∅ → |T F| ≤ ρ ^ F.card := by
    intro F hF
    have hprod : |∏ v ∈ F, sgn (s v)| = 1 := by
      have h2 : |∏ v ∈ F, sgn (s v)| * |∏ v ∈ F, sgn (s v)| = 1 := by
        rw [← abs_mul, prod_sgn_mul_self, abs_one]
      nlinarith [abs_nonneg (∏ v ∈ F, sgn (s v))]
    rw [hT]
    simp only [abs_mul, hprod, mul_one]
    exact hc F hF
  have hT0 : T ∅ = 1 := by rw [hT]; simp [h0]
  have hsum : (∑ F ∈ Finset.univ.erase (∅ : Finset ι), |T F|) ≤ 1 := by
    have e1 : (∑ F ∈ Finset.univ.erase (∅ : Finset ι), |T F|)
        ≤ ∑ F ∈ Finset.univ.erase (∅ : Finset ι), ρ ^ F.card := by
      refine Finset.sum_le_sum fun F hF => habs F (Finset.ne_of_mem_erase hF)
    have e2 : (∑ F ∈ Finset.univ.erase (∅ : Finset ι), ρ ^ F.card)
        = (1 + ρ) ^ Fintype.card ι - 1 := by
      have := Finset.sum_erase_add Finset.univ (fun F : Finset ι => ρ ^ F.card)
        (Finset.mem_univ (∅ : Finset ι))
      rw [sum_pow_card] at this
      simp only [Finset.card_empty, pow_zero] at this
      linarith
    rw [e2] at e1
    linarith
  have hkey : 0 ≤ ∑ F : Finset ι, T F := by
    have hsplit := Finset.sum_erase_add Finset.univ T (Finset.mem_univ (∅ : Finset ι))
    have hbd : |∑ F ∈ Finset.univ.erase (∅ : Finset ι), T F| ≤ 1 :=
      le_trans (Finset.abs_sum_le_sum_abs T _) hsum
    have := (abs_le.1 hbd).1
    rw [hT0] at hsplit
    linarith
  have : fourier c s = (1 / 2 : ℝ) ^ Fintype.card ι * ∑ F : Finset ι, T F := rfl
  rw [this]
  positivity

end Fourier

/-! ## The auxiliary sign density -/

section AuxH

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The auxiliary density `H_{N,q}(s) = 2^{−N} ∑_{|S| even} (−q)^{|S|/2} ∏_S s`. -/
noncomputable def auxH (ι : Type*) [Fintype ι] (q : ℝ) : (ι → Bool) → ℝ :=
  fourier (fun S : Finset ι => if Even S.card then (-q) ^ (S.card / 2) else 0)

/-- The Walsh moments of the auxiliary density. -/
theorem auxH_moment (q : ℝ) (S : Finset ι) :
    (∑ s : ι → Bool, auxH ι q s * ∏ l ∈ S, sgn (s l))
      = if Even S.card then (-q) ^ (S.card / 2) else 0 :=
  fourier_moment _ S

/-- The auxiliary density has total mass one. -/
theorem auxH_sum (q : ℝ) : (∑ s : ι → Bool, auxH ι q s) = 1 := by
  have h := auxH_moment (ι := ι) q ∅
  simpa using h

omit [DecidableEq ι] in
/-- The auxiliary density is nonnegative when `N²q ≤ 1/4`. -/
theorem auxH_nonneg (q : ℝ) (hq0 : 0 ≤ q)
    (hq : ((Fintype.card ι : ℝ)) ^ 2 * q ≤ 1 / 4) (s : ι → Bool) : 0 ≤ auxH ι q s := by
  classical
  set ρ := Real.sqrt q with hρdef
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg q
  have hρsq : ρ * ρ = q := Real.mul_self_sqrt hq0
  have hNρ : (Fintype.card ι : ℝ) * ρ ≤ 1 / 2 := by
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) (Fintype.card ι)) hρ0,
      sq_nonneg ((Fintype.card ι : ℝ) * ρ)]
  refine fourier_nonneg _ ρ hρ0 (by simp) ?_ (one_add_pow_le_two hρ0 hNρ) s
  intro S _
  by_cases hS : Even S.card
  · rw [ite_eq_left hS]
    obtain ⟨j, hj⟩ := hS
    have hcard : S.card / 2 = j := by omega
    rw [hcard, hj]
    have : |(-q) ^ j| = q ^ j := by
      rw [abs_pow, abs_neg, abs_of_nonneg hq0]
    rw [this, ← hρsq]
    have hpow : ρ ^ (j + j) = (ρ * ρ) ^ j := by ring
    rw [hpow]
  · rw [ite_eq_right hS, abs_zero]
    positivity

end AuxH

/-! ## The parity witness of a general pair-source scenario -/

section Parity

variable {Γ : PairGraph} {t : ℕ}

/-- A Walsh character as a power of `-1`. -/
theorem prod_sgn_eq_neg_one_pow {L : Type*} (A : Finset L) (s : L → Bool) :
    (∏ l ∈ A, sgn (s l)) = (-1 : ℝ) ^ (A.filter (fun l => s l = true)).card := by
  classical
  rw [← Finset.prod_filter_mul_prod_filter_not A (fun l => s l = true)]
  have h1 : (∏ l ∈ A.filter (fun l => s l = true), sgn (s l))
      = (-1 : ℝ) ^ (A.filter (fun l => s l = true)).card := by
    rw [Finset.prod_congr rfl (fun l hl => ?_), Finset.prod_const]
    have := (Finset.mem_filter.1 hl).2
    simp [sgn, this]
  have h2 : (∏ l ∈ A.filter (fun l => ¬ (s l = true)), sgn (s l)) = 1 := by
    refine Finset.prod_eq_one fun l hl => ?_
    have hl2 := (Finset.mem_filter.1 hl).2
    simp only [Bool.not_eq_true] at hl2
    simp [sgn, hl2]
  rw [h1, h2, mul_one]

/-- The parity read: a copied observation answers with the parity of the signs of its copied
latent ancestors (`O_v^{ij} = s_{v−1,i} s_{v,j}` for the cycle). -/
def parityRead (s : GLatent Γ t → Bool) : GAssign Γ t :=
  fun o => decide (((gAncestors o).filter (fun l => s l = true)).card % 2 = 1)

theorem sgn_parityRead (s : GLatent Γ t → Bool) (o : GObs Γ t) :
    sgn (parityRead s o) = ∏ l ∈ gAncestors o, sgn (s l) := by
  rw [prod_sgn_eq_neg_one_pow]
  set k := ((gAncestors o).filter (fun l => s l = true)).card with hk
  have : parityRead s o = decide (k % 2 = 1) := rfl
  rw [this]
  rcases Nat.even_or_odd k with h | h
  · rw [h.neg_one_pow]
    have : k % 2 = 0 := Nat.even_iff.1 h
    simp [this, sgn]
  · rw [h.neg_one_pow]
    have : k % 2 = 1 := Nat.odd_iff.1 h
    simp [this, sgn]

/-- The latent boundary of a set of copied observations: the copied sources that an odd number
of members of the set touch. -/
def latBd (A : Finset (GObs Γ t)) : Finset (GLatent Γ t) :=
  Finset.univ.filter (fun l => (A.filter (fun o => l ∈ gAncestors o)).card % 2 = 1)

theorem mem_latBd {A : Finset (GObs Γ t)} {l : GLatent Γ t} :
    l ∈ latBd A ↔ (A.filter (fun o => l ∈ gAncestors o)).card % 2 = 1 := by
  simp [latBd]

/-- A character of a set of copied observations, read through the parity witness, is the
character of its latent boundary. -/
theorem prod_sgn_parityRead (A : Finset (GObs Γ t)) (s : GLatent Γ t → Bool) :
    (∏ o ∈ A, sgn (parityRead s o)) = ∏ l ∈ latBd A, sgn (s l) := by
  have e1 : ∀ o ∈ A, sgn (parityRead s o)
      = ∏ l : GLatent Γ t, (if l ∈ gAncestors o then sgn (s l) else 1) := by
    intro o _
    rw [sgn_parityRead, prod_sgn_eq_prod_univ]
  rw [Finset.prod_congr rfl e1, Finset.prod_comm]
  have e2 : ∀ l : GLatent Γ t,
      (∏ o ∈ A, (if l ∈ gAncestors o then sgn (s l) else 1))
        = if l ∈ latBd A then sgn (s l) else 1 := by
    intro l
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one]
    · rw [Finset.prod_const]
      set k := (A.filter (fun o => l ∈ gAncestors o)).card with hk
      have hsq : sgn (s l) * sgn (s l) = 1 := sgn_mul_self _
      have hpow : sgn (s l) ^ k = if k % 2 = 1 then sgn (s l) else 1 := by
        rcases Nat.even_or_odd k with h | h
        · obtain ⟨j, hj⟩ := h
          have : k % 2 = 0 := Nat.even_iff.1 ⟨j, hj⟩
          rw [ite_eq_right (by omega), hj, ← two_mul, pow_mul]
          have : sgn (s l) ^ 2 = 1 := by rw [pow_two]; exact hsq
          rw [this, one_pow]
        · obtain ⟨j, hj⟩ := h
          have hmod : k % 2 = 1 := Nat.odd_iff.1 ⟨j, hj⟩
          rw [ite_eq_left hmod, hj, pow_add, pow_mul]
          have : sgn (s l) ^ 2 = 1 := by rw [pow_two]; exact hsq
          rw [this, one_pow, one_mul, pow_one]
      rw [hpow]
      by_cases h : l ∈ latBd A
      · rw [ite_eq_left h, ite_eq_left (mem_latBd.1 h)]
      · rw [ite_eq_right h, ite_eq_right (fun hc => h (mem_latBd.2 hc))]
  rw [Finset.prod_congr rfl fun l _ => e2 l, ← prod_sgn_eq_prod_univ]


/-- The auxiliary density is invariant under every permutation of its signs. -/
theorem auxH_perm {ι : Type*} [Fintype ι] (q : ℝ) (e : ι ≃ ι)
    (s : ι → Bool) : auxH ι q (fun l => s (e l)) = auxH ι q s := by
  classical
  simp only [auxH, fourier]
  congr 1
  refine Fintype.sum_bijective (Equiv.finsetCongr e) (Equiv.finsetCongr e).bijective _ _
    fun F => ?_
  have hcard : ((Equiv.finsetCongr e) F).card = F.card := by
    simp [Equiv.finsetCongr_apply]
  have hprod : (∏ v ∈ (Equiv.finsetCongr e) F, sgn (s v)) = ∏ v ∈ F, sgn (s (e v)) := by
    simp [Equiv.finsetCongr_apply, Finset.prod_map]
  rw [hcard, hprod]

/-- The parity witness of a pair-source scenario at order `t`: push the auxiliary sign density
forward along the parity read. -/
noncomputable def parWit (Γ : PairGraph) (t : ℕ) (q : ℝ) : GAssign Γ t → ℝ :=
  pushforward (auxH (GLatent Γ t) q) parityRead

/-- **The master moment identity.** Every Walsh character of the parity witness is the
auxiliary moment of the latent boundary of its index set. -/
theorem parWit_moment (q : ℝ) (A : Finset (GObs Γ t)) :
    (∑ ω : GAssign Γ t, parWit Γ t q ω * ∏ o ∈ A, sgn (ω o))
      = if Even (latBd A).card then (-q) ^ ((latBd A).card / 2) else 0 := by
  rw [parWit, ← Sound.sum_mul_comp]
  rw [Finset.sum_congr rfl fun s _ => by rw [prod_sgn_parityRead A s]]
  exact auxH_moment q (latBd A)

theorem parWit_nonneg (q : ℝ) (hq0 : 0 ≤ q)
    (hq : ((Fintype.card (GLatent Γ t) : ℝ)) ^ 2 * q ≤ 1 / 4) (ω : GAssign Γ t) :
    0 ≤ parWit Γ t q ω := by
  refine Finset.sum_nonneg fun s _ => ?_
  by_cases h : parityRead s = ω
  · rw [ite_eq_left h]; exact auxH_nonneg q hq0 hq s
  · rw [ite_eq_right h]

theorem parWit_sum (q : ℝ) : (∑ ω : GAssign Γ t, parWit Γ t q ω) = 1 := by
  rw [parWit, Sound.sum_pushforward]
  exact auxH_sum q

theorem parWit_isLaw (q : ℝ) (hq0 : 0 ≤ q)
    (hq : ((Fintype.card (GLatent Γ t) : ℝ)) ^ 2 * q ≤ 1 / 4) : IsLaw (parWit Γ t q) :=
  ⟨parWit_nonneg q hq0 hq, parWit_sum q⟩

/-! ### Symmetry -/

theorem gAncestors_gPerm (π : Γ.Edge → Equiv.Perm (Fin t)) (o : GObs Γ t) :
    gAncestors (gPerm π o) = (gAncestors o).image (Sound.gLatentPerm π) := by
  simp only [gAncestors, gPerm, Finset.image_image]
  rfl

theorem parityRead_gLatentPerm (π : Γ.Edge → Equiv.Perm (Fin t)) (s : GLatent Γ t → Bool) :
    parityRead (fun l => s (Sound.gLatentPerm π l)) = gRelabel π (parityRead s) := by
  funext o
  have hinj : Function.Injective (Sound.gLatentPerm π (Γ := Γ) (t := t)) :=
    (Sound.gLatentPerm π).injective
  have hkey : ((gAncestors (gPerm π o)).filter (fun l => s l = true)).card
      = ((gAncestors o).filter (fun l => s (Sound.gLatentPerm π l) = true)).card := by
    rw [gAncestors_gPerm, Finset.filter_image]
    exact Finset.card_image_of_injective _ hinj
  change decide (_ % 2 = 1) = parityRead s (gPerm π o)
  rw [parityRead]
  simp only
  rw [hkey]

theorem gRelabel_injective (π : Γ.Edge → Equiv.Perm (Fin t)) :
    Function.Injective (gRelabel π (Γ := Γ) (t := t)) := by
  intro ω ω' h
  funext o
  obtain ⟨p, hp⟩ := (Sound.gObsPerm π).surjective o
  have := congrFun h p
  simp only [gRelabel] at this
  rw [← hp]
  exact this

theorem parWit_symmetric (q : ℝ) : GSymmetric t (parWit Γ t q) := by
  intro π ω
  simp only [parWit, pushforward]
  refine (Fintype.sum_bijective (fun s l => s (Sound.gLatentPerm π l)) ?_ _ _ fun s => ?_).symm
  · refine ⟨fun s s' h => ?_, fun s => ⟨fun l => s ((Sound.gLatentPerm π).symm l), ?_⟩⟩
    · funext l
      have := congrFun h ((Sound.gLatentPerm π).symm l)
      simpa using this
    · funext l; simp
  · rw [parityRead_gLatentPerm, auxH_perm]
    by_cases h : parityRead s = ω
    · rw [ite_eq_left h, ite_eq_left (congrArg _ h)]
    · rw [ite_eq_right h, ite_eq_right (fun hc => h (gRelabel_injective π hc))]

/-! ### The latent boundary of an ancestrally disjoint family -/

theorem latBd_subset_anc (A : Finset (GObs Γ t)) : latBd A ⊆ gAncestorsOf A := by
  intro l hl
  rw [mem_latBd] at hl
  by_contra hc
  have hemp : A.filter (fun o => l ∈ gAncestors o) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro o ho hlo
    exact hc (Finset.mem_biUnion.2 ⟨o, ho, hlo⟩)
  rw [hemp] at hl
  simp at hl

theorem latBd_biUnion {n : Type*} [Fintype n] (A : n → Finset (GObs Γ t))
    (hd : ∀ k k', k ≠ k' → Disjoint (gAncestorsOf (A k)) (gAncestorsOf (A k'))) :
    latBd (Finset.univ.biUnion A) = Finset.univ.biUnion (fun k => latBd (A k)) := by
  classical
  have hdA : ∀ k k', k ≠ k' → Disjoint (A k) (A k') := fun k k' h =>
    Sound.disjoint_of_gAI (hd k k' h)
  have hsplit : ∀ l : GLatent Γ t,
      ((Finset.univ.biUnion A).filter (fun o => l ∈ gAncestors o)).card
        = ∑ k : n, ((A k).filter (fun o => l ∈ gAncestors o)).card := by
    intro l
    rw [Finset.filter_biUnion, Finset.card_biUnion]
    intro k _ k' _ hkk
    exact Finset.disjoint_filter_filter (hdA k k' hkk)
  have hzero : ∀ (l : GLatent Γ t) (k : n), l ∉ gAncestorsOf (A k) →
      ((A k).filter (fun o => l ∈ gAncestors o)).card = 0 := by
    intro l k hl
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro o ho hlo
    exact hl (Finset.mem_biUnion.2 ⟨o, ho, hlo⟩)
  ext l
  simp only [mem_latBd, Finset.mem_biUnion, Finset.mem_univ, true_and, hsplit]
  constructor
  · intro h
    by_contra hc
    push Not at hc
    have : ∀ k : n, ((A k).filter (fun o => l ∈ gAncestors o)).card % 2 = 0 := by
      intro k
      have := hc k
      omega
    have hev : (∑ k : n, ((A k).filter (fun o => l ∈ gAncestors o)).card) % 2 = 0 := by
      rw [Finset.sum_nat_mod]
      simp [this]
    omega
  · rintro ⟨k, hk⟩
    have hmem : l ∈ gAncestorsOf (A k) := latBd_subset_anc (A k) (mem_latBd.2 hk)
    have hother : ∀ k' : n, k' ≠ k →
        ((A k').filter (fun o => l ∈ gAncestors o)).card = 0 := by
      intro k' hk'
      refine hzero l k' fun hcon => ?_
      exact (Finset.disjoint_left.1 (hd k' k hk') hcon) hmem
    rw [Finset.sum_eq_single k (fun k' _ h => hother k' h) (fun h => absurd (Finset.mem_univ k) h)]
    exact hk

theorem latBd_biUnion_card {n : Type*} [Fintype n] (A : n → Finset (GObs Γ t))
    (hd : ∀ k k', k ≠ k' → Disjoint (gAncestorsOf (A k)) (gAncestorsOf (A k'))) :
    (latBd (Finset.univ.biUnion A)).card = ∑ k : n, (latBd (A k)).card := by
  classical
  rw [latBd_biUnion A hd, Finset.card_biUnion]
  intro k _ k' _ hkk
  exact Finset.disjoint_of_subset_left (latBd_subset_anc (A k))
    (Finset.disjoint_of_subset_right (latBd_subset_anc (A k')) (hd k k' hkk))

end Parity


/-! ## The edge structure of the cycle -/

section CycleStructure

variable {m : ℕ}

/-- The predecessor vertex on the cycle. -/
def cyclePrev (v : Fin m) : Fin m := ⟨(v.val + (m - 1)) % m, Nat.mod_lt _ v.pos⟩

theorem cycleNext_cyclePrev (v : Fin m) : cycleNext (cyclePrev v) = v := by
  have hm : 0 < m := v.pos
  refine Fin.ext ?_
  change ((v.val + (m - 1)) % m + 1) % m = v.val
  rw [Nat.mod_add_mod]
  have h : v.val + (m - 1) + 1 = v.val + m := by omega
  rw [h, Nat.add_mod_right, Nat.mod_eq_of_lt v.isLt]

theorem cyclePrev_cycleNext (v : Fin m) : cyclePrev (cycleNext v) = v := by
  have hm : 0 < m := v.pos
  refine Fin.ext ?_
  change ((v.val + 1) % m + (m - 1)) % m = v.val
  rw [Nat.mod_add_mod]
  have h : v.val + 1 + (m - 1) = v.val + m := by omega
  rw [h, Nat.add_mod_right, Nat.mod_eq_of_lt v.isLt]

theorem cycleNext_ne (hm : 2 ≤ m) (v : Fin m) : cycleNext v ≠ v := by
  intro h
  have hv : (v.val + 1) % m = v.val := congrArg Fin.val h
  have h1 := v.isLt
  rcases lt_or_ge (v.val + 1) m with hl | hl
  · rw [Nat.mod_eq_of_lt hl] at hv; omega
  · have he : v.val + 1 = m := by omega
    rw [he, Nat.mod_self] at hv
    omega

theorem cyclePrev_ne (hm : 2 ≤ m) (v : Fin m) : cyclePrev v ≠ v := by
  intro h
  exact cycleNext_ne hm v (by conv_lhs => rw [← h]; rw [cycleNext_cyclePrev])

theorem cycleNext_cycleNext_ne (hm : 3 ≤ m) (v : Fin m) : cycleNext (cycleNext v) ≠ v := by
  intro h
  have hv : ((v.val + 1) % m + 1) % m = v.val := congrArg Fin.val h
  have h1 := v.isLt
  rcases lt_or_ge (v.val + 1) m with hl | hl
  · rw [Nat.mod_eq_of_lt hl] at hv
    rcases lt_or_ge (v.val + 1 + 1) m with hl2 | hl2
    · rw [Nat.mod_eq_of_lt hl2] at hv; omega
    · have he : v.val + 1 + 1 = m := by omega
      rw [he, Nat.mod_self] at hv; omega
  · have he : v.val + 1 = m := by omega
    rw [he, Nat.mod_self, Nat.mod_eq_of_lt (by omega : 0 + 1 < m)] at hv
    omega

theorem cycleAdj_next (hm : 2 ≤ m) (v : Fin m) : (cycleAdj m).Adj v (cycleNext v) :=
  ⟨(cycleNext_ne hm v).symm, Or.inl rfl⟩

/-- The source of the cycle recorded by its lower endpoint: the edge `{j, j+1}`. -/
def ce (hm : 3 ≤ m) (j : Fin m) : (cycle m hm).Edge :=
  ⟨s(j, cycleNext j), by
    change s(j, cycleNext j) ∈ (cycleAdj m).edgeFinset
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact cycleAdj_next (by omega) j⟩

theorem ce_val (hm : 3 ≤ m) (j : Fin m) : (ce hm j).1 = s(j, cycleNext j) := rfl

theorem mem_ce (hm : 3 ≤ m) (j v : Fin m) :
    v ∈ (ce hm j).1 ↔ (v = j ∨ v = cycleNext j) := Sym2.mem_iff

theorem ce_injective (hm : 3 ≤ m) : Function.Injective (ce hm) := by
  intro j k h
  have h2 : s(j, cycleNext j) = s(k, cycleNext k) := congrArg Subtype.val h
  rw [Sym2.eq_iff] at h2
  rcases h2 with ⟨h3, _⟩ | ⟨h3, h4⟩
  · exact h3
  · exact absurd (by rw [← h3]; exact h4) (cycleNext_cycleNext_ne hm k)

theorem ce_surjective (hm : 3 ≤ m) (e : (cycle m hm).Edge) : ∃ j, e = ce hm j := by
  obtain ⟨x, hx⟩ := e
  revert hx
  induction x using Sym2.ind with
  | _ a b =>
    intro hx
    have hadj : (cycleAdj m).Adj a b := by
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hx
      exact hx
    rcases hadj.2 with h | h
    · refine ⟨a, Subtype.ext ?_⟩
      have hb : b = cycleNext a := Fin.ext h.symm
      subst hb
      rfl
    · refine ⟨b, Subtype.ext ?_⟩
      have ha : a = cycleNext b := Fin.ext h.symm
      subst ha
      change s(cycleNext b, b) = s(b, cycleNext b)
      exact Sym2.eq_swap

theorem mem_inc_iff {Γ : PairGraph} (v : Γ.V) (e : Γ.Edge) :
    e ∈ Γ.inc v ↔ v ∈ (e.1 : Sym2 Γ.V) := by
  simp [PairGraph.inc]

theorem mem_inc_ce (hm : 3 ≤ m) (v j : Fin m) :
    ce hm j ∈ (cycle m hm).inc v ↔ (v = j ∨ v = cycleNext j) :=
  (mem_inc_iff (Γ := cycle m hm) v (ce hm j)).trans Sym2.mem_iff

theorem mem_inc_cycle (hm : 3 ≤ m) (v : Fin m) (e : (cycle m hm).Edge) :
    e ∈ (cycle m hm).inc v ↔ (e = ce hm (cyclePrev v) ∨ e = ce hm v) := by
  obtain ⟨j, rfl⟩ := ce_surjective hm e
  rw [mem_inc_ce]
  constructor
  · rintro (h | h)
    · right; rw [h]
    · left; rw [h, cyclePrev_cycleNext]
  · rintro (h | h)
    · right; rw [ce_injective hm h, cycleNext_cyclePrev]
    · left; exact (ce_injective hm h).symm

/-- The incident source recorded by the predecessor vertex. -/
def incPrev (hm : 3 ≤ m) (v : Fin m) : ((cycle m hm).inc v) :=
  ⟨ce hm (cyclePrev v), (mem_inc_cycle hm v _).2 (Or.inl rfl)⟩

/-- The incident source recorded by the vertex itself. -/
def incSelf (hm : 3 ≤ m) (v : Fin m) : ((cycle m hm).inc v) :=
  ⟨ce hm v, (mem_inc_cycle hm v _).2 (Or.inr rfl)⟩

theorem univ_inc_cycle (hm : 3 ≤ m) (v : Fin m) :
    (Finset.univ : Finset ((cycle m hm).inc v)) = {incPrev hm v, incSelf hm v} := by
  ext e
  simp only [Finset.mem_univ, true_iff, Finset.mem_insert, Finset.mem_singleton]
  rcases (mem_inc_cycle hm v e.1).1 e.2 with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

theorem mem_gAncestors_copyObs (hm : 3 ≤ m) {t : ℕ} (ι : (cycle m hm).Edge → Fin t)
    (v j : Fin m) (r : Fin t) :
    ((ce hm j, r) : GLatent (cycle m hm) t) ∈ gAncestors (copyObs ι v) ↔
      (r = ι (ce hm j) ∧ (v = cycleNext j ∨ v = j)) := by
  rw [gAncestors, Finset.mem_image]
  constructor
  · rintro ⟨e, -, he⟩
    simp only [Prod.mk.injEq] at he
    obtain ⟨h1, h2⟩ := he
    have hval : (copyObs ι v).2 e = ι e.1 := rfl
    refine ⟨by rw [← h2, hval, h1], ?_⟩
    rcases (mem_inc_cycle hm v e.1).1 e.2 with h | h
    · left
      have hj : cyclePrev v = j := ce_injective hm (by rw [← h, h1])
      rw [← hj, cycleNext_cyclePrev]
    · right
      exact (ce_injective hm (by rw [← h, h1])).symm
  · rintro ⟨hr, hv | hv⟩
    · refine ⟨incPrev hm v, Finset.mem_univ _, ?_⟩
      have hfst : (incPrev hm v).1 = ce hm j := by
        change ce hm (cyclePrev v) = ce hm j
        rw [hv, cyclePrev_cycleNext]
      have hval : (copyObs ι v).2 (incPrev hm v) = ι (incPrev hm v).1 := rfl
      rw [Prod.ext_iff]
      exact ⟨hfst, by rw [hval, hfst, hr]⟩
    · refine ⟨incSelf hm v, Finset.mem_univ _, ?_⟩
      have hfst : (incSelf hm v).1 = ce hm j := by
        change ce hm v = ce hm j
        rw [hv]
      have hval : (copyObs ι v).2 (incSelf hm v) = ι (incSelf hm v).1 := rfl
      rw [Prod.ext_iff]
      exact ⟨hfst, by rw [hval, hfst, hr]⟩

end CycleStructure


/-! ## The latent boundary of a block of a copy of the cycle -/

section CycleCount

variable {m t : ℕ}

/-- The vertices of the cycle scenario are `Fin m`; this is that identification, written out
so that equations between vertices elaborate at the type `Fin m`. -/
def vtx (hm : 3 ≤ m) (v : (cycle m hm).V) : Fin m := v

theorem vtx_copyObs (hm : 3 ≤ m) (ι : (cycle m hm).Edge → Fin t) (v : Fin m) :
    vtx hm (copyObs ι v).1 = v := rfl

theorem eq_copyObs' (hm : 3 ≤ m) {ι : (cycle m hm).Edge → Fin t}
    {o : GObs (cycle m hm) t} (h : o ∈ copySet ι) : o = copyObs ι (vtx hm o.1) :=
  Sound.eq_copyObs h

/-- The vertex set of a set of copied observations. -/
def vertSet (hm : 3 ≤ m) (A : Finset (GObs (cycle m hm) t)) : Finset (Fin m) :=
  A.image (fun o => vtx hm o.1)

theorem fst_injOn (hm : 3 ≤ m) {ι : (cycle m hm).Edge → Fin t}
    {A : Finset (GObs (cycle m hm) t)} (hA : A ⊆ copySet ι) :
    Set.InjOn (fun o : GObs (cycle m hm) t => vtx hm o.1) ↑A := by
  intro o ho p hp h
  rw [eq_copyObs' hm (hA ho), eq_copyObs' hm (hA hp)]
  simp only at h
  rw [h]

theorem card_filter_image {α β : Type*} [DecidableEq β] (A : Finset α) (f : α → β)
    (hinj : Set.InjOn f ↑A) (Q : β → Prop) [DecidablePred Q] :
    ((A.image f).filter Q).card = (A.filter (fun a => Q (f a))).card := by
  rw [Finset.filter_image, Finset.card_image_of_injOn]
  exact hinj.mono (by exact_mod_cast Finset.filter_subset _ _)

theorem card_filter_pair {α : Type*} [DecidableEq α] (G : Finset α) (a b : α) (hab : a ≠ b) :
    (G.filter (fun v => v = a ∨ v = b)).card
      = (if a ∈ G then 1 else 0) + (if b ∈ G then 1 else 0) := by
  have hsplit : G.filter (fun v => v = a ∨ v = b)
      = G.filter (fun v => v = a) ∪ G.filter (fun v => v = b) := by
    rw [← Finset.filter_or]
  have hdis : Disjoint (G.filter (fun v => v = a)) (G.filter (fun v => v = b)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    exact hab (by rw [← (Finset.mem_filter.1 hx).2, (Finset.mem_filter.1 hx').2])
  rw [hsplit, Finset.card_union_of_disjoint hdis, Finset.filter_eq', Finset.filter_eq']
  by_cases h1 : a ∈ G <;> by_cases h2 : b ∈ G <;> simp [h1, h2]

theorem count_copy (hm : 3 ≤ m) (ι : (cycle m hm).Edge → Fin t)
    {A : Finset (GObs (cycle m hm) t)} (hA : A ⊆ copySet ι) (j : Fin m) (r : Fin t) :
    (A.filter (fun o => ((ce hm j, r) : GLatent (cycle m hm) t) ∈ gAncestors o)).card
      = if r = ι (ce hm j) then
          ((vertSet hm A).filter (fun v => v = cycleNext j ∨ v = j)).card else 0 := by
  have hcongr : A.filter (fun o => ((ce hm j, r) : GLatent (cycle m hm) t) ∈ gAncestors o)
      = A.filter (fun o => r = ι (ce hm j) ∧
          (vtx hm o.1 = cycleNext j ∨ vtx hm o.1 = j)) := by
    refine Finset.filter_congr fun o ho => ?_
    have h := mem_gAncestors_copyObs hm ι (vtx hm o.1) j r
    rw [← eq_copyObs' hm (hA ho)] at h
    exact h
  rw [hcongr]
  by_cases hr : r = ι (ce hm j)
  · rw [ite_eq_left hr]
    simp only [vertSet]
    rw [card_filter_image A _ (fst_injOn hm hA)]
    refine congrArg Finset.card (Finset.filter_congr fun o _ => ?_)
    simp [hr]
  · rw [ite_eq_right hr, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro o _ hc
    exact hr hc.1

theorem latBd_copy (hm : 3 ≤ m) (ι : (cycle m hm).Edge → Fin t)
    {A : Finset (GObs (cycle m hm) t)} (hA : A ⊆ copySet ι) :
    latBd A = (cycleBoundary m (vertSet hm A)).image (fun j => (ce hm j, ι (ce hm j))) := by
  ext l
  obtain ⟨j, hj⟩ := ce_surjective hm l.1
  have hl : l = (ce hm j, l.2) := by rw [← hj]
  rw [hl, mem_latBd, count_copy hm ι hA j l.2, Finset.mem_image]
  constructor
  · intro h
    have hr : l.2 = ι (ce hm j) := by
      by_contra hc
      rw [ite_eq_right hc] at h
      omega
    rw [ite_eq_left hr, card_filter_pair (vertSet hm A) (cycleNext j) j (cycleNext_ne (by omega) j)]
      at h
    refine ⟨j, ?_, by rw [hr]⟩
    rw [mem_cycleBoundary]
    by_cases h1 : j ∈ vertSet hm A <;> by_cases h2 : cycleNext j ∈ vertSet hm A
    · rw [ite_eq_left h2, ite_eq_left h1] at h; omega
    · exact fun hiff => h2 (hiff.1 h1)
    · exact fun hiff => h1 (hiff.2 h2)
    · rw [ite_eq_right h2, ite_eq_right h1] at h; omega
  · rintro ⟨j', hj', heq⟩
    have hjj : j' = j := ce_injective hm (congrArg Prod.fst heq)
    subst hjj
    have hr : l.2 = ι (ce hm j') := (congrArg Prod.snd heq).symm
    rw [ite_eq_left hr, card_filter_pair (vertSet hm A) (cycleNext j') j'
      (cycleNext_ne (by omega) j')]
    rw [mem_cycleBoundary] at hj'
    by_cases h1 : j' ∈ vertSet hm A <;> by_cases h2 : cycleNext j' ∈ vertSet hm A
    · exact absurd (Iff.intro (fun _ => h2) (fun _ => h1)) hj'
    · rw [ite_eq_right h2, ite_eq_left h1]
    · rw [ite_eq_left h2, ite_eq_right h1]
    · exact absurd (Iff.intro (fun hc => absurd hc h1) (fun hc => absurd hc h2)) hj'

theorem latBd_copy_card (hm : 3 ≤ m) (ι : (cycle m hm).Edge → Fin t)
    {A : Finset (GObs (cycle m hm) t)} (hA : A ⊆ copySet ι) :
    (latBd A).card = (cycleBoundary m (vertSet hm A)).card := by
  rw [latBd_copy hm ι hA, Finset.card_image_of_injective]
  intro a b hab
  exact ce_injective hm (congrArg Prod.fst hab)

end CycleCount


/-! ## Moments of the cycle witness -/

section CycleMoments

variable {m t : ℕ}

/-- Walsh uniqueness transported along an identification of the sample space with a Boolean
cube. -/
theorem eq_of_moments {α : Type*} [Fintype α] {ι : Type*} [Finite ι]
    (E : α ≃ (ι → Bool)) (P Q : α → ℝ)
    (h : ∀ F : Finset ι, (∑ a, P a * ∏ v ∈ F, sgn (E a v))
      = ∑ a, Q a * ∏ v ∈ F, sgn (E a v)) : P = Q := by
  classical
  let := Fintype.ofFinite ι
  have key : (fun s => P (E.symm s)) = (fun s => Q (E.symm s)) := by
    refine eq_of_walsh_moments_eq _ _ fun F => ?_
    have e : ∀ R : α → ℝ, (∑ s : ι → Bool, R (E.symm s) * ∏ v ∈ F, sgn (s v))
        = ∑ a : α, R a * ∏ v ∈ F, sgn (E a v) := by
      intro R
      refine (Fintype.sum_bijective E E.bijective _ _ fun a => ?_).symm
      simp
    rw [e, e]
    exact h F
  funext a
  have hk := congrFun key (E a)
  simpa using hk

theorem parWit_block_moment (hm : 3 ≤ m) (q : ℝ) (ι : (cycle m hm).Edge → Fin t)
    {A : Finset (GObs (cycle m hm) t)} (hA : A ⊆ copySet ι) :
    (∑ ω : GAssign (cycle m hm) t, parWit (cycle m hm) t q ω * ∏ o ∈ A, sgn (ω o))
      = (-q) ^ ((cycleBoundary m (vertSet hm A)).card / 2) := by
  rw [parWit_moment, latBd_copy_card hm ι hA, ite_eq_left (cycleBoundary_card_even _)]

theorem parWit_family_moment (hm : 3 ≤ m) (q : ℝ) {n : Type*} [Fintype n]
    (A : n → Finset (GObs (cycle m hm) t)) (ιf : n → (cycle m hm).Edge → Fin t)
    (hA : ∀ k, A k ⊆ copySet (ιf k))
    (hd : ∀ k k', k ≠ k' → Disjoint (gAncestorsOf (A k)) (gAncestorsOf (A k'))) :
    (∑ ω : GAssign (cycle m hm) t, parWit (cycle m hm) t q ω
        * ∏ o ∈ Finset.univ.biUnion A, sgn (ω o))
      = ∏ k : n, (-q) ^ ((cycleBoundary m (vertSet hm (A k))).card / 2) := by
  classical
  rw [parWit_moment, latBd_biUnion_card A hd,
    Finset.sum_congr rfl (fun k _ => latBd_copy_card hm (ιf k) (hA k))]
  set b : n → ℕ := fun k => (cycleBoundary m (vertSet hm (A k))).card with hb
  have heven : ∀ k, b k % 2 = 0 := fun k => Nat.even_iff.1 (cycleBoundary_card_even _)
  have hsum : (∑ k : n, b k) = 2 * ∑ k : n, b k / 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by have := heven k; omega
  rw [ite_eq_left (by rw [hsum]; exact even_two_mul _), hsum,
    show 2 * (∑ k : n, b k / 2) / 2 = ∑ k : n, b k / 2 by omega,
    ← Finset.prod_pow_eq_pow_sum]

/-- Every copied ancestor of a member of a copy of the original scenario carries that copy's
index. -/
theorem snd_of_mem_gAncestorsOf {Γ : PairGraph} {t : ℕ} {ι : Γ.Edge → Fin t}
    {A : Finset (GObs Γ t)} (hA : A ⊆ copySet ι) {l : GLatent Γ t}
    (hl : l ∈ gAncestorsOf A) : l.2 = ι l.1 := by
  obtain ⟨o, ho, hlo⟩ := Finset.mem_biUnion.1 hl
  rw [Sound.eq_copyObs (hA ho)] at hlo
  obtain ⟨e, -, he⟩ := Finset.mem_image.1 hlo
  rw [← he]
  rfl

end CycleMoments


/-! ## The injectable marginals -/

section Obligations

variable {m t : ℕ}

/-- The moments of the cycle target, read at the vertex type of the scenario. -/
theorem cycleTarget_moment' (hm : 3 ≤ m) (q : ℝ) (F : Finset (Fin m)) :
    (∑ w : (cycle m hm).V → Bool, cycleTarget m q w * ∏ v ∈ F, sgn (w v))
      = (-q) ^ ((cycleBoundary m F).card / 2) := cycleTarget_moment m q F

theorem vertSet_image (hm : 3 ≤ m) {S : Finset (GObs (cycle m hm) t)} (B : Finset ↥S) :
    vertSet hm (B.image (fun p : ↥S => p.1)) = B.image (fun p : ↥S => vtx hm p.1.1) := by
  rw [vertSet, Finset.image_image]
  rfl

theorem image_val_subset (hm : 3 ≤ m) {S : Finset (GObs (cycle m hm) t)} (B : Finset ↥S) :
    B.image (fun p : ↥S => p.1) ⊆ S := by
  intro o ho
  obtain ⟨p, -, hp⟩ := Finset.mem_image.1 ho
  rw [← hp]
  exact p.2

theorem val_inj_on {hm : 3 ≤ m} {S : Finset (GObs (cycle m hm) t)} (B : Finset ↥S) :
    ∀ _x ∈ B, ∀ _y ∈ B, (_x : ↥S).1 = (_y : ↥S).1 → _x = _y :=
  fun _ _ _ _ h => Subtype.ext h

/-- The target moment of a Walsh character of an injectable block. -/
theorem target_block_moment (hm : 3 ≤ m) (q : ℝ) {S : Finset (GObs (cycle m hm) t)}
    (hS : GInjectable S) (B : Finset ↥S) :
    (∑ ψ : ↥S → Bool, pushforward (α := (cycle m hm).V → Bool) (cycleTarget m q)
        (gPartyRead S) ψ * ∏ y ∈ B, sgn (ψ y))
      = (-q) ^ ((cycleBoundary m (B.image (fun p : ↥S => vtx hm p.1.1))).card / 2) := by
  obtain ⟨ι, hι⟩ := hS
  have hSinj : Set.InjOn (fun o : GObs (cycle m hm) t => vtx hm o.1) ↑S := fst_injOn hm hι
  have hinj2 : ∀ x ∈ B, ∀ y ∈ B,
      vtx hm (x : ↥S).1.1 = vtx hm (y : ↥S).1.1 → x = y :=
    fun x _ y _ h => Subtype.ext (hSinj x.2 y.2 h)
  have h1 : (∑ ψ : ↥S → Bool, pushforward (α := (cycle m hm).V → Bool) (cycleTarget m q)
        (gPartyRead S) ψ * ∏ y ∈ B, sgn (ψ y))
      = ∑ w : (cycle m hm).V → Bool, cycleTarget m q w * ∏ y ∈ B, sgn (gPartyRead S w y) :=
    (Sound.sum_mul_comp (α := (cycle m hm).V → Bool) _ _ _).symm
  rw [h1, ← cycleTarget_moment' hm q (B.image (fun p : ↥S => vtx hm p.1.1))]
  refine Finset.sum_congr rfl fun w _ => ?_
  congr 1
  rw [Finset.prod_image hinj2]
  rfl

/-- The witness moment of a Walsh character of an injectable block. -/
theorem wit_block_moment (hm : 3 ≤ m) (q : ℝ) {S : Finset (GObs (cycle m hm) t)}
    (hS : GInjectable S) (B : Finset ↥S) :
    (∑ φ : ↥S → Bool,
        pushforward (parWit (cycle m hm) t q) (gRestrict S) φ * ∏ y ∈ B, sgn (φ y))
      = (-q) ^ ((cycleBoundary m (B.image (fun p : ↥S => vtx hm p.1.1))).card / 2) := by
  obtain ⟨ι, hι⟩ := hS
  have hAS : B.image (fun p : ↥S => p.1) ⊆ copySet ι :=
    (image_val_subset hm B).trans hι
  rw [← vertSet_image hm B, ← parWit_block_moment hm q ι hAS, ← Sound.sum_mul_comp]
  refine Finset.sum_congr rfl fun ω _ => ?_
  congr 1
  rw [Finset.prod_image (val_inj_on B)]
  rfl

theorem parWit_injectable (hm : 3 ≤ m) (q : ℝ) :
    GInjectableMarginals t (parWit (cycle m hm) t q) (cycleTarget m q) := by
  intro S hS
  refine eq_of_moments (Equiv.refl (↥S → Bool)) _ _ fun B => ?_
  simp only [Equiv.refl_apply]
  rw [wit_block_moment hm q hS B, target_block_moment hm q hS B]

theorem gAncestorsOf_mono {Γ : PairGraph} {t : ℕ} {A A' : Finset (GObs Γ t)} (h : A ⊆ A') :
    gAncestorsOf A ⊆ gAncestorsOf A' := by
  intro l hl
  obtain ⟨o, ho, hlo⟩ := Finset.mem_biUnion.1 hl
  exact Finset.mem_biUnion.2 ⟨o, h ho, hlo⟩


/-- The ancestral-independence prescriptions. -/
theorem parWit_ai (hm : 3 ≤ m) (q : ℝ) :
    GAncestralProducts t (parWit (cycle m hm) t q) (cycleTarget m q) := by
  intro n S hinj hai
  have hdisjS : ∀ k k', k ≠ k' → Disjoint (S k) (S k') :=
    fun k k' h => Sound.disjoint_of_gAI (hai k k' h)
  obtain ⟨ιf, hιf⟩ : ∃ ιf : Fin n → ((cycle m hm).Edge → Fin t), ∀ k, S k ⊆ copySet (ιf k) :=
    ⟨fun k => (hinj k).choose, fun k => (hinj k).choose_spec⟩
  refine eq_of_moments (Sound.sigCurry S).symm _ _ fun B => ?_
  set Bf : ∀ k : Fin n, Finset ↥(S k) :=
    fun k => Finset.univ.filter (fun y : ↥(S k) => (⟨k, y⟩ : Σ k : Fin n, ↥(S k)) ∈ B) with hBfdef
  have hBsig : B = Finset.univ.sigma Bf := by
    ext x
    simp [hBfdef, Finset.mem_sigma]
  set A : Fin n → Finset (GObs (cycle m hm) t) :=
    fun k => (Bf k).image (fun y : ↥(S k) => y.1) with hAdef
  have hAsub : ∀ k, A k ⊆ S k := fun k => image_val_subset hm (Bf k)
  have hAcopy : ∀ k, A k ⊆ copySet (ιf k) := fun k => (hAsub k).trans (hιf k)
  have hAai : ∀ k k', k ≠ k' → Disjoint (gAncestorsOf (A k)) (gAncestorsOf (A k')) := by
    intro k k' h
    exact Finset.disjoint_of_subset_left (gAncestorsOf_mono (hAsub k))
      (Finset.disjoint_of_subset_right (gAncestorsOf_mono (hAsub k')) (hai k k' h))
  have hAdisj : ∀ k ∈ (Finset.univ : Finset (Fin n)), ∀ k' ∈ (Finset.univ : Finset (Fin n)),
      k ≠ k' → Disjoint (A k) (A k') :=
    fun k _ k' _ h => Sound.disjoint_of_gAI (hAai k k' h)
  have hvert : ∀ k, vertSet hm (A k) = (Bf k).image (fun p : ↥(S k) => vtx hm p.1.1) :=
    fun k => vertSet_image hm (Bf k)
  have hL : (∑ φ : (k : Fin n) → ↥(S k) → Bool,
        pushforward (parWit (cycle m hm) t q) (fun ω k => gRestrict (S k) ω) φ
          * ∏ x ∈ B, sgn ((Sound.sigCurry S).symm φ x))
      = ∏ k : Fin n, (-q) ^ ((cycleBoundary m (vertSet hm (A k))).card / 2) := by
    rw [← parWit_family_moment hm q A ιf hAcopy hAai, ← Sound.sum_mul_comp]
    refine Finset.sum_congr rfl fun ω _ => ?_
    congr 1
    rw [Finset.prod_biUnion hAdisj, hBsig, Finset.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [hAdef, Finset.prod_image (val_inj_on (Bf k))]
    rfl
  have hR : (∑ φ : (k : Fin n) → ↥(S k) → Bool,
        (∏ k : Fin n, pushforward (α := (cycle m hm).V → Bool) (cycleTarget m q)
            (gPartyRead (S k)) (φ k))
          * ∏ x ∈ B, sgn ((Sound.sigCurry S).symm φ x))
      = ∏ k : Fin n, (-q) ^ ((cycleBoundary m (vertSet hm (A k))).card / 2) := by
    have hsplit : ∀ φ : (k : Fin n) → ↥(S k) → Bool,
        (∏ x ∈ B, sgn ((Sound.sigCurry S).symm φ x)) = ∏ k : Fin n, ∏ y ∈ Bf k, sgn (φ k y) := by
      intro φ
      rw [hBsig, Finset.prod_sigma]
      rfl
    have hstep : (∑ φ : (k : Fin n) → ↥(S k) → Bool,
          (∏ k : Fin n, pushforward (α := (cycle m hm).V → Bool) (cycleTarget m q)
              (gPartyRead (S k)) (φ k))
            * ∏ x ∈ B, sgn ((Sound.sigCurry S).symm φ x))
        = ∑ φ : (k : Fin n) → ↥(S k) → Bool, ∏ k : Fin n,
            (pushforward (α := (cycle m hm).V → Bool) (cycleTarget m q)
              (gPartyRead (S k)) (φ k) * ∏ y ∈ Bf k, sgn (φ k y)) := by
      refine Finset.sum_congr rfl fun φ _ => ?_
      rw [hsplit φ, Finset.prod_mul_distrib]
    rw [hstep, Sound.sum_pi_prod (fun (k : Fin n) (ψ : ↥(S k) → Bool) =>
      pushforward (α := (cycle m hm).V → Bool) (cycleTarget m q) (gPartyRead (S k)) ψ
        * ∏ y ∈ Bf k, sgn (ψ y))]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [target_block_moment hm q (hinj k) (Bf k), hvert k]
  rw [hL, hR]


theorem card_cycle_edge (hm : 3 ≤ m) : Fintype.card ((cycle m hm).Edge) = m :=
  ((Fintype.card_of_bijective (f := ce hm)
    ⟨ce_injective hm, fun e => (ce_surjective hm e).imp fun _ h => h.symm⟩).symm).trans
    (Fintype.card_fin m)

theorem card_cycle_latent (hm : 3 ≤ m) :
    Fintype.card (GLatent (cycle m hm) t) = m * t := by
  have hp : Fintype.card (GLatent (cycle m hm) t)
      = Fintype.card ((cycle m hm).Edge) * Fintype.card (Fin t) := Fintype.card_prod _ _
  rw [hp, card_cycle_edge hm, Fintype.card_fin]

/-- The diagonal law of the witness is the tensor power of the cycle target. -/
theorem parWit_diag (hm : 3 ≤ m) (q : ℝ) :
    pushforward (parWit (cycle m hm) t q) readDiag = gTensorPow t (cycleTarget m q) := by
  refine eq_of_moments (Equiv.curry (Fin t) ((cycle m hm).V) Bool).symm _ _ fun F => ?_
  set Frow : Fin t → Finset (Fin m) :=
    fun r => (F.filter (fun p => p.1 = r)).image (fun p => vtx hm p.2) with hFrowdef
  set Ar : Fin t → Finset (GObs (cycle m hm) t) :=
    fun r => (F.filter (fun p => p.1 = r)).image (Sound.diagObs (cycle m hm) t) with hArdef
  have hfibinj : ∀ r : Fin t, ∀ x ∈ F.filter (fun p => p.1 = r), ∀ y ∈ F.filter (fun p => p.1 = r),
      vtx hm x.2 = vtx hm y.2 → x = y := by
    intro r x hx y hy h
    have hx1 := (Finset.mem_filter.1 hx).2
    have hy1 := (Finset.mem_filter.1 hy).2
    exact Prod.ext (by rw [hx1, hy1]) h
  have hcopy : ∀ r : Fin t, Ar r ⊆ copySet (fun _ : (cycle m hm).Edge => r) := by
    intro r o ho
    obtain ⟨p, hp, hpo⟩ := Finset.mem_image.1 ho
    have hp1 : p.1 = r := (Finset.mem_filter.1 hp).2
    refine Finset.mem_image.2 ⟨p.2, Finset.mem_univ _, ?_⟩
    rw [← hpo, ← hp1]
    rfl
  have hd : ∀ r r' : Fin t, r ≠ r' →
      Disjoint (gAncestorsOf (Ar r)) (gAncestorsOf (Ar r')) := by
    intro r r' hrr
    rw [Finset.disjoint_left]
    intro l hl hl'
    have h1 : l.2 = r := snd_of_mem_gAncestorsOf (hcopy r) hl
    have h2 : l.2 = r' := snd_of_mem_gAncestorsOf (hcopy r') hl'
    exact hrr (by rw [← h1, h2])
  have hArdisj : ∀ r ∈ (Finset.univ : Finset (Fin t)), ∀ r' ∈ (Finset.univ : Finset (Fin t)),
      r ≠ r' → Disjoint (Ar r) (Ar r') :=
    fun r _ r' _ h => Sound.disjoint_of_gAI (hd r r' h)
  have hvert : ∀ r : Fin t, vertSet hm (Ar r) = Frow r := by
    intro r
    rw [hArdef, hFrowdef, vertSet, Finset.image_image]
    rfl
  have hL : (∑ u : Fin t → (cycle m hm).V → Bool,
        pushforward (parWit (cycle m hm) t q) readDiag u
          * ∏ p ∈ F, sgn ((Equiv.curry (Fin t) ((cycle m hm).V) Bool).symm u p))
      = ∏ r : Fin t, (-q) ^ ((cycleBoundary m (Frow r)).card / 2) := by
    rw [Finset.prod_congr rfl (fun r _ => by rw [← hvert r] :
      ∀ r ∈ (Finset.univ : Finset (Fin t)),
        (-q) ^ ((cycleBoundary m (Frow r)).card / 2)
          = (-q) ^ ((cycleBoundary m (vertSet hm (Ar r))).card / 2))]
    rw [← parWit_family_moment hm q Ar (fun r _ => r) hcopy hd, ← Sound.sum_mul_comp]
    refine Finset.sum_congr rfl fun ω _ => ?_
    congr 1
    have hconv : (∏ p ∈ F, sgn ((Equiv.curry (Fin t) ((cycle m hm).V) Bool).symm (readDiag ω) p))
        = ∏ p ∈ F, sgn (ω (Sound.diagObs (cycle m hm) t p)) := rfl
    rw [hconv, Finset.prod_biUnion hArdisj, ← Finset.prod_fiberwise F (fun p => p.1)
      (fun p => sgn (ω (Sound.diagObs (cycle m hm) t p)))]
    refine Finset.prod_congr rfl fun r _ => ?_
    rw [hArdef, Finset.prod_image]
    intro x _ y _ h
    exact Sound.diagObs_injective (cycle m hm) t h
  have hR : (∑ u : Fin t → (cycle m hm).V → Bool,
        gTensorPow t (cycleTarget m q) u
          * ∏ p ∈ F, sgn ((Equiv.curry (Fin t) ((cycle m hm).V) Bool).symm u p))
      = ∏ r : Fin t, (-q) ^ ((cycleBoundary m (Frow r)).card / 2) := by
    have hsplit : ∀ u : Fin t → (cycle m hm).V → Bool,
        (∏ p ∈ F, sgn ((Equiv.curry (Fin t) ((cycle m hm).V) Bool).symm u p))
          = ∏ r : Fin t, ∏ v ∈ Frow r, sgn (u r v) := by
      intro u
      rw [← Finset.prod_fiberwise F (fun p => p.1)
        (fun p => sgn ((Equiv.curry (Fin t) ((cycle m hm).V) Bool).symm u p))]
      refine Finset.prod_congr rfl fun r _ => ?_
      rw [hFrowdef, Finset.prod_image (hfibinj r)]
      refine Finset.prod_congr rfl fun p hp => ?_
      change sgn (u p.1 p.2) = _
      rw [(Finset.mem_filter.1 hp).2]
      rfl
    have hstep : (∑ u : Fin t → (cycle m hm).V → Bool,
          gTensorPow t (cycleTarget m q) u
            * ∏ p ∈ F, sgn ((Equiv.curry (Fin t) ((cycle m hm).V) Bool).symm u p))
        = ∑ u : Fin t → (cycle m hm).V → Bool, ∏ r : Fin t,
            (cycleTarget m q (u r) * ∏ v ∈ Frow r, sgn (u r v)) := by
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [hsplit u,
        show gTensorPow t (cycleTarget m q) u = ∏ r : Fin t, cycleTarget m q (u r) from rfl,
        ← Finset.prod_mul_distrib]
    rw [hstep, Sound.sum_pi_prod (fun (r : Fin t) (w : (cycle m hm).V → Bool) =>
      cycleTarget m q w * ∏ v ∈ Frow r, sgn (w v))]
    exact Finset.prod_congr rfl fun r _ => cycleTarget_moment' hm q (Frow r)
  rw [hL, hR]

end Obligations

end CycleWitnessAux

open CycleWitnessAux in
/-- AUDIT-NOTES A5, the cycle witness. With `N = mt` auxiliary signs `s_{v,i}` carrying the
positive density `H_{N,q}(s) = 2^{−N} ∑_{|S| even} (−q)^{|S|/2} ∏_S s`, and copied
observations `O_v^{ij} = s_{v−1,i} s_{v,j}`, the target `P_{m,q}` with moments
`(−q)^{|∂F|/2}` passes every AI prescription at order `t`, for `q = 1/(4m²t²)`: the
boundaries of ancestrally disjoint injectable blocks are disjoint, so their moments
multiply. -/
theorem cycle_witness' (m t : ℕ) (hm : 3 ≤ m) (ht : 1 ≤ t) (q : ℝ)
    (hq : q = 1 / (4 * (m : ℝ) ^ 2 * (t : ℝ) ^ 2)) :
    GAIFeasible (cycle m hm) t (cycleTarget m q) := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by
    have : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have ht0 : (0 : ℝ) < (t : ℝ) := by
    have : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
    linarith
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  have hcard : ((Fintype.card (GLatent (cycle m hm) t) : ℝ)) ^ 2 * q ≤ 1 / 4 := by
    rw [card_cycle_latent hm, hq]
    have hcast : ((m * t : ℕ) : ℝ) = (m : ℝ) * (t : ℝ) := by push_cast; ring
    rw [hcast]
    have key : ((m : ℝ) * (t : ℝ)) ^ 2 * (1 / (4 * (m : ℝ) ^ 2 * (t : ℝ) ^ 2)) = 1 / 4 := by
      field_simp
    rw [key]
  exact ⟨parWit (cycle m hm) t q, parWit_isLaw (Γ := cycle m hm) q hq0 hcard,
    parWit_symmetric q, parWit_diag hm q, parWit_injectable hm q, parWit_ai hm q⟩

end TriangleInflation.Graph
