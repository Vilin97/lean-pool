/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FrenzyMath
-/
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.Complex.Cardinality
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Order.BourbakiWitt
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.MvPowerSeries.Rename
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.PowerSeries.Ideal
import LeanPool.AndersonConjecture.CompleteDomain.Domain

/-!
# The Complete Domain T -- Local Ring Properties

T = C[[x,y,z]]/(x^2 - yz) is a Noetherian complete local domain
whose residue field has the cardinality of C.
-/

noncomputable section

-- T is local since it's a quotient of a local ring by a proper ideal
instance T_isLocalRing : IsLocalRing T := by
  have : Nontrivial T := Ideal.Quotient.nontrivial_iff.mpr conjI_ne_top
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk conjI) Ideal.Quotient.mk_surjective

noncomputable instance : IsNoetherianRing (MvPowerSeries (Fin 1) ℂ) :=
  isNoetherianRing_of_ringEquiv (PowerSeries ℂ)
    (MvPowerSeries.renameEquiv ℂ (Equiv.equivPUnit (Fin 1))).symm.toRingEquiv

lemma Finsupp.cons_add' {n : ℕ} {a b : ℕ} {s t : Fin n →₀ ℕ} :
    Finsupp.cons (a + b) (s + t) = Finsupp.cons a s + Finsupp.cons b t := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [Finsupp.cons_zero]
  · simp [Finsupp.cons_succ]

lemma Finsupp.tail_add' {n : ℕ} (s t : Fin (n + 1) →₀ ℕ) :
    Finsupp.tail (s + t) = Finsupp.tail s + Finsupp.tail t := by
  ext i
  simp [Finsupp.tail_apply, Finsupp.add_apply]

lemma Finsupp.add_cons_zero {n : ℕ} (s t : Fin (n + 1) →₀ ℕ) :
    (s + t) 0 = s 0 + t 0 := by simp [Finsupp.add_apply]

lemma Finsupp.mem_antidiagonal_cons_iff {n : ℕ} {k : ℕ} {s : Fin n →₀ ℕ}
    {a b : Fin (n + 1) →₀ ℕ} :
    (a, b) ∈ Finset.antidiagonal (Finsupp.cons k s) ↔
      (a 0, b 0) ∈ Finset.antidiagonal k ∧
        (Finsupp.tail a, Finsupp.tail b) ∈ Finset.antidiagonal s := by
  simp only [Finset.mem_antidiagonal]
  constructor
  · intro h
    constructor
    · have := DFunLike.congr_fun h 0
      simp only [Finsupp.add_apply, Finsupp.cons_zero] at this
      exact this
    · ext i
      have := DFunLike.congr_fun h i.succ
      simp only [coe_add, Pi.add_apply] at this
      exact this
  · rintro ⟨h1, h2⟩
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [Finsupp.add_apply, Finsupp.cons_zero, h1]
    · have := DFunLike.congr_fun h2 j
      simp only [coe_add, Pi.add_apply] at this
      exact this

/-- The ring equivalence `MvPowerSeries (Fin 0) R ≃+* R` given by taking the
constant coefficient (its inverse is the constant-series embedding). -/
noncomputable def mvPowerSeriesFin0RingEquiv (R : Type*) [CommSemiring R] :
    MvPowerSeries (Fin 0) R ≃+* R where
  toFun := MvPowerSeries.constantCoeff
  invFun := MvPowerSeries.C
  left_inv f := by
    have huniq : ∀ (m : Fin 0 →₀ ℕ), m = 0 := fun m => by ext i
                                                          exact Fin.elim0 i
    ext m
    simp [huniq m, MvPowerSeries.coeff_C]
  right_inv r := MvPowerSeries.constantCoeff_C r
  map_mul' := map_mul _
  map_add' := map_add _

section MvPowerSeriesFinSuccEquiv

variable {n : ℕ} {R : Type*} [CommSemiring R]

lemma fin1_finsupp_eq {u : Fin 1 →₀ ℕ} : u = Finsupp.single 0 (u 0) := by
  refine Finsupp.ext_iff.mpr (fun i => ?_)
  have : i = (0 : Fin 1) := Subsingleton.elim i 0
  subst this
  simp [Finsupp.single_eq_same]

/-- `MvPowerSeries (Fin (n+1)) R ≃+* MvPowerSeries (Fin 1) (MvPowerSeries (Fin n) R)` -/
noncomputable def mvPowerSeriesFinSuccRingEquiv :
    MvPowerSeries (Fin (n + 1)) R ≃+* MvPowerSeries (Fin 1) (MvPowerSeries (Fin n) R) where
  toFun f u s := f (Finsupp.cons (u 0) s)
  invFun F m := F (Finsupp.single 0 (m 0)) (Finsupp.tail m)
  left_inv f := by
    funext m
    change f (Finsupp.cons ((Finsupp.single (0 : Fin 1) (m 0)) 0) (Finsupp.tail m)) = f m
    simp [Finsupp.single_eq_same, Finsupp.cons_tail]
  right_inv F := by
    funext u s
    change F (Finsupp.single 0 (Finsupp.cons (u 0) s 0))
      (Finsupp.tail (Finsupp.cons (u 0) s)) = F u s
    simp only [Finsupp.cons_zero, Finsupp.tail_cons]
    congr 1
    exact (fin1_finsupp_eq).symm
  map_add' f g := rfl
  map_mul' f g := by
    classical
    -- Strategy: unfold both sides to sums, then reindex via bijection
    funext u s
    set F : MvPowerSeries (Fin 1) (MvPowerSeries (Fin n) R) :=
      fun (u : Fin 1 →₀ ℕ) (s : Fin n →₀ ℕ) => f (Finsupp.cons (u 0) s)
    set G : MvPowerSeries (Fin 1) (MvPowerSeries (Fin n) R) :=
      fun (u : Fin 1 →₀ ℕ) (s : Fin n →₀ ℕ) => g (Finsupp.cons (u 0) s)
    have hLHS : (f * g) (Finsupp.cons (u 0) s) =
        ∑ p ∈ Finset.antidiagonal (Finsupp.cons (u 0) s), f p.1 * g p.2 :=
      MvPowerSeries.coeff_mul (Finsupp.cons (u 0) s) f g
    have hRHS : (F * G) u s =
        ∑ p ∈ Finset.antidiagonal u,
          ∑ q ∈ Finset.antidiagonal s,
            f (Finsupp.cons (p.1 0) q.1) * g (Finsupp.cons (p.2 0) q.2) := by
      change MvPowerSeries.coeff s (MvPowerSeries.coeff u (F * G)) = _
      rw [MvPowerSeries.coeff_mul u F G, map_sum]
      congr 1
      ext p
      change MvPowerSeries.coeff s (MvPowerSeries.coeff p.1 F * MvPowerSeries.coeff p.2 G) = _
      rw [MvPowerSeries.coeff_mul s]
      rfl
    change (f * g) (Finsupp.cons (u 0) s) = (F * G) u s
    rw [hLHS, hRHS, ← Finset.sum_product']
    apply Finset.sum_nbij'
      (fun (ab : (Fin (n + 1) →₀ ℕ) × (Fin (n + 1) →₀ ℕ)) =>
        ((Finsupp.single 0 (ab.1 0), Finsupp.single 0 (ab.2 0)),
         (Finsupp.tail ab.1, Finsupp.tail ab.2)))
      (fun (pq : ((Fin 1 →₀ ℕ) × (Fin 1 →₀ ℕ)) ×
          ((Fin n →₀ ℕ) × (Fin n →₀ ℕ))) =>
        (Finsupp.cons (pq.1.1 0) pq.2.1, Finsupp.cons (pq.1.2 0) pq.2.2))
    · -- forward maps into product set
      intro ⟨a, b⟩ hab
      rw [Finsupp.mem_antidiagonal_cons_iff] at hab
      rw [Finset.mem_product]
      refine ⟨?_, hab.2⟩
      rw [Finset.mem_antidiagonal]
      rw [Finset.mem_antidiagonal] at hab
      apply Finsupp.ext_iff.mpr
      intro i
      have : i = (0 : Fin 1) := Subsingleton.elim i 0
      subst this
      simp [Finsupp.single_eq_same, Finsupp.add_apply, hab.1]
    · -- backward maps into antidiagonal
      intro ⟨⟨u₁, u₂⟩, ⟨v₁, v₂⟩⟩ hpq
      rw [Finset.mem_product] at hpq
      rw [Finsupp.mem_antidiagonal_cons_iff]
      refine ⟨?_, by
        simp only [Fin.isValue, Finsupp.tail_cons, Finset.mem_antidiagonal]
        exact Finset.mem_antidiagonal.mp hpq.2⟩
      rw [Finset.mem_antidiagonal]
      rw [Finset.mem_antidiagonal] at hpq
      simp only [Fin.isValue, Finsupp.cons_zero]
      have := DFunLike.congr_fun hpq.1 (0 : Fin 1)
      simp only [Finsupp.add_apply] at this
      exact this
    · -- left inverse
      intro ⟨a, b⟩ _
      simp only [Finsupp.single_eq_same, Prod.mk.injEq]
      exact ⟨Finsupp.cons_tail a, Finsupp.cons_tail b⟩
    · -- right inverse
      intro ⟨⟨u₁, u₂⟩, ⟨v₁, v₂⟩⟩ _
      simp only [Finsupp.cons_zero, Finsupp.tail_cons, Prod.mk.injEq]
      exact ⟨⟨fin1_finsupp_eq.symm, fin1_finsupp_eq.symm⟩, trivial⟩
    · -- values agree
      intro ⟨a, b⟩ _
      simp only [Finsupp.single_eq_same, Finsupp.cons_tail]

end MvPowerSeriesFinSuccEquiv

/-- The ring equivalence `MvPowerSeries (Fin (n+1)) R ≃+* PowerSeries (MvPowerSeries (Fin n) R)`,
obtained from `mvPowerSeriesFinSuccRingEquiv` by identifying `Fin 1`-variable power series
with ordinary power series. -/
noncomputable def mvPowerSeriesFinSuccRingEquiv' {n : ℕ} {R : Type*} [CommSemiring R] :
    MvPowerSeries (Fin (n + 1)) R ≃+* PowerSeries (MvPowerSeries (Fin n) R) :=
  mvPowerSeriesFinSuccRingEquiv.trans
    ((MvPowerSeries.renameEquiv (MvPowerSeries (Fin n) R)
      (Equiv.equivPUnit (Fin 1))).toRingEquiv)

-- Noetherianity by induction on n, using the Fin (n+1) ≃ PowerSeries (Fin n) equiv
lemma mvPowerSeries_fin_isNoetherianRing {n : ℕ} {R : Type*} [CommRing R]
    [IsNoetherianRing R] : IsNoetherianRing (MvPowerSeries (Fin n) R) := by
  induction n with
  | zero => exact isNoetherianRing_of_ringEquiv R (mvPowerSeriesFin0RingEquiv R).symm
  | succ n ih =>
    haveI := ih
    exact isNoetherianRing_of_ringEquiv (PowerSeries (MvPowerSeries (Fin n) R))
      mvPowerSeriesFinSuccRingEquiv'.symm

lemma mvPowerSeries_fin3_isNoetherianRing :
    IsNoetherianRing (MvPowerSeries (Fin 3) ℂ) := by
  exact mvPowerSeries_fin_isNoetherianRing

-- T is Noetherian as a quotient of a Noetherian ring
instance T_isNoetherianRing : IsNoetherianRing T :=
  @isNoetherianRing_of_surjective (MvPowerSeries (Fin 3) ℂ) _ T _
    (Ideal.Quotient.mk conjI) Ideal.Quotient.mk_surjective mvPowerSeries_fin3_isNoetherianRing

section AdicComplete

open MvPowerSeries Finset Finsupp

/-- Local abbreviation for the maximal ideal of `ℂ[[x,y,z]] = MvPowerSeries (Fin 3) ℂ`. -/
abbrev MPS := IsLocalRing.maximalIdeal (MvPowerSeries (Fin 3) ℂ)

/-- Total degree of a monomial exponent vector `d : Fin 3 →₀ ℕ`. -/
abbrev tdeg (d : Fin 3 →₀ ℕ) : ℕ := d.sum fun _ k => k

lemma tdeg_add (a b : Fin 3 →₀ ℕ) :
    tdeg (a + b) = tdeg a + tdeg b := by
  simp [tdeg, Finsupp.sum_add_index']

lemma constantCoeff_eq_zero_of_mem_MPS
    {m : MvPowerSeries (Fin 3) ℂ}
    (hm : m ∈ MPS) :
    MvPowerSeries.constantCoeff (σ := Fin 3) (R := ℂ) m = 0 := by
  simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_constantCoeff] at hm
  by_contra h
  exact hm (IsUnit.mk0 _ h)

-- If f ∈ MPS^n then all coefficients at degree < n vanish
lemma coeff_eq_zero_of_mem_MPS_pow
    {f : MvPowerSeries (Fin 3) ℂ} {n : ℕ}
    (hf : f ∈ MPS ^ n) :
    ∀ d : Fin 3 →₀ ℕ, tdeg d < n → coeff d f = 0 := by
  induction hf using Submodule.pow_induction_on_left' with
  | algebraMap r => intro d hd
                    omega
  | add _ _ _ _ _ ihx ihy => intro d hd
                             simp [ihx d hd, ihy d hd]
  | mem_mul m hm i x _ ih =>
    intro d hd
    change coeff d (m * x) = 0
    simp only [coeff_mul]
    apply Finset.sum_eq_zero
    intro ⟨a, b⟩ hab
    rw [Finset.mem_antidiagonal] at hab
    -- Case split: if a = 0 then coeff 0 m = 0 since m ∈ MPS; else tdeg b < i
    by_cases ha : a = 0
    · subst ha
      rw [show coeff (0 : Fin 3 →₀ ℕ) m = constantCoeff m from rfl,
          constantCoeff_eq_zero_of_mem_MPS hm, zero_mul]
    · have ha_pos : 1 ≤ tdeg a := by
        have := Finsupp.support_nonempty_iff.mpr ha
        obtain ⟨j, hj⟩ := this
        exact Finset.sum_pos' (fun _ _ => Nat.zero_le _)
          ⟨j, hj, Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hj)⟩
      have hb : tdeg b < i := by
        have := tdeg_add a b
        rw [hab] at this
        omega
      rw [ih b hb, mul_zero]

-- Converse: vanishing coefficients at degree < n implies f ∈ MPS^n
lemma mem_MPS_pow_of_coeff_vanish
    (f : MvPowerSeries (Fin 3) ℂ) (n : ℕ)
    (hf : ∀ d : Fin 3 →₀ ℕ, tdeg d < n → coeff d f = 0) :
    f ∈ MPS ^ n := by
  induction n generalizing f with
  | zero => simp [pow_zero]
  | succ n ih =>
    -- Decompose f = X₀g₀ + X₁g₁ + X₂g₂ where g_i ∈ MPS^n by induction
    have hconst : MvPowerSeries.constantCoeff (σ := Fin 3) (R := ℂ) f = 0 :=
      hf 0 (by simp [tdeg, Finsupp.sum])
    let g₀ : MvPowerSeries (Fin 3) ℂ := fun m => coeff (m + single 0 1) f
    let g₁ : MvPowerSeries (Fin 3) ℂ := fun m =>
      if m 0 = 0 then coeff (m + single 1 1) f else 0
    let g₂ : MvPowerSeries (Fin 3) ℂ := fun m =>
      if m 0 = 0 ∧ m 1 = 0 then coeff (m + single 2 1) f else 0
    have hg₀ : g₀ ∈ MPS ^ n := ih _ fun d hd => by
      change coeff (d + single 0 1) f = 0
      exact hf _ (by
                    rw [tdeg_add]
                    simp [tdeg, Finsupp.sum_single_index]
                    omega)
    have hg₁ : g₁ ∈ MPS ^ n := ih _ fun d hd => by
      change (if d 0 = 0 then coeff (d + single 1 1) f else 0) = 0
      split
      · exact hf _ (by
                      rw [tdeg_add]
                      simp [tdeg, Finsupp.sum_single_index]
                      omega)
      · rfl
    have hg₂ : g₂ ∈ MPS ^ n := ih _ fun d hd => by
      change (if d 0 = 0 ∧ d 1 = 0 then coeff (d + single 2 1) f else 0) = 0
      split
      · exact hf _ (by
                      rw [tdeg_add]
                      simp [tdeg, Finsupp.sum_single_index]
                      omega)
      · rfl
    have hfM : f ∈ MPS := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_constantCoeff, hconst]
      exact not_isUnit_zero
    -- Decompose f = X₀g₀ + X₁g₁ + X₂g₂; each X_i*g_i ∈ MPS^(n+1)
    suffices hdecomp : f = X 0 * g₀ + X 1 * g₁ + X 2 * g₂ by
      rw [hdecomp]
      have hX : ∀ (i : Fin 3), X i ∈ MPS := fun i => by
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_constantCoeff,
            constantCoeff_X]
        exact not_isUnit_zero
      have key : ∀ (i : Fin 3) (g : MvPowerSeries (Fin 3) ℂ), g ∈ MPS ^ n →
          X i * g ∈ MPS ^ (n + 1) := fun i g hg => by
        have := Ideal.mul_mem_mul (hX i) hg
        rwa [show MPS * MPS ^ n = MPS ^ (n + 1) from
          (Ideal.IsTwoSided.pow_succ (I := MPS) n).symm] at this
      exact Ideal.add_mem _
        (Ideal.add_mem _ (key 0 g₀ hg₀) (key 1 g₁ hg₁)) (key 2 g₂ hg₂)
    ext m
    have step (s : Fin 3) (g : MvPowerSeries (Fin 3) ℂ) :
        coeff m (X s * g) = if single s 1 ≤ m then g (m - single s 1) else 0 := by
      change coeff m (monomial (single s 1) 1 * g) = _
      rw [coeff_monomial_mul, one_mul, coeff_apply]
    simp only [map_add, coeff_apply, step]
    have tsub_val (s j : Fin 3) (hle : single s 1 ≤ m) :
        (m - single s 1 : Fin 3 →₀ ℕ) j = m j - (single s 1 : Fin 3 →₀ ℕ) j :=
      Finsupp.tsub_apply _ _ _
    have h_g1_van (d : Fin 3 →₀ ℕ) (hd : d 0 ≠ 0) : g₁ d = 0 := if_neg hd
    have h_g2_van_0 (d : Fin 3 →₀ ℕ) (hd : d 0 ≠ 0) : g₂ d = 0 :=
      if_neg (not_and_of_not_left _ hd)
    have h_g2_van_1 (d : Fin 3 →₀ ℕ) (hd : d 1 ≠ 0) : g₂ d = 0 :=
      if_neg (not_and_of_not_right _ hd)
    -- Case split on which X_i "captures" monomial m
    by_cases hm0 : single (0 : Fin 3) 1 ≤ m
    · rw [if_pos hm0]
      set d₀ := m - single (0 : Fin 3) 1
      have hd₀_add : d₀ + single 0 1 = m := tsub_add_cancel_of_le hm0
      have hm0v := single_le_iff.mp hm0
      change f m = coeff (d₀ + single 0 1) f + _ + _
      rw [hd₀_add, coeff_apply]
      have h0_ne (s : Fin 3) (hs : s ≠ 0) (hle : single s 1 ≤ m) :
          (m - single s 1 : Fin 3 →₀ ℕ) 0 ≠ 0 := by
        rw [tsub_val s 0 hle, single_apply, if_neg hs]
        omega
      have t1 : ∀ h1 : single (1 : Fin 3) 1 ≤ m,
          g₁ (m - single (1 : Fin 3) 1) = 0 :=
        fun h1 => h_g1_van _ (h0_ne 1 (by decide) h1)
      have t2 : ∀ h2 : single (2 : Fin 3) 1 ≤ m,
          g₂ (m - single (2 : Fin 3) 1) = 0 :=
        fun h2 => h_g2_van_0 _ (h0_ne 2 (by decide) h2)
      by_cases h1 : single (1 : Fin 3) 1 ≤ m <;> by_cases h2 : single (2 : Fin 3) 1 ≤ m
      · simp only [if_pos h1, if_pos h2, t1 h1, t2 h2, add_zero]
      · simp only [if_pos h1, if_neg h2, t1 h1, add_zero]
      · simp only [if_neg h1, if_pos h2, t2 h2, add_zero]
      · simp only [if_neg h1, if_neg h2, add_zero]
    · rw [if_neg hm0, zero_add]
      have hm0v : m 0 = 0 := by simp [single_le_iff] at hm0
                                omega
      by_cases hm1 : single (1 : Fin 3) 1 ≤ m
      · rw [if_pos hm1]
        set d₁ := m - single (1 : Fin 3) 1
        have hd₁_add : d₁ + single 1 1 = m := tsub_add_cancel_of_le hm1
        have hm1v := single_le_iff.mp hm1
        have hd₁_0 : d₁ 0 = 0 := by
          change (m - single (1 : Fin 3) 1 : Fin 3 →₀ ℕ) 0 = 0
          rw [tsub_val 1 0 hm1, single_apply]
          simp only [Fin.isValue, one_ne_zero, ↓reduceIte, tsub_zero]
          exact hm0v
        change f m = (if d₁ 0 = 0 then coeff (d₁ + single 1 1) f else 0) + _
        rw [if_pos hd₁_0, hd₁_add, coeff_apply]
        have h1_ne : ∀ h2 : single (2 : Fin 3) 1 ≤ m,
            (m - single (2 : Fin 3) 1 : Fin 3 →₀ ℕ) 1 ≠ 0 := by
          intro h2
          rw [tsub_val 2 1 h2, single_apply, if_neg (by decide : (2 : Fin 3) ≠ 1)]
          omega
        by_cases h2 : single (2 : Fin 3) 1 ≤ m
        · simp only [if_pos h2, h_g2_van_1 _ (h1_ne h2), add_zero]
        · simp only [if_neg h2, add_zero]
      · rw [if_neg hm1, zero_add]
        have hm1v : m 1 = 0 := by simp [single_le_iff] at hm1
                                  omega
        by_cases hm2 : single (2 : Fin 3) 1 ≤ m
        · rw [if_pos hm2]
          set d₂ := m - single (2 : Fin 3) 1
          have hd₂_add : d₂ + single 2 1 = m := tsub_add_cancel_of_le hm2
          have hd₂_0 : d₂ 0 = 0 := by
            change (m - single (2 : Fin 3) 1 : Fin 3 →₀ ℕ) 0 = 0
            rw [tsub_val 2 0 hm2, single_apply]
            simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte, tsub_zero]
            exact hm0v
          have hd₂_1 : d₂ 1 = 0 := by
            change (m - single (2 : Fin 3) 1 : Fin 3 →₀ ℕ) 1 = 0
            rw [tsub_val 2 1 hm2, single_apply]
            simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte, tsub_zero]
            exact hm1v
          change f m = if d₂ 0 = 0 ∧ d₂ 1 = 0 then coeff (d₂ + single 2 1) f else 0
          rw [if_pos ⟨hd₂_0, hd₂_1⟩, hd₂_add, coeff_apply]
        · -- All exponents zero: m = 0, so coeff 0 f = constantCoeff f = 0
          rw [if_neg hm2]
          have hm2v : m 2 = 0 := by simp [single_le_iff] at hm2
                                    omega
          have : m = 0 := by ext i
                             fin_cases i <;> simp_all
          subst this
          exact hconst

-- Precompleteness: coefficients stabilize, so define limit coefficientwise
lemma mvPS_isPrecomplete : IsPrecomplete MPS (MvPowerSeries (Fin 3) ℂ) := by
  rw [isPrecomplete_iff]
  intro f hcauchy
  -- L(d) = coeff d (f(tdeg d + 1)); coefficients stabilize past tdeg d
  refine ⟨fun d => coeff d (f (tdeg d + 1)), fun n => ?_⟩
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
  apply mem_MPS_pow_of_coeff_vanish
  intro d hd
  simp only [map_sub, MvPowerSeries.coeff_apply]
  change coeff d (f n) - coeff d (f (tdeg d + 1)) = 0
  rw [sub_eq_zero]
  by_cases hn : tdeg d + 1 ≤ n
  · have h := hcauchy hn
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h
    have hcoeff := coeff_eq_zero_of_mem_MPS_pow h d (by omega)
    simp only [map_sub] at hcoeff
    exact sub_eq_zero.mp hcoeff |>.symm
  · push Not at hn
    omega

-- Lift Cauchy sequence from T to MvPowerSeries, use mvPS_isPrecomplete, project back
lemma T_isPrecomplete : IsPrecomplete (IsLocalRing.maximalIdeal T) T := by
  rw [isPrecomplete_iff]
  intro f hcauchy
  have M_T_eq : IsLocalRing.maximalIdeal T = MPS.map (Ideal.Quotient.mk conjI) :=
    (IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective).symm
  have M_T_pow_eq : ∀ k, (IsLocalRing.maximalIdeal T) ^ k =
      (MPS ^ k).map (Ideal.Quotient.mk conjI) := by
    intro k
    rw [M_T_eq, Ideal.map_pow]
  -- Lift elements of (maximalIdeal T)^k to MPS^k via surjectivity of mk
  have lift_mem : ∀ (x : T) (k : ℕ), x ∈ (IsLocalRing.maximalIdeal T) ^ k →
      ∃ y, y ∈ MPS ^ k ∧ Ideal.Quotient.mk conjI y = x := by
    intro x k hx
    rw [M_T_pow_eq] at hx
    exact (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hx
  obtain ⟨g0, hg0⟩ := Ideal.Quotient.mk_surjective (f 0)
  have diff_mem : ∀ n, f n - f (n + 1) ∈ (IsLocalRing.maximalIdeal T) ^ n := by
    intro n
    have h := hcauchy (Nat.le_succ n)
    rwa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h
  have : ∀ n, ∃ δ, δ ∈ MPS ^ n ∧ Ideal.Quotient.mk conjI δ = f n - f (n + 1) := by
    intro n
    exact lift_mem _ n (diff_mem n)
  choose δ hδ_mem hδ_eq using this
  -- Define g by accumulating lifts: g n = g0 - ∑_{i<n} δ i
  let g : ℕ → MvPowerSeries (Fin 3) ℂ := fun n => g0 - ∑ i ∈ Finset.range n, δ i
  -- Verify mk(g n) = f n by telescoping: mk(δ i) = f i - f(i+1)
  have hg_mk : ∀ n, Ideal.Quotient.mk conjI (g n) = f n := by
    intro n
    induction n with
    | zero => simp only [g, Finset.range_zero, Finset.sum_empty, sub_zero]
              exact hg0
    | succ n ihn =>
      change Ideal.Quotient.mk conjI (g0 - ∑ i ∈ Finset.range (n + 1), δ i) = f (n + 1)
      rw [Finset.sum_range_succ, ← sub_sub, map_sub, map_sub, map_sum]
      conv_lhs => rw [show Ideal.Quotient.mk conjI g0 -
        ∑ x ∈ Finset.range n, Ideal.Quotient.mk conjI (δ x) =
        Ideal.Quotient.mk conjI (g n) from by simp [g, map_sub, map_sum]]
      rw [ihn, hδ_eq n, sub_sub_cancel]
  -- g is Cauchy: δ i ∈ MPS^i ⊆ MPS^n for i ≥ n
  have hg_cauchy : ∀ {m n : ℕ}, n ≤ m → g m - g n ∈ MPS ^ n := by
    intro m n hnm
    change (g0 - ∑ i ∈ Finset.range m, δ i) -
      (g0 - ∑ i ∈ Finset.range n, δ i) ∈ MPS ^ n
    suffices h : ∑ i ∈ Finset.range m \ Finset.range n, δ i ∈ MPS ^ n by
      have calc_eq : (g0 - ∑ i ∈ Finset.range m, δ i) - (g0 - ∑ i ∈ Finset.range n, δ i) =
          -(∑ i ∈ Finset.range m \ Finset.range n, δ i) := by
        rw [← Finset.sum_sdiff (Finset.range_mono hnm)]
        ring
      rw [calc_eq, neg_mem_iff]
      exact h
    apply Ideal.sum_mem
    intro i hi
    rw [Finset.mem_sdiff, Finset.mem_range, Finset.mem_range] at hi
    exact Ideal.pow_le_pow_right (show n ≤ i by omega) (hδ_mem i)
  -- Use MvPowerSeries precompleteness to get limit G, then project to T
  have hprec := mvPS_isPrecomplete.prec' (f := g)
  have hcauchyG : ∀ {m n : ℕ}, m ≤ n → g m ≡ g n
      [SMOD (MPS ^ m • ⊤ :
        Submodule (MvPowerSeries (Fin 3) ℂ) (MvPowerSeries (Fin 3) ℂ))] := by
    intro m n hmn
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
    have h := hg_cauchy hmn
    rwa [show g m - g n = -(g n - g m) by ring, neg_mem_iff]
  obtain ⟨G, hG⟩ := hprec hcauchyG
  refine ⟨Ideal.Quotient.mk conjI G, fun n => ?_⟩
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, M_T_pow_eq]
  rw [← hg_mk n, ← map_sub]
  exact Ideal.mem_map_of_mem _ (by
    have := hG n
    rwa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this)

end AdicComplete

/-- T is complete with respect to its maximal ideal. -/
instance T_isAdicComplete : IsAdicComplete (IsLocalRing.maximalIdeal T) T where
  toIsHausdorff := inferInstance
  toIsPrecomplete := T_isPrecomplete

open MvPowerSeries Finsupp in
lemma mvPS_mem_span_X_of_constantCoeff_zero {k : Type*} [CommRing k]
    (f : MvPowerSeries (Fin 3) k) (hf : MvPowerSeries.constantCoeff f = 0) :
    f ∈ Ideal.span ({(X 0 : MvPowerSeries (Fin 3) k), X 1, X 2} : Set _) := by
  let I := Ideal.span ({(X 0 : MvPowerSeries (Fin 3) k), X 1, X 2} : Set _)
  let g₀ : MvPowerSeries (Fin 3) k := fun m => coeff (m + single 0 1) f
  let g₁ : MvPowerSeries (Fin 3) k := fun m =>
    if m 0 = 0 then coeff (m + single 1 1) f else 0
  let g₂ : MvPowerSeries (Fin 3) k := fun m =>
    if m 0 = 0 ∧ m 1 = 0 then coeff (m + single 2 1) f else 0
  have hX0 : X 0 * g₀ ∈ I := I.mul_mem_right _ (Ideal.subset_span (by simp))
  have hX1 : X 1 * g₁ ∈ I := I.mul_mem_right _ (Ideal.subset_span (by simp))
  have hX2 : X 2 * g₂ ∈ I := I.mul_mem_right _ (Ideal.subset_span (by simp))
  suffices hkey : f = X 0 * g₀ + X 1 * g₁ + X 2 * g₂ by
    rw [hkey]
    exact I.add_mem (I.add_mem hX0 hX1) hX2
  ext m
  have step (s : Fin 3) (g : MvPowerSeries (Fin 3) k) :
      coeff m (X s * g) = if single s 1 ≤ m then g (m - single s 1) else 0 := by
    change coeff m (monomial (single s 1) 1 * g) = _
    rw [coeff_monomial_mul, one_mul, coeff_apply]
  simp only [map_add, coeff_apply, step]
  have tsub_val (s j : Fin 3) (hle : single s 1 ≤ m) :
      (m - single s 1 : Fin 3 →₀ ℕ) j = m j - (single s 1 : Fin 3 →₀ ℕ) j :=
    Finsupp.tsub_apply _ _ _
  have h_g1_van (d : Fin 3 →₀ ℕ) (hd : d 0 ≠ 0) : g₁ d = 0 := if_neg hd
  have h_g2_van_0 (d : Fin 3 →₀ ℕ) (hd : d 0 ≠ 0) : g₂ d = 0 :=
    if_neg (not_and_of_not_left _ hd)
  have h_g2_van_1 (d : Fin 3 →₀ ℕ) (hd : d 1 ≠ 0) : g₂ d = 0 :=
    if_neg (not_and_of_not_right _ hd)
  by_cases hm0 : single (0 : Fin 3) 1 ≤ m
  · rw [if_pos hm0]
    set d₀ := m - single (0 : Fin 3) 1
    have hd₀_add : d₀ + single 0 1 = m := tsub_add_cancel_of_le hm0
    have hm0v := single_le_iff.mp hm0
    change f m = coeff (d₀ + single 0 1) f + _ + _
    rw [hd₀_add, coeff_apply]
    have h0_ne (s : Fin 3) (hs : s ≠ 0) (hle : single s 1 ≤ m) :
        (m - single s 1 : Fin 3 →₀ ℕ) 0 ≠ 0 := by
      rw [tsub_val s 0 hle, single_apply, if_neg hs]
      simp
      omega
    have t1 : ∀ h1 : single (1 : Fin 3) 1 ≤ m,
        g₁ (m - single (1 : Fin 3) 1) = 0 := fun h1 => h_g1_van _ (h0_ne 1 (by decide) h1)
    have t2 : ∀ h2 : single (2 : Fin 3) 1 ≤ m,
        g₂ (m - single (2 : Fin 3) 1) = 0 := fun h2 => h_g2_van_0 _ (h0_ne 2 (by decide) h2)
    by_cases h1 : single (1 : Fin 3) 1 ≤ m <;> by_cases h2 : single (2 : Fin 3) 1 ≤ m <;>
      simp only [h1, h2, t1, t2, ↓reduceIte, add_zero]
  · rw [if_neg hm0, zero_add]
    have hm0v : m 0 = 0 := by simp [single_le_iff] at hm0
                              omega
    by_cases hm1 : single (1 : Fin 3) 1 ≤ m
    · rw [if_pos hm1]
      set d₁ := m - single (1 : Fin 3) 1
      have hd₁_add : d₁ + single 1 1 = m := tsub_add_cancel_of_le hm1
      have hm1v := single_le_iff.mp hm1
      have hd₁_0 : d₁ 0 = 0 := by
        change (m - single (1 : Fin 3) 1 : Fin 3 →₀ ℕ) 0 = 0
        rw [tsub_val 1 0 hm1, single_apply]
        simp only [Fin.isValue, one_ne_zero, ↓reduceIte, tsub_zero]
        exact hm0v
      change f m = (if d₁ 0 = 0 then coeff (d₁ + single 1 1) f else 0) + _
      rw [if_pos hd₁_0, hd₁_add, coeff_apply]
      have h1_ne : ∀ h2 : single (2 : Fin 3) 1 ≤ m,
          (m - single (2 : Fin 3) 1 : Fin 3 →₀ ℕ) 1 ≠ 0 := by
        intro h2
        rw [tsub_val 2 1 h2, single_apply]
        simp
        omega
      by_cases h2 : single (2 : Fin 3) 1 ≤ m <;>
        simp only [h2, ↓reduceIte, add_zero]
      exact (h_g2_van_1 _ (h1_ne ‹_›) ▸ add_zero (f m)).symm
    · rw [if_neg hm1, zero_add]
      have hm1v : m 1 = 0 := by simp [single_le_iff] at hm1
                                omega
      by_cases hm2 : single (2 : Fin 3) 1 ≤ m
      · rw [if_pos hm2]
        set d₂ := m - single (2 : Fin 3) 1
        have hd₂_add : d₂ + single 2 1 = m := tsub_add_cancel_of_le hm2
        have hd₂_0 : d₂ 0 = 0 := by
          change (m - single (2 : Fin 3) 1 : Fin 3 →₀ ℕ) 0 = 0
          rw [tsub_val 2 0 hm2, single_apply]
          simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte, tsub_zero]
          exact hm0v
        have hd₂_1 : d₂ 1 = 0 := by
          change (m - single (2 : Fin 3) 1 : Fin 3 →₀ ℕ) 1 = 0
          rw [tsub_val 2 1 hm2, single_apply]
          simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte, tsub_zero]
          exact hm1v
        change f m = if d₂ 0 = 0 ∧ d₂ 1 = 0 then coeff (d₂ + single 2 1) f else 0
        rw [if_pos ⟨hd₂_0, hd₂_1⟩, hd₂_add, coeff_apply]
      · rw [if_neg hm2]
        have hm2v : m 2 = 0 := by simp [single_le_iff] at hm2
                                  omega
        have : m = 0 := by ext i
                           fin_cases i <;> assumption
        subst this
        exact hf

-- maximalIdeal = span{X₀, X₁, X₂}: ⊆ by decomposition, ⊇ since each X_i has zero constant term
open MvPowerSeries in
lemma mvPS_maximalIdeal_eq_span_X :
    IsLocalRing.maximalIdeal (MvPowerSeries (Fin 3) ℂ) =
    Ideal.span ({(X 0 : MvPowerSeries (Fin 3) ℂ), X 1, X 2} : Set _) := by
  apply le_antisymm
  · intro f hf
    simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hf
    rw [MvPowerSeries.isUnit_iff_constantCoeff] at hf
    exact mvPS_mem_span_X_of_constantCoeff_zero f (by
                                                     by_contra h
                                                     exact hf (IsUnit.mk0 _ h))
  · apply Ideal.span_le.mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    simp only [SetLike.mem_coe, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      MvPowerSeries.isUnit_iff_constantCoeff]
    rcases hx with rfl | rfl | rfl <;>
      simp [MvPowerSeries.constantCoeff_X]

-- dim ≤ 3 by Krull's height theorem: maxIdeal is 3-generated
open MvPowerSeries in
lemma mvPS_ringKrullDim_le :
    ringKrullDim (MvPowerSeries (Fin 3) ℂ) ≤ 3 := by
  haveI : IsNoetherianRing (MvPowerSeries (Fin 3) ℂ) := mvPowerSeries_fin3_isNoetherianRing
  -- dim = height(maxIdeal) for local rings; then apply Krull's height theorem
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, mvPS_maximalIdeal_eq_span_X]
  have hne : Ideal.span ({(X 0 : MvPowerSeries (Fin 3) ℂ), X 1, X 2} : Set _) ≠ ⊤ := by
    rw [← mvPS_maximalIdeal_eq_span_X]
    exact (IsLocalRing.maximalIdeal.isMaximal (R := MvPowerSeries (Fin 3) ℂ)).ne_top
  have h1 : (Ideal.span ({(X 0 : MvPowerSeries (Fin 3) ℂ), X 1, X 2} : Set _)).height ≤
      (Ideal.span ({(X 0 : MvPowerSeries (Fin 3) ℂ), X 1, X 2} : Set _)).spanFinrank :=
    Ideal.height_le_spanFinrank _ hne
  have h2 : (Ideal.span ({(X 0 : MvPowerSeries (Fin 3) ℂ), X 1, X 2} :
      Set _)).spanFinrank ≤ 3 := by
    have hfin : ({(X 0 : MvPowerSeries (Fin 3) ℂ), X 1, X 2} : Set _).Finite :=
      Set.Finite.insert _ (Set.Finite.insert _ (Set.finite_singleton _))
    exact le_trans (Submodule.spanFinrank_span_le_ncard_of_finite hfin) (by
      calc ({(X 0 : MvPowerSeries (Fin 3) ℂ), X 1, X 2} : Set _).ncard
          ≤ ({X 1, X 2} : Set (MvPowerSeries (Fin 3) ℂ)).ncard + 1 := Set.ncard_insert_le _ _
        _ ≤ ({X 2} : Set (MvPowerSeries (Fin 3) ℂ)).ncard + 1 + 1 := by
            gcongr
            exact Set.ncard_insert_le _ _
        _ ≤ 1 + 1 + 1 := by gcongr
                            exact le_of_eq (Set.ncard_singleton _)
        _ = 3 := by norm_num)
  change (↑(Ideal.span _).height : WithBot ℕ∞) ≤ 3
  calc (↑(Ideal.span _).height : WithBot ℕ∞)
      ≤ ↑(Ideal.span _).spanFinrank := by exact_mod_cast h1
    _ ≤ 3 := by exact_mod_cast h2

-- gen = x² - yz is a non-zero-divisor in the maximal ideal
open MvPowerSeries nonZeroDivisors in
lemma gen_mem_nonZeroDivisors :
    (X 0 : MvPowerSeries (Fin 3) ℂ) ^ 2 - X 1 * X 2 ∈ (MvPowerSeries (Fin 3) ℂ)⁰ :=
  mem_nonZeroDivisors_of_ne_zero anderson_gen_ne_zero

open MvPowerSeries in
lemma gen_mem_maximalIdeal :
    (X 0 : MvPowerSeries (Fin 3) ℂ) ^ 2 - X 1 * X 2 ∈
    IsLocalRing.maximalIdeal (MvPowerSeries (Fin 3) ℂ) := by
  simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    MvPowerSeries.isUnit_iff_constantCoeff]
  simp [map_sub, map_pow, map_mul, constantCoeff_X]

-- Injectivity of ℂ → MvPowerSeries → T: gen has zero constant term
open MvPowerSeries in
lemma cToT_injective : Function.Injective
    ((Ideal.Quotient.mk conjI).comp (MvPowerSeries.C (σ := Fin 3) (R := ℂ))) := by
  intro a b hab
  simp only [RingHom.comp_apply] at hab
  have hmem : C (σ := Fin 3) a - C (σ := Fin 3) b ∈ conjI := Ideal.Quotient.eq.mp hab
  rw [← map_sub, conjI, Ideal.mem_span_singleton] at hmem
  obtain ⟨q, hq⟩ := hmem
  have h1 := congr_arg (constantCoeff (σ := Fin 3) (R := ℂ)) hq
  simp only [MvPowerSeries.constantCoeff_C, map_mul, map_sub, map_pow,
    constantCoeff_X, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, mul_zero, sub_zero, zero_mul] at h1
  exact sub_eq_zero.mp h1

-- |Fin 3 →₀ ℕ| = ℵ₀ and |ℂ| = continuum, so |(Fin 3 →₀ ℕ) → ℂ| = |ℂ|
lemma mvPS_card_eq : Cardinal.mk (MvPowerSeries (Fin 3) ℂ) = Cardinal.mk ℂ := by
  change Cardinal.mk ((Fin 3 →₀ ℕ) → ℂ) = Cardinal.mk ℂ
  rw [Cardinal.mk_arrow]
  simp only [Cardinal.lift_id]
  rw [Cardinal.mk_complex]
  rw [le_antisymm Cardinal.mk_le_aleph0 (Cardinal.aleph0_le_mk_iff.mpr (Infinite.of_injective
    (fun n => Finsupp.single (0 : Fin 3) n) (Finsupp.single_injective _)))]
  exact Cardinal.continuum_power_aleph0

/-- |T| = |ℂ| (a power series ring over ℂ in finitely many vars has cardinality |ℂ|). -/
theorem T_card_eq : Cardinal.mk T = Cardinal.mk ℂ :=
  le_antisymm
    ((Cardinal.mk_le_of_surjective Ideal.Quotient.mk_surjective).trans mvPS_card_eq.le)
    (Cardinal.mk_le_of_injective cToT_injective)

-- If mk(g) is a unit in T, then constantCoeff g is a unit in ℂ
lemma unit_of_mk_unit_T (g : MvPowerSeries (Fin 3) ℂ)
    (h : IsUnit (Ideal.Quotient.mk conjI g)) : IsUnit (MvPowerSeries.constantCoeff g) := by
  obtain ⟨⟨u, v, huv, hvu⟩, hu⟩ := h
  obtain ⟨f₁, rfl⟩ := Ideal.Quotient.mk_surjective v
  have h1 : g * f₁ - 1 ∈ conjI := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_one]
    exact sub_eq_zero.mpr (hu ▸ huv)
  have hcc_I : ∀ x ∈ conjI, MvPowerSeries.constantCoeff (σ := Fin 3) (R := ℂ) x = 0 := by
    intro x hx
    rw [conjI, Ideal.mem_span_singleton] at hx
    obtain ⟨c, rfl⟩ := hx
    simp [map_mul, map_sub, map_pow, MvPowerSeries.constantCoeff_X]
  have hcc := hcc_I _ h1
  simp only [map_sub, map_mul, map_one] at hcc
  exact IsUnit.of_mul_eq_one (MvPowerSeries.constantCoeff f₁) (sub_eq_zero.mp hcc)

open MvPowerSeries in
lemma mk_sub_C_mem_maxIdeal_T (f : MvPowerSeries (Fin 3) ℂ) :
    Ideal.Quotient.mk conjI (f - MvPowerSeries.C (σ := Fin 3) (constantCoeff f)) ∈
    IsLocalRing.maximalIdeal T := by
  rw [IsLocalRing.mem_maximalIdeal]
  intro hu
  have hcc := unit_of_mk_unit_T _ hu
  have : constantCoeff (f - MvPowerSeries.C (σ := Fin 3) (constantCoeff f)) = 0 := by
    simp [map_sub, MvPowerSeries.constantCoeff_C]
  rw [this] at hcc
  exact (not_isUnit_zero hcc).elim

open MvPowerSeries in
/-- The composite `ℂ →[C] MvPowerSeries (Fin 3) ℂ →[mk] T →[residue] T/M` from `ℂ` to the
residue field of `T`. -/
noncomputable def cToResT : ℂ →+* IsLocalRing.ResidueField T :=
  (IsLocalRing.residue T).comp ((Ideal.Quotient.mk conjI).comp (C (σ := Fin 3)))

-- Surjectivity: every class in T/M has a constant representative
open MvPowerSeries in
lemma cToResT_surjective : Function.Surjective cToResT := by
  intro x
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective t
  use constantCoeff f
  change (Ideal.Quotient.mk (IsLocalRing.maximalIdeal T))
      ((Ideal.Quotient.mk conjI) (C (constantCoeff f))) =
    (Ideal.Quotient.mk (IsLocalRing.maximalIdeal T))
      ((Ideal.Quotient.mk conjI) f)
  rw [Ideal.Quotient.eq, ← map_sub]
  have : C (σ := Fin 3) (constantCoeff f) - f = -(f - C (constantCoeff f)) := by ring
  rw [this, map_neg]
  exact neg_mem (mk_sub_C_mem_maxIdeal_T f)

-- Injectivity: distinct constants map to distinct residue classes
open MvPowerSeries in
lemma cToResT_injective : Function.Injective cToResT := by
  intro a b hab
  by_contra h
  change (Ideal.Quotient.mk (IsLocalRing.maximalIdeal T))
      ((Ideal.Quotient.mk conjI) (C (σ := Fin 3) a)) =
    (Ideal.Quotient.mk (IsLocalRing.maximalIdeal T))
      ((Ideal.Quotient.mk conjI) (C (σ := Fin 3) b)) at hab
  rw [Ideal.Quotient.eq, ← map_sub, ← map_sub] at hab
  rw [IsLocalRing.mem_maximalIdeal] at hab
  apply hab
  apply (Ideal.Quotient.mk conjI).isUnit_map
  rw [MvPowerSeries.isUnit_iff_constantCoeff, MvPowerSeries.constantCoeff_C]
  exact IsUnit.mk0 _ (sub_ne_zero.mpr h)

/-- |T/M| = |ℂ| (the residue field is ℂ). -/
theorem T_residueField_card :
    Cardinal.mk (IsLocalRing.ResidueField T) = Cardinal.mk ℂ :=
  le_antisymm
    (Cardinal.mk_le_of_surjective cToResT_surjective)
    (Cardinal.mk_le_of_injective cToResT_injective)
