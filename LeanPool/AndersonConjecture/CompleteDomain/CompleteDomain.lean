/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FrenzyMath
-/
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.LinearAlgebra.AffineSpace.Combination
import LeanPool.AndersonConjecture.CompleteDomain.LocalRing

/-!
# The Complete Local Domain T = C[[x,y,z]]/(x^2-yz)

This folder constructs the complete local domain T used in the
main counterexample. T is the quotient of C[[x,y,z]] by the
ideal (x^2-yz). It is a two-dimensional Noetherian complete local
domain with a height-one prime Q = (x,y) that is not principal.
-/

noncomputable section

open MvPowerSeries in
/-- Q = (x, y)T, the height-1 prime that is not principal.
Here x = image of X 0, y = image of X 1 in T. -/
def Q : Ideal T :=
  Ideal.span {Ideal.Quotient.mk conjI (X 0), Ideal.Quotient.mk conjI (X 1)}

/-- Ring hom from MvPowerSeries (Fin 3) ℂ to PowerSeries ℂ that "projects onto X₂":
    φ(f)(n) = coeff (Finsupp.single 2 n) f.
    This sends X₀ ↦ 0, X₁ ↦ 0, X₂ ↦ X. -/
noncomputable def phiToPS : MvPowerSeries (Fin 3) ℂ →+* PowerSeries ℂ where
  toFun f := PowerSeries.mk (fun n => MvPowerSeries.coeff (Finsupp.single 2 n) f)
  map_one' := by
    ext n
    simp only [PowerSeries.coeff_mk, MvPowerSeries.coeff_one, Finsupp.single_eq_zero]
    erw [PowerSeries.coeff_one]
  map_mul' f g := by
    apply PowerSeries.ext
    intro n
    simp only [PowerSeries.coeff_mk]
    erw [PowerSeries.coeff_mul]
    rw [MvPowerSeries.coeff_mul, Finsupp.antidiagonal_single, Finset.sum_map]
    congr 1
    ext ⟨a, b⟩
    simp [PowerSeries.coeff_mk]
  map_zero' := by
    ext n
    simp only [PowerSeries.coeff_mk, map_zero]
  map_add' f g := by
    ext n
    simp only [PowerSeries.coeff_mk, map_add]

open MvPowerSeries in
/-- The ideal P = (X₀, X₁) in MvPowerSeries (Fin 3) ℂ. -/
def PPre : Ideal (MvPowerSeries (Fin 3) ℂ) :=
  Ideal.span {X 0, X 1}

open MvPowerSeries in
/-- conjI ≤ PPre: x²-yz ∈ (X₀, X₁) since x² ∈ (X₀) and yz ∈ (X₁). -/
theorem conjI_le_PPre : conjI ≤ PPre := by
  rw [conjI, Ideal.span_le]
  intro f hf
  simp only [Set.mem_singleton_iff] at hf
  subst hf
  change (X (0 : Fin 3)) ^ 2 - (X 1) * (X 2) ∈ PPre
  apply Ideal.sub_mem
  · rw [sq]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert _ _))
  · exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert_iff.mpr (Or.inr rfl)))

open MvPowerSeries in
/-- "Division by X s": shifts the s-index down by 1. -/
def divX (s : Fin 3) (f : MvPowerSeries (Fin 3) ℂ) : MvPowerSeries (Fin 3) ℂ :=
  fun m => f (m + Finsupp.single s 1)

open MvPowerSeries in
/-- f - X s * divX s f vanishes whenever m s ≥ 1, and equals f(m) when m s = 0. -/
theorem coeff_sub_X_mul_divX
    (s : Fin 3) (f : MvPowerSeries (Fin 3) ℂ) (m : Fin 3 →₀ ℕ) :
    MvPowerSeries.coeff m (f - X s * divX s f) =
      if m s = 0 then MvPowerSeries.coeff m f else 0 := by
  simp only [map_sub]
  rw [show (X s : MvPowerSeries (Fin 3) ℂ) =
    MvPowerSeries.monomial (R := ℂ) (Finsupp.single s 1) 1
    from rfl]
  rw [MvPowerSeries.coeff_monomial_mul]
  split_ifs with hle hms
  · exfalso
    have := hle s
    simp [Finsupp.single_eq_same] at this
    omega
  · simp only [one_mul]
    simp only [sub_eq_zero]
    change f m = f (m - Finsupp.single s 1 + Finsupp.single s 1)
    rw [tsub_add_cancel_of_le hle]
  · simp
  · exfalso
    apply hle
    intro i
    simp only [Finsupp.single_apply]
    split_ifs with heq
    · subst heq
      omega
    · exact Nat.zero_le _

open MvPowerSeries in
/-- ker phiToPS = PPre. -/
theorem ker_phiToPS_eq : RingHom.ker phiToPS = PPre := by
  apply le_antisymm
  · intro f hf
    rw [RingHom.mem_ker] at hf
    have hcoeff : ∀ n, MvPowerSeries.coeff (Finsupp.single 2 n) f = 0 := by
      intro n
      have h1 : PowerSeries.coeff n (phiToPS f) = 0 := by
        rw [hf, map_zero]
      simp only [phiToPS, PowerSeries.coeff_mk, RingHom.coe_mk, MonoidHom.coe_mk,
        OneHom.coe_mk] at h1
      exact h1
    -- Decompose f = X₀ * g₀ + X₁ * g₁ via successive division
    set g₀ := divX 0 f with hg₀_def
    set f' := f - X 0 * g₀ with hf'_def
    set g₁ := divX 1 f' with hg₁_def
    set f'' := f' - X 1 * g₁ with hf''_def
    have hf''_zero : f'' = 0 := by
      ext m
      rw [map_zero]
      rw [hf''_def, coeff_sub_X_mul_divX]
      split_ifs with h1
      · rw [hf'_def, coeff_sub_X_mul_divX]
        split_ifs with h0
        · have hm_eq : m = Finsupp.single 2 (m 2) := by
            ext i
            fin_cases i <;> simp [*]
          rw [hm_eq]
          exact hcoeff (m 2)
        · rfl
      · rfl
    have hdecomp : f = X 0 * g₀ + X 1 * g₁ := by
      have hf'eq : f' = X 1 * g₁ := by
        rw [hf''_def] at hf''_zero
        exact sub_eq_zero.mp hf''_zero
      have hfeq : f = X 0 * g₀ + f' := by rw [hf'_def]
                                          abel
      rw [hf'eq] at hfeq
      exact hfeq
    rw [hdecomp]
    apply Ideal.add_mem
    · exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert _ _))
    · exact Ideal.mul_mem_right _ _ (Ideal.subset_span
        (Set.mem_insert_iff.mpr (Or.inr rfl)))
  · rw [PPre, Ideal.span_le]
    intro f hf
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf
    rw [SetLike.mem_coe, RingHom.mem_ker]
    ext n
    change PowerSeries.coeff n (phiToPS f) = PowerSeries.coeff n 0
    simp only [map_zero, phiToPS, PowerSeries.coeff_mk, RingHom.coe_mk, MonoidHom.coe_mk,
      OneHom.coe_mk]
    cases hf with
    | inl h =>
      subst h
      simp only [MvPowerSeries.coeff_X]
      split_ifs with heq
      · exfalso
        have := DFunLike.congr_fun heq (0 : Fin 3)
        simp at this
      · rfl
    | inr h =>
      subst h
      simp only [MvPowerSeries.coeff_X]
      split_ifs with heq
      · exfalso
        have := DFunLike.congr_fun heq (1 : Fin 3)
        simp at this
      · rfl

open MvPowerSeries in
/-- PPre is prime because ker phiToPS = PPre and PowerSeries ℂ is a domain. -/
instance PPre_isPrime : PPre.IsPrime := by
  rw [← ker_phiToPS_eq]
  exact RingHom.ker_isPrime phiToPS

open MvPowerSeries in
/-- Q = Ideal.map (mk conjI) PPre. -/
theorem Q_eq_map_PPre :
    Q = Ideal.map (Ideal.Quotient.mk conjI) PPre := by
  simp only [Q, PPre, Ideal.map_span, Set.image_insert_eq, Set.image_singleton]

theorem Q_isPrime : Q.IsPrime := by
  rw [Q_eq_map_PPre]
  exact Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
    (by
       rw [Ideal.mk_ker]
       exact conjI_le_PPre)

theorem Q_height_one : Q.height = 1 := by
  open MvPowerSeries in
  -- Q is minimal over (mk(X₁)) by Krull's principal ideal theorem
  set y : T := Ideal.Quotient.mk conjI (X (1 : Fin 3)) with hy_def
  have hy_mem : y ∈ Q := Ideal.subset_span (Set.mem_insert_iff.mpr (Or.inr rfl))
  have hle : Q.height ≤ 1 := by
    apply Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {y})
    refine ⟨⟨Q_isPrime, Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hy_mem)⟩, ?_⟩
    intro q ⟨hq, hq_le⟩ hq_sub
    have hy_q : y ∈ q := hq_le (Ideal.subset_span rfl)
    have hrel : (Ideal.Quotient.mk conjI (X (0 : Fin 3))) ^ 2 =
        y * Ideal.Quotient.mk conjI (X 2) := by
      rw [← map_pow, ← map_mul, Ideal.Quotient.eq]
      exact Ideal.subset_span rfl
    have hx_q : Ideal.Quotient.mk conjI (X (0 : Fin 3)) ∈ q :=
      hq.mem_of_pow_mem 2 (hrel ▸ Ideal.mul_mem_right _ _ hy_q)
    change Q ≤ q
    rw [show Q = Ideal.span {Ideal.Quotient.mk conjI (X (0 : Fin 3)),
        Ideal.Quotient.mk conjI (X (1 : Fin 3))} from rfl]
    exact Ideal.span_le.mpr (fun a ha => by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl <;> assumption)
  have hne : Q.height ≠ 0 := by
    haveI := Q_isPrime
    rw [ne_eq, Ideal.height_eq_zero_iff,
      IsDomain.minimalPrimes_eq_singleton_bot, Set.mem_singleton_iff]
    intro hQ_bot
    have hx_mem : Ideal.Quotient.mk conjI (X (0 : Fin 3)) ∈ Q :=
      Ideal.subset_span (Set.mem_insert _ _)
    rw [hQ_bot, Ideal.mem_bot] at hx_mem
    have hker := conjI_le_ker_ψ (Ideal.Quotient.eq_zero_iff_mem.mp hx_mem)
    rw [RingHom.mem_ker] at hker
    have hψ : ψHom.toRingHom (X (0 : Fin 3) : MvPowerSeries (Fin 3) ℂ) =
        (X (0 : Fin 2) : MvPowerSeries (Fin 2) ℂ) * X 1 := by
      change ψHom (X 0) = X 0 * X 1
      rw [ψHom, MvPowerSeries.substAlgHom_X]
      rfl
    rw [hψ] at hker
    have hX0_zero := (mem_nonZeroDivisors_iff.mp
      (X_mem_nonzeroDivisors (i := (1 : Fin 2)))).2 _ hker
    have := congr_arg (MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1)) hX0_zero
    simp [MvPowerSeries.coeff_X] at this
  refine le_antisymm hle ?_
  by_contra hlt
  push Not at hlt
  apply hne
  rcases h : Q.height with _ | n
  · exact absurd hle (by
      rw [h]
      exact not_le.mpr (by
        exact_mod_cast (show 1 < (⊤ : ℕ∞) from WithTop.coe_lt_top 1)))
  · have hlt' : n < 1 := by
      have h1 := hlt
      rw [h] at h1
      exact WithTop.coe_lt_coe.mp h1
    have hn : n = 0 := by omega
    subst hn
    rfl

lemma ψBar_mk (f : MvPowerSeries (Fin 3) ℂ) :
    ψBar (Ideal.Quotient.mk conjI f) = ψHom f :=
  Ideal.Quotient.lift_mk conjI ψHom.toRingHom _

open MvPowerSeries in
lemma ψBar_mk_X0 :
    ψBar (Ideal.Quotient.mk conjI (X 0)) =
      (X (0 : Fin 2)) * (X 1 : MvPowerSeries (Fin 2) ℂ) := by
  rw [ψBar_mk, ψHom, MvPowerSeries.substAlgHom_X]
  rfl

open MvPowerSeries in
lemma ψBar_mk_X1 :
    ψBar (Ideal.Quotient.mk conjI (X 1)) =
      ((X (0 : Fin 2)) : MvPowerSeries (Fin 2) ℂ) ^ 2 := by
  rw [ψBar_mk, ψHom, MvPowerSeries.substAlgHom_X]
  rfl

open MvPowerSeries in
/-- Substitution data `Xᵢ ↦ -Xᵢ` on `ℂ[[u,v]]`, used to detect odd-parity
vanishing of coefficients (recall `ψMap` sends `X₀ ↦ X₀X₁`, `X₁ ↦ X₀²`,
`X₂ ↦ X₁²`, so the total degree of any monomial in the image is even). -/
noncomputable def negSubstMap : Fin 2 → MvPowerSeries (Fin 2) ℂ :=
  fun i => -(X i)

lemma negSubst_hasSubst : MvPowerSeries.HasSubst negSubstMap := by
  apply MvPowerSeries.hasSubst_of_constantCoeff_zero
  intro s
  simp [negSubstMap, MvPowerSeries.constantCoeff_X]

/-- The algebra hom on `ℂ[[u,v]]` induced by the substitution `Xᵢ ↦ -Xᵢ`. -/
noncomputable def negSubst :
    MvPowerSeries (Fin 2) ℂ →ₐ[ℂ] MvPowerSeries (Fin 2) ℂ :=
  MvPowerSeries.substAlgHom negSubst_hasSubst

open MvPowerSeries in
lemma negSubst_X (i : Fin 2) : negSubst (X i) = -(X i) := by
  change MvPowerSeries.substAlgHom negSubst_hasSubst (X i) = -(X i)
  rw [MvPowerSeries.substAlgHom_X]
  rfl

open MvPowerSeries in
lemma negSubst_ψMap (i : Fin 3) : negSubst (ψMap i) = ψMap i := by
  fin_cases i
  · change negSubst (X 0 * X 1) = X 0 * X 1
    rw [map_mul, negSubst_X, negSubst_X, neg_mul_neg]
  · change negSubst ((X 0) ^ 2) = (X 0) ^ 2
    rw [map_pow, negSubst_X, neg_sq]
  · change negSubst ((X 1) ^ 2) = (X 1) ^ 2
    rw [map_pow, negSubst_X, neg_sq]

open MvPowerSeries in
lemma negSubst_comp_ψHom (f : MvPowerSeries (Fin 3) ℂ) :
    negSubst (ψHom f) = ψHom f := by
  have h1 : negSubst (ψHom f) =
      MvPowerSeries.subst (fun s => MvPowerSeries.subst negSubstMap (ψMap s)) f := by
    rw [show ψHom f = MvPowerSeries.subst ψMap f from by
      rw [ψHom, MvPowerSeries.coe_substAlgHom]]
    rw [show (negSubst : MvPowerSeries (Fin 2) ℂ → _) = MvPowerSeries.subst negSubstMap from by
      rw [show (negSubst : MvPowerSeries (Fin 2) ℂ →ₐ[ℂ] _) =
        MvPowerSeries.substAlgHom negSubst_hasSubst from rfl, MvPowerSeries.coe_substAlgHom]]
    rw [MvPowerSeries.subst_comp_subst_apply ψ_hasSubst negSubst_hasSubst]
  rw [h1]
  have heq : (fun s => MvPowerSeries.subst negSubstMap (ψMap s)) = ψMap := by
    funext s
    have : MvPowerSeries.subst negSubstMap (ψMap s) = negSubst (ψMap s) := by
      change _ = MvPowerSeries.substAlgHom negSubst_hasSubst (ψMap s)
      rw [MvPowerSeries.coe_substAlgHom]
    rw [this, negSubst_ψMap]
  rw [heq, show MvPowerSeries.subst ψMap f = ψHom f from by
    rw [ψHom, MvPowerSeries.coe_substAlgHom]]

open MvPowerSeries in
lemma negSubstMap_eq (s : Fin 2) :
    negSubstMap s = ((-1 : ℂ) • MvPowerSeries.X s : MvPowerSeries (Fin 2) ℂ) := by
  simp [negSubstMap]

lemma Finsupp.sum_fin2
    (m : Fin 2 →₀ ℕ) (f : Fin 2 → ℕ → ℕ) (hf : ∀ i, f i 0 = 0) :
    m.sum f = f 0 (m 0) + f 1 (m 1) := by
  rw [Finsupp.sum]
  refine Finset.sum_subset_zero_on_sdiff (Finset.subset_univ _) (fun i hi => by
    simp only [Finsupp.mem_support_iff, ne_eq, not_not, Finset.mem_sdiff, Finset.mem_univ,
      true_and] at hi
    rw [hi]
    exact hf i) (fun _ _ => rfl)
  |>.trans ?_
  simp [Finset.univ_fin2]

open MvPowerSeries in
lemma coeff_negSubst (g : MvPowerSeries (Fin 2) ℂ) (m : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff m (negSubst g) = (-1) ^ (m 0 + m 1) * MvPowerSeries.coeff m g := by
  have hns : negSubst g = MvPowerSeries.subst negSubstMap g := by
    rw [negSubst, MvPowerSeries.coe_substAlgHom]
  rw [hns, MvPowerSeries.coeff_subst negSubst_hasSubst]
  have hprod : ∀ d : Fin 2 →₀ ℕ, d.prod (fun s n => (negSubstMap s) ^ n) =
      MvPowerSeries.monomial d ((-1 : ℂ) ^ (d.sum fun _ n => n)) := by
    intro d
    rw [Finsupp.prod_congr (g2 := fun s n => ((-1 : ℂ) • MvPowerSeries.X s) ^ n)
      (fun s _ => by rw [negSubstMap_eq])]
    exact (MvPowerSeries.monomial_smul_const d (-1)).symm
  simp_rw [hprod, MvPowerSeries.coeff_monomial, smul_eq_mul]
  rw [finsum_eq_single _ m]
  · simp only [ite_true]
    have hsum : m.sum (fun (_ : Fin 2) (n : ℕ) => n) = m 0 + m 1 := by
      rw [Finsupp.sum]
      exact Finset.sum_subset (Finset.subset_univ _)
        (fun i _ hi => by
           simp only [Finsupp.mem_support_iff, ne_eq, not_not] at hi
           exact hi)
        |>.trans (by simp [Finset.univ_fin2])
    rw [hsum]
    ring
  · intro d hd
    simp only [if_neg (Ne.symm hd), mul_zero]

open MvPowerSeries in
lemma ψHom_coeff_odd_parity (f : MvPowerSeries (Fin 3) ℂ)
    (m : Fin 2 →₀ ℕ) (hm : Odd (m 0 + m 1)) :
    MvPowerSeries.coeff m (ψHom f) = 0 := by
  have h := negSubst_comp_ψHom f
  have h1 := congr_arg (MvPowerSeries.coeff m) h
  rw [coeff_negSubst] at h1
  obtain ⟨k, hk⟩ := hm
  rw [hk, pow_succ, pow_mul, neg_one_sq, one_pow, one_mul, neg_one_mul] at h1
  have h2 : (2 : ℂ) • MvPowerSeries.coeff m (ψHom f) = 0 := by
    rw [two_smul]
    exact neg_eq_iff_add_eq_zero.mp h1
  rw [smul_eq_mul] at h2
  exact (mul_eq_zero.mp h2).resolve_left two_ne_zero

open MvPowerSeries in
lemma Q_le_maximalIdeal : Q ≤ IsLocalRing.maximalIdeal T :=
  IsLocalRing.le_maximalIdeal Q_isPrime.ne_top

theorem Q_not_isPrincipal : ¬ Q.IsPrincipal := by
  intro ⟨⟨a, ha⟩⟩
  have hx_mem : Ideal.Quotient.mk conjI (MvPowerSeries.X 0) ∈ Q :=
    Ideal.subset_span (Set.mem_insert _ _)
  have hy_mem : Ideal.Quotient.mk conjI (MvPowerSeries.X 1) ∈ Q :=
    Ideal.subset_span (Set.mem_insert_iff.mpr (Or.inr rfl))
  rw [ha] at hx_mem hy_mem
  rw [Submodule.mem_span_singleton] at hx_mem hy_mem
  obtain ⟨r, hr⟩ := hx_mem
  obtain ⟨s, hs⟩ := hy_mem
  simp only [smul_eq_mul] at hr hs
  have hψr : (MvPowerSeries.X (0 : Fin 2)) * MvPowerSeries.X 1 = ψBar r * ψBar a := by
    rw [← ψBar_mk_X0, ← hr, map_mul]
  have hψs : ((MvPowerSeries.X (0 : Fin 2)) : MvPowerSeries (Fin 2) ℂ) ^ 2
      = ψBar s * ψBar a := by
    rw [← ψBar_mk_X1, ← hs, map_mul]
  -- Cross-multiply and cancel X₀
  have hcross : MvPowerSeries.X 0 * (ψBar r) =
      (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) ℂ) * (ψBar s) := by
    have hX0_ne : (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) ℂ) ≠ 0 := by
      intro h
      have := congr_arg (MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1)) h
      simp [MvPowerSeries.coeff_X] at this
    have h1 : (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) ℂ) ^ 2 * ψBar r =
        MvPowerSeries.X 0 * MvPowerSeries.X 1 * ψBar s := by
      calc _ = ψBar s * ψBar a * ψBar r := by rw [hψs]
        _ = ψBar r * ψBar a * ψBar s := by ring
        _ = _ := by rw [hψr]
    rw [sq, mul_assoc, mul_assoc] at h1
    exact mul_left_cancel₀ hX0_ne h1
  have hconst_r : MvPowerSeries.constantCoeff (ψBar r) = 0 := by
    have h1 := congr_arg (MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1)) hcross
    change MvPowerSeries.coeff _ (MvPowerSeries.monomial (Finsupp.single (0 : Fin 2) 1) 1 * _) =
      MvPowerSeries.coeff _ (MvPowerSeries.monomial (Finsupp.single (1 : Fin 2) 1) 1 * _) at h1
    rw [MvPowerSeries.coeff_monomial_mul, MvPowerSeries.coeff_monomial_mul] at h1
    have hle : Finsupp.single (0 : Fin 2) 1 ≤ Finsupp.single (0 : Fin 2) 1 := le_refl _
    have hnle : ¬ Finsupp.single (1 : Fin 2) 1 ≤ Finsupp.single (0 : Fin 2) 1 := by
      intro h
      have := h 1
      simp at this
    simp only [hle, ite_true, hnle, ite_false, tsub_self, one_mul] at h1
    exact h1
  have hconst_s : MvPowerSeries.constantCoeff (ψBar s) = 0 := by
    have h1 := congr_arg (MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) 1)) hcross
    change MvPowerSeries.coeff _ (MvPowerSeries.monomial (Finsupp.single (0 : Fin 2) 1) 1 * _) =
      MvPowerSeries.coeff _ (MvPowerSeries.monomial (Finsupp.single (1 : Fin 2) 1) 1 * _) at h1
    rw [MvPowerSeries.coeff_monomial_mul, MvPowerSeries.coeff_monomial_mul] at h1
    have hle : Finsupp.single (1 : Fin 2) 1 ≤ Finsupp.single (1 : Fin 2) 1 := le_refl _
    have hnle : ¬ Finsupp.single (0 : Fin 2) 1 ≤ Finsupp.single (1 : Fin 2) 1 := by
      intro h
      have := h 0
      simp at this
    simp only [hle, ite_true, hnle, ite_false, tsub_self, one_mul] at h1
    exact h1.symm
  have ha_mem_Q : a ∈ Q := ha ▸ Submodule.mem_span_singleton_self a
  have ha_mem_M : a ∈ IsLocalRing.maximalIdeal T := Q_le_maximalIdeal ha_mem_Q
  have hconst_a : MvPowerSeries.constantCoeff (ψBar a) = 0 := by
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [ψBar_mk]
    by_contra h
    have hf : MvPowerSeries.constantCoeff f ≠ 0 := by
      intro hf0
      apply h
      have : ψHom f = MvPowerSeries.subst ψMap f := by
        rw [ψHom, MvPowerSeries.coe_substAlgHom]
      rw [this]
      exact MvPowerSeries.constantCoeff_subst_eq_zero ψ_hasSubst
        (fun s => by fin_cases s <;> simp [ψMap, MvPowerSeries.constantCoeff_X]) hf0
    have hf_unit : IsUnit f := by
      rw [MvPowerSeries.isUnit_iff_constantCoeff]
      exact Ne.isUnit hf
    have hmk_unit : IsUnit (Ideal.Quotient.mk conjI f) := hf_unit.map _
    have hnonunit := (IsLocalRing.mem_maximalIdeal _).mp ha_mem_M
    exact (mem_nonunits_iff.mp hnonunit) hmk_unit
  have hparity_a : MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1) (ψBar a) = 0 := by
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [ψBar_mk]
    exact ψHom_coeff_odd_parity f _ ⟨0, by simp⟩
  -- Contradiction at coeff(single 0 2): LHS = 1, RHS = 0
  have hcoeff_X0sq : MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 2)
      ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ) ^ 2) = 1 := by
    rw [MvPowerSeries.coeff_X_pow]
    simp
  have hcoeff_prod : MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 2)
      (ψBar s * ψBar a) = 0 := by
    rw [MvPowerSeries.coeff_mul]
    apply Finset.sum_eq_zero
    intro ⟨u, v⟩ huv
    rw [Finset.mem_antidiagonal] at huv
    have hu1 : u 1 = 0 := by
      have := DFunLike.congr_fun huv 1
      simp [Finsupp.add_apply] at this
      omega
    have hv1 : v 1 = 0 := by
      have := DFunLike.congr_fun huv 1
      simp [Finsupp.add_apply] at this
      omega
    have hu0v0 : u 0 + v 0 = 2 := by
      have := DFunLike.congr_fun huv 0
      simp only [Finsupp.add_apply, Finsupp.single_eq_same] at this
      exact this
    have hu_eq : u = Finsupp.single 0 (u 0) := by
      ext i
      fin_cases i <;> simp [*]
    have hv_eq : v = Finsupp.single 0 (v 0) := by
      ext i
      fin_cases i <;> simp [*]
    have hu0_le : u 0 ≤ 2 := by omega
    interval_cases (u 0)
    · rw [hu_eq, Finsupp.single_zero (0 : Fin 2),
        MvPowerSeries.coeff_zero_eq_constantCoeff, hconst_s, zero_mul]
    · have hv0 : v 0 = 1 := by omega
      rw [hv_eq, hv0, hparity_a, mul_zero]
    · have hv0 : v 0 = 0 := by omega
      rw [hv_eq, hv0, Finsupp.single_zero (0 : Fin 2),
        MvPowerSeries.coeff_zero_eq_constantCoeff, hconst_a, mul_zero]
  have : (1 : ℂ) = 0 := by
    rw [← hcoeff_X0sq, hψs, hcoeff_prod]
  exact one_ne_zero this

open MvPowerSeries in
lemma mk_X2_not_mem_Q :
    (Ideal.Quotient.mk conjI (X (2 : Fin 3)) : T) ∉ Q := by
  rw [Q_eq_map_PPre]
  intro hmem
  rw [Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at hmem
  obtain ⟨f, hf_mem, hf_eq⟩ := hmem
  have hfX2 : f - X 2 ∈ conjI := Ideal.Quotient.eq.mp hf_eq
  have hX2_P : X (2 : Fin 3) ∈ PPre := by
    have h := PPre.sub_mem hf_mem (conjI_le_PPre hfX2)
    rwa [show f - (f - X 2) = X 2 from by ring] at h
  rw [← ker_phiToPS_eq, RingHom.mem_ker] at hX2_P
  have : phiToPS (X 2) ≠ 0 := by
    intro h
    have h1 := congr_arg (PowerSeries.coeff 1) h
    simp only [map_zero] at h1
    change (phiToPS (X 2)).coeff 1 = 0 at h1
    simp only [phiToPS, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
      PowerSeries.coeff_mk] at h1
    rw [MvPowerSeries.coeff_X] at h1
    simp at h1
  exact this hX2_P

/-- T has Krull dimension 2. -/
theorem T_ringKrullDim : ringKrullDim T = 2 := by
  apply le_antisymm
  · haveI : IsNoetherianRing (MvPowerSeries (Fin 3) ℂ) := mvPowerSeries_fin3_isNoetherianRing
    have hdim_eq : ringKrullDim T + 1 = ringKrullDim (MvPowerSeries (Fin 3) ℂ) :=
      ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
        gen_mem_nonZeroDivisors gen_mem_maximalIdeal
    have hdim_mvps : ringKrullDim (MvPowerSeries (Fin 3) ℂ) ≤ 3 := mvPS_ringKrullDim_le
    have h3 : ringKrullDim T + 1 ≤ 3 := hdim_eq ▸ hdim_mvps
    cases hT : ringKrullDim T with
    | bot => exact bot_le
    | coe a =>
      rw [hT] at h3
      rw [show (↑a : WithBot ℕ∞) + 1 = ↑(a + 1) by
            push_cast
            rfl,
          show (3 : WithBot ℕ∞) = ↑(3 : ℕ∞) from rfl, WithBot.coe_le_coe] at h3
      rw [show (2 : WithBot ℕ∞) = ↑(2 : ℕ∞) from rfl, WithBot.coe_le_coe]
      cases a using ENat.recTopCoe with
      | top => exact absurd h3 (by norm_num)
      | coe n =>
        rw [show (↑n : ℕ∞) + 1 = ↑(n + 1) by
              push_cast
              ring,
            show (3 : ℕ∞) = ↑(3 : ℕ) from rfl, ENat.coe_le_coe] at h3
        rw [show (2 : ℕ∞) = ↑(2 : ℕ) from rfl, ENat.coe_le_coe]
        omega
  · -- Lower bound: chain ⊥ < Q < ⊤ gives length 2
    have hbot_lt_Q : (⊥ : PrimeSpectrum T) < ⟨Q, Q_isPrime⟩ := by
      rw [bot_lt_iff_ne_bot]
      intro h
      have hQ_bot : Q = ⊥ := by
        have := congr_arg PrimeSpectrum.asIdeal h
        simpa using this
      have := Q_height_one
      rw [hQ_bot, Ideal.height_bot] at this
      norm_num at this
    have hQ_lt_top : (⟨Q, Q_isPrime⟩ : PrimeSpectrum T) < ⊤ := by
      simp only [lt_top_iff_ne_top, ne_eq, PrimeSpectrum.ext_iff]
      intro h
      have hQ_max : Q = IsLocalRing.maximalIdeal T := by simpa using h
      have hmem : (Ideal.Quotient.mk conjI (MvPowerSeries.X (2 : Fin 3)) : T) ∈
          IsLocalRing.maximalIdeal T := by
        simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        intro ⟨u, hu⟩
        have := unit_of_mk_unit_T (MvPowerSeries.X (2 : Fin 3)) ⟨u, hu⟩
        simp [MvPowerSeries.constantCoeff_X] at this
      rw [← hQ_max] at hmem
      exact mk_X2_not_mem_Q hmem
    rw [show (2 : WithBot ℕ∞) = (2 : ℕ) from rfl, ringKrullDim]
    rw [Order.le_krullDim_iff]
    exact ⟨⟨2, ![⊥, ⟨Q, Q_isPrime⟩, ⊤], fun i => by
      fin_cases i <;> simpa⟩, rfl⟩


end
