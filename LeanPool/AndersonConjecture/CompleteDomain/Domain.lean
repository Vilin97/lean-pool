/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FrenzyMath
-/
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.MvPowerSeries.Substitution

/-!
# The Complete Local Domain T

Construction of T = C[[x,y,z]]/(x^2 - yz) and the proof that
T is an integral domain.
-/

noncomputable section

open MvPowerSeries in
/-- The ideal (x² - yz) in ℂ[[x,y,z]] where x = X 0, y = X 1, z = X 2. -/
def conjI : Ideal (MvPowerSeries (Fin 3) ℂ) :=
  Ideal.span {(X 0) ^ 2 - (X 1) * (X 2)}

/-- T = ℂ[[x,y,z]]/(x²-yz), the main complete local domain. -/
abbrev T := MvPowerSeries (Fin 3) ℂ ⧸ conjI

open MvPowerSeries in
theorem conjI_ne_top : conjI ≠ ⊤ := by
  apply Ideal.span_singleton_ne_top
  rw [MvPowerSeries.isUnit_iff_constantCoeff]
  change ¬IsUnit (MvPowerSeries.constantCoeff (σ := Fin 3) (R := ℂ)
      ((X 0) ^ 2 - (X 1) * (X 2)))
  simp only [map_sub, map_pow, map_mul, MvPowerSeries.constantCoeff_X]
  norm_num

section T_isDomain_proof

open MvPowerSeries

/-- The substitution map ψ : ℂ[[x,y,z]] → ℂ[[u,v]] defined by
  x ↦ u·v, y ↦ u², z ↦ v². -/
noncomputable def ψMap : Fin 3 → MvPowerSeries (Fin 2) ℂ :=
  fun i => match i with
  | 0 => X 0 * X 1
  | 1 => (X 0) ^ 2
  | 2 => (X 1) ^ 2

lemma ψ_hasSubst : HasSubst (a := ψMap) := by
  apply hasSubst_of_constantCoeff_zero
  intro s
  fin_cases s <;> simp [ψMap, constantCoeff_X]

/-- The algebra hom `ℂ[[x,y,z]] → ℂ[[u,v]]` induced by the substitution
`ψMap` (`x ↦ uv`, `y ↦ u²`, `z ↦ v²`). -/
noncomputable def ψHom :
    MvPowerSeries (Fin 3) ℂ →ₐ[ℂ] MvPowerSeries (Fin 2) ℂ :=
  MvPowerSeries.substAlgHom ψ_hasSubst

lemma ψ_kills_gen : ψHom ((X 0) ^ 2 - (X 1) * (X 2)) = 0 := by
  simp only [map_sub, map_pow, map_mul, ψHom, MvPowerSeries.substAlgHom_X]
  simp [ψMap]
  ring

lemma conjI_le_ker_ψ : conjI ≤ RingHom.ker ψHom.toRingHom := by
  rw [show conjI = Ideal.span {(X (0 : Fin 3) : MvPowerSeries (Fin 3) ℂ) ^ 2 -
    X 1 * X 2} from rfl, Ideal.span_le]
  intro x hx
  simp only [Set.mem_singleton_iff] at hx
  subst hx
  exact RingHom.mem_ker.mpr ψ_kills_gen

lemma anderson_gen_ne_zero : (X (0 : Fin 3) : MvPowerSeries (Fin 3) ℂ) ^ 2 -
    X 1 * X 2 ≠ 0 := by
  intro h
  have h1 := congr_arg (MvPowerSeries.coeff (R := ℂ) (Finsupp.single (0 : Fin 3) 2)) h
  simp only [map_sub, map_zero] at h1
  rw [MvPowerSeries.coeff_X_pow] at h1
  simp only [ite_true] at h1
  rw [MvPowerSeries.coeff_mul] at h1
  simp only [MvPowerSeries.coeff_X] at h1
  have : ∀ p ∈ Finset.antidiagonal (Finsupp.single (0 : Fin 3) 2),
    (if p.1 = Finsupp.single 1 1 then (1 : ℂ) else 0) *
    (if p.2 = Finsupp.single 2 1 then 1 else 0) = 0 := by
    intro ⟨a, b⟩ hab
    rw [Finset.mem_antidiagonal] at hab
    by_cases ha : a = Finsupp.single 1 1
    · simp only [ha, ite_true]
      by_cases hb : b = Finsupp.single 2 1
      · exfalso
        have h0 := congr_fun (congr_arg DFunLike.coe hab) (0 : Fin 3)
        simp [ha, hb, Finsupp.add_apply] at h0
      · simp [hb]
    · simp [ha]
  rw [Finset.sum_eq_zero this] at h1
  norm_num at h1

/-- The factored map ψbar : T → ℂ[[u,v]]. -/
noncomputable def ψBar : T →+* MvPowerSeries (Fin 2) ℂ :=
  Ideal.Quotient.lift conjI ψHom.toRingHom (fun x hx =>
    (conjI_le_ker_ψ hx : x ∈ RingHom.ker ψHom.toRingHom))

/-- Construct a `Fin 3 →₀ ℕ` from three natural numbers. -/
def mkFin3 (a b c : ℕ) : Fin 3 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm ![a, b, c]

@[simp] private lemma mkFin3_zero : mkFin3 a b c 0 = a := rfl
@[simp] private lemma mkFin3_one : mkFin3 a b c 1 = b := rfl
@[simp] private lemma mkFin3_two : mkFin3 a b c 2 = c := rfl

lemma mkFin3_ext (n : Fin 3 →₀ ℕ) : n = mkFin3 (n 0) (n 1) (n 2) := by
  ext i
  fin_cases i <;> rfl

/-- Construct a `Fin 2 →₀ ℕ` from two natural numbers. -/
def mkFin2 (a b : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm ![a, b]

/-- Explicit quotient: given f, define q so that f = q * (X₀² - X₁X₂) when ψ(f)=0.
  q(n₀,n₁,n₂) = Σ_{k=0}^{min(n₁,n₂)} f(n₀+2+2k, n₁-k, n₂-k). -/
def divQ (f : MvPowerSeries (Fin 3) ℂ) : MvPowerSeries (Fin 3) ℂ :=
  fun n => ∑ k ∈ Finset.range (min (n 1) (n 2) + 1),
    f (mkFin3 (n 0 + 2 + 2 * k) (n 1 - k) (n 2 - k))

/-- Key coefficient relation: the sum Σ_{k=0}^{min(m₁,m₂)} f(m₀+2k, m₁-k, m₂-k)
  equals a coefficient of ψHom(f) at the monomial u^{m₀+2m₁} v^{m₀+2m₂}. -/
lemma ψMap_prod_eq (d : Fin 3 →₀ ℕ) :
    d.prod (fun s n => ψMap s ^ n) =
    MvPowerSeries.monomial (mkFin2 (d 0 + 2 * d 1) (d 0 + 2 * d 2)) (1 : ℂ) := by
  have hprod : d.prod (fun s n => ψMap s ^ n) =
      (ψMap 0 ^ (d 0)) * (ψMap 1 ^ (d 1)) * (ψMap 2 ^ (d 2)) := by
    rw [Finsupp.prod]
    rw [Finset.prod_subset (Finset.subset_univ _) (fun i _ hi => by
      simp only [Finsupp.mem_support_iff, ne_eq, not_not] at hi
      rw [hi]
      simp)]
    have huniv : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
    rw [huniv]
    rw [Finset.prod_insert (show (0 : Fin 3) ∉ ({1, 2} : Finset (Fin 3)) by decide)]
    rw [Finset.prod_insert (show (1 : Fin 3) ∉ ({2} : Finset (Fin 3)) by decide)]
    rw [Finset.prod_singleton]
    ring
  rw [hprod]
  change ((MvPowerSeries.X 0 * MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ) ^ d 0 *
    ((MvPowerSeries.X 0) ^ 2) ^ d 1 *
    ((MvPowerSeries.X 1) ^ 2) ^ d 2) = _
  -- Use X_pow_eq to convert X^n to monomial form
  rw [show ((MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ) ^ d 0 *
    ((MvPowerSeries.X (0 : Fin 2)) ^ 2) ^ d 1 *
    ((MvPowerSeries.X (1 : Fin 2)) ^ 2) ^ d 2) =
    (MvPowerSeries.X (0 : Fin 2)) ^ (d 0 + 2 * d 1) *
    (MvPowerSeries.X (1 : Fin 2)) ^ (d 0 + 2 * d 2) from by ring]
  rw [MvPowerSeries.X_pow_eq, MvPowerSeries.X_pow_eq, MvPowerSeries.monomial_mul_monomial, one_mul]
  have : Finsupp.single (0 : Fin 2) (d 0 + 2 * d 1) + Finsupp.single 1 (d 0 + 2 * d 2) =
      mkFin2 (d 0 + 2 * d 1) (d 0 + 2 * d 2) := by
    apply Finsupp.ext
    intro i
    simp only [Finsupp.add_apply, Finsupp.single_apply]
    fin_cases i <;> simp [mkFin2]
  rw [this]

lemma mkFin2_inj {a b c d : ℕ} : mkFin2 a b = mkFin2 c d ↔ a = c ∧ b = d := by
  constructor
  · intro h
    exact ⟨congr_fun (congr_arg DFunLike.coe h) 0, congr_fun (congr_arg DFunLike.coe h) 1⟩
  · rintro ⟨rfl, rfl⟩
    rfl

lemma mkFin3_inj {a b c d e f : ℕ} :
    mkFin3 a b c = mkFin3 d e f ↔ a = d ∧ b = e ∧ c = f := by
  constructor
  · intro h
    exact ⟨congr_fun (congr_arg DFunLike.coe h) 0,
           congr_fun (congr_arg DFunLike.coe h) 1,
           congr_fun (congr_arg DFunLike.coe h) 2⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

-- Fiber characterization: preimages under ψ are {mkFin3(m₀+2k)(m₁-k)(m₂-k) : k ≤ min(m₁,m₂)}
lemma ψ_fiber_char (m₀ m₁ m₂ : ℕ) (hm₀ : m₀ ≤ 1) (d : Fin 3 →₀ ℕ) :
    mkFin2 (d 0 + 2 * d 1) (d 0 + 2 * d 2) = mkFin2 (m₀ + 2 * m₁) (m₀ + 2 * m₂) ↔
    ∃ k ≤ min m₁ m₂, d = mkFin3 (m₀ + 2 * k) (m₁ - k) (m₂ - k) := by
  rw [mkFin2_inj]
  constructor
  · rintro ⟨h1, h2⟩
    -- Parity of d 0 matches m₀ (since m₀ ≤ 1), so d 1 ≤ m₁ and d 2 ≤ m₂
    have hd1_le : d 1 ≤ m₁ := by omega
    have hd2_le : d 2 ≤ m₂ := by omega
    set k := m₁ - d 1 with hk_def
    refine ⟨k, ?_, ?_⟩
    · simp
      omega
    · rw [mkFin3_ext d, mkFin3_inj]
      omega
  · rintro ⟨k, hk, rfl⟩
    simp only [mkFin3_zero, mkFin3_one, mkFin3_two]
    constructor <;> omega

lemma ψHom_coeff_sum
    (f : MvPowerSeries (Fin 3) ℂ) (m₀ m₁ m₂ : ℕ) (hm₀ : m₀ ≤ 1) :
    ∑ k ∈ Finset.range (min m₁ m₂ + 1),
      f (mkFin3 (m₀ + 2 * k) (m₁ - k) (m₂ - k)) =
    MvPowerSeries.coeff (mkFin2 (m₀ + 2 * m₁) (m₀ + 2 * m₂)) (ψHom f) := by
  set e := mkFin2 (m₀ + 2 * m₁) (m₀ + 2 * m₂) with he_def
  -- Step 1: rewrite ψHom as subst and expand
  rw [show ψHom f = MvPowerSeries.subst ψMap f from by
    rw [ψHom, MvPowerSeries.coe_substAlgHom]]
  rw [MvPowerSeries.coeff_subst ψ_hasSubst]
  simp_rw [ψMap_prod_eq, MvPowerSeries.coeff_monomial, smul_eq_mul, mul_ite, mul_one, mul_zero]
  set g : (Fin 3 →₀ ℕ) → ℂ := fun d =>
    if e = mkFin2 (d 0 + 2 * d 1) (d 0 + 2 * d 2)
    then MvPowerSeries.coeff d f else 0
  set S := (Finset.range (min m₁ m₂ + 1)).image
    (fun k => mkFin3 (m₀ + 2 * k) (m₁ - k) (m₂ - k))
  suffices hgoal : ∑ k ∈ Finset.range (min m₁ m₂ + 1),
      f (mkFin3 (m₀ + 2 * k) (m₁ - k) (m₂ - k)) = ∑ᶠ d, g d by
    convert hgoal using 1
  -- Show support of g is contained in S
  have hsupp : Function.support g ⊆ ↑S := by
    intro d hd
    rw [Function.mem_support] at hd
    simp only [g] at hd
    split_ifs at hd with hcond
    · rw [he_def, eq_comm, ψ_fiber_char _ _ _ hm₀] at hcond
      obtain ⟨k, hk, rfl⟩ := hcond
      exact Finset.mem_coe.mpr (Finset.mem_image.mpr
        ⟨k, Finset.mem_range.mpr (Nat.lt_succ_of_le hk), rfl⟩)
    · exact absurd rfl hd
  rw [finsum_eq_sum_of_support_subset g hsupp]
  rw [show S = (Finset.range (min m₁ m₂ + 1)).image
    (fun k => mkFin3 (m₀ + 2 * k) (m₁ - k) (m₂ - k)) from rfl]
  rw [Finset.sum_image (fun k1 _ k2 _ heq => by
                          rw [mkFin3_inj] at heq
                          omega)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  have hk' : k ≤ min m₁ m₂ := Nat.lt_succ_iff.mp hk
  simp only [g]
  have hcond : e = mkFin2 (mkFin3 (m₀ + 2 * k) (m₁ - k) (m₂ - k) 0 + 2 *
      mkFin3 (m₀ + 2 * k) (m₁ - k) (m₂ - k) 1)
    (mkFin3 (m₀ + 2 * k) (m₁ - k) (m₂ - k) 0 + 2 *
      mkFin3 (m₀ + 2 * k) (m₁ - k) (m₂ - k) 2) := by
    simp only [mkFin3_zero, mkFin3_one, mkFin3_two, he_def, mkFin2_inj]
    constructor <;> omega
  rw [if_pos hcond]
  rfl

/-- Key lemma: ψbar is injective. This is equivalent to ker ψHom = conjI.

**Proof sketch:** View ℂ[[x,y,z]] ≅ ℂ[[y,z]][[x]] via the ring equiv.
Under this decomposition, every f can be written uniquely as q·(x²-yz) + (a + bx).
If ψ(f) = 0 then ψ(a + bx) = a(u²,v²) + b(u²,v²)·uv = 0.
The terms a(u²,v²) use only even-even degree monomials while b(u²,v²)·uv uses
only odd-odd degree monomials, so both must be zero. Since g ↦ g(u²,v²) is
injective, a = b = 0, hence f = q·(x²-yz) ∈ conjI. -/
lemma ψBar_injective : Function.Injective ψBar := by
  apply RingHom.lift_injective_of_ker_le_ideal
  intro f hf
  rw [RingHom.mem_ker] at hf
  rw [conjI, Ideal.mem_span_singleton]
  -- Need: (X 0 ^ 2 - X 1 * X 2) ∣ f
  refine ⟨divQ f, ?_⟩
  have hψ0 : ψHom f = 0 := hf
  -- Write gen = X₀² - X₁X₂ as difference of monomials
  set d₀ := Finsupp.single (0 : Fin 3) 2
  set d₁₂ := Finsupp.single (1 : Fin 3) 1 + Finsupp.single (2 : Fin 3) 1
  have hgen_eq : (MvPowerSeries.X (0 : Fin 3) : MvPowerSeries (Fin 3) ℂ) ^ 2 -
      MvPowerSeries.X 1 * MvPowerSeries.X 2 =
      MvPowerSeries.monomial d₀ (1 : ℂ) - MvPowerSeries.monomial d₁₂ 1 := by
    congr 1
    · exact MvPowerSeries.X_pow_eq 0 2
    · rw [show (MvPowerSeries.X (1 : Fin 3) : MvPowerSeries (Fin 3) ℂ) =
          MvPowerSeries.monomial (Finsupp.single 1 1) 1 from by
        rw [← MvPowerSeries.X_pow_eq (1 : Fin 3) 1]
        simp,
        show (MvPowerSeries.X (2 : Fin 3) : MvPowerSeries (Fin 3) ℂ) =
          MvPowerSeries.monomial (Finsupp.single 2 1) 1 from by
        rw [← MvPowerSeries.X_pow_eq (2 : Fin 3) 1]
        simp,
        MvPowerSeries.monomial_mul_monomial, one_mul]
  ext m
  rw [hgen_eq, sub_mul]
  simp only [map_sub, MvPowerSeries.coeff_monomial_mul, one_mul]
  have hd₀_iff : d₀ ≤ m ↔ 2 ≤ m 0 := by
    simp only [d₀, Finsupp.le_iff, Finsupp.support_single _ (by omega : (2 : ℕ) ≠ 0),
      Finset.mem_singleton, forall_eq, Finsupp.single_eq_same]
  have hd₁₂_iff : d₁₂ ≤ m ↔ 1 ≤ m 1 ∧ 1 ≤ m 2 := by
    constructor
    · intro h
      have h1 : d₁₂ 1 = 1 := by simp [d₁₂, Finsupp.add_apply]
      have h2 : d₁₂ 2 = 1 := by simp [d₁₂, Finsupp.add_apply]
      exact ⟨h1 ▸ h 1, h2 ▸ h 2⟩
    · intro ⟨h1, h2⟩ i
      show d₁₂ i ≤ m i
      simp only [d₁₂, Finsupp.add_apply]
      fin_cases i <;> simp <;> omega
  -- Case on m 0 ≥ 2
  by_cases hm0 : 2 ≤ m 0
  · -- m 0 ≥ 2: telescoping
    rw [if_pos (hd₀_iff.mpr hm0)]
    have sub0 : (m - d₀) 0 = m 0 - 2 := by simp [Finsupp.tsub_apply, d₀]
    have sub1 : (m - d₀) 1 = m 1 := by simp [Finsupp.tsub_apply, d₀]
    have sub2 : (m - d₀) 2 = m 2 := by simp [Finsupp.tsub_apply, d₀]
    have hdivQ0 : MvPowerSeries.coeff (m - d₀) (divQ f) =
        ∑ k ∈ Finset.range (min (m 1) (m 2) + 1),
        f (mkFin3 (m 0 + 2 * k) (m 1 - k) (m 2 - k)) := by
      change divQ f (m - d₀) = _
      simp only [divQ, sub0, sub1, sub2, show m 0 - 2 + 2 = m 0 from by omega]
    rw [hdivQ0]
    by_cases hm12 : 1 ≤ m 1 ∧ 1 ≤ m 2
    · rw [if_pos (hd₁₂_iff.mpr hm12)]
      have s0' : (m - d₁₂) 0 = m 0 := by simp [Finsupp.tsub_apply, d₁₂, Finsupp.add_apply]
      have s1' : (m - d₁₂) 1 = m 1 - 1 := by simp [Finsupp.tsub_apply, d₁₂, Finsupp.add_apply]
      have s2' : (m - d₁₂) 2 = m 2 - 1 := by simp [Finsupp.tsub_apply, d₁₂, Finsupp.add_apply]
      have hdivQ12 : MvPowerSeries.coeff (m - d₁₂) (divQ f) =
          ∑ k ∈ Finset.range (min (m 1 - 1) (m 2 - 1) + 1),
          f (mkFin3 (m 0 + 2 + 2 * k) (m 1 - 1 - k) (m 2 - 1 - k)) := by
        change divQ f (m - d₁₂) = _
        simp only [divQ, s0', s1', s2']
      rw [hdivQ12, show min (m 1 - 1) (m 2 - 1) = min (m 1) (m 2) - 1 from by omega]
      -- Telescoping: peel off k=0 from first sum, remaining terms cancel
      conv_lhs => rw [show (MvPowerSeries.coeff m) f = f m from rfl]
      conv_lhs => rw [mkFin3_ext m]
      set N := min (m 1) (m 2)
      have hN : 1 ≤ N := by omega
      rw [show N - 1 + 1 = N from by omega]
      rw [show N + 1 = N.succ from rfl, Finset.sum_range_succ']
      simp only [mul_zero, add_zero, Nat.sub_zero]
      have hterms : ∀ k ∈ Finset.range N,
          f (mkFin3 (m 0 + 2 * (k + 1)) (m 1 - (k + 1)) (m 2 - (k + 1))) =
          f (mkFin3 (m 0 + 2 + 2 * k) (m 1 - 1 - k) (m 2 - 1 - k)) := by
        intro k _
        congr 1
        rw [mkFin3_inj]
        refine ⟨by ring, ?_, ?_⟩ <;> omega
      rw [Finset.sum_congr rfl hterms]
      ring
    · push Not at hm12
      rw [if_neg (fun h => by
                    rw [hd₁₂_iff] at h
                    exact absurd h.2 (not_le.mpr (hm12 h.1)))]
      simp only [sub_zero]
      have hmin0 : min (m 1) (m 2) = 0 := by
        by_cases h : 1 ≤ m 1
        · have := hm12 h
          omega
        · omega
      rw [hmin0, show (0 : ℕ) + 1 = 1 from rfl]
      simp only [Finset.sum_range_one, mul_zero, add_zero, Nat.sub_zero]
      change f m = f (mkFin3 (m 0) (m 1) (m 2))
      rw [← mkFin3_ext]
  · -- m 0 < 2 (m 0 ≤ 1)
    have hm0' : m 0 ≤ 1 := by omega
    rw [if_neg (fun h => by
                  rw [hd₀_iff] at h
                  omega)]
    simp only [zero_sub]
    have hψ_sum : ∑ k ∈ Finset.range (min (m 1) (m 2) + 1),
        f (mkFin3 (m 0 + 2 * k) (m 1 - k) (m 2 - k)) = 0 := by
      rw [ψHom_coeff_sum f (m 0) (m 1) (m 2) hm0', hψ0, map_zero]
    by_cases hm12 : 1 ≤ m 1 ∧ 1 ≤ m 2
    · rw [if_pos (hd₁₂_iff.mpr hm12)]
      change f m = -(divQ f (m - d₁₂))
      simp only [divQ]
      have s0 : (m - d₁₂) 0 = m 0 := by simp [Finsupp.tsub_apply, d₁₂, Finsupp.add_apply]
      have s1 : (m - d₁₂) 1 = m 1 - 1 := by simp [Finsupp.tsub_apply, d₁₂, Finsupp.add_apply]
      have s2 : (m - d₁₂) 2 = m 2 - 1 := by simp [Finsupp.tsub_apply, d₁₂, Finsupp.add_apply]
      rw [s0, s1, s2]
      rw [show min (m 1 - 1) (m 2 - 1) + 1 = min (m 1) (m 2) from by omega]
      -- From hψ_sum, peel off first term
      rw [Finset.sum_range_succ'] at hψ_sum
      simp only [mul_zero, add_zero, Nat.sub_zero] at hψ_sum
      suffices ∀ k ∈ Finset.range (min (m 1) (m 2)),
          f (mkFin3 (m 0 + 2 * (k + 1)) (m 1 - (k + 1)) (m 2 - (k + 1))) =
          f (mkFin3 (m 0 + 2 + 2 * k) (m 1 - 1 - k) (m 2 - 1 - k)) by
        rw [Finset.sum_congr rfl this] at hψ_sum
        exact (congr_arg f (mkFin3_ext m)).trans (eq_neg_of_add_eq_zero_right hψ_sum)
      intro k _
      congr 1
      rw [mkFin3_inj]
      refine ⟨by ring, ?_, ?_⟩ <;> omega
    · push Not at hm12
      rw [if_neg (fun h => by
                    rw [hd₁₂_iff] at h
                    exact absurd h.2 (not_le.mpr (hm12 h.1)))]
      simp only [neg_zero]
      have : min (m 1) (m 2) = 0 := by
        by_cases h : 1 ≤ m 1
        · have := hm12 h
          omega
        · omega
      rw [this, show (0 : ℕ) + 1 = 1 from rfl] at hψ_sum
      simp only [Finset.sum_range_one, mul_zero, add_zero, Nat.sub_zero] at hψ_sum
      change f m = 0
      exact (congr_arg f (mkFin3_ext m)).trans hψ_sum

end T_isDomain_proof

instance T_isDomain : IsDomain T :=
  letI : Nontrivial T := Ideal.Quotient.nontrivial_iff.mpr conjI_ne_top
  letI : NoZeroDivisors T := ⟨fun {a b} hab => by
    have hinj := ψBar_injective
    have h1 : ψBar (a * b) = 0 := by rw [hab, map_zero]
    rw [map_mul] at h1
    rcases eq_zero_or_eq_zero_of_mul_eq_zero h1 with h | h
    · left
      exact hinj (by rw [h, map_zero])
    · right
      exact hinj (by rw [h, map_zero])⟩
  NoZeroDivisors.to_isDomain T


end
