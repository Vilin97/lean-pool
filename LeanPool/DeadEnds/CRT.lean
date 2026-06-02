/-
Copyright (c) 2026 Evan Chen, Kenny Lau, Seewoo Lee, Ken Ono, Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Chen, Kenny Lau, Seewoo Lee, Ken Ono, Jujian Zhang
-/

import LeanPool.DeadEnds.Basic

/-!
# LeanPool.DeadEnds.CRT
-/

namespace LeanPool.DeadEnds

/-- The modulus M = ∏_{p ∈ S} p² -/
noncomputable def primeSquareProduct (S : Finset Nat.Primes) : ℕ :=
  ∏ p ∈ S, (p : ℕ) ^ 2

/-- Valid residues mod M: residues r such that for all p ∈ S, r mod p² is valid -/
noncomputable def validResiduesMod (b : ℕ) (T : Finset ℕ) (S : Finset Nat.Primes) : Finset ℕ :=
  (Finset.range (primeSquareProduct S)).filter fun r =>
    ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ r) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ (b * r + d))

/-- The product of local density factors L = ∏_{p ∈ S} localDensityFactor p b T -/
noncomputable def localDensityProduct (b : ℕ) (T : Finset ℕ) (S : Finset Nat.Primes) : ℝ :=
  ∏ p ∈ S, localDensityFactor (p : ℕ) b T

/-- The local valid residues for a single prime p: residues r in [0, p²) such that
    p² ∤ r and for all d ∈ T, p² ∤ (b * r + d). -/
def localValidResidues (p : ℕ) (b : ℕ) (T : Finset ℕ) : Finset ℕ :=
  (Finset.range (p ^ 2)).filter fun r =>
    ¬(p ^ 2 ∣ r) ∧ ∀ d ∈ T, ¬(p ^ 2 ∣ (b * r + d))

lemma localValidResidues_card_eq (p : ℕ) (hp : Nat.Prime p) (b : ℕ) (T : Finset ℕ) :
    ((localValidResidues p b T).card : ℝ) = (p : ℝ) ^ 2 * localDensityFactor p b T := by
  have h1 : ((localValidResidues p b T).card : ℝ) = ((localValidResidues p b T).card : ℝ) := rfl
  have h2 : localDensityFactor p b T = ( ( (Finset.filter (fun r => ¬(p ^ 2 ∣ r) ∧ ∀ d ∈ T,
      ¬(p ^ 2 ∣ (b * r + d))) (Finset.range (p ^ 2))).card : ℝ) / ( (p ^ 2 : ℕ) : ℝ)) := by
    dsimp [localDensityFactor]
  have h3 : ((localValidResidues p b T).card : ℝ) = ( ( (Finset.filter (fun r => ¬(p ^ 2 ∣ r) ∧
      ∀ d ∈ T, ¬(p ^ 2 ∣ (b * r + d))) (Finset.range (p ^ 2))).card : ℝ)) := by
    dsimp [localValidResidues]
  have h4 : ( ( (Finset.filter (fun r => ¬(p ^ 2 ∣ r) ∧ ∀ d ∈ T, ¬(p ^ 2 ∣ (b * r + d))) (
      Finset.range (p ^ 2))).card : ℝ)) = (p : ℝ) ^ 2 * localDensityFactor p b T := by
    have h5 : localDensityFactor p b T = ( ( (Finset.filter (fun r => ¬(p ^ 2 ∣ r) ∧ ∀ d ∈ T,
        ¬(p ^ 2 ∣ (b * r + d))) (Finset.range (p ^ 2))).card : ℝ) / ( (p ^ 2 : ℕ) : ℝ)) := by
      rw [h2]
    have h6 : (p : ℝ) ≠ 0 := by
      norm_cast
      exact Nat.Prime.ne_zero hp
    have h7 : (p : ℝ) ^ 2 ≠ 0 := by
      positivity
    have h8 : ((p : ℝ) ^ 2 : ℝ) = (p ^ 2 : ℕ) := by
      norm_cast
    rw [h5]
    have h9 : (( (Finset.filter (fun r => ¬(p ^ 2 ∣ r) ∧ ∀ d ∈ T, ¬(p ^ 2 ∣ (b * r + d))) (
        Finset.range (p ^ 2))).card : ℝ)) = (( (Finset.filter (fun r => ¬(p ^ 2 ∣ r) ∧ ∀ d ∈ T,
            ¬(p ^ 2 ∣ (b * r + d))) (Finset.range (p ^ 2))).card : ℝ)) := rfl
    have h10 : ((p : ℝ) ^ 2 : ℝ) ≠ 0 := by positivity
    field_simp [h7, h10]; ring_nf; field_simp [h7, h10]; norm_cast
  calc
    ((localValidResidues p b T).card : ℝ) = ( ( (Finset.filter (fun r => ¬(p ^ 2 ∣ r) ∧ ∀ d ∈ T,
        ¬(p ^ 2 ∣ (b * r + d))) (Finset.range (p ^ 2))).card : ℝ)) := by rw [h3]
    _ = (p : ℝ) ^ 2 * localDensityFactor p b T := by rw [h4]

lemma prime_sq_coprime (p q : Nat.Primes) (hne : p ≠ q) :
    ((p : ℕ) ^ 2).Coprime ((q : ℕ) ^ 2) := by
  have hpq : (p : ℕ) ≠ (q : ℕ) := fun h => hne (Subtype.ext h)
  exact Nat.Coprime.pow_right 2
    (Nat.Coprime.pow_left 2 ((Nat.coprime_primes p.prop q.prop).mpr hpq))

lemma pairwise_coprime_prime_squares (S : Finset Nat.Primes) :
    (S : Set Nat.Primes).Pairwise (fun p q => ((p : ℕ) ^ 2).Coprime ((q : ℕ) ^ 2)) := by
  intro p _ q _ hpq
  exact prime_sq_coprime p q hpq

/-- The list S.toList satisfies pairwise coprimality for the map p ↦ p².
    Uses `pairwise_coprime_prime_squares` and transfers the set pairwise property to the list.
    Mathlib's `List.pairwise_of_reflexive_of_forall_ne` handles this for symmetric reflexive
    relations,
    but coprimality is not reflexive (unless p² = 1). Instead we use the fact that S.toList.Nodup
    and the set pairwise property directly imply the list pairwise property.
    Specifically, uses `List.Nodup.pairwise_of_set_pairwise : l.Nodup → {x | x ∈ l}.Pairwise r →
    List.Pairwise r l`
    together with `Finset.nodup_toList : ∀ (s : Finset α), s.toList.Nodup` and
    `Finset.coe_toList : ↑s.toList = ↑s` (as sets). -/
lemma toList_pairwise_coprime_prime_squares (S : Finset Nat.Primes) :
    List.Pairwise (Function.onFun Nat.Coprime (fun p : Nat.Primes => (p : ℕ) ^ 2)) S.toList := by
  apply List.Nodup.pairwise_of_set_pairwise (Finset.nodup_toList S)
  simp only [Finset.mem_toList]
  exact pairwise_coprime_prime_squares S

lemma list_map_prod_eq_primeSquareProduct (S : Finset Nat.Primes) :
    (List.map (fun p : Nat.Primes => (p : ℕ) ^ 2) S.toList).prod = primeSquareProduct S := by
  aesop

/-- Congruence modulo each prime-square factor implies congruence modulo their product. -/
lemma modEq_primeSquareProduct_of_forall_modEq (S : Finset Nat.Primes) (r₁ r₂ : ℕ)
    (h : ∀ p ∈ S, r₁ ≡ r₂ [MOD (p : ℕ) ^ 2]) :
    r₁ ≡ r₂ [MOD primeSquareProduct S] := by
  rw [← list_map_prod_eq_primeSquareProduct]
  rw [Nat.modEq_list_map_prod_iff (toList_pairwise_coprime_prime_squares S)]
  intro p hp
  exact h p (Finset.mem_toList.mp hp)

/-- The CRT remainder map is injective on residues below the product modulus. -/
lemma crtMap_injective_on_range (S : Finset Nat.Primes) :
    Set.InjOn (fun r => fun p (_hp : p ∈ S) => r % ((p : ℕ) ^ 2))
      {r | r < primeSquareProduct S} := by
  intro r₁ hr₁ r₂ hr₂ heq
  have h_modEq : ∀ p ∈ S, r₁ ≡ r₂ [MOD (p : ℕ) ^ 2] := by
    intro p hp
    have h : r₁ % (p : ℕ) ^ 2 = r₂ % (p : ℕ) ^ 2 := congrFun (congrFun heq p) hp
    exact h
  have h_modEq_M : r₁ ≡ r₂ [MOD primeSquareProduct S] :=
    modEq_primeSquareProduct_of_forall_modEq S r₁ r₂ h_modEq
  exact Nat.ModEq.eq_of_lt_of_lt h_modEq_M hr₁ hr₂

lemma dvd_iff_mod_dvd (p : ℕ) (_hp : 0 < p ^ 2) (r : ℕ) :
    p ^ 2 ∣ r ↔ r % (p ^ 2) = 0 := by
  have h_main : p ^ 2 ∣ r ↔ r % (p ^ 2) = 0 := Nat.dvd_iff_mod_eq_zero
  aesop

lemma shifted_dvd_iff_mod (p b d r : ℕ) (_hp : 0 < p ^ 2) :
    p ^ 2 ∣ (b * r + d) ↔ p ^ 2 ∣ (b * (r % (p ^ 2)) + d) := by
  rw [Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero]
  simp [Nat.add_mod, Nat.mul_mod]

lemma valid_iff_locally_valid (b : ℕ) (T : Finset ℕ) (S : Finset Nat.Primes) (r : ℕ) :
    (∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ r) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ (b * r + d))) ↔
    (∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ (r % (p : ℕ) ^ 2)) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ (b * (r % (p : ℕ) ^ 2) +
        d))) := by
  constructor
  · intro h p hp
    have hp_pos : 0 < (p : ℕ) ^ 2 := pow_pos (Nat.Prime.pos p.2) 2
    constructor
    · intro hmod
      have hzero : r % (p : ℕ) ^ 2 = 0 :=
        Nat.eq_zero_of_dvd_of_lt hmod (Nat.mod_lt r hp_pos)
      exact (h p hp).1 ((dvd_iff_mod_dvd (p : ℕ) hp_pos r).mpr hzero)
    · intro d hd hmod
      exact (h p hp).2 d hd ((shifted_dvd_iff_mod (p : ℕ) b d r hp_pos).mpr hmod)
  · intro h p hp
    have hp_pos : 0 < (p : ℕ) ^ 2 := pow_pos (Nat.Prime.pos p.2) 2
    constructor
    · intro hr
      have hzero := (dvd_iff_mod_dvd (p : ℕ) hp_pos r).mp hr
      have hmod : (p : ℕ) ^ 2 ∣ r % (p : ℕ) ^ 2 := by
        rw [hzero]
        simp
      exact (h p hp).1 hmod
    · intro d hd hr
      exact (h p hp).2 d hd ((shifted_dvd_iff_mod (p : ℕ) b d r hp_pos).mp hr)

/-- For any prime p, p² ≠ 0.
    This is needed to apply `Nat.chineseRemainderOfFinset`.
    Uses `Nat.Prime.pos : ∀ {p : ℕ}, Nat.Prime p → 0 < p` and
    `pow_ne_zero : ∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] {a : M₀} [NoZeroDivisors M₀] (n :
    ℕ), a ≠ 0 → a ^ n ≠ 0`. -/
lemma prime_sq_ne_zero (p : Nat.Primes) : (p : ℕ) ^ 2 ≠ 0 := by
  have hp : Nat.Prime p := p.2
  exact pow_ne_zero 2 hp.pos.ne'

lemma crt_surjective (S : Finset Nat.Primes) (t : (p : Nat.Primes) → p ∈ S → ℕ)
    (ht : ∀ p (hp : p ∈ S), t p hp < (p : ℕ) ^ 2) :
    ∃ r, r < primeSquareProduct S ∧ ∀ p (hp : p ∈ S), r % ((p : ℕ) ^ 2) = t p hp := by
  let s : Nat.Primes → ℕ := fun p => (p : ℕ) ^ 2
  let a : Nat.Primes → ℕ := fun p => if h : p ∈ S then t p h else 0
  have hs : ∀ i ∈ S, s i ≠ 0 := fun p _ => prime_sq_ne_zero p
  have hcoprime : (S : Set Nat.Primes).Pairwise (Function.onFun Nat.Coprime s) :=
    pairwise_coprime_prime_squares S
  let r := Nat.chineseRemainderOfFinset a s S hs hcoprime
  use r
  constructor
  · exact Nat.chineseRemainderOfFinset_lt_prod a s hs hcoprime
  · intro p hp
    have hcong : (r : ℕ) ≡ a p [MOD s p] := r.2 p hp
    have ha : a p = t p hp := by simp [a, hp]
    rw [ha] at hcong
    exact Nat.mod_eq_of_modEq hcong (ht p hp)

lemma crtMap_mapsTo_pi (b : ℕ) (T : Finset ℕ) (S : Finset Nat.Primes) (r : ℕ)
    (hr : r ∈ validResiduesMod b T S) (p : Nat.Primes) (hp : p ∈ S) :
    r % ((p : ℕ) ^ 2) ∈ localValidResidues (p : ℕ) b T := by
  simp only [validResiduesMod, Finset.mem_filter, Finset.mem_range] at hr
  obtain ⟨_, hvalid⟩ := hr
  have hp_cond := hvalid p hp
  have hp_sq_pos : 0 < (p : ℕ) ^ 2 := sq_pos_of_pos p.prop.pos
  have hmod_lt : r % ((p : ℕ) ^ 2) < (p : ℕ) ^ 2 := Nat.mod_lt r hp_sq_pos
  simp only [localValidResidues, Finset.mem_filter, Finset.mem_range]
  refine ⟨hmod_lt, ?_, ?_⟩
  · intro hdvd
    have h_rmod_eq_zero : r % ((p : ℕ) ^ 2) = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hmod_lt
    have hdvd_r : (p : ℕ) ^ 2 ∣ r := Nat.dvd_of_mod_eq_zero h_rmod_eq_zero
    exact hp_cond.1 hdvd_r
  · intro d hd hdvd_shifted
    have h_not_dvd := hp_cond.2 d hd
    have hmod : (r % ((p : ℕ) ^ 2)) ≡ r [MOD ((p : ℕ) ^ 2)] := Nat.mod_modEq r ((p : ℕ) ^ 2)
    have hmul : b * (r % ((p : ℕ) ^ 2)) ≡ b * r [MOD ((p : ℕ) ^ 2)] := hmod.mul_left b
    have hadd : b * (r % ((p : ℕ) ^ 2)) + d ≡ b * r + d [MOD ((p : ℕ) ^ 2)] := hmul.add_right d
    have hdvd_equiv : ((p : ℕ) ^ 2 ∣ b * (r % ((p : ℕ) ^ 2)) + d) ↔ ((p : ℕ) ^ 2 ∣ b * r + d) :=
      hadd.dvd_iff dvd_rfl
    exact h_not_dvd (hdvd_equiv.mp hdvd_shifted)

lemma not_dvd_of_mod_eq_not_dvd (p r f : ℕ) (_hp : 0 < p ^ 2) (hr_eq : r % p ^ 2 = f)
    (hf_ndiv : ¬(p ^ 2 ∣ f)) : ¬(p ^ 2 ∣ r) := by
  intro h_dvd_r
  have h_mod_eq : r % p ^ 2 = 0 := by
    have h₁ : p ^ 2 ∣ r := h_dvd_r
    have h₂ : r % p ^ 2 = 0 := by
      have h₃ := Nat.mod_eq_zero_of_dvd h₁
      exact h₃
    exact h₂
  have h_f_eq_zero : f = 0 := by
    linarith
  have h_p_sq_dvd_f : p ^ 2 ∣ f := by
    have h₁ : f = 0 := h_f_eq_zero
    rw [h₁]
    exact by
      exact ⟨0, by simp⟩
  exact hf_ndiv h_p_sq_dvd_f

lemma not_dvd_shift_of_mod_eq (p b r f d : ℕ) (_hp : 0 < p ^ 2) (hr_eq : r % p ^ 2 = f)
    (hf_shift : ¬(p ^ 2 ∣ b * f + d)) : ¬(p ^ 2 ∣ b * r + d) := by
  intro h
  have h₁ : p ^ 2 ∣ b * r + d := h
  have h₂ : (b * r + d) % (p ^ 2) = 0 := by
    exact Nat.mod_eq_zero_of_dvd h₁
  have h₃ : (b * r + d) % (p ^ 2) = (b * f + d) % (p ^ 2) := by
    have h₄ : r % p ^ 2 = f := hr_eq
    have h₅ : b * r % (p ^ 2) = b * f % (p ^ 2) := by
      have h₆ : b * r % (p ^ 2) = (b * (r % p ^ 2)) % (p ^ 2) := by
        simp [Nat.mul_mod]
      rw [h₆]
      have h₇ : (b * (r % p ^ 2)) % (p ^ 2) = (b * f) % (p ^ 2) := by
        rw [h₄]
      rw [h₇]
    have h₈ : (b * r + d) % (p ^ 2) = (b * f + d) % (p ^ 2) := by
      have h₉ : (b * r + d) % (p ^ 2) = ((b * r) % (p ^ 2) + d % (p ^ 2)) % (p ^ 2) := by
        simp [Nat.add_mod]
      rw [h₉]
      have h₁₀ : (b * f + d) % (p ^ 2) = ((b * f) % (p ^ 2) + d % (p ^ 2)) % (p ^ 2) := by
        simp [Nat.add_mod]
      rw [h₁₀]
      have h₁₁ : (b * r) % (p ^ 2) = (b * f) % (p ^ 2) := by
        exact h₅
      rw [h₁₁]
    exact h₈
  have h₄ : (b * f + d) % (p ^ 2) = 0 := by
    rw [h₃] at h₂
    exact h₂
  have h₅ : p ^ 2 ∣ b * f + d := by
    have h₆ : (b * f + d) % (p ^ 2) = 0 := h₄
    exact Nat.dvd_of_mod_eq_zero h₆
  exact hf_shift h₅

lemma crt_inverse_mapsTo (b : ℕ) (T : Finset ℕ) (S : Finset Nat.Primes)
    (f : (p : Nat.Primes) → p ∈ S → ℕ)
    (hf : ∀ p (hp : p ∈ S), f p hp ∈ localValidResidues (p : ℕ) b T) :
    ∃ r ∈ validResiduesMod b T S, ∀ p (hp : p ∈ S), r % ((p : ℕ) ^ 2) = f p hp := by
  have hf_bound : ∀ p (hp : p ∈ S), f p hp < (p : ℕ) ^ 2 := fun p hp => by
    have h := hf p hp
    simp only [localValidResidues, Finset.mem_filter, Finset.mem_range] at h
    exact h.1
  obtain ⟨r, hr_lt, hr_mod⟩ := crt_surjective S f hf_bound
  refine ⟨r, ?_, hr_mod⟩
  simp only [validResiduesMod, Finset.mem_filter, Finset.mem_range]
  constructor
  · exact hr_lt
  · intro p hp
    have hf_valid := hf p hp
    simp only [localValidResidues, Finset.mem_filter, Finset.mem_range] at hf_valid
    obtain ⟨_, hf_ndiv, hf_shift⟩ := hf_valid
    have hr_eq : r % ((p : ℕ) ^ 2) = f p hp := hr_mod p hp
    have hp_pos : 0 < (p : ℕ) ^ 2 := pow_pos (Nat.Prime.pos p.2) 2
    constructor
    · exact not_dvd_of_mod_eq_not_dvd (p : ℕ) r (f p hp) hp_pos hr_eq hf_ndiv
    · intro d hd
      exact not_dvd_shift_of_mod_eq (p : ℕ) b r (f p hp) d hp_pos hr_eq (hf_shift d hd)

lemma validResidues_equiv_pi (b : ℕ) (T : Finset ℕ) (S : Finset Nat.Primes) :
    Nonempty ((validResiduesMod b T S) ≃ (S.pi (fun p => localValidResidues (p : ℕ) b T))) := by
  have hfwd : ∀ r, r ∈ validResiduesMod b T S →
      (fun p (hp : p ∈ S) => r % ((p : ℕ) ^ 2)) ∈ S.pi (fun p => localValidResidues (p : ℕ) b T) :=
          by
    intro r hr
    rw [Finset.mem_pi]
    intro p hp
    exact crtMap_mapsTo_pi b T S r hr p hp
  let f : (validResiduesMod b T S) → (S.pi (fun p => localValidResidues (p : ℕ) b T)) :=
    fun ⟨r, hr⟩ => ⟨fun p hp => r % ((p : ℕ) ^ 2), hfwd r hr⟩
  have hf_inj : Function.Injective f := by
    intro ⟨r₁, hr₁⟩ ⟨r₂, hr₂⟩ heq
    simp only [Subtype.mk.injEq]
    have hr₁_lt : r₁ < primeSquareProduct S :=
      Finset.mem_filter.mp hr₁ |>.1 |> Finset.mem_range.mp
    have hr₂_lt : r₂ < primeSquareProduct S :=
      Finset.mem_filter.mp hr₂ |>.1 |> Finset.mem_range.mp
    apply crtMap_injective_on_range S hr₁_lt hr₂_lt
    have heq' := Subtype.mk.injEq _ _ _ _ |>.mp heq
    ext p hp
    have := congrFun₂ heq' p hp
    exact this
  have hf_surj : Function.Surjective f := by
    intro ⟨g, hg⟩
    have hg' : ∀ p (hp : p ∈ S), g p hp ∈ localValidResidues (p : ℕ) b T := by
      intro p hp
      rw [Finset.mem_pi] at hg
      exact hg p hp
    obtain ⟨r, hr, hr_eq⟩ := crt_inverse_mapsTo b T S g hg'
    use ⟨r, hr⟩
    apply Subtype.ext
    ext p hp
    exact hr_eq p hp
  exact ⟨Equiv.ofBijective f ⟨hf_inj, hf_surj⟩⟩

lemma validResiduesMod_card_eq_pi_card (b : ℕ) (T : Finset ℕ) (S : Finset Nat.Primes) :
    (validResiduesMod b T S).card =
      (S.pi (fun p => localValidResidues (p : ℕ) b T)).card := by
  exact Finset.card_eq_of_equiv (validResidues_equiv_pi b T S).some

/-- Valid residue counts factor as the product of local valid residue counts. -/
lemma validResiduesMod_card_eq_prod (b : ℕ) (T : Finset ℕ) (S : Finset Nat.Primes) :
    ((validResiduesMod b T S).card : ℝ) =
      ∏ p ∈ S, ((localValidResidues (p : ℕ) b T).card : ℝ) := by
  rw [validResiduesMod_card_eq_pi_card]
  rw [Finset.card_pi]
  simp only [Nat.cast_prod]

lemma validResidues_card_eq_mul (b : ℕ) (_hb : 2 ≤ b) (T : Finset ℕ) (_hT : T ⊆ Finset.range b)
    (S : Finset Nat.Primes) :
    ((validResiduesMod b T S).card : ℝ) =
      (primeSquareProduct S : ℝ) * localDensityProduct b T S := by
  rw [validResiduesMod_card_eq_prod]
  conv_lhs =>
    arg 2
    ext p
    rw [localValidResidues_card_eq p p.prop b T]
  rw [Finset.prod_mul_distrib]
  simp only [primeSquareProduct, localDensityProduct, Nat.cast_prod, Nat.cast_pow]

/-- A finite product of local density factors is at most one. -/
lemma localDensityProduct_le_one (b : ℕ) (T : Finset ℕ) (S : Finset Nat.Primes) :
    localDensityProduct b T S ≤ 1 := by
  unfold localDensityProduct
  apply Finset.prod_le_one
  · intro p _
    exact localDensityFactor_nonneg p b T
  · intro p _
    exact localDensityFactor_le_one p b T

lemma prime_sq_dvd_primeSquareProduct (S : Finset Nat.Primes) (p : Nat.Primes) (hp : p ∈ S) :
    (p : ℕ) ^ 2 ∣ primeSquareProduct S := by
  have h₁ : (p : ℕ) ^ 2 ∣ ∏ q ∈ S, (q : ℕ) ^ 2 := by
    apply Finset.dvd_prod_of_mem; simp_all
  simpa [primeSquareProduct] using h₁

lemma dvd_iff_of_mod_eq_primeSquareProduct (S : Finset Nat.Primes) (p : Nat.Primes) (hp : p ∈ S)
    (N₁ N₂ : ℕ) (hmod : N₁ % primeSquareProduct S = N₂ % primeSquareProduct S) :
    ((p : ℕ) ^ 2 ∣ N₁ ↔ (p : ℕ) ^ 2 ∣ N₂) := by
  have h₁ : (p : ℕ) ^ 2 ∣ primeSquareProduct S := by
    have h₂ : (p : ℕ) ^ 2 ∣ ∏ q ∈ S, (q : ℕ) ^ 2 := by
      have h₃ : p ∈ S := hp
      have h₅ : (p : ℕ) ^ 2 ∣ ∏ q ∈ S, (q : ℕ) ^ 2 := by
        apply Finset.dvd_prod_of_mem; simpa using h₃
      exact h₅
    simpa [primeSquareProduct] using h₂
  have h₂ : N₁ % primeSquareProduct S = N₂ % primeSquareProduct S := hmod
  have h₃ : N₁ ≡ N₂ [MOD primeSquareProduct S] := by
    rw [Nat.ModEq]; simp_all
  have h₄ : ((p : ℕ) ^ 2 ∣ N₁ ↔ (p : ℕ) ^ 2 ∣ N₂) := by
    have h₇ : ((p : ℕ) ^ 2 ∣ N₁ ↔ (p : ℕ) ^ 2 ∣ N₂) := by
      have h₉ : ((p : ℕ) ^ 2 ∣ N₁ ↔ (p : ℕ) ^ 2 ∣ N₂) := by
        have h₁₀ : N₁ ≡ N₂ [MOD primeSquareProduct S] := h₃
        have h₁₁ : (p : ℕ) ^ 2 ∣ primeSquareProduct S := h₁
        have h₁₂ : ((p : ℕ) ^ 2 ∣ N₁ ↔ (p : ℕ) ^ 2 ∣ N₂) := by
          apply Nat.ModEq.dvd_iff h₁₀; exact h₁₁
        exact h₁₂
      exact h₉
    exact h₇
  exact h₄

lemma shifted_dvd_iff_of_mod_eq_primeSquareProduct (b d : ℕ) (S : Finset Nat.Primes)
    (p : Nat.Primes) (hp : p ∈ S) (N₁ N₂ : ℕ)
    (hmod : N₁ % primeSquareProduct S = N₂ % primeSquareProduct S) :
    ((p : ℕ) ^ 2 ∣ b * N₁ + d ↔ (p : ℕ) ^ 2 ∣ b * N₂ + d) := by
  have h₁ : (p : ℕ) ^ 2 ∣ primeSquareProduct S := by
    rw [primeSquareProduct]
    apply Finset.dvd_prod_of_mem; simp_all
  have h₂ : N₁ ≡ N₂ [MOD primeSquareProduct S] := by
    rw [Nat.ModEq]
    exact hmod
  have h₃ : N₁ ≡ N₂ [MOD (p : ℕ) ^ 2] := by
    have h₃ : N₁ ≡ N₂ [MOD primeSquareProduct S] := h₂
    have h₄ : (p : ℕ) ^ 2 ∣ primeSquareProduct S := h₁
    exact h₃.of_dvd h₄
  have h₄ : b * N₁ ≡ b * N₂ [MOD (p : ℕ) ^ 2] := by
    have h₄ : N₁ ≡ N₂ [MOD (p : ℕ) ^ 2] := h₃
    exact h₄.mul_left b
  have h₅ : b * N₁ + d ≡ b * N₂ + d [MOD (p : ℕ) ^ 2] := by
    have h₅ : b * N₁ ≡ b * N₂ [MOD (p : ℕ) ^ 2] := h₄
    exact h₅.add_right d
  have h₆ : ((p : ℕ) ^ 2 ∣ b * N₁ + d ↔ (p : ℕ) ^ 2 ∣ b * N₂ + d) := by
    have h₆ : b * N₁ + d ≡ b * N₂ + d [MOD (p : ℕ) ^ 2] := h₅
    have h₇ : (p : ℕ) ^ 2 ∣ (p : ℕ) ^ 2 := by
      apply Nat.dvd_refl
    have h₈ : ((p : ℕ) ^ 2 ∣ b * N₁ + d ↔ (p : ℕ) ^ 2 ∣ b * N₂ + d) := by
      apply Nat.ModEq.dvd_iff h₆ h₇
    exact h₈
  exact h₆

theorem condition_mod_invariant (b : ℕ) (T : Finset ℕ) (S : Finset Nat.Primes)
    (N₁ N₂ : ℕ) (hmod : N₁ % primeSquareProduct S = N₂ % primeSquareProduct S) :
    (∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N₁) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N₁ + d)) ↔
    (∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N₂) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N₂ + d)) := by
  constructor <;> intro h p hp
  · constructor
    · rw [← dvd_iff_of_mod_eq_primeSquareProduct S p hp N₁ N₂ hmod]
      exact (h p hp).1
    · intro d hd
      rw [← shifted_dvd_iff_of_mod_eq_primeSquareProduct b d S p hp N₁ N₂ hmod]
      exact (h p hp).2 d hd
  · constructor
    · rw [dvd_iff_of_mod_eq_primeSquareProduct S p hp N₁ N₂ hmod]
      exact (h p hp).1
    · intro d hd
      rw [shifted_dvd_iff_of_mod_eq_primeSquareProduct b d S p hp N₁ N₂ hmod]
      exact (h p hp).2 d hd


end LeanPool.DeadEnds
