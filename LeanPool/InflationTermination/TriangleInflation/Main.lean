/-
Copyright (c) 2026 William Blair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Blair
-/

import LeanPool.InflationTermination.TriangleInflation.DefectLaw

/-!
# Nontermination

Statements for paper Section 5: Theorem 5.1 (`thm:membership`), Theorem 5.2 (`thm:main`) and
the nontermination corollary, together with the injectable-set characterization of
Appendix A. Proofs are deferred.

Formalization boundary: the recursively expressible hierarchy `I^exp_t` (paper
Definition 2.5, and Lemma 5.10 (`lem:expressible`) of Section 5.3) is not
formalized; see the header of `Defs.lean`. The paper's `Q(ε,r) ∈ I^exp_t ⊆ I^AI_t ⊆ I^NW_t`
is formalized here as its two weaker halves, membership in `I^AI_t` and in `I^NW_t`.
-/

namespace TriangleInflation

open Finset

noncomputable
section

/-! ## Auxiliary facts

These are general facts that the proofs below need and that the imported files do not
state; they are proved here privately. -/

/-- Pushforwards compose: pushing forward along `F` and then along `G` is pushing forward
along `G ∘ F`. -/
private theorem pushforward_comp {α β γ : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    [DecidableEq γ] (w : α → ℝ) (F : α → β) (G : β → γ) :
    pushforward (pushforward w F) G = pushforward w (fun a => G (F a)) := by
  funext c
  simp only [pushforward]
  have hsplit : ∀ b : β,
      (if G b = c then (∑ a : α, if F a = b then w a else 0) else 0)
        = ∑ a : α, (if G b = c then (if F a = b then w a else 0) else 0) := by
    intro b
    split
    · rfl
    · simp
  simp_rw [hsplit]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single (F a)]
  · simp
  · intro b _ hb
    have hFa : ¬ (F a = b) := fun h => hb h.symm
    simp [hFa]
  · intro ha
    exact absurd (Finset.mem_univ (F a)) ha

/-- Membership of the three party-indexed families in a set forces it into a copied
triangle. -/
private theorem subset_copiedTriangle_of {t : ℕ} {S : Finset (Obs t)} {i j k : Fin t}
    (hA : ∀ a b, Obs.A a b ∈ S → a = i ∧ b = j)
    (hB : ∀ a b, Obs.B a b ∈ S → a = i ∧ b = k)
    (hC : ∀ a b, Obs.C a b ∈ S → a = j ∧ b = k) :
    S ⊆ copiedTriangle i j k := by
  intro u hu
  cases u with
  | A a b =>
      obtain ⟨rfl, rfl⟩ := hA a b hu
      simp [copiedTriangle]
  | B a b =>
      obtain ⟨rfl, rfl⟩ := hB a b hu
      simp [copiedTriangle]
  | C a b =>
      obtain ⟨rfl, rfl⟩ := hC a b hu
      simp [copiedTriangle]

/-- At most one `A`-copy lies in a set on which copy-index erasure is injective. -/
private theorem uniq_A {t : ℕ} {S : Finset (Obs t)}
    (hinj : ∀ u ∈ S, ∀ v ∈ S, u.party = v.party → u = v) {i j : Fin t}
    (h : Obs.A i j ∈ S) : ∀ a b, Obs.A a b ∈ S → a = i ∧ b = j := by
  intro a b hab
  simpa using hinj _ hab _ h rfl

/-- At most one `B`-copy lies in a set on which copy-index erasure is injective. -/
private theorem uniq_B {t : ℕ} {S : Finset (Obs t)}
    (hinj : ∀ u ∈ S, ∀ v ∈ S, u.party = v.party → u = v) {i k : Fin t}
    (h : Obs.B i k ∈ S) : ∀ a b, Obs.B a b ∈ S → a = i ∧ b = k := by
  intro a b hab
  simpa using hinj _ hab _ h rfl

/-- At most one `C`-copy lies in a set on which copy-index erasure is injective. -/
private theorem uniq_C {t : ℕ} {S : Finset (Obs t)}
    (hinj : ∀ u ∈ S, ∀ v ∈ S, u.party = v.party → u = v) {j k : Fin t}
    (h : Obs.C j k ∈ S) : ∀ a b, Obs.C a b ∈ S → a = j ∧ b = k := by
  intro a b hab
  simpa using hinj _ hab _ h rfl

/-- On a subset of the copied triangle `Δ_{ijk}` the restriction of an assignment is the
party-read of the three-bit outcome of `Δ_{ijk}`. -/
private theorem restrictAssign_eq_partyRead {t : ℕ} {S : Finset (Obs t)} {i j k : Fin t}
    (hS : S ⊆ copiedTriangle i j k) :
    restrictAssign S = fun ω => partyRead S (readTriangle i j k ω) := by
  funext ω v
  obtain ⟨u, hu⟩ := v
  have hmem := hS hu
  simp only [copiedTriangle, Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl <;> rfl

/-! ## The two formalized hierarchies -/

/-- Paper equation (eq:nested), the part that the formalized definitions express:
`I^AI_t ⊆ I^NW_t`. -/
theorem nwFeasible_of_aiFeasible {t : ℕ} {P : ThreeBit → ℝ} (h : AIFeasible t P) :
    NWFeasible t P := by
  obtain ⟨Γ, hlaw, hsym, hdiag, -, -⟩ := h
  exact ⟨Γ, hlaw, hsym, hdiag⟩

/-- Paper Appendix A.3 (`app:injectable`): for the triangle, the injectable sets of the
order-`t` inflation are exactly the subsets of copied triangles. -/
theorem injectable_iff_injectableRaw {t : ℕ} (ht : 1 ≤ t) (S : Finset (Obs t)) :
    Injectable S ↔ InjectableRaw S := by
  classical
  constructor
  · rintro ⟨i, j, k, hS⟩
    refine ⟨?_, ?_⟩
    · intro u hu v hv hpar
      have hu' := hS hu
      have hv' := hS hv
      simp only [copiedTriangle, Finset.mem_insert, Finset.mem_singleton] at hu' hv'
      rcases hu' with rfl | rfl | rfl <;> rcases hv' with rfl | rfl | rfl <;>
        first
          | rfl
          | (exact absurd hpar (by simp [Obs.party]))
    · intro u hu v hv
      have hu' := hS hu
      have hv' := hS hv
      simp only [copiedTriangle, Finset.mem_insert, Finset.mem_singleton] at hu' hv'
      rcases hu' with rfl | rfl | rfl <;> rcases hv' with rfl | rfl | rfl <;>
        first
          | exact rfl
          | exact trivial
  · rintro ⟨hinj, hshare⟩
    have hd : Fin t := ⟨0, ht⟩
    by_cases hA : ∃ a b, Obs.A a b ∈ S
    · obtain ⟨i, j, hAm⟩ := hA
      have pA := uniq_A hinj hAm
      by_cases hB : ∃ a b, Obs.B a b ∈ S
      · obtain ⟨i2, k, hBm⟩ := hB
        have hii : i = i2 := hshare _ hAm _ hBm
        subst hii
        have pB := uniq_B hinj hBm
        by_cases hC : ∃ a b, Obs.C a b ∈ S
        · obtain ⟨j2, k2, hCm⟩ := hC
          have hjj : j = j2 := hshare _ hAm _ hCm
          have hkk : k = k2 := hshare _ hBm _ hCm
          subst hjj
          subst hkk
          exact ⟨i, j, k, subset_copiedTriangle_of pA pB (uniq_C hinj hCm)⟩
        · exact ⟨i, j, k, subset_copiedTriangle_of pA pB
            (fun a b hab => (hC ⟨a, b, hab⟩).elim)⟩
      · by_cases hC : ∃ a b, Obs.C a b ∈ S
        · obtain ⟨j2, k, hCm⟩ := hC
          have hjj : j = j2 := hshare _ hAm _ hCm
          subst hjj
          exact ⟨i, j, k, subset_copiedTriangle_of pA
            (fun a b hab => (hB ⟨a, b, hab⟩).elim) (uniq_C hinj hCm)⟩
        · exact ⟨i, j, hd, subset_copiedTriangle_of pA
            (fun a b hab => (hB ⟨a, b, hab⟩).elim)
            (fun a b hab => (hC ⟨a, b, hab⟩).elim)⟩
    · by_cases hB : ∃ a b, Obs.B a b ∈ S
      · obtain ⟨i, k, hBm⟩ := hB
        have pB := uniq_B hinj hBm
        by_cases hC : ∃ a b, Obs.C a b ∈ S
        · obtain ⟨j, k2, hCm⟩ := hC
          have hkk : k = k2 := hshare _ hBm _ hCm
          subst hkk
          exact ⟨i, j, k, subset_copiedTriangle_of
            (fun a b hab => (hA ⟨a, b, hab⟩).elim) pB (uniq_C hinj hCm)⟩
        · exact ⟨i, hd, k, subset_copiedTriangle_of
            (fun a b hab => (hA ⟨a, b, hab⟩).elim) pB
            (fun a b hab => (hC ⟨a, b, hab⟩).elim)⟩
      · by_cases hC : ∃ a b, Obs.C a b ∈ S
        · obtain ⟨j, k, hCm⟩ := hC
          exact ⟨hd, j, k, subset_copiedTriangle_of
            (fun a b hab => (hA ⟨a, b, hab⟩).elim)
            (fun a b hab => (hB ⟨a, b, hab⟩).elim) (uniq_C hinj hCm)⟩
        · exact ⟨hd, hd, hd, subset_copiedTriangle_of
            (fun a b hab => (hA ⟨a, b, hab⟩).elim)
            (fun a b hab => (hB ⟨a, b, hab⟩).elim)
            (fun a b hab => (hC ⟨a, b, hab⟩).elim)⟩

/-! ## Theorem 5.1: membership at every finite order -/

/-- The defect law with `s = 1 - r/(1-ε)^{t-1}` witnesses the ancestral-independence
conditions for `Q(ε,r)`: this is the content of paper Section 5.3 for the two formalized
hierarchies. -/
theorem defectLaw_witnesses_AI (t : ℕ) (ht : 1 ≤ t) {ε r : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ (1 - ε) ^ (t - 1)) :
    IsLaw (defectLaw t ε (sParam t ε r)) ∧
      SymmetricLaw t (defectLaw t ε (sParam t ε r)) ∧
      pushforward (defectLaw t ε (sParam t ε r)) readDiagonal = tensorPow t (Q ε r) ∧
      InjectableMarginals t (defectLaw t ε (sParam t ε r)) (Q ε r) ∧
      AncestralProducts t (defectLaw t ε (sParam t ε r)) (Q ε r) := by
  obtain ⟨hs0, hs1⟩ := sParam_mem_Icc t ht hε0 hε1 hr0 hr1
  have hlaw : IsLaw (defectLaw t ε (sParam t ε r)) :=
    defectLaw_isLaw hε0.le hε1.le hs0 hs1
  have hsym : SymmetricLaw t (defectLaw t ε (sParam t ε r)) :=
    defect_symmetric ε (sParam t ε r)
  have hdiag : pushforward (defectLaw t ε (sParam t ε r)) readDiagonal
      = tensorPow t (Q ε r) := by
    rw [defect_diagonal_law ht hε0.le hε1.le hs0 hs1, one_sub_sParam_mul t ht hε1]
  have hinjm : InjectableMarginals t (defectLaw t ε (sParam t ε r)) (Q ε r) := by
    rintro S ⟨i, j, k, hS⟩
    calc pushforward (defectLaw t ε (sParam t ε r)) (restrictAssign S)
        = pushforward (defectLaw t ε (sParam t ε r))
            (fun ω => partyRead S (readTriangle i j k ω)) := by
          rw [restrictAssign_eq_partyRead hS]
      _ = pushforward (pushforward (defectLaw t ε (sParam t ε r)) (readTriangle i j k))
            (partyRead S) :=
          (pushforward_comp _ _ _).symm
      _ = pushforward (Q ε r) (partyRead S) := by
          rw [defect_copiedTriangle_law ht hε0.le hε1.le hs0 hs1 i j k,
            one_sub_sParam_mul t ht hε1]
  refine ⟨hlaw, hsym, hdiag, hinjm, ?_⟩
  intro n S hInj hIndep
  rw [defect_independence_family hε0.le hε1.le hs0 hs1 S hIndep]
  funext φ
  exact Finset.prod_congr rfl fun m _ => by rw [hinjm (S m) (hInj m)]

/-- Paper Theorem 5.1 (`thm:membership`), ancestral-independence half: for `t ≥ 1`,
`0 < ε < 1` and `0 ≤ r ≤ (1-ε)^{t-1}`, the law `Q(ε,r)` is feasible at order `t` for the
ancestral-independence hierarchy. -/
theorem membership_AI (t : ℕ) (ht : 1 ≤ t) {ε r : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ (1 - ε) ^ (t - 1)) : AIFeasible t (Q ε r) :=
  ⟨defectLaw t ε (sParam t ε r), defectLaw_witnesses_AI t ht hε0 hε1 hr0 hr1⟩

/-- Paper Theorem 5.1 (`thm:membership`), Navascués–Wolfe half. -/
theorem membership_NW (t : ℕ) (ht : 1 ≤ t) {ε r : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ (1 - ε) ^ (t - 1)) : NWFeasible t (Q ε r) :=
  nwFeasible_of_aiFeasible (membership_AI t ht hε0 hε1 hr0 hr1)

/-! ## Theorem 5.2: no finite characterizing order -/

/-- The parameters of paper Theorem 5.2 lie in the range of Theorem 5.1. -/
theorem epsFam_mem (t : ℕ) (ht : 1 ≤ t) : 0 < epsFam t ∧ epsFam t < 1 := by
  have h1 : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have h3 : (1 : ℝ) ≤ (t : ℝ) ^ 3 := one_le_pow₀ h1
  have hpos : (0 : ℝ) < 2 * (t : ℝ) ^ 3 := by linarith
  have he : epsFam t = 1 / (2 * (t : ℝ) ^ 3) := rfl
  refine ⟨?_, ?_⟩
  · rw [he]
    exact div_pos one_pos hpos
  · rw [he, div_lt_one hpos]
    linarith

/-- `ε_t` is below the Finner threshold `t⁻³`. -/
private theorem epsFam_lt (t : ℕ) (ht : 1 ≤ t) : epsFam t < 1 / (t : ℝ) ^ 3 := by
  have h1 : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have h3 : (0 : ℝ) < (t : ℝ) ^ 3 := lt_of_lt_of_le zero_lt_one (one_le_pow₀ h1)
  have hx : (0 : ℝ) < 1 / (t : ℝ) ^ 3 := by positivity
  have he : epsFam t = 1 / (2 * (t : ℝ) ^ 3) := rfl
  rw [he]
  have hhalf : 1 / (2 * (t : ℝ) ^ 3) = (1 / (t : ℝ) ^ 3) / 2 := by
    field_simp
  rw [hhalf]
  linarith

/-- Paper Theorem 5.2 (`thm:main`), membership half: `P_t ∈ I^AI_t ⊆ I^NW_t`. -/
theorem main_membership (t : ℕ) (ht : 1 ≤ t) : AIFeasible t (Pfam t) ∧ NWFeasible t (Pfam t) := by
  obtain ⟨h0, h1⟩ := epsFam_mem t ht
  have hr0 : (0 : ℝ) ≤ (1 - epsFam t) ^ (t - 1) := pow_nonneg (by linarith) _
  have hai : AIFeasible t (Q (epsFam t) (rFam t)) :=
    membership_AI t ht h0 h1 hr0 le_rfl
  exact ⟨hai, nwFeasible_of_aiFeasible hai⟩

/-- Paper Theorem 5.2 (`thm:main`), violation half: the Finner margin of `P_t` is at least
`ε_t²/2 > 0`, so `P_t ∉ C_tri`. -/
theorem main_violation (t : ℕ) (ht : 1 ≤ t) :
    epsFam t ^ 2 / 2
        ≤ atom000 (Pfam t) ^ 2 - margA (Pfam t) * margB (Pfam t) * margC (Pfam t)
      ∧ ¬ TriangleCompatible (Pfam t) := by
  refine ⟨witness_margin t ht, ?_⟩
  exact witness_not_compatible t ht (epsFam_mem t ht).1 (epsFam_lt t ht)

/-- `P_t` is a probability law. -/
theorem Pfam_isLaw (t : ℕ) (ht : 1 ≤ t) : IsLaw (Pfam t) := by
  obtain ⟨h0, h1⟩ := epsFam_mem t ht
  have hr0 : (0 : ℝ) ≤ rFam t := pow_nonneg (by linarith) _
  have hr1 : rFam t ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  exact Q_isLaw h0.le h1.le hr0 hr1

/-- Paper Theorem 5.2 (`thm:main`), the nontermination corollary: for every finite order `t`
there is a three-bit law that passes the order-`t` test and is not triangle compatible, so no
finite order of the hierarchy characterizes `C_tri`.

The plain name `TriangleInflation.no_finite_characterizing_order` is reserved for the registry
statement, which `PalomarSolutions/TriangleInflation.lean` declares and discharges by this
theorem; Comparator identifies the Challenge and the Solution by that one name. -/
theorem no_finite_characterizing_order_lib (t : ℕ) (ht : 1 ≤ t) :
    ∃ P : ThreeBit → ℝ, IsLaw P ∧ AIFeasible t P ∧ NWFeasible t P ∧ ¬ TriangleCompatible P :=
  ⟨Pfam t, Pfam_isLaw t ht, (main_membership t ht).1, (main_membership t ht).2,
    (main_violation t ht).2⟩

end

end TriangleInflation
