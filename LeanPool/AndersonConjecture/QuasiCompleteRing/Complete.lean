/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FrenzyMath
-/
import LeanPool.AndersonConjecture.Basic
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Ideal.Quotient.Noetherian

/-!
# Complete Implies Quasi-Complete

A complete Noetherian local ring is quasi-complete
(Anderson, 2014, Theorem 3).
-/

open scoped Pointwise

section Helpers
variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
lemma krull_intersection_sup (J : Ideal R) :
    ⨅ n, (J ⊔ (IsLocalRing.maximalIdeal R) ^ n) = J := by
  set M := IsLocalRing.maximalIdeal R
  apply le_antisymm
  · intro x hx
    simp only [Submodule.mem_iInf] at hx
    by_cases hJ : J = ⊤
    · rw [hJ]
      exact Submodule.mem_top
    haveI : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
    haveI : IsLocalRing (R ⧸ J) := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
    haveI : IsLocalHom (Ideal.Quotient.mk J) :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    suffices Ideal.Quotient.mk J x = 0 from Ideal.Quotient.eq_zero_iff_mem.mp this
    set M' := IsLocalRing.maximalIdeal (R ⧸ J)
    have hM' : M' = Ideal.map (Ideal.Quotient.mk J) M := by
      apply le_antisymm
      · intro y hy
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hy
        have hr : r ∈ M := by
          rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
          exact fun hu => hy (hu.map _)
        exact (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mpr ⟨r, hr, rfl⟩
      · intro y hy
        obtain ⟨r, hr, rfl⟩ :=
          (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hy
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hr ⊢
        exact fun hu => hr (isUnit_of_map_unit _ r hu)
    have krl := Ideal.iInf_pow_eq_bot_of_isLocalRing M' (Ideal.IsMaximal.ne_top inferInstance)
    rw [eq_bot_iff] at krl
    apply krl
    rw [Submodule.mem_iInf]
    intro n
    rw [hM', ← Ideal.map_pow]
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp (hx n)
    have : Ideal.Quotient.mk J x = Ideal.Quotient.mk J b := by
      calc _ = Ideal.Quotient.mk J (a + b) := by rw [hab]
        _ = Ideal.Quotient.mk J a + Ideal.Quotient.mk J b := map_add _ _ _
        _ = 0 + Ideal.Quotient.mk J b := by rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
        _ = _ := zero_add _
    rw [this]
    exact (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mpr ⟨b, hb, rfl⟩
  · exact le_iInf fun _ => le_sup_left
lemma comap_map_algebraMap_adicCompletion [IsDomain R] (I : Ideal R) :
    let M := IsLocalRing.maximalIdeal R
    Ideal.comap (algebraMap R (AdicCompletion M R))
      (Ideal.map (algebraMap R (AdicCompletion M R)) I) = I := by
  set M := IsLocalRing.maximalIdeal R
  set f := algebraMap R (AdicCompletion M R)
  apply le_antisymm
  · intro r hr
    have hmem : ∀ n, r ∈ I ⊔ M ^ n := by
      intro n
      have heval_r : AdicCompletion.evalₐ M n (f r) = Ideal.Quotient.mk (M ^ n) r :=
        AdicCompletion.evalₐ_of M n r
      have hfr : f r ∈ Ideal.map f I := hr
      -- evalₐ n ∘ f = mk (M^n) as ring hom
      have hcomp : (AdicCompletion.evalₐ M n).toRingHom.comp f =
          Ideal.Quotient.mk (M ^ n) := by
        ext a
        exact AdicCompletion.evalₐ_of M n a
      have hmk : Ideal.Quotient.mk (M ^ n) r ∈
          Ideal.map (Ideal.Quotient.mk (M ^ n)) I := by
        have h1 : AdicCompletion.evalₐ M n (f r) ∈
            Ideal.map ((AdicCompletion.evalₐ M n).toRingHom) (Ideal.map f I) :=
          Ideal.mem_map_of_mem _ hfr
        rwa [Ideal.map_map, hcomp, heval_r] at h1
      obtain ⟨a, ha, haeq⟩ :=
        (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hmk
      have hdiff : r - a ∈ M ^ n := by
        have := Ideal.Quotient.eq.mp haeq
        rwa [show a - r = -(r - a) from by ring, neg_mem_iff] at this
      exact Submodule.mem_sup.mpr ⟨a, ha, r - a, hdiff, by ring⟩
    rw [← krull_intersection_sup I]
    exact (Submodule.mem_iInf _).mpr hmem
  · exact Ideal.le_comap_map
end Helpers

/-
## Anderson Theorem 3: Complete implies quasi-complete

If R is a complete Noetherian local ring (i.e., IsAdicComplete M R),
then R is quasi-complete.

Proof idea: Uses Artin-Rees / topology of the M-adic completion.
Given a descending chain {A_n}, pass to M/∩A_n. The M-adic topology
on the Artinian quotient M/J^k M forces stabilization.
-/
theorem anderson_complete_isQuasiComplete
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hR : IsAdicComplete (IsLocalRing.maximalIdeal R) R) :
    IsQuasiComplete R := by
  set M := IsLocalRing.maximalIdeal R
  intro A hA k
  set I := ⨅ n, A n
  have hstab : ∀ j, ∃ s, ∀ m, s ≤ m → A m + M ^ j = A s + M ^ j := by
    intro j
    by_cases hMj_top : M ^ j = ⊤
    · exact ⟨0, fun m _ => by simp [hMj_top]⟩
    haveI : Nontrivial (R ⧸ M ^ j) := Ideal.Quotient.nontrivial_iff.mpr hMj_top
    haveI : IsLocalRing (R ⧸ M ^ j) :=
      IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
    haveI : IsArtinianRing (R ⧸ M ^ j) := by
      rw [isArtinianRing_iff_isNilpotent_maximalIdeal]
      refine ⟨j, ?_⟩
      set mk := Ideal.Quotient.mk (M ^ j)
      haveI : IsLocalHom mk := IsLocalHom.of_surjective mk Ideal.Quotient.mk_surjective
      have hM'_eq : IsLocalRing.maximalIdeal (R ⧸ M ^ j) = Ideal.map mk M := by
        apply le_antisymm
        · intro x hx
          obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
          rw [IsLocalRing.mem_maximalIdeal] at hx
          exact (Ideal.mem_map_iff_of_surjective mk Ideal.Quotient.mk_surjective).mpr
            ⟨r, (IsLocalRing.mem_maximalIdeal r).mpr (fun hu => hx (hu.map mk)), rfl⟩
        · intro x hx
          obtain ⟨r, hr, rfl⟩ :=
            (Ideal.mem_map_iff_of_surjective mk Ideal.Quotient.mk_surjective).mp hx
          rw [IsLocalRing.mem_maximalIdeal] at hr ⊢
          exact fun hu => hr (isUnit_of_map_unit mk r hu)
      rw [hM'_eq, ← Ideal.map_pow]
      exact Ideal.map_mk_eq_bot_of_le (le_refl _)
    set Bj : ℕ → Ideal (R ⧸ M ^ j) := fun n => Ideal.map (Ideal.Quotient.mk (M ^ j)) (A n)
    have hBj_anti : Antitone Bj := fun _ _ hmn => Ideal.map_mono (hA hmn)
    let Bj' : ℕ →o (Submodule (R ⧸ M ^ j) (R ⧸ M ^ j))ᵒᵈ :=
      ⟨fun n => OrderDual.toDual (Bj n), fun _ _ h => hBj_anti h⟩
    obtain ⟨s, hs⟩ := WellFoundedGT.monotone_chain_condition Bj'
    refine ⟨s, fun m hm => ?_⟩
    have hBj_eq : Bj s = Bj m := hs m hm
    change A m + M ^ j = A s + M ^ j
    have h1 : ∀ n, A n + M ^ j = Ideal.comap (Ideal.Quotient.mk (M ^ j)) (Bj n) := by
      intro n
      change A n + M ^ j = Ideal.comap (Ideal.Quotient.mk (M ^ j))
        (Ideal.map (Ideal.Quotient.mk (M ^ j)) (A n))
      rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
      congr 1
      rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    rw [h1 m, h1 s, hBj_eq]
  choose s hs using hstab
  let σ : ℕ → ℕ := fun j => Finset.sup (Finset.range (j + 2)) s
  have hσ_ge : ∀ j, s (j + 1) ≤ σ j := fun j =>
    Finset.le_sup (f := s) (Finset.mem_range.mpr (by omega))
  have hσ_ge' : ∀ j, s j ≤ σ j := fun j =>
    Finset.le_sup (f := s) (Finset.mem_range.mpr (by omega))
  have hcompat : ∀ j, A (σ j) + M ^ (j + 1) = A (σ (j + 1)) + M ^ (j + 1) := fun j => by
    rw [hs (j + 1) _ (hσ_ge j), hs (j + 1) _ (hσ_ge' (j + 1))]
  have hdecomp : ∀ j, ∀ z ∈ A (σ j),
      ∃ y ∈ A (σ (j + 1)), ∃ a ∈ M ^ (j + 1), z = y + a := fun j z hz => by
    have hmem : z ∈ A (σ j) + M ^ (j + 1) :=
      Submodule.mem_sup.mpr ⟨z, hz, 0, Submodule.zero_mem _, add_zero z⟩
    rw [hcompat j] at hmem
    obtain ⟨y, hy, a, ha, heq⟩ := Submodule.mem_sup.mp hmem
    exact ⟨y, hy, a, ha, heq.symm⟩
  refine ⟨σ k, fun x hx => ?_⟩
  -- Step 3: Build sequence by recursion
  have hseq : ∃ (y a : ℕ → R),
      y 0 = x ∧
      (∀ n, y n ∈ A (σ (k + n))) ∧
      (∀ n, a n ∈ M ^ (k + n + 1)) ∧
      (∀ n, y n = y (n + 1) + a n) := by
    have step : ∀ n (z : R), z ∈ A (σ (k + n)) →
        ∃ y' ∈ A (σ (k + (n + 1))), ∃ a' ∈ M ^ (k + n + 1), z = y' + a' := by
      intro n z hz
      obtain ⟨y', hy', a', ha', heq⟩ := hdecomp (k + n) z hz
      exact ⟨y', hy', a', ha', heq⟩
    have bstep : ∀ n, ∀ z : {z : R // z ∈ A (σ (k + n))},
        ∃ (y' : {z : R // z ∈ A (σ (k + (n + 1)))}) (a' : {a : R // a ∈ M ^ (k + n + 1)}),
          z.val = y'.val + a'.val := by
      intro n ⟨z, hz⟩
      obtain ⟨y', hy', a', ha', heq⟩ := step n z hz
      exact ⟨⟨y', hy'⟩, ⟨a', ha'⟩, heq⟩
    choose yNext aNext hRec using bstep
    let yy : (n : ℕ) → {z : R // z ∈ A (σ (k + n))} :=
      fun n => Nat.rec ⟨x, hx⟩ (fun m ih => yNext m ih) n
    exact ⟨fun n => (yy n).val, fun n => (aNext n (yy n)).val, rfl,
      fun n => (yy n).property, fun n => (aNext n (yy n)).property,
      fun n => hRec n (yy n)⟩
  obtain ⟨y, a, hy0, hyA, haM, hyrec⟩ := hseq
  let f : ℕ → R := fun n => x - y n
  have hf0 : f 0 = 0 := by simp [f, hy0]
  have hy_diff : ∀ p q, p ≤ q → y p - y q ∈ (M ^ (k + p + 1) : Ideal R) := by
    intro p q hpq
    induction q with
    | zero => simp [Nat.le_zero.mp hpq]
    | succ q ih =>
      by_cases hpq' : p ≤ q
      · have h1 := ih hpq'
        have h2 : y q - y (q + 1) ∈ (M ^ (k + q + 1) : Ideal R) := by
          have : y q - y (q + 1) = a q := by rw [hyrec q]
                                             ring
          rw [this]
          exact haM q
        have h3 : y p - y (q + 1) = (y p - y q) + (y q - y (q + 1)) := by ring
        rw [h3]
        exact Ideal.add_mem _ h1 (Ideal.pow_le_pow_right (by omega) h2)
      · have hpeq : p = q + 1 := by omega
        subst hpeq
        simp
  -- Step 5: f is Cauchy
  have hf_cauchy : ∀ {m n : ℕ}, m ≤ n →
      f m ≡ f n [SMOD (M ^ m • ⊤ : Submodule R R)] := by
    intro m n hmn
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
    change (x - y m) - (x - y n) ∈ (M ^ m : Ideal R)
    have : (x - y m) - (x - y n) = -(y m - y n) := by ring
    rw [this]
    exact neg_mem (Ideal.pow_le_pow_right (by omega) (hy_diff m n hmn))
  -- Step 6: Get limit L
  obtain ⟨L, hL⟩ := IsPrecomplete.prec hR.toIsPrecomplete hf_cauchy
  -- Step 7: f(n) ∈ M^k for all n
  have hfMk : ∀ n, f n ∈ (M ^ k : Ideal R) := by
    intro n
    induction n with
    | zero => rw [hf0]
              exact Submodule.zero_mem _
    | succ n ih =>
      have hstep : f (n + 1) = f n + a n := by
        change x - y (n + 1) = (x - y n) + a n
        rw [hyrec n]
        ring
      rw [hstep]
      exact Ideal.add_mem _ ih (Ideal.pow_le_pow_right (by omega) (haM n))
  -- Step 8: L ∈ M^k
  have hLMk : L ∈ (M ^ k : Ideal R) := by
    have hLk := hL k
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hLk
    have : L = f k - (f k - L) := by ring
    rw [this]
    exact sub_mem (hfMk k) hLk
  have hxL_mem : x - L ∈ I := by
    rw [Submodule.mem_iInf]
    intro m
    rw [← krull_intersection_sup (A m), Submodule.mem_iInf]
    intro j
    -- σ(k+j) ≥ s(j) so stabilization applies
    have hmj : s j ≤ σ (k + j) :=
      Finset.le_sup (f := s) (Finset.mem_range.mpr (by omega))
    -- y(j) ∈ A(σ(k+j)) ⊆ A(s(j)) + M^j
    have hyj_sup : y j ∈ A (s j) + M ^ j := by
      have h1 : y j ∈ A (σ (k + j)) + M ^ j :=
        Submodule.mem_sup.mpr ⟨y j, hyA j, 0, Submodule.zero_mem _, add_zero _⟩
      rwa [hs j (σ (k + j)) hmj] at h1
    -- A(s(j)) ⊆ A(m) ⊔ M^j
    have hAs_sub : ∀ r ∈ A (s j), r ∈ (A m ⊔ M ^ j : Ideal R) := by
      intro r hr
      by_cases hms : m ≤ s j
      · exact Ideal.mem_sup_left (hA hms hr)
      · push Not at hms
        have h1 : r ∈ A (s j) + M ^ j :=
          Submodule.mem_sup.mpr ⟨r, hr, 0, Submodule.zero_mem _, add_zero _⟩
        rwa [← hs j m (by omega)] at h1
    -- y(j) ∈ A(m) ⊔ M^j
    have hyj_Am : y j ∈ (A m ⊔ M ^ j : Ideal R) := by
      obtain ⟨b, hb, c, hc, hbc⟩ := Submodule.mem_sup.mp hyj_sup
      rw [← hbc]
      exact add_mem (hAs_sub b hb) (Ideal.mem_sup_right hc)
    -- f(j) - L ∈ M^j
    have hfL : f j - L ∈ (M ^ j : Ideal R) := by
      have := hL j
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this
      exact this
    -- x - L = y(j) + (f(j) - L) ∈ A(m) ⊔ M^j
    have hxL_eq : x - L = y j + (f j - L) := by change x - L = y j + ((x - y j) - L)
                                                ring
    rw [hxL_eq]
    exact add_mem hyj_Am (Ideal.mem_sup_right hfL)
  -- Conclusion
  exact Submodule.mem_sup.mpr ⟨x - L, hxL_mem, L, hLMk, sub_add_cancel x L⟩
