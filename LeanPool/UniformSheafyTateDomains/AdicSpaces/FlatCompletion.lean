/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.AdicNakayama
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# Adic completions along faithfully flat maps with trivial special fibre

([hrw-decomposition] L1 engine.) For a faithfully flat algebra `B` over `A`
and an ideal `I` whose level-one map `A/I → B/IB` is surjective, all the
level maps `A/Iⁿ → B/(IB)ⁿ` are bijective — injectivity from
`comap (map I) = I` (faithful flatness), surjectivity by telescoping the
level-one splitting — so the adic completions agree.
-/

@[expose] public section


section FlatCompletion

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
variable (I : Ideal A)

open Classical in
/-- The induced map on power quotients. -/
noncomputable def levelMap (n : ℕ) :
    A ⧸ I ^ n →+* B ⧸ (I.map (algebraMap A B)) ^ n :=
  Ideal.quotientMap _ (algebraMap A B) (by
    rw [← Ideal.map_pow]
    exact Ideal.le_comap_map)

open Classical in
theorem levelMap_mk (n : ℕ) (a : A) :
    levelMap (B := B) I n (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk _ (algebraMap A B a) :=
  Ideal.quotientMap_mk

open Classical in
/-- Injectivity of every level map, from faithful flatness. -/
theorem levelMap_injective [Module.FaithfullyFlat A B] (n : ℕ) :
    Function.Injective (levelMap (B := B) I n) := by
  refine Ideal.quotientMap_injective' ?_
  rw [← Ideal.map_pow, Ideal.comap_map_eq_self_of_faithfullyFlat]

section Surjectivity

variable {I}
variable (h1 : Function.Surjective (levelMap (B := B) I 1))

include h1 in
open Classical in
/-- Level-one surjectivity, unpacked: every element of `B` is congruent to an
image modulo `IB`. -/
theorem exists_sub_mem_of_levelOne (b : B) :
    ∃ a : A, b - algebraMap A B a ∈ I.map (algebraMap A B) := by
  obtain ⟨z, hz⟩ := h1 (Ideal.Quotient.mk _ b)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [levelMap_mk] at hz
  refine ⟨a, ?_⟩
  have h2 := Ideal.Quotient.eq.mp hz
  rw [pow_one] at h2
  exact (Ideal.neg_mem_iff _).mp (by simpa using h2)

include h1 in
open Classical in
/-- **The refinement step**: an element of `(IB)ᵏ` is congruent to the image
of an element of `Iᵏ` modulo `(IB)^(k+1)`. -/
theorem exists_sub_mem_pow_succ {k : ℕ} {x : B}
    (hx : x ∈ (I.map (algebraMap A B)) ^ k) :
    ∃ a ∈ I ^ k, x - algebraMap A B a ∈ (I.map (algebraMap A B)) ^ (k + 1) := by
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap r =>
      obtain ⟨a, ha⟩ := exists_sub_mem_of_levelOne h1 r
      refine ⟨a, by simp, ?_⟩
      rw [pow_one]
      simpa using ha
  | add x y i hx hy ihx ihy =>
      obtain ⟨a, haI, ha⟩ := ihx
      obtain ⟨c, hcI, hc⟩ := ihy
      refine ⟨a + c, Ideal.add_mem _ haI hcI, ?_⟩
      rw [map_add]
      have h3 : x + y - (algebraMap A B a + algebraMap A B c) =
          (x - algebraMap A B a) + (y - algebraMap A B c) := by ring
      rw [h3]
      exact Ideal.add_mem _ ha hc
  | mem_mul m hm i x hx ih =>
      obtain ⟨a, haI, ha⟩ := ih
      -- m • x = m * x; split m * algebraMap a by span induction on m ∈ IB
      have hcore : ∃ a' ∈ I ^ (i + 1),
          m * algebraMap A B a - algebraMap A B a' ∈
            (I.map (algebraMap A B)) ^ (i + 1 + 1) := by
        have hmem : m ∈ Submodule.span B
            ((algebraMap A B) '' (I : Set A)) := hm
        refine Submodule.span_induction ?_ ?_ ?_ ?_ hmem
        · rintro _ ⟨i₀, hi₀, rfl⟩
          refine ⟨i₀ * a, by rw [pow_succ']; exact Ideal.mul_mem_mul hi₀ haI, ?_⟩
          rw [map_mul, sub_self]
          exact Ideal.zero_mem _
        · refine ⟨0, Ideal.zero_mem _, ?_⟩
          rw [map_zero, zero_mul, sub_zero]
          exact Ideal.zero_mem _
        · rintro y z - - ⟨ay, hayI, hay⟩ ⟨az, hazI, haz⟩
          refine ⟨ay + az, Ideal.add_mem _ hayI hazI, ?_⟩
          have h4 : (y + z) * algebraMap A B a -
              algebraMap A B (ay + az) =
              (y * algebraMap A B a - algebraMap A B ay) +
                (z * algebraMap A B a - algebraMap A B az) := by
            rw [map_add]; ring
          rw [h4]
          exact Ideal.add_mem _ hay haz
        · rintro b y - ⟨ay, hayI, hay⟩
          obtain ⟨c, hc⟩ := exists_sub_mem_of_levelOne h1 b
          refine ⟨c * ay, ?_, ?_⟩
          · have h5 : c * ay ∈ I ^ 0 * I ^ (i + 1) :=
              Ideal.mul_mem_mul (by simp) hayI
            simpa using h5
          · have h6 : b • y * algebraMap A B a -
                algebraMap A B (c * ay) =
                b * (y * algebraMap A B a - algebraMap A B ay) +
                  ((b - algebraMap A B c) * algebraMap A B ay) := by
              rw [map_mul]
              have hsmul : b • y = b * y := rfl
              rw [hsmul]
              ring
            rw [h6]
            refine Ideal.add_mem _ ?_ ?_
            · exact Ideal.mul_mem_left _ b hay
            · have h7 : algebraMap A B ay ∈
                  (I.map (algebraMap A B)) ^ (i + 1) := by
                rw [← Ideal.map_pow]
                exact Ideal.mem_map_of_mem _ hayI
              have h8 := Ideal.mul_mem_mul hc h7
              rw [← pow_succ'] at h8
              exact h8
      obtain ⟨a', ha'I, ha'⟩ := hcore
      refine ⟨a', ha'I, ?_⟩
      have h9 : m * x - algebraMap A B a' =
          m * (x - algebraMap A B a) +
            (m * algebraMap A B a - algebraMap A B a') := by ring
      rw [h9]
      refine Ideal.add_mem _ ?_ ha'
      have h10 := Ideal.mul_mem_mul hm ha
      rw [← pow_succ'] at h10
      exact h10

include h1 in
open Classical in
/-- The telescoped congruence: every element of `B` is congruent to an image
modulo `(IB)ⁿ`. -/
theorem exists_sub_mem_pow (b : B) (n : ℕ) :
    ∃ a : A, b - algebraMap A B a ∈ (I.map (algebraMap A B)) ^ n := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
      obtain ⟨a, ha⟩ := ih
      obtain ⟨c, -, hc⟩ := exists_sub_mem_pow_succ h1 ha
      refine ⟨a + c, ?_⟩
      have h11 : b - algebraMap A B (a + c) =
          (b - algebraMap A B a) - algebraMap A B c := by
        rw [map_add]; ring
      rw [h11]
      exact hc

include h1 in
open Classical in
theorem levelMap_surjective (n : ℕ) :
    Function.Surjective (levelMap (B := B) I n) := by
  intro z
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨a, ha⟩ := exists_sub_mem_pow h1 b n
  refine ⟨Ideal.Quotient.mk _ a, ?_⟩
  rw [levelMap_mk]
  exact Ideal.Quotient.eq.mpr ((Ideal.neg_mem_iff _).mp (by simpa using ha))

end Surjectivity

open Classical in
/-- **Adic completions along a faithfully flat map with trivial special
fibre**: if `A/I → B/IB` is surjective and `B` is faithfully flat, the adic
completions agree. -/
noncomputable def adicCompletionEquivOfFaithfullyFlat
    [Module.FaithfullyFlat A B]
    (h1 : Function.Surjective (levelMap (B := B) I 1)) :
    AdicCompletion I A ≃+* AdicCompletion (I.map (algebraMap A B)) B :=
  AdicCompletion.congrPow I (I.map (algebraMap A B))
    (fun n => RingEquiv.ofBijective (levelMap (B := B) I n)
      (⟨levelMap_injective I n, levelMap_surjective h1 n⟩ :
        Function.Bijective (levelMap (B := B) I n)))
    (fun {a b} hab x => by
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      change Ideal.Quotient.factor (Ideal.pow_le_pow_right hab)
          (levelMap (B := B) I b (Ideal.Quotient.mk _ y)) =
        levelMap (B := B) I a (Ideal.Quotient.factor
          (Ideal.pow_le_pow_right hab) (Ideal.Quotient.mk _ y))
      rw [levelMap_mk, Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk,
        levelMap_mk])

end FlatCompletion
