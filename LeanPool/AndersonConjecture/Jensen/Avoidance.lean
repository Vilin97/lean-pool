/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FrenzyMath
-/
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Mathlib.RingTheory.PicardGroup
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology

/-!
# Prime Avoidance in Complete Local Rings

Given a complete local ring and a family of primes, one can find
elements avoiding all shifted translates. The countable case uses
Cauchy sequences
the uncountable case uses a cardinality argument.

Heitmann, "Characterization of completions of UFDs", 1993, Lemmas 2--3.
-/

noncomputable section

open Cardinal Ideal Set Pointwise

-- Classical decidability is used pervasively (`dite` in `avoidStep`, `by_cases`, etc.).
attribute [local instance 20] Classical.propDecidable

variable {T : Type*} [CommRing T] [IsLocalRing T]

omit [IsLocalRing T] in
/-- Extract `u - r ∈ P` from `u ∈ ↑P + {r}` (Minkowski sum). -/
lemma mem_sub_of_mem_add_singleton {P : Ideal T} {r u : T}
    (hmem : u ∈ (P : Set T) + ({r} : Set T)) : u - r ∈ P := by
  obtain ⟨p, hp, s, hs, h⟩ := hmem
  rw [Set.mem_singleton_iff] at hs
  subst hs
  subst h
  rwa [add_sub_cancel_right]

omit [IsLocalRing T] in
/-- If `u ∈ P + {r}` and `y ∉ P`, then `u + y ∉ P + {r}`. -/
lemma not_mem_add_singleton_of_add {P : Ideal T}
    {r u y : T} (hu : u ∈ (P : Set T) + ({r} : Set T)) (hy : y ∉ P) :
    u + y ∉ (P : Set T) + ({r} : Set T) := by
  intro h
  exact hy (by
    have := P.sub_mem (mem_sub_of_mem_add_singleton h) (mem_sub_of_mem_add_singleton hu)
    rwa [show (u + y) - r - (u - r) = y from by ring] at this)

/-- Separation for translates: if `x ∉ P + {r}` with `P` prime `≠ 𝔪` in a Noetherian
local ring, then `∃ N` such that adding any element of `𝔪^N` preserves non-membership.
Uses the Krull intersection theorem in `T ⧸ P`. -/
lemma separation_for_translate [IsNoetherianRing T]
    (P : Ideal T) (hP : P.IsPrime) (_hP_ne : P ≠ IsLocalRing.maximalIdeal T)
    (x r : T) (hx : x ∉ (P : Set T) + ({r} : Set T)) :
    ∃ N : ℕ, ∀ m ∈ IsLocalRing.maximalIdeal T ^ N,
      x + m ∉ (P : Set T) + ({r} : Set T) := by
  have hxr : x - r ∉ P := fun h => hx ⟨x - r, h, r, rfl, sub_add_cancel x r⟩
  by_contra hall
  push Not at hall
  set 𝔪 := IsLocalRing.maximalIdeal T
  have hall' : ∀ N, ∃ m ∈ 𝔪 ^ N, (x - r) + m ∈ P := by
    intro N
    obtain ⟨m, hm, hmem⟩ := hall N
    refine ⟨m, hm, ?_⟩
    have := mem_sub_of_mem_add_singleton hmem
    rwa [show (x + m) - r = (x - r) + m from by ring] at this
  set 𝔪' := 𝔪.map (Ideal.Quotient.mk P)
  have hπ : ∀ N, (Ideal.Quotient.mk P) (x - r) ∈ 𝔪' ^ N := by
    intro N
    rw [← Ideal.map_pow]
    obtain ⟨m, hm, hxm⟩ := hall' N
    have heq : (Ideal.Quotient.mk P) (x - r) = (Ideal.Quotient.mk P) (-m) := by
      have h0 : (Ideal.Quotient.mk P) (x - r) + (Ideal.Quotient.mk P) m = 0 := by
        rw [← map_add]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr hxm
      rw [eq_neg_of_add_eq_zero_left h0, ← map_neg]
    rw [heq]
    exact Ideal.mem_map_of_mem _ ((𝔪 ^ N).neg_mem hm)
  have h𝔪' : 𝔪' ≠ ⊤ := by
    intro heq
    have h1 := (Ideal.eq_top_iff_one _).mp heq
    rw [Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at h1
    obtain ⟨m, hm, hm1⟩ := h1
    have hsub : m - 1 ∈ P :=
      Ideal.Quotient.eq_zero_iff_mem.mp (by rw [map_sub, hm1, map_one, sub_self])
    have : (1 : T) ∈ 𝔪 := by
      have := 𝔪.sub_mem hm (IsLocalRing.le_maximalIdeal hP.ne_top hsub)
      rwa [show m - (m - 1) = (1 : T) from by ring] at this
    exact (IsLocalRing.maximalIdeal.isMaximal T).ne_top ((Ideal.eq_top_iff_one _).mpr this)
  have _ : IsDomain (T ⧸ P) := Ideal.Quotient.isDomain P
  have _ : IsNoetherianRing (T ⧸ P) := Ideal.Quotient.isNoetherianRing P
  have hmem := Ideal.mem_iInf.mpr hπ
  rw [Ideal.iInf_pow_eq_bot_of_isDomain 𝔪' h𝔪', Ideal.mem_bot] at hmem
  exact hxr (Ideal.Quotient.eq_zero_iff_mem.mp hmem)

/-- Membership in `I` via Krull intersection: if `L ∈ I + 𝔪^n` for all `n`, then `L ∈ I`.
Uses the Artin-Rees lemma (via `Ideal.mem_iInf_smul_pow_eq_bot_iff`) on `T ⧸ I`. -/
lemma mem_of_mem_sup_pow [IsNoetherianRing T]
    (I : Ideal T) (L : T)
    (h : ∀ n, L ∈ I ⊔ IsLocalRing.maximalIdeal T ^ n) : L ∈ I := by
  set 𝔪 := IsLocalRing.maximalIdeal T
  set πI := Ideal.Quotient.mk I
  suffices πI L = 0 from Ideal.Quotient.eq_zero_iff_mem.mp this
  have hL : ∀ n, πI L ∈ (𝔪 ^ n • ⊤ : Submodule T (T ⧸ I)) := by
    intro n
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp (h n)
    rw [show πI L = πI b from by
          calc πI L = πI (a + b) := by rw [hab]
            _ = πI a + πI b := map_add _ _ _
            _ = 0 + πI b := by rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
            _ = πI b := zero_add _,
        show πI b = b • (1 : T ⧸ I) from by
          change Submodule.Quotient.mk b = Submodule.Quotient.mk (b * 1)
          rw [mul_one]]
    exact Submodule.smul_mem_smul hb Submodule.mem_top
  have hLinf := (Submodule.mem_iInf _).mpr hL
  rw [Ideal.mem_iInf_smul_pow_eq_bot_iff] at hLinf
  obtain ⟨⟨r, hr⟩, hrL⟩ := hLinf
  change r • πI L = πI L at hrL
  have hzero : (1 - r) • πI L = 0 := by rw [sub_smul, one_smul, hrL, sub_self]
  exact (IsLocalRing.isUnit_one_sub_self_of_mem_nonunits r
    ((IsLocalRing.mem_maximalIdeal r).mp hr)).smul_left_cancel.mp (by rw [hzero, smul_zero])

/-- Step function for the Cauchy sequence construction.
Given current value `u` and precision level `q`, produces `(u', q')` that avoids
`P + {r}` with separation at level `q'`. -/
def avoidStep [IsNoetherianRing T]
    (I P : Ideal T) (hP : P.IsPrime) (hP_ne : P ≠ IsLocalRing.maximalIdeal T)
    (r : T) (ea : ∀ n, ∃ z ∈ I * IsLocalRing.maximalIdeal T ^ n, z ∉ P)
    (u : T) (q : ℕ) : T × ℕ :=
  if hmem : u ∈ (P : Set T) + ({r} : Set T) then
    (u + (ea q).choose,
     max (q + 1) (separation_for_translate P hP hP_ne
       (u + (ea q).choose) r
       (not_mem_add_singleton_of_add hmem (ea q).choose_spec.2)).choose)
  else
    (u, max (q + 1) (separation_for_translate P hP hP_ne u r hmem).choose)

/-- Build the Cauchy sequence `(u_n, q_n)` by iterating `avoidStep`. -/
def buildSeq [IsNoetherianRing T]
    (I : Ideal T)
    {C : Set (Ideal T)} (hC_prime : ∀ P ∈ C, P.IsPrime)
    (hC_ne_max : ∀ P ∈ C, P ≠ IsLocalRing.maximalIdeal T)
    (exists_avoid : ∀ P ∈ C, ∀ n, ∃ z ∈ I * IsLocalRing.maximalIdeal T ^ n, z ∉ P)
    (P_of : ℕ → Ideal T) (r_of : ℕ → T) (hP_mem : ∀ n, P_of n ∈ C)
    : ℕ → T × ℕ
  | 0 => (0, 0)
  | n + 1 =>
    let prev := buildSeq I hC_prime hC_ne_max exists_avoid P_of r_of hP_mem n
    avoidStep I (P_of n) (hC_prime _ (hP_mem n)) (hC_ne_max _ (hP_mem n))
      (r_of n) (exists_avoid _ (hP_mem n)) prev.1 prev.2

-- Properties of avoidStep
lemma avoidStep_q_inc [IsNoetherianRing T]
    (I P : Ideal T) (hP : P.IsPrime) (hP_ne : P ≠ IsLocalRing.maximalIdeal T)
    (r : T) (ea : ∀ n, ∃ z ∈ I * IsLocalRing.maximalIdeal T ^ n, z ∉ P) (u : T) (q : ℕ) :
    (avoidStep I P hP hP_ne r ea u q).2 ≥ q + 1 := by
  unfold avoidStep
  split <;> exact le_max_left _ _

lemma avoidStep_diff [IsNoetherianRing T]
    (I P : Ideal T) (hP : P.IsPrime) (hP_ne : P ≠ IsLocalRing.maximalIdeal T)
    (r : T) (ea : ∀ n, ∃ z ∈ I * IsLocalRing.maximalIdeal T ^ n, z ∉ P) (u : T) (q : ℕ) :
    (avoidStep I P hP hP_ne r ea u q).1 - u ∈
      I * IsLocalRing.maximalIdeal T ^ q := by
  simp only [avoidStep]
  split
  · dsimp
    rw [show u + (ea q).choose - u = (ea q).choose from by ring]
    exact (ea q).choose_spec.1
  · dsimp
    simp [(I * IsLocalRing.maximalIdeal T ^ q).zero_mem]

lemma avoidStep_avoids [IsNoetherianRing T]
    (I P : Ideal T) (hP : P.IsPrime) (hP_ne : P ≠ IsLocalRing.maximalIdeal T)
    (r : T) (ea : ∀ n, ∃ z ∈ I * IsLocalRing.maximalIdeal T ^ n, z ∉ P) (u : T) (q : ℕ) :
    (avoidStep I P hP hP_ne r ea u q).1 ∉ (P : Set T) + ({r} : Set T) := by
  unfold avoidStep
  split
  · exact not_mem_add_singleton_of_add ‹_› (ea q).choose_spec.2
  · exact ‹_›

lemma avoidStep_sep [IsNoetherianRing T]
    (I P : Ideal T) (hP : P.IsPrime) (hP_ne : P ≠ IsLocalRing.maximalIdeal T)
    (r : T) (ea : ∀ n, ∃ z ∈ I * IsLocalRing.maximalIdeal T ^ n, z ∉ P) (u : T) (q : ℕ) :
    ∀ m ∈ IsLocalRing.maximalIdeal T ^ (avoidStep I P hP hP_ne r ea u q).2,
      (avoidStep I P hP hP_ne r ea u q).1 + m ∉ (P : Set T) + ({r} : Set T) := by
  unfold avoidStep
  split
  · intro m hm
    have havoid := not_mem_add_singleton_of_add ‹_› (ea q).choose_spec.2
    have hN := (separation_for_translate P hP hP_ne (u + (ea q).choose) r havoid).choose_spec
    apply hN
    exact Ideal.pow_le_pow_right (le_max_right _ _) hm
  · intro m hm
    have hN := (separation_for_translate P hP hP_ne u r ‹_›).choose_spec
    apply hN
    exact Ideal.pow_le_pow_right (le_max_right _ _) hm

lemma buildSeqQInc [IsNoetherianRing T]
    (I : Ideal T)
    {C : Set (Ideal T)} (hC_prime : ∀ P ∈ C, P.IsPrime)
    (hC_ne_max : ∀ P ∈ C, P ≠ IsLocalRing.maximalIdeal T)
    (ea : ∀ P ∈ C, ∀ n, ∃ z ∈ I * IsLocalRing.maximalIdeal T ^ n, z ∉ P)
    (P_of : ℕ → Ideal T) (r_of : ℕ → T) (hP_mem : ∀ n, P_of n ∈ C) (n : ℕ) :
    (buildSeq I hC_prime hC_ne_max ea P_of r_of hP_mem (n + 1)).2 ≥
    (buildSeq I hC_prime hC_ne_max ea P_of r_of hP_mem n).2 + 1 :=
  avoidStep_q_inc I (P_of n) (hC_prime _ (hP_mem n)) (hC_ne_max _ (hP_mem n))
    (r_of n) (ea _ (hP_mem n)) _ _

lemma buildSeqDiff [IsNoetherianRing T]
    (I : Ideal T)
    {C : Set (Ideal T)} (hC_prime : ∀ P ∈ C, P.IsPrime)
    (hC_ne_max : ∀ P ∈ C, P ≠ IsLocalRing.maximalIdeal T)
    (ea : ∀ P ∈ C, ∀ n, ∃ z ∈ I * IsLocalRing.maximalIdeal T ^ n, z ∉ P)
    (P_of : ℕ → Ideal T) (r_of : ℕ → T) (hP_mem : ∀ n, P_of n ∈ C) (n : ℕ) :
    (buildSeq I hC_prime hC_ne_max ea P_of r_of hP_mem (n + 1)).1 -
    (buildSeq I hC_prime hC_ne_max ea P_of r_of hP_mem n).1 ∈
    I * IsLocalRing.maximalIdeal T ^ (buildSeq I hC_prime hC_ne_max ea P_of r_of hP_mem n).2 :=
  avoidStep_diff I (P_of n) (hC_prime _ (hP_mem n)) (hC_ne_max _ (hP_mem n))
    (r_of n) (ea _ (hP_mem n)) _ _

lemma buildSeqAvoids [IsNoetherianRing T]
    (I : Ideal T)
    {C : Set (Ideal T)} (hC_prime : ∀ P ∈ C, P.IsPrime)
    (hC_ne_max : ∀ P ∈ C, P ≠ IsLocalRing.maximalIdeal T)
    (ea : ∀ P ∈ C, ∀ n, ∃ z ∈ I * IsLocalRing.maximalIdeal T ^ n, z ∉ P)
    (P_of : ℕ → Ideal T) (r_of : ℕ → T) (hP_mem : ∀ n, P_of n ∈ C) (n : ℕ) :
    (buildSeq I hC_prime hC_ne_max ea P_of r_of hP_mem (n + 1)).1 ∉
    (P_of n : Set T) + ({r_of n} : Set T) :=
  avoidStep_avoids I (P_of n) (hC_prime _ (hP_mem n)) (hC_ne_max _ (hP_mem n))
    (r_of n) (ea _ (hP_mem n)) _ _

lemma buildSeqSep [IsNoetherianRing T]
    (I : Ideal T)
    {C : Set (Ideal T)} (hC_prime : ∀ P ∈ C, P.IsPrime)
    (hC_ne_max : ∀ P ∈ C, P ≠ IsLocalRing.maximalIdeal T)
    (ea : ∀ P ∈ C, ∀ n, ∃ z ∈ I * IsLocalRing.maximalIdeal T ^ n, z ∉ P)
    (P_of : ℕ → Ideal T) (r_of : ℕ → T) (hP_mem : ∀ n, P_of n ∈ C) (n : ℕ) :
    ∀ m ∈ IsLocalRing.maximalIdeal T ^
        (buildSeq I hC_prime hC_ne_max ea P_of r_of hP_mem (n + 1)).2,
      (buildSeq I hC_prime hC_ne_max ea P_of r_of hP_mem (n + 1)).1 + m ∉
      (P_of n : Set T) + ({r_of n} : Set T) :=
  avoidStep_sep I (P_of n) (hC_prime _ (hP_mem n)) (hC_ne_max _ (hP_mem n))
    (r_of n) (ea _ (hP_mem n)) _ _

/-!
## Countable Avoidance (Heitmann Lemma 2)

If I ⊄ P for all P in a countable set C of primes (M ∉ C),
then there exists u ∈ I avoiding all translates P + r for P ∈ C, r ∈ D (countable).
Requires completeness of T (to take limits of Cauchy sequences).
-/

/-- Heitmann Lemma 2: Countable avoidance in complete local rings.
Given a countable set C of primes not containing M, a countable set D ⊆ T,
and an ideal I not contained in any P ∈ C, there exists u ∈ I such that
u ∉ P + {r} for all P ∈ C and r ∈ D.

The proof constructs a Cauchy sequence in I whose limit avoids all translates. -/
theorem countable_avoidance
    [TopologicalSpace T] [IsTopologicalRing T] [IsNoetherianRing T]
    [IsAdicComplete (IsLocalRing.maximalIdeal T) T]
    {C : Set (Ideal T)} (hC_countable : C.Countable)
    (hC_prime : ∀ P ∈ C, P.IsPrime)
    (hC_ne_max : ∀ P ∈ C, P ≠ IsLocalRing.maximalIdeal T)
    {D : Set T} (hD_countable : D.Countable)
    {I : Ideal T} (hI : ∀ P ∈ C, ¬(I ≤ P)) :
    ∃ u ∈ I, ∀ P ∈ C, ∀ r ∈ D, (u : T) ∉ (P : Set T) + ({r} : Set T) := by
  by_cases hC_empty : C = ∅
  · exact ⟨0, I.zero_mem, fun P hP => absurd hP (hC_empty ▸ fun a => a.elim)⟩
  by_cases hD_empty : D = ∅
  · exact ⟨0, I.zero_mem, fun _ _ r hr => absurd hr (hD_empty ▸ fun a => a.elim)⟩
  /- Proof sketch (Heitmann Lemma 2):
     Enumerate C × D = {(Pₙ, rₙ)}ₙ (countable). Build Cauchy sequence u₀ = 0 in I.
     At step n+1: if uₙ ∉ Pₙ + {rₙ}, set u_{n+1} = uₙ.
     Otherwise, find yₙ ∈ I · M^{q(n)} \ Pₙ (exists since I ⊄ Pₙ and M ≠ Pₙ,
     so I · M^n ⊄ Pₙ for all n: if M^n ⊆ Pₙ then M ⊆ Pₙ by primality, contradiction),
     set u_{n+1} = uₙ + yₙ.
     Choose q(n) increasing fast enough that:
     (a) the sequence is M-adically Cauchy (differences in M^{q(n)})
     (b) once uₙ ∉ Pₖ + {rₖ} for k ≤ n, later modifications don't re-enter Pₖ + {rₖ}
         (choose q(n) > N where uₙ ∉ Pₖ + {rₖ} + M^N for k ≤ n)
     The limit exists by IsAdicComplete, lies in I (I is M-adically closed as
     I = ⋂ₙ (I + M^n) in a complete ring), and avoids each Pₙ + {rₙ} by (b).
     Key sublemma: I · M^n ⊄ P for P ∈ C, since P ≠ M implies M ⊄ P,
     so ∃ m ∈ M \ P, and ∃ a ∈ I \ P, then a · mⁿ ∈ I · M^n \ P. -/
  set 𝔪 := IsLocalRing.maximalIdeal T with h𝔪_def
  -- Key sub-lemma: M^n ≤ P implies M ≤ P for P prime
  have pow_le_prime :
      ∀ (P : Ideal T), P.IsPrime → ∀ n : ℕ, 𝔪 ^ n ≤ P → 𝔪 ≤ P := by
    intro P hP n
    induction n with
    | zero =>
      intro h
      have : P = ⊤ := top_le_iff.mp (by rwa [pow_zero, Ideal.one_eq_top] at h)
      exact absurd this hP.ne_top
    | succ k ih =>
      intro h
      rw [pow_succ] at h
      exact (hP.mul_le.mp h).elim ih id
  -- Key sub-lemma: I * M^n ⊄ P for P ∈ C
  have key_sublemma : ∀ P ∈ C, ∀ n : ℕ, ¬(I * 𝔪 ^ n ≤ P) := by
    intro P hP n hle
    have hP_prime := hC_prime P hP
    rcases hP_prime.mul_le.mp hle with hI_le | hMn_le
    · exact hI P hP hI_le
    · have hM_le : 𝔪 ≤ P := pow_le_prime P hP_prime n hMn_le
      have hP_le : P ≤ 𝔪 := IsLocalRing.le_maximalIdeal hP_prime.ne_top
      exact hC_ne_max P hP (le_antisymm hP_le hM_le)
  have exists_avoid : ∀ P ∈ C, ∀ n : ℕ, ∃ z ∈ I * 𝔪 ^ n, z ∉ P :=
    fun P hP n => Set.not_subset.mp (key_sublemma P hP n)
  have hC_ne : C.Nonempty := Set.nonempty_iff_ne_empty.mpr hC_empty
  have hD_ne : D.Nonempty := Set.nonempty_iff_ne_empty.mpr hD_empty
  have hCD_nonempty : (C ×ˢ D).Nonempty := Set.Nonempty.prod hC_ne hD_ne
  obtain ⟨enum, henum⟩ := (hC_countable.prod hD_countable).exists_surjective hCD_nonempty
  let P_of : ℕ → Ideal T := fun n => (enum n).val.1
  let r_of : ℕ → T := fun n => (enum n).val.2
  have hP_mem : ∀ n, P_of n ∈ C := fun n => (Set.mem_prod.mp (enum n).property).1
  have hr_mem : ∀ n, r_of n ∈ D := fun n => (Set.mem_prod.mp (enum n).property).2
  -- Build the Cauchy sequence (u_n, q_n) using buildSeq
  let S := buildSeq I hC_prime hC_ne_max exists_avoid P_of r_of hP_mem
  let u_seq : ℕ → T := fun n => (S n).1
  let q_seq : ℕ → ℕ := fun n => (S n).2
  have hq_inc : ∀ n, q_seq (n + 1) ≥ q_seq n + 1 := fun n =>
    buildSeqQInc I hC_prime hC_ne_max exists_avoid P_of r_of hP_mem n
  have hq_ge : ∀ n, q_seq n ≥ n := by
    intro n
    induction n with
    | zero => exact Nat.zero_le _
    | succ k ih => have := hq_inc k
                   omega
  have hu_diff : ∀ n, u_seq (n + 1) - u_seq n ∈ 𝔪 ^ q_seq n :=
    fun n => Ideal.mul_le_left
      (buildSeqDiff I hC_prime hC_ne_max exists_avoid P_of r_of hP_mem n)
  have hu_mem : ∀ n, u_seq n ∈ I := by
    intro n
    induction n with
    | zero => exact I.zero_mem
    | succ k ih =>
      have : u_seq (k + 1) = u_seq k + (u_seq (k + 1) - u_seq k) := by ring
      rw [this]
      exact I.add_mem ih (Ideal.mul_le_right
        (buildSeqDiff I hC_prime hC_ne_max exists_avoid P_of r_of hP_mem k))
  have hu_avoids : ∀ n, u_seq (n + 1) ∉ (P_of n : Set T) + ({r_of n} : Set T) :=
    fun n => buildSeqAvoids I hC_prime hC_ne_max exists_avoid P_of r_of hP_mem n
  have hu_sep : ∀ n, ∀ m ∈ 𝔪 ^ q_seq (n + 1),
      u_seq (n + 1) + m ∉ (P_of n : Set T) + ({r_of n} : Set T) :=
    fun n => buildSeqSep I hC_prime hC_ne_max exists_avoid P_of r_of hP_mem n
  -- Cauchy property: u(b) - u(a) ∈ 𝔪^a for a ≤ b
  have hu_cauchy_telescope : ∀ a b, a ≤ b → u_seq b - u_seq a ∈ 𝔪 ^ a := by
    intro a b hab
    induction b with
    | zero => simp [show a = 0 from by omega]
    | succ k ih =>
      by_cases hak : a ≤ k
      · have : u_seq (k + 1) - u_seq a =
            (u_seq (k + 1) - u_seq k) + (u_seq k - u_seq a) := by ring
        rw [this]
        exact (𝔪 ^ a).add_mem
          (Ideal.pow_le_pow_right (by
                                     have := hq_ge k
                                     omega) (hu_diff k))
          (ih hak)
      · have : a = k + 1 := by omega
        subst this
        simp
  -- Cauchy property in SModEq form for IsPrecomplete
  have hu_smodEq : ∀ {a b : ℕ}, a ≤ b →
      u_seq a ≡ u_seq b [SMOD (𝔪 ^ a • ⊤ : Submodule T T)] := by
    intro a b hab
    rw [SModEq.sub_mem]
    simp only [smul_eq_mul, mul_top]
    have h := hu_cauchy_telescope a b hab
    rw [show u_seq a - u_seq b = -(u_seq b - u_seq a) from by ring]
    exact (𝔪 ^ a).neg_mem h
  -- Get the limit from IsPrecomplete
  have hpre : IsPrecomplete 𝔪 T := IsAdicComplete.toIsPrecomplete
  obtain ⟨L, hL⟩ := hpre.prec hu_smodEq
  have hL_diff : ∀ n, L - u_seq n ∈ 𝔪 ^ n := by
    intro n
    have := (hL n).symm
    rw [SModEq.sub_mem] at this
    simpa using this
  -- L ∈ I (by mem_of_mem_sup_pow)
  have hL_mem : L ∈ I := by
    apply mem_of_mem_sup_pow I L
    intro n
    rw [Submodule.mem_sup]
    exact ⟨u_seq n, hu_mem n, L - u_seq n, hL_diff n, by ring⟩
  -- L avoids all P_of(n) + {r_of(n)}
  have hL_avoids : ∀ n, L ∉ (P_of n : Set T) + ({r_of n} : Set T) := by
    intro n
    -- Stronger Cauchy: u(b) - u(a) ∈ 𝔪^{q_a}
    have hq_mono : ∀ a b, a ≤ b → q_seq a ≤ q_seq b := by
      intro a b hab
      induction b with
      | zero => simp [show a = 0 from by omega]
      | succ k ih =>
        by_cases hak : a ≤ k
        · exact le_trans (ih hak) (by
                                     have := hq_inc k
                                     omega)
        · exact le_of_eq (show q_seq a = q_seq (k + 1) by
                            congr 1
                            omega)
    have hu_cauchy_q : ∀ a b, a ≤ b → u_seq b - u_seq a ∈ 𝔪 ^ q_seq a := by
      intro a b hab
      induction b with
      | zero =>
        have ha : a = 0 := by omega
        subst ha
        simp [(𝔪 ^ q_seq 0).zero_mem]
      | succ k ih =>
        by_cases hak : a ≤ k
        · have heq : u_seq (k + 1) - u_seq a =
              (u_seq (k + 1) - u_seq k) + (u_seq k - u_seq a) := by ring
          rw [heq]
          exact (𝔪 ^ q_seq a).add_mem
            (Ideal.pow_le_pow_right (hq_mono a k hak) (hu_diff k))
            (ih hak)
        · have hak1 : a = k + 1 := by omega
          subst hak1
          simp [(𝔪 ^ q_seq (k + 1)).zero_mem]
    have hL_diff_q : L - u_seq (n + 1) ∈ 𝔪 ^ q_seq (n + 1) := by
      have : L - u_seq (n + 1) =
        (L - u_seq (q_seq (n + 1))) + (u_seq (q_seq (n + 1)) - u_seq (n + 1)) := by ring
      rw [this]
      exact (𝔪 ^ q_seq (n + 1)).add_mem
        (hL_diff (q_seq (n + 1)))
        (hu_cauchy_q (n + 1) (q_seq (n + 1)) (hq_ge (n + 1)))
    -- Apply separation
    have := hu_sep n (L - u_seq (n + 1)) hL_diff_q
    rwa [show u_seq (n + 1) + (L - u_seq (n + 1)) = L from by ring] at this
  exact ⟨L, hL_mem, fun P hP r hr => by
    obtain ⟨n, hn⟩ := henum ⟨(P, r), Set.mem_prod.mpr ⟨hP, hr⟩⟩
    have hPn : P_of n = P := congr_arg (·.val.1) hn
    have hrn : r_of n = r := congr_arg (·.val.2) hn
    rw [← hPn, ← hrn]
    exact hL_avoids n⟩

/-!
## Uncountable Avoidance (Heitmann Lemma 3)

If |C × D| < |T/M|, then I ⊄ ⋃{P + r | P ∈ C, r ∈ D}.
This is a cardinality argument using the fact that a vector space over a field k
cannot be covered by fewer than |k| proper subspaces.
-/

/-- Covering number argument: in a Noetherian local ring, if |C| < |T/M| and I ⊄ P
for all primes P ∈ C, then ∃ t ∈ I avoiding all P ∈ C.
Proof by induction on the number of generators of I. -/
lemma ideal_avoidance_of_card_lt_aux [IsNoetherianRing T] :
    ∀ (n : ℕ) (I : Ideal T) (C : Set (Ideal T)),
    (∀ P ∈ C, P.IsPrime) →
    Cardinal.mk C < Cardinal.mk (IsLocalRing.ResidueField T) →
    (∀ P ∈ C, ¬(I ≤ P)) →
    (∃ s : Finset T, Ideal.span (↑s : Set T) = I ∧ s.card ≤ n) →
    ∃ t ∈ I, ∀ P ∈ C, t ∉ P := by
  intro n
  induction n with
  | zero =>
    intro I C _ _ hI ⟨s, hs_eq, hs_card⟩
    rw [Finset.card_eq_zero.mp (Nat.le_zero.mp hs_card), Finset.coe_empty,
        Ideal.span_empty] at hs_eq
    subst hs_eq
    exact ⟨0, (⊥ : Ideal T).zero_mem, fun P hP => absurd bot_le (hI P hP)⟩
  | succ k ih =>
    intro I C hC_prime hC_card hI ⟨s, hs_eq, hs_card⟩
    by_cases hs_ne : s.Nonempty
    swap
    · rw [Finset.not_nonempty_iff_eq_empty.mp hs_ne, Finset.coe_empty,
          Ideal.span_empty] at hs_eq
      subst hs_eq
      exact ⟨0, (⊥ : Ideal T).zero_mem, fun P hP => absurd bot_le (hI P hP)⟩
    obtain ⟨g, hg⟩ := hs_ne
    have hg_mem : g ∈ I := hs_eq ▸ Ideal.subset_span (Finset.mem_coe.mpr hg)
    by_cases hg_good : ∀ P ∈ C, g ∉ (P : Set T)
    · exact ⟨g, hg_mem, hg_good⟩
    push Not at hg_good
    set S_bad := C ∩ {P | g ∈ (P : Set T)}
    set J := Ideal.span (↑(s.erase g) : Set T)
    have hJ_le_I : J ≤ I :=
      hs_eq ▸ Ideal.span_mono (Finset.coe_subset.mpr (Finset.erase_subset g s))
    -- For P ∈ S_bad: g ∈ P and I ⊄ P, so span(s \ {g}) ⊄ P
    have hJ_notI : ∀ P ∈ S_bad, ¬(J ≤ P) := by
      intro P ⟨hPC, hgP⟩ hJP
      apply hI P hPC
      rw [← hs_eq]
      exact Ideal.span_le.mpr fun x hx => by
        rw [Finset.mem_coe] at hx
        by_cases hxg : x = g
        · subst hxg
          exact hgP
        · exact hJP (Ideal.subset_span
            (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hxg, hx⟩)))
    have hS_card : Cardinal.mk S_bad < Cardinal.mk (IsLocalRing.ResidueField T) :=
      lt_of_le_of_lt (Cardinal.mk_le_mk_of_subset Set.inter_subset_left) hC_card
    obtain ⟨s_elem, hs_mem, hs_avoid⟩ := ih J S_bad
      (fun P ⟨hPC, _⟩ => hC_prime P hPC) hS_card hJ_notI
      ⟨s.erase g, rfl, by rw [Finset.card_erase_of_mem hg]
                          omega⟩
    have hs_in_I : s_elem ∈ I := hJ_le_I hs_mem
    -- Line argument: for each P ∈ C, at most one residue class of a puts g + a*s_elem ∈ P
    let forbidden : ↑C → IsLocalRing.ResidueField T :=
      fun ⟨P, _⟩ => if h : ∃ a : T, g + a * s_elem ∈ (P : Ideal T)
        then (Ideal.Quotient.mk (IsLocalRing.maximalIdeal T)) h.choose else 0
    have h_range : Cardinal.mk (Set.range forbidden) <
        Cardinal.mk (IsLocalRing.ResidueField T) :=
      lt_of_le_of_lt Cardinal.mk_range_le hC_card
    obtain ⟨a₀_bar, ha₀⟩ :
        ∃ z : IsLocalRing.ResidueField T, z ∉ Set.range forbidden := by
      by_contra hall
      push Not at hall
      exact absurd (Cardinal.mk_univ ▸ (Set.eq_univ_of_forall hall ▸ h_range)) (lt_irrefl _)
    obtain ⟨a₀, rfl⟩ := Ideal.Quotient.mk_surjective a₀_bar
    refine ⟨g + a₀ * s_elem, I.add_mem hg_mem (I.mul_mem_left a₀ hs_in_I),
      fun P hP hmem => ?_⟩
    -- s_elem ∉ P: if s_elem ∈ P then g ∈ P, so P ∈ S_bad, contradicting hs_avoid
    have hsP : s_elem ∉ (P : Set T) := by
      intro hsP
      have hgP : g ∈ (P : Ideal T) := by
        have := P.sub_mem hmem (P.mul_mem_left a₀ hsP)
        rwa [show g + a₀ * s_elem - a₀ * s_elem = g from by ring] at this
      exact hs_avoid P ⟨hP, SetLike.mem_coe.mpr hgP⟩ hsP
    apply ha₀
    refine ⟨⟨P, hP⟩, ?_⟩
    simp only [forbidden]
    rw [dif_pos ⟨a₀, hmem⟩]
    have hex := (⟨a₀, hmem⟩ : ∃ a : T, g + a * s_elem ∈ (P : Ideal T))
    have hdiff : (hex.choose - a₀) * s_elem ∈ (P : Ideal T) := by
      have := P.sub_mem hex.choose_spec hmem
      rwa [show g + hex.choose * s_elem - (g + a₀ * s_elem) =
        (hex.choose - a₀) * s_elem from by ring] at this
    have hsub : hex.choose - a₀ ∈ IsLocalRing.maximalIdeal T :=
      IsLocalRing.le_maximalIdeal (hC_prime P hP).ne_top
        (((hC_prime P hP).mem_or_mem hdiff).resolve_right hsP)
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem hex.choose a₀).mpr hsub

/-- Wrapper: in a Noetherian local ring, |C| < |T/M| and I ⊄ P
implies ∃ t ∈ I, t ∉ P for all P. -/
lemma ideal_avoidance_of_card_lt [IsNoetherianRing T]
    (I : Ideal T) (C : Set (Ideal T)) (hC_prime : ∀ P ∈ C, P.IsPrime)
    (hC_card : Cardinal.mk C < Cardinal.mk (IsLocalRing.ResidueField T))
    (hI : ∀ P ∈ C, ¬(I ≤ P)) :
    ∃ t ∈ I, ∀ P ∈ C, t ∉ P := by
  obtain ⟨s, hs⟩ := IsNoetherian.noetherian I
  exact ideal_avoidance_of_card_lt_aux s.card I C hC_prime hC_card hI ⟨s, hs, le_rfl⟩

/-- Heitmann Lemma 3: Uncountable avoidance.
If the product |C × D| has cardinality strictly less than |T/M|,
and I is not contained in any P ∈ C, then there exists u ∈ I
avoiding all translates P + r. -/
theorem uncountable_avoidance [IsNoetherianRing T]
    {C : Set (Ideal T)} (hC_prime : ∀ P ∈ C, P.IsPrime)
    {D : Set T}
    (hcard : Cardinal.mk (C × D) < Cardinal.mk (IsLocalRing.ResidueField T))
    {I : Ideal T} (hI : ∀ P ∈ C, ¬(I ≤ P)) :
    ∃ u ∈ I, ∀ P ∈ C, ∀ r ∈ D, (u : T) ∉ (P : Set T) + ({r} : Set T) := by
  classical
  -- Trivial cases
  by_cases hCne : C.Nonempty
  swap
  · rw [Set.not_nonempty_iff_eq_empty] at hCne
    exact ⟨0, I.zero_mem, fun P hP => absurd hP (hCne ▸ fun a => a.elim)⟩
  by_cases hDne : D.Nonempty
  swap
  · rw [Set.not_nonempty_iff_eq_empty] at hDne
    exact ⟨0, I.zero_mem, fun _ _ r hr => absurd hr (hDne ▸ fun a => a.elim)⟩
  -- Step 1: Find t ∈ I not in any P ∈ C
  have hC_card : Cardinal.mk C < Cardinal.mk (IsLocalRing.ResidueField T) := by
    obtain ⟨d, hd⟩ := hDne
    exact lt_of_le_of_lt
      (Cardinal.mk_le_of_injective (f := fun (c : ↑C) => ((c, ⟨d, hd⟩) : ↑C × ↑D))
        (fun _ _ h => congr_arg Prod.fst h)) hcard
  obtain ⟨t, ht_mem, ht_avoid⟩ : ∃ t ∈ I, ∀ P ∈ C, t ∉ P := by
    by_cases hfin : C.Finite
    · -- Finite C: standard prime avoidance
      by_contra h
      push Not at h
      have hsub : (I : Set T) ⊆ ⋃ P ∈ C, (P : Set T) :=
        fun t ht => let ⟨P, hP, htP⟩ := h t ht
        Set.mem_biUnion hP htP
      rw [Ideal.subset_union_prime_finite hfin (⊥ : Ideal T) ⊥
        (fun P hP _ _ => hC_prime P hP)] at hsub
      obtain ⟨P, hP, hle⟩ := hsub
      exact hI P hP hle
    · -- Infinite C: line argument
      obtain ⟨P₀, hP₀⟩ := hCne
      obtain ⟨v, hv_mem, hv_not⟩ := Set.not_subset.mp (hI P₀ hP₀)
      by_cases hvall : ∀ P ∈ C, v ∉ P
      · exact ⟨v, hv_mem, hvall⟩
      · push Not at hvall
        obtain ⟨Q₀, hQ₀, hv_in_Q⟩ := hvall
        obtain ⟨w, hw_mem, hw_not⟩ := Set.not_subset.mp (hI Q₀ hQ₀)
        -- Split on whether {P ∈ C | v ∈ P} is finite
        by_cases hCv_fin : (C ∩ {P | (v : T) ∈ (P : Set T)}).Finite
        · -- Finite Cv: find w' ∈ I avoiding all P ∈ Cv via prime avoidance
          obtain ⟨w', hw'_mem, hw'_avoid⟩ :
              ∃ w' ∈ I, ∀ P ∈ C, (v : T) ∈ (P : Set T) → w' ∉ (P : Set T) := by
            by_contra hall
            push Not at hall
            have hsub : (I : Set T) ⊆
                ⋃ P ∈ (C ∩ {P | (v : T) ∈ (P : Set T)}), (P : Set T) := by
              intro t ht
              obtain ⟨P, hPC, hvP, htP⟩ := hall t ht
              exact Set.mem_biUnion (Set.mem_inter hPC hvP) htP
            rw [Ideal.subset_union_prime_finite hCv_fin (⊥ : Ideal T) ⊥
              (fun P hP _ _ => hC_prime P (Set.mem_of_mem_inter_left hP))] at hsub
            obtain ⟨P, hP, hle⟩ := hsub
            exact hI P (Set.mem_of_mem_inter_left hP) hle
          let π := Ideal.Quotient.mk (IsLocalRing.maximalIdeal T)
          let g : ↑C → IsLocalRing.ResidueField T := fun ⟨P, _⟩ =>
            if h : ∃ a : T, v + a * w' ∈ (P : Ideal T) then π h.choose else 0
          have hg_range : Cardinal.mk (Set.range g) <
              Cardinal.mk (IsLocalRing.ResidueField T) :=
            lt_of_le_of_lt Cardinal.mk_range_le hC_card
          obtain ⟨y_bar, hy_bar⟩ : ∃ z : IsLocalRing.ResidueField T, z ∉ Set.range g := by
            by_contra hall
            push Not at hall
            exact absurd (Cardinal.mk_univ ▸ (Set.eq_univ_of_forall hall ▸ hg_range))
              (lt_irrefl _)
          obtain ⟨a₀, rfl⟩ := Ideal.Quotient.mk_surjective y_bar
          refine ⟨v + a₀ * w', I.add_mem hv_mem (I.mul_mem_left a₀ hw'_mem),
            fun P hP hmem => ?_⟩
          by_cases hw'P : (w' : T) ∈ (P : Set T)
          · -- w' ∈ P: contradicts hw'_avoid since v + a₀w' ∈ P implies v ∈ P
            have hv_in_P : (v : T) ∈ (P : Ideal T) := by
              have := P.sub_mem hmem (P.mul_mem_left a₀ hw'P)
              rwa [show v + a₀ * w' - a₀ * w' = v from by ring] at this
            exact hw'_avoid P hP hv_in_P hw'P
          · apply hy_bar
            refine ⟨⟨P, hP⟩, ?_⟩
            change g ⟨P, hP⟩ = π a₀
            simp only [g]
            rw [dif_pos ⟨a₀, hmem⟩]
            have hex : ∃ a : T, v + a * w' ∈ (P : Ideal T) := ⟨a₀, hmem⟩
            have hdiff : (hex.choose - a₀) * w' ∈ (P : Ideal T) := by
              have := P.sub_mem hex.choose_spec hmem
              rwa [show v + hex.choose * w' - (v + a₀ * w') =
                (hex.choose - a₀) * w' from by ring] at this
            have hsub : hex.choose - a₀ ∈ IsLocalRing.maximalIdeal T :=
              IsLocalRing.le_maximalIdeal (hC_prime P hP).ne_top
                (((hC_prime P hP).mem_or_mem hdiff).resolve_right hw'P)
            change (Ideal.Quotient.mk (IsLocalRing.maximalIdeal T)) hex.choose =
              (Ideal.Quotient.mk (IsLocalRing.maximalIdeal T)) a₀
            rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
            exact hsub
        · exact ideal_avoidance_of_card_lt I C hC_prime hC_card hI
  -- Step 2: For each (P, r) ∈ C × D, compute the unique forbidden residue class
  let π := Ideal.Quotient.mk (IsLocalRing.maximalIdeal T)
  let f : ↑C × ↑D → IsLocalRing.ResidueField T := fun ⟨⟨P, _⟩, ⟨r, _⟩⟩ =>
    if h : ∃ x : T, t * x - r ∈ (P : Ideal T) then π (Classical.choose h) else 0
  -- Step 3: |range f| ≤ |C × D| < |T/M|, so pick y ∉ range f.
  have h_range_small : Cardinal.mk (Set.range f) < Cardinal.mk (IsLocalRing.ResidueField T) :=
    lt_of_le_of_lt mk_range_le hcard
  obtain ⟨y_bar, hy_bar⟩ : ∃ z : IsLocalRing.ResidueField T, z ∉ Set.range f := by
    by_contra hall
    push Not at hall
    exact absurd (Cardinal.mk_univ ▸ (Set.eq_univ_of_forall hall ▸ h_range_small)) (lt_irrefl _)
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y_bar
  -- Step 4: u = ty ∈ I and avoids all P + {r}.
  refine ⟨t * y, I.mul_mem_right y ht_mem, fun P hP r hr hmem => ?_⟩
  have hmem' : t * y - r ∈ P := mem_sub_of_mem_add_singleton hmem
  apply hy_bar
  refine ⟨⟨⟨P, hP⟩, ⟨r, hr⟩⟩, ?_⟩
  change (if h : ∃ x, t * x - r ∈ (P : Ideal T) then π (Classical.choose h) else 0) = π y
  rw [dif_pos ⟨y, hmem'⟩]
  -- Uniqueness: t(x₀ - y) ∈ P with t ∉ P gives x₀ - y ∈ P ⊆ M
  let hex : ∃ x : T, t * x - r ∈ (P : Ideal T) := ⟨y, hmem'⟩
  have hx₀ : t * Classical.choose hex - r ∈ P := Classical.choose_spec hex
  change π (Classical.choose hex) = π y
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  have hmul : t * (Classical.choose hex - y) ∈ P := by
    have := P.sub_mem hx₀ hmem'
    rwa [show t * Classical.choose hex - r - (t * y - r) = t * (Classical.choose hex - y)
      by ring] at this
  exact IsLocalRing.le_maximalIdeal (hC_prime P hP).ne_top
    (((hC_prime P hP).mem_or_mem hmul).resolve_left (ht_avoid P hP))

/-- Combined avoidance: works for both countable and uncountable residue fields.
If C is a finite or countable set of primes (M ∉ C) and D is appropriately bounded,
find u ∈ I avoiding all P + r. -/
theorem avoidance
    [IsAdicComplete (IsLocalRing.maximalIdeal T) T]
    [IsNoetherianRing T]
    {C : Set (Ideal T)} (hC_prime : ∀ P ∈ C, P.IsPrime)
    (hC_ne_max : ∀ P ∈ C, P ≠ IsLocalRing.maximalIdeal T)
    {D : Set T}
    (hCD_bound : Cardinal.mk (C × D) < Cardinal.mk (IsLocalRing.ResidueField T) ∨
      (C.Countable ∧ D.Countable))
    {I : Ideal T} (hI : ∀ P ∈ C, ¬(I ≤ P)) :
    ∃ u ∈ I, ∀ P ∈ C, ∀ r ∈ D, (u : T) ∉ (P : Set T) + ({r} : Set T) := by
  rcases hCD_bound with h | ⟨hC_count, hD_count⟩
  · exact uncountable_avoidance hC_prime h hI
  · letI : TopologicalSpace T := (IsLocalRing.maximalIdeal T).adicTopology
    have _ : IsTopologicalRing T := inferInstance
    exact countable_avoidance hC_count hC_prime hC_ne_max hD_count hI

end
