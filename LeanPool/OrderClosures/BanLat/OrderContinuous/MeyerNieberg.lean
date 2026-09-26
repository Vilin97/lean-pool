/-
Copyright (c) 2026 David Muñoz-Lahoz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Muñoz-Lahoz
-/

module

public import LeanPool.OrderClosures.BanLat.OrderContinuous.Nakano
public import LeanPool.OrderClosures.BanLat.Disjoint


/-!
# Meyer-Nieberg theorem

A Banach lattice has an order continuous norm iff every order-bounded
pairwise disjoint sequence converges to zero in norm. As a corollary, in
an order continuous Banach lattice every order-bounded set of pairwise
disjoint non-zero elements is at most countable.
-/

@[expose] public section

variable {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]

section Disjointification

variable {E : Type*} [AddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]
  [VectorLattice E]

/-- A sequence is `k`-disjoint if every `k`-element finite subfamily has
infimum of moduli equal to zero. -/
private def IsKDisjointSeq (k : ℕ) (u : ℕ → E) : Prop :=
  ∀ s : Finset ℕ, s.card = k → ∀ hs : s.Nonempty,
    s.inf' hs (fun n => |u n|) = 0

omit [Lattice E] [IsOrderedAddMonoid E] [VectorLattice E] in
private lemma sum_range_increments (u : ℕ → E) :
    ∀ n : ℕ, (∑ i ∈ Finset.range n, (u (i + 1) - u i)) = u n - u 0 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      rw [ih]
      abel

omit [VectorLattice E] in
private lemma finset_sum_increments_le_bound {x : E} {u : ℕ → E}
    (h0 : ∀ n, 0 ≤ u n) (hmono : Monotone u) (hle : ∀ n, u n ≤ x)
    (s : Finset ℕ) :
    (∑ i ∈ s, (u (i + 1) - u i)) ≤ x := by
  classical
  let N : ℕ := s.sup id + 1
  have hsub : s ⊆ Finset.range N := by
    intro i hi
    have hi_le : i ≤ s.sup id := by
      simpa using (Finset.le_sup (f := id) hi)
    simpa [N] using Nat.lt_succ_of_le hi_le
  have hnonneg : ∀ i ∈ Finset.range N, i ∉ s → 0 ≤ u (i + 1) - u i := by
    intro i _ _
    exact sub_nonneg.mpr (hmono (Nat.le_succ i))
  calc
    (∑ i ∈ s, (u (i + 1) - u i)) ≤
        ∑ i ∈ Finset.range N, (u (i + 1) - u i) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg
    _ = u N - u 0 := sum_range_increments u N
    _ ≤ u N := sub_le_self _ (h0 0)
    _ ≤ x := hle N

omit [VectorLattice E] in
private lemma isVLDisjoint_finset_sum_local {ι : Type*} {s : Finset ι} {x : E}
    {f : ι → E} (h : ∀ i ∈ s, IsVLDisjoint x (f i)) :
    IsVLDisjoint x (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isVLDisjoint_zero_right x
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      refine (h a (Finset.mem_insert_self a s)).add_right ?_
      exact ih (fun i hi => h i (Finset.mem_insert_of_mem hi))

omit [VectorLattice E] in
private lemma sum_range_mono_of_nonneg {f : ℕ → E} (hf : ∀ n, 0 ≤ f n) :
    Monotone fun n => ∑ i ∈ Finset.range n, f i := by
  intro n m hnm
  exact Finset.sum_le_sum_of_subset_of_nonneg ((Finset.range_subset_range).2 hnm)
    (fun i _ _ => hf i)

/-- First disjointification step: replace the increments of an increasing
bounded sequence by a `(k + 1)`-disjoint sequence up to an error
`1 / (k + 1)` times the bound. -/
private theorem disjointification_step_one {x : E} {u : ℕ → E}
    (h0 : ∀ n, 0 ≤ u n) (hmono : Monotone u) (hle : ∀ n, u n ≤ x) (k : ℕ) :
    ∃ v : ℕ → E,
      IsKDisjointSeq (k + 1) v ∧
      (∀ n, v n ∈ Set.Icc (0 : E) x) ∧
      ∀ n, v n ≤ u (n + 1) - u n ∧
        u (n + 1) - u n ≤ v n + ((1 : ℝ) / ((k : ℝ) + 1)) • x := by
  classical
  let c : ℝ := (1 : ℝ) / ((k : ℝ) + 1)
  let d : ℕ → E := fun n => u (n + 1) - u n
  let v : ℕ → E := fun n => (d n - c • x)⁺
  have hx0 : 0 ≤ x := (h0 0).trans (hle 0)
  have hc0 : 0 ≤ c := by
    dsimp [c]
    positivity
  have hcx0 : 0 ≤ c • x := smul_nonneg hc0 hx0
  have hd0 : ∀ n, 0 ≤ d n := fun n => sub_nonneg.mpr (hmono (Nat.le_succ n))
  refine ⟨v, ?_, ?_, ?_⟩
  · intro s hcard hs
    have hv_nonneg : ∀ n, 0 ≤ v n := fun n => posPart_nonneg _
    have hv_abs : ∀ n, |v n| = v n := fun n => abs_of_nonneg (hv_nonneg n)
    rw [show s.inf' hs (fun n => |v n|) = s.inf' hs v by
      apply Finset.inf'_congr hs rfl
      intro n _
      exact hv_abs n]
    let a : E := s.inf' hs v
    let r : ℕ → E := fun n => (d n - c • x)⁻
    have ha0 : 0 ≤ a := Finset.le_inf' hs v (fun n _ => hv_nonneg n)
    have ha_le : ∀ n ∈ s, a ≤ v n := fun n hn => Finset.inf'_le v hn
    have hr_nonneg : ∀ n, 0 ≤ r n := fun n => negPart_nonneg _
    have hdisj_each : ∀ n ∈ s, IsVLDisjoint a (r n) := by
      intro n hn
      have hbase : IsVLDisjoint (v n) (r n) := by
        simpa only [v, r] using isVLDisjoint_posPart_negPart (d n - c • x)
      refine hbase.mono_left ?_
      rw [abs_of_nonneg ha0, abs_of_nonneg (hv_nonneg n)]
      exact ha_le n hn
    have hdisj_sum : IsVLDisjoint a (∑ n ∈ s, r n) :=
      isVLDisjoint_finset_sum_local hdisj_each
    have hmeet_zero : a ⊓ (∑ n ∈ s, r n) = 0 :=
      inf_eq_zero_of_isVLDisjoint ha0 (Finset.sum_nonneg (fun n _ => hr_nonneg n))
        hdisj_sum
    have hsumd_le : (∑ n ∈ s, d n) ≤ x :=
      finset_sum_increments_le_bound h0 hmono hle s
    have hxd_nonneg : 0 ≤ x - ∑ n ∈ s, d n := sub_nonneg.mpr hsumd_le
    have hsumv_ge : a ≤ ∑ n ∈ s, v n := by
      rcases hs with ⟨n, hn⟩
      exact (ha_le n hn).trans (Finset.single_le_sum (fun i _ => hv_nonneg i) hn)
    have hr_eq : ∀ n, r n = c • x - d n + v n := by
      intro n
      have hdec : v n - r n = d n - c • x := by
        simp [v, r, posPart_sub_negPart]
      have h1 : v n = d n - c • x + r n := sub_eq_iff_eq_add.mp hdec
      rw [h1]
      abel
    have hsumr_eq : (∑ n ∈ s, r n) = (x - ∑ n ∈ s, d n) + ∑ n ∈ s, v n := by
      calc
        (∑ n ∈ s, r n) = ∑ n ∈ s, (c • x - d n + v n) := by
          refine Finset.sum_congr rfl ?_
          intro n _
          exact hr_eq n
        _ = (∑ n ∈ s, c • x) - (∑ n ∈ s, d n) + ∑ n ∈ s, v n := by
          simp [Finset.sum_add_distrib, Finset.sum_sub_distrib]
        _ = x - (∑ n ∈ s, d n) + ∑ n ∈ s, v n := by
          have hcard_real : (s.card : ℝ) = (k : ℝ) + 1 := by
            norm_num [hcard]
          rw [Finset.sum_const]
          rw [← Nat.cast_smul_eq_nsmul ℝ s.card (c • x)]
          rw [smul_smul, hcard_real]
          have hcoef : ((k : ℝ) + 1) * c = 1 := by
            dsimp [c]
            field_simp [show (k : ℝ) + 1 ≠ 0 by positivity]
          rw [hcoef, one_smul]
    have ha_le_sumr : a ≤ ∑ n ∈ s, r n := by
      rw [hsumr_eq]
      exact hsumv_ge.trans (le_add_of_nonneg_left hxd_nonneg)
    have ha_eq_zero : a = 0 := by
      have : a ⊓ (∑ n ∈ s, r n) = a := inf_eq_left.mpr ha_le_sumr
      exact this ▸ hmeet_zero
    exact ha_eq_zero
  · intro n
    constructor
    · exact posPart_nonneg _
    · have hv_le_d : v n ≤ d n := by
        refine sup_le ?_ (hd0 n)
        exact sub_le_self _ hcx0
      exact hv_le_d.trans ((sub_le_self _ (h0 n)).trans (hle (n + 1)))
  · intro n
    constructor
    · have hv_le_d : v n ≤ d n := by
        refine sup_le ?_ (hd0 n)
        exact sub_le_self _ hcx0
      simpa [d, v] using hv_le_d
    · have : d n ≤ v n + c • x := sub_le_iff_le_add.mp (le_posPart (d n - c • x))
      simpa [d, v, c] using this

/-- Second disjointification step: split a `(k + 1)`-disjoint sequence into
one disjoint sequence and a `k`-disjoint remainder, up to an arbitrarily small
positive multiple of the bound. -/
private theorem disjointification_step_two {x : E} {u : ℕ → E} {k : ℕ}
    (hk : 1 < k) (hu_interval : ∀ n, u n ∈ Set.Icc (0 : E) x)
    (hu_disj : IsKDisjointSeq (k + 1) u) {eps : ℝ}
    (heps0 : 0 < eps) (heps1 : eps < 1) :
    ∃ w y : ℕ → E,
      IsKDisjointSeq k w ∧
      Pairwise (fun n m => IsVLDisjoint (y n) (y m)) ∧
      (∀ n, w n ∈ Set.Icc (0 : E) x) ∧
      (∀ n, y n ∈ Set.Icc (0 : E) x) ∧
      ∀ n, y n + w n ≤ u n ∧ u n ≤ y n + w n + eps • x := by
  classical
  have _hk_pos : 0 < k := by omega
  let pref : ℕ → E := fun n => ∑ i ∈ Finset.range n, u i
  let inv : ℝ := eps⁻¹
  let y : ℕ → E := fun n => (u n - inv • pref n - eps • x)⁺
  let w : ℕ → E := fun n => u n ⊓ inv • pref n
  have hx0 : 0 ≤ x := (hu_interval 0).1.trans (hu_interval 0).2
  have hu0 : ∀ n, 0 ≤ u n := fun n => (hu_interval n).1
  have hux : ∀ n, u n ≤ x := fun n => (hu_interval n).2
  have heps_nonneg : 0 ≤ eps := le_of_lt heps0
  have heps_ne : eps ≠ 0 := ne_of_gt heps0
  have hinv0 : 0 ≤ inv := by
    dsimp [inv]
    exact inv_nonneg.mpr heps_nonneg
  have hpref0 : ∀ n, 0 ≤ pref n := fun n => Finset.sum_nonneg (fun i _ => hu0 i)
  have hpref_mono : Monotone pref := by
    dsimp [pref]
    exact sum_range_mono_of_nonneg hu0
  have hinvpref0 : ∀ n, 0 ≤ inv • pref n := fun n => smul_nonneg hinv0 (hpref0 n)
  have hepsx0 : 0 ≤ eps • x := smul_nonneg heps_nonneg hx0
  have hy0 : ∀ n, 0 ≤ y n := fun n => posPart_nonneg _
  refine ⟨w, y, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hcard hs
    have hw_nonneg : ∀ n, 0 ≤ w n := fun n => le_inf (hu0 n) (hinvpref0 n)
    rw [show s.inf' hs (fun n => |w n|) = s.inf' hs w by
      apply Finset.inf'_congr hs rfl
      intro n _
      exact abs_of_nonneg (hw_nonneg n)]
    let a : E := s.inf' hs w
    let b : E := s.inf' hs u
    let n0 : ℕ := s.min' hs
    have hn0_mem : n0 ∈ s := by
      simpa [n0] using Finset.min'_mem s hs
    have ha0 : 0 ≤ a := Finset.le_inf' hs w (fun n _ => hw_nonneg n)
    have hb0 : 0 ≤ b := Finset.le_inf' hs u (fun n _ => hu0 n)
    have ha_le_w : ∀ n ∈ s, a ≤ w n := fun n hn => Finset.inf'_le w hn
    have ha_le_b : a ≤ b := by
      refine Finset.le_inf' hs u ?_
      intro n hn
      exact (ha_le_w n hn).trans inf_le_left
    have ha_le_pref : a ≤ inv • pref n0 := (ha_le_w n0 hn0_mem).trans inf_le_right
    have hb_disj_u_before : ∀ i ∈ Finset.range n0, IsVLDisjoint b (u i) := by
      intro i hi
      have hi_lt : i < n0 := by simpa using hi
      have hi_not : i ∉ s := by
        intro his
        exact (Nat.not_lt_of_ge (Finset.min'_le s i his)) hi_lt
      have hcard_insert : (insert i s).card = k + 1 := by
        simp [hi_not, hcard]
      have hne_insert : (insert i s : Finset ℕ).Nonempty :=
        ⟨i, Finset.mem_insert_self i s⟩
      have hinf := hu_disj (insert i s) hcard_insert hne_insert
      have hinf_eq : (insert i s).inf' hne_insert (fun j => |u j|) = u i ⊓ b := by
        rw [Finset.inf'_insert hs]
        rw [abs_of_nonneg (hu0 i)]
        congr 1
        apply Finset.inf'_congr hs rfl
        intro j _
        exact abs_of_nonneg (hu0 j)
      have hbi_zero : b ⊓ u i = 0 := by
        rw [hinf_eq] at hinf
        rwa [inf_comm] at hinf
      exact isVLDisjoint_of_inf_eq_zero hbi_zero
    have hb_disj_pref : IsVLDisjoint b (pref n0) := by
      simpa [pref] using isVLDisjoint_finset_sum_local hb_disj_u_before
    have hb_disj_invpref : IsVLDisjoint b (inv • pref n0) := hb_disj_pref.smul_right inv
    have ha_disj_invpref : IsVLDisjoint a (inv • pref n0) := by
      refine hb_disj_invpref.mono_left ?_
      rw [abs_of_nonneg ha0, abs_of_nonneg hb0]
      exact ha_le_b
    have ha_inf_zero : a ⊓ inv • pref n0 = 0 :=
      inf_eq_zero_of_isVLDisjoint ha0 (hinvpref0 n0) ha_disj_invpref
    have ha_eq_zero : a = 0 := by
      have : a ⊓ inv • pref n0 = a := inf_eq_left.mpr ha_le_pref
      exact this ▸ ha_inf_zero
    exact ha_eq_zero
  · have hdisj_gt : ∀ {n m : ℕ}, n < m → IsVLDisjoint (y m) (y n) := by
      intro n m hnm
      have hnm_succ : n + 1 ≤ m := Nat.succ_le_iff.mpr hnm
      have hpref_succ : pref (n + 1) = pref n + u n := by
        simp [pref, Finset.sum_range_succ]
      have hpref_nu_le_m : pref n + u n ≤ pref m := by
        rw [← hpref_succ]
        exact hpref_mono hnm_succ
      have hscale_y : eps • y m = (eps • u m - pref m - (eps * eps) • x)⁺ := by
        rw [← posPart_smul_nonneg heps_nonneg]
        congr 1
        rw [smul_sub, smul_sub, smul_smul, smul_smul]
        rw [show eps * inv = 1 by dsimp [inv]; exact mul_inv_cancel₀ heps_ne, one_smul]
      have harg_le₁ : eps • u m - pref m - (eps * eps) • x ≤
          eps • x - pref n - u n := by
        calc
          eps • u m - pref m - (eps * eps) • x ≤ eps • x - (pref n + u n) - 0 := by
            gcongr
            · exact hux m
            · exact smul_nonneg (mul_nonneg heps_nonneg heps_nonneg) hx0
          _ = eps • x - pref n - u n := by abel
      have hle₁ : eps • y m ≤ (eps • x - pref n - u n)⁺ := by
        rw [hscale_y]
        exact posPart_mono harg_le₁
      have hneg_pref_le : -pref n ≤ inv • pref n := by
        calc
          -pref n = (-1 : ℝ) • pref n := by simp
          _ ≤ inv • pref n := smul_le_smul_of_nonneg_right
            (by linarith : (-1 : ℝ) ≤ inv) (hpref0 n)
      have harg_le₂ : eps • x - pref n - u n ≤ inv • pref n + eps • x - u n := by
        calc
          eps • x - pref n - u n = eps • x + -pref n - u n := by abel
          _ ≤ eps • x + inv • pref n - u n := by
            gcongr
          _ = inv • pref n + eps • x - u n := by abel
      have hle₂ : eps • y m ≤ (inv • pref n + eps • x - u n)⁺ :=
        hle₁.trans (posPart_mono harg_le₂)
      have hneg_eq : (inv • pref n + eps • x - u n)⁺ =
          (u n - inv • pref n - eps • x)⁻ := by
        rw [negPart_def]
        congr 1
        abel
      have hbound : eps • y m ≤ (u n - inv • pref n - eps • x)⁻ := by
        rwa [hneg_eq] at hle₂
      have hbase : IsVLDisjoint (u n - inv • pref n - eps • x)⁻ (y n) := by
        exact isVLDisjoint_comm.mp (by
          simpa only [y] using isVLDisjoint_posPart_negPart
            (u n - inv • pref n - eps • x))
      have hscaled : IsVLDisjoint (eps • y m) (y n) := by
        refine hbase.mono_left ?_
        rw [abs_of_nonneg (smul_nonneg heps_nonneg (hy0 m)),
          abs_of_nonneg (negPart_nonneg (u n - inv • pref n - eps • x))]
        exact hbound
      have hres := hscaled.smul_left inv
      simpa [inv, smul_smul, heps_ne] using hres
    intro n m hnm
    rcases Nat.lt_or_gt_of_ne hnm with hlt | hgt
    · exact isVLDisjoint_comm.mp (hdisj_gt hlt)
    · exact hdisj_gt hgt
  · intro n
    constructor
    · exact le_inf (hu0 n) (hinvpref0 n)
    · exact inf_le_left.trans (hux n)
  · intro n
    constructor
    · exact hy0 n
    · have hy_le_u : y n ≤ u n := by
        refine sup_le ?_ (hu0 n)
        exact (sub_le_self _ hepsx0).trans (sub_le_self _ (hinvpref0 n))
      exact hy_le_u.trans (hux n)
  · intro n
    let p : E := inv • pref n
    let e : E := eps • x
    have hp0 : 0 ≤ p := hinvpref0 n
    have he0 : 0 ≤ e := hepsx0
    have hy_eq : y n = u n - u n ⊓ (p + e) := by
      rw [sub_inf_eq_posPart]
      simp [y, p, e]
      abel_nf
    have hdecomp : y n + u n ⊓ (p + e) = u n := by
      rw [hy_eq]
      abel
    constructor
    · calc
        y n + w n ≤ y n + u n ⊓ (p + e) := by
          gcongr
          exact inf_le_inf_left (u n) (le_add_of_nonneg_right he0)
        _ = u n := hdecomp
    · have hinf_le : u n ⊓ (p + e) ≤ w n + e := by
        calc
          u n ⊓ (p + e) ≤ u n ⊓ p + u n ⊓ e :=
            inf_le_inf_add_inf_of_nonneg (u n) p e (hu0 n) hp0 he0
          _ ≤ w n + e := by
            gcongr
            exact inf_le_right
      calc
        u n = y n + u n ⊓ (p + e) := hdecomp.symm
        _ ≤ y n + (w n + e) := by gcongr
        _ = y n + w n + eps • x := by simp [e]; abel

omit [IsOrderedAddMonoid E] [VectorLattice E] in
private lemma pairwise_of_isKDisjointSeq_two {u : ℕ → E}
    (hu : IsKDisjointSeq 2 u) :
    Pairwise fun n m => IsVLDisjoint (u n) (u m) := by
  intro n m hnm
  have hcard : ({n, m} : Finset ℕ).card = 2 := by simp [hnm]
  have hne : ({n, m} : Finset ℕ).Nonempty := ⟨n, by simp⟩
  have hinf := hu ({n, m} : Finset ℕ) hcard hne
  simpa [IsVLDisjoint, hnm, inf_comm] using hinf

private theorem split_isKDisjointSeq {x : E} :
    ∀ {k : ℕ} {u : ℕ → E}, 0 < k →
      (∀ n, u n ∈ Set.Icc (0 : E) x) → IsKDisjointSeq (k + 1) u →
      ∀ {eps : ℝ}, 0 < eps → eps < 1 →
      ∃ y : Fin k → ℕ → E,
        (∀ i, Pairwise fun n m => IsVLDisjoint (y i n) (y i m)) ∧
        (∀ i n, y i n ∈ Set.Icc (0 : E) x) ∧
        ∀ n, (∑ i : Fin k, y i n) ≤ u n ∧
          u n ≤ (∑ i : Fin k, y i n) + eps • x := by
  intro k
  induction k with
  | zero =>
      intro u hk
      exact (Nat.not_lt_zero _ hk).elim
  | succ k ih =>
      intro u hk hu_interval hu_disj eps heps0 heps1
      rcases k with _ | k
      · refine ⟨fun _ => u, ?_, ?_, ?_⟩
        · intro i
          exact pairwise_of_isKDisjointSeq_two hu_disj
        · intro i n
          exact hu_interval n
        · intro n
          have hx : 0 ≤ x := (hu_interval n).1.trans (hu_interval n).2
          have hepsx : 0 ≤ eps • x := smul_nonneg (le_of_lt heps0) hx
          simp [hepsx]
      · have hk_two : 1 < k.succ.succ := by omega
        have heps_half_pos : 0 < eps / 2 := by
          positivity
        have heps_half_lt : eps / 2 < 1 := by linarith
        obtain ⟨w, y0, hw_disj, hy0_disj, hw_interval, hy0_interval, hwy⟩ :=
          disjointification_step_two hk_two hu_interval hu_disj heps_half_pos heps_half_lt
        obtain ⟨yr, hyr_disj, hyr_interval, hyr_approx⟩ :=
          ih (by omega) hw_interval hw_disj heps_half_pos heps_half_lt
        let y : Fin (k.succ.succ) → ℕ → E := Fin.cons y0 yr
        refine ⟨y, ?_, ?_, ?_⟩
        · intro i
          induction i using Fin.cases with
          | zero =>
              exact hy0_disj
          | succ i =>
              exact hyr_disj i
        · intro i n
          induction i using Fin.cases with
          | zero =>
              exact hy0_interval n
          | succ i =>
              exact hyr_interval i n
        · intro n
          have hsum : (∑ i : Fin (k.succ.succ), y i n) = y0 n + ∑ i : Fin k.succ, yr i n := by
            simp [y, Fin.sum_univ_succ]
          constructor
          · rw [hsum]
            calc
              y0 n + ∑ i : Fin k.succ, yr i n ≤ y0 n + w n :=
                add_le_add_right (hyr_approx n).1 (y0 n)
              _ ≤ u n := (hwy n).1
          · have hupper := (hwy n).2
            have hrec := (hyr_approx n).2
            rw [hsum]
            have hscalar : (eps / 2) • x + (eps / 2) • x = eps • x := by
              rw [← add_smul]
              ring_nf
            calc
              u n ≤ y0 n + w n + (eps / 2) • x := hupper
              _ ≤ y0 n + ((∑ i : Fin k.succ, yr i n) + (eps / 2) • x) +
                    (eps / 2) • x := by
                    gcongr
              _ = y0 n + ∑ i : Fin k.succ, yr i n +
                    ((eps / 2) • x + (eps / 2) • x) := by abel
              _ = y0 n + ∑ i : Fin k.succ, yr i n + eps • x := by
                    rw [hscalar]

/-- Disjointification of increments of an increasing order-bounded sequence. -/
theorem exists_disjoint_sequences_approx_of_monotone_le {x : E} {u : ℕ → E}
    (h0 : ∀ n, 0 ≤ u n) (hmono : Monotone u) (hle : ∀ n, u n ≤ x)
    {k : ℕ} (hk : 0 < k) :
    ∃ y : Fin k → ℕ → E,
      (∀ i, Pairwise fun n m => IsVLDisjoint (y i n) (y i m)) ∧
      (∀ i n, y i n ∈ Set.Icc (0 : E) x) ∧
      ∀ n, (∑ i : Fin k, y i n) ≤ u (n + 1) - u n ∧
        u (n + 1) - u n ≤
          (∑ i : Fin k, y i n) + ((2 : ℝ) / ((k : ℝ) + 3)) • x := by
  rcases k with _ | k
  · exact (Nat.not_lt_zero _ hk).elim
  rcases k with _ | k
  · obtain ⟨v, hv_disj, hv_interval, hv_approx⟩ :=
      disjointification_step_one h0 hmono hle 1
    refine ⟨fun _ => v, ?_, ?_, ?_⟩
    · intro i
      exact pairwise_of_isKDisjointSeq_two hv_disj
    · intro i n
      exact hv_interval n
    · intro n
      have hcoef :
          ((1 : ℝ) / ((1 : ℝ) + 1)) = ((2 : ℝ) / ((1 : ℝ) + 3)) := by
        norm_num
      simpa [hcoef] using hv_approx n
  · let K : ℕ := k.succ.succ
    obtain ⟨v, hv_disj, hv_interval, hv_approx⟩ :=
      disjointification_step_one h0 hmono hle K
    let eps : ℝ := (2 : ℝ) / ((K : ℝ) + 3) - (1 : ℝ) / ((K : ℝ) + 1)
    have heps0 : 0 < eps := by
      dsimp [eps]
      have hlt :
          (1 : ℝ) / ((K : ℝ) + 1) < (2 : ℝ) / ((K : ℝ) + 3) := by
        rw [div_lt_div_iff₀ (show 0 < (K : ℝ) + 1 by positivity)
          (show 0 < (K : ℝ) + 3 by positivity)]
        have hK : (1 : ℝ) < K := by exact_mod_cast (by omega : 1 < K)
        nlinarith
      linarith
    have heps1 : eps < 1 := by
      dsimp [eps]
      have hpos : 0 < (1 : ℝ) / ((K : ℝ) + 1) := by positivity
      have hlt : (2 : ℝ) / ((K : ℝ) + 3) < 1 := by
        rw [div_lt_one₀ (show 0 < (K : ℝ) + 3 by positivity)]
        have hKnonneg : (0 : ℝ) ≤ K := by positivity
        nlinarith
      linarith
    obtain ⟨y, hy_disj, hy_interval, hy_approx⟩ :=
      split_isKDisjointSeq (x := x) (k := K) (u := v) (by omega) hv_interval hv_disj
        heps0 heps1
    refine ⟨y, hy_disj, hy_interval, ?_⟩
    intro n
    constructor
    · exact (hy_approx n).1.trans (hv_approx n).1
    · calc
        u (n + 1) - u n ≤ v n + ((1 : ℝ) / ((K : ℝ) + 1)) • x := (hv_approx n).2
        _ ≤ ((∑ i : Fin K, y i n) + eps • x) +
              ((1 : ℝ) / ((K : ℝ) + 1)) • x :=
              add_le_add_left (hy_approx n).2 _
        _ = (∑ i : Fin K, y i n) + ((2 : ℝ) / ((K : ℝ) + 3)) • x := by
              have hscalar : eps • x + ((1 : ℝ) / ((K : ℝ) + 1)) • x =
                  ((2 : ℝ) / ((K : ℝ) + 3)) • x := by
                rw [← add_smul]
                congr 1
                simp [eps]
              calc
                (∑ i : Fin K, y i n) + eps • x +
                    ((1 : ℝ) / ((K : ℝ) + 1)) • x =
                    (∑ i : Fin K, y i n) +
                      (eps • x + ((1 : ℝ) / ((K : ℝ) + 1)) • x) := by abel
                _ = (∑ i : Fin K, y i n) + ((2 : ℝ) / ((K : ℝ) + 3)) • x := by
                    rw [hscalar]

end Disjointification

section NormCriterion

variable {E : Type*} [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]
  [NormedVectorLattice E]

omit [NormedVectorLattice E] in
/-- One direction of the interval criterion: Cauchy partial sums force disjoint
sequences in the interval to converge to zero in norm. -/
private theorem disjoint_tendsto_zero_of_monotone_le_cauchySeq {x : E}
    (hx : 0 ≤ x)
    (hcauchy : ∀ {u : ℕ → E}, (∀ n, 0 ≤ u n) → Monotone u →
      (∀ n, u n ≤ x) → CauchySeq u)
    {u : ℕ → E} (hu_interval : ∀ n, u n ∈ Set.Icc (0 : E) x)
    (hu_disj : Pairwise fun n m => IsVLDisjoint (u n) (u m)) :
    Filter.Tendsto u Filter.atTop (nhds 0) := by
  let v : ℕ → E := fun m => ∑ k ∈ Finset.range m, u k
  have hv_nn : ∀ m, 0 ≤ v m := fun m =>
    Finset.sum_nonneg (fun k _ => (hu_interval k).1)
  have hv_mono : Monotone v := by
    refine monotone_nat_of_le_succ (fun n => ?_)
    simp only [v, Finset.sum_range_succ]
    exact le_add_of_nonneg_right (hu_interval n).1
  have key : ∀ m k, m ≤ k → v m ⊓ u k = 0 := by
    intro m
    induction m with
    | zero =>
        intro k _
        simpa [v] using (inf_eq_left.mpr (hu_interval k).1 : (0 : E) ⊓ u k = 0)
    | succ n ih =>
        intro k hk
        have h1 : v n ⊓ u k = 0 := ih k (by omega)
        have h2 : u n ⊓ u k = 0 :=
          inf_eq_zero_of_isVLDisjoint (hu_interval n).1 (hu_interval k).1
            (hu_disj (by omega))
        have heq : v (n + 1) = v n + u n := by
          simp [v, Finset.sum_range_succ]
        refine le_antisymm ?_
          (le_inf (by rw [heq]; exact add_nonneg (hv_nn n) (hu_interval n).1)
            (hu_interval k).1)
        rw [heq, inf_comm]
        calc u k ⊓ (v n + u n)
            ≤ u k ⊓ v n + u k ⊓ u n :=
              inf_le_inf_add_inf_of_nonneg (x := u k) (v n) (u n)
                (hu_interval k).1 (hv_nn n) (hu_interval n).1
          _ = 0 := by rw [inf_comm, h1, inf_comm, h2, add_zero]
  have hv_le : ∀ m, v m ≤ x := by
    intro m
    induction m with
    | zero => simpa [v] using hx
    | succ n ih =>
        have hdisj : IsVLDisjoint (v n) (u n) :=
          isVLDisjoint_of_inf_eq_zero (key n n (le_refl n))
        have heq : v (n + 1) = v n + u n := by
          simp [v, Finset.sum_range_succ]
        have hsup : v n + u n = v n ⊔ u n :=
          add_eq_sup_of_isVLDisjoint_of_nonneg (hv_nn n) (hu_interval n).1 hdisj
        rw [heq, hsup]
        exact sup_le ih (hu_interval n).2
  have hv_cauchy : CauchySeq v := hcauchy hv_nn hv_mono hv_le
  rw [Metric.cauchySeq_iff] at hv_cauchy
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨N, hN⟩ := hv_cauchy ε hε
  refine Filter.eventually_atTop.mpr ⟨N, fun m hm => ?_⟩
  have hdist : dist (v (m + 1)) (v m) < ε := hN (m + 1) (by omega) m hm
  have heq : v (m + 1) - v m = u m := by
    simp [v, Finset.sum_range_succ]
  rw [dist_zero_right]
  rw [dist_eq_norm, heq] at hdist
  exact hdist

/-- The converse direction of the interval criterion: disjoint null sequences
in the interval force every increasing sequence bounded by the endpoint to be
norm-Cauchy. -/
private theorem monotone_le_cauchySeq_of_disjoint_tendsto_zero {x : E}
    (hx : 0 ≤ x)
    (hdisj : ∀ {u : ℕ → E}, (∀ n, u n ∈ Set.Icc (0 : E) x) →
      Pairwise (fun n m => IsVLDisjoint (u n) (u m)) →
      Filter.Tendsto u Filter.atTop (nhds 0))
    {u : ℕ → E} (h0 : ∀ n, 0 ≤ u n) (hmono : Monotone u)
    (hle : ∀ n, u n ≤ x) :
    CauchySeq u := by
  rw [Metric.cauchySeq_iff']
  intro ε hε
  by_contra hbad
  push Not at hbad
  let next : ℕ → ℕ := fun N => (hbad N).choose
  have hnext : ∀ N, N ≤ next N ∧ ε ≤ dist (u (next N)) (u N) :=
    fun N => (hbad N).choose_spec
  let φ : ℕ → ℕ := fun n => Nat.rec 0 (fun _ N => next N) n
  have hφ_succ : ∀ n, φ n < φ (n + 1) := by
    intro n
    have hleφ : φ n ≤ φ (n + 1) := (hnext (φ n)).1
    refine lt_of_le_of_ne hleφ ?_
    intro heq
    have hdist : ε ≤ dist (u (φ (n + 1))) (u (φ n)) := by
      simpa [φ] using (hnext (φ n)).2
    rw [heq, dist_self] at hdist
    linarith
  have hφ_strict : StrictMono φ := strictMono_nat_of_lt_succ hφ_succ
  let z : ℕ → E := fun n => u (φ n)
  have hz0 : ∀ n, 0 ≤ z n := fun n => h0 (φ n)
  have hz_mono : Monotone z := fun m n hmn => hmono (hφ_strict.monotone hmn)
  have hz_le : ∀ n, z n ≤ x := fun n => hle (φ n)
  have hcoeff_tend :
      Filter.Tendsto (fun k : ℕ => ‖((2 : ℝ) / ((k : ℝ) + 3)) • x‖)
        Filter.atTop (nhds 0) := by
    have hone :
        Filter.Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 3)) Filter.atTop
          (nhds 0) := by
      have hbase :
          Filter.Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1)) Filter.atTop
            (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
      convert hbase.comp (Filter.tendsto_add_atTop_nat 2) using 1
      ext k
      simp
      ring
    have htwo :
        Filter.Tendsto (fun k : ℕ => (2 : ℝ) / ((k : ℝ) + 3)) Filter.atTop
          (nhds 0) := by
      simpa [div_eq_mul_inv] using (tendsto_const_nhds.mul hone)
    have hvec :
        Filter.Tendsto (fun k : ℕ => ((2 : ℝ) / ((k : ℝ) + 3)) • x)
          Filter.atTop (nhds ((0 : ℝ) • x)) :=
      htwo.smul (show Filter.Tendsto (fun _ : ℕ => x) Filter.atTop (nhds x) from
        tendsto_const_nhds)
    simpa using hvec.norm
  have herr_event := Metric.tendsto_nhds.mp hcoeff_tend (ε / 2) (by linarith)
  rw [Filter.eventually_atTop] at herr_event
  obtain ⟨K, hK⟩ := herr_event
  let k : ℕ := K + 1
  have hkpos : 0 < k := by simp [k]
  have herr : ‖((2 : ℝ) / ((k : ℝ) + 3)) • x‖ < ε / 2 := by
    have hk := hK k (by simp [k])
    rw [Real.dist_eq] at hk
    simpa [abs_of_nonneg (norm_nonneg _)] using hk
  obtain ⟨y, hy_disj, hy_interval, hy_approx⟩ :=
    exists_disjoint_sequences_approx_of_monotone_le hz0 hz_mono hz_le hkpos
  have hy_tend : ∀ i : Fin k, Filter.Tendsto (y i) Filter.atTop (nhds 0) :=
    fun i => hdisj (hy_interval i) (hy_disj i)
  have hsum_tend :
      Filter.Tendsto (fun n => ∑ i : Fin k, y i n) Filter.atTop (nhds 0) := by
    have hsum :
        Filter.Tendsto (fun n => ∑ i : Fin k, y i n) Filter.atTop
          (nhds (∑ i : Fin k, (0 : E))) :=
      tendsto_finsetSum Finset.univ (fun i _ => hy_tend i)
    simpa using hsum
  have hsum_event := Metric.tendsto_nhds.mp hsum_tend (ε / 2) (by linarith)
  rw [Filter.eventually_atTop] at hsum_event
  obtain ⟨N, hN⟩ := hsum_event
  have hsmall_sum : dist (∑ i : Fin k, y i N) 0 < ε / 2 := hN N (le_refl N)
  rw [dist_zero_right] at hsmall_sum
  have hlower : ε ≤ ‖z (N + 1) - z N‖ := by
    have hdist : ε ≤ dist (u (φ (N + 1))) (u (φ N)) := by
      simpa [φ] using (hnext (φ N)).2
    rwa [dist_eq_norm] at hdist
  have hd_nonneg : 0 ≤ z (N + 1) - z N :=
    sub_nonneg.mpr (hz_mono (Nat.le_succ N))
  have hsum_nonneg : 0 ≤ ∑ i : Fin k, y i N :=
    Finset.sum_nonneg fun i _ => (hy_interval i N).1
  have hcoeff_nonneg : 0 ≤ (2 : ℝ) / ((k : ℝ) + 3) := by positivity
  have hrhs_nonneg : 0 ≤
      (∑ i : Fin k, y i N) + ((2 : ℝ) / ((k : ℝ) + 3)) • x :=
    add_nonneg hsum_nonneg (smul_nonneg hcoeff_nonneg hx)
  have hnorm_le :
      ‖z (N + 1) - z N‖ ≤
        ‖(∑ i : Fin k, y i N) + ((2 : ℝ) / ((k : ℝ) + 3)) • x‖ := by
    rw [← norm_abs_eq_norm (z (N + 1) - z N),
      ← norm_abs_eq_norm ((∑ i : Fin k, y i N) + ((2 : ℝ) / ((k : ℝ) + 3)) • x)]
    exact norm_le_norm_of_abs_le_abs (by
      simpa [abs_of_nonneg hd_nonneg, abs_of_nonneg hrhs_nonneg] using (hy_approx N).2)
  have hnorm_add :
      ‖(∑ i : Fin k, y i N) + ((2 : ℝ) / ((k : ℝ) + 3)) • x‖ <
        ε := by
    have htri :
        ‖(∑ i : Fin k, y i N) + ((2 : ℝ) / ((k : ℝ) + 3)) • x‖ ≤
          ‖∑ i : Fin k, y i N‖ + ‖((2 : ℝ) / ((k : ℝ) + 3)) • x‖ :=
      norm_add_le _ _
    linarith
  linarith

/-- For a normed vector lattice, increasing sequences bounded by `x` are
norm-Cauchy iff disjoint sequences in `[0, x]` converge to zero in norm. -/
theorem monotone_le_cauchySeq_iff_disjoint_tendsto_zero {x : E} (hx : 0 ≤ x) :
    (∀ {u : ℕ → E}, (∀ n, 0 ≤ u n) → Monotone u → (∀ n, u n ≤ x) →
      CauchySeq u) ↔
    (∀ {u : ℕ → E}, (∀ n, u n ∈ Set.Icc (0 : E) x) →
      Pairwise (fun n m => IsVLDisjoint (u n) (u m)) →
      Filter.Tendsto u Filter.atTop (nhds 0)) := by
  exact ⟨disjoint_tendsto_zero_of_monotone_le_cauchySeq hx,
    monotone_le_cauchySeq_of_disjoint_tendsto_zero hx⟩

end NormCriterion

namespace BanachLattice

variable [BanachLattice X]

/-- In an order continuous Banach lattice, every order-bounded pairwise
disjoint sequence converges to zero in norm. -/
theorem disjoint_bddAbove_tendsto_zero [IsOrderContinuousNorm X]
    {u : ℕ → X} (hd : Pairwise fun i j => IsVLDisjoint (u i) (u j))
    (hbd : BddAbove (Set.range fun n => |u n|)) :
    Filter.Tendsto u Filter.atTop (nhds 0) := by
  classical
  obtain ⟨w, hw⟩ := hbd
  -- Partial sums of `|u_k|`.
  let v : ℕ → X := fun m => ∑ k ∈ Finset.range m, |u k|
  have hv_nn : ∀ m, 0 ≤ v m := fun m =>
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hv_mono : Monotone v := by
    refine monotone_nat_of_le_succ (fun n => ?_)
    simp only [v, Finset.sum_range_succ]
    exact le_add_of_nonneg_right (abs_nonneg _)
  -- Partial sums are disjoint from later terms (by induction).
  have key : ∀ m k, m ≤ k → v m ⊓ |u k| = 0 := by
    intro m
    induction m with
    | zero =>
        intro k _
        simp [v]
    | succ n ih =>
        intro k hk
        have h1 : v n ⊓ |u k| = 0 := ih k (by omega)
        have h2 : |u n| ⊓ |u k| = 0 := hd (by omega)
        have heq : v (n + 1) = v n + |u n| := by
          simp [v, Finset.sum_range_succ]
        refine le_antisymm ?_
          (le_inf (by rw [heq]; exact add_nonneg (hv_nn n) (abs_nonneg _))
            (abs_nonneg _))
        rw [heq, inf_comm]
        calc |u k| ⊓ (v n + |u n|)
            ≤ |u k| ⊓ v n + |u k| ⊓ |u n| :=
              inf_le_inf_add_inf_of_nonneg (x := |u k|) (v n) (|u n|)
                (abs_nonneg _) (hv_nn n) (abs_nonneg _)
          _ = 0 := by rw [inf_comm, h1, inf_comm, h2, add_zero]
  -- Partial sums are bounded by `w`.
  have hv_le : ∀ m, v m ≤ w := by
    intro m
    induction m with
    | zero => simpa [v] using (abs_nonneg (u 0)).trans (hw ⟨0, rfl⟩)
    | succ n ih =>
        have hdisj : v n ⊓ |u n| = 0 := key n n (le_refl n)
        have heq : v (n + 1) = v n + |u n| := by
          simp [v, Finset.sum_range_succ]
        have hsup : v n + |u n| = v n ⊔ |u n| := by
          have := inf_add_sup (v n) (|u n|)
          rw [hdisj, zero_add] at this
          exact this.symm
        rw [heq, hsup]
        exact sup_le ih (hw ⟨n, rfl⟩)
  -- Use Nakano to get `v` converges in norm.
  obtain ⟨_, _, hv_tend⟩ :=
    tendsto_of_monotone_bddAbove hv_mono ⟨w, by rintro _ ⟨m, rfl⟩; exact hv_le m⟩
  have hv_cauchy : CauchySeq v := hv_tend.cauchySeq
  rw [Metric.cauchySeq_iff] at hv_cauchy
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨N, hN⟩ := hv_cauchy ε hε
  refine Filter.eventually_atTop.mpr ⟨N, fun m hm => ?_⟩
  have hdist : dist (v (m + 1)) (v m) < ε := hN (m + 1) (by omega) m hm
  have heq : v (m + 1) - v m = |u m| := by
    simp [v, Finset.sum_range_succ]
  rw [dist_zero_right, ← norm_abs_eq_norm]
  rw [dist_eq_norm, heq] at hdist
  exact hdist

/-- A Banach lattice whose order-bounded pairwise disjoint sequences all
converge to zero in norm has an order continuous norm. -/
theorem isOrderContinuousNorm_of_disjoint_tendsto_zero
    (h : ∀ {u : ℕ → X},
      Pairwise (fun i j => IsVLDisjoint (u i) (u j)) →
      BddAbove (Set.range fun n => |u n|) →
      Filter.Tendsto u Filter.atTop (nhds 0)) :
    IsOrderContinuousNorm X := by
  classical
  have hmono_tend :
      ∀ {u : ℕ → X}, Monotone u → BddAbove (Set.range u) →
        ∃ x, IsLUB (Set.range u) x ∧ Filter.Tendsto u Filter.atTop (nhds x) := by
    intro u hu_mono hu_bdd
    obtain ⟨b, hb⟩ := hu_bdd
    let v : ℕ → X := fun n => u n - u 0
    have hv0 : ∀ n, 0 ≤ v n := fun n => sub_nonneg.mpr (hu_mono (Nat.zero_le n))
    have hv_mono : Monotone v := fun m n hmn => sub_le_sub_right (hu_mono hmn) (u 0)
    have hv_le : ∀ n, v n ≤ b - u 0 := fun n => sub_le_sub_right (hb ⟨n, rfl⟩) (u 0)
    have hb0 : 0 ≤ b - u 0 := by simpa [v] using hv_le 0
    have hv_cauchy : CauchySeq v := by
      refine (monotone_le_cauchySeq_iff_disjoint_tendsto_zero hb0).2 ?_ hv0 hv_mono hv_le
      intro y hy_interval hy_disj
      refine h hy_disj ?_
      exact ⟨b - u 0, by
        rintro _ ⟨n, rfl⟩
        simpa [abs_of_nonneg (hy_interval n).1] using (hy_interval n).2⟩
    obtain ⟨a, hv_tend⟩ := cauchySeq_tendsto_of_complete hv_cauchy
    have hu_tend : Filter.Tendsto u Filter.atTop (nhds (u 0 + a)) := by
      have htend : Filter.Tendsto (fun n => u 0 + v n) Filter.atTop (nhds (u 0 + a)) :=
        tendsto_const_nhds.add hv_tend
      convert htend using 1
      · ext n
        simp [v, sub_eq_add_neg]
    exact ⟨u 0 + a, isLUB_of_tendsto_atTop hu_mono hu_tend, hu_tend⟩
  let banach : BanachLattice X := inferInstance
  let : SigmaConditionallyCompleteLattice X :=
    sigmaConditionallyCompleteLatticeOfMonoBddAboveTendsto hmono_tend
  let orderedAdd : IsOrderedAddMonoid X := {
    add_le_add_left := fun _ _ h _ => add_le_add_left h _
  }
  let : IsOrderedAddMonoid X := orderedAdd
  let sigmaOrderContinuous : IsSigmaOrderContinuousNorm X :=
    isSigmaOrderContinuousNorm_of_mono_bddAbove_tendsto hmono_tend
  have : IsSigmaOrderContinuousNorm X := sigmaOrderContinuous
  exact @isOrderContinuousNorm_of_isSigmaConditionallyCompleteLattice X
    inferInstance inferInstance orderedAdd banach sigmaOrderContinuous

/-- **Meyer-Nieberg theorem**: a Banach lattice has an order continuous norm
iff every order-bounded pairwise disjoint sequence converges to zero. -/
theorem isOrderContinuousNorm_iff_disjoint_tendsto_zero :
    IsOrderContinuousNorm X ↔
      (∀ {u : ℕ → X},
        Pairwise (fun i j => IsVLDisjoint (u i) (u j)) →
        BddAbove (Set.range fun n => |u n|) →
        Filter.Tendsto u Filter.atTop (nhds 0)) :=
  ⟨fun _ => disjoint_bddAbove_tendsto_zero,
   fun h => isOrderContinuousNorm_of_disjoint_tendsto_zero (fun hd hbd => h hd hbd)⟩

/-- In an order continuous Banach lattice, any order-bounded set of pairwise
disjoint non-zero elements is at most countable. -/
theorem countable_of_pairwise_disjoint_bddAbove [IsOrderContinuousNorm X]
    {S : Set X} (h0 : ∀ x ∈ S, x ≠ 0)
    (hd : S.Pairwise (fun x y => IsVLDisjoint x y))
    (hbd : BddAbove ((fun x => |x|) '' S)) :
    S.Countable := by
  -- Stratify by norm: `S_n = {x ∈ S | ‖x‖ ≥ 1/(n+1)}`.
  classical
  set T : ℕ → Set X := fun n => {x ∈ S | 1 / (n + 1 : ℝ) ≤ ‖x‖} with hT
  -- Each stratum is finite.
  have hTfin : ∀ n, (T n).Finite := by
    intro n
    by_contra hinf
    rw [Set.not_finite] at hinf
    let φ : ℕ ↪ ↥(T n) := hinf.natEmbedding
    let y : ℕ → X := fun k => ((φ k : ↥(T n)) : X)
    have hy_mem : ∀ k, y k ∈ S := fun k => (φ k).prop.1
    have hy_norm : ∀ k, 1 / (n + 1 : ℝ) ≤ ‖y k‖ := fun k => (φ k).prop.2
    have hy_inj : Function.Injective y := by
      intro a b hab
      have : φ a = φ b := Subtype.ext hab
      exact φ.injective this
    have hy_disj : Pairwise fun i j => IsVLDisjoint (y i) (y j) := by
      intro i j hij
      exact hd (hy_mem i) (hy_mem j) (fun h => hij (hy_inj h))
    have hy_bd : BddAbove (Set.range fun k => |y k|) := by
      obtain ⟨u, hu⟩ := hbd
      exact ⟨u, by rintro _ ⟨k, rfl⟩; exact hu ⟨y k, hy_mem k, rfl⟩⟩
    have htend : Filter.Tendsto y Filter.atTop (nhds 0) :=
      disjoint_bddAbove_tendsto_zero hy_disj hy_bd
    rw [Metric.tendsto_nhds] at htend
    have hpos : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
    have hev := htend (1 / (n + 1 : ℝ)) hpos
    rw [Filter.eventually_atTop] at hev
    obtain ⟨K, hK⟩ := hev
    have := hK K (le_refl K)
    rw [dist_zero_right] at this
    exact absurd (hy_norm K) (not_le.mpr this)
  -- `S = ⋃ n, T n` because every nonzero element has positive norm.
  have hcover : S ⊆ ⋃ n, T n := by
    intro x hx
    have hne : x ≠ 0 := h0 x hx
    have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hne
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hnorm
    exact Set.mem_iUnion.mpr ⟨n, hx, le_of_lt hn⟩
  refine (Set.Countable.mono hcover ?_)
  exact Set.countable_iUnion (fun n => (hTfin n).countable)

end BanachLattice
