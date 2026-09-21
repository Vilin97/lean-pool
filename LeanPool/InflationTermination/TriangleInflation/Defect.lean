/-
Copyright (c) 2026 William Blair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Blair
-/

import LeanPool.InflationTermination.TriangleInflation.Finner

/-!
# The defect cube

Statements for paper Section 5.1 (`sec:construction`) and the Navascués–Wolfe part of
Section 5.3 (`sec:survival`): Lemma 5.4 (`lem:disjoint`), Lemma 5.5 (`lem:triangle-law`),
Lemma 5.6 (`lem:symmetry`) and Lemma 5.9 (`lem:diag`), together with the general
independence lemma for functions of disjoint coordinate sets under a product weight that
those proofs use. Proofs are deferred.
-/

namespace TriangleInflation

open Finset

noncomputable
section

/-! ## Independence under a product weight

The general fact behind the paper's repeated phrase "outputs that are functions of disjoint
families of independent bits are independent". -/

section ProductWeight

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The total mass of a product weight is one. -/
theorem sum_prodLaw {w : ι → Bool → ℝ} (hw : ∀ i, IsLaw (w i)) :
    ∑ x : ι → Bool, prodLaw w x = 1 := by
  have h := Finset.prod_univ_sum (fun _ : ι => (univ : Finset Bool)) w
  rw [Fintype.piFinset_univ] at h
  have h1 : ∏ i : ι, ∑ b : Bool, w i b = 1 :=
    Finset.prod_eq_one fun i _ => (hw i).2
  simp only [prodLaw]
  rw [← h]
  exact h1

/-- `mixOn I x y` takes its `I`-coordinates from `x` and all other coordinates from `y`. -/
def mixOn (I : Finset ι) (x y : ι → Bool) : ι → Bool := fun i => if i ∈ I then x i else y i

omit [Fintype ι] in
theorem mixOn_mem {I : Finset ι} {x y : ι → Bool} {i : ι} (hi : i ∈ I) :
    mixOn I x y i = x i := by simp [mixOn, hi]

omit [Fintype ι] in
theorem mixOn_not_mem {I : Finset ι} {x y : ι → Bool} {i : ι} (hi : i ∉ I) :
    mixOn I x y i = y i := by simp [mixOn, hi]

/-- Swapping the `I`-coordinates of a pair of assignments preserves the product weight of
the pair. -/
theorem prodLaw_mixOn_mul {w : ι → Bool → ℝ} (I : Finset ι) (x y : ι → Bool) :
    prodLaw w (mixOn I x y) * prodLaw w (mixOn I y x) = prodLaw w x * prodLaw w y := by
  simp only [prodLaw, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hi : i ∈ I
  · rw [mixOn_mem hi, mixOn_mem hi]
  · rw [mixOn_not_mem hi, mixOn_not_mem hi, mul_comm]

/-- The expectation form of independence: real-valued functions of disjoint coordinate sets
have uncorrelated expectations under a product weight. -/
theorem sum_prodLaw_mul_mul {w : ι → Bool → ℝ} (hw : ∀ i, IsLaw (w i))
    {I J : Finset ι} (hIJ : Disjoint I J) {φ ψ : (ι → Bool) → ℝ}
    (hφ : ∀ x y, (∀ i ∈ I, x i = y i) → φ x = φ y)
    (hψ : ∀ x y, (∀ i ∈ J, x i = y i) → ψ x = ψ y) :
    ∑ x, prodLaw w x * (φ x * ψ x)
      = (∑ x, prodLaw w x * φ x) * (∑ x, prodLaw w x * ψ x) := by
  classical
  set T : (ι → Bool) × (ι → Bool) → (ι → Bool) × (ι → Bool) :=
    fun q => (mixOn I q.1 q.2, mixOn I q.2 q.1) with hTdef
  have hTT : Function.LeftInverse T T := by
    intro q
    have h1 : mixOn I (mixOn I q.1 q.2) (mixOn I q.2 q.1) = q.1 := by
      funext i
      by_cases hi : i ∈ I
      · rw [mixOn_mem hi, mixOn_mem hi]
      · rw [mixOn_not_mem hi, mixOn_not_mem hi]
    have h2 : mixOn I (mixOn I q.2 q.1) (mixOn I q.1 q.2) = q.2 := by
      funext i
      by_cases hi : i ∈ I
      · rw [mixOn_mem hi, mixOn_mem hi]
      · rw [mixOn_not_mem hi, mixOn_not_mem hi]
    simp only [hTdef]
    exact Prod.ext h1 h2
  let e : (ι → Bool) × (ι → Bool) ≃ (ι → Bool) × (ι → Bool) := ⟨T, T, hTT, hTT⟩
  have hstep : ∀ q : (ι → Bool) × (ι → Bool),
      (prodLaw w q.1 * φ q.1) * (prodLaw w q.2 * ψ q.2)
        = (prodLaw w (e q).1 * (φ (e q).1 * ψ (e q).1)) * prodLaw w (e q).2 := by
    intro q
    have hφm : φ (mixOn I q.1 q.2) = φ q.1 :=
      hφ _ _ fun i hi => mixOn_mem hi
    have hψm : ψ (mixOn I q.1 q.2) = ψ q.2 :=
      hψ _ _ fun i hi => mixOn_not_mem (Finset.disjoint_right.mp hIJ hi)
    have hp := prodLaw_mixOn_mul (w := w) I q.1 q.2
    change (prodLaw w q.1 * φ q.1) * (prodLaw w q.2 * ψ q.2)
      = (prodLaw w (mixOn I q.1 q.2) * (φ (mixOn I q.1 q.2) * ψ (mixOn I q.1 q.2)))
          * prodLaw w (mixOn I q.2 q.1)
    rw [hφm, hψm]
    calc (prodLaw w q.1 * φ q.1) * (prodLaw w q.2 * ψ q.2)
        = (prodLaw w q.1 * prodLaw w q.2) * (φ q.1 * ψ q.2) := by ring
      _ = (prodLaw w (mixOn I q.1 q.2) * prodLaw w (mixOn I q.2 q.1)) * (φ q.1 * ψ q.2) := by
            rw [hp]
      _ = (prodLaw w (mixOn I q.1 q.2) * (φ q.1 * ψ q.2)) * prodLaw w (mixOn I q.2 q.1) := by
            ring
  have hsum := Fintype.sum_equiv e
    (fun q : (ι → Bool) × (ι → Bool) => (prodLaw w q.1 * φ q.1) * (prodLaw w q.2 * ψ q.2))
    (fun q : (ι → Bool) × (ι → Bool) =>
      (prodLaw w q.1 * (φ q.1 * ψ q.1)) * prodLaw w q.2) hstep
  have e1 : (∑ x, prodLaw w x * φ x) * (∑ x, prodLaw w x * ψ x)
      = ∑ q : (ι → Bool) × (ι → Bool), (prodLaw w q.1 * φ q.1) * (prodLaw w q.2 * ψ q.2) := by
    simp only [Fintype.sum_prod_type]
    exact Finset.sum_mul_sum _ _ _ _
  have e2 : (∑ x, prodLaw w x * (φ x * ψ x)) * (∑ x, prodLaw w x)
      = ∑ q : (ι → Bool) × (ι → Bool), (prodLaw w q.1 * (φ q.1 * ψ q.1)) * prodLaw w q.2 := by
    simp only [Fintype.sum_prod_type]
    exact Finset.sum_mul_sum _ _ _ _
  rw [e1, hsum, ← e2, sum_prodLaw hw, mul_one]

/-- The finite-family expectation form: real-valued functions of pairwise disjoint
coordinate sets have a product expectation under a product weight. -/
theorem sum_prodLaw_prod {w : ι → Bool → ℝ} (hw : ∀ i, IsLaw (w i)) :
    ∀ {n : ℕ} (I : Fin n → Finset ι) (χ : Fin n → (ι → Bool) → ℝ),
      (∀ m m', m ≠ m' → Disjoint (I m) (I m')) →
      (∀ m x y, (∀ i ∈ I m, x i = y i) → χ m x = χ m y) →
      ∑ x, prodLaw w x * ∏ m, χ m x = ∏ m, ∑ x, prodLaw w x * χ m x := by
  intro n
  induction n with
  | zero => intro I χ _ _; simp [sum_prodLaw hw]
  | succ n ih =>
      intro I χ hI hχ
      have hsplit : ∀ x : ι → Bool,
          (∏ m : Fin (n + 1), χ m x) = χ 0 x * ∏ m : Fin n, χ m.succ x := by
        intro x
        exact Fin.prod_univ_succ (fun m => χ m x)
      have hdisj : Disjoint (I 0) (univ.biUnion fun m : Fin n => I m.succ) := by
        rw [Finset.disjoint_biUnion_right]
        intro m _
        exact hI 0 m.succ (Ne.symm (Fin.succ_ne_zero m))
      have hdep : ∀ x y : ι → Bool,
          (∀ i ∈ univ.biUnion fun m : Fin n => I m.succ, x i = y i) →
            (∏ m : Fin n, χ m.succ x) = ∏ m : Fin n, χ m.succ y := by
        intro x y hxy
        refine Finset.prod_congr rfl fun m _ => ?_
        exact hχ m.succ x y fun i hi => hxy i (mem_biUnion.mpr ⟨m, mem_univ m, hi⟩)
      have key := sum_prodLaw_mul_mul hw hdisj (φ := χ 0)
        (ψ := fun x => ∏ m : Fin n, χ m.succ x) (hχ 0) hdep
      have hrest := ih (fun m : Fin n => I m.succ) (fun m : Fin n => χ m.succ)
        (fun m m' hm => hI m.succ m'.succ fun hc => hm (Fin.succ_injective n hc))
        (fun m => hχ m.succ)
      calc ∑ x, prodLaw w x * ∏ m : Fin (n + 1), χ m x
          = ∑ x, prodLaw w x * (χ 0 x * ∏ m : Fin n, χ m.succ x) := by
            refine Finset.sum_congr rfl fun x _ => ?_
            rw [hsplit x]
        _ = (∑ x, prodLaw w x * χ 0 x) * ∑ x, prodLaw w x * ∏ m : Fin n, χ m.succ x := key
        _ = (∑ x, prodLaw w x * χ 0 x) * ∏ m : Fin n, ∑ x, prodLaw w x * χ m.succ x := by
            rw [hrest]
        _ = ∏ m : Fin (n + 1), ∑ x, prodLaw w x * χ m x :=
            (Fin.prod_univ_succ (fun m => ∑ x, prodLaw w x * χ m x)).symm

end ProductWeight

/-- Two functions of disjoint coordinate sets are independent under a product weight. -/
theorem indep_of_disjoint_support {ι α β : Type*} [Fintype ι] [DecidableEq ι]
    [DecidableEq α] [DecidableEq β]
    {w : ι → Bool → ℝ} (hw : ∀ i, IsLaw (w i)) {I J : Finset ι} (hIJ : Disjoint I J)
    {F : (ι → Bool) → α} {G : (ι → Bool) → β}
    (hF : ∀ x y, (∀ i ∈ I, x i = y i) → F x = F y)
    (hG : ∀ x y, (∀ i ∈ J, x i = y i) → G x = G y) :
    pushforward (prodLaw w) (fun x => (F x, G x))
      = fun q => pushforward (prodLaw w) F q.1 * pushforward (prodLaw w) G q.2 := by
  classical
  funext q
  obtain ⟨a, b⟩ := q
  have hL : pushforward (prodLaw w) (fun x => (F x, G x)) (a, b)
      = ∑ x, prodLaw w x
          * ((if F x = a then (1 : ℝ) else 0) * (if G x = b then (1 : ℝ) else 0)) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases h1 : F x = a <;> by_cases h2 : G x = b <;>
      simp [Prod.ext_iff, h1, h2]
  have hA : pushforward (prodLaw w) F a
      = ∑ x, prodLaw w x * (if F x = a then (1 : ℝ) else 0) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases h1 : F x = a <;> simp [h1]
  have hB : pushforward (prodLaw w) G b
      = ∑ x, prodLaw w x * (if G x = b then (1 : ℝ) else 0) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases h1 : G x = b <;> simp [h1]
  rw [hL, hA, hB]
  refine sum_prodLaw_mul_mul hw hIJ ?_ ?_
  · intro x y hxy; rw [hF x y hxy]
  · intro x y hxy; rw [hG x y hxy]

/-- An indicator product collapses to the indicator of the full agreement. -/
theorem prod_ite_eq_ite_funext {n : ℕ} {β : Fin n → Type*} [∀ m, DecidableEq (β m)]
    (f g : ∀ m, β m) :
    (∏ m, if f m = g m then (1 : ℝ) else 0) = if f = g then 1 else 0 := by
  by_cases h : f = g
  · subst h; simp
  · rw [ite_eq_right h]
    obtain ⟨m, hm⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (mem_univ m) (ite_eq_right hm)

/-- The finite-family form: functions of pairwise disjoint coordinate sets are mutually
independent under a product weight. -/
theorem indep_of_disjoint_family {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    {β : Fin n → Type*} [∀ m, DecidableEq (β m)]
    {w : ι → Bool → ℝ} (hw : ∀ i, IsLaw (w i)) {I : Fin n → Finset ι}
    (hI : ∀ m m', m ≠ m' → Disjoint (I m) (I m'))
    {F : ∀ m, (ι → Bool) → β m}
    (hF : ∀ m x y, (∀ i ∈ I m, x i = y i) → F m x = F m y) :
    pushforward (prodLaw w) (fun x m => F m x)
      = fun φ : ∀ m, β m => ∏ m, pushforward (prodLaw w) (F m) (φ m) := by
  funext φ
  have hL : pushforward (prodLaw w) (fun x m => F m x) φ
      = ∑ x, prodLaw w x * ∏ m, (if F m x = φ m then (1 : ℝ) else 0) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [prod_ite_eq_ite_funext (fun m => F m x) φ]
    by_cases h : (fun m => F m x) = φ <;> simp [h]
  have hR : ∀ m, pushforward (prodLaw w) (F m) (φ m)
      = ∑ x, prodLaw w x * (if F m x = φ m then (1 : ℝ) else 0) := by
    intro m
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases h : F m x = φ m <;> simp [h]
  rw [hL]
  rw [show (∏ m, pushforward (prodLaw w) (F m) (φ m))
      = ∏ m, ∑ x, prodLaw w x * (if F m x = φ m then (1 : ℝ) else 0) from
    Finset.prod_congr rfl fun m _ => hR m]
  refine sum_prodLaw_prod hw I _ hI ?_
  intro m x y hxy
  rw [hF m x y hxy]

/-! ## Disjoint ancestry gives disjoint inputs (Lemma 5.4) -/

/-- Every copied observation has a copied latent ancestor. -/
theorem Obs.ancestors_nonempty {t : ℕ} (u : Obs t) : u.ancestors.Nonempty := by
  cases u <;> simp [Obs.ancestors]

/-- The combinatorial half of paper Lemma 5.4 (`lem:disjoint`): two lines through the cube
meet only if the corresponding observations share a copied latent ancestor. -/
theorem line_inter_ancestors {t : ℕ} {u v : Obs t} {c : Cell t}
    (hu : onLine u c = true) (hv : onLine v c = true) :
    u = v ∨ ¬ Disjoint u.ancestors v.ancestors := by
  cases u with
  | A i j =>
      simp only [onLine, Bool.and_eq_true, beq_iff_eq] at hu
      obtain ⟨hu1, hu2⟩ := hu
      subst hu1; subst hu2
      cases v with
      | A i' j' =>
          simp only [onLine, Bool.and_eq_true, beq_iff_eq] at hv
          obtain ⟨hv1, hv2⟩ := hv
          subst hv1; subst hv2
          exact Or.inl rfl
      | B i' k' =>
          simp only [onLine, Bool.and_eq_true, beq_iff_eq] at hv
          obtain ⟨hv1, hv2⟩ := hv
          subst hv1; subst hv2
          refine Or.inr ?_
          rw [Finset.not_disjoint_iff]
          exact ⟨Latent.X c.1, by simp [Obs.ancestors], by simp [Obs.ancestors]⟩
      | C j' k' =>
          simp only [onLine, Bool.and_eq_true, beq_iff_eq] at hv
          obtain ⟨hv1, hv2⟩ := hv
          subst hv1; subst hv2
          refine Or.inr ?_
          rw [Finset.not_disjoint_iff]
          exact ⟨Latent.Z c.2.1, by simp [Obs.ancestors], by simp [Obs.ancestors]⟩
  | B i k =>
      simp only [onLine, Bool.and_eq_true, beq_iff_eq] at hu
      obtain ⟨hu1, hu2⟩ := hu
      subst hu1; subst hu2
      cases v with
      | A i' j' =>
          simp only [onLine, Bool.and_eq_true, beq_iff_eq] at hv
          obtain ⟨hv1, hv2⟩ := hv
          subst hv1; subst hv2
          refine Or.inr ?_
          rw [Finset.not_disjoint_iff]
          exact ⟨Latent.X c.1, by simp [Obs.ancestors], by simp [Obs.ancestors]⟩
      | B i' k' =>
          simp only [onLine, Bool.and_eq_true, beq_iff_eq] at hv
          obtain ⟨hv1, hv2⟩ := hv
          subst hv1; subst hv2
          exact Or.inl rfl
      | C j' k' =>
          simp only [onLine, Bool.and_eq_true, beq_iff_eq] at hv
          obtain ⟨hv1, hv2⟩ := hv
          subst hv1; subst hv2
          refine Or.inr ?_
          rw [Finset.not_disjoint_iff]
          exact ⟨Latent.Y c.2.2, by simp [Obs.ancestors], by simp [Obs.ancestors]⟩
  | C j k =>
      simp only [onLine, Bool.and_eq_true, beq_iff_eq] at hu
      obtain ⟨hu1, hu2⟩ := hu
      subst hu1; subst hu2
      cases v with
      | A i' j' =>
          simp only [onLine, Bool.and_eq_true, beq_iff_eq] at hv
          obtain ⟨hv1, hv2⟩ := hv
          subst hv1; subst hv2
          refine Or.inr ?_
          rw [Finset.not_disjoint_iff]
          exact ⟨Latent.Z c.2.1, by simp [Obs.ancestors], by simp [Obs.ancestors]⟩
      | B i' k' =>
          simp only [onLine, Bool.and_eq_true, beq_iff_eq] at hv
          obtain ⟨hv1, hv2⟩ := hv
          subst hv1; subst hv2
          refine Or.inr ?_
          rw [Finset.not_disjoint_iff]
          exact ⟨Latent.Y c.2.2, by simp [Obs.ancestors], by simp [Obs.ancestors]⟩
      | C j' k' =>
          simp only [onLine, Bool.and_eq_true, beq_iff_eq] at hv
          obtain ⟨hv1, hv2⟩ := hv
          subst hv1; subst hv2
          exact Or.inl rfl

/-- Membership of a defect cell in the root support. -/
theorem mem_rootSupport_inl {t : ℕ} {S : Finset (Obs t)} {c : Cell t} :
    (Sum.inl c : Root t) ∈ rootSupport S ↔ ∃ v ∈ S, onLine v c = true := by
  simp [rootSupport]

/-- Membership of a private bit in the root support. -/
theorem mem_rootSupport_inr {t : ℕ} {S : Finset (Obs t)} {u : Obs t} :
    (Sum.inr u : Root t) ∈ rootSupport S ↔ u ∈ S := by
  simp [rootSupport]

/-- Paper Lemma 5.4 (`lem:disjoint`), "disjoint inputs": ancestrally independent sets of
copied observations read disjoint sets of defect cells and have distinct private bits. -/
theorem rootSupport_disjoint {t : ℕ} {S T : Finset (Obs t)} (h : AncestrallyIndependent S T) :
    Disjoint (rootSupport S) (rootSupport T) := by
  have h' : Disjoint (ancestorsOf S) (ancestorsOf T) := h
  have hanc : ∀ {u v : Obs t}, u ∈ S → v ∈ T → ¬ Disjoint u.ancestors v.ancestors → False := by
    intro u v hu hv hd
    rw [Finset.not_disjoint_iff] at hd
    obtain ⟨a, ha1, ha2⟩ := hd
    have h1 : a ∈ ancestorsOf S := mem_biUnion.mpr ⟨u, hu, ha1⟩
    have h2 : a ∈ ancestorsOf T := mem_biUnion.mpr ⟨v, hv, ha2⟩
    exact (Finset.disjoint_left.mp h' h1) h2
  rw [Finset.disjoint_left]
  intro r hrS hrT
  cases r with
  | inl c =>
      obtain ⟨u, hu, hcu⟩ := mem_rootSupport_inl.mp hrS
      obtain ⟨v, hv, hcv⟩ := mem_rootSupport_inl.mp hrT
      rcases line_inter_ancestors hcu hcv with rfl | hnd
      · refine hanc hu hv ?_
        rw [Finset.not_disjoint_iff]
        obtain ⟨a, ha⟩ := Obs.ancestors_nonempty u
        exact ⟨a, ha, ha⟩
      · exact hanc hu hv hnd
  | inr u =>
      have huS := mem_rootSupport_inr.mp hrS
      have huT := mem_rootSupport_inr.mp hrT
      refine hanc huS huT ?_
      rw [Finset.not_disjoint_iff]
      obtain ⟨a, ha⟩ := Obs.ancestors_nonempty u
      exact ⟨a, ha, ha⟩

/-- Ancestrally independent sets of copied observations are disjoint; each observation is
its own ancestor's descendant, so an observation in both would share ancestry with itself. -/
theorem disjoint_of_ancestrallyIndependent {t : ℕ} (ht : 1 ≤ t) {S T : Finset (Obs t)}
    (h : AncestrallyIndependent S T) : Disjoint S T := by
  have _pos : 0 < t := ht
  have h' : Disjoint (ancestorsOf S) (ancestorsOf T) := h
  rw [Finset.disjoint_left]
  intro u huS huT
  obtain ⟨a, ha⟩ := Obs.ancestors_nonempty u
  have h1 : a ∈ ancestorsOf S := mem_biUnion.mpr ⟨u, huS, ha⟩
  have h2 : a ∈ ancestorsOf T := mem_biUnion.mpr ⟨u, huT, ha⟩
  exact (Finset.disjoint_left.mp h' h1) h2

/-- The restriction of the defect-cube outputs to a set of copied observations depends only
on the root bits in its root support. -/
theorem restrictAssign_outputsOf_congr {t : ℕ} (S : Finset (Obs t)) (x y : Root t → Bool)
    (h : ∀ i ∈ rootSupport S, x i = y i) :
    restrictAssign S (outputsOf x) = restrictAssign S (outputsOf y) := by
  funext v
  obtain ⟨u, hu⟩ := v
  have hpriv : x (Sum.inr u) = y (Sum.inr u) :=
    h _ (mem_rootSupport_inr.mpr hu)
  have hcell : ∀ c : Cell t, onLine u c = true → x (Sum.inl c) = y (Sum.inl c) := by
    intro c hc
    exact h _ (mem_rootSupport_inl.mpr ⟨u, hu, hc⟩)
  simp only [restrictAssign, outputsOf, outputs]
  refine decide_eq_decide.mpr (and_congr ?_ (forall_congr' fun c => ?_))
  · rw [hpriv]
  · exact imp_congr_right fun hc => by rw [hcell c hc]

/-! ## The defect law -/

/-- Pushforwards compose. -/
theorem pushforward_pushforward {α β γ : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    [DecidableEq γ] (w : α → ℝ) (F : α → β) (G : β → γ) :
    pushforward (pushforward w F) G = pushforward w (fun a => G (F a)) := by
  funext c
  simp only [pushforward]
  have hswap : ∀ b : β, (if G b = c then (∑ a, if F a = b then w a else 0) else 0)
      = ∑ a, (if G b = c then (if F a = b then w a else 0) else 0) := by
    intro b
    by_cases hb : G b = c
    · simp [hb]
    · simp [hb]
  rw [Finset.sum_congr rfl fun b _ => hswap b, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single (F a)]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · intro ha
    exact absurd (mem_univ (F a)) ha

/-- `Bern(r)` is a law for `r ∈ [0,1]`. -/
theorem isLaw_bern {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) : IsLaw (bern r) := by
  refine ⟨fun b => ?_, ?_⟩
  · cases b
    · simp only [bern]; norm_num; linarith
    · simpa [bern] using h0
  · rw [Fintype.sum_bool]
    simp [bern]

/-- The per-root weights of the defect cube are laws for `ε, s ∈ [0,1]`. -/
theorem isLaw_rootWeight {t : ℕ} {ε s : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : ∀ i : Root t, IsLaw (rootWeight t ε s i) := by
  intro i
  cases i with
  | inl c => exact isLaw_bern hε0 hε1
  | inr v => exact isLaw_bern hs0 hs1

/-- The defect law is the pushforward of the root product weight along a map of root bits. -/
theorem pushforward_defectLaw {t : ℕ} {ε s : ℝ} {γ : Type*} [DecidableEq γ]
    (G : Assign t → γ) :
    pushforward (defectLaw t ε s) G
      = pushforward (prodLaw (rootWeight t ε s)) (fun x => G (outputsOf x)) := by
  rw [defectLaw, rootLaw, pushforward_pushforward]

/-- Paper Lemma 5.4 (`lem:disjoint`), independence: under the defect law the outputs of two
ancestrally independent sets of copied observations are independent. -/
theorem defect_independence {t : ℕ} {ε s : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {S T : Finset (Obs t)} (h : AncestrallyIndependent S T) :
    pushforward (defectLaw t ε s) (fun ω => (restrictAssign S ω, restrictAssign T ω))
      = fun q => pushforward (defectLaw t ε s) (restrictAssign S) q.1
          * pushforward (defectLaw t ε s) (restrictAssign T) q.2 := by
  rw [pushforward_defectLaw, pushforward_defectLaw (G := restrictAssign S),
    pushforward_defectLaw (G := restrictAssign T)]
  exact indep_of_disjoint_support (isLaw_rootWeight hε0 hε1 hs0 hs1) (rootSupport_disjoint h)
    (fun x y hxy => restrictAssign_outputsOf_congr S x y hxy)
    (fun x y hxy => restrictAssign_outputsOf_congr T x y hxy)

/-- The finite-family form of paper Lemma 5.4, which is what the ancestral-independence
prescriptions of Definition 2.4 require. -/
theorem defect_independence_family {t : ℕ} {ε s : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {n : ℕ} (S : Fin n → Finset (Obs t))
    (h : ∀ m m', m ≠ m' → AncestrallyIndependent (S m) (S m')) :
    pushforward (defectLaw t ε s) (fun ω m => restrictAssign (S m) ω)
      = fun φ : ∀ m : Fin n, (S m) → Bool =>
          ∏ m : Fin n, pushforward (defectLaw t ε s) (restrictAssign (S m)) (φ m) := by
  rw [pushforward_defectLaw]
  have hR : ∀ m : Fin n, pushforward (defectLaw t ε s) (restrictAssign (S m))
      = pushforward (prodLaw (rootWeight t ε s))
          (fun x => restrictAssign (S m) (outputsOf x)) := fun m =>
    pushforward_defectLaw (G := restrictAssign (S m))
  simp only [hR]
  exact indep_of_disjoint_family (isLaw_rootWeight hε0 hε1 hs0 hs1)
    (fun m m' hm => rootSupport_disjoint (h m m' hm))
    (fun m x y hxy => restrictAssign_outputsOf_congr (S m) x y hxy)

end

end TriangleInflation
