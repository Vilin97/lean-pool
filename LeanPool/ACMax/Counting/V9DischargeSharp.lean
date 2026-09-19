/-
Copyright (c) 2026 Zeru Zhu, Jinzheng Li, Yuanjie Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zeru Zhu, Jinzheng Li, Yuanjie Ren
-/
import LeanPool.ACMax.Counting.V9Discharge
import LeanPool.ACMax.Counting.MoatSharp

/-!
# The import-free starved kill at `n ≥ 123` (bulk-credited moat)

`Counting/V9Discharge.lean` closes the starved census import-free from `n ≥ 388`, at ball radius
`r = ⌊(⌊(n+8)/9⌋ − 1)/2⌋` — the radius the *old* moat threshold `9k ≤ n + 8` allows.

`Counting/MoatSharp.lean` sharpens that threshold to `12k + X ≤ 2n` by keeping the bulk excess
`Σ_{S₂}(deg − 3)` that `master_cycle_fires` discards.  The admissible radius rises to

  `r = ⌊(2n − X − 12)/24⌋`,

and re-running the same discharge with it drops the import-free threshold from `388` to **`123`**.

**Why `123`.**  The integer condition `|V₉|² < |V₉|(2r+1) + t₉(3r² − r)` holds on the whole
counting region from `n = 111` upward; the discharge below makes the same two relaxations as the
`388` route — `r` replaced by its uniform lower bound (`24r ≥ 2n − X − 35`, dropping `⌊·⌋`) and the
region replaced by an `H`-monotone endpoint — landing the *proved* threshold at `123`.

**Route.**  Unlike the `388` version, the radius now depends on `X`, so the excess term carries
`A = 2N − X − 35` rather than an `X`-free square.  Both `t₉` and `A` are bounded below by `X`-free
linear forms that are *simultaneously* tight at `X = X_max`, so pushing `X` to the master maximum
costs nothing:  `10·t₉ ≥ 6N + 160 − 23H` and `10·A ≥ 16N + 7H − 150`.  What remains is a two-
variable cubic that is monotone decreasing in `H` (every `H`-coefficient is negative at `N ≥ 123`),
so its minimum sits at `17H = 4N − 200`; there `4913·gap − cubic` splits *exactly* as a sum of
three manifestly non-negative products, and `strip_cubic_sharp` closes.
-/

namespace ACMax

open Finset

/-! ## The arithmetic core -/

open Classical in
/-- **The sharp strip cubic.**  The single-variable inequality the `n ≥ 123` region arithmetic
bottoms out at, after `X` is pushed to its master maximum and `H` to the end of its range.
Substituting `N = 123 + u` makes every coefficient non-negative
(`1068496017 + 1122649307u + 11552736u² + 20700u³`), which is what `nlinarith` finds. -/
theorem strip_cubic_sharp {N : ℤ} (hN : 123 ≤ N) :
    779812849 * N + 755972700 < 20700 * N ^ 3 + 3914436 * N ^ 2 := by
  have hu : (0 : ℤ) ≤ N - 123 := by linarith
  nlinarith [hu, mul_nonneg hu hu, mul_nonneg (mul_nonneg hu hu) hu]

open Classical in
/-- **The two-variable core.**  After both `X`-eliminations the target is a cubic in `(N, H)`:

  `4608000·(N−H)² < 38400·(N−H)·(Q+120) + 23·P·Q²`,  `P = 6N+160−23H`, `Q = 16N+7H−150`.

Every `H`-coefficient of the gap is negative at `N ≥ 123`, so the minimum is at `17H = 4N − 200`,
and `4913·gap − cubic` is *identically* `289(M−17H)(−c₁) + 17(M²−(17H)²)(−c₂) + (M³−(17H)³)·25921`
with `M = 4N − 200`, `−c₁ = 104512N² − 11944120N + 18478500 ≥ 0` (its larger root is `≈ 112.7`)
and `−c₂ = 111734N + 3585580 ≥ 0`.  So `linarith` closes on those three products plus the cubic. -/
theorem moore_strip_twovar_sharp {N H : ℤ} (hN : 123 ≤ N) (hH : 0 ≤ H)
    (hs : 17 * H ≤ 4 * N - 200) :
    4608000 * (N - H) ^ 2
      < 38400 * ((N - H) * (16 * N + 7 * H - 30))
        + 23 * ((6 * N + 160 - 23 * H) * (16 * N + 7 * H - 150) ^ 2) := by
  have hd : (0 : ℤ) ≤ (4 * N - 200) - 17 * H := by linarith
  have hHm : (0 : ℤ) ≤ 17 * H := by linarith
  have hnc1 : (0 : ℤ) ≤ 104512 * N ^ 2 - 11944120 * N + 18478500 := by nlinarith [hN]
  have hnc2 : (0 : ℤ) ≤ 111734 * N + 3585580 := by linarith
  have hsq : (0 : ℤ) ≤ (4 * N - 200) ^ 2 + 17 * H * (4 * N - 200) + (17 * H) ^ 2 := by
    nlinarith [hHm, hd, sq_nonneg (4 * N - 200), sq_nonneg (17 * H)]
  have e1 := mul_nonneg hd hnc1
  have e2 := mul_nonneg (mul_nonneg hd (by linarith : (0 : ℤ) ≤ (4 * N - 200) + 17 * H)) hnc2
  have e3 := mul_nonneg (mul_nonneg hd hsq) (by norm_num : (0 : ℤ) ≤ 25921)
  have hcub := strip_cubic_sharp hN
  linarith [e1, e2, e3, hcub]

open Classical in
/-- **The `R`-free core of the sharp strip discharge.**  On the counting region
(`0 ≤ H ≤ X`, `10X + 7H ≤ 4N − 200`) at `N ≥ 123`,

  `4608·(N−H)² < 384·(N−H)·(2N−X−23) + 23·(N−4−X−3H)·(2N−X−35)²`.

Both `X`-dependent factors are pushed to the master maximum simultaneously — `10·t ≥ 6N+160−23H`
and `10·A ≥ 16N+7H−150`, equalities together at `X = X_max` — and `moore_strip_twovar_sharp`
closes what is left. -/
theorem moore_strip_core_sharp {N X H : ℤ} (hN : 123 ≤ N) (hH : 0 ≤ H) (hHX : H ≤ X)
    (hmaster : 10 * X + 7 * H ≤ 4 * N - 200) :
    4608 * (N - H) ^ 2
      < 384 * ((N - H) * (2 * N - X - 23))
        + 23 * ((N - 4 - X - 3 * H) * (2 * N - X - 35) ^ 2) := by
  have h17 : 17 * H ≤ 4 * N - 200 := by linarith
  have hvpos : (0 : ℤ) ≤ N - H := by linarith
  have hPpos : (0 : ℤ) ≤ 6 * N + 160 - 23 * H := by linarith
  have hQpos : (0 : ℤ) ≤ 16 * N + 7 * H - 150 := by linarith
  have hP : 6 * N + 160 - 23 * H ≤ 10 * (N - 4 - X - 3 * H) := by linarith
  have hQ : 16 * N + 7 * H - 150 ≤ 10 * (2 * N - X - 35) := by linarith
  -- the ball factor, pushed to the master maximum
  have hA : 38400 * ((N - H) * (16 * N + 7 * H - 30))
      ≤ 1000 * (384 * ((N - H) * (2 * N - X - 23))) := by nlinarith [hvpos, hQ]
  -- the excess factor, pushed to the master maximum
  have hQ2 : (16 * N + 7 * H - 150) ^ 2 ≤ (10 * (2 * N - X - 35)) ^ 2 := by
    nlinarith [hQpos, hQ]
  have hmul : (6 * N + 160 - 23 * H) * (16 * N + 7 * H - 150) ^ 2
      ≤ (10 * (N - 4 - X - 3 * H)) * (10 * (2 * N - X - 35)) ^ 2 :=
    mul_le_mul hP hQ2 (sq_nonneg _) (by linarith)
  have hB : 23 * ((6 * N + 160 - 23 * H) * (16 * N + 7 * H - 150) ^ 2)
      ≤ 1000 * (23 * ((N - 4 - X - 3 * H) * (2 * N - X - 35) ^ 2)) := by nlinarith [hmul]
  have htv := moore_strip_twovar_sharp hN hH h17
  linarith [hA, hB, htv]

open Classical in
/-- **The sharp strip Moore arithmetic.**  On the counting region, `MASTER′` together with
`H ≤ X`, `N ≥ 123` and the sharpened radius bound `2N − X − 35 ≤ 24R` forces the SQRT side
condition

  `(N − H)² < (N − H)(2R + 1) + (N − 4 − X − 3H)(3R² − R)`.

Route: `moore_strip_core_sharp` supplies the `R`-free inequality; then `12(2R+1) ≥ 2N−X−23`
upgrades the ball term and `23(2N−X−35)² ≤ 4608(3R²−R)` the excess term (from `(2N−X−35)² ≤
576R²` and `23R² ≤ 8(3R²−R)`, the latter by `R ≥ 8`), both by the same factor `4608 = 384·12`. -/
theorem moore_strip_arith_sharp {N X H R : ℤ} (hN : 123 ≤ N)
    (hH : 0 ≤ H) (hHX : H ≤ X) (hR : 2 * N - X - 35 ≤ 24 * R)
    (hmaster : 10 * X + 7 * H ≤ 4 * N - 200) :
    (N - H) ^ 2 < (N - H) * (2 * R + 1) + (N - 4 - X - 3 * H) * (3 * R ^ 2 - R) := by
  have hR8 : (8 : ℤ) ≤ R := by omega
  have hvpos : (0 : ℤ) ≤ N - H := by linarith
  have hq : (0 : ℤ) ≤ N - 4 - X - 3 * H := by linarith
  have hApos : (0 : ℤ) ≤ 2 * N - X - 35 := by linarith
  have hcore := moore_strip_core_sharp hN hH hHX hmaster
  -- the ball term: `12(2R + 1) = 24R + 12 ≥ 2N − X − 23`
  have hball : (N - H) * (2 * N - X - 23) ≤ 12 * ((N - H) * (2 * R + 1)) := by
    nlinarith [hvpos, hR]
  -- the excess term
  have hsq : (2 * N - X - 35) ^ 2 ≤ 576 * R ^ 2 := by nlinarith [hR, hApos]
  have hRR : 23 * R ^ 2 ≤ 8 * (3 * R ^ 2 - R) := by nlinarith [hR8]
  have hexc : 23 * (2 * N - X - 35) ^ 2 ≤ 4608 * (3 * R ^ 2 - R) := by nlinarith [hsq, hRR]
  have hB : 23 * ((N - 4 - X - 3 * H) * (2 * N - X - 35) ^ 2)
      ≤ 4608 * ((N - 4 - X - 3 * H) * (3 * R ^ 2 - R)) := by nlinarith [hq, hexc]
  linarith [hcore, hball, hB]

/-! ## The graph-level dispatch -/

open Classical in
/-- **The sharpened tier-9 girth.**  In a never-firing starved census, `V₉` contains no cycle of
length `k` with `12k + X ≤ 2n` — against `9k ≤ n + 8` for `v9_girth`. -/
theorem v9_girth_sharp {n : ℕ} [Nonempty (Fin n)] {k : ℕ} [NeZero k]
    (G : SimpleGraph (Fin n)) (hm : G.edgeFinset.card = 2 * (n - 2))
    (h3 : ∀ v : Fin n, 3 ≤ G.degree v) (hnf : ¬ algConn G ≤ 2)
    (hk : 3 ≤ k) (hn8 : 8 ≤ n) (hkn : 12 * k + excessX n G ≤ 2 * n) (c : ZMod k → Fin n)
    (hcinj : Function.Injective c) (hadj : ∀ i : ZMod k, G.Adj (c i) (c (i + 1)))
    (hmem : ∀ i : ZMod k, c i ∈ v9Set G) : False :=
  hnf (v9_short_cycle_fires_sharp hk G hm h3 c hcinj hadj
    (fun i => mem_v9Set.mp (hmem i)) hn8 hkn)

open Classical in
/-- **The rebased tier-9 kill at the sharpened moat obligation.**  Identical to
`starved_v9_kill_sqrt` except that the moat obligation is `12(2r+1) + X ≤ 2n` rather than
`9(2r+1) ≤ n + 8`: the cycle the ball count produces has length at most `2r + 1`, and a `V₉`-cycle
that short fires `v9_short_cycle_fires_sharp`. -/
theorem starved_v9_kill_sharp {n : ℕ} [Nonempty (Fin n)] (G : SimpleGraph (Fin n))
    (hlo : 55 ≤ n) (hm : G.edgeFinset.card = 2 * (n - 2))
    (h3 : ∀ v : Fin n, 3 ≤ G.degree v) (hnf : ¬ algConn G ≤ 2)
    (hpos : excessX n G + 3 * (v9Set G)ᶜ.card + 5 ≤ n)
    (r : ℕ) (hr1 : 1 ≤ r) (hrn : 12 * (2 * r + 1) + excessX n G ≤ 2 * n)
    (hMoore : (v9Set G).card ^ 2
      < (v9Set G).card * (2 * r + 1)
        + (n - 4 - excessX n G - 3 * (v9Set G)ᶜ.card) * (3 * r ^ 2 - r)) : False := by
  set t9 : ℕ := n - 4 - excessX n G - 3 * (v9Set G)ᶜ.card with ht9def
  have hRsub : (v9Set G)ᶜ ⊆ Finset.univ.filter (fun w => 5 ≤ G.degree w) := by
    intro v hv
    rw [Finset.mem_compl, mem_v9Set] at hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ v, by omega⟩
  have hRcard : (v9Set G)ᶜ.card ≤ excessX n G :=
    le_trans (Finset.card_le_card hRsub) (heavy_le_excess G)
  have hexc : 2 * (v9Set G).card + 2 * t9 ≤ v9Pairs G := by
    have hq := v9_density_row_quant G (by omega) hm
    rw [ht9def]
    omega
  have ht1 : 1 ≤ t9 := by rw [ht9def]; omega
  have hne : (v9Set G).Nonempty := by
    rw [← Finset.card_pos]
    have hsize := v9_size_row G
    omega
  obtain ⟨k, hk3, hkr, c, hcinj, hadj, hmem⟩ :=
    girth_excess_bound_holds n G (v9Set G) t9 r hne ht1 hr1 hexc hMoore
  have : NeZero k := ⟨by omega⟩
  exact v9_girth_sharp G hm h3 hnf hk3 (by omega) (by omega) c hcinj hadj hmem

open Classical in
/-- **D3′ — the import-free starved kill at `n ≥ 123`.**  A never-firing starved census
(`m = 2(n−2)`, `δ ≥ 3`, `hs0`) on `123 ≤ n` cannot exist, with no external girth byline.  Same
single branch as `starved_dead_ge_388`, run at the bulk-credited radius
`r = ⌊(2n − X − 12)/24⌋` and discharged by `moore_strip_arith_sharp`. -/
theorem starved_dead_ge_123 {n : ℕ} [Nonempty (Fin n)] (G : SimpleGraph (Fin n))
    (hn : 123 ≤ n) (hm : G.edgeFinset.card = 2 * (n - 2))
    (h3 : ∀ v : Fin n, 3 ≤ G.degree v) (hnf : ¬ algConn G ≤ 2)
    (hs0 : ∀ v w : Fin n, G.degree v = 3 → G.degree w = 3 → ¬G.Adj v w) : False := by
  have hD1 := slots_p_row G (by omega) hm h3 hnf hs0
  have hPC := p_choke_row_unconditional (by omega) G hm h3 hs0 hnf
  have hbud := heavy_full_budget G (by omega)
  have hMaster : 10 * excessX n G + 7 * (v9Set G)ᶜ.card ≤ 4 * n - 200 := by omega
  have hhX : (v9Set G)ᶜ.card ≤ excessX n G := by
    have hRsub : (v9Set G)ᶜ ⊆ Finset.univ.filter (fun w => 5 ≤ G.degree w) := by
      intro v hv
      rw [Finset.mem_compl, mem_v9Set] at hv
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ v, by omega⟩
    exact le_trans (Finset.card_le_card hRsub) (heavy_le_excess G)
  have hpos : excessX n G + 3 * (v9Set G)ᶜ.card + 5 ≤ n := by omega
  -- the bulk-credited ball radius `r = ⌊(2n − X − 12)/24⌋`
  set Xe := excessX n G with hXe
  set Hc := (v9Set G)ᶜ.card with hHc
  have hr1 : 1 ≤ (2 * n - Xe - 12) / 24 := by omega
  have hrn : 12 * (2 * ((2 * n - Xe - 12) / 24) + 1) + Xe ≤ 2 * n := by omega
  have hr24 : 2 * n - Xe - 35 ≤ 24 * ((2 * n - Xe - 12) / 24) := by omega
  have hVhh : (v9Set G).card + Hc = n := by
    rw [hHc, Finset.card_add_card_compl, Fintype.card_fin]
  have hMoore : (v9Set G).card ^ 2
      < (v9Set G).card * (2 * ((2 * n - Xe - 12) / 24) + 1)
        + (n - 4 - Xe - 3 * Hc)
          * (3 * ((2 * n - Xe - 12) / 24) ^ 2 - ((2 * n - Xe - 12) / 24)) := by
    set Vc := (v9Set G).card with hVc
    set Rl := (2 * n - Xe - 12) / 24 with hRl
    -- make the radius opaque: `omega` must not reason under the nested `⌊·⌋`
    clear_value Rl
    clear hRl
    obtain ⟨q, hq⟩ : ∃ q, n = 4 + Xe + 3 * Hc + q := ⟨n - (4 + Xe + 3 * Hc), by omega⟩
    have e1 : n - 4 - Xe - 3 * Hc = q := by omega
    have e2 : Vc = 4 + Xe + 2 * Hc + q := by omega
    have hkey := moore_strip_arith_sharp (N := (n : ℤ)) (X := (Xe : ℤ)) (H := (Hc : ℤ))
      (R := (Rl : ℤ)) (by exact_mod_cast hn) (Int.natCast_nonneg _)
      (Nat.cast_le.mpr hhX) (by omega) (by omega)
    have hnZ : (n : ℤ) = 4 + (Xe : ℤ) + 3 * (Hc : ℤ) + (q : ℤ) := by exact_mod_cast hq
    have ea : (n : ℤ) - (Hc : ℤ) = 4 + (Xe : ℤ) + 2 * (Hc : ℤ) + (q : ℤ) := by rw [hnZ]; ring
    have eb : (n : ℤ) - 4 - (Xe : ℤ) - 3 * (Hc : ℤ) = (q : ℤ) := by rw [hnZ]; ring
    rw [ea, eb] at hkey
    have hle : Rl ≤ 3 * Rl ^ 2 :=
      calc Rl = Rl * 1 := (Nat.mul_one Rl).symm
        _ ≤ Rl * (3 * Rl) := Nat.mul_le_mul_left Rl (by omega)
        _ = 3 * Rl ^ 2 := by ring
    set w := 3 * Rl ^ 2 - Rl with hwdef
    have hw : 3 * Rl ^ 2 = w + Rl := by rw [hwdef, Nat.sub_add_cancel hle]
    have hwZ : (3 : ℤ) * (Rl : ℤ) ^ 2 - (Rl : ℤ) = (w : ℤ) := by
      have hcast : ((3 * Rl ^ 2 : ℕ) : ℤ) = ((w + Rl : ℕ) : ℤ) := by exact_mod_cast hw
      push_cast at hcast
      linarith
    rw [hwZ] at hkey
    rw [e1, e2]
    exact_mod_cast hkey
  exact starved_v9_kill_sharp G (by omega) hm h3 hnf hpos ((2 * n - Xe - 12) / 24) hr1 hrn hMoore

end ACMax
