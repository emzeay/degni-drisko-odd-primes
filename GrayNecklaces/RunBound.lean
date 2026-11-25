module

public import GrayNecklaces.DeletingWindows

/-!
# The central window's structure and the bound on the run
-/

@[expose] public section

namespace GrayNecklaces

open Tiozzo

section

variable {p σ τ e c : ℕ} (hc : Consec p σ τ) (hs : Split p σ τ e c) (h87 : Theorem87)
  (h9 : TuningNesting) (h4 : σ + 4 ≤ τ)
include hc hs h87 h9 h4

omit h9 h4 in
lemma Split.k_ge : 3 ≤ p - e ∧ 6 * c < 2 ^ (p - e) := by
  have h6 := hs.six_m hc h87
  have hpe : 2 ^ p = 2 ^ e * 2 ^ (p - e) := by rw [← pow_add]; congr 1; have := hs.hep; omega
  rw [hpe] at h6
  have h6' : 6 * c < 2 ^ (p - e) := by
    have : 0 < 2 ^ e := by positivity
    nlinarith
  refine ⟨?_, h6'⟩
  have hc1 : 1 ≤ c := hs.hodd.pos
  by_contra hh; push Not at hh
  have : 2 ^ (p - e) ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- The central window satisfies the hypotheses of the covering lemma. -/
theorem central_struct : Central c (p - e) := by
  have hm := central_max hc hs h87 h4
  have hgood := hm.good h87
  obtain ⟨hk3, h6⟩ := hs.k_ge hc h87
  exact {
    hk := hk3
    ha := hs.hodd
    h6 := h6
    lead := hgood.2.1
    prim := hgood.2.2
    anti := anti_of_max h87 h9 hm h6 hk3
    maxi := fun u d hd2 hdk hu hu3 h1 h2 =>
      hm.not_interior h87 h9 ⟨hd2, by have := hs.hep; omega, hu, hu3⟩ h1 h2 }

omit h9 h4 in
/-- Points `m ± w` near the center cannot be deleted. -/
lemma not_del_near {w n0 : ℕ} (hn0 : 1 ≤ n0) (hn0e : n0 ≤ e) (hw : w = wMid (n0 - 1))
    (hRw : wR c (p - e) * 2 ^ e ≤ w) {s : ℕ} (hsodd : Odd s) (h1 : σ < s) (h2 : s < τ)
    (hsw : (s : ℤ) = c * 2 ^ e + w ∨ (s : ℤ) = c * 2 ^ e - w) :
    ¬ ∃ b j, IsMaxWin p b j ∧ Del p b j s := by
  rintro ⟨b, j, hm, hd⟩
  obtain ⟨hcen1, hcen2, hle, heq, hfin⟩ := classify hc hs h87 hm hd h1 h2
  have hw3 := (wMid_spec (n0 - 1)).1
  rw [show n0 - 1 + 1 = n0 by omega] at hw3
  rw [← hw] at hw3
  rcases eq_or_lt_of_le hle with he | he
  · obtain ⟨hbc, hjk⟩ := heq he
    rw [hbc, hjk] at hd
    have hep := hs.hep
    have hdel := (del_iff (j := p - e) (by omega) (by omega)).mp hd
    rw [show p - (p - e) = e by omega] at hdel
    have : |(s : ℝ) - c * 2 ^ e| = w := by
      have : ((s : ℤ) : ℝ) - ((c * 2 ^ e : ℤ) : ℝ) = (w : ℝ) ∨
          ((s : ℤ) : ℝ) - ((c * 2 ^ e : ℤ) : ℝ) = -(w : ℝ) := by
        rcases hsw with h | h <;> [left; right] <;> rw [h] <;> push_cast <;> ring
      push_cast at this
      rcases this with h | h <;> rw [h]
      · exact abs_of_nonneg (by positivity)
      · rw [abs_neg]; exact abs_of_nonneg (by positivity)
    rw [this] at hdel
    linarith [hdel.2]
  · have h5 := hfin he
    obtain ⟨q, hq⟩ : ∃ q : ℕ, 2 ^ (p - j) = q := ⟨_, rfl⟩
    have hqR : (2 : ℝ) ^ (p - j) = q := by rw [← hq]; push_cast; ring
    rw [hqR] at h5
    have hq2 : 2 ≤ q := by rw [← hq]; exact two_le_two_pow (by have := hm.1.2.1; omega)
    have hmq : (c * 2 ^ e : ℤ) = 2 * q * (c * 2 ^ (e - (p - j) - 1)) := by
      have : (2 : ℤ) ^ e = 2 * 2 ^ (p - j) * 2 ^ (e - (p - j) - 1) := by
        rw [← pow_succ', ← pow_add]; congr 1; omega
      rw [this, show (2 : ℤ) ^ (p - j) = q by rw [← hq]; push_cast; ring]; ring
    obtain ⟨β, hβ⟩ := hm.1.2.2.1
    set X : ℤ := c * 2 ^ (e - (p - j) - 1)
    have hcq : ((b * 2 ^ (p - j) : ℕ) : ℤ) = q * (2 * β + 1) := by
      rw [hβ, hq]; push_cast; ring
    -- `x = s - cen` as an integer
    obtain ⟨x, hx⟩ : ∃ x : ℤ, x = (s : ℤ) - q * (2 * β + 1) := ⟨_, rfl⟩
    have hxR : |(s : ℝ) - b * q| = ((|x| : ℤ) : ℝ) := by
      rw [hx, hβ]; push_cast; ring_nf
    rw [hxR] at h5
    have h5' : 5 * |x| < (q : ℤ) := by
      have : ((5 * |x| : ℤ) : ℝ) < ((q : ℤ) : ℝ) := by push_cast at h5 ⊢; linarith
      exact_mod_cast this
    -- `x` is odd
    have hxodd : 1 ≤ |x| := by
      have hev : Even ((q : ℤ) * (2 * β + 1)) := Even.mul_right (by
          rw [← hq]; push_cast; exact Int.even_pow.mpr ⟨even_two, by have := hm.1.2.1; omega⟩) _
      have : Odd x := by rw [hx]; exact (Int.odd_natCast s |>.mpr hsodd).sub_even hev
      obtain ⟨r, hr⟩ := this
      rw [hr]; rcases le_or_gt 0 r with h | h
      · rw [abs_of_nonneg (by omega)]; omega
      · rw [abs_of_neg (by omega)]; omega
    rcases Nat.lt_or_ge q (2 ^ n0) with hqn | hqn
    · -- distance at least `(q-1)/3` from odd multiples
      have hg : p - j ≤ n0 - 1 := by
        by_contra hh; push Not at hh
        have : 2 ^ n0 ≤ 2 ^ (p - j) := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      have hod := oddDist_wMid (k := n0 - 1) (g := p - j) hg
      rw [← hw, hq] at hod
      have hle1 : oddDist q (w : ℤ) ≤ |x| := by
        rcases hsw with h | h
        · have := oddDist_le_abs (t := q) (by omega) (w : ℤ) (β - X)
          have e1 : (w : ℤ) - q * (2 * (β - X) + 1) = x := by
            rw [hx, h, hmq]; ring
          rw [e1] at this; exact this
        · have := oddDist_le_abs (t := q) (by omega) (-(w : ℤ)) (β - X)
          rw [oddDist_neg] at this
          have e1 : -(w : ℤ) - q * (2 * (β - X) + 1) = x := by
            rw [hx, h, hmq]; ring
          rw [e1] at this; exact this
      have hqZ : ((q : ℕ) : ℤ) - 1 ≤ 3 * oddDist q (w : ℤ) := by
        have : ((2 ^ (p - j) : ℕ) : ℤ) = (2 : ℤ) ^ (p - j) := by push_cast; ring
        rw [hq] at this; rw [this]; exact hod
      omega
    · -- far from the finer center
      have hdist := dist_odd_mult (q := (q : ℤ)) (X := X) (β := β) (by positivity)
      rw [← hmq] at hdist
      have hfar : (q : ℤ) - w ≤ |x| := by
        have h1 := abs_sub_abs_le_abs_sub ((c * 2 ^ e : ℤ) - q * (2 * β + 1)) x
        have h2 : |((c * 2 ^ e : ℤ) - q * (2 * β + 1)) - x| = w := by
          rw [hx]
          rcases hsw with h | h <;> rw [h]
          · rw [show (c * 2 ^ e : ℤ) - q * (2 * β + 1) - (c * 2 ^ e + w - q * (2 * β + 1)) = -w by ring,
              abs_neg]; simp
          · rw [show (c * 2 ^ e : ℤ) - q * (2 * β + 1) - (c * 2 ^ e - w - q * (2 * β + 1)) = w by ring]
            simp
        linarith
      have : 3 * (w : ℤ) ≤ q + 1 := by
        have : (2 ^ n0 : ℤ) ≤ q := by exact_mod_cast hqn
        rcases hw3 with h | h
        · have : (3 * w + 1 : ℤ) = 2 ^ n0 := by exact_mod_cast h
          linarith
        · have : (3 * w : ℤ) = 2 ^ n0 + 1 := by exact_mod_cast h
          linarith
      omega

omit h9 in
/-- **The bound on the run.** -/
theorem run_bound : ∃ w : ℕ, Odd w ∧ 3 * w ≤ 2 ^ e + 1 ∧ c * 2 ^ e ≤ σ + w ∧
    τ ≤ c * 2 ^ e + w ∧ wR c (p - e) * 2 ^ e ≤ w := by
  classical
  have he1 := hs.e_pos hc h4
  obtain ⟨hk3, h6⟩ := hs.k_ge hc h87
  set k := p - e
  set RQ := wR c k * 2 ^ e
  have hRpos : 0 < RQ := mul_pos (wR_pos hs.hodd.pos (by omega)) (by positivity)
  have hwit : RQ ≤ ((2 : ℝ) ^ e - 1) / 3 := by
    simp only [RQ]; unfold wR
    have h62 : 6 * c + 2 ≤ 2 ^ k := by
      have hodd : Odd (2 ^ k - 1) := by
        have : 2 ^ k = 2 * 2 ^ (k - 1) := by rw [← pow_succ']; congr 1; omega
        have : 1 ≤ 2 ^ (k - 1) := Nat.one_le_two_pow
        exact ⟨2 ^ (k - 1) - 1, by omega⟩
      obtain ⟨t, ht⟩ := hodd; omega
    have h62' : (6 * c : ℝ) + 2 ≤ 2 ^ k := by exact_mod_cast h62
    have hk8 : (8 : ℝ) ≤ 2 ^ k := by
      have : (2:ℝ) ^ 3 ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk3
      norm_num at this; linarith
    have he2 : (2 : ℝ) ≤ 2 ^ e := by
      have := pow_le_pow_right₀ (show (1:ℝ) ≤ 2 by norm_num) he1; simpa using this
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by linarith) (by norm_num)]
    nlinarith
  have hexP : ∃ n : ℕ, RQ ≤ ((2 : ℝ) ^ n - 1) / 3 := ⟨e, hwit⟩
  set n0 := Nat.find hexP
  have hn0 : RQ ≤ ((2 : ℝ) ^ n0 - 1) / 3 := Nat.find_spec hexP
  have hn0e : n0 ≤ e := Nat.find_min' hexP hwit
  have hn01 : 1 ≤ n0 := by
    by_contra hh; push Not at hh
    have : n0 = 0 := by omega
    rw [this] at hn0; norm_num at hn0; linarith
  set w := wMid (n0 - 1)
  have hw3 := (wMid_spec (n0 - 1)).1
  rw [show n0 - 1 + 1 = n0 by omega] at hw3
  have hwodd : Odd w := wMid_odd _
  have hRw : RQ ≤ w := by
    have : ((2 : ℝ) ^ n0 - 1) / 3 ≤ w := by
      rcases hw3 with h | h
      · have : ((3 * w + 1 : ℕ) : ℝ) = ((2 ^ n0 : ℕ) : ℝ) := by rw [h]
        push_cast at this; linarith
      · have : ((3 * w : ℕ) : ℝ) = ((2 ^ n0 + 1 : ℕ) : ℝ) := by rw [h]
        push_cast at this; linarith
    linarith
  have hw3e : 3 * w ≤ 2 ^ e + 1 := by
    have : 2 ^ n0 ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) hn0e
    rcases hw3 with h | h <;> omega
  have hmeven : Even (c * 2 ^ e) := (Nat.even_pow.mpr ⟨even_two, by omega⟩).mul_left c
  refine ⟨w, hwodd, hw3e, ?_, ?_, hRw⟩
  · -- `m - w ≤ σ`
    by_contra hh
    push Not at hh
    have h1 : σ < c * 2 ^ e - w := by omega
    have hodd' : Odd (c * 2 ^ e - w) := by
      obtain ⟨r, hr⟩ := hmeven; obtain ⟨t, ht⟩ := hwodd; exact ⟨r - t - 1, by omega⟩
    have h2 : c * 2 ^ e - w < τ := by have := hs.h2; omega
    obtain ⟨b, j, hm, hd⟩ := hc.gap_deleted h87 hodd' h1 h2
    exact not_del_near hc hs h87 hn01 hn0e rfl hRw hodd' h1 h2
      (Or.inr (by push_cast [show w ≤ c * 2 ^ e by omega]; ring)) ⟨b, j, hm, hd⟩
  · -- `τ ≤ m + w`
    by_contra hh
    push Not at hh
    have h1 : σ < c * 2 ^ e + w := by have := hs.h1; omega
    have hodd' : Odd (c * 2 ^ e + w) := hmeven.add_odd hwodd
    obtain ⟨b, j, hm, hd⟩ := hc.gap_deleted h87 hodd' h1 hh
    exact not_del_near hc hs h87 hn01 hn0e rfl hRw hodd' h1 hh
      (Or.inl (by push_cast; ring)) ⟨b, j, hm, hd⟩

end

end GrayNecklaces
