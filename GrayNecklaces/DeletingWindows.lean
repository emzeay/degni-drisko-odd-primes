module

public import GrayNecklaces.CentralMaximal

/-!
# Classification of deleting windows and the central window
-/

@[expose] public section

namespace GrayNecklaces

open Tiozzo

/-- The dyadic split data of `σ < τ`. -/
structure Split (p σ τ e c : ℕ) : Prop where
  hep : e < p
  h1 : σ < c * 2 ^ e
  h2 : c * 2 ^ e < τ
  h3 : (c - 1) * 2 ^ e ≤ σ
  h4 : τ ≤ (c + 1) * 2 ^ e
  hodd : Odd c
  hmax : ∀ e' c' : ℕ, σ < c' * 2 ^ e' → c' * 2 ^ e' < τ → e' ≤ e

lemma wMid_odd (k : ℕ) : Odd (wMid k) := by
  rcases Nat.eq_zero_or_pos k with h0 | hk
  · subst h0; decide
  · have hm := two_pow_mod_three (k + 1)
    have h4 : 4 ∣ 2 ^ (k + 1) := by
      rw [show 4 = 2 ^ 2 by norm_num]; exact Nat.pow_dvd_pow 2 (by omega)
    obtain ⟨r, hr⟩ := h4
    unfold wMid
    split_ifs with he
    · rw [ite_eq_left he] at hm
      exact Nat.odd_iff.mpr (by omega)
    · rw [ite_eq_right he] at hm
      exact Nat.odd_iff.mpr (by omega)

section

variable {p σ τ e c : ℕ} (hc : Consec p σ τ) (hs : Split p σ τ e c) (h87 : Theorem87)
include hc hs h87

lemma Split.six_m : 6 * (c * 2 ^ e) < 2 ^ p := by
  have := hc.τ_le h87; have := hs.h2; omega

lemma Split.eight_Q : 8 * 2 ^ e ≤ 2 ^ p := by
  have h6 := hs.six_m hc h87
  have hc1 : 1 ≤ c := hs.hodd.pos
  have : 2 ^ e ≤ c * 2 ^ e := Nat.le_mul_of_pos_left _ hc1
  have : 6 * 2 ^ e < 2 ^ p := by omega
  have hpe : 2 ^ p = 2 ^ e * 2 ^ (p - e) := by rw [← pow_add]; congr 1; have := hs.hep; omega
  rw [hpe] at this ⊢
  have : 6 < 2 ^ (p - e) := by nlinarith [Nat.one_le_two_pow (n := e)]
  have : 8 ≤ 2 ^ (p - e) := by
    by_contra hh; push Not at hh
    have : 2 ^ (p - e) < 2 ^ 3 := by omega
    have := (Nat.pow_lt_pow_iff_right (by norm_num)).mp this
    have : 2 ^ (p - e) ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  nlinarith

/-- Classification of a maximal window deleting a point between the leaders. -/
lemma classify {b j s : ℕ} (hm : IsMaxWin p b j) (hd : Del p b j s) (h1 : σ < s) (h2 : s < τ) :
    σ < b * 2 ^ (p - j) ∧ b * 2 ^ (p - j) < τ ∧ p - j ≤ e ∧
      (p - j = e → b = c ∧ j = p - e) ∧
      (p - j < e → 5 * |(s : ℝ) - b * 2 ^ (p - j)| < 2 ^ (p - j)) := by
  obtain ⟨hcen1, hcen2⟩ := hc.center_between h87 hm hd h1 h2
  have hj : 1 ≤ j := by have := hm.1.1; omega
  have hjp := hm.1.2.1
  have hle : p - j ≤ e := hs.hmax (p - j) b hcen1 hcen2
  refine ⟨hcen1, hcen2, hle, ?_, ?_⟩
  · intro he
    rw [he] at hcen1 hcen2
    have h3 := hs.h3; have h4 := hs.h4
    have hP : 0 < 2 ^ e := by positivity
    have hbc1 : c - 1 < b := by
      by_contra hh; push Not at hh
      have := Nat.mul_le_mul_right (2 ^ e) hh; omega
    have hbc2 : b < c + 1 := by
      by_contra hh; push Not at hh
      have := Nat.mul_le_mul_right (2 ^ e) hh; omega
    refine ⟨by omega, by omega⟩
  · intro hlt
    have hdel := (del_iff_cen hj hjp).mp hd
    have hτ := hc.τ_le h87
    have h8 := hs.eight_Q hc h87
    have hqle : 2 * 2 ^ (p - j) ≤ 2 ^ e := by
      rw [← pow_succ']; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have h16 : (16 : ℝ) * 2 ^ (p - j) ≤ 2 ^ p := by
      have : 16 * 2 ^ (p - j) ≤ 2 ^ p := by omega
      exact_mod_cast this
    have hcen6 : (6 : ℝ) * (b * 2 ^ (p - j)) < 2 ^ p := by
      have : 6 * (b * 2 ^ (p - j)) < 2 ^ p := by omega
      exact_mod_cast this
    have hq : (0 : ℝ) < 2 ^ (p - j) := by positivity
    by_contra hh
    push Not at hh
    have := hdel.2
    have hcen0 : (0 : ℝ) ≤ b * 2 ^ (p - j) := by positivity
    nlinarith [abs_nonneg ((s : ℝ) - b * 2 ^ (p - j))]

omit h87 in
/-- The run is nonempty: `e ≥ 1`. -/
lemma Split.e_pos (h4 : σ + 4 ≤ τ) : 1 ≤ e := by
  have hσ := hc.σ_odd
  obtain ⟨t, ht⟩ := hσ
  have := hs.hmax 1 (t + 1) (by omega) (by omega)
  exact this

/-- The central window `c / 2^(p-e)` is maximal. -/
theorem central_max (h4 : σ + 4 ≤ τ) : IsMaxWin p c (p - e) := by
  have he1 := hs.e_pos hc h4
  have hσ := hc.σ_odd
  have hmeven : Even (c * 2 ^ e) := (Nat.even_pow.mpr ⟨even_two, by omega⟩).mul_left c
  -- one of `m ± 1` lies strictly between the leaders
  obtain ⟨s0, hs0o, hs01, hs02, hs0m⟩ : ∃ s0, Odd s0 ∧ σ < s0 ∧ s0 < τ ∧
      ((s0 : ℤ) = c * 2 ^ e + 1 ∨ (s0 : ℤ) = c * 2 ^ e - 1) := by
    have h1 := hs.h1; have h2 := hs.h2
    obtain ⟨r, hr⟩ := hmeven
    by_cases hh : c * 2 ^ e + 1 < τ
    · exact ⟨c * 2 ^ e + 1, ⟨r, by omega⟩, by omega, hh, Or.inl (by push_cast; ring)⟩
    · refine ⟨c * 2 ^ e - 1, ⟨r - 1, by omega⟩, ?_, by omega, Or.inr (by push_cast [show 1 ≤ c * 2 ^ e by omega]; ring)⟩
      obtain ⟨t, ht⟩ := hσ; obtain ⟨t', ht'⟩ := hc.τ_odd
      omega
  obtain ⟨b, j, hm, hd⟩ := hc.gap_deleted h87 hs0o hs01 hs02
  obtain ⟨hcen1, hcen2, hle, heq, hfin⟩ := classify hc hs h87 hm hd hs01 hs02
  rcases eq_or_lt_of_le hle with he | he
  · obtain ⟨rfl, rfl⟩ := heq he; exact hm
  · exfalso
    have h5 := hfin he
    set q := 2 ^ (p - j) with hq
    have hq2 : 2 ≤ q := two_le_two_pow (by have := hm.1.2.1; omega)
    -- `m` is a multiple of `2q` and the center an odd multiple of `q`
    have hmq : (c * 2 ^ e : ℤ) = 2 * q * (c * 2 ^ (e - (p - j) - 1)) := by
      have : (2 : ℤ) ^ e = 2 * 2 ^ (p - j) * 2 ^ (e - (p - j) - 1) := by
        rw [← pow_succ', ← pow_add]; congr 1; omega
      rw [this, hq]; push_cast; ring
    obtain ⟨β, hβ⟩ := hm.1.2.2.1
    have hcq : ((b * q : ℕ) : ℤ) = q * (2 * β + 1) := by rw [hβ]; push_cast; ring
    have hdist := dist_odd_mult (q := (q : ℤ)) (X := c * 2 ^ (e - (p - j) - 1)) (β := β)
      (by positivity)
    rw [← hmq] at hdist
    have hab : (q : ℤ) - 1 ≤ |(s0 : ℤ) - (b * q : ℕ)| := by
      have h1 := abs_sub_abs_le_abs_sub ((c * 2 ^ e : ℤ) - (b * q : ℕ)) ((s0 : ℤ) - (b * q : ℕ))
      have h2 : |((c * 2 ^ e : ℤ) - (b * q : ℕ)) - ((s0 : ℤ) - (b * q : ℕ))| = 1 := by
        rcases hs0m with h0 | h0 <;> rw [h0] <;> norm_num
      rw [hcq] at h1 h2 ⊢
      linarith
    have habR : (2 : ℝ) ^ (p - j) - 1 ≤ |(s0 : ℝ) - b * 2 ^ (p - j)| := by
      have : ((q : ℤ) - 1 : ℝ) ≤ ((|(s0 : ℤ) - (b * q : ℕ)| : ℤ) : ℝ) := by exact_mod_cast hab
      push_cast at this; rw [hq] at this; push_cast at this; exact this
    have hqR : (2 : ℝ) ≤ 2 ^ (p - j) := by
      have : ((2 : ℕ) : ℝ) ≤ ((2 ^ (p - j) : ℕ) : ℝ) := by exact_mod_cast hq2
      push_cast at this; exact this
    linarith

end

end GrayNecklaces
