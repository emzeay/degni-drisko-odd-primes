module

public import GrayNecklaces.Truncation

/-!
# Ordering of maximal windows and the wing integers
-/

@[expose] public section

namespace GrayNecklaces

open Tiozzo

/-- Distinct maximal windows are ordered by their centers. -/
lemma maxwin_order (h87 : Theorem87) (h9 : TuningNesting) {p b1 j1 b2 j2 : ℕ}
    (hm1 : IsMaxWin p b1 j1) (hm2 : IsMaxWin p b2 j2) (hne : ¬ (b1 = b2 ∧ j1 = j2))
    (hlt : (b1 : ℝ) / 2 ^ j1 < b2 / 2 ^ j2) : wR b1 j1 ≤ wT b2 j2 := by
  by_contra hh
  push Not at hh
  have hj1 : 1 ≤ j1 := by have := hm1.1.1; omega
  have hj2 : 1 ≤ j2 := by have := hm2.1.1; omega
  have a1 := wT_lt_center (b := b1) (j := j1) hm1.1.2.2.1.pos hj1
  have a2 := center_lt_wR (b := b1) (j := j1) hm1.1.2.2.1.pos hj1
  have a3 := wT_lt_center (b := b2) (j := j2) hm2.1.2.2.1.pos hj2
  have a4 := center_lt_wR (b := b2) (j := j2) hm2.1.2.2.1.pos hj2
  set y := (max (wT b1 j1) (wT b2 j2) + min (wR b1 j1) (wR b2 j2)) / 2
  have hmx : max (wT b1 j1) (wT b2 j2) < min (wR b1 j1) (wR b2 j2) := by
    apply max_lt <;> apply lt_min <;> linarith
  obtain ⟨e1, e2⟩ := hm1.eq_of_overlap h87 h9 hm2 (y := y)
    (by have := le_max_left (wT b1 j1) (wT b2 j2); simp only [y]; linarith)
    (by have := min_le_left (wR b1 j1) (wR b2 j2); simp only [y]; linarith)
    (by have := le_max_right (wT b1 j1) (wT b2 j2); simp only [y]; linarith)
    (by have := min_le_right (wR b1 j1) (wR b2 j2); simp only [y]; linarith)
  exact hne ⟨e1.symm, e2.symm⟩

lemma center_real {p b j : ℕ} (hjp : j ≤ p) :
    ((b * 2 ^ (p - j) : ℕ) : ℝ) / 2 ^ p = (b : ℝ) / 2 ^ j := by
  rw [pow_split hjp]; push_cast; field_simp

/-- Integer identities for the wing (both orientations). -/
lemma wing_identity_right (B H v c : ℤ) :
    ((B - 1) * v - c * H) * (B * H - 1) - (B - 1) * (c * H + v) =
      ((B - 1) * v - c * H - c) * (B * H - 2) - 2 * c := by ring

lemma wing_identity_left (B H v c : ℤ) :
    ((B - 1) * v - c * H) * (B * H - 1) - (B - 1) * (c * H - v) =
      ((B - 1) * v - c * H - c) * (B * H) + 2 * c * H := by ring

/-- From disjointness of the central and wing windows: `ℓ ≥ 2`. -/
lemma ell_ge_two {B H v c bw D η : ℤ} (hB : 8 ≤ B) (hH : 2 ≤ H) (h6 : 6 * c < B) (hc : 1 ≤ c)
    (hη : η = 1 ∨ η = -1) (hbw : bw = c * H + η * v) (hD : D = B * H)
    (hint : (B - 1) * bw ≤ ((B - 1) * v - c * H) * (D - 1))
    (hev : Even ((B - 1) * v - c * H - c))
    (hanti : η = -1 → (B - 1) * v ≠ (H + 1) * c) :
    2 ≤ (B - 1) * v - c * H - c := by
  set ℓ := (B - 1) * v - c * H - c with hℓ
  have hBH : 16 ≤ B * H := by nlinarith
  subst hD hbw
  rcases hη with rfl | rfl
  · have hid := wing_identity_right B H v c
    have h0 : 0 ≤ ℓ * (B * H - 2) - 2 * c := by rw [← hid]; linarith
    have hpos : 0 < ℓ := by
      by_contra hh0; push Not at hh0
      have : ℓ * (B * H - 2) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hh0 (by linarith)
      linarith
    obtain ⟨r, hr⟩ := hev; omega
  · have hid := wing_identity_left B H v c
    have h0 : 0 ≤ ℓ * (B * H) + 2 * c * H := by
      rw [← hid]; simp only [neg_one_mul] at hint ⊢; linarith
    have hnn : 0 ≤ ℓ := by
      by_contra hh0; push Not at hh0
      have h1 : ℓ ≤ -1 := by omega
      have h2 : ℓ * (B * H) ≤ -1 * (B * H) := mul_le_mul_of_nonneg_right h1 (by linarith)
      have h3 : 2 * c * H < B * H := by
        have := mul_lt_mul_of_pos_right (show 2 * c < B by omega) (show (0 : ℤ) < H by omega)
        linarith
      linarith
    have hne0 : ℓ ≠ 0 := by
      intro h0; apply hanti rfl; simp only [ℓ] at h0; linarith
    obtain ⟨r, hr⟩ := hev; omega

lemma gapG_real {k : ℕ} :
    ((gapG k : ℕ) : ℝ) = if Even k then ((2 : ℝ) ^ k + 2) / 3 else ((2 : ℝ) ^ k - 2) / 3 := by
  have hm := two_pow_mod_three k
  unfold gapG
  split_ifs with he
  · rw [ite_eq_left he] at hm
    have : 3 * ((2 ^ k + 2) / 3) = 2 ^ k + 2 := by omega
    have : ((3 * ((2 ^ k + 2) / 3) : ℕ) : ℝ) = ((2 ^ k + 2 : ℕ) : ℝ) := by rw [this]
    push_cast at this; linarith
  · rw [ite_eq_right he] at hm
    have h1 : 2 ≤ 2 ^ k := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · subst h0; exact absurd (by decide : Even 0) he
      · exact two_le_two_pow h0
    have : 3 * ((2 ^ k - 2) / 3) = 2 ^ k - 2 := by omega
    have : ((3 * ((2 ^ k - 2) / 3) : ℕ) : ℝ) = ((2 ^ k - 2 : ℕ) : ℝ) := by rw [this]
    push_cast [h1] at this; linarith

lemma two_pow_step {a b : ℕ} (h : 2 ^ a < 2 ^ b) : 2 * 2 ^ a ≤ 2 ^ b := by
  have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h
  rw [← pow_succ']; exact Nat.pow_le_pow_right (by norm_num) this

section

variable {a k : ℕ} (h : Central a k)
include h

/-- Truncating the source interval still reaches `1/2` (the right-wing step of Section 6). -/
lemma trunc_half {j0 n : ℕ} (hcov : Set.Icc (2 * wR a k) (lam a k) ⊆ (Fm a k)^[n] '' topI a k j0)
    {Rw q : ℝ} (hq : 2 ^ n * 2 = q) (hRw : wR a k ≤ Rw) (hE : q * (Rw - wR a k) < 1 - 4 * wR a k)
    (hlo : xo a k j0 ≤ 1 - Rw) :
    ∃ z, xo a k j0 ≤ z ∧ z ≤ 1 - Rw ∧ (Fm a k)^[n] z = 1 / 2 := by
  have hR := wR_pos (b := a) (j := k) h.a_pos (by have := h.hk; omega)
  have hR3 := wR_le_third (a := a) (k := k) (by have := h.hk; omega) (by have := h.h6; omega)
  have hlamd : lam a k = 1 - wR a k := rfl
  have h2R : 2 * wR a k ≤ lam a k := by rw [hlamd]; linarith
  obtain ⟨z1, hz1, hz1v⟩ := hcov ⟨le_rfl, h2R⟩
  obtain ⟨z2, hz2, hz2v⟩ := hcov ⟨h2R, le_rfl⟩
  set z1' := min z1 (1 - Rw)
  set z2' := min z2 (1 - Rw)
  have hz1' : xo a k j0 ≤ z1' ∧ z1' ≤ 1 - Rw := ⟨le_min hz1.1 hlo, min_le_right _ _⟩
  have hz2' : xo a k j0 ≤ z2' ∧ z2' ≤ 1 - Rw := ⟨le_min hz2.1 hlo, min_le_right _ _⟩
  have hd1 : |z1' - z1| ≤ Rw - wR a k := by
    have := hz1.2; rw [hlamd] at this
    simp only [z1']
    rcases le_total z1 (1 - Rw) with hh | hh
    · rw [min_eq_left hh]; simp; linarith
    · rw [min_eq_right hh, abs_of_nonpos (by linarith)]; linarith
  have hd2 : |z2' - z2| ≤ Rw - wR a k := by
    have := hz2.2; rw [hlamd] at this
    simp only [z2']
    rcases le_total z2 (1 - Rw) with hh | hh
    · rw [min_eq_left hh]; simp; linarith
    · rw [min_eq_right hh, abs_of_nonpos (by linarith)]; linarith
  have hP : (0 : ℝ) ≤ 2 ^ n := by positivity
  have hl1 := Fm_iterate_lipschitz a k n z1' z1
  have hl2 := Fm_iterate_lipschitz a k n z2' z2
  have hb1 : (Fm a k)^[n] z1' < 1 / 2 := by
    rw [hz1v] at hl1
    have : 2 ^ n * |z1' - z1| ≤ 2 ^ n * (Rw - wR a k) := mul_le_mul_of_nonneg_left hd1 hP
    have : 2 ^ n * (Rw - wR a k) * 2 < 1 - 4 * wR a k := by rw [← hq] at hE; linarith
    have := le_abs_self ((Fm a k)^[n] z1' - 2 * wR a k)
    linarith
  have hb2 : 1 / 2 < (Fm a k)^[n] z2' := by
    rw [hz2v] at hl2
    have : 2 ^ n * |z2' - z2| ≤ 2 ^ n * (Rw - wR a k) := mul_le_mul_of_nonneg_left hd2 hP
    have : 2 ^ n * (Rw - wR a k) * 2 < 1 - 4 * wR a k := by rw [← hq] at hE; linarith
    have := neg_abs_le ((Fm a k)^[n] z2' - lam a k)
    rw [hlamd] at this hl2
    linarith
  have hcont : ContinuousOn (Fm a k)^[n] (Set.uIcc z1' z2') :=
    ((continuous_Fm a k).iterate n).continuousOn
  obtain ⟨z, hz, hzv⟩ := intermediate_value_uIcc hcont (show (1 / 2 : ℝ) ∈
    Set.uIcc ((Fm a k)^[n] z1') ((Fm a k)^[n] z2') by
      rw [Set.mem_uIcc]; left; exact ⟨hb1.le, hb2.le⟩)
  rw [Set.mem_uIcc] at hz
  refine ⟨z, ?_, ?_, hzv⟩ <;> rcases hz with hz | hz <;> linarith [hz.1, hz.2]

end

lemma odd_dvd_of_dvd_pow_mul {M x : ℤ} {n : ℕ} (hM : Odd M) (h : M ∣ 2 ^ n * x) : M ∣ x := by
  have hc : IsCoprime M 2 := by
    obtain ⟨t, ht⟩ := hM
    exact ⟨1, -t, by rw [ht]; ring⟩
  exact (hc.pow_right (n := n)).dvd_of_dvd_mul_left h

end GrayNecklaces
