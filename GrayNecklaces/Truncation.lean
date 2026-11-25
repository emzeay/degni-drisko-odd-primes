module

public import GrayNecklaces.NegativePhase

/-!
# The truncation estimate for a right wing

All quantities are real.  Here `c` is the central numerator, written `a` in the PDF.  `M = B - 1`,
`ℓ = M v - c H - c`, the gap length is
`Δ = q (ℓ (BH-2) - 2c) / (M (BH-1))` and the truncation is `E = q (ℓ + 2c) / (M (BH-1))`.
-/

@[expose] public section

namespace GrayNecklaces

/-- **Truncation bound** `E < 1 - 4R`. -/
lemma E_bound_arith {B H q c v ℓ G : ℝ} (hB : 8 ≤ B) (hH : 2 ≤ H) (hq : B ≤ q) (hc : 1 ≤ c)
    (_hv : 1 ≤ v) (h6 : 6 * c ≤ B - 2) (hℓ : 2 ≤ ℓ) (hℓdef : ℓ = (B - 1) * v - c * H - c)
    (hG : G ≤ (B + 2) / 3) (hGc : G = (B - 2) / 3 ∨ (G = (B + 2) / 3 ∧ 6 * c ≤ B - 10))
    (hΔ : q * (ℓ * (B * H - 2) - 2 * c) / ((B - 1) * (B * H - 1)) ≤ G)
    (hqB : q < B ^ 2 → 2 * q ≤ B ^ 2)
    (hmax : H < B → c / (B - 1) ≤ v * (H - 2) / (H * (H - 1))) :
    q * (ℓ + 2 * c) / ((B - 1) * (B * H - 1)) < 1 - 4 * (c / (B - 1)) := by
  have hM : 0 < B - 1 := by linarith
  have hBH : 0 < B * H - 2 := by nlinarith only [hB, hH]
  have hBH1 : 0 < B * H - 1 := by linarith
  have hden : 0 < (B - 1) * (B * H - 1) := mul_pos hM hBH1
  set R := c / (B - 1) with hRdef
  have hRM : R * (B - 1) = c := by simp only [R]; field_simp
  have hR6 : R < 1 / 6 := by rw [hRdef, div_lt_iff₀ hM]; linarith
  have hR0 : 0 < R := by positivity
  set E := q * (ℓ + 2 * c) / ((B - 1) * (B * H - 1)) with hEdef
  set Δ := q * (ℓ * (B * H - 2) - 2 * c) / ((B - 1) * (B * H - 1)) with hΔdef
  have hEden : E * ((B - 1) * (B * H - 1)) = q * (ℓ + 2 * c) := by
    simp only [E]; field_simp
  have hΔden : Δ * ((B - 1) * (B * H - 1)) = q * (ℓ * (B * H - 2) - 2 * c) := by
    simp only [Δ]; field_simp
  -- `E (BH - 2) = Δ + 2 q R`
  have hid : E * (B * H - 2) = Δ + 2 * q * R := by
    have h1 : (E * (B * H - 2) - Δ - 2 * q * R) * ((B - 1) * (B * H - 1)) = 0 := by
      have : (E * (B * H - 2) - Δ - 2 * q * R) * ((B - 1) * (B * H - 1)) =
          (E * ((B - 1) * (B * H - 1))) * (B * H - 2) - Δ * ((B - 1) * (B * H - 1)) -
            2 * q * (R * (B - 1)) * (B * H - 1) := by ring
      rw [this, hEden, hΔden, hRM]; ring
    have := mul_eq_zero.mp h1
    rcases this with h | h
    · linarith
    · exact absurd h hden.ne'
  have hq0 : 0 < q := by linarith
  rcases le_or_gt B H with hHB | hHB
  · -- large `H`: `q < B²`
    have hqB2 : q < B ^ 2 := by
      by_contra hh
      push Not at hh
      set T := B * H
      have hT : 2 * B ≤ T := by nlinarith only [hHB, hB]
      have hn0 : 2 * (T - 2) - 2 * c ≤ ℓ * (T - 2) - 2 * c := by
        nlinarith only [mul_le_mul_of_nonneg_right hℓ hBH.le]
      have hn0pos : 0 < 2 * (T - 2) - 2 * c := by linarith
      have h1 : B ^ 2 * (2 * (T - 2) - 2 * c) ≤ q * (ℓ * (T - 2) - 2 * c) := by
        calc B ^ 2 * (2 * (T - 2) - 2 * c) ≤ q * (2 * (T - 2) - 2 * c) :=
              mul_le_mul_of_nonneg_right hh hn0pos.le
          _ ≤ q * (ℓ * (T - 2) - 2 * c) := mul_le_mul_of_nonneg_left hn0 hq0.le
      -- `3 B² (2T - 4 - 2c) > (B+2)(B-1)(T-1)`
      have h2 : 6 * B ^ 2 * c ≤ B ^ 3 - 2 * B ^ 2 := by nlinarith only [h6, hB]
      have h3 : 2 * B ^ 2 * (5 * B - 1) ≤ B * T * (5 * B - 1) := by
        have : 0 ≤ B * (5 * B - 1) := by nlinarith only [hB]
        nlinarith only [mul_le_mul_of_nonneg_left hT this]
      have h4 : 0 < 9 * B ^ 3 - 11 * B ^ 2 - 2 := by nlinarith only [hB]
      have h5 : (B + 2) * (B - 1) * (T - 1) < 3 * (B ^ 2 * (2 * (T - 2) - 2 * c)) := by
        nlinarith only [h2, h3, h4, hT, hB]
      have h6' : (B + 2) / 3 < Δ := by
        rw [div_lt_iff₀ (by norm_num : (0:ℝ) < 3)]
        have : (B + 2) * ((B - 1) * (T - 1)) < 3 * (Δ * ((B - 1) * (T - 1))) := by
          rw [hΔden]; nlinarith only [h1, h5]
        by_contra hh2; push Not at hh2
        have : Δ * 3 * ((B - 1) * (T - 1)) ≤ (B + 2) * ((B - 1) * (T - 1)) :=
          mul_le_mul_of_nonneg_right hh2 hden.le
        linarith
      linarith
    have h2q := hqB hqB2
    have hBH2 : B ^ 2 - 2 ≤ B * H - 2 := by nlinarith only [hHB, hB]
    have hE0 : 0 ≤ E := div_nonneg (mul_nonneg hq0.le (by linarith)) hden.le
    have hupper : E * (B ^ 2 - 2) < (B + 2) / 3 + B ^ 2 / 6 := by
      have : E * (B ^ 2 - 2) ≤ E * (B * H - 2) := mul_le_mul_of_nonneg_left hBH2 hE0
      have : 2 * q * R ≤ B ^ 2 * R := mul_le_mul_of_nonneg_right h2q hR0.le
      have : B ^ 2 * R < B ^ 2 / 6 := by
        have := mul_lt_mul_of_pos_left hR6 (show (0:ℝ) < B ^ 2 by positivity)
        linarith
      linarith
    have : E < 1 / 3 := by
      by_contra hh; push Not at hh
      have : (B ^ 2 - 2) / 3 ≤ E * (B ^ 2 - 2) := by
        nlinarith only [mul_le_mul_of_nonneg_right hh (show (0:ℝ) ≤ B ^ 2 - 2 by nlinarith only [hB])]
      nlinarith only [hupper, this, hB]
    linarith
  · -- small `H`: maximality bounds `ℓ` below
    have hm := hmax hHB
    have hH4 : 2 < H := by
      by_contra hh; push Not at hh
      have : H = 2 := le_antisymm hh hH
      rw [this] at hm; norm_num at hm
      linarith
    have hH1 : 0 < H * (H - 1) := by nlinarith only [hH4]
    rw [div_le_div_iff₀ hM hH1] at hm
    -- `ℓ (H - 1) > 2c`
    have hℓH : 2 * c < ℓ * (H - 1) := by
      rw [hℓdef]
      have hX : c * (H * (H - 1)) * (H - 1) ≤ v * (H - 2) * (B - 1) * (H - 1) :=
        mul_le_mul_of_nonneg_right hm (by linarith)
      have e : (((B - 1) * v - c * H - c) * (H - 1)) * (H - 2) - (2 * c) * (H - 2) =
          (v * (H - 2) * (B - 1) * (H - 1) - c * (H * (H - 1)) * (H - 1)) + 2 * c := by ring
      have key : (2 * c) * (H - 2) < (((B - 1) * v - c * H - c) * (H - 1)) * (H - 2) := by
        linarith only [e, hX, hc]
      exact lt_of_mul_lt_mul_right key (by linarith)
    -- `E (BH - 1 - H) < H Δ`
    have hsum : (Δ + E) * (B - 1) = q * ℓ := by
      have h1 : ((Δ + E) * (B - 1) - q * ℓ) * ((B - 1) * (B * H - 1)) = 0 := by
        have : ((Δ + E) * (B - 1) - q * ℓ) * ((B - 1) * (B * H - 1)) =
            (Δ * ((B - 1) * (B * H - 1))) * (B - 1) + (E * ((B - 1) * (B * H - 1))) * (B - 1) -
              q * ℓ * ((B - 1) * (B * H - 1)) := by ring
        rw [this, hΔden, hEden]; ring
      rcases mul_eq_zero.mp h1 with h | h
      · linarith
      · exact absurd h hden.ne'
    have hlt : E * (B * H - 1) < H * (Δ + E) := by
      have h1 : E * (B * H - 1) * (B - 1) = q * (ℓ + 2 * c) := by rw [← hEden]; ring
      have h2 : q * (ℓ + 2 * c) < q * (H * ℓ) := by
        apply mul_lt_mul_of_pos_left _ hq0; linarith
      have h3 : q * (H * ℓ) = H * (Δ + E) * (B - 1) := by
        rw [mul_assoc H, hsum]; ring
      have : E * (B * H - 1) * (B - 1) < H * (Δ + E) * (B - 1) := by linarith
      exact lt_of_mul_lt_mul_right this hM.le
    have hHG : H * Δ ≤ H * G := mul_le_mul_of_nonneg_left hΔ (by linarith)
    have hlt2 : E * (B * H - 1 - H) < H * G := by linarith only [hlt, hHG]
    have hpos : 0 < B * H - 1 - H := by
      have : 7 * 2 ≤ (B - 1) * H := by nlinarith only [hB, hH]
      linarith
    rcases hGc with hG' | ⟨hG', h10⟩
    · rw [hG'] at hlt2
      have : E < 1 / 3 := by
        by_contra hh; push Not at hh
        have : (B * H - 1 - H) / 3 ≤ E * (B * H - 1 - H) := by
          nlinarith only [mul_le_mul_of_nonneg_right hh hpos.le]
        nlinarith only [this, hlt2, hH4]
      linarith
    · rw [hG'] at hlt2
      have hR : (B + 17) / (3 * (B - 1)) ≤ 1 - 4 * R := by
        rw [div_le_iff₀ (by positivity)]
        have : (1 - 4 * R) * (3 * (B - 1)) = 3 * (B - 1) - 12 * (R * (B - 1)) := by ring
        rw [this, hRM]; linarith
      have : E < (B + 17) / (3 * (B - 1)) := by
        rw [lt_div_iff₀ (by positivity)]
        by_contra hh; push Not at hh
        have h1 : (B + 17) * (B * H - 1 - H) ≤ E * (3 * (B - 1)) * (B * H - 1 - H) :=
          mul_le_mul_of_nonneg_right hh hpos.le
        have h2 : E * (3 * (B - 1)) * (B * H - 1 - H) < 3 * (B - 1) * (H * ((B + 2) / 3)) := by
          have := mul_lt_mul_of_pos_left hlt2 (show (0:ℝ) < 3 * (B - 1) by linarith)
          linarith only [this]
        have h3 : 2 * (B - 1) ≤ (B - 1) * H := by nlinarith only [hB, hH]
        have e1 : B * H - 1 - H = (B - 1) * H - 1 := by ring
        rw [e1] at h1 h2
        nlinarith only [h1, h2, h3, hB]
      linarith

end GrayNecklaces
