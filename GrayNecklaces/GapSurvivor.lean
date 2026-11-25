module

public import GrayNecklaces.MaskSurvivor

/-!
# A survivor in the gap contradicts consecutiveness
-/

@[expose] public section

namespace GrayNecklaces

open Tiozzo

lemma N_mul_wR {p b j : ℕ} (hj : 1 ≤ j) (hjp : j ≤ p) :
    (2 : ℝ) ^ p * wR b j = b * 2 ^ (p - j) + wR b j * 2 ^ (p - j) := by
  rw [pow_split hjp]
  conv_lhs => rw [wR_eq hj]
  have : (2:ℝ) ^ j ≠ 0 := by positivity
  field_simp

lemma N_mul_wT {p b j : ℕ} (hj : 1 ≤ j) (hjp : j ≤ p) :
    (2 : ℝ) ^ p * wT b j = b * 2 ^ (p - j) - wR b j * 2 ^ (p - j) := by
  rw [pow_split hjp, wT_eq hj]
  have : (2:ℝ) ^ j ≠ 0 := by positivity
  field_simp

section

variable {p σ τ e c : ℕ} (hc : Consec p σ τ) (hs : Split p σ τ e c) (h87 : Theorem87)
  (h9 : TuningNesting) (h4 : σ + 4 ≤ τ)
include hc hs h87 h9 h4

/-- **Separator.**  An odd mask survivor strictly inside the gap between the central window and
the first large window on one side gives a contradiction. -/
theorem sep_contra {w bw jw : ℕ} (hw3 : 3 * w ≤ 2 ^ e + 1) (hmw : τ ≤ c * 2 ^ e + w)
    (hmw' : c * 2 ^ e ≤ σ + w) (hwing : IsLarge p σ τ e bw jw) (η : ℤ)
    (hη : (η = 1 ∧ c * 2 ^ e < bw * 2 ^ (p - jw)) ∨ (η = -1 ∧ bw * 2 ^ (p - jw) < c * 2 ^ e))
    (hfirst : ∀ b j, IsLarge p σ τ e b j → ¬ (b = bw ∧ j = jw) →
      (min (c * 2 ^ e) (bw * 2 ^ (p - jw)) < b * 2 ^ (p - j) ∧
        b * 2 ^ (p - j) < max (c * 2 ^ e) (bw * 2 ^ (p - jw))) → False)
    (e' : ℤ) (he'odd : Odd e')
    (hL : wR bw jw * 2 ^ (p - jw) < (e' : ℝ))
    (hU : (e' : ℝ) < η * ((bw * 2 ^ (p - jw) : ℕ) - (c * 2 ^ e : ℕ) : ℝ) - wR c (p - e) * 2 ^ e)
    (hmask : ∀ g, 1 ≤ g → g < p - e → (c : ℤ) * 2 ^ g ≤ 2 ^ (p - e) * oddDist (2 ^ g) e') :
    False := by
  obtain ⟨hwm, hwσ, hwτ, hwk, hwe⟩ := hwing
  have hep := hs.hep
  have hjw : 1 ≤ jw := by have := hwm.1.1; omega
  have hjwp := hwm.1.2.1
  set m := c * 2 ^ e with hmdef
  set cw := bw * 2 ^ (p - jw) with hcwdef
  set R := wR c (p - e)
  set Rw := wR bw jw
  have hR := wR_pos (b := c) (j := p - e) hs.hodd.pos (by omega)
  have hRw := wR_pos (b := bw) (j := jw) hwm.1.2.2.1.pos hjw
  have hq : (0 : ℝ) < 2 ^ (p - jw) := by positivity
  have hQ : (0 : ℝ) < 2 ^ e := by positivity
  have he'pos : (0 : ℝ) < e' := lt_trans (by positivity) hL
  -- the separator rank
  set sZ : ℤ := (cw : ℤ) - η * e' with hsZ
  have hsR : (sZ : ℝ) = cw - η * e' := by simp only [sZ]; push_cast; ring
  -- its position
  have hpos : (η = 1 ∧ (m : ℝ) + R * 2 ^ e < sZ ∧ (sZ : ℝ) < cw - Rw * 2 ^ (p - jw)) ∨
      (η = -1 ∧ (cw : ℝ) + Rw * 2 ^ (p - jw) < sZ ∧ (sZ : ℝ) < m - R * 2 ^ e) := by
    rcases hη with ⟨rfl, h⟩ | ⟨rfl, h⟩
    · left; refine ⟨rfl, ?_, ?_⟩ <;> rw [hsR] <;> push_cast at hU ⊢ <;> linarith
    · right; refine ⟨rfl, ?_, ?_⟩ <;> rw [hsR] <;> push_cast at hU ⊢ <;> linarith
  have hmR : (0 : ℝ) < R * 2 ^ e := mul_pos hR hQ
  have hwR : (0 : ℝ) < Rw * 2 ^ (p - jw) := mul_pos hRw hq
  have hσR : (σ : ℝ) < m := by have := hs.h1; exact_mod_cast this
  have hτR : (m : ℝ) < τ := by have := hs.h2; exact_mod_cast this
  have hcwσ : (σ : ℝ) < cw := by exact_mod_cast hwσ
  have hcwτ : (cw : ℝ) < τ := by exact_mod_cast hwτ
  have hs1 : (σ : ℝ) < sZ ∧ (sZ : ℝ) < τ := by
    rcases hpos with ⟨_, h1, h2⟩ | ⟨_, h1, h2⟩ <;> constructor <;> linarith
  have hs1Z : (σ : ℤ) < sZ ∧ sZ < τ := by
    constructor <;> [have := hs1.1; have := hs1.2] <;> exact_mod_cast this
  obtain ⟨sN, hsN⟩ : ∃ sN : ℕ, (sN : ℤ) = sZ := ⟨sZ.toNat, Int.toNat_of_nonneg (by omega)⟩
  have hsNR : (sN : ℝ) = sZ := by rw [← hsN]; push_cast; ring
  have h1 : σ < sN := by omega
  have h2 : sN < τ := by omega
  have hsodd : Odd sN := by
    have hcwev : Even (cw : ℤ) := by
      have : Even cw := (Nat.even_pow.mpr ⟨even_two, by omega⟩).mul_left bw
      exact (Int.even_natCast cw).mpr this
    have : Odd sZ := by
      simp only [sZ]
      rcases hη with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · rw [one_mul]; exact hcwev.sub_odd he'odd
      · rw [show (cw : ℤ) - -1 * e' = cw + e' by ring]; exact hcwev.add_odd he'odd
    rw [← hsN] at this; exact (Int.odd_natCast sN).mp this
  obtain ⟨b, j, hm, hd⟩ := hc.gap_deleted h87 hsodd h1 h2
  obtain ⟨hcen1, hcen2, hle, heq, _⟩ := classify hc hs h87 hm hd h1 h2
  have hj : 1 ≤ j := by have := hm.1.1; omega
  have hjp := hm.1.2.1
  have hdelR := hd
  obtain ⟨_, hD1, hD2⟩ := hdelR
  -- `N wT`, `N wR` of the three windows
  have hcR := N_mul_wR (p := p) (b := c) (j := p - e) (by omega) (by omega)
  have hcT := N_mul_wT (p := p) (b := c) (j := p - e) (by omega) (by omega)
  rw [show p - (p - e) = e by omega] at hcR hcT
  have hwRR := N_mul_wR (p := p) (b := bw) (j := jw) hjw hjwp.le
  have hwTT := N_mul_wT (p := p) (b := bw) (j := jw) hjw hjwp.le
  have hmcast : ((m : ℕ) : ℝ) = (c : ℝ) * 2 ^ e := by simp only [m]; push_cast; ring
  have hcwcast : ((cw : ℕ) : ℝ) = (bw : ℝ) * 2 ^ (p - jw) := by simp only [cw]; push_cast; ring
  rw [← hmcast] at hcR hcT
  rw [← hcwcast] at hwRR hwTT
  rcases eq_or_lt_of_le hle with he | he
  · -- the central window
    obtain ⟨rfl, rfl⟩ := heq he
    rw [hsNR] at hD1 hD2
    rcases hpos with ⟨_, h1', h2'⟩ | ⟨_, h1', h2'⟩
    · linarith
    · linarith
  · by_cases hlarge : p - e ≤ p - j
    · -- another large window, or the wing itself
      by_cases hsame : b = bw ∧ j = jw
      · obtain ⟨rfl, rfl⟩ := hsame
        rw [hsNR] at hD1 hD2
        rcases hpos with ⟨rfl, h1', h2'⟩ | ⟨rfl, h1', h2'⟩
        · linarith
        · linarith
      · apply hfirst b j ⟨hm, hcen1, hcen2, hlarge, he⟩ hsame
        have hbR := N_mul_wR (p := p) (b := b) (j := j) hj hjp.le
        have hbT := N_mul_wT (p := p) (b := b) (j := j) hj hjp.le
        have hbRpos := wR_pos (b := b) (j := j) hm.1.2.2.1.pos hj
        have hbq : (0 : ℝ) < wR b j * 2 ^ (p - j) := mul_pos hbRpos (by positivity)
        have hN : (0 : ℝ) < 2 ^ p := by positivity
        rw [hsNR] at hD1 hD2
        -- disjointness from the central window
        have hdisj1 : ∀ y : ℝ, ¬ (wT c (p - e) < y ∧ y < wR c (p - e) ∧ wT b j < y ∧ y < wR b j) := by
          rintro y ⟨y1, y2, y3, y4⟩
          obtain ⟨_, hj'⟩ := (central_max hc hs h87 h4).eq_of_overlap h87 h9 hm y1 y2 y3 y4
          omega
        have hdisj2 : ∀ y : ℝ, ¬ (wT bw jw < y ∧ y < wR bw jw ∧ wT b j < y ∧ y < wR b j) := by
          rintro y ⟨y1, y2, y3, y4⟩
          obtain ⟨h1'', h2''⟩ := hwm.eq_of_overlap h87 h9 hm y1 y2 y3 y4
          exact hsame ⟨h1'', h2''⟩
        rcases hpos with ⟨hη1, h1', h2'⟩ | ⟨hη1, h1', h2'⟩
        · -- right side: the window lies between `m + RQ` and `cw - Rw q`
          have hl : wR c (p - e) ≤ wT b j := by
            by_contra hh; push Not at hh
            apply hdisj1 ((max (wT b j) (wT c (p - e)) + wR c (p - e)) / 2)
            have hT' : wT c (p - e) < wR c (p - e) := by
              have := wT_lt_center (b := c) (j := p - e) hs.hodd.pos (by omega)
              have := center_lt_wR (b := c) (j := p - e) hs.hodd.pos (by omega)
              linarith
            have hy : (sZ : ℝ) / 2 ^ p < wR b j := by rw [div_lt_iff₀ hN]; linarith
            have hy' : wR c (p - e) < (sZ : ℝ) / 2 ^ p := by
              rw [lt_div_iff₀ hN]; linarith
            refine ⟨?_, ?_, ?_, ?_⟩
            · have := le_max_right (wT b j) (wT c (p - e)); linarith
            · have := max_lt hh hT'; linarith
            · have := le_max_left (wT b j) (wT c (p - e)); linarith
            · have := max_lt hh hT'; linarith
          have hr : wR b j ≤ wT bw jw := by
            by_contra hh; push Not at hh
            apply hdisj2 ((wT bw jw + min (wR b j) (wR bw jw)) / 2)
            have hT' : wT bw jw < wR bw jw := by
              have := wT_lt_center (b := bw) (j := jw) hwm.1.2.2.1.pos hjw
              have := center_lt_wR (b := bw) (j := jw) hwm.1.2.2.1.pos hjw
              linarith
            have hy : (sZ : ℝ) / 2 ^ p < wT bw jw := by
              rw [div_lt_iff₀ hN]; linarith
            have hy' : wT b j < (sZ : ℝ) / 2 ^ p := by rw [lt_div_iff₀ hN]; linarith
            refine ⟨?_, ?_, ?_, ?_⟩
            · have := lt_min hh hT'; linarith
            · have := min_le_right (wR b j) (wR bw jw); linarith
            · have := lt_min hh hT'; linarith
            · have := min_le_left (wR b j) (wR bw jw); linarith
          have hcen1' : ((b * 2 ^ (p - j) : ℕ) : ℝ) > m := by
            push_cast
            have : (2 : ℝ) ^ p * wR c (p - e) ≤ 2 ^ p * wT b j := mul_le_mul_of_nonneg_left hl hN.le
            linarith
          have hcen2' : ((b * 2 ^ (p - j) : ℕ) : ℝ) < cw := by
            push_cast
            have : (2 : ℝ) ^ p * wR b j ≤ 2 ^ p * wT bw jw := mul_le_mul_of_nonneg_left hr hN.le
            linarith
          have hmc : m < cw := by
            rcases hη with ⟨_, h⟩ | ⟨h3, _⟩
            · exact h
            · rw [h3] at hη1; norm_num at hη1
          constructor
          · rw [min_eq_left hmc.le]; exact_mod_cast hcen1'
          · rw [max_eq_right hmc.le]; exact_mod_cast hcen2'
        · -- left side
          have hl : wR b j ≤ wT c (p - e) := by
            by_contra hh; push Not at hh
            apply hdisj1 ((wT c (p - e) + min (wR b j) (wR c (p - e))) / 2)
            have hT' : wT c (p - e) < wR c (p - e) := by
              have := wT_lt_center (b := c) (j := p - e) hs.hodd.pos (by omega)
              have := center_lt_wR (b := c) (j := p - e) hs.hodd.pos (by omega)
              linarith
            have hy : (sZ : ℝ) / 2 ^ p < wT c (p - e) := by
              rw [div_lt_iff₀ hN]; linarith
            have hy' : wT b j < (sZ : ℝ) / 2 ^ p := by rw [lt_div_iff₀ hN]; linarith
            refine ⟨?_, ?_, ?_, ?_⟩
            · have := lt_min hh hT'; linarith
            · have := min_le_right (wR b j) (wR c (p - e)); linarith
            · have := lt_min hh hT'; linarith
            · have := min_le_left (wR b j) (wR c (p - e)); linarith
          have hr : wR bw jw ≤ wT b j := by
            by_contra hh; push Not at hh
            apply hdisj2 ((max (wT b j) (wT bw jw) + wR bw jw) / 2)
            have hT' : wT bw jw < wR bw jw := by
              have := wT_lt_center (b := bw) (j := jw) hwm.1.2.2.1.pos hjw
              have := center_lt_wR (b := bw) (j := jw) hwm.1.2.2.1.pos hjw
              linarith
            have hy : (sZ : ℝ) / 2 ^ p < wR b j := by rw [div_lt_iff₀ hN]; linarith
            have hy' : wR bw jw < (sZ : ℝ) / 2 ^ p := by
              rw [lt_div_iff₀ hN]; linarith
            refine ⟨?_, ?_, ?_, ?_⟩
            · have := le_max_right (wT b j) (wT bw jw); linarith
            · have := max_lt hh hT'; linarith
            · have := le_max_left (wT b j) (wT bw jw); linarith
            · have := max_lt hh hT'; linarith
          have hcen1' : ((b * 2 ^ (p - j) : ℕ) : ℝ) < m := by
            push_cast
            have : (2 : ℝ) ^ p * wR b j ≤ 2 ^ p * wT c (p - e) := mul_le_mul_of_nonneg_left hl hN.le
            linarith
          have hcen2' : ((b * 2 ^ (p - j) : ℕ) : ℝ) > cw := by
            push_cast
            have : (2 : ℝ) ^ p * wR bw jw ≤ 2 ^ p * wT b j := mul_le_mul_of_nonneg_left hr hN.le
            linarith
          have hmc : cw < m := by
            rcases hη with ⟨h3, _⟩ | ⟨_, h⟩
            · rw [h3] at hη1; norm_num at hη1
            · exact h
          constructor
          · rw [min_eq_right hmc.le]; exact_mod_cast hcen2'
          · rw [max_eq_left hmc.le]; exact_mod_cast hcen1'
    · -- a window of scale below `B`: frozen radius and the mask
      push Not at hlarge
      have hBQ : 2 * 2 ^ (p - e) ≤ 2 ^ e := by
        rw [← pow_succ']; exact Nat.pow_le_pow_right (by norm_num) (by omega)
      have hfz := frozen hc hs h87 hw3 hmw hmw' hm hd h1 h2 hlarge hBQ
      have hmk := hmask (p - j) (by omega) hlarge
      -- `oddDist ≤ |s - cen|`
      obtain ⟨β, hβ⟩ := hm.1.2.2.1
      obtain ⟨t, ht⟩ : ∃ t : ℕ, 2 ^ (p - j) = t := ⟨_, rfl⟩
      have hcwt : (cw : ℤ) = 2 * t * (bw * 2 ^ ((p - jw) - (p - j) - 1)) := by
        have : (2 : ℤ) ^ (p - jw) = 2 * 2 ^ (p - j) * 2 ^ ((p - jw) - (p - j) - 1) := by
          rw [← pow_succ', ← pow_add]; congr 1; omega
        simp only [cw]; push_cast; rw [this, show (2 : ℤ) ^ (p - j) = t by rw [← ht]; push_cast; ring]
        ring
      have hcen : ((b * 2 ^ (p - j) : ℕ) : ℤ) = t * (2 * β + 1) := by
        rw [hβ, ht]; push_cast; ring
      have hod : oddDist t e' ≤ ((sN : ℤ) - ((b * 2 ^ (p - j) : ℕ) : ℤ)).natAbs := by
        rw [Int.natCast_natAbs, hsN, hcen]
        simp only [sZ]
        rw [hcwt]
        rcases hη with ⟨rfl, _⟩ | ⟨rfl, _⟩
        · have := oddDist_le_abs (t := t) (by rw [← ht]; positivity) e'
            (bw * 2 ^ ((p - jw) - (p - j) - 1) - β - 1)
          rw [show (2 * t * (bw * 2 ^ ((p - jw) - (p - j) - 1)) - 1 * e' - t * (2 * β + 1) : ℤ) =
            -(e' - t * (2 * (bw * 2 ^ ((p - jw) - (p - j) - 1) - β - 1) + 1)) by ring, abs_neg]
          exact this
        · have := oddDist_le_abs (t := t) (by rw [← ht]; positivity) (-e')
            (bw * 2 ^ ((p - jw) - (p - j) - 1) - β - 1)
          rw [oddDist_neg] at this
          rw [show (2 * t * (bw * 2 ^ ((p - jw) - (p - j) - 1)) - -1 * e' - t * (2 * β + 1) : ℤ) =
            -(-e' - t * (2 * (bw * 2 ^ ((p - jw) - (p - j) - 1) - β - 1) + 1)) by ring, abs_neg]
          exact this
      rw [ht] at hfz hmk hod
      have hfzZ : ((2 ^ (p - e) * ((sN : ℤ) - ((b * t : ℕ) : ℤ)).natAbs : ℕ) : ℤ) <
          ((c * t : ℕ) : ℤ) := by exact_mod_cast hfz
      push_cast at hfzZ
      have hB0 : (0 : ℤ) ≤ 2 ^ (p - e) := by positivity
      have := mul_le_mul_of_nonneg_left hod hB0
      push_cast at this
      have ht' : (2 : ℤ) ^ (p - j) = t := by rw [← ht]; push_cast; ring
      rw [ht'] at hmk
      linarith

end

end GrayNecklaces
