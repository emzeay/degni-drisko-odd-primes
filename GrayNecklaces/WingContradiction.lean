module

public import GrayNecklaces.WingArithmetic

/-!
# The first large window gives a contradiction
-/

@[expose] public section

namespace GrayNecklaces

open Tiozzo

section

variable {p σ τ e c : ℕ} (hc : Consec p σ τ) (hs : Split p σ τ e c) (h87 : Theorem87)
  (h9 : TuningNesting) (h4 : σ + 4 ≤ τ)
include hc hs h87 h9 h4

set_option maxHeartbeats 2000000 in
/-- **No first large wing.**  The arithmetic of a first large window (`v`, `ℓ ≥ 2`, `c ≥ b`)
and the separator from the gap bound or from the covering lemma. -/
theorem wing_contra {w bw jw : ℕ} (_hwodd : Odd w) (hw3 : 3 * w ≤ 2 ^ e + 1)
    (hmw' : c * 2 ^ e ≤ σ + w) (hmw : τ ≤ c * 2 ^ e + w) (hwing : IsLarge p σ τ e bw jw)
    (η : ℤ)
    (hη : (η = 1 ∧ c * 2 ^ e < bw * 2 ^ (p - jw)) ∨ (η = -1 ∧ bw * 2 ^ (p - jw) < c * 2 ^ e))
    (hfirst : ∀ b j, IsLarge p σ τ e b j → ¬ (b = bw ∧ j = jw) →
      (min (c * 2 ^ e) (bw * 2 ^ (p - jw)) < b * 2 ^ (p - j) ∧
        b * 2 ^ (p - j) < max (c * 2 ^ e) (bw * 2 ^ (p - jw))) → False) :
    False := by
  have hwing' := hwing
  obtain ⟨hwm, hwσ, hwτ, hwk, hwe⟩ := hwing
  have hep := hs.hep
  have hcen := central_struct hc hs h87 h9 h4
  have hcm := central_max hc hs h87 h4
  obtain ⟨hk3, h6⟩ := hs.k_ge hc h87
  have hc1 : 1 ≤ c := hs.hodd.pos
  have hjw1 : 1 ≤ jw := by have := hwm.1.1; omega
  have hjwp := hwm.1.2.1
  obtain ⟨j0, hj01, hj0k, hj0s, hj0min⟩ := exists_neg_phase hcen
  have hcov := cover hcen hj01 hj0k hj0s
  -- powers of two
  set k := p - e with hkdef
  set hh := p - jw with hhhdef
  obtain ⟨B, hB⟩ : ∃ B : ℕ, 2 ^ k = B := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : ℕ, 2 ^ e = Q := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : ℕ, 2 ^ hh = q := ⟨_, rfl⟩
  obtain ⟨H, hH⟩ : ∃ H : ℕ, 2 ^ (e - hh) = H := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℕ, 2 ^ jw = D := ⟨_, rfl⟩
  have hQqH : Q = q * H := by rw [← hQ, ← hq, ← hH, ← pow_add]; congr 1; omega
  have hDBH : D = B * H := by rw [← hD, ← hB, ← hH, ← pow_add]; congr 1; omega
  have hB8 : 8 ≤ B := by
    rw [← hB]; calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk3
  have hqB : B ≤ q := by rw [← hB, ← hq]; exact Nat.pow_le_pow_right (by norm_num) hwk
  have hH2 : 2 ≤ H := by rw [← hH]; exact two_le_two_pow (by omega)
  have hq2 : 2 ≤ q := by omega
  rw [hB] at h6
  set m := c * 2 ^ e with hmdef
  set cw := bw * 2 ^ (p - jw) with hcwdef
  have hmQ : m = c * Q := by rw [hmdef, hQ]
  have hcwq : cw = bw * q := by rw [hcwdef, ← hhhdef, hq]
  have hmqH : m = (c * H) * q := by rw [hmQ, hQqH]; ring
  rw [hQ] at hw3
  -- the integer `v`
  have hcwm : (cw : ℤ) - m < w ∧ (m : ℤ) - cw < w := by omega
  obtain ⟨v, hv⟩ : ∃ v : ℕ, ((bw : ℤ) - c * H) = η * v := by
    rcases hη with ⟨rfl, h⟩ | ⟨rfl, h⟩
    · refine ⟨bw - c * H, ?_⟩
      have : c * H < bw := by
        have : c * H * q < bw * q := by rw [← hmqH, ← hcwq]; exact h
        exact Nat.lt_of_mul_lt_mul_right this
      push_cast [this.le]; ring
    · refine ⟨c * H - bw, ?_⟩
      have : bw < c * H := by
        have : bw * q < c * H * q := by rw [← hmqH, ← hcwq]; exact h
        exact Nat.lt_of_mul_lt_mul_right this
      push_cast [this.le]; ring
  have hηsq : η * η = 1 := by rcases hη with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> norm_num
  have hdist : η * ((cw : ℤ) - m) = q * v := by
    rw [hcwq, hmqH]; push_cast
    have : (bw : ℤ) * q - c * H * q = q * (η * v) := by rw [← hv]; ring
    rw [this]; linear_combination (q * v : ℤ) * hηsq
  have hvodd : Odd v := by
    have hev : Even ((c * H : ℕ) : ℤ) := by
      have : Even H := by rw [← hH]; exact Nat.even_pow.mpr ⟨even_two, by omega⟩
      exact (Int.even_natCast _).mpr (this.mul_left c)
    have hodd1 : Odd ((bw : ℤ) - c * H) := by
      have := (Int.odd_natCast bw).mpr hwm.1.2.2.1
      push_cast at hev; exact this.sub_even hev
    have hvZ : (v : ℤ) = η * ((bw : ℤ) - c * H) := by
      rw [hv, ← mul_assoc, hηsq, one_mul]
    have : Odd (v : ℤ) := by
      rw [hvZ]
      rcases hη with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · rw [one_mul]; exact hodd1
      · rw [neg_one_mul]; exact hodd1.neg
    exact (Int.odd_natCast v).mp this
  have hv1 : 1 ≤ v := hvodd.pos
  have hv3 : 3 * v < H := by
    have h1 : (q : ℤ) * v < w := by
      rw [← hdist]; rcases hη with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
    have h2 : 3 * ((q : ℤ) * v) < q * H + 1 := by
      have : (3 * w : ℤ) ≤ Q + 1 := by exact_mod_cast hw3
      rw [hQqH] at this; push_cast at this; omega
    have h3 : 3 * v ≤ H := by
      by_contra hh3; push Not at hh3
      have : (q : ℤ) * (H + 1) ≤ q * (3 * v) := by
        have : (H + 1 : ℤ) ≤ 3 * v := by exact_mod_cast hh3
        exact mul_le_mul_of_nonneg_left this (by positivity)
      nlinarith
    have h4 : 3 * v ≠ H := by
      intro he; rw [← hH] at he
      exact three_not_dvd_two_pow (e - hh) ⟨v, he.symm⟩
    omega
  -- real coordinates
  have hBR : (2 : ℝ) ^ k = B := by rw [← hB]; push_cast; ring
  have hQR : (2 : ℝ) ^ e = Q := by rw [← hQ]; push_cast; ring
  have hqR : (2 : ℝ) ^ hh = q := by rw [← hq]; push_cast; ring
  have hDR : (2 : ℝ) ^ jw = D := by rw [← hD]; push_cast; ring
  have hB8R : (8 : ℝ) ≤ B := by exact_mod_cast hB8
  have hH2R : (2 : ℝ) ≤ H := by exact_mod_cast hH2
  have hqBR : (B : ℝ) ≤ q := by exact_mod_cast hqB
  have hQqHR : (Q : ℝ) = q * H := by exact_mod_cast hQqH
  have hDBHR : (D : ℝ) = B * H := by exact_mod_cast hDBH
  have hRdef : wR c k = c / (B - 1) := by unfold wR; rw [hBR]
  have hRwdef : wR bw jw = bw / (D - 1) := by unfold wR; rw [hDR]
  have hM0 : (0 : ℝ) < B - 1 := by linarith
  have hD0 : (0 : ℝ) < D - 1 := by rw [hDBHR]; nlinarith
  -- `U = q cc / M`
  set ccZ : ℤ := ((B : ℤ) - 1) * v - c * H with hccZ
  set ℓ : ℤ := ccZ - c with hℓdef
  have hU : (η : ℝ) * ((cw : ℝ) - m) - wR c k * Q = q * (ccZ : ℝ) / (B - 1) := by
    have : (η : ℝ) * ((cw : ℝ) - m) = q * v := by exact_mod_cast hdist
    rw [this, hRdef, hQqHR, hccZ]; push_cast; field_simp
  -- disjointness: `L ≤ U`
  have hN : (0 : ℝ) < 2 ^ p := by positivity
  have hpk : p - k = e := by omega
  have hcR := N_mul_wR (p := p) (b := c) (j := k) (by omega) (by omega)
  have hcT := N_mul_wT (p := p) (b := c) (j := k) (by omega) (by omega)
  have hwR' := N_mul_wR (p := p) (b := bw) (j := jw) hjw1 hjwp.le
  have hwT' := N_mul_wT (p := p) (b := bw) (j := jw) hjw1 hjwp.le
  rw [hpk, hQR] at hcR hcT
  rw [← hhhdef, hqR] at hwR' hwT'
  have hmR : ((m : ℕ) : ℝ) = c * Q := by rw [hmQ]; push_cast; ring
  have hcwR : ((cw : ℕ) : ℝ) = bw * q := by rw [hcwq]; push_cast; ring
  have hne : ¬ (c = bw ∧ k = jw) := by rintro ⟨_, h'⟩; omega
  have hne' : ¬ (bw = c ∧ jw = k) := by rintro ⟨_, h'⟩; omega
  have hLU : wR bw jw * q ≤ (η : ℝ) * ((cw : ℝ) - m) - wR c k * Q := by
    rcases hη with ⟨rfl, hlt⟩ | ⟨rfl, hlt⟩
    · have hlt' : (c : ℝ) / 2 ^ k < bw / 2 ^ jw := by
        rw [← center_real (p := p) (b := c) (j := k) (by omega),
          ← center_real (p := p) (b := bw) (j := jw) hjwp.le, hpk]
        apply div_lt_div_of_pos_right _ hN; exact_mod_cast hlt
      have := maxwin_order h87 h9 hcm hwm hne hlt'
      have := mul_le_mul_of_nonneg_left this hN.le
      rw [hcR, hwT'] at this
      rw [hmR, hcwR]; push_cast; linarith
    · have hlt' : (bw : ℝ) / 2 ^ jw < c / 2 ^ k := by
        rw [← center_real (p := p) (b := c) (j := k) (by omega),
          ← center_real (p := p) (b := bw) (j := jw) hjwp.le, hpk]
        apply div_lt_div_of_pos_right _ hN; exact_mod_cast hlt
      have := maxwin_order h87 h9 hwm hcm hne' hlt'
      have := mul_le_mul_of_nonneg_left this hN.le
      rw [hcT, hwR'] at this
      rw [hmR, hcwR]; push_cast; linarith
  -- the integer inequality `M bw ≤ cc (D - 1)`
  have hint : ((B : ℤ) - 1) * bw ≤ ccZ * ((D : ℤ) - 1) := by
    rw [hU, hRwdef] at hLU
    have hq0 : (0 : ℝ) < q := by positivity
    have : (bw : ℝ) / (D - 1) ≤ (ccZ : ℝ) / (B - 1) := by
      have h1 : (bw : ℝ) / (D - 1) * q ≤ q * ccZ / (B - 1) := hLU
      have h2 : (bw : ℝ) / (D - 1) * q ≤ (ccZ : ℝ) / (B - 1) * q := by
        calc (bw : ℝ) / (D - 1) * q ≤ q * ccZ / (B - 1) := h1
          _ = (ccZ : ℝ) / (B - 1) * q := by ring
      exact le_of_mul_le_mul_right h2 hq0
    rw [div_le_div_iff₀ hD0 hM0] at this
    have : ((((B : ℤ) - 1) * bw : ℤ) : ℝ) ≤ ((ccZ * ((D : ℤ) - 1) : ℤ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast this
  -- `ℓ ≥ 2`
  have hℓev : Even ℓ := by
    have hMo : Odd ((B : ℤ) - 1) := by
      have : Even (B : ℤ) := by
        rw [← hB]; push_cast; exact Int.even_pow.mpr ⟨even_two, by omega⟩
      exact this.sub_odd odd_one
    have hHe : Even (H : ℤ) := by rw [← hH]; push_cast; exact Int.even_pow.mpr ⟨even_two, by omega⟩
    have hco : Odd (c : ℤ) := (Int.odd_natCast c).mpr hs.hodd
    have hvo : Odd (v : ℤ) := (Int.odd_natCast v).mpr hvodd
    simp only [ℓ, ccZ]
    exact ((hMo.mul hvo).sub_even (hHe.mul_left _)).sub_odd hco
  have hℓ2 : 2 ≤ ℓ := by
    have hbw : (bw : ℤ) = c * H + η * v := by linarith [hv]
    have hη' : η = 1 ∨ η = -1 := by rcases hη with ⟨h', _⟩ | ⟨h', _⟩ <;> [left; right] <;> exact h'
    have hanti : η = -1 → ((B : ℤ) - 1) * v ≠ (H + 1) * c := by
      intro _ heq
      apply hcen.anti (e - hh)
      rw [hH]
      have : (((B - 1) * v : ℕ) : ℤ) = (((H + 1) * c : ℕ) : ℤ) := by
        push_cast [show 1 ≤ B by omega]; exact heq
      have : (B - 1) * v = (H + 1) * c := by exact_mod_cast this
      rw [← this, ← hB]; exact dvd_mul_right _ _
    exact ell_ge_two (by exact_mod_cast hB8) (by exact_mod_cast hH2) (by exact_mod_cast h6)
      (by exact_mod_cast hc1) hη' hbw (by exact_mod_cast hDBH) hint hℓev hanti
  -- `c ≥ b`
  have hccpos : 0 < ccZ := by simp only [ℓ] at hℓ2; omega
  obtain ⟨ccN, hccN⟩ : ∃ ccN : ℕ, (ccN : ℤ) = ccZ := ⟨ccZ.toNat, Int.toNat_of_nonneg hccpos.le⟩
  have hMk : 2 ^ k - 1 = B - 1 := by rw [hB]
  have hBev : Even B := by rw [← hB]; exact Nat.even_pow.mpr ⟨even_two, by omega⟩
  have hcHmod : (c * H) % (B - 1) ≠ 0 := by
    intro h0
    have hdvd : (B - 1) ∣ c * H := Nat.dvd_of_mod_eq_zero h0
    have hcop : Nat.Coprime (B - 1) H := by
      rw [← hH]; apply Nat.Coprime.pow_right
      rw [Nat.coprime_comm, Nat.prime_two.coprime_iff_not_dvd]
      intro h2; obtain ⟨t, ht⟩ := h2; obtain ⟨t', ht'⟩ := hBev; omega
    have := hcop.dvd_of_dvd_mul_right hdvd
    have := Nat.le_of_dvd (by omega) this; omega
  have hsum : ccN + c * H = (B - 1) * v := by
    have : (ccN : ℤ) + c * H = ((B - 1 : ℕ) : ℤ) * v := by
      rw [hccN]; simp only [ccZ]; push_cast [show 1 ≤ B by omega]; ring
    exact_mod_cast this
  have hccmod : ccN % (B - 1) + (c * H) % (B - 1) = B - 1 := by
    have h1 : (ccN + c * H) % (B - 1) = 0 := by rw [hsum]; simp
    rw [Nat.add_mod] at h1
    have h2 := Nat.mod_lt ccN (show 0 < B - 1 by omega)
    have h3 := Nat.mod_lt (c * H) (show 0 < B - 1 by omega)
    obtain ⟨t, ht⟩ := Nat.dvd_of_mod_eq_zero h1
    rcases t with _ | _ | t
    · omega
    · omega
    · have : (B - 1) * 2 ≤ (B - 1) * (t + 1 + 1) := Nat.mul_le_mul_left (B - 1) (by omega)
      omega
  have hbm_le : uo c k j0 ≤ ccN := by
    have h1 := hj0min (e - hh)
    rw [hH, hMk, mul_comm H c] at h1
    have := Nat.mod_le ccN (B - 1)
    omega
  have hbm_ge : c + 2 ≤ uo c k j0 := by
    have h1 := (uo_bounds hcen j0).1
    have h2 : uo c k j0 ≠ c := by
      intro he
      have : uo c k j0 = uo c k 0 := by rw [he]; rfl
      have := uo_inj hcen hj0k (by omega) this
      omega
    obtain ⟨t, ht⟩ := (uo_pos_lt hcen j0).2.2
    obtain ⟨t', ht'⟩ := hs.hodd
    omega
  have hxj0 : xo c k j0 = 1 - (uo c k j0 : ℝ) / (B - 1) := by unfold xo; rw [hBR]
  -- the separator wrapper
  have hsep : ∀ e' : ℤ, Odd e' → wR bw jw * q < e' → (e' : ℝ) < q * ccZ / (B - 1) →
      (∀ g, 1 ≤ g → g < k → (c : ℤ) * 2 ^ g ≤ B * oddDist (2 ^ g) e') → False := by
    intro e' ho hL hU' hmask
    refine sep_contra hc hs h87 h9 h4 (w := w) (by rw [hQ]; exact hw3) hmw hmw' hwing' η hη hfirst
      e' ho ?_ ?_ ?_
    · rw [← hhhdef, hqR]; exact hL
    · rw [hQR]; rw [← hU] at hU'; exact hU'
    · intro g hg1 hgk; have := hmask g hg1 hgk
      have hBZ : ((B : ℕ) : ℤ) = 2 ^ (p - e) := by rw [← hB]; push_cast; ring
      rw [← hBZ]; exact this
  -- positivity facts
  have hc0 : (0 : ℝ) < c := by exact_mod_cast hc1
  have hq0 : (0 : ℝ) < q := by positivity
  have hRpos : 0 < wR c k := wR_pos hs.hodd.pos (by omega)
  have hbmR : ((c : ℝ) + 2) / (B - 1) ≤ (uo c k j0 : ℝ) / (B - 1) := by
    apply div_le_div_of_nonneg_right _ hM0.le; exact_mod_cast hbm_ge
  have hbmcc : (uo c k j0 : ℝ) / (B - 1) ≤ (ccZ : ℝ) / (B - 1) := by
    apply div_le_div_of_nonneg_right _ hM0.le; rw [← hccN]; exact_mod_cast hbm_le
  -- the strict upper bound `e' < U`
  have hUstrict : ∀ e' : ℤ, (e' : ℝ) ≤ q * (uo c k j0 : ℝ) / (B - 1) →
      (e' : ℝ) < q * ccZ / (B - 1) := by
    intro e' he'
    have hle : (e' : ℝ) ≤ q * ccZ / (B - 1) := by
      calc (e' : ℝ) ≤ q * (uo c k j0 : ℝ) / (B - 1) := he'
        _ = q * ((uo c k j0 : ℝ) / (B - 1)) := by ring
        _ ≤ q * ((ccZ : ℝ) / (B - 1)) := mul_le_mul_of_nonneg_left hbmcc hq0.le
        _ = q * ccZ / (B - 1) := by ring
    rcases eq_or_lt_of_le hle with he | he
    · exfalso
      have h1 : (e' : ℝ) * (B - 1) = q * ccZ := by rw [he]; field_simp
      have h2 : e' * ((B : ℤ) - 1) = q * ccZ := by
        have : ((e' * ((B : ℤ) - 1) : ℤ) : ℝ) = ((q * ccZ : ℤ) : ℝ) := by push_cast; linarith
        exact_mod_cast this
      have hMo : Odd ((B : ℤ) - 1) := by
        have : Even (B : ℤ) := (Int.even_natCast B).mpr hBev
        exact this.sub_odd odd_one
      have h3 : ((B : ℤ) - 1) ∣ 2 ^ hh * ccZ := by
        rw [show (2 : ℤ) ^ hh = q by rw [← hq]; push_cast; ring, ← h2]; exact dvd_mul_left _ _
      have h4 := odd_dvd_of_dvd_pow_mul hMo h3
      rw [← hccN] at h4
      have h5 : (B - 1) ∣ ccN := by
        have : (((B - 1 : ℕ) : ℤ)) ∣ (ccN : ℤ) := by push_cast [show 1 ≤ B by omega]; exact h4
        exact Int.natCast_dvd_natCast.mp this
      have := Nat.mod_eq_zero_of_dvd h5
      have := Nat.mod_lt (c * H) (show 0 < B - 1 by omega)
      omega
    · exact he
  -- the mask from the dynamics
  have hmaskR : ∀ e' : ℤ, (∀ g, 1 ≤ g → g < hh → wR c k * 2 ^ g < (oddDist (2 ^ g) e' : ℝ)) →
      ∀ g, 1 ≤ g → g < k → (c : ℤ) * 2 ^ g ≤ B * oddDist (2 ^ g) e' := by
    intro e' hm g hg1 hgk
    have h1 := hm g hg1 (by omega)
    rw [hRdef] at h1
    have hod0 : (0 : ℝ) ≤ oddDist (2 ^ g) e' := by unfold oddDist; positivity
    have : (c : ℝ) * 2 ^ g ≤ B * oddDist (2 ^ g) e' := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ hM0] at h1
      nlinarith only [h1, hod0]
    exact_mod_cast this
  set L : ℝ := wR bw jw * q with hLdef
  set U : ℝ := q * ccZ / (B - 1) with hUdef
  set G : ℕ := gapG k with hGdef
  rcases lt_or_ge (G : ℝ) (U - L) with hbig | hsmall
  · -- a survivor from the gap bound
    have hα : (c : ℝ) / B ≤ 1 / 6 := by
      rw [div_le_iff₀ (by positivity)]; have : (6 * c : ℝ) < B := by exact_mod_cast h6
      linarith
    obtain ⟨e', he1, he2, hsurv⟩ := surv_gap hα (by positivity) k (by omega) ⌊L⌋
    apply hsep e' hsurv.1
    · have h1 := Int.lt_floor_add_one L
      have h2 : ((⌊L⌋ : ℤ) : ℝ) + 1 ≤ e' := by exact_mod_cast he1
      linarith
    · have h1 : (e' : ℝ) ≤ ⌊L⌋ + G := by exact_mod_cast he2
      have h2 := Int.floor_le L
      linarith
    · intro g hg1 hgk
      have h1 := hsurv.2 g hg1 hgk
      have hBpos : (0 : ℝ) < B := by positivity
      have : (c : ℝ) * 2 ^ g ≤ B * oddDist (2 ^ g) e' := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hBpos] at h1; linarith
      exact_mod_cast this
  · -- the dynamics
    have hh2 : 2 ≤ hh := by omega
    have hcovn := hcov (hh - 1) (by omega)
    have hq' : (2 : ℝ) ^ (hh - 1) * 2 = q := by
      rw [← hqR, ← pow_succ]; congr 1; omega
    have hlam : lam c k = 1 - wR c k := rfl
    have hR3 := wR_le_third (a := c) (k := k) (by omega) (by omega)
    rcases hη with ⟨hη1, hlt⟩ | ⟨hη1, hlt⟩
    · -- right wing: truncation
      have hbw : (bw : ℤ) = c * H + v := by rw [hη1] at hv; linarith
      have hbwR : (bw : ℝ) = c * H + v := by exact_mod_cast hbw
      have hBH1ne : (B : ℝ) * H - 1 ≠ 0 := by nlinarith only [hB8R, hH2R]
      have hM1ne : (B : ℝ) - 1 ≠ 0 := by linarith
      have hRwR : wR bw jw - wR c k = (ℓ + 2 * c : ℝ) / ((B - 1) * (B * H - 1)) := by
        rw [hRwdef, hRdef, hDBHR, hbwR]; simp only [ℓ, ccZ]; push_cast
        rw [div_sub_div _ _ hBH1ne hM1ne,
          div_eq_div_iff (mul_ne_zero hBH1ne hM1ne) (mul_ne_zero hM1ne hBH1ne)]
        ring
      have hUL : U - L = q * ((ℓ : ℝ) * (B * H - 2) - 2 * c) / ((B - 1) * (B * H - 1)) := by
        simp only [U, L]; rw [hRwdef, hDBHR, hbwR]; simp only [ℓ, ccZ]; push_cast
        rw [div_mul_eq_mul_div, div_sub_div _ _ hM1ne hBH1ne,
          div_eq_div_iff (mul_ne_zero hM1ne hBH1ne) (mul_ne_zero hM1ne hBH1ne)]
        ring
      have hGreal := gapG_real (k := k)
      rw [hBR] at hGreal
      have hE := E_bound_arith (B := B) (H := H) (q := q) (c := c) (v := v) (ℓ := ℓ) (G := G)
        hB8R hH2R hqBR (by exact_mod_cast hc1) (by exact_mod_cast hv1)
        (by have : 6 * c + 2 ≤ B := by obtain ⟨t, ht⟩ := hBev; omega
            have : (6 * c + 2 : ℝ) ≤ B := by exact_mod_cast this
            linarith)
        (by exact_mod_cast hℓ2) (by simp only [ℓ, ccZ]; push_cast; ring)
        (by rw [hGreal]; split_ifs <;> linarith)
        (by
          rw [hGreal]
          split_ifs with hev
          · right; refine ⟨rfl, ?_⟩
            have hm3 := two_pow_mod_three k
            rw [ite_eq_left hev] at hm3
            have h4 : 4 ∣ B := by
              rw [← hB, show 4 = 2 ^ 2 by norm_num]; exact Nat.pow_dvd_pow 2 (by omega)
            obtain ⟨t, ht⟩ := h4
            obtain ⟨α, hα⟩ := hs.hodd
            rw [hB] at hm3
            have : 6 * c + 10 ≤ B := by omega
            have : (6 * c + 10 : ℝ) ≤ B := by exact_mod_cast this
            linarith
          · left; rfl)
        (by rw [← hUL]; exact hsmall)
        (by
          intro hlt2
          have hlt3 : q < B ^ 2 := by exact_mod_cast hlt2
          have h2q : 2 * q ≤ B ^ 2 := by
            rw [← hq, ← hB, ← pow_mul] at hlt3 ⊢; exact two_pow_step hlt3
          exact_mod_cast h2q)
        (by
          intro hHB
          by_contra hh5
          push Not at hh5
          have hH4 : 4 ≤ H := by omega
          have hd2 : 2 ≤ e - hh := by
            by_contra hh6; push Not at hh6
            have : H ≤ 2 ^ 1 := by rw [← hH]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
            omega
          have hdk : e - hh < k := by
            by_contra hh6; push Not at hh6
            have : B ≤ H := by rw [← hB, ← hH]; exact Nat.pow_le_pow_right (by norm_num) hh6
            have : (B : ℝ) ≤ H := by exact_mod_cast this
            linarith
          have hHR' : (2 : ℝ) ^ (e - hh) = H := by rw [← hH]; push_cast; ring
          apply hcen.maxi v (e - hh) hd2 hdk hvodd (by rw [hH]; exact hv3)
          · unfold wT wR; rw [hHR', hBR]
            have : (v : ℝ) * (H - 2) / (H * (H - 1)) = v / (H - 1) * (1 - 2 / H) := by
              have : (H : ℝ) ≠ 0 := by positivity
              have : (H : ℝ) - 1 ≠ 0 := by linarith
              field_simp
            rw [← this]; exact hh5
          · unfold wR; rw [hHR', hBR]
            have hℓR : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ2
            have : (c : ℝ) * (H + 1) < (B - 1) * v := by
              have : (ℓ : ℝ) = (B - 1) * v - c * H - c := by simp only [ℓ, ccZ]; push_cast; ring
              linarith
            rw [div_lt_div_iff₀ hM0 (by linarith)]
            nlinarith only [this, hc0])
      have hEq : q * (wR bw jw - wR c k) < 1 - 4 * wR c k := by
        rw [hRwR, hRdef, ← mul_div_assoc]; exact hE
      have hRle : wR c k ≤ wR bw jw := by
        have : 0 ≤ (ℓ + 2 * c : ℝ) / ((B - 1) * (B * H - 1)) := by
          apply div_nonneg _ (mul_pos hM0 (by nlinarith only [hB8R, hH2R])).le
          have : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ2
          linarith
        linarith
      have hlo : xo c k j0 ≤ 1 - wR bw jw := by
        rw [hxj0]
        have h1 : wR bw jw - wR c k < 1 / q := by
          rw [lt_div_iff₀ hq0]; nlinarith
        have h2 : (1 : ℝ) / q ≤ 1 / B := one_div_le_one_div_of_le (by positivity) hqBR
        have h3 : (1 : ℝ) / B < 2 / (B - 1) := by
          rw [div_lt_div_iff₀ (by positivity) hM0]; linarith
        have h4 : ((c : ℝ) + 2) / (B - 1) = wR c k + 2 / (B - 1) := by rw [hRdef]; field_simp
        linarith
      obtain ⟨z, hz1, hz2, hzv⟩ := trunc_half hcen hcovn hq' hRle hEq hlo
      have hzu : 0 ≤ z ∧ z ≤ 1 := by
        constructor
        · have := xo_nonneg hcen j0; linarith
        · have := wR_pos (b := bw) (j := jw) hwm.1.2.2.1.pos hjw1; linarith
      obtain ⟨e', ho, he', hmk⟩ := extract hcen hzu hh2 hzv
      rw [hqR] at he'
      apply hsep e' ho _ _ (hmaskR e' hmk)
      · -- `L < e'` with strictness from integrality
        have hle : wR bw jw * q ≤ e' := by rw [he']; nlinarith
        rcases eq_or_lt_of_le hle with heq | hlt'
        · exfalso
          rw [hRwdef] at heq
          have h1 : (e' : ℝ) * (D - 1) = q * bw := by rw [← heq]; field_simp
          have h2 : e' * ((D : ℤ) - 1) = q * bw := by
            have : ((e' * ((D : ℤ) - 1) : ℤ) : ℝ) = ((q * bw : ℤ) : ℝ) := by push_cast; linarith
            exact_mod_cast this
          have hDo : Odd ((D : ℤ) - 1) := by
            have : Even (D : ℤ) := by rw [← hD]; push_cast; exact Int.even_pow.mpr ⟨even_two, by omega⟩
            exact this.sub_odd odd_one
          have h3 : ((D : ℤ) - 1) ∣ 2 ^ hh * bw := by
            rw [show (2 : ℤ) ^ hh = q by rw [← hq]; push_cast; ring, ← h2]; exact dvd_mul_left _ _
          have h4 := odd_dvd_of_dvd_pow_mul hDo h3
          have h5 := Int.le_of_dvd (by have := hwm.1.2.2.1.pos; omega) h4
          have h6' := hwm.1.2.2.2
          rw [hD] at h6'
          have h7 : (3 * bw : ℤ) < D := by exact_mod_cast h6'
          omega
        · exact hlt'
      · apply hUstrict
        rw [he']
        have : 1 - z ≤ (uo c k j0 : ℝ) / (B - 1) := by rw [hxj0] at hz1; linarith
        rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left this hq0.le
    · -- left wing: the whole interval
      have hbw : (bw : ℤ) = c * H - v := by rw [hη1] at hv; linarith
      have hbwR : (bw : ℝ) = c * H - v := by exact_mod_cast hbw
      have hRw_lt : wR bw jw < wR c k := by
        rw [hRwdef, hRdef, hDBHR, hbwR, div_lt_div_iff₀ (by nlinarith only [hB8R, hH2R]) hM0]
        have hv1R : (1 : ℝ) ≤ v := by exact_mod_cast hv1
        nlinarith only [hv1R, hc0, hH2R, hB8R]
      have hR6 : wR c k < 1 / 6 := by
        rw [hRdef, div_lt_iff₀ hM0]
        have h62 : 6 * c + 2 ≤ B := by obtain ⟨t, ht⟩ := hBev; omega
        have : (6 * c + 2 : ℝ) ≤ B := by exact_mod_cast h62
        linarith
      obtain ⟨z, hz, hzv⟩ := hcovn (⟨by linarith, by rw [hlam]; linarith⟩ :
        (1 / 2 : ℝ) ∈ Set.Icc (2 * wR c k) (lam c k))
      have hzu : 0 ≤ z ∧ z ≤ 1 := topI_sub_unit hcen hz
      obtain ⟨e', ho, he', hmk⟩ := extract hcen hzu hh2 hzv
      rw [hqR] at he'
      apply hsep e' ho _ _ (hmaskR e' hmk)
      · have : wR c k ≤ 1 - z := by have := hz.2; rw [hlam] at this; linarith
        rw [he']
        have := mul_le_mul_of_nonneg_left this hq0.le
        have := mul_lt_mul_of_pos_right hRw_lt hq0
        linarith
      · apply hUstrict
        rw [he']
        have : 1 - z ≤ (uo c k j0 : ℝ) / (B - 1) := by
          have := hz.1; rw [hxj0] at this; linarith
        rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left this hq0.le

end

end GrayNecklaces
