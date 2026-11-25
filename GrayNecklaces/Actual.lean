module

public import GrayNecklaces.TiozzoBridge

/-!
# Actual windows from Tiozzo's theorems

* `exists_actual` (from `Theorem87`): every admissible window is contained in an actual window
  with at most its denominator.
* `actual_nested` (from `TuningNesting`): actual windows with overlapping interiors are nested.
-/

@[expose] public section

namespace GrayNecklaces

open Tiozzo

lemma nint_intCast (n : ℤ) : nint n = 0 := by
  rw [show (n : ℝ) = 0 + n by ring, nint_add_int, nint_of_mem le_rfl (by norm_num)]

/-- Containment of windows from containment of the hole of `b/2^j` in the gap of `a/2^k`. -/
lemma winLE_of_hole {b j a k : ℕ} (hk : 1 ≤ k) (hkj : k ≤ j)
    (h1 : (b : ℝ) / (2 ^ j - 1) ≤ wR a k) (h2 : (a : ℝ) / (2 ^ k + 1) ≤ b / (2 ^ j + 1)) :
    WinLE b j a k := by
  refine ⟨?_, h1⟩
  have hj : 1 ≤ j := le_trans hk hkj
  rw [wT_eq hk, wT_eq hj]
  set B : ℝ := 2 ^ k
  set H : ℝ := 2 ^ (j - k)
  have hD : (2:ℝ) ^ j = B * H := by rw [← pow_add]; congr 1; omega
  have hB2 : (2 : ℝ) ≤ B := by
    have := pow_le_pow_right₀ (show (1:ℝ) ≤ 2 by norm_num) hk; simpa [B] using this
  have hH1 : (1 : ℝ) ≤ H := one_le_pow₀ (by norm_num)
  have hRb : wR b j ≤ wR a k := h1
  have hR : (a : ℝ) / (B + 1) ≤ wR a k := left_le_wR hk
  rw [hD] at h2 ⊢
  -- `b ≥ a (BH+1)/(B+1)`
  have hb : (a : ℝ) * (B * H + 1) / (B + 1) ≤ b := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)] at h2
    rw [div_le_iff₀ (by positivity)]; linarith
  have key : (a : ℝ) * H - wR a k * H ≤ b - wR b j := by
    have e : (a : ℝ) * (B * H + 1) / (B + 1) = a * H - (a / (B + 1)) * (H - 1) := by
      field_simp; ring
    rw [e] at hb
    nlinarith
  have hBH : (0 : ℝ) < B * H := by positivity
  rw [show (a : ℝ) / B - wR a k / B = (a * H - wR a k * H) / (B * H) by field_simp,
    show (b : ℝ) / (B * H) - wR b j / (B * H) = (b - wR b j) / (B * H) by ring]
  exact div_le_div_of_nonneg_right key hBH.le

lemma pow_pos_cast (n : ℕ) : ((2 : ℕ) ^ n : ℝ) = (2 : ℝ) ^ n := by push_cast; ring

/-- **Dummy containment.** -/
theorem exists_actual (h87 : Theorem87) {b j : ℕ} (hj : 2 ≤ j) (hb : Odd b)
    (h3 : 3 * b < 2 ^ j) : ∃ a k, k ≤ j ∧ IsActual a k ∧ WinLE b j a k := by
  classical
  have hbpos := hb.pos
  have hD4 : (4:ℝ) ≤ 2 ^ j := two_pow_ge_four hj
  have hb3 : (3:ℝ) * b < 2 ^ j := by exact_mod_cast h3
  have hbr : (0 : ℝ) < b := by exact_mod_cast hbpos
  set x0 : ℝ := b / 2 ^ j with hx0def
  have hx0pos : 0 < x0 := by positivity
  have hx0 : x0 < 1 / 3 := by rw [hx0def, div_lt_iff₀ (by positivity)]; linarith
  set θ0 := (1 - x0) / 2 with hθ0def
  have hθ0R : θ0 ∉ realAngles := by
    rw [hθ0def, inK_iff_angle hx0pos.le (by linarith)]
    rintro ⟨_, hK⟩
    have h := hK j
    have : (2:ℝ) ^ j * x0 = ((b : ℤ) : ℝ) := by rw [hx0def]; push_cast; field_simp
    rw [this, nint_intCast] at h
    linarith
  -- the real hyperbolic window containing `θ0`
  set A := {θ : ℝ | 1 / 3 ≤ θ ∧ θ ≤ θ0 ∧ ∀ n : ℕ, tent^[n] (2 * θ) ≤ 2 * θ}
  set Bs := {θ : ℝ | θ0 ≤ θ ∧ θ ≤ 1 / 2 ∧ ∀ n : ℕ, tent^[n] (2 * θ) ≤ 2 * θ}
  have hAc : IsClosed A := isClosed_angleSet _ _
  have hBc : IsClosed Bs := isClosed_angleSet _ _
  have h13 : ∀ n : ℕ, tent^[n] (2 * (1 / 3 : ℝ)) ≤ 2 * (1 / 3) :=
    (mem_realAngles_iff (by norm_num) (by norm_num)).mp one_third_mem
  have h12 : ∀ n : ℕ, tent^[n] (2 * (1 / 2 : ℝ)) ≤ 2 * (1 / 2) :=
    (mem_realAngles_iff (by norm_num) le_rfl).mp half_mem
  have hAne : (1 / 3 : ℝ) ∈ A := ⟨le_rfl, by rw [hθ0def]; linarith, h13⟩
  have hBne : (1 / 2 : ℝ) ∈ Bs := ⟨by rw [hθ0def]; linarith, le_rfl, h12⟩
  have hAbdd : BddAbove A := ⟨θ0, fun θ h => h.2.1⟩
  have hBbdd : BddBelow Bs := ⟨θ0, fun θ h => h.1⟩
  set θ₂ := sSup A with hθ₂def
  set θ₁ := sInf Bs with hθ₁def
  have hθ₂A : θ₂ ∈ A := hAc.csSup_mem ⟨_, hAne⟩ hAbdd
  have hθ₁B : θ₁ ∈ Bs := hBc.csInf_mem ⟨_, hBne⟩ hBbdd
  have hθ₂R : θ₂ ∈ realAngles :=
    (mem_realAngles_iff (by linarith [hθ₂A.1]) (by linarith [hθ₂A.2.1])).mpr hθ₂A.2.2
  have hθ₁R : θ₁ ∈ realAngles :=
    (mem_realAngles_iff (by linarith [hθ₁B.1]) hθ₁B.2.1).mpr hθ₁B.2.2
  have hlt2 : θ₂ < θ0 := lt_of_le_of_ne hθ₂A.2.1 (fun h => hθ0R (h ▸ hθ₂R))
  have hlt1 : θ0 < θ₁ := lt_of_le_of_ne hθ₁B.1 (fun h => hθ0R (h ▸ hθ₁R))
  have hwin : IsRealHyperbolicWindow θ₂ θ₁ := by
    refine ⟨by linarith [hθ₂A.1], by linarith, hθ₁B.2.1, hθ₂R, hθ₁R, ?_⟩
    intro θ h1 h2 hθ
    have hθ' := (mem_realAngles_iff (by linarith [hθ₂A.1]) (by linarith [hθ₁B.2.1])).mp hθ
    rcases le_total θ θ0 with h | h
    · have : θ ≤ θ₂ := le_csSup hAbdd ⟨by linarith [hθ₂A.1], h, hθ'⟩
      linarith
    · have : θ₁ ≤ θ := csInf_le hBbdd ⟨h, by linarith [hθ₁B.2.1], hθ'⟩
      linarith
  -- the pseudocenter
  have hex : ∃ n : ℕ, ∃ c : ℤ, θ₂ < c / 2 ^ n ∧ (c : ℝ) / 2 ^ n < θ₁ := by
    refine ⟨j + 1, 2 ^ j - b, ?_⟩
    have : (((2 ^ j - b : ℤ)) : ℝ) / 2 ^ (j + 1) = θ0 := by
      rw [hθ0def, hx0def]; push_cast; field_simp; ring
    rw [this]; exact ⟨hlt2, hlt1⟩
  set n := Nat.find hex with hndef
  obtain ⟨c, hc1, hc2⟩ := Nat.find_spec hex
  have hmin : ∀ (n' : ℕ) (c' : ℤ), θ₂ < c' / 2 ^ n' → (c' : ℝ) / 2 ^ n' < θ₁ → n ≤ n' :=
    fun n' c' h1 h2 => Nat.find_min' hex ⟨c', h1, h2⟩
  have hlo : (1 : ℝ) / 3 < c / 2 ^ n := by linarith [hθ₂A.1]
  have hhi : (c : ℝ) / 2 ^ n < 1 / 2 := by linarith [hθ₁B.2.1]
  have hP : (0 : ℝ) < 2 ^ n := by positivity
  have hlo' : (2 : ℝ) ^ n < 3 * c := by rw [lt_div_iff₀ hP] at hlo; linarith
  have hhi' : (2 : ℝ) * c < 2 ^ n := by rw [div_lt_iff₀ hP] at hhi; linarith
  have hcpos : 0 < c := by
    have : (0 : ℝ) < c := by linarith
    exact_mod_cast this
  have hn2 : 2 ≤ n := by
    by_contra hh
    have : (2 : ℝ) ^ n ≤ 2 := by
      have := pow_le_pow_right₀ (show (1:ℝ) ≤ 2 by norm_num) (show n ≤ 1 by omega)
      simpa using this
    have : (c : ℝ) < 1 := by linarith
    have : c < 1 := by exact_mod_cast this
    omega
  have hcodd : Odd c := by
    by_contra hev
    rw [Int.not_odd_iff_even] at hev
    obtain ⟨r, hr⟩ := hev
    have e : (c : ℝ) / 2 ^ n = (r : ℝ) / 2 ^ (n - 1) := by
      have hpow : (2:ℝ) ^ n = 2 ^ (n - 1) * 2 := by rw [← pow_succ]; congr 1; omega
      rw [hr, hpow]; push_cast; field_simp; ring
    have := hmin (n - 1) r (by rw [← e]; exact hc1) (by rw [← e]; exact hc2)
    omega
  -- natural-number data
  set k := n - 1 with hkdef
  have hnk : n = k + 1 := by omega
  obtain ⟨cn, hcn⟩ : ∃ cn : ℕ, (cn : ℤ) = c := ⟨c.toNat, Int.toNat_of_nonneg hcpos.le⟩
  have hcnR : (cn : ℝ) = c := by rw [← hcn]; push_cast; ring
  have hcnodd : cn % 2 = 1 := by
    obtain ⟨t, ht⟩ := hcodd; omega
  have hcnlt : cn < 2 ^ k := by
    have : (2 : ℝ) * cn < 2 ^ (k + 1) := by rw [hcnR, ← hnk]; exact hhi'
    rw [pow_succ] at this
    have : (cn : ℝ) < 2 ^ k := by linarith
    exact_mod_cast this
  set u := cn / 2 with hudef
  have hcnu : cn = 2 * u + 1 := by omega
  have hult : u < 2 ^ k := by omega
  have hk1 : 1 ≤ k := by omega
  -- the binary word of the pseudocenter
  set s := natBits n cn with hsdef
  have hfin : finBin s = c / 2 ^ n := by
    rw [hsdef, finBin_natBits, Nat.mod_eq_of_lt (by rw [hnk, pow_succ]; omega), hcnR]
  have hlast : s.getLast? = some true := by
    rw [hsdef, hnk, natBits_succ_getLast]; simp [hcnodd]
  have hpc : IsPseudocenter θ₂ θ₁ (finBin s) := by
    rw [hfin]; exact ⟨hc1, hc2, n, ⟨c, rfl⟩, hmin⟩
  obtain ⟨e2, e1⟩ := h87 θ₂ θ₁ s hwin hpc hlast
  have hdrop : s.dropLast = natBits k u := by rw [hsdef, hnk, natBits_succ_dropLast]
  rw [hdrop] at e2 e1
  have hPk : (1 : ℝ) < 2 ^ k := one_lt_pow₀ (by norm_num) (by omega)
  have huR : (u : ℝ) < 2 ^ k := by exact_mod_cast hult
  have hfinu : finBin (natBits k u) = u / 2 ^ k := by
    rw [finBin_natBits, Nat.mod_eq_of_lt hult]
  have hθ₂ : θ₂ = u / (2 ^ k - 1) := by
    rw [e2, perBin_eq _ (by rw [natBits_length]; omega), natBits_length, hfinu]
    field_simp
  have hθ₁ : θ₁ = (u + 1) / (2 ^ k + 1) := by
    rw [e1, perBin_eq _ (by simp [natBits_length]; omega), finBin_append, finBin_map_not,
      hfinu]
    simp only [List.length_append, List.length_map, natBits_length]
    rw [pow_add]
    set P : ℝ := 2 ^ k
    have hne : P * P - 1 ≠ 0 := by nlinarith
    rw [div_eq_div_iff hne (by positivity)]
    field_simp
    ring
  -- the actual window `a/2^k`
  set a := 2 ^ k - cn with hadef
  have haR : (a : ℝ) = 2 ^ k - 2 * u - 1 := by
    rw [hadef, Nat.cast_sub hcnlt.le, hcnu]; push_cast; ring
  have hwRa : wR a k = (2 ^ k - 2 * u - 1) / (2 ^ k - 1) := by unfold wR; rw [haR]
  have hθ₂' : (1 - wR a k) / 2 = θ₂ := by
    rw [hwRa, hθ₂]; field_simp; ring
  have hθ₁' : (1 - (a : ℝ) / (2 ^ k + 1)) / 2 = θ₁ := by
    rw [haR, hθ₁]; field_simp; ring
  have hcst : (c : ℝ) / 2 ^ n = 1 / 2 - (a : ℝ) / 2 ^ (k + 1) := by
    rw [← hcnR, haR, hnk, hcnu]; push_cast; rw [pow_succ]; field_simp; ring
  have ha3 : 3 * a < 2 ^ k := by
    have : (3 : ℝ) * a < 2 ^ k := by
      have h := hlo; rw [hcst] at h
      have h' : (a : ℝ) / 2 ^ (k + 1) < 1 / 6 := by linarith
      rw [div_lt_iff₀ (by positivity), pow_succ] at h'
      linarith
    exact_mod_cast this
  have haodd : Odd a := by
    have : Even (2 ^ k) := (Nat.even_pow.mpr ⟨even_two, by omega⟩)
    obtain ⟨t, ht⟩ := this
    exact ⟨t - u - 1, by omega⟩
  have hk2 : 2 ≤ k := by
    have := haodd.pos
    by_contra hh
    have : 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hminx : ∀ (n' : ℕ) (c' : ℤ), (a : ℝ) / (2 ^ k + 1) < c' / 2 ^ n' →
      (c' : ℝ) / 2 ^ n' < wR a k → k ≤ n' := by
    intro n' c' h1 h2
    have e : (((2 ^ n' - c' : ℤ)) : ℝ) / 2 ^ (n' + 1) = (1 - (c' : ℝ) / 2 ^ n') / 2 := by
      push_cast; rw [pow_succ]; field_simp
    have := hmin (n' + 1) (2 ^ n' - c') (by rw [e, ← hθ₂']; linarith)
      (by rw [e, ← hθ₁']; linarith)
    omega
  have hact : IsActual a k := by
    refine ⟨hk2, haodd, ha3, ?_, hminx⟩
    rw [hθ₂', hθ₁']; exact hwin
  -- `b/2^j` lies in the gap, so `k ≤ j`
  have hx0lo : (a : ℝ) / (2 ^ k + 1) < x0 := by
    have : θ0 < (1 - (a : ℝ) / (2 ^ k + 1)) / 2 := by rw [hθ₁']; exact hlt1
    rw [hθ0def] at this; linarith
  have hx0hi : x0 < wR a k := by
    have : (1 - wR a k) / 2 < θ0 := by rw [hθ₂']; exact hlt2
    rw [hθ0def] at this; linarith
  have hkj : k ≤ j := hminx j b (by push_cast; exact hx0lo) (by push_cast; exact hx0hi)
  refine ⟨a, k, hkj, hact, winLE_of_hole hk1 hkj ?_ ?_⟩
  · by_contra hh
    push Not at hh
    apply hole_not_inK (c := b) (i := j) (by omega) (y := wR a k) _ hh hact.inK_right
    calc (b : ℝ) / (2 ^ j + 1) < x0 := by
          rw [hx0def]; apply div_lt_div_of_pos_left hbr (by positivity) (by linarith)
      _ < wR a k := hx0hi
  · by_contra hh
    push Not at hh
    apply hole_not_inK (c := b) (i := j) (by omega) (y := (a : ℝ) / (2 ^ k + 1)) hh _
      hact.inK_left
    calc (a : ℝ) / (2 ^ k + 1) < x0 := hx0lo
      _ < b / (2 ^ j - 1) := by
          rw [hx0def]; apply div_lt_div_of_pos_left hbr (by linarith) (by linarith)

/-! ### Nesting -/

lemma nint_half_add {m : ℤ} {y : ℝ} (hy : |y| ≤ 1 / 2) : nint (m + 1 / 2 + y) = 1 / 2 - |y| := by
  rcases le_total 0 y with h | h
  · rw [nint_eq_abs_sub (n := m + 1) (by
      rw [abs_le] at hy ⊢; push_cast; constructor <;> linarith)]
    push_cast; rw [abs_of_nonpos (by rw [abs_of_nonneg h] at hy; linarith), abs_of_nonneg h]; ring
  · rw [nint_eq_abs_sub (n := m) (by
      rw [abs_le] at hy ⊢; constructor <;> linarith)]
    rw [abs_of_nonpos h] at hy ⊢
    rw [abs_of_nonneg (by linarith)]; ring

/-- `T^k` near the apex `1 - a/2^k`. -/
lemma tent_iterate_apex {a k : ℕ} (hk : 1 ≤ k) (ha : Odd a) (hak : a < 2 ^ k) {z : ℝ}
    (hz : |z - (1 - a / 2 ^ k)| ≤ 1 / 2 ^ k) :
    tent^[k] z = 1 - 2 ^ k * |z - (1 - a / 2 ^ k)| := by
  have hP : (0 : ℝ) < 2 ^ k := by positivity
  have haR : (a : ℝ) < 2 ^ k := by exact_mod_cast hak
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha.pos
  have hz0 : 0 ≤ z ∧ z ≤ 1 := by
    rw [abs_le] at hz
    have : (1 : ℝ) / 2 ^ k ≤ a / 2 ^ k := div_le_div_of_nonneg_right ha1 hP.le
    have : (a : ℝ) / 2 ^ k + 1 / 2 ^ k ≤ 1 := by
      rw [← add_div, div_le_one hP]
      have : a + 1 ≤ 2 ^ k := hak
      exact_mod_cast this
    constructor <;> linarith
  obtain ⟨t, ht⟩ := ha
  rw [show k = (k - 1) + 1 by omega, tent_iterate hz0.1 hz0.2, show k - 1 + 1 = k by omega]
  set y := 2 ^ (k - 1) * (z - (1 - a / 2 ^ k))
  have hsplit : (2 : ℝ) ^ (k - 1) * z = ((2 ^ (k - 1) - t - 1 : ℤ) : ℝ) + 1 / 2 + y := by
    have : (2:ℝ) ^ k = 2 * 2 ^ (k - 1) := by rw [← pow_succ']; congr 1; omega
    simp only [y]; push_cast
    have hat : (a : ℝ) = 2 * t + 1 := by exact_mod_cast ht
    rw [hat, this]; field_simp; ring
  have hy : |y| ≤ 1 / 2 := by
    simp only [y]; rw [abs_mul, abs_of_pos (by positivity)]
    have : (2:ℝ) ^ k = 2 * 2 ^ (k - 1) := by rw [← pow_succ']; congr 1; omega
    calc (2:ℝ) ^ (k - 1) * |z - (1 - a / 2 ^ k)| ≤ 2 ^ (k - 1) * (1 / 2 ^ k) :=
          mul_le_mul_of_nonneg_left hz (by positivity)
      _ = 1 / 2 := by rw [this]; field_simp
  rw [hsplit, nint_half_add hy]
  simp only [y]; rw [abs_mul, abs_of_pos (by positivity)]
  have : (2:ℝ) ^ k = 2 * 2 ^ (k - 1) := by rw [← pow_succ']; congr 1; omega
  rw [this]; ring

lemma IsActual.tuningEnd {a k : ℕ} (h : IsActual a k) :
    IsTuningEnd (leafLength ((1 - wR a k) / 2)) k (1 - wT a k) := by
  obtain ⟨hk, ha, h3, _, _⟩ := h
  have hk1 : 1 ≤ k := by omega
  have hR := wR_pos ha.pos hk1
  have hR3 := wR_le_third hk1 h3
  have hReq := wR_eq (b := a) hk1
  have hTeq := wT_eq (b := a) hk1
  have hP : (0 : ℝ) < 2 ^ k := by positivity
  have hP2 : (2 : ℝ) ≤ 2 ^ k := by
    have := pow_le_pow_right₀ (show (1:ℝ) ≤ 2 by norm_num) hk1; simpa using this
  have hak : a < 2 ^ k := by omega
  rw [leafLength_of_le (by linarith), show 2 * ((1 - wR a k) / 2) = 1 - wR a k by ring]
  have hRB : wR a k / 2 ^ k ≤ 1 / 2 ^ k := div_le_div_of_nonneg_right (by linarith) hP.le
  refine ⟨by rw [hTeq]; nlinarith [div_pos hR hP], ?_, ?_⟩
  · rw [tent_iterate_apex hk1 ha hak]
    · rw [hTeq, show 1 - (a / 2 ^ k - wR a k / 2 ^ k) - (1 - a / 2 ^ k) = wR a k / 2 ^ k by ring,
        abs_of_pos (by positivity)]
      field_simp
    · rw [hTeq, show 1 - (a / 2 ^ k - wR a k / 2 ^ k) - (1 - a / 2 ^ k) = wR a k / 2 ^ k by ring,
        abs_of_pos (by positivity)]; exact hRB
  · intro x hx1 hx2 heq
    have hxc : |x - (1 - a / 2 ^ k)| < wR a k / 2 ^ k := by
      rw [abs_lt]; constructor
      · have := hx1; rw [hReq] at this; linarith
      · have := hx2; rw [hTeq] at this; linarith
    rw [tent_iterate_apex hk1 ha hak (by linarith)] at heq
    have : 2 ^ k * |x - (1 - a / 2 ^ k)| < wR a k := by
      calc 2 ^ k * |x - (1 - a / 2 ^ k)| < 2 ^ k * (wR a k / 2 ^ k) :=
            mul_lt_mul_of_pos_left hxc hP
        _ = wR a k := by field_simp
    linarith

lemma IsActual.doublingPeriod {a k : ℕ} (h : IsActual a k) :
    DoublingPeriod ((1 - wR a k) / 2) k := by
  have hk : 2 ≤ k := h.1
  have ha := h.2.1
  have h3 := h.2.2.1
  have hprim := h.prim
  have hP1 : (1 : ℝ) < 2 ^ k := one_lt_pow₀ (by norm_num) (by omega)
  -- `θ₂ = u / (2^k - 1)` with `2u = 2^k - 1 - a`
  obtain ⟨t, ht⟩ := ha
  have hak : a < 2 ^ k := by omega
  have hPev : Even (2 ^ k) := Nat.even_pow.mpr ⟨even_two, by omega⟩
  obtain ⟨P, hPdef⟩ := hPev
  set u : ℕ := P - t - 1 with hu
  have h2u : 2 * u + a + 1 = 2 ^ k := by omega
  have h2uR : (2 * u : ℝ) + a + 1 = 2 ^ k := by exact_mod_cast h2u
  have h2uZ : (2 * u : ℤ) + a + 1 = 2 ^ k := by exact_mod_cast h2u
  have hθ : (1 - wR a k) / 2 = (u : ℝ) / (2 ^ k - 1) := by
    unfold wR
    field_simp; linarith
  rw [hθ]
  refine ⟨by omega, ?_, ?_⟩
  · rw [Int.fract_eq_fract]
    refine ⟨u, ?_⟩
    field_simp; push_cast; ring
  · intro m hm hmk heq
    rw [Int.fract_eq_fract] at heq
    obtain ⟨z, hz⟩ := heq
    apply hprim m hm hmk
    have hzR : ((2 : ℝ) ^ m - 1) * u = z * (2 ^ k - 1) := by
      have : (2 : ℝ) ^ m * (u / (2 ^ k - 1)) - u / (2 ^ k - 1) =
          ((2 : ℝ) ^ m - 1) * u / (2 ^ k - 1) := by ring
      rw [this, div_eq_iff (by linarith)] at hz; exact hz
    have hzZ : ((2 : ℤ) ^ m - 1) * u = z * (2 ^ k - 1) := by exact_mod_cast hzR
    have hdZ : ((2 ^ k - 1 : ℕ) : ℤ) ∣ ((2 ^ m - 1) * a : ℕ) := by
      have e1 : (((2 ^ m - 1) * a : ℕ) : ℤ) =
          ((2 : ℤ) ^ m - 1) * (2 ^ k - 1) - 2 * (z * (2 ^ k - 1)) := by
        rw [← hzZ]
        push_cast [Nat.one_le_two_pow]
        linear_combination (2 ^ m - 1 : ℤ) * h2uZ
      rw [e1]
      push_cast [Nat.one_le_two_pow]
      exact Dvd.dvd.sub (dvd_mul_left _ _) (Dvd.dvd.mul_left (dvd_mul_left _ _) _)
    exact Int.natCast_dvd_natCast.mp hdZ

/-- **Nesting of actual windows.** -/
theorem actual_nested (h9 : TuningNesting) {a k a' k' : ℕ} (h : IsActual a k)
    (h' : IsActual a' k') {y : ℝ} (hy1 : wT a k < y) (hy2 : y < wR a k)
    (hy1' : wT a' k' < y) (hy2' : y < wR a' k') :
    WinLE a k a' k' ∨ WinLE a' k' a k := by
  have hw := h.2.2.2.1
  have hw' := h'.2.2.2.1
  have hl : leafLength ((1 - wR a k) / 2) = 1 - wR a k := by
    rw [leafLength_of_le]; ring
    have := wR_pos h.2.1.pos (show 1 ≤ k by have := h.1; omega); linarith
  have hl' : leafLength ((1 - wR a' k') / 2) = 1 - wR a' k' := by
    rw [leafLength_of_le]; ring
    have := wR_pos h'.2.1.pos (show 1 ≤ k' by have := h'.1; omega); linarith
  have hnest := h9 _ _ _ _ _ _ k k' hw hw' h.doublingPeriod h'.doublingPeriod h.tuningEnd
    h'.tuningEnd
  rw [hl, hl'] at hnest
  have hov : (Set.Ioc (1 - wR a k) (1 - wT a k) ∩ Set.Ioc (1 - wR a' k') (1 - wT a' k')).Nonempty :=
    ⟨1 - y, ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have hlt : 1 - wR a k < 1 - wT a k := by linarith
  have hlt' : 1 - wR a' k' < 1 - wT a' k' := by linarith
  rcases hnest hov with hs | hs
  · rw [Set.Ioc_subset_Ioc_iff hlt] at hs
    left; exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  · rw [Set.Ioc_subset_Ioc_iff hlt'] at hs
    right; exact ⟨by linarith [hs.1], by linarith [hs.2]⟩

end GrayNecklaces
