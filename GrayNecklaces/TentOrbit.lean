module

public import GrayNecklaces.Maximal

/-!
# The orbit of `λ = 1 - a/(2^k-1)` under the tent map

Integer model: `uo i` is the numerator of `1 - x_i` on the denominator `M = 2^k - 1`, where
`x_i = T^i(λ)`.  It evolves by `u ↦ |2u - M|`, and `sg i = ±1` records the orientation, with
`uo i ≡ sg i * 2^i * a (mod M)`.
-/

@[expose] public section

namespace GrayNecklaces

open Tiozzo

/-- Hypotheses on a central window used by the covering lemma. -/
structure Central (a k : ℕ) : Prop where
  hk : 3 ≤ k
  ha : Odd a
  h6 : 6 * a < 2 ^ k
  lead : IsLeader (2 ^ k - 1) a
  prim : ∀ i, 0 < i → i < k → ¬ (2 ^ k - 1) ∣ (2 ^ i - 1) * a
  anti : ∀ i, ¬ (2 ^ k - 1) ∣ (2 ^ i + 1) * a
  maxi : ∀ u d, 2 ≤ d → d < k → Odd u → 3 * u < 2 ^ d → wT u d < wR a k → wR a k < wR u d → False

/-- Numerators of the orbit. -/
def uo (a k : ℕ) : ℕ → ℕ
  | 0 => a
  | i + 1 => if 2 ^ k - 1 ≤ 2 * uo a k i then 2 * uo a k i - (2 ^ k - 1)
             else (2 ^ k - 1) - 2 * uo a k i

/-- Orientation signs. -/
def sg (a k : ℕ) : ℕ → ℤ
  | 0 => 1
  | i + 1 => if 2 ^ k - 1 ≤ 2 * uo a k i then sg a k i else -sg a k i

section

variable {a k : ℕ}

lemma Central.M_odd (h : Central a k) : Odd (2 ^ k - 1) := by
  have : 2 ^ k = 2 * 2 ^ (k - 1) := by rw [← pow_succ']; congr 1; have := h.hk; omega
  have : 1 ≤ 2 ^ (k - 1) := Nat.one_le_two_pow
  exact ⟨2 ^ (k - 1) - 1, by omega⟩

lemma Central.M_ge (h : Central a k) : 7 ≤ 2 ^ k - 1 := by
  have : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h.hk
  omega

lemma Central.a_pos (h : Central a k) : 0 < a := h.ha.pos

lemma sg_cases (i : ℕ) : sg a k i = 1 ∨ sg a k i = -1 := by
  induction i with
  | zero => left; rfl
  | succ i ih =>
    simp only [sg]; split_ifs <;> rcases ih with h | h <;> simp [h]

lemma uo_pos_lt (h : Central a k) (i : ℕ) : 0 < uo a k i ∧ uo a k i < 2 ^ k - 1 ∧ Odd (uo a k i) := by
  have hM := h.M_odd
  have hMge := h.M_ge
  induction i with
  | zero =>
    simp only [uo]
    refine ⟨h.a_pos, by have := h.h6; omega, h.ha⟩
  | succ i ih =>
    obtain ⟨h1, h2, ⟨t, ht⟩⟩ := ih
    obtain ⟨m, hm⟩ := hM
    simp only [uo]
    split_ifs with hh
    · refine ⟨by omega, by omega, ⟨2 * t - m, by omega⟩⟩
    · exact ⟨by omega, by omega, ⟨m - 2 * t - 1, by omega⟩⟩

/-- `uo i ≡ sg i * 2^i * a (mod M)`. -/
lemma uo_cong (i : ℕ) :
    ((2 ^ k - 1 : ℕ) : ℤ) ∣ (uo a k i : ℤ) - sg a k i * 2 ^ i * a := by
  induction i with
  | zero => simp [uo, sg]
  | succ i ih =>
    obtain ⟨c, hc⟩ := ih
    simp only [uo, sg]
    split_ifs with hh
    · refine ⟨2 * c - 1, ?_⟩
      push_cast [hh]
      rw [pow_succ]; linear_combination 2 * hc
    · push Not at hh
      refine ⟨1 - 2 * c, ?_⟩
      push_cast [hh.le]
      rw [pow_succ]; linear_combination -2 * hc

lemma M_coprime_two_pow (h : Central a k) (i : ℕ) : IsCoprime ((2 ^ k - 1 : ℕ) : ℤ) (2 ^ i) := by
  apply IsCoprime.pow_right
  rw [Int.isCoprime_iff_gcd_eq_one]
  obtain ⟨m, hm⟩ := h.M_odd
  rw [hm]; push_cast
  rw [Int.gcd_comm]
  simp [Int.gcd, Int.natAbs_add_of_nonneg, Nat.gcd_comm]

/-- Two odd numbers in `(0, M)` congruent up to sign are equal, with the same sign. -/
lemma odd_cong_eq {M x y : ℕ} (hM : Odd M) (hx : 0 < x ∧ x < M ∧ Odd x) (hy : 0 < y ∧ y < M ∧ Odd y)
    (ε : ℤ) (hε : ε = 1 ∨ ε = -1) (hd : (M : ℤ) ∣ (x : ℤ) - ε * y) : x = y ∧ ε = 1 := by
  obtain ⟨c, hc⟩ := hd
  rcases hε with rfl | rfl
  · refine ⟨?_, rfl⟩
    have : c = 0 := by
      by_contra hc0
      rcases lt_or_gt_of_ne hc0 with h1 | h1 <;> nlinarith
    subst this; omega
  · exfalso
    have : c = 1 := by
      have h1 : (0 : ℤ) < M * c := by rw [← hc]; omega
      have h2 : (M : ℤ) * c < 2 * M := by rw [← hc]; omega
      have : 0 < c := by
        by_contra hh; push Not at hh; nlinarith
      have : c < 2 := by
        by_contra hh; push Not at hh; nlinarith
      omega
    subst this
    obtain ⟨p1, hp1⟩ := hx.2.2; obtain ⟨p2, hp2⟩ := hy.2.2; obtain ⟨p3, hp3⟩ := hM
    omega

lemma uo_period (h : Central a k) (i : ℕ) : uo a k (i + k) = uo a k i := by
  have h1 := uo_cong (a := a) (k := k) (i + k)
  have h2 := uo_cong (a := a) (k := k) i
  have h2k : ((2 ^ k - 1 : ℕ) : ℤ) ∣ (2 : ℤ) ^ k - 1 := by
    push_cast [Nat.one_le_two_pow]; exact dvd_rfl
  have key : ((2 ^ k - 1 : ℕ) : ℤ) ∣ (uo a k (i + k) : ℤ) - (sg a k (i + k) * sg a k i) * uo a k i := by
    have e : (uo a k (i + k) : ℤ) - (sg a k (i + k) * sg a k i) * uo a k i =
        ((uo a k (i + k) : ℤ) - sg a k (i + k) * 2 ^ (i + k) * a)
        + sg a k (i + k) * 2 ^ i * a * (2 ^ k - 1)
        - (sg a k (i + k) * sg a k i) * ((uo a k i : ℤ) - sg a k i * 2 ^ i * a)
        + sg a k (i + k) * (1 - sg a k i * sg a k i) * 2 ^ i * a := by ring
    have hsq : sg a k i * sg a k i = 1 := by rcases sg_cases (a := a) (k := k) i with hh | hh <;> simp [hh]
    rw [e, hsq, sub_self, mul_zero, zero_mul, zero_mul, add_zero]
    exact dvd_sub (dvd_add h1 (Dvd.dvd.mul_left h2k _)) (Dvd.dvd.mul_left h2 _)
  have hε : sg a k (i + k) * sg a k i = 1 ∨ sg a k (i + k) * sg a k i = -1 := by
    rcases sg_cases (a := a) (k := k) (i + k) with h3 | h3 <;>
      rcases sg_cases (a := a) (k := k) i with h4 | h4 <;> simp [h3, h4]
  exact (odd_cong_eq h.M_odd (uo_pos_lt h _) (uo_pos_lt h _) _ hε key).1

lemma uo_mod (h : Central a k) (i : ℕ) : uo a k i = uo a k (i % k) := by
  conv_lhs => rw [← Nat.mod_add_div i k]
  induction i / k with
  | zero => simp
  | succ n ih => rw [show i % k + k * (n + 1) = (i % k + k * n) + k by ring, uo_period h, ih]

/-- Primitive period: `M ∣ (2^d - 1) a` forces `k ∣ d`. -/
lemma Central.dvd_of_dvd (h : Central a k) {d : ℕ} (hd : (2 ^ k - 1) ∣ (2 ^ d - 1) * a) : k ∣ d := by
  have hk := h.hk
  set i := d % k
  have hsplit : 2 ^ d - 1 = 2 ^ i * ((2 ^ k) ^ (d / k) - 1) + (2 ^ i - 1) := by
    have h1 : 2 ^ d = 2 ^ i * (2 ^ k) ^ (d / k) := by
      rw [← pow_mul, ← pow_add, Nat.mod_add_div]
    have h2 : 1 ≤ (2 ^ k) ^ (d / k) := Nat.one_le_pow _ _ (by positivity)
    have h3 : 1 ≤ 2 ^ i := Nat.one_le_two_pow
    rw [h1, Nat.mul_sub, mul_one]
    have : 2 ^ i ≤ 2 ^ i * (2 ^ k) ^ (d / k) := Nat.le_mul_of_pos_right _ h2
    omega
  have hdvd1 : (2 ^ k - 1) ∣ (2 ^ k) ^ (d / k) - 1 := by
    simpa using Nat.sub_dvd_pow_sub_pow (2 ^ k) 1 (d / k)
  have hd2 : (2 ^ k - 1) ∣ (2 ^ i - 1) * a := by
    rw [hsplit, add_mul] at hd
    have : (2 ^ k - 1) ∣ 2 ^ i * ((2 ^ k) ^ (d / k) - 1) * a :=
      Dvd.dvd.mul_right (Dvd.dvd.mul_left hdvd1 _) _
    exact (Nat.dvd_add_right this).mp hd
  by_contra hkd
  have hi : 0 < i := Nat.pos_of_ne_zero (fun h0 => hkd (Nat.dvd_of_mod_eq_zero h0))
  exact h.prim i hi (Nat.mod_lt _ (by omega)) hd2

/-- Distinct phases give distinct orbit numerators. -/
lemma uo_inj (h : Central a k) {i i' : ℕ} (hi : i < k) (hi' : i' < k) (he : uo a k i = uo a k i') :
    i = i' := by
  wlog hle : i ≤ i' generalizing i i'
  · exact (this hi' hi he.symm (by omega)).symm
  set d := i' - i
  have h1 := uo_cong (a := a) (k := k) i
  have h2 := uo_cong (a := a) (k := k) i'
  rw [he] at h1
  -- `2^i (sg i * a - sg i' * 2^d * a) ≡ 0`
  have h3 : ((2 ^ k - 1 : ℕ) : ℤ) ∣ 2 ^ i * (sg a k i * a - sg a k i' * 2 ^ d * a) := by
    have : (2 : ℤ) ^ i * (sg a k i * a - sg a k i' * 2 ^ d * a) =
        ((uo a k i' : ℤ) - sg a k i' * 2 ^ i' * a) - ((uo a k i' : ℤ) - sg a k i * 2 ^ i * a) := by
      rw [show i' = i + d by omega, pow_add]; ring
    rw [this]; exact dvd_sub h2 h1
  have h4 := (M_coprime_two_pow h i).dvd_of_dvd_mul_left h3
  rcases sg_cases (a := a) (k := k) i with hs | hs <;>
    rcases sg_cases (a := a) (k := k) i' with hs' | hs'
  · rw [hs, hs'] at h4
    have : ((2 ^ k - 1 : ℕ) : ℤ) ∣ (((2 ^ d - 1) * a : ℕ) : ℤ) := by
      have e : (((2 ^ d - 1) * a : ℕ) : ℤ) = -(1 * a - 1 * 2 ^ d * a) := by
        push_cast [Nat.one_le_two_pow]; ring
      rw [e]; exact dvd_neg.mpr h4
    have := h.dvd_of_dvd (Int.natCast_dvd_natCast.mp this)
    rcases Nat.eq_zero_or_pos d with hd | hd
    · omega
    · have := Nat.le_of_dvd hd this; omega
  · rw [hs, hs'] at h4
    exfalso; apply h.anti d
    have : ((2 ^ k - 1 : ℕ) : ℤ) ∣ (((2 ^ d + 1) * a : ℕ) : ℤ) := by
      have e : (((2 ^ d + 1) * a : ℕ) : ℤ) = 1 * a - -1 * 2 ^ d * a := by push_cast; ring
      rw [e]; exact h4
    exact Int.natCast_dvd_natCast.mp this
  · rw [hs, hs'] at h4
    exfalso; apply h.anti d
    have : ((2 ^ k - 1 : ℕ) : ℤ) ∣ (((2 ^ d + 1) * a : ℕ) : ℤ) := by
      have e : (((2 ^ d + 1) * a : ℕ) : ℤ) = -(-1 * a - 1 * 2 ^ d * a) := by push_cast; ring
      rw [e]; exact dvd_neg.mpr h4
    exact Int.natCast_dvd_natCast.mp this
  · rw [hs, hs'] at h4
    have : ((2 ^ k - 1 : ℕ) : ℤ) ∣ (((2 ^ d - 1) * a : ℕ) : ℤ) := by
      have e : (((2 ^ d - 1) * a : ℕ) : ℤ) = -1 * a - -1 * 2 ^ d * a := by
        push_cast [Nat.one_le_two_pow]; ring
      rw [e]; exact h4
    have := h.dvd_of_dvd (Int.natCast_dvd_natCast.mp this)
    rcases Nat.eq_zero_or_pos d with hd | hd
    · omega
    · have := Nat.le_of_dvd hd this; omega

/-- The leader bounds: `a ≤ uo i ≤ M - a`. -/
lemma uo_bounds (h : Central a k) (i : ℕ) : a ≤ uo a k i ∧ uo a k i ≤ 2 ^ k - 1 - a := by
  have hc := uo_cong (a := a) (k := k) i
  have hMpos : 0 < 2 ^ k - 1 := by have := h.M_ge; omega
  have hL := h.lead.2 i
  set r := (2 ^ i * a) % (2 ^ k - 1)
  have hr : r < 2 ^ k - 1 := Nat.mod_lt _ hMpos
  have hsd : a ≤ r ∧ a ≤ 2 ^ k - 1 - r := by
    unfold sd at hL; exact ⟨le_trans hL (min_le_left _ _), le_trans hL (min_le_right _ _)⟩
  have hdm := Nat.div_add_mod (2 ^ i * a) (2 ^ k - 1)
  have hdmZ : ((2 ^ i * a : ℕ) : ℤ) = (2 ^ k - 1 : ℕ) * ((2 ^ i * a) / (2 ^ k - 1) : ℕ) + r := by
    exact_mod_cast hdm.symm
  obtain ⟨hu1, hu2, hu3⟩ := uo_pos_lt h i
  rcases sg_cases (a := a) (k := k) i with hs | hs
  · rw [hs] at hc
    have : ((2 ^ k - 1 : ℕ) : ℤ) ∣ (uo a k i : ℤ) - 1 * r := by
      have e : (uo a k i : ℤ) - 1 * r = ((uo a k i : ℤ) - 1 * 2 ^ i * a) +
          (2 ^ k - 1 : ℕ) * ((2 ^ i * a) / (2 ^ k - 1) : ℕ) := by
        push_cast at hdmZ ⊢; linarith
      rw [e]; exact dvd_add hc (dvd_mul_right _ _)
    obtain ⟨c, hc'⟩ := this
    have : c = 0 := by
      by_contra hc0
      rcases lt_or_gt_of_ne hc0 with h1 | h1 <;> nlinarith
    subst this
    have : uo a k i = r := by omega
    omega
  · rw [hs] at hc
    have : ((2 ^ k - 1 : ℕ) : ℤ) ∣ (uo a k i : ℤ) + r := by
      have e : (uo a k i : ℤ) + r = ((uo a k i : ℤ) - -1 * 2 ^ i * a) -
          (2 ^ k - 1 : ℕ) * ((2 ^ i * a) / (2 ^ k - 1) : ℕ) := by
        push_cast at hdmZ ⊢; linarith
      rw [e]; exact dvd_sub hc (dvd_mul_right _ _)
    obtain ⟨c, hc'⟩ := this
    have : c = 1 := by
      have h1 : (0 : ℤ) < (2 ^ k - 1 : ℕ) * c := by rw [← hc']; omega
      have h2 : ((2 ^ k - 1 : ℕ) : ℤ) * c < 2 * (2 ^ k - 1 : ℕ) := by rw [← hc']; omega
      have : 0 < c := by by_contra hh; push Not at hh; nlinarith
      have : c < 2 := by by_contra hh; push Not at hh; nlinarith
      omega
    subst this
    have : uo a k i = 2 ^ k - 1 - r := by omega
    omega

lemma uo_succ_le (h : Central a k) (i : ℕ) : uo a k (i + 1) ≤ 2 ^ k - 1 - 2 * a := by
  have := uo_bounds h i
  simp only [uo]; split_ifs <;> omega

/-! ### Real orbit -/

/-- `λ = 1 - a/(2^k-1)`. -/
noncomputable def lam (a k : ℕ) : ℝ := 1 - wR a k

/-- The orbit point `x_i = 1 - uo i / M`. -/
noncomputable def xo (a k : ℕ) (i : ℕ) : ℝ := 1 - (uo a k i : ℝ) / (2 ^ k - 1)

lemma Mreal_pos (h : Central a k) : (0 : ℝ) < 2 ^ k - 1 := by
  have : ((7 : ℕ) : ℝ) ≤ ((2 ^ k - 1 : ℕ) : ℝ) := by exact_mod_cast h.M_ge
  rw [two_pow_sub_one_cast] at this; push_cast at this; linarith

lemma xo_zero : xo a k 0 = lam a k := by simp [xo, lam, uo, wR]

lemma uo_cast_succ (_h : Central a k) (i : ℕ) :
    ((uo a k (i + 1) : ℕ) : ℝ) = |2 * (uo a k i : ℝ) - (2 ^ k - 1)| := by
  simp only [uo]
  split_ifs with hh
  · rw [Nat.cast_sub hh, abs_of_nonneg]
    · push_cast [Nat.one_le_two_pow]; ring
    · have : ((2 ^ k - 1 : ℕ) : ℝ) ≤ ((2 * uo a k i : ℕ) : ℝ) := by exact_mod_cast hh
      push_cast [Nat.one_le_two_pow] at this; linarith
  · push Not at hh
    rw [Nat.cast_sub hh.le, abs_of_nonpos]
    · push_cast [Nat.one_le_two_pow]; ring
    · have : ((2 * uo a k i : ℕ) : ℝ) < ((2 ^ k - 1 : ℕ) : ℝ) := by exact_mod_cast hh
      push_cast [Nat.one_le_two_pow] at this; linarith

lemma xo_succ (h : Central a k) (i : ℕ) : xo a k (i + 1) = tent (xo a k i) := by
  have hM := Mreal_pos h
  unfold xo tent
  rw [uo_cast_succ h]
  have hb := uo_pos_lt h i
  have hu0 : (0 : ℝ) ≤ uo a k i := by positivity
  have hu1 : (uo a k i : ℝ) ≤ 2 ^ k - 1 := by
    have : ((uo a k i : ℕ) : ℝ) ≤ ((2 ^ k - 1 : ℕ) : ℝ) := by exact_mod_cast hb.2.1.le
    rwa [two_pow_sub_one_cast] at this
  rcases le_total (2 * (uo a k i : ℝ)) (2 ^ k - 1) with hh | hh
  · rw [abs_of_nonpos (by linarith), min_eq_right]
    · field_simp; ring
    · rw [show 2 * (1 - (uo a k i : ℝ) / (2 ^ k - 1)) = 2 - 2 * (uo a k i / (2 ^ k - 1)) by ring]
      have : (uo a k i : ℝ) / (2 ^ k - 1) ≤ 1 / 2 := by
        rw [div_le_iff₀ hM]; linarith
      linarith
  · rw [abs_of_nonneg (by linarith), min_eq_left]
    · field_simp; ring
    · have : 1 / 2 ≤ (uo a k i : ℝ) / (2 ^ k - 1) := by
        rw [le_div_iff₀ hM]; linarith
      linarith

lemma xo_eq_iterate (h : Central a k) (i : ℕ) : xo a k i = tent^[i] (lam a k) := by
  induction i with
  | zero => simp [xo_zero]
  | succ i ih => rw [xo_succ h, ih, Function.iterate_succ_apply']

lemma xo_period (h : Central a k) (i : ℕ) : xo a k (i + k) = xo a k i := by
  simp only [xo, uo_period h]

lemma xo_mod (h : Central a k) (i : ℕ) : xo a k i = xo a k (i % k) := by
  simp only [xo, ← uo_mod h]

lemma xo_le_lam (h : Central a k) (i : ℕ) : xo a k i ≤ lam a k := by
  have hM := Mreal_pos h
  have := (uo_bounds h i).1
  unfold xo lam wR
  have : (a : ℝ) ≤ uo a k i := by exact_mod_cast this
  have : (a : ℝ) / (2 ^ k - 1) ≤ uo a k i / (2 ^ k - 1) := div_le_div_of_nonneg_right this hM.le
  linarith

lemma two_wR_le_xo (h : Central a k) (i : ℕ) (hi : 1 ≤ i) : 2 * wR a k ≤ xo a k i := by
  have hM := Mreal_pos h
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have h1 := uo_succ_le h j
  have hle : (uo a k (j + 1) : ℝ) ≤ 2 ^ k - 1 - 2 * a := by
    have h2a : 2 * a ≤ 2 ^ k - 1 := by have := h.h6; omega
    have h3 : ((uo a k (j + 1) : ℕ) : ℝ) ≤ ((2 ^ k - 1 - 2 * a : ℕ) : ℝ) := by exact_mod_cast h1
    rw [Nat.cast_sub h2a, two_pow_sub_one_cast] at h3; push_cast at h3; linarith
  unfold xo wR
  rw [le_sub_iff_add_le, ← le_sub_iff_add_le', div_le_iff₀ hM]
  field_simp
  linarith

lemma xo_one (h : Central a k) : xo a k 1 = 2 * wR a k := by
  have hM := Mreal_pos h
  rw [xo_succ h, xo_zero, lam, tent_eq]
  · rw [nint_eq_abs_sub (n := 1)]
    · push_cast
      have := wR_pos (b := a) (j := k) h.a_pos (by have := h.hk; omega)
      rw [abs_of_nonpos (by linarith)]; ring
    · have := wR_pos (b := a) (j := k) h.a_pos (by have := h.hk; omega)
      have := wR_le_third (a := a) (k := k) (by have := h.hk; omega) (by have := h.h6; omega)
      rw [abs_le]; push_cast; constructor <;> linarith
  · have := wR_le_third (a := a) (k := k) (by have := h.hk; omega) (by have := h.h6; omega)
    linarith
  · have := wR_pos (b := a) (j := k) h.a_pos (by have := h.hk; omega); linarith

lemma xo_ne_half (h : Central a k) (i : ℕ) : xo a k i ≠ 1 / 2 := by
  intro he
  have hM := Mreal_pos h
  unfold xo at he
  have : 2 * (uo a k i : ℝ) = 2 ^ k - 1 := by field_simp at he; linarith
  have : 2 * uo a k i = 2 ^ k - 1 := by
    have h' : ((2 * uo a k i : ℕ) : ℝ) = ((2 ^ k - 1 : ℕ) : ℝ) := by
      rw [two_pow_sub_one_cast]; push_cast; exact this
    exact_mod_cast h'
  obtain ⟨m, hm⟩ := h.M_odd; omega

lemma xo_inj (h : Central a k) {i i' : ℕ} (hi : i < k) (hi' : i' < k) (he : xo a k i = xo a k i') :
    i = i' := by
  apply uo_inj h hi hi'
  have hM := Mreal_pos h
  unfold xo at he
  have : (uo a k i : ℝ) = uo a k i' := by
    have := he; field_simp at this; linarith
  exact_mod_cast this

lemma xo_lt_lam (h : Central a k) {i : ℕ} (hi : 0 < i) (hik : i < k) : xo a k i < lam a k := by
  rcases eq_or_lt_of_le (xo_le_lam h i) with he | he
  · rw [← xo_zero] at he; have := xo_inj h hik (by have := h.hk; omega) he; omega
  · exact he

lemma lam_gt (h : Central a k) : 5 / 6 < lam a k := by
  unfold lam wR
  have hM := Mreal_pos h
  have h62 : 6 * a + 2 ≤ 2 ^ k := by
    have := h.h6; obtain ⟨m, hm⟩ := h.M_odd; omega
  have h62' : (6 * a : ℝ) + 2 ≤ 2 ^ k := by exact_mod_cast h62
  have h7 : (a : ℝ) / (2 ^ k - 1) < 1 / 6 := by rw [div_lt_iff₀ hM]; linarith
  linarith

/-- The side of `1/2` as a sign. -/
noncomputable def side (z : ℝ) : ℝ := if z ≤ 1 / 2 then 1 else -1

lemma side_xo (h : Central a k) (i : ℕ) :
    side (xo a k i) = if 2 ^ k - 1 ≤ 2 * uo a k i then 1 else -1 := by
  have hM := Mreal_pos h
  unfold side xo
  have hiff : (1 - (uo a k i : ℝ) / (2 ^ k - 1) ≤ 1 / 2) ↔ 2 ^ k - 1 ≤ 2 * uo a k i := by
    rw [sub_le_iff_le_add, ← sub_le_iff_le_add', le_div_iff₀ hM]
    constructor
    · intro hh
      have : ((2 ^ k - 1 : ℕ) : ℝ) ≤ ((2 * uo a k i : ℕ) : ℝ) := by
        rw [two_pow_sub_one_cast]; push_cast; linarith
      exact_mod_cast this
    · intro hh
      have : ((2 ^ k - 1 : ℕ) : ℝ) ≤ ((2 * uo a k i : ℕ) : ℝ) := by exact_mod_cast hh
      rw [two_pow_sub_one_cast] at this; push_cast at this; linarith
  by_cases hc : 2 ^ k - 1 ≤ 2 * uo a k i
  · rw [ite_eq_left (hiff.mpr hc), ite_eq_left hc]
  · rw [ite_eq_right (fun hh => hc (hiff.mp hh)), ite_eq_right hc]

/-- The orientation sign as a real number. -/
lemma sg_succ_real (h : Central a k) (i : ℕ) :
    (sg a k (i + 1) : ℝ) = sg a k i * side (xo a k i) := by
  rw [side_xo h]
  simp only [sg]; split_ifs <;> push_cast <;> ring

lemma sg_add_real (h : Central a k) (i d : ℕ) :
    (sg a k (i + d) : ℝ) = sg a k i * ∏ s ∈ Finset.range d, side (xo a k (i + s)) := by
  induction d with
  | zero => simp
  | succ d ih => rw [← add_assoc, sg_succ_real h, ih, Finset.prod_range_succ]; ring

end

end GrayNecklaces
