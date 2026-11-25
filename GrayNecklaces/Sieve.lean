module

public import GrayNecklaces.Windows

/-!
# The elementary sieve directions

* `enlDel_of_not_leader`: a non-leader for `2^p - 1` or `2^p + 1` is enlarged-deleted by a
  reduced dyadic window.
* `renorm`: a real point of `(wT, wR)` whose signed-doubling orbit has period `p` cannot stay
  above itself.
* `not_leader_of_del`: deletion by a primitive signed-leader window excludes both leaders.
-/

@[expose] public section

namespace GrayNecklaces

/-- Integer core of the deletion criterion for a non-leader. -/
lemma enl_core {D q s c ε : ℝ} (_hD : 1 ≤ D) (hc : 0 ≤ c) (hε : ε = 1 ∨ ε = -1)
    (h : |D * s - c * (D * q - ε)| < s) : |s - c * q| * (D - 1) < c * (q + 1) := by
  set δ := s - c * q with hδ
  have hs : s = c * q + δ := by rw [hδ]; ring
  have key : D * s - c * (D * q - ε) = D * δ + ε * c := by rw [hs]; ring
  rw [key, abs_lt] at h
  obtain ⟨h1, h2⟩ := h
  rcases le_or_gt 0 δ with hd | hd
  · rw [abs_of_nonneg hd]
    rcases hε with rfl | rfl <;> nlinarith
  · rw [abs_of_neg hd]
    rcases hε with rfl | rfl <;> nlinarith

/-- Reducing a dyadic only enlarges its deletion radius. -/
lemma enl_reduce {δ D' q c' E : ℝ} (_hD' : 1 ≤ D') (hq : 0 ≤ q) (hc' : 0 ≤ c') (hE : 1 ≤ E)
    (h : |δ| * (E * D' - 1) < E * c' * (q + 1)) : |δ| * (D' - 1) < c' * (E * q + 1) := by
  have hδ := abs_nonneg δ
  have h1 : E * (|δ| * (D' - 1)) ≤ |δ| * (E * D' - 1) := by nlinarith
  have h2 : |δ| * (D' - 1) < c' * (q + 1) := by
    have : E * (|δ| * (D' - 1)) < E * (c' * (q + 1)) := by nlinarith
    exact lt_of_mul_lt_mul_left this (by linarith)
  have : c' * (q + 1) ≤ c' * (E * q + 1) := mul_le_mul_of_nonneg_left (by nlinarith) hc'
  linarith

lemma three_not_dvd_two_pow (j : ℕ) : ¬ 3 ∣ 2 ^ j := by
  intro h
  have := (Nat.Prime.dvd_of_dvd_pow (by norm_num) h)
  omega

/-- A non-leader for `2^p - 1` or `2^p + 1` is enlarged-deleted by an admissible window. -/
theorem enlDel_of_not_leader {p s M : ℕ} (hp : 2 ≤ p) (hs : Odd s) (h3 : 3 * s < 2 ^ p)
    (hM : M = 2 ^ p - 1 ∨ M = 2 ^ p + 1)
    (hnl : ¬ IsLeader M s) : ∃ b j, IsWin p b j ∧ EnlDel p b j s := by
  have hspos : 0 < s := hs.pos
  have hN4 : 4 ≤ 2 ^ p := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hp
  obtain ⟨ε, hε, hMr⟩ : ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ (M : ℝ) = 2 ^ p - ε := by
    rcases hM with rfl | rfl
    · exact ⟨1, Or.inl rfl, by push_cast [show 1 ≤ 2 ^ p by omega]; ring⟩
    · exact ⟨-1, Or.inr rfl, by push_cast; ring⟩
  have hMpos : 0 < M := by omega
  have hsM : 3 * s ≤ M := by
    rcases hM with rfl | rfl
    · have : 3 * s ≠ 2 ^ p - 1 + 1 := by
        intro h; exact three_not_dvd_two_pow p ⟨s, by omega⟩
      omega
    · omega
  -- a failing shift
  unfold IsLeader at hnl
  push Not at hnl
  obtain ⟨j0, hj0⟩ := hnl hspos
  have hper : sd M (2 ^ j0 * s) = sd M (2 ^ (j0 % p) * s) := by
    rcases hM with rfl | rfl
    · exact sd_pow_mod_sub p j0 s
    · exact sd_pow_mod_add p j0 s
  rw [hper] at hj0
  set j := j0 % p
  have hjp : j < p := Nat.mod_lt _ (by omega)
  have hj1 : 1 ≤ j := by
    by_contra hj; have : j = 0 := by omega
    rw [this, pow_zero, one_mul, sd_eq_self (by omega)] at hj0; omega
  obtain ⟨c, hc⟩ := exists_near_of_sd_lt hMpos hj0
  -- real form of the nearness
  have hcR : |(2 : ℝ) ^ j * s - c * (2 ^ j * 2 ^ (p - j) - ε)| < s := by
    have : ((((2 ^ j * s : ℕ) : ℤ) - c * M).natAbs : ℝ) < s := by exact_mod_cast hc
    rw [Nat.cast_natAbs, Int.cast_abs] at this
    rw [← pow_split hjp.le, ← hMr]
    convert this using 2
    push_cast; ring
  have hD1 : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have hc0 : 1 ≤ c := by
    by_contra hc0; have : c = 0 := by omega
    subst this; simp at hcR
    have : (s : ℝ) ≤ 2 ^ j * s := le_mul_of_one_le_left (by positivity) hD1
    linarith
  -- `3c < 2^j`
  have h3c : 3 * c < 2 ^ j := by
    have hlt : (c : ℝ) * M < (2 ^ j + 1) * s := by
      have := (abs_lt.mp hcR).1
      rw [← pow_split hjp.le, ← hMr] at this; linarith
    have hsM' : (3 : ℝ) * s ≤ M := by exact_mod_cast hsM
    have hMr0 : (0 : ℝ) < M := by exact_mod_cast hMpos
    have : (3 * c : ℝ) < 2 ^ j + 1 := by
      by_contra hh; push Not at hh
      nlinarith
    have : 3 * c < 2 ^ j + 1 := by exact_mod_cast this
    have : 3 * c ≠ 2 ^ j := fun h => three_not_dvd_two_pow j ⟨c, h.symm⟩
    omega
  -- reduce `c`
  obtain ⟨e, c', hc'odd, hce⟩ := Nat.exists_eq_two_pow_mul_odd (show c ≠ 0 by omega)
  have hej : e < j := by
    have : 2 ^ e ≤ c := by rw [hce]; exact Nat.le_mul_of_pos_right _ hc'odd.pos
    have : 2 ^ e < 2 ^ j := by omega
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp this
  set j' := j - e
  have hjj : j = e + j' := by omega
  have h3c' : 3 * c' < 2 ^ j' := by
    have : 2 ^ e * (3 * c') < 2 ^ e * 2 ^ j' := by
      rw [← pow_add, ← hjj]; rw [hce] at h3c; linarith
    exact Nat.lt_of_mul_lt_mul_left this
  have hj'2 : 2 ≤ j' := by
    by_contra hh
    have : 2 ^ j' ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have := hc'odd.pos; omega
  refine ⟨c', j', ⟨hj'2, by omega, hc'odd, h3c'⟩, ?_⟩
  rw [enlDel_iff (by omega) (by omega)]
  refine ⟨hs, ?_⟩
  -- unreduced bound
  have hcore := enl_core (D := (2:ℝ) ^ j) (q := 2 ^ (p - j)) (s := s) (c := c) (ε := ε) hD1
    (by positivity) (by rcases hε with rfl | rfl <;> simp) hcR
  have hpj : p - j' = (p - j) + e := by omega
  have hcenter : (c : ℝ) * 2 ^ (p - j) = c' * 2 ^ (p - j') := by
    rw [hce, hpj, pow_add]; push_cast; ring
  rw [← hcenter]
  have hD'1 : (1 : ℝ) ≤ 2 ^ j' := one_le_pow₀ (by norm_num)
  have hred := enl_reduce (δ := (s : ℝ) - c * 2 ^ (p - j)) (D' := 2 ^ j') (q := 2 ^ (p - j))
    (c' := c') (E := 2 ^ e) hD'1 (by positivity) (by positivity) (one_le_pow₀ (by norm_num))
    (by
      have : (2:ℝ) ^ e * 2 ^ j' = 2 ^ j := by rw [← pow_add, ← hjj]
      rw [this]
      have : (c : ℝ) * (2 ^ (p - j) + 1) = 2 ^ e * c' * (2 ^ (p - j) + 1) := by
        rw [hce]; push_cast; ring
      linarith)
  unfold wR
  rw [hpj, pow_add]
  have hpos : (0 : ℝ) < 2 ^ j' - 1 := by
    have := two_pow_ge_four hj'2; linarith
  rw [div_mul_eq_mul_div, lt_div_iff₀ hpos]
  nlinarith [hred]

/-! ### Renormalization -/

lemma three_wR_le {a k : ℕ} (hk : 1 ≤ k) (h3 : 3 * a < 2 ^ k) : 3 * wR a k ≤ 1 := by
  unfold wR
  have h3' : 3 * a + 1 ≤ 2 ^ k := h3
  have : (3 : ℝ) * a + 1 ≤ 2 ^ k := by exact_mod_cast h3'
  have hpos : (0 : ℝ) < 2 ^ k - 1 := by
    have : (2:ℝ) ≤ 2 ^ k := by
      have := pow_le_pow_right₀ (show (1:ℝ) ≤ 2 by norm_num) hk; simpa using this
    linarith
  rw [mul_div_assoc', div_le_one hpos]; linarith

lemma nint_periodic {p : ℕ} {x : ℝ} (hper : ∀ j, nint (2 ^ (j + p) * x) = nint (2 ^ j * x))
    (j t : ℕ) : nint (2 ^ (j + p * t) * x) = nint (2 ^ j * x) := by
  induction t with
  | zero => simp
  | succ t ih => rw [show j + p * (t + 1) = (j + p * t) + p by ring, hper, ih]

/-- **Renormalization.**  A point of the open window `(wT a k, wR a k)` whose signed-doubling
orbit has period `p` (prime, `k < p`) and stays at or above the point cannot exist. -/
theorem renorm {p k a : ℕ} (hp : p.Prime) (hk : 1 ≤ k) (hkp : k < p) (ha : 0 < a)
    (h3 : 3 * a < 2 ^ k) {x : ℝ} (hT : wT a k < x) (hR : x < wR a k)
    (hper : ∀ j, nint (2 ^ (j + p) * x) = nint (2 ^ j * x))
    (hK : ∀ j, x ≤ nint (2 ^ j * x)) : False := by
  set B : ℝ := 2 ^ k
  set R := wR a k
  have hB : (2 : ℝ) ≤ B := by
    have := pow_le_pow_right₀ (show (1:ℝ) ≤ 2 by norm_num) hk; simpa [B] using this
  have hR3 : 3 * R ≤ 1 := three_wR_le hk h3
  have hReq : R = a / B + R / B := wR_eq hk
  have hTeq : wT a k = a / B - R / B := wT_eq hk
  have hRpos : 0 < R := wR_pos ha hk
  have hT0 : 0 ≤ wT a k := by
    unfold wT; apply mul_nonneg hRpos.le
    rw [sub_nonneg, div_le_one (by positivity)]; exact hB
  have hBpos : 0 < B := by positivity
  -- the orbit at multiples of `k` stays in the window
  have hstay : ∀ n : ℕ, wT a k < nint (2 ^ (n * k) * x) ∧ nint (2 ^ (n * k) * x) < R := by
    intro n
    induction n with
    | zero =>
      simp only [zero_mul, pow_zero, one_mul]
      rw [nint_of_mem (by linarith) (by linarith)]; exact ⟨hT, hR⟩
    | succ n ih =>
      set z := nint (2 ^ (n * k) * x)
      have hstep : nint (2 ^ ((n + 1) * k) * x) = nint (B * z) := by
        rw [show (n + 1) * k = k + n * k by ring, pow_add, mul_assoc,
          ← nint_pow_mul_nint k (2 ^ (n * k) * x)]
      rw [hstep]
      have hBz1 : B * z - a < R := by
        have : z < a / B + R / B := by rw [← hReq]; exact ih.2
        have := mul_lt_mul_of_pos_left this hBpos
        field_simp at this; linarith
      have hBz2 : -(R) < B * z - a := by
        have : a / B - R / B < z := by rw [← hTeq]; exact ih.1
        have := mul_lt_mul_of_pos_left this hBpos
        field_simp at this; linarith
      have habs : |B * z - (a : ℤ)| < R := by
        push_cast; rw [abs_lt]; exact ⟨hBz2, hBz1⟩
      rw [nint_eq_abs_sub (n := a) (by linarith)]
      refine ⟨?_, habs⟩
      have := hK ((n + 1) * k)
      rw [hstep, nint_eq_abs_sub (n := a) (by linarith)] at this
      linarith
  -- a multiple of `k` congruent to `1` modulo `p`
  have hcop : Nat.Coprime k p := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
    intro hd; have := Nat.le_of_dvd (by omega) hd; omega
  obtain ⟨n, -, hn⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
  have hnk : n * k = 1 + p * (k * n / p) := by
    have := Nat.mod_add_div (k * n) p
    rw [hn] at this; rw [mul_comm n k]; omega
  have h1 := hstay n
  rw [hnk, nint_periodic hper 1 _, pow_one] at h1
  -- contradiction from `x` and `nint (2x)` both in the window
  have hx2 : 2 * x ≤ 1 := by linarith
  rcases le_total (2 * x) (1 / 2) with hh | hh
  · rw [nint_eq_abs_sub (n := 0) (by simp [abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * x)]; linarith)]
      at h1
    simp only [Int.cast_zero, sub_zero] at h1
    rw [abs_of_nonneg (by linarith)] at h1
    have hu : (a : ℝ) = (a / B) * B := by field_simp
    have hv : R = (R / B) * B := by field_simp
    have h2 : 2 * (a / B - R / B) < a / B + R / B := by rw [← hTeq, ← hReq]; linarith
    have h4 : a / B < 3 * (R / B) := by linarith
    have h5 : (a / B) * B < 3 * (R / B) * B := mul_lt_mul_of_pos_right h4 hBpos
    have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
    nlinarith
  · rw [nint_eq_abs_sub (n := 1) (by rw [abs_le]; constructor <;> push_cast <;> linarith)] at h1
    push_cast at h1
    rw [abs_of_nonpos (by linarith)] at h1
    have : 1 < 3 * R := by linarith [h1.2]
    linarith

/-! ### Deletion by a primitive signed-leader window -/

lemma sd_le_of_good {p a k : ℕ} (h : GoodWin p a k) : a ≤ sd (2 ^ k - 1) (a * 2 ^ (p - k)) := by
  have := h.2.1.2 (p - k); rwa [mul_comm] at this

/-- `2^k - 1` does not divide `(2^(p-k) - 1) a` for a primitive window at prime length. -/
lemma not_dvd_of_good {p a k : ℕ} (hp : p.Prime) (h : GoodWin p a k) :
    ¬ (2 ^ k - 1) ∣ (2 ^ (p - k) - 1) * a := by
  obtain ⟨⟨hk2, hkp, _, _⟩, _, hprim⟩ := h
  intro hd
  set i := p - k
  have hsplit : 2 ^ i - 1 = 2 ^ (i % k) * ((2 ^ k) ^ (i / k) - 1) + (2 ^ (i % k) - 1) := by
    have h1 : 2 ^ i = 2 ^ (i % k) * (2 ^ k) ^ (i / k) := by
      rw [← pow_mul, ← pow_add, Nat.mod_add_div]
    have h2 : 1 ≤ (2 ^ k) ^ (i / k) := Nat.one_le_pow _ _ (by positivity)
    have h3 : 1 ≤ 2 ^ (i % k) := Nat.one_le_two_pow
    rw [h1, Nat.mul_sub, mul_one]
    have : 2 ^ (i % k) ≤ 2 ^ (i % k) * (2 ^ k) ^ (i / k) := Nat.le_mul_of_pos_right _ h2
    omega
  have hdvd1 : (2 ^ k - 1) ∣ (2 ^ k) ^ (i / k) - 1 := by
    simpa using Nat.sub_dvd_pow_sub_pow (2 ^ k) 1 (i / k)
  have hd2 : (2 ^ k - 1) ∣ (2 ^ (i % k) - 1) * a := by
    rw [hsplit, add_mul] at hd
    have : (2 ^ k - 1) ∣ 2 ^ (i % k) * ((2 ^ k) ^ (i / k) - 1) * a :=
      Dvd.dvd.mul_right (Dvd.dvd.mul_left hdvd1 _) _
    exact (Nat.dvd_add_right this).mp hd
  by_cases hm : i % k = 0
  · have hki : k ∣ p := by
      have : k ∣ i := Nat.dvd_of_mod_eq_zero hm
      have : k ∣ i + k := Nat.dvd_add this dvd_rfl
      rwa [show i + k = p by omega] at this
    rcases hp.eq_one_or_self_of_dvd k hki with h | h <;> omega
  · exact hprim (i % k) (Nat.pos_of_ne_zero hm) (Nat.mod_lt _ (by omega)) hd2

/-- Multiples of `M` avoid `[A - sd + 1, A + a)` when `a ≤ sd M A`. -/
lemma mult_le {M A a m : ℕ} (hM : 0 < M) (hsd : a ≤ sd M A) (hlt : m * M < A + a) :
    m * M ≤ A - A % M := by
  have h1 := Nat.div_add_mod' A M
  have h2 : a ≤ M - A % M := le_trans hsd (sd_le_sub M A)
  have h3 := Nat.mod_lt A hM
  have : m ≤ A / M := by
    by_contra hh; push Not at hh
    have : (A / M + 1) * M ≤ m * M := Nat.mul_le_mul_right _ hh
    rw [add_mul, one_mul] at this
    omega
  have := Nat.mul_le_mul_right M this
  omega

lemma abs_sub_natCast (s c : ℕ) : |(s : ℝ) - c| = (((s : ℤ) - c).natAbs : ℝ) := by
  rw [Nat.cast_natAbs, Int.cast_abs]; push_cast; ring_nf

lemma two_pow_sub_one_cast (k : ℕ) : (((2 ^ k - 1 : ℕ)) : ℝ) = 2 ^ k - 1 := by
  rw [Nat.cast_sub Nat.one_le_two_pow]; push_cast; ring

lemma good_center_even {p a k : ℕ} (h : GoodWin p a k) : Even (a * 2 ^ (p - k)) := by
  have : 1 ≤ p - k := by have := h.1.2.1; omega
  exact (Nat.even_pow.mpr ⟨even_two, by omega⟩).mul_left a

/-- The deletion test in natural numbers. -/
lemma del_iff_nat {p a k s : ℕ} (hk : 1 ≤ k) (hkp : k ≤ p) :
    Del p a k s ↔ Odd s ∧
      ((s : ℤ) - (a * 2 ^ (p - k) : ℕ)).natAbs * (2 ^ k - 1) < a * 2 ^ (p - k) := by
  rw [del_iff hk hkp]
  refine and_congr Iff.rfl ?_
  have hpos : (0 : ℝ) < ((2 ^ k - 1 : ℕ) : ℝ) := by
    rw [two_pow_sub_one_cast]
    have : (2:ℝ) ≤ 2 ^ k := by
      have := pow_le_pow_right₀ (show (1:ℝ) ≤ 2 by norm_num) hk; simpa using this
    linarith
  have hc : (((a * 2 ^ (p - k) : ℕ)) : ℝ) = a * 2 ^ (p - k) := by push_cast; ring
  have habs : |(s : ℝ) - a * 2 ^ (p - k)| =
      ((((s : ℤ) - (a * 2 ^ (p - k) : ℕ)).natAbs : ℕ) : ℝ) := by
    rw [← hc]; exact abs_sub_natCast s _
  have hw : wR a k * 2 ^ (p - k) = ((a * 2 ^ (p - k) : ℕ) : ℝ) / ((2 ^ k - 1 : ℕ) : ℝ) := by
    unfold wR; rw [hc, two_pow_sub_one_cast]; ring
  rw [habs, hw, lt_div_iff₀ hpos, ← Nat.cast_mul, Nat.cast_lt]

lemma enlDel_iff_nat {p a k s : ℕ} (hk : 1 ≤ k) (hkp : k ≤ p) :
    EnlDel p a k s ↔ Odd s ∧
      ((s : ℤ) - (a * 2 ^ (p - k) : ℕ)).natAbs * (2 ^ k - 1) < a * 2 ^ (p - k) + a := by
  rw [enlDel_iff hk hkp]
  refine and_congr Iff.rfl ?_
  have hpos : (0 : ℝ) < ((2 ^ k - 1 : ℕ) : ℝ) := by
    rw [two_pow_sub_one_cast]
    have : (2:ℝ) ≤ 2 ^ k := by
      have := pow_le_pow_right₀ (show (1:ℝ) ≤ 2 by norm_num) hk; simpa using this
    linarith
  have hc : (((a * 2 ^ (p - k) : ℕ)) : ℝ) = a * 2 ^ (p - k) := by push_cast; ring
  have habs : |(s : ℝ) - a * 2 ^ (p - k)| =
      ((((s : ℤ) - (a * 2 ^ (p - k) : ℕ)).natAbs : ℕ) : ℝ) := by
    rw [← hc]; exact abs_sub_natCast s _
  have hw : wR a k * (2 ^ (p - k) + 1) =
      ((a * 2 ^ (p - k) + a : ℕ) : ℝ) / ((2 ^ k - 1 : ℕ) : ℝ) := by
    unfold wR; rw [two_pow_sub_one_cast]; push_cast; ring
  rw [habs, hw, lt_div_iff₀ hpos, ← Nat.cast_mul, Nat.cast_lt]

lemma two_le_two_pow {k : ℕ} (hk : 1 ≤ k) : 2 ≤ 2 ^ k :=
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk

/-- For a primitive signed-leader window both radii delete the same odd ranks. -/
theorem del_of_enlDel_good {p a k s : ℕ} (h : GoodWin p a k) (he : EnlDel p a k s) :
    Del p a k s := by
  have hk : 1 ≤ k := by have := h.1.1; omega
  have hkp : k ≤ p := h.1.2.1.le
  rw [enlDel_iff_nat hk hkp] at he
  rw [del_iff_nat hk hkp]
  refine ⟨he.1, ?_⟩
  have hM : 0 < 2 ^ k - 1 := by have := two_le_two_pow hk; omega
  have hsd := sd_le_of_good h
  have hm := mult_le hM hsd he.2
  have ha := h.1.2.2.1.pos
  have hρ : a ≤ a * 2 ^ (p - k) % (2 ^ k - 1) := le_trans hsd (sd_le_mod _ _)
  have hml := Nat.mod_le (a * 2 ^ (p - k)) (2 ^ k - 1)
  generalize a * 2 ^ (p - k) % (2 ^ k - 1) = ρ at hρ hm hml
  generalize ((s : ℤ) - (a * 2 ^ (p - k) : ℕ)).natAbs * (2 ^ k - 1) = X at hm ⊢
  omega

/-- Deletion by a primitive signed-leader window rules out both kinds of leader. -/
theorem not_leader_of_del {p a k s : ℕ} (hp : p.Prime) (h : GoodWin p a k) (hd : Del p a k s) :
    ¬ IsLeader (2 ^ p - 1) s ∧ ¬ IsLeader (2 ^ p + 1) s := by
  have hgood := h
  obtain ⟨⟨hk2, hkp, haodd, ha3⟩, hlead, hprim⟩ := h
  have hk : 1 ≤ k := by omega
  have hdel := (del_iff_nat hk hkp.le).mp hd
  have hs := hdel.1
  have hsd := sd_le_of_good hgood
  have hnd := not_dvd_of_good hp hgood
  have hev := good_center_even hgood
  have hN : 2 ^ p = 2 ^ k * 2 ^ (p - k) := by rw [← pow_add]; congr 1; omega
  have hB4 : 4 ≤ 2 ^ k := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
  have hq2 : 2 ≤ 2 ^ (p - k) := two_le_two_pow (by omega)
  have hN2 : 2 ≤ 2 ^ p := two_le_two_pow (by omega)
  have hapos := haodd.pos
  have hM : 0 < 2 ^ k - 1 := by omega
  have hρ : a ≤ a * 2 ^ (p - k) % (2 ^ k - 1) := le_trans hsd (sd_le_mod _ _)
  have hml := Nat.mod_le (a * 2 ^ (p - k)) (2 ^ k - 1)
  -- a real-number view of the window, needed for renormalization
  have hwR : wR a k = a / ((2:ℝ) ^ k - 1) := rfl
  have hwT : wT a k = a * (2 ^ k - 2) / (2 ^ k * ((2:ℝ) ^ k - 1)) := by
    unfold wT wR; have : (2:ℝ) ^ k - 1 ≠ 0 := by
      have : (4:ℝ) ≤ 2 ^ k := two_pow_ge_four hk2
      linarith
    field_simp
  have hNr : (2 : ℝ) ^ p = 2 ^ k * 2 ^ (p - k) := pow_split hkp.le
  set q := 2 ^ (p - k) with hq
  set B := 2 ^ k with hB
  have hne : s ≠ a * q := by
    intro he; rw [← he] at hev
    exact (Nat.not_even_iff_odd.mpr hs) hev
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- left half: renormalization
    have hδnat : ((s : ℤ) - (a * q : ℕ)).natAbs = a * q - s := by omega
    have hdel2 := hdel.2
    rw [hδnat] at hdel2
    have hm := mult_le hM hsd (by omega : (a * q - s) * (B - 1) < a * q + a)
    have hδle : (a * q - s) * (B - 1) + a ≤ a * q := by
      generalize a * q % (B - 1) = ρ at hρ hm hml; omega
    -- real bounds
    have hBr : (4 : ℝ) ≤ B := by exact_mod_cast hB4
    have hqr : (2 : ℝ) ≤ q := by exact_mod_cast hq2
    have har : (1 : ℝ) ≤ a := by exact_mod_cast hapos
    obtain ⟨δ, hδ⟩ : ∃ δ, s + δ = a * q := ⟨a * q - s, by omega⟩
    have hδle' : δ * (B - 1) + a ≤ a * q := by
      rw [show δ = a * q - s by omega]; exact hδle
    have hsr : (s : ℝ) = a * q - δ := by
      have : (s : ℝ) + δ = a * q := by exact_mod_cast hδ
      linarith
    have hδ1 : (δ : ℝ) * (B - 1) + a ≤ a * q := by
      have : ((δ * (B - 1) + a : ℕ) : ℝ) ≤ ((a * q : ℕ) : ℝ) := by exact_mod_cast hδle'
      push_cast [show 1 ≤ B by omega] at this; linarith
    have hδ0 : (0 : ℝ) ≤ δ := by positivity
    have hBm : (0 : ℝ) < (B : ℝ) - 1 := by linarith
    have hBc : ((2:ℝ) ^ k) = B := by rw [hB]; push_cast; ring
    have hqc : ((2:ℝ) ^ (p - k)) = q := by rw [hq]; push_cast; ring
    rw [hBc] at hwR hwT hNr
    rw [hqc] at hNr
    constructor
    · intro hL
      have hL' := (isLeader_iff_real _ s (by omega)).mp hL
      have hMr : ((2 ^ p - 1 : ℕ) : ℝ) = B * q - 1 := by
        rw [two_pow_sub_one_cast, hNr]
      apply renorm hp hk hkp hapos ha3 (x := s / ((2 ^ p - 1 : ℕ) : ℝ))
      · rw [hwT, hMr, div_lt_div_iff₀ (by positivity) (by nlinarith), hsr]
        nlinarith
      · rw [hwR, hMr, div_lt_div_iff₀ (by nlinarith) hBm, hsr]
        nlinarith
      · intro j
        rw [← mul_div_assoc, ← mul_div_assoc]
        have e1 := sd_div_eq_nint (2 ^ p - 1) (2 ^ (j + p) * s) (by omega)
        have e2 := sd_div_eq_nint (2 ^ p - 1) (2 ^ j * s) (by omega)
        push_cast at e1 e2
        rw [← e1, ← e2, sd_pow_period_sub]
      · exact hL'.2
    · intro hL
      have hL' := (isLeader_iff_real _ s (by omega)).mp hL
      have hMr : ((2 ^ p + 1 : ℕ) : ℝ) = B * q + 1 := by push_cast; rw [hNr]
      apply renorm hp hk hkp hapos ha3 (x := s / ((2 ^ p + 1 : ℕ) : ℝ))
      · rw [hwT, hMr, div_lt_div_iff₀ (by positivity) (by positivity), hsr]
        nlinarith
      · rw [hwR, hMr, div_lt_div_iff₀ (by positivity) hBm, hsr]
        nlinarith
      · intro j
        rw [← mul_div_assoc, ← mul_div_assoc]
        have e1 := sd_div_eq_nint (2 ^ p + 1) (2 ^ (j + p) * s) (by omega)
        have e2 := sd_div_eq_nint (2 ^ p + 1) (2 ^ j * s) (by omega)
        push_cast at e1 e2 ⊢
        rw [← e1, ← e2]; exact_mod_cast congrArg (fun t : ℕ => (t : ℝ) / (2 ^ p + 1))
          (sd_pow_period_add p j s)
      · exact hL'.2
  · -- right half: a direct hole
    have hδnat : ((s : ℤ) - (a * q : ℕ)).natAbs = s - a * q := by omega
    have hdel2 := hdel.2
    rw [hδnat] at hdel2
    have hm := mult_le hM hsd (by omega : (s - a * q) * (B - 1) < a * q + a)
    have hstrict : (s - a * q) * (B - 1) + a < a * q := by
      by_contra hh
      have hρa : a * q % (B - 1) = a := by
        generalize a * q % (B - 1) = ρ at hρ hm hml ⊢; omega
      apply hnd
      have : (q - 1) * a = (s - a * q) * (B - 1) := by
        rw [Nat.sub_mul, one_mul, mul_comm q a]
        generalize a * q % (B - 1) = ρ at hρ hm hml hρa; omega
      rw [this]; exact dvd_mul_left _ _
    obtain ⟨δ, hδ⟩ : ∃ δ, s = a * q + δ := ⟨s - a * q, by omega⟩
    rw [hδ, Nat.add_sub_cancel_left] at hstrict
    have hBd : B * δ = δ * (B - 1) + δ := by
      rw [Nat.mul_sub, mul_one, mul_comm]
      have : δ ≤ δ * B := Nat.le_mul_of_pos_right _ (by omega)
      omega
    have hq1 : a ≤ a * q := Nat.le_mul_of_pos_right _ (by omega)
    constructor
    · intro hL
      have h1 : s ≤ sd (2 ^ p - 1) (B * s) := hL.2 k
      have h2 := sd_le_natAbs (2 ^ p - 1) (B * s) (a : ℤ) (by omega)
      have hBq : 1 ≤ B * q := by have := Nat.mul_le_mul hB4 hq2; omega
      have h3 : ((B * s : ℕ) : ℤ) - a * ((2 ^ p - 1 : ℕ) : ℤ) = ((B * δ : ℕ) : ℤ) + a := by
        have e : ((2 ^ p - 1 : ℕ) : ℤ) = (B : ℤ) * q - 1 := by
          rw [hN, Nat.cast_sub hBq]; push_cast; ring
        rw [e, hδ]; push_cast; ring
      rw [h3] at h2
      generalize δ * (B - 1) = Y at hBd hstrict
      generalize B * δ = X at hBd h2
      omega
    · intro hL
      have h1 : s ≤ sd (2 ^ p + 1) (B * s) := hL.2 k
      have h2 := sd_le_natAbs (2 ^ p + 1) (B * s) (a : ℤ) (by omega)
      have h3 : ((B * s : ℕ) : ℤ) - a * ((2 ^ p + 1 : ℕ) : ℤ) = ((B * δ : ℕ) : ℤ) - a := by
        have e : ((2 ^ p + 1 : ℕ) : ℤ) = (B : ℤ) * q + 1 := by
          rw [hN]; push_cast; ring
        rw [e, hδ]; push_cast; ring
      rw [h3] at h2
      generalize δ * (B - 1) = Y at hBd hstrict
      generalize B * δ = X at hBd h2
      generalize a * q = A at hstrict hq1 hδ
      omega

end GrayNecklaces
