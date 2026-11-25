module

public import Mathlib

/-!
# Signed distances and signed-doubling leaders

`sd M x` is the distance from `x` to the nearest multiple of `M`, for natural numbers.
`IsLeader M s` says that `s` is positive and is the least signed distance in its orbit
under doubling modulo `M`.  On the real side `nint y` is the distance from `y` to the
nearest integer.
-/

@[expose] public section

namespace GrayNecklaces

/-- Distance from `x` to the nearest multiple of `M`. -/
def sd (M x : ℕ) : ℕ := min (x % M) (M - x % M)

/-- A positive signed-doubling leader modulo `M`. -/
def IsLeader (M s : ℕ) : Prop := 0 < s ∧ ∀ j : ℕ, s ≤ sd M (2 ^ j * s)

lemma sd_le_mod (M x : ℕ) : sd M x ≤ x % M := min_le_left _ _

lemma sd_le_sub (M x : ℕ) : sd M x ≤ M - x % M := min_le_right _ _

lemma sd_mod (M x : ℕ) : sd M (x % M) = sd M x := by
  simp [sd]

lemma sd_add_mul (M x c : ℕ) : sd M (x + M * c) = sd M x := by
  rw [← sd_mod, Nat.add_mul_mod_self_left, sd_mod]

lemma sd_of_modEq {M x y : ℕ} (h : x % M = y % M) : sd M x = sd M y := by
  rw [← sd_mod, h, sd_mod]

/-- If `x ≡ -y (mod M)` then `x` and `y` have the same signed distance. -/
lemma sd_of_add_mod {M x y : ℕ} (hM : 0 < M) (h : (x + y) % M = 0) : sd M x = sd M y := by
  have hx := Nat.mod_lt x hM
  have hy := Nat.mod_lt y hM
  have key : (x % M + y % M) % M = 0 := by rw [← Nat.add_mod]; exact h
  rcases Nat.eq_zero_or_pos (x % M) with h0 | h0
  · have : y % M = 0 := by
      rw [h0, zero_add, Nat.mod_mod] at key; exact key
    simp [sd, h0, this]
  · have hsum : x % M + y % M = M := by
      have h1 : x % M + y % M < 2 * M := by omega
      have h2 : 0 < x % M + y % M := by omega
      obtain ⟨t, ht⟩ := Nat.dvd_of_mod_eq_zero key
      have : t = 1 := by
        rcases t with _ | _ | t
        · omega
        · rfl
        · nlinarith
      subst this; omega
    unfold sd
    rw [show M - x % M = y % M by omega, show M - y % M = x % M by omega, min_comm]

lemma sd_le_half (M x : ℕ) : 2 * sd M x ≤ M := by
  unfold sd
  rcases le_total (x % M) (M - x % M) with h | h
  · rw [min_eq_left h]; omega
  · rw [min_eq_right h]; omega

lemma sd_eq_self {M x : ℕ} (hx : 2 * x ≤ M) : sd M x = x := by
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM; simp [sd]; omega
  have : x < M ∨ x = M := by omega
  rcases this with h | h
  · unfold sd; rw [Nat.mod_eq_of_lt h]; omega
  · subst h; have : x = 0 := by omega
    subst this; simp [sd]

lemma sd_zero (M : ℕ) : sd M 0 = 0 := by simp [sd]

lemma sd_mul_sd (M c x : ℕ) (hM : 0 < M) : sd M (c * sd M x) = sd M (c * x) := by
  unfold sd at *
  rcases le_total (x % M) (M - x % M) with h | h
  · rw [min_eq_left h]
    apply sd_of_modEq
    rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
  · rw [min_eq_right h]
    apply sd_of_add_mod hM
    have hx := Nat.mod_lt x hM
    have : c * (M - x % M) + c * x = M * (c * (x / M + 1)) := by
      have := Nat.div_add_mod x M
      rw [← Nat.mul_add]
      have e : M - x % M + x = M * (x / M + 1) := by
        nth_rewrite 2 [← this]; rw [Nat.mul_add, Nat.mul_one]; omega
      rw [e]; ring
    rw [this]; simp

lemma sd_pow_mul_sd (M j x : ℕ) (hM : 0 < M) :
    sd M (2 ^ j * sd M x) = sd M (2 ^ j * x) := sd_mul_sd M _ x hM

/-- The signed distance is at most the distance to any multiple of `M`. -/
lemma sd_le_natAbs (M x : ℕ) (c : ℤ) (hM : 0 < M) :
    sd M x ≤ ((x : ℤ) - c * M).natAbs := by
  have h1 := Nat.div_add_mod x M
  have hr := Nat.mod_lt x hM
  set r := x % M
  generalize hQ : x / M = Q at h1
  set t : ℤ := (Q : ℤ) - c
  have hx : ((x : ℤ) - c * M) = r + M * t := by
    have : (x : ℤ) = M * Q + r := by exact_mod_cast h1.symm
    rw [this]; ring
  rw [hx]
  rcases le_or_gt 0 t with ht | ht
  · have : (sd M x : ℤ) ≤ r := by exact_mod_cast sd_le_mod M x
    have h2 : (0 : ℤ) ≤ M * t := by positivity
    omega
  · have : (sd M x : ℤ) ≤ M - r := by
      have := sd_le_sub M x; omega
    have h2 : (M : ℤ) * t ≤ -M := by nlinarith
    omega

/-- A small signed distance is witnessed by a nearby multiple of `M`. -/
lemma exists_near_of_sd_lt {M x s : ℕ} (hM : 0 < M) (h : sd M x < s) :
    ∃ c : ℕ, ((x : ℤ) - c * M).natAbs < s := by
  have h1 := Nat.div_add_mod x M
  have hr := Nat.mod_lt x hM
  unfold sd at h
  generalize hQ : x / M = Q at h1
  generalize hR : x % M = r at h1 h hr
  have hx : (x : ℤ) = M * Q + r := by exact_mod_cast h1.symm
  rcases le_total r (M - r) with hle | hle
  · refine ⟨Q, ?_⟩
    rw [min_eq_left hle] at h
    have : (x : ℤ) - (Q : ℕ) * M = (r : ℕ) := by rw [hx]; ring
    rw [this, Int.natAbs_natCast]; exact h
  · refine ⟨Q + 1, ?_⟩
    rw [min_eq_right hle] at h
    have : (x : ℤ) - ((Q + 1 : ℕ) : ℤ) * M = -((M - r : ℕ) : ℤ) := by
      rw [hx]; push_cast [show r ≤ M by omega]; ring
    rw [this, Int.natAbs_neg, Int.natAbs_natCast]; exact h

/-! ### Periodicity of signed doubling modulo `2^p ∓ 1` -/

lemma sd_pow_period_sub (p j s : ℕ) :
    sd (2 ^ p - 1) (2 ^ (j + p) * s) = sd (2 ^ p - 1) (2 ^ j * s) := by
  apply sd_of_modEq
  have h1 : 1 ≤ 2 ^ p := Nat.one_le_two_pow
  have : 2 ^ (j + p) * s = 2 ^ j * s + (2 ^ p - 1) * (2 ^ j * s) := by
    rw [pow_add]
    have : 2 ^ p = (2 ^ p - 1) + 1 := by omega
    conv_lhs => rw [this]
    ring
  rw [this, Nat.add_mul_mod_self_left]

lemma sd_pow_period_add (p j s : ℕ) :
    sd (2 ^ p + 1) (2 ^ (j + p) * s) = sd (2 ^ p + 1) (2 ^ j * s) := by
  apply sd_of_add_mod (by positivity)
  have : 2 ^ (j + p) * s + 2 ^ j * s = (2 ^ p + 1) * (2 ^ j * s) := by
    rw [pow_add]; ring
  rw [this]; simp

lemma sd_pow_mod_sub (p j s : ℕ) :
    sd (2 ^ p - 1) (2 ^ j * s) = sd (2 ^ p - 1) (2 ^ (j % p) * s) := by
  conv_lhs => rw [← Nat.mod_add_div j p]
  induction j / p with
  | zero => simp
  | succ n ih =>
    rw [show j % p + p * (n + 1) = (j % p + p * n) + p by ring, sd_pow_period_sub, ih]

lemma sd_pow_mod_add (p j s : ℕ) :
    sd (2 ^ p + 1) (2 ^ j * s) = sd (2 ^ p + 1) (2 ^ (j % p) * s) := by
  conv_lhs => rw [← Nat.mod_add_div j p]
  induction j / p with
  | zero => simp
  | succ n ih =>
    rw [show j % p + p * (n + 1) = (j % p + p * n) + p by ring, sd_pow_period_add, ih]

/-- A leader modulo an odd `M` is odd. -/
lemma IsLeader.odd {M s : ℕ} (hM : Odd M) (h : IsLeader M s) (hs2 : 2 * s ≤ M) : Odd s := by
  by_contra hev
  rw [Nat.not_odd_iff_even] at hev
  obtain ⟨t, rfl⟩ := hev
  -- `M` is odd, so `2` is invertible modulo `M` and `t` lies in the orbit of `t + t`.
  obtain ⟨m, hm⟩ := hM
  -- `2 * (m+1) ≡ 1 (mod M)`, so `(m+1) * (t+t) ≡ t`.
  have hpos := h.1
  have hsd := h.2
  have hMpos : 0 < M := by omega
  -- the orbit of `t+t` under doubling contains `t`: `2^φ(M) ≡ 1`.
  have hcop : Nat.Coprime 2 M := by
    rw [Nat.coprime_comm, Nat.Coprime, hm]; simp [Nat.gcd_comm]
  have htot := Nat.ModEq.pow_totient hcop
  -- `2^(φ M - 1) * (t + t) = 2^φ(M) * t ≡ t`
  have hφ : 0 < Nat.totient M := Nat.totient_pos.mpr hMpos
  have key := hsd (Nat.totient M - 1)
  have heq : 2 ^ (Nat.totient M - 1) * (t + t) = 2 ^ Nat.totient M * t := by
    rw [show t + t = 2 * t by ring, ← mul_assoc, ← pow_succ, Nat.sub_add_cancel hφ]
  rw [heq] at key
  have : sd M (2 ^ Nat.totient M * t) = sd M t := by
    apply sd_of_modEq
    have := htot.mul_right t
    simpa [Nat.ModEq, one_mul] using this
  rw [this] at key
  have : sd M t ≤ t := by
    have := sd_le_mod M t; have := Nat.mod_le t M; omega
  omega

/-! ### Distance to the nearest integer -/

/-- Distance from a real number to the nearest integer. -/
noncomputable def nint (y : ℝ) : ℝ := min (Int.fract y) (1 - Int.fract y)

lemma nint_nonneg (y : ℝ) : 0 ≤ nint y := by
  unfold nint; have := Int.fract_nonneg y; have := Int.fract_lt_one y
  exact le_min (by linarith) (by linarith)

lemma nint_le_half (y : ℝ) : nint y ≤ 1 / 2 := by
  unfold nint
  rcases le_total (Int.fract y) (1 / 2) with h | h
  · exact le_trans (min_le_left _ _) h
  · exact le_trans (min_le_right _ _) (by linarith)

lemma nint_add_int (y : ℝ) (n : ℤ) : nint (y + n) = nint y := by
  simp [nint, Int.fract_add_intCast]

lemma nint_int_add (y : ℝ) (n : ℤ) : nint (n + y) = nint y := by
  rw [add_comm]; exact nint_add_int y n

lemma nint_sub_int (y : ℝ) (n : ℤ) : nint (y - n) = nint y := by
  rw [sub_eq_add_neg, ← Int.cast_neg, nint_add_int]

lemma nint_neg (y : ℝ) : nint (-y) = nint y := by
  unfold nint
  rcases eq_or_ne (Int.fract y) 0 with h | h
  · rw [Int.fract_neg_eq_zero.mpr h, h]
  · rw [Int.fract_neg h]; rw [min_comm]; ring_nf

/-- `nint y` is at most the distance from `y` to any integer. -/
lemma nint_le_abs_sub (y : ℝ) (n : ℤ) : nint y ≤ |y - n| := by
  have hy : y = ⌊y⌋ + Int.fract y := (Int.floor_add_fract y).symm
  set f := Int.fract y
  have hf0 := Int.fract_nonneg y
  have hf1 := Int.fract_lt_one y
  set t : ℤ := ⌊y⌋ - n
  have : y - n = t + f := by simp only [t]; push_cast; linarith
  rw [this]
  unfold nint
  rcases le_or_gt 0 t with ht | ht
  · have : (0 : ℝ) ≤ t := by exact_mod_cast ht
    rw [abs_of_nonneg (by linarith)]
    exact le_trans (min_le_left _ _) (by linarith)
  · have : (t : ℝ) ≤ -1 := by exact_mod_cast (show t ≤ -1 by omega)
    rw [abs_of_neg (by linarith)]
    exact le_trans (min_le_right _ _) (by linarith)

/-- If `y` is within `1/2` of an integer `n`, that distance is `nint y`. -/
lemma nint_eq_abs_sub {y : ℝ} {n : ℤ} (h : |y - n| ≤ 1 / 2) : nint y = |y - n| := by
  apply le_antisymm (nint_le_abs_sub y n)
  have hy : y = ⌊y⌋ + Int.fract y := (Int.floor_add_fract y).symm
  have hf0 := Int.fract_nonneg y
  have hf1 := Int.fract_lt_one y
  set f := Int.fract y
  set fl := ⌊y⌋
  rw [abs_le] at h
  unfold nint
  have hn : n = fl ∨ n = fl + 1 := by
    have a1 : n < fl + 2 := by
      have : (n : ℝ) < fl + 2 := by linarith [h.1]
      exact_mod_cast this
    have a2 : fl - 1 < n := by
      have : (fl : ℝ) - 1 < n := by linarith [h.2]
      exact_mod_cast this
    omega
  rcases hn with rfl | rfl
  · have e : y - (fl : ℝ) = f := by linarith
    rw [e] at h ⊢
    rw [abs_of_nonneg hf0]
    exact le_min le_rfl (by linarith [h.2])
  · have e : y - ((fl + 1 : ℤ) : ℝ) = f - 1 := by push_cast; linarith
    rw [e] at h ⊢
    rw [abs_of_neg (by linarith)]
    exact le_min (by linarith [h.1]) (by linarith)

lemma nint_of_mem {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1 / 2) : nint y = y := by
  have := nint_eq_abs_sub (y := y) (n := 0) (by simp [abs_of_nonneg h0]; linarith)
  simpa [abs_of_nonneg h0] using this

lemma nint_zmul_nint (m : ℤ) (y : ℝ) : nint (m * nint y) = nint (m * y) := by
  -- `nint y = |y - n|` for `n = round y`
  have h := nint_eq_abs_sub (y := y) (n := round y) (abs_sub_round y)
  rw [h]
  rcases le_total 0 (y - round y) with hs | hs
  · rw [abs_of_nonneg hs, mul_sub, ← Int.cast_mul, nint_sub_int]
  · rw [abs_of_nonpos hs, show (m : ℝ) * -(y - round y) = -(m * y - ((m * round y : ℤ) : ℝ)) by
      push_cast; ring, nint_neg, nint_sub_int]

lemma nint_pow_mul_nint (j : ℕ) (y : ℝ) : nint (2 ^ j * nint y) = nint (2 ^ j * y) := by
  have := nint_zmul_nint (2 ^ j) y
  push_cast at this; exact this

/-- `sd` in terms of `nint`. -/
lemma sd_div_eq_nint (M x : ℕ) (hM : 0 < M) : (sd M x : ℝ) / M = nint ((x : ℝ) / M) := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hfr : Int.fract ((x : ℝ) / M) = ((x % M : ℕ) : ℝ) / M := by
    rw [Int.fract_eq_iff]
    refine ⟨by positivity, ?_, ?_⟩
    · rw [div_lt_one hMr]; exact_mod_cast Nat.mod_lt x hM
    · have h1 := Nat.div_add_mod x M
      generalize x / M = Q at h1
      refine ⟨Q, ?_⟩
      have : (x : ℝ) = M * Q + (x % M : ℕ) := by exact_mod_cast h1.symm
      rw [this]; field_simp; push_cast; ring
  unfold nint sd
  rw [hfr]
  have hle : x % M ≤ M := (Nat.mod_lt x hM).le
  rcases le_total (x % M) (M - x % M) with h | h
  · rw [min_eq_left h, min_eq_left]
    have : ((x % M : ℕ) : ℝ) ≤ ((M - x % M : ℕ) : ℝ) := by exact_mod_cast h
    push_cast [hle] at this
    rw [div_le_iff₀ hMr]; field_simp; linarith
  · rw [min_eq_right h, min_eq_right]
    · push_cast [hle]; field_simp
    · have : ((M - x % M : ℕ) : ℝ) ≤ ((x % M : ℕ) : ℝ) := by exact_mod_cast h
      push_cast [hle] at this
      rw [le_div_iff₀ hMr]; field_simp; linarith

/-- A leader modulo `M` as a real orbit inequality. -/
lemma isLeader_iff_real (M s : ℕ) (hM : 0 < M) :
    IsLeader M s ↔ 0 < s ∧ ∀ j : ℕ, (s : ℝ) / M ≤ nint (2 ^ j * ((s : ℝ) / M)) := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  unfold IsLeader
  refine and_congr Iff.rfl (forall_congr' fun j => ?_)
  have := sd_div_eq_nint M (2 ^ j * s) hM
  push_cast at this
  rw [← mul_div_assoc, ← this, div_le_div_iff_of_pos_right hMr]
  exact_mod_cast Iff.rfl

end GrayNecklaces
