module

public import GrayNecklaces.DeletedRun

/-!
# Maximality of the central window, absence of antipodal rotations, and the run bound
-/

@[expose] public section

namespace GrayNecklaces

open Tiozzo

lemma dist_odd_mult {q X β : ℤ} (hq : 0 ≤ q) : q ≤ |2 * q * X - q * (2 * β + 1)| := by
  have : 2 * q * X - q * (2 * β + 1) = q * (2 * (X - β) - 1) := by ring
  rw [this, abs_mul, abs_of_nonneg hq]
  have : 1 ≤ |2 * (X - β) - 1| := by
    rcases le_or_gt 0 (2 * (X - β) - 1) with h | h
    · rw [abs_of_nonneg h]; omega
    · rw [abs_of_neg h]; omega
  nlinarith

/-- `M ∣ (2^d - 1) a` forces `k ∣ d` for a primitive window. -/
lemma dvd_of_dvd_prim {a k : ℕ} (hk : 1 ≤ k)
    (prim : ∀ i, 0 < i → i < k → ¬ (2 ^ k - 1) ∣ (2 ^ i - 1) * a) {d : ℕ}
    (hd : (2 ^ k - 1) ∣ (2 ^ d - 1) * a) : k ∣ d := by
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
  exact prim i hi (Nat.mod_lt _ (by omega)) hd2

/-- A maximal window has no antipodal rotation. -/
theorem anti_of_max (h87 : Theorem87) (h9 : TuningNesting) {p a k : ℕ} (hm : IsMaxWin p a k)
    (h6 : 6 * a < 2 ^ k) (hk3 : 3 ≤ k) : ∀ i, ¬ (2 ^ k - 1) ∣ (2 ^ i + 1) * a := by
  intro i hd
  have hgood := hm.good h87
  have hprim := hgood.2.2
  have hapos := hm.1.2.2.1.pos
  have haodd := hm.1.2.2.1
  have hkp := hm.1.2.1
  have hpd : ∀ d, (2 ^ k - 1) ∣ (2 ^ d - 1) * a → k ∣ d :=
    fun d hd => dvd_of_dvd_prim (a := a) (k := k) (by omega) hprim hd
  -- `k ∣ 2i`
  have h2i : k ∣ 2 * i := by
    apply hpd
    have : (2 ^ (2 * i) - 1) * a = (2 ^ i - 1) * ((2 ^ i + 1) * a) := by
      rw [pow_mul', ← mul_assoc]; congr 1
      have : 1 ≤ 2 ^ i := Nat.one_le_two_pow
      zify [this, Nat.one_le_pow 2 _ (by positivity : 0 < 2 ^ i)]; ring
    rw [this]; exact Dvd.dvd.mul_left hd _
  -- reduce `i` modulo `k`
  set i' := i % k
  have hd' : (2 ^ k - 1) ∣ (2 ^ i' + 1) * a := by
    have h1 : 2 ^ i = 2 ^ i' * (2 ^ k) ^ (i / k) := by rw [← pow_mul, ← pow_add, Nat.mod_add_div]
    have h2 : 1 ≤ (2 ^ k) ^ (i / k) := Nat.one_le_pow _ _ (by positivity)
    have hdvd1 : (2 ^ k - 1) ∣ (2 ^ k) ^ (i / k) - 1 := by
      simpa using Nat.sub_dvd_pow_sub_pow (2 ^ k) 1 (i / k)
    have e : (2 ^ i + 1) * a = 2 ^ i' * ((2 ^ k) ^ (i / k) - 1) * a + (2 ^ i' + 1) * a := by
      rw [h1]
      have : 2 ^ i' ≤ 2 ^ i' * (2 ^ k) ^ (i / k) := Nat.le_mul_of_pos_right _ h2
      zify [h2, this]; ring
    rw [e] at hd
    exact (Nat.dvd_add_right (Dvd.dvd.mul_right (Dvd.dvd.mul_left hdvd1 _) _)).mp hd
  have hi'k : i' < k := Nat.mod_lt _ (by omega)
  have h2i' : k ∣ 2 * i' := by
    have e : 2 * i' + k * (2 * (i / k)) = 2 * i := by
      have := Nat.mod_add_div i k; simp only [i']; linarith
    rw [← e] at h2i
    exact (Nat.dvd_add_left (dvd_mul_right _ _)).mp h2i
  have hM : 7 ≤ 2 ^ k - 1 := by
    have : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk3; omega
  rcases Nat.eq_zero_or_pos i' with h0 | hpos
  · rw [h0, pow_zero] at hd'
    have hcop : Nat.Coprime (2 ^ k - 1) 2 := by
      rw [Nat.coprime_comm, Nat.prime_two.coprime_iff_not_dvd]
      intro h2; obtain ⟨t, ht⟩ := h2
      have : 2 ^ k = 2 * 2 ^ (k - 1) := by rw [← pow_succ']; congr 1; omega
      have : 1 ≤ 2 ^ (k - 1) := Nat.one_le_two_pow
      omega
    have := hcop.dvd_of_dvd_mul_left hd'
    have := Nat.le_of_dvd hapos this
    omega
  · have hk2 : k = 2 * i' := by
      obtain ⟨t, ht⟩ := h2i'
      have : t = 1 := by
        rcases t with _ | _ | t
        · omega
        · rfl
        · nlinarith
      subst this; omega
    set C := 2 ^ i'
    have hC4 : 4 ≤ C := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ i' := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hBC : 2 ^ k = C * C := by rw [hk2, two_mul, pow_add]
    have hfac : 2 ^ k - 1 = (C + 1) * (C - 1) := by
      rw [hBC]; zify [show 1 ≤ C by omega, show 1 ≤ C * C by nlinarith]; ring
    rw [hfac, mul_comm (2 ^ i' + 1) a] at hd'
    have hdiv : C - 1 ∣ a := by
      have : (C + 1) * (C - 1) ∣ (C + 1) * a := by rw [mul_comm (C + 1) a]; exact hd'
      exact Nat.dvd_of_mul_dvd_mul_left (by omega) this
    obtain ⟨b', hb'⟩ := hdiv
    have hb'odd : Odd b' := by
      rw [hb'] at haodd; exact (Nat.odd_mul.mp haodd).2
    have hb'3 : 3 * b' < C := by
      by_contra hh; push Not at hh
      rw [hb', hBC] at h6
      have : 2 * C * (C - 1) ≤ 6 * ((C - 1) * b') := by
        have : C * (C - 1) ≤ 3 * b' * (C - 1) := Nat.mul_le_mul_right _ hh
        nlinarith
      have : C * C ≤ 2 * C * (C - 1) := by
        have : C ≤ 2 * (C - 1) := by omega
        nlinarith
      omega
    have hwin : IsWin p b' i' := ⟨by omega, by omega, hb'odd, hb'3⟩
    have hCr : (4 : ℝ) ≤ C := by exact_mod_cast hC4
    have hC' : (2 : ℝ) ^ i' = C := by simp only [C]; push_cast; ring
    have hb'pos : (0 : ℝ) < b' := by have := hb'odd.pos; exact_mod_cast this
    have hRa : wR a k = b' / (C + 1) := by
      unfold wR
      have h1 : (2 : ℝ) ^ k = C * C := by exact_mod_cast hBC
      have h2 : (a : ℝ) = (C - 1) * b' := by
        rw [hb']; push_cast [show 1 ≤ C by omega]; ring
      rw [h1, h2, div_eq_div_iff (by nlinarith) (by linarith)]; ring
    have hwT : wT b' i' = b' * (C - 2) / (C * (C - 1)) := by
      unfold wT wR; rw [hC']; field_simp
    have hwR' : wR b' i' = b' / (C - 1) := by unfold wR; rw [hC']
    apply hm.not_interior h87 h9 hwin
    · rw [hRa, hwT, div_lt_div_iff₀ (by nlinarith) (by positivity)]; nlinarith
    · rw [hRa, hwR']
      exact div_lt_div_of_pos_left hb'pos (by linarith) (by linarith)

end GrayNecklaces
