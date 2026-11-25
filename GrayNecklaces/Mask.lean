module

public import GrayNecklaces.Basic

/-!
# The smaller-scale mask and its largest gap

`oddDist t x` is the distance from the integer `x` to the nearest odd multiple of `t`.
An odd `e` survives the mask of level `k` with parameter `α` if `α 2^g ≤ oddDist (2^g) e` for
`1 ≤ g < k`.  For `α ≤ 1/6` consecutive survivors are at most `G k` apart.
-/

@[expose] public section

namespace GrayNecklaces

/-- Distance from `x` to the nearest odd multiple of `t`. -/
def oddDist (t : ℕ) (x : ℤ) : ℤ := |x % (2 * t) - t|

lemma oddDist_bounds {t : ℕ} (ht : 0 < t) (x : ℤ) :
    -(t : ℤ) ≤ x % (2 * t) - t ∧ x % (2 * t) - t < t := by
  have h2t : (0 : ℤ) < 2 * t := by omega
  have hr := Int.emod_nonneg x h2t.ne'
  have hr2 := Int.emod_lt_of_pos x h2t
  constructor <;> omega

lemma oddDist_le {t : ℕ} (ht : 0 < t) (x : ℤ) : oddDist t x ≤ t := by
  have := oddDist_bounds ht x
  unfold oddDist; rw [abs_le]; constructor <;> omega

lemma oddDist_le_abs {t : ℕ} (ht : 0 < t) (x : ℤ) (n : ℤ) :
    oddDist t x ≤ |x - t * (2 * n + 1)| := by
  have hb := oddDist_bounds ht x
  have h1 := oddDist_le ht x
  unfold oddDist at h1 ⊢
  have hdm := Int.mul_ediv_add_emod x (2 * t)
  have e : x - t * (2 * n + 1) = (x % (2 * t) - t) + 2 * t * (x / (2 * t) - n) := by
    nth_rewrite 1 [← hdm]; ring
  rw [e]
  set y := x % (2 * t) - t
  set z := x / (2 * t) - n
  rcases lt_trichotomy z 0 with hz | hz | hz
  · have : 2 * (t : ℤ) * z ≤ -(2 * t) := by nlinarith
    calc |y| ≤ t := h1
      _ ≤ -(y + 2 * t * z) := by omega
      _ ≤ |y + 2 * t * z| := neg_le_abs _
  · rw [hz]; simp
  · have : 2 * (t : ℤ) ≤ 2 * t * z := by nlinarith
    calc |y| ≤ t := h1
      _ ≤ y + 2 * t * z := by omega
      _ ≤ |y + 2 * t * z| := le_abs_self _

lemma oddDist_eq {t : ℕ} (x : ℤ) : oddDist t x = |x - t * (2 * (x / (2 * t)) + 1)| := by
  unfold oddDist
  have hdm := Int.mul_ediv_add_emod x (2 * t)
  congr 1
  nth_rewrite 2 [← hdm]; ring

lemma oddDist_neg (t : ℕ) (x : ℤ) : oddDist t (-x) = oddDist t x := by
  rcases Nat.eq_zero_or_pos t with ht | ht
  · subst ht; simp [oddDist]
  have key : ∀ y : ℤ, oddDist t (-y) ≤ oddDist t y := by
    intro y
    rw [oddDist_eq (t := t) y]
    have := oddDist_le_abs ht (-y) (-(y / (2 * t)) - 1)
    calc oddDist t (-y) ≤ |-y - t * (2 * (-(y / (2 * t)) - 1) + 1)| := this
      _ = |y - t * (2 * (y / (2 * t)) + 1)| := by
          rw [show -y - t * (2 * (-(y / (2 * t)) - 1) + 1) = -(y - t * (2 * (y / (2 * t)) + 1)) by
            ring, abs_neg]
  apply le_antisymm (key x)
  have := key (-x); rwa [neg_neg] at this

lemma oddDist_add_mul (t : ℕ) (x n : ℤ) : oddDist t (x + 2 * t * n) = oddDist t x := by
  unfold oddDist; rw [Int.add_mul_emod_self_left]

/-- Survivors of the mask of level `k` with parameter `α`. -/
def Surv (k : ℕ) (α : ℝ) (e : ℤ) : Prop :=
  Odd e ∧ ∀ g, 1 ≤ g → g < k → α * 2 ^ g ≤ (oddDist (2 ^ g) e : ℝ)

/-- The gap bound `G_B`: `(2^k + 2)/3` for even `k`, `(2^k - 2)/3` for odd `k`. -/
def gapG (k : ℕ) : ℕ := if Even k then (2 ^ k + 2) / 3 else (2 ^ k - 2) / 3

lemma two_pow_mod_three (k : ℕ) : 2 ^ k % 3 = if Even k then 1 else 2 := by
  rcases Nat.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · rw [ite_eq_left ⟨m, rfl⟩, show m + m = 2 * m by ring, pow_mul, Nat.pow_mod]; norm_num
  · rw [ite_eq_right (Nat.not_even_iff_odd.mpr ⟨m, rfl⟩), pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num

/-- The odd integer `w = (2^(k+1) ± 1)/3`. -/
def wMid (k : ℕ) : ℕ := if Even (k + 1) then (2 ^ (k + 1) - 1) / 3 else (2 ^ (k + 1) + 1) / 3

lemma wMid_spec (k : ℕ) :
    (3 * wMid k + 1 = 2 ^ (k + 1) ∨ 3 * wMid k = 2 ^ (k + 1) + 1) ∧
    gapG (k + 1) = 2 ^ (k + 1) - 2 * wMid k := by
  have hm := two_pow_mod_three (k + 1)
  have h1 : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
  unfold wMid gapG
  split_ifs with he
  · rw [ite_eq_left he] at hm; constructor
    · left; omega
    · omega
  · rw [ite_eq_right he] at hm; constructor
    · right; omega
    · omega

/-- The midpoint survivors have distance at least `(t-1)/3` from odd multiples of `t`. -/
lemma oddDist_wMid {k g : ℕ} (hg : g ≤ k) :
    (2 ^ g : ℤ) - 1 ≤ 3 * oddDist (2 ^ g) (wMid k) := by
  set t := 2 ^ g with htdef
  have ht : 0 < t := by positivity
  have hdiv : 2 * t ∣ 2 ^ (k + 1) := by
    rw [htdef, ← pow_succ']; exact Nat.pow_dvd_pow 2 (by omega)
  obtain ⟨M', hM'⟩ := hdiv
  have hMZ : ((2 ^ (k + 1) : ℕ) : ℤ) = 2 * t * M' := by exact_mod_cast hM'
  rw [oddDist_eq]
  set n₀ := (wMid k : ℤ) / (2 * t)
  set Y : ℤ := 2 * M' - 6 * n₀ - 3
  have hY : Odd Y := ⟨M' - 3 * n₀ - 2, by simp only [Y]; ring⟩
  have hYabs : 1 ≤ |Y| := by
    rcases hY with ⟨r, hr⟩
    rw [hr]; rcases le_or_gt 0 r with h | h
    · rw [abs_of_nonneg (by omega)]; omega
    · rw [abs_of_neg (by omega)]; omega
  have htY : (t : ℤ) ≤ |(t : ℤ) * Y| := by
    rw [abs_mul, abs_of_pos (by exact_mod_cast ht)]; nlinarith
  obtain ⟨ε, hε, hw⟩ : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ 3 * (wMid k : ℤ) = 2 * t * M' + ε := by
    rcases (wMid_spec k).1 with h | h
    · have h' : ((3 * wMid k + 1 : ℕ) : ℤ) = ((2 ^ (k + 1) : ℕ) : ℤ) := by rw [h]
      rw [hMZ] at h'; push_cast at h'
      exact ⟨-1, Or.inr rfl, by linarith⟩
    · have h' : ((3 * wMid k : ℕ) : ℤ) = ((2 ^ (k + 1) + 1 : ℕ) : ℤ) := by rw [h]
      push_cast at h'
      have hMZ' : (2 : ℤ) ^ (k + 1) = 2 * t * M' := by push_cast at hMZ; exact hMZ
      exact ⟨1, Or.inl rfl, by linarith⟩
  have e : 3 * ((wMid k : ℤ) - t * (2 * n₀ + 1)) = t * Y + ε := by
    simp only [Y]; linear_combination hw
  have : |t * Y + ε| ≥ |(t : ℤ) * Y| - 1 := by
    have := abs_sub_abs_le_abs_sub ((t : ℤ) * Y) (-ε)
    rw [sub_neg_eq_add] at this
    rcases hε with rfl | rfl <;> simp at this ⊢ <;> linarith
  rw [← abs_of_pos (show (0:ℤ) < 3 by norm_num), ← abs_mul, e]
  linarith

/-- Shifting by a multiple of `2^k` preserves survival at level `k`. -/
lemma surv_add_mul {k : ℕ} {α : ℝ} {e : ℤ} (hk : 1 ≤ k) (h : Surv k α e) (n : ℤ) :
    Surv k α (e + 2 ^ k * n) := by
  refine ⟨?_, fun g hg1 hgk => ?_⟩
  · have : Even ((2 : ℤ) ^ k * n) := by
      apply Even.mul_right; exact (Int.even_pow.mpr ⟨even_two, by omega⟩)
    exact h.1.add_even this
  · have hp : (2 : ℤ) ^ k = 2 * 2 ^ g * 2 ^ (k - g - 1) := by
      conv_lhs => rw [show k = (g + 1) + (k - g - 1) by omega]
      rw [pow_add, pow_succ]; ring
    have e : (2 : ℤ) ^ k * n = 2 * ((2 ^ g : ℕ) : ℤ) * (2 ^ (k - g - 1) * n) := by
      push_cast; rw [hp]; ring
    rw [e, oddDist_add_mul]; exact h.2 g hg1 hgk

lemma surv_neg {k : ℕ} {α : ℝ} {e : ℤ} (h : Surv k α e) : Surv k α (-e) :=
  ⟨h.1.neg, fun g hg1 hgk => by rw [oddDist_neg]; exact h.2 g hg1 hgk⟩

/-- The midpoint `w` survives at level `k+1` when `α ≤ 1/6`. -/
lemma surv_wMid {k : ℕ} {α : ℝ} (hα : α ≤ 1 / 6) (hk : 1 ≤ k) : Surv (k + 1) α (wMid k) := by
  refine ⟨?_, fun g hg1 hgk => ?_⟩
  · have hm := two_pow_mod_three (k + 1)
    unfold wMid
    split_ifs with he
    · rw [ite_eq_left he] at hm
      have h4 : 4 ∣ 2 ^ (k + 1) := by
        rw [show 4 = 2 ^ 2 by norm_num]; exact Nat.pow_dvd_pow 2 (by omega)
      obtain ⟨r, hr⟩ := h4
      have : (2 ^ (k + 1) - 1) / 3 % 2 = 1 := by omega
      exact_mod_cast Nat.odd_iff.mpr this
    · rw [ite_eq_right he] at hm
      have h4 : 4 ∣ 2 ^ (k + 1) := by
        rw [show 4 = 2 ^ 2 by norm_num]; exact Nat.pow_dvd_pow 2 (by omega)
      obtain ⟨r, hr⟩ := h4
      have : (2 ^ (k + 1) + 1) / 3 % 2 = 1 := by omega
      exact_mod_cast Nat.odd_iff.mpr this
  · have h := oddDist_wMid (k := k) (g := g) (by omega)
    have h' : ((2 : ℝ) ^ g) - 1 ≤ 3 * (oddDist (2 ^ g) (wMid k) : ℝ) := by exact_mod_cast h
    have hP : (2 : ℝ) ≤ 2 ^ g := by
      have := pow_le_pow_right₀ (show (1:ℝ) ≤ 2 by norm_num) hg1; simpa using this
    nlinarith

/-- **The gap bound.**  For `α ≤ 1/6` every interval `(x, x + G k]` contains a survivor. -/
theorem surv_gap {α : ℝ} (hα : α ≤ 1 / 6) (_hα0 : 0 ≤ α) :
    ∀ k, 2 ≤ k → ∀ x : ℤ, ∃ e : ℤ, x < e ∧ e ≤ x + gapG k ∧ Surv k α e := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    intro x
    have hG : gapG 2 = 2 := by decide
    rw [hG]
    rcases Int.even_or_odd x with hx | hx
    · refine ⟨x + 1, by omega, by omega, hx.add_one, fun g hg1 hgk => ?_⟩
      have : g = 1 := by omega
      subst this
      have hod : oddDist (2 ^ 1) (x + 1) = 1 := by
        unfold oddDist
        obtain ⟨r, hr⟩ := hx
        have : (x + 1) % (2 * ((2 ^ 1 : ℕ) : ℤ)) = 1 ∨ (x + 1) % (2 * ((2 ^ 1 : ℕ) : ℤ)) = 3 := by
          push_cast; omega
        push_cast at this ⊢
        rcases this with h | h <;> rw [h] <;> norm_num
      rw [hod]; push_cast; linarith
    · refine ⟨x + 2, by omega, by omega, by
        obtain ⟨r, hr⟩ := hx; exact ⟨r + 1, by omega⟩, fun g hg1 hgk => ?_⟩
      have : g = 1 := by omega
      subst this
      have hod : oddDist (2 ^ 1) (x + 2) = 1 := by
        unfold oddDist
        obtain ⟨r, hr⟩ := hx
        have : (x + 2) % (2 * ((2 ^ 1 : ℕ) : ℤ)) = 1 ∨ (x + 2) % (2 * ((2 ^ 1 : ℕ) : ℤ)) = 3 := by
          push_cast; omega
        push_cast at this ⊢
        rcases this with h | h <;> rw [h] <;> norm_num
      rw [hod]; push_cast; linarith
  | succ k hk ih =>
    intro x
    obtain ⟨e, he1, he2, hes⟩ := ih x
    have hGle : gapG k ≤ gapG (k + 1) := by
      have h1 := two_pow_mod_three k
      have h2 := two_pow_mod_three (k + 1)
      have hp : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      have h4 : 4 ≤ 2 ^ k := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
      unfold gapG
      rcases Nat.even_or_odd k with hev | hod
      · have : ¬ Even (k + 1) := by rw [Nat.not_even_iff_odd]; exact hev.add_one
        rw [ite_eq_left hev, ite_eq_right this]; rw [ite_eq_left hev] at h1; rw [ite_eq_right this] at h2; omega
      · have : Even (k + 1) := hod.add_one
        rw [ite_eq_right (Nat.not_even_iff_odd.mpr hod), ite_eq_left this]
        rw [ite_eq_right (Nat.not_even_iff_odd.mpr hod)] at h1; rw [ite_eq_left this] at h2; omega
    by_cases hnew : Surv (k + 1) α e
    · exact ⟨e, he1, by omega, hnew⟩
    · -- `e` is in the new deletion zone around `2^k`
      obtain ⟨hw3, hG⟩ := wMid_spec k
      set w := wMid k
      have hwsurv := surv_wMid hα (by omega : 1 ≤ k)
      have h4 : (4 : ℕ) ≤ 2 ^ k := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
      have hp1 : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by ring
      have hw' : 3 * w ≤ 2 * 2 ^ k + 1 := by rcases hw3 with h | h <;> omega
      have hw'' : 2 * 2 ^ k ≤ 3 * w + 1 := by rcases hw3 with h | h <;> omega
      have hfail : (oddDist (2 ^ k) e : ℝ) < α * 2 ^ k := by
        by_contra hh; push Not at hh
        exact hnew ⟨hes.1, fun g hg1 hgk => by
          rcases Nat.lt_or_ge g k with hlt | hge
          · exact hes.2 g hg1 hlt
          · have : g = k := by omega
            subst this; exact hh⟩
      have h6 : 6 * oddDist (2 ^ k) e < 2 ^ k := by
        have : (6 * oddDist (2 ^ k) e : ℝ) < 2 ^ k := by
          have : (0 : ℝ) ≤ 2 ^ k := by positivity
          nlinarith
        exact_mod_cast this
      set T : ℤ := ((2 ^ k : ℕ) : ℤ) with hT
      have hTpos : (4 : ℤ) ≤ T := by simp only [T]; exact_mod_cast h4
      have hod : oddDist (2 ^ k) e = |e % (2 * T) - T| := rfl
      have h6' : 6 * |e % (2 * T) - T| < T := by rw [← hod]; exact h6
      have hwT : 3 * (w : ℤ) ≤ 2 * T + 1 := by simp only [T]; push_cast; exact_mod_cast hw'
      have hwT' : 2 * T ≤ 3 * (w : ℤ) + 1 := by simp only [T]; push_cast; exact_mod_cast hw''
      have hzone : (w : ℤ) < e % (2 * T) ∧ e % (2 * T) < 2 * T - w := by
        rcases abs_cases (e % (2 * T) - T) with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1] at h6' <;>
          constructor <;> omega
      have hPpos : (0 : ℤ) < 2 * T := by omega
      have hdm := Int.mul_ediv_add_emod e (2 * T)
      set n := e / (2 * T)
      have hPeq : (2 : ℤ) ^ (k + 1) = 2 * T := by simp only [T]; push_cast; ring
      have hs1 := surv_add_mul (by omega) hwsurv n
      have hs2 := surv_add_mul (by omega) (surv_add_mul (by omega) (surv_neg hwsurv) 1) n
      rw [hPeq] at hs1 hs2
      by_cases hc : x < 2 * T * n + w
      · refine ⟨2 * T * n + w, hc, ?_, ?_⟩
        · have : 2 * T * n + w < e := by rw [← hdm]; omega
          omega
        · rw [show 2 * T * n + (w : ℤ) = w + 2 * T * n by ring]
          convert hs1 using 2
      · push Not at hc
        refine ⟨2 * T * n + (2 * T - w), ?_, ?_, ?_⟩
        · have : e < 2 * T * n + (2 * T - w) := by rw [← hdm]; omega
          omega
        · have h2w : 2 * w ≤ 2 ^ (k + 1) := by omega
          have : (gapG (k + 1) : ℤ) = 2 * T - 2 * w := by
            rw [hG, Nat.cast_sub h2w]; push_cast; rw [hPeq]
          omega
        · rw [show 2 * T * n + (2 * T - w) = -(w : ℤ) + 2 * T * 1 + 2 * T * n by ring]
          convert hs2 using 2

end GrayNecklaces
