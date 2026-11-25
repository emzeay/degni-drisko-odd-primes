module

public import GrayNecklaces.GapSurvivor

/-!
# Survivors from preimages of `1/2` under the capped tent map
-/

@[expose] public section

namespace GrayNecklaces

open Tiozzo

/-- `2‖x/(2t)‖ = 1 - oddDist t x / t` for integers. -/
lemma two_nint_div {t : ℕ} (ht : 0 < t) (x : ℤ) :
    2 * nint ((x : ℝ) / (2 * t)) = 1 - (oddDist t x : ℝ) / t := by
  have h2t : (0 : ℤ) < 2 * t := by omega
  have hdm := Int.mul_ediv_add_emod x (2 * t)
  set r := x % (2 * t)
  have hr0 := Int.emod_nonneg x h2t.ne'
  have hr1 := Int.emod_lt_of_pos x h2t
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hx : (x : ℝ) / (2 * t) = ((x / (2 * t) : ℤ) : ℝ) + (r : ℝ) / (2 * t) := by
    have : (x : ℝ) = 2 * t * ((x / (2 * t) : ℤ) : ℝ) + r := by
      have := congrArg (fun z : ℤ => (z : ℝ)) hdm; push_cast at this; linarith
    rw [this]; field_simp
  rw [hx, add_comm, nint_add_int]
  have hrR0 : (0 : ℝ) ≤ r := by exact_mod_cast hr0
  have hrR1 : (r : ℝ) < 2 * t := by exact_mod_cast hr1
  unfold oddDist
  rw [show x % (2 * (t : ℤ)) = r from rfl]
  rcases le_total r t with h | h
  · have hR : (r : ℝ) ≤ t := by exact_mod_cast h
    have hn : nint ((r : ℝ) / (2 * t)) = r / (2 * t) :=
      nint_of_mem (by positivity) (by rw [div_le_iff₀ (by positivity)]; linarith)
    have ha : |r - (t : ℤ)| = t - r := by rw [abs_of_nonpos (by omega)]; ring
    rw [hn, ha]; push_cast; field_simp; ring
  · have hR : (t : ℝ) ≤ r := by exact_mod_cast h
    have hr2 : (r : ℝ) / (2 * t) < 1 := by rw [div_lt_one (by positivity)]; linarith
    have hr3 : 1 / 2 ≤ (r : ℝ) / (2 * t) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    have hn : nint ((r : ℝ) / (2 * t)) = 1 - r / (2 * t) := by
      rw [nint_eq_abs_sub (n := 1) (by push_cast; rw [abs_le]; constructor <;> linarith)]
      push_cast; rw [abs_of_neg (by linarith)]; ring
    have ha : |r - (t : ℤ)| = r - t := abs_of_nonneg (by omega)
    rw [hn, ha]; push_cast; field_simp; ring

section

variable {a k : ℕ} (h : Central a k)
include h

/-- A preimage of `1/2` under `Fm^n` never meets the cap. -/
lemma no_cap {z : ℝ} (_hz : 0 ≤ z ∧ z ≤ 1) {n : ℕ} (hn : (Fm a k)^[n] z = 1 / 2) :
    ∀ i ≤ n, (Fm a k)^[i] z = tent^[i] z ∧ (1 ≤ i → tent^[i] z < lam a k) := by
  intro i
  induction i with
  | zero => intro _; simp
  | succ i ih =>
    intro hi
    obtain ⟨h1, _⟩ := ih (by omega)
    have hlt : tent (tent^[i] z) < lam a k := by
      by_contra hh
      push Not at hh
      have hcap : (Fm a k)^[i + 1] z = lam a k := by
        rw [Function.iterate_succ_apply', h1]; unfold Fm; exact min_eq_right hh
      have : (Fm a k)^[n] z = xo a k (n - (i + 1)) := by
        have e : n = (n - (i + 1)) + (i + 1) := by omega
        calc (Fm a k)^[n] z = (Fm a k)^[(n - (i + 1)) + (i + 1)] z := by rw [← e]
          _ = xo a k (n - (i + 1)) := by
            rw [Function.iterate_add_apply, hcap, ← xo_zero, Fm_iterate_xo h, zero_add]
      rw [this] at hn
      exact xo_ne_half h _ hn
    refine ⟨?_, fun _ => by rw [Function.iterate_succ_apply']; exact hlt⟩
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', h1]
    unfold Fm; exact min_eq_left hlt.le

/-- **Extraction**: a preimage of `1/2` at time `h - 1` gives an odd integer `e' = 2^h (1 - z)`
passing the smaller-scale tests with the radius `R`. -/
theorem extract {z : ℝ} (hz : 0 ≤ z ∧ z ≤ 1) {hh : ℕ} (hh2 : 2 ≤ hh)
    (hn : (Fm a k)^[hh - 1] z = 1 / 2) :
    ∃ e' : ℤ, Odd e' ∧ (e' : ℝ) = 2 ^ hh * (1 - z) ∧
      ∀ g, 1 ≤ g → g < hh → wR a k * 2 ^ g < (oddDist (2 ^ g) e' : ℝ) := by
  have hnc := no_cap h hz hn
  have hT : tent^[hh - 1] z = 1 / 2 := by rw [← (hnc (hh - 1) le_rfl).1]; exact hn
  rw [show hh - 1 = (hh - 2) + 1 by omega, tent_iterate hz.1 hz.2] at hT
  have hq : |2 ^ (hh - 2) * z - round (2 ^ (hh - 2) * z)| = 1 / 4 := by
    rw [← nint_eq_abs_sub (abs_sub_round _)]; linarith
  have hC : (2 : ℝ) ^ hh = 4 * 2 ^ (hh - 2) := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
  obtain ⟨w', hw', hw'odd⟩ : ∃ w' : ℤ, (2 : ℝ) ^ hh * z = w' ∧ Odd w' := by
    set n := round (2 ^ (hh - 2) * z)
    rcases abs_eq (by norm_num : (0:ℝ) ≤ 1 / 4) |>.mp hq with h5 | h5
    · exact ⟨4 * n + 1, by rw [hC]; push_cast; linarith, ⟨2 * n, by ring⟩⟩
    · exact ⟨4 * n - 1, by rw [hC]; push_cast; linarith, ⟨2 * n - 1, by ring⟩⟩
  refine ⟨2 ^ hh - w', Even.sub_odd (Int.even_pow.mpr ⟨even_two, by omega⟩) hw'odd,
    by push_cast; rw [← hw']; ring, ?_⟩
  intro g hg1 hgh
  -- the step `i = hh - g`
  have hi := hnc (hh - g) (by omega)
  have hlt := hi.2 (by omega)
  rw [show hh - g = (hh - g - 1) + 1 by omega, tent_iterate hz.1 hz.2] at hlt
  have e1 : (2 : ℝ) ^ (hh - g - 1) * z =
      ((2 ^ (hh - g - 1) : ℤ) : ℝ) - ((2 ^ hh - w' : ℤ) : ℝ) / (2 * ((2 ^ g : ℕ) : ℝ)) := by
    push_cast
    have : (2 : ℝ) ^ hh = 2 ^ (hh - g - 1) * (2 * 2 ^ g) := by
      rw [← pow_succ', ← pow_add]; congr 1; omega
    rw [← hw', this]
    field_simp
    ring
  rw [e1, sub_eq_add_neg, add_comm, nint_add_int, nint_neg, two_nint_div (by positivity)] at hlt
  unfold lam at hlt
  push_cast at hlt
  have hP : (0 : ℝ) < 2 ^ g := by positivity
  have : wR a k < (oddDist (2 ^ g) (2 ^ hh - w') : ℝ) / 2 ^ g := by linarith
  rw [lt_div_iff₀ hP] at this
  exact this

end

/-- `Fm` is `2`-Lipschitz. -/
lemma Fm_lipschitz (a k : ℕ) (x y : ℝ) : |Fm a k x - Fm a k y| ≤ 2 * |x - y| := by
  unfold Fm
  have h1 := abs_min_sub_min_le_max (tent x) (lam a k) (tent y) (lam a k)
  have h2 : |tent x - tent y| ≤ 2 * |x - y| := by
    unfold tent
    have := abs_min_sub_min_le_max (2 * x) (2 - 2 * x) (2 * y) (2 - 2 * y)
    rw [show 2 * x - 2 * y = 2 * (x - y) by ring, show 2 - 2 * x - (2 - 2 * y) = -(2 * (x - y)) by ring,
      abs_neg, abs_mul, abs_two, max_self] at this
    exact this
  simp only [sub_self, abs_zero] at h1
  rcases le_total |tent x - tent y| 0 with h | h
  · have := le_max_iff.mp h1
    rcases this with h3 | h3
    · linarith
    · linarith [abs_nonneg (x - y)]
  · rw [max_eq_left h] at h1; linarith

lemma Fm_iterate_lipschitz (a k n : ℕ) (x y : ℝ) :
    |(Fm a k)^[n] x - (Fm a k)^[n] y| ≤ 2 ^ n * |x - y| := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', pow_succ]
    calc |Fm a k ((Fm a k)^[n] x) - Fm a k ((Fm a k)^[n] y)|
        ≤ 2 * |(Fm a k)^[n] x - (Fm a k)^[n] y| := Fm_lipschitz a k _ _
      _ ≤ 2 * (2 ^ n * |x - y|) := by linarith
      _ = 2 ^ n * 2 * |x - y| := by ring

end GrayNecklaces
