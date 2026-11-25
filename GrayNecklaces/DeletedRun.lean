module

public import GrayNecklaces.Assembly
public import GrayNecklaces.TentCover
public import GrayNecklaces.Mask

/-!
# Consecutive leaders, their dyadic split, and the central window
-/

@[expose] public section

namespace GrayNecklaces

open Tiozzo

/-- Consecutive positive leaders modulo `2^p - 1` at an odd prime length. -/
structure Consec (p σ τ : ℕ) : Prop where
  hp : p.Prime
  hodd : Odd p
  hσ : IsLeader (2 ^ p - 1) σ
  hτ : IsLeader (2 ^ p - 1) τ
  hlt : σ < τ
  hnone : ∀ t, σ < t → t < τ → ¬ IsLeader (2 ^ p - 1) t

/-- The dyadic split of `σ < τ`: the multiple of the largest power of two strictly between. -/
lemma exists_split {σ τ p : ℕ} (hlt : σ + 1 < τ) (hτ : τ < 2 ^ p) :
    ∃ e c : ℕ, e < p ∧ σ < c * 2 ^ e ∧ c * 2 ^ e < τ ∧ (c - 1) * 2 ^ e ≤ σ ∧
      τ ≤ (c + 1) * 2 ^ e ∧ Odd c ∧
      ∀ e' c' : ℕ, σ < c' * 2 ^ e' → c' * 2 ^ e' < τ → e' ≤ e := by
  classical
  let P : ℕ → Prop := fun e => ∃ c, σ < c * 2 ^ e ∧ c * 2 ^ e < τ
  have hP0 : P 0 := ⟨σ + 1, by simp, by simp; omega⟩
  have hPbig : ∀ e', p ≤ e' → ¬ P e' := by
    rintro e' he' ⟨c', h1, h2⟩
    have : 2 ^ p ≤ 2 ^ e' := Nat.pow_le_pow_right (by norm_num) he'
    rcases Nat.eq_zero_or_pos c' with hc | hc
    · subst hc; simp at h1
    · have : 2 ^ e' ≤ c' * 2 ^ e' := Nat.le_mul_of_pos_left _ hc
      omega
  set e := Nat.findGreatest P p
  have hPe : P e := Nat.findGreatest_spec (Nat.zero_le p) hP0
  have hep : e < p := by
    rcases Nat.lt_or_ge e p with h | h
    · exact h
    · exact absurd hPe (hPbig e h)
  have hmax : ∀ e' c' : ℕ, σ < c' * 2 ^ e' → c' * 2 ^ e' < τ → e' ≤ e := by
    intro e' c' h1 h2
    rcases Nat.lt_or_ge e' p with h | h
    · exact Nat.le_findGreatest h.le ⟨c', h1, h2⟩
    · exact absurd ⟨c', h1, h2⟩ (hPbig e' h)
  obtain ⟨c, hc1, hc2⟩ := hPe
  have hpow : 2 ^ (e + 1) = 2 * 2 ^ e := by ring
  have hcodd : Odd c := by
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    obtain ⟨r, hr⟩ := hev
    have := hmax (e + 1) r (by rw [hpow]; rw [hr] at hc1; linarith)
      (by rw [hpow]; rw [hr] at hc2; linarith)
    omega
  obtain ⟨β, hβ⟩ := hcodd
  refine ⟨e, c, hep, hc1, hc2, ?_, ?_, ⟨β, hβ⟩, hmax⟩
  · by_contra hh
    push Not at hh
    have := hmax (e + 1) β (by rw [hpow]; rw [hβ] at hh; simp at hh; nlinarith)
      (by rw [hpow]; rw [hβ] at hc2; nlinarith)
    omega
  · by_contra hh
    push Not at hh
    have := hmax (e + 1) (β + 1) (by rw [hpow]; rw [hβ] at hc1; nlinarith)
      (by rw [hpow]; rw [hβ] at hh; nlinarith)
    omega

namespace Consec

variable {p σ τ : ℕ} (hc : Consec p σ τ)
include hc

lemma p3 : 3 ≤ p := by
  have := hc.hp.two_le
  rcases Nat.lt_or_ge p 3 with h | h
  · have : p = 2 := by omega
    subst this; exact absurd hc.hodd (by decide)
  · exact h

lemma M_odd : Odd (2 ^ p - 1) := by
  have : 2 ^ p = 2 * 2 ^ (p - 1) := by rw [← pow_succ']; congr 1; have := hc.p3; omega
  have : 1 ≤ 2 ^ (p - 1) := Nat.one_le_two_pow
  exact ⟨2 ^ (p - 1) - 1, by omega⟩

lemma σ_odd : Odd σ := (hc.hσ.bounds hc.M_odd).1
lemma τ_odd : Odd τ := (hc.hτ.bounds hc.M_odd).1

lemma τ_le (h87 : Theorem87) : 6 * τ ≤ 2 ^ p - 2 := leader_le_max h87 hc.hp hc.p3 hc.hodd hc.hτ

lemma N_ge : 8 ≤ 2 ^ p := by
  calc 8 = 2 ^ 3 := by norm_num
    _ ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hc.p3

/-- Leaders among odd ranks below `N/3` are exactly the survivors of the maximal windows. -/
lemma leader_iff (h87 : Theorem87) {s : ℕ} (hs : Odd s) (h3 : 3 * s < 2 ^ p) :
    IsLeader (2 ^ p - 1) s ↔ ¬ ∃ b j, IsMaxWin p b j ∧ Del p b j s :=
  (sieve h87 hc.hp hs h3).1

/-- Every odd rank strictly between `σ` and `τ` is deleted by a maximal window. -/
lemma gap_deleted (h87 : Theorem87) {s : ℕ} (hs : Odd s) (h1 : σ < s) (h2 : s < τ) :
    ∃ b j, IsMaxWin p b j ∧ Del p b j s := by
  have := hc.τ_le h87
  by_contra hh
  exact hc.hnone s h1 h2 ((hc.leader_iff h87 hs (by omega)).mpr hh)

/-- An odd rank between the leaders deleted by an admissible window is deleted by a maximal one,
and hence is not a leader. -/
lemma not_leader_of_del (h87 : Theorem87) {b j s : ℕ} (hw : IsWin p b j) (hd : Del p b j s)
    (h3 : 3 * s < 2 ^ p) : ¬ IsLeader (2 ^ p - 1) s := by
  obtain ⟨b', j', hm, hd'⟩ := del_maximal hw hd
  exact fun hL => (hc.leader_iff h87 hd.1 h3).mp hL ⟨b', j', hm, hd'⟩

end Consec

/-! ### Deletion in center–radius form -/

/-- The deletion test as `|s - cen| (N - q) < cen q`. -/
lemma del_iff_cen {p b j s : ℕ} (hj : 1 ≤ j) (hjp : j < p) :
    Del p b j s ↔ Odd s ∧
      |(s : ℝ) - b * 2 ^ (p - j)| * (2 ^ p - 2 ^ (p - j)) < (b * 2 ^ (p - j)) * 2 ^ (p - j) := by
  rw [del_iff hj hjp.le]
  refine and_congr Iff.rfl ?_
  have hD : (2 : ℝ) ≤ 2 ^ j := by
    have := pow_le_pow_right₀ (show (1:ℝ) ≤ 2 by norm_num) hj; simpa using this
  have hq : (0 : ℝ) < 2 ^ (p - j) := by positivity
  have hN : (2 : ℝ) ^ p - 2 ^ (p - j) = (2 ^ j - 1) * 2 ^ (p - j) := by
    rw [pow_split hjp.le]; ring
  rw [hN]
  unfold wR
  rw [div_mul_eq_mul_div, lt_div_iff₀ (by linarith)]
  constructor <;> intro h <;> nlinarith

namespace Consec

variable {p σ τ : ℕ} (hc : Consec p σ τ)
include hc

/-- A maximal window deleting a point between the leaders is centered between them. -/
lemma center_between (h87 : Theorem87) {b j s : ℕ} (hm : IsMaxWin p b j) (hd : Del p b j s)
    (h1 : σ < s) (h2 : s < τ) : σ < b * 2 ^ (p - j) ∧ b * 2 ^ (p - j) < τ := by
  have hj : 1 ≤ j := by have := hm.1.1; omega
  have hjp := hm.1.2.1
  have hτ6 := hc.τ_le h87
  have hdel := (del_iff hj hjp.le).mp hd
  constructor
  · by_contra hh
    push Not at hh
    apply (hc.leader_iff h87 hc.σ_odd (by omega)).mp hc.hσ
    refine ⟨b, j, hm, (del_iff hj hjp.le).mpr ⟨hc.σ_odd, ?_⟩⟩
    have hh' : ((b * 2 ^ (p - j) : ℕ) : ℝ) ≤ σ := by exact_mod_cast hh
    push_cast at hh'
    have h1' : (σ : ℝ) < s := by exact_mod_cast h1
    have := hdel.2
    rw [abs_lt] at this ⊢
    constructor <;> linarith [this.1, this.2]
  · by_contra hh
    push Not at hh
    apply (hc.leader_iff h87 hc.τ_odd (by omega)).mp hc.hτ
    refine ⟨b, j, hm, (del_iff hj hjp.le).mpr ⟨hc.τ_odd, ?_⟩⟩
    have hh' : (τ : ℝ) ≤ ((b * 2 ^ (p - j) : ℕ) : ℝ) := by exact_mod_cast hh
    push_cast at hh'
    have h2' : (s : ℝ) < τ := by exact_mod_cast h2
    have := hdel.2
    rw [abs_lt] at this ⊢
    constructor <;> linarith [this.1, this.2]

end Consec

end GrayNecklaces
