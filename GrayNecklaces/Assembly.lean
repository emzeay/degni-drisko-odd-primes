module

public import GrayNecklaces.Ranks
public import GrayNecklaces.Maximal

/-!
# Assembly: from the reflection property to the exported statement

`ReflectionCore p` says that consecutive leaders modulo `2^p - 1` are mirror images about their
dyadic split.  This file proves the theorem from it (Section 2 of the proof).
-/

@[expose] public section

namespace GrayNecklaces

open Tiozzo

/-- Consecutive positive leaders `σ < τ` modulo `2^p - 1` satisfy `σ + τ = 2m`, where
`m = c 2^e` (`c` odd) is the unique highest-scale dyadic center between them. -/
def ReflectionCore (p : ℕ) : Prop :=
  ∀ σ τ : ℕ, IsLeader (2 ^ p - 1) σ → IsLeader (2 ^ p - 1) τ → σ < τ →
    (∀ t, σ < t → t < τ → ¬ IsLeader (2 ^ p - 1) t) →
    ∃ e c : ℕ, Odd c ∧ σ + τ = 2 * (c * 2 ^ e) ∧ c * 2 ^ e ≤ σ + 2 ^ e ∧ σ < c * 2 ^ e

/-- Mirror images about an odd multiple of `2^e` have XOR `2^(e+1) - 1`. -/
lemma reflect_xor {σ τ e c : ℕ} (hc : Odd c) (hsum : σ + τ = 2 * (c * 2 ^ e))
    (hlo : c * 2 ^ e ≤ σ + 2 ^ e) (hσ : σ < c * 2 ^ e) :
    σ ^^^ (τ - 1) = 2 ^ (e + 1) - 1 := by
  obtain ⟨β, rfl⟩ := hc
  have hP : 2 ^ (e + 1) = 2 * 2 ^ e := by rw [pow_succ]; ring
  have hQ1 : 1 ≤ 2 ^ e := Nat.one_le_two_pow
  have e1 : (2 * β + 1) * 2 ^ e = 2 * (β * 2 ^ e) + 2 ^ e := by ring
  have e2 : 2 ^ (e + 1) * β = 2 * (β * 2 ^ e) := by rw [hP]; ring
  rw [e1] at hsum hlo hσ
  set L1 := σ - 2 * (β * 2 ^ e) with hL1
  have hσeq : σ = 2 ^ (e + 1) * β + L1 := by omega
  have hτeq : τ - 1 = 2 ^ (e + 1) * β + (2 ^ (e + 1) - (L1 + 1)) := by omega
  have hL1lt : L1 < 2 ^ (e + 1) := by omega
  apply Nat.eq_of_testBit_eq; intro t
  rw [Nat.testBit_xor, hσeq, hτeq, Nat.testBit_two_pow_mul_add _ hL1lt,
    Nat.testBit_two_pow_mul_add _ (by omega), Nat.testBit_two_pow_sub_one]
  split_ifs with ht
  · rw [Nat.testBit_two_pow_sub_succ hL1lt]
    simp [ht]
  · simp [ht]

/-! ### Leaders and representatives -/

lemma IsLeader.bounds {M σ : ℕ} (hM : Odd M) (h : IsLeader M σ) : Odd σ ∧ 3 * σ ≤ M := by
  have h0 := h.2 0
  simp only [pow_zero, one_mul] at h0
  have h2 : 2 * σ ≤ M := by have := sd_le_half M σ; omega
  refine ⟨h.odd hM h2, ?_⟩
  have h1 := h.2 1
  simp only [pow_one] at h1
  have h2' : 2 * σ < M := by obtain ⟨m, hm⟩ := hM; omega
  have := sd_le_sub M (2 * σ)
  rw [Nat.mod_eq_of_lt h2'] at this
  omega

lemma two_pow_odd_mod_three {p : ℕ} (hp : Odd p) : 2 ^ p % 3 = 2 := by
  obtain ⟨m, rfl⟩ := hp
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]; norm_num

lemma rot1_zero (n : ℕ) : rot1 n 0 = 0 := by simp [rot1]

lemma isRep_iff {p : ℕ} (hp : 1 ≤ p) (x : Rank p) :
    IsRepresentativeRank x ↔ x.val = 0 ∨
      (Even x.val ∧ 2 ≤ x.val ∧ IsLeader (2 ^ p - 1) (2 ^ p - 1 - x.val)) ∨
      (Odd x.val ∧ IsLeader (2 ^ p + 1) (2 ^ p - x.val)) := by
  rw [isRepresentativeRank_iff hp]
  have hx := x.isLt
  rcases Nat.even_or_odd x.val with hev | hodd
  · obtain ⟨v, hv⟩ := hev
    rcases Nat.eq_zero_or_pos v with h0 | h0
    · subst h0
      have : x.val = 0 := by omega
      rw [this]
      simp only [true_or, iff_true]
      intro k; induction k with
      | zero => simp
      | succ k ih => rw [Function.iterate_succ_apply', show (rot1 p)^[k] 0 = 0 by omega, rot1_zero]
    · rw [hv, show v + v = 2 * v by ring]
      rw [isRep_even_iff hp (by omega) (by omega)]
      have : ¬ Odd (2 * v) := by rw [Nat.not_odd_iff_even]; exact even_two_mul v
      simp only [this, false_and, or_false]
      constructor
      · intro h; right; exact ⟨even_two_mul v, by omega, h⟩
      · rintro (h | ⟨_, _, h⟩)
        · omega
        · exact h
  · obtain ⟨w, hw⟩ := hodd
    have e : x.val = 2 * (w + 1) - 1 := by omega
    rw [e, isRep_odd_iff hp (by omega) (by omega)]
    have h1 : ¬ (2 * (w + 1) - 1 = 0) := by omega
    have h2 : ¬ Even (2 * (w + 1) - 1) := by
      rw [Nat.not_even_iff_odd]; exact ⟨w, by omega⟩
    have h3 : Odd (2 * (w + 1) - 1) := ⟨w, by omega⟩
    simp only [h1, h2, h3, false_and, false_or, true_and]
    rw [show 2 ^ p + 1 - 2 * (w + 1) = 2 ^ p - (2 * (w + 1) - 1) by omega]

/-- The largest positive leader. -/
lemma sigmaMax_leader {p : ℕ} (hp : Odd p) (hp3 : 3 ≤ p) :
    IsLeader (2 ^ p - 1) ((2 ^ p - 2) / 6) := by
  have hmod := two_pow_odd_mod_three hp
  have hP : 2 ^ p = 4 * 2 ^ (p - 2) := by
    rw [show 4 = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
  have hP1 : 2 ^ (p - 1) = 2 * 2 ^ (p - 2) := by rw [← pow_succ']; congr 1; omega
  have hP2pos : 2 ≤ 2 ^ (p - 2) := two_le_two_pow (by omega)
  set x := (2 ^ p - 2) / 6 with hx
  set P2 := 2 ^ (p - 2)
  have h3x : 3 * x = 2 * P2 - 1 := by omega
  refine ⟨by omega, fun j => ?_⟩
  rw [sd_pow_mod_sub]
  set i := j % p
  have hip : i < p := Nat.mod_lt _ (by omega)
  rcases Nat.eq_zero_or_pos i with hi | hi
  · rw [hi, pow_zero, one_mul, sd_eq_self (by omega)]
  set M := 2 ^ p - 1 with hMdef
  have hA : 2 ^ i = 2 * 2 ^ (i - 1) := by rw [← pow_succ']; congr 1; omega
  have hAle : 2 ^ (i - 1) ≤ P2 := Nat.pow_le_pow_right (by norm_num) (by omega)
  set A := 2 ^ (i - 1)
  have hA1 : 1 ≤ A := Nat.one_le_two_pow
  have hAnd : ¬ 3 ∣ A := by
    intro h; have := (Nat.Prime.dvd_of_dvd_pow (by norm_num) h); omega
  have key : (3 : ℤ) * (2 ^ i * x : ℕ) = A * (M - 1 : ℤ) := by
    have h3xZ : (3 : ℤ) * x = 2 * P2 - 1 := by
      have : 3 * x + 1 = 2 * P2 := by omega
      have : (3 * x + 1 : ℤ) = 2 * P2 := by exact_mod_cast this
      linarith
    have hMZ : (M : ℤ) = 4 * P2 - 1 := by
      have : M + 1 = 4 * P2 := by omega
      have : (M + 1 : ℤ) = 4 * P2 := by exact_mod_cast this
      linarith
    have hAZ : (2 : ℤ) ^ i = 2 * A := by exact_mod_cast hA
    push_cast; rw [hAZ, hMZ]
    linear_combination (2 * (A : ℤ)) * h3xZ
  have hdm := Nat.div_add_mod (2 ^ i * x) M
  have hρ : (2 ^ i * x) % M < M := Nat.mod_lt _ (by omega)
  unfold sd
  generalize (2 ^ i * x) / M = qq at hdm
  generalize (2 ^ i * x) % M = ρ at hdm hρ ⊢
  have hdmZ : ((2 ^ i * x : ℕ) : ℤ) = M * qq + ρ := by exact_mod_cast hdm.symm
  set c : ℤ := A - 3 * qq
  have hc : (3 * ρ + A : ℤ) = c * M := by
    simp only [c]; rw [hdmZ] at key; linear_combination key
  have hM0 : 0 < M := by omega
  have hMpos : (0 : ℤ) < M := by exact_mod_cast hM0
  have hc1 : 1 ≤ c := by
    by_contra hh; push Not at hh
    have : c * M ≤ 0 := by nlinarith
    omega
  have hc3 : c ≤ 3 := by
    by_contra hh; push Not at hh
    have : 4 * (M : ℤ) ≤ c * M := by nlinarith
    have : (A : ℤ) < M := by omega
    omega
  have hcases : c = 1 ∨ c = 2 ∨ c = 3 := by omega
  rcases hcases with h | h | h
  · rw [h] at hc
    have : 3 * ρ + A = M := by omega
    have : ρ ≤ M - ρ := by omega
    rw [min_eq_left this]; omega
  · rw [h] at hc
    have : 3 * ρ + A = 2 * M := by omega
    rcases le_total ρ (M - ρ) with h' | h'
    · rw [min_eq_left h']; omega
    · rw [min_eq_right h']; omega
  · rw [h] at hc
    exact absurd ⟨M - ρ, by omega⟩ hAnd

lemma window_one_two {p : ℕ} (hp3 : 3 ≤ p) : IsWin p 1 2 :=
  ⟨le_rfl, by omega, odd_one, by norm_num⟩

/-- Every positive leader is at most `(2^p - 2)/6`. -/
lemma leader_le_max (h87 : Theorem87) {p σ : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hodd : Odd p)
    (hL : IsLeader (2 ^ p - 1) σ) : 6 * σ ≤ 2 ^ p - 2 := by
  have hM : Odd (2 ^ p - 1) := by
    have : 2 ^ p = 2 * 2 ^ (p - 1) := by rw [← pow_succ']; congr 1; omega
    have : 1 ≤ 2 ^ (p - 1) := Nat.one_le_two_pow
    exact ⟨2 ^ (p - 1) - 1, by omega⟩
  obtain ⟨hσodd, hσ3⟩ := hL.bounds hM
  have hmod := two_pow_odd_mod_three hodd
  by_contra hh
  push Not at hh
  have h6 : 2 ^ p < 6 * σ := by
    have : 6 * σ ≠ 2 ^ p - 1 := by obtain ⟨t, ht⟩ := hσodd; omega
    have : 6 * σ ≠ 2 ^ p := by omega
    omega
  have hdel : Del p 1 2 σ := by
    refine ⟨hσodd, ?_, ?_⟩
    · unfold wT wR; norm_num
      have : ((2 ^ p : ℕ) : ℝ) < 6 * σ := by exact_mod_cast h6
      push_cast at this; linarith
    · unfold wR; norm_num
      have : (3 * σ : ℕ) < 2 ^ p := by omega
      have : ((3 * σ : ℕ) : ℝ) < ((2 ^ p : ℕ) : ℝ) := by exact_mod_cast this
      push_cast at this; linarith
  obtain ⟨b, j, hm, hd⟩ := del_maximal (window_one_two hp3) hdel
  exact ((sieve h87 hp hσodd (by omega)).1.mp hL) ⟨b, j, hm, hd⟩

lemma compl_xor {N x y : ℕ} (n : ℕ) (hN : N = 2 ^ n) (hx : x < N) (hy : y < N) :
    (N - 1 - x) ^^^ (N - 1 - y) = x ^^^ y := by
  subst hN
  apply Nat.eq_of_testBit_eq; intro t
  rw [Nat.testBit_xor, Nat.testBit_xor]
  by_cases ht : t < n
  · rw [testBit_compl hx ht, testBit_compl hy ht]
    cases x.testBit t <;> cases y.testBit t <;> rfl
  · have h1 : ∀ z : ℕ, z < 2 ^ n → z.testBit t = false := fun z hz =>
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hz (Nat.pow_le_pow_right (by norm_num) (by omega)))
    rw [h1 _ (by omega), h1 _ (by omega), h1 _ hx, h1 _ hy]

lemma odd_xor_pred {r : ℕ} (hr : Odd r) : r ^^^ (r - 1) = 2 ^ 1 - 1 := by
  obtain ⟨m, rfl⟩ := hr
  rw [show 2 * m + 1 - 1 = 2 ^ 1 * m + 0 by rw [pow_one]; omega,
    show 2 * m + 1 = 2 ^ 1 * m + 1 by ring]
  apply Nat.eq_of_testBit_eq; intro t
  rw [Nat.testBit_xor, Nat.testBit_two_pow_mul_add _ (by norm_num),
    Nat.testBit_two_pow_mul_add _ (by norm_num), Nat.testBit_two_pow_sub_one]
  split_ifs with ht
  · have : t = 0 := by omega
    subst this; simp
  · simp [ht]

/-- **The exported statement from the reflection property.** -/
theorem main_of_core (h87 : Theorem87) (hcore : ∀ p, p.Prime → Odd p → ReflectionCore p) :
    OddPrimeDegniDrisko := by
  intro p hp hodd r s hcons
  obtain ⟨hlt, hrepr, hreps, hnone⟩ := hcons
  have hp1 : 1 ≤ p := hp.one_lt.le
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    rcases Nat.lt_or_ge p 3 with h | h
    · have : p = 2 := by omega
      subst this; exact absurd hodd (by decide)
    · exact h
  have hmod := two_pow_odd_mod_three hodd
  have hN8 : 8 ≤ 2 ^ p := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hp3
  have hMsub : Odd (2 ^ p - 1) := by
    have : 2 ^ p = 2 * 2 ^ (p - 1) := by rw [← pow_succ']; congr 1; omega
    exact ⟨2 ^ (p - 1) - 1, by omega⟩
  have hMadd : Odd (2 ^ p + 1) := by
    have : 2 ^ p = 2 * 2 ^ (p - 1) := by rw [← pow_succ']; congr 1; omega
    exact ⟨2 ^ (p - 1), by omega⟩
  have hmaxL := sigmaMax_leader hodd hp3
  have hle : ∀ σ, IsLeader (2 ^ p - 1) σ → 6 * σ ≤ 2 ^ p - 2 :=
    fun σ h => leader_le_max h87 hp hp3 hodd h
  -- odd representatives come from leaders, except the constant word `1^p`
  have hodd_rep : ∀ σ, IsLeader (2 ^ p + 1) σ → 3 * σ = 2 ^ p + 1 ∨ IsLeader (2 ^ p - 1) σ := by
    intro σ hσ
    obtain ⟨hσo, hσ3⟩ := hσ.bounds hMadd
    by_cases h : 3 * σ = 2 ^ p + 1
    · exact Or.inl h
    · right
      have : 3 * σ < 2 ^ p := by
        have : 3 * σ ≠ 2 ^ p := by omega
        omega
      exact (leader_sub_iff_add h87 hp hσo this).mpr hσ
  -- uniqueness of the next representative
  have huniq : ∀ t : Rank p, IsRepresentativeRank t → t < r →
      (∀ t' : Rank p, IsRepresentativeRank t' → t < t' → t' < r → False) → s = t := by
    intro t ht htr hbet
    rcases lt_trichotomy s t with h | h | h
    · exact absurd ht (hnone t h htr)
    · exact h
    · exact (hbet s hreps h hlt).elim
  have hrep := (isRep_iff hp1 r).mp hrepr
  have hrlt := r.isLt
  rcases hrep with hr0 | ⟨hrev, hr2, hrL⟩ | ⟨hrodd, hrL⟩
  · exact absurd hlt (by rw [Fin.lt_def, hr0]; omega)
  · -- `r = 2^p - 1 - σ`: an even representative
    set σ := 2 ^ p - 1 - r.val with hσdef
    have hσle := hle σ hrL
    obtain ⟨hσo, _⟩ := hrL.bounds hMsub
    by_cases hσm : σ = (2 ^ p - 2) / 6
    · -- the next representative is the constant word `1^p`
      set t : Rank p := ⟨(2 * 2 ^ p - 1) / 3, by omega⟩
      have hfix : rot1 p t.val = t.val := by
        simp only [t, rot1]
        have : min ((2 * 2 ^ p - 1) / 3) (2 ^ p - 1 - (2 * 2 ^ p - 1) / 3) =
            2 ^ p - 1 - (2 * 2 ^ p - 1) / 3 := min_eq_right (by omega)
        rw [this]; omega
      have htrep : IsRepresentativeRank t := by
        rw [isRepresentativeRank_iff hp1]
        intro k; induction k with
        | zero => simp
        | succ k ih =>
          rw [Function.iterate_succ_apply']
          have : (rot1 p)^[k] t.val = t.val := by
            clear ih; induction k with
            | zero => simp
            | succ k ih2 => rw [Function.iterate_succ_apply', ih2, hfix]
          rw [this, hfix]
      have htr : t < r := by rw [Fin.lt_def]; simp only [t]; omega
      have hs : s = t := by
        apply huniq t htrep htr
        intro t' ht' h1 h2
        rw [Fin.lt_def] at h1 h2
        rcases (isRep_iff hp1 t').mp ht' with h0 | ⟨_, _, hL'⟩ | ⟨ho', hL'⟩
        · simp only [t] at h1; omega
        · have := hle _ hL'; simp only [t] at h1; omega
        · rcases hodd_rep _ hL' with h3 | hL''
          · simp only [t] at h1; omega
          · have := hle _ hL''; simp only [t] at h1; omega
      subst hs
      apply Or.inr
      apply differInOneBit_of_xor r t (e := p - 1) (by omega) (by omega)
      have hx1 : r.val = 2 ^ p - 1 - σ := by omega
      have hx2 : t.val = 2 ^ p - 1 - (2 ^ p - 2) / 3 := by simp only [t]; omega
      rw [hx1, hx2, compl_xor p rfl (by omega) (by omega), hσm]
      have := reflect_xor (σ := (2 ^ p - 2) / 6) (τ := (2 ^ p - 2) / 3 + 1) (e := p - 2) (c := 1)
        odd_one (by
          have : 2 ^ p = 4 * 2 ^ (p - 2) := by
            rw [show 4 = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
          omega) (by
          have : 2 ^ p = 4 * 2 ^ (p - 2) := by
            rw [show 4 = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
          omega) (by
          have : 2 ^ p = 4 * 2 ^ (p - 2) := by
            rw [show 4 = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
          omega)
      rw [Nat.add_sub_cancel, show p - 2 + 1 = p - 1 by omega] at this
      exact this
    · -- the next leader `τ` gives the next representative `2^p - τ`
      classical
      have hexτ : ∃ τ, σ < τ ∧ IsLeader (2 ^ p - 1) τ := ⟨_, by omega, hmaxL⟩
      set τ := Nat.find hexτ
      obtain ⟨hστ, hτL⟩ := Nat.find_spec hexτ
      have hτmin : ∀ t, σ < t → t < τ → ¬ IsLeader (2 ^ p - 1) t :=
        fun t h1 h2 h3 => Nat.find_min hexτ h2 ⟨h1, h3⟩
      have hτle := hle τ hτL
      obtain ⟨hτo, _⟩ := hτL.bounds hMsub
      have hτ2 : σ + 2 ≤ τ := by obtain ⟨a, ha⟩ := hσo; obtain ⟨b, hb⟩ := hτo; omega
      set t : Rank p := ⟨2 ^ p - τ, by omega⟩
      have htrep : IsRepresentativeRank t := by
        rw [isRep_iff hp1]
        right; right
        refine ⟨⟨(2 ^ p - τ - 1) / 2, by
          have : 2 ^ p = 2 * 2 ^ (p - 1) := by rw [← pow_succ']; congr 1; omega
          obtain ⟨b, hb⟩ := hτo; simp only [t]; omega⟩, ?_⟩
        simp only [t]
        rw [show 2 ^ p - (2 ^ p - τ) = τ by omega]
        exact (leader_sub_iff_add h87 hp hτo (by omega)).mp hτL
      have htr : t < r := by rw [Fin.lt_def]; simp only [t]; omega
      have hs : s = t := by
        apply huniq t htrep htr
        intro t' ht' h1 h2
        rw [Fin.lt_def] at h1 h2
        simp only [t] at h1
        rcases (isRep_iff hp1 t').mp ht' with h0 | ⟨_, _, hL'⟩ | ⟨ho', hL'⟩
        · omega
        · exact hτmin _ (by omega) (by omega) hL'
        · rcases hodd_rep _ hL' with h3 | hL''
          · omega
          · exact hτmin _ (by omega) (by omega) hL''
      subst hs
      apply Or.inr
      obtain ⟨e, c, hc, hsum, hlo, hσlt⟩ := hcore p hp hodd σ τ hrL hτL hστ hτmin
      have he : e + 1 ≤ p := by
        by_contra hh
        have : 2 ^ p ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) (by omega)
        have : 2 ^ e ≤ c * 2 ^ e := Nat.le_mul_of_pos_left _ hc.pos
        omega
      apply differInOneBit_of_xor r t (e := e + 1) (by omega) he
      have hx1 : r.val = 2 ^ p - 1 - σ := by omega
      have hx2 : t.val = 2 ^ p - 1 - (τ - 1) := by simp only [t]; omega
      rw [hx1, hx2, compl_xor p rfl (by omega) (by omega)]
      exact reflect_xor hc hsum hlo hσlt
  · -- `r = 2^p - σ`: an odd representative
    set σ := 2 ^ p - r.val with hσdef
    rcases hodd_rep σ hrL with h3 | hσL
    · -- `r` is the constant word `1^p`, followed by `0^p`
      set t : Rank p := ⟨0, by positivity⟩
      have htrep : IsRepresentativeRank t := by
        rw [isRep_iff hp1]; left; rfl
      have htr : t < r := by rw [Fin.lt_def]; simp only [t]; omega
      have hs : s = t := by
        apply huniq t htrep htr
        intro t' ht' h1 h2
        rw [Fin.lt_def] at h1 h2
        rcases (isRep_iff hp1 t').mp ht' with h0 | ⟨_, _, hL'⟩ | ⟨ho', hL'⟩
        · simp only [t] at h1; omega
        · have := hle _ hL'; omega
        · rcases hodd_rep _ hL' with h3' | hL''
          · omega
          · have := hle _ hL''; omega
      subst hs
      apply Or.inl
      have hfix : rot1 p r.val = r.val := by
        unfold rot1
        have : min r.val (2 ^ p - 1 - r.val) = 2 ^ p - 1 - r.val := min_eq_right (by omega)
        rw [this]; omega
      refine ⟨fun i => ?_, fun i => grayWord_zero hp1 i⟩
      rw [grayWord_const_of_rot1_fixed hp1 r hfix i]
      by_contra hb
      rw [Bool.not_eq_true] at hb
      have hall : grayWord r = grayWord (⟨0, by positivity⟩ : Rank p) := by
        funext i'
        rw [grayWord_const_of_rot1_fixed hp1 r hfix i', hb, grayWord_zero hp1]
      have h0 : r.val = 0 := congrArg Fin.val (grayWord_injective p hall)
      obtain ⟨m, hm⟩ := hrodd; omega
    · -- the paired even representative `r - 1`
      set t : Rank p := ⟨r.val - 1, by omega⟩
      obtain ⟨hσo, hσ3⟩ := hσL.bounds hMsub
      have htrep : IsRepresentativeRank t := by
        rw [isRep_iff hp1]
        right; left
        simp only [t]
        refine ⟨?_, by omega, ?_⟩
        · obtain ⟨m, hm⟩ := hrodd; exact ⟨m, by omega⟩
        · rw [show 2 ^ p - 1 - (r.val - 1) = σ by omega]; exact hσL
      have htr : t < r := by rw [Fin.lt_def]; simp only [t]; omega
      have hs : s = t := by
        apply huniq t htrep htr
        intro t' _ h1 h2
        rw [Fin.lt_def] at h1 h2; simp only [t] at h1; omega
      subst hs
      apply Or.inr
      apply differInOneBit_of_xor r t (e := 1) le_rfl hp1
      simp only [t]
      exact odd_xor_pred hrodd

end GrayNecklaces
