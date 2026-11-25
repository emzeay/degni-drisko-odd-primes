module

public import GrayNecklaces.Reflection

/-!
# A mask survivor between the central and the first large window is a leader
-/

@[expose] public section

namespace GrayNecklaces

open Tiozzo

/-- A large maximal window: centered between the leaders with scale in `[B, Q)`. -/
def IsLarge (p σ τ e b j : ℕ) : Prop :=
  IsMaxWin p b j ∧ σ < b * 2 ^ (p - j) ∧ b * 2 ^ (p - j) < τ ∧ p - e ≤ p - j ∧ p - j < e

section

variable {p σ τ e c : ℕ} (hc : Consec p σ τ) (hs : Split p σ τ e c) (h87 : Theorem87)
  (h9 : TuningNesting) (h4 : σ + 4 ≤ τ)
include hc hs h87 h9 h4

omit h9 h4 in
/-- **Frozen radius.**  A window of scale `t < B` centered near `m` deletes only points within
`a t / B` of its center. -/
lemma frozen {w b j s : ℕ} (hw3 : 3 * w ≤ 2 ^ e + 1) (hmw : τ ≤ c * 2 ^ e + w)
    (_hmw' : c * 2 ^ e ≤ σ + w) (hm : IsMaxWin p b j) (hd : Del p b j s) (h1 : σ < s) (h2 : s < τ)
    (hsmall : p - j < p - e) (hBQ : 2 * 2 ^ (p - e) ≤ 2 ^ e) :
    2 ^ (p - e) * ((s : ℤ) - (b * 2 ^ (p - j) : ℕ)).natAbs < c * 2 ^ (p - j) := by
  obtain ⟨hcen1, hcen2, hle, _, _⟩ := classify hc hs h87 hm hd h1 h2
  have hj : 1 ≤ j := by have := hm.1.1; omega
  have hjp := hm.1.2.1
  have hep := hs.hep
  obtain ⟨hk3, h6⟩ := hs.k_ge hc h87
  have hdel := (del_iff_nat hj hjp.le).mp hd
  obtain ⟨t, ht⟩ : ∃ t : ℕ, 2 ^ (p - j) = t := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℕ, 2 ^ (p - e) = B := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : ℕ, 2 ^ e = Q := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℕ, 2 ^ j = D := ⟨_, rfl⟩
  obtain ⟨P', hP'⟩ : ∃ P' : ℕ, 2 ^ (j - e) = P' := ⟨_, rfl⟩
  rw [ht, hD] at hdel
  rw [ht] at hcen1 hcen2 ⊢
  rw [hB] at h6 hBQ ⊢
  rw [hQ] at hw3 hmw hBQ
  have hBt : B = P' * t := by rw [← hB, ← hP', ← ht, ← pow_add]; congr 1; omega
  have hDQ : D = P' * Q := by rw [← hD, ← hP', ← hQ, ← pow_add]; congr 1; omega
  have hP'2 : 2 ≤ P' := by rw [← hP']; exact two_le_two_pow (by omega)
  have ht1 : 1 ≤ t := by rw [← ht]; exact Nat.one_le_two_pow
  have hc1 : 1 ≤ c := hs.hodd.pos
  obtain ⟨γ, hγ⟩ := hs.hodd
  set x := ((s : ℤ) - ((b * t : ℕ) : ℤ)).natAbs with hx
  have hdel2 : x * (D - 1) < b * t := hdel.2
  -- `x < (c+1) t / B`, i.e. `P' x ≤ c`
  have hPx : P' * x ≤ c := by
    by_contra hh
    push Not at hh
    -- then `x (D - 1) ≥ b t`
    have hcen : b * t ≤ c * Q + w := by omega
    have hD1 : D - 1 = P' * Q - 1 := by rw [hDQ]
    have hxP : c + 1 ≤ P' * x := hh
    -- `(c+1)(P'Q - 1) > P' (cQ + w)`
    have hbig : P' * (c * Q + w) < (c + 1) * (P' * Q - 1) := by
      have ha : 3 * (P' * w) ≤ P' * Q + P' := by
        have := Nat.mul_le_mul_left P' hw3; linarith
      have hb : 6 * c < P' * t := by rw [← hBt]; exact h6
      have hc' : 2 * (P' * t) ≤ Q := by rw [← hBt]; exact hBQ
      have hd : 2 * Q ≤ P' * Q := Nat.mul_le_mul_right _ hP'2
      have hQ8 : 8 ≤ Q := by
        have : 4 ≤ B := by rw [← hB]; calc 4 = 2 ^ 2 := by norm_num
                                            _ ≤ 2 ^ (p - e) := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      have he' : 8 * P' ≤ P' * Q := by have := Nat.mul_le_mul_left P' hQ8; linarith
      have e1 : P' * (c * Q + w) = c * (P' * Q) + P' * w := by ring
      have e2 : (c + 1) * (P' * Q - 1) = c * (P' * Q) + P' * Q - (c + 1) := by
        rw [Nat.add_mul, one_mul, Nat.mul_sub, mul_one]
        have : c ≤ c * (P' * Q) := Nat.le_mul_of_pos_right _ (by omega)
        omega
      rw [e1, e2]
      generalize c * (P' * Q) = Z at *
      omega
    have h1 : (c + 1) * (P' * Q - 1) ≤ x * (P' * Q - 1) * P' := by
      calc (c + 1) * (P' * Q - 1) ≤ (P' * x) * (P' * Q - 1) := Nat.mul_le_mul_right _ hxP
        _ = x * (P' * Q - 1) * P' := by ring
    have h2 : x * (P' * Q - 1) * P' < b * t * P' := by
      have := Nat.mul_lt_mul_of_pos_right hdel2 (show 0 < P' by omega)
      rwa [hD1] at this
    have h3 : b * t * P' ≤ (c * Q + w) * P' := Nat.mul_le_mul_right _ hcen
    have h4 : (c * Q + w) * P' = P' * (c * Q + w) := by ring
    omega
  -- parity: `P' x ≠ c`
  have hne : P' * x ≠ c := by
    intro he
    have : Even (P' * x) := by
      rw [← hP']; exact (Nat.even_pow.mpr ⟨even_two, by omega⟩).mul_right x
    rw [he] at this; exact (Nat.not_even_iff_odd.mpr ⟨γ, hγ⟩) this
  have : P' * x < c := lt_of_le_of_ne hPx hne
  calc B * x = t * (P' * x) := by rw [hBt]; ring
    _ < t * c := Nat.mul_lt_mul_of_pos_left this (by omega)
    _ = c * t := by ring

end

end GrayNecklaces
