module

public import GrayNecklaces.RunBound

/-!
# Reflection when every finer window has scale below `B`
-/

@[expose] public section

namespace GrayNecklaces

open Tiozzo

section

variable {p σ τ e c : ℕ} (hc : Consec p σ τ) (hs : Split p σ τ e c) (h87 : Theorem87)
  (h9 : TuningNesting) (h4 : σ + 4 ≤ τ)
include hc hs h87 h9 h4

omit h9 in
/-- The reflection of a deletion by a window of scale below `B` about `m`. -/
lemma reflect_del {w b j s : ℕ} (hw3 : 3 * w ≤ 2 ^ e + 1) (hmw : τ ≤ c * 2 ^ e + w)
    (hmw' : c * 2 ^ e ≤ σ + w) (hm : IsMaxWin p b j) (hd : Del p b j s) (h1 : σ < s) (h2 : s < τ)
    (hfin : p - j < e) (hsmall : p - j < p - e) :
    ∃ b', IsWin p b' j ∧ Del p b' j (2 * (c * 2 ^ e) - s) := by
  obtain ⟨hcen1, hcen2, hle, _, h5⟩ := classify hc hs h87 hm hd h1 h2
  have h5 := h5 hfin
  have hj : 1 ≤ j := by have := hm.1.1; omega
  have hjp := hm.1.2.1
  have hep := hs.hep
  have h6 := hs.six_m hc h87
  have h8 := hs.eight_Q hc h87
  have hc1 : 1 ≤ c := hs.hodd.pos
  obtain ⟨β, hβ⟩ := hm.1.2.2.1
  obtain ⟨γ, hγ⟩ := hs.hodd
  -- powers of two as variables
  obtain ⟨q, hq⟩ : ∃ q : ℕ, 2 ^ (p - j) = q := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : ℕ, 2 ^ e = Q := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℕ, 2 ^ j = D := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 2 ^ p = N := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : ℕ, 2 ^ (e - (p - j) - 1) = Y := ⟨_, rfl⟩
  have hqR : (2 : ℝ) ^ (p - j) = q := by rw [← hq]; push_cast; ring
  rw [hq] at hcen1 hcen2
  rw [hqR] at h5
  rw [hQ] at hw3 hmw hmw' h6 h8
  have hDq : D * q = N := by rw [← hD, ← hq, ← hN, ← pow_add]; congr 1; omega
  have hQq : Q = 2 * q * Y := by
    rw [← hQ, ← hq, ← hY, ← pow_succ', ← pow_add]; congr 1; omega
  have hDQ : D = 2 * Q * 2 ^ (j - e - 1) := by
    rw [← hD, ← hQ, ← pow_succ', ← pow_add]; congr 1; omega
  have hq2 : 2 ≤ q := by rw [← hq]; exact two_le_two_pow (by omega)
  have hY1 : 1 ≤ Y := by rw [← hY]; exact Nat.one_le_two_pow
  have hQ2 : 2 * q ≤ Q := by rw [hQq]; exact Nat.le_mul_of_pos_right _ hY1
  rw [hN] at h6 h8
  -- the products as atoms
  have hm_eq : c * Q = q * (2 * c * Y) := by rw [hQq]; ring
  have hmQ : Q ≤ c * Q := Nat.le_mul_of_pos_left _ hc1
  have hwm : w < c * Q := by omega
  have hcenm : b * q < 2 * (c * Q) := by omega
  have hb4 : b < 4 * (c * Y) := by
    have : b * q < (4 * (c * Y)) * q := by rw [hm_eq] at hcenm; nlinarith
    exact Nat.lt_of_mul_lt_mul_right this
  set b' := 4 * (c * Y) - b with hb'def
  have hb'q : b' * q = 2 * (c * Q) - b * q := by
    rw [hb'def, Nat.sub_mul, hm_eq]; ring_nf
  have hb'odd : Odd b' := ⟨2 * (c * Y) - β - 1, by rw [hb'def]; rw [hβ] at hb4 ⊢; omega⟩
  have hb'3 : 3 * b' < D := by
    have : 3 * b' * q < D * q := by
      rw [hDq, mul_assoc, hb'q]; omega
    exact Nat.lt_of_mul_lt_mul_right this
  refine ⟨b', ⟨hm.1.1, hjp, hb'odd, by rw [hD]; exact hb'3⟩, ?_⟩
  -- deletion of the reflected point
  have hdel := (del_iff_nat (a := b) hj hjp.le).mp hd
  rw [hq, hD] at hdel
  apply (del_iff_nat (a := b') hj hjp.le).mpr
  rw [hq, hD, hQ]
  have hsm : s ≤ 2 * (c * Q) := by omega
  refine ⟨?_, ?_⟩
  · obtain ⟨r, hr⟩ := hdel.1
    exact ⟨c * Q - r - 1, by omega⟩
  · set E := ((s : ℤ) - ((b * q : ℕ) : ℤ)).natAbs with hE
    have hE' : (((2 * (c * Q) - s : ℕ) : ℤ) - ((b' * q : ℕ) : ℤ)).natAbs = E := by
      rw [hE, hb'q]
      have : (((2 * (c * Q) - s : ℕ) : ℤ) - ((2 * (c * Q) - b * q : ℕ) : ℤ)) =
          -((s : ℤ) - ((b * q : ℕ) : ℤ)) := by
        push_cast [hsm, hcenm.le]; ring
      rw [this, Int.natAbs_neg]
    rw [hE']
    have hEdel : E * (D - 1) < b * q := hdel.2
    have h5' : 5 * E < q := by
      have : (5 * E : ℝ) < q := by
        have : (E : ℝ) = |(s : ℝ) - b * q| := by
          rw [hE, Nat.cast_natAbs, Int.cast_abs]; push_cast; ring_nf
        rw [this]; exact h5
      exact_mod_cast this
    by_contra hh
    push Not at hh
    rw [hb'q] at hh
    -- `|E D - m| < Q` contradicts parity of the multiples of `Q`
    have hD1 : 1 ≤ D := by rw [← hD]; exact Nat.one_le_two_pow
    have hED : E * D = E * (D - 1) + E := by
      rw [Nat.mul_sub, mul_one]; have : E ≤ E * D := Nat.le_mul_of_pos_right _ (by omega)
      omega
    have hdistZ := dist_odd_mult (q := (Q : ℤ)) (X := ((E * 2 ^ (j - e - 1) : ℕ) : ℤ)) (β := γ)
      (by positivity)
    have e1 : 2 * (Q : ℤ) * ((E * 2 ^ (j - e - 1) : ℕ) : ℤ) = ((E * D : ℕ) : ℤ) := by
      rw [hDQ]; push_cast; ring
    have e2 : (Q : ℤ) * (2 * γ + 1) = ((c * Q : ℕ) : ℤ) := by rw [hγ]; push_cast; ring
    rw [e1, e2] at hdistZ
    generalize E * D = X at hED hdistZ
    generalize E * (D - 1) = Z at hED hEdel hh
    generalize b * q = C at hcen1 hcen2 hcenm hEdel hh
    generalize c * Q = m at *
    rcases le_abs.mp hdistZ with h | h <;> omega

omit h9 in
/-- **Reflection.**  If no maximal window centered between the leaders has a scale in
`[B, Q)`, the leaders are mirror images about `m`. -/
theorem reflection_of_no_large
    (hnl : ∀ b j, IsMaxWin p b j → σ < b * 2 ^ (p - j) → b * 2 ^ (p - j) < τ → p - j < e →
      p - j < p - e) :
    σ + τ = 2 * (c * 2 ^ e) := by
  obtain ⟨w, hwodd, hw3, hmw', hmw, hRw⟩ := run_bound hc hs h87 h4
  have h6 := hs.six_m hc h87
  have h8 := hs.eight_Q hc h87
  have hc1 : 1 ≤ c := hs.hodd.pos
  have hmQ : 2 ^ e ≤ c * 2 ^ e := Nat.le_mul_of_pos_left _ hc1
  have he1 := hs.e_pos hc h4
  have hmev : Even (c * 2 ^ e) := (Nat.even_pow.mpr ⟨even_two, by omega⟩).mul_left c
  have hep := hs.hep
  -- reflections of deleted points are not leaders
  have key : ∀ s, Odd s → σ < s → s < τ → ¬ IsLeader (2 ^ p - 1) (2 * (c * 2 ^ e) - s) := by
    intro s hso h1 h2
    have hsm : s ≤ 2 * (c * 2 ^ e) := by omega
    have hodd' : Odd (2 * (c * 2 ^ e) - s) := by
      obtain ⟨r, hr⟩ := hso; exact ⟨c * 2 ^ e - r - 1, by omega⟩
    have h3 : 3 * (2 * (c * 2 ^ e) - s) < 2 ^ p := by omega
    obtain ⟨b, j, hm, hd⟩ := hc.gap_deleted h87 hso h1 h2
    obtain ⟨hcen1, hcen2, hle, heq, _⟩ := classify hc hs h87 hm hd h1 h2
    rcases eq_or_lt_of_le hle with he | he
    · obtain ⟨hbc, hjk⟩ := heq he
      rw [hbc, hjk] at hd hm
      apply hc.not_leader_of_del h87 hm.1 _ h3
      have hdel := (del_iff (j := p - e) (by omega) (by omega)).mp hd
      rw [show p - (p - e) = e by omega] at hdel
      apply (del_iff (j := p - e) (by omega) (by omega)).mpr
      rw [show p - (p - e) = e by omega]
      refine ⟨hodd', ?_⟩
      have : ((2 * (c * 2 ^ e) - s : ℕ) : ℝ) - c * 2 ^ e = -((s : ℝ) - c * 2 ^ e) := by
        push_cast [hsm]; ring
      rw [this, abs_neg]; exact hdel.2
    · obtain ⟨b', hw', hd'⟩ := reflect_del hc hs h87 h4 hw3 hmw hmw' hm hd h1 h2 he
        (hnl b j hm hcen1 hcen2 he)
      exact hc.not_leader_of_del h87 hw' hd' h3
  rcases lt_trichotomy (σ + τ) (2 * (c * 2 ^ e)) with hlt | heq | hgt
  · exfalso
    have := key (2 * (c * 2 ^ e) - τ) (by
        obtain ⟨r, hr⟩ := hc.τ_odd; exact ⟨c * 2 ^ e - r - 1, by have := hs.h2; omega⟩)
      (by omega) (by have := hs.h2; omega)
    rw [show 2 * (c * 2 ^ e) - (2 * (c * 2 ^ e) - τ) = τ by have := hs.h2; omega] at this
    exact this hc.hτ
  · exact heq
  · exfalso
    have := key (2 * (c * 2 ^ e) - σ) (by
        obtain ⟨r, hr⟩ := hc.σ_odd; exact ⟨c * 2 ^ e - r - 1, by have := hs.h1; omega⟩)
      (by have := hs.h1; omega) (by omega)
    rw [show 2 * (c * 2 ^ e) - (2 * (c * 2 ^ e) - σ) = σ by have := hs.h1; omega] at this
    exact this hc.hσ

end

end GrayNecklaces
