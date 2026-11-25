module

public import GrayNecklaces.Actual

/-!
# Maximal windows and the sieve characterization of leaders
-/

@[expose] public section

namespace GrayNecklaces

open Tiozzo

/-- A window not properly contained in another admissible window at length `p`. -/
def IsMaxWin (p b j : ℕ) : Prop :=
  IsWin p b j ∧ ∀ b' j', IsWin p b' j' → WinLE b j b' j' → b' = b ∧ j' = j

theorem exists_maxWin {p b j : ℕ} (h : IsWin p b j) :
    ∃ b' j', IsMaxWin p b' j' ∧ WinLE b j b' j' := by
  classical
  have hex : ∃ j', ∃ b', IsWin p b' j' ∧ WinLE b j b' j' := ⟨j, b, h, WinLE.refl b j⟩
  set j' := Nat.find hex
  obtain ⟨b', hw', hle'⟩ := Nat.find_spec hex
  refine ⟨b', j', ⟨hw', fun b'' j'' hw'' hle'' => ?_⟩, hle'⟩
  have hmin : j' ≤ j'' := Nat.find_min' hex ⟨b'', hw'', hle'.trans hle''⟩
  rcases hle''.le_exp hw'.2.2.1.pos hw'.1 (by have := hw''.1; omega) with h1 | h1
  · omega
  · exact ⟨h1.2, h1.1⟩

theorem IsMaxWin.actual (h87 : Theorem87) {p b j : ℕ} (hm : IsMaxWin p b j) : IsActual b j := by
  obtain ⟨a, k, hkj, hact, hle⟩ := exists_actual h87 hm.1.1 hm.1.2.2.1 hm.1.2.2.2
  have hw : IsWin p a k := ⟨hact.1, by have := hm.1.2.1; omega, hact.2.1, hact.2.2.1⟩
  obtain ⟨rfl, rfl⟩ := hm.2 a k hw hle
  exact hact

theorem IsMaxWin.good (h87 : Theorem87) {p b j : ℕ} (hm : IsMaxWin p b j) : GoodWin p b j :=
  (hm.actual h87).good hm.1.2.1

/-- Distinct maximal windows have disjoint interiors. -/
theorem IsMaxWin.eq_of_overlap (h87 : Theorem87) (h9 : TuningNesting) {p b j b' j' : ℕ}
    (hm : IsMaxWin p b j) (hm' : IsMaxWin p b' j') {y : ℝ} (h1 : wT b j < y) (h2 : y < wR b j)
    (h1' : wT b' j' < y) (h2' : y < wR b' j') : b' = b ∧ j' = j := by
  rcases actual_nested h9 (hm.actual h87) (hm'.actual h87) h1 h2 h1' h2' with h | h
  · exact hm.2 b' j' hm'.1 h
  · obtain ⟨e1, e2⟩ := hm'.2 b j hm.1 h
    exact ⟨e1.symm, e2.symm⟩

/-- The right endpoint of a maximal window is never interior to another admissible window. -/
theorem IsMaxWin.not_interior (h87 : Theorem87) (h9 : TuningNesting) {p a k u d : ℕ}
    (hm : IsMaxWin p a k) (hw : IsWin p u d) (h1 : wT u d < wR a k) (h2 : wR a k < wR u d) :
    False := by
  obtain ⟨u', d', hm', hle⟩ := exists_maxWin hw
  have hT : wT a k < wR a k := by
    have := wT_lt_center (b := a) (j := k) hm.1.2.2.1.pos (by have := hm.1.1; omega)
    have := center_lt_wR (b := a) (j := k) hm.1.2.2.1.pos (by have := hm.1.1; omega)
    linarith
  set y := (max (wT a k) (wT u' d') + wR a k) / 2
  have hmx : max (wT a k) (wT u' d') < wR a k :=
    max_lt hT (lt_of_le_of_lt hle.1 h1)
  have hy1 : wT a k < y := by
    have := le_max_left (wT a k) (wT u' d'); simp only [y]; linarith
  have hy2 : y < wR a k := by simp only [y]; linarith
  have hy1' : wT u' d' < y := by
    have := le_max_right (wT a k) (wT u' d'); simp only [y]; linarith
  have hy2' : y < wR u' d' := by linarith [hle.2]
  obtain ⟨rfl, rfl⟩ := hm.eq_of_overlap h87 h9 hm' hy1 hy2 hy1' hy2'
  linarith [hle.2]

/-- Deletion by any admissible window implies deletion by a maximal one. -/
theorem del_maximal {p b j s : ℕ} (hw : IsWin p b j) (hd : Del p b j s) :
    ∃ b' j', IsMaxWin p b' j' ∧ Del p b' j' s := by
  obtain ⟨b', j', hm, hle⟩ := exists_maxWin hw
  exact ⟨b', j', hm, hd.mono hle⟩

/-- **The sieve.**  For odd `s` with `3s < 2^p`, being a leader modulo `2^p - 1`, being a leader
modulo `2^p + 1`, and surviving every maximal window are equivalent. -/
theorem sieve (h87 : Theorem87) {p s : ℕ} (hp : p.Prime) (hs : Odd s) (h3 : 3 * s < 2 ^ p) :
    (IsLeader (2 ^ p - 1) s ↔ ¬ ∃ b j, IsMaxWin p b j ∧ Del p b j s) ∧
    (IsLeader (2 ^ p + 1) s ↔ ¬ ∃ b j, IsMaxWin p b j ∧ Del p b j s) := by
  have hp2 := hp.two_le
  have key : ∀ M, (M = 2 ^ p - 1 ∨ M = 2 ^ p + 1) →
      (IsLeader M s ↔ ¬ ∃ b j, IsMaxWin p b j ∧ Del p b j s) := by
    intro M hM
    constructor
    · rintro hL ⟨b, j, hm, hd⟩
      have := not_leader_of_del hp (hm.good h87) hd
      rcases hM with rfl | rfl
      · exact this.1 hL
      · exact this.2 hL
    · intro hnd
      by_contra hnl
      obtain ⟨b, j, hw, he⟩ := enlDel_of_not_leader hp2 hs h3 hM hnl
      obtain ⟨b', j', hm, hle⟩ := exists_maxWin hw
      exact hnd ⟨b', j', hm, del_of_enlDel_good (hm.good h87) (he.mono hle)⟩
  exact ⟨key _ (Or.inl rfl), key _ (Or.inr rfl)⟩

theorem leader_sub_iff_add (h87 : Theorem87) {p s : ℕ} (hp : p.Prime) (hs : Odd s)
    (h3 : 3 * s < 2 ^ p) : IsLeader (2 ^ p - 1) s ↔ IsLeader (2 ^ p + 1) s := by
  rw [(sieve h87 hp hs h3).1, (sieve h87 hp hs h3).2]

end GrayNecklaces
