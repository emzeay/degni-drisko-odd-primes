module

public import GrayNecklaces.WingContradiction

/-!
# The reflection property for consecutive leaders
-/

@[expose] public section

namespace GrayNecklaces

open Tiozzo

section

variable {p σ τ e c : ℕ} (hc : Consec p σ τ) (hs : Split p σ τ e c) (h87 : Theorem87)
  (h9 : TuningNesting) (h4 : σ + 4 ≤ τ)
include hc hs h87 h9 h4

/-- There is no large maximal window between consecutive leaders. -/
theorem no_large : ¬ ∃ b j, IsLarge p σ τ e b j := by
  classical
  rintro ⟨b0, j0, hl0⟩
  obtain ⟨w, hwodd, hw3, hmw', hmw, _⟩ := run_bound hc hs h87 h4
  set m := c * 2 ^ e with hmdef
  -- a large center is never `m`
  have hne : ∀ b j, IsLarge p σ τ e b j → b * 2 ^ (p - j) ≠ m := by
    rintro b j ⟨hm, _, _, _, he⟩ heq
    obtain ⟨β, hβ⟩ := hm.1.2.2.1
    have : 2 ^ e = 2 ^ (p - j) * 2 ^ (e - (p - j)) := by rw [← pow_add]; congr 1; omega
    rw [hmdef, this] at heq
    have hq : 0 < 2 ^ (p - j) := by positivity
    have : b = c * 2 ^ (e - (p - j)) := by
      have : b * 2 ^ (p - j) = (c * 2 ^ (e - (p - j))) * 2 ^ (p - j) := by rw [heq]; ring
      exact Nat.eq_of_mul_eq_mul_right hq this
    have hev : Even (c * 2 ^ (e - (p - j))) :=
      (Nat.even_pow.mpr ⟨even_two, by omega⟩).mul_left c
    rw [← this, hβ] at hev
    exact (Nat.not_even_iff_odd.mpr ⟨β, rfl⟩) hev
  by_cases hright : ∃ b j, IsLarge p σ τ e b j ∧ m < b * 2 ^ (p - j)
  · -- the first large window to the right
    have hex : ∃ d, ∃ b j, IsLarge p σ τ e b j ∧ b * 2 ^ (p - j) = m + d := by
      obtain ⟨b, j, hl, hlt⟩ := hright
      exact ⟨b * 2 ^ (p - j) - m, b, j, hl, by omega⟩
    set dmin := Nat.find hex
    obtain ⟨bw, jw, hlw, hcw⟩ := Nat.find_spec hex
    have hdpos : m < bw * 2 ^ (p - jw) := by
      rcases Nat.eq_zero_or_pos dmin with h0 | h0
      · have h0' : Nat.find hex = 0 := h0
        exact absurd (by omega) (hne bw jw hlw)
      · omega
    apply wing_contra hc hs h87 h9 h4 hwodd hw3 hmw' hmw hlw 1 (Or.inl ⟨rfl, hdpos⟩)
    intro b j hl hnot ⟨h1, h2⟩
    rw [min_eq_left hdpos.le] at h1
    rw [max_eq_right hdpos.le] at h2
    have := Nat.find_min' hex (show ∃ b' j', IsLarge p σ τ e b' j' ∧
      b' * 2 ^ (p - j') = m + (b * 2 ^ (p - j) - m) from ⟨b, j, hl, by omega⟩)
    omega
  · -- every large window is to the left: take the first one
    push Not at hright
    have hex : ∃ d, ∃ b j, IsLarge p σ τ e b j ∧ b * 2 ^ (p - j) + d = m := by
      have hlt : b0 * 2 ^ (p - j0) < m := by
        have := hright b0 j0 hl0; have := hne b0 j0 hl0; omega
      exact ⟨m - b0 * 2 ^ (p - j0), b0, j0, hl0, by omega⟩
    set dmin := Nat.find hex
    obtain ⟨bw, jw, hlw, hcw⟩ := Nat.find_spec hex
    have hdpos : bw * 2 ^ (p - jw) < m := by
      have := hright bw jw hlw; have := hne bw jw hlw; omega
    apply wing_contra hc hs h87 h9 h4 hwodd hw3 hmw' hmw hlw (-1) (Or.inr ⟨rfl, hdpos⟩)
    intro b j hl hnot ⟨h1, h2⟩
    rw [min_eq_right hdpos.le] at h1
    rw [max_eq_left hdpos.le] at h2
    have := Nat.find_min' hex (show ∃ b' j', IsLarge p σ τ e b' j' ∧
      b' * 2 ^ (p - j') + (m - b * 2 ^ (p - j)) = m from ⟨b, j, hl, by omega⟩)
    omega

end

/-- **The reflection property** at every odd prime length. -/
theorem reflectionCore (h87 : Theorem87) (h9 : TuningNesting) {p : ℕ} (hp : p.Prime)
    (hodd : Odd p) : ReflectionCore p := by
  intro σ τ hσ hτ hlt hnone
  have hc : Consec p σ τ := ⟨hp, hodd, hσ, hτ, hlt, hnone⟩
  have hσo := hc.σ_odd
  have hτo := hc.τ_odd
  have hτ6 := hc.τ_le h87
  have h2 : σ + 1 < τ := by obtain ⟨a, ha⟩ := hσo; obtain ⟨b, hb⟩ := hτo; omega
  obtain ⟨e, c, hep, h1, h2', h3, h4', hco, hmax⟩ := exists_split h2 (by omega : τ < 2 ^ p)
  have hs : Split p σ τ e c := ⟨hep, h1, h2', h3, h4', hco, hmax⟩
  have hc1 : 1 ≤ c := hco.pos
  have hlo : c * 2 ^ e ≤ σ + 2 ^ e := by
    have : c * 2 ^ e = (c - 1) * 2 ^ e + 2 ^ e := by
      rw [Nat.sub_mul, one_mul]; have : 2 ^ e ≤ c * 2 ^ e := Nat.le_mul_of_pos_left _ hc1
      omega
    omega
  refine ⟨e, c, hco, ?_, hlo, h1⟩
  by_cases h4 : σ + 4 ≤ τ
  · apply reflection_of_no_large hc hs h87 h4
    intro b j hm hcen1 hcen2 hfin
    by_contra hh
    push Not at hh
    exact no_large hc hs h87 h9 h4 ⟨b, j, hm, hcen1, hcen2, hh, hfin⟩
  · -- `τ = σ + 2`: the split is `σ + 1`
    have : τ = σ + 2 := by obtain ⟨a, ha⟩ := hσo; obtain ⟨b, hb⟩ := hτo; omega
    omega

end GrayNecklaces
