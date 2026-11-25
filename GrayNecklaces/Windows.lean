module

public import GrayNecklaces.Basic

/-!
# Windows and deletion intervals

For a reduced dyadic `b/2^j` the closed window is `[wT b j, wR b j]` with
`wR b j = b/(2^j-1)` and `wT b j = wR b j * (1 - 2/2^j)`.  An odd rank `s` at length `p` is
deleted by the window when `2^p * wT < s < 2^p * wR`.

This file defines the windows, the two deletion radii and containment of windows, and proves
the interval identities used by the sieve in `GrayNecklaces/Sieve.lean`.
-/

@[expose] public section

namespace GrayNecklaces

/-- The admissible windows at length `p`: reduced dyadics `b/2^j` in `(0,1/3)`, `2 ≤ j < p`. -/
def IsWin (p b j : ℕ) : Prop := 2 ≤ j ∧ j < p ∧ Odd b ∧ 3 * b < 2 ^ j

/-- Right endpoint `b/(2^j - 1)`. -/
noncomputable def wR (b j : ℕ) : ℝ := b / ((2 : ℝ) ^ j - 1)

/-- Left endpoint `wR * (1 - 2/2^j)`. -/
noncomputable def wT (b j : ℕ) : ℝ := wR b j * (1 - 2 / (2 : ℝ) ^ j)

/-- Small-radius deletion of the odd rank `s` by the window `(b,j)` at length `p`. -/
def Del (p b j s : ℕ) : Prop :=
  Odd s ∧ (2 : ℝ) ^ p * wT b j < s ∧ (s : ℝ) < (2 : ℝ) ^ p * wR b j

/-- Enlarged-radius deletion. -/
def EnlDel (p b j s : ℕ) : Prop :=
  Odd s ∧ (2 : ℝ) ^ p * wT b j - wR b j < s ∧ (s : ℝ) < ((2 : ℝ) ^ p + 1) * wR b j

/-- Containment of windows: `W(b,j) ⊆ W(b',j')`. -/
def WinLE (b j b' j' : ℕ) : Prop := wT b' j' ≤ wT b j ∧ wR b j ≤ wR b' j'

/-- Primitive signed-leader windows: the arithmetic content of an actual window. -/
def GoodWin (p a k : ℕ) : Prop :=
  IsWin p a k ∧ IsLeader (2 ^ k - 1) a ∧ ∀ i, 0 < i → i < k → ¬ (2 ^ k - 1) ∣ (2 ^ i - 1) * a

lemma two_pow_ge_four {j : ℕ} (hj : 2 ≤ j) : (4 : ℝ) ≤ 2 ^ j := by
  have : (2 : ℝ) ^ 2 ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hj
  norm_num at this; linarith

lemma wR_pos {b j : ℕ} (hb : 0 < b) (hj : 1 ≤ j) : 0 < wR b j := by
  unfold wR
  have : (2 : ℝ) ≤ 2 ^ j := by
    have := pow_le_pow_right₀ (show (1:ℝ) ≤ 2 by norm_num) hj; simpa using this
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  apply div_pos hb'; linarith

/-- `wR = b/2^j + wR/2^j`. -/
lemma wR_eq {b j : ℕ} (hj : 1 ≤ j) : wR b j = b / 2 ^ j + wR b j / 2 ^ j := by
  unfold wR
  have h2 : (2 : ℝ) ≤ 2 ^ j := by
    have := pow_le_pow_right₀ (show (1:ℝ) ≤ 2 by norm_num) hj; simpa using this
  have h1 : (2 : ℝ) ^ j - 1 ≠ 0 := by linarith
  have h0 : (2 : ℝ) ^ j ≠ 0 := by positivity
  field_simp
  ring

lemma wT_eq {b j : ℕ} (hj : 1 ≤ j) : wT b j = b / 2 ^ j - wR b j / 2 ^ j := by
  have := wR_eq (b := b) hj
  unfold wT
  have h0 : (2 : ℝ) ^ j ≠ 0 := by positivity
  field_simp
  field_simp at this
  linarith

lemma wT_lt_center {b j : ℕ} (hb : 0 < b) (hj : 1 ≤ j) : wT b j < b / 2 ^ j := by
  rw [wT_eq hj]; have := wR_pos hb hj; have : (0:ℝ) < 2 ^ j := by positivity
  have : 0 < wR b j / 2 ^ j := by positivity
  linarith

lemma center_lt_wR {b j : ℕ} (hb : 0 < b) (hj : 1 ≤ j) : (b : ℝ) / 2 ^ j < wR b j := by
  conv_rhs => rw [wR_eq hj]
  have := wR_pos hb hj; have : 0 < wR b j / 2 ^ j := by positivity
  linarith

lemma pow_split {p j : ℕ} (h : j ≤ p) : (2 : ℝ) ^ p = 2 ^ j * 2 ^ (p - j) := by
  rw [← pow_add]; congr 1; omega

/-- The deletion interval in center/radius form. -/
lemma del_iff {p b j s : ℕ} (hj : 1 ≤ j) (hjp : j ≤ p) :
    Del p b j s ↔ Odd s ∧ |(s : ℝ) - b * 2 ^ (p - j)| < wR b j * 2 ^ (p - j) := by
  unfold Del
  rw [wT_eq hj, abs_sub_lt_iff, pow_split hjp]
  have h0 : (2 : ℝ) ^ j ≠ 0 := by positivity
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, ?_, ?_⟩
    · have : (2:ℝ) ^ j * 2 ^ (p - j) * wR b j = wR b j * 2 ^ (p - j) + b * 2 ^ (p - j) := by
        conv_lhs => rw [wR_eq hj]
        field_simp; ring
      nlinarith
    · have : (2:ℝ) ^ j * 2 ^ (p - j) * (b / 2 ^ j - wR b j / 2 ^ j)
          = b * 2 ^ (p - j) - wR b j * 2 ^ (p - j) := by field_simp
      linarith
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, ?_, ?_⟩
    · have : (2:ℝ) ^ j * 2 ^ (p - j) * (b / 2 ^ j - wR b j / 2 ^ j)
          = b * 2 ^ (p - j) - wR b j * 2 ^ (p - j) := by field_simp
      linarith
    · have : (2:ℝ) ^ j * 2 ^ (p - j) * wR b j = wR b j * 2 ^ (p - j) + b * 2 ^ (p - j) := by
        conv_lhs => rw [wR_eq hj]
        field_simp; ring
      linarith

lemma enlDel_iff {p b j s : ℕ} (hj : 1 ≤ j) (hjp : j ≤ p) :
    EnlDel p b j s ↔ Odd s ∧ |(s : ℝ) - b * 2 ^ (p - j)| < wR b j * (2 ^ (p - j) + 1) := by
  unfold EnlDel
  rw [wT_eq hj, abs_sub_lt_iff, pow_split hjp]
  have h0 : (2 : ℝ) ^ j ≠ 0 := by positivity
  have e1 : (2:ℝ) ^ j * 2 ^ (p - j) * wR b j = wR b j * 2 ^ (p - j) + b * 2 ^ (p - j) := by
    conv_lhs => rw [wR_eq hj]
    field_simp; ring
  have e2 : (2:ℝ) ^ j * 2 ^ (p - j) * (b / 2 ^ j - wR b j / 2 ^ j)
      = b * 2 ^ (p - j) - wR b j * 2 ^ (p - j) := by field_simp
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, by nlinarith, by nlinarith⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, by nlinarith, by nlinarith⟩

lemma Del.enlDel {p b j s : ℕ} (hb : 0 < b) (hj : 1 ≤ j) (h : Del p b j s) : EnlDel p b j s := by
  obtain ⟨h1, h2, h3⟩ := h
  have := wR_pos hb hj
  refine ⟨h1, by linarith, by nlinarith⟩

lemma Del.mono {p b j b' j' s : ℕ} (hle : WinLE b j b' j') (h : Del p b j s) : Del p b' j' s := by
  obtain ⟨h1, h2, h3⟩ := h
  have hN : (0 : ℝ) < 2 ^ p := by positivity
  refine ⟨h1, ?_, ?_⟩
  · nlinarith [hle.1]
  · nlinarith [hle.2]

lemma EnlDel.mono {p b j b' j' s : ℕ} (hle : WinLE b j b' j') (h : EnlDel p b j s) :
    EnlDel p b' j' s := by
  obtain ⟨h1, h2, h3⟩ := h
  have hN : (0 : ℝ) < 2 ^ p := by positivity
  refine ⟨h1, ?_, ?_⟩
  · nlinarith [hle.1, hle.2]
  · nlinarith [hle.2]

lemma WinLE.trans {b j b' j' b'' j'' : ℕ} (h1 : WinLE b j b' j') (h2 : WinLE b' j' b'' j'') :
    WinLE b j b'' j'' := ⟨le_trans h2.1 h1.1, le_trans h1.2 h2.2⟩

lemma WinLE.refl (b j : ℕ) : WinLE b j b j := ⟨le_rfl, le_rfl⟩

/-- A window containing another one has at most its denominator, with equality only for the
same window. -/
lemma WinLE.le_exp {b j b' j' : ℕ} (hb : 0 < b) (hj : 2 ≤ j) (hj' : 1 ≤ j')
    (h : WinLE b j b' j') : j' < j ∨ (j' = j ∧ b' = b) := by
  by_contra hcon
  push Not at hcon
  have hjj : j ≤ j' := hcon.1
  obtain ⟨h1, h2⟩ := h
  have hR := wR_pos hb (by omega : 1 ≤ j)
  have hp : (2 : ℝ) ^ j ≤ 2 ^ j' := pow_le_pow_right₀ (by norm_num) hjj
  have h4 : (4:ℝ) ≤ 2 ^ j := two_pow_ge_four hj
  unfold wT at h1
  have hc0 : 0 < 1 - 2 / (2:ℝ) ^ j := by
    have : (2:ℝ) / 2 ^ j ≤ 1 / 2 := by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    linarith
  rcases eq_or_lt_of_le hjj with hjj | hjj
  · subst hjj
    apply hcon.2 rfl
    have := le_of_mul_le_mul_right h1 hc0
    have hRe : wR b' j = wR b j := le_antisymm this h2
    unfold wR at hRe
    have : (2:ℝ) ^ j - 1 ≠ 0 := by linarith
    rw [div_left_inj₀ this] at hRe
    exact_mod_cast hRe
  · have hp' : (2 : ℝ) ^ j < 2 ^ j' := pow_lt_pow_right₀ (by norm_num) hjj
    have hc' : (1 - 2 / (2:ℝ) ^ j) < 1 - 2 / 2 ^ j' := by
      have : (2:ℝ) / 2 ^ j' < 2 / 2 ^ j := div_lt_div_of_pos_left (by norm_num) (by positivity) hp'
      linarith
    nlinarith

end GrayNecklaces
