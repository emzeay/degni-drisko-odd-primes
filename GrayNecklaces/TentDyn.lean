module

public import GrayNecklaces.TentOrbit

/-!
# First returns of top intervals under the capped tent map

`Fm z = min (T z) λ`.  For a phase `i` the top interval is `[x_i, λ]`.  Its first return time
`dret i` is the least `r ≥ 1` such that some point of the interval has `T^r z ≥ λ`.  Before the
return `T^r` is affine on the interval with slope `sg r * 2^r`.
-/

@[expose] public section

namespace GrayNecklaces

open Tiozzo

/-- The capped tent map. -/
noncomputable def Fm (a k : ℕ) (z : ℝ) : ℝ := min (tent z) (lam a k)

/-- The top interval of phase `i`. -/
noncomputable def topI (a k i : ℕ) : Set ℝ := Set.Icc (xo a k i) (lam a k)

lemma tent_diff {z w : ℝ} (hs : z ≤ 1 / 2 ↔ w ≤ 1 / 2) :
    tent z - tent w = 2 * side z * (z - w) := by
  unfold tent side
  by_cases hz : z ≤ 1 / 2
  · have hw := hs.mp hz
    rw [ite_eq_left hz, min_eq_left (by linarith), min_eq_left (by linarith)]; ring
  · have hw : ¬ w ≤ 1 / 2 := fun h => hz (hs.mpr h)
    push Not at hz hw
    rw [ite_eq_right (by linarith), min_eq_right (by linarith), min_eq_right (by linarith)]; ring

lemma tent_half_add {y : ℝ} (_hy : |y| ≤ 1 / 2) : tent (1 / 2 + y) = 1 - 2 * |y| := by
  unfold tent
  rcases le_total 0 y with h | h
  · rw [abs_of_nonneg h, min_eq_right (by linarith)]; ring
  · rw [abs_of_nonpos h, min_eq_left (by linarith)]; ring

lemma continuous_Fm (a k : ℕ) : Continuous (Fm a k) :=
  continuous_tent.min continuous_const

/-! ### First return times -/

/-- `Fm` iterates agree with `T` iterates while the orbit stays at or below `λ`. -/
lemma Fm_iterate_eq {a k : ℕ} {z : ℝ} {r : ℕ} (hr : ∀ s, 1 ≤ s → s ≤ r → tent^[s] z ≤ lam a k) :
    (Fm a k)^[r] z = tent^[r] z := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      ih (fun s h1 h2 => hr s h1 (by omega))]
    unfold Fm
    rw [min_eq_left]
    have := hr (r + 1) (by omega) le_rfl
    rwa [Function.iterate_succ_apply'] at this


/-- The return predicate, with `k` as a default witness. -/
def RetP (a k i r : ℕ) : Prop :=
  (1 ≤ r ∧ ∃ z ∈ topI a k i, lam a k ≤ tent^[r] z) ∨ r = k

lemma retP_exists (a k i : ℕ) : ∃ r, RetP a k i r := ⟨k, Or.inr rfl⟩

open Classical in
/-- The first return time of the top interval of phase `i`. -/
noncomputable def dret (a k i : ℕ) : ℕ := Nat.find (retP_exists a k i)


section

variable {a k : ℕ} (h : Central a k)
include h

lemma lam_le_one : lam a k ≤ 1 := by
  have := wR_pos (b := a) (j := k) h.a_pos (by have := h.hk; omega)
  unfold lam; linarith

lemma xo_nonneg (i : ℕ) : 0 ≤ xo a k i := by
  have hM := Mreal_pos h
  have := (uo_pos_lt h i).2.1
  unfold xo
  have : ((uo a k i : ℕ) : ℝ) ≤ ((2 ^ k - 1 : ℕ) : ℝ) := by exact_mod_cast this.le
  rw [two_pow_sub_one_cast] at this
  rw [sub_nonneg, div_le_one hM]; exact this

lemma topI_sub_unit {i : ℕ} {z : ℝ} (hz : z ∈ topI a k i) : 0 ≤ z ∧ z ≤ 1 :=
  ⟨le_trans (xo_nonneg h i) hz.1, le_trans hz.2 (lam_le_one h)⟩

/-- `Fm` acts as `T` on the orbit. -/
lemma Fm_xo (i : ℕ) : Fm a k (xo a k i) = xo a k (i + 1) := by
  unfold Fm; rw [← xo_succ h, min_eq_left (xo_le_lam h _)]

lemma Fm_iterate_xo (i n : ℕ) : (Fm a k)^[n] (xo a k i) = xo a k (i + n) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', ih, Fm_xo h, ← add_assoc]

lemma tent_iterate_xo (i n : ℕ) : tent^[n] (xo a k i) = xo a k (i + n) := by
  rw [xo_eq_iterate h, xo_eq_iterate h, ← Function.iterate_add_apply, add_comm]

variable {i : ℕ}

lemma dret_spec (hi1 : 1 ≤ i) (hik : i < k) :
    1 ≤ dret a k i ∧ dret a k i ≤ k - i ∧ (∃ z ∈ topI a k i, lam a k ≤ tent^[dret a k i] z) ∧
      ∀ r, 1 ≤ r → r < dret a k i → ∀ z ∈ topI a k i, tent^[r] z < lam a k := by
  classical
  have hw : RetP a k i (k - i) := by
    left; refine ⟨by omega, xo a k i, ⟨le_rfl, xo_le_lam h i⟩, ?_⟩
    rw [tent_iterate_xo h, show i + (k - i) = 0 + k by omega, xo_period h, xo_zero]
  have hle : dret a k i ≤ k - i := Nat.find_min' (retP_exists a k i) hw
  have hspec := Nat.find_spec (retP_exists a k i)
  have hspec' : 1 ≤ dret a k i ∧ ∃ z ∈ topI a k i, lam a k ≤ tent^[dret a k i] z := by
    rcases hspec with h1 | h1
    · exact h1
    · exfalso; have : dret a k i = k := h1
      omega
  refine ⟨hspec'.1, hle, hspec'.2, fun r hr1 hr2 z hz => ?_⟩
  by_contra hh; push Not at hh
  exact Nat.find_min (retP_exists a k i) hr2 (Or.inl ⟨hr1, z, hz, hh⟩)

/-- Before the return, `T^r` is affine on the top interval. -/
lemma affine (hi1 : 1 ≤ i) (hik : i < k) :
    ∀ r, r + 1 ≤ dret a k i → ∀ z ∈ topI a k i,
      tent^[r] z = xo a k r + sg a k r * 2 ^ r * (z - lam a k) := by
  obtain ⟨hd1, hdle, _, hmin⟩ := dret_spec h hi1 hik
  intro r
  induction r with
  | zero => intro _ z _; simp [xo_zero, sg]
  | succ r ih =>
    intro hr z hz
    have ihz := ih (by omega) z hz
    -- every point is on the same side as `x_r`
    have hsame : (tent^[r] z ≤ 1 / 2 ↔ xo a k r ≤ 1 / 2) := by
      by_contra hns
      -- the preimage of `1/2` in the interval
      have hsg := sg_cases (a := a) (k := k) r
      have hsR : (sg a k r : ℝ) = 1 ∨ (sg a k r : ℝ) = -1 := by
        rcases hsg with h' | h' <;> simp [h']
      set c : ℝ := (sg a k r : ℝ) * 2 ^ r
      have hc0 : c ≠ 0 := by rcases hsR with h' | h' <;> simp [c, h']
      set z' := lam a k + (1 / 2 - xo a k r) / c
      have hz'val : xo a k r + c * (z' - lam a k) = 1 / 2 := by
        simp only [z']; field_simp; ring
      -- `z'` lies between `z` and `λ`
      have hzc : tent^[r] z - xo a k r = c * (z - lam a k) := by rw [ihz]; ring
      have hbetween : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ 1 / 2 - xo a k r = t * (tent^[r] z - xo a k r) := by
        have hne : tent^[r] z - xo a k r ≠ 0 := by
          intro he; apply hns; rw [show tent^[r] z = xo a k r by linarith]
        refine ⟨(1 / 2 - xo a k r) / (tent^[r] z - xo a k r), ?_, ?_, by field_simp⟩
        · rcases le_or_gt (tent^[r] z) (1/2) with h1 | h1
          · have : 1 / 2 < xo a k r := by
              by_contra h2; push Not at h2; exact hns ⟨fun _ => h2, fun _ => h1⟩
            apply div_nonneg_of_nonpos <;> linarith
          · have : xo a k r ≤ 1 / 2 := by
              by_contra h2; push Not at h2
              exact hns ⟨fun h3 => absurd h3 (not_le.mpr h1), fun h3 => absurd h3 (not_le.mpr h2)⟩
            apply div_nonneg <;> linarith
        · rcases le_or_gt (tent^[r] z) (1/2) with h1 | h1
          · have : 1 / 2 < xo a k r := by
              by_contra h2; push Not at h2; exact hns ⟨fun _ => h2, fun _ => h1⟩
            rw [div_le_one_of_neg (by linarith)]; linarith
          · have : xo a k r ≤ 1 / 2 := by
              by_contra h2; push Not at h2
              exact hns ⟨fun h3 => absurd h3 (not_le.mpr h1), fun h3 => absurd h3 (not_le.mpr h2)⟩
            rw [div_le_one (by linarith)]; linarith
      obtain ⟨t, ht0, ht1, ht⟩ := hbetween
      have hz'eq : z' = lam a k + t * (z - lam a k) := by
        simp only [z']; rw [ht, hzc]; field_simp
      have hz'I : z' ∈ topI a k i := by
        rw [hz'eq]; constructor <;> nlinarith [hz.1, hz.2]
      have hT : tent^[r] z' = 1 / 2 := by
        rw [ih (by omega) z' hz'I]; simpa [c, mul_assoc] using hz'val
      have := hmin (r + 1) (by omega) (by omega) z' hz'I
      rw [Function.iterate_succ_apply', hT] at this
      unfold tent at this; norm_num at this
      linarith [lam_le_one h]
    rw [Function.iterate_succ_apply']
    have hside : side (tent^[r] z) = side (xo a k r) := by
      unfold side; by_cases h1 : xo a k r ≤ 1 / 2
      · rw [ite_eq_left h1, ite_eq_left (hsame.mpr h1)]
      · rw [ite_eq_right h1, ite_eq_right (fun h2 => h1 (hsame.mp h2))]
    have hd := tent_diff hsame
    have hdiff : tent^[r] z - xo a k r = sg a k r * 2 ^ r * (z - lam a k) := by rw [ihz]; ring
    rw [hside, hdiff] at hd
    rw [xo_succ h r, sg_succ_real h, pow_succ]
    linarith

end

end GrayNecklaces
