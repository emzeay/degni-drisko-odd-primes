module

public import GrayNecklaces.TentDyn

/-!
# The return of a top interval

At the first return time `d` of `[x_i, λ]`, either `T^(d-1)` takes an interior point `z₀` to `1/2`
(case A, `T^d z = 1 - 2^d |z - z₀|`), or `T^d` is still affine and `i + d = k` (case B).  The image
`Fm^d [x_i, λ]` is the top interval of the next phase `nxt i`.
-/

@[expose] public section

namespace GrayNecklaces

open Tiozzo

/-- The phase of the next top interval. -/
noncomputable def nxt (a k i : ℕ) : ℕ :=
  if xo a k (i + dret a k i) < xo a k (dret a k i) then i + dret a k i else dret a k i

/-- An affine map on `[lo, λ]` taking values on both sides of `1/2` hits `1/2`. -/
lemma exists_half {lo lam x c z : ℝ} (hz : z ∈ Set.Icc lo lam) (hns : ¬ (x + c * (z - lam) ≤ 1 / 2 ↔ x ≤ 1 / 2)) :
    ∃ z' ∈ Set.Icc lo lam, x + c * (z' - lam) = 1 / 2 := by
  have hne : c * (z - lam) ≠ 0 := by
    intro he; apply hns; rw [he, add_zero]
  have hc : c ≠ 0 := fun h => hne (by rw [h, zero_mul])
  have hzl : z - lam ≠ 0 := fun h => hne (by rw [h, mul_zero])
  set t := (1 / 2 - x) / (c * (z - lam))
  have ht01 : 0 ≤ t ∧ t ≤ 1 := by
    rcases le_or_gt (x + c * (z - lam)) (1 / 2) with h1 | h1
    · have h2 : 1 / 2 < x := by
        by_contra h2; push Not at h2; exact hns ⟨fun _ => h2, fun _ => h1⟩
      have hneg : c * (z - lam) < 0 := by linarith
      exact ⟨div_nonneg_of_nonpos (by linarith) hneg.le,
        by rw [div_le_one_of_neg hneg]; linarith⟩
    · have h2 : x ≤ 1 / 2 := by
        by_contra h2; push Not at h2
        exact hns ⟨fun h3 => absurd h3 (not_le.mpr h1), fun h3 => absurd h3 (not_le.mpr h2)⟩
      have hpos : 0 < c * (z - lam) := by linarith
      exact ⟨div_nonneg (by linarith) hpos.le, by rw [div_le_one hpos]; linarith⟩
  refine ⟨lam + t * (z - lam), ⟨by nlinarith [hz.1, hz.2], by nlinarith [hz.1, hz.2]⟩, ?_⟩
  simp only [t]; field_simp; ring

section

variable {a k : ℕ} (h : Central a k)
include h

variable {i : ℕ}

omit h in
lemma sg_real_cases (r : ℕ) : (sg a k r : ℝ) = 1 ∨ (sg a k r : ℝ) = -1 := by
  rcases sg_cases (a := a) (k := k) r with h' | h' <;> simp [h']

/-- Same side of `1/2` before the last step before the return. -/
lemma same_side (hi1 : 1 ≤ i) (hik : i < k) {s : ℕ} (hs : s + 2 ≤ dret a k i) {z : ℝ}
    (hz : z ∈ topI a k i) : (tent^[s] z ≤ 1 / 2 ↔ xo a k s ≤ 1 / 2) := by
  obtain ⟨_, _, _, hmin⟩ := dret_spec h hi1 hik
  have haff := affine h hi1 hik s (by omega)
  by_contra hns
  rw [haff z hz] at hns
  obtain ⟨z', hz', hval⟩ := exists_half (c := sg a k s * 2 ^ s) hz
    (by simpa [mul_assoc] using hns)
  have hT : tent^[s] z' = 1 / 2 := by rw [haff z' hz']; linarith
  have := hmin (s + 1) (by omega) (by omega) z' hz'
  rw [Function.iterate_succ_apply', hT] at this
  unfold tent at this; norm_num at this
  linarith [lam_le_one h]

omit h in
lemma tent_iterate_unit {z : ℝ} (hz : 0 ≤ z ∧ z ≤ 1) (n : ℕ) : 0 ≤ tent^[n] z ∧ tent^[n] z ≤ 1 :=
  tent_iterate_le_one hz.1 hz.2 n

/-- The two return cases. -/
lemma ret_cases (hi1 : 1 ≤ i) (hik : i < k) :
    (∃ z0, xo a k i < z0 ∧ z0 < lam a k ∧ tent^[dret a k i - 1] z0 = 1 / 2 ∧
        (∀ z ∈ topI a k i, tent^[dret a k i] z = 1 - 2 ^ dret a k i * |z - z0|) ∧
        (∀ z ∈ topI a k i, tent^[dret a k i - 1] z =
          1 / 2 + sg a k (dret a k i - 1) * 2 ^ (dret a k i - 1) * (z - z0))) ∨
    (i + dret a k i = k ∧ sg a k (dret a k i) = -1 ∧
        ∀ z ∈ topI a k i, tent^[dret a k i] z =
          xo a k (dret a k i) + sg a k (dret a k i) * 2 ^ dret a k i * (z - lam a k)) := by
  obtain ⟨hd1, hdle, ⟨zr, hzr, hret⟩, hmin⟩ := dret_spec h hi1 hik
  set d := dret a k i with hd
  obtain ⟨r, hr⟩ : ∃ r, d = r + 1 := ⟨d - 1, by omega⟩
  have hr' : d - 1 = r := by omega
  rw [hr']
  have haff := affine h hi1 hik r (by omega)
  have hxi : xo a k i ∈ topI a k i := ⟨le_rfl, xo_le_lam h i⟩
  have hlam : lam a k ∈ topI a k i := ⟨xo_le_lam h i, le_rfl⟩
  by_cases hA : ∃ z0 ∈ topI a k i, tent^[r] z0 = 1 / 2
  · left
    obtain ⟨z0, hz0, hz0v⟩ := hA
    have hne1 : z0 ≠ xo a k i := by
      intro he; rw [he, tent_iterate_xo h] at hz0v; exact xo_ne_half h _ hz0v
    have hne2 : z0 ≠ lam a k := by
      intro he; rw [he, ← xo_zero, tent_iterate_xo h] at hz0v; exact xo_ne_half h _ hz0v
    have hform : ∀ z ∈ topI a k i, tent^[r] z = 1 / 2 + sg a k r * 2 ^ r * (z - z0) := by
      intro z hz
      rw [haff z hz]; rw [haff z0 hz0] at hz0v; linarith
    refine ⟨z0, lt_of_le_of_ne hz0.1 (Ne.symm hne1), lt_of_le_of_ne hz0.2 hne2, hz0v, ?_, hform⟩
    intro z hz
    rw [hr, Function.iterate_succ_apply', hform z hz]
    have hbd := tent_iterate_unit (topI_sub_unit h hz) r
    rw [hform z hz] at hbd
    rw [tent_half_add (by rw [abs_le]; constructor <;> linarith)]
    rw [abs_mul, abs_mul]
    rcases sg_real_cases r with hs | hs <;> rw [hs] <;> simp [pow_succ] <;> ring
  · right
    push Not at hA
    -- all of the interval is on the side of `x_r` at step `r`
    have hsame : ∀ z ∈ topI a k i, (tent^[r] z ≤ 1 / 2 ↔ xo a k r ≤ 1 / 2) := by
      intro z hz
      by_contra hns
      rw [haff z hz] at hns
      obtain ⟨z', hz', hval⟩ := exists_half (c := sg a k r * 2 ^ r) hz
        (by simpa [mul_assoc] using hns)
      exact hA z' hz' (by rw [haff z' hz']; linarith)
    have hformd : ∀ z ∈ topI a k i, tent^[d] z =
        xo a k d + sg a k d * 2 ^ d * (z - lam a k) := by
      intro z hz
      rw [hr, Function.iterate_succ_apply']
      have hside : side (tent^[r] z) = side (xo a k r) := by
        unfold side; by_cases h1 : xo a k r ≤ 1 / 2
        · rw [ite_eq_left h1, ite_eq_left ((hsame z hz).mpr h1)]
        · rw [ite_eq_right h1, ite_eq_right (fun h2 => h1 ((hsame z hz).mp h2))]
      have hdf := tent_diff (hsame z hz)
      have hdiff : tent^[r] z - xo a k r = sg a k r * 2 ^ r * (z - lam a k) := by
        rw [haff z hz]; ring
      rw [hside, hdiff] at hdf
      rw [xo_succ h r, sg_succ_real h, pow_succ]
      linarith
    -- the return forces `x_{i+d} = λ`
    have hxid : tent^[d] (xo a k i) = xo a k (i + d) := tent_iterate_xo h i d
    have hxd : xo a k d < lam a k := xo_lt_lam h (by omega) (by omega)
    rw [hformd zr hzr] at hret
    have hc : (sg a k d : ℝ) * 2 ^ d * (xo a k i - lam a k) = xo a k (i + d) - xo a k d := by
      rw [← hxid, hformd _ hxi]; ring
    have hsgd : (sg a k d : ℝ) = -1 := by
      rcases sg_real_cases d with hs | hs
      · exfalso
        rw [hs] at hret
        have : (1 : ℝ) * 2 ^ d * (zr - lam a k) ≤ 0 := by
          have := hzr.2; have : (0:ℝ) < 2 ^ d := by positivity
          nlinarith
        linarith
      · exact hs
    have hlamid : lam a k ≤ xo a k (i + d) := by
      rw [hsgd] at hret hc
      have : -1 * (2:ℝ) ^ d * (zr - lam a k) ≤ -1 * 2 ^ d * (xo a k i - lam a k) := by
        have := hzr.1; have : (0:ℝ) < 2 ^ d := by positivity
        nlinarith
      linarith
    have hid : i + d = k := by
      have he : xo a k (i + d) = lam a k := le_antisymm (xo_le_lam h _) hlamid
      rw [xo_mod h, ← xo_zero] at he
      have := xo_inj h (Nat.mod_lt _ (by omega)) (by omega) he
      have h0 : (i + d) % k = 0 := this
      rcases Nat.lt_or_ge (i + d) k with hl | hl
      · rw [Nat.mod_eq_of_lt hl] at h0; omega
      · omega
    refine ⟨hid, ?_, hformd⟩
    exact_mod_cast hsgd

/-- `Fm^d` on the top interval is the capped `T^d`. -/
lemma Fm_iterate_dret (hi1 : 1 ≤ i) (hik : i < k) {z : ℝ} (hz : z ∈ topI a k i) :
    (Fm a k)^[dret a k i] z = min (tent^[dret a k i] z) (lam a k) := by
  obtain ⟨hd1, _, _, hmin⟩ := dret_spec h hi1 hik
  obtain ⟨r, hr⟩ : ∃ r, dret a k i = r + 1 := ⟨dret a k i - 1, by omega⟩
  rw [hr, Function.iterate_succ_apply', Function.iterate_succ_apply',
    Fm_iterate_eq (fun s h1 h2 => (hmin s h1 (by omega) z hz).le)]
  rfl

lemma Fm_iterate_lt (hi1 : 1 ≤ i) (hik : i < k) {r : ℕ} (hr1 : 1 ≤ r) (hr : r < dret a k i)
    {z : ℝ} (hz : z ∈ topI a k i) : (Fm a k)^[r] z < lam a k := by
  obtain ⟨hd1, _, _, hmin⟩ := dret_spec h hi1 hik
  rw [Fm_iterate_eq (fun s h1 h2 => (hmin s h1 (by omega) z hz).le)]
  exact hmin r hr1 hr z hz

/-- Properties of the next phase. -/
theorem nxt_spec (hi1 : 1 ≤ i) (hik : i < k) (hsg : sg a k i = -1) :
    1 ≤ nxt a k i ∧ nxt a k i < k ∧ sg a k (nxt a k i) = -1 ∧
    (nxt a k i = i + dret a k i ∨ nxt a k i = dret a k i) ∧
    xo a k (nxt a k i) = min (xo a k (i + dret a k i)) (xo a k (dret a k i)) ∧
    (∀ z ∈ topI a k i, (Fm a k)^[dret a k i] z ∈ topI a k (nxt a k i)) ∧
    topI a k (nxt a k i) ⊆ (Fm a k)^[dret a k i] '' topI a k i := by
  obtain ⟨hd1, hdle, _, hmin⟩ := dret_spec h hi1 hik
  set d := dret a k i with hd
  have hxi : xo a k i ∈ topI a k i := ⟨le_rfl, xo_le_lam h i⟩
  have hlam : lam a k ∈ topI a k i := ⟨xo_le_lam h i, le_rfl⟩
  have hxd : xo a k d < lam a k := xo_lt_lam h (by omega) (by omega)
  have hFxi : (Fm a k)^[d] (xo a k i) = xo a k (i + d) := Fm_iterate_xo h i d
  have hFlam : (Fm a k)^[d] (lam a k) = xo a k d := by
    rw [← xo_zero, Fm_iterate_xo h, zero_add]
  have hcont : Continuous (Fm a k)^[d] := (continuous_Fm a k).iterate d
  rcases ret_cases h hi1 hik with ⟨z0, hz01, hz02, hz0v, hform, hform1⟩ | ⟨hid, hsgd, hform⟩
  · -- case A
    have hz0 : z0 ∈ topI a k i := ⟨hz01.le, hz02.le⟩
    have hFz0 : (Fm a k)^[d] z0 = lam a k := by
      rw [Fm_iterate_dret h hi1 hik hz0, hform z0 hz0, sub_self, abs_zero, mul_zero, sub_zero,
        min_eq_right (lam_le_one h)]
    -- signs
    obtain ⟨r, hr⟩ : ∃ r, d = r + 1 := ⟨d - 1, by omega⟩
    have hr' : d - 1 = r := by omega
    rw [hr'] at hform1 hz0v
    have hxr : xo a k r = 1 / 2 + sg a k r * 2 ^ r * (lam a k - z0) := by
      rw [← hform1 _ hlam, ← xo_zero, tent_iterate_xo h, zero_add]
    have hxir : xo a k (i + r) = 1 / 2 + sg a k r * 2 ^ r * (xo a k i - z0) := by
      rw [← hform1 _ hxi, tent_iterate_xo h]
    have hP : (0 : ℝ) < 2 ^ r := by positivity
    have hsgd : sg a k d = -1 := by
      have := sg_succ_real h r
      rw [← hr] at this
      have hv : (sg a k d : ℝ) = -1 := by
        rw [this]
        rcases sg_real_cases r with hs | hs
        · rw [hs]; unfold side; rw [ite_eq_right (by rw [hxr, hs]; nlinarith)]; ring
        · rw [hs]; unfold side; rw [ite_eq_left (by rw [hxr, hs]; nlinarith)]; ring
      exact_mod_cast hv
    have hsgid : sg a k (i + d) = -1 := by
      have e := sg_add_real h i d
      have hprod : ∏ s ∈ Finset.range d, side (xo a k (i + s)) = 1 := by
        rw [hr, Finset.prod_range_succ]
        have h1 : ∏ s ∈ Finset.range r, side (xo a k (i + s)) = sg a k r := by
          have e0 := sg_add_real h 0 r
          simp only [zero_add] at e0
          rw [e0]
          simp only [sg, Int.cast_one, one_mul]
          apply Finset.prod_congr rfl
          intro s hs
          rw [Finset.mem_range] at hs
          unfold side
          have hss := same_side h hi1 hik (s := s) (by omega) hxi
          rw [tent_iterate_xo h] at hss
          by_cases h2 : xo a k s ≤ 1 / 2
          · rw [ite_eq_left h2, ite_eq_left (hss.mpr h2)]
          · rw [ite_eq_right h2, ite_eq_right (fun h3 => h2 (hss.mp h3))]
        rw [h1]
        rcases sg_real_cases r with hs | hs
        · rw [hs]; unfold side; rw [ite_eq_left (by rw [hxir, hs]; nlinarith)]; ring
        · rw [hs]; unfold side; rw [ite_eq_right (by rw [hxir, hs]; nlinarith)]; ring
      rw [hprod, mul_one] at e
      have : (sg a k i : ℝ) = -1 := by exact_mod_cast hsg
      rw [this] at e; exact_mod_cast e
    have hmin' : xo a k (nxt a k i) = min (xo a k (i + d)) (xo a k d) := by
      unfold nxt; rw [← hd]
      split_ifs with hc
      · rw [min_eq_left hc.le]
      · rw [min_eq_right (not_lt.mp hc)]
    have hnxt_or : nxt a k i = i + d ∨ nxt a k i = d := by
      unfold nxt; rw [← hd]; split_ifs <;> simp
    refine ⟨?_, ?_, ?_, hnxt_or, hmin', ?_, ?_⟩
    · rcases hnxt_or with e | e <;> rw [e] <;> omega
    · unfold nxt; rw [← hd]
      split_ifs with hc
      · by_contra hh
        have : i + d = k := by omega
        rw [xo_mod h, this, Nat.mod_self, xo_zero] at hc
        linarith
      · omega
    · rcases hnxt_or with e | e <;> rw [e]
      · exact hsgid
      · exact hsgd
    · intro z hz
      rw [Fm_iterate_dret h hi1 hik hz]
      refine ⟨?_, min_le_right _ _⟩
      rw [hmin']
      apply le_min _ (le_trans (min_le_right _ _) hxd.le)
      rw [hform z hz]
      have e1 : xo a k (i + d) = 1 - 2 ^ d * |xo a k i - z0| := by
        rw [← hform _ hxi, tent_iterate_xo h]
      have e2 : xo a k d = 1 - 2 ^ d * |lam a k - z0| := by
        rw [← hform _ hlam, ← xo_zero, tent_iterate_xo h, zero_add]
      have hab : |z - z0| ≤ max (|xo a k i - z0|) (|lam a k - z0|) := by
        have h1 : z0 - xo a k i ≤ max (|xo a k i - z0|) (|lam a k - z0|) :=
          le_trans (by rw [abs_sub_comm]; exact le_abs_self _) (le_max_left _ _)
        have h2 : lam a k - z0 ≤ max (|xo a k i - z0|) (|lam a k - z0|) :=
          le_trans (le_abs_self _) (le_max_right _ _)
        rw [abs_le]
        constructor <;> linarith [hz.1, hz.2]
      have hPd : (0 : ℝ) < 2 ^ d := by positivity
      rcases le_total (|xo a k i - z0|) (|lam a k - z0|) with hh | hh
      · rw [max_eq_right hh] at hab
        exact min_le_of_right_le (by rw [e2]; nlinarith)
      · rw [max_eq_left hh] at hab
        exact min_le_of_left_le (by rw [e1]; nlinarith)
    · -- covering by the intermediate value theorem
      intro y hy
      simp only [topI, Set.mem_Icc] at hy
      rw [hmin'] at hy
      rcases le_total (xo a k (i + d)) (xo a k d) with hh | hh
      · rw [min_eq_left hh] at hy
        have := intermediate_value_Icc hz01.le hcont.continuousOn
        rw [hFxi, hFz0] at this
        obtain ⟨z, hz, hzv⟩ := this ⟨hy.1, hy.2⟩
        exact ⟨z, ⟨hz.1, le_trans hz.2 hz02.le⟩, hzv⟩
      · rw [min_eq_right hh] at hy
        have := intermediate_value_Icc' hz02.le hcont.continuousOn
        rw [hFz0, hFlam] at this
        obtain ⟨z, hz, hzv⟩ := this ⟨hy.1, hy.2⟩
        exact ⟨z, ⟨le_trans hz01.le hz.1, hz.2⟩, hzv⟩
  · -- case B
    have hxid : xo a k (i + d) = lam a k := by rw [xo_mod h, hid, Nat.mod_self, xo_zero]
    have hnxt : nxt a k i = d := by
      unfold nxt; rw [← hd, ite_eq_right (by rw [hxid]; exact not_lt.mpr hxd.le)]
    have hmin' : xo a k (nxt a k i) = min (xo a k (i + d)) (xo a k d) := by
      rw [hnxt, hxid, min_eq_right hxd.le]
    refine ⟨by rw [hnxt]; omega, by rw [hnxt]; omega, by rw [hnxt]; exact hsgd, Or.inr hnxt,
      hmin', ?_, ?_⟩
    · intro z hz
      rw [Fm_iterate_dret h hi1 hik hz]
      refine ⟨?_, min_le_right _ _⟩
      rw [hnxt]
      apply le_min _ hxd.le
      rw [hform z hz]
      have : (sg a k d : ℝ) = -1 := by exact_mod_cast hsgd
      rw [this]
      have : (0 : ℝ) < 2 ^ d := by positivity
      nlinarith [hz.2]
    · intro y hy
      rw [hnxt] at hy
      simp only [topI, Set.mem_Icc] at hy
      have := intermediate_value_Icc' (xo_le_lam h i) hcont.continuousOn
      rw [hFxi, hFlam, hxid] at this
      exact this hy

end

end GrayNecklaces
