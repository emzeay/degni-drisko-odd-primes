module

public import GrayNecklaces.TentRet

/-!
# Growth and stabilization of return intervals
-/

@[expose] public section

namespace GrayNecklaces

open Tiozzo

section

variable {a k : ℕ} (h : Central a k)
include h

variable {i : ℕ}

lemma Fm_iterate_mul_mem (hi1 : 1 ≤ i) (hik : i < k) (hsg : sg a k i = -1)
    (hsub : topI a k (nxt a k i) ⊆ topI a k i) :
    ∀ q : ℕ, ∀ z ∈ topI a k i, (Fm a k)^[(q + 1) * dret a k i] z ∈ topI a k (nxt a k i) := by
  have hF := (nxt_spec h hi1 hik hsg).2.2.2.2.2.1
  intro q
  induction q with
  | zero => intro z hz; simpa using hF z hz
  | succ q ih =>
    intro z hz
    rw [show (q + 1 + 1) * dret a k i = dret a k i + (q + 1) * dret a k i by ring,
      Function.iterate_add_apply]
    exact hF _ (hsub (ih z hz))

/-- **Growth**: return intervals contain their predecessors. -/
theorem xo_nxt_le (hi1 : 1 ≤ i) (hik : i < k) (hsg : sg a k i = -1) :
    xo a k (nxt a k i) ≤ xo a k i := by
  by_contra hlt
  push Not at hlt
  have hsub : topI a k (nxt a k i) ⊆ topI a k i :=
    fun z hz => ⟨le_trans hlt.le hz.1, hz.2⟩
  obtain ⟨hd1, hdle, _, _⟩ := dret_spec h hi1 hik
  set d := dret a k i
  have hmul := Fm_iterate_mul_mem h hi1 hik hsg hsub
  have hxi : xo a k i ∈ topI a k i := ⟨le_rfl, xo_le_lam h i⟩
  have hlam : lam a k ∈ topI a k i := ⟨xo_le_lam h i, le_rfl⟩
  have hq : 1 ≤ k / d := (Nat.one_le_div_iff (by omega)).mpr (by omega)
  have hkd : k = k % d + (k / d - 1 + 1) * d := by
    rw [Nat.sub_add_cancel hq, mul_comm]; exact (Nat.mod_add_div k d).symm
  have hFk : ∀ j, (Fm a k)^[k] (xo a k j) = xo a k j := by
    intro j; rw [Fm_iterate_xo h, xo_period h]
  rcases Nat.eq_zero_or_pos (k % d) with hr | hr
  · have := hmul (k / d - 1) (xo a k i) hxi
    have e : (k / d - 1 + 1) * d = k := by omega
    rw [e, hFk] at this
    exact absurd this.1 (not_le.mpr hlt)
  · have hw := hmul (k / d - 1) (lam a k) hlam
    have := Fm_iterate_lt h hi1 hik hr (Nat.mod_lt _ (by omega)) (hsub hw)
    rw [← Function.iterate_add_apply, ← hkd, ← xo_zero, hFk] at this
    exact lt_irrefl _ this

/-- Larger top intervals return no later. -/
theorem dret_mono {i i' : ℕ} (hi1 : 1 ≤ i) (hik : i < k) (hle : xo a k i' ≤ xo a k i) :
    dret a k i' ≤ dret a k i := by
  classical
  obtain ⟨hd1, _, ⟨z, hz, hzv⟩, _⟩ := dret_spec h hi1 hik
  exact Nat.find_min' (retP_exists a k i') (Or.inl ⟨hd1, z, ⟨le_trans hle hz.1, hz.2⟩, hzv⟩)

/-- **Phase shifts.**  If a later, larger top interval has a smaller phase, its whole return
segment ends at or before the earlier phase. -/
theorem shift_bound {i i' : ℕ} (_hi1 : 1 ≤ i) (_hik : i < k) (hi1' : 1 ≤ i') (hik' : i' < k)
    (hsg : sg a k i = -1) (hsg' : sg a k i' = -1) (_hle : xo a k i' ≤ xo a k i) (hlt : i' < i)
    (hd : dret a k i' ≤ dret a k i) : i' + dret a k i' ≤ i := by
  by_contra hh
  push Not at hh
  set r := i - i'
  obtain ⟨hd1', _, ⟨z, hz, hzv⟩, _⟩ := dret_spec h hi1' hik'
  have haff := affine h hi1' hik' r (by omega)
  -- the orientation of `T^r` on the later interval is positive
  have hsgr : (sg a k r : ℝ) = 1 := by
    have e := sg_add_real h i' r
    rw [show i' + r = i by omega] at e
    have hprod : ∏ s ∈ Finset.range r, side (xo a k (i' + s)) = sg a k r := by
      have e0 := sg_add_real h 0 r
      simp only [zero_add] at e0
      rw [e0]
      simp only [sg, Int.cast_one, one_mul]
      apply Finset.prod_congr rfl
      intro s hs
      rw [Finset.mem_range] at hs
      unfold side
      have hss := same_side h hi1' hik' (s := s) (by omega) (⟨le_rfl, xo_le_lam h i'⟩ :
        xo a k i' ∈ topI a k i')
      rw [tent_iterate_xo h] at hss
      by_cases h2 : xo a k s ≤ 1 / 2
      · rw [ite_eq_left h2, ite_eq_left (hss.mpr h2)]
      · rw [ite_eq_right h2, ite_eq_right (fun h3 => h2 (hss.mp h3))]
    rw [hprod] at e
    have h1 : (sg a k i : ℝ) = -1 := by exact_mod_cast hsg
    have h2 : (sg a k i' : ℝ) = -1 := by exact_mod_cast hsg'
    rw [h1, h2] at e
    linarith
  -- `T^r` maps the later interval into the earlier one
  have hmap : ∀ w ∈ topI a k i', tent^[r] w ∈ topI a k i := by
    intro w hw
    have e := haff _ (⟨le_rfl, xo_le_lam h i'⟩ : xo a k i' ∈ topI a k i')
    have hxi : xo a k i = xo a k r + 2 ^ r * (xo a k i' - lam a k) := by
      rw [← show i' + r = i by omega, ← tent_iterate_xo h, e, hsgr, one_mul]
    rw [haff w hw, hsgr, one_mul]
    have hP : (0 : ℝ) < 2 ^ r := by positivity
    constructor
    · rw [hxi]; nlinarith [hw.1]
    · have := xo_le_lam h r; nlinarith [hw.2]
  have hret : RetP a k i (dret a k i' - r) := by
    left
    refine ⟨by omega, tent^[r] z, hmap z hz, ?_⟩
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel (by omega)]; exact hzv
  classical
  have := Nat.find_min' (retP_exists a k i) hret
  have : dret a k i ≤ dret a k i' - r := this
  omega

omit h in
lemma half_mem_of_lt {x y z : ℝ} (h1 : x ≤ z) (h2 : z ≤ y) : z ∈ Set.uIcc x y := by
  rw [Set.mem_uIcc]; left; exact ⟨h1, h2⟩

/-- An orbit point in a top interval and in its image, when the interval contains `2/3`. -/
lemma orbit_pt_in_both (hi1 : 1 ≤ i) (hik : i < k) (hd2 : 2 ≤ dret a k i)
    (h23 : xo a k i ≤ 2 / 3) :
    ∃ l, xo a k l ∈ topI a k i ∧ ∃ z ∈ topI a k i, Fm a k z = xo a k l := by
  have hlam56 := lam_gt h
  have haff1 := affine h hi1 hik 1 (by omega)
  simp only [Function.iterate_one, pow_one] at haff1
  have hFeq : ∀ z ∈ topI a k i, Fm a k z = tent z := by
    intro z hz
    have h1 := Fm_iterate_lt h hi1 hik (r := 1) le_rfl (by omega) hz
    simp only [Function.iterate_one] at h1
    unfold Fm at h1 ⊢
    rcases min_cases (tent z) (lam a k) with ⟨h2, _⟩ | ⟨h2, _⟩
    · exact h2
    · rw [h2] at h1; exact absurd h1 (lt_irrefl _)
  have hxi : xo a k i ∈ topI a k i := ⟨le_rfl, xo_le_lam h i⟩
  have hlam : lam a k ∈ topI a k i := ⟨xo_le_lam h i, le_rfl⟩
  have h23I : (2 / 3 : ℝ) ∈ topI a k i := ⟨h23, by linarith⟩
  have e23 : (2 / 3 : ℝ) = xo a k 1 + sg a k 1 * 2 * (2 / 3 - lam a k) := by
    rw [← haff1 _ h23I]; unfold tent; norm_num
  have ei : xo a k (i + 1) = xo a k 1 + sg a k 1 * 2 * (xo a k i - lam a k) := by
    rw [← haff1 _ hxi, xo_succ h]
  have hpre : ∀ y : ℝ, (∃ z ∈ topI a k i, tent z = y) → (∃ z ∈ topI a k i, Fm a k z = y) := by
    rintro y ⟨z, hz, hzv⟩; exact ⟨z, hz, by rw [hFeq z hz, hzv]⟩
  rcases sg_real_cases 1 with hs | hs
  · rw [hs] at e23 ei haff1
    rcases le_total (xo a k (i + 1)) (xo a k i) with hh | hh
    · refine ⟨i, hxi, hpre _ ⟨lam a k + (xo a k i - xo a k 1) / 2, ⟨by linarith, by linarith⟩, ?_⟩⟩
      rw [haff1 _ ⟨by linarith, by linarith⟩]; ring
    · refine ⟨i + 1, ⟨hh, by linarith⟩, hpre _ ⟨xo a k i, hxi, (xo_succ h i).symm⟩⟩
  · rw [hs] at e23 ei haff1
    rcases le_total (xo a k 1) (xo a k i) with hh | hh
    · refine ⟨i, hxi, hpre _ ⟨lam a k + (xo a k 1 - xo a k i) / 2, ⟨by linarith, by linarith⟩, ?_⟩⟩
      rw [haff1 _ ⟨by linarith, by linarith⟩]; ring
    · refine ⟨1, ⟨hh, by linarith⟩, hpre _ ⟨lam a k, hlam, by rw [← xo_zero, xo_succ h]⟩⟩

lemma stable_mul (hi1 : 1 ≤ i) (hik : i < k) (hsg : sg a k i = -1) (hst : nxt a k i = i) :
    ∀ q : ℕ, ∀ z ∈ topI a k i, (Fm a k)^[q * dret a k i] z ∈ topI a k i := by
  have hF := (nxt_spec h hi1 hik hsg).2.2.2.2.2.1
  rw [hst] at hF
  intro q; induction q with
  | zero => intro z hz; simpa using hz
  | succ q ih =>
    intro z hz
    rw [show (q + 1) * dret a k i = dret a k i + q * dret a k i by ring, Function.iterate_add_apply]
    exact hF _ (ih z hz)

lemma stable_dvd (hi1 : 1 ≤ i) (hik : i < k) (hsg : sg a k i = -1) (hst : nxt a k i = i) :
    ∀ n : ℕ, ∀ z ∈ topI a k i, (Fm a k)^[n] z = lam a k → dret a k i ∣ n := by
  obtain ⟨hd1, _, _, _⟩ := dret_spec h hi1 hik
  intro n z hz hn
  set d := dret a k i
  have e : n = n % d + (n / d) * d := by rw [mul_comm]; exact (Nat.mod_add_div n d).symm
  rw [e, Function.iterate_add_apply] at hn
  by_contra hnd
  have hr : 0 < n % d := Nat.pos_of_ne_zero (fun h0 => hnd (Nat.dvd_of_mod_eq_zero h0))
  have := Fm_iterate_lt h hi1 hik hr (Nat.mod_lt _ (by omega))
    (stable_mul h hi1 hik hsg hst (n / d) z hz)
  linarith

lemma stable_gt_two_thirds (hi1 : 1 ≤ i) (hik : i < k) (hsg : sg a k i = -1)
    (hst : nxt a k i = i) (hd2 : 2 ≤ dret a k i) : 2 / 3 < xo a k i := by
  by_contra hh
  push Not at hh
  obtain ⟨l, hl, z, hz, hzv⟩ := orbit_pt_in_both h hi1 hik hd2 hh
  have hFy : (Fm a k)^[l * (k - 1)] (xo a k l) = lam a k := by
    have hk := h.hk
    have hlk : l + l * (k - 1) = l * k := by
      rw [Nat.mul_sub, mul_one]
      have : l ≤ l * k := Nat.le_mul_of_pos_right _ (by omega)
      omega
    rw [Fm_iterate_xo h, xo_mod h, hlk, Nat.mul_mod_left, xo_zero]
  have h1 := stable_dvd h hi1 hik hsg hst _ _ hl hFy
  have h2 := stable_dvd h hi1 hik hsg hst (l * (k - 1) + 1) z hz
    (by rw [Function.iterate_succ_apply, hzv, hFy])
  have : dret a k i ∣ 1 := (Nat.dvd_add_right h1).mp h2
  have := Nat.le_of_dvd (by norm_num) this
  omega

end

/-- A window endpoint `wT u d` with `d ≥ 2`, `u` odd, has even reduced denominator, so it is
never `a/(2^k - 1)`. -/
lemma wT_ne_wR {a k u d : ℕ} (hd : 2 ≤ d) (hk : 1 ≤ k) (hu : Odd u) (hM : Odd (2 ^ k - 1)) :
    wT u d ≠ wR a k := by
  intro he
  unfold wT wR at he
  have hC : (4 : ℝ) ≤ 2 ^ d := two_pow_ge_four hd
  have hK : (1 : ℝ) < 2 ^ k := one_lt_pow₀ (by norm_num) (by omega)
  have hint : u * (2 ^ d - 2) * (2 ^ k - 1) = a * (2 ^ d * (2 ^ d - 1)) := by
    have h2d : 2 ≤ 2 ^ d := two_le_two_pow (by omega)
    have h1k : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have e : (u : ℝ) * (2 ^ d - 2) * (2 ^ k - 1) = a * (2 ^ d * (2 ^ d - 1)) := by
      have he' : (u : ℝ) * (2 ^ d - 2) / (2 ^ d * (2 ^ d - 1)) = a / (2 ^ k - 1) := by
        rw [← he]; field_simp
      rw [div_eq_div_iff (by nlinarith) (by linarith)] at he'
      linarith
    have : ((u * (2 ^ d - 2) * (2 ^ k - 1) : ℕ) : ℝ) = ((a * (2 ^ d * (2 ^ d - 1)) : ℕ) : ℝ) := by
      rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub h2d, Nat.cast_sub h1k, Nat.cast_mul,
        Nat.cast_mul, Nat.cast_sub (le_trans (by norm_num) h2d)]
      push_cast; linarith
    exact_mod_cast this
  have hd4 : 2 ^ d = 4 * 2 ^ (d - 2) := by
    rw [show 4 = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
  have hd1 : 2 ^ d = 2 * 2 ^ (d - 1) := by rw [← pow_succ']; congr 1; omega
  have hd1' : 2 ^ (d - 1) = 2 * 2 ^ (d - 2) := by rw [← pow_succ']; congr 1; omega
  have hodd1 : Odd (2 ^ (d - 1) - 1) := by
    have : 1 ≤ 2 ^ (d - 2) := Nat.one_le_two_pow
    exact ⟨2 ^ (d - 2) - 1, by omega⟩
  have hodd2 : Odd (u * (2 ^ (d - 1) - 1) * (2 ^ k - 1)) := (hu.mul hodd1).mul hM
  have e3 : 2 ^ d - 2 = 2 * (2 ^ (d - 1) - 1) := by
    have : 1 ≤ 2 ^ (d - 1) := Nat.one_le_two_pow
    omega
  rw [e3, show u * (2 * (2 ^ (d - 1) - 1)) * (2 ^ k - 1) =
    2 * (u * (2 ^ (d - 1) - 1) * (2 ^ k - 1)) by ring, hd4] at hint
  obtain ⟨t, ht⟩ := hodd2
  rw [ht] at hint
  have : 4 ∣ 2 * (2 * t + 1) := by
    rw [hint]; exact ⟨a * (2 ^ (d - 2) * (4 * 2 ^ (d - 2) - 1)), by ring⟩
  omega

section

variable {a k : ℕ} (h : Central a k)
include h

variable {i : ℕ}

/-- The apex of a stable cycle produces a coarser window containing `R` in its interior. -/
lemma apex_contra (hi1 : 1 ≤ i) (hik : i < k) (hd2 : 2 ≤ dret a k i) (h23 : 2 / 3 < xo a k i)
    {z0 : ℝ} (hz01 : xo a k i < z0) (hz02 : z0 < lam a k)
    (hz0v : tent^[dret a k i - 1] z0 = 1 / 2)
    (hform : ∀ z ∈ topI a k i, tent^[dret a k i] z = 1 - 2 ^ dret a k i * |z - z0|)
    (hmin' : xo a k i = min (xo a k (i + dret a k i)) (xo a k (dret a k i))) : False := by
  obtain ⟨_, hdle, _, _⟩ := dret_spec h hi1 hik
  set d := dret a k i with hd
  have hxi : xo a k i ∈ topI a k i := ⟨le_rfl, xo_le_lam h i⟩
  have hlam : lam a k ∈ topI a k i := ⟨xo_le_lam h i, le_rfl⟩
  have hz0I : z0 ∈ topI a k i := ⟨hz01.le, hz02.le⟩
  have hC4 : (4 : ℝ) ≤ 2 ^ d := two_pow_ge_four hd2
  have e1 : xo a k (i + d) = 1 - 2 ^ d * (z0 - xo a k i) := by
    rw [← tent_iterate_xo h, hform _ hxi, abs_of_neg (by linarith)]; ring
  have e2 : xo a k d = 1 - 2 ^ d * (lam a k - z0) := by
    rw [← zero_add d, ← tent_iterate_xo h, xo_zero, zero_add, hform _ hlam,
      abs_of_pos (by linarith)]
  -- `2^d z0` is an odd integer
  have hz0unit : 0 ≤ z0 ∧ z0 ≤ 1 := topI_sub_unit h hz0I
  have hT := hz0v
  rw [show d - 1 = (d - 2) + 1 by omega, tent_iterate hz0unit.1 hz0unit.2] at hT
  have hq : |2 ^ (d - 2) * z0 - round (2 ^ (d - 2) * z0)| = 1 / 4 := by
    rw [← nint_eq_abs_sub (abs_sub_round _)]; linarith
  have hC : (2 : ℝ) ^ d = 4 * 2 ^ (d - 2) := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
  obtain ⟨w, hw, hwodd⟩ : ∃ w : ℤ, (2 : ℝ) ^ d * z0 = w ∧ Odd w := by
    set n := round (2 ^ (d - 2) * z0)
    rcases abs_eq (by norm_num : (0:ℝ) ≤ 1 / 4) |>.mp hq with h5 | h5
    · exact ⟨4 * n + 1, by rw [hC]; push_cast; linarith, ⟨2 * n, by ring⟩⟩
    · exact ⟨4 * n - 1, by rw [hC]; push_cast; linarith, ⟨2 * n - 1, by ring⟩⟩
  have hlam1 := lam_le_one h
  have hwC : w < 2 ^ d := by
    have : (w : ℝ) < 2 ^ d := by rw [← hw]; nlinarith
    exact_mod_cast this
  have hw23 : 2 * 2 ^ d < 3 * w := by
    have : (2 * 2 ^ d : ℝ) < 3 * w := by rw [← hw]; nlinarith
    exact_mod_cast this
  obtain ⟨u0, hu0⟩ : ∃ u0 : ℕ, (u0 : ℤ) = 2 ^ d - w := ⟨(2 ^ d - w).toNat, by omega⟩
  have hu0odd : Odd u0 := by
    have : Odd ((u0 : ℤ)) := by
      rw [hu0]; exact Even.sub_odd (Int.even_pow.mpr ⟨even_two, by omega⟩) hwodd
    exact (Int.odd_natCast u0).mp this
  have hu03 : 3 * u0 < 2 ^ d := by
    have : (3 * u0 : ℤ) < 2 ^ d := by rw [hu0]; linarith
    exact_mod_cast this
  have hu0R : (u0 : ℝ) = 2 ^ d - 2 ^ d * z0 := by
    have : ((u0 : ℤ) : ℝ) = ((2 ^ d - w : ℤ) : ℝ) := by rw [hu0]
    push_cast at this; rw [this, hw]
  -- window inequalities
  have hR : wR a k = 1 - lam a k := by unfold lam; ring
  have hstab : xo a k i = min (1 - 2 ^ d * (z0 - xo a k i)) (1 - 2 ^ d * (lam a k - z0)) := by
    rw [← e1, ← e2, hmin']
  have hrle : (lam a k - z0) * (2 ^ d - 1) ≤ 1 - z0 := by
    rcases le_total (lam a k - z0) (z0 - xo a k i) with hh | hh
    · have h1 : xo a k i = 1 - 2 ^ d * (z0 - xo a k i) := by
        have := hstab; rwa [min_eq_left (by nlinarith)] at this
      nlinarith
    · have h1 : xo a k i = 1 - 2 ^ d * (lam a k - z0) := by
        have := hstab; rwa [min_eq_right (by nlinarith)] at this
      nlinarith
  have hwTu : wT u0 d = u0 * (2 ^ d - 2) / (2 ^ d * (2 ^ d - 1)) := by
    unfold wT wR; field_simp
  have hlow : wT u0 d ≤ wR a k := by
    rw [hwTu, hR, div_le_iff₀ (by nlinarith), hu0R]; nlinarith
  have hlt1 : wT u0 d < wR a k :=
    lt_of_le_of_ne hlow (wT_ne_wR hd2 (by have := h.hk; omega) hu0odd h.M_odd)
  have hlt2 : wR a k < wR u0 d := by
    rw [hR]
    unfold wR
    have h2 : 1 - z0 = u0 / 2 ^ d := by rw [hu0R]; field_simp
    have h3 : (u0 : ℝ) / 2 ^ d < u0 / (2 ^ d - 1) := by
      have : (0 : ℝ) < u0 := by have := hu0odd.pos; exact_mod_cast this
      exact div_lt_div_of_pos_left this (by linarith) (by linarith)
    linarith
  exact h.maxi u0 d hd2 (by omega) hu0odd hu03 hlt1 hlt2

/-- **No proper stable cycle**: a stable top interval returns at once. -/
theorem stable_dret (hi1 : 1 ≤ i) (hik : i < k) (hsg : sg a k i = -1) (hst : nxt a k i = i) :
    dret a k i = 1 := by
  obtain ⟨hd1, hdle, _, _⟩ := dret_spec h hi1 hik
  by_contra hd1'
  have hd2 : 2 ≤ dret a k i := by omega
  have hmin' := (nxt_spec h hi1 hik hsg).2.2.2.2.1
  rw [hst] at hmin'
  have h23 := stable_gt_two_thirds h hi1 hik hsg hst hd2
  have hxi : xo a k i ∈ topI a k i := ⟨le_rfl, xo_le_lam h i⟩
  rcases ret_cases h hi1 hik with ⟨z0, hz01, hz02, hz0v, hform, _⟩ | ⟨hid, hsgd, hform⟩
  · exact apex_contra h hi1 hik hd2 h23 hz01 hz02 hz0v hform hmin'
  · have hxid : xo a k (i + dret a k i) = lam a k := by
      rw [xo_mod h, hid, Nat.mod_self, xo_zero]
    have hxd : xo a k (dret a k i) < lam a k := xo_lt_lam h (by omega) (by omega)
    have hnxtd : nxt a k i = dret a k i := by
      unfold nxt; rw [ite_eq_right (by rw [hxid]; exact not_lt.mpr hxd.le)]
    have hdi : dret a k i = i := by have := hst; rw [hnxtd] at this; exact this
    have := hform _ hxi
    rw [tent_iterate_xo h, hxid, hdi] at this
    have hs : (sg a k i : ℝ) = -1 := by exact_mod_cast hsg
    rw [← hdi, hsgd] at this
    push_cast at this
    rw [hdi] at this
    have hP : (1 : ℝ) < 2 ^ i := one_lt_pow₀ (by norm_num) (by omega)
    have hlt := xo_lt_lam h (i := i) (by omega) hik
    nlinarith

end

end GrayNecklaces
