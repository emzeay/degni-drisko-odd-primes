module

public import GrayNecklaces.Statement
public import GrayNecklaces.Basic

/-!
# Ranks, rotations and representatives

Section 2 of the proof.  Rotation by one position acts on standard BRGC ranks by
`rot1 n r = 2 * min r (2^n - 1 - r) + r % 2`.  The maximum ranks of rotation classes are
`0`, the rank of `1^n`, and `2^n - 1 - s`, `2^n - s` for signed-doubling leaders `s`.
-/

@[expose] public section

namespace GrayNecklaces

/-- The binary reflected Gray code of a rank, as a number. -/
def gcode (r : ℕ) : ℕ := r ^^^ (r >>> 1)

lemma testBit_gcode (r t : ℕ) : (gcode r).testBit t = (r.testBit t ^^ r.testBit (t + 1)) := by
  simp [gcode, Nat.testBit_xor, Nat.testBit_shiftRight, Nat.add_comm]

lemma gcode_xor (r s : ℕ) : gcode (r ^^^ s) = gcode r ^^^ gcode s := by
  apply Nat.eq_of_testBit_eq; intro t
  simp only [testBit_gcode, Nat.testBit_xor]
  cases r.testBit t <;> cases r.testBit (t+1) <;> cases s.testBit t <;> cases s.testBit (t+1) <;> rfl

lemma gcode_eq_zero {x : ℕ} (h : gcode x = 0) : x = 0 := by
  have hb : ∀ t, x.testBit t = x.testBit (t + 1) := by
    intro t
    have := congrArg (fun y => y.testBit t) h
    simp only [testBit_gcode, Nat.zero_testBit] at this
    revert this; cases x.testBit t <;> cases x.testBit (t+1) <;> simp
  have hall : ∀ m t, x.testBit t = x.testBit (t + m) := by
    intro m; induction m with
    | zero => simp
    | succ m ih => intro t; rw [ih t, hb (t + m)]; ring_nf
  apply Nat.eq_of_testBit_eq; intro t
  rw [hall x t, Nat.zero_testBit]
  apply Nat.testBit_lt_two_pow
  calc x < 2 ^ x := Nat.lt_two_pow_self
    _ ≤ 2 ^ (t + x) := Nat.pow_le_pow_right (by norm_num) (by omega)

lemma gcode_inj {r s : ℕ} (h : gcode r = gcode s) : r = s := by
  have : gcode (r ^^^ s) = 0 := by rw [gcode_xor, h, Nat.xor_self]
  have h0 := gcode_eq_zero this
  apply Nat.eq_of_testBit_eq; intro t
  have := congrArg (fun y => y.testBit t) h0
  simp only [Nat.testBit_xor, Nat.zero_testBit] at this
  revert this; cases r.testBit t <;> cases s.testBit t <;> simp

lemma grayWord_apply {n : ℕ} (r : Rank n) (i : Fin n) :
    grayWord r i = (gcode r.val).testBit (n - 1 - i.val) := rfl

lemma grayWord_injective (n : ℕ) : Function.Injective (grayWord (n := n)) := by
  intro r s h
  apply Fin.ext
  apply gcode_inj
  apply Nat.eq_of_testBit_eq; intro t
  by_cases ht : t < n
  · have := congrFun h ⟨n - 1 - t, by omega⟩
    simp only [grayWord_apply] at this
    rwa [show n - 1 - (n - 1 - t) = t by omega] at this
  · have h1 : ∀ x : ℕ, x < 2 ^ n → (gcode x).testBit t = false := by
      intro x hx
      rw [testBit_gcode, Nat.testBit_lt_two_pow (lt_of_lt_of_le hx
        (Nat.pow_le_pow_right (by norm_num) (by omega))),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (by omega)))]
      rfl
    rw [h1 _ r.isLt, h1 _ s.isLt]

lemma grayWord_bijective (n : ℕ) : Function.Bijective (grayWord (n := n)) := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨grayWord_injective n, by simp⟩

/-! ### Rotation by one on ranks -/

/-- Rotation by one position, acting on standard BRGC ranks of length `n`. -/
def rot1 (n r : ℕ) : ℕ := 2 * min r (2 ^ n - 1 - r) + r % 2

lemma rot1_lt {n r : ℕ} (hn : 1 ≤ n) (hr : r < 2 ^ n) : rot1 n r < 2 ^ n := by
  unfold rot1
  have : 2 ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ']; congr 1; omega
  have := Nat.mod_lt r (show 0 < 2 by norm_num)
  have : min r (2 ^ n - 1 - r) ≤ 2 ^ (n - 1) - 1 := by
    rcases le_total r (2 ^ n - 1 - r) with h | h
    · rw [min_eq_left h]; omega
    · rw [min_eq_right h]; omega
  omega

lemma rot1_mod_two (n r : ℕ) : rot1 n r % 2 = r % 2 := by
  unfold rot1; omega

lemma testBit_rot1_zero (n r : ℕ) : (rot1 n r).testBit 0 = r.testBit 0 := by
  simp only [Nat.testBit_zero, rot1_mod_two]

lemma testBit_rot1_succ (n r t : ℕ) :
    (rot1 n r).testBit (t + 1) = (min r (2 ^ n - 1 - r)).testBit t := by
  rw [← Nat.testBit_div_two]
  congr 1
  unfold rot1; omega

lemma testBit_compl {n r t : ℕ} (hr : r < 2 ^ n) (ht : t < n) :
    (2 ^ n - 1 - r).testBit t = !r.testBit t := by
  rw [show 2 ^ n - 1 - r = 2 ^ n - (r + 1) by omega, Nat.testBit_two_pow_sub_succ hr]
  simp [ht]

lemma testBit_high {n r : ℕ} (hn : 1 ≤ n) (h1 : 2 ^ (n - 1) ≤ r) (h2 : r < 2 ^ n) :
    r.testBit (n - 1) = true := by
  have hp : 2 ^ n = 2 * 2 ^ (n - 1) := by rw [← pow_succ']; congr 1; omega
  have : r = 2 ^ (n - 1) + (r - 2 ^ (n - 1)) := by omega
  rw [this, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow (by omega)]
  rfl

/-- The word of the rotated rank is the rotated word. -/
lemma testBit_gcode_rot1 {n r i : ℕ} (hn : 1 ≤ n) (hr : r < 2 ^ n) (hi : i < n) :
    (gcode (rot1 n r)).testBit (n - 1 - i) = (gcode r).testBit (n - 1 - ((i + 1) % n)) := by
  have hp : 2 ^ n = 2 * 2 ^ (n - 1) := by rw [← pow_succ']; congr 1; omega
  by_cases hlow : r < 2 ^ (n - 1)
  · have hmin : min r (2 ^ n - 1 - r) = r := min_eq_left (by omega)
    by_cases hin : i < n - 1
    · rw [Nat.mod_eq_of_lt (by omega)]
      rw [testBit_gcode, testBit_gcode, show n - 1 - i = (n - 2 - i) + 1 by omega,
        testBit_rot1_succ, testBit_rot1_succ, hmin, show n - 2 - i = n - 1 - (i + 1) by omega]
    · have : i = n - 1 := by omega
      subst this
      rw [show n - 1 + 1 = n by omega, Nat.mod_self, show n - 1 - (n - 1) = 0 by omega,
        testBit_gcode, testBit_gcode, testBit_rot1_zero, show (0:ℕ) + 1 = 1 by rfl,
        show (1:ℕ) = 0 + 1 by rfl, testBit_rot1_succ, hmin, Nat.sub_zero,
        Nat.testBit_lt_two_pow hlow, Nat.testBit_lt_two_pow (show r < 2 ^ (n - 1 + 1) by
          rw [show n - 1 + 1 = n by omega]; exact hr)]
      cases r.testBit 0 <;> rfl
  · push Not at hlow
    have hmin : min r (2 ^ n - 1 - r) = 2 ^ n - 1 - r := min_eq_right (by omega)
    by_cases hin : i < n - 1
    · rw [Nat.mod_eq_of_lt (by omega)]
      rw [testBit_gcode, testBit_gcode, show n - 1 - i = (n - 2 - i) + 1 by omega,
        testBit_rot1_succ, testBit_rot1_succ, hmin, show n - 2 - i = n - 1 - (i + 1) by omega,
        testBit_compl hr (by omega),
        testBit_compl hr (by omega)]
      cases r.testBit (n - 1 - (i + 1)) <;> cases r.testBit (n - 1 - (i + 1) + 1) <;> rfl
    · have : i = n - 1 := by omega
      subst this
      rw [show n - 1 + 1 = n by omega, Nat.mod_self, show n - 1 - (n - 1) = 0 by omega,
        testBit_gcode, testBit_gcode, testBit_rot1_zero, show (0:ℕ) + 1 = 1 by rfl,
        show (1:ℕ) = 0 + 1 by rfl, testBit_rot1_succ, hmin, Nat.sub_zero,
        testBit_compl hr (by omega), testBit_high hn hlow hr,
        Nat.testBit_lt_two_pow (show r < 2 ^ (n - 1 + 1) by
          rw [show n - 1 + 1 = n by omega]; exact hr)]
      cases r.testBit 0 <;> rfl

lemma rot1_iterate_lt {n r : ℕ} (hn : 1 ≤ n) (hr : r < 2 ^ n) (k : ℕ) :
    (rot1 n)^[k] r < 2 ^ n := by
  induction k with
  | zero => exact hr
  | succ k ih => rw [Function.iterate_succ_apply']; exact rot1_lt hn ih

/-- Rotating a Gray word by `k` positions corresponds to iterating `rot1`. -/
lemma rotate_grayWord {n : ℕ} (hn : 1 ≤ n) (r : Rank n) (k : Fin n) :
    rotate k (grayWord r) =
      grayWord ⟨(rot1 n)^[k.val] r.val, rot1_iterate_lt hn r.isLt _⟩ := by
  obtain ⟨k, hk⟩ := k
  simp only
  induction k with
  | zero =>
    funext i; simp [rotate, Nat.mod_eq_of_lt i.isLt]
  | succ k ih =>
    funext i
    have ih' := congrFun (ih (by omega)) ⟨(i.val + 1) % n, Nat.mod_lt _ (by omega)⟩
    simp only [rotate, grayWord_apply] at ih' ⊢
    rw [Function.iterate_succ_apply', testBit_gcode_rot1 hn (rot1_iterate_lt hn r.isLt k) i.isLt,
      ← ih']
    congr 2
    rw [Nat.mod_add_mod]; congr 1; ring

lemma rot1_iterate_period {n r : ℕ} (hn : 1 ≤ n) (hr : r < 2 ^ n) :
    (rot1 n)^[n] r = r := by
  have h := rotate_grayWord hn ⟨r, hr⟩ ⟨0, by omega⟩
  have h2 : ∀ w : Word n, rotate ⟨0, by omega⟩ w = w := by
    intro w; funext i; simp [rotate, Nat.mod_eq_of_lt i.isLt]
  -- Rotation by `n` equals rotation by `0`.
  have key : ∀ m : ℕ, ∀ w : Word n, (fun i : Fin n => w ⟨(i.val + m) % n, Nat.mod_lt _ (by omega)⟩) =
      (fun i : Fin n => w ⟨(i.val + m % n) % n, Nat.mod_lt _ (by omega)⟩) := by
    intro m w; funext i; congr 2; rw [Nat.add_mod (↑i) (m % n), Nat.mod_mod, ← Nat.add_mod]
  -- Iterating `rot1` matches the rotated word, then use injectivity.
  have hrot : ∀ k : ℕ, (fun i : Fin n => grayWord ⟨r, hr⟩ ⟨(i.val + k) % n, Nat.mod_lt _ (by omega)⟩)
      = grayWord ⟨(rot1 n)^[k] r, rot1_iterate_lt hn hr k⟩ := by
    intro k
    induction k with
    | zero => funext i; simp [Nat.mod_eq_of_lt i.isLt]
    | succ k ih =>
      funext i
      have ih' := congrFun ih ⟨(i.val + 1) % n, Nat.mod_lt _ (by omega)⟩
      simp only [grayWord_apply] at ih' ⊢
      rw [Function.iterate_succ_apply', testBit_gcode_rot1 hn (rot1_iterate_lt hn hr k) i.isLt,
        ← ih']
      congr 2
      rw [Nat.mod_add_mod]; congr 1; ring
  have := hrot n
  rw [key n, Nat.mod_self] at this
  have h0 : (fun i : Fin n => grayWord ⟨r, hr⟩ ⟨(i.val + 0) % n, Nat.mod_lt _ (by omega)⟩) =
      grayWord ⟨r, hr⟩ := by funext i; simp [Nat.mod_eq_of_lt i.isLt]
  rw [h0] at this
  have := grayWord_injective n this
  exact (congrArg Fin.val this).symm

lemma rot1_iterate_mod {n r : ℕ} (hn : 1 ≤ n) (hr : r < 2 ^ n) (k : ℕ) :
    (rot1 n)^[k] r = (rot1 n)^[k % n] r := by
  conv_lhs => rw [← Nat.mod_add_div k n]
  rw [Function.iterate_add_apply]
  congr 1
  induction k / n with
  | zero => rfl
  | succ m ih =>
    rw [Nat.mul_succ, Function.iterate_add_apply, rot1_iterate_period hn hr]
    exact ih

/-- The representative condition in terms of `rot1`. -/
lemma isRepresentativeRank_iff {n : ℕ} (hn : 1 ≤ n) (r : Rank n) :
    IsRepresentativeRank r ↔ ∀ k : ℕ, (rot1 n)^[k] r.val ≤ r.val := by
  constructor
  · intro h k
    rw [rot1_iterate_mod hn r.isLt]
    have := h ⟨(rot1 n)^[k % n] r.val, rot1_iterate_lt hn r.isLt _⟩
      ⟨⟨k % n, Nat.mod_lt _ (by omega)⟩, (rotate_grayWord hn r ⟨k % n, Nat.mod_lt _ (by omega)⟩).symm⟩
    exact this
  · rintro h s ⟨k, hk⟩
    rw [rotate_grayWord hn] at hk
    have := grayWord_injective n hk
    rw [this]; exact h _

/-! ### Rotation orbits as signed-doubling orbits -/

lemma two_pow_eq_two_mul {n : ℕ} (hn : 1 ≤ n) : ∃ P, 2 ^ n = 2 * P ∧ 1 ≤ P :=
  ⟨2 ^ (n - 1), by rw [← pow_succ']; congr 1; omega, Nat.one_le_two_pow⟩

lemma rot1_even {n v : ℕ} (hn : 1 ≤ n) (hv : 2 * v < 2 ^ n) :
    rot1 n (2 * v) = 2 * sd (2 ^ n - 1) (2 * v) := by
  obtain ⟨P, hP, hP1⟩ := two_pow_eq_two_mul hn
  unfold rot1 sd
  rw [hP] at hv ⊢
  rw [Nat.mod_eq_of_lt (by omega : 2 * v < 2 * P - 1)]
  omega

lemma rot1_odd {n w : ℕ} (hw1 : 1 ≤ w) (hw : 2 * w ≤ 2 ^ n) :
    rot1 n (2 * w - 1) = 2 * sd (2 ^ n + 1) (2 * w) - 1 := by
  unfold rot1 sd
  generalize 2 ^ n = N at hw ⊢
  rw [Nat.mod_eq_of_lt (by omega : 2 * w < N + 1)]
  omega

lemma sd_pos_of_coprime {M x k : ℕ} (hM : Odd M) (hx1 : 1 ≤ x) (hx : x < M) :
    0 < sd M (2 ^ k * x) := by
  unfold sd
  have hMpos : 0 < M := by omega
  have hnd : ¬ M ∣ 2 ^ k * x := by
    intro hd
    have hcop : Nat.Coprime M (2 ^ k) := by
      apply Nat.Coprime.pow_right
      rw [Nat.coprime_comm, Nat.prime_two.coprime_iff_not_dvd]
      exact fun h => by obtain ⟨m, hm⟩ := hM; omega
    have := hcop.dvd_of_dvd_mul_left hd
    have := Nat.le_of_dvd (by omega) this
    omega
  have h1 : 0 < (2 ^ k * x) % M := Nat.pos_of_ne_zero (fun h => hnd (Nat.dvd_of_mod_eq_zero h))
  have h2 := Nat.mod_lt (2 ^ k * x) hMpos
  omega

/-- Orbit-maximum versus leader: the dictionary of Section 2. -/
lemma orbitMax_iff_leader {M y P : ℕ} (hM : Odd M) (hy1 : 1 ≤ y) (hy : 2 * y ≤ M) (hP : 1 ≤ P)
    (hper : ∀ j, sd M (2 ^ (j + P) * y) = sd M (2 ^ j * y)) :
    (∀ k, sd M (2 ^ k * y) ≤ y) ↔ IsLeader M (M - 2 * y) := by
  have hMpos : 0 < M := by omega
  have hy2 : 2 * y < M := by obtain ⟨m, hm⟩ := hM; omega
  have hshift : ∀ j, sd M (2 ^ j * (M - 2 * y)) = sd M (2 ^ (j + 1) * y) := by
    intro j
    apply sd_of_add_mod hMpos
    have : 2 ^ j * (M - 2 * y) + 2 ^ (j + 1) * y = M * 2 ^ j := by
      rw [pow_succ, Nat.mul_sub]; have : 2 ^ j * (2 * y) ≤ 2 ^ j * M :=
        Nat.mul_le_mul_left _ hy2.le
      rw [show 2 ^ j * 2 * y = 2 ^ j * (2 * y) by ring]; rw [Nat.sub_add_cancel this]; ring
    rw [this]; simp
  constructor
  · intro h
    refine ⟨by omega, fun j => ?_⟩
    rw [hshift]
    classical
    have hex : ∃ c, ∃ k, sd M (2 ^ k * y) = c := ⟨_, 0, rfl⟩
    set σ := Nat.find hex with hσdef
    have hσmin : ∀ k, σ ≤ sd M (2 ^ k * y) := fun k => Nat.find_min' hex ⟨k, rfl⟩
    obtain ⟨k0, hk0⟩ := Nat.find_spec hex
    rw [← hσdef] at hk0
    have hpred : sd M (2 ^ (k0 + P - 1 + 1) * y) = σ := by
      rw [show k0 + P - 1 + 1 = k0 + P by omega, hper, hk0]
    have hz : sd M (2 ^ (k0 + P - 1) * y) ≤ y := h _
    have hsz : sd M (2 * sd M (2 ^ (k0 + P - 1) * y)) = σ := by
      rw [sd_mul_sd M 2 _ hMpos, ← hpred, pow_succ]; ring_nf
    have hσpos : 0 < σ := by rw [← hk0]; exact sd_pos_of_coprime hM hy1 (by omega)
    have hzσ := hσmin (k0 + P - 1)
    generalize sd M (2 ^ (k0 + P - 1) * y) = z at hz hsz hzσ
    have hz2 : 2 * z < M := by omega
    have hcalc : sd M (2 * z) = min (2 * z) (M - 2 * z) := by
      unfold sd; rw [Nat.mod_eq_of_lt hz2]
    rw [hsz] at hcalc
    have hσ' : σ = M - 2 * z := by
      rcases le_total (2 * z) (M - 2 * z) with hh | hh
      · rw [min_eq_left hh] at hcalc; omega
      · rw [min_eq_right hh] at hcalc; exact hcalc
    have := hσmin (j + 1)
    omega
  · rintro ⟨_, hL⟩ k
    by_contra hk
    push Not at hk
    have h1 := hL k
    rw [hshift, pow_succ, show 2 ^ k * 2 * y = 2 * (2 ^ k * y) by ring,
      ← sd_mul_sd M 2 _ hMpos] at h1
    have hz2 : 2 * sd M (2 ^ k * y) ≤ M := sd_le_half M _
    generalize sd M (2 ^ k * y) = z at hk h1 hz2
    have hz3 : 2 * z ≠ M := by obtain ⟨m, hm⟩ := hM; omega
    have : sd M (2 * z) ≤ M - 2 * z := by
      have := sd_le_sub M (2 * z); rwa [Nat.mod_eq_of_lt (by omega)] at this
    omega

lemma rot1_iterate_even {n v : ℕ} (hn : 1 ≤ n) (hv : 2 * v < 2 ^ n) (k : ℕ) :
    (rot1 n)^[k] (2 * v) = 2 * sd (2 ^ n - 1) (2 ^ k * v) := by
  induction k with
  | zero =>
    simp only [Function.iterate_zero, id, pow_zero, one_mul]
    rw [sd_eq_self (M := 2 ^ n - 1) (x := v) (by omega)]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    have h1 := sd_le_half (2 ^ n - 1) (2 ^ k * v)
    have h2 : 2 * sd (2 ^ n - 1) (2 ^ k * v) < 2 ^ n := by omega
    obtain ⟨P, hP, hP1⟩ := two_pow_eq_two_mul hn
    rw [rot1_even hn h2, sd_mul_sd _ _ _ (by omega)]
    congr 2; ring

lemma rot1_iterate_odd {n w : ℕ} (hn : 1 ≤ n) (hw1 : 1 ≤ w) (hw : 2 * w ≤ 2 ^ n) (k : ℕ) :
    (rot1 n)^[k] (2 * w - 1) = 2 * sd (2 ^ n + 1) (2 ^ k * w) - 1 := by
  have hodd : Odd (2 ^ n + 1) := by
    obtain ⟨P, hP, _⟩ := two_pow_eq_two_mul hn; exact ⟨P, by omega⟩
  induction k with
  | zero =>
    simp only [Function.iterate_zero, id, pow_zero, one_mul]
    rw [sd_eq_self (M := 2 ^ n + 1) (x := w) (by omega)]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    have hpos : 1 ≤ sd (2 ^ n + 1) (2 ^ k * w) := sd_pos_of_coprime hodd hw1 (by omega)
    have h1 := sd_le_half (2 ^ n + 1) (2 ^ k * w)
    have h2 : 2 * sd (2 ^ n + 1) (2 ^ k * w) ≤ 2 ^ n := by
      obtain ⟨P, hP, _⟩ := two_pow_eq_two_mul hn; omega
    rw [rot1_odd hpos h2, sd_mul_sd _ _ _ (by omega)]
    congr 3; ring

/-- Even representatives: `0` or `2^n - 1 - s` for a leader `s` modulo `2^n - 1`. -/
lemma isRep_even_iff {n : ℕ} (hn : 1 ≤ n) {v : ℕ} (hv1 : 1 ≤ v) (hv : 2 * v < 2 ^ n) :
    (∀ k, (rot1 n)^[k] (2 * v) ≤ 2 * v) ↔ IsLeader (2 ^ n - 1) (2 ^ n - 1 - 2 * v) := by
  obtain ⟨P, hP, hP1⟩ := two_pow_eq_two_mul hn
  have hodd : Odd (2 ^ n - 1) := ⟨P - 1, by omega⟩
  rw [← orbitMax_iff_leader hodd hv1 (by omega) hn (fun j => sd_pow_period_sub n j v)]
  refine forall_congr' fun k => ?_
  rw [rot1_iterate_even hn hv]; omega

/-- Odd representatives: `2^n - s` for a leader `s` modulo `2^n + 1`. -/
lemma isRep_odd_iff {n : ℕ} (hn : 1 ≤ n) {w : ℕ} (hw1 : 1 ≤ w) (hw : 2 * w ≤ 2 ^ n) :
    (∀ k, (rot1 n)^[k] (2 * w - 1) ≤ 2 * w - 1) ↔ IsLeader (2 ^ n + 1) (2 ^ n + 1 - 2 * w) := by
  obtain ⟨P, hP, hP1⟩ := two_pow_eq_two_mul hn
  have hodd : Odd (2 ^ n + 1) := ⟨P, by omega⟩
  rw [← orbitMax_iff_leader hodd hw1 (by omega) hn (fun j => sd_pow_period_add n j w)]
  refine forall_congr' fun k => ?_
  rw [rot1_iterate_odd hn hw1 hw]
  have : 1 ≤ sd (2 ^ n + 1) (2 ^ k * w) :=
    sd_pos_of_coprime hodd hw1 (by omega)
  omega

/-! ### Hamming distance -/

lemma gcode_two_pow_sub_one (e : ℕ) (he : 1 ≤ e) : gcode (2 ^ e - 1) = 2 ^ (e - 1) := by
  apply Nat.eq_of_testBit_eq; intro t
  rw [testBit_gcode, Nat.testBit_two_pow_sub_one, Nat.testBit_two_pow_sub_one, Nat.testBit_two_pow]
  by_cases h : t = e - 1
  · subst h; simp; omega
  · rcases lt_or_gt_of_ne h with h | h
    · simp [show t < e by omega, show t + 1 < e by omega, show e - 1 ≠ t by omega]
    · simp [show ¬ t < e by omega, show ¬ t + 1 < e by omega, show e - 1 ≠ t by omega]

/-- Ranks whose XOR is a block of trailing ones give words differing in one bit. -/
lemma differInOneBit_of_xor {n : ℕ} (r s : Rank n) {e : ℕ} (he1 : 1 ≤ e) (hen : e ≤ n)
    (h : r.val ^^^ s.val = 2 ^ e - 1) : DifferInOneBit (grayWord r) (grayWord s) := by
  have hx : gcode r.val ^^^ gcode s.val = 2 ^ (e - 1) := by
    rw [← gcode_xor, h, gcode_two_pow_sub_one e he1]
  have hbit : ∀ t, ((gcode r.val).testBit t ^^ (gcode s.val).testBit t) = decide (e - 1 = t) := by
    intro t
    have := congrArg (fun y => y.testBit t) hx
    simpa [Nat.testBit_xor, Nat.testBit_two_pow] using this
  refine ⟨⟨n - e, by omega⟩, ?_, ?_⟩
  · simp only [grayWord_apply]
    have := hbit (n - 1 - (n - e))
    rw [show e - 1 = n - 1 - (n - e) by omega] at this
    revert this
    cases (gcode r.val).testBit (n - 1 - (n - e)) <;>
      cases (gcode s.val).testBit (n - 1 - (n - e)) <;> simp
  · intro j hj
    simp only [grayWord_apply]
    have := hbit (n - 1 - j.val)
    have hne : e - 1 ≠ n - 1 - j.val := by
      intro h'; apply hj; apply Fin.ext; simp; omega
    simp only [hne, decide_false] at this
    revert this
    cases (gcode r.val).testBit (n - 1 - j.val) <;>
      cases (gcode s.val).testBit (n - 1 - j.val) <;> simp

/-- A rank fixed by rotation has a constant word. -/
lemma grayWord_const_of_rot1_fixed {n : ℕ} (hn : 1 ≤ n) (r : Rank n) (h : rot1 n r.val = r.val)
    (i : Fin n) : grayWord r i = grayWord r ⟨0, by omega⟩ := by
  have step : ∀ i : Fin n, grayWord r ⟨(i.val + 1) % n, Nat.mod_lt _ (by omega)⟩ = grayWord r i := by
    intro i
    simp only [grayWord_apply]
    rw [← testBit_gcode_rot1 hn r.isLt i.isLt, h]
  obtain ⟨i, hi⟩ := i
  induction i with
  | zero => rfl
  | succ i ih =>
    have := step ⟨i, by omega⟩
    simp only [Nat.mod_eq_of_lt hi] at this
    rw [this, ih (by omega)]

lemma grayWord_zero {n : ℕ} (_hn : 1 ≤ n) (i : Fin n) :
    grayWord (⟨0, Nat.two_pow_pos n⟩ : Rank n) i = false := by
  simp [grayWord_apply, gcode]

end GrayNecklaces
