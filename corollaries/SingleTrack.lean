import GrayNecklaces

/-!
# The Degni–Drisko property in Dzoba's form

Theorem A of C. Dzoba, *Optimal single-track Gray codes from Gray-ordered necklaces*
(arXiv:2610.24758), says that at prime length `n ≥ 7`, if consecutive necklaces, listed by the rank
of their least-rank representatives, are adjacent, then a single-track Gray code of length `n` and
period `2^n - 2` exists.  His Lean formalization states the hypothesis as `STGC.DDProperty n`.  This
file states the same property with its own definitions (`DDProperty` below) and proves it at every
odd prime from the exported theorem `OddPrimeDegniDrisko`.

The definitions are written to match those in his Lean files.  Words are `ZMod n → Bool`, with
position `0` most significant, and `rot k w i = w (i + k)`.  `rank w` is the position of `w` in the
binary reflected Gray code, the number whose binary digits, most significant first, are the prefix
parities `w 0 xor … xor w i`.  `IsFirstOcc w` says that `w` is nonconstant and no rotation of `w`
has smaller rank.  `NecklaceAdj u v` says that some rotation of `v` is at Hamming distance one from
`u`.  `DDProperty n` says that first occurrences consecutive in rank order are adjacent.

Proof outline.  `rank (toW p r) = r` for the BRGC word `toW p r` of rank `r`, and rotating by one
acts on ranks by `rot1`.  The least-rank first occurrences are the ranks `2σ - 1` and `2σ`, `σ` a
positive leader modulo `2^p - 1`.  Consecutive ones are `(2σ - 1, 2σ)`, consecutive BRGC ranks, or
`(2σ, 2τ - 1)` for consecutive leaders `σ < τ`.  In the second case the XOR
`2 (σ xor (τ - 1)) + 1` is a block of ones (`XorCore`), which `xorCore_of_main` derives from the
exported theorem.  Either way the two words differ in one bit (rotation `0`).

`ddProperty` takes only `Tiozzo.Theorem87` and `Tiozzo.TuningNesting`.  `ddProperty_of_main` takes
`Tiozzo.Theorem87` and the exported statement.
-/

namespace GrayNecklaces.SingleTrack

open Tiozzo

/-! ### Definitions -/

/-- A word of length `n`, with positions in `ZMod n` so that rotation is cyclic. -/
abbrev CWord (n : ℕ) := ZMod n → Bool

/-- Rotation by `k` positions. -/
def rot {n : ℕ} (k : ZMod n) (w : CWord n) : CWord n := fun i => w (i + k)

/-- The constant words `0ⁿ` and `1ⁿ`. -/
def IsConst {n : ℕ} (w : CWord n) : Prop := ∀ i j, w i = w j

/-- The prefix parity `w 0 xor w 1 xor … xor w i`. -/
def prefixParity {n : ℕ} (w : CWord n) : ℕ → Bool
  | 0 => w 0
  | i + 1 => prefixParity w i ^^ w ((i + 1 : ℕ) : ZMod n)

/-- The number whose binary digits, most significant first, are the first `m` prefix parities. -/
def rankUpTo {n : ℕ} (w : CWord n) : ℕ → ℕ
  | 0 => 0
  | m + 1 => 2 * rankUpTo w m + if prefixParity w m then 1 else 0

/-- The position of `w` in the binary reflected Gray code of length `n`. -/
def rank {n : ℕ} (w : CWord n) : ℕ := rankUpTo w n

/-- `w` is the first occurrence of its necklace, meaning it is nonconstant and of least rank among
its rotations. -/
def IsFirstOcc {n : ℕ} (w : CWord n) : Prop := ¬ IsConst w ∧ ∀ k : ZMod n, rank w ≤ rank (rot k w)

/-- Adjacent necklaces.  Some rotation of `v` differs from `u` in exactly one position. -/
def NecklaceAdj {n : ℕ} [NeZero n] (u v : CWord n) : Prop :=
  ∃ k : ZMod n, hammingDist u (rot k v) = 1

/-- **The Degni–Drisko property in Dzoba's form.**  First occurrences that are consecutive in rank
order lie in adjacent necklaces. -/
def DDProperty (n : ℕ) [NeZero n] : Prop :=
  ∀ u v : CWord n, IsFirstOcc u → IsFirstOcc v → rank u < rank v →
    (∀ x : CWord n, IsFirstOcc x → ¬ (rank u < rank x ∧ rank x < rank v)) → NecklaceAdj u v

/-! ### Elementary facts -/

lemma rot_rot {n : ℕ} (a b : ZMod n) (w : CWord n) : rot a (rot b w) = rot (a + b) w := by
  funext i; simp [rot, add_assoc]

@[simp] lemma rot_zero {n : ℕ} (w : CWord n) : rot 0 w = w := by
  funext i; simp [rot]

lemma rankUpTo_lt {n : ℕ} (w : CWord n) (m : ℕ) : rankUpTo w m < 2 ^ m := by
  induction m with
  | zero => simp [rankUpTo]
  | succ m ih => rw [rankUpTo, pow_succ]; split_ifs <;> omega

lemma rank_lt_pow {n : ℕ} (w : CWord n) : rank w < 2 ^ n := rankUpTo_lt w n

lemma hammingDist_eq_one_of {n : ℕ} [NeZero n] {u v : CWord n} (a : ZMod n)
    (h : ∀ i, u i ≠ v i ↔ i = a) : hammingDist u v = 1 := by
  unfold hammingDist
  rw [Finset.card_eq_one]
  refine ⟨a, ?_⟩
  ext i
  rw [Finset.mem_filter, Finset.mem_singleton]
  exact ⟨fun hi => (h i).mp hi.2, fun hi => ⟨Finset.mem_univ _, (h i).mpr hi⟩⟩

lemma eq_natCast_iff {n : ℕ} [NeZero n] (i : ZMod n) {c : ℕ} (hc : c < n) :
    i = (c : ZMod n) ↔ i.val = c := by
  constructor
  · rintro rfl; rw [ZMod.val_natCast, Nat.mod_eq_of_lt hc]
  · intro h; rw [← h, ZMod.natCast_zmod_val]

/-! ### The word of a rank -/

/-- The BRGC word of rank `r` (position `0` is the most significant). -/
def toW (p r : ℕ) : CWord p := fun i => (gcode r).testBit (p - 1 - i.val)

lemma toW_natCast {p : ℕ} [NeZero p] (r : ℕ) {j : ℕ} (hj : j < p) :
    toW p r (j : ZMod p) = (gcode r).testBit (p - 1 - j) := by
  simp [toW, ZMod.val_natCast, Nat.mod_eq_of_lt hj]

lemma prefixParity_toW {p : ℕ} [NeZero p] {r : ℕ} (hr : r < 2 ^ p) {i : ℕ} (hi : i < p) :
    prefixParity (toW p r) i = r.testBit (p - 1 - i) := by
  induction i with
  | zero =>
    have h0 : toW p r 0 = (gcode r).testBit (p - 1) := by
      have := toW_natCast (p := p) r (j := 0) hi
      simpa using this
    rw [prefixParity, h0, testBit_gcode, show p - 1 + 1 = p by omega, Nat.testBit_lt_two_pow hr,
      Nat.sub_zero, Bool.xor_false]
  | succ i ih =>
    rw [prefixParity, ih (by omega), toW_natCast r hi, testBit_gcode,
      show p - 1 - (i + 1) + 1 = p - 1 - i by omega]
    cases r.testBit (p - 1 - i) <;> cases r.testBit (p - 1 - (i + 1)) <;> rfl

lemma rankUpTo_toW {p : ℕ} [NeZero p] {r : ℕ} (hr : r < 2 ^ p) {m : ℕ} (hm : m ≤ p) :
    rankUpTo (toW p r) m = r / 2 ^ (p - m) := by
  induction m with
  | zero => rw [rankUpTo, Nat.sub_zero, Nat.div_eq_of_lt hr]
  | succ m ih =>
    rw [rankUpTo, ih (by omega), prefixParity_toW hr (by omega)]
    obtain ⟨k, hk⟩ : ∃ k, p - m = k + 1 := ⟨p - m - 1, by omega⟩
    rw [hk, show p - (m + 1) = k by omega, show p - 1 - m = k by omega,
      Nat.testBit_eq_decide_div_mod_eq, pow_succ, ← Nat.div_div_eq_div_mul]
    have := Nat.div_add_mod (r / 2 ^ k) 2
    have h2 := Nat.mod_lt (r / 2 ^ k) (show 0 < 2 by norm_num)
    split_ifs with h <;> simp at h <;> omega

/-- The rank of the BRGC word of rank `r` is `r`. -/
lemma rank_toW {p : ℕ} [NeZero p] {r : ℕ} (hr : r < 2 ^ p) : rank (toW p r) = r := by
  rw [rank, rankUpTo_toW hr le_rfl, Nat.sub_self, pow_zero, Nat.div_one]

/-- Every word is the BRGC word of its rank. -/
lemma eq_toW {p : ℕ} [NeZero p] (w : CWord p) : w = toW p (rank w) := by
  have hinj : Function.Injective (fun r : Fin (2 ^ p) => toW p r.val) := by
    intro a b h
    have := congrArg rank h
    simp only at this
    rw [rank_toW a.isLt, rank_toW b.isLt] at this
    exact Fin.ext this
  have hcard : Fintype.card (Fin (2 ^ p)) = Fintype.card (CWord p) := by
    simp [ZMod.card]
  obtain ⟨r, hr⟩ := ((Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, hcard⟩).2 w
  simp only at hr
  rw [← hr, rank_toW r.isLt]

/-! ### Rotation -/

lemma rot_one_toW {p : ℕ} (hp : 1 < p) {r : ℕ} (hr : r < 2 ^ p) :
    haveI : NeZero p := ⟨by omega⟩
    rot 1 (toW p r) = toW p (rot1 p r) := by
  have : NeZero p := ⟨by omega⟩
  have : Fact (1 < p) := ⟨hp⟩
  funext i
  simp only [rot, toW]
  rw [testBit_gcode_rot1 (by omega) hr (ZMod.val_lt i), ZMod.val_add, ZMod.val_one]

lemma rot_natCast_toW {p : ℕ} (hp : 1 < p) {r : ℕ} (hr : r < 2 ^ p) (m : ℕ) :
    haveI : NeZero p := ⟨by omega⟩
    rot (m : ZMod p) (toW p r) = toW p ((rot1 p)^[m] r) := by
  have : NeZero p := ⟨by omega⟩
  induction m with
  | zero => simp
  | succ m ih =>
    have e : ((m + 1 : ℕ) : ZMod p) = 1 + (m : ZMod p) := by push_cast; ring
    rw [e, ← rot_rot, ih, rot_one_toW hp (rot1_iterate_lt (by omega) hr m),
      Function.iterate_succ_apply']

lemma rank_rot_toW {p : ℕ} (hp : 1 < p) {r : ℕ} (hr : r < 2 ^ p) (k : ZMod p) :
    haveI : NeZero p := ⟨by omega⟩
    rank (rot k (toW p r)) = (rot1 p)^[k.val] r := by
  have : NeZero p := ⟨by omega⟩
  conv_lhs => rw [← ZMod.natCast_zmod_val k]
  rw [rot_natCast_toW hp hr, rank_toW (rot1_iterate_lt (by omega) hr _)]

/-! ### Constant words -/

lemma const_of_fixed {p : ℕ} (hp : 1 < p) {r : ℕ} (hr : r < 2 ^ p) (h : rot1 p r = r) :
    IsConst (toW p r) := by
  have : NeZero p := ⟨by omega⟩
  have hrot := rot_one_toW hp hr
  rw [h] at hrot
  have step : ∀ i : ZMod p, toW p r (i + 1) = toW p r i := fun i => congrFun hrot i
  have hall : ∀ m : ℕ, toW p r (m : ZMod p) = toW p r 0 := by
    intro m; induction m with
    | zero => simp
    | succ m ih => rw [Nat.cast_succ, step, ih]
  intro i j
  rw [← ZMod.natCast_zmod_val i, ← ZMod.natCast_zmod_val j, hall, hall]

lemma fixed_of_const {p : ℕ} (hp : 1 < p) {r : ℕ} (hr : r < 2 ^ p) (h : IsConst (toW p r)) :
    rot1 p r = r := by
  have : NeZero p := ⟨by omega⟩
  have hrot := rot_one_toW hp hr
  have : rot 1 (toW p r) = toW p r := by funext i; exact h _ _
  rw [this] at hrot
  have := congrArg rank hrot
  rwa [rank_toW hr, rank_toW (rot1_lt (by omega) hr), eq_comm] at this

/-- The ranks fixed by rotation: `0` and `(2^(p+1) - 1)/3`. -/
lemma fixed_iff {p r : ℕ} (hmod : 2 ^ p % 3 = 2) (h : rot1 p r = r) : r = 0 ∨ 3 * r = 2 * 2 ^ p - 1 := by
  unfold rot1 at h
  rcases le_total r (2 ^ p - 1 - r) with hh | hh
  · rw [min_eq_left hh] at h; left; omega
  · rw [min_eq_right hh] at h; right; omega

/-! ### First occurrences -/

lemma isFirstOcc_iff {p : ℕ} (hp : 1 < p) {r : ℕ} (hr : r < 2 ^ p) :
    IsFirstOcc (toW p r) ↔ ¬ IsConst (toW p r) ∧ ∀ m, r ≤ (rot1 p)^[m] r := by
  have : NeZero p := ⟨by omega⟩
  unfold IsFirstOcc
  refine and_congr_right fun _ => ?_
  constructor
  · intro h m
    have := h (m : ZMod p)
    rw [rank_rot_toW hp hr, rank_toW hr, ZMod.val_natCast, ← rot1_iterate_mod (by omega) hr] at this
    exact this
  · intro h k
    rw [rank_rot_toW hp hr, rank_toW hr]; exact h _

lemma min_even_iff {p v : ℕ} (hp : 1 ≤ p) (hv1 : 1 ≤ v) (hv : 2 * v < 2 ^ p) :
    (∀ m, 2 * v ≤ (rot1 p)^[m] (2 * v)) ↔ IsLeader (2 ^ p - 1) v := by
  unfold IsLeader
  simp only [rot1_iterate_even hp hv]
  constructor
  · intro h; exact ⟨by omega, fun j => by have := h j; omega⟩
  · intro h m; have := h.2 m; omega

lemma min_odd_iff {p w : ℕ} (hp : 1 ≤ p) (hw1 : 1 ≤ w) (hw : 2 * w ≤ 2 ^ p) :
    (∀ m, 2 * w - 1 ≤ (rot1 p)^[m] (2 * w - 1)) ↔ IsLeader (2 ^ p + 1) w := by
  have hodd : Odd (2 ^ p + 1) := by
    obtain ⟨P, hP, _⟩ := two_pow_eq_two_mul hp; exact ⟨P, by omega⟩
  unfold IsLeader
  simp only [rot1_iterate_odd hp hw1 hw]
  constructor
  · intro h; refine ⟨by omega, fun j => ?_⟩
    have := h j
    have := sd_pos_of_coprime hodd hw1 (k := j) (by omega)
    omega
  · intro h m; have := h.2 m; omega

section Prime

variable {p : ℕ} (h87 : Theorem87) (hp : p.Prime) (hodd : Odd p)
include h87 hp hodd

omit h87 in
lemma p_ge_three : 3 ≤ p := by
  have := hp.two_le
  rcases Nat.lt_or_ge p 3 with h | h
  · have : p = 2 := by omega
    subst this; exact absurd hodd (by decide)
  · exact h

omit h87 in
lemma odd_sub : Odd (2 ^ p - 1) := by
  have := p_ge_three hp hodd
  have : 2 ^ p = 2 * 2 ^ (p - 1) := by rw [← pow_succ']; congr 1; omega
  have : 1 ≤ 2 ^ (p - 1) := Nat.one_le_two_pow
  exact ⟨2 ^ (p - 1) - 1, by omega⟩

omit h87 in
lemma odd_add : Odd (2 ^ p + 1) := by
  have := p_ge_three hp hodd
  have : 2 ^ p = 2 * 2 ^ (p - 1) := by rw [← pow_succ']; congr 1; omega
  exact ⟨2 ^ (p - 1), by omega⟩

/-- Leaders modulo `2^p - 1` give two first occurrences, `2σ - 1` and `2σ`. -/
lemma firstOcc_of_leader {σ : ℕ} (hσ : IsLeader (2 ^ p - 1) σ) :
    1 ≤ σ ∧ 2 * σ < 2 ^ p ∧ IsFirstOcc (toW p (2 * σ)) ∧
      IsFirstOcc (toW p (2 * σ - 1)) := by
  have hp1 : 1 < p := hp.one_lt
  obtain ⟨hσo, hσ3⟩ := hσ.bounds (odd_sub hp hodd)
  have hmod := two_pow_odd_mod_three hodd
  have h1 : 1 ≤ σ := hσ.1
  have hlt : 2 * σ < 2 ^ p := by omega
  refine ⟨h1, hlt, ?_, ?_⟩
  · rw [isFirstOcc_iff hp1 hlt]
    refine ⟨fun hc => ?_, (min_even_iff hp1.le h1 hlt).mpr hσ⟩
    rcases fixed_iff hmod (fixed_of_const hp1 hlt hc) with h | h <;> omega
  · have hlt' : 2 * σ - 1 < 2 ^ p := by omega
    rw [isFirstOcc_iff hp1 hlt']
    refine ⟨fun hc => ?_, (min_odd_iff hp1.le h1 hlt.le).mpr
      ((leader_sub_iff_add h87 hp hσo (by omega)).mp hσ)⟩
    rcases fixed_iff hmod (fixed_of_const hp1 hlt' hc) with h | h <;> omega

/-- Every first occurrence has rank `2σ - 1` or `2σ` for a leader `σ` modulo `2^p - 1`. -/
lemma leader_of_firstOcc {r : ℕ} (hr : r < 2 ^ p) (h : IsFirstOcc (toW p r)) :
    ∃ σ, IsLeader (2 ^ p - 1) σ ∧ (r = 2 * σ ∨ r = 2 * σ - 1) := by
  have hp1 : 1 < p := hp.one_lt
  rw [isFirstOcc_iff hp1 hr] at h
  obtain ⟨hnc, hmin⟩ := h
  have hmod := two_pow_odd_mod_three hodd
  rcases Nat.even_or_odd r with ⟨v, hv⟩ | ⟨w, hw⟩
  · have hr2 : r = 2 * v := by omega
    rcases Nat.eq_zero_or_pos v with h0 | h0
    · exact absurd (const_of_fixed hp1 hr (by rw [hr2, h0]; exact rot1_zero p)) hnc
    · subst hr2
      exact ⟨v, (min_even_iff hp1.le h0 hr).mp hmin, Or.inl rfl⟩
  · have hr2 : r = 2 * (w + 1) - 1 := by omega
    subst hr2
    have hL := (min_odd_iff hp1.le (by omega) (by omega)).mp hmin
    obtain ⟨hσo, hσ3⟩ := hL.bounds (odd_add hp hodd)
    by_cases h3 : 3 * (w + 1) = 2 ^ p + 1
    · exfalso; apply hnc
      apply const_of_fixed hp1 hr
      unfold rot1
      rw [min_eq_right (by omega)]; omega
    · exact ⟨w + 1, (leader_sub_iff_add h87 hp hσo (by omega)).mpr hL, Or.inr rfl⟩

end Prime

/-! ### Bit arithmetic -/

lemma succ_xor (r : ℕ) : ∃ e, r ^^^ (r + 1) = 2 ^ (e + 1) - 1 := by
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (n := r + 1) (by omega)
  refine ⟨k, ?_⟩
  have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have := reflect_xor (σ := r) (τ := r + 2) (e := k) (c := m) hm (by rw [mul_comm m]; linarith)
    (by rw [mul_comm m]; linarith) (by rw [mul_comm m]; linarith)
  simpa using this

lemma double_xor (x y : ℕ) : (2 * x) ^^^ (2 * y + 1) = 2 * (x ^^^ y) + 1 := by
  apply Nat.eq_of_testBit_eq; intro t
  rw [show 2 * x = 2 ^ 1 * x + 0 by ring, show 2 * y + 1 = 2 ^ 1 * y + 1 by ring,
    show 2 * (x ^^^ y) + 1 = 2 ^ 1 * (x ^^^ y) + 1 by ring, Nat.testBit_xor,
    Nat.testBit_two_pow_mul_add _ (by norm_num), Nat.testBit_two_pow_mul_add _ (by norm_num),
    Nat.testBit_two_pow_mul_add _ (by norm_num)]
  split_ifs with ht
  · have : t = 0 := by omega
    subst this; simp
  · rw [Nat.testBit_xor]

/-- Ranks whose XOR is a block of ones give words at Hamming distance one. -/
lemma hammingDist_toW {p : ℕ} [NeZero p] {r s e : ℕ} (hr : r < 2 ^ p) (hs : s < 2 ^ p)
    (he : 1 ≤ e) (h : r ^^^ s = 2 ^ e - 1) : hammingDist (toW p r) (toW p s) = 1 := by
  have hen : e ≤ p := by
    have hx := Nat.xor_lt_two_pow hr hs
    rw [h] at hx
    by_contra hh; push Not at hh
    have : 2 ^ p < 2 ^ e := Nat.pow_lt_pow_right (by norm_num) hh
    omega
  obtain ⟨i0, hne, heq⟩ := differInOneBit_of_xor (n := p) ⟨r, hr⟩ ⟨s, hs⟩ he hen h
  simp only [grayWord_apply] at hne heq
  apply hammingDist_eq_one_of (i0.val : ZMod p)
  intro i
  rw [eq_natCast_iff i i0.isLt]
  constructor
  · intro hi
    by_contra hh
    exact hi (heq ⟨i.val, ZMod.val_lt i⟩ (fun h' => hh (congrArg Fin.val h')))
  · intro hi
    have : (⟨i.val, ZMod.val_lt i⟩ : Fin p) = i0 := Fin.ext hi
    simp only [toW]; rw [← this] at hne; exact hne

/-! ### The Degni–Drisko property -/

/-- Consecutive positive leaders `σ < τ` modulo `2^p - 1` have `σ xor (τ - 1)` a block of ones. -/
def XorCore (p : ℕ) : Prop :=
  ∀ σ τ : ℕ, IsLeader (2 ^ p - 1) σ → IsLeader (2 ^ p - 1) τ → σ < τ →
    (∀ t, σ < t → t < τ → ¬ IsLeader (2 ^ p - 1) t) → ∃ e, σ ^^^ (τ - 1) = 2 ^ (e + 1) - 1

lemma gcode_lt {p x : ℕ} (hx : x < 2 ^ p) : gcode x < 2 ^ p :=
  Nat.xor_lt_two_pow hx (by rw [Nat.shiftRight_eq_div_pow]; exact lt_of_le_of_lt (Nat.div_le_self _ _) hx)

/-- Words differing in one bit have ranks whose XOR is a block of ones. -/
lemma xor_of_differInOneBit {p : ℕ} (r s : Rank p) (h : DifferInOneBit (grayWord r) (grayWord s)) :
    ∃ e, r.val ^^^ s.val = 2 ^ (e + 1) - 1 := by
  obtain ⟨i, hne, heq⟩ := h
  have hi := i.isLt
  have hx : gcode r.val ^^^ gcode s.val = 2 ^ (p - 1 - i.val) := by
    apply Nat.eq_of_testBit_eq; intro t
    rw [Nat.testBit_xor, Nat.testBit_two_pow]
    by_cases ht : t < p
    · by_cases hti : t = p - 1 - i.val
      · subst hti
        simp only [grayWord_apply] at hne
        simp only [decide_true]
        revert hne
        cases (gcode r.val).testBit (p - 1 - i.val) <;>
          cases (gcode s.val).testBit (p - 1 - i.val) <;> simp
      · have hne' : (⟨p - 1 - t, by omega⟩ : Fin p) ≠ i := by
          intro h'; apply hti; rw [← h']; simp only; omega
        have hj := heq _ hne'
        simp only [grayWord_apply] at hj
        rw [show p - 1 - (p - 1 - t) = t by omega] at hj
        rw [hj, Bool.xor_self]
        simp only [false_eq_decide_iff]; omega
    · have hb : ∀ x : ℕ, x < 2 ^ p → (gcode x).testBit t = false := fun x hx =>
        Nat.testBit_lt_two_pow (lt_of_lt_of_le (gcode_lt hx)
          (Nat.pow_le_pow_right (by norm_num) (by omega)))
      rw [hb _ r.isLt, hb _ s.isLt]
      simp only [Bool.xor_false, false_eq_decide_iff]; omega
  refine ⟨p - 1 - i.val, gcode_inj ?_⟩
  rw [gcode_xor, hx, gcode_two_pow_sub_one _ (by omega), Nat.add_sub_cancel]

/-- **Our exported theorem supplies the XOR form of the reflection property.**  For consecutive
leaders `σ < τ` the ranks `2^p - 1 - σ` and `2^p - τ` are consecutive representatives, so the
theorem makes their words differ in one bit. -/
theorem xorCore_of_main (h87 : Theorem87) (hmain : OddPrimeDegniDrisko) {p : ℕ} (hp : p.Prime)
    (hodd : Odd p) : XorCore p := by
  intro σ τ hσ hτ hlt hnone
  have hp1 : 1 ≤ p := hp.one_lt.le
  have hp3 := p_ge_three hp hodd
  have hmod := two_pow_odd_mod_three hodd
  have hMsub := odd_sub hp hodd
  have hMadd := odd_add hp hodd
  have hP : 2 ^ p = 2 * 2 ^ (p - 1) := by rw [← pow_succ']; congr 1; omega
  have hle : ∀ x, IsLeader (2 ^ p - 1) x → 6 * x ≤ 2 ^ p - 2 :=
    fun x h => leader_le_max h87 hp hp3 hodd h
  obtain ⟨hσo, _⟩ := hσ.bounds hMsub
  obtain ⟨hτo, _⟩ := hτ.bounds hMsub
  have hσ1 := hσ.1
  have hτle := hle τ hτ
  have hστ : σ + 2 ≤ τ := by obtain ⟨a, ha⟩ := hσo; obtain ⟨b, hb⟩ := hτo; omega
  set r : Rank p := ⟨2 ^ p - 1 - σ, by omega⟩ with hr
  set s : Rank p := ⟨2 ^ p - τ, by omega⟩ with hs
  have hrep_r : IsRepresentativeRank r := by
    rw [isRep_iff hp1]; right; left
    obtain ⟨a, ha⟩ := hσo
    refine ⟨⟨2 ^ (p - 1) - 1 - a, by simp only [r]; omega⟩, by simp only [r]; omega, ?_⟩
    simp only [r]; rw [show 2 ^ p - 1 - (2 ^ p - 1 - σ) = σ by omega]; exact hσ
  have hrep_s : IsRepresentativeRank s := by
    rw [isRep_iff hp1]; right; right
    obtain ⟨b, hb⟩ := hτo
    refine ⟨⟨2 ^ (p - 1) - b - 1, by simp only [s]; omega⟩, ?_⟩
    simp only [s]; rw [show 2 ^ p - (2 ^ p - τ) = τ by omega]
    exact (leader_sub_iff_add h87 hp ⟨b, hb⟩ (by omega)).mp hτ
  have hsr : s < r := by rw [Fin.lt_def]; simp only [r, s]; omega
  have hbet : ∀ t : Rank p, s < t → t < r → ¬ IsRepresentativeRank t := by
    intro t h1 h2 ht
    rw [Fin.lt_def] at h1 h2
    simp only [r, s] at h1 h2
    have htlt := t.isLt
    rcases (isRep_iff hp1 t).mp ht with h0 | ⟨_, _, hL'⟩ | ⟨_, hL'⟩
    · omega
    · exact hnone _ (by omega) (by omega) hL'
    · obtain ⟨ho', h3'⟩ := hL'.bounds hMadd
      by_cases h3 : 3 * (2 ^ p - t.val) = 2 ^ p + 1
      · omega
      · have hL'' := (leader_sub_iff_add h87 hp ho' (by omega)).mpr hL'
        exact hnone _ (by omega) (by omega) hL''
  rcases hmain p hp hodd r s ⟨hsr, hrep_r, hrep_s, hbet⟩ with ⟨_, hz⟩ | hd
  · exfalso
    have hg : gcode s.val = 0 := by
      apply Nat.eq_of_testBit_eq; intro t
      rw [Nat.zero_testBit]
      by_cases ht : t < p
      · have := hz ⟨p - 1 - t, by omega⟩
        simp only [grayWord_apply] at this
        rwa [show p - 1 - (p - 1 - t) = t by omega] at this
      · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (gcode_lt s.isLt)
          (Nat.pow_le_pow_right (by norm_num) (by omega)))
    have := gcode_eq_zero hg
    simp only [s] at this; omega
  · obtain ⟨e, he⟩ := xor_of_differInOneBit r s hd
    refine ⟨e, ?_⟩
    rw [← he]; simp only [r, s]
    rw [show 2 ^ p - τ = 2 ^ p - 1 - (τ - 1) by omega, compl_xor p rfl (by omega) (by omega)]

/-- The Degni–Drisko property in Dzoba's form from the XOR form of the reflection property. -/
theorem ddProperty_of_xorCore (h87 : Theorem87) {p : ℕ} [NeZero p] (hp : p.Prime) (hodd : Odd p)
    (hx : XorCore p) : DDProperty p := by
  intro u v hu hv huv hbet
  have hp1 : 1 < p := hp.one_lt
  set a := rank u with ha
  set b := rank v with hb
  have har : a < 2 ^ p := rank_lt_pow u
  have hbr : b < 2 ^ p := rank_lt_pow v
  have hu' : u = toW p a := eq_toW u
  have hv' : v = toW p b := eq_toW v
  rw [hu'] at hu ⊢
  rw [hv'] at hv ⊢
  -- no first occurrence strictly between, in terms of ranks
  have hbet' : ∀ c, c < 2 ^ p → IsFirstOcc (toW p c) → ¬ (a < c ∧ c < b) := by
    intro c hc hfo
    have := hbet _ hfo
    rwa [rank_toW hc] at this
  refine ⟨0, ?_⟩
  rw [rot_zero]
  obtain ⟨σ, hσ, hσa⟩ := leader_of_firstOcc h87 hp hodd har hu
  obtain ⟨τ, hτ, hτb⟩ := leader_of_firstOcc h87 hp hodd hbr hv
  obtain ⟨hσ1, hσlt, hfo2σ, -⟩ := firstOcc_of_leader h87 hp hodd hσ
  obtain ⟨hτ1, hτlt, -, hfo2τ1⟩ := firstOcc_of_leader h87 hp hodd hτ
  rcases hσa with hσa | hσa
  · -- `a = 2σ`: the next one is `2τ - 1`
    have hστ : σ < τ := by omega
    have hb' : b = 2 * τ - 1 := by
      rcases hτb with hτb | hτb
      · exact absurd ⟨by omega, by omega⟩ (hbet' _ (by omega) hfo2τ1)
      · exact hτb
    have hnone : ∀ t, σ < t → t < τ → ¬ IsLeader (2 ^ p - 1) t := by
      intro t h1 h2 ht
      obtain ⟨_, htlt, hfo, -⟩ := firstOcc_of_leader h87 hp hodd ht
      exact hbet' _ htlt hfo ⟨by omega, by omega⟩
    obtain ⟨e, he⟩ := hx σ τ hσ hτ hστ hnone
    apply hammingDist_toW har hbr (e := e + 2) (by omega)
    rw [hσa, hb', show 2 * τ - 1 = 2 * (τ - 1) + 1 by omega, double_xor, he]
    have : 1 ≤ 2 ^ (e + 1) := Nat.one_le_two_pow
    rw [pow_succ 2 (e + 1)]; omega
  · -- `a = 2σ - 1`: the next one is `2σ`
    have hb' : b = 2 * σ := by
      by_contra hne
      exact hbet' _ hσlt hfo2σ ⟨by omega, by omega⟩
    obtain ⟨e, he⟩ := succ_xor a
    apply hammingDist_toW har hbr (e := e + 1) (by omega)
    rw [hb', show 2 * σ = a + 1 by omega, he]

/-- **Dzoba's hypothesis from the exported theorem.**  Our odd-prime theorem (with the cited input
`Theorem87`, used again for the leader dictionary) gives the Degni–Drisko property in Dzoba's form at
every odd prime. -/
theorem ddProperty_of_main (h87 : Theorem87) (hmain : OddPrimeDegniDrisko) (p : ℕ) [NeZero p]
    (hp : p.Prime) (hodd : Odd p) : DDProperty p :=
  ddProperty_of_xorCore h87 hp hodd (xorCore_of_main h87 hmain hp hodd)

/-- **Dzoba's hypothesis at every odd prime**, under the two cited inputs. -/
theorem ddProperty (h87 : Theorem87) (h9 : TuningNesting) (p : ℕ) [NeZero p] (hp : p.Prime)
    (hodd : Odd p) : DDProperty p :=
  ddProperty_of_main h87 (oddPrimeDegniDrisko h87 h9) p hp hodd

end GrayNecklaces.SingleTrack
