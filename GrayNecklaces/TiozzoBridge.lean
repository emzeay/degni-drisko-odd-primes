module

public import GrayNecklaces.Tiozzo
public import GrayNecklaces.Sieve

/-!
# Translating Tiozzo's statements into window coordinates

Coordinates: an angle `θ ∈ [1/4, 1/2]` corresponds to `x = 1 - 2θ ∈ [0, 1/2]`, and
`θ ∈ realAngles ↔ InK x` where `InK x` says `x ≤ ‖2^j x‖` for every `j` (the tent-orbit identity
`T^(j+1)(1-x) = 2‖2^j x‖`).

* `exists_actual`: from Theorem 8.7, every admissible window `W(b,j)` lies inside the window
  `W(a,k)` of the real hyperbolic window containing `b/2^j`, with `k ≤ j`.
* `IsActual.good`: such an actual window is a primitive signed-leader window.
* `actual_nested`: from the nesting statement of §9, overlapping actual windows are nested.
-/

@[expose] public section

namespace GrayNecklaces

open Tiozzo

/-! ### The tent map -/

lemma tent_eq {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : tent x = 2 * nint x := by
  unfold tent
  rcases le_total x (1 / 2) with h | h
  · rw [nint_of_mem h0 h, min_eq_left (by linarith)]
  · rw [nint_eq_abs_sub (n := 1) (by rw [abs_le]; push_cast; constructor <;> linarith)]
    push_cast; rw [abs_of_nonpos (by linarith), min_eq_right (by linarith)]; ring

lemma tent_mem {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : 0 ≤ tent x ∧ tent x ≤ 1 := by
  rw [tent_eq h0 h1]
  exact ⟨by have := nint_nonneg x; linarith, by have := nint_le_half x; linarith⟩

lemma tent_iterate {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) (n : ℕ) :
    tent^[n + 1] x = 2 * nint (2 ^ n * x) := by
  induction n with
  | zero => simp [tent_eq h0 h1]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    rw [tent_eq (by have := nint_nonneg (2 ^ n * x); linarith)
      (by have := nint_le_half (2 ^ n * x); linarith)]
    have := nint_zmul_nint 2 (2 ^ n * x)
    push_cast at this
    rw [this, pow_succ]; ring_nf

lemma tent_iterate_le_one {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) (n : ℕ) :
    0 ≤ tent^[n] x ∧ tent^[n] x ≤ 1 := by
  induction n with
  | zero => exact ⟨h0, h1⟩
  | succ n ih => rw [Function.iterate_succ_apply']; exact tent_mem ih.1 ih.2

lemma continuous_tent : Continuous tent :=
  (continuous_const.mul continuous_id).min (continuous_const.sub (continuous_const.mul continuous_id))

/-! ### The set `K` and real parameter angles -/

/-- The signed-minimum set `K` of the proof: `x ≤ ‖2^j x‖` for all `j`. -/
def InK (x : ℝ) : Prop := 0 ≤ x ∧ ∀ j : ℕ, x ≤ nint (2 ^ j * x)

lemma nint_of_unit {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1) : nint y = min y (1 - y) := by
  rcases le_total y (1 / 2) with h | h
  · rw [nint_of_mem h0 h, min_eq_left (by linarith)]
  · rw [nint_eq_abs_sub (n := 1) (by rw [abs_le]; push_cast; constructor <;> linarith)]
    push_cast; rw [abs_of_nonpos (by linarith), min_eq_right (by linarith)]; ring

lemma nint_succ_eq {x : ℝ} (j : ℕ) :
    nint (2 ^ (j + 1) * x) = min (2 * nint (2 ^ j * x)) (1 - 2 * nint (2 ^ j * x)) := by
  have := nint_zmul_nint 2 (2 ^ j * x)
  push_cast at this
  rw [pow_succ, show 2 ^ j * 2 * x = 2 * (2 ^ j * x) by ring, ← this]
  apply nint_of_unit
  · have := nint_nonneg (2 ^ j * x); linarith
  · have := nint_le_half (2 ^ j * x); linarith

lemma inK_iff_upper {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) :
    InK x ↔ ∀ j : ℕ, 2 * nint (2 ^ j * x) ≤ 1 - x := by
  constructor
  · rintro ⟨_, hK⟩ j
    have := hK (j + 1)
    rw [nint_succ_eq] at this
    have := min_le_right (2 * nint (2 ^ j * x)) (1 - 2 * nint (2 ^ j * x))
    linarith
  · intro hU
    refine ⟨h0, fun j => ?_⟩
    induction j with
    | zero => simp [nint_of_mem h0 h1]
    | succ j ih =>
      rw [nint_succ_eq]
      have := hU j
      exact le_min (by linarith) (by linarith)

lemma leafLength_of_le {θ : ℝ} (h : θ ≤ 1 / 2) : leafLength θ = 2 * θ := by
  unfold leafLength
  split_ifs with h'
  · rfl
  · have : θ = 1 / 2 := by linarith
    subst this; norm_num

lemma mem_realAngles_iff {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1 / 2) :
    θ ∈ realAngles ↔ ∀ n : ℕ, tent^[n] (2 * θ) ≤ 2 * θ := by
  unfold realAngles
  simp only [Set.mem_ofPred_eq, leafLength_of_le h1]
  constructor
  · rintro ⟨_, _, h⟩; exact h
  · intro h; exact ⟨h0, by linarith, h⟩

/-- The tent-orbit identity: `(1-x)/2` is a real parameter angle exactly when `x ∈ K`. -/
lemma inK_iff_angle {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) :
    (1 - x) / 2 ∈ realAngles ↔ InK x := by
  rw [mem_realAngles_iff (by linarith) (by linarith), inK_iff_upper h0 h1]
  rw [show 2 * ((1 - x) / 2) = 1 - x by ring]
  constructor
  · intro h j
    have := h (j + 1)
    rw [tent_iterate (by linarith) (by linarith)] at this
    have e : nint (2 ^ j * (1 - x)) = nint (2 ^ j * x) := by
      rw [show (2:ℝ) ^ j * (1 - x) = ((2 ^ j : ℕ) : ℤ) - 2 ^ j * x by push_cast; ring,
        sub_eq_add_neg, add_comm, nint_add_int, nint_neg]
    rw [e] at this; exact this
  · intro h n
    rcases n with _ | n
    · simp
    · rw [tent_iterate (by linarith) (by linarith)]
      have e : nint (2 ^ n * (1 - x)) = nint (2 ^ n * x) := by
        rw [show (2:ℝ) ^ n * (1 - x) = ((2 ^ n : ℕ) : ℤ) - 2 ^ n * x by push_cast; ring,
          sub_eq_add_neg, add_comm, nint_add_int, nint_neg]
      rw [e]; exact h n

/-- Points of the hole of `c/2^i` are not in `K`. -/
lemma hole_not_inK {c i : ℕ} (hi : 1 ≤ i) {y : ℝ} (h1 : (c : ℝ) / (2 ^ i + 1) < y)
    (h2 : y < c / (2 ^ i - 1)) : ¬ InK y := by
  rintro ⟨_, hK⟩
  have hD : (2 : ℝ) ≤ 2 ^ i := by
    have := pow_le_pow_right₀ (show (1:ℝ) ≤ 2 by norm_num) hi; simpa using this
  rw [div_lt_iff₀ (by positivity)] at h1
  rw [lt_div_iff₀ (by linarith)] at h2
  have := nint_le_abs_sub (2 ^ i * y) c
  have hab : |2 ^ i * y - (c : ℤ)| < y := by
    push_cast; rw [abs_lt]; constructor <;> nlinarith
  have := hK i
  linarith

lemma inK_one_third : InK (1 / 3) := by
  rw [inK_iff_upper (by norm_num) (by norm_num)]
  intro j
  have : nint (2 ^ j * (1 / 3)) = 1 / 3 := by
    induction j with
    | zero => rw [pow_zero, one_mul]; exact nint_of_mem (by norm_num) (by norm_num)
    | succ j ih =>
      rw [nint_succ_eq, ih]; norm_num
  rw [this]; norm_num

lemma one_third_mem : (1 : ℝ) / 3 ∈ realAngles := by
  have := (inK_iff_angle (x := 1 / 3) (by norm_num) (by norm_num)).mpr inK_one_third
  convert this using 1; norm_num

lemma half_mem : (1 : ℝ) / 2 ∈ realAngles := by
  rw [mem_realAngles_iff (by norm_num) le_rfl]
  intro n
  have := tent_iterate_le_one (x := 2 * (1/2)) (by norm_num) (by norm_num) n
  norm_num at this ⊢; exact this.2

lemma isClosed_angleSet (lo hi : ℝ) :
    IsClosed {θ : ℝ | lo ≤ θ ∧ θ ≤ hi ∧ ∀ n : ℕ, tent^[n] (2 * θ) ≤ 2 * θ} := by
  have h1 : IsClosed {θ : ℝ | lo ≤ θ} := isClosed_le continuous_const continuous_id
  have h2 : IsClosed {θ : ℝ | θ ≤ hi} := isClosed_le continuous_id continuous_const
  have h3 : IsClosed {θ : ℝ | ∀ n : ℕ, tent^[n] (2 * θ) ≤ 2 * θ} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun n =>
      isClosed_le ((continuous_tent.iterate n).comp (continuous_const.mul continuous_id))
        (continuous_const.mul continuous_id)
  have := (h1.inter h2).inter h3
  convert this using 1
  ext θ; simp [and_assoc]

/-! ### Binary words -/

/-- The `n`-digit binary word of `c`, most significant digit first. -/
def natBits : ℕ → ℕ → List Bool
  | 0, _ => []
  | n + 1, c => natBits n (c / 2) ++ [decide (c % 2 = 1)]

lemma natBits_length (n c : ℕ) : (natBits n c).length = n := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => simp [natBits, ih]

lemma bit_decide (c : ℕ) : bit (decide (c % 2 = 1)) = ((c % 2 : ℕ) : ℝ) := by
  unfold bit
  rcases Nat.mod_two_eq_zero_or_one c with h | h <;> simp [h]

lemma finBin_append (w₁ w₂ : List Bool) :
    finBin (w₁ ++ w₂) = finBin w₁ + finBin w₂ / 2 ^ w₁.length := by
  unfold finBin
  rw [List.length_append, Finset.sum_range_add]
  congr 1
  · apply Finset.sum_congr rfl; intro i hi
    rw [Finset.mem_range] at hi
    rw [List.getD_append _ _ _ _ hi]
  · rw [Finset.sum_div]
    apply Finset.sum_congr rfl; intro i hi
    rw [List.getD_append_right _ _ _ _ (by omega), show w₁.length + i - w₁.length = i by omega,
      pow_add, pow_add]
    field_simp
    ring

lemma finBin_natBits (n c : ℕ) : finBin (natBits n c) = ((c % 2 ^ n : ℕ) : ℝ) / 2 ^ n := by
  induction n generalizing c with
  | zero => simp [natBits, finBin, Nat.mod_one]
  | succ n ih =>
    rw [natBits, finBin_append, ih, natBits_length]
    unfold finBin
    simp only [List.length_singleton, Finset.range_one, Finset.sum_singleton, List.getD_cons_zero,
      zero_add, pow_one, bit_decide]
    have key : c % 2 ^ (n + 1) = 2 * (c / 2 % 2 ^ n) + c % 2 := by
      rw [pow_succ', Nat.mod_mul]; ring
    rw [key]; push_cast; field_simp; ring

lemma natBits_succ_dropLast (n c : ℕ) : (natBits (n + 1) c).dropLast = natBits n (c / 2) := by
  simp [natBits]

lemma natBits_succ_getLast (n c : ℕ) :
    (natBits (n + 1) c).getLast? = some (decide (c % 2 = 1)) := by
  simp [natBits]

lemma sum_geom_half (n : ℕ) : ∑ i ∈ Finset.range n, (1 : ℝ) / 2 ^ (i + 1) = 1 - 1 / 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; field_simp; ring

lemma finBin_map_not (w : List Bool) :
    finBin (w.map (fun b => !b)) = 1 - 1 / 2 ^ w.length - finBin w := by
  rw [← sum_geom_half]
  unfold finBin
  rw [List.length_map, eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i hi
  rw [Finset.mem_range] at hi
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ hi]
  simp only [List.getElem_map]
  unfold bit
  cases w[i] <;> simp

lemma perBin_eq (w : List Bool) (hw : 0 < w.length) :
    perBin w = finBin w * 2 ^ w.length / (2 ^ w.length - 1) := by
  set n := w.length
  set f : ℕ → ℝ := fun i => bit (w.getD (i % n) false) / 2 ^ (i + 1) with hf
  have hb : ∀ b, 0 ≤ bit b ∧ bit b ≤ 1 := by intro b; unfold bit; split_ifs <;> norm_num
  have hsum : Summable f := by
    apply Summable.of_nonneg_of_le (f := fun i : ℕ => (1 / 2 : ℝ) ^ i / 2)
    · intro i; exact div_nonneg (hb _).1 (by positivity)
    · intro i
      simp only [hf]
      rw [pow_succ, div_le_div_iff₀ (by positivity) (by positivity), one_div_pow]
      field_simp
      exact (hb _).2
    · exact summable_geometric_two.div_const 2
  have hshift : ∀ i, f (i + n) = f i / 2 ^ n := by
    intro i; simp only [hf]
    rw [Nat.add_mod_right, show i + n + 1 = (i + 1) + n by ring, pow_add]
    field_simp
  have hfirst : ∑ i ∈ Finset.range n, f i = finBin w := by
    unfold finBin
    apply Finset.sum_congr rfl; intro i hi
    rw [Finset.mem_range] at hi
    simp only [hf, Nat.mod_eq_of_lt hi]
  have key := hsum.sum_add_tsum_nat_add n
  simp only [hshift, tsum_div_const] at key
  rw [hfirst] at key
  have hpow : (1 : ℝ) < 2 ^ n := one_lt_pow₀ (by norm_num) (by omega)
  have : perBin w = ∑' i, f i := rfl
  rw [this]
  set S := ∑' i, f i
  field_simp
  field_simp at key
  linarith

/-! ### Actual windows -/

/-- An *actual* window: `(1 - wR a k)/2, (1 - a/(2^k+1))/2` is a real hyperbolic window, and
`a/2^k` is the pseudocenter of the corresponding interval in the `x = 1 - 2θ` coordinate. -/
def IsActual (a k : ℕ) : Prop :=
  2 ≤ k ∧ Odd a ∧ 3 * a < 2 ^ k ∧
    IsRealHyperbolicWindow ((1 - wR a k) / 2) ((1 - a / (2 ^ k + 1)) / 2) ∧
    ∀ (n : ℕ) (c : ℤ), (a : ℝ) / (2 ^ k + 1) < c / 2 ^ n → (c : ℝ) / 2 ^ n < wR a k → k ≤ n

lemma wR_le_third {a k : ℕ} (hk : 1 ≤ k) (h3 : 3 * a < 2 ^ k) : wR a k ≤ 1 / 3 := by
  have := three_wR_le hk h3; linarith

lemma left_le_wR {a k : ℕ} (hk : 1 ≤ k) : (a : ℝ) / (2 ^ k + 1) ≤ wR a k := by
  unfold wR
  have : (2:ℝ) ≤ 2 ^ k := by
    have := pow_le_pow_right₀ (show (1:ℝ) ≤ 2 by norm_num) hk; simpa using this
  apply div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)

lemma left_lt_wR {a k : ℕ} (ha : 0 < a) (hk : 1 ≤ k) : (a : ℝ) / (2 ^ k + 1) < wR a k := by
  unfold wR
  have : (2:ℝ) ≤ 2 ^ k := by
    have := pow_le_pow_right₀ (show (1:ℝ) ≤ 2 by norm_num) hk; simpa using this
  have : (0:ℝ) < a := by exact_mod_cast ha
  apply div_lt_div_of_pos_left (by positivity) (by linarith) (by linarith)

lemma IsActual.inK_right {a k : ℕ} (h : IsActual a k) : InK (wR a k) := by
  obtain ⟨hk, ha, h3, hw, _⟩ := h
  have := hw.2.2.2.1
  have hR0 := (wR_pos (j := k) ha.pos (by omega)).le
  exact (inK_iff_angle hR0 (by have := wR_le_third (by omega : 1 ≤ k) h3; linarith)).mp this

lemma IsActual.inK_left {a k : ℕ} (h : IsActual a k) : InK ((a : ℝ) / (2 ^ k + 1)) := by
  obtain ⟨hk, ha, h3, hw, _⟩ := h
  have := hw.2.2.2.2.1
  have h0 : (0 : ℝ) ≤ a / (2 ^ k + 1) := by positivity
  have h1 := le_trans (left_le_wR (a := a) (by omega : 1 ≤ k))
    (wR_le_third (by omega : 1 ≤ k) h3)
  exact (inK_iff_angle h0 (by linarith)).mp this

lemma IsActual.gap {a k : ℕ} (h : IsActual a k) {y : ℝ} (h1 : (a : ℝ) / (2 ^ k + 1) < y)
    (h2 : y < wR a k) : ¬ InK y := by
  obtain ⟨hk, ha, h3, hw, _⟩ := h
  intro hy
  have hy0 : 0 ≤ y := by have : (0 : ℝ) ≤ a / (2 ^ k + 1) := by positivity
                         linarith
  have hy1 : y ≤ 1 / 2 := by have := wR_le_third (by omega : 1 ≤ k) h3; linarith
  apply hw.2.2.2.2.2 ((1 - y) / 2) (by linarith) (by linarith)
  exact (inK_iff_angle hy0 hy1).mpr hy

lemma IsActual.leader {a k : ℕ} (h : IsActual a k) : IsLeader (2 ^ k - 1) a := by
  have hk : 2 ≤ k := h.1
  have hM : 0 < 2 ^ k - 1 := by have := two_le_two_pow (show 1 ≤ k by omega); omega
  rw [isLeader_iff_real _ _ hM]
  refine ⟨h.2.1.pos, fun j => ?_⟩
  have hK := h.inK_right.2 j
  unfold wR at hK
  rwa [two_pow_sub_one_cast]

lemma IsActual.prim {a k : ℕ} (h : IsActual a k) :
    ∀ i, 0 < i → i < k → ¬ (2 ^ k - 1) ∣ (2 ^ i - 1) * a := by
  intro i hi hik ⟨c, hc⟩
  have hk : 2 ≤ k := h.1
  have hapos := h.2.1.pos
  have hiR : (1 : ℝ) < 2 ^ i := one_lt_pow₀ (by norm_num) (by omega)
  have hkR : (1 : ℝ) < 2 ^ k := one_lt_pow₀ (by norm_num) (by omega)
  -- `wR a k = c / (2^i - 1)`
  have hcR : ((2 ^ i - 1 : ℕ) : ℝ) * a = ((2 ^ k - 1 : ℕ) : ℝ) * c := by exact_mod_cast hc
  rw [two_pow_sub_one_cast, two_pow_sub_one_cast] at hcR
  have hRc : wR a k = c / (2 ^ i - 1) := by
    unfold wR; rw [div_eq_div_iff (by linarith) (by linarith)]; linarith
  have hcpos : (0 : ℝ) < c := by
    have : (0 : ℝ) < (2 ^ i - 1) * a := by have : (0:ℝ) < a := by exact_mod_cast hapos
                                           positivity
    nlinarith
  have hdy : (c : ℝ) / 2 ^ i < wR a k := by
    rw [hRc]; apply div_lt_div_of_pos_left hcpos (by linarith) (by linarith)
  have hdy2 : (c : ℝ) / (2 ^ i + 1) < c / 2 ^ i :=
    div_lt_div_of_pos_left hcpos (by positivity) (by linarith)
  by_cases hl : (a : ℝ) / (2 ^ k + 1) < c / 2 ^ i
  · have := h.2.2.2.2 i (c : ℤ) (by push_cast; exact hl) (by push_cast; exact hdy)
    omega
  · push Not at hl
    apply hole_not_inK (c := c) (i := i) (by omega) (y := (a : ℝ) / (2 ^ k + 1)) (by linarith)
    · rw [← hRc]; exact left_lt_wR hapos (by omega)
    · exact h.inK_left

lemma IsActual.good {p a k : ℕ} (h : IsActual a k) (hkp : k < p) : GoodWin p a k :=
  ⟨⟨h.1, hkp, h.2.1, h.2.2.1⟩, h.leader, h.prim⟩

end GrayNecklaces
