import GrayNecklaces

/-!
# Gray codes for necklaces of odd prime length (Mütze's Problem P17, prime case)

Savage asked whether the binary necklaces of every odd length `n` admit a 1-Gray code, meaning a
listing of all necklaces, each once, in which consecutive necklaces have representatives differing
in one bit (T. Mütze, *Combinatorial Gray codes — an updated survey*, Problem P17).

`IsNecklaceGrayCode n m f` says that the words `f 0, …, f (m-1)` meet every necklace of length
`n` exactly once and that consecutive words differ in one bit.  `necklaceGrayCode_of_main`
derives such a listing, starting at `0^p`, from the exported theorem `OddPrimeDegniDrisko`.

The listing is the Degni–Drisko list of maximum-rank representatives in reversed BRGC order, with
the constant word `0^p` moved from the end to the front.  Degni and Drisko observed this
construction on page 7 of their paper, conditional on their conjecture.  By the theorem, every
step is one bit except the terminal `1^p → 0^p`, which the move removes.  The new first step `0^p → 10…0`
is one bit.
-/

namespace GrayNecklaces.NecklaceGrayCode

/-- A 1-Gray code for the necklaces of length `n`.  The words `f 0, …, f (m-1)` meet every
rotation class exactly once, and consecutive words differ in exactly one bit. -/
def IsNecklaceGrayCode (n m : ℕ) (f : ℕ → Word n) : Prop :=
  (∀ w : Word n, ∃ i < m, ∃ k : Fin n, w = rotate k (f i)) ∧
  (∀ i < m, ∀ j < m, ∀ k : Fin n, f j = rotate k (f i) → i = j) ∧
  (∀ i, i + 1 < m → DifferInOneBit (f i) (f (i + 1)))

/-- The BRGC word of rank `r`. -/
def wordOf (p r : ℕ) : Word p := fun i => (gcode r).testBit (p - 1 - i.val)

lemma wordOf_eq {p r : ℕ} (hr : r < 2 ^ p) : wordOf p r = grayWord (⟨r, hr⟩ : Rank p) := rfl

/-- Maximum-rank representatives, as a Boolean test on natural numbers. -/
def isRepB (p r : ℕ) : Bool := decide (∀ k < p, (rot1 p)^[k] r ≤ r)

/-- The representative ranks in increasing order. -/
def reps (p : ℕ) : List ℕ := (List.range (2 ^ p)).filter (isRepB p)

lemma isRepB_iff {p r : ℕ} (hp : 1 ≤ p) (hr : r < 2 ^ p) :
    isRepB p r = true ↔ ∀ k, (rot1 p)^[k] r ≤ r := by
  unfold isRepB
  rw [decide_eq_true_iff]
  constructor
  · intro h k
    rw [rot1_iterate_mod hp hr]; exact h _ (Nat.mod_lt _ (by omega))
  · intro h k _; exact h k

lemma mem_reps {p r : ℕ} : r ∈ reps p ↔ r < 2 ^ p ∧ isRepB p r = true := by
  simp [reps]

lemma reps_pairwise (p : ℕ) : (reps p).Pairwise (· < ·) :=
  List.pairwise_lt_range.filter _

lemma reps_lt {p i j : ℕ} (hi : i < (reps p).length) (hj : j < (reps p).length) (hij : i < j) :
    (reps p)[i] < (reps p)[j] :=
  List.pairwise_iff_getElem.mp (reps_pairwise p) i j hi hj hij

lemma reps_lt_iff {p i j : ℕ} (hi : i < (reps p).length) (hj : j < (reps p).length) :
    (reps p)[i] < (reps p)[j] ↔ i < j := by
  constructor
  · intro h
    by_contra hh; push Not at hh
    rcases Nat.lt_or_eq_of_le hh with h' | h'
    · have := reps_lt hj hi h'; omega
    · subst h'; omega
  · exact reps_lt hi hj

lemma reps_inj {p i j : ℕ} (hi : i < (reps p).length) (hj : j < (reps p).length)
    (h : (reps p)[i] = (reps p)[j]) : i = j := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h' | h'
  · have := reps_lt hi hj h'; omega
  · have := reps_lt hj hi h'; omega

lemma reps_bound {p i : ℕ} (hi : i < (reps p).length) : (reps p)[i] < 2 ^ p :=
  (mem_reps.mp (List.getElem_mem hi)).1

lemma zero_mem_reps (p : ℕ) : 0 ∈ reps p := by
  rw [mem_reps]
  refine ⟨Nat.two_pow_pos p, ?_⟩
  unfold isRepB; rw [decide_eq_true_iff]
  intro k _
  have : ∀ k, (rot1 p)^[k] 0 = 0 := by
    intro k; induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih, rot1_zero]
  rw [this]

lemma top_mem_reps {p : ℕ} (hp : 1 ≤ p) : 2 ^ p - 1 ∈ reps p := by
  have hr : 2 ^ p - 1 < 2 ^ p := by have := Nat.two_pow_pos p; omega
  rw [mem_reps, isRepB_iff hp hr]
  refine ⟨hr, fun k => ?_⟩
  have := rot1_iterate_lt hp hr k; omega

lemma reps_length_pos (p : ℕ) : 0 < (reps p).length :=
  List.length_pos_of_mem (zero_mem_reps p)

lemma reps_zero (p : ℕ) : (reps p)[0]'(reps_length_pos p) = 0 := by
  obtain ⟨j, hj, hjv⟩ := List.mem_iff_getElem.mp (zero_mem_reps p)
  rcases Nat.eq_zero_or_pos j with h0 | h0
  · subst h0; exact hjv
  · have := reps_lt (reps_length_pos p) hj h0; omega

lemma reps_last {p : ℕ} (hp : 1 ≤ p) :
    (reps p)[(reps p).length - 1]'(by have := reps_length_pos p; omega) = 2 ^ p - 1 := by
  obtain ⟨j, hj, hjv⟩ := List.mem_iff_getElem.mp (top_mem_reps hp)
  have hlast := reps_bound (p := p) (i := (reps p).length - 1) (by have := reps_length_pos p; omega)
  rcases Nat.lt_or_ge j ((reps p).length - 1) with h | h
  · have := reps_lt hj (by have := reps_length_pos p; omega) h; omega
  · have : j = (reps p).length - 1 := by omega
    subst this; exact hjv

/-- The listing: index `i` holds the representative at position `(len - i) mod len`. -/
def listing (p : ℕ) (i : ℕ) : Word p :=
  wordOf p ((reps p).getD (((reps p).length - i) % (reps p).length) 0)

lemma listing_eq {p i : ℕ} (_hi : i < (reps p).length) :
    listing p i = wordOf p ((reps p)[((reps p).length - i) % (reps p).length]'
      (Nat.mod_lt _ (reps_length_pos p))) := by
  unfold listing
  rw [List.getD_eq_getElem]

lemma isRep_of_mem {p r : ℕ} (hp : 1 ≤ p) (h : r ∈ reps p) :
    ∃ hr : r < 2 ^ p, IsRepresentativeRank (⟨r, hr⟩ : Rank p) := by
  obtain ⟨hr, hb⟩ := mem_reps.mp h
  exact ⟨hr, (isRepresentativeRank_iff hp _).mpr ((isRepB_iff hp hr).mp hb)⟩

/-- Two representatives in the same rotation class are equal. -/
lemma rep_eq_of_rot {p r s : ℕ} (hp : 1 ≤ p) (hr : r ∈ reps p) (hs : s ∈ reps p) (k : Fin p)
    (h : wordOf p s = rotate k (wordOf p r)) : r = s := by
  obtain ⟨hrb, hrb'⟩ := mem_reps.mp hr
  obtain ⟨hsb, hsb'⟩ := mem_reps.mp hs
  rw [isRepB_iff hp hrb] at hrb'
  rw [isRepB_iff hp hsb] at hsb'
  rw [wordOf_eq hrb, wordOf_eq hsb, rotate_grayWord hp] at h
  have hs_eq : s = (rot1 p)^[k.val] r := congrArg Fin.val (grayWord_injective p h)
  have h1 : s ≤ r := hs_eq ▸ hrb' k.val
  have hback : (rot1 p)^[p - k.val] s = r := by
    rw [hs_eq, ← Function.iterate_add_apply, show p - k.val + k.val = p by omega,
      rot1_iterate_period hp hrb]
  have h2 : r ≤ s := hback ▸ hsb' (p - k.val)
  omega

/-- **Problem P17 at odd prime lengths, from the exported theorem.**  The necklaces of length `p`
admit a 1-Gray code starting at `0^p`. -/
theorem necklaceGrayCode_of_main (hmain : OddPrimeDegniDrisko) {p : ℕ} (hp : p.Prime)
    (hodd : Odd p) :
    ∃ m f, IsNecklaceGrayCode p m f ∧ f 0 = fun _ => false := by
  have hp1 : 1 ≤ p := hp.one_lt.le
  have hlen0 : 0 < (reps p).length := reps_length_pos p
  -- the representative at listing position `i`
  have hidx : ∀ i < (reps p).length, ((reps p).length - i) % (reps p).length < (reps p).length := fun i _ => Nat.mod_lt _ hlen0
  refine ⟨(reps p).length, listing p, ⟨?_, ?_, ?_⟩, ?_⟩
  · -- every necklace is met
    intro w
    obtain ⟨x, rfl⟩ := (grayWord_bijective p).2 w
    obtain ⟨m0, hm0, hmax⟩ := Finset.exists_max_image (Finset.range p)
      (fun m => (rot1 p)^[m] x.val) ⟨0, Finset.mem_range.mpr (by omega)⟩
    rw [Finset.mem_range] at hm0
    set r := (rot1 p)^[m0] x.val with hrdef
    have hrlt : r < 2 ^ p := rot1_iterate_lt hp1 x.isLt m0
    have hrmem : r ∈ (reps p) := by
      rw [mem_reps, isRepB_iff hp1 hrlt]
      refine ⟨hrlt, fun k => ?_⟩
      rw [hrdef, ← Function.iterate_add_apply, rot1_iterate_mod hp1 x.isLt]
      exact hmax _ (Finset.mem_range.mpr (Nat.mod_lt _ (by omega)))
    obtain ⟨j, hj, hjv⟩ := List.mem_iff_getElem.mp hrmem
    refine ⟨((reps p).length - j) % (reps p).length, Nat.mod_lt _ hlen0, ⟨(p - m0) % p, Nat.mod_lt _ (by omega)⟩, ?_⟩
    have hjj : ((reps p).length - ((reps p).length - j) % (reps p).length) % (reps p).length = j := by
      rcases Nat.eq_zero_or_pos j with h0 | h0
      · subst h0; simp
      · rw [Nat.mod_eq_of_lt (by omega : (reps p).length - j < (reps p).length), Nat.mod_eq_of_lt (by omega)]; omega
    rw [listing_eq (Nat.mod_lt _ hlen0)]
    simp only [hjj, hjv]
    rw [wordOf_eq hrlt, rotate_grayWord hp1]
    congr 1
    apply Fin.ext
    simp only
    rw [hrdef, ← Function.iterate_add_apply]
    rcases Nat.eq_zero_or_pos m0 with h0 | h0
    · subst h0; simp
    · rw [Nat.mod_eq_of_lt (by omega : p - m0 < p), show p - m0 + m0 = p by omega,
        rot1_iterate_period hp1 x.isLt]
  · -- each necklace is met once
    intro i hi j hj k h
    rw [listing_eq hi, listing_eq hj] at h
    have := rep_eq_of_rot hp1 (List.getElem_mem _) (List.getElem_mem _) k h
    have h' := reps_inj (hidx i hi) (hidx j hj) this
    rcases Nat.eq_zero_or_pos i with hi0 | hi0 <;> rcases Nat.eq_zero_or_pos j with hj0 | hj0
    · omega
    · subst hi0
      rw [Nat.sub_zero, Nat.mod_self, Nat.mod_eq_of_lt (by omega : (reps p).length - j < (reps p).length)] at h'; omega
    · subst hj0
      rw [Nat.sub_zero, Nat.mod_self, Nat.mod_eq_of_lt (by omega : (reps p).length - i < (reps p).length)] at h'; omega
    · rw [Nat.mod_eq_of_lt (by omega : (reps p).length - i < (reps p).length),
        Nat.mod_eq_of_lt (by omega : (reps p).length - j < (reps p).length)] at h'
      omega
  · -- consecutive words differ in one bit
    intro i hi
    rw [listing_eq (by omega), listing_eq hi]
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · -- `0^p` to the top word `10…0`
      subst h0
      have e0 : ((reps p).length - 0) % (reps p).length = 0 := by simp
      have e1 : ((reps p).length - (0 + 1)) % (reps p).length = (reps p).length - 1 := Nat.mod_eq_of_lt (by omega)
      simp only [e0, e1, reps_zero, reps_last hp1]
      rw [wordOf_eq (Nat.two_pow_pos p), wordOf_eq (by have := Nat.two_pow_pos p; omega)]
      apply differInOneBit_of_xor _ _ hp1 le_rfl
      simp
    · -- consecutive representatives in reversed order
      have ea : ((reps p).length - i) % (reps p).length = (reps p).length - i := Nat.mod_eq_of_lt (by omega)
      have eb : ((reps p).length - (i + 1)) % (reps p).length = (reps p).length - i - 1 := by
        rw [Nat.mod_eq_of_lt (by omega)]; omega
      simp only [ea, eb]
      set r := (reps p)[(reps p).length - i]'(by omega) with hr
      set s := (reps p)[(reps p).length - i - 1]'(by omega) with hs
      have hrb : r < 2 ^ p := reps_bound _
      have hsb : s < 2 ^ p := reps_bound _
      have hsr : s < r := reps_lt (by omega) (by omega) (by omega)
      have hs0 : 0 < s := by
        have := reps_lt (p := p) (reps_length_pos p) (by omega : (reps p).length - i - 1 < (reps p).length)
          (by omega : 0 < (reps p).length - i - 1)
        rw [reps_zero] at this; exact this
      obtain ⟨_, hrepr⟩ := isRep_of_mem hp1 (List.getElem_mem (l := reps p) (by omega : (reps p).length - i < (reps p).length))
      obtain ⟨_, hreps⟩ := isRep_of_mem hp1
        (List.getElem_mem (l := reps p) (by omega : (reps p).length - i - 1 < (reps p).length))
      have hcons : ConsecutiveInReverseOrder (⟨r, hrb⟩ : Rank p) ⟨s, hsb⟩ := by
        refine ⟨by rw [Fin.lt_def]; exact hsr, hrepr, hreps, ?_⟩
        intro t h1 h2 ht
        rw [Fin.lt_def] at h1 h2
        have htmem : t.val ∈ (reps p) := by
          rw [mem_reps, isRepB_iff hp1 t.isLt]
          exact ⟨t.isLt, (isRepresentativeRank_iff hp1 t).mp ht⟩
        obtain ⟨j, hj, hjv⟩ := List.mem_iff_getElem.mp htmem
        have a1 : (reps p).length - i - 1 < j := (reps_lt_iff (by omega) hj).mp (by rw [hjv]; exact h1)
        have a2 : j < (reps p).length - i := (reps_lt_iff hj (by omega)).mp (by rw [hjv]; exact h2)
        omega
      rw [wordOf_eq hrb, wordOf_eq hsb]
      rcases hmain p hp hodd _ _ hcons with ⟨_, hz⟩ | hd
      · exfalso
        have hg : gcode s = 0 := by
          apply Nat.eq_of_testBit_eq; intro t
          rw [Nat.zero_testBit]
          by_cases ht : t < p
          · have := hz ⟨p - 1 - t, by omega⟩
            simp only [grayWord_apply] at this
            rwa [show p - 1 - (p - 1 - t) = t by omega] at this
          · have hsh : s >>> 1 < 2 ^ p := by
              rw [Nat.shiftRight_eq_div_pow]; exact lt_of_le_of_lt (Nat.div_le_self _ _) hsb
            have hlt : gcode s < 2 ^ p := Nat.xor_lt_two_pow hsb hsh
            exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt
              (Nat.pow_le_pow_right (by norm_num) (by omega)))
        have := gcode_eq_zero hg; omega
      · exact hd
  · -- the listing starts at `0^p`
    funext i
    rw [listing_eq hlen0]
    simp only [Nat.sub_zero, Nat.mod_self, reps_zero]
    rw [wordOf_eq (Nat.two_pow_pos p)]
    exact grayWord_zero hp1 i

/-- **Problem P17 at odd prime lengths.**  Under the two cited inputs, the necklaces of every odd
prime length `p` admit a 1-Gray code starting at `0^p`. -/
theorem necklaceGrayCode (h87 : Tiozzo.Theorem87) (h9 : Tiozzo.TuningNesting) {p : ℕ}
    (hp : p.Prime) (hodd : Odd p) :
    ∃ m f, IsNecklaceGrayCode p m f ∧ f 0 = fun _ => false :=
  necklaceGrayCode_of_main (oddPrimeDegniDrisko h87 h9) hp hodd

end GrayNecklaces.NecklaceGrayCode
