module

public import GrayNecklaces.TentGrowth

/-!
# The finite-time covering lemma

For a central window satisfying the maximality hypothesis, the capped tent map covers the
invariant interval `[2R, λ]` from `J = [1 - b/M, λ]` within `k - 1` steps.
-/

@[expose] public section

namespace GrayNecklaces

open Tiozzo

/-- Disjoint phase segments: the combinatorial core of the time bound. -/
lemma seg_sum (k L : ℕ) (ph d : ℕ → ℕ)
    (ha : ∀ m < L, 1 ≤ ph m ∧ ph m + d m ≤ k ∧ d m ≤ ph m)
    (hb : ∀ m < L, ph (m + 1) = ph m + d m ∨ ph (m + 1) = d m)
    (hc : ∀ m₁ m₂, m₁ ≤ m₂ → d m₂ ≤ d m₁)
    (hd : ∀ m₁ m₂, m₁ < m₂ → m₂ ≤ L → ph m₁ ≠ ph m₂)
    (he : ∀ m₁ m₂, m₁ < m₂ → m₂ < L → ph m₂ < ph m₁ → ph m₂ + d m₂ ≤ ph m₁) :
    ∑ m ∈ Finset.range L, d m ≤ k - 1 := by
  -- the invariant after a fixed segment
  have hQ : ∀ m₁ < L, ∀ m, m₁ < m → m ≤ L → ph m₁ + d m₁ ≤ ph m ∨ ph m < ph m₁ := by
    intro m₁ hm₁ m
    induction m with
    | zero => intro h; omega
    | succ m ih =>
      intro h1 h2
      have hne := hd m₁ (m + 1) h1 h2
      obtain ⟨_, _, hdle⟩ := ha m₁ hm₁
      rcases Nat.lt_or_ge m₁ m with hlt | hge
      · have hmL : m < L := by omega
        rcases ih hlt (by omega) with hh | hh
        · rcases hb m hmL with e | e
          · left; rw [e]; omega
          · right; rw [e]; have := hc m₁ m hlt.le; omega
        · have hs := he m₁ m hlt hmL hh
          rcases hb m hmL with e | e
          · right; rw [e]; omega
          · right; rw [e]; have := hc m₁ m hlt.le; omega
      · have : m = m₁ := by omega
        subst this
        rcases hb m (by omega) with e | e
        · left; rw [e]
        · right; rw [e]; omega
  have hdisj : ∀ x ∈ Finset.range L, ∀ y ∈ Finset.range L, x ≠ y →
      Disjoint (Finset.Ico (ph x) (ph x + d x)) (Finset.Ico (ph y) (ph y + d y)) := by
    have key : ∀ x y, x < L → y < L → x < y →
        Disjoint (Finset.Ico (ph x) (ph x + d x)) (Finset.Ico (ph y) (ph y + d y)) := by
      intro x y hx hy hxy
      rw [Finset.disjoint_left]
      intro t ht1 ht2
      rw [Finset.mem_Ico] at ht1 ht2
      rcases hQ x hx y hxy hy.le with hh | hh
      · omega
      · have := he x y hxy hy hh; omega
    intro x hx y hy hxy
    rw [Finset.mem_range] at hx hy
    rcases lt_or_gt_of_ne hxy with h1 | h1
    · exact key x y hx hy h1
    · exact (key y x hy hx h1).symm
  have hsub : (Finset.range L).biUnion (fun m => Finset.Ico (ph m) (ph m + d m)) ⊆
      Finset.Ico 1 k := by
    intro t ht
    rw [Finset.mem_biUnion] at ht
    obtain ⟨m, hm, ht⟩ := ht
    rw [Finset.mem_range] at hm
    rw [Finset.mem_Ico] at ht ⊢
    have := ha m hm; omega
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_biUnion hdisj] at hcard
  simp only [Nat.card_Ico] at hcard
  have : ∑ m ∈ Finset.range L, (ph m + d m - ph m) = ∑ m ∈ Finset.range L, d m := by
    apply Finset.sum_congr rfl; intro m _; omega
  rw [this] at hcard
  exact hcard

section

variable {a k : ℕ} (h : Central a k)
include h

/-- A top interval with negative orientation returns no later than its phase. -/
lemma dret_le_phase {i : ℕ} (hi1 : 1 ≤ i) (hik : i < k) (hsg : sg a k i = -1) :
    dret a k i ≤ i := by
  by_contra hh
  push Not at hh
  have haff := affine h hi1 hik i (by omega) (xo a k i) ⟨le_rfl, xo_le_lam h i⟩
  rw [tent_iterate_xo h] at haff
  have hs : (sg a k i : ℝ) = -1 := by exact_mod_cast hsg
  rw [hs] at haff
  have h1 := xo_le_lam h (i + i)
  have h2 := xo_lt_lam h (i := i) (by omega) hik
  have hP : (1 : ℝ) < 2 ^ i := one_lt_pow₀ (by norm_num) (by omega)
  nlinarith

/-- The phase sequence of successive return intervals. -/
noncomputable def phs (a k j : ℕ) : ℕ → ℕ
  | 0 => j
  | m + 1 => nxt a k (phs a k j m)

variable {j : ℕ} (hj1 : 1 ≤ j) (hjk : j < k) (hjs : sg a k j = -1)
include hj1 hjk hjs

lemma phs_valid (m : ℕ) : 1 ≤ phs a k j m ∧ phs a k j m < k ∧ sg a k (phs a k j m) = -1 := by
  induction m with
  | zero => exact ⟨hj1, hjk, hjs⟩
  | succ m ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    obtain ⟨g1, g2, g3, _⟩ := nxt_spec h h1 h2 h3
    exact ⟨g1, g2, g3⟩

lemma phs_xo_anti (m : ℕ) : xo a k (phs a k j (m + 1)) ≤ xo a k (phs a k j m) := by
  obtain ⟨h1, h2, h3⟩ := phs_valid h hj1 hjk hjs m
  exact xo_nxt_le h h1 h2 h3

lemma phs_xo_anti' {m₁ m₂ : ℕ} (hle : m₁ ≤ m₂) :
    xo a k (phs a k j m₂) ≤ xo a k (phs a k j m₁) := by
  induction m₂ with
  | zero => have : m₁ = 0 := by omega
            subst this; exact le_rfl
  | succ m ih =>
    rcases Nat.lt_or_ge m₁ (m + 1) with hl | hl
    · exact le_trans (phs_xo_anti h hj1 hjk hjs m) (ih (by omega))
    · have : m₁ = m + 1 := by omega
      subst this; exact le_rfl

lemma phs_dret_anti {m₁ m₂ : ℕ} (hle : m₁ ≤ m₂) :
    dret a k (phs a k j m₂) ≤ dret a k (phs a k j m₁) := by
  obtain ⟨h1, h2, _⟩ := phs_valid h hj1 hjk hjs m₁
  exact dret_mono h h1 h2 (phs_xo_anti' h hj1 hjk hjs hle)

lemma phs_stabilizes : ∃ m, phs a k j (m + 1) = phs a k j m := by
  by_contra hno
  push Not at hno
  have hstrict : ∀ m, xo a k (phs a k j (m + 1)) < xo a k (phs a k j m) := by
    intro m
    rcases eq_or_lt_of_le (phs_xo_anti h hj1 hjk hjs m) with he | he
    · exfalso
      exact hno m (xo_inj h (phs_valid h hj1 hjk hjs _).2.1 (phs_valid h hj1 hjk hjs _).2.1 he)
    · exact he
  have hanti : StrictAnti (fun m => xo a k (phs a k j m)) := strictAnti_nat_of_succ_lt hstrict
  have hinj : Function.Injective (phs a k j) := fun x y hxy => hanti.injective (by simp [hxy])
  have hsub : (Finset.range k).image (phs a k j) ⊆ Finset.Ico 1 k := by
    intro t ht
    rw [Finset.mem_image] at ht
    obtain ⟨m, _, rfl⟩ := ht
    rw [Finset.mem_Ico]; exact ⟨(phs_valid h hj1 hjk hjs m).1, (phs_valid h hj1 hjk hjs m).2.1⟩
  have := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hinj] at this
  simp at this
  have := h.hk
  omega

/-- The total time spent before stabilization. -/
noncomputable def tph (a k j : ℕ) (m : ℕ) : ℕ := ∑ m' ∈ Finset.range m, dret a k (phs a k j m')

lemma phs_cover (m : ℕ) :
    topI a k (phs a k j m) ⊆ (Fm a k)^[tph a k j m] '' topI a k j := by
  induction m with
  | zero => simp [tph, phs]
  | succ m ih =>
    obtain ⟨h1, h2, h3⟩ := phs_valid h hj1 hjk hjs m
    have hcov := (nxt_spec h h1 h2 h3).2.2.2.2.2.2
    have e : tph a k j (m + 1) = dret a k (phs a k j m) + tph a k j m := by
      simp only [tph, Finset.sum_range_succ]; ring
    rw [e, Function.iterate_add, Set.image_comp]
    exact le_trans hcov (Set.image_mono ih)

end

/-- **The covering lemma.**  There is a phase `j` with negative orientation whose numerator `b`
is the least complementary residue of `a`, and from `J = [1 - b/M, λ]` the capped tent map covers
`[2R, λ]` at every time `n ≥ k - 1`. -/
theorem cover {a k j : ℕ} (h : Central a k) (hj1 : 1 ≤ j) (hjk : j < k) (hjs : sg a k j = -1) :
    ∀ n, k - 1 ≤ n → Set.Icc (2 * wR a k) (lam a k) ⊆ (Fm a k)^[n] '' topI a k j := by
  classical
  have hst := phs_stabilizes h hj1 hjk hjs
  set L := Nat.find hst
  have hL : phs a k j (L + 1) = phs a k j L := Nat.find_spec hst
  have hLmin : ∀ m < L, phs a k j (m + 1) ≠ phs a k j m := fun m hm => Nat.find_min hst hm
  obtain ⟨hv1, hv2, hv3⟩ := phs_valid h hj1 hjk hjs L
  have hstab : nxt a k (phs a k j L) = phs a k j L := hL
  have hd1 := stable_dret h hv1 hv2 hv3 hstab
  -- the stabilized interval is `[2R, λ]`
  have hspec := nxt_spec h hv1 hv2 hv3
  have hxL : xo a k (phs a k j L) = 2 * wR a k := by
    have hmin' := hspec.2.2.2.2.1
    rw [hstab, hd1] at hmin'
    have h1 : xo a k (phs a k j L) ≤ xo a k 1 := by rw [hmin']; exact min_le_right _ _
    have h2 := two_wR_le_xo h (phs a k j L) hv1
    rw [xo_one h] at h1
    linarith
  have hself : Set.Icc (2 * wR a k) (lam a k) ⊆ Fm a k '' Set.Icc (2 * wR a k) (lam a k) := by
    have := hspec.2.2.2.2.2.2
    rw [hstab, hd1, Function.iterate_one] at this
    simp only [topI, hxL] at this
    exact this
  have hiter : ∀ q, Set.Icc (2 * wR a k) (lam a k) ⊆
      (Fm a k)^[q] '' Set.Icc (2 * wR a k) (lam a k) := by
    intro q; induction q with
    | zero => simp
    | succ q ih =>
      rw [Function.iterate_succ', Set.image_comp]
      exact le_trans hself (Set.image_mono ih)
  -- the time bound
  have htime : tph a k j L ≤ k - 1 := by
    apply seg_sum k L (phs a k j) (fun m => dret a k (phs a k j m))
    · intro m hm
      obtain ⟨g1, g2, g3⟩ := phs_valid h hj1 hjk hjs m
      obtain ⟨_, hdle, _, _⟩ := dret_spec h g1 g2
      exact ⟨g1, by omega, dret_le_phase h g1 g2 g3⟩
    · intro m hm
      obtain ⟨g1, g2, g3⟩ := phs_valid h hj1 hjk hjs m
      exact (nxt_spec h g1 g2 g3).2.2.2.1
    · intro m₁ m₂ hle; exact phs_dret_anti h hj1 hjk hjs hle
    · intro m₁ m₂ hlt hle he
      -- strict decrease of the left endpoints before stabilization
      have hstrict : ∀ m, m < L → xo a k (phs a k j (m + 1)) < xo a k (phs a k j m) := by
        intro m hm
        rcases eq_or_lt_of_le (phs_xo_anti h hj1 hjk hjs m) with he' | he'
        · exact absurd (xo_inj h (phs_valid h hj1 hjk hjs _).2.1
            (phs_valid h hj1 hjk hjs _).2.1 he') (hLmin m hm)
        · exact he'
      have : xo a k (phs a k j m₂) < xo a k (phs a k j m₁) := by
        have h1 := hstrict m₁ (by omega)
        have h2 := phs_xo_anti' h hj1 hjk hjs (show m₁ + 1 ≤ m₂ by omega)
        linarith
      rw [he] at this; exact lt_irrefl _ this
    · intro m₁ m₂ hlt hm₂ hph
      obtain ⟨g1, g2, g3⟩ := phs_valid h hj1 hjk hjs m₁
      obtain ⟨g1', g2', g3'⟩ := phs_valid h hj1 hjk hjs m₂
      exact shift_bound h g1 g2 g1' g2' g3 g3' (phs_xo_anti' h hj1 hjk hjs hlt.le) hph
        (phs_dret_anti h hj1 hjk hjs hlt.le)
  intro n hn
  have hcov := phs_cover h hj1 hjk hjs L
  rw [show topI a k (phs a k j L) = Set.Icc (2 * wR a k) (lam a k) by simp [topI, hxL]] at hcov
  have : n = (n - tph a k j L) + tph a k j L := by omega
  rw [this, Function.iterate_add, Set.image_comp]
  calc Set.Icc (2 * wR a k) (lam a k)
      ⊆ (Fm a k)^[n - tph a k j L] '' Set.Icc (2 * wR a k) (lam a k) := hiter _
    _ ⊆ _ := Set.image_mono hcov

end GrayNecklaces
