module

public import GrayNecklaces.Extraction

/-!
# The phase of the least complementary residue
-/

@[expose] public section

namespace GrayNecklaces

open Tiozzo

section

variable {a k : ℕ} (h : Central a k)
include h

/-- The orbit numerator is the residue or its complement, according to the orientation. -/
lemma uo_eq_res (i : ℕ) :
    (sg a k i = 1 ∧ uo a k i = (2 ^ i * a) % (2 ^ k - 1)) ∨
    (sg a k i = -1 ∧ uo a k i = (2 ^ k - 1) - (2 ^ i * a) % (2 ^ k - 1)) := by
  have hc := uo_cong (a := a) (k := k) i
  have hMpos : 0 < 2 ^ k - 1 := by have := h.M_ge; omega
  set r := (2 ^ i * a) % (2 ^ k - 1)
  have hr : r < 2 ^ k - 1 := Nat.mod_lt _ hMpos
  have hdm := Nat.div_add_mod (2 ^ i * a) (2 ^ k - 1)
  have hdmZ : ((2 ^ i * a : ℕ) : ℤ) = (2 ^ k - 1 : ℕ) * ((2 ^ i * a) / (2 ^ k - 1) : ℕ) + r := by
    exact_mod_cast hdm.symm
  obtain ⟨hu1, hu2, hu3⟩ := uo_pos_lt h i
  rcases sg_cases (a := a) (k := k) i with hs | hs
  · left; refine ⟨hs, ?_⟩
    rw [hs] at hc
    have : ((2 ^ k - 1 : ℕ) : ℤ) ∣ (uo a k i : ℤ) - 1 * r := by
      have e : (uo a k i : ℤ) - 1 * r = ((uo a k i : ℤ) - 1 * 2 ^ i * a) +
          (2 ^ k - 1 : ℕ) * ((2 ^ i * a) / (2 ^ k - 1) : ℕ) := by
        push_cast at hdmZ ⊢; linarith
      rw [e]; exact dvd_add hc (dvd_mul_right _ _)
    obtain ⟨c, hc'⟩ := this
    have : c = 0 := by
      by_contra hc0
      rcases lt_or_gt_of_ne hc0 with h1 | h1 <;> nlinarith
    subst this; omega
  · right; refine ⟨hs, ?_⟩
    rw [hs] at hc
    have : ((2 ^ k - 1 : ℕ) : ℤ) ∣ (uo a k i : ℤ) + r := by
      have e : (uo a k i : ℤ) + r = ((uo a k i : ℤ) - -1 * 2 ^ i * a) -
          (2 ^ k - 1 : ℕ) * ((2 ^ i * a) / (2 ^ k - 1) : ℕ) := by
        push_cast at hdmZ ⊢; linarith
      rw [e]; exact dvd_sub hc (dvd_mul_right _ _)
    obtain ⟨c, hc'⟩ := this
    have : c = 1 := by
      have h1 : (0 : ℤ) < (2 ^ k - 1 : ℕ) * c := by rw [← hc']; omega
      have h2 : ((2 ^ k - 1 : ℕ) : ℤ) * c < 2 * (2 ^ k - 1 : ℕ) := by rw [← hc']; omega
      have : 0 < c := by by_contra hh; push Not at hh; nlinarith
      have : c < 2 := by by_contra hh; push Not at hh; nlinarith
      omega
    subst this; omega

lemma res_mod (i : ℕ) : (2 ^ i * a) % (2 ^ k - 1) = (2 ^ (i % k) * a) % (2 ^ k - 1) := by
  have hk : 1 ≤ k := by have := h.hk; omega
  have h1 : 2 ^ i = 2 ^ (i % k) * (2 ^ k) ^ (i / k) := by rw [← pow_mul, ← pow_add, Nat.mod_add_div]
  have hcong : (2 ^ k) ^ (i / k) % (2 ^ k - 1) = 1 % (2 ^ k - 1) := by
    have : 2 ^ k % (2 ^ k - 1) = 1 % (2 ^ k - 1) := by
      have hM := h.M_ge
      rw [Nat.mod_eq_sub_mod (by omega), show 2 ^ k - (2 ^ k - 1) = 1 by omega]
    rw [Nat.pow_mod, this, ← Nat.pow_mod, one_pow]
  rw [h1, mul_assoc, mul_comm ((2 ^ k) ^ (i / k)), ← mul_assoc, Nat.mul_mod, hcong, ← Nat.mul_mod,
    mul_one]

/-- The phase whose numerator is the least complementary residue `b`. -/
theorem exists_neg_phase : ∃ j, 1 ≤ j ∧ j < k ∧ sg a k j = -1 ∧
    ∀ i, uo a k j ≤ (2 ^ k - 1) - (2 ^ i * a) % (2 ^ k - 1) := by
  have hk := h.hk
  have hMpos : 0 < 2 ^ k - 1 := by have := h.M_ge; omega
  set M := 2 ^ k - 1 with hMdef
  set f : ℕ → ℕ := fun i => M - (2 ^ i * a) % M
  obtain ⟨i0, hi0, hmin⟩ := Finset.exists_min_image (Finset.range k) f ⟨0, by simp; omega⟩
  rw [Finset.mem_range] at hi0
  have hmin' : ∀ i, f i0 ≤ f i := by
    intro i
    have : f i = f (i % k) := by simp only [f]; rw [res_mod h i]
    rw [this]; exact hmin _ (Finset.mem_range.mpr (Nat.mod_lt _ (by omega)))
  -- residues are never zero
  have hres0 : ∀ i, 0 < (2 ^ i * a) % M := by
    intro i
    have := (uo_pos_lt h i).1
    have h2 := (uo_pos_lt h i).2.1
    rw [← hMdef] at h2
    rcases uo_eq_res h i with ⟨_, he⟩ | ⟨_, he⟩ <;> rw [← hMdef] at he
    · omega
    · by_contra h0; push Not at h0
      have : (2 ^ i * a) % M = 0 := by omega
      rw [this] at he
      omega
  -- the minimum is odd
  have hodd : Odd (f i0) := by
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    obtain ⟨t, ht⟩ := hev
    set i1 := (i0 + k - 1) % k
    have hcong : (2 * (2 ^ i1 * a)) % M = (2 ^ i0 * a) % M := by
      rw [show 2 * (2 ^ i1 * a) = 2 ^ (i1 + 1) * a by ring, res_mod h (i1 + 1), res_mod h i0]
      congr 3
      simp only [i1]
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, show i0 + k - 1 + 1 = i0 + k by omega,
        Nat.add_mod_right]
    set r0 := (2 ^ i0 * a) % M
    set r1 := (2 ^ i1 * a) % M
    have hr1 : r1 < M := Nat.mod_lt _ hMpos
    have hr0 : r0 < M := Nat.mod_lt _ hMpos
    have hr1p := hres0 i1
    have hr0p := hres0 i0
    -- `2 r1 ≡ r0`
    have h2r : (2 * r1) % M = r0 := by
      rw [show 2 * r1 = 2 * ((2 ^ i1 * a) % M) from rfl, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod,
        hcong]
    have hdiv := Nat.div_add_mod (2 * r1) M
    rw [h2r] at hdiv
    -- `f i1 = M - r1 = t`
    have hq : 2 * r1 / M ≤ 1 := by
      by_contra hh; push Not at hh
      have : 2 * M ≤ M * (2 * r1 / M) := by nlinarith
      omega
    have hft : f i1 = t := by
      simp only [f]
      rcases Nat.eq_zero_or_pos (2 * r1 / M) with h0 | h0
      · rw [h0] at hdiv; simp at hdiv
        -- `2 r1 = r0`, `f i0 = M - 2 r1 = 2t`: impossible by parity of `M`
        obtain ⟨μ, hμ⟩ := h.M_odd
        simp only [f] at ht; omega
      · have : 2 * r1 / M = 1 := by omega
        rw [this, mul_one] at hdiv
        simp only [f] at ht; omega
    have := hmin' i1
    rw [hft, ht] at this
    have : 0 < t := by
      have : 0 < f i0 := by simp only [f]; omega
      omega
    omega
  -- the phase `i0` has negative orientation
  refine ⟨i0, ?_, hi0, ?_, ?_⟩
  · by_contra h0; push Not at h0
    have : i0 = 0 := by omega
    subst this
    -- `f 0 = M - a` is even
    obtain ⟨μ, hμ⟩ := h.M_odd
    obtain ⟨α, hα⟩ := h.ha
    have : (2 ^ 0 * a) % M = a := by simp; exact Nat.mod_eq_of_lt (by have := h.h6; omega)
    obtain ⟨t, ht⟩ := hodd
    simp only [f, this] at ht; omega
  · rcases uo_eq_res h i0 with ⟨hs, he⟩ | ⟨hs, _⟩
    · rw [← hMdef] at he
      exfalso
      have hu := (uo_pos_lt h i0).2.2
      obtain ⟨μ, hμ⟩ := h.M_odd
      obtain ⟨t, ht⟩ := hodd
      obtain ⟨t', ht'⟩ := hu
      simp only [f] at ht
      have := hres0 i0
      omega
    · exact hs
  · intro i
    rcases uo_eq_res h i0 with ⟨hs, he⟩ | ⟨hs, he⟩ <;> rw [← hMdef] at he
    · exfalso
      have hu := (uo_pos_lt h i0).2.2
      obtain ⟨μ, hμ⟩ := h.M_odd
      obtain ⟨t, ht⟩ := hodd
      obtain ⟨t', ht'⟩ := hu
      simp only [f] at ht
      have := hres0 i0
      omega
    · rw [he]; exact hmin' i

end

end GrayNecklaces
