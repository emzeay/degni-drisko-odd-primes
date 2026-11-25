module

public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Algebra.Ring.Parity

@[expose] public section

namespace GrayNecklaces

/-- The bits of a word of length `n`, with the most significant bit at index zero. -/
abbrev Word (n : ℕ) := Fin n → Bool

/-- A rank in the standard binary reflected Gray listing. -/
abbrev Rank (n : ℕ) := Fin (2 ^ n)

/-- The word at standard binary reflected Gray rank `r`, which is `r xor (r >>> 1)` read most
significant bit first. -/
def grayWord {n : ℕ} (r : Rank n) : Word n :=
  fun i => (r.val ^^^ (r.val >>> 1)).testBit (n - 1 - i.val)

/-- Rotation that moves the first `k` bits of a word to the end. -/
def rotate {n : ℕ} (k : Fin n) (w : Word n) : Word n :=
  fun i => w ⟨(i.val + k.val) % n, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩

/-- `r` is the greatest standard rank among the rotations of its word.  That word is the one
retained from its rotation class, since it comes first in reversed BRGC order. -/
def IsRepresentativeRank {n : ℕ} (r : Rank n) : Prop :=
  ∀ s : Rank n, (∃ k : Fin n, grayWord s = rotate k (grayWord r)) → s ≤ r

/-- Retained ranks `r > s` that are consecutive in reversed BRGC order, with no retained rank
strictly between them. -/
def ConsecutiveInReverseOrder {n : ℕ} (r s : Rank n) : Prop :=
  s < r ∧ IsRepresentativeRank r ∧ IsRepresentativeRank s ∧
    ∀ t : Rank n, s < t → t < r → ¬ IsRepresentativeRank t

/-- Exactly one coordinate differs. -/
def DifferInOneBit {n : ℕ} (u v : Word n) : Prop :=
  ∃ i : Fin n, u i ≠ v i ∧ ∀ j : Fin n, j ≠ i → u j = v j

/-- The step from `1^n` to `0^n`, the one exception the conjecture allows at odd prime length. -/
def IsTerminalPair {n : ℕ} (u v : Word n) : Prop :=
  (∀ i, u i = true) ∧ (∀ i, v i = false)

/-- The odd-prime case of Degni and Drisko's Conjecture 3.12.  At odd prime length, consecutive
retained words differ in exactly one bit, except for the step from `1^p` to `0^p`. -/
def OddPrimeDegniDrisko : Prop :=
  ∀ (p : ℕ), p.Prime → Odd p → ∀ r s : Rank p,
    ConsecutiveInReverseOrder r s →
    IsTerminalPair (grayWord r) (grayWord s) ∨ DifferInOneBit (grayWord r) (grayWord s)

end GrayNecklaces
