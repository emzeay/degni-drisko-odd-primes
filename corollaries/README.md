# Corollaries

Two open problems from [Mütze's survey of combinatorial Gray codes](https://arxiv.org/abs/2202.01280) follow from the odd-prime Degni–Drisko theorem. The Lean files here are a separate library, so the main theorem builds and audits on its own. Section 7 of [proof.pdf](../proof.pdf) summarizes them.

## Verification

From the repository root, after the setup in the [main README](../README.md#verification):

```sh
lake build Corollaries
lake env lean --trust=0 corollaries/Audit.lean
```

The audit reports `[propext, Classical.choice, Quot.sound]` for every statement below. Each statement comes in two forms. The `_of_main` form takes the exported statement `OddPrimeDegniDrisko` as a hypothesis. For P13 it also takes `Tiozzo.Theorem87`, because converting between least-rank and greatest-rank representatives uses the sieve's equality of leader sets, which depends on Theorem 8.7. This equality also follows from Degni and Drisko's Corollaries 3.10 and 4.3, which are not formalized here. The other form instantiates `OddPrimeDegniDrisko` with the main theorem `oddPrimeDegniDrisko`, so its only hypotheses are the two Tiozzo results listed in the [main README](../README.md#verification).

## Problem P17: Gray codes for necklaces of odd prime length

Savage asked whether the binary necklaces of every odd length admit a 1-Gray code, meaning a listing of all necklaces, each once, in which consecutive necklaces have representatives differing in one bit. The necklaces $0^n$ and $1^n$ each have only one neighbouring necklace, so such a code is a Gray path from $0^n$ to $1^n$. This is Problem P17 in Mütze's survey. Degni and Drisko observed on page 7 of their paper that their conjecture at a prime length gives such a code, by moving $0^n$ to the front of their list. At every odd prime length, the main theorem removes the dependence on their conjecture.

In [NecklaceGrayCode.lean](NecklaceGrayCode.lean), `IsNecklaceGrayCode n m f` says that the words `f 0, …, f (m-1)` meet every rotation class exactly once and that consecutive words differ in exactly one bit.

```text
GrayNecklaces.NecklaceGrayCode.necklaceGrayCode_of_main :
  OddPrimeDegniDrisko → ∀ {p : ℕ}, p.Prime → Odd p →
    ∃ m f, IsNecklaceGrayCode p m f ∧ f 0 = fun _ => false

GrayNecklaces.NecklaceGrayCode.necklaceGrayCode :
  Tiozzo.Theorem87 → Tiozzo.TuningNesting → ∀ {p : ℕ}, p.Prime → Odd p →
    ∃ m f, IsNecklaceGrayCode p m f ∧ f 0 = fun _ => false
```

The formal statement fixes the first word, $0^p$. That the list ends at $1^p$ is shown in the proof of Corollary 3 in the PDF.

The listing is Degni and Drisko's list of representatives in reversed reflected Gray order, with the constant word $0^p$ moved from the end to the front. By the theorem, every step is one bit except the terminal step $1^p\to0^p$, which the move removes. The new first step, from $0^p$ to $10\cdots0$, is also one bit.

## Problem P13: optimal single-track Gray codes at every odd prime length

A single-track Gray code of length $n$ and period $P$ is a cyclic Gray code of $P$ distinct $n$-bit words in which every column is a cyclic shift of the first. Hiltgen, Paterson and Brandestini introduced these codes in 1996. At prime length the longest possible period is $2^n-2$. Whether this period is attained at every prime $n\ge3$ is Problem P13 in Mütze's survey. Optimal codes were known for primes up to 19, and Dzoba extended this by computation to every odd prime up to 47.

Chris Dzoba's [Theorem A](https://arxiv.org/abs/2610.24758) reduces the question to the Degni–Drisko property. At prime length $n\ge7$, list the nonconstant necklaces by the rank of their least-rank representatives. If consecutive necklaces in this list are adjacent, then an optimal code exists. He gives explicit codes for $n=3,5$ and has formalized Theorem A in Lean, in the ancillary files of version 1 of his arXiv preprint. There the hypothesis is `STGC.DDProperty n`.

[SingleTrack.lean](SingleTrack.lean) proves that hypothesis at every odd prime from the main theorem. It states the property with its own definitions, written to match those in Dzoba's Lean files.

| This repository | Dzoba's Lean files | Meaning | Definition |
|---|---|---|---|
| `CWord n` | `Word n` | words `ZMod n → Bool`, position 0 most significant | identical |
| `rot k w` | `rot k w` | rotation, `(rot k w) i = w (i + k)` | identical |
| `IsConst w` | `IsConst w` | all bits equal | identical |
| `prefixParity w i` | `prefPar w i` | parity of the bits at positions `0, …, i` | equivalent, written differently |
| `rank w` | `rank w` | position in the binary reflected Gray code, from the prefix parities | equivalent, written differently |
| `IsFirstOcc w` | `IsFirstOcc w` | nonconstant, and of least rank among its rotations | identical |
| `NecklaceAdj u v` | `NecklaceAdj u v` | some rotation of `v` is at Hamming distance one from `u` | identical |
| `DDProperty n` | `DDProperty n` | consecutive first occurrences in rank order are adjacent | identical |

```text
GrayNecklaces.SingleTrack.ddProperty_of_main :
  Tiozzo.Theorem87 → OddPrimeDegniDrisko →
    ∀ (p : ℕ) [NeZero p], p.Prime → Odd p → DDProperty p

GrayNecklaces.SingleTrack.ddProperty :
  Tiozzo.Theorem87 → Tiozzo.TuningNesting →
    ∀ (p : ℕ) [NeZero p], p.Prime → Odd p → DDProperty p
```

Combined with Dzoba's Theorem A, this gives an optimal single-track Gray code at every odd prime length. The two definitions marked as written differently are equivalent to his. Our `prefixParity w i` is `w 0 xor … xor w i`, where his takes the parity of the number of ones among positions `0, …, i`. Our `rank` builds the binary number from these parities by the recursion `r ↦ 2r + digit`, where his sums `2^(n-1-i)` over the positions with odd parity. We have checked in Lean, against a local copy of his development, that our `DDProperty n` is equivalent to his `STGC.DDProperty n`. That check imports his code, so it is kept out of this repository.

## License

These files are under the repository's [Apache License, Version 2.0](../LICENSE).
