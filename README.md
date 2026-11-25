# The Degni–Drisko conjecture at odd prime lengths

A proof of the odd-prime case of **Degni and Drisko's conjecture** on binary necklaces in reflected Gray code order, formalized in Lean 4.

**Preliminary manuscript.** The proof is an early draft shared for feedback. The exposition may change as the argument is revised and simplified. Lean's kernel has checked the formal proof with two results from Tiozzo's work, listed below, as explicit hypotheses. External independent mathematical review has *not* been completed.

**Reading the result.** The draft in [proof.pdf](proof.pdf) states the theorem and gives the mathematical proof. The verification commands and a guide to the Lean modules are below.

**AI disclosure.** Various AI tools assisted with mathematical exploration, checking arguments, drafting the manuscript, and developing the Lean formalization.

## Statement

Let $p$ be an odd prime. From every necklace (rotation class) of binary words of length $p$, retain the word that comes first in reversed binary reflected Gray order, which Degni and Drisko call the Gray order. Consecutive retained words, listed in that order, differ in exactly one bit, except for the final step $1^p\to 0^p$.

This is Conjecture 3.12 of [Degni and Drisko (2007)](https://doi.org/10.37236/926) at odd prime lengths. Their conjecture covers every length $n$, with an exception at powers $\beta^k$, $k>1$, of odd prime necklaces $\beta$. In their terms a necklace is odd when it has an odd number of ones, and prime when it is aperiodic. At odd prime length the only such power is $1^p$, which gives the final step. They checked the conjecture by computer for every $n\le 37$.

The proof assumes two results of Tiozzo, and he states the second without proof. See [Verification](#verification).

The main declaration is `GrayNecklaces.oddPrimeDegniDrisko` in [GrayNecklaces/Main.lean](GrayNecklaces/Main.lean). Its conclusion `GrayNecklaces.OddPrimeDegniDrisko` is defined in [GrayNecklaces/Statement.lean](GrayNecklaces/Statement.lean).

## Consequences

Two open problems from [Mütze's survey of combinatorial Gray codes](https://arxiv.org/abs/2202.01280) are answered at odd prime lengths, the second together with Dzoba's Theorem A. The Lean files for both are in [corollaries/](corollaries/README.md), which builds separately.

- **Gray codes for necklaces (Problem P17).** Savage asked whether the necklaces of every odd length admit a 1-Gray code, a listing of all necklaces in which consecutive necklaces have representatives differing in one bit. Such a code is necessarily a path from $0^n$ to $1^n$. Degni and Drisko observed that their conjecture at a prime length gives one, by moving $0^n$ to the front of their list. The theorem therefore answers this for every odd prime length.
- **Optimal single-track Gray codes (Problem P13).** Single-track Gray codes were introduced in 1996. Whether one of length $p$ and period $2^p-2$ exists at every prime $p\ge3$ is Problem P13 in Mütze's survey. [Dzoba's Theorem A](https://arxiv.org/abs/2610.24758) derives such a code for every prime $p\ge7$ from the Degni–Drisko property, in a form that uses least-rank representatives and requires only necklace adjacency, and gives explicit codes for $p=3,5$. We prove that form of the property in Lean. With his theorem, this gives an optimal code at every odd prime length.

## Verification

Install [Lean and its toolchain manager, elan](https://lean-lang.org/install/). From the repository root, run:

```sh
lake exe cache get
lake build
lake env lean --trust=0 GrayNecklaces/Audit.lean
```

The project pins Lean **4.36.0** and mathlib through `lean-toolchain` and `lake-manifest.json`. `lake build` builds only the main theorem. The audit reports the following standard Lean axioms for it:

```text
[propext, Classical.choice, Quot.sound]
```

The theorem's signature is:

```text
GrayNecklaces.oddPrimeDegniDrisko :
  Tiozzo.Theorem87 → Tiozzo.TuningNesting → OddPrimeDegniDrisko
```

Two results from Tiozzo's work are explicit hypotheses. The sieve and the equality of leader sets use only the first. The second enters only in the reflection argument of Sections 4–6. Both are stated and cited in [GrayNecklaces/Tiozzo.lean](GrayNecklaces/Tiozzo.lean) and in Section 8 of [proof.pdf](proof.pdf):

1. `Tiozzo.Theorem87` gives the endpoints of the real hyperbolic windows from the dyadic pseudocenter. It is Theorem 8.7 of G. Tiozzo, *Topological entropy of quadratic polynomials and dimension of sections of the Mandelbrot set*, Adv. Math. 273 (2015) ([doi:10.1016/j.aim.2014.12.033](https://doi.org/10.1016/j.aim.2014.12.033)), applied to an interval that is itself a real hyperbolic window. That the windows are exactly the gaps of the real parameter angles comes from Proposition 8.4, its proof, and §8.1. Tiozzo derives Theorem 8.7 from Proposition 3 of C. Bonanno, C. Carminati, S. Isola and G. Tiozzo, *Dynamics of continued fractions and kneading sequences of unimodal maps*, Discrete Contin. Dyn. Syst. 33 (2013) ([doi:10.3934/dcds.2013.33.1313](https://doi.org/10.3934/dcds.2013.33.1313)).
2. `Tiozzo.TuningNesting` says that overlapping real tuning windows are nested. Tiozzo states this in §9 of the same paper without proof. Lemma 15 of C. Carminati and G. Tiozzo, *Tuning and plateaux for the entropy of α-continued fractions*, Nonlinearity 26 (2013) ([doi:10.1088/0951-7715/26/4/1049](https://doi.org/10.1088/0951-7715/26/4/1049)), proves the corresponding statement for α-continued fractions, and their Propositions 42 and 43 relate those windows to the real slice. The transfer of their lemma to the real slice is not written out there.

To trust the result, a reader checks the conclusion `OddPrimeDegniDrisko` in [GrayNecklaces/Statement.lean](GrayNecklaces/Statement.lean) (about 50 lines), the two hypotheses in [GrayNecklaces/Tiozzo.lean](GrayNecklaces/Tiozzo.lean), the signature above and the axiom report. Everything else is proof checked by Lean's kernel.

## Reading the proof

Start with [proof.pdf](proof.pdf). The signed distance of an integer modulo $M$ is its distance to the nearest multiple of $M$, and a signed leader modulo $M$ is a positive integer that equals the least positive signed distance in its orbit under doubling. The proof translates necklace representatives into orbits of signed doubling. Adjacency of consecutive representatives becomes a reflection identity for consecutive signed leaders. A sieve by dyadic windows describes the leaders, and a covering bound for a capped tent map produces the surviving rank that forces the reflection. The proof does not assume Degni and Drisko's pairing of odd and even representatives (their Corollaries 3.10 and 4.3). The sieve proves, using Theorem 8.7, that the odd signed leaders below $2^p/3$ are the same modulo $2^p-1$ and $2^p+1$ (`GrayNecklaces.sieve`, `GrayNecklaces.leader_sub_iff_add`).

For a route through the formalization:

1. [Statement](GrayNecklaces/Statement.lean) defines the conclusion. [Basic](GrayNecklaces/Basic.lean) defines signed distances and signed-doubling leaders. [Ranks](GrayNecklaces/Ranks.lean) relates rotation of words to signed doubling of ranks. [The assembly](GrayNecklaces/Assembly.lean) derives the exported statement from the reflection property `ReflectionCore` (Section 2).
2. [Windows](GrayNecklaces/Windows.lean) and [the elementary sieve](GrayNecklaces/Sieve.lean) prove that non-leaders are deleted and that deleted ranks are non-leaders, including the renormalization step. [The Tiozzo bridge](GrayNecklaces/TiozzoBridge.lean) and [actual windows](GrayNecklaces/Actual.lean) translate the two hypotheses into window coordinates. The sieve lemma and the equality of leader sets use only Theorem 8.7. The nesting hypothesis is first used in [Maximal windows](GrayNecklaces/Maximal.lean), in the facts about distinct maximal windows that steps 3–5 rely on. [Maximal windows](GrayNecklaces/Maximal.lean) prove the sieve lemma and the equality of leader sets (Section 3).
3. [DeletedRun](GrayNecklaces/DeletedRun.lean), [CentralMaximal](GrayNecklaces/CentralMaximal.lean), [DeletingWindows](GrayNecklaces/DeletingWindows.lean) and [RunBound](GrayNecklaces/RunBound.lean) set up a deleted run between consecutive leaders and bound it. [Reflection](GrayNecklaces/Reflection.lean) proves reflection when every finer window is small (Section 4).
4. [TentOrbit](GrayNecklaces/TentOrbit.lean), [TentDyn](GrayNecklaces/TentDyn.lean), [TentRet](GrayNecklaces/TentRet.lean), [TentGrowth](GrayNecklaces/TentGrowth.lean) and [TentCover](GrayNecklaces/TentCover.lean) prove the finite-time covering lemma for the capped tent map (Section 5).
5. [The mask](GrayNecklaces/Mask.lean) bounds gaps between smaller-scale survivors. [MaskSurvivor](GrayNecklaces/MaskSurvivor.lean), [GapSurvivor](GrayNecklaces/GapSurvivor.lean), [Extraction](GrayNecklaces/Extraction.lean), [NegativePhase](GrayNecklaces/NegativePhase.lean), [Truncation](GrayNecklaces/Truncation.lean), [WingArithmetic](GrayNecklaces/WingArithmetic.lean) and [WingContradiction](GrayNecklaces/WingContradiction.lean) find a survivor before the first large window. [NoLargeWindow](GrayNecklaces/NoLargeWindow.lean) concludes the reflection property (Section 6).

## License

Source and documentation are licensed under the [Apache License, Version 2.0](LICENSE).
