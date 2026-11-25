module

public import GrayNecklaces.NoLargeWindow

/-!
# The odd-prime Degni–Drisko theorem

The theorem takes two statements of Tiozzo (2015) as explicit hypotheses.  Their exact form is in
`GrayNecklaces/Tiozzo.lean`, and the citations are in Section 8 of `proof.pdf`.  The equality of the
two leader sets, which also follows from the Degni–Drisko pairing (their Corollaries 3.10 and 4.3),
is proved in `GrayNecklaces.sieve` and stated as `GrayNecklaces.leader_sub_iff_add`.
-/

@[expose] public section

namespace GrayNecklaces

/-- **Degni–Drisko at every odd prime length.**

From every rotation class of binary words of odd prime length, take the word of maximum standard
BRGC rank (the first word in reversed BRGC order).  Consecutive retained words differ in exactly one
bit, except for the terminal transition `1^p → 0^p`.

Hypotheses (Tiozzo, *Topological entropy of quadratic polynomials and dimension of sections of the
Mandelbrot set*, Adv. Math. 273 (2015), 651–715, <https://doi.org/10.1016/j.aim.2014.12.033>):
* `h87` is Theorem 8.7, the bisection algorithm, with Proposition 8.4 and §8.1.
* `h9` is the nesting of overlapping tuning windows from §9. -/
theorem oddPrimeDegniDrisko (h87 : Tiozzo.Theorem87) (h9 : Tiozzo.TuningNesting) :
    OddPrimeDegniDrisko :=
  main_of_core h87 (fun _ hp hodd => reflectionCore h87 h9 hp hodd)

end GrayNecklaces
