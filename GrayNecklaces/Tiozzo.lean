module

public import Mathlib

/-!
# Published inputs from Tiozzo (2015), stated as propositions

Giulio Tiozzo, *Topological entropy of quadratic polynomials and dimension of sections of the
Mandelbrot set*, Advances in Mathematics 273 (2015), 651–715.
DOI: <https://doi.org/10.1016/j.aim.2014.12.033> · Full text:
<https://www.math.toronto.edu/tiozzo/docs/Hdim.pdf>

This file contains definitions only.  The propositions `Theorem87` and `TuningNesting` enter the
proof as explicit hypotheses of `GrayNecklaces.oddPrimeDegniDrisko`.  See `README.md` and
Section 8 of `proof.pdf`.

## Conventions

* Angles are real numbers in `[0, 1)` (the circle `S¹ = ℝ/ℤ`).
* `tent x = min (2x) (2 - 2x)` is Tiozzo's full tent map `T` on `[0,1]` (§8, page 21 of the
  linked preprint).
* `leafLength θ` is the length `ℓ(θ)` of the leaf joining `θ` and `1-θ` (§8, page 20 of the
  linked preprint).  It is `2θ` for `0 ≤ θ < 1/2` and `2 - 2θ` for `1/2 ≤ θ < 1`.
* `realAngles` is the set `R` of real parameter angles, in the combinatorial form of
  **Proposition 8.4**: `R = {θ ∈ S¹ : T^n(ℓ_θ) ≤ ℓ_θ for all n ≥ 0}`.
* A *real hyperbolic window* `(θ₂, θ₁) ⊆ [0, 1/2]` is the interval of external angles of a real
  hyperbolic component `W`, between the two rays landing on `∂W ∩ ℝ` (§1.2, before Theorem 1.5).
  By §8.1 (the set `R` is the closure of the angles landing on boundaries of real hyperbolic
  components, and by the proof of Proposition 8.4 every angle of `[0,1/2]` outside `R` lies in the
  opening of a real hyperbolic component) these are the connected components of
  `[0, 1/2] \ R`.  We encode a window as an open interval with endpoints in `R` and no point of
  `R` inside.
* The *pseudocenter* of an interval is its dyadic rational `c/2^n` with least `n`
  (Definition 1.4).
* `finBin s` is the value of the finite binary expansion `0.s₁s₂…sₙ`, and `perBin s` is the value
  of the purely periodic expansion `0.s₁…sₙs₁…sₙ…` (the overline notation of Theorem 8.7).
-/

@[expose] public section

namespace GrayNecklaces
namespace Tiozzo

/-- Tiozzo's tent map `T(x) = min{2x, 2-2x}`. -/
noncomputable def tent (x : ℝ) : ℝ := min (2 * x) (2 - 2 * x)

/-- The leaf length `ℓ(θ)` (Tiozzo §8). -/
noncomputable def leafLength (θ : ℝ) : ℝ := if θ < 1 / 2 then 2 * θ else 2 - 2 * θ

/-- The set of real parameter angles, characterized by Tiozzo's Proposition 8.4. -/
def realAngles : Set ℝ :=
  {θ | 0 ≤ θ ∧ θ < 1 ∧ ∀ n : ℕ, tent^[n] (leafLength θ) ≤ leafLength θ}

/-- A real hyperbolic window `(θ₂, θ₁)` with `0 ≤ θ₂ < θ₁ ≤ 1/2`: a complementary interval of
the real parameter angles in `[0, 1/2]`. -/
def IsRealHyperbolicWindow (θ₂ θ₁ : ℝ) : Prop :=
  0 ≤ θ₂ ∧ θ₂ < θ₁ ∧ θ₁ ≤ 1 / 2 ∧ θ₂ ∈ realAngles ∧ θ₁ ∈ realAngles ∧
    ∀ θ, θ₂ < θ → θ < θ₁ → θ ∉ realAngles

/-- The binary digit `b` as a real number. -/
noncomputable def bit (b : Bool) : ℝ := if b then 1 else 0

/-- The finite binary expansion `0.s₁s₂…sₙ`. -/
noncomputable def finBin (s : List Bool) : ℝ :=
  ∑ i ∈ Finset.range s.length, bit (s.getD i false) / 2 ^ (i + 1)

/-- The purely periodic binary expansion `0.(s₁…sₙ)(s₁…sₙ)…`. -/
noncomputable def perBin (s : List Bool) : ℝ :=
  ∑' i : ℕ, bit (s.getD (i % s.length) false) / 2 ^ (i + 1)

/-- `x` is the dyadic pseudocenter of the interval `(θ₂, θ₁)`: the dyadic rational in it with the
least power of two in the denominator (Tiozzo, Definition 1.4). -/
def IsPseudocenter (θ₂ θ₁ x : ℝ) : Prop :=
  θ₂ < x ∧ x < θ₁ ∧ ∃ n : ℕ, (∃ c : ℤ, x = c / 2 ^ n) ∧
    ∀ (n' : ℕ) (c' : ℤ), θ₂ < c' / 2 ^ n' → (c' : ℝ) / 2 ^ n' < θ₁ → n ≤ n'

/-- **Tiozzo, Theorem 8.7** (the bisection algorithm), for a single real hyperbolic window.

Let `(θ₂, θ₁)` be a real hyperbolic window, whose endpoints are the external angles of two real
parameters on `∂M`, and let `θ* = 0.s₁…s_{n-1}sₙ` with `sₙ = 1` be the binary expansion of its
dyadic pseudocenter.  Theorem 8.7 says that the hyperbolic window of smallest period in
`(θ₂, θ₁)` has endpoints `α₂ = 0.(s₁…s_{n-1})‾` and `α₁ = 0.(s₁…s_{n-1}š₁…š_{n-1})‾`.
Since `(θ₂, θ₁)` is itself a window and windows are disjoint, that window is `(θ₂, θ₁)`.

Tiozzo proves Theorem 8.7 as a rephrasing of Proposition 3 of C. Bonanno, C. Carminati, S. Isola
and G. Tiozzo, *Dynamics of continued fractions and kneading sequences of unimodal maps*, Discrete
Contin. Dyn. Syst. 33 (2013), 1313–1332, <https://doi.org/10.3934/dcds.2013.33.1313>. -/
def Theorem87 : Prop :=
  ∀ (θ₂ θ₁ : ℝ) (s : List Bool), IsRealHyperbolicWindow θ₂ θ₁ →
    IsPseudocenter θ₂ θ₁ (finBin s) → s.getLast? = some true →
    θ₂ = perBin s.dropLast ∧ θ₁ = perBin (s.dropLast ++ s.dropLast.map (fun b => !b))

/-- `n` is the minimal period of the angle `θ` under the doubling map `θ ↦ 2θ mod 1`. -/
def DoublingPeriod (θ : ℝ) (n : ℕ) : Prop :=
  0 < n ∧ Int.fract (2 ^ n * θ) = Int.fract θ ∧
    ∀ m, 0 < m → m < n → Int.fract (2 ^ m * θ) ≠ Int.fract θ

/-- `ω = min {x > α : T^n(x) = α}`, the right end of the tuning window `Ω_W = (α, ω]`. -/
def IsTuningEnd (α : ℝ) (n : ℕ) (ω : ℝ) : Prop :=
  α < ω ∧ tent^[n] ω = α ∧ ∀ x, α < x → x < ω → tent^[n] x ≠ α

/-- **Tiozzo, §9 (after Proposition 9.1, before Definition 9.2): overlapping tuning windows are
nested.**

For a real hyperbolic component `W` with window `(θ₂, θ₁)`, the root `c` of `W` has the
characteristic angle `θ_c = θ₂` and characteristic length `ℓ_c = ℓ(θ₂)`.  Let `n` be the minimal
period of `θ_c` under doubling.  The tuning window is `Ω_W = (α, ω]` with `α = ℓ_c` and
`ω = min{x > α : T^n(x) = α}`.  Tiozzo states without proof that overlapping tuning windows are
nested.

The corresponding statement for α-continued fractions is proved in Lemma 15 of C. Carminati and
G. Tiozzo, *Tuning and plateaux for the entropy of α-continued fractions*, Nonlinearity 26 (2013),
1049–1070, <https://doi.org/10.1088/0951-7715/26/4/1049>, which shows that tuning windows whose
closures meet are nested.  Their Propositions 42 and 43 match those windows' maximal intervals
and tuning operators with real hyperbolic components and Douady–Hubbard tuning, through a
monotone dictionary. -/
def TuningNesting : Prop :=
  ∀ (θ₂ θ₁ φ₂ φ₁ ω ω' : ℝ) (n n' : ℕ),
    IsRealHyperbolicWindow θ₂ θ₁ → IsRealHyperbolicWindow φ₂ φ₁ →
    DoublingPeriod θ₂ n → DoublingPeriod φ₂ n' →
    IsTuningEnd (leafLength θ₂) n ω → IsTuningEnd (leafLength φ₂) n' ω' →
    (Set.Ioc (leafLength θ₂) ω ∩ Set.Ioc (leafLength φ₂) ω').Nonempty →
    Set.Ioc (leafLength θ₂) ω ⊆ Set.Ioc (leafLength φ₂) ω' ∨
      Set.Ioc (leafLength φ₂) ω' ⊆ Set.Ioc (leafLength θ₂) ω

end Tiozzo
end GrayNecklaces
