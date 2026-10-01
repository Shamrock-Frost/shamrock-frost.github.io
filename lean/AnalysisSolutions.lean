import Mathlib

/-
Fall 2026 Utah Lean Seminar, September 29th, 2026
Analysis and calculus in Mathlib
-/

open Filter Topology
open scoped Real

/-!
## 1. Limits with ε and N

A sequence of real numbers is a function `ℕ → ℝ`. This is the definition of convergence from a
first analysis course.
-/

def ConvergesTo (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε

example (c : ℝ) : ConvergesTo (fun _ => c) c := by
  intro ε hε
  use 0
  intro n _
  simp
  exact hε

-- Exercise 1.1
theorem ConvergesTo.add {a b : ℕ → ℝ} {L M : ℝ} (ha : ConvergesTo a L) (hb : ConvergesTo b M) :
    ConvergesTo (a + b) (L + M) := by
  intro ε hε
  obtain ⟨N₁, h₁⟩ := ha (ε / 2) (half_pos hε)
  obtain ⟨N₂, h₂⟩ := hb (ε / 2) (half_pos hε)
  use max N₁ N₂
  intro n hn
  obtain ⟨hn₁, hn₂⟩ := max_le_iff.mp hn
  rw [Pi.add_apply, add_sub_add_comm, ← add_halves ε]
  exact lt_of_le_of_lt (abs_add_le _ _) (add_lt_add (h₁ n hn₁) (h₂ n hn₂))

/-
With ε's and δ's, every kind of limit (functions as `x → a`, as `x → ∞`, one-sided, ...) needs
its own definition and its own copy of every theorem. Mathlib unifies these with filters.
-/


/-! ## 2. Filters

A *filter* on `X` is a collection of subsets of `X` ("big" sets) that
contains `X` and is closed under both supersets and finite intersections.
* `atTop : Filter ℕ` consists of the sets containing a tail `{n | n ≥ N}`.
* `𝓝 a : Filter ℝ` consists of the neighbourhoods of `a`.

`Tendsto f F G` means: the preimage under `f` of every `G`-big set is `F`-big.
So `Tendsto s atTop (𝓝 a)` says every neighbourhood of `a` contains a tail of
`s`, which is exactly convergence. Read `Tendsto f F G` as "`f` tends to `G` along `F`"

`∀ᶠ x in F, p x` (read "eventually p") means `{x | p x}` is `F`-big.
-/

-- Exercise 2.1
-- Hint: don't unfold anything!
theorem convergesTo_iff_tendsto (a : ℕ → ℝ) (L : ℝ) :
    ConvergesTo a L ↔ Tendsto a atTop (𝓝 L) :=
  .symm Metric.tendsto_atTop

/- With Exercise 2.1, Mathlib's library of facts about `Tendsto` applies to `ConvergesTo`. This is
Exercise 1.1 again. -/
#check Tendsto.add

example {a b : ℕ → ℝ} {L M : ℝ} (ha : ConvergesTo a L) (hb : ConvergesTo b M) :
    ConvergesTo (a + b) (L + M) := by
  rw [convergesTo_iff_tendsto] at *
  exact ha.add hb

-- see also; compositional API!
#check Tendsto.mul
#check Tendsto.pow
#check Tendsto.const_mul
#check Tendsto.sub
#check Tendsto.comp
/- The tactic `fun_prop` proves that functions which are "obviously"
continuous or differentiable are such, chaining the compositional lemmas. -/

-- Exercise 2.2
example {a b : ℕ → ℝ} {L M : ℝ} (ha : Tendsto a atTop (𝓝 L)) (hb : Tendsto b atTop (𝓝 M)) :
    Tendsto (fun n => 3 * a n ^ 2 - b n) atTop (𝓝 (3 * L ^ 2 - M)) :=
  ((ha.pow 2).const_mul _).sub hb

/-!
## 3. Unified limits

Nothing in `Tendsto.add` is specific to sequences: it holds for any filter on the domain.
Each filter gives a different kind of limit.

* `Tendsto a atTop (𝓝 L)`: the sequence `a n → L`
* `Tendsto a atTop atTop`: `a n → ∞`
* `Tendsto f atTop (𝓝 L)`: `f x → L` as `x → ∞`, for `f : ℝ → ℝ`
  (`atTop : Filter ℝ` is the collection of sets containing some `[R, ∞)`)
* `Tendsto f (𝓝[≠] x) (𝓝 L)`: `f y → L` as `y → x`, where `𝓝[≠] x` is the collection of sets
  containing a punctured ball around `x`
* `Tendsto f (𝓝[>] x) (𝓝 L)`: `f y → L` as `y → x` from the right (`𝓝[<] x`: from the left)
* `Tendsto f (𝓝 x) (𝓝 (f x))`: `f` is continuous at `x`. This is Mathlib's definition of
  `ContinuousAt f x`.
-/

-- Exercise 3.1
theorem tendsto_inv_natCast : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_nhds_zero_nat

-- Exercise 3.2
example : Tendsto (fun x : ℝ => Real.exp (x⁻¹)) (𝓝[>] 0) atTop :=
  Real.tendsto_exp_comp_atTop.mpr tendsto_inv_nhdsGT_zero

-- Exercise 3.3
-- try using `Continuous.tendsto`
example : Tendsto (fun x : ℝ => x ^ 2 + 3 * x) (𝓝 2) (𝓝 10) := by
  convert Continuous.tendsto _ _
  · norm_num
  · fun_prop

-- Exercise 3.4 (challenge)
example : Tendsto (fun n : ℕ => Real.sin n / n) atTop (𝓝 0) := by
  rw [← convergesTo_iff_tendsto]
  intro ε hε
  obtain ⟨N, hN⟩ := (convergesTo_iff_tendsto _ _).mpr tendsto_inv_natCast ε hε
  use N
  intro n hn
  refine lt_of_le_of_lt ?_ (hN n hn)
  conv => congr <;> rw [sub_zero]; rw [abs_div, Nat.abs_cast]
  refine le_of_le_of_eq ?_ (abs_of_nonneg ?_).symm
  · refine le_of_le_of_eq ?_ (inv_eq_one_div (n : ℝ)).symm
    refine div_le_div_of_nonneg_right (Real.abs_sin_le_one n) ?_
    exact n.cast_nonneg'
  · exact inv_nonneg_of_nonneg n.cast_nonneg'

/-!
## 4. Derivatives

For `f : ℝ → ℝ`:
* `HasDerivAt f f' x` says that `f` is differentiable at `x` with derivative `f'`.
* `deriv f x` is the derivative of `f` at `x` if it exists, and `0` if it doesn't.

`HasDerivAt` is defined with filters.
It is equivalent to the difference quotient tending to `f'` as `t → 0` with `t ≠ 0`:
-/
#check hasDerivAt_iff_tendsto_slope_zero

#check hasDerivAt_pow
#check hasDerivAt_id
#check HasDerivAt.add
#check HasDerivAt.const_mul
#check HasDerivAt.exp

/- `hasDerivAt_pow 2 x` gives the derivative as `↑2 * x ^ (2 - 1)`, which equals `2 * x` but is not
written that way. `HasDerivAt.congr_deriv` replaces the derivative with an equal one. -/
#check HasDerivAt.congr_deriv

example (x : ℝ) : HasDerivAt (fun x => x ^ 2) (2 * x) x := by
  have h := hasDerivAt_pow 2 x
  apply h.congr_deriv
  norm_num

-- Exercise 4.1
theorem hasDerivAt_cubic (x : ℝ) : HasDerivAt (fun x => x ^ 3 + 5 * x) (3 * x ^ 2 + 5) x :=
  (hasDerivAt_pow 3 x).add (hasDerivAt_const_mul 5)

-- Exercise 4.2
theorem hasDerivAt_exp_sq (x : ℝ) :
    HasDerivAt (fun x => Real.exp (x ^ 2)) (2 * x * Real.exp (x ^ 2)) x :=
  .congr_deriv (.exp ((hasDerivAt_pow 2 x).congr_deriv (congr_arg _ (pow_one x))))
    (mul_comm _ _)

-- Exercise 4.3
#check HasDerivAt.deriv

example : deriv (fun x : ℝ => x ^ 3 + 5 * x) 2 = 17 := by
  rw [deriv_fun_add]
  · norm_num
  all_goals fun_prop

-- Exercise 4.4
-- Prove this using `strictMono_of_deriv_pos`
example : StrictMono (fun x : ℝ => x ^ 3 + 5 * x) := by
  refine strictMono_of_deriv_pos ?_
  intro x
  rw [deriv_fun_add, deriv_pow_field, deriv_const_mul_id']
  · norm_num
    positivity
  all_goals fun_prop

-- Exercise 4.5.
-- Prove this using `is_const_of_deriv_eq_zero`; why does it need `Differentiable 𝕜 f`?
#check is_const_of_deriv_eq_zero

example (f : ℝ → ℝ) (hf : ∀ x, HasDerivAt f 0 x) : f 1 = f 0 :=
  is_const_of_deriv_eq_zero (HasDerivAt.differentiableAt <| hf ·)
    (HasDerivAt.deriv <| hf ·) 1 0

/-!
## 5. Integrals

`∫ x in a..b, f x` is the integral of `f` from `a` to `b`: the Lebesgue integral over `(a, b]`, or
minus the integral over `(b, a]` when `b < a`. If `f` is not integrable, the integral is the junk
value `0`.
-/
#check integral_pow
#check integral_sin
#check integral_id
#check intervalIntegral.integral_add
#check intervalIntegral.integral_const

example : ∫ x in (0 : ℝ)..1, x ^ 2 = 1 / 3 := by
  rw [integral_pow]
  norm_num

-- Exercise 5.1
example : ∫ x in (0 : ℝ)..π, Real.sin x = 2 := by
  simp only [integral_sin, Real.cos_zero, Real.cos_pi,
    sub_neg_eq_add, one_add_one_eq_two]

-- Exercise 5.2
-- see Continuous.intervalIntegrable
example : ∫ x in (0 : ℝ)..1, (x + x ^ 2) = 5 / 6 := by
  rw [intervalIntegral.integral_add, integral_pow, integral_id]
  · rw [one_pow, one_pow, zero_pow_eq_zero.mpr two_ne_zero,
      zero_pow_eq_zero.mpr three_ne_zero, sub_zero]
    ring
  all_goals refine Continuous.intervalIntegrable ?_ 0 1; fun_prop

-- Exercise 5.3
-- try using the second FToC!
#check intervalIntegral.integral_eq_sub_of_hasDerivAt

example : ∫ x in (0 : ℝ)..1, 2 * x * Real.exp (x ^ 2) = Real.exp 1 - 1 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x => Real.exp (x ^ 2))]
  · norm_num
  · refine fun x _ => (hasDerivAt_pow 2 x).exp.congr_deriv ?_
    push_cast
    ring
  · exact Continuous.intervalIntegrable (by fun_prop) 0 1

-- Exercise 5.4 (challenge)
#check Continuous.integral_hasStrictDerivAt

example (x : ℝ) :
    HasDerivAt (fun u => ∫ t in (0 : ℝ)..u, Real.exp (t ^ 2)) (Real.exp (x ^ 2)) x :=
  ((by fun_prop : Continuous fun t : ℝ => Real.exp (t ^ 2)).integral_hasStrictDerivAt 0 x).hasDerivAt
