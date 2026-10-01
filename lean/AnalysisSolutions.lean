import Mathlib

/-
Fall 2026 Utah Lean Seminar, September 29th, 2026
Analysis and calculus in Mathlib: solutions
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
  obtain ⟨N₁, hN₁⟩ := ha (ε / 2) (by positivity)
  obtain ⟨N₂, hN₂⟩ := hb (ε / 2) (by positivity)
  use max N₁ N₂
  intro n hn
  have h₁ : |a n - L| < ε / 2 := hN₁ n (le_of_max_le_left hn)
  have h₂ : |b n - M| < ε / 2 := hN₂ n (le_of_max_le_right hn)
  have h₃ : a n + b n - (L + M) = (a n - L) + (b n - M) := by ring
  have h₄ := abs_add_le (a n - L) (b n - M)
  rw [Pi.add_apply, h₃]
  linarith

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
    ConvergesTo a L ↔ Tendsto a atTop (𝓝 L) := by
  rw [Metric.tendsto_atTop]
  rfl

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
    Tendsto (fun n => 3 * a n ^ 2 - b n) atTop (𝓝 (3 * L ^ 2 - M)) := by
  exact ((ha.pow 2).const_mul 3).sub hb

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
theorem tendsto_inv_natCast : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) := by
  exact tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop

-- Exercise 3.2
example : Tendsto (fun x : ℝ => Real.exp (x⁻¹)) (𝓝[>] 0) atTop := by
  exact Real.tendsto_exp_atTop.comp tendsto_inv_nhdsGT_zero

-- Exercise 3.3
-- try using `Continuous.tendsto`
example : Tendsto (fun x : ℝ => x ^ 2 + 3 * x) (𝓝 2) (𝓝 10) := by
  have h : Continuous (fun x : ℝ => x ^ 2 + 3 * x) := by fun_prop
  have h2 := h.tendsto 2
  norm_num at h2
  exact h2

-- Exercise 3.4 (challenge)
example : Tendsto (fun n : ℕ => Real.sin n / n) atTop (𝓝 0) := by
  apply squeeze_zero_norm _ tendsto_inv_natCast
  intro n
  rw [Real.norm_eq_abs, abs_div, Nat.abs_cast, div_eq_mul_inv]
  apply mul_le_of_le_one_left
  · positivity
  · exact Real.abs_sin_le_one n

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
theorem hasDerivAt_cubic (x : ℝ) : HasDerivAt (fun x => x ^ 3 + 5 * x) (3 * x ^ 2 + 5) x := by
  have h := (hasDerivAt_pow 3 x).add ((hasDerivAt_id' x).const_mul 5)
  apply h.congr_deriv
  norm_num

-- Exercise 4.2
theorem hasDerivAt_exp_sq (x : ℝ) :
    HasDerivAt (fun x => Real.exp (x ^ 2)) (2 * x * Real.exp (x ^ 2)) x := by
  have h := (hasDerivAt_pow 2 x).exp
  apply h.congr_deriv
  norm_num
  ring

-- Exercise 4.3
#check HasDerivAt.deriv

example : deriv (fun x : ℝ => x ^ 3 + 5 * x) 2 = 17 := by
  rw [(hasDerivAt_cubic 2).deriv]
  norm_num

-- Exercise 4.4
-- Prove this using `strictMono_of_deriv_pos`
example : StrictMono (fun x : ℝ => x ^ 3 + 5 * x) := by
  apply strictMono_of_deriv_pos
  intro x
  rw [(hasDerivAt_cubic x).deriv]
  positivity

-- Exercise 4.5.
-- Prove this using `is_const_of_deriv_eq_zero`; why does it need `Differentiable 𝕜 f`?
#check is_const_of_deriv_eq_zero

example (f : ℝ → ℝ) (hf : ∀ x, HasDerivAt f 0 x) : f 1 = f 0 := by
  apply is_const_of_deriv_eq_zero
  · intro x
    exact (hf x).differentiableAt
  · intro x
    exact (hf x).deriv

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
  rw [integral_sin]
  norm_num

-- Exercise 5.2
-- see Continuous.intervalIntegrable
example : ∫ x in (0 : ℝ)..1, (x + x ^ 2) = 5 / 6 := by
  rw [intervalIntegral.integral_add]
  · rw [integral_id, integral_pow]
    norm_num
  · apply Continuous.intervalIntegrable
    fun_prop
  · apply Continuous.intervalIntegrable
    fun_prop

-- Exercise 5.3
-- try using the second FToC!
#check intervalIntegral.integral_eq_sub_of_hasDerivAt

example : ∫ x in (0 : ℝ)..1, 2 * x * Real.exp (x ^ 2) = Real.exp 1 - 1 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x => Real.exp (x ^ 2))]
  · norm_num
  · intro x _
    exact hasDerivAt_exp_sq x
  · apply Continuous.intervalIntegrable
    fun_prop

-- Exercise 5.4 (challenge)
#check Continuous.integral_hasStrictDerivAt

example (x : ℝ) :
    HasDerivAt (fun u => ∫ t in (0 : ℝ)..u, Real.exp (t ^ 2)) (Real.exp (x ^ 2)) x := by
  have h : Continuous (fun t : ℝ => Real.exp (t ^ 2)) := by fun_prop
  exact (h.integral_hasStrictDerivAt 0 x).hasDerivAt
