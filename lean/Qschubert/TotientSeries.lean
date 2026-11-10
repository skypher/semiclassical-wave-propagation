import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Data.Nat.Totient

/-!
# The Dirichlet series of Euler's totient function

Stage M4 of the plan for Proposition `ev:mod` (`lean/BLUEPRINT.md`): for `Re w > 2`,

`∑_{c ≥ 1} φ(c) c^{-w} = ζ(w - 1) / ζ(w)`

(`LSeries_totient`). In the manuscript `N_c = φ(c)` is the number of residues modulo `c` prime to `c`, and the identity is
used with `w = 2s`.
-/

namespace Qschubert

open LSeries Nat ArithmeticFunction
open scoped LSeries.notation ArithmeticFunction.zeta

/-- The coefficients `c ↦ φ(c)`. -/
noncomputable def totC (n : ℕ) : ℂ := (Nat.totient n : ℂ)

/-- The coefficients `c ↦ c`. -/
noncomputable def idC (n : ℕ) : ℂ := (n : ℂ)

lemma toArithmeticFunction_zeta :
    toArithmeticFunction (fun n : ℕ => ((ArithmeticFunction.zeta n : ℕ) : ℂ)) = (ArithmeticFunction.zeta : ArithmeticFunction ℂ) := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [toArithmeticFunction]
  · simp [toArithmeticFunction, hn]

lemma totC_convolution_zeta : totC ⍟ (fun n : ℕ => ((ArithmeticFunction.zeta n : ℕ) : ℂ)) = idC := by
  funext n
  rw [LSeries.convolution, toArithmeticFunction_zeta, ArithmeticFunction.coe_mul_zeta_apply, idC]
  have h : ∀ d ∈ n.divisors, toArithmeticFunction totC d = ((Nat.totient d : ℕ) : ℂ) := by
    intro d hd
    have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
    simp [toArithmeticFunction, hd0, totC]
  rw [Finset.sum_congr rfl h, ← Nat.cast_sum, Nat.sum_totient]

lemma summable_totC {w : ℂ} (hw : 2 < w.re) : LSeriesSummable totC w := by
  refine LSeriesSummable_of_le_const_mul_rpow (x := 2) hw ⟨1, fun n _ => ?_⟩
  rw [totC, Complex.norm_natCast, one_mul, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]
  exact_mod_cast Nat.totient_le n

lemma LSeries_idC {w : ℂ} (hw : 2 < w.re) : LSeries idC w = riemannZeta (w - 1) := by
  rw [← LSeries_one_eq_riemannZeta (s := w - 1) (by simp; linarith), LSeries, LSeries]
  refine tsum_congr fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, idC, Pi.one_apply,
      Complex.cpow_sub _ _ (Nat.cast_ne_zero.mpr hn), Complex.cpow_one]
    field_simp

/-- **The Dirichlet series of the totient function**: `∑ φ(c) c^{-w} = ζ(w - 1)/ζ(w)` for `Re w > 2`. -/
theorem LSeries_totient {w : ℂ} (hw : 2 < w.re) : LSeries totC w = riemannZeta (w - 1) / riemannZeta w := by
  have h1 : (1 : ℝ) < w.re := by linarith
  have hz : LSeriesSummable (fun n : ℕ => ((ArithmeticFunction.zeta n : ℕ) : ℂ)) w :=
    LSeriesSummable_zeta_iff.mpr h1
  have hc := LSeries_convolution' (summable_totC hw) hz
  rw [totC_convolution_zeta, LSeries_idC hw, LSeries_zeta_eq_riemannZeta h1] at hc
  rw [hc, mul_div_cancel_right₀ _ (riemannZeta_ne_zero_of_one_le_re h1.le)]

end Qschubert
