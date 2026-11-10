import Qschubert.EisSeries
import Qschubert.EisPointwise

/-!
# Auxiliary lemmas for the zero Fourier mode of the incomplete Eisenstein series

Stage E of the plan for Proposition `ev:mod` (`lean/BLUEPRINT.md`), part E3 (preparations).

* `hasSum_intervalIntegral_translates`: `∑_{n ∈ ℤ} ∫_0^1 f(x + n) dx = ∫_ℝ f` for integrable `f`;
* `sum_coprime_fin`: `∑_{d₀ < c, gcd(c, d₀) = 1} K = φ(c) K`;
* `norm_test_le_exp_log`: a test function on `(0, ∞)` satisfies `|g(t)| ≤ C t^{5/4}`;
* `integrable_test_hgt`: `x ↦ g(y / (c² (x² + y²)))` is integrable on `ℝ`.
-/

namespace Qschubert

open MeasureTheory Set Filter Topology
open scoped Real

/-- `∑_{n ∈ ℤ} ∫_0^1 f(x + n) dx = ∫_ℝ f`. -/
theorem hasSum_intervalIntegral_translates {f : ℝ → ℂ} (hf : Integrable f) :
    HasSum (fun n : ℤ => ∫ x in (0 : ℝ)..1, f (x + n)) (∫ x, f x) := by
  have h := hasSum_integral_iUnion (f := f) (μ := volume) (s := fun n : ℤ => Ioc (n : ℝ) (n + 1))
    (fun n => measurableSet_Ioc) (pairwise_disjoint_Ioc_intCast ℝ) (by rw [iUnion_Ioc_intCast]; exact hf.integrableOn)
  rw [iUnion_Ioc_intCast, setIntegral_univ] at h
  refine h.congr_fun fun n => ?_
  have e := intervalIntegral.integral_comp_add_right (a := (0 : ℝ)) (b := 1) f (n : ℝ)
  rw [e, zero_add, add_comm (1 : ℝ) (n : ℝ), intervalIntegral.integral_of_le (by linarith)]

/-- `∑_{d₀ < c, gcd(c, d₀) = 1} K = φ(c) K`. -/
lemma sum_coprime_fin (c : ℕ) (K : ℂ) :
    ∑ d₀ : Fin c, (if Nat.Coprime c d₀ then K else 0) = (Nat.totient c : ℂ) * K := by
  rw [Fin.sum_univ_eq_sum_range (fun d => if Nat.Coprime c d then K else 0) c, ← Finset.sum_filter,
    Finset.sum_const, Nat.totient_eq_card_coprime, nsmul_eq_mul]

/-- A test function on `(0, ∞)` is `O(t^{5/4})`. -/
lemma norm_test_le_exp_log {g : ℝ → ℂ} (hg : IsKTest g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → ‖g t‖ ≤ C * Real.exp (5 / 4 * Real.log t) := by
  obtain ⟨a, ha, hga⟩ := hg.exists_pos_le
  obtain ⟨B, hB⟩ := hg.continuous.bounded_above_of_compact_support hg.compact
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB a)
  refine ⟨B * Real.exp (-(5 / 4 * Real.log a)), by positivity, fun t ht => ?_⟩
  by_cases hne : g t = 0
  · rw [hne, norm_zero]
    positivity
  · have hat := hga t hne
    have hlog : Real.log a ≤ Real.log t := Real.log_le_log ha hat
    have h1 : (1 : ℝ) ≤ Real.exp (-(5 / 4 * Real.log a)) * Real.exp (5 / 4 * Real.log t) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by linarith)
    calc ‖g t‖ ≤ B := hB t
      _ = B * 1 := (mul_one B).symm
      _ ≤ B * (Real.exp (-(5 / 4 * Real.log a)) * Real.exp (5 / 4 * Real.log t)) :=
          mul_le_mul_of_nonneg_left h1 hB0
      _ = B * Real.exp (-(5 / 4 * Real.log a)) * Real.exp (5 / 4 * Real.log t) := by ring

/-- `x ↦ g(y / (c² (x² + y²)))` is integrable on `ℝ`. -/
lemma integrable_test_hgt {g : ℝ → ℂ} (hg : IsKTest g) {c y : ℝ} (hc : 0 < c) (hy : 0 < y) :
    Integrable fun x : ℝ => g (hgt c y x) := by
  obtain ⟨C, hC, hb⟩ := norm_test_le_exp_log hg
  refine ((integrable_exp_log_hgt hc hy).const_mul C).mono'
    (hg.continuous.comp (continuous_hgt hc hy)).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  exact hb _ (hgt_pos hc hy x)

end Qschubert
