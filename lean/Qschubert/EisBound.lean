import Qschubert.EisZero

/-!
# The incomplete Eisenstein series of a test function is bounded

Stage E of the plan for Proposition `ev:mod` (`lean/BLUEPRINT.md`). For a test function `g` on `(0, ∞)`,
`E_g = perio modGroup (stripFn g)` is bounded on `M = PSL(2, ℤ)\ℍ` (`norm_perio_stripFn_le`).

Proof: on a half-strip `|Re z| ≤ 1`, `Im z ≥ y₀` the terms satisfy `|g(Im σ(p) z)| ≤ D ‖p‖^{-5/2}` uniformly: the row
`(0, 1)` by the bound for `g`, and the rows with `c ≥ 1` by `|g(t)| ≤ C t^{5/2}`, `|cz + d| ≥ Im z` and Mathlib's bound
for Eisenstein sums on vertical strips. Every point of `M` has a representative in the standard fundamental domain.
-/

namespace Qschubert

open MeasureTheory Set Filter Topology Matrix UpperHalfPlane ModularGroup
open scoped Real MatrixGroups Modular

/-- A test function on `(0, ∞)` is `O(t^N)` for every `N ≥ 0`. -/
lemma norm_test_le_exp_log' {g : ℝ → ℂ} (hg : IsKTest g) {N : ℝ} (hN : 0 ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → ‖g t‖ ≤ C * Real.exp (N * Real.log t) := by
  obtain ⟨a, ha, hga⟩ := hg.exists_pos_le
  obtain ⟨B, hB⟩ := hg.continuous.bounded_above_of_compact_support hg.compact
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB a)
  refine ⟨B * Real.exp (-(N * Real.log a)), by positivity, fun t ht => ?_⟩
  by_cases hne : g t = 0
  · rw [hne, norm_zero]
    positivity
  · have hat := hga t hne
    have hlog : Real.log a ≤ Real.log t := Real.log_le_log ha hat
    have h1 : (1 : ℝ) ≤ Real.exp (-(N * Real.log a)) * Real.exp (N * Real.log t) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by nlinarith)
    calc ‖g t‖ ≤ B := hB t
      _ = B * 1 := (mul_one B).symm
      _ ≤ B * (Real.exp (-(N * Real.log a)) * Real.exp (N * Real.log t)) := mul_le_mul_of_nonneg_left h1 hB0
      _ = B * Real.exp (-(N * Real.log a)) * Real.exp (N * Real.log t) := by ring

/-- The terms of `E_g` on a half-strip, uniformly. -/
lemma norm_test_npSec_le {g : ℝ → ℂ} (hg : IsKTest g) {y₀ : ℝ} (hy₀ : 0 < y₀) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (p : NPair) (z : ℍ), |z.re| ≤ 1 → y₀ ≤ z.im →
      ‖g ((npSec p • z).im)‖ ≤ D * ‖p.1‖ ^ (-(5 / 2 : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := norm_test_le_exp_log' hg (N := 5 / 2) (by norm_num)
  obtain ⟨B, hB⟩ := hg.continuous.bounded_above_of_compact_support hg.compact
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 1)
  set r₀ : ℝ := EisensteinSeries.r ⟨⟨1, y₀⟩, hy₀⟩ with hr₀
  have hr₀pos : 0 < r₀ := EisensteinSeries.r_pos _
  refine ⟨max B (C * r₀ ^ (-(5 / 2 : ℝ))), le_max_of_le_left hB0, fun p z hx hy => ?_⟩
  have hstrip : z ∈ verticalStrip 1 y₀ := ⟨hx, hy⟩
  have hsb := EisensteinSeries.summand_bound_of_mem_verticalStrip (k := 5 / 2) (by norm_num) p.1 hy₀ hstrip
  have hpn : 0 ≤ ‖p.1‖ ^ (-(5 / 2 : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
  rcases p.2.2 with hc | ⟨hc, hd⟩
  · -- `c ≥ 1`
    set N : ℝ := ‖((p.1 0 : ℤ) : ℂ) * (z : ℂ) + (p.1 1 : ℤ)‖ with hN
    have hNy : z.im ≤ N := by
      have h1 := Complex.abs_im_le_norm (((p.1 0 : ℤ) : ℂ) * (z : ℂ) + (p.1 1 : ℤ))
      have h2 : (((p.1 0 : ℤ) : ℂ) * (z : ℂ) + (p.1 1 : ℤ)).im = (p.1 0 : ℝ) * z.im := by
        simp [UpperHalfPlane.coe_im]
      rw [h2, abs_mul, abs_of_pos z.im_pos] at h1
      have hc1 : (1 : ℝ) ≤ |(p.1 0 : ℝ)| := by
        have : (1 : ℤ) ≤ p.1 0 := hc
        have h3 : (1 : ℝ) ≤ (p.1 0 : ℝ) := by exact_mod_cast this
        exact h3.trans (le_abs_self _)
      calc z.im = 1 * z.im := (one_mul _).symm
        _ ≤ |(p.1 0 : ℝ)| * z.im := mul_le_mul_of_nonneg_right hc1 z.im_pos.le
        _ ≤ N := h1
    have hNpos : 0 < N := lt_of_lt_of_le z.im_pos hNy
    have him : (npSec p • z).im = z.im / N ^ 2 := by
      rw [im_npSec_smul, hN, Complex.normSq_eq_norm_sq]
    have hpos : 0 < (npSec p • z).im := (npSec p • z).im_pos
    have hexp : Real.exp (5 / 2 * Real.log ((npSec p • z).im)) ≤ N ^ (-(5 / 2 : ℝ)) := by
      rw [him, Real.log_div z.im_pos.ne' (by positivity), Real.log_pow, Real.rpow_def_of_pos hNpos]
      refine Real.exp_le_exp.2 ?_
      have hl : Real.log z.im ≤ Real.log N := Real.log_le_log z.im_pos hNy
      push_cast
      nlinarith
    calc ‖g ((npSec p • z).im)‖ ≤ C * Real.exp (5 / 2 * Real.log ((npSec p • z).im)) := hb _ hpos
      _ ≤ C * N ^ (-(5 / 2 : ℝ)) := mul_le_mul_of_nonneg_left hexp hC
      _ ≤ C * (r₀ ^ (-(5 / 2 : ℝ)) * ‖p.1‖ ^ (-(5 / 2 : ℝ))) := mul_le_mul_of_nonneg_left hsb hC
      _ = C * r₀ ^ (-(5 / 2 : ℝ)) * ‖p.1‖ ^ (-(5 / 2 : ℝ)) := by ring
      _ ≤ max B (C * r₀ ^ (-(5 / 2 : ℝ))) * ‖p.1‖ ^ (-(5 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hpn
  · -- the row `(0, 1)`
    have hnorm : ‖p.1‖ = 1 := by
      rw [EisensteinSeries.norm_eq_max_natAbs, hc, hd]
      simp
    rw [hnorm, Real.one_rpow, mul_one]
    exact (hB _).trans (le_max_left _ _)

/-- `E_g` is bounded on half-strips. -/
lemma norm_perio_stripFn_strip_le {g : ℝ → ℂ} (hg : IsKTest g) {y₀ : ℝ} (hy₀ : 0 < y₀) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℍ, |z.re| ≤ 1 → y₀ ≤ z.im →
      ‖perio modGroup (stripFn g) (surfMk modGroup z)‖ ≤ M := by
  obtain ⟨D, hD, hdom⟩ := norm_test_npSec_le hg hy₀
  have hsumM : Summable fun p : NPair => D * ‖p.1‖ ^ (-(5 / 2 : ℝ)) := summable_npair_norm.mul_left D
  refine ⟨∑' p : NPair, D * ‖p.1‖ ^ (-(5 / 2 : ℝ)), tsum_nonneg fun p => mul_nonneg hD
    (Real.rpow_nonneg (norm_nonneg _) _), fun z hx hy => ?_⟩
  rw [perio_stripFn hg]
  have hs : Summable fun p : NPair => ‖g ((npSec p • z).im)‖ :=
    Summable.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => hdom p z hx hy) hsumM
  exact (norm_tsum_le_tsum_norm hs).trans (hs.tsum_le_tsum (fun p => hdom p z hx hy) hsumM)

/-- **`E_g` is bounded on `M`.** -/
theorem norm_perio_stripFn_le {g : ℝ → ℂ} (hg : IsKTest g) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : Surf modGroup, ‖perio modGroup (stripFn g) x‖ ≤ M := by
  obtain ⟨M, hM, hb⟩ := norm_perio_stripFn_strip_le hg (y₀ := 1 / 2) (by norm_num)
  refine ⟨M, hM, fun x => ?_⟩
  induction x using Quotient.inductionOn with | _ z => ?_
  obtain ⟨A, hA⟩ := ModularGroup.exists_smul_mem_fd z
  have hmk : surfMk modGroup (A • z) = surfMk modGroup z := by
    rw [← modQ_smul]
    exact surfMk_smul modGroup (modQ A) z
  have hfd : 1 ≤ Complex.normSq (A • z : ℍ) ∧ |(A • z).re| ≤ 1 / 2 := hA
  have hre : |(A • z).re| ≤ 1 := hfd.2.trans (by norm_num)
  have him : (1 / 2 : ℝ) ≤ (A • z).im := by
    have h1 := hfd.1
    rw [Complex.normSq_apply] at h1
    have h2 : (A • z).re * (A • z).re ≤ 1 / 4 := by
      have := abs_le.1 hfd.2
      nlinarith [this.1, this.2]
    have h3 : (3 / 4 : ℝ) ≤ (A • z).im * (A • z).im := by
      have e1 : ((A • z : ℍ) : ℂ).re = (A • z).re := rfl
      have e2 : ((A • z : ℍ) : ℂ).im = (A • z).im := rfl
      rw [e1, e2] at h1
      linarith
    nlinarith [(A • z).im_pos]
  have := hb (A • z) hre him
  rwa [hmk] at this

end Qschubert
