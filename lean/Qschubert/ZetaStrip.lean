import Qschubert.ZetaInv

/-!
# Bounds for `ζ` and `1/ζ` away from the line `Re w = 1`

Stage R of the plan for Proposition `ev:mod` (`lean/BLUEPRINT.md`). Polynomial bounds used for the scattering
coefficient in the strip `1/2 ≤ Re s ≤ 5/4`:

* `zeta_strip_le`: `|ζ(σ + it)| ≤ 7 + 2|t|` for `1/2 ≤ σ ≤ 5/2`, `|t| ≥ 2` (`GlobalBound` of `PrimeNumberTheoremAnd`);
* `zeta_inv_right`: `1/|ζ(σ + it)| ≤ K log|t|` for `1 ≤ σ ≤ 2`, `|t| > 3` (`zeta_inv_region` near the line and
  `ZetaInvBound2` to the right of it);
* `zeta_inv_far`: `1/|ζ(σ + it)| ≤ C (1 + |t|)` for `2 ≤ σ ≤ 5/2`, `|t| ≥ 1` (the inequality
  `ζ(σ)³ |ζ(σ + it)|⁴ |ζ(σ + 2it)| ≥ 1`, `ZetaLowerBound1`).
-/

namespace Qschubert

open Complex Set

/-- `|ζ(σ + it)| ≤ 7 + 2|t|` for `1/2 ≤ σ ≤ 5/2`, `|t| ≥ 2`. -/
theorem zeta_strip_le {σ t : ℝ} (h1 : 1 / 2 ≤ σ) (h2 : σ ≤ 5 / 2) (ht : 2 ≤ |t|) :
    ‖riemannZeta (σ + t * I)‖ ≤ 7 + 2 * |t| := by
  have hs : ‖((σ - 3 / 2 : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have h := GlobalBound hs (t := t) ht
  have e : ((σ - 3 / 2 : ℝ) : ℂ) + 3 / 2 + I * t = σ + t * I := by
    push_cast
    ring
  rwa [e] at h

/-- `1/|ζ(σ + it)| ≤ K log|t|` for `1 ≤ σ ≤ 2`, `|t| > 3`. -/
theorem zeta_inv_right :
    ∃ K : ℝ, 0 < K ∧ ∀ σ t : ℝ, 3 < |t| → 1 ≤ σ → σ ≤ 2 → 1 / ‖riemannZeta (σ + t * I)‖ ≤ K * Real.log |t| := by
  obtain ⟨A, hA0, hA1, K₁, hK₁, hreg⟩ := zeta_inv_region
  obtain ⟨C₂, hC₂, hinv⟩ := ZetaInvBound2
  refine ⟨max K₁ (C₂ * A ^ (-(3 : ℝ) / 4)), lt_max_of_lt_left hK₁, fun σ t ht hσ1 hσ2 => ?_⟩
  set L := Real.log |t| with hL
  have hL1 : 1 < L := one_lt_log_of_three_lt ht
  have hL0 : 0 < L := by linarith
  have hAL : 0 < A / L := div_pos hA0 hL0
  by_cases hc : σ ≤ 1 + A / L
  · refine (hreg σ t ht (by linarith) hc).trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hL0.le
  · rw [not_le] at hc
    have hmem : σ ∈ Ioc (1 : ℝ) 2 := ⟨by linarith, hσ2⟩
    have h1 := hinv hmem t ht
    have hmono : (σ - 1) ^ (-(3 : ℝ) / 4) ≤ (A / L) ^ (-(3 : ℝ) / 4) :=
      Real.rpow_le_rpow_of_nonpos hAL (by linarith) (by norm_num)
    have hpow : (A / L) ^ (-(3 : ℝ) / 4) * L ^ ((1 : ℝ) / 4) = A ^ (-(3 : ℝ) / 4) * L := by
      rw [Real.div_rpow hA0.le hL0.le, div_mul_eq_mul_div, mul_div_assoc]
      congr 1
      rw [← Real.rpow_sub hL0]
      norm_num
    have hL4 : 0 ≤ L ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hL0.le _
    calc 1 / ‖riemannZeta (σ + t * I)‖ ≤ C₂ * (σ - 1) ^ (-(3 : ℝ) / 4) * L ^ ((1 : ℝ) / 4) := h1
      _ ≤ C₂ * (A / L) ^ (-(3 : ℝ) / 4) * L ^ ((1 : ℝ) / 4) := by gcongr
      _ = C₂ * ((A / L) ^ (-(3 : ℝ) / 4) * L ^ ((1 : ℝ) / 4)) := by ring
      _ = C₂ * A ^ (-(3 : ℝ) / 4) * L := by rw [hpow]; ring
      _ ≤ max K₁ (C₂ * A ^ (-(3 : ℝ) / 4)) * L := mul_le_mul_of_nonneg_right (le_max_right _ _) hL0.le

/-- `1/|ζ(σ + it)| ≤ C (1 + |t|)` for `2 ≤ σ ≤ 5/2`, `|t| ≥ 1`. -/
theorem zeta_inv_far :
    ∃ C : ℝ, 0 < C ∧ ∀ σ t : ℝ, 2 ≤ σ → σ ≤ 5 / 2 → 1 ≤ |t| →
      1 / ‖riemannZeta (σ + t * I)‖ ≤ C * (1 + |t|) := by
  have hcont : ContinuousOn (fun σ : ℝ => riemannZeta (σ : ℂ)) (Icc 2 (5 / 2)) := by
    intro σ hσ
    have hne : (σ : ℂ) ≠ 1 := by
      intro h
      have h1 : σ = 1 := by exact_mod_cast h
      have := hσ.1
      linarith
    exact ((differentiableAt_riemannZeta hne).continuousAt.comp Complex.continuous_ofReal.continuousAt).continuousWithinAt
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  set M' : ℝ := max M 1 with hM'
  have hM'1 : 1 ≤ M' := le_max_right _ _
  refine ⟨7 * M', by positivity, fun σ t hσ1 hσ2 ht => ?_⟩
  have h341 := ZetaLowerBound1 (σ := σ) (t := t) (by linarith)
  have hz : riemannZeta (σ + t * I) ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by simp; linarith)
  have hzpos : 0 < ‖riemannZeta (σ + t * I)‖ := norm_pos_iff.mpr hz
  have ha : ‖riemannZeta (σ : ℂ)‖ ^ ((3 : ℝ) / 4) ≤ M' := by
    have h1 : ‖riemannZeta (σ : ℂ)‖ ≤ M' := (hM σ ⟨hσ1, hσ2⟩).trans (le_max_left _ _)
    calc ‖riemannZeta (σ : ℂ)‖ ^ ((3 : ℝ) / 4) ≤ M' ^ ((3 : ℝ) / 4) :=
          Real.rpow_le_rpow (norm_nonneg _) h1 (by norm_num)
      _ ≤ M' ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hM'1 (by norm_num)
      _ = M' := Real.rpow_one _
  have hb : ‖riemannZeta (σ + 2 * t * I)‖ ^ ((1 : ℝ) / 4) ≤ 7 * (1 + |t|) := by
    have h2 : ‖riemannZeta (σ + 2 * t * I)‖ ≤ 7 + 2 * |2 * t| := by
      have h3 := zeta_strip_le (σ := σ) (t := 2 * t) (by linarith) hσ2 (by rw [abs_mul, abs_two]; linarith)
      have e : ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * I) = σ + 2 * t * I := by push_cast; ring
      rwa [e] at h3
    have h4 : 7 + 2 * |2 * t| ≤ 7 * (1 + |t|) := by
      rw [abs_mul, abs_two]
      linarith
    have h5 : (1 : ℝ) ≤ 7 * (1 + |t|) := by linarith
    calc ‖riemannZeta (σ + 2 * t * I)‖ ^ ((1 : ℝ) / 4) ≤ (7 * (1 + |t|)) ^ ((1 : ℝ) / 4) :=
          Real.rpow_le_rpow (norm_nonneg _) (h2.trans h4) (by norm_num)
      _ ≤ (7 * (1 + |t|)) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h5 (by norm_num)
      _ = 7 * (1 + |t|) := Real.rpow_one _
  have ha0 : 0 ≤ ‖riemannZeta (σ : ℂ)‖ ^ ((3 : ℝ) / 4) := Real.rpow_nonneg (norm_nonneg _) _
  have hb0 : 0 ≤ ‖riemannZeta (σ + 2 * t * I)‖ ^ ((1 : ℝ) / 4) := Real.rpow_nonneg (norm_nonneg _) _
  have hprod : 1 ≤ M' * (7 * (1 + |t|)) * ‖riemannZeta (σ + t * I)‖ := by
    calc (1 : ℝ) ≤ ‖riemannZeta (σ : ℂ)‖ ^ ((3 : ℝ) / 4) * ‖riemannZeta (σ + 2 * t * I)‖ ^ ((1 : ℝ) / 4)
          * ‖riemannZeta (σ + t * I)‖ := h341
      _ ≤ M' * (7 * (1 + |t|)) * ‖riemannZeta (σ + t * I)‖ := by
          refine mul_le_mul_of_nonneg_right ?_ hzpos.le
          exact mul_le_mul ha hb hb0 (by linarith)
  rw [div_le_iff₀ hzpos]
  linarith

end Qschubert
