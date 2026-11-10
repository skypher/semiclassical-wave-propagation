import PrimeNumberTheoremAnd.StrongPNT

/-!
# `ζ'/ζ = O(log|t|)` in the classical zero-free region

Stage M5b of the plan for Proposition `ev:mod` (`lean/BLUEPRINT.md`). The project `PrimeNumberTheoremAnd` proves
`|ζ'/ζ(σ + it)| ≤ C log²|t|` for `σ ≥ 1 - (E/3)/log|t|`. Its ingredients give the classical bound with the first power
of the logarithm (`logDerivZeta_log_bound`), by the argument of Montgomery and Vaughan, *Multiplicative Number Theory I*,
Theorem 6.7. With `δ = E/log|t|`, `z = σ + it`, `z₁ = 1 + δ + it` and `S(w) = ∑_ρ m_ρ/(w - ρ)`, the sum over the zeros
`ρ` with `|ρ - (3/2 + it)| ≤ 3/4`:

* `|ζ'/ζ(w) - S(w)| ≤ C₁ log|t|` for `w = z, z₁` (`SumBoundII`);
* `|ζ'/ζ(z₁)| ≤ 1/δ + C₀` (`triv_bound_zeta`), so `|S(z₁)| ≤ B := 1/δ + C₀ + C₁ log|t|`;
* `Re (1/(z₁ - ρ)) ≥ δ/|z₁ - ρ|²` because `Re ρ < 1`, so `∑_ρ m_ρ δ/|z₁ - ρ|² ≤ Re S(z₁) ≤ B`;
* `|z - ρ| ≥ δ/6` (`GapSize`) and `|z₁ - z| ≤ 4δ/3`, so `|z₁ - ρ| ≤ 9|z - ρ|` and
  `|S(z) - S(z₁)| ≤ 12 ∑_ρ m_ρ δ/|z₁ - ρ|² ≤ 12 B`.
-/

namespace Qschubert

open Complex Set

/-- The real part of `m/w` for a natural number `m`. -/
lemma re_natCast_div (m : ℕ) (w : ℂ) : ((m : ℂ) / w).re = m * (w.re / ‖w‖ ^ 2) := by
  rw [div_eq_mul_inv, ← Complex.ofReal_natCast, Complex.re_ofReal_mul, Complex.inv_re, Complex.normSq_eq_norm_sq]

/-- **`ζ'/ζ = O(log|t|)` in the classical zero-free region**: `|ζ'/ζ(σ + it)| ≤ C log|t|` for `|t| ≥ 3` and
`σ ≥ 1 - (E/3)/log|t|`, where `E` is the constant of the zero-free region of `PrimeNumberTheoremAnd`. -/
theorem logDerivZeta_log_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 3 ≤ |t| → ∀ σ : ℝ, 1 - (E / 3) / Real.log |t| ≤ σ →
      ‖deriv riemannZeta (σ + t * I) / riemannZeta (σ + t * I)‖ ≤ C * Real.log |t| := by
  obtain ⟨C₁, hC₁, hsum⟩ := SumBoundII
  obtain ⟨C₀, hC₀, htriv⟩ := triv_bound_zeta
  have hE := EinIoo
  have hE0 : 0 < E := hE.1
  refine ⟨14 * C₁ + 13 / E + 13 * C₀ + 1, by positivity, fun t ht σ hσ => ?_⟩
  set L := Real.log |t| with hL
  have hL1 : 1 ≤ L := by
    rw [hL, Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_three]
  have hL0 : 0 < L := by linarith
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, DeltaT t = δ := ⟨_, rfl⟩
  have hδeq : δ = E / L := by rw [← hδdef, DeltaT]
  have hδ0 : 0 < δ := by rw [hδeq]; exact div_pos hE0 hL0
  have hδ9 : δ < 1 / 9 := by rw [← hδdef]; exact DeltaRange t (by linarith)
  have hδinv : δ⁻¹ = L / E := by rw [hδeq, inv_div]
  have hσδ : 1 - δ / 3 ≤ σ := by
    have : (E / 3) / L = δ / 3 := by rw [hδeq]; ring
    linarith
  have hCL : C₀ ≤ C₀ * L := le_mul_of_one_le_right hC₀ hL1
  have hLE : 0 ≤ L / E := by positivity
  -- to the right of `1 + δ`
  have hright : ∀ x : ℝ, 1 + δ ≤ x →
      ‖deriv riemannZeta (x + t * I) / riemannZeta (x + t * I)‖ ≤ L / E + C₀ := by
    intro x hx
    have h := htriv x t (by linarith)
    rw [neg_div, norm_neg] at h
    refine h.trans ?_
    have : (x - 1)⁻¹ ≤ δ⁻¹ := inv_anti₀ hδ0 (by linarith)
    rw [hδinv] at this
    linarith
  by_cases hcase : 1 + δ ≤ σ
  · refine (hright σ hcase).trans ?_
    have e : (14 * C₁ + 13 / E + 13 * C₀ + 1) * L = 14 * (C₁ * L) + 13 * (L / E) + 13 * (C₀ * L) + L := by ring
    rw [e]
    have : 0 ≤ C₁ * L := by positivity
    linarith
  · rw [not_le] at hcase
    have fin := ZeroWindowFinite (t := t) (by linarith : |t| ≥ 2)
    set z : ℂ := σ + t * I with hz
    set z₁ : ℂ := ((1 + δ : ℝ) : ℂ) + t * I with hz₁
    have zIm : t = z.im := by simp [hz]
    have z₁Im : t = z₁.im := by simp [hz₁]
    have zRe' : z.re = σ := by simp [hz]
    have z₁Re' : z₁.re = 1 + δ := by simp [hz₁]
    have zRe : z.re ∈ Icc (1 - DeltaT t / 3) (3 / 2) := by
      rw [zRe', hδdef]
      exact ⟨hσδ, by linarith⟩
    have z₁Re : z₁.re ∈ Icc (1 - DeltaT t / 3) (3 / 2) := by
      rw [z₁Re', hδdef]
      exact ⟨by linarith, by linarith⟩
    set S : ℂ → ℂ := fun w => ∑ ρ ∈ fin.toFinset, (analyticOrderNatAt riemannZeta ρ : ℂ) / (w - ρ) with hS
    have h1 : ‖deriv riemannZeta z / riemannZeta z - S z‖ ≤ C₁ * L := hsum t (by linarith) z zIm zRe fin
    have h2 : ‖deriv riemannZeta z₁ / riemannZeta z₁ - S z₁‖ ≤ C₁ * L := hsum t (by linarith) z₁ z₁Im z₁Re fin
    have h3 : ‖deriv riemannZeta z₁ / riemannZeta z₁‖ ≤ L / E + C₀ := hright (1 + δ) le_rfl
    set B := L / E + C₀ + C₁ * L with hB
    have hS1 : ‖S z₁‖ ≤ B := by
      have e : S z₁ = deriv riemannZeta z₁ / riemannZeta z₁ - (deriv riemannZeta z₁ / riemannZeta z₁ - S z₁) := by
        ring
      calc ‖S z₁‖ = ‖deriv riemannZeta z₁ / riemannZeta z₁ - (deriv riemannZeta z₁ / riemannZeta z₁ - S z₁)‖ := by
            rw [← e]
        _ ≤ ‖deriv riemannZeta z₁ / riemannZeta z₁‖ + ‖deriv riemannZeta z₁ / riemannZeta z₁ - S z₁‖ :=
            norm_sub_le _ _
        _ ≤ B := by rw [hB]; linarith
    -- the zeros in the window
    have hρ : ∀ ρ ∈ fin.toFinset, ρ.re < 1 ∧ δ / 6 ≤ ‖z - ρ‖ := by
      intro ρ hρm
      rw [Set.Finite.mem_toFinset] at hρm
      refine ⟨?_, ?_⟩
      · by_contra h
        exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hρm.1
      · have := GapSize t ht z zRe ρ hρm
        rwa [hδdef] at this
    have hz₁ρre : ∀ ρ ∈ fin.toFinset, δ ≤ (z₁ - ρ).re := by
      intro ρ hρm
      rw [Complex.sub_re, z₁Re']
      linarith [(hρ ρ hρm).1]
    -- `∑ m δ/|z₁ - ρ|² ≤ Re S(z₁) ≤ B`
    have hkey : ∑ ρ ∈ fin.toFinset, (analyticOrderNatAt riemannZeta ρ : ℝ) * (δ / ‖z₁ - ρ‖ ^ 2) ≤ B := by
      calc ∑ ρ ∈ fin.toFinset, (analyticOrderNatAt riemannZeta ρ : ℝ) * (δ / ‖z₁ - ρ‖ ^ 2)
          ≤ ∑ ρ ∈ fin.toFinset, ((analyticOrderNatAt riemannZeta ρ : ℂ) / (z₁ - ρ)).re := by
            refine Finset.sum_le_sum fun ρ hρm => ?_
            rw [re_natCast_div]
            have := hz₁ρre ρ hρm
            gcongr
        _ = (S z₁).re := by rw [hS, Complex.re_sum]
        _ ≤ ‖S z₁‖ := Complex.re_le_norm _
        _ ≤ B := hS1
    -- `|S(z) - S(z₁)| ≤ 12 B`
    have hdiff : ‖S z - S z₁‖ ≤ 12 * B := by
      have e : S z - S z₁ = ∑ ρ ∈ fin.toFinset, ((analyticOrderNatAt riemannZeta ρ : ℂ) / (z - ρ)
          - (analyticOrderNatAt riemannZeta ρ : ℂ) / (z₁ - ρ)) := by
        rw [hS, Finset.sum_sub_distrib]
      rw [e]
      calc ‖∑ ρ ∈ fin.toFinset, ((analyticOrderNatAt riemannZeta ρ : ℂ) / (z - ρ)
              - (analyticOrderNatAt riemannZeta ρ : ℂ) / (z₁ - ρ))‖
          ≤ ∑ ρ ∈ fin.toFinset, 12 * ((analyticOrderNatAt riemannZeta ρ : ℝ) * (δ / ‖z₁ - ρ‖ ^ 2)) := by
            refine norm_sum_le_of_le _ fun ρ hρm => ?_
            obtain ⟨-, hgap⟩ := hρ ρ hρm
            have hzρ : 0 < ‖z - ρ‖ := lt_of_lt_of_le (by positivity) hgap
            have hz₁ρ : 0 < ‖z₁ - ρ‖ := lt_of_lt_of_le hδ0 ((hz₁ρre ρ hρm).trans (Complex.re_le_norm _))
            have hne : z - ρ ≠ 0 := norm_pos_iff.mp hzρ
            have hne₁ : z₁ - ρ ≠ 0 := norm_pos_iff.mp hz₁ρ
            have hzz : ‖z₁ - z‖ ≤ 4 / 3 * δ := by
              have : z₁ - z = ((1 + δ - σ : ℝ) : ℂ) := by
                rw [hz, hz₁]
                push_cast
                ring
              rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
              linarith
            have h9 : ‖z₁ - ρ‖ ≤ 9 * ‖z - ρ‖ := by
              have e9 : z₁ - ρ = (z₁ - z) + (z - ρ) := by ring
              calc ‖z₁ - ρ‖ = ‖(z₁ - z) + (z - ρ)‖ := by rw [← e9]
                _ ≤ ‖z₁ - z‖ + ‖z - ρ‖ := norm_add_le _ _
                _ ≤ 9 * ‖z - ρ‖ := by linarith
            have ed : (analyticOrderNatAt riemannZeta ρ : ℂ) / (z - ρ) - (analyticOrderNatAt riemannZeta ρ : ℂ) / (z₁ - ρ)
                = (analyticOrderNatAt riemannZeta ρ : ℂ) * (z₁ - z) / ((z - ρ) * (z₁ - ρ)) := by
              field_simp
              ring
            rw [ed, norm_div, norm_mul, norm_mul, Complex.norm_natCast, div_le_iff₀ (by positivity)]
            have e12 : 12 * ((analyticOrderNatAt riemannZeta ρ : ℝ) * (δ / ‖z₁ - ρ‖ ^ 2)) * (‖z - ρ‖ * ‖z₁ - ρ‖)
                = (analyticOrderNatAt riemannZeta ρ : ℝ) * (12 * δ * ‖z - ρ‖ / ‖z₁ - ρ‖) := by
              field_simp
            rw [e12]
            gcongr
            rw [le_div_iff₀ hz₁ρ]
            calc ‖z₁ - z‖ * ‖z₁ - ρ‖ ≤ (4 / 3 * δ) * (9 * ‖z - ρ‖) := by gcongr
              _ = 12 * δ * ‖z - ρ‖ := by ring
        _ = 12 * ∑ ρ ∈ fin.toFinset, (analyticOrderNatAt riemannZeta ρ : ℝ) * (δ / ‖z₁ - ρ‖ ^ 2) := by
            rw [Finset.mul_sum]
        _ ≤ 12 * B := by gcongr
    have e3 : deriv riemannZeta z / riemannZeta z
        = (deriv riemannZeta z / riemannZeta z - S z) + (S z - S z₁) + S z₁ := by ring
    calc ‖deriv riemannZeta z / riemannZeta z‖
        = ‖(deriv riemannZeta z / riemannZeta z - S z) + (S z - S z₁) + S z₁‖ := by rw [← e3]
      _ ≤ ‖deriv riemannZeta z / riemannZeta z - S z‖ + ‖S z - S z₁‖ + ‖S z₁‖ := norm_add₃_le
      _ ≤ C₁ * L + 12 * B + B := by linarith
      _ ≤ (14 * C₁ + 13 / E + 13 * C₀ + 1) * L := by
          have e : (14 * C₁ + 13 / E + 13 * C₀ + 1) * L = 14 * (C₁ * L) + 13 * (L / E) + 13 * (C₀ * L) + L := by ring
          rw [e, hB]
          linarith

end Qschubert
