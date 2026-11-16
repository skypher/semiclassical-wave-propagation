import Qschubert.KLPcEmA
import Qschubert.KLPcSchur

/-!
# Lemmas A.2(iii) and 5.8 in the form of the manuscript

The manuscript states Lemma `os:prof`(iii) with an absolute constant `c_H` whose value it fixes only in the proof, and
Lemma `os:transfer` for a linear map `T` and the weight `X_0` (the exponent `β = 1` of `transfer`). The theorems below
state them in that form. The witness for `c_H` is `cH = 1 + 4/e`; `transfer_paper` is `transfer` at `β = 1`, applied
to the underlying additive map of a `ℂ`-linear map.
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set
open scoped ENNReal UpperHalfPlane

local notation "L2H'" => Lp ℂ 2 (volume : Measure UpperHalfPlane)

/-- Lemma `os:prof`(iii) in the form of the manuscript: the tail bound holds with an absolute constant `c_H`. -/
theorem prof_iii_paper : ∃ c : ℝ, 0 < c ∧ ∀ {m κ s : ℝ}, 2 * κ ^ 2 < m ^ 2 → 0 < s →
    Integrable (fun r => |hSM m s r| * Real.exp (κ * |r|)) ∧
      ∫ r, |hSM m s r| * Real.exp (κ * |r|) ≤ 2 * c / s :=
  ⟨cH, cH_pos, fun h hs => hSM_expmass h hs⟩

/-- Lemma `os:transfer` in the form of the manuscript: a bounded linear map `T` that satisfies the shell bound (b)
at the weight `X_0` is bounded at every weight comparable to `e^{n/2} (1+n)^c` on the shells, with the factor
`M₀^{1/4} M₁^{3/4}`. -/
theorem transfer_paper {c D : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hD : 0 < D) :
    ∃ K : ℝ, 0 < K ∧ ∀ (om : UpperHalfPlane → ℝ), (∀ z, 0 ≤ om z) →
      (∀ (n : ℕ) (z : UpperHalfPlane), z ∈ shell n → Real.exp ((n : ℝ) / 2) * (1 + (n : ℝ)) ^ c ≤ om z) →
      (∀ (l : ℕ) (z : UpperHalfPlane), z ∈ shell l → om z ≤ D * Real.exp ((l : ℝ) / 2) * (1 + (l : ℝ)) ^ c) →
      ∀ (T : L2H' →ₗ[ℂ] L2H'), ∀ {M₀ M₁ : ℝ}, 0 ≤ M₀ → M₀ ≤ M₁ → (∀ u, ‖T u‖ ≤ M₀ * ‖u‖) →
      (∀ (l n : ℕ) (u : L2H'), cutN n u = u →
        Real.exp (l : ℝ) * ‖cutN l (T u)‖ ≤ M₁ * Real.exp ((n : ℝ) + 1) * ‖u‖) →
      ∀ f : L2H', ∫⁻ z, ENNReal.ofReal (om z ^ 2 * ‖T f z‖ ^ 2)
        ≤ ENNReal.ofReal ((K * (M₀ ^ (1 / 4 : ℝ) * M₁ ^ (3 / 4 : ℝ))) ^ 2)
          * ∫⁻ z, ENNReal.ofReal (om z ^ 2 * ‖f z‖ ^ 2) := by
  obtain ⟨K, hK, h⟩ := transfer (β := 1) (by norm_num) hc0 hc1 hD
  refine ⟨K, hK, fun om hom hlo hhi T M₀ M₁ h0 h01 hbd hw f => ?_⟩
  have hw' : ∀ (l n : ℕ) (u : L2H'), cutN n u = u →
      Real.exp (1 * (l : ℝ)) * ‖cutN l (T u)‖ ≤ M₁ * Real.exp (1 * ((n : ℝ) + 1)) * ‖u‖ := by
    intro l n u hu
    simpa only [one_mul] using hw l n u hu
  have key := h om hom hlo hhi (⇑T) (fun u v => T.map_add u v) h0 h01 hbd hw' f
  have e1 : (1 : ℝ) - (1 + 1 / (2 * 1)) / 2 = 1 / 4 := by norm_num
  have e2 : ((1 : ℝ) + 1 / (2 * 1)) / 2 = 3 / 4 := by norm_num
  rw [e1, e2] at key
  exact key

end Qschubert
