import Qschubert.KLA0c
import Qschubert.JEps

/-!
# `prop:a0` for the mollifier of the paper

`J_ε = j_ε(Λ)` (`MollProfile.cutoffEps`) satisfies the hypotheses of `prop_a0` with `B = 32/ε` and `L₀ = 4/ε`, which gives the
time window `|s₁ - s₀| ≤ c ((α - α')/α) (ε/ħ)` of the paper, with `c` depending only on `τ₀`.
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set
open scoped ENNReal

local notation "L2H'" => Lp ℂ 2 (volume : Measure UpperHalfPlane)

namespace MollProfile

variable (P : MollProfile) {ε : ℝ} (hε : 0 < ε)
include hε

/-- `J_ε` has the regularity used in `prop_a0`. -/
theorem cutK : CutK (P.cutoffEps hε) where
  cont := (P.continuous_jEps hε).comp continuous_abs.sqrt
  dec := by
    refine ⟨1, Real.exp (4 / ε) + 4 / ε * Real.exp 2, one_pos, fun s => ?_⟩
    set l := √|s| with hl
    have hl0 : 0 ≤ l := Real.sqrt_nonneg _
    show Real.exp (1 * l) * |P.jEps ε l| ≤ _
    rw [one_mul, abs_of_nonneg (P.jEps_nonneg _ _)]
    have hA : 0 ≤ 4 / ε * Real.exp 2 := by positivity
    have hB := Real.exp_pos (4 / ε)
    by_cases hbig : 4 / ε ≤ |l|
    · have hj := P.jEps_le_exp hε hbig
      have hq : l + -l ^ 2 / 8 ≤ 2 := by nlinarith [sq_nonneg (l - 4)]
      have hE : Real.exp l * Real.exp (-l ^ 2 / 8) ≤ Real.exp 2 := by
        rw [← Real.exp_add]; exact Real.exp_le_exp.2 hq
      calc Real.exp l * P.jEps ε l ≤ Real.exp l * (4 / ε * Real.exp (-l ^ 2 / 8)) :=
            mul_le_mul_of_nonneg_left hj (Real.exp_pos _).le
        _ = 4 / ε * (Real.exp l * Real.exp (-l ^ 2 / 8)) := by ring
        _ ≤ 4 / ε * Real.exp 2 := mul_le_mul_of_nonneg_left hE (by positivity)
        _ ≤ _ := by linarith
    · have hlt : l < 4 / ε := by rw [abs_of_nonneg hl0] at hbig; exact not_le.1 hbig
      have hj1 := P.jEps_le_one ε l
      have hj0 := P.jEps_nonneg ε l
      have hE : Real.exp l ≤ Real.exp (4 / ε) := Real.exp_le_exp.2 hlt.le
      calc Real.exp l * P.jEps ε l ≤ Real.exp (4 / ε) * 1 := mul_le_mul hE hj1 hj0 hB.le
        _ ≤ _ := by linarith

/-- The frequency bound `Λ² j² ≤ (32/ε) min(Λ, L)`, for `L ≥ 4/ε`. -/
theorem freq_bound {L : ℝ} (hL : 4 / ε ≤ L) (s : ℝ) :
    |s| * (P.cutoffEps hε).r s ^ 2 ≤ 32 / ε * ellS L s := by
  set l := √|s| with hl
  have hl0 : 0 ≤ l := Real.sqrt_nonneg _
  have hsl : |s| = l ^ 2 := (Real.sq_sqrt (abs_nonneg s)).symm
  show |s| * P.jEps ε l ^ 2 ≤ _
  rw [hsl]
  have hj1 := P.jEps_le_one ε l
  have hj0 := P.jEps_nonneg ε l
  have h4 : 0 < 4 / ε := by positivity
  have hB : 0 < 32 / ε := by positivity
  by_cases hbig : 4 / ε ≤ |l|
  · rw [abs_of_nonneg hl0] at hbig
    have hj := P.jEps_le_exp hε (by rwa [abs_of_nonneg hl0])
    have hell : 4 / ε ≤ ellS L s := le_min hbig hL
    have h8 := one_add_sq_mul_exp_le l
    have hE1 : l ^ 2 * Real.exp (-l ^ 2 / 8) ≤ 8 := by
      have := Real.exp_pos (-l ^ 2 / 8); nlinarith
    have hE2 : Real.exp (-l ^ 2 / 8) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg l])
    have hEp := Real.exp_pos (-l ^ 2 / 8)
    calc l ^ 2 * P.jEps ε l ^ 2 ≤ l ^ 2 * (4 / ε * Real.exp (-l ^ 2 / 8)) ^ 2 := by gcongr
      _ = (4 / ε) ^ 2 * ((l ^ 2 * Real.exp (-l ^ 2 / 8)) * Real.exp (-l ^ 2 / 8)) := by ring
      _ ≤ (4 / ε) ^ 2 * (8 * 1) := by gcongr
      _ = 32 / ε * (4 / ε) := by field_simp; ring
      _ ≤ 32 / ε * ellS L s := mul_le_mul_of_nonneg_left hell hB.le
  · have hlt : l ≤ 4 / ε := by rw [abs_of_nonneg hl0] at hbig; exact (not_le.1 hbig).le
    have hell : ellS L s = l := min_eq_left (hlt.trans hL)
    rw [hell]
    have hjj : P.jEps ε l ^ 2 ≤ 1 := pow_le_one₀ hj0 hj1
    calc l ^ 2 * P.jEps ε l ^ 2 ≤ l ^ 2 * 1 := by gcongr
      _ = l * l := by ring
      _ ≤ l * (4 / ε) := mul_le_mul_of_nonneg_left hlt hl0
      _ ≤ l * (32 / ε) := by
          refine mul_le_mul_of_nonneg_left ?_ hl0
          exact div_le_div_of_nonneg_right (by norm_num) hε.le
      _ = 32 / ε * l := by ring

end MollProfile

/-- The constant of the time window. -/
noncomputable def cA0 (τ₀ : ℝ) : ℝ := 1 / (32 * (∫ x, gK τ₀ x) * (∫ x, gQ τ₀ x) + 1)

lemma cA0_pos (τ₀ : ℝ) : 0 < cA0 τ₀ := by
  have hA1 : 0 ≤ ∫ x, gK τ₀ x := integral_nonneg fun x => gK_nonneg τ₀ x
  have hA2 : 0 ≤ ∫ x, gQ τ₀ x := integral_nonneg fun x => gQ_nonneg τ₀ x
  unfold cA0; positivity

/-- **Proposition A0** (`prop:a0`) for `V_ε`: for `0 ≤ α' ≤ α ≤ τ₀`, `|s₁ - s₀| ≤ c ((α - α')/α) (ε/ħ)`,
`‖e^{α'Λ} V_ε(s₁)V_ε(s₀)* a‖ ≤ ‖e^{αΛ} a‖`. -/
theorem prop_a0_eps (P : MollProfile) {τ₀ : ℝ} (hτ₀ : τ₀ < Real.pi / 2) {ε ħ α α' s₀ s₁ : ℝ} (hε : 0 < ε) (hħ : 0 < ħ)
    (hs₀ : 0 ≤ s₀) (hs₁ : 0 ≤ s₁) (hα' : 0 ≤ α') (hαα : α' ≤ α) (hα0 : 0 < α) (hα : α ≤ τ₀)
    (hwin : |s₁ - s₀| ≤ cA0 τ₀ * ((α - α') / α) * (ε / ħ)) (a : L2H') (had : a ∈ (expLambda α).domain) :
    ∃ hd : (P.cutoffEps hε).flowEps ħ s₁ (ContinuousLinearMap.adjoint ((P.cutoffEps hε).flowEps ħ s₀) a)
        ∈ (expLambda α').domain,
      ‖expLambda α' ⟨_, hd⟩‖ ≤ ‖expLambda α ⟨a, had⟩‖ := by
  have hB : 0 ≤ 32 / ε := by positivity
  refine prop_a0 (P.cutK hε) hτ₀ hB (L₀ := 4 / ε) (fun L hL s => P.freq_bound hε hL s) ħ hs₀ hs₁ hα0.le hα ?_ a had
  set A₁ := ∫ x, gK τ₀ x
  set A₂ := ∫ x, gQ τ₀ x
  have hA1 : 0 ≤ A₁ := integral_nonneg fun x => gK_nonneg τ₀ x
  have hA2 : 0 ≤ A₂ := integral_nonneg fun x => gQ_nonneg τ₀ x
  set T := |s₁ - s₀|
  have hT : 0 ≤ T := abs_nonneg _
  set r := (α - α') / α with hr
  have hr0 : 0 ≤ r := div_nonneg (by linarith) hα0.le
  have hρT : rhoA0 τ₀ (32 / ε) ħ * T ≤ r := by
    unfold rhoA0
    rw [abs_of_pos hħ]
    have hD : 0 < 32 * A₁ * A₂ + 1 := by positivity
    have hcl : cA0 τ₀ * (32 * A₁ * A₂) ≤ 1 := by
      show 1 / (32 * A₁ * A₂ + 1) * (32 * A₁ * A₂) ≤ 1
      rw [div_mul_eq_mul_div, one_mul, div_le_one hD]; linarith
    calc ħ * A₁ * A₂ * (32 / ε) * T
        ≤ ħ * A₁ * A₂ * (32 / ε) * (cA0 τ₀ * r * (ε / ħ)) := by gcongr
      _ = cA0 τ₀ * (32 * A₁ * A₂) * r := by field_simp
      _ ≤ 1 * r := mul_le_mul_of_nonneg_right hcl hr0
      _ = r := one_mul r
  have hexp : 1 - r ≤ Real.exp (-(rhoA0 τ₀ (32 / ε) ħ * T)) := by
    have := Real.add_one_le_exp (-(rhoA0 τ₀ (32 / ε) ħ * T))
    linarith
  have h1r : α * (1 - r) = α' := by rw [hr]; field_simp; ring
  calc α' = α * (1 - r) := h1r.symm
    _ ≤ α * Real.exp (-(rhoA0 τ₀ (32 / ε) ħ * T)) := mul_le_mul_of_nonneg_left hexp hα0.le

end Qschubert
