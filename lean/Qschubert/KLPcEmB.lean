import Qschubert.KLPcCWd
import Qschubert.KLPcEmA

/-!
# The semigroup `e^{-σΛ_m}` in weighted spaces

`w_superpose`: if `G(x) = ∫ g(r) cos(r√(x - 1/4)) dr` on `[1/4, ∞)` and `W` is a weight with `|∇ log W| ≤ l`, then
`‖W G(-Δ) f‖ ≤ (∫ |g| e^{(l + 1/2)|r|}) ‖W f‖`, by `wave_weightD`.

With `sM m x = √(x - 1/4 + m²)` (the symbol of `Λ_m`), `GWM m j σ` is the symbol of `Λ_m^{2j} e^{-σΛ_m}` and `GLamM m a` that of
`Λ_m e^{-aΛ_m}`. For `2(l + 1/2)² < m²`: `poissonM_w`, `lamM_w`, `lamM_pow_w`, `baseM_vj`.
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set Physicslib4.Spectral Physicslib4.Spectral.Unbounded
open scoped ENNReal InnerProductSpace ComplexConjugate UpperHalfPlane

local notation "L2H'" => Lp ℂ 2 (volume : Measure UpperHalfPlane)

/-- **Weighted bound for a superposition of the shifted wave group.** -/
theorem w_superpose {W : ℂ → ℝ} {C l : ℝ} (hW : WaveS W C l) {g : ℝ → ℝ} {G : ℝ → ℂ} (hg : Integrable g) (hG : G ∈ BddMeasurable ℝ)
    (hrep : ∀ x, 1 / 4 ≤ x → ∫ r, (g r : ℂ) * ((Real.cos (r * √(yD x)) : ℝ) : ℂ) = G x)
    {A : ℝ} (hI : Integrable fun r => |g r| * Real.exp ((l + 1 / 2) * |r|)) (hA : ∫ r, |g r| * Real.exp ((l + 1 / 2) * |r|) ≤ A)
    (f : L2H') : ‖mulCL hW.sb (specE.integral G f)‖ ≤ A * ‖mulCL hW.sb f‖ := by
  have hA0 : 0 ≤ A := (integral_nonneg fun r => by positivity).trans hA
  set v := mulCL hW.sb (specE.integral G f) with hv
  set N := ‖mulCL hW.sb f‖ with hN
  have h1 : ⟪v, v⟫_ℂ = ∫ r, (g r : ℂ) * ⟪mulCL hW.sb v, cosDOp r f⟫_ℂ := by
    rw [← pair_superpose hg hG hrep f (mulCL hW.sb v)]
    exact (inner_mulCL_left hW.sb v (specE.integral G f)).symm
  have h2 : ‖⟪v, v⟫_ℂ‖ ≤ ∫ r, |g r| * Real.exp ((l + 1 / 2) * |r|) * (‖v‖ * N) := by
    rw [h1]
    refine norm_integral_le_of_norm_le (hI.mul_const _) (Eventually.of_forall fun r => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, inner_mulCL_left]
    have hw := wave_weightD hW r f
    calc |g r| * ‖⟪v, mulCL hW.sb (cosDOp r f)⟫_ℂ‖
        ≤ |g r| * (‖v‖ * (Real.exp ((l + 1 / 2) * |r|) * N)) :=
          mul_le_mul_of_nonneg_left ((norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hw (norm_nonneg _))) (abs_nonneg _)
      _ = _ := by ring
  rw [integral_mul_const] at h2
  have e : ‖⟪v, v⟫_ℂ‖ = ‖v‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K, norm_pow]
    congr 1
    simp
  rw [e] at h2
  have hnn : 0 ≤ ‖v‖ * N := by positivity
  have h3 : ‖v‖ ^ 2 ≤ A * (‖v‖ * N) := h2.trans (mul_le_mul_of_nonneg_right hA hnn)
  rcases eq_or_lt_of_le (norm_nonneg v) with h0 | hpos
  · rw [← h0]
    positivity
  · have h4 : ‖v‖ * ‖v‖ ≤ ‖v‖ * (A * N) := by nlinarith
    exact le_of_mul_le_mul_left h4 hpos

lemma measurable_sM (m : ℝ) : Measurable (sM m) := by
  unfold sM
  fun_prop

lemma sM_nonneg (m x : ℝ) : 0 ≤ sM m x := Real.sqrt_nonneg _

/-- `Λ_m^{2j} e^{-σΛ_m}`. -/
noncomputable def rWM (m : ℝ) (j : ℕ) (σ x : ℝ) : ℝ := sM m x ^ (2 * j) * Real.exp (-(σ * sM m x))

/-- `Λ_m e^{-aΛ_m}`. -/
noncomputable def rLM (m a x : ℝ) : ℝ := sM m x * Real.exp (-(a * sM m x))

lemma measurable_rWM (m : ℝ) (j : ℕ) (σ : ℝ) : Measurable (rWM m j σ) :=
  ((measurable_sM m).pow_const _).mul (Real.measurable_exp.comp (measurable_const.mul (measurable_sM m)).neg)

lemma measurable_rLM (m a : ℝ) : Measurable (rLM m a) :=
  (measurable_sM m).mul (Real.measurable_exp.comp (measurable_const.mul (measurable_sM m)).neg)

lemma abs_rWM_le (m : ℝ) {j : ℕ} {σ : ℝ} (hσ : 0 < σ) (x : ℝ) : |rWM m j σ x| ≤ ((2 * j).factorial : ℝ) / σ ^ (2 * j) := by
  unfold rWM
  rw [abs_of_nonneg (mul_nonneg (pow_nonneg (sM_nonneg m x) _) (Real.exp_pos _).le)]
  exact pow_mul_exp_le_fac hσ (sM_nonneg m x) _

lemma abs_rLM_le (m : ℝ) {a : ℝ} (ha : 0 < a) (x : ℝ) : |rLM m a x| ≤ 1 / a := by
  unfold rLM
  rw [abs_of_nonneg (mul_nonneg (sM_nonneg m x) (Real.exp_pos _).le)]
  have := pow_mul_exp_le_fac ha (sM_nonneg m x) 1
  simpa using this

/-- The operator symbols. -/
noncomputable def GWM (m : ℝ) (j : ℕ) (σ : ℝ) : ℝ → ℂ := fun x => ((rWM m j σ x : ℝ) : ℂ)

noncomputable def GLamM (m a : ℝ) : ℝ → ℂ := fun x => ((rLM m a x : ℝ) : ℂ)

lemma GWM_mem (m : ℝ) (j : ℕ) {σ : ℝ} (hσ : 0 < σ) : GWM m j σ ∈ BddMeasurable ℝ :=
  memB_of_abs_le (measurable_rWM m j σ) (abs_rWM_le m hσ)

lemma GLamM_mem (m : ℝ) {a : ℝ} (ha : 0 < a) : GLamM m a ∈ BddMeasurable ℝ := memB_of_abs_le (measurable_rLM m a) (abs_rLM_le m ha)

/-- The unweighted bound. -/
lemma norm_GWM_le (m : ℝ) (j : ℕ) {σ : ℝ} (hσ : 0 < σ) (f : L2H') :
    ‖specE.integral (GWM m j σ) f‖ ≤ ((2 * j).factorial : ℝ) / σ ^ (2 * j) * ‖f‖ := by
  have h0 : 0 ≤ ((2 * j).factorial : ℝ) / σ ^ (2 * j) := by positivity
  have h1 : ‖specE.integral (GWM m j σ)‖ ≤ ((2 * j).factorial : ℝ) / σ ^ (2 * j) :=
    (specE.norm_integral_le (GWM_mem m j hσ)).trans (ciSup_le fun x => by
      show ‖((rWM m j σ x : ℝ) : ℂ)‖ ≤ _
      rw [Complex.norm_real]
      exact abs_rWM_le m hσ x)
  exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right h1 (norm_nonneg _))

lemma GWM_eq_pow (m : ℝ) {j : ℕ} (hj : 0 < j) (σ : ℝ) : GWM m j σ = GLamM m (σ / (2 * j)) ^ (2 * j) := by
  funext x
  simp only [GWM, GLamM, Pi.pow_apply, rWM, rLM]
  rw [← Complex.ofReal_pow, mul_pow, ← Real.exp_nat_mul]
  congr 3
  have hj' : (0 : ℝ) < j := by exact_mod_cast hj
  push_cast
  field_simp

section weighted

variable {W : ℂ → ℝ} {C l : ℝ} (hW : WaveS W C l) {m : ℝ} (hm : 1 / 2 ≤ m) (hml : 2 * (l + 1 / 2) ^ 2 < m ^ 2)
include hm hml

/-- **`e^{-τΛ_m}` in the weight `W`.** -/
theorem poissonM_w {τ : ℝ} (hτ : 0 < τ) (f : L2H') :
    ‖mulCL hW.sb (specE.integral (GWM m 0 τ) f)‖ ≤ √2 * ‖mulCL hW.sb f‖ := by
  obtain ⟨hI, hA⟩ := gTauM_expmass (κ := l + 1 / 2) hml hτ
  have hint : Integrable (gTauM m τ) := integrable_of_symbol (gTauM_symbol hm hτ le_rfl).1
  refine w_superpose hW hint (GWM_mem m 0 hτ) (fun x hx => ?_) hI hA f
  refine rep_of_real (R := Real.exp (-(τ * sM m x))) ?_ (gTauM_symbol hm hτ hx).2
  simp [GWM, rWM]

/-- **`Λ_m e^{-sΛ_m}` in the weight `W`.** -/
theorem lamM_w {s : ℝ} (hs : 0 < s) (f : L2H') :
    ‖mulCL hW.sb (specE.integral (GLamM m s) f)‖ ≤ 2 * cH / s * ‖mulCL hW.sb f‖ := by
  obtain ⟨hI, hA⟩ := hSM_expmass (κ := l + 1 / 2) hml hs
  have hint : Integrable (hSM m s) := integrable_of_symbol (hSM_symbol hm hs le_rfl).1
  refine w_superpose hW hint (GLamM_mem m hs) (fun x hx => ?_) hI hA f
  refine rep_of_real (R := sM m x * Real.exp (-(s * sM m x))) ?_ (hSM_symbol hm hs hx).2
  simp [GLamM, rLM]

/-- Powers of `Λ_m e^{-aΛ_m}`. -/
theorem lamM_pow_w {a : ℝ} (ha : 0 < a) (k : ℕ) (f : L2H') :
    ‖mulCL hW.sb (specE.integral (GLamM m a ^ k) f)‖ ≤ (2 * cH / a) ^ k * ‖mulCL hW.sb f‖ := by
  induction k generalizing f with
  | zero =>
    rw [pow_zero, pow_zero, one_mul, specE.integral_one]
    exact le_rfl
  | succ k ih =>
    have hk := pow_mem_B (GLamM_mem m ha) k
    have e : specE.integral (GLamM m a ^ (k + 1)) f = specE.integral (GLamM m a ^ k) (specE.integral (GLamM m a) f) := by
      rw [pow_succ, specE.integral_mul hk (GLamM_mem m ha)]
      rfl
    rw [e]
    have hc := cH_pos
    have hKa : 0 ≤ (2 * cH / a) ^ k := by positivity
    calc _ ≤ (2 * cH / a) ^ k * ‖mulCL hW.sb (specE.integral (GLamM m a) f)‖ := ih _
      _ ≤ (2 * cH / a) ^ k * (2 * cH / a * ‖mulCL hW.sb f‖) := mul_le_mul_of_nonneg_left (lamM_w hW hm hml ha f) hKa
      _ = _ := by rw [pow_succ]; ring

/-- **The base case of the word estimate in the weight `W`.** -/
theorem baseM_vj {σ : ℝ} (hσ : 0 < σ) (j : ℕ) (f : L2H') :
    ‖mulCL hW.sb (specE.integral (GWM m j σ) f)‖
      ≤ √2 * (Real.exp 1 * (2 * cH) / σ) ^ (2 * j) * ((2 * j).factorial : ℝ) * ‖mulCL hW.sb f‖ := by
  have hc := cH_pos
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · have h := poissonM_w hW hm hml hσ f
    simpa using h
  · have hj' : (0 : ℝ) < j := by exact_mod_cast hj
    set a := σ / (2 * j) with ha
    have ha0 : 0 < a := by positivity
    rw [GWM_eq_pow m hj σ]
    refine (lamM_pow_w hW hm hml ha0 (2 * j) f).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    have e1 : 2 * cH / a = (2 * j : ℕ) * (2 * cH / σ) := by
      rw [ha]
      push_cast
      field_simp
    rw [e1, mul_pow]
    have hn := Real.pow_div_factorial_le_exp ((2 * j : ℕ) : ℝ) (by positivity) (2 * j)
    have hf : (0 : ℝ) < (2 * j).factorial := by exact_mod_cast (2 * j).factorial_pos
    rw [div_le_iff₀ hf, ← Real.exp_one_pow] at hn
    have e2 : (Real.exp 1 * (2 * cH) / σ) ^ (2 * j) = Real.exp 1 ^ (2 * j) * (2 * cH / σ) ^ (2 * j) := by
      rw [mul_div_assoc, mul_pow]
    rw [e2]
    have hKs : 0 ≤ (2 * cH / σ) ^ (2 * j) := by positivity
    have h2 : (1 : ℝ) ≤ √2 := by
      rw [show (1 : ℝ) = √1 by simp]
      exact Real.sqrt_le_sqrt (by norm_num)
    calc ((2 * j : ℕ) : ℝ) ^ (2 * j) * (2 * cH / σ) ^ (2 * j)
        ≤ (Real.exp 1 ^ (2 * j) * ((2 * j).factorial : ℝ)) * (2 * cH / σ) ^ (2 * j) := mul_le_mul_of_nonneg_right hn hKs
      _ = 1 * (Real.exp 1 ^ (2 * j) * (2 * cH / σ) ^ (2 * j)) * ((2 * j).factorial : ℝ) := by ring
      _ ≤ √2 * (Real.exp 1 ^ (2 * j) * (2 * cH / σ) ^ (2 * j)) * ((2 * j).factorial : ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 (by positivity)) hf.le

end weighted

end Qschubert
