import Qschubert.KLKernelZ
import Qschubert.KLSchur
import Qschubert.FC0
import Qschubert.LocalWeak

/-!
# Lemma FC, case `Z = X`, `α'' > 0`

Piece A (the kernel bound of dd_appendix.tex:133–137). With `Λ(ν) = (ν² + 1/4)^{1/2}`,
`x = ν - ν'` and `g(x) = (1 + |x|) e^{τ|x|} / (2 cosh(πx/2))`: for `ν, ν' > 0` and `0 ≤ a ≤ τ`,
`√(w(ν) w(ν')) M_1(ν, ν') e^{a(Λ(ν) - Λ(ν'))} / Λ(ν') ≤ g(x)` (`kernel_bound`); `g` is integrable
for `τ < π/2` (`integrable_gK`); `Λ e^{-γΛ} ≤ 1/(eγ)` (`mul_exp_neg_le_inv`).
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set
open scoped ENNReal

/-- `Λ(ν) = (ν² + 1/4)^{1/2}`. -/
noncomputable def LamK (ν : ℝ) : ℝ := Real.sqrt (ν ^ 2 + 1 / 4)

lemma LamK_pos (ν : ℝ) : 0 < LamK ν := Real.sqrt_pos.2 (by positivity)

lemma le_LamK (ν : ℝ) : |ν| ≤ LamK ν := by
  rw [LamK, ← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by linarith)

lemma half_le_LamK (ν : ℝ) : 1 / 2 ≤ LamK ν := by
  rw [LamK, show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ν])

lemma continuous_LamK : Continuous LamK := by unfold LamK; fun_prop

/-- `Λ` is 1-Lipschitz. -/
lemma abs_LamK_sub_le (ν ν' : ℝ) : |LamK ν - LamK ν'| ≤ |ν - ν'| := by
  have h1 := LamK_pos ν; have h2 := LamK_pos ν'
  have hs : (LamK ν) ^ 2 = ν ^ 2 + 1 / 4 := Real.sq_sqrt (by positivity)
  have hs' : (LamK ν') ^ 2 = ν' ^ 2 + 1 / 4 := Real.sq_sqrt (by positivity)
  have hprod : |LamK ν - LamK ν'| * (LamK ν + LamK ν') = |ν - ν'| * |ν + ν'| := by
    rw [← abs_of_pos (add_pos h1 h2), ← abs_mul, ← abs_mul]; congr 1; nlinarith
  have hle : |ν + ν'| ≤ LamK ν + LamK ν' := (abs_add_le _ _).trans (add_le_add (le_LamK ν) (le_LamK ν'))
  by_contra hcon
  push_neg at hcon
  have : |ν - ν'| * |ν + ν'| < |LamK ν - LamK ν'| * (LamK ν + LamK ν') := by
    calc |ν - ν'| * |ν + ν'| ≤ |ν - ν'| * (LamK ν + LamK ν') := mul_le_mul_of_nonneg_left hle (abs_nonneg _)
      _ < |LamK ν - LamK ν'| * (LamK ν + LamK ν') := mul_lt_mul_of_pos_right hcon (by positivity)
  linarith

/-- `sinh a sinh b ≤ cosh²((a + b)/2)`. -/
lemma sinh_mul_sinh_le (a b : ℝ) : Real.sinh a * Real.sinh b ≤ Real.cosh ((a + b) / 2) ^ 2 := by
  have e : Real.sinh a * Real.sinh b = (Real.cosh (a + b) - Real.cosh (a - b)) / 2 := by
    rw [Real.cosh_add, Real.cosh_sub]; ring
  have h2 : Real.cosh (a + b) = 2 * Real.cosh ((a + b) / 2) ^ 2 - 1 := by
    have h := Real.cosh_two_mul ((a + b) / 2)
    rw [show 2 * ((a + b) / 2) = a + b by ring] at h
    rw [h, Real.cosh_sq ((a + b) / 2)]; ring
  rw [e, h2]
  nlinarith [Real.one_le_cosh (a - b)]

/-- `√(w w') M_1 ≤ √(ν ν') / (2 cosh(π(ν - ν')/2))`. -/
lemma sqrt_klW_mul_kerM1_le {ν ν' : ℝ} (hν : 0 ≤ ν) (hν' : 0 ≤ ν') :
    Real.sqrt (klW ν) * Real.sqrt (klW ν') * kerM1 ν ν'
      ≤ Real.sqrt (ν * ν') / (2 * Real.cosh (Real.pi * ((ν - ν') / 2))) := by
  have hp := Real.pi_pos
  have hw := klW_nonneg hν; have hw' := klW_nonneg hν'
  have hcp := Real.cosh_pos (Real.pi * ((ν + ν') / 2))
  have hcq := Real.cosh_pos (Real.pi * ((ν - ν') / 2))
  have hs0 : 0 ≤ Real.sinh (Real.pi * ν) := Real.sinh_nonneg_iff.2 (by positivity)
  have hs0' : 0 ≤ Real.sinh (Real.pi * ν') := Real.sinh_nonneg_iff.2 (by positivity)
  have hsin : Real.sinh (Real.pi * ν) * Real.sinh (Real.pi * ν') ≤ Real.cosh (Real.pi * ((ν + ν') / 2)) ^ 2 := by
    have := sinh_mul_sinh_le (Real.pi * ν) (Real.pi * ν')
    rwa [show (Real.pi * ν + Real.pi * ν') / 2 = Real.pi * ((ν + ν') / 2) by ring] at this
  have hL0 : 0 ≤ Real.sqrt (klW ν) * Real.sqrt (klW ν') * kerM1 ν ν' :=
    mul_nonneg (by positivity) (kerM1_pos _ _).le
  have hR0 : 0 ≤ Real.sqrt (ν * ν') / (2 * Real.cosh (Real.pi * ((ν - ν') / 2))) := by positivity
  refine (pow_le_pow_iff_left₀ hL0 hR0 two_ne_zero).1 ?_
  rw [mul_pow, mul_pow, Real.sq_sqrt hw, Real.sq_sqrt hw', div_pow, Real.sq_sqrt (mul_nonneg hν hν')]
  set Cp := Real.cosh (Real.pi * ((ν + ν') / 2))
  set Cq := Real.cosh (Real.pi * ((ν - ν') / 2))
  set S := Real.sinh (Real.pi * ν) * Real.sinh (Real.pi * ν')
  have key : klW ν * klW ν' * kerM1 ν ν' ^ 2 = ν * ν' * S / (4 * Cp ^ 2 * Cq ^ 2) := by
    unfold klW kerM1; simp only [S, Cp, Cq]; field_simp; ring
  rw [key]
  have hνν : 0 ≤ ν * ν' := mul_nonneg hν hν'
  calc ν * ν' * S / (4 * Cp ^ 2 * Cq ^ 2) ≤ ν * ν' * Cp ^ 2 / (4 * Cp ^ 2 * Cq ^ 2) := by gcongr
    _ = ν * ν' / (2 * Cq) ^ 2 := by field_simp; ring

/-- The paper's majorant `g(x) = (1 + |x|) e^{τ|x|} / (2 cosh(πx/2))`. -/
noncomputable def gK (τ x : ℝ) : ℝ := (1 + |x|) * Real.exp (τ * |x|) / (2 * Real.cosh (Real.pi * (x / 2)))

lemma gK_nonneg (τ x : ℝ) : 0 ≤ gK τ x := by
  unfold gK; have := Real.cosh_pos (Real.pi * (x / 2)); positivity

lemma continuous_gK (τ : ℝ) : Continuous (gK τ) := by
  unfold gK
  exact (by fun_prop : Continuous fun x : ℝ => (1 + |x|) * Real.exp (τ * |x|)).div (by fun_prop)
    (fun x => by have := Real.cosh_pos (Real.pi * (x / 2)); positivity)

/-- **The kernel bound** (dd_appendix.tex:133–137). -/
theorem kernel_bound {τ a ν ν' : ℝ} (ha : 0 ≤ a) (haτ : a ≤ τ) (hν : 0 ≤ ν) (hν' : 0 ≤ ν') :
    Real.sqrt (klW ν) * Real.sqrt (klW ν') * kerM1 ν ν' * Real.exp (a * (LamK ν - LamK ν')) / LamK ν'
      ≤ gK τ (ν - ν') := by
  have h1 := sqrt_klW_mul_kerM1_le hν hν'
  have hL := LamK_pos ν'
  have hcq := Real.cosh_pos (Real.pi * ((ν - ν') / 2))
  have he : Real.exp (a * (LamK ν - LamK ν')) ≤ Real.exp (τ * |ν - ν'|) := by
    refine Real.exp_le_exp.2 ?_
    calc a * (LamK ν - LamK ν') ≤ a * |LamK ν - LamK ν'| := mul_le_mul_of_nonneg_left (le_abs_self _) ha
      _ ≤ a * |ν - ν'| := mul_le_mul_of_nonneg_left (abs_LamK_sub_le ν ν') ha
      _ ≤ τ * |ν - ν'| := mul_le_mul_of_nonneg_right haτ (abs_nonneg _)
  have hs : Real.sqrt (ν * ν') ≤ (1 + |ν - ν'|) * LamK ν' := by
    have h2 : Real.sqrt (ν * ν') ≤ (ν + ν') / 2 := by
      rw [Real.sqrt_le_left (by positivity)]; nlinarith [sq_nonneg (ν - ν')]
    have h3 := le_LamK ν'; rw [abs_of_nonneg hν'] at h3
    have h4 := half_le_LamK ν'
    have h5 : (ν - ν') / 2 ≤ |ν - ν'| * LamK ν' := by
      nlinarith [le_abs_self (ν - ν'), abs_nonneg (ν - ν')]
    nlinarith
  have hk0 := (kerM1_pos ν ν').le
  have hA : 0 ≤ Real.sqrt (klW ν) * Real.sqrt (klW ν') * kerM1 ν ν' := by positivity
  calc Real.sqrt (klW ν) * Real.sqrt (klW ν') * kerM1 ν ν' * Real.exp (a * (LamK ν - LamK ν')) / LamK ν'
      ≤ Real.sqrt (ν * ν') / (2 * Real.cosh (Real.pi * ((ν - ν') / 2))) * Real.exp (τ * |ν - ν'|) / LamK ν' := by
        gcongr
    _ ≤ (1 + |ν - ν'|) * LamK ν' / (2 * Real.cosh (Real.pi * ((ν - ν') / 2))) * Real.exp (τ * |ν - ν'|) / LamK ν' := by
        gcongr
    _ = gK τ (ν - ν') := by unfold gK; field_simp

/-- `Λ e^{-γΛ} ≤ 1/(eγ)`. -/
lemma mul_exp_neg_le_inv {γ x : ℝ} (hγ : 0 < γ) (hx : 0 ≤ x) :
    x * Real.exp (-(γ * x)) ≤ 1 / (Real.exp 1 * γ) := by
  have h := Real.add_one_le_exp (γ * x - 1)
  have he : Real.exp (γ * x - 1) = Real.exp (γ * x) / Real.exp 1 := by rw [Real.exp_sub]
  rw [he] at h
  have hE := Real.exp_pos (γ * x)
  have h1 := Real.exp_pos 1
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ hE (by positivity)]
  rw [le_div_iff₀ h1] at h
  nlinarith

/-- `g` is integrable for `τ < π/2`: `g(x) ≤ (1 + 2/(eδ)) / cosh(δx/2)`, `δ = π/2 - τ`. -/
theorem integrable_gK {τ : ℝ} (hτ : τ < Real.pi / 2) : Integrable (gK τ) := by
  set δ : ℝ := Real.pi / 2 - τ
  have hδ : 0 < δ := by simp only [δ]; linarith
  have hsech : Integrable fun x : ℝ => (Real.cosh (δ / 2 * x))⁻¹ :=
    integrable_inv_cosh.comp_mul_left' (by positivity)
  refine (hsech.const_mul (1 + 2 / (Real.exp 1 * δ))).mono' (continuous_gK τ).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (gK_nonneg τ x)]
  have hx := abs_nonneg x
  have hcosh_ge : ∀ y : ℝ, Real.exp |y| / 2 ≤ Real.cosh y := by
    intro y
    rcases le_or_gt 0 y with hy | hy
    · rw [abs_of_nonneg hy, Real.cosh_eq]; linarith [Real.exp_pos (-y)]
    · rw [abs_of_neg hy, Real.cosh_eq]; linarith [Real.exp_pos y]
  have hcosh_le : ∀ y : ℝ, Real.cosh y ≤ Real.exp |y| := by
    intro y
    rw [Real.cosh_eq]
    rcases le_or_gt 0 y with hy | hy
    · rw [abs_of_nonneg hy]
      have : Real.exp (-y) ≤ Real.exp y := Real.exp_le_exp.2 (by linarith)
      linarith
    · rw [abs_of_neg hy]
      have : Real.exp y ≤ Real.exp (-y) := Real.exp_le_exp.2 (by linarith)
      linarith
  have h1 : Real.exp (Real.pi * |x| / 2) / 2 ≤ Real.cosh (Real.pi * (x / 2)) := by
    have := hcosh_ge (Real.pi * (x / 2))
    rwa [show |Real.pi * (x / 2)| = Real.pi * |x| / 2 by
      rw [abs_mul, abs_of_pos Real.pi_pos, abs_div, abs_two]; ring] at this
  have h2 : Real.cosh (δ / 2 * x) ≤ Real.exp (δ / 2 * |x|) := by
    have := hcosh_le (δ / 2 * x)
    rwa [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < δ / 2)] at this
  have h3 : |x| * Real.exp (-(δ / 2 * |x|)) ≤ 1 / (Real.exp 1 * (δ / 2)) :=
    mul_exp_neg_le_inv (by positivity) hx
  have hcp := Real.cosh_pos (Real.pi * (x / 2))
  have hcd := Real.cosh_pos (δ / 2 * x)
  -- `g(x) ≤ (1 + |x|) e^{-δ|x|}`
  have hg1 : gK τ x ≤ (1 + |x|) * Real.exp (-(δ * |x|)) := by
    unfold gK
    rw [div_le_iff₀ (by positivity)]
    have key : Real.exp (τ * |x|) = Real.exp (-(δ * |x|)) * Real.exp (Real.pi * |x| / 2) := by
      rw [← Real.exp_add]; congr 1; simp only [δ]; ring
    rw [key]
    have hE := Real.exp_pos (-(δ * |x|))
    nlinarith [mul_le_mul_of_nonneg_left h1 (show 0 ≤ (1 + |x|) * Real.exp (-(δ * |x|)) * 2 by positivity)]
  -- `(1 + |x|) e^{-δ|x|} cosh(δx/2) ≤ 1 + 2/(eδ)`
  have hg2 : (1 + |x|) * Real.exp (-(δ * |x|)) * Real.cosh (δ / 2 * x) ≤ 1 + 2 / (Real.exp 1 * δ) := by
    have e1 : Real.exp (-(δ * |x|)) * Real.exp (δ / 2 * |x|) = Real.exp (-(δ / 2 * |x|)) := by
      rw [← Real.exp_add]; congr 1; ring
    have hle1 : Real.exp (-(δ / 2 * |x|)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    have e2 : 1 / (Real.exp 1 * (δ / 2)) = 2 / (Real.exp 1 * δ) := by field_simp
    calc (1 + |x|) * Real.exp (-(δ * |x|)) * Real.cosh (δ / 2 * x)
        ≤ (1 + |x|) * Real.exp (-(δ * |x|)) * Real.exp (δ / 2 * |x|) := by gcongr
      _ = Real.exp (-(δ / 2 * |x|)) + |x| * Real.exp (-(δ / 2 * |x|)) := by rw [mul_assoc, e1]; ring
      _ ≤ 1 + 2 / (Real.exp 1 * δ) := by rw [← e2]; exact add_le_add hle1 h3
  calc gK τ x ≤ (1 + |x|) * Real.exp (-(δ * |x|)) := hg1
    _ = (1 + |x|) * Real.exp (-(δ * |x|)) * Real.cosh (δ / 2 * x) * (Real.cosh (δ / 2 * x))⁻¹ := by
        field_simp
    _ ≤ (1 + 2 / (Real.exp 1 * δ)) * (Real.cosh (δ / 2 * x))⁻¹ := by gcongr

/-! ### Piece B: kernel operators dominated by a convolution kernel (Schur) -/

/-- `T_κ a (ν) = ∫_0^∞ κ(ν, ν') a(ν') w(ν') dν'`. -/
noncomputable def kerOp (κ : ℝ → ℝ → ℝ) (a : ℝ → ℂ) (ν : ℝ) : ℂ :=
  ∫ ν' in Ioi 0, (κ ν ν' : ℂ) * ((klW ν' : ℂ) * a ν')

/-- `√w |a|` on `(0, ∞)`. -/
noncomputable def wb (a : ℝ → ℂ) (ν : ℝ) : ℝ≥0∞ :=
  (Ioi (0 : ℝ)).indicator (fun ν => ENNReal.ofReal (Real.sqrt (klW ν)) * ‖a ν‖ₑ) ν

lemma measurable_sqrt_klW : Measurable fun ν => ENNReal.ofReal (Real.sqrt (klW ν)) :=
  ENNReal.measurable_ofReal.comp (Real.continuous_sqrt.comp continuous_klW).measurable

lemma measurable_wb {a : ℝ → ℂ} (ha : Measurable a) : Measurable (wb a) :=
  (measurable_sqrt_klW.mul ha.enorm).indicator measurableSet_Ioi

lemma ofReal_sqrt_sq {x : ℝ} (hx : 0 ≤ x) : ENNReal.ofReal (Real.sqrt x) ^ 2 = ENNReal.ofReal x := by
  rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt hx]

lemma lintegral_wNu_eq {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ ν, F ν ∂wNu = ∫⁻ ν in Ioi 0, ENNReal.ofReal (klW ν) * F ν := by
  rw [wNu, lintegral_withDensity_eq_lintegral_mul _ measurable_klW_dens hF]; rfl

lemma lintegral_wb_sq {a : ℝ → ℂ} (ha : Measurable a) :
    ∫⁻ ν, wb a ν ^ 2 = ∫⁻ ν, ‖a ν‖ₑ ^ 2 ∂wNu := by
  rw [lintegral_wNu_eq (ha.enorm.pow_const 2)]
  have e : (fun ν => wb a ν ^ 2) = (Ioi (0 : ℝ)).indicator
      (fun ν => ENNReal.ofReal (klW ν) * ‖a ν‖ₑ ^ 2) := by
    funext ν
    by_cases hν : ν ∈ Ioi (0 : ℝ)
    · simp only [wb, Set.indicator_of_mem hν, mul_pow, ofReal_sqrt_sq (klW_nonneg (le_of_lt hν))]
    · simp [wb, Set.indicator_of_notMem hν]
  rw [e, lintegral_indicator measurableSet_Ioi]

/-- **Schur bound for `T_κ`**: if `√(w w') |κ| ≤ C g(ν - ν')` on `(0,∞)²`, then
`∫ w |T_κ a|² ≤ (C ∫ g)² ∫ w |a|²`. -/
theorem kerOp_bound {κ : ℝ → ℝ → ℝ} {g : ℝ → ℝ} (hg : Measurable g) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ ν ν', 0 < ν → 0 < ν' → Real.sqrt (klW ν) * Real.sqrt (klW ν') * |κ ν ν'| ≤ C * g (ν - ν'))
    {a : ℝ → ℂ} (ha : Measurable a) :
    ∫⁻ ν in Ioi 0, ENNReal.ofReal (klW ν) * ‖kerOp κ a ν‖ₑ ^ 2
      ≤ (ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal (g x)) ^ 2 * ∫⁻ ν, ‖a ν‖ₑ ^ 2 ∂wNu := by
  set G' : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (C * g x)
  have hG' : Measurable G' := ENNReal.measurable_ofReal.comp (measurable_const.mul hg)
  have hpt : ∀ ν, 0 < ν → ENNReal.ofReal (Real.sqrt (klW ν)) * ‖kerOp κ a ν‖ₑ
      ≤ ∫⁻ ν', G' (ν - ν') * wb a ν' := by
    intro ν hν
    have h1 : ‖kerOp κ a ν‖ₑ ≤ ∫⁻ ν' in Ioi 0, ‖(κ ν ν' : ℂ) * ((klW ν' : ℂ) * a ν')‖ₑ :=
      enorm_integral_le_lintegral_enorm _
    calc ENNReal.ofReal (Real.sqrt (klW ν)) * ‖kerOp κ a ν‖ₑ
        ≤ ENNReal.ofReal (Real.sqrt (klW ν)) * ∫⁻ ν' in Ioi 0, ‖(κ ν ν' : ℂ) * ((klW ν' : ℂ) * a ν')‖ₑ := by
          gcongr
      _ = ∫⁻ ν' in Ioi 0, ENNReal.ofReal (Real.sqrt (klW ν)) * ‖(κ ν ν' : ℂ) * ((klW ν' : ℂ) * a ν')‖ₑ :=
          (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ ≤ ∫⁻ ν' in Ioi 0, G' (ν - ν') * (ENNReal.ofReal (Real.sqrt (klW ν')) * ‖a ν'‖ₑ) := by
          refine setLIntegral_mono' measurableSet_Ioi (fun ν' hν' => ?_)
          have hw' := klW_nonneg (le_of_lt (hν' : (0 : ℝ) < ν'))
          have hκ := hb ν ν' hν hν'
          have e1 : ‖((κ ν ν' : ℝ) : ℂ)‖ₑ = ENNReal.ofReal |κ ν ν'| := by
            rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_eq_abs]
          have e2 : ‖((klW ν' : ℝ) : ℂ)‖ₑ = ENNReal.ofReal (Real.sqrt (klW ν')) ^ 2 := by
            rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw',
              ofReal_sqrt_sq hw']
          rw [enorm_mul, enorm_mul, e1, e2]
          have e3 : ENNReal.ofReal (Real.sqrt (klW ν)) * (ENNReal.ofReal |κ ν ν'| *
              (ENNReal.ofReal (Real.sqrt (klW ν')) ^ 2 * ‖a ν'‖ₑ))
              = ENNReal.ofReal (Real.sqrt (klW ν) * Real.sqrt (klW ν') * |κ ν ν'|) *
                (ENNReal.ofReal (Real.sqrt (klW ν')) * ‖a ν'‖ₑ) := by
            rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (Real.sqrt_nonneg _)]; ring
          rw [e3]
          gcongr
          exact ENNReal.ofReal_le_ofReal hκ
      _ = ∫⁻ ν', G' (ν - ν') * wb a ν' := by
          rw [← lintegral_indicator measurableSet_Ioi]
          refine lintegral_congr fun ν' => ?_
          simp only [wb, Set.indicator_apply]
          split_ifs <;> simp
  have hpt2 : ∀ ν, 0 < ν → ENNReal.ofReal (klW ν) * ‖kerOp κ a ν‖ₑ ^ 2
      ≤ (∫⁻ ν', G' (ν - ν') * wb a ν') ^ 2 := by
    intro ν hν
    rw [← ofReal_sqrt_sq (klW_nonneg (le_of_lt hν)), ← mul_pow]
    exact pow_le_pow_left₀ zero_le (hpt ν hν) 2
  have hS := schur_conv hG' (measurable_wb ha)
  rw [lintegral_wb_sq ha] at hS
  have hG'int : ∫⁻ x, G' x = ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal (g x) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun x => ?_
    simp only [G']
    rcases le_or_gt 0 (g x) with h | h
    · rw [ENNReal.ofReal_mul hC]
    · rw [ENNReal.ofReal_of_nonpos (by nlinarith), ENNReal.ofReal_of_nonpos h.le, mul_zero]
  calc ∫⁻ ν in Ioi 0, ENNReal.ofReal (klW ν) * ‖kerOp κ a ν‖ₑ ^ 2
      ≤ ∫⁻ ν in Ioi 0, (∫⁻ ν', G' (ν - ν') * wb a ν') ^ 2 :=
        setLIntegral_mono' measurableSet_Ioi hpt2
    _ ≤ ∫⁻ ν, (∫⁻ ν', G' (ν - ν') * wb a ν') ^ 2 := setLIntegral_le_lintegral _ _
    _ ≤ (∫⁻ x, G' x) ^ 2 * ∫⁻ ν, ‖a ν‖ₑ ^ 2 ∂wNu := hS
    _ = _ := by rw [hG'int]

/-- **Bilinear Schur bound** (finiteness of the Fubini integrand). -/
theorem kerOp_bilin {κ : ℝ → ℝ → ℝ} {g : ℝ → ℝ} (hg : Measurable g) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ ν ν', 0 < ν → 0 < ν' → Real.sqrt (klW ν) * Real.sqrt (klW ν') * |κ ν ν'| ≤ C * g (ν - ν'))
    {a c : ℝ → ℂ} (ha : Measurable a) (hc : Measurable c) :
    (∫⁻ ν in Ioi 0, ∫⁻ ν' in Ioi 0,
        ENNReal.ofReal (klW ν) * (ENNReal.ofReal (klW ν') * ENNReal.ofReal |κ ν ν'|) * (‖a ν'‖ₑ * ‖c ν‖ₑ)) ^ 2
      ≤ (ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal (g x)) ^ 2 * (∫⁻ ν, ‖c ν‖ₑ ^ 2 ∂wNu) * ∫⁻ ν, ‖a ν‖ₑ ^ 2 ∂wNu := by
  set G' : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (C * g x)
  have hG' : Measurable G' := ENNReal.measurable_ofReal.comp (measurable_const.mul hg)
  have hpt : ∀ ν, 0 < ν → ∫⁻ ν' in Ioi 0,
      ENNReal.ofReal (klW ν) * (ENNReal.ofReal (klW ν') * ENNReal.ofReal |κ ν ν'|) * (‖a ν'‖ₑ * ‖c ν‖ₑ)
      ≤ wb c ν * ∫⁻ ν', G' (ν - ν') * wb a ν' := by
    intro ν hν
    have hw := klW_nonneg (le_of_lt hν)
    have hwbc : wb c ν = ENNReal.ofReal (Real.sqrt (klW ν)) * ‖c ν‖ₑ := by
      unfold wb; rw [Set.indicator_of_mem (show ν ∈ Ioi (0 : ℝ) from hν)]
    rw [hwbc,
      ← lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top enorm_ne_top),
      ← lintegral_indicator measurableSet_Ioi]
    refine lintegral_mono fun ν' => ?_
    by_cases hν' : ν' ∈ Ioi (0 : ℝ)
    · have hw' := klW_nonneg (le_of_lt (hν' : (0 : ℝ) < ν'))
      have hκ := hb ν ν' hν hν'
      simp only [Set.indicator_of_mem hν', wb]
      rw [← ofReal_sqrt_sq hw, ← ofReal_sqrt_sq hw']
      calc ENNReal.ofReal (Real.sqrt (klW ν)) ^ 2 *
            (ENNReal.ofReal (Real.sqrt (klW ν')) ^ 2 * ENNReal.ofReal |κ ν ν'|) * (‖a ν'‖ₑ * ‖c ν‖ₑ)
          = (ENNReal.ofReal (Real.sqrt (klW ν)) * ‖c ν‖ₑ) *
              (ENNReal.ofReal (Real.sqrt (klW ν) * Real.sqrt (klW ν') * |κ ν ν'|) *
                (ENNReal.ofReal (Real.sqrt (klW ν')) * ‖a ν'‖ₑ)) := by
            rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (Real.sqrt_nonneg _)]; ring
        _ ≤ (ENNReal.ofReal (Real.sqrt (klW ν)) * ‖c ν‖ₑ) *
              (G' (ν - ν') * (ENNReal.ofReal (Real.sqrt (klW ν')) * ‖a ν'‖ₑ)) := by
            gcongr
            exact ENNReal.ofReal_le_ofReal hκ
    · simp [Set.indicator_of_notMem hν', wb]
  have hS := schur_bilin hG' (measurable_wb ha) (measurable_wb hc)
  rw [lintegral_wb_sq ha, lintegral_wb_sq hc] at hS
  have hG'int : ∫⁻ x, G' x = ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal (g x) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun x => ?_
    simp only [G']
    rcases le_or_gt 0 (g x) with h | h
    · rw [ENNReal.ofReal_mul hC]
    · rw [ENNReal.ofReal_of_nonpos (by nlinarith), ENNReal.ofReal_of_nonpos h.le, mul_zero]
  calc (∫⁻ ν in Ioi 0, ∫⁻ ν' in Ioi 0,
        ENNReal.ofReal (klW ν) * (ENNReal.ofReal (klW ν') * ENNReal.ofReal |κ ν ν'|) * (‖a ν'‖ₑ * ‖c ν‖ₑ)) ^ 2
      ≤ (∫⁻ ν in Ioi 0, wb c ν * ∫⁻ ν', G' (ν - ν') * wb a ν') ^ 2 :=
        pow_le_pow_left₀ zero_le (setLIntegral_mono' measurableSet_Ioi hpt) 2
    _ ≤ (∫⁻ ν, wb c ν * ∫⁻ ν', G' (ν - ν') * wb a ν') ^ 2 :=
        pow_le_pow_left₀ zero_le (setLIntegral_le_lintegral _ _) 2
    _ ≤ _ := by rw [← hG'int]; exact hS

/-! ### Piece C: `e^{-αΛ}` and `X` in the KL picture -/

lemma tendsto_expCut_g {α : ℝ} (hα : 0 < α) :
    Tendsto (fun s : ℝ => ((Real.exp (-(α * Real.sqrt |s|)) : ℝ) : ℂ)) (cocompact ℝ) (𝓝 0) := by
  have h1 : Tendsto (fun s : ℝ => |s|) (cocompact ℝ) atTop :=
    (tendsto_norm_cocompact_atTop (E := ℝ)).congr fun s => Real.norm_eq_abs s
  have h2 : Tendsto (fun s : ℝ => -(α * Real.sqrt |s|)) (cocompact ℝ) atBot :=
    tendsto_neg_atTop_atBot.comp ((Real.tendsto_sqrt_atTop.comp h1).const_mul_atTop hα)
  have h3 := Real.tendsto_exp_atBot.comp h2
  have h4 := (Complex.continuous_ofReal.tendsto 0).comp h3
  rw [Complex.ofReal_zero] at h4
  exact h4

/-- **`klU (e^{-αΛ} v) = e^{-αΛ(ν)} klU v`.** -/
theorem klU_expCut {α : ℝ} (hα : 0 < α) (v : Lp ℂ 2 (volume : Measure UpperHalfPlane)) :
    ((klU ((expCut α hα).J v) : Lp ℂ 2 muU) : ℝ × ℝ → ℂ) =ᵐ[muU]
      fun p => ((Real.exp (-(α * LamK p.2)) : ℝ) : ℂ) * (klU v : ℝ × ℝ → ℂ) p := by
  have hc : Continuous (expCut α hα).g := by
    show Continuous fun s : ℝ => ((Real.exp (-(α * Real.sqrt |s|)) : ℝ) : ℂ)
    fun_prop
  have h := klU_functionalCalculus hc (tendsto_expCut_g hα) v
  filter_upwards [h] with p hp
  rw [show (expCut α hα).J v = (Physicslib4.Spectral.Unbounded.spectralMeasure negLapH_isSelfAdjoint).integral
    (expCut α hα).g v from rfl, hp]
  show ((Real.exp (-(α * Real.sqrt |p.2 ^ 2 + 1 / 4|)) : ℝ) : ℂ) * _ = _
  rw [abs_of_pos (by positivity : (0 : ℝ) < p.2 ^ 2 + 1 / 4)]; rfl

/-- `sgn k = k/|k|`. -/
noncomputable def sgnK (k : ℝ) : ℝ := k / |k|

lemma abs_sgnK {k : ℝ} (hk : k ≠ 0) : |sgnK k| = 1 := by
  unfold sgnK; rw [abs_div, abs_abs, div_self (abs_ne_zero.2 hk)]

lemma measurable_sgnK : Measurable sgnK := by unfold sgnK; fun_prop

lemma klT_const_mul (c : ℂ) (g : ℝ → ℂ) (ν : ℝ) : klT (fun z => c * g z) ν = c * klT g ν := by
  unfold klT; rw [← MeasureTheory.integral_const_mul]; congr 1; funext z; ring

/-- **The mode identity for `X = y∂_x`**: `f_k(XP) = i sgn(k) z f_k(P)`. -/
lemma modeF_vfX (P : testFn) {k : ℝ} (hk : k ≠ 0) (z : ℝ) :
    modeF ((vfTest 1 P : testFn) : ℂ → ℂ) k z = (Complex.I * (sgnK k : ℂ)) * ((z : ℂ) * modeF P k z) := by
  unfold modeF
  rw [prof_vfX]
  have hk' : ((|k| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast abs_ne_zero.2 hk
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  unfold sgnK modeC
  push_cast
  field_simp

/-- The `X`-kernel on `L²(dk ⊗ w dν)`: `(K_X G)(k, ν) = i sgn(k) (K₁ G(k, ·))(ν)`. -/
noncomputable def KX (G : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  (Complex.I * (sgnK p.1 : ℂ)) * K1op (fun ν' => G (p.1, ν')) p.2

lemma stronglyMeasurable_KX {G : ℝ × ℝ → ℂ} (hG : StronglyMeasurable G) : StronglyMeasurable (KX G) := by
  set F : (ℝ × ℝ) × ℝ → ℂ := fun q => (kerM1 q.1.2 q.2 : ℂ) * ((klW q.2 : ℂ) * G (q.1.1, q.2))
  have m1 : Measurable fun q : (ℝ × ℝ) × ℝ => kerM1 q.1.2 q.2 :=
    (continuous_M1.comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd)).measurable
  have m2 : Measurable fun q : (ℝ × ℝ) × ℝ => klW q.2 := (continuous_klW.comp continuous_snd).measurable
  have m3 : Measurable fun q : (ℝ × ℝ) × ℝ => G (q.1.1, q.2) :=
    hG.measurable.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hF : StronglyMeasurable F :=
    ((Complex.measurable_ofReal.comp m1).mul ((Complex.measurable_ofReal.comp m2).mul m3)).stronglyMeasurable
  have h1 : StronglyMeasurable fun p : ℝ × ℝ => ∫ ν', F (p, ν') ∂(volume.restrict (Ioi (0 : ℝ))) :=
    hF.integral_prod_right'
  have h2 : StronglyMeasurable fun p : ℝ × ℝ => Complex.I * (sgnK p.1 : ℂ) :=
    (measurable_const.mul (Complex.measurable_ofReal.comp (measurable_sgnK.comp measurable_fst))).stronglyMeasurable
  have e : KX G = fun p : ℝ × ℝ => (Complex.I * (sgnK p.1 : ℂ)) *
      ∫ ν', F (p, ν') ∂(volume.restrict (Ioi (0 : ℝ))) := rfl
  rw [e]
  exact h2.mul h1

/-- **`klU (X P) = K_X (klU P)`** for test functions `P` (via `klT_mul_id_ae` on each mode). -/
theorem UF_vfX_ae (P : testFn) :
    UF ((vfTest 1 P : testFn) : ℂ → ℂ) =ᵐ[muU] KX (UF P) := by
  have hms : MeasurableSet {p | UF ((vfTest 1 P : testFn) : ℂ → ℂ) p = KX (UF P) p} :=
    measurableSet_eq_fun (stronglyMeasurable_UF (vfTest 1 P)).measurable
      (stronglyMeasurable_KX (stronglyMeasurable_UF P)).measurable
  show ∀ᵐ p ∂((volume : Measure ℝ).prod wNu), _
  rw [Measure.ae_prod_iff_ae_ae hms]
  filter_upwards [ae_ne_zero_real] with k hk
  have h := klT_mul_id_ae (isKTest_modeF P hk)
  have h' : ∀ᵐ ν ∂wNu, klT (fun z : ℝ => (z : ℂ) * modeF P k z) ν = K1op (klT (modeF P k)) ν :=
    (withDensity_absolutelyContinuous (volume.restrict (Ioi (0 : ℝ)))
      (fun ν => ENNReal.ofReal (klW ν))).ae_le h
  filter_upwards [h'] with ν hν
  simp only [UF, KX]
  rw [show modeF ((vfTest 1 P : testFn) : ℂ → ℂ) k
      = fun z : ℝ => (Complex.I * (sgnK k : ℂ)) * ((z : ℂ) * modeF P k z) from funext (modeF_vfX P hk),
    klT_const_mul, hν]

/-! ### Piece D1: the conjugated kernels in Schur form; Fubini on a fiber -/

lemma gK_neg (τ x : ℝ) : gK τ (-x) = gK τ x := by
  unfold gK; rw [abs_neg, show Real.pi * (-x / 2) = -(Real.pi * (x / 2)) by ring, Real.cosh_neg]

/-- `√(w w') e^{a Λ(ν)} M₁ e^{-b Λ(ν')} ≤ g_τ(ν - ν')/(e(b - a))` for `0 ≤ a ≤ τ`, `a < b`. -/
lemma kernel_bound_exp {τ a b ν ν' : ℝ} (ha : 0 ≤ a) (haτ : a ≤ τ) (hab : a < b) (hν : 0 < ν) (hν' : 0 < ν') :
    Real.sqrt (klW ν) * Real.sqrt (klW ν') * |Real.exp (a * LamK ν) * kerM1 ν ν' * Real.exp (-(b * LamK ν'))|
      ≤ 1 / (Real.exp 1 * (b - a)) * gK τ (ν - ν') := by
  have hk := kernel_bound (τ := τ) ha haτ hν.le hν'.le
  have hL := LamK_pos ν'
  have hγ : 0 < b - a := by linarith
  have hm := mul_exp_neg_le_inv hγ hL.le
  rw [abs_of_pos (by have := kerM1_pos ν ν'; positivity)]
  have e : Real.sqrt (klW ν) * Real.sqrt (klW ν') * (Real.exp (a * LamK ν) * kerM1 ν ν' * Real.exp (-(b * LamK ν')))
      = (Real.sqrt (klW ν) * Real.sqrt (klW ν') * kerM1 ν ν' * Real.exp (a * (LamK ν - LamK ν')) / LamK ν')
        * (LamK ν' * Real.exp (-((b - a) * LamK ν'))) := by
    have : Real.exp (a * LamK ν) * Real.exp (-(b * LamK ν'))
        = Real.exp (a * (LamK ν - LamK ν')) * Real.exp (-((b - a) * LamK ν')) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    calc Real.sqrt (klW ν) * Real.sqrt (klW ν') * (Real.exp (a * LamK ν) * kerM1 ν ν' * Real.exp (-(b * LamK ν')))
        = Real.sqrt (klW ν) * Real.sqrt (klW ν') * kerM1 ν ν' *
            (Real.exp (a * LamK ν) * Real.exp (-(b * LamK ν'))) := by ring
      _ = Real.sqrt (klW ν) * Real.sqrt (klW ν') * kerM1 ν ν' *
            (Real.exp (a * (LamK ν - LamK ν')) * Real.exp (-((b - a) * LamK ν'))) := by rw [this]
      _ = _ := by field_simp
  rw [e, mul_comm (1 / (Real.exp 1 * (b - a)))]
  exact mul_le_mul hk hm (by positivity) (gK_nonneg _ _)

/-- `√(w w') M₁ e^{-b Λ(ν)} ≤ g_0(ν - ν')/(e b)` (decay in the first variable). -/
lemma kernel_bound_exp_left {b ν ν' : ℝ} (hb : 0 < b) (hν : 0 < ν) (hν' : 0 < ν') :
    Real.sqrt (klW ν) * Real.sqrt (klW ν') * |kerM1 ν ν' * Real.exp (-(b * LamK ν))|
      ≤ 1 / Real.exp 1 / b * gK 0 (ν - ν') := by
  have h := kernel_bound_exp (τ := 0) (a := 0) (b := b) le_rfl le_rfl hb hν' hν
  rw [zero_mul, Real.exp_zero, one_mul, kerM1_symm, sub_zero, ← gK_neg, neg_sub] at h
  rw [mul_comm (Real.sqrt (klW ν))]
  calc Real.sqrt (klW ν') * Real.sqrt (klW ν) * |kerM1 ν ν' * Real.exp (-(b * LamK ν))|
      ≤ 1 / (Real.exp 1 * b) * gK 0 (ν - ν') := h
    _ = 1 / Real.exp 1 / b * gK 0 (ν - ν') := by rw [div_div]

lemma ae_restrict_of_ae_wNu {P : ℝ → Prop} (h : ∀ᵐ ν ∂wNu, P ν) :
    ∀ᵐ ν ∂(volume.restrict (Ioi (0 : ℝ))), P ν := by
  have hac : volume.restrict (Ioi (0 : ℝ)) ≪ wNu := by
    unfold wNu
    refine withDensity_absolutelyContinuous' measurable_klW_dens.aemeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with ν hν
    exact (ENNReal.ofReal_pos.2 (klW_pos hν)).ne'
  exact hac.ae_le h

lemma integral_wNu_eq {F : ℝ → ℂ} : ∫ ν, F ν ∂wNu = ∫ ν in Ioi 0, (klW ν : ℂ) * F ν := by
  rw [wNu, integral_withDensity_eq_integral_toReal_smul measurable_klW_dens
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine setIntegral_congr_fun measurableSet_Ioi (fun ν hν => ?_)
  rw [ENNReal.toReal_ofReal (klW_nonneg (le_of_lt hν)), Complex.real_smul]

/-- **Fubini on a fiber**: `∫ conj(K₁A) B dw = ∫ conj(A) K₁B dw` when `|B| ≤ e^{-bΛ}|C|`, `A, C ∈ L²(w)`. -/
theorem fiber_fubini {A B C : ℝ → ℂ} {b : ℝ} (hb : 0 < b) (hA : Measurable A) (hB : Measurable B)
    (hC : Measurable C) (hA2 : ∫⁻ ν, ‖A ν‖ₑ ^ 2 ∂wNu < ⊤) (hC2 : ∫⁻ ν, ‖C ν‖ₑ ^ 2 ∂wNu < ⊤)
    (hBC : ∀ᵐ ν ∂(volume.restrict (Ioi (0 : ℝ))), ‖B ν‖ ≤ Real.exp (-(b * LamK ν)) * ‖C ν‖) :
    ∫ ν, (starRingEnd ℂ) (K1op A ν) * B ν ∂wNu = ∫ ν, (starRingEnd ℂ) (A ν) * K1op B ν ∂wNu := by
  set μz : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  set H : ℝ × ℝ → ℂ := fun q => (klW q.1 : ℂ) * ((klW q.2 : ℂ) * (kerM1 q.1 q.2 : ℂ)) *
    ((starRingEnd ℂ) (A q.2) * B q.1)
  have hHm : AEStronglyMeasurable H (μz.prod μz) := by
    have m1 : Measurable fun q : ℝ × ℝ => klW q.1 := (continuous_klW.comp continuous_fst).measurable
    have m2 : Measurable fun q : ℝ × ℝ => klW q.2 := (continuous_klW.comp continuous_snd).measurable
    have m3 : Measurable fun q : ℝ × ℝ => kerM1 q.1 q.2 := continuous_M1.measurable
    exact ((Complex.measurable_ofReal.comp m1).mul ((Complex.measurable_ofReal.comp m2).mul
      (Complex.measurable_ofReal.comp m3))).mul ((Complex.continuous_conj.measurable.comp (hA.comp measurable_snd)).mul
        (hB.comp measurable_fst)) |>.aestronglyMeasurable
  -- finiteness from the bilinear Schur bound with `κ₃ = M₁ e^{-bΛ(ν)}`
  have hbil := kerOp_bilin (κ := fun ν ν' => kerM1 ν ν' * Real.exp (-(b * LamK ν))) (continuous_gK 0).measurable
    (by positivity : (0 : ℝ) ≤ 1 / Real.exp 1 / b)
    (fun ν ν' hν hν' => kernel_bound_exp_left hb hν hν') hA hC
  have hgfin : ∫⁻ x, ENNReal.ofReal (gK 0 x) < ⊤ := (integrable_gK (by positivity)).lintegral_lt_top
  have hfin : ∫⁻ ν in Ioi 0, ∫⁻ ν' in Ioi 0, ENNReal.ofReal (klW ν) * (ENNReal.ofReal (klW ν') *
      ENNReal.ofReal |kerM1 ν ν' * Real.exp (-(b * LamK ν))|) * (‖A ν'‖ₑ * ‖C ν‖ₑ) < ⊤ := by
    have hR : (ENNReal.ofReal (1 / Real.exp 1 / b) * ∫⁻ x, ENNReal.ofReal (gK 0 x)) ^ 2 *
        (∫⁻ ν, ‖C ν‖ₑ ^ 2 ∂wNu) * ∫⁻ ν, ‖A ν‖ₑ ^ 2 ∂wNu < ⊤ :=
      ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.pow_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hgfin)) hC2) hA2
    have h2 := lt_of_le_of_lt hbil hR
    by_contra hc
    rw [not_lt, top_le_iff] at hc
    rw [hc] at h2
    simp at h2
  have hHi : Integrable H (μz.prod μz) := by
    refine ⟨hHm, ?_⟩
    rw [HasFiniteIntegral, lintegral_prod _ hHm.enorm]
    refine lt_of_le_of_lt ?_ hfin
    refine lintegral_mono_ae ?_
    filter_upwards [hBC, ae_restrict_mem measurableSet_Ioi] with ν hBν hν
    have hν0 : (0 : ℝ) < ν := hν
    refine setLIntegral_mono' measurableSet_Ioi (fun ν' hν' => ?_)
    have hν'0 : (0 : ℝ) < ν' := hν'
    have hw := klW_nonneg hν0.le
    have hw' := klW_nonneg hν'0.le
    have hE := Real.exp_pos (-(b * LamK ν))
    have hk := kerM1_pos ν ν'
    have eR : ∀ r : ℝ, 0 ≤ r → ‖((r : ℝ) : ℂ)‖ₑ = ENNReal.ofReal r := fun r hr => by
      rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
    have hBe : ‖B ν‖ₑ ≤ ENNReal.ofReal (Real.exp (-(b * LamK ν))) * ‖C ν‖ₑ := by
      rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul hE.le]
      exact ENNReal.ofReal_le_ofReal hBν
    simp only [H, enorm_mul, eR _ hw, eR _ hw', eR _ hk.le, RCLike.enorm_conj]
    rw [abs_of_pos (mul_pos hk hE), ENNReal.ofReal_mul hk.le]
    calc ENNReal.ofReal (klW ν) * (ENNReal.ofReal (klW ν') * ENNReal.ofReal (kerM1 ν ν')) * (‖A ν'‖ₑ * ‖B ν‖ₑ)
        ≤ ENNReal.ofReal (klW ν) * (ENNReal.ofReal (klW ν') * ENNReal.ofReal (kerM1 ν ν')) *
            (‖A ν'‖ₑ * (ENNReal.ofReal (Real.exp (-(b * LamK ν))) * ‖C ν‖ₑ)) := by gcongr
      _ = _ := by ring
  have e1 := integral_prod H hHi
  have e2 := integral_prod_symm H hHi
  have hL : ∫ ν, (starRingEnd ℂ) (K1op A ν) * B ν ∂wNu = ∫ ν, ∫ ν', H (ν, ν') ∂μz ∂μz := by
    rw [integral_wNu_eq]
    refine integral_congr_ae (Eventually.of_forall fun ν => ?_)
    simp only [H, K1op]
    rw [← integral_conj, ← MeasureTheory.integral_mul_const, ← MeasureTheory.integral_const_mul]
    congr 1; funext ν'
    simp only [map_mul, Complex.conj_ofReal]; ring
  have hR : ∫ ν, (starRingEnd ℂ) (A ν) * K1op B ν ∂wNu = ∫ ν', ∫ ν, H (ν, ν') ∂μz ∂μz := by
    rw [integral_wNu_eq]
    refine integral_congr_ae (Eventually.of_forall fun ν' => ?_)
    simp only [H, K1op]
    rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul]
    congr 1; funext ν
    rw [kerM1_symm ν' ν]; ring
  rw [hL, hR, ← e1, e2]

/-! ### Piece D2: `klU (X e^{-α'Λ} v) = K_X (klU e^{-α'Λ} v)` -/

lemma abs_sgnK_le (k : ℝ) : |sgnK k| ≤ 1 := by
  by_cases hk : k = 0
  · simp [sgnK, hk]
  · rw [abs_sgnK hk]

lemma memLp_of_lintegral_sq_lt_top {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℂ}
    (hf : AEStronglyMeasurable f μ) (h : ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ < ⊤) : MemLp f 2 μ := by
  refine (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top hf).2 ?_
  have e : ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ := by
    congr 1; funext x; exact ENNReal.rpow_two _
  rw [ENNReal.toReal_ofNat, e]; exact h

lemma lintegral_enorm_sq_eq {α : Type*} [MeasurableSpace α] {μ : Measure α} (g : Lp ℂ 2 μ) :
    ∫⁻ x, ‖(g : α → ℂ) x‖ₑ ^ 2 ∂μ = ENNReal.ofReal (‖g‖ ^ 2) := by
  have h := norm_toLp_sq (Lp.memLp g)
  rw [Lp.toLp_coeFn] at h
  have hfin := lintegral_enorm_sq_lt_top g
  have e : ∫⁻ x, ‖(g : α → ℂ) x‖ₑ ^ (2 : ℝ) ∂μ = ∫⁻ x, ‖(g : α → ℂ) x‖ₑ ^ 2 ∂μ := by
    simp only [← ENNReal.rpow_natCast]; norm_num
  rw [h, e, ENNReal.ofReal_toReal hfin.ne]

/-- The fiber identity behind `K1op` of `e^{-bΛ} V`. -/
lemma K1op_eq_kerOp {G V : ℝ → ℂ} {b : ℝ}
    (h : ∀ᵐ ν ∂wNu, G ν = ((Real.exp (-(b * LamK ν)) : ℝ) : ℂ) * V ν) (ν : ℝ) :
    K1op G ν = kerOp (fun ν ν' => Real.exp (0 * LamK ν) * kerM1 ν ν' * Real.exp (-(b * LamK ν'))) V ν := by
  unfold K1op kerOp
  refine setIntegral_congr_ae measurableSet_Ioi ?_
  have h' := (ae_restrict_iff' measurableSet_Ioi).1 (ae_restrict_of_ae_wNu h)
  filter_upwards [h'] with ν' hν' hmem
  rw [hν' hmem]; push_cast; rw [zero_mul, Complex.exp_zero]; ring

local notation "L2H'" => Lp ℂ 2 (volume : Measure UpperHalfPlane)

/-- The Schur constant for `κ₁ = M₁ e^{-bΛ(ν')}`. -/
noncomputable def cstX (b : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal (1 / (Real.exp 1 * (b - 0))) * ∫⁻ x, ENNReal.ofReal (gK 0 x)) ^ 2

lemma cstX_lt_top (b : ℝ) : cstX b < ⊤ :=
  ENNReal.pow_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (integrable_gK (by positivity)).lintegral_lt_top)

/-- Fiber bound: `∫ w |K_X G(k, ·)|² ≤ c ∫ w |V(k, ·)|²` when `G(k, ·) = e^{-bΛ} V(k, ·)`. -/
lemma fiber_KX_bound {G V : ℝ × ℝ → ℂ} (hGm : StronglyMeasurable G) (hVm : StronglyMeasurable V)
    {b : ℝ} (hb : 0 < b) {k : ℝ}
    (hk : ∀ᵐ ν ∂wNu, G (k, ν) = ((Real.exp (-(b * LamK ν)) : ℝ) : ℂ) * V (k, ν)) :
    ∫⁻ ν, ‖KX G (k, ν)‖ₑ ^ 2 ∂wNu ≤ cstX b * ∫⁻ ν, ‖V (k, ν)‖ₑ ^ 2 ∂wNu := by
  have hVk : Measurable fun ν' => V (k, ν') := hVm.measurable.comp (measurable_prodMk_left (x := k))
  have hB := kerOp_bound (κ := fun ν ν' => Real.exp (0 * LamK ν) * kerM1 ν ν' * Real.exp (-(b * LamK ν')))
    (a := fun ν' => V (k, ν')) (continuous_gK 0).measurable (by positivity)
    (fun ν ν' hν hν' => kernel_bound_exp (τ := 0) le_rfl le_rfl hb hν hν') hVk
  have hKXm : Measurable fun ν => ‖KX G (k, ν)‖ₑ ^ 2 :=
    ((stronglyMeasurable_KX hGm).measurable.comp (measurable_prodMk_left (x := k))).enorm.pow_const (2 : ℕ)
  rw [lintegral_wNu_eq hKXm]
  refine le_trans (setLIntegral_mono' measurableSet_Ioi (fun ν _ => ?_)) hB
  have hc : ‖Complex.I * (sgnK k : ℂ)‖ₑ ≤ 1 := by
    rw [← ofReal_norm_eq_enorm, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    exact ENNReal.ofReal_le_one.2 (abs_sgnK_le k)
  have e : KX G (k, ν) = (Complex.I * (sgnK k : ℂ)) *
      kerOp (fun ν ν' => Real.exp (0 * LamK ν) * kerM1 ν ν' * Real.exp (-(b * LamK ν'))) (fun ν' => V (k, ν')) ν := by
    unfold KX; rw [K1op_eq_kerOp hk ν]
  rw [e, enorm_mul, mul_pow]
  gcongr _ * ?_
  calc ‖Complex.I * (sgnK k : ℂ)‖ₑ ^ 2 *
        ‖kerOp (fun ν ν' => Real.exp (0 * LamK ν) * kerM1 ν ν' * Real.exp (-(b * LamK ν'))) (fun ν' => V (k, ν')) ν‖ₑ ^ 2
      ≤ 1 ^ 2 * ‖kerOp (fun ν ν' => Real.exp (0 * LamK ν) * kerM1 ν ν' * Real.exp (-(b * LamK ν')))
          (fun ν' => V (k, ν')) ν‖ₑ ^ 2 := by gcongr
    _ = _ := by rw [one_pow, one_mul]

/-- `K_X G ∈ L²` when `G = e^{-bΛ} V`, `V ∈ L²`. -/
lemma memLp_KX {G V : ℝ × ℝ → ℂ} (hGm : StronglyMeasurable G) (hVm : StronglyMeasurable V)
    {b : ℝ} (hb : 0 < b) (hGV : G =ᵐ[muU] fun p => ((Real.exp (-(b * LamK p.2)) : ℝ) : ℂ) * V p)
    (hVfin : ∫⁻ p, ‖V p‖ₑ ^ 2 ∂muU < ⊤) : MemLp (KX G) 2 muU := by
  have hGV' : ∀ᵐ p ∂((volume : Measure ℝ).prod wNu),
      G p = ((Real.exp (-(b * LamK p.2)) : ℝ) : ℂ) * V p := hGV
  have hfib1 : ∀ᵐ k, ∀ᵐ ν ∂wNu, G (k, ν) = ((Real.exp (-(b * LamK ν)) : ℝ) : ℂ) * V (k, ν) :=
    Measure.ae_ae_of_ae_prod hGV'
  have hVmeas : Measurable fun p : ℝ × ℝ => ‖V p‖ₑ ^ 2 := hVm.measurable.enorm.pow_const (2 : ℕ)
  have eV : ∫⁻ p, ‖V p‖ₑ ^ 2 ∂muU = ∫⁻ k, ∫⁻ ν, ‖V (k, ν)‖ₑ ^ 2 ∂wNu :=
    lintegral_prod (μ := (volume : Measure ℝ)) (ν := wNu) _ hVmeas.aemeasurable
  have hKXm2 : StronglyMeasurable (KX G) := stronglyMeasurable_KX hGm
  refine memLp_of_lintegral_sq_lt_top hKXm2.aestronglyMeasurable ?_
  have hKXm3 : Measurable fun p : ℝ × ℝ => ‖KX G p‖ₑ ^ 2 := hKXm2.measurable.enorm.pow_const (2 : ℕ)
  have e : ∫⁻ p, ‖KX G p‖ₑ ^ 2 ∂muU = ∫⁻ k, ∫⁻ ν, ‖KX G (k, ν)‖ₑ ^ 2 ∂wNu :=
    lintegral_prod (μ := (volume : Measure ℝ)) (ν := wNu) _ hKXm3.aemeasurable
  rw [e]
  calc ∫⁻ k, ∫⁻ ν, ‖KX G (k, ν)‖ₑ ^ 2 ∂wNu ≤ ∫⁻ k, cstX b * ∫⁻ ν, ‖V (k, ν)‖ₑ ^ 2 ∂wNu :=
        lintegral_mono_ae (hfib1.mono fun k hk => fiber_KX_bound hGm hVm hb hk)
    _ = cstX b * ∫⁻ p, ‖V p‖ₑ ^ 2 ∂muU := by rw [lintegral_const_mul _ hVmeas.lintegral_prod_right', eV]
    _ < ⊤ := ENNReal.mul_lt_top (cstX_lt_top b) hVfin

lemma conj_I_mul_real (r : ℝ) : (starRingEnd ℂ) (Complex.I * (r : ℂ)) = -(Complex.I * (r : ℂ)) := by
  rw [map_mul, Complex.conj_I, Complex.conj_ofReal]; ring

lemma ae_fiber_lintegral_lt_top {V : ℝ × ℝ → ℂ} (hVm : StronglyMeasurable V)
    (hVfin : ∫⁻ p, ‖V p‖ₑ ^ 2 ∂muU < ⊤) : ∀ᵐ k, ∫⁻ ν, ‖V (k, ν)‖ₑ ^ 2 ∂wNu < ⊤ := by
  have hVmeas : Measurable fun p : ℝ × ℝ => ‖V p‖ₑ ^ 2 := hVm.measurable.enorm.pow_const (2 : ℕ)
  have eV : ∫⁻ p, ‖V p‖ₑ ^ 2 ∂muU = ∫⁻ k, ∫⁻ ν, ‖V (k, ν)‖ₑ ^ 2 ∂wNu :=
    lintegral_prod (μ := (volume : Measure ℝ)) (ν := wNu) _ hVmeas.aemeasurable
  exact ae_lt_top' hVmeas.lintegral_prod_right'.aemeasurable (by rw [← eV]; exact hVfin.ne)

/-- **`K_X` is skew on the pairs used**: `-⟨K_X A, G⟩ = ⟨A, K_X G⟩` when `G = e^{-bΛ}V`. -/
theorem integral_conj_KX_eq {A G V : ℝ × ℝ → ℂ} (hAm : StronglyMeasurable A) (hGm : StronglyMeasurable G)
    (hVm : StronglyMeasurable V) {b : ℝ} (hb : 0 < b)
    (hGV : G =ᵐ[muU] fun p => ((Real.exp (-(b * LamK p.2)) : ℝ) : ℂ) * V p)
    (hA : MemLp A 2 muU) (hG : MemLp G 2 muU) (hKXA : MemLp (KX A) 2 muU) (hKXG : MemLp (KX G) 2 muU)
    (hAfin : ∫⁻ p, ‖A p‖ₑ ^ 2 ∂muU < ⊤) (hVfin : ∫⁻ p, ‖V p‖ₑ ^ 2 ∂muU < ⊤) :
    -∫ p, (starRingEnd ℂ) (KX A p) * G p ∂muU = ∫ p, (starRingEnd ℂ) (A p) * KX G p ∂muU := by
  have I1 : Integrable (fun p => -((starRingEnd ℂ) (KX A p) * G p)) ((volume : Measure ℝ).prod wNu) :=
    (hKXA.star.integrable_mul hG).neg
  have I2 : Integrable (fun p => (starRingEnd ℂ) (A p) * KX G p) ((volume : Measure ℝ).prod wNu) :=
    hA.star.integrable_mul hKXG
  rw [← integral_neg]
  have e1 : ∫ p, -((starRingEnd ℂ) (KX A p) * G p) ∂muU
      = ∫ k, ∫ ν, -((starRingEnd ℂ) (KX A (k, ν)) * G (k, ν)) ∂wNu := integral_prod _ I1
  have e2 : ∫ p, (starRingEnd ℂ) (A p) * KX G p ∂muU
      = ∫ k, ∫ ν, (starRingEnd ℂ) (A (k, ν)) * KX G (k, ν) ∂wNu := integral_prod _ I2
  rw [e1, e2]
  have hGV' : ∀ᵐ p ∂((volume : Measure ℝ).prod wNu),
      G p = ((Real.exp (-(b * LamK p.2)) : ℝ) : ℂ) * V p := hGV
  have hfib1 : ∀ᵐ k, ∀ᵐ ν ∂wNu, G (k, ν) = ((Real.exp (-(b * LamK ν)) : ℝ) : ℂ) * V (k, ν) :=
    Measure.ae_ae_of_ae_prod hGV'
  refine integral_congr_ae ?_
  filter_upwards [hfib1, ae_fiber_lintegral_lt_top hAm hAfin, ae_fiber_lintegral_lt_top hVm hVfin]
    with k hk hAk hVk
  have hBC : ∀ᵐ ν ∂(volume.restrict (Ioi (0 : ℝ))), ‖G (k, ν)‖ ≤ Real.exp (-(b * LamK ν)) * ‖V (k, ν)‖ := by
    filter_upwards [ae_restrict_of_ae_wNu hk] with ν hν
    rw [hν, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hF := fiber_fubini hb (hAm.measurable.comp (measurable_prodMk_left (x := k)))
    (hGm.measurable.comp (measurable_prodMk_left (x := k))) (hVm.measurable.comp (measurable_prodMk_left (x := k)))
    hAk hVk hBC
  have hconj : ∀ ν, (starRingEnd ℂ) (KX A (k, ν))
      = -(Complex.I * (sgnK k : ℂ)) * (starRingEnd ℂ) (K1op (fun ν' => A (k, ν')) ν) := by
    intro ν; show (starRingEnd ℂ) ((Complex.I * (sgnK k : ℂ)) * K1op (fun ν' => A (k, ν')) ν) = _
    rw [map_mul, conj_I_mul_real]
  have hKG : ∀ ν, KX G (k, ν) = Complex.I * (sgnK k : ℂ) * K1op (fun ν' => G (k, ν')) ν := fun ν => rfl
  simp_rw [hconj, hKG]
  have l1 : ∫ ν, -(-(Complex.I * (sgnK k : ℂ)) * (starRingEnd ℂ) (K1op (fun ν' => A (k, ν')) ν) * G (k, ν)) ∂wNu
      = (Complex.I * (sgnK k : ℂ)) * ∫ ν, (starRingEnd ℂ) (K1op (fun ν' => A (k, ν')) ν) * G (k, ν) ∂wNu := by
    rw [← MeasureTheory.integral_const_mul]; congr 1; funext ν; ring
  have l2 : ∫ ν, (starRingEnd ℂ) (A (k, ν)) * (Complex.I * (sgnK k : ℂ) * K1op (fun ν' => G (k, ν')) ν) ∂wNu
      = (Complex.I * (sgnK k : ℂ)) * ∫ ν, (starRingEnd ℂ) (A (k, ν)) * K1op (fun ν' => G (k, ν')) ν ∂wNu := by
    rw [← MeasureTheory.integral_const_mul]; congr 1; funext ν; ring
  have hF' : ∫ ν, (starRingEnd ℂ) (K1op (fun ν' => A (k, ν')) ν) * G (k, ν) ∂wNu
      = ∫ ν, (starRingEnd ℂ) (A (k, ν)) * K1op (fun ν' => G (k, ν')) ν ∂wNu := hF
  rw [l1, l2, hF']

/-- **`X e^{-α'Λ} v` in the KL picture**: `klU (domX (e^{-α'Λ} v)) = K_X (klU (e^{-α'Λ} v))` a.e. -/
theorem klU_domX_expDom {α' : ℝ} (hα' : 0 < α') (v : L2H') :
    ((klU (domX (expDom α' hα' v)) : Lp ℂ 2 muU) : ℝ × ℝ → ℂ) =ᵐ[muU]
      KX ((klU ((expDom α' hα' v : negLapH.domain) : L2H') : Lp ℂ 2 muU) : ℝ × ℝ → ℂ) := by
  have hGV := klU_expCut hα' v
  have hKXL2 := memLp_KX (Lp.stronglyMeasurable (klU ((expCut α' hα').J v)))
    (Lp.stronglyMeasurable (klU v)) hα' hGV (lintegral_enorm_sq_lt_top _)
  obtain ⟨y, hy⟩ := klU_surjective (hKXL2.toLp _)
  have hpair : ∀ P : testFn, inner ℂ (toL2 P) (domX (expDom α' hα' v)) = inner ℂ (toL2 P) y := by
    intro P
    have h1 := inner_X_dom P (expDom α' hα' v)
    have h2 : inner ℂ (toL2 P) (domX (expDom α' hα' v))
        = -inner ℂ (klU (toL2 (vfTest 1 P))) (klU ((expCut α' hα').J v)) := by
      rw [← klUi_apply, ← klUi_apply, klUi.inner_map_map]
      rw [show ((expDom α' hα' v : negLapH.domain) : L2H') = (expCut α' hα').J v from rfl] at h1
      rw [h1, neg_neg]
    have h3 : inner ℂ (toL2 P) y = inner ℂ (klU (toL2 P)) (hKXL2.toLp _) := by
      rw [← hy, ← klUi_apply, ← klUi_apply, klUi.inner_map_map]
    rw [h2, h3, klU_toL2, klU_toL2, L2.inner_def, L2.inner_def]
    have hXP : MemLp (KX (UF P)) 2 muU := (memLp_UF (vfTest 1 P)).ae_eq (UF_vfX_ae P)
    have eL : ∫ p, inner ℂ ((UFL (vfTest 1 P) : Lp ℂ 2 muU) p) ((klU ((expCut α' hα').J v) : Lp ℂ 2 muU) p) ∂muU
        = ∫ p, (starRingEnd ℂ) (KX (UF P) p) * (klU ((expCut α' hα').J v) : ℝ × ℝ → ℂ) p ∂muU := by
      refine integral_congr_ae ?_
      filter_upwards [(memLp_UF (vfTest 1 P)).coeFn_toLp, UF_vfX_ae P] with p h1 h2
      rw [UFL, h1, h2, RCLike.inner_apply']
    have eR : ∫ p, inner ℂ ((UFL P : Lp ℂ 2 muU) p) ((hKXL2.toLp _ : Lp ℂ 2 muU) p) ∂muU
        = ∫ p, (starRingEnd ℂ) (UF P p) * KX ((klU ((expCut α' hα').J v) : ℝ × ℝ → ℂ)) p ∂muU := by
      refine integral_congr_ae ?_
      filter_upwards [(memLp_UF P).coeFn_toLp, hKXL2.coeFn_toLp] with p h1 h2
      rw [UFL, h1, h2, RCLike.inner_apply']
    have hUfin : ∫⁻ p, ‖UF P p‖ₑ ^ 2 ∂muU < ⊤ := by
      have h0 := lintegral_enorm_sq_lt_top (UFL P)
      have e0 : ∫⁻ p, ‖(UFL P : ℝ × ℝ → ℂ) p‖ₑ ^ 2 ∂muU = ∫⁻ p, ‖UF P p‖ₑ ^ 2 ∂muU :=
        lintegral_congr_ae ((memLp_UF P).coeFn_toLp.mono fun p hp => congrArg (fun z : ℂ => ‖z‖ₑ ^ 2) hp)
      rwa [e0] at h0
    rw [eL, eR]
    exact integral_conj_KX_eq (stronglyMeasurable_UF P) (Lp.stronglyMeasurable _) (Lp.stronglyMeasurable (klU v))
      hα' hGV (memLp_UF P) (Lp.memLp _) hXP hKXL2 hUfin (lintegral_enorm_sq_lt_top _)
  have hdy : domX (expDom α' hα' v) = y := by
    refine ext_inner_left ℂ fun w => ?_
    refine DenseRange.induction_on denseRange_toL2 w ?_ (fun P => hpair P)
    exact isClosed_eq (continuous_inner.comp (continuous_id.prodMk continuous_const))
      (continuous_inner.comp (continuous_id.prodMk continuous_const))
  rw [hdy, hy]
  exact hKXL2.coeFn_toLp

/-! ### Piece E: Lemma FC for `Z = X` -/

/-- The conjugated kernel `e^{aΛ(ν)} M₁(ν, ν') e^{-bΛ(ν')}`. -/
noncomputable def kapX (a b ν ν' : ℝ) : ℝ := Real.exp (a * LamK ν) * kerM1 ν ν' * Real.exp (-(b * LamK ν'))

/-- `e^{aΛ(ν)} K₁(e^{-bΛ}V)(ν) = T_κ V(ν)`. -/
lemma exp_mul_K1op_eq_kerOp {G V : ℝ → ℂ} {a b : ℝ}
    (h : ∀ᵐ ν ∂wNu, G ν = ((Real.exp (-(b * LamK ν)) : ℝ) : ℂ) * V ν) (ν : ℝ) :
    ((Real.exp (a * LamK ν) : ℝ) : ℂ) * K1op G ν = kerOp (kapX a b) V ν := by
  unfold K1op kerOp kapX
  rw [← MeasureTheory.integral_const_mul]
  refine setIntegral_congr_ae measurableSet_Ioi ?_
  have h' := (ae_restrict_iff' measurableSet_Ioi).1 (ae_restrict_of_ae_wNu h)
  filter_upwards [h'] with ν' hν' hmem
  rw [hν' hmem]; push_cast; ring

/-- `e^{aΛ} K_X G`. -/
noncomputable def expKX (a : ℝ) (G : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  ((Real.exp (a * LamK p.2) : ℝ) : ℂ) * KX G p

lemma stronglyMeasurable_expKX (a : ℝ) {G : ℝ × ℝ → ℂ} (hG : StronglyMeasurable G) :
    StronglyMeasurable (expKX a G) :=
  ((Complex.continuous_ofReal.comp (Real.continuous_exp.comp
    (continuous_const.mul (continuous_LamK.comp continuous_snd)))).stronglyMeasurable).mul
      (stronglyMeasurable_KX hG)

/-- **The `L²` bound of `e^{aΛ} K_X e^{-bΛ}`** with the paper's constant. -/
theorem lintegral_expKX_le {G V : ℝ × ℝ → ℂ} (hGm : StronglyMeasurable G) (hVm : StronglyMeasurable V)
    {τ a b : ℝ} (ha : 0 ≤ a) (haτ : a ≤ τ) (hab : a < b)
    (hGV : G =ᵐ[muU] fun p => ((Real.exp (-(b * LamK p.2)) : ℝ) : ℂ) * V p) :
    ∫⁻ p, ‖expKX a G p‖ₑ ^ 2 ∂muU
      ≤ (ENNReal.ofReal (1 / (Real.exp 1 * (b - a))) * ∫⁻ x, ENNReal.ofReal (gK τ x)) ^ 2 * ∫⁻ p, ‖V p‖ₑ ^ 2 ∂muU := by
  have hGV' : ∀ᵐ p ∂((volume : Measure ℝ).prod wNu),
      G p = ((Real.exp (-(b * LamK p.2)) : ℝ) : ℂ) * V p := hGV
  have hfib1 : ∀ᵐ k, ∀ᵐ ν ∂wNu, G (k, ν) = ((Real.exp (-(b * LamK ν)) : ℝ) : ℂ) * V (k, ν) :=
    Measure.ae_ae_of_ae_prod hGV'
  have hVmeas : Measurable fun p : ℝ × ℝ => ‖V p‖ₑ ^ 2 := hVm.measurable.enorm.pow_const (2 : ℕ)
  have eV : ∫⁻ p, ‖V p‖ₑ ^ 2 ∂muU = ∫⁻ k, ∫⁻ ν, ‖V (k, ν)‖ₑ ^ 2 ∂wNu :=
    lintegral_prod (μ := (volume : Measure ℝ)) (ν := wNu) _ hVmeas.aemeasurable
  have hEm : StronglyMeasurable (expKX a G) := stronglyMeasurable_expKX a hGm
  have hEm3 : Measurable fun p : ℝ × ℝ => ‖expKX a G p‖ₑ ^ 2 := hEm.measurable.enorm.pow_const (2 : ℕ)
  have e : ∫⁻ p, ‖expKX a G p‖ₑ ^ 2 ∂muU = ∫⁻ k, ∫⁻ ν, ‖expKX a G (k, ν)‖ₑ ^ 2 ∂wNu :=
    lintegral_prod (μ := (volume : Measure ℝ)) (ν := wNu) _ hEm3.aemeasurable
  rw [e, eV, ← lintegral_const_mul _ hVmeas.lintegral_prod_right']
  refine lintegral_mono_ae (hfib1.mono fun k hk => ?_)
  have hVk : Measurable fun ν' => V (k, ν') := hVm.measurable.comp (measurable_prodMk_left (x := k))
  have hγ : 0 < b - a := by linarith
  have hB := kerOp_bound (κ := kapX a b) (a := fun ν' => V (k, ν')) (continuous_gK τ).measurable
    (by positivity : (0 : ℝ) ≤ 1 / (Real.exp 1 * (b - a)))
    (fun ν ν' hν hν' => kernel_bound_exp (τ := τ) ha haτ hab hν hν') hVk
  have hm : Measurable fun ν => ‖expKX a G (k, ν)‖ₑ ^ 2 :=
    (hEm.measurable.comp (measurable_prodMk_left (x := k))).enorm.pow_const (2 : ℕ)
  rw [lintegral_wNu_eq hm]
  refine le_trans (setLIntegral_mono' measurableSet_Ioi (fun ν _ => ?_)) hB
  have hc : ‖Complex.I * (sgnK k : ℂ)‖ₑ ≤ 1 := by
    rw [← ofReal_norm_eq_enorm, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    exact ENNReal.ofReal_le_one.2 (abs_sgnK_le k)
  have e' : expKX a G (k, ν) = (Complex.I * (sgnK k : ℂ)) * kerOp (kapX a b) (fun ν' => V (k, ν')) ν := by
    rw [← exp_mul_K1op_eq_kerOp (G := fun ν' => G (k, ν')) (V := fun ν' => V (k, ν')) hk ν]
    show ((Real.exp (a * LamK ν) : ℝ) : ℂ) * ((Complex.I * (sgnK k : ℂ)) * K1op (fun ν' => G (k, ν')) ν) = _
    ring
  rw [e', enorm_mul, mul_pow]
  gcongr _ * ?_
  calc ‖Complex.I * (sgnK k : ℂ)‖ₑ ^ 2 * ‖kerOp (kapX a b) (fun ν' => V (k, ν')) ν‖ₑ ^ 2
      ≤ 1 ^ 2 * ‖kerOp (kapX a b) (fun ν' => V (k, ν')) ν‖ₑ ^ 2 := by gcongr
    _ = _ := by rw [one_pow, one_mul]

/-- **Lemma FC for `Z = X`** (`lem:fc`, all `0 ≤ α'' < α'`, `α'' ≤ τ < π/2`), with the paper's constant:
`X e^{-α'Λ} v ∈ Dom e^{α''Λ}` and `‖e^{α''Λ} X e^{-α'Λ} v‖ ≤ (∫ g_τ)/(e (α' - α'')) ‖v‖`. -/
theorem fc_X {τ α'' α' : ℝ} (hτ : τ < Real.pi / 2) (h0 : 0 ≤ α'') (h12 : α'' < α') (h2τ : α'' ≤ τ) (v : L2H') :
    ∃ h : domX (expDom α' (lt_of_le_of_lt h0 h12) v) ∈ (expLambda α'').domain,
      ‖expLambda α'' ⟨domX (expDom α' (lt_of_le_of_lt h0 h12) v), h⟩‖
        ≤ (∫ x, gK τ x) / (Real.exp 1 * (α' - α'')) * ‖v‖ := by
  have hα' : 0 < α' := lt_of_le_of_lt h0 h12
  set f : ℝ → ℂ := fun s => ((Real.exp (α'' * Real.sqrt s) : ℝ) : ℂ)
  have hf : Measurable f :=
    Complex.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul Real.continuous_sqrt.measurable))
  have hW := klU_domX_expDom hα' v
  have hGV := klU_expCut hα' v
  have hGm : StronglyMeasurable ((klU ((expCut α' hα').J v) : Lp ℂ 2 muU) : ℝ × ℝ → ℂ) := Lp.stronglyMeasurable _
  have hVm : StronglyMeasurable ((klU v : Lp ℂ 2 muU) : ℝ × ℝ → ℂ) := Lp.stronglyMeasurable _
  have hL := lintegral_expKX_le (τ := τ) hGm hVm h0 h2τ h12 hGV
  have hfW : (fun p => f (mKL p) * (klU (domX (expDom α' hα' v)) : ℝ × ℝ → ℂ) p)
      =ᵐ[muU] expKX α'' ((klU ((expCut α' hα').J v) : Lp ℂ 2 muU) : ℝ × ℝ → ℂ) := by
    filter_upwards [hW] with p hp
    rw [hp]; rfl
  set A : ℝ := ∫ x, gK τ x
  have hA0 : 0 ≤ A := integral_nonneg fun x => gK_nonneg τ x
  have hIg : ∫⁻ x, ENNReal.ofReal (gK τ x) = ENNReal.ofReal A :=
    (ofReal_integral_eq_lintegral_ofReal (integrable_gK hτ) (Eventually.of_forall fun x => gK_nonneg τ x)).symm
  have hVn : ∫⁻ p, ‖(klU v : ℝ × ℝ → ℂ) p‖ₑ ^ 2 ∂muU = ENNReal.ofReal (‖v‖ ^ 2) := by
    rw [lintegral_enorm_sq_eq, norm_klU]
  rw [hIg, hVn] at hL
  have hγ : 0 < α' - α'' := by linarith
  set C : ℝ := 1 / (Real.exp 1 * (α' - α''))
  have hC0 : 0 ≤ C := by positivity
  have hEfin : ∫⁻ p, ‖expKX α'' ((klU ((expCut α' hα').J v) : Lp ℂ 2 muU) : ℝ × ℝ → ℂ) p‖ₑ ^ 2 ∂muU < ⊤ :=
    lt_of_le_of_lt hL (ENNReal.mul_lt_top (ENNReal.pow_lt_top
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)) ENNReal.ofReal_lt_top)
  have hmem : MemLp (fun p => f (mKL p) * (klU (domX (expDom α' hα' v)) : ℝ × ℝ → ℂ) p) 2 muU :=
    (memLp_of_lintegral_sq_lt_top (stronglyMeasurable_expKX α'' hGm).aestronglyMeasurable hEfin).ae_eq hfW.symm
  have hd : domX (expDom α' hα' v) ∈ (Physicslib4.Spectral.Unbounded.functionalCalculus negLapH_isSelfAdjoint f).domain :=
    (mem_domain_fc_iff hf _).2 hmem
  refine ⟨hd, ?_⟩
  have hn := norm_fc_sq hf ⟨_, hd⟩
  change ‖expLambda α'' ⟨domX (expDom α' hα' v), hd⟩‖ ^ 2 = _ at hn
  set N : ℝ := ‖expLambda α'' ⟨domX (expDom α' hα' v), hd⟩‖
  have hsq : Integrable (fun p => ‖f (mKL p) * (klU (domX (expDom α' hα' v)) : ℝ × ℝ → ℂ) p‖ ^ 2) muU :=
    (memLp_two_iff_integrable_sq_norm hmem.aestronglyMeasurable).1 hmem
  have hN : ENNReal.ofReal (N ^ 2) = ∫⁻ p, ‖expKX α'' ((klU ((expCut α' hα').J v) : Lp ℂ 2 muU) : ℝ × ℝ → ℂ) p‖ₑ ^ 2 ∂muU := by
    have e1 : N ^ 2 = ∫ p, ‖f (mKL p) * (klU (domX (expDom α' hα' v)) : ℝ × ℝ → ℂ) p‖ ^ 2 ∂muU := by
      rw [hn]; congr 1; funext p; rw [norm_mul, mul_pow]
    rw [e1, ofReal_integral_eq_lintegral_ofReal hsq (Eventually.of_forall fun p => sq_nonneg _)]
    refine lintegral_congr_ae ?_
    filter_upwards [hfW] with p hp
    rw [← hp, ← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]
  rw [← hN] at hL
  have hR : (ENNReal.ofReal C * ENNReal.ofReal A) ^ 2 * ENNReal.ofReal (‖v‖ ^ 2)
      = ENNReal.ofReal ((C * A * ‖v‖) ^ 2) := by
    rw [← ENNReal.ofReal_mul hC0, ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1; ring
  rw [hR, ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)] at hL
  have hle : N ≤ C * A * ‖v‖ := abs_le_of_sq_le_sq' hL (by positivity) |>.2
  calc N ≤ C * A * ‖v‖ := hle
    _ = A / (Real.exp 1 * (α' - α'')) * ‖v‖ := by simp only [C]; field_simp

end Qschubert
