import Qschubert.KLPcCWc

/-!
# The critical-weight multiplier theorem, part 4: the Poisson semigroup and powers of the Laplacian

`omC c = e^{ψ/2} (1 + ψ)^c`, `ψ = log X₀`. `poisson_cw`: `‖ω e^{-τΛ} f‖ ≤ K ‖ω f‖`. `lam_cw`: `‖ω Λ e^{-sΛ} f‖ ≤ (K/s) ‖ω f‖`.
`base_vj`: `‖ω (-Δ)^j e^{-σΛ} f‖ ≤ C (C₀/σ)^{2j} (2j)! ‖ω f‖`.
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set Physicslib4.Spectral Physicslib4.Spectral.Unbounded
open scoped ENNReal InnerProductSpace ComplexConjugate UpperHalfPlane

local notation "L2H'" => Lp ℂ 2 (volume : Measure UpperHalfPlane)

/-- The critical weight in the variable `ψ`. -/
noncomputable def omC (c : ℝ) (w : ℂ) : ℝ := Real.exp (psiF w / 2) * (1 + psiF w) ^ c

lemma omC_nonneg (c : ℝ) (z : UpperHalfPlane) : 0 ≤ omC c (z : ℂ) := by
  have h := psiF_nonneg z.im_pos
  unfold omC
  have : 0 < (1 + psiF (z : ℂ)) ^ c := Real.rpow_pos_of_pos (by linarith) _
  positivity

lemma omC_lo {c : ℝ} (hc : 0 ≤ c) (n : ℕ) (z : UpperHalfPlane) (h : z ∈ shell n) :
    Real.exp ((n : ℝ) / 2) * (1 + (n : ℝ)) ^ c ≤ omC c (z : ℂ) := by
  obtain ⟨h1, -⟩ := mem_shell h
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have a1 : Real.exp ((n : ℝ) / 2) ≤ Real.exp (psiF (z : ℂ) / 2) := Real.exp_le_exp.2 (by linarith)
  have a2 : (1 + (n : ℝ)) ^ c ≤ (1 + psiF (z : ℂ)) ^ c := Real.rpow_le_rpow (by linarith) (by linarith) hc
  exact mul_le_mul a1 a2 (Real.rpow_nonneg (by linarith) _) (Real.exp_pos _).le

lemma omC_hi {c : ℝ} (hc : 0 ≤ c) (l : ℕ) (z : UpperHalfPlane) (h : z ∈ shell l) :
    omC c (z : ℂ) ≤ (Real.exp (1 / 2) * (2 : ℝ) ^ c) * Real.exp ((l : ℝ) / 2) * (1 + (l : ℝ)) ^ c := by
  obtain ⟨h1, h2⟩ := mem_shell h
  have hl : (0 : ℝ) ≤ l := Nat.cast_nonneg l
  have hp := psiF_nonneg z.im_pos
  have a1 : Real.exp (psiF (z : ℂ) / 2) ≤ Real.exp (1 / 2) * Real.exp ((l : ℝ) / 2) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  have a2 : (1 + psiF (z : ℂ)) ^ c ≤ (2 : ℝ) ^ c * (1 + (l : ℝ)) ^ c := by
    rw [← Real.mul_rpow (by norm_num) (by linarith)]
    exact Real.rpow_le_rpow (by linarith) (by linarith) hc
  have hp2 : 0 ≤ (1 + psiF (z : ℂ)) ^ c := Real.rpow_nonneg (by linarith) _
  have := mul_le_mul a1 a2 hp2 (by positivity)
  unfold omC
  calc _ ≤ Real.exp (1 / 2) * Real.exp ((l : ℝ) / 2) * ((2 : ℝ) ^ c * (1 + (l : ℝ)) ^ c) := this
    _ = _ := by ring

lemma tF_nonneg {T : ℝ} (hT : 0 ≤ T) : 0 ≤ tF T := by
  unfold tF
  positivity

lemma TailB.mono {g : ℝ → ℝ} {B B' : ℝ} (h : TailB g B) (hB : B ≤ B') : TailB g B' := fun T hT =>
  (h T hT).trans (mul_le_mul_of_nonneg_right hB (tF_nonneg hT))

/-- `(√s)^{2j} e^{-σ√s}` on `[0, ∞)`, zero elsewhere. -/
noncomputable def rW (j : ℕ) (σ s : ℝ) : ℝ := if 0 ≤ s then (√s) ^ (2 * j) * Real.exp (-(σ * √s)) else 0

/-- `√s e^{-a√s}` on `[0, ∞)`, zero elsewhere. -/
noncomputable def rL (a s : ℝ) : ℝ := if 0 ≤ s then √s * Real.exp (-(a * √s)) else 0

lemma measurable_rW (j : ℕ) (σ : ℝ) : Measurable (rW j σ) :=
  Measurable.ite measurableSet_Ici
    ((Real.continuous_sqrt.measurable.pow_const _).mul (Real.measurable_exp.comp (measurable_const.mul Real.continuous_sqrt.measurable).neg))
    measurable_const

lemma measurable_rL (a : ℝ) : Measurable (rL a) :=
  Measurable.ite measurableSet_Ici
    (Real.continuous_sqrt.measurable.mul (Real.measurable_exp.comp (measurable_const.mul Real.continuous_sqrt.measurable).neg))
    measurable_const

/-- `y^m e^{-σ y} ≤ m! / σ^m`. -/
lemma pow_mul_exp_le_fac {σ y : ℝ} (hσ : 0 < σ) (hy : 0 ≤ y) (m : ℕ) : y ^ m * Real.exp (-(σ * y)) ≤ (m.factorial : ℝ) / σ ^ m := by
  have h := Real.pow_div_factorial_le_exp (σ * y) (by positivity) m
  have hf : (0 : ℝ) < m.factorial := by exact_mod_cast m.factorial_pos
  have hE := Real.exp_pos (σ * y)
  have hs : 0 < σ ^ m := by positivity
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ hE hs]
  rw [div_le_iff₀ hf, mul_pow] at h
  linarith

lemma abs_rW_le {j : ℕ} {σ : ℝ} (hσ : 0 < σ) (s : ℝ) : |rW j σ s| ≤ ((2 * j).factorial : ℝ) / σ ^ (2 * j) := by
  have h0 : 0 ≤ ((2 * j).factorial : ℝ) / σ ^ (2 * j) := by positivity
  unfold rW
  split_ifs with hs
  · rw [abs_of_nonneg (by positivity)]
    exact pow_mul_exp_le_fac hσ (Real.sqrt_nonneg _) _
  · simpa using h0

lemma abs_rL_le {a : ℝ} (ha : 0 < a) (s : ℝ) : |rL a s| ≤ 1 / a := by
  have h0 : 0 ≤ 1 / a := by positivity
  unfold rL
  split_ifs with hs
  · rw [abs_of_nonneg (by positivity)]
    have := pow_mul_exp_le_fac ha (Real.sqrt_nonneg s) 1
    simpa using this
  · simpa using h0

/-- The operator symbols. -/
noncomputable def GW (j : ℕ) (σ : ℝ) : ℝ → ℂ := fun s => ((rW j σ s : ℝ) : ℂ)

noncomputable def GLam (a : ℝ) : ℝ → ℂ := fun s => ((rL a s : ℝ) : ℂ)

lemma GW_mem (j : ℕ) {σ : ℝ} (hσ : 0 < σ) : GW j σ ∈ BddMeasurable ℝ := memB_of_abs_le (measurable_rW j σ) (abs_rW_le hσ)

lemma GLam_mem {a : ℝ} (ha : 0 < a) : GLam a ∈ BddMeasurable ℝ := memB_of_abs_le (measurable_rL a) (abs_rL_le ha)

lemma pow_mem_B {G : ℝ → ℂ} (hG : G ∈ BddMeasurable ℝ) (m : ℕ) : G ^ m ∈ BddMeasurable ℝ := by
  induction m with
  | zero =>
    rw [pow_zero]
    exact (mem_bddMeasurable).2 ⟨measurable_one, 1, fun _ => by simp⟩
  | succ m ih =>
    rw [pow_succ]
    exact mul_mem_B ih hG

lemma integrable_of_symbol {g : ℝ → ℝ} (h : Integrable fun r => g r * Real.cos (r * √((1 / 4 : ℝ) - 1 / 4))) : Integrable g := by
  simpa using h

lemma rep_of_real {g : ℝ → ℝ} {G : ℝ → ℂ} {x R : ℝ} (hG : G x = (R : ℂ)) (h : ∫ r, g r * Real.cos (r * √(x - 1 / 4)) = R) :
    ∫ r, (g r : ℂ) * ((Real.cos (r * √(yD x)) : ℝ) : ℂ) = G x := by
  simp_rw [← Complex.ofReal_mul]
  rw [integral_complex_ofReal, hG]
  congr 1

section

variable {c : ℝ} (hc1 : 1 / 2 < c) (hc2 : c < 1)
include hc1 hc2

/-- **The Poisson semigroup at the critical weight.** -/
theorem poisson_cw : ∃ K : ℝ, 0 < K ∧ ∀ τ : ℝ, 0 < τ → τ ≤ 1 → ∀ f : L2H',
    ∫⁻ z : UpperHalfPlane, ENNReal.ofReal (omC c (z : ℂ) ^ 2 * ‖specE.integral (GW 0 τ) f z‖ ^ 2)
      ≤ ENNReal.ofReal (K ^ 2) * ∫⁻ z : UpperHalfPlane, ENNReal.ofReal (omC c (z : ℂ) ^ 2 * ‖f z‖ ^ 2) := by
  have hc0 : 0 ≤ c := by linarith
  have hD : 0 < Real.exp (1 / 2) * (2 : ℝ) ^ c := by positivity
  obtain ⟨K, hK, h⟩ := cw_abstract hc1 hc2 hD
  set B₀ : ℝ := 4 * √2 + 2 / √Real.pi * (2 * √2) with hB₀
  have hB₀0 : 0 < B₀ := by positivity
  refine ⟨K * B₀, by positivity, fun τ hτ hτ1 f => ?_⟩
  have hint : Integrable (gTau τ) := integrable_of_symbol (gTau_symbol hτ le_rfl).1
  have htail : TailB (gTau τ) B₀ := (gTau_TailB hτ).mono (by
    have e : τ / (2 * (τ / 2)) = 1 := by field_simp
    rw [e, hB₀]
    have h1 : 2 * τ / √Real.pi * (2 * √2) ≤ 2 / √Real.pi * (2 * √2) := by
      have hp : 0 ≤ 2 * √2 := by positivity
      refine mul_le_mul_of_nonneg_right ?_ hp
      have hs : 0 < √Real.pi := Real.sqrt_pos.2 Real.pi_pos
      exact div_le_div_of_nonneg_right (by linarith) hs.le
    linarith)
  refine h (fun z => omC c (z : ℂ)) (omC_nonneg c) (fun n z hz => omC_lo hc0 n z hz) (fun l z hz => omC_hi hc0 l z hz)
    hB₀0 hint htail (GW_mem 0 hτ) (fun x hx => ?_) f
  have hx0 : 0 ≤ x := by linarith
  refine rep_of_real (R := Real.exp (-(τ * √x))) ?_ (gTau_symbol hτ hx).2
  simp [GW, rW, hx0]

/-- **`Λ e^{-sΛ}` at the critical weight.** -/
theorem lam_cw : ∃ K : ℝ, 0 < K ∧ ∀ s : ℝ, 0 < s → s ≤ 1 → ∀ f : L2H',
    ∫⁻ z : UpperHalfPlane, ENNReal.ofReal (omC c (z : ℂ) ^ 2 * ‖specE.integral (GLam s) f z‖ ^ 2)
      ≤ ENNReal.ofReal ((K / s) ^ 2) * ∫⁻ z : UpperHalfPlane, ENNReal.ofReal (omC c (z : ℂ) ^ 2 * ‖f z‖ ^ 2) := by
  have hc0 : 0 ≤ c := by linarith
  have hD : 0 < Real.exp (1 / 2) * (2 : ℝ) ^ c := by positivity
  obtain ⟨K, hK, h⟩ := cw_abstract hc1 hc2 hD
  have hcH : 0 < cH := cH_pos
  set B₁ : ℝ := 4 * √2 * (cH * √2) + 2 * cH / √Real.pi * (2 * √2) with hB₁
  have hB₁0 : 0 < B₁ := by positivity
  refine ⟨K * B₁, by positivity, fun s hs hs1 f => ?_⟩
  have hint : Integrable (hS s) := integrable_of_symbol (hS_symbol hs le_rfl).1
  have hBs : 0 < B₁ / s := by positivity
  have htail : TailB (hS s) (B₁ / s) := (hS_TailB hs).mono (by
    have e : cH / (2 * (s / (2 * √2))) = cH * √2 / s := by
      have h2 : √2 ≠ 0 := by positivity
      field_simp
    rw [e, hB₁, add_div]
    have ht : 0 ≤ 2 * cH / √Real.pi * (2 * √2) := by positivity
    have e2 : 4 * √2 * (cH * √2 / s) = 4 * √2 * (cH * √2) / s := by ring
    rw [e2]
    have : 2 * cH / √Real.pi * (2 * √2) ≤ 2 * cH / √Real.pi * (2 * √2) / s := by
      rw [le_div_iff₀ hs]
      nlinarith
    linarith)
  have := h (fun z => omC c (z : ℂ)) (omC_nonneg c) (fun n z hz => omC_lo hc0 n z hz) (fun l z hz => omC_hi hc0 l z hz)
    hBs hint htail (GLam_mem hs) (fun x hx => ?_) f
  · have e : K * (B₁ / s) = K * B₁ / s := by ring
    rwa [e] at this
  · have hx0 : 0 ≤ x := by linarith
    refine rep_of_real (R := √x * Real.exp (-(s * √x))) ?_ (hS_symbol hs hx).2
    simp [GLam, rL, hx0]

/-- Powers of `Λ e^{-aΛ}`. -/
theorem lam_pow_cw : ∃ K : ℝ, 0 < K ∧ ∀ a : ℝ, 0 < a → a ≤ 1 → ∀ (m : ℕ) (f : L2H'),
    ∫⁻ z : UpperHalfPlane, ENNReal.ofReal (omC c (z : ℂ) ^ 2 * ‖specE.integral (GLam a ^ m) f z‖ ^ 2)
      ≤ ENNReal.ofReal (((K / a) ^ m) ^ 2) * ∫⁻ z : UpperHalfPlane, ENNReal.ofReal (omC c (z : ℂ) ^ 2 * ‖f z‖ ^ 2) := by
  obtain ⟨K, hK, h⟩ := lam_cw hc1 hc2
  refine ⟨K, hK, fun a ha ha1 m => ?_⟩
  induction m with
  | zero =>
    intro f
    rw [pow_zero, pow_zero, one_pow, ENNReal.ofReal_one, one_mul, specE.integral_one]
    exact le_rfl
  | succ m ih =>
    intro f
    have hm := pow_mem_B (GLam_mem ha) m
    have e : specE.integral (GLam a ^ (m + 1)) f = specE.integral (GLam a ^ m) (specE.integral (GLam a) f) := by
      rw [pow_succ, specE.integral_mul hm (GLam_mem ha)]
      rfl
    rw [e]
    have hKa : 0 < K / a := by positivity
    calc _ ≤ ENNReal.ofReal (((K / a) ^ m) ^ 2) * ∫⁻ z : UpperHalfPlane, ENNReal.ofReal (omC c (z : ℂ) ^ 2 * ‖specE.integral (GLam a) f z‖ ^ 2) := ih _
      _ ≤ ENNReal.ofReal (((K / a) ^ m) ^ 2) * (ENNReal.ofReal ((K / a) ^ 2) * ∫⁻ z : UpperHalfPlane, ENNReal.ofReal (omC c (z : ℂ) ^ 2 * ‖f z‖ ^ 2)) := by
          gcongr
          exact h a ha ha1 f
      _ = _ := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
          congr 2
          ring

/-- **The base case of the word estimate.** -/
theorem base_vj : ∃ Cs C0 : ℝ, 1 ≤ Cs ∧ 0 < C0 ∧ ∀ σ : ℝ, 0 < σ → σ ≤ 1 → ∀ (j : ℕ) (f : L2H'),
    ∫⁻ z : UpperHalfPlane, ENNReal.ofReal (omC c (z : ℂ) ^ 2 * ‖specE.integral (GW j σ) f z‖ ^ 2)
      ≤ ENNReal.ofReal ((Cs * (C0 / σ) ^ (2 * j) * ((2 * j).factorial : ℝ)) ^ 2)
        * ∫⁻ z : UpperHalfPlane, ENNReal.ofReal (omC c (z : ℂ) ^ 2 * ‖f z‖ ^ 2) := by
  obtain ⟨K₁, hK₁, h1⟩ := poisson_cw hc1 hc2
  obtain ⟨K, hK, h⟩ := lam_pow_cw hc1 hc2
  refine ⟨max K₁ 1, Real.exp 1 * K, le_max_right _ _, by positivity, fun σ hσ hσ1 j f => ?_⟩
  set Cs := max K₁ 1 with hCs
  have hCs1 : 1 ≤ Cs := le_max_right _ _
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · refine (h1 σ hσ hσ1 f).trans ?_
    gcongr
    simp only [mul_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one]
    exact le_max_left _ _
  · have hj' : (0 : ℝ) < j := by exact_mod_cast hj
    set a := σ / (2 * j) with ha
    have ha0 : 0 < a := by positivity
    have ha1 : a ≤ 1 := by
      rw [ha, div_le_one (by positivity)]
      have : (1 : ℝ) ≤ j := by exact_mod_cast hj
      linarith
    have eG : GW j σ = GLam a ^ (2 * j) := by
      funext s
      simp only [GW, GLam, Pi.pow_apply, rW, rL]
      split_ifs with hs
      · rw [← Complex.ofReal_pow, mul_pow, ← Real.exp_nat_mul]
        congr 3
        rw [ha]
        push_cast
        field_simp
      · rw [Complex.ofReal_zero, zero_pow (by omega)]
    rw [eG]
    refine (h a ha0 ha1 (2 * j) f).trans ?_
    gcongr
    have hb : (K / a) ^ (2 * j) ≤ Cs * (Real.exp 1 * K / σ) ^ (2 * j) * ((2 * j).factorial : ℝ) := by
      have e1 : K / a = (2 * j : ℕ) * (K / σ) := by
        rw [ha]
        push_cast
        field_simp
      rw [e1, mul_pow]
      have hn := Real.pow_div_factorial_le_exp ((2 * j : ℕ) : ℝ) (by positivity) (2 * j)
      have hf : (0 : ℝ) < (2 * j).factorial := by exact_mod_cast (2 * j).factorial_pos
      rw [div_le_iff₀ hf, ← Real.exp_one_pow] at hn
      have e2 : (Real.exp 1 * K / σ) ^ (2 * j) = Real.exp 1 ^ (2 * j) * (K / σ) ^ (2 * j) := by
        rw [mul_div_assoc, mul_pow]
      rw [e2]
      have hKs : 0 ≤ (K / σ) ^ (2 * j) := by positivity
      calc ((2 * j : ℕ) : ℝ) ^ (2 * j) * (K / σ) ^ (2 * j)
          ≤ (Real.exp 1 ^ (2 * j) * ((2 * j).factorial : ℝ)) * (K / σ) ^ (2 * j) := mul_le_mul_of_nonneg_right hn hKs
        _ = 1 * (Real.exp 1 ^ (2 * j) * (K / σ) ^ (2 * j)) * ((2 * j).factorial : ℝ) := by ring
        _ ≤ _ := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCs1 (by positivity)) hf.le
    exact hb

end

end Qschubert
