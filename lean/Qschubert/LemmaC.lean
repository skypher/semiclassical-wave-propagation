import Qschubert.AmpDomain

/-!
# Spectral domination and Lemma C

* `fc_dom_le` (**spectral domination for `-Δ`**): if `f, g` are measurable and `‖f(s)‖ ≤ C‖g(s)‖`
  for `s ≥ 0`, then `Dom(g(-Δ)) ⊆ Dom(f(-Δ))` and `‖f(-Δ)v‖ ≤ C‖g(-Δ)v‖`. From
  `‖h(A)v‖² = ∫ |h|² dμ_v` and `μ_v([0, ∞)ᶜ) = 0`.
* `one_add_pow_le_exp_sqrt`: `(1 + s)^k ≤ 2^k (1 + (2k)!) α^{-2k} e^{α√s}` for `s ≥ 0`, `0 < α ≤ 1`.
* `lemmaC` (paper Lemma C, `lem:c`, the second inequality, which is the strength its consumers use,
  `C α^{-2k}`): for `v ∈ Dom(e^{αΛ})`, `0 < α ≤ 1`, `k ∈ ℕ`: `v ∈ Dom((1 - Δ)^k)` and
  `‖(1 - Δ)^k v‖ ≤ 2^k (1 + (2k)!) α^{-2k} ‖e^{αΛ} v‖`, where `(1 - Δ)^k := ((1 + s)^k)(-Δ)`.
  In the paper `v = W_β a`.
-/

namespace Qschubert

open MeasureTheory UpperHalfPlane Filter Physicslib4.Spectral Physicslib4.Spectral.Unbounded
open scoped ENNReal

local notation "L2H" => Lp ℂ 2 (volume : Measure ℍ)
local notation "μH" => spectralMeasure negLapH_isSelfAdjoint

lemma ae_nonneg_assoc (v : L2H) : ∀ᵐ s ∂((μH).assoc v), 0 ≤ s := by
  rw [ae_iff]
  have e : {s : ℝ | ¬ 0 ≤ s} = Set.Iio 0 := by ext s; simp
  rw [e]
  exact assoc_Iio_zero v

/-- **Spectral domination for `-Δ`.** -/
theorem fc_dom_le {f g : ℝ → ℂ} (hf : Measurable f) (hg : Measurable g) {C : ℝ} (hC : 0 ≤ C)
    (hfg : ∀ s, 0 ≤ s → ‖f s‖ ≤ C * ‖g s‖) {v : L2H}
    (hv : v ∈ (functionalCalculus negLapH_isSelfAdjoint g).domain) :
    ∃ hv' : v ∈ (functionalCalculus negLapH_isSelfAdjoint f).domain,
      ‖functionalCalculus negLapH_isSelfAdjoint f ⟨v, hv'⟩‖
        ≤ C * ‖functionalCalculus negLapH_isSelfAdjoint g ⟨v, hv⟩‖ := by
  rw [functionalCalculus_domain, mem_integralDomain] at hv
  have hle : ∀ᵐ s ∂((μH).assoc v), ‖f s‖ ≤ C * ‖g s‖ := by
    filter_upwards [ae_nonneg_assoc v] with s hs
    exact hfg s hs
  have hf2 : MemLp f 2 ((μH).assoc v) := MemLp.of_le_mul hv hf.aestronglyMeasurable hle
  refine ⟨hf2, ?_⟩
  have hnf := norm_sq_pmapIntegral (μH) hf ⟨v, hf2⟩
  have hng := norm_sq_pmapIntegral (μH) hg ⟨v, hv⟩
  have key : ∫ s, ‖f s‖ ^ 2 ∂((μH).assoc v) ≤ C ^ 2 * ∫ s, ‖g s‖ ^ 2 ∂((μH).assoc v) := by
    rw [← integral_const_mul]
    refine integral_mono_ae (hf2.integrable_norm_pow two_ne_zero)
      ((hv.integrable_norm_pow two_ne_zero).const_mul _) ?_
    filter_upwards [hle] with s hs
    have h0 : 0 ≤ ‖f s‖ := norm_nonneg _
    calc ‖f s‖ ^ 2 ≤ (C * ‖g s‖) ^ 2 := pow_le_pow_left₀ h0 hs 2
      _ = C ^ 2 * ‖g s‖ ^ 2 := by ring
  have hsq : ‖functionalCalculus negLapH_isSelfAdjoint f ⟨v, hf2⟩‖ ^ 2
      ≤ (C * ‖functionalCalculus negLapH_isSelfAdjoint g ⟨v, hv⟩‖) ^ 2 := by
    rw [mul_pow]
    calc ‖functionalCalculus negLapH_isSelfAdjoint f ⟨v, hf2⟩‖ ^ 2
        = ∫ s, ‖f s‖ ^ 2 ∂((μH).assoc v) := hnf
      _ ≤ C ^ 2 * ∫ s, ‖g s‖ ^ 2 ∂((μH).assoc v) := key
      _ = C ^ 2 * ‖functionalCalculus negLapH_isSelfAdjoint g ⟨v, hv⟩‖ ^ 2 :=
          congrArg (fun x => C ^ 2 * x) hng.symm
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq

/-- `(1 + s)^k ≤ 2^k (1 + (2k)!) α^{-2k} e^{α√s}` for `s ≥ 0`, `0 < α ≤ 1`. -/
lemma one_add_pow_le_exp_sqrt (k : ℕ) {α s : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hs : 0 ≤ s) :
    (1 + s) ^ k ≤ 2 ^ k * (1 + (2 * k).factorial) * α⁻¹ ^ (2 * k) * Real.exp (α * Real.sqrt s) := by
  set l := Real.sqrt s with hl
  have hl0 : 0 ≤ l := Real.sqrt_nonneg s
  have hls : l ^ 2 = s := Real.sq_sqrt hs
  have hx : 0 ≤ α * l := mul_nonneg hα.le hl0
  have he1 : 1 ≤ Real.exp (α * l) := Real.one_le_exp hx
  -- `(αl)^{2k}/(2k)! ≤ e^{αl}`
  have hpow : (α * l) ^ (2 * k) / (2 * k).factorial ≤ Real.exp (α * l) :=
    Real.pow_div_factorial_le_exp (α * l) hx (2 * k)
  have hfac : (0 : ℝ) < (2 * k).factorial := by exact_mod_cast Nat.factorial_pos _
  have hl2k : l ^ (2 * k) ≤ (2 * k).factorial * α⁻¹ ^ (2 * k) * Real.exp (α * l) := by
    rw [mul_pow, div_le_iff₀ hfac] at hpow
    have hαi : α⁻¹ ^ (2 * k) * α ^ (2 * k) = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ hα.ne', one_pow]
    calc l ^ (2 * k) = α⁻¹ ^ (2 * k) * (α ^ (2 * k) * l ^ (2 * k)) := by rw [← mul_assoc, hαi, one_mul]
      _ ≤ α⁻¹ ^ (2 * k) * (Real.exp (α * l) * (2 * k).factorial) :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = (2 * k).factorial * α⁻¹ ^ (2 * k) * Real.exp (α * l) := by ring
  have hαk : 1 ≤ α⁻¹ ^ (2 * k) := one_le_pow₀ (one_le_inv₀ hα |>.2 hα1)
  -- `(1 + l²)^k ≤ 2^k (1 + l^{2k})`
  have hbin : (1 + l ^ 2) ^ k ≤ 2 ^ k * (1 + l ^ (2 * k)) := by
    have hmax : 1 + l ^ 2 ≤ 2 * max 1 (l ^ 2) := by
      rcases le_total 1 (l ^ 2) with h | h
      · rw [max_eq_right h]; linarith
      · rw [max_eq_left h]; linarith
    calc (1 + l ^ 2) ^ k ≤ (2 * max 1 (l ^ 2)) ^ k := pow_le_pow_left₀ (by positivity) hmax k
      _ = 2 ^ k * (max 1 (l ^ 2)) ^ k := by rw [mul_pow]
      _ ≤ 2 ^ k * (1 + l ^ (2 * k)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rcases le_total 1 (l ^ 2) with h | h
          · rw [max_eq_right h, ← pow_mul]; linarith [pow_nonneg (sq_nonneg l) k]
          · rw [max_eq_left h, one_pow]; linarith [pow_nonneg hl0 (2 * k)]
  rw [← hls]
  calc (1 + l ^ 2) ^ k ≤ 2 ^ k * (1 + l ^ (2 * k)) := hbin
    _ ≤ 2 ^ k * (α⁻¹ ^ (2 * k) * Real.exp (α * l)
          + (2 * k).factorial * α⁻¹ ^ (2 * k) * Real.exp (α * l)) := by
        refine mul_le_mul_of_nonneg_left (add_le_add ?_ hl2k) (by positivity)
        nlinarith
    _ = 2 ^ k * (1 + (2 * k).factorial) * α⁻¹ ^ (2 * k) * Real.exp (α * l) := by ring

/-- `(1 - Δ)^k = ((1 + s)^k)(-Δ)`. -/
noncomputable def powP (k : ℕ) : L2H →ₗ.[ℂ] L2H :=
  functionalCalculus negLapH_isSelfAdjoint (fun s => (((1 + s) ^ k : ℝ) : ℂ))

/-- **Lemma C**: `‖(1 - Δ)^k v‖ ≤ 2^k (1 + (2k)!) α^{-2k} ‖e^{αΛ} v‖` for `v ∈ Dom(e^{αΛ})`,
`0 < α ≤ 1`. -/
theorem lemmaC (k : ℕ) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {v : L2H}
    (hv : v ∈ (expLambda α).domain) :
    ∃ hv' : v ∈ (powP k).domain,
      ‖powP k ⟨v, hv'⟩‖ ≤ 2 ^ k * (1 + (2 * k).factorial) * α⁻¹ ^ (2 * k) * ‖expLambda α ⟨v, hv⟩‖ := by
  have hf : Measurable fun s : ℝ => (((1 + s) ^ k : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp ((measurable_const.add measurable_id).pow_const k)
  have hg : Measurable fun s : ℝ => ((Real.exp (α * Real.sqrt s) : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul Real.continuous_sqrt.measurable))
  refine fc_dom_le hf hg (by positivity) (fun s hs => ?_) hv
  rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by positivity), abs_of_pos (Real.exp_pos _)]
  exact one_add_pow_le_exp_sqrt k hα hα1 hs

end Qschubert
