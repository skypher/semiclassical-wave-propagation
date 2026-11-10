import Qschubert.EvModMellin

/-!
# The zero mode of the periodized approximation, tested against test functions

Stage A of the plan for Proposition `ev:mod` (`lean/BLUEPRINT.md`), items L1 to L3. For `w ∈ L²(M)`,
`M = PSL(2, ℤ)\ℍ`, let `c₀[w](y) = ∫_0^1 w(π(x + iy)) dx` (`zeroModeM`). Then for every test function `g` on `(0, ∞)`:

* `integral_mul_conj_eis_eq_zeroMode`: `∫_M w conj(E_g) dμ = ∫_0^∞ c₀[w](y) conj(g(y)) dy/y²`;
* `zeroMode_approx_star`: for `v_t = [u⁽⁰⁾(t)[a']]_Γ`,
  `∫_0^∞ c₀[v_t] conj(g) dy/y² = ∫_0^∞ f_t conj(g + R_g) dy/y²`.
-/

namespace Qschubert

open MeasureTheory Filter Topology UpperHalfPlane Set
open scoped MatrixGroups Real ComplexConjugate ENNReal

/-- The zero Fourier mode `c₀[w](y) = ∫_0^1 w(π(x + iy)) dx` of a function on the modular surface. -/
noncomputable def zeroModeM (w : Surf modGroup → ℂ) (y : ℝ) : ℂ :=
  if hy : 0 < y then ∫ x in (0 : ℝ)..1, w (surfMk modGroup ⟨⟨x, y⟩, hy⟩) else 0

/-- **The pairing with an incomplete Eisenstein series in terms of the zero mode.** -/
theorem integral_mul_conj_eis_eq_zeroMode {w : Surf modGroup → ℂ} (hw : MemLp w 2 (surfMeasure modGroup))
    {g : ℝ → ℂ} (hg : IsKTest g) :
    ∫ x, w x * conj (perio modGroup (stripFn g) x) ∂surfMeasure modGroup
      = ∫ y in Ioi (0 : ℝ), ((y ^ 2)⁻¹ : ℝ) • (zeroModeM w y * conj (g y)) := by
  have hwm := hw.aestronglyMeasurable
  rw [integral_mul_conj_perio_stripFn hwm hw hg, integral_H_slice (integrable_lift_mul_conj_stripFn hwm hw hg)]
  refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
  have hy0 : (0 : ℝ) < y := hy
  have e : ∀ x : ℝ, w (surfMk modGroup (UpperHalfPlane.ofComplex ⟨x, y⟩)) * conj (stripFn g (UpperHalfPlane.ofComplex ⟨x, y⟩))
      = (Ico (0 : ℝ) 1).indicator (fun x => w (surfMk modGroup ⟨⟨x, y⟩, hy0⟩) * conj (g y)) x := by
    intro x
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos (show 0 < (⟨x, y⟩ : ℂ).im from hy0)]
    have hs : stripFn g (⟨⟨x, y⟩, hy0⟩ : ℍ) = if ⌊x⌋ = 0 then g y else 0 := rfl
    rw [hs]
    by_cases hx : ⌊x⌋ = 0
    · rw [ite_eq_left hx, Set.indicator_of_mem (Int.floor_eq_zero_iff.1 hx)]
    · rw [ite_eq_right hx, Set.indicator_of_notMem (fun h => hx (Int.floor_eq_zero_iff.2 h)), map_zero, mul_zero]
  simp only [e]
  rw [integral_indicator measurableSet_Ico, integral_mul_const, zeroModeM, dite_eq_left hy0,
    intervalIntegral.integral_of_le zero_le_one, integral_Ico_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]

lemma mem_absSet_of_summable {Γ : Subgroup PGL(2, ℝ)} [Countable Γ] {F : ℍ → ℂ} {z : ℍ}
    (h : Summable fun γ : Γ => ‖F (γ • z)‖) : z ∈ absSet Γ F := by
  show absSum Γ F z < ∞
  have e : absSum Γ F z = ENNReal.ofReal (∑' γ : Γ, ‖F (γ • z)‖) := by
    rw [absSum, ENNReal.ofReal_tsum_of_nonneg (fun γ => norm_nonneg _) h]
    exact tsum_congr fun γ => (ofReal_norm _).symm
  rw [e]
  exact ENNReal.ofReal_lt_top

variable {α : ℝ} {h : ℂ → ℂ} {h₀ : ℝ → ℝ} {a' : ℍ → ℂ}

lemma measurable_approxSolB_zero (ham : Measurable a') (ħ t : ℝ) : Measurable (approxSolB 1 0 ħ t a') := by
  have e : approxSolB 1 0 ħ t a' = fun z => cT ħ t * a' (dilate t z) * phs ħ z.im :=
    funext fun z => approxSolB_one_zero_eq ħ t a' z
  rw [e]
  exact (measurable_const.mul (ham.comp (measurable_dilate t))).mul (measurable_phs_im ħ)

lemma integrable_approxSolB_zero (ham : Measurable a') (hai : Integrable a') (ħ t : ℝ) :
    Integrable (approxSolB 1 0 ħ t a') := by
  have h1 : Integrable a' (Measure.map (dilate t) (volume : Measure ℍ)) := by
    rw [map_dilate]
    exact hai.smul_measure ENNReal.ofReal_ne_top
  have h2 : Integrable (a' ∘ dilate t) := h1.comp_measurable (measurable_dilate t)
  refine (h2.norm.const_mul ‖cT ħ t‖).mono' (measurable_approxSolB_zero ham ħ t).aestronglyMeasurable
    (Eventually.of_forall fun z => ?_)
  rw [approxSolB_one_zero_eq, norm_mul, norm_mul, norm_phs, mul_one]
  rfl

/-- **The identity (★)**: the zero mode of the periodized approximation against a test function. -/
theorem zeroMode_approx_star (hα : 0 < α) (hd : ModData h h₀) (ham : Measurable a') (hai : Integrable a')
    (ha : a' =ᵐ[volume] ampMod α hα.le hd.test) {ħ t : ℝ} (hw : PerioConv modGroup (approxSolB 1 0 ħ t a'))
    {g : ℝ → ℂ} (hg : IsKTest g) :
    ∫ y in Ioi (0 : ℝ), ((y ^ 2)⁻¹ : ℝ) • (zeroModeM (perio modGroup (approxSolB 1 0 ħ t a')) y * conj (g y))
      = ∫ y in Ioi (0 : ℝ), ((y ^ 2)⁻¹ : ℝ) • (conj (g y + eisR g y) * fT ħ t a' y) := by
  have hFm := measurable_approxSolB_zero ham ħ t
  have hFi := integrable_approxSolB_zero ham hai ħ t
  have hS : ∀ᵐ z ∂(volume : Measure ℍ), z ∈ absSet modGroup (approxSolB 1 0 ħ t a') := by
    filter_upwards [hw.1] with z hz
    exact mem_absSet_of_summable hz
  rw [← integral_mul_conj_eis_eq_zeroMode hw.2 hg, ← pairing_approx_eis hα hd ham hai ha hg ħ t,
    ← integral_conj_perio_stripFn_mul hFm hFi hS hg]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  exact mul_comm _ _

end Qschubert
