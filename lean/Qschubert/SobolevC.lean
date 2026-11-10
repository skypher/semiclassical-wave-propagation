import Mathlib.Analysis.Distribution.Sobolev
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# The Sobolev embedding `H²(ℝ²) ⊂ C_b` on `ℂ ≅ ℝ²`

For `f, h ∈ L²(ℂ)` with `Δf = h` as tempered distributions: `(1 + |ξ|²) 𝓕f = 𝓕f - (2π)^{-2} 𝓕h`
(`smulLeft_one_add_fourier`), so `𝓕f = w · G` with `w = (1 + |ξ|²)^{-1} ∈ L²` and
`G = 𝓕f - (2π)^{-2}𝓕h ∈ L²` (`fourier_eq_weight_smul`); hence `𝓕f ∈ L¹` with
`‖𝓕f‖₁ ≤ ‖w‖₂ (‖f‖₂ + (2π)^{-2}‖h‖₂)`, and `f` agrees a.e. with a bounded continuous function.
This is the Euclidean step of the local Sobolev embedding behind Lemma T.
-/

namespace Qschubert

open MeasureTheory FourierTransform TemperedDistribution SchwartzMap
open scoped Laplacian Real ContDiff

local notation "L2C" => Lp ℂ 2 (volume : Measure ℂ)

/-- `|ξ|²` as a complex function. -/
noncomputable def sqNorm : ℂ → ℂ := fun x => ((‖x‖ ^ 2 : ℝ) : ℂ)

/-- `w(ξ) = (1 + |ξ|²)^{-1}`. -/
noncomputable def weightW : ℂ → ℂ := fun x => (((1 + ‖x‖ ^ 2) ^ (-(1 : ℝ)) : ℝ) : ℂ)

lemma sqNorm_temperate : sqNorm.HasTemperateGrowth := by unfold sqNorm; fun_prop

lemma weightW_temperate : weightW.HasTemperateGrowth := by unfold weightW; fun_prop

lemma weightW_mul_one_add (x : ℂ) : weightW x * (1 + sqNorm x) = 1 := by
  have hpos : (0 : ℝ) < 1 + ‖x‖ ^ 2 := by positivity
  simp only [weightW, sqNorm]
  rw [Real.rpow_neg_one]
  push_cast
  have hne : (1 + (‖x‖ : ℂ) ^ 2) ≠ 0 := by exact_mod_cast hpos.ne'
  exact inv_mul_cancel₀ hne

/-- `c = (2π)²` as a complex number. -/
noncomputable def twoPiSq : ℂ := (((2 * π) ^ 2 : ℝ) : ℂ)

lemma twoPiSq_ne_zero : twoPiSq ≠ 0 := by
  unfold twoPiSq; exact_mod_cast (by positivity : ((2 * π) ^ 2 : ℝ) ≠ 0)

lemma coe_L2 (f g : L2C) (c : ℂ) :
    ((f - c • g : L2C) : 𝓢'(ℂ, ℂ)) = (f : 𝓢'(ℂ, ℂ)) - c • (g : 𝓢'(ℂ, ℂ)) := by
  rw [← Lp.toTemperedDistributionCLM_apply (F := ℂ) (μ := volume) (f - c • g), map_sub, map_smul]
  rfl

/-- `(1 + |ξ|²) 𝓕f = 𝓕f - (2π)^{-2} 𝓕h` when `Δf = h`. -/
theorem smulLeft_one_add_fourier (f h : L2C) (hΔ : Δ (f : 𝓢'(ℂ, ℂ)) = (h : 𝓢'(ℂ, ℂ))) :
    TemperedDistribution.smulLeftCLM ℂ (fun x => 1 + sqNorm x) (𝓕 (f : 𝓢'(ℂ, ℂ)))
      = ((𝓕 f - twoPiSq⁻¹ • 𝓕 h : L2C) : 𝓢'(ℂ, ℂ)) := by
  have h1 : 𝓕 (Δ (f : 𝓢'(ℂ, ℂ)))
      = (-twoPiSq) • TemperedDistribution.smulLeftCLM ℂ sqNorm (𝓕 (f : 𝓢'(ℂ, ℂ))) := by
    rw [TemperedDistribution.laplacian_eq_fourierMultiplierCLM, ← Complex.coe_smul,
      FourierSMul.fourier_smul, TemperedDistribution.fourierMultiplierCLM_apply, fourier_fourierInv_eq]
    congr 1
    simp [twoPiSq]
  rw [hΔ, Lp.fourier_toTemperedDistribution_eq] at h1
  have hsq : TemperedDistribution.smulLeftCLM ℂ sqNorm (𝓕 (f : 𝓢'(ℂ, ℂ)))
      = -(twoPiSq⁻¹ • ((𝓕 h : L2C) : 𝓢'(ℂ, ℂ))) := by
    rw [h1, smul_smul, mul_neg, inv_mul_cancel₀ twoPiSq_ne_zero, neg_smul, one_smul, neg_neg]
  have hadd : (fun x => 1 + sqNorm x) = (fun _ : ℂ => (1 : ℂ)) + sqNorm := rfl
  rw [hadd, TemperedDistribution.smulLeftCLM_add (by fun_prop) sqNorm_temperate,
    add_apply, TemperedDistribution.smulLeftCLM_const, one_smul, hsq,
    Lp.fourier_toTemperedDistribution_eq, coe_L2]
  abel

lemma onePlusSq_temperate : (fun x => 1 + sqNorm x).HasTemperateGrowth := by unfold sqNorm; fun_prop

lemma memLp_weightW : MemLp weightW 2 (volume : Measure ℂ) := by
  have hfr : (Module.finrank ℝ ℂ : ℝ) < 4 := by rw [Complex.finrank_real_complex]; norm_num
  rw [memLp_two_iff_integrable_sq_norm weightW_temperate.1.continuous.aestronglyMeasurable]
  refine (integrable_rpow_neg_one_add_norm_sq hfr).congr (Filter.Eventually.of_forall fun x => ?_)
  have hpos : (0 : ℝ) < 1 + ‖x‖ ^ 2 := by positivity
  simp only [weightW]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hpos _),
    ← Real.rpow_mul_natCast hpos.le]
  norm_num

/-- `G = 𝓕f - (2π)^{-2}𝓕h ∈ L²`. -/
noncomputable def sobG (f h : L2C) : L2C := 𝓕 f - twoPiSq⁻¹ • 𝓕 h

/-- `v = w · G ∈ L¹`. -/
noncomputable def sobV (f h : L2C) : Lp ℂ 1 (volume : Measure ℂ) := memLp_weightW.toLp _ • sobG f h

/-- **`𝓕f = w · G`** as tempered distributions, when `Δf = h`. -/
theorem fourier_eq_sobV (f h : L2C) (hΔ : Δ (f : 𝓢'(ℂ, ℂ)) = (h : 𝓢'(ℂ, ℂ))) :
    𝓕 (f : 𝓢'(ℂ, ℂ)) = ((sobV f h : Lp ℂ 1 (volume : Measure ℂ)) : 𝓢'(ℂ, ℂ)) := by
  have e : 𝓕 (f : 𝓢'(ℂ, ℂ)) = TemperedDistribution.smulLeftCLM ℂ weightW
      (TemperedDistribution.smulLeftCLM ℂ (fun x => 1 + sqNorm x) (𝓕 (f : 𝓢'(ℂ, ℂ)))) := by
    rw [TemperedDistribution.smulLeftCLM_smulLeftCLM_apply onePlusSq_temperate weightW_temperate]
    have : ((fun x => 1 + sqNorm x) * weightW) = fun _ => (1 : ℂ) := by
      funext x; rw [Pi.mul_apply, mul_comm]; exact weightW_mul_one_add x
    rw [this, TemperedDistribution.smulLeftCLM_const, one_smul]
  rw [e, smulLeft_one_add_fourier f h hΔ, sobV,
    Lp.toTemperedDistribution_smul_eq weightW_temperate memLp_weightW]
  rfl

lemma norm_sobV_le (f h : L2C) :
    ‖sobV f h‖ ≤ ‖memLp_weightW.toLp weightW‖ * (‖f‖ + ‖twoPiSq⁻¹‖ * ‖h‖) := by
  refine (Lp.norm_smul_le _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  rw [sobG]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_smul, Lp.norm_fourier_eq, Lp.norm_fourier_eq]

/-- The continuous representative `g = 𝓕⁻ v`. -/
noncomputable def sobRep (f h : L2C) : ℂ → ℂ := 𝓕⁻ (⇑(sobV f h))

lemma integrable_sobV (f h : L2C) : Integrable (⇑(sobV f h)) (volume : Measure ℂ) :=
  L1.integrable_coeFn _

lemma continuous_sobRep (f h : L2C) : Continuous (sobRep f h) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    ((continuous_fst.inner continuous_snd).neg) (integrable_sobV f h)

lemma norm_sobRep_le (f h : L2C) (x : ℂ) : ‖sobRep f h x‖ ≤ ‖sobV f h‖ := by
  rw [sobRep, Real.fourierInv_eq_fourier_neg, L1.norm_eq_integral_norm]
  exact Real.norm_fourier_le_integral_norm _ _

/-- `∫ (𝓕⁻φ) v = ∫ φ (𝓕⁻ v)` for Schwartz `φ` and integrable `v`. -/
lemma integral_fourierInv_smul (φ : 𝓢(ℂ, ℂ)) {v : ℂ → ℂ} (hv : Integrable v) :
    ∫ ξ, (𝓕⁻ φ : 𝓢(ℂ, ℂ)) ξ • v ξ = ∫ x, φ x • (𝓕⁻ v) x := by
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip (μ := (volume : Measure ℂ))
    (ν := (volume : Measure ℂ)) (L := -innerₗ ℂ) (e := Real.fourierChar) Real.continuous_fourierChar
    ((continuous_fst.inner continuous_snd).neg) φ.integrable hv
  have hflip : (-innerₗ ℂ : ℂ →ₗ[ℝ] ℂ →ₗ[ℝ] ℝ).flip = -innerₗ ℂ := by
    ext a b
    simp [real_inner_comm]
  rw [hflip] at h
  rw [SchwartzMap.fourierInv_coe]
  exact h

/-- **Sobolev embedding on `ℂ ≅ ℝ²`**: if `f, h ∈ L²(ℂ)` and `Δf = h` as tempered distributions,
then `f` agrees a.e. with the continuous function `sobRep f h`, and
`|sobRep f h| ≤ ‖w‖₂ (‖f‖₂ + (2π)^{-2}‖h‖₂)` everywhere. -/
theorem sobolevC (f h : L2C) (hΔ : Δ (f : 𝓢'(ℂ, ℂ)) = (h : 𝓢'(ℂ, ℂ))) :
    Continuous (sobRep f h) ∧ (⇑f =ᵐ[volume] sobRep f h) ∧
      ∀ x, ‖sobRep f h x‖ ≤ ‖memLp_weightW.toLp weightW‖ * (‖f‖ + ‖twoPiSq⁻¹‖ * ‖h‖) := by
  refine ⟨continuous_sobRep f h, ?_, fun x => (norm_sobRep_le f h x).trans (norm_sobV_le f h)⟩
  have hfloc : LocallyIntegrable (⇑f) (volume : Measure ℂ) := (Lp.memLp f).locallyIntegrable (by norm_num)
  have hgloc : LocallyIntegrable (sobRep f h) (volume : Measure ℂ) := (continuous_sobRep f h).locallyIntegrable
  have key : ∀ (g : ℂ → ℝ), ContDiff ℝ ∞ g → HasCompactSupport g →
      ∫ x, g x • (⇑f - sobRep f h) x = 0 := by
    intro g hg hgc
    set u : 𝓢(ℂ, ℂ) := HasCompactSupport.toSchwartzMap (f := fun x => ((g x : ℝ) : ℂ))
      (hgc.comp_left Complex.ofReal_zero) (Complex.ofRealCLM.contDiff.comp hg)
    have hu : ∀ x, u x = ((g x : ℝ) : ℂ) := fun x => rfl
    have h1 : (f : 𝓢'(ℂ, ℂ)) u = ∫ x, u x • f x := Lp.toTemperedDistribution_apply f u
    have h2 : (f : 𝓢'(ℂ, ℂ)) = 𝓕⁻ ((sobV f h : Lp ℂ 1 (volume : Measure ℂ)) : 𝓢'(ℂ, ℂ)) := by
      rw [← fourier_eq_sobV f h hΔ, fourierInv_fourier_eq]
    have h3 : (f : 𝓢'(ℂ, ℂ)) u = ∫ x, u x • sobRep f h x := by
      rw [h2, TemperedDistribution.fourierInv_apply, Lp.toTemperedDistribution_apply,
        integral_fourierInv_smul u (integrable_sobV f h)]
      rfl
    have hi1 : Integrable fun x => u x • f x :=
      hfloc.integrable_smul_left_of_hasCompactSupport u.continuous (hgc.comp_left Complex.ofReal_zero)
    have hi2 : Integrable fun x => u x • sobRep f h x :=
      hgloc.integrable_smul_left_of_hasCompactSupport u.continuous (hgc.comp_left Complex.ofReal_zero)
    have hsub : ∫ x, u x • (⇑f - sobRep f h) x = 0 := by
      simp_rw [Pi.sub_apply, smul_sub]
      rw [integral_sub hi1 hi2, ← h1, ← h3, sub_self]
    rw [← hsub]
    congr 1
  have := ae_eq_zero_of_integral_contDiff_smul_eq_zero (hfloc.sub hgloc) key
  filter_upwards [this] with x hx
  exact sub_eq_zero.1 hx

end Qschubert
