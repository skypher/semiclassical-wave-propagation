import Qschubert.EvModOut
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# The zero mode of the periodized approximation, almost everywhere

Stage A of the plan for Proposition `ev:mod` (`lean/BLUEPRINT.md`), item L5. For the data of `ModData`, a measurable
representative `a'` of `e^{-αΛ} h` and a measurable representative `w` of `v_t = [u⁽⁰⁾(t)[a']]_Γ`:

`c₀[w](y) = f_t(y) + (3/π) ∫ f_t dy/y² + O_{f_t}(y)` for almost every `y > 0` (`zeroMode_approx_ae`),

where `O_{f_t}(y) = (1/2π) ∫ Φ(1/2 + ir) f̂_t(1/2 + ir) y^{1/2 - ir} dr` (`outF (fhat …)`).

Proof: both sides have the same integral against every real test function on `(0, ∞)` (`pair_real_test`), by
`zeroMode_approx_star`, `eisR_eq` and `transpose_out`; and a locally integrable function is determined by these
integrals.
-/

namespace Qschubert

open MeasureTheory Filter Topology UpperHalfPlane Set
open scoped MatrixGroups Real ComplexConjugate ENNReal ContDiff

/-- The mean `∫ f_t dy/y²`. -/
noncomputable def meanT (ħ t : ℝ) (a : ℍ → ℂ) : ℂ := ∫ y in Ioi (0 : ℝ), ((y ^ 2)⁻¹ : ℝ) • fT ħ t a y

/-- `y^{-2}` times the difference of the two sides. -/
noncomputable def zmDiff (α ħ t : ℝ) (h : ℂ → ℂ) (a : ℍ → ℂ) (w : Surf modGroup → ℂ) (y : ℝ) : ℂ :=
  ((y ^ 2)⁻¹ : ℝ) • (zeroModeM w y - fT ħ t a y - 3 / (π : ℂ) * meanT ħ t a - outF (fhat α ħ t (prof h 0)) y)

variable {α : ℝ} {h : ℂ → ℂ} {h₀ : ℝ → ℝ} {a' : ℍ → ℂ}

lemma powIm_zero (z : ℂ) : powIm 0 z = 1 := by
  simp [powIm, powR]

lemma integrable_amp (hα : 0 < α) (hα1 : α ≤ 1) (hh : IsTestFn h) (ha : a' =ᵐ[volume] ampMod α hα.le hh) :
    Integrable a' := by
  have h1 := (zeroMode_mult_amp hα hα1 hh ha (w := 0) (by simp) (by norm_num)).1
  refine h1.congr (Eventually.of_forall fun z => ?_)
  show powIm 0 (z : ℂ) * a' z = a' z
  rw [powIm_zero, one_mul]

lemma isKTest_ofReal {g : ℝ → ℝ} (hg1 : ContDiff ℝ ∞ g) (hg2 : HasCompactSupport g) (hg3 : tsupport g ⊆ Ioi 0) :
    IsKTest fun y => (g y : ℂ) :=
  ⟨Complex.ofRealCLM.contDiff.comp hg1, hg2.comp_left Complex.ofReal_zero,
    (tsupport_comp_subset Complex.ofReal_zero g).trans hg3⟩

lemma inv_sq_mul_exp_half {y : ℝ} (hy : 0 < y) :
    (y ^ 2)⁻¹ * Real.exp (1 / 2 * Real.log y) = ‖powR ((-(3 / 2) : ℝ) : ℂ) y‖ := by
  rw [norm_powR, Complex.ofReal_re]
  have e : (y ^ 2)⁻¹ = Real.exp (-2 * Real.log y) := by
    rw [show (-2 : ℝ) * Real.log y = -(Real.log y + Real.log y) by ring, Real.exp_neg, Real.exp_add, Real.exp_log hy, sq]
  rw [e, ← Real.exp_add]
  congr 1
  ring

/-- Both sides of the identity have the same integral against a real test function. -/
theorem pair_real_test (hα : 0 < α) (hα1 : α ≤ 1) (hd : ModData h h₀) (ham : Measurable a')
    (ha : a' =ᵐ[volume] ampMod α hα.le hd.test) {ħ t : ℝ} (hw : PerioConv modGroup (approxSolB 1 0 ħ t a'))
    {w : Surf modGroup → ℂ} (hwm : Measurable w)
    (hwe : w =ᵐ[surfMeasure modGroup] perio modGroup (approxSolB 1 0 ħ t a'))
    {g : ℝ → ℝ} (hg1 : ContDiff ℝ ∞ g) (hg2 : HasCompactSupport g) (hg3 : tsupport g ⊆ Ioi 0) :
    IntegrableOn (fun y => g y • zmDiff α ħ t h a' w y) (Ioi 0)
      ∧ ∫ y in Ioi (0 : ℝ), g y • zmDiff α ħ t h a' w y = 0 := by
  set gc : ℝ → ℂ := fun y => (g y : ℂ) with hgcd
  have hgc : IsKTest gc := isKTest_ofReal hg1 hg2 hg3
  have hcg : ∀ y, conj (gc y) = gc y := fun y => Complex.conj_ofReal _
  set f : ℝ → ℂ := fT ħ t a' with hfd
  have hZ : IsKTest (prof h 0) := isKTest_prof ⟨h, hd.test⟩ 0
  set Fh : ℝ → ℂ := fhat α ħ t (prof h 0) with hFhd
  set M : ℂ := meanT ħ t a' with hMd
  have hai : Integrable a' := integrable_amp hα hα1 hd.test ha
  have hi0 := (zeroMode_mult_amp hα hα1 hd.test ha (w := 0) (by simp) (by norm_num)).1
  have hih := (zeroMode_mult_amp hα hα1 hd.test ha (w := 1 / 2) (by norm_num) (by norm_num)).1
  have hfm : Measurable f := measurable_fT ham ħ t
  have hf0 : IntegrableOn (fun y : ℝ => ((y ^ 2)⁻¹ : ℝ) • f y) (Ioi 0) := by
    refine (integrableOn_powR_fT ham 0 hi0 ħ t).congr_fun (fun y _ => ?_) measurableSet_Ioi
    show ((y ^ 2)⁻¹ : ℝ) • (powR 0 y * fT ħ t a' y) = ((y ^ 2)⁻¹ : ℝ) • fT ħ t a' y
    rw [powR, zero_mul, Complex.exp_zero, one_mul]
  have hf32 : IntegrableOn (fun y : ℝ => powR ((-(3 / 2) : ℝ) : ℂ) y * f y) (Ioi 0) := by
    refine (integrableOn_powR_fT ham (1 / 2) hih ħ t).congr_fun (fun y hy => ?_) measurableSet_Ioi
    have hy0 : (0 : ℝ) < y := hy
    show ((y ^ 2)⁻¹ : ℝ) • (powR (1 / 2) y * fT ħ t a' y) = powR ((-(3 / 2) : ℝ) : ℂ) y * fT ħ t a' y
    rw [show (((-(3 / 2) : ℝ)) : ℂ) = 1 / 2 + -2 by push_cast; ring, powR_add, powR_neg_two hy0, Complex.real_smul]
    ring
  have hFi : Integrable Fh := integrable_fhat hα.le ħ t hZ
  have hFm : Measurable Fh := (continuous_fhat α ħ t hZ).measurable
  have hmel : ∀ r : ℝ, ∫ y in Ioi (0 : ℝ), powR (-(1 / 2 + r * Complex.I) - 1) y * f y = Fh r := fun r =>
    mellin_fT hα hα1 hd.test ha ħ t r
  have hwL : MemLp w 2 (surfMeasure modGroup) := MemLp.ae_eq hwe.symm hw.2
  obtain ⟨B, hB⟩ := hgc.continuous.bounded_above_of_compact_support hgc.compact
  have hsqm : Measurable fun y : ℝ => (y ^ 2)⁻¹ := (measurable_id.pow_const 2).inv
  have hgcm : Measurable fun y : ℝ => conj (gc y) := hgc.conj.continuous.measurable
  -- the pieces
  set J1 : ℝ → ℂ := fun y => ((y ^ 2)⁻¹ : ℝ) • (zeroModeM w y * conj (gc y)) with hJ1d
  set J2 : ℝ → ℂ := fun y => ((y ^ 2)⁻¹ : ℝ) • (conj (gc y) * f y) with hJ2d
  set J3 : ℝ → ℂ := fun y => ((y ^ 2)⁻¹ : ℝ) • conj (gc y) with hJ3d
  set J4 : ℝ → ℂ := fun y => ((y ^ 2)⁻¹ : ℝ) • (conj (gc y) * outF Fh y) with hJ4d
  set J5 : ℝ → ℂ := fun y => ((y ^ 2)⁻¹ : ℝ) • (conj (outO gc y) * f y) with hJ5d
  have hJ1 : IntegrableOn J1 (Ioi 0) := integrableOn_zeroModeM_mul_conj hwm hwL hgc
  have hJ2 : IntegrableOn J2 (Ioi 0) := by
    refine (hf0.norm.const_mul B).mono' (hsqm.smul (hgcm.mul hfm)).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
    simp only [hJ2d]
    rw [norm_smul, norm_mul, RCLike.norm_conj, norm_smul]
    calc ‖(y ^ 2)⁻¹‖ * (‖gc y‖ * ‖f y‖) = ‖gc y‖ * (‖(y ^ 2)⁻¹‖ * ‖f y‖) := by ring
      _ ≤ B * (‖(y ^ 2)⁻¹‖ * ‖f y‖) := mul_le_mul_of_nonneg_right (hB y) (by positivity)
  have hJ3 : IntegrableOn J3 (Ioi 0) := by
    refine (hgc.conj.integrable_powR_mul (-2)).integrableOn.congr_fun (fun y hy => ?_) measurableSet_Ioi
    have hy0 : (0 : ℝ) < y := hy
    show powR (-2) y * conj (gc y) = ((y ^ 2)⁻¹ : ℝ) • conj (gc y)
    rw [powR_neg_two hy0, Complex.real_smul]
  set C4 : ℝ := 1 / (2 * π) * ∫ r : ℝ, ‖Fh r‖ with hC4
  have hJ4 : IntegrableOn J4 (Ioi 0) := by
    refine ((hgc.integrable_powR_mul ((-(3 / 2) : ℝ) : ℂ)).norm.const_mul C4).integrableOn.mono'
      (hsqm.smul (hgcm.mul (measurable_outF hFm))).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy0 : (0 : ℝ) < y := hy
    simp only [hJ4d]
    rw [norm_smul, norm_mul, RCLike.norm_conj, Real.norm_of_nonneg (by positivity), norm_mul,
      ← inv_sq_mul_exp_half hy0]
    have hO := norm_outF_le Fh y
    rw [← hC4] at hO
    calc (y ^ 2)⁻¹ * (‖gc y‖ * ‖outF Fh y‖) ≤ (y ^ 2)⁻¹ * (‖gc y‖ * (C4 * Real.exp (1 / 2 * Real.log y))) := by
          have : 0 ≤ (y ^ 2)⁻¹ := by positivity
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hO (norm_nonneg _)) this
      _ = C4 * ((y ^ 2)⁻¹ * Real.exp (1 / 2 * Real.log y) * ‖gc y‖) := by ring
  set Gh : ℝ → ℂ := fun r => mellT gc (critS r) with hGhd
  have hGm : Measurable Gh := ((continuous_mellT hgc).comp continuous_critS).measurable
  set C5 : ℝ := 1 / (2 * π) * ∫ r : ℝ, ‖Gh r‖ with hC5
  have hOO : outO gc = outF Gh := funext fun y => outO_eq_outF gc y
  have hJ5 : IntegrableOn J5 (Ioi 0) := by
    have hOm : Measurable fun y : ℝ => conj (outO gc y) := by
      rw [hOO]
      exact Complex.continuous_conj.measurable.comp (measurable_outF hGm)
    refine (hf32.norm.const_mul C5).mono' (hsqm.smul (hOm.mul hfm)).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy0 : (0 : ℝ) < y := hy
    simp only [hJ5d]
    rw [norm_smul, norm_mul, RCLike.norm_conj, Real.norm_of_nonneg (by positivity), norm_mul,
      ← inv_sq_mul_exp_half hy0, hOO]
    have hO := norm_outF_le Gh y
    rw [← hC5] at hO
    calc (y ^ 2)⁻¹ * (‖outF Gh y‖ * ‖f y‖) ≤ (y ^ 2)⁻¹ * (C5 * Real.exp (1 / 2 * Real.log y) * ‖f y‖) := by
          have : 0 ≤ (y ^ 2)⁻¹ := by positivity
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hO (norm_nonneg _)) this
      _ = C5 * ((y ^ 2)⁻¹ * Real.exp (1 / 2 * Real.log y) * ‖f y‖) := by ring
  -- the identity (★) for `w`
  have hstar : ∫ y in Ioi (0 : ℝ), J1 y
      = ∫ y in Ioi (0 : ℝ), ((y ^ 2)⁻¹ : ℝ) • (conj (gc y + eisR gc y) * f y) := by
    have e1 := integral_mul_conj_eis_eq_zeroMode hwL hgc
    have e2 := integral_mul_conj_eis_eq_zeroMode hw.2 hgc
    have e3 : ∫ x, w x * conj (perio modGroup (stripFn gc) x) ∂surfMeasure modGroup
        = ∫ x, perio modGroup (approxSolB 1 0 ħ t a') x * conj (perio modGroup (stripFn gc) x) ∂surfMeasure modGroup :=
      integral_congr_ae (hwe.mono fun x hx => by
        show w x * conj (perio modGroup (stripFn gc) x)
          = perio modGroup (approxSolB 1 0 ħ t a') x * conj (perio modGroup (stripFn gc) x)
        rw [hx])
    rw [← e1, e3, e2]
    exact zeroMode_approx_star hα hd ham hai ha hw hgc
  have hsplit : ∀ y ∈ Ioi (0 : ℝ), ((y ^ 2)⁻¹ : ℝ) • (conj (gc y + eisR gc y) * f y)
      = J2 y + conj (3 / (π : ℂ) * mellT gc 1) * (((y ^ 2)⁻¹ : ℝ) • f y) + J5 y := by
    intro y hy
    have hy0 : (0 : ℝ) < y := hy
    have e : eisR gc y = 3 / (π : ℂ) * mellT gc 1 + outO gc y := eisR_eq hgc hy0
    simp only [hJ2d, hJ5d]
    rw [e, map_add, map_add, Complex.real_smul, Complex.real_smul, Complex.real_smul, Complex.real_smul]
    ring
  have hRHS : ∫ y in Ioi (0 : ℝ), ((y ^ 2)⁻¹ : ℝ) • (conj (gc y + eisR gc y) * f y)
      = (∫ y in Ioi (0 : ℝ), J2 y) + conj (3 / (π : ℂ) * mellT gc 1) * M + ∫ y in Ioi (0 : ℝ), J5 y := by
    have hfc : IntegrableOn (fun y : ℝ => conj (3 / (π : ℂ) * mellT gc 1) * (((y ^ 2)⁻¹ : ℝ) • f y)) (Ioi 0) :=
      hf0.const_mul _
    have hJ2c : IntegrableOn (fun y : ℝ => J2 y + conj (3 / (π : ℂ) * mellT gc 1) * (((y ^ 2)⁻¹ : ℝ) • f y)) (Ioi 0) :=
      hJ2.add hfc
    rw [setIntegral_congr_fun measurableSet_Ioi hsplit, integral_add hJ2c hJ5, integral_add hJ2 hfc,
      integral_const_mul]
    rfl
  have htr : ∫ y in Ioi (0 : ℝ), J5 y = ∫ y in Ioi (0 : ℝ), J4 y := transpose_out hgc hfm hf32 hFi hmel
  have h3 : ∫ y in Ioi (0 : ℝ), J3 y = mellT gc 1 := by
    rw [mellT_one_eq]
    refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
    simp only [hJ3d]
    rw [hcg]
  have hconj : conj (3 / (π : ℂ) * mellT gc 1) = 3 / (π : ℂ) * mellT gc 1 := by
    have e : (fun y => conj (gc y)) = gc := funext hcg
    rw [map_mul, conj_mellT, e, map_one, map_div₀, Complex.conj_ofReal, Complex.conj_ofNat]
  -- the tested difference
  have hpt : ∀ y ∈ Ioi (0 : ℝ), g y • zmDiff α ħ t h a' w y
      = J1 y - J2 y - 3 / (π : ℂ) * M * J3 y - J4 y := by
    intro y _
    simp only [zmDiff, hJ1d, hJ2d, hJ3d, hJ4d]
    rw [hcg, Complex.real_smul, Complex.real_smul, Complex.real_smul, Complex.real_smul, Complex.real_smul,
      Complex.real_smul]
    ring
  have hI12 : IntegrableOn (fun y => J1 y - J2 y) (Ioi 0) := hJ1.sub hJ2
  have hI3c : IntegrableOn (fun y => 3 / (π : ℂ) * M * J3 y) (Ioi 0) := hJ3.const_mul _
  have hI123 : IntegrableOn (fun y => J1 y - J2 y - 3 / (π : ℂ) * M * J3 y) (Ioi 0) := hI12.sub hI3c
  have hI : IntegrableOn (fun y => J1 y - J2 y - 3 / (π : ℂ) * M * J3 y - J4 y) (Ioi 0) := hI123.sub hJ4
  refine ⟨hI.congr_fun (fun y hy => (hpt y hy).symm) measurableSet_Ioi, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_sub hI123 hJ4, integral_sub hI12 hI3c,
    integral_sub hJ1 hJ2, integral_const_mul, hstar, hRHS, htr, h3, hconj]
  ring

/-- **The zero mode of the periodized approximation**:
`c₀[w](y) = f_t(y) + (3/π) ∫ f_t dy/y² + O_{f_t}(y)` for almost every `y > 0`. -/
theorem zeroMode_approx_ae (hα : 0 < α) (hα1 : α ≤ 1) (hd : ModData h h₀) (ham : Measurable a')
    (ha : a' =ᵐ[volume] ampMod α hα.le hd.test) {ħ t : ℝ} (hw : PerioConv modGroup (approxSolB 1 0 ħ t a'))
    {w : Surf modGroup → ℂ} (hwm : Measurable w)
    (hwe : w =ᵐ[surfMeasure modGroup] perio modGroup (approxSolB 1 0 ħ t a')) :
    ∀ᵐ y : ℝ, y ∈ Ioi (0 : ℝ) → zeroModeM w y
      = fT ħ t a' y + 3 / (π : ℂ) * meanT ħ t a' + outF (fhat α ħ t (prof h 0)) y := by
  have key := fun (g : ℝ → ℝ) (hg1 : ContDiff ℝ ∞ g) (hg2 : HasCompactSupport g) (hg3 : tsupport g ⊆ Ioi 0) =>
    pair_real_test hα hα1 hd ham ha hw hwm hwe hg1 hg2 hg3
  have hloc : LocallyIntegrableOn (zmDiff α ħ t h a' w) (Ioi 0) := by
    intro y₀ hy₀
    have hy0 : (0 : ℝ) < y₀ := hy₀
    set b : ContDiffBump y₀ := ⟨y₀ / 4, y₀ / 2, by positivity, by linarith⟩ with hb
    have hsub : ∀ ρ : ℝ, ρ ≤ y₀ / 2 → Metric.closedBall y₀ ρ ⊆ Ioi 0 := by
      intro ρ hρ y hy
      have h1 := Metric.mem_closedBall.1 hy
      rw [Real.dist_eq, abs_le] at h1
      show 0 < y
      linarith [h1.1]
    have hb3 : tsupport (b : ℝ → ℝ) ⊆ Ioi 0 := by
      rw [b.tsupport_eq]
      exact hsub _ le_rfl
    have hI := (key b b.contDiff b.hasCompactSupport hb3).1
    refine ⟨Metric.closedBall y₀ (y₀ / 4), mem_nhdsWithin_of_mem_nhds (Metric.closedBall_mem_nhds y₀ (by positivity)), ?_⟩
    refine (hI.mono_set (hsub _ (by linarith))).congr_fun (fun y hy => ?_) measurableSet_closedBall
    show (b y : ℝ) • zmDiff α ħ t h a' w y = zmDiff α ħ t h a' w y
    rw [b.one_of_mem_closedBall hy, one_smul]
  have h0 := isOpen_Ioi.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc (fun g hg1 hg2 hg3 => by
    rw [← (key g hg1 hg2 hg3).2]
    symm
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_
    have hgy : g y = 0 := image_eq_zero_of_notMem_tsupport (fun h' => hy (hg3 h'))
    rw [hgy, zero_smul])
  filter_upwards [h0] with y hy hy0
  have hz := hy hy0
  have hy0' : (0 : ℝ) < y := hy0
  have hne : ((y ^ 2)⁻¹ : ℝ) ≠ 0 := by positivity
  rw [zmDiff, smul_eq_zero] at hz
  rcases hz with hz | hz
  · exact absurd hz hne
  · linear_combination hz

end Qschubert
