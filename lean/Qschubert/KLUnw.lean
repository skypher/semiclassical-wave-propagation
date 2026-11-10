import Qschubert.KLWeightFlow
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The unweighted factor of part (II)

`‖(Δ_ε(s) - Δ(s)) z‖ ≤ C a⁻⁴ e^{-a/(8ε)} ‖e^{aΛ} z‖` for `s ≥ 0` (`unw_err`). Proof: `Δ_ε - Δ = -J T (1 - J) - (1 - J) T`; `1 - j_ε` is exponentially small on `[0, 1/(2ε)]`, and
`e^{-aλ}` is exponentially small on `[1/(2ε), ∞)`.
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set Physicslib4.Spectral Physicslib4.Spectral.Unbounded ProbabilityTheory
open scoped ENNReal InnerProductSpace Real

local notation "L2H'" => Lp ℂ 2 (volume : Measure UpperHalfPlane)

namespace MollProfile

variable (P : MollProfile) {ε : ℝ}

/-- `1 - j_ε` is exponentially small on `[-1/(2ε), 1/(2ε)]`. -/
lemma one_sub_jEps_small (hε : 0 < ε) {l : ℝ} (hl : |l| ≤ 1 / (2 * ε)) : 1 - P.jEps ε l ≤ √2 * Real.exp (-1 / (16 * ε ^ 2)) := by
  set g₂ : ℝ → ℝ := fun w => (√(2 * π))⁻¹ * Real.exp (-(1 / 4) * (w - l) ^ 2) with hg₂
  have hb : (0 : ℝ) < 1 / 4 := by norm_num
  have hint0 : Integrable fun x : ℝ => Real.exp (-(1 / 4) * x ^ 2) := integrable_exp_neg_mul_sq hb
  have hg₂i : Integrable g₂ := (hint0.comp_sub_right l).const_mul _
  have hg₂v : ∫ w, g₂ w = √2 := by
    have e1 : ∫ w, Real.exp (-(1 / 4) * (w - l) ^ 2) = √(π / (1 / 4)) := by
      rw [integral_sub_right_eq_self (fun x => Real.exp (-(1 / 4) * x ^ 2)) l]
      exact integral_gaussian (1 / 4)
    simp only [hg₂]
    rw [integral_const_mul, e1]
    have e2 : π / (1 / 4) = 2 * (2 * π) := by ring
    have e3 : √(π / (1 / 4)) = √2 * √(2 * π) := by rw [e2, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have hp : √(2 * π) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
    rw [e3, mul_comm √2, ← mul_assoc, inv_mul_cancel₀ hp, one_mul]
  have hgi := integrable_gaussianPDFReal l 1
  have h1 : 1 - P.jEps ε l = ∫ w, gaussianPDFReal l 1 w * (1 - P.χ (ε * w)) := by
    have e := integral_gaussianPDFReal_eq_one l (one_ne_zero)
    have h0 := integral_sub hgi (P.integrable_jEps_integrand ε l)
    rw [e] at h0
    unfold jEps
    rw [← h0]
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    show gaussianPDFReal l 1 w - gaussianPDFReal l 1 w * P.χ (ε * w) = gaussianPDFReal l 1 w * (1 - P.χ (ε * w))
    ring
  rw [h1]
  have hE := Real.exp_pos (-1 / (16 * ε ^ 2))
  have hmaj : Integrable fun w => Real.exp (-1 / (16 * ε ^ 2)) * g₂ w := hg₂i.const_mul _
  have hii : Integrable fun w => gaussianPDFReal l 1 w * (1 - P.χ (ε * w)) :=
    hgi.sub (P.integrable_jEps_integrand ε l) |>.congr (Eventually.of_forall fun w => by simp; ring)
  have hle : ∀ w, gaussianPDFReal l 1 w * (1 - P.χ (ε * w)) ≤ Real.exp (-1 / (16 * ε ^ 2)) * g₂ w := fun w => by
    have hg0 := gaussianPDFReal_nonneg l 1 w
    have hg₂0 : 0 ≤ g₂ w := by simp only [hg₂]; positivity
    by_cases hw : |w| ≤ 1 / ε
    · have : P.χ (ε * w) = 1 := P.one _ (by
        rw [abs_mul, abs_of_pos hε]
        calc ε * |w| ≤ ε * (1 / ε) := by gcongr
          _ = 1 := by field_simp)
      rw [this, sub_self, mul_zero]
      positivity
    · push_neg at hw
      have hd : 1 / (2 * ε) ≤ |w - l| := by
        have h3 := abs_sub_abs_le_abs_sub w l
        have e : 1 / ε = 2 * (1 / (2 * ε)) := by field_simp
        linarith
      have hsq : 1 / (4 * ε ^ 2) ≤ (w - l) ^ 2 := by
        have h4 : (1 / (2 * ε)) ^ 2 ≤ |w - l| ^ 2 := pow_le_pow_left₀ (by positivity) hd 2
        rw [sq_abs] at h4
        calc 1 / (4 * ε ^ 2) = (1 / (2 * ε)) ^ 2 := by field_simp; ring
          _ ≤ _ := h4
      have hχ : 1 - P.χ (ε * w) ≤ 1 := by linarith [P.nonneg (ε * w)]
      have hχ0 : 0 ≤ 1 - P.χ (ε * w) := by linarith [P.le_one (ε * w)]
      rw [gaussianPDFReal_def]
      simp only [NNReal.coe_one, mul_one]
      calc (√(2 * π))⁻¹ * Real.exp (-(w - l) ^ 2 / 2) * (1 - P.χ (ε * w))
          ≤ (√(2 * π))⁻¹ * Real.exp (-(w - l) ^ 2 / 2) * 1 := by gcongr
        _ = (√(2 * π))⁻¹ * (Real.exp (-(1 / 4) * (w - l) ^ 2) * Real.exp (-(1 / 4) * (w - l) ^ 2)) := by
            rw [mul_one, ← Real.exp_add]; congr 2; ring
        _ ≤ (√(2 * π))⁻¹ * (Real.exp (-1 / (16 * ε ^ 2)) * Real.exp (-(1 / 4) * (w - l) ^ 2)) := by
            gcongr
            have : -1 / (16 * ε ^ 2) = -(1 / 4) * (1 / (4 * ε ^ 2)) := by field_simp; ring
            rw [this]
            nlinarith
        _ = _ := by simp only [hg₂]; ring
  calc ∫ w, gaussianPDFReal l 1 w * (1 - P.χ (ε * w)) ≤ ∫ w, Real.exp (-1 / (16 * ε ^ 2)) * g₂ w := integral_mono hii hmaj hle
    _ = _ := by rw [integral_const_mul, hg₂v]; ring

/-- **The remainder symbol.** -/
lemma one_sub_jEps_bound (hε : 0 < ε) (hε1 : ε ≤ 1) {a l : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hl : 0 ≤ l) :
    (1 + l ^ 2) * (1 - P.jEps ε l) ≤ 100 * a⁻¹ * a⁻¹ * Real.exp (-(a / (4 * ε))) * Real.exp (a * l) := by
  have hj0 := P.jEps_nonneg ε l
  have hj1 := P.jEps_le_one ε l
  have hai : 1 ≤ a⁻¹ := (one_le_inv₀ ha).2 ha1
  have haa : 1 ≤ a⁻¹ * a⁻¹ := by nlinarith
  by_cases hsm : l ≤ 1 / (2 * ε)
  · set y := ε⁻¹ with hy
    have hy1 : 1 ≤ y := (one_le_inv₀ hε).2 hε1
    have hl2 : l ^ 2 ≤ y ^ 2 / 4 := by
      have h1 : l ^ 2 ≤ (1 / (2 * ε)) ^ 2 := pow_le_pow_left₀ hl hsm 2
      have e : (1 / (2 * ε)) ^ 2 = y ^ 2 / 4 := by rw [hy]; field_simp; ring
      linarith
    have hsmall := P.one_sub_jEps_small hε (l := l) (by rwa [abs_of_nonneg hl])
    have e2 : -1 / (16 * ε ^ 2) = -(y ^ 2 / 16) := by rw [hy]; field_simp
    rw [e2] at hsmall
    have hexp : (5 / 4) * √2 * (y ^ 2 * Real.exp (-(y ^ 2 / 16))) ≤ 100 * Real.exp (-(y / 4)) := by
      have hm : y ^ 2 * Real.exp (-(y ^ 2 / 16) + y / 4) ≤ 32 * Real.exp (1 / 2) := by
        have h1 : -(y ^ 2 / 16) + y / 4 ≤ -(y ^ 2 / 32) + 1 / 2 := by nlinarith [sq_nonneg (y - 4)]
        have h2 : y ^ 2 / 32 ≤ Real.exp (y ^ 2 / 32) := by linarith [Real.add_one_le_exp (y ^ 2 / 32)]
        have h3 : y ^ 2 * Real.exp (-(y ^ 2 / 32)) ≤ 32 := by
          have hp := Real.exp_pos (-(y ^ 2 / 32))
          have e : Real.exp (y ^ 2 / 32) * Real.exp (-(y ^ 2 / 32)) = 1 := by rw [← Real.exp_add]; simp
          nlinarith
        calc y ^ 2 * Real.exp (-(y ^ 2 / 16) + y / 4) ≤ y ^ 2 * Real.exp (-(y ^ 2 / 32) + 1 / 2) := by gcongr
          _ = y ^ 2 * Real.exp (-(y ^ 2 / 32)) * Real.exp (1 / 2) := by rw [Real.exp_add]; ring
          _ ≤ 32 * Real.exp (1 / 2) := by gcongr
      have he : Real.exp (1 / 2) ≤ 1.74 := by
        have h1 : Real.exp 1 < 3 := Real.exp_one_lt_three
        have h2 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
        nlinarith [Real.exp_pos (1 / 2 : ℝ)]
      have hs2 : √2 ≤ 1.415 := by
        rw [Real.sqrt_le_left (by norm_num)]; norm_num
      have hs0 : 0 ≤ √2 := Real.sqrt_nonneg _
      have hE := Real.exp_pos (-(y / 4))
      have hp : y ^ 2 * Real.exp (-(y ^ 2 / 16)) = y ^ 2 * Real.exp (-(y ^ 2 / 16) + y / 4) * Real.exp (-(y / 4)) := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring
      rw [hp]
      have h5 : y ^ 2 * Real.exp (-(y ^ 2 / 16) + y / 4) ≤ 32 * 1.74 := hm.trans (by linarith)
      have h6 : (5 / 4) * √2 * (y ^ 2 * Real.exp (-(y ^ 2 / 16) + y / 4)) ≤ 100 := by nlinarith
      calc (5 / 4) * √2 * (y ^ 2 * Real.exp (-(y ^ 2 / 16) + y / 4) * Real.exp (-(y / 4)))
          = (5 / 4) * √2 * (y ^ 2 * Real.exp (-(y ^ 2 / 16) + y / 4)) * Real.exp (-(y / 4)) := by ring
        _ ≤ 100 * Real.exp (-(y / 4)) := by gcongr
    have hstep1 : (1 + l ^ 2) * (1 - P.jEps ε l) ≤ (5 / 4 * y ^ 2) * (√2 * Real.exp (-(y ^ 2 / 16))) := by
      have hl3 : 1 + l ^ 2 ≤ 5 / 4 * y ^ 2 := by nlinarith
      refine mul_le_mul hl3 hsmall (by linarith) (by positivity)
    have hfin : 100 * Real.exp (-(y / 4)) ≤ 100 * a⁻¹ * a⁻¹ * Real.exp (-(a / (4 * ε))) * Real.exp (a * l) := by
      have h1 : Real.exp (-(y / 4)) ≤ Real.exp (-(a / (4 * ε))) := by
        apply Real.exp_le_exp.2
        have e : a / (4 * ε) = a * (y / 4) := by rw [hy]; field_simp
        rw [e]
        have hy0 : 0 ≤ y / 4 := by positivity
        nlinarith
      have h2 : (1 : ℝ) ≤ Real.exp (a * l) := Real.one_le_exp (by positivity)
      have hE := Real.exp_pos (-(a / (4 * ε)))
      calc 100 * Real.exp (-(y / 4)) ≤ 100 * Real.exp (-(a / (4 * ε))) := by gcongr
        _ = 100 * 1 * Real.exp (-(a / (4 * ε))) * 1 := by ring
        _ ≤ 100 * (a⁻¹ * a⁻¹) * Real.exp (-(a / (4 * ε))) * Real.exp (a * l) := by gcongr
        _ = _ := by ring
    calc (1 + l ^ 2) * (1 - P.jEps ε l) ≤ (5 / 4 * y ^ 2) * (√2 * Real.exp (-(y ^ 2 / 16))) := hstep1
      _ = (5 / 4) * √2 * (y ^ 2 * Real.exp (-(y ^ 2 / 16))) := by ring
      _ ≤ _ := hexp.trans hfin
  · push_neg at hsm
    have hE := Real.exp_pos (-(a / (4 * ε)))
    have hx : 0 ≤ a * l / 2 := by positivity
    have h1 : 1 + l ^ 2 ≤ 8 * a⁻¹ * a⁻¹ * Real.exp (a * l / 2) := by
      have h2 : 1 + (a * l / 2) + (a * l / 2) ^ 2 / 2 ≤ Real.exp (a * l / 2) := Real.quadratic_le_exp_of_nonneg hx
      have ha0 : a⁻¹ * a ≠ 0 := by positivity
      have e : l ^ 2 = 4 * (a * l / 2) ^ 2 * (a⁻¹ * a⁻¹) := by
        have : a⁻¹ * a = 1 := inv_mul_cancel₀ ha.ne'
        calc l ^ 2 = (a⁻¹ * a) ^ 2 * l ^ 2 := by rw [this]; ring
          _ = _ := by ring
      have h3 : 1 ≤ 8 * (a⁻¹ * a⁻¹) := by nlinarith
      rw [e]
      have h4 : 0 ≤ (a⁻¹ * a⁻¹) := by positivity
      calc 1 + 4 * (a * l / 2) ^ 2 * (a⁻¹ * a⁻¹) ≤ (a⁻¹ * a⁻¹) + 4 * (a * l / 2) ^ 2 * (a⁻¹ * a⁻¹) := by nlinarith
        _ = (a⁻¹ * a⁻¹) * (1 + 4 * (a * l / 2) ^ 2) := by ring
        _ ≤ (a⁻¹ * a⁻¹) * (8 * Real.exp (a * l / 2)) := by
            gcongr
            nlinarith [sq_nonneg (a * l / 2)]
        _ = _ := by ring
    have hj2 : 1 - P.jEps ε l ≤ 1 := by linarith
    have hj3 : 0 ≤ 1 - P.jEps ε l := by linarith
    have h5 : Real.exp (a * l / 2) ≤ Real.exp (-(a / (4 * ε))) * Real.exp (a * l) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      have : a / (4 * ε) < a * l / 2 := by
        have e : a / (4 * ε) = a * (1 / (2 * ε)) / 2 := by field_simp; ring
        rw [e]
        have := mul_lt_mul_of_pos_left hsm ha
        linarith
      linarith
    calc (1 + l ^ 2) * (1 - P.jEps ε l) ≤ (1 + l ^ 2) * 1 := by gcongr
      _ = 1 + l ^ 2 := mul_one _
      _ ≤ 8 * a⁻¹ * a⁻¹ * Real.exp (a * l / 2) := h1
      _ ≤ 8 * a⁻¹ * a⁻¹ * (Real.exp (-(a / (4 * ε))) * Real.exp (a * l)) := by gcongr
      _ ≤ _ := by
        have hp : 0 ≤ a⁻¹ * a⁻¹ * (Real.exp (-(a / (4 * ε))) * Real.exp (a * l)) := by positivity
        nlinarith

end MollProfile

lemma assoc_nonneg (u : L2H') : ∀ᵐ x ∂(specE.assoc u), 0 ≤ x := by
  have h := assoc_Iio_zero u
  rw [ae_iff]
  refine measure_mono_null (fun x hx => ?_) h
  simpa using hx

/-- A bounded symbol dominated by `B e^{a√x}`, applied to an analytic vector. -/
theorem spec_le_exp {k : ℝ → ℂ} (hk : k ∈ BddMeasurable ℝ) {a B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ x, 0 ≤ x → ‖k x‖ ≤ B * Real.exp (a * √x)) {z : L2H'} (hz : z ∈ (expLambda a).domain) :
    ‖specE.integral k z‖ ≤ B * ‖expLambda a ⟨z, hz⟩‖ := by
  set f : ℝ → ℂ := fun s => ((Real.exp (a * Real.sqrt s) : ℝ) : ℂ) with hf
  have hfm : Measurable f :=
    Complex.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul Real.continuous_sqrt.measurable))
  have hz' := hz
  rw [expLambda, functionalCalculus_domain, mem_integralDomain] at hz'
  have h1 := norm_sq_integral_apply specE hk z
  have hz3 : z ∈ integralDomain (spectralMeasure negLapH_isSelfAdjoint) f := by
    have hz2 : z ∈ (functionalCalculus negLapH_isSelfAdjoint f).domain := hz
    rwa [functionalCalculus_domain] at hz2
  have h2 := norm_sq_pmapIntegral (spectralMeasure negLapH_isSelfAdjoint) hfm ⟨z, hz3⟩
  have e2 : ‖expLambda a ⟨z, hz⟩‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂(specE.assoc z) := h2
  have hint : Integrable (fun x => ‖f x‖ ^ 2) (specE.assoc z) :=
    (memLp_two_iff_integrable_sq_norm hfm.aestronglyMeasurable).1 hz'
  have hmono : ∫ x, ‖k x‖ ^ 2 ∂(specE.assoc z) ≤ ∫ x, B ^ 2 * ‖f x‖ ^ 2 ∂(specE.assoc z) := by
    refine integral_mono_ae ?_ (hint.const_mul _) ?_
    · obtain ⟨hkm, C, hC⟩ := (mem_bddMeasurable).1 hk
      refine Integrable.mono' (integrable_const (C ^ 2)) (hkm.norm.pow_const 2).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hC x) 2
    · filter_upwards [assoc_nonneg z] with x hx
      have h3 := hB x hx
      have e : ‖f x‖ = Real.exp (a * √x) := by
        simp only [hf, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      rw [e, ← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) h3 2
  rw [integral_const_mul, ← e2, ← h1] at hmono
  have hp : (‖specE.integral k z‖) ^ 2 ≤ (B * ‖expLambda a ⟨z, hz⟩‖) ^ 2 := by rw [mul_pow]; exact hmono
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hp

lemma Cutoff.norm_J_le_one {χ : Cutoff} (h : ∀ x, |χ.r x| ≤ 1) : ‖χ.J‖ ≤ 1 := by
  refine (specE.norm_integral_le χ.g_mem).trans (ciSup_le fun x => ?_)
  show ‖((χ.r x : ℝ) : ℂ)‖ ≤ 1
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact h x

lemma Cutoff.J_negLapH (χ : Cutoff) (f : negLapH.domain) : χ.J (negLapH f) = χ.JS f := by
  refine ext_inner_left ℂ fun u => ?_
  have e1 : ⟪u, χ.J (negLapH f)⟫_ℂ = ⟪χ.J u, negLapH f⟫_ℂ := by
    have := ContinuousLinearMap.adjoint_inner_left χ.J (negLapH f) u
    rw [χ.adjoint_J] at this
    exact this.symm
  have e2 : ⟪u, χ.JS (f : L2H')⟫_ℂ = ⟪χ.JS u, (f : L2H')⟫_ℂ := by
    have := ContinuousLinearMap.adjoint_inner_left χ.JS (f : L2H') u
    rw [χ.adjoint_JS] at this
    exact this.symm
  rw [e1, e2, ← χ.negLapH_J u]
  exact negLapH_isPositive.1 ⟨χ.J u, χ.J_mem u⟩ f

lemma norm_lapTbar_le {s : ℝ} (hs : 0 ≤ s) (p : graphBar) : ‖lapTbar s p‖ ≤ 4 * ‖p‖ := by
  have he : ‖((Real.exp (-2 * s) : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.2 (by linarith)
  unfold lapTbar
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul]
  have h1 := norm_psiX_le p
  have h2 := norm_psiY_le p
  have hn : 0 ≤ ‖psiX p‖ := norm_nonneg _
  nlinarith [mul_le_mul_of_nonneg_right he hn]

lemma grP_add (u v : negLapH.domain) : grP (u + v) = grP u + grP v := by
  apply Subtype.ext
  simp only [grP, Submodule.coe_add]
  exact Prod.ext rfl (negLapH.map_add u v)

lemma lapTbar_add (s : ℝ) (p q : graphBar) : lapTbar s (p + q) = lapTbar s p + lapTbar s q := by
  simp only [lapTbar, map_add, smul_add]
  abel

section remainder

variable (P : MollProfile) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
include hε hε1

/-- The bound of the symbol of `1 - J`. -/
lemma k0_bound {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) {x : ℝ} (hx : 0 ≤ x) :
    (1 + x) * (1 - P.jEps ε √x) ≤ 100 * a⁻¹ * a⁻¹ * Real.exp (-(a / (4 * ε))) * Real.exp (a * √x) := by
  have h := P.one_sub_jEps_bound hε hε1 ha ha1 (Real.sqrt_nonneg x)
  rwa [Real.sq_sqrt hx] at h

variable {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) {z : L2H'} (hz : z ∈ (expLambda a).domain)
include ha ha1

/-- `(1 - J) z = k₀(-Δ) z`. -/
lemma one_sub_J_eq : z - (P.cutoffEps hε).J z = specE.integral (1 + (-1 : ℂ) • (P.cutoffEps hε).g) z := by
  have h1m : (1 : ℝ → ℂ) ∈ BddMeasurable ℝ := ⟨measurable_one, 1, fun _ => by simp⟩
  rw [specE.integral_add h1m ((BddMeasurable ℝ).smul_mem _ (P.cutoffEps hε).g_mem), specE.integral_one,
    specE.integral_smul _ (P.cutoffEps hε).g_mem]
  simp [sub_eq_add_neg]
  rfl

lemma k0_mem : (1 + (-1 : ℂ) • (P.cutoffEps hε).g) ∈ BddMeasurable ℝ :=
  (BddMeasurable ℝ).add_mem ⟨measurable_one, 1, fun _ => by simp⟩ ((BddMeasurable ℝ).smul_mem _ (P.cutoffEps hε).g_mem)

lemma k0_apply {x : ℝ} (hx : 0 ≤ x) : ‖(1 + (-1 : ℂ) • (P.cutoffEps hε).g) x‖ = 1 - P.jEps ε √x := by
  show ‖(1 : ℂ) + (-1 : ℂ) * ((P.jEps ε (√|x|) : ℝ) : ℂ)‖ = _
  rw [abs_of_nonneg hx]
  have e : (1 : ℂ) + (-1 : ℂ) * ((P.jEps ε √x : ℝ) : ℂ) = ((1 - P.jEps ε √x : ℝ) : ℂ) := by push_cast; ring
  rw [e, Complex.norm_real, Real.norm_of_nonneg (by linarith [P.jEps_le_one ε √x])]

include hz

/-- `‖(1 - J)z‖`. -/
theorem norm_one_sub_J_le : ‖z - (P.cutoffEps hε).J z‖ ≤ 100 * a⁻¹ * a⁻¹ * Real.exp (-(a / (4 * ε))) * ‖expLambda a ⟨z, hz⟩‖ := by
  rw [one_sub_J_eq P hε hε1 ha ha1]
  refine spec_le_exp (k0_mem P hε hε1 ha ha1) (by positivity) (fun x hx => ?_) hz
  rw [k0_apply P hε hε1 ha ha1 hx]
  have h := k0_bound P hε hε1 ha ha1 hx
  have hj : 0 ≤ 1 - P.jEps ε √x := by linarith [P.jEps_le_one ε √x]
  nlinarith

/-- `‖-Δ(1 - J)z‖`. -/
theorem norm_lap_one_sub_J_le {f : negLapH.domain} (hf : (f : L2H') = z - (P.cutoffEps hε).J z) :
    ‖negLapH f‖ ≤ 100 * a⁻¹ * a⁻¹ * Real.exp (-(a / (4 * ε))) * ‖expLambda a ⟨z, hz⟩‖ := by
  have hlev : ∀ n : ℕ, ‖(chiC n 0).J (negLapH f)‖ ≤ 100 * a⁻¹ * a⁻¹ * Real.exp (-(a / (4 * ε))) * ‖expLambda a ⟨z, hz⟩‖ := fun n => by
    rw [Cutoff.J_negLapH, hf, one_sub_J_eq P hε hε1 ha ha1]
    have e : (chiC n 0).JS (specE.integral (1 + (-1 : ℂ) • (P.cutoffEps hε).g) z)
        = specE.integral ((chiC n 0).gS * (1 + (-1 : ℂ) • (P.cutoffEps hε).g)) z := by
      rw [specE.integral_mul (chiC n 0).gS_mem (k0_mem P hε hε1 ha ha1)]
      rfl
    rw [e]
    refine spec_le_exp (mul_mem_B (chiC n 0).gS_mem (k0_mem P hε hε1 ha ha1)) (by positivity) (fun x hx => ?_) hz
    rw [Pi.mul_apply, norm_mul, k0_apply P hε hε1 ha ha1 hx]
    have h := k0_bound P hε hε1 ha ha1 hx
    have hj : 0 ≤ 1 - P.jEps ε √x := by linarith [P.jEps_le_one ε √x]
    have h2 : ‖(chiC (n : ℝ) 0).gS x‖ ≤ 1 + x := by
      show ‖((x * cR n 0 x : ℝ) : ℂ)‖ ≤ _
      rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg hx, cR_zero]
      have h3 := cutR_le_one n x
      have h4 := cutR_nonneg n x
      rw [abs_of_nonneg h4]
      nlinarith
    calc ‖(chiC (n : ℝ) 0).gS x‖ * (1 - P.jEps ε √x) ≤ (1 + x) * (1 - P.jEps ε √x) := mul_le_mul_of_nonneg_right h2 hj
      _ ≤ _ := h
  exact le_of_tendsto' (tendsto_PR (negLapH f)).norm hlev

end remainder

/-- **The unweighted estimate for `Δ_ε(s) - Δ(s)`.** -/
theorem unw_err (P : MollProfile) : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ {ε : ℝ} (hε : 0 < ε), ε ≤ 1 → ∀ {a : ℝ}, 0 < a → a ≤ 1 → ∀ {s : ℝ}, 0 ≤ s →
    ∀ (z : negLapH.domain) (hz : (z : L2H') ∈ (expLambda a).domain),
      ‖(P.cutoffEps hε).lapEps s (z : L2H') - lapTbar s (grP z)‖
        ≤ C₀ * (a⁻¹ * a⁻¹ * a⁻¹ * a⁻¹) * Real.exp (-(a / (8 * ε))) * ‖expLambda a ⟨z, hz⟩‖ := by
  have hτ : (1 : ℝ) < Real.pi / 2 := by linarith [Real.pi_gt_three]
  obtain ⟨C₁, hC, hF⟩ := lem_fc hτ
  set L := (1 + 4 * C₁) ^ 2 with hL
  have hL1 : 1 ≤ L := by rw [hL]; nlinarith [mul_nonneg hC hC]
  refine ⟨800 + 1200 * L, by positivity, fun {ε} hε hε1 {a} ha ha1 {s} hs z hz => ?_⟩
  set χ := P.cutoffEps hε with hχ
  set E := ‖expLambda a ⟨z, hz⟩‖ with hE
  have hE0 : 0 ≤ E := norm_nonneg _
  have hai : 1 ≤ a⁻¹ := (one_le_inv₀ ha).2 ha1
  have hA : AllWords (z : L2H') := fun S => (lem_wc_zero hF hC S ha ha1 hz).1
  set jz : negLapH.domain := ⟨χ.J z, χ.J_mem z⟩ with hjz
  set f : negLapH.domain := z - jz with hf
  have hfv : (f : L2H') = (z : L2H') - χ.J z := rfl
  have hzjf : z = jz + f := by rw [hf]; abel
  have hT : lapTbar s (grP jz) = lapTbar s (grP z) - lapTbar s (grP f) := by
    have e1 : lapTbar s (grP z) = lapTbar s (grP jz) + lapTbar s (grP f) := by
      conv_lhs => rw [hzjf]
      rw [grP_add, lapTbar_add]
    rw [e1]; abel
  have hLeps : χ.lapEps s (z : L2H') = χ.J (lapTbar s (grP jz)) := by
    rw [lapEps_eq]
    congr 1
    show ((Real.exp (-2 * s) : ℝ) : ℂ) • psiX (grJ χ z) + psiY (grJ χ z) = _
    rw [grJ_eq]
    rfl
  set A := 100 * a⁻¹ * a⁻¹ * Real.exp (-(a / (4 * ε))) with hAd
  have n1 : ‖f.1‖ ≤ A * E := by
    show ‖(f : L2H')‖ ≤ _
    rw [hfv]
    exact norm_one_sub_J_le P hε hε1 ha ha1 hz
  have n2 : ‖negLapH f‖ ≤ A * E := norm_lap_one_sub_J_le P hε hε1 ha ha1 hz hfv
  have hTf : ‖lapTbar s (grP f)‖ ≤ 8 * (A * E) := by
    have h := (norm_lapTbar_le hs (grP f)).trans (mul_le_mul_of_nonneg_left (norm_grP_le f) (by norm_num))
    linarith
  have hJ1 : ‖χ.J‖ ≤ 1 := Cutoff.norm_J_le_one fun x => by
    show |P.jEps ε (√|x|)| ≤ 1
    rw [abs_of_nonneg (P.jEps_nonneg _ _)]
    exact P.jEps_le_one _ _
  have hJT : ‖χ.J (lapTbar s (grP f))‖ ≤ ‖lapTbar s (grP f)‖ := by
    refine (χ.J.le_opNorm _).trans ?_
    exact mul_le_of_le_one_left (norm_nonneg _) hJ1
  set a' := a / 2 with ha'
  have ha'0 : 0 < a' := by rw [ha']; linarith
  have ha'1 : a' ≤ 1 := by rw [ha']; linarith
  have hgap : a' < a := by rw [ha']; linarith
  have hw : ∀ S : List Bool, S.length ≤ 2 → ∃ hS : wordAct S (z : L2H') ∈ (expLambda a').domain, ‖expLambda a' ⟨_, hS⟩‖ ≤ L * (a⁻¹ * a⁻¹) * E := fun S hS => by
    obtain ⟨-, hd, hb⟩ := lem_wc_dom hF hC S ha'0.le hgap ha1 hz
    refine ⟨hd, hb.trans (mul_le_mul_of_nonneg_right ?_ hE0)⟩
    have e : a - a' = a / 2 := by rw [ha']; ring
    rw [e]
    have hlen : ((S.length : ℕ) : ℝ) ≤ 2 := by exact_mod_cast hS
    have hbase : C₁ * S.length / (a / 2) ≤ (4 * C₁) * a⁻¹ := by
      have e2 : C₁ * S.length / (a / 2) = (2 * C₁ * S.length) * a⁻¹ := by field_simp
      rw [e2]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      nlinarith
    have hbase0 : 0 ≤ C₁ * S.length / (a / 2) := by positivity
    have hq : (4 * C₁) * a⁻¹ ≤ (1 + 4 * C₁) * a⁻¹ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have hbb := hbase.trans hq
    have hq1 : 1 ≤ (1 + 4 * C₁) * a⁻¹ := by nlinarith
    have hpow : (C₁ * S.length / (a / 2)) ^ S.length ≤ ((1 + 4 * C₁) * a⁻¹) ^ 2 :=
      (pow_le_pow_left₀ hbase0 hbb _).trans (pow_le_pow_right₀ hq1 hS)
    calc _ ≤ ((1 + 4 * C₁) * a⁻¹) ^ 2 := hpow
      _ = L * (a⁻¹ * a⁻¹) := by rw [hL]; ring
  set A' := 100 * a'⁻¹ * a'⁻¹ * Real.exp (-(a' / (4 * ε))) with hA'd
  have hk : ∀ S : List Bool, S.length ≤ 2 → ‖wordAct S (z : L2H') - χ.J (wordAct S (z : L2H'))‖ ≤ A' * (L * (a⁻¹ * a⁻¹) * E) := fun S hS => by
    obtain ⟨hd, hb⟩ := hw S hS
    refine (norm_one_sub_J_le P hε hε1 ha'0 ha'1 hd).trans (mul_le_mul_of_nonneg_left hb (by positivity))
  have hpoly : lapTbar s (grP z) = ((Real.exp (-2 * s) : ℝ) : ℂ) • wordAct [true, true] (z : L2H') + wordAct [false, false] (z : L2H') - wordAct [false] (z : L2H') := by
    have h := lapTbar_eq_polyAct s z hA
    have e : grP z = ⟨((z : L2H'), negLapH z), mem_graphBar_negLapH z⟩ := rfl
    rw [e, h, deltaP, polyAct_cons, polyAct_cons, polyAct_cons, polyAct_nil]
    simp only [one_smul, neg_smul, add_zero]
    abel
  have hsplit : lapTbar s (grP z) - χ.J (lapTbar s (grP z)) = ((Real.exp (-2 * s) : ℝ) : ℂ) • (wordAct [true, true] (z : L2H') - χ.J (wordAct [true, true] (z : L2H')))
      + (wordAct [false, false] (z : L2H') - χ.J (wordAct [false, false] (z : L2H')))
      - (wordAct [false] (z : L2H') - χ.J (wordAct [false] (z : L2H'))) := by
    rw [hpoly]
    simp only [map_add, map_sub, map_smul, smul_sub]
    abel
  have he1 : ‖((Real.exp (-2 * s) : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.2 (by linarith)
  have hk0 : 0 ≤ A' * (L * (a⁻¹ * a⁻¹) * E) := by positivity
  have hTz : ‖lapTbar s (grP z) - χ.J (lapTbar s (grP z))‖ ≤ 3 * (A' * (L * (a⁻¹ * a⁻¹) * E)) := by
    rw [hsplit]
    refine (norm_sub_le _ _).trans ?_
    have h1 := hk [true, true] (by simp)
    have h2 := hk [false, false] (by simp)
    have h3 := hk [false] (by simp)
    have h4 : ‖((Real.exp (-2 * s) : ℝ) : ℂ) • (wordAct [true, true] (z : L2H') - χ.J (wordAct [true, true] (z : L2H')))‖ ≤ A' * (L * (a⁻¹ * a⁻¹) * E) := by
      rw [norm_smul]
      exact (mul_le_of_le_one_left (norm_nonneg _) he1).trans h1
    have h5 := norm_add_le (((Real.exp (-2 * s) : ℝ) : ℂ) • (wordAct [true, true] (z : L2H') - χ.J (wordAct [true, true] (z : L2H'))))
      (wordAct [false, false] (z : L2H') - χ.J (wordAct [false, false] (z : L2H')))
    linarith
  have hid : χ.lapEps s (z : L2H') - lapTbar s (grP z) = -χ.J (lapTbar s (grP f)) - (lapTbar s (grP z) - χ.J (lapTbar s (grP z))) := by
    rw [hLeps, hT, map_sub]
    abel
  rw [hid]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_neg]
  have hA'val : A' = 400 * a⁻¹ * a⁻¹ * Real.exp (-(a / (8 * ε))) := by
    rw [hA'd, ha']
    have e1 : (a / 2) / (4 * ε) = a / (8 * ε) := by field_simp; ring
    rw [e1]
    field_simp
    ring
  have hExp : Real.exp (-(a / (4 * ε))) ≤ Real.exp (-(a / (8 * ε))) := by
    apply Real.exp_le_exp.2
    have : a / (8 * ε) ≤ a / (4 * ε) := by
      apply div_le_div_of_nonneg_left ha.le (by positivity)
      nlinarith
    linarith
  have hexp8 := Real.exp_pos (-(a / (8 * ε)))
  have ha2 : a⁻¹ * a⁻¹ ≤ a⁻¹ * a⁻¹ * a⁻¹ * a⁻¹ := by
    have h : 1 ≤ a⁻¹ * a⁻¹ := by nlinarith
    have hp : 0 ≤ a⁻¹ * a⁻¹ := by positivity
    calc a⁻¹ * a⁻¹ = a⁻¹ * a⁻¹ * 1 := (mul_one _).symm
      _ ≤ a⁻¹ * a⁻¹ * (a⁻¹ * a⁻¹) := mul_le_mul_of_nonneg_left h hp
      _ = _ := by ring
  have t1 : ‖χ.J (lapTbar s (grP f))‖ ≤ 800 * (a⁻¹ * a⁻¹ * a⁻¹ * a⁻¹) * Real.exp (-(a / (8 * ε))) * E := by
    refine hJT.trans (hTf.trans ?_)
    rw [hAd]
    have : 100 * a⁻¹ * a⁻¹ * Real.exp (-(a / (4 * ε))) * E ≤ 100 * (a⁻¹ * a⁻¹ * a⁻¹ * a⁻¹) * Real.exp (-(a / (8 * ε))) * E := by
      have h1 : a⁻¹ * a⁻¹ * Real.exp (-(a / (4 * ε))) ≤ (a⁻¹ * a⁻¹ * a⁻¹ * a⁻¹) * Real.exp (-(a / (8 * ε))) :=
        mul_le_mul ha2 hExp (Real.exp_pos _).le (by positivity)
      calc 100 * a⁻¹ * a⁻¹ * Real.exp (-(a / (4 * ε))) * E = 100 * (a⁻¹ * a⁻¹ * Real.exp (-(a / (4 * ε)))) * E := by ring
        _ ≤ 100 * ((a⁻¹ * a⁻¹ * a⁻¹ * a⁻¹) * Real.exp (-(a / (8 * ε)))) * E := by gcongr
        _ = _ := by ring
    linarith
  have t2 : ‖lapTbar s (grP z) - χ.J (lapTbar s (grP z))‖ ≤ 1200 * L * (a⁻¹ * a⁻¹ * a⁻¹ * a⁻¹) * Real.exp (-(a / (8 * ε))) * E := by
    refine hTz.trans (le_of_eq ?_)
    rw [hA'val]
    ring
  calc _ ≤ 800 * (a⁻¹ * a⁻¹ * a⁻¹ * a⁻¹) * Real.exp (-(a / (8 * ε))) * E + 1200 * L * (a⁻¹ * a⁻¹ * a⁻¹ * a⁻¹) * Real.exp (-(a / (8 * ε))) * E := add_le_add t1 t2
    _ = _ := by ring

end Qschubert
