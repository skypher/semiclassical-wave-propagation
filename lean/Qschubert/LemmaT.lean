import Qschubert.PerioMeas
import Qschubert.LemmaTGeom
import Qschubert.LocalSobolev

/-!
# Lemma T: periodization of transported weighted `H²` functions

Manuscript `paper.tex`, Appendix "Periodization for every Fuchsian group", Lemma T: for every
Fuchsian `Γ`, `γ₀ > 1`, `t ≥ 0`, every real phase `φ` and `w` with
`M_w = ‖e^{γ₀ψ̃} w‖_{H²} < ∞`, `‖[(S(t)w) e^{iφ}]_Γ‖_{L²(Γ\ℍ)} ≤ C e^{γ₀t/2} M_w`.

Formal reading (`lemmaT`): `e^{γ₀ψ̃} = X₀^{γ₀}`, `X₀ = cosh d(x₀, ·)`; the `H²` condition is
`X₀^{γ₀} w = U` a.e. for some `U` in the domain of the self-adjoint `-Δ`, with
`M_w = ‖U‖ + ‖(-Δ)U‖` (equivalent to `‖(1 - Δ)U‖` up to the factor `√2`, R71); `w` measurable;
the conclusion is `PerioConv` (absolute a.e. convergence, `L²(M)` membership) and the norm bound.
Proof as in the manuscript: the Sobolev envelope `|w| ≤ K M_w X₀^{-γ₀}` (`sobolev_ae_bound`),
`d(z, S_t z) = t` with `ψ̃` `1`-Lipschitz, Lemma P1 for the `L^∞` bound of the orbit sum, unfolding
for `L¹`, and `‖F‖₂² ≤ ‖F‖_∞ ‖F‖₁` (`lintegral_perio_sq_le`).
-/

namespace Qschubert

open MeasureTheory UpperHalfPlane Filter Topology Physicslib4.Spectral.Unbounded
open scoped ENNReal Pointwise MatrixGroups

local notation "L2H" => Lp ℂ 2 (volume : Measure ℍ)

/-- The envelope: `|w| ≤ K M X₀^{-γ₀}` a.e. -/
lemma envelope_ae (x₀ : ℍ) (γ₀ : ℝ) {w : ℍ → ℂ} (U : negLapH.domain)
    (hU : ⇑(U : L2H) =ᵐ[volume] fun z => ((coshD x₀ z ^ γ₀ : ℝ) : ℂ) * w z) :
    ∀ᵐ z ∂(volume : Measure ℍ),
      ‖w z‖ ≤ Kloc * (‖(U : L2H)‖ + ‖negLapH U‖) * coshD x₀ z ^ (-γ₀) := by
  filter_upwards [sobolev_ae_bound U, hU] with z h1 h2
  rw [h2, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos (coshD_pos x₀ z) _)] at h1
  have hc := Real.rpow_pos_of_pos (coshD_pos x₀ z) γ₀
  rw [Real.rpow_neg (coshD_pos x₀ z).le, ← div_eq_mul_inv, le_div_iff₀ hc]
  linarith

/-- `X₀(S_t z)^{-γ₀} ≤ e^{γ₀ t} X₀(z)^{-γ₀}` for `t ≥ 0`. -/
lemma coshD_dilate_rpow_neg_le (x₀ z : ℍ) {t γ₀ : ℝ} (ht : 0 ≤ t) (hγ : 0 ≤ γ₀) :
    coshD x₀ (dilate t z) ^ (-γ₀) ≤ Real.exp (γ₀ * t) * coshD x₀ z ^ (-γ₀) := by
  have h := coshD_le_exp_mul x₀ z (dilate t z)
  rw [dist_dilate, abs_of_nonneg ht] at h
  have hc := coshD_pos x₀ z
  have hc' := coshD_pos x₀ (dilate t z)
  have hp := Real.rpow_pos_of_pos hc γ₀
  have hp' := Real.rpow_pos_of_pos hc' γ₀
  have key : coshD x₀ z ^ γ₀ ≤ Real.exp (γ₀ * t) * coshD x₀ (dilate t z) ^ γ₀ :=
    calc coshD x₀ z ^ γ₀ ≤ (Real.exp t * coshD x₀ (dilate t z)) ^ γ₀ := Real.rpow_le_rpow hc.le h hγ
      _ = Real.exp (γ₀ * t) * coshD x₀ (dilate t z) ^ γ₀ := by
        rw [Real.mul_rpow (Real.exp_pos t).le hc'.le, ← Real.exp_mul, mul_comm t γ₀]
  rw [Real.rpow_neg hc'.le, Real.rpow_neg hc.le,
    show Real.exp (γ₀ * t) * (coshD x₀ z ^ γ₀)⁻¹ = Real.exp (γ₀ * t) / coshD x₀ z ^ γ₀ from
      (div_eq_mul_inv _ _).symm, inv_eq_one_div, div_le_div_iff₀ hp' hp, one_mul]
  exact key

lemma Kloc_nonneg : 0 ≤ Kloc := by
  unfold Kloc
  have := supCy_nonneg chiT
  have := Kh_nonneg
  positivity

lemma norm_transport_phase (t : ℝ) (w : ℍ → ℂ) (ph : ℍ → ℝ) (z : ℍ) :
    ‖transportS t w z * Complex.exp (Complex.I * (ph z : ℂ))‖ = Real.exp (-t / 2) * ‖w (dilate t z)‖ := by
  rw [norm_mul, mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I, mul_one, transportS, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

lemma measurable_transport_phase {t : ℝ} {w : ℍ → ℂ} (hw : Measurable w) {ph : ℍ → ℝ} (hph : Measurable ph) :
    Measurable fun z => transportS t w z * Complex.exp (Complex.I * (ph z : ℂ)) := by
  unfold transportS
  exact (measurable_const.mul (hw.comp (measurable_dilate t))).mul
    (Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp hph)))

/-- (1) `|S(t)w · e^{iφ}| ≤ A e^{(γ₀ - 1/2)t} X₀^{-γ₀}` a.e. from `|w| ≤ A X₀^{-γ₀}` a.e. -/
lemma transport_phase_ae_le (x₀ : ℍ) {γ₀ t A : ℝ} (ht : 0 ≤ t) (hγ0 : 0 ≤ γ₀) (hA : 0 ≤ A)
    {w : ℍ → ℂ} (ph : ℍ → ℝ) (henv : ∀ᵐ z ∂(volume : Measure ℍ), ‖w z‖ ≤ A * coshD x₀ z ^ (-γ₀)) :
    ∀ᵐ z ∂(volume : Measure ℍ), ‖transportS t w z * Complex.exp (Complex.I * (ph z : ℂ))‖
      ≤ A * Real.exp ((γ₀ - 1 / 2) * t) * coshD x₀ z ^ (-γ₀) := by
  filter_upwards [(quasiMeasurePreserving_dilate t).ae henv] with z hz
  rw [norm_transport_phase]
  have h2 := coshD_dilate_rpow_neg_le x₀ z ht hγ0
  have he : 0 ≤ Real.exp (-t / 2) := (Real.exp_pos _).le
  have h3 : A * coshD x₀ (dilate t z) ^ (-γ₀) ≤ A * (Real.exp (γ₀ * t) * coshD x₀ z ^ (-γ₀)) :=
    mul_le_mul_of_nonneg_left h2 hA
  have h4 : Real.exp (-t / 2) * ‖w (dilate t z)‖ ≤ Real.exp (-t / 2) * (A * (Real.exp (γ₀ * t) * coshD x₀ z ^ (-γ₀))) :=
    mul_le_mul_of_nonneg_left (hz.trans h3) he
  have e : Real.exp (-t / 2) * (A * (Real.exp (γ₀ * t) * coshD x₀ z ^ (-γ₀)))
      = A * Real.exp ((γ₀ - 1 / 2) * t) * coshD x₀ z ^ (-γ₀) := by
    rw [show (γ₀ - 1 / 2) * t = -t / 2 + γ₀ * t by ring, Real.exp_add]
    ring
  exact h4.trans_eq e

/-- (2) The orbit sum: `Σ_γ |F(γz)| ≤ c 2^{γ₀} P` a.e. from `|F| ≤ c X₀^{-γ₀}` a.e. -/
lemma absSum_ae_le (Γ : Subgroup PGL(2, ℝ)) [Countable Γ] (x₀ : ℍ) {γ₀ c : ℝ} (hγ0 : 0 ≤ γ₀) (hc : 0 ≤ c)
    {F : ℍ → ℂ} (hFb : ∀ᵐ z ∂(volume : Measure ℍ), ‖F z‖ ≤ c * coshD x₀ z ^ (-γ₀)) :
    ∀ᵐ z ∂(volume : Measure ℍ), absSum Γ F z ≤ ENNReal.ofReal (c * 2 ^ γ₀) * poincareSup Γ x₀ γ₀ := by
  have hFγ : ∀ᵐ z ∂(volume : Measure ℍ), ∀ γ : Γ, ‖F (γ • z)‖ ≤ c * coshD x₀ (γ • z) ^ (-γ₀) :=
    ae_all_iff.2 fun γ => by
      have h := (measurePreserving_smul γ (volume : Measure ℍ)).quasiMeasurePreserving.ae hFb
      exact h
  have h2 : (0 : ℝ) ≤ 2 ^ γ₀ := Real.rpow_nonneg (by norm_num) _
  filter_upwards [hFγ] with z hz
  have hterm : ∀ γ : Γ, ‖F (γ • z)‖ₑ
      ≤ ENNReal.ofReal (c * 2 ^ γ₀) * ENNReal.ofReal (Real.exp (-(γ₀ * dist x₀ (γ • z)))) := by
    intro γ
    rw [← ofReal_norm, ← ENNReal.ofReal_mul (mul_nonneg hc h2)]
    refine ENNReal.ofReal_le_ofReal ((hz γ).trans ?_)
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (coshD_rpow_neg_le x₀ (γ • z) hγ0) hc
  calc absSum Γ F z ≤ ∑' γ : Γ, ENNReal.ofReal (c * 2 ^ γ₀) *
        ENNReal.ofReal (Real.exp (-(γ₀ * dist x₀ (γ • z)))) := ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (c * 2 ^ γ₀) * ∑' γ : Γ, ENNReal.ofReal (Real.exp (-(γ₀ * dist x₀ (γ • z)))) :=
        ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal (c * 2 ^ γ₀) * poincareSup Γ x₀ γ₀ :=
        mul_le_mul' le_rfl (le_iSup (fun z : ℍ => ∑' γ : Γ,
          ENNReal.ofReal (Real.exp (-(γ₀ * dist x₀ (γ • z))))) z)

/-- (3) `L¹`: `∫ |S(t)w · e^{iφ}| ≤ e^{t/2} A ∫ X₀^{-γ₀}` from `|w| ≤ A X₀^{-γ₀}` a.e. -/
lemma lintegral_transport_phase_le (x₀ : ℍ) {γ₀ t A : ℝ} (hA : 0 ≤ A) {w : ℍ → ℂ} (hw : Measurable w)
    (ph : ℍ → ℝ) (henv : ∀ᵐ z ∂(volume : Measure ℍ), ‖w z‖ ≤ A * coshD x₀ z ^ (-γ₀)) :
    ∫⁻ z, ‖transportS t w z * Complex.exp (Complex.I * (ph z : ℂ))‖ₑ
      ≤ ENNReal.ofReal (Real.exp (t / 2) * A) * ∫⁻ z, ENNReal.ofReal (coshD x₀ z ^ (-γ₀)) := by
  have hmc : Measurable fun z : ℍ => ENNReal.ofReal (coshD x₀ z ^ (-γ₀)) :=
    ENNReal.measurable_ofReal.comp
      ((Real.continuous_cosh.comp (continuous_const.dist continuous_id)).measurable.pow_const _)
  have e1 : (fun z => ‖transportS t w z * Complex.exp (Complex.I * (ph z : ℂ))‖ₑ)
      = fun z => ENNReal.ofReal (Real.exp (-t / 2)) * ‖w (dilate t z)‖ₑ := by
    funext z
    rw [← ofReal_norm, norm_transport_phase, ENNReal.ofReal_mul (Real.exp_pos _).le, ofReal_norm]
  have henv' : ∀ᵐ z ∂(volume : Measure ℍ),
      ‖w z‖ₑ ≤ ENNReal.ofReal A * ENNReal.ofReal (coshD x₀ z ^ (-γ₀)) := by
    filter_upwards [henv] with z hz
    rw [← ofReal_norm, ← ENNReal.ofReal_mul hA]
    exact ENNReal.ofReal_le_ofReal hz
  have hint : ∫⁻ z, ‖w z‖ₑ ≤ ENNReal.ofReal A * ∫⁻ z, ENNReal.ofReal (coshD x₀ z ^ (-γ₀)) := by
    rw [← lintegral_const_mul _ hmc]
    exact lintegral_mono_ae henv'
  have hexp : ENNReal.ofReal (Real.exp (-t / 2)) * ENNReal.ofReal (Real.exp t) * ENNReal.ofReal A
      = ENNReal.ofReal (Real.exp (t / 2) * A) := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
      ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    congr 2; ring
  have hmw : Measurable fun z => ‖w (dilate t z)‖ₑ := (hw.comp (measurable_dilate t)).enorm
  rw [e1, lintegral_const_mul _ hmw, lintegral_comp_dilate t hw.enorm, ← mul_assoc]
  calc ENNReal.ofReal (Real.exp (-t / 2)) * ENNReal.ofReal (Real.exp t) * ∫⁻ z, ‖w z‖ₑ
      ≤ ENNReal.ofReal (Real.exp (-t / 2)) * ENNReal.ofReal (Real.exp t) *
          (ENNReal.ofReal A * ∫⁻ z, ENNReal.ofReal (coshD x₀ z ^ (-γ₀))) := mul_le_mul' le_rfl hint
    _ = ENNReal.ofReal (Real.exp (t / 2) * A) * ∫⁻ z, ENNReal.ofReal (coshD x₀ z ^ (-γ₀)) := by
        rw [← mul_assoc, hexp]

/-- (4) From the square integral to `eLpNorm`. -/
lemma eLpNorm_two_le_of_lintegral_sq_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℂ}
    (hf : AEStronglyMeasurable f μ) {a : ℝ} (ha : 0 ≤ a)
    (h : ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal (a ^ 2)) : eLpNorm f 2 μ ≤ ENNReal.ofReal a := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top hf, ENNReal.toReal_ofNat]
  have e : ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ := by simp_rw [ENNReal.rpow_two]
  rw [e]
  calc (∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ) ^ (1 / (2 : ℝ)) ≤ (ENNReal.ofReal (a ^ 2)) ^ (1 / (2 : ℝ)) :=
        ENNReal.rpow_le_rpow h (by norm_num)
    _ = ENNReal.ofReal a := by
        rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg _) (by norm_num), ← Real.sqrt_eq_rpow, Real.sqrt_sq ha]

/-- (5) The constant: `(c 2^{γ₀} P)(e^{t/2} A I) = (√(2^{γ₀}(PI)) e^{γ₀t/2} A)²` with
`c = A e^{(γ₀ - 1/2)t}`. -/
lemma lemmaT_const {A γ₀ t : ℝ} (hA : 0 ≤ A) {P I : ℝ≥0∞} (hPI : P * I ≠ ⊤) :
    ENNReal.ofReal (A * Real.exp ((γ₀ - 1 / 2) * t) * 2 ^ γ₀) * P * (ENNReal.ofReal (Real.exp (t / 2) * A) * I)
      = ENNReal.ofReal ((Real.sqrt (2 ^ γ₀ * (P * I).toReal) * Real.exp (γ₀ * t / 2) * A) ^ 2) := by
  have h2 : (0 : ℝ) ≤ 2 ^ γ₀ := Real.rpow_nonneg (by norm_num) _
  have hQ : 0 ≤ 2 ^ γ₀ * (P * I).toReal := mul_nonneg h2 ENNReal.toReal_nonneg
  have hexp : Real.exp (γ₀ * t / 2) ^ 2 = Real.exp ((γ₀ - 1 / 2) * t) * Real.exp (t / 2) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
  have e : (Real.sqrt (2 ^ γ₀ * (P * I).toReal) * Real.exp (γ₀ * t / 2) * A) ^ 2
      = (A * Real.exp ((γ₀ - 1 / 2) * t) * 2 ^ γ₀) * (Real.exp (t / 2) * A) * (P * I).toReal := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hQ, hexp]
    ring
  have hc : 0 ≤ A * Real.exp ((γ₀ - 1 / 2) * t) * 2 ^ γ₀ := mul_nonneg (mul_nonneg hA (Real.exp_pos _).le) h2
  have hd : 0 ≤ Real.exp (t / 2) * A := mul_nonneg (Real.exp_pos _).le hA
  rw [e, ENNReal.ofReal_mul (mul_nonneg hc hd), ENNReal.ofReal_toReal hPI, ENNReal.ofReal_mul hc]
  ring

/-- **Lemma T.** -/
theorem lemmaT (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ] (x₀ : ℍ) {γ₀ : ℝ} (hγ : 1 < γ₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t → ∀ ph : ℍ → ℝ, Measurable ph → ∀ w : ℍ → ℂ, Measurable w →
      ∀ U : negLapH.domain, (⇑(U : L2H) =ᵐ[volume] fun z => ((coshD x₀ z ^ γ₀ : ℝ) : ℂ) * w z) →
        PerioConv Γ (fun z => transportS t w z * Complex.exp (Complex.I * (ph z : ℂ))) ∧
        eLpNorm (perio Γ (fun z => transportS t w z * Complex.exp (Complex.I * (ph z : ℂ)))) 2 (surfMeasure Γ)
          ≤ ENNReal.ofReal (C * Real.exp (γ₀ * t / 2) * (‖(U : L2H)‖ + ‖negLapH U‖)) := by
  haveI : Countable Γ := countable_of_properlyDiscontinuous Γ
  have hγ0 : 0 ≤ γ₀ := by linarith
  have hP : poincareSup Γ x₀ γ₀ < ⊤ := poincareSup_lt_top Γ x₀ hγ
  have hI : ∫⁻ z, ENNReal.ofReal (coshD x₀ z ^ (-γ₀)) < ⊤ := lintegral_coshD_rpow_neg_lt_top x₀ hγ
  have hPI : poincareSup Γ x₀ γ₀ * ∫⁻ z, ENNReal.ofReal (coshD x₀ z ^ (-γ₀)) ≠ ⊤ :=
    ENNReal.mul_ne_top hP.ne hI.ne
  refine ⟨Kloc * Real.sqrt (2 ^ γ₀ * (poincareSup Γ x₀ γ₀ * ∫⁻ z, ENNReal.ofReal (coshD x₀ z ^ (-γ₀))).toReal),
    mul_nonneg Kloc_nonneg (Real.sqrt_nonneg _), ?_⟩
  intro t ht ph hph w hw U hU
  have hM : 0 ≤ ‖(U : L2H)‖ + ‖negLapH U‖ := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hA : 0 ≤ Kloc * (‖(U : L2H)‖ + ‖negLapH U‖) := mul_nonneg Kloc_nonneg hM
  have hFm := measurable_transport_phase (t := t) hw hph
  have henv := envelope_ae x₀ γ₀ U hU
  have hFb := transport_phase_ae_le x₀ ht hγ0 hA ph henv
  have hc : 0 ≤ Kloc * (‖(U : L2H)‖ + ‖negLapH U‖) * Real.exp ((γ₀ - 1 / 2) * t) :=
    mul_nonneg hA (Real.exp_pos _).le
  have hAbs := absSum_ae_le Γ x₀ hγ0 hc hFb
  have hLtop : ENNReal.ofReal (Kloc * (‖(U : L2H)‖ + ‖negLapH U‖) * Real.exp ((γ₀ - 1 / 2) * t) * 2 ^ γ₀)
      * poincareSup Γ x₀ γ₀ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hP
  have hS : ∀ᵐ z ∂(volume : Measure ℍ),
      z ∈ absSet Γ (fun z => transportS t w z * Complex.exp (Complex.I * (ph z : ℂ))) := by
    filter_upwards [hAbs] with z hz
    exact lt_of_le_of_lt hz hLtop
  have hL1 := lintegral_transport_phase_le x₀ hA hw ph henv (t := t)
  have hmeas := aestronglyMeasurable_perio Γ hFm hS
  have hsq := (lintegral_perio_sq_le Γ hFm hAbs).trans (mul_le_mul' le_rfl hL1)
  rw [lemmaT_const hA hPI] at hsq
  have hnorm := eLpNorm_two_le_of_lintegral_sq_le hmeas (by positivity) hsq
  have heq : Real.sqrt (2 ^ γ₀ * (poincareSup Γ x₀ γ₀ * ∫⁻ z, ENNReal.ofReal (coshD x₀ z ^ (-γ₀))).toReal)
        * Real.exp (γ₀ * t / 2) * (Kloc * (‖(U : L2H)‖ + ‖negLapH U‖))
      = Kloc * Real.sqrt (2 ^ γ₀ * (poincareSup Γ x₀ γ₀ * ∫⁻ z, ENNReal.ofReal (coshD x₀ z ^ (-γ₀))).toReal)
        * Real.exp (γ₀ * t / 2) * (‖(U : L2H)‖ + ‖negLapH U‖) := by ring
  rw [heq] at hnorm
  refine ⟨⟨?_, lt_of_le_of_lt hnorm ENNReal.ofReal_lt_top⟩, hnorm⟩
  filter_upwards [hS] with z hz
  have := ENNReal.summable_toReal
    (f := fun γ : Γ => ‖transportS t w (γ • z) * Complex.exp (Complex.I * (ph (γ • z) : ℂ))‖ₑ) hz.ne
  simpa [enorm_eq_nnnorm] using this

end Qschubert
