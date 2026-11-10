import Qschubert.LemmaT
import Qschubert.KLSchur

/-!
# Lemma T2: periodization by Cauchy–Schwarz

`dd_appendix.tex`, Lemma T2 (`lem:t2`). For a Fuchsian `Γ`, `s > 1/2`:

* `perio_weighted`: if `e^{s d(x₀,·)} f ∈ L²(ℍ)`, the orbit sum converges absolutely a.e., `f_Γ ∈ L²(M)`, and
  `‖f_Γ‖² ≤ P_Γ(2s) ‖e^{s d} f‖²`. By pointwise Cauchy–Schwarz and unfolding. This supplies (W1) of
  `subsec:dd-surf` for `ω = X₀^s`.
* `lem_t2`: with `f = (S(t)w) e^{iφ}`, `‖f_Γ‖² ≤ 2^{2s} e^{2s|t|} P_Γ(2s) ‖X₀^s w‖²`.
-/

namespace Qschubert

open MeasureTheory UpperHalfPlane Filter Topology
open scoped ENNReal Pointwise MatrixGroups

/-- Cauchy–Schwarz for `ℝ≥0∞`-valued series. -/
lemma tsum_mul_sq_le {ι : Type*} (f g : ι → ℝ≥0∞) :
    (∑' i, f i * g i) ^ 2 ≤ (∑' i, f i ^ 2) * ∑' i, g i ^ 2 := by
  letI : MeasurableSpace ι := ⊤
  haveI : MeasurableSingletonClass ι := ⟨fun _ => trivial⟩
  have h := lintegral_mul_sq_le (Measure.count : Measure ι) (f := f) (g := g)
    (measurable_from_top).aemeasurable (measurable_from_top).aemeasurable
  simpa only [lintegral_count] using h

/-- `e^{s d(x₀, ·)}`. -/
noncomputable def wtE (x₀ : ℍ) (s : ℝ) (z : ℍ) : ℝ≥0∞ := ENNReal.ofReal (Real.exp (s * dist x₀ z))

lemma measurable_wtE (x₀ : ℍ) (s : ℝ) : Measurable (wtE x₀ s) :=
  ENNReal.measurable_ofReal.comp
    (Real.continuous_exp.comp (continuous_const.mul (continuous_const.dist continuous_id))).measurable

lemma wtE_neg_mul (x₀ : ℍ) (s : ℝ) (z : ℍ) : wtE x₀ (-s) z * wtE x₀ s z = 1 := by
  rw [wtE, wtE, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  simp

lemma wtE_neg_sq (x₀ : ℍ) (s : ℝ) (z : ℍ) :
    wtE x₀ (-s) z ^ 2 = ENNReal.ofReal (Real.exp (-(2 * s * dist x₀ z))) := by
  rw [wtE, ← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul]
  congr 2; push_cast; ring

variable (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ]

/-- Pointwise Cauchy–Schwarz on the orbit. -/
lemma absSum_sq_le [Countable Γ] (x₀ : ℍ) (s : ℝ) (f : ℍ → ℂ) (z : ℍ) :
    absSum Γ f z ^ 2 ≤ poincareSup Γ x₀ (2 * s) * ∑' γ : Γ, (wtE x₀ s (γ • z) * ‖f (γ • z)‖ₑ) ^ 2 := by
  have h := tsum_mul_sq_le (fun γ : Γ => wtE x₀ (-s) (γ • z)) (fun γ : Γ => wtE x₀ s (γ • z) * ‖f (γ • z)‖ₑ)
  have e : ∀ γ : Γ, wtE x₀ (-s) (γ • z) * (wtE x₀ s (γ • z) * ‖f (γ • z)‖ₑ) = ‖f (γ • z)‖ₑ := fun γ => by
    rw [← mul_assoc, wtE_neg_mul, one_mul]
  simp only [e] at h
  refine h.trans (mul_le_mul' ?_ le_rfl)
  simp only [wtE_neg_sq]
  exact le_iSup (fun z : ℍ => ∑' γ : Γ, ENNReal.ofReal (Real.exp (-(2 * s * dist x₀ (γ • z))))) z

lemma tsum_smul_invariant [Countable Γ] (H : ℍ → ℝ≥0∞) (δ : Γ) (z : ℍ) :
    ∑' γ : Γ, H (γ • δ • z) = ∑' γ : Γ, H (γ • z) := by
  rw [← (Equiv.mulRight δ).tsum_eq (fun γ : Γ => H (γ • z))]
  congr 1; funext γ
  simp [mul_smul]

/-- **T2, core.** If `e^{s d} f ∈ L²(ℍ)` then `f_Γ` converges and `‖f_Γ‖² ≤ P_Γ(2s) ‖e^{s d} f‖²`. -/
theorem perio_weighted (x₀ : ℍ) {s : ℝ} (hs : 1 / 2 < s) {f : ℍ → ℂ} (hf : Measurable f)
    (hI : ∫⁻ z, (wtE x₀ s z * ‖f z‖ₑ) ^ 2 ≠ ⊤) :
    (∀ᵐ z ∂(volume : Measure ℍ), z ∈ absSet Γ f) ∧ PerioConv Γ f ∧
      ∫⁻ x, ‖perio Γ f x‖ₑ ^ 2 ∂surfMeasure Γ
        ≤ poincareSup Γ x₀ (2 * s) * ∫⁻ z, (wtE x₀ s z * ‖f z‖ₑ) ^ 2 := by
  haveI : Countable Γ := countable_of_properlyDiscontinuous Γ
  set H : ℍ → ℝ≥0∞ := fun z => (wtE x₀ s z * ‖f z‖ₑ) ^ 2 with hH_def
  have hH : Measurable H := ((measurable_wtE x₀ s).mul hf.enorm).pow_const 2
  set P := poincareSup Γ x₀ (2 * s)
  have hP : P < ⊤ := poincareSup_lt_top Γ x₀ (by linarith)
  set G : ℍ → ℝ≥0∞ := fun z => ∑' γ : Γ, H (γ • z) with hG_def
  have hHγ : ∀ γ : Γ, Measurable fun z : ℍ => H (γ • z) := fun γ => hH.comp (measurable_const_smul γ)
  have hGm : Measurable G := Measurable.ennreal_tsum hHγ
  have hF := isFundamentalDomain_fdSet Γ
  have hunf : ∫⁻ z in fdSet Γ, G z = ∫⁻ z, H z := by
    rw [hF.lintegral_eq_tsum'' H, lintegral_tsum fun γ => (hHγ γ).aemeasurable]
  have hpt : ∀ z, absSum Γ f z ^ 2 ≤ P * G z := absSum_sq_le Γ x₀ s f
  have hae : ∀ᵐ z ∂(volume : Measure ℍ), G z < ⊤ := by
    have h1 : ∀ᵐ z ∂((volume : Measure ℍ).restrict (fdSet Γ)), G z < ⊤ :=
      ae_lt_top hGm (by rw [hunf]; exact hI)
    set N : Set ℍ := {z | G z = ⊤} with hN_def
    have hN : MeasurableSet N := hGm (measurableSet_singleton ⊤)
    have hNF : (volume : Measure ℍ) (N ∩ fdSet Γ) = 0 := by
      rw [← Measure.restrict_apply hN]
      refine measure_mono_null (fun z hz => ?_) (ae_iff.1 h1)
      simp only [Set.mem_setOf_eq, hN_def] at hz ⊢
      rw [hz]; exact lt_irrefl _
    have hinv : ∀ g : Γ, g • N = N := fun g => by
      ext z
      rw [Set.mem_smul_set_iff_inv_smul_mem]
      simp only [hN_def, Set.mem_setOf_eq, hG_def, tsum_smul_invariant Γ H]
    have h0 : (volume : Measure ℍ) N = 0 := hF.measure_zero_of_invariant N hinv hNF
    rw [ae_iff]
    refine measure_mono_null (fun z hz => ?_) h0
    simp only [Set.mem_setOf_eq, hN_def] at hz ⊢
    exact top_le_iff.1 (not_lt.1 hz)
  have hS : ∀ᵐ z ∂(volume : Measure ℍ), z ∈ absSet Γ f := by
    filter_upwards [hae] with z hz
    have h2 : absSum Γ f z ^ 2 < ⊤ := (hpt z).trans_lt (ENNReal.mul_lt_top hP hz)
    show absSum Γ f z < ⊤
    by_contra hc
    rw [top_le_iff.1 (not_lt.1 hc)] at h2
    simp at h2
  have hmeas := aestronglyMeasurable_perio Γ hf hS
  have hAH : Measurable (MulAction.automorphize H : Surf Γ → ℝ≥0∞) :=
    measurable_from_quotient.2 hGm
  have hint : ∫⁻ x, ‖perio Γ f x‖ₑ ^ 2 ∂surfMeasure Γ ≤ P * ∫⁻ z, H z := by
    rw [lintegral_eq_lintegral_automorphize Γ hF hH, ← lintegral_const_mul _ hAH]
    refine lintegral_mono fun x => ?_
    induction x using Quotient.inductionOn with | _ z
    exact (pow_le_pow_left₀ zero_le (enorm_perio_le Γ f _) 2).trans (hpt z)
  have hPI : P * ∫⁻ z, H z ≠ ⊤ := ENNReal.mul_ne_top hP.ne hI
  have hsq : ∫⁻ x, ‖perio Γ f x‖ₑ ^ 2 ∂surfMeasure Γ
      ≤ ENNReal.ofReal (Real.sqrt (P * ∫⁻ z, H z).toReal ^ 2) := by
    rw [Real.sq_sqrt ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hPI]; exact hint
  have hnorm := eLpNorm_two_le_of_lintegral_sq_le hmeas (Real.sqrt_nonneg _) hsq
  refine ⟨hS, ⟨?_, lt_of_le_of_lt hnorm ENNReal.ofReal_lt_top⟩, hint⟩
  filter_upwards [hS] with z hz
  have := ENNReal.summable_toReal (f := fun γ : Γ => ‖f (γ • z)‖ₑ) hz.ne
  simpa [enorm_eq_nnnorm] using this

/-- `e^{s d} ≤ 2^s X₀^s`. -/
lemma wtE_le_coshD (x₀ : ℍ) {s : ℝ} (hs : 0 ≤ s) (z : ℍ) :
    wtE x₀ s z ≤ ENNReal.ofReal (2 ^ s) * ENNReal.ofReal (coshD x₀ z ^ s) := by
  rw [wtE, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← Real.mul_rpow (by norm_num) (coshD_pos x₀ z).le, mul_comm s, Real.exp_mul]
  exact Real.rpow_le_rpow (Real.exp_pos _).le (exp_le_two_coshD x₀ z) hs

/-- `e^{s d(x₀, z)} ≤ e^{s|t|} e^{s d(x₀, δ_t z)}`. -/
lemma wtE_le_dilate (x₀ : ℍ) {s : ℝ} (hs : 0 ≤ s) (t : ℝ) (z : ℍ) :
    wtE x₀ s z ≤ ENNReal.ofReal (Real.exp (s * |t|)) * wtE x₀ s (dilate t z) := by
  rw [wtE, wtE, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
  have h : dist x₀ z ≤ dist x₀ (dilate t z) + dist (dilate t z) z := dist_triangle _ _ _
  rw [dist_comm (dilate t z) z, dist_dilate] at h
  nlinarith

/-- **Lemma T2** (`lem:t2`): `‖[(S(t)w) e^{iφ}]_Γ‖² ≤ 2^{2s} e^{2s|t|} P_Γ(2s) ‖X₀^s w‖²`. -/
theorem lem_t2 (x₀ : ℍ) {s : ℝ} (hs : 1 / 2 < s) (t : ℝ) {ph : ℍ → ℝ} (hph : Measurable ph) {w : ℍ → ℂ}
    (hw : Measurable w) (hI : ∫⁻ z, (ENNReal.ofReal (coshD x₀ z ^ s) * ‖w z‖ₑ) ^ 2 ≠ ⊤) :
    PerioConv Γ (fun z => transportS t w z * Complex.exp (Complex.I * (ph z : ℂ))) ∧
      ∫⁻ x, ‖perio Γ (fun z => transportS t w z * Complex.exp (Complex.I * (ph z : ℂ))) x‖ₑ ^ 2 ∂surfMeasure Γ
        ≤ ENNReal.ofReal (2 ^ (2 * s) * Real.exp (2 * s * |t|)) * poincareSup Γ x₀ (2 * s)
          * ∫⁻ z, (ENNReal.ofReal (coshD x₀ z ^ s) * ‖w z‖ₑ) ^ 2 := by
  have hs0 : 0 ≤ s := by linarith
  set f : ℍ → ℂ := fun z => transportS t w z * Complex.exp (Complex.I * (ph z : ℂ))
  have hf : Measurable f := measurable_transport_phase hw hph
  set J := ∫⁻ z, (ENNReal.ofReal (coshD x₀ z ^ s) * ‖w z‖ₑ) ^ 2 with hJ
  have hc : ENNReal.ofReal (Real.exp (-t / 2)) ^ 2 * ENNReal.ofReal (Real.exp t) = 1 := by
    rw [← ENNReal.ofReal_pow (Real.exp_pos _).le, ← ENNReal.ofReal_mul (by positivity),
      ← Real.exp_nat_mul, ← Real.exp_add]
    simp only [Nat.cast_ofNat]
    rw [show (2 : ℝ) * (-t / 2) + t = 0 by ring]; simp
  have hWm : Measurable fun z : ℍ => (wtE x₀ s z * ‖w z‖ₑ) ^ 2 :=
    ((measurable_wtE x₀ s).mul hw.enorm).pow_const 2
  have hE1 : ∫⁻ z, (wtE x₀ s z * ‖f z‖ₑ) ^ 2
      ≤ ENNReal.ofReal (Real.exp (s * |t|)) ^ 2 * ∫⁻ z, (wtE x₀ s z * ‖w z‖ₑ) ^ 2 := by
    have hpt : ∀ z, (wtE x₀ s z * ‖f z‖ₑ) ^ 2
        ≤ ENNReal.ofReal (Real.exp (s * |t|)) ^ 2 * ENNReal.ofReal (Real.exp (-t / 2)) ^ 2
          * (wtE x₀ s (dilate t z) * ‖w (dilate t z)‖ₑ) ^ 2 := fun z => by
      have e : ‖f z‖ₑ = ENNReal.ofReal (Real.exp (-t / 2)) * ‖w (dilate t z)‖ₑ := by
        rw [← ofReal_norm, norm_transport_phase, ENNReal.ofReal_mul (Real.exp_pos _).le, ofReal_norm]
      rw [e, ← mul_pow, ← mul_pow]
      refine pow_le_pow_left₀ zero_le ?_ 2
      calc wtE x₀ s z * (ENNReal.ofReal (Real.exp (-t / 2)) * ‖w (dilate t z)‖ₑ)
          ≤ (ENNReal.ofReal (Real.exp (s * |t|)) * wtE x₀ s (dilate t z))
              * (ENNReal.ofReal (Real.exp (-t / 2)) * ‖w (dilate t z)‖ₑ) :=
            mul_le_mul' (wtE_le_dilate x₀ hs0 t z) le_rfl
        _ = _ := by ring
    calc ∫⁻ z, (wtE x₀ s z * ‖f z‖ₑ) ^ 2
        ≤ ∫⁻ z, ENNReal.ofReal (Real.exp (s * |t|)) ^ 2 * ENNReal.ofReal (Real.exp (-t / 2)) ^ 2
            * (wtE x₀ s (dilate t z) * ‖w (dilate t z)‖ₑ) ^ 2 := lintegral_mono hpt
      _ = ENNReal.ofReal (Real.exp (s * |t|)) ^ 2 * ENNReal.ofReal (Real.exp (-t / 2)) ^ 2
            * (ENNReal.ofReal (Real.exp t) * ∫⁻ z, (wtE x₀ s z * ‖w z‖ₑ) ^ 2) := by
          rw [lintegral_const_mul (f := fun z => (wtE x₀ s (dilate t z) * ‖w (dilate t z)‖ₑ) ^ 2) _
            (hWm.comp (measurable_dilate t))]
          congr 1
          exact lintegral_comp_dilate t hWm
      _ = _ := by
          rw [← mul_assoc, mul_assoc (ENNReal.ofReal (Real.exp (s * |t|)) ^ 2), hc, mul_one]
  have hE2 : ∫⁻ z, (wtE x₀ s z * ‖w z‖ₑ) ^ 2 ≤ ENNReal.ofReal (2 ^ s) ^ 2 * J := by
    rw [hJ, ← lintegral_const_mul' _ _ (by simp)]
    refine lintegral_mono fun z => ?_
    rw [← mul_pow]
    refine pow_le_pow_left₀ zero_le ?_ 2
    calc wtE x₀ s z * ‖w z‖ₑ
        ≤ (ENNReal.ofReal (2 ^ s) * ENNReal.ofReal (coshD x₀ z ^ s)) * ‖w z‖ₑ :=
          mul_le_mul' (wtE_le_coshD x₀ hs0 z) le_rfl
      _ = _ := by ring
  have htot : ∫⁻ z, (wtE x₀ s z * ‖f z‖ₑ) ^ 2 ≤ ENNReal.ofReal (2 ^ (2 * s) * Real.exp (2 * s * |t|)) * J := by
    refine hE1.trans ((mul_le_mul' le_rfl hE2).trans (le_of_eq ?_))
    rw [← mul_assoc, ← mul_pow, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ← ENNReal.ofReal_pow (by positivity)]
    congr 2
    rw [mul_pow, ← Real.exp_nat_mul, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    push_cast
    rw [mul_comm (Real.exp _)]
    congr 1 <;> [ring_nf; (congr 1; ring)]
  have hfin : ∫⁻ z, (wtE x₀ s z * ‖f z‖ₑ) ^ 2 ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hI) htot
  obtain ⟨-, hconv, hb⟩ := perio_weighted Γ x₀ hs hf hfin
  refine ⟨hconv, hb.trans ?_⟩
  calc poincareSup Γ x₀ (2 * s) * ∫⁻ z, (wtE x₀ s z * ‖f z‖ₑ) ^ 2
      ≤ poincareSup Γ x₀ (2 * s) * (ENNReal.ofReal (2 ^ (2 * s) * Real.exp (2 * s * |t|)) * J) :=
        mul_le_mul' le_rfl htot
    _ = _ := by ring

end Qschubert
