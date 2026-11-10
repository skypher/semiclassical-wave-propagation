import Qschubert.TransportCont
import Qschubert.LaplacianOp

/-!
# The generator of `S(t)` on test functions

For a test function `F`, `yF := (Y - 1/2)F`, `Y = y ∂_y` (`genYTest`), is again a test function, and
`t ↦ S(t) F` is differentiable in `L²(ℍ)` with derivative `S(t)(Y - 1/2)F` (`hasDerivAt_transportLp`).
-/

namespace Qschubert

open MeasureTheory UpperHalfPlane Real Filter Topology
open scoped ENNReal ContDiff

/-- `(Y - 1/2) F = y ∂_y F - F/2` on `ℂ`. -/
noncomputable def genYFun (F : ℂ → ℂ) (w : ℂ) : ℂ :=
  ((w.im : ℝ) : ℂ) * fderiv ℝ F w Complex.I - F w / 2

lemma isTestFn_genYFun {F : ℂ → ℂ} (hF : IsTestFn F) : IsTestFn (genYFun F) := by
  have hsub : tsupport (genYFun F) ⊆ tsupport F := by
    refine (tsupport_sub _ _).trans (Set.union_subset ?_ ?_)
    · exact (tsupport_mul_subset_right (f := fun w : ℂ => ((w.im : ℝ) : ℂ))).trans
        (tsupport_fderiv_apply_subset (𝕜 := ℝ) Complex.I)
    · exact tsupport_comp_subset (g := fun z : ℂ => z / 2) (by simp) F
  refine ⟨?_, IsCompact.of_isClosed_subset hF.compact (isClosed_tsupport _) hsub, hsub.trans hF.inside⟩
  have him : ContDiff ℝ ∞ fun w : ℂ => ((w.im : ℝ) : ℂ) := (Complex.ofRealCLM.comp Complex.imCLM).contDiff
  have hd : ContDiff ℝ ∞ fun w => fderiv ℝ F w Complex.I :=
    (hF.smooth.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const
  exact (him.mul hd).sub (hF.smooth.div_const 2)

/-- `(Y - 1/2)F` as a test function. -/
noncomputable def genYTest (F : testFn) : testFn := ⟨genYFun F, isTestFn_genYFun F.2⟩

lemma hasDerivAt_dilL_apply (w : ℂ) (r : ℝ) :
    HasDerivAt (fun r : ℝ => dilL r w) (((Real.exp r * w.im : ℝ) : ℂ) * Complex.I) r := by
  have e : (fun r : ℝ => dilL r w) = fun r : ℝ => ((w.re : ℝ) : ℂ) + ((Real.exp r * w.im : ℝ) : ℂ) * Complex.I := by
    funext r; apply Complex.ext <;> simp [dilL_apply, Complex.exp_ofReal_re]
  rw [e]
  have h1 : HasDerivAt (fun r : ℝ => ((Real.exp r * w.im : ℝ) : ℂ)) ((Real.exp r * w.im : ℝ) : ℂ) r :=
    ((Real.hasDerivAt_exp r).mul_const w.im).ofReal_comp
  simpa using (h1.mul_const Complex.I).const_add ((w.re : ℝ) : ℂ)

/-- Pointwise generator: `d/dr S(r)F(z) = S(r)(Y - 1/2)F(z)`. -/
lemma hasDerivAt_transportS_apply (F : testFn) (z : ℍ) (r : ℝ) :
    HasDerivAt (fun r => transportS r (fun w : ℍ => (F : ℂ → ℂ) w) z)
      (transportS r (fun w : ℍ => (genYTest F : ℂ → ℂ) w) z) r := by
  have hF : ContDiff ℝ ∞ (F : ℂ → ℂ) := F.2.smooth
  have hS : ∀ r', transportS r' (fun w : ℍ => (F : ℂ → ℂ) w) z
      = ((Real.exp (-r' / 2) : ℝ) : ℂ) * (F : ℂ → ℂ) (dilL r' (z : ℂ)) := fun r' => rfl
  have hSG : transportS r (fun w : ℍ => (genYTest F : ℂ → ℂ) w) z
      = ((Real.exp (-r / 2) : ℝ) : ℂ) * genYFun F (dilL r (z : ℂ)) := rfl
  simp_rw [hS]
  rw [hSG]
  have hd : HasDerivAt (fun r' : ℝ => (F : ℂ → ℂ) (dilL r' (z : ℂ)))
      (fderiv ℝ (F : ℂ → ℂ) (dilL r (z : ℂ)) (((Real.exp r * (z : ℂ).im : ℝ) : ℂ) * Complex.I)) r :=
    ((hF.differentiable (by simp)) _).hasFDerivAt.comp_hasDerivAt r (hasDerivAt_dilL_apply _ r)
  have he : HasDerivAt (fun r' : ℝ => ((Real.exp (-r' / 2) : ℝ) : ℂ))
      ((Real.exp (-r / 2) * (-1 / 2) : ℝ) : ℂ) r := by
    have := ((Real.hasDerivAt_exp (-r / 2)).comp r ((hasDerivAt_neg r).div_const 2)).ofReal_comp
    simpa using this
  convert he.mul hd using 1
  simp only [genYFun, dilL_apply]
  rw [show (((Real.exp r * (z : ℂ).im : ℝ) : ℂ) * Complex.I)
      = ((Real.exp r * (z : ℂ).im : ℝ) : ℝ) • Complex.I by rw [Complex.real_smul],
    ContinuousLinearMap.map_smul_of_tower]
  simp only [Complex.real_smul]
  push_cast
  ring

/-- `∫ |h⁻¹(S(t+h)F - S(t)F) - S(t)(Y - 1/2)F|² → 0` as `h → 0`, `h ≠ 0`. -/
lemma tendsto_lintegral_slope_transportS (F : testFn) (t : ℝ) :
    Tendsto (fun h : ℝ => ∫⁻ z, ‖h⁻¹ • (transportS (t + h) (fun w : ℍ => (F : ℂ → ℂ) w) z
      - transportS t (fun w : ℍ => (F : ℂ → ℂ) w) z)
      - transportS t (fun w : ℍ => (genYTest F : ℂ → ℂ) w) z‖ₑ ^ (2 : ℝ)) (𝓝[≠] 0) (𝓝 0) := by
  set a : ℍ → ℂ := fun w => (F : ℂ → ℂ) w with ha
  set b : ℍ → ℂ := fun w => (genYTest F : ℂ → ℂ) w with hb
  have hac : Continuous a := F.2.smooth.continuous.comp UpperHalfPlane.continuous_coe
  have hbc : Continuous b := (genYTest F).2.smooth.continuous.comp UpperHalfPlane.continuous_coe
  have hacs : HasCompactSupport a := hasCompactSupport_comp_coe F.2
  have hbcs : HasCompactSupport b := hasCompactSupport_comp_coe (genYTest F).2
  obtain ⟨C, hC⟩ := hbc.bounded_above_of_compact_support hbcs
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC (Classical.choice inferInstance))
  set K' : Set ℍ := (fun p : ℝ × ℍ => dilate (-p.1) p.2) ''
    (Set.Icc (t - 1) (t + 1) ×ˢ (tsupport a ∪ tsupport b))
  have hK' : IsCompact K' := (isCompact_Icc.prod (hacs.union hbcs)).image
    (continuous_dilate_joint.comp (continuous_fst.neg.prodMk continuous_snd))
  have hmema : ∀ r ∈ Set.Icc (t - 1) (t + 1), ∀ z, a (dilate r z) ≠ 0 → z ∈ K' := by
    intro r hr z hz
    exact ⟨(r, dilate r z), ⟨hr, Or.inl (subset_tsupport _ hz)⟩, dilate_neg_left r z⟩
  have hmemb : ∀ r ∈ Set.Icc (t - 1) (t + 1), ∀ z, b (dilate r z) ≠ 0 → z ∈ K' := by
    intro r hr z hz
    exact ⟨(r, dilate r z), ⟨hr, Or.inr (subset_tsupport _ hz)⟩, dilate_neg_left r z⟩
  have ht : t ∈ Set.Icc (t - 1) (t + 1) := ⟨by linarith, by linarith⟩
  set E : ℝ := Real.exp ((|t| + 1) / 2)
  set B : ℝ := (2 * (E * C)) ^ 2
  have hexp : ∀ r ∈ Set.Icc (t - 1) (t + 1), Real.exp (-r / 2) ≤ E := by
    intro r hr
    apply Real.exp_le_exp.2
    have := neg_abs_le t
    linarith [hr.1, hr.2]
  have hbd : ∀ z, ∀ r ∈ Set.Icc (t - 1) (t + 1), ‖transportS r b z‖ ≤ E * C := by
    intro z r hr
    unfold transportS
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul (hexp r hr) (hC _) (norm_nonneg _) (Real.exp_pos _).le
  have hcontS : ∀ (c : ℍ → ℂ), Continuous c → ∀ r, Continuous fun z => transportS r c z := by
    intro c hc r
    unfold transportS
    exact continuous_const.mul (hc.comp (continuous_dilate_joint.comp (continuous_const.prodMk continuous_id)))
  have hfin : ∫⁻ z, K'.indicator (fun _ => ENNReal.ofReal B) z ≠ ⊤ := by
    rw [lintegral_indicator_const hK'.measurableSet]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hK'.measure_lt_top.ne
  have h0 : (0 : ℝ≥0∞) = ∫⁻ z : ℍ, (0 : ℝ≥0∞) := by simp
  rw [h0]
  refine tendsto_lintegral_filter_of_dominated_convergence
    (fun z => K'.indicator (fun _ => ENNReal.ofReal B) z) ?_ ?_ hfin ?_
  · refine Eventually.of_forall fun h => ?_
    exact (((((hcontS a hac (t + h)).sub (hcontS a hac t)).const_smul h⁻¹).sub
      (hcontS b hbc t)).enorm.measurable.pow_const _)
  · have hI : Set.Icc (-1 : ℝ) 1 ∈ 𝓝[≠] (0 : ℝ) :=
      nhdsWithin_le_nhds (Icc_mem_nhds (by norm_num) (by norm_num))
    filter_upwards [hI, self_mem_nhdsWithin] with h hh hne
    have hne' : h ≠ 0 := hne
    have hth : t + h ∈ Set.Icc (t - 1) (t + 1) := ⟨by linarith [hh.1], by linarith [hh.2]⟩
    refine Eventually.of_forall fun z => ?_
    by_cases hz : z ∈ K'
    · rw [Set.indicator_of_mem hz, ← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hmvt : ‖transportS (t + h) a z - transportS t a z‖ ≤ E * C * ‖(t + h) - t‖ :=
        (convex_Icc (t - 1) (t + 1)).norm_image_sub_le_of_norm_hasDerivWithin_le
          (f := fun r => transportS r a z) (f' := fun r => transportS r b z)
          (fun r _ => (hasDerivAt_transportS_apply F z r).hasDerivWithinAt)
          (fun r hr => hbd z r hr) ht hth
      have hq : ‖h⁻¹ • (transportS (t + h) a z - transportS t a z)‖ ≤ E * C := by
        rw [norm_smul, norm_inv]
        have hpos : 0 < ‖h‖ := norm_pos_iff.2 hne'
        rw [show (t + h) - t = h by ring] at hmvt
        calc ‖h‖⁻¹ * ‖transportS (t + h) a z - transportS t a z‖ ≤ ‖h‖⁻¹ * (E * C * ‖h‖) :=
              mul_le_mul_of_nonneg_left hmvt (inv_nonneg.2 hpos.le)
          _ = E * C := by field_simp
      have h2 : ‖h⁻¹ • (transportS (t + h) a z - transportS t a z) - transportS t b z‖ ≤ 2 * (E * C) := by
        calc _ ≤ ‖h⁻¹ • (transportS (t + h) a z - transportS t a z)‖ + ‖transportS t b z‖ :=
              norm_sub_le _ _
          _ ≤ 2 * (E * C) := by linarith [hbd z t ht]
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      exact pow_le_pow_left₀ (norm_nonneg _) h2 2
    · rw [Set.indicator_of_notMem hz]
      have ht0 : a (dilate (t + h) z) = 0 := by by_contra hc; exact hz (hmema _ hth z hc)
      have hs0 : a (dilate t z) = 0 := by by_contra hc; exact hz (hmema t ht z hc)
      have hb0 : b (dilate t z) = 0 := by by_contra hc; exact hz (hmemb t ht z hc)
      simp [transportS, ht0, hs0, hb0]
  · refine Eventually.of_forall fun z => ?_
    have hd := (hasDerivAt_iff_tendsto_slope_zero.1 (hasDerivAt_transportS_apply F z t))
    have h1 := ((hd.sub (tendsto_const_nhds (x := transportS t b z))).enorm)
    rw [sub_self, enorm_zero] at h1
    have h2 := (ENNReal.continuous_rpow_const (y := (2 : ℝ))).tendsto _ |>.comp h1
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h2
    simpa [Function.comp_def] using h2

/-- **Generator of `S(t)` on test functions**: `d/dt S(t)F = S(t)(Y - 1/2)F` in `L²(ℍ)`. -/
theorem hasDerivAt_transportLp (F : testFn) (t : ℝ) :
    HasDerivAt (fun r => transportLp r (toL2 F)) (transportLp t (toL2 (genYTest F))) t := by
  rw [hasDerivAt_iff_tendsto_slope_zero, Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  set a : ℍ → ℂ := fun w => (F : ℂ → ℂ) w with ha
  set b : ℍ → ℂ := fun w => (genYTest F : ℂ → ℂ) w with hb
  have hFa : ⇑(toL2 F) =ᵐ[volume] a := (memLp_comp_coe F.2).coeFn_toLp
  have hGb : ⇑(toL2 (genYTest F)) =ᵐ[volume] b := (memLp_comp_coe (genYTest F).2).coeFn_toLp
  have e : ∀ h : ℝ, eLpNorm (⇑(h⁻¹ • (transportLp (t + h) (toL2 F) - transportLp t (toL2 F)))
      - ⇑(transportLp t (toL2 (genYTest F)))) 2 volume
      = (∫⁻ z, ‖h⁻¹ • (transportS (t + h) a z - transportS t a z) - transportS t b z‖ₑ ^ (2 : ℝ))
        ^ (1 / (2 : ℝ)) := by
    intro h
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top
      ((Lp.aestronglyMeasurable _).sub (Lp.aestronglyMeasurable _)), ENNReal.toReal_ofNat]
    congr 1
    refine lintegral_congr_ae ?_
    filter_upwards [Lp.coeFn_smul h⁻¹ (transportLp (t + h) (toL2 F) - transportLp t (toL2 F)),
      Lp.coeFn_sub (transportLp (t + h) (toL2 F)) (transportLp t (toL2 F)),
      transportLp_ae (t + h) (toL2 F), transportLp_ae t (toL2 F), transportLp_ae t (toL2 (genYTest F)),
      transportS_ae_congr (t + h) hFa, transportS_ae_congr t hFa, transportS_ae_congr t hGb]
      with z h1 h2 h3 h4 h5 h6 h7 h8
    simp only [Pi.sub_apply, Pi.smul_apply, h1, h2, h3, h4, h5, h6, h7, h8]
  simp_rw [e]
  have h := (ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ))).tendsto 0 |>.comp
    (tendsto_lintegral_slope_transportS F t)
  rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h
  exact h

end Qschubert
