import Qschubert.Transport
import Qschubert.TestFnDense

/-!
# `S(t)` is strongly continuous on `L²(ℍ)`

For continuous compactly supported `a`, `‖S(t)a - S(s)a‖ → 0` as `t → s` by dominated convergence
(`tendsto_transportLp_of_cc`); with `‖S(t)‖ = 1` and the density of test functions this gives strong
continuity of `t ↦ S(t) f` for every `f ∈ L²(ℍ)` (`continuous_transportLp_apply`).
-/

namespace Qschubert

open MeasureTheory UpperHalfPlane Real Filter Topology
open scoped ENNReal

lemma continuous_dilate_joint : Continuous fun p : ℝ × ℍ => dilate p.1 p.2 := by
  rw [UpperHalfPlane.isEmbedding_coe.continuous_iff]
  have e : (UpperHalfPlane.coe ∘ fun p : ℝ × ℍ => dilate p.1 p.2)
      = fun p : ℝ × ℍ => (((p.2 : ℂ).re : ℝ) : ℂ) + ((Real.exp p.1 * (p.2 : ℂ).im : ℝ) : ℂ) * Complex.I := by
    funext p
    apply Complex.ext <;> simp [dilate, Complex.exp_ofReal_re]
  rw [e]
  have h1 : Continuous fun p : ℝ × ℍ => (p.2 : ℂ) := UpperHalfPlane.continuous_coe.comp continuous_snd
  fun_prop

lemma continuous_transportS_apply {a : ℍ → ℂ} (hc : Continuous a) (z : ℍ) :
    Continuous fun t => transportS t a z := by
  unfold transportS
  have : Continuous fun t : ℝ => dilate t z := continuous_dilate_joint.comp (continuous_id.prodMk continuous_const)
  exact (Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_id.neg.div_const 2))).mul
    (hc.comp this)

lemma dilate_neg_left (t : ℝ) (z : ℍ) : dilate (-t) (dilate t z) = z := by
  simpa using dilate_neg (-t) z

/-- `∫ |S(t)a - S(s)a|² → 0` as `t → s`, for continuous compactly supported `a`. -/
lemma tendsto_lintegral_transportS {a : ℍ → ℂ} (hc : Continuous a) (hcs : HasCompactSupport a) (s : ℝ) :
    Tendsto (fun t => ∫⁻ z, ‖transportS t a z - transportS s a z‖ₑ ^ (2 : ℝ)) (𝓝 s) (𝓝 0) := by
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hcs
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC (Classical.choice inferInstance))
  set K' : Set ℍ := (fun p : ℝ × ℍ => dilate (-p.1) p.2) '' (Set.Icc (s - 1) (s + 1) ×ˢ tsupport a)
  have hK' : IsCompact K' := (isCompact_Icc.prod hcs).image
    (continuous_dilate_joint.comp (continuous_fst.neg.prodMk continuous_snd))
  have hmem : ∀ t ∈ Set.Icc (s - 1) (s + 1), ∀ z, a (dilate t z) ≠ 0 → z ∈ K' := by
    intro t ht z hz
    exact ⟨(t, dilate t z), ⟨ht, subset_tsupport _ hz⟩, dilate_neg_left t z⟩
  have hs : s ∈ Set.Icc (s - 1) (s + 1) := ⟨by linarith, by linarith⟩
  set B : ℝ := (2 * Real.exp ((|s| + 1) / 2) * C) ^ 2
  have hexp : ∀ t ∈ Set.Icc (s - 1) (s + 1), Real.exp (-t / 2) ≤ Real.exp ((|s| + 1) / 2) := by
    intro t ht
    apply Real.exp_le_exp.2
    have := neg_abs_le s
    linarith [ht.1, ht.2]
  have hfin : ∫⁻ z, K'.indicator (fun _ => ENNReal.ofReal B) z ≠ ⊤ := by
    rw [lintegral_indicator_const hK'.measurableSet]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hK'.measure_lt_top.ne
  have h0 : (0 : ℝ≥0∞) = ∫⁻ z : ℍ, (0 : ℝ≥0∞) := by simp
  rw [h0]
  refine tendsto_lintegral_filter_of_dominated_convergence (fun z => K'.indicator (fun _ => ENNReal.ofReal B) z)
    ?_ ?_ hfin ?_
  · refine Eventually.of_forall fun t => ?_
    have h1 : Continuous fun z => transportS t a z := by
      unfold transportS
      exact continuous_const.mul (hc.comp (continuous_dilate_joint.comp (continuous_const.prodMk continuous_id)))
    have h2 : Continuous fun z => transportS s a z := by
      unfold transportS
      exact continuous_const.mul (hc.comp (continuous_dilate_joint.comp (continuous_const.prodMk continuous_id)))
    exact ((h1.sub h2).enorm.measurable.pow_const _)
  · filter_upwards [Icc_mem_nhds (show s - 1 < s by linarith) (show s < s + 1 by linarith)] with t ht
    refine Eventually.of_forall fun z => ?_
    by_cases hz : z ∈ K'
    · rw [Set.indicator_of_mem hz, ← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hb : ∀ r ∈ Set.Icc (s - 1) (s + 1), ‖transportS r a z‖ ≤ Real.exp ((|s| + 1) / 2) * C := by
        intro r hr
        unfold transportS
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact mul_le_mul (hexp r hr) (hC _) (norm_nonneg _) (Real.exp_pos _).le
      have h2 : ‖transportS t a z - transportS s a z‖ ≤ 2 * Real.exp ((|s| + 1) / 2) * C := by
        calc ‖transportS t a z - transportS s a z‖ ≤ ‖transportS t a z‖ + ‖transportS s a z‖ :=
              norm_sub_le _ _
          _ ≤ 2 * Real.exp ((|s| + 1) / 2) * C := by linarith [hb t ht, hb s hs]
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      exact pow_le_pow_left₀ (norm_nonneg _) h2 2
    · rw [Set.indicator_of_notMem hz]
      have ht0 : a (dilate t z) = 0 := by by_contra h; exact hz (hmem t ht z h)
      have hs0 : a (dilate s z) = 0 := by by_contra h; exact hz (hmem s hs z h)
      simp [transportS, ht0, hs0]
  · refine Eventually.of_forall fun z => ?_
    have h1 := (((continuous_transportS_apply hc z).sub
      (continuous_const (y := transportS s a z))).enorm.tendsto s)
    have h2 := (ENNReal.continuous_rpow_const (y := (2 : ℝ))).tendsto _ |>.comp h1
    simpa [Function.comp_def] using h2

/-- `S(t) f → S(s) f` in `L²` for `f` with a continuous compactly supported representative. -/
theorem tendsto_transportLp_of_cc (f : Lp ℂ 2 (volume : Measure ℍ)) {a : ℍ → ℂ} (hc : Continuous a)
    (hcs : HasCompactSupport a) (hfa : ⇑f =ᵐ[volume] a) (s : ℝ) :
    Tendsto (fun t => transportLp t f) (𝓝 s) (𝓝 (transportLp s f)) := by
  show Tendsto (fun t => (memLp_transportS t f).toLp (transportS t ⇑f)) (𝓝 s)
    (𝓝 ((memLp_transportS s f).toLp (transportS s ⇑f)))
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'']
  have e : ∀ t, eLpNorm (transportS t ⇑f - transportS s ⇑f) 2 volume
      = (∫⁻ z, ‖transportS t a z - transportS s a z‖ₑ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
    intro t
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top
      ((memLp_transportS t f).sub (memLp_transportS s f)).aestronglyMeasurable, ENNReal.toReal_ofNat]
    congr 1
    refine lintegral_congr_ae ?_
    filter_upwards [transportS_ae_congr t hfa, transportS_ae_congr s hfa] with z h1 h2
    simp only [Pi.sub_apply, h1, h2]
  simp_rw [e]
  have h := (ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ))).tendsto 0 |>.comp
    (tendsto_lintegral_transportS hc hcs s)
  rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h
  exact h

/-- **Strong continuity of `S(t)`** on `L²(ℍ)`. -/
theorem continuous_transportLp_apply (f : Lp ℂ 2 (volume : Measure ℍ)) :
    Continuous fun t => transportLp t f := by
  rw [Metric.continuous_iff]
  intro s ε hε
  obtain ⟨F, hF⟩ := (Metric.denseRange_iff.1 denseRange_toL2) f (ε / 3) (by linarith)
  have hg := tendsto_transportLp_of_cc (toL2 F) (F.2.smooth.continuous.comp UpperHalfPlane.continuous_coe)
    (hasCompactSupport_comp_coe F.2)
    (memLp_comp_coe F.2).coeFn_toLp s
  obtain ⟨δ, hδ, hδ'⟩ := Metric.tendsto_nhds_nhds.1 hg (ε / 3) (by linarith)
  refine ⟨δ, hδ, fun t ht => ?_⟩
  have h1 := hδ' ht
  calc dist (transportLp t f) (transportLp s f)
      ≤ dist (transportLp t f) (transportLp t (toL2 F)) + dist (transportLp t (toL2 F)) (transportLp s (toL2 F))
        + dist (transportLp s (toL2 F)) (transportLp s f) := dist_triangle4 _ _ _ _
    _ = dist f (toL2 F) + dist (transportLp t (toL2 F)) (transportLp s (toL2 F)) + dist (toL2 F) f := by
        rw [LinearIsometry.dist_map, LinearIsometry.dist_map]
    _ < ε / 3 + ε / 3 + ε / 3 := by
        rw [dist_comm (toL2 F) f]
        gcongr
    _ = ε := by ring

/-- Joint continuity of `(t, f) ↦ S(t) f` along a filter. -/
lemma tendsto_transportLp_apply {α : Type*} {l : Filter α} {t₀ : ℝ} {x₀ : Lp ℂ 2 (volume : Measure ℍ)}
    {φ : α → ℝ} {q : α → Lp ℂ 2 (volume : Measure ℍ)} (hφ : Tendsto φ l (𝓝 t₀)) (hq : Tendsto q l (𝓝 x₀)) :
    Tendsto (fun a => transportLp (φ a) (q a)) l (𝓝 (transportLp t₀ x₀)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero] at hq ⊢
  have h2 : Tendsto (fun a => ‖transportLp (φ a) x₀ - transportLp t₀ x₀‖) l (𝓝 0) := by
    have := ((continuous_transportLp_apply x₀).tendsto t₀).comp hφ
    rw [tendsto_iff_norm_sub_tendsto_zero] at this
    exact this
  refine squeeze_zero (fun a => norm_nonneg _) (fun a => ?_) (by simpa using hq.add h2)
  calc ‖transportLp (φ a) (q a) - transportLp t₀ x₀‖
      = ‖transportLp (φ a) (q a - x₀) + (transportLp (φ a) x₀ - transportLp t₀ x₀)‖ := by
        rw [map_sub]; congr 1; abel
    _ ≤ ‖transportLp (φ a) (q a - x₀)‖ + ‖transportLp (φ a) x₀ - transportLp t₀ x₀‖ := norm_add_le _ _
    _ = ‖q a - x₀‖ + ‖transportLp (φ a) x₀ - transportLp t₀ x₀‖ := by rw [LinearIsometry.norm_map]

end Qschubert
