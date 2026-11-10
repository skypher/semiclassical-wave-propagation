import Qschubert.KLLogCosh

/-!
# The reverse KL Parseval identity

`rev_parseval`: for `h` smooth with compact support in `(0, ∞)` and `ψ = ∫ h(ν) w(ν) K_{iν} dν`,
`∫_0^∞ |ψ(z)|² dz/z = ∫_0^∞ |h(ν)|² w(ν) dν`.

Part 1: scalar facts for the limit `s → 0⁺`: `Γ(1 + s) ≤ 1` on `[0, 1]` (log-convexity),
`|Γ(s)(C^{-s} - 1)| ≤ log C` for `C ≥ 1`, `s ∈ (0, 1]`, and `Γ(s)(C^{-s} - 1) → -log C`.
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set
open scoped ContDiff

lemma Gamma_one_add_le_one {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : Real.Gamma (1 + s) ≤ 1 := by
  have h := Real.convexOn_log_Gamma.2 (show (1 : ℝ) ∈ Ioi 0 by norm_num) (show (2 : ℝ) ∈ Ioi 0 by norm_num)
    (show (0 : ℝ) ≤ 1 - s by linarith) hs0 (by ring)
  simp only [Function.comp_apply, smul_eq_mul, Real.Gamma_one, Real.Gamma_two, Real.log_one, mul_zero,
    add_zero] at h
  have hpos : 0 < Real.Gamma (1 + s) := Real.Gamma_pos_of_pos (by linarith)
  rw [show (1 - s) * 1 + s * 2 = 1 + s by ring] at h
  exact (Real.log_nonpos_iff hpos.le).1 h

lemma abs_Gamma_mul_rpow_sub_le {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) {C : ℝ} (hC : 1 ≤ C) :
    |Real.Gamma s * (C ^ (-s) - 1)| ≤ Real.log C := by
  have hC0 : 0 < C := by linarith
  have hlog : 0 ≤ Real.log C := Real.log_nonneg hC
  have hG : 0 < Real.Gamma s := Real.Gamma_pos_of_pos hs
  have hGs : Real.Gamma s * s ≤ 1 := by
    have := Gamma_one_add_le_one hs.le hs1
    rw [add_comm, Real.Gamma_add_one hs.ne'] at this; linarith
  have e : C ^ (-s) = Real.exp (-(s * Real.log C)) := by
    rw [Real.rpow_def_of_pos hC0]; ring_nf
  have h1 : C ^ (-s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hC (by linarith)
  have h2 : 1 - s * Real.log C ≤ C ^ (-s) := by
    rw [e]; have := Real.add_one_le_exp (-(s * Real.log C)); linarith
  rw [abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hG.le (by linarith))]
  have : Real.Gamma s * (1 - C ^ (-s)) ≤ Real.Gamma s * (s * Real.log C) :=
    mul_le_mul_of_nonneg_left (by linarith) hG.le
  nlinarith

lemma tendsto_Gamma_mul_rpow_sub {C : ℝ} (hC : 0 < C) :
    Tendsto (fun s : ℝ => Real.Gamma s * (C ^ (-s) - 1)) (𝓝[>] 0) (𝓝 (-Real.log C)) := by
  -- `g(s) = C^{-s}` has derivative `-log C` at `0`
  have hg : HasDerivAt (fun s : ℝ => Real.exp (-(s * Real.log C))) (-Real.log C) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).mul_const (Real.log C)).neg.exp
    simpa using this
  have hslope := hasDerivAt_iff_tendsto_slope_zero.1 hg
  have hslope' : Tendsto (fun t : ℝ => t⁻¹ * (C ^ (-t) - 1)) (𝓝[>] 0) (𝓝 (-Real.log C)) := by
    refine (hslope.mono_left (nhdsWithin_mono _ fun t ht => ne_of_gt ht)).congr' ?_
    filter_upwards with t
    simp only [zero_add, zero_mul, neg_zero, Real.exp_zero, smul_eq_mul]
    rw [Real.rpow_def_of_pos hC]; ring_nf
  have hG1 : Tendsto (fun s : ℝ => Real.Gamma (s + 1)) (𝓝[>] 0) (𝓝 1) := by
    have hc : ContinuousAt Real.Gamma 1 :=
      (Real.differentiableAt_Gamma (fun m h => by have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith)).continuousAt
    have := (hc.tendsto.comp ((continuous_id.add (continuous_const (y := (1 : ℝ)))).tendsto' 0 1 (by simp)))
    rw [Real.Gamma_one] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hmul := hG1.mul hslope'
  rw [one_mul] at hmul
  refine hmul.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : (s : ℝ) ≠ 0 := ne_of_gt hs
  rw [Real.Gamma_add_one hs']
  field_simp

/-! ### Part 2: the limit of the right side -/

lemma log_coshSum_le (p : ℝ × ℝ) : Real.log (coshSum p) ≤ 1 + |p.1| + |p.2| := by
  have hc1 := Real.one_le_cosh p.1
  have hc2 := Real.one_le_cosh p.2
  have hle : coshSum p ≤ 2 * Real.cosh p.1 * Real.cosh p.2 := by unfold coshSum; nlinarith
  have hpos := coshSum_pos p
  calc Real.log (coshSum p) ≤ Real.log (2 * Real.cosh p.1 * Real.cosh p.2) := Real.log_le_log hpos hle
    _ = Real.log 2 + Real.log (Real.cosh p.1) + Real.log (Real.cosh p.2) := by
        rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity)]
    _ ≤ 1 + |p.1| + |p.2| := by
        have := log_cosh_le_abs p.1; have := log_cosh_le_abs p.2
        have : Real.log 2 ≤ 1 := by
          rw [Real.log_le_iff_le_exp (by norm_num)]
          have := Real.add_one_le_exp (1 : ℝ); linarith
        linarith

section limit

variable {a : ℝ → ℂ} (ha : IsKTest a)
include ha

lemma integral_Phi_eq_zero :
    ∫ p : ℝ × ℝ, hatA a p.1 * (starRingEnd ℂ) (hatA a p.2) = 0 := by
  have h := integral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (hatA a) (fun u => (starRingEnd ℂ) (hatA a u))
  rw [show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl, h, integral_hatA ha, zero_mul]

lemma integrable_Phi_weight :
    Integrable (fun p : ℝ × ℝ => (1 + |p.1| + |p.2|) * ‖hatA a p.1 * (starRingEnd ℂ) (hatA a p.2)‖)
      ((volume : Measure ℝ).prod volume) := by
  have hA := integrable_hatA ha
  have h0 := hA.norm.mul_prod hA.norm
  have h1 := (integrable_mul_hatA ha).mul_prod hA.norm
  have h2 := hA.norm.mul_prod (integrable_mul_hatA ha)
  refine ((h0.add h1).add h2).congr (Eventually.of_forall fun p => ?_)
  simp only [Pi.add_apply, norm_mul, Complex.norm_conj]; ring

/-- **The right side converges**: `¼ Γ(s) ∬ C^{-s} Φ → -¼ ∬ log C · Φ` as `s → 0⁺`. -/
theorem tendsto_rhs :
    Tendsto (fun s : ℝ => (1 / 4 : ℂ) * (Real.Gamma s : ℂ) * ∫ p : ℝ × ℝ,
        ((coshSum p ^ (-s) : ℝ) : ℂ) * (hatA a p.1 * (starRingEnd ℂ) (hatA a p.2)))
      (𝓝[>] 0) (𝓝 (-(1 / 4 : ℂ) * ∫ p : ℝ × ℝ,
        ((Real.log (coshSum p) : ℝ) : ℂ) * (hatA a p.1 * (starRingEnd ℂ) (hatA a p.2)))) := by
  set Φ : ℝ × ℝ → ℂ := fun p => hatA a p.1 * (starRingEnd ℂ) (hatA a p.2)
  have hcA := continuous_hatA ha
  have hcΦ : Continuous Φ := (hcA.comp continuous_fst).mul (Complex.continuous_conj.comp (hcA.comp continuous_snd))
  have hcC : Continuous coshSum := by unfold coshSum; fun_prop
  have hΦ : Integrable Φ ((volume : Measure ℝ).prod volume) :=
    (integrable_Phi_weight ha).mono' hcΦ.aestronglyMeasurable (Eventually.of_forall fun p => by
      show ‖Φ p‖ ≤ (1 + |p.1| + |p.2|) * ‖Φ p‖
      have := norm_nonneg (Φ p)
      nlinarith [abs_nonneg p.1, abs_nonneg p.2])
  have hiC : ∀ s : ℝ, 0 ≤ s → Integrable (fun p : ℝ × ℝ => ((coshSum p ^ (-s) : ℝ) : ℂ) * Φ p)
      ((volume : Measure ℝ).prod volume) := by
    intro s hs
    refine hΦ.norm.mono' ((Complex.continuous_ofReal.comp (hcC.rpow_const fun p => Or.inl (coshSum_pos p).ne')).mul
      hcΦ).aestronglyMeasurable (Eventually.of_forall fun p => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (coshSum_pos p).le _)]
    exact mul_le_of_le_one_left (norm_nonneg _)
      (Real.rpow_le_one_of_one_le_of_nonpos (by linarith [two_le_coshSum p]) (by linarith))
  have hre : ∀ s : ℝ, 0 ≤ s → (1 / 4 : ℂ) * (Real.Gamma s : ℂ) * ∫ p : ℝ × ℝ, ((coshSum p ^ (-s) : ℝ) : ℂ) * Φ p
      = (1 / 4 : ℂ) * ∫ p : ℝ × ℝ, ((Real.Gamma s * (coshSum p ^ (-s) - 1) : ℝ) : ℂ) * Φ p := by
    intro s hs
    have e : (fun p : ℝ × ℝ => ((Real.Gamma s * (coshSum p ^ (-s) - 1) : ℝ) : ℂ) * Φ p)
        = fun p => (Real.Gamma s : ℂ) * (((coshSum p ^ (-s) : ℝ) : ℂ) * Φ p - Φ p) := by
      funext p; push_cast; ring
    have h0 : ∫ p : ℝ × ℝ, Φ p ∂((volume : Measure ℝ).prod volume) = 0 := integral_Phi_eq_zero ha
    rw [e, show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl,
      MeasureTheory.integral_const_mul, integral_sub (hiC s hs) hΦ, h0, sub_zero]; ring
  set F : ℝ → ℝ × ℝ → ℂ := fun s p => ((Real.Gamma s * (coshSum p ^ (-s) - 1) : ℝ) : ℂ) * Φ p
  have hlim : Tendsto (fun s => ∫ p : ℝ × ℝ, F s p ∂((volume : Measure ℝ).prod volume)) (𝓝[>] 0)
      (𝓝 (∫ p : ℝ × ℝ, ((-Real.log (coshSum p) : ℝ) : ℂ) * Φ p ∂((volume : Measure ℝ).prod volume))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun p : ℝ × ℝ => (1 + |p.1| + |p.2|) * ‖Φ p‖) ?_ ?_ (integrable_Phi_weight ha) ?_
    · exact Eventually.of_forall fun s => ((Complex.continuous_ofReal.comp (continuous_const.mul
        ((hcC.rpow_const fun p => Or.inl (coshSum_pos p).ne').sub continuous_const))).mul hcΦ).aestronglyMeasurable
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with s hs
      refine Eventually.of_forall fun p => ?_
      simp only [F, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have h1 := abs_Gamma_mul_rpow_sub_le hs.1 hs.2.le (by linarith [two_le_coshSum p] : (1 : ℝ) ≤ coshSum p)
      have h2 := log_coshSum_le p
      rw [← abs_mul]
      exact mul_le_mul_of_nonneg_right (h1.trans h2) (norm_nonneg _)
    · refine Eventually.of_forall fun p => ?_
      have h := tendsto_Gamma_mul_rpow_sub (coshSum_pos p)
      exact ((Complex.continuous_ofReal.tendsto _).comp h).mul_const (Φ p)
  have hev : (fun s : ℝ => (1 / 4 : ℂ) * ∫ p : ℝ × ℝ, F s p ∂((volume : Measure ℝ).prod volume))
      =ᶠ[𝓝[>] 0] fun s : ℝ => (1 / 4 : ℂ) * (Real.Gamma s : ℂ) * ∫ p : ℝ × ℝ,
        ((coshSum p ^ (-s) : ℝ) : ℂ) * (hatA a p.1 * (starRingEnd ℂ) (hatA a p.2)) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [hre s (le_of_lt hs)]; rfl
  have hfin : (1 / 4 : ℂ) * ∫ p : ℝ × ℝ, ((-Real.log (coshSum p) : ℝ) : ℂ) * Φ p ∂((volume : Measure ℝ).prod volume)
      = -(1 / 4 : ℂ) * ∫ p : ℝ × ℝ, ((Real.log (coshSum p) : ℝ) : ℂ) * (hatA a p.1 * (starRingEnd ℂ) (hatA a p.2)) := by
    rw [show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl]
    have : (fun p : ℝ × ℝ => ((-Real.log (coshSum p) : ℝ) : ℂ) * Φ p)
        = fun p => -(((Real.log (coshSum p) : ℝ) : ℂ) * Φ p) := by funext p; push_cast; ring
    rw [this, integral_neg]; ring
  rw [← hfin]
  exact (hlim.const_mul (1 / 4 : ℂ)).congr' hev

end limit

/-! ### Part 3: the left side and the reverse Parseval identity -/

section lhs

variable {a : ℝ → ℂ} (ha : IsKTest a)
include ha

lemma ofReal_sq_rpow_eq {s : ℝ} {z : ℝ} (hz : 0 < z) :
    ((‖klInvA a z‖ ^ 2 * z ^ (s - 1) : ℝ) : ℂ) = (1 / 4 : ℂ) * ∫ p : ℝ × ℝ, revG a s (z, p) := by
  rw [Complex.ofReal_mul, norm_sq_klInvA ha hz, mul_comm, mul_left_comm, ← MeasureTheory.integral_const_mul]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only [revG]; push_cast; ring

lemma integrableOn_sq_rpow {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun z => ‖klInvA a z‖ ^ 2 * z ^ (s - 1)) (Ioi 0) := by
  have h := ((integrable_revG ha hs).integral_prod_left).const_mul (1 / 4 : ℂ)
  refine h.norm.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
  rw [← ofReal_sq_rpow_eq ha hz, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_of_lt hz) _))]

/-- **The reverse KL Parseval identity, amplitude form**: `|ψ|²/z` is integrable and
`∫_0^∞ |ψ|² dz/z = (π²/2) ∫ |a(ν)|²/(ν sinh πν) dν`. -/
theorem rev_parseval_amp :
    IntegrableOn (fun z => ‖klInvA a z‖ ^ 2 / z) (Ioi 0) ∧
      ∫ z in Ioi 0, ‖klInvA a z‖ ^ 2 / z
        = Real.pi ^ 2 / 2 * ∫ ν, ‖a ν‖ ^ 2 * (ν * Real.sinh (Real.pi * ν))⁻¹ := by
  set L : ℝ := Real.pi ^ 2 / 2 * ∫ ν, ‖a ν‖ ^ 2 * (ν * Real.sinh (Real.pi * ν))⁻¹
  set I : ℝ → ℝ := fun s => ∫ z in Ioi 0, ‖klInvA a z‖ ^ 2 * z ^ (s - 1)
  -- the limit of `I`
  have hI : Tendsto I (𝓝[>] 0) (𝓝 L) := by
    have hC := tendsto_rhs ha
    rw [integral_log_coshSum ha] at hC
    have hL : -(1 / 4 : ℂ) * (-((2 * Real.pi ^ 2 : ℝ) : ℂ) * ∫ ν, ((‖a ν‖ ^ 2 : ℝ) : ℂ)
        * ((ν * Real.sinh (Real.pi * ν))⁻¹ : ℝ)) = (L : ℂ) := by
      simp only [L]
      rw [show (fun ν : ℝ => ((‖a ν‖ ^ 2 : ℝ) : ℂ) * ((ν * Real.sinh (Real.pi * ν))⁻¹ : ℝ))
          = fun ν => ((‖a ν‖ ^ 2 * (ν * Real.sinh (Real.pi * ν))⁻¹ : ℝ) : ℂ) by funext ν; push_cast; ring,
        integral_complex_ofReal]
      push_cast; ring
    rw [hL] at hC
    have hev : (fun s : ℝ => (1 / 4 : ℂ) * (Real.Gamma s : ℂ) * ∫ p : ℝ × ℝ,
        ((coshSum p ^ (-s) : ℝ) : ℂ) * (hatA a p.1 * (starRingEnd ℂ) (hatA a p.2)))
        =ᶠ[𝓝[>] 0] fun s => ((I s : ℝ) : ℂ) := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact (integral_revG_eq ha hs).symm
    have hc := (Complex.continuous_re.tendsto _).comp (hC.congr' hev)
    simpa [Function.comp_def] using hc
  -- Fatou along `s_n = 1/(n+2)`
  set sn : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 2)
  have hsn0 : ∀ n, 0 < sn n := fun n => by simp only [sn]; positivity
  have hsn1 : ∀ n, sn n < 1 := fun n => by
    simp only [sn]; rw [div_lt_one (by positivity)]; have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith
  have hsnT : Tendsto sn atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall hsn0⟩
    exact tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hpw : ∀ z : ℝ, 0 < z → Tendsto (fun s : ℝ => z ^ (s - 1)) (𝓝[>] 0) (𝓝 (z⁻¹)) := by
    intro z hz
    have hc : Continuous fun s : ℝ => Real.exp (Real.log z * (s - 1)) := by fun_prop
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simp only [zero_sub, mul_neg, mul_one, Real.exp_neg, Real.exp_log hz] at this
    refine this.congr' (Eventually.of_forall fun s => ?_)
    show _ = z ^ (s - 1)
    rw [Real.rpow_def_of_pos hz]
  have hmeasψ : Measurable fun z => ‖klInvA a z‖ := by
    have hm : StronglyMeasurable (Function.uncurry fun (z : ℝ) (ν : ℝ) => a ν * (besselKi ν z : ℂ)) := by
      have h1 : Measurable fun q : ℝ × ℝ => besselKi q.2 q.1 :=
        measurable_besselKi.comp (measurable_snd.prodMk measurable_fst)
      exact ((ha.continuous.measurable.comp measurable_snd).mul (Complex.measurable_ofReal.comp h1)).stronglyMeasurable
    exact (hm.integral_prod_right (ν := volume)).measurable.norm
  have hfin : ∫⁻ z in Ioi 0, ENNReal.ofReal (‖klInvA a z‖ ^ 2 / z) ≤ ENNReal.ofReal L := by
    have hfat := lintegral_liminf_le (μ := volume.restrict (Ioi 0)) (u := (atTop : Filter ℕ))
      (f := fun n z => ENNReal.ofReal (‖klInvA a z‖ ^ 2 * z ^ (sn n - 1)))
      (fun n => ENNReal.measurable_ofReal.comp (show Measurable fun z => ‖klInvA a z‖ ^ 2 * z ^ (sn n - 1) from
        (hmeasψ.pow_const 2).mul (measurable_id.pow_const _)))
    have hlim_pt : ∀ᵐ z ∂(volume.restrict (Ioi 0)),
        liminf (fun n => ENNReal.ofReal (‖klInvA a z‖ ^ 2 * z ^ (sn n - 1))) atTop
          = ENNReal.ofReal (‖klInvA a z‖ ^ 2 / z) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
      refine Tendsto.liminf_eq ?_
      refine (ENNReal.continuous_ofReal.tendsto _).comp ?_
      rw [div_eq_mul_inv]
      exact ((hpw z hz).comp hsnT).const_mul _
    have hint_n : ∀ n, ∫⁻ z in Ioi 0, ENNReal.ofReal (‖klInvA a z‖ ^ 2 * z ^ (sn n - 1)) = ENNReal.ofReal (I (sn n)) := by
      intro n
      rw [ofReal_integral_eq_lintegral_ofReal (integrableOn_sq_rpow ha (hsn0 n))]
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
      exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_of_lt hz) _)
    have hliminf : liminf (fun n => ∫⁻ z in Ioi 0, ENNReal.ofReal (‖klInvA a z‖ ^ 2 * z ^ (sn n - 1))) atTop
        = ENNReal.ofReal L := by
      simp_rw [hint_n]
      exact Tendsto.liminf_eq ((ENNReal.continuous_ofReal.tendsto _).comp (hI.comp hsnT))
    rw [← lintegral_congr_ae hlim_pt, ← hliminf]
    exact hfat
  have hint : IntegrableOn (fun z => ‖klInvA a z‖ ^ 2 / z) (Ioi 0) := by
    refine ⟨(((hmeasψ.pow_const 2).div measurable_id).aestronglyMeasurable), ?_⟩
    rw [hasFiniteIntegral_iff_ofReal]
    · exact hfin.trans_lt ENNReal.ofReal_lt_top
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
      exact div_nonneg (sq_nonneg _) (le_of_lt hz)
  -- dominated convergence for `I`
  have h1 := integrableOn_sq_rpow ha (s := 1) one_pos
  simp only [sub_self, Real.rpow_zero, mul_one] at h1
  have hdc : Tendsto I (𝓝[>] 0) (𝓝 (∫ z in Ioi 0, ‖klInvA a z‖ ^ 2 / z)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun z => ‖klInvA a z‖ ^ 2 / z + ‖klInvA a z‖ ^ 2) ?_ ?_
      (show Integrable (fun z => ‖klInvA a z‖ ^ 2 / z + ‖klInvA a z‖ ^ 2) (volume.restrict (Ioi 0)) from hint.add h1) ?_
    · exact Eventually.of_forall fun s =>
        ((hmeasψ.pow_const 2).mul (measurable_id.pow_const _)).aestronglyMeasurable
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with s hs
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
      have hz0 : 0 < z := hz
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hz0.le _))]
      have hb : z ^ (s - 1) ≤ z⁻¹ + 1 := by
        rcases le_total z 1 with hz1 | hz1
        · have := Real.rpow_le_rpow_of_exponent_ge hz0 hz1 (show (-1 : ℝ) ≤ s - 1 by linarith [hs.1])
          rw [Real.rpow_neg_one] at this; linarith
        · have := Real.rpow_le_rpow_of_exponent_le hz1 (show s - 1 ≤ 0 by linarith [hs.2])
          rw [Real.rpow_zero] at this; have := inv_nonneg.2 hz0.le; linarith
      calc ‖klInvA a z‖ ^ 2 * z ^ (s - 1) ≤ ‖klInvA a z‖ ^ 2 * (z⁻¹ + 1) :=
            mul_le_mul_of_nonneg_left hb (sq_nonneg _)
        _ = _ := by rw [div_eq_mul_inv]; ring
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
      rw [div_eq_mul_inv]
      exact (hpw z hz).const_mul _
  exact ⟨hint, tendsto_nhds_unique hdc hI⟩

end lhs

/-- **The reverse Kontorovich–Lebedev Parseval identity**: for `h` smooth with compact support in `(0, ∞)`
and `ψ(z) = ∫ h(ν) w(ν) K_{iν}(z) dν`, `∫_0^∞ |ψ(z)|² dz/z = ∫_0^∞ |h(ν)|² w(ν) dν`. -/
theorem rev_parseval {h : ℝ → ℂ} (hh : IsKTest h) :
    ∫ z in Ioi 0, ‖klInvA (fun ν => (klW ν : ℂ) * h ν) z‖ ^ 2 / z = ∫ ν in Ioi 0, klW ν * ‖h ν‖ ^ 2 := by
  have hw : ContDiff ℝ ∞ fun ν : ℝ => ((klW ν : ℝ) : ℂ) :=
    Complex.ofRealCLM.contDiff.comp
      (show ContDiff ℝ ∞ fun ν : ℝ => 2 / Real.pi ^ 2 * ν * Real.sinh (Real.pi * ν) by fun_prop)
  have ha : IsKTest fun ν => (klW ν : ℂ) * h ν := hh.mul_smooth hw
  rw [(rev_parseval_amp ha).2]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi (0 : ℝ)) (fun ν hν => by
    rw [hh.eq_zero_of_nonpos (not_lt.1 hν)]; simp), ← MeasureTheory.integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi (fun ν hν => ?_)
  have hν0 : (0 : ℝ) < ν := hν
  have hs : 0 < Real.sinh (Real.pi * ν) := Real.sinh_pos_iff.2 (by positivity)
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, klW]
  field_simp

end Qschubert
