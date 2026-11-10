import Qschubert.KLAssembly

/-!
# The reverse Kontorovich–Lebedev Parseval identity

For `h` smooth with compact support in `(0, ∞)` and `ψ(z) = ∫ h(ν) w(ν) K_{iν}(z) dν`:
`∫_0^∞ |ψ(z)|² dz/z = ∫_0^∞ |h(ν)|² w(ν) dν`.

Part 1: `Â(t) = ∫ a(ν) e^{iνt} dν` for `a = w h` is a rescaled Schwartz Fourier transform
(`hatA_eq`), `Â` and `t Â(t)` are integrable, `∫ Â = 2π a(0) = 0` (`integral_hatA`), and
`ψ(z) = ½ ∫ e^{-z cosh t} Â(t) dt` (`klInv_eq`).
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set FourierTransform
open scoped ContDiff

lemma IsKTest.mul_smooth {φ k : ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ) (hk : IsKTest k) :
    IsKTest fun x => φ x * k x :=
  ⟨hφ.mul hk.smooth, hk.compact.mul_left, (tsupport_mul_subset_right (f := φ)).trans hk.pos⟩

/-- The Schwartz function of a KL test function. -/
noncomputable def IsKTest.toS {k : ℝ → ℂ} (hk : IsKTest k) : SchwartzMap ℝ ℂ :=
  hk.compact.toSchwartzMap hk.smooth

lemma IsKTest.toS_apply {k : ℝ → ℂ} (hk : IsKTest k) (x : ℝ) : hk.toS x = k x := rfl

/-- `Â(t) = ∫ a(ν) e^{iνt} dν`. -/
noncomputable def hatA (a : ℝ → ℂ) (t : ℝ) : ℂ := ∫ ν : ℝ, Complex.exp ((ν : ℂ) * t * I) * a ν

lemma hatA_eq (a : ℝ → ℂ) (t : ℝ) : hatA a t = 𝓕 a ((-(2 * Real.pi)⁻¹) * t) := by
  rw [hatA, show (-(2 * Real.pi)⁻¹) * t = -t / (2 * Real.pi) by ring, ← integral_exp_mul_eq_fourier]
  refine integral_congr_ae (Eventually.of_forall fun ν => ?_)
  simp only; ring_nf

variable {a : ℝ → ℂ}

lemma integrable_hatA (ha : IsKTest a) : Integrable (hatA a) := by
  have h := (SchwartzMap.integrable (μ := volume) (𝓕 ha.toS)).comp_mul_left' (R := -(2 * Real.pi)⁻¹)
    (neg_ne_zero.2 (inv_ne_zero (by positivity)))
  refine h.congr (Eventually.of_forall fun t => ?_)
  simp only
  rw [hatA_eq, SchwartzMap.fourier_coe]; rfl

lemma integrable_mul_hatA (ha : IsKTest a) : Integrable fun t => |t| * ‖hatA a t‖ := by
  have hc : (-(2 * Real.pi)⁻¹ : ℝ) ≠ 0 := neg_ne_zero.2 (inv_ne_zero (by positivity))
  have h := ((SchwartzMap.integrable_pow_mul volume (𝓕 ha.toS) 1).comp_mul_left' hc).const_mul
    |(-(2 * Real.pi)⁻¹ : ℝ)|⁻¹
  refine h.congr (Eventually.of_forall fun t => ?_)
  simp only [pow_one, Real.norm_eq_abs]
  rw [hatA_eq, SchwartzMap.fourier_coe, abs_mul, show (ha.toS : ℝ → ℂ) = a from rfl]
  have : |(-(2 * Real.pi)⁻¹ : ℝ)| ≠ 0 := abs_ne_zero.2 hc
  field_simp

/-- `∫ Â = 2π a(0) = 0`. -/
theorem integral_hatA (ha : IsKTest a) : ∫ t, hatA a t = 0 := by
  set c : ℝ := -(2 * Real.pi)⁻¹
  have hinv := (ha.toS).continuous.fourierInv_fourier_eq (ha.toS).integrable
    (by rw [← SchwartzMap.fourier_coe]; exact (𝓕 ha.toS).integrable)
  have h0 : ∫ ξ, 𝓕 (ha.toS : ℝ → ℂ) ξ = a 0 := by
    have := congrFun hinv 0
    rw [Real.fourierInv_eq'] at this
    simp only [inner_zero_right, mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_smul] at this
    rw [this]; rfl
  have e : (fun t => hatA a t) = fun t => 𝓕 (ha.toS : ℝ → ℂ) (c * t) := by
    funext t; rw [hatA_eq]; rfl
  rw [e, Measure.integral_comp_mul_left, h0, ha.eq_zero_of_nonpos le_rfl, smul_zero]

/-- `ψ(z) = ∫ a(ν) K_{iν}(z) dν`. -/
noncomputable def klInvA (a : ℝ → ℂ) (z : ℝ) : ℂ := ∫ ν, a ν * (besselKi ν z : ℂ)

/-- **`ψ(z) = ½ ∫ e^{-z cosh t} Â(t) dt`** for `z > 0`. -/
theorem klInvA_eq (ha : IsKTest a) {z : ℝ} (hz : 0 < z) :
    klInvA a z = (1 / 2 : ℂ) * ∫ t, ((Real.exp (-(z * Real.cosh t)) : ℝ) : ℂ) * hatA a t := by
  set H : ℝ × ℝ → ℂ := fun p => a p.1 * kInt (p.1 * I) z p.2
  have hH : Integrable H ((volume : Measure ℝ).prod volume) := by
    have hmaj := ha.integrable.norm.mul_prod (integrable_kInt 0 hz).norm
    refine hmaj.mono' ?_ (Eventually.of_forall fun p => ?_)
    · exact (ha.continuous.comp continuous_fst |>.mul (by unfold kInt; fun_prop)).aestronglyMeasurable
    · simp only [H, norm_mul, norm_kInt_I, norm_kInt_zero]; rfl
  have e1 : klInvA a z = (1 / 2 : ℂ) * ∫ ν, ∫ t, H (ν, t) := by
    rw [klInvA, ← MeasureTheory.integral_const_mul]
    congr 1; funext ν
    simp only [H]
    rw [← besselK_mul_I hz, besselK, MeasureTheory.integral_const_mul]; ring
  rw [e1, integral_integral_swap (f := fun ν t => H (ν, t)) hH]
  refine congrArg _ (integral_congr_ae (Eventually.of_forall fun t => ?_))
  simp only
  rw [hatA, ← MeasureTheory.integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun ν => ?_)
  simp only [H, kInt]
  rw [show Complex.exp (↑t * (↑ν * I)) = Complex.exp (↑ν * ↑t * I) by ring_nf]; ring

/-! ### Part 2: the `z^{s-1}`-regularized square -/

/-- `C(t, u) = cosh t + cosh u`. -/
noncomputable def coshSum (p : ℝ × ℝ) : ℝ := Real.cosh p.1 + Real.cosh p.2

lemma two_le_coshSum (p : ℝ × ℝ) : 2 ≤ coshSum p := by
  have := Real.one_le_cosh p.1; have := Real.one_le_cosh p.2; unfold coshSum; linarith

lemma coshSum_pos (p : ℝ × ℝ) : 0 < coshSum p := by linarith [two_le_coshSum p]

/-- The integrand `z^{s-1} e^{-z C(t,u)} Â(t) conj Â(u)` on `(0, ∞) × ℝ²`. -/
noncomputable def revG (a : ℝ → ℂ) (s : ℝ) (q : ℝ × (ℝ × ℝ)) : ℂ :=
  ((q.1 ^ (s - 1) * Real.exp (-(q.1 * coshSum q.2)) : ℝ) : ℂ)
    * (hatA a q.2.1 * (starRingEnd ℂ) (hatA a q.2.2))

lemma norm_sq_klInvA (ha : IsKTest a) {z : ℝ} (hz : 0 < z) :
    ((‖klInvA a z‖ ^ 2 : ℝ) : ℂ) = (1 / 4 : ℂ) * ∫ p : ℝ × ℝ,
      ((Real.exp (-(z * coshSum p)) : ℝ) : ℂ) * (hatA a p.1 * (starRingEnd ℂ) (hatA a p.2)) := by
  rw [Complex.ofReal_pow, ← Complex.mul_conj', klInvA_eq ha hz, map_mul, ← integral_conj]
  have hpm := integral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (fun t => ((Real.exp (-(z * Real.cosh t)) : ℝ) : ℂ) * hatA a t)
    (fun u => (starRingEnd ℂ) (((Real.exp (-(z * Real.cosh u)) : ℝ) : ℂ) * hatA a u))
  have e : ∀ p : ℝ × ℝ, ((Real.exp (-(z * Real.cosh p.1)) : ℝ) : ℂ) * hatA a p.1
      * (starRingEnd ℂ) (((Real.exp (-(z * Real.cosh p.2)) : ℝ) : ℂ) * hatA a p.2)
      = ((Real.exp (-(z * coshSum p)) : ℝ) : ℂ) * (hatA a p.1 * (starRingEnd ℂ) (hatA a p.2)) := by
    intro p
    rw [map_mul, Complex.conj_ofReal, coshSum, mul_add, neg_add, Real.exp_add]
    push_cast; ring
  simp_rw [e] at hpm
  rw [show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl, hpm]
  simp only [map_one, map_div₀, map_ofNat]
  ring

lemma norm_revG (s : ℝ) {z : ℝ} (hz : 0 < z) (p : ℝ × ℝ) :
    ‖revG a s (z, p)‖ = z ^ (s - 1) * Real.exp (-(coshSum p * z)) * (‖hatA a p.1‖ * ‖hatA a p.2‖) := by
  rw [revG, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    Complex.norm_conj, mul_comm z]

lemma integral_norm_revG {s : ℝ} (hs : 0 < s) (p : ℝ × ℝ) :
    ∫ z in Ioi 0, ‖revG a s (z, p)‖
      = Real.Gamma s * coshSum p ^ (-s) * (‖hatA a p.1‖ * ‖hatA a p.2‖) := by
  rw [setIntegral_congr_fun measurableSet_Ioi (fun z hz => norm_revG s hz p), integral_mul_const,
    Real.integral_rpow_mul_exp_neg_mul_Ioi hs (coshSum_pos p), one_div,
    Real.inv_rpow (coshSum_pos p).le, ← Real.rpow_neg (coshSum_pos p).le]
  ring

lemma continuous_hatA (ha : IsKTest a) : Continuous (hatA a) := by
  have hc : Continuous (𝓕 a) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ ha.integrable
  have e : hatA a = fun t => 𝓕 a ((-(2 * Real.pi)⁻¹) * t) := funext (hatA_eq a)
  rw [e]; exact hc.comp (continuous_const.mul continuous_id)

lemma measurable_revG (ha : IsKTest a) (s : ℝ) : Measurable (revG a s) := by
  have hcA := continuous_hatA ha
  have hC : Continuous fun q : ℝ × (ℝ × ℝ) => coshSum q.2 := by unfold coshSum; fun_prop
  refine (Complex.measurable_ofReal.comp ((measurable_fst.pow_const _).mul
    (Real.continuous_exp.measurable.comp ((measurable_fst.mul hC.measurable).neg)))).mul ?_
  exact ((hcA.comp (continuous_fst.comp continuous_snd)).mul
    (Complex.continuous_conj.comp (hcA.comp (continuous_snd.comp continuous_snd)))).measurable

lemma integrable_revG (ha : IsKTest a) {s : ℝ} (hs : 0 < s) :
    Integrable (revG a s) ((volume.restrict (Ioi 0)).prod volume) := by
  rw [integrable_prod_iff' (measurable_revG ha s).aestronglyMeasurable]
  refine ⟨Eventually.of_forall fun p => ?_, ?_⟩
  · have hI := (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := s - 1) (b := coshSum p)
      (by linarith) one_pos (coshSum_pos p)).mul_const (‖hatA a p.1‖ * ‖hatA a p.2‖)
    refine hI.mono' ((measurable_revG ha s).comp measurable_prodMk_right).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    rw [norm_revG s hz p, Real.rpow_one, neg_mul]
  · simp_rw [integral_norm_revG hs]
    have hA := integrable_hatA ha
    refine ((hA.norm.mul_prod hA.norm).const_mul (Real.Gamma s)).mono' ?_ (Eventually.of_forall fun p => ?_)
    · have hcA := continuous_hatA ha
      exact (((by unfold coshSum; fun_prop : Continuous coshSum).rpow_const
        (fun p => Or.inl (coshSum_pos p).ne')).const_smul (Real.Gamma s) |>.mul
        ((hcA.comp continuous_fst).norm.mul (hcA.comp continuous_snd).norm)).aestronglyMeasurable
    · have hG := Real.Gamma_pos_of_pos hs
      have hle : coshSum p ^ (-s) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by linarith [two_le_coshSum p]) (by linarith)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg hG.le (Real.rpow_nonneg (coshSum_pos p).le _))
        (by positivity))]
      calc Real.Gamma s * coshSum p ^ (-s) * (‖hatA a p.1‖ * ‖hatA a p.2‖)
          ≤ Real.Gamma s * 1 * (‖hatA a p.1‖ * ‖hatA a p.2‖) := by gcongr
        _ = _ := by ring

/-- **`∫_0^∞ |ψ|² z^{s-1} dz = ¼ Γ(s) ∬ Â(t) conj Â(u) (cosh t + cosh u)^{-s} dt du`** for `s > 0`. -/
theorem integral_revG_eq (ha : IsKTest a) {s : ℝ} (hs : 0 < s) :
    ((∫ z in Ioi 0, ‖klInvA a z‖ ^ 2 * z ^ (s - 1) : ℝ) : ℂ)
      = (1 / 4 : ℂ) * (Real.Gamma s : ℂ) * ∫ p : ℝ × ℝ,
          ((coshSum p ^ (-s) : ℝ) : ℂ) * (hatA a p.1 * (starRingEnd ℂ) (hatA a p.2)) := by
  rw [← integral_complex_ofReal]
  have e1 : ∀ z ∈ Ioi (0 : ℝ), ((‖klInvA a z‖ ^ 2 * z ^ (s - 1) : ℝ) : ℂ)
      = (1 / 4 : ℂ) * ∫ p : ℝ × ℝ, revG a s (z, p) := by
    intro z hz
    rw [Complex.ofReal_mul, norm_sq_klInvA ha hz, mul_comm, mul_left_comm, ← MeasureTheory.integral_const_mul]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    simp only [revG]; push_cast; ring
  have key : ∀ p : ℝ × ℝ, ∫ z in Ioi (0 : ℝ), revG a s (z, p)
      = (Real.Gamma s : ℂ) * (((coshSum p ^ (-s) : ℝ) : ℂ) * (hatA a p.1 * (starRingEnd ℂ) (hatA a p.2))) := by
    intro p
    simp only [revG]
    rw [integral_mul_const, integral_complex_ofReal]
    have h := Real.integral_rpow_mul_exp_neg_mul_Ioi hs (coshSum_pos p)
    have h' : ∫ z in Ioi (0 : ℝ), z ^ (s - 1) * Real.exp (-(z * coshSum p))
        = Real.Gamma s * coshSum p ^ (-s) := by
      have e : ∫ z in Ioi (0 : ℝ), z ^ (s - 1) * Real.exp (-(z * coshSum p))
          = ∫ t in Ioi (0 : ℝ), t ^ (s - 1) * Real.exp (-(coshSum p * t)) :=
        setIntegral_congr_fun measurableSet_Ioi (fun z _ => by rw [mul_comm z])
      rw [e, h, one_div, Real.inv_rpow (coshSum_pos p).le, ← Real.rpow_neg (coshSum_pos p).le]; ring
    rw [h']; push_cast; ring
  rw [setIntegral_congr_fun measurableSet_Ioi e1, MeasureTheory.integral_const_mul,
    integral_integral_swap (f := fun z p => revG a s (z, p)) (integrable_revG ha hs),
    integral_congr_ae (Eventually.of_forall key), MeasureTheory.integral_const_mul]
  ring

end Qschubert
