import Qschubert.HypCutoff
import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous

/-!
# Mollification on `ℂ ≅ ℝ²`

`φ_n` (`mollR n`) is the normalized smooth bump of radius `1/(n+1)` at `0`: `φ_n ≥ 0`,
`∫ φ_n = 1`, `φ_n = 0` off `B(0, 1/(n+1))`. For `f : ℂ → ℂ`, `molF n f = f ⋆ φ_n`, i.e.
`molF n f x = ∫ φ_n(x - t) f(t) dt = ∫ φ_n(t) f(x - t) dt`.

* `enorm_integral_smul_sq_le` (Jensen for a probability density, via Hölder):
  `‖∫ φ h‖² ≤ ∫ φ ‖h‖²`.
* `tendsto_molF` (**the `L²` approximate identity**): for measurable `f ∈ L²(ℂ)`,
  `‖molF n f - f‖₂ → 0`. Proof: `molF n f x - f x = ∫ φ_n(t)(f(x - t) - f(x)) dt`, Jensen and Tonelli
  give `‖molF n f - f‖₂² ≤ ∫ φ_n(t) ‖f(· - t) - f‖₂² dt`, and translation is continuous on `L²`
  (Mathlib's `DomAddAct` action), so the right side is `≤ ε²` once `1/(n+1)` is below the
  continuity radius.
-/

namespace Qschubert

open MeasureTheory Filter Topology Metric Set
open scoped Convolution ENNReal ContDiff

local notation "L2C" => Lp ℂ 2 (volume : Measure ℂ)

/-! ### The mollifiers -/

/-- The smooth bump at `0` with radii `1/(2(n+1)) < 1/(n+1)`. -/
noncomputable def bumpN (n : ℕ) : ContDiffBump (0 : ℂ) where
  rIn := 1 / (2 * ((n : ℝ) + 1))
  rOut := 1 / ((n : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have h : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    exact one_div_lt_one_div_of_lt h (by linarith)

/-- The normalized mollifier `φ_n`. -/
noncomputable def mollR (n : ℕ) : ℂ → ℝ := (bumpN n).normed volume

lemma mollR_nonneg (n : ℕ) (z : ℂ) : 0 ≤ mollR n z := (bumpN n).nonneg_normed z

lemma integral_mollR (n : ℕ) : ∫ z, mollR n z = 1 := (bumpN n).integral_normed

lemma integrable_mollR (n : ℕ) : Integrable (mollR n) := (bumpN n).integrable_normed

lemma contDiff_mollR (n : ℕ) : ContDiff ℝ ∞ (mollR n) := (bumpN n).contDiff_normed

lemma continuous_mollR (n : ℕ) : Continuous (mollR n) := (contDiff_mollR n).continuous

lemma hasCompactSupport_mollR (n : ℕ) : HasCompactSupport (mollR n) :=
  (bumpN n).hasCompactSupport_normed

lemma mollR_eq_zero {n : ℕ} {z : ℂ} (hz : 1 / ((n : ℝ) + 1) ≤ ‖z‖) : mollR n z = 0 := by
  have h : z ∉ Function.support (mollR n) := by
    rw [mollR, (bumpN n).support_normed_eq, mem_ball, dist_zero_right]
    exact not_lt.2 hz
  simpa using h

lemma lintegral_mollR (n : ℕ) : ∫⁻ z, ENNReal.ofReal (mollR n z) = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_mollR n)
    (Eventually.of_forall (mollR_nonneg n)), integral_mollR, ENNReal.ofReal_one]

/-- `(a, r) ↦ r • a`. -/
noncomputable def smulL : ℂ →L[ℝ] ℝ →L[ℝ] ℂ := (ContinuousLinearMap.lsmul ℝ ℝ).flip

@[simp] lemma smulL_apply (a : ℂ) (r : ℝ) : smulL a r = r • a := by simp [smulL]

/-- `f ⋆ φ_n`. -/
noncomputable def molF (n : ℕ) (f : ℂ → ℂ) : ℂ → ℂ := f ⋆[smulL, volume] mollR n

lemma molF_apply (n : ℕ) (f : ℂ → ℂ) (x : ℂ) : molF n f x = ∫ t, mollR n (x - t) • f t := by
  rw [molF, convolution_def]; simp

lemma molF_apply_swap (n : ℕ) (f : ℂ → ℂ) (x : ℂ) : molF n f x = ∫ t, mollR n t • f (x - t) := by
  rw [molF, convolution_eq_swap]; simp

lemma contDiff_molF_aux (n : ℕ) {f : ℂ → ℂ} (hf : LocallyIntegrable f) : ContDiff ℝ ∞ (molF n f) :=
  (hasCompactSupport_mollR n).contDiff_convolution_right smulL hf (contDiff_mollR n)

lemma convolutionExists_molF (n : ℕ) {f : ℂ → ℂ} (hf : LocallyIntegrable f) :
    ConvolutionExists f (mollR n) smulL volume :=
  (hasCompactSupport_mollR n).convolutionExists_right smulL hf (continuous_mollR n)

lemma integrable_mollR_smul (n : ℕ) {f : ℂ → ℂ} (hf : LocallyIntegrable f) (x : ℂ) :
    Integrable fun t => mollR n t • f (x - t) := by
  have h := (convolutionExists_molF n hf x).integrable_swap
  simpa using h

/-! ### Jensen -/

/-- `‖∫ φ h‖² ≤ ∫ φ ‖h‖²` for a probability density `φ`. -/
lemma enorm_integral_smul_sq_le (φ : ℂ → ℝ) (hφ0 : ∀ t, 0 ≤ φ t) (hφm : Measurable φ)
    (hφ1 : ∫⁻ t, ENNReal.ofReal (φ t) = 1) (h : ℂ → ℂ) (hh : AEMeasurable h) :
    ‖∫ t, φ t • h t‖ₑ ^ (2 : ℝ) ≤ ∫⁻ t, ENNReal.ofReal (φ t) * ‖h t‖ₑ ^ (2 : ℝ) := by
  have h1 : ‖∫ t, φ t • h t‖ₑ ≤ ∫⁻ t, ENNReal.ofReal (φ t) * ‖h t‖ₑ := by
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    congr 1; funext t
    rw [enorm_smul, Real.enorm_eq_ofReal (hφ0 t)]
  set a : ℂ → ℝ≥0∞ := fun t => ENNReal.ofReal (Real.sqrt (φ t)) with ha_def
  have ham : AEMeasurable a :=
    (ENNReal.measurable_ofReal.comp (Real.continuous_sqrt.measurable.comp hφm)).aemeasurable
  have ha2 : ∀ t, a t ^ (2 : ℝ) = ENNReal.ofReal (φ t) := fun t => by
    simp only [ha_def]
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) (by norm_num)]
    congr 1
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, Real.sq_sqrt (hφ0 t)]
  have hab : ∀ t, a t * (a t * ‖h t‖ₑ) = ENNReal.ofReal (φ t) * ‖h t‖ₑ := fun t => by
    rw [← mul_assoc]; congr 1
    simp only [ha_def]
    rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _), Real.mul_self_sqrt (hφ0 t)]
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq volume Real.HolderConjugate.two_two
    (f := a) (g := fun t => a t * ‖h t‖ₑ) ham (ham.mul hh.enorm)
  simp only [Pi.mul_apply, hab] at hH
  have hA : ∫⁻ t, a t ^ (2 : ℝ) = 1 := by simp_rw [ha2]; exact hφ1
  have hB : ∫⁻ t, (a t * ‖h t‖ₑ) ^ (2 : ℝ) = ∫⁻ t, ENNReal.ofReal (φ t) * ‖h t‖ₑ ^ (2 : ℝ) := by
    congr 1; funext t; rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ha2]
  rw [hA, ENNReal.one_rpow, one_mul, hB] at hH
  calc ‖∫ t, φ t • h t‖ₑ ^ (2 : ℝ)
      ≤ ((∫⁻ t, ENNReal.ofReal (φ t) * ‖h t‖ₑ ^ (2 : ℝ)) ^ (1 / (2 : ℝ))) ^ (2 : ℝ) :=
        ENNReal.rpow_le_rpow (h1.trans hH) (by norm_num)
    _ = ∫⁻ t, ENNReal.ofReal (φ t) * ‖h t‖ₑ ^ (2 : ℝ) := by
        rw [← ENNReal.rpow_mul]; norm_num

/-! ### The `L²` approximate identity -/

lemma eLpNorm_two_eq {g : ℂ → ℂ} (hg : AEStronglyMeasurable g) :
    eLpNorm g 2 volume = (∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top hg,
    ENNReal.toReal_ofNat]

lemma lintegral_eq_eLpNorm_sq {g : ℂ → ℂ} (hg : AEStronglyMeasurable g) :
    ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) = eLpNorm g 2 volume ^ (2 : ℝ) := by
  rw [eLpNorm_two_eq hg, ← ENNReal.rpow_mul]; norm_num

/-- **`f ⋆ φ_n → f` in `L²(ℂ)`.** -/
theorem tendsto_molF (f : ℂ → ℂ) (hfm : Measurable f) (hf : MemLp f 2) :
    Tendsto (fun n => eLpNorm (fun x => molF n f x - f x) 2 volume) atTop (𝓝 0) := by
  haveI : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨ENNReal.ofNat_ne_top⟩
  set F : L2C := hf.toLp f
  set τ : ℂ → L2C := fun s => (DomAddAct.mk (-s)) +ᵥ F with hτ_def
  have hτc : Continuous τ :=
    (DomAddAct.continuous_mk.comp continuous_neg).vadd continuous_const
  have hτ0 : τ 0 = F := by simp [τ]
  have hτae : ∀ s, (τ s : ℂ → ℂ) =ᵐ[volume] fun x => f (x - s) := by
    intro s
    have h1 := DomAddAct.vadd_Lp_ae_eq (DomAddAct.mk (-s)) F
    have h2 : (fun x => (F : ℂ → ℂ) (-s + x)) =ᵐ[volume] fun x => f (-s + x) :=
      (measurePreserving_add_left volume (-s)).quasiMeasurePreserving.ae_eq_comp hf.coeFn_toLp
    filter_upwards [h1, h2] with x hx1 hx2
    rw [hx1, Equiv.symm_apply_apply, vadd_eq_add, hx2, neg_add_eq_sub]
  have hτn : ∀ s, eLpNorm (fun x => f (x - s) - f x) 2 volume = ENNReal.ofReal ‖τ s - F‖ := by
    intro s
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]
    apply eLpNorm_congr_ae
    filter_upwards [Lp.coeFn_sub (τ s) F, hτae s, hf.coeFn_toLp] with x h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3]
  have hloc : LocallyIntegrable f := hf.locallyIntegrable (by norm_num)
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨e, he0, heε⟩ : ∃ e : ℝ, 0 < e ∧ ENNReal.ofReal e ≤ ε := by
    by_cases htop : ε = ⊤
    · exact ⟨1, one_pos, by rw [htop]; exact le_top⟩
    · refine ⟨ε.toReal, ENNReal.toReal_pos hε.ne' htop, ?_⟩
      rw [ENNReal.ofReal_toReal htop]
  have hc := Metric.continuousAt_iff.1 (hτc.continuousAt (x := (0 : ℂ))) e he0
  obtain ⟨r, hr0, hr⟩ := hc
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hr0
  filter_upwards [eventually_ge_atTop N] with n hn
  have hrn : 1 / ((n : ℝ) + 1) ≤ r := by
    have h1 : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hn 1)
    linarith
  have hpt : ∀ x, molF n f x - f x = ∫ t, mollR n t • (f (x - t) - f x) := by
    intro x
    rw [molF_apply_swap]
    simp_rw [smul_sub]
    rw [integral_sub (integrable_mollR_smul n hloc x) ((integrable_mollR n).smul_const (f x)),
      integral_smul_const, integral_mollR, one_smul]
  have hmeas : Measurable (Function.uncurry fun x t : ℂ =>
      ENNReal.ofReal (mollR n t) * ‖f (x - t) - f x‖ₑ ^ (2 : ℝ)) := by
    apply Measurable.mul
    · exact ENNReal.measurable_ofReal.comp ((continuous_mollR n).measurable.comp measurable_snd)
    · exact (((hfm.comp (measurable_fst.sub measurable_snd)).sub
        (hfm.comp measurable_fst)).enorm).pow_const _
  have hinner : ∀ t, ENNReal.ofReal (mollR n t) * ∫⁻ x, ‖f (x - t) - f x‖ₑ ^ (2 : ℝ)
      ≤ ENNReal.ofReal (mollR n t) * ENNReal.ofReal e ^ (2 : ℝ) := by
    intro t
    by_cases ht : ‖t‖ < r
    · refine mul_le_mul' le_rfl ?_
      rw [lintegral_eq_eLpNorm_sq (g := fun x => f (x - t) - f x)
        ((hfm.comp (measurable_id.sub measurable_const)).sub hfm).aestronglyMeasurable, hτn t]
      refine ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal ?_) (by norm_num)
      have := hr (show dist t 0 < r by rwa [dist_zero_right])
      rw [hτ0, dist_eq_norm] at this
      exact this.le
    · rw [mollR_eq_zero (hrn.trans (not_lt.1 ht)), ENNReal.ofReal_zero, zero_mul, zero_mul]
  have hbound : ∫⁻ x, ‖molF n f x - f x‖ₑ ^ (2 : ℝ) ≤ ENNReal.ofReal e ^ (2 : ℝ) := by
    calc ∫⁻ x, ‖molF n f x - f x‖ₑ ^ (2 : ℝ)
        = ∫⁻ x, ‖∫ t, mollR n t • (f (x - t) - f x)‖ₑ ^ (2 : ℝ) := by simp_rw [hpt]
      _ ≤ ∫⁻ x, ∫⁻ t, ENNReal.ofReal (mollR n t) * ‖f (x - t) - f x‖ₑ ^ (2 : ℝ) :=
          lintegral_mono fun x => enorm_integral_smul_sq_le _ (mollR_nonneg n)
            (continuous_mollR n).measurable (lintegral_mollR n) _
            ((hfm.comp (measurable_const.sub measurable_id)).sub measurable_const).aemeasurable
      _ = ∫⁻ t, ∫⁻ x, ENNReal.ofReal (mollR n t) * ‖f (x - t) - f x‖ₑ ^ (2 : ℝ) :=
          lintegral_lintegral_swap hmeas.aemeasurable
      _ = ∫⁻ t, ENNReal.ofReal (mollR n t) * ∫⁻ x, ‖f (x - t) - f x‖ₑ ^ (2 : ℝ) := by
          congr 1; funext t
          exact lintegral_const_mul _ ((((hfm.comp (measurable_id.sub measurable_const)).sub
            hfm).enorm).pow_const _)
      _ ≤ ∫⁻ t, ENNReal.ofReal (mollR n t) * ENNReal.ofReal e ^ (2 : ℝ) := lintegral_mono hinner
      _ = ENNReal.ofReal e ^ (2 : ℝ) := by
          have hmR : Measurable fun t => ENNReal.ofReal (mollR n t) :=
            ENNReal.measurable_ofReal.comp (continuous_mollR n).measurable
          rw [lintegral_mul_const _ hmR, lintegral_mollR, one_mul]
  calc eLpNorm (fun x => molF n f x - f x) 2 volume
      = (∫⁻ x, ‖molF n f x - f x‖ₑ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) :=
        eLpNorm_two_eq ((contDiff_molF_aux n hloc).continuous.aestronglyMeasurable.sub
          hfm.aestronglyMeasurable)
    _ ≤ (ENNReal.ofReal e ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := ENNReal.rpow_le_rpow hbound (by norm_num)
    _ = ENNReal.ofReal e := by rw [← ENNReal.rpow_mul]; norm_num
    _ ≤ ε := heε

/-! ### Derivatives of `f ⋆ k` fall on the kernel -/

/-- The directional derivative `∂_v k` of a real kernel `k`. -/
noncomputable def dirK (k : ℂ → ℝ) (v : ℂ) : ℂ → ℝ := fun a => fderiv ℝ k a v

lemma contDiff_dirK {k : ℂ → ℝ} (hk : ContDiff ℝ ∞ k) (v : ℂ) : ContDiff ℝ ∞ (dirK k v) :=
  (hk.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const

lemma hasCompactSupport_dirK {k : ℂ → ℝ} (hk : HasCompactSupport k) (v : ℂ) :
    HasCompactSupport (dirK k v) :=
  hk.fderiv_apply (𝕜 := ℝ) v

lemma fderiv_conv_apply {f : ℂ → ℂ} {k : ℂ → ℝ} (hk : ContDiff ℝ ∞ k) (hks : HasCompactSupport k)
    (hf : LocallyIntegrable f) (x v : ℂ) :
    fderiv ℝ (f ⋆[smulL, volume] k) x v = (f ⋆[smulL, volume] dirK k v) x := by
  have h := hks.hasFDerivAt_convolution_right smulL hf (hk.of_le (by simp)) x
  rw [h.fderiv]
  exact convolution_precompR_apply smulL hf (hks.fderiv ℝ) (hk.continuous_fderiv (by simp)) x v

lemma fderiv_fderiv_apply_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : ℂ → E}
    (hF : ContDiff ℝ ∞ F) (x v : ℂ) :
    fderiv ℝ (fderiv ℝ F) x v v = fderiv ℝ (fun y => fderiv ℝ F y v) x v := by
  have hc : DifferentiableAt ℝ (fderiv ℝ F) x :=
    ((hF.fderiv_right (m := ∞) le_rfl).differentiable (by simp)) x
  rw [fderiv_clm_apply hc (differentiableAt_const v)]
  simp

/-- The Euclidean Laplacian of a real kernel, `∂ₓ²k + ∂_y²k`. -/
noncomputable def lapR (k : ℂ → ℝ) : ℂ → ℝ := fun a => dirK (dirK k 1) 1 a + dirK (dirK k Complex.I) Complex.I a

lemma contDiff_lapR {k : ℂ → ℝ} (hk : ContDiff ℝ ∞ k) : ContDiff ℝ ∞ (lapR k) :=
  (contDiff_dirK (contDiff_dirK hk 1) 1).add (contDiff_dirK (contDiff_dirK hk _) _)

lemma hasCompactSupport_lapR {k : ℂ → ℝ} (hk : HasCompactSupport k) : HasCompactSupport (lapR k) :=
  (hasCompactSupport_dirK (hasCompactSupport_dirK hk 1) 1).add
    (hasCompactSupport_dirK (hasCompactSupport_dirK hk _) _)

/-- **`Δ_E(f ⋆ k) = f ⋆ Δ_E k`.** -/
lemma lapE_conv {f : ℂ → ℂ} {k : ℂ → ℝ} (hk : ContDiff ℝ ∞ k) (hks : HasCompactSupport k)
    (hf : LocallyIntegrable f) (x : ℂ) :
    lapE (f ⋆[smulL, volume] k) x = (f ⋆[smulL, volume] lapR k) x := by
  have hF : ContDiff ℝ ∞ (f ⋆[smulL, volume] k) := hks.contDiff_convolution_right smulL hf hk
  have e : ∀ v, (fun y => fderiv ℝ (f ⋆[smulL, volume] k) y v) = f ⋆[smulL, volume] dirK k v :=
    fun v => funext fun y => fderiv_conv_apply hk hks hf y v
  have h1 := contDiff_dirK hk 1
  have hI := contDiff_dirK hk Complex.I
  rw [lapE, fderiv_fderiv_apply_eq hF, fderiv_fderiv_apply_eq hF, e, e,
    fderiv_conv_apply h1 (hasCompactSupport_dirK hks 1) hf,
    fderiv_conv_apply hI (hasCompactSupport_dirK hks _) hf]
  have ex1 := (hasCompactSupport_dirK (hasCompactSupport_dirK hks 1) 1).convolutionExists_right smulL hf
    (contDiff_dirK h1 1).continuous x
  have exI := (hasCompactSupport_dirK (hasCompactSupport_dirK hks Complex.I) Complex.I).convolutionExists_right
    smulL hf (contDiff_dirK hI Complex.I).continuous x
  exact (ex1.distrib_add exI).symm

/-! ### The kernel `t ↦ k(x - t)` -/

lemma fderiv_comp_sub_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {G : ℂ → E}
    (hG : Differentiable ℝ G) (x t v : ℂ) :
    fderiv ℝ (fun s => G (x - s)) t v = -(fderiv ℝ G (x - t) v) := by
  have h : HasFDerivAt (fun s => G (x - s))
      ((fderiv ℝ G (x - t)).comp (-(ContinuousLinearMap.id ℝ ℂ))) t :=
    (hG (x - t)).hasFDerivAt.comp t ((hasFDerivAt_id t).const_sub x)
  rw [h.fderiv]; simp

lemma fderiv_ofReal_comp_apply {k : ℂ → ℝ} (hk : Differentiable ℝ k) (a v : ℂ) :
    fderiv ℝ (fun t => ((k t : ℝ) : ℂ)) a v = ((fderiv ℝ k a v : ℝ) : ℂ) := by
  have h : HasFDerivAt (fun t => ((k t : ℝ) : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ k a)) a :=
    Complex.ofRealCLM.hasFDerivAt.comp a (hk a).hasFDerivAt
  rw [h.fderiv]; simp

/-- `Δ_E` of `t ↦ k(x - t)` (as a complex function) is `(Δ_E k)(x - t)`. -/
lemma lapE_kernel {k : ℂ → ℝ} (hk : ContDiff ℝ ∞ k) (x t : ℂ) :
    lapE (fun s => ((k (x - s) : ℝ) : ℂ)) t = ((lapR k (x - t) : ℝ) : ℂ) := by
  set Ψ : ℂ → ℂ := fun a => ((k a : ℝ) : ℂ) with hΨ
  have hΨs : ContDiff ℝ ∞ Ψ := Complex.ofRealCLM.contDiff.comp hk
  have hk1 : Differentiable ℝ k := hk.differentiable (by simp)
  have hdir : ∀ v, (fun a => fderiv ℝ Ψ a v) = fun a => ((dirK k v a : ℝ) : ℂ) :=
    fun v => funext fun a => fderiv_ofReal_comp_apply hk1 a v
  have hG : ContDiff ℝ ∞ (fun s => Ψ (x - s)) := hΨs.comp (contDiff_const.sub contDiff_id)
  have hstep : ∀ v, (fun y => fderiv ℝ (fun s => Ψ (x - s)) y v)
      = fun y => -(((dirK k v (x - y)) : ℝ) : ℂ) := by
    intro v; funext y
    rw [fderiv_comp_sub_apply (hΨs.differentiable (by simp)) x y v]
    rw [show fderiv ℝ Ψ (x - y) v = ((dirK k v (x - y) : ℝ) : ℂ) from congrFun (hdir v) (x - y)]
  have hsecond : ∀ v, fderiv ℝ (fun y => -(((dirK k v (x - y)) : ℝ) : ℂ)) t v
      = ((dirK (dirK k v) v (x - t) : ℝ) : ℂ) := by
    intro v
    have hd : Differentiable ℝ (fun a => ((dirK k v a : ℝ) : ℂ)) :=
      (Complex.ofRealCLM.contDiff.comp (contDiff_dirK hk v)).differentiable (by simp)
    have h1 : fderiv ℝ (fun y => -(((dirK k v (x - y)) : ℝ) : ℂ)) t v
        = -(fderiv ℝ (fun y => (((dirK k v (x - y)) : ℝ) : ℂ)) t v) := by
      rw [show (fun y => -(((dirK k v (x - y)) : ℝ) : ℂ))
          = -(fun y => (((dirK k v (x - y)) : ℝ) : ℂ)) from rfl, fderiv_neg]; rfl
    rw [h1, fderiv_comp_sub_apply hd x t v, neg_neg,
      fderiv_ofReal_comp_apply ((contDiff_dirK hk v).differentiable (by simp))]
    rfl
  rw [lapE, fderiv_fderiv_apply_eq hG, fderiv_fderiv_apply_eq hG, hstep, hstep, hsecond, hsecond]
  simp [lapR]

end Qschubert
