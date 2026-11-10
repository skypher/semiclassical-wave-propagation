import Qschubert.KLRevParseval

/-!
# The log-cosh pairing for the reverse KL Parseval identity

Part 1: Plancherel in the normalization `Â(t) = ∫ u(ν) e^{iνt} dν`:
`∫ Â_u conj Â_v = 2π ∫ u conj v` (`integral_hatA_mul_conj`), shifts in `t` are modulations in `ν`
(`hatA_add`, `hatA_neg`), and the cross term vanishes for `u` supported in `(0, ∞)` (`integral_hatA_shift_cross`).
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set FourierTransform

variable {u v : ℝ → ℂ}

lemma memLp_two_of_isKTest (hu : IsKTest u) : MemLp u 2 :=
  hu.continuous.memLp_of_hasCompactSupport hu.compact

/-- **Plancherel**: `∫ Â_u conj Â_v = 2π ∫ u conj v`. -/
theorem integral_hatA_mul_conj (hu : Continuous u) (hcu : HasCompactSupport u)
    (hv : Continuous v) (hcv : HasCompactSupport v) :
    ∫ t, hatA u t * (starRingEnd ℂ) (hatA v t) = (2 * Real.pi : ℂ) * ∫ x, u x * (starRingEnd ℂ) (v x) := by
  set c : ℝ := -(2 * Real.pi)⁻¹
  have hc : c ≠ 0 := neg_ne_zero.2 (inv_ne_zero (by positivity))
  have hP := integral_conj_fourier_mul_fourier (hv.integrable_of_hasCompactSupport hcv)
    (hv.memLp_of_hasCompactSupport hcv) (hu.integrable_of_hasCompactSupport hcu) (hu.memLp_of_hasCompactSupport hcu)
  have e : (fun t => hatA u t * (starRingEnd ℂ) (hatA v t))
      = fun t => (starRingEnd ℂ) (𝓕 v (c * t)) * 𝓕 u (c * t) := by
    funext t; rw [hatA_eq, hatA_eq]; ring
  rw [e, Measure.integral_comp_mul_left (fun ξ => (starRingEnd ℂ) (𝓕 v ξ) * 𝓕 u ξ) c, hP]
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  rw [show |c⁻¹| = 2 * Real.pi by simp [c, abs_of_pos hpi], Complex.real_smul]
  push_cast
  congr 1
  exact integral_congr_ae (Eventually.of_forall fun x => by simp only; ring)

lemma hatA_add (u : ℝ → ℂ) (α β : ℝ) :
    hatA u (α + β) = hatA (fun ν => u ν * Complex.exp (ν * α * I)) β := by
  simp only [hatA]
  refine integral_congr_ae (Eventually.of_forall fun ν => ?_)
  simp only
  rw [show (ν : ℂ) * ((α + β : ℝ) : ℂ) * I = ν * α * I + ν * β * I by push_cast; ring, Complex.exp_add]; ring

lemma hatA_neg (u : ℝ → ℂ) (β : ℝ) : hatA u (-β) = hatA (fun ν => u (-ν)) β := by
  simp only [hatA]
  rw [← integral_neg_eq_self (fun ν : ℝ => Complex.exp (ν * ((-β : ℝ) : ℂ) * I) * u ν)]
  refine integral_congr_ae (Eventually.of_forall fun ν => ?_)
  simp only; push_cast; ring_nf

/-- **The cross term vanishes**: `∫_β Â_a(α+β) conj Â_a(α-β) dβ = 0` for `a` supported in `(0, ∞)`. -/
theorem integral_hatA_shift_cross {a : ℝ → ℂ} (ha : IsKTest a) (α : ℝ) :
    ∫ β, hatA a (α + β) * (starRingEnd ℂ) (hatA a (α - β)) = 0 := by
  set u₁ : ℝ → ℂ := fun ν => a ν * Complex.exp (ν * α * I)
  have hu₁ : Continuous u₁ := ha.continuous.mul (by fun_prop)
  have hcu₁ : HasCompactSupport u₁ := ha.compact.mul_right
  have e : ∀ β : ℝ, hatA a (α + β) * (starRingEnd ℂ) (hatA a (α - β))
      = hatA u₁ β * (starRingEnd ℂ) (hatA (fun ν => u₁ (-ν)) β) := by
    intro β
    rw [hatA_add, sub_eq_add_neg, hatA_add, hatA_neg]
  simp_rw [e]
  rw [integral_hatA_mul_conj (v := fun ν => u₁ (-ν)) hu₁ hcu₁ (hu₁.comp continuous_neg)
    (hcu₁.comp_homeomorph (Homeomorph.neg ℝ))]
  have h0 : ∀ x, u₁ x * (starRingEnd ℂ) (u₁ (-x)) = 0 := by
    intro x
    rcases le_or_gt x 0 with hx | hx
    · simp [u₁, ha.eq_zero_of_nonpos hx]
    · simp [u₁, ha.eq_zero_of_nonpos (by linarith : -x ≤ 0)]
  simp [h0]

/-- `∫_α Â_a(α+β) conj Â_a(α-β) dα = 2π ∫ |a(ν)|² e^{2iνβ} dν`. -/
theorem integral_hatA_shift_diag {a : ℝ → ℂ} (ha : IsKTest a) (β : ℝ) :
    ∫ α, hatA a (α + β) * (starRingEnd ℂ) (hatA a (α - β))
      = (2 * Real.pi : ℂ) * ∫ ν, ((‖a ν‖ ^ 2 : ℝ) : ℂ) * Complex.exp (2 * ν * β * I) := by
  set u₂ : ℝ → ℂ := fun ν => a ν * Complex.exp (ν * β * I)
  set u₃ : ℝ → ℂ := fun ν => a ν * Complex.exp (ν * (-β : ℝ) * I)
  have e : ∀ α : ℝ, hatA a (α + β) * (starRingEnd ℂ) (hatA a (α - β))
      = hatA u₂ α * (starRingEnd ℂ) (hatA u₃ α) := by
    intro α
    rw [add_comm, hatA_add, sub_eq_neg_add, hatA_add]
  simp_rw [e]
  rw [integral_hatA_mul_conj (u := u₂) (v := u₃) (ha.continuous.mul (by fun_prop)) ha.compact.mul_right
    (ha.continuous.mul (by fun_prop)) ha.compact.mul_right]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun ν => ?_)
  simp only [u₂, u₃, map_mul]
  rw [← Complex.exp_conj, Complex.ofReal_pow, ← Complex.mul_conj']
  have : (starRingEnd ℂ) ((ν : ℂ) * ((-β : ℝ) : ℂ) * I) = ν * β * I := by
    simp [Complex.conj_ofReal]
  rw [this, show Complex.exp (2 * ν * β * I) = Complex.exp (ν * β * I) * Complex.exp (ν * β * I) by
    rw [← Complex.exp_add]; ring_nf]
  ring

/-! ### Part 2: derivatives of `Â` and the Fourier transform of `sech²` -/

/-- `d/dt Â_k(t) = Â_{iνk}(t)`. -/
theorem hasDerivAt_hatA {k : ℝ → ℂ} (hk : IsKTest k) (t₀ : ℝ) :
    HasDerivAt (hatA k) (hatA (fun ν => (ν : ℂ) * I * k ν) t₀) t₀ := by
  have hb : Integrable fun ν : ℝ => |ν| * ‖k ν‖ :=
    ((continuous_abs.mul hk.continuous.norm).integrable_of_hasCompactSupport hk.compact.norm.mul_left)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℝ) (μ := (volume : Measure ℝ))
    (F := fun t ν => Complex.exp ((ν : ℂ) * t * I) * k ν)
    (F' := fun t ν => Complex.exp ((ν : ℂ) * t * I) * ((ν : ℂ) * I * k ν))
    (bound := fun ν => |ν| * ‖k ν‖) (x₀ := t₀) (s := univ) Filter.univ_mem
    (Eventually.of_forall fun t => (Continuous.aestronglyMeasurable (by fun_prop) |>.mul
      hk.continuous.aestronglyMeasurable))
    ((by fun_prop : Continuous fun ν : ℝ => Complex.exp ((ν : ℂ) * t₀ * I)).mul hk.continuous
      |>.integrable_of_hasCompactSupport hk.compact.mul_left)
    ((Continuous.aestronglyMeasurable (by fun_prop)).mul
      ((by fun_prop : Continuous fun ν : ℝ => (ν : ℂ) * I).mul hk.continuous).aestronglyMeasurable)
    (Eventually.of_forall fun ν t _ => by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      rw [show (ν : ℂ) * t * I = ((ν * t : ℝ) : ℂ) * I by push_cast; ring, Complex.norm_exp_ofReal_mul_I,
        one_mul])
    hb
    (Eventually.of_forall fun ν t _ => by
      have h1 : HasDerivAt (fun t : ℝ => (ν : ℂ) * t * I) ((ν : ℂ) * I) t := by
        have := ((hasDerivAt_id t).ofReal_comp.const_mul (ν : ℂ)).mul_const I
        simpa using this
      exact (h1.cexp.mul_const (k ν)).congr_deriv (by ring))
  exact h.2

lemma IsKTest.mul_nuI {k : ℝ → ℂ} (hk : IsKTest k) : IsKTest fun ν => (ν : ℂ) * I * k ν :=
  hk.mul_smooth (Complex.ofRealCLM.contDiff.mul contDiff_const)

/-- `Γ(1 + iν) Γ(1 - iν) = πν / sinh(πν)` for `ν ≠ 0`. -/
lemma Gamma_one_add_mul_I {ν : ℝ} (hν : ν ≠ 0) :
    Complex.Gamma (1 + ν * I) * Complex.Gamma (1 - ν * I) = ((Real.pi * ν / Real.sinh (Real.pi * ν) : ℝ) : ℂ) := by
  have h := Complex.Gamma_mul_Gamma_one_sub ((ν : ℂ) * I)
  have hz : ((ν : ℂ) * I) ≠ 0 := mul_ne_zero (by exact_mod_cast hν) Complex.I_ne_zero
  rw [add_comm (1 : ℂ), Complex.Gamma_add_one _ hz]
  have hs : Complex.sin (Real.pi * (ν * I)) = Complex.sinh (Real.pi * ν) * I := by
    rw [show (Real.pi : ℂ) * (ν * I) = (Real.pi * ν) * I by ring, Complex.sin_mul_I]
  rw [hs] at h
  have hsh : Real.sinh (Real.pi * ν) ≠ 0 := Real.sinh_ne_zero.2 (mul_ne_zero Real.pi_ne_zero hν)
  have hsh' : Complex.sinh ((Real.pi : ℂ) * ν) ≠ 0 := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_sinh]; exact_mod_cast hsh
  calc (ν : ℂ) * I * Complex.Gamma (ν * I) * Complex.Gamma (1 - ν * I)
      = (ν : ℂ) * I * (Complex.Gamma (ν * I) * Complex.Gamma (1 - ν * I)) := by ring
    _ = (ν : ℂ) * I * (Real.pi / (Complex.sinh (Real.pi * ν) * I)) := by rw [h]
    _ = _ := by
      push_cast
      field_simp

/-- **`∫ e^{2iνβ} sech² β dβ = 2πν / sinh(πν)`** for `ν ≠ 0`. -/
theorem integral_exp_mul_sech_sq {ν : ℝ} (hν : ν ≠ 0) :
    ∫ β : ℝ, Complex.exp ((2 * ν : ℝ) * β * I) * ((Real.cosh β : ℝ) : ℂ) ^ (-(2 : ℂ))
      = ((2 * Real.pi * ν / Real.sinh (Real.pi * ν) : ℝ) : ℂ) := by
  rw [integral_exp_mul_cosh_cpow (s := 2) (by norm_num) (2 * ν)]
  have e1 : ((2 : ℂ) + ((2 * ν : ℝ) : ℂ) * I) / 2 = 1 + ν * I := by push_cast; ring
  have e2 : ((2 : ℂ) - ((2 * ν : ℝ) : ℂ) * I) / 2 = 1 - ν * I := by push_cast; ring
  rw [e1, e2, Gamma_one_add_mul_I hν, show (2 : ℂ) = ((1 : ℕ) : ℂ) + 1 by norm_num, Complex.Gamma_nat_eq_factorial]
  norm_num
  ring

/-! ### Part 3: two integrations by parts against `log cosh` -/

lemma hatA_smul (c : ℂ) (k : ℝ → ℂ) (t : ℝ) : hatA (fun ν => c * k ν) t = c * hatA k t := by
  simp only [hatA]; rw [← MeasureTheory.integral_const_mul]
  exact integral_congr_ae (Eventually.of_forall fun ν => by simp only; ring)

lemma integrable_hatA_two {k : ℝ → ℂ} (hk : IsKTest k) : Integrable fun β : ℝ => hatA k (2 * β) :=
  (integrable_hatA hk).comp_mul_left' two_ne_zero

lemma integrable_abs_mul_hatA_two {k : ℝ → ℂ} (hk : IsKTest k) :
    Integrable fun β : ℝ => |β| * ‖hatA k (2 * β)‖ := by
  have h := ((integrable_mul_hatA hk).comp_mul_left' (two_ne_zero (α := ℝ))).const_mul (1 / 2)
  refine h.congr (Eventually.of_forall fun β => ?_)
  simp only [abs_mul, abs_two]; ring

lemma log_cosh_nonneg (β : ℝ) : 0 ≤ Real.log (Real.cosh β) := Real.log_nonneg (Real.one_le_cosh β)

lemma log_cosh_le_abs (β : ℝ) : Real.log (Real.cosh β) ≤ |β| := by
  rw [Real.log_le_iff_le_exp (Real.cosh_pos β), Real.cosh_eq]
  have h1 : Real.exp β ≤ Real.exp |β| := Real.exp_le_exp.2 (le_abs_self β)
  have h2 : Real.exp (-β) ≤ Real.exp |β| := Real.exp_le_exp.2 (neg_le_abs β)
  linarith

lemma abs_tanh_le_one (β : ℝ) : |Real.tanh β| ≤ 1 := by
  rw [Real.tanh_eq_sinh_div_cosh, abs_div, abs_of_pos (Real.cosh_pos β), div_le_one (Real.cosh_pos β)]
  have h1 := Real.cosh_sub_sinh β
  have h2 := Real.cosh_add_sinh β
  have := Real.exp_pos β
  have := Real.exp_pos (-β)
  rw [abs_le]; constructor <;> linarith

lemma hasDerivAt_log_cosh (β : ℝ) : HasDerivAt (fun β => Real.log (Real.cosh β)) (Real.tanh β) β := by
  have h := (Real.hasDerivAt_cosh β).log (Real.cosh_pos β).ne'
  rw [Real.tanh_eq_sinh_div_cosh]; exact h

lemma hasDerivAt_tanh' (β : ℝ) : HasDerivAt Real.tanh ((Real.cosh β ^ 2)⁻¹) β := by
  have hc := Real.cosh_pos β
  have h := (Real.hasDerivAt_sinh β).div (Real.hasDerivAt_cosh β) hc.ne'
  have e : Real.tanh = fun β => Real.sinh β / Real.cosh β := funext Real.tanh_eq_sinh_div_cosh
  rw [e]
  refine h.congr_deriv ?_
  have := Real.cosh_sq β
  field_simp
  nlinarith [this]

/-- **`∫ log cosh β · Â_r(2β) dβ = -(π/2) ∫ r(ν)/(ν sinh πν) dν`** for `r` smooth with compact support in `(0,∞)`. -/
theorem integral_log_cosh_hatA {r : ℝ → ℂ} (hr : IsKTest r) :
    ∫ β : ℝ, ((Real.log (Real.cosh β) : ℝ) : ℂ) * hatA r (2 * β)
      = -((Real.pi / 2 : ℝ) : ℂ) * ∫ ν, r ν * ((ν * Real.sinh (Real.pi * ν))⁻¹ : ℝ) := by
  set rt : ℝ → ℂ := fun ν => (-1 / 4 : ℂ) * ((ν : ℂ)⁻¹ * ((ν : ℂ)⁻¹ * r ν))
  have hrt : IsKTest rt := hr.inv_mul.inv_mul.mul_smooth (φ := fun _ => (-1 / 4 : ℂ)) contDiff_const |> fun h => h
  have hrt1 := hrt.mul_nuI
  set rt1 : ℝ → ℂ := fun ν => (ν : ℂ) * I * rt ν
  have hrt2_eq : (fun ν : ℝ => (ν : ℂ) * I * rt1 ν) = fun ν : ℝ => (1 / 4 : ℂ) * r ν := by
    funext ν
    by_cases hν : ν = 0
    · simp [rt1, rt, hν, hr.eq_zero_of_nonpos le_rfl]
    · have : (ν : ℂ) ≠ 0 := by exact_mod_cast hν
      simp only [rt1, rt]
      field_simp
      rw [Complex.I_sq]; ring
  set Rt : ℝ → ℂ := fun β => hatA rt (2 * β)
  set Rt1 : ℝ → ℂ := fun β => 2 * hatA rt1 (2 * β)
  have hRt : ∀ β, HasDerivAt Rt (Rt1 β) β := by
    intro β
    have h := (hasDerivAt_hatA hrt (2 * β)).scomp β ((hasDerivAt_id' β).const_mul (2 : ℝ))
    refine h.congr_deriv ?_
    simp only [Rt1, rt1, Complex.real_smul]; push_cast; ring
  have hRt1 : ∀ β, HasDerivAt Rt1 (hatA r (2 * β)) β := by
    intro β
    have h := ((hasDerivAt_hatA hrt1 (2 * β)).scomp β ((hasDerivAt_id' β).const_mul (2 : ℝ))).const_mul (2 : ℂ)
    refine h.congr_deriv ?_
    rw [hrt2_eq, hatA_smul, Complex.real_smul]; push_cast; ring
  set L : ℝ → ℂ := fun β => ((Real.log (Real.cosh β) : ℝ) : ℂ)
  set T : ℝ → ℂ := fun β => ((Real.tanh β : ℝ) : ℂ)
  set T' : ℝ → ℂ := fun β => (((Real.cosh β ^ 2)⁻¹ : ℝ) : ℂ)
  have hL : ∀ β, HasDerivAt L (T β) β := fun β => (hasDerivAt_log_cosh β).ofReal_comp
  have hT : ∀ β, HasDerivAt T (T' β) β := fun β => (hasDerivAt_tanh' β).ofReal_comp
  have hU : ∀ β, HasDerivAt (fun β => L β * Rt1 β - T β * Rt β) (L β * hatA r (2 * β) - T' β * Rt β) β := by
    intro β
    refine (((hL β).mul (hRt1 β)).sub ((hT β).mul (hRt β))).congr_deriv ?_
    ring
  -- integrability
  have hcR : ∀ {k : ℝ → ℂ}, IsKTest k → Continuous fun β : ℝ => hatA k (2 * β) :=
    fun hk => (continuous_hatA hk).comp (continuous_const.mul continuous_id)
  have hcL : Continuous L := Complex.continuous_ofReal.comp
    (Real.continuous_cosh.log fun β => (Real.cosh_pos β).ne')
  have hcT : Continuous T := Complex.continuous_ofReal.comp
    ((Real.continuous_sinh.div Real.continuous_cosh fun β => (Real.cosh_pos β).ne').congr
      fun β => (Real.tanh_eq_sinh_div_cosh β).symm)
  have hcT' : Continuous T' := Complex.continuous_ofReal.comp
    ((Real.continuous_cosh.pow 2).inv₀ fun β => (pow_pos (Real.cosh_pos β) 2).ne')
  have hnL : ∀ β, ‖L β‖ ≤ |β| := fun β => by
    simp only [L, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (log_cosh_nonneg β)]
    exact log_cosh_le_abs β
  have hnT : ∀ β, ‖T β‖ ≤ 1 := fun β => by
    simp only [T, Complex.norm_real, Real.norm_eq_abs]; exact abs_tanh_le_one β
  have hnT' : ∀ β, ‖T' β‖ ≤ 1 := fun β => by
    simp only [T', Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity)]; exact inv_cosh_sq_le_one β
  have iLR : Integrable fun β => L β * hatA r (2 * β) := by
    refine (integrable_abs_mul_hatA_two hr).mono' (hcL.mul (hcR hr)).aestronglyMeasurable
      (Eventually.of_forall fun β => ?_)
    rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hnL β) (norm_nonneg _)
  have iTRt : Integrable fun β => T' β * Rt β := by
    refine (integrable_hatA_two hrt).norm.mono' (hcT'.mul (hcR hrt)).aestronglyMeasurable
      (Eventually.of_forall fun β => ?_)
    rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (hnT' β)
  have iLRt1 : Integrable fun β => L β * Rt1 β := by
    refine ((integrable_abs_mul_hatA_two hrt1).const_mul 2).mono'
      (hcL.mul (continuous_const.mul (hcR hrt1))).aestronglyMeasurable (Eventually.of_forall fun β => ?_)
    simp only [Rt1, norm_mul, Complex.norm_ofNat]
    nlinarith [hnL β, norm_nonneg (hatA rt1 (2 * β)), norm_nonneg (L β)]
  have iTRt' : Integrable fun β => T β * Rt β := by
    refine (integrable_hatA_two hrt).norm.mono' (hcT.mul (hcR hrt)).aestronglyMeasurable
      (Eventually.of_forall fun β => ?_)
    rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (hnT β)
  have h0 := integral_eq_zero_of_hasDerivAt_of_integrable hU (iLR.sub iTRt) (iLRt1.sub iTRt')
  rw [integral_sub iLR iTRt, sub_eq_zero] at h0
  change ∫ β, L β * hatA r (2 * β) = _
  rw [h0]
  -- `∫ sech² β · Â_rt(2β) dβ = ∫ rt(ν) · 2πν/sinh(πν) dν`
  set H : ℝ × ℝ → ℂ := fun q => T' q.1 * (Complex.exp ((q.2 : ℂ) * ((2 * q.1 : ℝ) : ℂ) * I) * rt q.2)
  have hH : Integrable H ((volume : Measure ℝ).prod volume) := by
    refine (integrable_inv_cosh_sq.mul_prod hrt.integrable.norm).mono'
      ((hcT'.comp continuous_fst).mul ((by fun_prop : Continuous fun q : ℝ × ℝ =>
        Complex.exp ((q.2 : ℂ) * ((2 * q.1 : ℝ) : ℂ) * I)).mul (hrt.continuous.comp continuous_snd))).aestronglyMeasurable
      (Eventually.of_forall fun q => ?_)
    simp only [H, T', norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [show (q.2 : ℂ) * ((2 * q.1 : ℝ) : ℂ) * I = ((q.2 * (2 * q.1) : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, one_mul, abs_of_nonneg (by positivity)]
  have e1 : ∫ β, T' β * Rt β = ∫ β, ∫ ν, H (β, ν) := by
    refine integral_congr_ae (Eventually.of_forall fun β => ?_)
    simp only [Rt, H, hatA]; rw [← MeasureTheory.integral_const_mul]
  have hcpow : ∀ x : ℝ, ((x : ℝ) : ℂ) ^ (-(2 : ℂ)) = (((x ^ 2)⁻¹ : ℝ) : ℂ) := by
    intro x
    rw [Complex.cpow_neg, show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast]; push_cast; ring
  have e2 : ∀ ν : ℝ, ∫ β, H (β, ν) = rt ν * ((2 * Real.pi * ν / Real.sinh (Real.pi * ν) : ℝ) : ℂ) := by
    intro ν
    by_cases hν : ν = 0
    · simp [H, rt, hν, hr.eq_zero_of_nonpos le_rfl]
    · rw [← integral_exp_mul_sech_sq hν, ← MeasureTheory.integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun β => ?_)
      simp only [H, T', hcpow]
      rw [show ((ν : ℝ) : ℂ) * ((2 * β : ℝ) : ℂ) * I = ((2 * ν : ℝ) : ℂ) * β * I by push_cast; ring]; ring
  rw [e1, integral_integral_swap (f := fun β ν => H (β, ν)) hH, integral_congr_ae (Eventually.of_forall e2),
    ← MeasureTheory.integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun ν => ?_)
  simp only [rt]
  by_cases hν : ν = 0
  · simp [hν, hr.eq_zero_of_nonpos le_rfl]
  · have hs : Real.sinh (Real.pi * ν) ≠ 0 := Real.sinh_ne_zero.2 (mul_ne_zero Real.pi_ne_zero hν)
    have : (ν : ℂ) ≠ 0 := by exact_mod_cast hν
    have hs' : ((Real.sinh (Real.pi * ν) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs
    push_cast
    field_simp
    ring

/-! ### Part 4: the log-cosh pairing on `ℝ²` -/

lemma IsKTest.normSq {a : ℝ → ℂ} (ha : IsKTest a) : IsKTest fun ν => ((‖a ν‖ ^ 2 : ℝ) : ℂ) := by
  have e : (fun ν => ((‖a ν‖ ^ 2 : ℝ) : ℂ)) = fun ν => a ν * (starRingEnd ℂ) (a ν) := by
    funext ν; rw [Complex.mul_conj']; push_cast; ring
  rw [e]
  refine ⟨ha.smooth.mul (Complex.conjCLE.contDiff.comp ha.smooth), ha.compact.mul_right,
    (tsupport_mul_subset_left (f := a)).trans ha.pos⟩

theorem integral_log_coshSum {a : ℝ → ℂ} (ha : IsKTest a) :
    ∫ p : ℝ × ℝ, ((Real.log (coshSum p) : ℝ) : ℂ) * (hatA a p.1 * (starRingEnd ℂ) (hatA a p.2))
      = -((2 * Real.pi ^ 2 : ℝ) : ℂ) * ∫ ν, ((‖a ν‖ ^ 2 : ℝ) : ℂ) * ((ν * Real.sinh (Real.pi * ν))⁻¹ : ℝ) := by
  have hA := integrable_hatA ha
  have hcA := continuous_hatA ha
  set Φ : ℝ × ℝ → ℂ := fun p => hatA a p.1 * (starRingEnd ℂ) (hatA a p.2)
  set F : ℝ × ℝ → ℂ := fun p => ((Real.log (coshSum p) : ℝ) : ℂ) * Φ p
  have hcΦ : Continuous Φ := (hcA.comp continuous_fst).mul (Complex.continuous_conj.comp (hcA.comp continuous_snd))
  have hcC : Continuous coshSum := by unfold coshSum; fun_prop
  have hcF : Continuous F := (Complex.continuous_ofReal.comp
    (hcC.log fun p => (coshSum_pos p).ne')).mul hcΦ
  have hAc : Integrable fun t => (starRingEnd ℂ) (hatA a t) :=
    hA.norm.mono' (Complex.continuous_conj.comp hcA).aestronglyMeasurable
      (Eventually.of_forall fun t => by simp)
  have hΦ : Integrable Φ ((volume : Measure ℝ).prod volume) := hA.mul_prod hAc
  -- the weight `(|t| + |u|) ‖Φ‖`
  set Gw : ℝ × ℝ → ℂ := fun p => (((|p.1| + |p.2|) * ‖Φ p‖ : ℝ) : ℂ)
  have hGw : Integrable Gw ((volume : Measure ℝ).prod volume) := by
    have h1 := (integrable_mul_hatA ha).mul_prod hA.norm
    have h2 := hA.norm.mul_prod (integrable_mul_hatA ha)
    have h12 := (h1.add h2).ofReal (𝕜 := ℂ)
    refine h12.congr (Eventually.of_forall fun p => ?_)
    simp only [Gw, Φ, Pi.add_apply, norm_mul, Complex.norm_conj]
    exact congrArg _ (by
      show _ = (|p.1| + |p.2|) * (‖hatA a p.1‖ * ‖hatA a p.2‖)
      ring)
  have hcGw : Continuous Gw := Complex.continuous_ofReal.comp
    ((continuous_abs.comp continuous_fst).add (continuous_abs.comp continuous_snd) |>.mul hcΦ.norm)
  -- pass to `(α, β)`
  set Ψ : ℝ × ℝ → ℂ := fun q => hatA a (q.1 + q.2) * (starRingEnd ℂ) (hatA a (q.1 - q.2))
  have hΨ : Integrable Ψ ((volume : Measure ℝ).prod volume) := by
    have := (integrable_comp_sumDiff_iff hcΦ.aestronglyMeasurable).2 hΦ
    exact this
  have hGwL : Integrable (fun q => Gw (sumDiff q)) ((volume : Measure ℝ).prod volume) :=
    (integrable_comp_sumDiff_iff hcGw.aestronglyMeasurable).2 hGw
  have hcΨ : Continuous Ψ := (hcA.comp (continuous_fst.add continuous_snd)).mul
    (Complex.continuous_conj.comp (hcA.comp (continuous_fst.sub continuous_snd)))
  have hbound : ∀ q : ℝ × ℝ, ∀ x : ℝ, (x = q.1 ∨ x = q.2) →
      ‖((Real.log (Real.cosh x) : ℝ) : ℂ) * Ψ q‖ ≤ ‖Gw (sumDiff q)‖ := by
    intro q x hx
    have hΨn : ‖Ψ q‖ = ‖hatA a (q.1 + q.2)‖ * ‖hatA a (q.1 - q.2)‖ := by
      simp only [Ψ, norm_mul, Complex.norm_conj]
    have hGn : ‖Gw (sumDiff q)‖ = (|q.1 + q.2| + |q.1 - q.2|) * (‖hatA a (q.1 + q.2)‖ * ‖hatA a (q.1 - q.2)‖) := by
      simp only [Gw, Φ, sumDiff_apply, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_norm]
      rw [abs_of_nonneg (by positivity)]
    have hle : Real.log (Real.cosh x) ≤ |q.1 + q.2| + |q.1 - q.2| := by
      refine (log_cosh_le_abs x).trans ?_
      rcases hx with rfl | rfl
      · have := abs_add_le (q.1 + q.2) (q.1 - q.2); rw [show q.1 + q.2 + (q.1 - q.2) = 2 * q.1 by ring,
          abs_mul, abs_two] at this; linarith [abs_nonneg q.1]
      · have := abs_sub (q.1 + q.2) (q.1 - q.2); rw [show q.1 + q.2 - (q.1 - q.2) = 2 * q.2 by ring,
          abs_mul, abs_two] at this; linarith [abs_nonneg q.2]
    rw [norm_mul, hΨn, hGn, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (log_cosh_nonneg x)]
    exact mul_le_mul_of_nonneg_right hle (by positivity)
  have hΨα : Integrable (fun q : ℝ × ℝ => ((Real.log (Real.cosh q.1) : ℝ) : ℂ) * Ψ q)
      ((volume : Measure ℝ).prod volume) :=
    hGwL.norm.mono' ((Complex.continuous_ofReal.comp ((Real.continuous_cosh.comp continuous_fst).log
      fun q => (Real.cosh_pos _).ne')).mul hcΨ).aestronglyMeasurable
      (Eventually.of_forall fun q => hbound q q.1 (Or.inl rfl))
  have hΨβ : Integrable (fun q : ℝ × ℝ => ((Real.log (Real.cosh q.2) : ℝ) : ℂ) * Ψ q)
      ((volume : Measure ℝ).prod volume) :=
    hGwL.norm.mono' ((Complex.continuous_ofReal.comp ((Real.continuous_cosh.comp continuous_snd).log
      fun q => (Real.cosh_pos _).ne')).mul hcΨ).aestronglyMeasurable
      (Eventually.of_forall fun q => hbound q q.2 (Or.inr rfl))
  -- `F ∘ L = (log 2 + log cosh α + log cosh β) Ψ`
  have hFL : ∀ q : ℝ × ℝ, F (sumDiff q) = ((Real.log 2 : ℝ) : ℂ) * Ψ q
      + ((Real.log (Real.cosh q.1) : ℝ) : ℂ) * Ψ q + ((Real.log (Real.cosh q.2) : ℝ) : ℂ) * Ψ q := by
    intro q
    have h1 : coshSum (sumDiff q) = 2 * Real.cosh q.1 * Real.cosh q.2 := by
      simp only [coshSum, sumDiff_apply]; rw [Real.cosh_add, Real.cosh_sub]; ring
    have hc1 := Real.cosh_pos q.1
    have hc2 := Real.cosh_pos q.2
    simp only [F, Φ, Ψ]
    rw [h1, Real.log_mul (by positivity) hc2.ne', Real.log_mul (by norm_num) hc1.ne']
    simp only [sumDiff_apply]
    push_cast; ring
  have hint : ∫ p, F p = 2 * ∫ q, F (sumDiff q) := by
    rw [integral_comp_sumDiff hcF.aestronglyMeasurable]; ring
  simp_rw [hFL] at hint
  change ∫ p, F p = _
  have i12 : Integrable (fun q : ℝ × ℝ => ((Real.log 2 : ℝ) : ℂ) * Ψ q
      + ((Real.log (Real.cosh q.1) : ℝ) : ℂ) * Ψ q) ((volume : Measure ℝ).prod volume) :=
    (hΨ.const_mul _).add hΨα
  rw [hint, show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl,
    integral_add i12 hΨβ, integral_add (hΨ.const_mul _) hΨα,
    MeasureTheory.integral_const_mul]
  -- the three terms
  have t1 : ∫ q, Ψ q ∂((volume : Measure ℝ).prod volume) = 0 := by
    rw [integral_prod _ hΨ]
    simp only [Ψ]
    simp_rw [integral_hatA_shift_cross ha]; simp
  have t2 : ∫ q, ((Real.log (Real.cosh q.1) : ℝ) : ℂ) * Ψ q ∂((volume : Measure ℝ).prod volume) = 0 := by
    rw [integral_prod _ hΨα]
    simp only [Ψ]
    simp_rw [MeasureTheory.integral_const_mul, integral_hatA_shift_cross ha]; simp
  have t3 : ∫ q, ((Real.log (Real.cosh q.2) : ℝ) : ℂ) * Ψ q ∂((volume : Measure ℝ).prod volume)
      = -((Real.pi ^ 2 : ℝ) : ℂ) * ∫ ν, ((‖a ν‖ ^ 2 : ℝ) : ℂ) * ((ν * Real.sinh (Real.pi * ν))⁻¹ : ℝ) := by
    rw [integral_prod_symm _ hΨβ]
    simp only [Ψ]
    simp_rw [MeasureTheory.integral_const_mul, integral_hatA_shift_diag ha]
    have hr := ha.normSq
    have e : ∀ β : ℝ, ((Real.log (Real.cosh β) : ℝ) : ℂ) * ((2 * Real.pi : ℂ)
        * ∫ ν, ((‖a ν‖ ^ 2 : ℝ) : ℂ) * Complex.exp (2 * ν * β * I))
        = (2 * Real.pi : ℂ) * (((Real.log (Real.cosh β) : ℝ) : ℂ) * hatA (fun ν => ((‖a ν‖ ^ 2 : ℝ) : ℂ)) (2 * β)) := by
      intro β
      simp only [hatA]
      have : ∫ ν, ((‖a ν‖ ^ 2 : ℝ) : ℂ) * Complex.exp (2 * ν * β * I)
          = ∫ ν : ℝ, Complex.exp ((ν : ℂ) * ((2 * β : ℝ) : ℂ) * I) * ((‖a ν‖ ^ 2 : ℝ) : ℂ) :=
        integral_congr_ae (Eventually.of_forall fun ν => by simp only; push_cast; ring_nf)
      rw [this]; ring
    simp_rw [e]
    rw [MeasureTheory.integral_const_mul, integral_log_cosh_hatA hr]
    push_cast; ring
  rw [t1, t2, t3]
  push_cast; ring

end Qschubert
