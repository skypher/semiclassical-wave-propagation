import Qschubert.KLFCY

/-!
# Lemma FC, case `Z = Y`: the kernel of `z²`

`gam y = Γ(1+iy)Γ(1-iy)` (`= πy/sinh πy`, and `1` at `y = 0`); `kerM2 ν ν' = ½ gam((ν+ν')/2) gam((ν-ν')/2)`
is `∫_0^∞ z K_{iν}K_{iν'} dz` (`integral_z_besselKi_mul`, the Mellin product formula at `s = 2`), and
`⟨ψ_a, z²ψ_b⟩_{dz/z} = ∬ conj a(ν) b(ν') kerM2(ν,ν')` (`Zform_eq_kerM2`).
Bound: `gam y ≤ 4(1 + π|y|)e^{-π|y|}` (`gam_le`).
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set
open scoped ENNReal

/-- `Γ(1+iy)Γ(1-iy)` as a real function. -/
noncomputable def gam (y : ℝ) : ℝ := if y = 0 then 1 else Real.pi * y / Real.sinh (Real.pi * y)

lemma gam_zero : gam 0 = 1 := by simp [gam]

lemma gam_of_ne {y : ℝ} (hy : y ≠ 0) : gam y = Real.pi * y / Real.sinh (Real.pi * y) := by simp [gam, hy]

lemma Gamma_mul_eq_gam (y : ℝ) :
    Complex.Gamma (1 + y * I) * Complex.Gamma (1 - y * I) = (gam y : ℂ) := by
  by_cases hy : y = 0
  · simp [hy, gam_zero]
  · rw [Gamma_one_add_mul_I hy, gam_of_ne hy]

lemma gam_neg (y : ℝ) : gam (-y) = gam y := by
  by_cases hy : y = 0
  · simp [hy]
  · rw [gam_of_ne hy, gam_of_ne (neg_ne_zero.2 hy), mul_neg, Real.sinh_neg, neg_div_neg_eq]

lemma gam_of_pos {x : ℝ} (hx : 0 < x) : 0 < gam x := by
  have hp := Real.pi_pos
  rw [gam_of_ne hx.ne']
  have : 0 < Real.sinh (Real.pi * x) := Real.sinh_pos_iff.2 (by positivity)
  positivity

lemma gam_pos (y : ℝ) : 0 < gam y := by
  rcases lt_trichotomy y 0 with h | h | h
  · rw [← gam_neg]; exact gam_of_pos (by linarith)
  · rw [h, gam_zero]; exact one_pos
  · exact gam_of_pos h

lemma measurable_gam : Measurable gam := by
  unfold gam
  refine Measurable.ite (measurableSet_eq_fun measurable_id measurable_const) measurable_const ?_
  fun_prop

/-- `x/sinh x ≤ 4(1 + x)e^{-x}` for `x > 0`. -/
lemma div_sinh_le {x : ℝ} (hx : 0 < x) : x / Real.sinh x ≤ 4 * (1 + x) * Real.exp (-x) := by
  have hs : 0 < Real.sinh x := Real.sinh_pos_iff.2 hx
  have hE := Real.exp_pos x
  have h1 := Real.add_one_le_exp x
  have hm : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hsh : Real.sinh x = (Real.exp x - Real.exp (-x)) / 2 := Real.sinh_eq x
  have key : x * Real.exp x ≤ 4 * (1 + x) * Real.sinh x := by
    rw [hsh]; nlinarith [mul_nonneg hx.le (sub_nonneg.2 hm), mul_pos hx hE]
  rw [div_le_iff₀ hs, Real.exp_neg]
  have hi : Real.exp x * (Real.exp x)⁻¹ = 1 := mul_inv_cancel₀ hE.ne'
  have hii : 0 < (Real.exp x)⁻¹ := inv_pos.2 hE
  calc x = x * Real.exp x * (Real.exp x)⁻¹ := by rw [mul_assoc, hi, mul_one]
    _ ≤ 4 * (1 + x) * Real.sinh x * (Real.exp x)⁻¹ := by gcongr
    _ = 4 * (1 + x) * (Real.exp x)⁻¹ * Real.sinh x := by ring

/-- **`gam y ≤ 4(1 + π|y|)e^{-π|y|}`.** -/
lemma gam_le (y : ℝ) : gam y ≤ 4 * (1 + Real.pi * |y|) * Real.exp (-(Real.pi * |y|)) := by
  have hp := Real.pi_pos
  have key : ∀ x : ℝ, 0 < x → gam x ≤ 4 * (1 + Real.pi * x) * Real.exp (-(Real.pi * x)) := by
    intro x hx
    rw [gam_of_ne hx.ne']; exact div_sinh_le (by positivity)
  rcases lt_trichotomy y 0 with h | h | h
  · rw [abs_of_neg h, ← gam_neg]; exact key _ (by linarith)
  · rw [h, gam_zero]; simp
  · rw [abs_of_pos h]; exact key _ h

/-- The kernel of `z²`. -/
noncomputable def kerM2 (ν ν' : ℝ) : ℝ := 1 / 2 * gam ((ν + ν') / 2) * gam ((ν - ν') / 2)

lemma kerM2_pos (ν ν' : ℝ) : 0 < kerM2 ν ν' := by
  have := gam_pos ((ν + ν') / 2); have := gam_pos ((ν - ν') / 2); unfold kerM2; positivity

lemma kerM2_symm (ν ν' : ℝ) : kerM2 ν ν' = kerM2 ν' ν := by
  unfold kerM2
  rw [add_comm ν ν', show (ν - ν') / 2 = -((ν' - ν) / 2) by ring, gam_neg]

lemma measurable_kerM2 : Measurable fun q : ℝ × ℝ => kerM2 q.1 q.2 := by
  unfold kerM2
  have h1 : Measurable fun q : ℝ × ℝ => (q.1 + q.2) / 2 := by fun_prop
  have h2 : Measurable fun q : ℝ × ℝ => (q.1 - q.2) / 2 := by fun_prop
  exact (measurable_const.mul (measurable_gam.comp h1)).mul (measurable_gam.comp h2)

/-- **`∫_0^∞ z K_{iν}K_{iν'} dz = kerM2 ν ν'`.** -/
theorem integral_z_besselKi_mul (ν ν' : ℝ) :
    ∫ z in Ioi 0, z * (besselKi ν z * besselKi ν' z) = kerM2 ν ν' := by
  have h := mellin_besselK_mul (s := 2) (a := ν * I) (b := ν' * I) (by simp)
  have e : ∫ z : ℝ in Ioi 0, (z : ℂ) ^ ((2 : ℂ) - 1) * (besselK (ν * I) z * besselK (ν' * I) z)
      = ((∫ z in Ioi 0, z * (besselKi ν z * besselKi ν' z) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi (fun z hz => ?_)
    rw [show (2 : ℂ) - 1 = 1 by norm_num, Complex.cpow_one, besselK_mul_I hz, besselK_mul_I hz]
    push_cast; ring
  rw [e] at h
  apply Complex.ofReal_injective
  rw [h]
  have g1 := Gamma_mul_eq_gam ((ν + ν') / 2)
  have g2 := Gamma_mul_eq_gam ((ν - ν') / 2)
  have eA : (2 + ↑ν * I + ↑ν' * I) / 2 = 1 + (((ν + ν') / 2 : ℝ) : ℂ) * I := by push_cast; ring
  have eB : (2 + ↑ν * I - ↑ν' * I) / 2 = 1 + (((ν - ν') / 2 : ℝ) : ℂ) * I := by push_cast; ring
  have eC : (2 - ↑ν * I + ↑ν' * I) / 2 = 1 - (((ν - ν') / 2 : ℝ) : ℂ) * I := by push_cast; ring
  have eD : (2 - ↑ν * I - ↑ν' * I) / 2 = 1 - (((ν + ν') / 2 : ℝ) : ℂ) * I := by push_cast; ring
  rw [eA, eB, eC, eD]
  have hprod : ∀ A B C D : ℂ, A * B * C * D = (A * D) * (B * C) := fun A B C D => by ring
  have hG2 : Complex.Gamma 2 = 1 := by
    rw [show (2 : ℂ) = 1 + 1 by norm_num, Complex.Gamma_add_one 1 one_ne_zero, Complex.Gamma_one]; ring
  rw [hprod, g1, g2, hG2, div_one]
  have h2pow : (2 : ℂ) ^ ((2 : ℂ) - 3) = ((1 / 2 : ℝ) : ℂ) := by
    rw [show (2 : ℂ) - 3 = -((1 : ℕ) : ℂ) by push_cast; ring, Complex.cpow_neg, Complex.cpow_natCast]
    push_cast; norm_num
  rw [h2pow, kerM2]
  push_cast; ring

lemma integrableOn_z_besselKi_mul (ν ν' : ℝ) :
    IntegrableOn (fun z => z * (besselKi ν z * besselKi ν' z)) (Ioi 0) := by
  by_contra h
  have e := integral_z_besselKi_mul ν ν'
  rw [integral_undef h] at e
  exact (kerM2_pos ν ν').ne' e.symm

/-- **`⟨ψ_a, z²ψ_b⟩_{dz/z} = ∬ conj a(ν) b(ν') M₂(ν, ν')`.** -/
theorem Zform_eq_kerM2 {a b : ℝ → ℂ} (ha : IsKTest a) (hb : IsKTest b) :
    Zform a b = ∫ p : ℝ × ℝ, (kerM2 p.1 p.2 : ℂ) * ((starRingEnd ℂ) (a p.1) * b p.2) := by
  set μz : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  set H : ℝ × (ℝ × ℝ) → ℂ := fun q =>
    ((q.1 * (besselKi q.2.1 q.1 * besselKi q.2.2 q.1) : ℝ) : ℂ) * ((starRingEnd ℂ) (a q.2.1) * b q.2.2)
  have hHm : Measurable H := by
    have m1 : Measurable fun q : ℝ × (ℝ × ℝ) => besselKi q.2.1 q.1 :=
      measurable_besselKi.comp ((measurable_fst.comp measurable_snd).prodMk measurable_fst)
    have m2 : Measurable fun q : ℝ × (ℝ × ℝ) => besselKi q.2.2 q.1 :=
      measurable_besselKi.comp ((measurable_snd.comp measurable_snd).prodMk measurable_fst)
    have m3 : Measurable fun q : ℝ × (ℝ × ℝ) => (starRingEnd ℂ) (a q.2.1) :=
      Complex.continuous_conj.measurable.comp (ha.continuous.measurable.comp (measurable_fst.comp measurable_snd))
    have m4 : Measurable fun q : ℝ × (ℝ × ℝ) => b q.2.2 :=
      hb.continuous.measurable.comp (measurable_snd.comp measurable_snd)
    exact (Complex.measurable_ofReal.comp (measurable_fst.mul (m1.mul m2))).mul (m3.mul m4)
  have hdom : Integrable (fun q : ℝ × (ℝ × ℝ) => (q.1 * (besselKi 0 q.1 * besselKi 0 q.1)) * (‖a q.2.1‖ * ‖b q.2.2‖))
      (μz.prod ((volume : Measure ℝ).prod volume)) :=
    (integrableOn_z_besselKi_mul 0 0).mul_prod (ha.integrable.norm.mul_prod hb.integrable.norm)
  have hHi : Integrable H (μz.prod ((volume : Measure ℝ).prod volume)) := by
    refine hdom.mono' hHm.aestronglyMeasurable ?_
    have hpos : ∀ᵐ q : ℝ × (ℝ × ℝ) ∂(μz.prod ((volume : Measure ℝ).prod (volume : Measure ℝ))), 0 < q.1 := by
      have := (ae_restrict_mem measurableSet_Ioi : ∀ᵐ z ∂μz, z ∈ Ioi (0 : ℝ))
      exact (Measure.quasiMeasurePreserving_fst (μ := μz) (ν := (volume : Measure ℝ).prod volume)).ae this
    filter_upwards [hpos] with q hq
    simp only [H, norm_mul, Complex.norm_real, Real.norm_eq_abs, RCLike.norm_conj]
    rw [abs_of_pos hq]
    have k1 := abs_besselKi_le_zero hq q.2.1
    have k2 := abs_besselKi_le_zero hq q.2.2
    have k0 := besselKi_zero_nonneg hq
    have ha0 := norm_nonneg (a q.2.1)
    have hb0 := norm_nonneg (b q.2.2)
    gcongr
  have hpt : ∀ z ∈ Ioi (0 : ℝ), (z : ℂ) * ((starRingEnd ℂ) (klInvA a z) * klInvA b z)
      = ∫ p : ℝ × ℝ, H (z, p) := by
    intro z _
    have hpm := integral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
      (fun ν => (starRingEnd ℂ) (a ν * (besselKi ν z : ℂ))) (fun ν' => b ν' * (besselKi ν' z : ℂ))
    have e : klInvA b z = ∫ ν', b ν' * (besselKi ν' z : ℂ) := rfl
    have hpm' : (∫ ν, (starRingEnd ℂ) (a ν * (besselKi ν z : ℂ))) * ∫ ν', b ν' * (besselKi ν' z : ℂ)
        = ∫ p : ℝ × ℝ, (starRingEnd ℂ) (a p.1 * (besselKi p.1 z : ℂ)) * (b p.2 * (besselKi p.2 z : ℂ)) := hpm.symm
    rw [show (starRingEnd ℂ) (klInvA a z) = ∫ ν, (starRingEnd ℂ) (a ν * (besselKi ν z : ℂ)) from integral_conj.symm,
      e, hpm', ← MeasureTheory.integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    simp only [H, map_mul, Complex.conj_ofReal]; push_cast; ring
  have hsw : ∫ z in Ioi (0 : ℝ), ∫ p : ℝ × ℝ, H (z, p) = ∫ p : ℝ × ℝ, ∫ z in Ioi (0 : ℝ), H (z, p) :=
    integral_integral_swap (f := fun z p => H (z, p)) hHi
  rw [Zform, setIntegral_congr_fun measurableSet_Ioi hpt, hsw]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only [H]
  rw [integral_mul_const, integral_complex_ofReal, integral_z_besselKi_mul]

/-! ### The `L²` extension of the KL transform -/

lemma memLp_muZ_test {f : ℝ → ℂ} (hf : IsKTest f) : MemLp f 2 muZ :=
  memLp_muZ_of hf.continuous.aestronglyMeasurable (integrableOn_test_sq_div hf)

lemma memLp_klT_test {f : ℝ → ℂ} (hf : IsKTest f) : MemLp (klT f) 2 wNu :=
  memLp_wNu_of (aestronglyMeasurable_klT hf.continuous.aestronglyMeasurable).restrict (integrableOn_klW_mul hf)

lemma memLp_klInvA_muZ {A : ℝ → ℂ} (hA : IsKTest A) : MemLp (klInvA (aW A)) 2 muZ :=
  memLp_muZ_of ((continuousOn_klInvA (isKTest_aW hA)).aestronglyMeasurable measurableSet_Ioi)
    (rev_parseval_amp (isKTest_aW hA)).1

lemma integrableOn_K0_test {g : ℝ → ℂ} (hg : IsKTest g) :
    IntegrableOn (fun z => besselKi 0 z * ‖g z / z‖) (Ioi 0) := by
  obtain ⟨c, hc, hcle⟩ := hg.exists_pos_le
  set M : ℝ := (1 / 2) * ∫ t, ‖kInt 0 c t‖
  have hi : IntegrableOn (fun z : ℝ => ‖g z / z‖) (Ioi 0) :=
    (hg.inv_mul.integrable.norm.integrableOn).congr_fun (fun z _ => by simp only [div_eq_inv_mul])
      measurableSet_Ioi
  refine (hi.const_mul M).mono' ?_ (Eventually.of_forall fun z => ?_)
  · exact (measurable_besselKi_zero.mul (hg.continuous.measurable.div Complex.measurable_ofReal).norm).aestronglyMeasurable
  · rw [norm_mul, norm_norm, Real.norm_eq_abs]
    by_cases h0 : g z = 0
    · simp [h0]
    · exact mul_le_mul_of_nonneg_right (abs_besselKi_le hc (hcle z h0)) (norm_nonneg _)

/-- Polarized Parseval between test functions. -/
lemma inner_klT_test {f g : ℝ → ℂ} (hf : IsKTest f) (hg : IsKTest g) :
    inner ℂ ((memLp_klT_test hf).toLp (klT f)) ((memLp_klT_test hg).toLp (klT g))
      = inner ℂ ((memLp_muZ_test hf).toLp f) ((memLp_muZ_test hg).toLp g) := by
  rw [inner_toLp_wNu, inner_toLp_muZ]
  exact kl_polar hf hg.continuous.aestronglyMeasurable (integrableOn_test_sq_div hg) (integrableOn_K0_test hg)
    (integrableOn_klW_mul hg)

/-- The adjoint identity between `L²(w)` and `L²(dz/z)` on test functions. -/
lemma inner_test_klT {A g : ℝ → ℂ} (hA : IsKTest A) (hg : IsKTest g) :
    inner ℂ ((memLp_wNu hA).toLp A) ((memLp_klT_test hg).toLp (klT g))
      = inner ℂ ((memLp_klInvA_muZ hA).toLp (klInvA (aW A))) ((memLp_muZ_test hg).toLp g) := by
  rw [inner_toLp_wNu, inner_toLp_muZ, ← integral_conj_aW_mul hA (klT g),
    ← integral_conj_klInvA_mul (isKTest_aW hA) hg.continuous.aestronglyMeasurable (integrableOn_K0_test hg)]
  refine setIntegral_congr_fun measurableSet_Ioi (fun z _ => ?_)
  ring

lemma muZ_lt_top {K : Set ℝ} (hK : IsCompact K) (hKs : K ⊆ Ioi 0) : muZ K < ⊤ := by
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (f := fun z : ℝ => z⁻¹)
    (continuousOn_inv₀.mono fun z hz => (ne_of_gt (hKs hz)))
  rw [muZ, withDensity_apply _ hKm, Measure.restrict_restrict hKm, inter_eq_left.2 hKs]
  calc ∫⁻ z in K, ENNReal.ofReal z⁻¹ ≤ ∫⁻ _ in K, ENNReal.ofReal M := by
        refine setLIntegral_mono' hKm (fun z hz => ENNReal.ofReal_le_ofReal ?_)
        exact (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans (hM z hz))
    _ = ENNReal.ofReal M * volume K := setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top

/-- A function in `L²(dz/z)` orthogonal to every test function vanishes a.e. -/
lemma ae_eq_zero_of_forall_test_Z {g : ℝ → ℂ} (hg : MemLp g 2 muZ)
    (h0 : ∀ h : ℝ → ℂ, IsKTest h → ∫ z, (starRingEnd ℂ) (h z) * g z ∂muZ = 0) : ∀ᵐ z ∂muZ, g z = 0 := by
  set f : ℝ → ℂ := fun z => (ENNReal.ofReal z⁻¹).toReal • g z
  have hloc : LocallyIntegrableOn f (Ioi 0) (volume : Measure ℝ) := by
    rw [locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed]
    intro K hKs hK
    have hKm : MeasurableSet K := hK.isClosed.measurableSet
    have hχ : MemLp (K.indicator fun _ => (1 : ℂ)) 2 muZ :=
      memLp_indicator_const 2 hKm.nullMeasurableSet 1 (Or.inr (muZ_lt_top hK hKs).ne)
    have hint := hχ.integrable_mul hg
    rw [muZ, integrable_withDensity_iff_integrable_smul' measurable_inv_dens
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)] at hint
    have hK' : IntegrableOn (fun z => (ENNReal.ofReal z⁻¹).toReal •
        ((K.indicator fun _ => (1 : ℂ)) z * g z)) K ((volume : Measure ℝ).restrict (Ioi 0)) := hint.integrableOn
    have e : ((volume : Measure ℝ).restrict (Ioi 0)).restrict K = (volume : Measure ℝ).restrict K := by
      rw [Measure.restrict_restrict hKm, inter_eq_left.2 hKs]
    have hK'' : IntegrableOn (fun z => (ENNReal.ofReal z⁻¹).toReal •
        ((K.indicator fun _ => (1 : ℂ)) z * g z)) K (volume : Measure ℝ) := by
      unfold IntegrableOn; rw [← e]; exact hK'
    refine hK''.congr_fun (fun z hz => ?_) hKm
    simp only [f, Set.indicator_of_mem hz, one_mul]
  have h1 := isOpen_Ioi.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc (fun r r_diff r_supp r_sub => by
    have hr : IsKTest fun z => (r z : ℂ) :=
      ⟨Complex.ofRealCLM.contDiff.comp r_diff, r_supp.comp_left Complex.ofReal_zero,
        (closure_mono (Function.support_comp_subset Complex.ofReal_zero r)).trans r_sub⟩
    have := h0 _ hr
    rw [muZ, integral_withDensity_eq_integral_toReal_smul measurable_inv_dens
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)] at this
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi (0 : ℝ)) (fun z hz => by
      rw [image_eq_zero_of_notMem_tsupport (fun h => hz (r_sub h)), zero_smul]), ← this]
    refine setIntegral_congr_fun measurableSet_Ioi (fun z _ => ?_)
    simp only [f, Complex.conj_ofReal, Complex.real_smul]; ring)
  have h2 : ∀ᵐ z ∂(volume : Measure ℝ).restrict (Ioi 0), g z = 0 := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards [h1] with z hz hz0
    have h3 := hz hz0
    have hz1 : (0 : ℝ) < z := hz0
    simp only [f, Complex.real_smul, mul_eq_zero, Complex.ofReal_eq_zero,
      ENNReal.toReal_ofReal (inv_nonneg.2 hz1.le), inv_eq_zero, hz1.ne', false_or] at h3
    exact h3
  exact (withDensity_absolutelyContinuous _ _).ae_le h2

/-- Test functions are dense in `L²(dz/z)`. -/
lemma exists_seq_test_tendsto_Z (G : Lp ℂ 2 muZ) :
    ∃ f : ℕ → ℝ → ℂ, ∃ hf : ∀ n, IsKTest (f n),
      Tendsto (fun n => (memLp_muZ_test (hf n)).toLp (f n)) atTop (𝓝 G) := by
  let K : Submodule ℂ (Lp ℂ 2 muZ) :=
    { carrier := {g | ∃ h : ℝ → ℂ, ∃ hh : IsKTest h, g = (memLp_muZ_test hh).toLp h}
      add_mem' := by
        rintro _ _ ⟨h1, hh1, rfl⟩ ⟨h2, hh2, rfl⟩
        exact ⟨h1 + h2, hh1.add hh2, by rw [MemLp.toLp_add]⟩
      zero_mem' := ⟨0, isKTest_zero, by rw [MemLp.toLp_zero]⟩
      smul_mem' := by
        rintro c _ ⟨h, hh, rfl⟩
        refine ⟨fun x => c * h x, hh.mul_smooth (φ := fun _ => c) contDiff_const, ?_⟩
        rw [← MemLp.toLp_const_smul]; rfl }
  have hdense : K.topologicalClosure = ⊤ := by
    rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
    intro G hG
    rw [Lp.eq_zero_iff_ae_eq_zero]
    refine ae_eq_zero_of_forall_test_Z (Lp.memLp G) (fun h hh => ?_)
    have h0 := (Submodule.mem_orthogonal _ _).1 hG _ (⟨h, hh, rfl⟩ : (memLp_muZ_test hh).toLp h ∈ K)
    rw [L2.inner_def] at h0
    rw [← h0]
    refine integral_congr_ae ?_
    filter_upwards [(memLp_muZ_test hh).coeFn_toLp] with z h1
    rw [h1, RCLike.inner_apply']
  have hG : G ∈ closure (K : Set (Lp ℂ 2 muZ)) := by
    rw [← Submodule.topologicalClosure_coe, hdense]; trivial
  obtain ⟨x, hx, hlim⟩ := mem_closure_iff_seq_limit.1 hG
  have hch : ∀ n, ∃ h : ℝ → ℂ, ∃ hh : IsKTest h, x n = (memLp_muZ_test hh).toLp h := fun n => hx n
  choose h hh he using hch
  exact ⟨h, hh, by simpa only [← he] using hlim⟩

/-- **The `L²` extension of `KL`.** For `η ∈ L²(dz/z)` there is `H ∈ L²(w)` with
`⟨KL f, H⟩ = ⟨f, η⟩` for test `f` and `⟨A, H⟩ = ⟨ψ_{wA}, η⟩` for test `A`. -/
theorem exists_klExt (η : Lp ℂ 2 muZ) :
    ∃ H : Lp ℂ 2 wNu,
      (∀ (f : ℝ → ℂ) (hf : IsKTest f), inner ℂ ((memLp_klT_test hf).toLp (klT f)) H
        = inner ℂ ((memLp_muZ_test hf).toLp f) η) ∧
      (∀ (A : ℝ → ℂ) (hA : IsKTest A), inner ℂ ((memLp_wNu hA).toLp A) H
        = inner ℂ ((memLp_klInvA_muZ hA).toLp (klInvA (aW A))) η) := by
  obtain ⟨f, hf, hlim⟩ := exists_seq_test_tendsto_Z η
  set x : ℕ → Lp ℂ 2 wNu := fun n => (memLp_klT_test (hf n)).toLp (klT (f n))
  set y : ℕ → Lp ℂ 2 muZ := fun n => (memLp_muZ_test (hf n)).toLp (f n)
  have hdist : ∀ n m, ‖x n - x m‖ = ‖y n - y m‖ := by
    intro n m
    refine inner_self_eq_ofReal ?_
    rw [inner_sub_sub_self, inner_sub_sub_self]
    simp only [x, y]
    rw [inner_klT_test (hf n) (hf n), inner_klT_test (hf n) (hf m), inner_klT_test (hf m) (hf n),
      inner_klT_test (hf m) (hf m)]
  have hxc : CauchySeq x := by
    have hy := hlim.cauchySeq
    rw [Metric.cauchySeq_iff] at hy ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hy ε hε
    exact ⟨N, fun m hm n hn => by
      rw [dist_eq_norm, hdist, ← dist_eq_norm]; exact hN m hm n hn⟩
  obtain ⟨H, hH⟩ := cauchySeq_tendsto_of_complete hxc
  refine ⟨H, fun g hg => ?_, fun A hA => ?_⟩
  · have l1 := (tendsto_const_nhds (x := (memLp_klT_test hg).toLp (klT g))).inner (𝕜 := ℂ) hH
    have l2 := (tendsto_const_nhds (x := (memLp_muZ_test hg).toLp g)).inner (𝕜 := ℂ) hlim
    refine tendsto_nhds_unique l1 (l2.congr fun n => ?_)
    exact (inner_klT_test hg (hf n)).symm
  · have l1 := (tendsto_const_nhds (x := (memLp_wNu hA).toLp A)).inner (𝕜 := ℂ) hH
    have l2 := (tendsto_const_nhds (x := (memLp_klInvA_muZ hA).toLp (klInvA (aW A)))).inner (𝕜 := ℂ) hlim
    refine tendsto_nhds_unique l1 (l2.congr fun n => ?_)
    exact (inner_test_klT hA (hf n)).symm

end Qschubert
