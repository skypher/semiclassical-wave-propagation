import Qschubert.KLFCY4

/-!
# Lemma FC, case `Z = Y`: Duhamel on exponential curves

`SS A B = ⟨A, HY B⟩ = S(wA, wB)`. The commutator form `C(A, B) = S(ΛA, B) - S(A, ΛB)` has the kernel
`-2 M₂/(Λ + Λ')` (`CC_eq`), and `S(e^{aΛ}A, e^{-aΛ}B) - S(A, B)` has the kernel
`R_a = -2 M₂ φ_a(Λ - Λ')/(Λ + Λ')`, `φ_a(δ) = ∫_0^a e^{sδ} ds` (`duhamel_SS`). No principal value occurs.
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set
open scoped ENNReal

variable {A B : ℝ → ℂ}

/-- The form on test functions. -/
noncomputable def SS (A B : ℝ → ℂ) : ℂ := inner ℂ (TL A) (HY B)

/-- The commutator form. -/
noncomputable def CC (A B : ℝ → ℂ) : ℂ := SS (mL A) B - SS A (mL B)

lemma mL_eL (c : ℝ) (A : ℝ → ℂ) : mL (eL c A) = eL c (mL A) := by funext ν; simp only [mL, eL]; ring

lemma eL_zero (A : ℝ → ℂ) : eL 0 A = A := by funext ν; simp [eL]

lemma eL_eL (c d : ℝ) (A : ℝ → ℂ) : eL c (eL d A) = eL (c + d) A := by
  funext ν; simp only [eL]; rw [add_mul, Real.exp_add]; push_cast; ring

lemma norm_SS_le (hB : IsKTest B) : ‖SS A B‖ ≤ ‖TL A‖ * (5 / 2 * ‖TL (eL 1 B)‖) :=
  (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (norm_HY_le hB) (norm_nonneg _))

lemma inner_real_smul_left {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedSpace ℝ E]
    [IsScalarTower ℝ ℂ E] (r : ℝ) (x y : E) : inner ℂ (r • x) y = (r : ℂ) * inner ℂ x y := by
  have e : r • x = (r : ℂ) • x := (algebraMap_smul ℂ r x).symm
  rw [e, inner_smul_left, Complex.conj_ofReal]

lemma inner_real_smul_right {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedSpace ℝ E]
    [IsScalarTower ℝ ℂ E] (r : ℝ) (x y : E) : inner ℂ x (r • y) = (r : ℂ) * inner ℂ x y := by
  have e : r • y = (r : ℂ) • y := (algebraMap_smul ℂ r y).symm
  rw [e, inner_smul_right]

lemma hasDerivAt_TL (σ : ℝ) (hA : IsKTest A) (s : ℝ) :
    HasDerivAt (fun s => TL (eL (σ * s) A)) (σ • TL (mL (eL (σ * s) A))) s :=
  curve_deriv (L := TL) (κ := 1) zero_le_one (fun h₁ h₂ c₁ c₂ => TL_lin h₁ h₂ c₁ c₂)
    (fun hB => by rw [one_mul]; exact norm_TL_le_eL hB) σ hA s

lemma hasDerivAt_HY (σ : ℝ) (hB : IsKTest B) (s : ℝ) :
    HasDerivAt (fun s => HY (eL (σ * s) B)) (σ • HY (mL (eL (σ * s) B))) s :=
  curve_deriv (L := HY) (κ := 5 / 2) (by norm_num) (fun h₁ h₂ c₁ c₂ => HY_lin h₁ h₂ c₁ c₂)
    (fun hB => norm_HY_le hB) σ hB s

/-- The derivative of `S` along two exponential curves. -/
theorem hasDerivAt_SS (σ₁ σ₂ : ℝ) (hA : IsKTest A) (hB : IsKTest B) (s : ℝ) :
    HasDerivAt (fun s => SS (eL (σ₁ * s) A) (eL (σ₂ * s) B))
      ((σ₂ : ℂ) * SS (eL (σ₁ * s) A) (mL (eL (σ₂ * s) B)) + (σ₁ : ℂ) * SS (mL (eL (σ₁ * s) A)) (eL (σ₂ * s) B)) s := by
  have h := (hasDerivAt_TL σ₁ hA s).inner ℂ (hasDerivAt_HY σ₂ hB s)
  rw [inner_real_smul_right, inner_real_smul_left] at h
  exact h

/-- `Λ² = ν² + ¼`. -/
lemma mL_mL (A : ℝ → ℂ) : mL (mL A) = fun ν => (1 : ℂ) * n2 A ν + (1 / 4 : ℂ) * A ν := by
  funext ν
  have h : (LamK ν : ℂ) * (LamK ν : ℂ) = (ν : ℂ) ^ 2 + 1 / 4 := by
    have h0 : LamK ν * LamK ν = ν ^ 2 + 1 / 4 := Real.mul_self_sqrt (by positivity)
    rw [← Complex.ofReal_mul, h0]; push_cast; ring
  simp only [mL, n2]
  linear_combination (A ν) * h

lemma aW_n2 (A : ℝ → ℂ) : aW (n2 A) = n2 (aW A) := by funext ν; simp only [aW, n2]; ring

/-- **The Sylvester identity for `SS`.** -/
theorem SS_sylvester (hA : IsKTest A) (hB : IsKTest B) :
    SS (mL (mL A)) B - SS A (mL (mL B)) = -2 * Zform (aW A) (aW B) := by
  unfold SS
  rw [mL_mL, mL_mL, TL_lin hA.n2 hA, HY_lin hB.n2 hB, inner_add_left, inner_add_right, inner_smul_left, inner_smul_left,
    inner_smul_right, inner_smul_right, HY_spec hA.n2 hB, HY_spec hA hB, HY_spec hA hB.n2, aW_n2, aW_n2]
  have h := Sform_sylvester (isKTest_aW hA) (isKTest_aW hB)
  simp only [map_one, map_div₀, map_ofNat]
  linear_combination h

/-! ### The kernel of the commutator -/

/-- The density `M₂ conj(wA) wB`. -/
noncomputable def Tk (A B : ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  (kerM2 p.1 p.2 : ℂ) * ((starRingEnd ℂ) (aW A p.1) * aW B p.2)

lemma gam_le_four (y : ℝ) : gam y ≤ 4 := by
  have h := gam_le y
  have hx : 0 ≤ Real.pi * |y| := by have := Real.pi_pos; positivity
  have h1 : (1 + Real.pi * |y|) * Real.exp (-(Real.pi * |y|)) ≤ 1 := by
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
    linarith [Real.add_one_le_exp (Real.pi * |y|)]
  nlinarith

lemma kerM2_le (ν ν' : ℝ) : kerM2 ν ν' ≤ 8 := by
  unfold kerM2
  have h1 := gam_le_four ((ν + ν') / 2)
  have h2 := gam_le_four ((ν - ν') / 2)
  have p1 := gam_pos ((ν + ν') / 2)
  have p2 := gam_pos ((ν - ν') / 2)
  nlinarith

lemma measurable_Tk (hA : IsKTest A) (hB : IsKTest B) : Measurable (Tk A B) := by
  have ha := (isKTest_aW hA).continuous
  have hb := (isKTest_aW hB).continuous
  unfold Tk
  exact (Complex.measurable_ofReal.comp measurable_kerM2).mul
    (((Complex.continuous_conj.comp (ha.comp continuous_fst)).mul (hb.comp continuous_snd)).measurable)

lemma norm_Tk_le (p : ℝ × ℝ) : ‖Tk A B p‖ ≤ 8 * (‖aW A p.1‖ * ‖aW B p.2‖) := by
  unfold Tk
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (kerM2_pos _ _), RCLike.norm_conj]
  exact mul_le_mul_of_nonneg_right (kerM2_le _ _) (by positivity)

lemma integrable_Tk (hA : IsKTest A) (hB : IsKTest B) : Integrable (Tk A B) ((volume : Measure ℝ).prod volume) :=
  (((isKTest_aW hA).integrable.norm.mul_prod (isKTest_aW hB).integrable.norm).const_mul 8).mono'
    (measurable_Tk hA hB).aestronglyMeasurable (Eventually.of_forall norm_Tk_le)

lemma aW_eL (c : ℝ) (A : ℝ → ℂ) (ν : ℝ) : aW (eL c A) ν = ((Real.exp (c * LamK ν) : ℝ) : ℂ) * aW A ν := by
  simp only [aW, eL]; ring

lemma Tk_eL (c₁ c₂ : ℝ) (A B : ℝ → ℂ) (p : ℝ × ℝ) :
    Tk (eL c₁ A) (eL c₂ B) p = ((Real.exp (c₁ * LamK p.1 + c₂ * LamK p.2) : ℝ) : ℂ) * Tk A B p := by
  simp only [Tk, aW_eL, map_mul, Complex.conj_ofReal]
  rw [Real.exp_add]; push_cast; ring

lemma Zform_eq_Tk (hA : IsKTest A) (hB : IsKTest B) : Zform (aW A) (aW B) = ∫ p : ℝ × ℝ, Tk A B p :=
  Zform_eq_kerM2 (isKTest_aW hA) (isKTest_aW hB)

lemma one_le_lam_sum (p : ℝ × ℝ) : 1 ≤ LamK p.1 + LamK p.2 := by
  have := half_le_LamK p.1; have := half_le_LamK p.2; linarith

lemma norm_TL_eL_neg {X : ℝ → ℂ} (hX : IsKTest X) {t : ℝ} (ht : 0 ≤ t) :
    ‖TL (eL (-1 * t) X)‖ ≤ Real.exp (-(t / 2)) * ‖TL X‖ := by
  refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
  filter_upwards [coe_TL (hX.eL (-1 * t)), coe_TL hX] with ν h1 h2
  rw [h1, h2, eL, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (norm_nonneg _)
  nlinarith [half_le_LamK ν]

lemma eL_comm (c d : ℝ) (X : ℝ → ℂ) : eL c (eL d X) = eL d (eL c X) := by
  rw [eL_eL, eL_eL, add_comm]

/-- **The commutator form**: `C(A, B) = -2 ∬ (Λ + Λ')⁻¹ M₂ conj(wA) wB`. -/
theorem CC_eq (hA : IsKTest A) (hB : IsKTest B) :
    CC A B = -2 * ∫ p : ℝ × ℝ, (((LamK p.1 + LamK p.2)⁻¹ : ℝ) : ℂ) * Tk A B p := by
  set g : ℝ → ℂ := fun t => SS (eL (-1 * t) (mL A)) (eL (-1 * t) B) - SS (eL (-1 * t) A) (eL (-1 * t) (mL B))
  set E : ℝ × (ℝ × ℝ) → ℂ := fun q => ((Real.exp (-1 * q.1 * LamK q.2.1 + -1 * q.1 * LamK q.2.2) : ℝ) : ℂ) * Tk A B q.2
  have hg0 : g 0 = CC A B := by
    simp only [g, CC, mul_zero, eL_zero]
  have hd : ∀ t : ℝ, HasDerivAt g (2 * ∫ p : ℝ × ℝ, E (t, p)) t := by
    intro t
    have d1 := hasDerivAt_SS (-1) (-1) hA.mL hB t
    have d2 := hasDerivAt_SS (-1) (-1) hA hB.mL t
    refine (d1.sub d2).congr_deriv ?_
    set X := eL (-1 * t) A
    set Y := eL (-1 * t) B
    have hX : IsKTest X := hA.eL _
    have hY : IsKTest Y := hB.eL _
    have s1 : eL (-1 * t) (mL A) = mL X := (mL_eL _ _).symm
    have s2 : eL (-1 * t) (mL B) = mL Y := (mL_eL _ _).symm
    rw [s1, s2]
    have hs := SS_sylvester hX hY
    have hZ : Zform (aW X) (aW Y) = ∫ p : ℝ × ℝ, E (t, p) := by
      rw [Zform_eq_Tk hX hY]
      refine integral_congr_ae (Eventually.of_forall fun p => ?_)
      simp only [X, Y, E]
      rw [Tk_eL]
    rw [← hZ]
    push_cast
    linear_combination (-1 : ℂ) * hs
  have hTi := integrable_Tk hA hB
  have hEi : Integrable E ((volume.restrict (Ioi (0 : ℝ))).prod ((volume : Measure ℝ).prod volume)) := by
    have hexp : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Ioi 0) := integrableOn_exp_neg_Ioi 0 
    refine (hexp.mul_prod hTi.norm).mono' ?_ ?_
    · refine (((Complex.continuous_ofReal.comp (by
        exact Real.continuous_exp.comp (((continuous_const.mul continuous_fst).mul
          (continuous_LamK.comp (continuous_fst.comp continuous_snd))).add
          ((continuous_const.mul continuous_fst).mul (continuous_LamK.comp (continuous_snd.comp continuous_snd))))))
          ).aestronglyMeasurable).mul ?_
      exact (measurable_Tk hA hB).comp measurable_snd |>.aestronglyMeasurable
    · have hpos : ∀ᵐ q : ℝ × (ℝ × ℝ) ∂((volume.restrict (Ioi (0 : ℝ))).prod ((volume : Measure ℝ).prod (volume : Measure ℝ))), 0 < q.1 := by
        have h0 := (ae_restrict_mem measurableSet_Ioi : ∀ᵐ z ∂(volume.restrict (Ioi (0 : ℝ))), z ∈ Ioi (0 : ℝ))
        exact (Measure.quasiMeasurePreserving_fst (μ := volume.restrict (Ioi (0 : ℝ)))
          (ν := (volume : Measure ℝ).prod volume)).ae h0
      filter_upwards [hpos] with q hq
      simp only [E]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (norm_nonneg _)
      nlinarith [one_le_lam_sum q.2]
  have hg'i : IntegrableOn (fun t => 2 * ∫ p : ℝ × ℝ, E (t, p)) (Ioi 0) :=
    (hEi.integral_prod_left).const_mul 2
  have hlim : Tendsto g atTop (𝓝 0) := by
    set c : ℝ := ‖TL (mL A)‖ * (5 / 2 * ‖TL (eL 1 B)‖) + ‖TL A‖ * (5 / 2 * ‖TL (eL 1 (mL B))‖)
    have h1 : Tendsto (fun t : ℝ => Real.exp (-(t / 2)) * c) atTop (𝓝 0) := by
      have h2 : Tendsto (fun t : ℝ => -(t / 2)) atTop atBot :=
        tendsto_neg_atTop_atBot.comp (tendsto_id.atTop_div_const (by norm_num))
      simpa using (Real.tendsto_exp_atBot.comp h2).mul_const c
    refine squeeze_zero_norm' ?_ h1
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    have hE1 : Real.exp (-(t / 2)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have hE0 := Real.exp_pos (-(t / 2))
    have b1 : ‖SS (eL (-1 * t) (mL A)) (eL (-1 * t) B)‖ ≤ Real.exp (-(t / 2)) * (‖TL (mL A)‖ * (5 / 2 * ‖TL (eL 1 B)‖)) := by
      refine (norm_SS_le (hB.eL _)).trans ?_
      rw [eL_comm]
      have h3 := norm_TL_eL_neg hA.mL ht
      have h4 := norm_TL_eL_neg (hB.eL 1) ht
      have n1 := norm_nonneg (TL (mL A))
      have n2 := norm_nonneg (TL (eL 1 B))
      calc _ ≤ (Real.exp (-(t / 2)) * ‖TL (mL A)‖) * (5 / 2 * (Real.exp (-(t / 2)) * ‖TL (eL 1 B)‖)) := by gcongr
        _ ≤ (Real.exp (-(t / 2)) * ‖TL (mL A)‖) * (5 / 2 * (1 * ‖TL (eL 1 B)‖)) := by gcongr
        _ = _ := by ring
    have b2 : ‖SS (eL (-1 * t) A) (eL (-1 * t) (mL B))‖ ≤ Real.exp (-(t / 2)) * (‖TL A‖ * (5 / 2 * ‖TL (eL 1 (mL B))‖)) := by
      refine (norm_SS_le (hB.mL.eL _)).trans ?_
      rw [eL_comm]
      have h3 := norm_TL_eL_neg hA ht
      have h4 := norm_TL_eL_neg (hB.mL.eL 1) ht
      have n1 := norm_nonneg (TL A)
      have n2 := norm_nonneg (TL (eL 1 (mL B)))
      calc _ ≤ (Real.exp (-(t / 2)) * ‖TL A‖) * (5 / 2 * (Real.exp (-(t / 2)) * ‖TL (eL 1 (mL B))‖)) := by gcongr
        _ ≤ (Real.exp (-(t / 2)) * ‖TL A‖) * (5 / 2 * (1 * ‖TL (eL 1 (mL B))‖)) := by gcongr
        _ = _ := by ring
    calc ‖g t‖ ≤ _ := norm_sub_le _ _
      _ ≤ _ := add_le_add b1 b2
      _ = _ := by simp only [c]; ring
  have hF := integral_Ioi_of_hasDerivAt_of_tendsto' (fun t _ => hd t) hg'i hlim
  have hval : ∫ t in Ioi (0 : ℝ), ∫ p : ℝ × ℝ, E (t, p) = ∫ p : ℝ × ℝ, (((LamK p.1 + LamK p.2)⁻¹ : ℝ) : ℂ) * Tk A B p := by
    have hsw : ∫ t in Ioi (0 : ℝ), ∫ p : ℝ × ℝ, E (t, p) = ∫ p : ℝ × ℝ, ∫ t in Ioi (0 : ℝ), E (t, p) :=
      integral_integral_swap (f := fun t p => E (t, p)) hEi
    rw [hsw]
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    simp only [E]
    rw [integral_mul_const, integral_complex_ofReal]
    have hσ : 0 < LamK p.1 + LamK p.2 := by linarith [one_le_lam_sum p]
    have h := Real.integral_rpow_mul_exp_neg_mul_Ioi one_pos hσ
    simp only [sub_self, Real.rpow_zero, one_mul, Real.Gamma_one, mul_one, Real.rpow_one] at h
    have e : ∫ t in Ioi (0 : ℝ), Real.exp (-1 * t * LamK p.1 + -1 * t * LamK p.2)
        = ∫ t in Ioi (0 : ℝ), Real.exp (-((LamK p.1 + LamK p.2) * t)) :=
      setIntegral_congr_fun measurableSet_Ioi (fun t _ => by congr 1; ring)
    rw [e, h, one_div]
  rw [MeasureTheory.integral_const_mul, hval, hg0, zero_sub] at hF
  linear_combination hF

/-- `φ_a(δ) = ∫_0^a e^{sδ} ds`. -/
noncomputable def phiA (a δ : ℝ) : ℝ := ∫ s in (0 : ℝ)..a, Real.exp (s * δ)

/-- The Duhamel integrand. -/
noncomputable def GG (A B : ℝ → ℂ) (q : ℝ × (ℝ × ℝ)) : ℂ :=
  (((LamK q.2.1 + LamK q.2.2)⁻¹ * Real.exp (q.1 * (LamK q.2.1 - LamK q.2.2)) : ℝ) : ℂ) * Tk A B q.2

lemma integrable_GG (hA : IsKTest A) (hB : IsKTest B) (a : ℝ) :
    Integrable (GG A B) ((volume.restrict (Ioc (0 : ℝ) a)).prod ((volume : Measure ℝ).prod volume)) := by
  have hTi := integrable_Tk hA hB
  obtain ⟨M, hM⟩ := (isKTest_aW hA).compact.exists_bound_of_continuousOn continuous_LamK.continuousOn
  have hM' : ∀ ν, aW A ν ≠ 0 → LamK ν ≤ M := fun ν hν =>
    (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans (hM ν (subset_tsupport _ hν)))
  have hc : IntegrableOn (fun _ : ℝ => Real.exp (a * |M|)) (Ioc 0 a) := integrableOn_const (by simp)
  refine (hc.mul_prod hTi.norm).mono' ?_ ?_
  · refine (((Complex.continuous_ofReal.comp ?_).aestronglyMeasurable)).mul
      ((measurable_Tk hA hB).comp measurable_snd |>.aestronglyMeasurable)
    refine Continuous.mul ?_ ?_
    · exact ((continuous_LamK.comp (continuous_fst.comp continuous_snd)).add
        (continuous_LamK.comp (continuous_snd.comp continuous_snd))).inv₀
        (fun q => by
          show LamK q.2.1 + LamK q.2.2 ≠ 0
          have := one_le_lam_sum q.2
          exact ne_of_gt (by linarith))
    · exact Real.continuous_exp.comp (continuous_fst.mul ((continuous_LamK.comp (continuous_fst.comp continuous_snd)).sub
        (continuous_LamK.comp (continuous_snd.comp continuous_snd))))
  · have hs : ∀ᵐ q : ℝ × (ℝ × ℝ) ∂((volume.restrict (Ioc (0 : ℝ) a)).prod ((volume : Measure ℝ).prod (volume : Measure ℝ))), q.1 ∈ Ioc (0 : ℝ) a := by
      have h0 := (ae_restrict_mem measurableSet_Ioc : ∀ᵐ z ∂(volume.restrict (Ioc (0 : ℝ) a)), z ∈ Ioc (0 : ℝ) a)
      exact (Measure.quasiMeasurePreserving_fst (μ := volume.restrict (Ioc (0 : ℝ) a))
        (ν := (volume : Measure ℝ).prod volume)).ae h0
    filter_upwards [hs] with q hq
    simp only [GG]
    by_cases hc0 : aW A q.2.1 = 0
    · have : Tk A B q.2 = 0 := by simp [Tk, hc0]
      rw [this]; simp
    · have hσ := one_le_lam_sum q.2
      have hinv : (LamK q.2.1 + LamK q.2.2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hσ
      have hinv0 : 0 < (LamK q.2.1 + LamK q.2.2)⁻¹ := inv_pos.2 (by linarith)
      have hE : Real.exp (q.1 * (LamK q.2.1 - LamK q.2.2)) ≤ Real.exp (a * |M|) := by
        refine Real.exp_le_exp.2 ?_
        have h1 := hM' _ hc0
        have h2 := LamK_pos q.2.2
        have h3 := LamK_pos q.2.1
        have h4 : LamK q.2.1 - LamK q.2.2 ≤ |M| := by linarith [le_abs_self M]
        have h5 : 0 ≤ |M| := abs_nonneg M
        calc q.1 * (LamK q.2.1 - LamK q.2.2) ≤ q.1 * |M| := mul_le_mul_of_nonneg_left h4 hq.1.le
          _ ≤ a * |M| := mul_le_mul_of_nonneg_right hq.2 h5
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (mul_pos hinv0 (Real.exp_pos _))]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      calc (LamK q.2.1 + LamK q.2.2)⁻¹ * Real.exp (q.1 * (LamK q.2.1 - LamK q.2.2))
          ≤ 1 * Real.exp (a * |M|) := by gcongr
        _ = _ := one_mul _

lemma integral_GG_slice {a : ℝ} (ha : 0 ≤ a) (p : ℝ × ℝ) :
    ∫ s in Ioc (0 : ℝ) a, GG A B (s, p)
      = (((LamK p.1 + LamK p.2)⁻¹ * phiA a (LamK p.1 - LamK p.2) : ℝ) : ℂ) * Tk A B p := by
  simp only [GG]
  rw [integral_mul_const, integral_complex_ofReal, MeasureTheory.integral_const_mul]
  congr 3
  rw [phiA, intervalIntegral.integral_of_le ha]

/-- **Duhamel**: `S(e^{aΛ}A, e^{-aΛ}B) - S(A, B) = -2 ∬ (Λ + Λ')⁻¹ φ_a(Λ - Λ') M₂ conj(wA) wB`. -/
theorem duhamel_SS (hA : IsKTest A) (hB : IsKTest B) {a : ℝ} (ha : 0 ≤ a) :
    SS (eL a A) (eL (-a) B) - SS A B
      = -2 * ∫ p : ℝ × ℝ, (((LamK p.1 + LamK p.2)⁻¹ * phiA a (LamK p.1 - LamK p.2) : ℝ) : ℂ) * Tk A B p := by
  set h : ℝ → ℂ := fun s => SS (eL (1 * s) A) (eL (-1 * s) B)
  set G : ℝ × (ℝ × ℝ) → ℂ := GG A B
  have hd : ∀ s : ℝ, HasDerivAt h (-2 * ∫ p : ℝ × ℝ, G (s, p)) s := by
    intro s
    refine (hasDerivAt_SS 1 (-1) hA hB s).congr_deriv ?_
    set X := eL (1 * s) A
    set Y := eL (-1 * s) B
    have hC := CC_eq (hA.eL (1 * s)) (hB.eL (-1 * s))
    have e : ∫ p : ℝ × ℝ, (((LamK p.1 + LamK p.2)⁻¹ : ℝ) : ℂ) * Tk X Y p = ∫ p : ℝ × ℝ, G (s, p) := by
      refine integral_congr_ae (Eventually.of_forall fun p => ?_)
      simp only [X, Y, G, GG]
      rw [Tk_eL, show 1 * s * LamK p.1 + -1 * s * LamK p.2 = s * (LamK p.1 - LamK p.2) by ring]
      push_cast; ring
    rw [← e, ← hC, CC]
    push_cast; ring
  have hGi : Integrable G ((volume.restrict (Ioc (0 : ℝ) a)).prod ((volume : Measure ℝ).prod volume)) := integrable_GG hA hB a
  have hii : IntervalIntegrable (fun s => -2 * ∫ p : ℝ × ℝ, G (s, p)) volume 0 a := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ha]
    exact (hGi.integral_prod_left).const_mul (-2)
  have hF := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s) hii
  have h0 : h 0 = SS A B := by simp only [h, mul_zero, eL_zero]
  have ha' : h a = SS (eL a A) (eL (-a) B) := by simp only [h, one_mul, neg_mul]
  have hval : ∫ s in Ioc (0 : ℝ) a, ∫ p : ℝ × ℝ, G (s, p)
      = ∫ p : ℝ × ℝ, (((LamK p.1 + LamK p.2)⁻¹ * phiA a (LamK p.1 - LamK p.2) : ℝ) : ℂ) * Tk A B p := by
    have hsw : ∫ s in Ioc (0 : ℝ) a, ∫ p : ℝ × ℝ, G (s, p) = ∫ p : ℝ × ℝ, ∫ s in Ioc (0 : ℝ) a, G (s, p) :=
      integral_integral_swap (f := fun s p => G (s, p)) hGi
    rw [hsw]
    exact integral_congr_ae (Eventually.of_forall fun p => integral_GG_slice ha p)
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le ha, hval, ha', h0] at hF
  exact hF.symm

end Qschubert
