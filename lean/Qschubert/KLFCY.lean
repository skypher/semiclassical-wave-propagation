import Qschubert.KLFCX

/-!
# Lemma FC, case `Z = Y`: the form `S(a, b) = ⟨ψ_a, z∂_z ψ_b⟩`

Part 1 (the `t`-representation). With `ψ_a(z) = ½∫e^{-z cosh t}â(t)dt`:
* `klInvD a z = z∂_z ψ_a(z) = -½∫ z cosh t e^{-z cosh t} â(t) dt` (`hasDerivAt_klInvA`);
* `Sform a b = ∫_0^∞ conj ψ_a · (z∂_z ψ_b) dz/z = -¼ ∬ conj â(t) b̂(u) Q(t,u)`, `Q = cosh u/(cosh t + cosh u)`
  (`Sform_eq`), an absolutely convergent double integral (`0 ≤ Q ≤ 1`);
* `Zform a b = ∫_0^∞ conj ψ_a ψ_b z dz = ¼ ∬ conj â b̂/(cosh t + cosh u)²` (`Zform_eq`);
* **Sylvester identity** `S(ν²a, b) - S(a, ν²b) = -2 Z(a, b)` (`Sform_sylvester`), from two integrations by
  parts in `t` and in `u` and `(∂_u² - ∂_t²) Q = 2/(cosh t + cosh u)²`.

No principal value occurs: the form is evaluated on the `t`-side.
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set
open scoped ENNReal

section tz

variable {a b : ℝ → ℂ}

/-- The integrand on `(0, ∞) × ℝ²`. -/
noncomputable def tzG (a b : ℝ → ℂ) (s : ℝ) (W : ℝ × ℝ → ℝ) (q : ℝ × (ℝ × ℝ)) : ℂ :=
  ((q.1 ^ (s - 1) * W q.2 * Real.exp (-(q.1 * coshSum q.2)) : ℝ) : ℂ)
    * ((starRingEnd ℂ) (hatA a q.2.1) * hatA b q.2.2)

lemma integral_rpow_exp_cosh {s : ℝ} (hs : 0 < s) (p : ℝ × ℝ) :
    ∫ z in Ioi (0 : ℝ), z ^ (s - 1) * Real.exp (-(z * coshSum p)) = Real.Gamma s * coshSum p ^ (-s) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi hs (coshSum_pos p)
  have e : ∫ z in Ioi (0 : ℝ), z ^ (s - 1) * Real.exp (-(z * coshSum p))
      = ∫ t in Ioi (0 : ℝ), t ^ (s - 1) * Real.exp (-(coshSum p * t)) :=
    setIntegral_congr_fun measurableSet_Ioi (fun z _ => by rw [mul_comm z])
  rw [e, h, one_div, Real.inv_rpow (coshSum_pos p).le, ← Real.rpow_neg (coshSum_pos p).le]; ring

lemma continuous_coshSum : Continuous coshSum := by unfold coshSum; fun_prop

variable (ha : IsKTest a) (hb : IsKTest b) {s : ℝ} (hs : 0 < s) {W : ℝ × ℝ → ℝ} (hWc : Continuous W)
  (hW0 : ∀ p, 0 ≤ W p) (hWle : ∀ p, W p ≤ coshSum p ^ s)
include ha hb hs hWc hW0 hWle

lemma measurable_tzG : Measurable (tzG a b s W) := by
  have hcA := continuous_hatA ha
  have hcB := continuous_hatA hb
  unfold tzG
  refine (Complex.measurable_ofReal.comp ?_).mul ?_
  · exact ((measurable_fst.pow_const _).mul (hWc.measurable.comp measurable_snd)).mul
      (Real.measurable_exp.comp ((measurable_fst.mul (continuous_coshSum.measurable.comp measurable_snd)).neg))
  · exact ((Complex.continuous_conj.comp (hcA.comp continuous_fst)).measurable.comp measurable_snd).mul
      ((hcB.comp continuous_snd).measurable.comp measurable_snd)

lemma integrable_tzG : Integrable (tzG a b s W) ((volume.restrict (Ioi 0)).prod volume) := by
  have hm := measurable_tzG ha hb hs hWc hW0 hWle
  have hnorm : ∀ (z : ℝ) (p : ℝ × ℝ), 0 < z → ‖tzG a b s W (z, p)‖
      = z ^ (s - 1) * Real.exp (-(z * coshSum p)) * (W p * (‖hatA a p.1‖ * ‖hatA b p.2‖)) := by
    intro z p hz
    unfold tzG
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (mul_nonneg (Real.rpow_nonneg hz.le _) (hW0 p)) (Real.exp_pos _).le), RCLike.norm_conj]
    ring
  rw [integrable_prod_iff' hm.aestronglyMeasurable]
  have hI : ∀ p : ℝ × ℝ, IntegrableOn (fun z : ℝ => z ^ (s - 1) * Real.exp (-(z * coshSum p))) (Ioi 0) := by
    intro p
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := s - 1) (b := coshSum p)
      (by linarith) one_pos (coshSum_pos p)
    refine h.congr_fun (fun z _ => ?_) measurableSet_Ioi
    simp only [Real.rpow_one]; ring_nf
  refine ⟨Eventually.of_forall fun p => ?_, ?_⟩
  · refine ((hI p).mul_const (W p * (‖hatA a p.1‖ * ‖hatA b p.2‖))).mono'
      (hm.comp measurable_prodMk_right).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    exact (hnorm z p hz).le
  · have hval : ∀ p : ℝ × ℝ, ∫ z in Ioi 0, ‖tzG a b s W (z, p)‖
        = Real.Gamma s * coshSum p ^ (-s) * (W p * (‖hatA a p.1‖ * ‖hatA b p.2‖)) := by
      intro p
      rw [setIntegral_congr_fun measurableSet_Ioi (fun z hz => hnorm z p hz), integral_mul_const,
        integral_rpow_exp_cosh hs p]
    simp_rw [hval]
    have hA := integrable_hatA ha
    have hB := integrable_hatA hb
    have hcA := continuous_hatA ha
    have hcB := continuous_hatA hb
    refine ((hA.norm.mul_prod hB.norm).const_mul (Real.Gamma s)).mono' ?_ (Eventually.of_forall fun p => ?_)
    · exact (((continuous_coshSum.rpow_const (fun p => Or.inl (coshSum_pos p).ne')).const_smul (Real.Gamma s)).mul
        (hWc.mul ((hcA.comp continuous_fst).norm.mul (hcB.comp continuous_snd).norm))).aestronglyMeasurable
    · have hG := Real.Gamma_pos_of_pos hs
      have hσ := coshSum_pos p
      have hle : coshSum p ^ (-s) * W p ≤ 1 := by
        rw [Real.rpow_neg hσ.le, inv_mul_le_iff₀ (Real.rpow_pos_of_pos hσ s), mul_one]
        exact hWle p
      have h0 : 0 ≤ coshSum p ^ (-s) * W p := mul_nonneg (Real.rpow_nonneg hσ.le _) (hW0 p)
      have hpq : 0 ≤ ‖hatA a p.1‖ * ‖hatA b p.2‖ := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg hG.le (Real.rpow_nonneg hσ.le _))
        (mul_nonneg (hW0 p) hpq))]
      calc Real.Gamma s * coshSum p ^ (-s) * (W p * (‖hatA a p.1‖ * ‖hatA b p.2‖))
          = Real.Gamma s * (coshSum p ^ (-s) * W p) * (‖hatA a p.1‖ * ‖hatA b p.2‖) := by ring
        _ ≤ Real.Gamma s * 1 * (‖hatA a p.1‖ * ‖hatA b p.2‖) := by gcongr
        _ = _ := by ring

/-- `z ↦ ∫_p G(z, p)` is integrable on `(0, ∞)`. -/
lemma integrableOn_tzG_slice : IntegrableOn (fun z => ∫ p : ℝ × ℝ, tzG a b s W (z, p)) (Ioi 0) :=
  (integrable_tzG ha hb hs hWc hW0 hWle).integral_prod_left

/-- **The `z`-integral**: `∫_0^∞ ∫_p G = Γ(s) ∫_p σ^{-s} W conj â b̂`. -/
theorem integral_tzG :
    ∫ z in Ioi (0 : ℝ), ∫ p : ℝ × ℝ, tzG a b s W (z, p)
      = (Real.Gamma s : ℂ) * ∫ p : ℝ × ℝ, ((coshSum p ^ (-s) * W p : ℝ) : ℂ)
          * ((starRingEnd ℂ) (hatA a p.1) * hatA b p.2) := by
  rw [integral_integral_swap (f := fun z p => tzG a b s W (z, p)) (integrable_tzG ha hb hs hWc hW0 hWle),
    ← MeasureTheory.integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only [tzG]
  rw [integral_mul_const, integral_complex_ofReal]
  have e : ∫ z in Ioi (0 : ℝ), z ^ (s - 1) * W p * Real.exp (-(z * coshSum p))
      = W p * (Real.Gamma s * coshSum p ^ (-s)) := by
    rw [← integral_rpow_exp_cosh hs p, ← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun z _ => ?_)
    ring
  rw [e]; push_cast; ring

end tz

section deriv

variable {a : ℝ → ℂ}

/-- `z ∂_z ψ_a(z)`. -/
noncomputable def klInvD (a : ℝ → ℂ) (z : ℝ) : ℂ :=
  -(1 / 2 : ℂ) * ∫ t, ((z * Real.cosh t * Real.exp (-(z * Real.cosh t)) : ℝ) : ℂ) * hatA a t

lemma abs_mul_exp_neg_le (x : ℝ) (hx : 0 ≤ x) : x * Real.exp (-x) ≤ 1 := by
  have h := Real.add_one_le_exp x
  have hE := Real.exp_pos x
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one hE]; linarith

lemma integrable_exp_cosh_hatA (ha : IsKTest a) (z : ℝ) (hz : 0 < z) :
    Integrable fun t => ((Real.exp (-(z * Real.cosh t)) : ℝ) : ℂ) * hatA a t := by
  refine (integrable_hatA ha).bdd_mul (c := 1) (by fun_prop) (Eventually.of_forall fun t => ?_)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
  nlinarith [Real.cosh_pos t]

/-- `ψ_a' = (z ∂_z ψ_a)/z` on `(0, ∞)`. -/
theorem hasDerivAt_klInvA (ha : IsKTest a) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (klInvA a) (klInvD a z / z) z := by
  set γ : ℝ := z / 2
  have hγ : 0 < γ := by positivity
  set F : ℝ → ℝ → ℂ := fun z t => ((Real.exp (-(z * Real.cosh t)) : ℝ) : ℂ) * hatA a t
  set F' : ℝ → ℝ → ℂ := fun z t => ((-(Real.cosh t * Real.exp (-(z * Real.cosh t))) : ℝ) : ℂ) * hatA a t
  have hb : Integrable fun t => 1 / (Real.exp 1 * γ) * ‖hatA a t‖ := (integrable_hatA ha).norm.const_mul _
  have hball : ∀ w ∈ Metric.ball z γ, γ < w := by
    intro w hw
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hw
    simp only [γ] at hw ⊢; linarith
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℝ) (μ := (volume : Measure ℝ))
    (F := F) (F' := F') (bound := fun t => 1 / (Real.exp 1 * γ) * ‖hatA a t‖) (x₀ := z)
    (s := Metric.ball z γ) (Metric.ball_mem_nhds z hγ)
    (Eventually.of_forall fun w => ?_) (integrable_exp_cosh_hatA ha z hz)
    ((by fun_prop : Continuous fun t => ((-(Real.cosh t * Real.exp (-(z * Real.cosh t))) : ℝ) : ℂ)).mul
      (continuous_hatA ha)).aestronglyMeasurable
    (Eventually.of_forall fun t w hw => ?_) hb
    (Eventually.of_forall fun t w _ => ?_)
  · have hev : klInvA a =ᶠ[𝓝 z] fun w => (1 / 2 : ℂ) * ∫ t, F w t := by
      filter_upwards [Ioi_mem_nhds hz] with w hw using klInvA_eq ha hw
    have hd := (h.2.const_mul (1 / 2 : ℂ)).congr_of_eventuallyEq hev
    refine hd.congr_deriv ?_
    have hz' : (z : ℂ) ≠ 0 := by exact_mod_cast hz.ne'
    have e1 : ∫ t, F' z t = -∫ t, ((z * Real.cosh t * Real.exp (-(z * Real.cosh t)) : ℝ) : ℂ) * hatA a t / z := by
      rw [← integral_neg]
      congr 1; funext t
      simp only [F']; push_cast; field_simp
    rw [e1, klInvD, mul_div_assoc, ← integral_div]; ring
  · exact ((by fun_prop : Continuous fun t => ((Real.exp (-(w * Real.cosh t)) : ℝ) : ℂ)).mul
      (continuous_hatA ha)).aestronglyMeasurable
  · have hw' := hball w hw
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    have hc := Real.cosh_pos t
    calc Real.cosh t * Real.exp (-(w * Real.cosh t)) ≤ Real.cosh t * Real.exp (-(γ * Real.cosh t)) := by
          gcongr
      _ ≤ 1 / (Real.exp 1 * γ) := mul_exp_neg_le_inv hγ hc.le
  · have h1 : HasDerivAt (fun w : ℝ => -(w * Real.cosh t)) (-(1 * Real.cosh t)) w :=
      ((hasDerivAt_id w).mul_const _).neg
    have h2 := (h1.exp).ofReal_comp.mul_const (hatA a t)
    refine h2.congr_deriv ?_
    simp only [F']; push_cast; ring

end deriv

section forms

variable {a b : ℝ → ℂ}

lemma alg_aux1 {z A B T : ℂ} (hz : z ≠ 0) (h : z * T = A * B) :
    (1 / 2 : ℂ) * A * (-(1 / 2 : ℂ) * B / z) = -(1 / 4 : ℂ) * T := by
  have hT : T = A * B / z := by rw [eq_div_iff hz, mul_comm]; exact h
  rw [hT]; ring

lemma alg_aux2 {z A B T : ℂ} (hz : z ≠ 0) (h : z * T = A * B) :
    -(1 / 2 : ℂ) * A * (-(1 / 2 : ℂ) * B) / z = (1 / 4 : ℂ) * T := by
  have hT : T = A * B / z := by rw [eq_div_iff hz, mul_comm]; exact h
  rw [hT]; ring

/-- `⟨ψ_a, z∂_z ψ_b⟩_{dz/z}`. -/
noncomputable def Sform (a b : ℝ → ℂ) : ℂ :=
  ∫ z in Ioi (0 : ℝ), (starRingEnd ℂ) (klInvA a z) * (klInvD b z / z)

/-- `⟨ψ_a, z² ψ_b⟩_{dz/z}`. -/
noncomputable def Zform (a b : ℝ → ℂ) : ℂ :=
  ∫ z in Ioi (0 : ℝ), (z : ℂ) * ((starRingEnd ℂ) (klInvA a z) * klInvA b z)

lemma conj_klInvA_eq (ha : IsKTest a) {z : ℝ} (hz : 0 < z) :
    (starRingEnd ℂ) (klInvA a z)
      = (1 / 2 : ℂ) * ∫ t, ((Real.exp (-(z * Real.cosh t)) : ℝ) : ℂ) * (starRingEnd ℂ) (hatA a t) := by
  rw [klInvA_eq ha hz, map_mul, ← integral_conj]
  simp only [map_mul, Complex.conj_ofReal, map_div₀, map_one, map_ofNat]

lemma conj_klInvD_eq (a : ℝ → ℂ) (z : ℝ) :
    (starRingEnd ℂ) (klInvD a z)
      = -(1 / 2 : ℂ) * ∫ t, ((z * Real.cosh t * Real.exp (-(z * Real.cosh t)) : ℝ) : ℂ)
          * (starRingEnd ℂ) (hatA a t) := by
  rw [klInvD, map_mul, ← integral_conj]
  simp only [map_mul, Complex.conj_ofReal, map_div₀, map_one, map_ofNat, map_neg]

lemma cosh_snd_le (p : ℝ × ℝ) : Real.cosh p.2 ≤ coshSum p ^ (1 : ℝ) := by
  rw [Real.rpow_one]; unfold coshSum; linarith [Real.cosh_pos p.1]

lemma one_le_coshSum_sq (p : ℝ × ℝ) : (1 : ℝ) ≤ coshSum p ^ (2 : ℝ) :=
  Real.one_le_rpow (by linarith [two_le_coshSum p]) (by norm_num)

lemma cosh_mul_le (p : ℝ × ℝ) : Real.cosh p.1 * Real.cosh p.2 ≤ coshSum p ^ (2 : ℝ) := by
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  unfold coshSum; nlinarith [Real.cosh_pos p.1, Real.cosh_pos p.2]

lemma continuous_cosh_snd : Continuous fun p : ℝ × ℝ => Real.cosh p.2 := by fun_prop

/-- Pointwise form of `conj ψ_a · (z∂_z ψ_b)/z`. -/
lemma conj_mul_klInvD (ha : IsKTest a) {z : ℝ} (hz : 0 < z) :
    (starRingEnd ℂ) (klInvA a z) * (klInvD b z / z)
      = -(1 / 4 : ℂ) * ∫ p : ℝ × ℝ, tzG a b 1 (fun p => Real.cosh p.2) (z, p) := by
  have hz' : (z : ℂ) ≠ 0 := by exact_mod_cast hz.ne'
  have hpm := integral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (fun t => ((Real.exp (-(z * Real.cosh t)) : ℝ) : ℂ) * (starRingEnd ℂ) (hatA a t))
    (fun u => ((z * Real.cosh u * Real.exp (-(z * Real.cosh u)) : ℝ) : ℂ) * hatA b u)
  have e : ∀ p : ℝ × ℝ, ((Real.exp (-(z * Real.cosh p.1)) : ℝ) : ℂ) * (starRingEnd ℂ) (hatA a p.1)
      * (((z * Real.cosh p.2 * Real.exp (-(z * Real.cosh p.2)) : ℝ) : ℂ) * hatA b p.2)
      = (z : ℂ) * tzG a b 1 (fun p => Real.cosh p.2) (z, p) := by
    intro p
    simp only [tzG, coshSum]
    rw [sub_self, Real.rpow_zero, one_mul, mul_add, neg_add, Real.exp_add]; push_cast; ring
  simp_rw [e] at hpm
  rw [MeasureTheory.integral_const_mul] at hpm
  have hpm' : (z : ℂ) * ∫ p : ℝ × ℝ, tzG a b 1 (fun p => Real.cosh p.2) (z, p)
      = (∫ t, ((Real.exp (-(z * Real.cosh t)) : ℝ) : ℂ) * (starRingEnd ℂ) (hatA a t))
        * ∫ u, ((z * Real.cosh u * Real.exp (-(z * Real.cosh u)) : ℝ) : ℂ) * hatA b u := hpm
  rw [conj_klInvA_eq ha hz, klInvD]
  exact alg_aux1 hz' hpm'

/-- Pointwise form of `z conj ψ_a ψ_b`. -/
lemma mul_conj_klInvA (ha : IsKTest a) (hb : IsKTest b) {z : ℝ} (hz : 0 < z) :
    (z : ℂ) * ((starRingEnd ℂ) (klInvA a z) * klInvA b z)
      = (1 / 4 : ℂ) * ∫ p : ℝ × ℝ, tzG a b 2 (fun _ => 1) (z, p) := by
  have hpm := integral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (fun t => ((Real.exp (-(z * Real.cosh t)) : ℝ) : ℂ) * (starRingEnd ℂ) (hatA a t))
    (fun u => ((Real.exp (-(z * Real.cosh u)) : ℝ) : ℂ) * hatA b u)
  have e : ∀ p : ℝ × ℝ, (z : ℂ) * (((Real.exp (-(z * Real.cosh p.1)) : ℝ) : ℂ) * (starRingEnd ℂ) (hatA a p.1)
      * (((Real.exp (-(z * Real.cosh p.2)) : ℝ) : ℂ) * hatA b p.2))
      = tzG a b 2 (fun _ => 1) (z, p) := by
    intro p
    simp only [tzG, coshSum]
    rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, mul_add, neg_add, Real.exp_add]; push_cast; ring
  have hpm' : ∫ p : ℝ × ℝ, tzG a b 2 (fun _ => 1) (z, p)
      = (z : ℂ) * ((∫ t, ((Real.exp (-(z * Real.cosh t)) : ℝ) : ℂ) * (starRingEnd ℂ) (hatA a t))
        * ∫ u, ((Real.exp (-(z * Real.cosh u)) : ℝ) : ℂ) * hatA b u) := by
    rw [← show _ = _ from hpm, ← MeasureTheory.integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun p => (e p).symm)
  rw [conj_klInvA_eq ha hz, klInvA_eq hb hz, hpm']; ring

/-- `|z∂_zψ_b|²/z`. -/
lemma norm_sq_klInvD_div {z : ℝ} (hz : 0 < z) :
    ((‖klInvD b z‖ ^ 2 / z : ℝ) : ℂ)
      = (1 / 4 : ℂ) * ∫ p : ℝ × ℝ, tzG b b 2 (fun p => Real.cosh p.1 * Real.cosh p.2) (z, p) := by
  have hz' : (z : ℂ) ≠ 0 := by exact_mod_cast hz.ne'
  have hpm := integral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (fun t => ((z * Real.cosh t * Real.exp (-(z * Real.cosh t)) : ℝ) : ℂ) * (starRingEnd ℂ) (hatA b t))
    (fun u => ((z * Real.cosh u * Real.exp (-(z * Real.cosh u)) : ℝ) : ℂ) * hatA b u)
  have e : ∀ p : ℝ × ℝ, ((z * Real.cosh p.1 * Real.exp (-(z * Real.cosh p.1)) : ℝ) : ℂ) * (starRingEnd ℂ) (hatA b p.1)
      * (((z * Real.cosh p.2 * Real.exp (-(z * Real.cosh p.2)) : ℝ) : ℂ) * hatA b p.2)
      = (z : ℂ) * tzG b b 2 (fun p => Real.cosh p.1 * Real.cosh p.2) (z, p) := by
    intro p
    simp only [tzG, coshSum]
    rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, mul_add, neg_add, Real.exp_add]; push_cast; ring
  simp_rw [e] at hpm
  rw [MeasureTheory.integral_const_mul] at hpm
  have hpm' : (z : ℂ) * ∫ p : ℝ × ℝ, tzG b b 2 (fun p => Real.cosh p.1 * Real.cosh p.2) (z, p)
      = (∫ t, ((z * Real.cosh t * Real.exp (-(z * Real.cosh t)) : ℝ) : ℂ) * (starRingEnd ℂ) (hatA b t))
        * ∫ u, ((z * Real.cosh u * Real.exp (-(z * Real.cosh u)) : ℝ) : ℂ) * hatA b u := hpm
  have h2 : ((‖klInvD b z‖ ^ 2 : ℝ) : ℂ) = (starRingEnd ℂ) (klInvD b z) * klInvD b z := by
    rw [Complex.conj_mul']; push_cast; ring
  rw [Complex.ofReal_div, h2, conj_klInvD_eq, klInvD]
  exact alg_aux2 hz' hpm'

/-- `z∂_zψ_b ∈ L²(dz/z)`. -/
lemma integrableOn_klInvD_sq (hb : IsKTest b) : IntegrableOn (fun z => ‖klInvD b z‖ ^ 2 / z) (Ioi 0) := by
  have hI := integrableOn_tzG_slice (s := 2) hb hb (by norm_num)
    (W := fun p => Real.cosh p.1 * Real.cosh p.2) (by fun_prop)
    (fun p => mul_nonneg (Real.cosh_pos _).le (Real.cosh_pos _).le) cosh_mul_le
  have h2 : IntegrableOn (fun z : ℝ => ((‖klInvD b z‖ ^ 2 / z : ℝ) : ℂ)) (Ioi 0) :=
    IntegrableOn.congr_fun (hI.const_mul (1 / 4 : ℂ)) (fun z hz => (norm_sq_klInvD_div hz).symm) measurableSet_Ioi
  exact IntegrableOn.congr_fun h2.re (fun z _ => Complex.ofReal_re _) measurableSet_Ioi

/-- **`S(a, b)` on the `t`-side.** -/
theorem Sform_eq (ha : IsKTest a) (hb : IsKTest b) :
    Sform a b = -(1 / 4 : ℂ) * ∫ p : ℝ × ℝ, ((coshSum p ^ (-(1 : ℝ)) * Real.cosh p.2 : ℝ) : ℂ)
      * ((starRingEnd ℂ) (hatA a p.1) * hatA b p.2) := by
  have h := integral_tzG (s := 1) ha hb one_pos continuous_cosh_snd (fun p => (Real.cosh_pos _).le) cosh_snd_le
  rw [Real.Gamma_one, Complex.ofReal_one, one_mul] at h
  rw [Sform, setIntegral_congr_fun measurableSet_Ioi (fun z hz => conj_mul_klInvD ha hz),
    MeasureTheory.integral_const_mul, h]

/-- **`Z(a, b)` on the `t`-side.** -/
theorem Zform_eq (ha : IsKTest a) (hb : IsKTest b) :
    Zform a b = (1 / 4 : ℂ) * ∫ p : ℝ × ℝ, ((coshSum p ^ (-(2 : ℝ)) : ℝ) : ℂ)
      * ((starRingEnd ℂ) (hatA a p.1) * hatA b p.2) := by
  have h := integral_tzG (s := 2) ha hb (by norm_num) (W := fun _ => 1) continuous_const (fun _ => zero_le_one)
    one_le_coshSum_sq
  rw [show (2 : ℝ) = (1 : ℝ) + 1 by norm_num, Real.Gamma_add_one one_ne_zero, Real.Gamma_one] at h
  simp only [mul_one, one_mul, Complex.ofReal_one] at h
  rw [show (2 : ℝ) = (1 : ℝ) + 1 by norm_num, Zform,
    setIntegral_congr_fun measurableSet_Ioi (fun z hz => by
      rw [mul_conj_klInvA ha hb hz, show (2 : ℝ) = (1 : ℝ) + 1 by norm_num]),
    MeasureTheory.integral_const_mul, h]

end forms

section sylvester

variable {a b : ℝ → ℂ}

/-- `ν² a`. -/
noncomputable def n2 (a : ℝ → ℂ) (ν : ℝ) : ℂ := (ν : ℂ) ^ 2 * a ν

lemma IsKTest.n2 (ha : IsKTest a) : IsKTest (n2 a) := by
  have e : Qschubert.n2 a = fun x : ℝ => (x : ℂ) * ((x : ℂ) * a x) := by
    funext ν; simp only [Qschubert.n2]; ring
  rw [e]; exact ha.mul_id.mul_id

/-- Two integrations by parts against a bounded `q`: `∫ hat(ν²a) q = -∫ â q₂`. -/
lemma ibp_hatA (ha : IsKTest a) {q q₁ q₂ : ℝ → ℝ} (hqc : Continuous q) (hq₁c : Continuous q₁) (hq₂c : Continuous q₂)
    (hq : ∀ t, HasDerivAt q (q₁ t) t) (hq₁ : ∀ t, HasDerivAt q₁ (q₂ t) t) {C : ℝ}
    (b0 : ∀ t, |q t| ≤ C) (b1 : ∀ t, |q₁ t| ≤ C) (b2 : ∀ t, |q₂ t| ≤ C) :
    ∫ t, hatA (Qschubert.n2 a) t * (q t : ℂ) = -∫ t, hatA a t * (q₂ t : ℂ) := by
  have hsm : ∀ {k : ℝ → ℂ}, IsKTest k → IsKTest fun ν => (ν : ℂ) * I * k ν := fun hk =>
    hk.mul_smooth (φ := fun ν : ℝ => (ν : ℂ) * I) (Complex.ofRealCLM.contDiff.mul contDiff_const)
  set a1 : ℝ → ℂ := fun ν => (ν : ℂ) * I * a ν
  set a2 : ℝ → ℂ := fun ν => (ν : ℂ) * I * a1 ν
  have ha1 : IsKTest a1 := hsm ha
  have ha2 : IsKTest a2 := hsm ha1
  have e2 : ∀ t, hatA (Qschubert.n2 a) t = -hatA a2 t := by
    intro t
    have h := hatA_smul (-1 : ℂ) (Qschubert.n2 a) t
    have e : (fun ν => (-1 : ℂ) * Qschubert.n2 a ν) = a2 := by
      funext ν; simp only [Qschubert.n2, a2, a1]
      linear_combination (-(ν : ℂ) ^ 2 * a ν) * Complex.I_mul_I
    rw [e] at h
    rw [h]; ring
  have bdC : ∀ (g : ℝ → ℝ), Continuous g → (∀ t, |g t| ≤ C) → ∀ (k : ℝ → ℂ), IsKTest k →
      Integrable fun t => (g t : ℂ) * hatA k t := fun g hg hb k hk =>
    (integrable_hatA hk).bdd_mul (c := C) (Complex.continuous_ofReal.comp hg).aestronglyMeasurable
      (Eventually.of_forall fun t => by
        show ‖((g t : ℝ) : ℂ)‖ ≤ C
        rw [Complex.norm_real, Real.norm_eq_abs]; exact hb t)
  have hD : ∀ {k : ℝ → ℂ}, IsKTest k → ∀ t, HasDerivAt (hatA k) (hatA (fun ν => (ν : ℂ) * I * k ν) t) t :=
    fun hk t => hasDerivAt_hatA hk t
  have s1 : ∫ t, (q t : ℂ) * hatA a2 t = -∫ t, (q₁ t : ℂ) * hatA a1 t :=
    integral_mul_deriv_eq_deriv_mul_of_integrable (u := fun t => (q t : ℂ)) (u' := fun t => (q₁ t : ℂ))
      (v := hatA a1) (v' := hatA a2) (fun t _ => (hq t).ofReal_comp) (fun t _ => hD ha1 t)
      (bdC q hqc b0 _ ha2) (bdC q₁ hq₁c b1 _ ha1) (bdC q hqc b0 _ ha1)
  have s2 : ∫ t, (q₁ t : ℂ) * hatA a1 t = -∫ t, (q₂ t : ℂ) * hatA a t :=
    integral_mul_deriv_eq_deriv_mul_of_integrable (u := fun t => (q₁ t : ℂ)) (u' := fun t => (q₂ t : ℂ))
      (v := hatA a) (v' := hatA a1) (fun t _ => (hq₁ t).ofReal_comp) (fun t _ => hD ha t)
      (bdC q₁ hq₁c b1 _ ha1) (bdC q₂ hq₂c b2 _ ha) (bdC q₁ hq₁c b1 _ ha)
  have e3 : ∫ t, hatA (Qschubert.n2 a) t * (q t : ℂ) = -∫ t, (q t : ℂ) * hatA a2 t := by
    rw [← integral_neg]; congr 1; funext t; rw [e2]; ring
  have e4 : ∫ t, hatA a t * (q₂ t : ℂ) = ∫ t, (q₂ t : ℂ) * hatA a t := by congr 1; funext t; ring
  rw [e3, s1, s2, e4]; ring

end sylvester

section sylvester2

variable {a b : ℝ → ℂ}

/-- `Q` in the variable `t` (fixed `u`). -/
noncomputable def q0f (u t : ℝ) : ℝ := Real.cosh u / (Real.cosh t + Real.cosh u)
noncomputable def q1t (u t : ℝ) : ℝ := -(Real.cosh u * Real.sinh t) / (Real.cosh t + Real.cosh u) ^ 2
noncomputable def q2t (u t : ℝ) : ℝ :=
  -(Real.cosh u * Real.cosh t) / (Real.cosh t + Real.cosh u) ^ 2
    + 2 * Real.cosh u * Real.sinh t ^ 2 / (Real.cosh t + Real.cosh u) ^ 3
/-- `Q` in the variable `u` (fixed `t`). -/
noncomputable def r0f (t u : ℝ) : ℝ := Real.cosh u / (Real.cosh t + Real.cosh u)
noncomputable def r1u (t u : ℝ) : ℝ := Real.cosh t * Real.sinh u / (Real.cosh t + Real.cosh u) ^ 2
noncomputable def r2u (t u : ℝ) : ℝ :=
  Real.cosh t * Real.cosh u / (Real.cosh t + Real.cosh u) ^ 2
    - 2 * Real.cosh t * Real.sinh u ^ 2 / (Real.cosh t + Real.cosh u) ^ 3

lemma cosh_add_ne (t u : ℝ) : Real.cosh t + Real.cosh u ≠ 0 := by
  have := Real.cosh_pos t; have := Real.cosh_pos u; positivity

lemma hasDerivAt_q0f (u t : ℝ) : HasDerivAt (q0f u) (q1t u t) t := by
  have h : HasDerivAt (fun t => Real.cosh t + Real.cosh u) (Real.sinh t) t := (Real.hasDerivAt_cosh t).add_const _
  refine ((hasDerivAt_const t (Real.cosh u)).div h (cosh_add_ne t u)).congr_deriv ?_
  unfold q1t; ring

lemma hasDerivAt_q1t (u t : ℝ) : HasDerivAt (q1t u) (q2t u t) t := by
  have h : HasDerivAt (fun t => Real.cosh t + Real.cosh u) (Real.sinh t) t := (Real.hasDerivAt_cosh t).add_const _
  have hN : HasDerivAt (fun t => -(Real.cosh u * Real.sinh t)) (-(Real.cosh u * Real.cosh t)) t :=
    ((Real.hasDerivAt_sinh t).const_mul _).neg
  have hD : HasDerivAt (fun t => (Real.cosh t + Real.cosh u) ^ 2)
      (2 * (Real.cosh t + Real.cosh u) * Real.sinh t) t := by
    have e : (fun t => (Real.cosh t + Real.cosh u) ^ 2) = fun t => (Real.cosh t + Real.cosh u) * (Real.cosh t + Real.cosh u) := by
      funext t; ring
    rw [e]; exact (h.mul h).congr_deriv (by ring)
  refine (hN.div hD (pow_ne_zero 2 (cosh_add_ne t u))).congr_deriv ?_
  have hn := cosh_add_ne t u
  unfold q2t; field_simp; ring

lemma hasDerivAt_r0f (t u : ℝ) : HasDerivAt (r0f t) (r1u t u) u := by
  have h : HasDerivAt (fun u => Real.cosh t + Real.cosh u) (Real.sinh u) u := (Real.hasDerivAt_cosh u).const_add _
  refine ((Real.hasDerivAt_cosh u).div h (cosh_add_ne t u)).congr_deriv ?_
  have hn := cosh_add_ne t u
  unfold r1u; field_simp; ring

lemma hasDerivAt_r1u (t u : ℝ) : HasDerivAt (r1u t) (r2u t u) u := by
  have h : HasDerivAt (fun u => Real.cosh t + Real.cosh u) (Real.sinh u) u := (Real.hasDerivAt_cosh u).const_add _
  have hN : HasDerivAt (fun u => Real.cosh t * Real.sinh u) (Real.cosh t * Real.cosh u) u :=
    (Real.hasDerivAt_sinh u).const_mul _
  have hD : HasDerivAt (fun u => (Real.cosh t + Real.cosh u) ^ 2)
      (2 * (Real.cosh t + Real.cosh u) * Real.sinh u) u := by
    have e : (fun u => (Real.cosh t + Real.cosh u) ^ 2) = fun u => (Real.cosh t + Real.cosh u) * (Real.cosh t + Real.cosh u) := by
      funext u; ring
    rw [e]; exact (h.mul h).congr_deriv (by ring)
  refine (hN.div hD (pow_ne_zero 2 (cosh_add_ne t u))).congr_deriv ?_
  have hn := cosh_add_ne t u
  unfold r2u; field_simp

/-- Bounds, in the notation `c = cosh`, `s = sinh`, for the derivative pair. -/
lemma q_bounds {c d s : ℝ} (hc : 1 ≤ c) (hd : 1 ≤ d) (hs : s ^ 2 ≤ c ^ 2) :
    |d / (c + d)| ≤ 3 ∧ |(d * s) / (c + d) ^ 2| ≤ 3 ∧
      |-(d * c) / (c + d) ^ 2 + 2 * d * s ^ 2 / (c + d) ^ 3| ≤ 3 := by
  have hσ : 0 < c + d := by linarith
  set x := d / (c + d)
  set y := c / (c + d)
  set e := s / (c + d)
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 := by rw [div_le_one hσ]; linarith
  have hy0 : 0 ≤ y := by positivity
  have hy1 : y ≤ 1 := by rw [div_le_one hσ]; linarith
  have he : e ^ 2 ≤ 1 := by
    rw [div_pow, div_le_one (by positivity)]
    nlinarith
  have he' : |e| ≤ 1 := by
    rw [← sq_le_one_iff_abs_le_one]; exact he
  have e1 : (d * s) / (c + d) ^ 2 = x * e := by simp only [x, e]; field_simp
  have e2 : -(d * c) / (c + d) ^ 2 + 2 * d * s ^ 2 / (c + d) ^ 3 = -(x * y) + 2 * x * e ^ 2 := by
    simp only [x, y, e]; field_simp
  rw [e1, e2]
  refine ⟨by rw [abs_of_nonneg hx0]; linarith, ?_, ?_⟩
  · rw [abs_mul, abs_of_nonneg hx0]; nlinarith [abs_nonneg e]
  · rw [abs_le]; constructor <;> nlinarith [mul_nonneg hx0 hy0, mul_nonneg hx0 (sq_nonneg e),
      mul_le_mul hx1 hy1 hy0 zero_le_one, mul_le_mul hx1 he (sq_nonneg e) zero_le_one]

lemma sinh_sq_le_cosh_sq (t : ℝ) : Real.sinh t ^ 2 ≤ Real.cosh t ^ 2 := by
  rw [Real.cosh_sq]; linarith

lemma cont_q0 : Continuous fun p : ℝ × ℝ => Real.cosh p.2 / (Real.cosh p.1 + Real.cosh p.2) :=
  Continuous.div (by fun_prop) (by fun_prop) (fun p => cosh_add_ne _ _)

/-- `K(p) conj â(p₁) b̂(p₂)` is integrable for bounded continuous `K`. -/
lemma integrable_K (ha : IsKTest a) (hb : IsKTest b) {K : ℝ × ℝ → ℝ} (hK : Continuous K) {C : ℝ}
    (hC : ∀ p, |K p| ≤ C) :
    Integrable (fun p : ℝ × ℝ => (K p : ℂ) * ((starRingEnd ℂ) (hatA a p.1) * hatA b p.2))
      ((volume : Measure ℝ).prod volume) := by
  have hA := integrable_hatA ha
  have hB := integrable_hatA hb
  have h0 : Integrable (fun p : ℝ × ℝ => (starRingEnd ℂ) (hatA a p.1) * hatA b p.2)
      ((volume : Measure ℝ).prod volume) := by
    refine (hA.norm.mul_prod hB.norm).mono' ?_ (Eventually.of_forall fun p => ?_)
    · exact ((Complex.continuous_conj.comp ((continuous_hatA ha).comp continuous_fst)).mul
        ((continuous_hatA hb).comp continuous_snd)).aestronglyMeasurable
    · simp only [norm_mul, RCLike.norm_conj]; exact le_refl _
  exact h0.bdd_mul (c := C) (Complex.continuous_ofReal.comp hK).aestronglyMeasurable
    (Eventually.of_forall fun p => by
      show ‖((K p : ℝ) : ℂ)‖ ≤ C
      rw [Complex.norm_real, Real.norm_eq_abs]; exact hC p)

/-- The first variable: `∬ Q conj hat(ν²a) b̂ = -∬ ∂_t²Q conj â b̂`. -/
lemma SQ_left (ha : IsKTest a) (hb : IsKTest b) :
    ∫ p : ℝ × ℝ, ((Real.cosh p.2 / (Real.cosh p.1 + Real.cosh p.2) : ℝ) : ℂ)
        * ((starRingEnd ℂ) (hatA (n2 a) p.1) * hatA b p.2)
      = -∫ p : ℝ × ℝ, ((q2t p.2 p.1 : ℝ) : ℂ) * ((starRingEnd ℂ) (hatA a p.1) * hatA b p.2) := by
  have hc0 := cont_q0
  have hc2 : Continuous fun p : ℝ × ℝ => q2t p.2 p.1 := by
    unfold q2t
    exact Continuous.add (Continuous.div (by fun_prop) (by fun_prop) (fun p => pow_ne_zero _ (cosh_add_ne _ _)))
      (Continuous.div (by fun_prop) (by fun_prop) (fun p => pow_ne_zero _ (cosh_add_ne _ _)))
  have b0 : ∀ p : ℝ × ℝ, |Real.cosh p.2 / (Real.cosh p.1 + Real.cosh p.2)| ≤ 3 := fun p =>
    (q_bounds (Real.one_le_cosh p.1) (Real.one_le_cosh p.2) (sinh_sq_le_cosh_sq p.1)).1
  have b2 : ∀ p : ℝ × ℝ, |q2t p.2 p.1| ≤ 3 := fun p =>
    (q_bounds (Real.one_le_cosh p.1) (Real.one_le_cosh p.2) (sinh_sq_le_cosh_sq p.1)).2.2
  have i0 := integrable_K ha.n2 hb hc0 b0
  have i2 := integrable_K ha hb hc2 b2
  rw [show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl,
    integral_prod_symm _ i0, integral_prod_symm _ i2, ← integral_neg]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  have hI := ibp_hatA ha (q := q0f u) (q₁ := q1t u) (q₂ := q2t u)
    (Continuous.div (by fun_prop) (by fun_prop) (fun t => cosh_add_ne _ _))
    (Continuous.div (by fun_prop) (by fun_prop) (fun t => pow_ne_zero _ (cosh_add_ne _ _)))
    (Continuous.add (Continuous.div (by fun_prop) (by fun_prop) (fun t => pow_ne_zero _ (cosh_add_ne _ _)))
      (Continuous.div (by fun_prop) (by fun_prop) (fun t => pow_ne_zero _ (cosh_add_ne _ _))))
    (hasDerivAt_q0f u) (hasDerivAt_q1t u) (C := 3)
    (fun t => (q_bounds (Real.one_le_cosh t) (Real.one_le_cosh u) (sinh_sq_le_cosh_sq t)).1)
    (fun t => by
      have := (q_bounds (Real.one_le_cosh t) (Real.one_le_cosh u) (sinh_sq_le_cosh_sq t)).2.1
      unfold q1t; rwa [neg_div, abs_neg])
    (fun t => (q_bounds (Real.one_le_cosh t) (Real.one_le_cosh u) (sinh_sq_le_cosh_sq t)).2.2)
  have hC := congrArg (starRingEnd ℂ) hI
  rw [← integral_conj, map_neg, ← integral_conj] at hC
  simp only [map_mul, Complex.conj_ofReal] at hC
  have e1 : ∫ t, ((Real.cosh u / (Real.cosh t + Real.cosh u) : ℝ) : ℂ)
      * ((starRingEnd ℂ) (hatA (n2 a) t) * hatA b u)
      = (∫ t, (starRingEnd ℂ) (hatA (n2 a) t) * ((q0f u t : ℝ) : ℂ)) * hatA b u := by
    rw [← integral_mul_const]; congr 1; funext t; simp only [q0f]; ring
  have e2 : -∫ t, ((q2t u t : ℝ) : ℂ) * ((starRingEnd ℂ) (hatA a t) * hatA b u)
      = (-∫ t, (starRingEnd ℂ) (hatA a t) * ((q2t u t : ℝ) : ℂ)) * hatA b u := by
    rw [neg_mul, ← integral_mul_const]; congr 2; funext t; ring
  simp only
  rw [e1, e2, hC]

/-- The second variable: `∬ Q conj â hat(ν²b) = -∬ ∂_u²Q conj â b̂`. -/
lemma SQ_right (ha : IsKTest a) (hb : IsKTest b) :
    ∫ p : ℝ × ℝ, ((Real.cosh p.2 / (Real.cosh p.1 + Real.cosh p.2) : ℝ) : ℂ)
        * ((starRingEnd ℂ) (hatA a p.1) * hatA (n2 b) p.2)
      = -∫ p : ℝ × ℝ, ((r2u p.1 p.2 : ℝ) : ℂ) * ((starRingEnd ℂ) (hatA a p.1) * hatA b p.2) := by
  have hc0 := cont_q0
  have hc2 : Continuous fun p : ℝ × ℝ => r2u p.1 p.2 := by
    unfold r2u
    exact Continuous.sub (Continuous.div (by fun_prop) (by fun_prop) (fun p => pow_ne_zero _ (cosh_add_ne _ _)))
      (Continuous.div (by fun_prop) (by fun_prop) (fun p => pow_ne_zero _ (cosh_add_ne _ _)))
  have bq : ∀ t u : ℝ, |r1u t u| ≤ 3 ∧ |r2u t u| ≤ 3 := by
    intro t u
    obtain ⟨-, h1, h2⟩ := q_bounds (Real.one_le_cosh u) (Real.one_le_cosh t) (sinh_sq_le_cosh_sq u)
    rw [add_comm (Real.cosh u)] at h1 h2
    constructor
    · unfold r1u; exact h1
    · have e : r2u t u = -(-(Real.cosh t * Real.cosh u) / (Real.cosh t + Real.cosh u) ^ 2
          + 2 * Real.cosh t * Real.sinh u ^ 2 / (Real.cosh t + Real.cosh u) ^ 3) := by
        unfold r2u; ring
      rw [e, abs_neg]; exact h2
  have b0 : ∀ p : ℝ × ℝ, |Real.cosh p.2 / (Real.cosh p.1 + Real.cosh p.2)| ≤ 3 := fun p =>
    (q_bounds (Real.one_le_cosh p.1) (Real.one_le_cosh p.2) (sinh_sq_le_cosh_sq p.1)).1
  have i0 := integrable_K ha hb.n2 hc0 b0
  have i2 := integrable_K ha hb hc2 (fun p => (bq p.1 p.2).2)
  rw [show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl,
    integral_prod _ i0, integral_prod _ i2, ← integral_neg]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  have hI := ibp_hatA hb (q := r0f t) (q₁ := r1u t) (q₂ := r2u t)
    (Continuous.div (by fun_prop) (by fun_prop) (fun u => cosh_add_ne _ _))
    (Continuous.div (by fun_prop) (by fun_prop) (fun u => pow_ne_zero _ (cosh_add_ne _ _)))
    (Continuous.sub (Continuous.div (by fun_prop) (by fun_prop) (fun u => pow_ne_zero _ (cosh_add_ne _ _)))
      (Continuous.div (by fun_prop) (by fun_prop) (fun u => pow_ne_zero _ (cosh_add_ne _ _))))
    (hasDerivAt_r0f t) (hasDerivAt_r1u t) (C := 3)
    (fun u => (q_bounds (Real.one_le_cosh t) (Real.one_le_cosh u) (sinh_sq_le_cosh_sq t)).1)
    (fun u => (bq t u).1) (fun u => (bq t u).2)
  have e1 : ∫ u, ((Real.cosh u / (Real.cosh t + Real.cosh u) : ℝ) : ℂ)
      * ((starRingEnd ℂ) (hatA a t) * hatA (n2 b) u)
      = (starRingEnd ℂ) (hatA a t) * ∫ u, hatA (n2 b) u * ((r0f t u : ℝ) : ℂ) := by
    rw [← MeasureTheory.integral_const_mul]; congr 1; funext u; simp only [r0f]; ring
  have e2 : -∫ u, ((r2u t u : ℝ) : ℂ) * ((starRingEnd ℂ) (hatA a t) * hatA b u)
      = (starRingEnd ℂ) (hatA a t) * -∫ u, hatA b u * ((r2u t u : ℝ) : ℂ) := by
    rw [mul_neg, ← MeasureTheory.integral_const_mul]; congr 2; funext u; ring
  simp only
  rw [e1, e2, hI]

lemma r2u_sub_q2t (p : ℝ × ℝ) :
    r2u p.1 p.2 - q2t p.2 p.1 = 2 * coshSum p ^ (-(2 : ℝ)) := by
  have hσ := coshSum_pos p
  have hn := cosh_add_ne p.1 p.2
  have ec : coshSum p = Real.cosh p.1 + Real.cosh p.2 := rfl
  rw [Real.rpow_neg hσ.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, ec]
  unfold r2u q2t
  have s1 := Real.cosh_sq p.1
  have s2 := Real.cosh_sq p.2
  have e1 : Real.sinh p.1 ^ 2 = Real.cosh p.1 ^ 2 - 1 := by linarith
  have e2 : Real.sinh p.2 ^ 2 = Real.cosh p.2 ^ 2 - 1 := by linarith
  rw [e1, e2]
  field_simp
  ring

/-- **The Sylvester identity** `S(ν²a, b) - S(a, ν²b) = -2 Z(a, b)`. -/
theorem Sform_sylvester (ha : IsKTest a) (hb : IsKTest b) :
    Sform (n2 a) b - Sform a (n2 b) = -2 * Zform a b := by
  have eQ : ∀ p : ℝ × ℝ, coshSum p ^ (-(1 : ℝ)) * Real.cosh p.2 = Real.cosh p.2 / (Real.cosh p.1 + Real.cosh p.2) := by
    intro p
    rw [Real.rpow_neg_one]
    show (Real.cosh p.1 + Real.cosh p.2)⁻¹ * _ = _
    rw [div_eq_inv_mul]
  rw [Sform_eq ha.n2 hb, Sform_eq ha hb.n2, Zform_eq ha hb]
  simp_rw [eQ]
  rw [SQ_left ha hb, SQ_right ha hb]
  have hc2t : Continuous fun p : ℝ × ℝ => q2t p.2 p.1 := by
    unfold q2t
    exact Continuous.add (Continuous.div (by fun_prop) (by fun_prop) (fun p => pow_ne_zero _ (cosh_add_ne _ _)))
      (Continuous.div (by fun_prop) (by fun_prop) (fun p => pow_ne_zero _ (cosh_add_ne _ _)))
  have hc2u : Continuous fun p : ℝ × ℝ => r2u p.1 p.2 := by
    unfold r2u
    exact Continuous.sub (Continuous.div (by fun_prop) (by fun_prop) (fun p => pow_ne_zero _ (cosh_add_ne _ _)))
      (Continuous.div (by fun_prop) (by fun_prop) (fun p => pow_ne_zero _ (cosh_add_ne _ _)))
  have bq2 : ∀ p : ℝ × ℝ, |q2t p.2 p.1| ≤ 3 := fun p =>
    (q_bounds (Real.one_le_cosh p.1) (Real.one_le_cosh p.2) (sinh_sq_le_cosh_sq p.1)).2.2
  have bu2 : ∀ p : ℝ × ℝ, |r2u p.1 p.2| ≤ 3 := by
    intro p
    obtain ⟨-, -, h2⟩ := q_bounds (Real.one_le_cosh p.2) (Real.one_le_cosh p.1) (sinh_sq_le_cosh_sq p.2)
    rw [add_comm (Real.cosh p.2)] at h2
    have e : r2u p.1 p.2 = -(-(Real.cosh p.1 * Real.cosh p.2) / (Real.cosh p.1 + Real.cosh p.2) ^ 2
        + 2 * Real.cosh p.1 * Real.sinh p.2 ^ 2 / (Real.cosh p.1 + Real.cosh p.2) ^ 3) := by
      unfold r2u; ring
    rw [e, abs_neg]; exact h2
  have i1 := integrable_K ha hb hc2t bq2
  have i2 := integrable_K ha hb hc2u bu2
  have hdiff : (∫ p : ℝ × ℝ, ((r2u p.1 p.2 : ℝ) : ℂ) * ((starRingEnd ℂ) (hatA a p.1) * hatA b p.2))
      - (∫ p : ℝ × ℝ, ((q2t p.2 p.1 : ℝ) : ℂ) * ((starRingEnd ℂ) (hatA a p.1) * hatA b p.2))
      = 2 * ∫ p : ℝ × ℝ, ((coshSum p ^ (-(2 : ℝ)) : ℝ) : ℂ) * ((starRingEnd ℂ) (hatA a p.1) * hatA b p.2) := by
    have hs := integral_sub i2 i1
    rw [show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl, ← hs,
      ← MeasureTheory.integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    have h := r2u_sub_q2t p
    have hc : ((r2u p.1 p.2 : ℝ) : ℂ) - ((q2t p.2 p.1 : ℝ) : ℂ) = 2 * ((coshSum p ^ (-(2 : ℝ)) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_sub, h]; push_cast; ring
    show ((r2u p.1 p.2 : ℝ) : ℂ) * _ - ((q2t p.2 p.1 : ℝ) : ℂ) * _ = 2 * (_ * _)
    rw [← sub_mul, hc, mul_assoc]
  linear_combination (-1 / 4 : ℂ) * hdiff

end sylvester2

end Qschubert
