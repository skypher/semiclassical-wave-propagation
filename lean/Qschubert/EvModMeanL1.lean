import Qschubert.EvModAe

/-!
# The mean lemma in slice form, for integrable pairings

Stage A of the plan for Proposition `ev:mod` (`lean/BLUEPRINT.md`), item L8 (first part).

For a representative `a'` of `e^{-αΛ} h` (`ModData h h₀`) and a function `E` on `ℍ` with `E(z + n) = E(z)`:

* `integral_amp_mul_slice`: for bounded `E`, `∫_ℍ a' E dν = ∫_0^∞ a₀(y) (∫_0^1 E(s + iy) ds) dy/y²`;
* `slice_norm_le_bdd`, `slice_lintegral_le`: for `g ≥ 0`, `∫_0^∞ |a₀(y)| (∫_0^1 g(s + iy) ds) dy/y² ≤ ∫_ℍ |a'| g dν`
  (apply the first statement to `E = g · conj(sgn a₀(Im z))`);
* `integral_amp_mul_slice_L1`: the first statement for all measurable `E` with `a' E ∈ L¹(ℍ)` (truncation; the
  second statement gives the domination).
-/

namespace Qschubert

open MeasureTheory Filter Topology Set Complex
open scoped Real ComplexConjugate MatrixGroups UpperHalfPlane ENNReal

variable {α : ℝ} {h : ℂ → ℂ} {h₀ : ℝ → ℝ} {a' : ℍ → ℂ}

/-- The point `s + iy` of `ℍ` (for `y > 0`). -/
noncomputable def ptH (s y : ℝ) : ℍ := UpperHalfPlane.ofComplex ⟨s, y⟩

lemma measurable_ptH : Measurable fun p : ℝ × ℝ => ptH p.2 p.1 := by
  have hc : Measurable fun p : ℝ × ℝ => (⟨p.2, p.1⟩ : ℂ) := by
    have e0 : (fun p : ℝ × ℝ => (⟨p.2, p.1⟩ : ℂ)) = fun p : ℝ × ℝ => (p.2 : ℂ) + (p.1 : ℂ) * Complex.I := by
      funext p
      apply Complex.ext <;> simp
    rw [e0]
    fun_prop
  exact measurable_ofComplex.comp hc

lemma ptH_eq {s y : ℝ} (hy : 0 < y) : ptH s y = ⟨⟨s, y⟩, hy⟩ := by
  rw [ptH, UpperHalfPlane.ofComplex_apply_of_im_pos (show 0 < (⟨s, y⟩ : ℂ).im from hy)]

lemma ptH_im {s y : ℝ} (hy : 0 < y) : (ptH s y).im = y := by
  rw [ptH_eq hy]
  rfl

lemma ptH_re {s y : ℝ} (hy : 0 < y) : (ptH s y).re = s := by
  rw [ptH_eq hy]
  rfl

lemma transGL_smul_eq_ptH (s : ℝ) (w : ℍ) : transGL s • w = ptH (w.re + s) w.im := by
  rw [transGL_smul_eq_ofComplex, ptH]
  congr 1
  apply Complex.ext <;> simp

/-- The mean over a period does not depend on the starting point. -/
lemma mean_periodic {E : ℍ → ℂ} (hEper : ∀ (n : ℤ) (z : ℍ), E (transGL (n : ℝ) • z) = E z) (w : ℍ) :
    ∫ s in (0 : ℝ)..1, E (transGL (-s) • w) = ∫ s in (0 : ℝ)..1, E (ptH s w.im) := by
  set ψ : ℝ → ℂ := fun u => E (ptH u w.im) with hψ
  have hper : Function.Periodic ψ 1 := by
    intro u
    have e : ptH (u + 1) w.im = transGL ((1 : ℤ) : ℝ) • ptH u w.im := by
      rw [transGL_smul_eq_ptH, ptH_re w.im_pos, ptH_im w.im_pos]
      simp
    show E (ptH (u + 1) w.im) = E (ptH u w.im)
    rw [e, hEper]
  have e1 : ∀ s : ℝ, E (transGL (-s) • w) = ψ (w.re - s) := by
    intro s
    show E (transGL (-s) • w) = E (ptH (w.re - s) w.im)
    rw [transGL_smul_eq_ptH, sub_eq_add_neg]
  simp_rw [e1]
  have h1 := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := 1) ψ w.re
  have h2 := hper.intervalIntegral_add_eq (w.re - 1) 0
  rw [h1, sub_zero]
  have e2 : w.re = w.re - 1 + 1 := by ring
  rw [show (∫ u in (w.re - 1)..w.re, ψ u) = ∫ u in (w.re - 1)..(w.re - 1 + 1), ψ u by rw [← e2], h2, zero_add]

lemma measurable_sliceMean {E : ℍ → ℂ} (hEm : Measurable E) :
    Measurable fun y : ℝ => ∫ s in (0 : ℝ)..1, E (ptH s y) := by
  have e : (fun y : ℝ => ∫ s in (0 : ℝ)..1, E (ptH s y)) = fun y : ℝ => ∫ s in Ioc (0 : ℝ) 1, E (ptH s y) := by
    funext y
    rw [intervalIntegral.integral_of_le zero_le_one]
  rw [e]
  have hj : Measurable fun p : ℝ × ℝ => E (ptH p.2 p.1) := hEm.comp measurable_ptH
  exact (hj.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioc (0 : ℝ) 1))).measurable

/-- **The mean lemma in slice form**, bounded `E`. -/
theorem integral_amp_mul_slice (hα : 0 < α) (hd : ModData h h₀) (ham : Measurable a') (hai : Integrable a')
    (ha : a' =ᵐ[volume] ampMod α hα.le hd.test) {E : ℍ → ℂ} (hEm : Measurable E) {M : ℝ} (hEb : ∀ z, ‖E z‖ ≤ M)
    (hEper : ∀ (n : ℤ) (z : ℍ), E (transGL (n : ℝ) • z) = E z) :
    ∫ z : ℍ, a' z * E z
      = ∫ y in Ioi (0 : ℝ), ((y ^ 2)⁻¹ : ℝ) • (zeroModeH a' y * ∫ s in (0 : ℝ)..1, E (ptH s y)) := by
  have hstep3 := integral_amp_mul_eq_mean hα hd ham hai ha hEm hEb hEper
  have hDb : ∀ y : ℝ, ‖∫ s in (0 : ℝ)..1, E (ptH s y)‖ ≤ |M| := by
    intro y
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
      (f := fun s => E (ptH s y)) (C := |M|) (fun s _ => (hEb _).trans (le_abs_self M))
    simpa using this
  have hDm := measurable_sliceMean hEm
  have hint5 : Integrable fun w : ℍ => a' w * ∫ s in (0 : ℝ)..1, E (ptH s w.im) :=
    (hai.norm.mul_const |M|).mono'
      (ham.mul (hDm.comp UpperHalfPlane.continuous_im.measurable)).aestronglyMeasurable
      (Eventually.of_forall fun w => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hDb _) (norm_nonneg _))
  rw [hstep3]
  simp_rw [mean_periodic hEper]
  rw [integral_H_slice hint5]
  refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
  have hy0 : (0 : ℝ) < y := hy
  have e : ∀ x : ℝ, a' (UpperHalfPlane.ofComplex ⟨x, y⟩)
        * ∫ s in (0 : ℝ)..1, E (ptH s (UpperHalfPlane.ofComplex ⟨x, y⟩).im)
      = a' ⟨⟨x, y⟩, hy0⟩ * ∫ s in (0 : ℝ)..1, E (ptH s y) := by
    intro x
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos (show 0 < (⟨x, y⟩ : ℂ).im from hy0)]
    rfl
  simp only [e]
  rw [integral_mul_const, zeroModeH, dite_eq_left hy0]

/-- `c · unitC c = |c|`. -/
noncomputable def unitC (c : ℂ) : ℂ := if c = 0 then 0 else conj c / (‖c‖ : ℂ)

lemma mul_unitC (c : ℂ) : c * unitC c = (‖c‖ : ℂ) := by
  by_cases hc : c = 0
  · simp [unitC, hc]
  · have hn : (‖c‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.2 hc)
    have e : unitC c = conj c / (‖c‖ : ℂ) := by simp [unitC, hc]
    rw [e, mul_div_assoc', Complex.mul_conj, Complex.normSq_eq_norm_sq, div_eq_iff hn]
    push_cast
    ring

lemma norm_unitC_le (c : ℂ) : ‖unitC c‖ ≤ 1 := by
  by_cases hc : c = 0
  · simp [unitC, hc]
  · have e : unitC c = conj c / (‖c‖ : ℂ) := by simp [unitC, hc]
    rw [e, norm_div, RCLike.norm_conj, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 hc)]

lemma measurable_unitC : Measurable unitC := by
  unfold unitC
  exact Measurable.ite (measurableSet_singleton 0) measurable_const
    (Complex.continuous_conj.measurable.div (Complex.measurable_ofReal.comp measurable_norm))

lemma integrableOn_inv_sq_norm_zeroModeH (ham : Measurable a') (hai : Integrable a') :
    IntegrableOn (fun y : ℝ => (y ^ 2)⁻¹ * ‖zeroModeH a' y‖) (Ioi 0) := by
  have h0 : Integrable fun z : ℍ => powIm 0 (z : ℂ) * a' z := by
    refine hai.congr (Eventually.of_forall fun z => ?_)
    show a' z = powIm 0 (z : ℂ) * a' z
    rw [powIm_zero, one_mul]
  have h1 : IntegrableOn (fun y : ℝ => ‖((y ^ 2)⁻¹ : ℝ) • (powR 0 y * zeroModeH a' y)‖) (Ioi 0) :=
    (integrableOn_powR_zeroModeH ham 0 h0).norm
  refine h1.congr_fun (fun y _ => ?_) measurableSet_Ioi
  show ‖((y ^ 2)⁻¹ : ℝ) • (powR 0 y * zeroModeH a' y)‖ = (y ^ 2)⁻¹ * ‖zeroModeH a' y‖
  rw [norm_smul, Real.norm_of_nonneg (by positivity), norm_mul, norm_powR]
  simp

/-- **The slice inequality**, bounded `g ≥ 0`. -/
theorem slice_norm_le_bdd (hα : 0 < α) (hd : ModData h h₀) (ham : Measurable a') (hai : Integrable a')
    (ha : a' =ᵐ[volume] ampMod α hα.le hd.test) {g : ℍ → ℝ} (hgm : Measurable g) (hg0 : ∀ z, 0 ≤ g z) {M : ℝ}
    (hgb : ∀ z, g z ≤ M) (hgper : ∀ (n : ℤ) (z : ℍ), g (transGL (n : ℝ) • z) = g z) :
    IntegrableOn (fun y : ℝ => (y ^ 2)⁻¹ * ‖zeroModeH a' y‖ * ∫ s in (0 : ℝ)..1, g (ptH s y)) (Ioi 0) ∧
    ∫ y in Ioi (0 : ℝ), (y ^ 2)⁻¹ * ‖zeroModeH a' y‖ * ∫ s in (0 : ℝ)..1, g (ptH s y) ≤ ∫ z : ℍ, ‖a' z‖ * g z := by
  have hzm := measurable_zeroModeH ham
  have hM0 : 0 ≤ M := (hg0 UpperHalfPlane.I).trans (hgb _)
  set E : ℍ → ℂ := fun z => (g z : ℂ) * unitC (zeroModeH a' z.im) with hE
  have hEm : Measurable E :=
    (Complex.measurable_ofReal.comp hgm).mul
      (measurable_unitC.comp (hzm.comp UpperHalfPlane.continuous_im.measurable))
  have hEn : ∀ z, ‖E z‖ ≤ g z := by
    intro z
    show ‖(g z : ℂ) * unitC (zeroModeH a' z.im)‖ ≤ g z
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hg0 z)]
    exact mul_le_of_le_one_right (hg0 z) (norm_unitC_le _)
  have hEb : ∀ z, ‖E z‖ ≤ M := fun z => (hEn z).trans (hgb z)
  have hEper : ∀ (n : ℤ) (z : ℍ), E (transGL (n : ℝ) • z) = E z := by
    intro n z
    show (g (transGL (n : ℝ) • z) : ℂ) * unitC (zeroModeH a' (transGL (n : ℝ) • z).im) = _
    rw [hgper, im_transGL_smul]
  have hJ0 := integral_amp_mul_slice hα hd ham hai ha hEm hEb hEper
  -- the real mean
  have hgm' : Measurable fun y : ℝ => ∫ s in (0 : ℝ)..1, g (ptH s y) := by
    have e : (fun y : ℝ => ∫ s in (0 : ℝ)..1, g (ptH s y)) = fun y : ℝ => ∫ s in Ioc (0 : ℝ) 1, g (ptH s y) := by
      funext y
      rw [intervalIntegral.integral_of_le zero_le_one]
    rw [e]
    have hj : Measurable fun p : ℝ × ℝ => g (ptH p.2 p.1) := hgm.comp measurable_ptH
    exact (hj.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioc (0 : ℝ) 1))).measurable
  have hmb : ∀ y : ℝ, 0 ≤ ∫ s in (0 : ℝ)..1, g (ptH s y) ∧ ∫ s in (0 : ℝ)..1, g (ptH s y) ≤ M := by
    intro y
    refine ⟨intervalIntegral.integral_nonneg zero_le_one fun s _ => hg0 _, ?_⟩
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
      (f := fun s => g (ptH s y)) (C := M) (fun s _ => by
        rw [Real.norm_of_nonneg (hg0 _)]
        exact hgb _)
    have h2 := le_abs_self (∫ s in (0 : ℝ)..1, g (ptH s y))
    rw [Real.norm_eq_abs] at this
    simpa using h2.trans this
  have hρ := integrableOn_inv_sq_norm_zeroModeH ham hai
  have hRi : IntegrableOn (fun y : ℝ => (y ^ 2)⁻¹ * ‖zeroModeH a' y‖ * ∫ s in (0 : ℝ)..1, g (ptH s y)) (Ioi 0) := by
    refine (hρ.mul_const M).mono' ((((measurable_id.pow_const 2).inv.mul hzm.norm).mul hgm').aestronglyMeasurable)
      (Eventually.of_forall fun y => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (by positivity) (hmb y).1)]
    exact mul_le_mul_of_nonneg_left (hmb y).2 (by positivity)
  refine ⟨hRi, ?_⟩
  -- the identity
  have hval : ∫ z : ℍ, a' z * E z
      = ((∫ y in Ioi (0 : ℝ), (y ^ 2)⁻¹ * ‖zeroModeH a' y‖ * ∫ s in (0 : ℝ)..1, g (ptH s y) : ℝ) : ℂ) := by
    rw [hJ0, ← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
    have hy0 : (0 : ℝ) < y := hy
    have e1 : ∫ s in (0 : ℝ)..1, E (ptH s y)
        = ((∫ s in (0 : ℝ)..1, g (ptH s y) : ℝ) : ℂ) * unitC (zeroModeH a' y) := by
      have e2 : ∀ s : ℝ, E (ptH s y) = (g (ptH s y) : ℂ) * unitC (zeroModeH a' y) := by
        intro s
        show (g (ptH s y) : ℂ) * unitC (zeroModeH a' (ptH s y).im) = _
        rw [ptH_im hy0]
      simp_rw [e2]
      rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal]
    show ((y ^ 2)⁻¹ : ℝ) • (zeroModeH a' y * ∫ s in (0 : ℝ)..1, E (ptH s y)) = _
    rw [e1, Complex.real_smul, mul_left_comm (zeroModeH a' y), mul_unitC]
    push_cast
    ring
  have h1 : ‖∫ z : ℍ, a' z * E z‖ ≤ ∫ z : ℍ, ‖a' z‖ * g z := by
    refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
      (Eventually.of_forall fun z => norm_nonneg _) ?_ (Eventually.of_forall fun z => ?_))
    · exact (hai.norm.mul_const M).mono' (ham.norm.mul hgm).aestronglyMeasurable (Eventually.of_forall fun z => by
        rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (hg0 z))]
        exact mul_le_mul_of_nonneg_left (hgb z) (norm_nonneg _))
    · show ‖a' z * E z‖ ≤ ‖a' z‖ * g z
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hEn z) (norm_nonneg _)
  rw [hval, Complex.norm_real, Real.norm_eq_abs] at h1
  exact (le_abs_self _).trans h1

lemma iSup_ofReal_min (x : ℝ) : ⨆ n : ℕ, ENNReal.ofReal (min x n) = ENNReal.ofReal x := by
  refine le_antisymm (iSup_le fun n => ENNReal.ofReal_le_ofReal (min_le_left _ _)) ?_
  obtain ⟨n, hn⟩ := exists_nat_ge x
  refine le_iSup_of_le n ?_
  rw [min_eq_left hn]

/-- **The slice inequality**, `g ≥ 0`. -/
theorem slice_lintegral_le (hα : 0 < α) (hd : ModData h h₀) (ham : Measurable a') (hai : Integrable a')
    (ha : a' =ᵐ[volume] ampMod α hα.le hd.test) {g : ℍ → ℝ} (hgm : Measurable g) (hg0 : ∀ z, 0 ≤ g z)
    (hgper : ∀ (n : ℤ) (z : ℍ), g (transGL (n : ℝ) • z) = g z) :
    ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal ((y ^ 2)⁻¹ * ‖zeroModeH a' y‖)
        * ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (g (ptH s y))
      ≤ ∫⁻ z : ℍ, ENNReal.ofReal (‖a' z‖ * g z) := by
  have hzm := measurable_zeroModeH ham
  have hgnm : ∀ n : ℕ, Measurable fun z : ℍ => min (g z) (n : ℝ) := fun n => hgm.min measurable_const
  have hgn0 : ∀ (n : ℕ) (z : ℍ), 0 ≤ min (g z) (n : ℝ) := fun n z => le_min (hg0 z) (Nat.cast_nonneg n)
  have hgnb : ∀ (n : ℕ) (z : ℍ), min (g z) (n : ℝ) ≤ n := fun n z => min_le_right _ _
  have hgnper : ∀ (n : ℕ) (k : ℤ) (z : ℍ), min (g (transGL (k : ℝ) • z)) (n : ℝ) = min (g z) (n : ℝ) := fun n k z => by
    rw [hgper]
  have hjm : ∀ n : ℕ, Measurable fun p : ℝ × ℝ => ENNReal.ofReal (min (g (ptH p.2 p.1)) (n : ℝ)) := fun n =>
    ENNReal.measurable_ofReal.comp ((hgnm n).comp measurable_ptH)
  have hXm : ∀ n : ℕ, Measurable fun y : ℝ => ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (min (g (ptH s y)) (n : ℝ)) :=
    fun n => (hjm n).lintegral_prod_right'
  have hmono : ∀ (y : ℝ) (n m : ℕ), n ≤ m →
      ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (min (g (ptH s y)) (n : ℝ))
        ≤ ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (min (g (ptH s y)) (m : ℝ)) := by
    intro y n m hnm
    refine lintegral_mono fun s => ENNReal.ofReal_le_ofReal ?_
    exact min_le_min le_rfl (by exact_mod_cast hnm)
  have hXsup : ∀ y : ℝ, ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (g (ptH s y))
      = ⨆ n : ℕ, ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (min (g (ptH s y)) (n : ℝ)) := by
    intro y
    have h1 := lintegral_iSup (μ := volume.restrict (Ioc (0 : ℝ) 1))
      (f := fun (n : ℕ) (s : ℝ) => ENNReal.ofReal (min (g (ptH s y)) (n : ℝ)))
      (fun n => (hjm n).comp measurable_prodMk_left)
      (fun n m hnm s => ENNReal.ofReal_le_ofReal (min_le_min le_rfl (by exact_mod_cast hnm)))
    rw [← h1]
    exact lintegral_congr fun s => (iSup_ofReal_min _).symm
  -- each term
  have hterm : ∀ n : ℕ, ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal ((y ^ 2)⁻¹ * ‖zeroModeH a' y‖)
        * ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (min (g (ptH s y)) (n : ℝ))
      ≤ ∫⁻ z : ℍ, ENNReal.ofReal (‖a' z‖ * g z) := by
    intro n
    obtain ⟨hRi, hle⟩ := slice_norm_le_bdd hα hd ham hai ha (hgnm n) (hgn0 n) (hgnb n) (hgnper n)
    have hXv : ∀ y : ℝ, ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (min (g (ptH s y)) (n : ℝ))
        = ENNReal.ofReal (∫ s in (0 : ℝ)..1, min (g (ptH s y)) (n : ℝ)) := by
      intro y
      rw [intervalIntegral.integral_of_le zero_le_one]
      have hi : Integrable (fun s : ℝ => min (g (ptH s y)) (n : ℝ)) (volume.restrict (Ioc (0 : ℝ) 1)) := by
        refine (integrable_const (n : ℝ)).mono'
          (((hgnm n).comp (measurable_ptH.comp measurable_prodMk_left)).aestronglyMeasurable)
          (Eventually.of_forall fun s => ?_)
        rw [Real.norm_of_nonneg (hgn0 n _)]
        exact hgnb n _
      exact (ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun s => hgn0 n _)).symm
    have h1 : ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal ((y ^ 2)⁻¹ * ‖zeroModeH a' y‖)
          * ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (min (g (ptH s y)) (n : ℝ))
        = ENNReal.ofReal (∫ y in Ioi (0 : ℝ), (y ^ 2)⁻¹ * ‖zeroModeH a' y‖
            * ∫ s in (0 : ℝ)..1, min (g (ptH s y)) (n : ℝ)) := by
      rw [ofReal_integral_eq_lintegral_ofReal hRi (Eventually.of_forall fun y =>
        mul_nonneg (by positivity) (intervalIntegral.integral_nonneg zero_le_one fun s _ => hgn0 n _))]
      refine lintegral_congr fun y => ?_
      rw [hXv, ← ENNReal.ofReal_mul (by positivity)]
    have hi2 : Integrable fun z : ℍ => ‖a' z‖ * min (g z) (n : ℝ) :=
      (hai.norm.mul_const (n : ℝ)).mono' (ham.norm.mul (hgnm n)).aestronglyMeasurable
        (Eventually.of_forall fun z => by
          rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (hgn0 n z))]
          exact mul_le_mul_of_nonneg_left (hgnb n z) (norm_nonneg _))
    have h2 : ENNReal.ofReal (∫ z : ℍ, ‖a' z‖ * min (g z) (n : ℝ))
        = ∫⁻ z : ℍ, ENNReal.ofReal (‖a' z‖ * min (g z) (n : ℝ)) :=
      ofReal_integral_eq_lintegral_ofReal hi2 (Eventually.of_forall fun z => mul_nonneg (norm_nonneg _) (hgn0 n z))
    rw [h1]
    refine (ENNReal.ofReal_le_ofReal hle).trans ?_
    rw [h2]
    exact lintegral_mono fun z =>
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (min_le_left _ _) (norm_nonneg _))
  -- monotone convergence
  have h3 := lintegral_iSup (μ := volume.restrict (Ioi (0 : ℝ)))
    (f := fun (n : ℕ) (y : ℝ) => ENNReal.ofReal ((y ^ 2)⁻¹ * ‖zeroModeH a' y‖)
      * ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (min (g (ptH s y)) (n : ℝ)))
    (fun n => (ENNReal.measurable_ofReal.comp ((measurable_id.pow_const 2).inv.mul hzm.norm)).mul (hXm n))
    (fun n m hnm y => mul_le_mul' le_rfl (hmono y n m hnm))
  have hLHS : ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal ((y ^ 2)⁻¹ * ‖zeroModeH a' y‖)
        * ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (g (ptH s y))
      = ⨆ n : ℕ, ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal ((y ^ 2)⁻¹ * ‖zeroModeH a' y‖)
        * ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (min (g (ptH s y)) (n : ℝ)) := by
    rw [← h3]
    refine lintegral_congr fun y => ?_
    rw [hXsup, ENNReal.mul_iSup]
  rw [hLHS]
  exact iSup_le hterm

/-- **The mean lemma in slice form**, for `a' E ∈ L¹(ℍ)`. -/
theorem integral_amp_mul_slice_L1 (hα : 0 < α) (hd : ModData h h₀) (ham : Measurable a') (hai : Integrable a')
    (ha : a' =ᵐ[volume] ampMod α hα.le hd.test) {E : ℍ → ℂ} (hEm : Measurable E)
    (hEper : ∀ (n : ℤ) (z : ℍ), E (transGL (n : ℝ) • z) = E z) (hint : Integrable fun z : ℍ => a' z * E z) :
    ∫ z : ℍ, a' z * E z
      = ∫ y in Ioi (0 : ℝ), ((y ^ 2)⁻¹ : ℝ) • (zeroModeH a' y * ∫ s in (0 : ℝ)..1, E (ptH s y)) := by
  have hzm := measurable_zeroModeH ham
  set En : ℕ → ℍ → ℂ := fun n z => if ‖E z‖ ≤ (n : ℝ) then E z else 0 with hEn
  have hEnm : ∀ n, Measurable (En n) := fun n =>
    Measurable.ite (measurableSet_le hEm.norm measurable_const) hEm measurable_const
  have hEnb : ∀ (n : ℕ) (z : ℍ), ‖En n z‖ ≤ n := by
    intro n z
    by_cases hc : ‖E z‖ ≤ (n : ℝ)
    · have e : En n z = E z := by simp [hEn, hc]
      rw [e]
      exact hc
    · have e : En n z = 0 := by simp [hEn, hc]
      rw [e, norm_zero]
      exact Nat.cast_nonneg n
  have hEnle : ∀ (n : ℕ) (z : ℍ), ‖En n z‖ ≤ ‖E z‖ := by
    intro n z
    by_cases hc : ‖E z‖ ≤ (n : ℝ)
    · have e : En n z = E z := by simp [hEn, hc]
      rw [e]
    · have e : En n z = 0 := by simp [hEn, hc]
      rw [e, norm_zero]
      exact norm_nonneg _
  have hEnper : ∀ (n : ℕ) (k : ℤ) (z : ℍ), En n (transGL (k : ℝ) • z) = En n z := fun n k z => by
    show (if ‖E (transGL (k : ℝ) • z)‖ ≤ (n : ℝ) then E (transGL (k : ℝ) • z) else 0) = _
    rw [hEper]
  have hEnev : ∀ z : ℍ, ∀ᶠ n : ℕ in atTop, En n z = E z := by
    intro z
    obtain ⟨N, hN⟩ := exists_nat_ge ‖E z‖
    filter_upwards [eventually_ge_atTop N] with n hn
    have hc : ‖E z‖ ≤ (n : ℝ) := hN.trans (by exact_mod_cast hn)
    simp [hEn, hc]
  have hJ0 := fun n => integral_amp_mul_slice hα hd ham hai ha (hEnm n) (hEnb n) (hEnper n)
  -- the left side
  have hL : Tendsto (fun n : ℕ => ∫ z : ℍ, a' z * En n z) atTop (𝓝 (∫ z : ℍ, a' z * E z)) := by
    refine tendsto_integral_of_dominated_convergence (fun z => ‖a' z * E z‖)
      (fun n => (ham.mul (hEnm n)).aestronglyMeasurable) hint.norm
      (fun n => Eventually.of_forall fun z => ?_) (Eventually.of_forall fun z => ?_)
    · rw [norm_mul, norm_mul]
      exact mul_le_mul_of_nonneg_left (hEnle n z) (norm_nonneg _)
    · refine Tendsto.congr' ((hEnev z).mono fun n hn => ?_) tendsto_const_nhds
      show a' z * E z = a' z * En n z
      rw [hn]
  -- the domination
  have hJ2 := slice_lintegral_le hα hd ham hai ha hEm.norm (fun z => norm_nonneg _) (fun n z => by rw [hEper])
  have hfin : ∫⁻ z : ℍ, ENNReal.ofReal (‖a' z‖ * ‖E z‖) < ⊤ := by
    have h1 : ∫⁻ z : ℍ, ENNReal.ofReal (‖a' z‖ * ‖E z‖) = ∫⁻ z : ℍ, ‖a' z * E z‖ₑ :=
      lintegral_congr fun z => by rw [← norm_mul, ofReal_norm]
    rw [h1]
    exact hint.2
  set B : ℝ → ℝ≥0∞ := fun y => ENNReal.ofReal ((y ^ 2)⁻¹ * ‖zeroModeH a' y‖)
    * ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal ‖E (ptH s y)‖ with hB
  have hjm : Measurable fun p : ℝ × ℝ => ENNReal.ofReal ‖E (ptH p.2 p.1)‖ :=
    ENNReal.measurable_ofReal.comp (hEm.norm.comp measurable_ptH)
  have hBm : Measurable B :=
    (ENNReal.measurable_ofReal.comp ((measurable_id.pow_const 2).inv.mul hzm.norm)).mul hjm.lintegral_prod_right'
  have hBfin : ∫⁻ y in Ioi (0 : ℝ), B y ≠ ⊤ := (hJ2.trans_lt hfin).ne
  have hBae : ∀ᵐ y ∂(volume.restrict (Ioi (0 : ℝ))), B y < ⊤ := ae_lt_top hBm hBfin
  have hBint : Integrable (fun y => (B y).toReal) (volume.restrict (Ioi (0 : ℝ))) :=
    integrable_toReal_of_lintegral_ne_top hBm.aemeasurable hBfin
  -- pointwise
  have key : ∀ y : ℝ, B y < ⊤ →
      (∀ n : ℕ, ‖((y ^ 2)⁻¹ : ℝ) • (zeroModeH a' y * ∫ s in (0 : ℝ)..1, En n (ptH s y))‖ ≤ (B y).toReal) ∧
      Tendsto (fun n : ℕ => ((y ^ 2)⁻¹ : ℝ) • (zeroModeH a' y * ∫ s in (0 : ℝ)..1, En n (ptH s y))) atTop
        (𝓝 (((y ^ 2)⁻¹ : ℝ) • (zeroModeH a' y * ∫ s in (0 : ℝ)..1, E (ptH s y)))) := by
    intro y hBy
    by_cases h0 : zeroModeH a' y = 0
    · refine ⟨fun n => ?_, ?_⟩
      · rw [h0, zero_mul, smul_zero, norm_zero]
        exact ENNReal.toReal_nonneg
      · simp only [h0, zero_mul, smul_zero]
        exact tendsto_const_nhds
    · have hc0 : 0 ≤ (y ^ 2)⁻¹ * ‖zeroModeH a' y‖ := by positivity
      have hI : ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal ‖E (ptH s y)‖ < ⊤ := by
        rcases ENNReal.mul_lt_top_iff.1 hBy with ⟨-, h2⟩ | h2 | h2
        · exact h2
        · exfalso
          have hy : 0 < y := by
            by_contra hny
            exact h0 (by simp [zeroModeH, hny])
          have : 0 < (y ^ 2)⁻¹ * ‖zeroModeH a' y‖ := mul_pos (by positivity) (norm_pos_iff.2 h0)
          rw [ENNReal.ofReal_eq_zero] at h2
          linarith
        · rw [h2]
          exact ENNReal.zero_lt_top
      have hsm : Measurable fun s : ℝ => E (ptH s y) := hEm.comp (measurable_ptH.comp measurable_prodMk_left)
      have hsI : Integrable (fun s : ℝ => E (ptH s y)) (volume.restrict (Ioc (0 : ℝ) 1)) := by
        refine ⟨hsm.aestronglyMeasurable, ?_⟩
        have e : ∫⁻ s in Ioc (0 : ℝ) 1, ‖E (ptH s y)‖ₑ = ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal ‖E (ptH s y)‖ :=
          lintegral_congr fun s => (ofReal_norm _).symm
        show ∫⁻ s in Ioc (0 : ℝ) 1, ‖E (ptH s y)‖ₑ < ⊤
        rw [e]
        exact hI
      have hsn : ∀ n : ℕ, Measurable fun s : ℝ => En n (ptH s y) := fun n =>
        (hEnm n).comp (measurable_ptH.comp measurable_prodMk_left)
      have hval : (B y).toReal = (y ^ 2)⁻¹ * ‖zeroModeH a' y‖ * ∫ s in Ioc (0 : ℝ) 1, ‖E (ptH s y)‖ := by
        rw [hB, ENNReal.toReal_mul, ENNReal.toReal_ofReal hc0,
          integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun s => norm_nonneg _) hsm.norm.aestronglyMeasurable]
      refine ⟨fun n => ?_, ?_⟩
      · rw [hval, norm_smul, Real.norm_of_nonneg (by positivity), norm_mul, ← mul_assoc,
          intervalIntegral.integral_of_le zero_le_one]
        refine mul_le_mul_of_nonneg_left ?_ hc0
        exact norm_integral_le_of_norm_le hsI.norm (Eventually.of_forall fun s => hEnle n _)
      · have ht : Tendsto (fun n : ℕ => ∫ s in Ioc (0 : ℝ) 1, En n (ptH s y)) atTop
            (𝓝 (∫ s in Ioc (0 : ℝ) 1, E (ptH s y))) := by
          refine tendsto_integral_of_dominated_convergence (fun s => ‖E (ptH s y)‖)
            (fun n => (hsn n).aestronglyMeasurable) hsI.norm
            (fun n => Eventually.of_forall fun s => hEnle n _) (Eventually.of_forall fun s => ?_)
          refine Tendsto.congr' ((hEnev (ptH s y)).mono fun n hn => ?_) tendsto_const_nhds
          show E (ptH s y) = En n (ptH s y)
          rw [hn]
        simp_rw [intervalIntegral.integral_of_le zero_le_one]
        exact (ht.const_mul _).const_smul _
  -- the right side
  have hR : Tendsto (fun n : ℕ => ∫ y in Ioi (0 : ℝ),
        ((y ^ 2)⁻¹ : ℝ) • (zeroModeH a' y * ∫ s in (0 : ℝ)..1, En n (ptH s y))) atTop
      (𝓝 (∫ y in Ioi (0 : ℝ), ((y ^ 2)⁻¹ : ℝ) • (zeroModeH a' y * ∫ s in (0 : ℝ)..1, E (ptH s y)))) := by
    refine tendsto_integral_of_dominated_convergence (fun y => (B y).toReal)
      (fun n => ((measurable_id.pow_const 2).inv.smul
        (hzm.mul (measurable_sliceMean (hEnm n)))).aestronglyMeasurable) hBint (fun n => ?_) ?_
    · filter_upwards [hBae] with y hBy
      exact (key y hBy).1 n
    · filter_upwards [hBae] with y hBy
      exact (key y hBy).2
  have hR' : Tendsto (fun n : ℕ => ∫ z : ℍ, a' z * En n z) atTop
      (𝓝 (∫ y in Ioi (0 : ℝ), ((y ^ 2)⁻¹ : ℝ) • (zeroModeH a' y * ∫ s in (0 : ℝ)..1, E (ptH s y)))) := by
    simp_rw [hJ0]
    exact hR
  exact tendsto_nhds_unique hL hR'

end Qschubert
