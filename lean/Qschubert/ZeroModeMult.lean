import Qschubert.ZeroModeBounds

/-!
# The zero-mode multiplier identity

Stage Z of the plan for Proposition `ev:mod` (`lean/BLUEPRINT.md`). For a test function `h`, `0 < α ≤ 1`,
`u = e^{-αΛ} h` (as `specE.integral (GW 0 α) (toL2 h)`) and `0 ≤ Re w ≤ 1/2`:

`∫_ℍ y^w u dν = (∫ gTau α r · cosh((w - 1/2) r) dr) · ∫_ℍ y^w h dν` (`zeroMode_mult`),

where `gTau α` is the subordination kernel of `e^{-αΛ}` to the wave group (`gTau_symbol`). In terms of the zero mode
`u₀(y) = ∫ u(x + iy) dx` this says `û₀(s) = m(s) ĥ₀(s)` on `1/2 ≤ Re s ≤ 1` (`s = 1 - w`), and on the critical line
`m(1/2 + iρ) = e^{-α √(1/4 + ρ²)}` (`zeroMode_mult_critical`).

Proof. Pair `u` with `χ_S y^{conj w}`, `S = e^{a+n}`, where `h` vanishes outside `{ψ ≤ a}`. By `pair_superpose` the
pairing is `∫ gTau α r ⟪χ_S y^{conj w}, cos(rD) h⟫ dr`, and for `|r| < n` the inner pairing is `cosh((w-1/2) r) ∫ y^w h`
(`pair_powCut_cosD`). The rest is at most `‖χ_S y^{conj w}‖ ‖h‖ ∫_{|r| ≥ n} |gTau| + |∫ y^w h| ∫_{|r| ≥ n} |gTau| e^{|r|/2}`,
which tends to `0`: the first term is `O((1 + n)^{-1/2})` by `norm_toL2_powCut_sq_le` and the tail of `gTau`.
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set Physicslib4.Spectral Physicslib4.Spectral.Unbounded
open scoped ENNReal InnerProductSpace ComplexConjugate UpperHalfPlane Real

local notation "L2H'" => Lp ℂ 2 (volume : Measure UpperHalfPlane)

lemma conj_powIm (w : ℂ) (z : ℂ) : conj (powIm (conj w) z) = powIm w z := by
  rw [powIm, powR, powIm, powR, ← Complex.exp_conj, map_mul, Complex.conj_conj, Complex.conj_ofReal]

lemma conj_cutS (S : ℝ) (z : ℂ) : conj (cutS S z) = cutS S z := by
  unfold cutS
  split_ifs <;> simp [Complex.conj_ofReal]

/-- `⟪χ_S y^{conj w}, x⟫ = ∫ χ_S y^w x dν`. -/
lemma inner_powCut {S : ℝ} (hS : 0 < S) (w : ℂ) (x : L2H') :
    ⟪toL2 (powCut S hS (conj w)), x⟫_ℂ = ∫ z : UpperHalfPlane, cutS S (z : ℂ) * (powIm w (z : ℂ) * x z) := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [toL2_ae (powCut S hS (conj w))] with z ez
  rw [ez, powCut_coe, powCutFun, RCLike.inner_apply, map_mul, conj_powIm, conj_cutS]
  ring

lemma norm_cosh_le (k : ℂ) (hk : |k.re| ≤ 1 / 2) (r : ℝ) : ‖Complex.cosh (k * r)‖ ≤ Real.exp (|r| / 2) := by
  have hre : (k * (r : ℂ)).re = k.re * r := by simp
  have h1 : |k.re * r| ≤ |r| / 2 := by
    rw [abs_mul]
    nlinarith [abs_nonneg r]
  rw [Complex.cosh]
  calc ‖(Complex.exp (k * r) + Complex.exp (-(k * r))) / 2‖
      ≤ (‖Complex.exp (k * r)‖ + ‖Complex.exp (-(k * r))‖) / 2 := by
        rw [norm_div, Complex.norm_ofNat]
        exact div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num)
    _ = (Real.exp (k.re * r) + Real.exp (-(k.re * r))) / 2 := by
        rw [Complex.norm_exp, Complex.norm_exp, Complex.neg_re, hre]
    _ ≤ (Real.exp (|r| / 2) + Real.exp (|r| / 2)) / 2 := by
        have a1 : Real.exp (k.re * r) ≤ Real.exp (|r| / 2) := Real.exp_le_exp.2 ((le_abs_self _).trans h1)
        have a2 : Real.exp (-(k.re * r)) ≤ Real.exp (|r| / 2) := Real.exp_le_exp.2 ((neg_le_abs _).trans h1)
        linarith
    _ = Real.exp (|r| / 2) := by ring

/-- **The zero-mode multiplier identity.** -/
theorem zeroMode_mult {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (h : testFn) {w : ℂ} (hw0 : 0 ≤ w.re) (hw1 : w.re ≤ 1 / 2) :
    Integrable (fun z : UpperHalfPlane => powIm w (z : ℂ) * (specE.integral (GW 0 α) (toL2 h) : L2H') z)
      ∧ Integrable (fun r : ℝ => (gTau α r : ℂ) * Complex.cosh ((w - 1 / 2) * r))
      ∧ ∫ z : UpperHalfPlane, powIm w (z : ℂ) * (specE.integral (GW 0 α) (toL2 h) : L2H') z
        = (∫ r : ℝ, (gTau α r : ℂ) * Complex.cosh ((w - 1 / 2) * r))
          * ∫ z : UpperHalfPlane, powIm w (z : ℂ) * (h : ℂ → ℂ) z := by
  set f : L2H' := toL2 h with hf
  set u : L2H' := specE.integral (GW 0 α) f with hu
  set g : ℝ → ℝ := gTau α with hg
  set k : ℂ := w - 1 / 2 with hk
  have hc1 : (1 / 2 : ℝ) < 3 / 4 := by norm_num
  have hc2 : (3 / 4 : ℝ) < 1 := by norm_num
  -- the kernel
  have hgi : Integrable g := integrable_of_symbol (gTau_symbol hα le_rfl).1
  have hgT := gTau_TailB hα
  set B : ℝ := 4 * Real.sqrt 2 * (α / (2 * (α / 2))) + 2 * α / Real.sqrt π * (2 * Real.sqrt 2) with hB
  have hrep : ∀ x, 1 / 4 ≤ x → ∫ r, (g r : ℂ) * ((Real.cos (r * √(yD x)) : ℝ) : ℂ) = GW 0 α x := fun x hx => by
    have hx0 : 0 ≤ x := by linarith
    refine rep_of_real (R := Real.exp (-(α * √x))) ?_ (gTau_symbol hα hx).2
    simp [GW, rW, hx0]
  have hge : Integrable fun r => |g r| * Real.exp (|r| / 2) := tail_exp_integrable hgi hgT
  have hkre : |k.re| ≤ 1 / 2 := by
    have : k.re = w.re - 1 / 2 := by simp [hk]
    rw [this, abs_le]
    constructor <;> linarith
  have hgc : Integrable fun r : ℝ => (g r : ℂ) * Complex.cosh (k * r) := by
    refine hge.mono' ((Complex.continuous_ofReal.comp_aestronglyMeasurable hgi.1).mul
      (by fun_prop : Continuous fun r : ℝ => Complex.cosh (k * r)).aestronglyMeasurable) (Eventually.of_forall fun r => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (norm_cosh_le k hkre r) (abs_nonneg _)
  -- weighted bounds
  obtain ⟨K, hK, hp⟩ := poisson_cw hc1 hc2
  have hfw := lintegral_omC_test_lt_top (c := 3 / 4) (by norm_num) h
  have huw : ∫⁻ z : UpperHalfPlane, ENNReal.ofReal (omC (3 / 4) (z : ℂ) ^ 2 * ‖u z‖ ^ 2) < ∞ :=
    (hp α hα hα1 f).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfw)
  have hiu : Integrable fun z : UpperHalfPlane => powIm w (z : ℂ) * u z := integrable_powIm_mul hc1 hw0 hw1 u huw
  have hif : Integrable fun z : UpperHalfPlane => powIm w (z : ℂ) * f z := integrable_powIm_mul hc1 hw0 hw1 f hfw
  set M₀ : ℂ := ∫ z : UpperHalfPlane, powIm w (z : ℂ) * (h : ℂ → ℂ) z with hM₀
  have hM₀f : ∫ z : UpperHalfPlane, powIm w (z : ℂ) * f z = M₀ := by
    refine integral_congr_ae ?_
    filter_upwards [toL2_ae h] with z ez
    rw [ez]
  refine ⟨hiu, hgc, ?_⟩
  -- the support of `h`
  obtain ⟨a, ha, hsupp⟩ := exists_psiF_bound h
  have hfa : ∀ᵐ z : UpperHalfPlane, f z ≠ 0 → psiF (z : ℂ) ≤ a := by
    filter_upwards [toL2_ae h] with z ez hz
    exact hsupp z (ez ▸ hz)
  -- the cutoffs
  set S : ℕ → ℝ := fun n => Real.exp (a + n) with hSd
  have hS0 : ∀ n, 0 < S n := fun n => Real.exp_pos _
  have hS1 : ∀ n, 1 ≤ S n := fun n => Real.one_le_exp (by positivity)
  set I : ℕ → ℂ := fun n => ⟪toL2 (powCut (S n) (hS0 n) (conj w)), u⟫_ℂ with hI
  -- the left side converges
  have hlim1 : Tendsto I atTop (𝓝 (∫ z : UpperHalfPlane, powIm w (z : ℂ) * u z)) := by
    simp only [hI, inner_powCut]
    refine tendsto_integral_of_dominated_convergence (fun z : UpperHalfPlane => ‖powIm w (z : ℂ) * u z‖)
      (fun n => ?_) hiu.norm (fun n => Eventually.of_forall fun z => ?_) (Eventually.of_forall fun z => ?_)
    · exact (((contDiff_cutS (hS0 n)).continuous.comp UpperHalfPlane.continuous_coe).aestronglyMeasurable).mul hiu.1
    · rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (norm_cutS_le_one _ _)
    · refine tendsto_const_nhds.congr' ?_
      have hev : ∀ᶠ n : ℕ in atTop, gH (z : ℂ) < S n := by
        have ht : Tendsto S atTop atTop :=
          Real.tendsto_exp_atTop.comp (tendsto_atTop_add_const_left _ a tendsto_natCast_atTop_atTop)
        exact ht.eventually_gt_atTop _
      filter_upwards [hev] with n hn
      have h1 := (cutT_eventually (hS0 n) z.im_pos hn).1
      rw [cutT_coe] at h1
      rw [h1, one_mul]
  -- the right side: the main term and the error
  have hM : ∀ n : ℕ, 1 ≤ n → ⟪toL2 (powCut (S n) (hS0 n) (conj w)), f⟫_ℂ = M₀ := by
    intro n hn
    rw [inner_powCut, ← hM₀f]
    refine integral_congr_ae ?_
    filter_upwards [toL2_ae h] with z ez
    by_cases hz : (h : ℂ → ℂ) z = 0
    · rw [ez, hz]; simp
    · have h1 : psiF (z : ℂ) < a + n := by
        have := hsupp z hz
        have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
        linarith
      have h2 := gH_lt_of_psiF_lt z.im_pos h1
      have h3 := (cutT_eventually (hS0 n) z.im_pos h2).1
      rw [cutT_coe] at h3
      rw [h3, one_mul]
  have hinner : ∀ (n : ℕ) (r : ℝ), 1 ≤ n → |r| < n →
      ⟪toL2 (powCut (S n) (hS0 n) (conj w)), cosDOp r f⟫_ℂ = Complex.cosh (k * r) * M₀ := by
    intro n r hn hr
    have hr' : |r| < Real.log (S n) - a := by
      rw [hSd, Real.log_exp]
      linarith
    rw [pair_powCut_cosD hfa (hS0 n) (conj w) hr', Complex.conj_conj, hM n hn]
  set G : ℂ := ∫ r : ℝ, (g r : ℂ) * Complex.cosh (k * r) with hG
  set P : ℕ → ℝ := fun n => ‖toL2 (powCut (S n) (hS0 n) (conj w))‖ * ‖f‖ with hP
  set A : ℕ → Set ℝ := fun n => {r : ℝ | (n : ℝ) ≤ |r|} with hA
  have hAm : ∀ n, MeasurableSet (A n) := fun n => measurableSet_le measurable_const continuous_abs.measurable
  have herr : ∀ n : ℕ, 1 ≤ n → ‖I n - G * M₀‖
      ≤ P n * (∫ r in A n, |g r|) + ‖M₀‖ * ∫ r in A n, |g r| * Real.exp (|r| / 2) := by
    intro n hn
    have hmi : Integrable fun r : ℝ => (g r : ℂ) * ⟪toL2 (powCut (S n) (hS0 n) (conj w)), cosDOp r f⟫_ℂ := by
      refine (hgi.abs.mul_const (P n)).mono' ((Complex.continuous_ofReal.comp_aestronglyMeasurable hgi.1).mul
        (measurable_inner_cosDOp _ _).aestronglyMeasurable) (Eventually.of_forall fun r => ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (norm_inner_cosDOp_le _ _ r) (abs_nonneg _)
    have e1 : I n - G * M₀ = ∫ r : ℝ, ((g r : ℂ) * ⟪toL2 (powCut (S n) (hS0 n) (conj w)), cosDOp r f⟫_ℂ
        - (g r : ℂ) * Complex.cosh (k * r) * M₀) := by
      rw [integral_sub hmi (hgc.mul_const M₀), integral_mul_const]
      simp only [hI]
      rw [pair_superpose hgi (GW_mem 0 hα) hrep f]
    rw [e1]
    have hbound : ∀ r : ℝ, ‖(g r : ℂ) * ⟪toL2 (powCut (S n) (hS0 n) (conj w)), cosDOp r f⟫_ℂ
        - (g r : ℂ) * Complex.cosh (k * r) * M₀‖
        ≤ (A n).indicator (fun r => P n * |g r| + ‖M₀‖ * (|g r| * Real.exp (|r| / 2))) r := by
      intro r
      by_cases hr : r ∈ A n
      · rw [Set.indicator_of_mem hr]
        calc _ ≤ ‖(g r : ℂ) * ⟪toL2 (powCut (S n) (hS0 n) (conj w)), cosDOp r f⟫_ℂ‖
              + ‖(g r : ℂ) * Complex.cosh (k * r) * M₀‖ := norm_sub_le _ _
          _ ≤ P n * |g r| + ‖M₀‖ * (|g r| * Real.exp (|r| / 2)) := by
              rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
              have b1 := norm_inner_cosDOp_le (toL2 (powCut (S n) (hS0 n) (conj w))) f r
              have b2 := norm_cosh_le k hkre r
              have b3 : |g r| * ‖⟪toL2 (powCut (S n) (hS0 n) (conj w)), cosDOp r f⟫_ℂ‖ ≤ P n * |g r| := by
                rw [mul_comm]
                exact mul_le_mul_of_nonneg_right b1 (abs_nonneg _)
              have b4 : |g r| * ‖Complex.cosh (k * r)‖ * ‖M₀‖ ≤ ‖M₀‖ * (|g r| * Real.exp (|r| / 2)) := by
                rw [mul_comm]
                exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left b2 (abs_nonneg _)) (norm_nonneg _)
              linarith
      · rw [Set.indicator_of_notMem hr]
        have hr' : |r| < n := not_le.1 hr
        rw [hinner n r hn hr']
        simp [mul_assoc]
    have hbi : Integrable fun r => P n * |g r| + ‖M₀‖ * (|g r| * Real.exp (|r| / 2)) :=
      (hgi.abs.const_mul _).add (hge.const_mul _)
    calc _ ≤ ∫ r, (A n).indicator (fun r => P n * |g r| + ‖M₀‖ * (|g r| * Real.exp (|r| / 2))) r :=
          norm_integral_le_of_norm_le (hbi.indicator (hAm n)) (Eventually.of_forall hbound)
      _ = ∫ r in A n, (P n * |g r| + ‖M₀‖ * (|g r| * Real.exp (|r| / 2))) := integral_indicator (hAm n)
      _ = P n * (∫ r in A n, |g r|) + ‖M₀‖ * ∫ r in A n, |g r| * Real.exp (|r| / 2) := by
          rw [integral_add (hgi.abs.const_mul _).integrableOn (hge.const_mul _).integrableOn, integral_const_mul,
            integral_const_mul]
  -- the two error terms tend to zero
  have hAanti : Antitone A := fun m n hmn r hr => le_trans (by exact_mod_cast hmn) (show (n : ℝ) ≤ |r| from hr)
  have hAint : (⋂ n, A n) = ∅ := by
    ext r
    simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false, not_forall, hA, Set.mem_ofPred_eq, not_le]
    exact exists_nat_gt |r|
  have hE2 : Tendsto (fun n => ‖M₀‖ * ∫ r in A n, |g r| * Real.exp (|r| / 2)) atTop (𝓝 0) := by
    have h1 := tendsto_setIntegral_of_antitone hAm hAanti ⟨0, hge.integrableOn⟩
    rw [hAint, Measure.restrict_empty, integral_zero_measure] at h1
    simpa using h1.const_mul ‖M₀‖
  set J : ℝ := (∫⁻ z : UpperHalfPlane, ENNReal.ofReal (((omC (3 / 4) (z : ℂ))⁻¹) ^ 2 * (1 + z.im))).toReal with hJ
  set A₀ : ℝ := 1 + Real.log 2 + a with hA₀
  have hA₀1 : 1 ≤ A₀ := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    linarith
  set D : ℝ := 2 * Real.exp a * J * A₀ ^ 2 * (‖f‖ * |B|) ^ 2 with hD
  have hE1b : ∀ n : ℕ, P n * ∫ r in A n, |g r| ≤ Real.sqrt (D / (1 + n)) := by
    intro n
    have hn0 : (0 : ℝ) < 1 + n := by positivity
    have hQ := norm_toL2_powCut_sq_le hc1 (hS1 n) (v := conj w) (by simpa using hw0) (by simpa using hw1)
    rw [← hJ] at hQ
    have hlog : Real.log (2 * S n) = Real.log 2 + a + n := by
      rw [Real.log_mul (by norm_num) (hS0 n).ne', hSd, Real.log_exp]
      ring
    have hpow : (1 + Real.log (2 * S n)) ^ (2 * (3 / 4 : ℝ)) ≤ A₀ ^ 2 * (1 + n) ^ 2 := by
      have hb : 1 + Real.log (2 * S n) ≤ A₀ * (1 + n) := by
        rw [hlog, hA₀]
        nlinarith [Nat.cast_nonneg (α := ℝ) n, Real.log_pos (by norm_num : (1 : ℝ) < 2)]
      have hb1 : 1 ≤ 1 + Real.log (2 * S n) := by
        rw [hlog]
        have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
        linarith [Nat.cast_nonneg (α := ℝ) n]
      calc (1 + Real.log (2 * S n)) ^ (2 * (3 / 4 : ℝ)) ≤ (1 + Real.log (2 * S n)) ^ (2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hb1 (by norm_num)
        _ = (1 + Real.log (2 * S n)) ^ 2 := by norm_cast
        _ ≤ (A₀ * (1 + n)) ^ 2 := pow_le_pow_left₀ (by linarith) hb 2
        _ = A₀ ^ 2 * (1 + n) ^ 2 := by ring
    have hJ0 : 0 ≤ J := ENNReal.toReal_nonneg
    have hT := hgT n (Nat.cast_nonneg n)
    have hT' : ∫ r in A n, |g r| ≤ |B| * tF n :=
      hT.trans (mul_le_mul_of_nonneg_right (le_abs_self B) (tF_nonneg (Nat.cast_nonneg n)))
    have hi0 : 0 ≤ ∫ r in A n, |g r| := setIntegral_nonneg (hAm n) fun r _ => abs_nonneg _
    have htF : tF n ^ 2 = Real.exp (-(n : ℝ)) / (1 + n) ^ 3 := by
      have e1 : Real.exp (-(n : ℝ) / 2) ^ 2 = Real.exp (-(n : ℝ)) := by
        rw [sq, ← Real.exp_add]
        congr 1
        ring
      unfold tF
      rw [div_pow, mul_pow, Real.sq_sqrt hn0.le, e1]
      ring
    refine Real.le_sqrt_of_sq_le ?_
    have hP0 : 0 ≤ P n := by positivity
    calc (P n * ∫ r in A n, |g r|) ^ 2 ≤ (P n * (|B| * tF n)) ^ 2 :=
          pow_le_pow_left₀ (mul_nonneg hP0 hi0) (mul_le_mul_of_nonneg_left hT' hP0) 2
      _ = ‖toL2 (powCut (S n) (hS0 n) (conj w))‖ ^ 2 * (‖f‖ * |B|) ^ 2 * tF n ^ 2 := by
          simp only [hP]; ring
      _ ≤ (2 * S n * (A₀ ^ 2 * (1 + n) ^ 2) * J) * (‖f‖ * |B|) ^ 2 * tF n ^ 2 := by
          have h2 : 2 * S n * (1 + Real.log (2 * S n)) ^ (2 * (3 / 4 : ℝ)) * J ≤ 2 * S n * (A₀ ^ 2 * (1 + n) ^ 2) * J :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by have := hS0 n; positivity)) hJ0
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hQ.trans h2) (by positivity)) (by positivity)
      _ = D / (1 + n) := by
          have hSn : S n = Real.exp a * Real.exp n := by
            simp only [hSd]
            rw [Real.exp_add]
          rw [htF, hD, hSn, Real.exp_neg]
          have he : Real.exp (n : ℝ) ≠ 0 := (Real.exp_pos _).ne'
          field_simp
  have hE1 : Tendsto (fun n : ℕ => P n * ∫ r in A n, |g r|) atTop (𝓝 0) := by
    have hD0 : Tendsto (fun n : ℕ => Real.sqrt (D / (1 + n))) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => D / (1 + (n : ℝ))) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_left _ 1 tendsto_natCast_atTop_atTop)
      have h2 := (Real.continuous_sqrt.tendsto 0).comp h1
      rw [Real.sqrt_zero] at h2
      exact h2
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hD0 (fun n => ?_) hE1b
    exact mul_nonneg (by positivity) (setIntegral_nonneg (hAm n) fun r _ => abs_nonneg _)
  have hlim2 : Tendsto I atTop (𝓝 (G * M₀)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hsum := hE1.add hE2
    rw [add_zero] at hsum
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
      (Eventually.of_forall fun n => norm_nonneg _) ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact herr n hn
  exact tendsto_nhds_unique hlim1 hlim2

/-- **The multiplier on the critical line**: `∫_ℍ y^{1/2 - iρ} u dν = e^{-α √(1/4 + ρ²)} ∫_ℍ y^{1/2 - iρ} h dν`. -/
theorem zeroMode_mult_critical {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (h : testFn) (ρ : ℝ) :
    ∫ z : UpperHalfPlane, powIm (1 / 2 - ρ * I) (z : ℂ) * (specE.integral (GW 0 α) (toL2 h) : L2H') z
      = (Real.exp (-(α * Real.sqrt (1 / 4 + ρ ^ 2))) : ℂ)
        * ∫ z : UpperHalfPlane, powIm (1 / 2 - ρ * I) (z : ℂ) * (h : ℂ → ℂ) z := by
  have hw0 : (0 : ℝ) ≤ ((1 / 2 : ℂ) - ρ * I).re := by simp
  have hw1 : ((1 / 2 : ℂ) - ρ * I).re ≤ 1 / 2 := by simp
  rw [(zeroMode_mult hα hα1 h hw0 hw1).2.2]
  congr 1
  have hx : (1 / 4 : ℝ) ≤ 1 / 4 + ρ ^ 2 := by nlinarith [sq_nonneg ρ]
  have hs := (gTau_symbol hα hx).2
  rw [show (1 / 4 : ℝ) + ρ ^ 2 - 1 / 4 = ρ ^ 2 by ring, Real.sqrt_sq_eq_abs] at hs
  rw [← hs, ← integral_complex_ofReal]
  refine integral_congr_ae (Eventually.of_forall fun r => ?_)
  have e : ((1 / 2 : ℂ) - ρ * I - 1 / 2) * (r : ℂ) = ((-(ρ * r) : ℝ) : ℂ) * I := by
    push_cast
    ring
  have hcos : Real.cos (r * |ρ|) = Real.cos (ρ * r) := by
    rcases abs_cases ρ with ⟨h1, _⟩ | ⟨h1, _⟩
    · rw [h1, mul_comm]
    · rw [h1, mul_neg, Real.cos_neg, mul_comm]
  simp only []
  rw [e, Complex.cosh_mul_I, ← Complex.ofReal_cos, Real.cos_neg, hcos]
  push_cast
  ring

end Qschubert
