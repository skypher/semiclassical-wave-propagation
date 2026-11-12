import Qschubert.KLPcCor

/-!
# The printed class at every radius (Corollary `pc:allalpha`)

Theorem `pc:main` is formalized on the range `0 < α ≤ 1/2` (`pcmain_half_smooth`). Its proof uses the amplitude only through the data
`f̃` with `a = e^{-σΛ_m} f̃` and the norm of `f̃` at the critical weight (`dd_core_pc`). For `α > 1/2` the data are obtained from
`f = e^{αΛ} a` by `f₁ = e^{-(α-1/2)Λ} f`, which is bounded at the critical weight for every `α` (`poisson_cw_all`, the semigroup
property and `poisson_cw`), followed by the factorization `data_factor` at the radius `1/2` with `σ = 1/12`.

* `GW_comp`: `e^{-τΛ} e^{-τ'Λ} = e^{-(τ+τ')Λ}`.
* `poisson_cw_all`: `e^{-τΛ}` at the critical weight for `0 < τ ≤ n`, with the constant `K^n`.
* `pcmain_big_smooth`: the estimate of `pc:main` for `1/2 < α ≤ A`, smooth amplitudes.
* `pcMainAt_all`: `PcMainAt Γ x₀ β κ A` for every `A > 0`.
* `expLambda_domain_mono`, `lift1_pr_all`: the `C^∞` representative for every radius.
* `pt_arith_A`, `pccor16bg_coreA`, `pccor16_coreA`: the pointwise corollaries from `PcMainAt` on a range `α ≤ A` with no restriction on `A`.
* `pcmain_all`, `pcthm13_all`, `pccor15_all`, `pccor16bg_all`, `pccor16_all`: the statements for every amplitude of finite printed norm,
  `0 < α ≤ A`.
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set Physicslib4.Spectral Physicslib4.Spectral.Unbounded UpperHalfPlane
open scoped ENNReal InnerProductSpace MatrixGroups Pointwise ComplexConjugate

local notation "L2H'" => Lp ℂ 2 (volume : Measure UpperHalfPlane)

/-- `e^{-τΛ} e^{-τ'Λ} = e^{-(τ+τ')Λ}`. -/
lemma GW_comp {τ τ' : ℝ} (hτ : 0 < τ) (hτ' : 0 < τ') (f : L2H') :
    specE.integral (GW 0 τ) (specE.integral (GW 0 τ') f) = specE.integral (GW 0 (τ + τ')) f := by
  have h1 : specE.integral (GW 0 τ) (specE.integral (GW 0 τ') f) = specE.integral (GW 0 τ * GW 0 τ') f := by
    rw [specE.integral_mul (GW_mem 0 hτ) (GW_mem 0 hτ')]
    rfl
  rw [h1]
  have h2 := integral_congr_nonneg (mul_mem_B (GW_mem 0 hτ) (GW_mem 0 hτ')) (GW_mem 0 (add_pos hτ hτ'))
    (fun s hs => by
      show ((rW 0 τ s : ℝ) : ℂ) * ((rW 0 τ' s : ℝ) : ℂ) = ((rW 0 (τ + τ') s : ℝ) : ℂ)
      unfold rW
      simp only [hs, ite_true, mul_zero, pow_zero, one_mul]
      rw [← Complex.ofReal_mul, ← Real.exp_add]
      congr 2
      ring)
  exact congrArg (fun T : L2H' →L[ℂ] L2H' => T f) h2

/-- **The Poisson semigroup at the critical weight, every time**: for `0 < τ ≤ n` the constant is `K^n`. -/
theorem poisson_cw_all {c : ℝ} (hc1 : 1 / 2 < c) (hc2 : c < 1) : ∃ K : ℝ, 1 ≤ K ∧ ∀ (n : ℕ) (τ : ℝ), 0 < τ → τ ≤ n → ∀ f : L2H',
    ∫⁻ z : UpperHalfPlane, ENNReal.ofReal (omC c (z : ℂ) ^ 2 * ‖specE.integral (GW 0 τ) f z‖ ^ 2)
      ≤ ENNReal.ofReal ((K ^ n) ^ 2) * ∫⁻ z : UpperHalfPlane, ENNReal.ofReal (omC c (z : ℂ) ^ 2 * ‖f z‖ ^ 2) := by
  obtain ⟨K₀, hK₀, h⟩ := poisson_cw hc1 hc2
  refine ⟨max 1 K₀, le_max_left _ _, ?_⟩
  set K : ℝ := max 1 K₀ with hK
  have hK1 : (1 : ℝ) ≤ K := le_max_left _ _
  have hK0 : 0 < K := lt_of_lt_of_le one_pos hK1
  have hstep : ∀ τ : ℝ, 0 < τ → τ ≤ 1 → ∀ f : L2H',
      ∫⁻ z : UpperHalfPlane, ENNReal.ofReal (omC c (z : ℂ) ^ 2 * ‖specE.integral (GW 0 τ) f z‖ ^ 2)
        ≤ ENNReal.ofReal (K ^ 2) * ∫⁻ z : UpperHalfPlane, ENNReal.ofReal (omC c (z : ℂ) ^ 2 * ‖f z‖ ^ 2) := fun τ hτ hτ1 f => by
    refine (h τ hτ hτ1 f).trans ?_
    gcongr
    exact le_max_right _ _
  intro n
  induction n with
  | zero =>
    intro τ hτ hτn f
    exfalso
    have : τ ≤ 0 := by simpa using hτn
    linarith
  | succ n ih =>
    intro τ hτ hτn f
    by_cases h1 : τ ≤ 1
    · refine (hstep τ hτ h1 f).trans ?_
      gcongr
      calc K = K ^ 1 := (pow_one K).symm
        _ ≤ K ^ (n + 1) := pow_le_pow_right₀ hK1 (by omega)
    · rw [not_le] at h1
      have hτ' : 0 < τ - 1 := by linarith
      have hτn' : τ - 1 ≤ n := by
        have : τ ≤ (n : ℝ) + 1 := by exact_mod_cast hτn
        linarith
      have e : specE.integral (GW 0 τ) f = specE.integral (GW 0 1) (specE.integral (GW 0 (τ - 1)) f) := by
        rw [GW_comp one_pos hτ']
        congr 2
        ring
      rw [e]
      calc ∫⁻ z : UpperHalfPlane, ENNReal.ofReal (omC c (z : ℂ) ^ 2 * ‖specE.integral (GW 0 1) (specE.integral (GW 0 (τ - 1)) f) z‖ ^ 2)
          ≤ ENNReal.ofReal (K ^ 2) * ∫⁻ z : UpperHalfPlane, ENNReal.ofReal (omC c (z : ℂ) ^ 2 * ‖specE.integral (GW 0 (τ - 1)) f z‖ ^ 2) :=
            hstep 1 one_pos le_rfl _
        _ ≤ ENNReal.ofReal (K ^ 2) * (ENNReal.ofReal ((K ^ n) ^ 2) * ∫⁻ z : UpperHalfPlane, ENNReal.ofReal (omC c (z : ℂ) ^ 2 * ‖f z‖ ^ 2)) := by
            gcongr
            exact ih (τ - 1) hτ' hτn' f
        _ = ENNReal.ofReal ((K ^ (n + 1)) ^ 2) * ∫⁻ z : UpperHalfPlane, ENNReal.ofReal (omC c (z : ℂ) ^ 2 * ‖f z‖ ^ 2) := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
            congr 2
            ring

/-- Change of the radius in `ddBound`, with a factor `B` for each power. -/
lemma ddBound_scaleB {C' Cf B σ α ħ t : ℝ} (hC' : 0 ≤ C') (hB : 0 ≤ B) (hσ : 0 < σ) (hα : 0 < α) (hħ : 0 < ħ) (ht : 0 ≤ t)
    (h1 : ((σ * ħ)⁻¹) ^ 2 ≤ B * ((α * ħ)⁻¹) ^ 2) (h2 : ħ * t / σ ^ 2 ≤ B * (ħ * t / α ^ 2)) (K N : ℕ) :
    ddBound C' σ ħ t K N * Cf ≤ ddBound (B * C' * max 1 Cf) α ħ t K N := by
  unfold ddBound
  have hs0 : 0 ≤ ((σ * ħ)⁻¹) ^ 2 := by positivity
  have hy0 : 0 ≤ ħ * t / σ ^ 2 := by positivity
  have e1 : ((σ * ħ)⁻¹) ^ (2 * N) ≤ B ^ N * ((α * ħ)⁻¹) ^ (2 * N) := by
    rw [pow_mul, pow_mul, ← mul_pow]
    exact pow_le_pow_left₀ hs0 h1 N
  have e2 : (ħ * t / σ ^ 2) ^ (K + 1) ≤ B ^ (K + 1) * (ħ * t / α ^ 2) ^ (K + 1) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hy0 h2 (K + 1)
  have hm1 : (1 : ℝ) ≤ max 1 Cf := le_max_left _ _
  have hm2 : Cf ≤ max 1 Cf ^ (N + K + 1) := (le_max_right 1 Cf).trans (le_self_pow₀ hm1 (by omega))
  have hmc : (0 : ℝ) ≤ max 1 Cf ^ (N + K + 1) := by positivity
  have hP0 : 0 ≤ C' ^ (N + K + 1) * (N : ℝ) ^ (2 * N) * (K.factorial : ℝ) := by positivity
  have hZ0 : (0 : ℝ) ≤ (ħ * t / σ ^ 2) ^ (K + 1) := by positivity
  have hW0 : (0 : ℝ) ≤ B ^ N * ((α * ħ)⁻¹) ^ (2 * N) := by positivity
  have hV0 : (0 : ℝ) ≤ B ^ (K + 1) * (ħ * t / α ^ 2) ^ (K + 1) := by positivity
  have hL0 : 0 ≤ C' ^ (N + K + 1) * (N : ℝ) ^ (2 * N) * (K.factorial : ℝ) * ((σ * ħ)⁻¹) ^ (2 * N) * (ħ * t / σ ^ 2) ^ (K + 1) := by
    positivity
  have hQ0 : 0 ≤ C' ^ (N + K + 1) * (N : ℝ) ^ (2 * N) * (K.factorial : ℝ) * (B ^ N * ((α * ħ)⁻¹) ^ (2 * N))
      * (B ^ (K + 1) * (ħ * t / α ^ 2) ^ (K + 1)) := mul_nonneg (mul_nonneg hP0 hW0) hV0
  have s1 : C' ^ (N + K + 1) * (N : ℝ) ^ (2 * N) * (K.factorial : ℝ) * ((σ * ħ)⁻¹) ^ (2 * N) * (ħ * t / σ ^ 2) ^ (K + 1)
      ≤ C' ^ (N + K + 1) * (N : ℝ) ^ (2 * N) * (K.factorial : ℝ) * (B ^ N * ((α * ħ)⁻¹) ^ (2 * N))
        * (B ^ (K + 1) * (ħ * t / α ^ 2) ^ (K + 1)) :=
    mul_le_mul (mul_le_mul_of_nonneg_left e1 hP0) e2 hZ0 (mul_nonneg hP0 hW0)
  have s2 : C' ^ (N + K + 1) * (N : ℝ) ^ (2 * N) * (K.factorial : ℝ) * ((σ * ħ)⁻¹) ^ (2 * N) * (ħ * t / σ ^ 2) ^ (K + 1) * Cf
      ≤ C' ^ (N + K + 1) * (N : ℝ) ^ (2 * N) * (K.factorial : ℝ) * (B ^ N * ((α * ħ)⁻¹) ^ (2 * N))
        * (B ^ (K + 1) * (ħ * t / α ^ 2) ^ (K + 1)) * max 1 Cf ^ (N + K + 1) := by
    by_cases hCf : 0 ≤ Cf
    · exact mul_le_mul s1 hm2 hCf hQ0
    · have hCf' : Cf ≤ 0 := le_of_lt (not_le.1 hCf)
      exact (mul_nonpos_of_nonneg_of_nonpos hL0 hCf').trans (mul_nonneg hQ0 hmc)
  refine s2.trans (le_of_eq ?_)
  have hB1 : B ^ N * B ^ (K + 1) = B ^ (N + K + 1) := by
    rw [← pow_add, add_assoc]
  rw [mul_pow, mul_pow, ← hB1]
  ring

/-- Passing from the internal radius `1/12` to a radius `α ≤ A`. -/
lemma ddBound_scale12 {C' Cf α A ħ t : ℝ} (hC' : 0 ≤ C') (hα : 0 < α) (hαA : α ≤ A) (hħ : 0 < ħ) (ht : 0 ≤ t) (K N : ℕ) :
    ddBound C' (1 / 12) ħ t K N * Cf ≤ ddBound ((12 * A) ^ 2 * C' * max 1 Cf) α ħ t K N := by
  have hA : 0 < A := lt_of_lt_of_le hα hαA
  have h12 : (12 * α) ^ 2 ≤ (12 * A) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
  refine ddBound_scaleB hC' (by positivity) (by norm_num) hα hħ ht ?_ ?_ K N
  · have e : ((1 / 12 * ħ)⁻¹) ^ 2 = (12 * α) ^ 2 * ((α * ħ)⁻¹) ^ 2 := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_right h12 (by positivity)
  · have e : ħ * t / (1 / 12) ^ 2 = (12 * α) ^ 2 * (ħ * t / α ^ 2) := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_right h12 (by positivity)

set_option maxHeartbeats 16000000 in
/-- **The estimate of `pc:main` for `1/2 < α ≤ A`, smooth amplitudes.** -/
theorem pcmain_big_smooth (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ] (_hOP : OrientationPreserving Γ)
    (x₀ : ℍ) (β κ A : ℝ) (hβ : 1 / 2 < β) (hκ : 0 < κ) (hA : 1 / 2 ≤ A) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
    ∀ (ħ' α t : ℝ) (K N : ℕ) (g : SL(2, ℝ)) (a : ℍ → ℂ),
      0 < ħ' → ħ' ≤ 1 → 1 / 2 < α → α ≤ A → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ →
      0 ≤ t → t ≤ δ * Real.sqrt (α / ħ') → SmoothH a → prNormX x₀ α β a < ∞ →
      ∃ (hv : PerioConv Γ (initState g ħ' a)) (hw : PerioConv Γ (approxSolB g K ħ' t a)),
        approxErr Γ N ħ' t hv hw ≤ ENNReal.ofReal (ddBound C α ħ' t K N) * prNormX x₀ α β a := by
  haveI : Countable Γ := countable_of_properlyDiscontinuous Γ
  have hA0 : 0 < A := by linarith
  have hτ : (1 : ℝ) < Real.pi / 2 := by linarith [Real.pi_gt_three]
  obtain ⟨C₁, hC, hF'⟩ := lem_fc hτ
  have hc0 : (0 : ℝ) ≤ 3 / 4 := by norm_num
  have hc1 : (3 / 4 : ℝ) ≤ 1 := by norm_num
  have hc12 : (1 / 2 : ℝ) < 3 / 4 := by norm_num
  have hc2 : (3 / 4 : ℝ) < 1 := by norm_num
  have hm : (1 / 2 : ℝ) ≤ 3 := by norm_num
  have hml : 2 * ((1 : ℝ) + 1 / 2) ^ 2 < (3 : ℝ) ^ 2 := by norm_num
  have hl := log_two_pos'
  have hD : 0 < Real.exp (1 / 2) * (2 / Real.log 2) ^ (3 / 4 : ℝ) := by positivity
  have hDg : 0 ≤ 2 / Real.log 2 := by positivity
  have hkp : 0 < κ / (1728 * A ^ 3) := by positivity
  obtain ⟨K₁, δ', hK₁, hδ', hcore⟩ := dd_core_pc hc0 hc1 hD hDg hm hml hkp hC hF'
  obtain ⟨Cd, hCd, hdata⟩ := data_factor hc12 hc2 hm
  obtain ⟨Kp, hKp1, hpois⟩ := poisson_cw_all hc12 hc2
  have hKp0 : 0 < Kp := lt_of_lt_of_le one_pos hKp1
  set n₀ : ℕ := ⌈A⌉₊ with hn₀
  have h12A : 0 < Real.sqrt (12 * A) := Real.sqrt_pos.2 (by positivity)
  set S₀ : ℝ := Real.sqrt (surfW_printed Γ x₀ hc12).C.toReal with hS₀
  have hS₀0 : 0 ≤ S₀ := Real.sqrt_nonneg _
  have hC₄1 : 1 ≤ C4m C₁ := one_le_C4m C₁
  set Cc : ℝ := (1 ^ 2 * C4m C₁ * 128) * (1 + 4 * C4m C₁ ^ 2 * (S₀ * K₁)) with hCc
  have hCc0 : 0 < Cc := by
    rw [hCc]
    have h2 : 0 < C4m C₁ := by linarith
    positivity
  have hη : 0 < β - 1 / 2 := by linarith
  set Cβ : ℝ := (1 + 1 / (β - 1 / 2)) / Real.log 2 * Real.exp β with hCβ
  have hCβ0 : 0 ≤ Cβ := by positivity
  set Lc : ℝ := (1 / Real.log 2) ^ (3 / 4 : ℝ) with hLc
  have hLc0 : 0 ≤ Lc := by positivity
  set Cf : ℝ := Lc * (Cd * Kp ^ n₀) * Cβ with hCf
  have hCf0 : 0 ≤ Cf := by positivity
  refine ⟨(12 * A) ^ 2 * Cc * max 1 Cf, δ' / Real.sqrt (12 * A), by positivity, by positivity, ?_⟩
  intro ħ α t K N g a hħ hħ1 hα12 hαA hk hgx ht htδ hsm hfin
  have hα : 0 < α := by linarith
  -- the internal radius
  set σ : ℝ := 1 / 12 with hσd
  have hσ : 0 < σ := by rw [hσd]; norm_num
  have hσ1 : σ ≤ 1 := by rw [hσd]; norm_num
  have hσh : σ < 1 / 2 := by rw [hσd]; norm_num
  have hση : 1 / 2 - σ ≤ 1 := by rw [hσd]; norm_num
  have hσm : σ * 3 ≤ 1 / 2 := by rw [hσd]; norm_num
  have hk' : κ / (1728 * A ^ 3) * ħ ≤ σ ^ 3 := by
    have h3 : α ^ 3 ≤ A ^ 3 := pow_le_pow_left₀ hα.le hαA 3
    have hA3 : 0 < 1728 * A ^ 3 := by positivity
    have e : κ / (1728 * A ^ 3) * ħ = (κ * ħ) / (1728 * A ^ 3) := by ring
    rw [e, div_le_iff₀ hA3, hσd]
    have : κ * ħ ≤ A ^ 3 := hk.trans h3
    nlinarith
  have htδ' : t ≤ δ' * Real.sqrt (σ / ħ) := by
    have e : Real.sqrt (α / ħ) / Real.sqrt (12 * A) = Real.sqrt (α / ħ / (12 * A)) :=
      (Real.sqrt_div' _ (by positivity)).symm
    have hle : α / ħ / (12 * A) ≤ σ / ħ := by
      rw [hσd, div_div, div_le_div_iff₀ (by positivity) hħ]
      nlinarith
    calc t ≤ δ' / Real.sqrt (12 * A) * Real.sqrt (α / ħ) := htδ
      _ = δ' * (Real.sqrt (α / ħ) / Real.sqrt (12 * A)) := by ring
      _ = δ' * Real.sqrt (α / ħ / (12 * A)) := by rw [e]
      _ ≤ δ' * Real.sqrt (σ / ħ) := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hle) hδ'.le
  -- the base point
  set G : SL(2, ℝ) := g * transH x₀ with hG
  have hGI : G • UpperHalfPlane.I = x₀ := by rw [hG, mul_smul, transH_smul_I, hgx]
  set p : PGL(2, ℝ) := Matrix.SpecialLinearGroup.toPGL G with hp
  -- the norm
  by_cases ha : MemLp a 2 (volume : Measure ℍ)
  swap
  · exfalso
    simp [prNormX, ha] at hfin
  by_cases hd : ha.toLp _ ∈ (expLambda α).domain
  swap
  · exfalso
    simp [prNormX, ha, hd] at hfin
  have hPR : prNormX x₀ α β a = eLpNorm (fun z => ((Real.exp (β * angleDx x₀ z) : ℝ) : ℂ)
      * (expLambda α ⟨ha.toLp _, hd⟩ : L2H') z) 2 (volume : Measure ℍ) := by
    simp only [prNormX, dif_pos ha, dif_pos hd]
  set f₀ : L2H' := expLambda α ⟨ha.toLp _, hd⟩ with hf₀
  have hg2 : MemLp (fun z => ((Real.exp (β * angleDx x₀ z) : ℝ) : ℂ) * f₀ z) 2 (volume : Measure ℍ) := by
    rw [hPR] at hfin
    exact hfin
  set Gp : L2H' := hg2.toLp _ with hGp
  have hPRn : prNormX x₀ α β a = ENNReal.ofReal ‖Gp‖ := by
    rw [hPR, hGp, Lp.norm_toLp, ENNReal.ofReal_toReal hg2.ne]
  set F : L2H' := isoU p f₀ with hF
  have hFae : ⇑F =ᵐ[volume] fun z => f₀ (p • z) := isoU_ae p f₀
  have hGpae : ⇑(isoU p Gp) =ᵐ[volume] fun z => ((Real.exp (β * angleDx UpperHalfPlane.I z) : ℝ) : ℂ) * F z := by
    have h1 := (measurePreserving_smul p (volume : Measure ℍ)).quasiMeasurePreserving.ae_eq_comp hg2.coeFn_toLp
    filter_upwards [isoU_ae p Gp, h1, hFae] with z e1 e2 e3
    rw [e1, e3]
    have e2' : (Gp : L2H') (p • z) = ((Real.exp (β * angleDx x₀ (p • z)) : ℝ) : ℂ) * f₀ (p • z) := e2
    rw [e2']
    have hpz : p • z = G • z := toPGL_smul G z
    have e4 : angleDx x₀ (p • z) = angleDx UpperHalfPlane.I z := by
      unfold angleDx
      rw [hpz, ← hGI, dist_smul]
    rw [e4]
  -- the weights
  set Γ' := conjS (Matrix.SpecialLinearGroup.toPGL G⁻¹) Γ with hΓ'
  set W : SurfW Γ' := surfW_printed Γ' UpperHalfPlane.I hc12 with hWd
  set Wγ : SurfW Γ' := surfW_cosh Γ' UpperHalfPlane.I hc12 with hWγd
  set Wβ : SurfW Γ' := surfW_cosh Γ' UpperHalfPlane.I (show (1 / 2 : ℝ) < 1 by norm_num) with hWβd
  have hWγ : ∀ z, Wγ.ω z = omG (3 / 4) z := fun z => rfl
  have hWβ : ∀ z, Wβ.ω z = omG 1 z := fun z => rfl
  have hW : CritW (3 / 4) (Real.exp (1 / 2) * (2 / Real.log 2) ^ (3 / 4 : ℝ)) W.ω := critW_printed hc0
  have hgr : ∀ s z, |W.mS s z| ≤ 2 / Real.log 2 * Real.exp |s| := fun s z => mS_printed_le hc12 hc1 UpperHalfPlane.I s z
  have hWω : ∀ z, W.ω z = omP (3 / 4) (dist UpperHalfPlane.I z) := fun z => rfl
  -- the chart of `F`
  obtain ⟨Fω, hFω, nFω⟩ : ∃ Fω : L2H', ((Fω : ℍ → ℂ) =ᵐ[volume] fun z => ((W.ω z : ℝ) : ℂ) * F z) ∧ ‖Fω‖ ≤ Cβ * ‖Gp‖ := by
    refine exists_chart_of_lint W.meas (fun z => (W.ω_pos z).le) F (by positivity) ?_
    calc ∫⁻ z : ℍ, (ENNReal.ofReal (W.ω z) * ‖F z‖ₑ) ^ 2 ≤ ∫⁻ z : ℍ, ENNReal.ofReal (Cβ ^ 2) * ‖(isoU p Gp) z‖ₑ ^ 2 := by
          refine lintegral_mono_ae ?_
          filter_upwards [hGpae] with z hz
          rw [hz, enorm_mul, ← ofReal_norm ((Real.exp (β * angleDx UpperHalfPlane.I z) : ℝ) : ℂ), Complex.norm_real,
            Real.norm_of_nonneg (Real.exp_pos _).le, ENNReal.ofReal_pow hCβ0, ← mul_pow, ← mul_assoc, ← ENNReal.ofReal_mul hCβ0]
          gcongr
          rw [hWω]
          exact omP_le_exp_angle hc1 hβ UpperHalfPlane.I z
      _ = ENNReal.ofReal ((Cβ * ‖Gp‖) ^ 2) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_enorm_sq_eq, LinearIsometryEquiv.norm_map,
            ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
  -- the data: first `e^{-(α - 1/2)Λ}`, then the factorization at the radius `1/2`
  have hα' : 0 < α - 1 / 2 := by linarith
  have hαn : α - 1 / 2 ≤ (n₀ : ℝ) := by
    have := Nat.le_ceil A
    rw [hn₀]
    linarith
  set F₁ : L2H' := specE.integral (GW 0 (α - 1 / 2)) F with hF₁
  obtain ⟨e1, e2⟩ := hdata σ (1 / 2) hσ hσh hση hσm F₁
  set Ft : L2H' := specE.integral (GQ σ 3) (specE.integral (GW 0 (1 / 2 - σ)) F₁) with hFt
  obtain ⟨Hω, hHω, nHω⟩ : ∃ Hω : L2H', ((Hω : ℍ → ℂ) =ᵐ[volume] fun z => ((W.ω z : ℝ) : ℂ) * Ft z) ∧ ‖Hω‖ ≤ Lc * (Cd * Kp ^ n₀) * ‖Fω‖ := by
    refine exists_chart_of_lint W.meas (fun z => (W.ω_pos z).le) Ft (by positivity) ?_
    have hF2 : ∫⁻ z : ℍ, ENNReal.ofReal (omC (3 / 4) (z : ℂ) ^ 2 * ‖F z‖ ^ 2) ≤ ENNReal.ofReal (‖Fω‖ ^ 2) := by
      rw [← lintegral_enorm_sq_eq]
      refine lintegral_mono_ae ?_
      filter_upwards [hFω] with z hz
      rw [hz, enorm_mul, ← ofReal_norm ((W.ω z : ℝ) : ℂ), Complex.norm_real, Real.norm_of_nonneg (W.ω_pos z).le,
        ← sq_ofReal_enorm (omC_nonneg _ z)]
      gcongr
      rw [hWω]
      exact omC_le_omP hc0 z
    have hF12 : ∫⁻ z : ℍ, ENNReal.ofReal (omC (3 / 4) (z : ℂ) ^ 2 * ‖F₁ z‖ ^ 2)
        ≤ ENNReal.ofReal ((Kp ^ n₀) ^ 2) * ENNReal.ofReal (‖Fω‖ ^ 2) := by
      refine (hpois n₀ (α - 1 / 2) hα' hαn F).trans ?_
      gcongr
    calc ∫⁻ z : ℍ, (ENNReal.ofReal (W.ω z) * ‖Ft z‖ₑ) ^ 2
        ≤ ∫⁻ z : ℍ, ENNReal.ofReal (Lc ^ 2) * ENNReal.ofReal (omC (3 / 4) (z : ℂ) ^ 2 * ‖Ft z‖ ^ 2) := by
          refine lintegral_mono fun z => ?_
          rw [← sq_ofReal_enorm (omC_nonneg _ z), ENNReal.ofReal_pow hLc0, ← mul_pow, ← mul_assoc, ← ENNReal.ofReal_mul hLc0]
          gcongr
          rw [hWω]
          exact omP_le_omC hc0 z
      _ = ENNReal.ofReal (Lc ^ 2) * ∫⁻ z : ℍ, ENNReal.ofReal (omC (3 / 4) (z : ℂ) ^ 2 * ‖Ft z‖ ^ 2) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (Lc ^ 2) * (ENNReal.ofReal (Cd ^ 2) * (ENNReal.ofReal ((Kp ^ n₀) ^ 2) * ENNReal.ofReal (‖Fω‖ ^ 2))) := by
          gcongr
          exact e2.trans (by gcongr)
      _ = ENNReal.ofReal ((Lc * (Cd * Kp ^ n₀) * ‖Fω‖) ^ 2) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
  have hHωn : ‖Hω‖ ≤ Cf * ‖Gp‖ := by
    calc ‖Hω‖ ≤ Lc * (Cd * Kp ^ n₀) * ‖Fω‖ := nHω
      _ ≤ Lc * (Cd * Kp ^ n₀) * (Cβ * ‖Gp‖) := by gcongr
      _ = _ := by rw [hCf]; ring
  -- the amplitude
  set A' : L2H' := vE 3 σ Ft 0 with hA'
  have hA1 : A' = isoU p (ha.toLp a) := by
    have e3 : specE.integral (GW 0 (1 / 2)) F₁ = specE.integral (GW 0 α) F := by
      rw [hF₁, GW_comp (by norm_num) hα']
      congr 2
      ring
    rw [e1, e3, hF, integral_iso p (GW_mem 0 hα) f₀, hf₀, poisson_left_inv hα hd]
  have hAae : ⇑A' =ᵐ[volume] fun w => a (G • w) := by
    have h1 := (measurePreserving_smul p (volume : Measure ℍ)).quasiMeasurePreserving.ae_eq_comp ha.coeFn_toLp
    rw [hA1]
    filter_upwards [isoU_ae p (ha.toLp a), h1] with z e3 e4
    rw [e3]
    have e4' : (ha.toLp a : L2H') (p • z) = a (p • z) := e4
    have hpz : p • z = G • z := toPGL_smul G z
    rw [e4', hpz]
  have hAW : AllWords A' := vE_allWords hm hσ hσ1 Ft 0
  have hsG : SmoothH fun w => a (G • w) := smoothH_comp G hsm
  have hGa' : ∀ w : List Bool, ∃ G' : L2H', W.Chart G' (wordAct w A') := fun w =>
    word_chart_om hc0 hc1 hD hm hml hW hσ hσ1 w hHω
  choose Ga hGa using hGa'
  obtain ⟨hvG, hwG⟩ := perioConv_general (W := W) hsG hAae hAW hGa K ħ t
  have hE := approxErr_general (W := W) hsG hAae hAW hGa hħ.ne' K N t hvG hwG
  have hcore2 := hcore Γ' W Wγ Wβ hW hgr hWγ hWβ ħ σ t K N Ft Hω hHω hħ hħ1 hσ hσ1 hk' ht htδ'
  have hWC : W.C = (surfW_printed Γ x₀ hc12).C := by
    have e : Matrix.SpecialLinearGroup.toPGL G⁻¹ • x₀ = UpperHalfPlane.I := by
      rw [toPGL_smul, ← hGI, inv_smul_smul]
    show (⨆ z : ℍ, ∑' γ : conjS (Matrix.SpecialLinearGroup.toPGL G⁻¹) Γ,
        ENNReal.ofReal ((omP (3 / 4) (dist UpperHalfPlane.I (γ • z)))⁻¹) ^ 2)
      = ⨆ z : ℍ, ∑' γ : Γ, ENNReal.ofReal ((omP (3 / 4) (dist x₀ (γ • z)))⁻¹) ^ 2
    rw [← e]
    exact iSup_tsum_conj_move _ Γ x₀ (fun d => ENNReal.ofReal ((omP (3 / 4) d)⁻¹) ^ 2)
  rw [hWC, ← hS₀, ← hCc] at hcore2
  have hfinal : ‖(Complex.I * (ħ : ℂ) / 2) ^ (K + 1) • simplexInt (K + 1) t fun ss => W.vS ħ (ss.headD 0) (polyAct (bP ħ N (ss.headD 0) ss) A')‖
      ≤ ddBound ((12 * A) ^ 2 * Cc * max 1 Cf) α ħ t K N * ‖Gp‖ := by
    refine hcore2.trans ?_
    have hdd0 : 0 ≤ ddBound Cc σ ħ t K N := ddBound_nonneg K N hCc0.le hσ hħ ht
    calc ddBound Cc σ ħ t K N * ‖Hω‖ ≤ ddBound Cc σ ħ t K N * (Cf * ‖Gp‖) := mul_le_mul_of_nonneg_left hHωn hdd0
      _ = (ddBound Cc (1 / 12) ħ t K N * Cf) * ‖Gp‖ := by rw [hσd]; ring
      _ ≤ ddBound ((12 * A) ^ 2 * Cc * max 1 Cf) α ħ t K N * ‖Gp‖ :=
          mul_le_mul_of_nonneg_right (ddBound_scale12 hCc0.le hα hαA hħ ht K N) (norm_nonneg _)
  have hc1' := norm_cstB x₀ ħ
  have hc0' := cstB_ne x₀ ħ
  have ei := initState_mul x₀ g ħ a
  have ea := approxSolB_mul x₀ g K ħ t a
  have hvG' : PerioConv Γ fun z => cstB x₀ ħ * initState g ħ a z := ei ▸ hvG
  have hwG' : PerioConv Γ fun z => cstB x₀ ħ * approxSolB g K ħ t a z := ea ▸ hwG
  have hv : PerioConv Γ (initState g ħ a) := perioConv_const hc0' hvG'
  have hw2 : PerioConv Γ (approxSolB g K ħ t a) := perioConv_const hc0' hwG'
  refine ⟨hv, hw2, ?_⟩
  rw [← approxErr_const hc1' hv hw2 hvG' hwG', ← approxErr_congr ei ea hvG hwG hvG' hwG', hE, hPRn]
  rw [← ofReal_norm, ← ENNReal.ofReal_mul (ddBound_nonneg K N (by positivity) hα hħ ht)]
  exact ENNReal.ofReal_le_ofReal hfinal

/-- **The estimate of `pc:main` on `0 < α ≤ A`, for every `A > 0`**; `C, δ` depend also on `A`. -/
theorem pcMainAt_all (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ] (hOP : OrientationPreserving Γ)
    (x₀ : ℍ) (β κ A : ℝ) (hβ : 1 / 2 < β) (hκ : 0 < κ) : PcMainAt Γ x₀ β κ A := by
  obtain ⟨Ca, δa, hCa, hδa, ha⟩ := pcmain_half_smooth Γ hOP x₀ β κ hβ hκ
  obtain ⟨Cb, δb, hCb, hδb, hb⟩ := pcmain_big_smooth Γ hOP x₀ β κ (max A (1 / 2)) hβ hκ (le_max_right _ _)
  refine ⟨max Ca Cb, min δa δb, lt_max_of_lt_left hCa, lt_min hδa hδb, ?_⟩
  intro ħ α t K N g a hħ hħ1 hα hαA hk hg ht htδ hsm hfin
  have hs0 : 0 ≤ Real.sqrt (α / ħ) := Real.sqrt_nonneg _
  by_cases h : α ≤ 1 / 2
  · obtain ⟨hv, hw, hbd⟩ := ha ħ α t K N g a hħ hħ1 hα h hk hg ht
      (htδ.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hs0)) hsm hfin
    refine ⟨hv, hw, hbd.trans ?_⟩
    gcongr
    exact ddBound_mono (K := K) (N := N) hCa.le (le_max_left _ _) hα hħ ht
  · rw [not_le] at h
    obtain ⟨hv, hw, hbd⟩ := hb ħ α t K N g a hħ hħ1 h (hαA.trans (le_max_left _ _)) hk hg ht
      (htδ.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hs0)) hsm hfin
    refine ⟨hv, hw, hbd.trans ?_⟩
    gcongr
    exact ddBound_mono (K := K) (N := N) hCb.le (le_max_right _ _) hα hħ ht

/-- The domain of `e^{αΛ}` decreases with `α ≥ 0`. -/
lemma expLambda_domain_mono {α α' : ℝ} (h0 : 0 ≤ α') (h : α' ≤ α) {u : L2H'} (hu : u ∈ (expLambda α).domain) :
    u ∈ (expLambda α').domain := by
  have hu' : MemLp (fun s : ℝ => ((Real.exp (α * Real.sqrt s) : ℝ) : ℂ)) 2 (specE.assoc u) := hu
  show MemLp (fun s : ℝ => ((Real.exp (α' * Real.sqrt s) : ℝ) : ℂ)) 2 (specE.assoc u)
  refine hu'.mono (measurable_fExp α').aestronglyMeasurable (Filter.Eventually.of_forall fun s => ?_)
  rw [Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_of_nonneg (Real.exp_pos _).le]
  exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right h (Real.sqrt_nonneg s))

/-- An amplitude of finite printed norm, at any radius `α > 0`, has a `C^∞` representative. -/
theorem lift1_pr_all {x₀ : ℍ} {α β : ℝ} {a : ℍ → ℂ} (hα : 0 < α) (hfin : prNormX x₀ α β a < ⊤) :
    ∃ a' : ℍ → ℂ, SmoothH a' ∧ a' =ᵐ[volume] a := by
  by_cases h1 : α ≤ 1
  · exact lift1_pr hα h1 hfin
  · rw [not_le] at h1
    unfold prNormX at hfin
    split_ifs at hfin with ha h
    · have h' : ha.toLp _ ∈ (expLambda 1).domain := expLambda_domain_mono zero_le_one h1.le h
      obtain ⟨G, hG, hGa⟩ := glue_smooth (patch_smooth one_pos le_rfl h')
      exact ⟨G, hG, hGa.trans ha.coeFn_toLp⟩
    · exact absurd hfin (by simp)
    · exact absurd hfin (by simp)

/-! ### The statements for every amplitude of finite printed norm, `0 < α ≤ A` -/

/-- **Corollary `pc:allalpha`, the estimate of Theorem `pc:main` at every radius**: `0 < α ≤ A`, every amplitude of finite printed
norm; the constants `C, δ` depend also on `A`. -/
def Stmt_pcmain_all : Prop :=
  ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ →
  ∀ (x₀ : ℍ) (β κ A : ℝ), 1 / 2 < β → 0 < κ →
  ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
  ∀ (α : ℝ) (a : ℍ → ℂ), 0 < α → α ≤ A → prNormX x₀ α β a < ⊤ →
    ∃ a' : ℍ → ℂ, SmoothH a' ∧ a' =ᵐ[volume] a ∧
    ∀ (ħ' t : ℝ) (K N : ℕ) (g : SL(2, ℝ)),
      0 < ħ' → ħ' ≤ 1 → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ → 0 ≤ t → t ≤ δ * Real.sqrt (α / ħ') →
      ∃ (hv : PerioConv Γ (initState g ħ' a')) (hw : PerioConv Γ (approxSolB g K ħ' t a')),
        approxErr Γ N ħ' t hv hw ≤ ENNReal.ofReal (ddBound C α ħ' t K N) * prNormX x₀ α β a

theorem pcmain_all : Stmt_pcmain_all := by
  intro Γ _ hOr x₀ β κ A hβ hκ
  obtain ⟨C, δ, hC, hδ, h⟩ := pcMainAt_all Γ hOr x₀ β κ A hβ hκ
  refine ⟨C, δ, hC, hδ, fun α a hα hαα hfin => ?_⟩
  obtain ⟨a', hs, ha⟩ := lift1_pr_all hα hfin
  have e := prNormX_congr (x₀ := x₀) (α := α) (β := β) ha
  refine ⟨a', hs, ha, fun ħ t K N g hħ hħ1 hκc hg ht htδ => ?_⟩
  obtain ⟨hv, hw, hb⟩ := h ħ α t K N g a' hħ hħ1 hα hαα hκc hg ht htδ hs (e.symm ▸ hfin)
  exact ⟨hv, hw, e ▸ hb⟩

/-- **Corollary `pc:thm13` at every radius.** -/
def Stmt_pcthm13_all : Prop :=
  ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ →
  ∀ (x₀ : ℍ) (β κ A : ℝ), 1 / 2 < β → 0 < κ →
  ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
  ∀ (α : ℝ) (a : ℍ → ℂ), 0 < α → α ≤ A → prNormX x₀ α β a < ⊤ →
    ∃ a' : ℍ → ℂ, SmoothH a' ∧ a' =ᵐ[volume] a ∧
    ∀ (ħ' t : ℝ) (g : SL(2, ℝ)),
      0 < ħ' → ħ' ≤ 1 → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ → 0 ≤ t → t ≤ δ * Real.sqrt (α / ħ') →
      ∃ (hv : PerioConv Γ (initState g ħ' a')) (hw : PerioConv Γ (approxSolB g 0 ħ' t a')),
        ‖propM Γ ħ' t ⟨hv.2.toLp _, by rw [propM_domain_eq_top]; trivial⟩ - hw.2.toLp _‖ₑ
          ≤ ENNReal.ofReal (C * (ħ' * t / α ^ 2)) * prNormX x₀ α β a

theorem pcthm13_all : Stmt_pcthm13_all := by
  intro Γ _ hOr x₀ β κ A hβ hκ
  obtain ⟨C, δ, hC, hδ, h⟩ := pcthm13_core (pcMainAt_all Γ hOr x₀ β κ A hβ hκ)
  refine ⟨C, δ, hC, hδ, fun α a hα hαα hfin => ?_⟩
  obtain ⟨a', hs, ha⟩ := lift1_pr_all hα hfin
  have e := prNormX_congr (x₀ := x₀) (α := α) (β := β) ha
  refine ⟨a', hs, ha, fun ħ t g hħ hħ1 hκc hg ht htδ => ?_⟩
  obtain ⟨hv, hw, hb⟩ := h ħ α t g a' hħ hħ1 hα hαα hκc hg ht htδ hs (e.symm ▸ hfin)
  exact ⟨hv, hw, e ▸ hb⟩

/-- **Corollary `pc:cor15` at every radius.** The cap `δ ≤ κ^{1/2}/max(1, C)` of the manuscript is part of the statement. -/
def Stmt_pccor15_all : Prop :=
  ∃ C' : ℝ, 0 < C' ∧
  ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ →
  ∀ (x₀ : ℍ) (β κ A : ℝ), 1 / 2 < β → 0 < κ →
  ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ δ ≤ Real.sqrt κ / max 1 C ∧
  ∀ (α : ℝ) (a : ℍ → ℂ), 0 < α → α ≤ A → prNormX x₀ α β a < ⊤ →
    ∃ a' : ℍ → ℂ, SmoothH a' ∧ a' =ᵐ[volume] a ∧
    ∀ (ħ' t ε : ℝ) (K N : ℕ) (g : SL(2, ℝ)),
      0 < ħ' → ħ' ≤ 1 → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ → 0 ≤ t → t ≤ δ * Real.sqrt (α / ħ') →
      0 < ε → ε < 1 → 1 - ε ≤ K * (C * ħ' * t / α ^ 2) → K * (C * ħ' * t / α ^ 2) ≤ 1 - ε / 2 →
      ∃ (hv : PerioConv Γ (initState g ħ' a')) (hw : PerioConv Γ (approxSolB g K ħ' t a')),
        approxErr Γ N ħ' t hv hw
          ≤ ENNReal.ofReal (C' / Real.sqrt ε * C ^ (N + 1) * (N : ℝ) ^ (2 * N)
              * ((α * ħ')⁻¹) ^ (2 * N) * Real.exp (-((1 - ε) * α ^ 2 / (C * ħ' * t)))) * prNormX x₀ α β a

theorem pccor15_all : Stmt_pccor15_all := by
  refine ⟨Real.exp (1 / 2), Real.exp_pos _, ?_⟩
  intro Γ _ hOr x₀ β κ A hβ hκ
  obtain ⟨C, δ, hC, hδ, hcap, h⟩ := pccor15_core hκ (pcMainAt_all Γ hOr x₀ β κ A hβ hκ)
  refine ⟨C, δ, hC, hδ, hcap, fun α a hα hαα hfin => ?_⟩
  obtain ⟨a', hs, ha⟩ := lift1_pr_all hα hfin
  have e := prNormX_congr (x₀ := x₀) (α := α) (β := β) ha
  refine ⟨a', hs, ha, fun ħ t ε K N g hħ hħ1 hκc hg ht htδ hε hε1 hK1 hK2 => ?_⟩
  obtain ⟨hv, hw, hb⟩ := h ħ α t ε K N g a' hħ hħ1 hα hαα hκc hg ht htδ hs (e.symm ▸ hfin) hε hε1 hK1 hK2
  exact ⟨hv, hw, e ▸ hb⟩

/-! ### The pointwise corollaries on a range `α ≤ A` without the restriction `A < 1` -/

/-- `pt_arith` with `X` replaced by `m X ≥ 1`, `m ≥ 1`: the factor `m^{2N+2}` goes into the constant. -/
lemma pt_arith_A {C K₀ X Y m : ℝ} {K N : ℕ} (hC : 0 < C) (hK₀ : 0 ≤ K₀) (hm : 1 ≤ m) (hX0 : 0 ≤ X) (hX : 1 ≤ m * X) (hY : 0 ≤ Y) :
    K₀ * (C ^ (N + K + 1) * (N : ℝ) ^ (2 * N) * (K.factorial : ℝ) * X ^ (2 * N) * Y
        + C ^ (N + 1 + K + 1) * ((N + 1 : ℕ) : ℝ) ^ (2 * (N + 1)) * (K.factorial : ℝ) * X ^ (2 * (N + 1)) * Y)
      ≤ (2 * (K₀ + 1) * (max C 1) ^ 2 * 54 * m ^ 4) ^ (N + K + 1) * ((2 * N).factorial : ℝ) * (K.factorial : ℝ) * X ^ (2 * N + 2) * Y := by
  have h := pt_arith (C := C) (K₀ := K₀) (X := m * X) (Y := Y) (K := K) (N := N) hC hK₀ hX hY
  have hm0 : 0 ≤ m := by linarith
  have hXm : X ≤ m * X := by nlinarith
  have hF0 : (0 : ℝ) ≤ (K.factorial : ℝ) := Nat.cast_nonneg _
  have hQ0 : (0 : ℝ) ≤ ((2 * N).factorial : ℝ) := Nat.cast_nonneg _
  have a1 : X ^ (2 * N) ≤ (m * X) ^ (2 * N) := pow_le_pow_left₀ hX0 hXm _
  have a2 : X ^ (2 * (N + 1)) ≤ (m * X) ^ (2 * (N + 1)) := pow_le_pow_left₀ hX0 hXm _
  have hCp : ∀ j : ℕ, 0 ≤ C ^ j := fun j => pow_nonneg hC.le j
  have hN0 : (0 : ℝ) ≤ (N : ℝ) ^ (2 * N) := by positivity
  have hN1 : (0 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) ^ (2 * (N + 1)) := by positivity
  have l1 : C ^ (N + K + 1) * (N : ℝ) ^ (2 * N) * (K.factorial : ℝ) * X ^ (2 * N) * Y
      ≤ C ^ (N + K + 1) * (N : ℝ) ^ (2 * N) * (K.factorial : ℝ) * (m * X) ^ (2 * N) * Y :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left a1 (mul_nonneg (mul_nonneg (hCp _) hN0) hF0)) hY
  have l2 : C ^ (N + 1 + K + 1) * ((N + 1 : ℕ) : ℝ) ^ (2 * (N + 1)) * (K.factorial : ℝ) * X ^ (2 * (N + 1)) * Y
      ≤ C ^ (N + 1 + K + 1) * ((N + 1 : ℕ) : ℝ) ^ (2 * (N + 1)) * (K.factorial : ℝ) * (m * X) ^ (2 * (N + 1)) * Y :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left a2 (mul_nonneg (mul_nonneg (hCp _) hN1) hF0)) hY
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = 2 * (K₀ + 1) * (max C 1) ^ 2 * 54 := ⟨_, rfl⟩
  rw [← hD] at h ⊢
  refine (mul_le_mul_of_nonneg_left (add_le_add l1 l2) hK₀).trans (h.trans ?_)
  have hD0 : 0 ≤ D := by
    have : (0 : ℝ) ≤ max C 1 := le_trans zero_le_one (le_max_right _ _)
    rw [hD]
    positivity
  have hmp : m ^ (2 * N + 2) ≤ (m ^ 4) ^ (N + K + 1) := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ hm (by omega)
  have hXp : (0 : ℝ) ≤ X ^ (2 * N + 2) := pow_nonneg hX0 _
  calc D ^ (N + K + 1) * ((2 * N).factorial : ℝ) * (K.factorial : ℝ) * (m * X) ^ (2 * N + 2) * Y
      = D ^ (N + K + 1) * m ^ (2 * N + 2) * (((2 * N).factorial : ℝ) * (K.factorial : ℝ) * X ^ (2 * N + 2) * Y) := by
        rw [mul_pow]
        ring
    _ ≤ D ^ (N + K + 1) * (m ^ 4) ^ (N + K + 1) * (((2 * N).factorial : ℝ) * (K.factorial : ℝ) * X ^ (2 * N + 2) * Y) := by
        have hR0 : (0 : ℝ) ≤ ((2 * N).factorial : ℝ) * (K.factorial : ℝ) * X ^ (2 * N + 2) * Y :=
          mul_nonneg (mul_nonneg (mul_nonneg hQ0 hF0) hXp) hY
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmp (pow_nonneg hD0 _)) hR0
    _ = (D * m ^ 4) ^ (N + K + 1) * ((2 * N).factorial : ℝ) * (K.factorial : ℝ) * X ^ (2 * N + 2) * Y := by
        rw [mul_pow]
        ring

/-- `1 ≤ max(1, A) (αħ)⁻¹` for `0 < α ≤ A`, `0 < ħ ≤ 1`. -/
lemma one_le_maxA_mul_inv {α A ħ : ℝ} (hα : 0 < α) (hαA : α ≤ A) (hħ : 0 < ħ) (hħ1 : ħ ≤ 1) : 1 ≤ max 1 A * (α * ħ)⁻¹ := by
  have hp : 0 < α * ħ := mul_pos hα hħ
  have h1 : α * ħ ≤ max 1 A := by
    have : α * ħ ≤ α := by nlinarith
    exact this.trans (hαA.trans (le_max_right _ _))
  rw [← div_eq_mul_inv, le_div_iff₀ hp]
  linarith

/-- **`pc:cor16bg` on a range `α ≤ A`**, any `A`, from the estimate of `pc:main` on that range; smooth amplitudes. -/
theorem pccor16bg_coreA {Γ : Subgroup PGL(2, ℝ)} [ProperlyDiscontinuousSMul Γ ℍ] {x₀ : ℍ} {β κ A r₀ : ℝ}
    (hr₀ : 0 < r₀) (hinj : InjRadGe Γ r₀) (hmain0 : PcMainAt Γ x₀ β κ A) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
    ∀ (ħ' α t : ℝ) (K N : ℕ) (g : SL(2, ℝ)) (a : ℍ → ℂ),
      0 < ħ' → ħ' ≤ 1 → 0 < α → α ≤ A → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ →
      0 ≤ t → t ≤ δ * Real.sqrt (α / ħ') → SmoothH a → prNormX x₀ α β a < ⊤ →
      ∃ (hv : PerioConv Γ (initState g ħ' a)) (hw : PerioConv Γ (approxSolB g K ħ' t a)),
        PointwiseBound Γ N (errVec Γ ħ' t hv hw)
          (fun _ => ENNReal.ofReal (ptBound C α ħ' t K N) * prNormX x₀ α β a) := by
  obtain ⟨C, δ, hC, hδ, hmain⟩ := hmain0
  obtain ⟨K₀, hK₀, hS⟩ := sobolev_M hr₀
  have hm1 : (1 : ℝ) ≤ max 1 A := le_max_left _ _
  set C' : ℝ := 2 * (K₀ + 1) * (max C 1) ^ 2 * 54 * max 1 A ^ 4 with hC'
  have hC'0 : 0 < C' := by
    have : 0 < max C 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    have : (0 : ℝ) < max 1 A := lt_of_lt_of_le one_pos hm1
    positivity
  refine ⟨C', δ, hC'0, hδ, ?_⟩
  intro ħ α t K N g a hħ hħ1 hα hαα hκc hg ht htδ hsm hfin
  obtain ⟨hv, hw, hN⟩ := hmain ħ α t K N g a hħ hħ1 hα hαα hκc hg ht htδ hsm hfin
  obtain ⟨hv', hw', hN1⟩ := hmain ħ α t K (N + 1) g a hħ hħ1 hα hαα hκc hg ht htδ hsm hfin
  refine ⟨hv, hw, ?_⟩
  set S : ℝ := (prNormX x₀ α β a).toReal with hSdef
  have hS0 : 0 ≤ S := ENNReal.toReal_nonneg
  have hSe : prNormX x₀ α β a = ENNReal.ofReal S := (ENNReal.ofReal_toReal hfin.ne).symm
  set E := errVec Γ ħ t hv hw with hE
  have hd0 : ∀ n, 0 ≤ ddBound C α ħ t K n := fun n => ddBound_nonneg K n hC.le hα hħ ht
  rw [hSe, ← ENNReal.ofReal_mul (hd0 N)] at hN
  rw [hSe, ← ENNReal.ofReal_mul (hd0 (N + 1))] at hN1
  obtain ⟨hdN, hbN⟩ := errNorm_le Γ (n := N) (E := E) (mul_nonneg (hd0 N) hS0) hN
  obtain ⟨hdN1, hbN1⟩ := errNorm_le Γ (n := N + 1) (E := E) (mul_nonneg (hd0 (N + 1)) hS0) hN1
  obtain ⟨hu, hAu⟩ := lapPow_succ Γ N E hdN hdN1
  obtain ⟨f, hfc, hfa, hfb⟩ := hS Γ hinj ⟨lapPowM Γ N ⟨E, hdN⟩, hu⟩
  refine ⟨hdN, f, hfc, hfa, fun x => ?_⟩
  have hX0 : 0 ≤ (α * ħ)⁻¹ := (inv_pos.2 (mul_pos hα hħ)).le
  have hX : 1 ≤ max 1 A * (α * ħ)⁻¹ := one_le_maxA_mul_inv hα hαα hħ hħ1
  have hY : 0 ≤ (ħ * t / α ^ 2) ^ (K + 1) := by positivity
  have hb : ‖f x‖ ≤ ptBound C' α ħ t K N * S := by
    refine (hfb x).trans ?_
    have e1 : ‖negLapMH Γ ⟨lapPowM Γ N ⟨E, hdN⟩, hu⟩‖ = ‖lapPowM Γ (N + 1) ⟨E, hdN1⟩‖ := by
      rw [hAu, norm_neg]
    show K₀ * (‖lapPowM Γ N ⟨E, hdN⟩‖ + ‖negLapMH Γ ⟨lapPowM Γ N ⟨E, hdN⟩, hu⟩‖) ≤ _
    rw [e1]
    have h1 : K₀ * (‖lapPowM Γ N ⟨E, hdN⟩‖ + ‖lapPowM Γ (N + 1) ⟨E, hdN1⟩‖)
        ≤ K₀ * (ddBound C α ħ t K N * S + ddBound C α ħ t K (N + 1) * S) :=
      mul_le_mul_of_nonneg_left (add_le_add hbN hbN1) hK₀
    refine h1.trans ?_
    have h2 := pt_arith_A (K := K) (N := N) hC hK₀ hm1 hX0 hX hY
    have h3 := mul_le_mul_of_nonneg_right h2 hS0
    refine le_trans (le_of_eq ?_) (h3.trans (le_of_eq ?_))
    · unfold ddBound; ring
    · unfold ptBound; rw [← hC']
  have hpt : 0 ≤ ptBound C' α ħ t K N := by
    unfold ptBound
    have := (Nat.cast_nonneg (2 * N).factorial : (0 : ℝ) ≤ _)
    have := (Nat.cast_nonneg K.factorial : (0 : ℝ) ≤ _)
    have := inv_pos.2 (mul_pos hα hħ)
    positivity
  show ‖f x‖ₑ ≤ ENNReal.ofReal (ptBound C' α ħ t K N) * prNormX x₀ α β a
  rw [hSe, ← ENNReal.ofReal_mul hpt, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal hb

/-- **`pc:cor16` on a range `α ≤ A`**, any `A`, from the estimate of `pc:main` on that range; smooth amplitudes. -/
theorem pccor16_coreA {Γ : Subgroup PGL(2, ℝ)} [ProperlyDiscontinuousSMul Γ ℍ] {x₀ : ℍ} {β κ A : ℝ}
    (hmain0 : PcMainAt Γ x₀ β κ A) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
    ∀ (ħ' α t : ℝ) (K N : ℕ) (g : SL(2, ℝ)) (a : ℍ → ℂ),
      0 < ħ' → ħ' ≤ 1 → 0 < α → α ≤ A → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ →
      0 ≤ t → t ≤ δ * Real.sqrt (α / ħ') → SmoothH a → prNormX x₀ α β a < ⊤ →
      ∃ (hv : PerioConv Γ (initState g ħ' a)) (hw : PerioConv Γ (approxSolB g K ħ' t a)),
        PointwiseBound Γ N (errVec Γ ħ' t hv hw)
          (fun x => ENNReal.ofReal C * ((multM Γ x : ℝ≥0∞) ^ (1 / 2 : ℝ))
            * ENNReal.ofReal (ptBound C α ħ' t K N) * prNormX x₀ α β a) := by
  obtain ⟨C, δ, hC, hδ, hmain⟩ := hmain0
  obtain ⟨K₀, hK₀, hS⟩ := sobolev_M_mult
  have hm1 : (1 : ℝ) ≤ max 1 A := le_max_left _ _
  set C' : ℝ := 2 * (1 + 1) * (max C 1) ^ 2 * 54 * max 1 A ^ 4 with hC'
  have hC'0 : 0 < C' := by
    have : 0 < max C 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    have : (0 : ℝ) < max 1 A := lt_of_lt_of_le one_pos hm1
    positivity
  set Cs : ℝ := max K₀ C' with hCs
  have hCs0 : 0 < Cs := lt_of_lt_of_le hC'0 (le_max_right _ _)
  refine ⟨Cs, δ, hCs0, hδ, ?_⟩
  intro ħ α t K N g a hħ hħ1 hα hαα hκc hg ht htδ hsm hfin
  obtain ⟨hv, hw, hN⟩ := hmain ħ α t K N g a hħ hħ1 hα hαα hκc hg ht htδ hsm hfin
  obtain ⟨hv', hw', hN1⟩ := hmain ħ α t K (N + 1) g a hħ hħ1 hα hαα hκc hg ht htδ hsm hfin
  refine ⟨hv, hw, ?_⟩
  set S : ℝ := (prNormX x₀ α β a).toReal with hSdef
  have hS0 : 0 ≤ S := ENNReal.toReal_nonneg
  have hSe : prNormX x₀ α β a = ENNReal.ofReal S := (ENNReal.ofReal_toReal hfin.ne).symm
  set E := errVec Γ ħ t hv hw with hE
  have hd0 : ∀ n, 0 ≤ ddBound C α ħ t K n := fun n => ddBound_nonneg K n hC.le hα hħ ht
  rw [hSe, ← ENNReal.ofReal_mul (hd0 N)] at hN
  rw [hSe, ← ENNReal.ofReal_mul (hd0 (N + 1))] at hN1
  obtain ⟨hdN, hbN⟩ := errNorm_le Γ (n := N) (E := E) (mul_nonneg (hd0 N) hS0) hN
  obtain ⟨hdN1, hbN1⟩ := errNorm_le Γ (n := N + 1) (E := E) (mul_nonneg (hd0 (N + 1)) hS0) hN1
  obtain ⟨hu, hAu⟩ := lapPow_succ Γ N E hdN hdN1
  obtain ⟨f, hfc, hfa, hfb⟩ := hS Γ ⟨lapPowM Γ N ⟨E, hdN⟩, hu⟩
  refine ⟨hdN, f, hfc, hfa, fun x => ?_⟩
  have hX0 : 0 ≤ (α * ħ)⁻¹ := (inv_pos.2 (mul_pos hα hħ)).le
  have hX : 1 ≤ max 1 A * (α * ħ)⁻¹ := one_le_maxA_mul_inv hα hαα hħ hħ1
  have hY : 0 ≤ (ħ * t / α ^ 2) ^ (K + 1) := by positivity
  have hsum : ‖lapPowM Γ N ⟨E, hdN⟩‖ + ‖negLapMH Γ ⟨lapPowM Γ N ⟨E, hdN⟩, hu⟩‖ ≤ ptBound C' α ħ t K N * S := by
    have e1 : ‖negLapMH Γ ⟨lapPowM Γ N ⟨E, hdN⟩, hu⟩‖ = ‖lapPowM Γ (N + 1) ⟨E, hdN1⟩‖ := by
      rw [hAu, norm_neg]
    rw [e1]
    have h1 := add_le_add hbN hbN1
    have h2 := pt_arith_A (K := K) (N := N) hC (zero_le_one : (0 : ℝ) ≤ 1) hm1 hX0 hX hY
    have h3 := mul_le_mul_of_nonneg_right h2 hS0
    refine h1.trans (le_trans (le_of_eq ?_) (h3.trans (le_of_eq ?_)))
    · unfold ddBound; ring
    · unfold ptBound; rw [← hC']
  have hptC : ptBound C' α ħ t K N ≤ ptBound Cs α ħ t K N := ptBound_mono hC'0.le (le_max_right _ _) hα hħ ht
  have hpt0 : 0 ≤ ptBound Cs α ħ t K N := by
    unfold ptBound
    have := (Nat.cast_nonneg (2 * N).factorial : (0 : ℝ) ≤ _)
    have := (Nat.cast_nonneg K.factorial : (0 : ℝ) ≤ _)
    have := inv_pos.2 (mul_pos hα hħ)
    positivity
  show ‖f x‖ₑ ≤ ENNReal.ofReal Cs * ((multM Γ x : ℝ≥0∞) ^ (1 / 2 : ℝ)) * ENNReal.ofReal (ptBound Cs α ħ t K N) * prNormX x₀ α β a
  calc ‖f x‖ₑ ≤ ENNReal.ofReal K₀ * (multM Γ x : ℝ≥0∞) ^ (1 / 2 : ℝ)
        * ENNReal.ofReal (‖lapPowM Γ N ⟨E, hdN⟩‖ + ‖negLapMH Γ ⟨lapPowM Γ N ⟨E, hdN⟩, hu⟩‖) := hfb x
    _ ≤ ENNReal.ofReal Cs * (multM Γ x : ℝ≥0∞) ^ (1 / 2 : ℝ) * ENNReal.ofReal (ptBound Cs α ħ t K N * S) := by
        gcongr
        · exact le_max_left _ _
        · exact hsum.trans (mul_le_mul_of_nonneg_right hptC hS0)
    _ = _ := by
        rw [hSe, ENNReal.ofReal_mul hpt0]
        ring

/-- **Corollary `pc:cor16bg` at every radius.** -/
def Stmt_pccor16bg_all : Prop :=
  ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ →
  ∀ (x₀ : ℍ) (β κ A r₀ : ℝ), 1 / 2 < β → 0 < κ → 0 < r₀ → InjRadGe Γ r₀ →
  ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
  ∀ (α : ℝ) (a : ℍ → ℂ), 0 < α → α ≤ A → prNormX x₀ α β a < ⊤ →
    ∃ a' : ℍ → ℂ, SmoothH a' ∧ a' =ᵐ[volume] a ∧
    ∀ (ħ' t : ℝ) (K N : ℕ) (g : SL(2, ℝ)),
      0 < ħ' → ħ' ≤ 1 → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ → 0 ≤ t → t ≤ δ * Real.sqrt (α / ħ') →
      ∃ (hv : PerioConv Γ (initState g ħ' a')) (hw : PerioConv Γ (approxSolB g K ħ' t a')),
        PointwiseBound Γ N (errVec Γ ħ' t hv hw)
          (fun _ => ENNReal.ofReal (ptBound C α ħ' t K N) * prNormX x₀ α β a)

theorem pccor16bg_all : Stmt_pccor16bg_all := by
  intro Γ _ hOr x₀ β κ A r₀ hβ hκ hr₀ hinj
  obtain ⟨C, δ, hC, hδ, h⟩ := pccor16bg_coreA hr₀ hinj (pcMainAt_all Γ hOr x₀ β κ A hβ hκ)
  refine ⟨C, δ, hC, hδ, fun α a hα hαα hfin => ?_⟩
  obtain ⟨a', hs, ha⟩ := lift1_pr_all hα hfin
  have e := prNormX_congr (x₀ := x₀) (α := α) (β := β) ha
  refine ⟨a', hs, ha, fun ħ t K N g hħ hħ1 hκc hg ht htδ => ?_⟩
  obtain ⟨hv, hw, hb⟩ := h ħ α t K N g a' hħ hħ1 hα hαα hκc hg ht htδ hs (e.symm ▸ hfin)
  exact ⟨hv, hw, e ▸ hb⟩

/-- **Corollary `pc:cor16` at every radius**: every Fuchsian quotient, with the factor `m(z)^{1/2}`. -/
def Stmt_pccor16_all : Prop :=
  ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ →
  ∀ (x₀ : ℍ) (β κ A : ℝ), 1 / 2 < β → 0 < κ →
  ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
  ∀ (α : ℝ) (a : ℍ → ℂ), 0 < α → α ≤ A → prNormX x₀ α β a < ⊤ →
    ∃ a' : ℍ → ℂ, SmoothH a' ∧ a' =ᵐ[volume] a ∧
    ∀ (ħ' t : ℝ) (K N : ℕ) (g : SL(2, ℝ)),
      0 < ħ' → ħ' ≤ 1 → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ → 0 ≤ t → t ≤ δ * Real.sqrt (α / ħ') →
      ∃ (hv : PerioConv Γ (initState g ħ' a')) (hw : PerioConv Γ (approxSolB g K ħ' t a')),
        PointwiseBound Γ N (errVec Γ ħ' t hv hw)
          (fun x => ENNReal.ofReal C * ((multM Γ x : ℝ≥0∞) ^ (1 / 2 : ℝ))
            * ENNReal.ofReal (ptBound C α ħ' t K N) * prNormX x₀ α β a)

theorem pccor16_all : Stmt_pccor16_all := by
  intro Γ _ hOr x₀ β κ A hβ hκ
  obtain ⟨C, δ, hC, hδ, h⟩ := pccor16_coreA (pcMainAt_all Γ hOr x₀ β κ A hβ hκ)
  refine ⟨C, δ, hC, hδ, fun α a hα hαα hfin => ?_⟩
  obtain ⟨a', hs, ha⟩ := lift1_pr_all hα hfin
  have e := prNormX_congr (x₀ := x₀) (α := α) (β := β) ha
  refine ⟨a', hs, ha, fun ħ t K N g hħ hħ1 hκc hg ht htδ => ?_⟩
  obtain ⟨hv, hw, hb⟩ := h ħ α t K N g a' hħ hħ1 hα hαα hκc hg ht htδ hs (e.symm ▸ hfin)
  exact ⟨hv, hw, e ▸ hb⟩

end Qschubert
