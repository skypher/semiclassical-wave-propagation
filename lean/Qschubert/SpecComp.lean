import Physicslib4.Spectral.Unbounded.FunctionalCalculus

/-!
# Composition in the unbounded functional calculus (SPEC-COMP)

For a projection-valued measure `μ`, a bounded measurable `g`, a measurable `f` with `f g` bounded and
any `ψ`: `μ_{g(A)ψ} = |g|² μ_ψ` (`assoc_integral_eq`), so `g(A)ψ ∈ Dom f(A)`
(`integral_apply_mem_integralDomain`), and `f(A) g(A) ψ = (f g)(A) ψ`
(`pmapIntegral_integral_apply`), by the truncations `f 1_{|f| < n}`. Not in physicslib4.
-/

namespace Qschubert

open Physicslib4.Spectral Physicslib4.Spectral.Unbounded MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal

variable {X : Type*} [MeasurableSpace X] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] (μ : ProjectionValuedMeasure X H)

lemma bdd_mul {u v : X → ℂ} (hu : u ∈ BddMeasurable X) (hv : v ∈ BddMeasurable X) :
    u * v ∈ BddMeasurable X := by
  obtain ⟨hum, Cu, hCu⟩ := hu
  obtain ⟨hvm, Cv, hCv⟩ := hv
  refine ⟨hum.mul hvm, Cu * Cv, fun x => ?_⟩
  rw [Pi.mul_apply, norm_mul]
  exact mul_le_mul (hCu x) (hCv x) (norm_nonneg _) ((norm_nonneg _).trans (hCu x))

lemma indicator_one_mem {E : Set X} (hE : MeasurableSet E) :
    E.indicator (1 : X → ℂ) ∈ BddMeasurable X :=
  ⟨measurable_one.indicator hE, 1, fun x => by by_cases hx : x ∈ E <;> simp [hx]⟩

/-- `μ_{g(A)ψ}(E) = ∫_E |g|² dμ_ψ`. -/
lemma assoc_integral_apply {g : X → ℂ} (hg : g ∈ BddMeasurable X) (ψ : H) {E : Set X}
    (hE : MeasurableSet E) :
    μ.assoc (μ.integral g ψ) E = ∫⁻ x in E, ENNReal.ofReal (‖g x‖ ^ 2) ∂(μ.assoc ψ) := by
  have hind := indicator_one_mem hE
  have hprod := bdd_mul hind hg
  rw [assoc_apply_eq_norm_sq μ _ hE, ← ProjectionValuedMeasure.integral_indicator μ hE,
    show (μ.integral (E.indicator 1)) (μ.integral g ψ)
      = (μ.integral (E.indicator 1) * μ.integral g) ψ from rfl,
    ← ProjectionValuedMeasure.integral_mul μ hind hg, norm_sq_integral_apply μ hprod]
  obtain ⟨hpm, Cp, hCp⟩ := hprod
  have hint : Integrable (fun x => ‖(E.indicator (1 : X → ℂ) * g) x‖ ^ 2) (μ.assoc ψ) := by
    refine Integrable.of_bound (C := Cp ^ 2) ((hpm.norm.pow_const 2).aestronglyMeasurable) ?_
    refine Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hCp x) 2
  rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun x => by positivity),
    ← lintegral_indicator hE]
  congr 1
  funext x
  by_cases hx : x ∈ E <;> simp [hx]

/-- `g(A)ψ ∈ Dom f(A)` when `f g` is bounded. -/
theorem integral_apply_mem_integralDomain {f g : X → ℂ} (hf : Measurable f)
    (hg : g ∈ BddMeasurable X) (hfg : f * g ∈ BddMeasurable X) (ψ : H) :
    μ.integral g ψ ∈ integralDomain μ f := by
  have hgm : Measurable g := hg.1
  obtain ⟨_, C, hC⟩ := hfg
  rw [mem_integralDomain, memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero
    ENNReal.ofNat_ne_top hf.aestronglyMeasurable]
  have hle : ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ≥0∞).toReal ∂(μ.assoc (μ.integral g ψ))
      ≤ ∫⁻ x, ENNReal.ofReal (C ^ 2) ∂(μ.assoc ψ) := by
    have hm : Measurable fun x => ‖f x‖ₑ ^ (2 : ℝ≥0∞).toReal := hf.enorm.pow_const _
    have hassoc : μ.assoc (μ.integral g ψ)
        = (μ.assoc ψ).withDensity fun x => ENNReal.ofReal (‖g x‖ ^ 2) := by
      ext E hE
      rw [assoc_integral_apply μ hg ψ hE, withDensity_apply _ hE]
    have hdm : Measurable fun x => ENNReal.ofReal (‖g x‖ ^ 2) :=
      ENNReal.measurable_ofReal.comp (hgm.norm.pow_const 2)
    rw [hassoc, lintegral_withDensity_eq_lintegral_mul _ hdm hm]
    refine lintegral_mono fun x => ?_
    simp only [Pi.mul_apply, ENNReal.toReal_ofNat]
    have h1 : ENNReal.ofReal (‖g x‖ ^ 2) * ‖f x‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖f x * g x‖ ^ 2) := by
      rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
        ← ENNReal.ofReal_mul (by positivity), norm_mul]
      congr 1
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      ring
    rw [h1]
    refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) ?_ 2)
    simpa using hC x
  refine lt_of_le_of_lt hle ?_
  rw [lintegral_const]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

/-- `‖u(A)ψ - v(A)ψ‖² = ∫ |u - v|² dμ_ψ` for bounded `u, v`. -/
lemma norm_sq_integral_sub {u v : X → ℂ} (hu : u ∈ BddMeasurable X) (hv : v ∈ BddMeasurable X)
    (ψ : H) : ‖μ.integral u ψ - μ.integral v ψ‖ ^ 2 = ∫ x, ‖u x - v x‖ ^ 2 ∂(μ.assoc ψ) := by
  have hv' : (-1 : ℂ) • v ∈ BddMeasurable X := (BddMeasurable X).smul_mem _ hv
  have hsum : u + (-1 : ℂ) • v ∈ BddMeasurable X := (BddMeasurable X).add_mem hu hv'
  have e : μ.integral u ψ - μ.integral v ψ = μ.integral (u + (-1 : ℂ) • v) ψ := by
    rw [ProjectionValuedMeasure.integral_add μ hu hv', ProjectionValuedMeasure.integral_smul μ _ hv]
    simp [sub_eq_add_neg]
  rw [e, norm_sq_integral_apply μ hsum]
  congr 1
  funext x
  simp [sub_eq_add_neg]

/-- **SPEC-COMP**: `f(A) g(A) ψ = (f g)(A) ψ` for bounded `g` and `f g`. -/
theorem pmapIntegral_integral_apply {f g : X → ℂ} (hf : Measurable f) (hg : g ∈ BddMeasurable X)
    (hfg : f * g ∈ BddMeasurable X) (ψ : H) :
    pmapIntegral μ f ⟨μ.integral g ψ, integral_apply_mem_integralDomain μ hf hg hfg ψ⟩
      = μ.integral (f * g) ψ := by
  set η : integralDomain μ f := ⟨μ.integral g ψ, integral_apply_mem_integralDomain μ hf hg hfg ψ⟩
  have h1 := tendsto_integral_truncation μ hf η
  set fn : ℕ → X → ℂ := fun n => {x | ‖f x‖ < n}.indicator f
  have hfn : ∀ n, fn n ∈ BddMeasurable X := fun n => indicator_lt_mem_bddMeasurable hf n
  have e : ∀ n, μ.integral (fn n) (η : H) = μ.integral (fn n * g) ψ := fun n => by
    rw [ProjectionValuedMeasure.integral_mul μ (hfn n) hg]; rfl
  obtain ⟨_, C, hC⟩ := hfg
  have hfin : IsFiniteMeasure (μ.assoc ψ) := inferInstance
  have h2 : Tendsto (fun n => μ.integral (fn n * g) ψ) atTop (𝓝 (μ.integral (f * g) ψ)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hsq : Tendsto (fun n => ∫ x, ‖(fn n * g) x - (f * g) x‖ ^ 2 ∂(μ.assoc ψ)) atTop (𝓝 0) := by
      have h0 : (0 : ℝ) = ∫ x, (0 : ℝ) ∂(μ.assoc ψ) := by simp
      rw [h0]
      refine tendsto_integral_of_dominated_convergence (fun _ => (2 * C) ^ 2) ?_
        (integrable_const _) ?_ ?_
      · intro n
        exact ((((hfn n).1.mul hg.1).sub (hf.mul hg.1)).norm.pow_const 2).aestronglyMeasurable
      · intro n
        refine Eventually.of_forall fun x => ?_
        have hb1 : ‖(fn n * g) x‖ ≤ C := by
          simp only [Pi.mul_apply, fn]
          by_cases hx : x ∈ {x | ‖f x‖ < n}
          · rw [Set.indicator_of_mem hx]; simpa using hC x
          · rw [Set.indicator_of_notMem hx, zero_mul, norm_zero]
            exact (norm_nonneg _).trans (hC x)
        have hb : ‖(fn n * g) x - (f * g) x‖ ≤ 2 * C :=
          (norm_sub_le _ _).trans (by linarith [hC x])
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) hb 2
      · refine Eventually.of_forall fun x => ?_
        obtain ⟨N, hN⟩ := exists_nat_gt ‖f x‖
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop N] with n hn
        have hx : x ∈ {x | ‖f x‖ < n} := by
          show ‖f x‖ < n
          exact lt_of_lt_of_le hN (by exact_mod_cast hn)
        simp [fn, Pi.mul_apply, Set.indicator_of_mem hx]
    have hsq' : Tendsto (fun n => ‖μ.integral (fn n * g) ψ - μ.integral (f * g) ψ‖ ^ 2) atTop
        (𝓝 0) := by
      refine hsq.congr fun n => ?_
      rw [norm_sq_integral_sub μ (bdd_mul (hfn n) hg) ⟨‹_›, C, hC⟩]
    have := (Real.continuous_sqrt.tendsto 0).comp hsq'
    simp only [Function.comp_def, Real.sqrt_zero] at this
    exact this.congr fun n => by rw [Real.sqrt_sq (norm_nonneg _)]
  exact tendsto_nhds_unique h1 (h2.congr fun n => (e n).symm)

/-- `‖c • f(A)ψ - g(A)ψ‖² = ∫ |c f - g|² dμ_ψ` for measurable `f`, `ψ ∈ Dom f(A)`, bounded `g`. -/
theorem norm_sq_smul_pmapIntegral_sub (c : ℂ) {f g : X → ℂ} (hf : Measurable f)
    (hg : g ∈ BddMeasurable X) (ψ : integralDomain μ f) :
    ‖c • pmapIntegral μ f ψ - μ.integral g ψ‖ ^ 2
      = ∫ x, ‖c * f x - g x‖ ^ 2 ∂(μ.assoc (ψ : H)) := by
  set fn : ℕ → X → ℂ := fun n => {x | ‖f x‖ < n}.indicator f
  have hfn : ∀ n, fn n ∈ BddMeasurable X := fun n => indicator_lt_mem_bddMeasurable hf n
  have h1 := tendsto_integral_truncation μ hf ψ
  have hL : Tendsto (fun n => ‖c • μ.integral (fn n) (ψ : H) - μ.integral g ψ‖ ^ 2) atTop
      (𝓝 (‖c • pmapIntegral μ f ψ - μ.integral g ψ‖ ^ 2)) :=
    (((h1.const_smul c).sub tendsto_const_nhds).norm).pow 2
  have hR : ∀ n, ‖c • μ.integral (fn n) (ψ : H) - μ.integral g ψ‖ ^ 2
      = ∫ x, ‖c * fn n x - g x‖ ^ 2 ∂(μ.assoc (ψ : H)) := by
    intro n
    have hc : c • fn n ∈ BddMeasurable X := (BddMeasurable X).smul_mem c (hfn n)
    rw [show c • μ.integral (fn n) (ψ : H) = (c • μ.integral (fn n)) (ψ : H) from rfl,
      ← ProjectionValuedMeasure.integral_smul μ c (hfn n), norm_sq_integral_sub μ hc hg]
    rfl
  obtain ⟨hgm, C, hC⟩ := hg
  have hint : Integrable (fun x => 2 * ‖c‖ ^ 2 * ‖f x‖ ^ 2 + 2 * C ^ 2) (μ.assoc (ψ : H)) :=
    ((ψ.2.integrable_norm_pow two_ne_zero).const_mul _).add (integrable_const _)
  have hlim : Tendsto (fun n => ∫ x, ‖c * fn n x - g x‖ ^ 2 ∂(μ.assoc (ψ : H))) atTop
      (𝓝 (∫ x, ‖c * f x - g x‖ ^ 2 ∂(μ.assoc (ψ : H)))) := by
    refine tendsto_integral_of_dominated_convergence (fun x => 2 * ‖c‖ ^ 2 * ‖f x‖ ^ 2 + 2 * C ^ 2)
      (fun n => ((((hfn n).1.const_mul c).sub hgm).norm.pow_const 2).aestronglyMeasurable) hint
      (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · have hfnx : ‖fn n x‖ ≤ ‖f x‖ := norm_indicator_le_norm_self f x
      have hgx := hC x
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have h2 : ‖c * fn n x - g x‖ ≤ ‖c‖ * ‖f x‖ + C := by
        calc ‖c * fn n x - g x‖ ≤ ‖c * fn n x‖ + ‖g x‖ := norm_sub_le _ _
          _ ≤ ‖c‖ * ‖f x‖ + C := by rw [norm_mul]; gcongr
      have h3 : 0 ≤ ‖c * fn n x - g x‖ := norm_nonneg _
      nlinarith [sq_nonneg (‖c‖ * ‖f x‖ - C), norm_nonneg c, norm_nonneg (f x)]
    · obtain ⟨N, hN⟩ := exists_nat_gt ‖f x‖
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop N] with n hn
      have hx : x ∈ {x | ‖f x‖ < n} := lt_of_lt_of_le hN (by exact_mod_cast hn)
      simp [fn, Set.indicator_of_mem hx]
  exact tendsto_nhds_unique hL (by simp_rw [hR]; exact hlim)

lemma assoc_integral_eq {g : X → ℂ} (hg : g ∈ BddMeasurable X) (ψ : H) :
    μ.assoc (μ.integral g ψ) = (μ.assoc ψ).withDensity fun x => ENNReal.ofReal (‖g x‖ ^ 2) := by
  ext E hE
  rw [assoc_integral_apply μ hg ψ hE, withDensity_apply _ hE]

/-- `g(A)ψ ∈ Dom f(A)` when `ψ ∈ Dom (f g)(A)`. -/
theorem integral_apply_mem_of_mem {f g : X → ℂ} (hf : Measurable f) (hg : g ∈ BddMeasurable X)
    {ψ : H} (hψ : ψ ∈ integralDomain μ (f * g)) : μ.integral g ψ ∈ integralDomain μ f := by
  have hgm : Measurable g := hg.1
  rw [mem_integralDomain, memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero
    ENNReal.ofNat_ne_top hf.aestronglyMeasurable]
  have hfg := hψ
  rw [mem_integralDomain, memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero
    ENNReal.ofNat_ne_top (hf.mul hgm).aestronglyMeasurable] at hfg
  have hm : Measurable fun x => ‖f x‖ₑ ^ (2 : ℝ≥0∞).toReal := hf.enorm.pow_const _
  have hdm : Measurable fun x => ENNReal.ofReal (‖g x‖ ^ 2) :=
    ENNReal.measurable_ofReal.comp (hgm.norm.pow_const 2)
  rw [assoc_integral_eq μ hg, lintegral_withDensity_eq_lintegral_mul _ hdm hm]
  refine lt_of_le_of_lt (le_of_eq ?_) hfg
  congr 1
  funext x
  simp only [Pi.mul_apply, ENNReal.toReal_ofNat]
  rw [← ofReal_norm, ← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
    ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num), ← ENNReal.ofReal_mul (by positivity),
    norm_mul]
  congr 1
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, Real.rpow_natCast]
  ring

/-- **SPEC-COMP, general form**: `f(A) g(A) ψ = (f g)(A) ψ` for bounded `g` and `ψ ∈ Dom (f g)(A)`. -/
theorem pmapIntegral_integral_apply_of_mem {f g : X → ℂ} (hf : Measurable f)
    (hg : g ∈ BddMeasurable X) {ψ : H} (hψ : ψ ∈ integralDomain μ (f * g)) :
    pmapIntegral μ f ⟨μ.integral g ψ, integral_apply_mem_of_mem μ hf hg hψ⟩
      = pmapIntegral μ (f * g) ⟨ψ, hψ⟩ := by
  set η : integralDomain μ f := ⟨μ.integral g ψ, integral_apply_mem_of_mem μ hf hg hψ⟩
  have hfgm : Measurable (f * g) := hf.mul hg.1
  have h1 := tendsto_integral_truncation μ hf η
  set fn : ℕ → X → ℂ := fun n => {x | ‖f x‖ < n}.indicator f
  have hfn : ∀ n, fn n ∈ BddMeasurable X := fun n => indicator_lt_mem_bddMeasurable hf n
  have e : ∀ n, μ.integral (fn n) (η : H) = μ.integral (fn n * g) ψ := fun n => by
    rw [ProjectionValuedMeasure.integral_mul μ (hfn n) hg]; rfl
  have h2 : Tendsto (fun n => μ.integral (fn n * g) ψ) atTop (𝓝 (pmapIntegral μ (f * g) ⟨ψ, hψ⟩)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hsq : ∀ n, ‖μ.integral (fn n * g) ψ - pmapIntegral μ (f * g) ⟨ψ, hψ⟩‖ ^ 2
        = ∫ x, ‖1 * (f * g) x - (fn n * g) x‖ ^ 2 ∂(μ.assoc ψ) := fun n => by
      have := norm_sq_smul_pmapIntegral_sub μ 1 hfgm (bdd_mul (hfn n) hg) ⟨ψ, hψ⟩
      rw [one_smul] at this
      rw [norm_sub_rev]
      exact this
    have hint : Integrable (fun x => 4 * ‖(f * g) x‖ ^ 2) (μ.assoc ψ) :=
      (hψ.integrable_norm_pow two_ne_zero).const_mul _
    have hlim : Tendsto (fun n => ∫ x, ‖1 * (f * g) x - (fn n * g) x‖ ^ 2 ∂(μ.assoc ψ)) atTop (𝓝 0) := by
      suffices key : Tendsto (fun n => ∫ x, ‖1 * (f * g) x - (fn n * g) x‖ ^ 2 ∂(μ.assoc ψ)) atTop
          (𝓝 (∫ x, (0 : ℝ) ∂(μ.assoc ψ))) by simpa using key
      refine tendsto_integral_of_dominated_convergence (fun x => 4 * ‖(f * g) x‖ ^ 2)
        (fun n => (((hfgm.const_mul 1).sub ((hfn n).1.mul hg.1)).norm.pow_const 2).aestronglyMeasurable)
        hint (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
      · have hb : ‖(fn n * g) x‖ ≤ ‖(f * g) x‖ := by
          simp only [Pi.mul_apply, norm_mul]
          gcongr
          exact norm_indicator_le_norm_self f x
        have h2 : ‖1 * (f * g) x - (fn n * g) x‖ ≤ 2 * ‖(f * g) x‖ := by
          rw [one_mul]; exact (norm_sub_le _ _).trans (by linarith)
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        calc ‖1 * (f * g) x - (fn n * g) x‖ ^ 2 ≤ (2 * ‖(f * g) x‖) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) h2 2
          _ = 4 * ‖(f * g) x‖ ^ 2 := by ring
      · obtain ⟨N, hN⟩ := exists_nat_gt ‖f x‖
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop N] with n hn
        have hx : x ∈ {x | ‖f x‖ < n} := lt_of_lt_of_le hN (by exact_mod_cast hn)
        simp [fn, Set.indicator_of_mem hx]
    have hsq' : Tendsto (fun n => ‖μ.integral (fn n * g) ψ - pmapIntegral μ (f * g) ⟨ψ, hψ⟩‖ ^ 2)
        atTop (𝓝 0) := by simp_rw [hsq]; exact hlim
    have := (Real.continuous_sqrt.tendsto 0).comp hsq'
    simp only [Function.comp_def, Real.sqrt_zero] at this
    exact this.congr fun n => by rw [Real.sqrt_sq (norm_nonneg _)]
  exact tendsto_nhds_unique h1 (h2.congr fun n => (e n).symm)

/-- `Dom f(A) ⊆ Dom (g f)(A)` for bounded `g`. -/
lemma mem_integralDomain_mul_of_bdd {f g : X → ℂ} (hf : Measurable f) (hg : g ∈ BddMeasurable X)
    {ψ : H} (hψ : ψ ∈ integralDomain μ f) : ψ ∈ integralDomain μ (g * f) := by
  obtain ⟨hgm, C, hC⟩ := hg
  rw [mem_integralDomain] at hψ ⊢
  refine hψ.of_le_mul (c := C) (hgm.mul hf).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  rw [Pi.mul_apply, norm_mul]
  exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)

/-- **SPEC-COMP, other order**: `g(A) f(A) ψ = (g f)(A) ψ` for bounded `g` and `ψ ∈ Dom f(A)`. -/
theorem integral_pmapIntegral_apply {f g : X → ℂ} (hf : Measurable f) (hg : g ∈ BddMeasurable X)
    (ψ : integralDomain μ f) :
    μ.integral g (pmapIntegral μ f ψ)
      = pmapIntegral μ (g * f) ⟨ψ, mem_integralDomain_mul_of_bdd μ hf hg ψ.2⟩ := by
  have hψ' := mem_integralDomain_mul_of_bdd μ hf hg ψ.2
  have hgfm : Measurable (g * f) := hg.1.mul hf
  set fn : ℕ → X → ℂ := fun n => {x | ‖f x‖ < n}.indicator f
  have hfn : ∀ n, fn n ∈ BddMeasurable X := fun n => indicator_lt_mem_bddMeasurable hf n
  have h1 : Tendsto (fun n => μ.integral g (μ.integral (fn n) (ψ : H))) atTop
      (𝓝 (μ.integral g (pmapIntegral μ f ψ))) :=
    ((μ.integral g).continuous.tendsto _).comp (tendsto_integral_truncation μ hf ψ)
  have e : ∀ n, μ.integral g (μ.integral (fn n) (ψ : H)) = μ.integral (g * fn n) (ψ : H) := fun n => by
    rw [ProjectionValuedMeasure.integral_mul μ hg (hfn n)]; rfl
  obtain ⟨hgm, C, hC⟩ := hg
  have h2 : Tendsto (fun n => μ.integral (g * fn n) (ψ : H)) atTop
      (𝓝 (pmapIntegral μ (g * f) ⟨ψ, hψ'⟩)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hsq : ∀ n, ‖μ.integral (g * fn n) (ψ : H) - pmapIntegral μ (g * f) ⟨ψ, hψ'⟩‖ ^ 2
        = ∫ x, ‖1 * (g * f) x - (g * fn n) x‖ ^ 2 ∂(μ.assoc (ψ : H)) := fun n => by
      have := norm_sq_smul_pmapIntegral_sub μ 1 hgfm (bdd_mul ⟨hgm, C, hC⟩ (hfn n)) ⟨ψ, hψ'⟩
      rw [one_smul] at this
      rw [norm_sub_rev]
      exact this
    have hint : Integrable (fun x => 4 * ‖(g * f) x‖ ^ 2) (μ.assoc (ψ : H)) :=
      (hψ'.integrable_norm_pow two_ne_zero).const_mul _
    have hlim : Tendsto (fun n => ∫ x, ‖1 * (g * f) x - (g * fn n) x‖ ^ 2 ∂(μ.assoc (ψ : H))) atTop
        (𝓝 0) := by
      suffices key : Tendsto (fun n => ∫ x, ‖1 * (g * f) x - (g * fn n) x‖ ^ 2 ∂(μ.assoc (ψ : H)))
          atTop (𝓝 (∫ x, (0 : ℝ) ∂(μ.assoc (ψ : H)))) by simpa using key
      refine tendsto_integral_of_dominated_convergence (fun x => 4 * ‖(g * f) x‖ ^ 2)
        (fun n => (((hgfm.const_mul 1).sub (hgm.mul (hfn n).1)).norm.pow_const 2).aestronglyMeasurable)
        hint (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
      · have hb : ‖(g * fn n) x‖ ≤ ‖(g * f) x‖ := by
          simp only [Pi.mul_apply, norm_mul]
          gcongr
          exact norm_indicator_le_norm_self f x
        have h2 : ‖1 * (g * f) x - (g * fn n) x‖ ≤ 2 * ‖(g * f) x‖ := by
          rw [one_mul]; exact (norm_sub_le _ _).trans (by linarith)
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        calc ‖1 * (g * f) x - (g * fn n) x‖ ^ 2 ≤ (2 * ‖(g * f) x‖) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) h2 2
          _ = 4 * ‖(g * f) x‖ ^ 2 := by ring
      · obtain ⟨N, hN⟩ := exists_nat_gt ‖f x‖
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop N] with n hn
        have hx : x ∈ {x | ‖f x‖ < n} := lt_of_lt_of_le hN (by exact_mod_cast hn)
        simp [fn, Set.indicator_of_mem hx]
    have hsq' : Tendsto (fun n => ‖μ.integral (g * fn n) (ψ : H) - pmapIntegral μ (g * f) ⟨ψ, hψ'⟩‖ ^ 2)
        atTop (𝓝 0) := by simp_rw [hsq]; exact hlim
    have := (Real.continuous_sqrt.tendsto 0).comp hsq'
    simp only [Function.comp_def, Real.sqrt_zero] at this
    exact this.congr fun n => by rw [Real.sqrt_sq (norm_nonneg _)]
  exact tendsto_nhds_unique h1 (h2.congr fun n => (e n).symm)

end Qschubert
