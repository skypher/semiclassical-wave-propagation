import Qschubert.JEps

/-!
# SPEC-POS: the spectral measure of `-Δ` lives on `[0, ∞)`

For every `v ∈ L²(ℍ)`, the spectral measure `μ_v` of `negLapH` gives `(-∞, 0)` measure zero
(`assoc_Iio_zero`): on `E = [-n, -1/(n+1)]`, `ψ = 1_E(-Δ) v` has `μ_ψ = μ_v|_E`, so
`0 ≤ Re⟪ψ, -Δψ⟫ = ∫_E s dμ_v ≤ -μ_v(E)/(n+1)`. Consequently bounded spectral functions that agree
on `[0, ∞)` give the same operator (`integral_congr_nonneg`), and Schubert's mollifier is
`J_ε = j_ε(√(-Δ))` exactly, with `√` the real square root (`cutoffEps_J`).
-/

namespace Qschubert

open MeasureTheory Filter Topology Physicslib4.Spectral Physicslib4.Spectral.Unbounded
open scoped InnerProductSpace ENNReal

local notation "L2H" => Lp ℂ 2 (volume : Measure UpperHalfPlane)
local notation "μH" => spectralMeasure negLapH_isSelfAdjoint

lemma indicator_one_mem_bdd {E : Set ℝ} (hE : MeasurableSet E) :
    E.indicator (1 : ℝ → ℂ) ∈ BddMeasurable ℝ := by
  rw [mem_bddMeasurable]
  refine ⟨measurable_const.indicator hE, 1, fun x => ?_⟩
  by_cases hx : x ∈ E <;> simp [hx]

/-- `μ_{1_E(A) v} = μ_v|_E`. -/
lemma assoc_indicator {E : Set ℝ} (hE : MeasurableSet E) (v : L2H) :
    (μH).assoc ((μH).integral (E.indicator 1) v) = ((μH).assoc v).restrict E := by
  ext F hF
  rw [assoc_integral_apply _ (indicator_one_mem_bdd hE) v hF, Measure.restrict_apply hF]
  have e : (fun x => ENNReal.ofReal (‖E.indicator (1 : ℝ → ℂ) x‖ ^ 2)) = E.indicator 1 := by
    funext x; by_cases hx : x ∈ E <;> simp [hx]
  rw [e, lintegral_indicator_one hE, Measure.restrict_apply hE, Set.inter_comm]

lemma id_mul_indicator_mem {a b : ℝ} :
    (fun x : ℝ => (x : ℂ)) * (Set.Icc a b).indicator (1 : ℝ → ℂ) ∈ BddMeasurable ℝ := by
  rw [mem_bddMeasurable]
  refine ⟨Complex.measurable_ofReal.mul (measurable_const.indicator measurableSet_Icc), max |a| |b|, fun x => ?_⟩
  by_cases hx : x ∈ Set.Icc a b
  · simp only [Pi.mul_apply, Set.indicator_of_mem hx, Pi.one_apply, mul_one, Complex.norm_real,
      Real.norm_eq_abs]
    exact abs_le_max_abs_abs hx.1 hx.2
  · simp [hx]

/-- `μ_v([-n, -1/n]) = 0`. -/
lemma assoc_Icc_neg_zero (v : L2H) (n : ℕ) :
    (μH).assoc v (Set.Icc (-(n : ℝ)) (-(1 / ((n : ℝ) + 1)))) = 0 := by
  set E : Set ℝ := Set.Icc (-(n : ℝ)) (-(1 / ((n : ℝ) + 1)))
  set c : ℝ := 1 / ((n : ℝ) + 1)
  have hc : 0 < c := by positivity
  set ψ : L2H := (μH).integral (E.indicator 1) v
  have hmem : ψ ∈ integralDomain (μH) (fun x : ℝ => (x : ℂ)) :=
    integral_apply_mem_integralDomain _ Complex.measurable_ofReal (indicator_one_mem_bdd measurableSet_Icc)
      id_mul_indicator_mem v
  have hdom : ψ ∈ negLapH.domain := by rw [A_domain_eq negLapH_isSelfAdjoint]; exact hmem
  have hA : negLapH ⟨ψ, hdom⟩ = pmapIntegral (μH) (fun x : ℝ => (x : ℂ)) ⟨ψ, hmem⟩ :=
    (LinearPMap.ext_iff.mp (A_eq_pmapIntegral negLapH_isSelfAdjoint)).2 (x := ψ) (hf := hdom) (hg := hmem)
  have hpos : 0 ≤ (⟪ψ, negLapH ⟨ψ, hdom⟩⟫_ℂ).re := negLapH_isPositive.2 ⟨ψ, hdom⟩
  have hq : ⟪ψ, pmapIntegral (μH) (fun x : ℝ => (x : ℂ)) ⟨ψ, hmem⟩⟫_ℂ = ∫ x, (x : ℂ) ∂((μH).assoc ψ) :=
    inner_self_pmapIntegral (μH) (f := fun x : ℝ => (x : ℂ)) Complex.measurable_ofReal ⟨ψ, hmem⟩
  rw [hA, hq] at hpos
  rw [assoc_indicator measurableSet_Icc v] at hpos
  have hint : IntegrableOn (fun x : ℝ => x) E ((μH).assoc v) := continuous_id.integrableOn_Icc
  rw [show (∫ x, (x : ℂ) ∂(((μH).assoc v).restrict E)) = ((∫ x, x ∂(((μH).assoc v).restrict E) : ℝ) : ℂ)
    from integral_ofReal, Complex.ofReal_re] at hpos
  have hle : ∫ x in E, x ∂((μH).assoc v) ≤ ∫ x in E, (-c) ∂((μH).assoc v) :=
    setIntegral_mono_on hint (integrable_const _) measurableSet_Icc (fun x hx => hx.2)
  simp only [integral_const, smul_eq_mul, measureReal_def, Measure.restrict_apply_univ] at hle
  have hm : 0 ≤ (((μH).assoc v) E).toReal := ENNReal.toReal_nonneg
  have hm0 : (((μH).assoc v) E).toReal = 0 := by nlinarith
  rw [ENNReal.toReal_eq_zero_iff] at hm0
  exact hm0.resolve_right (measure_ne_top _ _)

lemma Iio_zero_eq_iUnion :
    Set.Iio (0 : ℝ) = ⋃ n : ℕ, Set.Icc (-(n : ℝ)) (-(1 / ((n : ℝ) + 1))) := by
  ext x
  simp only [Set.mem_Iio, Set.mem_iUnion, Set.mem_Icc]
  constructor
  · intro hx
    obtain ⟨n₁, hn₁⟩ := exists_nat_ge (-x)
    obtain ⟨n₂, hn₂⟩ := exists_nat_gt (1 / (-x))
    refine ⟨max n₁ n₂, ?_, ?_⟩
    · have : (n₁ : ℝ) ≤ (max n₁ n₂ : ℕ) := by exact_mod_cast le_max_left _ _
      linarith
    · have h2 : (n₂ : ℝ) ≤ (max n₁ n₂ : ℕ) := by exact_mod_cast le_max_right _ _
      have hpos : 0 < -x := by linarith
      have h3 : 1 / (-x) < (max n₁ n₂ : ℕ) + 1 := by linarith
      have h4 : 1 / (((max n₁ n₂ : ℕ) : ℝ) + 1) < -x := by
        rw [div_lt_iff₀ (by positivity)]
        rw [div_lt_iff₀ hpos] at h3
        linarith
      linarith
  · rintro ⟨n, _, h2⟩
    have : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith

/-- **SPEC-POS**: `μ_v((-∞, 0)) = 0` for every `v`. -/
theorem assoc_Iio_zero (v : L2H) : (μH).assoc v (Set.Iio 0) = 0 := by
  rw [Iio_zero_eq_iUnion]
  exact measure_iUnion_null fun n => assoc_Icc_neg_zero v n

/-- Bounded spectral functions of `-Δ` that agree on `[0, ∞)` give the same operator. -/
theorem integral_congr_nonneg {f g : ℝ → ℂ} (hf : f ∈ BddMeasurable ℝ) (hg : g ∈ BddMeasurable ℝ)
    (h : ∀ s, 0 ≤ s → f s = g s) : (μH).integral f = (μH).integral g := by
  refine ContinuousLinearMap.ext fun v => ?_
  have h1 := norm_sq_integral_sub (μH) hf hg v
  have hae : (fun x => ‖f x - g x‖ ^ 2) =ᵐ[(μH).assoc v] 0 := by
    have hnull : (μH).assoc v {x | ¬ (0 ≤ x)} = 0 := by
      have : {x : ℝ | ¬ (0 ≤ x)} = Set.Iio 0 := by ext x; simp
      rw [this]; exact assoc_Iio_zero v
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with x hx
    simp only [not_not] at hx
    simp [h x hx]
  rw [integral_congr_ae hae] at h1
  simp only [Pi.zero_apply, integral_zero] at h1
  have : ‖(μH).integral f v - (μH).integral g v‖ = 0 := by
    nlinarith [norm_nonneg ((μH).integral f v - (μH).integral g v)]
  exact sub_eq_zero.1 (norm_eq_zero.1 this)

/-- Schubert's mollifier is `J_ε = j_ε(√(-Δ))` with the real square root. -/
theorem cutoffEps_J (P : MollProfile) {ε : ℝ} (hε : 0 < ε) :
    (P.cutoffEps hε).J = (μH).integral (fun s => ((P.jEps ε (Real.sqrt s) : ℝ) : ℂ)) := by
  refine integral_congr_nonneg (P.cutoffEps hε).g_mem ?_ (fun s hs => ?_)
  · rw [mem_bddMeasurable]
    refine ⟨Complex.measurable_ofReal.comp ((P.continuous_jEps hε).comp Real.continuous_sqrt).measurable, 1,
      fun s => ?_⟩
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (P.jEps_nonneg _ _)]
    exact P.jEps_le_one _ _
  · show (((P.jEps ε (Real.sqrt |s|)) : ℝ) : ℂ) = _
    rw [abs_of_nonneg hs]

end Qschubert
