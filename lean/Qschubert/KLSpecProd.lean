import Qschubert.KLSurf5

/-!
# Composition in the unbounded functional calculus, and `Δ_M^N`

Not in physicslib4; `SpecComp.lean` covers only one bounded factor.

* `assoc_pmap_apply`: `μ_{f(A)ψ}(E) = ∫_E |f|² dμ_ψ` for `ψ ∈ Dom f(A)`;
* `pmap_comp`: if `ψ ∈ Dom f(A)` and `f(A)ψ ∈ Dom g(A)` then `ψ ∈ Dom (gf)(A)` and `(gf)(A)ψ = g(A)f(A)ψ`;
* `lapPowM_of_lapIter`, `errNormM_of_lapIter`: `LapIterM` computes `lapPowM` (the functional-calculus power in the
  statement of Theorem 1.4R);
* `LapIterM.prop`: `U_M(t)` commutes with `Δ_M^N`.
-/

namespace Qschubert

open MeasureTheory Filter Topology Physicslib4.Spectral Physicslib4.Spectral.Unbounded
open scoped ENNReal InnerProductSpace MatrixGroups UpperHalfPlane

section comp

variable {X : Type*} [MeasurableSpace X] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] (μ : ProjectionValuedMeasure X H)

/-- `μ_{f(A)ψ}(E) = ∫_E |f|² dμ_ψ`. -/
theorem assoc_pmap_apply {f : X → ℂ} (hf : Measurable f) (ψ : integralDomain μ f) {E : Set X} (hE : MeasurableSet E) :
    (μ.assoc (pmapIntegral μ f ψ)) E = ∫⁻ x in E, ‖f x‖ₑ ^ 2 ∂(μ.assoc (ψ : H)) := by
  set fn : ℕ → X → ℂ := fun n => {x | ‖f x‖ < n}.indicator f with hfn
  have hb : ∀ n, fn n ∈ BddMeasurable X := fun n => indicator_lt_mem_bddMeasurable hf n
  have h1 := tendsto_integral_truncation μ hf ψ
  have hL : Tendsto (fun n => μ.assoc (μ.integral (fn n) (ψ : H)) E) atTop
      (𝓝 (μ.assoc (pmapIntegral μ f ψ) E)) := by
    simp only [assoc_apply_eq_norm_sq μ _ hE]
    exact ENNReal.tendsto_ofReal ((((μ E).continuous.tendsto _).comp h1).norm.pow 2)
  have e : ∀ n, μ.assoc (μ.integral (fn n) (ψ : H)) E = ∫⁻ x in E, ‖fn n x‖ₑ ^ 2 ∂(μ.assoc (ψ : H)) := fun n => by
    rw [assoc_integral_apply μ (hb n) _ hE]
    refine lintegral_congr fun x => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  simp_rw [e] at hL
  refine tendsto_nhds_unique hL ?_
  have hmeas : ∀ n, Measurable fun x => ‖fn n x‖ₑ ^ 2 := fun n => (hb n).1.enorm.pow_const 2
  have hmono : Monotone fun n x => ‖fn n x‖ₑ ^ 2 := fun n m hnm x => by
    refine pow_le_pow_left₀ zero_le ?_ 2
    by_cases hx : ‖f x‖ < n
    · have hx' : ‖f x‖ < m := hx.trans_le (by exact_mod_cast hnm)
      simp only [hfn, Set.indicator_apply, Set.mem_setOf_eq, hx, hx', if_true, le_refl]
    · simp only [hfn, Set.indicator_apply, Set.mem_setOf_eq, hx, if_false, enorm_zero, zero_le]
  have hsup : ∀ x, Tendsto (fun n => ‖fn n x‖ₑ ^ 2) atTop (𝓝 (‖f x‖ₑ ^ 2)) := fun x => by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [tendsto_natCast_atTop_atTop.eventually_gt_atTop ‖f x‖] with n hn
    simp only [hfn, Set.indicator_apply, Set.mem_setOf_eq, hn, if_true]
  have := lintegral_tendsto_of_tendsto_of_monotone (μ := (μ.assoc (ψ : H)).restrict E)
    (f := fun n x => ‖fn n x‖ₑ ^ 2) (F := fun x => ‖f x‖ₑ ^ 2)
    (fun n => (hmeas n).aemeasurable) (Eventually.of_forall fun x n m hnm => hmono hnm x)
    (Eventually.of_forall hsup)
  exact this

/-- `μ_{f(A)ψ} = |f|² μ_ψ`. -/
theorem assoc_pmap {f : X → ℂ} (hf : Measurable f) (ψ : integralDomain μ f) :
    μ.assoc (pmapIntegral μ f ψ) = (μ.assoc (ψ : H)).withDensity fun x => ‖f x‖ₑ ^ 2 := by
  refine Measure.ext fun E hE => ?_
  rw [assoc_pmap_apply μ hf ψ hE, withDensity_apply _ hE]

/-- `μ(B_n) χ → χ` when the `B_n` increase to everything. -/
lemma tendsto_indicator_apply {g : X → ℂ} (hg : Measurable g) (χ : H) :
    Tendsto (fun n : ℕ => μ.integral ({x | ‖g x‖ < n}.indicator 1) χ) atTop (𝓝 χ) := by
  set B : ℕ → Set X := fun n => {x | ‖g x‖ < n}
  have hB : ∀ n, MeasurableSet (B n) := fun n => measurableSet_lt hg.norm measurable_const
  have hbd : ∀ n, (B n).indicator (1 : X → ℂ) ∈ BddMeasurable X := fun n =>
    ⟨measurable_one.indicator (hB n), 1, fun x => by by_cases hx : x ∈ B n <;> simp [hx]⟩
  have hbc : ∀ n, (B n)ᶜ.indicator (1 : X → ℂ) ∈ BddMeasurable X := fun n =>
    ⟨measurable_one.indicator (hB n).compl, 1, fun x => by by_cases hx : x ∈ B n <;> simp [hx]⟩
  have hsplit : ∀ n, χ - μ.integral ((B n).indicator 1) χ = μ.integral ((B n)ᶜ.indicator 1) χ := fun n => by
    have h1 : (B n).indicator (1 : X → ℂ) + (B n)ᶜ.indicator 1 = 1 := by
      funext x; by_cases hx : x ∈ B n <;> simp [hx]
    have h2 := μ.integral_add (hbd n) (hbc n)
    rw [h1, μ.integral_one] at h2
    have h3 := congrArg (fun T : H →L[ℂ] H => T χ) h2
    simp only [ContinuousLinearMap.one_apply, ContinuousLinearMap.add_apply] at h3
    exact sub_eq_of_eq_add' h3
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsq : Tendsto (fun n => ‖μ.integral ((B n)ᶜ.indicator 1) χ‖ ^ 2) atTop (𝓝 0) := by
    simp only [norm_sq_integral_apply μ (hbc _)]
    have := tendsto_integral_of_dominated_convergence (μ := μ.assoc χ) (fun _ : X => (1 : ℝ))
      (F := fun n x => ‖(B n)ᶜ.indicator (1 : X → ℂ) x‖ ^ 2) (f := fun _ => 0)
      (fun n => ((hbc n).1.norm.pow_const 2).aestronglyMeasurable) (integrable_const _)
      (fun n => ae_of_all _ fun x => by by_cases hx : x ∈ B n <;> simp [hx])
      (ae_of_all _ fun x => tendsto_const_nhds.congr' ?_)
    · simpa using this
    · filter_upwards [tendsto_natCast_atTop_atTop.eventually_gt_atTop ‖g x‖] with n hn
      have hx : x ∈ B n := hn
      simp [hx]
  have hs := hsq.sqrt
  simp only [Real.sqrt_zero, Real.sqrt_sq (norm_nonneg _)] at hs
  refine hs.congr fun n => ?_
  rw [← hsplit, norm_sub_rev]

/-- **Composition**: `(g f)(A) ψ = g(A) f(A) ψ`. -/
theorem pmap_comp {f g : X → ℂ} (hf : Measurable f) (hg : Measurable g) (ψ : integralDomain μ f)
    (hφ : pmapIntegral μ f ψ ∈ integralDomain μ g) :
    ∃ h : (ψ : H) ∈ integralDomain μ (g * f), pmapIntegral μ (g * f) ⟨ψ, h⟩ = pmapIntegral μ g ⟨_, hφ⟩ := by
  have hd : Measurable fun x => ‖f x‖ₑ ^ 2 := hf.enorm.pow_const 2
  have hgfm : Measurable (g * f) := hg.mul hf
  have hmem : (ψ : H) ∈ integralDomain μ (g * f) := by
    have h0 := (mem_integralDomain μ).1 hφ
    rw [assoc_pmap μ hf ψ] at h0
    have hgr : AEStronglyMeasurable g ((μ.assoc (ψ : H)).withDensity fun x => ‖f x‖ₑ ^ 2) := hg.aestronglyMeasurable
    rw [memLp_two_iff_integrable_sq_norm hgr, integrable_withDensity_iff_integrable_smul' hd
      (Eventually.of_forall fun _ => ENNReal.pow_lt_top enorm_lt_top)] at h0
    rw [mem_integralDomain, memLp_two_iff_integrable_sq_norm hgfm.aestronglyMeasurable]
    refine (integrable_congr (Eventually.of_forall fun x => ?_)).1 h0
    simp only [ENNReal.toReal_pow, toReal_enorm, smul_eq_mul, Pi.mul_apply, norm_mul, mul_pow]
    ring
  refine ⟨hmem, ?_⟩
  set χ := pmapIntegral μ (g * f) ⟨ψ, hmem⟩ with hχ
  set gn : ℕ → X → ℂ := fun n => {x | ‖g x‖ < n}.indicator g with hgn
  have hb : ∀ n, gn n ∈ BddMeasurable X := fun n => indicator_lt_mem_bddMeasurable hg n
  have hB : ∀ n : ℕ, MeasurableSet {x | ‖g x‖ < (n : ℝ)} := fun n => measurableSet_lt hg.norm measurable_const
  have hbi : ∀ n : ℕ, {x | ‖g x‖ < (n : ℝ)}.indicator (1 : X → ℂ) ∈ BddMeasurable X := fun n =>
    ⟨measurable_one.indicator (hB n), 1, fun x => by by_cases hx : x ∈ {x | ‖g x‖ < (n : ℝ)} <;> simp [hx]⟩
  have h1 := tendsto_integral_truncation μ hg ⟨_, hφ⟩
  have key : ∀ n : ℕ, μ.integral (gn n) (pmapIntegral μ f ψ)
      = μ.integral ({x | ‖g x‖ < (n : ℝ)}.indicator 1) χ := fun n => by
    have e1 := integral_pmapIntegral_apply μ hf (hb n) ψ
    have e2 := integral_pmapIntegral_apply μ hgfm (hbi n) ⟨ψ, hmem⟩
    refine e1.trans (Eq.trans ?_ e2.symm)
    refine pmapIntegral_congr_fun μ ?_ _ _ _
    funext x
    by_cases hx : ‖g x‖ < (n : ℝ)
    · simp only [hgn, Pi.mul_apply, Set.indicator_apply, Set.mem_setOf_eq, hx, ite_true, Pi.one_apply, one_mul]
    · simp only [hgn, Pi.mul_apply, Set.indicator_apply, Set.mem_setOf_eq, hx, ite_false, zero_mul]
  have h2 := tendsto_indicator_apply μ hg χ
  refine tendsto_nhds_unique h2 (h1.congr fun n => ?_)
  exact key n

end comp

variable {Γ : Subgroup PGL(2, ℝ)} [ProperlyDiscontinuousSMul Γ ℍ]

local notation "L2M" => Lp ℂ 2 (surfMeasure Γ)

/-- `Δ_M`, as the multiplier `-s`. -/
lemma pmap_neg_id (u : L2M) (hu : u ∈ (negLapMH Γ).domain) :
    ∃ h : u ∈ integralDomain (spectralMeasure (negLapMH_isSelfAdjoint Γ)) (fun s : ℝ => ((-s : ℝ) : ℂ)),
      pmapIntegral (spectralMeasure (negLapMH_isSelfAdjoint Γ)) (fun s : ℝ => ((-s : ℝ) : ℂ)) ⟨u, h⟩ = -negLapMH Γ ⟨u, hu⟩ := by
  set μ := spectralMeasure (negLapMH_isSelfAdjoint Γ)
  have hid : Measurable fun x : ℝ => (x : ℂ) := Complex.measurable_ofReal
  have hu' : u ∈ integralDomain μ (fun x : ℝ => (x : ℂ)) := by
    rw [← A_domain_eq (negLapMH_isSelfAdjoint Γ)]; exact hu
  have hc : (fun _ : ℝ => (-1 : ℂ)) ∈ BddMeasurable ℝ := ⟨measurable_const, 1, fun _ => by simp⟩
  have e := integral_pmapIntegral_apply μ hid hc ⟨u, hu'⟩
  have hfun : (fun _ : ℝ => (-1 : ℂ)) * (fun x : ℝ => (x : ℂ)) = fun s : ℝ => ((-s : ℝ) : ℂ) := by
    funext s; simp
  have hmem : u ∈ integralDomain μ (fun s : ℝ => ((-s : ℝ) : ℂ)) := hfun ▸ mem_integralDomain_mul_of_bdd μ hid hc hu'
  refine ⟨hmem, ?_⟩
  have e2 := pmapIntegral_congr_fun μ hfun u (mem_integralDomain_mul_of_bdd μ hid hc hu') hmem
  rw [← e2, ← e]
  have hA : negLapMH Γ ⟨u, hu⟩ = pmapIntegral μ (fun x : ℝ => (x : ℂ)) ⟨u, hu'⟩ :=
    (LinearPMap.ext_iff.mp (A_eq_pmapIntegral (negLapMH_isSelfAdjoint Γ))).2 (x := u) (hf := hu) (hg := hu')
  rw [hA]
  have hsm : (fun _ : ℝ => (-1 : ℂ)) = (-1 : ℂ) • (1 : ℝ → ℂ) := by funext s; simp
  have h1b : (1 : ℝ → ℂ) ∈ BddMeasurable ℝ := ⟨measurable_one, 1, fun _ => by simp⟩
  rw [hsm, μ.integral_smul _ h1b, μ.integral_one]
  simp

/-- `LapIterM` computes the functional-calculus power `Δ_M^N`. -/
theorem lapPowM_of_lapIter : ∀ (N : ℕ) {u v : L2M}, LapIterM Γ N u v →
    ∃ h : u ∈ (lapPowM Γ N).domain, lapPowM Γ N ⟨u, h⟩ = v
  | 0, u, v, h => by
      obtain rfl : u = v := h
      have hf : (fun s : ℝ => (((-s) ^ 0 : ℝ) : ℂ)) = 1 := by funext s; simp
      have hb : Measurable (fun s : ℝ => (((-s) ^ 0 : ℝ) : ℂ)) ∧
          ∃ C, ∀ s : ℝ, ‖(((-s) ^ 0 : ℝ) : ℂ)‖ ≤ C := ⟨Continuous.measurable (by fun_prop), ⟨1, fun s => by simp⟩⟩
      have hdom : u ∈ (lapPowM Γ 0).domain := by
        rw [lapPowM, (functionalCalculus_of_bddMeasurable (negLapMH_isSelfAdjoint Γ) hb).1]; trivial
      exact ⟨hdom, functionalCalculus_eq_one_apply Γ hf hb u hdom⟩
  | N + 1, u, v, ⟨hu, hi⟩ => by
      obtain ⟨hw, ew⟩ := lapPowM_of_lapIter N hi
      obtain ⟨hn, en⟩ := pmap_neg_id u hu
      set μ := spectralMeasure (negLapMH_isSelfAdjoint Γ)
      have hf : Measurable fun s : ℝ => ((-s : ℝ) : ℂ) := by fun_prop
      have hg : Measurable fun s : ℝ => (((-s) ^ N : ℝ) : ℂ) := by fun_prop
      have hw' : pmapIntegral μ (fun s : ℝ => ((-s : ℝ) : ℂ)) ⟨u, hn⟩
          ∈ integralDomain μ (fun s : ℝ => (((-s) ^ N : ℝ) : ℂ)) := by
        rw [en]; exact hw
      obtain ⟨hmem, ev⟩ := pmap_comp μ hf hg ⟨u, hn⟩ hw'
      have hfun : (fun s : ℝ => (((-s) ^ N : ℝ) : ℂ)) * (fun s : ℝ => ((-s : ℝ) : ℂ))
          = fun s : ℝ => (((-s) ^ (N + 1) : ℝ) : ℂ) := by
        funext s; simp [pow_succ]
      have hd : u ∈ (lapPowM Γ (N + 1)).domain := by
        show u ∈ integralDomain μ (fun s : ℝ => (((-s) ^ (N + 1) : ℝ) : ℂ))
        rw [← hfun]; exact hmem
      refine ⟨hd, ?_⟩
      have e1 : lapPowM Γ (N + 1) ⟨u, hd⟩ = pmapIntegral μ ((fun s : ℝ => (((-s) ^ N : ℝ) : ℂ)) * (fun s : ℝ => ((-s : ℝ) : ℂ))) ⟨u, hmem⟩ :=
        (pmapIntegral_congr_fun μ hfun u hmem hd).symm
      rw [e1, ev]
      have e2 : pmapIntegral μ (fun s : ℝ => (((-s) ^ N : ℝ) : ℂ)) ⟨_, hw'⟩ = lapPowM Γ N ⟨-negLapMH Γ ⟨u, hu⟩, hw⟩ := by
        show pmapIntegral μ _ _ = pmapIntegral μ _ _
        congr 1
        exact Subtype.ext en
      exact e2.trans ew

theorem errNormM_of_lapIter {N : ℕ} {u v : L2M} (h : LapIterM Γ N u v) : errNormM Γ N u = ‖v‖ₑ := by
  obtain ⟨hd, e⟩ := lapPowM_of_lapIter N h
  rw [errNormM, dite_eq_left hd, e]

/-- `U_M(t)` commutes with `Δ_M^N`. -/
theorem LapIterM.prop (hb t : ℝ) : ∀ (N : ℕ) {u v : L2M}, LapIterM Γ N u v →
    LapIterM Γ N (propCLM Γ hb t u) (propCLM Γ hb t v)
  | 0, u, v, h => by
      obtain rfl : u = v := h
      rfl
  | N + 1, u, v, ⟨h, hi⟩ => by
      obtain ⟨h', e⟩ := negLapMH_propCLM Γ hb t u h
      refine ⟨h', ?_⟩
      rw [e, ← map_neg]
      exact LapIterM.prop hb t N hi

end Qschubert
