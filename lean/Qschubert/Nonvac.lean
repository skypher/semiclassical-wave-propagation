import Qschubert.Refutation

/-!
# Both amplitude classes contain nonzero amplitudes (NONVAC-1, norm level)

For `α ≥ 0`, `κ > 1`, `w = e^{-κX₀} ∈ L²(ℍ)` and `v = e^{-αΛ} w`:
* printed class: `v` has finite printed norm (`β = 1`, `supp_prNormCl2`) and `v ≠ 0`;
* swapped class (appendix form): `a = X₀^{-β} v` has `‖e^{αΛ} X₀^β a‖ = ‖w‖ < ∞` and `a ≠ 0` a.e.
The smooth-representative statements additionally need a `C^∞` representative (LIFT-1).
-/

namespace Qschubert

open MeasureTheory UpperHalfPlane Real
open scoped ENNReal

lemma coshD_pos (x₀ z : ℍ) : 0 < coshD x₀ z := Real.cosh_pos _

/-- `e^{-κX₀} ≠ 0` in `L²(ℍ)`. -/
lemma toLp_exp_neg_coshD_ne_zero {κ : ℝ} (hκ : 0 < κ) : (memLp_exp_neg_coshD hκ).toLp _ ≠ 0 := by
  intro h
  rw [Lp.eq_zero_iff_ae_eq_zero] at h
  have h2 := (memLp_exp_neg_coshD hκ).coeFn_toLp.symm.trans h
  have hne : ∀ z : ℍ, ((Real.exp (-κ * coshD I z) : ℝ) : ℂ) ≠ 0 := fun z => by
    exact_mod_cast (Real.exp_pos _).ne'
  have hnull : (volume : Measure ℍ) Set.univ = 0 := by
    have h3 : ∀ᵐ z ∂(volume : Measure ℍ), ((Real.exp (-κ * coshD I z) : ℝ) : ℂ) = 0 := h2
    rw [ae_iff] at h3
    simpa [hne] using h3
  exact (isOpen_univ.measure_pos (volume : Measure ℍ) Set.univ_nonempty).ne' hnull

/-- `e^{-αΛ}` is injective on the vector `e^{-κX₀}`: `e^{-αΛ} e^{-κX₀} ≠ 0`. -/
lemma expLambda_neg_ne_zero {α κ : ℝ} (hα : 0 ≤ α) (hκ : 0 < κ)
    (h : (memLp_exp_neg_coshD hκ).toLp _ ∈ (expLambda (-α)).domain) :
    (expLambda (-α) ⟨_, h⟩ : Lp ℂ 2 (volume : Measure ℍ)) ≠ 0 := by
  intro h0
  obtain ⟨h', hval⟩ := expLambda_comp_neg hα _ h
  have hz : (⟨_, h'⟩ : (expLambda α).domain) = 0 := Subtype.ext h0
  rw [hz, LinearPMap.map_zero] at hval
  exact toLp_exp_neg_coshD_ne_zero hκ hval.symm

/-- **Printed class is nonvacuous**: `e^{-αΛ}e^{-κX₀}` has finite printed norm (`β = 1`) and is not
`0` a.e. -/
theorem printed_class_nonvacuous {α κ : ℝ} (hα : 0 ≤ α) (hκ : 1 < κ) :
    prNormX I α 1 (ampCl2 α κ hα) < ⊤ ∧ ¬ (ampCl2 α κ hα =ᵐ[volume] 0) := by
  have hκ0 : 0 < κ := by linarith
  refine ⟨supp_prNormCl2 α κ hα hκ, ?_⟩
  rw [ampCl2_eq hα hκ0]
  intro h
  exact expLambda_neg_ne_zero hα hκ0 _ ((Lp.eq_zero_iff_ae_eq_zero).2 h)

/-- `swNormX` when the weighted function is (pointwise) an `L²` class in the domain of `e^{αΛ}`. -/
lemma swNormX_of_eq (x₀ : ℍ) (α β : ℝ) (a : ℍ → ℂ) (v : Lp ℂ 2 (volume : Measure ℍ))
    (hav : (fun z => ((coshD x₀ z ^ β : ℝ) : ℂ) * a z) = ⇑v) (h : v ∈ (expLambda α).domain) :
    swNormX x₀ α β a = ‖expLambda α ⟨v, h⟩‖ₑ := by
  classical
  have hm : MemLp (fun z => ((coshD x₀ z ^ β : ℝ) : ℂ) * a z) 2 (volume : Measure ℍ) := by
    rw [hav]; exact Lp.memLp v
  rw [swNormX, dite_eq_left hm]
  have e : hm.toLp _ = v := by
    rw [← Lp.toLp_coeFn v (Lp.memLp v)]
    exact MemLp.toLp_congr _ _ (Filter.EventuallyEq.of_eq hav)
  have key : ∀ u : Lp ℂ 2 (volume : Measure ℍ), u = v →
      (if hd : u ∈ (expLambda α).domain then ‖expLambda α ⟨u, hd⟩‖ₑ else ⊤)
        = ‖expLambda α ⟨v, h⟩‖ₑ := by
    rintro u rfl
    rw [dite_eq_left h]
  exact key _ e

/-- **Swapped class (appendix form) is nonvacuous**: `a = X₀^{-β} e^{-αΛ} e^{-κX₀}` has
`‖e^{αΛ} X₀^β a‖ = ‖e^{-κX₀}‖ < ∞` and is not `0` a.e. -/
theorem swapped_class_nonvacuous {α κ : ℝ} (β : ℝ) (hα : 0 ≤ α) (hκ : 0 < κ) :
    ∃ a : ℍ → ℂ, swNormX I α β a < ⊤ ∧ ¬ (a =ᵐ[volume] 0) := by
  have hw := memLp_exp_neg_coshD hκ
  have hdom : hw.toLp _ ∈ (expLambda (-α)).domain := by
    rw [expLambda_domain_eq_top (by linarith)]; trivial
  set v : Lp ℂ 2 (volume : Measure ℍ) := expLambda (-α) ⟨_, hdom⟩
  obtain ⟨h', hval⟩ := expLambda_comp_neg hα _ hdom
  refine ⟨fun z => ((coshD I z ^ (-β) : ℝ) : ℂ) * v z, ?_, ?_⟩
  · have hav : (fun z => ((coshD I z ^ β : ℝ) : ℂ) * (((coshD I z ^ (-β) : ℝ) : ℂ) * v z)) = ⇑v := by
      funext z
      rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.rpow_add (coshD_pos I z), add_neg_cancel,
        Real.rpow_zero, Complex.ofReal_one, one_mul]
    rw [swNormX_of_eq I α β _ v hav h', hval]
    exact enorm_lt_top
  · intro h0
    apply expLambda_neg_ne_zero hα hκ hdom
    rw [Lp.eq_zero_iff_ae_eq_zero]
    filter_upwards [h0] with z hz
    have hne : ((coshD I z ^ (-β) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.rpow_pos_of_pos (coshD_pos I z) _).ne'
    have hz' : ((coshD I z ^ (-β) : ℝ) : ℂ) * v z = 0 := hz
    exact (mul_eq_zero.1 hz').resolve_left hne

/-- The printed norm of `e^{-αΛ} e^{-κX₀}` is finite for every `β ≥ 0` and `κ > β`. -/
theorem prNormX_ampCl2_lt_top {α β κ : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hκ : β < κ) :
    prNormX I α β (ampCl2 α κ hα) < ⊤ := by
  have hκ0 : 0 < κ := by linarith
  have hw := memLp_exp_neg_coshD hκ0
  have hdom : hw.toLp _ ∈ (expLambda (-α)).domain := by
    rw [expLambda_domain_eq_top (by linarith)]; trivial
  obtain ⟨h', hval⟩ := expLambda_comp_neg hα (hw.toLp _) hdom
  rw [ampCl2_eq hα hκ0, prNormX_coe I α β _ h', hval]
  have hae : (fun z => ((Real.exp (β * angleDx I z) : ℝ) : ℂ) * (hw.toLp _ : Lp ℂ 2 (volume : Measure ℍ)) z)
      =ᵐ[volume] fun z => ((Real.exp (β * angleDx I z) : ℝ) : ℂ) * ((Real.exp (-κ * coshD I z) : ℝ) : ℂ) := by
    filter_upwards [hw.coeFn_toLp] with z hz
    rw [hz]
  rw [eLpNorm_congr_ae hae]
  have hw1 := memLp_exp_neg_coshD (show 0 < κ - β by linarith)
  have hcont : Continuous fun z : ℍ => coshD I z :=
    Real.continuous_cosh.comp (continuous_const.dist continuous_id)
  have hcontA : Continuous fun z : ℍ => angleDx I z :=
    (Real.continuous_sqrt.comp (continuous_const.add
      ((continuous_const.dist continuous_id).pow 2))).sub continuous_const
  have hmeas : AEStronglyMeasurable (fun z : ℍ => ((Real.exp (β * angleDx I z) : ℝ) : ℂ)
      * ((Real.exp (-κ * coshD I z) : ℝ) : ℂ)) (volume : Measure ℍ) :=
    ((Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul hcontA))).mul
      (Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul hcont)))).aestronglyMeasurable
  refine lt_of_le_of_lt (eLpNorm_mono hmeas fun z => ?_) hw1
  rw [norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _),
    abs_of_pos (Real.exp_pos _), ← Real.exp_add, Real.exp_le_exp]
  have := angleDx_le_coshD I z
  nlinarith

/-- **Printed class is nonvacuous for every `β ≥ 0`.** -/
theorem printed_class_nonvacuous_beta {α β κ : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hκ : β < κ) :
    prNormX I α β (ampCl2 α κ hα) < ⊤ ∧ ¬ (ampCl2 α κ hα =ᵐ[volume] 0) := by
  have hκ0 : 0 < κ := by linarith
  refine ⟨prNormX_ampCl2_lt_top hα hβ hκ, ?_⟩
  rw [ampCl2_eq hα hκ0]
  intro h
  exact expLambda_neg_ne_zero hα hκ0 _ ((Lp.eq_zero_iff_ae_eq_zero).2 h)

/-- `swNormD` when the weighted function is (pointwise) an `L²` class in the domain of `e^{αΛ}`. -/
lemma swNormD_of_eq (x₀ : ℍ) (α β : ℝ) (a : ℍ → ℂ) (v : Lp ℂ 2 (volume : Measure ℍ))
    (hav : (fun z => ((Real.exp (β * angleDx x₀ z) : ℝ) : ℂ) * a z) = ⇑v)
    (h : v ∈ (expLambda α).domain) :
    swNormD x₀ α β a = ‖expLambda α ⟨v, h⟩‖ₑ := by
  classical
  have hm : MemLp (fun z => ((Real.exp (β * angleDx x₀ z) : ℝ) : ℂ) * a z) 2 (volume : Measure ℍ) := by
    rw [hav]; exact Lp.memLp v
  rw [swNormD, dite_eq_left hm]
  have e : hm.toLp _ = v := by
    rw [← Lp.toLp_coeFn v (Lp.memLp v)]
    exact MemLp.toLp_congr _ _ (Filter.EventuallyEq.of_eq hav)
  have key : ∀ u : Lp ℂ 2 (volume : Measure ℍ), u = v →
      (if hd : u ∈ (expLambda α).domain then ‖expLambda α ⟨u, hd⟩‖ₑ else ⊤)
        = ‖expLambda α ⟨v, h⟩‖ₑ := by
    rintro u rfl
    rw [dite_eq_left h]
  exact key _ e

/-- **Swapped class (main-text form, weight `e^{β⟨d⟩}`) is nonvacuous**: `a = e^{-β⟨d⟩} e^{-αΛ} e^{-κX₀}`
has `‖e^{αΛ} e^{β⟨d⟩} a‖ = ‖e^{-κX₀}‖ < ∞` and is not `0` a.e. -/
theorem swappedD_class_nonvacuous {α κ : ℝ} (β : ℝ) (hα : 0 ≤ α) (hκ : 0 < κ) :
    ∃ a : ℍ → ℂ, swNormD I α β a < ⊤ ∧ ¬ (a =ᵐ[volume] 0) := by
  have hw := memLp_exp_neg_coshD hκ
  have hdom : hw.toLp _ ∈ (expLambda (-α)).domain := by
    rw [expLambda_domain_eq_top (by linarith)]; trivial
  set v : Lp ℂ 2 (volume : Measure ℍ) := expLambda (-α) ⟨_, hdom⟩
  obtain ⟨h', hval⟩ := expLambda_comp_neg hα _ hdom
  refine ⟨fun z => ((Real.exp (-β * angleDx I z) : ℝ) : ℂ) * v z, ?_, ?_⟩
  · have hav : (fun z => ((Real.exp (β * angleDx I z) : ℝ) : ℂ)
        * (((Real.exp (-β * angleDx I z) : ℝ) : ℂ) * v z)) = ⇑v := by
      funext z
      rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add,
        show β * angleDx I z + -β * angleDx I z = 0 by ring, Real.exp_zero, Complex.ofReal_one, one_mul]
    rw [swNormD_of_eq I α β _ v hav h', hval]
    exact enorm_lt_top
  · intro h0
    apply expLambda_neg_ne_zero hα hκ hdom
    rw [Lp.eq_zero_iff_ae_eq_zero]
    filter_upwards [h0] with z hz
    have hne : ((Real.exp (-β * angleDx I z) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.exp_pos _).ne'
    have hz' : ((Real.exp (-β * angleDx I z) : ℝ) : ℂ) * v z = 0 := hz
    exact (mul_eq_zero.1 hz').resolve_left hne

end Qschubert
