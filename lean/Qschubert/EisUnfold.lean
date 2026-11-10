import Qschubert.EisAbs
import Qschubert.UnfoldPair
import Qschubert.Density
import Qschubert.ZeroModeBounds

/-!
# Unfolding the pairing of an `L²` function with an incomplete Eisenstein series

Stage E of the plan for Proposition `ev:mod` (`lean/BLUEPRINT.md`), part E4. For `w ∈ L²(M)`, `M = PSL(2, ℤ)\ℍ`, and a
test function `g` on `(0, ∞)`, with `E_g = perio modGroup (stripFn g)`:

`∫_M w conj(E_g) dμ = ∫_ℍ w(π z) conj(stripFn g z) dν` (`integral_mul_conj_perio_stripFn`),

the integral of `w ∘ π` against `conj g(Im z)` over the strip `0 ≤ Re z < 1`.
-/

namespace Qschubert

open MeasureTheory Set Filter Topology UpperHalfPlane
open scoped Real MatrixGroups ENNReal ComplexConjugate

lemma perio_conj_stripFn (g : ℝ → ℂ) (x : Surf modGroup) :
    perio modGroup (fun z => conj (stripFn g z)) x = conj (perio modGroup (stripFn g) x) := by
  induction x using Quotient.inductionOn with | _ z => ?_
  show ∑' γ : modGroup, conj (stripFn g (γ • z)) = conj (∑' γ : modGroup, stripFn g (γ • z))
  rw [Complex.conj_tsum]

/-- `∫_ℍ |stripFn g| dν < ∞`. -/
lemma lintegral_stripFn_lt_top {g : ℝ → ℂ} (hg : IsKTest g) : ∫⁻ z : ℍ, ‖stripFn g z‖ₑ < ∞ := by
  rw [lintegral_H_slice' (measurable_stripFn hg).enorm]
  have hfin : ∫⁻ y in Ioi (0 : ℝ), ‖powR (-2) y * g y‖ₑ < ∞ :=
    lt_of_le_of_lt (setLIntegral_le_lintegral _ _) (hg.integrable_powR_mul (-2)).hasFiniteIntegral
  refine lt_of_le_of_lt (setLIntegral_mono' measurableSet_Ioi fun y hy => ?_) hfin
  have hy0 : (0 : ℝ) < y := hy
  have hinner : ∫⁻ x : ℝ, ‖stripFn g (UpperHalfPlane.ofComplex ⟨x, y⟩)‖ₑ ≤ ‖g y‖ₑ := by
    have e : ∀ x : ℝ, ‖stripFn g (UpperHalfPlane.ofComplex ⟨x, y⟩)‖ₑ = (Ico (0 : ℝ) 1).indicator (fun _ => ‖g y‖ₑ) x := by
      intro x
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos (show 0 < (⟨x, y⟩ : ℂ).im from hy0)]
      show ‖(if ⌊x⌋ = 0 then g y else 0)‖ₑ = _
      by_cases hx : ⌊x⌋ = 0
      · rw [ite_eq_left hx, Set.indicator_of_mem (Int.floor_eq_zero_iff.1 hx)]
      · rw [ite_eq_right hx, Set.indicator_of_notMem (fun h => hx (Int.floor_eq_zero_iff.2 h)), enorm_zero]
    simp_rw [e]
    rw [lintegral_indicator_const measurableSet_Ico, Real.volume_Ico]
    simp
  have hp : ‖powR (-2) y * g y‖ₑ = ENNReal.ofReal ((y ^ 2)⁻¹) * ‖g y‖ₑ := by
    rw [enorm_mul, ← ofReal_norm (powR (-2) y), norm_powR]
    congr 2
    have hre : ((-2 : ℂ)).re = -2 := by simp
    rw [hre, show (-2 : ℝ) * Real.log y = -(Real.log y + Real.log y) by ring, Real.exp_neg, Real.exp_add,
      Real.exp_log hy0, ← sq]
  rw [hp]
  exact mul_le_mul_right hinner _

/-- `(w ∘ π) conj(stripFn g)` is integrable on `ℍ` for `w ∈ L²(M)`. -/
theorem integrable_lift_mul_conj_stripFn {w : Surf modGroup → ℂ}
    (hwm : AEStronglyMeasurable w (surfMeasure modGroup)) (hw : MemLp w 2 (surfMeasure modGroup))
    {g : ℝ → ℂ} (hg : IsKTest g) :
    Integrable fun z : ℍ => w (surfMk modGroup z) * conj (stripFn g z) := by
  obtain ⟨M, hM, hMb⟩ := absSum_stripFn_le hg
  have hqmp := quasiMeasurePreserving_surfMk modGroup
  set w' : Surf modGroup → ℂ := hwm.mk w with hw'
  have hw'm : StronglyMeasurable w' := hwm.stronglyMeasurable_mk
  have hww' : w =ᵐ[surfMeasure modGroup] w' := hwm.ae_eq_mk
  have hlift : (fun z : ℍ => w (surfMk modGroup z)) =ᵐ[volume] fun z : ℍ => w' (surfMk modGroup z) :=
    hqmp.ae_eq_comp hww'
  have hum : Measurable fun z : ℍ => conj (stripFn g z) := Complex.continuous_conj.measurable.comp (measurable_stripFn hg)
  refine ⟨(hwm.comp_quasiMeasurePreserving hqmp).mul hum.aestronglyMeasurable, ?_⟩
  have hF := isFundamentalDomain_fdSet modGroup
  -- the two pieces
  set f : ℍ → ℝ≥0∞ := fun z => ‖w' (surfMk modGroup z)‖ₑ ^ 2 * ‖stripFn g z‖ₑ with hf
  have hfm : Measurable f :=
    ((hw'm.measurable.comp (measurable_surfMk modGroup)).enorm.pow_const 2).mul (measurable_stripFn hg).enorm
  have haut : ∀ x : Surf modGroup, MulAction.automorphize f x ≤ ENNReal.ofReal M * ‖w' x‖ₑ ^ 2 := by
    intro x
    induction x using Quotient.inductionOn with | _ z => ?_
    show ∑' γ : modGroup, f (γ • z) ≤ _
    have e : ∀ γ : modGroup, f (γ • z) = ‖w' (surfMk modGroup z)‖ₑ ^ 2 * ‖stripFn g (γ • z)‖ₑ := fun γ => by
      simp only [hf]
      rw [surfMk_smul]
    simp_rw [e]
    rw [ENNReal.tsum_mul_left, mul_comm]
    exact mul_le_mul' (hMb z) le_rfl
  have hw2 : ∫⁻ x, ‖w' x‖ₑ ^ 2 ∂surfMeasure modGroup < ∞ := by
    have h1 : eLpNorm w' 2 (surfMeasure modGroup) < ∞ := by
      rw [← eLpNorm_congr_ae hww']
      exact hw
    have h3 := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (p := 2) (by norm_num) (by norm_num)
      hw'm.aestronglyMeasurable).1 h1
    refine lt_of_eq_of_lt (lintegral_congr fun x => ?_) h3
    rw [show ((2 : ℝ≥0∞)).toReal = 2 by norm_num, ENNReal.rpow_two]
  have h1 : ∫⁻ z : ℍ, f z < ∞ := by
    rw [lintegral_eq_lintegral_automorphize modGroup hF hfm]
    refine lt_of_le_of_lt (lintegral_mono haut) ?_
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hw2
  have h2 := lintegral_stripFn_lt_top hg
  have hpt : ∀ a b : ℝ≥0∞, a * b ≤ a ^ 2 * b + b := by
    intro a b
    rcases le_total a 1 with h | h
    · exact (mul_le_of_le_one_left' h).trans le_add_self
    · have : a ≤ a ^ 2 := by
        rw [sq]
        exact le_mul_of_one_le_left' h
      exact (mul_le_mul' this le_rfl).trans le_self_add
  have hbound : ∫⁻ z : ℍ, ‖w (surfMk modGroup z) * conj (stripFn g z)‖ₑ ≤ ∫⁻ z : ℍ, (f z + ‖stripFn g z‖ₑ) := by
    refine lintegral_mono_ae ?_
    filter_upwards [hlift] with z hz
    rw [hz, enorm_mul, RCLike.enorm_conj]
    exact hpt _ _
  refine lt_of_le_of_lt hbound ?_
  rw [lintegral_add_left hfm]
  exact ENNReal.add_lt_top.2 ⟨h1, h2⟩

/-- **Unfolding the pairing with an incomplete Eisenstein series.** -/
theorem integral_mul_conj_perio_stripFn {w : Surf modGroup → ℂ}
    (hwm : AEStronglyMeasurable w (surfMeasure modGroup)) (hw : MemLp w 2 (surfMeasure modGroup))
    {g : ℝ → ℂ} (hg : IsKTest g) :
    ∫ x, w x * conj (perio modGroup (stripFn g) x) ∂surfMeasure modGroup
      = ∫ z : ℍ, w (surfMk modGroup z) * conj (stripFn g z) := by
  have hm : AEStronglyMeasurable (fun x : Surf modGroup => w x * perio modGroup (fun z => conj (stripFn g z)) x)
      (surfMeasure modGroup) := by
    simp_rw [perio_conj_stripFn]
    exact hwm.mul (Complex.continuous_conj.comp_aestronglyMeasurable (aestronglyMeasurable_perio_stripFn hg))
  have h := integral_lift_mul_eq modGroup (integrable_lift_mul_conj_stripFn hwm hw hg) hm
  rw [h]
  simp_rw [perio_conj_stripFn]

end Qschubert
