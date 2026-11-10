import Qschubert.EvModStar
import Qschubert.EvModStatement
import Qschubert.ZeroModeMass

/-!
# The cusp of the modular surface and the zero Fourier mode

Stage A of the plan for Proposition `ev:mod` (`lean/BLUEPRINT.md`), item L7. For `Y ≥ 1` let
`S_Y = {z : 0 ≤ Re z < 1, Im z > Y}` (`cuspS`).

* `eq_one_of_smul_mem_cuspS`: an element of `PSL(2, ℤ)` that maps a point of `S_Y` into `S_Y` is the identity;
* `not_mem_cuspS_of_fd`: no point of the orbit of `z' ∈ 𝒟` with `Im z' ≤ Y` lies in `S_Y`;
* `lintegral_compactPart_add_zeroMode_le`: for measurable `w` on `M`,
  `∫_{M_Y} |w|² dμ + ∫_Y^∞ |c₀[w](y)|² dy/y² ≤ ∫_M |w|² dμ`, where `M_Y = compactPart Y`.
-/

namespace Qschubert

open MeasureTheory Set Filter Topology Matrix UpperHalfPlane ModularGroup
open scoped Real MatrixGroups ENNReal Modular

/-- The part of the strip `0 ≤ Re z < 1` above height `Y`. -/
def cuspS (Y : ℝ) : Set ℍ := {z : ℍ | ⌊z.re⌋ = 0 ∧ Y < z.im}

lemma measurableSet_cuspS (Y : ℝ) : MeasurableSet (cuspS Y) :=
  ((Int.measurable_floor.comp UpperHalfPlane.continuous_re.measurable) (measurableSet_singleton 0)).inter
    (measurableSet_lt measurable_const UpperHalfPlane.continuous_im.measurable)

lemma npMap_smul (pn : NPair × ℤ) (z : ℍ) : npMap pn • z = T ^ pn.2 • (npSec pn.1 • z) := by
  rw [npMap, modQ_smul, mul_smul]

lemma im_npMap_smul (pn : NPair × ℤ) (z : ℍ) :
    (npMap pn • z).im = z.im / Complex.normSq ((pn.1.1 0 : ℂ) * z + pn.1.1 1) := by
  rw [npMap_smul, im_T_zpow_smul, im_npSec_smul]

lemma re_npMap_smul (pn : NPair × ℤ) (z : ℍ) : (npMap pn • z).re = (npSec pn.1 • z).re + pn.2 := by
  rw [npMap_smul, re_T_zpow_smul]

lemma normSq_cz_add_d (c d : ℤ) (z : ℍ) :
    Complex.normSq ((c : ℂ) * z + d) = ((c : ℝ) * z.re + d) ^ 2 + ((c : ℝ) * z.im) ^ 2 := by
  rw [Complex.normSq_apply]
  simp [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  ring

/-- For `c > 0` the height drops below `1/Im z`. -/
lemma im_npMap_smul_le_of_pos {pn : NPair × ℤ} (hc : 0 < pn.1.1 0) (z : ℍ) : (npMap pn • z).im ≤ 1 / z.im := by
  have hy := z.im_pos
  have hc1 : (1 : ℝ) ≤ (pn.1.1 0 : ℝ) := by exact_mod_cast hc
  have hN : z.im ^ 2 ≤ Complex.normSq ((pn.1.1 0 : ℂ) * z + pn.1.1 1) := by
    rw [normSq_cz_add_d]
    have h1 : z.im ≤ (pn.1.1 0 : ℝ) * z.im := le_mul_of_one_le_left hy.le hc1
    nlinarith [sq_nonneg ((pn.1.1 0 : ℝ) * z.re + pn.1.1 1)]
  rw [im_npMap_smul, div_le_div_iff₀ (lt_of_lt_of_le (by positivity) hN) hy]
  nlinarith

lemma npair_eq_of_zero {p q : NPair} (hp : p.1 0 = 0) (hq : q.1 0 = 0) : p = q := by
  have hp1 : p.1 1 = 1 := by
    rcases p.2.2 with h | ⟨_, h⟩
    · omega
    · exact h
  have hq1 : q.1 1 = 1 := by
    rcases q.2.2 with h | ⟨_, h⟩
    · omega
    · exact h
  apply Subtype.ext
  funext i
  fin_cases i
  · show p.1 0 = q.1 0
    rw [hp, hq]
  · show p.1 1 = q.1 1
    rw [hp1, hq1]

/-- In `S_Y`, `Y ≥ 1`, only the bottom row `(0, 1)` keeps the height above `Y`. -/
lemma fst_zero_of_smul_mem_cuspS {Y : ℝ} (hY : 1 ≤ Y) {z : ℍ} (hz : z ∈ cuspS Y) {pn : NPair × ℤ}
    (h : npMap pn • z ∈ cuspS Y) : pn.1.1 0 = 0 := by
  by_contra hne
  have hc : 0 < pn.1.1 0 := lt_of_le_of_ne (npair_nonneg pn.1) (Ne.symm hne)
  have h1 := im_npMap_smul_le_of_pos hc z
  have hy : Y < z.im := hz.2
  have h2 : Y < (npMap pn • z).im := h.2
  have h3 : 1 / z.im < 1 := by
    rw [div_lt_one z.im_pos]
    linarith
  linarith

/-- **An element of `PSL(2, ℤ)` that maps a point of `S_Y` into `S_Y` is the identity** (`Y ≥ 1`). -/
theorem eq_one_of_smul_mem_cuspS {Y : ℝ} (hY : 1 ≤ Y) {z : ℍ} (hz : z ∈ cuspS Y) {δ : modGroup}
    (h : δ • z ∈ cuspS Y) : δ = 1 := by
  obtain ⟨pn, rfl⟩ := npMap_surjective δ
  obtain ⟨qn, hq⟩ := npMap_surjective (1 : modGroup)
  have h1z : npMap qn • z ∈ cuspS Y := by
    rw [hq, one_smul]
    exact hz
  have hp0 := fst_zero_of_smul_mem_cuspS hY hz h
  have hq0 := fst_zero_of_smul_mem_cuspS hY hz h1z
  have hpq : pn.1 = qn.1 := npair_eq_of_zero hp0 hq0
  have hr1 : ⌊(npMap pn • z).re⌋ = 0 := h.1
  have hr2 : ⌊(npMap qn • z).re⌋ = 0 := h1z.1
  rw [re_npMap_smul, Int.floor_add_intCast] at hr1 hr2
  rw [hpq] at hr1
  have hn : pn.2 = qn.2 := by omega
  rw [← hq]
  congr 1
  exact Prod.ext hpq hn

lemma one_le_int_form {c d : ℤ} (h : c ≠ 0 ∨ d ≠ 0) : (1 : ℤ) ≤ c ^ 2 - |c| * |d| + d ^ 2 := by
  have hc := abs_nonneg c
  have hd := abs_nonneg d
  have hc2 : c ^ 2 = |c| ^ 2 := (sq_abs c).symm
  have hd2 : d ^ 2 = |d| ^ 2 := (sq_abs d).symm
  rw [hc2, hd2]
  rcases h with h | h
  · have h1 : 1 ≤ |c| := Int.one_le_abs h
    nlinarith [sq_nonneg (|c| - |d|)]
  · have h1 : 1 ≤ |d| := Int.one_le_abs h
    nlinarith [sq_nonneg (|c| - |d|)]

/-- In the standard fundamental domain `|cz + d| ≥ 1` for integers `(c, d) ≠ (0, 0)`. -/
lemma one_le_normSq_of_fd {z : ℍ} (hz : z ∈ 𝒟) {c d : ℤ} (h : c ≠ 0 ∨ d ≠ 0) :
    1 ≤ Complex.normSq ((c : ℂ) * z + d) := by
  have h1 : (1 : ℝ) ≤ Complex.normSq (z : ℂ) := hz.1
  have h2 : |z.re| ≤ 1 / 2 := hz.2
  rw [Complex.normSq_apply] at h1
  have e1 : ((z : ℂ)).re = z.re := rfl
  have e2 : ((z : ℂ)).im = z.im := rfl
  rw [e1, e2] at h1
  have hint := one_le_int_form h
  have hreal : (1 : ℝ) ≤ (c : ℝ) ^ 2 - |(c : ℝ)| * |(d : ℝ)| + (d : ℝ) ^ 2 := by
    have := (Int.cast_le (R := ℝ)).2 hint
    push_cast at this
    exact this
  rw [normSq_cz_add_d]
  have hcd : -(|(c : ℝ)| * |(d : ℝ)|) ≤ 2 * ((c : ℝ) * (d : ℝ)) * z.re := by
    have h3 : |2 * ((c : ℝ) * (d : ℝ)) * z.re| ≤ |(c : ℝ)| * |(d : ℝ)| := by
      rw [abs_mul, abs_mul, abs_mul, abs_two]
      nlinarith [abs_nonneg (c : ℝ), abs_nonneg (d : ℝ), mul_nonneg (abs_nonneg (c : ℝ)) (abs_nonneg (d : ℝ))]
    linarith [neg_abs_le (2 * ((c : ℝ) * (d : ℝ)) * z.re)]
  nlinarith [sq_nonneg (c : ℝ), sq_nonneg (d : ℝ)]

/-- No point of the orbit of `z' ∈ 𝒟` with `Im z' ≤ Y` lies in `S_Y`. -/
theorem not_mem_cuspS_of_fd {Y : ℝ} {z : ℍ} (hz : z ∈ 𝒟) (hzY : z.im ≤ Y) (δ : modGroup) : δ • z ∉ cuspS Y := by
  obtain ⟨pn, rfl⟩ := npMap_surjective δ
  intro h
  have h2 : Y < (npMap pn • z).im := h.2
  have hN := one_le_normSq_of_fd hz (npair_ne_zero pn.1)
  rw [im_npMap_smul] at h2
  have h3 : z.im / Complex.normSq ((pn.1.1 0 : ℂ) * z + pn.1.1 1) ≤ z.im := div_le_self z.im_pos.le hN
  linarith

/-- The number of points of the orbit in `S_Y`. -/
noncomputable def cuspN (Y : ℝ) : Surf modGroup → ℝ≥0∞ := MulAction.automorphize ((cuspS Y).indicator (1 : ℍ → ℝ≥0∞))

lemma cuspN_mk (Y : ℝ) (z : ℍ) : cuspN Y (surfMk modGroup z) = ∑' γ : modGroup, (cuspS Y).indicator (1 : ℍ → ℝ≥0∞) (γ • z) :=
  rfl

lemma measurable_cuspN (Y : ℝ) : Measurable (cuspN Y) :=
  measurable_from_quotient.2 (Measurable.tsum fun γ =>
    (measurable_one.indicator (measurableSet_cuspS Y)).comp (measurable_const_smul γ))

lemma cuspN_le_one {Y : ℝ} (hY : 1 ≤ Y) (x : Surf modGroup) : cuspN Y x ≤ 1 := by
  induction x using Quotient.inductionOn with | _ z => ?_
  show cuspN Y (surfMk modGroup z) ≤ 1
  rw [cuspN_mk]
  by_cases hex : ∃ γ₀ : modGroup, γ₀ • z ∈ cuspS Y
  · obtain ⟨γ₀, hγ₀⟩ := hex
    rw [tsum_eq_single γ₀]
    · rw [Set.indicator_of_mem hγ₀]
      simp
    · intro γ hγ
      refine Set.indicator_of_notMem (fun h => hγ ?_) _
      have h1 : (γ * γ₀⁻¹) • (γ₀ • z) ∈ cuspS Y := by
        rw [mul_smul, inv_smul_smul]
        exact h
      have h2 := eq_one_of_smul_mem_cuspS hY hγ₀ h1
      exact mul_inv_eq_one.1 h2
  · have h0 : ∀ γ : modGroup, (cuspS Y).indicator (1 : ℍ → ℝ≥0∞) (γ • z) = 0 := fun γ =>
      Set.indicator_of_notMem (fun h => hex ⟨γ, h⟩) _
    simp_rw [h0]
    simp

lemma cuspN_eq_zero_of_compactPart {Y : ℝ} {x : Surf modGroup} (hx : x ∈ compactPart Y) : cuspN Y x = 0 := by
  obtain ⟨z, ⟨hz, hzY⟩, rfl⟩ := hx
  rw [cuspN_mk]
  have h0 : ∀ γ : modGroup, (cuspS Y).indicator (1 : ℍ → ℝ≥0∞) (γ • z) = 0 := fun γ =>
    Set.indicator_of_notMem (not_mem_cuspS_of_fd hz hzY γ) _
  simp_rw [h0]
  simp

/-- `‖∫_{[0,1)} φ‖² ≤ ∫_{[0,1)} ‖φ‖²`. -/
lemma enorm_integral_Ico_sq_le {φ : ℝ → ℂ} (hφ : Measurable φ) :
    ‖∫ x in Ico (0 : ℝ) 1, φ x‖ₑ ^ 2 ≤ ∫⁻ x in Ico (0 : ℝ) 1, ‖φ x‖ₑ ^ 2 := by
  have h1 : ‖∫ x in Ico (0 : ℝ) 1, φ x‖ₑ ≤ ∫⁻ x in Ico (0 : ℝ) 1, ‖φ x‖ₑ := enorm_integral_le_lintegral_enorm _
  have h2 := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (Ico (0 : ℝ) 1)) Real.HolderConjugate.two_two
    (f := fun x => ‖φ x‖ₑ) (g := fun _ => 1) hφ.enorm.aemeasurable aemeasurable_const
  have hone : ∫⁻ _ in Ico (0 : ℝ) 1, (1 : ℝ≥0∞) ^ (2 : ℝ) = 1 := by
    simp [Real.volume_Ico]
  have hsq : ∀ t : ℝ≥0∞, (t ^ (1 / (2 : ℝ))) ^ 2 = t := fun t => by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have h3 : ∫⁻ x in Ico (0 : ℝ) 1, ‖φ x‖ₑ ≤ (∫⁻ x in Ico (0 : ℝ) 1, ‖φ x‖ₑ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
    have h4 : ∫⁻ x in Ico (0 : ℝ) 1, ((fun x : ℝ => ‖φ x‖ₑ) * fun _ : ℝ => (1 : ℝ≥0∞)) x
        = ∫⁻ x in Ico (0 : ℝ) 1, ‖φ x‖ₑ := lintegral_congr fun x => by simp
    rw [← h4]
    refine h2.trans ?_
    rw [hone, ENNReal.one_rpow, mul_one]
  calc ‖∫ x in Ico (0 : ℝ) 1, φ x‖ₑ ^ 2 ≤ ((∫⁻ x in Ico (0 : ℝ) 1, ‖φ x‖ₑ ^ (2 : ℝ)) ^ (1 / (2 : ℝ))) ^ 2 :=
        pow_le_pow_left' (h1.trans h3) 2
    _ = ∫⁻ x in Ico (0 : ℝ) 1, ‖φ x‖ₑ ^ (2 : ℝ) := hsq _
    _ = ∫⁻ x in Ico (0 : ℝ) 1, ‖φ x‖ₑ ^ 2 := by simp_rw [ENNReal.rpow_two]

lemma zeroModeM_eq_Ico (w : Surf modGroup → ℂ) {y : ℝ} (hy : 0 < y) :
    zeroModeM w y = ∫ x in Ico (0 : ℝ) 1, w (surfMk modGroup ⟨⟨x, y⟩, hy⟩) := by
  rw [zeroModeM, dite_eq_left hy, intervalIntegral.integral_of_le zero_le_one, integral_Ico_eq_integral_Ioo,
    integral_Ioc_eq_integral_Ioo]

/-- **The mass in the compact part and the zero mode above height `Y`.** -/
theorem lintegral_compactPart_add_zeroMode_le {Y : ℝ} (hY : 1 ≤ Y) {w : Surf modGroup → ℂ} (hwm : Measurable w) :
    (∫⁻ x in compactPart Y, ‖w x‖ₑ ^ 2 ∂surfMeasure modGroup)
      + ∫⁻ y in Ioi Y, ENNReal.ofReal ((y ^ 2)⁻¹) * ‖zeroModeM w y‖ₑ ^ 2
      ≤ ∫⁻ x, ‖w x‖ₑ ^ 2 ∂surfMeasure modGroup := by
  have hY0 : (0 : ℝ) < Y := by linarith
  set A : Set (Surf modGroup) := {x | cuspN Y x = 0} with hA
  have hAm : MeasurableSet A := measurable_cuspN Y (measurableSet_singleton 0)
  have hsub : compactPart Y ⊆ A := fun x hx => cuspN_eq_zero_of_compactPart hx
  -- the cusp part as an integral over `S_Y`
  set f : ℍ → ℝ≥0∞ := (cuspS Y).indicator fun z => ‖w (surfMk modGroup z)‖ₑ ^ 2 with hf
  have hfm : Measurable f := ((hwm.comp (measurable_surfMk modGroup)).enorm.pow_const 2).indicator (measurableSet_cuspS Y)
  have hF := isFundamentalDomain_fdSet modGroup
  have haut : ∀ x : Surf modGroup, MulAction.automorphize f x = ‖w x‖ₑ ^ 2 * cuspN Y x := by
    intro x
    induction x using Quotient.inductionOn with | _ z => ?_
    show ∑' γ : modGroup, f (γ • z) = ‖w (surfMk modGroup z)‖ₑ ^ 2 * cuspN Y (surfMk modGroup z)
    rw [cuspN_mk, ← ENNReal.tsum_mul_left]
    refine tsum_congr fun γ => ?_
    simp only [hf]
    by_cases h : γ • z ∈ cuspS Y
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, surfMk_smul]
      simp
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, mul_zero]
  have hcusp : ∫⁻ z : ℍ, f z ≤ ∫⁻ x in Aᶜ, ‖w x‖ₑ ^ 2 ∂surfMeasure modGroup := by
    rw [lintegral_eq_lintegral_automorphize modGroup hF hfm, ← lintegral_indicator hAm.compl]
    refine lintegral_mono fun x => ?_
    rw [haut]
    by_cases hx : x ∈ A
    · have hx0 : cuspN Y x = 0 := hx
      rw [hx0, mul_zero]
      exact zero_le
    · rw [Set.indicator_of_mem (show x ∈ Aᶜ from hx)]
      exact mul_le_of_le_one_right' (cuspN_le_one hY x)
  -- the zero mode
  have hzero : ∫⁻ y in Ioi Y, ENNReal.ofReal ((y ^ 2)⁻¹) * ‖zeroModeM w y‖ₑ ^ 2 ≤ ∫⁻ z : ℍ, f z := by
    rw [lintegral_H_slice' hfm]
    refine (lintegral_mono_set (Ioi_subset_Ioi hY0.le)).trans' ?_
    refine setLIntegral_mono' measurableSet_Ioi fun y hy => ?_
    have hyY : Y < y := hy
    have hy0 : (0 : ℝ) < y := lt_trans hY0 hyY
    refine mul_le_mul' le_rfl ?_
    have e : ∀ x : ℝ, f (UpperHalfPlane.ofComplex ⟨x, y⟩)
        = (Ico (0 : ℝ) 1).indicator (fun x => ‖w (surfMk modGroup ⟨⟨x, y⟩, hy0⟩)‖ₑ ^ 2) x := by
      intro x
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos (show 0 < (⟨x, y⟩ : ℂ).im from hy0)]
      simp only [hf]
      by_cases hx : ⌊x⌋ = 0
      · rw [Set.indicator_of_mem (show (⟨⟨x, y⟩, hy0⟩ : ℍ) ∈ cuspS Y from ⟨hx, hyY⟩),
          Set.indicator_of_mem (Int.floor_eq_zero_iff.1 hx)]
      · rw [Set.indicator_of_notMem (fun h : (⟨⟨x, y⟩, hy0⟩ : ℍ) ∈ cuspS Y => hx h.1),
          Set.indicator_of_notMem (fun h => hx (Int.floor_eq_zero_iff.2 h))]
    simp_rw [e]
    rw [lintegral_indicator measurableSet_Ico, zeroModeM_eq_Ico w hy0]
    exact enorm_integral_Ico_sq_le (hwm.comp ((measurable_surfMk modGroup).comp (measurable_mk_line hy0)))
  calc (∫⁻ x in compactPart Y, ‖w x‖ₑ ^ 2 ∂surfMeasure modGroup)
        + ∫⁻ y in Ioi Y, ENNReal.ofReal ((y ^ 2)⁻¹) * ‖zeroModeM w y‖ₑ ^ 2
      ≤ (∫⁻ x in A, ‖w x‖ₑ ^ 2 ∂surfMeasure modGroup) + ∫⁻ x in Aᶜ, ‖w x‖ₑ ^ 2 ∂surfMeasure modGroup :=
        add_le_add (lintegral_mono_set hsub) (hzero.trans hcusp)
    _ = ∫⁻ x, ‖w x‖ₑ ^ 2 ∂surfMeasure modGroup := lintegral_add_compl _ hAm

end Qschubert
