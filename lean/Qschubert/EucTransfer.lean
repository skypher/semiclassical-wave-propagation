import Qschubert.LocalWeak
import Qschubert.SobolevC
import Qschubert.Transport

/-!
# From `L²(ℍ, dx dy/y²)` to `L²(ℂ, dx dy)` through a test-function multiplier

For a test function `c` and `w ∈ L²(ℍ)`, `E_c w (ζ) = c(ζ) w(ζ)` on `ℍ` (zero elsewhere, through a
strongly measurable representative of `w`) is in `L²(ℂ)` (`eucL`), with
`‖E_c w‖ ≤ (sup |c(ζ)| Im ζ) ‖w‖` (`norm_eucL_le`), and its pairing with a Schwartz function is a
hyperbolic inner product: `∫ φ · E_c w = ⟪conj(y² φ c), w⟫` (`integral_smul_eucL`).
-/

namespace Qschubert

open MeasureTheory UpperHalfPlane Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ENNReal

local notation "L2H" => Lp ℂ 2 (volume : Measure ℍ)
local notation "L2C" => Lp ℂ 2 (volume : Measure ℂ)

/-- A strongly measurable representative. -/
noncomputable def repL2 (w : L2H) : ℍ → ℂ := (Lp.aestronglyMeasurable w).mk w

lemma stronglyMeasurable_repL2 (w : L2H) : StronglyMeasurable (repL2 w) :=
  (Lp.aestronglyMeasurable w).stronglyMeasurable_mk

lemma repL2_ae (w : L2H) : ⇑w =ᵐ[volume] repL2 w := (Lp.aestronglyMeasurable w).ae_eq_mk

/-- `E_c w` as a function on `ℂ`. -/
noncomputable def eucFun (c : testFn) (w : L2H) (ζ : ℂ) : ℂ :=
  (c : ℂ → ℂ) ζ * repL2 w (UpperHalfPlane.ofComplex ζ)

lemma measurable_eucFun (c : testFn) (w : L2H) : Measurable (eucFun c w) :=
  c.2.smooth.continuous.measurable.mul ((stronglyMeasurable_repL2 w).measurable.comp measurable_ofComplex)

lemma exists_bound_cy (c : testFn) : ∃ C : ℝ, ∀ ζ : ℂ, ‖(c : ℂ → ℂ) ζ‖ * |ζ.im| ≤ C := by
  obtain ⟨C, hC⟩ := (c.2.smooth.continuous.mul (Complex.continuous_ofReal.comp Complex.continuous_im)).bounded_above_of_compact_support
    (c.2.compact.mul_right (f' := fun ζ : ℂ => ((ζ.im : ℝ) : ℂ)))
  refine ⟨C, fun ζ => ?_⟩
  have h := hC ζ
  simp only [Pi.mul_apply, Function.comp_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs] at h
  exact h

/-- `sup |c(ζ)| Im ζ`. -/
noncomputable def supCy (c : testFn) : ℝ := Classical.choose (exists_bound_cy c)

lemma norm_c_mul_im_le (c : testFn) (ζ : ℂ) : ‖(c : ℂ → ℂ) ζ‖ * |ζ.im| ≤ supCy c :=
  Classical.choose_spec (exists_bound_cy c) ζ

lemma eucFun_eq_zero (c : testFn) (w : L2H) {ζ : ℂ} (hζ : ¬ 0 < ζ.im) : eucFun c w ζ = 0 := by
  simp [eucFun, testFn_eq_zero c hζ]

/-- `‖E_c w‖₂² ≤ sup(|c| y)² ‖w‖₂²`, as lower integrals. -/
lemma lintegral_eucFun_le (c : testFn) (w : L2H) :
    ∫⁻ ζ, ‖eucFun c w ζ‖ₑ ^ (2 : ℝ) ≤ ENNReal.ofReal (supCy c ^ 2) * ∫⁻ z, ‖repL2 w z‖ₑ ^ (2 : ℝ) := by
  set g : ℍ → ℝ≥0∞ := fun z => ENNReal.ofReal ((z.im) ^ 2 * ‖(c : ℂ → ℂ) z‖ ^ 2) * ‖repL2 w z‖ₑ ^ (2 : ℝ)
  have hg : Measurable g := by
    refine (ENNReal.measurable_ofReal.comp ?_).mul ?_
    · exact ((UpperHalfPlane.continuous_im.pow 2).mul
        ((c.2.smooth.continuous.comp UpperHalfPlane.continuous_coe).norm.pow 2)).measurable
    · exact (stronglyMeasurable_repL2 w).measurable.enorm.pow_const _
  have hH := lintegral_H_eq hg
  have hpt : ∀ ζ : ℂ, ‖eucFun c w ζ‖ₑ ^ (2 : ℝ)
      = {w : ℂ | 0 < w.im}.indicator
        (fun ζ => ENNReal.ofReal ((1 / ζ.im) ^ 2) * g (UpperHalfPlane.ofComplex ζ)) ζ := by
    intro ζ
    by_cases hζ : 0 < ζ.im
    · rw [Set.indicator_of_mem (show ζ ∈ {w : ℂ | 0 < w.im} from hζ)]
      simp only [g, eucFun]
      rw [ofComplex_apply_of_im_pos hζ]
      have him : ((⟨ζ, hζ⟩ : ℍ)).im = ζ.im := rfl
      rw [him, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      have e : (1 / ζ.im) ^ 2 * (ζ.im ^ 2 * ‖(c : ℂ → ℂ) ζ‖ ^ 2) = ‖(c : ℂ → ℂ) ζ‖ ^ 2 := by
        field_simp
      rw [e, enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
      congr 1
      rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]
      norm_num
    · rw [Set.indicator_of_notMem (show ζ ∉ {w : ℂ | 0 < w.im} from hζ), eucFun_eq_zero c w hζ]
      simp
  simp_rw [hpt]
  rw [← hH, ← lintegral_const_mul _ ((stronglyMeasurable_repL2 w).measurable.enorm.pow_const _)]
  refine lintegral_mono fun z => ?_
  refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
  have h := norm_c_mul_im_le c (z : ℂ)
  have hz : |(z : ℂ).im| = z.im := abs_of_pos z.im_pos
  rw [hz] at h
  have h0 : 0 ≤ ‖(c : ℂ → ℂ) z‖ * z.im := mul_nonneg (norm_nonneg _) z.im_pos.le
  calc z.im ^ 2 * ‖(c : ℂ → ℂ) z‖ ^ 2 = (‖(c : ℂ → ℂ) z‖ * z.im) ^ 2 := by ring
    _ ≤ supCy c ^ 2 := pow_le_pow_left₀ h0 h 2

lemma supCy_nonneg (c : testFn) : 0 ≤ supCy c :=
  (mul_nonneg (norm_nonneg _) (abs_nonneg _)).trans (norm_c_mul_im_le c 0)

lemma lintegral_repL2_lt_top (w : L2H) : ∫⁻ z, ‖repL2 w z‖ₑ ^ (2 : ℝ) < ⊤ := by
  have h := (Lp.memLp w).eLpNorm_lt_top
  rw [eLpNorm_congr_ae (repL2_ae w), eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top
    (stronglyMeasurable_repL2 w).aestronglyMeasurable, ENNReal.toReal_ofNat] at h
  exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num)).1 h

lemma memLp_eucFun (c : testFn) (w : L2H) : MemLp (eucFun c w) 2 (volume : Measure ℂ) := by
  have hlt : eLpNorm (eucFun c w) 2 volume < ⊤ := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top
      (measurable_eucFun c w).aestronglyMeasurable, ENNReal.toReal_ofNat]
    refine ENNReal.rpow_lt_top_of_nonneg (by norm_num) (ne_top_of_le_ne_top ?_ (lintegral_eucFun_le c w))
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (lintegral_repL2_lt_top w).ne
  exact hlt

/-- `E_c w ∈ L²(ℂ)`. -/
noncomputable def eucL (c : testFn) (w : L2H) : L2C := (memLp_eucFun c w).toLp _

lemma eucL_ae (c : testFn) (w : L2H) : ⇑(eucL c w) =ᵐ[volume] eucFun c w := (memLp_eucFun c w).coeFn_toLp

/-- `‖E_c w‖ ≤ sup(|c| y) ‖w‖`. -/
theorem norm_eucL_le (c : testFn) (w : L2H) : ‖eucL c w‖ ≤ supCy c * ‖w‖ := by
  rw [eucL, Lp.norm_toLp, Lp.norm_def]
  have hw : eLpNorm (⇑w) 2 volume = (∫⁻ z, ‖repL2 w z‖ₑ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
    rw [eLpNorm_congr_ae (repL2_ae w), eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero
      ENNReal.ofNat_ne_top (stronglyMeasurable_repL2 w).aestronglyMeasurable, ENNReal.toReal_ofNat]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top
    (measurable_eucFun c w).aestronglyMeasurable, ENNReal.toReal_ofNat, hw]
  rw [← ENNReal.toReal_ofReal (supCy_nonneg c), ← ENNReal.toReal_mul]
  refine ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (lintegral_repL2_lt_top w).ne)) ?_
  calc (∫⁻ ζ, ‖eucFun c w ζ‖ₑ ^ (2 : ℝ)) ^ (1 / (2 : ℝ))
      ≤ (ENNReal.ofReal (supCy c ^ 2) * ∫⁻ z, ‖repL2 w z‖ₑ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) :=
        ENNReal.rpow_le_rpow (lintegral_eucFun_le c w) (by norm_num)
    _ = ENNReal.ofReal (supCy c) * (∫⁻ z, ‖repL2 w z‖ₑ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.ofReal_rpow_of_nonneg (by positivity)
          (by norm_num)]
        congr 2
        rw [← Real.rpow_natCast, ← Real.rpow_mul (supCy_nonneg c)]
        norm_num

/-- `g · P` for a smooth `g` and a test function `P`. -/
noncomputable def smulTF (g : ℂ → ℂ) (hg : ContDiff ℝ ∞ g) (P : testFn) : testFn :=
  ⟨fun ζ => g ζ * (P : ℂ → ℂ) ζ, isTestFn_mul_of_contDiffAt (fun _ _ => hg.contDiffAt) P.2⟩

/-- The complex conjugate of a test function. -/
noncomputable def conjT (P : testFn) : testFn :=
  ⟨fun ζ => conj ((P : ℂ → ℂ) ζ), by
    have hsub : tsupport (fun ζ => conj ((P : ℂ → ℂ) ζ)) ⊆ tsupport (P : ℂ → ℂ) :=
      tsupport_comp_subset (g := fun z : ℂ => conj z) (by simp) _
    exact ⟨Complex.conjCLE.toContinuousLinearMap.contDiff.comp P.2.smooth,
      IsCompact.of_isClosed_subset P.2.compact (isClosed_tsupport _) hsub, hsub.trans P.2.inside⟩⟩

lemma contDiff_imSq : ContDiff ℝ ∞ fun ζ : ℂ => ((ζ.im : ℝ) : ℂ) ^ 2 :=
  ((Complex.ofRealCLM.comp Complex.imCLM).contDiff).pow 2

/-- **The pairing**: `∫ φ · E_c w = ⟪conj(y² φ c), w⟫` for smooth `φ`. -/
theorem integral_smul_eucFun (c : testFn) (w : L2H) {φ : ℂ → ℂ} (hφ : ContDiff ℝ ∞ φ) :
    ∫ ζ, φ ζ • eucFun c w ζ
      = inner ℂ (toL2 (conjT (smulTF (fun ζ => ((ζ.im : ℝ) : ℂ) ^ 2 * φ ζ) (contDiff_imSq.mul hφ) c))) w := by
  set Q := conjT (smulTF (fun ζ => ((ζ.im : ℝ) : ℂ) ^ 2 * φ ζ) (contDiff_imSq.mul hφ) c)
  rw [MeasureTheory.L2.inner_def]
  have hQ : ⇑(toL2 Q) =ᵐ[volume] fun z : ℍ => (Q : ℂ → ℂ) z := (memLp_comp_coe Q.2).coeFn_toLp
  have e1 : ∫ z : ℍ, inner ℂ ((toL2 Q) z) (w z)
      = ∫ z : ℍ, (z.im : ℂ) ^ 2 * (φ z * eucFun c w z) := by
    refine integral_congr_ae ?_
    filter_upwards [hQ, repL2_ae w] with z h1 h2
    rw [RCLike.inner_apply, h1, h2]
    show repL2 w z * conj (conj (((z : ℂ).im : ℂ) ^ 2 * φ z * (c : ℂ → ℂ) z)) = _
    rw [Complex.conj_conj, eucFun, ofComplex_apply]
    simp only [UpperHalfPlane.coe_im]
    ring
  rw [e1, integral_im_sq_mul (fun ζ => φ ζ * eucFun c w ζ)]
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun ζ hζ => ?_).symm
  have hζ' : ¬ 0 < ζ.im := fun h => hζ ⟨⟨ζ, h⟩, rfl⟩
  rw [eucFun_eq_zero c w hζ', smul_zero]

end Qschubert
