import Qschubert.PartialFourier
import Qschubert.FormOps
import Qschubert.EllipticId

/-!
# The partial Fourier transform intertwines `X = y∂ₓ` with multiplication by `2πiky`

`pF_vfX`: for a test function `F`, `(XF)^(k, y) = 2πi k y F̂(k, y)`. Proof: the slice of `XF` is
`y · (slice F y)'` (chain rule along `x ↦ x + iy`), and `𝓕(f') = 2πik 𝓕 f` (Mathlib's
`Real.fourier_deriv`). With `norm_partialFourier`, this is the reduction `X = i sgn(k) z` of the
proof of Lemma FC (after `z = |k|y`, up to the `2π` of Mathlib's Fourier convention).

`pF_vfY`: `(YF)^(k, y) = y ∂_y F̂(k, y)`, with `∂_y F̂ = (∂_y F)^` (`hasDerivAt_pF_y`,
differentiation under the integral, dominated by `sup|∂_y F|` on the compact set `Re(tsupport F)`).
-/

namespace Qschubert

open MeasureTheory UpperHalfPlane Filter Topology FourierTransform Set
open scoped ContDiff ENNReal SchwartzMap

lemma hasDerivAt_slice (F : testFn) (y x : ℝ) :
    HasDerivAt (slice F y) (fderiv ℝ (F : ℂ → ℂ) ⟨x, y⟩ 1) x := by
  have hline : HasDerivAt (fun x : ℝ => (x : ℂ) + (y : ℂ) * Complex.I) 1 x := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).add_const ((y : ℂ) * Complex.I)
  have hF : HasFDerivAt (F : ℂ → ℂ) (fderiv ℝ (F : ℂ → ℂ) ⟨x, y⟩) ((x : ℂ) + (y : ℂ) * Complex.I) := by
    have e : ((x : ℂ) + (y : ℂ) * Complex.I) = ⟨x, y⟩ := by apply Complex.ext <;> simp
    rw [e]
    exact ((F.2.smooth.differentiable (by simp)) _).hasFDerivAt
  rw [slice_eq]
  have h := hF.comp_hasDerivAt x hline
  simpa using h

lemma deriv_slice (F : testFn) (y x : ℝ) : deriv (slice F y) x = fderiv ℝ (F : ℂ → ℂ) ⟨x, y⟩ 1 :=
  (hasDerivAt_slice F y x).deriv

lemma slice_vfX (F : testFn) (y : ℝ) :
    slice ((vfTest 1 F : testFn) : ℂ → ℂ) y = fun x => (y : ℂ) * deriv (slice F y) x := by
  funext x
  rw [deriv_slice]
  rfl

lemma integrable_deriv_slice (F : testFn) (y : ℝ) : Integrable (deriv (slice F y)) := by
  have hc : Continuous (deriv (slice F y)) :=
    (contDiff_slice F.2.smooth y).continuous_deriv (by simp)
  exact hc.integrable_of_hasCompactSupport (hasCompactSupport_slice F.2.compact y).deriv

/-- **`(XF)^(k, y) = 2πi k y F̂(k, y)`.** -/
theorem pF_vfX (F : testFn) (k y : ℝ) :
    pF ((vfTest 1 F : testFn) : ℂ → ℂ) (k, y) = 2 * Real.pi * Complex.I * k * y * pF F (k, y) := by
  have hint : Integrable (slice F y) := (sliceS F y).integrable
  have hdiff : Differentiable ℝ (slice F y) := (contDiff_slice F.2.smooth y).differentiable (by simp)
  have hd := Real.fourier_deriv hint hdiff (integrable_deriv_slice F y)
  have h1 : pF ((vfTest 1 F : testFn) : ℂ → ℂ) (k, y) = (y : ℂ) * 𝓕 (deriv (slice F y)) k := by
    show 𝓕 (slice ((vfTest 1 F : testFn) : ℂ → ℂ) y) k = _
    rw [slice_vfX, Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul,
      ← integral_const_mul]
    congr 1; funext x
    simp only [smul_eq_mul]; ring
  rw [h1, hd]
  show (y : ℂ) * ((2 * Real.pi * Complex.I * k) • 𝓕 (slice F y) k) = _
  rw [smul_eq_mul]
  simp only [pF]
  ring

/-! ### `Y = y∂_y` -/

lemma hasDerivAt_vert (F : testFn) (x y : ℝ) :
    HasDerivAt (fun y' : ℝ => (F : ℂ → ℂ) ⟨x, y'⟩) (fderiv ℝ (F : ℂ → ℂ) ⟨x, y⟩ Complex.I) y := by
  have hline : HasDerivAt (fun y' : ℝ => (x : ℂ) + (y' : ℂ) * Complex.I) Complex.I y := by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := y)).mul_const Complex.I).const_add (x : ℂ)
  have e : ∀ y' : ℝ, ((x : ℂ) + (y' : ℂ) * Complex.I) = ⟨x, y'⟩ := fun y' => by
    apply Complex.ext <;> simp
  have hF : HasFDerivAt (F : ℂ → ℂ) (fderiv ℝ (F : ℂ → ℂ) ⟨x, y⟩) ((x : ℂ) + (y : ℂ) * Complex.I) := by
    rw [e]; exact ((F.2.smooth.differentiable (by simp)) _).hasFDerivAt
  have h := hF.comp_hasDerivAt y hline
  simp only [Function.comp_def, e] at h
  exact h

/-- `∂_y F̂(k, y) = (∂_y F)^(k, y)`. -/
theorem hasDerivAt_pF_y (F : testFn) (k y : ℝ) :
    HasDerivAt (fun y' => pF F (k, y')) (pF ((dirTest Complex.I F : testFn) : ℂ → ℂ) (k, y)) y := by
  set e : ℝ → ℂ := fun x => Complex.exp (↑(-2 * Real.pi * x * k) * Complex.I)
  have he : ∀ x, ‖e x‖ = 1 := fun x => by
    simp only [e]; rw [Complex.norm_exp_ofReal_mul_I]
  have hcont : Continuous e := Complex.continuous_exp.comp
    ((Complex.continuous_ofReal.comp (by fun_prop : Continuous fun x : ℝ => -2 * Real.pi * x * k)).mul
      continuous_const)
  set K : Set ℝ := Complex.re '' tsupport (F : ℂ → ℂ)
  have hK : IsCompact K := F.2.compact.image Complex.continuous_re
  obtain ⟨M, hM⟩ := (dirTest Complex.I F).2.smooth.continuous.bounded_above_of_compact_support
    (dirTest Complex.I F).2.compact
  have hzero : ∀ x y' : ℝ, x ∉ K → ((dirTest Complex.I F : testFn) : ℂ → ℂ) ⟨x, y'⟩ = 0 := by
    intro x y' hx
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    exact hx ⟨_, tsupport_fderiv_apply_subset (𝕜 := ℝ) Complex.I hmem, rfl⟩
  have hcF : ∀ y' : ℝ, Continuous fun x : ℝ => (F : ℂ → ℂ) ⟨x, y'⟩ := fun y' =>
    F.2.smooth.continuous.comp (Complex.equivRealProdCLM.symm.continuous.comp
      (continuous_id.prodMk continuous_const))
  have hcD : ∀ y' : ℝ, Continuous fun x : ℝ => ((dirTest Complex.I F : testFn) : ℂ → ℂ) ⟨x, y'⟩ := fun y' =>
    (dirTest Complex.I F).2.smooth.continuous.comp (Complex.equivRealProdCLM.symm.continuous.comp
      (continuous_id.prodMk continuous_const))
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (volume : Measure ℝ))
    (F := fun y' x => e x • (F : ℂ → ℂ) ⟨x, y'⟩)
    (F' := fun y' x => e x • ((dirTest Complex.I F : testFn) : ℂ → ℂ) ⟨x, y'⟩)
    (bound := K.indicator fun _ => M) (x₀ := y) (s := Set.univ) Filter.univ_mem
    (Eventually.of_forall fun y' => (hcont.smul (hcF y')).aestronglyMeasurable)
    ((hcont.smul (hcF y)).integrable_of_hasCompactSupport
      (show HasCompactSupport (e • slice F y) from (hasCompactSupport_slice F.2.compact y).smul_left))
    ((hcont.smul (hcD y)).aestronglyMeasurable)
    (Eventually.of_forall fun x y' _ => by
      by_cases hx : x ∈ K
      · rw [Set.indicator_of_mem hx, norm_smul, he, one_mul]; exact hM _
      · rw [Set.indicator_of_notMem hx, hzero x y' hx, smul_zero, norm_zero])
    ((integrableOn_const hK.measure_lt_top.ne).integrable_indicator hK.measurableSet)
    (Eventually.of_forall fun x y' _ => (hasDerivAt_vert F x y').const_smul (e x))
  have e1 : (fun y' => pF F (k, y')) = fun y' => ∫ x, e x • (F : ℂ → ℂ) ⟨x, y'⟩ :=
    funext fun y' => pF_eq_integral F (k, y')
  rw [e1, pF_eq_integral]
  exact h.2

lemma slice_vfY (F : testFn) (y : ℝ) :
    slice ((vfTest Complex.I F : testFn) : ℂ → ℂ) y
      = fun x => (y : ℂ) * ((dirTest Complex.I F : testFn) : ℂ → ℂ) ⟨x, y⟩ := by
  funext x; rfl

/-- **`(YF)^(k, y) = y ∂_y F̂(k, y)`.** -/
theorem pF_vfY (F : testFn) (k y : ℝ) :
    pF ((vfTest Complex.I F : testFn) : ℂ → ℂ) (k, y)
      = (y : ℂ) * pF ((dirTest Complex.I F : testFn) : ℂ → ℂ) (k, y) := by
  rw [pF_eq_integral, pF_eq_integral, ← integral_const_mul]
  congr 1; funext x
  simp only [smul_eq_mul]
  show Complex.exp (↑(-2 * Real.pi * x * k) * Complex.I) * (((⟨x, y⟩ : ℂ).im : ℂ) *
    fderiv ℝ (F : ℂ → ℂ) ⟨x, y⟩ Complex.I) = (y : ℂ) * (Complex.exp (↑(-2 * Real.pi * x * k) * Complex.I) *
    fderiv ℝ (F : ℂ → ℂ) ⟨x, y⟩ Complex.I)
  ring

end Qschubert
