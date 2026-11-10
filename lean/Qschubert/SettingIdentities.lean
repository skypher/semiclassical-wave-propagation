import Qschubert.Setting
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Identities of the Setting section

`Δ = X² + Y² - Y` on `C²` functions (manuscript, Section "Setting"), hence `Δ(0) = Δ`.
-/

namespace Qschubert

open UpperHalfPlane Complex Filter Topology

/-- Functions on `ℍ` that are `C²` in the sense of their extension `f ∘ ofComplex`. -/
def IsC2H (f : ℍ → ℂ) : Prop := ∀ z : ℍ, ContDiffAt ℝ 2 (extC f) (z : ℂ)

lemma extC_eventuallyEq {F : ℍ → ℂ} {G : ℂ → ℂ} (h : ∀ w : ℍ, F w = G (w : ℂ)) (z : ℍ) :
    extC F =ᶠ[𝓝 (z : ℂ)] G := by
  have hopen : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
  filter_upwards [hopen.mem_nhds z.im_pos] with w hw
  simp only [extC, ofComplex_apply_of_im_pos hw, h]

lemma dX_eq_of {F : ℍ → ℂ} {G : ℂ → ℂ} (h : ∀ w : ℍ, F w = G (w : ℂ)) (z : ℍ) :
    dX F z = fderiv ℝ G (z : ℂ) 1 := by
  simp only [dX, (extC_eventuallyEq h z).fderiv_eq]

lemma dY_eq_of {F : ℍ → ℂ} {G : ℂ → ℂ} (h : ∀ w : ℍ, F w = G (w : ℂ)) (z : ℍ) :
    dY F z = fderiv ℝ G (z : ℂ) Complex.I := by
  simp only [dY, (extC_eventuallyEq h z).fderiv_eq]

/-- Derivative of `w ↦ fderiv f w v₀` in the direction `v`. -/
lemma fderiv_apply_const {f : ℂ → ℂ} {z : ℂ} (hf : ContDiffAt ℝ 2 f z) (v₀ v : ℂ) :
    fderiv ℝ (fun w => fderiv ℝ f w v₀) z v = fderiv ℝ (fderiv ℝ f) z v v₀ := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [fderiv_clm_apply hd (differentiableAt_const v₀)]
  simp

/-- Derivative of `w ↦ (Im w) · fderiv f w v₀` in the direction `v`. -/
lemma fderiv_im_mul {f : ℂ → ℂ} {z : ℂ} (hf : ContDiffAt ℝ 2 f z) (v₀ v : ℂ) :
    fderiv ℝ (fun w : ℂ => ((w.im : ℝ) : ℂ) * fderiv ℝ f w v₀) z v
      = (v.im : ℂ) * fderiv ℝ f z v₀ + (z.im : ℂ) * fderiv ℝ (fderiv ℝ f) z v v₀ := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hd2 : DifferentiableAt ℝ (fun w => fderiv ℝ f w v₀) z := hd.clm_apply (differentiableAt_const v₀)
  have him : HasFDerivAt (fun w : ℂ => ((w.im : ℝ) : ℂ)) (ofRealCLM.comp imCLM) z :=
    (ofRealCLM.comp imCLM).hasFDerivAt
  have e : (fun w : ℂ => ((w.im : ℝ) : ℂ) * fderiv ℝ f w v₀)
      = (fun w : ℂ => ((w.im : ℝ) : ℂ)) * (fun w => fderiv ℝ f w v₀) := rfl
  rw [e, (him.mul hd2.hasFDerivAt).fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul,
    ContinuousLinearMap.comp_apply, imCLM_apply, ofRealCLM_apply]
  rw [fderiv_apply_const hf v₀ v]
  ring

lemma vecX_vecX_eq {f : ℍ → ℂ} (hf : IsC2H f) (z : ℍ) :
    vecX (vecX f) z = (z.im : ℂ) ^ 2 * fderiv ℝ (fderiv ℝ (extC f)) (z : ℂ) 1 1 := by
  have h := hf z
  have hvX : dX (vecX f) z = (z.im : ℂ) * fderiv ℝ (fderiv ℝ (extC f)) (z : ℂ) 1 1 := by
    rw [dX_eq_of (F := vecX f) (G := fun w : ℂ => ((w.im : ℝ) : ℂ) * fderiv ℝ (extC f) w 1)
      (fun w => rfl) z, fderiv_im_mul h]
    simp
  rw [vecX, hvX]; ring

lemma vecY_vecY_sub_eq {f : ℍ → ℂ} (hf : IsC2H f) (z : ℍ) :
    vecY (vecY f) z - vecY f z
      = (z.im : ℂ) ^ 2 * fderiv ℝ (fderiv ℝ (extC f)) (z : ℂ) Complex.I Complex.I := by
  have h := hf z
  have hvY : dY (vecY f) z = fderiv ℝ (extC f) (z : ℂ) Complex.I
      + (z.im : ℂ) * fderiv ℝ (fderiv ℝ (extC f)) (z : ℂ) Complex.I Complex.I := by
    rw [dY_eq_of (F := vecY f) (G := fun w : ℂ => ((w.im : ℝ) : ℂ) * fderiv ℝ (extC f) w Complex.I)
      (fun w => rfl) z, fderiv_im_mul h]
    simp
  have hdY : dY f z = fderiv ℝ (extC f) (z : ℂ) Complex.I := rfl
  rw [vecY, vecY, hvY, hdY]; ring

/-- `Δ = X² + Y² - Y` on `C²` functions. -/
theorem lapH_eq_vec {f : ℍ → ℂ} (hf : IsC2H f) (z : ℍ) :
    lapH f z = vecX (vecX f) z + vecY (vecY f) z - vecY f z := by
  have h := hf z
  -- second derivatives
  have hXX : dX (dX f) z = fderiv ℝ (fderiv ℝ (extC f)) (z : ℂ) 1 1 := by
    rw [dX_eq_of (F := dX f) (G := fun w => fderiv ℝ (extC f) w 1) (fun w => rfl) z,
      fderiv_apply_const h]
  have hYY : dY (dY f) z = fderiv ℝ (fderiv ℝ (extC f)) (z : ℂ) Complex.I Complex.I := by
    rw [dY_eq_of (F := dY f) (G := fun w => fderiv ℝ (extC f) w Complex.I) (fun w => rfl) z,
      fderiv_apply_const h]
  have hvX : dX (vecX f) z = (z.im : ℂ) * fderiv ℝ (fderiv ℝ (extC f)) (z : ℂ) 1 1 := by
    rw [dX_eq_of (F := vecX f) (G := fun w : ℂ => ((w.im : ℝ) : ℂ) * fderiv ℝ (extC f) w 1)
      (fun w => rfl) z,
      fderiv_im_mul h]
    simp
  have hvY : dY (vecY f) z = fderiv ℝ (extC f) (z : ℂ) Complex.I
      + (z.im : ℂ) * fderiv ℝ (fderiv ℝ (extC f)) (z : ℂ) Complex.I Complex.I := by
    rw [dY_eq_of (F := vecY f) (G := fun w : ℂ => ((w.im : ℝ) : ℂ) * fderiv ℝ (extC f) w Complex.I)
      (fun w => rfl) z, fderiv_im_mul h]
    simp
  have hdY : dY f z = fderiv ℝ (extC f) (z : ℂ) Complex.I := rfl
  simp only [lapH, vecX, vecY, hXX, hYY, hvX, hvY, hdY]
  ring

/-- `Δ(0) = Δ` on `C²` functions. -/
theorem lapT_zero {f : ℍ → ℂ} (hf : IsC2H f) (z : ℍ) : lapT 0 f z = lapH f z := by
  rw [lapH_eq_vec hf z, lapT]
  simp

end Qschubert

namespace Qschubert

open UpperHalfPlane Complex Filter Topology

/-- The real-linear map `x + i y ↦ x + i e^t y`. -/
noncomputable def dilL (t : ℝ) : ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => ⟨w.re, Real.exp t * w.im⟩
      map_add' := fun v w => by apply Complex.ext <;> simp; ring
      map_smul' := fun c w => by apply Complex.ext <;> simp; ring }

lemma dilL_apply (t : ℝ) (w : ℂ) : dilL t w = ⟨w.re, Real.exp t * w.im⟩ := rfl

lemma dilL_one (t : ℝ) : dilL t 1 = 1 := by apply Complex.ext <;> simp [dilL_apply]

lemma dilL_I (t : ℝ) : dilL t Complex.I = (Real.exp t : ℝ) • Complex.I := by
  apply Complex.ext <;> simp [dilL_apply, Complex.exp_ofReal_re, Complex.exp_ofReal_im]

lemma coe_dilate (t : ℝ) (z : ℍ) : ((dilate t z : ℍ) : ℂ) = dilL t (z : ℂ) := rfl

lemma dilate_neg (t : ℝ) (z : ℍ) : dilate t (dilate (-t) z) = z := by
  apply UpperHalfPlane.ext
  apply Complex.ext
  · rfl
  · show Real.exp t * (Real.exp (-t) * z.im) = z.im
    rw [← mul_assoc, ← Real.exp_add]; simp

/-- Derivative of `w ↦ fderiv F (L w) v₀` in the direction `v`, for a continuous linear `L`. -/
lemma fderiv_apply_const_comp {F : ℂ → ℂ} (L : ℂ →L[ℝ] ℂ) {z : ℂ}
    (hF : ContDiffAt ℝ 2 F (L z)) (v₀ v : ℂ) :
    fderiv ℝ (fun w => fderiv ℝ F (L w) v₀) z v = fderiv ℝ (fderiv ℝ F) (L z) (L v) v₀ := by
  have hd : DifferentiableAt ℝ (fderiv ℝ F) (L z) :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hcomp : HasFDerivAt (fun w => fderiv ℝ F (L w)) ((fderiv ℝ (fderiv ℝ F) (L z)).comp L) z :=
    hd.hasFDerivAt.comp z L.hasFDerivAt
  rw [fderiv_clm_apply hcomp.differentiableAt (differentiableAt_const v₀), hcomp.fderiv]
  simp

/-- `∂ (c · F ∘ L)` in the direction `v`. -/
lemma fderiv_const_mul_comp {F : ℂ → ℂ} (L : ℂ →L[ℝ] ℂ) (c : ℂ) {z : ℂ}
    (hF : DifferentiableAt ℝ F (L z)) (v : ℂ) :
    fderiv ℝ (fun w => c * F (L w)) z v = c * fderiv ℝ F (L z) (L v) := by
  have h : HasFDerivAt (fun w => F (L w)) ((fderiv ℝ F (L z)).comp L) z :=
    hF.hasFDerivAt.comp z L.hasFDerivAt
  rw [(h.const_mul c).fderiv]
  simp

/-- Schubert (2.9): `Δ(t) = S(t)⁻¹ Δ S(t)` on `C²` functions, with `S(t)⁻¹ = S(-t)`. -/
theorem lapT_eq_conj {f : ℍ → ℂ} (hf : IsC2H f) (t : ℝ) (z : ℍ) :
    lapT t f z = transportS (-t) (lapH (transportS t f)) z := by
  set c : ℂ := (Real.exp (-t / 2) : ℂ) with hc
  set F := extC f with hFdef
  set z' := dilate (-t) z with hz'
  have hLz : dilL t (z' : ℂ) = (z : ℂ) := by rw [← coe_dilate, hz', dilate_neg]
  have hC2 : ∀ w : ℍ, ContDiffAt ℝ 2 F (dilL t (w : ℂ)) := fun w => by
    rw [← coe_dilate]; exact hf _
  have hS : ∀ w : ℍ, transportS t f w = c * F (dilL t (w : ℂ)) := by
    intro w
    simp only [transportS, hc, hFdef, extC]
    congr 2
    apply UpperHalfPlane.ext
    rw [coe_dilate, ofComplex_apply_of_im_pos (by rw [← coe_dilate]; exact (dilate t w).im_pos)]
  have hdXS : ∀ w : ℍ, dX (transportS t f) w = c * fderiv ℝ F (dilL t (w : ℂ)) 1 := by
    intro w
    rw [dX_eq_of (G := fun w => c * F (dilL t w)) hS w,
      fderiv_const_mul_comp _ _ ((hC2 w).differentiableAt (by norm_num)), dilL_one]
  have hdYS : ∀ w : ℍ, dY (transportS t f) w
      = c * ((Real.exp t : ℂ) * fderiv ℝ F (dilL t (w : ℂ)) Complex.I) := by
    intro w
    rw [dY_eq_of (G := fun w => c * F (dilL t w)) hS w,
      fderiv_const_mul_comp _ _ ((hC2 w).differentiableAt (by norm_num)), dilL_I,
      map_smul, Complex.real_smul]
  have hXX : dX (dX (transportS t f)) z' = c * fderiv ℝ (fderiv ℝ F) (z : ℂ) 1 1 := by
    rw [dX_eq_of (G := fun w => c * fderiv ℝ F (dilL t w) 1) hdXS z']
    have hd : DifferentiableAt ℝ (fun w => fderiv ℝ F (dilL t w) 1) (z' : ℂ) :=
      ((((hC2 z').fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).comp _
        (dilL t).differentiableAt).clm_apply (differentiableAt_const 1)
    rw [fderiv_const_mul hd, smul_apply, smul_eq_mul,
      fderiv_apply_const_comp _ (hC2 z'), dilL_one, hLz]
  have hYY : dY (dY (transportS t f)) z'
      = c * ((Real.exp t : ℂ) * ((Real.exp t : ℂ) *
          fderiv ℝ (fderiv ℝ F) (z : ℂ) Complex.I Complex.I)) := by
    rw [dY_eq_of (G := fun w => c * ((Real.exp t : ℂ) * fderiv ℝ F (dilL t w) Complex.I)) hdYS z']
    have hd : DifferentiableAt ℝ (fun w => fderiv ℝ F (dilL t w) Complex.I) (z' : ℂ) :=
      ((((hC2 z').fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).comp _
        (dilL t).differentiableAt).clm_apply (differentiableAt_const Complex.I)
    rw [fderiv_const_mul (hd.const_mul _), smul_apply, smul_eq_mul,
      fderiv_const_mul hd, smul_apply, smul_eq_mul,
      fderiv_apply_const_comp _ (hC2 z'), dilL_I, hLz, map_smul,
      smul_apply, Complex.real_smul]
  have him' : (z'.im : ℂ) = (Real.exp (-t) : ℂ) * (z.im : ℂ) := by
    have : (z'.im : ℝ) = Real.exp (-t) * z.im := rfl
    rw [this]; push_cast; ring
  have hT : transportS (-t) (lapH (transportS t f)) z
      = (Real.exp (t / 2) : ℂ) * ((z'.im : ℂ) ^ 2 *
          (dX (dX (transportS t f)) z' + dY (dY (transportS t f)) z')) := by
    simp only [transportS, lapH, hz', neg_neg]
  rw [hT, hXX, hYY, him', lapT, add_sub_assoc, vecX_vecX_eq hf, vecY_vecY_sub_eq hf]
  have e1 : (Real.exp (t / 2) : ℂ) * c = 1 := by
    have h : Real.exp (t / 2) * Real.exp (-t / 2) = 1 := by
      rw [← Real.exp_add, show t / 2 + -t / 2 = 0 by ring, Real.exp_zero]
    rw [hc, ← Complex.ofReal_mul, h, Complex.ofReal_one]
  have e2 : (Real.exp (-t) : ℂ) ^ 2 = (Real.exp (-2 * t) : ℂ) := by
    rw [← Complex.ofReal_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
  have e3 : (Real.exp (-2 * t) : ℂ) * ((Real.exp t : ℂ) * (Real.exp t : ℂ)) = 1 := by
    have h : Real.exp (-2 * t) * (Real.exp t * Real.exp t) = 1 := by
      rw [← Real.exp_add, ← Real.exp_add, show -2 * t + (t + t) = 0 by ring, Real.exp_zero]
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, h, Complex.ofReal_one]
  set A := fderiv ℝ (fderiv ℝ (extC f)) (z : ℂ) 1 1
  set B := fderiv ℝ (fderiv ℝ (extC f)) (z : ℂ) Complex.I Complex.I
  set q := (Real.exp (-t) : ℂ) ^ 2
  set r := (Real.exp t : ℂ)
  linear_combination (-(z.im : ℂ) ^ 2 * A * q - (z.im : ℂ) ^ 2 * B * q * r ^ 2) * e1
    + (-(z.im : ℂ) ^ 2 * A - (z.im : ℂ) ^ 2 * B * r ^ 2) * e2 + (-(z.im : ℂ) ^ 2 * B) * e3

end Qschubert
