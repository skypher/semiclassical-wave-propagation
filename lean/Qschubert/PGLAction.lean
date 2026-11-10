import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
import Qschubert.OrbitCount

/-!
# `PGL(2, ℝ)` acts on `ℍ` by measure-preserving isometries

Mathlib provides the action of `GL(2, ℝ)` and of `PGL(2, ℝ)` on `ℍ` (orientation-reversing elements
act through complex conjugation), the `GL(2, ℝ)`-invariant measure `dx dy / y²`, and the
isometric action of `SL(2, ℝ)`. This file proves that every `g ∈ GL(2, ℝ)` acts isometrically, and
derives the isometry, continuity and measure-invariance instances for `PGL(2, ℝ)` and its
subgroups. `PGL(2, ℝ)` acts faithfully, so a Fuchsian group is a subgroup of it, and
`pgl_setLIntegral_ball_le` states Lemma G4.3, Step 2, for every countable `Γ ≤ PGL(2, ℝ)` with a
fundamental domain, without the lifting restriction of `fuchsian_setLIntegral_ball_le`.
-/

namespace Qschubert

open UpperHalfPlane Complex MeasureTheory Metric
open scoped MatrixGroups ComplexConjugate ENNReal

/-- Möbius difference formula. -/
lemma moebius_sub (g : GL (Fin 2) ℝ) {z w : ℂ} (hz : denom g z ≠ 0) (hw : denom g w ≠ 0) :
    num g z / denom g z - num g w / denom g w
      = ((g.det : ℝ) : ℂ) * (z - w) / (denom g z * denom g w) := by
  rw [div_sub_div _ _ hz hw]
  congr 1
  simp only [num, denom, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
  push_cast
  ring

/-- `σ g` (the identity or complex conjugation) preserves distances. -/
lemma dist_σ (g : GL (Fin 2) ℝ) (u v : ℂ) : dist (σ g u) (σ g v) = dist u v := by
  unfold σ
  split_ifs
  · simp
  · simp [Complex.dist_conj_conj]

lemma im_gl_smul (g : GL (Fin 2) ℝ) (z : ℍ) :
    (g • z).im = |(g.det : ℝ)| * z.im / Complex.normSq (denom g z) :=
  smulAux'_im g z

/-- Every `g ∈ GL(2, ℝ)` acts on `ℍ` isometrically. -/
theorem gl_dist_smul (g : GL (Fin 2) ℝ) (z w : ℍ) : dist (g • z) (g • w) = dist z w := by
  have hz : denom g z ≠ 0 := denom_ne_zero g z
  have hw : denom g w ≠ 0 := denom_ne_zero g w
  have hdet : |(g.det : ℝ)| ≠ 0 := abs_ne_zero.mpr g.det.ne_zero
  have hdz : 0 < ‖denom g z‖ := norm_pos_iff.mpr hz
  have hdw : 0 < ‖denom g w‖ := norm_pos_iff.mpr hw
  rw [UpperHalfPlane.dist_eq, UpperHalfPlane.dist_eq]
  congr 2
  have hnum : dist ((g • z : ℍ) : ℂ) (g • w : ℍ)
      = |(g.det : ℝ)| * dist (z : ℂ) w / (‖denom g z‖ * ‖denom g w‖) := by
    rw [coe_smul, coe_smul, dist_σ, dist_eq_norm, moebius_sub g hz hw, norm_div, norm_mul, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, ← dist_eq_norm]
  have him : (g • z).im * (g • w).im
      = (|(g.det : ℝ)| / (‖denom g z‖ * ‖denom g w‖)) ^ 2 * (z.im * w.im) := by
    rw [im_gl_smul, im_gl_smul, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    field_simp
  have hk : 0 ≤ |(g.det : ℝ)| / (‖denom g z‖ * ‖denom g w‖) := by positivity
  have hsq : √((g • z).im * (g • w).im)
      = |(g.det : ℝ)| / (‖denom g z‖ * ‖denom g w‖) * √(z.im * w.im) := by
    rw [him, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hk]
  have hzw : 0 < √(z.im * w.im) := Real.sqrt_pos.mpr (mul_pos z.im_pos w.im_pos)
  rw [hnum, hsq]
  field_simp

instance : IsIsometricSMul (GL (Fin 2) ℝ) ℍ :=
  ⟨fun g => Isometry.of_dist_eq (gl_dist_smul g)⟩

instance : IsIsometricSMul PGL(2, ℝ) ℍ :=
  ⟨fun c => by
    obtain ⟨g, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective c
    exact Isometry.of_dist_eq fun z w => by
      simp only [pglMk_smul]
      exact gl_dist_smul g z w⟩

instance : ContinuousConstSMul PGL(2, ℝ) ℍ :=
  ⟨fun c => (isometry_smul ℍ c).continuous⟩

instance : SMulInvariantMeasure PGL(2, ℝ) ℍ volume :=
  ⟨fun c s hs => by
    obtain ⟨g, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective c
    have e : (fun x : ℍ => Matrix.ProjGenLinGroup.mk g • x) = fun x => g • x :=
      funext (pglMk_smul g)
    rw [e]
    exact SMulInvariantMeasure.measure_preimage_smul (μ := (volume : Measure ℍ)) g hs⟩

instance (Γ : Subgroup PGL(2, ℝ)) : IsIsometricSMul Γ ℍ :=
  ⟨fun γ => isometry_smul ℍ (γ : PGL(2, ℝ))⟩

instance (Γ : Subgroup PGL(2, ℝ)) : SMulInvariantMeasure Γ ℍ volume :=
  ⟨fun γ _ hs => SMulInvariantMeasure.measure_preimage_smul (μ := (volume : Measure ℍ))
    (γ : PGL(2, ℝ)) hs⟩

/-- Lemma G4.3, Step 2, on `ℍ` for every countable `Γ ≤ PGL(2, ℝ)` with a fundamental domain
(in particular every Fuchsian group): `∫_{B(z,1)} f dν ≤ m(z) ∫_F f dν` for `Γ`-invariant
measurable `f ≥ 0`, with `m(z) = #{γ ∈ Γ : d(z, γ z) < 2}`. -/
theorem pgl_setLIntegral_ball_le (Γ : Subgroup PGL(2, ℝ)) [Countable Γ] {F : Set ℍ}
    (hF : IsFundamentalDomain Γ F volume) {f : ℍ → ℝ≥0∞} (hf : Measurable f)
    (hinv : ∀ (γ : Γ) (z : ℍ), f (γ • z) = f z) (z : ℍ) :
    ∫⁻ x in ball z 1, f x ≤ (orbitMult Γ z : ℝ≥0∞) * ∫⁻ x in F, f x :=
  setLIntegral_ball_le_orbitMult_mul hF hf hinv z

end Qschubert
