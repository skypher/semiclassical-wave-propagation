import Qschubert.Mobius

/-!
# The energy density is invariant under the isometries of `ℍ`

Spine stage S4 (`lean/BLUEPRINT.md`). `gradPair f k w = ∂ₓf ∂ₓk̄ + ∂_yf ∂_yk̄` at `w`, and on `ℍ` the
hyperbolic energy density `hgrad A B = y² gradPair`. For every `g ∈ GL(2, ℝ)`:
`hgrad (A ∘ g) (B ∘ g) = hgrad A B ∘ g` (`hgrad_comp_smul`), the first-order analogue of
`lapH_comp_smul`, from the identity `a(c) conj(b(c)) + a(ic) conj(b(ic)) = |c|² (a(1) conj(b(1)) + a(i) conj(b(i)))`
for real-linear `a, b`.
-/

namespace Qschubert

open Complex Filter Topology
open scoped ComplexConjugate ContDiff MatrixGroups UpperHalfPlane

/-- `∂ₓf ∂ₓk̄ + ∂_yf ∂_yk̄` at `w`. -/
noncomputable def gradPair (f k : ℂ → ℂ) (w : ℂ) : ℂ :=
  fderiv ℝ f w 1 * conj (fderiv ℝ k w 1) + fderiv ℝ f w I * conj (fderiv ℝ k w I)

lemma sesq_rot_aux (a b : ℂ →L[ℝ] ℂ) (p q : ℝ) :
    a (p • (1 : ℂ) + q • I) * conj (b (p • (1 : ℂ) + q • I))
      + a ((-q) • (1 : ℂ) + p • I) * conj (b ((-q) • (1 : ℂ) + p • I))
      = ((p ^ 2 + q ^ 2 : ℝ) : ℂ) * (a 1 * conj (b 1) + a I * conj (b I)) := by
  simp only [map_add, map_smul]
  simp only [Complex.real_smul, map_mul, Complex.conj_ofReal]
  push_cast
  ring

/-- For real-linear `a, b` and `c ∈ ℂ`:
`a(c) conj(b(c)) + a(ic) conj(b(ic)) = |c|² (a(1) conj(b(1)) + a(i) conj(b(i)))`. -/
lemma sesq_rot (a b : ℂ →L[ℝ] ℂ) (c : ℂ) :
    a c * conj (b c) + a (I * c) * conj (b (I * c))
      = ((Complex.normSq c : ℝ) : ℂ) * (a 1 * conj (b 1) + a I * conj (b I)) := by
  have hc : c = c.re • (1 : ℂ) + c.im • I := by apply Complex.ext <;> simp
  have hIc : I * c = (-c.im) • (1 : ℂ) + c.re • I := by apply Complex.ext <;> simp
  rw [hIc, Complex.normSq_apply]
  conv_lhs => rw [show a c * conj (b c) = a (c.re • (1 : ℂ) + c.im • I)
    * conj (b (c.re • (1 : ℂ) + c.im • I)) by rw [← hc]]
  rw [sesq_rot_aux]
  congr 2
  ring

lemma gradPair_comp {f k m : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f (m z))
    (hk : DifferentiableAt ℝ k (m z)) (hm : DifferentiableAt ℝ m z) :
    gradPair (f ∘ m) (k ∘ m) z
      = fderiv ℝ f (m z) (fderiv ℝ m z 1) * conj (fderiv ℝ k (m z) (fderiv ℝ m z 1))
        + fderiv ℝ f (m z) (fderiv ℝ m z I) * conj (fderiv ℝ k (m z) (fderiv ℝ m z I)) := by
  rw [gradPair, fderiv_comp z hf hm, fderiv_comp z hk hm]
  rfl

/-- On `ℍ`: the hyperbolic energy density `y² (∂ₓA ∂ₓB̄ + ∂_yA ∂_yB̄)`. -/
noncomputable def hgrad (A B : ℍ → ℂ) (z : ℍ) : ℂ := (z.im : ℂ) ^ 2 * gradPair (extC A) (extC B) z

lemma extC_smul_eventuallyEq (g : GL (Fin 2) ℝ) (A : ℍ → ℂ) (z : ℍ) :
    extC (fun w => A (g • w)) =ᶠ[𝓝 (z : ℂ)] fun y => extC A (UpperHalfPlane.σ g (moeb g y)) := by
  have hopen : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
  filter_upwards [hopen.mem_nhds z.im_pos] with w hw
  have hw' : ((g • (⟨w, hw⟩ : ℍ) : ℍ) : ℂ) = UpperHalfPlane.σ g (moeb g w) := rfl
  have hpos' : 0 < (UpperHalfPlane.σ g (moeb g w)).im := by
    rw [← hw']; exact (g • (⟨w, hw⟩ : ℍ)).im_pos
  simp only [extC, UpperHalfPlane.ofComplex_apply_of_im_pos hw,
    UpperHalfPlane.ofComplex_apply_of_im_pos hpos']
  congr 1

/-- **The energy density is invariant**: `hgrad (A ∘ g) (B ∘ g) z = hgrad A B (g z)` for every
`g ∈ GL(2, ℝ)`, where `A, B` are differentiable at `g z`. -/
theorem hgrad_comp_smul (g : GL (Fin 2) ℝ) {A B : ℍ → ℂ} (z : ℍ)
    (hA : DifferentiableAt ℝ (extC A) ((g • z : ℍ) : ℂ))
    (hB : DifferentiableAt ℝ (extC B) ((g • z : ℍ) : ℂ)) :
    hgrad (fun w => A (g • w)) (fun w => B (g • w)) z = hgrad A B (g • z) := by
  have hzU : (z : ℂ) ∈ {w : ℂ | UpperHalfPlane.denom g w ≠ 0} := UpperHalfPlane.denom_ne_zero g z
  have hmd := hasDerivAt_moeb g hzU
  set c := ((g.det : ℝ) : ℂ) / UpperHalfPlane.denom g z ^ 2
  have hmR : ∀ v, fderiv ℝ (moeb g) z v = v * c := fun v => by
    rw [(hmd.hasFDerivAt.restrictScalars ℝ).fderiv]; simp
  have hmdiff : DifferentiableAt ℝ (moeb g) z := (hmd.differentiableAt).restrictScalars ℝ
  have key : (((g • z).im : ℝ) : ℂ) ^ 2 = ((z.im : ℝ) : ℂ) ^ 2 * ((Complex.normSq c : ℝ) : ℂ) := by
    have := normSq_deriv_moeb g z
    rw [hmd.deriv] at this
    exact_mod_cast this.symm
  have hfd : ∀ C : ℍ → ℂ, fderiv ℝ (extC (fun w => C (g • w))) z
      = fderiv ℝ (fun y => extC C (UpperHalfPlane.σ g (moeb g y))) z :=
    fun C => (extC_smul_eventuallyEq g C z).fderiv_eq
  unfold hgrad gradPair
  rw [hfd A, hfd B]
  by_cases hpos : 0 < g.det.val
  · have hσ : ∀ w, UpperHalfPlane.σ g w = w := fun w => by
      rw [UpperHalfPlane.σ, ite_eq_left hpos]; rfl
    have hval : ((g • z : ℍ) : ℂ) = moeb g z := UpperHalfPlane.coe_smul_of_det_pos hpos z
    simp only [hσ]
    rw [hval] at hA hB ⊢
    have e := gradPair_comp hA hB hmdiff
    unfold gradPair at e
    simp only [Function.comp_def] at e
    rw [e, hmR, hmR, one_mul, sesq_rot, key]
    ring
  · have hσ : ∀ w, UpperHalfPlane.σ g w = conj w := fun w => by
      rw [UpperHalfPlane.σ, ite_eq_right hpos]; rfl
    have hval : ((g • z : ℍ) : ℂ) = conj (moeb g z) := by
      rw [UpperHalfPlane.coe_smul, hσ]; rfl
    simp only [hσ]
    rw [hval] at hA hB ⊢
    have hconj : DifferentiableAt ℝ (fun y => conj (moeb g y)) z :=
      Complex.conjCLE.differentiableAt.comp (z : ℂ) hmdiff
    have hcR : ∀ v, fderiv ℝ (fun y => conj (moeb g y)) z v = conj (v * c) := fun v => by
      rw [show (fun y => conj (moeb g y)) = Complex.conjCLE ∘ moeb g from rfl,
        fderiv_comp (z : ℂ) Complex.conjCLE.differentiableAt hmdiff, ContinuousLinearEquiv.fderiv]
      simp [hmR]
    have e := gradPair_comp (m := fun y => conj (moeb g y)) hA hB hconj
    unfold gradPair at e
    simp only [Function.comp_def] at e
    rw [e, hcR, hcR]
    have h1 : conj (1 * c) = conj c := by rw [one_mul]
    have h2 : conj (I * c) = -(I * conj c) := by simp [map_mul, Complex.conj_I]
    rw [h1, h2, map_neg, map_neg, map_neg, neg_mul_neg, sesq_rot, Complex.normSq_conj, key]
    ring

end Qschubert
