import Qschubert.LaplacianSymm
import Qschubert.PGLAction
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# `Δ` commutes with the isometries of `ℍ`

Spine stage S4 (`lean/BLUEPRINT.md`). For `m` holomorphic, `Δ_E (f ∘ m) = |m'|² (Δ_E f) ∘ m`
(`lapE_comp_holo`; the second-order term `Df[m'' (1² + i²)]` vanishes and the rotation identity
`B(c,c) + B(ic,ic) = |c|² (B(1,1) + B(i,i))` handles the first-order part). Composition with complex
conjugation preserves `Δ_E` (`lapE_comp_conj`). With `Im(g z) = |det g| Im z / |cz + d|²` and
`|m'(z)| = |det g| / |cz + d|²` this gives `Δ(A ∘ g) = (ΔA) ∘ g` for every `g ∈ GL(2, ℝ)`, of either
determinant sign (`lapH_comp_smul`), and for every `g ∈ PGL(2, ℝ)` (`lapH_comp_pgl_smul`).
-/

namespace Qschubert

open Complex Filter Topology
open scoped ComplexConjugate ContDiff MatrixGroups UpperHalfPlane

lemma bilin_rot_aux (B : ℂ →L[ℝ] ℂ →L[ℝ] ℂ) (p q : ℝ) :
    B (p • (1 : ℂ) + q • I) (p • (1 : ℂ) + q • I) + B ((-q) • (1 : ℂ) + p • I) ((-q) • (1 : ℂ) + p • I)
      = ((p ^ 2 + q ^ 2 : ℝ) : ℂ) * (B 1 1 + B I I) := by
  simp only [map_add, map_smul, add_apply, smul_apply]
  simp only [Complex.real_smul]
  push_cast
  ring

/-- For `ℝ`-bilinear `B` and `c ∈ ℂ`: `B(c,c) + B(ic,ic) = |c|² (B(1,1) + B(i,i))`. -/
lemma bilin_rot (B : ℂ →L[ℝ] ℂ →L[ℝ] ℂ) (c : ℂ) :
    B c c + B (I * c) (I * c) = ((Complex.normSq c : ℝ) : ℂ) * (B 1 1 + B I I) := by
  have hc : c = c.re • (1 : ℂ) + c.im • I := by
    apply Complex.ext <;> simp
  have hIc : I * c = (-c.im) • (1 : ℂ) + c.re • I := by
    apply Complex.ext <;> simp
  rw [hIc, Complex.normSq_apply]
  conv_lhs => rw [show B c c = B (c.re • (1 : ℂ) + c.im • I) (c.re • (1 : ℂ) + c.im • I) by
    rw [← hc]]
  rw [bilin_rot_aux]
  congr 2
  ring

/-- **Conformal change of `Δ_E`.** For `m` holomorphic on an open `U ∋ z` and `f` `C²` at `m z`:
`Δ_E (f ∘ m)(z) = |m'(z)|² (Δ_E f)(m z)`. -/
theorem lapE_comp_holo {f m : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hm : DifferentiableOn ℂ m U)
    {z : ℂ} (hz : z ∈ U) (hf : ContDiffAt ℝ 2 f (m z)) :
    lapE (f ∘ m) z = ((Complex.normSq (deriv m z) : ℝ) : ℂ) * lapE f (m z) := by
  have hUz : U ∈ 𝓝 z := hU.mem_nhds hz
  have hmd : ∀ w ∈ U, HasDerivAt m (deriv m w) w :=
    fun w hw => (hm.differentiableAt (hU.mem_nhds hw)).hasDerivAt
  have hmR : ∀ w ∈ U, ∀ v, fderiv ℝ m w v = v * deriv m w := fun w hw v => by
    rw [((hmd w hw).hasFDerivAt.restrictScalars ℝ).fderiv]
    simp
  have hmC : ContDiffAt ℝ 2 m z := ((hm.contDiffOn hU).contDiffAt hUz).restrict_scalars ℝ
  have hm' : DifferentiableAt ℂ (deriv m) z := (hm.deriv hU).differentiableAt hUz
  have hfev : ∀ᶠ w in 𝓝 z, ContDiffAt ℝ 2 f (m w) :=
    hmC.continuousAt.tendsto.eventually (hf.eventually (by simp))
  have hfirst : ∀ v : ℂ, (fun w => fderiv ℝ (f ∘ m) w v)
      =ᶠ[𝓝 z] fun w => fderiv ℝ f (m w) (v * deriv m w) := by
    intro v
    filter_upwards [hfev, hUz] with w hw hwU
    rw [fderiv_comp w (hw.differentiableAt (by norm_num))
      ((hm.differentiableAt (hU.mem_nhds hwU)).restrictScalars ℝ)]
    simp [hmR w hwU v]
  have hsecond : ∀ v : ℂ, fderiv ℝ (fderiv ℝ (f ∘ m)) z v v
      = fderiv ℝ (fderiv ℝ f) (m z) (v * deriv m z) (v * deriv m z)
        + fderiv ℝ f (m z) (v * (v * deriv (deriv m) z)) := by
    intro v
    rw [← fderiv_apply_const (hf.comp z hmC) v v, (hfirst v).fderiv_eq]
    have hL : HasFDerivAt (fun w => fderiv ℝ f (m w))
        ((fderiv ℝ (fderiv ℝ f) (m z)).comp (fderiv ℝ m z)) z :=
      ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt.comp z
        (hmC.differentiableAt (by norm_num)).hasFDerivAt
    have hφ : HasFDerivAt (fun w => v * deriv m w)
        (((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (v * deriv (deriv m) z))).restrictScalars ℝ) z :=
      ((hm'.hasDerivAt.const_mul v).hasFDerivAt).restrictScalars ℝ
    rw [(hL.clm_apply hφ).fderiv]
    simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.smulRight_apply,
      one_apply_eq_self, smul_eq_mul, hmR z hz v]
    ring_nf
  have hzero : fderiv ℝ f (m z) (1 * (1 * deriv (deriv m) z))
      + fderiv ℝ f (m z) (I * (I * deriv (deriv m) z)) = 0 := by
    rw [← map_add]
    have : 1 * (1 * deriv (deriv m) z) + I * (I * deriv (deriv m) z) = 0 := by
      rw [← mul_assoc I, I_mul_I]; ring
    rw [this, map_zero]
  have hrot := bilin_rot (fderiv ℝ (fderiv ℝ f) (m z)) (deriv m z)
  unfold lapE
  rw [hsecond 1, hsecond I]
  simp only [one_mul] at hzero ⊢
  linear_combination hrot + hzero

/-- Complex conjugation preserves `Δ_E`: `Δ_E (f ∘ conj)(w) = (Δ_E f)(conj w)`. -/
theorem lapE_comp_conj {f : ℂ → ℂ} {w : ℂ} (hf : ContDiffAt ℝ 2 f (conj w)) :
    lapE (fun y => f (conj y)) w = lapE f (conj w) := by
  set L : ℂ →L[ℝ] ℂ := Complex.conjCLE.toContinuousLinearMap
  have hLy : ∀ y, L y = conj y := fun y => rfl
  have hcomp : (fun y => f (conj y)) = f ∘ L := rfl
  have hfL : ContDiffAt ℝ 2 f (L w) := hf
  have hfev : ∀ᶠ y in 𝓝 w, ContDiffAt ℝ 2 f (L y) :=
    L.continuous.continuousAt.tendsto.eventually (hfL.eventually (by simp))
  have hC : ContDiffAt ℝ 2 (f ∘ L) w := hfL.comp w L.contDiff.contDiffAt
  have hfirst : ∀ v, (fun y => fderiv ℝ (f ∘ L) y v) =ᶠ[𝓝 w] fun y => fderiv ℝ f (L y) (L v) := by
    intro v
    filter_upwards [hfev] with y hy
    rw [fderiv_comp y (hy.differentiableAt (by norm_num)) L.differentiableAt, L.fderiv]
    rfl
  have hsecond : ∀ v, fderiv ℝ (fderiv ℝ (f ∘ L)) w v v
      = fderiv ℝ (fderiv ℝ f) (L w) (L v) (L v) := by
    intro v
    rw [← fderiv_apply_const hC v v, (hfirst v).fderiv_eq]
    have hL : HasFDerivAt (fun y => fderiv ℝ f (L y)) ((fderiv ℝ (fderiv ℝ f) (L w)).comp L) w :=
      ((hfL.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt.comp w
        L.hasFDerivAt
    rw [(hL.clm_apply (hasFDerivAt_const (L v) w)).fderiv]
    simp
  unfold lapE
  rw [hcomp, hsecond 1, hsecond I]
  simp [hLy]

lemma extC_fderiv_eventuallyEq {A : ℍ → ℂ} {G : ℂ → ℂ} {z : ℍ}
    (h : extC A =ᶠ[𝓝 (z : ℂ)] G) (v : ℂ) :
    extC (fun w : ℍ => fderiv ℝ (extC A) (w : ℂ) v) =ᶠ[𝓝 (z : ℂ)] fun w => fderiv ℝ G w v := by
  have hopen : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
  filter_upwards [h.eventuallyEq_nhds, hopen.mem_nhds z.im_pos] with w hw hwpos
  simp only [extC, UpperHalfPlane.ofComplex_apply_of_im_pos hwpos]
  show fderiv ℝ (extC A) w v = _
  rw [hw.fderiv_eq]

/-- Local form of `lapH_eq_im_sq_lapE`: if `A ∘ UpperHalfPlane.ofComplex` agrees near `z` with a function `G`
that is `C²` at `z`, then `Δ A (z) = y² Δ_E G (z)`. -/
theorem lapH_eq_of_eventuallyEq {A : ℍ → ℂ} {G : ℂ → ℂ} {z : ℍ} (hG : ContDiffAt ℝ 2 G z)
    (h : extC A =ᶠ[𝓝 (z : ℂ)] G) : lapH A z = (z.im : ℂ) ^ 2 * lapE G z := by
  have hX : dX (dX A) z = fderiv ℝ (fderiv ℝ G) z 1 1 := by
    show fderiv ℝ (extC (fun w : ℍ => fderiv ℝ (extC A) (w : ℂ) 1)) (z : ℂ) 1 = _
    rw [(extC_fderiv_eventuallyEq h 1).fderiv_eq, fderiv_apply_const hG 1 1]
  have hY : dY (dY A) z = fderiv ℝ (fderiv ℝ G) z I I := by
    show fderiv ℝ (extC (fun w : ℍ => fderiv ℝ (extC A) (w : ℂ) I)) (z : ℂ) I = _
    rw [(extC_fderiv_eventuallyEq h I).fderiv_eq, fderiv_apply_const hG I I]
  rw [lapH, hX, hY, lapE]

/-- The Möbius map `w ↦ (aw + b)/(cw + d)` of `g`, before the conjugation for `det g < 0`. -/
noncomputable def moeb (g : GL (Fin 2) ℝ) (w : ℂ) : ℂ := UpperHalfPlane.num g w / UpperHalfPlane.denom g w

lemma isOpen_denom_ne (g : GL (Fin 2) ℝ) : IsOpen {w : ℂ | UpperHalfPlane.denom g w ≠ 0} :=
  isOpen_ne_fun (by unfold UpperHalfPlane.denom; fun_prop) continuous_const

lemma hasDerivAt_moeb (g : GL (Fin 2) ℝ) {w : ℂ} (hw : UpperHalfPlane.denom g w ≠ 0) :
    HasDerivAt (moeb g) (((g.det : ℝ) : ℂ) / UpperHalfPlane.denom g w ^ 2) w := by
  have hn : HasDerivAt (UpperHalfPlane.num g) ((g 0 0 : ℝ) : ℂ) w := by
    have := ((hasDerivAt_id w).const_mul ((g 0 0 : ℝ) : ℂ)).add_const ((g 0 1 : ℝ) : ℂ)
    unfold UpperHalfPlane.num
    simpa only [mul_one, id_eq] using this
  have hd : HasDerivAt (UpperHalfPlane.denom g) ((g 1 0 : ℝ) : ℂ) w := by
    have := ((hasDerivAt_id w).const_mul ((g 1 0 : ℝ) : ℂ)).add_const ((g 1 1 : ℝ) : ℂ)
    unfold UpperHalfPlane.denom
    simpa only [mul_one, id_eq] using this
  have e : ((g.det : ℝ) : ℂ) / UpperHalfPlane.denom g w ^ 2
      = (((g 0 0 : ℝ) : ℂ) * UpperHalfPlane.denom g w - UpperHalfPlane.num g w * ((g 1 0 : ℝ) : ℂ))
        / UpperHalfPlane.denom g w ^ 2 := by
    congr 1
    simp only [UpperHalfPlane.num, UpperHalfPlane.denom, Matrix.GeneralLinearGroup.val_det_apply,
      Matrix.det_fin_two]
    push_cast
    ring
  rw [e]
  exact hn.div hd hw

lemma differentiableOn_moeb (g : GL (Fin 2) ℝ) :
    DifferentiableOn ℂ (moeb g) {w : ℂ | UpperHalfPlane.denom g w ≠ 0} :=
  fun _ hw => (hasDerivAt_moeb g hw).differentiableAt.differentiableWithinAt

lemma normSq_deriv_moeb (g : GL (Fin 2) ℝ) (z : ℍ) :
    (z.im : ℝ) ^ 2 * Complex.normSq (deriv (moeb g) z) = (g • z).im ^ 2 := by
  have hz := UpperHalfPlane.denom_ne_zero g z
  rw [(hasDerivAt_moeb g hz).deriv, im_gl_smul, Complex.normSq_div, Complex.normSq_ofReal,
    map_pow]
  have h0 : Complex.normSq (UpperHalfPlane.denom g z) ≠ 0 := (Complex.normSq_pos.2 hz).ne'
  rw [div_pow, mul_pow, sq_abs]
  field_simp

/-- **`Δ` commutes with every `g ∈ GL(2, ℝ)`**: `Δ(A ∘ g) = (ΔA) ∘ g` at every `z ∈ ℍ` where `A` is
`C²` at `g z`. -/
theorem lapH_comp_smul (g : GL (Fin 2) ℝ) {A : ℍ → ℂ} (z : ℍ)
    (hA : ContDiffAt ℝ 2 (extC A) ((g • z : ℍ) : ℂ)) :
    lapH (fun w => A (g • w)) z = lapH A (g • z) := by
  have hU := isOpen_denom_ne g
  have hzU : (z : ℂ) ∈ {w : ℂ | UpperHalfPlane.denom g w ≠ 0} := UpperHalfPlane.denom_ne_zero g z
  have hmC : ContDiffAt ℝ 2 (moeb g) z :=
    (((differentiableOn_moeb g).contDiffOn hU).contDiffAt (hU.mem_nhds hzU)).restrict_scalars ℝ
  have hopen : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
  have hrhs : lapH A (g • z) = ((g • z).im : ℂ) ^ 2 * lapE (extC A) ((g • z : ℍ) : ℂ) :=
    lapH_eq_of_eventuallyEq hA EventuallyEq.rfl
  rw [hrhs]
  by_cases hpos : 0 < g.det.val
  · have hval : ∀ w : ℍ, ((g • w : ℍ) : ℂ) = moeb g w := fun w => UpperHalfPlane.coe_smul_of_det_pos hpos w
    have hloc : extC (fun w => A (g • w)) =ᶠ[𝓝 (z : ℂ)] (extC A) ∘ moeb g := by
      filter_upwards [hopen.mem_nhds z.im_pos] with w hw
      have hw' := hval ⟨w, hw⟩
      have hpos' : 0 < (moeb g w).im := by rw [← show ((g • (⟨w, hw⟩ : ℍ) : ℍ) : ℂ) = moeb g w from hw']; exact (g • (⟨w, hw⟩ : ℍ)).im_pos
      simp only [extC, Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hw,
        UpperHalfPlane.ofComplex_apply_of_im_pos hpos']
      congr 1
      exact UpperHalfPlane.ext hw'
    have hA' : ContDiffAt ℝ 2 (extC A) (moeb g z) := by rw [← hval]; exact hA
    rw [lapH_eq_of_eventuallyEq (hA'.comp (z : ℂ) hmC) hloc,
      lapE_comp_holo hU (differentiableOn_moeb g) hzU hA', ← hval]
    have key : (((g • z).im : ℝ) : ℂ) ^ 2
        = ((z.im : ℝ) : ℂ) ^ 2 * ((Complex.normSq (deriv (moeb g) z) : ℝ) : ℂ) := by
      exact_mod_cast (normSq_deriv_moeb g z).symm
    rw [key]
    ring
  · have hval : ∀ w : ℍ, ((g • w : ℍ) : ℂ) = conj (moeb g w) := fun w => by
      rw [UpperHalfPlane.coe_smul, UpperHalfPlane.σ, ite_eq_right hpos]
      rfl
    have hloc : extC (fun w => A (g • w)) =ᶠ[𝓝 (z : ℂ)] (fun y => extC A (conj y)) ∘ moeb g := by
      filter_upwards [hopen.mem_nhds z.im_pos] with w hw
      have hw' := hval ⟨w, hw⟩
      have hpos' : 0 < (conj (moeb g w)).im := by
        rw [← show ((g • (⟨w, hw⟩ : ℍ) : ℍ) : ℂ) = conj (moeb g w) from hw']
        exact (g • (⟨w, hw⟩ : ℍ)).im_pos
      simp only [extC, Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hw,
        UpperHalfPlane.ofComplex_apply_of_im_pos hpos']
      congr 1
      exact UpperHalfPlane.ext hw'
    have hA' : ContDiffAt ℝ 2 (extC A) (conj (moeb g z)) := by rw [← hval]; exact hA
    have hf' : ContDiffAt ℝ 2 (fun y => extC A (conj y)) (moeb g z) :=
      hA'.comp (moeb g z) Complex.conjCLE.contDiff.contDiffAt
    rw [lapH_eq_of_eventuallyEq (hf'.comp (z : ℂ) hmC) hloc,
      lapE_comp_holo hU (differentiableOn_moeb g) hzU hf', lapE_comp_conj hA', ← hval]
    have key : (((g • z).im : ℝ) : ℂ) ^ 2
        = ((z.im : ℝ) : ℂ) ^ 2 * ((Complex.normSq (deriv (moeb g) z) : ℝ) : ℂ) := by
      exact_mod_cast (normSq_deriv_moeb g z).symm
    rw [key]
    ring

/-- `Δ` commutes with every `g ∈ PGL(2, ℝ)`. -/
theorem lapH_comp_pgl_smul (g : PGL(2, ℝ)) {A : ℍ → ℂ} (z : ℍ)
    (hA : ContDiffAt ℝ 2 (extC A) ((g • z : ℍ) : ℂ)) :
    lapH (fun w => A (g • w)) z = lapH A (g • z) := by
  obtain ⟨M, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
  simp only [UpperHalfPlane.pglMk_smul] at hA ⊢
  exact lapH_comp_smul M z hA

end Qschubert
