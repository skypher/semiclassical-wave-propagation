import Qschubert.KLDDFinal
import Qschubert.Boundary
import Qschubert.Corollaries

/-!
# Theorem 1.4R (`thm:dd-appx`), smooth-amplitude version

`thm14R_smooth : Stmt_thm14R_smooth`. Replacing `g` by `g · transH x₀` multiplies the initial state and the approximant by one constant phase (`initState_mul`, `approxSolB_mul`), so the
base point can be moved to `i`, where the word bounds and the weighted propagation are proved. The lift to amplitudes that are not assumed smooth is LIFT-1, which is not part of this file.
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set Physicslib4.Spectral Physicslib4.Spectral.Unbounded UpperHalfPlane
open scoped ENNReal InnerProductSpace MatrixGroups Pointwise

local notation "L2H'" => Lp ℂ 2 (volume : Measure UpperHalfPlane)

lemma fderiv_affine (h : ℂ → ℂ) {l : ℝ} (hl : l ≠ 0) (b z v : ℂ) :
    fderiv ℝ (fun u => h ((l : ℂ) * u + b)) z v = (l : ℂ) * fderiv ℝ h ((l : ℂ) * z + b) v := by
  set e : ℂ ≃L[ℝ] ℂ := ContinuousLinearEquiv.smulLeft (Units.mk0 l hl) with he
  have heu : ∀ u : ℂ, e u = (l : ℂ) * u := fun u => by
    show (Units.mk0 l hl) • u = _
    rw [Units.smul_def, Units.val_mk0, Complex.real_smul]
  set h₂ : ℂ → ℂ := fun v => h (v + b) with hh₂
  have e1 : (fun u => h ((l : ℂ) * u + b)) = h₂ ∘ e := by
    funext u
    simp only [Function.comp_apply, hh₂, heu]
  rw [e1, e.comp_right_fderiv]
  have e2 : fderiv ℝ h₂ (e z) = fderiv ℝ h (e z + b) := fderiv_comp_add_right b
  show (fderiv ℝ h₂ (e z)) (e v) = _
  rw [e2, heu, heu]
  have e3 : (l : ℂ) * v = l • v := (Complex.real_smul).symm
  rw [e3, map_smul, Complex.real_smul]

section affine

variable (x₀ : ℍ)

lemma transH_coe (z : ℍ) : ((transH x₀ • z : ℍ) : ℂ) = (x₀.im : ℂ) * z + x₀.re := by
  rw [coe_specialLinearGroup_apply]
  have h : 0 < √x₀.im := Real.sqrt_pos.2 x₀.im_pos
  have hq : (√x₀.im : ℂ) ≠ 0 := by exact_mod_cast h.ne'
  have hsq : (√x₀.im : ℂ) ^ 2 = (x₀.im : ℂ) := by exact_mod_cast Real.sq_sqrt x₀.im_pos.le
  simp only [transH, Algebra.algebraMap_self, RingHom.id_apply]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  push_cast
  field_simp
  rw [hsq]
  ring

lemma transH_im (z : ℍ) : (transH x₀ • z).im = x₀.im * z.im := by
  have h := congrArg Complex.im (transH_coe x₀ z)
  simpa using h

lemma transH_re (z : ℍ) : (transH x₀ • z).re = x₀.im * z.re + x₀.re := by
  have h := congrArg Complex.re (transH_coe x₀ z)
  simpa using h

lemma extC_comp_transH (f : ℍ → ℂ) (w : ℍ) :
    extC (fun z => f (transH x₀ • z)) =ᶠ[𝓝 (w : ℂ)] fun u => extC f ((x₀.im : ℂ) * u + x₀.re) := by
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds w.im_pos] with u hu
  have hu' : 0 < u.im := hu
  have hT : 0 < ((x₀.im : ℂ) * u + x₀.re).im := by
    simp only [Complex.add_im, Complex.ofReal_im, add_zero, Complex.mul_im, Complex.ofReal_re, zero_mul]
    exact mul_pos x₀.im_pos hu'
  simp only [extC]
  rw [ofComplex_apply_of_im_pos hu', ofComplex_apply_of_im_pos hT]
  congr 1
  apply UpperHalfPlane.ext
  rw [transH_coe]

lemma dZ_comp (f : ℍ → ℂ) (z : ℍ) (v : ℂ) :
    fderiv ℝ (extC fun w => f (transH x₀ • w)) (z : ℂ) v = (x₀.im : ℂ) * fderiv ℝ (extC f) ((transH x₀ • z : ℍ) : ℂ) v := by
  rw [(extC_comp_transH x₀ f z).fderiv_eq, fderiv_affine _ x₀.im_pos.ne', transH_coe]

lemma vecX_comp (f : ℍ → ℂ) : vecX (fun w => f (transH x₀ • w)) = fun z => vecX f (transH x₀ • z) := by
  funext z
  simp only [vecX, dX]
  rw [dZ_comp, transH_im]
  push_cast
  ring

lemma vecY_comp (f : ℍ → ℂ) : vecY (fun w => f (transH x₀ • w)) = fun z => vecY f (transH x₀ • z) := by
  funext z
  simp only [vecY, dY]
  rw [dZ_comp, transH_im]
  push_cast
  ring

lemma lapT_comp (s : ℝ) (f : ℍ → ℂ) (z : ℍ) : lapT s (fun w => f (transH x₀ • w)) z = lapT s f (transH x₀ • z) := by
  simp only [lapT]
  rw [vecX_comp, vecY_comp]
  rw [vecX_comp x₀ (vecX f), vecY_comp x₀ (vecY f)]

lemma dysonP_comp (k : ℕ) (f : ℍ → ℂ) : ∀ t : ℝ, dysonP k t (fun w => f (transH x₀ • w)) = fun z => dysonP k t f (transH x₀ • z) := by
  induction k with
  | zero => intro t; rfl
  | succ k ih =>
    intro t
    funext z
    simp only [dysonP]
    refine intervalIntegral.integral_congr fun s _ => ?_
    show lapT s (dysonP k s fun w => f (transH x₀ • w)) z = lapT s (dysonP k s f) (transH x₀ • z)
    rw [ih s, lapT_comp]

lemma approxAmp_comp (K : ℕ) (ħ t : ℝ) (f : ℍ → ℂ) :
    approxAmp K ħ t (fun w => f (transH x₀ • w)) = fun z => approxAmp K ħ t f (transH x₀ • z) := by
  funext z
  simp only [approxAmp]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show dysonP k t (fun w => f (transH x₀ • w)) = fun z => dysonP k t f (transH x₀ • z) from dysonP_comp x₀ k f t]

lemma dilate_comm (t : ℝ) (z : ℍ) : transH x₀ • dilate t z = dilate t (transH x₀ • z) := by
  apply UpperHalfPlane.ext
  apply Complex.ext
  · show (transH x₀ • dilate t z).re = (dilate t (transH x₀ • z)).re
    rw [transH_re, dilate_re, dilate_re, transH_re]
  · show (transH x₀ • dilate t z).im = (dilate t (transH x₀ • z)).im
    rw [transH_im, dilate_im, dilate_im, transH_im]
    ring

lemma transportS_comp (t : ℝ) (h : ℍ → ℂ) (z : ℍ) :
    transportS t (fun w => h (transH x₀ • w)) z = transportS t h (transH x₀ • z) := by
  simp only [transportS]
  rw [dilate_comm]

lemma phaseInf_comp (z : ℍ) : phaseInf z = phaseInf (transH x₀ • z) + Real.log x₀.im := by
  simp only [phaseInf]
  rw [transH_im, Real.log_mul x₀.im_pos.ne' z.im_pos.ne']
  ring

/-- The constant phase. -/
noncomputable def cstB (ħ : ℝ) : ℂ := Complex.exp (Complex.I * (Real.log x₀.im : ℂ) / (ħ : ℂ))

lemma norm_cstB (ħ : ℝ) : ‖cstB x₀ ħ‖ = 1 := by
  unfold cstB
  have e : Complex.I * (Real.log x₀.im : ℂ) / (ħ : ℂ) = ((Real.log x₀.im / ħ : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [e, Complex.norm_exp_ofReal_mul_I]

lemma cstB_ne (ħ : ℝ) : cstB x₀ ħ ≠ 0 := Complex.exp_ne_zero _

lemma approxSol_comp (K : ℕ) (ħ t : ℝ) (f : ℍ → ℂ) (z : ℍ) :
    approxSol K ħ t (fun w => f (transH x₀ • w)) z = cstB x₀ ħ * approxSol K ħ t f (transH x₀ • z) := by
  simp only [approxSol]
  rw [approxAmp_comp, transportS_comp, phaseInf_comp x₀ z]
  have e : Complex.exp (Complex.I * ((phaseInf (transH x₀ • z) + Real.log x₀.im : ℝ) : ℂ) / (ħ : ℂ))
      = Complex.exp (Complex.I * (phaseInf (transH x₀ • z) : ℂ) / (ħ : ℂ)) * cstB x₀ ħ := by
    unfold cstB
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [e]
  ring

lemma approxSolB_mul (g : SL(2, ℝ)) (K : ℕ) (ħ t : ℝ) (a : ℍ → ℂ) :
    approxSolB (g * transH x₀) K ħ t a = fun z => cstB x₀ ħ * approxSolB g K ħ t a z := by
  funext z
  simp only [approxSolB]
  have e1 : (fun w => a ((g * transH x₀) • w)) = fun w => (fun v => a (g • v)) (transH x₀ • w) := by
    funext w; rw [mul_smul]
  have e2 : (g * transH x₀)⁻¹ • z = (transH x₀)⁻¹ • g⁻¹ • z := by rw [mul_inv_rev, mul_smul]
  have e3 := approxSol_comp x₀ K ħ t (fun v => a (g • v)) ((transH x₀)⁻¹ • g⁻¹ • z)
  rw [e1, e2, e3, smul_inv_smul]

lemma initState_mul (g : SL(2, ℝ)) (ħ : ℝ) (a : ℍ → ℂ) :
    initState (g * transH x₀) ħ a = fun z => cstB x₀ ħ * initState g ħ a z := by
  funext z
  simp only [initState, phaseB]
  have e2 : (g * transH x₀)⁻¹ • z = (transH x₀)⁻¹ • g⁻¹ • z := by rw [mul_inv_rev, mul_smul]
  have e3 := phaseInf_comp x₀ ((transH x₀)⁻¹ • g⁻¹ • z)
  rw [smul_inv_smul] at e3
  rw [e2]
  rw [e3]
  unfold cstB
  have e5 : Complex.exp (Complex.I * ((phaseInf (g⁻¹ • z) + Real.log x₀.im : ℝ) : ℂ) / (ħ : ℂ))
      = Complex.exp (Complex.I * (phaseInf (g⁻¹ • z) : ℂ) / (ħ : ℂ)) * Complex.exp (Complex.I * (Real.log x₀.im : ℂ) / (ħ : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [e5]
  ring

end affine

section phase

variable {Γ : Subgroup PGL(2, ℝ)} [ProperlyDiscontinuousSMul Γ ℍ]

lemma perio_const (c : ℂ) (u : ℍ → ℂ) (x : Surf Γ) : perio Γ (fun z => c * u z) x = c * perio Γ u x := by
  induction x using Quotient.inductionOn with | _ z
  show ∑' γ : Γ, c * u (γ • z) = c * ∑' γ : Γ, u (γ • z)
  exact tsum_mul_left

lemma perioConv_const {c : ℂ} (hc : c ≠ 0) {u : ℍ → ℂ} (h : PerioConv Γ fun z => c * u z) : PerioConv Γ u := by
  refine ⟨?_, ?_⟩
  · filter_upwards [h.1] with z hz
    have hn : ‖c‖ ≠ 0 := norm_ne_zero_iff.2 hc
    have e : (fun γ : Γ => ‖u (γ • z)‖) = fun γ : Γ => ‖c‖⁻¹ * ‖c * u (γ • z)‖ := by
      funext γ
      rw [norm_mul, inv_mul_cancel_left₀ hn]
    rw [e]
    exact hz.mul_left _
  · have e : perio Γ u = fun x => c⁻¹ * perio Γ (fun z => c * u z) x := by
      funext x
      rw [perio_const, inv_mul_cancel_left₀ hc]
    rw [e]
    exact h.2.const_mul _

lemma toLp_const {c : ℂ} {u : ℍ → ℂ} (h' : PerioConv Γ fun z => c * u z) (h : PerioConv Γ u) :
    h'.2.toLp _ = c • h.2.toLp _ := by
  refine Lp.ext ?_
  filter_upwards [h'.2.coeFn_toLp, h.2.coeFn_toLp, Lp.coeFn_smul c (h.2.toLp _)] with x e1 e2 e3
  rw [e1, e3, Pi.smul_apply, e2, perio_const, smul_eq_mul]

lemma errNormM_smul {c : ℂ} (hc : ‖c‖ = 1) (N : ℕ) (x : Lp ℂ 2 (surfMeasure Γ)) : errNormM Γ N (c • x) = errNormM Γ N x := by
  have hc0 : c ≠ 0 := by
    intro h; rw [h, norm_zero] at hc; exact zero_ne_one hc
  unfold errNormM
  by_cases h : x ∈ (lapPowM Γ N).domain
  · have h' : c • x ∈ (lapPowM Γ N).domain := Submodule.smul_mem _ c h
    rw [dif_pos h, dif_pos h']
    have e : (⟨c • x, h'⟩ : (lapPowM Γ N).domain) = c • ⟨x, h⟩ := rfl
    rw [e, LinearPMap.map_smul, enorm_smul]
    have : ‖c‖ₑ = 1 := by rw [← ofReal_norm, hc, ENNReal.ofReal_one]
    rw [this, one_mul]
  · have h' : c • x ∉ (lapPowM Γ N).domain := fun hm => h (by
      have := Submodule.smul_mem _ c⁻¹ hm
      rwa [smul_smul, inv_mul_cancel₀ hc0, one_smul] at this)
    rw [dif_neg h, dif_neg h']

lemma approxErr_congr {N : ℕ} {ħ t : ℝ} {v v' w w' : ℍ → ℂ} (hvv : v = v') (hww : w = w') (hv : PerioConv Γ v) (hw : PerioConv Γ w)
    (hv' : PerioConv Γ v') (hw' : PerioConv Γ w') : approxErr Γ N ħ t hv hw = approxErr Γ N ħ t hv' hw' := by
  subst hvv hww
  rfl

lemma approxErr_const {c : ℂ} (hc : ‖c‖ = 1) {N : ℕ} {ħ t : ℝ} {v w : ℍ → ℂ} (hv : PerioConv Γ v) (hw : PerioConv Γ w)
    (hv' : PerioConv Γ fun z => c * v z) (hw' : PerioConv Γ fun z => c * w z) : approxErr Γ N ħ t hv' hw' = approxErr Γ N ħ t hv hw := by
  unfold approxErr
  have e1 : hv'.2.toLp _ = c • hv.2.toLp _ := toLp_const hv' hv
  have e2 : hw'.2.toLp _ = c • hw.2.toLp _ := toLp_const hw' hw
  have e3 : (⟨hv'.2.toLp _, by rw [propM_domain_eq_top]; trivial⟩ : (propM Γ ħ t).domain) = c • ⟨hv.2.toLp _, by rw [propM_domain_eq_top]; trivial⟩ :=
    Subtype.ext e1
  rw [e3, LinearPMap.map_smul, e2, ← smul_sub, errNormM_smul hc]

end phase

lemma smoothH_comp (g : SL(2, ℝ)) {a : ℍ → ℂ} (ha : SmoothH a) : SmoothH fun w => a (g • w) := fun z => by
  set G : GL (Fin 2) ℝ := (g : GL (Fin 2) ℝ) with hG
  have hop : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
  have hloc : extC (fun w => a (g • w)) =ᶠ[𝓝 (z : ℂ)] fun y => extC a (UpperHalfPlane.σ G (moeb G y)) := by
    filter_upwards [hop.mem_nhds z.im_pos] with y hy
    have hy' : 0 < y.im := hy
    simp only [extC]
    rw [ofComplex_apply_of_im_pos hy']
    have e : (UpperHalfPlane.σ G (moeb G y)) = ((G • (⟨y, hy'⟩ : ℍ) : ℍ) : ℂ) := rfl
    rw [e, ofComplex_apply]
    rfl
  have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (extC a) (UpperHalfPlane.σ G (moeb G (z : ℂ))) := ha (G • z)
  have hin : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => UpperHalfPlane.σ G (moeb G y)) (z : ℂ) :=
    ContDiffAt.comp (g := fun w => UpperHalfPlane.σ G w) (f := moeb G) (z : ℂ) (contDiff_σ G).contDiffAt (contDiffAt_moeb G z)
  have hd : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => extC a (UpperHalfPlane.σ G (moeb G y))) (z : ℂ) :=
    ContDiffAt.comp (g := extC a) (f := fun y => UpperHalfPlane.σ G (moeb G y)) (z : ℂ) h1 hin
  exact hd.congr_of_eventuallyEq hloc

lemma poincareSup_conj_move (p : PGL(2, ℝ)) (Γ : Subgroup PGL(2, ℝ)) (x₀ : ℍ) (s : ℝ) :
    poincareSup (conjS p Γ) (p • x₀) s = poincareSup Γ x₀ s := by
  unfold poincareSup
  rw [← (MulAction.toPerm p : Equiv.Perm ℍ).iSup_comp]
  refine iSup_congr fun w => ?_
  show ∑' γ' : conjS p Γ, ENNReal.ofReal (Real.exp (-(s * dist (p • x₀) (γ' • p • w)))) = _
  rw [← (conjE p Γ).toEquiv.tsum_eq (fun γ' : conjS p Γ => ENNReal.ofReal (Real.exp (-(s * dist (p • x₀) (γ' • p • w)))))]
  refine tsum_congr fun γ => ?_
  show ENNReal.ofReal (Real.exp (-(s * dist (p • x₀) (conjE p Γ γ • p • w)))) = _
  rw [conjE_smul, dist_smul]

lemma ddBound_nonneg {C α ħ t : ℝ} (K N : ℕ) (hC : 0 ≤ C) (hα : 0 < α) (hħ : 0 < ħ) (ht : 0 ≤ t) : 0 ≤ ddBound C α ħ t K N := by
  unfold ddBound
  positivity

set_option maxHeartbeats 8000000 in
/-- **Theorem 1.4R (`thm:dd-appx`), smooth-amplitude version.** -/
theorem thm14R_smooth : Stmt_thm14R_smooth := by
  intro Γ _ _hOP x₀ β κ α₀ hβ hκ hα₀ hα₀1
  haveI : Countable Γ := countable_of_properlyDiscontinuous Γ
  have hτ : (1 : ℝ) < Real.pi / 2 := by linarith [Real.pi_gt_three]
  obtain ⟨C₁, hC, hF'⟩ := lem_fc hτ
  have hβ0 : 0 ≤ β := by linarith
  obtain ⟨B, hB0, hB⟩ := fdb β
  obtain ⟨K₁, δ, hK₁, hδ, hcore⟩ := dd_core hβ hκ hβ0 hB0 hB hC hF'
  set γ : ℝ := (2 * β + 1) / 4 with hγd
  have hγ12 : 1 / 2 < γ := by rw [hγd]; linarith
  have hγβ : γ ≤ β := by rw [hγd]; linarith
  set S₀ : ℝ := Real.sqrt (ENNReal.ofReal (2 ^ γ) ^ 2 * poincareSup Γ x₀ (2 * γ)).toReal with hS₀
  have hS₀0 : 0 ≤ S₀ := Real.sqrt_nonneg _
  set Cc : ℝ := ((4 * mM C₁) ^ 2 * C4 (K3c 1 C₁) * 128) * (1 + 4 * C4 (K3c 1 C₁) ^ 2 * (S₀ * K₁)) with hCc
  have hM1 : 1 ≤ mM C₁ := one_le_mM C₁
  have hC₄1 : 1 ≤ C4 (K3c 1 C₁) := by
    unfold C4
    have := one_le_K3c 1 C₁
    nlinarith [sq_nonneg (K3c 1 C₁)]
  have hCc0 : 0 < Cc := by
    rw [hCc]
    have h1 : 0 < mM C₁ := by linarith
    have h2 : 0 < C4 (K3c 1 C₁) := by linarith
    positivity
  refine ⟨Cc, δ, hCc0, hδ, ?_⟩
  intro ħ α t K N g a hħ hħ1 hα hαα₀ hk hgx ht htδ hsm hfin
  have hα1 : α ≤ 1 := hαα₀.trans (hα₀1.le.trans (min_le_left _ _))
  set G : SL(2, ℝ) := g * transH x₀ with hG
  have hGI : G • UpperHalfPlane.I = x₀ := by rw [hG, mul_smul, transH_smul_I, hgx]
  by_cases hw : MemLp (fun z => ((coshD x₀ z ^ β : ℝ) : ℂ) * a z) 2 (volume : Measure ℍ)
  swap
  · exfalso
    simp [swNormX, hw] at hfin
  by_cases h : hw.toLp _ ∈ (expLambda α).domain
  swap
  · exfalso
    simp [swNormX, hw, h] at hfin
  have hSW : swNormX x₀ α β a = ‖expLambda α ⟨hw.toLp _, h⟩‖ₑ := by simp only [swNormX, dif_pos hw, dif_pos h]
  set p : PGL(2, ℝ) := Matrix.SpecialLinearGroup.toPGL G with hp
  obtain ⟨hFd, hFn⟩ := expLambda_iso p h
  set Fx : L2H' := hw.toLp _ with hFx
  set F : L2H' := isoU p Fx with hFdef
  set A : L2H' := mulW hβ0 hB [] F with hA
  have hFae : ⇑F =ᵐ[volume] fun z => ((coshD UpperHalfPlane.I z ^ β : ℝ) : ℂ) * a (G • z) := by
    have h1 := (measurePreserving_smul p (volume : Measure ℍ)).quasiMeasurePreserving.ae_eq_comp hw.coeFn_toLp
    filter_upwards [isoU_ae p Fx, h1] with z e1 e2
    rw [e1]
    have e2' : (Fx : L2H') (p • z) = ((coshD x₀ (p • z) ^ β : ℝ) : ℂ) * a (p • z) := e2
    have hpz : p • z = G • z := toPGL_smul G z
    rw [e2', hpz]
    have e3 : coshD x₀ (G • z) = coshD UpperHalfPlane.I z := by
      unfold coshD
      rw [← hGI, dist_smul]
    rw [e3]
  have hAae : ⇑A =ᵐ[volume] fun w => a (G • w) := by
    have h1 : ⇑A =ᵐ[volume] fun z => ((hF (z : ℂ) ^ β : ℝ) : ℂ) * F z := coe_mulCL (adm_word hβ0 hB []).sb F
    filter_upwards [h1, hFae] with z e1 e2
    rw [e1, e2, ← mul_assoc, ← Complex.ofReal_mul]
    have hc : 0 < coshD UpperHalfPlane.I z := Real.cosh_pos _
    have e3 : hF (z : ℂ) ^ β * coshD UpperHalfPlane.I z ^ β = 1 := by
      rw [hF_eq_inv_coshD, Real.inv_rpow hc.le, inv_mul_cancel₀ (Real.rpow_pos_of_pos hc β).ne']
    rw [e3, Complex.ofReal_one, one_mul]
  have hAW : AllWords A := fun S => (lem_sc hF' hC hβ0 hB S hα hα1 hFd).1
  have hsG : SmoothH fun w => a (G • w) := smoothH_comp G hsm
  set Γ' := conjS (Matrix.SpecialLinearGroup.toPGL G⁻¹) Γ with hΓ'
  set W : SurfW Γ' := surfW_cosh Γ' UpperHalfPlane.I hγ12 with hW
  set Wβ : SurfW Γ' := surfW_cosh Γ' UpperHalfPlane.I hβ with hWβ
  have hWω : ∀ z, W.ω z = omG γ z := fun z => rfl
  have hWβω : ∀ z, Wβ.ω z = omG β z := fun z => rfl
  have hGa' : ∀ w : List Bool, ∃ G' : L2H', W.Chart G' (wordAct w A) := fun w => by
    obtain ⟨-, Gb, hGb, -⟩ := lem_sc hF' hC hβ0 hB w hα hα1 hFd
    have hGb' : ⇑Gb =ᵐ[volume] fun z => ((omG β z : ℝ) : ℂ) * wordAct w A z := by
      filter_upwards [hGb] with z hz
      rw [hz, hF_neg_rpow]
    obtain ⟨G', hG', -⟩ := chart_down hβ0 hγβ hGb'
    exact ⟨G', hG'⟩
  choose Ga hGa using hGa'
  obtain ⟨hvG, hwG⟩ := perioConv_general (W := W) hsG hAae hAW hGa K ħ t
  have hE := approxErr_general (W := W) hsG hAae hAW hGa hħ.ne' K N t hvG hwG
  have hcore2 := hcore Γ' W Wβ hWω hWβω ħ α t K N F hFd hħ hħ1 hα hα1 hk ht htδ
  have hWC : W.C = ENNReal.ofReal (2 ^ γ) ^ 2 * poincareSup Γ x₀ (2 * γ) := by
    have e : Matrix.SpecialLinearGroup.toPGL G⁻¹ • x₀ = UpperHalfPlane.I := by
      rw [toPGL_smul, ← hGI, inv_smul_smul]
    show ENNReal.ofReal (2 ^ γ) ^ 2 * poincareSup Γ' UpperHalfPlane.I (2 * γ) = _
    rw [hΓ', ← e, poincareSup_conj_move]
  rw [hWC, ← hS₀, ← hCc] at hcore2
  have hc1 := norm_cstB x₀ ħ
  have hc0 := cstB_ne x₀ ħ
  have ei := initState_mul x₀ g ħ a
  have ea := approxSolB_mul x₀ g K ħ t a
  have hvG' : PerioConv Γ fun z => cstB x₀ ħ * initState g ħ a z := ei ▸ hvG
  have hwG' : PerioConv Γ fun z => cstB x₀ ħ * approxSolB g K ħ t a z := ea ▸ hwG
  have hv : PerioConv Γ (initState g ħ a) := perioConv_const hc0 hvG'
  have hw2 : PerioConv Γ (approxSolB g K ħ t a) := perioConv_const hc0 hwG'
  refine ⟨hv, hw2, ?_⟩
  rw [← approxErr_const hc1 hv hw2 hvG' hwG', ← approxErr_congr ei ea hvG hwG hvG' hwG', hE, hSW]
  rw [← ofReal_norm, ← ofReal_norm, ← hFn, ← ENNReal.ofReal_mul (ddBound_nonneg K N hCc0.le hα hħ ht)]
  exact ENNReal.ofReal_le_ofReal hcore2

/-- **Corollary 1.5R (`cor:dd15-appx`), smooth-amplitude version.** -/
theorem cor15R_smooth : Stmt_cor15R_smooth := cor15R_of_thm14R thm14R_smooth

end Qschubert
