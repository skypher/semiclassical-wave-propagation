import Qschubert.Transport
import Qschubert.TransportCont
import Qschubert.Evolution
import Qschubert.LaplacianSA

/-!
# The dispersive part `V(t)` and the factorization `eq:factor`

Manuscript `paper/paper.tex`, Section "Setting": `e^{-iφ/ħ} U(t) e^{iφ/ħ} = e^{-it/(2ħ)} S(t) V(t)`
(Schubert, Prop. 2.2), `U(t) = e^{iħtΔ/2}` on `L²(ℍ)`. Here `V(t)` is DEFINED from this identity,
`V(t) = e^{it/(2ħ)} S(-t) e^{-iφ/ħ} U(t) e^{iφ/ħ}` (`dispV`), so `eq:factor` holds by construction
(`factor_identity`). That `V` solves `i∂_t V = -(ħ/2)Δ(t)V`, `V(0) = I`, the manuscript's definition,
is the open bridge (V-ODE). Proved here: `V(0) = 1` and `‖V(t)v‖ = ‖v‖`.
-/

namespace Qschubert

open MeasureTheory UpperHalfPlane
open scoped ENNReal UpperHalfPlane

/-- `U(t) = e^{iħtΔ/2}` on `L²(ℍ)`. -/
noncomputable def propH (ħ' t : ℝ) : Lp ℂ 2 (volume : Measure ℍ) →L[ℂ] Lp ℂ 2 (volume : Measure ℍ) :=
  evol negLapH_isSelfAdjoint ħ' t

/-- `V(t) = e^{it/(2ħ)} S(-t) e^{-iφ/ħ} U(t) e^{iφ/ħ}`. -/
noncomputable def dispV (ħ' t : ℝ) (v : Lp ℂ 2 (volume : Measure ℍ)) : Lp ℂ 2 (volume : Measure ℍ) :=
  Complex.exp (Complex.I * ((t / (2 * ħ') : ℝ) : ℂ)) •
    transportLp (-t) (phaseLp (-1) ħ' (propH ħ' t (phaseLp 1 ħ' v)))

/-- **`eq:factor`**: `e^{-iφ/ħ} U(t) e^{iφ/ħ} v = e^{-it/(2ħ)} S(t) V(t) v`. -/
theorem factor_identity (ħ' t : ℝ) (v : Lp ℂ 2 (volume : Measure ℍ)) :
    phaseLp (-1) ħ' (propH ħ' t (phaseLp 1 ħ' v))
      = Complex.exp (-(Complex.I * ((t / (2 * ħ') : ℝ) : ℂ))) • transportLp t (dispV ħ' t v) := by
  rw [dispV, map_smul, transportLp_comp_neg, smul_smul, ← Complex.exp_add, neg_add_cancel,
    Complex.exp_zero, one_smul]

/-- `V(t)` is an isometry. -/
theorem norm_dispV (ħ' t : ℝ) (v : Lp ℂ 2 (volume : Measure ℍ)) : ‖dispV ħ' t v‖ = ‖v‖ := by
  rw [dispV, norm_smul, LinearIsometry.norm_map, LinearIsometry.norm_map, propH, norm_evol,
    LinearIsometry.norm_map, mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I, one_mul]

lemma phaseLp_neg_phaseLp (ħ' : ℝ) (v : Lp ℂ 2 (volume : Measure ℍ)) :
    phaseLp (-1) ħ' (phaseLp 1 ħ' v) = v := by
  refine Lp.ext ?_
  have h1 := unimodMul_ae (measurable_phaseFactor (-1) ħ') (norm_phaseFactor (-1) ħ') (phaseLp 1 ħ' v)
  have h2 := unimodMul_ae (measurable_phaseFactor 1 ħ') (norm_phaseFactor 1 ħ') v
  filter_upwards [h1, h2] with z hz1 hz2
  rw [show (phaseLp (-1) ħ' (phaseLp 1 ħ' v) : ℍ → ℂ) z = _ from hz1,
    show (phaseLp 1 ħ' v : ℍ → ℂ) z = _ from hz2, ← mul_assoc, phaseFactor, phaseFactor,
    ← Complex.exp_add]
  rw [show Complex.I * (((-1) * phaseInf z / ħ' : ℝ) : ℂ) + Complex.I * ((1 * phaseInf z / ħ' : ℝ) : ℂ) = 0 by
    push_cast; ring, Complex.exp_zero, one_mul]

lemma transportLp_zero (v : Lp ℂ 2 (volume : Measure ℍ)) : transportLp 0 v = v := by
  refine Lp.ext ?_
  filter_upwards [transportLp_ae 0 v] with z hz
  rw [hz]
  simp only [transportS]
  rw [show dilate 0 z = z by
    apply UpperHalfPlane.ext; apply Complex.ext <;> simp [dilate]]
  simp

/-- `V(0) = 1`. -/
theorem dispV_zero (ħ' : ℝ) (v : Lp ℂ 2 (volume : Measure ℍ)) : dispV ħ' 0 v = v := by
  rw [dispV, propH, evol_zero]
  rw [show (1 : Lp ℂ 2 (volume : Measure ℍ) →L[ℂ] Lp ℂ 2 (volume : Measure ℍ)) (phaseLp 1 ħ' v)
    = phaseLp 1 ħ' v from rfl, phaseLp_neg_phaseLp, neg_zero, transportLp_zero]
  simp

/-- `t ↦ V(t) v` is continuous. -/
theorem continuous_dispV (ħ' : ℝ) (v : Lp ℂ 2 (volume : Measure ℍ)) : Continuous fun t => dispV ħ' t v := by
  unfold dispV
  have hc : Continuous fun t : ℝ => Complex.exp (Complex.I * ((t / (2 * ħ') : ℝ) : ℂ)) :=
    Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
      (continuous_id.div_const _)))
  have hv : Continuous fun t : ℝ =>
      transportLp (-t) (phaseLp (-1) ħ' (propH ħ' t (phaseLp 1 ħ' v))) := by
    refine continuous_iff_continuousAt.2 fun t => ?_
    refine tendsto_transportLp_apply (continuous_id.neg.tendsto t) ?_
    exact ((phaseLp (-1) ħ').continuous.tendsto _).comp
      ((continuous_evol_apply negLapH_isSelfAdjoint ħ' (phaseLp 1 ħ' v)).tendsto t)
  exact hc.smul hv

end Qschubert
