import Qschubert.PerioZero2
import Qschubert.ZeroModeFn

/-!
# The pairing of `e^{-αΛ} h` with a periodic function is invariant under horizontal translations

Stage X of the plan for Proposition `ev:mod` (`lean/BLUEPRINT.md`). Let `h, h₀` satisfy `ModData`, let `a'` be a
representative of `e^{-αΛ} h`, and let `E` be measurable with `E(z + n) = E(z)` for integers `n`. Then for every
real `s` (`integral_amp_trans_periodic`), under the integrability hypotheses stated,

`∫_ℍ a'(z + s) E(z) dν = ∫_ℍ a'(z) E(z) dν`.

Proof: `k = h(· + s) - h` is a test function whose periodization vanishes (`transDiff`, `hasSum_transDiff`),
`e^{-αΛ} k = a'(· + s) - a'` almost everywhere (`expCut_J_glU`), and `integral_expCut_mul_periodic` applies.
-/

namespace Qschubert

open MeasureTheory Filter Topology UpperHalfPlane Set Physicslib4.Spectral Physicslib4.Spectral.Unbounded
open scoped MatrixGroups InnerProductSpace ComplexConjugate

local notation "L2H" => Lp ℂ 2 (volume : Measure ℍ)

/-- `h(· + s) - h` as a test function. -/
noncomputable def transDiff (s : ℝ) (h : testFn) : testFn := testCompT (transGL s) h - h

lemma transDiff_coe (s : ℝ) (h : testFn) (z : ℍ) :
    ((transDiff s h : testFn) : ℂ → ℂ) (z : ℂ) = (h : ℂ → ℂ) ((z : ℂ) + s) - (h : ℂ → ℂ) (z : ℂ) := by
  show testComp (transGL s) (h : ℂ → ℂ) (z : ℂ) - (h : ℂ → ℂ) (z : ℂ) = _
  rw [testComp_coe, coe_transGL_smul]

/-- The periodization of `h(· + s) - h` vanishes when that of `h` depends on `Im z` only. -/
lemma hasSum_transDiff {h : ℂ → ℂ} {h₀ : ℝ → ℝ} (hd : ModData h h₀) (s : ℝ) (z : ℍ) :
    HasSum (fun n : ℤ => ((transDiff s ⟨h, hd.test⟩ : testFn) : ℂ → ℂ) ((z : ℂ) + n)) 0 := by
  have h1 := hd.periodized (transGL s • z)
  have h2 := hd.periodized z
  have him : (transGL s • z).im = z.im := by
    have h := congrArg Complex.im (coe_transGL_smul s z)
    simpa [UpperHalfPlane.coe_im] using h
  rw [him] at h1
  have h3 := h1.sub h2
  rw [sub_self] at h3
  refine h3.congr_fun fun n => ?_
  have e : ((z : ℂ) + n) = ((transGL (n : ℝ) • z : ℍ) : ℂ) := by
    rw [coe_transGL_smul, Complex.ofReal_intCast]
  rw [e, transDiff_coe, ← e, coe_transGL_smul]
  show h ((z : ℂ) + n + s) - h ((z : ℂ) + n) = h ((z : ℂ) + s + n) - h ((z : ℂ) + n)
  rw [add_right_comm]

/-- `e^{-αΛ} (h(· + s) - h) = a'(· + s) - a'` almost everywhere. -/
lemma expCut_transDiff_ae {α : ℝ} (hα : 0 < α) {h : ℂ → ℂ} (hh : IsTestFn h) {a' : ℍ → ℂ}
    (ha : a' =ᵐ[volume] ampMod α hα.le hh) (s : ℝ) :
    ⇑((expCut α hα).J (toL2 (transDiff s ⟨h, hh⟩)) : L2H)
      =ᵐ[volume] fun z : ℍ => a' (transGL s • z) - a' z := by
  have e0 : ampMod α hα.le hh = (expCut α hα).J (toL2 ⟨h, hh⟩) := by
    rw [ampMod, expLambda_neg_eq_J hα]
  have e1 : (expCut α hα).J (toL2 (transDiff s ⟨h, hh⟩))
      = glU (transGL s) ((expCut α hα).J (toL2 ⟨h, hh⟩)) - (expCut α hα).J (toL2 ⟨h, hh⟩) := by
    rw [transDiff, map_sub, map_sub, toL2_testCompT, expCut_J_glU]
  rw [e1, ← e0]
  filter_upwards [Lp.coeFn_sub (glU (transGL s) (ampMod α hα.le hh)) (ampMod α hα.le hh),
    glUL_ae (transGL s) (ampMod α hα.le hh), ha, comp_gl_ae (transGL s) ha] with z e2 e3 e4 e5
  rw [e2, Pi.sub_apply, glU_apply, e3, e4, e5]

/-- **Translation invariance of the pairing with a periodic function.** -/
theorem integral_amp_trans_periodic {α : ℝ} (hα : 0 < α) {h : ℂ → ℂ} {h₀ : ℝ → ℝ} (hd : ModData h h₀)
    {a' : ℍ → ℂ} (ha : a' =ᵐ[volume] ampMod α hα.le hd.test) {E : ℍ → ℂ}
    (hEper : ∀ (n : ℤ) (z : ℍ), E (transGL (n : ℝ) • z) = E z)
    (hEL : MemLp (fun z : ℍ => conj ((stripZ 0).indicator E z)) 2 volume) (s : ℝ)
    (hi1 : Integrable fun z : ℍ => a' (transGL s • z) * E z) (hi2 : Integrable fun z : ℍ => a' z * E z) :
    ∫ z : ℍ, a' (transGL s • z) * E z = ∫ z : ℍ, a' z * E z := by
  have hae := expCut_transDiff_ae hα hd.test ha s
  have hae' : (fun z : ℍ => ((expCut α hα).J (toL2 (transDiff s ⟨h, hd.test⟩)) : L2H) z * E z)
      =ᵐ[volume] fun z : ℍ => a' (transGL s • z) * E z - a' z * E z := by
    filter_upwards [hae] with z hz
    rw [hz, sub_mul]
  have hzero := integral_expCut_mul_periodic hα (transDiff s ⟨h, hd.test⟩) (hasSum_transDiff hd s) hEper hEL
    ((hi1.sub hi2).congr hae'.symm)
  rw [integral_congr_ae hae', integral_sub hi1 hi2] at hzero
  exact sub_eq_zero.1 hzero

end Qschubert
