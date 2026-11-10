import Qschubert.KLPartII

/-!
# Quantitative bounds along the weighted path

`‖G(r)‖` from Proposition WS at `k = 0`, then `‖H(s)‖` and the integrand `x(s)` of the Duhamel formula on `M`.
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set Physicslib4.Spectral Physicslib4.Spectral.Unbounded
open scoped ENNReal InnerProductSpace UpperHalfPlane MatrixGroups Pointwise

local notation "L2H'" => Lp ℂ 2 (volume : Measure UpperHalfPlane)

section

variable {Γ : Subgroup PGL(2, ℝ)} [Countable Γ] [ProperlyDiscontinuousSMul Γ ℍ] (W : SurfW Γ) (P : MollProfile) {ε : ℝ} (hε : 0 < ε)
  {γ : ℝ} {hγ : 0 ≤ γ} (hWω : ∀ z, W.ω z = omG γ z) (O : WOps (P.cutoffEps hε) hγ) (hb s₁ : ℝ)
  {b' : negLapH.domain} {G₀ GX₀ GY₀ GXX₀ GYY₀ : L2H'} (hI : W.SurfIn b' G₀ GX₀ GY₀ GXX₀ GYY₀)

include hγ hWω in
lemma lint_chart {G v : L2H'} (c : W.Chart G v) : ∫⁻ z : ℍ, (ENNReal.ofReal (coshD UpperHalfPlane.I z ^ γ) * ‖v z‖ₑ) ^ 2 = ENNReal.ofReal (‖G‖ ^ 2) := by
  rw [← lintegral_enorm_sq_eq]
  refine lintegral_congr_ae ?_
  have c' : ⇑G =ᵐ[volume] _ := c
  filter_upwards [c'] with z hz
  have hp := omG_pos hγ z
  rw [hz, enorm_mul, hWω, ← ofReal_norm_eq_enorm ((omG γ z : ℝ) : ℂ), Complex.norm_real, Real.norm_of_nonneg hp.le]
  rfl

include hWω hI in
/-- The propagation bound along the path. -/
theorem norm_pathG_le {Gc : ℝ}
    (hws : ∀ {ε : ℝ} (hε : 0 < ε), ε ≤ 1 → ∀ (hb : ℝ) {s₀ s₁ : ℝ}, 0 ≤ s₀ → 0 ≤ s₁ → ∀ a : L2H',
      ∫⁻ z : ℍ, (ENNReal.ofReal (coshD UpperHalfPlane.I z ^ γ)
          * ‖((P.cutoffEps hε).flowEps hb s₁ (ContinuousLinearMap.adjoint ((P.cutoffEps hε).flowEps hb s₀) a) : L2H') z‖ₑ) ^ 2
        ≤ ENNReal.ofReal (Real.exp (|hb| * (ε⁻¹ * Gc) * |s₁ - s₀|))
          * ∫⁻ z : ℍ, (ENNReal.ofReal (coshD UpperHalfPlane.I z ^ γ) * ‖a z‖ₑ) ^ 2)
    (hε1 : ε ≤ 1) (hs₁ : 0 ≤ s₁) {r : ℝ} (hr : 0 ≤ r) :
    ‖O.pathG hb s₁ G₀ r‖ ≤ Real.exp (|hb| * (ε⁻¹ * Gc) * |r - s₁| / 2) * ‖G₀‖ := by
  have h := hws hε hε1 hb hs₁ hr (b' : L2H')
  have hS := pathD_surfIn W P hε hWω O hb s₁ hI r
  rw [← pathD_flow W P hε hWω O hb s₁ hI r] at h
  rw [lint_chart W hWω (hγ := hγ) hS.cG, lint_chart W hWω (hγ := hγ) hI.cG, ← ENNReal.ofReal_mul (Real.exp_pos _).le] at h
  have h2 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h
  refine le_exp_of_sq_le (norm_nonneg _) (norm_nonneg _) ?_
  have e : 2 * (|hb| * (ε⁻¹ * Gc) * |r - s₁| / 2) = |hb| * (ε⁻¹ * Gc) * |r - s₁| := by ring
  rwa [e]

end

section ops

variable {χ : Cutoff} {γ : ℝ} {hγ : 0 ≤ γ} (O : WOps χ hγ) (hb s₁ : ℝ) (G₀ : L2H')

lemma norm_lapW_le {s : ℝ} (hs : 0 ≤ s) (F : L2H') : ‖O.lapW s F‖ ≤ 2 * O.Qc * ‖F‖ := by
  have he : ‖((Real.exp (-2 * s) : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.2 (by linarith)
  have h1 : ‖O.XXw F‖ ≤ O.Qc * ‖F‖ := (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right (norm_wConj_le hγ O.hc O.hXX) (norm_nonneg _))
  have h2 : ‖O.YYw F‖ ≤ O.Qc * ‖F‖ := (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right (norm_wConj_le hγ O.hc O.hYY) (norm_nonneg _))
  show ‖((Real.exp (-2 * s) : ℝ) : ℂ) • O.XXw F + O.YYw F‖ ≤ _
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul]
  have hnn := mul_nonneg O.hc (norm_nonneg F)
  have h3 : ‖((Real.exp (-2 * s) : ℝ) : ℂ)‖ * ‖O.XXw F‖ ≤ 1 * (O.Qc * ‖F‖) := mul_le_mul he h1 (norm_nonneg _) zero_le_one
  linarith

lemma norm_coef (hb : ℝ) : ‖Complex.I * (hb : ℂ) / 2‖ = |hb| / 2 := by simp

lemma norm_genW_le {s : ℝ} (hs : 0 ≤ s) (F : L2H') : ‖O.genW hb s F‖ ≤ |hb| / 2 * (O.Qa * (2 * O.Qc * ‖F‖)) := by
  show ‖(Complex.I * (hb : ℂ) / 2) • O.Jw (O.lapW s F)‖ ≤ _
  rw [norm_smul, norm_coef]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
  exact mul_le_mul (norm_wConj_le hγ O.ha O.hJ) (norm_lapW_le O hs F) (norm_nonneg _) O.ha

/-- The bound for `H(s)`. -/
lemma norm_pathH_le {s Gm : ℝ} (hs₁ : 0 ≤ s₁) (hs : 0 ≤ s) (hG : ∀ r ∈ uIcc s₁ s, ‖O.pathG hb s₁ G₀ r‖ ≤ Gm) :
    ‖O.pathH hb s₁ G₀ s‖ ≤ |hb| / 2 * (2 * O.Qc * Gm) * |s - s₁| := by
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun r hr => ?_
  have hr' : r ∈ uIcc s₁ s := uIoc_subset_uIcc hr
  have hr0 : 0 ≤ r := by
    rcases le_total s₁ s with h | h
    · rw [uIcc_of_le h] at hr'; linarith [hr'.1]
    · rw [uIcc_of_ge h] at hr'; linarith [hr'.1]
  show ‖(Complex.I * (hb : ℂ) / 2) • O.lapW r (O.pathG hb s₁ G₀ r)‖ ≤ _
  rw [norm_smul, norm_coef]
  refine mul_le_mul_of_nonneg_left ((norm_lapW_le O hr0 _).trans ?_) (by positivity)
  have hQ : 0 ≤ 2 * O.Qc := by have := O.hc; positivity
  exact mul_le_mul_of_nonneg_left (hG r hr') hQ

/-- The bound for the integrand. -/
lemma norm_xInt_le {s Gm Hm : ℝ} (hs : 0 ≤ s) (hG : ‖O.pathG hb s₁ G₀ s‖ ≤ Gm) (hH : ‖O.pathH hb s₁ G₀ s‖ ≤ Hm) {GY₀ GXX₀ GYY₀ : L2H'} :
    ‖O.xInt hb s₁ G₀ GY₀ GXX₀ GYY₀ s‖ ≤ |hb| / 2 * (O.Qa * (2 * O.Qc * Gm) + (‖GXX₀‖ + ‖GYY₀‖ + ‖GY₀‖) + (2 * O.Qc + 2 * O.Qb) * Hm) := by
  have he : ‖((Real.exp (-2 * s) : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.2 (by linarith)
  set H := O.pathH hb s₁ G₀ s with hHd
  have hHm0 : 0 ≤ Hm := (norm_nonneg _).trans hH
  have n1 : ‖O.XXw H‖ ≤ O.Qc * Hm := (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul (norm_wConj_le hγ O.hc O.hXX) hH (norm_nonneg _) O.hc)
  have n2 : ‖O.YYw H‖ ≤ O.Qc * Hm := (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul (norm_wConj_le hγ O.hc O.hYY) hH (norm_nonneg _) O.hc)
  have n3 : ‖O.Byw H‖ ≤ O.Qb * Hm := (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul (norm_wConj_le hγ O.hb O.hBy) hH (norm_nonneg _) O.hb)
  have hgen : ‖O.pathGd hb s₁ G₀ s‖ ≤ |hb| / 2 * (O.Qa * (2 * O.Qc * Gm)) := by
    refine (norm_genW_le O hb hs _).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hG ?_) O.ha
    have := O.hc; positivity
  have hdel : ‖SurfW.gDel s (GY₀ + O.Byw H) (GXX₀ + O.XXw H) (GYY₀ + O.YYw H + O.Byw H)‖
      ≤ ‖GXX₀‖ + ‖GYY₀‖ + ‖GY₀‖ + (2 * O.Qc + 2 * O.Qb) * Hm := by
    unfold SurfW.gDel
    have a1 : ‖((Real.exp (-2 * s) : ℝ) : ℂ) • (GXX₀ + O.XXw H)‖ ≤ ‖GXX₀‖ + O.Qc * Hm := by
      rw [norm_smul]
      refine (mul_le_of_le_one_left (norm_nonneg _) he).trans ((norm_add_le _ _).trans ?_)
      linarith
    have a2 : ‖GYY₀ + O.YYw H + O.Byw H‖ ≤ ‖GYY₀‖ + O.Qc * Hm + O.Qb * Hm :=
      (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add le_rfl n2)) n3)
    have a3 : ‖GY₀ + O.Byw H‖ ≤ ‖GY₀‖ + O.Qb * Hm := (norm_add_le _ _).trans (add_le_add le_rfl n3)
    refine (norm_sub_le _ _).trans ((add_le_add ((norm_add_le _ _).trans (add_le_add a1 a2)) a3).trans (le_of_eq ?_))
    ring
  show ‖O.pathGd hb s₁ G₀ s - (Complex.I * (hb : ℂ) / 2) • SurfW.gDel s (GY₀ + O.Byw H) (GXX₀ + O.XXw H) (GYY₀ + O.YYw H + O.Byw H)‖ ≤ _
  refine (norm_sub_le _ _).trans ?_
  rw [norm_smul, norm_coef]
  have hh : 0 ≤ |hb| / 2 := by positivity
  calc _ ≤ |hb| / 2 * (O.Qa * (2 * O.Qc * Gm)) + |hb| / 2 * (‖GXX₀‖ + ‖GYY₀‖ + ‖GY₀‖ + (2 * O.Qc + 2 * O.Qb) * Hm) :=
        add_le_add hgen (mul_le_mul_of_nonneg_left hdel hh)
    _ = _ := by ring

end ops

end Qschubert
