import Qschubert.KLUnw

/-!
# Part (II) of the proof of Theorem 1.4R

The surface bound `‖𝒱_s x‖ ≤ √C e^{γ|s|} ‖x‖` for the weight `X₀^γ`, the Hölder split, and the bounds for the integrand in the Duhamel formula on `M`.
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set Physicslib4.Spectral Physicslib4.Spectral.Unbounded
open scoped ENNReal InnerProductSpace UpperHalfPlane MatrixGroups Pointwise

local notation "L2H'" => Lp ℂ 2 (volume : Measure UpperHalfPlane)

section surf

variable {Γ : Subgroup PGL(2, ℝ)} [Countable Γ] [ProperlyDiscontinuousSMul Γ ℍ] (W : SurfW Γ)

lemma norm_TW_le' (hb s : ℝ) {D : ℝ} (hD : ∀ z, |W.mS s z| ≤ D) (x : L2H') : ‖W.TW hb s x‖ ≤ D * ‖x‖ := by
  rw [SurfW.TW_apply]
  refine (bddMul_bound (W.measurable_mS s) (W.mS_bdd s) hD _).trans ?_
  rw [LinearIsometry.norm_map, LinearIsometry.norm_map]

variable {γ : ℝ} (hγ : 0 ≤ γ) (hWω : ∀ z, W.ω z = omG γ z)
include hγ hWω

lemma mS_le (s : ℝ) (z : ℍ) : |W.mS s z| ≤ Real.exp (γ * |s|) := by
  have hz := omG_pos hγ z
  have hd := omG_pos hγ (dilate s z)
  rw [SurfW.mS, hWω, hWω, abs_of_pos (div_pos hz hd), div_le_iff₀ hd]
  have h1 : coshD UpperHalfPlane.I z ≤ coshD UpperHalfPlane.I (dilate s z) * Real.exp |s| := by
    refine cosh_le_cosh_mul_exp dist_nonneg dist_nonneg (abs_nonneg s) ?_
    have := dist_triangle UpperHalfPlane.I (dilate s z) z
    rw [dist_comm (dilate s z) z, dist_dilate] at this
    exact this
  have h0 : 0 ≤ coshD UpperHalfPlane.I z := (Real.cosh_pos _).le
  have h2 : coshD UpperHalfPlane.I z ^ γ ≤ (coshD UpperHalfPlane.I (dilate s z) * Real.exp |s|) ^ γ := Real.rpow_le_rpow h0 h1 hγ
  have h00 : 0 ≤ coshD UpperHalfPlane.I (dilate s z) := (Real.cosh_pos _).le
  rw [Real.mul_rpow h00 (Real.exp_pos _).le, ← Real.exp_mul] at h2
  show coshD UpperHalfPlane.I z ^ γ ≤ _
  have e : |s| * γ = γ * |s| := mul_comm _ _
  rw [e] at h2
  exact h2.trans_eq (mul_comm _ _)

/-- **`‖𝒱_s x‖ ≤ √C e^{γ|s|} ‖x‖`.** -/
theorem norm_surfV_le (hb s : ℝ) (x : L2H') : ‖W.surfV hb s x‖ ≤ Real.sqrt W.C.toReal * (Real.exp (γ * |s|) * ‖x‖) := by
  rw [SurfW.norm_surfV]
  show ‖W.perioW (W.TW hb s x)‖ ≤ _
  refine (W.perioW.le_of_opNorm_le (LinearMap.mkContinuous_norm_le _ (Real.sqrt_nonneg _) _) _).trans ?_
  exact mul_le_mul_of_nonneg_left (norm_TW_le' W hb s (mS_le W hγ hWω s) x) (Real.sqrt_nonneg _)

end surf

/-- **Hölder for charts.** -/
theorem chart_holder {γ β θ : ℝ} (hβ : 0 ≤ β) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hγ : γ = θ * β) {xγ xβ d : L2H'}
    (cγ : ⇑xγ =ᵐ[volume] fun z => ((omG γ z : ℝ) : ℂ) * d z) (cβ : ⇑xβ =ᵐ[volume] fun z => ((omG β z : ℝ) : ℂ) * d z) :
    ‖xγ‖ ≤ ‖xβ‖ ^ θ * ‖d‖ ^ (1 - θ) := by
  have hp : (1 / θ : ℝ).HolderConjugate (1 / (1 - θ)) := by
    refine Real.holderConjugate_iff.2 ⟨?_, ?_⟩
    · rw [lt_div_iff₀ hθ0]; linarith
    · have h1 : θ ≠ 0 := hθ0.ne'
      have h2 : 1 - θ ≠ 0 := by linarith
      field_simp
      ring
  set A : ℍ → ℝ≥0∞ := fun z => ENNReal.ofReal (omG β z) with hA
  set D : ℍ → ℝ≥0∞ := fun z => ‖d z‖ₑ with hD
  have hAm : Measurable A := ENNReal.measurable_ofReal.comp (measurable_omG β)
  have hDm : Measurable D := (Lp.stronglyMeasurable d).measurable.enorm
  set f : ℍ → ℝ≥0∞ := fun z => (A z ^ 2 * D z ^ 2) ^ θ with hf
  set g : ℍ → ℝ≥0∞ := fun z => (D z ^ 2) ^ (1 - θ) with hg
  have hfm : AEMeasurable f volume := (((hAm.pow_const 2).mul (hDm.pow_const 2)).pow_const θ).aemeasurable
  have hgm : AEMeasurable g volume := ((hDm.pow_const 2).pow_const (1 - θ)).aemeasurable
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume : Measure ℍ) hp hfm hgm
  have e1 : ∀ z, f z ^ (1 / θ) = A z ^ 2 * D z ^ 2 := fun z => by
    simp only [hf]
    rw [← ENNReal.rpow_mul]
    field_simp
    simp
  have e2 : ∀ z, g z ^ (1 / (1 - θ)) = D z ^ 2 := fun z => by
    simp only [hg]
    rw [← ENNReal.rpow_mul]
    have h2 : 1 - θ ≠ 0 := by linarith
    field_simp
    simp
  simp only [e1, e2] at hH
  have e3 : ∀ z, (ENNReal.ofReal (omG γ z) * D z) ^ 2 = f z * g z := fun z => by
    have hAe : ENNReal.ofReal (omG γ z) = A z ^ θ := by
      simp only [hA]
      rw [ENNReal.ofReal_rpow_of_pos (omG_pos hβ z)]
      congr 1
      show coshD UpperHalfPlane.I z ^ γ = (coshD UpperHalfPlane.I z ^ β) ^ θ
      have h00 : 0 ≤ coshD UpperHalfPlane.I z := (Real.cosh_pos _).le
      rw [hγ, ← Real.rpow_mul h00, mul_comm]
    simp only [hf, hg]
    rw [hAe, ENNReal.mul_rpow_of_nonneg _ _ hθ0.le, mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ hθ0.le (by linarith)]
    have e4 : θ + (1 - θ) = 1 := by ring
    rw [e4, ENNReal.rpow_one, mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast (A z) 2, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, mul_comm θ]
  have Iγ : ∫⁻ z, f z * g z = ENNReal.ofReal (‖xγ‖ ^ 2) := by
    rw [← lintegral_enorm_sq_eq]
    refine lintegral_congr_ae ?_
    filter_upwards [cγ] with z hz
    rw [hz, enorm_mul, ← e3, ← ofReal_norm_eq_enorm ((omG γ z : ℝ) : ℂ), Complex.norm_real, Real.norm_of_nonneg (omG_pos (by rw [hγ]; positivity) z).le]
  have Iβ : ∫⁻ z, A z ^ 2 * D z ^ 2 = ENNReal.ofReal (‖xβ‖ ^ 2) := by
    rw [← lintegral_enorm_sq_eq]
    refine lintegral_congr_ae ?_
    filter_upwards [cβ] with z hz
    rw [hz, enorm_mul, ← ofReal_norm_eq_enorm ((omG β z : ℝ) : ℂ), Complex.norm_real, Real.norm_of_nonneg (omG_pos hβ z).le, mul_pow]
  have Id : ∫⁻ z, D z ^ 2 = ENNReal.ofReal (‖d‖ ^ 2) := lintegral_enorm_sq_eq d
  have hIg : (∫⁻ z, (f * g) z) = ∫⁻ z, f z * g z := rfl
  rw [hIg, Iγ, Iβ, Id] at hH
  have hsimp : ‖xγ‖ ^ 2 ≤ (‖xβ‖ ^ 2) ^ θ * (‖d‖ ^ 2) ^ (1 - θ) := by
    have e5 : 1 / (1 / θ) = θ := by field_simp
    have e6 : 1 / (1 / (1 - θ)) = 1 - θ := by
      have h2 : 1 - θ ≠ 0 := by linarith
      field_simp
    rw [e5, e6, ENNReal.ofReal_rpow_of_nonneg (by positivity) hθ0.le, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by linarith),
      ← ENNReal.ofReal_mul (by positivity)] at hH
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hH
  have e7 : (‖xβ‖ ^ 2) ^ θ * (‖d‖ ^ 2) ^ (1 - θ) = (‖xβ‖ ^ θ * ‖d‖ ^ (1 - θ)) ^ 2 := by
    rw [mul_pow, ← Real.rpow_natCast (‖xβ‖ ^ θ), ← Real.rpow_mul (norm_nonneg _), ← Real.rpow_natCast (‖d‖ ^ (1 - θ)), ← Real.rpow_mul (norm_nonneg _),
      ← Real.rpow_natCast ‖xβ‖ 2, ← Real.rpow_mul (norm_nonneg _), ← Real.rpow_natCast ‖d‖ 2, ← Real.rpow_mul (norm_nonneg _)]
    push_cast
    ring_nf
  rw [e7] at hsimp
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsimp

section chartInt

variable {Γ : Subgroup PGL(2, ℝ)} [Countable Γ] [ProperlyDiscontinuousSMul Γ ℍ] (W : SurfW Γ) (P : MollProfile) {ε : ℝ} (hε : 0 < ε)
  {γ : ℝ} {hγ : 0 ≤ γ} (hWω : ∀ z, W.ω z = omG γ z) (O : WOps (P.cutoffEps hε) hγ) (hb s₁ : ℝ)
  {b' : negLapH.domain} {G₀ GX₀ GY₀ GXX₀ GYY₀ : L2H'} (hI : W.SurfIn b' G₀ GX₀ GY₀ GXX₀ GYY₀)

/-- `c (Δ_ε(s) - Δ(s)) g`. -/
noncomputable def dFun (χ : Cutoff) (hb : ℝ) (g : negLapH.domain) (s : ℝ) : L2H' :=
  (Complex.I * (hb : ℂ) / 2) • (χ.lapEps s (g : L2H') - lapTbar s (grP g))

include hWω hI

lemma pathD_val (s : ℝ) : (O.pathD P hε hb s₁ (G₀ := G₀) b' s : L2H') = omInv hγ (O.pathG hb s₁ G₀ s) := by
  have hG : omInv hγ G₀ = (b' : L2H') := omInv_of_chart W hWω (hγ := hγ) hI.cG
  rw [O.pathG_eq, map_add, hG]
  show (b' : L2H') + (P.cutoffEps hε).J (omInv hγ (O.pathH hb s₁ G₀ s)) = _
  rw [← show omInv hγ (O.Jw (O.pathH hb s₁ G₀ s)) = (P.cutoffEps hε).J (omInv hγ (O.pathH hb s₁ G₀ s)) from omInv_wConj hγ O.ha O.hJ _]

lemma pathD_flow (s : ℝ) : (O.pathD P hε hb s₁ (G₀ := G₀) b' s : L2H')
    = (P.cutoffEps hε).flowEps hb s (ContinuousLinearMap.adjoint ((P.cutoffEps hε).flowEps hb s₁) (b' : L2H')) := by
  rw [pathD_val W P hε hWω O hb s₁ hI s]
  exact O.omInv_pathG hb s₁ G₀ (omInv_of_chart W hWω (hγ := hγ) hI.cG) s

/-- `x(s)` is the chart of `c (Δ_ε(s) - Δ(s)) g(s)`. -/
theorem xInt_chart (s : ℝ) : W.Chart (O.xInt hb s₁ G₀ GY₀ GXX₀ GYY₀ s) (dFun (P.cutoffEps hε) hb (O.pathD P hε hb s₁ (G₀ := G₀) b' s) s) := by
  have hS := pathD_surfIn W P hε hWω O hb s₁ hI s
  set g := O.pathD P hε hb s₁ (G₀ := G₀) b' s with hg
  have c1 : W.Chart (O.pathGd hb s₁ G₀ s) ((Complex.I * (hb : ℂ) / 2) • (P.cutoffEps hε).lapEps s (g : L2H')) := by
    have h := chart_omInv W hWω (hγ := hγ) (O.pathGd hb s₁ G₀ s)
    have e : omInv hγ (O.pathGd hb s₁ G₀ s) = (Complex.I * (hb : ℂ) / 2) • (P.cutoffEps hε).lapEps s (g : L2H') := by
      show omInv hγ (O.genW hb s (O.pathG hb s₁ G₀ s)) = _
      rw [O.omInv_genW, ← pathD_val W P hε hWω O hb s₁ hI s]
    rwa [e] at h
  have c2 : W.Chart (SurfW.gDel s (GY₀ + O.Byw (O.pathH hb s₁ G₀ s)) (GXX₀ + O.XXw (O.pathH hb s₁ G₀ s))
      (GYY₀ + O.YYw (O.pathH hb s₁ G₀ s) + O.Byw (O.pathH hb s₁ G₀ s))) (lapTbar s (grP g)) := by
    have h := ((hS.cXX.smul ((Real.exp (-2 * s) : ℝ) : ℂ)).add hS.cYY).sub hS.cY
    have e : lapTbar s (grP g) = ((Real.exp (-2 * s) : ℝ) : ℂ) • domX ⟨domX g, hS.hX⟩ + domY ⟨domY g, hS.hY⟩ - domY g := by
      unfold lapTbar
      rw [psiX_word g hS.hX, psiY_word g hS.hY, add_sub_assoc]
    rw [e]
    exact h
  have h := c1.sub (c2.smul (Complex.I * (hb : ℂ) / 2))
  show W.Chart _ ((Complex.I * (hb : ℂ) / 2) • ((P.cutoffEps hε).lapEps s (g : L2H') - lapTbar s (grP g)))
  rw [smul_sub]
  exact h

end chartInt

section master

variable {Γ : Subgroup PGL(2, ℝ)} [Countable Γ] [ProperlyDiscontinuousSMul Γ ℍ] (W Wβ : SurfW Γ) (P : MollProfile) {ε : ℝ} (hε : 0 < ε)
  {γ β θ : ℝ} {hγ : 0 ≤ γ} {hβ : 0 ≤ β}

/-- **The master bound for the surface object.** -/
theorem surfV_master (hWω : ∀ z, W.ω z = omG γ z) (hWβ : ∀ z, Wβ.ω z = omG β z) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hγβ : γ = θ * β)
    (O : WOps (P.cutoffEps hε) hγ) (Oβ : WOps (P.cutoffEps hε) hβ) {hb : ℝ} (hb0 : hb ≠ 0) {s₁ : ℝ} (hs₁ : 0 ≤ s₁) {b' : negLapH.domain}
    {G₀ GX₀ GY₀ GXX₀ GYY₀ B₀ BX₀ BY₀ BXX₀ BYY₀ : L2H'} (hI : W.SurfIn b' G₀ GX₀ GY₀ GXX₀ GYY₀) (hIβ : Wβ.SurfIn b' B₀ BX₀ BY₀ BXX₀ BYY₀)
    {X Yd : ℝ} (hX : ∀ s ∈ Icc 0 s₁, ‖Oβ.xInt hb s₁ B₀ BY₀ BXX₀ BYY₀ s‖ ≤ X)
    (hY : ∀ s ∈ Icc 0 s₁, ‖dFun (P.cutoffEps hε) hb (O.pathD P hε hb s₁ (G₀ := G₀) b' s) s‖ ≤ Yd) :
    ‖W.surfV hb s₁ G₀‖ ≤ Real.sqrt W.C.toReal * ‖O.pathG hb s₁ G₀ 0‖
      + s₁ * (Real.sqrt W.C.toReal * (Real.exp (γ * s₁) * (X ^ θ * Yd ^ (1 - θ)))) := by
  have hdu := path_duhamel W P hε hWω O s₁ hI hb0 0 s₁
  rw [O.pathG_base] at hdu
  have hγ' : 0 ≤ γ := hγ
  set x := O.xInt hb s₁ G₀ GY₀ GXX₀ GYY₀ with hx
  have hint : ‖∫ s in (0 : ℝ)..s₁, W.surfV hb s (x s)‖ ≤ Real.sqrt W.C.toReal * (Real.exp (γ * s₁) * (X ^ θ * Yd ^ (1 - θ))) * |s₁ - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun s hs => ?_
    rw [uIoc_of_le hs₁] at hs
    have hs' : s ∈ Icc 0 s₁ := ⟨hs.1.le, hs.2⟩
    refine (norm_surfV_le W hγ hWω hb s (x s)).trans (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _))
    have c1 := xInt_chart W P hε hWω O hb s₁ hI s
    have c2 := xInt_chart Wβ P hε hWβ Oβ hb s₁ hIβ s
    have hv : (Oβ.pathD P hε hb s₁ (G₀ := B₀) b' s : L2H') = (O.pathD P hε hb s₁ (G₀ := G₀) b' s : L2H') := by
      rw [pathD_flow Wβ P hε hWβ Oβ hb s₁ hIβ s, pathD_flow W P hε hWω O hb s₁ hI s]
    have hgg : Oβ.pathD P hε hb s₁ (G₀ := B₀) b' s = O.pathD P hε hb s₁ (G₀ := G₀) b' s := Subtype.ext hv
    rw [hgg] at c2
    set d := dFun (P.cutoffEps hε) hb (O.pathD P hε hb s₁ (G₀ := G₀) b' s) s with hd
    have cγ : ⇑(x s) =ᵐ[volume] fun z => ((omG γ z : ℝ) : ℂ) * d z := by
      have h : ⇑(x s) =ᵐ[volume] _ := c1
      filter_upwards [h] with z hz
      rw [hz, hWω]
    have cβ : ⇑(Oβ.xInt hb s₁ B₀ BY₀ BXX₀ BYY₀ s) =ᵐ[volume] fun z => ((omG β z : ℝ) : ℂ) * d z := by
      have h : ⇑(Oβ.xInt hb s₁ B₀ BY₀ BXX₀ BYY₀ s) =ᵐ[volume] _ := c2
      filter_upwards [h] with z hz
      rw [hz, hWβ]
    have hH := chart_holder hβ hθ0 hθ1 hγβ cγ cβ
    have hYs := hY s hs'
    have hXs := hX s hs'
    have hexp : Real.exp (γ * |s|) ≤ Real.exp (γ * s₁) := by
      rw [abs_of_nonneg hs.1.le]
      exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hs.2 hγ)
    have hYd0 : 0 ≤ Yd := (norm_nonneg _).trans hYs
    have hX0 : 0 ≤ X := (norm_nonneg _).trans hXs
    have hp1 : ‖Oβ.xInt hb s₁ B₀ BY₀ BXX₀ BYY₀ s‖ ^ θ ≤ X ^ θ := Real.rpow_le_rpow (norm_nonneg _) hXs hθ0.le
    have hp2 : ‖d‖ ^ (1 - θ) ≤ Yd ^ (1 - θ) := Real.rpow_le_rpow (norm_nonneg _) hYs (by linarith)
    have hprod : ‖x s‖ ≤ X ^ θ * Yd ^ (1 - θ) :=
      hH.trans (mul_le_mul hp1 hp2 (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg hX0 _))
    exact mul_le_mul hexp hprod (norm_nonneg _) (Real.exp_pos _).le
  have hG : ‖W.surfV hb 0 (O.pathG hb s₁ G₀ 0)‖ ≤ Real.sqrt W.C.toReal * ‖O.pathG hb s₁ G₀ 0‖ := by
    have h := norm_surfV_le W hγ hWω hb 0 (O.pathG hb s₁ G₀ 0)
    simpa using h
  have hEq : W.surfV hb s₁ G₀ = W.surfV hb 0 (O.pathG hb s₁ G₀ 0) + ∫ s in (0 : ℝ)..s₁, W.surfV hb s (x s) := by
    rw [← hdu]; abel
  rw [hEq]
  refine (norm_add_le _ _).trans (add_le_add hG (hint.trans (le_of_eq ?_)))
  rw [sub_zero, abs_of_nonneg hs₁]
  ring

end master

end Qschubert
