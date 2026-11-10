import Qschubert.KLPcD2c

/-!
# The bound of `𝒱_{s₁} b'` on the simplex for the printed class

`surfV_indep`: the surface object does not depend on the weight of the chart. `vS_bound_pc`: for a periodization weight `W` of critical type
(`CritW`) with `|ω(z)/ω(δ_s z)| ≤ D_g e^{|s|}`, and `h` with a chart in `W`,

`‖𝒱_{s₁} B'_s e^{-σΛ_m} h‖ ≤ √C K₁ C₄^{N+L+2} (2N)! (2+2L)! σ^{-2L} (σħ)^{-2N} ‖ω h‖`.

For `h` that also has a chart in the weight `X₀`, this is the Duhamel formula on `M` in the weight `X₀^{3/4}` (`path_duhamel`), with each
term bounded through `W` by `flow_chart_om` and `dvec_chart_om`. The general case follows by density (`tendsto_sum_cutN`), with the
continuity from `bE_chart_om`. This is Section 6 (d) of `notes/printed_interp_route.md`.
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set Physicslib4.Spectral Physicslib4.Spectral.Unbounded
open scoped ENNReal InnerProductSpace ComplexConjugate UpperHalfPlane MatrixGroups Pointwise

local notation "L2H'" => Lp ℂ 2 (volume : Measure UpperHalfPlane)

lemma split_rpow {p q k a b : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q = 1) (hk : 0 ≤ k) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    k * (a ^ q * b ^ p) = (k * b) ^ p * (k * a) ^ q := by
  rw [Real.mul_rpow hk hb, Real.mul_rpow hk ha]
  have e : k = k ^ p * k ^ q := by rw [← Real.rpow_add_of_nonneg hk hp hq, hpq, Real.rpow_one]
  calc k * (a ^ q * b ^ p) = (k ^ p * k ^ q) * (a ^ q * b ^ p) := by rw [← e]
    _ = _ := by ring

section surf

variable {Γ : Subgroup PGL(2, ℝ)} [Countable Γ] [ProperlyDiscontinuousSMul Γ ℍ]

/-- **The surface object does not depend on the weight of the chart.** -/
theorem surfV_indep (W₁ W₂ : SurfW Γ) (hb s : ℝ) {G₁ G₂ v : L2H'} (h₁ : W₁.Chart G₁ v) (h₂ : W₂.Chart G₂ v) :
    W₁.surfV hb s G₁ = W₂.surfV hb s G₂ := by
  have e : W₁.surfL hb s G₁ = W₂.surfL hb s G₂ := by
    show W₁.perioW (W₁.TW hb s G₁) = W₂.perioW (W₂.TW hb s G₂)
    have c1 := W₁.TW_chart hb s h₁
    have c2 := W₂.TW_chart hb s h₂
    have hm : Measurable ((phaseLp 1 hb (transportLp s v) : L2H') : ℍ → ℂ) := (Lp.stronglyMeasurable _).measurable
    refine Lp.ext ?_
    filter_upwards [W₁.perioW_ae hm c1, W₂.perioW_ae hm c2] with x e1 e2
    rw [e1, e2]
  rw [SurfW.surfV_apply, SurfW.surfV_apply, e]

/-- `‖𝒱_s x‖ ≤ √C D ‖x‖` if `|ω(z)/ω(δ_s z)| ≤ D`. -/
lemma norm_surfV_le_gen (W : SurfW Γ) (hb s : ℝ) {Dg : ℝ} (hD : ∀ z, |W.mS s z| ≤ Dg) (x : L2H') :
    ‖W.surfV hb s x‖ ≤ Real.sqrt W.C.toReal * (Dg * ‖x‖) := by
  rw [SurfW.norm_surfV]
  show ‖W.perioW (W.TW hb s x)‖ ≤ _
  refine (W.perioW.le_of_opNorm_le (LinearMap.mkContinuous_norm_le _ (Real.sqrt_nonneg _) _) _).trans ?_
  exact mul_le_mul_of_nonneg_left (norm_TW_le' W hb s hD x) (Real.sqrt_nonneg _)

end surf

section assemble

variable {c D Dg m : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hD : 0 < D) (hDg : 0 ≤ Dg) (hm : 1 / 2 ≤ m) (hml : 2 * ((1 : ℝ) + 1 / 2) ^ 2 < m ^ 2)
include hc0 hc1 hD hDg hm hml

set_option maxHeartbeats 16000000 in
/-- **The bound of `𝒱_{s₁} b'` on the simplex, printed class.** -/
theorem vS_bound_pc {kp C₁ : ℝ} (hkp : 0 < kp) (hC : 0 ≤ C₁) (hF' : FCBound 1 C₁) :
    ∃ K₁ δ : ℝ, 0 ≤ K₁ ∧ 0 < δ ∧ ∀ (Γ' : Subgroup PGL(2, ℝ)) [Countable Γ'] [ProperlyDiscontinuousSMul Γ' ℍ] (W Wγ Wβ : SurfW Γ'),
      CritW c D W.ω → (∀ s z, |W.mS s z| ≤ Dg * Real.exp |s|) → (∀ z, Wγ.ω z = omG (3 / 4) z) → (∀ z, Wβ.ω z = omG 1 z) →
      ∀ (ħ σ t : ℝ) (N : ℕ) (ss : List ℝ) (h Hω : L2H'), W.Chart Hω h → 0 < ħ → ħ ≤ 1 → 0 < σ → σ ≤ 1 → kp * ħ ≤ σ ^ 3 → 0 ≤ t →
        t ≤ δ * Real.sqrt (σ / ħ) → (∀ s ∈ ss, 0 ≤ s ∧ s ≤ t) →
        ‖W.vS ħ (ss.headD 0) (bE m σ ħ N (ss.headD 0) ss h)‖
          ≤ Real.sqrt W.C.toReal * K₁ * C4m C₁ ^ (N + ss.length + 2) * ((2 * N).factorial : ℝ)
            * ((2 + 2 * ss.length).factorial : ℝ) * (σ⁻¹) ^ (2 * ss.length) * ((σ * ħ)⁻¹) ^ (2 * N) * ‖Hω‖ := by
  obtain ⟨Ka, hKa, hbE⟩ := bE_chart_om hc0 hc1 hD hm hml
  obtain ⟨Kf, A₀, hKf, hA₀, hflow⟩ := flow_chart_om hc0 hc1 hD hm hml
  obtain ⟨Kd, A₁, C₀, hKd, hA₁, hC₀, hdv⟩ := dvec_chart_om hc0 hc1 hD hm hml
  have hγ0 : (0 : ℝ) ≤ 3 / 4 := by norm_num
  obtain ⟨Qγ, hQγ0, hQγ⟩ := wbd_ops stdP hγ0
  have hcA0 : 0 < cA0 1 := cA0_pos 1
  set ke : ℝ := 1 / 64 with hke
  have hke0 : 0 < ke := by rw [hke]; norm_num
  set δ : ℝ := min (1 / 64) (cA0 1 / 6) with hδ
  have hδ0 : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ1 : δ ≤ 1 / 64 := min_le_left _ _
  have hδ2 : δ ≤ cA0 1 / 6 := min_le_right _ _
  set KD : ℝ := Kd * Dg with hKD
  have hKD0 : 0 ≤ KD := by positivity
  set a₂ : ℝ := KD * (8 * C₀) with ha₂
  have ha₂0 : 0 ≤ a₂ := by positivity
  set A₁' : ℝ := KD * (A₁ + 8 * C₀ / (4 * kp)) with hA₁'
  have hA₁'0 : 0 ≤ A₁' := by positivity
  set cR := cR2 δ A₁' a₂ kp ke with hcR
  have hcR0 : 0 ≤ cR := by
    rw [hcR]; unfold cR2; positivity
  set Bc : ℝ := Dg * (Kf * (1 + A₀)) with hBc
  have hBc0 : 0 ≤ Bc := by positivity
  refine ⟨(1 + Bc) * 1 + cR, δ, by positivity, hδ0, fun Γ' _ _ W Wγ Wβ hW hgr hWγ hWβ ħ σ t N ss h Hω hHω hħ hħ1 hσ hσ1 hk ht htδ hss => ?_⟩
  -- scales
  set y := Real.sqrt (σ / ħ) with hyd
  have hy0 : 0 < y := Real.sqrt_pos.2 (by positivity)
  set ε := Real.sqrt (σ * ħ) / 2 with hεd
  have hS0 : 0 < Real.sqrt (σ * ħ) := Real.sqrt_pos.2 (by positivity)
  have hε : 0 < ε := by rw [hεd]; positivity
  have hε1 : ε ≤ 1 := by
    have h1 : Real.sqrt (σ * ħ) ≤ 1 := Real.sqrt_le_one.2 (by nlinarith)
    rw [hεd]; linarith
  have hεα : σ = 2 * ε * y := by
    have h : Real.sqrt (σ * ħ) * Real.sqrt (σ / ħ) = σ := by
      rw [← Real.sqrt_mul (by positivity)]
      have e : σ * ħ * (σ / ħ) = σ ^ 2 := by field_simp
      rw [e, Real.sqrt_sq hσ.le]
    rw [hεd, hyd]
    linarith
  have hħy : ħ * y = 2 * ε := by
    have e : σ * ħ = ħ ^ 2 * (σ / ħ) := by field_simp
    have h : Real.sqrt (σ * ħ) = ħ * Real.sqrt (σ / ħ) := by
      rw [e, Real.sqrt_mul (by positivity), Real.sqrt_sq hħ.le]
    rw [hεd, h, hyd]
    ring
  have hεsq : ε ^ 2 = σ * ħ / 4 := by
    rw [hεd, div_pow, Real.sq_sqrt (by positivity)]
    norm_num
  have hssn : ∀ s ∈ ss, 0 ≤ s := fun s h => (hss s h).1
  obtain ⟨hs₁0, hs₁t⟩ : 0 ≤ ss.headD 0 ∧ ss.headD 0 ≤ t := by
    cases ss with
    | nil => exact ⟨le_rfl, ht⟩
    | cons a l => exact hss a (by simp)
  set s₁ := ss.headD 0 with hs₁d
  have hs₁y : s₁ ≤ δ * y := hs₁t.trans htδ
  have hwin : ħ * s₁ ≤ ε := by
    calc ħ * s₁ ≤ ħ * (δ * y) := by gcongr
      _ = δ * (ħ * y) := by ring
      _ = δ * (2 * ε) := by rw [hħy]
      _ ≤ 1 / 2 * (2 * ε) := by gcongr; linarith
      _ = ε := by ring
  have hE1 : 1 ≤ ε⁻¹ := (one_le_inv₀ hε).2 hε1
  have hE0 : 0 < ε⁻¹ := by linarith
  have hεE : ε * ε⁻¹ = 1 := mul_inv_cancel₀ hε.ne'
  have hAi0 : 0 < σ⁻¹ := inv_pos.2 hσ
  have hAi1 : 1 ≤ σ⁻¹ := (one_le_inv₀ hσ).2 hσ1
  have hAσ : σ * σ⁻¹ = 1 := mul_inv_cancel₀ hσ.ne'
  have hwin2 : ∀ s ∈ Icc (0 : ℝ) s₁, |s - s₁| ≤ cA0 1 * (1 / 3) * (ε / ħ) := fun s hs => by
    have h1 : |s - s₁| ≤ s₁ := by
      rw [abs_le]; constructor <;> linarith [hs.1, hs.2]
    have h3 : ε / ħ = y / 2 := by
      rw [div_eq_iff hħ.ne']
      linarith
    rw [h3]
    have h5 : δ * y ≤ cA0 1 / 6 * y := mul_le_mul_of_nonneg_right hδ2 hy0.le
    have e : cA0 1 * (1 / 3) * (y / 2) = cA0 1 / 6 * y := by ring
    rw [e]
    linarith
  have hCm1 : 1 ≤ C4m C₁ := one_le_C4m C₁
  have hCm0 : 0 ≤ C4m C₁ := by linarith
  have hfac20 : 0 ≤ facP (C4m C₁) σ ħ N ss.length 2 := facP_nonneg hCm0 hσ hħ N ss.length 2
  set Bq : ℝ := C4m C₁ ^ (N + ss.length + 2) * ((2 * N).factorial : ℝ) * ((2 + 2 * ss.length).factorial : ℝ) * (σ⁻¹) ^ (2 * ss.length)
    * ((σ * ħ)⁻¹) ^ (2 * N) with hBq
  have hBq0 : 0 ≤ Bq := by positivity
  have hfacBq : σ ^ 2 * facP (C4m C₁) σ ħ N ss.length 2 = Bq := by
    unfold facP
    rw [hBq, pow_add (σ⁻¹) 2 (2 * ss.length)]
    calc σ ^ 2 * (C4m C₁ ^ (N + ss.length + 2) * ((2 * N).factorial : ℝ) * ((2 + 2 * ss.length).factorial : ℝ) * (σ⁻¹ ^ 2 * σ⁻¹ ^ (2 * ss.length))
          * ((σ * ħ)⁻¹) ^ (2 * N))
        = (σ * σ⁻¹) ^ 2 * (C4m C₁ ^ (N + ss.length + 2) * ((2 * N).factorial : ℝ) * ((2 + 2 * ss.length).factorial : ℝ) * σ⁻¹ ^ (2 * ss.length)
          * ((σ * ħ)⁻¹) ^ (2 * N)) := by ring
      _ = _ := by rw [hAσ]; ring
  have hfac0Bq : facP (C4m C₁) σ ħ N ss.length 0 ≤ Bq := by
    rw [facP_zero, hBq]
    have h1 : C4m C₁ ^ (N + ss.length) ≤ C4m C₁ ^ (N + ss.length + 2) := pow_le_pow_right₀ hCm1 (by omega)
    have h2 : ((2 * ss.length).factorial : ℝ) ≤ ((2 + 2 * ss.length).factorial : ℝ) := by exact_mod_cast Nat.factorial_le (by omega)
    gcongr
  -- the arithmetic of the factor R
  have hAiE : 4 * σ⁻¹ ≤ (ε⁻¹) ^ 2 := by
    have h1 : 4 * σ⁻¹ * ε ^ 2 = ħ := by
      rw [hεsq]
      field_simp
    have h2 : 4 * σ⁻¹ = (4 * σ⁻¹ * ε ^ 2) * (ε⁻¹) ^ 2 := by
      have h3 : ε ^ 2 * (ε⁻¹) ^ 2 = 1 := by rw [← mul_pow, hεE, one_pow]
      calc 4 * σ⁻¹ = 4 * σ⁻¹ * (ε ^ 2 * (ε⁻¹) ^ 2) := by rw [h3, mul_one]
        _ = _ := by ring
    rw [h2, h1]
    calc ħ * (ε⁻¹) ^ 2 ≤ 1 * (ε⁻¹) ^ 2 := by gcongr
      _ = (ε⁻¹) ^ 2 := one_mul _
  have hħA : ħ * (σ⁻¹) ^ 4 ≤ (ε⁻¹) ^ 3 / (4 * kp) := by
    have h2 : ħ ≤ kp⁻¹ * σ ^ 3 := by
      have hkpi : kp⁻¹ * kp = 1 := inv_mul_cancel₀ hkp.ne'
      calc ħ = (kp⁻¹ * kp) * ħ := by rw [hkpi, one_mul]
        _ = kp⁻¹ * (kp * ħ) := by ring
        _ ≤ kp⁻¹ * σ ^ 3 := by gcongr
    have h3 : ħ * (σ⁻¹) ^ 4 ≤ kp⁻¹ * σ⁻¹ := by
      calc ħ * (σ⁻¹) ^ 4 ≤ (kp⁻¹ * σ ^ 3) * (σ⁻¹) ^ 4 := by gcongr
        _ = kp⁻¹ * ((σ * σ⁻¹) ^ 3 * σ⁻¹) := by ring
        _ = kp⁻¹ * σ⁻¹ := by rw [hAσ]; ring
    have h4 : 4 * σ⁻¹ ≤ (ε⁻¹) ^ 3 := hAiE.trans (pow_le_pow_right₀ hE1 (by norm_num))
    rw [le_div_iff₀ (by positivity)]
    calc ħ * (σ⁻¹) ^ 4 * (4 * kp) ≤ kp⁻¹ * σ⁻¹ * (4 * kp) := by gcongr
      _ = (kp⁻¹ * kp) * (4 * σ⁻¹) := by ring
      _ = 4 * σ⁻¹ := by rw [inv_mul_cancel₀ hkp.ne', one_mul]
      _ ≤ (ε⁻¹) ^ 3 := h4
  have hYE : 8 * C₀ * ħ * (σ⁻¹) ^ 4 * Real.exp (-(σ / (16 * ε))) ≤ 8 * C₀ / (4 * kp) * (ε⁻¹) ^ 3 := by
    have h1 : Real.exp (-(σ / (16 * ε))) ≤ 1 := Real.exp_le_one_iff.2 (neg_nonpos.2 (by positivity))
    have h0 : 0 ≤ 8 * C₀ * ħ * (σ⁻¹) ^ 4 := by positivity
    calc 8 * C₀ * ħ * (σ⁻¹) ^ 4 * Real.exp (-(σ / (16 * ε))) ≤ 8 * C₀ * ħ * (σ⁻¹) ^ 4 * 1 := by gcongr
      _ = 8 * C₀ * (ħ * (σ⁻¹) ^ 4) := by ring
      _ ≤ 8 * C₀ * ((ε⁻¹) ^ 3 / (4 * kp)) := by gcongr
      _ = _ := by ring
  have eER : σ / (16 * ε) = 1 * y / 8 := by
    have hεne := hε.ne'
    rw [hεα]
    field_simp
    ring
  have hdec : ke + 1 * δ ≤ (1 - 3 / 4) * ((1 : ℝ) / 8) := by
    rw [hke]
    linarith
  have hR := dd_R_bound (A₁ := A₁') (a₂ := a₂) (δ := δ) (γ := 1) (θ := 3 / 4) (c₀ := 1) (kp := kp) (ke := ke) hσ hσ1 hħ hy0 hε hε1 hεα hħy hkp hk
    hA₁'0 ha₂0 hδ0.le hs₁0 hs₁y zero_le_one hke0 hdec
  have hE5 : (Real.exp (-(1 * y / 8))) ^ (1 - 3 / 4 : ℝ) = Real.exp (-((1 - 3 / 4) * (1 * y / 8))) := by
    rw [← Real.exp_mul]
    congr 1
    ring
  have hR' : s₁ * Real.exp (1 * s₁) * ((1 + A₁' * (ε⁻¹) ^ 3) * (1 + a₂ * ħ * (σ⁻¹) ^ 4)) * (Real.exp (-(1 * y / 8))) ^ (1 - 3 / 4 : ℝ)
      ≤ cR * σ ^ 2 := by
    rw [hE5]
    exact hR
  -- inputs with a chart in the weight `X₀`
  have hnice : ∀ (u Uω U G : L2H'), W.Chart Uω u → ((U : ℍ → ℂ) =ᵐ[volume] fun z => ((omG 1 z : ℝ) : ℂ) * u z) →
      W.Chart G (bE m σ ħ N s₁ ss u) → ‖W.surfV ħ s₁ G‖ ≤ Real.sqrt W.C.toReal * ((1 + Bc) * 1 + cR) * (1 * (Bq * ‖Uω‖)) := by
    intro u Uω U G hUω hU hG
    have hU0 := norm_nonneg Uω
    have hA : AllWords (bE m σ ħ N s₁ ss u) := bE_allWords hm hσ hσ1 ħ N s₁ ss u
    have hbm : bE m σ ħ N s₁ ss u ∈ negLapH.domain := bE_mem hm hσ hσ1 ħ N s₁ ss u
    set b' : negLapH.domain := ⟨bE m σ ħ N s₁ ss u, hbm⟩ with hb'
    have hwg : ∀ (J : List Bool), ∃ Gj : L2H', Wγ.Chart Gj (wordAct J (bE m σ ħ N s₁ ss u)) := fun J => by
      obtain ⟨-, B, hB, -⟩ := pc_wb_w (β := 1) zero_le_one hm hml hσ hσ1 hU hħ hħ1 N hs₁0 ss hssn J (n := J.length) le_rfl
      obtain ⟨G', hG', -⟩ := chart_down (zero_le_one : (0 : ℝ) ≤ 1) (by norm_num : (3 / 4 : ℝ) ≤ 1) hB
      refine ⟨G', ?_⟩
      show ⇑G' =ᵐ[volume] _
      filter_upwards [hG'] with z hz
      rw [hz, hWγ]
      rfl
    obtain ⟨G₀, hG₀⟩ := hwg []
    obtain ⟨GX, hGX⟩ := hwg [true]
    obtain ⟨GY, hGY⟩ := hwg [false]
    obtain ⟨GXX, hGXX⟩ := hwg [true, true]
    obtain ⟨GYY, hGYY⟩ := hwg [false, false]
    have hIγ : Wγ.SurfIn b' G₀ GX GY GXX GYY := surfIn_of_words Wγ b' hA hG₀ hGX hGY hGXX hGYY
    obtain ⟨hJγ, hBxγ, hByγ, -, hXXγ, hYYγ⟩ := hQγ hε hε1
    have hEp : 0 ≤ ε⁻¹ := (inv_pos.2 hε).le
    let O : WOps (stdP.cutoffEps hε) hγ0 := ⟨Qγ, ε⁻¹ * Qγ, ε⁻¹ * ε⁻¹ * Qγ, hQγ0, by positivity, by positivity, hJγ, hBxγ, hByγ, hXXγ, hYYγ⟩
    have hdu := path_duhamel Wγ stdP hε hWγ O s₁ hIγ hħ.ne' 0 s₁
    rw [O.pathG_base] at hdu
    have hgg : ∀ s, O.pathD stdP hε ħ s₁ (G₀ := G₀) b' s = gflow stdP hε hε1 ħ s₁ b' s := fun s =>
      Subtype.ext (pathD_flow Wγ stdP hε hWγ O ħ s₁ hIγ s)
    -- the first term
    have e1 : Wγ.surfV ħ s₁ G₀ = W.surfV ħ s₁ G := surfV_indep Wγ W ħ s₁ hIγ.cG hG
    obtain ⟨Pω, hPω, nPω⟩ := hflow hW hF' hC Γ' Wβ hWβ hσ hσ1 hε hε1 hħ hħ1 N hs₁0 (⟨le_rfl, hs₁0⟩ : (0 : ℝ) ∈ Icc 0 s₁) hwin ss hssn hUω
    have hcP : Wγ.Chart (O.pathG ħ s₁ G₀ 0) (O.pathD stdP hε ħ s₁ (G₀ := G₀) b' 0 : L2H') := (pathD_surfIn Wγ stdP hε hWγ O ħ s₁ hIγ 0).cG
    rw [hgg 0] at hcP
    have hPω' : W.Chart Pω (gflow stdP hε hε1 ħ s₁ b' 0 : L2H') := hPω
    have e2 : Wγ.surfV ħ 0 (O.pathG ħ s₁ G₀ 0) = W.surfV ħ 0 Pω := surfV_indep Wγ W ħ 0 hcP hPω'
    have hfirst : ‖W.surfV ħ 0 Pω‖ ≤ Real.sqrt W.C.toReal * (Dg * ‖Pω‖) := by
      have := norm_surfV_le_gen W ħ 0 (Dg := Dg * Real.exp |0|) (hgr 0) Pω
      simpa using this
    -- the integrand
    have hint : ‖∫ s in (0 : ℝ)..s₁, Wγ.surfV ħ s (O.xInt ħ s₁ G₀ GY GXX GYY s)‖
        ≤ Real.sqrt W.C.toReal * (Real.exp (1 * s₁) * ((A₁' * (ε⁻¹) ^ 3 * (facP (C4m C₁) σ ħ N ss.length 2 * ‖Uω‖)) ^ (3 / 4 : ℝ)
          * (a₂ * ħ * (σ⁻¹) ^ 4 * Real.exp (-(1 * y / 8)) * 1 * (facP (C4m C₁) σ ħ N ss.length 2 * ‖Uω‖)) ^ (1 - 3 / 4 : ℝ))) * |s₁ - 0| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun s hs => ?_
      rw [uIoc_of_le hs₁0] at hs
      have hs' : s ∈ Icc 0 s₁ := ⟨hs.1.le, hs.2⟩
      have c1 := xInt_chart Wγ stdP hε hWγ O ħ s₁ hIγ s
      rw [hgg s] at c1
      obtain ⟨Xω, hXω, nXω⟩ := hdv hW hF' hC Γ' Wβ hWβ hσ hσ1 hε hε1 hħ hħ1 N hs₁0 hs' hwin (hwin2 s hs') ss hssn hUω
      have hXω' : W.Chart Xω (dFun (stdP.cutoffEps hε) ħ (gflow stdP hε hε1 ħ s₁ b' s) s) := hXω
      rw [surfV_indep Wγ W ħ s c1 hXω']
      refine (norm_surfV_le_gen W ħ s (hgr s) Xω).trans (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _))
      have hexp : Real.exp |s| ≤ Real.exp (1 * s₁) := by
        rw [abs_of_nonneg hs'.1, one_mul]
        exact Real.exp_le_exp.2 hs'.2
      have hY0 : 0 ≤ 8 * C₀ * ħ * (σ⁻¹) ^ 4 * Real.exp (-(σ / (16 * ε))) := by positivity
      have hE30 : 0 ≤ A₁ * (ε⁻¹) ^ 3 := by positivity
      have e14 : (1 / 4 : ℝ) = 1 - 3 / 4 := by norm_num
      rw [e14] at nXω
      have hsplit := split_rpow (p := 3 / 4) (q := 1 - 3 / 4) (by norm_num) (by norm_num) (by norm_num) (mul_nonneg hKD0 hU0)
        (mul_nonneg hY0 hfac20) (mul_nonneg (add_nonneg hY0 hE30) hfac20)
      have hM1 : KD * ‖Uω‖ * ((8 * C₀ * ħ * (σ⁻¹) ^ 4 * Real.exp (-(σ / (16 * ε))) + A₁ * (ε⁻¹) ^ 3) * facP (C4m C₁) σ ħ N ss.length 2)
          ≤ A₁' * (ε⁻¹) ^ 3 * (facP (C4m C₁) σ ħ N ss.length 2 * ‖Uω‖) := by
        have h1 : 8 * C₀ * ħ * (σ⁻¹) ^ 4 * Real.exp (-(σ / (16 * ε))) + A₁ * (ε⁻¹) ^ 3 ≤ (A₁ + 8 * C₀ / (4 * kp)) * (ε⁻¹) ^ 3 := by
          nlinarith [hYE]
        calc KD * ‖Uω‖ * ((8 * C₀ * ħ * (σ⁻¹) ^ 4 * Real.exp (-(σ / (16 * ε))) + A₁ * (ε⁻¹) ^ 3) * facP (C4m C₁) σ ħ N ss.length 2)
            ≤ KD * ‖Uω‖ * (((A₁ + 8 * C₀ / (4 * kp)) * (ε⁻¹) ^ 3) * facP (C4m C₁) σ ħ N ss.length 2) := by gcongr
          _ = _ := by rw [hA₁']; ring
      have hM0 : KD * ‖Uω‖ * (8 * C₀ * ħ * (σ⁻¹) ^ 4 * Real.exp (-(σ / (16 * ε))) * facP (C4m C₁) σ ħ N ss.length 2)
          = a₂ * ħ * (σ⁻¹) ^ 4 * Real.exp (-(1 * y / 8)) * 1 * (facP (C4m C₁) σ ħ N ss.length 2 * ‖Uω‖) := by
        rw [eER, ha₂]
        ring
      have hZb : Dg * ‖Xω‖ ≤ (A₁' * (ε⁻¹) ^ 3 * (facP (C4m C₁) σ ħ N ss.length 2 * ‖Uω‖)) ^ (3 / 4 : ℝ)
          * (a₂ * ħ * (σ⁻¹) ^ 4 * Real.exp (-(1 * y / 8)) * 1 * (facP (C4m C₁) σ ħ N ss.length 2 * ‖Uω‖)) ^ (1 - 3 / 4 : ℝ) := by
        calc Dg * ‖Xω‖
            ≤ Dg * (Kd * ((8 * C₀ * ħ * (σ⁻¹) ^ 4 * Real.exp (-(σ / (16 * ε))) * facP (C4m C₁) σ ħ N ss.length 2) ^ (1 - 3 / 4 : ℝ)
              * ((8 * C₀ * ħ * (σ⁻¹) ^ 4 * Real.exp (-(σ / (16 * ε))) + A₁ * (ε⁻¹) ^ 3) * facP (C4m C₁) σ ħ N ss.length 2) ^ (3 / 4 : ℝ)) * ‖Uω‖) :=
              mul_le_mul_of_nonneg_left nXω hDg
          _ = KD * ‖Uω‖ * ((8 * C₀ * ħ * (σ⁻¹) ^ 4 * Real.exp (-(σ / (16 * ε))) * facP (C4m C₁) σ ħ N ss.length 2) ^ (1 - 3 / 4 : ℝ)
              * ((8 * C₀ * ħ * (σ⁻¹) ^ 4 * Real.exp (-(σ / (16 * ε))) + A₁ * (ε⁻¹) ^ 3) * facP (C4m C₁) σ ħ N ss.length 2) ^ (3 / 4 : ℝ)) := by
              rw [hKD]; ring
          _ = (KD * ‖Uω‖ * ((8 * C₀ * ħ * (σ⁻¹) ^ 4 * Real.exp (-(σ / (16 * ε))) + A₁ * (ε⁻¹) ^ 3) * facP (C4m C₁) σ ħ N ss.length 2)) ^ (3 / 4 : ℝ)
              * (KD * ‖Uω‖ * (8 * C₀ * ħ * (σ⁻¹) ^ 4 * Real.exp (-(σ / (16 * ε))) * facP (C4m C₁) σ ħ N ss.length 2)) ^ (1 - 3 / 4 : ℝ) := hsplit
          _ ≤ _ := by
              rw [hM0]
              refine mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (by positivity) hM1 (by norm_num)) (Real.rpow_nonneg (by positivity) _)
      calc Dg * Real.exp |s| * ‖Xω‖ = Real.exp |s| * (Dg * ‖Xω‖) := by ring
        _ ≤ _ := mul_le_mul hexp hZb (by positivity) (Real.exp_pos _).le
    have hV : ‖W.surfV ħ s₁ G‖ ≤ Real.sqrt W.C.toReal * (Dg * ‖Pω‖)
        + s₁ * (Real.sqrt W.C.toReal * (Real.exp (1 * s₁) * ((A₁' * (ε⁻¹) ^ 3 * (facP (C4m C₁) σ ħ N ss.length 2 * ‖Uω‖)) ^ (3 / 4 : ℝ)
          * (a₂ * ħ * (σ⁻¹) ^ 4 * Real.exp (-(1 * y / 8)) * 1 * (facP (C4m C₁) σ ħ N ss.length 2 * ‖Uω‖)) ^ (1 - 3 / 4 : ℝ)))) := by
      have hEq : W.surfV ħ s₁ G = W.surfV ħ 0 Pω + ∫ s in (0 : ℝ)..s₁, Wγ.surfV ħ s (O.xInt ħ s₁ G₀ GY GXX GYY s) := by
        rw [← e1, ← e2, ← hdu]; abel
      rw [hEq]
      refine (norm_add_le _ _).trans (add_le_add hfirst (hint.trans (le_of_eq ?_)))
      rw [sub_zero, abs_of_nonneg hs₁0]
      ring
    have hG0 : Dg * ‖Pω‖ ≤ 1 * (Bc * (Bq * ‖Uω‖)) := by
      have h1 : ‖Pω‖ ≤ Kf * ((1 + A₀) * Bq) * ‖Uω‖ := by
        refine nPω.trans ?_
        gcongr
      calc Dg * ‖Pω‖ ≤ Dg * (Kf * ((1 + A₀) * Bq) * ‖Uω‖) := mul_le_mul_of_nonneg_left h1 hDg
        _ = _ := by rw [hBc]; ring
    have hal : σ ^ 2 * (facP (C4m C₁) σ ħ N ss.length 2 * ‖Uω‖) = Bq * ‖Uω‖ := by
      rw [← mul_assoc, hfacBq]
    exact final_arith (S := Real.sqrt W.C.toReal) (G0 := Dg * ‖Pω‖) (γ := 1) (θ := 3 / 4) (AE := A₁' * (ε⁻¹) ^ 3)
      (Bd₁ := facP (C4m C₁) σ ħ N ss.length 2 * ‖Uω‖) (Yh := a₂ * ħ * (σ⁻¹) ^ 4) (ER := Real.exp (-(1 * y / 8))) (Lam := 1) (G5 := 1) (B := Bc)
      (Bd₂ := Bq * ‖Uω‖) (cR := cR) (al := σ ^ 2) (Real.sqrt_nonneg _) hs₁0 (by norm_num) (by norm_num) (by positivity) (by positivity)
      (by positivity) (Real.exp_pos _) le_rfl one_pos hBc0 (by positivity) hcR0 hV hG0 hR' hal
  -- the general case, by density
  obtain ⟨G, hG, -⟩ := hbE hW hF' hC hσ hσ1 hħ hħ1 N hs₁0 ss hssn hHω
  have hG' : W.Chart G (bE m σ ħ N s₁ ss h) := hG
  rw [W.vS_apply ħ s₁ hG']
  have hHω' : ⇑Hω =ᵐ[volume] fun z => (W.ω z : ℂ) * h z := hHω
  have hc1 : ∀ k : ℕ, W.Chart (∑ j ∈ Finset.range k, cutN j Hω) (∑ j ∈ Finset.range k, cutN j h) := fun k => by
    induction k with
    | zero =>
      rw [Finset.sum_range_zero, Finset.sum_range_zero]
      exact SurfW.chart_zero
    | succ k ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      refine ih.add ?_
      show ⇑(cutN k Hω) =ᵐ[volume] _
      filter_upwards [cutN_ae k Hω, cutN_ae k h, hHω'] with z a b c
      rw [a, b, c]
      ring
  have hc2 : ∀ k : ℕ, ∃ U : L2H', (U : ℍ → ℂ) =ᵐ[volume] fun z => ((omG 1 z : ℝ) : ℂ) * (∑ j ∈ Finset.range k, cutN j h : L2H') z := fun k => by
    have hk : ∃ U : L2H', Wβ.Chart U (∑ j ∈ Finset.range k, cutN j h) := by
      induction k with
      | zero =>
        rw [Finset.sum_range_zero]
        exact ⟨0, SurfW.chart_zero⟩
      | succ k ih =>
        obtain ⟨U, hU⟩ := ih
        obtain ⟨V, hV, -⟩ := chart_of_shell (β := 1) zero_le_one (cutN_idem k h)
        have hV' : Wβ.Chart V (cutN k h) := by
          show ⇑V =ᵐ[volume] _
          filter_upwards [hV] with z hz
          rw [hz, hWβ]
        rw [Finset.sum_range_succ]
        exact ⟨U + V, hU.add hV'⟩
    obtain ⟨U, hU⟩ := hk
    refine ⟨U, ?_⟩
    have hU' : ⇑U =ᵐ[volume] fun z => (Wβ.ω z : ℂ) * (∑ j ∈ Finset.range k, cutN j h : L2H') z := hU
    filter_upwards [hU'] with z hz
    rw [hz, hWβ]
  have hGk : ∀ k : ℕ, ∃ Gk : L2H', W.Chart Gk (bE m σ ħ N s₁ ss (∑ j ∈ Finset.range k, cutN j h)) := fun k => by
    obtain ⟨Gk, hGk, -⟩ := hbE hW hF' hC hσ hσ1 hħ hħ1 N hs₁0 ss hssn (hc1 k)
    exact ⟨Gk, hGk⟩
  choose Gs hGs using hGk
  have hdiff : ∀ k, ‖Gs k - G‖ ≤ Ka * (√2 * facP (C4m C₁) σ ħ N ss.length 0) * ‖(∑ j ∈ Finset.range k, cutN j Hω) - Hω‖ := fun k => by
    obtain ⟨G₂, hG₂, nG₂⟩ := hbE hW hF' hC hσ hσ1 hħ hħ1 N hs₁0 ss hssn ((hc1 k).sub hHω)
    have hG₂' : W.Chart G₂ (bE m σ ħ N s₁ ss ((∑ j ∈ Finset.range k, cutN j h) - h)) := hG₂
    have e : bE m σ ħ N s₁ ss (∑ j ∈ Finset.range k, cutN j h)
        = bE m σ ħ N s₁ ss ((∑ j ∈ Finset.range k, cutN j h) - h) + bE m σ ħ N s₁ ss h := by
      rw [← bE_add hm hσ hσ1, sub_add_cancel]
    have hch : W.Chart (G₂ + G) (bE m σ ħ N s₁ ss (∑ j ∈ Finset.range k, cutN j h)) := by
      rw [e]
      exact hG₂'.add hG'
    have e2 : Gs k = G₂ + G := (hGs k).unique hch
    rw [e2, add_sub_cancel_right]
    exact nG₂
  have hlimH : Tendsto (fun k : ℕ => ∑ j ∈ Finset.range k, cutN j Hω) atTop (𝓝 Hω) := tendsto_sum_cutN Hω
  have hlimG : Tendsto Gs atTop (𝓝 G) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h0 : Tendsto (fun k : ℕ => Ka * (√2 * facP (C4m C₁) σ ħ N ss.length 0) * ‖(∑ j ∈ Finset.range k, cutN j Hω) - Hω‖) atTop (𝓝 0) := by
      have := (tendsto_iff_norm_sub_tendsto_zero.1 hlimH).const_mul (Ka * (√2 * facP (C4m C₁) σ ħ N ss.length 0))
      simpa using this
    exact squeeze_zero (fun k => norm_nonneg _) hdiff h0
  have hlimV : Tendsto (fun k => ‖W.surfV ħ s₁ (Gs k)‖) atTop (𝓝 ‖W.surfV ħ s₁ G‖) :=
    (((W.surfV ħ s₁).continuous.tendsto G).comp hlimG).norm
  have hlimR : Tendsto (fun k : ℕ => Real.sqrt W.C.toReal * ((1 + Bc) * 1 + cR) * (1 * (Bq * ‖∑ j ∈ Finset.range k, cutN j Hω‖))) atTop
      (𝓝 (Real.sqrt W.C.toReal * ((1 + Bc) * 1 + cR) * (1 * (Bq * ‖Hω‖)))) :=
    ((hlimH.norm.const_mul Bq).const_mul 1).const_mul _
  have hfinal := le_of_tendsto_of_tendsto' hlimV hlimR (fun k => by
    obtain ⟨U, hU⟩ := hc2 k
    exact hnice _ _ U (Gs k) (hc1 k) hU (hGs k))
  refine hfinal.trans (le_of_eq ?_)
  rw [hBq]
  ring

end assemble

end Qschubert
