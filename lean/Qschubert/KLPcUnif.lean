import Qschubert.KLPcAll

/-!
# Theorem `pc:main`, uniform in the group (part (ii))

The proofs of `pcmain_half_smooth` and `pcmain_big_smooth` choose `δ` before the group, and the group and base point enter the
constant `C` only through the periodization constant `critSup Γ x₀ = sup_z Σ_γ ω(γ z)^{-2}` of the critical weight
`ω = omP (3/4) (dist x₀ ·)`. The declarations below repeat those proofs with that constant replaced by an upper bound `Q`.

* `critSup`, `critSup_eq`: the periodization constant, equal to the constant of `surfW_printed`.
* `PcMainCD`: the estimate of `pc:main` on `0 < α ≤ A` with given constants `C, δ`.
* `pcmain_half_unif`, `pcmain_big_unif`, `pcMainCD_unif`: `δ` before `Q`, `C` after `Q`, then every group and base point.
* `pcmain_unif`: Theorem `pc:main` (ii) for every amplitude of finite printed norm.
-/

namespace Qschubert

open MeasureTheory
open scoped ENNReal MatrixGroups UpperHalfPlane

/-- The periodization constant of the critical weight `ω = X₀^{1/2} ℓ^{3/4}` based at `x₀`: `sup_z Σ_γ ω(γ z)^{-2}`. -/
noncomputable def critSup (Γ : Subgroup PGL(2, ℝ)) (x₀ : ℍ) : ENNReal :=
  ⨆ z : ℍ, ∑' γ : Γ, ENNReal.ofReal ((omP (3 / 4) (dist x₀ (γ • z)))⁻¹) ^ 2

lemma critSup_eq (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ] [Countable Γ] (x₀ : ℍ) :
    critSup Γ x₀ = (surfW_printed Γ x₀ (show (1 / 2 : ℝ) < 3 / 4 by norm_num)).C := rfl

/-- The estimate of Theorem `pc:main` on `0 < α ≤ A` for `C^∞` amplitudes, with the constants `C, δ`. -/
def PcMainCD (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ] (x₀ : ℍ) (β κ A C δ : ℝ) : Prop :=
  ∀ (ħ' α t : ℝ) (K N : ℕ) (g : SL(2, ℝ)) (a : ℍ → ℂ),
    0 < ħ' → ħ' ≤ 1 → 0 < α → α ≤ A → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ →
    0 ≤ t → t ≤ δ * Real.sqrt (α / ħ') → SmoothH a → prNormX x₀ α β a < ∞ →
    ∃ (hv : PerioConv Γ (initState g ħ' a)) (hw : PerioConv Γ (approxSolB g K ħ' t a)),
      approxErr Γ N ħ' t hv hw ≤ ENNReal.ofReal (ddBound C α ħ' t K N) * prNormX x₀ α β a

section half

open MeasureTheory Filter Topology Complex Set Physicslib4.Spectral Physicslib4.Spectral.Unbounded
open scoped ENNReal InnerProductSpace ComplexConjugate UpperHalfPlane MatrixGroups Pointwise

local notation "L2H'" => Lp ℂ 2 (volume : Measure UpperHalfPlane)

set_option maxHeartbeats 16000000 in
/-- **Theorem `pc:main` (ii) on `0 < α ≤ 1/2`, smooth amplitudes**: `δ` before `Q`, `C` after `Q`. -/
theorem pcmain_half_unif (β κ : ℝ) (hβ : 1 / 2 < β) (hκ : 0 < κ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ Q : ℝ, ∃ C : ℝ, 0 < C ∧
    ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ → ∀ x₀ : ℍ,
      critSup Γ x₀ ≤ ENNReal.ofReal Q → PcMainCD Γ x₀ β κ (1 / 2) C δ := by
  have hτ : (1 : ℝ) < Real.pi / 2 := by linarith [Real.pi_gt_three]
  obtain ⟨C₁, hC, hF'⟩ := lem_fc hτ
  have hc0 : (0 : ℝ) ≤ 3 / 4 := by norm_num
  have hc1 : (3 / 4 : ℝ) ≤ 1 := by norm_num
  have hc12 : (1 / 2 : ℝ) < 3 / 4 := by norm_num
  have hc2 : (3 / 4 : ℝ) < 1 := by norm_num
  have hm : (1 / 2 : ℝ) ≤ 3 := by norm_num
  have hml : 2 * ((1 : ℝ) + 1 / 2) ^ 2 < (3 : ℝ) ^ 2 := by norm_num
  have hl := log_two_pos'
  have hD : 0 < Real.exp (1 / 2) * (2 / Real.log 2) ^ (3 / 4 : ℝ) := by positivity
  have hDg : 0 ≤ 2 / Real.log 2 := by positivity
  have hkp : 0 < κ / 216 := by positivity
  obtain ⟨K₁, δ', hK₁, hδ', hcore⟩ := dd_core_pc hc0 hc1 hD hDg hm hml hkp hC hF'
  obtain ⟨Cd, hCd, hdata⟩ := data_factor hc12 hc2 hm
  have h6 : 0 < Real.sqrt 6 := Real.sqrt_pos.2 (by norm_num)
  refine ⟨δ' / Real.sqrt 6, by positivity, fun Q => ?_⟩
  set S₀ : ℝ := Real.sqrt (max Q 0) with hS₀
  have hS₀0 : 0 ≤ S₀ := Real.sqrt_nonneg _
  have hC₄1 : 1 ≤ C4m C₁ := one_le_C4m C₁
  set Cc : ℝ := (1 ^ 2 * C4m C₁ * 128) * (1 + 4 * C4m C₁ ^ 2 * (S₀ * K₁)) with hCc
  have hCc0 : 0 < Cc := by
    rw [hCc]
    have h2 : 0 < C4m C₁ := by linarith
    positivity
  have hη : 0 < β - 1 / 2 := by linarith
  set Cβ : ℝ := (1 + 1 / (β - 1 / 2)) / Real.log 2 * Real.exp β with hCβ
  have hCβ0 : 0 ≤ Cβ := by positivity
  set Lc : ℝ := (1 / Real.log 2) ^ (3 / 4 : ℝ) with hLc
  have hLc0 : 0 ≤ Lc := by positivity
  set Cf : ℝ := Lc * Cd * Cβ with hCf
  have hCf0 : 0 ≤ Cf := by positivity
  refine ⟨36 * Cc * max 1 Cf, by positivity, ?_⟩
  intro Γ _ _hOP x₀ hQ
  haveI : Countable Γ := countable_of_properlyDiscontinuous Γ
  unfold PcMainCD
  intro ħ α t K N g a hħ hħ1 hα hα1 hk hgx ht htδ hsm hfin
  -- the internal radius
  set σ : ℝ := α / 6 with hσd
  have hσ : 0 < σ := by rw [hσd]; positivity
  have hσ1 : σ ≤ 1 := by rw [hσd]; linarith
  have hσα : σ < α := by rw [hσd]; linarith
  have hση : α - σ ≤ 1 := by rw [hσd]; linarith
  have hσm : σ * 3 ≤ 1 / 2 := by rw [hσd]; linarith
  have hk' : κ / 216 * ħ ≤ σ ^ 3 := by
    have e : σ ^ 3 = α ^ 3 / 216 := by rw [hσd]; ring
    rw [e]
    have e2 : κ / 216 * ħ = (κ * ħ) / 216 := by ring
    rw [e2]
    linarith
  have htδ' : t ≤ δ' * Real.sqrt (σ / ħ) := by
    have e : σ / ħ = (α / ħ) / 6 := by rw [hσd]; ring
    rw [e, Real.sqrt_div (by positivity)]
    calc t ≤ δ' / Real.sqrt 6 * Real.sqrt (α / ħ) := htδ
      _ = _ := by ring
  -- the base point
  set G : SL(2, ℝ) := g * transH x₀ with hG
  have hGI : G • UpperHalfPlane.I = x₀ := by rw [hG, mul_smul, transH_smul_I, hgx]
  set p : PGL(2, ℝ) := Matrix.SpecialLinearGroup.toPGL G with hp
  -- the norm
  by_cases ha : MemLp a 2 (volume : Measure ℍ)
  swap
  · exfalso
    simp [prNormX, ha] at hfin
  by_cases hd : ha.toLp _ ∈ (expLambda α).domain
  swap
  · exfalso
    simp [prNormX, ha, hd] at hfin
  have hPR : prNormX x₀ α β a = eLpNorm (fun z => ((Real.exp (β * angleDx x₀ z) : ℝ) : ℂ)
      * (expLambda α ⟨ha.toLp _, hd⟩ : L2H') z) 2 (volume : Measure ℍ) := by
    simp only [prNormX, dif_pos ha, dif_pos hd]
  set f₀ : L2H' := expLambda α ⟨ha.toLp _, hd⟩ with hf₀
  have hg2 : MemLp (fun z => ((Real.exp (β * angleDx x₀ z) : ℝ) : ℂ) * f₀ z) 2 (volume : Measure ℍ) := by
    rw [hPR] at hfin
    exact hfin
  set Gp : L2H' := hg2.toLp _ with hGp
  have hPRn : prNormX x₀ α β a = ENNReal.ofReal ‖Gp‖ := by
    rw [hPR, hGp, Lp.norm_toLp, ENNReal.ofReal_toReal hg2.ne]
  set F : L2H' := isoU p f₀ with hF
  have hFae : ⇑F =ᵐ[volume] fun z => f₀ (p • z) := isoU_ae p f₀
  have hGpae : ⇑(isoU p Gp) =ᵐ[volume] fun z => ((Real.exp (β * angleDx UpperHalfPlane.I z) : ℝ) : ℂ) * F z := by
    have h1 := (measurePreserving_smul p (volume : Measure ℍ)).quasiMeasurePreserving.ae_eq_comp hg2.coeFn_toLp
    filter_upwards [isoU_ae p Gp, h1, hFae] with z e1 e2 e3
    rw [e1, e3]
    have e2' : (Gp : L2H') (p • z) = ((Real.exp (β * angleDx x₀ (p • z)) : ℝ) : ℂ) * f₀ (p • z) := e2
    rw [e2']
    have hpz : p • z = G • z := toPGL_smul G z
    have e4 : angleDx x₀ (p • z) = angleDx UpperHalfPlane.I z := by
      unfold angleDx
      rw [hpz, ← hGI, dist_smul]
    rw [e4]
  -- the weights
  set Γ' := conjS (Matrix.SpecialLinearGroup.toPGL G⁻¹) Γ with hΓ'
  set W : SurfW Γ' := surfW_printed Γ' UpperHalfPlane.I hc12 with hWd
  set Wγ : SurfW Γ' := surfW_cosh Γ' UpperHalfPlane.I hc12 with hWγd
  set Wβ : SurfW Γ' := surfW_cosh Γ' UpperHalfPlane.I (show (1 / 2 : ℝ) < 1 by norm_num) with hWβd
  have hWγ : ∀ z, Wγ.ω z = omG (3 / 4) z := fun z => rfl
  have hWβ : ∀ z, Wβ.ω z = omG 1 z := fun z => rfl
  have hW : CritW (3 / 4) (Real.exp (1 / 2) * (2 / Real.log 2) ^ (3 / 4 : ℝ)) W.ω := critW_printed hc0
  have hgr : ∀ s z, |W.mS s z| ≤ 2 / Real.log 2 * Real.exp |s| := fun s z => mS_printed_le hc12 hc1 UpperHalfPlane.I s z
  have hWω : ∀ z, W.ω z = omP (3 / 4) (dist UpperHalfPlane.I z) := fun z => rfl
  -- the chart of `F`
  obtain ⟨Fω, hFω, nFω⟩ : ∃ Fω : L2H', ((Fω : ℍ → ℂ) =ᵐ[volume] fun z => ((W.ω z : ℝ) : ℂ) * F z) ∧ ‖Fω‖ ≤ Cβ * ‖Gp‖ := by
    refine exists_chart_of_lint W.meas (fun z => (W.ω_pos z).le) F (by positivity) ?_
    calc ∫⁻ z : ℍ, (ENNReal.ofReal (W.ω z) * ‖F z‖ₑ) ^ 2 ≤ ∫⁻ z : ℍ, ENNReal.ofReal (Cβ ^ 2) * ‖(isoU p Gp) z‖ₑ ^ 2 := by
          refine lintegral_mono_ae ?_
          filter_upwards [hGpae] with z hz
          rw [hz, enorm_mul, ← ofReal_norm ((Real.exp (β * angleDx UpperHalfPlane.I z) : ℝ) : ℂ), Complex.norm_real,
            Real.norm_of_nonneg (Real.exp_pos _).le, ENNReal.ofReal_pow hCβ0, ← mul_pow, ← mul_assoc, ← ENNReal.ofReal_mul hCβ0]
          gcongr
          rw [hWω]
          exact omP_le_exp_angle hc1 hβ UpperHalfPlane.I z
      _ = ENNReal.ofReal ((Cβ * ‖Gp‖) ^ 2) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_enorm_sq_eq, LinearIsometryEquiv.norm_map,
            ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
  -- the data
  obtain ⟨e1, e2⟩ := hdata σ α hσ hσα hση hσm F
  set Ft : L2H' := specE.integral (GQ σ 3) (specE.integral (GW 0 (α - σ)) F) with hFt
  obtain ⟨Hω, hHω, nHω⟩ : ∃ Hω : L2H', ((Hω : ℍ → ℂ) =ᵐ[volume] fun z => ((W.ω z : ℝ) : ℂ) * Ft z) ∧ ‖Hω‖ ≤ Lc * Cd * ‖Fω‖ := by
    refine exists_chart_of_lint W.meas (fun z => (W.ω_pos z).le) Ft (by positivity) ?_
    have hF2 : ∫⁻ z : ℍ, ENNReal.ofReal (omC (3 / 4) (z : ℂ) ^ 2 * ‖F z‖ ^ 2) ≤ ENNReal.ofReal (‖Fω‖ ^ 2) := by
      rw [← lintegral_enorm_sq_eq]
      refine lintegral_mono_ae ?_
      filter_upwards [hFω] with z hz
      rw [hz, enorm_mul, ← ofReal_norm ((W.ω z : ℝ) : ℂ), Complex.norm_real, Real.norm_of_nonneg (W.ω_pos z).le,
        ← sq_ofReal_enorm (omC_nonneg _ z)]
      gcongr
      rw [hWω]
      exact omC_le_omP hc0 z
    calc ∫⁻ z : ℍ, (ENNReal.ofReal (W.ω z) * ‖Ft z‖ₑ) ^ 2
        ≤ ∫⁻ z : ℍ, ENNReal.ofReal (Lc ^ 2) * ENNReal.ofReal (omC (3 / 4) (z : ℂ) ^ 2 * ‖Ft z‖ ^ 2) := by
          refine lintegral_mono fun z => ?_
          rw [← sq_ofReal_enorm (omC_nonneg _ z), ENNReal.ofReal_pow hLc0, ← mul_pow, ← mul_assoc, ← ENNReal.ofReal_mul hLc0]
          gcongr
          rw [hWω]
          exact omP_le_omC hc0 z
      _ = ENNReal.ofReal (Lc ^ 2) * ∫⁻ z : ℍ, ENNReal.ofReal (omC (3 / 4) (z : ℂ) ^ 2 * ‖Ft z‖ ^ 2) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (Lc ^ 2) * (ENNReal.ofReal (Cd ^ 2) * ENNReal.ofReal (‖Fω‖ ^ 2)) := by
          gcongr
          exact e2.trans (by gcongr)
      _ = ENNReal.ofReal ((Lc * Cd * ‖Fω‖) ^ 2) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
  have hHωn : ‖Hω‖ ≤ Cf * ‖Gp‖ := by
    calc ‖Hω‖ ≤ Lc * Cd * ‖Fω‖ := nHω
      _ ≤ Lc * Cd * (Cβ * ‖Gp‖) := by gcongr
      _ = _ := by rw [hCf]; ring
  -- the amplitude
  set A : L2H' := vE 3 σ Ft 0 with hA
  have hA1 : A = isoU p (ha.toLp a) := by
    rw [e1, hF, integral_iso p (GW_mem 0 hα) f₀, hf₀, poisson_left_inv hα hd]
  have hAae : ⇑A =ᵐ[volume] fun w => a (G • w) := by
    have h1 := (measurePreserving_smul p (volume : Measure ℍ)).quasiMeasurePreserving.ae_eq_comp ha.coeFn_toLp
    rw [hA1]
    filter_upwards [isoU_ae p (ha.toLp a), h1] with z e3 e4
    rw [e3]
    have e4' : (ha.toLp a : L2H') (p • z) = a (p • z) := e4
    have hpz : p • z = G • z := toPGL_smul G z
    rw [e4', hpz]
  have hAW : AllWords A := vE_allWords hm hσ hσ1 Ft 0
  have hsG : SmoothH fun w => a (G • w) := smoothH_comp G hsm
  have hGa' : ∀ w : List Bool, ∃ G' : L2H', W.Chart G' (wordAct w A) := fun w =>
    word_chart_om hc0 hc1 hD hm hml hW hσ hσ1 w hHω
  choose Ga hGa using hGa'
  obtain ⟨hvG, hwG⟩ := perioConv_general (W := W) hsG hAae hAW hGa K ħ t
  have hE := approxErr_general (W := W) hsG hAae hAW hGa hħ.ne' K N t hvG hwG
  have hcore2 := hcore Γ' W Wγ Wβ hW hgr hWγ hWβ ħ σ t K N Ft Hω hHω hħ hħ1 hσ hσ1 hk' ht htδ'
  have hWC : W.C = (surfW_printed Γ x₀ hc12).C := by
    have e : Matrix.SpecialLinearGroup.toPGL G⁻¹ • x₀ = UpperHalfPlane.I := by
      rw [toPGL_smul, ← hGI, inv_smul_smul]
    show (⨆ z : ℍ, ∑' γ : conjS (Matrix.SpecialLinearGroup.toPGL G⁻¹) Γ,
        ENNReal.ofReal ((omP (3 / 4) (dist UpperHalfPlane.I (γ • z)))⁻¹) ^ 2)
      = ⨆ z : ℍ, ∑' γ : Γ, ENNReal.ofReal ((omP (3 / 4) (dist x₀ (γ • z)))⁻¹) ^ 2
    rw [← e]
    exact iSup_tsum_conj_move _ Γ x₀ (fun d => ENNReal.ofReal ((omP (3 / 4) d)⁻¹) ^ 2)
  rw [hWC] at hcore2
  have hS₁ : Real.sqrt (surfW_printed Γ x₀ hc12).C.toReal ≤ S₀ := by
    rw [hS₀]
    refine Real.sqrt_le_sqrt (ENNReal.toReal_le_of_le_ofReal (le_max_right _ _) ?_)
    exact (critSup_eq Γ x₀ ▸ hQ).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hCc₁ : (1 ^ 2 * C4m C₁ * 128) * (1 + 4 * C4m C₁ ^ 2 * (Real.sqrt (surfW_printed Γ x₀ hc12).C.toReal * K₁)) ≤ Cc := by
    rw [hCc]
    have h4 : 0 ≤ C4m C₁ := by linarith
    gcongr
  have hC₀ : 0 ≤ (1 ^ 2 * C4m C₁ * 128) * (1 + 4 * C4m C₁ ^ 2 * (Real.sqrt (surfW_printed Γ x₀ hc12).C.toReal * K₁)) := by
    have h4 : 0 ≤ C4m C₁ := by linarith
    positivity
  have hcore3 := hcore2.trans (mul_le_mul_of_nonneg_right
    (ddBound_mono (K := K) (N := N) hC₀ hCc₁ hσ hħ ht) (norm_nonneg Hω))
  have hfinal : ‖(Complex.I * (ħ : ℂ) / 2) ^ (K + 1) • simplexInt (K + 1) t fun ss => W.vS ħ (ss.headD 0) (polyAct (bP ħ N (ss.headD 0) ss) A)‖
      ≤ ddBound (36 * Cc * max 1 Cf) α ħ t K N * ‖Gp‖ := by
    refine hcore3.trans ?_
    have hdd0 : 0 ≤ ddBound Cc σ ħ t K N := ddBound_nonneg K N hCc0.le hσ hħ ht
    calc ddBound Cc σ ħ t K N * ‖Hω‖ ≤ ddBound Cc σ ħ t K N * (Cf * ‖Gp‖) := mul_le_mul_of_nonneg_left hHωn hdd0
      _ = (ddBound Cc (α / 6) ħ t K N * Cf) * ‖Gp‖ := by ring
      _ ≤ ddBound (36 * Cc * max 1 Cf) α ħ t K N * ‖Gp‖ :=
          mul_le_mul_of_nonneg_right (ddBound_scale hCc0.le hα hħ ht K N) (norm_nonneg _)
  have hc1' := norm_cstB x₀ ħ
  have hc0' := cstB_ne x₀ ħ
  have ei := initState_mul x₀ g ħ a
  have ea := approxSolB_mul x₀ g K ħ t a
  have hvG' : PerioConv Γ fun z => cstB x₀ ħ * initState g ħ a z := ei ▸ hvG
  have hwG' : PerioConv Γ fun z => cstB x₀ ħ * approxSolB g K ħ t a z := ea ▸ hwG
  have hv : PerioConv Γ (initState g ħ a) := perioConv_const hc0' hvG'
  have hw2 : PerioConv Γ (approxSolB g K ħ t a) := perioConv_const hc0' hwG'
  refine ⟨hv, hw2, ?_⟩
  rw [← approxErr_const hc1' hv hw2 hvG' hwG', ← approxErr_congr ei ea hvG hwG hvG' hwG', hE, hPRn]
  rw [← ofReal_norm, ← ENNReal.ofReal_mul (ddBound_nonneg K N (by positivity) hα hħ ht)]
  exact ENNReal.ofReal_le_ofReal hfinal

end half

section big

open MeasureTheory Filter Topology Complex Set Physicslib4.Spectral Physicslib4.Spectral.Unbounded UpperHalfPlane
open scoped ENNReal InnerProductSpace MatrixGroups Pointwise ComplexConjugate

local notation "L2H'" => Lp ℂ 2 (volume : Measure UpperHalfPlane)

set_option maxHeartbeats 16000000 in
/-- **Theorem `pc:main` (ii) on `1/2 < α ≤ A`, smooth amplitudes**: `δ` before `Q`, `C` after `Q`. -/
theorem pcmain_big_unif (β κ A : ℝ) (hβ : 1 / 2 < β) (hκ : 0 < κ) (hA : 1 / 2 ≤ A) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ Q : ℝ, ∃ C : ℝ, 0 < C ∧
    ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ → ∀ x₀ : ℍ,
      critSup Γ x₀ ≤ ENNReal.ofReal Q →
    ∀ (ħ' α t : ℝ) (K N : ℕ) (g : SL(2, ℝ)) (a : ℍ → ℂ),
      0 < ħ' → ħ' ≤ 1 → 1 / 2 < α → α ≤ A → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ →
      0 ≤ t → t ≤ δ * Real.sqrt (α / ħ') → SmoothH a → prNormX x₀ α β a < ∞ →
      ∃ (hv : PerioConv Γ (initState g ħ' a)) (hw : PerioConv Γ (approxSolB g K ħ' t a)),
        approxErr Γ N ħ' t hv hw ≤ ENNReal.ofReal (ddBound C α ħ' t K N) * prNormX x₀ α β a := by
  have hA0 : 0 < A := by linarith
  have hτ : (1 : ℝ) < Real.pi / 2 := by linarith [Real.pi_gt_three]
  obtain ⟨C₁, hC, hF'⟩ := lem_fc hτ
  have hc0 : (0 : ℝ) ≤ 3 / 4 := by norm_num
  have hc1 : (3 / 4 : ℝ) ≤ 1 := by norm_num
  have hc12 : (1 / 2 : ℝ) < 3 / 4 := by norm_num
  have hc2 : (3 / 4 : ℝ) < 1 := by norm_num
  have hm : (1 / 2 : ℝ) ≤ 3 := by norm_num
  have hml : 2 * ((1 : ℝ) + 1 / 2) ^ 2 < (3 : ℝ) ^ 2 := by norm_num
  have hl := log_two_pos'
  have hD : 0 < Real.exp (1 / 2) * (2 / Real.log 2) ^ (3 / 4 : ℝ) := by positivity
  have hDg : 0 ≤ 2 / Real.log 2 := by positivity
  have hkp : 0 < κ / (1728 * A ^ 3) := by positivity
  obtain ⟨K₁, δ', hK₁, hδ', hcore⟩ := dd_core_pc hc0 hc1 hD hDg hm hml hkp hC hF'
  obtain ⟨Cd, hCd, hdata⟩ := data_factor hc12 hc2 hm
  obtain ⟨Kp, hKp1, hpois⟩ := poisson_cw_all hc12 hc2
  have hKp0 : 0 < Kp := lt_of_lt_of_le one_pos hKp1
  set n₀ : ℕ := ⌈A⌉₊ with hn₀
  have h12A : 0 < Real.sqrt (12 * A) := Real.sqrt_pos.2 (by positivity)
  refine ⟨δ' / Real.sqrt (12 * A), by positivity, fun Q => ?_⟩
  set S₀ : ℝ := Real.sqrt (max Q 0) with hS₀
  have hS₀0 : 0 ≤ S₀ := Real.sqrt_nonneg _
  have hC₄1 : 1 ≤ C4m C₁ := one_le_C4m C₁
  set Cc : ℝ := (1 ^ 2 * C4m C₁ * 128) * (1 + 4 * C4m C₁ ^ 2 * (S₀ * K₁)) with hCc
  have hCc0 : 0 < Cc := by
    rw [hCc]
    have h2 : 0 < C4m C₁ := by linarith
    positivity
  have hη : 0 < β - 1 / 2 := by linarith
  set Cβ : ℝ := (1 + 1 / (β - 1 / 2)) / Real.log 2 * Real.exp β with hCβ
  have hCβ0 : 0 ≤ Cβ := by positivity
  set Lc : ℝ := (1 / Real.log 2) ^ (3 / 4 : ℝ) with hLc
  have hLc0 : 0 ≤ Lc := by positivity
  set Cf : ℝ := Lc * (Cd * Kp ^ n₀) * Cβ with hCf
  have hCf0 : 0 ≤ Cf := by positivity
  refine ⟨(12 * A) ^ 2 * Cc * max 1 Cf, by positivity, ?_⟩
  intro Γ _ _hOP x₀ hQ
  haveI : Countable Γ := countable_of_properlyDiscontinuous Γ
  intro ħ α t K N g a hħ hħ1 hα12 hαA hk hgx ht htδ hsm hfin
  have hα : 0 < α := by linarith
  -- the internal radius
  set σ : ℝ := 1 / 12 with hσd
  have hσ : 0 < σ := by rw [hσd]; norm_num
  have hσ1 : σ ≤ 1 := by rw [hσd]; norm_num
  have hσh : σ < 1 / 2 := by rw [hσd]; norm_num
  have hση : 1 / 2 - σ ≤ 1 := by rw [hσd]; norm_num
  have hσm : σ * 3 ≤ 1 / 2 := by rw [hσd]; norm_num
  have hk' : κ / (1728 * A ^ 3) * ħ ≤ σ ^ 3 := by
    have h3 : α ^ 3 ≤ A ^ 3 := pow_le_pow_left₀ hα.le hαA 3
    have hA3 : 0 < 1728 * A ^ 3 := by positivity
    have e : κ / (1728 * A ^ 3) * ħ = (κ * ħ) / (1728 * A ^ 3) := by ring
    rw [e, div_le_iff₀ hA3, hσd]
    have : κ * ħ ≤ A ^ 3 := hk.trans h3
    nlinarith
  have htδ' : t ≤ δ' * Real.sqrt (σ / ħ) := by
    have e : Real.sqrt (α / ħ) / Real.sqrt (12 * A) = Real.sqrt (α / ħ / (12 * A)) :=
      (Real.sqrt_div' _ (by positivity)).symm
    have hle : α / ħ / (12 * A) ≤ σ / ħ := by
      rw [hσd, div_div, div_le_div_iff₀ (by positivity) hħ]
      nlinarith
    calc t ≤ δ' / Real.sqrt (12 * A) * Real.sqrt (α / ħ) := htδ
      _ = δ' * (Real.sqrt (α / ħ) / Real.sqrt (12 * A)) := by ring
      _ = δ' * Real.sqrt (α / ħ / (12 * A)) := by rw [e]
      _ ≤ δ' * Real.sqrt (σ / ħ) := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hle) hδ'.le
  -- the base point
  set G : SL(2, ℝ) := g * transH x₀ with hG
  have hGI : G • UpperHalfPlane.I = x₀ := by rw [hG, mul_smul, transH_smul_I, hgx]
  set p : PGL(2, ℝ) := Matrix.SpecialLinearGroup.toPGL G with hp
  -- the norm
  by_cases ha : MemLp a 2 (volume : Measure ℍ)
  swap
  · exfalso
    simp [prNormX, ha] at hfin
  by_cases hd : ha.toLp _ ∈ (expLambda α).domain
  swap
  · exfalso
    simp [prNormX, ha, hd] at hfin
  have hPR : prNormX x₀ α β a = eLpNorm (fun z => ((Real.exp (β * angleDx x₀ z) : ℝ) : ℂ)
      * (expLambda α ⟨ha.toLp _, hd⟩ : L2H') z) 2 (volume : Measure ℍ) := by
    simp only [prNormX, dif_pos ha, dif_pos hd]
  set f₀ : L2H' := expLambda α ⟨ha.toLp _, hd⟩ with hf₀
  have hg2 : MemLp (fun z => ((Real.exp (β * angleDx x₀ z) : ℝ) : ℂ) * f₀ z) 2 (volume : Measure ℍ) := by
    rw [hPR] at hfin
    exact hfin
  set Gp : L2H' := hg2.toLp _ with hGp
  have hPRn : prNormX x₀ α β a = ENNReal.ofReal ‖Gp‖ := by
    rw [hPR, hGp, Lp.norm_toLp, ENNReal.ofReal_toReal hg2.ne]
  set F : L2H' := isoU p f₀ with hF
  have hFae : ⇑F =ᵐ[volume] fun z => f₀ (p • z) := isoU_ae p f₀
  have hGpae : ⇑(isoU p Gp) =ᵐ[volume] fun z => ((Real.exp (β * angleDx UpperHalfPlane.I z) : ℝ) : ℂ) * F z := by
    have h1 := (measurePreserving_smul p (volume : Measure ℍ)).quasiMeasurePreserving.ae_eq_comp hg2.coeFn_toLp
    filter_upwards [isoU_ae p Gp, h1, hFae] with z e1 e2 e3
    rw [e1, e3]
    have e2' : (Gp : L2H') (p • z) = ((Real.exp (β * angleDx x₀ (p • z)) : ℝ) : ℂ) * f₀ (p • z) := e2
    rw [e2']
    have hpz : p • z = G • z := toPGL_smul G z
    have e4 : angleDx x₀ (p • z) = angleDx UpperHalfPlane.I z := by
      unfold angleDx
      rw [hpz, ← hGI, dist_smul]
    rw [e4]
  -- the weights
  set Γ' := conjS (Matrix.SpecialLinearGroup.toPGL G⁻¹) Γ with hΓ'
  set W : SurfW Γ' := surfW_printed Γ' UpperHalfPlane.I hc12 with hWd
  set Wγ : SurfW Γ' := surfW_cosh Γ' UpperHalfPlane.I hc12 with hWγd
  set Wβ : SurfW Γ' := surfW_cosh Γ' UpperHalfPlane.I (show (1 / 2 : ℝ) < 1 by norm_num) with hWβd
  have hWγ : ∀ z, Wγ.ω z = omG (3 / 4) z := fun z => rfl
  have hWβ : ∀ z, Wβ.ω z = omG 1 z := fun z => rfl
  have hW : CritW (3 / 4) (Real.exp (1 / 2) * (2 / Real.log 2) ^ (3 / 4 : ℝ)) W.ω := critW_printed hc0
  have hgr : ∀ s z, |W.mS s z| ≤ 2 / Real.log 2 * Real.exp |s| := fun s z => mS_printed_le hc12 hc1 UpperHalfPlane.I s z
  have hWω : ∀ z, W.ω z = omP (3 / 4) (dist UpperHalfPlane.I z) := fun z => rfl
  -- the chart of `F`
  obtain ⟨Fω, hFω, nFω⟩ : ∃ Fω : L2H', ((Fω : ℍ → ℂ) =ᵐ[volume] fun z => ((W.ω z : ℝ) : ℂ) * F z) ∧ ‖Fω‖ ≤ Cβ * ‖Gp‖ := by
    refine exists_chart_of_lint W.meas (fun z => (W.ω_pos z).le) F (by positivity) ?_
    calc ∫⁻ z : ℍ, (ENNReal.ofReal (W.ω z) * ‖F z‖ₑ) ^ 2 ≤ ∫⁻ z : ℍ, ENNReal.ofReal (Cβ ^ 2) * ‖(isoU p Gp) z‖ₑ ^ 2 := by
          refine lintegral_mono_ae ?_
          filter_upwards [hGpae] with z hz
          rw [hz, enorm_mul, ← ofReal_norm ((Real.exp (β * angleDx UpperHalfPlane.I z) : ℝ) : ℂ), Complex.norm_real,
            Real.norm_of_nonneg (Real.exp_pos _).le, ENNReal.ofReal_pow hCβ0, ← mul_pow, ← mul_assoc, ← ENNReal.ofReal_mul hCβ0]
          gcongr
          rw [hWω]
          exact omP_le_exp_angle hc1 hβ UpperHalfPlane.I z
      _ = ENNReal.ofReal ((Cβ * ‖Gp‖) ^ 2) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_enorm_sq_eq, LinearIsometryEquiv.norm_map,
            ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
  -- the data: first `e^{-(α - 1/2)Λ}`, then the factorization at the radius `1/2`
  have hα' : 0 < α - 1 / 2 := by linarith
  have hαn : α - 1 / 2 ≤ (n₀ : ℝ) := by
    have := Nat.le_ceil A
    rw [hn₀]
    linarith
  set F₁ : L2H' := specE.integral (GW 0 (α - 1 / 2)) F with hF₁
  obtain ⟨e1, e2⟩ := hdata σ (1 / 2) hσ hσh hση hσm F₁
  set Ft : L2H' := specE.integral (GQ σ 3) (specE.integral (GW 0 (1 / 2 - σ)) F₁) with hFt
  obtain ⟨Hω, hHω, nHω⟩ : ∃ Hω : L2H', ((Hω : ℍ → ℂ) =ᵐ[volume] fun z => ((W.ω z : ℝ) : ℂ) * Ft z) ∧ ‖Hω‖ ≤ Lc * (Cd * Kp ^ n₀) * ‖Fω‖ := by
    refine exists_chart_of_lint W.meas (fun z => (W.ω_pos z).le) Ft (by positivity) ?_
    have hF2 : ∫⁻ z : ℍ, ENNReal.ofReal (omC (3 / 4) (z : ℂ) ^ 2 * ‖F z‖ ^ 2) ≤ ENNReal.ofReal (‖Fω‖ ^ 2) := by
      rw [← lintegral_enorm_sq_eq]
      refine lintegral_mono_ae ?_
      filter_upwards [hFω] with z hz
      rw [hz, enorm_mul, ← ofReal_norm ((W.ω z : ℝ) : ℂ), Complex.norm_real, Real.norm_of_nonneg (W.ω_pos z).le,
        ← sq_ofReal_enorm (omC_nonneg _ z)]
      gcongr
      rw [hWω]
      exact omC_le_omP hc0 z
    have hF12 : ∫⁻ z : ℍ, ENNReal.ofReal (omC (3 / 4) (z : ℂ) ^ 2 * ‖F₁ z‖ ^ 2)
        ≤ ENNReal.ofReal ((Kp ^ n₀) ^ 2) * ENNReal.ofReal (‖Fω‖ ^ 2) := by
      refine (hpois n₀ (α - 1 / 2) hα' hαn F).trans ?_
      gcongr
    calc ∫⁻ z : ℍ, (ENNReal.ofReal (W.ω z) * ‖Ft z‖ₑ) ^ 2
        ≤ ∫⁻ z : ℍ, ENNReal.ofReal (Lc ^ 2) * ENNReal.ofReal (omC (3 / 4) (z : ℂ) ^ 2 * ‖Ft z‖ ^ 2) := by
          refine lintegral_mono fun z => ?_
          rw [← sq_ofReal_enorm (omC_nonneg _ z), ENNReal.ofReal_pow hLc0, ← mul_pow, ← mul_assoc, ← ENNReal.ofReal_mul hLc0]
          gcongr
          rw [hWω]
          exact omP_le_omC hc0 z
      _ = ENNReal.ofReal (Lc ^ 2) * ∫⁻ z : ℍ, ENNReal.ofReal (omC (3 / 4) (z : ℂ) ^ 2 * ‖Ft z‖ ^ 2) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (Lc ^ 2) * (ENNReal.ofReal (Cd ^ 2) * (ENNReal.ofReal ((Kp ^ n₀) ^ 2) * ENNReal.ofReal (‖Fω‖ ^ 2))) := by
          gcongr
          exact e2.trans (by gcongr)
      _ = ENNReal.ofReal ((Lc * (Cd * Kp ^ n₀) * ‖Fω‖) ^ 2) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
  have hHωn : ‖Hω‖ ≤ Cf * ‖Gp‖ := by
    calc ‖Hω‖ ≤ Lc * (Cd * Kp ^ n₀) * ‖Fω‖ := nHω
      _ ≤ Lc * (Cd * Kp ^ n₀) * (Cβ * ‖Gp‖) := by gcongr
      _ = _ := by rw [hCf]; ring
  -- the amplitude
  set A' : L2H' := vE 3 σ Ft 0 with hA'
  have hA1 : A' = isoU p (ha.toLp a) := by
    have e3 : specE.integral (GW 0 (1 / 2)) F₁ = specE.integral (GW 0 α) F := by
      rw [hF₁, GW_comp (by norm_num) hα']
      congr 2
      ring
    rw [e1, e3, hF, integral_iso p (GW_mem 0 hα) f₀, hf₀, poisson_left_inv hα hd]
  have hAae : ⇑A' =ᵐ[volume] fun w => a (G • w) := by
    have h1 := (measurePreserving_smul p (volume : Measure ℍ)).quasiMeasurePreserving.ae_eq_comp ha.coeFn_toLp
    rw [hA1]
    filter_upwards [isoU_ae p (ha.toLp a), h1] with z e3 e4
    rw [e3]
    have e4' : (ha.toLp a : L2H') (p • z) = a (p • z) := e4
    have hpz : p • z = G • z := toPGL_smul G z
    rw [e4', hpz]
  have hAW : AllWords A' := vE_allWords hm hσ hσ1 Ft 0
  have hsG : SmoothH fun w => a (G • w) := smoothH_comp G hsm
  have hGa' : ∀ w : List Bool, ∃ G' : L2H', W.Chart G' (wordAct w A') := fun w =>
    word_chart_om hc0 hc1 hD hm hml hW hσ hσ1 w hHω
  choose Ga hGa using hGa'
  obtain ⟨hvG, hwG⟩ := perioConv_general (W := W) hsG hAae hAW hGa K ħ t
  have hE := approxErr_general (W := W) hsG hAae hAW hGa hħ.ne' K N t hvG hwG
  have hcore2 := hcore Γ' W Wγ Wβ hW hgr hWγ hWβ ħ σ t K N Ft Hω hHω hħ hħ1 hσ hσ1 hk' ht htδ'
  have hWC : W.C = (surfW_printed Γ x₀ hc12).C := by
    have e : Matrix.SpecialLinearGroup.toPGL G⁻¹ • x₀ = UpperHalfPlane.I := by
      rw [toPGL_smul, ← hGI, inv_smul_smul]
    show (⨆ z : ℍ, ∑' γ : conjS (Matrix.SpecialLinearGroup.toPGL G⁻¹) Γ,
        ENNReal.ofReal ((omP (3 / 4) (dist UpperHalfPlane.I (γ • z)))⁻¹) ^ 2)
      = ⨆ z : ℍ, ∑' γ : Γ, ENNReal.ofReal ((omP (3 / 4) (dist x₀ (γ • z)))⁻¹) ^ 2
    rw [← e]
    exact iSup_tsum_conj_move _ Γ x₀ (fun d => ENNReal.ofReal ((omP (3 / 4) d)⁻¹) ^ 2)
  rw [hWC] at hcore2
  have hS₁ : Real.sqrt (surfW_printed Γ x₀ hc12).C.toReal ≤ S₀ := by
    rw [hS₀]
    refine Real.sqrt_le_sqrt (ENNReal.toReal_le_of_le_ofReal (le_max_right _ _) ?_)
    exact (critSup_eq Γ x₀ ▸ hQ).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hCc₁ : (1 ^ 2 * C4m C₁ * 128) * (1 + 4 * C4m C₁ ^ 2 * (Real.sqrt (surfW_printed Γ x₀ hc12).C.toReal * K₁)) ≤ Cc := by
    rw [hCc]
    have h4 : 0 ≤ C4m C₁ := by linarith
    gcongr
  have hC₀ : 0 ≤ (1 ^ 2 * C4m C₁ * 128) * (1 + 4 * C4m C₁ ^ 2 * (Real.sqrt (surfW_printed Γ x₀ hc12).C.toReal * K₁)) := by
    have h4 : 0 ≤ C4m C₁ := by linarith
    positivity
  have hcore3 := hcore2.trans (mul_le_mul_of_nonneg_right
    (ddBound_mono (K := K) (N := N) hC₀ hCc₁ hσ hħ ht) (norm_nonneg Hω))
  have hfinal : ‖(Complex.I * (ħ : ℂ) / 2) ^ (K + 1) • simplexInt (K + 1) t fun ss => W.vS ħ (ss.headD 0) (polyAct (bP ħ N (ss.headD 0) ss) A')‖
      ≤ ddBound ((12 * A) ^ 2 * Cc * max 1 Cf) α ħ t K N * ‖Gp‖ := by
    refine hcore3.trans ?_
    have hdd0 : 0 ≤ ddBound Cc σ ħ t K N := ddBound_nonneg K N hCc0.le hσ hħ ht
    calc ddBound Cc σ ħ t K N * ‖Hω‖ ≤ ddBound Cc σ ħ t K N * (Cf * ‖Gp‖) := mul_le_mul_of_nonneg_left hHωn hdd0
      _ = (ddBound Cc (1 / 12) ħ t K N * Cf) * ‖Gp‖ := by rw [hσd]; ring
      _ ≤ ddBound ((12 * A) ^ 2 * Cc * max 1 Cf) α ħ t K N * ‖Gp‖ :=
          mul_le_mul_of_nonneg_right (ddBound_scale12 hCc0.le hα hαA hħ ht K N) (norm_nonneg _)
  have hc1' := norm_cstB x₀ ħ
  have hc0' := cstB_ne x₀ ħ
  have ei := initState_mul x₀ g ħ a
  have ea := approxSolB_mul x₀ g K ħ t a
  have hvG' : PerioConv Γ fun z => cstB x₀ ħ * initState g ħ a z := ei ▸ hvG
  have hwG' : PerioConv Γ fun z => cstB x₀ ħ * approxSolB g K ħ t a z := ea ▸ hwG
  have hv : PerioConv Γ (initState g ħ a) := perioConv_const hc0' hvG'
  have hw2 : PerioConv Γ (approxSolB g K ħ t a) := perioConv_const hc0' hwG'
  refine ⟨hv, hw2, ?_⟩
  rw [← approxErr_const hc1' hv hw2 hvG' hwG', ← approxErr_congr ei ea hvG hwG hvG' hwG', hE, hPRn]
  rw [← ofReal_norm, ← ENNReal.ofReal_mul (ddBound_nonneg K N (by positivity) hα hħ ht)]
  exact ENNReal.ofReal_le_ofReal hfinal

/-- **Theorem `pc:main` (ii) on `0 < α ≤ A`, smooth amplitudes.** -/
theorem pcMainCD_unif (β κ A : ℝ) (hβ : 1 / 2 < β) (hκ : 0 < κ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ Q : ℝ, ∃ C : ℝ, 0 < C ∧
    ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ → ∀ x₀ : ℍ,
      critSup Γ x₀ ≤ ENNReal.ofReal Q → PcMainCD Γ x₀ β κ A C δ := by
  obtain ⟨δa, hδa, ha⟩ := pcmain_half_unif β κ hβ hκ
  obtain ⟨δb, hδb, hb⟩ := pcmain_big_unif β κ (max A (1 / 2)) hβ hκ (le_max_right _ _)
  refine ⟨min δa δb, lt_min hδa hδb, fun Q => ?_⟩
  obtain ⟨Ca, hCa, ha'⟩ := ha Q
  obtain ⟨Cb, hCb, hb'⟩ := hb Q
  refine ⟨max Ca Cb, lt_max_of_lt_left hCa, ?_⟩
  intro Γ _ hOP x₀ hQ ħ α t K N g a hħ hħ1 hα hαA hk hg ht htδ hsm hfin
  have hs0 : 0 ≤ Real.sqrt (α / ħ) := Real.sqrt_nonneg _
  by_cases h : α ≤ 1 / 2
  · obtain ⟨hv, hw, hbd⟩ := ha' Γ hOP x₀ hQ ħ α t K N g a hħ hħ1 hα h hk hg ht
      (htδ.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hs0)) hsm hfin
    refine ⟨hv, hw, hbd.trans ?_⟩
    gcongr
    exact ddBound_mono (K := K) (N := N) hCa.le (le_max_left _ _) hα hħ ht
  · rw [not_le] at h
    obtain ⟨hv, hw, hbd⟩ := hb' Γ hOP x₀ hQ ħ α t K N g a hħ hħ1 h (hαA.trans (le_max_left _ _)) hk hg ht
      (htδ.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hs0)) hsm hfin
    refine ⟨hv, hw, hbd.trans ?_⟩
    gcongr
    exact ddBound_mono (K := K) (N := N) hCb.le (le_max_right _ _) hα hħ ht

/-- **Theorem `pc:main` (ii)**: for every amplitude of finite printed norm, `0 < α ≤ A`. `δ` depends only on `β, κ, A`; `C`
depends only on `β, κ, A` and an upper bound `Q` for the periodization constant `critSup Γ x₀`. -/
def Stmt_pcmain_unif : Prop :=
  ∀ (β κ A : ℝ), 1 / 2 < β → 0 < κ →
  ∃ δ : ℝ, 0 < δ ∧ ∀ Q : ℝ, ∃ C : ℝ, 0 < C ∧
  ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ → ∀ x₀ : ℍ,
    critSup Γ x₀ ≤ ENNReal.ofReal Q →
  ∀ (α : ℝ) (a : ℍ → ℂ), 0 < α → α ≤ A → prNormX x₀ α β a < ⊤ →
    ∃ a' : ℍ → ℂ, SmoothH a' ∧ a' =ᵐ[volume] a ∧
    ∀ (ħ' t : ℝ) (K N : ℕ) (g : SL(2, ℝ)),
      0 < ħ' → ħ' ≤ 1 → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ → 0 ≤ t → t ≤ δ * Real.sqrt (α / ħ') →
      ∃ (hv : PerioConv Γ (initState g ħ' a')) (hw : PerioConv Γ (approxSolB g K ħ' t a')),
        approxErr Γ N ħ' t hv hw ≤ ENNReal.ofReal (ddBound C α ħ' t K N) * prNormX x₀ α β a

theorem pcmain_unif : Stmt_pcmain_unif := by
  intro β κ A hβ hκ
  obtain ⟨δ, hδ, h0⟩ := pcMainCD_unif β κ A hβ hκ
  refine ⟨δ, hδ, fun Q => ?_⟩
  obtain ⟨C, hC, h1⟩ := h0 Q
  refine ⟨C, hC, fun Γ _ hOr x₀ hQ α a hα hαα hfin => ?_⟩
  have h := h1 Γ hOr x₀ hQ
  obtain ⟨a', hs, ha⟩ := lift1_pr_all hα hfin
  have e := prNormX_congr (x₀ := x₀) (α := α) (β := β) ha
  refine ⟨a', hs, ha, fun ħ t K N g hħ hħ1 hκc hg ht htδ => ?_⟩
  obtain ⟨hv, hw, hb⟩ := h ħ α t K N g a' hħ hħ1 hα hαα hκc hg ht htδ hs (e.symm ▸ hfin)
  exact ⟨hv, hw, e ▸ hb⟩

end big

end Qschubert
