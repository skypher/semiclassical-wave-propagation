import Qschubert.KLPcD2a

/-!
# The defect in the power weight, and shells

`chart_of_shell`, `block_of_chart`: a vector supported in one shell has a chart in the weight `X₀^β` of norm at most `e^{β(n+1)}` times its
norm, and a vector with chart `V` has `e^{βl} ‖1_l v‖ ≤ ‖V‖`.

`dvec_chart_beta`: for `h` with a chart in the weight `X₀^β`, the vector `V_ε(s) V_ε(s₁)* b'_h` has a chart there, of norm at most a constant
times the bound of `pc_wb_w`, and the defect `c (Δ_ε(s) - Δ(s)) V_ε(s) V_ε(s₁)* b'_h` has a chart there, of norm at most `A₁ ε⁻³` times
the bound of `pc_wb_w` at two extra letters. The argument is that of `vS_bound`, on the amplitude `e^{-σΛ_m} h`.
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set Physicslib4.Spectral Physicslib4.Spectral.Unbounded
open scoped ENNReal InnerProductSpace ComplexConjugate UpperHalfPlane MatrixGroups Pointwise

local notation "L2H'" => Lp ℂ 2 (volume : Measure UpperHalfPlane)

lemma omG_eq_exp (β : ℝ) (z : ℍ) : omG β z = Real.exp (β * psiF (z : ℂ)) := by
  have hc : 0 < coshD UpperHalfPlane.I z := Real.cosh_pos _
  unfold omG psiF
  rw [hF_eq_inv_coshD, Real.log_inv, neg_neg, Real.rpow_def_of_pos hc, mul_comm]

lemma omG_shell {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {z : ℍ} (h : z ∈ shell n) :
    Real.exp (β * n) ≤ omG β z ∧ omG β z ≤ Real.exp (β * (n + 1)) := by
  obtain ⟨h1, h2⟩ := mem_shell h
  rw [omG_eq_exp]
  exact ⟨Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left h1 hβ), Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left h2.le hβ)⟩

/-- A vector supported in the shell `n` has a chart in the weight `X₀^β`. -/
lemma chart_of_shell {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {u : L2H'} (hu : cutN n u = u) :
    ∃ U : L2H', ((U : ℍ → ℂ) =ᵐ[volume] fun z => ((omG β z : ℝ) : ℂ) * u z) ∧ ‖U‖ ≤ Real.exp (β * (n + 1)) * ‖u‖ := by
  set c := Real.exp (β * ((n : ℝ) + 1)) with hc
  have hc0 : 0 < c := Real.exp_pos _
  refine exists_chart_of_lint (measurable_omG β) (fun z => (Real.rpow_pos_of_pos (Real.cosh_pos _) _).le) u (by positivity) ?_
  have hsupp := cutN_supp n u
  rw [hu] at hsupp
  have hle : ∫⁻ z : ℍ, (ENNReal.ofReal (omG β z) * ‖u z‖ₑ) ^ 2 ≤ ∫⁻ z : ℍ, ENNReal.ofReal (c ^ 2) * ‖u z‖ₑ ^ 2 := by
    refine lintegral_mono_ae ?_
    filter_upwards [hsupp] with z hz
    by_cases h0 : u z = 0
    · simp [h0]
    · have h1 := (omG_shell hβ (hz h0)).2
      have hp : 0 ≤ omG β z := (Real.rpow_pos_of_pos (Real.cosh_pos _) _).le
      rw [mul_pow, ← ENNReal.ofReal_pow hp]
      gcongr
  refine hle.trans (le_of_eq ?_)
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_enorm_sq_eq, ← ENNReal.ofReal_mul (by positivity), mul_pow]

/-- The shell norms are below the chart. -/
lemma block_of_chart {β : ℝ} (hβ : 0 ≤ β) {v V : L2H'} (hV : (V : ℍ → ℂ) =ᵐ[volume] fun z => ((omG β z : ℝ) : ℂ) * v z) (l : ℕ) :
    Real.exp (β * l) * ‖cutN l v‖ ≤ ‖V‖ := by
  set c := Real.exp (β * (l : ℝ)) with hc
  have hc0 : 0 < c := Real.exp_pos _
  have e : c * ‖cutN l v‖ = ‖(c : ℂ) • cutN l v‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hc0.le]
  rw [e]
  refine Lp.norm_le_norm_of_ae_le ?_
  filter_upwards [hV, cutN_ae l v, Lp.coeFn_smul (c : ℂ) (cutN l v)] with z h1 h2 h3
  have hp : 0 ≤ omG β z := (Real.rpow_pos_of_pos (Real.cosh_pos _) _).le
  rw [h3, Pi.smul_apply, h2, h1, smul_eq_mul, norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg hc0.le, Real.norm_of_nonneg hp]
  by_cases hm : z ∈ shell l
  · have h4 : chiN l z = 1 := by simp [chiN, hm]
    rw [h4, norm_one, one_mul]
    exact mul_le_mul_of_nonneg_right (omG_shell hβ hm).1 (norm_nonneg _)
  · have h4 : chiN l z = 0 := by simp [chiN, hm]
    rw [h4, norm_zero, zero_mul, mul_zero]
    exact mul_nonneg hp (norm_nonneg _)

section defect

variable {β m : ℝ} (hβ0 : 0 ≤ β) (hm : 1 / 2 ≤ m) (hml : 2 * (β + 1 / 2) ^ 2 < m ^ 2)
include hβ0 hm hml

set_option maxHeartbeats 4000000 in
/-- **The defect in the weight `X₀^β`.** -/
theorem dvec_chart_beta : ∃ A₀ A₁ : ℝ, 0 ≤ A₀ ∧ 0 ≤ A₁ ∧ ∀ (Γ' : Subgroup PGL(2, ℝ)) [Countable Γ'] [ProperlyDiscontinuousSMul Γ' ℍ] (Wβ : SurfW Γ'),
    (∀ z, Wβ.ω z = omG β z) → ∀ {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {ħ : ℝ} (_ : 0 < ħ) (_ : ħ ≤ 1)
      (N : ℕ) {s₁ s : ℝ} (_ : 0 ≤ s₁), s ∈ Icc 0 s₁ → ħ * s₁ ≤ ε → ∀ (ss : List ℝ), (∀ r ∈ ss, 0 ≤ r) →
      ∀ {h H : L2H'}, ((H : ℍ → ℂ) =ᵐ[volume] fun z => ((omG β z : ℝ) : ℂ) * h z) →
      (∃ P : L2H', ((P : ℍ → ℂ) =ᵐ[volume] fun z => ((omG β z : ℝ) : ℂ)
          * (gflow stdP hε hε1 ħ s₁ ⟨bE m σ ħ N s₁ ss h, bE_mem hm hσ hσ1 ħ N s₁ ss h⟩ s : L2H') z)
        ∧ ‖P‖ ≤ A₀ * (C4 (K3p β) ^ (N + ss.length) * ((2 * N).factorial : ℝ) * ((2 * ss.length).factorial : ℝ)
          * (σ⁻¹) ^ (2 * ss.length) * ((σ * ħ)⁻¹) ^ (2 * N) * ‖H‖))
      ∧ ∃ X : L2H', ((X : ℍ → ℂ) =ᵐ[volume] fun z => ((omG β z : ℝ) : ℂ)
          * dvec stdP hε hε1 ħ s₁ ⟨bE m σ ħ N s₁ ss h, bE_mem hm hσ hσ1 ħ N s₁ ss h⟩ s z)
        ∧ ‖X‖ ≤ A₁ * (ε⁻¹) ^ 3 * (C4 (K3p β) ^ (N + ss.length + 2) * ((2 * N).factorial : ℝ) * ((2 + 2 * ss.length).factorial : ℝ)
          * (σ⁻¹) ^ (2 + 2 * ss.length) * ((σ * ħ)⁻¹) ^ (2 * N) * ‖H‖) := by
  obtain ⟨Gcβ, hGcβ0, hGcβ⟩ := ws0_cosh stdP hβ0
  obtain ⟨Qβ, hQβ0, hQβ⟩ := wbd_ops stdP hβ0
  set B : ℝ := √2 with hBd
  have hB0 : 0 ≤ B := Real.sqrt_nonneg _
  set A₁ : ℝ := (3 * Qβ ^ 2 * Real.exp (Gcβ / 2) + 3) * (1 + B) with hA₁
  have hA₁0 : 0 ≤ A₁ := by positivity
  refine ⟨Real.exp (Gcβ / 2) * B, A₁, by positivity, hA₁0, fun Γ' _ _ Wβ hWβ {σ} hσ hσ1 {ε} hε hε1 {ħ} hħ hħ1 N {s₁ s} hs₁0 hs hwin ss hssn {h H} hH => ?_⟩
  set E := ε⁻¹ with hE
  have hE1 : 1 ≤ E := (one_le_inv₀ hε).2 hε1
  have hE0 : 0 < E := by linarith
  have hεE : ε * E = 1 := mul_inv_cancel₀ hε.ne'
  have hEw : ħ * E * s₁ ≤ 1 := by
    calc ħ * E * s₁ = (ħ * s₁) * E := by ring
      _ ≤ ε * E := by gcongr
      _ = 1 := hεE
  set L := ss.length with hLd
  set b'v := bE m σ ħ N s₁ ss h with hb'v
  have hwb : ∀ (J : List Bool) (n : ℕ), J.length ≤ n → WordDom J b'v ∧ ∃ G : L2H',
      (⇑G =ᵐ[volume] fun z => ((omG β z : ℝ) : ℂ) * wordAct J b'v z) ∧
      ‖G‖ ≤ B * C4 (K3p β) ^ (N + L + n) * ((2 * N).factorial : ℝ) * ((n + 2 * L).factorial : ℝ) * (σ⁻¹) ^ (n + 2 * L) * ((σ * ħ)⁻¹) ^ (2 * N) * ‖H‖ :=
    fun J n hJ => pc_wb_w hβ0 hm hml hσ hσ1 hH hħ hħ1 N hs₁0 ss hssn J hJ
  have hA : AllWords b'v := bE_allWords hm hσ hσ1 ħ N s₁ ss h
  have hbm : b'v ∈ negLapH.domain := bE_mem hm hσ hσ1 ħ N s₁ ss h
  set b' : negLapH.domain := ⟨b'v, hbm⟩ with hb'
  set FN := ‖H‖ with hFN
  have hFN0 : 0 ≤ FN := norm_nonneg _
  set C₄ := C4 (K3p β) with hC₄
  have hC₄1 : 1 ≤ C₄ := by
    rw [hC₄]; unfold C4
    have := one_le_K3p hβ0
    nlinarith [sq_nonneg (K3p β)]
  have hC₄0 : 0 ≤ C₄ := by linarith
  have hAi0 : 0 < σ⁻¹ := inv_pos.2 hσ
  have hAi1 : 1 ≤ σ⁻¹ := (one_le_inv₀ hσ).2 hσ1
  obtain ⟨-, B₀, hB₀, nB₀⟩ := hwb [] 0 le_rfl
  obtain ⟨-, BX, hBX, nBX⟩ := hwb [true] 2 (by simp)
  obtain ⟨-, BY, hBY, nBY⟩ := hwb [false] 2 (by simp)
  obtain ⟨-, BXX, hBXX, nBXX⟩ := hwb [true, true] 2 (by simp)
  obtain ⟨-, BYY, hBYY, nBYY⟩ := hwb [false, false] 2 (by simp)
  have toChartβ : ∀ {G v : L2H'}, (⇑G =ᵐ[volume] fun z => ((omG β z : ℝ) : ℂ) * v z) → Wβ.Chart G v := fun {G v} h => by
    show ⇑G =ᵐ[volume] _
    filter_upwards [h] with z hz
    rw [hz, hWβ]
  have hIβ : Wβ.SurfIn b' B₀ BX BY BXX BYY :=
    surfIn_of_words Wβ b' hA (toChartβ hB₀) (toChartβ hBX) (toChartβ hBY) (toChartβ hBXX) (toChartβ hBYY)
  obtain ⟨hJβ, hBxβ, hByβ, -, hXXβ, hYYβ⟩ := hQβ hε hε1
  have hEp : 0 ≤ ε⁻¹ := (inv_pos.2 hε).le
  let Oβ : WOps (stdP.cutoffEps hε) hβ0 := ⟨Qβ, ε⁻¹ * Qβ, ε⁻¹ * ε⁻¹ * Qβ, hQβ0, by positivity, by positivity, hJβ, hBxβ, hByβ, hXXβ, hYYβ⟩
  set Bd₁ : ℝ := C₄ ^ (N + L + 2) * ((2 * N).factorial : ℝ) * ((2 + 2 * L).factorial : ℝ) * (σ⁻¹) ^ (2 + 2 * L) * ((σ * ħ)⁻¹) ^ (2 * N) * FN with hBd₁
  have hAh : 0 ≤ ((σ * ħ)⁻¹) ^ (2 * N) := by positivity
  have hBd₁0 : 0 ≤ Bd₁ := by positivity
  have hfac : ((2 * L).factorial : ℝ) ≤ ((2 + 2 * L).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega)
  have hCp : C₄ ^ (N + L) ≤ C₄ ^ (N + L + 2) := pow_le_pow_right₀ hC₄1 (by omega)
  have hAp : (σ⁻¹) ^ (2 * L) ≤ (σ⁻¹) ^ (2 + 2 * L) := pow_le_pow_right₀ hAi1 (by omega)
  have hZ : C₄ ^ (N + L) * ((2 * N).factorial : ℝ) * ((2 * L).factorial : ℝ) * (σ⁻¹) ^ (2 * L) * ((σ * ħ)⁻¹) ^ (2 * N) * FN ≤ Bd₁ := by
    rw [hBd₁]
    have h2N : (0 : ℝ) ≤ ((2 * N).factorial : ℝ) := by positivity
    gcongr
  have hBz : ‖B₀‖ ≤ B * Bd₁ := by
    refine nB₀.trans (le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left hZ hB0))
    simp only [Nat.add_zero, Nat.zero_add]
    ring
  have eBd : B * C₄ ^ (N + L + 2) * ((2 * N).factorial : ℝ) * ((2 + 2 * L).factorial : ℝ) * (σ⁻¹) ^ (2 + 2 * L) * ((σ * ħ)⁻¹) ^ (2 * N) * FN = B * Bd₁ := by
    rw [hBd₁]; ring
  rw [eBd] at nBX nBY nBXX nBYY
  set G₂ := Real.exp (Gcβ / 2) with hG₂
  have hG₂0 : 0 < G₂ := Real.exp_pos _
  set Gm := G₂ * ((1 + B) * Bd₁) with hGm
  have hGm0 : 0 ≤ Gm := by positivity
  have hBB : B * Bd₁ ≤ (1 + B) * Bd₁ := mul_le_mul_of_nonneg_right (by linarith) hBd₁0
  have hexpbd : ∀ {c r : ℝ}, 0 ≤ c → r ∈ Icc 0 s₁ → Real.exp (|ħ| * (ε⁻¹ * c) * |r - s₁| / 2) ≤ Real.exp (c / 2) := fun {c r} hc hr => by
    apply Real.exp_le_exp.2
    have h1 : |r - s₁| ≤ s₁ := by
      rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
    rw [abs_of_pos hħ]
    have h2 : ħ * E * |r - s₁| ≤ 1 := by
      calc ħ * E * |r - s₁| ≤ ħ * E * s₁ := by gcongr
        _ ≤ 1 := hEw
    have h3 : ħ * (E * c) * |r - s₁| / 2 = (ħ * E * |r - s₁|) * c / 2 := by ring
    show ħ * (E * c) * |r - s₁| / 2 ≤ c / 2
    rw [h3]
    nlinarith
  have hrG : ∀ r ∈ Icc 0 s₁, ‖Oβ.pathG ħ s₁ B₀ r‖ ≤ Gm := fun r hr => by
    refine (norm_pathG_le Wβ stdP hε hWβ Oβ ħ s₁ hIβ hGcβ hε1 hs₁0 hr.1).trans ?_
    exact mul_le_mul (hexpbd hGcβ0 hr) (hBz.trans hBB) (norm_nonneg _) hG₂0.le
  have hE3 : 1 ≤ E ^ 3 := one_le_pow₀ hE1
  have hE23 : E ^ 2 ≤ E ^ 3 := pow_le_pow_right₀ hE1 (by norm_num)
  have hX : ‖Oβ.xInt ħ s₁ B₀ BY BXX BYY s‖ ≤ A₁ * E ^ 3 * Bd₁ := by
    have hsub : uIcc s₁ s ⊆ Icc 0 s₁ := by
      rw [uIcc_of_ge hs.2]
      exact Icc_subset_Icc_left hs.1
    have hHa := norm_pathH_le Oβ ħ s₁ B₀ (Gm := Gm) hs₁0 hs.1 (fun r hr => hrG r (hsub hr))
    set Q := Qβ with hQ
    have hQc : Oβ.Qc = E * E * Q := rfl
    have hQb : Oβ.Qb = E * Q := rfl
    have hQa : Oβ.Qa = Q := rfl
    have hHm : ‖Oβ.pathH ħ s₁ B₀ s‖ ≤ E * Q * Gm := by
      refine hHa.trans ?_
      rw [hQc, abs_of_pos hħ]
      have h1 : |s - s₁| ≤ s₁ := by
        rw [abs_le]; constructor <;> linarith [hs.1, hs.2]
      have h2 : ħ * |s - s₁| ≤ ε := (mul_le_mul_of_nonneg_left h1 hħ.le).trans hwin
      have hQp : 0 ≤ E * E * Q * Gm := by positivity
      calc ħ / 2 * (2 * (E * E * Q) * Gm) * |s - s₁| = (ħ * |s - s₁|) * (E * E * Q * Gm) := by ring
        _ ≤ ε * (E * E * Q * Gm) := by gcongr
        _ = (ε * E) * (E * Q * Gm) := by ring
        _ = E * Q * Gm := by rw [hεE, one_mul]
    have hx := norm_xInt_le Oβ ħ s₁ B₀ hs.1 (hrG s hs) hHm (GY₀ := BY) (GXX₀ := BXX) (GYY₀ := BYY)
    refine hx.trans ?_
    rw [hQa, hQc, hQb, abs_of_pos hħ]
    have hN : ‖BXX‖ + ‖BYY‖ + ‖BY‖ ≤ 3 * (B * Bd₁) := by linarith
    have hN0 : 0 ≤ ‖BXX‖ + ‖BYY‖ + ‖BY‖ := by positivity
    set P := Q ^ 2 * Gm with hP
    have hP0 : 0 ≤ P := by positivity
    have e1 : Q * (2 * (E * E * Q) * Gm) + (‖BXX‖ + ‖BYY‖ + ‖BY‖) + (2 * (E * E * Q) + 2 * (E * Q)) * (E * Q * Gm)
        = 4 * (E ^ 2 * P) + 2 * (E ^ 3 * P) + (‖BXX‖ + ‖BYY‖ + ‖BY‖) := by rw [hP]; ring
    rw [e1]
    have h1 : 4 * (E ^ 2 * P) ≤ 4 * (E ^ 3 * P) := by gcongr
    have hin : 0 ≤ 4 * (E ^ 2 * P) + 2 * (E ^ 3 * P) + (‖BXX‖ + ‖BYY‖ + ‖BY‖) := by positivity
    have h2 : ħ / 2 * (4 * (E ^ 2 * P) + 2 * (E ^ 3 * P) + (‖BXX‖ + ‖BYY‖ + ‖BY‖)) ≤ 1 / 2 * (4 * (E ^ 2 * P) + 2 * (E ^ 3 * P) + (‖BXX‖ + ‖BYY‖ + ‖BY‖)) :=
      mul_le_mul_of_nonneg_right (by linarith) hin
    refine h2.trans ?_
    have h3 : (3 / 2) * (B * Bd₁) ≤ 3 * (1 + B) * E ^ 3 * Bd₁ := by
      have hBBd : 0 ≤ B * Bd₁ := by positivity
      have h4 : (3 / 2) * (B * Bd₁) ≤ 3 * ((1 + B) * Bd₁) := by linarith
      have h5 : 3 * ((1 + B) * Bd₁) ≤ 3 * (1 + B) * E ^ 3 * Bd₁ := by
        have h6 : 0 ≤ 3 * ((1 + B) * Bd₁) := by positivity
        calc 3 * ((1 + B) * Bd₁) = 1 * (3 * ((1 + B) * Bd₁)) := by ring
          _ ≤ E ^ 3 * (3 * ((1 + B) * Bd₁)) := by gcongr
          _ = _ := by ring
      linarith
    have e2 : A₁ * E ^ 3 * Bd₁ = 3 * (E ^ 3 * P) + 3 * (1 + B) * E ^ 3 * Bd₁ := by
      rw [hA₁, hP, hGm]; ring
    rw [e2]
    linarith
  have hchart := xInt_chart Wβ stdP hε hWβ Oβ ħ s₁ hIβ s
  have hgg : Oβ.pathD stdP hε ħ s₁ (G₀ := B₀) b' s = gflow stdP hε hε1 ħ s₁ b' s :=
    Subtype.ext (pathD_flow Wβ stdP hε hWβ Oβ ħ s₁ hIβ s)
  rw [hgg] at hchart
  have hcP : Wβ.Chart (Oβ.pathG ħ s₁ B₀ s) (Oβ.pathD stdP hε ħ s₁ (G₀ := B₀) b' s : L2H') := (pathD_surfIn Wβ stdP hε hWβ Oβ ħ s₁ hIβ s).cG
  rw [hgg] at hcP
  have hPn : ‖Oβ.pathG ħ s₁ B₀ s‖ ≤ G₂ * B * (C₄ ^ (N + L) * ((2 * N).factorial : ℝ) * ((2 * L).factorial : ℝ) * (σ⁻¹) ^ (2 * L)
      * ((σ * ħ)⁻¹) ^ (2 * N) * FN) := by
    refine (norm_pathG_le Wβ stdP hε hWβ Oβ ħ s₁ hIβ hGcβ hε1 hs₁0 hs.1).trans ?_
    have h1 : ‖B₀‖ ≤ B * (C₄ ^ (N + L) * ((2 * N).factorial : ℝ) * ((2 * L).factorial : ℝ) * (σ⁻¹) ^ (2 * L) * ((σ * ħ)⁻¹) ^ (2 * N) * FN) := by
      refine nB₀.trans (le_of_eq ?_)
      simp only [Nat.add_zero, Nat.zero_add]
      ring
    calc Real.exp (|ħ| * (ε⁻¹ * Gcβ) * |s - s₁| / 2) * ‖B₀‖
        ≤ G₂ * (B * (C₄ ^ (N + L) * ((2 * N).factorial : ℝ) * ((2 * L).factorial : ℝ) * (σ⁻¹) ^ (2 * L) * ((σ * ħ)⁻¹) ^ (2 * N) * FN)) :=
          mul_le_mul (hexpbd hGcβ0 hs) h1 (norm_nonneg _) hG₂0.le
      _ = _ := by ring
  refine ⟨⟨Oβ.pathG ħ s₁ B₀ s, ?_, hPn⟩, Oβ.xInt ħ s₁ B₀ BY BXX BYY s, ?_, hX⟩
  · have hc' : ⇑(Oβ.pathG ħ s₁ B₀ s) =ᵐ[volume] _ := hcP
    filter_upwards [hc'] with z hz
    rw [hz, hWβ]
  · have hc' : ⇑(Oβ.xInt ħ s₁ B₀ BY BXX BYY s) =ᵐ[volume] _ := hchart
    filter_upwards [hc'] with z hz
    rw [hz, hWβ]
    rfl

end defect

end Qschubert
