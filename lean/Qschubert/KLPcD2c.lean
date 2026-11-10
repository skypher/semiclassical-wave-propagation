import Qschubert.KLPcD2b
import Qschubert.KLPcSchur

/-!
# The transfer lemma for charts, and the maps of the proof of `pc:main`

`CritW c D om`: the weight `om` is comparable to `e^{ψ/2}(1+ψ)^c` on the shells. `transfer_chart`: Lemma S in terms of charts. Then, for
`β = 1` and a weight of this type: the charts of `b'_f` (`bE_chart_om`), of the words of `e^{-σΛ_m} f` (`word_chart_om`), of
`V_ε(s) V_ε(s₁)* b'_f` (`flow_chart_om`) and of the defect (`dvec_chart_om`), for `f` with a chart in the weight `om`.
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set Physicslib4.Spectral Physicslib4.Spectral.Unbounded
open scoped ENNReal InnerProductSpace ComplexConjugate UpperHalfPlane MatrixGroups Pointwise

local notation "L2H'" => Lp ℂ 2 (volume : Measure UpperHalfPlane)

lemma sq_ofReal_enorm {a : ℝ} (ha : 0 ≤ a) (x : ℂ) : (ENNReal.ofReal a * ‖x‖ₑ) ^ 2 = ENNReal.ofReal (a ^ 2 * ‖x‖ ^ 2) := by
  rw [← ofReal_norm, ← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_pow (mul_nonneg ha (norm_nonneg _)), mul_pow]

lemma rpow_split_self {x t : ℝ} (hx : 0 ≤ x) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : x ^ (1 - t) * x ^ t = x := by
  rw [← Real.rpow_add_of_nonneg hx (by linarith) ht0, sub_add_cancel, Real.rpow_one]

/-- A weight comparable to `e^{ψ/2}(1+ψ)^c` on the shells. -/
structure CritW (c D : ℝ) (om : ℍ → ℝ) : Prop where
  meas : Measurable om
  nonneg : ∀ z, 0 ≤ om z
  lo : ∀ (n : ℕ) (z : ℍ), z ∈ shell n → Real.exp ((n : ℝ) / 2) * (1 + (n : ℝ)) ^ c ≤ om z
  hi : ∀ (l : ℕ) (z : ℍ), z ∈ shell l → om z ≤ D * Real.exp ((l : ℝ) / 2) * (1 + (l : ℝ)) ^ c

/-- **The transfer lemma for charts.** -/
theorem transfer_chart {β c D : ℝ} (hβ : 1 / 2 < β) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hD : 0 < D) :
    ∃ K : ℝ, 0 < K ∧ ∀ {om : ℍ → ℝ}, CritW c D om →
      ∀ (T : L2H' → L2H'), (∀ u v, T (u + v) = T u + T v) → ∀ {M₀ M₁ : ℝ}, 0 ≤ M₀ → M₀ ≤ M₁ → (∀ u, ‖T u‖ ≤ M₀ * ‖u‖) →
      (∀ (u U : L2H'), ((U : ℍ → ℂ) =ᵐ[volume] fun z => ((omG β z : ℝ) : ℂ) * u z) →
        ∃ X : L2H', ((X : ℍ → ℂ) =ᵐ[volume] fun z => ((omG β z : ℝ) : ℂ) * T u z) ∧ ‖X‖ ≤ M₁ * ‖U‖) →
      ∀ {f F : L2H'}, ((F : ℍ → ℂ) =ᵐ[volume] fun z => ((om z : ℝ) : ℂ) * f z) →
        ∃ G : L2H', ((G : ℍ → ℂ) =ᵐ[volume] fun z => ((om z : ℝ) : ℂ) * T f z)
          ∧ ‖G‖ ≤ K * (M₀ ^ (1 - (1 + 1 / (2 * β)) / 2) * M₁ ^ ((1 + 1 / (2 * β)) / 2)) * ‖F‖ := by
  obtain ⟨K, hK, hT⟩ := transfer hβ hc0 hc1 hD
  have hβ0 : 0 ≤ β := by linarith
  refine ⟨K, hK, fun {om} hW T hadd {M₀ M₁} hM₀ hM hu hw {f F} hF => ?_⟩
  have hM₁ : 0 ≤ M₁ := hM₀.trans hM
  have hblock : ∀ (l n : ℕ) (u : L2H'), cutN n u = u → Real.exp (β * l) * ‖cutN l (T u)‖ ≤ M₁ * Real.exp (β * (n + 1)) * ‖u‖ := fun l n u hcu => by
    obtain ⟨U, hU, nU⟩ := chart_of_shell hβ0 hcu
    obtain ⟨X, hX, nX⟩ := hw u U hU
    calc Real.exp (β * l) * ‖cutN l (T u)‖ ≤ ‖X‖ := block_of_chart hβ0 hX l
      _ ≤ M₁ * ‖U‖ := nX
      _ ≤ M₁ * (Real.exp (β * (n + 1)) * ‖u‖) := mul_le_mul_of_nonneg_left nU hM₁
      _ = _ := by ring
  have h := hT om hW.nonneg hW.lo hW.hi T hadd hM₀ hM hu hblock f
  set Kc := K * (M₀ ^ (1 - (1 + 1 / (2 * β)) / 2) * M₁ ^ ((1 + 1 / (2 * β)) / 2)) with hKc
  have hKc0 : 0 ≤ Kc := by
    rw [hKc]
    exact mul_nonneg hK.le (mul_nonneg (Real.rpow_nonneg hM₀ _) (Real.rpow_nonneg hM₁ _))
  have eF : ∫⁻ z : ℍ, ENNReal.ofReal (om z ^ 2 * ‖f z‖ ^ 2) = ENNReal.ofReal (‖F‖ ^ 2) := by
    rw [← lintegral_enorm_sq_eq]
    refine lintegral_congr_ae ?_
    filter_upwards [hF] with z hz
    rw [hz, enorm_mul, ← sq_ofReal_enorm (hW.nonneg z), ← ofReal_norm ((om z : ℝ) : ℂ), Complex.norm_real, Real.norm_of_nonneg (hW.nonneg z)]
  rw [eF, ← ENNReal.ofReal_mul (by positivity), ← mul_pow] at h
  refine exists_chart_of_lint hW.meas hW.nonneg (T f) (mul_nonneg hKc0 (norm_nonneg _)) ?_
  refine le_trans (le_of_eq ?_) h
  refine lintegral_congr fun z => ?_
  exact sq_ofReal_enorm (hW.nonneg z) _

/-- The transfer lemma with one constant for both bounds. -/
theorem transfer_chart_same {β c D : ℝ} (hβ : 1 / 2 < β) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hD : 0 < D) :
    ∃ K : ℝ, 0 < K ∧ ∀ {om : ℍ → ℝ}, CritW c D om →
      ∀ (T : L2H' → L2H'), (∀ u v, T (u + v) = T u + T v) → ∀ {M : ℝ}, 0 ≤ M → (∀ u, ‖T u‖ ≤ M * ‖u‖) →
      (∀ (u U : L2H'), ((U : ℍ → ℂ) =ᵐ[volume] fun z => ((omG β z : ℝ) : ℂ) * u z) →
        ∃ X : L2H', ((X : ℍ → ℂ) =ᵐ[volume] fun z => ((omG β z : ℝ) : ℂ) * T u z) ∧ ‖X‖ ≤ M * ‖U‖) →
      ∀ {f F : L2H'}, ((F : ℍ → ℂ) =ᵐ[volume] fun z => ((om z : ℝ) : ℂ) * f z) →
        ∃ G : L2H', ((G : ℍ → ℂ) =ᵐ[volume] fun z => ((om z : ℝ) : ℂ) * T f z) ∧ ‖G‖ ≤ K * M * ‖F‖ := by
  obtain ⟨K, hK, hT⟩ := transfer_chart hβ hc0 hc1 hD
  have hβ0 : 0 < β := by linarith
  refine ⟨K, hK, fun {om} hW T hadd {M} hM hu hw {f F} hF => ?_⟩
  obtain ⟨G, hG, nG⟩ := hT hW T hadd hM le_rfl hu hw hF
  refine ⟨G, hG, ?_⟩
  have ht0 : 0 ≤ (1 + 1 / (2 * β)) / 2 := by positivity
  have ht1 : (1 + 1 / (2 * β)) / 2 ≤ 1 := by
    have : 1 / (2 * β) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    linarith
  rwa [rpow_split_self hM ht0 ht1] at nG

/-! ### Constants -/

lemma one_le_C4 {K : ℝ} (hK : 1 ≤ K) : 1 ≤ C4 K := by
  unfold C4
  nlinarith [sq_nonneg (K - 1)]

/-- The common constant of the two word counts. -/
noncomputable def C4m (C₁ : ℝ) : ℝ := max (C4 (K3c 1 C₁)) (C4 (K3p 1))

lemma one_le_C4m (C₁ : ℝ) : 1 ≤ C4m C₁ := (one_le_C4 (one_le_K3c 1 C₁)).trans (le_max_left _ _)

/-- The common factor of the bounds, with `a` extra letters. -/
noncomputable def facP (Cm σ ħ : ℝ) (N L a : ℕ) : ℝ :=
  Cm ^ (N + L + a) * ((2 * N).factorial : ℝ) * ((a + 2 * L).factorial : ℝ) * (σ⁻¹) ^ (a + 2 * L) * ((σ * ħ)⁻¹) ^ (2 * N)

lemma facP_nonneg {Cm σ ħ : ℝ} (hCm : 0 ≤ Cm) (hσ : 0 < σ) (hħ : 0 < ħ) (N L a : ℕ) : 0 ≤ facP Cm σ ħ N L a := by
  unfold facP; positivity

lemma facP_zero (Cm σ ħ : ℝ) (N L : ℕ) :
    facP Cm σ ħ N L 0 = Cm ^ (N + L) * ((2 * N).factorial : ℝ) * ((2 * L).factorial : ℝ) * (σ⁻¹) ^ (2 * L) * ((σ * ħ)⁻¹) ^ (2 * N) := by
  unfold facP
  simp only [Nat.add_zero, Nat.zero_add]

lemma le_facP {C Cm σ ħ : ℝ} (hC0 : 0 ≤ C) (hC : C ≤ Cm) (hσ : 0 < σ) (hħ : 0 < ħ) (N L a : ℕ) :
    C ^ (N + L + a) * ((2 * N).factorial : ℝ) * ((a + 2 * L).factorial : ℝ) * (σ⁻¹) ^ (a + 2 * L) * ((σ * ħ)⁻¹) ^ (2 * N) ≤ facP Cm σ ħ N L a := by
  unfold facP
  gcongr

lemma le_facP_zero {C Cm σ ħ : ℝ} (hC0 : 0 ≤ C) (hC : C ≤ Cm) (hσ : 0 < σ) (hħ : 0 < ħ) (N L : ℕ) :
    C ^ (N + L) * ((2 * N).factorial : ℝ) * ((2 * L).factorial : ℝ) * (σ⁻¹) ^ (2 * L) * ((σ * ħ)⁻¹) ^ (2 * N) ≤ facP Cm σ ħ N L 0 := by
  rw [facP_zero]
  gcongr

lemma facP_zero_le_two {Cm σ ħ : ℝ} (hCm : 1 ≤ Cm) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hħ : 0 < ħ) (N L : ℕ) :
    facP Cm σ ħ N L 0 ≤ facP Cm σ ħ N L 2 := by
  unfold facP
  have hAi1 : 1 ≤ σ⁻¹ := (one_le_inv₀ hσ).2 hσ1
  have h1 : Cm ^ (N + L + 0) ≤ Cm ^ (N + L + 2) := pow_le_pow_right₀ hCm (by omega)
  have h2 : ((0 + 2 * L).factorial : ℝ) ≤ ((2 + 2 * L).factorial : ℝ) := by exact_mod_cast Nat.factorial_le (by omega)
  have h3 : (σ⁻¹) ^ (0 + 2 * L) ≤ (σ⁻¹) ^ (2 + 2 * L) := pow_le_pow_right₀ hAi1 (by omega)
  have hC0 : 0 ≤ Cm := by linarith
  gcongr

/-! ### The flow is isometric -/

lemma norm_of_adjoint_mul_self {U : L2H' →L[ℂ] L2H'} (h : ContinuousLinearMap.adjoint U * U = 1) (x : L2H') : ‖U x‖ = ‖x‖ := by
  have h2 : ContinuousLinearMap.adjoint U (U x) = x := by
    have := congrArg (fun T : L2H' →L[ℂ] L2H' => T x) h
    simpa [ContinuousLinearMap.mul_apply] using this
  have e : ⟪U x, U x⟫_ℂ = ⟪x, x⟫_ℂ := by
    rw [← ContinuousLinearMap.adjoint_inner_right, h2]
  have h3 := congrArg RCLike.re e
  rw [inner_self_eq_norm_sq, inner_self_eq_norm_sq] at h3
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h3

lemma norm_gflow (P : MollProfile) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hb s₁ : ℝ) (b' : negLapH.domain) (s : ℝ) :
    ‖(gflow P hε hε1 hb s₁ b' s : L2H')‖ = ‖(b' : L2H')‖ := by
  show ‖(P.cutoffEps hε).flowEps hb s (ContinuousLinearMap.adjoint ((P.cutoffEps hε).flowEps hb s₁) (b' : L2H'))‖ = _
  rw [norm_of_adjoint_mul_self ((P.cutoffEps hε).flowEps_unitary hb s).1]
  refine norm_of_adjoint_mul_self ?_ _
  rw [ContinuousLinearMap.adjoint_adjoint]
  exact ((P.cutoffEps hε).flowEps_unitary hb s₁).2

lemma chart_zero_self (u : L2H') : (u : ℍ → ℂ) =ᵐ[volume] fun z => ((omG 0 z : ℝ) : ℂ) * u z :=
  Filter.Eventually.of_forall fun z => by
    show (u : ℍ → ℂ) z = ((omG 0 z : ℝ) : ℂ) * u z
    rw [show omG 0 z = 1 from Real.rpow_zero _]
    simp

/-! ### The maps -/

section maps

variable {c D m : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hD : 0 < D) (hm : 1 / 2 ≤ m) (hml : 2 * ((1 : ℝ) + 1 / 2) ^ 2 < m ^ 2)
include hc0 hc1 hD hm hml

/-- **The chart of `b'_f` in a critical weight.** -/
theorem bE_chart_om : ∃ K : ℝ, 0 < K ∧ ∀ {om : ℍ → ℝ}, CritW c D om → ∀ {C₁ : ℝ}, FCBound 1 C₁ → 0 ≤ C₁ →
    ∀ {σ : ℝ}, 0 < σ → σ ≤ 1 → ∀ {ħ : ℝ}, 0 < ħ → ħ ≤ 1 → ∀ (N : ℕ) {s₁ : ℝ}, 0 ≤ s₁ → ∀ (ss : List ℝ), (∀ r ∈ ss, 0 ≤ r) →
    ∀ {f F : L2H'}, ((F : ℍ → ℂ) =ᵐ[volume] fun z => ((om z : ℝ) : ℂ) * f z) →
    ∃ G : L2H', ((G : ℍ → ℂ) =ᵐ[volume] fun z => ((om z : ℝ) : ℂ) * bE m σ ħ N s₁ ss f z)
      ∧ ‖G‖ ≤ K * (√2 * facP (C4m C₁) σ ħ N ss.length 0) * ‖F‖ := by
  obtain ⟨K, hK, hT⟩ := transfer_chart_same (β := 1) (by norm_num) hc0 hc1 hD
  refine ⟨K, hK, fun {om} hW {C₁} hF' hC {σ} hσ hσ1 {ħ} hħ hħ1 N {s₁} hs₁ ss hss {f F} hF => ?_⟩
  have hCm := one_le_C4m C₁
  have hCm0 : 0 ≤ C4m C₁ := by linarith
  have hs2 : (1 : ℝ) ≤ √2 := by
    rw [show (1 : ℝ) = √1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hfac0 := facP_nonneg hCm0 hσ hħ N ss.length 0
  have hc0' : 0 ≤ C4 (K3c 1 C₁) := le_trans zero_le_one (one_le_C4 (one_le_K3c 1 C₁))
  have hp0' : 0 ≤ C4 (K3p 1) := le_trans zero_le_one (one_le_C4 (one_le_K3p zero_le_one))
  have hle : facP (C4m C₁) σ ħ N ss.length 0 ≤ √2 * facP (C4m C₁) σ ħ N ss.length 0 := by nlinarith
  have h1 : ∀ u, ‖bE m σ ħ N s₁ ss u‖ ≤ (√2 * facP (C4m C₁) σ ħ N ss.length 0) * ‖u‖ := fun u => by
    refine (norm_bE_le hm hσ hσ1 hF' hC hħ hħ1 N hs₁ ss hss u).trans ?_
    exact mul_le_mul_of_nonneg_right ((le_facP_zero hc0' (le_max_left _ _) hσ hħ N ss.length).trans hle) (norm_nonneg _)
  have h2 : ∀ (u U : L2H'), ((U : ℍ → ℂ) =ᵐ[volume] fun z => ((omG 1 z : ℝ) : ℂ) * u z) →
      ∃ X : L2H', ((X : ℍ → ℂ) =ᵐ[volume] fun z => ((omG 1 z : ℝ) : ℂ) * bE m σ ħ N s₁ ss u z)
        ∧ ‖X‖ ≤ (√2 * facP (C4m C₁) σ ħ N ss.length 0) * ‖U‖ := fun u U hU => by
    obtain ⟨-, G, hG, nG⟩ := pc_wb_w (β := 1) zero_le_one hm hml hσ hσ1 hU hħ hħ1 N hs₁ ss hss [] (n := 0) le_rfl
    refine ⟨G, hG, nG.trans (le_of_eq_of_le ?_ (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (le_facP_zero hp0' (le_max_right _ _) hσ hħ N ss.length) (Real.sqrt_nonneg 2)) (norm_nonneg U)))⟩
    simp only [Nat.add_zero, Nat.zero_add]
    ring
  exact hT hW (bE m σ ħ N s₁ ss) (bE_add hm hσ hσ1 ħ N s₁ ss) (by positivity) h1 h2 hF

/-- **The words of `e^{-σΛ_m} f` have charts in a critical weight.** -/
theorem word_chart_om {om : ℍ → ℝ} (hW : CritW c D om) {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (S : List Bool) {f F : L2H'}
    (hF : (F : ℍ → ℂ) =ᵐ[volume] fun z => ((om z : ℝ) : ℂ) * f z) :
    ∃ G : L2H', (G : ℍ → ℂ) =ᵐ[volume] fun z => ((om z : ℝ) : ℂ) * wordAct S (vE m σ f 0) z := by
  obtain ⟨K, hK, hT⟩ := transfer_chart_same (β := 1) (by norm_num) hc0 hc1 hD
  have hml0 : 2 * ((0 : ℝ) + 1 / 2) ^ 2 < m ^ 2 := by
    norm_num at hml ⊢
    linarith
  have hK0 : 0 < K3p 0 := lt_of_lt_of_le one_pos (one_le_K3p le_rfl)
  have hK1 : 0 < K3p 1 := lt_of_lt_of_le one_pos (one_le_K3p zero_le_one)
  set M0 := √2 * ((S.length : ℝ) + 1) * S.length.factorial * (K3p 0 / σ) ^ S.length with hM0
  set M1 := √2 * ((S.length : ℝ) + 1) * S.length.factorial * (K3p 1 / σ) ^ S.length with hM1
  have hM00 : 0 ≤ M0 := by positivity
  have hadd : ∀ u v, wordAct S (vE m σ (u + v) 0) = wordAct S (vE m σ u 0) + wordAct S (vE m σ v 0) := fun u v => by
    have e : vE m σ (u + v) 0 = vE m σ u 0 + vE m σ v 0 := by
      unfold vE
      rw [map_add]
    rw [e, wordAct_add (vE_allWords hm hσ hσ1 u 0) (vE_allWords hm hσ hσ1 v 0)]
  have h1 : ∀ u, ‖wordAct S (vE m σ u 0)‖ ≤ max M0 M1 * ‖u‖ := fun u => by
    obtain ⟨G, hG, nG⟩ := pc_word_chart (β := 0) le_rfl hm hml0 hσ hσ1 (chart_zero_self u) S
    have e : G = wordAct S (vE m σ u 0) := by
      refine Lp.ext ?_
      filter_upwards [hG] with z hz
      rw [hz, show omG 0 z = 1 from Real.rpow_zero _]
      simp
    rw [← e]
    exact nG.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  have h2 : ∀ (u U : L2H'), ((U : ℍ → ℂ) =ᵐ[volume] fun z => ((omG 1 z : ℝ) : ℂ) * u z) →
      ∃ X : L2H', ((X : ℍ → ℂ) =ᵐ[volume] fun z => ((omG 1 z : ℝ) : ℂ) * wordAct S (vE m σ u 0) z) ∧ ‖X‖ ≤ max M0 M1 * ‖U‖ := fun u U hU => by
    obtain ⟨G, hG, nG⟩ := pc_word_chart (β := 1) zero_le_one hm hml hσ hσ1 hU S
    exact ⟨G, hG, nG.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))⟩
  obtain ⟨G, hG, -⟩ := hT hW (fun u => wordAct S (vE m σ u 0)) hadd (le_max_of_le_left hM00) h1 h2 hF
  exact ⟨G, hG⟩

/-- **The chart of `V_ε(s) V_ε(s₁)* b'_f` in a critical weight.** -/
theorem flow_chart_om : ∃ K A₀ : ℝ, 0 < K ∧ 0 ≤ A₀ ∧ ∀ {om : ℍ → ℝ}, CritW c D om → ∀ {C₁ : ℝ}, FCBound 1 C₁ → 0 ≤ C₁ →
    ∀ (Γ' : Subgroup PGL(2, ℝ)) [Countable Γ'] [ProperlyDiscontinuousSMul Γ' ℍ] (Wβ : SurfW Γ'), (∀ z, Wβ.ω z = omG 1 z) →
    ∀ {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {ħ : ℝ}, 0 < ħ → ħ ≤ 1 → ∀ (N : ℕ) {s₁ s : ℝ}, 0 ≤ s₁ →
      s ∈ Icc 0 s₁ → ħ * s₁ ≤ ε → ∀ (ss : List ℝ), (∀ r ∈ ss, 0 ≤ r) →
    ∀ {f F : L2H'}, ((F : ℍ → ℂ) =ᵐ[volume] fun z => ((om z : ℝ) : ℂ) * f z) →
    ∃ P : L2H', ((P : ℍ → ℂ) =ᵐ[volume] fun z => ((om z : ℝ) : ℂ)
        * (gflow stdP hε hε1 ħ s₁ ⟨bE m σ ħ N s₁ ss f, bE_mem hm hσ hσ1 ħ N s₁ ss f⟩ s : L2H') z)
      ∧ ‖P‖ ≤ K * ((1 + A₀) * facP (C4m C₁) σ ħ N ss.length 0) * ‖F‖ := by
  obtain ⟨K, hK, hT⟩ := transfer_chart_same (β := 1) (by norm_num) hc0 hc1 hD
  obtain ⟨A₀, A₁, hA₀, -, hch⟩ := dvec_chart_beta (β := 1) zero_le_one hm hml
  refine ⟨K, A₀, hK, hA₀, fun {om} hW {C₁} hF' hC Γ' _ _ Wβ hWβ {σ} hσ hσ1 {ε} hε hε1 {ħ} hħ hħ1 N {s₁ s} hs₁ hs hwin ss hss {f F} hF => ?_⟩
  have hCm := one_le_C4m C₁
  have hCm0 : 0 ≤ C4m C₁ := by linarith
  have hfac0 := facP_nonneg hCm0 hσ hħ N ss.length 0
  have hc0' : 0 ≤ C4 (K3c 1 C₁) := le_trans zero_le_one (one_le_C4 (one_le_K3c 1 C₁))
  have hp0' : 0 ≤ C4 (K3p 1) := le_trans zero_le_one (one_le_C4 (one_le_K3p zero_le_one))
  set T : L2H' → L2H' := fun u => (gflow stdP hε hε1 ħ s₁ ⟨bE m σ ħ N s₁ ss u, bE_mem hm hσ hσ1 ħ N s₁ ss u⟩ s : L2H') with hTd
  have hadd : ∀ u v, T (u + v) = T u + T v := fun u v => by
    have e : (⟨bE m σ ħ N s₁ ss (u + v), bE_mem hm hσ hσ1 ħ N s₁ ss (u + v)⟩ : negLapH.domain)
        = ⟨bE m σ ħ N s₁ ss u, bE_mem hm hσ hσ1 ħ N s₁ ss u⟩ + ⟨bE m σ ħ N s₁ ss v, bE_mem hm hσ hσ1 ħ N s₁ ss v⟩ :=
      Subtype.ext (bE_add hm hσ hσ1 ħ N s₁ ss u v)
    show ((gflow stdP hε hε1 ħ s₁ ⟨bE m σ ħ N s₁ ss (u + v), bE_mem hm hσ hσ1 ħ N s₁ ss (u + v)⟩ s : negLapH.domain) : L2H') = _
    rw [e, gflow_add]
    rfl
  have h1 : ∀ u, ‖T u‖ ≤ ((1 + A₀) * facP (C4m C₁) σ ħ N ss.length 0) * ‖u‖ := fun u => by
    show ‖(gflow stdP hε hε1 ħ s₁ ⟨bE m σ ħ N s₁ ss u, bE_mem hm hσ hσ1 ħ N s₁ ss u⟩ s : L2H')‖ ≤ _
    rw [norm_gflow]
    refine (norm_bE_le hm hσ hσ1 hF' hC hħ hħ1 N hs₁ ss hss u).trans ?_
    have h3 : C4 (K3c 1 C₁) ^ (N + ss.length) * ((2 * N).factorial : ℝ) * ((2 * ss.length).factorial : ℝ) * (σ⁻¹) ^ (2 * ss.length)
        * ((σ * ħ)⁻¹) ^ (2 * N) ≤ facP (C4m C₁) σ ħ N ss.length 0 := le_facP_zero hc0' (le_max_left _ (C4 (K3p 1))) hσ hħ N ss.length
    have h4 : facP (C4m C₁) σ ħ N ss.length 0 ≤ (1 + A₀) * facP (C4m C₁) σ ħ N ss.length 0 := by nlinarith
    exact mul_le_mul_of_nonneg_right (h3.trans h4) (norm_nonneg _)
  have h2 : ∀ (u U : L2H'), ((U : ℍ → ℂ) =ᵐ[volume] fun z => ((omG 1 z : ℝ) : ℂ) * u z) →
      ∃ X : L2H', ((X : ℍ → ℂ) =ᵐ[volume] fun z => ((omG 1 z : ℝ) : ℂ) * T u z)
        ∧ ‖X‖ ≤ ((1 + A₀) * facP (C4m C₁) σ ħ N ss.length 0) * ‖U‖ := fun u U hU => by
    obtain ⟨P, hP, nP⟩ := (hch Γ' Wβ hWβ hσ hσ1 hε hε1 hħ hħ1 N hs₁ hs hwin ss hss hU).1
    refine ⟨P, hP, nP.trans ?_⟩
    have h3 : C4 (K3p 1) ^ (N + ss.length) * ((2 * N).factorial : ℝ) * ((2 * ss.length).factorial : ℝ) * (σ⁻¹) ^ (2 * ss.length)
        * ((σ * ħ)⁻¹) ^ (2 * N) ≤ facP (C4m C₁) σ ħ N ss.length 0 := le_facP_zero hp0' (le_max_right (C4 (K3c 1 C₁)) _) hσ hħ N ss.length
    have hU0 := norm_nonneg U
    calc A₀ * (C4 (K3p 1) ^ (N + ss.length) * ((2 * N).factorial : ℝ) * ((2 * ss.length).factorial : ℝ) * (σ⁻¹) ^ (2 * ss.length)
          * ((σ * ħ)⁻¹) ^ (2 * N) * ‖U‖)
        = A₀ * (C4 (K3p 1) ^ (N + ss.length) * ((2 * N).factorial : ℝ) * ((2 * ss.length).factorial : ℝ) * (σ⁻¹) ^ (2 * ss.length)
          * ((σ * ħ)⁻¹) ^ (2 * N)) * ‖U‖ := by ring
      _ ≤ A₀ * facP (C4m C₁) σ ħ N ss.length 0 * ‖U‖ := by gcongr
      _ ≤ (1 + A₀) * facP (C4m C₁) σ ħ N ss.length 0 * ‖U‖ := by nlinarith [mul_nonneg hfac0 hU0]
  exact hT hW T hadd (by positivity) h1 h2 hF

/-- **The chart of the defect in a critical weight.** -/
theorem dvec_chart_om : ∃ K A₁ C₀ : ℝ, 0 < K ∧ 0 ≤ A₁ ∧ 0 ≤ C₀ ∧ ∀ {om : ℍ → ℝ}, CritW c D om → ∀ {C₁ : ℝ}, FCBound 1 C₁ → 0 ≤ C₁ →
    ∀ (Γ' : Subgroup PGL(2, ℝ)) [Countable Γ'] [ProperlyDiscontinuousSMul Γ' ℍ] (Wβ : SurfW Γ'), (∀ z, Wβ.ω z = omG 1 z) →
    ∀ {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {ħ : ℝ}, 0 < ħ → ħ ≤ 1 → ∀ (N : ℕ) {s₁ s : ℝ}, 0 ≤ s₁ →
      s ∈ Icc 0 s₁ → ħ * s₁ ≤ ε → |s - s₁| ≤ cA0 1 * (1 / 3) * (ε / ħ) → ∀ (ss : List ℝ), (∀ r ∈ ss, 0 ≤ r) →
    ∀ {f F : L2H'}, ((F : ℍ → ℂ) =ᵐ[volume] fun z => ((om z : ℝ) : ℂ) * f z) →
    ∃ X : L2H', ((X : ℍ → ℂ) =ᵐ[volume] fun z => ((om z : ℝ) : ℂ)
        * dvec stdP hε hε1 ħ s₁ ⟨bE m σ ħ N s₁ ss f, bE_mem hm hσ hσ1 ħ N s₁ ss f⟩ s z)
      ∧ ‖X‖ ≤ K * ((8 * C₀ * ħ * (σ⁻¹) ^ 4 * Real.exp (-(σ / (16 * ε))) * facP (C4m C₁) σ ħ N ss.length 2) ^ (1 / 4 : ℝ)
        * ((8 * C₀ * ħ * (σ⁻¹) ^ 4 * Real.exp (-(σ / (16 * ε))) + A₁ * (ε⁻¹) ^ 3) * facP (C4m C₁) σ ħ N ss.length 2) ^ (3 / 4 : ℝ)) * ‖F‖ := by
  obtain ⟨K, hK, hT⟩ := transfer_chart (β := 1) (by norm_num) hc0 hc1 hD
  obtain ⟨A₀, A₁, -, hA₁, hch⟩ := dvec_chart_beta (β := 1) zero_le_one hm hml
  obtain ⟨C₀, hC₀, hun⟩ := dvec_bE_le hm
  refine ⟨K, A₁, C₀, hK, hA₁, hC₀, fun {om} hW {C₁} hF' hC Γ' _ _ Wβ hWβ {σ} hσ hσ1 {ε} hε hε1 {ħ} hħ hħ1 N {s₁ s} hs₁ hs hwin hwin2 ss hss {f F} hF => ?_⟩
  have hCm := one_le_C4m C₁
  have hCm0 : 0 ≤ C4m C₁ := by linarith
  have hc0' : 0 ≤ C4 (K3c 1 C₁) := le_trans zero_le_one (one_le_C4 (one_le_K3c 1 C₁))
  have hp0' : 0 ≤ C4 (K3p 1) := le_trans zero_le_one (one_le_C4 (one_le_K3p zero_le_one))
  set fac := facP (C4m C₁) σ ħ N ss.length 2 with hfac
  have hfac0 : 0 ≤ fac := facP_nonneg hCm0 hσ hħ N ss.length 2
  set Y := 8 * C₀ * ħ * (σ⁻¹) ^ 4 * Real.exp (-(σ / (16 * ε))) with hY
  have hY0 : 0 ≤ Y := by positivity
  have hE0 : 0 ≤ A₁ * (ε⁻¹) ^ 3 := by positivity
  set T : L2H' → L2H' := fun u => dvec stdP hε hε1 ħ s₁ ⟨bE m σ ħ N s₁ ss u, bE_mem hm hσ hσ1 ħ N s₁ ss u⟩ s with hTd
  have hadd : ∀ u v, T (u + v) = T u + T v := fun u v => by
    have e : (⟨bE m σ ħ N s₁ ss (u + v), bE_mem hm hσ hσ1 ħ N s₁ ss (u + v)⟩ : negLapH.domain)
        = ⟨bE m σ ħ N s₁ ss u, bE_mem hm hσ hσ1 ħ N s₁ ss u⟩ + ⟨bE m σ ħ N s₁ ss v, bE_mem hm hσ hσ1 ħ N s₁ ss v⟩ :=
      Subtype.ext (bE_add hm hσ hσ1 ħ N s₁ ss u v)
    show dvec stdP hε hε1 ħ s₁ ⟨bE m σ ħ N s₁ ss (u + v), bE_mem hm hσ hσ1 ħ N s₁ ss (u + v)⟩ s = _
    rw [e, dvec_add]
  have hQ0 : C4 (K3c 1 C₁) ^ (N + ss.length) * ((2 * N).factorial : ℝ) * ((2 * ss.length).factorial : ℝ) * (σ⁻¹) ^ (2 * ss.length)
      * ((σ * ħ)⁻¹) ^ (2 * N) ≤ fac :=
    (le_facP_zero hc0' (le_max_left _ (C4 (K3p 1))) hσ hħ N ss.length).trans (facP_zero_le_two hCm hσ hσ1 hħ N ss.length)
  have h1 : ∀ u, ‖T u‖ ≤ (Y * fac) * ‖u‖ := fun u => by
    refine (hun hσ hσ1 hF' hC hε hε1 hħ hħ1 N hs₁ hs.1 hwin2 ss hss u).trans ?_
    have hu0 := norm_nonneg u
    calc ħ / 2 * (C₀ * (16 * (σ⁻¹) ^ 4) * Real.exp (-(σ / (16 * ε)))
          * (C4 (K3c 1 C₁) ^ (N + ss.length) * ((2 * N).factorial : ℝ) * ((2 * ss.length).factorial : ℝ)
            * (σ⁻¹) ^ (2 * ss.length) * ((σ * ħ)⁻¹) ^ (2 * N) * ‖u‖))
        = Y * (C4 (K3c 1 C₁) ^ (N + ss.length) * ((2 * N).factorial : ℝ) * ((2 * ss.length).factorial : ℝ)
            * (σ⁻¹) ^ (2 * ss.length) * ((σ * ħ)⁻¹) ^ (2 * N)) * ‖u‖ := by rw [hY]; ring
      _ ≤ Y * fac * ‖u‖ := by gcongr
  have h2 : ∀ (u U : L2H'), ((U : ℍ → ℂ) =ᵐ[volume] fun z => ((omG 1 z : ℝ) : ℂ) * u z) →
      ∃ X : L2H', ((X : ℍ → ℂ) =ᵐ[volume] fun z => ((omG 1 z : ℝ) : ℂ) * T u z)
        ∧ ‖X‖ ≤ ((Y + A₁ * (ε⁻¹) ^ 3) * fac) * ‖U‖ := fun u U hU => by
    obtain ⟨X, hX, nX⟩ := (hch Γ' Wβ hWβ hσ hσ1 hε hε1 hħ hħ1 N hs₁ hs hwin ss hss hU).2
    refine ⟨X, hX, nX.trans ?_⟩
    have hU0 := norm_nonneg U
    have h3 : C4 (K3p 1) ^ (N + ss.length + 2) * ((2 * N).factorial : ℝ) * ((2 + 2 * ss.length).factorial : ℝ) * (σ⁻¹) ^ (2 + 2 * ss.length)
        * ((σ * ħ)⁻¹) ^ (2 * N) ≤ fac := le_facP hp0' (le_max_right (C4 (K3c 1 C₁)) _) hσ hħ N ss.length 2
    calc A₁ * (ε⁻¹) ^ 3 * (C4 (K3p 1) ^ (N + ss.length + 2) * ((2 * N).factorial : ℝ) * ((2 + 2 * ss.length).factorial : ℝ)
          * (σ⁻¹) ^ (2 + 2 * ss.length) * ((σ * ħ)⁻¹) ^ (2 * N) * ‖U‖)
        = A₁ * (ε⁻¹) ^ 3 * (C4 (K3p 1) ^ (N + ss.length + 2) * ((2 * N).factorial : ℝ) * ((2 + 2 * ss.length).factorial : ℝ)
          * (σ⁻¹) ^ (2 + 2 * ss.length) * ((σ * ħ)⁻¹) ^ (2 * N)) * ‖U‖ := by ring
      _ ≤ A₁ * (ε⁻¹) ^ 3 * fac * ‖U‖ := by gcongr
      _ ≤ (Y + A₁ * (ε⁻¹) ^ 3) * fac * ‖U‖ := by nlinarith [mul_nonneg (mul_nonneg hY0 hfac0) hU0]
  have hM : Y * fac ≤ (Y + A₁ * (ε⁻¹) ^ 3) * fac := by nlinarith [mul_nonneg hE0 hfac0]
  obtain ⟨G, hG, nG⟩ := hT hW T hadd (mul_nonneg hY0 hfac0) hM h1 h2 hF
  have e1 : (1 - (1 + 1 / (2 * (1 : ℝ))) / 2) = 1 / 4 := by norm_num
  have e2 : ((1 + 1 / (2 * (1 : ℝ))) / 2) = 3 / 4 := by norm_num
  rw [e1, e2] at nG
  exact ⟨G, hG, nG⟩

end maps

end Qschubert
