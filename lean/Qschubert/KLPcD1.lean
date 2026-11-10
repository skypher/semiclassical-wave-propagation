import Qschubert.KLPcRB

/-!
# The amplitude `e^{-σΛ_m} h` in the power weight `X₀^β`: words and `b'(s)`

`wb_w_gen`: the count of Lemma WB for an amplitude whose words have charts with factorial bounds, in any weight.
`pc_word_chart`: for `h` with `X₀^β h ∈ L²`, every word of `e^{-σΛ_m} h` has a chart in the weight `X₀^β`, with the bound of `words_w`.
`pc_wb_w`: the resulting bound for the words of `b'(s) = Δ_φ(s₁)^N Δ(s₁)⋯ e^{-σΛ_m} h`.
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set Physicslib4.Spectral Physicslib4.Spectral.Unbounded
open scoped ENNReal InnerProductSpace ComplexConjugate UpperHalfPlane

local notation "L2H'" => Lp ℂ 2 (volume : Measure UpperHalfPlane)

/-- **(WB-w) for a general amplitude and weight.** -/
theorem wb_w_gen {a : L2H'} (hA : AllWords a) (wt : UpperHalfPlane → ℂ) (Gw : List Bool → L2H')
    (hGw1 : ∀ S, (Gw S : UpperHalfPlane → ℂ) =ᵐ[volume] fun z => wt z * wordAct S a z)
    {B K₃ α NF : ℝ} (hB0 : 0 ≤ B) (hK₃ : 1 ≤ K₃) (hNF : 0 ≤ NF)
    (hGw2 : ∀ S : List Bool, ‖Gw S‖ ≤ B * ((S.length : ℝ) + 1) * S.length.factorial * (K₃ / α) ^ S.length * NF)
    {ħ : ℝ} (hħ : 0 < ħ) (hħ1 : ħ ≤ 1) (hα : 0 < α) (hα1 : α ≤ 1) (N : ℕ) {s₁ : ℝ} (hs₁ : 0 ≤ s₁)
    (ss : List ℝ) (hss : ∀ s ∈ ss, 0 ≤ s) (J : List Bool) {n : ℕ} (hJ : J.length ≤ n) :
    WordDom J (polyAct (bP ħ N s₁ ss) a) ∧ ∃ G : L2H',
      (G : UpperHalfPlane → ℂ) =ᵐ[volume] (fun z => wt z * wordAct J (polyAct (bP ħ N s₁ ss) a) z) ∧
      ‖G‖ ≤ B * C4 K₃ ^ (N + ss.length + n) * (2 * N).factorial * (n + 2 * ss.length).factorial
        * (α⁻¹) ^ (n + 2 * ss.length) * ((α * ħ)⁻¹) ^ (2 * N) * NF := by
  set P := bP ħ N s₁ ss
  obtain ⟨hd, hs⟩ := poly_words hA P J
  refine ⟨hd, ?_⟩
  set A' := n + 2 * ss.length
  obtain ⟨hinv, hlen⟩ := bP_inv hħ hħ1 hs₁ N ss hss
  set M : ℝ := B * (2 ^ N * (4 * K₃) ^ (2 * N + A') * (2 * N).factorial * A'.factorial * (α⁻¹) ^ A' * ((α * ħ)⁻¹) ^ (2 * N)) * NF
  have hterm : ∀ t ∈ P, ‖t.1 • Gw (J ++ t.2)‖ ≤ M := by
    intro t ht
    obtain ⟨ℓ, r, hlw, hℓ, hr, hc⟩ := hinv t ht
    set S := J ++ t.2
    have hSl : S.length ≤ ℓ + A' := by
      simp only [S, List.length_append, A']; omega
    have hG := hGw2 S
    have hs1 := sca (N := N) (K₃ := K₃) hℓ hSl hK₃ hα hα1 hħ hħ1
    have hc' := coeff_le hħ hc
    rw [norm_smul]
    have hi : 0 ≤ ħ⁻¹ := by positivity
    have e : ((α * ħ)⁻¹) ^ (2 * N) = (α⁻¹) ^ (2 * N) * (ħ⁻¹) ^ (2 * N) := by rw [mul_inv, mul_pow]
    have hK0 : 0 ≤ K₃ / α := by positivity
    calc ‖t.1‖ * ‖Gw S‖
        ≤ (2 ^ N * ħ ^ ℓ * (ħ⁻¹) ^ (2 * N)) * (B * ((S.length : ℝ) + 1) * S.length.factorial * (K₃ / α) ^ S.length * NF) :=
          mul_le_mul hc' hG (norm_nonneg _) (by positivity)
      _ = B * 2 ^ N * (ħ⁻¹) ^ (2 * N) * NF * (((S.length : ℝ) + 1) * S.length.factorial * (K₃ / α) ^ S.length * ħ ^ ℓ) := by ring
      _ ≤ B * 2 ^ N * (ħ⁻¹) ^ (2 * N) * NF
          * ((4 * K₃) ^ (2 * N + A') * (2 * N).factorial * A'.factorial * (α⁻¹) ^ A' * (α⁻¹) ^ (2 * N)) := by gcongr
      _ = M := by simp only [M]; rw [e]; ring
  refine ⟨(P.map fun t => t.1 • Gw (J ++ t.2)).sum, ?_, ?_⟩
  · rw [hs]
    have eP : polyAct (leftW J P) a = (P.map fun t => t.1 • wordAct (J ++ t.2) a).sum := by
      simp only [polyAct, leftW, List.map_map, Function.comp_def]
    rw [eP]
    refine ae_sum_weight _ _ _ _ fun t => ?_
    filter_upwards [hGw1 (J ++ t.2), Lp.coeFn_smul t.1 (Gw (J ++ t.2)), Lp.coeFn_smul t.1 (wordAct (J ++ t.2) a)] with z h1 h2 h3
    rw [h2, h3]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [h1]; ring
  · have hsum := (norm_list_sum_le' P fun t => t.1 • Gw (J ++ t.2)).trans (list_sum_le (g := fun _ => M) hterm)
    have hconst : (P.map fun _ => M).sum = (P.length : ℝ) * M := by
      simp [List.map_const', List.sum_replicate]
    rw [hconst, hlen] at hsum
    push_cast at hsum
    have hc4 := c4_bound hK₃ N ss.length n
    have hM0 : 0 ≤ B * (2 * N).factorial * A'.factorial * (α⁻¹) ^ A' * ((α * ħ)⁻¹) ^ (2 * N) * NF := by positivity
    calc _ ≤ _ := hsum
      _ = ((5 : ℝ) ^ N * 3 ^ ss.length * 2 ^ N * (4 * K₃) ^ (2 * N + (n + 2 * ss.length)))
          * (B * (2 * N).factorial * A'.factorial * (α⁻¹) ^ A' * ((α * ħ)⁻¹) ^ (2 * N) * NF) := by simp only [M, A']; ring
      _ ≤ C4 K₃ ^ (N + ss.length + n) * (B * (2 * N).factorial * A'.factorial * (α⁻¹) ^ A' * ((α * ħ)⁻¹) ^ (2 * N) * NF) := by
          gcongr
      _ = _ := by ring

/-- A vector with a finite weighted integral has a chart. -/
lemma exists_chart_of_lint {om : UpperHalfPlane → ℝ} (hom : Measurable om) (hom0 : ∀ z, 0 ≤ om z) (v : L2H') {C : ℝ} (hC : 0 ≤ C)
    (h : ∫⁻ z, (ENNReal.ofReal (om z) * ‖v z‖ₑ) ^ 2 ≤ ENNReal.ofReal (C ^ 2)) :
    ∃ G : L2H', ((G : UpperHalfPlane → ℂ) =ᵐ[volume] fun z => ((om z : ℝ) : ℂ) * v z) ∧ ‖G‖ ≤ C := by
  have hm : Measurable fun z => ((om z : ℝ) : ℂ) * v z :=
    (Complex.measurable_ofReal.comp hom).mul (Lp.stronglyMeasurable v).measurable
  have e : eLpNorm (fun z => ((om z : ℝ) : ℂ) * v z) 2 volume ≤ ENNReal.ofReal C := by
    refine eLpNorm_two_le_of_lintegral_sq_le hm.aestronglyMeasurable hC ?_
    refine le_trans (le_of_eq ?_) h
    refine lintegral_congr fun z => ?_
    rw [enorm_mul, ← ofReal_norm_eq_enorm ((om z : ℝ) : ℂ), Complex.norm_real, Real.norm_of_nonneg (hom0 z)]
  have hmem : MemLp (fun z => ((om z : ℝ) : ℂ) * v z) 2 (volume : Measure UpperHalfPlane) :=
    lt_of_le_of_lt e ENNReal.ofReal_lt_top
  refine ⟨hmem.toLp _, hmem.coeFn_toLp, ?_⟩
  rw [Lp.norm_toLp]
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top e
  rwa [ENNReal.toReal_ofReal hC] at this

/-- From bounds in every truncated weight to a chart in the weight `X₀^γ`. -/
lemma chart_of_trunc {γ : ℝ} (v : L2H') {C : ℝ} (hC : 0 ≤ C) (h : ∀ (n : ℕ) (hn : 0 < n), ‖mulCL (sb_Wn γ n hn) v‖ ≤ C) :
    ∃ G : L2H', ((G : UpperHalfPlane → ℂ) =ᵐ[volume] fun z => ((omG γ z : ℝ) : ℂ) * v z) ∧ ‖G‖ ≤ C := by
  refine exists_chart_of_lint (measurable_omG γ) (fun z => (Real.rpow_pos_of_pos (Real.cosh_pos _) _).le) v hC ?_
  refine fatou_W v fun n => ?_
  rw [lint_W (sb_Wn γ (n + 1) n.succ_pos) (fun w hw => Wn_pos γ (n + 1) n.succ_pos hw)]
  exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (h (n + 1) n.succ_pos) 2)

/-- The truncated weights are below the chart. -/
lemma norm_trunc_le_chart {γ : ℝ} {h H : L2H'} (hH : (H : UpperHalfPlane → ℂ) =ᵐ[volume] fun z => ((omG γ z : ℝ) : ℂ) * h z)
    (n : ℕ) (hn : 0 < n) : ‖mulCL (sb_Wn γ n hn) h‖ ≤ ‖H‖ := by
  have h1 := lint_Wn_le (γ := γ) h n hn
  have h2 : ∫⁻ z : UpperHalfPlane, (ENNReal.ofReal (omG γ z) * ‖h z‖ₑ) ^ 2 = ENNReal.ofReal (‖H‖ ^ 2) := by
    rw [← lintegral_enorm_sq_eq]
    refine lintegral_congr_ae ?_
    filter_upwards [hH] with z hz
    have hp : 0 ≤ omG γ z := (Real.rpow_pos_of_pos (Real.cosh_pos _) _).le
    rw [hz, enorm_mul, ← ofReal_norm_eq_enorm ((omG γ z : ℝ) : ℂ), Complex.norm_real, Real.norm_of_nonneg hp]
  rw [h2] at h1
  have h3 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h1
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h3

/-- The constant of the word bound in the weight `X₀^β`. -/
noncomputable def K3p (β : ℝ) : ℝ := (4 + 2 * β) * (Real.exp 1 * (2 * cH))

lemma one_le_K3p {β : ℝ} (hβ : 0 ≤ β) : 1 ≤ K3p β := by
  unfold K3p
  have hc : 1 ≤ cH := by
    unfold cH
    have := Real.exp_pos (-1)
    linarith
  have he : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have h1 : (4 : ℝ) ≤ 4 + 2 * β := by linarith
  have h2 : (4 : ℝ) ≤ Real.exp 1 * (2 * cH) := by nlinarith
  calc (1 : ℝ) ≤ 4 * 4 := by norm_num
    _ ≤ (4 + 2 * β) * (Real.exp 1 * (2 * cH)) := mul_le_mul h1 h2 (by norm_num) (by linarith)

section pc

variable {β m σ : ℝ} (hβ : 0 ≤ β) (hm : 1 / 2 ≤ m) (hml : 2 * (β + 1 / 2) ^ 2 < m ^ 2) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
include hβ hm hml hσ hσ1

/-- **Words of `e^{-σΛ_m} h` in the weight `X₀^β`.** -/
theorem pc_word_chart {h H : L2H'} (hH : (H : UpperHalfPlane → ℂ) =ᵐ[volume] fun z => ((omG β z : ℝ) : ℂ) * h z) (S : List Bool) :
    ∃ G : L2H', ((G : UpperHalfPlane → ℂ) =ᵐ[volume] fun z => ((omG β z : ℝ) : ℂ) * wordAct S (vE m σ h 0) z)
      ∧ ‖G‖ ≤ √2 * ((S.length : ℝ) + 1) * S.length.factorial * (K3p β / σ) ^ S.length * ‖H‖ := by
  have hc := cH_pos
  have hK0 : 0 < K3p β := lt_of_lt_of_le one_pos (one_le_K3p hβ)
  refine chart_of_trunc _ (by positivity) fun n hn => ?_
  obtain ⟨C', hWS⟩ := waveS_Wn hβ n hn
  have h1 := words_w hWS hm hml hσ hσ1 h 0 S
  rw [mulCL_congr_C hWS.sb (sb_Wn β n hn), mulCL_congr_C hWS.sb (sb_Wn β n hn) h] at h1
  have h2 := norm_trunc_le_chart hH n hn
  have hk : (0 : ℝ) ≤ S.length := Nat.cast_nonneg _
  have e : (K3p β / σ) ^ S.length = (4 + 2 * β) ^ S.length * (Real.exp 1 * (2 * cH) / σ) ^ S.length := by
    unfold K3p
    rw [← mul_pow]
    congr 1
    ring
  have hp : 0 ≤ (4 + 2 * β) ^ S.length * (Real.exp 1 * (2 * cH) / σ) ^ (S.length + 2 * 0) * ((S.length + 2 * 0).factorial : ℝ) := by positivity
  calc ‖mulCL (sb_Wn β n hn) (wordAct S (vE m σ h 0))‖
      ≤ √2 * ‖mulCL (sb_Wn β n hn) h‖ * (4 + 2 * β) ^ S.length * (Real.exp 1 * (2 * cH) / σ) ^ (S.length + 2 * 0)
        * ((S.length + 2 * 0).factorial : ℝ) := h1
    _ ≤ √2 * ‖H‖ * (4 + 2 * β) ^ S.length * (Real.exp 1 * (2 * cH) / σ) ^ (S.length + 2 * 0) * ((S.length + 2 * 0).factorial : ℝ) := by
        gcongr
    _ = 1 * (√2 * (S.length.factorial : ℝ) * (K3p β / σ) ^ S.length * ‖H‖) := by
        rw [e]
        simp only [mul_zero, add_zero]
        ring
    _ ≤ ((S.length : ℝ) + 1) * (√2 * (S.length.factorial : ℝ) * (K3p β / σ) ^ S.length * ‖H‖) := by
        refine mul_le_mul_of_nonneg_right (by linarith) ?_
        positivity
    _ = _ := by ring

/-- **(WB-w) for `e^{-σΛ_m} h` in the weight `X₀^β`.** -/
theorem pc_wb_w {h H : L2H'} (hH : (H : UpperHalfPlane → ℂ) =ᵐ[volume] fun z => ((omG β z : ℝ) : ℂ) * h z)
    {ħ : ℝ} (hħ : 0 < ħ) (hħ1 : ħ ≤ 1) (N : ℕ) {s₁ : ℝ} (hs₁ : 0 ≤ s₁) (ss : List ℝ) (hss : ∀ s ∈ ss, 0 ≤ s)
    (J : List Bool) {n : ℕ} (hJ : J.length ≤ n) :
    WordDom J (polyAct (bP ħ N s₁ ss) (vE m σ h 0)) ∧ ∃ G : L2H',
      ((G : UpperHalfPlane → ℂ) =ᵐ[volume] fun z => ((omG β z : ℝ) : ℂ) * wordAct J (polyAct (bP ħ N s₁ ss) (vE m σ h 0)) z) ∧
      ‖G‖ ≤ √2 * C4 (K3p β) ^ (N + ss.length + n) * (2 * N).factorial * (n + 2 * ss.length).factorial
        * (σ⁻¹) ^ (n + 2 * ss.length) * ((σ * ħ)⁻¹) ^ (2 * N) * ‖H‖ := by
  have hA := vE_allWords hm hσ hσ1 h 0
  choose Gw hGw1 hGw2 using fun S => pc_word_chart hβ hm hml hσ hσ1 hH S
  exact wb_w_gen hA (fun z => ((omG β z : ℝ) : ℂ)) Gw hGw1 (by positivity) (one_le_K3p hβ) (norm_nonneg _) hGw2 hħ hħ1 hσ hσ1 N hs₁ ss hss J hJ

end pc

end Qschubert
