import Qschubert.KLCor16c

/-!
# Corollary 1.6R, smooth-amplitude version

`cor16R_smooth : Stmt_cor16R_smooth`. The Sobolev bound `sobolev_M` is applied to `Δ_M^N E`, whose norm and the norm of its Laplacian are bounded by Theorem 1.4R at `N` and `N + 1`.
(The paper's Corollary uses `Δ²`; one Laplacian suffices here, since `sobolev_M` needs only `Dom(-Δ_M)`.)
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set Physicslib4.Spectral Physicslib4.Spectral.Unbounded UpperHalfPlane
open scoped ENNReal InnerProductSpace MatrixGroups Pointwise ComplexConjugate

section

variable {X H : Type*} [MeasurableSpace X] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (μ : ProjectionValuedMeasure X H)

/-- Converse of the domain part of `pmap_comp`. -/
theorem pmap_comp_mem {f g : X → ℂ} (hf : Measurable f) (hg : Measurable g) (ψ : integralDomain μ f)
    (h : (ψ : H) ∈ integralDomain μ (g * f)) : pmapIntegral μ f ψ ∈ integralDomain μ g := by
  have hd : Measurable fun x => ‖f x‖ₑ ^ 2 := hf.enorm.pow_const 2
  have hgfm : Measurable (g * f) := hg.mul hf
  rw [mem_integralDomain, assoc_pmap μ hf ψ]
  have hgr : AEStronglyMeasurable g ((μ.assoc (ψ : H)).withDensity fun x => ‖f x‖ₑ ^ 2) := hg.aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hgr, integrable_withDensity_iff_integrable_smul' hd
    (Eventually.of_forall fun _ => ENNReal.pow_lt_top enorm_lt_top)]
  have h0 := (mem_integralDomain μ).1 h
  rw [memLp_two_iff_integrable_sq_norm hgfm.aestronglyMeasurable] at h0
  refine (integrable_congr (Eventually.of_forall fun x => ?_)).1 h0
  simp only [ENNReal.toReal_pow, toReal_enorm, smul_eq_mul, Pi.mul_apply, norm_mul, mul_pow]
  ring

end

section

variable (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ]

local notation "L2M" => Lp ℂ 2 (surfMeasure Γ)

/-- `Δ_M^N E ∈ Dom(-Δ_M)` when `E ∈ Dom Δ_M^{N+1}`, and `-Δ_M Δ_M^N E = -Δ_M^{N+1} E` up to the sign convention. -/
theorem lapPow_succ (N : ℕ) (E : L2M) (hN : E ∈ (lapPowM Γ N).domain) (hN1 : E ∈ (lapPowM Γ (N + 1)).domain) :
    ∃ h : lapPowM Γ N ⟨E, hN⟩ ∈ (negLapMH Γ).domain, negLapMH Γ ⟨lapPowM Γ N ⟨E, hN⟩, h⟩ = -lapPowM Γ (N + 1) ⟨E, hN1⟩ := by
  set μ := spectralMeasure (negLapMH_isSelfAdjoint Γ) with hμ
  set f : ℝ → ℂ := fun s : ℝ => (((-s) ^ N : ℝ) : ℂ) with hf_def
  set g : ℝ → ℂ := fun s : ℝ => ((-s : ℝ) : ℂ) with hg_def
  have hf : Measurable f := by rw [hf_def]; fun_prop
  have hg : Measurable g := by rw [hg_def]; fun_prop
  have hfun : g * f = fun s : ℝ => (((-s) ^ (N + 1) : ℝ) : ℂ) := by
    funext s
    simp [hf_def, hg_def, pow_succ, mul_comm]
  have hEf : E ∈ integralDomain μ f := hN
  have hEgf : E ∈ integralDomain μ (g * f) := by
    rw [hfun]; exact hN1
  have hφ : pmapIntegral μ f ⟨E, hEf⟩ ∈ integralDomain μ g := pmap_comp_mem μ hf hg ⟨E, hEf⟩ hEgf
  have hcc : (fun _ : ℝ => (-1 : ℂ)) ∈ BddMeasurable ℝ := ⟨measurable_const, 1, fun _ => by simp⟩
  have hid : pmapIntegral μ f ⟨E, hEf⟩ ∈ integralDomain μ (fun x : ℝ => (x : ℂ)) := by
    have h1 := mem_integralDomain_mul_of_bdd μ hg hcc hφ
    have e : (fun _ : ℝ => (-1 : ℂ)) * g = fun x : ℝ => (x : ℂ) := by
      funext s; simp [hg_def]
    rwa [e] at h1
  have hu : lapPowM Γ N ⟨E, hN⟩ ∈ (negLapMH Γ).domain := by
    rw [A_domain_eq (negLapMH_isSelfAdjoint Γ)]; exact hid
  refine ⟨hu, ?_⟩
  obtain ⟨hn, en⟩ := pmap_neg_id _ hu
  obtain ⟨hmem, ev⟩ := pmap_comp μ hf hg ⟨E, hEf⟩ hφ
  have e1 : lapPowM Γ (N + 1) ⟨E, hN1⟩ = pmapIntegral μ (g * f) ⟨E, hmem⟩ :=
    (pmapIntegral_congr_fun μ hfun E hmem hN1).symm
  rw [e1, ev]
  have e2 : pmapIntegral μ g ⟨pmapIntegral μ f ⟨E, hEf⟩, hφ⟩ = -negLapMH Γ ⟨lapPowM Γ N ⟨E, hN⟩, hu⟩ := en
  exact neg_eq_iff_eq_neg.1 e2.symm

lemma errNorm_le {n : ℕ} {E : L2M} {B : ℝ} (hB : 0 ≤ B) (h : errNormM Γ n E ≤ ENNReal.ofReal B) :
    ∃ hd : E ∈ (lapPowM Γ n).domain, ‖lapPowM Γ n ⟨E, hd⟩‖ ≤ B := by
  unfold errNormM at h
  split_ifs at h with hd
  · refine ⟨hd, ?_⟩
    rw [← ofReal_norm] at h
    exact (ENNReal.ofReal_le_ofReal_iff hB).1 h
  · exact absurd h (by simp)

end

lemma six_pow_ge (N : ℕ) : ((2 * N + 2 : ℕ) : ℝ) * ((2 * N + 1 : ℕ) : ℝ) ≤ 6 ^ (N + 1) := by
  induction N with
  | zero => norm_num
  | succ n ih =>
    push_cast at ih ⊢
    rw [pow_succ]
    nlinarith [sq_nonneg (n : ℝ), (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

lemma pow_fact_le (N : ℕ) : ((N + 1 : ℕ) : ℝ) ^ (2 * (N + 1)) ≤ 54 ^ (N + 1) * ((2 * N).factorial : ℝ) := by
  set n := 2 * (N + 1) with hn
  have h1 : ((N + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
    rw [hn]; push_cast; linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have h2 := Real.pow_div_factorial_le_exp (n : ℝ) (Nat.cast_nonneg n) n
  have hf : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
  rw [div_le_iff₀ hf] at h2
  have hfe : (n.factorial : ℝ) = ((2 * N + 2 : ℕ) : ℝ) * ((2 * N + 1 : ℕ) : ℝ) * ((2 * N).factorial : ℝ) := by
    rw [hn, show 2 * (N + 1) = 2 * N + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
    push_cast; ring
  have he : Real.exp (n : ℝ) ≤ 9 ^ (N + 1) := by
    have e : Real.exp (n : ℝ) = (Real.exp 1 ^ 2) ^ (N + 1) := by
      rw [← pow_mul, ← Real.exp_nat_mul, hn]; congr 1; push_cast; ring
    rw [e]
    refine pow_le_pow_left₀ (by positivity) ?_ _
    have h3 := Real.exp_one_lt_three
    have h4 := Real.exp_pos 1
    nlinarith
  have hf2 : (0 : ℝ) ≤ ((2 * N).factorial : ℝ) := Nat.cast_nonneg _
  calc ((N + 1 : ℕ) : ℝ) ^ (2 * (N + 1)) ≤ (n : ℝ) ^ n := pow_le_pow_left₀ (Nat.cast_nonneg _) h1 _
    _ ≤ Real.exp n * (n.factorial : ℝ) := h2
    _ ≤ 9 ^ (N + 1) * (6 ^ (N + 1) * ((2 * N).factorial : ℝ)) := by
        rw [hfe]
        exact mul_le_mul he (mul_le_mul_of_nonneg_right (six_pow_ge N) hf2) (by positivity) (by positivity)
    _ = 54 ^ (N + 1) * ((2 * N).factorial : ℝ) := by
        rw [show (54 : ℝ) = 9 * 6 by norm_num, mul_pow]; ring

lemma pow_fact_le' (N : ℕ) : (N : ℝ) ^ (2 * N) ≤ 54 ^ (N + 1) * ((2 * N).factorial : ℝ) := by
  have h : (N : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by push_cast; linarith
  have h1 : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by push_cast; linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  calc (N : ℝ) ^ (2 * N) ≤ ((N + 1 : ℕ) : ℝ) ^ (2 * N) := pow_le_pow_left₀ (Nat.cast_nonneg _) h _
    _ ≤ ((N + 1 : ℕ) : ℝ) ^ (2 * (N + 1)) := pow_le_pow_right₀ h1 (by omega)
    _ ≤ _ := pow_fact_le N

/-- The arithmetic of the corollary. -/
lemma pt_arith {C K₀ X Y : ℝ} {K N : ℕ} (hC : 0 < C) (hK₀ : 0 ≤ K₀) (hX : 1 ≤ X) (hY : 0 ≤ Y) :
    K₀ * (C ^ (N + K + 1) * (N : ℝ) ^ (2 * N) * (K.factorial : ℝ) * X ^ (2 * N) * Y
        + C ^ (N + 1 + K + 1) * ((N + 1 : ℕ) : ℝ) ^ (2 * (N + 1)) * (K.factorial : ℝ) * X ^ (2 * (N + 1)) * Y)
      ≤ (2 * (K₀ + 1) * (max C 1) ^ 2 * 54) ^ (N + K + 1) * ((2 * N).factorial : ℝ) * (K.factorial : ℝ) * X ^ (2 * N + 2) * Y := by
  set C₁ := max C 1 with hC₁
  have hC₁1 : 1 ≤ C₁ := le_max_right _ _
  have hCC : C ≤ C₁ := le_max_left _ _
  set M := N + K + 1 with hM
  set Q : ℝ := ((2 * N).factorial : ℝ) with hQ
  set F : ℝ := (K.factorial : ℝ) with hF
  have hQ0 : 0 ≤ Q := Nat.cast_nonneg _
  have hF0 : 0 ≤ F := Nat.cast_nonneg _
  have hX0 : 0 ≤ X := by linarith
  set T : ℝ := C₁ ^ (M + 1) * ((54 : ℝ) ^ (N + 1) * Q) * F * X ^ (2 * N + 2) * Y with hT
  have hT0 : 0 ≤ T := by positivity
  have t1 : C ^ M * (N : ℝ) ^ (2 * N) * F * X ^ (2 * N) * Y ≤ T := by
    have a1 : C ^ M ≤ C₁ ^ (M + 1) :=
      (pow_le_pow_left₀ hC.le hCC M).trans (pow_le_pow_right₀ hC₁1 (by omega))
    have a2 := pow_fact_le' N
    have a3 : X ^ (2 * N) ≤ X ^ (2 * N + 2) := pow_le_pow_right₀ hX (by omega)
    rw [hT]
    gcongr
  have t2 : C ^ (N + 1 + K + 1) * ((N + 1 : ℕ) : ℝ) ^ (2 * (N + 1)) * F * X ^ (2 * (N + 1)) * Y ≤ T := by
    have a1 : C ^ (N + 1 + K + 1) ≤ C₁ ^ (M + 1) := by
      rw [show N + 1 + K + 1 = M + 1 by omega]
      exact pow_le_pow_left₀ hC.le hCC _
    have a2 := pow_fact_le N
    have a3 : X ^ (2 * (N + 1)) ≤ X ^ (2 * N + 2) := pow_le_pow_right₀ hX (by omega)
    rw [hT]
    gcongr
  have step1 : K₀ * (C ^ M * (N : ℝ) ^ (2 * N) * F * X ^ (2 * N) * Y
      + C ^ (N + 1 + K + 1) * ((N + 1 : ℕ) : ℝ) ^ (2 * (N + 1)) * F * X ^ (2 * (N + 1)) * Y) ≤ 2 * (K₀ + 1) * T := by
    have := mul_le_mul_of_nonneg_left (add_le_add t1 t2) hK₀
    nlinarith
  refine step1.trans ?_
  have hA : 1 ≤ 2 * (K₀ + 1) := by linarith
  have hMpos : 1 ≤ M := by omega
  have b1 : 2 * (K₀ + 1) ≤ (2 * (K₀ + 1)) ^ M := by
    calc 2 * (K₀ + 1) = (2 * (K₀ + 1)) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ hA hMpos
  have b2 : C₁ ^ (M + 1) ≤ (C₁ ^ 2) ^ M := by
    rw [← pow_mul]; exact pow_le_pow_right₀ hC₁1 (by omega)
  have b3 : (54 : ℝ) ^ (N + 1) ≤ 54 ^ M := pow_le_pow_right₀ (by norm_num) (by omega)
  have e : (2 * (K₀ + 1) * C₁ ^ 2 * 54) ^ M * Q * F * X ^ (2 * N + 2) * Y
      = (2 * (K₀ + 1)) ^ M * ((C₁ ^ 2) ^ M * ((54 : ℝ) ^ M * Q)) * F * X ^ (2 * N + 2) * Y := by
    rw [mul_pow, mul_pow]; ring
  have e2 : 2 * (K₀ + 1) * T = 2 * (K₀ + 1) * (C₁ ^ (M + 1) * ((54 : ℝ) ^ (N + 1) * Q)) * F * X ^ (2 * N + 2) * Y := by
    rw [hT]; ring
  rw [e, e2]
  gcongr

/-- **Corollary 1.6R**, smooth-amplitude version. -/
theorem cor16R_smooth : Stmt_cor16R_smooth := by
  intro Γ _ hOr x₀ β κ α₀ r₀ hβ hκ hα₀ hα₁ hr₀ hinj
  obtain ⟨C, δ, hC, hδ, hmain⟩ := thm14R_smooth Γ hOr x₀ β κ α₀ hβ hκ hα₀ hα₁
  obtain ⟨K₀, hK₀, hS⟩ := sobolev_M hr₀
  set C' : ℝ := 2 * (K₀ + 1) * (max C 1) ^ 2 * 54 with hC'
  have hC'0 : 0 < C' := by
    have : 0 < max C 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    positivity
  refine ⟨C', δ, hC'0, hδ, ?_⟩
  intro ħ α t K N g a hħ hħ1 hα hαα hκc hg ht htδ hsm hfin
  obtain ⟨hv, hw, hN⟩ := hmain ħ α t K N g a hħ hħ1 hα hαα hκc hg ht htδ hsm hfin
  obtain ⟨hv', hw', hN1⟩ := hmain ħ α t K (N + 1) g a hħ hħ1 hα hαα hκc hg ht htδ hsm hfin
  refine ⟨hv, hw, ?_⟩
  set S : ℝ := (swNormX x₀ α β a).toReal with hSdef
  have hS0 : 0 ≤ S := ENNReal.toReal_nonneg
  have hSe : swNormX x₀ α β a = ENNReal.ofReal S := (ENNReal.ofReal_toReal hfin.ne).symm
  set E := errVec Γ ħ t hv hw with hE
  have hd0 : ∀ n, 0 ≤ ddBound C α ħ t K n := fun n => ddBound_nonneg K n hC.le hα hħ ht
  rw [hSe, ← ENNReal.ofReal_mul (hd0 N)] at hN
  rw [hSe, ← ENNReal.ofReal_mul (hd0 (N + 1))] at hN1
  obtain ⟨hdN, hbN⟩ := errNorm_le Γ (n := N) (E := E) (mul_nonneg (hd0 N) hS0) hN
  obtain ⟨hdN1, hbN1⟩ := errNorm_le Γ (n := N + 1) (E := E) (mul_nonneg (hd0 (N + 1)) hS0) hN1
  obtain ⟨hu, hAu⟩ := lapPow_succ Γ N E hdN hdN1
  obtain ⟨f, hfc, hfa, hfb⟩ := hS Γ hinj ⟨lapPowM Γ N ⟨E, hdN⟩, hu⟩
  refine ⟨hdN, f, hfc, hfa, fun x => ?_⟩
  have hX : 1 ≤ (α * ħ)⁻¹ := by
    have h1 : α < 1 := lt_of_le_of_lt hαα (lt_of_lt_of_le hα₁ (min_le_left _ _))
    have h2 : α * ħ ≤ 1 := by nlinarith
    exact (one_le_inv₀ (mul_pos hα hħ)).2 h2
  have hY : 0 ≤ (ħ * t / α ^ 2) ^ (K + 1) := by positivity
  have hb : ‖f x‖ ≤ ptBound C' α ħ t K N * S := by
    refine (hfb x).trans ?_
    have e1 : ‖negLapMH Γ ⟨lapPowM Γ N ⟨E, hdN⟩, hu⟩‖ = ‖lapPowM Γ (N + 1) ⟨E, hdN1⟩‖ := by
      rw [hAu, norm_neg]
    show K₀ * (‖lapPowM Γ N ⟨E, hdN⟩‖ + ‖negLapMH Γ ⟨lapPowM Γ N ⟨E, hdN⟩, hu⟩‖) ≤ _
    rw [e1]
    have h1 : K₀ * (‖lapPowM Γ N ⟨E, hdN⟩‖ + ‖lapPowM Γ (N + 1) ⟨E, hdN1⟩‖)
        ≤ K₀ * (ddBound C α ħ t K N * S + ddBound C α ħ t K (N + 1) * S) :=
      mul_le_mul_of_nonneg_left (add_le_add hbN hbN1) hK₀
    refine h1.trans ?_
    have h2 := pt_arith (K := K) (N := N) hC hK₀ hX hY
    have h3 := mul_le_mul_of_nonneg_right h2 hS0
    refine le_trans (le_of_eq ?_) (h3.trans (le_of_eq ?_))
    · unfold ddBound; ring
    · unfold ptBound; rw [← hC']
  have hpt : 0 ≤ ptBound C' α ħ t K N := by
    unfold ptBound
    have := (Nat.cast_nonneg (2 * N).factorial : (0 : ℝ) ≤ _)
    have := (Nat.cast_nonneg K.factorial : (0 : ℝ) ≤ _)
    have := inv_pos.2 (mul_pos hα hħ)
    positivity
  show ‖f x‖ₑ ≤ ENNReal.ofReal (ptBound C' α ħ t K N) * swNormX x₀ α β a
  rw [hSe, ← ENNReal.ofReal_mul hpt, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal hb

end Qschubert
