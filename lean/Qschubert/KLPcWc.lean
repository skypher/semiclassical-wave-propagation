import Qschubert.KLPcWb

/-!
# Words in weighted spaces, part 3: the semigroup `e^{-σΛ_m}`

`vE m σ f j = Λ_m^{2j} e^{-σΛ_m} f`. All words act on it (`vE_allWords`), `-Δ vE_j = vE_{j+1} - (m² - 1/4) vE_j` (`vE_step`), and for a
weight with `|∇ log W| ≤ l`, `2(l + 1/2)² < m²`:

`‖W Z_S vE_j‖ ≤ √2 ‖W f‖ (4 + 2l)^k (2e c_H/σ)^{k+2j} (k + 2j)!`, `k = |S|` (`words_w`).

Also `e^{-σΛ_m} f ∈ Dom(e^{σΛ})` with `‖e^{σΛ} e^{-σΛ_m} f‖ ≤ ‖f‖` (`vE_exp`).
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set Physicslib4.Spectral Physicslib4.Spectral.Unbounded
open scoped ENNReal InnerProductSpace ComplexConjugate UpperHalfPlane

local notation "L2H'" => Lp ℂ 2 (volume : Measure UpperHalfPlane)

/-- **`e^{aΛ}` on a bounded multiplier with exponential decay.** -/
theorem spec_exp {G : ℝ → ℂ} (hG : G ∈ BddMeasurable ℝ) {a : ℝ} (hfg : fExp a * G ∈ BddMeasurable ℝ) (v : L2H') :
    ∃ h : specE.integral G v ∈ (expLambda a).domain, expLambda a ⟨specE.integral G v, h⟩ = specE.integral (fExp a * G) v := by
  have hmem := integral_apply_mem_integralDomain specE (measurable_fExp a) hG hfg v
  have hcomp := pmapIntegral_integral_apply specE (measurable_fExp a) hG hfg v
  have hd : specE.integral G v ∈ (expLambda a).domain := by
    rw [expLambda, functionalCalculus_domain]
    exact hmem
  exact ⟨hd, hcomp⟩

lemma sqrt_le_sM {m : ℝ} (hm : 1 / 2 ≤ m) (s : ℝ) : √s ≤ sM m s := by
  unfold sM
  refine Real.sqrt_le_sqrt ?_
  have : (1 / 2 : ℝ) ^ 2 ≤ m ^ 2 := pow_le_pow_left₀ (by norm_num) hm 2
  linarith

lemma sM_sq {m : ℝ} (hm : 1 / 2 ≤ m) {s : ℝ} (hs : 0 ≤ s) : sM m s ^ 2 = s - 1 / 4 + m ^ 2 := by
  unfold sM
  have : (1 / 2 : ℝ) ^ 2 ≤ m ^ 2 := pow_le_pow_left₀ (by norm_num) hm 2
  exact Real.sq_sqrt (by linarith)

lemma rWM_succ (m : ℝ) (j : ℕ) (σ x : ℝ) : rWM m (j + 1) σ x = sM m x ^ 2 * rWM m j σ x := by
  unfold rWM
  rw [show 2 * (j + 1) = 2 * j + 2 by ring, pow_add]
  ring

lemma rWM_nonneg (m : ℝ) (j : ℕ) (σ x : ℝ) : 0 ≤ rWM m j σ x :=
  mul_nonneg (pow_nonneg (sM_nonneg m x) _) (Real.exp_pos _).le

lemma fExp_GWM_le {m : ℝ} (hm : 1 / 2 ≤ m) {a σ : ℝ} (ha : 0 ≤ a) (haσ : a < σ) (j : ℕ) (s : ℝ) :
    ‖fExp a s * GWM m j σ s‖ ≤ ((2 * j).factorial : ℝ) / (σ - a) ^ (2 * j) := by
  have hs := sqrt_le_sM hm s
  have h0 := sM_nonneg m s
  show ‖((Real.exp (a * Real.sqrt s) : ℝ) : ℂ) * ((rWM m j σ s : ℝ) : ℂ)‖ ≤ _
  rw [← Complex.ofReal_mul, Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (rWM_nonneg m j σ s))]
  unfold rWM
  have e : Real.exp (a * √s) * Real.exp (-(σ * sM m s)) ≤ Real.exp (-((σ - a) * sM m s)) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    nlinarith
  have h1 : Real.exp (a * √s) * (sM m s ^ (2 * j) * Real.exp (-(σ * sM m s))) ≤ sM m s ^ (2 * j) * Real.exp (-((σ - a) * sM m s)) := by
    calc _ = sM m s ^ (2 * j) * (Real.exp (a * √s) * Real.exp (-(σ * sM m s))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left e (pow_nonneg h0 _)
  exact h1.trans (pow_mul_exp_le_fac (by linarith) h0 _)

lemma fExp_GWM_mem {m : ℝ} (hm : 1 / 2 ≤ m) {a σ : ℝ} (ha : 0 ≤ a) (haσ : a < σ) (j : ℕ) : fExp a * GWM m j σ ∈ BddMeasurable ℝ := by
  rw [mem_bddMeasurable]
  exact ⟨(measurable_fExp a).mul (GWM_mem m j (ha.trans_lt haσ)).1, _, fun s => fExp_GWM_le hm ha haσ j s⟩

lemma fExp_GWM_zero_le {m : ℝ} (hm : 1 / 2 ≤ m) {σ : ℝ} (hσ : 0 ≤ σ) (s : ℝ) : ‖fExp σ s * GWM m 0 σ s‖ ≤ 1 := by
  have hs := sqrt_le_sM hm s
  show ‖((Real.exp (σ * Real.sqrt s) : ℝ) : ℂ) * ((rWM m 0 σ s : ℝ) : ℂ)‖ ≤ _
  rw [← Complex.ofReal_mul, Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (rWM_nonneg m 0 σ s))]
  unfold rWM
  rw [mul_zero, pow_zero, one_mul, ← Real.exp_add]
  refine Real.exp_le_one_iff.2 ?_
  nlinarith

/-- `Λ_m^{2j} e^{-σΛ_m} f`. -/
noncomputable def vE (m σ : ℝ) (f : L2H') (j : ℕ) : L2H' := specE.integral (GWM m j σ) f

section vE

variable {m σ : ℝ} (hm : 1 / 2 ≤ m) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
include hm hσ

/-- `e^{-σΛ_m} f` is an analytic vector of radius `σ`, with norm at most `‖f‖`. -/
theorem vE_exp (f : L2H') : ∃ h : vE m σ f 0 ∈ (expLambda σ).domain, ‖expLambda σ ⟨vE m σ f 0, h⟩‖ ≤ ‖f‖ := by
  have hmem : fExp σ * GWM m 0 σ ∈ BddMeasurable ℝ := by
    rw [mem_bddMeasurable]
    exact ⟨(measurable_fExp σ).mul (GWM_mem m 0 hσ).1, 1, fun s => fExp_GWM_zero_le hm hσ.le s⟩
  obtain ⟨h, he⟩ := spec_exp (GWM_mem m 0 hσ) hmem f
  refine ⟨h, ?_⟩
  show ‖expLambda σ ⟨specE.integral (GWM m 0 σ) f, h⟩‖ ≤ ‖f‖
  rw [he]
  have h1 : ‖specE.integral (fExp σ * GWM m 0 σ)‖ ≤ 1 :=
    (specE.norm_integral_le hmem).trans (ciSup_le fun s => fExp_GWM_zero_le hm hσ.le s)
  calc ‖specE.integral (fExp σ * GWM m 0 σ) f‖ ≤ ‖specE.integral (fExp σ * GWM m 0 σ)‖ * ‖f‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖f‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ = ‖f‖ := one_mul _

include hσ1

lemma vE_allWords (f : L2H') (j : ℕ) : AllWords (vE m σ f j) := by
  have ha : 0 < σ / 2 := by positivity
  obtain ⟨h, -⟩ := spec_exp (GWM_mem m j hσ) (fExp_GWM_mem hm ha.le (by linarith : σ / 2 < σ) j) f
  exact allWords_of_exp ha (by linarith) h

omit hσ1

/-- The cutoff with symbol `Λ_m^{2j} e^{-σΛ_m}` on `[0, ∞)`. -/
noncomputable def chiW (j : ℕ) : Cutoff where
  r := fun x => if 0 ≤ x then rWM m j σ x else 0
  meas := Measurable.ite measurableSet_Ici (measurable_rWM m j σ) measurable_const
  C := ((2 * j).factorial : ℝ) / σ ^ (2 * j) + ((2 * (j + 1)).factorial : ℝ) / σ ^ (2 * (j + 1))
  bound x := by
    have h0 : 0 ≤ ((2 * j).factorial : ℝ) / σ ^ (2 * j) := by positivity
    have h1 : 0 ≤ ((2 * (j + 1)).factorial : ℝ) / σ ^ (2 * (j + 1)) := by positivity
    split_ifs with hx
    · exact (abs_rWM_le m hσ x).trans (by linarith)
    · rw [abs_zero]; linarith
  bound1 x := by
    have h0 : 0 ≤ ((2 * j).factorial : ℝ) / σ ^ (2 * j) := by positivity
    have h1 : 0 ≤ ((2 * (j + 1)).factorial : ℝ) / σ ^ (2 * (j + 1)) := by positivity
    split_ifs with hx
    · have hr := rWM_nonneg m j σ x
      rw [abs_of_nonneg (mul_nonneg (by linarith) hr)]
      have e1 := abs_rWM_le m (j := j) hσ x
      have e2 := abs_rWM_le m (j := j + 1) hσ x
      rw [abs_of_nonneg hr] at e1
      rw [abs_of_nonneg (rWM_nonneg m (j + 1) σ x), rWM_succ, sM_sq hm hx] at e2
      have hm2 : (1 / 2 : ℝ) ^ 2 ≤ m ^ 2 := pow_le_pow_left₀ (by norm_num) hm 2
      nlinarith
    · rw [mul_zero, abs_zero]; linarith

lemma chiW_J (j : ℕ) (f : L2H') : (chiW hm hσ j).J f = vE m σ f j := by
  have h := integral_congr_nonneg (chiW hm hσ j).g_mem (GWM_mem m j hσ) (fun s hs => by
    show (((if 0 ≤ s then rWM m j σ s else 0 : ℝ)) : ℂ) = ((rWM m j σ s : ℝ) : ℂ)
    simp only [hs, ↓reduceIte])
  exact congrArg (fun T : L2H' →L[ℂ] L2H' => T f) h

lemma chiW_gS (j : ℕ) :
    (chiW hm hσ j).gS = (chiW hm hσ (j + 1)).g + (-((m ^ 2 - 1 / 4 : ℝ) : ℂ)) • (chiW hm hσ j).g := by
  funext s
  show (((s * (if 0 ≤ s then rWM m j σ s else 0) : ℝ)) : ℂ)
    = (((if 0 ≤ s then rWM m (j + 1) σ s else 0 : ℝ)) : ℂ) + (-((m ^ 2 - 1 / 4 : ℝ) : ℂ)) * (((if 0 ≤ s then rWM m j σ s else 0 : ℝ)) : ℂ)
  split_ifs with hs
  · rw [rWM_succ, sM_sq hm hs]
    push_cast
    ring
  · simp

include hσ1

/-- **`-Δ vE_j = vE_{j+1} - (m² - 1/4) vE_j`.** -/
theorem vE_step (f : L2H') (j : ℕ) :
    negLapH ⟨vE m σ f j, AllWords.mem (vE_allWords hm hσ hσ1 f j) []⟩
      = vE m σ f (j + 1) - ((m ^ 2 - 1 / 4 : ℝ) : ℂ) • vE m σ f j := by
  have h1 := (chiW hm hσ j).negLapH_J f
  have hJS : (chiW hm hσ j).JS f = (chiW hm hσ (j + 1)).J f - ((m ^ 2 - 1 / 4 : ℝ) : ℂ) • (chiW hm hσ j).J f := by
    have e : (chiW hm hσ j).JS = specE.integral ((chiW hm hσ (j + 1)).g + (-((m ^ 2 - 1 / 4 : ℝ) : ℂ)) • (chiW hm hσ j).g) := by
      rw [← chiW_gS hm hσ j]
      rfl
    rw [e, specE.integral_add (chiW hm hσ (j + 1)).g_mem ((BddMeasurable ℝ).smul_mem _ (chiW hm hσ j).g_mem),
      specE.integral_smul _ (chiW hm hσ j).g_mem]
    show (chiW hm hσ (j + 1)).J f + (-((m ^ 2 - 1 / 4 : ℝ) : ℂ)) • (chiW hm hσ j).J f = _
    rw [neg_smul, ← sub_eq_add_neg]
  have e0 : (⟨vE m σ f j, AllWords.mem (vE_allWords hm hσ hσ1 f j) []⟩ : negLapH.domain)
      = ⟨(chiW hm hσ j).J f, (chiW hm hσ j).J_mem f⟩ := Subtype.ext (chiW_J hm hσ j f).symm
  rw [e0, h1, hJS, chiW_J, chiW_J]

end vE

/-- **Words of `Λ_m^{2j} e^{-σΛ_m} f` in the weight `W`.** -/
theorem words_w {W : ℂ → ℝ} {C l : ℝ} (hW : WaveS W C l) {m : ℝ} (hm : 1 / 2 ≤ m) (hml : 2 * (l + 1 / 2) ^ 2 < m ^ 2)
    {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (f : L2H') (j : ℕ) (S : List Bool) :
    ‖mulCL hW.sb (wordAct S (vE m σ f j))‖
      ≤ √2 * ‖mulCL hW.sb f‖ * (4 + 2 * l) ^ S.length * (Real.exp 1 * (2 * cH) / σ) ^ (S.length + 2 * j)
        * ((S.length + 2 * j).factorial : ℝ) := by
  have hm2 : (1 / 2 : ℝ) ^ 2 ≤ m ^ 2 := pow_le_pow_left₀ (by norm_num) hm 2
  have hμ : (0 : ℝ) ≤ m ^ 2 - 1 / 4 := by linarith
  have hc : 1 ≤ cH := by
    unfold cH
    have := Real.exp_pos (-1)
    linarith
  have hq : 1 ≤ Real.exp 1 * (2 * cH) / σ := by
    rw [le_div_iff₀ hσ]
    have he : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ)
      linarith
    nlinarith
  refine words_rec hW hμ (vE m σ f) (vE_allWords hm hσ hσ1 f) (vE_step hm hσ hσ1 f) (A := √2 * ‖mulCL hW.sb f‖) (by positivity) hq
    (fun j => ?_) S.length j S rfl
  have h := baseM_vj hW hm hml hσ j f
  calc ‖mulCL hW.sb (vE m σ f j)‖ ≤ √2 * (Real.exp 1 * (2 * cH) / σ) ^ (2 * j) * ((2 * j).factorial : ℝ) * ‖mulCL hW.sb f‖ := h
    _ = _ := by ring

end Qschubert
