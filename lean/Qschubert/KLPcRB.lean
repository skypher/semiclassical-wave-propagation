import Qschubert.KLPcRA
import Qschubert.KLPcWc

/-!
# The data of the printed class: `e^{-αΛ} = e^{-σΛ_m} e^{σ(Λ_m - Λ)} e^{-(α-σ)Λ}`

`B = Λ_m - Λ` is a bounded multiplier whose profile has the critical tail, so it is bounded in the critical weight (`B_cw`, by `cw_abstract`).
Its exponential `e^{σB}` is bounded there as well (`Q_cw`), by the series and a truncation of the weight (`series_weighted`). Hence
`f̃ = e^{σB} e^{-(α-σ)Λ} f` satisfies `e^{-σΛ_m} f̃ = e^{-αΛ} f` and `‖ω f̃‖ ≤ C ‖ω f‖` (`data_factor`).
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set Physicslib4.Spectral Physicslib4.Spectral.Unbounded
open scoped ENNReal InnerProductSpace ComplexConjugate UpperHalfPlane

local notation "L2H'" => Lp ℂ 2 (volume : Measure UpperHalfPlane)

/-! ### Weighted integrals through bounded truncations -/

lemma ofReal_norm_mulBM {g : UpperHalfPlane → ℝ} {C : ℝ} (H : BM g C) (hg : ∀ z, 0 ≤ g z) (u : L2H') :
    ENNReal.ofReal (‖mulBM H u‖ ^ 2) = ∫⁻ z, ENNReal.ofReal (g z ^ 2 * ‖u z‖ ^ 2) := by
  rw [← lintegral_enorm_sq_eq]
  refine lintegral_congr_ae ?_
  filter_upwards [coe_mulBM H u] with z hz
  rw [hz, ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _), norm_mul, Complex.norm_real, Real.norm_of_nonneg (hg z), mul_pow]

lemma lint_le_of_trunc {om : UpperHalfPlane → ℝ} (hom : Measurable om) (hom0 : ∀ z, 0 ≤ om z) (v : L2H') {C : ℝ≥0∞}
    (h : ∀ N : ℕ, ∫⁻ z, ENNReal.ofReal ((min (om z) N) ^ 2 * ‖v z‖ ^ 2) ≤ C) :
    ∫⁻ z, ENNReal.ofReal (om z ^ 2 * ‖v z‖ ^ 2) ≤ C := by
  have hvm : Measurable fun z => ‖v z‖ ^ 2 := ((Lp.stronglyMeasurable v).measurable.norm).pow_const 2
  have e : (fun z => ENNReal.ofReal (om z ^ 2 * ‖v z‖ ^ 2)) = fun z => ⨆ N : ℕ, ENNReal.ofReal ((min (om z) N) ^ 2 * ‖v z‖ ^ 2) := by
    funext z
    refine le_antisymm ?_ (iSup_le fun N => ?_)
    · obtain ⟨N, hN⟩ := exists_nat_ge (om z)
      refine le_iSup_of_le N (le_of_eq ?_)
      rw [min_eq_left hN]
    · refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _))
      exact pow_le_pow_left₀ (le_min (hom0 z) (Nat.cast_nonneg N)) (min_le_left _ _) 2
  have hmeas : ∀ N : ℕ, Measurable fun z => ENNReal.ofReal ((min (om z) N) ^ 2 * ‖v z‖ ^ 2) := fun N =>
    ENNReal.measurable_ofReal.comp (((hom.min measurable_const).pow_const 2).mul hvm)
  have hmono : Monotone fun (N : ℕ) z => ENNReal.ofReal ((min (om z) N) ^ 2 * ‖v z‖ ^ 2) := by
    intro N N' hNN z
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _))
    refine pow_le_pow_left₀ (le_min (hom0 z) (Nat.cast_nonneg N)) ?_ 2
    exact min_le_min le_rfl (by exact_mod_cast hNN)
  have hsup : ∫⁻ z, ⨆ N : ℕ, ENNReal.ofReal ((min (om z) N) ^ 2 * ‖v z‖ ^ 2)
      = ⨆ N : ℕ, ∫⁻ z, ENNReal.ofReal ((min (om z) N) ^ 2 * ‖v z‖ ^ 2) :=
    lintegral_iSup (f := fun (N : ℕ) z => ENNReal.ofReal ((min (om z) N) ^ 2 * ‖v z‖ ^ 2)) hmeas hmono
  rw [e, hsup]
  exact iSup_le h

/-- **A norm-convergent series of powers in a weight.** -/
theorem series_weighted {om : UpperHalfPlane → ℝ} (hom : Measurable om) (hom0 : ∀ z, 0 ≤ om z) {A : L2H' →L[ℂ] L2H'} {K : ℝ} (hK : 0 ≤ K)
    (hA : ∀ f : L2H', ∫⁻ z, ENNReal.ofReal (om z ^ 2 * ‖A f z‖ ^ 2) ≤ ENNReal.ofReal (K ^ 2) * ∫⁻ z, ENNReal.ofReal (om z ^ 2 * ‖f z‖ ^ 2))
    {Q : L2H' →L[ℂ] L2H'} {c : ℕ → ℝ} (hc : ∀ k, 0 ≤ c k) {M : ℝ} (hM : 0 < M) (hsum : ∀ n, ∑ k ∈ Finset.range n, c k * K ^ k ≤ M)
    (hlim : ∀ f : L2H', Tendsto (fun n => ∑ k ∈ Finset.range n, ((c k : ℝ) : ℂ) • (A ^ k) f) atTop (𝓝 (Q f))) (f : L2H') :
    ∫⁻ z, ENNReal.ofReal (om z ^ 2 * ‖Q f z‖ ^ 2) ≤ ENNReal.ofReal (M ^ 2) * ∫⁻ z, ENNReal.ofReal (om z ^ 2 * ‖f z‖ ^ 2) := by
  set I₀ := ∫⁻ z, ENNReal.ofReal (om z ^ 2 * ‖f z‖ ^ 2) with hI₀
  by_cases hfin : I₀ = ⊤
  · rw [hfin, ENNReal.mul_top]
    · exact le_top
    · simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      positivity
  set I := I₀.toReal with hI
  have hI0 : 0 ≤ I := ENNReal.toReal_nonneg
  have hpow : ∀ (k : ℕ) (g : L2H'), ∫⁻ z, ENNReal.ofReal (om z ^ 2 * ‖(A ^ k) g z‖ ^ 2)
      ≤ ENNReal.ofReal ((K ^ k) ^ 2) * ∫⁻ z, ENNReal.ofReal (om z ^ 2 * ‖g z‖ ^ 2) := fun k => by
    induction k with
    | zero => intro g; simp
    | succ k ih =>
      intro g
      have e : (A ^ (k + 1)) g = (A ^ k) (A g) := by rw [pow_succ]; rfl
      rw [e]
      calc _ ≤ ENNReal.ofReal ((K ^ k) ^ 2) * ∫⁻ z, ENNReal.ofReal (om z ^ 2 * ‖A g z‖ ^ 2) := ih (A g)
        _ ≤ ENNReal.ofReal ((K ^ k) ^ 2) * (ENNReal.ofReal (K ^ 2) * ∫⁻ z, ENNReal.ofReal (om z ^ 2 * ‖g z‖ ^ 2)) := by
            gcongr
            exact hA g
        _ = _ := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
            congr 2
            ring
  refine lint_le_of_trunc hom hom0 (Q f) fun N => ?_
  have HN : BM (fun z => min (om z) N) N := ⟨hom.min measurable_const, fun z => by
    rw [abs_of_nonneg (le_min (hom0 z) (Nat.cast_nonneg N))]
    exact min_le_right _ _⟩
  have hgN : ∀ z, 0 ≤ min (om z) (N : ℝ) := fun z => le_min (hom0 z) (Nat.cast_nonneg N)
  have hterm : ∀ k, ‖mulBM HN ((A ^ k) f)‖ ≤ K ^ k * √I := fun k => by
    have h1 := hpow k f
    have h2 : ENNReal.ofReal (‖mulBM HN ((A ^ k) f)‖ ^ 2) ≤ ENNReal.ofReal ((K ^ k) ^ 2 * I) := by
      rw [ofReal_norm_mulBM HN hgN, ENNReal.ofReal_mul (by positivity), hI, ENNReal.ofReal_toReal hfin]
      refine le_trans (lintegral_mono fun z => ?_) h1
      refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _))
      exact pow_le_pow_left₀ (hgN z) (min_le_left _ _) 2
    have h3 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h2
    have e : (K ^ k) ^ 2 * I = (K ^ k * √I) ^ 2 := by rw [mul_pow, Real.sq_sqrt hI0]
    rw [e] at h3
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h3
  have hpart : ∀ n, ‖mulBM HN (∑ k ∈ Finset.range n, ((c k : ℝ) : ℂ) • (A ^ k) f)‖ ≤ M * √I := fun n => by
    rw [map_sum]
    refine (norm_sum_le _ _).trans ?_
    have h1 : ∀ k ∈ Finset.range n, ‖mulBM HN (((c k : ℝ) : ℂ) • (A ^ k) f)‖ ≤ c k * K ^ k * √I := fun k _ => by
      rw [map_smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg (hc k), mul_assoc]
      exact mul_le_mul_of_nonneg_left (hterm k) (hc k)
    refine (Finset.sum_le_sum h1).trans ?_
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hsum n) (Real.sqrt_nonneg _)
  have hQ : ‖mulBM HN (Q f)‖ ≤ M * √I :=
    le_of_tendsto' (((mulBM HN).continuous.tendsto _).comp (hlim f)).norm hpart
  rw [← ofReal_norm_mulBM HN hgN]
  have e : ENNReal.ofReal (M ^ 2) * I₀ = ENNReal.ofReal ((M * √I) ^ 2) := by
    rw [mul_pow, Real.sq_sqrt hI0, ENNReal.ofReal_mul (by positivity), hI, ENNReal.ofReal_toReal hfin]
  rw [e]
  exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) hQ 2)

/-! ### `B = Λ_m - Λ` -/

/-- The symbol of `Λ_m - Λ`. -/
noncomputable def rB (m x : ℝ) : ℝ := sM m x - √x

lemma measurable_rB (m : ℝ) : Measurable (rB m) := (measurable_sM m).sub Real.continuous_sqrt.measurable

lemma rB_nonneg {m : ℝ} (hm : 1 / 2 ≤ m) (x : ℝ) : 0 ≤ rB m x := sub_nonneg.2 (sqrt_le_sM hm x)

lemma rB_le {m : ℝ} (hm : 0 ≤ m) (x : ℝ) : rB m x ≤ m := by
  unfold rB sM
  have h0 := Real.sqrt_nonneg x
  have h : Real.sqrt (x - 1 / 4 + m ^ 2) ≤ √x + m := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    rcases le_or_gt 0 x with hx | hx
    · have := Real.sq_sqrt hx
      nlinarith
    · rw [Real.sqrt_eq_zero_of_nonpos hx.le]
      nlinarith
  linarith

/-- The operator symbol of `Λ_m - Λ`. -/
noncomputable def GB (m : ℝ) : ℝ → ℂ := fun x => ((rB m x : ℝ) : ℂ)

lemma GB_mem {m : ℝ} (hm : 1 / 2 ≤ m) : GB m ∈ BddMeasurable ℝ :=
  memB_of_abs_le (measurable_rB m) (C := m) fun x => by
    rw [abs_of_nonneg (rB_nonneg hm x)]
    exact rB_le (by linarith) x

lemma measurable_omC (c : ℝ) : Measurable fun z : UpperHalfPlane => omC c (z : ℂ) := by
  unfold omC
  have h := measurable_psi_coe
  fun_prop

/-- **`Λ_m - Λ` at the critical weight.** -/
theorem B_cw {c : ℝ} (hc1 : 1 / 2 < c) (hc2 : c < 1) {m : ℝ} (hm : 1 / 2 ≤ m) : ∃ K : ℝ, 0 < K ∧ ∀ f : L2H',
    ∫⁻ z : UpperHalfPlane, ENNReal.ofReal (omC c (z : ℂ) ^ 2 * ‖specE.integral (GB m) f z‖ ^ 2)
      ≤ ENNReal.ofReal (K ^ 2) * ∫⁻ z : UpperHalfPlane, ENNReal.ofReal (omC c (z : ℂ) ^ 2 * ‖f z‖ ^ 2) := by
  have hc0 : 0 ≤ c := by linarith
  have hD : 0 < Real.exp (1 / 2) * (2 : ℝ) ^ c := by positivity
  obtain ⟨K, hK, h⟩ := cw_abstract hc1 hc2 hD
  set B₀ : ℝ := 4 * √2 * (m - 1 / 2) + 2 / √Real.pi * (2 * √2) with hB₀
  have hB₀0 : 0 < B₀ := by
    have h1 : 0 ≤ 4 * √2 * (m - 1 / 2) := mul_nonneg (by positivity) (by linarith)
    have h2 : 0 < 2 / √Real.pi * (2 * √2) := by positivity
    linarith
  refine ⟨K * B₀, by positivity, fun f => ?_⟩
  refine h (fun z => omC c (z : ℂ)) (omC_nonneg c) (fun n z hz => omC_lo hc0 n z hz) (fun l z hz => omC_hi hc0 l z hz)
    hB₀0 (bProf_mass hm).1 (bProf_TailB hm) (GB_mem hm) (fun x hx => ?_) f
  exact rep_of_real (R := rB m x) rfl (bProf_symbol hm hx).2

/-! ### `e^{σB}` -/

/-- The symbol of `e^{σ(Λ_m - Λ)}`. -/
noncomputable def GQ (σ m : ℝ) : ℝ → ℂ := fun x => ((Real.exp (σ * rB m x) : ℝ) : ℂ)

lemma GQ_mem {σ m : ℝ} (hσ : 0 ≤ σ) (hm : 1 / 2 ≤ m) : GQ σ m ∈ BddMeasurable ℝ :=
  memB_of_abs_le (Real.measurable_exp.comp (measurable_const.mul (measurable_rB m))) (C := Real.exp (σ * m)) fun x => by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (rB_le (by linarith) x) hσ)

lemma spec_pow {G : ℝ → ℂ} (hG : G ∈ BddMeasurable ℝ) (n : ℕ) : specE.integral (G ^ n) = (specE.integral G) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, specE.integral_one]
  | succ n ih => rw [pow_succ, pow_succ, specE.integral_mul (pow_mem_B hG n) hG, ih]

/-- The partial sums of the exponential series as symbols. -/
noncomputable def PQ (σ m : ℝ) (n : ℕ) : ℝ → ℂ := ∑ k ∈ Finset.range n, (((σ ^ k / k.factorial : ℝ)) : ℂ) • GB m ^ k

lemma PQ_mem {σ m : ℝ} (hm : 1 / 2 ≤ m) (n : ℕ) : PQ σ m n ∈ BddMeasurable ℝ :=
  Submodule.sum_mem _ fun k _ => (BddMeasurable ℝ).smul_mem _ (pow_mem_B (GB_mem hm) k)

lemma spec_PQ {σ m : ℝ} (hm : 1 / 2 ≤ m) (n : ℕ) :
    specE.integral (PQ σ m n) = ∑ k ∈ Finset.range n, (((σ ^ k / k.factorial : ℝ)) : ℂ) • (specE.integral (GB m)) ^ k := by
  induction n with
  | zero =>
    simp only [PQ, Finset.range_zero, Finset.sum_empty]
    have h := specE.integral_smul (0 : ℂ) (GB_mem hm)
    rw [zero_smul, zero_smul] at h
    exact h
  | succ n ih =>
    have e : PQ σ m (n + 1) = PQ σ m n + (((σ ^ n / n.factorial : ℝ)) : ℂ) • GB m ^ n := by
      unfold PQ
      rw [Finset.sum_range_succ]
    rw [e, specE.integral_add (PQ_mem hm n) ((BddMeasurable ℝ).smul_mem _ (pow_mem_B (GB_mem hm) n)),
      specE.integral_smul _ (pow_mem_B (GB_mem hm) n), ih, spec_pow (GB_mem hm), Finset.sum_range_succ]

lemma PQ_apply (σ m : ℝ) (n : ℕ) (x : ℝ) :
    PQ σ m n x = ∑ k ∈ Finset.range n, (((σ * rB m x : ℝ)) : ℂ) ^ k / (k.factorial : ℂ) := by
  unfold PQ
  rw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  show (((σ ^ k / k.factorial : ℝ)) : ℂ) * (GB m x) ^ k = _
  unfold GB
  push_cast
  rw [mul_pow]
  ring

lemma GQ_sub_PQ_le {σ m : ℝ} (hσ : 0 ≤ σ) (hm : 1 / 2 ≤ m) (hσm : σ * m ≤ 1 / 2) (n : ℕ) (x : ℝ) :
    ‖GQ σ m x - PQ σ m n x‖ ≤ (1 / 2) ^ n * Real.exp (1 / 2) := by
  have h := Complex.norm_exp_sub_sum_le_norm_mul_exp (((σ * rB m x : ℝ)) : ℂ) n
  have hy0 : 0 ≤ σ * rB m x := mul_nonneg hσ (rB_nonneg hm x)
  have hy : σ * rB m x ≤ 1 / 2 := (mul_le_mul_of_nonneg_left (rB_le (by linarith) x) hσ).trans hσm
  rw [Complex.norm_real, Real.norm_of_nonneg hy0] at h
  have e : GQ σ m x = Complex.exp (((σ * rB m x : ℝ)) : ℂ) := by
    unfold GQ
    rw [Complex.ofReal_exp]
  rw [e, PQ_apply]
  refine h.trans (mul_le_mul (pow_le_pow_left₀ hy0 hy n) (Real.exp_le_exp.2 hy) (Real.exp_pos _).le (by positivity))

lemma tendsto_spec_PQ {σ m : ℝ} (hσ : 0 ≤ σ) (hm : 1 / 2 ≤ m) (hσm : σ * m ≤ 1 / 2) (f : L2H') :
    Tendsto (fun n => ∑ k ∈ Finset.range n, ((((σ ^ k / k.factorial : ℝ)) : ℝ) : ℂ) • ((specE.integral (GB m)) ^ k) f) atTop
      (𝓝 (specE.integral (GQ σ m) f)) := by
  have hdiff : ∀ n, ‖specE.integral (GQ σ m) f - specE.integral (PQ σ m n) f‖ ≤ (1 / 2) ^ n * Real.exp (1 / 2) * ‖f‖ := fun n => by
    have hmem : GQ σ m + (-1 : ℂ) • PQ σ m n ∈ BddMeasurable ℝ :=
      Submodule.add_mem _ (GQ_mem hσ hm) ((BddMeasurable ℝ).smul_mem _ (PQ_mem hm n))
    have e : specE.integral (GQ σ m) f - specE.integral (PQ σ m n) f = specE.integral (GQ σ m + (-1 : ℂ) • PQ σ m n) f := by
      rw [specE.integral_add (GQ_mem hσ hm) ((BddMeasurable ℝ).smul_mem _ (PQ_mem hm n)), specE.integral_smul _ (PQ_mem hm n)]
      simp [sub_eq_add_neg]
    rw [e]
    have h1 : ‖specE.integral (GQ σ m + (-1 : ℂ) • PQ σ m n)‖ ≤ (1 / 2) ^ n * Real.exp (1 / 2) :=
      (specE.norm_integral_le hmem).trans (ciSup_le fun x => by
        have := GQ_sub_PQ_le hσ hm hσm n x
        simpa [sub_eq_add_neg] using this)
    exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right h1 (norm_nonneg _))
  have hsum : ∀ n, ∑ k ∈ Finset.range n, ((((σ ^ k / k.factorial : ℝ)) : ℝ) : ℂ) • ((specE.integral (GB m)) ^ k) f = specE.integral (PQ σ m n) f := fun n => by
    rw [spec_PQ hm n, ContinuousLinearMap.sum_apply]
    rfl
  simp_rw [hsum]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n * Real.exp (1 / 2) * ‖f‖) atTop (𝓝 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    have h2 := (h.mul_const (Real.exp (1 / 2))).mul_const ‖f‖
    simpa using h2
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hlim
  rw [norm_sub_rev]
  exact hdiff n

/-- **`e^{σ(Λ_m - Λ)}` at the critical weight.** -/
theorem Q_cw {c : ℝ} (hc1 : 1 / 2 < c) (hc2 : c < 1) {m : ℝ} (hm : 1 / 2 ≤ m) : ∃ K : ℝ, 0 < K ∧ ∀ σ : ℝ, 0 ≤ σ → σ * m ≤ 1 / 2 →
    ∀ f : L2H', ∫⁻ z : UpperHalfPlane, ENNReal.ofReal (omC c (z : ℂ) ^ 2 * ‖specE.integral (GQ σ m) f z‖ ^ 2)
      ≤ ENNReal.ofReal (Real.exp (σ * K) ^ 2) * ∫⁻ z : UpperHalfPlane, ENNReal.ofReal (omC c (z : ℂ) ^ 2 * ‖f z‖ ^ 2) := by
  obtain ⟨K, hK, hB⟩ := B_cw hc1 hc2 hm
  refine ⟨K, hK, fun σ hσ hσm f => ?_⟩
  refine series_weighted (measurable_omC c) (omC_nonneg c) hK.le hB (c := fun k => σ ^ k / k.factorial) (fun k => by positivity)
    (Real.exp_pos _) (fun n => ?_) (fun g => tendsto_spec_PQ hσ hm hσm g) f
  have h := Real.sum_le_exp_of_nonneg (mul_nonneg hσ hK.le) n
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_)) h
  rw [mul_pow]
  ring

/-! ### The factorization -/

/-- **The data of the printed class.** For `0 < σ < α`, `α - σ ≤ 1`, `σ m ≤ 1/2`: `f̃ = e^{σ(Λ_m - Λ)} e^{-(α-σ)Λ} f` satisfies
`e^{-σΛ_m} f̃ = e^{-αΛ} f`, and `‖ω f̃‖ ≤ C ‖ω f‖` at the critical weight. -/
theorem data_factor {c : ℝ} (hc1 : 1 / 2 < c) (hc2 : c < 1) {m : ℝ} (hm : 1 / 2 ≤ m) : ∃ Cd : ℝ, 0 < Cd ∧ ∀ (σ α : ℝ), 0 < σ → σ < α →
    α - σ ≤ 1 → σ * m ≤ 1 / 2 → ∀ f : L2H',
    vE m σ (specE.integral (GQ σ m) (specE.integral (GW 0 (α - σ)) f)) 0 = specE.integral (GW 0 α) f
    ∧ ∫⁻ z : UpperHalfPlane, ENNReal.ofReal (omC c (z : ℂ) ^ 2 * ‖specE.integral (GQ σ m) (specE.integral (GW 0 (α - σ)) f) z‖ ^ 2)
      ≤ ENNReal.ofReal (Cd ^ 2) * ∫⁻ z : UpperHalfPlane, ENNReal.ofReal (omC c (z : ℂ) ^ 2 * ‖f z‖ ^ 2) := by
  obtain ⟨K, hK, hQ⟩ := Q_cw hc1 hc2 hm
  obtain ⟨Kp, hKp, hP⟩ := poisson_cw hc1 hc2
  refine ⟨Real.exp K * Kp, by positivity, fun σ α hσ hσα hη hσm f => ⟨?_, ?_⟩⟩
  · have hη0 : 0 < α - σ := by linarith
    have hα : 0 < α := by linarith
    unfold vE
    have e1 : specE.integral (GWM m 0 σ) (specE.integral (GQ σ m) (specE.integral (GW 0 (α - σ)) f))
        = specE.integral (GWM m 0 σ * (GQ σ m * GW 0 (α - σ))) f := by
      rw [specE.integral_mul (GWM_mem m 0 hσ) (mul_mem_B (GQ_mem hσ.le hm) (GW_mem 0 hη0)),
        specE.integral_mul (GQ_mem hσ.le hm) (GW_mem 0 hη0)]
      rfl
    rw [e1]
    have e2 := integral_congr_nonneg (mul_mem_B (GWM_mem m 0 hσ) (mul_mem_B (GQ_mem hσ.le hm) (GW_mem 0 hη0))) (GW_mem 0 hα)
      (fun s hs => by
        show ((rWM m 0 σ s : ℝ) : ℂ) * (((Real.exp (σ * rB m s) : ℝ) : ℂ) * ((rW 0 (α - σ) s : ℝ) : ℂ)) = ((rW 0 α s : ℝ) : ℂ)
        unfold rWM rW rB
        simp only [hs, ite_true, mul_zero, pow_zero, one_mul]
        rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Real.exp_add, ← Real.exp_add]
        congr 2
        ring)
    exact congrArg (fun T : L2H' →L[ℂ] L2H' => T f) e2
  · have hη0 : 0 < α - σ := by linarith
    have hσ1 : σ ≤ 1 := by
      have : σ * (1 / 2) ≤ σ * m := mul_le_mul_of_nonneg_left hm hσ.le
      linarith
    calc _ ≤ ENNReal.ofReal (Real.exp (σ * K) ^ 2) * ∫⁻ z : UpperHalfPlane, ENNReal.ofReal (omC c (z : ℂ) ^ 2 * ‖specE.integral (GW 0 (α - σ)) f z‖ ^ 2) :=
          hQ σ hσ.le hσm _
      _ ≤ ENNReal.ofReal (Real.exp (σ * K) ^ 2) * (ENNReal.ofReal (Kp ^ 2) * ∫⁻ z : UpperHalfPlane, ENNReal.ofReal (omC c (z : ℂ) ^ 2 * ‖f z‖ ^ 2)) := by
          gcongr
          exact hP (α - σ) hη0 hη f
      _ ≤ _ := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
          gcongr
          have h1 : Real.exp (σ * K) ≤ Real.exp K := Real.exp_le_exp.2 (by nlinarith)
          have h0 := Real.exp_pos (σ * K)
          rw [← mul_pow]
          exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right h1 hKp.le) 2

end Qschubert
