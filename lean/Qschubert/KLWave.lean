import Qschubert.KLMweak

/-!
# A weighted energy estimate for the wave group

`‖W cos(sΛ) u‖ ≤ e^{2ρ|s|} ‖W u‖` for a bounded weight with `|Z W²| ≤ 2ρ W²`, `Z ∈ {X, Y}` (`wave_weight`). This replaces finite
propagation speed and the covering by unit balls in the paper's proof of `lem:w3`: only the conjugation bound is used.

The proof runs on spectrally truncated vectors, where every operator is bounded and differentiable in operator norm.

* `hasDerivAt_specE`: a family of bounded symbols with a Lipschitz `s`-derivative gives a norm-differentiable family of operators;
* `cR`, `dR`: the symbols `cos(s√x) 1_{[0,R]}(x)` and `sin(s√x)/√x 1_{[0,R]}(x)`;
* `chiC`, `chiD`: the corresponding cutoffs.
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set Physicslib4.Spectral Physicslib4.Spectral.Unbounded
open scoped ENNReal InnerProductSpace ComplexConjugate

local notation "L2H'" => Lp ℂ 2 (volume : Measure UpperHalfPlane)

/-- **A norm-differentiable family of spectral multipliers.** -/
theorem hasDerivAt_specE {φ ψ : ℝ → ℝ → ℂ} {K : ℝ} (hφ : ∀ s, φ s ∈ BddMeasurable ℝ) (hψ : ∀ s, ψ s ∈ BddMeasurable ℝ)
    (hK : 0 ≤ K) (hd : ∀ s x, HasDerivAt (fun r => φ r x) (ψ s x) s)
    (hL : ∀ s₁ s₂ x, ‖ψ s₁ x - ψ s₂ x‖ ≤ K * |s₁ - s₂|) (s : ℝ) :
    HasDerivAt (fun r => specE.integral (φ r)) (specE.integral (ψ s)) s := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  refine Asymptotics.IsBigO.trans_isLittleO (g := fun h : ℝ => h ^ 2) ?_ (Asymptotics.isLittleO_pow_id (𝕜 := ℝ) (n := 2) (by norm_num))
  refine Asymptotics.IsBigO.of_bound K (Eventually.of_forall fun h => ?_)
  set ξ : ℝ → ℂ := φ (s + h) + (-1 : ℂ) • φ s + (-(h : ℂ)) • ψ s with hξ
  have hs1 := (BddMeasurable ℝ).smul_mem (-1 : ℂ) (hφ s)
  have hs2 := (BddMeasurable ℝ).smul_mem (-(h : ℂ)) (hψ s)
  have hξm : ξ ∈ BddMeasurable ℝ := (BddMeasurable ℝ).add_mem ((BddMeasurable ℝ).add_mem (hφ _) hs1) hs2
  have hop : specE.integral (φ (s + h)) - specE.integral (φ s) - h • specE.integral (ψ s) = specE.integral ξ := by
    rw [hξ, specE.integral_add ((BddMeasurable ℝ).add_mem (hφ _) hs1) hs2, specE.integral_add (hφ _) hs1,
      specE.integral_smul _ (hφ s), specE.integral_smul _ (hψ s)]
    ext1 x
    have e := RCLike.real_smul_eq_coe_smul (K := ℂ) h (specE.integral (ψ s) x)
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
    rw [e]
    module
  have hpt : ∀ x, ‖ξ x‖ ≤ K * h ^ 2 := fun x => by
    have hmv : ‖φ (s + h) x - ((s + h : ℝ) : ℂ) * ψ s x - (φ s x - (s : ℂ) * ψ s x)‖ ≤ K * |h| * ‖(s + h) - s‖ := by
      refine Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (𝕜 := ℝ) (f := fun r : ℝ => φ r x - (r : ℂ) * ψ s x)
        (f' := fun r => ψ r x - ψ s x) (s := Set.uIcc s (s + h)) (C := K * |h|) (x := s) (y := s + h)
        (fun r _ => ?_) (fun r hr => ?_) (convex_uIcc _ _) left_mem_uIcc right_mem_uIcc
      · have h1 : HasDerivAt (fun r : ℝ => (r : ℂ) * ψ s x) (ψ s x) r := by
          simpa using ((hasDerivAt_id' r).ofReal_comp).mul_const (ψ s x)
        exact ((hd r x).sub h1).hasDerivWithinAt
      · have hr' : |r - s| ≤ |h| := by
          rcases Set.mem_uIcc.1 hr with ⟨a, b⟩ | ⟨a, b⟩
          · rw [abs_of_nonneg (by linarith)]; exact le_trans (by linarith) (le_abs_self h)
          · rw [abs_of_nonpos (by linarith)]; exact le_trans (by linarith) (neg_le_abs h)
        exact (hL r s x).trans (mul_le_mul_of_nonneg_left hr' hK)
    simp only [add_sub_cancel_left, Real.norm_eq_abs] at hmv
    have e : ξ x = φ (s + h) x - ((s + h : ℝ) : ℂ) * ψ s x - (φ s x - (s : ℂ) * ψ s x) := by
      simp only [hξ, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      push_cast
      ring
    rw [e]
    refine hmv.trans (le_of_eq ?_)
    rw [mul_assoc, ← sq, sq_abs]
  have hn := specE.norm_integral_le hξm
  have hsup : ⨆ x, ‖ξ x‖ ≤ K * h ^ 2 := ciSup_le hpt
  rw [show specE.integral (φ (s + h)) - specE.integral (φ s) - h • specE.integral (ψ s) = specE.integral ξ from hop]
  simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg h)] using hn.trans hsup

/-- `1_{[0,R]}`. -/
noncomputable def cutR (R x : ℝ) : ℝ := (Icc 0 R).indicator 1 x

lemma measurable_cutR (R : ℝ) : Measurable (cutR R) := measurable_one.indicator measurableSet_Icc

lemma cutR_nonneg (R x : ℝ) : 0 ≤ cutR R x := by unfold cutR; exact indicator_nonneg (fun _ _ => zero_le_one) x

lemma cutR_le_one (R x : ℝ) : cutR R x ≤ 1 := by
  unfold cutR; by_cases h : x ∈ Icc 0 R <;> simp [h]

lemma cutR_x_le {R x : ℝ} : |x| * cutR R x ≤ |R| := by
  unfold cutR
  by_cases h : x ∈ Icc 0 R
  · simp only [h, indicator_of_mem, Pi.one_apply, mul_one]
    rw [abs_of_nonneg h.1, abs_of_nonneg (h.1.trans h.2)]; exact h.2
  · simp [h, abs_nonneg]

/-- `sin(s l)/l`, with value `s` at `l = 0`. -/
noncomputable def sincS (s l : ℝ) : ℝ := s * Real.sinc (s * l)

lemma sincS_mul (s l : ℝ) : sincS s l * l = Real.sin (s * l) := by
  unfold sincS
  by_cases h : s * l = 0
  · rcases mul_eq_zero.1 h with h0 | h0 <;> simp [h0]
  · rw [Real.sinc_of_ne_zero h]
    have hl : l ≠ 0 := right_ne_zero_of_mul h
    have hs : s ≠ 0 := left_ne_zero_of_mul h
    field_simp

lemma abs_sincS_le (s l : ℝ) : |sincS s l| ≤ |s| := by
  unfold sincS
  rw [abs_mul]
  have h : |Real.sinc (s * l)| ≤ 1 := Real.abs_sinc_le_one _
  nlinarith [abs_nonneg s]

lemma hasDerivAt_sincS (s l : ℝ) : HasDerivAt (fun r => sincS r l) (Real.cos (s * l)) s := by
  by_cases hl : l = 0
  · subst hl
    have e : (fun r : ℝ => sincS r 0) = fun r => r := by funext r; simp [sincS]
    rw [e]; simpa using hasDerivAt_id' s
  · have e : (fun r : ℝ => sincS r l) = fun r => Real.sin (r * l) / l := by
      funext r
      rw [← sincS_mul r l]; field_simp
    rw [e]
    have h1 : HasDerivAt (fun r : ℝ => r * l) l s := by simpa using (hasDerivAt_id' s).mul_const l
    have h2 := (h1.sin).div_const l
    convert h2 using 1
    field_simp

lemma abs_sincS_sub_le (s₁ s₂ l : ℝ) : |sincS s₁ l - sincS s₂ l| ≤ |s₁ - s₂| := by
  by_cases hl : l = 0
  · subst hl; simp [sincS]
  · have e : ∀ r, sincS r l = Real.sin (r * l) / l := fun r => by rw [← sincS_mul r l]; field_simp
    rw [e, e, ← sub_div, abs_div, div_le_iff₀ (abs_pos.2 hl)]
    calc |Real.sin (s₁ * l) - Real.sin (s₂ * l)| ≤ |s₁ * l - s₂ * l| := Real.abs_sin_sub_sin_le _ _
      _ = |s₁ - s₂| * |l| := by rw [← sub_mul, abs_mul]

/-- `cos(s√x) 1_{[0,R]}(x)`. -/
noncomputable def cR (R s x : ℝ) : ℝ := Real.cos (s * √x) * cutR R x

/-- `sin(s√x)/√x 1_{[0,R]}(x)`. -/
noncomputable def dR (R s x : ℝ) : ℝ := sincS s (√x) * cutR R x

lemma measurable_sincS_sqrt (s : ℝ) : Measurable fun x : ℝ => sincS s √x := by
  unfold sincS
  exact (Real.continuous_sinc.comp (continuous_const.mul Real.continuous_sqrt)).measurable.const_mul s

lemma measurable_cR (R s : ℝ) : Measurable (cR R s) :=
  (Real.continuous_cos.comp (continuous_const.mul Real.continuous_sqrt)).measurable.mul (measurable_cutR R)

lemma measurable_dR (R s : ℝ) : Measurable (dR R s) := (measurable_sincS_sqrt s).mul (measurable_cutR R)

lemma abs_cR_le (R s x : ℝ) : |cR R s x| ≤ cutR R x := by
  rw [cR, abs_mul, abs_of_nonneg (cutR_nonneg R x)]
  exact mul_le_of_le_one_left (cutR_nonneg R x) (Real.abs_cos_le_one _)

lemma abs_dR_le (R s x : ℝ) : |dR R s x| ≤ |s| * cutR R x := by
  rw [dR, abs_mul, abs_of_nonneg (cutR_nonneg R x)]
  exact mul_le_mul_of_nonneg_right (abs_sincS_le _ _) (cutR_nonneg R x)

lemma cut_le_one_add (R x : ℝ) : (1 + |x|) * cutR R x ≤ 1 + |R| := by
  have h1 := cutR_x_le (R := R) (x := x)
  have h2 := cutR_le_one R x
  nlinarith

/-- The cutoff of `cos(s√x) 1_{[0,R]}`. -/
noncomputable def chiC (R s : ℝ) : Cutoff where
  r := cR R s
  meas := measurable_cR R s
  C := 1 + |R|
  bound x := (abs_cR_le R s x).trans ((cutR_le_one R x).trans (by linarith [abs_nonneg R]))
  bound1 x := by
    rw [abs_mul]
    calc |1 + x| * |cR R s x| ≤ (1 + |x|) * cutR R x := by
          refine mul_le_mul ?_ (abs_cR_le R s x) (abs_nonneg _) (by positivity)
          simpa using abs_add_le 1 x
      _ ≤ 1 + |R| := cut_le_one_add R x

/-- The cutoff of `sin(s√x)/√x 1_{[0,R]}`. -/
noncomputable def chiD (R s : ℝ) : Cutoff where
  r := dR R s
  meas := measurable_dR R s
  C := |s| * (1 + |R|)
  bound x := by
    refine (abs_dR_le R s x).trans (mul_le_mul_of_nonneg_left ?_ (abs_nonneg s))
    exact (cutR_le_one R x).trans (by linarith [abs_nonneg R])
  bound1 x := by
    rw [abs_mul]
    calc |1 + x| * |dR R s x| ≤ (1 + |x|) * (|s| * cutR R x) := by
          refine mul_le_mul ?_ (abs_dR_le R s x) (abs_nonneg _) (by positivity)
          simpa using abs_add_le 1 x
      _ = |s| * ((1 + |x|) * cutR R x) := by ring
      _ ≤ |s| * (1 + |R|) := mul_le_mul_of_nonneg_left (cut_le_one_add R x) (abs_nonneg s)

lemma hasDerivAt_dR (R s x : ℝ) : HasDerivAt (fun r => dR R r x) (cR R s x) s := by
  unfold dR cR
  exact (hasDerivAt_sincS s √x).mul_const _

lemma hasDerivAt_cR (R s x : ℝ) : HasDerivAt (fun r => cR R r x) (-(x * dR R s x)) s := by
  unfold dR cR
  have h1 : HasDerivAt (fun r : ℝ => r * √x) (√x) s := by simpa using (hasDerivAt_id' s).mul_const √x
  have h2 := (h1.cos).mul_const (cutR R x)
  convert h2 using 1
  by_cases hx : x ∈ Icc 0 R
  · have hs := sincS_mul s √x
    have hsq : √x * √x = x := Real.mul_self_sqrt hx.1
    rw [← hs]
    nth_rewrite 1 [← hsq]
    ring
  · simp [cutR, hx]

lemma abs_cR_sub_le (R s₁ s₂ x : ℝ) : |cR R s₁ x - cR R s₂ x| ≤ (1 + |R|) * |s₁ - s₂| := by
  unfold cR
  rw [← sub_mul, abs_mul, abs_of_nonneg (cutR_nonneg R x)]
  by_cases hx : x ∈ Icc 0 R
  · have hc : cutR R x = 1 := by simp [cutR, hx]
    rw [hc, mul_one]
    have hsq : √x ≤ 1 + |R| := by
      have h1 : √x ≤ √(max R 1) := Real.sqrt_le_sqrt (hx.2.trans (le_max_left _ _))
      have h2 : √(max R 1) ≤ max R 1 := by
        rw [Real.sqrt_le_left (by positivity)]
        have : 1 ≤ max R 1 := le_max_right _ _
        nlinarith
      have h3 : max R 1 ≤ 1 + |R| := max_le (by linarith [le_abs_self R, abs_nonneg R]) (by linarith [abs_nonneg R])
      linarith
    calc |Real.cos (s₁ * √x) - Real.cos (s₂ * √x)| ≤ |s₁ * √x - s₂ * √x| := Real.abs_cos_sub_cos_le _ _
      _ = |s₁ - s₂| * √x := by rw [← sub_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      _ ≤ (1 + |R|) * |s₁ - s₂| := by nlinarith [abs_nonneg (s₁ - s₂)]
  · have hc : cutR R x = 0 := by simp [cutR, hx]
    rw [hc, mul_zero]; positivity

lemma abs_x_dR_sub_le (R s₁ s₂ x : ℝ) : |x * dR R s₁ x - x * dR R s₂ x| ≤ |R| * |s₁ - s₂| := by
  unfold dR
  rw [show x * (sincS s₁ √x * cutR R x) - x * (sincS s₂ √x * cutR R x) = (sincS s₁ √x - sincS s₂ √x) * (x * cutR R x) by ring,
    abs_mul, mul_comm]
  have h : |x * cutR R x| ≤ |R| := by
    rw [abs_mul, abs_of_nonneg (cutR_nonneg R x)]; exact cutR_x_le
  exact mul_le_mul h (abs_sincS_sub_le _ _ _) (abs_nonneg _) (abs_nonneg _)

lemma memB_of_abs_le {f : ℝ → ℝ} (hm : Measurable f) {C : ℝ} (hC : ∀ x, |f x| ≤ C) :
    (fun x => ((f x : ℝ) : ℂ)) ∈ BddMeasurable ℝ :=
  ⟨Complex.measurable_ofReal.comp hm, C, fun x => by rw [Complex.norm_real]; exact hC x⟩

/-- Three operator derivatives. -/
lemma hasDerivAt_D_J (R s : ℝ) : HasDerivAt (fun r => (chiD R r).J) (chiC R s).J s := by
  refine hasDerivAt_specE (φ := fun r x => ((dR R r x : ℝ) : ℂ)) (ψ := fun r x => ((cR R r x : ℝ) : ℂ)) (K := 1 + |R|)
    (fun r => (chiD R r).g_mem) (fun r => (chiC R r).g_mem) (by positivity) (fun r x => (hasDerivAt_dR R r x).ofReal_comp)
    (fun s₁ s₂ x => ?_) s
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact abs_cR_sub_le R s₁ s₂ x

lemma hasDerivAt_C_J (R s : ℝ) : HasDerivAt (fun r => (chiC R r).J) (-(chiD R s).JS) s := by
  have h := hasDerivAt_specE (φ := fun r x => ((cR R r x : ℝ) : ℂ)) (ψ := fun r x => ((-(x * dR R r x) : ℝ) : ℂ)) (K := |R|)
    (fun r => (chiC R r).g_mem)
    (fun r => (BddMeasurable ℝ).smul_mem (-1 : ℂ) (chiD R r).gS_mem |> fun hm => by
      convert hm using 1; funext x; simp [Cutoff.gS, chiD])
    (abs_nonneg R) (fun r x => (hasDerivAt_cR R r x).ofReal_comp)
    (fun s₁ s₂ x => by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        show -(x * dR R s₁ x) - -(x * dR R s₂ x) = -(x * dR R s₁ x - x * dR R s₂ x) by ring, abs_neg]
      exact abs_x_dR_sub_le R s₁ s₂ x) s
  have h' : HasDerivAt (fun r => (chiC R r).J) (specE.integral fun x : ℝ => ((-(x * dR R s x) : ℝ) : ℂ)) s := h
  convert h' using 1
  have e : (fun x : ℝ => ((-(x * dR R s x) : ℝ) : ℂ)) = (-1 : ℂ) • (chiD R s).gS := by
    funext x; simp [Cutoff.gS, chiD]
  rw [e, specE.integral_smul _ (chiD R s).gS_mem]
  simp [Cutoff.JS]

lemma hasDerivAt_D_JS (R s : ℝ) : HasDerivAt (fun r => (chiD R r).JS) (chiC R s).JS s := by
  refine hasDerivAt_specE (φ := fun r x => ((x * dR R r x : ℝ) : ℂ)) (ψ := fun r x => ((x * cR R r x : ℝ) : ℂ))
    (K := (1 + |R|) ^ 2) (fun r => (chiD R r).gS_mem) (fun r => (chiC R r).gS_mem) (by positivity)
    (fun r x => ((hasDerivAt_dR R r x).const_mul x).ofReal_comp) (fun s₁ s₂ x => ?_) s
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, ← mul_sub, abs_mul]
  by_cases hx : x ∈ Icc 0 R
  · have hxR : |x| ≤ 1 + |R| := by
      rw [abs_of_nonneg hx.1]; linarith [hx.2, le_abs_self R]
    calc |x| * |cR R s₁ x - cR R s₂ x| ≤ (1 + |R|) * ((1 + |R|) * |s₁ - s₂|) :=
          mul_le_mul hxR (abs_cR_sub_le R s₁ s₂ x) (abs_nonneg _) (by positivity)
      _ = _ := by ring
  · have hc : cutR R x = 0 := by simp [cutR, hx]
    simp only [cR, hc, mul_zero, sub_self, abs_zero]
    positivity

/-! ### The energy -/

/-- A bounded weight with `|Z W²| ≤ 2ρ W²`. -/
structure WaveW (W : ℂ → ℝ) (C ρ : ℝ) : Prop where
  pos : ∀ w : ℂ, 0 < w.im → 0 < W w
  sb : SB W C
  adm : Adm (fun w => W w ^ 2) C
  mX : SB (fun w => vfR 1 (fun u => W u ^ 2) w / W w) C
  mY : SB (fun w => vfR Complex.I (fun u => W u ^ 2) w / W w) C
  bX : ∀ w : ℂ, 0 < w.im → |vfR 1 (fun u => W u ^ 2) w / W w| ≤ 2 * ρ * W w
  bY : ∀ w : ℂ, 0 < w.im → |vfR Complex.I (fun u => W u ^ 2) w / W w| ≤ 2 * ρ * W w
  ρ0 : 0 ≤ ρ

lemma inner_mulCL_left {g : ℂ → ℝ} {C : ℝ} (H : SB g C) (x y : L2H') : ⟪mulCL H x, y⟫_ℂ = ⟪x, mulCL H y⟫_ℂ := by
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coe_mulCL H x, coe_mulCL H y] with z h1 h2
  rw [h1, h2]
  simp only [RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring

lemma By_eq_domY {χ : Cutoff} (v : L2H') : χ.By v = domY ⟨χ.J v, χ.J_mem v⟩ := by
  show formVec Complex.I (Or.inr rfl) (formLift ((χ.J + χ.JS) v))
    = formVec Complex.I (Or.inr rfl) (formLift (χ.J v + negLapH ⟨χ.J v, χ.J_mem v⟩))
  rw [Cutoff.negLapH_J]
  rfl

/-- The form identity on `Dom(-Δ)`. -/
lemma inner_dom_add (u w : negLapH.domain) :
    ⟪domX u, domX w⟫_ℂ + ⟪domY u, domY w⟫_ℂ = ⟪negLapH u, (w : L2H')⟫_ℂ := by
  have h := inner_formVec_lift_add ((u : L2H') + negLapH u) ((w : L2H') + negLapH w)
  have hu : formRes negLap ((u : L2H') + negLapH u) = (u : L2H') := formIncl_liftDom u
  have hw : formRes negLap ((w : L2H') + negLapH w) = (w : L2H') := formIncl_liftDom w
  rw [hu, hw, add_sub_cancel_left] at h
  exact h

lemma hasDerivAt_norm_sq_C {f : ℝ → L2H'} {f' : L2H'} {s : ℝ} (h : HasDerivAt f f' s) :
    HasDerivAt (fun r => ‖f r‖ ^ 2) (2 * (⟪f s, f'⟫_ℂ).re) s := by
  have hI := h.inner ℂ h
  have hR : HasDerivAt (fun r => (⟪f r, f r⟫_ℂ).re) _ s := (Complex.reCLM.hasFDerivAt).comp_hasDerivAt s hI
  have e : (fun r => ‖f r‖ ^ 2) = fun r => (⟪f r, f r⟫_ℂ).re := by
    funext r
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [e]
  convert hR using 1
  have h2 : (⟪f', f s⟫_ℂ).re = (⟪f s, f'⟫_ℂ).re := inner_re_symm (𝕜 := ℂ) f' (f s)
  show _ = (⟪f s, f'⟫_ℂ + ⟪f', f s⟫_ℂ).re
  rw [Complex.add_re, h2]
  ring

lemma hasDerivAt_clm_comp {A : L2H' →L[ℂ] L2H'} {f : ℝ → L2H'} {f' : L2H'} {s : ℝ} (h : HasDerivAt f f' s) :
    HasDerivAt (fun r => A (f r)) (A f') s :=
  ((A.restrictScalars ℝ).hasFDerivAt).comp_hasDerivAt s h

section energy

variable {W : ℂ → ℝ} {C ρ : ℝ} (hW : WaveW W C ρ) (R : ℝ) (u : L2H')
include hW

/-- `|⟪(Z W²)p, x⟫| ≤ 2ρ ‖Wp‖ ‖Wx‖`. -/
lemma cross_bound {m g : ℂ → ℝ} {Cm Cg : ℝ} (Hm : SB m Cm) (Hg : SB g Cg) (he : ∀ w : ℂ, 0 < w.im → g w = m w * W w)
    (hb : ∀ w : ℂ, 0 < w.im → |m w| ≤ 2 * ρ * W w) (p x : L2H') :
    ‖⟪mulCL Hg p, x⟫_ℂ‖ ≤ 2 * ρ * ‖mulCL hW.sb p‖ * ‖mulCL hW.sb x‖ := by
  have e : ⟪mulCL Hg p, x⟫_ℂ = ⟪mulCL Hm p, mulCL hW.sb x⟫_ℂ := by
    rw [L2.inner_def, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [coe_mulCL Hg p, coe_mulCL Hm p, coe_mulCL hW.sb x] with z h1 h2 h3
    rw [h1, h2, h3, he z z.im_pos]
    simp only [RCLike.inner_apply, map_mul, Complex.conj_ofReal, Complex.ofReal_mul]
    ring
  rw [e]
  refine (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
  filter_upwards [coe_mulCL Hm p, coe_mulCL hW.sb p] with z h1 h2
  rw [h1, h2, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (hW.pos z z.im_pos), ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hb z z.im_pos) (norm_nonneg _)

/-- The energy. -/
noncomputable def waveE (W : ℂ → ℝ) (hW : WaveW W C ρ) (R : ℝ) (u : L2H') (s : ℝ) : ℝ :=
  ‖mulCL hW.sb ((chiC R s).J u)‖ ^ 2 + ‖mulCL hW.sb ((chiD R s).Bx u)‖ ^ 2 + ‖mulCL hW.sb ((chiD R s).By u)‖ ^ 2

/-- **The derivative of the wave energy.** -/
theorem waveE_deriv (s : ℝ) :
    HasDerivAt (waveE W hW R u)
      (-(2 * (⟪mulCL hW.adm.sbX ((chiC R s).J u), (chiD R s).Bx u⟫_ℂ).re)
        - 2 * (⟪mulCL hW.adm.sbY ((chiC R s).J u), (chiD R s).By u⟫_ℂ).re) s := by
  set Wm := mulCL hW.sb with hWm
  set hm := mulCL hW.adm.sb with hhm
  set p := (chiC R s).J u with hp
  set q := (chiD R s).J u with hq
  have hpd : HasDerivAt (fun r => (chiC R r).J u) (-(chiD R s).JS u) s := by
    have h : HasDerivAt (fun r => (chiC R r).J u) _ s := hasDerivAt_clm_apply_C (hasDerivAt_C_J R s) (hasDerivAt_const s u)
    convert h using 1
    simp
  have hDd : HasDerivAt (fun r => ((chiD R r).J + (chiD R r).JS) u) (((chiC R s).J + (chiC R s).JS) u) s := by
    have h : HasDerivAt (fun r => ((chiD R r).J + (chiD R r).JS) u) _ s :=
      hasDerivAt_clm_apply_C ((hasDerivAt_D_J R s).add (hasDerivAt_D_JS R s)) (hasDerivAt_const s u)
    convert h using 1
    simp
  have hXd : HasDerivAt (fun r => (chiD R r).Bx u) ((chiC R s).Bx u) s :=
    hasDerivAt_clm_comp (A := (formVec 1 (Or.inl rfl)).comp formLift) hDd
  have hYd : HasDerivAt (fun r => (chiD R r).By u) ((chiC R s).By u) s :=
    hasDerivAt_clm_comp (A := (formVec Complex.I (Or.inr rfl)).comp formLift) hDd
  have h1 := hasDerivAt_norm_sq_C (hasDerivAt_clm_comp (A := Wm) hpd)
  have h2 := hasDerivAt_norm_sq_C (hasDerivAt_clm_comp (A := Wm) hXd)
  have h3 := hasDerivAt_norm_sq_C (hasDerivAt_clm_comp (A := Wm) hYd)
  have hall := (h1.add h2).add h3
  have hval : 2 * (⟪Wm p, Wm (-(chiD R s).JS u)⟫_ℂ).re + 2 * (⟪Wm ((chiD R s).Bx u), Wm ((chiC R s).Bx u)⟫_ℂ).re
        + 2 * (⟪Wm ((chiD R s).By u), Wm ((chiC R s).By u)⟫_ℂ).re
      = -(2 * (⟪mulCL hW.adm.sbX p, (chiD R s).Bx u⟫_ℂ).re) - 2 * (⟪mulCL hW.adm.sbY p, (chiD R s).By u⟫_ℂ).re := by
    set ps : negLapH.domain := ⟨p, (chiC R s).J_mem u⟩ with hps
    set qs : negLapH.domain := ⟨q, (chiD R s).J_mem u⟩ with hqs
    have hWW : ∀ x y : L2H', ⟪Wm x, Wm y⟫_ℂ = ⟪hm x, y⟫_ℂ := fun x y => by
      rw [hWm, ← inner_mulCL_left]
      rw [L2.inner_def, L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [coe_mulCL hW.sb (mulCL hW.sb x), coe_mulCL hW.sb x, coe_mulCL hW.adm.sb x] with z h1 h2 h3
      rw [hhm, h1, h2, h3]
      push_cast
      ring_nf
    set Ps : negLapH.domain := ⟨hm p, mul_mem_domain hW.adm ps⟩ with hPs
    have hX : domX Ps = mulCL hW.adm.sbX p + hm (domX ps) := domX_mul hW.adm ps
    have hY : domY Ps = mulCL hW.adm.sbY p + hm (domY ps) := domY_mul hW.adm ps
    have hneg : negLapH qs = (chiD R s).JS u := Cutoff.negLapH_J _ u
    have hform := inner_dom_add Ps qs
    have hsym : ⟪negLapH Ps, (qs : L2H')⟫_ℂ = ⟪(Ps : L2H'), negLapH qs⟫_ℂ := (negLapH_isPositive.1 Ps qs).symm
    have eXq : (chiD R s).Bx u = domX qs := Bx_eq_domX u
    have eYq : (chiD R s).By u = domY qs := By_eq_domY u
    have eXp : (chiC R s).Bx u = domX ps := Bx_eq_domX u
    have eYp : (chiC R s).By u = domY ps := By_eq_domY u
    rw [map_neg, inner_neg_right, hWW, ← hneg, eXq, eYq, eXp, eYp]
    have hmain : ⟪hm p, negLapH qs⟫_ℂ = ⟪mulCL hW.adm.sbX p, domX qs⟫_ℂ + ⟪hm (domX ps), domX qs⟫_ℂ
        + (⟪mulCL hW.adm.sbY p, domY qs⟫_ℂ + ⟪hm (domY ps), domY qs⟫_ℂ) := by
      have e1 : ⟪hm p, negLapH qs⟫_ℂ = ⟪(Ps : L2H'), negLapH qs⟫_ℂ := rfl
      rw [e1, ← hsym, ← hform, hX, hY, inner_add_left, inner_add_left]
    have hconj1 : (⟪Wm (domX qs), Wm (domX ps)⟫_ℂ).re = (⟪hm (domX ps), domX qs⟫_ℂ).re := by
      rw [show (⟪Wm (domX qs), Wm (domX ps)⟫_ℂ).re = (⟪Wm (domX ps), Wm (domX qs)⟫_ℂ).re from
        inner_re_symm (𝕜 := ℂ) _ _, hWW]
    have hconj2 : (⟪Wm (domY qs), Wm (domY ps)⟫_ℂ).re = (⟪hm (domY ps), domY qs⟫_ℂ).re := by
      rw [show (⟪Wm (domY qs), Wm (domY ps)⟫_ℂ).re = (⟪Wm (domY ps), Wm (domY qs)⟫_ℂ).re from
        inner_re_symm (𝕜 := ℂ) _ _, hWW]
    rw [hmain, hconj1, hconj2]
    simp only [Complex.neg_re, Complex.add_re]
    ring
  exact (show HasDerivAt (waveE W hW R u) _ s from hall).congr_deriv hval

/-- **The energy grows at most like `e^{4ρ s}`.** -/
theorem waveE_le {s : ℝ} (hs : 0 ≤ s) : waveE W hW R u s ≤ Real.exp (4 * ρ * s) * waveE W hW R u 0 := by
  set E := waveE W hW R u with hE
  set D : ℝ → ℝ := fun r => -(2 * (⟪mulCL hW.adm.sbX ((chiC R r).J u), (chiD R r).Bx u⟫_ℂ).re)
    - 2 * (⟪mulCL hW.adm.sbY ((chiC R r).J u), (chiD R r).By u⟫_ℂ).re with hD
  have hd : ∀ r, HasDerivAt E (D r) r := waveE_deriv hW R u
  set G : ℝ → ℝ := fun r => Real.exp (-(4 * ρ * r)) * E r with hG
  have hGd : ∀ r, HasDerivAt G (Real.exp (-(4 * ρ * r)) * (-(4 * ρ) * E r + D r)) r := fun r => by
    have h1 : HasDerivAt (fun r : ℝ => -(4 * ρ * r)) (-(4 * ρ)) r := by
      have h0 : HasDerivAt (fun r : ℝ => (-(4 * ρ)) * r) (-(4 * ρ) * 1) r := (hasDerivAt_id' r).const_mul (-(4 * ρ))
      rw [mul_one] at h0
      convert h0 using 1
      funext x; ring
    exact ((h1.exp).mul (hd r)).congr_deriv (by ring)
  have hanti : AntitoneOn G (Icc 0 s) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 s)
      (fun r _ => (hGd r).continuousAt.continuousWithinAt) (fun r _ => (hGd r).differentiableAt.differentiableWithinAt)
      fun r _ => ?_
    rw [(hGd r).deriv]
    refine mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le ?_
    set a := ‖mulCL hW.sb ((chiC R r).J u)‖
    set b1 := ‖mulCL hW.sb ((chiD R r).Bx u)‖
    set b2 := ‖mulCL hW.sb ((chiD R r).By u)‖
    have he1 : ∀ w : ℂ, 0 < w.im → vfR 1 (fun u => W u ^ 2) w = (vfR 1 (fun u => W u ^ 2) w / W w) * W w := fun w hw => by
      have := hW.pos w hw
      field_simp
    have he2 : ∀ w : ℂ, 0 < w.im → vfR Complex.I (fun u => W u ^ 2) w
        = (vfR Complex.I (fun u => W u ^ 2) w / W w) * W w := fun w hw => by
      have := hW.pos w hw
      field_simp
    have c1 := cross_bound hW hW.mX hW.adm.sbX he1 hW.bX ((chiC R r).J u) ((chiD R r).Bx u)
    have c2 := cross_bound hW hW.mY hW.adm.sbY he2 hW.bY ((chiC R r).J u) ((chiD R r).By u)
    have r1 := (Complex.abs_re_le_norm _).trans c1
    have r2 := (Complex.abs_re_le_norm _).trans c2
    have hρ := hW.ρ0
    have ha := norm_nonneg (mulCL hW.sb ((chiC R r).J u))
    have hEeq : E r = a ^ 2 + b1 ^ 2 + b2 ^ 2 := rfl
    have l1 := neg_le_abs (⟪mulCL hW.adm.sbX ((chiC R r).J u), (chiD R r).Bx u⟫_ℂ).re
    have l2 := neg_le_abs (⟪mulCL hW.adm.sbY ((chiC R r).J u), (chiD R r).By u⟫_ℂ).re
    rw [hEeq]
    show -(4 * ρ) * (a ^ 2 + b1 ^ 2 + b2 ^ 2) + (-(2 * (⟪mulCL hW.adm.sbX ((chiC R r).J u), (chiD R r).Bx u⟫_ℂ).re)
      - 2 * (⟪mulCL hW.adm.sbY ((chiC R r).J u), (chiD R r).By u⟫_ℂ).re) ≤ 0
    have hab1 : a * b1 ≤ (a ^ 2 + b1 ^ 2) / 2 := by nlinarith [sq_nonneg (a - b1)]
    have hab2 : a * b2 ≤ (a ^ 2 + b2 ^ 2) / 2 := by nlinarith [sq_nonneg (a - b2)]
    have hb1 : 0 ≤ b1 ^ 2 := sq_nonneg _
    have hb2 : 0 ≤ b2 ^ 2 := sq_nonneg _
    have key : 2 * (2 * ρ * a * b1) + 2 * (2 * ρ * a * b2) ≤ 4 * ρ * (a ^ 2 + b1 ^ 2 + b2 ^ 2) := by
      have : a * b1 + a * b2 ≤ a ^ 2 + b1 ^ 2 + b2 ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left this hρ]
    linarith
  have hle := hanti (left_mem_Icc.2 hs) (right_mem_Icc.2 hs) hs
  simp only [hG, mul_zero, neg_zero, Real.exp_zero, one_mul] at hle
  have hE1 := Real.exp_pos (4 * ρ * s)
  have e : Real.exp (-(4 * ρ * s)) * Real.exp (4 * ρ * s) = 1 := by rw [← Real.exp_add]; simp
  calc E s = Real.exp (4 * ρ * s) * (Real.exp (-(4 * ρ * s)) * E s) := by
        rw [← mul_assoc, mul_comm (Real.exp (4 * ρ * s)), e, one_mul]
    _ ≤ Real.exp (4 * ρ * s) * E 0 := mul_le_mul_of_nonneg_left hle hE1.le

end energy

/-- `cos(sΛ)`. -/
noncomputable def cosOp (s : ℝ) : L2H' →L[ℂ] L2H' := specE.integral fun x => ((Real.cos (s * √x) : ℝ) : ℂ)

lemma cosSymbol_mem (s : ℝ) : (fun x : ℝ => ((Real.cos (s * √x) : ℝ) : ℂ)) ∈ BddMeasurable ℝ :=
  memB_of_abs_le (Real.continuous_cos.comp (continuous_const.mul Real.continuous_sqrt)).measurable
    (fun _ => Real.abs_cos_le_one _)

/-- `cos(sΛ) 1_{[0,n]}(-Δ) → cos(sΛ)` strongly. -/
theorem tendsto_chiC (s : ℝ) (u : L2H') : Tendsto (fun n : ℕ => (chiC n s).J u) atTop (𝓝 (cosOp s u)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  set ξ : ℕ → ℝ → ℂ := fun n x => ((Real.cos (s * √x) * (cutR n x - 1) : ℝ) : ℂ) with hξ
  have hξm : ∀ n, ξ n ∈ BddMeasurable ℝ := fun n => by
    refine memB_of_abs_le (C := 1) ?_ fun x => ?_
    · exact (Real.continuous_cos.comp (continuous_const.mul Real.continuous_sqrt)).measurable.mul
        ((measurable_cutR n).sub_const 1)
    · rw [abs_mul]
      have h1 := Real.abs_cos_le_one (s * √x)
      have h2 : |cutR n x - 1| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith [cutR_nonneg n x, cutR_le_one n x]
      calc |Real.cos (s * √x)| * |cutR n x - 1| ≤ 1 * 1 := mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
        _ = 1 := one_mul 1
  have hop : ∀ n : ℕ, (chiC n s).J u - cosOp s u = specE.integral (ξ n) u := fun n => by
    have e : ξ n = (chiC n s).g + (-1 : ℂ) • fun x : ℝ => ((Real.cos (s * √x) : ℝ) : ℂ) := by
      funext x
      simp only [hξ, Cutoff.g, chiC, cR, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      push_cast
      ring
    rw [e, specE.integral_add (chiC n s).g_mem ((BddMeasurable ℝ).smul_mem _ (cosSymbol_mem s)),
      specE.integral_smul _ (cosSymbol_mem s)]
    simp [cosOp, Cutoff.J, sub_eq_add_neg]
  have hsq : Tendsto (fun n : ℕ => ‖(chiC n s).J u - cosOp s u‖ ^ 2) atTop (𝓝 0) := by
    simp_rw [hop, norm_sq_integral_apply specE (hξm _)]
    have hpos : ∀ᵐ x ∂(specE.assoc u), 0 ≤ x := by
      have h := assoc_Iio_zero u
      rw [ae_iff]
      refine measure_mono_null (fun x hx => ?_) h
      simpa using hx
    have := tendsto_integral_of_dominated_convergence (μ := specE.assoc u) (fun _ : ℝ => (1 : ℝ))
      (F := fun (n : ℕ) x => ‖ξ n x‖ ^ 2) (f := fun _ => 0)
      (fun n => ((hξm n).1.norm.pow_const 2).aestronglyMeasurable) (integrable_const _)
      (fun n => ae_of_all _ fun x => by
        have h := (hξm n).2
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        have hb : ‖ξ n x‖ ≤ 1 := by
          simp only [hξ]
          rw [Complex.norm_real, Real.norm_eq_abs, abs_mul]
          have h1 := Real.abs_cos_le_one (s * √x)
          have h2 : |cutR n x - 1| ≤ 1 := by
            rw [abs_le]; constructor <;> linarith [cutR_nonneg n x, cutR_le_one n x]
          calc |Real.cos (s * √x)| * |cutR n x - 1| ≤ 1 * 1 := mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
            _ = 1 := one_mul 1
        exact pow_le_one₀ (norm_nonneg _) hb)
      (by
        filter_upwards [hpos] with x hx
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop x] with n hn
        have hc : cutR n x = 1 := by simp [cutR, Set.mem_Icc, hx, hn]
        simp [hξ, hc])
    simpa using this
  have hs := hsq.sqrt
  simp only [Real.sqrt_zero, Real.sqrt_sq (norm_nonneg _)] at hs
  exact hs

/-- **`‖W cos(sΛ) u‖ ≤ e^{2ρ|s|} ‖W u‖`.** -/
theorem wave_weight {W : ℂ → ℝ} {C ρ : ℝ} (hW : WaveW W C ρ) (s : ℝ) (u : L2H') :
    ‖mulCL hW.sb (cosOp s u)‖ ≤ Real.exp (2 * ρ * |s|) * ‖mulCL hW.sb u‖ := by
  have hρ := hW.ρ0
  have heven : cosOp s = cosOp |s| := by
    unfold cosOp
    congr 1; funext x
    rcases abs_cases s with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [h]
  rw [heven]
  set t := |s| with ht
  have ht0 : 0 ≤ t := abs_nonneg s
  have hz : cosOp 0 = 1 := by
    have e : (fun x : ℝ => ((Real.cos (0 * √x) : ℝ) : ℂ)) = 1 := by funext x; simp
    rw [cosOp, e, specE.integral_one]
  have h1 : ∀ n : ℕ, ‖mulCL hW.sb ((chiC n t).J u)‖ ≤ Real.exp (2 * ρ * t) * ‖mulCL hW.sb ((chiC n 0).J u)‖ := fun n => by
    have hE := waveE_le hW n u ht0
    have h0D : ∀ v : L2H', (chiD n 0).Bx v = 0 ∧ (chiD n 0).By v = 0 := fun v => by
      have hg : (chiD (n : ℝ) 0).J = 0 ∧ (chiD (n : ℝ) 0).JS = 0 := by
        have e1 : (chiD (n : ℝ) 0).g = (0 : ℂ) • (1 : ℝ → ℂ) := by
          funext x; simp [Cutoff.g, chiD, dR, sincS]
        have e2 : (chiD (n : ℝ) 0).gS = (0 : ℂ) • (1 : ℝ → ℂ) := by
          funext x; simp [Cutoff.gS, chiD, dR, sincS]
        have h1m : (1 : ℝ → ℂ) ∈ BddMeasurable ℝ := ⟨measurable_one, 1, fun _ => by simp⟩
        constructor
        · show specE.integral _ = 0
          rw [e1, specE.integral_smul _ h1m, zero_smul]
        · show specE.integral _ = 0
          rw [e2, specE.integral_smul _ h1m, zero_smul]
      have hd : (chiD (n : ℝ) 0).J + (chiD (n : ℝ) 0).JS = 0 := by rw [hg.1, hg.2, add_zero]
      constructor
      · show formVec 1 (Or.inl rfl) (formLift (((chiD (n : ℝ) 0).J + (chiD (n : ℝ) 0).JS) v)) = 0
        rw [hd]; simp
      · show formVec Complex.I (Or.inr rfl) (formLift (((chiD (n : ℝ) 0).J + (chiD (n : ℝ) 0).JS) v)) = 0
        rw [hd]; simp
    have hE0 : waveE W hW n u 0 = ‖mulCL hW.sb ((chiC n 0).J u)‖ ^ 2 := by
      simp only [waveE, (h0D u).1, (h0D u).2, map_zero, norm_zero]
      ring
    have hle : ‖mulCL hW.sb ((chiC n t).J u)‖ ^ 2 ≤ waveE W hW n u t := by
      simp only [waveE]
      nlinarith [sq_nonneg ‖mulCL hW.sb ((chiD n t).Bx u)‖, sq_nonneg ‖mulCL hW.sb ((chiD n t).By u)‖]
    have hsq : ‖mulCL hW.sb ((chiC n t).J u)‖ ^ 2 ≤ (Real.exp (2 * ρ * t) * ‖mulCL hW.sb ((chiC n 0).J u)‖) ^ 2 := by
      rw [mul_pow, ← Real.exp_nat_mul, ← hE0]
      push_cast
      rw [show (2 : ℝ) * (2 * ρ * t) = 4 * ρ * t by ring]
      exact hle.trans hE
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq
  have ht1 := ((mulCL hW.sb).continuous.tendsto _).comp (tendsto_chiC t u)
  have ht2 := ((mulCL hW.sb).continuous.tendsto _).comp (tendsto_chiC 0 u)
  rw [hz] at ht2
  refine le_of_tendsto_of_tendsto' ht1.norm (ht2.norm.const_mul _) fun n => ?_
  exact h1 n

end Qschubert
