import Qschubert.KLM2b
import Qschubert.KLWeightN

/-!
# The shifted wave group: a sharp weighted energy estimate and finite propagation speed

`cosD r = cos(r √(-Δ - 1/4))`. For a bounded weight with `|∇ log W| ≤ λ`: `‖W cosD(r) u‖ ≤ e^{(λ + 1/2)|r|} ‖W u‖` (`wave_weightD`). Rate `λ` is sharp, and this gives speed one in `ψ = log X₀` (`finite_speed`): only `|∇ψ| ≤ 1` is used, not the distance function.
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set Physicslib4.Spectral Physicslib4.Spectral.Unbounded
open scoped ENNReal InnerProductSpace ComplexConjugate

local notation "L2H'" => Lp ℂ 2 (volume : Measure UpperHalfPlane)

/-- `1_{[1/4,R]}`. -/
noncomputable def cutD (R x : ℝ) : ℝ := (Icc (1 / 4) R).indicator 1 x

lemma measurable_cutD (R : ℝ) : Measurable (cutD R) := measurable_one.indicator measurableSet_Icc

lemma cutD_nonneg (R x : ℝ) : 0 ≤ cutD R x := by unfold cutD; exact indicator_nonneg (fun _ _ => zero_le_one) x

lemma cutD_of_mem {R x : ℝ} (h : x ∈ Icc (1 / 4 : ℝ) R) : cutD R x = 1 := Set.indicator_of_mem h _

lemma cutD_of_notMem {R x : ℝ} (h : x ∉ Icc (1 / 4 : ℝ) R) : cutD R x = 0 := Set.indicator_of_notMem h _

lemma cutD_le_one (R x : ℝ) : cutD R x ≤ 1 := by
  by_cases h : x ∈ Icc (1 / 4 : ℝ) R
  · rw [cutD_of_mem h]
  · rw [cutD_of_notMem h]; norm_num

lemma cutD_le_cutR (R x : ℝ) : cutD R x ≤ cutR R x := by
  by_cases h : x ∈ Icc (1 / 4 : ℝ) R
  · have h2 : x ∈ Icc 0 R := ⟨by linarith [h.1], h.2⟩
    rw [cutD_of_mem h]
    show (1 : ℝ) ≤ (Icc 0 R).indicator 1 x
    rw [Set.indicator_of_mem h2]
    rfl
  · rw [cutD_of_notMem h]
    exact cutR_nonneg R x

/-- The shifted spectral variable. -/
noncomputable def yD (x : ℝ) : ℝ := x - 1 / 4

/-- `cos(s√(x-1/4)) 1_{[1/4,R]}(x)`. -/
noncomputable def cD (R s x : ℝ) : ℝ := Real.cos (s * √(yD x)) * cutD R x

/-- `sin(s√(x-1/4))/√(x-1/4) 1_{[1/4,R]}(x)`. -/
noncomputable def dD (R s x : ℝ) : ℝ := sincS s (√(yD x)) * cutD R x

lemma measurable_sqrt_yD : Measurable fun x : ℝ => √(yD x) := by unfold yD; fun_prop

lemma measurable_cD (R s : ℝ) : Measurable (cD R s) := by
  unfold cD
  exact (Real.continuous_cos.measurable.comp (measurable_const.mul measurable_sqrt_yD)).mul (measurable_cutD R)

lemma measurable_sincS_yD (s : ℝ) : Measurable fun x : ℝ => sincS s (√(yD x)) := by
  unfold sincS
  exact (Real.continuous_sinc.measurable.comp (measurable_const.mul measurable_sqrt_yD)).const_mul s

lemma measurable_dD (R s : ℝ) : Measurable (dD R s) := (measurable_sincS_yD s).mul (measurable_cutD R)

lemma abs_cD_le (R s x : ℝ) : |cD R s x| ≤ cutD R x := by
  unfold cD
  rw [abs_mul, abs_of_nonneg (cutD_nonneg R x)]
  exact mul_le_of_le_one_left (cutD_nonneg R x) (Real.abs_cos_le_one _)

lemma abs_dD_le (R s x : ℝ) : |dD R s x| ≤ |s| * cutD R x := by
  unfold dD
  rw [abs_mul, abs_of_nonneg (cutD_nonneg R x)]
  exact mul_le_mul_of_nonneg_right (abs_sincS_le _ _) (cutD_nonneg R x)

lemma cutD_one_add_le (R x : ℝ) : (1 + |x|) * cutD R x ≤ 1 + |R| :=
  (mul_le_mul_of_nonneg_left (cutD_le_cutR R x) (by positivity)).trans (cut_le_one_add R x)

/-- The cosine cutoff. -/
noncomputable def chiCD (R s : ℝ) : Cutoff where
  r := cD R s
  meas := measurable_cD R s
  C := 1 + |R|
  bound x := (abs_cD_le R s x).trans ((cutD_le_one R x).trans (by linarith [abs_nonneg R]))
  bound1 x := by
    rw [abs_mul]
    calc |1 + x| * |cD R s x| ≤ (1 + |x|) * cutD R x :=
          mul_le_mul (by simpa using abs_add_le 1 x) (abs_cD_le R s x) (abs_nonneg _) (by positivity)
      _ ≤ _ := cutD_one_add_le R x

/-- The sine cutoff. -/
noncomputable def chiDD (R s : ℝ) : Cutoff where
  r := dD R s
  meas := measurable_dD R s
  C := |s| * (1 + |R|)
  bound x := by
    refine (abs_dD_le R s x).trans (mul_le_mul_of_nonneg_left ?_ (abs_nonneg s))
    exact (cutD_le_one R x).trans (by linarith [abs_nonneg R])
  bound1 x := by
    rw [abs_mul]
    calc |1 + x| * |dD R s x| ≤ (1 + |x|) * (|s| * cutD R x) := by
          refine mul_le_mul ?_ (abs_dD_le R s x) (abs_nonneg _) (by positivity)
          simpa using abs_add_le 1 x
      _ = |s| * ((1 + |x|) * cutD R x) := by ring
      _ ≤ |s| * (1 + |R|) := mul_le_mul_of_nonneg_left (cutD_one_add_le R x) (abs_nonneg s)

lemma hasDerivAt_dD (R s x : ℝ) : HasDerivAt (fun r => dD R r x) (cD R s x) s := by
  unfold dD cD
  exact (hasDerivAt_sincS s _).mul_const _

lemma hasDerivAt_cD (R s x : ℝ) : HasDerivAt (fun r => cD R r x) (-(yD x * dD R s x)) s := by
  unfold dD cD
  have h1 : HasDerivAt (fun r : ℝ => r * √(yD x)) (√(yD x)) s := by simpa using (hasDerivAt_id' s).mul_const √(yD x)
  have h2 := (h1.cos).mul_const (cutD R x)
  convert h2 using 1
  by_cases hx : x ∈ Icc (1 / 4 : ℝ) R
  · have hs := sincS_mul s √(yD x)
    have hsq : √(yD x) * √(yD x) = yD x := Real.mul_self_sqrt (by unfold yD; linarith [hx.1])
    rw [← hs]
    nth_rewrite 1 [← hsq]
    ring
  · rw [cutD_of_notMem hx]
    ring

lemma sqrt_yD_le {R x : ℝ} (hx : x ∈ Icc (1 / 4 : ℝ) R) : √(yD x) ≤ 1 + |R| := by
  have h0 : yD x ≤ max R 1 := by
    unfold yD
    linarith [hx.2, le_max_left R 1]
  have h1 : √(yD x) ≤ √(max R 1) := Real.sqrt_le_sqrt h0
  have h2 : √(max R 1) ≤ max R 1 := by
    rw [Real.sqrt_le_left (by positivity)]
    have : 1 ≤ max R 1 := le_max_right _ _
    nlinarith
  have h3 : max R 1 ≤ 1 + |R| := max_le (by linarith [le_abs_self R, abs_nonneg R]) (by linarith [abs_nonneg R])
  linarith

lemma abs_cD_sub_le (R s₁ s₂ x : ℝ) : |cD R s₁ x - cD R s₂ x| ≤ (1 + |R|) * |s₁ - s₂| := by
  unfold cD
  rw [← sub_mul, abs_mul, abs_of_nonneg (cutD_nonneg R x)]
  by_cases hx : x ∈ Icc (1 / 4 : ℝ) R
  · have hc : cutD R x = 1 := cutD_of_mem hx
    rw [hc, mul_one]
    have hsq := sqrt_yD_le hx
    calc |Real.cos (s₁ * √(yD x)) - Real.cos (s₂ * √(yD x))| ≤ |s₁ * √(yD x) - s₂ * √(yD x)| := Real.abs_cos_sub_cos_le _ _
      _ = |s₁ - s₂| * √(yD x) := by rw [← sub_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      _ ≤ (1 + |R|) * |s₁ - s₂| := by nlinarith [abs_nonneg (s₁ - s₂)]
  · have hc : cutD R x = 0 := cutD_of_notMem hx
    rw [hc, mul_zero]; positivity

lemma abs_yD_cut_le (R x : ℝ) : |yD x * cutD R x| ≤ |R| := by
  by_cases hx : x ∈ Icc (1 / 4 : ℝ) R
  · have hc : cutD R x = 1 := cutD_of_mem hx
    rw [hc, mul_one]
    unfold yD
    rw [abs_of_nonneg (by linarith [hx.1])]
    linarith [hx.2, le_abs_self R]
  · have hc : cutD R x = 0 := cutD_of_notMem hx
    rw [hc, mul_zero, abs_zero]; positivity

lemma abs_y_dD_sub_le (R s₁ s₂ x : ℝ) : |yD x * dD R s₁ x - yD x * dD R s₂ x| ≤ |R| * |s₁ - s₂| := by
  unfold dD
  rw [show yD x * (sincS s₁ √(yD x) * cutD R x) - yD x * (sincS s₂ √(yD x) * cutD R x)
    = (sincS s₁ √(yD x) - sincS s₂ √(yD x)) * (yD x * cutD R x) by ring, abs_mul, mul_comm]
  exact mul_le_mul (abs_yD_cut_le R x) (abs_sincS_sub_le _ _ _) (abs_nonneg _) (abs_nonneg _)

lemma hasDerivAt_D_J' (R s : ℝ) : HasDerivAt (fun r => (chiDD R r).J) (chiCD R s).J s := by
  refine hasDerivAt_specE (φ := fun r x => ((dD R r x : ℝ) : ℂ)) (ψ := fun r x => ((cD R r x : ℝ) : ℂ)) (K := 1 + |R|)
    (fun r => (chiDD R r).g_mem) (fun r => (chiCD R r).g_mem) (by positivity) (fun r x => (hasDerivAt_dD R r x).ofReal_comp)
    (fun s₁ s₂ x => ?_) s
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact abs_cD_sub_le R s₁ s₂ x

lemma hasDerivAt_C_J' (R s : ℝ) : HasDerivAt (fun r => (chiCD R r).J) (-(chiDD R s).JS + (1 / 4 : ℂ) • (chiDD R s).J) s := by
  have hm : ∀ r, (fun x : ℝ => ((-(yD x * dD R r x) : ℝ) : ℂ)) ∈ BddMeasurable ℝ := fun r => by
    have e : (fun x : ℝ => ((-(yD x * dD R r x) : ℝ) : ℂ)) = (-1 : ℂ) • (chiDD R r).gS + (1 / 4 : ℂ) • (chiDD R r).g := by
      funext x
      simp only [Cutoff.gS, Cutoff.g, chiDD, yD, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      push_cast
      ring
    rw [e]
    exact (BddMeasurable ℝ).add_mem ((BddMeasurable ℝ).smul_mem _ (chiDD R r).gS_mem) ((BddMeasurable ℝ).smul_mem _ (chiDD R r).g_mem)
  have h := hasDerivAt_specE (φ := fun r x => ((cD R r x : ℝ) : ℂ)) (ψ := fun r x => ((-(yD x * dD R r x) : ℝ) : ℂ)) (K := |R|)
    (fun r => (chiCD R r).g_mem) hm (abs_nonneg R) (fun r x => (hasDerivAt_cD R r x).ofReal_comp)
    (fun s₁ s₂ x => by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        show -(yD x * dD R s₁ x) - -(yD x * dD R s₂ x) = -(yD x * dD R s₁ x - yD x * dD R s₂ x) by ring, abs_neg]
      exact abs_y_dD_sub_le R s₁ s₂ x) s
  have h' : HasDerivAt (fun r => (chiCD R r).J) (specE.integral fun x : ℝ => ((-(yD x * dD R s x) : ℝ) : ℂ)) s := h
  convert h' using 1
  have e : (fun x : ℝ => ((-(yD x * dD R s x) : ℝ) : ℂ)) = (-1 : ℂ) • (chiDD R s).gS + (1 / 4 : ℂ) • (chiDD R s).g := by
    funext x
    simp only [Cutoff.gS, Cutoff.g, chiDD, yD, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring
  rw [e, specE.integral_add ((BddMeasurable ℝ).smul_mem _ (chiDD R s).gS_mem) ((BddMeasurable ℝ).smul_mem _ (chiDD R s).g_mem),
    specE.integral_smul _ (chiDD R s).gS_mem, specE.integral_smul _ (chiDD R s).g_mem]
  simp [Cutoff.JS, Cutoff.J]

lemma hasDerivAt_D_JS' (R s : ℝ) : HasDerivAt (fun r => (chiDD R r).JS) (chiCD R s).JS s := by
  refine hasDerivAt_specE (φ := fun r x => ((x * dD R r x : ℝ) : ℂ)) (ψ := fun r x => ((x * cD R r x : ℝ) : ℂ))
    (K := (1 + |R|) ^ 2) (fun r => (chiDD R r).gS_mem) (fun r => (chiCD R r).gS_mem) (by positivity)
    (fun r x => ((hasDerivAt_dD R r x).const_mul x).ofReal_comp) (fun s₁ s₂ x => ?_) s
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, ← mul_sub, abs_mul]
  by_cases hx : x ∈ Icc (1 / 4 : ℝ) R
  · have hxR : |x| ≤ 1 + |R| := by
      rw [abs_of_nonneg (by linarith [hx.1])]; linarith [hx.2, le_abs_self R]
    calc |x| * |cD R s₁ x - cD R s₂ x| ≤ (1 + |R|) * ((1 + |R|) * |s₁ - s₂|) :=
          mul_le_mul hxR (abs_cD_sub_le R s₁ s₂ x) (abs_nonneg _) (by positivity)
      _ = _ := by ring
  · have hc : cutD R x = 0 := cutD_of_notMem hx
    simp only [cD, hc, mul_zero, sub_self, abs_zero]
    positivity

/-- `‖f‖² = ∫ ‖f z‖²`. -/
lemma norm_sq_int (f : L2H') : ‖f‖ ^ 2 = ∫ z, ‖f z‖ ^ 2 := by
  rw [@norm_sq_eq_re_inner ℂ, L2.inner_def, RCLike.re_to_complex]
  have hi : Integrable (fun z => (inner ℂ (f z) (f z) : ℂ)) := L2.integrable_inner f f
  have := Complex.reCLM.integral_comp_comm hi
  rw [show (∫ z, (inner ℂ (f z) (f z) : ℂ)).re = Complex.reCLM (∫ z, (inner ℂ (f z) (f z) : ℂ)) from rfl, ← this]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  show (inner ℂ (f z) (f z) : ℂ).re = _
  rw [@inner_self_eq_norm_sq_to_K ℂ]
  norm_cast

/-- The elementary inequality behind the sharp rate. -/
lemma cross_real {x₁ x₂ a b₁ b₂ w l : ℝ} (hl : 0 ≤ l) (hw : 0 < w) (ha : 0 ≤ a) (h1 : 0 ≤ b₁) (h2 : 0 ≤ b₂)
    (h : x₁ ^ 2 + x₂ ^ 2 ≤ (2 * l * w ^ 2) ^ 2) :
    |x₁| * a * b₁ + |x₂| * a * b₂ ≤ l * ((w * a) ^ 2 + (w * b₁) ^ 2 + (w * b₂) ^ 2) := by
  set S := |x₁| * b₁ + |x₂| * b₂ with hS
  have hS0 : 0 ≤ S := by positivity
  have hsq : S ^ 2 ≤ (2 * l * w ^ 2) ^ 2 * (b₁ ^ 2 + b₂ ^ 2) := by
    have e1 : |x₁| ^ 2 = x₁ ^ 2 := sq_abs x₁
    have e2 : |x₂| ^ 2 = x₂ ^ 2 := sq_abs x₂
    have hc : S ^ 2 ≤ (x₁ ^ 2 + x₂ ^ 2) * (b₁ ^ 2 + b₂ ^ 2) := by
      rw [hS, ← e1, ← e2]
      nlinarith [sq_nonneg (|x₁| * b₂ - |x₂| * b₁)]
    exact hc.trans (mul_le_mul_of_nonneg_right h (by positivity))
  rcases hl.eq_or_lt with h0 | h0
  · subst h0
    have : S ^ 2 ≤ 0 := by simpa using hsq
    have hS00 : S = 0 := by nlinarith [sq_nonneg S]
    have e : |x₁| * a * b₁ + |x₂| * a * b₂ = a * S := by rw [hS]; ring
    rw [e, hS00]; simp
  · set t := 2 * l * w ^ 2 with ht
    have ht0 : 0 < t := by positivity
    have key : t * (a * S) ≤ t * (l * w ^ 2 * (a ^ 2 + b₁ ^ 2 + b₂ ^ 2)) := by
      have e3 : t * (l * w ^ 2 * (a ^ 2 + b₁ ^ 2 + b₂ ^ 2)) = t ^ 2 * (a ^ 2 + b₁ ^ 2 + b₂ ^ 2) / 2 := by
        rw [ht]; ring
      rw [e3]
      nlinarith [sq_nonneg (t * a - S)]
    have h3 := le_of_mul_le_mul_left key ht0
    have e : |x₁| * a * b₁ + |x₂| * a * b₂ = a * S := by rw [hS]; ring
    rw [e]
    refine h3.trans (le_of_eq ?_)
    ring

/-- A bounded weight with `|∇ log W| ≤ l`. -/
structure WaveS (W : ℂ → ℝ) (C l : ℝ) : Prop where
  pos : ∀ w : ℂ, 0 < w.im → 0 < W w
  sb : SB W C
  adm : Adm (fun w => W w ^ 2) C
  l0 : 0 ≤ l
  grad : ∀ w : ℂ, 0 < w.im →
    (vfR 1 (fun u => W u ^ 2) w) ^ 2 + (vfR Complex.I (fun u => W u ^ 2) w) ^ 2 ≤ (2 * l * W w ^ 2) ^ 2

lemma re_inner_int (f g : L2H') : (⟪f, g⟫_ℂ).re = ∫ z, (inner ℂ (f z) (g z) : ℂ).re := by
  rw [L2.inner_def]
  have hi : Integrable (fun z => (inner ℂ (f z) (g z) : ℂ)) := L2.integrable_inner f g
  exact (Complex.reCLM.integral_comp_comm hi).symm

lemma integrable_re_inner (f g : L2H') : Integrable fun z => (inner ℂ (f z) (g z) : ℂ).re := by
  have hi : Integrable (fun z => (inner ℂ (f z) (g z) : ℂ)) := L2.integrable_inner f g
  exact Complex.reCLM.integrable_comp hi

lemma integrable_norm_sq (f : L2H') : Integrable fun z => ‖f z‖ ^ 2 :=
  (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).1 (Lp.memLp f)

section energy

variable {W : ℂ → ℝ} {C l : ℝ} (hW : WaveS W C l) (R : ℝ) (u : L2H')
include hW

/-- **The sharp cross term.** -/
lemma cross_sharp (p b₁ b₂ : L2H') :
    -(2 * (⟪mulCL hW.adm.sbX p, b₁⟫_ℂ).re) - 2 * (⟪mulCL hW.adm.sbY p, b₂⟫_ℂ).re
      ≤ 2 * l * (‖mulCL hW.sb p‖ ^ 2 + ‖mulCL hW.sb b₁‖ ^ 2 + ‖mulCL hW.sb b₂‖ ^ 2) := by
  set A₁ := mulCL hW.adm.sbX p with hA₁
  set A₂ := mulCL hW.adm.sbY p with hA₂
  set P := mulCL hW.sb p with hP
  set Q₁ := mulCL hW.sb b₁ with hQ₁
  set Q₂ := mulCL hW.sb b₂ with hQ₂
  have i1 := integrable_re_inner A₁ b₁
  have i2 := integrable_re_inner A₂ b₂
  have nP := integrable_norm_sq P
  have nQ1 := integrable_norm_sq Q₁
  have nQ2 := integrable_norm_sq Q₂
  have i1' : Integrable fun z => -(2 * (inner ℂ (A₁ z) (b₁ z) : ℂ).re) := (i1.const_mul 2).neg
  have i2' : Integrable fun z => 2 * (inner ℂ (A₂ z) (b₂ z) : ℂ).re := i2.const_mul 2
  have n12 : Integrable fun z => ‖P z‖ ^ 2 + ‖Q₁ z‖ ^ 2 := nP.add nQ1
  have n123 : Integrable fun z => ‖P z‖ ^ 2 + ‖Q₁ z‖ ^ 2 + ‖Q₂ z‖ ^ 2 := n12.add nQ2
  have hL : -(2 * (⟪A₁, b₁⟫_ℂ).re) - 2 * (⟪A₂, b₂⟫_ℂ).re
      = ∫ z, (-(2 * (inner ℂ (A₁ z) (b₁ z) : ℂ).re) - 2 * (inner ℂ (A₂ z) (b₂ z) : ℂ).re) := by
    rw [re_inner_int, re_inner_int, integral_sub i1' i2', integral_neg, integral_const_mul, integral_const_mul]
  have hR : 2 * l * (‖P‖ ^ 2 + ‖Q₁‖ ^ 2 + ‖Q₂‖ ^ 2) = ∫ z, 2 * l * (‖P z‖ ^ 2 + ‖Q₁ z‖ ^ 2 + ‖Q₂ z‖ ^ 2) := by
    rw [norm_sq_int P, norm_sq_int Q₁, norm_sq_int Q₂, integral_const_mul, integral_add n12 nQ2, integral_add nP nQ1]
  rw [hL, hR]
  refine integral_mono_ae (i1'.sub i2') (n123.const_mul _) ?_
  filter_upwards [coe_mulCL hW.adm.sbX p, coe_mulCL hW.adm.sbY p, coe_mulCL hW.sb p, coe_mulCL hW.sb b₁, coe_mulCL hW.sb b₂]
    with z e1 e2 e3 e4 e5
  have hw := hW.pos z z.im_pos
  have hg := hW.grad z z.im_pos
  have hc := cross_real hW.l0 hw (norm_nonneg (p z)) (norm_nonneg (b₁ z)) (norm_nonneg (b₂ z)) hg
  have n1 : ‖A₁ z‖ = |vfR 1 (fun u => W u ^ 2) z| * ‖p z‖ := by
    rw [hA₁, e1, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have n2 : ‖A₂ z‖ = |vfR Complex.I (fun u => W u ^ 2) z| * ‖p z‖ := by
    rw [hA₂, e2, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have n3 : ‖P z‖ = W z * ‖p z‖ := by
    rw [hP, e3, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw]
  have n4 : ‖Q₁ z‖ = W z * ‖b₁ z‖ := by
    rw [hQ₁, e4, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw]
  have n5 : ‖Q₂ z‖ = W z * ‖b₂ z‖ := by
    rw [hQ₂, e5, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw]
  have t1 : -(2 * (inner ℂ (A₁ z) (b₁ z) : ℂ).re) ≤ 2 * (|vfR 1 (fun u => W u ^ 2) z| * ‖p z‖ * ‖b₁ z‖) := by
    have h1 := (Complex.abs_re_le_norm _).trans (norm_inner_le_norm (𝕜 := ℂ) (A₁ z) (b₁ z))
    rw [n1] at h1
    linarith [neg_le_abs (inner ℂ (A₁ z) (b₁ z) : ℂ).re]
  have t2 : -(2 * (inner ℂ (A₂ z) (b₂ z) : ℂ).re) ≤ 2 * (|vfR Complex.I (fun u => W u ^ 2) z| * ‖p z‖ * ‖b₂ z‖) := by
    have h1 := (Complex.abs_re_le_norm _).trans (norm_inner_le_norm (𝕜 := ℂ) (A₂ z) (b₂ z))
    rw [n2] at h1
    linarith [neg_le_abs (inner ℂ (A₂ z) (b₂ z) : ℂ).re]
  rw [n3, n4, n5]
  linarith

/-- The shifted energy. -/
noncomputable def waveED (W : ℂ → ℝ) (hW : WaveS W C l) (R : ℝ) (u : L2H') (s : ℝ) : ℝ :=
  ‖mulCL hW.sb ((chiCD R s).J u)‖ ^ 2 + ‖mulCL hW.sb ((chiDD R s).Bx u)‖ ^ 2 + ‖mulCL hW.sb ((chiDD R s).By u)‖ ^ 2
    + 1 / 4 * ‖mulCL hW.sb ((chiDD R s).J u)‖ ^ 2

/-- **The derivative of the shifted energy.** -/
theorem waveED_deriv (s : ℝ) :
    HasDerivAt (waveED W hW R u)
      (-(2 * (⟪mulCL hW.adm.sbX ((chiCD R s).J u), (chiDD R s).Bx u⟫_ℂ).re)
        - 2 * (⟪mulCL hW.adm.sbY ((chiCD R s).J u), (chiDD R s).By u⟫_ℂ).re
        + (⟪mulCL hW.sb ((chiCD R s).J u), mulCL hW.sb ((chiDD R s).J u)⟫_ℂ).re) s := by
  set Wm := mulCL hW.sb with hWm
  set hm := mulCL hW.adm.sb with hhm
  set p := (chiCD R s).J u with hp
  set q := (chiDD R s).J u with hq
  have hpd : HasDerivAt (fun r => (chiCD R r).J u) (-(chiDD R s).JS u + (1 / 4 : ℂ) • q) s := by
    have h : HasDerivAt (fun r => (chiCD R r).J u) _ s := hasDerivAt_clm_apply_C (hasDerivAt_C_J' R s) (hasDerivAt_const s u)
    convert h using 1
    simp [hq]
  have hqd : HasDerivAt (fun r => (chiDD R r).J u) p s := by
    have h : HasDerivAt (fun r => (chiDD R r).J u) _ s := hasDerivAt_clm_apply_C (hasDerivAt_D_J' R s) (hasDerivAt_const s u)
    convert h using 1
    simp [hp]
  have hDd : HasDerivAt (fun r => ((chiDD R r).J + (chiDD R r).JS) u) (((chiCD R s).J + (chiCD R s).JS) u) s := by
    have h : HasDerivAt (fun r => ((chiDD R r).J + (chiDD R r).JS) u) _ s :=
      hasDerivAt_clm_apply_C ((hasDerivAt_D_J' R s).add (hasDerivAt_D_JS' R s)) (hasDerivAt_const s u)
    convert h using 1
    simp
  have hXd : HasDerivAt (fun r => (chiDD R r).Bx u) ((chiCD R s).Bx u) s :=
    hasDerivAt_clm_comp (A := (formVec 1 (Or.inl rfl)).comp formLift) hDd
  have hYd : HasDerivAt (fun r => (chiDD R r).By u) ((chiCD R s).By u) s :=
    hasDerivAt_clm_comp (A := (formVec Complex.I (Or.inr rfl)).comp formLift) hDd
  have h1 := hasDerivAt_norm_sq_C (hasDerivAt_clm_comp (A := Wm) hpd)
  have h2 := hasDerivAt_norm_sq_C (hasDerivAt_clm_comp (A := Wm) hXd)
  have h3 := hasDerivAt_norm_sq_C (hasDerivAt_clm_comp (A := Wm) hYd)
  have h4 := (hasDerivAt_norm_sq_C (hasDerivAt_clm_comp (A := Wm) hqd)).const_mul (1 / 4 : ℝ)
  have hall := ((h1.add h2).add h3).add h4
  have hval : 2 * (⟪Wm p, Wm (-(chiDD R s).JS u + (1 / 4 : ℂ) • q)⟫_ℂ).re + 2 * (⟪Wm ((chiDD R s).Bx u), Wm ((chiCD R s).Bx u)⟫_ℂ).re
        + 2 * (⟪Wm ((chiDD R s).By u), Wm ((chiCD R s).By u)⟫_ℂ).re + 1 / 4 * (2 * (⟪Wm q, Wm p⟫_ℂ).re)
      = -(2 * (⟪mulCL hW.adm.sbX p, (chiDD R s).Bx u⟫_ℂ).re) - 2 * (⟪mulCL hW.adm.sbY p, (chiDD R s).By u⟫_ℂ).re + (⟪Wm p, Wm q⟫_ℂ).re := by
    set ps : negLapH.domain := ⟨p, (chiCD R s).J_mem u⟩ with hps
    set qs : negLapH.domain := ⟨q, (chiDD R s).J_mem u⟩ with hqs
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
    have hneg : negLapH qs = (chiDD R s).JS u := Cutoff.negLapH_J _ u
    have hform := inner_dom_add Ps qs
    have hsym : ⟪negLapH Ps, (qs : L2H')⟫_ℂ = ⟪(Ps : L2H'), negLapH qs⟫_ℂ := (negLapH_isPositive.1 Ps qs).symm
    have eXq : (chiDD R s).Bx u = domX qs := Bx_eq_domX u
    have eYq : (chiDD R s).By u = domY qs := By_eq_domY u
    have eXp : (chiCD R s).Bx u = domX ps := Bx_eq_domX u
    have eYp : (chiCD R s).By u = domY ps := By_eq_domY u
    have esplit : ⟪Wm p, Wm (-(chiDD R s).JS u + (1 / 4 : ℂ) • q)⟫_ℂ = -⟪Wm p, Wm ((chiDD R s).JS u)⟫_ℂ + ((1 / 4 : ℝ) : ℂ) * ⟪Wm p, Wm q⟫_ℂ := by
      rw [map_add, map_neg, map_smul, inner_add_right, inner_neg_right, inner_smul_right]
      norm_num
    rw [esplit, hWW p ((chiDD R s).JS u), ← hneg, eXq, eYq, eXp, eYp]
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
    have hconj3 : (⟪Wm q, Wm p⟫_ℂ).re = (⟪Wm p, Wm q⟫_ℂ).re := inner_re_symm (𝕜 := ℂ) _ _
    rw [hmain, hconj1, hconj2, hconj3, Complex.add_re, Complex.neg_re, Complex.re_ofReal_mul]
    simp only [Complex.add_re]
    ring
  exact (show HasDerivAt (waveED W hW R u) _ s from hall).congr_deriv hval

/-- **The shifted energy grows at most like `e^{(2l+1)s}`.** -/
theorem waveED_le {s : ℝ} (hs : 0 ≤ s) : waveED W hW R u s ≤ Real.exp ((2 * l + 1) * s) * waveED W hW R u 0 := by
  set E := waveED W hW R u with hE
  set D : ℝ → ℝ := fun r => -(2 * (⟪mulCL hW.adm.sbX ((chiCD R r).J u), (chiDD R r).Bx u⟫_ℂ).re)
    - 2 * (⟪mulCL hW.adm.sbY ((chiCD R r).J u), (chiDD R r).By u⟫_ℂ).re
    + (⟪mulCL hW.sb ((chiCD R r).J u), mulCL hW.sb ((chiDD R r).J u)⟫_ℂ).re with hD
  have hd : ∀ r, HasDerivAt E (D r) r := waveED_deriv hW R u
  set c := 2 * l + 1 with hc
  set G : ℝ → ℝ := fun r => Real.exp (-(c * r)) * E r with hG
  have hGd : ∀ r, HasDerivAt G (Real.exp (-(c * r)) * (-c * E r + D r)) r := fun r => by
    have h1 : HasDerivAt (fun r : ℝ => -(c * r)) (-c) r := by
      have h0 : HasDerivAt (fun r : ℝ => (-c) * r) (-c * 1) r := (hasDerivAt_id' r).const_mul (-c)
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
    have hl := hW.l0
    have hcross := cross_sharp hW ((chiCD R r).J u) ((chiDD R r).Bx u) ((chiDD R r).By u)
    set a := ‖mulCL hW.sb ((chiCD R r).J u)‖ with ha
    set b1 := ‖mulCL hW.sb ((chiDD R r).Bx u)‖
    set b2 := ‖mulCL hW.sb ((chiDD R r).By u)‖
    set e := ‖mulCL hW.sb ((chiDD R r).J u)‖ with he
    have hEeq : E r = a ^ 2 + b1 ^ 2 + b2 ^ 2 + 1 / 4 * e ^ 2 := rfl
    have hip : (⟪mulCL hW.sb ((chiCD R r).J u), mulCL hW.sb ((chiDD R r).J u)⟫_ℂ).re ≤ a * e :=
      (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
    have hae : a * e ≤ a ^ 2 + 1 / 4 * e ^ 2 := by nlinarith [sq_nonneg (a - e / 2)]
    show -c * E r + D r ≤ 0
    simp only [hD]
    rw [hEeq, hc]
    have h3 : 0 ≤ l * e ^ 2 := by positivity
    have h4 := sq_nonneg b1
    have h5 := sq_nonneg b2
    nlinarith
  have hle := hanti (left_mem_Icc.2 hs) (right_mem_Icc.2 hs) hs
  simp only [hG, mul_zero, neg_zero, Real.exp_zero, one_mul] at hle
  have hE1 := Real.exp_pos (c * s)
  have e : Real.exp (-(c * s)) * Real.exp (c * s) = 1 := by rw [← Real.exp_add]; simp
  calc E s = Real.exp (c * s) * (Real.exp (-(c * s)) * E s) := by
        rw [← mul_assoc, mul_comm (Real.exp (c * s)), e, one_mul]
    _ ≤ Real.exp (c * s) * E 0 := mul_le_mul_of_nonneg_left hle hE1.le

end energy

/-- `cos(r √(-Δ - 1/4))`. -/
noncomputable def cosDOp (s : ℝ) : L2H' →L[ℂ] L2H' := specE.integral fun x => ((Real.cos (s * √(yD x)) : ℝ) : ℂ)

lemma cosDSymbol_mem (s : ℝ) : (fun x : ℝ => ((Real.cos (s * √(yD x)) : ℝ) : ℂ)) ∈ BddMeasurable ℝ :=
  memB_of_abs_le (Real.continuous_cos.measurable.comp (measurable_const.mul measurable_sqrt_yD)) (fun _ => Real.abs_cos_le_one _)

/-- The spectrum of `-Δ` lies in `[1/4, ∞)`. -/
lemma assoc_Iio_quarter (u : L2H') : specE.assoc u (Iio (1 / 4)) = 0 := by
  rw [assoc_eq_map, Measure.map_apply measurable_mKL measurableSet_Iio]
  have e : mKL ⁻¹' Iio (1 / 4) = ∅ := by
    ext p
    simp only [mem_preimage, mem_Iio, mem_empty_iff_false, iff_false, not_lt]
    unfold mKL
    nlinarith [sq_nonneg p.2]
  rw [e, measure_empty]

/-- `cos(rD) 1_{[1/4,n]}(-Δ) → cos(rD)` strongly. -/
theorem tendsto_chiCD (s : ℝ) (u : L2H') : Tendsto (fun n : ℕ => (chiCD n s).J u) atTop (𝓝 (cosDOp s u)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  set ξ : ℕ → ℝ → ℂ := fun n x => ((Real.cos (s * √(yD x)) * (cutD n x - 1) : ℝ) : ℂ) with hξ
  have hbd : ∀ n x, ‖ξ n x‖ ≤ 1 := fun n x => by
    simp only [hξ]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul]
    have h1 := Real.abs_cos_le_one (s * √(yD x))
    have h2 : |cutD n x - 1| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith [cutD_nonneg n x, cutD_le_one n x]
    calc |Real.cos (s * √(yD x))| * |cutD n x - 1| ≤ 1 * 1 := mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hξm : ∀ n, ξ n ∈ BddMeasurable ℝ := fun n =>
    ⟨Complex.measurable_ofReal.comp ((Real.continuous_cos.measurable.comp (measurable_const.mul measurable_sqrt_yD)).mul
      ((measurable_cutD n).sub_const 1)), 1, hbd n⟩
  have hop : ∀ n : ℕ, (chiCD n s).J u - cosDOp s u = specE.integral (ξ n) u := fun n => by
    have e : ξ n = (chiCD n s).g + (-1 : ℂ) • fun x : ℝ => ((Real.cos (s * √(yD x)) : ℝ) : ℂ) := by
      funext x
      simp only [hξ, Cutoff.g, chiCD, cD, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      push_cast
      ring
    rw [e, specE.integral_add (chiCD n s).g_mem ((BddMeasurable ℝ).smul_mem _ (cosDSymbol_mem s)),
      specE.integral_smul _ (cosDSymbol_mem s)]
    simp [cosDOp, Cutoff.J, sub_eq_add_neg]
  have hsq : Tendsto (fun n : ℕ => ‖(chiCD n s).J u - cosDOp s u‖ ^ 2) atTop (𝓝 0) := by
    simp_rw [hop, norm_sq_integral_apply specE (hξm _)]
    have hpos : ∀ᵐ x ∂(specE.assoc u), 1 / 4 ≤ x := by
      rw [ae_iff]
      refine measure_mono_null (fun x hx => ?_) (assoc_Iio_quarter u)
      simpa using hx
    have := tendsto_integral_of_dominated_convergence (μ := specE.assoc u) (fun _ : ℝ => (1 : ℝ))
      (F := fun (n : ℕ) x => ‖ξ n x‖ ^ 2) (f := fun _ => 0)
      (fun n => ((hξm n).1.norm.pow_const 2).aestronglyMeasurable) (integrable_const _)
      (fun n => ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact pow_le_one₀ (norm_nonneg _) (hbd n x))
      (by
        filter_upwards [hpos] with x hx
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop x] with n hn
        have hc : cutD n x = 1 := cutD_of_mem ⟨hx, hn⟩
        simp [hξ, hc])
    simpa using this
  have hs := hsq.sqrt
  simp only [Real.sqrt_zero, Real.sqrt_sq (norm_nonneg _)] at hs
  exact hs

/-- **`‖W cos(rD) u‖ ≤ e^{(l + 1/2)|r|} ‖W u‖`.** -/
theorem wave_weightD {W : ℂ → ℝ} {C l : ℝ} (hW : WaveS W C l) (s : ℝ) (u : L2H') :
    ‖mulCL hW.sb (cosDOp s u)‖ ≤ Real.exp ((l + 1 / 2) * |s|) * ‖mulCL hW.sb u‖ := by
  have hl := hW.l0
  have heven : cosDOp s = cosDOp |s| := by
    unfold cosDOp
    congr 1; funext x
    rcases abs_cases s with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [h]
  rw [heven]
  set t := |s| with ht
  have ht0 : 0 ≤ t := abs_nonneg s
  have hz : cosDOp 0 = 1 := by
    have e : (fun x : ℝ => ((Real.cos (0 * √(yD x)) : ℝ) : ℂ)) = 1 := by funext x; simp
    rw [cosDOp, e, specE.integral_one]
  have h1 : ∀ n : ℕ, ‖mulCL hW.sb ((chiCD n t).J u)‖ ≤ Real.exp ((l + 1 / 2) * t) * ‖mulCL hW.sb ((chiCD n 0).J u)‖ := fun n => by
    have hE := waveED_le hW n u ht0
    have hg : (chiDD (n : ℝ) 0).J = 0 ∧ (chiDD (n : ℝ) 0).JS = 0 := by
      have e1 : (chiDD (n : ℝ) 0).g = (0 : ℂ) • (1 : ℝ → ℂ) := by
        funext x; simp [Cutoff.g, chiDD, dD, sincS]
      have e2 : (chiDD (n : ℝ) 0).gS = (0 : ℂ) • (1 : ℝ → ℂ) := by
        funext x; simp [Cutoff.gS, chiDD, dD, sincS]
      have h1m : (1 : ℝ → ℂ) ∈ BddMeasurable ℝ := ⟨measurable_one, 1, fun _ => by simp⟩
      constructor
      · show specE.integral _ = 0
        rw [e1, specE.integral_smul _ h1m, zero_smul]
      · show specE.integral _ = 0
        rw [e2, specE.integral_smul _ h1m, zero_smul]
    have hd : (chiDD (n : ℝ) 0).J + (chiDD (n : ℝ) 0).JS = 0 := by rw [hg.1, hg.2, add_zero]
    have hBx : (chiDD (n : ℝ) 0).Bx u = 0 := by
      show formVec 1 (Or.inl rfl) (formLift (((chiDD (n : ℝ) 0).J + (chiDD (n : ℝ) 0).JS) u)) = 0
      rw [hd]; simp
    have hBy : (chiDD (n : ℝ) 0).By u = 0 := by
      show formVec Complex.I (Or.inr rfl) (formLift (((chiDD (n : ℝ) 0).J + (chiDD (n : ℝ) 0).JS) u)) = 0
      rw [hd]; simp
    have hE0 : waveED W hW n u 0 = ‖mulCL hW.sb ((chiCD n 0).J u)‖ ^ 2 := by
      simp only [waveED, hBx, hBy, hg.1, ContinuousLinearMap.zero_apply, map_zero, norm_zero]
      ring
    have hle : ‖mulCL hW.sb ((chiCD n t).J u)‖ ^ 2 ≤ waveED W hW n u t := by
      simp only [waveED]
      nlinarith [sq_nonneg ‖mulCL hW.sb ((chiDD n t).Bx u)‖, sq_nonneg ‖mulCL hW.sb ((chiDD n t).By u)‖,
        sq_nonneg ‖mulCL hW.sb ((chiDD n t).J u)‖]
    have hsq : ‖mulCL hW.sb ((chiCD n t).J u)‖ ^ 2 ≤ (Real.exp ((l + 1 / 2) * t) * ‖mulCL hW.sb ((chiCD n 0).J u)‖) ^ 2 := by
      rw [mul_pow, ← Real.exp_nat_mul, ← hE0]
      push_cast
      rw [show (2 : ℝ) * ((l + 1 / 2) * t) = (2 * l + 1) * t by ring]
      exact hle.trans hE
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq
  have ht1 := ((mulCL hW.sb).continuous.tendsto _).comp (tendsto_chiCD t u)
  have ht2 := ((mulCL hW.sb).continuous.tendsto _).comp (tendsto_chiCD 0 u)
  rw [hz] at ht2
  refine le_of_tendsto_of_tendsto' ht1.norm (ht2.norm.const_mul _) fun n => ?_
  exact h1 n

lemma xi_up_sq (w : ℂ) : xiF w ^ 2 + (upF w + -1) ^ 2 ≤ 1 := by
  have hN := normN_pos w
  have e : xiF w ^ 2 + (upF w + -1) ^ 2 = 1 - (2 * w.im / normN w) ^ 2 := by
    unfold xiF upF
    have hne := hN.ne'
    field_simp
    unfold normN
    ring
  rw [e]
  nlinarith [sq_nonneg (2 * w.im / normN w)]

/-- The truncated weights have `|∇ log W| ≤ γ`, with no loss. -/
theorem waveS_Wn {γ : ℝ} (hγ : 0 ≤ γ) (n : ℕ) (hn : 0 < n) : ∃ C, WaveS (Wn γ n) C γ := by
  obtain ⟨K, -, h⟩ := waveW3_Wn hγ
  obtain ⟨C, hC⟩ := h n hn
  refine ⟨C, ⟨fun w hw => Wn_pos γ n hn hw, hC.sb, hC.adm, hγ, fun w hw => ?_⟩⟩
  have h1 := vfR_pow_Wn γ n hn hw 1 (vfR_Wn_one γ n hn hw) 2
  have h2 := vfR_pow_Wn γ n hn hw Complex.I (vfR_Wn_I γ n hn hw) 2
  rw [h1, h2]
  have hp0 := (pN_pos γ n hn hw).le
  have hp1 := pN_le γ n hn hw
  have hx := xi_up_sq w
  unfold aX aY
  set p := pN γ n w
  set x := xiF w
  set y := upF w + -1
  set q := Wn γ n w ^ 2
  have hp2 : p ^ 2 ≤ 1 := pow_le_one₀ hp0 hp1
  have hq : 0 ≤ q ^ 2 * γ ^ 2 := by positivity
  have e1 : ((2 : ℕ) : ℝ) = 2 := by norm_num
  rw [e1]
  have hb : p ^ 2 * (x ^ 2 + y ^ 2) ≤ 1 := by
    calc p ^ 2 * (x ^ 2 + y ^ 2) ≤ 1 * 1 := mul_le_mul hp2 hx (by positivity) zero_le_one
      _ = 1 := one_mul 1
  have e2 : (2 * q * (γ * (x * p))) ^ 2 + (2 * q * (γ * (y * p))) ^ 2 = 4 * (q ^ 2 * γ ^ 2) * (p ^ 2 * (x ^ 2 + y ^ 2)) := by ring
  have e3 : (2 * γ * q) ^ 2 = 4 * (q ^ 2 * γ ^ 2) * 1 := by ring
  rw [e2, e3]
  exact mul_le_mul_of_nonneg_left hb (by positivity)

lemma measurable_psi_coe : Measurable fun z : UpperHalfPlane => psiF (z : ℂ) := by
  have : Continuous fun z : UpperHalfPlane => psiF (z : ℂ) :=
    continuous_iff_continuousAt.2 fun z =>
      ((contDiffAt_psiF z.im_pos).continuousAt).comp UpperHalfPlane.continuous_coe.continuousAt
  exact this.measurable

lemma tauG_eq {w : ℂ} (hw : 0 < w.im) (γ : ℝ) : tauG γ w = Real.exp (-(γ * psiF w)) := by
  have h := hF_pos hw
  unfold tauG psiF
  rw [Real.rpow_def_of_pos h]
  congr 1
  ring

lemma Wn_le_of_psi {γ a : ℝ} (hγ : 0 ≤ γ) (n : ℕ) (hn : 0 < n) {w : ℂ} (hw : 0 < w.im) (h : psiF w ≤ a) :
    Wn γ n w ≤ Real.exp (γ * a) := by
  refine (Wn_le_lim γ n hn hw).trans ?_
  rw [tauG_eq hw, ← Real.exp_neg, neg_neg]
  exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left h hγ)

lemma Wn_ge_of_psi {γ b : ℝ} (hγ : 0 ≤ γ) (n : ℕ) (hn : 0 < n) (hnb : Real.exp (γ * b) ≤ n) {w : ℂ} (hw : 0 < w.im)
    (h : b ≤ psiF w) : Real.exp (γ * b) / 2 ≤ Wn γ n w := by
  have hE := Real.exp_pos (γ * b)
  have ht : tauG γ w ≤ (Real.exp (γ * b))⁻¹ := by
    rw [tauG_eq hw, ← Real.exp_neg]
    exact Real.exp_le_exp.2 (by nlinarith [mul_le_mul_of_nonneg_left h hγ])
  have hn' : (n : ℝ)⁻¹ ≤ (Real.exp (γ * b))⁻¹ := inv_anti₀ hE hnb
  have hsum := sum_pos γ n hn hw
  unfold Wn
  have hle : tauG γ w + (n : ℝ)⁻¹ ≤ 2 * (Real.exp (γ * b))⁻¹ := by linarith
  have h2 : (2 * (Real.exp (γ * b))⁻¹)⁻¹ ≤ (tauG γ w + (n : ℝ)⁻¹)⁻¹ := inv_anti₀ hsum hle
  have e : (2 * (Real.exp (γ * b))⁻¹)⁻¹ = Real.exp (γ * b) / 2 := by
    field_simp
  rwa [e] at h2

/-- **Finite propagation speed, unit speed in `ψ = log X₀`.** -/
theorem finite_speed {a b r : ℝ} (hr : |r| < b - a) (f : L2H') (hf : ∀ᵐ z : UpperHalfPlane, f z ≠ 0 → psiF (z : ℂ) ≤ a) :
    ∀ᵐ z : UpperHalfPlane, b ≤ psiF (z : ℂ) → cosDOp r f z = 0 := by
  set v := cosDOp r f with hv
  set S : Set UpperHalfPlane := {z | b ≤ psiF (z : ℂ)} with hS
  have hSm : MeasurableSet S := measurableSet_le measurable_const measurable_psi_coe
  set I : ℝ := ∫ z in S, ‖v z‖ ^ 2 with hI
  have hI0 : 0 ≤ I := setIntegral_nonneg hSm fun _ _ => by positivity
  have hmain : ∀ γ : ℝ, 0 ≤ γ → I ≤ 4 * Real.exp |r| * ‖f‖ ^ 2 * Real.exp (-(2 * (b - a - |r|)) * γ) := fun γ hγ => by
    obtain ⟨n, hn1⟩ := exists_nat_ge (Real.exp (γ * b))
    have hn : 0 < n + 1 := Nat.succ_pos n
    have hnb : Real.exp (γ * b) ≤ ((n + 1 : ℕ) : ℝ) := by push_cast; linarith
    obtain ⟨C, hW⟩ := waveS_Wn hγ (n + 1) hn
    set N := n + 1 with hN
    have h1 := wave_weightD hW r f
    have h2 : ‖mulCL hW.sb f‖ ≤ Real.exp (γ * a) * ‖f‖ := by
      refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
      filter_upwards [coe_mulCL hW.sb f, hf] with z e1 e2
      rw [e1, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hW.pos z z.im_pos)]
      by_cases h0 : f z = 0
      · simp [h0]
      · exact mul_le_mul_of_nonneg_right (Wn_le_of_psi hγ N hn z.im_pos (e2 h0)) (norm_nonneg _)
    have hE := Real.exp_pos (γ * b)
    have h3 : (Real.exp (γ * b) / 2) ^ 2 * I ≤ ‖mulCL hW.sb v‖ ^ 2 := by
      have nW := integrable_norm_sq (mulCL hW.sb v)
      have nv := integrable_norm_sq v
      calc (Real.exp (γ * b) / 2) ^ 2 * I = ∫ z in S, (Real.exp (γ * b) / 2) ^ 2 * ‖v z‖ ^ 2 := by rw [hI, integral_const_mul]
        _ ≤ ∫ z in S, ‖mulCL hW.sb v z‖ ^ 2 := by
          refine setIntegral_mono_on_ae (nv.integrableOn.const_mul _) nW.integrableOn hSm ?_
          filter_upwards [coe_mulCL hW.sb v] with z e1 hz
          rw [e1, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hW.pos z z.im_pos), mul_pow]
          exact mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (by positivity) (Wn_ge_of_psi hγ N hn hnb z.im_pos hz) 2) (by positivity)
        _ ≤ ∫ z, ‖mulCL hW.sb v z‖ ^ 2 := setIntegral_le_integral nW (Eventually.of_forall fun _ => by positivity)
        _ = ‖mulCL hW.sb v‖ ^ 2 := (norm_sq_int _).symm
    have h4 : ‖mulCL hW.sb v‖ ≤ Real.exp ((γ + 1 / 2) * |r|) * (Real.exp (γ * a) * ‖f‖) :=
      h1.trans (mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le)
    have h5 : (Real.exp (γ * b) / 2) ^ 2 * I ≤ (Real.exp ((γ + 1 / 2) * |r|) * (Real.exp (γ * a) * ‖f‖)) ^ 2 :=
      h3.trans (pow_le_pow_left₀ (norm_nonneg _) h4 2)
    have hpos : 0 < (Real.exp (γ * b) / 2) ^ 2 := by positivity
    have e : (Real.exp ((γ + 1 / 2) * |r|) * (Real.exp (γ * a) * ‖f‖)) ^ 2
        = (Real.exp (γ * b) / 2) ^ 2 * (4 * Real.exp |r| * ‖f‖ ^ 2 * Real.exp (-(2 * (b - a - |r|)) * γ)) := by
      have ex : Real.exp ((γ + 1 / 2) * |r|) ^ 2 * Real.exp (γ * a) ^ 2
          = Real.exp (γ * b) ^ 2 * (Real.exp |r| * Real.exp (-(2 * (b - a - |r|)) * γ)) := by
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
        push_cast
        ring
      calc _ = (Real.exp ((γ + 1 / 2) * |r|) ^ 2 * Real.exp (γ * a) ^ 2) * ‖f‖ ^ 2 := by ring
        _ = _ := by rw [ex]; ring
    rw [e] at h5
    exact le_of_mul_le_mul_left h5 hpos
  have hδ : 0 < b - a - |r| := by linarith
  have hlim : Tendsto (fun γ : ℝ => 4 * Real.exp |r| * ‖f‖ ^ 2 * Real.exp (-(2 * (b - a - |r|)) * γ)) atTop (𝓝 (4 * Real.exp |r| * ‖f‖ ^ 2 * 0)) := by
    refine Tendsto.const_mul _ (Real.tendsto_exp_atBot.comp ?_)
    exact tendsto_id.const_mul_atTop_of_neg (by linarith)
  have hI00 : I ≤ 0 := by
    rw [mul_zero] at hlim
    exact ge_of_tendsto hlim ((eventually_ge_atTop 0).mono hmain)
  have hzero : I = 0 := le_antisymm hI00 hI0
  have hint := (integrable_norm_sq v).integrableOn (s := S)
  have hae := (setIntegral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall fun z => by positivity) hint).1 hzero
  rw [EventuallyEq, ae_restrict_iff' hSm] at hae
  filter_upwards [hae] with z hz hb
  have := hz hb
  simpa using this

lemma cosDOp_adjoint (r : ℝ) (x y : L2H') : ⟪cosDOp r x, y⟫_ℂ = ⟪x, cosDOp r y⟫_ℂ := by
  have h : ContinuousLinearMap.adjoint (cosDOp r) = cosDOp r := by
    unfold cosDOp
    rw [← ProjectionValuedMeasure.integral_conj _ (cosDSymbol_mem r)]
    congr 1
    funext t
    exact Complex.conj_ofReal _
  have e := ContinuousLinearMap.adjoint_inner_left (cosDOp r) y x
  rwa [h] at e

/-- **Finite speed, in inner-product form, in both directions.** -/
theorem finite_speed_inner {a b r : ℝ} (hr : |r| < b - a) (f h : L2H') (hf : ∀ᵐ z : UpperHalfPlane, f z ≠ 0 → psiF (z : ℂ) ≤ a)
    (hh : ∀ᵐ z : UpperHalfPlane, h z ≠ 0 → b ≤ psiF (z : ℂ)) : ⟪h, cosDOp r f⟫_ℂ = 0 ∧ ⟪f, cosDOp r h⟫_ℂ = 0 := by
  have h0 : ⟪h, cosDOp r f⟫_ℂ = 0 := by
    rw [L2.inner_def]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [finite_speed hr f hf, hh] with z e1 e2
    by_cases hz : h z = 0
    · simp [hz]
    · simp [e1 (e2 hz)]
  refine ⟨h0, ?_⟩
  rw [← cosDOp_adjoint, ← inner_conj_symm, h0, map_zero]

end Qschubert
