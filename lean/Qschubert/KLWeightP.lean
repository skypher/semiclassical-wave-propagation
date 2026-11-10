import Qschubert.KLConnect
import Mathlib.Analysis.PSeries

/-!
# The printed-class periodization weight as a `SurfW`

`ω = X₀^{1/2} (log(2X₀)/log 2)^{c}`, `c > 1/2`: the weight `X₀^{1/2} L^{c}` of `sec_printed.tex` divided by its minimum,
as in `subsec:dd-surf`.

* `perio_weighted_gen`: the Cauchy–Schwarz periodization bound for a general weight;
* `tsum_shell_le`: summing over the shells of the orbit, from `exists_orbit_count`;
* `poincare_omP`: `sup_z Σ_γ ω(γz)^{-2} < ∞`; the shell sum is `Σ (n+1)^{-2c}`, which is where `c > 1/2` is used;
* `surfW_printed`: (W1), (W2) for `ω` (os:p1 at `t = 0`).
-/

namespace Qschubert

open MeasureTheory UpperHalfPlane Filter Topology Metric
open scoped ENNReal Pointwise MatrixGroups

variable (Γ : Subgroup PGL(2, ℝ)) [Countable Γ] [ProperlyDiscontinuousSMul Γ ℍ]

/-- **Periodization by Cauchy–Schwarz**, for a general weight. -/
theorem perio_weighted_gen {W Wi : ℍ → ℝ≥0∞} (hW : Measurable W) (hWi : ∀ z, Wi z * W z = 1) {P : ℝ≥0∞} (hP : P < ⊤)
    (hPz : ∀ z : ℍ, ∑' γ : Γ, Wi (γ • z) ^ 2 ≤ P) {f : ℍ → ℂ} (hf : Measurable f)
    (hI : ∫⁻ z, (W z * ‖f z‖ₑ) ^ 2 ≠ ⊤) :
    (∀ᵐ z ∂(volume : Measure ℍ), z ∈ absSet Γ f) ∧ PerioConv Γ f ∧
      ∫⁻ x, ‖perio Γ f x‖ₑ ^ 2 ∂surfMeasure Γ ≤ P * ∫⁻ z, (W z * ‖f z‖ₑ) ^ 2 := by
  set H : ℍ → ℝ≥0∞ := fun z => (W z * ‖f z‖ₑ) ^ 2 with hH_def
  have hH : Measurable H := (hW.mul hf.enorm).pow_const 2
  set G : ℍ → ℝ≥0∞ := fun z => ∑' γ : Γ, H (γ • z) with hG_def
  have hHγ : ∀ γ : Γ, Measurable fun z : ℍ => H (γ • z) := fun γ => hH.comp (measurable_const_smul γ)
  have hGm : Measurable G := Measurable.ennreal_tsum hHγ
  have hF := isFundamentalDomain_fdSet Γ
  have hunf : ∫⁻ z in fdSet Γ, G z = ∫⁻ z, H z := by
    rw [hF.lintegral_eq_tsum'' H, lintegral_tsum fun γ => (hHγ γ).aemeasurable]
  have hpt : ∀ z, absSum Γ f z ^ 2 ≤ P * G z := fun z => by
    have h := tsum_mul_sq_le (fun γ : Γ => Wi (γ • z)) (fun γ : Γ => W (γ • z) * ‖f (γ • z)‖ₑ)
    have e : ∀ γ : Γ, Wi (γ • z) * (W (γ • z) * ‖f (γ • z)‖ₑ) = ‖f (γ • z)‖ₑ := fun γ => by
      rw [← mul_assoc, hWi, one_mul]
    simp only [e] at h
    exact h.trans (mul_le_mul' (hPz z) le_rfl)
  have hae : ∀ᵐ z ∂(volume : Measure ℍ), G z < ⊤ := by
    have h1 : ∀ᵐ z ∂((volume : Measure ℍ).restrict (fdSet Γ)), G z < ⊤ :=
      ae_lt_top hGm (by rw [hunf]; exact hI)
    set N : Set ℍ := {z | G z = ⊤} with hN_def
    have hN : MeasurableSet N := hGm (measurableSet_singleton ⊤)
    have hNF : (volume : Measure ℍ) (N ∩ fdSet Γ) = 0 := by
      rw [← Measure.restrict_apply hN]
      refine measure_mono_null (fun z hz => ?_) (ae_iff.1 h1)
      simp only [Set.mem_setOf_eq, hN_def] at hz ⊢
      rw [hz]; exact lt_irrefl _
    have hinv : ∀ g : Γ, g • N = N := fun g => by
      ext z
      rw [Set.mem_smul_set_iff_inv_smul_mem]
      simp only [hN_def, Set.mem_setOf_eq, hG_def, tsum_smul_invariant Γ H]
    have h0 : (volume : Measure ℍ) N = 0 := hF.measure_zero_of_invariant N hinv hNF
    rw [ae_iff]
    refine measure_mono_null (fun z hz => ?_) h0
    simp only [Set.mem_setOf_eq, hN_def] at hz ⊢
    exact top_le_iff.1 (not_lt.1 hz)
  have hS : ∀ᵐ z ∂(volume : Measure ℍ), z ∈ absSet Γ f := by
    filter_upwards [hae] with z hz
    have h2 : absSum Γ f z ^ 2 < ⊤ := (hpt z).trans_lt (ENNReal.mul_lt_top hP hz)
    show absSum Γ f z < ⊤
    by_contra hc
    rw [top_le_iff.1 (not_lt.1 hc)] at h2
    simp at h2
  have hmeas := aestronglyMeasurable_perio Γ hf hS
  have hAH : Measurable (MulAction.automorphize H : Surf Γ → ℝ≥0∞) :=
    measurable_from_quotient.2 hGm
  have hint : ∫⁻ x, ‖perio Γ f x‖ₑ ^ 2 ∂surfMeasure Γ ≤ P * ∫⁻ z, H z := by
    rw [lintegral_eq_lintegral_automorphize Γ hF hH, ← lintegral_const_mul _ hAH]
    refine lintegral_mono fun x => ?_
    induction x using Quotient.inductionOn with | _ z
    exact (pow_le_pow_left₀ zero_le (enorm_perio_le Γ f _) 2).trans (hpt z)
  have hPI : P * ∫⁻ z, H z ≠ ⊤ := ENNReal.mul_ne_top hP.ne hI
  have hsq : ∫⁻ x, ‖perio Γ f x‖ₑ ^ 2 ∂surfMeasure Γ
      ≤ ENNReal.ofReal (Real.sqrt (P * ∫⁻ z, H z).toReal ^ 2) := by
    rw [Real.sq_sqrt ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hPI]; exact hint
  have hnorm := eLpNorm_two_le_of_lintegral_sq_le hmeas (Real.sqrt_nonneg _) hsq
  refine ⟨hS, ⟨?_, lt_of_le_of_lt hnorm ENNReal.ofReal_lt_top⟩, hint⟩
  filter_upwards [hS] with z hz
  have := ENNReal.summable_toReal (f := fun γ : Γ => ‖f (γ • z)‖ₑ) hz.ne
  simpa [enorm_eq_nnnorm] using this

/-- **Summing over the shells of the orbit.** -/
lemma tsum_shell_le (x₀ : ℍ) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ (z : ℍ) (R : ℝ), ({γ : Γ | dist z (γ • x₀) < R}.ncard : ℝ) ≤ K * Real.exp R) (z : ℍ) {φ : Γ → ℝ≥0∞} {a : ℕ → ℝ≥0∞}
    (hφ : ∀ γ : Γ, φ γ ≤ a ⌊dist z (γ • x₀)⌋₊) :
    ∑' γ : Γ, φ γ ≤ ∑' n : ℕ, ENNReal.ofReal (K * Real.exp (n + 1)) * a n := by
  set A : ℕ → Set Γ := fun n => {γ : Γ | dist z (γ • x₀) < n + 1}
  have hpt : ∀ γ : Γ, φ γ ≤ ∑' n : ℕ, (A n).indicator (fun _ => a n) γ := fun γ => by
    refine le_trans ?_ (ENNReal.le_tsum ⌊dist z (γ • x₀)⌋₊)
    rw [Set.indicator_of_mem (show γ ∈ A ⌊dist z (γ • x₀)⌋₊ from Nat.lt_floor_add_one (dist z (γ • x₀)))]
    exact hφ γ
  have hcount : ∀ n : ℕ, ∑' γ : Γ, (A n).indicator (fun _ => a n) γ ≤ ENNReal.ofReal (K * Real.exp (n + 1)) * a n := by
    intro n
    have hfin : (A n).Finite := (finite_near Γ x₀ z (n + 1)).subset fun γ hγ =>
      show dist z (γ • x₀) ≤ n + 1 from le_of_lt hγ
    rw [← tsum_subtype, ENNReal.tsum_set_const, ← hfin.cast_ncard_eq]
    refine mul_le_mul' ?_ le_rfl
    have e1 : ((((A n).ncard : ℕ∞)) : ℝ≥0∞) = ENNReal.ofReal ((A n).ncard : ℝ) := by simp
    rw [e1]
    exact ENNReal.ofReal_le_ofReal (hK z (n + 1))
  calc ∑' γ : Γ, φ γ ≤ ∑' γ : Γ, ∑' n : ℕ, (A n).indicator (fun _ => a n) γ := ENNReal.tsum_le_tsum hpt
    _ = ∑' n : ℕ, ∑' γ : Γ, (A n).indicator (fun _ => a n) γ := ENNReal.tsum_comm
    _ ≤ _ := ENNReal.tsum_le_tsum hcount

/-! ### The weight -/

/-- `log(2 cosh d)/log 2`. -/
noncomputable def ellP (d : ℝ) : ℝ := Real.log (2 * Real.cosh d) / Real.log 2

/-- `cosh(d)^{1/2} (log(2 cosh d)/log 2)^c`. -/
noncomputable def omP (c d : ℝ) : ℝ := Real.cosh d ^ (1 / 2 : ℝ) * ellP d ^ c

lemma log_two_pos' : 0 < Real.log 2 := Real.log_pos (by norm_num)

lemma log_two_le_log (d : ℝ) : Real.log 2 ≤ Real.log (2 * Real.cosh d) :=
  Real.log_le_log (by norm_num) (by nlinarith [Real.one_le_cosh d])

lemma one_le_ellP (d : ℝ) : 1 ≤ ellP d := by
  rw [ellP, one_le_div log_two_pos']; exact log_two_le_log d

lemma continuous_ellP : Continuous ellP :=
  (Continuous.log (continuous_const.mul Real.continuous_cosh)
    (fun d => (mul_pos two_pos (Real.cosh_pos d)).ne')).div_const _

lemma continuous_omP {c : ℝ} (hc : 0 ≤ c) : Continuous (omP c) :=
  (Real.continuous_cosh.rpow_const fun _ => Or.inr (by norm_num)).mul
    (continuous_ellP.rpow_const fun _ => Or.inr hc)

lemma one_le_omP {c : ℝ} (hc : 0 ≤ c) (d : ℝ) : 1 ≤ omP c d := by
  have h1 : 1 ≤ Real.cosh d ^ (1 / 2 : ℝ) := Real.one_le_rpow (Real.one_le_cosh d) (by norm_num)
  have h2 : 1 ≤ ellP d ^ c := Real.one_le_rpow (one_le_ellP d) hc
  rw [omP]; nlinarith

lemma omP_sq (c d : ℝ) : omP c d ^ 2 = Real.cosh d * ellP d ^ (2 * c) := by
  have h1 : (Real.cosh d ^ (1 / 2 : ℝ)) ^ 2 = Real.cosh d := by
    rw [← Real.sqrt_eq_rpow, Real.sq_sqrt (Real.cosh_pos d).le]
  have h2 : (ellP d ^ c) ^ 2 = ellP d ^ (2 * c) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith [one_le_ellP d])]
    congr 1; push_cast; ring
  rw [omP, mul_pow, h1, h2]

lemma exp_le_two_cosh (d : ℝ) : Real.exp d ≤ 2 * Real.cosh d := by
  rw [Real.cosh_eq]; linarith [Real.exp_pos (-d)]

lemma succ_half_le_ellP {d : ℝ} (hd : 0 ≤ d) : ((⌊d⌋₊ : ℝ) + 1) / 2 ≤ ellP d := by
  rcases Nat.eq_zero_or_pos ⌊d⌋₊ with h | h
  · rw [h]; have := one_le_ellP d; push_cast; linarith
  · have hn : (1 : ℝ) ≤ (⌊d⌋₊ : ℝ) := by exact_mod_cast h
    have hfl : (⌊d⌋₊ : ℝ) ≤ d := Nat.floor_le hd
    have hl : d ≤ Real.log (2 * Real.cosh d) := by
      rw [Real.le_log_iff_exp_le (mul_pos two_pos (Real.cosh_pos d))]
      exact exp_le_two_cosh d
    have hlog : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
      linarith
    have hdiv : d ≤ ellP d := by
      rw [ellP, le_div_iff₀ log_two_pos']
      nlinarith [log_two_pos']
    linarith

/-- The lower bound on `ω²` on the shell of `d`. -/
lemma omP_inv_sq_le {c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d) :
    ((omP c d)⁻¹) ^ 2 ≤ 2 * 2 ^ (2 * c) * Real.exp (-(⌊d⌋₊ : ℝ)) * ((((⌊d⌋₊ : ℝ) + 1) ^ (2 * c))⁻¹) := by
  set n : ℝ := (⌊d⌋₊ : ℝ) with hn
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have hom : 0 < omP c d := lt_of_lt_of_le one_pos (one_le_omP hc d)
  have h2c : 0 ≤ 2 * c := by linarith
  have hexp : Real.exp n / 2 ≤ Real.cosh d := by
    have h1 : Real.exp n ≤ Real.exp d := Real.exp_le_exp.2 (Nat.floor_le hd)
    have h2 := exp_le_two_cosh d
    linarith
  have hell : ((n + 1) / 2) ^ (2 * c) ≤ ellP d ^ (2 * c) :=
    Real.rpow_le_rpow (by positivity) (succ_half_le_ellP hd) h2c
  have hlow : Real.exp n / 2 * ((n + 1) / 2) ^ (2 * c) ≤ omP c d ^ 2 := by
    rw [omP_sq]
    exact mul_le_mul hexp hell (by positivity) (Real.cosh_pos d).le
  have hpow : ((n + 1) / 2) ^ (2 * c) = (n + 1) ^ (2 * c) / 2 ^ (2 * c) :=
    Real.div_rpow (by positivity) (by norm_num) _
  have hA : 0 < (n + 1) ^ (2 * c) := by positivity
  have hB : (0 : ℝ) < 2 ^ (2 * c) := by positivity
  have hE := Real.exp_pos n
  rw [inv_pow, Real.exp_neg, ← mul_inv_cancel_right₀ hA.ne' ((omP c d ^ 2)⁻¹)]
  have hmain : (omP c d ^ 2)⁻¹ ≤ 2 * 2 ^ (2 * c) * (Real.exp n)⁻¹ * ((n + 1) ^ (2 * c))⁻¹ := by
    have hpos : 0 < Real.exp n / 2 * ((n + 1) / 2) ^ (2 * c) := by positivity
    refine (inv_anti₀ hpos hlow).trans (le_of_eq ?_)
    rw [hpow]
    field_simp
  rw [mul_inv_cancel_right₀ hA.ne']
  exact hmain

/-- **`sup_z Σ_γ ω(γz)^{-2} < ∞`.** -/
theorem poincare_omP (x₀ : ℍ) {c : ℝ} (hc : 1 / 2 < c) :
    ∃ P : ℝ≥0∞, P < ⊤ ∧ ∀ z : ℍ, ∑' γ : Γ, ENNReal.ofReal ((omP c (dist x₀ (γ • z)))⁻¹) ^ 2 ≤ P := by
  obtain ⟨K, hK0, hK⟩ := exists_orbit_count Γ x₀
  have hc0 : 0 ≤ c := by linarith
  set B : ℝ := 2 * 2 ^ (2 * c) with hB
  have hB0 : 0 ≤ B := by positivity
  have hsum : Summable fun n : ℕ => (((n : ℝ) + 1) ^ (2 * c))⁻¹ := by
    have h := (Real.summable_nat_rpow_inv (p := 2 * c)).2 (by linarith)
    have h2 := (summable_nat_add_iff 1).2 h
    refine h2.congr fun n => ?_
    push_cast
    rfl
  set S : ℝ := ∑' n : ℕ, (((n : ℝ) + 1) ^ (2 * c))⁻¹
  refine ⟨ENNReal.ofReal (K * Real.exp 1 * B * S), ENNReal.ofReal_lt_top, fun z => ?_⟩
  set a : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (B * Real.exp (-(n : ℝ)) * (((n : ℝ) + 1) ^ (2 * c))⁻¹) with ha
  have hre : ∑' γ : Γ, ENNReal.ofReal ((omP c (dist x₀ (γ • z)))⁻¹) ^ 2
      = ∑' γ : Γ, ENNReal.ofReal ((omP c (dist z (γ • x₀)))⁻¹) ^ 2 := by
    rw [← (Equiv.inv Γ).tsum_eq (fun γ : Γ => ENNReal.ofReal ((omP c (dist z (γ • x₀)))⁻¹) ^ 2)]
    congr 1; funext γ
    simp only [Equiv.inv_apply]
    have hd : dist z (γ⁻¹ • x₀) = dist x₀ (γ • z) := by
      rw [← dist_smul γ z (γ⁻¹ • x₀), smul_inv_smul, dist_comm]
    rw [hd]
  rw [hre]
  refine (tsum_shell_le Γ x₀ hK0 hK z (a := a) fun γ => ?_).trans ?_
  · rw [ha]
    dsimp only
    rw [← ENNReal.ofReal_pow (inv_nonneg.2 (lt_of_lt_of_le one_pos (one_le_omP hc0 _)).le)]
    exact ENNReal.ofReal_le_ofReal (omP_inv_sq_le hc0 dist_nonneg)
  · have hterm : ∀ n : ℕ, ENNReal.ofReal (K * Real.exp (n + 1)) * a n
        = ENNReal.ofReal (K * Real.exp 1 * B * (((n : ℝ) + 1) ^ (2 * c))⁻¹) := fun n => by
      rw [ha]
      dsimp only
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      have : Real.exp ((n : ℝ) + 1) * Real.exp (-(n : ℝ)) = Real.exp 1 := by
        rw [← Real.exp_add]; congr 1; ring
      calc K * Real.exp ((n : ℝ) + 1) * (B * Real.exp (-(n : ℝ)) * (((n : ℝ) + 1) ^ (2 * c))⁻¹)
          = K * (Real.exp ((n : ℝ) + 1) * Real.exp (-(n : ℝ))) * B * (((n : ℝ) + 1) ^ (2 * c))⁻¹ := by ring
        _ = _ := by rw [this]
    simp_rw [hterm]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) (hsum.mul_left _), tsum_mul_left]

/-- **The printed-class weight, normalized so that `ω ≥ 1`, satisfies (W1), (W2).** -/
noncomputable def surfW_printed (x₀ : ℍ) {c : ℝ} (hc : 1 / 2 < c) : SurfW Γ where
  ω z := omP c (dist x₀ z)
  meas := ((continuous_omP (by linarith)).comp (continuous_const.dist continuous_id)).measurable
  cont := (continuous_omP (by linarith)).comp (continuous_const.dist continuous_id)
  one_le z := one_le_omP (by linarith) _
  locBdd K hK := by
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (f := fun z : ℍ => omP c (dist x₀ z))
      ((continuous_omP (by linarith)).comp (continuous_const.dist continuous_id)).continuousOn
    exact ⟨C, fun z hz => (le_abs_self _).trans (hC z hz)⟩
  C := ⨆ z : ℍ, ∑' γ : Γ, ENNReal.ofReal ((omP c (dist x₀ (γ • z)))⁻¹) ^ 2
  C_lt := by
    obtain ⟨P, hP, h⟩ := poincare_omP Γ x₀ hc
    exact lt_of_le_of_lt (iSup_le h) hP
  perio_bd f hf hI := by
    have hc0 : 0 ≤ c := by linarith
    have hm : Measurable fun z : ℍ => ENNReal.ofReal (omP c (dist x₀ z)) :=
      ENNReal.measurable_ofReal.comp ((continuous_omP hc0).comp (continuous_const.dist continuous_id)).measurable
    exact perio_weighted_gen Γ (Wi := fun z => ENNReal.ofReal ((omP c (dist x₀ z))⁻¹)) hm
      (fun z => by
        have hp : 0 < omP c (dist x₀ z) := lt_of_lt_of_le one_pos (one_le_omP hc0 _)
        rw [← ENNReal.ofReal_mul (inv_pos.2 hp).le, inv_mul_cancel₀ hp.ne', ENNReal.ofReal_one])
      (by
        obtain ⟨P, hP, h⟩ := poincare_omP Γ x₀ hc
        exact lt_of_le_of_lt (iSup_le h) hP)
      (fun z => le_iSup (fun z : ℍ => ∑' γ : Γ, ENNReal.ofReal ((omP c (dist x₀ (γ • z)))⁻¹) ^ 2) z) hf hI
  dil T := by
    have hc0 : 0 ≤ c := by linarith
    refine ⟨Real.exp (|T| / 2) * (1 + |T| / Real.log 2) ^ c, by positivity, fun s hs z => ?_⟩
    have hsT : |s| ≤ |T| := hs.trans (le_abs_self T)
    set d := dist x₀ z
    set d' := dist x₀ (dilate s z)
    have hA : Real.cosh d ≤ Real.exp |s| * Real.cosh d' := by
      have h := coshD_le_exp_mul x₀ z (dilate s z)
      rwa [dist_dilate] at h
    have hcp := Real.cosh_pos d
    have hcp' := Real.cosh_pos d'
    have h1 : Real.cosh d ^ (1 / 2 : ℝ) ≤ Real.exp (|T| / 2) * Real.cosh d' ^ (1 / 2 : ℝ) := by
      calc Real.cosh d ^ (1 / 2 : ℝ) ≤ (Real.exp |s| * Real.cosh d') ^ (1 / 2 : ℝ) :=
            Real.rpow_le_rpow hcp.le hA (by norm_num)
        _ = Real.exp (|s| / 2) * Real.cosh d' ^ (1 / 2 : ℝ) := by
            rw [Real.mul_rpow (Real.exp_pos _).le hcp'.le, ← Real.exp_mul]; congr 2; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by linarith)) (by positivity)
    have hl2 := log_two_pos'
    have hE' := one_le_ellP d'
    have hE := one_le_ellP d
    have hlog : Real.log (2 * Real.cosh d) ≤ |s| + Real.log (2 * Real.cosh d') := by
      calc Real.log (2 * Real.cosh d) ≤ Real.log (Real.exp |s| * (2 * Real.cosh d')) :=
            Real.log_le_log (by positivity) (by nlinarith [Real.exp_pos |s|])
        _ = _ := by rw [Real.log_mul (Real.exp_pos _).ne' (by positivity), Real.log_exp]
    have h2 : ellP d ≤ (1 + |T| / Real.log 2) * ellP d' := by
      have e : ellP d ≤ |s| / Real.log 2 + ellP d' := by
        rw [ellP, ellP, ← add_div]
        exact div_le_div_of_nonneg_right hlog hl2.le
      have e2 : |s| / Real.log 2 ≤ |T| / Real.log 2 := div_le_div_of_nonneg_right hsT hl2.le
      have e3 : 0 ≤ |T| / Real.log 2 := by positivity
      nlinarith
    have h3 : ellP d ^ c ≤ (1 + |T| / Real.log 2) ^ c * ellP d' ^ c := by
      rw [← Real.mul_rpow (by positivity) (by linarith)]
      exact Real.rpow_le_rpow (by linarith) h2 hc0
    show Real.cosh d ^ (1 / 2 : ℝ) * ellP d ^ c
      ≤ Real.exp (|T| / 2) * (1 + |T| / Real.log 2) ^ c * (Real.cosh d' ^ (1 / 2 : ℝ) * ellP d' ^ c)
    calc Real.cosh d ^ (1 / 2 : ℝ) * ellP d ^ c
        ≤ (Real.exp (|T| / 2) * Real.cosh d' ^ (1 / 2 : ℝ)) * ((1 + |T| / Real.log 2) ^ c * ellP d' ^ c) :=
          mul_le_mul h1 h3 (by positivity) (by positivity)
      _ = _ := by ring

end Qschubert
