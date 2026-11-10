import Qschubert.KLPcCWa

/-!
# The wave group paired with an eigenfunction of the Laplacian

Stage Z of the plan for Proposition `ev:mod` (`lean/BLUEPRINT.md`). Let `F` be a test function with `ΔF = μ F` on the
set `{ψ < b}` (`ψ = log cosh d(i, ·)`), and let `f ∈ L²(ℍ)` vanish outside `{ψ ≤ a}`. Then, for `|r| < b - a`,

`⟪F, cos(r √(-Δ - 1/4)) f⟫ = cosh(k r) ⟪F, f⟫`, where `k² = conj μ + 1/4` (`pair_cosD_cosh`).

For `F = θ y^v` with a cutoff `θ` this is the statement that the zero Fourier mode of the wave group is given by the
one-dimensional wave equation in `log y`.

Proof. With `Ψ₁ = (-Δ - 1/4) F` (`shiftLap`):
* `⟪F, cos(rD) f⟫ = ⟪F, f⟫ - ∫_0^r ∫_0^s ⟪Ψ₁, cos(σD) f⟫ dσ ds` (`pair_cosD_eq`), from the spectrally truncated wave
  group, where the two derivatives exist in operator norm, and dominated convergence;
* by finite propagation speed, `⟪Ψ₁, cos(σD) f⟫ = -(conj μ + 1/4) ⟪F, cos(σD) f⟫` for `|σ| < b - a`
  (`pair_shiftLap_cosD`);
* so `m(r) = ⟪F, cos(rD) f⟫` and `p(r) = ∫_0^r m` satisfy `m' = k² p`, `p' = m` on `(-(b-a), b-a)`, and
  `(m ± k p) e^{∓kr}` is constant.
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set Physicslib4.Spectral Physicslib4.Spectral.Unbounded
open scoped ENNReal InnerProductSpace ComplexConjugate UpperHalfPlane

local notation "L2H'" => Lp ℂ 2 (volume : Measure UpperHalfPlane)

/-- `(-Δ - 1/4) F` for a test function `F`, as an `L²` class. -/
noncomputable def shiftLap (F : testFn) : L2H' := -toL2 (lapTest F) - (1 / 4 : ℂ) • toL2 F

lemma cosDOp_zero : cosDOp 0 = 1 := by
  unfold cosDOp
  have e : (fun x : ℝ => ((Real.cos (0 * √(yD x)) : ℝ) : ℂ)) = (1 : ℝ → ℂ) := by
    funext x; simp
  rw [e, specE.integral_one]

lemma norm_cosDOp_apply_le (r : ℝ) (f : L2H') : ‖cosDOp r f‖ ≤ ‖f‖ :=
  le_of_tendsto' (tendsto_chiCD r f).norm fun n => norm_chiCD_le n r f

lemma continuous_chiCD_J (n : ℝ) : Continuous fun r => (chiCD n r).J :=
  continuous_iff_continuousAt.2 fun s => (hasDerivAt_C_J' n s).continuousAt

lemma continuous_chiDD_J (n : ℝ) : Continuous fun r => (chiDD n r).J :=
  continuous_iff_continuousAt.2 fun s => (hasDerivAt_D_J' n s).continuousAt

lemma measurable_inner_cosDOp (Φ f : L2H') : Measurable fun σ : ℝ => ⟪Φ, cosDOp σ f⟫_ℂ := by
  refine measurable_of_tendsto_metrizable (f := fun (n : ℕ) (σ : ℝ) => ⟪Φ, (chiCD n σ).J f⟫_ℂ) (fun n => ?_) ?_
  · exact (continuous_const.inner ((continuous_chiCD_J n).clm_apply continuous_const)).measurable
  · rw [tendsto_pi_nhds]
    exact fun σ => tendsto_const_nhds.inner (tendsto_chiCD σ f)

lemma norm_inner_cosDOp_le (Φ f : L2H') (σ : ℝ) : ‖⟪Φ, cosDOp σ f⟫_ℂ‖ ≤ ‖Φ‖ * ‖f‖ :=
  (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (norm_cosDOp_apply_le σ f) (norm_nonneg _))

lemma chiDD_zero_J (n : ℝ) : (chiDD n 0).J = 0 := by
  have e1 : (chiDD n 0).g = (0 : ℂ) • (1 : ℝ → ℂ) := by
    funext x; simp [Cutoff.g, chiDD, dD, sincS]
  have h1m : (1 : ℝ → ℂ) ∈ BddMeasurable ℝ := ⟨measurable_one, 1, fun _ => by simp⟩
  show specE.integral _ = 0
  rw [e1, specE.integral_smul _ h1m, zero_smul]

/-- `⟪F, (s r)(-Δ) u⟫ = ⟪-ΔF, r(-Δ) u⟫`. -/
lemma inner_toL2_JS (F : testFn) (χ : Cutoff) (u : L2H') :
    ⟪toL2 F, χ.JS u⟫_ℂ = ⟪-toL2 (lapTest F), χ.J u⟫_ℂ := by
  rw [← χ.negLapH_J u, ← negLapH_toL2 F (toL2_mem_negLapH_domain F)]
  exact negLapH_isPositive.1 ⟨toL2 F, toL2_mem_negLapH_domain F⟩ ⟨χ.J u, χ.J_mem u⟩

lemma hasDerivAt_pair_chiCD (F : testFn) (f : L2H') (n s : ℝ) :
    HasDerivAt (fun r => ⟪toL2 F, (chiCD n r).J f⟫_ℂ) (-⟪shiftLap F, (chiDD n s).J f⟫_ℂ) s := by
  have h1 : HasDerivAt (fun r => (chiCD n r).J f) ((-(chiDD n s).JS + (1 / 4 : ℂ) • (chiDD n s).J) f) s := by
    have h : HasDerivAt (fun r => (chiCD n r).J f) _ s := hasDerivAt_clm_apply_C (hasDerivAt_C_J' n s) (hasDerivAt_const s f)
    convert h using 1
    simp
  have h2 := (hasDerivAt_const s (toL2 F)).inner ℂ h1
  convert h2 using 1
  rw [inner_zero_left, add_zero, add_apply, neg_apply, smul_apply, inner_add_right, inner_neg_right, inner_smul_right,
    inner_toL2_JS, shiftLap, inner_sub_left, inner_neg_left, inner_smul_left]
  simp
  rw [Complex.conj_ofNat]
  ring

lemma hasDerivAt_pair_chiDD (Φ f : L2H') (n s : ℝ) :
    HasDerivAt (fun r => ⟪Φ, (chiDD n r).J f⟫_ℂ) ⟪Φ, (chiCD n s).J f⟫_ℂ s := by
  have h1 : HasDerivAt (fun r => (chiDD n r).J f) ((chiCD n s).J f) s := by
    have h : HasDerivAt (fun r => (chiDD n r).J f) _ s := hasDerivAt_clm_apply_C (hasDerivAt_D_J' n s) (hasDerivAt_const s f)
    convert h using 1
    simp
  simpa using (hasDerivAt_const s Φ).inner ℂ h1

/-- The integrated wave equation for the truncated wave group. -/
lemma pair_chiCD_eq (F : testFn) (f : L2H') (n r : ℝ) :
    ⟪toL2 F, (chiCD n r).J f⟫_ℂ = ⟪toL2 F, (chiCD n 0).J f⟫_ℂ
      - ∫ s in (0 : ℝ)..r, ∫ σ in (0 : ℝ)..s, ⟪shiftLap F, (chiCD n σ).J f⟫_ℂ := by
  have hce : Continuous fun σ => ⟪shiftLap F, (chiCD n σ).J f⟫_ℂ :=
    continuous_const.inner ((continuous_chiCD_J n).clm_apply continuous_const)
  have hcd : Continuous fun s => ⟪shiftLap F, (chiDD n s).J f⟫_ℂ :=
    continuous_const.inner ((continuous_chiDD_J n).clm_apply continuous_const)
  have hinner : ∀ s : ℝ, ∫ σ in (0 : ℝ)..s, ⟪shiftLap F, (chiCD n σ).J f⟫_ℂ = ⟪shiftLap F, (chiDD n s).J f⟫_ℂ := by
    intro s
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_pair_chiDD (shiftLap F) f n x)
      (hce.intervalIntegrable _ _), chiDD_zero_J]
    simp
  simp_rw [hinner]
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := r)
    (fun x _ => hasDerivAt_pair_chiCD F f n x) (hcd.neg.intervalIntegrable _ _)
  rw [intervalIntegral.integral_neg] at h
  linear_combination (-1 : ℂ) * h

/-- **The integrated wave equation**: `⟪F, cos(rD) f⟫ = ⟪F, f⟫ - ∫_0^r ∫_0^s ⟪(-Δ - 1/4)F, cos(σD) f⟫ dσ ds`. -/
theorem pair_cosD_eq (F : testFn) (f : L2H') (r : ℝ) :
    ⟪toL2 F, cosDOp r f⟫_ℂ = ⟪toL2 F, f⟫_ℂ
      - ∫ s in (0 : ℝ)..r, ∫ σ in (0 : ℝ)..s, ⟪shiftLap F, cosDOp σ f⟫_ℂ := by
  set C : ℝ := ‖shiftLap F‖ * ‖f‖ with hC
  have hl1 : Tendsto (fun n : ℕ => ⟪toL2 F, (chiCD n r).J f⟫_ℂ) atTop (𝓝 ⟪toL2 F, cosDOp r f⟫_ℂ) :=
    tendsto_const_nhds.inner (tendsto_chiCD r f)
  have hl0 : Tendsto (fun n : ℕ => ⟪toL2 F, (chiCD n 0).J f⟫_ℂ) atTop (𝓝 ⟪toL2 F, f⟫_ℂ) := by
    have h : Tendsto (fun n : ℕ => ⟪toL2 F, (chiCD n 0).J f⟫_ℂ) atTop (𝓝 ⟪toL2 F, cosDOp 0 f⟫_ℂ) :=
      tendsto_const_nhds.inner (tendsto_chiCD 0 f)
    rwa [cosDOp_zero, one_apply_eq_self] at h
  have hce : ∀ n : ℕ, Continuous fun σ => ⟪shiftLap F, (chiCD n σ).J f⟫_ℂ := fun n =>
    continuous_const.inner ((continuous_chiCD_J n).clm_apply continuous_const)
  have hbd : ∀ (n : ℕ) (σ : ℝ), ‖⟪shiftLap F, (chiCD n σ).J f⟫_ℂ‖ ≤ C := fun n σ =>
    (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (norm_chiCD_le n σ f) (norm_nonneg _))
  have hinner : ∀ s : ℝ, Tendsto (fun n : ℕ => ∫ σ in (0 : ℝ)..s, ⟪shiftLap F, (chiCD n σ).J f⟫_ℂ) atTop
      (𝓝 (∫ σ in (0 : ℝ)..s, ⟪shiftLap F, cosDOp σ f⟫_ℂ)) := fun s =>
    intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => C)
      (Eventually.of_forall fun n => (hce n).aestronglyMeasurable)
      (Eventually.of_forall fun n => Eventually.of_forall fun σ _ => hbd n σ)
      intervalIntegrable_const
      (Eventually.of_forall fun σ _ => tendsto_const_nhds.inner (tendsto_chiCD σ f))
  have houter : Tendsto (fun n : ℕ => ∫ s in (0 : ℝ)..r, ∫ σ in (0 : ℝ)..s, ⟪shiftLap F, (chiCD n σ).J f⟫_ℂ) atTop
      (𝓝 (∫ s in (0 : ℝ)..r, ∫ σ in (0 : ℝ)..s, ⟪shiftLap F, cosDOp σ f⟫_ℂ)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun s => C * |s - 0|)
      (Eventually.of_forall fun n => ?_) (Eventually.of_forall fun n => Eventually.of_forall fun s _ => ?_)
      ?_ (Eventually.of_forall fun s _ => hinner s)
    · exact (intervalIntegral.continuous_primitive (fun a b => (hce n).intervalIntegrable a b) 0).aestronglyMeasurable
    · exact intervalIntegral.norm_integral_le_of_norm_le_const fun σ _ => hbd n σ
    · exact (continuous_const.mul (continuous_abs.comp (continuous_id.sub continuous_const))).intervalIntegrable _ _
  exact tendsto_nhds_unique hl1 ((hl0.sub houter).congr fun n => (pair_chiCD_eq F f n r).symm)

lemma intervalIntegrable_inner_cosDOp (Φ f : L2H') (a b : ℝ) :
    IntervalIntegrable (fun σ => ⟪Φ, cosDOp σ f⟫_ℂ) volume a b :=
  (intervalIntegrable_const (c := ‖Φ‖ * ‖f‖)).mono_fun' (measurable_inner_cosDOp Φ f).aestronglyMeasurable
    (Eventually.of_forall fun σ => norm_inner_cosDOp_le Φ f σ)

/-- `r ↦ ⟪F, cos(rD) f⟫` is differentiable, with derivative `-∫_0^r ⟪(-Δ - 1/4)F, cos(σD) f⟫ dσ`. -/
theorem hasDerivAt_pair_cosD (F : testFn) (f : L2H') (r : ℝ) :
    HasDerivAt (fun r => ⟪toL2 F, cosDOp r f⟫_ℂ) (-∫ σ in (0 : ℝ)..r, ⟪shiftLap F, cosDOp σ f⟫_ℂ) r := by
  have hQ : Continuous fun s => ∫ σ in (0 : ℝ)..s, ⟪shiftLap F, cosDOp σ f⟫_ℂ :=
    intervalIntegral.continuous_primitive (intervalIntegrable_inner_cosDOp _ _) 0
  have h := intervalIntegral.integral_hasDerivAt_right (hQ.intervalIntegrable 0 r)
    (hQ.stronglyMeasurableAtFilter _ _) hQ.continuousAt
  have e : (fun r => ⟪toL2 F, cosDOp r f⟫_ℂ)
      = fun r => ⟪toL2 F, f⟫_ℂ - ∫ s in (0 : ℝ)..r, ∫ σ in (0 : ℝ)..s, ⟪shiftLap F, cosDOp σ f⟫_ℂ :=
    funext fun r => pair_cosD_eq F f r
  rw [e]
  exact ((hasDerivAt_const r _).sub h).congr_deriv (by simp)

lemma shiftLap_ae (F : testFn) :
    ⇑(shiftLap F) =ᵐ[volume] fun z : UpperHalfPlane => -lapTestFun F z - (1 / 4 : ℂ) * (F : ℂ → ℂ) z := by
  have h1 := toL2_ae (lapTest F)
  have h2 := toL2_ae F
  have h3 := Lp.coeFn_sub (-toL2 (lapTest F)) ((1 / 4 : ℂ) • toL2 F)
  have h4 := Lp.coeFn_neg (toL2 (lapTest F))
  have h5 := Lp.coeFn_smul (1 / 4 : ℂ) (toL2 F)
  filter_upwards [h1, h2, h3, h4, h5] with z e1 e2 e3 e4 e5
  rw [shiftLap, e3, Pi.sub_apply, e4, Pi.neg_apply, e5, Pi.smul_apply, e1, e2, smul_eq_mul]
  rfl

/-- By finite propagation speed, `(-Δ - 1/4)F` may be replaced by `-(μ + 1/4) F` in the pairing. -/
theorem pair_shiftLap_cosD {F : testFn} {f : L2H'} {a b : ℝ} {μ : ℂ}
    (hf : ∀ᵐ z : UpperHalfPlane, f z ≠ 0 → psiF (z : ℂ) ≤ a)
    (hF : ∀ z : UpperHalfPlane, psiF (z : ℂ) < b → lapTestFun F z = μ * (F : ℂ → ℂ) z) {σ : ℝ} (hσ : |σ| < b - a) :
    ⟪shiftLap F, cosDOp σ f⟫_ℂ = -(conj μ + 1 / 4) * ⟪toL2 F, cosDOp σ f⟫_ℂ := by
  set b' := (|σ| + a + b) / 2 with hb'
  have h1 : |σ| < b' - a := by rw [hb']; linarith
  have h2 : b' < b := by rw [hb']; linarith
  have hfs := finite_speed h1 f hf
  rw [L2.inner_def, L2.inner_def, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [hfs, shiftLap_ae F, toL2_ae F] with z e1 e2 e3
  by_cases hz : b' ≤ psiF (z : ℂ)
  · rw [e1 hz]; simp
  · rw [e2, e3, hF z (lt_trans (not_le.mp hz) h2)]
    simp only [RCLike.inner_apply, map_sub, map_neg, map_mul, map_div₀, map_one, Complex.conj_ofNat]
    ring

/-- **The wave group paired with an eigenfunction.** -/
theorem pair_cosD_cosh {F : testFn} {f : L2H'} {a b : ℝ} {μ k : ℂ}
    (hf : ∀ᵐ z : UpperHalfPlane, f z ≠ 0 → psiF (z : ℂ) ≤ a)
    (hF : ∀ z : UpperHalfPlane, psiF (z : ℂ) < b → lapTestFun F z = μ * (F : ℂ → ℂ) z)
    (hk : k ^ 2 = conj μ + 1 / 4) {r : ℝ} (hr : |r| < b - a) :
    ⟪toL2 F, cosDOp r f⟫_ℂ = Complex.cosh (k * r) * ⟪toL2 F, f⟫_ℂ := by
  set ρ := b - a with hρ
  set m : ℝ → ℂ := fun r => ⟪toL2 F, cosDOp r f⟫_ℂ with hm
  set q : ℝ → ℂ := fun σ => ⟪shiftLap F, cosDOp σ f⟫_ℂ with hq
  have hm' : ∀ r, HasDerivAt m (-∫ σ in (0 : ℝ)..r, q σ) r := fun r => hasDerivAt_pair_cosD F f r
  have hmc : Continuous m := continuous_iff_continuousAt.2 fun r => (hm' r).continuousAt
  set p : ℝ → ℂ := fun r => ∫ σ in (0 : ℝ)..r, m σ with hp
  have hp' : ∀ r, HasDerivAt p (m r) r := fun r =>
    intervalIntegral.integral_hasDerivAt_right (hmc.intervalIntegrable _ _) (hmc.stronglyMeasurableAtFilter _ _)
      hmc.continuousAt
  have hqm : ∀ σ, |σ| < ρ → q σ = -(k ^ 2) * m σ := fun σ hσ => by
    rw [hk]; exact pair_shiftLap_cosD hf hF hσ
  have hQ : ∀ r, |r| < ρ → -∫ σ in (0 : ℝ)..r, q σ = k ^ 2 * p r := fun r hr => by
    have e : ∫ σ in (0 : ℝ)..r, q σ = ∫ σ in (0 : ℝ)..r, -(k ^ 2) * m σ := by
      refine intervalIntegral.integral_congr fun σ hσ => hqm σ ?_
      rcases Set.mem_uIcc.1 hσ with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [abs_of_nonneg h1]; exact lt_of_le_of_lt (h2.trans (le_abs_self r)) hr
      · rw [abs_of_nonpos h2]; exact lt_of_le_of_lt (by linarith [neg_abs_le r]) hr
    rw [e, intervalIntegral.integral_const_mul]
    ring
  have hm0 : m 0 = ⟪toL2 F, f⟫_ℂ := by simp [hm, cosDOp_zero]
  have hp0 : p 0 = 0 := by simp [hp]
  have key : ∀ ε : ℂ, ε ^ 2 = 1 → (m r + ε * k * p r) * Complex.exp (-(ε * k * r)) = m 0 := by
    intro ε hε
    set E : ℝ → ℂ := fun r => (m r + ε * k * p r) * Complex.exp (-(ε * k * r)) with hE
    have hE' : ∀ x ∈ Ioo (-ρ) ρ, HasDerivAt E 0 x := by
      intro x hx
      have hxρ : |x| < ρ := abs_lt.mpr hx
      have h1 : HasDerivAt (fun r => m r + ε * k * p r) (k ^ 2 * p x + ε * k * m x) x := by
        have := (hm' x).add ((hp' x).const_mul (ε * k))
        rwa [hQ x hxρ] at this
      have h3 : HasDerivAt (fun r : ℝ => -(ε * k * (r : ℂ))) (-(ε * k)) x := by
        have h4 : HasDerivAt (fun r : ℝ => (r : ℂ)) 1 x := (hasDerivAt_id x).ofReal_comp
        have h5 := (h4.const_mul (ε * k)).neg
        rw [mul_one] at h5
        exact h5
      have h2 : HasDerivAt (fun r : ℝ => Complex.exp (-(ε * k * r))) (Complex.exp (-(ε * k * x)) * (-(ε * k))) x :=
        h3.cexp
      have h := h1.mul h2
      convert h using 1
      have e2 : ε * k * (ε * k) = k ^ 2 := by
        rw [show ε * k * (ε * k) = ε ^ 2 * k ^ 2 by ring, hε, one_mul]
      linear_combination (p x * Complex.exp (-(ε * k * x))) * e2
    have hconst := IsOpen.is_const_of_deriv_eq_zero isOpen_Ioo isPreconnected_Ioo
      (fun x hx => (hE' x hx).differentiableAt.differentiableWithinAt) (fun x hx => (hE' x hx).deriv)
      (x := r) (y := 0) (abs_lt.mp hr) (by constructor <;> linarith [abs_nonneg r])
    have e0 : E 0 = m 0 := by simp [hE, hp0]
    rw [← e0, ← hconst]
  have h1 := key 1 (by norm_num)
  have h2 := key (-1) (by norm_num)
  simp only [one_mul, neg_mul, neg_neg] at h1 h2
  have e1 : Complex.exp (-(k * r)) * Complex.exp (k * r) = 1 := by
    rw [← Complex.exp_add]; simp
  show m r = Complex.cosh (k * r) * ⟪toL2 F, f⟫_ℂ
  rw [← hm0, Complex.cosh]
  linear_combination (Complex.exp (k * r) / 2) * h1 + (Complex.exp (-(k * r)) / 2) * h2 - m r * e1

end Qschubert
