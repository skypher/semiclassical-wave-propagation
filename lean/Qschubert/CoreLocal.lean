import Qschubert.Mollify

/-!
# The local step of the core dictionary: `χu ∈ Dom(Ā)`

For a real test function `χ`, a test function `θ` equal to `1` near every point of `tsupport χ`,
and `u ∈ Dom(-Δ)` (the Friedrichs domain), with `tsupport χ ⊆ {y₀ ≤ y ≤ Y₁}`, `y₀ > 0`:

* `integral_lapE_smul_eucFun` (the localization pairing for a general pair `(χ, θ)`): for smooth
  `φ`, `∫ Δ_Eφ · χu = -∫ φ (χ/y²)(-Δu) + 2∫ φ ((Xχ)/y²) Xu + 2∫ φ ((Yχ)/y²) Yu + ∫ φ ((Δχ)/y²) u`;
* `lapE_molF_eucFun`: hence `Δ_E((χu) ⋆ φ_n) = -(χ(-Δu)/y²) ⋆ φ_n + 2((Xχ)Xu/y²) ⋆ φ_n
  + 2((Yχ)Yu/y²) ⋆ φ_n + ((Δχ)u/y²) ⋆ φ_n` pointwise;
* `isTestFn_molF`: `(cw) ⋆ φ_n` is a test function once `1/(n+1) < y₀`;
* `tendsto_molF_H`: `m · ((cw) ⋆ φ_n) → m · cw` in `L²(ℍ)` for smooth `m`
  (from `tendsto_molF` and the transfer `eLpNorm_H_le` on supports in `{y ≥ y₀/2}`);
* `mem_graphBar_local`: `(χu, χ(-Δu) - 2(Xχ)Xu - 2(Yχ)Yu - (Δχ)u) ∈ graphBar`.
-/

namespace Qschubert

open MeasureTheory UpperHalfPlane Filter Topology Metric Set
open scoped ContDiff ComplexConjugate ENNReal Convolution Pointwise

local notation "L2H" => Lp ℂ 2 (volume : Measure ℍ)

/-! ### The localization pairing for a general `(χ, θ)` -/

/-- `θφ` as a test function. -/
noncomputable def thetaPhiG (θ : testFn) (φ : ℂ → ℂ) (hφ : ContDiff ℝ ∞ φ) : testFn := smulTF φ hφ θ

lemma mulT_conj_thetaPhiG {θ c : testFn} (hc : IsRealT c)
    (hsupp : ∀ ζ, (c : ℂ → ℂ) ζ ≠ 0 → (θ : ℂ → ℂ) ζ = 1) {φ : ℂ → ℂ} (hφ : ContDiff ℝ ∞ φ) :
    mulT c (conjT (thetaPhiG θ φ hφ))
      = conjT (smulTF (fun ζ => ((ζ.im : ℝ) : ℂ) ^ 2 * φ ζ) (contDiff_imSq.mul hφ) (divIm2 c)) := by
  apply Subtype.ext; funext ζ
  show (c : ℂ → ℂ) ζ * conj (φ ζ * (θ : ℂ → ℂ) ζ)
    = conj (((ζ.im : ℝ) : ℂ) ^ 2 * φ ζ * (invIm ζ * (invIm ζ * (c : ℂ → ℂ) ζ)))
  by_cases h0 : (c : ℂ → ℂ) ζ = 0
  · simp [h0]
  · have hy : 0 < ζ.im := testFn_im_pos h0
    rw [hsupp ζ h0, mul_one]
    have hyc : ((ζ.im : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hy.ne'
    have e : ((ζ.im : ℝ) : ℂ) ^ 2 * φ ζ * (invIm ζ * (invIm ζ * (c : ℂ → ℂ) ζ)) = φ ζ * (c : ℂ → ℂ) ζ := by
      simp only [invIm]; push_cast; field_simp
    rw [e, map_mul, hc]
    ring

lemma conj_lap_chiG {θ χ : testFn} (hχ : IsRealT χ)
    (hθ : ∀ ζ ∈ tsupport (χ : ℂ → ℂ), ∀ᶠ w in 𝓝 ζ, (θ : ℂ → ℂ) w = 1)
    {φ : ℂ → ℂ} (hφ : ContDiff ℝ ∞ φ) :
    conjT (smulTF (fun ζ => ((ζ.im : ℝ) : ℂ) ^ 2 * lapE φ ζ) (contDiff_imSq.mul (contDiff_lapE hφ)) χ)
      = mulT χ (lapTest (conjT (thetaPhiG θ φ hφ))) := by
  rw [lapTest_conjT]
  apply Subtype.ext; funext ζ
  show conj (((ζ.im : ℝ) : ℂ) ^ 2 * lapE φ ζ * (χ : ℂ → ℂ) ζ)
    = (χ : ℂ → ℂ) ζ * conj (((ζ.im : ℝ) : ℂ) ^ 2 * lapE (fun w => φ w * (θ : ℂ → ℂ) w) ζ)
  by_cases h0 : (χ : ℂ → ℂ) ζ = 0
  · simp [h0]
  · have hζ : ζ ∈ tsupport (χ : ℂ → ℂ) := subset_tsupport _ h0
    have hev : (fun w => φ w * (θ : ℂ → ℂ) w) =ᶠ[𝓝 ζ] φ := by
      filter_upwards [hθ ζ hζ] with w hw
      rw [hw, mul_one]
    have hlap : lapE (fun w => φ w * (θ : ℂ → ℂ) w) ζ = lapE φ ζ := by
      simp only [lapE, hev.fderiv.fderiv_eq]
    rw [hlap, map_mul, map_mul, hχ]
    ring

/-- **The localization pairing**, for any real test `χ` and any `θ = 1` near `tsupport χ`. -/
theorem integral_lapE_smul_eucFun {θ χ : testFn} (hχ : IsRealT χ)
    (hθ : ∀ ζ ∈ tsupport (χ : ℂ → ℂ), ∀ᶠ w in 𝓝 ζ, (θ : ℂ → ℂ) w = 1)
    (u : negLapH.domain) {φ : ℂ → ℂ} (hφ : ContDiff ℝ ∞ φ) :
    ∫ ζ, lapE φ ζ • eucFun χ u ζ
      = -(∫ ζ, φ ζ • eucFun (divIm2 χ) (negLapH u) ζ)
        + 2 * (∫ ζ, φ ζ • eucFun (divIm2 (vfTest 1 χ)) (domX u) ζ)
        + 2 * (∫ ζ, φ ζ • eucFun (divIm2 (vfTest Complex.I χ)) (domY u) ζ)
        + (∫ ζ, φ ζ • eucFun (divIm2 (lapTest χ)) u ζ) := by
  have hsupp : ∀ c : testFn, tsupport (c : ℂ → ℂ) ⊆ tsupport (χ : ℂ → ℂ) →
      ∀ ζ, (c : ℂ → ℂ) ζ ≠ 0 → (θ : ℂ → ℂ) ζ = 1 := fun c hc ζ hζ =>
    (hθ ζ (hc (subset_tsupport _ hζ))).self_of_nhds
  rw [integral_smul_eucFun χ u (contDiff_lapE hφ), conj_lap_chiG hχ hθ hφ, inner_local_lap,
    mulT_conj_thetaPhiG hχ (hsupp χ subset_rfl) hφ,
    mulT_conj_thetaPhiG (isRealT_vfTest 1 hχ) (hsupp _ (tsupport_vfTest_sub 1 χ)) hφ,
    mulT_conj_thetaPhiG (isRealT_vfTest Complex.I hχ) (hsupp _ (tsupport_vfTest_sub Complex.I χ)) hφ,
    mulT_conj_thetaPhiG (isRealT_lapTest hχ) (hsupp _ (tsupport_lapTest_sub χ)) hφ,
    ← integral_smul_eucFun _ _ hφ, ← integral_smul_eucFun _ _ hφ, ← integral_smul_eucFun _ _ hφ,
    ← integral_smul_eucFun _ _ hφ]

/-! ### The Laplacian of the mollified localization -/

lemma molF_eucFun_eq (n : ℕ) (c : testFn) (w : L2H) (x : ℂ) :
    molF n (eucFun c w) x = ∫ t, ((mollR n (x - t) : ℝ) : ℂ) • eucFun c w t := by
  rw [molF_apply]
  congr 1

lemma locallyIntegrable_eucFun (c : testFn) (w : L2H) : LocallyIntegrable (eucFun c w) :=
  (memLp_eucFun c w).locallyIntegrable (by norm_num)

/-- **`Δ_E((χu) ⋆ φ_n)`** in terms of the mollified localized data. -/
theorem lapE_molF_eucFun {θ χ : testFn} (hχ : IsRealT χ)
    (hθ : ∀ ζ ∈ tsupport (χ : ℂ → ℂ), ∀ᶠ w in 𝓝 ζ, (θ : ℂ → ℂ) w = 1)
    (u : negLapH.domain) (n : ℕ) (x : ℂ) :
    lapE (molF n (eucFun χ u)) x
      = -molF n (eucFun (divIm2 χ) (negLapH u)) x
        + 2 * molF n (eucFun (divIm2 (vfTest 1 χ)) (domX u)) x
        + 2 * molF n (eucFun (divIm2 (vfTest Complex.I χ)) (domY u)) x
        + molF n (eucFun (divIm2 (lapTest χ)) u) x := by
  have hk : ContDiff ℝ ∞ (fun t => ((mollR n (x - t) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp ((contDiff_mollR n).comp (contDiff_const.sub contDiff_id))
  have h1 : lapE (molF n (eucFun χ u)) x
      = ∫ t, lapE (fun s => ((mollR n (x - s) : ℝ) : ℂ)) t • eucFun χ u t := by
    rw [molF, lapE_conv (contDiff_mollR n) (hasCompactSupport_mollR n) (locallyIntegrable_eucFun χ u),
      convolution_def]
    congr 1; funext t
    rw [smulL_apply, lapE_kernel (contDiff_mollR n), Complex.coe_smul]
  rw [h1, integral_lapE_smul_eucFun hχ hθ u hk]
  simp only [molF_eucFun_eq]

/-! ### Mollified localizations are test functions -/

lemma support_eucFun_subset (c : testFn) (w : L2H) :
    Function.support (eucFun c w) ⊆ tsupport (c : ℂ → ℂ) := by
  intro ζ hζ
  apply subset_tsupport
  intro h0; apply hζ; simp [eucFun, h0]

/-- `tsupport c + closedBall 0 r`. -/
def thick (c : testFn) (r : ℝ) : Set ℂ := tsupport (c : ℂ → ℂ) + closedBall (0 : ℂ) r

lemma isCompact_thick (c : testFn) (r : ℝ) : IsCompact (thick c r) :=
  (show IsCompact (tsupport (c : ℂ → ℂ)) from c.2.compact).add (isCompact_closedBall 0 r)

lemma thick_mono (c : testFn) {r s : ℝ} (h : r ≤ s) : thick c r ⊆ thick c s :=
  Set.add_subset_add subset_rfl (closedBall_subset_closedBall h)

lemma im_ge_of_mem_thick {c : testFn} {y₀ r : ℝ} (hc : ∀ a ∈ tsupport (c : ℂ → ℂ), y₀ ≤ a.im)
    {z : ℂ} (hz : z ∈ thick c r) : y₀ - r ≤ z.im := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.1 hz
  have h1 := hc a ha
  have h2 : |b.im| ≤ r := (Complex.abs_im_le_norm b).trans (mem_closedBall_zero_iff.1 hb)
  rw [Complex.add_im]
  have := neg_abs_le b.im
  linarith

lemma support_molF_subset (n : ℕ) (c : testFn) (w : L2H) :
    Function.support (molF n (eucFun c w)) ⊆ thick c (1 / ((n : ℝ) + 1)) := by
  refine (support_convolution_subset (L := smulL) (μ := volume)).trans ?_
  refine Set.add_subset_add (support_eucFun_subset c w) ?_
  rw [mollR, (bumpN n).support_normed_eq]
  exact ball_subset_closedBall

lemma isTestFn_molF {c : testFn} (w : L2H) {y₀ : ℝ}
    (hc : ∀ a ∈ tsupport (c : ℂ → ℂ), y₀ ≤ a.im) {n : ℕ} (hn : 1 / ((n : ℝ) + 1) < y₀) :
    IsTestFn (molF n (eucFun c w)) := by
  have htsupp : tsupport (molF n (eucFun c w)) ⊆ thick c (1 / ((n : ℝ) + 1)) :=
    closure_minimal (support_molF_subset n c w) (isCompact_thick c _).isClosed
  refine ⟨contDiff_molF_aux n (locallyIntegrable_eucFun c w),
    IsCompact.of_isClosed_subset (isCompact_thick c _) (isClosed_tsupport _) htsupp, ?_⟩
  intro z hz
  have := im_ge_of_mem_thick hc (htsupp hz)
  show 0 < z.im
  linarith

/-! ### Multiplication of `L²(ℍ)` by a test function -/

lemma memLp_mulTL (c : testFn) (w : L2H) :
    MemLp (fun z : ℍ => (c : ℂ → ℂ) z * repL2 w z) 2 volume := by
  obtain ⟨B, hB⟩ := c.2.smooth.continuous.bounded_above_of_compact_support c.2.compact
  refine MemLp.of_le_mul (c := B) ((Lp.memLp w).ae_eq (repL2_ae w)) ?_ ?_
  · exact ((c.2.smooth.continuous.comp UpperHalfPlane.continuous_coe).aestronglyMeasurable).mul
      (stronglyMeasurable_repL2 w).aestronglyMeasurable
  · exact Eventually.of_forall fun z => by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hB z) (norm_nonneg _)

/-- `c · w ∈ L²(ℍ)` for a test function `c`. -/
noncomputable def mulTL (c : testFn) (w : L2H) : L2H := (memLp_mulTL c w).toLp _

lemma mulTL_ae (c : testFn) (w : L2H) :
    ⇑(mulTL c w) =ᵐ[volume] fun z : ℍ => (c : ℂ → ℂ) z * repL2 w z := (memLp_mulTL c w).coeFn_toLp

lemma toL2_ae (F : testFn) : ⇑(toL2 F) =ᵐ[volume] fun z : ℍ => (F : ℂ → ℂ) z :=
  (memLp_comp_coe F.2).coeFn_toLp

lemma eucFun_coe (c : testFn) (w : L2H) (z : ℍ) :
    eucFun c w (z : ℂ) = (c : ℂ → ℂ) z * repL2 w z := by
  simp [eucFun]

/-! ### From `L²(ℂ)` to `L²(ℍ)` on supports away from the boundary -/

lemma lintegral_H_le {G m : ℂ → ℂ} (hG : Measurable G) (hm : Measurable m) {a M : ℝ} (ha : 0 < a)
    (hM : 0 ≤ M) (hb : ∀ ζ, G ζ ≠ 0 → a ≤ ζ.im ∧ ‖m ζ‖ ≤ M) :
    ∫⁻ z : ℍ, ‖m z * G z‖ₑ ^ (2 : ℝ) ≤ ENNReal.ofReal ((M / a) ^ 2) * ∫⁻ ζ, ‖G ζ‖ₑ ^ (2 : ℝ) := by
  have hg : Measurable fun z : ℍ => ‖m z * G z‖ₑ ^ (2 : ℝ) :=
    ((hm.comp measurable_coe).mul (hG.comp measurable_coe)).enorm.pow_const _
  rw [lintegral_H_eq hg, ← lintegral_const_mul _ (hG.enorm.pow_const _)]
  refine lintegral_mono fun ζ => ?_
  by_cases hζ : 0 < ζ.im
  · rw [Set.indicator_of_mem (show ζ ∈ {w : ℂ | 0 < w.im} from hζ)]
    have e : ((UpperHalfPlane.ofComplex ζ : ℍ) : ℂ) = ζ := by
      rw [ofComplex_apply_of_im_pos hζ]
    simp only [e]
    by_cases h0 : G ζ = 0
    · simp [h0]
    · obtain ⟨h1, h2⟩ := hb ζ h0
      rw [enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← mul_assoc]
      refine mul_le_mul' ?_ le_rfl
      rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
        ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [show ‖m ζ‖ ^ (2 : ℝ) = ‖m ζ‖ ^ 2 by norm_cast]
      have h3 : 1 / ζ.im ≤ 1 / a := one_div_le_one_div_of_le ha h1
      calc (1 / ζ.im) ^ 2 * ‖m ζ‖ ^ 2 = (‖m ζ‖ * (1 / ζ.im)) ^ 2 := by ring
        _ ≤ (M * (1 / a)) ^ 2 :=
            pow_le_pow_left₀ (by positivity) (mul_le_mul h2 h3 (by positivity) hM) 2
        _ = (M / a) ^ 2 := by ring
  · rw [Set.indicator_of_notMem (show ζ ∉ {w : ℂ | 0 < w.im} from hζ)]
    exact bot_le

lemma eLpNorm_H_le {G m : ℂ → ℂ} (hG : Measurable G) (hm : Measurable m) {a M : ℝ} (ha : 0 < a)
    (hM : 0 ≤ M) (hb : ∀ ζ, G ζ ≠ 0 → a ≤ ζ.im ∧ ‖m ζ‖ ≤ M) :
    eLpNorm (fun z : ℍ => m z * G z) 2 volume ≤ ENNReal.ofReal (M / a) * eLpNorm G 2 volume := by
  have hmeasH : AEStronglyMeasurable (fun z : ℍ => m z * G z) volume :=
    ((hm.comp measurable_coe).mul (hG.comp measurable_coe)).aestronglyMeasurable
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top hmeasH,
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top hG.aestronglyMeasurable,
    ENNReal.toReal_ofNat]
  calc (∫⁻ z : ℍ, ‖m z * G z‖ₑ ^ (2 : ℝ)) ^ (1 / (2 : ℝ))
      ≤ (ENNReal.ofReal ((M / a) ^ 2) * ∫⁻ ζ, ‖G ζ‖ₑ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) :=
        ENNReal.rpow_le_rpow (lintegral_H_le hG hm ha hM hb) (by norm_num)
    _ = ENNReal.ofReal (M / a) * (∫⁻ ζ, ‖G ζ‖ₑ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
          ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
        congr 2
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        norm_num

/-! ### Convergence of the mollified localizations in `L²(ℍ)` -/

lemma one_div_le_of_ge {N n : ℕ} (h : N ≤ n) : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
  one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right h 1)

lemma hlt_shift {y₀ : ℝ} {N : ℕ} (hN : 1 / ((N : ℝ) + 1) < y₀ / 2) (hy₀ : 0 < y₀) (k : ℕ) :
    1 / (((k + N : ℕ) : ℝ) + 1) < y₀ :=
  lt_of_le_of_lt (one_div_le_of_ge (Nat.le_add_left N k)) (by linarith)

/-- The mollified localization `(cw) ⋆ φ_n` as a test function. -/
noncomputable def molT (c : testFn) (w : L2H) {y₀ : ℝ} (hc : ∀ a ∈ tsupport (c : ℂ → ℂ), y₀ ≤ a.im)
    (n : ℕ) (hn : 1 / ((n : ℝ) + 1) < y₀) : testFn :=
  ⟨molF n (eucFun c w), isTestFn_molF w hc hn⟩

lemma molT_coe (c : testFn) (w : L2H) {y₀ : ℝ} (hc : ∀ a ∈ tsupport (c : ℂ → ℂ), y₀ ≤ a.im)
    (n : ℕ) (hn : 1 / ((n : ℝ) + 1) < y₀) :
    ((molT c w hc n hn : testFn) : ℂ → ℂ) = molF n (eucFun c w) := rfl

lemma tsupport_subset_thick (c : testFn) {r : ℝ} (hr : 0 ≤ r) : tsupport (c : ℂ → ℂ) ⊆ thick c r :=
  fun a ha => Set.mem_add.2 ⟨a, ha, 0, mem_closedBall_self hr, add_zero a⟩

/-- **`m · ((cw) ⋆ φ_{k+N}) → W` in `L²(ℍ)`** when `W = m · cw` a.e. on `ℍ`. -/
theorem tendsto_molF_H {c : testFn} (w : L2H) {y₀ : ℝ} (hy₀ : 0 < y₀)
    (hc : ∀ a ∈ tsupport (c : ℂ → ℂ), y₀ ≤ a.im) {m : ℂ → ℂ} (hm : ContDiff ℝ ∞ m)
    {W : L2H} (hW : ⇑W =ᵐ[volume] fun z : ℍ => m z * eucFun c w z) {N : ℕ}
    (hN : 1 / ((N : ℝ) + 1) < y₀ / 2) :
    Tendsto (fun k : ℕ => toL2 (smulTF m hm (molT c w hc (k + N) (hlt_shift hN hy₀ k))))
      atTop (𝓝 W) := by
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  set K := thick c (y₀ / 2)
  obtain ⟨M, hM⟩ := (isCompact_thick c (y₀ / 2)).exists_bound_of_continuousOn hm.continuous.continuousOn
  set M' := max M 0
  have hM' : ∀ z ∈ K, ‖m z‖ ≤ M' := fun z hz => (hM z hz).trans (le_max_left _ _)
  set f := eucFun c w
  have hG : ∀ n : ℕ, N ≤ n → ∀ ζ, molF n f ζ - f ζ ≠ 0 → y₀ / 2 ≤ ζ.im ∧ ‖m ζ‖ ≤ M' := by
    intro n hn ζ hζ
    have hK : ζ ∈ K := by
      by_cases h1 : molF n f ζ = 0
      · have h2 : f ζ ≠ 0 := by intro h2; apply hζ; rw [h1, h2, sub_zero]
        exact tsupport_subset_thick c (by positivity) (support_eucFun_subset c w h2)
      · refine thick_mono c ?_ (support_molF_subset n c w h1)
        exact (one_div_le_of_ge hn).trans hN.le
    exact ⟨by linarith [im_ge_of_mem_thick hc hK], hM' ζ hK⟩
  have hbound : ∀ k : ℕ, eLpNorm (⇑(toL2 (smulTF m hm (molT c w hc (k + N) (hlt_shift hN hy₀ k))))
      - ⇑W) 2 volume ≤ ENNReal.ofReal (M' / (y₀ / 2))
        * eLpNorm (fun x => molF (k + N) f x - f x) 2 volume := by
    intro k
    have hae : (⇑(toL2 (smulTF m hm (molT c w hc (k + N) (hlt_shift hN hy₀ k)))) - ⇑W)
        =ᵐ[volume] fun z : ℍ => m z * (molF (k + N) f z - f z) := by
      filter_upwards [toL2_ae (smulTF m hm (molT c w hc (k + N) (hlt_shift hN hy₀ k))), hW]
        with z h1 h2
      rw [Pi.sub_apply, h1, h2]
      show m z * molF (k + N) f z - m z * f z = _
      ring
    rw [eLpNorm_congr_ae hae]
    exact eLpNorm_H_le ((contDiff_molF_aux (k + N) (locallyIntegrable_eucFun c w)).continuous.measurable.sub
      (measurable_eucFun c w)) hm.continuous.measurable (by positivity) (le_max_right _ _)
      (hG (k + N) (Nat.le_add_left N k))
  have hconv := (tendsto_molF f (measurable_eucFun c w) (memLp_eucFun c w)).comp
    (tendsto_add_atTop_nat N)
  have hmul := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (M' / (y₀ / 2))) hconv
    (Or.inr ENNReal.ofReal_ne_top)
  rw [mul_zero] at hmul
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmul (fun k => bot_le) hbound

lemma smulTF_one (P : testFn) : smulTF (fun _ => (1 : ℂ)) contDiff_const P = P := by
  apply Subtype.ext; funext ζ
  show 1 * (P : ℂ → ℂ) ζ = (P : ℂ → ℂ) ζ
  rw [one_mul]

lemma tsupport_divImTest_sub (c : testFn) :
    tsupport ((divImTest c : testFn) : ℂ → ℂ) ⊆ tsupport (c : ℂ → ℂ) :=
  tsupport_mul_subset_right

lemma tsupport_divIm2_sub (c : testFn) :
    tsupport ((divIm2 c : testFn) : ℂ → ℂ) ⊆ tsupport (c : ℂ → ℂ) :=
  (tsupport_divImTest_sub _).trans (tsupport_divImTest_sub c)

lemma mulTL_ae_imSq (c : testFn) (w : L2H) :
    ⇑(mulTL c w) =ᵐ[volume] fun z : ℍ => ((z : ℂ).im : ℂ) ^ 2 * eucFun (divIm2 c) w z := by
  filter_upwards [mulTL_ae c w] with z hz
  rw [hz, eucFun_coe]
  have hy : ((z : ℂ).im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 z.im_pos.ne'
  show (c : ℂ → ℂ) z * repL2 w z
    = ((z : ℂ).im : ℂ) ^ 2 * ((invIm z * (invIm z * (c : ℂ → ℂ) z)) * repL2 w z)
  simp only [invIm]; push_cast; field_simp

/-! ### The local step -/

/-- Test functions with supports in one compact set, converging to the localized pair in graph norm. -/
theorem exists_approx_local {θ χ : testFn} (hχ : IsRealT χ)
    (hθ : ∀ ζ ∈ tsupport (χ : ℂ → ℂ), ∀ᶠ w in 𝓝 ζ, (θ : ℂ → ℂ) w = 1)
    {y₀ : ℝ} (hy₀ : 0 < y₀) (hsupp : ∀ a ∈ tsupport (χ : ℂ → ℂ), y₀ ≤ a.im) (u : negLapH.domain) :
    ∃ T : ℕ → testFn, (∀ k, tsupport (T k : ℂ → ℂ) ⊆ thick χ (y₀ / 2)) ∧
      Tendsto (fun k => toL2 (T k)) atTop (𝓝 (mulTL χ u)) ∧
      Tendsto (fun k => -toL2 (lapTest (T k))) atTop
        (𝓝 (mulTL χ (negLapH u) - (2 : ℂ) • mulTL (vfTest 1 χ) (domX u)
          - (2 : ℂ) • mulTL (vfTest Complex.I χ) (domY u) - mulTL (lapTest χ) u)) := by
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt (half_pos hy₀)
  have hsub : ∀ c : testFn, tsupport (c : ℂ → ℂ) ⊆ tsupport (χ : ℂ → ℂ) →
      ∀ a ∈ tsupport ((divIm2 c : testFn) : ℂ → ℂ), y₀ ≤ a.im :=
    fun c hc a ha => hsupp a (hc (tsupport_divIm2_sub c ha))
  have h1 := hsub χ subset_rfl
  have h2 := hsub _ (tsupport_vfTest_sub 1 χ)
  have h3 := hsub _ (tsupport_vfTest_sub Complex.I χ)
  have h4 := hsub _ (tsupport_lapTest_sub χ)
  set T : ℕ → testFn := fun k => molT χ u hsupp (k + N) (hlt_shift hN hy₀ k) with hT
  set T1 : ℕ → testFn := fun k => smulTF _ contDiff_imSq
    (molT (divIm2 χ) (negLapH u) h1 (k + N) (hlt_shift hN hy₀ k))
  set T2 : ℕ → testFn := fun k => smulTF _ contDiff_imSq
    (molT (divIm2 (vfTest 1 χ)) (domX u) h2 (k + N) (hlt_shift hN hy₀ k))
  set T3 : ℕ → testFn := fun k => smulTF _ contDiff_imSq
    (molT (divIm2 (vfTest Complex.I χ)) (domY u) h3 (k + N) (hlt_shift hN hy₀ k))
  set T4 : ℕ → testFn := fun k => smulTF _ contDiff_imSq
    (molT (divIm2 (lapTest χ)) u h4 (k + N) (hlt_shift hN hy₀ k))
  have hlap : ∀ k, -toL2 (lapTest (T k))
      = toL2 (T1 k) - (2 : ℂ) • toL2 (T2 k) - (2 : ℂ) • toL2 (T3 k) - toL2 (T4 k) := by
    intro k
    have e : -lapTest (T k) = T1 k - (2 : ℂ) • T2 k - (2 : ℂ) • T3 k - T4 k := by
      apply Subtype.ext; funext ζ
      show -(((ζ.im : ℝ) : ℂ) ^ 2 * lapE (molF (k + N) (eucFun χ u)) ζ)
        = ((ζ.im : ℝ) : ℂ) ^ 2 * molF (k + N) (eucFun (divIm2 χ) (negLapH u)) ζ
          - 2 * (((ζ.im : ℝ) : ℂ) ^ 2 * molF (k + N) (eucFun (divIm2 (vfTest 1 χ)) (domX u)) ζ)
          - 2 * (((ζ.im : ℝ) : ℂ) ^ 2 * molF (k + N) (eucFun (divIm2 (vfTest Complex.I χ)) (domY u)) ζ)
          - ((ζ.im : ℝ) : ℂ) ^ 2 * molF (k + N) (eucFun (divIm2 (lapTest χ)) u) ζ
      rw [lapE_molF_eucFun hχ hθ u]
      ring
    rw [← map_neg, e, map_sub, map_sub, map_sub, map_smul, map_smul]
  have hc0 : Tendsto (fun k => toL2 (T k)) atTop (𝓝 (mulTL χ u)) := by
    have h := tendsto_molF_H (u : L2H) hy₀ hsupp contDiff_const (W := mulTL χ u)
      (by filter_upwards [mulTL_ae χ u] with z hz; rw [hz, eucFun_coe, one_mul]) hN
    simpa only [smulTF_one] using h
  have hc1 := tendsto_molF_H (negLapH u) hy₀ h1 contDiff_imSq (mulTL_ae_imSq χ (negLapH u)) hN
  have hc2 := tendsto_molF_H (domX u) hy₀ h2 contDiff_imSq (mulTL_ae_imSq (vfTest 1 χ) (domX u)) hN
  have hc3 := tendsto_molF_H (domY u) hy₀ h3 contDiff_imSq
    (mulTL_ae_imSq (vfTest Complex.I χ) (domY u)) hN
  have hc4 := tendsto_molF_H (u : L2H) hy₀ h4 contDiff_imSq (mulTL_ae_imSq (lapTest χ) u) hN
  have hsnd : Tendsto (fun k => -toL2 (lapTest (T k))) atTop
      (𝓝 (mulTL χ (negLapH u) - (2 : ℂ) • mulTL (vfTest 1 χ) (domX u)
        - (2 : ℂ) • mulTL (vfTest Complex.I χ) (domY u) - mulTL (lapTest χ) u)) := by
    simp_rw [hlap]
    exact ((hc1.sub (hc2.const_smul (2 : ℂ))).sub (hc3.const_smul (2 : ℂ))).sub hc4
  refine ⟨T, fun k => ?_, hc0, hsnd⟩
  have h1 : tsupport (T k : ℂ → ℂ) ⊆ thick χ (1 / (((k + N : ℕ) : ℝ) + 1)) :=
    closure_minimal (support_molF_subset (k + N) χ u) (isCompact_thick χ _).isClosed
  exact h1.trans (thick_mono χ ((one_div_le_of_ge (Nat.le_add_left N k)).trans hN.le))

/-- **`χu ∈ Dom(Ā)` with `Ā(χu) = χ(-Δu) - 2(Xχ)Xu - 2(Yχ)Yu - (Δχ)u`.** -/
theorem mem_graphBar_local {θ χ : testFn} (hχ : IsRealT χ)
    (hθ : ∀ ζ ∈ tsupport (χ : ℂ → ℂ), ∀ᶠ w in 𝓝 ζ, (θ : ℂ → ℂ) w = 1)
    {y₀ : ℝ} (hy₀ : 0 < y₀) (hsupp : ∀ a ∈ tsupport (χ : ℂ → ℂ), y₀ ≤ a.im) (u : negLapH.domain) :
    ((mulTL χ u, mulTL χ (negLapH u) - (2 : ℂ) • mulTL (vfTest 1 χ) (domX u)
        - (2 : ℂ) • mulTL (vfTest Complex.I χ) (domY u) - mulTL (lapTest χ) u) : L2H × L2H)
      ∈ graphBar := by
  obtain ⟨T, -, hc0, hsnd⟩ := exists_approx_local hχ hθ hy₀ hsupp u
  have hgraph : ∀ k, ((toL2 (T k), -toL2 (lapTest (T k))) : L2H × L2H) ∈ negLap.graph := by
    intro k
    have h := negLap.mem_graph (toL2Equiv (T k))
    rwa [coe_toL2Equiv, negLap_toL2Equiv] at h
  have hclosed : IsClosed (graphBar : Set (L2H × L2H)) := negLap.graph.isClosed_topologicalClosure
  exact hclosed.mem_of_tendsto (hc0.prodMk_nhds hsnd)
    (Eventually.of_forall fun k => negLap.graph.le_topologicalClosure (hgraph k))

end Qschubert
