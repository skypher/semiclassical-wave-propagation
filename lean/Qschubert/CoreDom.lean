import Qschubert.CoreLocal

/-!
# The core dictionary `Dom(-Δ) ⊆ Dom(Ā)`

`negLapH` is the Friedrichs extension of `-Δ` on test functions; `Ā = negLap.closure` is the
closure of `-Δ` on test functions, with graph `graphBar`.

* `tendsto_mulTL` (dominated convergence for test-function multipliers on `L²(ℍ)`).
* `mem_graphBar_negLapH` (**the core dictionary**): for every `u ∈ Dom(negLapH)`,
  `(u, negLapH u) ∈ graphBar`. Proof: `χ_S u ∈ Dom(Ā)` with
  `Ā(χ_S u) = χ_S(-Δu) - 2(Xχ_S)Xu - 2(Yχ_S)Yu - (Δχ_S)u` (`mem_graphBar_local`, with `θ = χ_{3S}`,
  `y₀ = 1/(4S)`), and as `S → ∞` this converges to `(u, -Δu)` by dominated convergence (uniform
  bounds and pointwise eventual constancy from `HypCutoff`); `graphBar` is closed.
* `negLapH_domain_le` / `negLap_closure_eq_negLapH`: `Dom(negLapH) ⊆ Dom(Ā)` and `Ā u = negLapH u`
  there, i.e. `negLapH ≤ Ā`; with `Ā ≤ negLapH` (`Ā` is the closure of a restriction of the
  closed operator `negLapH`) this gives `Ā = negLapH`: `-Δ` is essentially self-adjoint on test
  functions.
* `lapTbar_zero` (R74's request): `lapTbar 0 p = -p.2` on `graphBar`.
-/

namespace Qschubert

open MeasureTheory UpperHalfPlane Filter Topology Metric Set
open scoped ContDiff ENNReal

local notation "L2H" => Lp ℂ 2 (volume : Measure ℍ)

/-! ### Dominated convergence for multipliers -/

theorem tendsto_mulTL {c : ℕ → testFn} {g : ℍ → ℂ} {B : ℝ} (w : L2H)
    (hB : ∀ k (z : ℍ), ‖(c k : ℂ → ℂ) z‖ ≤ B) (hg : ∀ z, ‖g z‖ ≤ B) (hgm : AEStronglyMeasurable g volume)
    (hlim : ∀ z : ℍ, Tendsto (fun k => (c k : ℂ → ℂ) z) atTop (𝓝 (g z)))
    {W : L2H} (hW : ⇑W =ᵐ[volume] fun z => g z * repL2 w z) :
    Tendsto (fun k => mulTL (c k) w) atTop (𝓝 W) := by
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  set F : ℕ → ℍ → ℂ := fun k z => ((c k : ℂ → ℂ) z - g z) * repL2 w z
  have hae : ∀ k, (⇑(mulTL (c k) w) - ⇑W) =ᵐ[volume] F k := by
    intro k
    filter_upwards [mulTL_ae (c k) w, hW] with z h1 h2
    rw [Pi.sub_apply, h1, h2]
    simp only [F]; ring
  have hFm : ∀ k, AEStronglyMeasurable (F k) volume := fun k =>
    ((((c k).2.smooth.continuous.comp UpperHalfPlane.continuous_coe).aestronglyMeasurable).sub hgm).mul
      (stronglyMeasurable_repL2 w).aestronglyMeasurable
  have heq : ∀ k, eLpNorm (⇑(mulTL (c k) w) - ⇑W) 2 volume
      = (∫⁻ z, ‖F k z‖ₑ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
    intro k
    rw [eLpNorm_congr_ae (hae k), eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero
      ENNReal.ofNat_ne_top (hFm k), ENNReal.toReal_ofNat]
  simp_rw [heq]
  have hbound : ∀ k, (fun z => ‖F k z‖ₑ ^ (2 : ℝ))
      ≤ᵐ[volume] fun z => ENNReal.ofReal ((2 * B) ^ 2) * ‖repL2 w z‖ₑ ^ (2 : ℝ) := by
    intro k
    refine Eventually.of_forall fun z => ?_
    simp only [F]
    rw [enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
    refine mul_le_mul' ?_ le_rfl
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [show ‖(c k : ℂ → ℂ) z - g z‖ ^ (2 : ℝ) = ‖(c k : ℂ → ℂ) z - g z‖ ^ 2 by norm_cast]
    have h1 : ‖(c k : ℂ → ℂ) z - g z‖ ≤ 2 * B := (norm_sub_le _ _).trans (by linarith [hB k z, hg z])
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  have hfin : ∫⁻ z, ENNReal.ofReal ((2 * B) ^ 2) * ‖repL2 w z‖ₑ ^ (2 : ℝ) ≠ ⊤ := by
    rw [lintegral_const_mul _ ((stronglyMeasurable_repL2 w).measurable.enorm.pow_const _)]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (lintegral_repL2_lt_top w).ne
  have hpt : ∀ z : ℍ, Tendsto (fun k => ‖F k z‖ₑ ^ (2 : ℝ)) atTop (𝓝 0) := by
    intro z
    have h1 : Tendsto (fun k => F k z) atTop (𝓝 0) := by
      have := ((hlim z).sub_const (g z)).mul_const (repL2 w z)
      simpa [F] using this
    have h2 := ((ENNReal.continuous_rpow_const (y := (2 : ℝ))).tendsto _).comp
      ((continuous_enorm.tendsto (0 : ℂ)).comp h1)
    simpa [Function.comp_def] using h2
  have hDCT := tendsto_lintegral_of_dominated_convergence' _
    (fun k => (hFm k).enorm.pow_const _) hbound hfin (Eventually.of_forall hpt)
  simp only [lintegral_zero] at hDCT
  have h3 := ((ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ))).tendsto _).comp hDCT
  simpa [Function.comp_def] using h3

/-! ### The core dictionary -/

lemma cutT_tsupport_im {S : ℝ} (hS : 0 < S) :
    ∀ a ∈ tsupport ((cutT S hS : testFn) : ℂ → ℂ), 1 / (4 * S) ≤ a.im := by
  intro a ha
  have h := (tsupport_cutS_subset hS ha).1
  rw [div_le_iff₀ (by positivity)]
  linarith

lemma eventually_cutT {z : ℍ} :
    ∀ᶠ k : ℕ in atTop, gH z < (k : ℝ) + 1 := by
  obtain ⟨K, hK⟩ := exists_nat_gt (gH z)
  filter_upwards [eventually_ge_atTop K] with k hk
  have : (K : ℝ) ≤ k := by exact_mod_cast hk
  linarith

/-- **The core dictionary**: `(u, -Δu) ∈ graph(Ā)` for every `u` in the Friedrichs domain. -/
theorem mem_graphBar_negLapH (u : negLapH.domain) :
    (((u : L2H), negLapH u) : L2H × L2H) ∈ graphBar := by
  have hS : ∀ k : ℕ, (0 : ℝ) < (k : ℝ) + 1 := fun k => by positivity
  set χ : ℕ → testFn := fun k => cutT ((k : ℝ) + 1) (hS k) with hχ
  have hloc : ∀ k, ((mulTL (χ k) u, mulTL (χ k) (negLapH u) - (2 : ℂ) • mulTL (vfTest 1 (χ k)) (domX u)
      - (2 : ℂ) • mulTL (vfTest Complex.I (χ k)) (domY u) - mulTL (lapTest (χ k)) u) : L2H × L2H)
      ∈ graphBar := fun k =>
    mem_graphBar_local (θ := cutT (3 * ((k : ℝ) + 1)) (by positivity)) (isRealT_cutT (hS k))
      (fun ζ hζ => cutS_three_eventuallyEq_one (hS k) hζ) (by positivity) (cutT_tsupport_im (hS k)) u
  -- pointwise behaviour
  have hev : ∀ z : ℍ, ∀ᶠ k : ℕ in atTop,
      ((χ k : testFn) : ℂ → ℂ) z = 1 ∧ ((vfTest 1 (χ k) : testFn) : ℂ → ℂ) z = 0
        ∧ ((vfTest Complex.I (χ k) : testFn) : ℂ → ℂ) z = 0
        ∧ ((lapTest (χ k) : testFn) : ℂ → ℂ) z = 0 := fun z => by
    filter_upwards [eventually_cutT (z := z)] with k hk
    exact cutT_eventually (hS k) z.im_pos hk
  have lim1 : ∀ z : ℍ, Tendsto (fun k => ((χ k : testFn) : ℂ → ℂ) z) atTop (𝓝 ((fun _ => (1 : ℂ)) z)) :=
    fun z => tendsto_const_nhds.congr' ((hev z).mono fun k hk => hk.1.symm)
  have limX : ∀ z : ℍ, Tendsto (fun k => ((vfTest 1 (χ k) : testFn) : ℂ → ℂ) z) atTop
      (𝓝 ((fun _ => (0 : ℂ)) z)) :=
    fun z => tendsto_const_nhds.congr' ((hev z).mono fun k hk => hk.2.1.symm)
  have limY : ∀ z : ℍ, Tendsto (fun k => ((vfTest Complex.I (χ k) : testFn) : ℂ → ℂ) z) atTop
      (𝓝 ((fun _ => (0 : ℂ)) z)) :=
    fun z => tendsto_const_nhds.congr' ((hev z).mono fun k hk => hk.2.2.1.symm)
  have limL : ∀ z : ℍ, Tendsto (fun k => ((lapTest (χ k) : testFn) : ℂ → ℂ) z) atTop
      (𝓝 ((fun _ => (0 : ℂ)) z)) :=
    fun z => tendsto_const_nhds.congr' ((hev z).mono fun k hk => hk.2.2.2.symm)
  have hW1 : ∀ w : L2H, ⇑w =ᵐ[volume] fun z => (fun _ => (1 : ℂ)) z * repL2 w z := fun w => by
    filter_upwards [repL2_ae w] with z hz; rw [hz, one_mul]
  have hW0 : ∀ w : L2H, ⇑(0 : L2H) =ᵐ[volume] fun z => (fun _ => (0 : ℂ)) z * repL2 w z := fun w => by
    filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure ℍ)] with z hz; rw [hz, zero_mul]; rfl
  have b1 : ∀ k (z : ℍ), ‖((χ k : testFn) : ℂ → ℂ) z‖ ≤ 1 := fun k z => norm_cutS_le_one _ _
  have bX : ∀ k (z : ℍ), ‖((vfTest 1 (χ k) : testFn) : ℂ → ℂ) z‖ ≤ 2 * M1 := fun k z =>
    norm_vf_cutT_one_le (hS k) z.im_pos
  have bY : ∀ k (z : ℍ), ‖((vfTest Complex.I (χ k) : testFn) : ℂ → ℂ) z‖ ≤ 2 * M1 := fun k z =>
    norm_vf_cutT_I_le (hS k) z.im_pos
  have bL : ∀ k (z : ℍ), ‖((lapTest (χ k) : testFn) : ℂ → ℂ) z‖ ≤ 8 * M2 + 4 * M1 := fun k z =>
    norm_lap_cutT_le (hS k) z.im_pos
  have hM1 := M1_nonneg
  have hM2 := M2_nonneg
  have m1 : AEStronglyMeasurable (fun _ : ℍ => (1 : ℂ)) volume := aestronglyMeasurable_const
  have m0 : AEStronglyMeasurable (fun _ : ℍ => (0 : ℂ)) volume := aestronglyMeasurable_const
  have t1 := tendsto_mulTL (u : L2H) b1 (fun _ => by simp) m1 lim1 (hW1 u)
  have t2 := tendsto_mulTL (negLapH u) b1 (fun _ => by simp) m1 lim1 (hW1 (negLapH u))
  have tX := tendsto_mulTL (domX u) bX (fun _ => by simp; linarith) m0 limX (hW0 (domX u))
  have tY := tendsto_mulTL (domY u) bY (fun _ => by simp; linarith) m0 limY (hW0 (domY u))
  have tL := tendsto_mulTL (u : L2H) bL (fun _ => by simp; linarith) m0 limL (hW0 (u : L2H))
  have hsnd : Tendsto (fun k => mulTL (χ k) (negLapH u) - (2 : ℂ) • mulTL (vfTest 1 (χ k)) (domX u)
      - (2 : ℂ) • mulTL (vfTest Complex.I (χ k)) (domY u) - mulTL (lapTest (χ k)) u) atTop
      (𝓝 (negLapH u)) := by
    have := ((t2.sub (tX.const_smul (2 : ℂ))).sub (tY.const_smul (2 : ℂ))).sub tL
    simpa using this
  have hclosed : IsClosed (graphBar : Set (L2H × L2H)) := negLap.graph.isClosed_topologicalClosure
  exact hclosed.mem_of_tendsto (t1.prodMk_nhds hsnd) (Eventually.of_forall hloc)

/-- `Dom(-Δ_Friedrichs) ⊆ Dom(Ā)`, with `Ā u = -Δu` there. -/
theorem negLapH_le_closure : negLapH ≤ negLap.closure := by
  refine LinearPMap.le_of_le_graph ?_
  intro p hp
  rw [LinearPMap.mem_graph_iff] at hp
  obtain ⟨u, hu1, hu2⟩ := hp
  rw [← graphBar_eq]
  have hp : p = ((u : L2H), negLapH u) := Prod.ext hu1.symm hu2.symm
  rw [hp]
  exact mem_graphBar_negLapH u

/-- `Ā ≤ -Δ_Friedrichs`: the closure of a restriction of the closed operator `negLapH`. -/
theorem negLap_closure_le_negLapH : negLap.closure ≤ negLapH := by
  refine LinearPMap.le_of_le_graph ?_
  rw [← negLap_isClosable.graph_closure_eq_closure_graph]
  exact Submodule.topologicalClosure_minimal _ (LinearPMap.le_graph_of_le negLap_le_negLapH)
    negLapH_isSelfAdjoint.isClosed

/-- **`Ā = -Δ_Friedrichs`: `-Δ` is essentially self-adjoint on test functions.** -/
theorem negLap_closure_eq_negLapH : negLap.closure = negLapH :=
  le_antisymm negLap_closure_le_negLapH negLapH_le_closure

/-! ### `Δ(0) = Δ` on the graph closure (R74) -/

lemma lapTL2_zero (G : testFn) : lapTL2 0 G = toL2 (lapTest G) := by
  rw [lapTL2_eq, mul_zero, Real.exp_zero, Complex.ofReal_one, one_smul, ← map_add, xxTest_eq,
    yyTest_eq, lapTest_eq_vf]
  congr 1
  abel

/-- `lapTbar 0 p = -p.2` on `graphBar`: `Δ(0)` is `Δ = -Ā`. -/
theorem lapTbar_zero (p : graphBar) : lapTbar 0 p = -(p : L2H × L2H).2 := by
  have hc1 : Continuous fun p : graphBar => lapTbar 0 p :=
    continuous_lapTbar_uncurry.comp (continuous_id.prodMk continuous_const)
  have hc2 : Continuous fun p : graphBar => -(p : L2H × L2H).2 :=
    (continuous_snd.comp continuous_subtype_val).neg
  have h := denseRange_graphIncl.equalizer hc1 hc2 (funext fun q => by
    simp only [Function.comp_apply]
    rw [lapTbar_incl, lapTL2_zero]
    change toL2 (lapTest (testOf q)) = -(q : L2H × L2H).2
    rw [← neg_toL2_lapTest_testOf q, neg_neg])
  exact congrFun h p

end Qschubert
