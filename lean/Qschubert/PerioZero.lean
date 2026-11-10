import Qschubert.TransGL
import Qschubert.KLWaveD
import Qschubert.TestTransport

/-!
# A test function with vanishing periodization: the translated pairings of `e^{-αΛ} k` sum to zero

Stage X of the plan for Proposition `ev:mod` (`lean/BLUEPRINT.md`). Let `k` be a test function with
`Σ_{n ∈ ℤ} k(z + n) = 0` for all `z ∈ ℍ`, and `U_n f = f(· + n)`. Then for every `Ψ ∈ L²(ℍ)`,

`Σ_{|n| ≤ N} ⟪Ψ, U_n e^{-αΛ} k⟫ → 0` as `N → ∞` (`tendsto_sum_pair_trans`).

Proof. The sum is `⟪e^{-αΛ} Ψ, K_N⟫` with `K_N = Σ_{|n| ≤ N} U_n k` (`e^{-αΛ}` is self-adjoint and commutes with `U_n`).
If `k` vanishes outside `{|x| ≤ R}` and `L > 2R`, then `K_N = 1_{B_N} (K_N - K_{N-L})` with `B_N = {|x| ≥ N - R}`, so
`|⟪G, K_N⟫| ≤ ‖1_{B_N} G‖ · 2L ‖k‖`, and `‖1_{B_N} G‖ → 0` for `G ∈ L²`.
-/

namespace Qschubert

open MeasureTheory Filter Topology UpperHalfPlane Set Physicslib4.Spectral Physicslib4.Spectral.Unbounded
open scoped MatrixGroups InnerProductSpace ComplexConjugate

local notation "L2H" => Lp ℂ 2 (volume : Measure ℍ)

/-- `K_s = Σ_{n ∈ s} U_n k`. -/
noncomputable def transSumL (k : testFn) (s : Finset ℤ) : L2H := ∑ n ∈ s, glU (transGL (n : ℝ)) (toL2 k)

lemma transSumL_ae (k : testFn) (s : Finset ℤ) :
    ⇑(transSumL k s) =ᵐ[volume] fun z : ℍ => ∑ n ∈ s, (k : ℂ → ℂ) ((z : ℂ) + n) := by
  have e : transSumL k s = toL2 (∑ n ∈ s, testCompT (transGL (n : ℝ)) k) := by
    rw [transSumL, map_sum]
    exact Finset.sum_congr rfl fun n _ => (toL2_testCompT _ k).symm
  rw [e]
  filter_upwards [toL2_ae (∑ n ∈ s, testCompT (transGL (n : ℝ)) k)] with z hz
  rw [hz, Submodule.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun n _ => ?_
  show testComp (transGL (n : ℝ)) (k : ℂ → ℂ) (z : ℂ) = _
  rw [testComp_coe, coe_transGL_smul, Complex.ofReal_intCast]

/-- The translated pairings in terms of `K_s`. -/
lemma sum_pair_trans {α : ℝ} (hα : 0 < α) (k : testFn) (Ψ : L2H) (s : Finset ℤ) :
    ∑ n ∈ s, ⟪Ψ, glU (transGL (n : ℝ)) ((expCut α hα).J (toL2 k))⟫_ℂ
      = ⟪(expCut α hα).J Ψ, transSumL k s⟫_ℂ := by
  rw [transSumL, inner_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← expCut_J_glU hα, ← ContinuousLinearMap.adjoint_inner_left, (expCut α hα).adjoint_J]

/-- **The translated pairings of `e^{-αΛ} k` sum to zero.** -/
theorem tendsto_sum_pair_trans {α : ℝ} (hα : 0 < α) (k : testFn)
    (hk : ∀ z : ℍ, HasSum (fun n : ℤ => (k : ℂ → ℂ) ((z : ℂ) + n)) 0) (Ψ : L2H) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc (-(N : ℤ)) N,
      ⟪Ψ, glU (transGL (n : ℝ)) ((expCut α hα).J (toL2 k))⟫_ℂ) atTop (𝓝 0) := by
  set G : L2H := (expCut α hα).J Ψ with hG
  -- the support of `k` in `x`
  obtain ⟨R₀, hR₀⟩ := k.2.compact.isBounded.exists_norm_le
  set R : ℝ := max R₀ 0 with hRd
  have hR0 : 0 ≤ R := le_max_right _ _
  have hsupp : ∀ w : ℂ, (k : ℂ → ℂ) w ≠ 0 → |w.re| ≤ R := fun w hw =>
    (Complex.abs_re_le_norm w).trans ((hR₀ w (subset_tsupport _ hw)).trans (le_max_left _ _))
  set L : ℕ := ⌈2 * R⌉₊ + 1 with hLd
  have hL : 2 * R < L := by
    rw [hLd]
    push_cast
    linarith [Nat.le_ceil (2 * R)]
  set B : ℕ → Set ℍ := fun N => {z : ℍ | (N : ℝ) - R ≤ |z.re|} with hBd
  have hBm : ∀ N, MeasurableSet (B N) := fun N =>
    measurableSet_le measurable_const (continuous_abs.measurable.comp UpperHalfPlane.continuous_re.measurable)
  have hGint : Integrable fun z : ℍ => ‖G z‖ ^ 2 := integrable_norm_sq G
  -- the tail of `G`
  have htail : Tendsto (fun N : ℕ => ∫ z in B N, ‖G z‖ ^ 2) atTop (𝓝 0) := by
    have hanti : Antitone B := fun M N hMN z hz => by
      have h1 : (M : ℝ) ≤ N := by exact_mod_cast hMN
      exact le_trans (by linarith) (show (N : ℝ) - R ≤ |z.re| from hz)
    have hint : (⋂ N, B N) = ∅ := by
      ext z
      simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false, not_forall, hBd, Set.mem_ofPred_eq, not_le]
      obtain ⟨N, hN⟩ := exists_nat_gt (|z.re| + R)
      exact ⟨N, by linarith⟩
    have h1 := tendsto_setIntegral_of_antitone hBm hanti ⟨0, hGint.integrableOn⟩
    rwa [hint, Measure.restrict_empty, integral_zero_measure] at h1
  -- the bound for each `N ≥ L`
  have hbound : ∀ N : ℕ, L ≤ N → ‖⟪G, transSumL k (Finset.Icc (-(N : ℤ)) N)⟫_ℂ‖
      ≤ Real.sqrt (∫ z in B N, ‖G z‖ ^ 2) * (2 * L * ‖toL2 k‖) := by
    intro N hN
    set s : Finset ℤ := Finset.Icc (-(N : ℤ)) N with hs
    set s' : Finset ℤ := Finset.Icc (-((N - L : ℕ) : ℤ)) ((N - L : ℕ) : ℤ) with hs'
    have hNL : ((N - L : ℕ) : ℝ) = (N : ℝ) - L := by
      rw [Nat.cast_sub hN]
    have hss : s' ⊆ s := by
      intro n hn
      rw [hs', Finset.mem_Icc] at hn
      rw [hs, Finset.mem_Icc]
      have h1 : ((N - L : ℕ) : ℤ) ≤ N := by exact_mod_cast Nat.sub_le N L
      constructor <;> linarith [hn.1, hn.2]
    set D : L2H := transSumL k s - transSumL k s' with hD
    -- `K_N = 1_B (K_N - K_{N-L})` a.e.
    have hae : ∀ᵐ z : ℍ, transSumL k s z = (B N).indicator (fun z => D z) z := by
      filter_upwards [transSumL_ae k s, transSumL_ae k s', Lp.coeFn_sub (transSumL k s) (transSumL k s')]
        with z e1 e2 e3
      by_cases hz : z ∈ B N
      · rw [Set.indicator_of_mem hz, hD, e3, Pi.sub_apply, e2]
        have hzero : ∑ n ∈ s', (k : ℂ → ℂ) ((z : ℂ) + n) = 0 := by
          refine Finset.sum_eq_zero fun n hn => ?_
          by_contra hne
          have h1 := hsupp _ hne
          rw [hs', Finset.mem_Icc] at hn
          have hn' : |(n : ℝ)| ≤ (N : ℝ) - L := by
            rw [abs_le, ← hNL]
            constructor
            · exact_mod_cast hn.1
            · exact_mod_cast hn.2
          have hre : ((z : ℂ) + n).re = z.re + n := by simp [UpperHalfPlane.coe_re]
          rw [hre] at h1
          have hz' : (N : ℝ) - R ≤ |z.re| := hz
          have h2 : |z.re| ≤ |z.re + n| + |(n : ℝ)| := by
            have := abs_sub (z.re + n) (n : ℝ)
            simpa using this
          linarith
        rw [hzero, sub_zero]
      · rw [Set.indicator_of_notMem hz, e1]
        have hz' : |z.re| < (N : ℝ) - R := not_le.1 hz
        have hout : ∀ n : ℤ, n ∉ s → (k : ℂ → ℂ) ((z : ℂ) + n) = 0 := by
          intro n hn
          by_contra hne
          have h1 := hsupp _ hne
          have hre : ((z : ℂ) + n).re = z.re + n := by simp [UpperHalfPlane.coe_re]
          rw [hre] at h1
          have hn' : (N : ℝ) < |(n : ℝ)| := by
            rw [hs, Finset.mem_Icc, not_and_or, not_le, not_le] at hn
            rcases hn with h | h
            · have h' : (n : ℝ) < -(N : ℝ) := by exact_mod_cast h
              rw [abs_of_neg (by linarith [Nat.cast_nonneg (α := ℝ) N])]
              linarith
            · have h' : (N : ℝ) < n := by exact_mod_cast h
              exact lt_of_lt_of_le h' (le_abs_self _)
          have h2 : |(n : ℝ)| ≤ |z.re + n| + |z.re| := by
            have := abs_sub (z.re + n) z.re
            simpa using this
          linarith
        exact (hasSum_sum_of_ne_finset_zero hout).unique (hk z)
    -- the pairing as an integral over `B`
    have hDn : ‖D‖ ≤ 2 * L * ‖toL2 k‖ := by
      have e : D = ∑ n ∈ s \ s', glU (transGL (n : ℝ)) (toL2 k) := by
        rw [hD, transSumL, transSumL, ← Finset.sum_sdiff hss]
        abel
      rw [e]
      refine (norm_sum_le _ _).trans ?_
      simp only [LinearIsometryEquiv.norm_map, Finset.sum_const, nsmul_eq_mul]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      have hcard : (s \ s').card = 2 * L := by
        rw [Finset.card_sdiff_of_subset hss, hs, hs', Int.card_Icc, Int.card_Icc]
        omega
      rw [hcard]
      push_cast
      rfl
    have hGB : MemLp ((B N).indicator fun z => G z) 2 volume := (Lp.memLp G).indicator (hBm N).nullMeasurableSet
    have hpair : ⟪G, transSumL k s⟫_ℂ = ⟪hGB.toLp _, D⟫_ℂ := by
      rw [L2.inner_def, L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [hae, hGB.coeFn_toLp] with z e1 e2
      rw [e1, e2]
      by_cases hz : z ∈ B N
      · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]
      · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz]
        simp
    have hnormB : ‖hGB.toLp _‖ = Real.sqrt (∫ z in B N, ‖G z‖ ^ 2) := by
      rw [← Real.sqrt_sq (norm_nonneg _), norm_sq_int]
      congr 1
      rw [← integral_indicator (hBm N)]
      refine integral_congr_ae ?_
      filter_upwards [hGB.coeFn_toLp] with z e2
      rw [e2]
      by_cases hz : z ∈ B N
      · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]
      · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz]
        simp
    rw [hpair]
    calc ‖⟪hGB.toLp _, D⟫_ℂ‖ ≤ ‖hGB.toLp _‖ * ‖D‖ := norm_inner_le_norm _ _
      _ ≤ Real.sqrt (∫ z in B N, ‖G z‖ ^ 2) * (2 * L * ‖toL2 k‖) := by
          rw [hnormB]
          exact mul_le_mul_of_nonneg_left hDn (Real.sqrt_nonneg _)
  -- conclusion
  simp only [sum_pair_trans hα k Ψ]
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hlim : Tendsto (fun N : ℕ => Real.sqrt (∫ z in B N, ‖G z‖ ^ 2) * (2 * L * ‖toL2 k‖)) atTop (𝓝 0) := by
    have h1 := (Real.continuous_sqrt.tendsto 0).comp htail
    rw [Real.sqrt_zero] at h1
    simpa using h1.mul_const (2 * L * ‖toL2 k‖)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun N => norm_nonneg _) ?_
  filter_upwards [eventually_ge_atTop L] with N hN
  exact hbound N hN

end Qschubert
