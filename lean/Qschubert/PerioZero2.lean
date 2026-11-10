import Qschubert.PerioZero

/-!
# A test function with vanishing periodization: `e^{-αΛ} k` is orthogonal to periodic functions

Stage X of the plan for Proposition `ev:mod` (`lean/BLUEPRINT.md`). Let `k` be a test function with
`Σ_{n ∈ ℤ} k(z + n) = 0` on `ℍ`, `b = e^{-αΛ} k`, and let `E` be measurable with `E(z + n) = E(z)` for integers `n`,
such that `E 1_{0 ≤ x < 1} ∈ L²(ℍ)` and `b E ∈ L¹(ℍ)`. Then `∫_ℍ b E dν = 0` (`integral_expCut_mul_periodic`).

Proof: `∫_ℍ b E = Σ_n ∫_{n ≤ x < n+1} b E = Σ_n ⟪Ψ, U_n b⟫` with `Ψ = conj(E) 1_{0 ≤ x < 1}` (the translations
preserve the measure), and the symmetric partial sums tend to `0` by `tendsto_sum_pair_trans`.
-/

namespace Qschubert

open MeasureTheory Filter Topology UpperHalfPlane Set Physicslib4.Spectral Physicslib4.Spectral.Unbounded
open scoped MatrixGroups InnerProductSpace ComplexConjugate

local notation "L2H" => Lp ℂ 2 (volume : Measure ℍ)

/-- The strips `n ≤ x < n + 1`. -/
def stripZ (n : ℤ) : Set ℍ := {z : ℍ | ⌊z.re⌋ = n}

lemma measurableSet_stripZ (n : ℤ) : MeasurableSet (stripZ n) :=
  (Int.measurable_floor.comp UpperHalfPlane.continuous_re.measurable) (measurableSet_singleton n)

lemma re_transGL_smul (s : ℝ) (z : ℍ) : (transGL s • z).re = z.re + s := by
  have h := congrArg Complex.re (coe_transGL_smul s z)
  simpa [UpperHalfPlane.coe_re] using h

lemma mem_stripZ_transGL (n : ℤ) (z : ℍ) : transGL (n : ℝ) • z ∈ stripZ n ↔ z ∈ stripZ 0 := by
  simp only [stripZ, Set.mem_ofPred_eq, re_transGL_smul, Int.floor_add_intCast]
  omega

lemma tendsto_Icc_neg_atTop : Tendsto (fun N : ℕ => Finset.Icc (-(N : ℤ)) N) atTop atTop := by
  refine tendsto_atTop_finset_of_monotone (fun M N hMN => ?_) fun n => ?_
  · have h : (M : ℤ) ≤ N := by exact_mod_cast hMN
    exact Finset.Icc_subset_Icc (by linarith) h
  · refine ⟨n.natAbs, Finset.mem_Icc.2 ⟨?_, ?_⟩⟩ <;> omega

/-- **`e^{-αΛ} k` is orthogonal to periodic functions.** -/
theorem integral_expCut_mul_periodic {α : ℝ} (hα : 0 < α) (k : testFn)
    (hk : ∀ z : ℍ, HasSum (fun n : ℤ => (k : ℂ → ℂ) ((z : ℂ) + n)) 0) {E : ℍ → ℂ}
    (hEper : ∀ (n : ℤ) (z : ℍ), E (transGL (n : ℝ) • z) = E z)
    (hEL : MemLp (fun z : ℍ => conj ((stripZ 0).indicator E z)) 2 volume)
    (hint : Integrable fun z : ℍ => ((expCut α hα).J (toL2 k) : L2H) z * E z) :
    ∫ z : ℍ, ((expCut α hα).J (toL2 k) : L2H) z * E z = 0 := by
  set b : L2H := (expCut α hα).J (toL2 k) with hb
  set Ψ : L2H := hEL.toLp _ with hΨ
  have hcover : (⋃ n, stripZ n) = univ := by
    ext z
    simp [stripZ]
  have hdisj : Pairwise (Function.onFun Disjoint stripZ) := fun i j hij => by
    rw [Function.onFun, Set.disjoint_left]
    intro z hi hj
    exact hij (hi.symm.trans hj)
  have hsum := hasSum_integral_iUnion measurableSet_stripZ hdisj (f := fun z : ℍ => b z * E z)
    (by rw [hcover]; exact hint.integrableOn)
  rw [hcover, setIntegral_univ] at hsum
  -- each strip integral is a pairing
  have hterm : ∀ n : ℤ, ∫ z in stripZ n, b z * E z = ⟪Ψ, glU (transGL (n : ℝ)) b⟫_ℂ := by
    intro n
    have hmp := measurePreserving_gl (transGL (n : ℝ))
    have hme : MeasurableEmbedding fun z : ℍ => transGL (n : ℝ) • z :=
      (MeasurableEquiv.smul (transGL (n : ℝ))).measurableEmbedding
    have hpre : (fun z : ℍ => transGL (n : ℝ) • z) ⁻¹' stripZ n = stripZ 0 := by
      ext z
      exact mem_stripZ_transGL n z
    have h1 := hmp.setIntegral_preimage_emb hme (fun z : ℍ => b z * E z) (stripZ n)
    rw [hpre] at h1
    rw [← h1, L2.inner_def, ← integral_indicator (measurableSet_stripZ 0)]
    refine integral_congr_ae ?_
    filter_upwards [hEL.coeFn_toLp, glUL_ae (transGL (n : ℝ)) b] with z e1 e2
    rw [hΨ, e1, glU_apply, e2, RCLike.inner_apply, Complex.conj_conj]
    by_cases hz : z ∈ stripZ 0
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz, hEper]
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, mul_zero]
  simp only [hterm] at hsum
  have h1 := hsum.comp tendsto_Icc_neg_atTop
  have h2 := tendsto_sum_pair_trans hα k hk Ψ
  exact tendsto_nhds_unique h1 h2

end Qschubert
