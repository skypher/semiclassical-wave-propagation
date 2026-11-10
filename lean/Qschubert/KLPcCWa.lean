import Qschubert.KLWaveD
import Qschubert.KLPcG2

/-!
# The critical-weight multiplier theorem, part 1: blocks on shells

If `m(x) = ∫ g(r) cos(r √(x - 1/4)) dr` for `x ≥ 1/4`, then `⟪h, m(-Δ) f⟫ = ∫ g(r) ⟪h, cos(rD) f⟫ dr` (`pair_superpose`). With finite propagation speed
(`finite_speed_inner`) this bounds the block `A_l m(-Δ) A_n` of the shells `A_n = {⌊log X₀⌋ = n}` by the tail of `g` at distance `max(|l - n| - 1, 0)` (`block`).
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set Physicslib4.Spectral Physicslib4.Spectral.Unbounded
open scoped ENNReal InnerProductSpace ComplexConjugate UpperHalfPlane

local notation "L2H'" => Lp ℂ 2 (volume : Measure UpperHalfPlane)

/-- `spec_superpose` for an a.e.-measurable weight. -/
theorem spec_superpose_ae {w : ℝ → ℝ} {f : ℝ → ℝ → ℂ} {F : ℝ → ℂ} {b : ℝ → ℝ}
    (hf : ∀ s, f s ∈ BddMeasurable ℝ) (hF : F ∈ BddMeasurable ℝ)
    (hjm : Measurable (Function.uncurry f)) (hw : AEStronglyMeasurable w volume)
    (hb : ∀ s x, ‖f s x‖ ≤ b s) (hwb : Integrable fun s => |w s| * b s)
    (hrep : ∀ x, ∫ s, (w s : ℂ) * f s x = F x)
    (hc : Continuous fun s => specE.integral (f s)) :
    (Integrable fun s => (w s : ℂ) • specE.integral (f s)) ∧ ∫ s, (w s : ℂ) • specE.integral (f s) = specE.integral F := by
  have hbound : ∀ s, ‖specE.integral (f s)‖ ≤ b s := fun s =>
    (specE.norm_integral_le (hf s)).trans (ciSup_le fun x => hb s x)
  have hwc : AEStronglyMeasurable (fun s => (w s : ℂ)) volume := Complex.continuous_ofReal.comp_aestronglyMeasurable hw
  have hint : Integrable fun s => (w s : ℂ) • specE.integral (f s) := by
    refine hwb.mono' (hwc.smul hc.aestronglyMeasurable) (Eventually.of_forall fun s => ?_)
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hbound s) (abs_nonneg _)
  refine ⟨hint, ?_⟩
  apply ContinuousLinearMap.coe_injective
  refine (ext_inner_map _ _).1 fun u => ?_
  show ⟪(∫ s, (w s : ℂ) • specE.integral (f s)) u, u⟫_ℂ = ⟪specE.integral F u, u⟫_ℂ
  rw [← inner_conj_symm, ← inner_conj_symm (specE.integral F u) u]
  congr 1
  set ν := specE.assoc u with hν
  have e1 : (∫ s, (w s : ℂ) • specE.integral (f s)) u = ∫ s, (w s : ℂ) • specE.integral (f s) u :=
    ContinuousLinearMap.integral_apply hint u
  have hu : Integrable fun s => (w s : ℂ) • specE.integral (f s) u := hint.apply_continuousLinearMap u
  rw [e1, ← integral_inner hu u, specE.inner_integral hF u]
  have hprod : Integrable (Function.uncurry fun s x => (w s : ℂ) * f s x) ((volume : Measure ℝ).prod ν) := by
    refine (hwb.comp_fst ν).mono' ?_ (Eventually.of_forall fun p => ?_)
    · exact (hwc.comp_fst).mul hjm.aestronglyMeasurable
    · simp only [Function.uncurry]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hb _ _) (abs_nonneg _)
  have e2 : ∀ s, ⟪u, (w s : ℂ) • specE.integral (f s) u⟫_ℂ = ∫ x, (w s : ℂ) * f s x ∂ν := fun s => by
    rw [inner_smul_right, specE.inner_integral (hf s) u, integral_const_mul]
  simp_rw [e2]
  rw [integral_integral_swap (f := fun s x => (w s : ℂ) * f s x) hprod]
  exact integral_congr_ae (Eventually.of_forall fun x => hrep x)

lemma norm_chiCD_le (n : ℝ) (r : ℝ) (f : L2H') : ‖(chiCD n r).J f‖ ≤ ‖f‖ := by
  have h : ‖(chiCD n r).J‖ ≤ 1 := by
    refine (specE.norm_integral_le (chiCD n r).g_mem).trans (ciSup_le fun x => ?_)
    show ‖((cD n r x : ℝ) : ℂ)‖ ≤ 1
    rw [Complex.norm_real, Real.norm_eq_abs, cD, abs_mul]
    have h1 := Real.abs_cos_le_one (r * √(yD x))
    have h2 : |cutD n x| ≤ 1 := by rw [abs_of_nonneg (cutD_nonneg n x)]; exact cutD_le_one n x
    calc _ ≤ 1 * 1 := mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  calc _ ≤ ‖(chiCD n r).J‖ * ‖f‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖f‖ := by gcongr
    _ = ‖f‖ := one_mul _

lemma norm_cosDOp_le (r : ℝ) (f : L2H') : ‖cosDOp r f‖ ≤ ‖f‖ := by
  have h : ‖cosDOp r‖ ≤ 1 := by
    refine (specE.norm_integral_le (cosDSymbol_mem r)).trans (ciSup_le fun x => ?_)
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact Real.abs_cos_le_one _
  calc _ ≤ ‖cosDOp r‖ * ‖f‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖f‖ := by gcongr
    _ = ‖f‖ := one_mul _

/-- Cutting a bounded symbol to `[1/4, n]` converges strongly. -/
lemma tendsto_cut {G : ℝ → ℂ} (hG : G ∈ BddMeasurable ℝ) (u : L2H') :
    Tendsto (fun n : ℕ => specE.integral (fun x => G x * ((cutD n x : ℝ) : ℂ)) u) atTop (𝓝 (specE.integral G u)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  obtain ⟨hGm, C, hC⟩ := (mem_bddMeasurable).1 hG
  set ξ : ℕ → ℝ → ℂ := fun n x => G x * ((cutD n x - 1 : ℝ) : ℂ) with hξ
  have h2 : ∀ (n : ℕ) (x : ℝ), ‖((cutD n x - 1 : ℝ) : ℂ)‖ ≤ 1 := fun n x => by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith [cutD_nonneg n x, cutD_le_one n x]
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hbd : ∀ n x, ‖ξ n x‖ ≤ C := fun n x => by
    simp only [hξ, norm_mul]
    calc _ ≤ C * 1 := mul_le_mul (hC x) (h2 n x) (norm_nonneg _) hC0
      _ = C := mul_one C
  have hξm : ∀ n, ξ n ∈ BddMeasurable ℝ := fun n =>
    (mem_bddMeasurable).2 ⟨hGm.mul (Complex.measurable_ofReal.comp ((measurable_cutD n).sub_const 1)), C, hbd n⟩
  have hc : ∀ n : ℕ, (fun x => G x * ((cutD n x : ℝ) : ℂ)) ∈ BddMeasurable ℝ := fun n => by
    refine (mem_bddMeasurable).2 ⟨hGm.mul (Complex.measurable_ofReal.comp (measurable_cutD n)), C, fun x => ?_⟩
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (cutD_nonneg n x)]
    calc _ ≤ C * 1 := mul_le_mul (hC x) (cutD_le_one n x) (cutD_nonneg n x) hC0
      _ = C := mul_one C
  have hop : ∀ n : ℕ, specE.integral (fun x => G x * ((cutD n x : ℝ) : ℂ)) u - specE.integral G u = specE.integral (ξ n) u := fun n => by
    have e : ξ n = (fun x => G x * ((cutD n x : ℝ) : ℂ)) + (-1 : ℂ) • G := by
      funext x
      simp only [hξ, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      push_cast
      ring
    rw [e, specE.integral_add (hc n) ((BddMeasurable ℝ).smul_mem _ hG), specE.integral_smul _ hG]
    simp [sub_eq_add_neg]
  have hsq : Tendsto (fun n : ℕ => ‖specE.integral (fun x => G x * ((cutD n x : ℝ) : ℂ)) u - specE.integral G u‖ ^ 2) atTop (𝓝 0) := by
    simp_rw [hop, norm_sq_integral_apply specE (hξm _)]
    have hpos : ∀ᵐ x ∂(specE.assoc u), 1 / 4 ≤ x := by
      rw [ae_iff]
      refine measure_mono_null (fun x hx => ?_) (assoc_Iio_quarter u)
      simpa using hx
    have := tendsto_integral_of_dominated_convergence (μ := specE.assoc u) (fun _ : ℝ => C ^ 2)
      (F := fun (n : ℕ) x => ‖ξ n x‖ ^ 2) (f := fun _ => 0)
      (fun n => (((mem_bddMeasurable).1 (hξm n)).1.norm.pow_const 2).aestronglyMeasurable) (integrable_const _)
      (fun n => ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hbd n x) 2)
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

/-- **The kernel identity.** -/
theorem pair_superpose {g : ℝ → ℝ} {G : ℝ → ℂ} (hg : Integrable g) (hG : G ∈ BddMeasurable ℝ)
    (hrep : ∀ x, 1 / 4 ≤ x → ∫ r, (g r : ℂ) * ((Real.cos (r * √(yD x)) : ℝ) : ℂ) = G x) (f h : L2H') :
    ⟪h, specE.integral G f⟫_ℂ = ∫ r, (g r : ℂ) * ⟪h, cosDOp r f⟫_ℂ := by
  have hcont : ∀ n : ℝ, Continuous fun r => (chiCD n r).J := fun n =>
    continuous_iff_continuousAt.2 fun s => (hasDerivAt_C_J' n s).continuousAt
  have hgc : AEStronglyMeasurable (fun r => (g r : ℂ)) volume := Complex.continuous_ofReal.comp_aestronglyMeasurable hg.1
  have key : ∀ n : ℕ, ⟪h, specE.integral (fun x => G x * ((cutD n x : ℝ) : ℂ)) f⟫_ℂ = ∫ r, (g r : ℂ) * ⟪h, (chiCD n r).J f⟫_ℂ := fun n => by
    have hcutm : (fun x => ((cutD n x : ℝ) : ℂ)) ∈ BddMeasurable ℝ :=
      memB_of_abs_le (measurable_cutD n) (C := 1) fun x => by rw [abs_of_nonneg (cutD_nonneg n x)]; exact cutD_le_one n x
    have hsup := spec_superpose_ae (w := g) (f := fun s => (chiCD n s).g) (F := fun x => G x * ((cutD n x : ℝ) : ℂ)) (b := fun _ => 1)
      (fun s => (chiCD n s).g_mem) (mul_mem_B hG hcutm)
      (by
        have e : Function.uncurry (fun s => (chiCD n s).g) = fun p : ℝ × ℝ => ((cD n p.1 p.2 : ℝ) : ℂ) := rfl
        rw [e]
        refine Complex.measurable_ofReal.comp ?_
        exact (Real.continuous_cos.measurable.comp (measurable_fst.mul (measurable_sqrt_yD.comp measurable_snd))).mul
          ((measurable_cutD n).comp measurable_snd))
      hg.1
      (fun s x => by
        show ‖((cD n s x : ℝ) : ℂ)‖ ≤ 1
        rw [Complex.norm_real, Real.norm_eq_abs, cD, abs_mul]
        have h1 := Real.abs_cos_le_one (s * √(yD x))
        have h2 : |cutD n x| ≤ 1 := by rw [abs_of_nonneg (cutD_nonneg n x)]; exact cutD_le_one n x
        calc _ ≤ 1 * 1 := mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
          _ = 1 := one_mul 1)
      (by simpa using hg.abs)
      (fun x => by
        show ∫ s, (g s : ℂ) * ((cD n s x : ℝ) : ℂ) = G x * ((cutD n x : ℝ) : ℂ)
        by_cases hx : x ∈ Icc (1 / 4 : ℝ) n
        · have e : ∀ s, (g s : ℂ) * ((cD n s x : ℝ) : ℂ) = (g s : ℂ) * ((Real.cos (s * √(yD x)) : ℝ) : ℂ) := fun s => by
            rw [cD, cutD_of_mem hx, mul_one]
          simp_rw [e]
          rw [hrep x hx.1, cutD_of_mem hx]
          simp
        · have e : ∀ s, (g s : ℂ) * ((cD n s x : ℝ) : ℂ) = 0 := fun s => by
            rw [cD, cutD_of_notMem hx]; simp
          simp_rw [e]
          rw [cutD_of_notMem hx]
          simp)
      (hcont n)
    have hint1 : Integrable fun s => (g s : ℂ) • (chiCD n s).J := hsup.1
    have hi : Integrable fun s => (g s : ℂ) • (chiCD n s).J f := hint1.apply_continuousLinearMap f
    have e1 : specE.integral (fun x => G x * ((cutD n x : ℝ) : ℂ)) = ∫ s, (g s : ℂ) • (chiCD n s).J := hsup.2.symm
    have e2 : (∫ s, (g s : ℂ) • (chiCD n s).J) f = ∫ s, (g s : ℂ) • (chiCD n s).J f :=
      ContinuousLinearMap.integral_apply hint1 f
    rw [e1, e2, ← integral_inner hi h]
    exact integral_congr_ae (Eventually.of_forall fun s => inner_smul_right _ _ _)
  have hl1 : Tendsto (fun n : ℕ => ⟪h, specE.integral (fun x => G x * ((cutD n x : ℝ) : ℂ)) f⟫_ℂ) atTop (𝓝 ⟪h, specE.integral G f⟫_ℂ) :=
    tendsto_const_nhds.inner (tendsto_cut hG f)
  have hl2 : Tendsto (fun n : ℕ => ∫ r, (g r : ℂ) * ⟪h, (chiCD n r).J f⟫_ℂ) atTop (𝓝 (∫ r, (g r : ℂ) * ⟪h, cosDOp r f⟫_ℂ)) := by
    refine tendsto_integral_of_dominated_convergence (fun r => |g r| * (‖h‖ * ‖f‖))
      (fun n => hgc.mul ?_) (hg.abs.mul_const _) (fun n => Eventually.of_forall fun r => ?_)
      (Eventually.of_forall fun r => tendsto_const_nhds.mul (tendsto_const_nhds.inner (tendsto_chiCD r f)))
    · have : Continuous fun r => ⟪h, (chiCD n r).J f⟫_ℂ :=
        continuous_const.inner ((hcont n).clm_apply continuous_const)
      exact this.aestronglyMeasurable
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (norm_chiCD_le n r f) (norm_nonneg _))
  simp_rw [key] at hl1
  exact tendsto_nhds_unique hl1 hl2

/-- **Off-diagonal bound by the tail.** -/
theorem pair_tail {g : ℝ → ℝ} {G : ℝ → ℂ} (hg : Integrable g) (hG : G ∈ BddMeasurable ℝ)
    (hrep : ∀ x, 1 / 4 ≤ x → ∫ r, (g r : ℂ) * ((Real.cos (r * √(yD x)) : ℝ) : ℂ) = G x) {f h : L2H'} {T : ℝ}
    (hvan : ∀ r, |r| < T → ⟪h, cosDOp r f⟫_ℂ = 0) :
    ‖⟪h, specE.integral G f⟫_ℂ‖ ≤ (∫ r in {r : ℝ | T ≤ |r|}, |g r|) * (‖h‖ * ‖f‖) := by
  rw [pair_superpose hg hG hrep f h]
  set S : Set ℝ := {r | T ≤ |r|} with hS
  have e : ∫ r, (g r : ℂ) * ⟪h, cosDOp r f⟫_ℂ = ∫ r in S, (g r : ℂ) * ⟪h, cosDOp r f⟫_ℂ := by
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun r hr => ?_).symm
    have : |r| < T := not_le.1 hr
    simp [hvan r this]
  rw [e, ← integral_mul_const]
  refine norm_integral_le_of_norm_le (hg.abs.integrableOn.mul_const _) (Eventually.of_forall fun r => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (norm_cosDOp_le r f) (norm_nonneg _))

/-- A bounded measurable real multiplier on `ℍ`. -/
structure BM (g : UpperHalfPlane → ℝ) (C : ℝ) : Prop where
  m : Measurable g
  b : ∀ z, |g z| ≤ C

section BM

variable {g : UpperHalfPlane → ℝ} {C : ℝ}

lemma memLp_mulBM (H : BM g C) (u : L2H') : MemLp (fun z : UpperHalfPlane => ((g z : ℝ) : ℂ) * u z) 2 volume :=
  (Lp.memLp u).of_le_mul (c := C) (((Complex.measurable_ofReal.comp H.m).aestronglyMeasurable).mul
    (Lp.aestronglyMeasurable u)) (Eventually.of_forall fun z => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (H.b z) (norm_nonneg _))

/-- Multiplication by a bounded measurable function. -/
noncomputable def mulBM (H : BM g C) : L2H' →L[ℂ] L2H' :=
  LinearMap.mkContinuous
    { toFun := fun u => (memLp_mulBM H u).toLp _
      map_add' := fun u v => by
        apply Lp.ext
        filter_upwards [(memLp_mulBM H (u + v)).coeFn_toLp, (memLp_mulBM H u).coeFn_toLp, (memLp_mulBM H v).coeFn_toLp,
          Lp.coeFn_add u v, Lp.coeFn_add ((memLp_mulBM H u).toLp _) ((memLp_mulBM H v).toLp _)] with z h1 h2 h3 h4 h5
        rw [h1, h5]; simp only [Pi.add_apply]; rw [h2, h3, h4]; simp only [Pi.add_apply]; ring
      map_smul' := fun c u => by
        apply Lp.ext
        filter_upwards [(memLp_mulBM H (c • u)).coeFn_toLp, (memLp_mulBM H u).coeFn_toLp,
          Lp.coeFn_smul c u, Lp.coeFn_smul c ((memLp_mulBM H u).toLp _)] with z h1 h2 h3 h4
        simp only [RingHom.id_apply]
        rw [h1, h4]; simp only [Pi.smul_apply, smul_eq_mul]; rw [h2, h3]; simp only [Pi.smul_apply, smul_eq_mul]; ring }
    C (fun u => by
      show ‖(memLp_mulBM H u).toLp _‖ ≤ C * ‖u‖
      refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
      filter_upwards [(memLp_mulBM H u).coeFn_toLp] with z hz
      rw [hz, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (H.b z) (norm_nonneg _))

lemma coe_mulBM (H : BM g C) (u : L2H') : mulBM H u =ᵐ[volume] fun z => ((g z : ℝ) : ℂ) * u z :=
  (memLp_mulBM H u).coeFn_toLp

lemma norm_mulBM_le (H : BM g C) (u : L2H') : ‖mulBM H u‖ ≤ C * ‖u‖ := by
  refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
  filter_upwards [coe_mulBM H u] with z hz
  rw [hz, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (H.b z) (norm_nonneg _)

lemma inner_mulBM_left (H : BM g C) (x y : L2H') : ⟪mulBM H x, y⟫_ℂ = ⟪x, mulBM H y⟫_ℂ := by
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coe_mulBM H x, coe_mulBM H y] with z h1 h2
  rw [h1, h2]
  simp only [RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring

end BM

/-- The shell `A_n = {n ≤ log X₀ < n + 1}`. -/
def shell (n : ℕ) : Set UpperHalfPlane := {z | ⌊psiF (z : ℂ)⌋₊ = n}

lemma measurableSet_shell (n : ℕ) : MeasurableSet (shell n) :=
  (Nat.measurable_floor.comp measurable_psi_coe) (measurableSet_singleton n)

lemma mem_shell {n : ℕ} {z : UpperHalfPlane} (h : z ∈ shell n) : (n : ℝ) ≤ psiF (z : ℂ) ∧ psiF (z : ℂ) < n + 1 :=
  (Nat.floor_eq_iff (psiF_nonneg z.im_pos)).1 h

/-- The indicator of a shell. -/
noncomputable def chiN (n : ℕ) : UpperHalfPlane → ℝ := (shell n).indicator 1

lemma bm_chiN (n : ℕ) : BM (chiN n) 1 :=
  ⟨measurable_one.indicator (measurableSet_shell n), fun z => by
    unfold chiN
    by_cases hz : z ∈ shell n <;> simp [hz]⟩

/-- The cut to a shell. -/
noncomputable def cutN (n : ℕ) : L2H' →L[ℂ] L2H' := mulBM (bm_chiN n)

lemma cutN_ae (n : ℕ) (u : L2H') : cutN n u =ᵐ[volume] fun z => ((chiN n z : ℝ) : ℂ) * u z := coe_mulBM _ u

lemma cutN_supp (n : ℕ) (u : L2H') : ∀ᵐ z, cutN n u z ≠ 0 → z ∈ shell n := by
  filter_upwards [cutN_ae n u] with z hz h0
  by_contra hn
  apply h0
  rw [hz]
  simp [chiN, hn]

lemma norm_cutN_le (n : ℕ) (u : L2H') : ‖cutN n u‖ ≤ ‖u‖ := by
  have h := norm_mulBM_le (bm_chiN n) u
  rw [one_mul] at h
  exact h

lemma cutN_idem (n : ℕ) (u : L2H') : cutN n (cutN n u) = cutN n u := by
  apply Lp.ext
  filter_upwards [cutN_ae n (cutN n u), cutN_ae n u] with z h1 h2
  rw [h1, h2, ← mul_assoc]
  by_cases hz : z ∈ shell n <;> simp [chiN, hz]

/-- The gap between two shells. -/
noncomputable def Tgap (l n : ℕ) : ℝ := max (|(l : ℝ) - n| - 1) 0

lemma Tgap_nonneg (l n : ℕ) : 0 ≤ Tgap l n := le_max_right _ _

/-- **The block of `m(-Δ)` between two shells.** -/
theorem block {g : ℝ → ℝ} {G : ℝ → ℂ} (hg : Integrable g) (hG : G ∈ BddMeasurable ℝ)
    (hrep : ∀ x, 1 / 4 ≤ x → ∫ r, (g r : ℂ) * ((Real.cos (r * √(yD x)) : ℝ) : ℂ) = G x) (l n : ℕ) (u : L2H') :
    ‖cutN l (specE.integral G (cutN n u))‖ ≤ (∫ r in {r : ℝ | Tgap l n ≤ |r|}, |g r|) * ‖cutN n u‖ := by
  set f := cutN n u with hf
  set v := specE.integral G f with hv
  set h := cutN l v with hh
  have hfs : ∀ᵐ z : UpperHalfPlane, f z ≠ 0 → z ∈ shell n := cutN_supp n u
  have hhs : ∀ᵐ z : UpperHalfPlane, h z ≠ 0 → z ∈ shell l := cutN_supp l v
  have hvan : ∀ r, |r| < Tgap l n → ⟪h, cosDOp r f⟫_ℂ = 0 := fun r hr => by
    have hr' : |r| < |(l : ℝ) - n| - 1 := by
      rcases lt_max_iff.1 hr with h1 | h1
      · exact h1
      · exact absurd h1 (not_lt.2 (abs_nonneg r))
    rcases lt_trichotomy l n with hln | hln | hln
    · have hlt : (l : ℝ) < n := by exact_mod_cast hln
      have e0 : |(l : ℝ) - n| = n - l := by rw [abs_of_neg (sub_neg.2 hlt)]; ring
      rw [e0] at hr'
      refine (finite_speed_inner (a := l + 1) (b := n) (by linarith) h f ?_ ?_).2
      · filter_upwards [hhs] with z hz h0
        exact (mem_shell (hz h0)).2.le
      · filter_upwards [hfs] with z hz h0
        exact (mem_shell (hz h0)).1
    · subst hln
      simp only [sub_self, abs_zero] at hr'
      linarith [abs_nonneg r]
    · have hlt : (n : ℝ) < l := by exact_mod_cast hln
      have e0 : |(l : ℝ) - n| = l - n := abs_of_pos (sub_pos.2 hlt)
      rw [e0] at hr'
      refine (finite_speed_inner (a := n + 1) (b := l) (by linarith) f h ?_ ?_).1
      · filter_upwards [hfs] with z hz h0
        exact (mem_shell (hz h0)).2.le
      · filter_upwards [hhs] with z hz h0
        exact (mem_shell (hz h0)).1
  have hp := pair_tail hg hG hrep hvan
  rw [← hv] at hp
  have hi : ⟪h, v⟫_ℂ = ⟪h, h⟫_ℂ := by
    have e : ⟪h, h⟫_ℂ = ⟪h, cutN l v⟫_ℂ := rfl
    rw [e]
    have e2 : ⟪h, cutN l v⟫_ℂ = ⟪cutN l h, v⟫_ℂ := (inner_mulBM_left (bm_chiN l) h v).symm
    rw [e2, hh, cutN_idem]
  have e4 : ‖⟪h, h⟫_ℂ‖ = ‖h‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K, norm_pow]
    simp
  rw [hi, e4] at hp
  set t := ∫ r in {r : ℝ | Tgap l n ≤ |r|}, |g r| with ht
  by_cases h0 : ‖h‖ = 0
  · rw [h0]
    have ht0 : 0 ≤ t := setIntegral_nonneg (measurableSet_le measurable_const continuous_abs.measurable) fun _ _ => abs_nonneg _
    positivity
  · have hpos : 0 < ‖h‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    have e3 : ‖h‖ * ‖h‖ ≤ ‖h‖ * (t * ‖f‖) := by nlinarith
    exact le_of_mul_le_mul_left e3 hpos

end Qschubert
