import Qschubert.KLSpectral
import Qschubert.KLKernel
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The kernel of multiplication by `z` in the KL picture (step (X) of `lem:fc`)

Part 1 (bounds and a general adjoint identity):
* `abs_besselKi_le_zero`: `|K_{iν}(z)| ≤ K_0(z)` for `z > 0`;
* `integrableOn_besselKi_zero_sq`: `K_0² ∈ L¹(0, ∞)` (its integral is `π²/4 ≠ 0`);
* `kerM1` (`= ∫ K_{iν}K_{iν'} dz = π²/(4 cosh p cosh q)`) with `kerM1 ≤ π²/(2 cosh πν')`;
* `norm_klInvA_le_K0`: `|ψ_a(z)| ≤ ‖a‖₁ K_0(z)`; `norm_klInvA_le_exp`: `|ψ_a(z)| ≤ ½‖Â‖₁ e^{-z}`;
* `integral_conj_klInvA_mul`: `∫_0^∞ conj(ψ_a) g/z dz = ∫ conj(a) KL(g) dν` whenever `K_0 |g|/z ∈ L¹(0, ∞)`.
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set
open scoped ENNReal

lemma integrableOn_exp_neg_cosh {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun t => Real.exp (-(z * Real.cosh t))) (Ioi 0) := by
  have h := (integrable_kInt 0 hz).norm
  simp only [norm_kInt_zero] at h
  exact h.integrableOn

/-- `|K_{iν}(z)| ≤ K_0(z)` for `z > 0`. -/
lemma abs_besselKi_le_zero {z : ℝ} (hz : 0 < z) (ν : ℝ) : |besselKi ν z| ≤ besselKi 0 z := by
  rw [← Real.norm_eq_abs]
  have h := norm_integral_le_of_norm_le (integrableOn_exp_neg_cosh hz)
    (Eventually.of_forall fun t => (by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_cos_le_one _)) :
      ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
        ‖Real.exp (-(z * Real.cosh t)) * Real.cos (ν * t)‖ ≤ Real.exp (-(z * Real.cosh t)))
  refine h.trans (le_of_eq ?_)
  unfold besselKi
  congr 1; funext t; simp

lemma besselKi_zero_nonneg {z : ℝ} (hz : 0 < z) : 0 ≤ besselKi 0 z :=
  (abs_nonneg _).trans (abs_besselKi_le_zero hz 0)

/-- `∫ K_{iν}K_{iν'} dz`. -/
noncomputable def kerM1 (ν ν' : ℝ) : ℝ :=
  Real.pi ^ 2 / (4 * (Real.cosh (Real.pi * ((ν + ν') / 2)) * Real.cosh (Real.pi * ((ν - ν') / 2))))

lemma kerM1_pos (ν ν' : ℝ) : 0 < kerM1 ν ν' := by
  unfold kerM1; have := Real.pi_pos; positivity

lemma kerM1_symm (ν ν' : ℝ) : kerM1 ν ν' = kerM1 ν' ν := by
  unfold kerM1
  rw [add_comm ν ν', show (ν - ν') / 2 = -((ν' - ν) / 2) by ring, mul_neg, Real.cosh_neg]

lemma continuous_M1 : Continuous fun q : ℝ × ℝ => kerM1 q.1 q.2 := by
  unfold kerM1
  refine continuous_const.div (by fun_prop) (fun q => ?_)
  have := Real.cosh_pos (Real.pi * ((q.1 + q.2) / 2)); have := Real.cosh_pos (Real.pi * ((q.1 - q.2) / 2))
  positivity

/-- `cosh p cosh q ≥ cosh(p - q)/2`, so `kerM1 ν ν' ≤ π²/(2 cosh πν')`. -/
lemma kerM1_le (ν ν' : ℝ) : kerM1 ν ν' ≤ Real.pi ^ 2 / (2 * Real.cosh (Real.pi * ν')) := by
  unfold kerM1
  have hp := Real.pi_pos
  set a := Real.pi * ((ν + ν') / 2); set b := Real.pi * ((ν - ν') / 2)
  have hab : Real.cosh (Real.pi * ν') = Real.cosh (a - b) := by congr 1; simp only [a, b]; ring
  have hprod : Real.cosh (a - b) ≤ 2 * (Real.cosh a * Real.cosh b) := by
    rw [Real.cosh_sub]
    have h1 := Real.cosh_pos a; have h2 := Real.cosh_pos b
    have hs : (Real.sinh a * Real.sinh b) ^ 2 ≤ (Real.cosh a * Real.cosh b) ^ 2 := by
      rw [mul_pow, mul_pow, Real.cosh_sq a, Real.cosh_sq b]
      nlinarith [sq_nonneg (Real.sinh a), sq_nonneg (Real.sinh b)]
    have h3 := (abs_le_of_sq_le_sq' hs (by positivity)).1
    linarith
  rw [hab]
  have hc := Real.cosh_pos (a - b)
  rw [div_le_div_iff₀ (by have := Real.cosh_pos a; have := Real.cosh_pos b; positivity) (by positivity)]
  nlinarith [sq_nonneg Real.pi]

lemma integral_besselKi_mul_eq_M1 (ν ν' : ℝ) : ∫ z in Ioi 0, besselKi ν z * besselKi ν' z = kerM1 ν ν' :=
  integral_besselKi_mul ν ν'

/-- `K_0² ∈ L¹(0, ∞)`: its integral is `π²/4 ≠ 0`. -/
lemma integrableOn_besselKi_zero_sq : IntegrableOn (fun z => besselKi 0 z * besselKi 0 z) (Ioi 0) := by
  by_contra h
  have e := integral_besselKi_mul_eq_M1 0 0
  rw [integral_undef h] at e
  exact (kerM1_pos 0 0).ne' e.symm

lemma integrableOn_besselKi_mul (ν ν' : ℝ) : IntegrableOn (fun z => besselKi ν z * besselKi ν' z) (Ioi 0) := by
  by_contra h
  have e := integral_besselKi_mul_eq_M1 ν ν'
  rw [integral_undef h] at e
  exact (kerM1_pos ν ν').ne' e.symm

/-- `|ψ_a(z)| ≤ ‖a‖₁ K_0(z)`. -/
lemma norm_klInvA_le_K0 {a : ℝ → ℂ} (ha : IsKTest a) {z : ℝ} (hz : 0 < z) :
    ‖klInvA a z‖ ≤ (∫ ν, ‖a ν‖) * besselKi 0 z := by
  rw [klInvA, ← integral_mul_const]
  refine norm_integral_le_of_norm_le (ha.integrable.norm.mul_const _) (Eventually.of_forall fun ν => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (abs_besselKi_le_zero hz ν) (norm_nonneg _)

/-- `|ψ_a(z)| ≤ ½ ‖Â‖₁ e^{-z}`. -/
lemma norm_klInvA_le_exp {a : ℝ → ℂ} (ha : IsKTest a) {z : ℝ} (hz : 0 < z) :
    ‖klInvA a z‖ ≤ (1 / 2) * (∫ t, ‖hatA a t‖) * Real.exp (-z) := by
  rw [klInvA_eq ha hz, norm_mul]
  have h : ‖∫ t, ((Real.exp (-(z * Real.cosh t)) : ℝ) : ℂ) * hatA a t‖ ≤ ∫ t, Real.exp (-z) * ‖hatA a t‖ := by
    refine norm_integral_le_of_norm_le ((integrable_hatA ha).norm.const_mul _) (Eventually.of_forall fun t => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (norm_nonneg _)
    nlinarith [Real.one_le_cosh t]
  rw [MeasureTheory.integral_const_mul] at h
  have h2 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  rw [h2]
  have hA : 0 ≤ ∫ t, ‖hatA a t‖ := integral_nonneg fun t => norm_nonneg _
  nlinarith [Real.exp_pos (-z)]

/-- **General adjoint identity**: `∫_0^∞ conj(ψ_a) g/z dz = ∫ conj(a) KL(g) dν` when `K_0 |g|/z ∈ L¹`. -/
theorem integral_conj_klInvA_mul {a g : ℝ → ℂ} (ha : IsKTest a)
    (hg : AEStronglyMeasurable g (volume.restrict (Ioi (0 : ℝ))))
    (hK : IntegrableOn (fun z => besselKi 0 z * ‖g z / z‖) (Ioi 0)) :
    ∫ z in Ioi 0, (starRingEnd ℂ) (klInvA a z) * (g z / z) = ∫ ν, (starRingEnd ℂ) (a ν) * klT g ν := by
  set μz : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  set H : ℝ × ℝ → ℂ := fun q => (starRingEnd ℂ) (a q.1) * ((besselKi q.1 q.2 : ℝ) : ℂ) * (g q.2 / q.2)
  have hHm : AEStronglyMeasurable H ((volume : Measure ℝ).prod μz) := by
    refine ((ha.continuous.star.comp continuous_fst).aestronglyMeasurable.mul
      (Complex.continuous_ofReal.measurable.comp measurable_besselKi).aestronglyMeasurable).mul ?_
    have hgz : AEStronglyMeasurable (fun z : ℝ => g z / z) μz := by
      exact (hg.mul (Complex.continuous_ofReal.measurable.inv.aestronglyMeasurable)).congr
        (Eventually.of_forall fun z => by simp [div_eq_mul_inv])
    exact hgz.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
  have hdom : Integrable (fun q : ℝ × ℝ => ‖a q.1‖ * (besselKi 0 q.2 * ‖g q.2 / q.2‖))
      ((volume : Measure ℝ).prod μz) := ha.integrable.norm.mul_prod hK
  have hHi : Integrable H ((volume : Measure ℝ).prod μz) := by
    refine hdom.mono' hHm ?_
    have hpos : ∀ᵐ q ∂((volume : Measure ℝ).prod μz), 0 < q.2 := by
      have := (ae_restrict_mem measurableSet_Ioi : ∀ᵐ z ∂μz, z ∈ Ioi (0 : ℝ))
      exact (Measure.quasiMeasurePreserving_snd).ae this
    filter_upwards [hpos] with q hq
    simp only [H, norm_mul, Complex.norm_real, Real.norm_eq_abs, RCLike.norm_conj]
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (abs_besselKi_le_zero hq q.1)
      (norm_nonneg _)) (norm_nonneg _)
  have e1 := integral_prod H hHi
  have e2 := integral_prod_symm H hHi
  -- `∫ν ∫z H = ∫ conj(a) KL g`
  have hR : ∫ ν, ∫ z, H (ν, z) ∂μz = ∫ ν, (starRingEnd ℂ) (a ν) * klT g ν := by
    refine integral_congr_ae (Eventually.of_forall fun ν => ?_)
    simp only [H, klT, mul_assoc]
    rw [MeasureTheory.integral_const_mul]
  -- `∫z ∫ν H = ∫ conj(ψ_a) g/z`
  have hL : ∫ z, ∫ ν, H (ν, z) ∂volume ∂μz = ∫ z in Ioi 0, (starRingEnd ℂ) (klInvA a z) * (g z / z) := by
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [H]
    rw [MeasureTheory.integral_mul_const, klInvA, ← integral_conj]
    congr 2; funext ν; simp [map_mul]
  rw [← hL, ← e2, e1, hR]

/-! ### Part 2: polarized Parseval `⟨KL f, KL g⟩_w = ⟨f, g⟩_{dz/z}` for a test function `f` -/

/-- The measure `dz/z` on `(0, ∞)`. -/
noncomputable def muZ : Measure ℝ := (volume.restrict (Ioi 0)).withDensity fun z => ENNReal.ofReal z⁻¹

lemma measurable_inv_dens : Measurable fun z : ℝ => ENNReal.ofReal z⁻¹ :=
  ENNReal.measurable_ofReal.comp measurable_inv

lemma inner_toLp_muZ {a b : ℝ → ℂ} (ha : MemLp a 2 muZ) (hb : MemLp b 2 muZ) :
    inner ℂ (ha.toLp a) (hb.toLp b) = ∫ z in Ioi 0, (starRingEnd ℂ) (a z) * b z / z := by
  rw [L2.inner_def]
  have e : ∫ z, inner ℂ ((ha.toLp a : Lp ℂ 2 muZ) z) ((hb.toLp b : Lp ℂ 2 muZ) z) ∂muZ
      = ∫ z, (starRingEnd ℂ) (a z) * b z ∂muZ := by
    refine integral_congr_ae ?_
    filter_upwards [ha.coeFn_toLp, hb.coeFn_toLp] with z h1 h2
    rw [h1, h2, RCLike.inner_apply']
  rw [e, muZ, integral_withDensity_eq_integral_toReal_smul measurable_inv_dens
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine setIntegral_congr_fun measurableSet_Ioi (fun z hz => ?_)
  rw [ENNReal.toReal_ofReal (inv_nonneg.2 (le_of_lt hz)), Complex.real_smul]
  push_cast; ring

lemma inner_toLp_wNu {a b : ℝ → ℂ} (ha : MemLp a 2 wNu) (hb : MemLp b 2 wNu) :
    inner ℂ (ha.toLp a) (hb.toLp b) = ∫ ν in Ioi 0, (klW ν : ℂ) * ((starRingEnd ℂ) (a ν) * b ν) := by
  rw [L2.inner_def]
  have e : ∫ ν, inner ℂ ((ha.toLp a : Lp ℂ 2 wNu) ν) ((hb.toLp b : Lp ℂ 2 wNu) ν) ∂wNu
      = ∫ ν, (starRingEnd ℂ) (a ν) * b ν ∂wNu := by
    refine integral_congr_ae ?_
    filter_upwards [ha.coeFn_toLp, hb.coeFn_toLp] with z h1 h2
    rw [h1, h2, RCLike.inner_apply']
  rw [e, wNu, integral_withDensity_eq_integral_toReal_smul measurable_klW_dens
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine setIntegral_congr_fun measurableSet_Ioi (fun ν hν => ?_)
  rw [ENNReal.toReal_ofReal (klW_nonneg (le_of_lt hν)), Complex.real_smul]

lemma memLp_muZ_of {g : ℝ → ℂ} (hgm : AEStronglyMeasurable g (volume.restrict (Ioi (0 : ℝ))))
    (hi : IntegrableOn (fun z => ‖g z‖ ^ 2 / z) (Ioi 0)) : MemLp g 2 muZ := by
  have hm : AEStronglyMeasurable g muZ := hgm.mono_ac (withDensity_absolutelyContinuous _ _)
  refine (memLp_two_iff_integrable_sq_norm hm).2 ?_
  rw [muZ, integrable_withDensity_iff_integrable_smul' measurable_inv_dens
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine IntegrableOn.congr_fun hi (fun z hz => ?_) measurableSet_Ioi
  rw [ENNReal.toReal_ofReal (inv_nonneg.2 (le_of_lt hz)), smul_eq_mul]; ring

lemma memLp_wNu_of {G : ℝ → ℂ} (hGm : AEStronglyMeasurable G (volume.restrict (Ioi (0 : ℝ))))
    (hi : IntegrableOn (fun ν => klW ν * ‖G ν‖ ^ 2) (Ioi 0)) : MemLp G 2 wNu := by
  have hm : AEStronglyMeasurable G wNu := hGm.mono_ac (withDensity_absolutelyContinuous _ _)
  refine (memLp_two_iff_integrable_sq_norm hm).2 ?_
  rw [wNu, integrable_withDensity_iff_integrable_smul' measurable_klW_dens
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine IntegrableOn.congr_fun hi (fun ν hν => ?_) measurableSet_Ioi
  rw [ENNReal.toReal_ofReal (klW_nonneg (le_of_lt hν)), smul_eq_mul]

lemma integrableOn_test_sq_div {f : ℝ → ℂ} (hf : IsKTest f) :
    IntegrableOn (fun z => ‖f z‖ ^ 2 / z) (Ioi 0) := by
  have hi : Integrable fun z => ‖f z‖ * ‖(z : ℂ)⁻¹ * f z‖ :=
    (hf.continuous.norm.mul hf.inv_mul.continuous.norm).integrable_of_hasCompactSupport hf.compact.norm.mul_right
  refine IntegrableOn.congr_fun hi.integrableOn (fun z hz => ?_) measurableSet_Ioi
  simp only [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (show (0 : ℝ) < z from hz)]
  ring

lemma aestronglyMeasurable_klT {g : ℝ → ℂ} (hgm : AEStronglyMeasurable g (volume.restrict (Ioi (0 : ℝ)))) :
    AEStronglyMeasurable (klT g) volume := by
  have hgz : AEStronglyMeasurable (fun z : ℝ => g z / z) (volume.restrict (Ioi (0 : ℝ))) :=
    (hgm.mul (Complex.continuous_ofReal.measurable.inv.aestronglyMeasurable)).congr
      (Eventually.of_forall fun z => by simp [div_eq_mul_inv])
  have hF : AEStronglyMeasurable (fun q : ℝ × ℝ => ((besselKi q.1 q.2 : ℝ) : ℂ) * (g q.2 / q.2))
      ((volume : Measure ℝ).prod (volume.restrict (Ioi (0 : ℝ)))) :=
    (Complex.continuous_ofReal.measurable.comp measurable_besselKi).aestronglyMeasurable.mul
      (hgz.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)
  exact hF.integral_prod_right'

lemma isKTest_zero : IsKTest (0 : ℝ → ℂ) :=
  ⟨contDiff_const, HasCompactSupport.zero, by simp [tsupport_zero]⟩

lemma IsKTest.add {f g : ℝ → ℂ} (hf : IsKTest f) (hg : IsKTest g) : IsKTest (f + g) :=
  ⟨hf.smooth.add hg.smooth, hf.compact.add hg.compact,
    ((closure_mono (Function.support_add f g)).trans closure_union.le).trans (union_subset hf.pos hg.pos)⟩

/-- The KL test functions as a subspace of `L²(w dν)`. -/
noncomputable def testSubW : Submodule ℂ (Lp ℂ 2 wNu) where
  carrier := testSetW
  add_mem' := by
    rintro _ _ ⟨h1, hh1, rfl⟩ ⟨h2, hh2, rfl⟩
    exact ⟨h1 + h2, hh1.add hh2, by rw [MemLp.toLp_add]⟩
  zero_mem' := ⟨0, isKTest_zero, by rw [MemLp.toLp_zero]⟩
  smul_mem' := by
    rintro c _ ⟨h, hh, rfl⟩
    refine ⟨fun x => c * h x, hh.mul_smooth (φ := fun _ => c) contDiff_const, ?_⟩
    rw [← MemLp.toLp_const_smul]; rfl

lemma testSubW_dense : testSubW.topologicalClosure = ⊤ := by
  rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro G hG
  rw [Lp.eq_zero_iff_ae_eq_zero]
  refine ae_eq_zero_of_forall_test (Lp.memLp G) (fun h hh => ?_)
  have h0 := (Submodule.mem_orthogonal _ _).1 hG _ (⟨h, hh, rfl⟩ : (memLp_wNu hh).toLp h ∈ testSubW)
  rw [L2.inner_def] at h0
  rw [← h0]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_wNu hh).coeFn_toLp] with ν h1
  rw [h1, RCLike.inner_apply']

/-- Every `G ∈ L²(w dν)` is a limit of KL test functions. -/
lemma exists_seq_test_tendsto (G : Lp ℂ 2 wNu) :
    ∃ h : ℕ → ℝ → ℂ, ∃ hh : ∀ n, IsKTest (h n),
      Tendsto (fun n => (memLp_wNu (hh n)).toLp (h n)) atTop (𝓝 G) := by
  have hG : G ∈ closure (testSubW : Set (Lp ℂ 2 wNu)) := by
    rw [← Submodule.topologicalClosure_coe, testSubW_dense]; trivial
  obtain ⟨x, hx, hlim⟩ := mem_closure_iff_seq_limit.1 hG
  have hch : ∀ n, ∃ h : ℝ → ℂ, ∃ hh : IsKTest h, x n = (memLp_wNu hh).toLp h := fun n => hx n
  choose h hh he using hch
  exact ⟨h, hh, by simpa only [← he] using hlim⟩

lemma integral_conj_aW_mul {h : ℝ → ℂ} (hh : IsKTest h) (G : ℝ → ℂ) :
    ∫ ν, (starRingEnd ℂ) (aW h ν) * G ν = ∫ ν in Ioi 0, (klW ν : ℂ) * ((starRingEnd ℂ) (h ν) * G ν) := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi (0 : ℝ)) (fun ν hν => by
    simp [aW, hh.eq_zero_of_nonpos (not_lt.1 hν)])]
  refine setIntegral_congr_fun measurableSet_Ioi (fun ν _ => ?_)
  simp only [aW, map_mul, Complex.conj_ofReal]; ring

lemma integral_conj_mul_aW {h : ℝ → ℂ} (hh : IsKTest h) (G : ℝ → ℂ) :
    ∫ ν, (starRingEnd ℂ) (G ν) * aW h ν = ∫ ν in Ioi 0, (klW ν : ℂ) * ((starRingEnd ℂ) (G ν) * h ν) := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi (0 : ℝ)) (fun ν hν => by
    simp [aW, hh.eq_zero_of_nonpos (not_lt.1 hν)])]
  refine setIntegral_congr_fun measurableSet_Ioi (fun ν _ => ?_)
  simp only [aW]; ring

lemma inner_self_eq_ofReal {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] {x : E} {y : F}
    (h : inner ℂ x x = inner ℂ y y) : ‖x‖ = ‖y‖ := by
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h2 : ‖x‖ ^ 2 = ‖y‖ ^ 2 := by exact_mod_cast h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2

/-- **Polarized KL Parseval** for a test function `f` and a function `g ∈ L²(dz/z)` with
`K_0|g|/z ∈ L¹` and `KL g ∈ L²(w)`. -/
theorem kl_polar {f g : ℝ → ℂ} (hf : IsKTest f) (hgm : AEStronglyMeasurable g (volume.restrict (Ioi (0 : ℝ))))
    (hg2 : IntegrableOn (fun z => ‖g z‖ ^ 2 / z) (Ioi 0))
    (hK : IntegrableOn (fun z => besselKi 0 z * ‖g z / z‖) (Ioi 0))
    (hKg : IntegrableOn (fun ν => klW ν * ‖klT g ν‖ ^ 2) (Ioi 0)) :
    ∫ ν in Ioi 0, (klW ν : ℂ) * ((starRingEnd ℂ) (klT f ν) * klT g ν)
      = ∫ z in Ioi 0, (starRingEnd ℂ) (f z) * g z / z := by
  have mF : MemLp f 2 muZ := memLp_muZ_of hf.continuous.aestronglyMeasurable (integrableOn_test_sq_div hf)
  have mG : MemLp g 2 muZ := memLp_muZ_of hgm hg2
  have mKF : MemLp (klT f) 2 wNu :=
    memLp_wNu_of (aestronglyMeasurable_klT hf.continuous.aestronglyMeasurable).restrict (integrableOn_klW_mul hf)
  have mKG : MemLp (klT g) 2 wNu := memLp_wNu_of (aestronglyMeasurable_klT hgm).restrict hKg
  obtain ⟨h, hh, hlim⟩ := exists_seq_test_tendsto (mKF.toLp (klT f))
  have ha : ∀ n, IsKTest (aW (h n)) := fun n => isKTest_aW (hh n)
  have mΨ : ∀ n, MemLp (klInvA (aW (h n))) 2 muZ := fun n =>
    memLp_muZ_of ((continuousOn_klInvA (ha n)).aestronglyMeasurable measurableSet_Ioi) (rev_parseval_amp (ha n)).1
  -- (1) `⟨Ψ_n, g⟩ = ⟨h_n, KL g⟩`
  have h1 : ∀ n, inner ℂ ((mΨ n).toLp (klInvA (aW (h n)))) (mG.toLp g)
      = inner ℂ ((memLp_wNu (hh n)).toLp (h n)) (mKG.toLp (klT g)) := by
    intro n
    rw [inner_toLp_muZ, inner_toLp_wNu, ← integral_conj_aW_mul (hh n),
      ← integral_conj_klInvA_mul (ha n) hgm hK]
    refine setIntegral_congr_fun measurableSet_Ioi (fun z _ => ?_)
    ring
  -- (2) `‖Ψ_n - f‖ = ‖h_n - KL f‖`
  have hPP : ∀ n, inner ℂ (mF.toLp f) ((mΨ n).toLp (klInvA (aW (h n))))
      = inner ℂ (mKF.toLp (klT f)) ((memLp_wNu (hh n)).toLp (h n)) := by
    intro n
    rw [inner_toLp_muZ, inner_toLp_wNu, ← integral_conj_mul_aW (hh n), integral_conj_klT_mul hf (ha n)]
    refine setIntegral_congr_fun measurableSet_Ioi (fun z _ => ?_)
    simp only [map_div₀, Complex.conj_ofReal]; ring
  have hPP' : ∀ n, inner ℂ ((mΨ n).toLp (klInvA (aW (h n)))) (mF.toLp f)
      = inner ℂ ((memLp_wNu (hh n)).toLp (h n)) (mKF.toLp (klT f)) := by
    intro n
    rw [← inner_conj_symm, hPP n, inner_conj_symm]
  have hΨΨ : ∀ n, inner ℂ ((mΨ n).toLp (klInvA (aW (h n)))) ((mΨ n).toLp (klInvA (aW (h n))))
      = inner ℂ ((memLp_wNu (hh n)).toLp (h n)) ((memLp_wNu (hh n)).toLp (h n)) := by
    intro n
    rw [inner_toLp_muZ, inner_toLp_wNu]
    have e1 : ∫ z in Ioi 0, (starRingEnd ℂ) (klInvA (aW (h n)) z) * klInvA (aW (h n)) z / z
        = ((∫ z in Ioi 0, ‖klInvA (aW (h n)) z‖ ^ 2 / z : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      refine setIntegral_congr_fun measurableSet_Ioi (fun z _ => ?_)
      rw [Complex.conj_mul']; push_cast; ring
    have e2 : ∫ ν in Ioi 0, (klW ν : ℂ) * ((starRingEnd ℂ) (h n ν) * h n ν)
        = ((∫ ν in Ioi 0, klW ν * ‖h n ν‖ ^ 2 : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      refine setIntegral_congr_fun measurableSet_Ioi (fun ν _ => ?_)
      rw [Complex.conj_mul']; push_cast; ring
    rw [e1, e2, show aW (h n) = fun ν => (klW ν : ℂ) * h n ν from rfl, rev_parseval (hh n)]
  have hFF : inner ℂ (mF.toLp f) (mF.toLp f) = inner ℂ (mKF.toLp (klT f)) (mKF.toLp (klT f)) := by
    rw [inner_toLp_muZ, inner_toLp_wNu]
    have e1 : ∫ z in Ioi 0, (starRingEnd ℂ) (f z) * f z / z = ((∫ z in Ioi 0, ‖f z‖ ^ 2 / z : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      refine setIntegral_congr_fun measurableSet_Ioi (fun z _ => ?_)
      rw [Complex.conj_mul']; push_cast; ring
    have e2 : ∫ ν in Ioi 0, (klW ν : ℂ) * ((starRingEnd ℂ) (klT f ν) * klT f ν)
        = ((∫ ν in Ioi 0, 2 / Real.pi ^ 2 * ν * Real.sinh (Real.pi * ν) * ‖klT f ν‖ ^ 2 : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      refine setIntegral_congr_fun measurableSet_Ioi (fun ν _ => ?_)
      rw [Complex.conj_mul', klW]; push_cast; ring
    rw [e1, e2, kl_parseval hf]
  have h2 : ∀ n, ‖(mΨ n).toLp (klInvA (aW (h n))) - mF.toLp f‖
      = ‖(memLp_wNu (hh n)).toLp (h n) - mKF.toLp (klT f)‖ := by
    intro n
    refine inner_self_eq_ofReal ?_
    rw [inner_sub_sub_self, inner_sub_sub_self, hΨΨ n, hFF, hPP n, hPP' n]
  -- (3) limits
  have hΨ : Tendsto (fun n => (mΨ n).toLp (klInvA (aW (h n)))) atTop (𝓝 (mF.toLp f)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp_rw [h2]
    exact (tendsto_iff_norm_sub_tendsto_zero.1 hlim)
  have l1 := hΨ.inner (𝕜 := ℂ) (tendsto_const_nhds (x := mG.toLp g))
  have l2 := hlim.inner (𝕜 := ℂ) (tendsto_const_nhds (x := mKG.toLp (klT g)))
  simp_rw [h1] at l1
  have := tendsto_nhds_unique l2 l1
  rw [inner_toLp_wNu, inner_toLp_muZ] at this
  exact this

/-! ### Part 3: the kernel of `z`, `KL(z f) = K₁(KL f)` for test functions `f` -/

/-- `(K₁ G)(ν) = ∫_0^∞ M₁(ν, ν') G(ν') w(ν') dν'`. -/
noncomputable def K1op (G : ℝ → ℂ) (ν : ℝ) : ℂ := ∫ ν' in Ioi 0, (kerM1 ν ν' : ℂ) * ((klW ν' : ℂ) * G ν')

lemma inv_cosh_le_two_exp {x : ℝ} : (Real.cosh x)⁻¹ ≤ 2 * Real.exp (-x) := by
  have h1 : Real.exp x / 2 ≤ Real.cosh x := by rw [Real.cosh_eq]; linarith [Real.exp_pos (-x)]
  calc (Real.cosh x)⁻¹ ≤ (Real.exp x / 2)⁻¹ := inv_anti₀ (by positivity) h1
    _ = 2 * Real.exp (-x) := by rw [inv_div, Real.exp_neg, div_eq_mul_inv]

lemma integrableOn_mul_exp_neg : IntegrableOn (fun ν : ℝ => ν * Real.exp (-ν)) (Ioi 0) := by
  have h := Real.GammaIntegral_convergent (s := 2) (by norm_num)
  refine h.congr_fun (fun x _ => ?_) measurableSet_Ioi
  simp only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]; ring

lemma continuous_inv_cosh : Continuous fun ν : ℝ => (Real.cosh (Real.pi * ν))⁻¹ :=
  (Real.continuous_cosh.comp (continuous_const.mul continuous_id)).inv₀ (fun ν => (Real.cosh_pos _).ne')

lemma continuous_klW : Continuous klW := by unfold klW; fun_prop

lemma klW_mul_inv_cosh_sq_le {ν : ℝ} (hν : 0 < ν) :
    klW ν * ((Real.cosh (Real.pi * ν))⁻¹) ^ 2 ≤ 4 / Real.pi ^ 2 * (ν * Real.exp (-ν)) := by
  have hp := Real.pi_pos
  have hc := Real.cosh_pos (Real.pi * ν)
  have hs : Real.sinh (Real.pi * ν) ≤ Real.cosh (Real.pi * ν) := (Real.sinh_lt_cosh _).le
  have hs0 : 0 ≤ Real.sinh (Real.pi * ν) := Real.sinh_nonneg_iff.2 (by positivity)
  have he : Real.exp (-(Real.pi * ν)) ≤ Real.exp (-ν) := Real.exp_le_exp.2 (by nlinarith [Real.pi_gt_three])
  have hi := inv_cosh_le_two_exp (x := Real.pi * ν)
  have hci : 0 < (Real.cosh (Real.pi * ν))⁻¹ := inv_pos.2 hc
  unfold klW
  calc 2 / Real.pi ^ 2 * ν * Real.sinh (Real.pi * ν) * ((Real.cosh (Real.pi * ν))⁻¹) ^ 2
      ≤ 2 / Real.pi ^ 2 * ν * Real.cosh (Real.pi * ν) * ((Real.cosh (Real.pi * ν))⁻¹) ^ 2 := by
        gcongr
    _ = 2 / Real.pi ^ 2 * ν * (Real.cosh (Real.pi * ν))⁻¹ := by field_simp
    _ ≤ 2 / Real.pi ^ 2 * ν * (2 * Real.exp (-ν)) := by
        gcongr; exact hi.trans (by gcongr)
    _ = 4 / Real.pi ^ 2 * (ν * Real.exp (-ν)) := by ring

lemma integrableOn_klW_inv_cosh_sq :
    IntegrableOn (fun ν => klW ν * ((Real.cosh (Real.pi * ν))⁻¹) ^ 2) (Ioi 0) := by
  refine (integrableOn_mul_exp_neg.const_mul (4 / Real.pi ^ 2)).mono'
    ((continuous_klW.mul (continuous_inv_cosh.pow 2)).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with ν hν
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (klW_nonneg (le_of_lt hν)) (sq_nonneg _))]
  exact klW_mul_inv_cosh_sq_le hν

lemma memLp_inv_cosh_wNu : MemLp (fun ν => (((Real.cosh (Real.pi * ν))⁻¹ : ℝ) : ℂ)) 2 wNu := by
  refine memLp_wNu_of (Complex.continuous_ofReal.comp continuous_inv_cosh).aestronglyMeasurable ?_
  refine integrableOn_klW_inv_cosh_sq.congr_fun (fun ν _ => ?_) measurableSet_Ioi
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos (Real.cosh_pos _)]

lemma integrableOn_klW_mul_inv_cosh {G : ℝ → ℂ} (hG : MemLp G 2 wNu) :
    IntegrableOn (fun ν => klW ν * (‖G ν‖ * (Real.cosh (Real.pi * ν))⁻¹)) (Ioi 0) := by
  have h := (hG.integrable_mul memLp_inv_cosh_wNu).norm
  rw [wNu, integrable_withDensity_iff_integrable_smul' measurable_klW_dens
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)] at h
  refine IntegrableOn.congr_fun h (fun ν hν => ?_) measurableSet_Ioi
  simp only [Pi.mul_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_inv,
    abs_of_pos (Real.cosh_pos _), smul_eq_mul, ENNReal.toReal_ofReal (klW_nonneg (le_of_lt hν))]

lemma kerM1_le' (ν ν' : ℝ) : kerM1 ν ν' ≤ Real.pi ^ 2 / (2 * Real.cosh (Real.pi * ν)) := by
  rw [kerM1_symm]; exact kerM1_le ν' ν

lemma norm_K1op_integrand_le {G : ℝ → ℂ} {ν ν' : ℝ} (hν' : 0 < ν') :
    ‖(kerM1 ν ν' : ℂ) * ((klW ν' : ℂ) * G ν')‖
      ≤ Real.pi ^ 2 / 2 * (klW ν' * (‖G ν'‖ * (Real.cosh (Real.pi * ν'))⁻¹)) := by
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (kerM1_pos _ _), abs_of_nonneg (klW_nonneg (le_of_lt hν'))]
  have h := kerM1_le ν ν'
  have hc := Real.cosh_pos (Real.pi * ν')
  have hw := klW_nonneg (le_of_lt hν')
  calc kerM1 ν ν' * (klW ν' * ‖G ν'‖) ≤ Real.pi ^ 2 / (2 * Real.cosh (Real.pi * ν')) * (klW ν' * ‖G ν'‖) :=
        mul_le_mul_of_nonneg_right h (by positivity)
    _ = Real.pi ^ 2 / 2 * (klW ν' * (‖G ν'‖ * (Real.cosh (Real.pi * ν'))⁻¹)) := by field_simp

lemma integrableOn_K1op_integrand {G : ℝ → ℂ} (hG : MemLp G 2 wNu) (hGm : AEStronglyMeasurable G (volume.restrict (Ioi (0 : ℝ))))
    (ν : ℝ) : IntegrableOn (fun ν' => (kerM1 ν ν' : ℂ) * ((klW ν' : ℂ) * G ν')) (Ioi 0) := by
  refine ((integrableOn_klW_mul_inv_cosh hG).const_mul (Real.pi ^ 2 / 2)).mono' ?_ ?_
  · exact ((Complex.continuous_ofReal.comp (continuous_M1.comp (continuous_const.prodMk continuous_id))).aestronglyMeasurable.mul
      ((Complex.continuous_ofReal.comp continuous_klW).aestronglyMeasurable.mul hGm))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with ν' hν'
    exact norm_K1op_integrand_le hν'

lemma norm_K1op_le {G : ℝ → ℂ} (hG : MemLp G 2 wNu) (ν : ℝ) :
    ‖K1op G ν‖ ≤ Real.pi ^ 2 / 2 * ∫ ν' in Ioi 0, klW ν' * (‖G ν'‖ * (Real.cosh (Real.pi * ν'))⁻¹) := by
  rw [K1op, ← MeasureTheory.integral_const_mul]
  refine norm_integral_le_of_norm_le ((integrableOn_klW_mul_inv_cosh hG).const_mul _) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with ν' hν'
  exact norm_K1op_integrand_le hν'

lemma aestronglyMeasurable_K1op {G : ℝ → ℂ} (hGm : AEStronglyMeasurable G (volume.restrict (Ioi (0 : ℝ)))) :
    AEStronglyMeasurable (K1op G) volume := by
  have hF : AEStronglyMeasurable (fun q : ℝ × ℝ => (kerM1 q.1 q.2 : ℂ) * ((klW q.2 : ℂ) * G q.2))
      ((volume : Measure ℝ).prod (volume.restrict (Ioi (0 : ℝ)))) :=
    (Complex.continuous_ofReal.comp continuous_M1).aestronglyMeasurable.mul
      (((Complex.continuous_ofReal.comp continuous_klW).aestronglyMeasurable.mul hGm).comp_quasiMeasurePreserving
        Measure.quasiMeasurePreserving_snd)
  exact hF.integral_prod_right'

/-- `KL(z ψ_{wh}) = K₁ h`. -/
lemma klT_mul_klInvA {h : ℝ → ℂ} (hh : IsKTest h) (ν : ℝ) :
    klT (fun z => (z : ℂ) * klInvA (aW h) z) ν = K1op h ν := by
  have ha := isKTest_aW hh
  have e1 : klT (fun z => (z : ℂ) * klInvA (aW h) z) ν
      = ∫ z in Ioi 0, ((besselKi ν z : ℝ) : ℂ) * klInvA (aW h) z := by
    unfold klT
    refine setIntegral_congr_fun measurableSet_Ioi (fun z hz => ?_)
    have : (z : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hz)
    simp only; field_simp
  set μz : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  set H : ℝ × ℝ → ℂ := fun q => ((besselKi ν q.1 : ℝ) : ℂ) * (aW h q.2 * ((besselKi q.2 q.1 : ℝ) : ℂ))
  have hHm : AEStronglyMeasurable H (μz.prod volume) := by
    have m1 : Measurable fun q : ℝ × ℝ => besselKi ν q.1 :=
      measurable_besselKi.comp (measurable_const.prodMk measurable_fst)
    have m2 : Measurable fun q : ℝ × ℝ => besselKi q.2 q.1 :=
      measurable_besselKi.comp (measurable_snd.prodMk measurable_fst)
    exact ((Complex.measurable_ofReal.comp m1).aestronglyMeasurable).mul
      ((ha.continuous.comp continuous_snd).aestronglyMeasurable.mul (Complex.measurable_ofReal.comp m2).aestronglyMeasurable)
  have hdom : Integrable (fun q : ℝ × ℝ => (besselKi 0 q.1 * besselKi 0 q.1) * ‖aW h q.2‖) (μz.prod volume) :=
    integrableOn_besselKi_zero_sq.mul_prod ha.integrable.norm
  have hHi : Integrable H (μz.prod volume) := by
    refine hdom.mono' hHm ?_
    have hpos : ∀ᵐ q ∂(μz.prod (volume : Measure ℝ)), 0 < q.1 := by
      have := (ae_restrict_mem measurableSet_Ioi : ∀ᵐ z ∂μz, z ∈ Ioi (0 : ℝ))
      exact (Measure.quasiMeasurePreserving_fst (μ := μz) (ν := (volume : Measure ℝ))).ae this
    filter_upwards [hpos] with q hq
    simp only [H, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have k1 := abs_besselKi_le_zero hq ν
    have k2 := abs_besselKi_le_zero hq q.2
    have k0 := besselKi_zero_nonneg hq
    calc |besselKi ν q.1| * (‖aW h q.2‖ * |besselKi q.2 q.1|)
        ≤ besselKi 0 q.1 * (‖aW h q.2‖ * besselKi 0 q.1) := by gcongr
      _ = besselKi 0 q.1 * besselKi 0 q.1 * ‖aW h q.2‖ := by ring
  have e2 := integral_prod H hHi
  have e3 := integral_prod_symm H hHi
  have hL : ∫ z, ∫ ν', H (z, ν') ∂volume ∂μz = ∫ z in Ioi 0, ((besselKi ν z : ℝ) : ℂ) * klInvA (aW h) z := by
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [H, klInvA]
    rw [MeasureTheory.integral_const_mul]
  have hR : ∫ ν', ∫ z, H (z, ν') ∂μz = ∫ ν', aW h ν' * (kerM1 ν ν' : ℂ) := by
    refine integral_congr_ae (Eventually.of_forall fun ν' => ?_)
    simp only [H]
    have : ∫ z in Ioi 0, ((besselKi ν z : ℝ) : ℂ) * (aW h ν' * ((besselKi ν' z : ℝ) : ℂ))
        = aW h ν' * ∫ z in Ioi 0, (((besselKi ν z * besselKi ν' z : ℝ)) : ℂ) := by
      rw [← MeasureTheory.integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi (fun z _ => ?_)
      push_cast; ring
    rw [this, integral_complex_ofReal, integral_besselKi_mul_eq_M1]
  rw [e1, ← hL, ← e2, e3, hR, K1op]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi (0 : ℝ)) (fun ν' hν' => by
    simp [aW, hh.eq_zero_of_nonpos (not_lt.1 hν')])]
  refine setIntegral_congr_fun measurableSet_Ioi (fun ν' _ => ?_)
  simp only [aW]; ring

/-! ### Part 4: `KL(z f) = K₁(KL f)` a.e. on `(0, ∞)` -/

lemma norm_klT_le_of_test {f : ℝ → ℂ} (hf : IsKTest f) : ∃ C, ∀ ν, ‖klT f ν‖ ≤ C := by
  obtain ⟨c, hc, hcle⟩ := hf.exists_pos_le
  set M : ℝ := (1 / 2) * ∫ t, ‖kInt 0 c t‖
  have hM : 0 ≤ M := mul_nonneg (by norm_num) (integral_nonneg fun t => norm_nonneg _)
  have hi : IntegrableOn (fun z : ℝ => ‖f z / z‖) (Ioi 0) :=
    (hf.inv_mul.integrable.norm.integrableOn).congr_fun (fun z _ => by simp only [div_eq_inv_mul])
      measurableSet_Ioi
  refine ⟨M * ∫ z in Ioi 0, ‖f z / z‖, fun ν => ?_⟩
  unfold klT
  rw [← MeasureTheory.integral_const_mul]
  refine norm_integral_le_of_norm_le (hi.const_mul M) (Eventually.of_forall fun z => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  by_cases h0 : f z = 0
  · simp [h0]
  · exact mul_le_mul_of_nonneg_right (abs_besselKi_le hc (hcle z h0)) (norm_nonneg _)

/-- A bounded measurable `g` with `∫ w conj(g) h = 0` for all test `h` vanishes a.e. on `(0, ∞)`. -/
lemma ae_eq_zero_of_forall_test_bdd {g : ℝ → ℂ} (hgm : AEStronglyMeasurable g volume) {C : ℝ}
    (hb : ∀ ν, ‖g ν‖ ≤ C)
    (h0 : ∀ h : ℝ → ℂ, IsKTest h → ∫ ν in Ioi 0, (klW ν : ℂ) * ((starRingEnd ℂ) (g ν) * h ν) = 0) :
    ∀ᵐ ν ∂(volume.restrict (Ioi (0 : ℝ))), g ν = 0 := by
  set f : ℝ → ℂ := fun ν => (klW ν : ℂ) * g ν
  have hloc : LocallyIntegrableOn f (Ioi 0) volume := by
    refine LocallyIntegrable.locallyIntegrableOn ?_ _
    rw [locallyIntegrable_iff]
    intro K hK
    obtain ⟨W, hW⟩ := hK.exists_bound_of_continuousOn continuous_klW.continuousOn
    refine Measure.integrableOn_of_bounded hK.measure_lt_top.ne
      ((Complex.continuous_ofReal.comp continuous_klW).aestronglyMeasurable.mul hgm) (M := W * C) ?_
    filter_upwards [ae_restrict_mem hK.measurableSet] with ν hν
    rw [norm_mul, Complex.norm_real]
    exact mul_le_mul (hW ν hν) (hb ν) (norm_nonneg _) ((norm_nonneg _).trans (hW ν hν))
  have h1 := isOpen_Ioi.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc (fun r r_diff r_supp r_sub => by
    have hr : IsKTest fun ν => (r ν : ℂ) :=
      ⟨Complex.ofRealCLM.contDiff.comp r_diff, r_supp.comp_left Complex.ofReal_zero,
        (closure_mono (Function.support_comp_subset Complex.ofReal_zero r)).trans r_sub⟩
    have hz := h0 _ hr
    have e1 : ∫ ν, r ν • f ν = ∫ ν in Ioi 0, r ν • f ν :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero (fun ν hν => by
        rw [image_eq_zero_of_notMem_tsupport (fun h => hν (r_sub h)), zero_smul])).symm
    have e2 : ∫ ν in Ioi 0, r ν • f ν
        = (starRingEnd ℂ) (∫ ν in Ioi 0, (klW ν : ℂ) * ((starRingEnd ℂ) (g ν) * (r ν : ℂ))) := by
      rw [← integral_conj]
      refine setIntegral_congr_fun measurableSet_Ioi (fun ν _ => ?_)
      simp only [f, map_mul, Complex.conj_ofReal, Complex.conj_conj, Complex.real_smul]; ring
    rw [e1, e2, hz, map_zero])
  rw [ae_restrict_iff' measurableSet_Ioi]
  filter_upwards [h1] with ν hν hν0
  have := hν hν0
  simp only [f, mul_eq_zero, Complex.ofReal_eq_zero, (klW_pos hν0).ne', false_or] at this
  exact this

lemma norm_K1op_le_cosh {G : ℝ → ℂ} (hG : IntegrableOn (fun ν => klW ν * ‖G ν‖) (Ioi 0)) (ν : ℝ) :
    ‖K1op G ν‖ ≤ Real.pi ^ 2 / 2 * (Real.cosh (Real.pi * ν))⁻¹ * ∫ ν' in Ioi 0, klW ν' * ‖G ν'‖ := by
  rw [K1op, ← MeasureTheory.integral_const_mul]
  refine norm_integral_le_of_norm_le (hG.const_mul _) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with ν' hν'
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (kerM1_pos _ _), abs_of_nonneg (klW_nonneg (le_of_lt hν'))]
  have h := kerM1_le' ν ν'
  have hc := Real.cosh_pos (Real.pi * ν)
  calc kerM1 ν ν' * (klW ν' * ‖G ν'‖) ≤ Real.pi ^ 2 / (2 * Real.cosh (Real.pi * ν)) * (klW ν' * ‖G ν'‖) :=
        mul_le_mul_of_nonneg_right h (mul_nonneg (klW_nonneg (le_of_lt hν')) (norm_nonneg _))
    _ = Real.pi ^ 2 / 2 * (Real.cosh (Real.pi * ν))⁻¹ * (klW ν' * ‖G ν'‖) := by field_simp

lemma integrableOn_klW_norm_test {h : ℝ → ℂ} (hh : IsKTest h) :
    IntegrableOn (fun ν => klW ν * ‖h ν‖) (Ioi 0) :=
  ((continuous_klW.mul hh.continuous.norm).integrable_of_hasCompactSupport hh.compact.norm.mul_left).integrableOn

lemma measurable_besselKi_zero : Measurable fun z : ℝ => besselKi 0 z :=
  measurable_besselKi.comp (measurable_const.prodMk measurable_id)

/-- **The kernel of multiplication by `z` in the KL picture**: for `f` smooth with compact support in
`(0, ∞)`, `KL(z f)(ν) = ∫_0^∞ M₁(ν, ν') KL(f)(ν') w(ν') dν'` for a.e. `ν > 0`. -/
theorem klT_mul_id_ae {f : ℝ → ℂ} (hf : IsKTest f) :
    ∀ᵐ ν ∂(volume.restrict (Ioi (0 : ℝ))), klT (fun z => (z : ℂ) * f z) ν = K1op (klT f) ν := by
  have hzf := hf.mul_id
  have hFm0 := aestronglyMeasurable_klT hf.continuous.aestronglyMeasurable
  have hFm : AEStronglyMeasurable (klT f) (volume.restrict (Ioi (0 : ℝ))) := hFm0.restrict
  have mKF : MemLp (klT f) 2 wNu := memLp_wNu_of hFm (integrableOn_klW_mul hf)
  obtain ⟨C1, hC1⟩ := norm_klT_le_of_test hzf
  set C2 : ℝ := Real.pi ^ 2 / 2 * ∫ ν' in Ioi 0, klW ν' * (‖klT f ν'‖ * (Real.cosh (Real.pi * ν'))⁻¹)
  set D : ℝ → ℂ := fun ν => klT (fun z => (z : ℂ) * f z) ν - K1op (klT f) ν
  have hDm : AEStronglyMeasurable D volume :=
    (aestronglyMeasurable_klT hzf.continuous.aestronglyMeasurable).sub (aestronglyMeasurable_K1op hFm)
  have hDb : ∀ ν, ‖D ν‖ ≤ C1 + C2 := fun ν =>
    (norm_sub_le _ _).trans (add_le_add (hC1 ν) (norm_K1op_le mKF ν))
  have key : ∀ h : ℝ → ℂ, IsKTest h →
      ∫ ν in Ioi 0, (klW ν : ℂ) * ((starRingEnd ℂ) (klT (fun z => (z : ℂ) * f z) ν) * h ν)
        = ∫ ν in Ioi 0, (klW ν : ℂ) * ((starRingEnd ℂ) (K1op (klT f) ν) * h ν) := by
    intro h hh
    have ha := isKTest_aW hh
    set ψ := klInvA (aW h)
    -- A = ∫ conj(f) ψ
    have hA : ∫ ν in Ioi 0, (klW ν : ℂ) * ((starRingEnd ℂ) (klT (fun z => (z : ℂ) * f z) ν) * h ν)
        = ∫ z in Ioi 0, (starRingEnd ℂ) (f z) * ψ z := by
      rw [← integral_conj_mul_aW hh, integral_conj_klT_mul hzf ha]
      refine setIntegral_congr_fun measurableSet_Ioi (fun z hz => ?_)
      have : (z : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hz)
      simp only [map_div₀, map_mul, Complex.conj_ofReal]; field_simp
      rfl
    -- kl_polar with g = z ψ
    have hgm : AEStronglyMeasurable (fun z : ℝ => (z : ℂ) * ψ z) (volume.restrict (Ioi (0 : ℝ))) :=
      (Complex.continuous_ofReal.continuousOn.mul (continuousOn_klInvA ha)).aestronglyMeasurable measurableSet_Ioi
    have hψm : AEStronglyMeasurable ψ (volume.restrict (Ioi (0 : ℝ))) :=
      (continuousOn_klInvA ha).aestronglyMeasurable measurableSet_Ioi
    set cA : ℝ := (1 / 2) * ∫ t, ‖hatA (aW h) t‖
    have hg2 : IntegrableOn (fun z : ℝ => ‖(z : ℂ) * ψ z‖ ^ 2 / z) (Ioi 0) := by
      refine (integrableOn_mul_exp_neg.const_mul (cA ^ 2)).mono' ?_ ?_
      · exact ((hgm.norm.pow 2).mul (measurable_inv.aestronglyMeasurable)).congr
          (Eventually.of_forall fun z => by simp [div_eq_mul_inv])
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
        have hz0 : (0 : ℝ) < z := hz
        have hb := norm_klInvA_le_exp ha hz0
        have hcA : 0 ≤ cA := mul_nonneg (by norm_num) (integral_nonneg fun t => norm_nonneg _)
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hz0]
        have hψ0 := norm_nonneg (ψ z)
        have he : Real.exp (-z) ^ 2 ≤ Real.exp (-z) := by
          rw [sq]; exact mul_le_of_le_one_left (Real.exp_pos _).le (Real.exp_le_one_iff.2 (by linarith))
        calc (z * ‖ψ z‖) ^ 2 / z = z * ‖ψ z‖ ^ 2 := by field_simp
          _ ≤ z * (cA * Real.exp (-z)) ^ 2 := by gcongr
          _ = cA ^ 2 * (z * Real.exp (-z) ^ 2) := by ring
          _ ≤ cA ^ 2 * (z * Real.exp (-z)) := by gcongr
    have hK : IntegrableOn (fun z : ℝ => besselKi 0 z * ‖(z : ℂ) * ψ z / z‖) (Ioi 0) := by
      refine (integrableOn_besselKi_zero_sq.const_mul (∫ ν, ‖aW h ν‖)).mono' ?_ ?_
      · exact (measurable_besselKi_zero.aestronglyMeasurable.restrict).mul
          ((hgm.mul (Complex.continuous_ofReal.measurable.inv.aestronglyMeasurable)).norm.congr
            (Eventually.of_forall fun z => by simp [div_eq_mul_inv]))
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
        have hz0 : (0 : ℝ) < z := hz
        have hzc : (z : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hz0)
        have k0 := besselKi_zero_nonneg hz0
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg k0 (norm_nonneg _)),
          show (z : ℂ) * ψ z / z = ψ z by field_simp]
        calc besselKi 0 z * ‖ψ z‖ ≤ besselKi 0 z * ((∫ ν, ‖aW h ν‖) * besselKi 0 z) :=
              mul_le_mul_of_nonneg_left (norm_klInvA_le_K0 ha hz0) k0
          _ = (∫ ν, ‖aW h ν‖) * (besselKi 0 z * besselKi 0 z) := by ring
    have hKg : IntegrableOn (fun ν => klW ν * ‖klT (fun z : ℝ => (z : ℂ) * ψ z) ν‖ ^ 2) (Ioi 0) := by
      set c3 : ℝ := Real.pi ^ 2 / 2 * ∫ ν' in Ioi 0, klW ν' * ‖h ν'‖
      refine (integrableOn_klW_inv_cosh_sq.const_mul (c3 ^ 2)).mono' ?_ ?_
      · exact (continuous_klW.aestronglyMeasurable.restrict).mul
          ((aestronglyMeasurable_klT hgm).restrict.norm.pow 2)
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with ν hν
        have hν0 : (0 : ℝ) < ν := hν
        have hb := norm_K1op_le_cosh (integrableOn_klW_norm_test hh) ν
        rw [← klT_mul_klInvA hh ν] at hb
        have hw := klW_nonneg hν0.le
        have hc := inv_pos.2 (Real.cosh_pos (Real.pi * ν))
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hw (sq_nonneg _))]
        have hk0 := norm_nonneg (klT (fun z : ℝ => (z : ℂ) * ψ z) ν)
        calc klW ν * ‖klT (fun z : ℝ => (z : ℂ) * ψ z) ν‖ ^ 2
            ≤ klW ν * (c3 * (Real.cosh (Real.pi * ν))⁻¹) ^ 2 := by
              gcongr; calc _ ≤ _ := hb
                _ = c3 * (Real.cosh (Real.pi * ν))⁻¹ := by simp only [c3]; ring
          _ = c3 ^ 2 * (klW ν * ((Real.cosh (Real.pi * ν))⁻¹) ^ 2) := by ring
    have hP := kl_polar hf hgm hg2 hK hKg
    have hP' : ∫ ν in Ioi 0, (klW ν : ℂ) * ((starRingEnd ℂ) (klT f ν) * K1op h ν)
        = ∫ z in Ioi 0, (starRingEnd ℂ) (f z) * ψ z := by
      rw [show K1op h = klT (fun z : ℝ => (z : ℂ) * ψ z) from funext fun ν => (klT_mul_klInvA hh ν).symm, hP]
      refine setIntegral_congr_fun measurableSet_Ioi (fun z hz => ?_)
      have : (z : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hz)
      field_simp
    -- Fubini: `∫ w conj(F) K₁h = ∫ w conj(K₁ F) h`
    have hB : ∫ ν in Ioi 0, (klW ν : ℂ) * ((starRingEnd ℂ) (klT f ν) * K1op h ν)
        = ∫ ν in Ioi 0, (klW ν : ℂ) * ((starRingEnd ℂ) (K1op (klT f) ν) * h ν) := by
      set μz : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
      set H : ℝ × ℝ → ℂ := fun q => (klW q.1 : ℂ) * ((starRingEnd ℂ) (klT f q.1) *
        ((kerM1 q.1 q.2 : ℂ) * ((klW q.2 : ℂ) * h q.2)))
      have hHm : AEStronglyMeasurable H (μz.prod μz) := by
        refine ((Complex.continuous_ofReal.comp (continuous_klW.comp continuous_fst)).aestronglyMeasurable).mul
          ((hFm.star.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst).mul
            ((Complex.continuous_ofReal.comp continuous_M1).aestronglyMeasurable.mul
              ((Complex.continuous_ofReal.comp (continuous_klW.comp continuous_snd)).mul
                (hh.continuous.comp continuous_snd)).aestronglyMeasurable))
      have hdom : Integrable (fun q : ℝ × ℝ => (Real.pi ^ 2 / 2) *
          ((klW q.1 * (‖klT f q.1‖ * (Real.cosh (Real.pi * q.1))⁻¹)) * (klW q.2 * ‖h q.2‖))) (μz.prod μz) :=
        ((integrableOn_klW_mul_inv_cosh mKF).mul_prod (integrableOn_klW_norm_test hh)).const_mul _
      have hHi : Integrable H (μz.prod μz) := by
        refine hdom.mono' hHm ?_
        have hp1 : ∀ᵐ q ∂(μz.prod μz), 0 < q.1 := by
          have := (ae_restrict_mem measurableSet_Ioi : ∀ᵐ z ∂μz, z ∈ Ioi (0 : ℝ))
          exact (Measure.quasiMeasurePreserving_fst (μ := μz) (ν := μz)).ae this
        have hp2 : ∀ᵐ q ∂(μz.prod μz), 0 < q.2 := by
          have := (ae_restrict_mem measurableSet_Ioi : ∀ᵐ z ∂μz, z ∈ Ioi (0 : ℝ))
          exact (Measure.quasiMeasurePreserving_snd (μ := μz) (ν := μz)).ae this
        filter_upwards [hp1, hp2] with q hq1 hq2
        simp only [H, norm_mul, Complex.norm_real, Real.norm_eq_abs, RCLike.norm_conj,
          abs_of_nonneg (klW_nonneg hq1.le), abs_of_nonneg (klW_nonneg hq2.le), abs_of_pos (kerM1_pos _ _)]
        have h1 := kerM1_le' q.1 q.2
        have hc := Real.cosh_pos (Real.pi * q.1)
        have hw1 := klW_nonneg hq1.le
        have hw2 := klW_nonneg hq2.le
        have hk := norm_nonneg (klT f q.1)
        have hh2 := norm_nonneg (h q.2)
        calc klW q.1 * (‖klT f q.1‖ * (kerM1 q.1 q.2 * (klW q.2 * ‖h q.2‖)))
            ≤ klW q.1 * (‖klT f q.1‖ * (Real.pi ^ 2 / (2 * Real.cosh (Real.pi * q.1)) * (klW q.2 * ‖h q.2‖))) := by
              gcongr
          _ = Real.pi ^ 2 / 2 * (klW q.1 * (‖klT f q.1‖ * (Real.cosh (Real.pi * q.1))⁻¹) * (klW q.2 * ‖h q.2‖)) := by
              field_simp
      have e1 := integral_prod H hHi
      have e2 := integral_prod_symm H hHi
      have hL : ∫ ν, ∫ ν', H (ν, ν') ∂μz ∂μz = ∫ ν in Ioi 0, (klW ν : ℂ) * ((starRingEnd ℂ) (klT f ν) * K1op h ν) := by
        refine integral_congr_ae (Eventually.of_forall fun ν => ?_)
        simp only [H, K1op]
        rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
      have hR : ∫ ν', ∫ ν, H (ν, ν') ∂μz ∂μz
          = ∫ ν in Ioi 0, (klW ν : ℂ) * ((starRingEnd ℂ) (K1op (klT f) ν) * h ν) := by
        refine integral_congr_ae (Eventually.of_forall fun ν' => ?_)
        simp only [H, K1op]
        rw [← integral_conj, ← MeasureTheory.integral_mul_const, ← MeasureTheory.integral_const_mul]
        congr 1; funext ν
        simp only [map_mul, Complex.conj_ofReal]
        rw [kerM1_symm ν' ν]; ring
      rw [← hL, ← e1, e2, hR]
    rw [hA, ← hP', hB]
  have hD := ae_eq_zero_of_forall_test_bdd hDm hDb (fun h hh => by
    have i1 : Integrable (fun ν => (starRingEnd ℂ) (klT (fun z : ℝ => (z : ℂ) * f z) ν) * aW h ν)
        (volume.restrict (Ioi (0 : ℝ))) :=
      ((isKTest_aW hh).integrable.restrict).bdd_mul
        ((aestronglyMeasurable_klT hzf.continuous.aestronglyMeasurable).restrict.star)
        (Eventually.of_forall fun ν => by rw [RCLike.norm_conj]; exact hC1 ν)
    have i2 : Integrable (fun ν => (starRingEnd ℂ) (K1op (klT f) ν) * aW h ν)
        (volume.restrict (Ioi (0 : ℝ))) :=
      ((isKTest_aW hh).integrable.restrict).bdd_mul ((aestronglyMeasurable_K1op hFm).restrict.star)
        (Eventually.of_forall fun ν => by rw [RCLike.norm_conj]; exact norm_K1op_le mKF ν)
    have e : ∫ ν in Ioi 0, (klW ν : ℂ) * ((starRingEnd ℂ) (D ν) * h ν)
        = ∫ ν in Ioi 0, ((starRingEnd ℂ) (klT (fun z : ℝ => (z : ℂ) * f z) ν) * aW h ν
            - (starRingEnd ℂ) (K1op (klT f) ν) * aW h ν) := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun ν _ => ?_)
      simp only [D, aW, map_sub]; ring
    rw [e, integral_sub i1 i2]
    have k := key h hh
    have k1 : ∫ ν in Ioi 0, (starRingEnd ℂ) (klT (fun z : ℝ => (z : ℂ) * f z) ν) * aW h ν
        = ∫ ν in Ioi 0, (klW ν : ℂ) * ((starRingEnd ℂ) (klT (fun z : ℝ => (z : ℂ) * f z) ν) * h ν) :=
      setIntegral_congr_fun measurableSet_Ioi (fun ν _ => by simp only [aW]; ring)
    have k2 : ∫ ν in Ioi 0, (starRingEnd ℂ) (K1op (klT f) ν) * aW h ν
        = ∫ ν in Ioi 0, (klW ν : ℂ) * ((starRingEnd ℂ) (K1op (klT f) ν) * h ν) :=
      setIntegral_congr_fun measurableSet_Ioi (fun ν _ => by simp only [aW]; ring)
    rw [k1, k2, k, sub_self])
  filter_upwards [hD] with ν hν
  exact sub_eq_zero.1 hν

end Qschubert
