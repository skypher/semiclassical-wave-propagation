import Qschubert.KLFCY2

/-!
# Lemma FC, case `Z = Y`: `Y` on products in the KL picture

For `u ∈ Dom(-Δ)` with `klU u = φ ⊗ B` (`φ` continuous with compact support away from `k = 0`, `B` a KL test
function): `klU (Y u) = φ ⊗ (½ B + H)`, where `H ∈ L²(w)` is any function with `⟨KL f, H⟩ = ⟨f, z∂_z ψ_{wB}⟩_{dz/z}`
for test `f` (`klU_domY_Hfun`). Proof: `Y` is characterized against test functions (`inner_Y_dom`), the mode identity
`f_k(YP) = (z∂_z + ½) f_k(P)` (`modeF_vfY`), and one integration by parts in `z` (`integral_conj_Df`).
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set
open scoped ENNReal

local notation "L2H'" => Lp ℂ 2 (volume : Measure UpperHalfPlane)

section fiber

variable {f a B : ℝ → ℂ}

lemma IsKTest.conj (hf : IsKTest f) : IsKTest fun z => (starRingEnd ℂ) (f z) := by
  refine ⟨Complex.conjCLE.contDiff.comp hf.smooth, hf.compact.comp_left (map_zero _), ?_⟩
  refine (closure_mono fun z hz => ?_).trans hf.pos
  simpa using hz

lemma deriv_conj_test (hf : IsKTest f) (z : ℝ) :
    deriv (fun z => (starRingEnd ℂ) (f z)) z = (starRingEnd ℂ) (deriv f z) :=
  (((Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp_hasDerivAt z (hf.differentiable z).hasDerivAt)).deriv

lemma continuousOn_klInvD (ha : IsKTest a) : ContinuousOn (klInvD a) (Ioi 0) := by
  unfold klInvD
  refine continuousOn_const.mul (continuousOn_of_dominated (bound := fun t => ‖hatA a t‖) ?_ ?_
    (integrable_hatA ha).norm ?_)
  · exact fun z _ => ((Complex.continuous_ofReal.comp (by fun_prop)).mul (continuous_hatA ha)).aestronglyMeasurable
  · intro z hz
    refine Eventually.of_forall fun t => ?_
    have hz0 : (0 : ℝ) < z := hz
    have hx : 0 ≤ z * Real.cosh t := mul_nonneg hz0.le (Real.cosh_pos t).le
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hx (Real.exp_pos _).le)]
    exact mul_le_of_le_one_left (norm_nonneg _) (abs_mul_exp_neg_le _ hx)
  · exact Eventually.of_forall fun t => (Complex.continuous_ofReal.comp (by fun_prop)).continuousOn.mul
      continuousOn_const

/-- Integration by parts in `z`. -/
lemma integral_conj_Df (hf : IsKTest f) (ha : IsKTest a) :
    ∫ z in Ioi (0 : ℝ), (starRingEnd ℂ) (((z : ℂ) * deriv f z) / z) * klInvA a z
      = -∫ z in Ioi (0 : ℝ), (starRingEnd ℂ) (f z) * (klInvD a z / z) := by
  have hk := hf.conj
  set k : ℝ → ℂ := fun z => (starRingEnd ℂ) (f z)
  have hu := hasDerivAt_mul_of_tsupport hk (φ := klInvA a) (φ' := fun z => klInvD a z / z)
    (fun z hz => hasDerivAt_klInvA ha hz)
  have cψ := continuousOn_klInvA ha
  have cD : ContinuousOn (fun z : ℝ => klInvD a z / z) (Ioi 0) :=
    (continuousOn_klInvD ha).div Complex.continuous_ofReal.continuousOn
      (fun z hz => by exact_mod_cast (ne_of_gt hz))
  have i1 := integrable_mul_of_tsupport hk cD
  have i2 := integrable_mul_of_tsupport hk.deriv' cψ
  have iu := integrable_mul_of_tsupport hk cψ
  have h0 := integral_eq_zero_of_hasDerivAt_of_integrable hu (i1.add i2) iu
  have h1 : (∫ z, klInvD a z / z * k z) + ∫ z, klInvA a z * deriv k z = 0 := by
    rw [← integral_add i1 i2]; exact h0
  have e1 : ∫ z in Ioi (0 : ℝ), (starRingEnd ℂ) (((z : ℂ) * deriv f z) / z) * klInvA a z
      = ∫ z, klInvA a z * deriv k z := by
    have e' : ∫ z, klInvA a z * deriv k z = ∫ z in Ioi (0 : ℝ), klInvA a z * deriv k z :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
        rw [hk.deriv'.eq_zero_of_nonpos (not_lt.1 hz), mul_zero])).symm
    rw [e']
    refine setIntegral_congr_fun measurableSet_Ioi (fun z hz => ?_)
    have hz' : (z : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hz)
    simp only [k]
    rw [deriv_conj_test hf z, mul_div_cancel_left₀ _ hz', mul_comm]
  have e2 : ∫ z in Ioi (0 : ℝ), (starRingEnd ℂ) (f z) * (klInvD a z / z) = ∫ z, klInvD a z / z * k z := by
    have e' : ∫ z, klInvD a z / z * k z = ∫ z in Ioi (0 : ℝ), klInvD a z / z * k z :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
        rw [hk.eq_zero_of_nonpos (not_lt.1 hz), mul_zero])).symm
    rw [e']
    exact setIntegral_congr_fun measurableSet_Ioi (fun z _ => mul_comm _ _)
  rw [e1, e2]
  linear_combination h1

/-- `⟨KL(z f'), B⟩_w = -⟨f, z∂_z ψ_{wB}⟩_{dz/z}`. -/
lemma fiber_Y (hf : IsKTest f) (hB : IsKTest B) :
    ∫ ν in Ioi (0 : ℝ), (klW ν : ℂ) * ((starRingEnd ℂ) (klT (fun z : ℝ => (z : ℂ) * deriv f z) ν) * B ν)
      = -∫ z in Ioi (0 : ℝ), (starRingEnd ℂ) (f z) * (klInvD (aW B) z / z) := by
  rw [← integral_conj_mul_aW hB (klT fun z : ℝ => (z : ℂ) * deriv f z),
    integral_conj_klT_mul hf.deriv'.mul_id (isKTest_aW hB), integral_conj_Df hf (isKTest_aW hB)]

lemma memLp_klInvD_muZ (hB : IsKTest B) : MemLp (klInvD (aW B)) 2 muZ :=
  memLp_muZ_of ((continuousOn_klInvD (isKTest_aW hB)).aestronglyMeasurable measurableSet_Ioi)
    (integrableOn_klInvD_sq (isKTest_aW hB))

end fiber

/-- **The mode identity for `Y = y∂_y`.** -/
lemma modeF_vfY (P : testFn) {k : ℝ} (hk : k ≠ 0) {z : ℝ} (hz : 0 < z) :
    modeF ((vfTest Complex.I P : testFn) : ℂ → ℂ) k z
      = (z : ℂ) * deriv (modeF P k) z + (1 / 2 : ℂ) * modeF P k z := by
  set c := modeC k
  have hc : 0 < c := modeC_pos hk
  set u := prof P k
  have hu : IsKTest u := isKTest_prof P k
  set v : ℝ → ℂ := fun z => u (z / c)
  have hv : IsKTest v := hu.comp_div hc
  have hv1 : deriv v z = deriv u (z / c) / c := (hasDerivAt_comp_div hu c z).deriv
  set φ : ℝ → ℂ := fun z => ((sF c z : ℝ) : ℂ)
  set φ' : ℝ → ℂ := fun z => ((-sF c z / (2 * z) : ℝ) : ℂ)
  have hφ : ∀ z : ℝ, 0 < z → HasDerivAt φ (φ' z) z := fun z hz => (hasDerivAt_sF c hz).ofReal_comp
  have hm : modeF P k = fun z => φ z * v z := rfl
  have hd1 : deriv (modeF P k) z = φ' z * v z + φ z * deriv v z := by
    rw [hm]; exact (hasDerivAt_mul_of_tsupport hv hφ z).deriv
  have hY : modeF ((vfTest Complex.I P : testFn) : ℂ → ℂ) k z = φ z * (((z / c : ℝ) : ℂ) * deriv u (z / c)) := by
    show φ z * prof ((vfTest Complex.I P : testFn) : ℂ → ℂ) k (z / c) = _
    rw [prof_vfY]
  have hz' : (z : ℂ) ≠ 0 := by exact_mod_cast hz.ne'
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  rw [hY, hd1, hv1, show modeF P k z = φ z * v z from rfl]
  simp only [φ']
  push_cast
  field_simp
  ring

/-- `KL` of the `Y`-mode. -/
lemma klT_modeF_vfY (P : testFn) {k : ℝ} (hk : k ≠ 0) (ν : ℝ) :
    klT (modeF ((vfTest Complex.I P : testFn) : ℂ → ℂ) k) ν
      = klT (fun z : ℝ => (z : ℂ) * deriv (modeF P k) z) ν + (1 / 2 : ℂ) * klT (modeF P k) ν := by
  have hf := isKTest_modeF P hk
  have h := klT_linear hf.deriv'.mul_id hf 1 (1 / 2) ν
  simp only [one_mul] at h
  rw [← h]
  unfold klT
  exact setIntegral_congr_fun measurableSet_Ioi (fun z hz => by rw [modeF_vfY P hk hz])

section twoD

variable {φ B : ℝ → ℂ}

lemma inner_UFL_eq (P : testFn) (g : Lp ℂ 2 muU) {G : ℝ × ℝ → ℂ} (hg : (g : ℝ × ℝ → ℂ) =ᵐ[muU] G) :
    inner ℂ (UFL P) g = ∫ p, (starRingEnd ℂ) (UF P p) * G p ∂muU := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_UF P).coeFn_toLp, hg] with p h1 h2
  rw [UFL, h1, h2, RCLike.inner_apply']

lemma memLp_two_phi (hφc : Continuous φ) (hφs : HasCompactSupport φ) : MemLp φ 2 (volume : Measure ℝ) :=
  hφc.memLp_of_hasCompactSupport hφs

/-- **`Y` on products**: `klU (Y u) = φ ⊗ (½ B + H)`. -/
theorem klU_domY_Hfun (hφc : Continuous φ) (hφs : HasCompactSupport φ) (hB : IsKTest B)
    (u : negLapH.domain) (hu : ((klU (u : L2H') : Lp ℂ 2 muU) : ℝ × ℝ → ℂ) =ᵐ[muU] Hfun φ B)
    (H : Lp ℂ 2 wNu)
    (hH : ∀ (f : ℝ → ℂ) (hf : IsKTest f), inner ℂ ((memLp_klT_test hf).toLp (klT f)) H
      = inner ℂ ((memLp_muZ_test hf).toLp f) ((memLp_klInvD_muZ hB).toLp (klInvD (aW B)))) :
    ((klU (domY u) : Lp ℂ 2 muU) : ℝ × ℝ → ℂ) =ᵐ[muU] fun p => φ p.1 * ((1 / 2 : ℂ) * B p.2 + H p.2) := by
  have hBm := memLp_wNu hB
  have hχ : MemLp (fun ν => (1 / 2 : ℂ) * B ν + H ν) 2 wNu := (hBm.const_mul (1 / 2)).add (Lp.memLp H)
  set R₀ : ℝ × ℝ → ℂ := fun p => φ p.1 * ((1 / 2 : ℂ) * B p.2 + H p.2)
  have m₀ : MemLp R₀ 2 muU := memLp_prod_mul (memLp_two_phi hφc hφs) hχ
  have mHf : MemLp (Hfun φ B) 2 muU := memLp_prod_mul (memLp_two_phi hφc hφs) hBm
  obtain ⟨y, hy⟩ := klU_surjective (m₀.toLp R₀)
  have hiso : ∀ x x' : L2H', inner ℂ (klU x) (klU x') = inner ℂ x x' := fun x x' => by
    rw [← klUi_apply, ← klUi_apply, klUi.inner_map_map]
  have hpair : ∀ P : testFn, inner ℂ (toL2 P) (domY u) = inner ℂ (toL2 P) y := by
    intro P
    have h1 := inner_Y_dom P u
    have e1 : inner ℂ (toL2 P) (domY u) = inner ℂ (toL2 P) (u : L2H') - inner ℂ (toL2 (vfTest Complex.I P)) (u : L2H') := by
      linear_combination h1
    rw [e1, ← hiso (toL2 P) (u : L2H'), ← hiso (toL2 (vfTest Complex.I P)) (u : L2H'), ← hiso (toL2 P) y, klU_toL2,
      klU_toL2, hy, inner_UFL_eq P _ hu, inner_UFL_eq _ _ hu, inner_UFL_eq P _ m₀.coeFn_toLp]
    have I1 : Integrable (fun p => (starRingEnd ℂ) (UF P p) * Hfun φ B p) ((volume : Measure ℝ).prod wNu) :=
      (memLp_UF P).star.integrable_mul mHf
    have I2 : Integrable (fun p => (starRingEnd ℂ) (UF ((vfTest Complex.I P : testFn) : ℂ → ℂ) p) * Hfun φ B p)
        ((volume : Measure ℝ).prod wNu) := (memLp_UF (vfTest Complex.I P)).star.integrable_mul mHf
    have I3 : Integrable (fun p => (starRingEnd ℂ) (UF P p) * R₀ p) ((volume : Measure ℝ).prod wNu) :=
      (memLp_UF P).star.integrable_mul m₀
    have e2 : ∫ p, (starRingEnd ℂ) (UF P p) * Hfun φ B p ∂muU
        = ∫ k, ∫ ν, (starRingEnd ℂ) (UF P (k, ν)) * Hfun φ B (k, ν) ∂wNu := integral_prod _ I1
    have e3 : ∫ p, (starRingEnd ℂ) (UF ((vfTest Complex.I P : testFn) : ℂ → ℂ) p) * Hfun φ B p ∂muU
        = ∫ k, ∫ ν, (starRingEnd ℂ) (UF ((vfTest Complex.I P : testFn) : ℂ → ℂ) (k, ν)) * Hfun φ B (k, ν) ∂wNu :=
      integral_prod _ I2
    have e4 : ∫ p, (starRingEnd ℂ) (UF P p) * R₀ p ∂muU
        = ∫ k, ∫ ν, (starRingEnd ℂ) (UF P (k, ν)) * R₀ (k, ν) ∂wNu := integral_prod _ I3
    rw [e2, e3, e4, ← integral_sub I1.integral_prod_left I2.integral_prod_left]
    refine integral_congr_ae ?_
    filter_upwards [ae_ne_zero_real] with k hk
    have hf := isKTest_modeF P hk
    set f := modeF P k
    have hDf := hf.deriv'.mul_id
    have mK := memLp_klT_test hf
    have mD := memLp_klT_test hDf
    have iKB : Integrable (fun ν => (starRingEnd ℂ) (klT f ν) * B ν) wNu := mK.star.integrable_mul hBm
    have iDB : Integrable (fun ν => (starRingEnd ℂ) (klT (fun z : ℝ => (z : ℂ) * deriv f z) ν) * B ν) wNu :=
      mD.star.integrable_mul hBm
    have iKH : Integrable (fun ν => (starRingEnd ℂ) (klT f ν) * H ν) wNu := mK.star.integrable_mul (Lp.memLp H)
    -- the key fiber identity
    have key : -∫ ν, (starRingEnd ℂ) (klT (fun z : ℝ => (z : ℂ) * deriv f z) ν) * B ν ∂wNu
        = ∫ ν, (starRingEnd ℂ) (klT f ν) * H ν ∂wNu := by
      have a1 : ∫ ν, (starRingEnd ℂ) (klT (fun z : ℝ => (z : ℂ) * deriv f z) ν) * B ν ∂wNu
          = -∫ z in Ioi (0 : ℝ), (starRingEnd ℂ) (f z) * (klInvD (aW B) z / z) := by
        rw [integral_wNu_eq]; exact fiber_Y hf hB
      have a2 : ∫ ν, (starRingEnd ℂ) (klT f ν) * H ν ∂wNu
          = ∫ z in Ioi (0 : ℝ), (starRingEnd ℂ) (f z) * (klInvD (aW B) z / z) := by
        have h2 := hH f hf
        rw [inner_toLp_muZ] at h2
        have h3 : inner ℂ ((memLp_klT_test hf).toLp (klT f)) H = ∫ ν, (starRingEnd ℂ) (klT f ν) * H ν ∂wNu := by
          rw [L2.inner_def]
          refine integral_congr_ae ?_
          filter_upwards [(memLp_klT_test hf).coeFn_toLp] with ν h1
          rw [h1, RCLike.inner_apply']
        rw [← h3, h2]
        exact setIntegral_congr_fun measurableSet_Ioi (fun z _ => mul_div_assoc _ _ _)
      rw [a1, a2, neg_neg]
    have hUY : ∀ ν, UF ((vfTest Complex.I P : testFn) : ℂ → ℂ) (k, ν)
        = klT (fun z : ℝ => (z : ℂ) * deriv f z) ν + (1 / 2 : ℂ) * klT f ν := fun ν => klT_modeF_vfY P hk ν
    have hUP : ∀ ν, UF P (k, ν) = klT f ν := fun ν => rfl
    simp only [hUY, hUP, Hfun, R₀]
    have L1 : ∫ ν, (starRingEnd ℂ) (klT f ν) * (φ k * B ν) ∂wNu
        = φ k * ∫ ν, (starRingEnd ℂ) (klT f ν) * B ν ∂wNu := by
      rw [← MeasureTheory.integral_const_mul]; congr 1; funext ν; ring
    have L2' : ∫ ν, (starRingEnd ℂ) (klT (fun z : ℝ => (z : ℂ) * deriv f z) ν + (1 / 2 : ℂ) * klT f ν) * (φ k * B ν) ∂wNu
        = φ k * ((∫ ν, (starRingEnd ℂ) (klT (fun z : ℝ => (z : ℂ) * deriv f z) ν) * B ν ∂wNu)
            + (1 / 2 : ℂ) * ∫ ν, (starRingEnd ℂ) (klT f ν) * B ν ∂wNu) := by
      rw [← MeasureTheory.integral_const_mul, ← integral_add iDB (iKB.const_mul _), ← MeasureTheory.integral_const_mul]
      congr 1; funext ν
      simp only [map_add, map_mul, map_div₀, map_one, map_ofNat]; ring
    have L3 : ∫ ν, (starRingEnd ℂ) (klT f ν) * (φ k * ((1 / 2 : ℂ) * B ν + H ν)) ∂wNu
        = φ k * ((1 / 2 : ℂ) * (∫ ν, (starRingEnd ℂ) (klT f ν) * B ν ∂wNu)
            + ∫ ν, (starRingEnd ℂ) (klT f ν) * H ν ∂wNu) := by
      rw [← MeasureTheory.integral_const_mul, ← integral_add (iKB.const_mul _) iKH, ← MeasureTheory.integral_const_mul]
      congr 1; funext ν; ring
    rw [L1, L2', L3, ← key]; ring
  have hdy : domY u = y := by
    refine ext_inner_left ℂ fun w => ?_
    refine DenseRange.induction_on denseRange_toL2 w ?_ (fun P => hpair P)
    exact isClosed_eq (continuous_inner.comp (continuous_id.prodMk continuous_const))
      (continuous_inner.comp (continuous_id.prodMk continuous_const))
  rw [hdy, hy]
  exact m₀.coeFn_toLp

end twoD

end Qschubert
