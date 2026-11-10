import Qschubert.KLMode
import Qschubert.CoreDom
import Qschubert.SpecTransfer

/-!
# The Kontorovich–Lebedev picture of `L²(ℍ)`

`klU : L²(ℍ) →L L²(ℝ × ℝ, dk ⊗ w(ν)dν|_{ν>0})`, `w(ν) = (2/π²) ν sinh πν`, is the isometric extension of
`F ↦ ((k, ν) ↦ KL(f_k)(ν))` from test functions (partial Fourier transform in `x`, scaling `z = 2π|k|y`, KL in `z`).
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set UpperHalfPlane
open scoped ENNReal

/-! ### Integrability of the weighted square -/

/-- `w(ν) = (2/π²) ν sinh(πν)`. -/
noncomputable def klW (ν : ℝ) : ℝ := 2 / Real.pi ^ 2 * ν * Real.sinh (Real.pi * ν)

lemma klW_nonneg {ν : ℝ} (hν : 0 ≤ ν) : 0 ≤ klW ν := by
  unfold klW
  have := Real.sinh_nonneg_iff.2 (mul_nonneg Real.pi_pos.le hν)
  positivity

theorem integrableOn_klW_mul {f : ℝ → ℂ} (hf : IsKTest f) :
    IntegrableOn (fun ν => klW ν * ‖klT f ν‖ ^ 2) (Ioi 0) := by
  have hpi := Real.pi_pos
  set G : ℝ → ℝ := fun η => -(1 / (2 * Real.pi)) * (klQ f (-η) + klQ f η)
  have hq := integrable_klQ hf
  have hG : Integrable G := (hq.comp_neg.add hq).const_mul _
  have hpt : ∀ ν : ℝ, klW ν * ‖klT f ν‖ ^ 2 = G ((2 * Real.pi)⁻¹ * ν) := by
    intro ν
    rw [klW, weight_mul_norm_klT_sq hf]
    simp only [G, klQ]
    rw [show -((2 * Real.pi)⁻¹ * ν) = -ν / (2 * Real.pi) by field_simp,
      show (2 * Real.pi)⁻¹ * ν = ν / (2 * Real.pi) by field_simp]
    field_simp
    ring
  simp_rw [hpt]
  exact (hG.comp_mul_left' (by positivity)).integrableOn

lemma integrable_norm_sq_div_sq {g : ℝ → ℂ} (hg : IsKTest g) :
    Integrable fun y : ℝ => ‖g y‖ ^ 2 / y ^ 2 := by
  have h := hg.inv_mul
  have hc : Continuous fun y : ℝ => ‖(y : ℂ)⁻¹ * g y‖ ^ 2 := (h.continuous.norm.pow 2)
  have hcs : HasCompactSupport fun y : ℝ => ‖(y : ℂ)⁻¹ * g y‖ ^ 2 :=
    h.compact.norm.comp_left (g := fun r : ℝ => r ^ 2) (by norm_num)
  refine (hc.integrable_of_hasCompactSupport hcs).congr ?_
  · refine Eventually.of_forall fun y => ?_
    simp only [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, mul_pow, inv_pow, sq_abs]
    ring

/-! ### The target space and the map on test functions -/

/-- `w(ν) dν` on `ν > 0`. -/
noncomputable def wNu : Measure ℝ := (volume.restrict (Ioi 0)).withDensity fun ν => ENNReal.ofReal (klW ν)

instance : SFinite wNu := by unfold wNu; infer_instance

/-- `dk ⊗ w(ν) dν`. -/
noncomputable def muU : Measure (ℝ × ℝ) := (volume : Measure ℝ).prod wNu

/-- `(UF)(k, ν) = KL(f_k)(ν)`. -/
noncomputable def UF (F : ℂ → ℂ) (p : ℝ × ℝ) : ℂ := klT (modeF F p.1) p.2

lemma measurable_besselKi : Measurable fun q : ℝ × ℝ => besselKi q.1 q.2 := by
  have hc : Continuous (Function.uncurry fun (q : ℝ × ℝ) (t : ℝ) =>
      Real.exp (-(q.2 * Real.cosh t)) * Real.cos (q.1 * t)) := by
    unfold Function.uncurry; fun_prop
  exact (hc.stronglyMeasurable.integral_prod_right (ν := volume.restrict (Ioi 0))).measurable

lemma measurable_modeF (F : testFn) : Measurable fun q : ℝ × ℝ => modeF F q.1 q.2 := by
  have hc : Measurable fun q : ℝ × ℝ => modeC q.1 := (by unfold modeC; fun_prop : Continuous _).measurable
  have hs : Measurable fun q : ℝ × ℝ => sF (modeC q.1) q.2 := by
    unfold sF
    exact (Real.continuous_sqrt.measurable.comp hc).mul
      ((Real.continuous_sqrt.measurable.comp measurable_snd).inv)
  have hp : Measurable fun q : ℝ × ℝ => pF F (q.1, q.2 / modeC q.1) :=
    (stronglyMeasurable_pF F).measurable.comp (measurable_fst.prodMk (measurable_snd.div hc))
  exact (Complex.measurable_ofReal.comp hs).mul hp

lemma stronglyMeasurable_UF (F : testFn) : StronglyMeasurable (UF F) := by
  have hm : Measurable (Function.uncurry fun (p : ℝ × ℝ) (z : ℝ) =>
      ((besselKi p.2 z : ℝ) : ℂ) * (modeF F p.1 z / z)) := by
    have h1 : Measurable fun q : (ℝ × ℝ) × ℝ => besselKi q.1.2 q.2 :=
      measurable_besselKi.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
    have h2 : Measurable fun q : (ℝ × ℝ) × ℝ => modeF F q.1.1 q.2 :=
      (measurable_modeF F).comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
    exact (Complex.measurable_ofReal.comp h1).mul (h2.div (Complex.measurable_ofReal.comp measurable_snd))
  exact hm.stronglyMeasurable.integral_prod_right (ν := volume.restrict (Ioi 0))

lemma enorm_rpow_two (z : ℂ) : ‖z‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖z‖ ^ 2) := by
  rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]
  norm_num

lemma lintegral_wNu_UF (F : testFn) {k : ℝ} (hk : k ≠ 0) :
    ∫⁻ ν, ‖UF F (k, ν)‖ₑ ^ (2 : ℝ) ∂wNu = ∫⁻ y, ‖pF F (k, y)‖ₑ ^ (2 : ℝ) ∂nuY := by
  have hdw : Measurable fun ν : ℝ => ENNReal.ofReal (klW ν) :=
    ENNReal.measurable_ofReal.comp (by unfold klW; fun_prop : Continuous klW).measurable
  have hdy : Measurable fun y : ℝ => ENNReal.ofReal ((y ^ 2)⁻¹) :=
    ENNReal.measurable_ofReal.comp ((measurable_id.pow_const 2).inv)
  have hmU : Measurable fun ν => ‖UF F (k, ν)‖ₑ ^ (2 : ℝ) :=
    ((stronglyMeasurable_UF F).measurable.comp measurable_prodMk_left).enorm.pow_const _
  have hmP : Measurable fun y => ‖pF F (k, y)‖ₑ ^ (2 : ℝ) :=
    ((stronglyMeasurable_pF F).measurable.comp measurable_prodMk_left).enorm.pow_const _
  rw [wNu, nuY, lintegral_withDensity_eq_lintegral_mul _ hdw hmU,
    lintegral_withDensity_eq_lintegral_mul _ hdy hmP]
  have e1 : ∫⁻ ν in Ioi 0, ((fun ν => ENNReal.ofReal (klW ν)) * fun ν => ‖UF F (k, ν)‖ₑ ^ (2 : ℝ)) ν
      = ENNReal.ofReal (∫ ν in Ioi 0, klW ν * ‖klT (modeF F k) ν‖ ^ 2) := by
    rw [ofReal_integral_eq_lintegral_ofReal (integrableOn_klW_mul (isKTest_modeF F hk))]
    · refine setLIntegral_congr_fun measurableSet_Ioi (fun ν hν => ?_)
      simp only [Pi.mul_apply, UF, enorm_rpow_two]
      rw [← ENNReal.ofReal_mul (klW_nonneg (le_of_lt hν))]
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with ν hν
      exact mul_nonneg (klW_nonneg (le_of_lt hν)) (sq_nonneg _)
  have e2 : ∫⁻ y in Ioi 0, ((fun y => ENNReal.ofReal ((y ^ 2)⁻¹)) * fun y => ‖pF F (k, y)‖ₑ ^ (2 : ℝ)) y
      = ENNReal.ofReal (∫ y in Ioi 0, ‖prof F k y‖ ^ 2 / y ^ 2) := by
    rw [ofReal_integral_eq_lintegral_ofReal (integrable_norm_sq_div_sq (isKTest_prof F k)).integrableOn]
    · refine setLIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
      simp only [Pi.mul_apply, enorm_rpow_two, prof]
      rw [← ENNReal.ofReal_mul (inv_nonneg.2 (sq_nonneg y)), div_eq_mul_inv, mul_comm]
    · exact Eventually.of_forall fun y => div_nonneg (sq_nonneg _) (sq_nonneg _)
  rw [e1, e2]
  congr 1
  exact kl_parseval_modeF F hk

/-- **`∫ |UF|² d(dk ⊗ w dν) = ∫_ℍ |F|²`.** -/
theorem lintegral_UF (F : testFn) :
    ∫⁻ p, ‖UF F p‖ₑ ^ (2 : ℝ) ∂muU = ∫⁻ z : ℍ, ‖(F : ℂ → ℂ) z‖ₑ ^ (2 : ℝ) := by
  rw [← lintegral_pF F, muU, muT,
    lintegral_prod _ ((stronglyMeasurable_UF F).measurable.enorm.pow_const _).aemeasurable,
    lintegral_prod _ ((stronglyMeasurable_pF F).measurable.enorm.pow_const _).aemeasurable]
  refine lintegral_congr_ae ?_
  have h0 : ∀ᵐ k : ℝ ∂volume, k ≠ 0 := by
    rw [ae_iff]; simp
  filter_upwards [h0] with k hk
  exact lintegral_wNu_UF F hk

lemma ae_fst_ne_zero : ∀ᵐ p ∂muU, p.1 ≠ 0 := by
  rw [ae_iff]
  have e : {p : ℝ × ℝ | ¬p.1 ≠ 0} = ({0} : Set ℝ) ×ˢ (univ : Set ℝ) := by ext p; simp
  rw [e, muU, Measure.prod_prod]; simp

lemma memLp_UF (F : testFn) : MemLp (UF F) 2 muU := by
  show eLpNorm (UF F) 2 muU < ⊤
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top
    (stronglyMeasurable_UF F).aestronglyMeasurable, ENNReal.toReal_ofNat, lintegral_UF]
  refine ENNReal.rpow_lt_top_of_nonneg (by norm_num) ?_
  have h := (memLp_comp_coe F.2).eLpNorm_lt_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top
    (show AEStronglyMeasurable (fun z : ℍ => (F : ℂ → ℂ) z) volume from
      (F.2.smooth.continuous.comp UpperHalfPlane.continuous_coe).aestronglyMeasurable), ENNReal.toReal_ofNat] at h
  exact ((ENNReal.rpow_lt_top_iff_of_pos (by norm_num)).1 h).ne

/-- `UF ∈ L²(dk ⊗ w dν)`. -/
noncomputable def UFL (F : testFn) : Lp ℂ 2 muU := (memLp_UF F).toLp _

theorem norm_UFL (F : testFn) : ‖UFL F‖ = ‖toL2 F‖ := by
  rw [UFL, Lp.norm_toLp, Lp.norm_def]
  congr 1
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top
      (stronglyMeasurable_UF F).aestronglyMeasurable,
    show toL2 F = (memLp_comp_coe F.2).toLp _ from rfl, eLpNorm_congr_ae ((memLp_comp_coe F.2).coeFn_toLp),
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top
      (show AEStronglyMeasurable (fun z : ℍ => (F : ℂ → ℂ) z) volume from
      (F.2.smooth.continuous.comp UpperHalfPlane.continuous_coe).aestronglyMeasurable),
    ENNReal.toReal_ofNat, lintegral_UF]

lemma modeF_add (F G : testFn) (k : ℝ) :
    modeF ((F + G : testFn) : ℂ → ℂ) k = fun z => 1 * modeF F k z + 1 * modeF G k z := by
  funext z; simp only [modeF, prof_add, Pi.add_apply]; ring

lemma modeF_smul (c : ℂ) (F : testFn) (k : ℝ) :
    modeF ((c • F : testFn) : ℂ → ℂ) k = fun z => c * modeF F k z + 0 * modeF F k z := by
  funext z
  have h : prof ((c • F : testFn) : ℂ → ℂ) k (z / modeC k) = c * prof F k (z / modeC k) := by
    show pF ((c • F : testFn) : ℂ → ℂ) (k, z / modeC k) = c * pF F (k, z / modeC k)
    rw [pF_smul]; rfl
  simp only [modeF, h]; ring

lemma UF_add (F G : testFn) {p : ℝ × ℝ} (hp : p.1 ≠ 0) :
    UF ((F + G : testFn) : ℂ → ℂ) p = UF F p + UF G p := by
  simp only [UF]
  rw [modeF_add, klT_linear (isKTest_modeF F hp) (isKTest_modeF G hp)]; ring

lemma UF_smul (c : ℂ) (F : testFn) {p : ℝ × ℝ} (hp : p.1 ≠ 0) :
    UF ((c • F : testFn) : ℂ → ℂ) p = c * UF F p := by
  simp only [UF]
  rw [modeF_smul, klT_linear (isKTest_modeF F hp) (isKTest_modeF F hp)]; ring

/-- `F ↦ UF` as a linear map into `L²(dk ⊗ w dν)`. -/
noncomputable def klULin : testFn →ₗ[ℂ] Lp ℂ 2 muU where
  toFun := UFL
  map_add' F G := by
    apply Lp.ext
    filter_upwards [(memLp_UF (F + G)).coeFn_toLp, (memLp_UF F).coeFn_toLp, (memLp_UF G).coeFn_toLp,
      Lp.coeFn_add (UFL F) (UFL G), ae_fst_ne_zero] with p h1 h2 h3 h4 hp
    rw [UFL, h1, h4, Pi.add_apply, UFL, UFL, h2, h3, UF_add F G hp]
  map_smul' c F := by
    apply Lp.ext
    filter_upwards [(memLp_UF (c • F)).coeFn_toLp, (memLp_UF F).coeFn_toLp,
      Lp.coeFn_smul c (UFL F), ae_fst_ne_zero] with p h1 h2 h3 hp
    rw [UFL, h1, RingHom.id_apply, h3, Pi.smul_apply, UFL, h2, UF_smul c F hp, smul_eq_mul]

noncomputable def klUDom : lapDomain →ₗ[ℂ] Lp ℂ 2 muU := klULin.comp toL2Equiv.symm.toLinearMap

lemma klUDom_apply (F : testFn) : klUDom (toL2Equiv F) = klULin F := by simp [klUDom]

lemma norm_klUDom (x : lapDomain) : ‖klUDom x‖ = ‖(x : Lp ℂ 2 (volume : Measure ℍ))‖ := by
  obtain ⟨F, rfl⟩ := toL2Equiv.surjective x
  rw [klUDom_apply, coe_toL2Equiv]; exact norm_UFL F

/-- **The Kontorovich–Lebedev picture** `klU : L²(ℍ) →L L²(dk ⊗ w dν)`. -/
noncomputable def klU : Lp ℂ 2 (volume : Measure ℍ) →L[ℂ] Lp ℂ 2 muU :=
  klUDom.extendOfNorm lapDomain.subtypeL

lemma klU_toL2 (F : testFn) : klU (toL2 F) = UFL F := by
  have h := LinearMap.extendOfNorm_eq denseRange_lapDomain_subtypeL
    ⟨1, fun x => by rw [one_mul, norm_klUDom]; rfl⟩ (toL2Equiv F)
  have e1 : (lapDomain.subtypeL (toL2Equiv F) : Lp ℂ 2 (volume : Measure ℍ)) = toL2 F := coe_toL2Equiv F
  calc klU (toL2 F) = klU (lapDomain.subtypeL (toL2Equiv F)) := by rw [e1]
    _ = klUDom (toL2Equiv F) := h
    _ = UFL F := by rw [klUDom_apply]; rfl

/-- **`klU` is an isometry.** -/
theorem norm_klU (u : Lp ℂ 2 (volume : Measure ℍ)) : ‖klU u‖ = ‖u‖ := by
  refine DenseRange.induction_on denseRange_toL2 u
    (isClosed_eq (continuous_norm.comp klU.continuous) continuous_norm) fun F => ?_
  rw [klU_toL2, norm_UFL]

/-- **Intertwining on test functions**: `klU (-ΔF) = (ν² + 1/4) · klU F`. -/
theorem klU_negLap_test (F : testFn) :
    ((klU (-toL2 (lapTest F)) : Lp ℂ 2 muU) : ℝ × ℝ → ℂ) =ᵐ[muU]
      fun p => ((p.2 : ℂ) ^ 2 + 1 / 4) * (klU (toL2 F) : ℝ × ℝ → ℂ) p := by
  rw [map_neg, klU_toL2, klU_toL2]
  filter_upwards [Lp.coeFn_neg (UFL (lapTest F)), (memLp_UF (lapTest F)).coeFn_toLp,
    (memLp_UF F).coeFn_toLp, ae_fst_ne_zero] with p h1 h2 h3 hp
  rw [h1, Pi.neg_apply, UFL, h2, UFL, h3]
  simp only [UF]
  rw [klT_modeF_lap F hp]; ring

/-! ### The intertwining on `Dom(-Δ)` and the functional calculus -/

/-- **`klU (-Δ u) = (ν² + 1/4) · klU u`** for `u ∈ Dom(-Δ)` (Friedrichs Laplacian `negLapH`). -/
theorem klU_negLapH (u : negLapH.domain) :
    ((klU (negLapH u) : Lp ℂ 2 muU) : ℝ × ℝ → ℂ) =ᵐ[muU]
      fun p => ((p.2 : ℂ) ^ 2 + 1 / 4) * (klU (u : Lp ℂ 2 (volume : Measure ℍ)) : ℝ × ℝ → ℂ) p := by
  have hmem : ((u : Lp ℂ 2 (volume : Measure ℍ)), negLapH u) ∈ closure (negLap.graph : Set _) := by
    rw [← Submodule.topologicalClosure_coe]; exact mem_graphBar_negLapH u
  obtain ⟨a, ha, hlim⟩ := mem_closure_iff_seq_limit.1 hmem
  -- each `a n` is `(toL2 F_n, -toL2 (lapTest F_n))`
  have hF : ∀ n, ∃ F : testFn, a n = (toL2 F, -toL2 (lapTest F)) := by
    intro n
    obtain ⟨y, hy1, hy2⟩ := (LinearPMap.mem_graph_iff _).1 (ha n)
    obtain ⟨F, hF⟩ := toL2Equiv.surjective y
    refine ⟨F, Prod.ext ?_ ?_⟩
    · rw [← hy1, ← hF, coe_toL2Equiv]
    · rw [← hy2, ← hF, negLap_toL2Equiv]
  choose F hFn using hF
  have h1 : Tendsto (fun n => klU (a n).1) atTop (𝓝 (klU (u : Lp ℂ 2 (volume : Measure ℍ)))) :=
    (klU.continuous.tendsto _).comp (continuous_fst.continuousAt.tendsto.comp hlim)
  have h2 : Tendsto (fun n => klU (a n).2) atTop (𝓝 (klU (negLapH u))) :=
    (klU.continuous.tendsto _).comp (continuous_snd.continuousAt.tendsto.comp hlim)
  obtain ⟨ns, hns, hae1⟩ := (tendstoInMeasure_of_tendsto_Lp h1).exists_seq_tendsto_ae
  obtain ⟨ms, hms, hae2⟩ := (tendstoInMeasure_of_tendsto_Lp (h2.comp hns.tendsto_atTop)).exists_seq_tendsto_ae
  have hrel : ∀ᵐ p ∂muU, ∀ n, (klU (a n).2 : ℝ × ℝ → ℂ) p = ((p.2 : ℂ) ^ 2 + 1 / 4) * (klU (a n).1 : ℝ × ℝ → ℂ) p := by
    rw [ae_all_iff]; intro n
    rw [hFn n]; exact klU_negLap_test (F n)
  filter_upwards [hae1, hae2, hrel] with p hp1 hp2 hp3
  have hp1' : Tendsto (fun i => (klU (a (ns (ms i))).1 : ℝ × ℝ → ℂ) p) atTop
      (𝓝 ((klU (u : Lp ℂ 2 (volume : Measure ℍ)) : ℝ × ℝ → ℂ) p)) := hp1.comp hms.tendsto_atTop
  have hp2' : Tendsto (fun i => (klU (a (ns (ms i))).2 : ℝ × ℝ → ℂ) p) atTop
      (𝓝 ((klU (negLapH u) : ℝ × ℝ → ℂ) p)) := hp2
  simp_rw [hp3] at hp2'
  exact tendsto_nhds_unique hp2' (hp1'.const_mul _)

/-- **The functional calculus of `-Δ` in the KL picture**: for `φ` continuous with `φ → 0` at infinity,
`klU (φ(-Δ) η) = φ(ν² + 1/4) · klU η`. -/
theorem klU_functionalCalculus {φ : ℝ → ℂ} (hφc : Continuous φ) (hφ0 : Tendsto φ (cocompact ℝ) (𝓝 0))
    (η : Lp ℂ 2 (volume : Measure ℍ)) :
    ((klU ((Physicslib4.Spectral.Unbounded.spectralMeasure negLapH_isSelfAdjoint).integral φ η) :
      Lp ℂ 2 muU) : ℝ × ℝ → ℂ) =ᵐ[muU] fun p => φ (p.2 ^ 2 + 1 / 4) * (klU η : ℝ × ℝ → ℂ) p := by
  have hV : ∀ x : negLapH.domain, ((klU (negLapH x) : Lp ℂ 2 muU) : ℝ × ℝ → ℂ) =ᵐ[muU]
      fun p => (((p.2 ^ 2 + 1 / 4 : ℝ)) : ℂ) * (klU (x : Lp ℂ 2 (volume : Measure ℍ)) : ℝ × ℝ → ℂ) p := by
    intro x
    filter_upwards [klU_negLapH x] with p hp
    rw [hp]; push_cast; ring
  exact isGood_of_tendsto_cocompact hV (by fun_prop) hφc hφ0 η

end Qschubert
