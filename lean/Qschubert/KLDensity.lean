import Qschubert.KLUnitary
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# Density of the products `φ ⊗ h` in `L²(dk ⊗ w dν)`; `klU` is unitary

`eq_zero_of_inner_Hfun`: if `G ∈ L²(muU)` is orthogonal to every `φ ⊗ h` (`φ` continuous with compact
support away from `k = 0`, `h` a KL test function), then `G = 0`. Route:

* for each test `h`, `m_h(k) = ∫ conj(h ν) G(k, ν) dw(ν)` is locally integrable and `∫ φ m_h = 0` for all
  smooth real `φ` supported in `k ≠ 0`, so `m_h = 0` a.e. (`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`);
* `L²(w dν)` is second countable, so the test functions have a countable dense subfamily `D`; for a.e. `k`
  the slice `G(k, ·)` lies in `L²(w dν)` and is orthogonal to `D`, hence to every test function;
* a function in `L²(w dν)` orthogonal to every test function vanishes a.e. (the same lemma in `ν > 0`).

With `klU_PsiH` (every `φ ⊗ h` is in the range of `klU`) and the isometry this gives `klU_surjective`
and the unitary `klUequiv`.

This is used by `lem:fc` (dd_appendix.tex:197, "on the dense set `Λe^{-γΛ}𝒞`, and then by closure"):
`𝒞 = span{Ψ}` is dense in `L²(ℍ)`.
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set
open scoped ENNReal ContDiff

lemma klW_pos {ν : ℝ} (hν : 0 < ν) : 0 < klW ν := by
  unfold klW
  have := Real.sinh_pos_iff.2 (mul_pos Real.pi_pos hν)
  have := Real.pi_pos
  positivity

lemma measurable_klW_dens : Measurable fun ν : ℝ => ENNReal.ofReal (klW ν) :=
  ENNReal.measurable_ofReal.comp (by unfold klW; fun_prop : Continuous klW).measurable

instance : IsLocallyFiniteMeasure wNu := by
  unfold wNu
  exact IsLocallyFiniteMeasure.withDensity_ofReal (by unfold klW; fun_prop)

/-- KL test functions lie in `L²(w dν)`. -/
lemma memLp_wNu {h : ℝ → ℂ} (hh : IsKTest h) : MemLp h 2 wNu := by
  refine (memLp_two_iff_integrable_sq_norm hh.continuous.aestronglyMeasurable).2 ?_
  rw [wNu, integrable_withDensity_iff_integrable_smul' measurable_klW_dens
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal']
  have hc : Continuous fun ν => max (klW ν) 0 • ‖h ν‖ ^ 2 :=
    ((by unfold klW; fun_prop : Continuous klW).max continuous_const).smul (hh.continuous.norm.pow 2)
  have hcs : HasCompactSupport fun ν => max (klW ν) 0 • ‖h ν‖ ^ 2 :=
    HasCompactSupport.intro hh.compact (fun ν hν => by rw [image_eq_zero_of_notMem_tsupport hν]; simp)
  exact (hc.integrable_of_hasCompactSupport hcs).restrict

/-- `ψ ∈ L²(dk)`, `χ ∈ L²(w dν)` give `ψ ⊗ χ ∈ L²(muU)`. -/
lemma memLp_prod_mul {ψ χ : ℝ → ℂ} (hψ : MemLp ψ 2 (volume : Measure ℝ)) (hχ : MemLp χ 2 wNu) :
    MemLp (fun p : ℝ × ℝ => ψ p.1 * χ p.2) 2 muU := by
  show MemLp _ 2 ((volume : Measure ℝ).prod wNu)
  have hm : AEStronglyMeasurable (fun p : ℝ × ℝ => ψ p.1 * χ p.2) ((volume : Measure ℝ).prod wNu) :=
    (hψ.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst).mul
      (hχ.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)
  refine (memLp_two_iff_integrable_sq_norm hm).2 ?_
  have h1 := (memLp_two_iff_integrable_sq_norm hψ.aestronglyMeasurable).1 hψ
  have h2 := (memLp_two_iff_integrable_sq_norm hχ.aestronglyMeasurable).1 hχ
  exact (h1.mul_prod h2).congr (Eventually.of_forall fun p => by simp [norm_mul, mul_pow])

section dens

variable (G : Lp ℂ 2 muU)

/-- `m_h(k) = ∫ conj(h ν) G(k, ν) dw(ν)`. -/
noncomputable def mH (h : ℝ → ℂ) (k : ℝ) : ℂ :=
  ∫ ν, (starRingEnd ℂ) (h ν) * (G : ℝ × ℝ → ℂ) (k, ν) ∂wNu

lemma inner_Hfun_eq {φ h : ℝ → ℂ} (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (hφ0 : (0 : ℝ) ∉ tsupport φ) (hh : IsKTest h) :
    inner ℂ ((memLp_Hfun hφc hφs hφ0 hh).toLp (Hfun φ h)) G = ∫ k, (starRingEnd ℂ) (φ k) * mH G h k := by
  rw [L2.inner_def]
  have hint : Integrable (fun p : ℝ × ℝ => (starRingEnd ℂ) (Hfun φ h p) * (G : ℝ × ℝ → ℂ) p) muU :=
    ((memLp_Hfun hφc hφs hφ0 hh).star.integrable_mul (Lp.memLp G)).congr (Eventually.of_forall fun p => rfl)
  have e : ∫ p, inner ℂ (((memLp_Hfun hφc hφs hφ0 hh).toLp (Hfun φ h) : Lp ℂ 2 muU) p)
      ((G : ℝ × ℝ → ℂ) p) ∂muU = ∫ p, (starRingEnd ℂ) (Hfun φ h p) * (G : ℝ × ℝ → ℂ) p ∂muU := by
    refine integral_congr_ae ?_
    filter_upwards [(memLp_Hfun hφc hφs hφ0 hh).coeFn_toLp] with p h1
    rw [h1, RCLike.inner_apply']
  have key : ∫ p, (starRingEnd ℂ) (Hfun φ h p) * (G : ℝ × ℝ → ℂ) p ∂muU
      = ∫ k, ∫ ν, (starRingEnd ℂ) (Hfun φ h (k, ν)) * (G : ℝ × ℝ → ℂ) (k, ν) ∂wNu :=
    integral_prod _ (hint : Integrable _ ((volume : Measure ℝ).prod wNu))
  rw [e, key]
  refine integral_congr_ae (Eventually.of_forall fun k => ?_)
  simp only [mH, Hfun, map_mul]
  rw [← MeasureTheory.integral_const_mul]
  congr 1; funext ν; ring

lemma locallyIntegrable_mH {h : ℝ → ℂ} (hh : IsKTest h) : LocallyIntegrable (mH G h) := by
  rw [locallyIntegrable_iff]
  intro K hK
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hχ : MemLp (K.indicator fun _ => (1 : ℂ)) 2 (volume : Measure ℝ) :=
    memLp_indicator_const 2 hKm.nullMeasurableSet 1 (Or.inr hK.measure_lt_top.ne)
  have hP := memLp_prod_mul hχ (memLp_wNu hh).star
  have hint : Integrable (fun p : ℝ × ℝ =>
      (K.indicator (fun _ => (1 : ℂ)) p.1 * (star h) p.2) * (G : ℝ × ℝ → ℂ) p) muU :=
    hP.integrable_mul (Lp.memLp G)
  have h2 := (hint : Integrable _ ((volume : Measure ℝ).prod wNu)).integral_prod_left
  rw [← integrable_indicator_iff hKm]
  refine h2.congr (Eventually.of_forall fun k => ?_)
  by_cases hk : k ∈ K
  · simp only [Set.indicator_of_mem hk, one_mul, Pi.star_apply, mH, Complex.star_def]
  · simp only [Set.indicator_of_notMem hk, zero_mul, integral_zero]

variable {G}

lemma ae_ne_zero_real : ∀ᵐ k : ℝ, k ≠ 0 := by
  rw [ae_iff]; simp

/-- **`m_h = 0` a.e.** when `G` is orthogonal to all products. -/
lemma mH_ae_eq_zero
    (hG : ∀ (φ h : ℝ → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ) (hφ0 : (0 : ℝ) ∉ tsupport φ)
      (hh : IsKTest h), inner ℂ ((memLp_Hfun hφc hφs hφ0 hh).toLp (Hfun φ h)) G = 0)
    {h : ℝ → ℂ} (hh : IsKTest h) : ∀ᵐ k, mH G h k = 0 := by
  have hU : IsOpen ({0}ᶜ : Set ℝ) := isOpen_compl_singleton
  have h1 := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero ((locallyIntegrable_mH G hh).locallyIntegrableOn _)
    (fun g g_diff g_supp g_sub => by
      have hφc : Continuous fun k => (g k : ℂ) := Complex.continuous_ofReal.comp g_diff.continuous
      have hφs : HasCompactSupport fun k => (g k : ℂ) := g_supp.comp_left Complex.ofReal_zero
      have hφ0 : (0 : ℝ) ∉ tsupport fun k => (g k : ℂ) := fun h0 =>
        g_sub (closure_mono (Function.support_comp_subset Complex.ofReal_zero g) h0) rfl
      have := hG _ _ hφc hφs hφ0 hh
      rw [inner_Hfun_eq G hφc hφs hφ0 hh] at this
      rw [← this]
      refine integral_congr_ae (Eventually.of_forall fun k => ?_)
      simp only [Complex.conj_ofReal, Complex.real_smul])
  filter_upwards [h1, ae_ne_zero_real] with k hk hk0 using hk hk0

/-- A function in `L²(w dν)` orthogonal to every KL test function vanishes `w dν`-a.e. -/
lemma ae_eq_zero_of_forall_test {g : ℝ → ℂ} (hg : MemLp g 2 wNu)
    (h0 : ∀ h : ℝ → ℂ, IsKTest h → ∫ ν, (starRingEnd ℂ) (h ν) * g ν ∂wNu = 0) : ∀ᵐ ν ∂wNu, g ν = 0 := by
  set f : ℝ → ℂ := fun ν => (ENNReal.ofReal (klW ν)).toReal • g ν
  have hloc : LocallyIntegrableOn f (Ioi 0) (volume : Measure ℝ) := by
    rw [locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed]
    intro K hKs hK
    have hKm : MeasurableSet K := hK.isClosed.measurableSet
    have hχ : MemLp (K.indicator fun _ => (1 : ℂ)) 2 wNu :=
      memLp_indicator_const 2 hKm.nullMeasurableSet 1 (Or.inr hK.measure_lt_top.ne)
    have hint := hχ.integrable_mul hg
    rw [wNu, integrable_withDensity_iff_integrable_smul' measurable_klW_dens
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)] at hint
    have hK' : IntegrableOn (fun ν => (ENNReal.ofReal (klW ν)).toReal •
        ((K.indicator fun _ => (1 : ℂ)) ν * g ν)) K ((volume : Measure ℝ).restrict (Ioi 0)) := hint.integrableOn
    have e : ((volume : Measure ℝ).restrict (Ioi 0)).restrict K = (volume : Measure ℝ).restrict K := by
      rw [Measure.restrict_restrict hKm, inter_eq_left.2 hKs]
    have hK'' : IntegrableOn (fun ν => (ENNReal.ofReal (klW ν)).toReal •
        ((K.indicator fun _ => (1 : ℂ)) ν * g ν)) K (volume : Measure ℝ) := by
      unfold IntegrableOn; rw [← e]; exact hK'
    refine hK''.congr_fun (fun ν hν => ?_) hKm
    simp only [f, Set.indicator_of_mem hν, one_mul]
  have h1 := isOpen_Ioi.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc (fun r r_diff r_supp r_sub => by
    have hr : IsKTest fun ν => (r ν : ℂ) :=
      ⟨Complex.ofRealCLM.contDiff.comp r_diff, r_supp.comp_left Complex.ofReal_zero,
        (closure_mono (Function.support_comp_subset Complex.ofReal_zero r)).trans r_sub⟩
    have := h0 _ hr
    rw [wNu, integral_withDensity_eq_integral_toReal_smul measurable_klW_dens
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)] at this
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi (0 : ℝ)) (fun ν hν => by
      rw [image_eq_zero_of_notMem_tsupport (fun h => hν (r_sub h)), zero_smul]), ← this]
    refine setIntegral_congr_fun measurableSet_Ioi (fun ν _ => ?_)
    simp only [f, Complex.conj_ofReal, Complex.real_smul]; ring)
  have h2 : ∀ᵐ ν ∂(volume : Measure ℝ).restrict (Ioi 0), g ν = 0 := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards [h1] with ν hν hν0
    have := hν hν0
    simp only [f, Complex.real_smul, mul_eq_zero, Complex.ofReal_eq_zero,
      ENNReal.toReal_ofReal (klW_pos hν0).le, (klW_pos hν0).ne', false_or] at this
    exact this
  exact (withDensity_absolutelyContinuous _ _).ae_le h2

/-- The KL test functions as a subset of `L²(w dν)`. -/
def testSetW : Set (Lp ℂ 2 wNu) := {f | ∃ h : ℝ → ℂ, ∃ hh : IsKTest h, f = (memLp_wNu hh).toLp h}

/-- **Density of the products**: `G ⊥ φ ⊗ h` for all `φ, h` forces `G = 0`. -/
theorem eq_zero_of_inner_Hfun
    (hG : ∀ (φ h : ℝ → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ) (hφ0 : (0 : ℝ) ∉ tsupport φ)
      (hh : IsKTest h), inner ℂ ((memLp_Hfun hφc hφs hφ0 hh).toLp (Hfun φ h)) G = 0) : G = 0 := by
  have : Fact ((2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞)) := ⟨ENNReal.ofNat_ne_top⟩
  obtain ⟨D, hDS, hDc, hSD⟩ := (TopologicalSpace.IsSeparable.of_separableSpace testSetW).exists_countable_dense_subset
  have hch : ∀ f : D, ∃ h : ℝ → ℂ, ∃ hh : IsKTest h, (f : Lp ℂ 2 wNu) = (memLp_wNu hh).toLp h :=
    fun f => hDS f.2
  choose H hH hHeq using hch
  haveI : Countable D := hDc.to_subtype
  have hall : ∀ᵐ k, ∀ f : D, mH G (H f) k = 0 := ae_all_iff.2 fun f => mH_ae_eq_zero hG (hH f)
  -- slices
  have hsm : StronglyMeasurable (G : ℝ × ℝ → ℂ) := Lp.stronglyMeasurable G
  have hsq : Integrable (fun p => ‖(G : ℝ × ℝ → ℂ) p‖ ^ 2) ((volume : Measure ℝ).prod wNu) :=
    (memLp_two_iff_integrable_sq_norm (Lp.memLp G).aestronglyMeasurable).1 (Lp.memLp G)
  have hsl : ∀ᵐ k, MemLp (fun ν => (G : ℝ × ℝ → ℂ) (k, ν)) 2 wNu := by
    filter_upwards [hsq.prod_right_ae] with k hk
    have hm : AEStronglyMeasurable (fun ν => (G : ℝ × ℝ → ℂ) (k, ν)) wNu :=
      (hsm.comp_measurable measurable_prodMk_left).aestronglyMeasurable
    exact (memLp_two_iff_integrable_sq_norm hm).2 hk
  have hfib : ∀ᵐ k, ∀ᵐ ν ∂wNu, (G : ℝ × ℝ → ℂ) (k, ν) = 0 := by
    filter_upwards [hall, hsl] with k hk hk2
    refine ae_eq_zero_of_forall_test hk2 (fun h hh => ?_)
    -- `inner (toLp h) G_k = m_h(k)`, continuous in the first slot, zero on `D`
    have hin : ∀ (h : ℝ → ℂ) (hh : IsKTest h), inner ℂ ((memLp_wNu hh).toLp h) (hk2.toLp _) = mH G h k := by
      intro h hh
      rw [L2.inner_def, mH]
      refine integral_congr_ae ?_
      filter_upwards [(memLp_wNu hh).coeFn_toLp, hk2.coeFn_toLp] with ν h1 h2
      rw [h1, h2, RCLike.inner_apply']
    have hcl : IsClosed {f : Lp ℂ 2 wNu | inner ℂ f (hk2.toLp _) = 0} :=
      isClosed_eq (continuous_inner.comp (continuous_id.prodMk continuous_const)) continuous_const
    have hD : D ⊆ {f : Lp ℂ 2 wNu | inner ℂ f (hk2.toLp _) = 0} := fun f hf => by
      simp only [mem_setOf_eq]
      have e1 : f = (memLp_wNu (hH ⟨f, hf⟩)).toLp (H ⟨f, hf⟩) := hHeq ⟨f, hf⟩
      rw [e1, hin _ (hH ⟨f, hf⟩)]
      exact hk ⟨f, hf⟩
    have hmem := (hcl.closure_subset_iff.2 hD) (hSD ⟨h, hh, rfl⟩)
    simp only [mem_setOf_eq, hin h hh] at hmem
    exact hmem
  rw [Lp.eq_zero_iff_ae_eq_zero]
  have hms : MeasurableSet {p : ℝ × ℝ | (G : ℝ × ℝ → ℂ) p = 0} :=
    hsm.measurable (measurableSet_singleton 0)
  have h3 : ∀ᵐ p ∂((volume : Measure ℝ).prod wNu), (G : ℝ × ℝ → ℂ) p = 0 :=
    (Measure.ae_prod_iff_ae_ae hms).2 hfib
  exact h3

/-- `klU` as a linear isometry. -/
noncomputable def klUi : Lp ℂ 2 (volume : Measure UpperHalfPlane) →ₗᵢ[ℂ] Lp ℂ 2 muU :=
  { (klU : Lp ℂ 2 (volume : Measure UpperHalfPlane) →ₗ[ℂ] Lp ℂ 2 muU) with norm_map' := norm_klU }

lemma klUi_apply (u : Lp ℂ 2 (volume : Measure UpperHalfPlane)) : klUi u = klU u := rfl

/-- **`klU` is surjective.** -/
theorem klU_surjective : Function.Surjective klU := by
  set K : Submodule ℂ (Lp ℂ 2 muU) := LinearMap.range (klU : Lp ℂ 2 (volume : Measure UpperHalfPlane) →ₗ[ℂ] Lp ℂ 2 muU)
  have hc : IsComplete (K : Set (Lp ℂ 2 muU)) := by
    have : (K : Set (Lp ℂ 2 muU)) = range klUi := by
      ext v; simp [K, klUi_apply]
    rw [this]
    exact klUi.isometry.isUniformInducing.isComplete_range
  have : CompleteSpace K := hc.completeSpace_coe
  have hbot : Kᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro G hG
    refine eq_zero_of_inner_Hfun (fun φ h hφc hφs hφ0 hh => ?_)
    have hmem : (memLp_Hfun hφc hφs hφ0 hh).toLp (Hfun φ h) ∈ K :=
      ⟨_, klU_PsiH hφc hφs hφ0 hh⟩
    exact Submodule.inner_right_of_mem_orthogonal hmem hG
  have htop := (Submodule.orthogonal_eq_bot_iff (K := K)).1 hbot
  intro v
  have : v ∈ K := htop ▸ Submodule.mem_top
  obtain ⟨u, hu⟩ := this
  exact ⟨u, hu⟩

/-- **The KL picture of `L²(ℍ)` is unitary.** -/
noncomputable def klUequiv : Lp ℂ 2 (volume : Measure UpperHalfPlane) ≃ₗᵢ[ℂ] Lp ℂ 2 muU :=
  LinearIsometryEquiv.ofSurjective klUi klU_surjective

lemma klUequiv_apply (u : Lp ℂ 2 (volume : Measure UpperHalfPlane)) : klUequiv u = klU u := rfl

end dens

end Qschubert
