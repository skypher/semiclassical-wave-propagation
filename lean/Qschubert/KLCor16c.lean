import Qschubert.KLCor16b

/-!
# The Sobolev bound on `M` with a continuous representative

On a surface of injectivity radius at least `r₀`, every `u ∈ Dom(-Δ_M)` has a continuous representative bounded by `K (‖u‖ + ‖Δ_M u‖)`, with `K` depending on `r₀` only (`sobolev_M`).
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set Physicslib4.Spectral.Unbounded UpperHalfPlane Metric
open scoped ENNReal InnerProductSpace MatrixGroups Pointwise ComplexConjugate

local notation "L2H'" => Lp ℂ 2 (volume : Measure UpperHalfPlane)

/-- A continuous representative on the fixed chart. -/
theorem local_rep (v : negLapH.domain) : ∃ f : ℂ → ℂ, Continuous f ∧
    (∀ᵐ z : ℍ ∂(volume : Measure ℍ), dist (z : ℂ) Complex.I < 1 / 4 → (v : L2H') z = f z) ∧
    ∀ ζ, ‖f ζ‖ ≤ Kloc * (‖(v : L2H')‖ + ‖negLapH v‖) := by
  obtain ⟨hc, hae, hbd⟩ := sobolevC (eucL chiT v) (hEuc v) (laplacian_eucL_chi v)
  refine ⟨_, hc, ?_, fun ζ => (hbd ζ).trans ?_⟩
  · have hC : ∀ᵐ ζ ∂(volume : Measure ℂ), eucFun chiT (v : L2H') ζ = sobRep (eucL chiT v) (hEuc v) ζ := by
      filter_upwards [hae, eucL_ae chiT (v : L2H')] with ζ h1 h2
      rw [← h2, h1]
    have hH : ∀ᵐ (z : ℍ) ∂(volume : Measure ℍ), eucFun chiT (v : L2H') (z : ℂ) = sobRep (eucL chiT v) (hEuc v) (z : ℂ) := by
      rw [ae_iff] at hC ⊢
      exact volume_preimage_coe_null' hC
    filter_upwards [hH, repL2_ae (v : L2H')] with z h1 h2 hz
    rw [h2, ← h1]
    have hχ : (chiT : ℂ → ℂ) z = 1 := chiT_eq_one hz.le
    rw [eucFun, hχ, one_mul, ofComplex_apply]
  · have h1 := norm_eucL_le chiT (v : L2H')
    have h2 := norm_hEuc_le v
    have hw := norm_nonneg (memLp_weightW.toLp weightW)
    have hc' := norm_nonneg twoPiSq⁻¹
    have hs := supCy_nonneg chiT
    unfold Kloc
    have : ‖eucL chiT (v : L2H')‖ + ‖twoPiSq⁻¹‖ * ‖hEuc v‖
        ≤ (supCy chiT + ‖twoPiSq⁻¹‖ * Kh) * (‖(v : L2H')‖ + ‖negLapH v‖) := by
      nlinarith [mul_le_mul_of_nonneg_left h2 hc', norm_nonneg (negLapH v), norm_nonneg (v : L2H')]
    calc ‖memLp_weightW.toLp weightW‖ * (‖eucL chiT (v : L2H')‖ + ‖twoPiSq⁻¹‖ * ‖hEuc v‖)
        ≤ ‖memLp_weightW.toLp weightW‖ * ((supCy chiT + ‖twoPiSq⁻¹‖ * Kh) * (‖(v : L2H')‖ + ‖negLapH v‖)) :=
          mul_le_mul_of_nonneg_left this hw
      _ = _ := by ring

/-! ### The bumps -/

/-- The bump at `i`, `1` on `B(i, r)`, support `B(i, 2r)`. -/
noncomputable def bR (r : ℝ) (hr : 0 < r) : ContDiffBump Complex.I := ⟨r, 2 * r, hr, by linarith⟩

noncomputable def chiR (r : ℝ) (hr : 0 < r) (h1 : 2 * r < 1) : testFn := ⟨_, isTestFn_bump (bR r hr) h1⟩

lemma chiR_apply {r : ℝ} {hr : 0 < r} {h1 : 2 * r < 1} (ζ : ℂ) : (chiR r hr h1 : ℂ → ℂ) ζ = ((bR r hr ζ : ℝ) : ℂ) := rfl

lemma isRealT_chiR {r : ℝ} {hr : 0 < r} {h1 : 2 * r < 1} : IsRealT (chiR r hr h1) := fun ζ => by
  rw [chiR_apply, Complex.conj_ofReal]

lemma chiR_one {r : ℝ} {hr : 0 < r} {h1 : 2 * r < 1} {ζ : ℂ} (h : dist ζ Complex.I ≤ r) : (chiR r hr h1 : ℂ → ℂ) ζ = 1 := by
  rw [chiR_apply, (bR r hr).one_of_mem_closedBall (by rw [mem_closedBall]; exact h)]; simp

lemma chiR_ne {r : ℝ} {hr : 0 < r} {h1 : 2 * r < 1} {ζ : ℂ} (h : (chiR r hr h1 : ℂ → ℂ) ζ ≠ 0) : dist ζ Complex.I < 2 * r := by
  rw [chiR_apply] at h
  have h2 : (bR r hr) ζ ≠ 0 := fun h0 => h (by rw [h0]; simp)
  have h3 : ζ ∈ Function.support (bR r hr) := h2
  rw [(bR r hr).support_eq] at h3
  exact h3

lemma oneOn_chiR {r r' : ℝ} {hr : 0 < r} {h1 : 2 * r < 1} {hr' : 0 < r'} {h1' : 2 * r' < 1} (h : 2 * r ≤ r') :
    OneOn (chiR r' hr' h1') (chiR r hr h1) := fun w hw => by
  have hs : tsupport (chiR r hr h1 : ℂ → ℂ) ⊆ tsupport (bR r hr) :=
    tsupport_comp_subset (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero _
  have h2 := hs hw
  rw [(bR r hr).tsupport_eq, mem_closedBall] at h2
  exact chiR_one (h2.trans h)

/-- A Euclidean radius at `i` inside the hyperbolic ball of radius `r₀`. -/
noncomputable def rho (r₀ : ℝ) : ℝ := min (1 / 8) (Real.sqrt (Real.cosh r₀ - 1))

lemma cosh_sub_pos {r₀ : ℝ} (h : 0 < r₀) : 0 < Real.cosh r₀ - 1 := by
  have := Real.one_lt_cosh.2 h.ne'
  linarith

lemma rho_pos {r₀ : ℝ} (h : 0 < r₀) : 0 < rho r₀ :=
  lt_min (by norm_num) (Real.sqrt_pos.2 (cosh_sub_pos h))

lemma rho_le {r₀ : ℝ} : rho r₀ ≤ 1 / 8 := min_le_left _ _

lemma dist_lt_of_near {r₀ : ℝ} (h0 : 0 < r₀) {z : ℍ} (h : dist (z : ℂ) Complex.I ≤ rho r₀) : dist z UpperHalfPlane.I < r₀ := by
  have hd : dist (z : ℂ) Complex.I ≤ 1 / 8 := h.trans rho_le
  have him : 7 / 8 ≤ z.im := by
    have h1 : |(z : ℂ).im - 1| ≤ dist (z : ℂ) Complex.I := by
      rw [Complex.dist_eq]
      have := Complex.abs_im_le_norm ((z : ℂ) - Complex.I)
      simpa using this
    have h2 := (abs_le.1 (h1.trans hd)).1
    have e : (z : ℂ).im = z.im := rfl
    rw [e] at h2
    linarith
  have hsq : dist (z : ℂ) Complex.I ^ 2 ≤ Real.cosh r₀ - 1 := by
    have h3 : dist (z : ℂ) Complex.I ≤ Real.sqrt (Real.cosh r₀ - 1) := h.trans (min_le_right _ _)
    calc _ ≤ Real.sqrt (Real.cosh r₀ - 1) ^ 2 := pow_le_pow_left₀ dist_nonneg h3 2
      _ = _ := Real.sq_sqrt (cosh_sub_pos h0).le
  have hc := UpperHalfPlane.cosh_dist z UpperHalfPlane.I
  have hI : ((UpperHalfPlane.I : ℍ) : ℂ) = Complex.I := rfl
  have hIm : (UpperHalfPlane.I : ℍ).im = 1 := rfl
  rw [hI, hIm, mul_one] at hc
  have hlt : Real.cosh (dist z UpperHalfPlane.I) < Real.cosh r₀ := by
    rw [hc]
    have hpos := cosh_sub_pos h0
    have hy : 0 < 2 * z.im := by linarith
    have : dist (z : ℂ) Complex.I ^ 2 / (2 * z.im) ≤ (Real.cosh r₀ - 1) * (4 / 7) := by
      rw [div_le_iff₀ hy]
      nlinarith [sq_nonneg (dist (z : ℂ) Complex.I)]
    linarith
  have := Real.cosh_lt_cosh.1 hlt
  rwa [abs_of_nonneg dist_nonneg, abs_of_pos h0] at this

lemma injT_chiR {Γ : Subgroup PGL(2, ℝ)} [ProperlyDiscontinuousSMul Γ ℍ] {r₀ : ℝ} (h0 : 0 < r₀) (hΓ : InjRadGe Γ r₀)
    {r : ℝ} {hr : 0 < r} {h1 : 2 * r < 1} (h : 2 * r ≤ rho r₀) : InjT Γ (chiR r hr h1) := by
  intro z γ hγ hz
  by_contra hc
  have b1 := dist_lt_of_near h0 ((chiR_ne hz).le.trans h)
  have b2 := dist_lt_of_near h0 ((chiR_ne hc).le.trans h)
  have h2 := hΓ γ hγ z
  have t : dist z (γ • z) ≤ dist z UpperHalfPlane.I + dist UpperHalfPlane.I (γ • z) := dist_triangle _ _ _
  rw [dist_comm UpperHalfPlane.I] at t
  linarith

/-- **The chart at `i`**, uniformly over all groups of injectivity radius at least `r₀`. -/
theorem chart_rep {r₀ : ℝ} (h0 : 0 < r₀) : ∃ K r : ℝ, 0 ≤ K ∧ 0 < r ∧
    ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], InjRadGe Γ r₀ → ∀ u : (negLapMH Γ).domain,
      ∃ f : ℂ → ℂ, Continuous f ∧ (∀ᵐ z : ℍ ∂(volume : Measure ℍ), dist (z : ℂ) Complex.I < r → liftM Γ (u : Lp ℂ 2 (surfMeasure Γ)) z = f z) ∧
        ∀ ζ, ‖f ζ‖ ≤ K * (‖(u : Lp ℂ 2 (surfMeasure Γ))‖ + ‖negLapMH Γ u‖) := by
  have hρ := rho_pos h0
  have hρ8 : rho r₀ ≤ 1 / 8 := rho_le
  have r0 : 0 < rho r₀ / 2 := by linarith
  have r1 : 0 < rho r₀ / 4 := by linarith
  have r2 : 0 < rho r₀ / 8 := by linarith
  have s0 : 2 * (rho r₀ / 2) < 1 := by linarith
  have s1 : 2 * (rho r₀ / 4) < 1 := by linarith
  have s2 : 2 * (rho r₀ / 8) < 1 := by linarith
  set χ₀ := chiR (rho r₀ / 2) r0 s0
  set χ₁ := chiR (rho r₀ / 4) r1 s1
  set χ₂ := chiR (rho r₀ / 8) r2 s2
  have hK : 0 ≤ Kloc * (supT χ₂ + Kdom χ₂ χ₁ χ₀) :=
    mul_nonneg Kloc_nonneg (add_nonneg (supT_nonneg _) (Kdom_nonneg _ _ _))
  refine ⟨Kloc * (supT χ₂ + Kdom χ₂ χ₁ χ₀), rho r₀ / 8, hK, r2, ?_⟩
  intro Γ _ hΓ u
  have hi2 : CutB Γ χ₂ 1 := cutB_of_injT (injT_chiR h0 hΓ (by linarith))
  have hi1 : CutB Γ χ₁ 1 := cutB_of_injT (injT_chiR h0 hΓ (by linarith))
  have hi0 : CutB Γ χ₀ 1 := cutB_of_injT (injT_chiR h0 hΓ (by linarith))
  have h21 : OneOn χ₁ χ₂ := oneOn_chiR (by linarith)
  have h10 : OneOn χ₀ χ₁ := oneOn_chiR (by linarith)
  obtain ⟨hv, hb⟩ := cut_dom (isRealT_chiR (hr := r2) (h1 := s2)) (isRealT_chiR (hr := r1) (h1 := s1)) (isRealT_chiR (hr := r0) (h1 := s0))
    hi2 hi1 hi0 h21 h10 u
  rw [one_mul, one_mul] at hb
  obtain ⟨f, hfc, hfa, hfb⟩ := local_rep ⟨cutV hi2 (u : Lp ℂ 2 (surfMeasure Γ)), hv⟩
  refine ⟨f, hfc, ?_, fun ζ => (hfb ζ).trans ?_⟩
  · filter_upwards [hfa, cutV_ae hi2 (u : Lp ℂ 2 (surfMeasure Γ))] with z h1 h2 hz
    have hz' : dist (z : ℂ) Complex.I < 1 / 4 := by linarith
    have e := h1 hz'
    have e' : (cutV hi2 (u : Lp ℂ 2 (surfMeasure Γ)) : L2H') z = f z := e
    rw [h2] at e'
    rwa [show (χ₂ : ℂ → ℂ) z = 1 from chiR_one hz.le, one_mul] at e'
  · have hn := norm_cutV_le hi2 (u : Lp ℂ 2 (surfMeasure Γ))
    rw [mul_one] at hn
    have hU := norm_nonneg (u : Lp ℂ 2 (surfMeasure Γ))
    have hW := norm_nonneg (negLapMH Γ u)
    have hS := supT_nonneg χ₂
    have hsum : ‖cutV hi2 (u : Lp ℂ 2 (surfMeasure Γ))‖ + ‖negLapH ⟨cutV hi2 (u : Lp ℂ 2 (surfMeasure Γ)), hv⟩‖
        ≤ (supT χ₂ + Kdom χ₂ χ₁ χ₀) * (‖(u : Lp ℂ 2 (surfMeasure Γ))‖ + ‖negLapMH Γ u‖) := by
      nlinarith [mul_nonneg hS hW]
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hsum Kloc_nonneg

/-! ### Moving the chart -/

lemma injRadGe_conj {Γ : Subgroup PGL(2, ℝ)} {r₀ : ℝ} (p : PGL(2, ℝ)) (hΓ : InjRadGe Γ r₀) : InjRadGe (conjS p Γ) r₀ := by
  intro γ' hγ' z
  obtain ⟨γ, rfl⟩ := (conjE p Γ).surjective γ'
  have hγ : γ ≠ 1 := fun h => hγ' (by rw [h, map_one])
  have h1 := hΓ γ hγ (p⁻¹ • z)
  have e : conjE p Γ γ • z = p • (γ • p⁻¹ • z) := by
    rw [← conjE_smul, smul_inv_smul]
  rw [e]
  have e2 : dist z (p • (γ • p⁻¹ • z)) = dist (p⁻¹ • z) (γ • p⁻¹ • z) := by
    rw [← dist_smul p (p⁻¹ • z), smul_inv_smul]
  rw [e2]
  exact h1

lemma exists_pgl_to_I (z₀ : ℍ) : ∃ p : PGL(2, ℝ), p • z₀ = UpperHalfPlane.I := by
  refine ⟨Matrix.SpecialLinearGroup.toPGL (transH z₀)⁻¹, ?_⟩
  rw [toPGL_smul, inv_smul_eq_iff]
  apply UpperHalfPlane.ext
  rw [transH_coe]
  apply Complex.ext <;> simp

/-- A patch at every point. -/
theorem patch_rep {r₀ K r : ℝ} (hr : 0 < r)
    (hrep : ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], InjRadGe Γ r₀ → ∀ u : (negLapMH Γ).domain,
      ∃ f : ℂ → ℂ, Continuous f ∧ (∀ᵐ z : ℍ ∂(volume : Measure ℍ), dist (z : ℂ) Complex.I < r → liftM Γ (u : Lp ℂ 2 (surfMeasure Γ)) z = f z) ∧
        ∀ ζ, ‖f ζ‖ ≤ K * (‖(u : Lp ℂ 2 (surfMeasure Γ))‖ + ‖negLapMH Γ u‖))
    (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ] (hΓ : InjRadGe Γ r₀) (u : (negLapMH Γ).domain) (z₀ : ℍ) :
    ∃ F : ℍ → ℂ, Continuous F ∧ ∃ V : Set ℍ, IsOpen V ∧ z₀ ∈ V ∧ (∀ᵐ w ∂(volume : Measure ℍ), w ∈ V → liftM Γ (u : Lp ℂ 2 (surfMeasure Γ)) w = F w) ∧
      ∀ w, ‖F w‖ ≤ K * (‖(u : Lp ℂ 2 (surfMeasure Γ))‖ + ‖negLapMH Γ u‖) := by
  obtain ⟨p, hp⟩ := exists_pgl_to_I z₀
  set v : Lp ℂ 2 (surfMeasure (conjS p Γ)) := (conjU p Γ).symm (u : Lp ℂ 2 (surfMeasure Γ)) with hv
  obtain ⟨hvd, hAv⟩ : ∃ h : v ∈ (negLapMH (conjS p Γ)).domain,
      negLapMH (conjS p Γ) ⟨v, h⟩ = (conjU p Γ).symm (negLapMH Γ u) :=
    friedrichsExt_U2 (negLapM Γ) (negLapM (conjS p Γ)) (negLapM_hasDenseDomain Γ) (negLapM_hasDenseDomain _)
      (intertwines_conj_symm p Γ) (intertwines_conj p Γ) u
  obtain ⟨f, hfc, hfa, hfb⟩ := hrep (conjS p Γ) (injRadGe_conj p hΓ) ⟨v, hvd⟩
  have hsmul : Continuous fun w : ℍ => ((p • w : ℍ) : ℂ) := UpperHalfPlane.continuous_coe.comp (continuous_const_smul p)
  refine ⟨fun w => f ((p • w : ℍ) : ℂ), hfc.comp hsmul, {w | dist ((p • w : ℍ) : ℂ) Complex.I < r},
    isOpen_lt (hsmul.dist continuous_const) continuous_const, ?_, ?_, fun w => ?_⟩
  · show dist ((p • z₀ : ℍ) : ℂ) Complex.I < r
    rw [hp]
    show dist Complex.I Complex.I < r
    rw [dist_self]; exact hr
  · have h1 := (measurePreserving_smul p (volume : Measure ℍ)).quasiMeasurePreserving.ae hfa
    have hU : conjU p Γ v = (u : Lp ℂ 2 (surfMeasure Γ)) := (conjU p Γ).apply_symm_apply _
    have h2 := ae_comp_surfMk Γ (conjU_ae p Γ v)
    filter_upwards [h1, h2] with w e1 e2 hw
    have e3 := e1 hw
    rw [hU] at e2
    have e4 : liftM Γ (u : Lp ℂ 2 (surfMeasure Γ)) w = liftM (conjS p Γ) v (p • w) := e2
    rw [e4]
    exact e3
  · refine (hfb _).trans (le_of_eq ?_)
    congr 2
    · exact LinearIsometryEquiv.norm_map _ _
    · rw [hAv]; exact LinearIsometryEquiv.norm_map _ _

/-- **Gluing** local continuous representatives. -/
theorem glue_rep {u' : ℍ → ℂ} {B : ℝ}
    (hp : ∀ z₀ : ℍ, ∃ F : ℍ → ℂ, Continuous F ∧ ∃ V : Set ℍ, IsOpen V ∧ z₀ ∈ V ∧ (∀ᵐ w ∂(volume : Measure ℍ), w ∈ V → u' w = F w) ∧ ∀ w, ‖F w‖ ≤ B) :
    ∃ F : ℍ → ℂ, Continuous F ∧ F =ᵐ[volume] u' ∧ ∀ z, ‖F z‖ ≤ B := by
  choose Fz hFc V hVo hVm hFa hFb using hp
  have hag : ∀ a b : ℍ, ∀ w ∈ V a ∩ V b, Fz a w = Fz b w := by
    intro a b
    have hO : IsOpen (V a ∩ V b) := (hVo a).inter (hVo b)
    have hae : Fz a =ᵐ[(volume : Measure ℍ).restrict (V a ∩ V b)] Fz b := by
      rw [Filter.EventuallyEq, ae_restrict_iff' hO.measurableSet]
      filter_upwards [hFa a, hFa b] with w h1 h2 hw
      rw [← h1 hw.1, ← h2 hw.2]
    exact Measure.eqOn_open_of_ae_eq hae hO (hFc a).continuousOn (hFc b).continuousOn
  set F : ℍ → ℂ := fun z => Fz z z with hF
  have key : ∀ z₀, ∀ z ∈ V z₀, F z = Fz z₀ z := fun z₀ z hz => hag z z₀ z ⟨hVm z, hz⟩
  refine ⟨F, ?_, ?_, fun z => hFb z z⟩
  · refine continuous_iff_continuousAt.2 fun z₀ => ?_
    refine (hFc z₀).continuousAt.congr ?_
    filter_upwards [(hVo z₀).mem_nhds (hVm z₀)] with z hz
    exact (key z₀ z hz).symm
  · obtain ⟨T, hT, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable V hVo
    have hall : ∀ᵐ w ∂(volume : Measure ℍ), ∀ z₀ ∈ T, w ∈ V z₀ → u' w = Fz z₀ w :=
      (ae_ball_iff hT).2 fun z₀ _ => hFa z₀
    filter_upwards [hall] with w hw
    have hmem : w ∈ ⋃ i ∈ T, V i := by
      rw [hTU]; exact mem_iUnion.2 ⟨w, hVm w⟩
    obtain ⟨z₀, hz₀, hwz⟩ := mem_iUnion₂.1 hmem
    rw [key z₀ w hwz, hw z₀ hz₀ hwz]

/-- **The Sobolev bound on `M`.** -/
theorem sobolev_M {r₀ : ℝ} (h0 : 0 < r₀) : ∃ K : ℝ, 0 ≤ K ∧
    ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], InjRadGe Γ r₀ → ∀ u : (negLapMH Γ).domain,
      ∃ f : Surf Γ → ℂ, Continuous f ∧ f =ᵐ[surfMeasure Γ] ⇑(u : Lp ℂ 2 (surfMeasure Γ)) ∧
        ∀ x, ‖f x‖ ≤ K * (‖(u : Lp ℂ 2 (surfMeasure Γ))‖ + ‖negLapMH Γ u‖) := by
  obtain ⟨K, r, hK, hr, hrep⟩ := chart_rep h0
  refine ⟨K, hK, ?_⟩
  intro Γ _ hΓ u
  obtain ⟨F, hFc, hFa, hFb⟩ := glue_rep (patch_rep hr hrep Γ hΓ u)
  have hinv : ∀ (γ : Γ) (z : ℍ), F (γ • z) = F z := by
    intro γ
    have hcγ : Continuous fun z : ℍ => F (γ • z) := hFc.comp (continuous_const_smul γ)
    refine congrFun ((Continuous.ae_eq_iff_eq (volume : Measure ℍ) hcγ hFc).1 ?_)
    have h1 := (measurePreserving_smul γ (volume : Measure ℍ)).quasiMeasurePreserving.ae_eq_comp hFa
    filter_upwards [h1, hFa] with z e1 e2
    have e1' : F (γ • z) = liftM Γ (u : Lp ℂ 2 (surfMeasure Γ)) (γ • z) := e1
    rw [e1', e2, liftM_smul]
  have hs : ∀ a b : ℍ, (MulAction.orbitRel Γ ℍ) a b → F a = F b := by
    rintro a b ⟨γ, rfl⟩
    exact hinv γ b
  refine ⟨Quotient.lift F hs, hFc.quotient_lift hs, ?_, ?_⟩
  · have hml : Measurable (Quotient.lift F hs : Surf Γ → ℂ) := measurable_from_quotient.2 hFc.measurable
    have hm : Measurable fun x : Surf Γ => Quotient.lift F hs x - (u : Lp ℂ 2 (surfMeasure Γ)) x :=
      hml.sub (Lp.stronglyMeasurable _).measurable
    have h := ae_eq_zero_of_lift Γ hm (by
      filter_upwards [hFa] with z hz
      show F z - liftM Γ (u : Lp ℂ 2 (surfMeasure Γ)) z = 0
      rw [hz, sub_self])
    filter_upwards [h] with x hx
    exact sub_eq_zero.1 hx
  · intro x
    induction x using Quotient.inductionOn with | _ z
    exact hFb z

end Qschubert
