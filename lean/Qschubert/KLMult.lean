import Qschubert.KLWC
import Qschubert.FdbBound

/-!
# Smooth bounded multipliers on `Dom(-Δ)`

For `h` smooth on `ℍ` with `h`, `Xh`, `Yh`, `Δh` bounded (`Adm h C`) and `u ∈ Dom(-Δ)`:
`hu ∈ Dom(-Δ)` (`mul_mem_domain`) and `Z(hu) = (Zh)u + h(Zu)` for `Z ∈ {X, Y}` (`domZ_mul`). The domain statement uses the
Friedrichs construction: `hu` lies in the form space (`mulFormE`), and its form pairing with test functions is computed
by `inner_local_lap`.
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set
open scoped ENNReal ContDiff Manifold

local notation "L2H'" => Lp ℂ 2 (volume : Measure UpperHalfPlane)

/-- Smooth on `ℍ` and bounded by `C` there. -/
structure SB (g : ℂ → ℝ) (C : ℝ) : Prop where
  s : ∀ w : ℂ, 0 < w.im → ContDiffAt ℝ ∞ g w
  b : ∀ w : ℂ, 0 < w.im → |g w| ≤ C

lemma contDiffAt_vfR (v : ℂ) {g : ℂ → ℝ} {w : ℂ} (hs : ContDiffAt ℝ ∞ g w) : ContDiffAt ℝ ∞ (vfR v g) w :=
  Complex.imCLM.contDiff.contDiffAt.mul ((hs.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const)

/-- `Δ = X² + Y² - Y` on real functions. -/
noncomputable def lapRv (g : ℂ → ℝ) : ℂ → ℝ := fun w =>
  vfR 1 (vfR 1 g) w + vfR Complex.I (vfR Complex.I g) w - vfR Complex.I g w

lemma contDiffAt_lapRv {g : ℂ → ℝ} {w : ℂ} (hw : 0 < w.im) (hs : ∀ w : ℂ, 0 < w.im → ContDiffAt ℝ ∞ g w) :
    ContDiffAt ℝ ∞ (lapRv g) w :=
  ((contDiffAt_vfR 1 (contDiffAt_vfR 1 (hs w hw))).add (contDiffAt_vfR _ (contDiffAt_vfR _ (hs w hw)))).sub
    (contDiffAt_vfR _ (hs w hw))

/-- Admissible multipliers. -/
structure Adm (h : ℂ → ℝ) (C : ℝ) : Prop where
  s : ∀ w : ℂ, 0 < w.im → ContDiffAt ℝ ∞ h w
  b0 : ∀ w : ℂ, 0 < w.im → |h w| ≤ C
  bX : ∀ w : ℂ, 0 < w.im → |vfR 1 h w| ≤ C
  bY : ∀ w : ℂ, 0 < w.im → |vfR Complex.I h w| ≤ C
  bL : ∀ w : ℂ, 0 < w.im → |lapRv h w| ≤ C

lemma Adm.sb {h : ℂ → ℝ} {C : ℝ} (H : Adm h C) : SB h C := ⟨H.s, H.b0⟩
lemma Adm.sbX {h : ℂ → ℝ} {C : ℝ} (H : Adm h C) : SB (vfR 1 h) C := ⟨fun w hw => contDiffAt_vfR _ (H.s w hw), H.bX⟩
lemma Adm.sbY {h : ℂ → ℝ} {C : ℝ} (H : Adm h C) : SB (vfR Complex.I h) C := ⟨fun w hw => contDiffAt_vfR _ (H.s w hw), H.bY⟩
lemma Adm.sbL {h : ℂ → ℝ} {C : ℝ} (H : Adm h C) : SB (lapRv h) C := ⟨fun w hw => contDiffAt_lapRv hw H.s, H.bL⟩

lemma SB.nonneg {g : ℂ → ℝ} {C : ℝ} (H : SB g C) : 0 ≤ C := (abs_nonneg _).trans (H.b Complex.I (by simp))

section mulCL

variable {g : ℂ → ℝ} {C : ℝ}

lemma SB.continuous (H : SB g C) : Continuous fun z : UpperHalfPlane => g (z : ℂ) :=
  continuous_iff_continuousAt.2 fun z =>
    (H.s (z : ℂ) z.im_pos).continuousAt.comp_of_eq UpperHalfPlane.continuous_coe.continuousAt rfl

lemma memLp_mulSB (H : SB g C) (u : L2H') : MemLp (fun z : UpperHalfPlane => ((g (z : ℂ) : ℝ) : ℂ) * u z) 2 volume :=
  (Lp.memLp u).of_le_mul (c := C) (((Complex.continuous_ofReal.comp H.continuous).aestronglyMeasurable).mul
    (Lp.aestronglyMeasurable u)) (Eventually.of_forall fun z => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (H.b _ z.im_pos) (norm_nonneg _))

/-- Multiplication by `g` on `L²(ℍ)`. -/
noncomputable def mulCL (H : SB g C) : L2H' →L[ℂ] L2H' :=
  LinearMap.mkContinuous
    { toFun := fun u => (memLp_mulSB H u).toLp _
      map_add' := fun u v => by
        apply Lp.ext
        filter_upwards [(memLp_mulSB H (u + v)).coeFn_toLp, (memLp_mulSB H u).coeFn_toLp, (memLp_mulSB H v).coeFn_toLp,
          Lp.coeFn_add u v, Lp.coeFn_add ((memLp_mulSB H u).toLp _) ((memLp_mulSB H v).toLp _)] with z h1 h2 h3 h4 h5
        rw [h1, h5]; simp only [Pi.add_apply]; rw [h2, h3, h4]; simp only [Pi.add_apply]; ring
      map_smul' := fun c u => by
        apply Lp.ext
        filter_upwards [(memLp_mulSB H (c • u)).coeFn_toLp, (memLp_mulSB H u).coeFn_toLp,
          Lp.coeFn_smul c u, Lp.coeFn_smul c ((memLp_mulSB H u).toLp _)] with z h1 h2 h3 h4
        simp only [RingHom.id_apply]
        rw [h1, h4]; simp only [Pi.smul_apply, smul_eq_mul]; rw [h2, h3]; simp only [Pi.smul_apply, smul_eq_mul]; ring }
    C (fun u => by
      refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
      filter_upwards [(memLp_mulSB H u).coeFn_toLp] with z h1
      show ‖((memLp_mulSB H u).toLp _ : L2H') z‖ ≤ _
      rw [h1, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (H.b _ z.im_pos) (norm_nonneg _))

lemma coe_mulCL (H : SB g C) (u : L2H') :
    (mulCL H u : UpperHalfPlane → ℂ) =ᵐ[volume] fun z => ((g (z : ℂ) : ℝ) : ℂ) * u z :=
  (memLp_mulSB H u).coeFn_toLp

lemma norm_mulCL_le (H : SB g C) (u : L2H') : ‖mulCL H u‖ ≤ C * ‖u‖ := by
  refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
  filter_upwards [coe_mulCL H u] with z h1
  rw [h1, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (H.b _ z.im_pos) (norm_nonneg _)

/-- `g · P` for a test function `P`. -/
noncomputable def mulHT (H : SB g C) (P : testFn) : testFn :=
  ⟨fun w => ((g w : ℝ) : ℂ) * (P : ℂ → ℂ) w,
    isTestFn_mul_of_contDiffAt (fun w hw => Complex.ofRealCLM.contDiff.contDiffAt.comp w (H.s w hw)) P.2⟩

lemma mulHT_coe (H : SB g C) (P : testFn) (w : ℂ) :
    ((mulHT H P : testFn) : ℂ → ℂ) w = ((g w : ℝ) : ℂ) * (P : ℂ → ℂ) w := rfl

lemma toL2_mulHT (H : SB g C) (P : testFn) : toL2 (mulHT H P) = mulCL H (toL2 P) := by
  apply Lp.ext
  filter_upwards [(memLp_comp_coe (mulHT H P).2).coeFn_toLp, coe_mulCL H (toL2 P), (memLp_comp_coe P.2).coeFn_toLp] with z h1 h2 h3
  show ((memLp_comp_coe (mulHT H P).2).toLp _ : L2H') z = _
  rw [h1, h2]
  show _ = _ * ((memLp_comp_coe P.2).toLp _ : L2H') z
  rw [h3]; rfl

/-- `⟪gP, u⟫ = ⟪P, gu⟫` for real `g`. -/
lemma inner_mulHT (H : SB g C) (P : testFn) (u : L2H') :
    inner ℂ (toL2 (mulHT H P)) u = inner ℂ (toL2 P) (mulCL H u) := by
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_comp_coe (mulHT H P).2).coeFn_toLp, (memLp_comp_coe P.2).coeFn_toLp, coe_mulCL H u] with z h1 h2 h3
  show inner ℂ (((memLp_comp_coe (mulHT H P).2).toLp _ : L2H') z) (u z)
    = inner ℂ (((memLp_comp_coe P.2).toLp _ : L2H') z) ((mulCL H u : L2H') z)
  rw [h1, h2, h3, RCLike.inner_apply', RCLike.inner_apply']
  simp only [Function.comp, mulHT_coe, map_mul, Complex.conj_ofReal]
  ring

end mulCL

section local_

lemma exists_cutoff (P : testFn) : ∃ η : testFn, ∀ w ∈ tsupport (P : ℂ → ℂ), (η : ℂ → ℂ) =ᶠ[𝓝 w] fun _ => 1 := by
  have hU : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
  obtain ⟨L, hL, hKL, hLU⟩ := exists_compact_between P.2.compact hU P.2.inside
  obtain ⟨f, h1, h0, -⟩ := exists_contMDiffMap_one_nhds_of_subset_interior (I := 𝓘(ℝ, ℂ)) (n := ⊤)
    (isClosed_tsupport _) hKL
  have hsm : ContDiff ℝ ∞ (f : ℂ → ℝ) := f.contMDiff.contDiff
  have hη : IsTestFn fun w => ((f w : ℝ) : ℂ) := by
    have hsup : tsupport (fun w => ((f w : ℝ) : ℂ)) ⊆ L :=
      closure_minimal (fun w hw => by
        by_contra hc
        exact hw (by simp [h0 w hc])) hL.isClosed
    exact ⟨Complex.ofRealCLM.contDiff.comp hsm, HasCompactSupport.intro hL (fun w hw => by simp [h0 w hw]),
      hsup.trans hLU⟩
  refine ⟨⟨_, hη⟩, fun w hw => ?_⟩
  filter_upwards [h1.filter_mono (nhds_le_nhdsSet hw)] with y hy
  show ((f y : ℝ) : ℂ) = 1
  rw [hy]; simp

lemma vfTest_local (v : ℂ) (c : testFn) {g : ℂ → ℝ} {w : ℂ} (hg : DifferentiableAt ℝ g w)
    (h : (c : ℂ → ℂ) =ᶠ[𝓝 w] fun y => ((g y : ℝ) : ℂ)) :
    ((vfTest v c : testFn) : ℂ → ℂ) w = ((vfR v g w : ℝ) : ℂ) := by
  rw [vfTest_coe, h.fderiv_eq]
  have hd : HasFDerivAt (fun y => ((g y : ℝ) : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ g w)) w :=
    Complex.ofRealCLM.hasFDerivAt.comp w hg.hasFDerivAt
  rw [hd.fderiv]
  simp [vfR]

lemma vfTest_local_ev (v : ℂ) (c : testFn) {g : ℂ → ℝ} {w : ℂ} (hw : 0 < w.im)
    (hs : ∀ w : ℂ, 0 < w.im → ContDiffAt ℝ ∞ g w)
    (h : (c : ℂ → ℂ) =ᶠ[𝓝 w] fun y => ((g y : ℝ) : ℂ)) :
    ((vfTest v c : testFn) : ℂ → ℂ) =ᶠ[𝓝 w] fun y => ((vfR v g y : ℝ) : ℂ) := by
  have hU : ∀ᶠ y in 𝓝 w, 0 < y.im := (isOpen_lt continuous_const Complex.continuous_im).mem_nhds hw
  filter_upwards [h.eventually_nhds, hU] with y hy hy0
  exact vfTest_local v c ((hs y hy0).differentiableAt (by simp)) hy

lemma vfTest_zero_off (v : ℂ) (P : testFn) {w : ℂ} (hw : w ∉ tsupport (P : ℂ → ℂ)) :
    ((vfTest v P : testFn) : ℂ → ℂ) w = 0 := by
  rw [vfTest_coe, (notMem_tsupport_iff_eventuallyEq.1 hw).fderiv_eq]
  simp

lemma tsupport_vfTest_subset (v : ℂ) (P : testFn) :
    tsupport ((vfTest v P : testFn) : ℂ → ℂ) ⊆ tsupport (P : ℂ → ℂ) :=
  closure_minimal (fun w hw => by
    by_contra hc
    exact hw (vfTest_zero_off v P hc)) (isClosed_tsupport _)

lemma lapTest_zero_off (P : testFn) {w : ℂ} (hw : w ∉ tsupport (P : ℂ → ℂ)) :
    ((lapTest P : testFn) : ℂ → ℂ) w = 0 := by
  have h1 : w ∉ tsupport ((vfTest 1 P : testFn) : ℂ → ℂ) := fun h => hw (tsupport_vfTest_subset _ _ h)
  have h2 : w ∉ tsupport ((vfTest Complex.I P : testFn) : ℂ → ℂ) := fun h => hw (tsupport_vfTest_subset _ _ h)
  rw [lapTest_eq_vf]
  show ((vfTest 1 (vfTest 1 P) : testFn) : ℂ → ℂ) w + ((vfTest Complex.I (vfTest Complex.I P) : testFn) : ℂ → ℂ) w
    - ((vfTest Complex.I P : testFn) : ℂ → ℂ) w = 0
  rw [vfTest_zero_off _ _ h1, vfTest_zero_off _ _ h2, vfTest_zero_off _ _ hw]
  simp

end local_

section mult

variable {h : ℂ → ℝ} {C : ℝ} (H : Adm h C)

lemma mulT_eq_mulHT {g : ℂ → ℝ} {C' : ℝ} (G : SB g C') {c Q : testFn}
    (hc : ∀ w, (Q : ℂ → ℂ) w ≠ 0 → (c : ℂ → ℂ) w = ((g w : ℝ) : ℂ)) : mulT c Q = mulHT G Q := by
  apply Subtype.ext; funext w
  show (c : ℂ → ℂ) w * (Q : ℂ → ℂ) w = ((g w : ℝ) : ℂ) * (Q : ℂ → ℂ) w
  by_cases hQ : (Q : ℂ → ℂ) w = 0
  · simp [hQ]
  · rw [hc w hQ]

/-- The pairing with a cutoff of `h`: all the local identities. -/
lemma exists_chi (P : testFn) : ∃ χ : testFn,
    mulT χ P = mulHT H.sb P ∧
    (∀ v, mulT χ (vfTest v P) = mulHT H.sb (vfTest v P)) ∧
    mulT χ (lapTest P) = mulHT H.sb (lapTest P) ∧
    mulT (vfTest 1 χ) P = mulHT H.sbX P ∧
    mulT (vfTest Complex.I χ) P = mulHT H.sbY P ∧
    mulT (lapTest χ) P = mulHT H.sbL P := by
  obtain ⟨η, hη⟩ := exists_cutoff P
  set χ := mulHT H.sb η
  have hχ : ∀ w ∈ tsupport (P : ℂ → ℂ), (χ : ℂ → ℂ) =ᶠ[𝓝 w] fun y => ((h y : ℝ) : ℂ) := fun w hw => by
    filter_upwards [hη w hw] with y hy
    rw [mulHT_coe, hy, mul_one]
  have hχ0 : ∀ w ∈ tsupport (P : ℂ → ℂ), (χ : ℂ → ℂ) w = ((h w : ℝ) : ℂ) := fun w hw => (hχ w hw).self_of_nhds
  have hmem : ∀ {w}, (P : ℂ → ℂ) w ≠ 0 → w ∈ tsupport (P : ℂ → ℂ) := fun hw => subset_tsupport _ hw
  have hd : ∀ {w : ℂ}, w ∈ tsupport (P : ℂ → ℂ) → DifferentiableAt ℝ h w := fun hw =>
    (H.s _ (P.2.inside hw)).differentiableAt (by simp)
  refine ⟨χ, mulT_eq_mulHT _ fun w hw => hχ0 w (hmem hw), fun v => mulT_eq_mulHT _ fun w hw => hχ0 w ?_,
    mulT_eq_mulHT _ fun w hw => hχ0 w ?_, mulT_eq_mulHT _ fun w hw => vfTest_local 1 χ (hd (hmem hw)) (hχ w (hmem hw)),
    mulT_eq_mulHT _ fun w hw => vfTest_local _ χ (hd (hmem hw)) (hχ w (hmem hw)), mulT_eq_mulHT _ fun w hw => ?_⟩
  · by_contra hc; exact hw (vfTest_zero_off v P hc)
  · by_contra hc; exact hw (lapTest_zero_off P hc)
  · have hwm := hmem hw
    have hw0 : 0 < w.im := P.2.inside hwm
    have hX := vfTest_local_ev 1 χ hw0 H.s (hχ w hwm)
    have hY := vfTest_local_ev Complex.I χ hw0 H.s (hχ w hwm)
    rw [lapTest_eq_vf]
    show ((vfTest 1 (vfTest 1 χ) : testFn) : ℂ → ℂ) w + ((vfTest Complex.I (vfTest Complex.I χ) : testFn) : ℂ → ℂ) w
      - ((vfTest Complex.I χ : testFn) : ℂ → ℂ) w = _
    rw [vfTest_local 1 _ ((H.sbX.s w hw0).differentiableAt (by simp)) hX,
      vfTest_local _ _ ((H.sbY.s w hw0).differentiableAt (by simp)) hY, hY.self_of_nhds, lapRv]
    push_cast; ring

/-- `X(hP) = (Xh)P + h XP`. -/
lemma vf_mulHT_X (P : testFn) : vfTest 1 (mulHT H.sb P) = mulHT H.sbX P + mulHT H.sb (vfTest 1 P) := by
  obtain ⟨χ, f1, f2, -, f4, -, -⟩ := exists_chi H P
  rw [← f1, vf_mulT, f4, f2]

lemma vf_mulHT_Y (P : testFn) :
    vfTest Complex.I (mulHT H.sb P) = mulHT H.sbY P + mulHT H.sb (vfTest Complex.I P) := by
  obtain ⟨χ, f1, f2, -, -, f4, -⟩ := exists_chi H P
  rw [← f1, vf_mulT, f4, f2]

/-- `(-Δ)(hu)`. -/
noncomputable def gZero (u : negLapH.domain) : L2H' :=
  mulCL H.sb (negLapH u) - (2 : ℂ) • mulCL H.sbX (domX u) - (2 : ℂ) • mulCL H.sbY (domY u) - mulCL H.sbL (u : L2H')

/-- `⟪ΔP, hu⟫ = -⟪P, (-Δ)(hu)⟫`. -/
theorem inner_lap_mul (P : testFn) (u : negLapH.domain) :
    inner ℂ (toL2 (lapTest P)) (mulCL H.sb (u : L2H')) = -inner ℂ (toL2 P) (gZero H u) := by
  obtain ⟨χ, f1, -, f3, f4, f5, f6⟩ := exists_chi H P
  have h := inner_local_lap χ P u
  rw [f3, f1, f4, f5, f6, inner_mulHT, inner_mulHT, inner_mulHT, inner_mulHT, inner_mulHT] at h
  rw [h, gZero, inner_sub_right, inner_sub_right, inner_sub_right, inner_smul_right, inner_smul_right]
  ring

lemma mulHT_add (P Q : testFn) : mulHT H.sb (P + Q) = mulHT H.sb P + mulHT H.sb Q := by
  apply Subtype.ext; funext w
  show ((h w : ℝ) : ℂ) * ((P : ℂ → ℂ) w + (Q : ℂ → ℂ) w) = ((h w : ℝ) : ℂ) * (P : ℂ → ℂ) w + ((h w : ℝ) : ℂ) * (Q : ℂ → ℂ) w
  ring

lemma mulHT_smul (c : ℂ) (P : testFn) : mulHT H.sb (c • P) = c • mulHT H.sb P := by
  apply Subtype.ext; funext w
  show ((h w : ℝ) : ℂ) * (c * (P : ℂ → ℂ) w) = c * (((h w : ℝ) : ℂ) * (P : ℂ → ℂ) w)
  ring

/-- `P ↦ hP` as a linear map. -/
noncomputable def mulHTLin : testFn →ₗ[ℂ] testFn where
  toFun := mulHT H.sb
  map_add' := mulHT_add H
  map_smul' := mulHT_smul H

/-- `lapDomain → FormDom negLap`, the identity. -/
noncomputable def ofDomLin : lapDomain →ₗ[ℂ] FormDom negLap where
  toFun := FormDom.ofDom negLap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Multiplication by `h` on the form domain. -/
noncomputable def mulFormLin : FormDom negLap →ₗ[ℂ] FormDom negLap :=
  ofDomLin ∘ₗ toL2Equiv.toLinearMap ∘ₗ mulHTLin H ∘ₗ toL2Equiv.symm.toLinearMap ∘ₗ toDomLin

/-- `‖x‖² = ‖P‖² + ‖XP‖² + ‖YP‖²`. -/
lemma form_norm_sq (x : FormDom negLap) :
    ‖x‖ ^ 2 = ‖toL2 (toL2Equiv.symm (FormDom.toDom negLap x))‖ ^ 2
      + ‖toL2 (vfTest 1 (toL2Equiv.symm (FormDom.toDom negLap x)))‖ ^ 2
      + ‖toL2 (vfTest Complex.I (toL2Equiv.symm (FormDom.toDom negLap x)))‖ ^ 2 := by
  have h1 := inner_vfDomLin_add x x
  have hre := congrArg Complex.re h1
  have e1 : ‖vfDomLin 1 x‖ ^ 2 = (inner ℂ (vfDomLin 1 x) (vfDomLin 1 x)).re := by
    rw [@norm_sq_eq_re_inner ℂ, RCLike.re_to_complex]
  have e2 : ‖vfDomLin Complex.I x‖ ^ 2 = (inner ℂ (vfDomLin Complex.I x) (vfDomLin Complex.I x)).re := by
    rw [@norm_sq_eq_re_inner ℂ, RCLike.re_to_complex]
  rw [Complex.add_re, ← e1, ← e2] at hre
  rw [FormDom.norm_sq_eq negLap x, ← hre, formDom_val_eq]
  show _ = _ + ‖vfDomLin 1 x‖ ^ 2 + ‖vfDomLin Complex.I x‖ ^ 2
  ring

lemma toDom_mulFormLin (x : FormDom negLap) :
    toL2Equiv.symm (FormDom.toDom negLap (mulFormLin H x)) = mulHT H.sb (toL2Equiv.symm (FormDom.toDom negLap x)) :=
  toL2Equiv.symm_apply_apply _

lemma norm_mulFormLin_le (x : FormDom negLap) : ‖mulFormLin H x‖ ≤ 3 * C * ‖x‖ := by
  have hC : 0 ≤ C := H.sb.nonneg
  set P := toL2Equiv.symm (FormDom.toDom negLap x)
  have hx := form_norm_sq x
  have hx' := form_norm_sq (mulFormLin H x)
  rw [toDom_mulFormLin] at hx'
  change ‖mulFormLin H x‖ ^ 2 = ‖toL2 (mulHT H.sb P)‖ ^ 2 + ‖toL2 (vfTest 1 (mulHT H.sb P))‖ ^ 2
    + ‖toL2 (vfTest Complex.I (mulHT H.sb P))‖ ^ 2 at hx'
  change ‖x‖ ^ 2 = ‖toL2 P‖ ^ 2 + ‖toL2 (vfTest 1 P)‖ ^ 2 + ‖toL2 (vfTest Complex.I P)‖ ^ 2 at hx
  set a := ‖toL2 P‖
  set b := ‖toL2 (vfTest 1 P)‖
  set c := ‖toL2 (vfTest Complex.I P)‖
  have ha : 0 ≤ a := norm_nonneg _
  have hb : 0 ≤ b := norm_nonneg _
  have hc : 0 ≤ c := norm_nonneg _
  have n0 : ‖toL2 (mulHT H.sb P)‖ ≤ C * a := by rw [toL2_mulHT]; exact norm_mulCL_le _ _
  have n1 : ‖toL2 (vfTest 1 (mulHT H.sb P))‖ ≤ C * a + C * b := by
    rw [vf_mulHT_X H, map_add, toL2_mulHT, toL2_mulHT]
    exact (norm_add_le _ _).trans (add_le_add (norm_mulCL_le _ _) (norm_mulCL_le _ _))
  have n2 : ‖toL2 (vfTest Complex.I (mulHT H.sb P))‖ ≤ C * a + C * c := by
    rw [vf_mulHT_Y H, map_add, toL2_mulHT, toL2_mulHT]
    exact (norm_add_le _ _).trans (add_le_add (norm_mulCL_le _ _) (norm_mulCL_le _ _))
  have s0 := pow_le_pow_left₀ (norm_nonneg _) n0 2
  have s1 := pow_le_pow_left₀ (norm_nonneg _) n1 2
  have s2 := pow_le_pow_left₀ (norm_nonneg _) n2 2
  have hsq : ‖mulFormLin H x‖ ^ 2 ≤ (3 * C * ‖x‖) ^ 2 := by
    rw [hx', mul_pow, hx]
    nlinarith [sq_nonneg (C * (a - b)), sq_nonneg (C * (a - c)), mul_nonneg (sq_nonneg C) (sq_nonneg a),
      mul_nonneg (sq_nonneg C) (sq_nonneg b), mul_nonneg (sq_nonneg C) (sq_nonneg c)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

/-- Multiplication by `h` on the form space. -/
noncomputable def mulFormE : FormSpace negLap →L[ℂ] FormSpace negLap :=
  ((UniformSpace.Completion.toComplL : FormDom negLap →L[ℂ] FormSpace negLap).comp
    (LinearMap.mkContinuous (mulFormLin H) (3 * C) (norm_mulFormLin_le H))).extend
    (UniformSpace.Completion.toComplL : FormDom negLap →L[ℂ] FormSpace negLap)

lemma mulFormE_coe (x : FormDom negLap) : mulFormE H (x : FormSpace negLap) = (mulFormLin H x : FormDom negLap) :=
  ContinuousLinearMap.extend_eq _ (e := (UniformSpace.Completion.toComplL : FormDom negLap →L[ℂ] FormSpace negLap))
    UniformSpace.Completion.denseRange_coe (UniformSpace.Completion.isUniformInducing_coe _) x

lemma incl_mulFormE (ξ : FormSpace negLap) : formIncl negLap (mulFormE H ξ) = mulCL H.sb (formIncl negLap ξ) := by
  refine UniformSpace.Completion.induction_on ξ ?_ ?_
  · exact isClosed_eq ((formIncl negLap).continuous.comp (mulFormE H).continuous)
      ((mulCL H.sb).continuous.comp (formIncl negLap).continuous)
  · intro x
    rw [mulFormE_coe, formIncl_coe, formIncl_coe, formDom_val_eq, formDom_val_eq, toDom_mulFormLin, toL2_mulHT]

/-- **`hu ∈ Dom(-Δ)`.** -/
theorem mul_mem_domain (u : negLapH.domain) : mulCL H.sb (u : L2H') ∈ negLapH.domain := by
  set ξ := mulFormE H (liftDom u)
  have hξ : formIncl negLap ξ = mulCL H.sb (u : L2H') := by
    rw [incl_mulFormE, formIncl_liftDom]
  set g : L2H' := mulCL H.sb (u : L2H') + gZero H u
  have hξg : ξ = formLift g := by
    refine ext_inner_left ℂ fun w => ?_
    refine UniformSpace.Completion.induction_on w ?_ ?_
    · exact isClosed_eq (continuous_id.inner continuous_const) (continuous_id.inner continuous_const)
    · intro x
      rw [inner_coe_formSpace, formLift, ContinuousLinearMap.adjoint_inner_right, hξ, formIncl_coe,
        formDom_val_eq, formDom_app_eq, inner_add_left, inner_neg_left, inner_lap_mul H _ u, neg_neg, inner_add_right]
  show mulCL H.sb (u : L2H') ∈ LinearMap.range (formRes negLap).toLinearMap
  refine ⟨g, ?_⟩
  show formIncl negLap (formLift g) = _
  rw [← hξg, hξ]

/-- **`X(hu) = (Xh)u + h Xu`.** -/
theorem domX_mul (u : negLapH.domain) :
    domX ⟨mulCL H.sb (u : L2H'), mul_mem_domain H u⟩ = mulCL H.sbX (u : L2H') + mulCL H.sb (domX u) := by
  refine ext_inner_left ℂ fun w => ?_
  refine DenseRange.induction_on denseRange_toL2 w ?_ fun P => ?_
  · exact isClosed_eq (continuous_id.inner continuous_const) (continuous_id.inner continuous_const)
  · obtain ⟨χ, f1, f2, -, f4, -, -⟩ := exists_chi H P
    have h1 := inner_X_dom P ⟨mulCL H.sb (u : L2H'), mul_mem_domain H u⟩
    have h2 := inner_X_dom (mulHT H.sb P) u
    have h3 : inner ℂ (toL2 (vfTest 1 P)) (mulCL H.sb (u : L2H'))
        = inner ℂ (toL2 (vfTest 1 (mulHT H.sb P))) (u : L2H') - inner ℂ (toL2 (mulHT H.sbX P)) (u : L2H') := by
      rw [← inner_mulHT]
      have e := vf_mulHT_X H P
      have e' : mulHT H.sb (vfTest 1 P) = vfTest 1 (mulHT H.sb P) - mulHT H.sbX P := by rw [e]; abel
      rw [e', map_sub, inner_sub_left]
    rw [inner_add_right, ← inner_mulHT H.sbX, ← inner_mulHT H.sb]
    show inner ℂ (toL2 P) (domX ⟨mulCL H.sb (u : L2H'), mul_mem_domain H u⟩) = _
    have h1' : inner ℂ (toL2 (vfTest 1 P)) (mulCL H.sb (u : L2H'))
        = -inner ℂ (toL2 P) (domX ⟨mulCL H.sb (u : L2H'), mul_mem_domain H u⟩) := h1
    linear_combination h1' - h3 - h2

/-- **`Y(hu) = (Yh)u + h Yu`.** -/
theorem domY_mul (u : negLapH.domain) :
    domY ⟨mulCL H.sb (u : L2H'), mul_mem_domain H u⟩ = mulCL H.sbY (u : L2H') + mulCL H.sb (domY u) := by
  refine ext_inner_left ℂ fun w => ?_
  refine DenseRange.induction_on denseRange_toL2 w ?_ fun P => ?_
  · exact isClosed_eq (continuous_id.inner continuous_const) (continuous_id.inner continuous_const)
  · have h1 := inner_Y_dom P ⟨mulCL H.sb (u : L2H'), mul_mem_domain H u⟩
    have h2 := inner_Y_dom (mulHT H.sb P) u
    have h3 : inner ℂ (toL2 (vfTest Complex.I P)) (mulCL H.sb (u : L2H'))
        = inner ℂ (toL2 (vfTest Complex.I (mulHT H.sb P))) (u : L2H') - inner ℂ (toL2 (mulHT H.sbY P)) (u : L2H') := by
      rw [← inner_mulHT]
      have e := vf_mulHT_Y H P
      have e' : mulHT H.sb (vfTest Complex.I P) = vfTest Complex.I (mulHT H.sb P) - mulHT H.sbY P := by rw [e]; abel
      rw [e', map_sub, inner_sub_left]
    have h4 : inner ℂ (toL2 (mulHT H.sb P)) (u : L2H') = inner ℂ (toL2 P) (mulCL H.sb (u : L2H')) := inner_mulHT _ _ _
    rw [inner_add_right, ← inner_mulHT H.sbY, ← inner_mulHT H.sb]
    show inner ℂ (toL2 P) (domY ⟨mulCL H.sb (u : L2H'), mul_mem_domain H u⟩) = _
    have h1' : inner ℂ (toL2 (vfTest Complex.I P)) (mulCL H.sb (u : L2H'))
        = -inner ℂ (toL2 P) (domY ⟨mulCL H.sb (u : L2H'), mul_mem_domain H u⟩)
          + inner ℂ (toL2 P) (mulCL H.sb (u : L2H')) := h1
    linear_combination h1' - h3 - h2 - h4

end mult

end Qschubert
