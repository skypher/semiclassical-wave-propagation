import Qschubert.KLCor16
import Qschubert.KLLift1a

/-!
# LIFT-1: every amplitude of finite norm has a `C^∞` representative

A vector on which all words in `X`, `Y` act has a `C^∞` representative near `i` (`words_smooth_near_I`): the span of the `χ w` (`χ` a real cutoff, `w` such a vector) is closed under the Euclidean
Laplacian, so `smooth_rep_of_iter` applies. `Dom e^{αΛ}` consists of such vectors (`allWords_of_exp`) and is isometry invariant, so local representatives exist at every point, and they glue (`glue_smooth`).
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set Physicslib4.Spectral.Unbounded UpperHalfPlane Metric
open scoped ENNReal InnerProductSpace MatrixGroups Pointwise ComplexConjugate ContDiff Laplacian

local notation "L2H'" => Lp ℂ 2 (volume : Measure UpperHalfPlane)
local notation "L2C" => Lp ℂ 2 (volume : Measure ℂ)

/-- `conj(y² (Δ_E φ) c) = c · Δ(conj(θφ))`, for a real `c` supported in `supp χ`. -/
lemma conj_lap_c {c : testFn} (hc : IsRealT c) (hs : tsupport (c : ℂ → ℂ) ⊆ tsupport (chiT : ℂ → ℂ))
    {φ : ℂ → ℂ} (hφ : ContDiff ℝ ∞ φ) {g : ℂ → ℂ} (hg : ContDiff ℝ ∞ g) (hgφ : ∀ ζ, g ζ = lapE φ ζ) :
    conjT (smulTF (fun ζ => ((ζ.im : ℝ) : ℂ) ^ 2 * g ζ) (contDiff_imSq.mul hg) c)
      = mulT c (lapTest (conjT (thetaPhi φ hφ))) := by
  rw [lapTest_conjT]
  apply Subtype.ext; funext ζ
  show conj (((ζ.im : ℝ) : ℂ) ^ 2 * g ζ * (c : ℂ → ℂ) ζ)
    = (c : ℂ → ℂ) ζ * conj (((ζ.im : ℝ) : ℂ) ^ 2 * lapE (fun w => φ w * (thetaT : ℂ → ℂ) w) ζ)
  by_cases h0 : (c : ℂ → ℂ) ζ = 0
  · simp [h0]
  · have hζ : ζ ∈ tsupport (chiT : ℂ → ℂ) := hs (subset_tsupport _ h0)
    have hev : (fun w => φ w * (thetaT : ℂ → ℂ) w) =ᶠ[𝓝 ζ] φ := by
      filter_upwards [thetaT_eventuallyEq_one hζ] with w hw
      rw [hw, mul_one]
    have hlap : lapE (fun w => φ w * (thetaT : ℂ → ℂ) w) ζ = lapE φ ζ := by
      simp only [lapE, hev.fderiv.fderiv_eq]
    rw [hlap, ← hgφ, map_mul, map_mul, hc]
    ring

/-- The right side of `Δ_E(c u) = h`. -/
noncomputable def hEucC (c : testFn) (u : negLapH.domain) : L2C :=
  -eucL (divIm2 c) (negLapH u) + (2 : ℂ) • eucL (divIm2 (vfTest 1 c)) (domX u)
    + (2 : ℂ) • eucL (divIm2 (vfTest Complex.I c)) (domY u) + eucL (divIm2 (lapTest c)) u

open FourierTransform SchwartzMap TemperedDistribution in
/-- **`Δ_E(c u) = h`** for a real `c` supported in `supp χ`. -/
theorem laplacian_eucL_c {c : testFn} (hc : IsRealT c) (hs : tsupport (c : ℂ → ℂ) ⊆ tsupport (chiT : ℂ → ℂ)) (u : negLapH.domain) :
    Δ ((eucL c u : L2C) : 𝓢'(ℂ, ℂ)) = ((hEucC c u : L2C) : 𝓢'(ℂ, ℂ)) := by
  ext φ
  have hφ := φ.smooth ⊤
  rw [TemperedDistribution.laplacian_apply_apply, pairing_eucL]
  have hΔ : ∀ ζ, (Δ φ : 𝓢(ℂ, ℂ)) ζ = lapE φ ζ := fun ζ => by
    rw [SchwartzMap.laplacian_apply, laplacian_eq_lapE]
  rw [conj_lap_c hc hs hφ ((Δ φ).smooth ⊤) hΔ, inner_local_lap]
  have hX := tsupport_vfTest_sub 1 c
  have hY := tsupport_vfTest_sub Complex.I c
  have hL := tsupport_lapTest_sub c
  rw [mulT_conj_thetaPhi hc (hsupp_of_sub hs) hφ,
    mulT_conj_thetaPhi (isRealT_vfTest 1 hc) (hsupp_of_sub (hX.trans hs)) hφ,
    mulT_conj_thetaPhi (isRealT_vfTest Complex.I hc) (hsupp_of_sub (hY.trans hs)) hφ,
    mulT_conj_thetaPhi (isRealT_lapTest hc) (hsupp_of_sub (hL.trans hs)) hφ]
  rw [hEucC, ← Lp.toTemperedDistributionCLM_apply (F := ℂ) (μ := volume)]
  simp only [map_add, map_neg, map_smul, Lp.toTemperedDistributionCLM_apply]
  simp only [add_apply, neg_apply, smul_apply, pairing_eucL, smul_eq_mul]

lemma allWords_domX {w : L2H'} (hA : AllWords w) (hw : w ∈ negLapH.domain) : AllWords (domX ⟨w, hw⟩) := by
  have h := allWords_polyAct hA [((1 : ℂ), [true])]
  have e : polyAct [((1 : ℂ), [true])] w = domX ⟨w, hw⟩ := by
    rw [polyAct_cons, polyAct_nil, one_smul, add_zero, wordAct_cons true [] (show wordAct [] w ∈ negLapH.domain from hw)]
    simp only [domZ, ite_true]; rfl
  rwa [e] at h

lemma allWords_domY {w : L2H'} (hA : AllWords w) (hw : w ∈ negLapH.domain) : AllWords (domY ⟨w, hw⟩) := by
  have h := allWords_polyAct hA [((1 : ℂ), [false])]
  have e : polyAct [((1 : ℂ), [false])] w = domY ⟨w, hw⟩ := by
    rw [polyAct_cons, polyAct_nil, one_smul, add_zero, wordAct_cons false [] (show wordAct [] w ∈ negLapH.domain from hw)]
    simp only [domZ, Bool.false_eq_true, ite_false]; rfl
  rwa [e] at h

lemma allWords_neg {x : L2H'} (h : AllWords x) : AllWords (-x) := by
  have h1 := allWords_polyAct h [((-1 : ℂ), [])]
  have e : polyAct [((-1 : ℂ), [])] x = -x := by
    rw [polyAct_cons, polyAct_nil, add_zero]
    show (-1 : ℂ) • x = -x
    rw [_root_.neg_smul, one_smul]
  rwa [e] at h1

lemma negLapH_eq_delta {w : L2H'} (hA : AllWords w) (hw : w ∈ negLapH.domain) :
    negLapH ⟨w, hw⟩ = -polyAct (deltaP 0) w := by
  have h1 := lapTbar_eq_polyAct 0 ⟨w, hw⟩ hA
  have h2 := lapTbar_zero ⟨((w : L2H'), negLapH ⟨w, hw⟩), mem_graphBar_negLapH ⟨w, hw⟩⟩
  have h3 : polyAct (deltaP 0) w = -negLapH ⟨w, hw⟩ := h1.symm.trans h2
  rw [h3, neg_neg]

lemma allWords_negLapH {w : L2H'} (hA : AllWords w) (hw : w ∈ negLapH.domain) : AllWords (negLapH ⟨w, hw⟩) := by
  rw [negLapH_eq_delta hA hw]
  exact allWords_neg (allWords_polyAct hA _)

/-- The generators. -/
def VSet : Set L2C := {f | ∃ (c : testFn) (w : L2H'), IsRealT c ∧ tsupport (c : ℂ → ℂ) ⊆ tsupport (chiT : ℂ → ℂ) ∧ AllWords w ∧ f = eucL c w}

/-- Their span. -/
noncomputable def VSpan : Submodule ℂ L2C := Submodule.span ℂ VSet

section lapSpan

open FourierTransform SchwartzMap TemperedDistribution

lemma coeC_add (f g : L2C) : ((f + g : L2C) : 𝓢'(ℂ, ℂ)) = (f : 𝓢'(ℂ, ℂ)) + (g : 𝓢'(ℂ, ℂ)) := by
  rw [← Lp.toTemperedDistributionCLM_apply (F := ℂ) (μ := volume) (f + g), map_add]; rfl

lemma coeC_smul (c : ℂ) (f : L2C) : ((c • f : L2C) : 𝓢'(ℂ, ℂ)) = c • (f : 𝓢'(ℂ, ℂ)) := by
  rw [← Lp.toTemperedDistributionCLM_apply (F := ℂ) (μ := volume) (c • f), map_smul]; rfl

lemma coeC_zero : ((0 : L2C) : 𝓢'(ℂ, ℂ)) = 0 := by
  rw [← Lp.toTemperedDistributionCLM_apply (F := ℂ) (μ := volume) (0 : L2C), map_zero]

lemma lapD_add (a b : 𝓢'(ℂ, ℂ)) : Δ (a + b) = Δ a + Δ b := by
  ext φ
  simp only [TemperedDistribution.laplacian_apply_apply, add_apply]

lemma lapD_smul (c : ℂ) (a : 𝓢'(ℂ, ℂ)) : Δ (c • a) = c • Δ a := by
  ext φ
  simp only [TemperedDistribution.laplacian_apply_apply, smul_apply]

lemma lapD_zero : Δ (0 : 𝓢'(ℂ, ℂ)) = 0 := by
  ext φ
  simp only [TemperedDistribution.laplacian_apply_apply, zero_apply]

lemma lap_gen {c : testFn} {w : L2H'} (hc : IsRealT c) (hs : tsupport (c : ℂ → ℂ) ⊆ tsupport (chiT : ℂ → ℂ)) (hA : AllWords w) :
    ∃ g ∈ VSpan, Δ ((eucL c w : L2C) : 𝓢'(ℂ, ℂ)) = (g : 𝓢'(ℂ, ℂ)) := by
  have hw : w ∈ negLapH.domain := by simpa [wordAct] using AllWords.mem hA []
  have hd : ∀ {d : testFn}, IsRealT d → tsupport (d : ℂ → ℂ) ⊆ tsupport (chiT : ℂ → ℂ) →
      IsRealT (divIm2 d) ∧ tsupport (divIm2 d : ℂ → ℂ) ⊆ tsupport (chiT : ℂ → ℂ) := fun hdr hds =>
    ⟨isRealT_divImTest (isRealT_divImTest hdr), (tsupport_divIm2_sub _).trans hds⟩
  have mk : ∀ {d : testFn} {v : L2H'}, IsRealT d → tsupport (d : ℂ → ℂ) ⊆ tsupport (chiT : ℂ → ℂ) → AllWords v → eucL (divIm2 d) v ∈ VSpan :=
    fun hdr hds hv => Submodule.subset_span ⟨_, _, (hd hdr hds).1, (hd hdr hds).2, hv, rfl⟩
  refine ⟨hEucC c ⟨w, hw⟩, ?_, laplacian_eucL_c hc hs ⟨w, hw⟩⟩
  refine add_mem (add_mem (add_mem (neg_mem ?_) (Submodule.smul_mem _ _ ?_)) (Submodule.smul_mem _ _ ?_)) ?_
  · exact mk hc hs (allWords_negLapH hA hw)
  · exact mk (isRealT_vfTest 1 hc) ((tsupport_vfTest_sub 1 c).trans hs) (allWords_domX hA hw)
  · exact mk (isRealT_vfTest Complex.I hc) ((tsupport_vfTest_sub Complex.I c).trans hs) (allWords_domY hA hw)
  · exact mk (isRealT_lapTest hc) ((tsupport_lapTest_sub c).trans hs) hA

theorem lap_span {f : L2C} (hf : f ∈ VSpan) : ∃ g ∈ VSpan, Δ (f : 𝓢'(ℂ, ℂ)) = (g : 𝓢'(ℂ, ℂ)) := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, w, hc, hs, hA, rfl⟩ := hx
    exact lap_gen hc hs hA
  | zero => exact ⟨0, zero_mem _, by rw [coeC_zero, lapD_zero]⟩
  | add x y _ _ hx hy =>
    obtain ⟨g₁, h₁, e₁⟩ := hx
    obtain ⟨g₂, h₂, e₂⟩ := hy
    exact ⟨g₁ + g₂, add_mem h₁ h₂, by rw [coeC_add, lapD_add, e₁, e₂, coeC_add]⟩
  | smul a x _ hx =>
    obtain ⟨g, h, e⟩ := hx
    exact ⟨a • g, Submodule.smul_mem _ _ h, by rw [coeC_smul, lapD_smul, e, coeC_smul]⟩

/-- **A vector on which all words act is `C^∞` near `i`.** -/
theorem words_smooth_near_I {w : L2H'} (hA : AllWords w) :
    ∃ s : ℂ → ℂ, ContDiff ℝ ∞ s ∧ ∀ᵐ z : ℍ ∂(volume : Measure ℍ), dist (z : ℂ) Complex.I < 1 / 4 → w z = s z := by
  choose! T hTm hT using (fun (f : L2C) (hf : f ∈ VSpan) => lap_span hf)
  set f₀ : L2C := eucL chiT w with hf₀
  have h0 : f₀ ∈ VSpan := Submodule.subset_span ⟨chiT, w, isRealT_chiT, subset_rfl, hA, rfl⟩
  have hm : ∀ n, T^[n] f₀ ∈ VSpan := by
    intro n
    induction n with
    | zero => exact h0
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact hTm _ ih
  have hΔ : ∀ n, Δ ((T^[n] f₀ : L2C) : 𝓢'(ℂ, ℂ)) = ((T^[n + 1] f₀ : L2C) : 𝓢'(ℂ, ℂ)) := fun n => by
    rw [Function.iterate_succ_apply']
    exact hT _ (hm n)
  obtain ⟨s, hs, hae⟩ := smooth_rep_of_iter (fun n => T^[n] f₀) hΔ
  refine ⟨s, hs, ?_⟩
  have hC : ∀ᵐ ζ ∂(volume : Measure ℂ), eucFun chiT w ζ = s ζ := by
    filter_upwards [hae, eucL_ae chiT w] with ζ h1 h2
    rw [← h2]; exact h1
  have hH : ∀ᵐ (z : ℍ) ∂(volume : Measure ℍ), eucFun chiT w (z : ℂ) = s (z : ℂ) := by
    rw [ae_iff] at hC ⊢
    exact volume_preimage_coe_null' hC
  filter_upwards [hH, repL2_ae w] with z h1 h2 hz
  rw [h2, ← h1]
  have hχ : (chiT : ℂ → ℂ) z = 1 := chiT_eq_one hz.le
  rw [eucFun, hχ, one_mul, ofComplex_apply]

end lapSpan

theorem allWords_of_exp {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {z : L2H'} (hz : z ∈ (expLambda α).domain) : AllWords z := by
  have hτ : (1 : ℝ) < Real.pi / 2 := by linarith [Real.pi_gt_three]
  obtain ⟨C₁, hC, hF⟩ := lem_fc hτ
  exact fun S => (lem_wc_zero hF hC S hα hα1 hz).1

/-- `ζ ↦ (ζ - x₀)/y₀`. -/
noncomputable def affL (z₀ : ℍ) (ζ : ℂ) : ℂ := (ζ - (z₀.re : ℂ)) / (z₀.im : ℂ)

lemma contDiff_affL (z₀ : ℍ) : ContDiff ℝ ∞ (affL z₀) := by
  unfold affL
  exact (contDiff_id.sub contDiff_const).div_const _

lemma affL_smul (z₀ z : ℍ) : affL z₀ ((transH z₀ • z : ℍ) : ℂ) = z := by
  have hy : (z₀.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 z₀.im_pos.ne'
  rw [affL, transH_coe]
  field_simp
  ring

lemma affL_inv (z₀ w : ℍ) : (((transH z₀)⁻¹ • w : ℍ) : ℂ) = affL z₀ w := by
  have h := affL_smul z₀ ((transH z₀)⁻¹ • w)
  rw [smul_inv_smul] at h
  exact h.symm

/-- A smooth patch at every point. -/
theorem patch_smooth {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {F : L2H'} (hF : F ∈ (expLambda α).domain) (z₀ : ℍ) :
    ∃ S : ℂ → ℂ, ContDiff ℝ ∞ S ∧ ∃ V : Set ℍ, IsOpen V ∧ z₀ ∈ V ∧ ∀ᵐ w ∂(volume : Measure ℍ), w ∈ V → F w = S w := by
  set p : PGL(2, ℝ) := Matrix.SpecialLinearGroup.toPGL (transH z₀) with hp
  obtain ⟨h1, -⟩ := expLambda_iso p hF
  obtain ⟨s, hs, hae⟩ := words_smooth_near_I (allWords_of_exp hα hα1 h1)
  have hcomp : ∀ᵐ z : ℍ ∂(volume : Measure ℍ), dist (z : ℂ) Complex.I < 1 / 4 → F (p • z) = s z := by
    filter_upwards [hae, isoU_ae p F] with z e1 e2 hz
    rw [← e2]; exact e1 hz
  have hpull := (measurePreserving_smul p⁻¹ (volume : Measure ℍ)).quasiMeasurePreserving.ae hcomp
  have hinv : ∀ w : ℍ, ((p⁻¹ • w : ℍ) : ℂ) = affL z₀ w := fun w => by
    rw [hp, ← map_inv, toPGL_smul]
    exact affL_inv z₀ w
  refine ⟨s ∘ affL z₀, hs.comp (contDiff_affL z₀), {w : ℍ | dist (affL z₀ w) Complex.I < 1 / 4},
    isOpen_lt (((contDiff_affL z₀).continuous.comp UpperHalfPlane.continuous_coe).dist continuous_const) continuous_const, ?_, ?_⟩
  · show dist (affL z₀ z₀) Complex.I < 1 / 4
    have e : affL z₀ (z₀ : ℂ) = Complex.I := by
      have h := affL_smul z₀ UpperHalfPlane.I
      rw [transH_smul_I] at h
      exact h
    rw [e, dist_self]; norm_num
  · filter_upwards [hpull] with w hw hV
    have e := hinv w
    have h2 := hw (by rw [e]; exact hV)
    rw [smul_inv_smul] at h2
    rw [h2, e]
    rfl

/-- **Gluing** smooth local representatives. -/
theorem glue_smooth {u' : ℍ → ℂ}
    (hp : ∀ z₀ : ℍ, ∃ S : ℂ → ℂ, ContDiff ℝ ∞ S ∧ ∃ V : Set ℍ, IsOpen V ∧ z₀ ∈ V ∧ ∀ᵐ w ∂(volume : Measure ℍ), w ∈ V → u' w = S w) :
    ∃ F : ℍ → ℂ, SmoothH F ∧ F =ᵐ[volume] u' := by
  choose S hSc V hVo hVm hSa using hp
  have hcoe : ∀ a, Continuous fun w : ℍ => S a (w : ℂ) := fun a => (hSc a).continuous.comp UpperHalfPlane.continuous_coe
  have hag : ∀ a b : ℍ, ∀ w ∈ V a ∩ V b, S a (w : ℂ) = S b (w : ℂ) := by
    intro a b
    have hO : IsOpen (V a ∩ V b) := (hVo a).inter (hVo b)
    have hae : (fun w : ℍ => S a (w : ℂ)) =ᵐ[(volume : Measure ℍ).restrict (V a ∩ V b)] fun w : ℍ => S b (w : ℂ) := by
      rw [Filter.EventuallyEq, ae_restrict_iff' hO.measurableSet]
      filter_upwards [hSa a, hSa b] with w h1 h2 hw
      rw [← h1 hw.1, ← h2 hw.2]
    exact Measure.eqOn_open_of_ae_eq hae hO (hcoe a).continuousOn (hcoe b).continuousOn
  set F : ℍ → ℂ := fun z => S z (z : ℂ) with hF
  have key : ∀ z₀, ∀ z ∈ V z₀, F z = S z₀ (z : ℂ) := fun z₀ z hz => hag z z₀ z ⟨hVm z, hz⟩
  refine ⟨F, fun z => ?_, ?_⟩
  · have himg : (UpperHalfPlane.coe '' V z) ∈ 𝓝 (z : ℂ) :=
      (isOpenEmbedding_coe.isOpenMap _ (hVo z)).mem_nhds ⟨z, hVm z, rfl⟩
    refine ((hSc z).contDiffAt (x := (z : ℂ))).congr_of_eventuallyEq ?_
    filter_upwards [himg] with ζ hζ
    obtain ⟨w, hw, rfl⟩ := hζ
    show F (ofComplex (w : ℂ)) = S z (w : ℂ)
    rw [ofComplex_apply]
    exact key z w hw
  · obtain ⟨T, hT, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable V hVo
    have hall : ∀ᵐ w ∂(volume : Measure ℍ), ∀ z₀ ∈ T, w ∈ V z₀ → u' w = S z₀ (w : ℂ) :=
      (ae_ball_iff hT).2 fun z₀ _ => hSa z₀
    filter_upwards [hall] with w hw
    have hmem : w ∈ ⋃ i ∈ T, V i := by
      rw [hTU]; exact mem_iUnion.2 ⟨w, hVm w⟩
    obtain ⟨z₀, hz₀, hwz⟩ := mem_iUnion₂.1 hmem
    rw [key z₀ w hwz, hw z₀ hz₀ hwz]

lemma wt_eq (x₀ z : ℍ) : hF (affL x₀ z) = (coshD x₀ z)⁻¹ := by
  rw [← affL_inv x₀ z, hF_eq_inv_coshD]
  congr 1
  unfold coshD
  congr 1
  rw [← dist_smul (transH x₀) UpperHalfPlane.I, transH_smul_I, smul_inv_smul]

lemma smoothH_wt (x₀ : ℍ) (β : ℝ) {G : ℍ → ℂ} (hG : SmoothH G) :
    SmoothH fun z => ((hF (affL x₀ z) ^ β : ℝ) : ℂ) * G z := fun z => by
  have him : 0 < (affL x₀ z).im := by
    rw [← affL_inv x₀ z]; exact ((transH x₀)⁻¹ • z).im_pos
  have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ζ => hF (affL x₀ ζ) ^ β) (z : ℂ) :=
    ((contDiff_hF.comp (contDiff_affL x₀)).contDiffAt).rpow_const_of_ne (hF_pos him).ne'
  have h2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ζ => ((hF (affL x₀ ζ) ^ β : ℝ) : ℂ)) (z : ℂ) :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp _ h1
  refine (h2.mul (hG z)).congr_of_eventuallyEq ?_
  filter_upwards [isOpenEmbedding_coe.isOpen_range.mem_nhds (mem_range_self z)] with ζ hζ
  obtain ⟨w, rfl⟩ := hζ
  simp only [extC, ofComplex_apply]

/-- **LIFT-1.** Every amplitude of finite norm has a `C^∞` representative. -/
theorem lift1 {x₀ : ℍ} {α β : ℝ} {a : ℍ → ℂ} (hα : 0 < α) (hα1 : α ≤ 1) (hfin : swNormX x₀ α β a < ⊤) :
    ∃ a' : ℍ → ℂ, SmoothH a' ∧ a' =ᵐ[volume] a := by
  unfold swNormX at hfin
  split_ifs at hfin with hw h
  · obtain ⟨G, hG, hGa⟩ := glue_smooth (patch_smooth hα hα1 h)
    refine ⟨fun z => ((hF (affL x₀ z) ^ β : ℝ) : ℂ) * G z, smoothH_wt x₀ β hG, ?_⟩
    filter_upwards [hGa, hw.coeFn_toLp] with z e1 e2
    show ((hF (affL x₀ z) ^ β : ℝ) : ℂ) * G z = a z
    rw [e1, e2, wt_eq]
    have hc : 0 < coshD x₀ z := Real.cosh_pos _
    have hp : 0 < coshD x₀ z ^ β := Real.rpow_pos_of_pos hc β
    rw [Real.inv_rpow hc.le]
    have hne : ((coshD x₀ z ^ β : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hp.ne'
    push_cast at hne ⊢
    rw [inv_mul_cancel_left₀ hne]
  · exact absurd hfin (by simp)
  · exact absurd hfin (by simp)

/-- The representative is unique. -/
lemma smooth_rep_unique {a₁ a₂ : ℍ → ℂ} (h₁ : SmoothH a₁) (h₂ : SmoothH a₂) (h : a₁ =ᵐ[volume] a₂) : a₁ = a₂ :=
  (Continuous.ae_eq_iff_eq (volume : Measure ℍ) (continuous_of_smoothH h₁) (continuous_of_smoothH h₂)).1 h

/-- The norm depends only on the class of `a`. -/
lemma swNormX_congr {x₀ : ℍ} {α β : ℝ} {a a' : ℍ → ℂ} (h : a' =ᵐ[volume] a) : swNormX x₀ α β a' = swNormX x₀ α β a := by
  have e : (fun z => ((coshD x₀ z ^ β : ℝ) : ℂ) * a' z) =ᵐ[volume] fun z => ((coshD x₀ z ^ β : ℝ) : ℂ) * a z := by
    filter_upwards [h] with z hz
    rw [hz]
  unfold swNormX
  by_cases hw : MemLp (fun z => ((coshD x₀ z ^ β : ℝ) : ℂ) * a z) 2 (volume : Measure ℍ)
  · have hw' := (memLp_congr_ae e).2 hw
    have et : hw'.toLp _ = hw.toLp _ := MemLp.toLp_congr _ _ e
    rw [dif_pos hw', dif_pos hw, et]
  · have hw' : ¬ MemLp (fun z => ((coshD x₀ z ^ β : ℝ) : ℂ) * a' z) 2 (volume : Measure ℍ) := fun h' => hw ((memLp_congr_ae e).1 h')
    rw [dif_neg hw', dif_neg hw]

/-- **Theorem 1.4R for every amplitude of finite norm.** The `C^∞` representative is chosen before `ħ, t, K, N, g`, and the approximant is built from it. -/
def Stmt_thm14R_rep : Prop :=
  ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ →
  ∀ (x₀ : ℍ) (β κ α₀ : ℝ), 1 / 2 < β → 0 < κ → 0 < α₀ → α₀ < min 1 (Real.pi / 4) →
  ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
  ∀ (α : ℝ) (a : ℍ → ℂ), 0 < α → α ≤ α₀ → swNormX x₀ α β a < ⊤ →
    ∃ a' : ℍ → ℂ, SmoothH a' ∧ a' =ᵐ[volume] a ∧
    ∀ (ħ' t : ℝ) (K N : ℕ) (g : SL(2, ℝ)),
      0 < ħ' → ħ' ≤ 1 → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ → 0 ≤ t → t ≤ δ * Real.sqrt (α / ħ') →
      ∃ (hv : PerioConv Γ (initState g ħ' a')) (hw : PerioConv Γ (approxSolB g K ħ' t a')),
        approxErr Γ N ħ' t hv hw ≤ ENNReal.ofReal (ddBound C α ħ' t K N) * swNormX x₀ α β a

theorem thm14R_rep : Stmt_thm14R_rep := by
  intro Γ _ hOr x₀ β κ α₀ hβ hκ hα₀ hα₁
  obtain ⟨C, δ, hC, hδ, h⟩ := thm14R_smooth Γ hOr x₀ β κ α₀ hβ hκ hα₀ hα₁
  refine ⟨C, δ, hC, hδ, fun α a hα hαα hfin => ?_⟩
  have hα1 : α ≤ 1 := hαα.trans (hα₁.le.trans (min_le_left _ _))
  obtain ⟨a', hs, ha⟩ := lift1 hα hα1 hfin
  have e := swNormX_congr (x₀ := x₀) (α := α) (β := β) ha
  refine ⟨a', hs, ha, fun ħ t K N g hħ hħ1 hκc hg ht htδ => ?_⟩
  obtain ⟨hv, hw, hb⟩ := h ħ α t K N g a' hħ hħ1 hα hαα hκc hg ht htδ hs (e.symm ▸ hfin)
  exact ⟨hv, hw, e ▸ hb⟩

/-- **Corollary 1.5R for every amplitude of finite norm.** -/
def Stmt_cor15R_rep : Prop :=
  ∃ C' : ℝ, 0 < C' ∧
  ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ →
  ∀ (x₀ : ℍ) (β κ α₀ : ℝ), 1 / 2 < β → 0 < κ → 0 < α₀ → α₀ < min 1 (Real.pi / 4) →
  ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
  ∀ (α : ℝ) (a : ℍ → ℂ), 0 < α → α ≤ α₀ → swNormX x₀ α β a < ⊤ →
    ∃ a' : ℍ → ℂ, SmoothH a' ∧ a' =ᵐ[volume] a ∧
    ∀ (ħ' t ε : ℝ) (K N : ℕ) (g : SL(2, ℝ)),
      0 < ħ' → ħ' ≤ 1 → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ → 0 ≤ t → t ≤ δ * Real.sqrt (α / ħ') →
      0 < ε → ε < 1 → 1 - ε ≤ K * (C * ħ' * t / α ^ 2) → K * (C * ħ' * t / α ^ 2) ≤ 1 - ε / 2 →
      ∃ (hv : PerioConv Γ (initState g ħ' a')) (hw : PerioConv Γ (approxSolB g K ħ' t a')),
        approxErr Γ N ħ' t hv hw
          ≤ ENNReal.ofReal (C' / Real.sqrt ε * C ^ (N + 1) * (N : ℝ) ^ (2 * N)
              * ((α * ħ')⁻¹) ^ (2 * N) * Real.exp (-((1 - ε) * α ^ 2 / (C * ħ' * t)))) * swNormX x₀ α β a

theorem cor15R_rep : Stmt_cor15R_rep := by
  obtain ⟨C', hC', h0⟩ := cor15R_smooth
  refine ⟨C', hC', ?_⟩
  intro Γ _ hOr x₀ β κ α₀ hβ hκ hα₀ hα₁
  obtain ⟨C, δ, hC, hδ, h⟩ := h0 Γ hOr x₀ β κ α₀ hβ hκ hα₀ hα₁
  refine ⟨C, δ, hC, hδ, fun α a hα hαα hfin => ?_⟩
  have hα1 : α ≤ 1 := hαα.trans (hα₁.le.trans (min_le_left _ _))
  obtain ⟨a', hs, ha⟩ := lift1 hα hα1 hfin
  have e := swNormX_congr (x₀ := x₀) (α := α) (β := β) ha
  refine ⟨a', hs, ha, fun ħ t ε K N g hħ hħ1 hκc hg ht htδ hε hε1 hK1 hK2 => ?_⟩
  obtain ⟨hv, hw, hb⟩ := h ħ α t ε K N g a' hħ hħ1 hα hαα hκc hg ht htδ hs (e.symm ▸ hfin) hε hε1 hK1 hK2
  exact ⟨hv, hw, e ▸ hb⟩

/-- **Corollary 1.6R for every amplitude of finite norm.** -/
def Stmt_cor16R_rep : Prop :=
  ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ →
  ∀ (x₀ : ℍ) (β κ α₀ r₀ : ℝ), 1 / 2 < β → 0 < κ → 0 < α₀ → α₀ < min 1 (Real.pi / 4) → 0 < r₀ →
    InjRadGe Γ r₀ →
  ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
  ∀ (α : ℝ) (a : ℍ → ℂ), 0 < α → α ≤ α₀ → swNormX x₀ α β a < ⊤ →
    ∃ a' : ℍ → ℂ, SmoothH a' ∧ a' =ᵐ[volume] a ∧
    ∀ (ħ' t : ℝ) (K N : ℕ) (g : SL(2, ℝ)),
      0 < ħ' → ħ' ≤ 1 → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ → 0 ≤ t → t ≤ δ * Real.sqrt (α / ħ') →
      ∃ (hv : PerioConv Γ (initState g ħ' a')) (hw : PerioConv Γ (approxSolB g K ħ' t a')),
        PointwiseBound Γ N (errVec Γ ħ' t hv hw)
          (fun _ => ENNReal.ofReal (ptBound C α ħ' t K N) * swNormX x₀ α β a)

theorem cor16R_rep : Stmt_cor16R_rep := by
  intro Γ _ hOr x₀ β κ α₀ r₀ hβ hκ hα₀ hα₁ hr₀ hinj
  obtain ⟨C, δ, hC, hδ, h⟩ := cor16R_smooth Γ hOr x₀ β κ α₀ r₀ hβ hκ hα₀ hα₁ hr₀ hinj
  refine ⟨C, δ, hC, hδ, fun α a hα hαα hfin => ?_⟩
  have hα1 : α ≤ 1 := hαα.trans (hα₁.le.trans (min_le_left _ _))
  obtain ⟨a', hs, ha⟩ := lift1 hα hα1 hfin
  have e := swNormX_congr (x₀ := x₀) (α := α) (β := β) ha
  refine ⟨a', hs, ha, fun ħ t K N g hħ hħ1 hκc hg ht htδ => ?_⟩
  obtain ⟨hv, hw, hb⟩ := h ħ α t K N g a' hħ hħ1 hα hαα hκc hg ht htδ hs (e.symm ▸ hfin)
  exact ⟨hv, hw, e ▸ hb⟩

end Qschubert
