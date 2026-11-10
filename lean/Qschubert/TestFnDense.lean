import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
import Mathlib.Topology.Metrizable.Basic
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Qschubert.LaplacianL2

/-!
# Test functions are dense in `L²(ℍ, dx dy / y²)`

Spine stage S2 (`lean/BLUEPRINT.md`): the domain of the Friedrichs construction is dense.
Compactly supported continuous functions are dense (Mathlib, for the regular measure `dx dy / y²`);
each is extended by zero to `ℂ` and mollified by a bump of radius smaller than its distance to the real
axis, which gives a test function uniformly close on a fixed compact set of finite measure.
-/

namespace Qschubert

open UpperHalfPlane MeasureTheory Complex Topology Metric Set
open scoped ComplexConjugate ENNReal ContDiff Convolution

/-- Extension by zero of a function on `ℍ` to `ℂ`. -/
noncomputable def extZero (g : ℍ → ℂ) : ℂ → ℂ := fun w => if h : 0 < w.im then g ⟨w, h⟩ else 0

lemma extZero_coe (g : ℍ → ℂ) (z : ℍ) : extZero g z = g z := by
  have h : 0 < (z : ℂ).im := z.im_pos
  rw [extZero, dite_eq_left h]

lemma support_extZero_subset (g : ℍ → ℂ) :
    Function.support (extZero g) ⊆ UpperHalfPlane.coe '' tsupport g := by
  intro w hw
  simp only [extZero, Function.mem_support, ne_eq] at hw
  split_ifs at hw with h
  · exact ⟨⟨w, h⟩, subset_tsupport _ hw, rfl⟩
  · exact absurd rfl hw

lemma isCompact_image_tsupport {g : ℍ → ℂ} (hgc : HasCompactSupport g) :
    IsCompact (UpperHalfPlane.coe '' tsupport g) :=
  hgc.isCompact.image continuous_coe

lemma tsupport_extZero_subset {g : ℍ → ℂ} (hgc : HasCompactSupport g) :
    tsupport (extZero g) ⊆ UpperHalfPlane.coe '' tsupport g :=
  closure_minimal (support_extZero_subset g) (isCompact_image_tsupport hgc).isClosed

lemma image_tsupport_subset (g : ℍ → ℂ) :
    UpperHalfPlane.coe '' tsupport g ⊆ {w : ℂ | 0 < w.im} := by
  rintro _ ⟨z, _, rfl⟩
  exact z.im_pos

lemma continuous_extZero {g : ℍ → ℂ} (hg : Continuous g) (hgc : HasCompactSupport g) :
    Continuous (extZero g) := by
  rw [continuous_iff_continuousAt]
  intro w
  by_cases hw : 0 < w.im
  · have hopen : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
    have heq : extZero g =ᶠ[𝓝 w] fun v => g (ofComplex v) := by
      filter_upwards [hopen.mem_nhds hw] with v hv
      simp only [extZero, dite_eq_left (show 0 < v.im from hv), ofComplex_apply_of_im_pos hv]
    refine ContinuousAt.congr ?_ heq.symm
    exact hg.continuousAt.comp ((isOpenEmbedding_coe.toOpenPartialHomeomorph).continuousAt_symm
      (by simp; exact hw) |> fun h => by simpa [ofComplex] using h)
  · have hK := (isCompact_image_tsupport hgc).isClosed
    have hnot : w ∉ UpperHalfPlane.coe '' tsupport g := fun h => hw (image_tsupport_subset g h)
    have hzero : extZero g =ᶠ[𝓝 w] fun _ => 0 := by
      filter_upwards [hK.isOpen_compl.mem_nhds hnot] with v hv
      by_contra hne
      exact hv (support_extZero_subset g hne)
    have hw0 : extZero g w = 0 := by simp [extZero, hw]
    rw [ContinuousAt, hw0]
    exact tendsto_const_nhds.congr' hzero.symm

lemma eq_zero_of_notMem_image {g : ℍ → ℂ} {w : ℂ} (hw : w ∉ UpperHalfPlane.coe '' tsupport g) :
    extZero g w = 0 := by
  by_contra h
  exact hw (support_extZero_subset g h)

/-- Every continuous compactly supported `g` on `ℍ` is `L²`-close to a test function. -/
theorem exists_testFn_eLpNorm_sub_le {g : ℍ → ℂ} (hg : Continuous g) (hgc : HasCompactSupport g)
    {η : ℝ≥0∞} (hη : η ≠ 0) :
    ∃ F : testFn, eLpNorm (g - fun z : ℍ => (F : ℂ → ℂ) z) 2 volume ≤ η := by
  set G := extZero g with hGdef
  have hG : Continuous G := continuous_extZero hg hgc
  have hK : IsCompact (UpperHalfPlane.coe '' tsupport g) := isCompact_image_tsupport hgc
  have hopen : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
  obtain ⟨δ, hδ, hδsub⟩ := hK.exists_cthickening_subset_open hopen (image_tsupport_subset g)
  set S := cthickening δ (UpperHalfPlane.coe '' tsupport g) with hS
  have hScomp : IsCompact S := hK.cthickening
  set S' : Set ℍ := UpperHalfPlane.coe ⁻¹' S with hS'
  have hS'comp : IsCompact S' := by
    have hemb := isOpenEmbedding_coe.isEmbedding
    rw [hemb.isCompact_iff, Set.image_preimage_eq_of_subset (fun w hw => ⟨⟨w, hδsub hw⟩, rfl⟩)]
    exact hScomp
  have hS'fin : volume S' ≠ ⊤ := hS'comp.measure_lt_top.ne
  set C : ℝ≥0∞ := volume S' ^ (2 : ℝ≥0∞).toReal⁻¹ with hCdef
  have hC : C ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hS'fin
  obtain ⟨ε', hε'pos, hε'⟩ := ENNReal.exists_nnreal_pos_mul_lt hC hη
  have hGc : HasCompactSupport G := HasCompactSupport.intro hK fun w hw => eq_zero_of_notMem_image hw
  have huc : UniformContinuous G := hGc.uniformContinuous_of_continuous hG
  obtain ⟨r0, hr0, hr0'⟩ := Metric.uniformContinuous_iff.mp huc (ε' : ℝ) (by exact_mod_cast hε'pos)
  set r := min r0 δ / 2 with hrdef
  have hr : 0 < r := by positivity
  have hrr0 : r < r0 := by have := min_le_left r0 δ; linarith
  have hrδ : r ≤ δ := by have := min_le_right r0 δ; linarith
  let φ : ContDiffBump (0 : ℂ) := ⟨r / 2, r, by positivity, by linarith⟩
  set F : ℂ → ℂ := φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] G with hFdef
  have hFsmooth : ContDiff ℝ ∞ F :=
    φ.hasCompactSupport_normed.contDiff_convolution_left _ φ.contDiff_normed hG.locallyIntegrable
  have hFsupp : Function.support F ⊆ S := by
    intro x hx
    obtain ⟨b, hb, k, hk, rfl⟩ := support_convolution_subset (ContinuousLinearMap.lsmul ℝ ℝ) hx
    rw [φ.support_normed_eq, mem_ball, dist_zero_right] at hb
    have hk' : k ∈ UpperHalfPlane.coe '' tsupport g := by
      by_contra h; exact hk (eq_zero_of_notMem_image h)
    refine mem_cthickening_of_dist_le _ k _ _ hk' ?_
    rw [dist_eq_norm, add_sub_cancel_right]
    exact (le_of_lt hb).trans hrδ
  have hFtsupp : tsupport F ⊆ S := closure_minimal hFsupp hScomp.isClosed
  have hFtest : IsTestFn F := ⟨hFsmooth, HasCompactSupport.intro hScomp fun x hx => by
    by_contra h; exact hx (hFsupp h), hFtsupp.trans hδsub⟩
  refine ⟨⟨F, hFtest⟩, ?_⟩
  have hbound : ∀ a, dist (F a) (G a) ≤ ε' := fun a =>
    φ.dist_normed_convolution_le hG.aestronglyMeasurable fun x hx =>
      (hr0' (lt_trans (mem_ball.mp hx) hrr0)).le
  set h : ℍ → ℂ := g - fun z : ℍ => F z with hhdef
  have hhz : ∀ z : ℍ, h z = G z - F z := fun z => by simp [hhdef, extZero_coe, hGdef]
  have hhS : h = S'.indicator h := by
    funext z
    by_cases hz : z ∈ S'
    · simp [hz]
    · rw [Set.indicator_of_notMem hz, hhz]
      have h1 : (z : ℂ) ∉ UpperHalfPlane.coe '' tsupport g := fun h' => hz (self_subset_cthickening _ h')
      have h2 : (z : ℂ) ∉ Function.support F := fun h' => hz (hFsupp h')
      rw [show G (z : ℂ) = 0 from eq_zero_of_notMem_image h1, Function.notMem_support.mp h2, sub_zero]
  have hmeas : MeasurableSet S' := hS'comp.isClosed.measurableSet
  have hhmeas : AEStronglyMeasurable h (volume.restrict S') :=
    (hg.sub (hFsmooth.continuous.comp continuous_coe)).aestronglyMeasurable
  calc eLpNorm h 2 volume = eLpNorm (S'.indicator h) 2 volume := by rw [← hhS]
    _ = eLpNorm h 2 (volume.restrict S') := eLpNorm_indicator_eq_eLpNorm_restrict hmeas.nullMeasurableSet
    _ ≤ (volume.restrict S') Set.univ ^ (2 : ℝ≥0∞).toReal⁻¹ * ENNReal.ofReal ε' :=
        eLpNorm_le_of_ae_bound hhmeas (Filter.Eventually.of_forall fun z => by
          rw [hhz, ← dist_eq_norm, dist_comm]; exact hbound z)
    _ = C * ε' := by
        rw [Measure.restrict_apply_univ, ENNReal.ofReal_coe_nnreal]
    _ ≤ η := by rw [mul_comm]; exact hε'.le

/-- Test functions are dense in `L²(ℍ, dx dy / y²)`. -/
theorem denseRange_toL2 : DenseRange (toL2 : testFn → Lp ℂ 2 (volume : Measure ℍ)) := by
  rw [Metric.denseRange_iff]
  intro f ε hε
  have hε3 : ENNReal.ofReal (ε / 3) ≠ 0 := by simp; linarith
  obtain ⟨g, hgc, hfg, hgcont, hgLp⟩ := (Lp.memLp f).exists_hasCompactSupport_eLpNorm_sub_le
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hε3
  obtain ⟨F, hF⟩ := exists_testFn_eLpNorm_sub_le hgcont hgc hε3
  refine ⟨F, ?_⟩
  rw [dist_eq_norm, Lp.norm_def]
  have hcoe : ⇑(toL2 F) =ᵐ[volume] fun z : ℍ => (F : ℂ → ℂ) z := MemLp.coeFn_toLp (memLp_comp_coe F.2)
  have hae : ⇑(f - toL2 F) =ᵐ[volume] (⇑f - g) + (g - fun z : ℍ => (F : ℂ → ℂ) z) := by
    filter_upwards [Lp.coeFn_sub f (toL2 F), hcoe] with z h1 h2
    rw [h1, Pi.sub_apply, h2]; simp
  rw [eLpNorm_congr_ae hae]
  have htri := eLpNorm_add_le (μ := (volume : Measure ℍ)) (f := ⇑f - g)
    (g := g - fun z : ℍ => (F : ℂ → ℂ) z) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hsum : eLpNorm ((⇑f - g) + (g - fun z : ℍ => (F : ℂ → ℂ) z)) 2 volume
      ≤ ENNReal.ofReal (2 * (ε / 3)) := by
    calc _ ≤ _ := htri
      _ ≤ ENNReal.ofReal (ε / 3) + ENNReal.ofReal (ε / 3) := add_le_add hfg hF
      _ = ENNReal.ofReal (2 * (ε / 3)) := by
        rw [← ENNReal.ofReal_add (by linarith) (by linarith)]; ring_nf
  have hfin : eLpNorm ((⇑f - g) + (g - fun z : ℍ => (F : ℂ → ℂ) z)) 2 volume ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hsum
  calc (eLpNorm _ 2 volume).toReal ≤ (ENNReal.ofReal (2 * (ε / 3))).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hsum
    _ = 2 * (ε / 3) := ENNReal.toReal_ofReal (by linarith)
    _ < ε := by linarith

end Qschubert
