import Qschubert.Mobius
import Qschubert.LaplacianL2

/-!
# Test functions are carried to test functions by `GL(2, ℝ)`

Spine stage S4 (`lean/BLUEPRINT.md`). For a test function `F` and `g ∈ GL(2, ℝ)`, `testComp g F` is
`w ↦ F(g w)` on `ℍ`, extended by `0`. It is again a test function (`isTestFn_testComp`), and
`Δ (F ∘ g) = (ΔF) ∘ g` (`lapH_testComp`).
-/

namespace Qschubert

open Complex Filter Topology
open scoped ComplexConjugate ContDiff MatrixGroups UpperHalfPlane Pointwise

/-- `F ∘ g` on `ℍ`, `0` off `ℍ`. -/
noncomputable def testComp (g : GL (Fin 2) ℝ) (F : ℂ → ℂ) (w : ℂ) : ℂ :=
  if h : 0 < w.im then F ((g • (⟨w, h⟩ : ℍ) : ℍ) : ℂ) else 0

lemma testComp_coe (g : GL (Fin 2) ℝ) (F : ℂ → ℂ) (z : ℍ) :
    testComp g F z = F ((g • z : ℍ) : ℂ) := by
  rw [testComp, dite_eq_left (show 0 < (z : ℂ).im from z.im_pos)]

lemma contDiff_σ (g : GL (Fin 2) ℝ) : ContDiff ℝ ∞ (fun w => UpperHalfPlane.σ g w) := by
  unfold UpperHalfPlane.σ
  split_ifs
  · exact contDiff_id
  · exact Complex.conjCLE.contDiff

lemma contDiffAt_moeb (g : GL (Fin 2) ℝ) (z : ℍ) : ContDiffAt ℝ ∞ (moeb g) (z : ℂ) :=
  (((differentiableOn_moeb g).contDiffOn (isOpen_denom_ne g)).contDiffAt
    ((isOpen_denom_ne g).mem_nhds (UpperHalfPlane.denom_ne_zero g z))).restrict_scalars ℝ

/-- The support of `testComp g F` lies in the image in `ℂ` of `g⁻¹ (tsupport F)`, a compact set. -/
lemma isCompact_testComp_set {F : ℂ → ℂ} (hF : IsTestFn F) (g : GL (Fin 2) ℝ) :
    IsCompact ((fun z : ℍ => (z : ℂ)) '' {z : ℍ | ((g • z : ℍ) : ℂ) ∈ tsupport F}) := by
  have hK : IsCompact ((fun z : ℍ => (z : ℂ)) ⁻¹' tsupport F) :=
    (UpperHalfPlane.isEmbedding_coe.isInducing.isCompact_preimage_iff (by
      intro w hw; exact ⟨⟨w, hF.inside hw⟩, rfl⟩)).2 hF.compact
  have e : {z : ℍ | ((g • z : ℍ) : ℂ) ∈ tsupport F}
      = (fun z : ℍ => g⁻¹ • z) '' ((fun z : ℍ => (z : ℂ)) ⁻¹' tsupport F) := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_image, Set.mem_preimage]
    constructor
    · intro h; exact ⟨g • z, h, by simp⟩
    · rintro ⟨w, hw, rfl⟩; simpa using hw
  rw [e]
  exact (hK.image (continuous_const_smul g⁻¹)).image UpperHalfPlane.continuous_coe

lemma support_testComp_subset (F : ℂ → ℂ) (g : GL (Fin 2) ℝ) :
    Function.support (testComp g F)
      ⊆ (fun z : ℍ => (z : ℂ)) '' {z : ℍ | ((g • z : ℍ) : ℂ) ∈ tsupport F} := by
  intro w hw
  by_cases h : 0 < w.im
  · refine ⟨⟨w, h⟩, ?_, rfl⟩
    have : F ((g • (⟨w, h⟩ : ℍ) : ℍ) : ℂ) ≠ 0 := by
      simpa [testComp, h] using hw
    exact subset_tsupport _ this
  · exact absurd (by simp [testComp, h]) hw

/-- `F ∘ g` is a test function. -/
theorem isTestFn_testComp {F : ℂ → ℂ} (hF : IsTestFn F) (g : GL (Fin 2) ℝ) :
    IsTestFn (testComp g F) := by
  set C := (fun z : ℍ => (z : ℂ)) '' {z : ℍ | ((g • z : ℍ) : ℂ) ∈ tsupport F}
  have hC : IsCompact C := isCompact_testComp_set hF g
  have hts : tsupport (testComp g F) ⊆ C :=
    closure_minimal (support_testComp_subset F g) hC.isClosed
  have hCH : C ⊆ {w : ℂ | 0 < w.im} := by rintro _ ⟨z, _, rfl⟩; exact z.im_pos
  have hopen : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
  refine ⟨?_, IsCompact.of_isClosed_subset hC (isClosed_tsupport _) hts, hts.trans hCH⟩
  refine contDiff_iff_contDiffAt.2 fun w => ?_
  by_cases h : 0 < w.im
  · have hloc : testComp g F =ᶠ[𝓝 w] fun y => F (UpperHalfPlane.σ g (moeb g y)) := by
      filter_upwards [hopen.mem_nhds h] with y hy
      rw [testComp, dite_eq_left hy]
      rfl
    have hd : ContDiffAt ℝ ∞ (fun y => F (UpperHalfPlane.σ g (moeb g y))) w :=
      hF.smooth.contDiffAt.comp w ((contDiff_σ g).contDiffAt.comp w
        (contDiffAt_moeb g ⟨w, h⟩))
    exact hd.congr_of_eventuallyEq hloc
  · have hw : w ∉ C := fun hw => h (hCH hw)
    have hloc : testComp g F =ᶠ[𝓝 w] fun _ => 0 := by
      filter_upwards [hC.isClosed.isOpen_compl.mem_nhds hw] with y hy
      exact Function.notMem_support.1 fun hs => hy (support_testComp_subset F g hs)
    exact contDiffAt_const.congr_of_eventuallyEq hloc

/-- `Δ (F ∘ g) = (ΔF) ∘ g` for a test function `F`. -/
theorem lapH_testComp {F : ℂ → ℂ} (hF : IsTestFn F) (g : GL (Fin 2) ℝ) (z : ℍ) :
    lapH (fun w : ℍ => testComp g F w) z = lapH (fun w : ℍ => F w) (g • z) := by
  have e : (fun w : ℍ => testComp g F w) = fun w : ℍ => F ((g • w : ℍ) : ℂ) :=
    funext fun w => testComp_coe g F w
  have hA : ContDiffAt ℝ 2 (extC fun u : ℍ => F u) ((g • z : ℍ) : ℂ) :=
    (hF.smooth.contDiffAt.of_le (by norm_num)).congr_of_eventuallyEq
      (extC_eventuallyEq (fun w => rfl) (g • z))
  rw [e]
  exact lapH_comp_smul g (A := fun u : ℍ => F u) z hA

end Qschubert
