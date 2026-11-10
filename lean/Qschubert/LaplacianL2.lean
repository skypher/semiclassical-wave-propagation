import Qschubert.LaplacianSymm
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# The Laplacian on test functions as an operator in `L²(ℍ)`

Spine stage S2 (`lean/BLUEPRINT.md`). Test functions (`IsTestFn`) form a submodule; `toL2` maps
them into `L²(ℍ, dx dy / y²)`; it is injective because the measure charges every nonempty open set.
-/

namespace Qschubert

open UpperHalfPlane MeasureTheory Complex Topology
open scoped ComplexConjugate ENNReal

instance : (volume.comap UpperHalfPlane.coe : Measure ℍ).IsOpenPosMeasure :=
  Measure.IsOpenPosMeasure.comap volume isOpenEmbedding_coe

/-- The hyperbolic measure charges every nonempty open subset of `ℍ`. -/
instance : (volume : Measure ℍ).IsOpenPosMeasure :=
  ⟨fun U hU hne => by
    rw [volume_def, Ne, withDensity_apply_eq_zero measurable_density.coe_nnreal_ennreal]
    have hpos : {z : ℍ | (((1 / NNReal.mk z.im z.im_pos.le : NNReal) ^ 2 : NNReal) : ℝ≥0∞) ≠ 0}
        = Set.univ := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true, ne_eq, ENNReal.coe_eq_zero]
      exact pow_ne_zero _ (one_div_ne_zero (NNReal.ne_iff.mp z.im_ne_zero))
    rw [hpos, Set.univ_inter]
    exact hU.measure_ne_zero _ hne⟩

/-- Test functions as a submodule of `ℂ → ℂ`. -/
def testFn : Submodule ℂ (ℂ → ℂ) where
  carrier := {F | IsTestFn F}
  add_mem' {F G} hF hG :=
    ⟨hF.smooth.add hG.smooth, hF.compact.add hG.compact,
      (tsupport_add F G).trans (Set.union_subset hF.inside hG.inside)⟩
  zero_mem' := ⟨contDiff_const, HasCompactSupport.zero, by simp⟩
  smul_mem' c {F} hF :=
    ⟨contDiff_const.smul hF.smooth, hF.compact.smul_left,
      (tsupport_smul_subset_right (fun _ => c) F).trans hF.inside⟩

lemma hasCompactSupport_comp_coe {F : ℂ → ℂ} (hF : IsTestFn F) :
    HasCompactSupport (fun z : ℍ => F z) := by
  have hemb : Topology.IsEmbedding (UpperHalfPlane.coe) := isOpenEmbedding_coe.isEmbedding
  have himage : UpperHalfPlane.coe '' (UpperHalfPlane.coe ⁻¹' tsupport F) = tsupport F := by
    apply Set.image_preimage_eq_of_subset
    intro w hw
    exact ⟨⟨w, hF.inside hw⟩, rfl⟩
  have hK : IsCompact (UpperHalfPlane.coe ⁻¹' tsupport F) := by
    rw [hemb.isCompact_iff, himage]; exact hF.compact
  refine HasCompactSupport.intro hK fun z hz => ?_
  exact image_eq_zero_of_notMem_tsupport hz

lemma memLp_comp_coe {F : ℂ → ℂ} (hF : IsTestFn F) :
    MemLp (fun z : ℍ => F z) 2 (volume : Measure ℍ) :=
  (hF.smooth.continuous.comp continuous_coe).memLp_of_hasCompactSupport (hasCompactSupport_comp_coe hF)

/-- The map from test functions to `L²(ℍ, dx dy / y²)`. -/
noncomputable def toL2 : testFn →ₗ[ℂ] Lp ℂ 2 (volume : Measure ℍ) where
  toFun F := (memLp_comp_coe F.2).toLp _
  map_add' F G := by
    rw [← MemLp.toLp_add]; rfl
  map_smul' c F := by
    rw [← MemLp.toLp_const_smul]; rfl

lemma toL2_injective : Function.Injective toL2 := by
  intro F G h
  have hae := (MemLp.toLp_eq_toLp_iff (memLp_comp_coe F.2) (memLp_comp_coe G.2)).mp h
  have hc : (fun z : ℍ => (F : ℂ → ℂ) z) = fun z : ℍ => (G : ℂ → ℂ) z :=
    Continuous.ae_eq_iff_eq _ (F.2.smooth.continuous.comp continuous_coe)
      (G.2.smooth.continuous.comp continuous_coe) |>.mp hae
  apply Subtype.ext
  funext w
  by_cases hw : 0 < w.im
  · exact congrFun hc ⟨w, hw⟩
  · have h1 : w ∉ tsupport (F : ℂ → ℂ) := fun h' => hw (F.2.inside h')
    have h2 : w ∉ tsupport (G : ℂ → ℂ) := fun h' => hw (G.2.inside h')
    rw [image_eq_zero_of_notMem_tsupport h1, image_eq_zero_of_notMem_tsupport h2]

end Qschubert
