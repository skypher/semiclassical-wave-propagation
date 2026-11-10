import Qschubert.Periodize
import Qschubert.TestTransport
import Qschubert.LaplacianOp

/-!
# `Δ` on periodized test functions in `L²(M)`

Spine stage S4 (`lean/BLUEPRINT.md`). For a Fuchsian `Γ` and test functions `F, G`:
on the support of `u`, `v_Γ` is the finite sum of `v ∘ γ` over the transporter set
(`integral_conj_perio_mul`), and `⟪G_Γ, (ΔF)_Γ⟫_{L²(M)} = ⟪(ΔG)_Γ, F_Γ⟫_{L²(M)}` (`perioT_lap_symm`):
each translate `G ∘ γ` is a test function with `Δ(G ∘ γ) = (ΔG) ∘ γ`, and Green's identity on `ℍ`
applies term by term.
-/

namespace Qschubert

open MeasureTheory Complex Filter Topology
open scoped ComplexConjugate ContDiff MatrixGroups UpperHalfPlane Pointwise

/-- A representative in `GL(2, ℝ)` of `γ ∈ PGL(2, ℝ)`. -/
noncomputable def pglRep (γ : PGL(2, ℝ)) : GL (Fin 2) ℝ :=
  (Matrix.ProjGenLinGroup.mk_surjective γ).choose

lemma pglRep_smul (γ : PGL(2, ℝ)) (z : ℍ) : pglRep γ • z = γ • z := by
  conv_rhs => rw [← (Matrix.ProjGenLinGroup.mk_surjective γ).choose_spec]
  rw [UpperHalfPlane.pglMk_smul]
  rfl

/-- A test function as a function on `ℍ`. -/
def tfn (F : testFn) : ℍ → ℂ := fun z => (F : ℂ → ℂ) z

lemma continuous_tfn (F : testFn) : Continuous (tfn F) :=
  F.2.smooth.continuous.comp UpperHalfPlane.continuous_coe

lemma hasCompactSupport_tfn (F : testFn) : HasCompactSupport (tfn F) :=
  hasCompactSupport_comp_coe F.2

variable (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ]

/-- The transporter set `{γ : γ K ∩ L ≠ ∅}`. -/
def transp (K L : Set ℍ) : Set Γ := {γ | ((γ • ·) '' K ∩ L).Nonempty}

lemma transp_finite {K L : Set ℍ} (hK : IsCompact K) (hL : IsCompact L) : (transp Γ K L).Finite :=
  ProperlyDiscontinuousSMul.finite_disjoint_inter_image hK hL

/-- On the support of `u`, the periodization of `v` is a finite sum over the transporter set. -/
lemma integral_conj_perio_mul {u v : ℍ → ℂ} (hcu : Continuous u) (hu : HasCompactSupport u)
    (hcv : Continuous v) {K L : Set ℍ} (hK : IsCompact K)
    (hL : IsCompact L) (huK : tsupport u ⊆ K) (hvL : tsupport v ⊆ L) :
    ∫ z, conj (perio Γ v (surfMk Γ z)) * u z
      = ∑ γ ∈ (transp_finite Γ hK hL).toFinset, ∫ z, conj (v (γ • z)) * u z := by
  have hint : ∀ γ : Γ, Integrable fun z => conj (v (γ • z)) * u z := fun γ =>
    ((Complex.continuous_conj.comp (hcv.comp (continuous_const_smul γ))).mul hcu).integrable_of_hasCompactSupport
      hu.mul_left
  rw [← integral_finsetSum _ (fun γ _ => hint γ)]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  show conj (perio Γ v (surfMk Γ z)) * u z = ∑ γ ∈ _, conj (v (γ • z)) * u z
  by_cases hz : u z = 0
  · simp [hz]
  · have hzK : z ∈ K := huK (subset_tsupport _ hz)
    rw [perio_mk, tsum_eq_sum (s := (transp_finite Γ hK hL).toFinset) ?_, map_sum, Finset.sum_mul]
    intro γ hγ
    by_contra hne
    apply hγ
    rw [Set.Finite.mem_toFinset]
    exact ⟨γ • z, ⟨z, hzK, rfl⟩, hvL (subset_tsupport _ hne)⟩

/-- `F_Γ ∈ L²(M)` for a test function `F`. -/
noncomputable def perioT (F : testFn) : Lp ℂ 2 (surfMeasure Γ) :=
  perioL2 Γ (continuous_tfn F) (hasCompactSupport_tfn F)

lemma tfn_lapTest (F : testFn) (z : ℍ) : tfn (lapTest F) z = lapH (fun w : ℍ => (F : ℂ → ℂ) w) z :=
  lapTest_coe F z

/-- Green's identity against a translate: `∫ conj(G(γz)) (ΔF)(z) = ∫ conj((ΔG)(γz)) F(z)`. -/
lemma integral_translate_lap (F G : testFn) (γ : PGL(2, ℝ)) :
    ∫ z, conj (tfn G (γ • z)) * tfn (lapTest F) z
      = ∫ z, conj (tfn (lapTest G) (γ • z)) * tfn F z := by
  have hG' : IsTestFn (testComp (pglRep γ) (G : ℂ → ℂ)) := isTestFn_testComp G.2 (pglRep γ)
  have h1 : ∀ z : ℍ, testComp (pglRep γ) (G : ℂ → ℂ) z = tfn G (γ • z) := fun z => by
    rw [testComp_coe, pglRep_smul]; rfl
  have h2 : ∀ z : ℍ, lapH (fun w : ℍ => testComp (pglRep γ) (G : ℂ → ℂ) w) z
      = tfn (lapTest G) (γ • z) := fun z => by
    rw [lapH_testComp G.2, pglRep_smul, tfn_lapTest]
  have hsym := lapH_symmetric F.2 hG'
  calc ∫ z, conj (tfn G (γ • z)) * tfn (lapTest F) z
      = ∫ z : ℍ, lapH (fun w : ℍ => (F : ℂ → ℂ) w) z
          * conj (testComp (pglRep γ) (G : ℂ → ℂ) z) := by
        congr 1; funext z; rw [h1, tfn_lapTest, mul_comm]
    _ = ∫ z : ℍ, (F : ℂ → ℂ) z
          * conj (lapH (fun w : ℍ => testComp (pglRep γ) (G : ℂ → ℂ) w) z) := hsym
    _ = ∫ z, conj (tfn (lapTest G) (γ • z)) * tfn F z := by
        congr 1; funext z; rw [h2, mul_comm]; rfl

lemma tsupport_tfn_subset (F : testFn) :
    tsupport (tfn F) ⊆ (fun z : ℍ => (z : ℂ)) ⁻¹' tsupport (F : ℂ → ℂ) :=
  tsupport_comp_subset_preimage _ UpperHalfPlane.continuous_coe

lemma tsupport_tfn_lapTest_subset (F : testFn) :
    tsupport (tfn (lapTest F)) ⊆ (fun z : ℍ => (z : ℂ)) ⁻¹' tsupport (F : ℂ → ℂ) := by
  have hsub : tsupport (lapTestFun (F : ℂ → ℂ)) ⊆ tsupport (F : ℂ → ℂ) :=
    (tsupport_mul_subset_right (f := fun w : ℂ => ((w.im : ℝ) : ℂ) ^ 2)).trans
      (tsupport_lapE_subset _)
  exact (tsupport_comp_subset_preimage _ UpperHalfPlane.continuous_coe).trans
    (Set.preimage_mono hsub)

lemma isCompact_preimage_tsupport (F : testFn) :
    IsCompact ((fun z : ℍ => (z : ℂ)) ⁻¹' tsupport (F : ℂ → ℂ)) :=
  (UpperHalfPlane.isEmbedding_coe.isInducing.isCompact_preimage_iff (by
    intro w hw; exact ⟨⟨w, F.2.inside hw⟩, rfl⟩)).2 F.2.compact

/-- **Symmetry**: `⟪G_Γ, (ΔF)_Γ⟫_{L²(M)} = ⟪(ΔG)_Γ, F_Γ⟫_{L²(M)}`. -/
theorem perioT_lap_symm (F G : testFn) :
    inner ℂ (perioT Γ G) (perioT Γ (lapTest F)) = inner ℂ (perioT Γ (lapTest G)) (perioT Γ F) := by
  have hK := isCompact_preimage_tsupport F
  have hL := isCompact_preimage_tsupport G
  rw [perioT, perioT, inner_perioL2, perioT, perioT, inner_perioL2,
    integral_conj_perio_mul Γ (continuous_tfn _) (hasCompactSupport_tfn _) (continuous_tfn _)
      hK hL (tsupport_tfn_lapTest_subset F) (tsupport_tfn_subset G),
    integral_conj_perio_mul Γ (continuous_tfn _) (hasCompactSupport_tfn _) (continuous_tfn _)
      hK hL (tsupport_tfn_subset F) (tsupport_tfn_lapTest_subset G)]
  refine Finset.sum_congr rfl fun γ _ => ?_
  exact integral_translate_lap F G γ

end Qschubert
