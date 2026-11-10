import Qschubert.Statements
import Mathlib.Analysis.Complex.UpperHalfPlane.ProperAction
import Mathlib.Topology.Algebra.Group.DiscontinuousSubgroup

/-!
# Schubert's Fuchsian groups act properly discontinuously

Closes the open item of R30 (`lean/BLUEPRINT.md`, representation choice 2). Schubert's Fuchsian
group is a discrete subgroup of `PSL(2, ℝ)`; its preimage `Γ'` in `SL(2, ℝ)` is discrete. For a
discrete `Γ' ≤ SL(2, ℝ)`, Mathlib proves that `Γ'` acts properly discontinuously on `ℍ`
(`instProperlyDiscontinuousSL2RSubgroup`, via properness of `g ↦ g • i`). Hence its image in
`PGL(2, ℝ)` acts properly discontinuously (`properlyDiscontinuous_map_toPGL`) and is
orientation-preserving (`orientationPreserving_map_toPGL`). The statements of
`Qschubert/Statements.lean`, quantified over such subgroups of `PGL(2, ℝ)`, therefore apply to every
Fuchsian group in Schubert's sense.
-/

namespace Qschubert

open Matrix
open scoped MatrixGroups UpperHalfPlane Pointwise

lemma toPGL_smul (g : SL(2, ℝ)) (z : ℍ) : SpecialLinearGroup.toPGL g • z = g • z := by
  show Matrix.ProjGenLinGroup.mk (SpecialLinearGroup.toGL g) • z = g • z
  rw [UpperHalfPlane.pglMk_smul]
  rfl

/-- The image in `PGL(2, ℝ)` of a discrete subgroup of `SL(2, ℝ)` acts properly discontinuously. -/
theorem properlyDiscontinuous_map_toPGL (Γ' : Subgroup SL(2, ℝ)) [DiscreteTopology Γ'] :
    ProperlyDiscontinuousSMul (Γ'.map SpecialLinearGroup.toPGL) ℍ := by
  have h : ProperlyDiscontinuousSMul Γ' ℍ := inferInstance
  rw [Subgroup.properlyDiscontinuousSMul_iff] at h ⊢
  intro K L hK hL
  refine ((h hK hL).image SpecialLinearGroup.toPGL).subset ?_
  rintro _ ⟨⟨g, hg, rfl⟩, hne⟩
  refine ⟨g, ⟨hg, ?_⟩, rfl⟩
  obtain ⟨w, ⟨z, hz, rfl⟩, hw⟩ := hne
  exact ⟨g • z, ⟨z, hz, rfl⟩, by rw [← toPGL_smul]; exact hw⟩

/-- The image in `PGL(2, ℝ)` of a subgroup of `SL(2, ℝ)` is orientation-preserving. -/
theorem orientationPreserving_map_toPGL (Γ' : Subgroup SL(2, ℝ)) :
    OrientationPreserving (Γ'.map SpecialLinearGroup.toPGL) := by
  rintro _ ⟨g, _, rfl⟩
  refine ⟨SpecialLinearGroup.toGL g, ?_, rfl⟩
  simp

end Qschubert
