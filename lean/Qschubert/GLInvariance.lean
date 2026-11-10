import Qschubert.FriedrichsNat
import Qschubert.TestTransport
import Qschubert.EllipticId
import Qschubert.PGLAction

/-!
# `-Δ` commutes with the isometries of `ℍ`

For `g ∈ GL(2, ℝ)`, `U_g f = f ∘ (g •)` is a unitary of `L²(ℍ)` (`glU`; the action preserves
`dx dy / y²`), it maps test functions to test functions (`toL2_testCompT`) and commutes with `Δ`
there (`lapTest_testCompT`, from `lapH_testComp`). By the naturality of the Friedrichs extension
(`friedrichsExt_U`), `U_g` maps `Dom(-Δ)` onto itself and `-Δ U_g = U_g (-Δ)` (`negLapH_glU`).
With `g = [[y₀, x₀], [0, 1]]` this transports the local Sobolev chart at `i` to every centre.
-/

namespace Qschubert

open MeasureTheory UpperHalfPlane Physicslib4.Spectral.Unbounded

local notation "L2H" => Lp ℂ 2 (volume : Measure ℍ)

lemma measurePreserving_gl (g : GL (Fin 2) ℝ) : MeasurePreserving (fun z : ℍ => g • z) volume volume :=
  measurePreserving_smul g volume

/-- `f ↦ f ∘ (g •)` on `L²(ℍ)`. -/
noncomputable def glUL (g : GL (Fin 2) ℝ) : L2H →ₗᵢ[ℂ] L2H :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun z : ℍ => g • z) (measurePreserving_gl g)

lemma glUL_ae (g : GL (Fin 2) ℝ) (f : L2H) : ⇑(glUL g f) =ᵐ[volume] fun z => f (g • z) :=
  Lp.coeFn_compMeasurePreserving f _

lemma comp_gl_ae (g : GL (Fin 2) ℝ) {a b : ℍ → ℂ} (h : a =ᵐ[volume] b) :
    (fun z => a (g • z)) =ᵐ[volume] fun z => b (g • z) :=
  (measurePreserving_gl g).quasiMeasurePreserving.ae_eq_comp h

lemma glUL_glUL_inv (g : GL (Fin 2) ℝ) (f : L2H) : glUL g (glUL g⁻¹ f) = f := by
  apply Lp.ext
  filter_upwards [glUL_ae g (glUL g⁻¹ f), comp_gl_ae g (glUL_ae g⁻¹ f)] with z e1 e2
  rw [e1, e2, inv_smul_smul]

/-- `U_g` as a unitary. -/
noncomputable def glU (g : GL (Fin 2) ℝ) : L2H ≃ₗᵢ[ℂ] L2H :=
  LinearIsometryEquiv.ofSurjective (glUL g) fun f => ⟨glUL g⁻¹ f, glUL_glUL_inv g f⟩

lemma glU_apply (g : GL (Fin 2) ℝ) (f : L2H) : glU g f = glUL g f := rfl

lemma glU_symm (g : GL (Fin 2) ℝ) : (glU g).symm = glU g⁻¹ := by
  ext1 f
  apply (glU g).injective
  rw [LinearIsometryEquiv.apply_symm_apply, glU_apply, glU_apply, glUL_glUL_inv]

/-- `F ∘ g` as a test function. -/
noncomputable def testCompT (g : GL (Fin 2) ℝ) (F : testFn) : testFn :=
  ⟨testComp g F, isTestFn_testComp F.2 g⟩

lemma toL2_testCompT (g : GL (Fin 2) ℝ) (F : testFn) : toL2 (testCompT g F) = glU g (toL2 F) := by
  apply Lp.ext
  have h1 : ⇑(toL2 (testCompT g F)) =ᵐ[volume] fun z : ℍ => ((testCompT g F : testFn) : ℂ → ℂ) z :=
    (memLp_comp_coe (testCompT g F).2).coeFn_toLp
  have h2 : ⇑(toL2 F) =ᵐ[volume] fun z : ℍ => (F : ℂ → ℂ) z := (memLp_comp_coe F.2).coeFn_toLp
  filter_upwards [h1, glUL_ae g (toL2 F), comp_gl_ae g h2] with z e1 e2 e3
  rw [e1, glU_apply, e2, e3]
  exact testComp_coe g F z

lemma lapTest_testCompT (g : GL (Fin 2) ℝ) (F : testFn) :
    lapTest (testCompT g F) = testCompT g (lapTest F) := by
  apply Subtype.ext; funext w
  by_cases hw : 0 < w.im
  · set z : ℍ := ⟨w, hw⟩
    show ((lapTest (testCompT g F) : testFn) : ℂ → ℂ) (z : ℂ) = testComp g (lapTest F) (z : ℂ)
    rw [lapTest_coe, testComp_coe, lapTest_coe]
    exact lapH_testComp F.2 g z
  · rw [testFn_eq_zero _ hw, testFn_eq_zero (testCompT g (lapTest F)) hw]

/-- `U_g` preserves `-Δ` on test functions. -/
theorem preservesOp_gl (g : GL (Fin 2) ℝ) : PreservesOp negLap (glU g) where
  mem x hx := by
    obtain ⟨F, rfl⟩ := hx
    exact ⟨testCompT g F, toL2_testCompT g F⟩
  comm x hx := by
    obtain ⟨F, rfl⟩ := toL2Equiv.surjective x
    have heq : (⟨glU g (toL2Equiv F : lapDomain), hx⟩ : negLap.domain) = toL2Equiv (testCompT g F) :=
      Subtype.ext (toL2_testCompT g F).symm
    rw [heq, negLap_toL2Equiv, negLap_toL2Equiv, lapTest_testCompT, toL2_testCompT, map_neg]

/-- **`-Δ` commutes with every isometry `g ∈ GL(2, ℝ)` of `ℍ`**: `U_g` maps `Dom(-Δ)` into itself
and `-Δ U_g = U_g (-Δ)`. -/
theorem negLapH_glU (g : GL (Fin 2) ℝ) (u : negLapH.domain) :
    ∃ h : glU g u ∈ negLapH.domain, negLapH ⟨glU g u, h⟩ = glU g (negLapH u) := by
  have hsymm : PreservesOp negLap (glU g).symm := by rw [glU_symm]; exact preservesOp_gl g⁻¹
  exact friedrichsExt_U negLap negLap_hasDenseDomain (preservesOp_gl g) hsymm u

end Qschubert
