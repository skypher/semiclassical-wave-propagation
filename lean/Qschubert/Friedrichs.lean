import Physicslib4.Spectral.Unbounded.Basic
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The Friedrichs extension

For a densely defined positive operator `T` (physicslib4's `IsPositive`: symmetric and
`0 ≤ Re ⟪ψ, Tψ⟫`) on a complex Hilbert space `H`, a self-adjoint positive extension.

Construction:
* `FormDom T`: the domain of `T` with the inner product `⟪x, y⟫_T := ⟪x, y⟫ + ⟪x, T y⟫`;
* `Q := Completion (FormDom T)`, and `ι : Q →L[ℂ] H` extending the inclusion (`‖ι u‖ ≤ ‖u‖`);
* the identity `⟪x, u⟫_Q = ⟪(1 + T) x, ι u⟫` for `x ∈ Dom T`, which gives injectivity of `ι`;
* `R := ι ∘ ι†`, bounded, self-adjoint and injective, and `S := R⁻¹ - 1`.

Spine stage S2 (`lean/BLUEPRINT.md`, representation choice 3).
-/

namespace Qschubert

open Physicslib4.Spectral.Unbounded
open scoped InnerProductSpace LinearPMap ComplexConjugate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The domain of `T`, to be given the form inner product. -/
def FormDom (T : H →ₗ.[ℂ] H) : Type _ := T.domain

namespace FormDom

variable (T : H →ₗ.[ℂ] H)

instance : AddCommGroup (FormDom T) := inferInstanceAs (AddCommGroup T.domain)
instance : Module ℂ (FormDom T) := inferInstanceAs (Module ℂ T.domain)

/-- The identity map to the domain of `T`. -/
def toDom (x : FormDom T) : T.domain := x

/-- The identity map from the domain of `T`. -/
def ofDom (y : T.domain) : FormDom T := y

@[simp] lemma toDom_ofDom (y : T.domain) : toDom T (ofDom T y) = y := rfl

lemma toDom_add (x y : FormDom T) : toDom T (x + y) = toDom T x + toDom T y := rfl
lemma toDom_smul (c : ℂ) (x : FormDom T) : toDom T (c • x) = c • toDom T x := rfl

/-- The underlying vector of `H`. -/
def val (x : FormDom T) : H := (toDom T x : H)

/-- `T` applied to a point of the form domain. -/
def app (x : FormDom T) : H := T (toDom T x)

lemma val_add (x y : FormDom T) : val T (x + y) = val T x + val T y := by
  simp [val, toDom_add]
lemma val_smul (c : ℂ) (x : FormDom T) : val T (c • x) = c • val T x := by
  simp [val, toDom_smul]
lemma app_add (x y : FormDom T) : app T (x + y) = app T x + app T y := by
  simp only [app, toDom_add]; exact T.toFun.map_add _ _
lemma app_smul (c : ℂ) (x : FormDom T) : app T (c • x) = c • app T x := by
  simp only [app, toDom_smul]; exact T.toFun.map_smul _ _

/-- The form inner product `⟪x, y⟫ + ⟪x, T y⟫`. -/
noncomputable def formInner (x y : FormDom T) : ℂ := ⟪val T x, val T y⟫_ℂ + ⟪val T x, app T y⟫_ℂ

variable {T}

/-- The inner product core of the form, for positive `T`. -/
noncomputable def core (hT : IsPositive T) : InnerProductSpace.Core ℂ (FormDom T) where
  inner := formInner T
  conj_inner_symm x y := by
    simp only [formInner, map_add, inner_conj_symm]
    congr 1
    exact (hT.1 (toDom T x) (toDom T y)).symm
  re_inner_nonneg x := by
    simp only [formInner]
    have h1 := inner_self_nonneg (𝕜 := ℂ) (x := val T x)
    rw [RCLike.re_to_complex] at h1
    exact add_nonneg h1 (hT.2 (toDom T x))
  add_left x y z := by
    simp only [formInner, val_add, inner_add_left]; ring
  smul_left x y c := by
    simp only [formInner, val_smul, inner_smul_left]; ring
  definite x hx := by
    have hre : (formInner T x x).re = 0 := by rw [hx]; rfl
    simp only [formInner, Complex.add_re] at hre
    have h1 : 0 ≤ (⟪val T x, val T x⟫_ℂ).re := by
      have := inner_self_nonneg (𝕜 := ℂ) (x := val T x); rwa [RCLike.re_to_complex] at this
    have h2 : 0 ≤ (⟪val T x, app T x⟫_ℂ).re := hT.2 (toDom T x)
    have h3 : (⟪val T x, val T x⟫_ℂ).re = 0 := by linarith
    have h4 : val T x = 0 := by
      rw [← inner_self_eq_zero (𝕜 := ℂ)]
      apply Complex.ext
      · simpa using h3
      · rw [inner_self_eq_norm_sq_to_K]; norm_cast
    exact Subtype.ext h4

end FormDom

namespace FormDom

variable (T : H →ₗ.[ℂ] H) [hT : Fact (IsPositive T)]

noncomputable instance instNormedAddCommGroup : NormedAddCommGroup (FormDom T) :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℂ (FormDom T) _ _ _ (core hT.out)

noncomputable instance instInnerProductSpace : InnerProductSpace ℂ (FormDom T) :=
  InnerProductSpace.ofCore (core hT.out).toCore

lemma inner_eq (x y : FormDom T) : ⟪x, y⟫_ℂ = formInner T x y := rfl

lemma norm_sq_eq (x : FormDom T) :
    ‖x‖ ^ 2 = ‖val T x‖ ^ 2 + (⟪val T x, app T x⟫_ℂ).re := by
  rw [@norm_sq_eq_re_inner ℂ, RCLike.re_to_complex, inner_eq, formInner, Complex.add_re,
    @norm_sq_eq_re_inner ℂ, RCLike.re_to_complex]

lemma norm_val_le (x : FormDom T) : ‖val T x‖ ≤ ‖x‖ := by
  have h := norm_sq_eq T x
  have h2 : 0 ≤ (⟪val T x, app T x⟫_ℂ).re := hT.out.2 (toDom T x)
  have h3 : ‖val T x‖ ^ 2 ≤ ‖x‖ ^ 2 := by rw [h]; linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h3

/-- The inclusion of the form domain into `H`, of norm at most `1`. -/
noncomputable def incl : FormDom T →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun := val T, map_add' := val_add T, map_smul' := val_smul T } 1
    (fun x => by simpa using norm_val_le T x)

lemma incl_apply (x : FormDom T) : incl T x = val T x := rfl

end FormDom

/-- The form domain completed: the form space `Q`. -/
abbrev FormSpace (T : H →ₗ.[ℂ] H) [Fact (IsPositive T)] := UniformSpace.Completion (FormDom T)

variable (T : H →ₗ.[ℂ] H) [hT : Fact (IsPositive T)]

/-- The extension `ι : Q →L[ℂ] H` of the inclusion. -/
noncomputable def formIncl [CompleteSpace H] : FormSpace T →L[ℂ] H :=
  (FormDom.incl T).extend (UniformSpace.Completion.toComplL : FormDom T →L[ℂ] FormSpace T)

variable [CompleteSpace H]

lemma formIncl_coe (x : FormDom T) : formIncl T (x : FormSpace T) = FormDom.val T x := by
  have := ContinuousLinearMap.extend_eq (FormDom.incl T)
    (e := (UniformSpace.Completion.toComplL : FormDom T →L[ℂ] FormSpace T))
    (UniformSpace.Completion.denseRange_coe) (UniformSpace.Completion.isUniformInducing_coe _) x
  exact this

/-- The key identity `⟪x, u⟫_Q = ⟪(1 + T) x, ι u⟫` for `x` in the domain of `T`. -/
lemma inner_coe_formSpace (x : FormDom T) (u : FormSpace T) :
    ⟪(x : FormSpace T), u⟫_ℂ = ⟪FormDom.val T x + FormDom.app T x, formIncl T u⟫_ℂ := by
  refine UniformSpace.Completion.induction_on u ?_ ?_
  · exact isClosed_eq (continuous_const.inner continuous_id)
      (continuous_const.inner (formIncl T).continuous)
  · intro y
    rw [UniformSpace.Completion.inner_coe, FormDom.inner_eq, FormDom.formInner, formIncl_coe,
      inner_add_left]
    congr 1
    exact hT.out.1 (FormDom.toDom T x) (FormDom.toDom T y)

/-- Closability: `ι` is injective. -/
lemma formIncl_injective : Function.Injective (formIncl T) := by
  rw [injective_iff_map_eq_zero]
  intro u hu'
  have h1 : ∀ v : FormSpace T, ⟪v, u⟫_ℂ = 0 := by
    intro v
    refine UniformSpace.Completion.induction_on v ?_ ?_
    · exact isClosed_eq (continuous_id.inner continuous_const) continuous_const
    · intro x; rw [inner_coe_formSpace, hu', inner_zero_right]
  exact inner_self_eq_zero.mp (h1 u)

lemma norm_formIncl_le : ‖formIncl T‖ ≤ 1 := by
  have h := ContinuousLinearMap.opNorm_extend_le (FormDom.incl T)
    (e := (UniformSpace.Completion.toComplL : FormDom T →L[ℂ] FormSpace T)) (N := 1)
    UniformSpace.Completion.denseRange_coe (fun x => by simp [UniformSpace.Completion.norm_coe])
  have h1 : ‖FormDom.incl T‖ ≤ 1 :=
    LinearMap.mkContinuous_norm_le _ zero_le_one _
  calc ‖formIncl T‖ ≤ (1 : NNReal) * ‖FormDom.incl T‖ := h
    _ ≤ 1 := by simpa using h1

/-- `R := ι ∘ ι†`, the inverse of `1 + S`. -/
noncomputable def formRes : H →L[ℂ] H := (formIncl T).comp (ContinuousLinearMap.adjoint (formIncl T))

lemma inner_formRes_left (f g : H) :
    ⟪formRes T f, g⟫_ℂ = ⟪ContinuousLinearMap.adjoint (formIncl T) f,
      ContinuousLinearMap.adjoint (formIncl T) g⟫_ℂ := by
  rw [formRes, ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.adjoint_inner_right]

lemma formRes_symm (f g : H) : ⟪formRes T f, g⟫_ℂ = ⟪f, formRes T g⟫_ℂ := by
  rw [inner_formRes_left, ← inner_conj_symm, ← inner_formRes_left, inner_conj_symm]

lemma adjoint_one_add (x : FormDom T) :
    ContinuousLinearMap.adjoint (formIncl T) (FormDom.val T x + FormDom.app T x) = (x : FormSpace T) := by
  apply ext_inner_right ℂ
  intro u
  rw [ContinuousLinearMap.adjoint_inner_left, inner_coe_formSpace]

lemma formRes_one_add (x : FormDom T) :
    formRes T (FormDom.val T x + FormDom.app T x) = FormDom.val T x := by
  rw [formRes, ContinuousLinearMap.comp_apply, adjoint_one_add, formIncl_coe]

lemma formRes_injective (hd : HasDenseDomain T) : Function.Injective (formRes T) := by
  rw [injective_iff_map_eq_zero]
  intro f hf
  have h0 : ContinuousLinearMap.adjoint (formIncl T) f = 0 := by
    have := inner_formRes_left T f f
    rw [hf, inner_zero_left] at this
    exact inner_self_eq_zero.mp this.symm
  have hperp : f ∈ T.domainᗮ := by
    rw [Submodule.mem_orthogonal]
    intro x hx
    have := ContinuousLinearMap.adjoint_inner_left (formIncl T) ((FormDom.ofDom T ⟨x, hx⟩ : FormDom T) : FormSpace T) f
    -- ⟪ι† f, x⟫ = ⟪f, ι x⟫
    rw [h0, inner_zero_left, formIncl_coe] at this
    have hval : FormDom.val T (FormDom.ofDom T ⟨x, hx⟩) = x := rfl
    rw [hval] at this
    rw [← inner_conj_symm, ← this, map_zero]
  rw [(dense_iff_orthogonal_eq_bot).mp hd] at hperp
  exact (Submodule.mem_bot ℂ).mp hperp

variable (hd : HasDenseDomain T)

/-- `H ≃ₗ Ran R`. -/
noncomputable def resEquiv : H ≃ₗ[ℂ] LinearMap.range (formRes T).toLinearMap :=
  LinearEquiv.ofInjective (formRes T).toLinearMap (formRes_injective T hd)

/-- The Friedrichs extension `S := R⁻¹ - 1` on `Ran R`. -/
noncomputable def friedrichsExt : H →ₗ.[ℂ] H :=
  ⟨LinearMap.range (formRes T).toLinearMap,
    (LinearMap.id - (formRes T).toLinearMap) ∘ₗ (resEquiv T hd).symm.toLinearMap⟩

lemma friedrichsExt_apply (f : H) :
    friedrichsExt T hd (resEquiv T hd f) = f - formRes T f := by
  show ((LinearMap.id - (formRes T).toLinearMap) ∘ₗ (resEquiv T hd).symm.toLinearMap) (resEquiv T hd f) = _
  rw [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_apply, LinearMap.sub_apply,
    LinearMap.id_apply]
  rfl

lemma coe_resEquiv (f : H) : ((resEquiv T hd f : LinearMap.range (formRes T).toLinearMap) : H) = formRes T f :=
  rfl

theorem le_friedrichsExt : T ≤ friedrichsExt T hd := by
  refine ⟨fun x hx => ⟨x + T ⟨x, hx⟩, ?_⟩, ?_⟩
  · have := formRes_one_add T (FormDom.ofDom T ⟨x, hx⟩)
    simpa [FormDom.val, FormDom.app] using this
  · intro x y hxy
    obtain ⟨f, rfl⟩ := (resEquiv T hd).surjective y
    rw [friedrichsExt_apply]
    have hR := formRes_one_add T (FormDom.ofDom T x)
    simp only [FormDom.val, FormDom.app, FormDom.toDom_ofDom] at hR
    have hf : f = (x : H) + T x := by
      apply formRes_injective T hd
      rw [hR, ← coe_resEquiv T hd f, ← hxy]
    rw [hf, hR]
    abel

theorem friedrichsExt_hasDenseDomain : HasDenseDomain (friedrichsExt T hd) :=
  Dense.mono (le_friedrichsExt T hd).1 hd

theorem friedrichsExt_isSymmetric : IsSymmetric (friedrichsExt T hd) := by
  intro φ ψ
  obtain ⟨f, rfl⟩ := (resEquiv T hd).surjective φ
  obtain ⟨g, rfl⟩ := (resEquiv T hd).surjective ψ
  rw [friedrichsExt_apply, friedrichsExt_apply, coe_resEquiv, coe_resEquiv, inner_sub_right,
    inner_sub_left, formRes_symm]

theorem friedrichsExt_nonneg (φ : (friedrichsExt T hd).domain) :
    0 ≤ (⟪(φ : H), friedrichsExt T hd φ⟫_ℂ).re := by
  obtain ⟨f, rfl⟩ := (resEquiv T hd).surjective φ
  rw [friedrichsExt_apply, coe_resEquiv, inner_sub_right, inner_formRes_left, Complex.sub_re]
  set u := ContinuousLinearMap.adjoint (formIncl T) f
  have h1 : (⟪u, u⟫_ℂ).re = ‖u‖ ^ 2 := by
    rw [@norm_sq_eq_re_inner ℂ, RCLike.re_to_complex]
  have h2 : (⟪formRes T f, formRes T f⟫_ℂ).re = ‖formRes T f‖ ^ 2 := by
    rw [@norm_sq_eq_re_inner ℂ, RCLike.re_to_complex]
  have h3 : ‖formRes T f‖ ≤ ‖u‖ := by
    calc ‖formRes T f‖ = ‖formIncl T u‖ := rfl
      _ ≤ ‖formIncl T‖ * ‖u‖ := (formIncl T).le_opNorm u
      _ ≤ 1 * ‖u‖ := by gcongr; exact norm_formIncl_le T
      _ = ‖u‖ := one_mul _
  rw [h1, h2]
  have := pow_le_pow_left₀ (norm_nonneg _) h3 2
  linarith

theorem friedrichsExt_isSelfAdjoint : IsSelfAdjoint (friedrichsExt T hd) := by
  rw [LinearPMap.isSelfAdjoint_def]
  have hdS := friedrichsExt_hasDenseDomain T hd
  have hle : friedrichsExt T hd ≤ (friedrichsExt T hd)† :=
    (isSymmetric_iff_le_adjoint hdS).mp (friedrichsExt_isSymmetric T hd)
  have hform := LinearPMap.adjoint_isFormalAdjoint (T := friedrichsExt T hd) hdS
  have key : ∀ ψ : (friedrichsExt T hd)†.domain,
      formRes T ((friedrichsExt T hd)† ψ + ψ) = ψ := by
    intro ψ
    apply ext_inner_right ℂ
    intro f
    have := hform ψ (resEquiv T hd f)
    rw [friedrichsExt_apply, coe_resEquiv, inner_sub_right] at this
    rw [formRes_symm, inner_add_left, this]
    ring
  refine le_antisymm ?_ hle
  refine ⟨fun x hx => ⟨_, key ⟨x, hx⟩⟩, ?_⟩
  intro ψ y hψy
  obtain ⟨f, rfl⟩ := (resEquiv T hd).surjective y
  rw [friedrichsExt_apply]
  have hf : f = (friedrichsExt T hd)† ψ + ψ := by
    apply formRes_injective T hd
    rw [key ψ, ← coe_resEquiv T hd f, ← hψy]
  rw [hf, key ψ]
  abel

include hd in
/-- **Friedrichs extension.** A densely defined positive operator has a self-adjoint positive
extension. -/
theorem exists_isSelfAdjoint_extension : ∃ S : H →ₗ.[ℂ] H,
    IsSelfAdjoint S ∧ T ≤ S ∧ IsPositive S :=
  ⟨friedrichsExt T hd, friedrichsExt_isSelfAdjoint T hd, le_friedrichsExt T hd,
    friedrichsExt_isSymmetric T hd, friedrichsExt_nonneg T hd⟩

end Qschubert
