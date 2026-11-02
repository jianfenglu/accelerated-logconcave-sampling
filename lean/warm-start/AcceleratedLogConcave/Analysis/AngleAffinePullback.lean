import AcceleratedLogConcave.Tensor.PhasePolynomialPullback

/-! Literal all-order coordinate derivatives under the fixed-midpoint affine
pullback. The midpoint is a parameter, not a random variable requiring moments. -/
noncomputable section
open scoped ContDiff
namespace AcceleratedLogConcave.Tensor.PolynomialClosure
open AdjointReduction Conditional.Appell
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem dir_comp_affine {f : F → ℝ} (hf : ContDiff ℝ ∞ f)
    (M : F) (L : E →L[ℝ] F) (v : E) :
    dir v (fun x => f (M+L x)) = fun x => dir (L v) f (M+L x) := by
  funext x
  have hg : HasFDerivAt (fun y => M+L y) L x := L.hasFDerivAt.const_add M
  have hh := ((hf.differentiable (by simp) (M+L x)).hasFDerivAt).comp x hg
  change fderiv ℝ (fun y => f (M+L y)) x v = fderiv ℝ f (M+L x) (L v)
  exact congrArg (fun A : E →L[ℝ] ℝ => A v) hh.fderiv

theorem partialAlong_comp_affine {f : F → ℝ} (hf : ContDiff ℝ ∞ f)
    (M : F) (L : E →L[ℝ] F) (J : List E) :
    partialAlong id J (fun x => f (M+L x)) =
      fun x => partialAlong id (J.map L) f (M+L x) := by
  induction J with
  | nil => rfl
  | cons v J ih =>
    simp only [partialAlong,List.map_cons,id_eq,ih]
    exact dir_comp_affine (contDiff_partialAlong id (J.map L) hf) M L v

theorem HasPolynomialJets.comp_affine {f : F → ℝ} (hf : HasPolynomialJets f)
    (hs : ContDiff ℝ ∞ f) (M : F) (L : E →L[ℝ] F) :
    HasPolynomialJets (fun x => f (M+L x)) := by
  intro J
  rw [partialAlong_comp_affine hs]
  obtain ⟨C,hC,n,hf⟩ := hf (J.map L)
  have hA : HasGrowth (fun x : E => M+L x) := (HasGrowth.const M).add (HasGrowth.linear L)
  obtain ⟨A,hA0,k,hk⟩ := (HasGrowth.const C).mul
    ((HasGrowth.const (1:ℝ)).add (hA.norm.pow n))
  refine ⟨A,hA0,k,fun x => (hf (M+L x)).trans ?_⟩
  exact (le_abs_self _).trans (hk x)
end AcceleratedLogConcave.Tensor.PolynomialClosure
