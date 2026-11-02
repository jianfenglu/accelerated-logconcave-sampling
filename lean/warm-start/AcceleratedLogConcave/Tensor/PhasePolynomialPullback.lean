import AcceleratedLogConcave.Tensor.PolynomialClosure

/-! NEW reconstruction, not historical source recovery. Literal ordered
all-order derivatives and polynomial growth under a fixed continuous linear map.
The imported `partialAlong_map_id` already preserves direction labels in order;
no permutation, moment law, or target derivative bound is assumed here. -/
noncomputable section
open scoped ContDiff
namespace AcceleratedLogConcave.Tensor.PolynomialClosure
open AdjointReduction Conditional.Appell
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The actual Fréchet chain rule, evaluated on the same direction slot. -/
theorem dir_comp_linear {f : F → ℝ} (hf : ContDiff ℝ ∞ f)
    (L : E →L[ℝ] F) (v : E) :
    dir v (f ∘ L) = fun x => dir (L v) f (L x) := by
  funext x
  have hh := ((hf.differentiable (by simp) (L x)).hasFDerivAt).comp x L.hasFDerivAt
  change fderiv ℝ (f ∘ L) x v = fderiv ℝ f (L x) (L v)
  exact congrArg (fun A : E →L[ℝ] ℝ => A v) hh.fderiv

/-- Map each ordered derivative direction; the empty list is literal evaluation. -/
theorem partialAlong_comp_linear {f : F → ℝ} (hf : ContDiff ℝ ∞ f)
    (L : E →L[ℝ] F) (J : List E) :
    partialAlong id J (f ∘ L) = fun x => partialAlong id (J.map L) f (L x) := by
  induction J with
  | nil => rfl
  | cons v J ih =>
    simp only [partialAlong, List.map_cons, id_eq, ih]
    exact dir_comp_linear (contDiff_partialAlong id (J.map L) hf) L v

/-- Actual linear growth controls the composed polynomial jet, at every order. -/
theorem HasPolynomialJets.comp_linear {f : F → ℝ} (hf : HasPolynomialJets f)
    (hs : ContDiff ℝ ∞ f) (L : E →L[ℝ] F) : HasPolynomialJets (f ∘ L) := by
  intro J
  rw [partialAlong_comp_linear hs]
  obtain ⟨C, hC, n, hf⟩ := hf (J.map L)
  obtain ⟨A, hA0, k, hk⟩ := (HasGrowth.const C).mul
    ((HasGrowth.const (1 : ℝ)).add ((HasGrowth.linear L).norm.pow n))
  refine ⟨A, hA0, k, fun x => (hf (L x)).trans ?_⟩
  exact (le_abs_self _).trans (hk x)
end AcceleratedLogConcave.Tensor.PolynomialClosure
