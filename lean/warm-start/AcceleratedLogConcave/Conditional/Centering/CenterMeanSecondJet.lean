import AcceleratedLogConcave.Conditional.Centering.SourceObservableJets

/-! Literal finite-order centering observable chain rule. This module does not
assert an L² interchange or substitute a derivative norm for its moment bound. -/
noncomputable section
namespace AcceleratedLogConcave.Conditional.Centering
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The first source mean jet, written with the actual spatial derivatives. -/
def meanFirstJet (K : E → E →L[ℝ] E) (M : E → E) (s : ℝ) (y g : E) : E :=
  (-s⁻¹) • (fderiv ℝ M y (K y g))

/-- The second jet retains the derivative of both K and the Gaussian momentum. -/
def meanSecondJet (K : E → E →L[ℝ] E) (M : E → E) (u : E)
    (s : ℝ) (y g : E) : E :=
  (s⁻¹)^2 • ((fderiv ℝ (fderiv ℝ M) y (K y g)) (K y g) +
    fderiv ℝ M y ((fderiv ℝ K y (K y g)) g) -
    fderiv ℝ M y (K y (M y - u)))

/-- A literal derivative identity; all differentiability premises are spatial,
so actual smooth source data can discharge them independently of L² bounds. -/
theorem hasDerivAt_meanFirstJet_along
    {K : E → E →L[ℝ] E} {M : E → E} {u : E} {s t : ℝ}
    {y g : ℝ → E}
    (hK : DifferentiableAt ℝ K (y t))
    (hM : DifferentiableAt ℝ (fderiv ℝ M) (y t))
    (hy : HasDerivAt y ((-s⁻¹) • (K (y t) (g t))) t)
    (hg : HasDerivAt g (s⁻¹ • (M (y t) - u)) t) :
    HasDerivAt (fun a => meanFirstJet K M s (y a) (g a))
      (meanSecondJet K M u s (y t) (g t)) t := by
  have hDM := hM.hasFDerivAt.comp_hasDerivAt t hy
  have hKt := hK.hasFDerivAt.comp_hasDerivAt t hy
  have h := (hDM.clm_apply (hKt.clm_apply hg)).const_smul (-s⁻¹)
  convert h using 1
  · rfl
  · dsimp [meanSecondJet]
    simp only [map_smul, map_add, smul_apply, smul_add, smul_smul]
    module

end AcceleratedLogConcave.Conditional.Centering
