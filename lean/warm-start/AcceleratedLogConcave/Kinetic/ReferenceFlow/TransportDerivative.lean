import AcceleratedLogConcave.External.OAI.BackwardTest

/-! Differentiating actual backward-transported tests along a different frame.
The full drift cancels by the proved flow equation, leaving the drift difference. -/
noncomputable section
open Set Function
open scoped NNReal
open OAI.LogConcaveSampling.GlobalODE
namespace AcceleratedLogConcave.Kinetic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [ProperSpace E]
  {a b : ℝ} (hab : a ≤ b) {v : ℝ → E → E} (hv : Continuous (uncurry v))
  {K : ℝ≥0} (hL : ∀ t ∈ Icc a b, LipschitzWith K (v t))
  {D : ℝ → E → E →L[ℝ] E} (hD : Continuous (uncurry D))
  (hd : ∀ t x, HasFDerivAt (v t) (D t x) x)

include hD hd in
/-- The derivative is the spatial test derivative against the difference
between the chosen reference-frame velocity and the actual full drift. -/
theorem backwardTest_along_hasDerivAt (T : Icc a b) {φ : E → ℝ}
    (hφ : Differentiable ℝ φ) (z : ℝ → E) (t : ℝ) (ht : t ∈ Ioo a b)
    (w : E) (hz : HasDerivAt z w t) :
    HasDerivAt (fun u => backwardTest hab hv hL T φ (u, z u))
      (fderiv ℝ (fun x => backwardTest hab hv hL T φ (t,x)) (z t) (w-v t (z t))) t := by
  let B := backwardTest hab hv hL T φ
  have hB : DifferentiableAt ℝ B (t,z t) :=
    backwardTest_differentiableAt hab hv hL hD hd T hφ (t,z t) ht
  have hc := hB.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).prodMk hz)
  have hzero : fderiv ℝ B (t,z t) (1,v t (z t)) = 0 :=
    backwardTest_material_zero hab hv hL hD hd T hφ (t,z t) ht
  have hslice := hB.hasFDerivAt.comp (z t)
    ((hasFDerivAt_const t (z t)).prodMk (hasFDerivAt_id (𝕜 := ℝ) (z t)))
  have he : fderiv ℝ B (t,z t) (1,w) =
      fderiv ℝ (fun x => B (t,x)) (z t) (w-v t (z t)) := by
    change fderiv ℝ B (t,z t) (1,w) = fderiv ℝ (B ∘ Prod.mk t) (z t) (w-v t (z t))
    rw [hslice.fderiv]
    change fderiv ℝ B (t,z t) (1,w) = fderiv ℝ B (t,z t) (0,w-v t (z t))
    have hp : ((0 : ℝ),w-v t (z t)) = (1,w) - (1,v t (z t)) := by ext <;> simp
    rw [hp, map_sub, hzero, sub_zero]
  exact he ▸ hc

end AcceleratedLogConcave.Kinetic
