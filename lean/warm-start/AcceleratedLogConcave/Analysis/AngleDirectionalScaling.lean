import AcceleratedLogConcave.Tensor.AdjointReduction

/-! Ordered affine pullback bookkeeping for the angle's literal spatial jets. -/
noncomputable section
open scoped ContDiff
namespace AcceleratedLogConcave.Tensor.AdjointReduction
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem dir_const_mul (v : E) (c : ℝ) {f : E → ℝ} (hf : Differentiable ℝ f) :
    dir v (fun x => c * f x) = fun x => c * dir v f x := by
  funext x
  have h := (hf x).hasFDerivAt.const_mul c
  exact congrArg (fun A : E →L[ℝ] ℝ => A v) h.fderiv

theorem partialAlong_const_mul {I : Type*} (d : I → E) (J : List I) (c : ℝ)
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) :
    partialAlong d J (fun x => c * f x) = fun x => c * partialAlong d J f x := by
  induction J with
  | nil => rfl
  | cons i J ih =>
    simp only [partialAlong,ih]
    exact dir_const_mul _ _ ((contDiff_partialAlong d J hf).differentiable (by simp))

theorem partialAlong_scaled_directions {I : Type*} (d : I → E) (J : List I) (c : ℝ)
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) :
    partialAlong (fun i => c • d i) J f = fun x => c^J.length * partialAlong d J f x := by
  induction J with
  | nil => simp [partialAlong]
  | cons i J ih =>
    simp only [partialAlong,ih]
    rw [dir_const_mul _ _ ((contDiff_partialAlong d J hf).differentiable (by simp))]
    funext x
    simp only [dir,map_smul,smul_eq_mul,List.length_cons,pow_succ]
    ring

theorem partialAlong_zero_direction {I : Type*} (d : I → E) (J : List I)
    (f : E → ℝ) (hz : ∃ i ∈ J, d i = 0) : partialAlong d J f = fun _ => 0 := by
  induction J with
  | nil => simp at hz
  | cons i J ih =>
    obtain ⟨j,hj,hzero⟩ := hz
    rcases List.mem_cons.mp hj with rfl | hj
    · funext x
      change fderiv ℝ (partialAlong d J f) x (d j) = 0
      rw [hzero,map_zero]
    · rw [partialAlong,ih ⟨j,hj,hzero⟩]
      funext x
      change fderiv ℝ (fun _ : E => (0 : ℝ)) x (d i) = 0
      simp only [fderiv_const_apply,zero_apply]
end AcceleratedLogConcave.Tensor.AdjointReduction
