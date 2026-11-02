import AcceleratedLogConcave.Conditional.MeanReferenceVariance

noncomputable section
open MeasureTheory ProbabilityTheory AcceleratedLogConcave
open Numerics Numerics.MeanFlowLp Conditional Conditional.MeanReferenceLayer
open scoped RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace AcceleratedLogConcave.Conditional.MeanReferenceVariance
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
local notation "E" => EuclideanSpace ℝ ι

theorem splitExecution_preserving (d : Data ι m) (c : Children d) :
    MeasurePreserving (fun z : Execution ι m => (splitState d c z.1,z.2))
      (averagedJoint d c)
      (((MeanReferenceLayer.baseLaw d).prod (Measure.pi (fun _ : Fin m => stdGaussian E))) ⊗ₘ stateChildren d c) := by
  refine ⟨((measurable_splitState d c).comp measurable_fst).prodMk measurable_snd, ?_⟩
  have hp := compProd_comap_push ((stdGaussian E).prod (freshLaw d))
    (stateChildren d c) (splitState d c) (measurable_splitState d c)
  rwa [← children_eq_state_comap,← averagedJoint_eq,splitState_law] at hp

theorem returned_memLp (d : Data ι m) (c : Children d) (i : Fin m) :
    MemLp (fun z : Execution ι m => z.2 i) 2 (averagedJoint d c) := by
  exact IsGaussian.memLp_two_id.comp_measurePreserving
    ((measurePreserving_eval (fun _ : Option (Option (Fin m)) => stdGaussian E)
      (some (some i))).comp (outputCoordinates_preserving d c))

theorem active_memLp (d : Data ι m) (c : Children d) (i : Fin m) :
    MemLp (fun z : Execution ι m => active d c z.1 (some i)) 2 (averagedJoint d c) :=
  IsGaussian.memLp_two_id.comp_measurePreserving (active_preserving d c (some i))

omit [DecidableEq ι] in
private theorem gaussian_coordinate_mean (v : E) (i : Fin m) :
    (∫ p : Fin m → E, ⟪v,p i⟫ ∂Measure.pi (fun _ : Fin m => stdGaussian E))=0 := by
  have h := measurePreserving_eval (fun _ : Fin m => stdGaussian E) i
  rw [← integral_map_of_stronglyMeasurable h.measurable (by fun_prop),h.map_eq]
  exact integral_strongDual_stdGaussian (innerSL ℝ v)

/-- A returned child momentum is orthogonal to another child's initial momentum. -/
theorem returned_active_cross (d : Data ι m) (c : Children d) (v : E)
    (i j : Fin m) (hij : i≠j) :
    (∫ z : Execution ι m,⟪v,z.2 i⟫ * ⟪v,active d c z.1 (some j)⟫ ∂averagedJoint d c)=0 := by
  let π := Measure.pi (fun _ : Fin m => stdGaussian E)
  let ν := (MeanReferenceLayer.baseLaw d).prod π
  let f : SplitState ι m × (Fin m → E) → ℝ :=
    fun z => ⟪v,z.2 i⟫ * ⟪v,z.1.2 j⟫
  have hf : StronglyMeasurable f := by dsimp [f]; fun_prop
  have hp := splitExecution_preserving d c
  have hint : Integrable f (ν ⊗ₘ stateChildren d c) := by
    apply (hp.integrable_comp hf.aestronglyMeasurable).mp
    exact ((returned_memLp d c i).const_inner (𝕜 := ℝ) v).integrable_mul
      ((active_memLp d c j).const_inner (𝕜 := ℝ) v)
  have hinter : Integrable
      (fun z : SplitState ι m => ∫ q, f (z,q) ∂stateChildren d c z) ν := by
    have h := hint.integral_compProd
    simpa only [Kernel.const_apply,Kernel.prodMkLeft_apply] using h
  change (∫ z, f (splitState d c z.1,z.2) ∂averagedJoint d c)=0
  rw [← integral_map_of_stronglyMeasurable hp.measurable hf,hp.map_eq]
  rw [Measure.integral_compProd hint,integral_prod _ hinter]
  apply integral_eq_zero_of_ae
  filter_upwards with b
  have he : ∀ p : Fin m → E,
      (∫ q,f ((b,p),q) ∂stateChildren d c (b,p))=
      (∫ x,⟪v,x⟫ ∂c.kernel i (stateCenter d i b,p i)) * ⟪v,p j⟫ := by
    intro p
    dsimp [f]
    rw [integral_mul_const,stateChildren_apply]
    let : ∀ k, IsProbabilityMeasure (c.kernel k (stateCenter d k b,p k)) :=
      fun k => by let := c.markov k; infer_instance
    have hh := measurePreserving_eval (fun k => c.kernel k (stateCenter d k b,p k)) i
    congr 1
    rw [← integral_map_of_stronglyMeasurable hh.measurable (by fun_prop),hh.map_eq]
  simp_rw [he]
  let a : E → ℝ := fun p => ∫ x,⟪v,x⟫ ∂c.kernel i (stateCenter d i b,p)
  have ha : StronglyMeasurable a := by
    have hh : StronglyMeasurable (fun z : E × E => ∫ x,⟪v,x⟫ ∂c.kernel i z) :=
      (show StronglyMeasurable (fun x : E => ⟪v,x⟫) by fun_prop).integral_kernel
    exact hh.comp_measurable measurable_prodMk_left
  have hind := (iIndepFun_pi (μ := fun _ : Fin m => stdGaussian E)
    (X := fun _ (p : E) => p) (fun _ => measurable_id.aemeasurable)).indepFun hij
  have hscalar := hind.comp ha.measurable (by fun_prop : Measurable (fun p : E => ⟪v,p⟫))
  have hfactor := hscalar.integral_fun_mul_eq_mul_integral
    (ha.comp_measurable (measurable_pi_apply i)).aestronglyMeasurable
    (by fun_prop : StronglyMeasurable (fun p : Fin m → E => ⟪v,p j⟫)).aestronglyMeasurable
  simpa [Function.comp_def,gaussian_coordinate_mean,mul_zero,a,π] using hfactor


omit [DecidableEq ι] in
private theorem gaussian_pair_cross {J : Type*} [Fintype J] (v : E) (i j : J) (hij : i≠j) :
    (∫ p : J → E,⟪v,p i⟫ * ⟪v,p j⟫ ∂Measure.pi (fun _ : J => stdGaussian E))=0 := by
  have hi := iIndepFun_pi (μ := fun _ : J => stdGaussian E)
    (X := fun _ (p : E) => ⟪v,p⟫) (fun _ => by fun_prop)
  rw [(hi.indepFun hij).integral_fun_mul_eq_mul_integral
    (by fun_prop : StronglyMeasurable (fun p : J → E => ⟪v,p i⟫)).aestronglyMeasurable
    (by fun_prop : StronglyMeasurable (fun p : J → E => ⟪v,p j⟫)).aestronglyMeasurable]
  have h := measurePreserving_eval (fun _ : J => stdGaussian E) j
  have hz : (∫ p : J → E,⟪v,p j⟫ ∂Measure.pi (fun _ : J => stdGaussian E))=0 := by
    rw [← integral_map_of_stronglyMeasurable h.measurable (by fun_prop),h.map_eq]
    exact integral_strongDual_stdGaussian (innerSL ℝ v)
  rw [hz,mul_zero]

omit [DecidableEq ι] in
private theorem gaussian_pair_cross_comp {Ω J : Type*} [MeasurableSpace Ω] [Fintype J]
    {μ : Measure Ω} {g : Ω → J → E}
    (hg : MeasurePreserving g μ (Measure.pi (fun _ : J => stdGaussian E)))
    (v : E) (i j : J) (hij : i≠j) :
    (∫ z,⟪v,g z i⟫ * ⟪v,g z j⟫ ∂μ)=0 := by
  have hm : StronglyMeasurable (fun p : J → E => ⟪v,p i⟫ * ⟪v,p j⟫) := by fun_prop
  rw [← integral_map_of_stronglyMeasurable hg.measurable hm,hg.map_eq]
  exact gaussian_pair_cross v i j hij

theorem activeCoordinates_preserving (d : Data ι m) (c : Children d) :
    MeasurePreserving (fun z : Execution ι m => fun i => active d c z.1 (some i))
      (averagedJoint d c) (Measure.pi (fun _ : Fin m => stdGaussian E)) := by
  have hs : MeasurePreserving (splitState d c) ((stdGaussian E).prod (freshLaw d))
      ((MeanReferenceLayer.baseLaw d).prod (Measure.pi (fun _ : Fin m => stdGaussian E))) :=
    ⟨measurable_splitState d c,splitState_law d c⟩
  exact measurePreserving_snd.comp (hs.comp (host_preserving d c))

theorem child_child_cross (d : Data ι m) (c : Children d) (v : E)
    (i j : Fin m) (hij : i≠j) :
    (∫ z,⟪v,childIncrement d c i z⟫ * ⟪v,childIncrement d c j z⟫ ∂averagedJoint d c)=0 := by
  have hqq : (∫ z : Execution ι m,⟪v,z.2 i⟫ * ⟪v,z.2 j⟫ ∂averagedJoint d c)=0 :=
    gaussian_pair_cross_comp (outputCoordinates_preserving d c) v
      (some (some i)) (some (some j)) (by simpa using hij)
  have hpp := gaussian_pair_cross_comp (activeCoordinates_preserving d c) v i j hij
  have hqp := returned_active_cross d c v i j hij
  have hpq : (∫ z : Execution ι m,⟪v,active d c z.1 (some i)⟫ * ⟪v,z.2 j⟫
      ∂averagedJoint d c)=0 := by
    simpa only [mul_comm] using returned_active_cross d c v j i hij.symm
  have hqi := (returned_memLp d c i).const_inner (𝕜 := ℝ) v
  have hqj := (returned_memLp d c j).const_inner (𝕜 := ℝ) v
  have hpi := (active_memLp d c i).const_inner (𝕜 := ℝ) v
  have hpj := (active_memLp d c j).const_inner (𝕜 := ℝ) v
  simp only [childIncrement,inner_sub_right,sub_mul,mul_sub]
  have h1 := integral_sub ((hqi.integrable_mul hqj).sub (hpi.integrable_mul hqj))
    ((hqi.integrable_mul hpj).sub (hpi.integrable_mul hpj))
  have h2 := integral_sub (hqi.integrable_mul hqj) (hpi.integrable_mul hqj)
  have h3 := integral_sub (hqi.integrable_mul hpj) (hpi.integrable_mul hpj)
  simp only [Pi.sub_apply,Pi.mul_apply] at h1 h2 h3
  rw [h1,h2,h3,hqq,hpp,hqp,hpq]
  norm_num

end AcceleratedLogConcave.Conditional.MeanReferenceVariance
