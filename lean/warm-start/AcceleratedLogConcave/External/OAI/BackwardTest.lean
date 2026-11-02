import AcceleratedLogConcave.External.OAI.SpaceTimeForward
import AcceleratedLogConcave.External.OAI.FDerivTimePartial

/-! Adapted from openai/math, revision 1581d4cbdd69a0faf34b2089614fe2a814316a6a,
lean/OAI/Probability/LogConcave/Dynamics/TriangularEquiv.lean. Apache-2.0; see LICENSE and PROVENANCE.json. -/

namespace OAI

section
section
noncomputable section
open Filter
open scoped ENNReal NNReal Topology

section UpperProof
open Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling.GlobalODE
open Set Function Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def triangularEquiv (v : E) (J : E ≃L[ℝ] E) : (ℝ × E) ≃L[ℝ] (ℝ × E) where
  toLinearEquiv :=
    { toFun := fun p => (p.1,p.1 •v+J p.2)
      invFun := fun p => (p.1,J.symm (p.2-p.1 •v))
      left_inv := fun p => by simp
      right_inv := fun p => by simp
      map_add' := fun p q => by simp [add_smul]; abel
      map_smul' := fun c p => by simp [smul_add,smul_smul] }
  continuous_toFun := continuous_fst.prodMk
    ((continuous_fst.smul continuous_const).add (J.continuous.comp continuous_snd))
  continuous_invFun := continuous_fst.prodMk
    (J.symm.continuous.comp (continuous_snd.sub (continuous_fst.smul continuous_const)))

variable [CompleteSpace E] [ProperSpace E]
    {a b : ℝ} (hab : a≤b) {f : ℝ → E → E} (hc : Continuous (uncurry f))
    {K : ℝ≥0} (hL : ∀ t∈Icc a b,LipschitzWith K (f t))
    {D : ℝ → E → E →L[ℝ] E} (hD : Continuous (uncurry D))
    (hf : ∀ t z,HasFDerivAt (f t) (D t z) z)

omit [ProperSpace E] in
lemma spaceTimeForward_time_deriv (p : ℝ × E) (hp : p.1∈Ioo a b) :
    HasDerivAt (fun t => (spaceTimeForward hab hc hL (t,p.2)).2)
      (f p.1 (spaceTimeForward hab hc hL p).2) p.1 := by
  have hpi : p.1∈Icc a b := ⟨hp.1.le,hp.2.le⟩
  have hh := (flow_deriv hL hc ⟨a,le_rfl,hab⟩ p.2 p.1 hpi).hasDerivAt
    (Icc_mem_nhds hp.1 hp.2)
  have he : (spaceTimeForward hab hc hL p).2=flow hL hc ⟨a,le_rfl,hab⟩ p.2 p.1 := by
    simp [spaceTimeForward,projIcc_of_mem _ hpi]
  rw [he]
  apply hh.congr_of_eventuallyEq
  filter_upwards [Icc_mem_nhds hp.1 hp.2] with t ht
  simp [spaceTimeForward,projIcc_of_mem _ ht]

theorem spaceTimeForward_hasFDerivAt (p : ℝ × E) (hp : p.1∈Ioo a b) :
    HasFDerivAt (spaceTimeForward hab hc hL)
      (triangularEquiv (f p.1 (spaceTimeForward hab hc hL p).2)
        (fundamentalEquiv (flowSpatialCoefficient_continuous hab hc hL hD p.2)
          (flowSpatialCoefficient_bound hab hc hL hf p.2) ⟨a,le_rfl,hab⟩
            ⟨p.1,hp.1.le,hp.2.le⟩) : (ℝ × E) →L[ℝ] (ℝ × E)) p := by
  let J := flowLinearization hab hc hL hD hf p.2 p.1
  have hsp : HasFDerivAt (fun z => (spaceTimeForward hab hc hL (p.1,z)).2) J p.2 := by
    simpa [spaceTimeForward,projIcc_of_mem _ ⟨hp.1.le,hp.2.le⟩] using
      flow_hasFDerivAt_left hab hc hL hD hf p.2 ⟨p.1,hp.1.le,hp.2.le⟩
  have hg : Continuous (fun q : ℝ × E => f q.1 (spaceTimeForward hab hc hL q).2) :=
    hc.comp (continuous_fst.prodMk (spaceTimeForward_continuous hab hc hL).snd)
  have hh := LogConcaveSampling.hasFDerivAt_of_time_partial
    (f:=fun t z => (spaceTimeForward hab hc hL (t,z)).2)
    (g:=fun t z => f t (spaceTimeForward hab hc hL (t,z)).2)
    (isOpen_Ioo.prod isOpen_univ) (show p∈Ioo a b ×ˢ (univ:Set E) from ⟨hp,mem_univ _⟩)
    hg.continuousAt (fun q hq => spaceTimeForward_time_deriv hab hc hL q hq.1) hsp
  convert! hasFDerivAt_fst.prodMk hh using 1

include hD hf in

theorem spaceTimeBackward_differentiableAt (p : ℝ × E) (hp : p.1∈Ioo a b) :
    DifferentiableAt ℝ (spaceTimeBackward hab hc hL) p := by
  have hh := spaceTimeForward_hasFDerivAt hab hc hL hD hf
    (spaceTimeBackward hab hc hL p) hp
  exact (hh.of_local_left_inverse (spaceTimeBackward_continuous hab hc hL).continuousAt
    (Filter.Eventually.of_forall (spaceTime_right_inverse hab hc hL))).differentiableAt
end LogConcaveSampling.GlobalODE
namespace LogConcaveSampling.GlobalODE
open Set Function Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {a b : ℝ} (hab : a≤b) {f : ℝ → E → E} (hc : Continuous (uncurry f))
    {K : ℝ≥0} (hL : ∀ t∈Icc a b,LipschitzWith K (f t))

def backwardTest (T : Icc a b) (φ : E → ℝ) (p : ℝ × E) : ℝ :=
  φ (flow hL hc ⟨a,le_rfl,hab⟩ (spaceTimeBackward hab hc hL p).2 T)

lemma backwardTest_eq (T : Icc a b) (φ : E → ℝ) (p : ℝ × E) :
    backwardTest hab hc hL T φ p=φ (flow hL hc (projIcc a b hab p.1) p.2 T) := by
  unfold backwardTest spaceTimeBackward
  rw [flow_cocycle hL hc (projIcc a b hab p.1) ⟨a,le_rfl,hab⟩ T]

lemma backwardTest_continuous (T : Icc a b) {φ : E → ℝ} (hφ : Continuous φ) :
    Continuous (backwardTest hab hc hL T φ) :=
  hφ.comp ((flow_lipschitz hL hc ⟨a,le_rfl,hab⟩ T).continuous.comp
    (spaceTimeBackward_continuous hab hc hL).snd)

lemma backwardTest_lipschitz (T : Icc a b) {φ : E → ℝ} {L : ℝ≥0}
    (hφ : LipschitzWith L φ) (t : ℝ) :
    LipschitzWith (L*⟨Real.exp ((K:ℝ)*(b-a)),(Real.exp_pos _).le⟩)
      (fun z => backwardTest hab hc hL T φ (t,z)) := by
  simp only [backwardTest_eq]
  apply hφ.comp
  apply (flow_lipschitz hL hc (projIcc a b hab t) T).weaken
  change Real.exp _≤Real.exp _
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ K.coe_nonneg
  rw [abs_le]
  constructor <;> linarith [T.2.1,T.2.2,(projIcc a b hab t).2.1,(projIcc a b hab t).2.2]

variable [ProperSpace E] {D : ℝ → E → E →L[ℝ] E} (hD : Continuous (uncurry D))
    (hf : ∀ t z,HasFDerivAt (f t) (D t z) z)

include hD hf in
lemma backwardTest_differentiableAt (T : Icc a b) {φ : E → ℝ}
    (hφ : Differentiable ℝ φ) (p : ℝ × E) (hp : p.1∈Ioo a b) :
    DifferentiableAt ℝ (backwardTest hab hc hL T φ) p :=
  (hφ _).comp p (((flow_contDiff_one_left hab hc hL hD hf T).differentiable (by norm_num) _).comp p
    (spaceTimeBackward_differentiableAt hab hc hL hD hf p hp).snd)

include hD hf in

theorem backwardTest_material_zero (T : Icc a b) {φ : E → ℝ}
    (hφ : Differentiable ℝ φ) (p : ℝ × E) (hp : p.1∈Ioo a b) :
    fderiv ℝ (backwardTest hab hc hL T φ) p (1,f p.1 p.2)=0 := by
  let B := spaceTimeBackward hab hc hL
  let G := fun z => φ (flow hL hc ⟨a,le_rfl,hab⟩ z T)
  have hG : Differentiable ℝ G := hφ.comp
    ((flow_contDiff_one_left hab hc hL hD hf T).differentiable (by norm_num))
  have hv : f (B p).1 (spaceTimeForward hab hc hL (B p)).2=f p.1 p.2 := by
    rw [spaceTime_right_inverse hab hc hL p]
    rfl
  have hB := (spaceTimeForward_hasFDerivAt hab hc hL hD hf (B p) hp).of_local_left_inverse
    (spaceTimeBackward_continuous hab hc hL).continuousAt
    (Filter.Eventually.of_forall (spaceTime_right_inverse hab hc hL))
  have hcomp := (hG (B p).2).hasFDerivAt.comp p hB.snd
  change (fderiv ℝ (G ∘ fun x => (spaceTimeBackward hab hc hL x).2) p) (1,f p.1 p.2)=0
  rw [hcomp.fderiv]
  change (fderiv ℝ G (B p).2) _=0
  have he : (((triangularEquiv (f (B p).1 (spaceTimeForward hab hc hL (B p)).2)
      (fundamentalEquiv (flowSpatialCoefficient_continuous hab hc hL hD (B p).2)
        (flowSpatialCoefficient_bound hab hc hL hf (B p).2) ⟨a,le_rfl,hab⟩
          ⟨(B p).1,hp.1.le,hp.2.le⟩)).symm : (ℝ × E) →L[ℝ] (ℝ × E)) (1,f p.1 p.2)).2=0 := by
    change (fundamentalEquiv _ _ _ _).symm (f p.1 p.2-1 • _)=0
    rw [hv,one_smul,sub_self,map_zero]
  convert! (congrArg (fderiv ℝ G (B p).2) he).trans (map_zero _) using 1
end LogConcaveSampling.GlobalODE

end UpperProof
end
end
end
end OAI
