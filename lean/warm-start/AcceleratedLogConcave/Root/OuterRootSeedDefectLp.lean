import AcceleratedLogConcave.Root.ClockQuadraturePower
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped BigOperators
namespace AcceleratedLogConcave.Root.OuterRootSeedDefectLp
open Analysis.Poisson Numerics Numerics.ConditionalSmoothing
open OuterRootStrongJetLp
variable {ι : Type*} [Fintype ι] {a b : ℝ}
variable (F : ReferencePoissonFamily (EuclideanSpace ℝ ι) a b)
  (d : SamplingCenterLp.Data ι) (c : ℝ)

/-- Existing main's endpoint defect, with the identical node/weight row. -/
def endpointDefect (J m : ℕ) (rho : ClockSchedule.Clock) :=
  (jetLp F d c 0 rho - jetLp F d c 0 0) -
    ∑ i, ClockSchedule.weight J m rho i •
      jetLp F d c 1 (ClockSchedule.nodeValue J m rho i)

private theorem finite_toLp {Ω X I : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup X] [Fintype I] (mu : Measure Ω)
    (f : I → Ω → X) (hf : ∀ i, MemLp (f i) 2 mu) :
    (memLp_finsetSum' Finset.univ (fun i _ => hf i)).toLp
      (∑ i, f i) = ∑ i, (hf i).toLp (f i) := by
  classical
  have H (s : Finset I) :
      (memLp_finsetSum' s (fun i _ => hf i)).toLp (∑ i ∈ s, f i) =
        ∑ i ∈ s, (hf i).toLp (f i) := by
    induction s using Finset.induction_on with
    | empty => simp only [Finset.sum_empty]; exact MemLp.toLp_zero _
    | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      change ((hf i).add (memLp_finsetSum' s (fun j _ => hf j))).toLp
        (f i + ∑ j ∈ s, f j) = _
      rw [MemLp.toLp_add (hf i) (memLp_finsetSum' s (fun j _ => hf j)),ih]
  exact H Finset.univ

def seedDefect (J m : ℕ) (rho : ClockSchedule.Clock) (s : ℝ)
    (p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  s • seedJet d c 0 0 p +
    s • (∑ i, ClockSchedule.weight J m rho i •
      seedJet d c 1 (ClockSchedule.nodeValue J m rho i) p) -
    s • seedJet d c 0 rho p

private theorem seedDefect_eq_function (J m : ℕ) (rho : ClockSchedule.Clock) (s : ℝ) :
    seedDefect d c J m rho s =
      s • seedJet d c 0 0 + s • (∑ i, ClockSchedule.weight J m rho i •
        seedJet d c 1 (ClockSchedule.nodeValue J m rho i)) - s • seedJet d c 0 rho := by
  funext p
  simp only [seedDefect, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Finset.sum_apply]

theorem seedDefect_memLp (J m : ℕ) (rho : ClockSchedule.Clock) (s : ℝ) :
    MemLp (seedDefect d c J m rho s) 2 (seedMeasure F) := by
  rw [seedDefect_eq_function]
  exact (((seedJet_memLp F d c 0 0).const_smul s).add
    ((memLp_finsetSum' Finset.univ (fun i _ =>
      (seedJet_memLp F d c 1 (ClockSchedule.nodeValue J m rho i)).const_smul
        (ClockSchedule.weight J m rho i))).const_smul s)).sub
    ((seedJet_memLp F d c 0 rho).const_smul s)

theorem seedDefect_toLp (J m : ℕ) (rho : ClockSchedule.Clock)
    (s : ℝ) :
    (seedDefect_memLp F d c J m rho s).toLp (seedDefect d c J m rho s) =
      -s • endpointDefect F d c J m rho := by
  have hrow (i : Fin (J*m)) :=
    (seedJet_memLp F d c 1 (ClockSchedule.nodeValue J m rho i)).const_smul
      (ClockSchedule.weight J m rho i)
  have hsum := memLp_finsetSum' Finset.univ (fun i _ => hrow i)
  have hstart := (seedJet_memLp F d c 0 0).const_smul s
  have hend := (seedJet_memLp F d c 0 rho).const_smul s
  simp only [seedDefect_eq_function]
  rw [MemLp.toLp_sub (hstart.add (hsum.const_smul s)) hend,
    MemLp.toLp_add hstart (hsum.const_smul s),
    MemLp.toLp_const_smul s (seedJet_memLp F d c 0 0),
    MemLp.toLp_const_smul s hsum,
    MemLp.toLp_const_smul s (seedJet_memLp F d c 0 rho),
    finite_toLp _ _ hrow]
  change s • jetLp F d c 0 0 + s • (∑ i, ClockSchedule.weight J m rho i •
    jetLp F d c 1 (ClockSchedule.nodeValue J m rho i)) - s • jetLp F d c 0 rho = _
  simp only [endpointDefect, smul_sub, neg_smul]
  abel

/-- Genuine square-integrability and exact L2 norm identity for the random
common-seed defect. This bridges Banach GL bounds to the RMS receiver. -/
theorem seedDefect_energy (J m : ℕ) (rho : ClockSchedule.Clock)
    (s : ℝ) :
    Integrable (fun p => ‖seedDefect d c J m rho s p‖^2) (seedMeasure F) ∧
    (∫ p, ‖seedDefect d c J m rho s p‖^2 ∂seedMeasure F) =
      s^2 * ‖endpointDefect F d c J m rho‖^2 := by
  refine ⟨(seedDefect_memLp F d c J m rho s).norm.integrable_sq,?_⟩
  rw [← Analysis.DominatedLp.norm_sq_toLp (seedDefect_memLp F d c J m rho s),
    seedDefect_toLp F d c J m rho s,norm_smul,mul_pow,Real.norm_eq_abs,abs_neg,sq_abs]

end AcceleratedLogConcave.Root.OuterRootSeedDefectLp
