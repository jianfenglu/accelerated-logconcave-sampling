import AcceleratedLogConcave.Oracle.TapeLowering
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-! Actual measurable spaces and independent draw laws on the compiler's structural tapes.
The product laws here define the independent-instruction sampling semantics. Identifying a
particular recursively compiled producer with these laws is a separate consumer obligation.
Uniform instructions keep their actual closed-unit-interval values, including endpoints. -/

noncomputable section
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Probability.MixedResidualTape
open Oracle Oracle.TapeLowering

instance instrResidualMeasurableSpace (i : Instr c Γ τ) :
    MeasurableSpace (InstrResidualTape i) := by
  cases i <;> dsimp [InstrResidualTape] <;> infer_instance

instance residualMeasurableSpace (p : Prog c Γ τ) : MeasurableSpace (ResidualTape p) :=
  match p with
  | .ret _ => inferInstanceAs (MeasurableSpace PUnit)
  | .step _ i next => by
      letI := instrResidualMeasurableSpace i
      letI := residualMeasurableSpace next
      exact inferInstanceAs (MeasurableSpace (InstrResidualTape i × ResidualTape next))
  | .batch _ children next => by
      letI := fun j => residualMeasurableSpace (children j)
      letI := residualMeasurableSpace next
      exact inferInstanceAs (MeasurableSpace ((∀ j, ResidualTape (children j)) × ResidualTape next))

instance instrTapeMeasurableSpace (d : ℕ) (i : Instr c Γ τ) :
    MeasurableSpace (i.Tape d) := by
  cases i <;> dsimp [Instr.Tape] <;> infer_instance

instance tapeMeasurableSpace (d : ℕ) (p : Prog c Γ τ) : MeasurableSpace (Tape d p) :=
  match p with
  | .ret _ => inferInstanceAs (MeasurableSpace PUnit)
  | .step _ i next => by
      letI := instrTapeMeasurableSpace d i
      letI := tapeMeasurableSpace d next
      exact inferInstanceAs (MeasurableSpace (i.Tape d × Tape d next))
  | .batch _ children next => by
      letI := fun j => tapeMeasurableSpace d (children j)
      letI := tapeMeasurableSpace d next
      exact inferInstanceAs (MeasurableSpace ((∀ j, Tape d (children j)) × Tape d next))

/-- The genuine uniform law on the compiler's `UniformValue` subtype. -/
def uniformLaw : Measure UniformValue := volume

instance : IsProbabilityMeasure uniformLaw := by
  unfold uniformLaw
  infer_instance

/-- Unit leaves are deterministic; uniform leaves use the actual uniform instruction law. -/
def instrResidualLaw (i : Instr c Γ τ) : Measure (InstrResidualTape i) :=
  match i with
  | .uniform => uniformLaw
  | .pure _ | .center | .momentum | .grad _ | .gaussian => Measure.dirac PUnit.unit

instance instrResidualLaw_probability (i : Instr c Γ τ) :
    IsProbabilityMeasure (instrResidualLaw i) := by
  cases i with
  | uniform => exact inferInstanceAs (IsProbabilityMeasure uniformLaw)
  | _ => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac PUnit.unit))

/-- Every residual coordinate is present; repeated equal-code children have separate factors. -/
def residualLaw (p : Prog c Γ τ) : Measure (ResidualTape p) :=
  match p with
  | .ret _ => Measure.dirac PUnit.unit
  | .step _ i next => (instrResidualLaw i).prod (residualLaw next)
  | .batch _ children next =>
      (Measure.pi (fun j => residualLaw (children j))).prod (residualLaw next)

instance residualLaw_probability (p : Prog c Γ τ) : IsProbabilityMeasure (residualLaw p) := by
  induction p with
  | ret _ => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac PUnit.unit))
  | step _ i next ih =>
      have := ih
      change IsProbabilityMeasure ((instrResidualLaw i).prod (residualLaw next))
      infer_instance
  | batch _ children next ihc ihn =>
      have := ihc
      have := ihn
      change IsProbabilityMeasure ((Measure.pi (fun j => residualLaw (children j))).prod
        (residualLaw next))
      infer_instance

/-- Original-gradient instructions are deterministic, Gaussian and uniform instructions are draws. -/
def instrLaw (d : ℕ) (i : Instr c Γ τ) : Measure (i.Tape d) :=
  match i with
  | .gaussian => stdGaussian (Point d)
  | .uniform => uniformLaw
  | .pure _ | .center | .momentum | .grad _ => Measure.dirac PUnit.unit

instance instrLaw_probability (d : ℕ) (i : Instr c Γ τ) :
    IsProbabilityMeasure (instrLaw d i) := by
  cases i with
  | gaussian => exact inferInstanceAs (IsProbabilityMeasure (stdGaussian (Point d)))
  | uniform => exact inferInstanceAs (IsProbabilityMeasure uniformLaw)
  | _ => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac PUnit.unit))

/-- The literal independent-instruction law on the exact raw execution tape. -/
def tapeLaw (d : ℕ) (p : Prog c Γ τ) : Measure (Tape d p) :=
  match p with
  | .ret _ => Measure.dirac PUnit.unit
  | .step _ i next => (instrLaw d i).prod (tapeLaw d next)
  | .batch _ children next =>
      (Measure.pi (fun j => tapeLaw d (children j))).prod (tapeLaw d next)

instance tapeLaw_probability (d : ℕ) (p : Prog c Γ τ) :
    IsProbabilityMeasure (tapeLaw d p) := by
  induction p with
  | ret _ => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac PUnit.unit))
  | step _ i next ih =>
      have := ih
      change IsProbabilityMeasure ((instrLaw d i).prod (tapeLaw d next))
      infer_instance
  | batch _ children next ihc ihn =>
      have := ihc
      have := ihn
      change IsProbabilityMeasure ((Measure.pi (fun j => tapeLaw d (children j))).prod
        (tapeLaw d next))
      infer_instance

/-- Measurability of the actual Gaussian/residual reconstruction, without replacing residuals. -/
theorem measurable_joinTape (d : ℕ) (p : Prog c Γ τ) :
    Measurable (fun zr : (GaussianSlot p → Point d) × ResidualTape p =>
      joinTape p zr.1 zr.2) := by
  induction p with
  | ret _ => exact measurable_const
  | step origin i next ih =>
      change Measurable (fun zr => (_, _))
      apply Measurable.prodMk
      · cases i with
        | gaussian =>
            change Measurable (fun zr : (GaussianSlot (.step origin .gaussian next) → Point d) × ResidualTape (.step origin .gaussian next) => zr.1 (Sum.inl PUnit.unit))
            fun_prop
        | uniform =>
            change Measurable (fun zr : (GaussianSlot (.step origin .uniform next) → Point d) × ResidualTape (.step origin .uniform next) => zr.2.1)
            fun_prop
        | _ => exact measurable_const
      · exact ih.comp (show Measurable (fun zr :
          (GaussianSlot (.step origin i next) → Point d) × ResidualTape (.step origin i next) =>
            ((fun s => zr.1 (Sum.inr s)), zr.2.2)) from by fun_prop)
  | batch origin children next ihc ihn =>
      change Measurable (fun zr => (_, _))
      apply Measurable.prodMk
      · apply Measurable.of_eval
        intro j
        exact (ihc j).comp (show Measurable (fun zr :
          (GaussianSlot (.batch origin children next) → Point d) ×
            ResidualTape (.batch origin children next) =>
              ((fun s => zr.1 (Sum.inl ⟨j,s⟩)), zr.2.1 j)) from by fun_prop)
      · exact ihn.comp (show Measurable (fun zr :
          (GaussianSlot (.batch origin children next) → Point d) ×
            ResidualTape (.batch origin children next) =>
              ((fun s => zr.1 (Sum.inr s)), zr.2.2)) from by fun_prop)

/-- The literal extraction is measurable for all Gaussian, uniform, and unit leaves. -/
theorem measurable_splitTape (d : ℕ) (p : Prog c Γ τ) :
    Measurable (splitTape (d := d) p) := by
  induction p with
  | ret _ => exact measurable_const
  | step origin i next ih =>
      apply Measurable.prodMk
      · apply Measurable.of_eval
        intro s
        cases s with
        | inl s =>
            cases i with
            | gaussian =>
                change Measurable (fun w : Tape d (.step origin .gaussian next) => w.1)
                exact measurable_fst
            | _ => cases s
        | inr s =>
            exact (measurable_pi_apply s).comp (measurable_fst.comp
              (ih.comp measurable_snd))
      · apply Measurable.prodMk
        · cases i with
          | uniform =>
              change Measurable (fun w : Tape d (.step origin .uniform next) => w.1)
              exact measurable_fst
          | _ => exact measurable_const
        · exact measurable_snd.comp (ih.comp measurable_snd)
  | batch origin children next ihc ihn =>
      apply Measurable.prodMk
      · apply Measurable.of_eval
        intro s
        cases s with
        | inl s =>
            exact (measurable_pi_apply s.2).comp (measurable_fst.comp
              ((ihc s.1).comp ((measurable_pi_apply s.1).comp measurable_fst)))
        | inr s =>
            exact (measurable_pi_apply s).comp (measurable_fst.comp
              (ihn.comp measurable_snd))
      · apply Measurable.prodMk
        · apply Measurable.of_eval
          intro j
          exact measurable_snd.comp ((ihc j).comp
            ((measurable_pi_apply j).comp measurable_fst))
        · exact measurable_snd.comp (ihn.comp measurable_snd)

/-- The existing complete tape equivalence, now with its actual measurable structures. -/
def splitGaussianMeasurableEquiv (d : ℕ) (p : Prog c Γ τ) :
    Tape d p ≃ᵐ ((GaussianSlot p → Point d) × ResidualTape p) where
  toEquiv := splitGaussianTape d p
  measurable_toFun := measurable_splitTape d p
  measurable_invFun := measurable_joinTape d p

end AcceleratedLogConcave.Probability.MixedResidualTape
