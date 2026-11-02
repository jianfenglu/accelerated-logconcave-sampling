import AcceleratedLogConcave.Oracle.SamplingCanonicalTapeMeasurability
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
Independent primitive product laws on the EXISTING finite tapes. The point
and interval measures are explicit inputs. In particular, naming an instruction
`gaussian` or `uniform` does NOT prove that its supplied measure is Gaussian or
uniform. No actual RNG, warm input, coupling, covariance, or accuracy claim.

Independence is a property of the product model DEFINED here, not a conclusion
about arbitrary tape-valued random variables. `splitLaw` is exact pushforward
through the existing split equivalence; it is NOT defined as a product and this
module does not claim its Gaussian-array/residual product factorization.

No evaluator/tape/split/join implementation is modified. No global instances.
-/
noncomputable section
namespace AcceleratedLogConcave.Oracle
namespace CanonicalTapeLaw
open MeasureTheory TapeLowering CanonicalTapeMeasurability
open scoped BigOperators

/-- A homogeneous normalized law for each primitive kind. Actual distribution
identification and any connection to an external source remain supplier work. -/
structure PrimitiveLaws (d : ℕ) where
  pointDraw : Measure (Point d)
  uniformDraw : Measure UniformValue
  point_probability : IsProbabilityMeasure pointDraw
  uniform_probability : IsProbabilityMeasure uniformDraw

/-- Pure, input and oracle instructions carry only their literal unit tape. -/
def instrLaw (L : PrimitiveLaws d) (instr : Instr c Γ τ) :
    @Measure (instr.Tape d) (instrSpace d instr) :=
  match instr with
  | .gaussian => L.pointDraw
  | .uniform => L.uniformDraw
  | .pure _ | .center | .momentum | .grad _ => Measure.dirac (α := PUnit) PUnit.unit

/-- Syntax-recursive product law, retaining every child occurrence and tail.
Repeated equal-code children get separate coordinates in the finite Pi product. -/
def tapeLaw (L : PrimitiveLaws d) (p : Prog c Γ τ) :
    @Measure (Tape d p) (tapeSpace d p) :=
  match p with
  | .ret _ => Measure.dirac (α := PUnit) PUnit.unit
  | .step _ instr next =>
      let : MeasurableSpace (instr.Tape d) := instrSpace d instr
      let : MeasurableSpace (Tape d next) := tapeSpace d next
      (instrLaw L instr).prod (tapeLaw L next)
  | .batch _ children next =>
      let : ∀ j, MeasurableSpace (Tape d (children j)) :=
        fun j => tapeSpace d (children j)
      let : MeasurableSpace (Tape d next) := tapeSpace d next
      (Measure.pi (fun j => tapeLaw L (children j))).prod (tapeLaw L next)

/-- Only uniforms survive in the residual. No point-law dependency is added. -/
def instrResidualLaw (ν : Measure UniformValue) (instr : Instr c Γ τ) :
    @Measure (InstrResidualTape instr) (instrResidualSpace instr) :=
  match instr with
  | .uniform => ν
  | .pure _ | .center | .momentum | .grad _ | .gaussian => Measure.dirac (α := PUnit) PUnit.unit

/-- Candidate residual product law, recursively retaining every uniform leaf.
Identification with the residual marginal of tapeLaw is a separate theorem. -/
def residualLaw (ν : Measure UniformValue) (p : Prog c Γ τ) :
    @Measure (ResidualTape p) (residualSpace p) :=
  match p with
  | .ret _ => Measure.dirac (α := PUnit) PUnit.unit
  | .step _ instr next =>
      let : MeasurableSpace (InstrResidualTape instr) := instrResidualSpace instr
      let : MeasurableSpace (ResidualTape next) := residualSpace next
      (instrResidualLaw ν instr).prod (residualLaw ν next)
  | .batch _ children next =>
      let : ∀ j, MeasurableSpace (ResidualTape (children j)) :=
        fun j => residualSpace (children j)
      let : MeasurableSpace (ResidualTape next) := residualSpace next
      (Measure.pi (fun j => residualLaw ν (children j))).prod (residualLaw ν next)

theorem instrLaw_probability (L : PrimitiveLaws d) (instr : Instr c Γ τ) :
    let : MeasurableSpace (instr.Tape d) := instrSpace d instr
    IsProbabilityMeasure (instrLaw L instr) := by
  cases instr with
  | gaussian => exact L.point_probability
  | uniform => exact L.uniform_probability
  | pure p => change IsProbabilityMeasure (Measure.dirac (α := PUnit) PUnit.unit); infer_instance
  | center => change IsProbabilityMeasure (Measure.dirac (α := PUnit) PUnit.unit); infer_instance
  | momentum => change IsProbabilityMeasure (Measure.dirac (α := PUnit) PUnit.unit); infer_instance
  | grad r => change IsProbabilityMeasure (Measure.dirac (α := PUnit) PUnit.unit); infer_instance

/-- Normalization follows by induction, not by assuming a full tape law. -/
theorem tapeLaw_probability (L : PrimitiveLaws d) (p : Prog c Γ τ) :
    let : MeasurableSpace (Tape d p) := tapeSpace d p
    IsProbabilityMeasure (tapeLaw L p) := by
  induction p with
  | ret r => change IsProbabilityMeasure (Measure.dirac (α := PUnit) PUnit.unit); infer_instance
  | step origin instr next ih =>
      let : MeasurableSpace (instr.Tape d) := instrSpace d instr
      let : MeasurableSpace (Tape d next) := tapeSpace d next
      let : IsProbabilityMeasure (instrLaw L instr) := instrLaw_probability L instr
      let : IsProbabilityMeasure (tapeLaw L next) := ih
      change IsProbabilityMeasure ((instrLaw L instr).prod (tapeLaw L next))
      infer_instance
  | batch origin children next ihChildren ihNext =>
      let : ∀ j, MeasurableSpace (Tape d (children j)) :=
        fun j => tapeSpace d (children j)
      let : MeasurableSpace (Tape d next) := tapeSpace d next
      let : ∀ j, IsProbabilityMeasure (tapeLaw L (children j)) := ihChildren
      let : IsProbabilityMeasure (tapeLaw L next) := ihNext
      change IsProbabilityMeasure
        ((Measure.pi (fun j => tapeLaw L (children j))).prod (tapeLaw L next))
      infer_instance

theorem instrResidualLaw_probability (ν : Measure UniformValue) [IsProbabilityMeasure ν]
    (instr : Instr c Γ τ) :
    let : MeasurableSpace (InstrResidualTape instr) := instrResidualSpace instr
    IsProbabilityMeasure (instrResidualLaw ν instr) := by
  cases instr with
  | uniform => assumption
  | pure p => change IsProbabilityMeasure (Measure.dirac (α := PUnit) PUnit.unit); infer_instance
  | center => change IsProbabilityMeasure (Measure.dirac (α := PUnit) PUnit.unit); infer_instance
  | momentum => change IsProbabilityMeasure (Measure.dirac (α := PUnit) PUnit.unit); infer_instance
  | grad r => change IsProbabilityMeasure (Measure.dirac (α := PUnit) PUnit.unit); infer_instance
  | gaussian => change IsProbabilityMeasure (Measure.dirac (α := PUnit) PUnit.unit); infer_instance

theorem residualLaw_probability (ν : Measure UniformValue) [IsProbabilityMeasure ν]
    (p : Prog c Γ τ) :
    let : MeasurableSpace (ResidualTape p) := residualSpace p
    IsProbabilityMeasure (residualLaw ν p) := by
  induction p with
  | ret r => change IsProbabilityMeasure (Measure.dirac (α := PUnit) PUnit.unit); infer_instance
  | step origin instr next ih =>
      let : MeasurableSpace (InstrResidualTape instr) := instrResidualSpace instr
      let : MeasurableSpace (ResidualTape next) := residualSpace next
      let : IsProbabilityMeasure (instrResidualLaw ν instr) :=
        instrResidualLaw_probability ν instr
      let : IsProbabilityMeasure (residualLaw ν next) := ih
      change IsProbabilityMeasure ((instrResidualLaw ν instr).prod (residualLaw ν next))
      infer_instance
  | batch origin children next ihChildren ihNext =>
      let : ∀ j, MeasurableSpace (ResidualTape (children j)) :=
        fun j => residualSpace (children j)
      let : MeasurableSpace (ResidualTape next) := residualSpace next
      let : ∀ j, IsProbabilityMeasure (residualLaw ν (children j)) := ihChildren
      let : IsProbabilityMeasure (residualLaw ν next) := ihNext
      change IsProbabilityMeasure
        ((Measure.pi (fun j => residualLaw ν (children j))).prod (residualLaw ν next))
      infer_instance

/-- Literal head/tail rectangle factorization. Product-model independence is
proved at the actual syntax seam, without assuming independence of evaluations. -/
theorem tapeLaw_step_rectangle (L : PrimitiveLaws d) (origin : Origin)
    (instr : Instr c Γ σ) (next : Prog c (σ :: Γ) τ)
    (A : Set (instr.Tape d)) (B : Set (Tape d next)) :
    tapeLaw L (.step origin instr next) (A ×ˢ B) =
      instrLaw L instr A * tapeLaw L next B := by
  let : MeasurableSpace (instr.Tape d) := instrSpace d instr
  let : MeasurableSpace (Tape d next) := tapeSpace d next
  let : IsProbabilityMeasure (tapeLaw L next) := tapeLaw_probability L next
  exact Measure.prod_prod A B

/-- Every child occurrence contributes, even when its output is unused. -/
theorem tapeLaw_batch_rectangle (L : PrimitiveLaws d) (origin : Origin)
    (children : Fin n → Prog c Γ .point)
    (next : Prog c (List.replicate n .point ++ Γ) τ)
    (A : ∀ j, Set (Tape d (children j))) (B : Set (Tape d next)) :
    tapeLaw L (Prog.batch (c := c) (Γ := Γ) (τ := τ) (n := n) origin children next)
      (by exact Set.pi Set.univ A ×ˢ B) =
      (∏ j, tapeLaw L (children j) (A j)) * tapeLaw L next B := by
  let : ∀ j, MeasurableSpace (Tape d (children j)) :=
    fun j => tapeSpace d (children j)
  let : MeasurableSpace (Tape d next) := tapeSpace d next
  let : ∀ j, IsProbabilityMeasure (tapeLaw L (children j)) :=
    fun j => tapeLaw_probability L (children j)
  let : IsProbabilityMeasure (tapeLaw L next) := tapeLaw_probability L next
  change (Measure.pi (fun j => tapeLaw L (children j))).prod (tapeLaw L next)
    (Set.pi Set.univ A ×ˢ B) = _
  rw [Measure.prod_prod, Measure.pi_pi]

theorem residualLaw_step_rectangle (ν : Measure UniformValue) [IsProbabilityMeasure ν]
    (origin : Origin) (instr : Instr c Γ σ) (next : Prog c (σ :: Γ) τ)
    (A : Set (InstrResidualTape instr)) (B : Set (ResidualTape next)) :
    residualLaw ν (.step origin instr next) (A ×ˢ B) =
      instrResidualLaw ν instr A * residualLaw ν next B := by
  let : MeasurableSpace (InstrResidualTape instr) := instrResidualSpace instr
  let : MeasurableSpace (ResidualTape next) := residualSpace next
  let : IsProbabilityMeasure (residualLaw ν next) := residualLaw_probability ν next
  exact Measure.prod_prod A B

theorem residualLaw_batch_rectangle (ν : Measure UniformValue) [IsProbabilityMeasure ν]
    (origin : Origin) (children : Fin n → Prog c Γ .point)
    (next : Prog c (List.replicate n .point ++ Γ) τ)
    (A : ∀ j, Set (ResidualTape (children j))) (B : Set (ResidualTape next)) :
    residualLaw ν (Prog.batch (c := c) (Γ := Γ) (τ := τ) (n := n) origin children next)
      (by exact Set.pi Set.univ A ×ˢ B) =
      (∏ j, residualLaw ν (children j) (A j)) * residualLaw ν next B := by
  let : ∀ j, MeasurableSpace (ResidualTape (children j)) :=
    fun j => residualSpace (children j)
  let : MeasurableSpace (ResidualTape next) := residualSpace next
  let : ∀ j, IsProbabilityMeasure (residualLaw ν (children j)) :=
    fun j => residualLaw_probability ν (children j)
  let : IsProbabilityMeasure (residualLaw ν next) := residualLaw_probability ν next
  change (Measure.pi (fun j => residualLaw ν (children j))).prod (residualLaw ν next)
    (Set.pi Set.univ A ×ˢ B) = _
  rw [Measure.prod_prod, Measure.pi_pi]

/-- Exact transported law, not a postulated flattened product law. -/
def splitLaw (L : PrimitiveLaws d) (p : Prog c Γ τ) :
    let : MeasurableSpace (ResidualTape p) := residualSpace p
    Measure ((GaussianSlot p → Point d) × ResidualTape p) := by
  let : MeasurableSpace (Tape d p) := tapeSpace d p
  let : MeasurableSpace (ResidualTape p) := residualSpace p
  exact (tapeLaw L p).map (splitGaussianMeasurableEquiv d p)

theorem splitLaw_probability (L : PrimitiveLaws d) (p : Prog c Γ τ) :
    let : MeasurableSpace (ResidualTape p) := residualSpace p
    IsProbabilityMeasure (splitLaw L p) := by
  let : MeasurableSpace (Tape d p) := tapeSpace d p
  let : MeasurableSpace (ResidualTape p) := residualSpace p
  let : IsProbabilityMeasure (tapeLaw L p) := tapeLaw_probability L p
  change IsProbabilityMeasure ((tapeLaw L p).map (splitGaussianMeasurableEquiv d p))
  infer_instance

/-- Exact event transport along the same measurable equivalence, for any set. -/
theorem splitLaw_apply (L : PrimitiveLaws d) (p : Prog c Γ τ)
    (A : Set ((GaussianSlot p → Point d) × ResidualTape p)) :
    splitLaw L p A = tapeLaw L p (splitTape p ⁻¹' A) := by
  let : MeasurableSpace (Tape d p) := tapeSpace d p
  let : MeasurableSpace (ResidualTape p) := residualSpace p
  exact (splitGaussianMeasurableEquiv d p).map_apply A

/-- Joining the transported law recovers the recursive law without loss. -/
theorem map_join_splitLaw (L : PrimitiveLaws d) (p : Prog c Γ τ) :
    let : MeasurableSpace (Tape d p) := tapeSpace d p
    let : MeasurableSpace (ResidualTape p) := residualSpace p
    (splitLaw L p).map (fun a => joinTape p a.1 a.2) = tapeLaw L p := by
  let : MeasurableSpace (Tape d p) := tapeSpace d p
  let : MeasurableSpace (ResidualTape p) := residualSpace p
  exact MeasurableEquiv.map_symm_map (splitGaussianMeasurableEquiv d p)

/-- Measurable observations have the same law in literal and split coordinates. -/
theorem map_splitLaw_observable {β : Type*} [MeasurableSpace β]
    (L : PrimitiveLaws d) (p : Prog c Γ τ) (f : Tape d p → β)
    (hf : @Measurable (Tape d p) β (tapeSpace d p) _ f) :
    let : MeasurableSpace (Tape d p) := tapeSpace d p
    let : MeasurableSpace (ResidualTape p) := residualSpace p
    (splitLaw L p).map (fun a => f (joinTape p a.1 a.2)) =
      (tapeLaw L p).map f := by
  let : MeasurableSpace (Tape d p) := tapeSpace d p
  let : MeasurableSpace (ResidualTape p) := residualSpace p
  calc
    (splitLaw L p).map (fun a => f (joinTape p a.1 a.2)) =
        ((splitLaw L p).map (fun a => joinTape p a.1 a.2)).map f :=
      (Measure.map_map hf (measurable_joinTape d p)).symm
    _ = (tapeLaw L p).map f := congrArg (Measure.map f) (map_join_splitLaw L p)

/-- Actual execution has a genuine normalized output law for a measurable G.
The proof uses event transport explicitly, rather than relying only on Mathlib's
normalization of map, whose definition has a fallback for nonmeasurable maps. -/
theorem program_point_probability (L : PrimitiveLaws d) (p : Program c .point)
    (G : Point d → Point d) (hG : Measurable G)
    (coeff : Fin c → ℝ) (x P : Point d) :
    let : MeasurableSpace (Tape d p) := tapeSpace d p
    IsProbabilityMeasure ((tapeLaw L p).map (β := Point d)
      (fun ω => (run p G ⟨coeff, x, P⟩ Env.empty ω).value)) := by
  let : MeasurableSpace (Tape d p) := tapeSpace d p
  let : IsProbabilityMeasure (tapeLaw L p) := tapeLaw_probability L p
  have hf := program_point_of_measurable p G hG (fun _ : Tape d p => coeff)
    (fun _ => x) (fun _ => P) (fun ω => ω)
    measurable_const measurable_const measurable_const measurable_id
  constructor
  rw [Measure.map_apply hf MeasurableSet.univ]
  change tapeLaw L p Set.univ = 1
  exact measure_univ

/-- Event formula ties the output law to literal execution, not a map fallback. -/
theorem program_point_map_apply (L : PrimitiveLaws d) (p : Program c .point)
    (G : Point d → Point d) (hG : Measurable G)
    (coeff : Fin c → ℝ) (x P : Point d) (A : Set (Point d)) (hA : MeasurableSet A) :
    let : MeasurableSpace (Tape d p) := tapeSpace d p
    (tapeLaw L p).map (β := Point d) (fun ω => (run p G ⟨coeff, x, P⟩ Env.empty ω).value) A =
      tapeLaw L p {ω | (run p G ⟨coeff, x, P⟩ Env.empty ω).value ∈ A} := by
  let : MeasurableSpace (Tape d p) := tapeSpace d p
  exact Measure.map_apply
    (program_point_of_measurable p G hG (fun _ : Tape d p => coeff)
      (fun _ => x) (fun _ => P) (fun ω => ω)
      measurable_const measurable_const measurable_const measurable_id) hA

/-- Same actual output distribution, with every split residual coordinate kept. -/
theorem program_point_split_law (L : PrimitiveLaws d) (p : Program c .point)
    (G : Point d → Point d) (hG : Measurable G)
    (coeff : Fin c → ℝ) (x P : Point d) :
    let : MeasurableSpace (Tape d p) := tapeSpace d p
    let : MeasurableSpace (ResidualTape p) := residualSpace p
    (splitLaw L p).map (β := Point d) (fun a =>
      (run p G ⟨coeff, x, P⟩ Env.empty (joinTape p a.1 a.2)).value) =
      (tapeLaw L p).map (β := Point d) (fun ω => (run p G ⟨coeff, x, P⟩ Env.empty ω).value) := by
  let : MeasurableSpace (Tape d p) := tapeSpace d p
  let : MeasurableSpace (ResidualTape p) := residualSpace p
  exact map_splitLaw_observable L p _
    (program_point_of_measurable p G hG (fun _ : Tape d p => coeff)
      (fun _ => x) (fun _ => P) (fun ω => ω)
      measurable_const measurable_const measurable_const measurable_id)

end CanonicalTapeLaw
end AcceleratedLogConcave.Oracle
