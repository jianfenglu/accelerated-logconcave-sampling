import AcceleratedLogConcave.Oracle.SamplingOperationalMeasurability
import Mathlib.MeasureTheory.MeasurableSpace.Embedding

/-!
Canonical measurable structures on the EXISTING Tape and ResidualTape types.
The structures follow literal finite syntax and use only ordinary unit,
Euclidean, subtype, product and dependent-Pi measurable structures. No new
carrier, probability measure, law, independence, Fubini or accuracy premise.

All structures below are ordinary definitions, NOT global or scoped instances.
Each measurable statement specifies its structures explicitly, or installs them
with a local letI in its statement. Importing this module changes no global
instance search. The original evaluator and split/join functions are unchanged.
-/
noncomputable section
namespace AcceleratedLogConcave.Oracle
namespace CanonicalTapeMeasurability
open TapeLowering OperationalMeasurability Numerics.AffineGraph

/-- Existing Borel point, inherited uniform subtype, or ordinary unit structure. -/
@[instance_reducible] def instrSpace (d : ℕ) (instr : Instr c Γ τ) : MeasurableSpace (instr.Tape d) :=
  match instr with
  | .gaussian => inferInstanceAs (MeasurableSpace (Point d))
  | .uniform => inferInstanceAs (MeasurableSpace UniformValue)
  | .pure _ | .center | .momentum | .grad _ => inferInstanceAs (MeasurableSpace PUnit)

/-- Canonical finite structural product on precisely the tape used by run. -/
@[instance_reducible] def tapeSpace (d : ℕ) (p : Prog c Γ τ) : MeasurableSpace (Tape d p) :=
  match p with
  | .ret _ => inferInstanceAs (MeasurableSpace PUnit)
  | .step _ instr next => (instrSpace d instr).prod (tapeSpace d next)
  | .batch _ children next =>
      let : ∀ j, MeasurableSpace (Tape d (children j)) :=
        fun j => tapeSpace d (children j)
      (inferInstance : MeasurableSpace (∀ j, Tape d (children j))).prod (tapeSpace d next)

/-- All uniform leaves survive Gaussian splitting, with their subtype structure. -/
@[instance_reducible] def instrResidualSpace (instr : Instr c Γ τ) : MeasurableSpace (InstrResidualTape instr) :=
  match instr with
  | .uniform => inferInstanceAs (MeasurableSpace UniformValue)
  | .pure _ | .center | .momentum | .grad _ | .gaussian =>
      inferInstanceAs (MeasurableSpace PUnit)

/-- Canonical product on the actual residual, including every child and tail. -/
@[instance_reducible] def residualSpace (p : Prog c Γ τ) : MeasurableSpace (ResidualTape p) :=
  match p with
  | .ret _ => inferInstanceAs (MeasurableSpace PUnit)
  | .step _ instr next => (instrResidualSpace instr).prod (residualSpace next)
  | .batch _ children next =>
      let : ∀ j, MeasurableSpace (ResidualTape (children j)) :=
        fun j => residualSpace (children j)
      (inferInstance : MeasurableSpace (∀ j, ResidualTape (children j))).prod
        (residualSpace next)

variable {α : Type*} [MeasurableSpace α]

/-- Uniform real-coordinate measurability is exactly subtype measurability. -/
theorem instr_measurable_iff (instr : Instr c Γ τ) (ω : α → instr.Tape d) :
    @Measurable α (instr.Tape d) _ (instrSpace d instr) ω ↔
      InstrTapePathMeasurable instr ω := by
  cases instr with
  | gaussian => exact Iff.rfl
  | uniform =>
      change Measurable (β := UniformValue) ω ↔ Measurable (fun a => (ω a).val)
      exact ⟨fun h => h.subtype_val, fun h => h.subtype_mk⟩
  | pure p => exact ⟨fun _ => trivial, fun _ => measurable_of_subsingleton_codomain (β := PUnit) _⟩
  | center => exact ⟨fun _ => trivial, fun _ => measurable_of_subsingleton_codomain (β := PUnit) _⟩
  | momentum => exact ⟨fun _ => trivial, fun _ => measurable_of_subsingleton_codomain (β := PUnit) _⟩
  | grad r => exact ⟨fun _ => trivial, fun _ => measurable_of_subsingleton_codomain (β := PUnit) _⟩

/-- Equivalence, not an extra output-regularity assumption: the old structural
predicate is EXACTLY measurability into the canonical full tape space. -/
theorem measurable_iff_tapePath (p : Prog c Γ τ) :
    ∀ ω : α → Tape d p,
      @Measurable α (Tape d p) _ (tapeSpace d p) ω ↔ TapePathMeasurable p ω := by
  induction p with
  | ret r =>
      intro ω
      exact ⟨fun _ => trivial, fun _ => measurable_of_subsingleton_codomain (β := PUnit) _⟩
  | step origin instr next ih =>
      intro ω
      let : MeasurableSpace (instr.Tape d) := instrSpace d instr
      let : MeasurableSpace (Tape d next) := tapeSpace d next
      change Measurable (β := instr.Tape d × Tape d next) ω ↔
        InstrTapePathMeasurable instr (fun a => (ω a).1) ∧
          TapePathMeasurable next (fun a => (ω a).2)
      constructor
      · intro h
        exact ⟨(instr_measurable_iff instr _).mp h.fst, (ih _).mp h.snd⟩
      · intro h
        exact ((instr_measurable_iff instr _).mpr h.1).prodMk ((ih _).mpr h.2)
  | batch origin children next ihChildren ihNext =>
      intro ω
      let : ∀ j, MeasurableSpace (Tape d (children j)) :=
        fun j => tapeSpace d (children j)
      let : MeasurableSpace (Tape d next) := tapeSpace d next
      change Measurable (β := (∀ j, Tape d (children j)) × Tape d next) ω ↔
        (∀ j, TapePathMeasurable (children j) (fun a => (ω a).1 j)) ∧
          TapePathMeasurable next (fun a => (ω a).2)
      constructor
      · intro h
        exact ⟨fun j => (ihChildren j _).mp ((measurable_pi_apply j).comp h.fst),
          (ihNext _).mp h.snd⟩
      · intro h
        have hc : Measurable (fun a => (ω a).1) :=
          measurable_pi_iff.mpr (fun j => (ihChildren j _).mpr (h.1 j))
        exact hc.prodMk ((ihNext _).mpr h.2)

theorem instrResidual_measurable_iff (instr : Instr c Γ τ)
    (υ : α → InstrResidualTape instr) :
    @Measurable α (InstrResidualTape instr) _ (instrResidualSpace instr) υ ↔
      InstrResidualPathMeasurable instr υ := by
  cases instr with
  | uniform =>
      change Measurable (β := UniformValue) υ ↔ Measurable (fun a => (υ a).val)
      exact ⟨fun h => h.subtype_val, fun h => h.subtype_mk⟩
  | pure p => exact ⟨fun _ => trivial, fun _ => measurable_of_subsingleton_codomain (β := PUnit) _⟩
  | center => exact ⟨fun _ => trivial, fun _ => measurable_of_subsingleton_codomain (β := PUnit) _⟩
  | momentum => exact ⟨fun _ => trivial, fun _ => measurable_of_subsingleton_codomain (β := PUnit) _⟩
  | grad r => exact ⟨fun _ => trivial, fun _ => measurable_of_subsingleton_codomain (β := PUnit) _⟩
  | gaussian => exact ⟨fun _ => trivial, fun _ => measurable_of_subsingleton_codomain (β := PUnit) _⟩

theorem measurable_iff_residualPath (p : Prog c Γ τ) :
    ∀ υ : α → ResidualTape p,
      @Measurable α (ResidualTape p) _ (residualSpace p) υ ↔
        ResidualPathMeasurable p υ := by
  induction p with
  | ret r =>
      intro υ
      exact ⟨fun _ => trivial, fun _ => measurable_of_subsingleton_codomain (β := PUnit) _⟩
  | step origin instr next ih =>
      intro υ
      let : MeasurableSpace (InstrResidualTape instr) := instrResidualSpace instr
      let : MeasurableSpace (ResidualTape next) := residualSpace next
      change Measurable (β := InstrResidualTape instr × ResidualTape next) υ ↔
        InstrResidualPathMeasurable instr (fun a => (υ a).1) ∧
          ResidualPathMeasurable next (fun a => (υ a).2)
      constructor
      · intro h
        exact ⟨(instrResidual_measurable_iff instr _).mp h.fst, (ih _).mp h.snd⟩
      · intro h
        exact ((instrResidual_measurable_iff instr _).mpr h.1).prodMk ((ih _).mpr h.2)
  | batch origin children next ihChildren ihNext =>
      intro υ
      let : ∀ j, MeasurableSpace (ResidualTape (children j)) :=
        fun j => residualSpace (children j)
      let : MeasurableSpace (ResidualTape next) := residualSpace next
      change Measurable (β := (∀ j, ResidualTape (children j)) × ResidualTape next) υ ↔
        (∀ j, ResidualPathMeasurable (children j) (fun a => (υ a).1 j)) ∧
          ResidualPathMeasurable next (fun a => (υ a).2)
      constructor
      · intro h
        exact ⟨fun j => (ihChildren j _).mp ((measurable_pi_apply j).comp h.fst),
          (ihNext _).mp h.snd⟩
      · intro h
        have hc : Measurable (fun a => (υ a).1) :=
          measurable_pi_iff.mpr (fun j => (ihChildren j _).mpr (h.1 j))
        exact hc.prodMk ((ihNext _).mpr h.2)

/-- Read ALL split coordinates from the exact splitTape implementation. The
left sum/sigma routes go to instruction/child slots; the right goes to the tail.
This does not choose a flattened replacement carrier or forget uniform leaves. -/
theorem splitTape_paths (p : Prog c Γ τ) :
    ∀ ω : α → Tape d p, TapePathMeasurable p ω →
      (∀ s, Measurable (fun a => (splitTape p (ω a)).1 s)) ∧
        ResidualPathMeasurable p (fun a => (splitTape p (ω a)).2) := by
  induction p with
  | ret r =>
      intro ω hω
      constructor
      · intro s
        exact nomatch s
      · trivial
  | step origin instr next ih =>
      intro ω hω
      have ht := ih (fun a => (ω a).2) hω.2
      constructor
      · intro s
        cases s with
        | inl s =>
            cases instr with
            | gaussian => exact hω.1
            | uniform => cases s
            | pure p => cases s
            | center => cases s
            | momentum => cases s
            | grad r => cases s
        | inr s => exact ht.1 s
      · constructor
        · cases instr with
          | uniform => exact hω.1
          | gaussian => trivial
          | pure p => trivial
          | center => trivial
          | momentum => trivial
          | grad r => trivial
        · exact ht.2
  | batch origin children next ihChildren ihNext =>
      intro ω hω
      have hc := fun j => ihChildren j (fun a => (ω a).1 j) (hω.1 j)
      have ht := ihNext (fun a => (ω a).2) hω.2
      constructor
      · intro s
        cases s with
        | inl s => exact (hc s.1).1 s.2
        | inr s => exact ht.1 s
      · exact ⟨fun j => (hc j).2, ht.2⟩

/-- Canonical full-tape -> Gaussian-array/residual product, all coordinates. -/
theorem measurable_splitTape (d : ℕ) (p : Prog c Γ τ) :
    let : MeasurableSpace (Tape d p) := tapeSpace d p
    let : MeasurableSpace (ResidualTape p) := residualSpace p
    Measurable (splitTape (d := d) p) := by
  let : MeasurableSpace (Tape d p) := tapeSpace d p
  let : MeasurableSpace (ResidualTape p) := residualSpace p
  have h := splitTape_paths p (fun ω : Tape d p => ω)
    ((measurable_iff_tapePath p _).mp measurable_id)
  exact (measurable_pi_iff.mpr h.1).prodMk ((measurable_iff_residualPath p _).mpr h.2)

/-- Canonical Gaussian-array/residual product -> exact original full tape. -/
theorem measurable_joinTape (d : ℕ) (p : Prog c Γ τ) :
    let : MeasurableSpace (Tape d p) := tapeSpace d p
    let : MeasurableSpace (ResidualTape p) := residualSpace p
    Measurable (fun a : (GaussianSlot p → Point d) × ResidualTape p =>
      joinTape p a.1 a.2) := by
  let : MeasurableSpace (Tape d p) := tapeSpace d p
  let : MeasurableSpace (ResidualTape p) := residualSpace p
  apply (measurable_iff_tapePath p _).mpr
  exact tapePathMeasurable_joinTape p Prod.fst Prod.snd
    (fun s => (measurable_pi_apply s).comp measurable_fst)
    ((measurable_iff_residualPath p _).mp measurable_snd)

/-- This is the SAME existing equivalence, furnished with measurable proofs.
Its inverse laws are exactly joinTape_splitTape and splitTape_joinTape. -/
def splitGaussianMeasurableEquiv (d : ℕ) (p : Prog c Γ τ) :
    let : MeasurableSpace (Tape d p) := tapeSpace d p
    let : MeasurableSpace (ResidualTape p) := residualSpace p
    Tape d p ≃ᵐ ((GaussianSlot p → Point d) × ResidualTape p) := by
  let : MeasurableSpace (Tape d p) := tapeSpace d p
  let : MeasurableSpace (ResidualTape p) := residualSpace p
  exact
    { toEquiv := splitGaussianTape d p
      measurable_toFun := measurable_splitTape d p
      measurable_invFun := measurable_joinTape d p }

/-- Exact coordinate characterization in split coordinates, in both directions. -/
theorem measurable_iff_split_coordinates (p : Prog c Γ τ) (ω : α → Tape d p) :
    @Measurable α (Tape d p) _ (tapeSpace d p) ω ↔
      (∀ s, Measurable (fun a => (splitTape p (ω a)).1 s)) ∧
        @Measurable α (ResidualTape p) _ (residualSpace p)
          (fun a => (splitTape p (ω a)).2) := by
  let : MeasurableSpace (Tape d p) := tapeSpace d p
  let : MeasurableSpace (ResidualTape p) := residualSpace p
  constructor
  · intro h
    have hs := (measurable_splitTape d p).comp h
    exact ⟨fun s => (measurable_pi_apply s).comp hs.fst, hs.snd⟩
  · intro h
    have hs : Measurable (fun a => splitTape p (ω a)) :=
      (measurable_pi_iff.mpr h.1).prodMk h.2
    have hj := (measurable_joinTape d p).comp hs
    simpa only [Function.comp_def, joinTape_splitTape] using hj

/-- An ordinary measurable tape map supplies the former structural obligations;
no structural predicate or child-output regularity premise remains here. -/
theorem program_point_of_measurable (p : Program c .point)
    (G : Point d → Point d) (hG : Measurable G)
    (coeff : α → Fin c → ℝ) (x P : α → Point d) (ω : α → Tape d p)
    (hc : Measurable coeff) (hx : Measurable x) (hP : Measurable P)
    (hω : @Measurable α (Tape d p) _ (tapeSpace d p) ω) :
    Measurable (β := Point d) (fun a => (run p G ⟨coeff a, x a, P a⟩ Env.empty (ω a)).value) :=
  OperationalMeasurability.program_point p G hG coeff x P ω
    (fun j => (measurable_pi_apply j).comp hc) hx hP
    ((measurable_iff_tapePath p ω).mp hω)

/-- Joint coefficient/center/momentum/full-tape measurability for any fixed
finite point program. Only the oracle remains fixed and explicitly measurable. -/
theorem program_point_joint (d : ℕ) (p : Program c .point)
    (G : Point d → Point d) (hG : Measurable G) :
    let : MeasurableSpace (Tape d p) := tapeSpace d p
    Measurable (β := Point d) (fun a : ((Fin c → ℝ) × (Point d × Point d)) × Tape d p =>
      (run p G ⟨a.1.1, a.1.2.1, a.1.2.2⟩ Env.empty a.2).value) := by
  let : MeasurableSpace (Tape d p) := tapeSpace d p
  exact program_point_of_measurable (α := ((Fin c → ℝ) × (Point d × Point d)) × Tape d p) p G hG (fun a => a.1.1)
    (fun a => a.1.2.1) (fun a => a.1.2.2) (fun a => a.2)
    measurable_fst.fst measurable_fst.snd.fst measurable_fst.snd.snd measurable_snd

/-- The literal SamplingExecutable.build, its real fixed coefficient table,
all actual children and the empty entering store. Existing SamplingGeometry
and executable data are retained; no extra positivity/accuracy record is used. -/
theorem sampling_build_of_measurable (S : SamplingGeometry m) (e : Fin n ≃ S.Node)
    (r Ds : ℝ) (main final : Fin n → ExecutableData) (N : ℕ)
    (G : Point d → Point d) (hG : Measurable G) (x P : α → Point d)
    (ω : α → Tape d (SamplingExecutable.build S e r Ds main final N).program)
    (hx : Measurable x) (hP : Measurable P)
    (hω : @Measurable α _ _
      (tapeSpace d (SamplingExecutable.build S e r Ds main final N).program) ω) :
    Measurable (β := Point d) (fun a =>
      (run (SamplingExecutable.build S e r Ds main final N).program G
        ⟨(SamplingExecutable.build S e r Ds main final N).coefficient, x a, P a⟩
        Env.empty (ω a)).value) :=
  program_point_of_measurable _ G hG
    (fun _ => (SamplingExecutable.build S e r Ds main final N).coefficient)
    x P ω measurable_const hx hP hω

/-- The missing canonical joint-FULL-tape statement, with all uniform,
Gaussian, sibling and continuation coordinates varying as actual product data. -/
theorem sampling_build_joint (d : ℕ) (S : SamplingGeometry m) (e : Fin n ≃ S.Node)
    (r Ds : ℝ) (main final : Fin n → ExecutableData) (N : ℕ)
    (G : Point d → Point d) (hG : Measurable G) :
    let : MeasurableSpace
      (Tape d (SamplingExecutable.build S e r Ds main final N).program) :=
      tapeSpace d (SamplingExecutable.build S e r Ds main final N).program
    Measurable (β := Point d) (fun a : (Point d × Point d) ×
        Tape d (SamplingExecutable.build S e r Ds main final N).program =>
      (run (SamplingExecutable.build S e r Ds main final N).program G
        ⟨(SamplingExecutable.build S e r Ds main final N).coefficient, a.1.1, a.1.2⟩
        Env.empty a.2).value) := by
  let : MeasurableSpace
    (Tape d (SamplingExecutable.build S e r Ds main final N).program) :=
    tapeSpace d (SamplingExecutable.build S e r Ds main final N).program
  exact sampling_build_of_measurable (α := (Point d × Point d) ×
      Tape d (SamplingExecutable.build S e r Ds main final N).program) S e r Ds main final N G hG
    (fun a => a.1.1) (fun a => a.1.2) (fun a => a.2)
    measurable_fst.fst measurable_fst.snd measurable_snd

/-- Equivalent actual-build joint statement in the exact split coordinates.
The entire residual varies; it is NOT fixed and its predicate is NOT assumed. -/
theorem sampling_build_joint_split (d : ℕ) (S : SamplingGeometry m) (e : Fin n ≃ S.Node)
    (r Ds : ℝ) (main final : Fin n → ExecutableData) (N : ℕ)
    (G : Point d → Point d) (hG : Measurable G) :
    let : MeasurableSpace
      (ResidualTape (SamplingExecutable.build S e r Ds main final N).program) :=
      residualSpace (SamplingExecutable.build S e r Ds main final N).program
    Measurable (β := Point d) (fun a : (Point d × Point d) ×
        ((GaussianSlot (SamplingExecutable.build S e r Ds main final N).program → Point d) ×
          ResidualTape (SamplingExecutable.build S e r Ds main final N).program) =>
      (run (SamplingExecutable.build S e r Ds main final N).program G
        ⟨(SamplingExecutable.build S e r Ds main final N).coefficient, a.1.1, a.1.2⟩
        Env.empty (joinTape (SamplingExecutable.build S e r Ds main final N).program
          a.2.1 a.2.2)).value) := by
  let : MeasurableSpace
    (ResidualTape (SamplingExecutable.build S e r Ds main final N).program) :=
    residualSpace (SamplingExecutable.build S e r Ds main final N).program
  let : MeasurableSpace
    (Tape d (SamplingExecutable.build S e r Ds main final N).program) :=
    tapeSpace d (SamplingExecutable.build S e r Ds main final N).program
  exact sampling_build_of_measurable (α := (Point d × Point d) ×
      ((GaussianSlot (SamplingExecutable.build S e r Ds main final N).program → Point d) ×
        ResidualTape (SamplingExecutable.build S e r Ds main final N).program))
    S e r Ds main final N G hG
    (fun a => a.1.1) (fun a => a.1.2) _ measurable_fst.fst measurable_fst.snd
    ((measurable_joinTape d _).comp measurable_snd)

end CanonicalTapeMeasurability
end AcceleratedLogConcave.Oracle
