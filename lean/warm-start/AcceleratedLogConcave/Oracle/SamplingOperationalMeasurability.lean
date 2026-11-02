import AcceleratedLogConcave.Oracle.SamplingExecutable
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
Measurability of the actual finite evaluator under explicit coordinate-path
assumptions. These predicates put no measurable-space instance on Tape, change
no tape representation, and assert no probability law or recursive accuracy.
Every Gaussian and uniform coordinate, including every child and continuation,
is retained. Only the returned value is treated, not Result or its event trace.
-/
noncomputable section
namespace AcceleratedLogConcave.Oracle
namespace OperationalMeasurability
open TapeLowering Numerics.AffineGraph

variable {α : Type*} [MeasurableSpace α]

/-- Ordinary measurability in the two actual value carriers. This avoids adding
a global measurable-space instance on the dependent value carrier Ty.denote. -/
def ValuePathMeasurable : (τ : Ty) → (α → Ty.denote d τ) → Prop
  | .scalar, f => Measurable (β := ℝ) (fun a => f a)
  | .point, f => Measurable (β := Point d) (fun a => f a)

/-- Every typed stored reference has a measurable value along the parameter. -/
def EnvPathMeasurable (ρ : α → Env d Γ) : Prop :=
  ∀ {τ : Ty} (r : Ref Γ τ), ValuePathMeasurable τ (fun a => ρ a r)

/-- An instruction asks only for measurability of its actual consumed datum.
Uniform endpoints are retained; pure/input/gradient instructions use unit tape. -/
def InstrTapePathMeasurable (instr : Instr c Γ τ) : (α → instr.Tape d) → Prop :=
  match instr with
  | .gaussian => fun ω => Measurable (β := Point d) (fun a => ω a)
  | .uniform => fun ω => Measurable (fun a => (ω a).val)
  | .pure _ | .center | .momentum | .grad _ => fun _ => True

/-- A coordinate condition on the EXISTING structural tape, not an assumed
measurability conclusion for execution. Every sibling and tail is checked. -/
def TapePathMeasurable (p : Prog c Γ τ) : (α → Tape d p) → Prop :=
  match p with
  | .ret _ => fun _ => True
  | .step _ instr next => fun ω =>
      InstrTapePathMeasurable instr (fun a => (ω a).1) ∧
        TapePathMeasurable next (fun a => (ω a).2)
  | .batch _ children next => fun ω =>
      (∀ j, TapePathMeasurable (children j) (fun a => (ω a).1 j)) ∧
        TapePathMeasurable next (fun a => (ω a).2)

/-- The split residual includes all actual uniforms, not just unit fillers. -/
def InstrResidualPathMeasurable (instr : Instr c Γ τ) :
    (α → InstrResidualTape instr) → Prop :=
  match instr with
  | .uniform => fun υ => Measurable (fun a => (υ a).val)
  | .pure _ | .center | .momentum | .grad _ | .gaussian => fun _ => True

def ResidualPathMeasurable (p : Prog c Γ τ) : (α → ResidualTape p) → Prop :=
  match p with
  | .ret _ => fun _ => True
  | .step _ instr next => fun υ =>
      InstrResidualPathMeasurable instr (fun a => (υ a).1) ∧
        ResidualPathMeasurable next (fun a => (υ a).2)
  | .batch _ children next => fun υ =>
      (∀ j, ResidualPathMeasurable (children j) (fun a => (υ a).1 j)) ∧
        ResidualPathMeasurable next (fun a => (υ a).2)

theorem envPathMeasurable_empty :
    EnvPathMeasurable (fun _ : α => (Env.empty : Env d [])) := by
  intro τ r
  cases r

theorem envPathMeasurable_cons (value : α → Ty.denote d τ) (ρ : α → Env d Γ)
    (hv : ValuePathMeasurable τ value) (hρ : EnvPathMeasurable ρ) :
    EnvPathMeasurable (fun a => Env.cons (value a) (ρ a)) := by
  intro σ r
  cases r with
  | here => exact hv
  | there r => exact hρ r

/-- The same ascending Fin order as Env.prepend, including the empty batch. -/
theorem envPathMeasurable_prepend (n : ℕ) :
    ∀ (values : α → Fin n → Point d) (ρ : α → Env d Γ),
      (∀ j, Measurable (fun a => values a j)) → EnvPathMeasurable ρ →
        EnvPathMeasurable (fun a => Env.prepend (values a) (ρ a)) := by
  induction n with
  | zero =>
      intro values ρ hv hρ
      exact hρ
  | succ n ih =>
      intro values ρ hv hρ
      exact envPathMeasurable_cons (τ := .point) (fun a => values a 0)
        (fun a => Env.prepend (fun j => values a j.succ) (ρ a)) (hv 0)
        (ih (fun a j => values a j.succ) ρ (fun j => hv j.succ) hρ)

/-- Every closed primitive is treated, including total inverse at zero and
total real square root. No domain-validity or coefficient-sign claim is made. -/
theorem evalPure_value (p : Pure c Γ τ) (coeff : α → Fin c → ℝ)
    (ρ : α → Env d Γ) (hc : ∀ j, Measurable (fun a => coeff a j))
    (hρ : EnvPathMeasurable ρ) :
    ValuePathMeasurable τ (fun a => evalPure p (coeff a) (ρ a)) := by
  have hs (r : Ref Γ .scalar) : Measurable (β := ℝ) (fun a => ρ a r) := hρ r
  have hp (r : Ref Γ .point) : Measurable (β := Point d) (fun a => ρ a r) := hρ r
  cases p with
  | publicScalar j => exact hc j
  | rational q => exact measurable_const
  | add x y => exact (hs x).add (hs y)
  | mul x y => exact (hs x).mul (hs y)
  | neg x => exact (hs x).neg
  | inv x => exact (hs x).inv
  | sqrt x => exact (hs x).sqrt
  | zero => exact measurable_const
  | vadd x y => exact (hp x).add (hp y)
  | smul x y => exact (hs x).smul (hp y)

theorem evalInstr_value (origin : Origin) (instr : Instr c Γ τ)
    (G : Point d → Point d) (hG : Measurable G) (input : α → Inputs d c)
    (ρ : α → Env d Γ) (ω : α → instr.Tape d)
    (hc : ∀ j, Measurable (fun a => (input a).coefficient j))
    (hx : Measurable (fun a => (input a).center))
    (hP : Measurable (fun a => (input a).momentum))
    (hρ : EnvPathMeasurable ρ) (hω : InstrTapePathMeasurable instr ω) :
    ValuePathMeasurable τ (fun a => (evalInstr origin instr G (input a) (ρ a) (ω a)).value) := by
  cases instr with
  | pure p => exact evalPure_value p (fun a => (input a).coefficient) ρ hc hρ
  | center => exact hx
  | momentum => exact hP
  | grad r => exact hG.comp (hρ r)
  | gaussian => exact hω
  | uniform => exact hω

/-- Induction through the literal evaluator. Batch IHs apply to each child's
actual raw tape and common pre-batch store, then to the actual continuation.
No child measurability certificate or sampler conclusion is assumed. -/
theorem run_value (p : Prog c Γ τ) (G : Point d → Point d) (hG : Measurable G) :
    ∀ (input : α → Inputs d c) (ρ : α → Env d Γ) (ω : α → Tape d p),
      (∀ j, Measurable (fun a => (input a).coefficient j)) →
      Measurable (fun a => (input a).center) →
      Measurable (fun a => (input a).momentum) →
      EnvPathMeasurable ρ → TapePathMeasurable p ω →
      ValuePathMeasurable τ (fun a => (run p G (input a) (ρ a) (ω a)).value) := by
  induction p with
  | ret r =>
      intro input ρ ω hc hx hP hρ hω
      exact hρ r
  | step origin instr next ih =>
      intro input ρ ω hc hx hP hρ hω
      have hv := evalInstr_value origin instr G hG input ρ (fun a => (ω a).1)
        hc hx hP hρ hω.1
      exact ih input
        (fun a => Env.cons (evalInstr origin instr G (input a) (ρ a) (ω a).1).value (ρ a))
        (fun a => (ω a).2) hc hx hP
        (envPathMeasurable_cons _ ρ hv hρ) hω.2
  | batch origin children next ihChildren ihNext =>
      intro input ρ ω hc hx hP hρ hω
      have hv (j) : Measurable (β := Point d) (fun a =>
          ((run (children j) G (input a) (ρ a) ((ω a).1 j)).value : Point d)) :=
        ihChildren j input ρ (fun a => (ω a).1 j) hc hx hP hρ (hω.1 j)
      exact ihNext input
        (fun a => Env.prepend
          (fun j => (run (children j) G (input a) (ρ a) ((ω a).1 j)).value) (ρ a))
        (fun a => (ω a).2) hc hx hP
        (envPathMeasurable_prepend _ _ ρ hv hρ) hω.2

/-- Empty-store root specialization; coefficients may themselves vary
measurably. The code remains fixed, as required by the finite syntax model. -/
theorem program_point (p : Program c .point) (G : Point d → Point d)
    (hG : Measurable G) (coeff : α → Fin c → ℝ) (x P : α → Point d)
    (ω : α → Tape d p) (hc : ∀ j, Measurable (fun a => coeff a j))
    (hx : Measurable x) (hP : Measurable P) (hω : TapePathMeasurable p ω) :
    Measurable (β := Point d) (fun a => ((run p G ⟨coeff a, x a, P a⟩ Env.empty (ω a)).value : Point d)) :=
  run_value p G hG (fun a => ⟨coeff a, x a, P a⟩) (fun _ => Env.empty) ω
    hc hx hP envPathMeasurable_empty hω

theorem residualPathMeasurable_const (p : Prog c Γ τ) :
    ∀ υ : ResidualTape p, ResidualPathMeasurable p (fun _ : α => υ) := by
  induction p with
  | ret r => intro υ; trivial
  | step origin instr next ih =>
      intro υ
      constructor
      · cases instr <;> try trivial
        exact measurable_const
      · exact ih υ.2
  | batch origin children next ihChildren ihNext =>
      intro υ
      exact ⟨fun j => ihChildren j (υ.1 j), ihNext υ.2⟩

/-- Reconstructing the EXISTING tape preserves the explicit coordinate
condition. Gaussian coordinates may be correlated or repeated, and uniform
residual coordinates may vary; neither independence nor a law is assumed. -/
theorem tapePathMeasurable_joinTape (p : Prog c Γ τ) :
    ∀ (z : α → GaussianSlot p → Point d) (υ : α → ResidualTape p),
      (∀ s, Measurable (fun a => z a s)) → ResidualPathMeasurable p υ →
      TapePathMeasurable p (fun a => joinTape p (z a) (υ a)) := by
  induction p with
  | ret r => intro z υ hz hυ; trivial
  | step origin instr next ih =>
      intro z υ hz hυ
      constructor
      · cases instr with
        | gaussian =>
            change Measurable (fun a => z a (.inl PUnit.unit))
            exact hz (.inl PUnit.unit)
        | uniform => exact hυ.1
        | pure p => trivial
        | center => trivial
        | momentum => trivial
        | grad r => trivial
      · exact ih (fun a s => z a (.inr s)) (fun a => (υ a).2)
          (fun s => hz (.inr s)) hυ.2
  | batch origin children next ihChildren ihNext =>
      intro z υ hz hυ
      constructor
      · intro j
        exact ihChildren j (fun a s => z a (.inl ⟨j, s⟩)) (fun a => (υ a).1 j)
          (fun s => hz (.inl ⟨j, s⟩)) (hυ.1 j)
      · exact ihNext (fun a s => z a (.inr s)) (fun a => (υ a).2)
          (fun s => hz (.inr s)) hυ.2

/-- The ACTUAL sampling build, with its actual coefficient table, children,
setup and continuation tape. No ChildStable premise or rank induction is used.
This is a measurability theorem only; all analytic accuracy obligations remain. -/
theorem sampling_build_value (S : SamplingGeometry m) (e : Fin n ≃ S.Node)
    (r Ds : ℝ) (main final : Fin n → ExecutableData) (N : ℕ)
    (G : Point d → Point d) (hG : Measurable G) (x P : α → Point d)
    (ω : α → Tape d (SamplingExecutable.build S e r Ds main final N).program)
    (hx : Measurable x) (hP : Measurable P)
    (hω : TapePathMeasurable (SamplingExecutable.build S e r Ds main final N).program ω) :
    Measurable (β := Point d) (fun a =>
      ((run (SamplingExecutable.build S e r Ds main final N).program G
        ⟨(SamplingExecutable.build S e r Ds main final N).coefficient, x a, P a⟩
        Env.empty (ω a)).value : Point d)) :=
  program_point _ G hG (fun _ => (SamplingExecutable.build S e r Ds main final N).coefficient)
    x P ω (fun _ => measurable_const) hx hP hω

/-- Operational composition with a varying finite Gaussian array and the
complete varying residual tape. The latter's uniform-coordinate obligations
are explicit, not discarded by the Gaussian split. -/
theorem sampling_build_value_joinTape (S : SamplingGeometry m) (e : Fin n ≃ S.Node)
    (r Ds : ℝ) (main final : Fin n → ExecutableData) (N : ℕ)
    (G : Point d → Point d) (hG : Measurable G) (x P : α → Point d)
    (z : α → GaussianSlot (SamplingExecutable.build S e r Ds main final N).program → Point d)
    (υ : α → ResidualTape (SamplingExecutable.build S e r Ds main final N).program)
    (hx : Measurable x) (hP : Measurable P)
    (hz : ∀ s, Measurable (fun a => z a s))
    (hυ : ResidualPathMeasurable (SamplingExecutable.build S e r Ds main final N).program υ) :
    Measurable (β := Point d) (fun a =>
      ((run (SamplingExecutable.build S e r Ds main final N).program G
        ⟨(SamplingExecutable.build S e r Ds main final N).coefficient, x a, P a⟩ Env.empty
        (joinTape (SamplingExecutable.build S e r Ds main final N).program (z a) (υ a))).value : Point d)) :=
  sampling_build_value S e r Ds main final N G hG x P _ hx hP
    (tapePathMeasurable_joinTape _ z υ hz hυ)

end OperationalMeasurability
end AcceleratedLogConcave.Oracle
