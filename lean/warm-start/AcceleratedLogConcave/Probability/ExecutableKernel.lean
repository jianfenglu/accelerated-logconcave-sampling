import AcceleratedLogConcave.Probability.MixedResidualTape
import AcceleratedLogConcave.Oracle.RecursiveExecutable

/-! Joint measurability and Markov kernels of the actual finite interpreter.
The source specialization uses the constructed precision program with its full
independent instruction tape, including all uniform/unit coordinates. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Probability.ExecutableKernel
open Oracle MixedResidualTape
instance valueMeasurableSpace (d : ℕ) : (τ : Ty) → MeasurableSpace (Ty.denote d τ)
  | .scalar => inferInstanceAs (MeasurableSpace ℝ)
  | .point => inferInstanceAs (MeasurableSpace (Point d))
variable {Ω : Type*} [MeasurableSpace Ω]

theorem measurable_cons {value : Ω → Ty.denote d σ} {env : Ω → Env d Γ}
    (hv : Measurable value) (he : ∀ τ (r : Ref Γ τ), Measurable (fun ω => env ω r))
    (r : Ref (σ::Γ) τ) : Measurable (fun ω => Env.cons (value ω) (env ω) r) := by
  cases r with
  | here => exact hv
  | there r => exact he _ r

theorem measurable_prepend {values : Ω → Fin n → Point d} {env : Ω → Env d Γ}
    (hv : ∀ j, Measurable (fun ω => values ω j))
    (he : ∀ τ (r : Ref Γ τ), Measurable (fun ω => env ω r))
    (r : Ref (List.replicate n .point ++ Γ) τ) :
    Measurable (fun ω => Env.prepend (values ω) (env ω) r) := by
  induction n with
  | zero => exact he _ r
  | succ n ih =>
    cases r with
    | here => exact hv 0
    | there r => exact ih (fun j => hv j.succ) r

theorem measurable_pure (p : Pure c Γ τ) {coeff : Ω → Fin c → ℝ} {env : Ω → Env d Γ}
    (hc : ∀ j, Measurable (fun ω => coeff ω j))
    (he : ∀ τ (r : Ref Γ τ), Measurable (fun ω => env ω r)) :
    Measurable (fun ω => evalPure p (coeff ω) (env ω)) := by
  let sx : Ref Γ .scalar → Ω → ℝ := fun r ω => env ω r
  let vx : Ref Γ .point → Ω → Point d := fun r ω => env ω r
  have hs (r : Ref Γ .scalar) : Measurable (fun ω => (env ω r : ℝ)) := he _ r
  have hv (r : Ref Γ .point) : Measurable (fun ω => (env ω r : Point d)) := he _ r
  cases p with
  | publicScalar j => exact hc j
  | rational _ => exact measurable_const
  | add x y =>
    change Measurable (fun ω => sx x ω + sx y ω)
    exact (show Measurable (fun p : ℝ × ℝ => p.1 + p.2) from measurable_add).comp ((hs x).prodMk (hs y))
  | mul x y =>
    change Measurable (fun ω => sx x ω * sx y ω)
    exact (show Measurable (fun p : ℝ × ℝ => p.1 * p.2) from measurable_mul).comp ((hs x).prodMk (hs y))
  | neg x =>
    change Measurable (fun ω => -(sx x ω))
    exact (show Measurable (fun x : ℝ => -x) from measurable_neg).comp (hs x)
  | inv x =>
    change Measurable (fun ω => (sx x ω)⁻¹)
    exact (show Measurable (fun x : ℝ => x⁻¹) from measurable_inv).comp (hs x)
  | sqrt x => exact Real.continuous_sqrt.measurable.comp (he _ x)
  | zero => exact measurable_const
  | vadd x y =>
    change Measurable (fun ω => vx x ω + vx y ω)
    exact (show Measurable (fun p : Point d × Point d => p.1 + p.2) from measurable_add).comp ((hv x).prodMk (hv y))
  | smul a x =>
    change Measurable (fun ω => sx a ω • vx x ω)
    exact (show Measurable (fun p : ℝ × Point d => p.1 • p.2) from measurable_smul).comp ((hs a).prodMk (hv x))

theorem measurable_instr (origin : Origin) (i : Instr c Γ τ)
    {G : Point d → Point d} (hG : Measurable G) {input : Ω → Inputs d c}
    {env : Ω → Env d Γ} {tape : Ω → i.Tape d}
    (hc : ∀ j, Measurable (fun ω => (input ω).coefficient j))
    (hx : Measurable (fun ω => (input ω).center))
    (hp : Measurable (fun ω => (input ω).momentum))
    (he : ∀ τ (r : Ref Γ τ), Measurable (fun ω => env ω r)) (ht : Measurable tape) :
    Measurable (fun ω => (evalInstr origin i G (input ω) (env ω) (tape ω)).value) := by
  cases i with
  | pure p => exact measurable_pure p hc he
  | center => exact hx
  | momentum => exact hp
  | grad r => exact hG.comp (he _ r)
  | gaussian => exact ht
  | uniform => exact measurable_subtype_coe.comp ht

theorem measurable_run_value (p : Prog c Γ τ) {G : Point d → Point d} (hG : Measurable G)
    {input : Ω → Inputs d c} {env : Ω → Env d Γ} {tape : Ω → Tape d p}
    (hc : ∀ j, Measurable (fun ω => (input ω).coefficient j))
    (hx : Measurable (fun ω => (input ω).center))
    (hp : Measurable (fun ω => (input ω).momentum))
    (he : ∀ τ (r : Ref Γ τ), Measurable (fun ω => env ω r)) (ht : Measurable tape) :
    Measurable (fun ω => (run p G (input ω) (env ω) (tape ω)).value) := by
  induction p with
  | ret r => exact he _ r
  | step origin instr next ih =>
    apply ih
    · exact fun _ r => measurable_cons (measurable_instr origin instr hG hc hx hp he ht.fst) he r
    · exact ht.snd
  | batch origin children next ihc ihn =>
    apply ihn
    · exact fun _ r => measurable_prepend
        (fun j => ihc j he ((measurable_pi_apply j).comp ht.fst)) he r
    · exact ht.snd

/-- The output of the closed interpreter, with the original momentum retained
as the second external input and the entire mixed tape supplied verbatim. -/
def output (p : Program c .point) (coeff : Fin c → ℝ) (G : Point d → Point d)
    (z : (Point d × Point d) × Tape d p) : Point d :=
  (run p G ⟨coeff, z.1.1, z.1.2⟩ Env.empty z.2).value

theorem measurable_output (p : Program c .point) (coeff : Fin c → ℝ)
    {G : Point d → Point d} (hG : Measurable G) : Measurable (output p coeff G) := by
  unfold output
  apply measurable_run_value (Ω := (Point d × Point d) × Tape d p) p hG
    (input := fun (z : (Point d × Point d) × Tape d p) => ⟨coeff,z.1.1,z.1.2⟩)
    (env := fun _ => Env.empty) (tape := Prod.snd) (fun _ => measurable_const)
    measurable_fst.fst measurable_fst.snd
  · intro τ r
    exact nomatch r
  · exact measurable_snd

/-- Full instruction tape, not a Gaussian replacement of the residual tape. -/
def fresh (p : Program c .point) :
    Kernel (Point d × Point d) ((Point d × Point d) × Tape d p) :=
  (Kernel.id : Kernel (Point d × Point d) _) ×ₖ
    Kernel.const (Point d × Point d) (tapeLaw d p)

instance fresh_markov (p : Program c .point) : IsMarkovKernel (fresh (d := d) p) := by
  unfold fresh
  infer_instance

/-- The actual executed program kernel. -/
def executed (p : Program c .point) (coeff : Fin c → ℝ) (G : Point d → Point d) :
    Kernel (Point d × Point d) (Point d) :=
  (fresh p).map (output p coeff G)

theorem executed_markov (p : Program c .point) (coeff : Fin c → ℝ)
    {G : Point d → Point d} (hG : Measurable G) :
    IsMarkovKernel (executed p coeff G) :=
  Kernel.IsMarkovKernel.map _ (measurable_output p coeff hG)

/-- In particular the kernel of every constructed precision program is Markov;
this does not assert its accuracy or identify its retained joint law. -/
def dataKernel (e : ExecutableData) (G : Point d → Point d) :
    Kernel (Point d × Point d) (Point d) := executed e.program e.coefficient G

theorem dataKernel_markov (e : ExecutableData) {G : Point d → Point d}
    (hG : Measurable G) : IsMarkovKernel (dataKernel e G) :=
  executed_markov e.program e.coefficient hG

end AcceleratedLogConcave.Probability.ExecutableKernel
