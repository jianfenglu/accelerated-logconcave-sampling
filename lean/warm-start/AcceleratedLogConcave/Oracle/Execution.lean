import AcceleratedLogConcave.Oracle.Syntax
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Exact fixed-tape execution of finite original-gradient programs

The tape type follows the finite program structurally. Every draw has exactly one
supplied datum, and sibling programs have distinct product components. There is
no default randomness, partial lookup, dynamic cursor, or hidden oracle state.
The semantics executes every instruction and every batch child. This is an
exact-real operational model, not a finite-bit runtime or a sampling-kernel claim.
-/

namespace AcceleratedLogConcave.Oracle

/-- Public coefficients and explicit supplied inputs. The warm center/momentum
may have an oracle-dependent input law; the coefficient table must ultimately
be selected from public parameters before the potential is quantified. -/
structure Inputs (d c : ℕ) where
  coefficient : Fin c → ℝ
  center : Point d
  momentum : Point d

/-- Uniform endpoints are included; counting does not use a probability law. -/
abbrev UniformValue := Set.Icc (0 : ℝ) 1

/-- Exact local tape. A draw needs its datum; a non-draw has no random input. -/
def Instr.Tape (d : ℕ) : Instr c Γ τ → Type
  | .gaussian => Point d
  | .uniform => UniformValue
  | _ => PUnit

/-- The whole fixed tape has precisely the structural slices used by execution.
No absent coordinate can be silently filled. Freshness here means distinct
slots; probabilistic independence requires a separate product-law theorem. -/
def Tape (d : ℕ) : Prog c Γ τ → Type
  | .ret _ => PUnit
  | .step _ instr next => instr.Tape d × Tape d next
  | .batch _ children next => (∀ j, Tape d (children j)) × Tape d next

/-- Every primitive has its fixed total mathematical interpretation. Inverse
at zero and square root at negative inputs use Lean's total real operations;
source-domain validity is a separate compiler obligation. -/
noncomputable def evalPure (p : Pure c Γ τ) (coeff : Fin c → ℝ)
    (ρ : Env d Γ) : Ty.denote d τ :=
  match p with
  | .publicScalar j => coeff j
  | .rational q => (q : ℝ)
  | .add x y =>
      let a : ℝ := ρ x
      let b : ℝ := ρ y
      a + b
  | .mul x y =>
      let a : ℝ := ρ x
      let b : ℝ := ρ y
      a * b
  | .neg x =>
      let a : ℝ := ρ x
      (-a)
  | .inv x =>
      let a : ℝ := ρ x
      Inv.inv (α := ℝ) a
  | .sqrt x => Real.sqrt (ρ x)
  | .zero => (0 : Point d)
  | .vadd x y =>
      let a : Point d := ρ x
      let b : Point d := ρ y
      a + b
  | .smul a x =>
      let scalar : ℝ := ρ a
      let point : Point d := ρ x
      scalar • point

/-- A Gaussian event is one block of physical dimension `d`, even for `d = 0`.
Gradient events retain both the query point and its original-gradient answer. -/
inductive Event (d : ℕ) where
  | gradient : Origin → Point d → Point d → Event d
  | gaussian : Origin → Event d
  | uniform : Origin → Event d

/-- Erase values but retain event kind and source provenance. -/
def Event.erase : Event d → EventKind × Origin
  | .gradient origin _ _ => (.gradient, origin)
  | .gaussian origin => (.gaussian, origin)
  | .uniform origin => (.uniform, origin)

/-- A provenance prefix changes neither an oracle query nor its answer. -/
def Event.withPrefix (pref : Origin) : Event d → Event d
  | .gradient origin x a => .gradient (pref ++ origin) x a
  | .gaussian origin => .gaussian (pref ++ origin)
  | .uniform origin => .uniform (pref ++ origin)

/-- Explicit dimension metadata for each Gaussian block. -/
def Event.gaussianDimension : Event d → Option ℕ
  | .gaussian _ => some d
  | _ => none

/-- A result has an output and the actual executed event transcript, not a cost
correctness field. The relation to syntax counts is proved in `Oracle.Work`. -/
structure Result (d : ℕ) (τ : Ty) where
  value : Ty.denote d τ
  trace : List (Event d)

/-- Only the `grad` case applies `G`. Every random datum comes from the exact
instruction tape. No functions supplied by a compiler interpret pure opcodes. -/
noncomputable def evalInstr (origin : Origin) (instr : Instr c Γ τ)
    (G : Point d → Point d) (i : Inputs d c) (ρ : Env d Γ)
    (ω : instr.Tape d) : Result d τ :=
  match instr with
  | .pure p => ⟨evalPure p i.coefficient ρ, []⟩
  | .center => ⟨i.center, []⟩
  | .momentum => ⟨i.momentum, []⟩
  | .grad r =>
      let x := ρ r
      let answer := G x
      ⟨answer, [.gradient origin x answer]⟩
  | .gaussian => ⟨ω, [.gaussian origin]⟩
  | .uniform => ⟨ω.val, [.uniform origin]⟩

/-- Interpret all instructions. At a batch, all children receive the identical
pre-layer environment and their own exact tape slices. Their outputs are stored
in ascending `Fin n` order before the continuation. Every child trace is retained,
including children whose result is unused or later multiplied by zero. -/
noncomputable def run (p : Prog c Γ τ) (G : Point d → Point d)
    (i : Inputs d c) (ρ : Env d Γ) (ω : Tape d p) : Result d τ :=
  match p with
  | .ret r => ⟨ρ r, []⟩
  | .step origin instr next =>
      let first := evalInstr origin instr G i ρ ω.1
      let tail := run next G i (Env.cons first.value ρ) ω.2
      ⟨tail.value, first.trace ++ tail.trace⟩
  | .batch origin children next =>
      let results := fun j => run (children j) G i ρ (ω.1 j)
      let tail := run next G i (Env.prepend (fun j => (results j).value) ρ) ω.2
      ⟨tail.value,
        ((List.ofFn fun j => (results j).trace).flatten ++ tail.trace).map
          (Event.withPrefix origin)⟩

/-- Typed structural identities of random slots. The constructors distinguish
head/tail and every batch child, independently of equal numerical tape values. -/
inductive TapeSlot : {Γ : Ctx} → {τ : Ty} → Prog c Γ τ → Type where
  | gaussian (origin : Origin) (next : Prog c (.point :: Γ) τ) :
      TapeSlot (.step origin .gaussian next)
  | uniform (origin : Origin) (next : Prog c (.scalar :: Γ) τ) :
      TapeSlot (.step origin .uniform next)
  | stepNext (origin : Origin) (instr : Instr c Γ σ) {next : Prog c (σ :: Γ) τ} :
      TapeSlot next → TapeSlot (.step origin instr next)
  | batchChild (origin : Origin) (children : Fin n → Prog c Γ .point)
      (next : Prog c (List.replicate n .point ++ Γ) τ) (j : Fin n) :
      TapeSlot (children j) → TapeSlot (.batch origin children next)
  | batchNext (origin : Origin) (children : Fin n → Prog c Γ .point)
      {next : Prog c (List.replicate n .point ++ Γ) τ} :
      TapeSlot next → TapeSlot (.batch origin children next)

/-- Values returned by a typed slot read; no random value can be fabricated by
the reader. Each slot constructor determines which summand is returned. -/
abbrev RandomValue (d : ℕ) := Point d ⊕ UniformValue

/-- Read precisely the structural product component named by a tape slot. -/
def Tape.read {p : Prog c Γ τ} (ω : Tape d p) (s : TapeSlot p) : RandomValue d :=
  match s with
  | .gaussian _ _ => .inl ω.1
  | .uniform _ _ => .inr ω.1
  | .stepNext _ _ s => Tape.read ω.2 s
  | .batchChild _ _ _ j s => Tape.read (ω.1 j) s
  | .batchNext _ _ s => Tape.read ω.2 s

/-- Different synchronous children have disjoint structural random slots. -/
theorem TapeSlot.batchChild_ne_of_ne (origin : Origin)
    (children : Fin n → Prog c Γ .point)
    (next : Prog c (List.replicate n .point ++ Γ) τ)
    {j k : Fin n} (h : j ≠ k) (s : TapeSlot (children j))
    (t : TapeSlot (children k)) :
    TapeSlot.batchChild origin children next j s ≠
      TapeSlot.batchChild origin children next k t := by
  intro he
  cases he
  exact h rfl

/-- No child random slot aliases a continuation random slot. -/
theorem TapeSlot.batchChild_ne_batchNext (origin : Origin)
    (children : Fin n → Prog c Γ .point)
    (next : Prog c (List.replicate n .point ++ Γ) τ)
    (j : Fin n) (s : TapeSlot (children j)) (t : TapeSlot next) :
    TapeSlot.batchChild origin children next j s ≠
      TapeSlot.batchNext origin children t := by
  intro he
  cases he

end AcceleratedLogConcave.Oracle
