import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Finite original-gradient program syntax

This is a bounded operational foundation for W10, not the recursive source
compiler. Instructions have a closed primitive grammar and refer only to values
already stored. A batch gives each child the same pre-batch environment; child
programs may use their own earlier gradient replies. Every child is executed,
including suppliers whose values or eventual shift contributions are zero.

Origins record source provenance only. They do not assert independence,
read-access restrictions, rank decrease, shift support, or compiler correctness.
Public coefficient tables and programs must ultimately be chosen independently
of the unknown potential; fixed syntax alone does not establish that uniformity.
-/

namespace AcceleratedLogConcave.Oracle

/-- The physical vector carrier, including the zero-dimensional case. -/
abbrev Point (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The two stored-value types required by the finite affine program foundation. -/
inductive Ty where
  | scalar
  | point
  deriving DecidableEq, Repr

/-- Interpret a stored-value type in physical dimension `d`. -/
def Ty.denote (d : ℕ) : Ty → Type
  | .scalar => ℝ
  | .point => Point d

/-- A context lists already stored values, most recently prepended first. -/
abbrev Ctx := List Ty

/-- A typed reference into the existing store; no forward references exist. -/
inductive Ref : Ctx → Ty → Type where
  | here : Ref (τ :: Γ) τ
  | there : Ref Γ τ → Ref (σ :: Γ) τ

/-- A value environment, with a value for every well-typed reference. -/
abbrev Env (d : ℕ) (Γ : Ctx) := ∀ {τ}, Ref Γ τ → Ty.denote d τ

namespace Env

/-- The external entry point has no unexplained initial stored values. -/
def empty : Env d [] := fun r => nomatch r

/-- Store one computed value. Reading it later does not execute its producer. -/
def cons (value : Ty.denote d τ) (env : Env d Γ) : Env d (τ :: Γ) :=
  fun r => match r with
    | .here => value
    | .there previous => env previous

@[simp] theorem cons_here (value : Ty.denote d τ) (env : Env d Γ) :
    cons value env Ref.here = value := rfl

@[simp] theorem cons_there (value : Ty.denote d τ) (env : Env d Γ)
    (r : Ref Γ σ) : cons value env (Ref.there r) = env r := rfl

/-- Store batch outputs in ascending order: output zero occupies the first slot. -/
def prepend : {n : ℕ} → (Fin n → Point d) → Env d Γ →
    Env d (List.replicate n .point ++ Γ)
  | 0, _, env => env
  | _n + 1, values, env =>
      cons (d := d) (τ := .point) (values 0) (prepend (fun i => values i.succ) env)

@[simp] theorem prepend_zero (values : Fin 0 → Point d) (env : Env d Γ)
    (r : Ref Γ τ) : prepend values env r = env r := rfl

@[simp] theorem prepend_succ (values : Fin (n + 1) → Point d) (env : Env d Γ)
    (r : Ref (List.replicate (n + 1) .point ++ Γ) τ) :
    prepend values env r =
      cons (d := d) (τ := .point) (values 0) (prepend (fun i => values i.succ) env) r := rfl

end Env

/-- Which source block owns a provenance frame. This does not change execution. -/
inductive BlockRole where
  | mean
  | privateSampling
  | publicSampling
  deriving DecidableEq, Repr

/-- The source site within a block; this does not discount inactive suppliers. -/
inductive SiteRole where
  | setup
  | mainLayer
  | activeFinal
  | samplingLayer
  | samplingFinal
  deriving DecidableEq, Repr

/-- Finite source metadata, not a semantic certificate or a unique execution ID. -/
structure Frame where
  block : BlockRole
  site : SiteRole
  occurrence : ℕ
  layer : ℕ
  node : ℕ
  deriving DecidableEq, Repr

/-- Nested source provenance. Distinct executions may carry identical metadata. -/
abbrev Origin := List Frame

/-- Closed deterministic primitives. There is no arbitrary function constructor. -/
inductive Pure (c : ℕ) (Γ : Ctx) : Ty → Type where
  | publicScalar : Fin c → Pure c Γ .scalar
  | rational : ℚ → Pure c Γ .scalar
  | add : Ref Γ .scalar → Ref Γ .scalar → Pure c Γ .scalar
  | mul : Ref Γ .scalar → Ref Γ .scalar → Pure c Γ .scalar
  | neg : Ref Γ .scalar → Pure c Γ .scalar
  | inv : Ref Γ .scalar → Pure c Γ .scalar
  | sqrt : Ref Γ .scalar → Pure c Γ .scalar
  | zero : Pure c Γ .point
  | vadd : Ref Γ .point → Ref Γ .point → Pure c Γ .point
  | smul : Ref Γ .scalar → Ref Γ .point → Pure c Γ .point

/-- Instructions. Only `grad` may consult the supplied original-gradient oracle.
Draw instructions consume fresh fixed-tape data; references reuse stored draws. -/
inductive Instr (c : ℕ) (Γ : Ctx) : Ty → Type where
  | pure : Pure c Γ τ → Instr c Γ τ
  | center : Instr c Γ .point
  | momentum : Instr c Γ .point
  | grad : Ref Γ .point → Instr c Γ .point
  | gaussian : Instr c Γ .point
  | uniform : Instr c Γ .scalar

/-- Finite syntax: continuations are syntax values, not reply-dependent code.
Each batch child reads the same prior store, then all outputs precede `next`. -/
inductive Prog (c : ℕ) : Ctx → Ty → Type where
  | ret : Ref Γ τ → Prog c Γ τ
  | step : Origin → Instr c Γ σ → Prog c (σ :: Γ) τ → Prog c Γ τ
  | batch {n : ℕ} : Origin → (Fin n → Prog c Γ .point) →
      Prog c (List.replicate n .point ++ Γ) τ → Prog c Γ τ

/-- An externally admissible entry point has an empty initial store. -/
abbrev Program (c : ℕ) (τ : Ty) := Prog c [] τ

/-- Observable instruction categories. Only `gradient` contributes public work. -/
inductive EventKind where
  | gradient
  | gaussian
  | uniform
  deriving DecidableEq, Repr

namespace Instr

/-- A pure/input instruction emits no event. -/
def eventKind : Instr c Γ τ → Option EventKind
  | .pure _ => none
  | .center => none
  | .momentum => none
  | .grad _ => some .gradient
  | .gaussian => some .gaussian
  | .uniform => some .uniform

/-- The number of original-gradient calls made by one instruction. -/
def queryCount : Instr c Γ τ → ℕ
  | .grad _ => 1
  | _ => 0

/-- The number of fresh `d`-dimensional Gaussian blocks consumed. -/
def gaussianCount : Instr c Γ τ → ℕ
  | .gaussian => 1
  | _ => 0

/-- The number of fresh scalar uniform coordinates consumed. -/
def uniformCount : Instr c Γ τ → ℕ
  | .uniform => 1
  | _ => 0

/-- The event shape of an instruction with its source provenance. -/
def staticTrace (origin : Origin) (instr : Instr c Γ τ) : List (EventKind × Origin) :=
  instr.eventKind.toList.map (fun kind => (kind, origin))

end Instr

/-- Raw tape demand; Gaussian blocks are distinct from scalar coordinates. -/
structure TapeShape where
  gaussianBlocks : ℕ
  uniformScalars : ℕ
  deriving DecidableEq, Repr

/-- Fixed tape demand, summing every child, including unused suppliers. -/
def tapeShape : Prog c Γ τ → TapeShape
  | .ret _ => ⟨0, 0⟩
  | .step _ instr next =>
      ⟨instr.gaussianCount + (tapeShape next).gaussianBlocks,
        instr.uniformCount + (tapeShape next).uniformScalars⟩
  | .batch _ children next =>
      ⟨(List.ofFn fun i => (tapeShape (children i)).gaussianBlocks).sum +
          (tapeShape next).gaussianBlocks,
        (List.ofFn fun i => (tapeShape (children i)).uniformScalars).sum +
          (tapeShape next).uniformScalars⟩

/-- Prefix a batch's origin to each child/continuation event. -/
def prefixStaticTrace (origin : Origin) (events : List (EventKind × Origin)) :
    List (EventKind × Origin) :=
  events.map fun event => (event.1, origin ++ event.2)

/-- The fixed event sequence in ascending child order, followed by continuation.
Origins do not affect whether any instruction executes or contributes work. -/
def staticTrace : Prog c Γ τ → List (EventKind × Origin)
  | .ret _ => []
  | .step origin instr next => instr.staticTrace origin ++ staticTrace next
  | .batch origin children next =>
      prefixStaticTrace origin
        ((List.ofFn fun i => staticTrace (children i)).flatten ++ staticTrace next)

end AcceleratedLogConcave.Oracle
