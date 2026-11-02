import AcceleratedLogConcave.Oracle.AffineLowering
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Sigma

/-! Closed presampling and replay of all auxiliary Gaussian slots. Probability
laws and source covariance matrices are separate obligations. -/
namespace AcceleratedLogConcave.Oracle
namespace TapeLowering

/-- The Gaussian datum supplied to one instruction, when present. -/
def InstrGaussianSlot : Instr c Γ τ → Type
  | .gaussian => PUnit
  | _ => PEmpty

instance instrGaussianSlotFintype (i : Instr c Γ τ) : Fintype (InstrGaussianSlot i) := by
  cases i <;> dsimp [InstrGaussianSlot] <;> infer_instance

/-- Actual structural Gaussian positions, including repeated equal-code children. -/
def GaussianSlot : Prog c Γ τ → Type
  | .ret _ => PEmpty
  | .step _ i next => InstrGaussianSlot i ⊕ GaussianSlot next
  | .batch _ children next => (Σ j, GaussianSlot (children j)) ⊕ GaussianSlot next

instance gaussianSlotFintype (p : Prog c Γ τ) : Fintype (GaussianSlot p) :=
  match p with
  | .ret _ => inferInstanceAs (Fintype PEmpty)
  | .step _ i next => by
      letI := instrGaussianSlotFintype i
      letI := gaussianSlotFintype next
      exact inferInstanceAs (Fintype (InstrGaussianSlot i ⊕ GaussianSlot next))
  | .batch _ children next => by
      letI := fun j => gaussianSlotFintype (children j)
      letI := gaussianSlotFintype next
      exact inferInstanceAs (Fintype ((Σ j, GaussianSlot (children j)) ⊕ GaussianSlot next))

/-- The nongeneric residual tape still includes every uniform datum. -/
def InstrResidualTape : Instr c Γ τ → Type
  | .uniform => UniformValue
  | _ => PUnit

/-- Remove Gaussian data, retaining uniform and unit coordinates. -/
def ResidualTape : Prog c Γ τ → Type
  | .ret _ => PUnit
  | .step _ i next => InstrResidualTape i × ResidualTape next
  | .batch _ children next => (∀ j, ResidualTape (children j)) × ResidualTape next

private def instrGaussian (i : Instr c Γ τ) (ω : i.Tape d) : InstrGaussianSlot i → Point d :=
  match i with
  | .gaussian => fun _ => ω
  | .pure _ | .center | .momentum | .grad _ | .uniform => fun s => nomatch s

private def instrResidual (i : Instr c Γ τ) (ω : i.Tape d) : InstrResidualTape i :=
  match i with
  | .uniform => ω
  | .pure _ | .center | .momentum | .grad _ | .gaussian => PUnit.unit

private def instrJoin (i : Instr c Γ τ) (z : InstrGaussianSlot i → Point d)
    (υ : InstrResidualTape i) : i.Tape d :=
  match i with
  | .gaussian => z PUnit.unit
  | .uniform => υ
  | .pure _ | .center | .momentum | .grad _ => PUnit.unit

/-- Extract the exact Gaussian and uniform coordinates from the source tape. -/
def splitTape (p : Prog c Γ τ) (ω : Tape d p) :
    (GaussianSlot p → Point d) × ResidualTape p :=
  match p with
  | .ret _ => ((fun s => nomatch s), PUnit.unit)
  | .step _ i next =>
      let tail := splitTape next ω.2
      (Sum.elim (instrGaussian i ω.1) tail.1, (instrResidual i ω.1, tail.2))
  | .batch _ children next =>
      let cs := fun j => splitTape (children j) (ω.1 j)
      let tail := splitTape next ω.2
      (Sum.elim (fun s => (cs s.1).1 s.2) tail.1, (fun j => (cs j).2, tail.2))

/-- Reconstruct every source tape from its Gaussian array and residual coordinates. -/
def joinTape (p : Prog c Γ τ) (z : GaussianSlot p → Point d)
    (υ : ResidualTape p) : Tape d p :=
  match p with
  | .ret _ => PUnit.unit
  | .step _ i next =>
      (instrJoin i (fun s => z (.inl s)) υ.1,
       joinTape next (fun s => z (.inr s)) υ.2)
  | .batch _ children next =>
      (fun j => joinTape (children j) (fun s => z (.inl ⟨j,s⟩)) (υ.1 j),
       joinTape next (fun s => z (.inr s)) υ.2)

private theorem instrJoin_split (i : Instr c Γ τ) (ω : i.Tape d) :
    instrJoin i (instrGaussian i ω) (instrResidual i ω) = ω := by
  cases i <;> rfl

private theorem instrGaussian_join (i : Instr c Γ τ) (z : InstrGaussianSlot i → Point d)
    (υ : InstrResidualTape i) : instrGaussian i (instrJoin i z υ) = z := by
  cases i <;> funext s
  all_goals cases s
  rfl

private theorem instrResidual_join (i : Instr c Γ τ) (z : InstrGaussianSlot i → Point d)
    (υ : InstrResidualTape i) : instrResidual i (instrJoin i z υ) = υ := by
  cases i <;> rfl

@[simp] theorem joinTape_splitTape (p : Prog c Γ τ) (ω : Tape d p) :
    joinTape p (splitTape p ω).1 (splitTape p ω).2 = ω := by
  induction p with
  | ret r => rfl
  | step origin i next ih =>
      simp only [splitTape, joinTape, Sum.elim_inl, Sum.elim_inr, instrJoin_split, ih]
      rfl
  | batch origin children next ihc ihn =>
      simp only [splitTape, joinTape, Sum.elim_inl, Sum.elim_inr, ihc, ihn]
      rfl

@[simp] theorem splitTape_joinTape (p : Prog c Γ τ) (z : GaussianSlot p → Point d)
    (υ : ResidualTape p) : splitTape p (joinTape p z υ) = (z,υ) := by
  induction p with
  | ret r =>
      simp only [splitTape]
      apply Prod.ext
      · funext s; cases s
      · cases υ; rfl
  | step origin i next ih =>
      simp only [splitTape, joinTape, ih, instrGaussian_join, instrResidual_join]
      apply Prod.ext
      · funext s
        cases s <;> rfl
      · rfl
  | batch origin children next ihc ihn =>
      simp only [splitTape, joinTape, ihc, ihn]
      apply Prod.ext
      · funext s
        cases s with
        | inl s => cases s; rfl
        | inr s => rfl
      · rfl

/-- Complete source tape routing, not just an injection of chosen inputs. -/
def splitGaussianTape (d : ℕ) (p : Prog c Γ τ) :
    Tape d p ≃ ((GaussianSlot p → Point d) × ResidualTape p) where
  toFun := splitTape p
  invFun := fun a => joinTape p a.1 a.2
  left_inv := joinTape_splitTape p
  right_inv := fun a => splitTape_joinTape p a.1 a.2

@[simp] theorem card_instrGaussianSlot (i : Instr c Γ τ) :
    Fintype.card (InstrGaussianSlot i) = i.gaussianCount := by
  cases i <;> simp [InstrGaussianSlot, Instr.gaussianCount, Fintype.card_pempty]

@[simp] theorem card_gaussianSlot (p : Prog c Γ τ) :
    Fintype.card (GaussianSlot p) = (tapeShape p).gaussianBlocks := by
  induction p with
  | ret r =>
      dsimp only [GaussianSlot, gaussianSlotFintype, tapeShape]
      exact Fintype.card_pempty
  | step origin i next ih =>
      dsimp only [GaussianSlot, gaussianSlotFintype, tapeShape]
      erw [Fintype.card_sum, card_instrGaussianSlot, ih]
  | batch origin children next ihc ihn =>
      dsimp only [GaussianSlot, gaussianSlotFintype, tapeShape]
      erw [Fintype.card_sum, Fintype.card_sigma]
      simp only [ihc, ihn, Fin.sum_ofFn]

/-- A fixed finite enumeration depends on syntax alone, never on an oracle. -/
noncomputable def gaussianSlotEquiv (p : Prog c Γ τ) :
    GaussianSlot p ≃ Fin (tapeShape p).gaussianBlocks :=
  Fintype.equivFinOfCardEq (card_gaussianSlot p)

/-- Replay a source program against stored auxiliary Gaussian coordinates. -/
def replayGaussian (κ : Fin c → Fin c') (p : Prog c Γ τ) (f : RefMap Γ Δ)
    (slots : GaussianSlot p → Ref Δ .point) (center momentum : Ref Δ .point) :
    Prog c' Δ τ :=
  match p with
  | .ret r => .ret (f r)
  | .step origin (.pure a) next =>
      .step origin (.pure (a.reindex κ f))
        (replayGaussian κ next f.lift (fun s => .there (slots (.inr s)))
          (.there center) (.there momentum))
  | .step _ .center next =>
      replayGaussian κ next (f.bind center) (fun s => slots (.inr s)) center momentum
  | .step _ .momentum next =>
      replayGaussian κ next (f.bind momentum) (fun s => slots (.inr s)) center momentum
  | .step origin (.grad r) next =>
      .step origin (.grad (f r))
        (replayGaussian κ next f.lift (fun s => .there (slots (.inr s)))
          (.there center) (.there momentum))
  | .step _ .gaussian next =>
      replayGaussian κ next (f.bind (slots (.inl PUnit.unit)))
        (fun s => slots (.inr s)) center momentum
  | .step origin .uniform next =>
      .step origin .uniform
        (replayGaussian κ next f.lift (fun s => .there (slots (.inr s)))
          (.there center) (.there momentum))
  | .batch origin children next =>
      .batch origin
        (fun j => replayGaussian κ (children j) f (fun s => slots (.inl ⟨j,s⟩))
          center momentum)
        (replayGaussian κ next (f.liftMany _) (fun s => RefMap.shiftMany _ (slots (.inr s)))
          (RefMap.shiftMany _ center) (RefMap.shiftMany _ momentum))

/-- Route every nongeneric random datum to its actual replay instruction. -/
def replayTape (κ : Fin c → Fin c') (p : Prog c Γ τ) (f : RefMap Γ Δ)
    (slots : GaussianSlot p → Ref Δ .point) (center momentum : Ref Δ .point)
    (υ : ResidualTape p) : Tape d (replayGaussian κ p f slots center momentum) :=
  match p with
  | .ret _ => υ
  | .step _ (.pure _) next =>
      (υ.1, replayTape κ next f.lift (fun s => .there (slots (.inr s)))
        (.there center) (.there momentum) υ.2)
  | .step _ .center next =>
      replayTape κ next (f.bind center) (fun s => slots (.inr s)) center momentum υ.2
  | .step _ .momentum next =>
      replayTape κ next (f.bind momentum) (fun s => slots (.inr s)) center momentum υ.2
  | .step _ (.grad _) next =>
      (υ.1, replayTape κ next f.lift (fun s => .there (slots (.inr s)))
        (.there center) (.there momentum) υ.2)
  | .step _ .gaussian next =>
      replayTape κ next (f.bind (slots (.inl PUnit.unit)))
        (fun s => slots (.inr s)) center momentum υ.2
  | .step _ .uniform next =>
      (υ.1, replayTape κ next f.lift (fun s => .there (slots (.inr s)))
        (.there center) (.there momentum) υ.2)
  | .batch _ children next =>
      (fun j => replayTape κ (children j) f (fun s => slots (.inl ⟨j,s⟩))
          center momentum (υ.1 j),
       replayTape κ next (f.liftMany _) (fun s => RefMap.shiftMany _ (slots (.inr s)))
          (RefMap.shiftMany _ center) (RefMap.shiftMany _ momentum) υ.2)

/-- Restore the exact residual coordinates from every target replay tape. -/
def restoreReplayTape (κ : Fin c → Fin c') (p : Prog c Γ τ) (f : RefMap Γ Δ)
    (slots : GaussianSlot p → Ref Δ .point) (center momentum : Ref Δ .point)
    (ω : Tape d (replayGaussian κ p f slots center momentum)) : ResidualTape p :=
  match p with
  | .ret _ => ω
  | .step _ (.pure _) next =>
      (ω.1, restoreReplayTape κ next f.lift (fun s => .there (slots (.inr s)))
        (.there center) (.there momentum) ω.2)
  | .step _ .center next =>
      (PUnit.unit, restoreReplayTape κ next (f.bind center)
        (fun s => slots (.inr s)) center momentum ω)
  | .step _ .momentum next =>
      (PUnit.unit, restoreReplayTape κ next (f.bind momentum)
        (fun s => slots (.inr s)) center momentum ω)
  | .step _ (.grad _) next =>
      (ω.1, restoreReplayTape κ next f.lift (fun s => .there (slots (.inr s)))
        (.there center) (.there momentum) ω.2)
  | .step _ .gaussian next =>
      (PUnit.unit, restoreReplayTape κ next (f.bind (slots (.inl PUnit.unit)))
        (fun s => slots (.inr s)) center momentum ω)
  | .step _ .uniform next =>
      (ω.1, restoreReplayTape κ next f.lift (fun s => .there (slots (.inr s)))
        (.there center) (.there momentum) ω.2)
  | .batch _ children next =>
      (fun j => restoreReplayTape κ (children j) f (fun s => slots (.inl ⟨j,s⟩))
          center momentum (ω.1 j),
       restoreReplayTape κ next (f.liftMany _) (fun s => RefMap.shiftMany _ (slots (.inr s)))
          (RefMap.shiftMany _ center) (RefMap.shiftMany _ momentum) ω.2)

theorem replayTape_restoreReplayTape (κ : Fin c → Fin c') (p : Prog c Γ τ)
    (f : RefMap Γ Δ) (slots : GaussianSlot p → Ref Δ .point)
    (center momentum : Ref Δ .point)
    (ω : Tape d (replayGaussian κ p f slots center momentum)) :
    replayTape κ p f slots center momentum
      (restoreReplayTape κ p f slots center momentum ω) = ω := by
  induction p generalizing Δ with
  | ret _ => rfl
  | step origin instr next ih =>
      cases instr <;> simp only [replayTape, restoreReplayTape]
      all_goals first
      | exact ih _ _ _ _ _
      | (simp only [ih]; rfl)
  | batch origin children next ihc ihn =>
      simp only [replayTape, restoreReplayTape, ihc, ihn]
      rfl

theorem restoreReplayTape_replayTape {d : ℕ} (κ : Fin c → Fin c') (p : Prog c Γ τ)
    (f : RefMap Γ Δ) (slots : GaussianSlot p → Ref Δ .point)
    (center momentum : Ref Δ .point) (υ : ResidualTape p) :
    restoreReplayTape (d := d) κ p f slots center momentum
      (replayTape κ p f slots center momentum υ) = υ := by
  induction p generalizing Δ with
  | ret _ => rfl
  | step origin instr next ih =>
      cases instr <;> simp only [replayTape, restoreReplayTape, ih]
      all_goals apply Prod.ext
      all_goals rfl
  | batch origin children next ihc ihn =>
      simp only [replayTape, restoreReplayTape, ihc, ihn]
      rfl

/-- All target replay executions are represented, including every uniform slice. -/
def replayTapeEquiv (κ : Fin c → Fin c') (p : Prog c Γ τ)
    (f : RefMap Γ Δ) (slots : GaussianSlot p → Ref Δ .point)
    (center momentum : Ref Δ .point) :
    ResidualTape p ≃ Tape d (replayGaussian κ p f slots center momentum) where
  toFun := replayTape κ p f slots center momentum
  invFun := restoreReplayTape κ p f slots center momentum
  left_inv := restoreReplayTape_replayTape κ p f slots center momentum
  right_inv := replayTape_restoreReplayTape κ p f slots center momentum


/-- Gaussian events alone are removed by replay. Queries and uniform draws remain. -/
def keepNonGaussian : Event d → Bool
  | .gaussian _ => false
  | .gradient _ _ _ | .uniform _ => true

def withoutGaussian (r : Result d τ) : Result d τ :=
  ⟨r.value, r.trace.filter keepNonGaussian⟩

@[simp] theorem keepNonGaussian_prefix (o : Origin) (e : Event d) :
    keepNonGaussian (e.withPrefix o) = keepNonGaussian e := by cases e <;> rfl

@[simp] theorem filterNonGaussian_prefix (o : Origin) (xs : List (Event d)) :
    (xs.map (Event.withPrefix o)).filter keepNonGaussian =
      (xs.filter keepNonGaussian).map (Event.withPrefix o) := by
  simp only [List.filter_map, Function.comp_def, keepNonGaussian_prefix]

/-- Exact replay: same values, queries, answers, order and non-Gaussian provenance. -/
theorem run_replayGaussian (κ : Fin c → Fin c') (p : Prog c Γ τ)
    (G : Point d → Point d) (i : Inputs d c) (i' : Inputs d c')
    (f : RefMap Γ Δ) (slots : GaussianSlot p → Ref Δ .point)
    (center momentum : Ref Δ .point) (ρ : Env d Γ) (ρ' : Env d Δ) (ω : Tape d p)
    (hc : ∀ j, i'.coefficient (κ j) = i.coefficient j)
    (he : ∀ {σ} (r : Ref Γ σ), ρ' (f r) = ρ r)
    (hx : ρ' center = i.center) (hp : ρ' momentum = i.momentum)
    (hs : ∀ s, ρ' (slots s) = (splitTape p ω).1 s) :
    run (replayGaussian κ p f slots center momentum) G i' ρ'
      (replayTape κ p f slots center momentum (splitTape p ω).2) =
      withoutGaussian (run p G i ρ ω) := by
  induction p generalizing Δ with
  | ret r => simp only [replayGaussian, replayTape, run, he, withoutGaussian, List.filter_nil]
  | step origin instr next ih =>
      cases instr with
      | pure a =>
          have hv := evalPure_reindex κ f a i.coefficient i'.coefficient ρ ρ' hc he
          have hr := ih f.lift (fun s => .there (slots (.inr s)))
            (.there center) (.there momentum)
            (Env.cons (evalPure a i.coefficient ρ) ρ)
            (Env.cons (evalPure a i.coefficient ρ) ρ') ω.2
            (env_lift f _ ρ ρ' he) hx hp (fun s => hs (.inr s))
          simpa only [replayGaussian, replayTape, splitTape, run, evalInstr, hv,
            List.nil_append, withoutGaussian] using hr
      | center =>
          have hr := ih (f.bind center) (fun s => slots (.inr s)) center momentum
            (Env.cons (d := d) (τ := .point) i.center ρ) ρ' ω.2
            (env_bind (d := d) f center i.center ρ ρ' he hx) hx hp
            (fun s => hs (.inr s))
          simpa only [replayGaussian, replayTape, splitTape, run, evalInstr,
            List.nil_append, withoutGaussian] using hr
      | momentum =>
          have hr := ih (f.bind momentum) (fun s => slots (.inr s)) center momentum
            (Env.cons (d := d) (τ := .point) i.momentum ρ) ρ' ω.2
            (env_bind (d := d) f momentum i.momentum ρ ρ' he hp) hx hp
            (fun s => hs (.inr s))
          simpa only [replayGaussian, replayTape, splitTape, run, evalInstr,
            List.nil_append, withoutGaussian] using hr
      | grad r =>
          have hr := ih f.lift (fun s => .there (slots (.inr s)))
            (.there center) (.there momentum)
            (Env.cons (d := d) (τ := .point) (G (ρ r)) ρ)
            (Env.cons (d := d) (τ := .point) (G (ρ r)) ρ') ω.2
            (env_lift f _ ρ ρ' he) hx hp (fun s => hs (.inr s))
          simp only [replayGaussian, replayTape, splitTape, run, evalInstr, he, hr,
            withoutGaussian, List.singleton_append, List.filter_cons, keepNonGaussian,
            ↓reduceIte]
      | gaussian =>
          have hg : ρ' (slots (.inl PUnit.unit)) = ω.1 := hs (.inl PUnit.unit)
          have hr := ih (f.bind (slots (.inl PUnit.unit))) (fun s => slots (.inr s))
            center momentum (Env.cons (d := d) (τ := .point) ω.1 ρ) ρ' ω.2
            (env_bind (d := d) f (slots (.inl PUnit.unit)) ω.1 ρ ρ' he hg)
            hx hp (fun s => hs (.inr s))
          simpa only [replayGaussian, replayTape, splitTape, run, evalInstr,
            withoutGaussian, List.singleton_append, List.filter_cons, keepNonGaussian,
            Bool.false_eq_true, ↓reduceIte] using hr
      | uniform =>
          have hr := ih f.lift (fun s => .there (slots (.inr s)))
            (.there center) (.there momentum)
            (Env.cons (d := d) (τ := .scalar) ω.1.val ρ)
            (Env.cons (d := d) (τ := .scalar) ω.1.val ρ') ω.2
            (env_lift f _ ρ ρ' he) hx hp (fun s => hs (.inr s))
          simp only [replayGaussian, replayTape, splitTape, instrResidual, run, evalInstr, hr,
            withoutGaussian, List.singleton_append, List.filter_cons, keepNonGaussian,
            ↓reduceIte]
  | batch origin children next ihc ihn =>
      have hc' : ∀ j,
          run (replayGaussian κ (children j) f (fun s => slots (.inl ⟨j,s⟩)) center momentum)
            G i' ρ' (replayTape κ (children j) f (fun s => slots (.inl ⟨j,s⟩))
              center momentum (splitTape (children j) (ω.1 j)).2) =
          withoutGaussian (run (children j) G i ρ (ω.1 j)) :=
        fun j => ihc j f (fun s => slots (.inl ⟨j,s⟩)) center momentum
          ρ ρ' (ω.1 j) he hx hp (fun s => hs (.inl ⟨j,s⟩))
      have hr := ihn (f.liftMany _) (fun s => RefMap.shiftMany _ (slots (.inr s)))
        (RefMap.shiftMany _ center) (RefMap.shiftMany _ momentum)
        (Env.prepend (fun j => (run (children j) G i ρ (ω.1 j)).value) ρ)
        (Env.prepend (fun j => (run (children j) G i ρ (ω.1 j)).value) ρ') ω.2
        (env_prepend_liftMany _ f _ ρ ρ' he)
        ((env_prepend_shiftMany _ _ ρ' center).trans hx)
        ((env_prepend_shiftMany _ _ ρ' momentum).trans hp)
        (fun s => (env_prepend_shiftMany _ _ ρ' (slots (.inr s))).trans (hs (.inr s)))
      simp only [replayGaussian, replayTape, splitTape, run, hc', withoutGaussian] at hr ⊢
      rw [hr]
      simp only [filterNonGaussian_prefix, List.filter_append,
        List.filter_flatten, List.map_ofFn, Function.comp_def]

/-- Presampling removes all hidden Gaussian instructions from replay. -/
theorem syntaxCount_replayGaussian (kind : EventKind) (κ : Fin c → Fin c')
    (p : Prog c Γ τ) (f : RefMap Γ Δ) (slots : GaussianSlot p → Ref Δ .point)
    (center momentum : Ref Δ .point) :
    syntaxCount kind (replayGaussian κ p f slots center momentum) =
      if kind = .gaussian then 0 else syntaxCount kind p := by
  cases kind <;> induction p generalizing Δ with
  | ret r => rfl
  | step origin i next ih =>
      cases i <;> simp [replayGaussian, syntaxCount, instructionCount, Instr.eventKind, ih]
  | batch origin children next ihc ihn =>
      simp [replayGaussian, syntaxCount, ihc, ihn]

open scoped BigOperators
open AffineLowering

/-- Gaussian-slot replay stated directly on a reconstructed source tape. -/
theorem run_replayGaussian_join (κ : Fin c → Fin c') (p : Prog c Γ τ)
    (G : Point d → Point d) (i : Inputs d c) (i' : Inputs d c')
    (f : RefMap Γ Δ) (slots : GaussianSlot p → Ref Δ .point)
    (center momentum : Ref Δ .point) (ρ : Env d Γ) (ρ' : Env d Δ)
    (Z : GaussianSlot p → Point d) (r : ResidualTape p)
    (hc : ∀ j, i'.coefficient (κ j) = i.coefficient j)
    (he : ∀ {σ} (a : Ref Γ σ), ρ' (f a) = ρ a)
    (hx : ρ' center = i.center) (hp : ρ' momentum = i.momentum)
    (hs : ∀ s, ρ' (slots s) = Z s) :
    run (replayGaussian κ p f slots center momentum) G i' ρ'
      (replayTape κ p f slots center momentum r) =
      withoutGaussian (run p G i ρ (joinTape p Z r)) := by
  have h := run_replayGaussian κ p G i i' f slots center momentum ρ ρ'
    (joinTape p Z r) hc he hx hp
    (by simpa only [splitTape_joinTape] using hs)
  simpa only [splitTape_joinTape] using h

abbrev inputCtx : Ctx := [.point, .point]
abbrev rawCtx (n : ℕ) : Ctx := List.replicate n .point ++ inputCtx
abbrev zeroCtx (n : ℕ) : Ctx := .point :: rawCtx n
abbrev replayCtx (n : ℕ) : Ctx := List.replicate n .point ++ zeroCtx n

/-- One actual raw Gaussian instruction; the returned reference reuses its value. -/
def rawDraw (origin : Origin) : Prog c inputCtx .point :=
  .step origin .gaussian (.ret .here)

/-- A literal dense matrix row over the one stored raw block. -/
def transformRow (c n : ℕ) (j : Fin n) : Prog (n*n+c) (zeroCtx n) .point :=
  affineRow [] .here (List.ofFn fun k => (matrixIndex c j k, .there (batchRef k)))

def compiledCenter (n : ℕ) : Ref (replayCtx n) .point :=
  RefMap.shiftMany n (.there (RefMap.shiftMany n (.there .here)))

def compiledMomentum (n : ℕ) : Ref (replayCtx n) .point :=
  RefMap.shiftMany n (.there (RefMap.shiftMany n .here))

/-- Replay reads the transformed rows, never the original raw blocks. -/
def replayBody (p : Program c τ) (e : GaussianSlot p ≃ Fin n) :
    Prog (n*n+c) (replayCtx n) τ :=
  replayGaussian (Fin.natAdd (n*n)) p (fun a => nomatch a)
    (fun s => batchRef (e s)) (compiledCenter n) (compiledMomentum n)

/-- Concrete setup, one raw batch, one pure matrix batch, then source replay. -/
def compileWith (p : Program c τ) (e : GaussianSlot p ≃ Fin n)
    (seedOrigin : Fin n → Origin) : Program (n*n+c) τ :=
  .step [] .center (.step [] .momentum
    (.batch [] (fun j => rawDraw (seedOrigin j))
      (.step [] (.pure .zero)
        (.batch [] (transformRow c n) (replayBody p e)))))

/-- Canonical code depends on syntax and provenance, never matrix entries or replies. -/
noncomputable def compileGaussian (p : Program c τ)
    (seedOrigin : Fin (tapeShape p).gaussianBlocks → Origin) :
    Program ((tapeShape p).gaussianBlocks * (tapeShape p).gaussianBlocks + c) τ :=
  compileWith p (gaussianSlotEquiv p) seedOrigin

noncomputable def transformedGaussian (T : Fin n → Fin n → ℝ)
    (Z : Fin n → Point d) (j : Fin n) : Point d := ∑ k, T j k • Z k

/-- The pure rows have unique unit-only tapes. -/
def transformRowTape (d c n : ℕ) (j : Fin n) : Tape d (transformRow c n j) :=
  rowTape d [] (List.ofFn fun k => (matrixIndex c j k, .there (batchRef k)))
    (fun a => a) .here

theorem transformRowTape_unique (c n : ℕ) (j : Fin n)
    (ω : Tape d (transformRow c n j)) : ω = transformRowTape d c n j :=
  rowTape_unique [] _ (fun a => a) .here ω

/-- Every raw coordinate is consumed once; uniform residuals route to replay. -/
def packCompiledTape (p : Program c τ) (e : GaussianSlot p ≃ Fin n)
    (seedOrigin : Fin n → Origin) (ω : (Fin n → Point d) × ResidualTape p) :
    Tape d (compileWith p e seedOrigin) :=
  ⟨PUnit.unit, PUnit.unit, (fun j => (ω.1 j, PUnit.unit)), PUnit.unit,
    (fun j => transformRowTape d c n j),
    replayTape (Fin.natAdd (n*n)) p (fun a => nomatch a)
      (fun s => batchRef (e s)) (compiledCenter n) (compiledMomentum n) ω.2⟩

def unpackCompiledTape (p : Program c τ) (e : GaussianSlot p ≃ Fin n)
    (seedOrigin : Fin n → Origin) (ω : Tape d (compileWith p e seedOrigin)) :
    (Fin n → Point d) × ResidualTape p :=
  ⟨fun j => (ω.2.2.1 j).1,
    restoreReplayTape (Fin.natAdd (n*n)) p (fun a => nomatch a)
      (fun s => batchRef (e s)) (compiledCenter n) (compiledMomentum n) ω.2.2.2.2.2⟩

theorem unpack_packCompiledTape (p : Program c τ) (e : GaussianSlot p ≃ Fin n)
    (seedOrigin : Fin n → Origin) (ω : (Fin n → Point d) × ResidualTape p) :
    unpackCompiledTape p e seedOrigin (packCompiledTape p e seedOrigin ω) = ω := by
  simp only [unpackCompiledTape, packCompiledTape, restoreReplayTape_replayTape]

theorem pack_unpackCompiledTape (p : Program c τ) (e : GaussianSlot p ≃ Fin n)
    (seedOrigin : Fin n → Origin) (ω : Tape d (compileWith p e seedOrigin)) :
    packCompiledTape p e seedOrigin (unpackCompiledTape p e seedOrigin ω) = ω := by
  rcases ω with ⟨⟨⟩, ⟨⟩, raw, ⟨⟩, rows, tail⟩
  simp only [packCompiledTape, unpackCompiledTape]
  have ht := replayTape_restoreReplayTape (Fin.natAdd (n*n)) p
    (fun a => nomatch a) (fun s => batchRef (e s))
    (compiledCenter n) (compiledMomentum n) tail
  rw [ht]
  have hraw : (fun j => ((raw j).1, PUnit.unit)) = raw := by
    funext j
    rcases raw j with ⟨z, ⟨⟩⟩
    rfl
  have hrows : (fun j => transformRowTape d c n j) = rows := by
    funext j
    exact (transformRowTape_unique c n j (rows j)).symm
  erw [hraw, hrows]

/-- Complete raw target-tape equivalence; no invertibility of T is required. -/
def compiledTapeEquivWith (p : Program c τ) (e : GaussianSlot p ≃ Fin n)
    (seedOrigin : Fin n → Origin) :
    Tape d (compileWith p e seedOrigin) ≃ ((Fin n → Point d) × ResidualTape p) where
  toFun := unpackCompiledTape p e seedOrigin
  invFun := packCompiledTape p e seedOrigin
  left_inv := pack_unpackCompiledTape p e seedOrigin
  right_inv := unpack_packCompiledTape p e seedOrigin

noncomputable def compiledTapeEquiv (p : Program c τ)
    (seedOrigin : Fin (tapeShape p).gaussianBlocks → Origin) :
    Tape d (compileGaussian p seedOrigin) ≃
      ((Fin (tapeShape p).gaussianBlocks → Point d) × ResidualTape p) :=
  compiledTapeEquivWith p (gaussianSlotEquiv p) seedOrigin

/-- The store produced by the closed setup, before matrix rows run. -/
noncomputable def setupEnv (x v : Point d) (Z : Fin n → Point d) : Env d (zeroCtx n) :=
  Env.cons (d := d) (τ := .point) (0 : Point d)
    (Env.prepend Z (Env.cons (d := d) (τ := .point) v
      (Env.cons (d := d) (τ := .point) x Env.empty)))

/-- Literal closed row evaluation uses the actual row-major public table. -/
theorem run_transformRow (T : Fin n → Fin n → ℝ) (coeff : Fin c → ℝ)
    (x v : Point d) (Z : Fin n → Point d) (j : Fin n) (G : Point d → Point d)
    (ω : Tape d (transformRow c n j)) :
    run (transformRow c n j) G (matrixInputs T coeff x v) (setupEnv x v Z) ω =
      pointResult (transformedGaussian T Z j) [] := by
  unfold transformRow
  erw [run_affineRow_ofFn]
  change pointResult ((0 : Point d) + ∑ k, (matrixInputs T coeff x v).coefficient
    (matrixIndex c j k) • storedPoint (Env.prepend Z
      (Env.cons (d := d) (τ := .point) v
        (Env.cons (d := d) (τ := .point) x Env.empty))) (batchRef k)) [] = _
  simp only [matrixInputs, matrixTable_entry, prepend_batchRef, zero_add,
    transformedGaussian]

theorem replayCenter_value (x v : Point d) (Z W : Fin n → Point d) :
    Env.prepend W (setupEnv x v Z) (compiledCenter n) = x := by
  simp only [compiledCenter, prepend_shiftMany]
  change Env.prepend Z (Env.cons (d := d) (τ := .point) v
    (Env.cons (d := d) (τ := .point) x Env.empty)) (RefMap.shiftMany n (.there .here)) = x
  rw [prepend_shiftMany]
  rfl

theorem replayMomentum_value (x v : Point d) (Z W : Fin n → Point d) :
    Env.prepend W (setupEnv x v Z) (compiledMomentum n) = v := by
  simp only [compiledMomentum, prepend_shiftMany]
  change Env.prepend Z (Env.cons (d := d) (τ := .point) v
    (Env.cons (d := d) (τ := .point) x Env.empty)) (RefMap.shiftMany n .here) = v
  rw [prepend_shiftMany]
  rfl

/-- Source tape induced by T may be non-surjective when T is singular. -/
noncomputable def transformedSourceTape (p : Program c τ) (e : GaussianSlot p ≃ Fin n)
    (T : Fin n → Fin n → ℝ) (Z : Fin n → Point d) (r : ResidualTape p) : Tape d p :=
  joinTape p (fun s => transformedGaussian T Z (e s)) r

theorem run_replayBody (p : Program c τ) (e : GaussianSlot p ≃ Fin n)
    (T : Fin n → Fin n → ℝ) (coeff : Fin c → ℝ)
    (x v : Point d) (Z : Fin n → Point d) (r : ResidualTape p) (G : Point d → Point d) :
    run (replayBody p e) G (matrixInputs T coeff x v)
      (Env.prepend (transformedGaussian T Z) (setupEnv x v Z))
      (replayTape (Fin.natAdd (n*n)) p (fun a => nomatch a)
        (fun s => batchRef (e s)) (compiledCenter n) (compiledMomentum n) r) =
      withoutGaussian (run p G ⟨coeff,x,v⟩ Env.empty
        (transformedSourceTape p e T Z r)) := by
  apply run_replayGaussian_join
  · intro j
    exact matrixTable_extra T coeff j
  · intro σ a
    cases a
  · exact replayCenter_value x v Z (transformedGaussian T Z)
  · exact replayMomentum_value x v Z (transformedGaussian T Z)
  · intro s
    exact prepend_batchRef (transformedGaussian T Z) _ (e s)

private theorem flatten_ofFn_singleton (f : Fin n → α) :
    (List.ofFn (fun j => [f j])).flatten = List.ofFn f := by
  induction n with
  | zero => simp
  | succ n ih => simp only [List.ofFn_succ, List.flatten_cons, List.singleton_append, ih]

/-- Entire operational result: raw draws move to the front; Gaussian source
observations are removed, while all query/answer and uniform events remain. -/
theorem run_compileWith_packed (p : Program c τ) (e : GaussianSlot p ≃ Fin n)
    (seedOrigin : Fin n → Origin) (T : Fin n → Fin n → ℝ) (coeff : Fin c → ℝ)
    (x v : Point d) (Z : Fin n → Point d) (r : ResidualTape p) (G : Point d → Point d) :
    let source := run p G ⟨coeff,x,v⟩ Env.empty (transformedSourceTape p e T Z r)
    run (compileWith p e seedOrigin) G (matrixInputs T coeff x v) Env.empty
      (packCompiledTape p e seedOrigin (Z,r)) =
      ⟨source.value, List.ofFn (fun j => Event.gaussian (seedOrigin j)) ++
        source.trace.filter keepNonGaussian⟩ := by
  dsimp only
  simp only [compileWith, packCompiledTape, run, rawDraw, evalInstr, evalPure,
    matrixInputs, List.append_nil, List.nil_append, prefix_nil, flatten_ofFn_singleton]
  change (let rows := fun j => run (transformRow c n j) G (matrixInputs T coeff x v)
            (setupEnv x v Z) (transformRowTape d c n j)
          let tail := run (replayBody p e) G (matrixInputs T coeff x v)
            (Env.prepend (fun j => (rows j).value) (setupEnv x v Z))
            (replayTape (Fin.natAdd (n*n)) p (fun a => nomatch a)
              (fun s => batchRef (e s)) (compiledCenter n) (compiledMomentum n) r)
          (⟨tail.value, List.ofFn (fun j => Event.gaussian (seedOrigin j)) ++
            ((List.ofFn fun j => (rows j).trace).flatten ++ tail.trace)⟩ : Result d τ)) = _
  simp only [run_transformRow, pointResult, List.ofFn_const, List.flatten_replicate_nil,
    List.nil_append, run_replayBody, withoutGaussian]

/-- The exact result theorem holds for every target execution tape. -/
theorem run_compileWith_every_tape (p : Program c τ) (e : GaussianSlot p ≃ Fin n)
    (seedOrigin : Fin n → Origin) (T : Fin n → Fin n → ℝ) (coeff : Fin c → ℝ)
    (x v : Point d) (G : Point d → Point d) (ω : Tape d (compileWith p e seedOrigin)) :
    let data := unpackCompiledTape p e seedOrigin ω
    let source := run p G ⟨coeff,x,v⟩ Env.empty
      (transformedSourceTape p e T data.1 data.2)
    run (compileWith p e seedOrigin) G (matrixInputs T coeff x v) Env.empty ω =
      ⟨source.value, List.ofFn (fun j => Event.gaussian (seedOrigin j)) ++
        source.trace.filter keepNonGaussian⟩ := by
  have h := run_compileWith_packed p e seedOrigin T coeff x v
    (unpackCompiledTape p e seedOrigin ω).1 (unpackCompiledTape p e seedOrigin ω).2 G
  have ht := pack_unpackCompiledTape p e seedOrigin ω
  erw [ht] at h
  exact h

/-- Exact resource counts charge every raw block, including unused zero columns. -/
theorem syntaxCount_compileWith (kind : EventKind) (p : Program c τ)
    (e : GaussianSlot p ≃ Fin n) (seedOrigin : Fin n → Origin) :
    syntaxCount kind (compileWith p e seedOrigin) =
      if kind = .gaussian then n else syntaxCount kind p := by
  cases kind <;>
    simp [compileWith, rawDraw, transformRow, replayBody, syntaxCount,
      instructionCount, Instr.eventKind, syntaxCount_affineRow, syntaxCount_replayGaussian]

/-- Canonical whole-result specialization, for every raw compiled tape. -/
theorem run_compileGaussian (p : Program c τ)
    (seedOrigin : Fin (tapeShape p).gaussianBlocks → Origin)
    (T : Fin (tapeShape p).gaussianBlocks → Fin (tapeShape p).gaussianBlocks → ℝ)
    (coeff : Fin c → ℝ) (x v : Point d) (G : Point d → Point d)
    (ω : Tape d (compileGaussian p seedOrigin)) :
    let data := compiledTapeEquiv p seedOrigin ω
    let source := run p G ⟨coeff,x,v⟩ Env.empty
      (transformedSourceTape p (gaussianSlotEquiv p) T data.1 data.2)
    run (compileGaussian p seedOrigin) G (matrixInputs T coeff x v) Env.empty ω =
      ⟨source.value, List.ofFn (fun j => Event.gaussian (seedOrigin j)) ++
        source.trace.filter keepNonGaussian⟩ :=
  run_compileWith_every_tape p (gaussianSlotEquiv p) seedOrigin T coeff x v G ω

/-- Every resource count of the actual canonical compiled syntax equals source. -/
theorem syntaxCount_compileGaussian (kind : EventKind) (p : Program c τ)
    (seedOrigin : Fin (tapeShape p).gaussianBlocks → Origin) :
    syntaxCount kind (compileGaussian p seedOrigin) = syntaxCount kind p := by
  rw [compileGaussian, syntaxCount_compileWith]
  split_ifs with h
  · subst kind
    exact (gaussianCount_eq_tapeShape p).symm
  · rfl

/-- Operational counts, with no restriction on matrix entries, dimension or tape. -/
theorem executedCount_compileGaussian (kind : EventKind) (p : Program c τ)
    (seedOrigin : Fin (tapeShape p).gaussianBlocks → Origin)
    (G : Point d → Point d)
    (i : Inputs d ((tapeShape p).gaussianBlocks * (tapeShape p).gaussianBlocks + c))
    (ω : Tape d (compileGaussian p seedOrigin)) :
    shapeCount kind ((run (compileGaussian p seedOrigin) G i Env.empty ω).trace.map
      Event.erase) = syntaxCount kind p := by
  rw [run_trace_shape, shapeCount_staticTrace, syntaxCount_compileGaussian]

/-- An observable subsequence keeps full query values and answers, not just tags. -/
def eventIsKind (kind : EventKind) (event : Event d) : Bool := decide (event.erase.1 = kind)

theorem filter_withoutGaussian (kind : EventKind) (hk : kind ≠ .gaussian)
    (events : List (Event d)) :
    (events.filter keepNonGaussian).filter (eventIsKind kind) =
      events.filter (eventIsKind kind) := by
  rw [List.filter_filter]
  congr 1
  funext event
  cases kind <;> cases event <;> simp [eventIsKind, Event.erase, keepNonGaussian] at hk ⊢

private theorem filter_raw_draws (kind : EventKind) (hk : kind ≠ .gaussian)
    (seedOrigin : Fin n → Origin) :
    (List.ofFn (fun j => Event.gaussian (d := d) (seedOrigin j))).filter
      (eventIsKind kind) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro event he
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp he
  cases kind <;> simp [eventIsKind, Event.erase] at hk ⊢

/-- Exact ordered gradient queries/answers or uniforms survive all presampling. -/
theorem run_compileWith_subsequence (kind : EventKind) (hk : kind ≠ .gaussian)
    (p : Program c τ) (e : GaussianSlot p ≃ Fin n)
    (seedOrigin : Fin n → Origin) (T : Fin n → Fin n → ℝ) (coeff : Fin c → ℝ)
    (x v : Point d) (G : Point d → Point d) (ω : Tape d (compileWith p e seedOrigin)) :
    let data := unpackCompiledTape p e seedOrigin ω
    (run (compileWith p e seedOrigin) G (matrixInputs T coeff x v) Env.empty ω).trace.filter
      (eventIsKind kind) =
    (run p G ⟨coeff,x,v⟩ Env.empty (transformedSourceTape p e T data.1 data.2)).trace.filter
      (eventIsKind kind) := by
  dsimp only
  rw [run_compileWith_every_tape]
  simp only [List.filter_append, filter_raw_draws kind hk, filter_withoutGaussian kind hk,
    List.nil_append]

end TapeLowering
end AcceleratedLogConcave.Oracle
