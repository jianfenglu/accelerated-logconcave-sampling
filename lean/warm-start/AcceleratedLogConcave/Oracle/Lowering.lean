import AcceleratedLogConcave.Oracle.Work

/-! Typed compile-time embedding of child programs into a shared stored context.
The supplied center and momentum are replaced by stored references, and public
coefficient indices are reindexed without invoking the gradient oracle. -/
namespace AcceleratedLogConcave.Oracle

abbrev RefMap (Γ Δ : Ctx) := ∀ {τ}, Ref Γ τ → Ref Δ τ

namespace RefMap

def bind (f : RefMap Γ Δ) (r : Ref Δ σ) : RefMap (σ :: Γ) Δ :=
  fun s => match s with
  | .here => r
  | .there s => f s

def lift (f : RefMap Γ Δ) : RefMap (σ :: Γ) (σ :: Δ) :=
  bind (fun r => .there (f r)) .here

def liftMany (n : ℕ) (f : RefMap Γ Δ) :
    RefMap (List.replicate n .point ++ Γ) (List.replicate n .point ++ Δ) :=
  match n with
  | 0 => f
  | n + 1 => lift (liftMany n f)

def shiftMany (n : ℕ) (r : Ref Δ τ) : Ref (List.replicate n .point ++ Δ) τ :=
  match n with
  | 0 => r
  | n + 1 => .there (shiftMany n r)

end RefMap

def Pure.reindex (κ : Fin c → Fin c') (f : RefMap Γ Δ) :
    Pure c Γ τ → Pure c' Δ τ
  | .publicScalar j => .publicScalar (κ j)
  | .rational q => .rational q
  | .add a b => .add (f a) (f b)
  | .mul a b => .mul (f a) (f b)
  | .neg a => .neg (f a)
  | .inv a => .inv (f a)
  | .sqrt a => .sqrt (f a)
  | .zero => .zero
  | .vadd a b => .vadd (f a) (f b)
  | .smul a b => .smul (f a) (f b)

def Prog.lower (κ : Fin c → Fin c') (p : Prog c Γ τ) (f : RefMap Γ Δ)
    (center momentum : Ref Δ .point) : Prog c' Δ τ :=
  match p with
  | .ret r => .ret (f r)
  | .step origin (.pure a) next =>
      .step origin (.pure (a.reindex κ f))
        (next.lower κ f.lift (.there center) (.there momentum))
  | .step _ .center next => next.lower κ (f.bind center) center momentum
  | .step _ .momentum next => next.lower κ (f.bind momentum) center momentum
  | .step origin (.grad r) next =>
      .step origin (.grad (f r))
        (next.lower κ f.lift (.there center) (.there momentum))
  | .step origin .gaussian next =>
      .step origin .gaussian (next.lower κ f.lift (.there center) (.there momentum))
  | .step origin .uniform next =>
      .step origin .uniform (next.lower κ f.lift (.there center) (.there momentum))
  | .batch origin children next =>
      .batch origin (fun j => (children j).lower κ f center momentum)
        (next.lower κ (f.liftMany _) (RefMap.shiftMany _ center)
          (RefMap.shiftMany _ momentum))


/-- Re-route the exact structural tape, removing only nondraw input-read slots. -/
def lowerTape (κ : Fin c → Fin c') (p : Prog c Γ τ) (f : RefMap Γ Δ)
    (center momentum : Ref Δ .point) (ω : Tape d p) :
    Tape d (p.lower κ f center momentum) :=
  match p with
  | .ret _ => ω
  | .step _ (.pure _) next =>
      (ω.1, lowerTape κ next f.lift (.there center) (.there momentum) ω.2)
  | .step _ .center next => lowerTape κ next (f.bind center) center momentum ω.2
  | .step _ .momentum next => lowerTape κ next (f.bind momentum) center momentum ω.2
  | .step _ (.grad _) next =>
      (ω.1, lowerTape κ next f.lift (.there center) (.there momentum) ω.2)
  | .step _ .gaussian next =>
      (ω.1, lowerTape κ next f.lift (.there center) (.there momentum) ω.2)
  | .step _ .uniform next =>
      (ω.1, lowerTape κ next f.lift (.there center) (.there momentum) ω.2)
  | .batch _ children next =>
      ((fun j => lowerTape κ (children j) f center momentum (ω.1 j)),
        lowerTape κ next (f.liftMany _) (RefMap.shiftMany _ center)
          (RefMap.shiftMany _ momentum) ω.2)

theorem evalPure_reindex (κ : Fin c → Fin c') (f : RefMap Γ Δ)
    (a : Pure c Γ τ) (coeff : Fin c → ℝ) (coeff' : Fin c' → ℝ)
    (ρ : Env d Γ) (ρ' : Env d Δ)
    (hc : ∀ j, coeff' (κ j) = coeff j)
    (he : ∀ {σ} (r : Ref Γ σ), ρ' (f r) = ρ r) :
    evalPure (a.reindex κ f) coeff' ρ' = evalPure a coeff ρ := by
  cases a <;> simp [Pure.reindex, evalPure, hc, he] <;> rfl

theorem env_bind (f : RefMap Γ Δ) (r : Ref Δ σ) (x : Ty.denote d σ)
    (ρ : Env d Γ) (ρ' : Env d Δ)
    (he : ∀ {τ} (s : Ref Γ τ), ρ' (f s) = ρ s) (hx : ρ' r = x) :
    ∀ {τ} (s : Ref (σ :: Γ) τ), ρ' (f.bind r s) = Env.cons x ρ s := by
  intro τ s
  cases s <;> simp [RefMap.bind, Env.cons, hx, he]

theorem env_lift (f : RefMap Γ Δ) (x : Ty.denote d σ)
    (ρ : Env d Γ) (ρ' : Env d Δ)
    (he : ∀ {τ} (s : Ref Γ τ), ρ' (f s) = ρ s) :
    ∀ {τ} (s : Ref (σ :: Γ) τ),
      Env.cons x ρ' (f.lift s) = Env.cons x ρ s := by
  intro τ s
  cases s <;> simp [RefMap.lift, RefMap.bind, Env.cons, he]

theorem env_prepend_liftMany (n : ℕ) (f : RefMap Γ Δ)
    (values : Fin n → Point d) (ρ : Env d Γ) (ρ' : Env d Δ)
    (he : ∀ {τ} (r : Ref Γ τ), ρ' (f r) = ρ r) :
    ∀ {τ} (r : Ref (List.replicate n .point ++ Γ) τ),
      Env.prepend values ρ' (f.liftMany n r) = Env.prepend values ρ r := by
  induction n with
  | zero => exact he
  | succ n ih =>
      intro τ r
      cases r with
      | here => rfl
      | there r => exact ih (fun j => values j.succ) r

theorem env_prepend_shiftMany (n : ℕ) (values : Fin n → Point d)
    (ρ : Env d Δ) (r : Ref Δ τ) :
    Env.prepend values ρ (RefMap.shiftMany n r) = ρ r := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih (fun j => values j.succ)


theorem syntaxCount_lower (kind : EventKind) (κ : Fin c → Fin c')
    (p : Prog c Γ τ) (f : RefMap Γ Δ) (center momentum : Ref Δ .point) :
    syntaxCount kind (p.lower κ f center momentum) = syntaxCount kind p := by
  induction p generalizing Δ with
  | ret r => rfl
  | step origin instr next ih =>
      cases instr <;>
        simp [Prog.lower, syntaxCount, instructionCount, Instr.eventKind, ih]
  | batch origin children next ihc ihn =>
      simp [Prog.lower, syntaxCount, ihc, ihn]

/-- Erasing deterministic input reads preserves ordered event kinds and origins. -/
theorem staticTrace_lower (κ : Fin c → Fin c') (p : Prog c Γ τ)
    (f : RefMap Γ Δ) (center momentum : Ref Δ .point) :
    staticTrace (p.lower κ f center momentum) = staticTrace p := by
  induction p generalizing Δ with
  | ret r => rfl
  | step origin instr next ih =>
      cases instr <;>
        simp [Prog.lower, staticTrace, Instr.staticTrace, Instr.eventKind, ih]
  | batch origin children next ihc ihn =>
      simp [Prog.lower, staticTrace, ihc, ihn]

/-- Substitution preserves the complete value-carrying oracle transcript. -/
theorem run_lower (κ : Fin c → Fin c') (p : Prog c Γ τ)
    (G : Point d → Point d) (i : Inputs d c) (i' : Inputs d c')
    (f : RefMap Γ Δ) (center momentum : Ref Δ .point)
    (ρ : Env d Γ) (ρ' : Env d Δ) (ω : Tape d p)
    (hc : ∀ j, i'.coefficient (κ j) = i.coefficient j)
    (he : ∀ {σ} (r : Ref Γ σ), ρ' (f r) = ρ r)
    (hx : ρ' center = i.center) (hp : ρ' momentum = i.momentum) :
    run (p.lower κ f center momentum) G i' ρ' (lowerTape κ p f center momentum ω) =
      run p G i ρ ω := by
  induction p generalizing Δ with
  | ret r => simp only [Prog.lower, lowerTape, run, he]
  | step origin instr next ih =>
      cases instr with
      | pure a =>
          have hv := evalPure_reindex κ f a i.coefficient i'.coefficient ρ ρ' hc he
          have hr := ih f.lift (.there center) (.there momentum)
            (Env.cons (evalPure a i.coefficient ρ) ρ)
            (Env.cons (evalPure a i.coefficient ρ) ρ') ω.2
            (env_lift f _ ρ ρ' he) hx hp
          simpa only [Prog.lower, lowerTape, run, evalInstr, hv, List.nil_append] using hr
      | center =>
          have hr := ih (f.bind center) center momentum (Env.cons (d := d) (τ := .point) i.center ρ) ρ' ω.2
            (env_bind (d := d) f center i.center ρ ρ' he hx) hx hp
          simpa only [Prog.lower, lowerTape, run, evalInstr, List.nil_append] using hr
      | momentum =>
          have hr := ih (f.bind momentum) center momentum (Env.cons (d := d) (τ := .point) i.momentum ρ) ρ' ω.2
            (env_bind (d := d) f momentum i.momentum ρ ρ' he hp) hx hp
          simpa only [Prog.lower, lowerTape, run, evalInstr, List.nil_append] using hr
      | grad r =>
          have hr := ih f.lift (.there center) (.there momentum)
            (Env.cons (d := d) (τ := .point) (G (ρ r)) ρ) (Env.cons (d := d) (τ := .point) (G (ρ r)) ρ') ω.2
            (env_lift f _ ρ ρ' he) hx hp
          simp only [Prog.lower, lowerTape, run, evalInstr, he, hr]
      | gaussian =>
          have hr := ih f.lift (.there center) (.there momentum)
            (Env.cons (d := d) (τ := .point) ω.1 ρ) (Env.cons (d := d) (τ := .point) ω.1 ρ') ω.2
            (env_lift f _ ρ ρ' he) hx hp
          simp only [Prog.lower, lowerTape, run, evalInstr, hr]
      | uniform =>
          have hr := ih f.lift (.there center) (.there momentum)
            (Env.cons (d := d) (τ := .scalar) ω.1.val ρ) (Env.cons (d := d) (τ := .scalar) ω.1.val ρ') ω.2
            (env_lift f _ ρ ρ' he) hx hp
          simp only [Prog.lower, lowerTape, run, evalInstr, hr]
  | batch origin children next ihc ihn =>
      have hc' : ∀ j,
          run ((children j).lower κ f center momentum) G i' ρ'
            (lowerTape κ (children j) f center momentum (ω.1 j)) =
          run (children j) G i ρ (ω.1 j) :=
        fun j => ihc j f center momentum ρ ρ' (ω.1 j) he hx hp
      have hr := ihn (f.liftMany _) (RefMap.shiftMany _ center)
        (RefMap.shiftMany _ momentum)
        (Env.prepend (fun j => (run (children j) G i ρ (ω.1 j)).value) ρ)
        (Env.prepend (fun j => (run (children j) G i ρ (ω.1 j)).value) ρ') ω.2
        (env_prepend_liftMany _ f _ ρ ρ' he)
        ((env_prepend_shiftMany _ _ ρ' center).trans hx)
        ((env_prepend_shiftMany _ _ ρ' momentum).trans hp)
      simp only [Prog.lower, lowerTape, run, hc', hr]


/-- Restore the trivial input-read slots; all random data retain their values. -/
def restoreTape (κ : Fin c → Fin c') (p : Prog c Γ τ) (f : RefMap Γ Δ)
    (center momentum : Ref Δ .point) (ω : Tape d (p.lower κ f center momentum)) :
    Tape d p :=
  match p with
  | .ret _ => ω
  | .step _ (.pure _) next =>
      (ω.1, restoreTape κ next f.lift (.there center) (.there momentum) ω.2)
  | .step _ .center next =>
      (PUnit.unit, restoreTape κ next (f.bind center) center momentum ω)
  | .step _ .momentum next =>
      (PUnit.unit, restoreTape κ next (f.bind momentum) center momentum ω)
  | .step _ (.grad _) next =>
      (ω.1, restoreTape κ next f.lift (.there center) (.there momentum) ω.2)
  | .step _ .gaussian next =>
      (ω.1, restoreTape κ next f.lift (.there center) (.there momentum) ω.2)
  | .step _ .uniform next =>
      (ω.1, restoreTape κ next f.lift (.there center) (.there momentum) ω.2)
  | .batch _ children next =>
      ((fun j => restoreTape κ (children j) f center momentum (ω.1 j)),
        restoreTape κ next (f.liftMany _) (RefMap.shiftMany _ center)
          (RefMap.shiftMany _ momentum) ω.2)

theorem lowerTape_restoreTape (κ : Fin c → Fin c') (p : Prog c Γ τ)
    (f : RefMap Γ Δ) (center momentum : Ref Δ .point)
    (ω : Tape d (p.lower κ f center momentum)) :
    lowerTape κ p f center momentum (restoreTape κ p f center momentum ω) = ω := by
  induction p generalizing Δ with
  | ret _ => rfl
  | step origin instr next ih =>
      cases instr <;> simp only [lowerTape, restoreTape]
      all_goals first
      | exact ih _ _ _ _
      | (simp only [ih]; rfl)
  | batch origin children next ihc ihn =>
      simp only [lowerTape, restoreTape, ihc, ihn]
      rfl

theorem restoreTape_lowerTape (κ : Fin c → Fin c') (p : Prog c Γ τ)
    (f : RefMap Γ Δ) (center momentum : Ref Δ .point) (ω : Tape d p) :
    restoreTape κ p f center momentum (lowerTape κ p f center momentum ω) = ω := by
  induction p generalizing Δ with
  | ret _ => rfl
  | step origin instr next ih =>
      cases instr <;> simp only [lowerTape, restoreTape, ih]
      all_goals apply Prod.ext
      all_goals rfl
  | batch origin children next ihc ihn =>
      simp only [lowerTape, restoreTape, ihc, ihn]
      rfl

/-- Lowering neither duplicates nor deletes any nontrivial tape coordinate. -/
def lowerTapeEquiv (κ : Fin c → Fin c') (p : Prog c Γ τ)
    (f : RefMap Γ Δ) (center momentum : Ref Δ .point) :
    Tape d p ≃ Tape d (p.lower κ f center momentum) where
  toFun := lowerTape κ p f center momentum
  invFun := restoreTape κ p f center momentum
  left_inv := restoreTape_lowerTape κ p f center momentum
  right_inv := lowerTape_restoreTape κ p f center momentum

theorem syntaxCounts_lower (κ : Fin c → Fin c') (p : Prog c Γ τ)
    (f : RefMap Γ Δ) (center momentum : Ref Δ .point) :
    syntaxCounts (p.lower κ f center momentum) = syntaxCounts p := by
  simp only [syntaxCounts, syntaxCount_lower]

theorem queryCount_lower (κ : Fin c → Fin c') (p : Prog c Γ τ)
    (f : RefMap Γ Δ) (center momentum : Ref Δ .point) :
    queryCount (p.lower κ f center momentum) = queryCount p := by
  simp only [queryCount, syntaxCounts_lower]

theorem bookkeepingWork_lower (κ : Fin c → Fin c') (p : Prog c Γ τ)
    (f : RefMap Γ Δ) (center momentum : Ref Δ .point) :
    bookkeepingWork (p.lower κ f center momentum) = bookkeepingWork p := by
  simp only [bookkeepingWork, syntaxCounts_lower]

/-- Every execution of a lowered program has the original resource counts. -/
theorem run_lower_counts (κ : Fin c → Fin c') (p : Prog c Γ τ)
    (f : RefMap Γ Δ) (center momentum : Ref Δ .point)
    (G : Point d → Point d) (i' : Inputs d c') (ρ' : Env d Δ)
    (ω : Tape d (p.lower κ f center momentum)) :
    traceCounts (run (p.lower κ f center momentum) G i' ρ' ω).trace = syntaxCounts p := by
  rw [run_counts, syntaxCounts_lower]

/-- Inline a closed child at two already stored point references. -/
def Program.embed (κ : Fin c → Fin c') (p : Program c τ)
    (center momentum : Ref Δ .point) : Prog c' Δ τ :=
  p.lower κ (fun r => nomatch r) center momentum

/-- The child sees the stored inputs and pulled-back public table. The global
center and momentum of the host execution are not passed to the child. -/
theorem run_embed (κ : Fin c → Fin c') (p : Program c τ)
    (center momentum : Ref Δ .point) (G : Point d → Point d)
    (i' : Inputs d c') (ρ' : Env d Δ) (ω : Tape d p) :
    run (p.embed κ center momentum) G i' ρ'
      (lowerTape κ p (fun r => nomatch r) center momentum ω) =
    run p G ⟨i'.coefficient ∘ κ, ρ' center, ρ' momentum⟩ Env.empty ω := by
  exact run_lower κ p G _ i' _ center momentum Env.empty ρ' ω
    (fun _ => rfl) (fun r => nomatch r) rfl rfl

/-- The embedded-child characterization applies to every target tape. -/
theorem run_embed_every_tape (κ : Fin c → Fin c') (p : Program c τ)
    (center momentum : Ref Δ .point) (G : Point d → Point d)
    (i' : Inputs d c') (ρ' : Env d Δ) (ω : Tape d (p.embed κ center momentum)) :
    run (p.embed κ center momentum) G i' ρ' ω =
    run p G ⟨i'.coefficient ∘ κ, ρ' center, ρ' momentum⟩ Env.empty
      (restoreTape κ p (fun r => nomatch r) center momentum ω) := by
  calc
    _ = run (p.embed κ center momentum) G i' ρ'
        (lowerTape κ p (fun r => nomatch r) center momentum
          (restoreTape κ p (fun r => nomatch r) center momentum ω)) :=
      congrArg (fun z => run (p.embed κ center momentum) G i' ρ' z)
        (lowerTape_restoreTape κ p (fun r => nomatch r) center momentum ω).symm
    _ = _ := run_embed κ p center momentum G i' ρ'
      (restoreTape κ p (fun r => nomatch r) center momentum ω)

end AcceleratedLogConcave.Oracle
