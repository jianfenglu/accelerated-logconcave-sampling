import AcceleratedLogConcave.Oracle.PrivateSamplingValue
import AcceleratedLogConcave.Oracle.SamplingCanonicalSplitFactorization
import Mathlib.Probability.Independence.Basic

/-! Actual occurrence projections from the complete private sampling tape.
No executable recursion or tape replacement is introduced. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Oracle.PrivateSamplingTapeProjections
open AffineLowering TapeLowering NoisyLayer RecursiveMeanProgram
  RecursiveMeanContinuation SourceMeanLayer PrivateSamplingProgram
  CanonicalTapeLaw CanonicalTapeMeasurability
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

variable {n C d : ℕ} {c cf : Fin n → ℕ}
  {p : ∀ i, Program (c i) .point} {pf : ∀ i, Program (cf i) .point}
  (cfg : Config n C c cf p pf)

/-- Each final designated input, followed by the residual and reserve blocks. -/
abbrev FinalIndex (n : ℕ) := Fin n ⊕ (Unit ⊕ Unit)
/-- The initial position block is kept distinct from all final occurrences. -/
abbrev Index (n : ℕ) := Unit ⊕ FinalIndex n

def finishSlot {Γ : Ctx} (old : Fin n → Ref Γ .point) (out : Ref Γ .point) :
    FinalIndex n → GaussianSlot (finish cfg old out)
  | .inl i => .inl ⟨i, .inl PUnit.unit⟩
  | .inr (.inl _) => .inr (.inl PUnit.unit)
  | .inr (.inr _) => .inr (.inr (.inl PUnit.unit))

def classifyFinish {Γ : Ctx} (old : Fin n → Ref Γ .point) (out : Ref Γ .point) :
    GaussianSlot (finish cfg old out) → FinalIndex n
  | .inl ⟨i, _⟩ => .inl i
  | .inr (.inl _) => .inr (.inl ())
  | .inr (.inr _) => .inr (.inr ())

theorem finishSlot_injective {Γ : Ctx} (old : Fin n → Ref Γ .point)
    (out : Ref Γ .point) : Function.Injective (finishSlot cfg old out) := by
  apply Function.LeftInverse.injective (g := classifyFinish cfg old out)
  intro i
  cases i with
  | inl i => rfl
  | inr j => cases j <;> rfl

def loopSlot {Ξ : Ctx} (out : Ref Ξ .point) :
    (N : ℕ) → {Γ : Ctx} → (old direct : Fin n → Ref Γ .point) →
      (saved : RefMap Ξ Γ) → FinalIndex n →
      GaussianSlot (iterateThen c p cfg.mainSlots cfg.mainEquiv cfg.layerOrigin
        cfg.mainDesignated cfg.mainResidual cfg.mainAuxiliary
        (fun old _ saved => finish cfg old (saved out)) N old direct saved)
  | 0, _, old, _, saved, j => finishSlot cfg old (saved out) j
  | N+1, _, _, direct, saved, j => .inr (.inr (.inr
      (loopSlot out N batchRef (fun i => preserveDirect (direct i))
        (fun r => preserveDirect (saved r)) j)))

theorem loopSlot_injective {Ξ : Ctx} (out : Ref Ξ .point) (N : ℕ)
    {Γ : Ctx} (old direct : Fin n → Ref Γ .point) (saved : RefMap Ξ Γ) :
    Function.Injective (loopSlot cfg out N old direct saved) := by
  induction N generalizing Γ with
  | zero => exact finishSlot_injective cfg old (saved out)
  | succ N ih =>
      intro i j h
      exact ih _ _ _ (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj h)))

def bodySlot {Γ : Ctx} (direct : Fin n → Ref Γ .point) (out : Ref Γ .point)
    (j : FinalIndex n) : GaussianSlot (body cfg direct out) :=
  .inr (.inr (loopSlot cfg out cfg.layers batchRef
    (fun i => RefMap.shiftMany n (RefMap.shiftMany n (direct i)))
    (fun r => RefMap.shiftMany n (RefMap.shiftMany n r)) j))

def slot : Index n → GaussianSlot (code cfg)
  | .inl _ => .inr (.inl PUnit.unit)
  | .inr j => .inr (.inr (.inr (.inr (.inr
      (bodySlot cfg batchRef (RefMap.shiftMany n .here) j)))))

theorem slot_injective : Function.Injective (slot cfg) := by
  intro i j h
  cases i with
  | inl i => cases j with
    | inl j => exact congrArg Sum.inl (Subsingleton.elim _ _)
    | inr j =>
      have hh := congrArg (fun s : GaussianSlot (code cfg) =>
        match s with | .inr (.inr _) => false | _ => true) h
      cases hh
  | inr i => cases j with
    | inl j =>
      have hh := congrArg (fun s : GaussianSlot (code cfg) =>
        match s with | .inr (.inr _) => false | _ => true) h
      cases hh
    | inr j =>
      apply congrArg Sum.inr
      apply loopSlot_injective cfg (RefMap.shiftMany n .here) cfg.layers batchRef
        (fun i => RefMap.shiftMany n (RefMap.shiftMany n (batchRef i)))
        (fun r => RefMap.shiftMany n (RefMap.shiftMany n r))
      exact Sum.inr.inj (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj
        (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj h))))))

def coordinates (ω : Tape d (code cfg)) : Index n → Point d :=
  fun i => (splitTape (code cfg) ω).1 (slot cfg i)

theorem position_eq (ω : Tape d (code cfg)) :
    coordinates cfg ω (.inl ()) = ω.2.1 := rfl

/-- Injective occurrence selection preserves the finite product law. -/
theorem pi_selection {I J X : Type*} [Fintype I] [Fintype J]
    [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (f : J → I) (hf : Function.Injective f) :
    (Measure.pi (fun _ : I => μ)).map (fun z j => z (f j)) =
      Measure.pi (fun _ : J => μ) := by
  have hi : iIndepFun (fun i (z : I → X) => z i) (Measure.pi (fun _ : I => μ)) :=
    iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  have h := (hi.precomp hf).map_fun_eq_pi_map
    (fun j => (measurable_pi_apply (f j)).aemeasurable)
  rw [h]
  congr 1
  funext j
  exact (measurePreserving_eval (fun _ : I => μ) (f j)).map_eq

/-- Every selected block is an actual tape occurrence; all unselected data
remain in the domain of this pushforward. -/
theorem map_coordinates (L : PrimitiveLaws d) :
    let : MeasurableSpace (Tape d (code cfg)) := tapeSpace d (code cfg)
    (tapeLaw L (code cfg)).map (coordinates cfg) =
      Measure.pi (fun _ : Index n => L.pointDraw) := by
  let : MeasurableSpace (Tape d (code cfg)) := tapeSpace d (code cfg)
  let : IsProbabilityMeasure L.pointDraw := L.point_probability
  have hm : Measurable (fun z : GaussianSlot (code cfg) → Point d =>
      fun j => z (slot cfg j)) := by fun_prop
  change Measure.map ((fun z j => z (slot cfg j)) ∘
    (fun ω => (splitTape (code cfg) ω).1)) _ = _
  rw [← Measure.map_map hm (measurable_splitTape d (code cfg)).fst,
    CanonicalTapeFactorization.map_gaussian_tapeLaw]
  exact pi_selection _ _ (slot_injective cfg)

theorem loopSlot_evaluation {Ξ : Ctx} (out : Ref Ξ .point)
    (G : Point d → Point d) (input : Inputs d C) (N : ℕ)
    {Γ : Ctx} (old direct : Fin n → Ref Γ .point) (saved : RefMap Ξ Γ)
    (env : Env d Γ)
    (ω : Tape d (iterateThen c p cfg.mainSlots cfg.mainEquiv cfg.layerOrigin
      cfg.mainDesignated cfg.mainResidual cfg.mainAuxiliary
      (fun old _ saved => finish cfg old (saved out)) N old direct saved))
    (j : FinalIndex n) :
    let state := finalState c p cfg.mainSlots cfg.mainEquiv cfg.layerOrigin
      cfg.mainDesignated cfg.mainResidual cfg.mainAuxiliary
      (fun old _ saved => finish cfg old (saved out)) G input N old direct saved env ω
    (splitTape _ ω).1 (loopSlot cfg out N old direct saved j) =
      (splitTape _ state.tape).1 (finishSlot cfg state.old (state.saved out) j) := by
  induction N generalizing Γ with
  | zero => rfl
  | succ N ih =>
      exact ih batchRef (fun i => preserveDirect (direct i))
        (fun r => preserveDirect (saved r)) _ ω.2.2.2

def bodyState {Γ : Ctx} (direct : Fin n → Ref Γ .point) (out : Ref Γ .point)
    (G : Point d → Point d) (input : Inputs d C) (env : Env d Γ)
    (ω : Tape d (body cfg direct out)) :=
  let Z : Fin n → Point d := fun i => (ω.1 i).1
  let initialEnv : Env d (replyCtx n (replyCtx n Γ)) := Env.prepend
    (fun j => storedPoint env (direct j) + input.coefficient cfg.noise • Z j)
    (Env.prepend Z env)
  finalState c p cfg.mainSlots cfg.mainEquiv cfg.layerOrigin
    cfg.mainDesignated cfg.mainResidual cfg.mainAuxiliary
    (fun old _ saved => finish cfg old (saved out)) G input cfg.layers batchRef
    (fun i => RefMap.shiftMany n (RefMap.shiftMany n (direct i)))
    (fun r => RefMap.shiftMany n (RefMap.shiftMany n r)) initialEnv ω.2.2

def state (G : Point d → Point d) (input : Inputs d C)
    (ω : Tape d (code cfg)) :=
  bodyState cfg batchRef (RefMap.shiftMany n .here) G input
    (setupEnv cfg input ω.2.1) ω.2.2.2.2.2

theorem coordinates_final (G : Point d → Point d) (input : Inputs d C)
    (ω : Tape d (code cfg)) (j : FinalIndex n) :
    coordinates cfg ω (.inr j) =
      (splitTape _ (state cfg G input ω).tape).1
        (finishSlot cfg (state cfg G input ω).old
          ((state cfg G input ω).saved (RefMap.shiftMany n .here)) j) :=
  loopSlot_evaluation cfg (RefMap.shiftMany n .here) G input cfg.layers batchRef
    (fun i => RefMap.shiftMany n (RefMap.shiftMany n (batchRef i)))
    (fun r => RefMap.shiftMany n (RefMap.shiftMany n r)) _ _ j

theorem designated_eq (G : Point d → Point d) (input : Inputs d C)
    (ω : Tape d (code cfg)) (i : Fin n) :
    coordinates cfg ω (.inr (.inl i)) = ((state cfg G input ω).tape.1 i).1 :=
  coordinates_final cfg G input ω (.inl i)

theorem residual_eq (G : Point d → Point d) (input : Inputs d C)
    (ω : Tape d (code cfg)) :
    coordinates cfg ω (.inr (.inr (.inl ()))) = (state cfg G input ω).tape.2.1 :=
  coordinates_final cfg G input ω (.inr (.inl ()))

theorem reserve_eq (G : Point d → Point d) (input : Inputs d C)
    (ω : Tape d (code cfg)) :
    coordinates cfg ω (.inr (.inr (.inr ()))) = (state cfg G input ω).tape.2.2.1 :=
  coordinates_final cfg G input ω (.inr (.inr ()))

def finalData (G : Point d → Point d) (input : Inputs d C)
    (ω : Tape d (code cfg)) (i : Fin n) :=
  freshChildTapeEquiv (pf i) (cfg.finalEquiv i) (cfg.finalSlots i)
    ((state cfg G input ω).old i) (cfg.finalDesignated i) (cfg.finalAuxiliary i)
    ((state cfg G input ω).tape.1 i)

def finalValue (G : Point d → Point d) (input : Inputs d C)
    (ω : Tape d (code cfg)) (i : Fin n) : Point d :=
  (run (freshChild (pf i) (cfg.finalEquiv i) (cfg.finalSlots i)
    ((state cfg G input ω).old i) (cfg.finalDesignated i) (cfg.finalAuxiliary i))
    G input (state cfg G input ω).env ((state cfg G input ω).tape.1 i)).value

theorem run_code_value (G : Point d → Point d) (input : Inputs d C)
    (ω : Tape d (code cfg)) :
    (run (code cfg) G input Env.empty ω).value =
      input.coefficient cfg.invEnd • coordinates cfg ω (.inl ()) +
      (∑ i, input.coefficient (cfg.rowWeight i) • finalValue cfg G input ω i) +
      (input.coefficient cfg.beta • coordinates cfg ω (.inr (.inr (.inl ()))) +
       input.coefficient cfg.reserve • coordinates cfg ω (.inr (.inr (.inr ())))) := by
  rw [run_code_setup, run_body_value, setupEnv_output]
  rw [residual_eq cfg G input ω, reserve_eq cfg G input ω]
  rfl

/-- Algebra after the literal interpreter identity; all coefficient premises are
local lookups, not stochastic or stability assumptions. -/
theorem run_code_affine (G : Point d → Point d) (input : Inputs d C)
    (ω : Tape d (code cfg)) (c β v σ : ℝ) (w : Fin n → ℝ) (Q : Fin n → Point d)
    (hc : input.coefficient cfg.invEnd = c)
    (hβ : input.coefficient cfg.beta = β) (hv : input.coefficient cfg.reserve = v)
    (hw : ∀ i, input.coefficient (cfg.rowWeight i) = w i)
    (hQ : ∀ i, finalValue cfg G input ω i = Q i + σ • coordinates cfg ω (.inr (.inl i))) :
    (run (code cfg) G input Env.empty ω).value =
      c • coordinates cfg ω (.inl ()) + (∑ i, w i • Q i) +
      ((∑ i, (w i*σ) • coordinates cfg ω (.inr (.inl i))) +
        β • coordinates cfg ω (.inr (.inr (.inl ()))) +
        v • coordinates cfg ω (.inr (.inr (.inr ())))) := by
  rw [run_code_value cfg G input ω, hc, hβ, hv]
  simp_rw [hw, hQ, smul_add, smul_smul, Finset.sum_add_distrib]
  abel

def grouped (z : Index n → Point d) : Point d × (FinalIndex n → Point d) :=
  (z (.inl ()), fun j => z (.inr j))

theorem map_grouped (L : PrimitiveLaws d) :
    (Measure.pi (fun _ : Index n => L.pointDraw)).map (grouped (n := n)) =
      L.pointDraw.prod (Measure.pi (fun _ : FinalIndex n => L.pointDraw)) := by
  let : IsProbabilityMeasure L.pointDraw := L.point_probability
  have hsum := measurePreserving_sumPiEquivProdPi (fun _ : Index n => L.pointDraw)
  have hev := measurePreserving_eval (fun _ : Unit => L.pointDraw) ()
  have h := (hev.prod (MeasurePreserving.id
    (Measure.pi (fun _ : FinalIndex n => L.pointDraw)))).comp hsum
  exact h.map_eq

theorem map_grouped_coordinates (L : PrimitiveLaws d) :
    let : MeasurableSpace (Tape d (code cfg)) := tapeSpace d (code cfg)
    (tapeLaw L (code cfg)).map (fun ω => grouped (coordinates cfg ω)) =
      L.pointDraw.prod (Measure.pi (fun _ : FinalIndex n => L.pointDraw)) := by
  let : MeasurableSpace (Tape d (code cfg)) := tapeSpace d (code cfg)
  have hm : Measurable (coordinates cfg : Tape d (code cfg) → Index n → Point d) :=
    (measurable_pi_iff.mpr fun j => measurable_pi_apply (slot cfg j)).comp
      (measurable_splitTape d (code cfg)).fst
  rw [show (fun ω => grouped (coordinates cfg ω)) = grouped ∘ coordinates cfg from rfl,
    ← Measure.map_map (by unfold grouped; fun_prop) hm, map_coordinates, map_grouped]

end AcceleratedLogConcave.Oracle.PrivateSamplingTapeProjections
