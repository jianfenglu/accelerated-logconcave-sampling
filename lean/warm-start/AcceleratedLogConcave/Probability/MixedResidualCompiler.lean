import AcceleratedLogConcave.Probability.MixedResidualRouting

/-! The compiler's complete raw tape equivalence preserves the actual independent
instruction measure. Uniform residuals remain actual uniform coordinates throughout
Gaussian presampling and replay, including when the public transform is singular. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory MeasureTheory.Measure ProbabilityTheory
namespace AcceleratedLogConcave.Probability.MixedResidualTape
open Oracle Oracle.TapeLowering

/-- Actual source replay preserves the residual instruction law. Removed center,
momentum and Gaussian instructions have only unit residual leaves. -/
theorem replayTape_preserving (d : ℕ) (κ : Fin c → Fin c') (p : Prog c Γ τ)
    (f : RefMap Γ Δ) (slots : GaussianSlot p → Ref Δ .point)
    (center momentum : Ref Δ .point) :
    MeasurePreserving (replayTape (d := d) κ p f slots center momentum)
      (residualLaw p) (tapeLaw d (replayGaussian κ p f slots center momentum)) := by
  induction p generalizing Δ with
  | ret _ => exact MeasurePreserving.id _
  | step origin i next ih =>
      cases i with
      | pure a =>
          exact (MeasurePreserving.id (Measure.dirac PUnit.unit)).prod
            (ih f.lift (fun s => .there (slots (.inr s))) (.there center) (.there momentum))
      | grad r =>
          exact (MeasurePreserving.id (Measure.dirac PUnit.unit)).prod
            (ih f.lift (fun s => .there (slots (.inr s))) (.there center) (.there momentum))
      | uniform =>
          exact (MeasurePreserving.id uniformLaw).prod
            (ih f.lift (fun s => .there (slots (.inr s))) (.there center) (.there momentum))
      | center =>
          exact (ih (f.bind center) (fun s => slots (.inr s)) center momentum).comp
            (measurePreserving_snd (μ := Measure.dirac PUnit.unit) (ν := residualLaw next))
      | momentum =>
          exact (ih (f.bind momentum) (fun s => slots (.inr s)) center momentum).comp
            (measurePreserving_snd (μ := Measure.dirac PUnit.unit) (ν := residualLaw next))
      | gaussian =>
          exact (ih (f.bind (slots (.inl PUnit.unit))) (fun s => slots (.inr s)) center momentum).comp
            (measurePreserving_snd (μ := Measure.dirac PUnit.unit) (ν := residualLaw next))
  | batch origin children next ihc ihn =>
      exact (measurePreserving_pi _ _ (fun j => ihc j f (fun s => slots (.inl ⟨j,s⟩))
        center momentum)).prod
        (ihn (f.liftMany _) (fun s => RefMap.shiftMany _ (slots (.inr s)))
          (RefMap.shiftMany _ center) (RefMap.shiftMany _ momentum))

/-- Measurability of every restored actual residual coordinate. -/
theorem measurable_restoreReplayTape (d : ℕ) (κ : Fin c → Fin c') (p : Prog c Γ τ)
    (f : RefMap Γ Δ) (slots : GaussianSlot p → Ref Δ .point)
    (center momentum : Ref Δ .point) :
    Measurable (restoreReplayTape (d := d) κ p f slots center momentum) := by
  induction p generalizing Δ with
  | ret _ => exact measurable_id
  | step origin i next ih =>
      cases i with
      | pure a =>
          exact measurable_fst.prodMk ((ih f.lift (fun s => .there (slots (.inr s)))
            (.there center) (.there momentum)).comp measurable_snd)
      | grad r =>
          exact measurable_fst.prodMk ((ih f.lift (fun s => .there (slots (.inr s)))
            (.there center) (.there momentum)).comp measurable_snd)
      | uniform =>
          exact measurable_fst.prodMk ((ih f.lift (fun s => .there (slots (.inr s)))
            (.there center) (.there momentum)).comp measurable_snd)
      | center =>
          exact measurable_const.prodMk (ih (f.bind center) (fun s => slots (.inr s)) center momentum)
      | momentum =>
          exact measurable_const.prodMk (ih (f.bind momentum) (fun s => slots (.inr s)) center momentum)
      | gaussian =>
          exact measurable_const.prodMk (ih (f.bind (slots (.inl PUnit.unit)))
            (fun s => slots (.inr s)) center momentum)
  | batch origin children next ihc ihn =>
      apply Measurable.prodMk
      · apply Measurable.of_eval
        intro j
        exact (ihc j f (fun s => slots (.inl ⟨j,s⟩)) center momentum).comp
          ((measurable_pi_apply j).comp measurable_fst)
      · exact (ihn (f.liftMany _) (fun s => RefMap.shiftMany _ (slots (.inr s)))
          (RefMap.shiftMany _ center) (RefMap.shiftMany _ momentum)).comp measurable_snd

private theorem add_const_left {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) [SFinite μ] (b : B) :
    MeasurePreserving (fun a => (b,a)) μ ((Measure.dirac b).prod μ) :=
  ⟨by fun_prop, (Measure.dirac_prod b).symm⟩

private theorem add_const_right {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) [SFinite μ] (b : B) :
    MeasurePreserving (fun a => (a,b)) μ (μ.prod (Measure.dirac b)) :=
  ⟨by fun_prop, (Measure.prod_dirac b).symm⟩

private theorem probability_eq_dirac_of_all_eq {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ] (a : A) (ha : ∀ x, x = a) :
    μ = Measure.dirac a := by
  have he : (id : A → A) = fun _ => a := funext ha
  calc
    μ = μ.map id := Measure.map_id.symm
    _ = μ.map (fun _ => a) := congrArg (fun f : A → A => μ.map f) he
    _ = Measure.dirac a := by simp

private theorem transformRowsLaw (d c n : ℕ) :
    Measure.pi (fun j : Fin n => tapeLaw d (transformRow c n j)) =
      Measure.dirac (fun j => transformRowTape d c n j) :=
  probability_eq_dirac_of_all_eq _ _ (fun x => funext (fun j =>
    transformRowTape_unique c n j (x j)))

/-- Every raw compiled tape is generated with its exact structural instruction law.
No Gaussian invariance or invertibility of the public matrix is required. -/
theorem packCompiledTape_preserving (d : ℕ) (p : Program c τ)
    (e : GaussianSlot p ≃ Fin n) (seedOrigin : Fin n → Origin) :
    MeasurePreserving (packCompiledTape (d := d) p e seedOrigin)
      ((Measure.pi (fun _ : Fin n => stdGaussian (Point d))).prod (residualLaw p))
      (tapeLaw d (compileWith p e seedOrigin)) := by
  have hreplay := replayTape_preserving d (Fin.natAdd (n*n)) p (fun a => nomatch a)
    (fun s => AffineLowering.batchRef (e s)) (compiledCenter n) (compiledMomentum n)
  have hrows := add_const_left (tapeLaw d (replayBody p e))
    (fun j => transformRowTape d c n j)
  rw [← transformRowsLaw d c n] at hrows
  have hzero := add_const_left
    ((Measure.pi (fun j => tapeLaw d (transformRow c n j))).prod
      (tapeLaw d (replayBody p e))) PUnit.unit
  have hraw : MeasurePreserving (fun z : Fin n → Point d => fun j =>
        (show Tape d (rawDraw (c := n*n+c) (seedOrigin j)) from (z j,PUnit.unit)))
      (Measure.pi (fun _ : Fin n => stdGaussian (Point d)))
      (Measure.pi (fun j => tapeLaw d (rawDraw (c := n*n+c) (seedOrigin j)))) := by
    exact measurePreserving_pi (fun _ : Fin n => stdGaussian (Point d))
      (fun j => tapeLaw d (rawDraw (c := n*n+c) (seedOrigin j)))
      (fun _ => add_const_right (stdGaussian (Point d)) PUnit.unit)

  have hbody := hraw.prod (hzero.comp (hrows.comp hreplay))
  have hmomentum := add_const_left
    ((Measure.pi (fun j => tapeLaw d (rawDraw (c := n*n+c) (seedOrigin j)))).prod
      ((Measure.dirac PUnit.unit).prod
        ((Measure.pi (fun j => tapeLaw d (transformRow c n j))).prod
          (tapeLaw d (replayBody p e))))) PUnit.unit
  have hcenter := add_const_left
    ((Measure.dirac PUnit.unit).prod
      ((Measure.pi (fun j => tapeLaw d (rawDraw (c := n*n+c) (seedOrigin j)))).prod
        ((Measure.dirac PUnit.unit).prod
          ((Measure.pi (fun j => tapeLaw d (transformRow c n j))).prod
            (tapeLaw d (replayBody p e)))))) PUnit.unit
  exact hcenter.comp (hmomentum.comp hbody)

/-- Unpacking includes all residual leaves and is measurable on the actual compiled tape. -/
theorem measurable_unpackCompiledTape (d : ℕ) (p : Program c τ)
    (e : GaussianSlot p ≃ Fin n) (seedOrigin : Fin n → Origin) :
    Measurable (unpackCompiledTape (d := d) p e seedOrigin) := by
  apply Measurable.prodMk
  · apply Measurable.of_eval
    intro j
    change Measurable (fun w : Tape d (compileWith p e seedOrigin) => (w.2.2.1 j).1)
    fun_prop
  · exact (measurable_restoreReplayTape d (Fin.natAdd (n*n)) p (fun a => nomatch a)
      (fun s => AffineLowering.batchRef (e s)) (compiledCenter n) (compiledMomentum n)).comp
        (show Measurable (fun w : Tape d (compileWith p e seedOrigin) => w.2.2.2.2.2) from
          by fun_prop)

/-- The compiler's existing complete raw-tape equivalence with verified measurability. -/
def compiledTapeMeasurableEquiv (d : ℕ) (p : Program c τ)
    (e : GaussianSlot p ≃ Fin n) (seedOrigin : Fin n → Origin) :
    Tape d (compileWith p e seedOrigin) ≃ᵐ ((Fin n → Point d) × ResidualTape p) where
  toEquiv := compiledTapeEquivWith p e seedOrigin
  measurable_toFun := measurable_unpackCompiledTape d p e seedOrigin
  measurable_invFun := (packCompiledTape_preserving d p e seedOrigin).measurable

/-- Actual compiled sampling semantics gives the full product law claimed in V2,
including the original child's actual residual law. -/
theorem unpackCompiledTape_preserving (d : ℕ) (p : Program c τ)
    (e : GaussianSlot p ≃ Fin n) (seedOrigin : Fin n → Origin) :
    MeasurePreserving (compiledTapeMeasurableEquiv d p e seedOrigin)
      (tapeLaw d (compileWith p e seedOrigin))
      ((Measure.pi (fun _ : Fin n => stdGaussian (Point d))).prod (residualLaw p)) :=
  (show MeasurePreserving (compiledTapeMeasurableEquiv d p e seedOrigin).symm _ _ from
    packCompiledTape_preserving d p e seedOrigin).symm

end AcceleratedLogConcave.Probability.MixedResidualTape
