import AcceleratedLogConcave.Probability.MixedResidualRouting
import AcceleratedLogConcave.Oracle.TerminalMean

/-! The terminal branch's actual independent-instruction tape and retained
execution law. Original P is retained; no Gaussian replacement of residual
coordinates occurs. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Probability.ExecutableTerminalLaw
open Oracle Oracle.TapeLowering MixedResidualTape

private theorem prefixUnit {A : Type*} [MeasurableSpace A] (μ : Measure A) [SFinite μ] :
    MeasurePreserving (fun z => (PUnit.unit,z)) μ ((Measure.dirac PUnit.unit).prod μ) :=
  ⟨by fun_prop, (Measure.dirac_prod PUnit.unit).symm⟩

/-- The single auxiliary point, with every unit leaf kept in place, generates
the full instruction tape with exactly its prescribed product law. -/
theorem terminalTape_preserving (d : ℕ) (origin : Origin) :
    MeasurePreserving (terminalMeanTapeEquiv d origin)
      (stdGaussian (Point d)) (tapeLaw d (terminalMeanProgram origin)) := by
  let Γt : Ctx := [.scalar,.scalar,.scalar,.point,.point]
  let xr : Ref Γt .point := .there (.there (.there (.there .here)))
  let pr : Ref Γt .point := .there (.there (.there .here))
  let rr : Ref Γt .scalar := .there (.there .here)
  let sr : Ref Γt .scalar := .there .here
  let ar : Ref Γt .scalar := .here
  have hbody : MeasurePreserving (terminalMeanBodyTapeEquiv (c := 3) d origin xr pr rr sr ar)
      (stdGaussian (Point d))
      (tapeLaw d (terminalMeanBody (c := 3) origin xr pr rr sr ar)) := by
    refine ⟨?_,?_⟩
    · change Measurable (fun z : Point d =>
        (z,PUnit.unit,PUnit.unit,PUnit.unit,PUnit.unit,PUnit.unit,PUnit.unit,PUnit.unit,PUnit.unit))
      fun_prop
    · change (stdGaussian (Point d)).map (fun z =>
        (z,PUnit.unit,PUnit.unit,PUnit.unit,PUnit.unit,PUnit.unit,PUnit.unit,PUnit.unit,PUnit.unit)) = _
      simp only [terminalMeanBody,tapeLaw,instrLaw,Measure.dirac_prod_dirac]
      exact (Measure.prod_dirac _).symm
  exact (prefixUnit _).comp ((prefixUnit _).comp ((prefixUnit _).comp
    ((prefixUnit _).comp ((prefixUnit _).comp hbody))))

/-- The terminal actual retained law is precisely the counted interpreter under
its standalone full tape law, rather than an unrelated Gaussian realization. -/
theorem terminal_retained_actualLaw {G : Point d → Point d} (hG : Continuous G)
    (origin : Origin) (scale r σ : ℝ) (x : Point d) :
    (standaloneLaw d (terminalMeanProgram origin)).map (fun pw =>
      ((show Point d from (run (terminalMeanProgram origin) G
        (terminalMeanInputs scale r σ x pw.1) Env.empty pw.2).value),pw.1)) =
      terminalMeanActualLaw origin G scale r σ x := by
  have hp := (MeasurePreserving.id (stdGaussian (Point d))).prod
    (terminalTape_preserving d origin)
  unfold standaloneLaw
  erw [← hp.map_eq]
  rw [Measure.map_map]
  · rfl
  · have hm := measurable_terminalMeanRetained_value hG origin scale r σ x
    change Measurable (fun pw : Point d × Tape d (terminalMeanProgram origin) =>
      ((show Point d from (run (terminalMeanProgram origin) G
        (terminalMeanInputs scale r σ x pw.1) Env.empty pw.2).value),pw.1))
    have hinv : Measurable (fun pw : Point d × Tape d (terminalMeanProgram origin) =>
        (pw.1,(terminalMeanTapeEquiv d origin).symm pw.2)) := by
      change Measurable (fun pw : Point d × Tape d (terminalMeanProgram origin) =>
        (pw.1,pw.2.2.2.2.2.2.1))
      fun_prop
    convert hm.comp hinv using 1
    funext pw
    apply Prod.ext
    · congr 1
    · rfl
  · exact hp.measurable

/-- At the terminal branch the exact retained reference uses P'=P. Thus its
full retained pair is diagonal Gaussian under the actual standalone tape law. -/
theorem terminal_retained_reference_diagonal (d : ℕ) (origin : Origin) :
    (standaloneLaw d (terminalMeanProgram origin)).map (fun pw => (pw.1,pw.1)) =
      (stdGaussian (Point d)).map (fun P => (P,P)) := by
  have hf : (standaloneLaw d (terminalMeanProgram origin)).map Prod.fst =
      stdGaussian (Point d) := measurePreserving_fst.map_eq
  rw [← hf,Measure.map_map (by fun_prop) measurable_fst]
  rfl

end AcceleratedLogConcave.Probability.ExecutableTerminalLaw
