import AcceleratedLogConcave.Oracle.SamplingCanonicalTapeLaw

/-!
Factor the already-defined recursive product law through the EXISTING splitTape.
The desired factorization is a theorem conclusion, never a definition or premise.
All helpers below are explicit coordinate permutations or their measure proofs.
The dependent child family and real continuation are both retained. Empty child
families, absent Gaussian slots, and dimension zero require no special premise.

No evaluator, tape, residual carrier, GaussianSlot, splitTape or joinTape changes.
No global instances; no external-source, random-warm-input, coupling or accuracy
claim. Every result, including inherited suppliers, still requires compilation.
-/
noncomputable section
namespace AcceleratedLogConcave.Oracle
namespace CanonicalTapeFactorization
open MeasureTheory MeasureTheory.Measure TapeLowering CanonicalTapeMeasurability CanonicalTapeLaw
open scoped BigOperators

section ProductCoordinates

variable {A B C D : Type*}
  [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]

/-- Explicit four-coordinate permutation: no coordinate is discarded. -/
def regroup : (A × B) × (C × D) → (A × C) × (B × D) :=
  fun q => ((q.1.1, q.2.1), (q.1.2, q.2.2))

/-- Derive the permutation law from product associativity and symmetry. -/
theorem measurePreserving_regroup (μ : Measure A) (ν : Measure B)
    (κ : Measure C) (ρ : Measure D)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsProbabilityMeasure κ] [IsProbabilityMeasure ρ] :
    MeasurePreserving regroup ((μ.prod ν).prod (κ.prod ρ))
      ((μ.prod κ).prod (ν.prod ρ)) := by
  have h1 := measurePreserving_prodAssoc μ ν (κ.prod ρ)
  have h2 := (MeasurePreserving.id μ).prod
    ((measurePreserving_prodAssoc ν κ ρ).symm MeasurableEquiv.prodAssoc)
  have h3 := (MeasurePreserving.id μ).prod
    ((measurePreserving_swap (μ := ν) (ν := κ)).prod (MeasurePreserving.id ρ))
  have h4 := (MeasurePreserving.id μ).prod (measurePreserving_prodAssoc κ ν ρ)
  have h5 := (measurePreserving_prodAssoc μ κ (ν.prod ρ)).symm
    MeasurableEquiv.prodAssoc
  exact h5.comp (h4.comp (h3.comp (h2.comp h1)))

end ProductCoordinates

section FiniteCoordinates

variable {ι : Type*} [Fintype ι] {A B : ι → Type*}
  [∀ i, MeasurableSpace (A i)] [∀ i, MeasurableSpace (B i)]

/-- Dependent child-pair separation. The nondependent upstream arrow lemma
does not suffice for syntax-dependent child tape/residual types. -/
def childPairsEquiv : (∀ i, A i × B i) ≃ᵐ ((∀ i, A i) × (∀ i, B i)) where
  toEquiv :=
    { toFun := fun q => (fun i => (q i).1, fun i => (q i).2)
      invFun := fun q i => (q.1 i, q.2 i)
      left_inv := by intro q; funext i; exact Prod.eta (q i)
      right_inv := by intro q; cases q; rfl }
  measurable_toFun :=
    (measurable_pi_iff.mpr fun i => (measurable_pi_apply i).fst).prodMk
      (measurable_pi_iff.mpr fun i => (measurable_pi_apply i).snd)
  measurable_invFun := measurable_pi_iff.mpr fun i =>
    ((measurable_pi_apply i).comp measurable_fst).prodMk
      ((measurable_pi_apply i).comp measurable_snd)

/-- Prove the dependent separation on generating Pi rectangles. This is not
an assumed independence theorem for a child execution or an arbitrary source. -/
theorem measurePreserving_childPairs (μ : ∀ i, Measure (A i))
    (ν : ∀ i, Measure (B i)) [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)] :
    MeasurePreserving (childPairsEquiv (A := A) (B := B))
      (Measure.pi fun i => (μ i).prod (ν i)) ((Measure.pi μ).prod (Measure.pi ν)) where
  measurable := childPairsEquiv.measurable
  map_eq := by
    refine (FiniteSpanningSetsIn.ext ?_ (isPiSystem_pi.prod isPiSystem_pi)
      ((FiniteSpanningSetsIn.pi fun i => (μ i).toFiniteSpanningSetsIn).prod
        (FiniteSpanningSetsIn.pi fun i => (ν i).toFiniteSpanningSetsIn)) ?_).symm
    · refine (generateFrom_eq_prod generateFrom_pi generateFrom_pi ?_ ?_).symm
      · exact (FiniteSpanningSetsIn.pi fun i => (μ i).toFiniteSpanningSetsIn).isCountablySpanning
      · exact (FiniteSpanningSetsIn.pi fun i => (ν i).toFiniteSpanningSetsIn).isCountablySpanning
    · rintro _ ⟨s, ⟨s, _, rfl⟩, ⟨_, ⟨t, _, rfl⟩, rfl⟩⟩
      rw [MeasurableEquiv.map_apply]
      have hp : (childPairsEquiv (A := A) (B := B)) ⁻¹'
          (Set.pi Set.univ s ×ˢ Set.pi Set.univ t) =
            Set.pi Set.univ (fun i => s i ×ˢ t i) := by
        ext q
        simp [childPairsEquiv, Set.mem_pi, forall_and]
      rw [hp]
      simp_rw [Measure.pi_pi, Measure.prod_prod, Measure.pi_pi,
        Finset.prod_mul_distrib]

end FiniteCoordinates

section SigmaCoordinates

variable {ι : Type*} [Fintype ι] {κ : ι → Type*} [∀ i, Fintype (κ i)]
  {X : Type*} [MeasurableSpace X]

/-- Flatten every child Gaussian occurrence via the exact Sigma coordinate.
The proof includes an empty outer family and empty individual child families. -/
theorem measurePreserving_sigmaUncurry (μ : Measure X) [IsProbabilityMeasure μ] :
    MeasurePreserving (MeasurableEquiv.piCurry (fun (i : ι) (_ : κ i) => X)).symm
      (Measure.pi fun i => Measure.pi fun _ : κ i => μ)
      (Measure.pi fun _ : Sigma κ => μ) where
  measurable := (MeasurableEquiv.piCurry (fun (i : ι) (_ : κ i) => X)).symm.measurable
  map_eq := by
    refine (Measure.pi_eq fun s _ => ?_).symm
    rw [MeasurableEquiv.map_apply]
    have hp : (MeasurableEquiv.piCurry (fun (i : ι) (_ : κ i) => X)).symm ⁻¹'
        Set.pi Set.univ s =
          Set.pi Set.univ (fun i => Set.pi Set.univ (fun j => s ⟨i, j⟩)) := by
      ext q
      simp [MeasurableEquiv.coe_piCurry_symm, Set.mem_pi, Sigma.forall, Sigma.uncurry]
    rw [hp, Measure.pi_pi]
    simp_rw [Measure.pi_pi]
    exact (Fintype.prod_sigma (fun ij : Sigma κ => μ (s ij))).symm

end SigmaCoordinates

section SumCoordinates

variable {ι κ X R S : Type*} [Fintype ι] [Fintype κ]
  [MeasurableSpace X] [MeasurableSpace R] [MeasurableSpace S]

/-- The literal left/right routing used by splitTape at every syntax seam. -/
def combine : ((ι → X) × R) × ((κ → X) × S) → ((ι ⊕ κ → X) × (R × S)) :=
  fun q => (Sum.elim q.1.1 q.2.1, (q.1.2, q.2.2))

theorem measurePreserving_combine (μ : Measure X) (ν : Measure R) (ρ : Measure S)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ] :
    MeasurePreserving (combine (ι := ι) (κ := κ))
      (((Measure.pi fun _ : ι => μ).prod ν).prod
        ((Measure.pi fun _ : κ => μ).prod ρ))
      ((Measure.pi fun _ : ι ⊕ κ => μ).prod (ν.prod ρ)) := by
  have hs := (measurePreserving_sumPiEquivProdPi_symm
    (fun _ : ι ⊕ κ => μ)).prod (MeasurePreserving.id (ν.prod ρ))
  exact hs.comp (measurePreserving_regroup
    (Measure.pi fun _ : ι => μ) ν (Measure.pi fun _ : κ => μ) ρ)

end SumCoordinates

/-- Explicit instruction coordinate map, used only to expose the primitive
calculation. Agreement with the original private instruction helpers is checked
by cases in the complete splitTape induction below. -/
def splitInstr (instr : Instr c Γ τ) (ω : instr.Tape d) :
    (InstrGaussianSlot instr → Point d) × InstrResidualTape instr :=
  match instr with
  | .gaussian => ((fun _ => ω), PUnit.unit)
  | .uniform => ((fun s => nomatch s), ω)
  | .pure _ | .center | .momentum | .grad _ =>
      ((fun s => nomatch s), PUnit.unit)

theorem measurePreserving_splitInstr (L : PrimitiveLaws d) (instr : Instr c Γ τ) :
    let : MeasurableSpace (instr.Tape d) := instrSpace d instr
    let : MeasurableSpace (InstrResidualTape instr) := instrResidualSpace instr
    MeasurePreserving (splitInstr (d := d) instr) (instrLaw L instr)
      ((Measure.pi fun _ : InstrGaussianSlot instr => L.pointDraw).prod
        (instrResidualLaw L.uniformDraw instr)) := by
  let : IsProbabilityMeasure L.pointDraw := L.point_probability
  let : IsProbabilityMeasure L.uniformDraw := L.uniform_probability
  let : MeasurableSpace (instr.Tape d) := instrSpace d instr
  let : MeasurableSpace (InstrResidualTape instr) := instrResidualSpace instr
  dsimp only
  cases instr with
  | gaussian =>
      change MeasurePreserving (fun x : Point d => ((fun _ : PUnit.{1} => x), PUnit.unit)) L.pointDraw
        ((Measure.pi fun _ : PUnit.{1} => L.pointDraw).prod (Measure.dirac (α := PUnit.{1}) PUnit.unit))
      have hc := (measurePreserving_funUnique L.pointDraw PUnit.{1}).symm
        (MeasurableEquiv.funUnique PUnit (Point d))
      have hu : MeasurePreserving (fun z : PUnit → Point d => (z, PUnit.unit))
          (Measure.pi fun _ : PUnit.{1} => L.pointDraw)
          ((Measure.pi fun _ : PUnit.{1} => L.pointDraw).prod (Measure.dirac (α := PUnit.{1}) PUnit.unit)) :=
        ⟨measurable_id.prodMk measurable_const, (Measure.prod_dirac PUnit.unit).symm⟩
      exact hu.comp hc
  | uniform =>
      have h : MeasurePreserving (fun u : UniformValue =>
          ((fun s : PEmpty.{1} => nomatch s), u)) L.uniformDraw
          ((Measure.pi fun _ : PEmpty.{1} => L.pointDraw).prod L.uniformDraw) := by
        rw [Measure.pi_of_empty (x := fun s : PEmpty.{1} => nomatch s)]
        exact ⟨measurable_const.prodMk measurable_id, (Measure.dirac_prod _).symm⟩
      convert h using 1 <;> first | rfl | (apply heq_of_eq; funext ω; apply Prod.ext <;> first | rfl | (funext s; cases s))
  | pure p | center | momentum | grad r =>
      have h : MeasurePreserving (fun _ : PUnit.{1} =>
          ((fun s : PEmpty.{1} => nomatch s), PUnit.unit))
          (Measure.dirac (α := PUnit.{1}) PUnit.unit)
          ((Measure.pi fun _ : PEmpty.{1} => L.pointDraw).prod
            (Measure.dirac (α := PUnit.{1}) PUnit.unit)) := by
        constructor
        · exact measurable_const
        · rw [Measure.pi_of_empty (x := fun s : PEmpty.{1} => nomatch s),
            Measure.dirac_prod_dirac, Measure.map_dirac' measurable_const]
      convert h using 1 <;> first | rfl | (apply heq_of_eq; funext ω; apply Prod.ext <;> first | rfl | (funext s; cases s))


/-- Main syntax induction. All primitive, child and continuation measures are
the recursive laws from the supplier, not new factorization hypotheses. -/
theorem measurePreserving_splitTape (L : PrimitiveLaws d) (p : Prog c Γ τ) :
    let : MeasurableSpace (Tape d p) := tapeSpace d p
    let : MeasurableSpace (ResidualTape p) := residualSpace p
    MeasurePreserving (splitTape (d := d) p) (tapeLaw L p)
      ((Measure.pi fun _ : GaussianSlot p => L.pointDraw).prod
        (residualLaw L.uniformDraw p)) := by
  let : IsProbabilityMeasure L.pointDraw := L.point_probability
  let : IsProbabilityMeasure L.uniformDraw := L.uniform_probability
  induction p with
  | ret r =>
      have h : MeasurePreserving (fun _ : PUnit.{1} =>
          ((fun s : PEmpty.{1} => nomatch s), PUnit.unit))
          (Measure.dirac (α := PUnit.{1}) PUnit.unit)
          ((Measure.pi fun _ : PEmpty.{1} => L.pointDraw).prod
            (Measure.dirac (α := PUnit.{1}) PUnit.unit)) := by
        constructor
        · exact measurable_const
        · rw [Measure.pi_of_empty (x := fun s : PEmpty.{1} => nomatch s),
            Measure.dirac_prod_dirac, Measure.map_dirac' measurable_const]
      dsimp only
      convert h using 1 <;> first | rfl | (apply heq_of_eq; funext ω; apply Prod.ext <;> first | rfl | (funext s; cases s))
  | step origin instr next ih =>
      let : MeasurableSpace (instr.Tape d) := instrSpace d instr
      let : MeasurableSpace (InstrResidualTape instr) := instrResidualSpace instr
      let : MeasurableSpace (Tape d next) := tapeSpace d next
      let : MeasurableSpace (ResidualTape next) := residualSpace next
      let : IsProbabilityMeasure (instrLaw L instr) := instrLaw_probability L instr
      let : IsProbabilityMeasure (tapeLaw L next) := tapeLaw_probability L next
      let : IsProbabilityMeasure (instrResidualLaw L.uniformDraw instr) :=
        instrResidualLaw_probability L.uniformDraw instr
      let : IsProbabilityMeasure (residualLaw L.uniformDraw next) :=
        residualLaw_probability L.uniformDraw next
      have h := (measurePreserving_combine (ι := InstrGaussianSlot instr)
        (κ := GaussianSlot next) L.pointDraw (instrResidualLaw L.uniformDraw instr)
        (residualLaw L.uniformDraw next)).comp
          ((measurePreserving_splitInstr L instr).prod ih)
      let : MeasurableSpace (Tape d (.step origin instr next)) := tapeSpace d _
      let : MeasurableSpace (ResidualTape (.step origin instr next)) := residualSpace _
      change MeasurePreserving
        (fun ω : Tape d (.step origin instr next) =>
          combine (splitInstr instr ω.1, splitTape next ω.2))
        (tapeLaw L (.step origin instr next))
        ((Measure.pi fun _ : GaussianSlot (.step origin instr next) => L.pointDraw).prod
          (residualLaw L.uniformDraw (.step origin instr next))) at h
      have hf : (fun ω : Tape d (.step origin instr next) =>
          combine (splitInstr instr ω.1, splitTape next ω.2)) =
            splitTape (d := d) (.step origin instr next) := by
        funext ω
        cases instr <;> rfl
      rw [hf] at h
      exact h
  | batch origin children next ihChildren ihNext =>
      let : ∀ j, MeasurableSpace (Tape d (children j)) :=
        fun j => tapeSpace d (children j)
      let : ∀ j, MeasurableSpace (ResidualTape (children j)) :=
        fun j => residualSpace (children j)
      let : MeasurableSpace (Tape d next) := tapeSpace d next
      let : MeasurableSpace (ResidualTape next) := residualSpace next
      let : ∀ j, IsProbabilityMeasure (tapeLaw L (children j)) :=
        fun j => tapeLaw_probability L (children j)
      let : ∀ j, IsProbabilityMeasure (residualLaw L.uniformDraw (children j)) :=
        fun j => residualLaw_probability L.uniformDraw (children j)
      let : IsProbabilityMeasure (tapeLaw L next) := tapeLaw_probability L next
      let : IsProbabilityMeasure (residualLaw L.uniformDraw next) :=
        residualLaw_probability L.uniformDraw next
      have hc := measurePreserving_pi
        (fun j => tapeLaw L (children j))
        (fun j => (Measure.pi fun _ : GaussianSlot (children j) => L.pointDraw).prod
          (residualLaw L.uniformDraw (children j))) ihChildren
      have hu := measurePreserving_childPairs
        (fun j => Measure.pi fun _ : GaussianSlot (children j) => L.pointDraw)
        (fun j => residualLaw L.uniformDraw (children j))
      have hs := (measurePreserving_sigmaUncurry
        (κ := fun j => GaussianSlot (children j)) L.pointDraw).prod
          (MeasurePreserving.id (Measure.pi fun j => residualLaw L.uniformDraw (children j)))
      have hchildren := hs.comp (hu.comp hc)
      have h := (measurePreserving_combine
        (ι := Sigma fun j => GaussianSlot (children j)) (κ := GaussianSlot next)
        L.pointDraw (Measure.pi fun j => residualLaw L.uniformDraw (children j))
        (residualLaw L.uniformDraw next)).comp (hchildren.prod ihNext)
      exact h

/-- Factorization is derived from the previous induction through the exact
existing measurable split equivalence, not inserted into splitLaw's definition. -/
theorem splitLaw_eq_product (L : PrimitiveLaws d) (p : Prog c Γ τ) :
    let : MeasurableSpace (ResidualTape p) := residualSpace p
    splitLaw L p = (Measure.pi fun _ : GaussianSlot p => L.pointDraw).prod
      (residualLaw L.uniformDraw p) := by
  let : MeasurableSpace (Tape d p) := tapeSpace d p
  let : MeasurableSpace (ResidualTape p) := residualSpace p
  exact (measurePreserving_splitTape L p).map_eq

/-- The recursively constructed residual is now identified as the extracted
residual marginal of the full tape law, not merely separately normalized. -/
theorem map_residual_tapeLaw (L : PrimitiveLaws d) (p : Prog c Γ τ) :
    let : MeasurableSpace (Tape d p) := tapeSpace d p
    let : MeasurableSpace (ResidualTape p) := residualSpace p
    (tapeLaw L p).map (fun ω => (splitTape p ω).2) = residualLaw L.uniformDraw p := by
  let : MeasurableSpace (Tape d p) := tapeSpace d p
  let : MeasurableSpace (ResidualTape p) := residualSpace p
  let : IsProbabilityMeasure L.pointDraw := L.point_probability
  let : IsProbabilityMeasure L.uniformDraw := L.uniform_probability
  let : IsProbabilityMeasure (residualLaw L.uniformDraw p) :=
    residualLaw_probability L.uniformDraw p
  calc
    (tapeLaw L p).map (fun ω => (splitTape p ω).2) =
        (splitLaw L p).map Prod.snd :=
      (Measure.map_map measurable_snd (measurable_splitTape d p)).symm
    _ = residualLaw L.uniformDraw p := by
      rw [splitLaw_eq_product]
      exact Measure.snd_prod

/-- All Gaussian occurrence coordinates have the finite product of the
supplied point law. This does not identify an arbitrary supplied law as Gaussian. -/
theorem map_gaussian_tapeLaw (L : PrimitiveLaws d) (p : Prog c Γ τ) :
    let : MeasurableSpace (Tape d p) := tapeSpace d p
    (tapeLaw L p).map (fun ω => (splitTape p ω).1) =
      Measure.pi fun _ : GaussianSlot p => L.pointDraw := by
  let : MeasurableSpace (Tape d p) := tapeSpace d p
  let : MeasurableSpace (ResidualTape p) := residualSpace p
  let : IsProbabilityMeasure L.uniformDraw := L.uniform_probability
  let : IsProbabilityMeasure (residualLaw L.uniformDraw p) :=
    residualLaw_probability L.uniformDraw p
  calc
    (tapeLaw L p).map (fun ω => (splitTape p ω).1) =
        (splitLaw L p).map Prod.fst :=
      (Measure.map_map measurable_fst (measurable_splitTape d p)).symm
    _ = Measure.pi fun _ : GaussianSlot p => L.pointDraw := by
      rw [splitLaw_eq_product]
      exact Measure.fst_prod

/-- Genuine rectangle independence under the specifically chosen recursive
model. Both entire coordinate blocks are retained; no external RNG is involved. -/
theorem split_rectangle (L : PrimitiveLaws d) (p : Prog c Γ τ)
    (A : Set (GaussianSlot p → Point d)) (B : Set (ResidualTape p)) :
    tapeLaw L p (splitTape p ⁻¹' (A ×ˢ B)) =
      (Measure.pi fun _ : GaussianSlot p => L.pointDraw) A *
        residualLaw L.uniformDraw p B := by
  let : MeasurableSpace (ResidualTape p) := residualSpace p
  let : IsProbabilityMeasure L.uniformDraw := L.uniform_probability
  let : IsProbabilityMeasure (residualLaw L.uniformDraw p) :=
    residualLaw_probability L.uniformDraw p
  rw [← splitLaw_apply, splitLaw_eq_product, Measure.prod_prod]

/-- Existing execution-law transport can now use the proved product, with
the entire residual still varying and the original measurable oracle fixed. -/
theorem program_point_product_law (L : PrimitiveLaws d) (p : Program c .point)
    (G : Point d → Point d) (hG : Measurable G)
    (coeff : Fin c → ℝ) (x P : Point d) :
    let : MeasurableSpace (Tape d p) := tapeSpace d p
    let : MeasurableSpace (ResidualTape p) := residualSpace p
    ((Measure.pi fun _ : GaussianSlot p => L.pointDraw).prod
      (residualLaw L.uniformDraw p)).map (β := Point d) (fun a =>
        (run p G ⟨coeff, x, P⟩ Env.empty (joinTape p a.1 a.2)).value) =
      (tapeLaw L p).map (β := Point d) (fun ω => (run p G ⟨coeff, x, P⟩ Env.empty ω).value) := by
  let : MeasurableSpace (Tape d p) := tapeSpace d p
  let : MeasurableSpace (ResidualTape p) := residualSpace p
  rw [← splitLaw_eq_product]
  exact program_point_split_law L p G hG coeff x P

end CanonicalTapeFactorization
end AcceleratedLogConcave.Oracle
