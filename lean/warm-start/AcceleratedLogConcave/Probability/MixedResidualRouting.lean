import AcceleratedLogConcave.Probability.MixedResidualTape

/-! Probability-level identification of the actual structural split and join maps.
The raw tape is the recursively defined independent-instruction measure, not a law
postulated on a chosen tape equivalence. -/

noncomputable section
open MeasureTheory MeasureTheory.Measure ProbabilityTheory
open scoped ENNReal
namespace AcceleratedLogConcave.Probability.MixedResidualTape
open Oracle Oracle.TapeLowering

private theorem prod_shuffle {A B C D : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]
    (μ : Measure A) (ν : Measure B) (ρ : Measure C) (σ : Measure D)
    [SFinite μ] [SFinite ν] [SFinite ρ] [SFinite σ] :
    MeasurePreserving (fun x : (A × B) × (C × D) => ((x.1.1,x.2.1),(x.1.2,x.2.2)))
      ((μ.prod ν).prod (ρ.prod σ)) ((μ.prod ρ).prod (ν.prod σ)) := by
  have h1 := measurePreserving_prodAssoc μ ν (ρ.prod σ)
  have h2 := (MeasurePreserving.id μ).prod (measurePreserving_prodAssoc ν ρ σ).symm
  have h3 := (MeasurePreserving.id μ).prod
    ((measurePreserving_swap (μ := ν) (ν := ρ)).prod (MeasurePreserving.id σ))
  have h4 := (MeasurePreserving.id μ).prod (measurePreserving_prodAssoc ρ ν σ)
  have h5 := (measurePreserving_prodAssoc μ ρ (ν.prod σ)).symm
  exact h5.comp (h4.comp (h3.comp (h2.comp h1)))

/-- Flattening a finite family of Gaussian inventories preserves its complete joint law. -/
private theorem pi_uncurry {J : Type*} {K : J → Type*} [Fintype J] [∀ j, Fintype (K j)]
    {X : (j : J) → K j → Type*} [∀ j k, MeasurableSpace (X j k)]
    (μ : ∀ j k, Measure (X j k)) [∀ j k, SigmaFinite (μ j k)] :
    MeasurePreserving (MeasurableEquiv.piCurry X).symm
      (Measure.pi (fun j => Measure.pi (μ j))) (Measure.pi (fun s : Σ j, K j => μ s.1 s.2)) := by
  refine ⟨(MeasurableEquiv.piCurry X).symm.measurable, ?_⟩
  refine (Measure.pi_eq (fun s hs => ?_)).symm
  rw [Measure.map_apply (MeasurableEquiv.piCurry X).symm.measurable (.univ_pi hs)]
  have he : (MeasurableEquiv.piCurry X).symm ⁻¹' Set.univ.pi s =
      Set.univ.pi (fun j => Set.univ.pi (fun k => s ⟨j,k⟩)) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left]
    exact ⟨fun h j k => h ⟨j,k⟩, fun h s => h s.1 s.2⟩
  rw [he, Measure.pi_pi]
  simp only [Measure.pi_pi, Fintype.prod_sigma]

/-- Dependent pairs of full tapes keep independence between the two complete inventories. -/
private theorem pi_prod {J : Type*} [Fintype J] {A B : J → Type*}
    [∀ j, MeasurableSpace (A j)] [∀ j, MeasurableSpace (B j)]
    (μ : ∀ j, Measure (A j)) (ν : ∀ j, Measure (B j))
    [∀ j, SigmaFinite (μ j)] [∀ j, SigmaFinite (ν j)] :
    MeasurePreserving (fun x : (∀ j, A j) × (∀ j, B j) => fun j => (x.1 j, x.2 j))
      ((Measure.pi μ).prod (Measure.pi ν)) (Measure.pi (fun j => (μ j).prod (ν j))) := by
  let e : (∀ j, A j × B j) ≃ᵐ ((∀ j, A j) × (∀ j, B j)) :=
    ⟨⟨fun x => (fun j => (x j).1, fun j => (x j).2),
      fun x j => (x.1 j, x.2 j), fun _ => rfl, fun _ => rfl⟩,
      by change Measurable (fun x : ∀ j, A j × B j =>
        (fun j => (x j).1, fun j => (x j).2)); fun_prop,
      by change Measurable (fun x : (∀ j, A j) × (∀ j, B j) =>
        fun j => (x.1 j, x.2 j)); fun_prop⟩
  suffices h : MeasurePreserving e (Measure.pi (fun j => (μ j).prod (ν j)))
      ((Measure.pi μ).prod (Measure.pi ν)) from h.symm
  refine ⟨e.measurable, ?_⟩
  refine (FiniteSpanningSetsIn.ext ?_ (isPiSystem_pi.prod isPiSystem_pi)
    ((FiniteSpanningSetsIn.pi fun j => (μ j).toFiniteSpanningSetsIn).prod
      (FiniteSpanningSetsIn.pi fun j => (ν j).toFiniteSpanningSetsIn)) ?_).symm
  · refine (generateFrom_eq_prod generateFrom_pi generateFrom_pi ?_ ?_).symm
    · exact (FiniteSpanningSetsIn.pi fun j => (μ j).toFiniteSpanningSetsIn).isCountablySpanning
    · exact (FiniteSpanningSetsIn.pi fun j => (ν j).toFiniteSpanningSetsIn).isCountablySpanning
  · rintro _ ⟨s, ⟨s, _, rfl⟩, ⟨_, ⟨t, _, rfl⟩, rfl⟩⟩
    rw [e.map_apply]
    have he : e ⁻¹' (Set.univ.pi s ×ˢ Set.univ.pi t) =
        Set.univ.pi (fun j => s j ×ˢ t j) := by
      ext x
      simp [e, Set.mem_pi, forall_and]
    rw [he]
    simp_rw [Measure.pi_pi, Measure.prod_prod, Measure.pi_pi, Finset.prod_mul_distrib]

private def joinInstr (d : ℕ) (i : Instr c Γ τ)
    (zr : (InstrGaussianSlot i → Point d) × InstrResidualTape i) : i.Tape d :=
  match i with
  | .gaussian => zr.1 PUnit.unit
  | .uniform => zr.2
  | .pure _ | .center | .momentum | .grad _ => PUnit.unit

private theorem joinInstr_preserving (d : ℕ) (i : Instr c Γ τ) :
    MeasurePreserving (joinInstr d i)
      ((Measure.pi (fun _ : InstrGaussianSlot i => stdGaussian (Point d))).prod
        (instrResidualLaw i)) (instrLaw d i) := by
  cases i with
  | gaussian =>
      exact (measurePreserving_eval (fun _ : PUnit => stdGaussian (Point d)) PUnit.unit).comp
        (measurePreserving_fst (μ := Measure.pi (fun _ : PUnit => stdGaussian (Point d)))
          (ν := Measure.dirac PUnit.unit))
  | uniform =>
      change MeasurePreserving Prod.snd ((Measure.pi (fun _ : PEmpty =>
        stdGaussian (Point d))).prod uniformLaw) uniformLaw
      exact measurePreserving_snd
  | _ =>
      exact (measurePreserving_snd (μ := Measure.pi (fun _ : PEmpty =>
        stdGaussian (Point d))) (ν := Measure.dirac PUnit.unit)).congr
        measurable_const (ae_of_all _ fun _ => Subsingleton.elim _ _)

/-- The actual raw instruction product law splits into independent Gaussian inventory
and full residual law. Every raw tape coordinate is covered by the existing bijection. -/
theorem joinTape_preserving (d : ℕ) (p : Prog c Γ τ) :
    MeasurePreserving (fun zr : (GaussianSlot p → Point d) × ResidualTape p =>
      joinTape p zr.1 zr.2)
      ((Measure.pi (fun _ : GaussianSlot p => stdGaussian (Point d))).prod (residualLaw p))
      (tapeLaw d p) := by
  induction p with
  | ret _ =>
      exact (measurePreserving_snd (μ := Measure.pi (fun _ : PEmpty =>
        stdGaussian (Point d))) (ν := Measure.dirac PUnit.unit)).congr
        measurable_const (ae_of_all _ fun _ => Subsingleton.elim _ _)
  | step origin i next ih =>
      have h1 := (measurePreserving_sumPiEquivProdPi
        (fun _ : InstrGaussianSlot i ⊕ GaussianSlot next => stdGaussian (Point d))).prod
          (MeasurePreserving.id ((instrResidualLaw i).prod (residualLaw next)))
      have h2 := prod_shuffle
        (Measure.pi (fun _ : InstrGaussianSlot i => stdGaussian (Point d)))
        (Measure.pi (fun _ : GaussianSlot next => stdGaussian (Point d)))
        (instrResidualLaw i) (residualLaw next)
      have h3 := (joinInstr_preserving d i).prod ih
      cases i <;> exact h3.comp (h2.comp h1)

  | batch origin children next ihc ihn =>
      have h1 := (measurePreserving_sumPiEquivProdPi
        (fun _ : (Σ j, GaussianSlot (children j)) ⊕ GaussianSlot next =>
          stdGaussian (Point d))).prod
        (MeasurePreserving.id ((Measure.pi (fun j => residualLaw (children j))).prod
          (residualLaw next)))
      have h2 := prod_shuffle
        (Measure.pi (fun _ : Σ j, GaussianSlot (children j) => stdGaussian (Point d)))
        (Measure.pi (fun _ : GaussianSlot next => stdGaussian (Point d)))
        (Measure.pi (fun j => residualLaw (children j))) (residualLaw next)
      have hcurry := (pi_uncurry (X := fun j (_ : GaussianSlot (children j)) => Point d)
        (fun _ _ => stdGaussian (Point d))).symm
      have h3 := (hcurry.prod (MeasurePreserving.id (Measure.pi (fun j =>
        residualLaw (children j))))).prod
        (MeasurePreserving.id ((Measure.pi (fun _ : GaussianSlot next => stdGaussian (Point d))).prod
          (residualLaw next)))
      have h4 := (pi_prod (fun j => Measure.pi (fun _ : GaussianSlot (children j) =>
        stdGaussian (Point d))) (fun j => residualLaw (children j))).prod
        (MeasurePreserving.id ((Measure.pi (fun _ : GaussianSlot next => stdGaussian (Point d))).prod
          (residualLaw next)))
      have h5 := (measurePreserving_pi _ _ ihc).prod ihn
      exact h5.comp (h4.comp (h3.comp (h2.comp h1)))

/-- Full probability-level split, including all actual uniform/unit residual coordinates. -/
theorem splitTape_preserving (d : ℕ) (p : Prog c Γ τ) :
    MeasurePreserving (splitGaussianMeasurableEquiv d p) (tapeLaw d p)
      ((Measure.pi (fun _ : GaussianSlot p => stdGaussian (Point d))).prod (residualLaw p)) :=
  (show MeasurePreserving (splitGaussianMeasurableEquiv d p).symm _ _ from
    joinTape_preserving d p).symm

/-- Finite enumeration preserves the entire Gaussian inventory and the actual residual. -/
theorem enumeratedSplit_preserving (d : ℕ) (p : Prog c Γ τ)
    (e : GaussianSlot p ≃ Fin N) :
    MeasurePreserving (fun w : Tape d p =>
      ((fun j => (splitTape p w).1 (e.symm j)), (splitTape p w).2)) (tapeLaw d p)
      ((Measure.pi (fun _ : Fin N => stdGaussian (Point d))).prod (residualLaw p)) :=
  by
  have h := ((measurePreserving_piCongrLeft (fun _ : Fin N => stdGaussian (Point d)) e).prod
    (MeasurePreserving.id (residualLaw p))).comp (splitTape_preserving d p)
  convert h using 1
  funext w
  apply Prod.ext
  · funext j
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply,
      splitGaussianMeasurableEquiv, splitGaussianTape]
  · rfl

/-- Reconstructing from the fixed finite enumeration has the actual raw source tape law. -/
theorem enumeratedJoin_preserving (d : ℕ) (p : Prog c Γ τ)
    (e : GaussianSlot p ≃ Fin N) :
    MeasurePreserving (fun zr : (Fin N → Point d) × ResidualTape p =>
      joinTape p (fun s => zr.1 (e s)) zr.2)
      ((Measure.pi (fun _ : Fin N => stdGaussian (Point d))).prod (residualLaw p))
      (tapeLaw d p) := by
  have h := (joinTape_preserving d p).comp
    ((measurePreserving_piCongrLeft (fun _ : GaussianSlot p => stdGaussian (Point d))
      e.symm).prod (MeasurePreserving.id (residualLaw p)))
  convert h using 1
  funext zr
  apply congrArg (fun z => joinTape p z zr.2)
  funext s
  simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]

/-- Actual standalone designated input and full tape law for independent instructions. -/
def standaloneLaw (d : ℕ) (p : Prog c Γ τ) : Measure (Point d × Tape d p) :=
  (stdGaussian (Point d)).prod (tapeLaw d p)

instance standaloneLaw_probability (d : ℕ) (p : Prog c Γ τ) :
    IsProbabilityMeasure (standaloneLaw d p) := by
  unfold standaloneLaw
  infer_instance

/-- Product specialization (P) follows for the independently sampled source semantics,
including every residual coordinate, with its literal fixed enumeration. This does not
identify a compiler's coupled final-call law or its conditional outside sigma-algebra. -/
theorem standaloneLaw_full_split (d : ℕ) (p : Prog c Γ τ)
    (e : GaussianSlot p ≃ Fin N) :
    (standaloneLaw d p).map (fun pw =>
      (pw.1, (fun j => (splitTape p pw.2).1 (e.symm j)), (splitTape p pw.2).2)) =
      (stdGaussian (Point d)).prod
        ((Measure.pi (fun _ : Fin N => stdGaussian (Point d))).prod (residualLaw p)) :=
  ((MeasurePreserving.id (stdGaussian (Point d))).prod
    (enumeratedSplit_preserving d p e)).map_eq

end AcceleratedLogConcave.Probability.MixedResidualTape
