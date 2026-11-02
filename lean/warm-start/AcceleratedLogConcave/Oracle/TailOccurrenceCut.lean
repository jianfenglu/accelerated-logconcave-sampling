import AcceleratedLogConcave.Oracle.SamplingCanonicalSplitFactorization

/-! Exact syntax-tail cuts under the EXISTING
recursive tapeLaw. No independence hypothesis; no random variable is resampled.
The focused tape retains the entire current batch and its entire continuation. -/
noncomputable section
namespace AcceleratedLogConcave.Oracle.TailOccurrenceCut
open MeasureTheory CanonicalTapeMeasurability CanonicalTapeLaw
open OperationalMeasurability

inductive TailCut {c : ℕ} {Δ : Ctx} {σ : Ty} (q : Prog c Δ σ) :
    {Γ : Ctx} → {τ : Ty} → Prog c Γ τ → Type where
  | here : TailCut q q
  | step (o : Origin) (a : Instr c Γ ρ) (next : Prog c (ρ :: Γ) τ)
      (tail : TailCut q next) : TailCut q (.step o a next)
  | batch (o : Origin) (children : Fin n → Prog c Γ .point)
      (next : Prog c (List.replicate n .point ++ Γ) τ)
      (tail : TailCut q next) : TailCut q (.batch o children next)

namespace TailCut
variable {c d : ℕ} {Γ Δ : Ctx} {τ σ : Ty} {p : Prog c Γ τ} {q : Prog c Δ σ}

def Prefix (d : ℕ) : {Γ : Ctx} → {τ : Ty} → {p : Prog c Γ τ} → TailCut q p → Type
  | _, _, _, .here => PUnit
  | _, _, _, .step _ a _ t => a.Tape d × Prefix d t
  | _, _, _, .batch _ children _ t => (∀ i, Tape d (children i)) × Prefix d t

@[instance_reducible] def prefixSpace (d : ℕ) :
    {Γ : Ctx} → {τ : Ty} → {p : Prog c Γ τ} → (t : TailCut q p) → MeasurableSpace (Prefix d t)
  | _, _, _, .here => inferInstanceAs (MeasurableSpace PUnit)
  | _, _, _, .step _ a _ t => (instrSpace d a).prod (prefixSpace d t)
  | _, _, _, .batch _ children _ t =>
      let : ∀ i, MeasurableSpace (Tape d (children i)) := fun i => tapeSpace d (children i)
      (inferInstance : MeasurableSpace (∀ i, Tape d (children i))).prod (prefixSpace d t)

def prefixLaw (L : PrimitiveLaws d) :
    {Γ : Ctx} → {τ : Ty} → {p : Prog c Γ τ} → (t : TailCut q p) →
      @Measure (Prefix d t) (prefixSpace d t)
  | _, _, _, .here =>
      let : MeasurableSpace PUnit := inferInstance
      (show Measure PUnit from Measure.dirac PUnit.unit)
  | _, _, _, .step _ a _ t =>
      let : MeasurableSpace (a.Tape d) := instrSpace d a
      let : MeasurableSpace (Prefix d t) := prefixSpace d t
      (instrLaw L a).prod (prefixLaw L t)
  | _, _, _, .batch _ children _ t =>
      let : ∀ i, MeasurableSpace (Tape d (children i)) := fun i => tapeSpace d (children i)
      let : MeasurableSpace (Prefix d t) := prefixSpace d t
      (Measure.pi fun i => tapeLaw L (children i)).prod (prefixLaw L t)

def split : {Γ : Ctx} → {τ : Ty} → {p : Prog c Γ τ} →
    (t : TailCut q p) → Tape d p → Prefix d t × Tape d q
  | _, _, _, .here, ω => (PUnit.unit, ω)
  | _, _, _, .step _ _ _ t, ω => let z := split t ω.2; ((ω.1,z.1),z.2)
  | _, _, _, .batch _ _ _ t, ω => let z := split t ω.2; ((ω.1,z.1),z.2)

def join : {Γ : Ctx} → {τ : Ty} → {p : Prog c Γ τ} →
    (t : TailCut q p) → Prefix d t × Tape d q → Tape d p
  | _, _, _, .here, z => z.2
  | _, _, _, .step _ _ _ t, z => (z.1.1, join t (z.1.2,z.2))
  | _, _, _, .batch _ _ _ t, z => (z.1.1, join t (z.1.2,z.2))

theorem join_split (t : TailCut q p) (ω : Tape d p) : join t (split t ω) = ω := by
  induction t with
  | here => rfl
  | step o a next t ih => cases ω; simp only [split, join, ih]; rfl
  | batch o children next t ih => cases ω; simp only [split, join, ih]; rfl

theorem split_join (t : TailCut q p) (z : Prefix d t × Tape d q) : split t (join t z) = z := by
  induction t with
  | here => rcases z with ⟨⟨⟩, z⟩; rfl
  | step o a next t ih => rcases z with ⟨⟨h,r⟩,z⟩; simp only [split, join, ih]
  | batch o children next t ih => rcases z with ⟨⟨h,r⟩,z⟩; simp only [split, join, ih]

theorem measurable_join (t : TailCut q p) :
    let : MeasurableSpace (Prefix d t) := prefixSpace d t
    let : MeasurableSpace (Tape d q) := tapeSpace d q
    let : MeasurableSpace (Tape d p) := tapeSpace d p
    Measurable (join (d := d) t) := by
  induction t with
  | here => exact measurable_snd
  | step o a next t ih =>
      let : MeasurableSpace (a.Tape d) := instrSpace d a
      let : MeasurableSpace (Prefix d t) := prefixSpace d t
      let : MeasurableSpace (Tape d q) := tapeSpace d q
      let : MeasurableSpace (Tape d next) := tapeSpace d next
      exact measurable_fst.fst.prodMk (ih.comp (measurable_fst.snd.prodMk measurable_snd))
  | batch o children next t ih =>
      let : ∀ i, MeasurableSpace (Tape d (children i)) := fun i => tapeSpace d (children i)
      let : MeasurableSpace (Prefix d t) := prefixSpace d t
      let : MeasurableSpace (Tape d q) := tapeSpace d q
      let : MeasurableSpace (Tape d next) := tapeSpace d next
      exact measurable_fst.fst.prodMk (ih.comp (measurable_fst.snd.prodMk measurable_snd))

theorem prefixLaw_probability (L : PrimitiveLaws d) (t : TailCut q p) :
    let : MeasurableSpace (Prefix d t) := prefixSpace d t
    IsProbabilityMeasure (prefixLaw L t) := by
  induction t with
  | here => change IsProbabilityMeasure (Measure.dirac PUnit.unit); infer_instance
  | step o a next t ih =>
      let : MeasurableSpace (a.Tape d) := instrSpace d a
      let : MeasurableSpace (Prefix d t) := prefixSpace d t
      let : IsProbabilityMeasure (instrLaw L a) := instrLaw_probability L a
      let : IsProbabilityMeasure (prefixLaw L t) := ih
      change IsProbabilityMeasure ((instrLaw L a).prod (prefixLaw L t)); infer_instance
  | batch o children next t ih =>
      let : ∀ i, MeasurableSpace (Tape d (children i)) := fun i => tapeSpace d (children i)
      let : MeasurableSpace (Prefix d t) := prefixSpace d t
      let : ∀ i, IsProbabilityMeasure (tapeLaw L (children i)) := fun i => tapeLaw_probability L _
      let : IsProbabilityMeasure (prefixLaw L t) := ih
      change IsProbabilityMeasure ((Measure.pi fun i => tapeLaw L (children i)).prod (prefixLaw L t))
      infer_instance

/-- Product law is a conclusion derived from recursive tapeLaw, not a premise. -/
theorem measurePreserving_split (L : PrimitiveLaws d) (t : TailCut q p) :
    let : MeasurableSpace (Tape d p) := tapeSpace d p
    let : MeasurableSpace (Tape d q) := tapeSpace d q
    let : MeasurableSpace (Prefix d t) := prefixSpace d t
    MeasurePreserving (split t) (tapeLaw L p) ((prefixLaw L t).prod (tapeLaw L q)) := by
  induction t with
  | here =>
      let : MeasurableSpace (Tape d q) := tapeSpace d q
      let : IsProbabilityMeasure (tapeLaw L q) := tapeLaw_probability L q
      change MeasurePreserving (fun ω : Tape d q => (PUnit.unit,ω)) (tapeLaw L q) ((Measure.dirac PUnit.unit).prod (tapeLaw L q))
      exact ⟨measurable_const.prodMk measurable_id, (Measure.dirac_prod _).symm⟩
  | step o a next t ih =>
      let : MeasurableSpace (a.Tape d) := instrSpace d a
      let : MeasurableSpace (Tape d next) := tapeSpace d next
      let : IsProbabilityMeasure (tapeLaw L next) := tapeLaw_probability L next
      let : MeasurableSpace (Tape d q) := tapeSpace d q
      let : MeasurableSpace (Prefix d t) := prefixSpace d t
      let : IsProbabilityMeasure (instrLaw L a) := instrLaw_probability L a
      let : IsProbabilityMeasure (prefixLaw L t) := prefixLaw_probability L t
      let : IsProbabilityMeasure (tapeLaw L q) := tapeLaw_probability L q
      exact ((measurePreserving_prodAssoc (instrLaw L a) (prefixLaw L t) (tapeLaw L q)).symm
        MeasurableEquiv.prodAssoc).comp ((MeasurePreserving.id (instrLaw L a)).prod ih)
  | batch o children next t ih =>
      let : ∀ i, MeasurableSpace (Tape d (children i)) := fun i => tapeSpace d (children i)
      let : MeasurableSpace (Tape d next) := tapeSpace d next
      let : IsProbabilityMeasure (tapeLaw L next) := tapeLaw_probability L next
      let : MeasurableSpace (Tape d q) := tapeSpace d q
      let : MeasurableSpace (Prefix d t) := prefixSpace d t
      let : ∀ i, IsProbabilityMeasure (tapeLaw L (children i)) := fun i => tapeLaw_probability L _
      let : IsProbabilityMeasure (prefixLaw L t) := prefixLaw_probability L t
      let : IsProbabilityMeasure (tapeLaw L q) := tapeLaw_probability L q
      exact ((measurePreserving_prodAssoc (Measure.pi fun i => tapeLaw L (children i))
        (prefixLaw L t) (tapeLaw L q)).symm MeasurableEquiv.prodAssoc).comp
        ((MeasurePreserving.id (Measure.pi fun i => tapeLaw L (children i))).prod ih)

/-- The literal environment reached by traversing the selected syntax tail.
Whole preceding child tapes are evaluated once in the same pre-batch store. -/
def envAt (G : Point d → Point d) (input : Inputs d c) :
    {Γ : Ctx} → {τ : Ty} → {p : Prog c Γ τ} → (t : TailCut q p) →
      Env d Γ → Prefix d t → Env d Δ
  | _, _, _, .here, env, _ => env
  | _, _, _, .step o a _ t, env, h =>
      envAt G input t (Env.cons (evalInstr o a G input env h.1).value env) h.2
  | _, _, _, .batch _ children _ t, env, h =>
      envAt G input t (Env.prepend (fun i => (run (children i) G input env (h.1 i)).value) env) h.2

/-- Prefix environment is derived from interpreter measurability, not assumed. -/
theorem envAt_pathMeasurable {α : Type*} [MeasurableSpace α]
    (G : Point d → Point d) (hG : Measurable G) (t : TailCut q p) :
    ∀ (input : α → Inputs d c) (env : α → Env d Γ) (h : α → Prefix d t),
      (∀ j, Measurable (fun a => (input a).coefficient j)) →
      Measurable (fun a => (input a).center) →
      Measurable (fun a => (input a).momentum) → EnvPathMeasurable env →
      @Measurable α (Prefix d t) _ (prefixSpace d t) h →
      EnvPathMeasurable (fun a => envAt G (input a) t (env a) (h a)) := by
  induction t with
  | here => intro input env h hc hx hP he hh; exact he
  | step o a next t ih =>
      intro input env h hc hx hP he hh
      let : MeasurableSpace (a.Tape d) := instrSpace d a
      let : MeasurableSpace (Prefix d t) := prefixSpace d t
      have hv := evalInstr_value o a G hG input env (fun z => (h z).1)
        hc hx hP he ((instr_measurable_iff a _).mp hh.fst)
      intro ty r
      exact ih input (fun z => Env.cons (evalInstr o a G (input z) (env z) (h z).1).value (env z))
        (fun z => (h z).2) hc hx hP (envPathMeasurable_cons _ _ hv he) hh.snd r
  | batch o children next t ih =>
      intro input env h hc hx hP he hh
      let : ∀ i, MeasurableSpace (Tape d (children i)) := fun i => tapeSpace d (children i)
      let : MeasurableSpace (Prefix d t) := prefixSpace d t
      have hv (i) := run_value (children i) G hG input env (fun z => (h z).1 i)
        hc hx hP he ((measurable_iff_tapePath (children i) _).mp
          ((measurable_pi_apply i).comp hh.fst))
      intro ty r
      exact ih input
        (fun z => Env.prepend (fun i => (run (children i) G (input z) (env z) ((h z).1 i)).value) (env z))
        (fun z => (h z).2) hc hx hP (envPathMeasurable_prepend _ _ _ hv he) hh.snd r

/-- Actual prefix-store point readout is measurable for fixed measurable G.
No assumed center measurability or assumed independence is used. -/
theorem prefixReadout_measurable (G : Point d → Point d) (hG : Measurable G)
    (t : TailCut q p) (input : Inputs d c) (env : Env d Γ) (r : Ref Δ .point) :
    @Measurable (Prefix d t) (Point d) (prefixSpace d t) _
      (fun h => envAt G input t env h r) := by
  let : MeasurableSpace (Prefix d t) := prefixSpace d t
  have he : EnvPathMeasurable (fun _ : Prefix d t => env) := by
    intro ty r
    cases ty <;> exact measurable_const
  exact envAt_pathMeasurable G hG t (fun _ : Prefix d t => input)
    (fun _ => env) id (fun _ => measurable_const) measurable_const measurable_const
    he measurable_id r

end TailCut
end AcceleratedLogConcave.Oracle.TailOccurrenceCut
