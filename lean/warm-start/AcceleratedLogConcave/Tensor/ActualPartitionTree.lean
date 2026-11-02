import AcceleratedLogConcave.Tensor.ActualCoefficientBridge

/-!

-/
noncomputable section
open scoped BigOperators Classical
namespace AcceleratedLogConcave.Tensor.ActualPartitionTree
open EdgeClosure ActualCoefficient

variable {D : ℕ} {I C G : Type*} [Fintype I] [DecidableEq I]
  [Fintype C] [DecidableEq C] [NormedAddCommGroup G] [NormedSpace ℝ G]
variable (B : I → Type*) [∀ i, Fintype (B i)] [∀ i, DecidableEq (B i)]

/-- Pending root slots, attached branch leaves, and retained readout slots.
Even two leaves with identical coordinate values are distinct source slots. -/
abbrev Slots (s : Finset I) :=
  {i : I // i ∉ s} ⊕ ((Σ i : {i : I // i ∈ s}, B i.val) ⊕ C)

/-- Actual root directions after precisely the branches in s are attached. -/
def directions (V : ∀ i, ContinuousMultilinearMap ℝ (fun _ : B i => Space D) (Space D))
    (s : Finset I) (a : Slots (C := C) B s → Fin D) : I → Space D :=
  fun i => if hi : i ∈ s then
    V i (fun b => basis D (a (.inr (.inl ⟨⟨i, hi⟩, b⟩))))
  else basis D (a (.inl ⟨i, hi⟩))

/-- Every partial tree is an actual map evaluation, with ALL external slots. -/
def partialCoeff
    (T : ContinuousMultilinearMap ℝ (fun _ : I => Space D) G)
    (R : (C → Fin D) → G →L[ℝ] ℝ)
    (V : ∀ i, ContinuousMultilinearMap ℝ (fun _ : B i => Space D) (Space D))
    (s : Finset I) : Coeff (Slots (C := C) B s) D :=
  WithLp.toLp 2 (fun a => R (fun c => a (.inr (.inr c))) (T (directions B V s a)))

abbrev EdgeSlots (s : Finset I) (p : I) (hp : p ∉ s) :=
  {z : Slots (C := C) B s // z ≠ Sum.inl ⟨p, hp⟩} ⊕
    {z : B p ⊕ Unit // z ≠ Sum.inr ()}

/-- Forward slot map of one actual attachment. The retained branch copy is
mapped to the new p-block, not identified by its numerical coordinate label. -/
def stepTo (s : Finset I) (p : I) (hp : p ∉ s) :
    EdgeSlots (C := C) B s p hp → Slots (C := C) B (insert p s)
  | .inl ⟨.inl i, hne⟩ => .inl ⟨i.val, by
      simp only [Finset.mem_insert, not_or]
      refine ⟨?_, i.property⟩
      intro h; exact hne (congrArg Sum.inl (Subtype.ext h))⟩
  | .inl ⟨.inr (.inl ⟨i, b⟩), _⟩ =>
      .inr (.inl ⟨⟨i.val, Finset.mem_insert_of_mem i.property⟩, b⟩)
  | .inl ⟨.inr (.inr c), _⟩ => .inr (.inr c)
  | .inr ⟨.inl b, _⟩ => .inr (.inl ⟨⟨p, Finset.mem_insert_self p s⟩, b⟩)
  | .inr ⟨.inr u, h⟩ => False.elim (h (by cases u; rfl))

/-- Inverse slot map, separating the newly attached block from old blocks. -/
def stepFrom (s : Finset I) (p : I) (hp : p ∉ s) :
    Slots (C := C) B (insert p s) → EdgeSlots (C := C) B s p hp
  | .inl i => .inl ⟨.inl ⟨i.val, fun h =>
      i.property (Finset.mem_insert_of_mem h)⟩, by
      intro h
      have hi : i.val = p := congrArg (fun z : Slots (C := C) B s =>
        match z with | .inl j => j.val | .inr _ => p) h
      exact i.property (by simpa only [hi] using Finset.mem_insert_self p s)⟩
  | .inr (.inl ⟨i, b⟩) =>
      if h : i.val = p then
        .inr ⟨.inl (h ▸ b), by simp⟩
      else .inl ⟨.inr (.inl ⟨⟨i.val,
        (Finset.mem_insert.mp i.property).resolve_left h⟩, b⟩), by simp⟩
  | .inr (.inr c) => .inl ⟨.inr (.inr c), by simp⟩

/-- Bijective chart, never an equicardinality replacement of actual labels. -/
def stepChart (s : Finset I) (p : I) (hp : p ∉ s) :
    EdgeSlots (C := C) B s p hp ≃ Slots (C := C) B (insert p s) where
  toFun := stepTo B s p hp
  invFun := stepFrom B s p hp
  left_inv z := by
    rcases z with ⟨i | (⟨i,b⟩ | c), hz⟩ | ⟨b | u, hz⟩
    · have hi : i.val ≠ p := by
        intro h; apply hz; apply congrArg Sum.inl; exact Subtype.ext h
      simp [stepTo, stepFrom]
    · have hi : i.val ≠ p := by intro h; exact hp (h ▸ i.property)
      simp [stepTo, stepFrom, hi]
    · rfl
    · simp [stepTo, stepFrom]
    · exact False.elim (hz (by cases u; rfl))
  right_inv z := by
    rcases z with i | (⟨i,b⟩ | c)
    · simp [stepTo, stepFrom]
    · by_cases h : i.val = p
      · cases i with
        | mk i hi =>
          dsimp at h
          subst i
          simp [stepTo, stepFrom]
      · simp [stepTo, stepFrom, h]
    · rfl

/-- Coefficient identity for a complete arbitrary assignment, not merely a
pure tensor test. This is the induction's actual-map identification. -/
theorem partialCoeff_insert
    (T : ContinuousMultilinearMap ℝ (fun _ : I => Space D) G)
    (R : (C → Fin D) → G →L[ℝ] ℝ)
    (V : ∀ i, ContinuousMultilinearMap ℝ (fun _ : B i => Space D) (Space D))
    (s : Finset I) (p : I) (hp : p ∉ s) :
    relabel D (stepChart B s p hp)
      (contractAt D (Sum.inl ⟨p, hp⟩) (Sum.inr ())
        (partialCoeff B T R V s) (vectorCoeff (V p))) =
      partialCoeff B T R V (insert p s) := by
  ext a
  let v := directions B V (insert p s) a
  let L : Space D →L[ℝ] ℝ :=
    (R (fun c => a (.inr (.inr c)))).comp (T.toContinuousLinearMap v p)
  let vp : Space D := V p (fun b => basis D
    (a (.inr (.inl ⟨⟨p, Finset.mem_insert_self p s⟩, b⟩))))
  have hv : v p = vp := by simp [v, directions, vp]
  have hleft (w : Fin D) :
      partialCoeff B T R V s
        (insertEdge D (Sum.inl ⟨p,hp⟩)
          (fun z => a (stepChart B s p hp (.inl z))) w) = L (basis D w) := by
    change R (fun c => a (.inr (.inr c))) (T _) =
      R (fun c => a (.inr (.inr c))) (T (Function.update v p (basis D w)))
    apply congrArg (fun u => R (fun c => a (.inr (.inr c))) (T u))
    funext i
    by_cases hip : i = p
    · subst i
      simp [directions, hp, insertEdge]
    · by_cases his : i ∈ s
      · simp [directions, his, hip, v, insertEdge, stepChart, stepTo]
      · simp [directions, his, hip, v, insertEdge, stepChart, stepTo]
  have hright (w : Fin D) :
      vectorCoeff (V p)
        (insertEdge D (Sum.inr ())
          (fun z => a (stepChart B s p hp (.inr z))) w) =
      inner ℝ (basis D w) vp := by
    simp [vectorCoeff, mapCoeff, insertEdge, stepChart, stepTo, vp]
  dsimp only [relabel, contractAt, Function.comp_def]
  simp_rw [hleft, hright]
  have hactual : partialCoeff B T R V (insert p s) a = L vp := by
    change R _ (T v) = R _ (T (Function.update v p vp))
    rw [← hv, Function.update_eq_self]
  rw [hactual, linear_basis_expansion L vp]
  apply Finset.sum_congr rfl
  intro w _
  simp only [smul_eq_mul, mul_comm]

/-- Empty partial tree is exactly the root, under this literal chart. -/
def emptyChart : (I ⊕ C) ≃ Slots (C := C) B (∅ : Finset I) where
  toFun := Sum.elim (fun i => .inl ⟨i, by simp⟩) (fun c => .inr (.inr c))
  invFun := Sum.elim (fun i => .inl i.val)
    (Sum.elim (fun z => False.elim (Finset.notMem_empty _ z.1.property)) Sum.inr)
  left_inv z := by cases z <;> rfl
  right_inv z := by
    rcases z with i | (⟨i,b⟩ | c)
    · rfl
    · exact False.elim (Finset.notMem_empty _ i.property)
    · rfl

omit [DecidableEq C] [∀ i, DecidableEq (B i)] in
theorem partialCoeff_empty
    (T : ContinuousMultilinearMap ℝ (fun _ : I => Space D) G)
    (R : (C → Fin D) → G →L[ℝ] ℝ)
    (V : ∀ i, ContinuousMultilinearMap ℝ (fun _ : B i => Space D) (Space D)) :
    partialCoeff B T R V ∅ = relabel D (emptyChart B) (mapCoeff T R) := by
  ext a
  dsimp only [partialCoeff, relabel, mapCoeff, emptyChart, Function.comp_def]
  unfold directions
  simp

/-- Successive attachments multiply the root and branch all-proper budgets.
Only endpoint budgets are premises; no bound on a composite is assumed. -/
theorem partialCoeff_allProper [Nonempty C] [∀ i, Nonempty (B i)]
    (T : ContinuousMultilinearMap ℝ (fun _ : I => Space D) G)
    (R : (C → Fin D) → G →L[ℝ] ℝ)
    (V : ∀ i, ContinuousMultilinearMap ℝ (fun _ : B i => Space D) (Space D))
    (CT : ℝ) (CV : I → ℝ) (hCT : 0 ≤ CT) (hCV : ∀ i, 0 ≤ CV i)
    (hT : AllProper D (mapCoeff T R) CT)
    (hV : ∀ i, AllProper D (vectorCoeff (V i)) (CV i)) (s : Finset I) :
    AllProper D (partialCoeff B T R V s) (CT * ∏ i ∈ s, CV i) := by
  induction s using Finset.induction_on with
  | empty =>
      simpa only [partialCoeff_empty, Finset.prod_empty, mul_one] using
        hT.relabel (emptyChart B)
  | @insert p s hp ih =>
      let : Nonempty {z : Slots (C := C) B s // z ≠ Sum.inl ⟨p,hp⟩} := by
        obtain ⟨c⟩ := ‹Nonempty C›
        exact ⟨⟨.inr (.inr c), by simp⟩⟩
      have hprod : 0 ≤ CT * ∏ i ∈ s, CV i :=
        mul_nonneg hCT (Finset.prod_nonneg (fun i _ => hCV i))
      have hedge := attachVector_allProper D (Sum.inl ⟨p,hp⟩)
        (partialCoeff B T R V s) (vectorCoeff (V p)) hprod (hCV p) ih (hV p)
      have htransport : AllProper D
          (relabel D (stepChart B s p hp)
            (contractAt D (Sum.inl ⟨p,hp⟩) (Sum.inr ())
              (partialCoeff B T R V s) (vectorCoeff (V p))))
          ((CT * ∏ i ∈ s, CV i) * CV p) := by
        apply AllProper.relabel
        convert hedge using 1
      rw [partialCoeff_insert] at htransport
      simpa only [Finset.prod_insert hp, mul_assoc, mul_left_comm, mul_comm]
        using htransport

/-- All branches attached: only their labeled input leaves and readout remain. -/
def fullChart : Slots (C := C) B (Finset.univ : Finset I) ≃ ((Σ i, B i) ⊕ C) where
  toFun := Sum.elim (fun i => False.elim (i.property (Finset.mem_univ _)))
    (Sum.elim (fun z => .inl ⟨z.1.val, z.2⟩) Sum.inr)
  invFun := Sum.elim (fun z => .inr (.inl ⟨⟨z.1, Finset.mem_univ _⟩, z.2⟩))
    (fun c => .inr (.inr c))
  left_inv z := by
    rcases z with i | (⟨i,b⟩ | c)
    · exact False.elim (i.property (Finset.mem_univ _))
    · rfl
    · rfl
  right_inv z := by rcases z with ⟨i,b⟩ | c <;> rfl

/-- Literal actual full star evaluation, before any coefficient estimates. -/
def starCoeff
    (T : ContinuousMultilinearMap ℝ (fun _ : I => Space D) G)
    (R : (C → Fin D) → G →L[ℝ] ℝ)
    (V : ∀ i, ContinuousMultilinearMap ℝ (fun _ : B i => Space D) (Space D)) :
    Coeff ((Σ i, B i) ⊕ C) D :=
  WithLp.toLp 2 (fun a => R (fun c => a (.inr c))
    (T (fun i => V i (fun b => basis D (a (.inl ⟨i,b⟩))))))

omit [DecidableEq C] [∀ i, DecidableEq (B i)] in
theorem full_eq_star
    (T : ContinuousMultilinearMap ℝ (fun _ : I => Space D) G)
    (R : (C → Fin D) → G →L[ℝ] ℝ)
    (V : ∀ i, ContinuousMultilinearMap ℝ (fun _ : B i => Space D) (Space D)) :
    relabel D (fullChart B) (partialCoeff B T R V Finset.univ) =
      starCoeff B T R V := by
  ext a
  dsimp only [relabel, partialCoeff, fullChart, starCoeff, Function.comp_def]
  unfold directions
  simp

omit [DecidableEq C] [∀ i, DecidableEq (B i)] in
/-- Actual all-internal-coordinate basis sum. The assignment w is ANY function,
so repeated labels are included and no injectivity hypothesis is smuggled in. -/
theorem starCoeff_basis_sum
    (T : ContinuousMultilinearMap ℝ (fun _ : I => Space D) G)
    (R : (C → Fin D) → G →L[ℝ] ℝ)
    (V : ∀ i, ContinuousMultilinearMap ℝ (fun _ : B i => Space D) (Space D))
    (a : ((Σ i, B i) ⊕ C) → Fin D) :
    starCoeff B T R V a = ∑ w : I → Fin D,
      (∏ i, inner ℝ (basis D (w i))
        (V i (fun b => basis D (a (.inl ⟨i,b⟩))))) *
      R (fun c => a (.inr c)) (T (fun i => basis D (w i))) := by
  change R _ (T _) = _
  rw [multilinear_basis_expansion]
  simp only [map_sum, map_smul, smul_eq_mul]

theorem starCoeff_allProper [Nonempty C] [∀ i, Nonempty (B i)]
    (T : ContinuousMultilinearMap ℝ (fun _ : I => Space D) G)
    (R : (C → Fin D) → G →L[ℝ] ℝ)
    (V : ∀ i, ContinuousMultilinearMap ℝ (fun _ : B i => Space D) (Space D))
    (CT : ℝ) (CV : I → ℝ) (hCT : 0 ≤ CT) (hCV : ∀ i, 0 ≤ CV i)
    (hT : AllProper D (mapCoeff T R) CT)
    (hV : ∀ i, AllProper D (vectorCoeff (V i)) (CV i)) :
    AllProper D (starCoeff B T R V) (CT * ∏ i, CV i) := by
  have h := (partialCoeff_allProper B T R V CT CV hCT hCV hT hV Finset.univ).relabel
    (fullChart B)
  rwa [full_eq_star] at h

end AcceleratedLogConcave.Tensor.ActualPartitionTree
