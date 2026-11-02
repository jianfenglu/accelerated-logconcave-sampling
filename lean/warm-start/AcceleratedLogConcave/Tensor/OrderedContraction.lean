import AcceleratedLogConcave.Tensor.SplitNorm
import Mathlib.Tactic

/-!
# Ordered coordinate contractions with one dimension factor

Finite wire/circuit algebra is adapted from openai/math immutable revision
1581d4cbdd69a0faf34b2089614fe2a814316a6a, Apache-2.0,
OAI/Probability/LogConcave/JetEstimates/WireStep.lean and Bound.lean.
It is restated using the genuine Hilbert energy bound of Tensor.SplitNorm.
-/ 

noncomputable section
open scoped BigOperators
namespace AcceleratedLogConcave.Tensor

variable {I J K L : Type*} [Fintype I] [Fintype J] [Fintype K] [Fintype L]

lemma EnergyBound.reindex {A : I → J → ℝ} {C : ℝ} (h : EnergyBound A C)
    (e : K ≃ I) (f : L ≃ J) : EnergyBound (fun k l => A (e k) (f l)) C := by
  intro v
  have hh := h (v ∘ f.symm)
  rw [← e.sum_comp] at hh
  simp_rw [← f.sum_comp] at hh
  simpa only [Function.comp_def, Equiv.symm_apply_apply] using hh

lemma EnergyBound.comp {A : I → J → ℝ} {B : J → K → ℝ} {C D : ℝ}
    (hA : EnergyBound A C) (hB : EnergyBound B D) (hC : 0≤C) :
    EnergyBound (fun i k => ∑ j,A i j*B j k) (C*D) := by
  intro v
  have he (i : I) : (∑ k,(∑ j,A i j*B j k)*v k)=
      ∑ j,A i j*(∑ k,B j k*v k) := by
    simp only [Finset.sum_mul,Finset.mul_sum,mul_assoc]
    exact Finset.sum_comm
  simp_rw [he]
  exact (hA _).trans ((mul_le_mul_of_nonneg_left (hB v) hC).trans_eq (by ring))

lemma bound_identity [DecidableEq I] : EnergyBound (fun i j : I => if i=j then (1:ℝ) else 0) 1 := by
  intro v
  simp

lemma EnergyBound.entry_sq {A : I → J → ℝ} {C : ℝ} (hA : EnergyBound A C) (i : I) (j : J) :
    (A i j)^2 ≤ C := by
  classical
  have hh := hA (fun k => if k=j then 1 else 0)
  simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true,
    ite_pow,one_pow,zero_pow (by decide : (2:ℕ)≠0)] at hh
  exact (Finset.single_le_sum (fun k _ => sq_nonneg (A k j)) (Finset.mem_univ i)).trans hh

lemma EnergyBound.trace_sq {A : I → I → ℝ} {C : ℝ} (hA : EnergyBound A C) :
    (∑ i,A i i)^2 ≤ (Fintype.card I:ℝ)^2*C := by
  have hh := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset I) (fun _ : I => (1:ℝ)) (fun i => A i i)
  simp only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at hh
  have hg := Finset.sum_le_sum (fun i (_ : i∈(Finset.univ:Finset I)) => hA.entry_sq i i)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hg
  exact hh.trans ((mul_le_mul_of_nonneg_left hg (Nat.cast_nonneg _)).trans_eq (by ring))
open scoped BigOperators

def wireStep {I O S X Y : Type*} [DecidableEq S]
    (A : O → I → ℝ) (ei : X ≃ I×S) (eo : Y ≃ O×S) : Y → X → ℝ :=
  fun y x => A (eo y).1 (ei x).1 * if (eo y).2=(ei x).2 then 1 else 0

lemma EnergyBound.wireStep {I O S X Y : Type*} [Fintype I] [Fintype O] [Fintype S]
    [Fintype X] [Fintype Y] [DecidableEq S] {A : O → I → ℝ} {C : ℝ}
    (hA : EnergyBound A C) (hC : 0≤C) (ei : X ≃ I×S) (eo : Y ≃ O×S) :
    EnergyBound (wireStep A ei eo) C := by
  have hh := (hA.kronecker (bound_identity (I:=S)) hC).reindex eo ei
  change EnergyBound (fun y x => A (eo y).1 (ei x).1 * if (eo y).2=(ei x).2 then 1 else 0) C
  simpa only [mul_one, Matrix.kronecker, Matrix.kroneckerMap, Matrix.of_apply] using hh

def circuit {D : ℕ → Type*} [∀k,Fintype (D k)] [DecidableEq (D 0)]
    (A : ∀k,D (k+1) → D k → ℝ) : ∀n,D n → D 0 → ℝ
  | 0 => fun i j => if i=j then 1 else 0
  | n+1 => fun i j => ∑k,A n i k*circuit A n k j

lemma circuit_bound {D : ℕ → Type*} [∀k,Fintype (D k)] [DecidableEq (D 0)]
    (A : ∀k,D (k+1) → D k → ℝ) (C : ℕ → ℝ)
    (hC : ∀k,0≤C k) (hA : ∀k,EnergyBound (A k) (C k)) (n : ℕ) :
    EnergyBound (circuit A n) (∏k∈Finset.range n,C k) := by
  induction n with
  | zero => simpa only [circuit,Finset.range_zero,Finset.prod_empty] using (bound_identity (I:=D 0))
  | succ n ih =>
    simpa only [circuit,Finset.prod_range_succ,mul_comm] using (hA n).comp ih (hC n)

lemma EnergyBound.trace_abs {I : Type*} [Fintype I] {A : I → I → ℝ} {C : ℝ}
    (hA : EnergyBound A (C^2)) (hC : 0≤C) : |∑i,A i i|≤(Fintype.card I:ℝ)*C := by
  have hh := hA.trace_sq
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hC)).mp
  simpa only [sq_abs,mul_pow] using hh

theorem closed_wire_circuit_bound
    {D I O S : ℕ → Type*} [∀k,Fintype (D k)] [∀k,Fintype (I k)]
    [∀k,Fintype (O k)] [∀k,Fintype (S k)] [∀k,DecidableEq (S k)]
    [DecidableEq (D 0)]
    (A : ∀k,O k → I k → ℝ) (C : ℕ → ℝ)
    (hC : ∀k,0≤C k) (hA : ∀k,EnergyBound (A k) ((C k)^2))
    (ei : ∀k,D k ≃ I k×S k) (eo : ∀k,D (k+1) ≃ O k×S k)
    (n : ℕ) (close : D 0 ≃ D n) :
    |∑i,circuit (fun k => wireStep (A k) (ei k) (eo k)) n (close i) i|≤
      (Fintype.card (D 0):ℝ)*(∏k∈Finset.range n,C k) := by
  have hlocal (k : ℕ) : EnergyBound (wireStep (A k) (ei k) (eo k)) ((C k)^2) :=
    (hA k).wireStep (sq_nonneg _) (ei k) (eo k)
  have hh := (circuit_bound _ (fun k => (C k)^2) (fun k => sq_nonneg _) hlocal n).reindex
    close (Equiv.refl (D 0))
  rw [Finset.prod_pow] at hh
  exact hh.trace_abs (Finset.prod_nonneg (fun k _ => hC k))

lemma cut_bundle_card (d b : ℕ) : Fintype.card (Fin b → Fin d)=d^b := by simp
open scoped BigOperators Classical

variable {D : ℕ → Type*} [∀k,Fintype (D k)] [DecidableEq (D 0)]

abbrev Path (n : ℕ) := ∀k : Fin (n+1),D k.val

def pathWeight (A : ∀k,D (k+1) → D k → ℝ) (n : ℕ) (h : Path (D:=D) n) : ℝ :=
  ∏k : Fin n,A k.val (h k.succ) (h k.castSucc)

omit [∀k,Fintype (D k)] [DecidableEq (D 0)] in
lemma pathWeight_snoc (A : ∀k,D (k+1) → D k → ℝ) (n : ℕ)
    (h : Path (D:=D) n) (y : D (n+1)) :
    pathWeight A (n+1) (Fin.snoc (α:=fun k : Fin (n+2) => D k.val) h y)=pathWeight A n h*A n y (h (Fin.last n)) := by
  unfold pathWeight
  rw [Fin.prod_univ_castSucc]
  congr 1
  · apply Finset.prod_congr rfl
    intro k hk
    change A k.val (Fin.snoc (α:=fun k : Fin (n+2) => D k.val) h y k.succ.castSucc)
      (Fin.snoc (α:=fun k : Fin (n+2) => D k.val) h y k.castSucc.castSucc) = _
    simp only [Fin.snoc_castSucc]
  · simp only [Fin.succ_last,Fin.snoc_last,Fin.snoc_castSucc,Fin.val_last]

theorem circuit_path_expansion (A : ∀k,D (k+1) → D k → ℝ) (n : ℕ)
    (B : D 0 → D n → ℝ) :
    (∑h : Path (D:=D) n,pathWeight A n h*B (h 0) (h (Fin.last n)))=
      ∑i,∑j,circuit A n j i*B i j := by
  induction n with
  | zero =>
    rw [←(Fin.consEquiv (fun k : Fin 1 => D k.val)).sum_comp]
    simp [pathWeight,circuit,Fintype.sum_prod_type]
  | succ n ih =>
    rw [←(Fin.snocEquiv (fun k : Fin (n+2) => D k.val)).sum_comp]
    simp only [Fintype.sum_prod_type,Fin.snocEquiv_apply]
    change (∑y : D (n+1),∑h : Path (D:=D) n,
      pathWeight A (n+1) (Fin.snoc (α:=fun k : Fin (n+2) => D k.val) h y)*
        B (Fin.snoc (α:=fun k : Fin (n+2) => D k.val) h y (0 : Fin (n+1)).castSucc)
          (Fin.snoc (α:=fun k : Fin (n+2) => D k.val) h y (Fin.last (n+1))))=_
    simp_rw [pathWeight_snoc,Fin.snoc_castSucc,Fin.snoc_last]
    have hh (y : D (n+1)) :
        (∑h : Path (D:=D) n,pathWeight A n h*A n y (h (Fin.last n))*B (h 0) y)=
        ∑i,∑j,circuit A n j i*(A n y j*B i y) := by
      simpa only [mul_assoc] using ih (fun i j => A n y j*B i y)
    simp_rw [hh]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro y hy
    simp only [circuit,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    ring

end AcceleratedLogConcave.Tensor



noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
namespace AcceleratedLogConcave.Tensor

variable {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]

def outputSlots : Finset (I ⊕ O) := Finset.univ.filter (fun s => s.isRight = true)

omit [DecidableEq I] [DecidableEq O] in
@[simp] lemma inl_not_mem_outputSlots (i : I) : Sum.inl i ∉ (outputSlots : Finset (I ⊕ O)) := by
  simp [outputSlots]
omit [DecidableEq I] [DecidableEq O] in
@[simp] lemma inr_mem_outputSlots (o : O) : Sum.inr o ∈ (outputSlots : Finset (I ⊕ O)) := by
  simp [outputSlots]

def outputPortEquiv : O ≃ {s : I ⊕ O // s ∈ (outputSlots : Finset (I ⊕ O))} where
  toFun o := ⟨Sum.inr o,inr_mem_outputSlots o⟩
  invFun
    | ⟨Sum.inl i,h⟩ => False.elim (inl_not_mem_outputSlots i h)
    | ⟨Sum.inr o,_⟩ => o
  left_inv _ := rfl
  right_inv s := by
    rcases s with ⟨s,h⟩
    cases s with
    | inl i => exact False.elim (inl_not_mem_outputSlots i h)
    | inr o => rfl

def inputPortEquiv : I ≃ {s : I ⊕ O // s ∉ (outputSlots : Finset (I ⊕ O))} where
  toFun i := ⟨Sum.inl i,inl_not_mem_outputSlots i⟩
  invFun
    | ⟨Sum.inl i,_⟩ => i
    | ⟨Sum.inr o,h⟩ => False.elim (h (inr_mem_outputSlots o))
  left_inv _ := rfl
  right_inv s := by
    rcases s with ⟨s,h⟩
    cases s with
    | inl i => rfl
    | inr o => exact False.elim (h (inr_mem_outputSlots o))

def outputAssignmentEquiv (D : ℕ) :
    (O → Fin D) ≃ LeftAssignment D (outputSlots : Finset (I ⊕ O)) :=
  Equiv.arrowCongr outputPortEquiv (Equiv.refl (Fin D))

def inputAssignmentEquiv (D : ℕ) :
    (I → Fin D) ≃ RightAssignment D (outputSlots : Finset (I ⊕ O)) :=
  Equiv.arrowCongr inputPortEquiv (Equiv.refl (Fin D))

lemma sum_unfold_reindex (D : ℕ) (T : Coeff (I ⊕ O) D)
    (o : O → Fin D) (i : I → Fin D) :
    unfoldEquiv D outputSlots T (outputAssignmentEquiv D o) (inputAssignmentEquiv D i) =
      T (Sum.elim i o) := by
  rw [unfold_apply]
  apply congrArg (fun a => T a)
  funext s
  cases s with
  | inl a => simp [inputAssignmentEquiv,inputPortEquiv]
  | inr a => simp [outputAssignmentEquiv,outputPortEquiv]

lemma matrixCLM_reindex_norm {R C R' C' : Type*} [Fintype R] [Fintype C]
    [Fintype R'] [Fintype C'] [DecidableEq C] [DecidableEq C'] (A : Matrix R C ℝ) (e : R' ≃ R) (f : C' ≃ C) :
    ‖matrixCLMEquiv (fun r c => A (e r) (f c))‖ = ‖matrixCLMEquiv A‖ := by
  apply le_antisymm
  · exact opNorm_le_of_energyBound _ _ (norm_nonneg _) ((energyBound_opNorm A).reindex e f)
  · have h := opNorm_le_of_energyBound _ _ (norm_nonneg _)
      ((energyBound_opNorm (fun r c => A (e r) (f c))).reindex e.symm f.symm)
    simpa only [Equiv.apply_symm_apply] using h

lemma sum_unfold_norm (D : ℕ) (T : Coeff (I ⊕ O) D) :
    ‖matrixCLMEquiv (fun (o : O → Fin D) (i : I → Fin D) => T (Sum.elim i o))‖ =
      splitNorm D outputSlots T := by
  have h := matrixCLM_reindex_norm (unfoldEquiv D outputSlots T)
    (outputAssignmentEquiv D) (inputAssignmentEquiv D)
  change ‖matrixCLMEquiv (fun (o : O → Fin D) (i : I → Fin D) => T (Sum.elim i o))‖ =
    ‖matrixCLMEquiv (unfoldEquiv D outputSlots T)‖
  convert h using 1
  simp only [sum_unfold_reindex]

lemma outputSlots_nontrivial [Nonempty I] [Nonempty O] :
    NontrivialSplit (outputSlots : Finset (I ⊕ O)) := by
  obtain ⟨i⟩ := ‹Nonempty I›
  obtain ⟨o⟩ := ‹Nonempty O›
  exact ⟨⟨Sum.inr o,inr_mem_outputSlots o⟩,
    ⟨Sum.inl i,Finset.mem_compl.mpr (inl_not_mem_outputSlots i)⟩⟩

end AcceleratedLogConcave.Tensor

noncomputable section
open scoped BigOperators
namespace AcceleratedLogConcave.Tensor.Ordered

/-- A nonempty ordered occurrence set and labeled forward edges. Parallel edges
are allowed. The single cut coordinate is represented separately by `none`. -/
structure Graph (n : ℕ) (Edge : Type*) where
  source : Edge → Fin (n+1)
  target : Edge → Fin (n+1)
  forward : ∀ e, source e < target e

namespace Graph
open scoped Classical

variable {n : ℕ} {Edge : Type*} (g : Graph n Edge)
abbrev Wire := Option Edge

def incoming (v : Fin (n+1)) : Wire (Edge := Edge) → Prop
  | none => v = 0
  | some e => g.target e = v

def outgoing (v : Fin (n+1)) : Wire (Edge := Edge) → Prop
  | none => v = Fin.last n
  | some e => g.source e = v

def live (k : ℕ) : Wire (Edge := Edge) → Prop
  | none => k = 0 ∨ k = n+1
  | some e => (g.source e).val < k ∧ k ≤ (g.target e).val

def bypass (k : ℕ) : Wire (Edge := Edge) → Prop
  | none => False
  | some e => (g.source e).val < k ∧ k < (g.target e).val

abbrev InPort (v : Fin (n+1)) := {w : Wire (Edge := Edge) // g.incoming v w}
abbrev OutPort (v : Fin (n+1)) := {w : Wire (Edge := Edge) // g.outgoing v w}
abbrev Frontier (k : ℕ) := {w : Wire (Edge := Edge) // g.live k w}
abbrev Bypass (k : ℕ) := {w : Wire (Edge := Edge) // g.bypass k w}
abbrev Slot (v : Fin (n+1)) := g.InPort v ⊕ g.OutPort v

def Admissible : Prop := ∀ v, Nonempty (g.InPort v) ∧ Nonempty (g.OutPort v)

lemma incoming_live (v : Fin (n+1)) {w : Wire (Edge := Edge)}
    (h : g.incoming v w) : g.live v.val w := by
  cases w with
  | none => simp only [incoming] at h; subst v; simp [live]
  | some e =>
    change g.target e = v at h
    subst v
    exact ⟨g.forward e, le_refl _⟩

lemma outgoing_live (v : Fin (n+1)) {w : Wire (Edge := Edge)}
    (h : g.outgoing v w) : g.live (v.val+1) w := by
  cases w with
  | none => simp only [outgoing] at h; subst v; simp [live]
  | some e =>
    change g.source e = v at h
    subst v
    exact ⟨Nat.lt_succ_self _, g.forward e⟩

lemma bypass_live_before (k : ℕ) {w : Wire (Edge := Edge)}
    (h : g.bypass k w) : g.live k w := by
  cases w with
  | none => exact False.elim h
  | some e => exact ⟨h.1, le_of_lt h.2⟩

lemma bypass_live_after (k : ℕ) {w : Wire (Edge := Edge)}
    (h : g.bypass k w) : g.live (k+1) w := by
  cases w with
  | none => exact False.elim h
  | some e => exact ⟨Nat.lt_succ_of_lt h.1, h.2⟩

lemma live_before_iff (v : Fin (n+1)) (w : Wire (Edge := Edge)) :
    g.live v.val w ↔ g.incoming v w ∨ g.bypass v.val w := by
  cases w with
  | none => simp only [live, incoming, bypass, or_false, Fin.ext_iff, Fin.val_zero]; omega
  | some e =>
    have hf := g.forward e
    simp only [live, incoming, bypass, Fin.ext_iff, Fin.lt_def] at *
    omega

lemma live_after_iff (v : Fin (n+1)) (w : Wire (Edge := Edge)) :
    g.live (v.val+1) w ↔ g.outgoing v w ∨ g.bypass v.val w := by
  cases w with
  | none => simp only [live, outgoing, bypass, or_false, Fin.ext_iff, Fin.val_last]; omega
  | some e =>
    have hf := g.forward e
    simp only [live, outgoing, bypass, Fin.ext_iff, Fin.lt_def] at *
    omega

lemma incoming_not_bypass (v : Fin (n+1)) {w : Wire (Edge := Edge)}
    (h : g.incoming v w) : ¬ g.bypass v.val w := by
  cases w with
  | none => simp [bypass]
  | some e => simp only [incoming, Fin.ext_iff] at h; simp only [bypass]; omega

lemma outgoing_not_bypass (v : Fin (n+1)) {w : Wire (Edge := Edge)}
    (h : g.outgoing v w) : ¬ g.bypass v.val w := by
  cases w with
  | none => simp [bypass]
  | some e => simp only [outgoing, Fin.ext_iff] at h; simp only [bypass]; omega

noncomputable def beforeEquiv (v : Fin (n+1)) :
    g.Frontier v.val ≃ g.InPort v ⊕ g.Bypass v.val where
  toFun w := if h : g.incoming v w.val then .inl ⟨w.val,h⟩
    else .inr ⟨w.val, ((g.live_before_iff v w.val).mp w.property).resolve_left h⟩
  invFun
    | .inl w => ⟨w.val,g.incoming_live v w.property⟩
    | .inr w => ⟨w.val,g.bypass_live_before v.val w.property⟩
  left_inv w := by dsimp; split_ifs <;> rfl
  right_inv w := by
    cases w with
    | inl w => simp [w.property]
    | inr w =>
      have h : ¬ g.incoming v w.val := fun h => g.incoming_not_bypass v h w.property
      simp [h]

noncomputable def afterEquiv (v : Fin (n+1)) :
    g.Frontier (v.val+1) ≃ g.OutPort v ⊕ g.Bypass v.val where
  toFun w := if h : g.outgoing v w.val then .inl ⟨w.val,h⟩
    else .inr ⟨w.val, ((g.live_after_iff v w.val).mp w.property).resolve_left h⟩
  invFun
    | .inl w => ⟨w.val,g.outgoing_live v w.property⟩
    | .inr w => ⟨w.val,g.bypass_live_after v.val w.property⟩
  left_inv w := by dsimp; split_ifs <;> rfl
  right_inv w := by
    cases w with
    | inl w => simp [w.property]
    | inr w =>
      have h : ¬ g.outgoing v w.val := fun h => g.outgoing_not_bypass v h w.property
      simp [h]


section Finite
variable [Fintype Edge]
noncomputable instance (v : Fin (n+1)) : Fintype (g.InPort v) := Fintype.ofFinite _
noncomputable instance (v : Fin (n+1)) : Fintype (g.OutPort v) := Fintype.ofFinite _
noncomputable instance (k : ℕ) : Fintype (g.Frontier k) := Fintype.ofFinite _
noncomputable instance (k : ℕ) : Fintype (g.Bypass k) := Fintype.ofFinite _

variable (D : ℕ)
abbrev State (k : ℕ) := g.Frontier k → Fin D
abbrev StatePath := ∀ k : Fin (n+2), g.State D k.val
abbrev Tensors := ∀ v : Fin (n+1), Coeff (g.Slot v) D

/-- The original complete contraction, with one coordinate for every labeled
internal edge and one common cut coordinate. This is independent of operators. -/
def coordinateEval (T : g.Tensors D) : ℝ :=
  ∑ a : Wire (Edge := Edge) → Fin D,
    ∏ v, T v (Sum.elim (fun p : g.InPort v => a p.val)
      (fun p : g.OutPort v => a p.val))

def localValue (T : g.Tensors D) (h : g.StatePath D) (v : Fin (n+1)) : ℝ :=
  T v (Sum.elim
    (fun p : g.InPort v => h v.castSucc ⟨p.val,g.incoming_live v p.property⟩)
    (fun p : g.OutPort v => h v.succ ⟨p.val,g.outgoing_live v p.property⟩))

def pathTensorProduct (T : g.Tensors D) (h : g.StatePath D) : ℝ :=
  ∏ v, g.localValue D T h v

/-- Constancy of each coordinate across all of its retained copies, including
identification of the two ends of the cut coordinate. -/
def Consistent (h : g.StatePath D) : Prop :=
  ∀ (k l : Fin (n+2)) (w : Wire (Edge := Edge))
    (hk : g.live k.val w) (hl : g.live l.val w), h k ⟨w,hk⟩ = h l ⟨w,hl⟩

def chosenSlice : Wire (Edge := Edge) → Fin (n+2)
  | none => 0
  | some e => ⟨(g.source e).val+1, by have := (g.source e).isLt; omega⟩

omit [Fintype Edge] in
lemma live_chosenSlice (w : Wire (Edge := Edge)) : g.live (g.chosenSlice w).val w := by
  cases w with
  | none => exact Or.inl rfl
  | some e => exact ⟨Nat.lt_succ_self _,g.forward e⟩

/-- Actual assignments and consistent frontier paths are in bijection. -/
noncomputable def assignmentEquivPath :
    (Wire (Edge := Edge) → Fin D) ≃ {h : g.StatePath D // g.Consistent D h} where
  toFun a := ⟨fun _ p => a p.val, fun _ _ _ _ _ => rfl⟩
  invFun h w := h.val (g.chosenSlice w) ⟨w,g.live_chosenSlice w⟩
  left_inv a := rfl
  right_inv h := by
    apply Subtype.ext
    funext k w
    exact h.property (g.chosenSlice w.val) k w.val (g.live_chosenSlice w.val) w.property

lemma coordinateEval_eq_consistent_sum (T : g.Tensors D) :
    g.coordinateEval D T = ∑ h : {h : g.StatePath D // g.Consistent D h},
      g.pathTensorProduct D T h.val := by
  rw [← (g.assignmentEquivPath D).sum_comp]
  rfl

def stepConsistent (h : g.StatePath D) (v : Fin (n+1)) : Prop :=
  ∀ w : g.Bypass v.val,
    h v.castSucc ⟨w.val,g.bypass_live_before v.val w.property⟩ =
      h v.succ ⟨w.val,g.bypass_live_after v.val w.property⟩

def closes (h : g.StatePath D) : Prop :=
  h 0 ⟨none,Or.inl rfl⟩ = h (Fin.last (n+1)) ⟨none,Or.inr rfl⟩

def edgeValue (h : g.StatePath D) (e : Edge) (k : ℕ)
    (hk : (g.source e).val < k) (hl : k ≤ (g.target e).val) : Fin D :=
  h ⟨k,by have := (g.target e).isLt; omega⟩ ⟨some e,⟨hk,hl⟩⟩

omit [Fintype Edge] in
lemma edgeValue_eq_of_steps (h : g.StatePath D)
    (hs : ∀ v, g.stepConsistent D h v) (e : Edge) {k l : ℕ}
    (hkl : k ≤ l) (hk : (g.source e).val < k) (hl : l ≤ (g.target e).val) :
    g.edgeValue D h e k hk (hkl.trans hl) =
      g.edgeValue D h e l (lt_of_lt_of_le hk hkl) hl := by
  have aux : ∀ l, ∀ hkl : k ≤ l, ∀ hl : l ≤ (g.target e).val,
      g.edgeValue D h e k hk (hkl.trans hl) =
        g.edgeValue D h e l (lt_of_lt_of_le hk hkl) hl := by
    intro l hkl
    induction l, hkl using Nat.le_induction with
    | base => intro _; rfl
    | succ l hkl ih =>
      intro hl
      have hl' : l ≤ (g.target e).val := (Nat.le_succ l).trans hl
      have hv : l < n+1 := by have := (g.target e).isLt; omega
      have hb : g.bypass l (some e) := ⟨lt_of_lt_of_le hk hkl,hl⟩
      exact (ih hl').trans (hs ⟨l,hv⟩ ⟨some e,hb⟩)
  exact aux l hkl hl

omit [Fintype Edge] in
lemma consistent_iff_steps (h : g.StatePath D) :
    g.Consistent D h ↔ (∀ v, g.stepConsistent D h v) ∧ g.closes D h := by
  constructor
  · intro hh
    exact ⟨fun v w => hh _ _ _ _ _,hh _ _ _ _ _⟩
  · rintro ⟨hs,hc⟩ k l w hk hl
    cases w with
    | none =>
      have hk' : k = 0 ∨ k = Fin.last (n+1) := by
        rcases hk with hh | hh
        · left; apply Fin.ext; exact hh
        · right; apply Fin.ext; exact hh
      have hl' : l = 0 ∨ l = Fin.last (n+1) := by
        rcases hl with hh | hh
        · left; apply Fin.ext; exact hh
        · right; apply Fin.ext; exact hh
      rcases hk' with rfl | rfl <;> rcases hl' with rfl | rfl
      · rfl
      · exact hc
      · exact hc.symm
      · rfl
    | some e =>
      rcases le_total k.val l.val with hkl | hlk
      · exact g.edgeValue_eq_of_steps D h hs e hkl hk.1 hl.2
      · exact (g.edgeValue_eq_of_steps D h hs e hlk hl.1 hk.2).symm

end Finite

end Graph
end AcceleratedLogConcave.Tensor.Ordered

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Classical
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
variable {n : ℕ} {Edge : Type*} [Fintype Edge] (g : Ordered.Graph n Edge) (D : ℕ)

def beforeAssignments (v : Fin (n+1)) :
    g.State D v.val ≃ (g.InPort v → Fin D) × (g.Bypass v.val → Fin D) :=
  (Equiv.arrowCongr (g.beforeEquiv v) (Equiv.refl (Fin D))).trans
    (Equiv.sumArrowEquivProdArrow _ _ _)

def afterAssignments (v : Fin (n+1)) :
    g.State D (v.val+1) ≃ (g.OutPort v → Fin D) × (g.Bypass v.val → Fin D) :=
  (Equiv.arrowCongr (g.afterEquiv v) (Equiv.refl (Fin D))).trans
    (Equiv.sumArrowEquivProdArrow _ _ _)

/-- The actual matrix unfolding from incoming to outgoing coefficient indices. -/
def vertexMatrix (T : g.Tensors D) (v : Fin (n+1)) :
    Matrix (g.OutPort v → Fin D) (g.InPort v → Fin D) ℝ :=
  fun o i => T v (Sum.elim i o)

def stepMatrix (T : g.Tensors D) (k : ℕ) : Matrix (g.State D (k+1)) (g.State D k) ℝ :=
  if hk : k < n+1 then
    wireStep (g.vertexMatrix D T ⟨k,hk⟩)
      (g.beforeAssignments D ⟨k,hk⟩) (g.afterAssignments D ⟨k,hk⟩)
  else 0

def stageNorm (T : g.Tensors D) (k : ℕ) : ℝ :=
  if hk : k < n+1 then ‖matrixCLMEquiv (g.vertexMatrix D T ⟨k,hk⟩)‖ else 0

lemma stageNorm_nonneg (T : g.Tensors D) (k : ℕ) : 0 ≤ g.stageNorm D T k := by
  unfold stageNorm
  split_ifs <;> positivity

lemma stepMatrix_energy (T : g.Tensors D) (k : ℕ) :
    EnergyBound (g.stepMatrix D T k) ((g.stageNorm D T k)^2) := by
  unfold stepMatrix stageNorm
  split_ifs with hk
  · exact (energyBound_opNorm _).wireStep (sq_nonneg _)
      (g.beforeAssignments D ⟨k,hk⟩) (g.afterAssignments D ⟨k,hk⟩)
  · intro v
    simp

lemma stepMatrix_path (T : g.Tensors D) (h : g.StatePath D) (v : Fin (n+1)) :
    g.stepMatrix D T v.val (h v.succ) (h v.castSucc) =
      g.localValue D T h v * if g.stepConsistent D h v then 1 else 0 := by
  rw [stepMatrix, dite_eq_left v.isLt]
  change g.localValue D T h v *
    (if (fun w : g.Bypass v.val => h v.succ ⟨w.val,g.bypass_live_after v.val w.property⟩) =
      (fun w : g.Bypass v.val => h v.castSucc ⟨w.val,g.bypass_live_before v.val w.property⟩)
      then 1 else 0) = _
  congr 1
  simp only [funext_iff]
  congr 1
  exact propext (forall_congr' (fun _ => eq_comm))

/-- The scalar delta closing the cut is separate from every vertex operator. -/
def closingDelta (h : g.StatePath D) : ℝ := if g.closes D h then 1 else 0

lemma pathWeight_with_closure (T : g.Tensors D) (h : g.StatePath D) :
    pathWeight (g.stepMatrix D T) (n+1) h * g.closingDelta D h =
      if g.Consistent D h then g.pathTensorProduct D T h else 0 := by
  classical
  unfold pathWeight
  simp_rw [g.stepMatrix_path D T h]
  by_cases hc : g.Consistent D h
  · obtain ⟨hs,hclose⟩ := (g.consistent_iff_steps D h).mp hc
    simp [hc, hs, closingDelta, hclose, pathTensorProduct]
  · rw [ite_eq_right hc]
    by_cases hclose : g.closes D h
    · have hn : ¬ ∀ v, g.stepConsistent D h v := by
        intro hs
        exact hc ((g.consistent_iff_steps D h).mpr ⟨hs,hclose⟩)
      push Not at hn
      obtain ⟨v,hv⟩ := hn
      have hz : (∏ v, g.localValue D T h v * if g.stepConsistent D h v then 1 else 0) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ v)
        simp [hv]
      rw [hz,zero_mul]
    · simp [closingDelta,hclose]

omit [Fintype Edge] in
lemma live_zero_iff (w : Wire (Edge := Edge)) : g.live 0 w ↔ w = none := by
  cases w <;> simp [live]

omit [Fintype Edge] in
lemma live_last_iff (w : Wire (Edge := Edge)) : g.live (n+1) w ↔ w = none := by
  cases w with
  | none => simp [live]
  | some e =>
    have := (g.target e).isLt
    simp only [live, Option.some_ne_none, iff_false, not_and]
    omega

def initialEquiv : g.State D 0 ≃ Fin D where
  toFun a := a ⟨none,Or.inl rfl⟩
  invFun a _ := a
  left_inv a := by
    funext w
    have h : w.val = none := (g.live_zero_iff w.val).mp w.property
    cases w
    cases h
    rfl
  right_inv _ := rfl

def finalEquiv : g.State D (n+1) ≃ Fin D where
  toFun a := a ⟨none,Or.inr rfl⟩
  invFun a _ := a
  left_inv a := by
    funext w
    have h : w.val = none := (g.live_last_iff w.val).mp w.property
    cases w
    cases h
    rfl
  right_inv _ := rfl

def closingEquiv : g.State D 0 ≃ g.State D (n+1) :=
  (g.initialEquiv D).trans (g.finalEquiv D).symm

omit [Fintype Edge] in
lemma closingEquiv_eq_iff (a : g.State D 0) (b : g.State D (n+1)) :
    g.closingEquiv D a = b ↔ g.initialEquiv D a = g.finalEquiv D b := by
  rw [← (g.finalEquiv D).injective.eq_iff]
  simp only [closingEquiv,Equiv.trans_apply,Equiv.apply_symm_apply]

/-- The finite coordinate product sum is proved to be the closed retained
matrix circuit; it is not a certificate supplied by the network. -/
lemma coordinateEval_eq_closedCircuit (T : g.Tensors D) :
    g.coordinateEval D T = ∑ a, circuit (g.stepMatrix D T) (n+1) (g.closingEquiv D a) a := by
  calc
    _ = ∑ h : {h : g.StatePath D // g.Consistent D h}, g.pathTensorProduct D T h.val :=
      g.coordinateEval_eq_consistent_sum D T
    _ = ∑ h : g.StatePath D, if g.Consistent D h then g.pathTensorProduct D T h else 0 := by
      simpa only [Finset.sum_filter] using (Finset.sum_subtype
        (Finset.univ.filter (g.Consistent D)) (by simp) (g.pathTensorProduct D T)).symm
    _ = ∑ h : g.StatePath D, pathWeight (g.stepMatrix D T) (n+1) h * g.closingDelta D h := by
      apply Finset.sum_congr rfl
      intro h _
      exact (g.pathWeight_with_closure D T h).symm
    _ = ∑ a, ∑ b, circuit (g.stepMatrix D T) (n+1) b a *
        if g.initialEquiv D a = g.finalEquiv D b then 1 else 0 := by
      simpa [closingDelta,closes,initialEquiv,finalEquiv] using
        (circuit_path_expansion (g.stepMatrix D T) (n+1)
          (fun a b => if g.initialEquiv D a = g.finalEquiv D b then (1 : ℝ) else 0))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      simp_rw [← g.closingEquiv_eq_iff D a]
      simp

/-- Exactly one physical dimension factor. No retained frontier dimension
appears, regardless of the number of simultaneously live coordinates. -/
theorem coordinateEval_bound (T : g.Tensors D) :
    |g.coordinateEval D T| ≤ (D : ℝ) *
      ∏ v : Fin (n+1), ‖matrixCLMEquiv (g.vertexMatrix D T v)‖ := by
  rw [g.coordinateEval_eq_closedCircuit D T]
  -- Use the already proved energy bound of the actual stage matrices directly.
  have h := (circuit_bound (g.stepMatrix D T) (fun k => (g.stageNorm D T k)^2)
    (fun k => sq_nonneg _) (g.stepMatrix_energy D T) (n+1)).reindex
      (g.closingEquiv D) (Equiv.refl (g.State D 0))
  rw [Finset.prod_pow] at h
  have ht := h.trace_abs (Finset.prod_nonneg (fun k _ => g.stageNorm_nonneg D T k))
  have hcard : Fintype.card (g.State D 0) = D := by
    simpa using Fintype.card_congr (g.initialEquiv D)
  rw [hcard] at ht
  have hp : (∏ k ∈ Finset.range (n+1),g.stageNorm D T k) =
      ∏ v : Fin (n+1), ‖matrixCLMEquiv (g.vertexMatrix D T v)‖ := by
    rw [← Fin.prod_univ_eq_prod_range]
    apply Finset.prod_congr rfl
    intro v _
    simp [stageNorm,v.isLt]
  simpa only [hp,Equiv.refl_apply] using ht

end AcceleratedLogConcave.Tensor.Ordered.Graph

noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Classical
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
variable {n : ℕ} {Edge : Type*} [Fintype Edge] (g : Ordered.Graph n Edge) (D : ℕ)

/-- The final retained operator is a literal matrix on the one physical cut coordinate. -/
def retainedMatrix (T : g.Tensors D) : Matrix (Fin D) (Fin D) ℝ :=
  fun o i => circuit (g.stepMatrix D T) (n+1)
    ((g.finalEquiv D).symm o) ((g.initialEquiv D).symm i)

lemma coordinateEval_eq_trace (T : g.Tensors D) :
    g.coordinateEval D T = Matrix.trace (g.retainedMatrix D T) := by
  rw [g.coordinateEval_eq_closedCircuit D T]
  unfold Matrix.trace
  rw [← (g.initialEquiv D).sum_comp]
  apply Finset.sum_congr rfl
  intro a _
  simp [retainedMatrix,closingEquiv]

lemma retainedMatrix_energy (T : g.Tensors D) :
    EnergyBound (g.retainedMatrix D T)
      ((∏ v : Fin (n+1), ‖matrixCLMEquiv (g.vertexMatrix D T v)‖)^2) := by
  have h := (circuit_bound (g.stepMatrix D T) (fun k => (g.stageNorm D T k)^2)
    (fun k => sq_nonneg _) (g.stepMatrix_energy D T) (n+1)).reindex
      (g.finalEquiv D).symm (g.initialEquiv D).symm
  rw [Finset.prod_pow] at h
  have hp : (∏ k ∈ Finset.range (n+1),g.stageNorm D T k) =
      ∏ v : Fin (n+1), ‖matrixCLMEquiv (g.vertexMatrix D T v)‖ := by
    rw [← Fin.prod_univ_eq_prod_range]
    apply Finset.prod_congr rfl
    intro v _
    simp [stageNorm,v.isLt]
  rw [hp] at h
  exact h

lemma retainedMatrix_norm_le (T : g.Tensors D) :
    ‖matrixCLMEquiv (g.retainedMatrix D T)‖ ≤
      ∏ v : Fin (n+1), ‖matrixCLMEquiv (g.vertexMatrix D T v)‖ :=
  opNorm_le_of_energyBound _ _ (Finset.prod_nonneg (fun _ _ => norm_nonneg _))
    (g.retainedMatrix_energy D T)

lemma coordinateEval_abs_le_trace_norm (T : g.Tensors D) :
    |g.coordinateEval D T| ≤ (D : ℝ) * ‖matrixCLMEquiv (g.retainedMatrix D T)‖ := by
  rw [g.coordinateEval_eq_trace D T]
  simpa only [Matrix.trace,Matrix.diag,Fintype.card_fin] using
    (energyBound_opNorm (g.retainedMatrix D T)).trace_abs (norm_nonneg _)

lemma vertexMatrix_norm_eq_splitNorm (T : g.Tensors D) (v : Fin (n+1)) :
    ‖matrixCLMEquiv (g.vertexMatrix D T v)‖ = splitNorm D outputSlots (T v) :=
  sum_unfold_norm (I := g.InPort v) (O := g.OutPort v) D (T v)

lemma stepMatrix_norm_le_splitNorm (T : g.Tensors D) (v : Fin (n+1)) :
    ‖matrixCLMEquiv (g.stepMatrix D T v.val)‖ ≤ splitNorm D outputSlots (T v) := by
  have h := opNorm_le_of_energyBound _ _ (g.stageNorm_nonneg D T v.val)
    (g.stepMatrix_energy D T v.val)
  simpa only [stageNorm,Fin.is_lt,dite_true,g.vertexMatrix_norm_eq_splitNorm D T] using h

/-- The selected incoming/outgoing split is genuinely nontrivial under admissibility. -/
lemma outputSlots_nontrivial_of_admissible (ha : g.Admissible) (v : Fin (n+1)) :
    NontrivialSplit (outputSlots : Finset (g.Slot v)) := by
  let _ := (ha v).1
  let _ := (ha v).2
  exact outputSlots_nontrivial (I := g.InPort v) (O := g.OutPort v)

/-- Exact selected-split bound, with one and only one physical dimension factor. -/
theorem coordinateEval_split_bound (T : g.Tensors D) :
    |g.coordinateEval D T| ≤ (D : ℝ) *
      ∏ v : Fin (n+1), splitNorm D outputSlots (T v) := by
  simpa only [g.vertexMatrix_norm_eq_splitNorm D T] using g.coordinateEval_bound D T

/-- Manuscript ordered-contraction estimate from a bound on every nonempty proper split.
The only analytic input is the supplied bound on the actual rectangular Hilbert operator;
no coefficient Hilbert--Schmidt norm is substituted for it. -/
theorem orderedContraction_bound (ha : g.Admissible) (T : g.Tensors D)
    (B : Fin (n+1) → ℝ)
    (hB : ∀ v (S : Finset (g.Slot v)), NontrivialSplit S → splitNorm D S (T v) ≤ B v) :
    |g.coordinateEval D T| ≤ (D : ℝ) * ∏ v, B v := by
  apply (g.coordinateEval_split_bound D T).trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg D)
  apply Finset.prod_le_prod₀ (fun v _ => splitNorm_nonneg D outputSlots (T v))
  intro v _
  exact hB v outputSlots (g.outputSlots_nontrivial_of_admissible ha v)

/-- The zero-dimensional boundary is the empty closing-coordinate sum. -/
lemma coordinateEval_zero_dimension (T : g.Tensors 0) : g.coordinateEval 0 T = 0 := by
  apply abs_eq_zero.mp
  apply le_antisymm _ (abs_nonneg _)
  simpa only [Nat.cast_zero,zero_mul] using g.coordinateEval_bound 0 T

end AcceleratedLogConcave.Tensor.Ordered.Graph

noncomputable section
namespace AcceleratedLogConcave.Tensor.Ordered
namespace Graph
open scoped Classical
variable {n : ℕ} {Edge : Type*} (g : Graph n Edge)

/-- Preserve all old labels and add one fresh, ordered edge. -/
def addOrderedEdge (u v : Fin (n+1)) (h : u < v) : Graph n (Option Edge) where
  source | none => u | some e => g.source e
  target | none => v | some e => g.target e
  forward | none => h | some e => g.forward e

def oldWire : Option Edge ↪ Option (Option Edge) where
  toFun := Option.map some
  inj' := by intro a b h; cases a <;> cases b <;> simp_all

def addEdgeInEmbedding (u v : Fin (n+1)) (h : u < v) (w : Fin (n+1)) :
    g.InPort w ↪ (g.addOrderedEdge u v h).InPort w where
  toFun p := ⟨oldWire p.val, by cases p with | mk p hp => cases p <;> exact hp⟩
  inj' _a _b h := Subtype.ext (oldWire.injective (congrArg Subtype.val h))

def addEdgeOutEmbedding (u v : Fin (n+1)) (h : u < v) (w : Fin (n+1)) :
    g.OutPort w ↪ (g.addOrderedEdge u v h).OutPort w where
  toFun p := ⟨oldWire p.val, by cases p with | mk p hp => cases p <;> exact hp⟩
  inj' _a _b h := Subtype.ext (oldWire.injective (congrArg Subtype.val h))

theorem addOrderedEdge_admissible (hg : g.Admissible)
    (u v : Fin (n+1)) (h : u < v) : (g.addOrderedEdge u v h).Admissible := by
  intro w
  rcases hg w with ⟨⟨i⟩,⟨o⟩⟩
  exact ⟨⟨g.addEdgeInEmbedding u v h w i⟩,⟨g.addEdgeOutEmbedding u v h w o⟩⟩

/-- An edge may be added between either pair of distinct occurrences; its
orientation is chosen from the existing order. -/
theorem exists_addEdge_admissible (hg : g.Admissible)
    (u v : Fin (n+1)) (huv : u ≠ v) :
    ∃ a b : Fin (n+1), (a = u ∧ b = v ∨ a = v ∧ b = u) ∧
      ∃ h : a < b, (g.addOrderedEdge a b h).Admissible := by
  rcases lt_or_gt_of_ne huv with h | h
  · exact ⟨u,v,Or.inl ⟨rfl,rfl⟩,h,g.addOrderedEdge_admissible hg u v h⟩
  · exact ⟨v,u,Or.inr ⟨rfl,rfl⟩,h,g.addOrderedEdge_admissible hg v u h⟩

/-- Insert two consecutive children at the position of the old parent. The
Boolean selects the second child only when `v` is the parent. -/
def splitVertex (p v : Fin (n+1)) (second : Bool) : Fin (n+2) :=
  ⟨if v.val < p.val then v.val else if p.val < v.val then v.val+1
    else p.val + if second then 1 else 0, by
      have := v.isLt
      have := p.isLt
      split_ifs <;> omega⟩

lemma splitVertex_strict (p u v : Fin (n+1)) (a b : Bool) (h : u < v) :
    splitVertex p u a < splitVertex p v b := by
  simp only [splitVertex, Fin.lt_def] at *
  split_ifs <;> omega

lemma splitVertex_ne_parent (p v : Fin (n+1)) (h : v ≠ p) (b : Bool) :
    splitVertex p v b = splitVertex p v false := by
  apply Fin.ext
  have hh : v.val ≠ p.val := fun h' => h (Fin.ext h')
  simp only [splitVertex]
  split_ifs <;> omega

@[simp] lemma splitVertex_parent_false (p : Fin (n+1)) :
    splitVertex p p false = p.castSucc := by ext; simp [splitVertex]
@[simp] lemma splitVertex_parent_true (p : Fin (n+1)) :
    splitVertex p p true = p.succ := by ext; simp [splitVertex]

lemma splitVertex_zero (p : Fin (n+1)) : splitVertex p 0 false = 0 := by
  ext
  simp only [splitVertex, Fin.val_zero, Bool.false_eq_true, ↓reduceIte]
  split_ifs <;> omega

lemma splitVertex_last (p : Fin (n+1)) :
    splitVertex p (Fin.last n) true = Fin.last (n+1) := by
  ext
  have := p.isLt
  simp only [splitVertex, Fin.val_last, ↓reduceIte]
  split_ifs <;> omega

/-- At the first occurrence the sole incoming port is the input cut port. -/
lemma first_inPort (q : g.InPort 0) : q.val = none := by
  rcases q with ⟨_ | e,h⟩
  · rfl
  · have hf := g.forward e
    simp only [incoming, Fin.ext_iff, Fin.val_zero] at h
    simp only [Fin.lt_def] at hf
    omega

/-- At the last occurrence the sole outgoing port is the output cut port. -/
lemma last_outPort (q : g.OutPort (Fin.last n)) : q.val = none := by
  rcases q with ⟨_ | e,h⟩
  · rfl
  · have hf := g.forward e
    have ht := (g.target e).isLt
    simp only [outgoing, Fin.ext_iff, Fin.val_last] at h
    simp only [Fin.lt_def] at hf
    omega

def replacementInFlag (p : Fin (n+1)) (part : g.Slot p → Bool) (e : Edge) : Bool :=
  if h : g.target e = p then part (.inl ⟨some e,h⟩) else false

def replacementOutFlag (p : Fin (n+1)) (part : g.Slot p → Bool) (e : Edge) : Bool :=
  if h : g.source e = p then part (.inr ⟨some e,h⟩) else false

/-- Replace the parent by two consecutive children, redirect each labeled old
edge according to its inherited slot, and add a fresh joining edge. -/
def replaceVertex (p : Fin (n+1)) (part : g.Slot p → Bool) : Graph (n+1) (Option Edge) where
  source
    | none => p.castSucc
    | some e => splitVertex p (g.source e) (g.replacementOutFlag p part e)
  target
    | none => p.succ
    | some e => splitVertex p (g.target e) (g.replacementInFlag p part e)
  forward
    | none => by simp [Fin.lt_def]
    | some e => splitVertex_strict p _ _ _ _ (g.forward e)

lemma replace_in_other (p v : Fin (n+1)) (part : g.Slot p → Bool)
    (hv : v ≠ p) (q : g.InPort v) :
    (g.replaceVertex p part).incoming (splitVertex p v false) (oldWire q.val) := by
  rcases q with ⟨_ | e,h⟩
  · change v = 0 at h
    subst v
    exact splitVertex_zero p
  · change g.target e = v at h
    subst v
    change splitVertex p (g.target e) (g.replacementInFlag p part e) =
      splitVertex p (g.target e) false
    exact splitVertex_ne_parent p _ hv _

lemma replace_out_other (p v : Fin (n+1)) (part : g.Slot p → Bool)
    (hv : v ≠ p) (q : g.OutPort v) :
    (g.replaceVertex p part).outgoing (splitVertex p v false) (oldWire q.val) := by
  rcases q with ⟨_ | e,h⟩
  · change v = Fin.last n at h
    subst v
    change splitVertex p (Fin.last n) false = Fin.last (n+1)
    rw [← splitVertex_ne_parent p _ hv true]
    exact splitVertex_last p
  · change g.source e = v at h
    subst v
    change splitVertex p (g.source e) (g.replacementOutFlag p part e) =
      splitVertex p (g.source e) false
    exact splitVertex_ne_parent p _ hv _

/-- Every unaffected occurrence retains an injective copy of its old inputs. -/
def replaceInOtherEmbedding (p v : Fin (n+1)) (part : g.Slot p → Bool) (hv : v ≠ p) :
    g.InPort v ↪ (g.replaceVertex p part).InPort (splitVertex p v false) where
  toFun q := ⟨oldWire q.val,g.replace_in_other p v part hv q⟩
  inj' _a _b h := Subtype.ext (oldWire.injective (congrArg Subtype.val h))

/-- Every unaffected occurrence retains an injective copy of its old outputs. -/
def replaceOutOtherEmbedding (p v : Fin (n+1)) (part : g.Slot p → Bool) (hv : v ≠ p) :
    g.OutPort v ↪ (g.replaceVertex p part).OutPort (splitVertex p v false) where
  toFun q := ⟨oldWire q.val,g.replace_out_other p v part hv q⟩
  inj' _a _b h := Subtype.ext (oldWire.injective (congrArg Subtype.val h))

/-- An inherited input is redirected to exactly the child receiving its slot.
The incoming witness forces the input cut to the first child when `p = 0`. -/
lemma replace_in_parent (p : Fin (n+1)) (part : g.Slot p → Bool)
    (hI : ∃ q : g.InPort p, part (.inl q) = false) (q : g.InPort p) :
    (g.replaceVertex p part).incoming (splitVertex p p (part (.inl q)))
      (oldWire q.val) := by
  rcases q with ⟨_ | e,h⟩
  · change p = 0 at h
    subst p
    rcases hI with ⟨q,hq⟩
    have he : q = ⟨none,rfl⟩ := Subtype.ext (g.first_inPort q)
    subst q
    change splitVertex 0 0 (part (.inl ⟨none,rfl⟩)) = 0
    rw [hq]
    exact splitVertex_zero 0
  · change g.target e = p at h
    change splitVertex p (g.target e) (g.replacementInFlag p part e) =
      splitVertex p p (part (.inl ⟨some e,h⟩))
    simp [replacementInFlag,h]

/-- An inherited output is redirected to exactly the child receiving its slot.
The outgoing witness forces the output cut to the second child at the end. -/
lemma replace_out_parent (p : Fin (n+1)) (part : g.Slot p → Bool)
    (hO : ∃ q : g.OutPort p, part (.inr q) = true) (q : g.OutPort p) :
    (g.replaceVertex p part).outgoing (splitVertex p p (part (.inr q)))
      (oldWire q.val) := by
  rcases q with ⟨_ | e,h⟩
  · change p = Fin.last n at h
    subst p
    rcases hO with ⟨q,hq⟩
    have he : q = ⟨none,rfl⟩ := Subtype.ext (g.last_outPort q)
    subst q
    change splitVertex (Fin.last n) (Fin.last n) (part (.inr ⟨none,rfl⟩)) =
      Fin.last (n+1)
    rw [hq]
    exact splitVertex_last (Fin.last n)
  · change g.source e = p at h
    change splitVertex p (g.source e) (g.replacementOutFlag p part e) =
      splitVertex p p (part (.inr ⟨some e,h⟩))
    simp [replacementOutFlag,h]

def replaceInChildEmbedding (p : Fin (n+1)) (part : g.Slot p → Bool)
    (hI : ∃ q : g.InPort p, part (.inl q) = false) (b : Bool) :
    {q : g.InPort p // part (.inl q) = b} ↪
      (g.replaceVertex p part).InPort (splitVertex p p b) where
  toFun q := ⟨oldWire q.val.val, by
    have h := g.replace_in_parent p part hI q.val
    rwa [q.property] at h⟩
  inj' a b h := by
    apply Subtype.ext
    apply Subtype.ext
    exact oldWire.injective (congrArg Subtype.val h)

def replaceOutChildEmbedding (p : Fin (n+1)) (part : g.Slot p → Bool)
    (hO : ∃ q : g.OutPort p, part (.inr q) = true) (b : Bool) :
    {q : g.OutPort p // part (.inr q) = b} ↪
      (g.replaceVertex p part).OutPort (splitVertex p p b) where
  toFun q := ⟨oldWire q.val.val, by
    have h := g.replace_out_parent p part hO q.val
    rwa [q.property] at h⟩
  inj' a b h := by
    apply Subtype.ext
    apply Subtype.ext
    exact oldWire.injective (congrArg Subtype.val h)

lemma splitVertex_cover (p : Fin (n+1)) (w : Fin (n+2)) :
    w = p.castSucc ∨ w = p.succ ∨
      ∃ v : Fin (n+1), v ≠ p ∧ splitVertex p v false = w := by
  by_cases h₁ : w.val < p.val
  · right; right
    have hv : w.val < n+1 := by have := p.isLt; omega
    refine ⟨⟨w.val,hv⟩,?_,?_⟩
    · intro h; have hh := congrArg Fin.val h; change w.val = p.val at hh; omega
    · apply Fin.ext; simp [splitVertex,h₁]
  · by_cases h₂ : w.val = p.val
    · left; exact Fin.ext h₂
    · by_cases h₃ : w.val = p.val+1
      · right; left; exact Fin.ext h₃
      · right; right
        have hv : w.val-1 < n+1 := by have := w.isLt; omega
        refine ⟨⟨w.val-1,hv⟩,?_,?_⟩
        · intro h; have hh := congrArg Fin.val h; change w.val-1 = p.val at hh; omega
        · apply Fin.ext
          have hh : p.val < w.val-1 := by omega
          simp only [splitVertex,Fin.val_mk]
          split_ifs <;> omega

/-- The fresh joining edge provides the first child's output and the second
child's input. All other required ports are genuinely inherited. -/
theorem replaceVertex_admissible (hg : g.Admissible)
    (p : Fin (n+1)) (part : g.Slot p → Bool)
    (hI : ∃ q : g.InPort p, part (.inl q) = false)
    (hO : ∃ q : g.OutPort p, part (.inr q) = true) :
    (g.replaceVertex p part).Admissible := by
  intro w
  rcases splitVertex_cover p w with rfl | rfl | ⟨v,hv,rfl⟩
  · rcases hI with ⟨i,hi⟩
    have h := g.replace_in_parent p part ⟨i,hi⟩ i
    rw [hi,splitVertex_parent_false] at h
    exact ⟨⟨⟨oldWire i.val,h⟩⟩,⟨⟨some none,rfl⟩⟩⟩
  · rcases hO with ⟨o,ho⟩
    have h := g.replace_out_parent p part ⟨o,ho⟩ o
    rw [ho,splitVertex_parent_true] at h
    exact ⟨⟨⟨some none,rfl⟩⟩,⟨⟨oldWire o.val,h⟩⟩⟩
  · rcases hg v with ⟨⟨i⟩,⟨o⟩⟩
    exact ⟨⟨g.replaceInOtherEmbedding p v part hv i⟩,
      ⟨g.replaceOutOtherEmbedding p v part hv o⟩⟩

/-- The precise two-child orientation criterion. -/
lemma child_orientation {IA OA IB OB : Prop}
    (hI : IA ∨ IB) (hO : OA ∨ OB) (hA : IA ∨ OA) (hB : IB ∨ OB) :
    (IA ∧ OB) ∨ (IB ∧ OA) := by tauto

/-- Each nonempty child partition admits one of the two consecutive orders. -/
theorem partition_orientation (hg : g.Admissible) (p : Fin (n+1))
    (part : g.Slot p → Bool)
    (hA : ∃ s, part s = false) (hB : ∃ s, part s = true) :
    ((∃ q : g.InPort p, part (.inl q) = false) ∧
      (∃ q : g.OutPort p, part (.inr q) = true)) ∨
    ((∃ q : g.InPort p, part (.inl q) = true) ∧
      (∃ q : g.OutPort p, part (.inr q) = false)) := by
  apply child_orientation
  · rcases (hg p).1 with ⟨q⟩
    cases h : part (.inl q) with
    | false => exact Or.inl ⟨q,h⟩
    | true => exact Or.inr ⟨q,h⟩
  · rcases (hg p).2 with ⟨q⟩
    cases h : part (.inr q) with
    | false => exact Or.inl ⟨q,h⟩
    | true => exact Or.inr ⟨q,h⟩
  · rcases hA with ⟨q,hq⟩
    cases q with
    | inl q => exact Or.inl ⟨q,hq⟩
    | inr q => exact Or.inr ⟨q,hq⟩
  · rcases hB with ⟨q,hq⟩
    cases q with
    | inl q => exact Or.inl ⟨q,hq⟩
    | inr q => exact Or.inr ⟨q,hq⟩

/-- A concrete admissible refined graph exists in one of the two child orders.
Its edge inventory is exactly the old labels plus one fresh joining label. -/
theorem replacement_admissible_either_order (hg : g.Admissible)
    (p : Fin (n+1)) (part : g.Slot p → Bool)
    (hA : ∃ s, part s = false) (hB : ∃ s, part s = true) :
    (g.replaceVertex p part).Admissible ∨
      (g.replaceVertex p (fun s => !(part s))).Admissible := by
  rcases g.partition_orientation hg p part hA hB with ⟨hi,ho⟩ | ⟨hi,ho⟩
  · exact Or.inl (g.replaceVertex_admissible hg p part hi ho)
  · right
    apply g.replaceVertex_admissible hg
    · rcases hi with ⟨q,hq⟩
      exact ⟨q,by simp [hq]⟩
    · rcases ho with ⟨q,hq⟩
      exact ⟨q,by simp [hq]⟩

/-- The selected admissible replacement together with the old-slot orientation
witnesses needed by the inherited-port embeddings, including the cut ports. -/
theorem exists_oriented_replacement (hg : g.Admissible)
    (p : Fin (n+1)) (part : g.Slot p → Bool)
    (hA : ∃ s, part s = false) (hB : ∃ s, part s = true) :
    ∃ chosen : g.Slot p → Bool,
      (chosen = part ∨ chosen = fun s => !(part s)) ∧
      (∃ q : g.InPort p, chosen (.inl q) = false) ∧
      (∃ q : g.OutPort p, chosen (.inr q) = true) ∧
      (g.replaceVertex p chosen).Admissible := by
  rcases g.partition_orientation hg p part hA hB with ⟨hi,ho⟩ | ⟨hi,ho⟩
  · exact ⟨part,Or.inl rfl,hi,ho,g.replaceVertex_admissible hg p part hi ho⟩
  · have hi' : ∃ q : g.InPort p, (!part (.inl q)) = false := by
      obtain ⟨q,hq⟩ := hi
      exact ⟨q,by simp [hq]⟩
    have ho' : ∃ q : g.OutPort p, (!part (.inr q)) = true := by
      obtain ⟨q,hq⟩ := ho
      exact ⟨q,by simp [hq]⟩
    exact ⟨(fun s => !part s),Or.inr rfl,hi',ho',
      g.replaceVertex_admissible hg p _ hi' ho'⟩

lemma splitVertex_eq_implies (p u v : Fin (n+1)) (a b : Bool)
    (h : splitVertex p u a = splitVertex p v b) : u = v := by
  by_contra huv
  rcases lt_or_gt_of_ne huv with hlt | hlt
  · have hh := splitVertex_strict p u v a b hlt
    exact (ne_of_lt hh) h
  · have hh := splitVertex_strict p v u b a hlt
    exact (ne_of_lt hh) h.symm

lemma replaceInOtherEmbedding_surjective (p v : Fin (n+1))
    (part : g.Slot p → Bool) (hv : v ≠ p) :
    Function.Surjective (g.replaceInOtherEmbedding p v part hv) := by
  rintro ⟨(_ | (_ | e)),h⟩
  · change splitVertex p v false = 0 at h
    have he : v = 0 := splitVertex_eq_implies p v 0 false false
      (h.trans (splitVertex_zero p).symm)
    exact ⟨⟨none,he⟩,rfl⟩
  · change p.succ = splitVertex p v false at h
    have he : v = p := splitVertex_eq_implies p v p false true
      (h.symm.trans (splitVertex_parent_true p).symm)
    exact False.elim (hv he)
  · change splitVertex p (g.target e) (g.replacementInFlag p part e) =
      splitVertex p v false at h
    have he : g.target e = v := splitVertex_eq_implies p _ _ _ _ h
    exact ⟨⟨some e,he⟩,rfl⟩

lemma replaceOutOtherEmbedding_surjective (p v : Fin (n+1))
    (part : g.Slot p → Bool) (hv : v ≠ p) :
    Function.Surjective (g.replaceOutOtherEmbedding p v part hv) := by
  rintro ⟨(_ | (_ | e)),h⟩
  · change splitVertex p v false = Fin.last (n+1) at h
    have he : v = Fin.last n := splitVertex_eq_implies p v (Fin.last n) false true
      (h.trans (splitVertex_last p).symm)
    exact ⟨⟨none,he⟩,rfl⟩
  · change p.castSucc = splitVertex p v false at h
    have he : v = p := splitVertex_eq_implies p v p false false
      (h.symm.trans (splitVertex_parent_false p).symm)
    exact False.elim (hv he)
  · change splitVertex p (g.source e) (g.replacementOutFlag p part e) =
      splitVertex p v false at h
    have he : g.source e = v := splitVertex_eq_implies p _ _ _ _ h
    exact ⟨⟨some e,he⟩,rfl⟩

/-- Unaffected occurrences have exactly their old incoming ports. -/
def replaceInOtherEquiv (p v : Fin (n+1)) (part : g.Slot p → Bool) (hv : v ≠ p) :
    g.InPort v ≃ (g.replaceVertex p part).InPort (splitVertex p v false) :=
  Equiv.ofBijective (g.replaceInOtherEmbedding p v part hv)
    ⟨(g.replaceInOtherEmbedding p v part hv).injective,
      g.replaceInOtherEmbedding_surjective p v part hv⟩

/-- Unaffected occurrences have exactly their old outgoing ports. -/
def replaceOutOtherEquiv (p v : Fin (n+1)) (part : g.Slot p → Bool) (hv : v ≠ p) :
    g.OutPort v ≃ (g.replaceVertex p part).OutPort (splitVertex p v false) :=
  Equiv.ofBijective (g.replaceOutOtherEmbedding p v part hv)
    ⟨(g.replaceOutOtherEmbedding p v part hv).injective,
      g.replaceOutOtherEmbedding_surjective p v part hv⟩

end Graph
end AcceleratedLogConcave.Tensor.Ordered
