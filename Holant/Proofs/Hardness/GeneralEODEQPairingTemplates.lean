import Holant.Proofs.Hardness.GeneralEODEQPairingFilter
import Holant.Proofs.Hardness.LabelledNetwork
import Holant.Proofs.Algorithms.MacroTransport

/-! Actual fixed-template source for arbitrary ordered pairing restrictions,
when the target contains a literal DEQ4. The byte compiler substitutes the
proved filter graphs and retains the target's original fixed-field codec. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEODEQPairingTemplates
open Holant Holant.Tractable Holant.Complexity FixedGadgetSubstitution
open Holant.Algebraic Computability
namespace N
export GeneralEODEQPairingFilter (network denote native)
end N
namespace L
export Holant.LocalDrafts.Tractability.EOEvaluation.PairLift (Compatible)
end L
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {K : Type} [Field K] {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature K (a i.val))
variable (P : (i : Fin s) → OrientedPerfectPairing (a i.val))
variable (e : Fin s) (hE : (⟨a e.val,G e⟩ : AnySignature K) = ⟨4,ExactTwoSignatures.E⟩)

def labelling (i : Fin s) : Labelling (N.network (P i) (G i)).shape s 1 a where
  vertex := Fin.cases i (fun _ => e)
  vertex_arity v := by
    induction v using Fin.cases with
    | zero => rfl
    | succ j => exact congrArg Sigma.fst hE
  edge _ := 0

theorem exact_labels (i : Fin s) :
    LabelledNetwork.Exact G (N.network (P i) (G i)) (labelling G P e hE i) := by
  intro v
  induction v using Fin.cases with
  | zero => rfl
  | succ j => exact hE

omit [Field K] in
private theorem apply_exact {m n : ℕ} (f : Signature K m) (g : Signature K n)
    (equation : (⟨m,f⟩ : AnySignature K) = ⟨n,g⟩) (h : m=n) (x : Fin n → Bool) :
    f (fun i => x (Fin.cast h i)) = g x := by
  cases equation
  rfl

theorem template_denote (i : Fin s) :
    ((labelling G P e hE i).template.network (labelling G P e hE i).wellFormed
      G (fun _ => Signature.disequality)).denote =
        fun x => if L.Compatible (P i) x then G i x else 0 := by
  calc
    _ = (N.network (P i) (G i)).denote := by
      apply (labelling G P e hE i).denote_template_of_labels
      · intro v x
        exact apply_exact _ _ (exact_labels G P e hE i v)
          ((labelling G P e hE i).vertex_arity v) x
      · intro j x y
        rfl
    _ = _ := N.denote (P i) (G i)

def templates (label : ℕ) : Template :=
  if h : label < s then (labelling G P e hE ⟨label,h⟩).template else identityTemplate a label

theorem valid : ∀ label < s, (templates G P e hE label).WellFormed s 1 a := by
  intro label h
  simpa only [templates,dite_eq_left h] using (labelling G P e hE ⟨label,h⟩).wellFormed

theorem arity_eq : sourceArity (templates G P e hE) = a := by
  funext label
  by_cases h : label < s
  · simp [sourceArity,templates,h,Labelling.template]
  · simp [sourceArity,templates,h,identityTemplate]

private theorem template_signature_congr (g h : Template)
    (hg : g.WellFormed s 1 a) (hh : h.WellFormed s 1 a) (same : g=h)
    (W : Fin 1 → Kernel K) :
    (⟨g.boundary,(g.network hg G W).denote⟩ : AnySignature K) =
      ⟨h.boundary,(h.network hh G W).denote⟩ := by
  subst h
  rfl

section Presented
variable [Algebra ℚ K] {d : ℕ}
variable (F : FixedField K d) (T : ExactSignatureTables d s 1 a)

def family (i : Fin s) : Signature K (a i.val) := fun x => F.decode (T.vertex i x)

variable (e : Fin s)
variable (hE : (⟨a e.val,family F T e⟩ : AnySignature K) = ⟨4,ExactTwoSignatures.E⟩)
abbrev sourceArity := FixedGadgetSubstitution.sourceArity (templates (family F T) P e hE)
abbrev coordinates := templateCoordinates F (templates (family F T) P e hE)
  (valid (family F T) P e hE) T
abbrev tables := sourceTables (templates (family F T) P e hE) T (coordinates P F T e hE)
abbrev inputEncoding := RawClosedNetwork.validatedEncoding s 1 (sourceArity P F T e hE)
abbrev value := (tables P F T e hE).evaluate F

/-- Concrete substitution, with actual valid queries and both answer and
query-length bounds. No target problem or complexity assertion is a premise. -/
def controlled : LengthControlledOracleReduction (inputEncoding P F T e hE) F.encoding
    (RawClosedNetwork.validatedEncoding s 1 a) F.encoding (value P F T e hE) (T.evaluate F) :=
  Holant.LocalDrafts.MainChain.MacroTransport.controlled F (templates (family F T) P e hE)
    (valid (family F T) P e hE) T

theorem signature_exact
    (native : ∀ j x y, F.decode (T.edge j x y) = Signature.disequality x y) (i : Fin s) :
    (⟨sourceArity P F T e hE i.val,fun x => F.decode (coordinates P F T e hE i x)⟩ :
      AnySignature K) =
        ⟨a i.val,fun x => if L.Compatible (P i) x then family F T i x else 0⟩ := by
  have hm : (fun x => F.decode (coordinates P F T e hE i x)) =
      ((templates (family F T) P e hE i.val).network
        (valid (family F T) P e hE i.val i.isLt) (family F T)
        (fun j x y => F.decode (T.edge j x y))).denote := by
    funext x
    exact decode_templateCoordinates F _ _ T i x
  rw [hm]
  change (⟨(templates (family F T) P e hE i.val).boundary,_⟩ : AnySignature K) = _
  apply (template_signature_congr (family F T)
    (templates (family F T) P e hE i.val) (labelling (family F T) P e hE i).template
    (valid (family F T) P e hE i.val i.isLt) (labelling (family F T) P e hE i).wellFormed
    (dite_eq_left i.isLt) (fun j x y => F.decode (T.edge j x y))).trans
  refine Sigma.ext ?_ ?_
  · rfl
  · apply heq_of_eq
    have hk : (fun j x y => F.decode (T.edge j x y)) = (fun _ => Signature.disequality) :=
      funext (fun j => funext (fun x => funext (fun y => native j x y)))
    rw [hk]
    exact template_denote (family F T) P e hE i
end Presented

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEODEQPairingTemplates
