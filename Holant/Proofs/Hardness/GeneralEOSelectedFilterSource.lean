import Holant.Proofs.Hardness.GeneralEOFiniteMacroSource

/-! Independent selected pairings are implemented by actual DEQ4 filter
networks. Different source labels may refer to the same original target row.
The resulting source uses its own generated field and the target codec is
unchanged. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOSelectedFilterSource
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open FixedGadgetSubstitution
namespace N
export GeneralEODEQPairingFilter (network denote native)
end N
namespace L
export Holant.LocalDrafts.Tractability.EOEvaluation.PairLift (Compatible restrict)
end L
namespace O
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget
  (originalPresentation originalValue)
end O
namespace M
export GeneralEODEQPairingTemplates (family)
end M
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option Elab.async false
variable (K : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ K := K.algebra'
variable {d s t : ℕ} {a b : ℕ → ℕ}
variable (F : FixedField K d) (T : ExactSignatureTables d s 1 a)
variable (H : (i : Fin t) → Signature K (b i.val))
variable (G : (i : Fin t) → Signature AlgebraicComplex (b i.val))
variable (P : (i : Fin t) → OrientedPerfectPairing (b i.val))
variable (label : Fin t → Fin s)
variable (slots : ∀i,(⟨a (label i).val,M.family F T (label i)⟩ : AnySignature K)=⟨b i.val,H i⟩)
variable (e : Fin s) (hE : (⟨a e.val,M.family F T e⟩ : AnySignature K)=⟨4,ExactTwoSignatures.E⟩)

noncomputable def labels (i : Fin t) : Labelling (N.network (P i) (H i)).shape s 1 a where
  vertex := Fin.cases (label i) (fun _ => e)
  vertex_arity v := by
    induction v using Fin.cases with
    | zero => exact congrArg Sigma.fst (slots i)
    | succ j => exact congrArg Sigma.fst hE
  edge _ := 0

theorem exact_labels (i : Fin t) : LabelledNetwork.Exact (M.family F T)
    (N.network (P i) (H i)) (labels K F T H P label slots e hE i) := by
  intro v
  induction v using Fin.cases with
  | zero => exact slots i
  | succ j => exact hE

private theorem apply_exact {A : Type} {m n : ℕ} (f : Signature A m) (g : Signature A n)
    (eqn : (⟨m,f⟩ : AnySignature A)=⟨n,g⟩) (h : m=n) (x : Fin n → Bool) :
    f (fun i => x (Fin.cast h i))=g x := by
  cases eqn
  rfl

variable (native : ∀i x y,F.decode (T.edge i x y)=Signature.disequality x y)
variable (values : ∀i x,(H i x : AlgebraicComplex)=G i x)

include native in
theorem template_denote (i : Fin t) :
    ((labels K F T H P label slots e hE i).template.network
      (labels K F T H P label slots e hE i).wellFormed (M.family F T)
      (fun j x y => F.decode (T.edge j x y))).denote=
      fun x => if L.Compatible (P i) x then H i x else 0 := by
  calc
    _=(N.network (P i) (H i)).denote := by
      apply (labels K F T H P label slots e hE i).denote_template_of_labels
      · intro v x
        exact apply_exact _ _ (exact_labels K F T H P label slots e hE i v) _ x
      · intro j x y
        exact native _ x y
    _=_ := N.denote (P i) (H i)

noncomputable def templates (k : ℕ) : Template :=
  if hk : k<t then (labels K F T H P label slots e hE ⟨k,hk⟩).template
  else identityTemplate b k

theorem valid : ∀k<t,(templates K F T H P label slots e hE k).WellFormed s 1 a := by
  intro k hk
  simpa only [templates,dite_eq_left hk] using (labels K F T H P label slots e hE ⟨k,hk⟩).wellFormed

theorem arity_eq (i : Fin t) : b i.val=sourceArity (templates K F T H P label slots e hE) i.val := by
  simp [sourceArity,templates,i.isLt,Labelling.template]

def restricted (i : Fin t) : Signature AlgebraicComplex (b i.val) := L.restrict (P i) (G i)

private theorem signature_congr (g h : Template) (hg : g.WellFormed s 1 a)
    (hh : h.WellFormed s 1 a) (same : g=h) :
    (⟨g.boundary,(g.network hg (M.family F T) (fun j x y => F.decode (T.edge j x y))).denote⟩ : AnySignature K)=
      ⟨h.boundary,(h.network hh (M.family F T) (fun j x y => F.decode (T.edge j x y))).denote⟩ := by
  subst h
  rfl

include native in
theorem signature_exact (i : Fin t) :
    (⟨sourceArity (templates K F T H P label slots e hE) i.val,
      fun x => F.decode (templateCoordinates F (templates K F T H P label slots e hE)
        (valid K F T H P label slots e hE) T i x)⟩ : AnySignature K)=
      ⟨b i.val,fun x => if L.Compatible (P i) x then H i x else 0⟩ := by
  have hd : (fun x => F.decode (templateCoordinates F (templates K F T H P label slots e hE)
      (valid K F T H P label slots e hE) T i x))=
    ((templates K F T H P label slots e hE i.val).network
      (valid K F T H P label slots e hE i.val i.isLt) (M.family F T)
      (fun j x y => F.decode (T.edge j x y))).denote := by
    funext x
    exact decode_templateCoordinates F _ _ T i x
  rw [hd]
  change (⟨(templates K F T H P label slots e hE i.val).boundary,_⟩ : AnySignature K)=_
  apply (signature_congr K F T _ (labels K F T H P label slots e hE i).template
    (valid K F T H P label slots e hE i.val i.isLt)
    (labels K F T H P label slots e hE i).wellFormed (dite_eq_left i.isLt)).trans
  exact Sigma.ext rfl (heq_of_eq (template_denote K F T H P label slots e hE native i))

include native values in
theorem coordinates_exact (i : Fin t) (x : Fin (sourceArity (templates K F T H P label slots e hE) i.val) → Bool) :
    (F.decode (templateCoordinates F (templates K F T H P label slots e hE)
      (valid K F T H P label slots e hE) T i x) : AlgebraicComplex)=
      restricted G P i (fun j => x (Fin.cast (arity_eq K F T H P label slots e hE i) j)) := by
  have h := apply_exact _ _ (signature_exact K F T H P label slots e hE native i).symm
    (arity_eq K F T H P label slots e hE i) x
  rw [←h]
  unfold restricted L.restrict
  split_ifs
  · exact values i _
  · rfl

/-- A compiled original-field source for every finite selected restriction. -/
def source : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding t 1 b) (O.originalPresentation (restricted G P)).encoding
    (RawClosedNetwork.validatedEncoding s 1 a) F.encoding
    (O.originalValue (restricted G P)) (T.evaluate F) :=
  GeneralEOFiniteMacroSource.source K F T (templates K F T H P label slots e hE)
    (valid K F T H P label slots e hE) (restricted G P)
    (arity_eq K F T H P label slots e hE) native
    (coordinates_exact K F T H G P label slots e hE native values)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOSelectedFilterSource
