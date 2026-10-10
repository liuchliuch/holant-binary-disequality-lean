import Holant.Proofs.Dichotomy.Closure.Symmetric.GlobalCloseCompletionSymmetricGHZActual

/-! Enlarge an arbitrary ordinary source by finitely many algebraic constants
without adding vertices. Both the old oracle codec and every physical macro
are preserved through the actual generated number-field presentation. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSymmetricGHZField
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedGadgetSubstitution Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace O
export GlobalCloseCompletionUnaryOrdinaryFieldCodec (ambient controlled)
end O
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option maxRecDepth 16384
set_option Elab.async false
variable {r degree k : ℕ} {arity : ℕ→ℕ}
variable (L : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ L := L.algebra'
variable (F : FixedField L degree) (H : (i : Fin r)→Signature L (arity i.val))
variable (extra : Fin k→AlgebraicComplex)

def coefficients : ((Σi : Fin r,Fin (arity i.val)→Bool)⊕Fin k)→AlgebraicComplex
  | .inl ⟨i,x⟩=>(H i x : AlgebraicComplex)
  | .inr i=>extra i
theorem algebraic (i) : IsAlgebraic ℚ (coefficients L H extra i) := Algebra.IsAlgebraic.isAlgebraic _
abbrev field := familyField (coefficients L H extra)
local instance : Algebra ℚ (field L H extra) := (field L H extra).algebra'
abbrev presentation := familyPresentation (coefficients L H extra) (algebraic L H extra)
def table (i : Fin r) : Signature (field L H extra) (arity i.val) :=
  fun x=>fieldCoefficient (coefficients L H extra) (.inl ⟨i,x⟩)
def constant (i : Fin k) : field L H extra := fieldCoefficient (coefficients L H extra) (.inr i)
abbrev tables:=QuaternaryOrdinaryCompanion.tables (presentation L H extra) (table L H extra)
abbrev value:=(tables L H extra).evaluate (presentation L H extra)
abbrev inputEncoding:=RawClosedNetwork.validatedEncoding r 1 arity
abbrev oldCoefficients:=KSourceTransport.originalCoefficient (O.ambient L H)
abbrev oldPresentation:=KSourceTransport.originalPresentation (O.ambient L H)
abbrev oldValue:=KSourceTransport.originalValue (O.ambient L H)

theorem table_value (i : Fin r) (x : Fin (arity i.val)→Bool) :
    (table L H extra i x : AlgebraicComplex)=(H i x : AlgebraicComplex) := rfl
theorem constant_value (i : Fin k) : (constant L H extra i : AlgebraicComplex)=extra i := rfl

theorem value_exact (q : ExactSignatureTables.Input r 1 arity) :
    (value L H extra q : AlgebraicComplex)=(oldValue L H q : AlgebraicComplex) := by
  rw [OriginalFamily.value_exact]
  change (((tables L H extra).evaluate (presentation L H extra) q : field L H extra) : AlgebraicComplex)=_
  rw [ExactSignatureTables.evaluate_eq_decoded]
  change (field L H extra).subtype _=_
  rw [←Network.denote_map]
  congr 1
  unfold Network.map RawClosedNetwork.realize
  congr 1
  · funext v x
    simp only [tables,QuaternaryOrdinaryCompanion.tables,LinearEquiv.apply_symm_apply]
    rfl
  · funext e p q
    simp only [tables,QuaternaryOrdinaryCompanion.tables,LinearEquiv.apply_symm_apply]
    cases p <;> cases q <;> rfl

def recover : Computes (oldPresentation L H).encoding (presentation L H extra).encoding
    (FamilyAnswerTransport.recover (coefficients L H extra) (oldCoefficients L H)) :=
  FamilyAnswerTransport.computes _ _ (algebraic L H extra)
    (OriginalFamily.coefficient_algebraic (O.ambient L H) KSourceTransport.equalityEdges)

def canonical : LengthControlledOracleReduction
    (inputEncoding (r:=r) (arity:=arity)) (presentation L H extra).encoding
    (inputEncoding (r:=r) (arity:=arity)) (oldPresentation L H).encoding
    (value L H extra) (oldValue L H) :=
  controlledOneQueryOfEq (identityComputes (inputEncoding (r:=r) (arity:=arity))) (recover L H extra)
    ((OriginalFamily.tables (O.ambient L H) KSourceTransport.equalityEdges).outputBound (oldPresentation L H))
    (value L H extra) (fun q=>(FamilyAnswerTransport.recover_exact
      (coefficients L H extra) (oldCoefficients L H) (value L H extra q) (oldValue L H q)
      (value_exact L H extra q).symm).symm)

def controlled : LengthControlledOracleReduction
    (inputEncoding (r:=r) (arity:=arity)) (presentation L H extra).encoding
    (inputEncoding (r:=r) (arity:=arity)) F.encoding
    (value L H extra) ((QuaternaryOrdinaryCompanion.tables F H).evaluate F) :=
  Programme.compose (canonical L H extra) (O.controlled L F H)

section Graph
variable {n : ℕ} (N : NoXOrdinaryGraphAdjoin.Output H n)
def graph : Network (field L H extra) n := N.labels.sourceNetwork (table L H extra) (fun _ : Fin 1=>Signature.equality)

private theorem exact_cast {A : Type} {m n : ℕ} (f : Signature A m) (g : Signature A n)
    (h : (⟨m,f⟩ : AnySignature A)=⟨n,g⟩) (hn : m=n) (x : Fin n→Bool) :
    f (fun i=>x (Fin.cast hn i))=g x := by cases h; rfl

theorem map_graph : (graph L H extra N).map (field L H extra).subtype=N.network.map L.subtype := by
  unfold graph Network.map Labelling.sourceNetwork
  congr 1
  · funext v x
    change ((H (N.labels.vertex v) (fun i=>x (Fin.cast (N.labels.vertex_arity v) i)) : L) : AlgebraicComplex)=_
    exact congrArg (fun z : L=>(z:AlgebraicComplex))
      (exact_cast _ _ (N.exact v) (N.labels.vertex_arity v) x)
  · funext e p q
    rw [N.ordinary]
    cases p <;> cases q <;> rfl

def lift : NoXOrdinaryGraphAdjoin.Output (table L H extra) n where
  network:=graph L H extra N
  labels:=N.labels
  exact:=by
    intro v
    apply Sigma.ext (N.labels.vertex_arity v)
    exact HEq.symm (EdgeSubdivision.signature_cast_heq (N.labels.vertex_arity v)
      (table L H extra (N.labels.vertex v)))
  ordinary:=fun _=>rfl

theorem lift_value : RingHomRealization.mapSignature (field L H extra).subtype (lift L H extra N).network.denote=
    RingHomRealization.mapSignature L.subtype N.network.denote := by
  funext x
  change (field L H extra).subtype ((graph L H extra N).denote x)=L.subtype (N.network.denote x)
  rw [←Network.denote_map,←Network.denote_map,map_graph]


end Graph
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSymmetricGHZField
end
