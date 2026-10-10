import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXOrdinaryGraphAdjoin

/-! Normalize a genuine ordinary macro by its nonzero fixed-field scalar.
Every occurrence is expanded by the existing scaled compiler; all original
rows are retained literally. This supplies exact pins from scalar-pin graphs
without postulating physical scalar vertices. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIndependentPinsAdjoin
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open FixedGadgetSubstitution
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] {degree s : ℕ} {a : ℕ→ℕ}
variable (F : FixedField K degree) (H : (i : Fin s)→Signature K (a i.val))

export NoXOrdinaryGraphAdjoin (Output)
variable {n : ℕ} (d : Output H n) (c : K)
abbrev baseTables := QuaternaryOrdinaryCompanion.tables F H
abbrev template := d.labels.template
abbrev arity := sourceArity (Adjoin.templates s a (template H d))
abbrev coordinates := ScaledAdjoin.coordinates F (baseTables F H)
  (template H d) d.labels.wellFormed c
abbrev tables := sourceTables (Adjoin.templates s a (template H d)) (baseTables F H) (coordinates F H d c)
def signatures (i : Fin (s+1)) : Signature K (arity H d i.val) :=
  fun x=>F.decode ((tables F H d c).vertex i x)
abbrev inputEncoding := RawClosedNetwork.validatedEncoding (s+1) 1 (arity H d)
abbrev value := (tables F H d c).evaluate F

private theorem exact_cast {L : Type} {m n : ℕ} (f : Signature L m) (g : Signature L n)
    (h : (⟨m,f⟩ : AnySignature L)=⟨n,g⟩) (hn : m=n) (x : Fin n→Bool) :
    f (fun i=>x (Fin.cast hn i))=g x := by cases h; rfl

theorem macro_exact : ((template H d).network d.labels.wellFormed
    (fun i x=>F.decode ((baseTables F H).vertex i x))
    (fun j b c=>F.decode ((baseTables F H).edge j b c))).denote=
      d.network.denote := by
  simp only [baseTables,QuaternaryOrdinaryCompanion.tables,LinearEquiv.apply_symm_apply]
  rw [Labelling.denote_template]
  apply Network.denote_congr
  · intro v x
    exact exact_cast _ _ (d.exact v) (d.labels.vertex_arity v) x
  · intro e b c
    exact congrFun (congrFun (d.ordinary e).symm b) c

private def decodeAny (f : AnySignature (Fin degree→ℚ)) : AnySignature K :=
  ⟨f.1,fun x=>F.decode (f.2 x)⟩

def old (_H : (i : Fin s)→Signature K (a i.val)) (i : Fin s) : Fin (s+1) := Fin.castAdd 1 i
def newLabel (_H : (i : Fin s)→Signature K (a i.val)) : Fin (s+1) := ⟨s,Nat.lt_succ_self _⟩

theorem old_literal (i : Fin s) :
    (⟨arity H d (old H i).val,signatures F H d c (old H i)⟩ : AnySignature K)=⟨a i.val,H i⟩ := by
  have h : (⟨arity H d (old H i).val,coordinates F H d c (old H i)⟩ :
      AnySignature (Fin degree→ℚ))=⟨a i.val,(baseTables F H).vertex i⟩ :=
    Sigma.ext (Adjoin.old_boundary (template H d) i)
      (ScaledAdjoin.old_coordinates F (baseTables F H) (template H d) d.labels.wellFormed c i)
  refine (congrArg (decodeAny F) h).trans ?_
  apply congrArg (fun f : Signature K (a i.val)=>(⟨a i.val,f⟩ : AnySignature K))
  funext x
  exact LinearEquiv.apply_symm_apply _ _

theorem new_literal :
    (⟨arity H d (newLabel H).val,signatures F H d c (newLabel H)⟩ : AnySignature K)=
      ⟨n,fun x=>d.network.denote x/c⟩ := by
  have h : (⟨arity H d (newLabel H).val,coordinates F H d c (newLabel H)⟩ :
      AnySignature (Fin degree→ℚ))=
      ⟨n,fun x=>F.decode.symm (((template H d).network d.labels.wellFormed
        (fun i x=>F.decode ((baseTables F H).vertex i x))
        (fun j b c=>F.decode ((baseTables F H).edge j b c))).denote x/c)⟩ :=
    Sigma.ext (Adjoin.new_boundary (template H d))
      (ScaledAdjoin.new_coordinates F (baseTables F H) (template H d) d.labels.wellFormed c)
  refine (congrArg (decodeAny F) h).trans ?_
  apply congrArg (fun f : Signature K n=>(⟨n,f⟩ : AnySignature K))
  funext x
  change F.decode (F.decode.symm _)=_
  rw [LinearEquiv.apply_symm_apply,macro_exact]

theorem ordinary_tables : QuaternaryOrdinaryCompanion.tables F (signatures F H d c)=tables F H d c := by
  unfold QuaternaryOrdinaryCompanion.tables
  congr 1
  · funext i x
    exact F.decode.symm_apply_apply _

def source (hc : c≠0) : LengthControlledOracleReduction
    (inputEncoding H d) F.encoding (RawClosedNetwork.validatedEncoding s 1 a) F.encoding
    ((QuaternaryOrdinaryCompanion.tables F (signatures F H d c)).evaluate F)
    ((baseTables F H).evaluate F) := by
  rw [ordinary_tables]
  exact Holant.LocalDrafts.Hardness.ControlledCap.scaledAdjoin F (baseTables F H)
    (template H d) d.labels.wellFormed c hc

theorem normalized_literal (f : Signature K n) (hc : c≠0)
    (form : d.network.denote=fun x=>c*f x) :
    (⟨arity H d (newLabel H).val,signatures F H d c (newLabel H)⟩ : AnySignature K)=⟨n,f⟩ := by
  rw [new_literal,form]
  apply congrArg (fun g : Signature K n=>(⟨n,g⟩ : AnySignature K))
  funext x
  exact mul_div_cancel_left₀ (f x) hc

def lift {m : ℕ} (e : Output H m) : Output (signatures F H d c) m where
  network := e.network
  labels := {
    vertex v := old H (e.labels.vertex v)
    vertex_arity v := (congrArg Sigma.fst (old_literal F H d c (e.labels.vertex v))).trans
      (e.labels.vertex_arity v)
    edge _ := 0 }
  exact v := (old_literal F H d c (e.labels.vertex v)).trans (e.exact v)
  ordinary := e.ordinary


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIndependentPinsAdjoin
end
